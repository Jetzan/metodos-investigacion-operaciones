'use strict';
/* Problemas de asignación: Método Húngaro. */

const esc = (s) => String(s).replace(/[&<>"]/g, (c) => ({ '&': '&amp;', '<': '&lt;', '>': '&gt;', '"': '&quot;' }[c]));
const r6 = (v) => Math.round(v * 1e6) / 1e6;
const num = (v) => String(r6(v));
const xv = (i, j) => `x<sub>${i + 1}${j + 1}</sub>`;

/** Mínimo de líneas (filas/columnas) que cubren todos los ceros: acoplamiento máximo + teorema de König. */
function minCover(M) {
	const n = M.length;
	const zero = (i, j) => Math.abs(M[i][j]) < 1e-9;
	const matchCol = Array(n).fill(-1), matchRow = Array(n).fill(-1);
	const tryRow = (i, seen) => {
		for (let j = 0; j < n; j++) {
			if (!zero(i, j) || seen[j]) continue;
			seen[j] = true;
			if (matchCol[j] < 0 || tryRow(matchCol[j], seen)) { matchCol[j] = i; matchRow[i] = j; return true; }
		}
		return false;
	};
	let size = 0;
	for (let i = 0; i < n; i++) if (tryRow(i, Array(n).fill(false))) size++;
	const visR = Array(n).fill(false), visC = Array(n).fill(false);
	const walk = (i) => {
		visR[i] = true;
		for (let j = 0; j < n; j++) {
			if (!zero(i, j) || visC[j]) continue;
			visC[j] = true;
			if (matchCol[j] >= 0 && !visR[matchCol[j]]) walk(matchCol[j]);
		}
	};
	for (let i = 0; i < n; i++) if (matchRow[i] < 0) walk(i);
	return { lines: size, rows: visR.map((v) => !v), cols: visC };
}

function allAssignments(M, cap = 30) {
	const n = M.length, out = [], used = Array(n).fill(false), cur = [];
	const go = (i) => {
		if (out.length >= cap) return;
		if (i === n) { out.push(cur.slice()); return; }
		for (let j = 0; j < n; j++) {
			if (used[j] || Math.abs(M[i][j]) > 1e-9) continue;
			used[j] = true; cur[i] = j; go(i + 1); used[j] = false;
		}
	};
	go(0);
	return out;
}

function solveAssignment(p) {
	const rows = p.c.length, cols = p.c[0].length, n = Math.max(rows, cols);
	const notes = [];
	let orig = Array.from({ length: n }, (_, i) => Array.from({ length: n }, (_, j) => (i < rows && j < cols ? p.c[i][j] : 0)));
	if (rows !== cols) notes.push(`La matriz no es cuadrada: se agregan ${Math.abs(rows - cols)} ${rows < cols ? 'filas' : 'columnas'} ficticias con costo 0 (F) para formar una matriz de ${n}×${n}.`);
	let M = orig.map((r) => r.slice());
	if (p.sense === 'max') {
		const mx = Math.max(...M.flat());
		M = M.map((r) => r.map((v) => r6(mx - v)));
		notes.push(`Es un problema de maximizar: se convierte a minimizar restando cada valor a ${num(mx)} (el mayor de la matriz).`);
	}
	const base = M.map((r) => r.slice());
	const rowMin = M.map((r) => Math.min(...r));
	M = M.map((r, i) => r.map((v) => r6(v - rowMin[i])));
	const afterRows = M.map((r) => r.slice());
	const colMin = Array.from({ length: n }, (_, j) => Math.min(...M.map((r) => r[j])));
	M = M.map((r) => r.map((v, j) => r6(v - colMin[j])));
	const afterCols = M.map((r) => r.slice());

	const iters = [];
	let guard = 0;
	for (;;) {
		const cv = minCover(M);
		const it = { M: M.map((r) => r.slice()), cover: cv };
		iters.push(it);
		if (cv.lines === n) break;
		if (++guard > 100) throw new Error('El método no converge.');
		let k = Infinity;
		for (let i = 0; i < n; i++) for (let j = 0; j < n; j++) if (!cv.rows[i] && !cv.cols[j]) k = Math.min(k, M[i][j]);
		M = M.map((r, i) => r.map((v, j) => {
			const cr = cv.rows[i], cc = cv.cols[j];
			return r6(!cr && !cc ? v - k : cr && cc ? v + k : v);
		}));
		it.k = k;
		it.next = M.map((r) => r.slice());
	}
	const assigns = allAssignments(M).map((a) => {
		let z = 0;
		a.forEach((j, i) => { z += orig[i][j]; });
		return { a, z: r6(z) };
	});
	return { n, rows, cols, notes, orig, base, rowMin, afterRows, colMin, afterCols, iters, final: M, assigns, z: assigns[0] ? assigns[0].z : null, sense: p.sense };
}

/* ---------- Render ---------- */

const section = (num_, title, body) => `<div class="sec"><h3><span class="num">${num_}</span>${title}</h3>${body}</div>`;

function matHTML(M, ctx, o = {}) {
	const n = M.length;
	let h = `<div class="tscroll"><table class="hm"><thead><tr><th class="corner">${esc(ctx.rowName)} \\ ${esc(ctx.colName)}</th>`;
	for (let j = 0; j < n; j++) h += `<th class="${o.cols && o.cols[j] ? 'cov' : ''}">${ctx.colL[j]}</th>`;
	if (o.rowExtra) h += `<th>${o.rowExtraTitle}</th>`;
	h += '</tr></thead><tbody>';
	for (let i = 0; i < n; i++) {
		h += `<tr><th class="${o.rows && o.rows[i] ? 'cov' : ''}">${ctx.rowL[i]}</th>`;
		for (let j = 0; j < n; j++) {
			const cl = [];
			if (Math.abs(M[i][j]) < 1e-9) cl.push('z');
			if (o.rows && o.cols) {
				const cr = o.rows[i], cc = o.cols[j];
				if (cr && cc) cl.push('cx'); else if (cr) cl.push('cr'); else if (cc) cl.push('cc'); else if (o.k !== undefined) cl.push('dn');
				if (cr && cc && o.k !== undefined) cl.push('up');
			}
			if (o.pick && o.pick[i] === j) cl.push('pick');
			h += `<td class="${cl.join(' ')}">${num(M[i][j])}</td>`;
		}
		if (o.rowExtra) h += `<td class="ext">− ${num(o.rowExtra[i])}</td>`;
		h += '</tr>';
	}
	if (o.colExtra) {
		h += `<tr><th>${o.colExtraTitle}</th>${o.colExtra.map((v) => `<td class="ext">− ${num(v)}</td>`).join('')}${o.rowExtra ? '<td></td>' : ''}</tr>`;
	}
	return h + '</tbody></table></div>';
}

function listLines(it, ctx) {
	const r = it.cover.rows.map((v, i) => (v ? `fila ${ctx.rowL[i]}` : null)).filter(Boolean);
	const c = it.cover.cols.map((v, j) => (v ? `columna ${ctx.colL[j]}` : null)).filter(Boolean);
	return [...r, ...c].join(', ');
}

function render(p) {
	const res = solveAssignment(p);
	const n = res.n;
	const lab = (arr, cnt, len) => Array.from({ length: len }, (_, i) => (i < cnt ? esc(arr[i]) : 'F'));
	const ctx = { rowName: p.rowName, colName: p.colName, rowL: lab(p.rowLabels, res.rows, n), colL: lab(p.colLabels, res.cols, n) };
	const isMax = p.sense === 'max';
	let h = '';
	let k = 1;

	// 1. Planteamiento
	const terms = Array.from({ length: n }, (_, i) => `<div>${Array.from({ length: n }, (_, j) => `${num(res.orig[i][j])}${xv(i, j)}`).join(' + ')}${i < n - 1 ? ' +' : ''}</div>`).join('');
	const rowEq = Array.from({ length: n }, (_, i) => `<div>${Array.from({ length: n }, (_, j) => xv(i, j)).join(' + ')} = 1</div>`).join('');
	const colEq = Array.from({ length: n }, (_, j) => `<div>${Array.from({ length: n }, (_, i) => xv(i, j)).join(' + ')} = 1</div>`).join('');
	h += section(k++, 'Planteamiento del problema',
		(res.notes.length ? `<ul class="notes">${res.notes.map((t) => `<li>${t}</li>`).join('')}</ul>` : '') +
		matHTML(res.orig, ctx) +
		`<div class="blk" style="margin-top:16px"><h4>Modelo de programación lineal</h4><div class="tscroll"><div class="mplt">
			<div class="mplt-row"><span class="kw">${isMax ? 'Max' : 'Min'}</span><span class="kw">Z =</span><div>${terms}</div></div>
			<div class="mplt-row"><span class="kw sa">s.a.</span><div class="mplt-cons"><div>${rowEq}</div><div>${colEq}</div></div></div>
			<div class="mplt-row"><span class="kw"></span><span class="nn">x<sub>ij</sub> = 0, 1 ; i, j = 1..${n}</span></div>
		</div></div></div>`);

	// 2. Reducción
	let body = '';
	if (isMax) body += `<div class="blk"><h4>Matriz convertida a minimización</h4>${matHTML(res.base, ctx)}</div>`;
	body += `<div class="blk"><h4>Restar el mínimo de cada fila</h4>${matHTML(res.afterRows, ctx, { rowExtra: res.rowMin, rowExtraTitle: 'Mín. fila' })}</div>`;
	body += `<div class="blk"><h4>Restar el mínimo de cada columna</h4>${matHTML(res.afterCols, ctx, { colExtra: res.colMin, colExtraTitle: 'Mín. columna' })}</div>`;
	h += section(k++, 'Reducción de filas y columnas', '<p>Primero se resta a cada fila su valor mínimo y luego a cada columna su valor mínimo, para obtener ceros.</p>' + body);

	// 3. Cobertura y ajustes
	body = '<p>Se cubren todos los ceros con el mínimo número de líneas (filas o columnas). Si ese número es igual a mín{R, C} = ' + n + ', ya existe una asignación óptima; si no, se ajusta la matriz.</p>';
	res.iters.forEach((it, idx) => {
		const ok = it.cover.lines === n;
		body += `<div class="blk"><h4>Cobertura de ceros${res.iters.length > 1 ? ` ${idx + 1}` : ''}</h4>${matHTML(it.M, ctx, { rows: it.cover.rows, cols: it.cover.cols })}` +
			`<p class="step-note">Líneas: ${listLines(it, ctx) || '—'}.<br>N.º de líneas = ${it.cover.lines} ; mín{R, C} = ${n} → ${it.cover.lines} ${ok ? '=' : '≠'} ${n} ${ok ? '✓' : '✗'}</p></div>`;
		if (!ok) {
			body += `<div class="blk"><h4>Ajuste de la matriz</h4><p>El menor valor sin cubrir es <b>${num(it.k)}</b>: se resta a los valores sin cubrir y se suma a los que están en la intersección de dos líneas.</p>` +
				matHTML(it.next, ctx, { rows: it.cover.rows, cols: it.cover.cols, k: it.k }) + '</div>';
		}
	});
	body += '<p class="legend">Celdas sombreadas = cubiertas por una línea (más oscuro = intersección de dos líneas).</p>';
	h += section(k++, 'Cobertura de ceros y ajustes', body);

	// 4. Asignación
	const label = (i, j) => `${ctx.rowL[i]} → ${ctx.colL[j]}`;
	body = `<p>Con ${n} líneas se puede escoger una asignación usando solo ceros (uno por fila y por columna). El costo se calcula con la matriz original.</p>`;
	body += matHTML(res.final, ctx, { pick: res.assigns[0] ? res.assigns[0].a : null });
	body += '<div class="steps">';
	res.assigns.forEach((as, idx) => {
		let t = '<table class="mat"><tbody>';
		as.a.forEach((j, i) => {
			const dummy = i >= res.rows || j >= res.cols;
			t += `<tr><td>${label(i, j)}</td><td>${dummy ? 'ficticio' : num(res.orig[i][j])}</td></tr>`;
		});
		t += `<tr><td><b>Z</b></td><td><b>${num(as.z)}</b></td></tr></tbody></table>`;
		body += `<div class="step"><div class="d">${res.assigns.length > 1 ? `Asignación ${idx + 1}` : 'Asignación óptima'}</div>${t}</div>`;
	});
	body += '</div>';
	if (res.assigns.length > 1) body += `<p class="legend">Hay ${res.assigns.length >= 30 ? 'al menos 30' : res.assigns.length} asignaciones óptimas; todas tienen el mismo costo.${res.assigns.length >= 30 ? ' Se muestran las primeras 30.' : ''}</p>`;
	body += `<div class="result" style="margin-top:14px"><div class="rt">Asignación óptima${res.assigns.length > 1 ? ' (múltiple)' : ''}</div><div>→ Z${isMax ? ' (máximo)' : ' (mínimo)'} = ${num(res.z)}</div></div>`;
	h += section(k++, 'Asignación óptima', body);

	document.getElementById('result').innerHTML = h;
}

/* ---------- Interfaz ---------- */

function initHungaroUI() {
	const $ = (id) => document.getElementById(id);
	const state = { sense: 'min', r: 4, c: 4, rowName: 'Filas', colName: 'Columnas', built: false };

	function goStep(k) {
		[1, 2, 3].forEach((i) => {
			$('step' + i).hidden = i !== k;
			$('ind' + i).classList.toggle('active', i === k);
			$('ind' + i).classList.toggle('done', i < k);
		});
		window.scrollTo({ top: 0 });
	}

	function buildForm() {
		const { r, c } = state;
		let h = `<table class="tpform"><thead><tr><th>${esc(state.rowName)} \\ ${esc(state.colName)}</th>`;
		for (let j = 0; j < c; j++) h += `<th><input type="text" class="lab" data-cl="${j}" value="${j + 1}" aria-label="Nombre de ${esc(state.colName)} ${j + 1}"></th>`;
		h += '</tr></thead><tbody>';
		for (let i = 0; i < r; i++) {
			h += `<tr><th><input type="text" class="lab" data-rl="${i}" value="${i + 1}" aria-label="Nombre de ${esc(state.rowName)} ${i + 1}"></th>`;
			for (let j = 0; j < c; j++) h += `<td><input type="text" inputmode="decimal" placeholder="0" data-c="${i},${j}"></td>`;
			h += '</tr>';
		}
		$('mplForm').innerHTML = h + '</tbody></table>';
		state.built = true;
	}

	function read() {
		let bad = false;
		const f = $('mplForm');
		const c = Array.from({ length: state.r }, (_, i) => Array.from({ length: state.c }, (_, j) => {
			const el = f.querySelector(`[data-c="${i},${j}"]`);
			const t = el.value.trim().replace(',', '.');
			const v = t === '' ? 0 : Number(t);
			el.classList.toggle('bad', !Number.isFinite(v));
			if (!Number.isFinite(v)) bad = true;
			return Number.isFinite(v) ? v : 0;
		}));
		const lab = (attr, len) => Array.from({ length: len }, (_, i) => f.querySelector(`[${attr}="${i}"]`).value.trim() || String(i + 1));
		return bad ? null : { c, sense: state.sense, rowName: state.rowName, colName: state.colName, rowLabels: lab('data-rl', state.r), colLabels: lab('data-cl', state.c) };
	}

	$('cfg').addEventListener('submit', (e) => {
		e.preventDefault();
		const clamp = (v) => Math.min(8, Math.max(1, parseInt(v, 10) || 1));
		const sense = document.querySelector('input[name="sense"]:checked').value;
		const r = clamp($('nRows').value), c = clamp($('nCols').value);
		$('nRows').value = r; $('nCols').value = c;
		const rowName = $('nameR').value.trim() || 'Filas', colName = $('nameC').value.trim() || 'Columnas';
		const same = state.built && r === state.r && c === state.c && rowName === state.rowName && colName === state.colName;
		Object.assign(state, { sense, r, c, rowName, colName });
		if (!same) buildForm();
		$('err').hidden = true;
		goStep(2);
	});
	$('back1').addEventListener('click', () => goStep(1));
	$('edit').addEventListener('click', () => goStep(2));
	$('restart').addEventListener('click', () => { state.built = false; goStep(1); });
	$('mpl').addEventListener('submit', (e) => {
		e.preventDefault();
		const p = read();
		const err = $('err');
		if (!p) {
			err.textContent = 'Hay valores no válidos (marcados en la tabla). Usa números enteros o decimales.';
			err.hidden = false;
			return;
		}
		try { render(p); err.hidden = true; goStep(3); } catch (ex) { err.textContent = ex.message; err.hidden = false; }
	});
}

if (typeof document !== 'undefined') initHungaroUI();
if (typeof module !== 'undefined') module.exports = { solveAssignment, minCover };
