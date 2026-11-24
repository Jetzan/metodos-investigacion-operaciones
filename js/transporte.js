'use strict';
/* Problemas de transporte: Esquina Noroeste y Costo Mínimo (soluciones básicas factibles iniciales). */

const esc = (s) => String(s).replace(/[&<>"]/g, (c) => ({ '&': '&amp;', '<': '&lt;', '>': '&gt;', '"': '&quot;' }[c]));
const r6 = (v) => Math.round(v * 1e6) / 1e6;
const num = (v) => String(r6(v));
const money = (v) => r6(v).toLocaleString('en-US');
const xv = (i, j) => `x<sub>${i + 1}${j + 1}</sub>`;
const METHOD_NAME = { nw: 'Esquina Noroeste', min: 'Costo Mínimo' };

/** Si oferta ≠ demanda agrega un origen o destino ficticio con costo 0. */
function balance(p) {
	const c = p.c.map((r) => r.slice()), s = p.s.slice(), d = p.d.slice();
	const sumS = s.reduce((a, b) => a + b, 0), sumD = d.reduce((a, b) => a + b, 0);
	let dummy = null;
	if (r6(sumS - sumD) > 0) {
		d.push(r6(sumS - sumD)); c.forEach((r) => r.push(0)); dummy = 'col';
	} else if (r6(sumD - sumS) > 0) {
		s.push(r6(sumD - sumS)); c.push(Array(d.length).fill(0)); dummy = 'row';
	}
	return { c, s, d, dummy, sumS, sumD, m: s.length, n: d.length };
}

function allocate(b, method) {
	const { c, m, n } = b;
	const rs = b.s.slice(), cs = b.d.slice();
	const rowOn = rs.map((v) => v > 0), colOn = cs.map((v) => v > 0);
	const rowHist = rs.map((v) => [v]), colHist = cs.map((v) => [v]);
	const a = Array.from({ length: m }, () => Array(n).fill(null));
	const steps = [];
	while (rowOn.some(Boolean) && colOn.some(Boolean)) {
		let bi = -1, bj = -1;
		if (method === 'nw') {
			bi = rowOn.indexOf(true); bj = colOn.indexOf(true);
		} else {
			for (let i = 0; i < m; i++) {
				if (!rowOn[i]) continue;
				for (let j = 0; j < n; j++) if (colOn[j] && (bi < 0 || c[i][j] < c[bi][bj])) { bi = i; bj = j; }
			}
		}
		const sa = rs[bi], da = cs[bj], x = r6(Math.min(sa, da));
		a[bi][bj] = x;
		rs[bi] = r6(rs[bi] - x); cs[bj] = r6(cs[bj] - x);
		rowHist[bi].push(rs[bi]); colHist[bj].push(cs[bj]);
		const crossRow = rs[bi] === 0, crossCol = cs[bj] === 0;
		if (crossRow) rowOn[bi] = false;
		if (crossCol) colOn[bj] = false;
		steps.push({ i: bi, j: bj, x, sa, da, cost: c[bi][bj], crossRow, crossCol });
	}
	let z = 0;
	const basic = [];
	for (let i = 0; i < m; i++) for (let j = 0; j < n; j++) if (a[i][j] !== null) { z += a[i][j] * c[i][j]; basic.push({ i, j, x: a[i][j], cost: c[i][j] }); }
	return { a, steps, rowHist, colHist, z: r6(z), basic, degenerate: basic.length < m + n - 1 };
}

/* ---------- Render ---------- */

const section = (num_, title, body) => `<div class="sec"><h3><span class="num">${num_}</span>${title}</h3>${body}</div>`;

function histHTML(h) {
	return h.map((v, k) => (k < h.length - 1 ? `<s>${num(v)}</s>` : num(v))).join(' ');
}

function tableHTML(b, res, names, labels) {
	const { c, m, n } = b;
	const rl = (i) => (b.dummy === 'row' && i === m - 1 ? 'F' : i + 1);
	const cl = (j) => (b.dummy === 'col' && j === n - 1 ? 'F' : j + 1);
	let h = `<div class="tscroll"><table class="tp"><thead><tr><th class="corner">${esc(names.o)} \\ ${esc(names.d)}</th>`;
	for (let j = 0; j < n; j++) h += `<th>${cl(j)}</th>`;
	h += '<th>Oferta</th></tr></thead><tbody>';
	for (let i = 0; i < m; i++) {
		h += `<tr><th>${rl(i)}</th>`;
		for (let j = 0; j < n; j++) {
			const v = res ? res.a[i][j] : null;
			h += `<td class="c ${v !== null ? 'on' : ''}"><span class="cost">${num(c[i][j])}</span>` +
				(res ? (v !== null ? `<span class="v">${num(v)}</span>` : '<span class="x">✕</span>') : '') + '</td>';
		}
		h += `<td class="rem">${res ? histHTML(res.rowHist[i]) : num(b.s[i])}</td></tr>`;
	}
	h += '<tr><th>Demanda</th>';
	for (let j = 0; j < n; j++) h += `<td class="rem">${res ? histHTML(res.colHist[j]) : num(b.d[j])}</td>`;
	h += `<td class="rem">${num(b.sumS)}</td></tr></tbody></table></div>`;
	return h;
}

function mplHTML(b, names) {
	const { c, m, n } = b;
	const tName = (i, j) => `${num(c[i][j])}${xv(i, j)}`;
	let obj = '';
	for (let i = 0; i < m; i++) obj += `<div>${Array.from({ length: n }, (_, j) => tName(i, j)).join(' + ')}${i < m - 1 ? ' +' : ''}</div>`;
	const sup = Array.from({ length: m }, (_, i) => `<div>${Array.from({ length: n }, (_, j) => xv(i, j)).join(' + ')} = ${num(b.s[i])}</div>`).join('');
	const dem = Array.from({ length: n }, (_, j) => `<div>${Array.from({ length: m }, (_, i) => xv(i, j)).join(' + ')} = ${num(b.d[j])}</div>`).join('');
	return `<div class="tscroll"><div class="mplt">
		<div class="mplt-row"><span class="kw">Min</span><span class="kw">Z =</span><div>${obj}</div></div>
		<div class="mplt-row"><span class="kw sa">s.a.</span><div class="mplt-cons"><div>${sup}</div><div>${dem}</div></div></div>
		<div class="mplt-row"><span class="kw"></span><span class="nn">x<sub>ij</sub> ≥ 0 ; i = 1..${m} ; j = 1..${n}</span></div>
	</div></div>`;
}

function methodHTML(b, method, res, names) {
	const nameO = esc(names.o), nameD = esc(names.d);
	const rl = (i) => (b.dummy === 'row' && i === b.m - 1 ? 'F' : i + 1);
	const cl = (j) => (b.dummy === 'col' && j === b.n - 1 ? 'F' : j + 1);
	let h = method === 'nw'
		? '<p>Se empieza en la esquina superior izquierda de la tabla. En cada paso se asigna lo máximo posible (el menor entre la oferta y la demanda restantes) y se tacha la fila o columna agotada.</p>'
		: '<p>En cada paso se elige la celda de menor costo entre las que siguen disponibles (si hay empate, la primera de arriba hacia abajo y de izquierda a derecha), se asigna lo máximo posible y se tacha la fila o columna agotada.</p>';
	h += tableHTML(b, res, names);
	h += '<p class="legend">✕ = celda sin asignación. Las ofertas y demandas muestran su valor restante; el valor anterior aparece tachado.</p>';
	h += '<div class="blk"><h4>Paso a paso</h4><ol class="stepl">';
	res.steps.forEach((s) => {
		const lead = method === 'nw'
			? `Esquina noroeste: celda (${rl(s.i)}, ${cl(s.j)}).`
			: `Menor costo disponible: ${num(s.cost)}, celda (${rl(s.i)}, ${cl(s.j)}).`;
		let cut;
		if (s.crossRow && s.crossCol) cut = `Se agotan a la vez la ${nameO.toLowerCase()} ${rl(s.i)} y la ${nameD.toLowerCase()} ${cl(s.j)}; se tachan ambas.`;
		else if (s.crossRow) cut = `Se tacha la fila ${rl(s.i)}.`;
		else cut = `Se tacha la columna ${cl(s.j)}.`;
		h += `<li>${lead} ${xv(s.i, s.j)} = mín(${num(s.sa)}, ${num(s.da)}) = <b>${num(s.x)}</b>. ${cut}</li>`;
	});
	h += '</ol></div>';
	const nz = res.basic.map((v) => `${xv(v.i, v.j)} = ${num(v.x)}`).join(', ');
	const zero = [];
	for (let i = 0; i < b.m; i++) for (let j = 0; j < b.n; j++) if (res.a[i][j] === null) zero.push(xv(i, j));
	h += `<div class="blk"><h4>SBFI</h4><p>${nz}</p>${zero.length ? `<p>${zero.join(', ')} = 0</p>` : ''}`;
	h += `<p>Z = ${res.basic.map((v) => `${num(v.x)}(${num(v.cost)})`).join(' + ')} = ${money(res.z)}</p></div>`;
	if (res.degenerate) h += `<p class="legend">La solución es degenerada: tiene ${res.basic.length} variables básicas con valor positivo, menos de m + n − 1 = ${b.m + b.n - 1}.</p>`;
	h += `<div class="result"><div class="rt">${METHOD_NAME[method]}</div><div>→ Z = ${money(res.z)}</div></div>`;
	return h;
}

function render(p) {
	const b = balance(p);
	const names = p.names;
	let k = 1, h = '';
	const notes = [];
	if (b.dummy === 'col') notes.push(`La oferta total (${num(b.sumS)}) es mayor que la demanda total (${num(b.sumD)}): se agrega un destino ficticio F con demanda ${num(b.sumS - b.sumD)} y costos 0.`);
	if (b.dummy === 'row') notes.push(`La demanda total (${num(b.sumD)}) es mayor que la oferta total (${num(b.sumS)}): se agrega un origen ficticio F con oferta ${num(b.sumD - b.sumS)} y costos 0.`);
	if (!notes.length) notes.push(`Problema balanceado: oferta total = demanda total = ${num(b.sumS)}.`);
	h += section(k++, 'Planteamiento del problema',
		`<ul class="notes">${notes.map((t) => `<li>${t}</li>`).join('')}</ul>` + tableHTML(b, null, names) +
		'<div class="blk" style="margin-top:16px"><h4>Modelo de programación lineal</h4>' + mplHTML(b, names) + '</div>');
	const methods = p.method === 'both' ? ['nw', 'min'] : [p.method];
	const out = {};
	methods.forEach((mt) => {
		out[mt] = allocate(b, mt);
		h += section(k++, `Método de ${METHOD_NAME[mt]}`, methodHTML(b, mt, out[mt], names));
	});
	if (p.method === 'both') {
		const a = out.nw.z, c = out.min.z;
		const best = a < c ? 'la Esquina Noroeste' : c < a ? 'el Costo Mínimo' : null;
		h += section(k++, 'Comparación',
			`<div class="facts"><div>Esquina Noroeste: <b>${money(a)}</b></div><div>Costo Mínimo: <b>${money(c)}</b></div></div>` +
			`<p>${best ? `La solución inicial con menor costo es la obtenida con ${best} (diferencia de ${money(Math.abs(a - c))}).` : 'Ambos métodos dan el mismo costo inicial.'} Ambas son soluciones iniciales: se pueden mejorar con el método de transporte (MODI / paso secuencial).</p>`);
	}
	document.getElementById('result').innerHTML = h;
}

/* ---------- Interfaz ---------- */

function initTransporteUI() {
	const $ = (id) => document.getElementById(id);
	const state = { method: 'both', m: 3, n: 4, names: { o: 'Plantas', d: 'Almacenes' }, built: false };

	function goStep(k) {
		[1, 2, 3].forEach((i) => {
			$('step' + i).hidden = i !== k;
			$('ind' + i).classList.toggle('active', i === k);
			$('ind' + i).classList.toggle('done', i < k);
		});
		window.scrollTo({ top: 0 });
	}

	function buildForm() {
		const { m, n, names } = state;
		let h = `<table class="tpform"><thead><tr><th>${esc(names.o)} \\ ${esc(names.d)}</th>`;
		for (let j = 0; j < n; j++) h += `<th>${j + 1}</th>`;
		h += '<th>Oferta</th></tr></thead><tbody>';
		for (let i = 0; i < m; i++) {
			h += `<tr><th>${i + 1}</th>`;
			for (let j = 0; j < n; j++) h += `<td><input type="text" inputmode="decimal" placeholder="0" data-c="${i},${j}"></td>`;
			h += `<td><input type="text" inputmode="decimal" placeholder="0" data-s="${i}"></td></tr>`;
		}
		h += '<tr><th>Demanda</th>';
		for (let j = 0; j < n; j++) h += `<td><input type="text" inputmode="decimal" placeholder="0" data-d="${j}"></td>`;
		h += '<td></td></tr></tbody></table>';
		$('mplForm').innerHTML = h;
		state.built = true;
	}

	function read() {
		let bad = false;
		const get = (el, nonneg) => {
			const t = el.value.trim().replace(',', '.');
			const v = t === '' ? 0 : Number(t);
			const ok = Number.isFinite(v) && (!nonneg || v >= 0);
			el.classList.toggle('bad', !ok);
			if (!ok) bad = true;
			return ok ? v : 0;
		};
		const f = $('mplForm');
		const c = Array.from({ length: state.m }, (_, i) => Array.from({ length: state.n }, (_, j) => get(f.querySelector(`[data-c="${i},${j}"]`), false)));
		const s = Array.from({ length: state.m }, (_, i) => get(f.querySelector(`[data-s="${i}"]`), true));
		const d = Array.from({ length: state.n }, (_, j) => get(f.querySelector(`[data-d="${j}"]`), true));
		return bad ? null : { c, s, d, method: state.method, names: state.names };
	}

	$('cfg').addEventListener('submit', (e) => {
		e.preventDefault();
		const clamp = (v) => Math.min(6, Math.max(1, parseInt(v, 10) || 1));
		const method = document.querySelector('input[name="method"]:checked').value;
		const m = clamp($('nOrig').value), n = clamp($('nDest').value);
		$('nOrig').value = m; $('nDest').value = n;
		const names = { o: $('nameO').value.trim() || 'Orígenes', d: $('nameD').value.trim() || 'Destinos' };
		const same = state.built && m === state.m && n === state.n && names.o === state.names.o && names.d === state.names.d;
		Object.assign(state, { method, m, n, names });
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
			err.textContent = 'Hay valores no válidos (marcados en la tabla). Usa números; la oferta y la demanda no pueden ser negativas.';
			err.hidden = false;
			return;
		}
		if (p.s.every((v) => v === 0) || p.d.every((v) => v === 0)) {
			err.textContent = 'Escribe al menos una oferta y una demanda mayores que 0.';
			err.hidden = false;
			return;
		}
		render(p);
		err.hidden = true;
		goStep(3);
	});
}

if (typeof document !== 'undefined') initTransporteUI();
if (typeof module !== 'undefined') module.exports = { balance, allocate };
