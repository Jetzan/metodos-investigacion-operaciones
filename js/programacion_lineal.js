'use strict';
const absB = (a) => (a < 0n ? -a : a);
const gcdB = (a, b) => { a = absB(a); b = absB(b); while (b) { [a, b] = [b, a % b]; } return a; };

class Fr {
	constructor(n, d = 1n) {
		if (d === 0n) throw new Error('División entre cero');
		if (d < 0n) { n = -n; d = -d; }
		const g = gcdB(n, d) || 1n;
		this.n = n / g;
		this.d = d / g;
	}
	add(o) { return new Fr(this.n * o.d + o.n * this.d, this.d * o.d); }
	sub(o) { return new Fr(this.n * o.d - o.n * this.d, this.d * o.d); }
	mul(o) { return new Fr(this.n * o.n, this.d * o.d); }
	div(o) { return new Fr(this.n * o.d, this.d * o.n); }
	neg() { return new Fr(-this.n, this.d); }
	abs() { return new Fr(absB(this.n), this.d); }
	sign() { return this.n < 0n ? -1 : this.n > 0n ? 1 : 0; }
	isZero() { return this.n === 0n; }
	isOne() { return this.n === 1n && this.d === 1n; }
	cmp(o) { const l = this.n * o.d, r = o.n * this.d; return l < r ? -1 : l > r ? 1 : 0; }
	toNumber() { return Number(this.n) / Number(this.d); }
	toString() { return this.d === 1n ? this.n.toString() : `${this.n}/${this.d}`; }
}

const ZERO = new Fr(0n);
const ONE = new Fr(1n);

/** Convierte texto ("3", "-2.5", "3/4") en Fr. Vacío = 0. Inválido = undefined. */
function parseFr(str) {
	let s = String(str).trim().replace(',', '.').replace('−', '-');
	if (s === '') return ZERO;
	let m = s.match(/^([+-]?)(\d+)\/(\d+)$/);
	if (m) {
		if (BigInt(m[3]) === 0n) return undefined;
		const f = new Fr(BigInt(m[2]), BigInt(m[3]));
		return m[1] === '-' ? f.neg() : f;
	}
	m = s.match(/^([+-]?)(\d*)(?:\.(\d*))?$/);
	if (!m || (m[2] === '' && (m[3] === undefined || m[3] === ''))) return undefined;
	const ip = m[2] || '0', fp = m[3] || '';
	const f = new Fr(BigInt(ip + fp), 10n ** BigInt(fp.length));
	return m[1] === '-' ? f.neg() : f;
}

const approx = (f) => f.d === 1n ? f.toString() : `${f} ≈ ${f.toNumber().toFixed(4).replace(/\.?0+$/, '')}`;

const MAX_COMBOS = 20000;
// Letras disponibles (sin z, para no confundirla con la función Z).
// Variables de decisión: las primeras n (x, y, w, ...). Holguras: las siguientes m, en orden alfabético.
const POOL = 'xywvutsrqponmlkjihgfedcba'.split('');
const decisionNames = (n) => POOL.slice(0, n);
const slackNames = (n, m) => POOL.slice(n, n + m).sort();

function binom(N, m) {
	let r = 1n;
	for (let i = 1n; i <= BigInt(m); i++) r = (r * (BigInt(N) - BigInt(m) + i)) / i;
	return r;
}

function* combos(N, m) {
	const idx = Array.from({ length: m }, (_, i) => i);
	while (true) {
		yield idx.slice();
		let i = m - 1;
		while (i >= 0 && idx[i] === N - m + i) i--;
		if (i < 0) return;
		idx[i]++;
		for (let j = i + 1; j < m; j++) idx[j] = idx[j - 1] + 1;
	}
}

/** Resuelve un sistema cuadrado aumentado m×(m+1). Devuelve null si es singular. */
function solveSquare(M0) {
	const m = M0.length;
	const M = M0.map((r) => r.slice());
	for (let k = 0; k < m; k++) {
		let r = -1;
		for (let i = k; i < m; i++) if (!M[i][k].isZero()) { r = i; break; }
		if (r < 0) return null;
		[M[k], M[r]] = [M[r], M[k]];
		const p = M[k][k];
		M[k] = M[k].map((v) => v.div(p));
		for (let i = 0; i < m; i++) {
		if (i !== k && !M[i][k].isZero()) {
			const f = M[i][k];
			M[i] = M[i].map((v, j) => v.sub(f.mul(M[k][j])));
		}
		}
	}
	return M.map((r) => r[m]);
}

/** Forma canónica: Max con todas las restricciones ≤. */
function toCanonical(p) {
	const notes = [];
	let c = p.c.slice();
	if (p.sense === 'min') {
		c = c.map((v) => v.neg());
		notes.push('La función es de minimizar: se convierte en maximizar Z′ = −Z (al final Z* = −Z′*).');
	}
	const A = [], b = [];
	p.A.forEach((row, i) => {
		const k = i + 1;
		if (p.ops[i] === 'le') {
		A.push(row.slice()); b.push(p.b[i]);
		} else if (p.ops[i] === 'ge') {
		A.push(row.map((v) => v.neg())); b.push(p.b[i].neg());
		notes.push(`Restricción ${k} (≥): se multiplica por −1 para dejarla en ≤.`);
		} else {
		A.push(row.slice()); b.push(p.b[i]);
		A.push(row.map((v) => v.neg())); b.push(p.b[i].neg());
		notes.push(`Restricción ${k} (=): se reemplaza por dos desigualdades (≤ y ≥); la ≥ se multiplica por −1.`);
		}
	});
	return { c, A, b, notes, applies: notes.length > 0 };
}

/** Forma estándar: agrega una variable de holgura por cada restricción. */
function buildStandard(A, b, c, n) {
	const m = A.length;
	const S = A.map((row, i) => [...row, ...Array.from({ length: m }, (_, j) => (j === i ? ONE : ZERO))]);
	const cStd = [...c, ...Array(m).fill(ZERO)];
	const names = [...decisionNames(n), ...slackNames(n, m)];
	return { S, b, cStd, names, m, N: n + m };
}

/** Enumera las C(N, m) soluciones básicas. */
function enumerate(std) {
	const { S, b, cStd, m, N } = std;
	if (binom(N, m) > BigInt(MAX_COMBOS)) {
		throw new Error(`El problema genera demasiadas soluciones básicas (${binom(N, m)}). Reduce variables o restricciones.`);
	}
	const rows = [];
	let id = 1;
	// Se eligen las N−m variables que valen 0 (empezando por las de la izquierda: x, y, ...)
	// y las demás son las variables básicas que se despejan.
	for (const zeros of combos(N, N - m)) {
		const combo = [];
		for (let j = 0; j < N; j++) if (!zeros.includes(j)) combo.push(j);
		const M = S.map((r, i) => [...combo.map((j) => r[j]), b[i]]);
		const sol = solveSquare(M);
		const x = Array(N).fill(ZERO);
		let status, z = null;
		if (!sol) status = 'singular';
		else {
		combo.forEach((col, k) => { x[col] = sol[k]; });
		if (x.every((v) => v.sign() >= 0)) {
			status = 'ok';
			z = x.reduce((acc, v, j) => acc.add(v.mul(cStd[j])), ZERO);
		} else status = 'nf';
		}
		rows.push({ id: id++, combo, x, status, z, opt: false });
	}
	return rows;
}

const bestOf = (rows) => rows.filter((r) => r.status === 'ok').reduce((best, r) => (best === null || r.z.cmp(best) > 0 ? r.z : best), null);

/** Filas óptimas con puntos distintos (una solución degenerada puede repetirse con distintas bases). */
function distinctOpt(rows) {
	const seen = new Set();
	return rows.filter((r) => {
		if (!r.opt) return false;
		const key = r.x.join('|');
		if (seen.has(key)) return false;
		seen.add(key);
		return true;
	});
}

function solveProblem(p) {
	const canon = toCanonical(p);
	const std = buildStandard(canon.A, canon.b, canon.c, p.n);
	const rows = enumerate(std);
	const best = bestOf(rows);
	let status;
	if (best === null) status = 'infeasible';
	else {
		// ¿No acotado? Se acota la región con Σx ≤ M (M enorme): si Z mejora, la región no está acotada en esa dirección.
		const M = new Fr(1000000000n);
		const A2 = [...canon.A, Array.from({ length: p.n }, () => ONE)];
		const b2 = [...canon.b, M];
		const best2 = bestOf(enumerate(buildStandard(A2, b2, canon.c, p.n)));
		if (best2 !== null && best2.cmp(best) > 0) status = 'unbounded';
		else {
		rows.forEach((r) => { r.opt = r.status === 'ok' && r.z.cmp(best) === 0; });
		status = distinctOpt(rows).length > 1 ? 'multiple' : 'unique';
		}
	}
	return { canon, std, rows, best, status };
}

const SYM = { le: '≤', ge: '≥', eq: '=' };

function termHTML(c, name) {
	const a = c.abs();
	if (a.isOne()) return name;
	return (a.d === 1n ? a.n.toString() : `(${a.n}/${a.d})`) + name;
}

function linearHTML(coefs, names) {
	let out = '', first = true;
	coefs.forEach((c, i) => {
		if (c.isZero()) return;
		const neg = c.sign() < 0;
		const t = termHTML(c, names[i]);
		out += first ? (neg ? '−' : '') + t : (neg ? ' − ' : ' + ') + t;
		first = false;
	});
	return first ? '0' : out;
}

function systemHTML(A, names, ops, b) {
	let h = '<table class="sys">';
	A.forEach((row, i) => {
		let first = true;
		const cells = row.map((c, j) => {
		if (c.isZero()) return '<td></td>';
		const neg = c.sign() < 0;
		const t = termHTML(c, names[j]);
		const pre = first ? (neg ? '−' : '') : neg ? '− ' : '+ ';
		first = false;
		return `<td>${pre}${t}</td>`;
		});
		if (first) cells[0] = '<td>0</td>';
		h += `<tr>${cells.join('')}<td class="op">${ops[i]}</td><td>${b[i]}</td></tr>`;
	});
	return h + '</table>';
}

function mplHTML({ sense, z, c, names, A, ops, b, nn }) {
	return `<div class="mpl">
		<div class="mpl-row"><span class="kw">${sense}</span><span>${z} = ${linearHTML(c, names)}</span></div>
		<div class="mpl-row"><span class="kw sa">s.a.</span><div>${systemHTML(A, names, ops, b)}</div></div>
		<div class="mpl-row"><span class="kw"></span><span class="nn">${nn.join(', ')} ≥ 0</span></div>
	</div>`;
}

const section = (num, title, body) => `<div class="sec"><h3><span class="num">${num}</span>${title}</h3>${body}</div>`;

function tableHTML(std, rows, zLabel) {
	let h = '<div class="tscroll"><table class="sol"><thead><tr><th>N</th>';
	h += std.names.map((n) => `<th>${n}</th>`).join('');
	h += `<th>${zLabel} = ${linearHTML(std.cStd, std.names)}</th></tr></thead><tbody>`;
	rows.forEach((r) => {
		const cls = r.opt ? 'best' : r.status !== 'ok' ? 'nf' : '';
		h += `<tr class="${cls}"><td>${r.id}</td>`;
		if (r.status === 'singular') {
		h += `<td colspan="${std.N}">Sistema singular (sin solución única)</td><td>—</td>`;
		} else {
		h += r.x.map((v) => `<td>${v}</td>`).join('');
		h += `<td>${r.status === 'ok' ? r.z : 'NF'}</td>`;
		}
		h += '</tr>';
	});
	return h + '</tbody></table></div>' +
		'<p class="legend">NF = no factible (alguna variable resulta negativa). La fila resaltada es la solución óptima.</p></div>';
}

function resultHTML(p, res) {
	const isMin = p.sense === 'min';
	const xs = (row) => `(${row.x.slice(0, p.n).map(approx).join(', ')})`;
	if (res.status === 'infeasible') {
		return '<div class="result"><div class="rt">Sin solución factible</div><div>Ninguna solución básica cumple x ≥ 0 (todas son NF).</div></div>';
	}
	if (res.status === 'unbounded') {
		return `<div class="result"><div class="rt">Solución no acotada</div><div>Z puede ${isMin ? 'disminuir' : 'crecer'} sin límite dentro de la región factible.</div></div>`;
	}
	const opt = distinctOpt(res.rows);
	const zFinal = isMin ? res.best.neg() : res.best;
	const zLines = isMin
		? `<div>→ Z′* = ${res.best}</div><div>→ Z* = −(${res.best}) = ${approx(zFinal)}</div>`
		: `<div>→ Z* = ${approx(zFinal)}</div>`;
	if (res.status === 'unique') {
		return `<div class="result"><div class="rt">Solución única</div><div>→ x* = ${xs(opt[0])}</div>${zLines}</div>`;
	}
	return `<div class="result"><div class="rt">Soluciones óptimas múltiples</div>` +
		opt.map((r, i) => `<div>→ x*<sub>${i + 1}</sub> = ${xs(r)}</div>`).join('') + zLines;
}

function render(p, res) {
	const xs = decisionNames(p.n);
	const isMin = p.sense === 'min';
	const zL = isMin ? 'Z′' : 'Z';
	const { canon, std } = res;
	let h = '';

	// 1. Planteamiento
	h += section(1, 'Planteamiento del problema', mplHTML({
		sense: isMin ? 'Min' : 'Max', z: 'Z', c: p.c, names: xs, A: p.A,
		ops: p.ops.map((o) => SYM[o]), b: p.b, nn: xs,
	}));

	// 2. Forma canónica (solo si aplica)
	const canonMPL = mplHTML({
		sense: 'Max', z: zL, c: canon.c, names: xs, A: canon.A,
		ops: canon.A.map(() => '≤'), b: canon.b, nn: xs,
	});
	h += section(2, 'Forma canónica', canon.applies
		? `<ul class="notes">${canon.notes.map((t) => `<li>${t}</li>`).join('')}</ul>${canonMPL}`
		: '<p>El problema ya está en forma canónica (maximizar con restricciones ≤); no se requiere conversión.</p>');

	// 3. Forma estándar
	h += section(3, 'Forma estándar',
		`<p>Se suma una variable de holgura a cada restricción ≤ para volverla igualdad.</p>` +
		mplHTML({
		sense: 'Max', z: zL, c: canon.c, names: std.names, A: std.S,
		ops: std.S.map(() => '='), b: std.b, nn: std.names,
		}));

	// 4. Soluciones básicas
	const k = std.N - std.m;
	h += section(4, 'Soluciones básicas',
		`<div class="facts">
		<div>m = ${std.m} <small>(variables distintas de cero)</small></div>
		<div>n = ${std.N} <small>(n − m = ${k}, ${k} en cero)</small></div>
		<div>Combinaciones(${std.N}, ${std.m}) = ${binom(std.N, std.m)}</div>
		</div>` + tableHTML(std, res.rows, zL));

	// 5. Solución
	h += section(5, 'Solución', resultHTML(p, res));

	document.getElementById('result').innerHTML = h;
}

function initUI() {
	const $ = (id) => document.getElementById(id);
	const state = { sense: 'max', n: 2, m: 2, built: false };

	function goStep(k) {
		[1, 2, 3].forEach((i) => {
		$('step' + i).hidden = i !== k;
		$('ind' + i).classList.toggle('active', i === k);
		$('ind' + i).classList.toggle('done', i < k);
		});
		window.scrollTo({ top: 0 });
	}

	function buildForm() {
		const { n, m, sense } = state;
		const names = decisionNames(n);
		let h = `<div class="zrow"><span class="kw" id="kwSense">${sense === 'max' ? 'Max' : 'Min'}</span><span class="lbl">Z =</span>`;
		for (let j = 0; j < n; j++) {
		h += `<span class="term"><input type="text" inputmode="decimal" placeholder="0" data-c="${j}"><span>${names[j]}</span></span>`;
		if (j < n - 1) h += '<span class="plus">+</span>';
		}
		h += '</div><div class="crow"><span class="kw sa">s.a.</span></div>';
		for (let i = 0; i < m; i++) {
		h += '<div class="crow"><span class="kw"></span>';
		for (let j = 0; j < n; j++) {
			h += `<span class="term"><input type="text" inputmode="decimal" placeholder="0" data-a="${i},${j}"><span>${names[j]}</span></span>`;
			if (j < n - 1) h += '<span class="plus">+</span>';
		}
		h += `<select data-op="${i}"><option value="le">≤</option><option value="ge">≥</option><option value="eq">=</option></select>`;
		h += `<input type="text" inputmode="decimal" placeholder="0" class="rhs" data-b="${i}"></div>`;
		}
		h += `<div class="crow nn"><span class="kw"></span>${names.join(', ')} ≥ 0</div>`;
		$('mplForm').innerHTML = h;
		state.built = true;
	}

	function readModel() {
		let bad = false;
		const get = (el) => {
		const v = parseFr(el.value);
		el.classList.toggle('bad', v === undefined);
		if (v === undefined) { bad = true; return ZERO; }
		return v;
		};
		const f = $('mplForm');
		const c = Array.from({ length: state.n }, (_, j) => get(f.querySelector(`[data-c="${j}"]`)));
		const A = [], ops = [], b = [];
		for (let i = 0; i < state.m; i++) {
		A.push(Array.from({ length: state.n }, (_, j) => get(f.querySelector(`[data-a="${i},${j}"]`))));
		ops.push(f.querySelector(`[data-op="${i}"]`).value);
		b.push(get(f.querySelector(`[data-b="${i}"]`)));
		}
		return bad ? null : { sense: state.sense, n: state.n, m: state.m, c, A, ops, b };
	}

	$('cfg').addEventListener('submit', (e) => {
		e.preventDefault();
		const clamp = (v) => Math.min(6, Math.max(1, parseInt(v, 10) || 1));
		const sense = document.querySelector('input[name="sense"]:checked').value;
		const n = clamp($('nVars').value), m = clamp($('nCons').value);
		$('nVars').value = n; $('nCons').value = m;
		const same = state.built && n === state.n && m === state.m;
		Object.assign(state, { sense, n, m });
		if (same) $('kwSense').textContent = sense === 'max' ? 'Max' : 'Min';
		else buildForm();
		$('err').hidden = true;
		goStep(2);
	});

	$('back1').addEventListener('click', () => goStep(1));
	$('edit').addEventListener('click', () => goStep(2));
	$('restart').addEventListener('click', () => { state.built = false; goStep(1); });

	$('mpl').addEventListener('submit', (e) => {
		e.preventDefault();
		const err = $('err');
		const p = readModel();
		if (!p) {
		err.textContent = 'Hay valores no válidos (marcados en el formulario). Usa números, decimales o fracciones como 3/4.';
		err.hidden = false;
		return;
		}
		try {
		render(p, solveProblem(p));
		err.hidden = true;
		goStep(3);
		} catch (ex) {
		err.textContent = ex.message;
		err.hidden = false;
		}
	});
}

if (typeof document !== 'undefined') initUI();
if (typeof module !== 'undefined') module.exports = { Fr, parseFr, solveProblem, ZERO, ONE };