'use strict';
/* Núcleo compartido por el Método simplex (tabla) y la Penalización por M.
   - Fracciones exactas (BigInt) y números de la forma a + bM (M = número muy grande).
   - Motor de tablas simplex, render paso a paso y formulario. */

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
	eq(o) { return this.n === o.n && this.d === o.d; }
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

/** Número a + b·M, con M mucho mayor que cualquier número real. Se compara primero b y luego a. */
class MV {
	constructor(a = ZERO, b = ZERO) { this.a = a; this.b = b; }
	add(o) { return new MV(this.a.add(o.a), this.b.add(o.b)); }
	sub(o) { return new MV(this.a.sub(o.a), this.b.sub(o.b)); }
	mulFr(f) { return new MV(this.a.mul(f), this.b.mul(f)); }
	neg() { return new MV(this.a.neg(), this.b.neg()); }
	isZero() { return this.a.isZero() && this.b.isZero(); }
	hasM() { return !this.b.isZero(); }
	sign() { const s = this.b.sign(); return s !== 0 ? s : this.a.sign(); }
	cmp(o) { const c = this.b.cmp(o.b); return c !== 0 ? c : this.a.cmp(o.a); }
}

const fs = (f) => f.toString().replace('-', '−');
const frM = (b) => (b.isOne() ? 'M' : b.d === 1n ? `${b}M` : `(${b})M`);

/** Texto de un número a + bM: "2 − M", "−3/2 + M", "−10M", "M", "5/2". */
function mstr(x) {
	const { a, b } = x;
	if (b.isZero()) return fs(a);
	if (a.isZero()) return (b.sign() < 0 ? '−' : '') + frM(b.abs());
	return `${fs(a)} ${b.sign() < 0 ? '−' : '+'} ${frM(b.abs())}`;
}

const approx = (f) => f.d === 1n ? fs(f) : `${fs(f)} ≈ ${f.toNumber().toFixed(4).replace(/\.?0+$/, '')}`;

/* ---------- Construcción del modelo (forma estándar) ---------- */

const SLACK_LETTERS = ['U', 'V', 'W', 'S', 'T', 'R'];
const sub = (s, i) => `${s}<sub>${i}</sub>`;

function decisionNames(mode, n) {
	if (mode === 'simplex' && n <= 2) return ['x', 'y'].slice(0, n);
	return Array.from({ length: n }, (_, j) => sub('x', j + 1));
}

function buildModel(p, mode) {
	const { n, m } = p;
	const notes = [];
	let c = p.c.slice();
	if (p.sense === 'min') {
		c = c.map((v) => v.neg());
		notes.push('La función es de minimizar: se convierte en maximizar Z′ = −Z (al final Z* = −Z′*).');
	}
	const A = p.A.map((r) => r.slice());
	const b = p.b.slice();
	const ops = p.ops.slice();
	for (let i = 0; i < m; i++) {
		if (b[i].sign() < 0) {
			if (mode === 'simplex') {
				throw new Error('En el método simplex el lado derecho de cada restricción debe ser ≥ 0. Si hay restricciones con lado derecho negativo, ≥ o =, usa la Penalización por M.');
			}
			A[i] = A[i].map((v) => v.neg());
			b[i] = b[i].neg();
			ops[i] = ops[i] === 'le' ? 'ge' : ops[i] === 'ge' ? 'le' : 'eq';
			notes.push(`Restricción ${i + 1}: el lado derecho era negativo; se multiplica por −1 (y se invierte la desigualdad).`);
		}
	}

	const dec = decisionNames(mode, n);
	const cols = dec.map((name) => ({ name, kind: 'dec' }));
	const slackCol = Array(m).fill(-1), artCol = Array(m).fill(-1);
	let k = 0;
	const nextName = () => (mode === 'simplex' && n <= 2 ? SLACK_LETTERS[k] : sub('x', cols.length + 1));
	for (let i = 0; i < m; i++) {
		if (ops[i] === 'eq') continue;
		slackCol[i] = cols.length;
		cols.push({ name: nextName(), kind: ops[i] === 'le' ? 'slack' : 'surplus' });
		k++;
	}
	for (let i = 0; i < m; i++) {
		if (ops[i] === 'le') continue;
		artCol[i] = cols.length;
		cols.push({ name: sub('x', cols.length + 1), kind: 'art' });
	}
	const N = cols.length;

	const T = A.map((row, i) => {
		const r = Array(N + 1).fill(ZERO);
		row.forEach((v, j) => { r[j] = v; });
		if (slackCol[i] >= 0) r[slackCol[i]] = ops[i] === 'le' ? ONE : ONE.neg();
		if (artCol[i] >= 0) r[artCol[i]] = ONE;
		r[N] = b[i];
		return r;
	});
	const basis = A.map((_, i) => (ops[i] === 'le' ? slackCol[i] : artCol[i]));

	// Fila Z:  Z′ − c·x = 0, y +M por cada variable artificial (penalización).
	const zRaw = Array.from({ length: N + 1 }, (_, j) => {
		if (j < n) return new MV(c[j].neg());
		if (j < N && cols[j].kind === 'art') return new MV(ZERO, ONE);
		return new MV();
	});

	const rowsArt = [];
	for (let i = 0; i < m; i++) if (artCol[i] >= 0) rowsArt.push(i);
	let z = zRaw, zOp = null;
	if (rowsArt.length) {
		z = zRaw.map((v, j) => rowsArt.reduce((acc, i) => acc.sub(new MV(ZERO, T[i][j])), v));
		const lst = rowsArt.map((i) => sub('R', i + 1)).join(' + ');
		zOp = `R<sub>Z</sub> − M${rowsArt.length > 1 ? `(${lst})` : `·${lst}`}`;
	}

	return { mode, p, n, m, c, A, b, ops, cols, N, T, basis, zRaw, z, zOp, hasArt: rowsArt.length > 0, notes, dec, slackCol, artCol };
}

/* ---------- Motor simplex ---------- */

const coefTxt = (f) => (f.isOne() ? '' : `${f}·`);

function opLabel(rowName, f, pivName) {
	// fila_nueva = fila − f·fila_pivote
	if (f.isZero()) return 'sin cambio';
	const mag = coefTxt(f.abs());
	return `${rowName} ${f.sign() > 0 ? '−' : '+'} ${mag}${pivName}`;
}

function pivotOnce(snap, e, l, model) {
	const { N, m } = model;
	const rows = snap.rows.map((r) => r.slice());
	const p = rows[l][e];
	rows[l] = rows[l].map((v) => v.div(p));
	const pivName = sub('R', l + 1);
	const ops = Array(m).fill(null);
	ops[l] = p.isOne() ? 'sin cambio' : `${pivName} ÷ ${p}`;
	for (let i = 0; i < m; i++) {
		if (i === l) continue;
		const f = rows[i][e];
		ops[i] = opLabel(sub('R', i + 1), f, pivName);
		if (!f.isZero()) rows[i] = rows[i].map((v, j) => v.sub(f.mul(rows[l][j])));
	}
	const zc = snap.z[e];
	let zOp;
	if (zc.isZero()) zOp = 'sin cambio';
	else if (zc.hasM()) zOp = `R<sub>Z</sub> + (${mstr(zc.neg())})·${pivName}`;
	else zOp = `R<sub>Z</sub> ${zc.a.sign() < 0 ? '+' : '−'} ${coefTxt(zc.a.abs())}${pivName}`;
	const z = snap.z.map((v, j) => v.sub(zc.mulFr(rows[l][j])));
	const basis = snap.basis.slice();
	basis[l] = e;
	return { z, zRaw: null, rows, basis, ops, zOp };
}

function ratiosFor(snap, e, N) {
	return snap.rows.map((r) => (r[e].sign() > 0 ? r[N].div(r[e]) : null));
}

function chooseLeaving(ratios) {
	let l = -1;
	ratios.forEach((q, i) => { if (q !== null && (l < 0 || q.cmp(ratios[l]) < 0)) l = i; });
	return l;
}

function solutionVector(snap, N) {
	const x = Array(N).fill(ZERO);
	snap.basis.forEach((col, i) => { x[col] = snap.rows[i][N]; });
	return x;
}

function runSimplex(model) {
	const { N, cols } = model;
	const snaps = [{ z: model.z, zRaw: model.hasArt ? model.zRaw : null, rows: model.T, basis: model.basis, ops: null, zOp: model.zOp }];
	let status = null;
	for (let it = 0; it < 200 && !status; it++) {
		const cur = snaps[snaps.length - 1];
		let e = -1;
		for (let j = 0; j < N; j++) if (cur.z[j].sign() < 0 && (e < 0 || cur.z[j].cmp(cur.z[e]) < 0)) e = j;
		if (e < 0) { status = 'optimal'; break; }
		const ratios = ratiosFor(cur, e, N);
		const l = chooseLeaving(ratios);
		cur.enter = e; cur.ratios = ratios;
		if (l < 0) { cur.leave = -1; status = 'unbounded'; break; }
		cur.leave = l;
		snaps.push(pivotOnce(cur, e, l, model));
	}
	if (!status) throw new Error('El método no converge (posible ciclado).');

	const last = snaps[snaps.length - 1];
	const x = solutionVector(last, N);
	let outcome = status, alt = null, altInfo = null;

	if (status === 'optimal') {
		const artPos = cols.some((c, j) => c.kind === 'art' && x[j].sign() > 0);
		if (artPos) outcome = 'infeasible';
		else {
			outcome = 'unique';
			// ¿Variable no básica (no artificial) con coeficiente 0 en Z? → posibles soluciones múltiples.
			let ray = false;
			for (let j = 0; j < N; j++) {
				if (last.basis.includes(j) || cols[j].kind === 'art' || !last.z[j].isZero()) continue;
				const ratios = ratiosFor(last, j, N);
				const l = chooseLeaving(ratios);
				if (l < 0) { ray = true; continue; }
				const cand = pivotOnce(last, j, l, model);
				const xc = solutionVector(cand, N);
				if (xc.some((v, i) => !v.eq(x[i]))) {
					last.enter = j; last.leave = l; last.ratios = ratios; last.altPivot = true;
					cand.title = 'Solución óptima alternativa';
					snaps.push(cand);
					alt = xc; altInfo = { j };
					outcome = 'multiple';
					break;
				}
			}
			if (outcome === 'unique' && ray) outcome = 'multiple-ray';
		}
	}
	return { snaps, status: outcome, x, alt, last: snaps[snaps.length - 1 - (alt ? 1 : 0)] };
}

function solveProblem(p, mode) {
	const model = buildModel(p, mode);
	return { model, run: runSimplex(model) };
}

/* ---------- Render ---------- */

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

/** Ecuación de la fila Z:  Z′ + 2x₁ + Mx₅ = 0 */
function zEquationHTML(label, zc, names) {
	let out = label;
	zc.forEach((v, j) => {
		if (j >= names.length || v.isZero()) return;
		const neg = v.sign() < 0;
		const abs = neg ? v.neg() : v;
		let t;
		if (abs.hasM()) t = abs.a.isZero() ? (abs.b.isOne() ? 'M' : `${abs.b.d === 1n ? abs.b : `(${abs.b})`}M`) : `(${mstr(abs)})`;
		else t = abs.a.isOne() ? '' : abs.a.d === 1n ? abs.a.toString() : `(${abs.a})`;
		out += `${neg ? ' − ' : ' + '}${t}${names[j]}`;
	});
	return `${out} = 0`;
}

function mplHTML({ sense, z, c, names, A, ops, b, nn }) {
	return `<div class="mpl">
		<div class="mpl-row"><span class="kw">${sense}</span><span>${z} = ${linearHTML(c, names)}</span></div>
		<div class="mpl-row"><span class="kw sa">s.a.</span><div class="tscroll">${systemHTML(A, names, ops, b)}</div></div>
		<div class="mpl-row"><span class="kw"></span><span class="nn">${nn.join(', ')} ≥ 0</span></div>
	</div>`;
}

const section = (num, title, body) => `<div class="sec"><h3><span class="num">${num}</span>${title}</h3>${body}</div>`;

function tableauHTML(idx, snap, model, zL) {
	const { cols, N, m } = model;
	const showRatio = snap.enter !== undefined && snap.enter !== null;
	let h = `<div class="blk"><h4>Tabla ${idx + 1}${snap.title ? ' · ' + snap.title : ''}</h4><div class="tscroll"><table class="simp"><thead><tr><th>Operación</th><th>Base</th>`;
	h += cols.map((c, j) => `<th class="${showRatio && snap.enter === j ? 'ent' : ''}">${c.name}</th>`).join('');
	h += '<th>Solución</th><th>Cociente</th></tr></thead><tbody>';
	const zRow = (z, label, op, cls) => `<tr class="zrow ${cls}"><td class="op">${op || ''}</td><td class="bs">${label}</td>` +
		z.map((v) => `<td>${mstr(v)}</td>`).join('') + '<td></td></tr>';
	if (snap.zRaw) {
		h += zRow(snap.zRaw, `${zL} <small>(inicial)</small>`, '', '');
		h += zRow(snap.z, `${zL} <small>(ajustada)</small>`, snap.zOp, '');
	} else {
		h += zRow(snap.z, zL, snap.zOp, '');
	}
	snap.rows.forEach((r, i) => {
		const isLeave = showRatio && snap.leave === i;
		h += `<tr class="${isLeave ? 'lev' : ''}"><td class="op">${snap.ops ? snap.ops[i] : ''}</td><td class="bs">${cols[snap.basis[i]].name}</td>`;
		h += r.slice(0, N + 1).map((v, j) => `<td class="${isLeave && snap.enter === j ? 'pivot' : ''}">${fs(v)}</td>`).join('');
		let rat = '';
		if (showRatio) {
			const q = snap.ratios[i];
			rat = q === null ? '—' : `${fs(r[N])}/${fs(r[snap.enter])} = ${fs(q)}`;
		}
		h += `<td class="rat">${rat}</td></tr>`;
	});
	h += '</tbody></table></div>';
	if (showRatio) {
		const en = cols[snap.enter].name;
		if (snap.leave < 0) {
			h += `<p class="step-note">Entra ${en}: su columna no tiene valores positivos, no hay cociente.</p>`;
		} else {
			const lv = cols[snap.basis[snap.leave]].name;
			const zc = snap.z[snap.enter];
			h += snap.altPivot
				? `<p class="step-note">El coeficiente de ${en} en Z es 0: al hacerlo entrar se obtiene otra solución óptima. <b>Entra ${en}</b> · <b>Sale ${lv}</b> (cociente mínimo = ${fs(snap.ratios[snap.leave])}).</p>`
				: `<p class="step-note">Entra la de coeficiente más negativo en Z (${en}, ${mstr(zc)}). Sale la del cociente mínimo (${fs(snap.ratios[snap.leave])}). <b>Entra ${en}</b> · <b>Sale ${lv}</b>.</p>`;
		}
	}
	return h + '</div>';
}

function standardHTML(p, model, zL) {
	const { cols, N, notes, mode } = model;
	const names = cols.map((c) => c.name);
	const nt = [...notes];
	model.ops.forEach((op, i) => {
		const k = i + 1;
		const s = model.slackCol[i] >= 0 ? names[model.slackCol[i]] : null;
		const a = model.artCol[i] >= 0 ? names[model.artCol[i]] : null;
		if (op === 'le') nt.push(`Restricción ${k} (≤): se suma la variable de holgura ${s}.`);
		else if (op === 'ge') nt.push(`Restricción ${k} (≥): se resta la variable de exceso ${s} y se suma la variable artificial ${a}.`);
		else nt.push(`Restricción ${k} (=): se suma la variable artificial ${a}.`);
	});
	const eqs = mplHTML({
		sense: 'Max', z: zL, c: model.c.concat(Array(N - model.n).fill(ZERO)), names,
		A: model.T.map((r) => r.slice(0, N)), ops: model.T.map(() => '='), b: model.T.map((r) => r[N]), nn: names,
	});
	let h = `<ul class="notes">${nt.map((t) => `<li>${t}</li>`).join('')}</ul>${eqs}`;
	h += `<p class="zeq">${mode === 'm' ? 'Función objetivo penalizada' : 'Función objetivo'}: <b>${zEquationHTML(zL, model.zRaw, names)}</b></p>`;
	if (model.hasArt) {
		h += '<p>Cada variable artificial se penaliza con <b>M</b> (un número muy grande). Para que las artificiales queden en la base se elimina M de la fila Z restando M por cada fila que tenga una variable artificial.</p>';
	}
	return h;
}

function resultHTML(p, model, run) {
	const isMin = p.sense === 'min';
	const zL = isMin ? 'Z′' : 'Z';
	const { status, x, alt, snaps } = run;
	const last = run.last;
	const xs = (v) => `(${v.map(approx).join(', ')})`;
	const zv = last.z[model.N].a;
	if (status === 'infeasible') {
		const bad = model.cols.map((c, j) => ({ c, j })).filter(({ c, j }) => c.kind === 'art' && x[j].sign() > 0).map(({ c, j }) => `${c.name} = ${approx(x[j])}`);
		return `<div class="result"><div class="rt">Sin solución factible</div><div>Al terminar, una variable artificial sigue en la base con valor distinto de 0 (${bad.join(', ')}), así que las restricciones no se pueden cumplir a la vez.</div></div>`;
	}
	if (status === 'unbounded') {
		return `<div class="result"><div class="rt">Solución no acotada</div><div>La columna de la variable que entra no tiene valores positivos: Z puede ${isMin ? 'disminuir' : 'crecer'} sin límite.</div></div>`;
	}
	const zFinal = isMin ? zv.neg() : zv;
	const zLines = isMin
		? `<div>→ Z′* = ${approx(zv)}</div><div>→ Z* = −(${fs(zv)}) = ${approx(zFinal)}</div>`
		: `<div>→ Z* = ${approx(zFinal)}</div>`;
	const artNote = model.hasArt ? '<div>Las variables artificiales valen 0, por lo que la solución es real.</div>' : '';
	if (status === 'unique') {
		return `<div class="result"><div class="rt">Solución única</div><div>→ x* = ${xs(x)}</div>${zLines}${artNote}</div>`;
	}
	const extra = status === 'multiple-ray'
		? '<div>Además existe una dirección no acotada de soluciones óptimas (la región no está acotada).</div>'
		: '<div>Cualquier combinación convexa de ambas soluciones también es óptima.</div>';
	const second = alt ? `<div>→ x*<sub>2</sub> = ${xs(alt)}</div>` : '';
	return `<div class="result"><div class="rt">Soluciones óptimas múltiples</div><div>→ x*<sub>1</sub> = ${xs(x)}</div>${second}${zLines}${extra}${artNote}</div>`;
}

function render(p, res) {
	const { model, run } = res;
	const isMin = p.sense === 'min';
	const zL = isMin ? 'Z′' : 'Z';
	let h = '';
	h += section(1, 'Planteamiento del problema', mplHTML({
		sense: isMin ? 'Min' : 'Max', z: 'Z', c: p.c, names: model.dec, A: p.A,
		ops: p.ops.map((o) => SYM[o]), b: p.b, nn: model.dec,
	}));
	h += section(2, 'Forma estándar', standardHTML(p, model, zL));
	h += section(3, 'Tablas simplex',
		`<p>${model.hasArt ? 'La base inicial está formada por las variables de holgura y las artificiales.' : 'La base inicial está formada por las variables de holgura.'} Se repite hasta que no haya coeficientes negativos en la fila Z.</p>` +
		run.snaps.map((s, i) => tableauHTML(i, s, model, zL)).join('') +
		(run.status === 'unbounded' ? '' : '<p class="legend">Celda resaltada = elemento pivote. “Operación” indica cómo se obtuvo cada fila a partir de la tabla anterior.</p>'));
	h += section(4, 'Solución', resultHTML(p, model, run));
	document.getElementById('result').innerHTML = h;
}

/* ---------- Interfaz ---------- */

function initSimplexUI(mode) {
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
		const names = decisionNames(mode, n);
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
			h += mode === 'simplex'
				? `<span class="opfix" data-op="${i}" data-val="le">≤</span>`
				: `<select data-op="${i}"><option value="le">≤</option><option value="ge">≥</option><option value="eq">=</option></select>`;
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
			const opEl = f.querySelector(`[data-op="${i}"]`);
			ops.push(opEl.value || opEl.dataset.val);
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
			render(p, solveProblem(p, mode));
			err.hidden = true;
			goStep(3);
		} catch (ex) {
			err.textContent = ex.message;
			err.hidden = false;
		}
	});
}

if (typeof module !== 'undefined') module.exports = { Fr, MV, parseFr, solveProblem, ZERO, ONE, mstr };
