const $ = (s) => document.querySelector(s),
  rd = (n) => (Math.abs(n) < 1e-10 ? 0 : +n.toFixed(10)),
  fm = (n) => String(+rd(n).toFixed(4)),
  f2 = (n) => {
    n = rd(n);
    return Number.isInteger(n) ? String(n) : n.toFixed(2);
  };
function fr(n) {
  n = rd(n);
  if (Number.isInteger(n)) return String(n);
  for (let q = 2; q <= 60; q++) {
    const p = Math.round(n * q);
    if (Math.abs(p / q - n) < 1e-9) return p + "/" + q;
  }
  return f2(n);
}
const sym = (o) => (o == "<=" ? "≤" : o == ">=" ? "≥" : "=");
const COL = [
  "#e4572e",
  "#2e86de",
  "#17a398",
  "#c06c84",
  "#f0a202",
  "#7d5ba6",
  "#4d908e",
  "#c1666b",
];
let N = 2,
  NM = ["x", "y"];
const names = (n) =>
  n == 2
    ? ["x", "y"]
    : n == 3
      ? ["x", "y", "z"]
      : Array.from({ length: n }, (_, i) => "x" + (i + 1));
const lin = (a) => {
  let s = "";
  a.forEach((k, i) => {
    if (!k) return;
    const t = (Math.abs(k) === 1 ? "" : fm(Math.abs(k))) + NM[i];
    s += s ? (k < 0 ? " - " : " + ") + t : (k < 0 ? "-" : "") + t;
  });
  return s || "0";
};
const eq = (a, c, o = "=") => `${lin(a)} ${sym(o)} ${fm(c)}`;
const pt = (p) => {
  const a = `(${p.map(fr).join(", ")})`;
  return a.includes("/") ? `${a} ≈ (${p.map(f2).join(", ")})` : a;
};
const dot = (a, b) => a.reduce((s, k, i) => s + k * b[i], 0);

/* ---------- formulario ---------- */
function addRow(r = { a: [], op: "<=", c: "" }) {
  const d = document.createElement("div");
  d.className = "row";
  d.innerHTML =
    NM.map(
      (v, i) =>
        `<input class="ca" type="number" step="any" value="${r.a[i] ?? ""}" aria-label="Coeficiente de ${v}"><span>${v}${i < N - 1 ? " +" : ""}</span>`,
    ).join("") +
    `<select aria-label="Signo">${["<=", ">=", "="].map((o) => `<option value="${o}"${o == r.op ? " selected" : ""}>${sym(o)}</option>`).join("")}</select><input class="cb" type="number" step="any" value="${r.c}" aria-label="Término independiente"><button type="button" class="x" title="Quitar restricción" aria-label="Quitar restricción">✕</button>`;
  d.querySelector(".x").onclick = () => d.remove();
  $("#rows").append(d);
}
function getForm() {
  return {
    c: [...document.querySelectorAll(".oc")].map((i) => i.value),
    r: [...document.querySelectorAll("#rows .row")].map((r) => ({
      a: [...r.querySelectorAll(".ca")].map((i) => i.value),
      op: r.querySelector("select").value,
      c: r.querySelector(".cb").value,
    })),
  };
}
function mk(n, f) {
  N = n;
  NM = names(n);
  $("#oc").innerHTML = NM.map(
    (v, i) =>
      `<input class="oc" type="number" step="any" value="${f.c[i] ?? ""}" aria-label="Coeficiente de ${v} en Z"><span>${v}${i < n - 1 ? " +" : ""}</span>`,
  ).join("");
  $("#rows").innerHTML = "";
  f.r.forEach(addRow);
}
const blank = () => ({
  c: [],
  r: [
    { a: [], op: "<=", c: "" },
    { a: [], op: "<=", c: "" },
  ],
});

/* ---------- álgebra ---------- */
function gs(M, b) {
  const n = b.length,
    A = M.map((r, i) => [...r, b[i]]);
  for (let c = 0; c < n; c++) {
    let p = c;
    for (let r = c + 1; r < n; r++)
      if (Math.abs(A[r][c]) > Math.abs(A[p][c])) p = r;
    if (Math.abs(A[p][c]) < 1e-10) return null;
    [A[c], A[p]] = [A[p], A[c]];
    for (let r = 0; r < n; r++)
      if (r != c) {
        const f = A[r][c] / A[c][c];
        for (let k = c; k <= n; k++) A[r][k] -= f * A[c][k];
      }
  }
  return A.map((r, i) => rd(r[n] / r[i]));
}
function* comb(m, k, s = 0, cur = []) {
  if (cur.length == k) {
    yield cur;
    return;
  }
  for (let i = s; i < m; i++) yield* comb(m, k, i + 1, [...cur, i]);
}
const binom = (m, k) => {
  let r = 1;
  for (let i = 1; i <= k; i++) r = (r * (m - k + i)) / i;
  return r;
};
const ok = (p, L) =>
  L.every((l) => {
    const v = dot(l.a, p),
      e = 1e-7 * (1 + Math.abs(l.c));
    return l.op == "<="
      ? v <= l.c + e
      : l.op == ">="
        ? v >= l.c - e
        : Math.abs(v - l.c) <= e;
  });
function verts(L, n) {
  const V = [];
  if (L.length < n) return V;
  for (const S of comb(L.length, n)) {
    const x = gs(
      S.map((i) => L[i].a),
      S.map((i) => L[i].c),
    );
    if (
      x &&
      ok(x, L) &&
      !V.some((v) => v.p.every((k, i) => Math.abs(k - x[i]) < 1e-7))
    )
      V.push({ p: x, S });
  }
  return V;
}

/* ---------- gráfica (2 variables) ---------- */
function clip(poly, l) {
  const f = (p) => (l.op == ">=" ? l.c - dot(l.a, p) : dot(l.a, p) - l.c),
    o = [];
  for (let i = 0; i < poly.length; i++) {
    const A = poly[i],
      B = poly[(i + 1) % poly.length],
      fa = f(A),
      fb = f(B);
    if (fa <= 0) o.push(A);
    if (fa * fb < 0) {
      const t = fa / (fa - fb);
      o.push([A[0] + t * (B[0] - A[0]), A[1] + t * (B[1] - A[1])]);
    }
  }
  return o;
}
function seg(l, [x0, x1, y0, y1]) {
  const [a, b] = l.a,
    P = [],
    add = (x, y) => {
      if (
        x >= x0 - 1e-9 &&
        x <= x1 + 1e-9 &&
        y >= y0 - 1e-9 &&
        y <= y1 + 1e-9 &&
        !P.some((q) => Math.hypot(q[0] - x, q[1] - y) < 1e-9)
      )
        P.push([x, y]);
    };
  if (b) {
    add(x0, (l.c - a * x0) / b);
    add(x1, (l.c - a * x1) / b);
  }
  if (a) {
    add((l.c - b * y0) / a, y0);
    add((l.c - b * y1) / a, y1);
  }
  return P;
}
const ns = (r) => {
  const s = r / 8,
    p = 10 ** Math.floor(Math.log10(s)),
    f = s / p;
  return p * (f < 1.5 ? 1 : f < 3.5 ? 2 : f < 7.5 ? 5 : 10);
};
function svg(A, V, F, W, iso) {
  const w = 700,
    h = 470,
    m = 46,
    [x0, x1, y0, y1] = W,
    X = (x) => m + ((x - x0) / (x1 - x0)) * (w - 2 * m),
    Y = (y) => h - m - ((y - y0) / (y1 - y0)) * (h - 2 * m);
  let s = `<svg viewBox="0 0 ${w} ${h}" role="img" aria-label="Gráfica de la región factible"><rect x="${m}" y="${m}" width="${w - 2 * m}" height="${h - 2 * m}" fill="#fff" stroke="var(--line)"/>`;
  let st = ns(x1 - x0);
  for (let k = Math.ceil(x0 / st); k <= Math.floor(x1 / st); k++) {
    const r = rd(k * st);
    s += `<line x1="${X(r)}" x2="${X(r)}" y1="${m}" y2="${h - m}" stroke="var(--line)"/><text x="${X(r)}" y="${h - m + 16}" text-anchor="middle">${fm(r)}</text>`;
  }
  st = ns(y1 - y0);
  for (let k = Math.ceil(y0 / st); k <= Math.floor(y1 / st); k++) {
    const r = rd(k * st);
    s += `<line y1="${Y(r)}" y2="${Y(r)}" x1="${m}" x2="${w - m}" stroke="var(--line)"/><text x="${m - 6}" y="${Y(r) + 4}" text-anchor="end">${fm(r)}</text>`;
  }
  if (x0 < 0 && x1 > 0)
    s += `<line x1="${X(0)}" x2="${X(0)}" y1="${m}" y2="${h - m}" stroke="var(--ink)" stroke-width="1.5"/>`;
  if (y0 < 0 && y1 > 0)
    s += `<line y1="${Y(0)}" y2="${Y(0)}" x1="${m}" x2="${w - m}" stroke="var(--ink)" stroke-width="1.5"/>`;
  if (F.length > 2)
    s += `<polygon points="${F.map((p) => X(p[0]) + "," + Y(p[1])).join(" ")}" fill="#8fcbff" fill-opacity=".5"/>`;
  A.filter((l) => !l.ax).forEach((l, k) => {
    const P = seg(l, W);
    if (P.length > 1)
      s += `<line x1="${X(P[0][0])}" y1="${Y(P[0][1])}" x2="${X(P[1][0])}" y2="${Y(P[1][1])}" stroke="${COL[k % 8]}" stroke-width="2.4"/>`;
  });
  if (iso) {
    const P = seg(iso, W);
    if (P.length > 1)
      s += `<line x1="${X(P[0][0])}" y1="${Y(P[0][1])}" x2="${X(P[1][0])}" y2="${Y(P[1][1])}" stroke="var(--ink)" stroke-width="1.6" stroke-dasharray="6 5"/>`;
  }
  V.forEach(
    (v) =>
      (s += `<circle cx="${X(v.p[0])}" cy="${Y(v.p[1])}" r="5" fill="var(--ink)"/><text class="vl" x="${X(v.p[0]) + 8}" y="${Y(v.p[1]) - 8}">${v.l}</text>`),
  );
  return s + "</svg>";
}

/* ---------- pasos de cada vértice ---------- */
function steps(L, v) {
  const p = v.p,
    l = v.S.map((i) => L[i]),
    e = (q) => eq(q.a, q.c);
  if (N > 2)
    return (
      l.map(e).join("<br>") +
      `<br>⇒ ${NM.map((n, i) => n + " = " + fr(p[i])).join(", ")}`
    );
  const [l1, l2] = l;
  if (l1.ax && l2.ax) return "Se cruzan los ejes: x = 0 y y = 0.";
  if (l1.ax || l2.ax) {
    const u = l1.ax ? l1 : l2,
      o = l1.ax ? l2 : l1;
    return u.a[1] === 0
      ? `${e(u)}; en ${e(o)} ⇒ y = ${fr(p[1])}`
      : `${e(u)}; en ${e(o)} ⇒ x = ${fr(p[0])}`;
  }
  const h = !l1.a[0] ? l1 : !l2.a[0] ? l2 : null,
    vt = !l1.a[1] ? l1 : !l2.a[1] ? l2 : null;
  if (h) {
    const o = h === l1 ? l2 : l1;
    return `${e(h)} ⇒ y = ${fr(p[1])}. En ${e(o)} ⇒ x = ${fr(p[0])}`;
  }
  if (vt) {
    const o = vt === l1 ? l2 : l1;
    return `${e(vt)} ⇒ x = ${fr(p[0])}. En ${e(o)} ⇒ y = ${fr(p[1])}`;
  }
  const m = -l2.a[0] / l1.a[0],
    k = l2.a[1] + m * l1.a[1],
    r = l2.c + m * l1.c;
  return `(${e(l1)})·(${fr(m)}) &nbsp;+&nbsp; (${e(l2)}) ⇒ ${fm(k)}y = ${fm(r)} ⇒ y = ${fr(p[1])}<br>Sustituyendo: x = ${fr(p[0])}`;
}

/* ---------- resolver ---------- */
function solve() {
  const n = N,
    mx = $("#tipo").value == "max",
    sg = mx ? 1 : -1,
    f = getForm(),
    num = (s) => (s === "" ? 0 : +s),
    nn = $("#nn").checked,
    c = f.c.map(num);
  while (c.length < n) c.push(0);
  const L = [];
  let err = "";
  f.r.forEach((r, k) => {
    if (r.c === "" && r.a.every((v) => v === "")) return;
    const a = r.a.map(num);
    if (r.c === "")
      err = `Escribe el término independiente de la restricción ${k + 1}.`;
    else if (a.every((v) => !v))
      err = `La restricción ${k + 1} no tiene variables.`;
    else L.push({ a, c: +r.c, op: r.op });
  });
  if (!err && !L.length) err = "Agrega al menos una restricción.";
  if (!err && c.every((v) => !v)) err = "Escribe al menos un coeficiente en Z.";
  if (!err && binom(L.length + 2 * n, n) > 6e5)
    err =
      "Demasiadas restricciones para este número de variables. Reduce alguna de las dos.";
  if (err) return ($("#out").innerHTML = `<div class="card bad">${err}</div>`);
  const U = (i) => NM.map((_, j) => +(i == j)),
    AX = nn ? NM.map((_, i) => ({ a: U(i), c: 0, op: ">=", ax: 1 })) : [],
    A = L.concat(AX);
  let V = verts(A, n);
  V.forEach((v) => (v.z = dot(c, v.p)));
  const cone = V.length
    ? verts(
        A.map((l) => ({ ...l, c: 0 })).concat(
          NM.map((_, i) => ({ a: U(i), c: 1, op: "<=" })),
          nn ? [] : NM.map((_, i) => ({ a: U(i), c: -1, op: ">=" })),
        ),
        n,
      )
    : [];
  const unb = cone.some((v) => sg * dot(c, v.p) > 1e-9),
    ray = cone.some(
      (v) => Math.hypot(...v.p) > 1e-9 && Math.abs(dot(c, v.p)) < 1e-9,
    );
  if (V.length && n == 2) {
    const mx0 = V.reduce((s, v) => s + v.p[0], 0) / V.length,
      my0 = V.reduce((s, v) => s + v.p[1], 0) / V.length;
    V.sort(
      (u, v) =>
        Math.atan2(v.p[1] - my0, v.p[0] - mx0) -
        Math.atan2(u.p[1] - my0, u.p[0] - mx0),
    );
    const k0 = V.reduce(
      (b, v, i) => (Math.hypot(...v.p) < Math.hypot(...V[b].p) ? i : b),
      0,
    );
    V = V.slice(k0).concat(V.slice(0, k0));
  }
  V.forEach((v, i) => (v.l = "ABCDEFGHIJKLMNOPQRSTUVWXYZ"[i] || "V" + (i + 1)));
  let ties = [],
    best = null;
  if (V.length && !unb) {
    best = Math[mx ? "max" : "min"](...V.map((v) => v.z));
    ties = V.filter((v) => Math.abs(v.z - best) <= 1e-7 * (1 + Math.abs(best)));
    ties.forEach((v) => (v.opt = 1));
  }
  let H = `<div class="card"><h2>1. Problema</h2><p class="m">${mx ? "Max" : "Min"} Z = ${lin(c)}<br>Sujeto a:<br>${L.map((l) => "&nbsp;&nbsp;" + eq(l.a, l.c, l.op)).join("<br>")}${nn ? `<br>&nbsp;&nbsp;${NM.join(", ")} ≥ 0` : ""}</p></div>`;
  H += `<div class="card"><h2>2. Evaluar: cortes de cada recta con los ejes</h2>${L.map(
    (l) => {
      const q = [];
      for (let i = n - 1; i >= 0; i--)
        if (l.a[i]) {
          const p = NM.map(() => 0);
          p[i] = l.c / l.a[i];
          q.push(`(${p.map(fr).join(", ")})`);
        }
      return `<p class="m">${eq(l.a, l.c, l.op)} ⇒ ${q.join(" , ")}</p>`;
    },
  ).join("")}</div>`;
  if (n == 2) {
    let P = V.map((v) => v.p).concat([[0, 0]]);
    if (!V.length || unb)
      L.forEach((l) => {
        if (l.a[0]) P.push([l.c / l.a[0], 0]);
        if (l.a[1]) P.push([0, l.c / l.a[1]]);
      });
    let x0 = Math.min(...P.map((p) => p[0])),
      x1 = Math.max(...P.map((p) => p[0])),
      y0 = Math.min(...P.map((p) => p[1])),
      y1 = Math.max(...P.map((p) => p[1]));
    const sx = Math.max(x1 - x0, 1),
      sy = Math.max(y1 - y0, 1);
    x0 -= 0.12 * sx;
    x1 += 0.12 * sx;
    y0 -= 0.12 * sy;
    y1 += 0.12 * sy;
    const W = [x0, x1, y0, y1];
    let F = [];
    if (V.length) {
      F = [
        [x0, y0],
        [x1, y0],
        [x1, y1],
        [x0, y1],
      ];
      A.filter((l) => l.op != "=").forEach((l) => (F = clip(F, l)));
    }
    const iso = ties.length ? { a: c, c: best } : null;
    H += `<div class="card"><h2>3. Gráfica</h2>${svg(A, V, F, W, iso)}<div class="lg">${L.map((l, k) => `<span><i style="background:${COL[k % 8]}"></i>${eq(l.a, l.c, l.op)}</span>`).join("")}${F.length > 2 ? '<span><i style="background:#8fcbff"></i>región factible</span>' : ""}${iso ? "<span>- - - Z = Z*</span>" : ""}</div></div>`;
  } else
    H += `<div class="card"><h2>3. Gráfica</h2><p class="hint">Solo se puede dibujar con 2 variables. Con ${n} variables se aplica el mismo criterio: cada vértice es la intersección de ${n} restricciones, se descartan los que no cumplen todas y se evalúa Z en los que quedan.</p></div>`;
  if (!V.length) {
    H += `<div class="card"><div class="res no"><b>No hay región factible</b> ∴ no hay solución.<br>Ninguna combinación de valores cumple todas las restricciones a la vez.${nn ? "" : " (Si la región no tiene vértices, activa «Todas las variables ≥ 0» para usar el método.)"}</div></div>`;
    return ($("#out").innerHTML = H);
  }
  H += `<div class="card"><h2>4. Vértices de la región factible</h2>${V.map((v) => `<div class="v"><p><b>${v.l}</b> ${pt(v.p)}</p><p class="m">${steps(A, v)}</p></div>`).join("")}</div>`;
  H += `<div class="card"><h2>5. Evaluar Z en cada vértice</h2><div class="box"><table><tr><th>Punto</th><th>(${NM.join(", ")})</th><th>Z = ${lin(c)}</th></tr>${V.map(
    (v) =>
      `<tr class="${v.opt ? "best" : ""}"><td>${v.l}</td><td>${pt(v.p)}</td><td class="m">${c
        .map((k, i) => (k ? `${fm(k)}(${fr(v.p[i])})` : null))
        .filter(Boolean)
        .join(" + ")} = ${f2(v.z)}</td></tr>`,
  ).join("")}</table></div></div>`;
  const sol = (p) => NM.map((v, i) => `${v} = ${fr(p[i])}`).join(", ");
  let C;
  if (unb)
    C = `<div class="res no"><b>Solución no acotada.</b> La región factible es abierta y Z puede ${mx ? "crecer hasta +∞" : "decrecer hasta −∞"} sin llegar a un ${mx ? "máximo" : "mínimo"} finito.</div>`;
  else if (ties.length > 1)
    C = `<div class="res"><b>Múltiples soluciones óptimas</b> con Z* = ${f2(best)}.<br>Empatan los vértices ${ties.map((v) => v.l + " " + pt(v.p)).join(" y ")}.<br>${ties.length == 2 ? `Todo punto del segmento ${ties[0].l}–${ties[1].l} es óptimo: X = λ·${ties[0].l} + (1 − λ)·${ties[1].l}, con 0 ≤ λ ≤ 1.` : "Todos los puntos de la región (arista o cara) que une esos vértices son óptimos."}${ray ? "<br>Además la región es abierta en esa dirección: también hay óptimos sobre una semirrecta." : ""}</div>`;
  else
    C = `<div class="res"><b>Solución óptima única:</b> X* = ${pt(ties[0].p)}${n > 2 ? " → " + sol(ties[0].p) : ""}<br>Z* = ${f2(best)}${ray ? "<br>Aviso: la región es abierta y hay óptimos adicionales sobre una semirrecta." : ""}</div>`;
  $("#out").innerHTML =
    H + `<div class="card"><h2>6. Conclusión</h2>${C}</div>`;
}

$("#solve").onclick = () => {
  solve();
  $("#out").scrollIntoView({ behavior: "smooth" });
};
$("#add").onclick = () => addRow();
$("#clr").onclick = () => {
  mk(N, blank());
  $("#out").innerHTML = "";
};
mk(2, blank());
