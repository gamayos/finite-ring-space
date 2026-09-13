// Exact verification of the finite Hopf fibration and its section: the
// observable frame group PGL2(F_p) fibered by the boost torus C_{p+1},
// with the Borel (the cone chart) a global transversal. Checked at the
// minimal non-trivial Subject p = 13 and, Omega-blind, at the trivial
// Subject p = 5. Every check is integer arithmetic; any FAIL exits
// nonzero.
'use strict';
let fails = 0;
const ok = (name, cond) => { console.log((cond ? 'PASS ' : 'FAIL ') + name); if (!cond) fails++; };

function hopf(P, NS){                       // NS: a fixed non-square mod P
  const md = a => ((a % P) + P) % P;
  const inv = [0]; for (let a = 1; a < P; a++) inv.push(
    (() => { for (let b = 1; b < P; b++) if (md(a * b) === 1) return b; })());
  // PGL2: invertible 2x2 mod scalars; canonical: first nonzero entry -> 1
  const canon = m => {
    for (const x of m) if (md(x)){ const f = inv[md(x)];
      return m.map(v => md(v * f)).join(','); }
  };
  const mul = (m, n) => {
    const [a,b,c,d] = m, [e,f,g,h] = n;
    return [a*e+b*g, a*f+b*h, c*e+d*g, c*f+d*h].map(md);
  };
  const det = m => md(m[0]*m[3] - m[1]*m[2]);
  const G = new Set();
  for (let a = 0; a < P; a++) for (let b = 0; b < P; b++)
    for (let c = 0; c < P; c++) for (let d = 0; d < P; d++)
      if (det([a,b,c,d])) G.add(canon([a,b,c,d]));
  // the Borel: the stabilizer of the horizon class [1:0] = the affine group x -> ax + b
  const B = new Set();
  for (let a = 1; a < P; a++) for (let b = 0; b < P; b++)
    B.add(canon([a, b, 0, 1]));
  // the boost torus: the image of K* for K = F_p[w], w^2 = NS
  const T = new Set();
  for (let x = 0; x < P; x++) for (let y = 0; y < P; y++)
    if ((x || y) && det([x, md(NS*y), y, x]))
      T.add(canon([x, md(NS*y), y, x]));
  const Tm = [...T].map(s => s.split(',').map(Number));
  // the action on P1 = F_p + the horizon class [1:0]
  const act = (m, q) => {
    const [a,b,c,d] = m;
    if (q === P) return md(c) === 0 ? P : md(a * inv[md(c)]);
    const num = md(a*q + b), den = md(c*q + d);
    return den === 0 ? P : md(num * inv[den]);
  };
  const I = canon([1,0,0,1]);
  const free = Tm.every(t => canon(t) === I ||
    [...Array(P + 1).keys()].every(q => act(t, q) !== q));
  // unique factorization g = b t
  const prods = new Set(); let dup = false;
  for (const bs of B){ const bm = bs.split(',').map(Number);
    for (const t of Tm){ const g = canon(mul(bm, t));
      if (prods.has(g)) dup = true; prods.add(g); } }
  // the fibers: right T-cosets, each meeting B exactly once
  const fibers = new Set(); let onceEach = true;
  for (const gs of G){ const gm = gs.split(',').map(Number);
    const cs = Tm.map(t => canon(mul(gm, t))).sort().join('|');
    fibers.add(cs); }
  for (const cs of fibers){
    const hit = cs.split('|').filter(s => B.has(s)).length;
    if (hit !== 1) onceEach = false; }
  // the fiber coordinate is the horizon circle: t -> t([1:0]) bijects
  // T with P1, the shell's cells plus the horizon class [1:0]
  const orb = new Set(Tm.map(t => act(t, P)));
  return { P, G: G.size, B: B.size, T: T.size, free,
           unique: !dup && prods.size === G.size,
           fibers: fibers.size, onceEach, orbP1: orb.size };
}

for (const [P, NS] of [[13, 2], [5, 2]]){
  const H = hopf(P, NS);
  const n = P * (P - 1) * (P + 1);
  ok(`p = ${P}: the observable frame group PGL2 has (p-1)p(p+1) = ${n} `+
     `elements, the Borel p(p-1) = ${P*(P-1)}, the boost torus p+1 = ${P+1}`,
     H.G === n && H.B === P*(P-1) && H.T === P+1);
  ok(`p = ${P}: the boost torus is fixed-point-free on P1: the boosts `+
     `change every observer`, H.free);
  ok(`p = ${P}: unique factorization: every frame is exactly one `+
     `(cone-chart event) x (boost); the Borel meets every Hopf fiber `+
     `exactly once: the cone chart is a global section of the finite `+
     `Hopf fibration, ${P*(P-1)} fibers of ${P+1}`,
     H.unique && H.fibers === P*(P-1) && H.onceEach);
  ok(`p = ${P}: the fiber coordinate is the horizon circle: t -> `+
     `t([1:0]) bijects the boost torus with P1, the cells plus the `+
     `horizon class [1:0]`, H.orbP1 === P + 1);
}

// the spin contrast at p = 13: in SL2 the section is obstructed at -1
{
  const P = 13, md = a => ((a % P) + P) % P;
  const dets = m => md(m[0]*m[3] - m[1]*m[2]);
  const key = m => m.join(',');
  const mul = (m, n) => { const [a,b,c,d] = m, [e,f,g,h] = n;
    return [a*e+b*g, a*f+b*h, c*e+d*g, c*f+d*h].map(md); };
  const SL = new Set();
  for (let a = 0; a < P; a++) for (let b = 0; b < P; b++)
    for (let c = 0; c < P; c++) for (let d = 0; d < P; d++)
      if (dets([a,b,c,d]) === 1) SL.add(key([a,b,c,d]));
  const ainv = a => { for (let x = 1; x < P; x++) if (md(a*x) === 1) return x; };
  const Bs = [], Ts = [];
  for (let a = 1; a < P; a++) for (let b = 0; b < P; b++)
    Bs.push([a, b, 0, ainv(a)]);
  for (let x = 0; x < P; x++) for (let y = 0; y < P; y++)
    if (md(x*x - 2*y*y) === 1) Ts.push([x, md(2*y), y, x]);
  const prods = new Set();
  for (const b of Bs) for (const t of Ts) prods.add(key(mul(b, t)));
  ok('the spin contrast: |SL2| = 2184 with |B| = 156 and |T| = 14, but '+
     'B and T share the sign -I, so |BT| = 1092 = |PSL2|: the section '+
     'belongs to the observable PGL2 (B meets T trivially there); SL2 '+
     'is the spin double cover of PSL2, the index-two rotation half of '+
     'PGL2', SL.size === 2184 && Bs.length === 156 && Ts.length === 14 &&
     prods.size === 1092);
}

// the Cayley station theorem (the M0 station count is a theorem, not a
// convention): the scalar Cayley map phi([x:y]) = (y + wx)/(y - wx),
// w^2 = nu = 2, bijects P1(F13) -- the thirteen cells plus the horizon
// class [1:0] -- onto the norm-one torus C14; phi(0) = 1 and
// phi([1:0]) = -1: the origin and the horizon are the sign pair, the
// base-transportable core (00:Y5)
{
  const P = 13, NU = 2;
  const md = a => ((a % P) + P) % P;
  const mulK = (a, b) => [md(a[0]*b[0] + NU*a[1]*b[1]), md(a[0]*b[1] + a[1]*b[0])];
  const invK = a => {
    const n = md(a[0]*a[0] - NU*a[1]*a[1]);
    let ni = 0; for (let x = 1; x < P; x++) if (md(n*x) === 1) ni = x;
    return [md(a[0]*ni), md(-a[1]*ni)];
  };
  const normK = a => md(a[0]*a[0] - NU*a[1]*a[1]);
  const phi = (x, y) => mulK([md(y), md(x)], invK([md(y), md(-x)]));
  const img = new Set();
  let norms = true;
  for (let l = 0; l < P; l++){                 // the affine cells
    const v = phi(l, 1);
    img.add(v.join(','));
    if (normK(v) !== 1) norms = false;
  }
  const hz = phi(1, 0);                        // the horizon class [1:0]
  img.add(hz.join(','));
  const org = phi(0, 1);
  ok('the Cayley station theorem: phi bijects P1(F13) onto the norm-one '+
     'torus C14 (image 14, all norms 1); phi(0) = 1, phi([1:0]) = -1 -- '+
     'origin and horizon the sign pair, antipodal stations',
     img.size === 14 && norms && normK(hz) === 1 &&
     org[0] === 1 && org[1] === 0 && hz[0] === P - 1 && hz[1] === 0);
}

console.log(fails ? `\n${fails} FAILURES` : '\nall checks pass');
process.exit(fails ? 1 : 0);
