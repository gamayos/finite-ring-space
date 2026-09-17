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
     'B and T share the sign -I, so BT is a sign-saturated half, |BT| = '+
     '1092 = |SL2|/2, projecting onto half of PSL2: the section '+
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
// base-transportable core (00:D14)
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


// the rotation group and the two fibrations (Theorem 11 of the paper; master
// row 00:C22, the Y4 record of 2026-09-17): the norm-one quaternion sphere is
// SL2, the observable variety PGL2 is SO3(F_p); the boost torus fibres the
// p(p-1) quadric of nonsquare radius with the Borel as section, the drive
// torus fibres the p(p+1) unit sphere with no section; every frame is one
// direction x one shell cell x one drive phase. Integer arithmetic only.
for (const [P, NU, R] of [[13, 2, 5], [5, 2, 2]]){          // R^2 = -1, NU a nonsquare
  const md = a => ((a % P) + P) % P;
  const inv = a => { for (let x = 1; x < P; x++) if (md(a*x) === 1) return x; };
  const mul = (m, n) => { const [a,b,c,d] = m, [e,f,g,h] = n;
    return [a*e+b*g, a*f+b*h, c*e+d*g, c*f+d*h].map(md); };
  const det = m => md(m[0]*m[3] - m[1]*m[2]);
  const inv2 = m => { const di = inv(det(m)); return [m[3]*di, -m[1]*di, -m[2]*di, m[0]*di].map(md); };
  const canon = m => { for (const x of m) if (md(x)){ const f = inv(md(x)); return m.map(v => md(v*f)); } };
  const key = m => m.join(',');
  const G = new Map(), SL = [];
  for (let a = 0; a < P; a++) for (let b = 0; b < P; b++)
    for (let c = 0; c < P; c++) for (let d = 0; d < P; d++){
      const m = [a,b,c,d], dt = det(m); if (!dt) continue;
      if (dt === 1) SL.push(m);
      const cm = canon(m); G.set(key(cm), cm);
    }
  const Gl = [...G.values()], n = P*(P*P - 1);
  // (a) the norm-one sphere is SL2
  let sph = 0; const img = new Set(); let dets1 = true;
  for (let x = 0; x < P; x++) for (let y = 0; y < P; y++)
    for (let z = 0; z < P; z++) for (let w = 0; w < P; w++){
      if (md(x*x + y*y + z*z + w*w) !== 1) continue; sph++;
      const m = [md(x + y*R), md(z + w*R), md(-z + w*R), md(x - y*R)];   // 1,i,j,k -> I, diag(R,-R), [0,1;-1,0], [0,R;R,0]
      if (det(m) !== 1) dets1 = false; img.add(key(m));
    }
  ok(`p = ${P}: the norm-one quaternion sphere x^2+y^2+z^2+w^2 = 1 has p^3-p = ${n} `+
     `points and maps bijectively onto SL2 with norm = det: the combinatorial S3 is `+
     `the spin cover SL2, not the observable PGL2`,
     sph === n && dets1 && img.size === SL.length && SL.length === n);
  // (b) involutions: the two groups of order p(p^2-1) are not isomorphic
  const I = canon([1,0,0,1]);
  const invSL = SL.filter(m => key(m) !== '1,0,0,1' && key(mul(m, m)) === '1,0,0,1').length;
  const invG = Gl.filter(m => key(m) !== key(I) && key(canon(mul(m, m))) === key(I)).length;
  ok(`p = ${P}: SL2 has one involution and PGL2 has p^2 = ${P*P}: two groups of order `+
     `${n}, not isomorphic`, invSL === 1 && invG === P*P);
  // (c) the adjoint action: PGL2 -> SO3(F_p), injective, -det preserved, determinant 1
  const basis = [[1,0,0,P-1],[0,1,0,0],[0,0,1,0]];
  const Ad = g => { const gi = inv2(g); return basis.map(u => { const v = mul(mul(g, u), gi); return [v[0], v[1], v[2]]; }); };
  const det3 = c => md(c[0][0]*(c[1][1]*c[2][2] - c[1][2]*c[2][1]) - c[1][0]*(c[0][1]*c[2][2] - c[0][2]*c[2][1])
                     + c[2][0]*(c[0][1]*c[1][2] - c[0][2]*c[1][1]));
  const Q = v => md(v[0]*v[0] + v[1]*v[2]);
  const ads = new Set(); let d1 = true, orth = true;
  for (const g of Gl){
    const c = Ad(g); ads.add(c.map(key).join('|')); if (det3(c) !== 1) d1 = false;
    for (const v of [[1,0,0],[0,1,0],[0,0,1],[1,1,1],[2,3,5]]){
      const w = [0,1,2].map(k => md(c[0][k]*v[0] + c[1][k]*v[1] + c[2][k]*v[2]));
      if (Q(w) !== Q(v)) orth = false; }
  }
  ok(`p = ${P}: the adjoint action on trace-zero matrices is injective on PGL2, preserves `+
     `-det and has determinant 1: PGL2 = SO3(F_p), the finite rotation group, ${n} elements`,
     ads.size === n && d1 && orth);
  // (d) the two 2-spheres
  let s1 = 0, snu = 0;
  for (let a = 0; a < P; a++) for (let b = 0; b < P; b++) for (let c = 0; c < P; c++){
    const q = md(a*a + b*c); if (q === 1) s1++; if (q === NU) snu++; }
  ok(`p = ${P}: the unit quadric a^2+bc = 1 has p(p+1) = ${P*(P+1)} points, the nonsquare `+
     `quadric a^2+bc = ${NU} has p(p-1) = ${P*(P-1)}`, s1 === P*(P+1) && snu === P*(P-1));
  // (e) orbits and centralisers of the boost axis (u^2 = nu) and of the unit i (i^2 = -1)
  const un = [0, NU, 1, 0], ui = [R, 0, 0, md(-R)];
  const orbit = u => { const s = new Set(); for (const g of Gl) s.add(key(mul(mul(g, u), inv2(g)))); return s.size; };
  const cent = u => Gl.filter(g => key(mul(g, u)) === key(mul(u, g))).length;
  ok(`p = ${P}: conjugation by the boost axis u (u^2 = ${NU}, a nonsquare) has centraliser `+
     `C_{p+1} (${P+1}) and orbit the nonsquare quadric (${P*(P-1)}); conjugation by the `+
     `unit i has the split centraliser C_{p-1} (${P-1}) and orbit ${P*(P+1)}`,
     cent(un) === P+1 && orbit(un) === P*(P-1) && cent(ui) === P-1 && orbit(ui) === P*(P+1));
  // (f) the split circle lies inside the Borel of SL2: no section for the split fibration
  const circ = [];
  for (let x = 0; x < P; x++) for (let y = 0; y < P; y++)
    if (md(x*x + y*y) === 1) circ.push([md(x + y*R), 0, 0, md(x - y*R)]);
  ok(`p = ${P}: the circle x^2+y^2 = 1 has p-1 = ${P-1} points and is the diagonal torus of `+
     `SL2, inside the Borel: the split fibration (fibre C_{p-1}, base p(p+1)) has no `+
     `section in B`, circ.length === P-1 && circ.every(m => m[2] === 0));
  // (g) the frame triple: G = P1 x B by g -> (g[1:0], t(g[1:0])^-1 g)
  const T = [];
  for (let x = 0; x < P; x++) for (let y = 0; y < P; y++)
    if ((x || y) && det([x, md(NU*y), y, x])) T.push(canon([x, md(NU*y), y, x]));
  const act = (m, q) => { const [a,b,c,d] = m;
    if (q === P) return md(c) === 0 ? P : md(a*inv(md(c)));
    const num = md(a*q + b), den = md(c*q + d); return den === 0 ? P : md(num*inv(den)); };
  const tof = new Map(); for (const t of T) tof.set(act(t, P), t);
  const pairs = new Set(); let backOk = true, bInB = true;
  for (const g of Gl){
    const x = act(g, P), t = tof.get(x), b = canon(mul(inv2(t), g));
    if (b[2] !== 0) bInB = false; pairs.add(x + ':' + key(b));
    if (key(canon(mul(t, b))) !== key(g)) backOk = false;
  }
  ok(`p = ${P}: the boost torus is simply transitive on P1, and g -> (g[1:0], t(g[1:0])^-1 g) `+
     `bijects PGL2 onto P1 x B with inverse (x, b) -> t(x) b: every frame is one direction, `+
     `one shell cell, one drive phase, ${P+1} x ${P} x ${P-1} = ${n}`,
     tof.size === P+1 && pairs.size === n && backOk && bInB);
  // (h) Stab([1:0]) = B exactly, and [1:0] is the only B-fixed point
  const Bl = []; for (let a = 1; a < P; a++) for (let b = 0; b < P; b++) Bl.push(canon([a, b, 0, 1]));
  const stab = Gl.filter(g => act(g, P) === P).length;
  let fixed = 0; for (let q = 0; q <= P; q++) if (Bl.every(s => act(s, q) === q)) fixed++;
  ok(`p = ${P}: the stabiliser of the horizon class is exactly the cone chart B (${P*(P-1)}) `+
     `and [1:0] is its only fixed point: the shell is the one affine chart of the boundary `+
     `P1 that B preserves`, stab === P*(P-1) && Bl.length === P*(P-1) && fixed === 1);
}

console.log(fails ? `\n${fails} FAILURES` : '\nall checks pass');
process.exit(fails ? 1 : 0);
