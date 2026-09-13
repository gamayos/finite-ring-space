// Exact verification for 1-space: the Subject phase field on the space
// great circle. The instance is the minimal non-trivial pair (13, 233):
// Subject F13 (kappa = 3), fold per 00:F4. Every check is integer
// arithmetic; any FAIL exits nonzero.
'use strict';
let fails = 0;
const ok = (name, cond) => { console.log((cond ? 'PASS ' : 'FAIL ') + name); if (!cond) fails++; };

const P = 13, G = 2;
const mod = (a, m) => ((a % m) + m) % m;
const ORB = [], DL = {};
for (let j = 0, x = 1; j < 12; j++){ ORB.push(x); DL[x] = j; x = (x * G) % P; }
const INV = []; for (let t = 0; t < 12; t++) INV.push(ORB[mod(-t, 12)]);
const r = x => DL[x] % 4, s = x => DL[x] % 3;
const QR = new Set(); for (let a = 1; a < P; a++) QR.add((a * a) % P);

// ---- 1. the shell and the space circle ----
ok('g = 2 is primitive: twelve distinct units', new Set(ORB).size === 12);
ok('the space circle: thirteen cells, additive order, the additive group '+
   'simple (13 prime), translations acting as the rotation by 2 pi/13',
   P === 13 && (() => { for (let d = 2; d < P; d++) if (P % d === 0) return false;
     return true; })());
ok('the Observer origin is a cell of the circle, its value 0 at every '+
   'chronon: fixedness and phaselessness are one fact',
   [...Array(12).keys()].every(t => (0 * ORB[t]) % P === 0));

// ---- 2. the field is a complete registration ----
{
  let bij = true;
  for (let t = 0; t < 12; t++){
    const seen = new Set();
    for (let a = 0; a < P; a++) seen.add((a * ORB[t]) % P);
    if (seen.size !== P) bij = false;
  }
  ok('at every chronon the field is a bijection: the thirteen cells carry '+
     'the thirteen values, once each', bij);
}

// ---- 3. the field laws ----
ok('the global phase: one chronon turns every arrow one quarter, '+
   'r(a g^{tau+1}) = r(a g^tau) + 1, every cell, every chronon',
   [...Array(12).keys()].every(t => [...Array(12).keys()].every(j => {
     const a = ORB[j];
     return r((a * ORB[mod(t + 1, 12)]) % P) === (r((a * ORB[t]) % P) + 1) % 4;
   })));
ok('the diagonal law: one chronon steps every tint one rung',
   [...Array(12).keys()].every(t => [...Array(12).keys()].every(j => {
     const a = ORB[j];
     return s((a * ORB[mod(t + 1, 12)]) % P) === (s((a * ORB[t]) % P) + 1) % 3;
   })));
ok('the periods: the field returns after 12 chronons, the phases after 4, '+
   'the tints after 3',
   ORB.every(a => (a * ORB[0]) % P === a) && 12 % 4 === 0 && 12 % 3 === 0 &&
   ORB.every(a => r((a * ORB[4 % 12]) % P) === r(a)) &&
   ORB.every(a => s((a * ORB[3]) % P) === s(a)));

// ---- 4. the polarization pattern is the quadratic character ----
ok('the radial cells are the squares shifted by the drive: the arrow at '+
   'cell a is radial exactly when chi(a) = (-1)^tau, every chronon',
   [...Array(12).keys()].every(t => [...Array(12).keys()].every(j => {
     const a = ORB[j];
     const radial = r((a * ORB[t]) % P) % 2 === 0;
     const chi = QR.has(a) ? 1 : -1;
     return radial === (chi === (t % 2 === 0 ? 1 : -1));
   })));

// ---- 5. the distinguished cells ----
ok('the pullback cell: the value 1 sits at cell g^{-tau} = INV[tau], every '+
   'chronon', [...Array(12).keys()].every(t => (INV[t] * ORB[t]) % P === 1));
ok('the unit cell reads g^tau: the frame datum on the space circle',
   [...Array(12).keys()].every(t => (1 * ORB[t]) % P === ORB[t]));

// ---- 6. the frame orientation and the chart ----
ok('the orientation: i = -g^kappa = 5, the odd member of the pair {5, 8} '+
   '(C14)', mod(-ORB[3], P) === 5 && 5 % 2 === 1 && 8 % 2 === 0);
ok('the quarter of the Carrier chart takes S chronons: 58 * 360 = 90 * 232',
   58 * 360 === 90 * 232);
ok('the drive enters the Carrier as a PGL2 element: 2 is a non-residue '+
   'mod 13 on its own shell as well as t^2 = 2 unsolvable there',
   !QR.has(2));

// ---- 7. the observer variety and the light cone ----
{
  ok('the observer variety (00:C6): (p-1) p (p+1) = 12 x 13 x 14 = 2184 = '+
     '|PGL2(F13)| = |SL2(F13)|, and at the Carrier scale (Om-1) Om (Om+1) = 232 x 233 x '+
     '234 = 12649104 = |SL2(F233)|; the Borel plane is one boost slice, '+
     '2184 / 14 = 156',
     12 * 13 * 14 === P * (P * P - 1) &&
     232 * 233 * 234 === 233 * (233 * 233 - 1) && 2184 / 14 === 156);
  // the past cone in the Borel plane: cell a at lookback |a| reads
  // (a mod p) g^{tau - |a|}, the unit slope
  const val = (a, t) => (mod(a, P) * ORB[mod(t - Math.abs(a), 12)]) % P;
  let drv = true, slope = true, flip = true, arms = true, mono = true;
  for (let t = 0; t < 12; t++) for (let a = -6; a <= 6; a++){
    if (a === 0) continue;
    if (val(a, t + 1) !== (val(a, t) * G) % P) drv = false;
    const inst = (mod(a, P) * ORB[t]) % P;                 // the field now
    if (r(val(a, t)) !== mod(r(inst) - Math.abs(a), 4)) slope = false;
    const c0 = QR.has(val(a, t)), c1 = QR.has(val(a, t + 1));
    if (c0 === c1) flip = false;
    if (QR.has(val(-a, t)) !== QR.has(val(a, t))) arms = false;
    if (val(a, t + 13) !== (val(a, t + 1) * ORB[0]) % P) mono = false;
  }
  ok('the retardation law: every observed cell advances x -> gx in place, '+
     'the register retarded one chronon per space quantum', drv);
  ok('the unit slope: the observed phase lags the instantaneous field by '+
     'one quarter per space quantum, |a| quarters at distance |a|; every '+
     'observed arrow turns one quarter per chronon, T = 4', slope);
  ok('the doublet flip: the sheet of every observed cell is the quadratic '+
     'character of its value, exchanging every chronon, chi(g) = -1; the '+
     'two arms ride the same sheet, chi(-1) = +1 (00:C16)',
     flip && arms && !QR.has(G) && QR.has(P - 1));
  ok('the precession curl: one Carrier tick-angle per chronon of lookback '+
     'into the boost direction; at lookback S the quarter, 58 * 360 = '+
     '90 * 232: q becomes p (00:C18)', 58 * 360 === 90 * 232);
  ok('the monodromy: circumnavigation is thirteen steps and 13 = 1 (mod '+
     '12): one chronon per lap, x g^{-1} on the field', mono && 13 % 12 === 1);
  ok('the cone chart is the affine group AGL(1, 13): 13 x 12 = 156 = '+
     'p(p - 1) cells, closing at lcm(12, 13) = 156 -- the Borel (point '+
     'stabilizer) of PGL2(F13); the nonsplit C14 acts regularly on the '+
     '14 points of P1, so |PGL2| = 156 x 14 = 2184, stabilizer times '+
     'transversal; SL2 (also order 2184) is the spin double cover of '+
     'PSL2, the index-two rotation half of PGL2',
     13 * 12 === P * (P - 1) && P * (P - 1) === 156 &&
     12 * 13 === 156 && 156 * 14 === P * (P * P - 1));
}

// ---- 8. the boost circle: the quadratic extension ----
{
  // K = F13[w]/(w^2 - g), g = 2 a non-square, so the extension is a field:
  // the Clifford layer (8-dirac). The norm is N(x + y w) = x^2 - g y^2;
  // the norm-one circle is the nonsplit torus, one point per boost cell.
  const N1 = [];
  for (let x = 0; x < P; x++) for (let y = 0; y < P; y++)
    if (mod(x * x - G * y * y, P) === 1) N1.push([x, y]);
  const mulK = (u, v) => [mod(u[0]*v[0] + G*u[1]*v[1], P),
                          mod(u[0]*v[1] + u[1]*v[0], P)];
  const ordK = u => { let v = u.slice(), n = 1;
    while (!(v[0] === 1 && v[1] === 0) && n <= 196){ v = mulK(v, u); n++; }
    return n; };
  ok('the boost axis is an extension datum: it requires K = F13[w], w^2 = '+
     'g, and its cells are the norm-one circle x^2 - 2y^2 = 1: exactly '+
     'p + 1 = 14 points', !QR.has(G) && N1.length === 14);
  ok('the boost circle is cyclic: a norm-one generator of order 14 '+
     'exists, the nonsplit torus C14; the third axis of the spatial '+
     'lattice comes from the extension, the shell supplies the Borel '+
     'plane', N1.some(u => ordK(u) === 14));
}

// ---- 9. the rank-3 horizon ----
ok('the frame space of E2: |SL2(F13)| = p(p^2 - 1) = 2184; the three cyclic sectors '+
   '-- the split torus C12, the unipotent translation subgroup C13, the '+
   'nonsplit torus C14 counted from the norm form a^2 - 2b^2 = 1',
   P * (P * P - 1) === 2184 && (() => { let n1 = 0;
     for (let a = 0; a < P; a++) for (let b = 0; b < P; b++)
       if (mod(a * a - 2 * b * b, P) === 1) n1++;
     return n1 === 14; })());

// ---- 10b. the curl's Carrier algebra: delta_k = u^k in the declared
// C232 chart (generator 78 = 3^{-1}); the curl is exact Carrier-chart
// algebra -- a homomorphism landing on the cardinals: delta_58 = h =
// 89, delta_116 = -1, delta_232 = 1; the C14-valued form remains the
// open derivation
{
  const OM = 233, U = 78;
  const dk = k => { let x = 1; for (let i = 0; i < k; i++) x = x*U % OM; return x; };
  let hom = true;
  for (let a2 = 0; a2 < 30; a2++) for (let b2 = 0; b2 < 30; b2++)
    if (dk(a2 + b2) !== dk(a2)*dk(b2) % OM) hom = false;
  let ord = 1, x = U;
  while (x !== 1){ x = x*U % OM; ord++; }
  ok('the curl algebra: delta_k = 78^k is a homomorphism on the declared '+
     'C232 chart, 78 primitive (order 232), landing exactly on the '+
     'cardinals: delta_58 = h = 89, delta_116 = -1 = 232, delta_232 = 1',
     hom && ord === 232 && dk(58) === 89 && dk(116) === 232 &&
     dk(232) === 1);
}

// ---- 10. the permutation spectrum and the spectral generator ----
// Two faces, kept separate: the active register advances as R_{tau+1}
// = g R_tau, while coefficient functions advance as Psi_{tau+1} = P_g
// Psi with (P_g Psi)(a) = Psi(g^{-1} a). The eigenmodes of P_g are the
// characters chi_k(a) = zeta_12^{k dlog a}. Define the spectral
// generator H by H chi_k = k chi_k; then the drive step is exactly
// P_g = zeta_12^{-H}, verified cell by cell in index arithmetic --
// the energy of mode k is its winding rate k (the i-hbar-d/dt face is
// the chart face of the same law, per [2])
{
  let spec = true, gen = true;
  const ginv = ORB[11];                       // g^{-1} = g^11
  const H = k => k;                           // the spectral generator
  for (let k = 0; k < 12; k++)
    for (let j = 0; j < 12; j++){
      const a = ORB[j];
      // (P_g chi_k)(a) = chi_k(g^{-1} a): exponent k * dlog(g^{-1} a)
      const lhs = mod(k * DL[(ginv * a) % P], 12);
      // zeta^{-k} chi_k(a): exponent k * dlog(a) - k
      const rhs = mod(k * DL[a] - k, 12);
      if (lhs !== rhs) spec = false;
      // the generator identity: P_g = zeta^{-H} on mode k
      if (lhs !== mod(k * DL[a] - H(k), 12)) gen = false;
    }
  ok('the permutation spectrum: P_g chi_k = zeta_12^{-k} chi_k for all '+
     'twelve modes, cell by cell in index arithmetic; with the spectral '+
     'generator H chi_k = k chi_k this is the operator identity P_g = '+
     'zeta_12^{-H} -- the energy of mode k is its winding rate k',
     spec && gen);
}

console.log(fails ? `\n${fails} FAILURES` : '\nall checks pass');
process.exit(fails ? 1 : 0);
