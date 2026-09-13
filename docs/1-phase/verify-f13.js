// Subject-shell dynamics verification for 3-phase (instance checks: verify-233.js).
// F13 sphere and frame, zonal theorem, coefficient plane K = F13[w]/(w^2-2) = F169.
// Every check is integer arithmetic. Any FAIL exits nonzero.
'use strict';
let fails = 0;
const ok = (name, cond) => { console.log((cond ? 'PASS ' : 'FAIL ') + name); if (!cond) fails++; };

const P = 13, OM = 233, S = 58;
const mod = (a, m) => ((a % m) + m) % m;
const pwm = (b, e, m) => { b = mod(b, m); e = mod(e, m - 1);
  let r = 1; while (e > 0) { if (e & 1) r = (r * b) % m; b = (b * b) % m; e >>>= 1; } return r; };
const gcd = (a, b) => b ? gcd(b, a % b) : a;
const isPrime = n => { if (n < 4) return n > 1;
  for (let d = 2; d * d <= n; d++) if (n % d === 0) return false; return true; };

// ---- 1. the Subject frame F13(tau; 0, 1, 2) ----
ok('p = 13 = 4k+1, k = 3', P === 4 * 3 + 1);
const ORB = []; for (let j = 0, x = 1; j < 12; j++) { ORB.push(x); x = (x * 2) % P; }
ok('g = 2 primitive: orbit 1,2,4,8,3,6,12,11,9,5,10,7', JSON.stringify(ORB) ===
   JSON.stringify([1,2,4,8,3,6,12,11,9,5,10,7]));
const I13 = mod(-pwm(2, 3, P), P);
ok('i = -g^3 = g^9 = 5, i^2 = -1', I13 === 5 && pwm(2, 9, P) === 5 && (5 * 5) % P === P - 1);
ok('pi = 6, e = g^i = 2^5 = 6', 2 * 3 === 6 && pwm(2, 5, P) === 6);
ok('Subject Q4 = {1, 5, 12, 8} at exponents 0, 9, 6, 3',
   pwm(2, 0, P) === 1 && pwm(2, 9, P) === 5 && pwm(2, 6, P) === 12 && pwm(2, 3, P) === 8);

// ---- 2. the sphere node rule: node(m, a) = a * g^m ----
// meridian M_0 (unit direction): depths 1..6 read 1..6; opposite ray reads 12..7
const M = (m, a) => (a * pwm(2, m, P)) % P;
ok('prime meridian: a*1 = 1..6, opposite -a = 12,11,10,9,8,7',
   [1,2,3,4,5,6].every(a => M(0, a) === a) &&
   [1,2,3,4,5,6].every(a => M(6, a) === P - a));
ok('quarter meridian (direction 8): 8, 3, 11, 6, 1, 9',
   JSON.stringify([1,2,3,4,5,6].map(a => M(3, a))) === JSON.stringify([8,3,11,6,1,9]));
ok('latitude a = drive orbit through a, in drive order',
   [1,2,3].every(a => JSON.stringify(ORB.map((_,m) => M(m, a))) ===
     JSON.stringify(ORB.map(x => (x * a) % P))));
// rotation: content of (m, a) moves to slot (m+1, a): g * node(m,a) = node(m+1,a)
let rotOK = true;
for (let m = 0; m < 12; m++) for (let a = 1; a < 13; a++)
  if ((2 * M(m, a)) % P !== M(m + 1, a)) rotOK = false;
ok('rotation law: g * node(m,a) = node(m+1,a), all 144 slots', rotOK);
// Subject view: the residues evolve x -> gx; static slot (m, a) reads
// a * g^{m + tau}, the same cells the Carrier-view frame stands over
const inv13 = x => pwm(x, P - 2, P);
let subOK = true;
for (let tau = 0; tau < 12; tau++) for (let m = 0; m < 12; m++) for (let a = 1; a < 13; a++){
  const now = M(mod(m + tau, 12), a), next = M(mod(m + tau + 1, 12), a);
  if ((2 * now) % P !== next) subOK = false;
}
ok('Subject view: slot (m,a) reads a * g^{m+tau}; evolution x -> gx per chronon', subOK);
ok('unit slot walks the drive orbit: 1, 2, 4, 8, 3', [0,1,2,3,4].every(t =>
   pwm(2, t, P) === [1,2,4,8,3][t]));
// the pullback is the naming: the Subject names the fixed unit cell g^{-tau}
let nameOK = true;
for (let tau = 0; tau < 12; tau++)
  if (pwm(inv13(2), tau, P) !== pwm(2, mod(-tau, 12), P)) nameOK = false;
ok('the pullback naming: cell 1 is named g^{-tau}, walking 1, 7, 10, 5, 9', nameOK &&
   [0,1,2,3,4].every(t => pwm(inv13(2), t, P) === [1,7,10,5,9][t]));

// ---- 3. the zonal theorem: D chi_k = g^{-k} chi_k, dispersion, isotropy ----
let zonOK = true;
for (let k = 0; k < 12; k++) for (let j = 0; j < 12; j++) {
  const lhs = pwm(2, mod((j - 1) * k, 12), P);          // chi_k(g^{j-1})
  const rhs = (pwm(inv13(2), k, P) * pwm(2, mod(j * k, 12), P)) % P;
  if (lhs !== rhs) zonOK = false;
}
ok('zonal law: D chi_k = 2^{-k} chi_k pointwise, all 12 windings', zonOK);
ok('material mode k = 1 acquires x7 per chronon (7 = 2^{-1})', inv13(2) === 7);
const disp = [];
for (let k = 0; k < 12; k++) disp.push(mod(2 - pwm(2, k, P) - pwm(inv13(2), k, P), P));
console.log('  dispersion 2 - 2^k - 2^{-k} mod 13, k = 0..11:', JSON.stringify(disp));
ok('dispersion symmetric: E(k) = E(12-k)', [1,2,3,4,5].every(k => disp[k] === disp[12-k]));
let isoOK = true;
for (let k = 0; k < 12; k++) {
  let n = 0;
  for (let j = 0; j < 12; j++) n = (n + pwm(2, mod(2 * k * j, 12), P)) % P;
  const expect = (k === 0 || k === 6) ? 12 : 0;         // 12 = -1 mod 13
  if (n !== expect) isoOK = false;
}
ok('isotropy: <chi_k, chi_k> = 0 except k = 0, 6 (values -1)', isoOK);

// ---- 4. the coefficient plane K = F13[w]/(w^2-2), nu = g = 2 ----
const QR13 = new Set([1,3,4,9,10,12]);
ok('nu = g = 2 is a nonsquare in F13 (canonical Lorentzian coefficient)', !QR13.has(2));
// K arithmetic: z = [a, b] for a + b w, w^2 = 2
const kmul = (z, u) => [ (z[0]*u[0] + 2*z[1]*u[1]) % P, (z[0]*u[1] + z[1]*u[0]) % P ];
const kconj = z => [ z[0], mod(-z[1], P) ];             // Frobenius: w -> -w
const knorm = z => kmul(z, kconj(z))[0];
let n1 = 0;
for (let a = 0; a < P; a++) for (let b = 0; b < P; b++)
  if (knorm([a, b]) === 1) n1++;
ok('norm-one torus N1 has order p + 1 = 14', n1 === 14);
ok('split cycle meets N1 in {1, -1} alone', knorm([1,0]) === 1 && knorm([12,0]) === 1 &&
   ORB.filter(x => knorm([x,0]) === 1).length === 2);
ok('alpha_fwd = -2^{-1} i w = 4w', mod(-inv13(2) * I13, P) === 4);
ok('the Carrier counts the plane: |K| = 169 < 233, spare 64', 169 < OM && OM - 169 === 64);

// ---- 5. the Cayley kinetic example: order 13 over F169 (ex:cayley-13) ----
// H = -(T + T^{-1} - 2I) on H(F13), alpha = w. U = (I - wH)^{-1}(I + wH).
const ZERO = [0,0], ONE = [1,0];
const kadd = (z,u) => [ (z[0]+u[0])%P, (z[1]+u[1])%P ];
const ksub = (z,u) => [ mod(z[0]-u[0],P), mod(z[1]-u[1],P) ];
const kinv = z => { const n = knorm(z); const ni = inv13(n);
  const c = kconj(z); return [ (c[0]*ni)%P, (c[1]*ni)%P ]; };
const mat = f => Array.from({length:13},(_,r)=>Array.from({length:13},(_,c)=>f(r,c)));
const mmul = (A,B) => mat((r,c) => { let s = ZERO;
  for (let t = 0; t < 13; t++) s = kadd(s, kmul(A[r][t], B[t][c])); return s; });
const meq = (A,B) => A.every((row,r)=>row.every((z,c)=>z[0]===B[r][c][0]&&z[1]===B[r][c][1]));
const IDm = mat((r,c)=>r===c?ONE:ZERO);
// H entries in F13 (Frobenius-fixed): H[r][c] = -( [c=r+1] + [c=r-1] - 2[c=r] )
const H = mat((r,c)=>{ let v = 0;
  if (c === (r+1)%13) v -= 1; if (c === mod(r-1,13)) v -= 1; if (c === r) v += 2;
  return [mod(v,P), 0]; });
const wH = mat((r,c)=>kmul([0,1], H[r][c]));            // alpha = w
const Aplus = mat((r,c)=>kadd(IDm[r][c], wH[r][c]));
const Aminus = mat((r,c)=>ksub(IDm[r][c], wH[r][c]));
// invert Aminus by Gaussian elimination over K
function minvert(Ain){
  const A = Ain.map(row=>row.map(z=>z.slice())); const B = IDm.map(row=>row.map(z=>z.slice()));
  for (let col = 0; col < 13; col++){
    let piv = -1;
    for (let r = col; r < 13; r++) if (A[r][col][0] !== 0 || A[r][col][1] !== 0){ piv = r; break; }
    if (piv < 0) return null;
    [A[col],A[piv]] = [A[piv],A[col]]; [B[col],B[piv]] = [B[piv],B[col]];
    const pi = kinv(A[col][col]);
    for (let c = 0; c < 13; c++){ A[col][c] = kmul(A[col][c],pi); B[col][c] = kmul(B[col][c],pi); }
    for (let r = 0; r < 13; r++){ if (r === col) continue;
      const f = A[r][col]; if (f[0]===0 && f[1]===0) continue;
      for (let c = 0; c < 13; c++){
        A[r][c] = ksub(A[r][c], kmul(f, A[col][c]));
        B[r][c] = ksub(B[r][c], kmul(f, B[col][c]));
      }
    }
  }
  return B;
}
const Ainv = minvert(Aminus);
ok('I - wH invertible (kinetic admissibility)', Ainv !== null);
const U = mmul(Ainv, Aplus);
// H nilpotent: H^7 = 0
let Hp = H; for (let i = 1; i < 7; i++) Hp = mmul(Hp, H);
ok('H nilpotent: H^7 = 0', meq(Hp, mat(()=>ZERO)));
let Up = U, ord = 1;
while (!meq(Up, IDm) && ord <= 14) { Up = mmul(Up, U); ord++; }
ok('Cayley kinetic order: ord(U) = 13 exactly (every orbit returns in 13 steps)', ord === 13);
// unitarity: U^dagger U = I, with dagger = conjugate transpose (Frobenius)
const Udag = mat((r,c)=>kconj(U[c][r]));
ok('U exactly unitary: U^dagger U = I', meq(mmul(Udag, U), IDm));

process.exit(fails ? 1 : 0);
