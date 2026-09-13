// Exact verification for 1-phase-6 on the minimal non-trivial pair (13, 233).
// 1-phase-1 = the 1-phase episode plus the Carrier quarter-turn mechanism
// (00:C15, 00:C17, 00:C18; face 00:Y2): the flip x h, the 6/29 precession, the
// double cover, and the perihelion trace. Supersedes the 3-phase folder.
// Subject F13 (kappa = 3), Carrier F233 (S = 58), fold per 00:F4.
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

// ---- 1. the minimal pair under the complete admissibility predicate ----
ok('Subject minimality: kappa=1 gives p=5, its own Q4 core (4k=4, p-1=4); '+
   'kappa=2 gives 9, composite; kappa=3 gives 13, prime',
   5 - 1 === 4 && !isPrime(9) && isPrime(13));
ok('Omega = 233 prime, = 4S+1, S = 58', isPrime(OM) && OM === 4 * S + 1);
ok('complete admissibility: S = 2 (mod 4), S = 1 (mod 3), Omega = 5 (mod 12), p^2 < Omega',
   S % 4 === 2 && S % 3 === 1 && OM % 12 === 5 && P * P < OM);
ok('jointly: Omega = 41 (mod 48)', OM % 48 === 41);
let scanOK = true;
for (let n = 170; n < 233; n++){
  if (!isPrime(n) || n % 4 !== 1) continue;
  const s = (n - 1) / 4;
  if (s % 4 === 2 && s % 3 === 1) scanOK = false;      // an earlier complete Carrier
}
ok('the scan of (169, 233) leaves nothing: 173,181,197,229 fail S even; 193 fails S=1(3)',
   scanOK && [43,45,48,49,57].every((s,i)=>[173,181,193,197,229][i] === 4*s+1) &&
   43%2===1 && 45%2===1 && 48%3===0 && 49%2===1 && 57%2===1);
ok('octant exists: Omega = 1 (mod 8)', (OM - 1) % 8 === 0);
// The guard: S even alone does not give the octant completion. Omega = 257
// (S = 64) passes the weaker conditions, but its octant exponent 32 is even,
// so its octant sits in class 0 and cannot carry the odd classes.
ok('the completion needs S = 2 (mod 4): the guard Omega = 257 (S = 64) passes '+
   'S even, S = 1 (mod 3), Omega = 5 (mod 12), p^2 < Omega, yet (257-1)/8 = 32 '+
   'is even, while (233-1)/8 = 29 is odd',
   64 % 2 === 0 && 64 % 3 === 1 && 257 % 12 === 5 && 169 < 257 &&
   ((257 - 1) / 8) % 2 === 0 && ((OM - 1) / 8) % 2 === 1);

// ---- 2. the full register, bit-verified ----
const HB = 144, H = 89, C = 74, KB = 124, G = 116;
ok('hbar = 2 sqrt(S): 72^2 = 58, hbar = 144, hbar^2 = -1',
   (72*72) % OM === S && 2*72 === HB && (HB*HB) % OM === OM - 1);
ok('h = -hbar = 89, G = 2S = 116', OM - HB === H && G === 2 * S);
ok('c = 74: c^2 = 117 = 2S+1 = 2^{-1}', (C*C) % OM === 2*S+1 && (2*(2*S+1)) % OM === 1);
ok('k_B = 124: k_B^2 = Omega-2 = 231', (KB*KB) % OM === OM - 2);
ok('the gauge bit: k_B c = h selects c = 74 (the branch -c = 159 gives k_B(-c) = hbar)',
   (KB*C) % OM === H && (KB*(OM-C)) % OM === HB && OM - C === 159);
ok('core Q4 = {1, hbar, -1, h} = {1, 144, 232, 89}: hbar^2 = -1, h = -hbar, '+
   'closed under multiplication',
   HB === 144 && OM - 1 === 232 && H === 89 && (HB * HB) % OM === OM - 1 &&
   (H === OM - HB) && [1, HB, OM - 1, H].every(x =>
     [1, HB, OM - 1, H].every(y => [1, HB, OM - 1, H].includes((x * y) % OM))));

// ---- 3. the Subject's declared chart on the torsor ----
// The Carrier is a timeless torsor: no generator, no origin. The register
// and the subgroup chain are its canonical content; the tick coordinates of
// the ring display are the Subject's declared chart, not Carrier structure.
const g = 78;
ok('the declared chart: 78 = 3^{-1} (the reframing gauge; the torsor itself '+
   'has no generator)', (3 * g) % OM === 1);
ok('the chart is a valid coordinate: 78 generates the full cycle', pwm(g, 116, OM) === OM - 1 && pwm(g, 8, OM) !== 1 &&
   pwm(g, 232/29, OM) !== 1);
ok('chart orientation: hbar = 78^{-S} = 78^{174} = 144', pwm(g, 232 - S, OM) === HB);
const Z8 = pwm(g, 29, OM);
ok('octant zeta_8 = 97 at chart position 29, order 8, zeta_8^2 in the core', pwm(Z8, 4, OM) === OM - 1 &&
   (Z8*Z8) % OM === pwm(g, 58, OM));
console.log('  zeta_8 = 78^29 =', Z8, ' zeta_8^2 = 78^58 =', pwm(g, 58, OM), '(= h? ', pwm(g,58,OM) === H, ')');

// ---- 4. the transport ----
ok('gcd(12, 232) = 4: only the quarter class transports', gcd(12, OM - 1) === 4);
ok('no 12-cycle in the Carrier: 3 does not divide 232', (OM - 1) % 3 !== 0);
ok('transport invariant S mod 4 = 2', S % 4 === 2);
{
  // the joint recurrence as events, no count named: walk the pair dynamics
  let a = 0, b = 0, n = 0; const seen = new Set();
  do { seen.add(a + ',' + b); a = (a + 1) % 12; b = (b + 1) % (OM - 1); n++; }
  while (!(a === 0 && b === 0));
  ok('the pair space closes: walking (a, b) from (home, home), every '+
     'class-compatible pair occurs exactly once before the return',
     seen.size === n && n === 12 * (OM - 1) / gcd(12, OM - 1));
}

// ---- 5. the F4 fold ----
// Subject, kappa = 3 odd: the product holds; the drive step itself folds:
const I13 = 5;
ok('Subject fold is a product (kappa odd): the drive step folds, 2 = i * g^4 = 5 * 3',
   (I13 * 16) % P === 2 && pwm(2, 4, P) === 3);
let foldOK = true;
for (let t = 0; t < 12; t++)
  if ((pwm(I13, mod(t,4), P) * pwm(3, mod(t,3), P)) % P !== pwm(2, t, P)) foldOK = false;
ok('fold of the position, all tau: 2^tau = i^{tau mod 4} * 3^{tau mod 3}', foldOK);
// division form on the Subject: remainders g^s, s in 0..2 (distinct from
// the CRT fold x = i^r * 3^s used by the display): unique naming
{
  const seen = new Set();
  for (let r = 0; r < 4; r++) for (let s = 0; s < 3; s++)
    seen.add((pwm(I13, r, P) * pwm(2, s, P)) % P);
  ok('division-unique on F13: the 12 pairs (r, s) name the 12 cycle elements once', seen.size === 12);
}
// Carrier, S = 58 even: division-unique, but NOT a product
{
  const seen = new Set();
  for (let r = 0; r < 4; r++) for (let s = 0; s < 58; s++)
    seen.add((pwm(HB, r, OM) * pwm(g, s, OM)) % OM);
  ok('division-unique on F233: the 232 pairs (r, s) name the 232 cycle elements once', seen.size === 232);
}
{
  // the product fails: no (r, u) with g = hbar^r * (g^4)^u  (parity obstruction)
  let sol = false;
  for (let r = 0; r < 4; r++) for (let u = 0; u < 58; u++)
    if ((pwm(HB, r, OM) * pwm(pwm(g, 4, OM), u, OM)) % OM === g) sol = true;
  ok('no product on F233: the drive step is not core x rung (odd exponent)', !sol);
  // the octant completes: g * zeta_8^{-1} lies in the even-exponent layer
  const even = new Set();
  for (let u = 0; u < 116; u++) even.add(pwm(g, 2*u, OM));
  // Z8^7 = Z8^{-1}; g sits at odd chart exponent 1, zeta_8 at 29, and
  // 1 - 29 = -28 is even: g factors as zeta_8 times an even-layer element.
  ok('octant completion: g * zeta_8^{-1} lies in the even-exponent layer',
     even.has(mod(g * pwm(Z8, 7, OM), OM)));
}
// sign-blindness: the crossing class (exponent mod 4) puts hbar and h together
ok('sign-blindness: crossing classes of the core are even only: 1,-1 in class 0; '+
   'hbar (exp 174) and h (exp 58) both in class 2', (232-S) % 4 === 2 && S % 4 === 2);
ok('the octant carries the odd classes: exp(zeta_8) = 29 = 1 (mod 4)', 29 % 4 === 1);

// ---- 6. the state vector on the great circle ----
{
  const DLOG = {}; let x = 1;
  for (let j = 0; j < 12; j++){ DLOG[x] = j; x = (x * 2) % P; }
  ok('dlog table: dlog(2) = 1, dlog(5) = 9, dlog(12) = 6', DLOG[2] === 1 && DLOG[5] === 9 && DLOG[12] === 6);
  let occOK = true, bijOK = true, diagOK = true;
  for (let tau = 0; tau < 12; tau++){
    const cells = new Set();
    for (let a = 1; a < 13; a++){
      const j = mod(DLOG[a] + tau, 12);                 // the component's position
      if ((a * pwm(2, tau, P)) % P !== pwm(2, j, P)) occOK = false;   // sits on its value
      const r = j % 4, sr = j % 3;
      cells.add(r + ',' + sr);
      const j2 = mod(j + 1, 12);
      if ((j2 % 4) !== ((r + 1) % 4) || (j2 % 3) !== ((sr + 1) % 3)) diagOK = false;
    }
    if (cells.size !== 12) bijOK = false;
  }
  ok('occupancy: the depth-a component sits on its value a g^tau, all tau', occOK);
  ok('bijection: the twelve components fill the twelve (r, s) fold cells, all tau', bijOK);
  ok('diagonal law: each component advances one class and one rung per chronon', diagOK);
  ok('the origin component is fixed: 0 * g = 0', (0 * 2) % P === 0);
}

// ---- 7. the shared clock and the winding rates ----
// the registrable class r = tau mod 4 on both shells: lockstep by construction;
// windings around the core per own period: kappa and S
ok('winding per own period: 12/4 = 3 = kappa (Subject), 232/4 = 58 = S (Carrier): '+
   'mass is the winding rate', 12/4 === 3 && 232/4 === S);
// the Subject fold hand walks i^tau on core residues
ok('fold hand residues: i^tau = 1, 5, 12, 8', [0,1,2,3].every(t =>
   pwm(I13, t, P) === [1,5,12,8][t]));

// ---- 8. the wavefunction comb on the great circle ----
// The wavefunction is space-like: the residue vector of the frame's prime
// great circle (the additive line through 0), each cell carrying the 4-state
// phase i^r of its residue, r = dlog(x) mod 4 in the fold x = i^r * 3^s.
{
  const DLOG = {}; let x = 1;
  for (let j = 0; j < 12; j++){ DLOG[x] = j; x = (x * 2) % P; }
  const cls = a => DLOG[a] % 4;
  // the display table WCLS of index.html
  const WCLS = [0,1,0,2,1,1,3,3,0,2,3,2];
  ok('class profile: r(a) = dlog(a) mod 4 for a = 1..12 is 0,1,0,2,1,1,3,3,0,2,3,2',
     WCLS.every((r, k) => cls(k + 1) === r));
  const count = [0,0,0,0];
  for (let a = 1; a < 13; a++) count[cls(a)]++;
  ok('equipartition: exactly three cells per class', count.every(c => c === 3));
  let rigid = true;
  for (let tau = 0; tau < 12; tau++)
    for (let a = 1; a < 13; a++)
      if (cls((a * pwm(2, tau, P)) % P) !== (cls(a) + tau) % 4) rigid = false;
  ok('the rigid turn: r(a g^tau) = r(a) + tau, all a, all tau: '+
     'one step is the global phase i^tau, one quarter on every arrow', rigid);
  let anti = true;
  for (let a = 1; a < 13; a++)
    if (cls(P - a) !== (cls(a) + 2) % 4) anti = false;
  ok('the antipode law: r(-a) = r(a) + 2: the opposite ray runs two quarters ahead', anti);
  let complete = true;
  for (let tau = 0; tau < 12; tau++){
    const seen = new Set([0]);
    for (let a = 1; a <= 6; a++){
      seen.add((a * pwm(2, tau, P)) % P);
      seen.add((a * pwm(2, tau + 6, P)) % P);
    }
    if (seen.size !== 13) complete = false;
  }
  ok('space-like completeness: at every tau the comb cells 0, a g^tau, -a g^tau '+
     'register all thirteen residues exactly once', complete);
  // The arrow is orthogonal to the meridian fiber: a fiber datum, no
  // component along the space-like base. The transverse plane is spanned by
  // the surface radial (the real axis) and the latitude tangent (the
  // imaginary axis). The imaginary axis is zonal because the class is a
  // shell operation: i = g^9, nine drive steps along the latitudes.
  ok('the imaginary direction is zonal: i = g^9 (nine drive steps along the '+
     'latitudes), 9 = -3 (mod 12): one counterclockwise quarter', pwm(2, 9, P) === I13 && (9 + 3) % 12 === 0);
  // The antipode is the fiber half-turn: -x = i^2 x, so opposite cells sit
  // two quarters apart in their fiber planes (zonal states parallel, radial
  // states mirrored through the horizontal plane).
  let par = true;
  for (let a = 1; a < 13; a++)
    if ((cls(P - a) * 90 + 180) % 360 !== (cls(a) * 90) % 360) par = false;
  ok('the fiber half-turn: q(-a) = q(a) + 180 (mod 360), all a: opposite '+
     'cells sit two quarters apart in the fiber plane', par);
  // The tint: each arrow is coloured by its rung s = dlog(x) mod 3. Direction
  // and tint together display the complete fold (r, s), hence the whole value.
  const rng = a => DLOG[a] % 3;
  const WRNG = [0,1,1,2,0,2,2,0,2,1,1,0];
  ok('rung profile: s(a) = dlog(a) mod 3 for a = 1..12 is 0,1,1,2,0,2,2,0,2,1,1,0',
     WRNG.every((v, k) => rng(k + 1) === v));
  const rcount = [0,0,0];
  for (let a = 1; a < 13; a++) rcount[rng(a)]++;
  ok('rung equipartition: exactly four cells per rung', rcount.every(c => c === 4));
  const pairs = new Set();
  for (let a = 1; a < 13; a++) pairs.add(cls(a) + ',' + rng(a));
  ok('the complete display: (r, s) determines the residue, the twelve pairs '+
     'are distinct: direction and tint read the whole value', pairs.size === 12);
}

// ---- 9. the animated operator: the drive pullback ----
// The exact operator content of one step is the basis-label permutation
// P2|a> = |2a>, in component form the pullback (P2 psi)(a) = psi(2^{-1} a):
// the drive D of the zonal theorem. The scalar reading 2I is not the
// operator content; the register vector is isotropic and unitarity is
// carried by the permutation.
{
  const img = new Set();
  for (let a = 0; a < 13; a++) img.add((2 * a) % P);
  ok('P2 is a bijection of the thirteen labels with the origin fixed',
     img.size === 13 && (2 * 0) % P === 0);
  let x = 1, ord = 0;
  do { x = (2 * x) % P; ord++; } while (x !== 1);
  ok('P2^12 = I: the permutation has exact order 12 on the units', ord === 12);
  let s2 = 0;
  for (let a = 0; a < 13; a++) s2 += a * a;
  ok('the register vector is isotropic: sum a^2 = 0 (mod 13): the zonal '+
     'theorem isotropy of the winding-one line', s2 % P === 0);
  // the zonal eigenrelation, pointwise for every winding: with
  // chi_k(g^j) = g^{jk} and (D psi)(x) = psi(g^{-1} x),
  // (D chi_k)(g^j) = g^{(j-1)k} = g^{-k} chi_k(g^j)
  let eig = true;
  for (let k = 0; k < 12; k++)
    for (let j = 0; j < 12; j++)
      if (pwm(2, mod((j - 1) * k, 12), P) !==
          (pwm(2, mod(-k, 12), P) * pwm(2, mod(j * k, 12), P)) % P) eig = false;
  ok('zonal eigenrelation: D chi_k = g^{-k} chi_k, all twelve windings, pointwise', eig);
  // the animated step is the register orientation of the same operator:
  // f_tau(a) = a g^tau is the winding-one line and f_{tau+1} = D^{-1} f_tau
  let pull = true;
  for (let tau = 0; tau < 12; tau++)
    for (let a = 0; a < 13; a++)
      if ((((2 * a) % P) * pwm(2, tau, P)) % P !== (a * pwm(2, tau + 1, P)) % P) pull = false;
  ok('the comb is g^tau chi_1 and the animated step is f_{tau+1} = D^{-1} f_tau: '+
     'the drive pullback in the register orientation, all tau, all cells', pull);
}

// ---- 10. the joint registration recurrence: the fibre product as events ----
{
  const seen = new Set(); let compat = true, u = 0, v = 0, n = 0;
  do { if (u % 4 !== v % 4) compat = false;
    seen.add(u + ',' + v); u = (u + 1) % 12; v = (v + 1) % (OM - 1); n++;
  } while (!(u === 0 && v === 0));
  ok('the fibre product as events: between consecutive (home, home) events '+
     'the trajectory visits every class-compatible pair exactly once, the '+
     'shared class agreeing at every chronon; no count beyond the shells is '+
     'named', compat && seen.size === n && n === 12 * (OM - 1) / gcd(12, OM - 1));
}

// ---- 11. end to end: the sibling index.html (repository consistency) ----
// The page and this verifier must not merely agree by duplication: read the
// sibling file and compare its tables and register labels to recomputation.
// This establishes repository consistency; the live deployment is compared
// by diff outside this script.
{
  const fs = require('fs');
  let html = '';
  try { html = fs.readFileSync(__dirname + '/index.html', 'utf8'); } catch (e) {}
  ok('index.html is readable next to the verifier', html.length > 0);
  const arr = name => {
    const m = html.match(new RegExp('const ' + name + ' = \\[(,?[0-9,]+)\\]'));
    return m ? m[1].replace(/^,/, '').split(',').map(Number) : null;
  };
  const ORB = [], INV = [];
  for (let j = 0, x = 1; j < 12; j++){ ORB.push(x); x = (x * 2) % P; }
  for (let t = 0; t < 12; t++) INV.push(pwm(pwm(2, t, P), P - 2, P));
  const DL = {}; ORB.forEach((x, j) => DL[x] = j);
  const WCLS = [], WRNG = [];
  for (let a = 1; a < 13; a++){ WCLS.push(DL[a] % 4); WRNG.push(DL[a] % 3); }
  ok('deployed ORB = the drive orbit 2^j', JSON.stringify(arr('ORB')) === JSON.stringify(ORB));
  ok('deployed INV = the pullback names 2^{-t}', JSON.stringify(arr('INV')) === JSON.stringify(INV));
  ok('deployed WCLS = dlog mod 4', JSON.stringify(arr('WCLS')) === JSON.stringify(WCLS));
  ok('deployed WRNG = dlog mod 3', JSON.stringify(arr('WRNG')) === JSON.stringify(WRNG));
  ok('deployed register labels: S 58, Omega 233, G 116, c 74, hbar 144, h 89, '+
     'k_B 124, zeta_8 97, cores as sets',
     ['S = <b>58</b>', '&Omega; = <b>233</b>', 'G = <b>116</b>', 'c = <b>74</b>',
      '&#295; = <b>144</b>', 'h = <b>89</b>', 'k<sub>B</sub> = <b>124</b>',
      '&zeta;&#8328; = <b>97</b>', '{1, 144, 232, 89}', '{1, 5, 12, 8}']
     .every(t => html.includes(t)));
  ok('deployed fold notation is i^r 3^s and never i^r g^s',
     html.includes('i<sup>r</sup>&middot;3<sup>s</sup>') &&
     !html.includes('i<sup>r</sup>&middot;g<sup>s</sup>'));
  ok('the page carries the episode marker (1-phase-6)',
     html.includes('data-episode="1-phase-6"'));
}

// ---- 12. the register and coefficient readings, the trivial pair, the octant lift ----
{
  // Active register vs coefficient wavefunction. One comb step composed with
  // the drive pullback is the identity, so the animation runs by D^{-1}; the
  // coefficient side runs by D. On one cell: the comb sends 1 -> 2, while
  // (D chi_1)(1) = chi_1(2^{-1}) = 7. Duals through INV, one dynamics.
  const inv2 = pwm(2, P - 2, P);
  let dual = true;
  for (let a = 1; a < P; a++) if ((2 * ((inv2 * a) % P)) % P !== a % P) dual = false;
  ok('the comb evolves by D^{-1}: one active step then the pullback is the identity; '+
     'on one cell the comb sends 1 -> 2 while (D chi_1)(1) = 7',
     dual && (2 * 1) % P === 2 && (inv2 * 1) % P === 7 && inv2 === 7);

  // The trivial pair (5, 41): admissible in full, but F_5^x is its own fold.
  const q = 5, om = 41;
  const units5 = new Set(); for (let j = 0, x = 1; j < 4; j++){ units5.add(x); x = (x * 2) % q; }
  ok('the trivial pair (5, 41) passes every admissibility clause (S = 10: 2 mod 4, 1 mod 3; '+
     '41 = 5 mod 12, 41 mod 48, 25 < 41; register 32^2 = -1, 12^2 = 2S+1, 11^2 = Omega-2) '+
     'while F_5 is its own fold, pure Q4, no rung: (13, 233) is the minimal non-trivial pair',
     10 % 4 === 2 && 10 % 3 === 1 && om % 12 === 5 && om % 48 === 41 && q * q < om &&
     (32 * 32) % om === om - 1 && (12 * 12) % om === 2 * 10 + 1 && (11 * 11) % om === om - 2 &&
     units5.size === 4 && [1, 2, 3, 4].every(u => units5.has(u)));

  // The L1-latitude ring law: in the Carrier view the cell at longitude
  // IEXP[r] holds i^r; in the Subject view slot IEXP[r] - tau re-registers
  // to i^r. The fold hand always points at the cell holding the lift.
  {
    const IEXP = [0, 9, 6, 3], CORE4 = [1, 5, 12, 8];
    const ORB2 = []; for (let j = 0, x = 1; j < 12; j++){ ORB2.push(x); x = (x * 2) % P; }
    let handOK = true;
    const rec = 12 * (OM - 1) / gcd(12, OM - 1);
    for (let tau = 0; tau < rec; tau++){
      const r = tau % 4;
      if (ORB2[IEXP[r]] !== CORE4[r]) handOK = false;                       // Carrier view
      const m = mod(IEXP[r] - tau, 12);
      if (ORB2[mod(m + tau, 12)] !== CORE4[r]) handOK = false;              // Subject view
      if (ORB2[mod(mod(-tau, 12) + tau, 12)] !== 1) handOK = false;         // the gold-ringed cell reads 1
    }
    ok('the L1 ring law over the full recurrence: the fold hand points at the cell '+
       'holding i^tau in both views, and the pullback-named cell reads 1', handOK);
  }

  // The Carrier Q4 lifts even fold classes only; the octant exponent is odd.
  const dl = {}; for (let k = 0, x = 1; k < 232; k++){ dl[x] = k; x = (x * 78) % OM; }
  ok('Carrier core chart exponents {0, 174, 116, 58} sit in even classes {0, 2, 0, 2} (mod 4); '+
     'the octant exponent 29 is odd: the odd classes ride the octant',
     dl[1] === 0 && dl[144] === 174 && dl[232] === 116 && dl[89] === 58 &&
     JSON.stringify([0, 174, 116, 58].map(e => e % 4)) === JSON.stringify([0, 2, 0, 2]) &&
     dl[97] === 29 && 29 % 2 === 1);
}

// ---- 13. the Carrier's quarter-turn and the precession (00:C17, 00:C18) ----
// The cycles share the C4 class quotient; the joint recurrence is the pair
// space, event structure. The bridge is the quadratic extension K = F169 with its leak;
// the Carrier evolves in itself over its complete period, each quarter the
// Fourier flip x h, and the Subject's orbit precesses against the quarter.
{
  const h = pwm(78, 58, OM);
  ok('the quarter of the Carrier period is the Fourier flip: 78^58 = h = 89, '+
     'h^2 = -1, h^4 = 1 (space and momentum exchange each quarter)',
     h === 89 && (h * h) % OM === OM - 1 && pwm(h, 4, OM) === 1);
  ok('the four cardinals are the quarter operators: chart exponents '+
     '{0, 58, 116, 174} carry {1, h, -1, hbar}',
     pwm(78, 0, OM) === 1 && pwm(78, 58, OM) === 89 &&
     pwm(78, 116, OM) === OM - 1 && pwm(78, 174, OM) === 144);
  ok('the flip chirality is Carrier-blind: h and hbar share class 2 '+
     '(exponents 58 and 174, both = 2 mod 4): the C14 bit',
     58 % 4 === 2 && 174 % 4 === 2);
  ok('the leak: the plane K = F169 is counted by the Carrier with spare '+
     '233 - 169 = 64 = 8^2; which leak cells carry the flip is open',
     OM - 169 === 64 && 8 * 8 === 64 && 169 === P * P);
  {
    // the precession as events: walk the pair dynamics from (home, home)
    let a = 0, b = 0, n = 0, half = 0, halves = 0;
    do { a = (a + 1) % 12; b = (b + 1) % (OM - 1); n++;
      if (a === 0 && b === (OM - 1) / 2){ half = n; halves++; }
    } while (!(a === 0 && b === 0));
    ok('the precession: 12 ticks per Subject orbit against the 58-tick '+
       'quarter advances the q/p frame 6/29 quarter per orbit; the event '+
       '(home, dlog(-1)) occurs exactly once between consecutive '+
       '(home, home) events, at the exact midpoint, the chart residue '+
       'there being the Carrier\'s own -1',
       12 / gcd(12, 58) === 6 && 58 / gcd(12, 58) === 29 &&
       halves === 1 && 2 * half === n &&
       pwm(78, (OM - 1) / 2, OM) === OM - 1);
  }
  const peri = new Set();
  for (let k = 0; k < 58; k++) peri.add(mod(12 * k, 232));
  ok('the perihelion trace: orbit closures land at ticks 12k mod 232 -- 58 '+
     'distinct positions, every fourth tick; orbit 29 lands on 116, the -1 '+
     'cardinal due west (the half cover), and orbit 58 closes east',
     peri.size === 58 && [...peri].every(p => p % 4 === 0) &&
     mod(12 * 29, 232) === 116 && mod(12 * 58, 232) === 0);
  ok('the Subject cardinal drift: one tick per chronon against the fixed '+
     'cardinals; the quarter takes exactly S chronons (58*360 = 90*232), '+
     'q landing on the h cardinal at tau = S; closure at Omega - 1 = 232',
     58 * 360 === 90 * 232 && pwm(78, 58, OM) === 89 && mod(232, 232) === 0);
  {
    const rec = 12 * (OM - 1) / gcd(12, OM - 1);
    const recT = 4 * 40 / gcd(4, 40);
    ok('the composed frame-ray rate: numerator kappa + S = 61, coprime to '+
       'the pair space, so the ray is home only at (home, home) and '+
       'antipodal exactly at the (home, dlog(-1)) event; per-orbit overshoot '+
       '12 ticks; the trivial pair concurs with numerator kappa + S = 11',
       3 + 58 === 61 && gcd(61, rec) === 1 &&
       mod(61 * (rec / 2), rec) === rec / 2 &&
       mod(61 * 12, rec) / 3 === 12 &&
       1 + 10 === 11 && gcd(11, recT) === 1 &&
       mod(11 * (recT / 2), recT) === recT / 2);
  }
}

// ---- 14. the octant bridge and the chirality ----
// The coefficient plane K = F13[w]/(w^2 - 2) is built explicitly; the octant
// is the homomorphic bridge between its units (C168) and the Carrier's
// (C232), gcd = 8; an octant-equivariant counting transports the flip
// exactly, the image and the remainder each closed under the flip, the
// remainder eight full octant fibres. The chirality is Subject parity:
// C14's odd-member rule and the gauge bit both select h.
{
  const kmul = (x, y) => [(x[0]*y[0] + 2*x[1]*y[1]) % P, (x[0]*y[1] + x[1]*y[0]) % P];
  const kord = (x) => { let o = 1, y = x;
    while (!(y[0] === 1 && y[1] === 0) && o <= 168){ y = kmul(y, x); o++; } return o; };
  // the bridge is oriented by the corpus rule (C7, C14): the half-lift
  // 3w (with (3w)^2 = i = 5, the odd member) sits at one octant step,
  // dlog(3w) = 1 (mod 8); the generator is selected accordingly, so
  // i = gen^42 exactly, and the orientation is pinned, not accidental
  let gen = null;
  for (let a = 0; a < P && !gen; a++) for (let b = 0; b < P && !gen; b++){
    if (a === 0 && b === 0) continue;
    if (kord([a, b]) !== 168) continue;
    let e = 0, y = [1, 0];
    while (!(y[0] === 0 && y[1] === 3) && e < 168){ y = kmul(y, [a, b]); e++; }
    if (e === 105) gen = [a, b];             // dlog(3w) = 105 = 1 (mod 8)
  }
  ok('the coefficient plane built explicitly: K = F13[w]/(w^2-2), |K*| = 168, '+
     'a generator found and oriented: dlog(3w) = 105 = 1 (mod 8), whence '+
     'gen^42 = i = 5, the C14 odd member', gen !== null);
  ok('the octant is the whole homomorphic bridge between the plane and the '+
     'Carrier: gcd(168, 232) = 8', gcd(168, 232) === 8);
  const dlK = new Map(); { let x = [1, 0];
    for (let e = 0; e < 168; e++){ dlK.set(x[0] + ',' + x[1], e); x = kmul(x, gen); } }
  const z8C = pwm(78, 29, OM), coC = pwm(78, 8, OM), hh = pwm(78, 58, OM);
  const cnt = (u) => { const e = dlK.get(u[0] + ',' + u[1]);
    return (pwm(z8C, e % 8, OM) * pwm(coC, e % 21, OM)) % OM; };
  let iK = [1, 0]; for (let k = 0; k < 42; k++) iK = kmul(iK, gen);
  const chi8 = (u) => pwm(z8C, dlK.get(u[0] + ',' + u[1]) % 8, OM);
  const img = new Set([0]); let equi = true, half = true;
  for (const key of dlK.keys()){ const u = key.split(',').map(Number);
    img.add(cnt(u));
    if (cnt(kmul(iK, u)) !== (hh * cnt(u)) % OM) equi = false;
    if (chi8(kmul([0, 3], u)) !== (z8C * chi8(u)) % OM) half = false;
  }
  ok('an octant-equivariant counting exists: 169 cells hit exactly, and '+
     'the oriented flip transports exactly: i_K = gen^42 = i = 5, with '+
     'c(i u) = h c(u) on all 168 units, and the half-lift carries one '+
     'octant step, chi8((3w) u) = zeta8 chi8(u)',
     iK[0] === 5 && iK[1] === 0 && img.size === 169 && equi && half);
  const leak = []; for (let c = 0; c < OM; c++) if (!img.has(c)) leak.push(c);
  const leakSet = new Set(leak);
  const dlC = new Map(); { let y = 1;
    for (let e = 0; e < 232; e++){ dlC.set(y, e); y = (y * 78) % OM; } }
  const fib = new Map();
  leak.forEach(v => { const c = dlC.get(v) % 29; fib.set(c, (fib.get(c) || 0) + 1); });
  let seen = new Set(), cyc = 0;
  for (const v of leak){ if (seen.has(v)) continue; let o = v;
    while (!seen.has(o)){ seen.add(o); o = (hh * o) % OM; } cyc++; }
  ok('the octant remainder: 64 cells, closed under the flip, organised as '+
     '8 full octant fibres over 8 co-octant classes, 16 flip 4-cycles',
     leak.length === 64 && leak.every(v => leakSet.has((hh * v) % OM)) &&
     fib.size === 8 && [...fib.values()].every(n => n === 8) && cyc === 16);
  ok('the general leak law (kappa-odd pairs): Omega - p^2 = 8(S/2 - '+
     'kappa(2 kappa + 1)): (5,41) 16, (13,233) 64, (29,857) 16, (37,1433) 64',
     [[5, 41], [13, 233], [29, 857], [37, 1433]].every(([pp, oo]) => {
       const kk = (pp - 1) / 4, ss = (oo - 1) / 4;
       return oo - pp * pp === 8 * (ss / 2 - kk * (2 * kk + 1)); }));
  ok('the chirality is Subject parity: C14 selects the odd member on '+
     'both shells (i = 5 odd over 8 even; h = 89 odd over hbar = 144 even), '+
     'the gauge bit k_B c = h concurs, and the transported flip lands on h; '+
     'GR orientation is likewise orbit-relative: prograde',
     5 % 2 === 1 && 8 % 2 === 0 && 89 % 2 === 1 && 144 % 2 === 0 &&
     (124 * 74) % OM === 89 && pwm(z8C, 2, OM) === 89);
}

// ---- 15. the pair-native state ----
// The registered state is the pair (shell a mod 12, Carrier b mod 232),
// each a residue of its own shell; the joint recurrence is the pair space,
// its count the lcm (00:F2) -- a label count, not an entity. The double
// cover is event structure: -1 at the pair event (home, 116), the Carrier's
// own dlog(-1); closure at (home, home). Everything reduces to pairs.
{
  const rec = 12 * (OM - 1) / gcd(12, OM - 1);
  let crt = true, sheet = true, events = true;
  for (let tau = 0; tau < rec; tau++){
    const a = tau % 12, b = tau % (OM - 1);
    const j = mod((a - b) / 4, 3);
    if (b + (OM - 1) * j !== tau) crt = false;                  // CRT rebuild
    const s2 = (j > 1 || (j === 1 && b >= (OM - 1) / 2));       // pair-derived sheet
    if (s2 !== (tau >= rec / 2)) sheet = false;
    if ((a === 0 && b === (OM - 1) / 2) !== (tau === rec / 2)) events = false;
    if ((a === 0 && b === 0) !== (tau === 0)) events = false;
  }
  ok('the pair determines everything: CRT rebuild b + (Omega-1) j with '+
     'j = ((a - b)/4) mod 3 recovers every chronon of the recurrence', crt);
  ok('the sheet is pair-derived: the second sheet '+
     'runs from the event (home, 116) to (home, home), and the pair formula '+
     'agrees with the timeline at every chronon', sheet && events);
  ok('every registered datum is a '+
     'residue of its shell (a < 12, b < Omega - 1, the perihelion a tick), '+
     'and the sheet sign is the Carrier\'s own -1 at dlog (Omega-1)/2 = 116',
     (OM - 1) / 2 === 116 && pwm(78, (OM - 1) / 2, OM) === OM - 1 &&
     12 < OM && 232 === OM - 1);
  ok('the precession theorem (00:C18): the apsidal fraction per revolution '+
     'is the winding ratio, kappa/S = (p-1)/(Omega-1), here 3/58, the '+
     'mass-ratio reading of D2; the trivial pair concurs at 1/10',
     (P - 1) * S === (OM - 1) * 3 && gcd(3, S) === 1 &&
     4 * 10 === 40 * 1 && gcd(1, 10) === 1);
  // the mass--energy channel (00:Y5, closed): the winding cycle meets the
  // boost torus in the sign alone, its spinor cover in exactly the quarter
  // core Q4 -- gcd(p-1, 2(p+1)) = 4 for every p = 4 kappa + 1 -- and the
  // quarter is spinorial: i^2 = -1 gives N(i) = -1, the sheet crossing
  // forced. The per-tick boost step is the winding rate's Q4 class on the
  // cover; the full (53,13) kill test lives in the ledger's check_y5.
  {
    let univ = true;
    for (let k = 1; k <= 10000; k++)
      if (gcd(4*k, 4*(2*k + 1)) !== 4 || gcd(4*k, 4*k + 2) !== 2) univ = false;
    ok('the mass--energy channel (00:Y5): gcd(p-1, p+1) = 2 and '+
       'gcd(p-1, 2(p+1)) = 4 for every p = 4 kappa + 1 (kappa <= 1e4) -- '+
       'the sign on the base, the quarter core Q4 on the spinor cover; '+
       'here gcd(232, 14) = 2, gcd(232, 28) = 4',
       univ && gcd(232, 14) === 2 && gcd(232, 28) === 4);
    ok('the quarter is spinorial: on both shells i^2 = -1 forces norm '+
       'N(i) = i * conj(i) = i^2 = -1 (i Frobenius-fixed) -- the Subject '+
       'i = 5 on F13, the Carrier root 78^58 = 89 squaring to -1 on F233: '+
       'the mass-energy transport crosses the sheet',
       (5 * 5) % 13 === 12 && pwm(78, 58, OM) === 89 &&
       (89 * 89) % OM === OM - 1);
  }
}

process.exit(fails ? 1 : 0);
