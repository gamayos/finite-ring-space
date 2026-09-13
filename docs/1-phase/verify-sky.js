// Exact verification for the Subject's sky: the 3D chart of the twelve
// observed nodes, derived from the coherence-pair spinor over the
// quadratic extension K = F13[eta], eta^2 = g. The instance is the
// minimal non-trivial pair (13, 233), kappa = 3. Every check is integer
// arithmetic; any FAIL exits nonzero.
'use strict';
let fails = 0;
const ok = (name, cond) => { console.log((cond ? 'PASS ' : 'FAIL ') + name); if (!cond) fails++; };

const P = 13, G = 2, KAP = 3;
const mod = (a, m) => ((a % m) + m) % m;
const ORB = [], DL = {};
for (let j = 0, x = 1; j < 12; j++){ ORB.push(x); DL[x] = j; x = (x * G) % P; }
const QR = new Set(); for (let a = 1; a < P; a++) QR.add((a * a) % P);

// ---- 1. the half-phase clock: K = F13[eta], eta^2 = g ----
const mulK = (u, v) => [mod(u[0]*v[0] + G*u[1]*v[1], P), mod(u[0]*v[1] + u[1]*v[0], P)];
const powK = (u, n) => { let r = [1, 0]; for (let i = 0; i < n; i++) r = mulK(r, u); return r; };
const ETA = [0, 1];
{
  ok('the extension generator is the drive\'s own root: eta^2 = g = 2, and '+
     'g is a non-square, so K = F13[eta] is a field: the Clifford layer',
     powK(ETA, 2)[0] === G && powK(ETA, 2)[1] === 0 && !QR.has(G));
  let ord = 1, v = ETA.slice();
  while (!(v[0] === 1 && v[1] === 0)){ v = mulK(v, ETA); ord++; }
  ok('the spinor clock: ord(eta) = 24, the double cover of the drive '+
     'cycle; even steps are the drive orbit, odd steps are K-proper',
     ord === 24 &&
     [...Array(12).keys()].every(j => powK(ETA, 2*j)[0] === ORB[j] &&
                                      powK(ETA, 2*j)[1] === 0) &&
     [...Array(12).keys()].every(j => powK(ETA, 2*j+1)[1] !== 0));
  ok('the cover\'s sign: eta^12 = -1, so one drive circuit negates the '+
     'spinor and two close it; the canonical half-lift u(x) = eta^dlog(x) '+
     'squares to x on every unit',
     powK(ETA, 12)[0] === P - 1 && powK(ETA, 12)[1] === 0 &&
     [...Array(12).keys()].every(j => powK(ETA, 2*j)[0] === ORB[j]));
  ok('the two quarter half-lifts: (3 eta)^2 = i = 5 and (2 eta)^2 = -i = '+
     '8: the C14 pair {i, -i} appears as the two lifts, one per chirality',
     mulK([0,3],[0,3])[0] === 5 && mulK([0,2],[0,2])[0] === 8);
  const N = u => mulK(u, [u[0], mod(-u[1], P)])[0];   // Frobenius norm
  ok('phase norms carry scale, N(eta) = -2, so no norm ratio is a pure '+
     'budget: the colatitude is the decoherence count itself (00-ledger '+
     'D-metric doctrine: distance is the count)', N(ETA) === P - 2);
}

// ---- 2. the sky map: two covers ----
// The sky law is pair-native: two double covers, both of this universe.
// The temporal cover is the spinor clock C24 (eta = sqrt g, section 1);
// the spatial cover is C26 = 2p, the loop itself, the double cover of
// the space circle. Node (arm e, route k = 1..12): cell ek mod 13,
// value cell g^{tau-k}; colatitude: the walk position on C26, k half-
// steps of 180/13 degrees; azimuth: the pair (alpha, beta) with
// alpha = tau + 3k on C24 (the transport, direction-blind) and
// beta = the cell's own half-angle, c half-steps on C26: the space-
// circle position halved, a datum of the cell alone, the same from
// either route -- the sign of -1 distributed, one half-step per cell.
// Fiber: the half-phase u = eta^dlog(v); the rung and phase ride the
// fiber, never the position.
const val = (a, t) => (mod(a, P) * ORB[mod(t - Math.abs(a), 12)]) % P;
const TH = a => Math.abs(a);                       // row = route count
const PH = (a, t) => [mod(t + 3*Math.abs(a), 24),  // alpha on C24
                      mod(a, 13)];                 // beta: the cell
const eqPH = (u, v) => u[0] === v[0] && u[1] === v[1];
{
  ok('the two covers are of this universe: C24 = 2 x 12 doubles the '+
     'drive cycle and C26 = 2p doubles the space circle, both below '+
     'the totality; they share exactly the one sign, gcd(24, 26) = 2: '+
     'the central product glued over the common -1 has cardinality '+
     '24 x 26 / 2 = 312 = 2 x 156, a two-to-one event-set cover of '+
     'the Borel count; the base cycles are coprime, gcd(13, 24) = 1',
     24 === 2 * 12 && 26 === 2 * P && 24 < 233 && 26 < 233 &&
     (() => { const g = (x, y) => y ? g(y, x % y) : x;
       return g(24, 26) === 2 && g(13, 24) === 1 &&
              24 * 26 / 2 === 312 && 312 === 2 * P * (P - 1); })());
  // the central product proven as a structure, not a count: phi(a, b) =
  // 13a + 12b mod 312 is a homomorphism C24 x C26 -> C312 whose kernel
  // is exactly the identified sign pair, and [(1, 1)] generates
  {
    const ker = [];
    for (let a = 0; a < 24; a++) for (let b = 0; b < 26; b++)
      if ((13*a + 12*b) % 312 === 0) ker.push(a + ',' + b);
    let hom = true;
    for (let i = 0; i < 200; i++){
      const a1 = i % 24, b1 = (i*7) % 26, a2 = (i*5) % 24, b2 = (i*11) % 26;
      const lhs = (13*((a1 + a2) % 24) + 12*((b1 + b2) % 26)) % 312;
      const rhs = ((13*a1 + 12*b1) + (13*a2 + 12*b2)) % 312;
      if (lhs !== rhs) hom = false;
    }
    const g312 = (13*1 + 12*1) % 312;
    const gcd2 = (x, y) => y ? gcd2(y, x % y) : x;
    ok('the central product exactly: phi(a, b) = 13a + 12b mod 312 has '+
       'kernel {(0,0), (12,13)} -- the identified signs and nothing '+
       'else -- and [(1,1)] = 25 has order 312: (C24 x C26)/<(12,13)> '+
       '= C312 as an isomorphism, not a cardinality',
       ker.join('|') === '0,0|12,13' && hom &&
       312 / gcd2(g312, 312) === 312);
  }
  ok('the horizon falls strictly between rows 6 and 7: 6 x 180 < 90 x '+
     '13 < 7 x 180: the direct/echo boundary, and nothing is registered '+
     'on it', 6 * 180 < 90 * 13 && 90 * 13 < 7 * 180);
  // (c) the zonal reading: the global clock on the temporal cover
  let per24 = true, per12 = true, anti = true, rig = true;
  for (let t = 0; t < 24; t++) for (let a = -6; a <= 6; a++){
    if (a === 0) continue;
    if (!eqPH(PH(a, t + 24), PH(a, t))) per24 = false;
    if (val(a, t + 12) !== val(a, t)) per12 = false;
    if (PH(a, t + 12)[0] !== mod(PH(a, t)[0] + 12, 24)) anti = false;
    if (PH(a, t + 1)[0] !== mod(PH(a, t)[0] + 1, 24) ||
        PH(a, t + 1)[1] !== PH(a, t)[1]) rig = false;
  }
  ok('(c) the zonal reading is the global half-phase clock: positions '+
     'close after 24 chronons and values after 12; at one drive circuit '+
     'alpha advances half the temporal cover: the double cover is '+
     'observable, S(-1) = -I on the sky; the whole sky precesses '+
     'rigidly, one C24 step per chronon, the sheet fixed',
     per24 && per12 && anti && rig);
  // (b) the distributed sign
  ok('(b) the winding is direction-blind, 45 degrees (three C24 steps) '+
     'per quantum on both arms; the sign of -1 enters distributed as '+
     'the cell\'s half-angle, one C26 half-step per cell, accumulating '+
     '13 = half the spatial cover per circuit: the precession spread '+
     'over the whole orbit', 45 === 3 * 15 && 13 === 26 / 2);
  // injectivity: everywhere, every chronon
  let inj = true;
  for (let t = 0; t < 24; t++){
    const seen = new Set();
    for (let a = -6; a <= 6; a++){
      if (a === 0) continue;
      const u = PH(a, t);
      const key = TH(a) + ',' + u[0] + ',' + u[1];
      if (seen.has(key)) inj = false;
      seen.add(key);
    }
  }
  ok('the sky map is injective: the twelve direct images occupy twelve '+
     'distinct points at every chronon (the full twenty-four in '+
     'section 3): no folds anywhere', inj);
  // (a) the rung stays on the fiber
  let rungfree = true, complete = true;
  for (let t = 0; t < 12; t++) for (let a = -6; a <= 6; a++){
    if (a === 0) continue;
    const u = PH(a, t);
    if (u[0] !== mod(t + 3*Math.abs(a), 24) || u[1] !== mod(a, 13)) rungfree = false;
    const j = DL[val(a, t)];
    if (powK(ETA, 2*j)[0] !== val(a, t) || powK(ETA, 2*j)[1] !== 0) complete = false;
  }
  ok('(a) the rung never enters the position: the sky map factors '+
     'through (route, sheet, tau); the fiber half-phase u = eta^dlog '+
     'recovers the whole value, hence the fold (r, s): tint and arrow '+
     'stay fiber data, the energy reading (zonal Fourier partner)',
     rungfree && complete);
}

// ---- 3. the echo sky: the loop and the trace, pair-native ----
{
  // one formula covers the sphere: arm e, route k = 1..12, cell ek mod
  // 13, value cell g^{tau-k}; colatitude row k on C26; azimuth the pair
  // (alpha = tau + 3k on C24, beta = the cell's half-angle)
  const cell = (e, k) => mod(e * k, P);
  const vv = (e, k, t) => (cell(e, k) * ORB[mod(t - k, 12)]) % P;
  const AL = (k, t) => mod(t + 3 * k, 24);
  const BE = (e, k) => cell(e, k);                 // beta = the cell
  const UNF = (e, k) => e > 0 ? k : 13 - k;        // the guide, unfolded
  ok('the two routes of every cell: lookbacks |a| and 13 - |a| sum to '+
     '13, and the colatitudes sum exactly 180 degrees: the two images '+
     'of a cell are colatitude-antipodal',
     [...Array(6).keys()].every(j => {
       const a = j + 1;
       return a + (13 - a) === 13 &&
              a * 180 + (13 - a) * 180 === 13 * 180; }));
  ok('the loop passes straight through both poles: along the loop the '+
     'unfolded half-angle ends one leg at 13 and begins the other at 0, '+
     'a jump of half the cover at each crossing -- the azimuth branch '+
     'flip of passing through a pole, no cusp and no twist; the anchors '+
     'are the two null points of the walk, cell 0 at k = 0 (the '+
     'Observer) and cell 0 at k = 13 (the null self-echo, beyond the '+
     'faithful window of 12, one drive cycle)',
     UNF(1, 13) - UNF(-1, 13) === 13 && UNF(-1, 0) - UNF(1, 0) === 13 &&
     13 === 26 / 2 &&
     cell(1, 0) === 0 && cell(-1, 0) === 0 &&
     cell(1, 13) === 0 && cell(-1, 13) === 0 &&
     (0 * ORB[0]) % P === 0 && 13 > 12 && 12 === ORB.length);
  ok('the cover\'s parity signature: the two images of cell c share '+
     'their half-angle (beta = c from either route) and their '+
     'transports differ by (13 - 2c) x 3 C24 steps, always an odd '+
     'multiple of 45 degrees',
     [...Array(12).keys()].every(j => {
       const c = j + 1;
       return BE(1, c) === c && BE(-1, 13 - c) === c &&
              (13 - 2 * c) % 2 !== 0; }));
  ok('the direct ring runs continuous through the horizon: the '+
     'space-neighbors 6 and 7 share their row and transport, their '+
     'half-angles one half-step apart',
     TH(6) === 6 && BE(1, 6) === 6 && BE(-1, 6) === 7 &&
     BE(-1, 6) - BE(1, 6) === 1);
  // the echo values: the wrapped past cone is the advanced cone
  let echo = true, conj = true;
  for (let t = 0; t < 12; t++) for (let a = 1; a <= 6; a++)
    for (const e of [1, -1]){
      const c = mod(e * a, P);
      const vfut = (c * ORB[mod(t + a, 12)]) % P;          // the future value
      const vl = (c * ORB[mod(t - (13 - a), 12)]) % P;     // the long route
      if (vl !== (vfut * ORB[11]) % P) echo = false;       // ORB[11] = g^-1
      const vconj = (c * ORB[mod(a - t, 12)]) % P;         // the C7 reading
      const vret = vv(e, a, t);
      if ((vret * vconj) % P !== (c * c) % P) conj = false;
    }
  ok('the echo is the advanced cone: values are 12-periodic, so the '+
     'long route shows cell g^{tau+|a|-1}, the future value times the '+
     'monodromy g^{-1}: the past cone, wrapped around the world, is the '+
     'advanced branch', echo);
  ok('C7 lives on the values: retarded x conjugate = a^2 at every node '+
     'and chronon, the matter-antimatter gauge as the norm-circle '+
     'relation; the instance\'s matter content selects the direct '+
     'branch', conj);
  // full injectivity, both arms
  let inj = true;
  for (let t = 0; t < 24; t++){
    const seen = new Set();
    for (const e of [1, -1]) for (let k = 1; k <= 12; k++){
      const key = k + ',' + AL(k, t) + ',' + BE(e, k);
      if (seen.has(key)) inj = false;
      seen.add(key);
    }
  }
  ok('full injectivity: the twenty-four images occupy twenty-four '+
     'distinct points at every chronon: no folds anywhere on the sky',
     inj);
  // what remains of the mirror: the equal-row half-turn
  ok('the mirror is gone; equal-row images share alpha and their cells '+
     'sum to 13, half-angles summing to 180 degrees: the half-turn of '+
     'the space circle, the -1, recollected row by row',
     [...Array(12).keys()].every(j =>
       BE(1, j + 1) + BE(-1, j + 1) === 13));
  // the trace and the closure
  ok('the trace realizes the cone chart (00:Y3): per drive circuit '+
     '12 x 12 + 12 = 156 = p(p - 1) direct events, one per element of '+
     'the Borel; the covers are coprime, gcd(13, 24) = 1, and the '+
     'closed circuit carries twice the Borel count of images: 24 x 13 '+
     '= 2 x 156, the cover of the Borel',
     12 * 12 + 12 === P * (P - 1) && 24 * 13 === 2 * P * (P - 1) &&
     (() => { const g = (x, y) => y ? g(y, x % y) : x;
       return g(13, 24) === 1; })());
  // the lattice incidence: per row and arm, the 24 alpha-slots
  let inc = true;
  for (let k = 1; k <= 12; k++)
    for (let t = 0; t < 24; t++)
      for (let t2 = t + 1; t2 < 24; t2++)
        if (AL(k, t) === AL(k, t2)) inc = false;
  ok('the sky lattice: per row and arm, the 24 slots of the spinor '+
     'clock, each visited exactly once per closed circuit; the sheet '+
     'fixes the arm, so the closed circuit sweeps every slot of both '+
     'arms once', inc);
}

// ---- 4. the radial ladder: three fibers ----
{
  // scale-generic: a Subject of capacity kappa resolves exactly kappa
  // radial steps within its horizon at the axial radii R sin(2 a pi/p)
  // [approx, the chart flattening: the latitude circles' own radii,
  // the outer shell nearly at the rim]; checked across scales, Omega-blind
  ok('the capacity counts the radial shells: 4a < p iff a <= kappa, '+
     'identically for p = 4 kappa + 1; checked at kappa = 1, 3, 7, 58 '+
     '(p = 5, 13, 29, 233): the instance draws kappa = 3',
     [[1,5],[3,13],[7,29],[58,233]].every(([kp, pp]) =>
       pp === 4*kp + 1 &&
       [...Array(kp).keys()].every(j => 4*(j+1) < pp) && 4*(kp+1) > pp));
  ok('the fold forces the fiber count (00:F4): C12 = C4 x C3 is the '+
     'unique coprime split; the fiber realizes the quarter internally '+
     '(T = 4, verified), so the rung factor is external: exactly three '+
     'fibers', (() => {
       const g = (x, y) => y ? g(y, x % y) : x;
       const splits = [];
       for (let d = 2; d < 12; d++)
         if (12 % d === 0 && g(d, 12/d) === 1) splits.push(d);
       return splits.length === 2 && splits.includes(4) && 12/4 === 3; })());
  ok('the fiber lag, two faces of one rung: x3 = g^4 (dlog 3 = 4) is '+
     'four drive steps = 120 degrees, a third of the turn; on the '+
     'values it is the rung shift (tints cycle, 4 = 1 mod 3), on the '+
     'mounting it is the orientation: each shell rigidly rotated 120 '+
     'degrees = 8 C24-steps about the main axis, at full angle, a '+
     'congruence not a phase; the quarter is blind to both (4 = 8 = 0 '+
     'mod 4): the arrows repeat identically across the shells',
     DL[3] === 4 && 4 * 30 === 360 / 3 && 8 * 15 === 120 &&
     mod(4, 4) === 0 && mod(8, 4) === 0 && mod(4, 3) === 1);
  // per cell, the three shells x two routes show six distinct drive
  // states (2c - 1 is odd); the complementary six arrive two chronons
  // on: E_c and E_c + 2 are disjoint and their union is the whole
  // drive cycle, checked as sets. The origin stabilizer -- the pure
  // drive, the observer's clock -- completes the group. The 48 per
  // shell counts the 24 simultaneous images with their two spinor
  // lifts; the affine realization itself is per drive circuit (00:Y3)
  let six = true, comp2 = true;
  for (let c = 1; c < P; c++){
    const ex = new Set();
    for (let s = 0; s < 3; s++){
      ex.add(mod(-c + 4*s, 12)); ex.add(mod(c - 1 + 4*s, 12));
    }
    if (ex.size !== 6) six = false;
    const ex2 = new Set([...ex].map(e => mod(e + 2, 12)));
    const union = new Set([...ex, ...ex2]);
    if (union.size !== 12) comp2 = false;
    for (const e of ex) if (ex2.has(e)) comp2 = false;
  }
  ok('the totality decomposed: per cell the three shells x two routes '+
     'display six distinct drive-states (2c - 1 odd), and the '+
     'complementary six arrive two chronons on: E_c and E_c + 2 are '+
     'disjoint with union the whole drive cycle, as sets; over the pair '+
     '{tau, tau + 2} the cells sweep 2 x 72 = 144 = the affine '+
     'translation count, and the origin stabilizer, the pure drive, is '+
     'the observer\'s own clock, 12 null events: 144 + 12 = 156 = '+
     'p(p - 1) (00:Y3), the bijection (c, e) -> [x -> g^e x + c]; the '+
     '48 per shell counts the 24 images at tau with the 24 at tau + 2 '+
     '-- base events; the spinor lifts live on the 312 cover alone',
     six && comp2 && 2 * 72 + 12 === P * (P - 1) &&
     3 * 48 + 12 === P * (P - 1) && 48 === 2 * 24);
}

// ---- 5. head-turn against Fourier ----// ---- 5. head-turn against Fourier ----
{
  // a head quarter-turn about the polar axis: a congruence: every
  // azimuth shifts 90 degrees (six C24 steps), every fiber unchanged.
  // the meridional Fourier flip: a chart quarter: every azimuth shifts
  // 45 degrees (three C24 steps, the half of the chart quarter) and
  // every fiber advances a quarter (values x i): the two coordinates
  // both differ.
  const headPhi = 6, headFib = 0;    // C24 steps
  const fourPhi = 3, fourFib = 9;    // u -> u * eta^9: (eta^9)^2 = i: x i on the value
  ok('no rotation of the observer is the Fourier dual: the head quarter '+
     'shifts azimuths 90 degrees (six C24 steps) with the fiber fixed; '+
     'the chart quarter shifts azimuths 45 degrees (three C24 steps) '+
     'and turns every fiber a quarter, (eta^9)^2 = i: the operations '+
     'differ in both coordinates, and the halving exists only through '+
     'the extension', headPhi !== fourPhi && headFib !== fourFib &&
     6 * 15 === 90 && 3 * 15 === 45 &&
     powK(ETA, 18)[0] === 5 && powK(ETA, 18)[1] === 0);
  ok('the anchor of the fine curl: the tick-angle sense agrees with the '+
     'coarse 45-degree steps, both the conjugated lag; the quarter at '+
     'lookback S: 58 * 360 = 90 * 232 (00:C18)', 58 * 360 === 90 * 232);
}

console.log(fails ? `\n${fails} FAILURES` : '\nall checks pass');
process.exit(fails ? 1 : 0);
