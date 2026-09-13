// Production-render verification for 1-phase-2: loads index.html itself,
// runs the three production draw functions in a canvas-recording sandbox,
// and checks the rendered output -- positions, labels, counts, and the
// Carrier-view continuity -- against the exact laws. This suite consumes
// the production code directly; any FAIL exits nonzero.
// Run: node verify-render.js   (from the episode directory)
'use strict';
const fs = require('fs'), vm = require('vm');
let fails = 0;
const ok = (name, cond) => { console.log((cond ? 'PASS ' : 'FAIL ') + name); if (!cond) fails++; };

const html = fs.readFileSync(__dirname + '/index.html', 'utf8');
const src = html.replace(/^[\s\S]*?<script>\n/m, '').replace(/<\/script>[\s\S]*$/m, '');
const recs = { sph: [], rings: [], spc: [] };
const mk = tag => { let style = '', alpha = 1, lw = 1;
  return new Proxy({}, {
    get: (t, p) => {
      if (p === 'measureText') return () => ({ width: 0 });
      return (...a) => {
        if (p === 'fillText') recs[tag].push(['txt', String(a[0]), a[1], a[2]]);
        if (p === 'stroke' || p === 'fill') recs[tag].push([p, style, alpha, lw]);
        if (p === 'ellipse') recs[tag].push(['ell', a[0], a[1], a[2], a[3], a[4]]);
        if (p === 'arc') recs[tag].push(['arc', a[0], a[1], a[2]]);
        if (p === 'lineTo') recs[tag].push(['seg']);
        if (p === 'bezierCurveTo') recs[tag].push(['bez']);
        return undefined; };
    },
    set: (t, p, v) => { if (p === 'strokeStyle' || p === 'fillStyle') style = v;
      if (p === 'globalAlpha') alpha = v;
      if (p === 'lineWidth') lw = v; return true; } }); };
const els = {};
const el = id => els[id] ||= (() => {
  const e = { getContext: () => mk(recs[id] ? id : 'spc'), setAttribute: () => {},
              value: 5, style: {}, className: '' };
  Object.defineProperty(e, 'onclick', { set(){}, get(){ return null; } });
  Object.defineProperty(e, 'textContent', { set(){}, get(){ return ''; } });
  return e; })();
const sandbox = { document: { getElementById: el }, requestAnimationFrame: () => {}, Math, console, Proxy };
vm.createContext(sandbox);
vm.runInContext(src, sandbox);

const render = (v, s, c, sg, mode) => { for (const k in recs) recs[k].length = 0;
  vm.runInContext(`view = "${v}"; tS = ${s}; tC = ${c}; sigC = ${sg || 0};` +
    `skyMode = "${mode || 'helix'}";` +
    'drawSphere(tS, tC); drawRings(tS, tC); drawSpace(tS, tC);', sandbox); };

// 1. the full pair sweep, both views, three panels
let swept = true;
try {
  for (const mode of ['helix', 'cone', 'hopf'])
    for (const v of ['subject', 'carrier'])
      for (let t = 0; t < 696; t++)
        render(v, t % 12, t % 232, Math.floor(t / 232) % 2, mode);
} catch (e) { swept = false; }
ok('the full 696-state pair sweep renders all three panels, both views, '+
   'both sky representations', swept);

// 2. captions live under the panels: the canvases carry geometry only
render('subject', 0, 0);
const foot = k => recs[k].filter(r => r[0] === 'txt' && r[3] >= 478 &&
                                 (r[2] <= 20 || r[2] >= 500)).length;
ok('the canvases carry no caption text: geometry and data labels only',
   foot('sph') + foot('rings') + foot('spc') === 0);

// 3. the sky labels match the exact law from the production rendering
const md = (a, n) => ((a % n) + n) % n;
const ORB = vm.runInContext('ORB.slice()', sandbox);
const lab = recs.spc.filter(r => r[0] === 'txt' && /^\d+$/.test(r[1]) && r[1] !== '0');
const want = [];
for (const e of [1, -1]) for (let k = 1; k <= 12; k++)
  want.push((md(e * k, 13) * ORB[md(0 - k, 12)]) % 13);
const ms = xs => xs.map(String).sort().join();
ok('the outer fiber\'s twenty-four labels match the exact retarded values',
   lab.length === 24 && ms(lab.map(r => +r[1])) === ms(want));

// 4. the sky closures on the rendered positions, at a fixed Carrier
// state (the drive isolated from the leak): in the Carrier view the
// drive turns the sky -- half a circuit at t24 + 12, the antipodal
// spinor sign, closure at t24 + 24; in the Subject view the drive is
// hidden by re-registration -- the same three states render
// identically
const pos = rs => rs.filter(r => r[0] === 'txt' && /^\d+$/.test(r[1]) && r[1] !== '0')
  .map(r => Math.round(r[2]) + ',' + Math.round(r[3])).sort().join();
render('carrier', 0, 0);  const C0 = pos(recs.spc);
render('carrier', 6, 0);  const C6 = pos(recs.spc);
render('carrier', 12, 0); const C12 = pos(recs.spc);
ok('the double cover on the rendered sky (Carrier view, fixed Carrier '+
   'state): positions close at t24 + 24 and stand antipodal at t24 + 12',
   C12 === C0 && C6 !== C0);
render('subject', 0, 0);   const S0 = pos(recs.spc);
render('subject', 1, 0);   const S1 = pos(recs.spc);
render('subject', 6, 0);   const S6 = pos(recs.spc);
render('subject', 12, 0);  const S12 = pos(recs.spc);
render('subject', 5, 117); const SB = pos(recs.spc);
const curlP = vm.runInContext(`
(() => {
  view = "subject"; sigC = 0; frac = 0;
  const S = skyState(0, 0);
  let dmin = 1e9, dmax = 0;
  for (const n of S.nodes.filter(n => n.outer)){
    const d = Math.hypot(...n.wF.map((c, i) => c - n.w[i]));
    dmin = Math.min(dmin, d); dmax = Math.max(dmax, d);
  }
  view = "carrier";
  return { dmin, dmax };
})()`, sandbox);
ok('the Subject view holds the section and shows the relational '+
   'observable: the sky is identical across every drive phase and '+
   'Carrier tick (the rotation and the common flow are gauge), while '+
   'the retarded boost-curl displaces every image along its leaf by '+
   'its lookback (00:C18) -- static, integer-exact, visible',
   S1 === S0 && S6 === S0 && S12 === S0 && SB === S0 &&
   S0.length > 0 && curlP.dmin > 1 && curlP.dmax > 20);

// 5. the wrap continuity: the leak is a half-angle on the Carrier's
// spinor cover, carried by the sheet sigC; across the wrap (tau 695
// -> 696) every Carrier-view label moves by a small step, with no
// 180-degree branch jump; the Subject view stands exactly
const labxy = rs => { const m = new Map();
  rs.filter(r => r[0] === 'txt' && /^\d+$/.test(r[1]) && r[1] !== '0')
    .forEach((r, i) => m.set(i, [r[2], r[3]])); return m; };
const step = v => {
  render(v, 11, 231, 0); const A = labxy(recs.spc);
  render(v, 0, 0, 1);    const B = labxy(recs.spc);
  let maxstep = 0;
  for (const [i, a] of A){ const b = B.get(i);
    if (b) maxstep = Math.max(maxstep, Math.hypot(b[0]-a[0], b[1]-a[1])); }
  return maxstep;
};
const cStep = step('carrier'), sStep = step('subject');
ok('the wrap: the Carrier sky steps continuously through tau 695 -> '+
   '696 (a single-step size under 80 px, the sheet carrying the '+
   'half-angle branch) and the Subject sky stands exactly (the curl '+
   'is lookback-anchored, not clock-driven)',
   cStep > 0 && cStep < 80 && sStep === 0);

// 6. panel activity: all three panels draw substantively
render('carrier', 3, 51, 0);
ok('all three panels draw substantively in the Carrier view',
   recs.sph.length > 100 && recs.rings.length > 200 && recs.spc.length > 200);

// 7. the Hopf representation: the lit fibers carry the exact values
render('subject', 0, 0, 0, 'hopf');
const hlab = recs.spc.filter(r => r[0] === 'txt' && /^\d+$/.test(r[1]) && r[1] !== '0');
const hwant = [];
for (let k = 1; k <= 12; k++) for (const e of [1, -1]){
  const m = md(0 - k, 12), b = md(e * k, 13);
  hwant.push((b * ORB[m]) % 13);
}
ok('the Hopf mode lights twenty-four fibers labelled with the exact '+
   'event values (m, b) -> b g^m', hlab.length === 24 &&
   ms(hlab.map(r => +r[1])) === ms(hwant));
render('subject', 5, 5, 0, 'hopf');
const hlab2 = recs.spc.filter(r => r[0] === 'txt' && /^\d+$/.test(r[1]) && r[1] !== '0');
const hwant2 = [];
for (let k = 1; k <= 12; k++) for (const e of [1, -1]){
  const m = md(5 - k, 12), b = md(e * k, 13);
  hwant2.push((b * ORB[m]) % 13);
}
ok('the Hopf lighting follows the drive: at another chronon the lit '+
   'values track (tau - k, ek) exactly', hlab2.length === 24 &&
   ms(hlab2.map(r => +r[1])) === ms(hwant2));

// 9. the leaves in the helix guide style at half strength: 24
// outer-rung leaves, each split into a front and a back primitive
// elliptical arc (48 arc strokes), guide grey, front alpha 0.35 and
// back 0.12 -- half the helix loop convention -- with no fiber
// voxels; the inner-rung leaves
// hidden; the only line segments are the node arrows, the polar axis,
// and the observer's degenerate leaf (72 x 3 + 2 = 218); every leaf
// bounded by the chart silhouette
let ellOK = true;
for (const [v, s, c, sg] of [['subject',0,0,0],['subject',7,113,0],['carrier',11,231,1]]){
  render(v, s, c, sg, 'hopf');
  const ells = recs.spc.filter(r => r[0] === 'ell');
  const nseg = recs.spc.filter(r => r[0] === 'seg').length;
  const rimOK = ells.every(r =>
    Math.hypot(r[1]-260, r[2]-260) + Math.max(r[3], r[4]) < 300);
  const pairs = [];
  for (let i = 0; i < recs.spc.length - 1; i++)
    if (recs.spc[i][0] === 'ell' && recs.spc[i+1][0] === 'stroke')
      pairs.push({ style: recs.spc[i+1][1], alpha: recs.spc[i+1][2] });
  const grey = pairs.filter(p => p.style === '#8a877f');
  const cyan = pairs.filter(p => p.style !== '#8a877f');
  const nF = grey.filter(p => Math.abs(p.alpha - 0.35) < 1e-9).length;
  const nB = grey.filter(p => Math.abs(p.alpha - 0.12) < 1e-9).length;
  const nT = cyan.filter(p => Math.abs(p.alpha - 0.10) < 1e-9).length;
  const wantT = v === 'carrier' ? 0 : 24;
  const vox = recs.spc.filter(r => r[0] === 'arc' && r[3] < 1.2).length;
  if (ells.length !== 48 + wantT || grey.length !== 48 ||
      nF !== 24 || nB !== 24 || cyan.length !== wantT || nT !== wantT ||
      nseg !== 217 || !rimOK || vox !== 0) ellOK = false;   // the spirals live in the light-cone mode alone
}
ok('the Hopf leaves at the release density: 24 leaves as 48 primitive '+
   'grey front/back arcs (alphas 0.35/0.12) in both views, plus, in '+
   'the Subject view only, the 24 faint cyan curl-trace arcs (alpha 0.10) '+
   'from base to bead along each leaf; no voxels, polylines, or other '+
   'extras; every arc bounded', ellOK);

// 10. the section test: at a paused state the two representations
// share every node dot and every label exactly -- the toggle switches
// the fibers and only the fibers
let invOK = true;
for (const [v, s, c, sg] of [['subject',0,0,0],['subject',7,113,0],['carrier',11,231,1]]){
  const grab = mode => { render(v, s, c, sg, mode);
    return {
      labs: recs.spc.filter(r => r[0] === 'txt')
        .map(r => r[1] + '@' + r[2].toFixed(2) + ',' + r[3].toFixed(2))
        .sort().join('|'),
      dots: recs.spc.filter(r => r[0] === 'arc' && r[3] > 1.2)
        .map(r => r[1].toFixed(2) + ',' + r[2].toFixed(2) + ',' + r[3].toFixed(2))
        .sort().join('|') }; };
  const H = grab('helix'), F = grab('hopf');
  if (!(H.labs === F.labs && H.dots === F.dots && H.dots.length > 0)) invOK = false;
}
ok('the section test: pausing and toggling the representation keeps '+
   'every node dot and every label fixed; only the fibers change',
   invOK);

// 11. the drive orbits (L1, L2, L3) render as depth-banded Bezier
// chains under the ported 173 scheme: cubic spans present on every
// loop, every loop stroke's alpha exactly on the [0.1, 0.9] 24-band
// grid with several distinct bands, and the width riding the same
// band -- width = nominal x (0.1 + 0.9(alpha - 0.1)/0.8), nominal
// 1.75 green (the L1 time latitude, a = 1: the INNERMOST shell --
// corrected 14 Aug, this comment previously said the outer one) and
// 1.35 grey (L2 and L3) -- same-band runs chained, so the joints
// carry no segment overlaps. The assertion below keys the nominal off
// the COLOUR, not off the shell index, so it is blind to which rung
// wears the green and held across that correction unchanged.
let helixOK = true;
for (const [v, s, c, sg] of [['subject',0,0,0],['carrier',5,117,1]]){
  render(v, s, c, sg, 'helix');
  const bez = recs.spc.filter(r => r[0] === 'bez').length;
  const st = recs.spc.filter(r => r[0] === 'stroke' &&
    (r[1] === '#8a877f' || r[1] === '#58a35e'));
  const grid = st.every(r => r[2] >= 0.1 - 1e-9 && r[2] <= 0.9 + 1e-9 &&
    Math.abs(r[2] - (0.1 + Math.round((r[2] - 0.1)*30)/30)) < 1e-9);
  const law = st.every(r => Math.abs(r[3] - (r[1] === '#58a35e' ? 1.75 : 1.35)
    *(0.1 + 0.9*(r[2] - 0.1)/0.8)) < 1e-9);
  const bands = new Set(st.map(r => r[2]));
  if (!(bez > 300 && st.length >= 6 && grid && law && bands.size >= 4))
    helixOK = false;
}
ok('the drive orbits draw as depth-banded Bezier chains (the ported '+
   '173 scheme): cubic spans on every loop, stroke alphas exact on '+
   'the [0.1, 0.9] 24-band grid, the width riding the same band at '+
   'each shell nominal (1.75 green L1 = the innermost, 1.35 grey)', helixOK);

// 12. the frame leak (00:C17, 00:C18): each view holds its own frame.
// Subject view: the register stands (east slot reads 1 at every bC)
// and the Carrier chart turns counterclockwise -- hbar = 144 (the
// i-oriented quarter) on top at bC = 0, and after the S = 58 quarter
// the Carrier's h = 89 arrives at the register's 1 (east). Carrier
// view: the quarters stand (hbar on top at every bC), the q hand of
// the glued q/p dial stands at east, and the register drifts
// clockwise: its i = 5 arrives at q (east) at bC = 58 -- the Fourier
// x hbar exchange
const near = (rs, x, y, tol) => rs.filter(r => r[0] === 'txt' &&
  Math.hypot(r[2] - x, r[3] - y) < tol).map(r => r[1]);
const HBAR = 'ħ = 144', H = 'h = 89';
let leakOK = true;
{
  render('subject', 0, 0);
  const sTop0 = near(recs.rings, 260, 39, 8);
  const sReg0 = near(recs.rings, 408, 260, 8);
  const sQ0 = near(recs.rings, 64 + 39, 66, 8);
  render('subject', 0, 58);
  const sReg1 = near(recs.rings, 408, 260, 8);
  const sChart1 = near(recs.rings, 481, 260, 8);
  const sQ1 = near(recs.rings, 64, 66 + 39, 8);
  render('carrier', 0, 0);
  const cTop0 = near(recs.rings, 260, 39, 8);
  const cQ0 = near(recs.rings, 64 + 39, 66, 8);
  render('carrier', 0, 58);
  const cTop1 = near(recs.rings, 260, 39, 8);
  const cQ1 = near(recs.rings, 64, 66 + 39, 8);
  const cReg1 = near(recs.rings, 408, 260, 8);
  leakOK = sTop0.join() === HBAR &&
           sReg0.includes('1') && sReg1.includes('1') &&
           sChart1.join() === H &&
           sQ0.includes('q') && sQ1.includes('q') &&
           cTop0.join() === HBAR && cTop1.join() === HBAR &&
           cQ0.includes('q') && cQ1.includes('q') &&
           cReg1.some(t => t.includes('i = 5'));
}
ok('the frame leak: the Subject view holds the register (east reads '+
   '1 at every bC) while the Carrier chart turns counterclockwise, h '+
   'reaching east at bC = 58; the Carrier view holds the quarters '+
   '(hbar on top) while the register drifts clockwise, its i = 5 '+
   'reaching east at bC = 58; the q/p dial reads identically in both '+
   'views, q sweeping clockwise to the h cardinal (south) at bC = 58',
   leakOK);

// 13. the drive sense is one across the panels: in the Carrier view
// the sky's world azimuth steps clockwise with the drive, matching
// the shell's frame sweep and the chart hand -- from tau = 0 to tau
// = 4 the k = 1 node advances -(4 x 15 deg) plus the small drift,
// the same sign and quarter-step as the rings' hand
const senseP = vm.runInContext(`
(() => {
  view = "carrier"; sigC = 0;
  const n0 = skyState(0, 0).nodes.find(n => n.outer && n.e === 1 && n.k === 1);
  const n1 = skyState(4, 4).nodes.find(n => n.outer && n.e === 1 && n.k === 1);
  const a0 = Math.atan2(n0.w[1], n0.w[0]), a1 = Math.atan2(n1.w[1], n1.w[0]);
  let d = a1 - a0;
  while (d > Math.PI) d -= 2*Math.PI;
  while (d < -Math.PI) d += 2*Math.PI;
  return d;
})()`, sandbox);
ok('the drive sense is one across the panels: the Carrier-view sky '+
   'steps clockwise with the drive, one quarter-step from tau = 0 to '+
   'tau = 4 within a drift margin, as on the shell and the chart',
   senseP < 0 && Math.abs(senseP + Math.PI/3) < 0.12);

// 14. the interpolated mode is exact at the endpoints and on-tick in
// its data: the sub-chronon fraction moves geometry linearly (the
// midpoint azimuth is the exact average of the two tick azimuths, and
// frac = 1 reproduces the next tick's geometry), the quarter class
// advances by exactly +1 per chronon for every node (the arrow
// handoff), and no label or tint reads the fraction
const interpP = vm.runInContext(`
(() => {
  view = "carrier"; sigC = 0;
  const ang = S => { const n = S.nodes.find(n => n.outer && n.e === 1 && n.k === 1);
    return Math.atan2(n.w[1], n.w[0]); };
  frac = 0;   const a0 = ang(skyState(0, 0));
  frac = 0;   const a1 = ang(skyState(1, 1));
  frac = 0.5; const am = ang(skyState(0, 0));
  frac = 1;   const ah = ang(skyState(0, 0));
  frac = 0;
  const w = x => { let d = x; while (d > Math.PI) d -= 2*Math.PI;
                   while (d < -Math.PI) d += 2*Math.PI; return d; };
  let clsOK = true;
  for (let tau = 0; tau < 12; tau++){
    const A = skyState(tau % 12, tau % 232).nodes;
    const B = skyState((tau + 1) % 12, (tau + 1) % 232).nodes;
    for (let i = 0; i < A.length; i++)
      if (B[i].cls !== (A[i].cls + 1) % 4) clsOK = false;
  }
  return { mid: Math.abs(w(am - (a0 + w(a1 - a0)/2))),
           hand: Math.abs(w(ah - a1)), clsOK };
})()`, sandbox);
render('subject', 3, 51, 0);
const L0 = recs.spc.filter(r => r[0] === 'txt').map(r => r[1]).sort().join('|');
vm.runInContext('frac = 0.5', sandbox);
render('subject', 3, 51, 0);
const Lh = recs.spc.filter(r => r[0] === 'txt').map(r => r[1]).sort().join('|');
const D0 = pos(recs.spc);
vm.runInContext('frac = 0', sandbox);
render('subject', 3, 51, 0);
ok('the interpolated mode: midpoint geometry is the exact average of '+
   'the tick geometries, frac = 1 hands off to the next tick, the '+
   'quarter class steps +1 per chronon everywhere, and the labels and '+
   'the Subject-view positions read the tick alone (the curl is '+
   'lookback-anchored, fraction-free)',
   interpP.mid < 1e-9 && interpP.hand < 1e-9 && interpP.clsOK &&
   Lh === L0 && D0 === pos(recs.spc));

// 15. the frame dilation (00:Y5), the pure fiber flow in the
// sheet-fair chart. Stations exact and gauge-free: at the half the
// pattern is the congruent parity image, wF = -w to machine
// precision at full scale; home at the cycle; at the quarter the
// sharp outer shell disperses into a radial band (the Fourier dual's
// spread). Every bead rides its own leaf at every phase, and the
// ensemble breathes without collapsing: the outer ensemble's maximum
// radius never falls below 140 px and no single bead below 60. The
// Subject view stands unflowed
const dilP = vm.runInContext(`
(() => {
  view = "carrier"; skyMode = "hopf"; sigC = 0; frac = 0;
  const outN = S => S.nodes.filter(n => n.outer);
  // the retarded stations are ROW-GRADED: row k carries the flow of
  // its emission chronon, phi(k) = -(bC - k) pi/116, so it reaches
  // its congruent parity image at bC = 116 + k and its home at
  // bC = k -- each row at its own retarded epoch
  let dH = 0, dHome = 0;
  for (let k = 1; k <= 12; k++){
    const stH = skyState(0, 116 + k);
    for (const n of stH.nodes) if (n.k === k) dH = Math.max(dH,
      Math.hypot(...n.wF.map((c, i) => c + n.w[i])));
    const stC = skyState(0, k);
    for (const n of stC.nodes) if (n.k === k) dHome = Math.max(dHome,
      Math.hypot(...n.wF.map((c, i) => c - n.w[i])));
  }
  // quarter: the shell dispersed into a radial band
  const rQ = outN(skyState(0, 58)).map(n => Math.hypot(...n.wF));
  const band = Math.max(...rQ) - Math.min(...rQ);
  // bead-on-drawn-fiber: the drawn fiber is the foliation leaf through
  // the current bead (the re-lifted flowed position); the bead must
  // sit on it at every sampled phase
  let dmin = 0;
  for (const b of [10, 37, 58, 90, 116, 200]){
    const stG = skyState(0, b);
    const n5 = stG.nodes.find(n => n.outer && n.e === 1 && n.k === 5);
    const v = liftS3(n5.wF, false) || n5.v;
    const u = [-v[1], v[0], -v[3], v[2]];
    const pF = proj3(n5.wF);
    let db = 1e9;
    for (let q = 0; q < 1440; q++){
      const p = ptF3(v, u, q*Math.PI/720);
      db = Math.min(db, Math.hypot(p.x - pF.x, p.y - pF.y));
    }
    dmin = Math.max(dmin, db);
  }
  // no collapse through the cycle
  let rminE = 1e9, rmaxMin = 1e9;
  for (let b = 0; b < 232; b += 4){
    const S = skyState(0, b);
    const rr = outN(S).map(n => Math.hypot(...n.wF));
    rminE = Math.min(rminE, Math.min(...rr));
    rmaxMin = Math.min(rmaxMin, Math.max(...rr));
  }
  view = "subject";
  // the Subject-view curl is Carrier-tick invariant: the same at any bC
  const nA = skyState(0, 58).nodes[40], nB = skyState(0, 116).nodes[40];
  const subInv = Math.hypot(...nA.wF.map((c, i) => c - nB.wF[i]));
  view = "carrier";
  return { dH, dHome, band, dmin, rminE, rmaxMin, subInv };
})()`, sandbox);
ok('the frame dilation under the retarded common flow (phi(k) = '+
   'PHI + k CURL, one law, the Carrier view the Subject view plus '+
   'the gauge): the stations are row-graded -- row k reaches its '+
   'congruent parity image wF = -w to 1e-9 at bC = 116 + k and its '+
   'home at bC = k, each row at its own retarded epoch -- the dual\'s '+
   'radial band at the quarter, every bead rides its own leaf to '+
   'sub-pixel, the ensemble breathes without collapse, and the '+
   'Subject-view curl stands invariant under the Carrier tick',
   dilP.dH < 1e-9 && dilP.dHome < 1e-12 && dilP.band > 30 &&
   dilP.dmin < 0.15 && dilP.rminE > 60 && dilP.rmaxMin > 140 &&
   dilP.subInv < 1e-9);

// 16. the spinor half-turn: at the pair return (696 chronons) the
// sheet is flipped and the sky stands rotated by exactly pi ABOUT THE
// POLAR AXIS -- the axial half-turn (x, y, z) -> (-x, -y, z), not the
// spatial antipode -- and the double flip closes: full closure 1392.
// The closure numbers are proxy-chart data (696 = S x 12): checks 16
// and 17 verify the declaring chart's clock; the pair's own
// registered datum is the monotone dephasing
const sigP = vm.runInContext(`
(() => {
  view = "carrier"; frac = 0;
  sigC = 0; const A = skyState(0, 0).nodes;
  sigC = 1; const B = skyState(0, 0).nodes;
  let dTurn = 0, dAnti = 1e9;
  for (let i = 0; i < A.length; i++){
    const a = A[i].wF, b = B[i].wF;
    dTurn = Math.max(dTurn, Math.hypot(b[0]+a[0], b[1]+a[1], b[2]-a[2]));
    dAnti = Math.min(dAnti, Math.hypot(b[0]+a[0], b[1]+a[1], b[2]+a[2]));
  }
  sigC = 0; const C2 = skyState(0, 0).nodes;
  let dClose = 0;
  for (let i = 0; i < A.length; i++)
    dClose = Math.max(dClose, Math.hypot(...C2[i].wF.map((c, j) => c - A[i].wF[j])));
  return { dTurn, dAnti, dClose };
})()`, sandbox);
ok('the spinor half-turn: the sheet flip rotates the sky by exactly '+
   'pi about the polar axis (to 1e-9), is NOT the spatial antipode, '+
   'and the double flip closes exactly: 696 spinor-half, 1392 full',
   sigP.dTurn < 1e-9 && sigP.dAnti > 1 && sigP.dClose === 0);

// 17. the production clock: closure exercised through stepChronon
// itself -- at tick 696 the pair is home with the sheet flipped and
// the Carrier sky axially half-turned; at tick 1392 the full triple
// and the rendered geometry are home
const clkP = vm.runInContext(`
(() => {
  view = "carrier"; frac = 0;
  tS = 0; tC = 0; sigC = 0; pT = 0;
  const A = skyState(0, 0).nodes.map(n => n.wF.slice());
  for (let i = 0; i < 696; i++) stepChronon();
  const half = { tS, tC, sigC };
  const B = skyState(tS, tC).nodes;
  let dTurn = 0;
  for (let i = 0; i < A.length; i++)
    dTurn = Math.max(dTurn, Math.hypot(B[i].wF[0]+A[i][0],
      B[i].wF[1]+A[i][1], B[i].wF[2]-A[i][2]));
  for (let i = 0; i < 696; i++) stepChronon();
  const full = { tS, tC, sigC };
  const C3 = skyState(tS, tC).nodes;
  let dHome = 0;
  for (let i = 0; i < A.length; i++)
    dHome = Math.max(dHome, Math.hypot(...C3[i].wF.map((c, j) => c - A[i][j])));
  tS = 0; tC = 0; sigC = 0; pT = 0;
  return { half, full, dTurn, dHome };
})()`, sandbox);
ok('the production clock: after 696 stepChronon calls the pair is '+
   'home with sigma flipped and the Carrier sky exactly axially '+
   'half-turned; after 1392 the full triple and the geometry are '+
   'home', clkP.half.tS === 0 && clkP.half.tC === 0 &&
   clkP.half.sigC === 1 && clkP.dTurn < 1e-9 &&
   clkP.full.tS === 0 && clkP.full.tC === 0 && clkP.full.sigC === 0 &&
   clkP.dHome === 0);

// 18. the space-meridian obstruction (1-phase-6): the sky is the past
// light cone, not space. The labels are retarded (check 3) and the
// azimuth law twists each latitude step by one transport step, so
// simultaneous space -- the additive line at one instant -- admits no
// geodesic image: NO plane through the Observer contains more than two
// of the outer nodes. The orthogonal meridian through all cells lives
// on the shell panel (the register chart); the sky shows only its
// retarded image, the helix chain. Machine form: sweep all outer node
// pairs, count nodes coplanar with each pair and the Observer; the
// maximum is exactly 2 -- the obstruction, verified
{
  const outer = JSON.parse(vm.runInContext(
    'JSON.stringify(skyState(0,0).nodes.filter(n => n.outer).map(n => n.w))',
    sandbox));
  const cross = (a, b) => [a[1]*b[2]-a[2]*b[1], a[2]*b[0]-a[0]*b[2],
                           a[0]*b[1]-a[1]*b[0]];
  let maxCop = 0;
  for (let i = 0; i < outer.length; i++)
    for (let j = i + 1; j < outer.length; j++){
      const nv = cross(outer[i], outer[j]);
      const L = Math.hypot(...nv);
      if (L < 1e-6) continue;
      let cnt = 0;
      for (const w of outer)
        if (Math.abs((w[0]*nv[0] + w[1]*nv[1] + w[2]*nv[2])/L) < 1e-6) cnt++;
      maxCop = Math.max(maxCop, cnt);
    }
  ok('the space-meridian obstruction: no plane through the Observer '+
     'contains more than two outer nodes (maximum coplanar count = 2 '+
     'over all 276 pairs) -- simultaneous space has no geodesic image '+
     'in the light-cone sky; the meridian through all cells lives on '+
     'the shell panel, its retarded image is the helix chain',
     maxCop === 2);
}

// 19. the observable meridian: the kappa-step trace (1-phase-6). The
// meridian is a light-cone object; the capacity bound 4a < p resolves
// exactly kappa = 3 radial steps, and the observable segment threads
// the existing nodes cell +-a on shell L_a, terminating at the quarter
// fold. The trace alternates sides by exactly 11 pi/12 + pi/13 +
// pi/232 per step (route +; the route half-angle flips sign on route
// -): the deviation from a flat great circle is pi/156 - pi/232 per
// step -- the totality half-angle against the halved Carrier tick
{
  let capOK = true, nodeOK = true, azOK = true, drawOK = true;
  for (let a = 1; a <= 4; a++) if ((4*a < 13) !== (a <= 3)) capOK = false;
  const tr = JSON.parse(vm.runInContext(
    `(() => { skyMode = "cone"; const S = skyState(0,0); view = "subject";
       return JSON.stringify([1,-1].map(e => S.m0.trace[e].map(n =>
         ({ s: n.s, e: n.e, k: n.k, c: n.c, w: n.w })))); })()`, sandbox));
  const RSH = JSON.parse(vm.runInContext(
    'JSON.stringify(skyState(0,0).RSH)', sandbox));
  for (const [ri, e] of [[0, 1], [1, -1]].map((x, i) => [i, x[1]]))
    for (let a = 1; a <= 3; a++){
      const n = tr[ri][a - 1];
      if (n.s !== a - 1 || n.e !== e || n.k !== a ||
          n.c !== md(e*a, 13)) nodeOK = false;
      if (Math.abs(Math.hypot(...n.w) - RSH[a - 1]) > 1e-9) nodeOK = false;
    }
  const m2 = x => { while (x > Math.PI) x -= 2*Math.PI;
                    while (x < -Math.PI) x += 2*Math.PI; return x; };
  for (const [ri, e] of [[0, 1], [1, -1]].map((x, i) => [i, x[1]])){
    const want = -(11*Math.PI/12 + e*Math.PI/13 + Math.PI/232);
    for (let a = 1; a <= 2; a++){
      const A = tr[ri][a - 1].w, B = tr[ri][a].w;
      const d = m2(Math.atan2(B[1], B[0]) - Math.atan2(A[1], A[0]));
      if (Math.abs(m2(d - want)) > 1e-9) azOK = false;
    }
  }
  // the residual identity: |step + pi| = pi/12 - pi/13 - pi/232 = pi/156 - pi/232
  const residOK = Math.abs((Math.PI/12 - Math.PI/13 - Math.PI/232) -
                           (Math.PI/156 - Math.PI/232)) < 1e-12;
  // the guide is smooth in every view and state: no seam kink, no
  // sheet jump (one Huber-smoothed sheet-fair chart, the pi-branch
  // an exact point reflection, the quarter residual alone swept)
  let smoothOK = true;
  for (const [vv, ss, cc] of [['subject',0,0],['subject',5,117],
                              ['carrier',5,117],['carrier',0,58],
                              ['carrier',2,110],['carrier',6,174]]){
    const mx = +vm.runInContext(
      `(() => { view = "${vv}"; skyMode = "cone"; frac = 0; const S = skyState(${ss},${cc});
         let mx = 0;
         for (const e of [1,-1]){ let prev = null;
           for (let j = 0; j <= 2600; j++){ const a = j*13/2600, p = S.m0.pos(e, a);
             if (prev && Math.abs(a - 6.5) > 0.02)
               mx = Math.max(mx, Math.hypot(p[0]-prev[0],
                                     p[1]-prev[1], p[2]-prev[2]));
             prev = p; } }
         return mx; })()`, sandbox);
    if (mx > 45) smoothOK = false;   // the quarter-residual sweep peaks near ~40 at the deepest flow; genuine jumps measured well above
  }
  vm.runInContext('view = "subject"; tS = 0; tC = 0', sandbox);
  if (!smoothOK) drawOK = false;
  // the smooth spiral passes the nodes exactly and terminates at the
  // fold: the continuous law at integer a equals the drawn node
  const resid = +vm.runInContext(
    `(() => { view = "subject"; frac = 0; const S = skyState(0,0);
       let w = 0;
       for (const e of [1,-1]) for (let a = 1; a <= 3; a++){
         const n = S.m0.trace[e][a-1], p = S.m0.pos(e, a);
         w = Math.max(w, Math.hypot(p[0]-n.wF[0], p[1]-n.wF[1], p[2]-n.wF[2]));
       } return w; })()`, sandbox);
  if (resid > 1e-9) drawOK = false;
  // ONE flow map: the guides flow through flowF, the nodes' own map,
  // so every station of both meridians threads exactly in both views
  // at every state -- direct and echo, including the dispersion
  // stations, where the meridians delocalize WITH their nodes
  let uniOK = true;
  for (const [vv, ss, cc] of [['subject',0,0],['carrier',3,51],
                              ['carrier',0,58],['carrier',5,117],
                              ['carrier',2,110],['carrier',6,174],
                              ['carrier',8,200]]){
    const res = +vm.runInContext(
      `(() => { view = "${vv}"; skyMode = "cone"; frac = 0; const S = skyState(${ss},${cc});
         let r = 0;
         for (const e of [1,-1]){
           for (let a = 1; a <= 3; a++){
             const n = S.m0.trace[e][a-1], p = S.m0.pos(e, a);
             r = Math.max(r, Math.hypot(p[0]-n.wF[0], p[1]-n.wF[1], p[2]-n.wF[2]));
           }
           [[0,10],[1,11],[2,12]].forEach(([i,k]) => {
             const n = S.m0.traceE[e][i], p = S.m0.pos(e, k);
             r = Math.max(r, Math.hypot(p[0]-n.wF[0], p[1]-n.wF[1], p[2]-n.wF[2]));
           });
           [1,2,3,10,11,12].forEach((t,i) => {
             const n = S.m3.st[e][i], p = S.m3.pos(e, t);
             r = Math.max(r, Math.hypot(p[0]-n.wF[0], p[1]-n.wF[1], p[2]-n.wF[2]));
           });
         }
         return r; })()`, sandbox);
    if (res > 1e-9) uniOK = false;
  }
  vm.runInContext('view = "subject"; tS = 0; tC = 0', sandbox);
  if (!uniOK) drawOK = false;
  render('subject', 0, 0, 0, 'cone');
  const acc = recs.spc.filter(r => r[0] === 'stroke' && r[1] === '#3987e5');
  // FOUR RAYS as depth-banded Bezier chains (the ported 173 scheme):
  // the arc strokes are the band runs -- alphas exact on the [0.1,
  // 0.9] 24-band grid, width riding the same band at nominal 1.55 --
  // plus exactly 4 fold rings (2 routes x 2, alpha 0.35, width 1);
  // the Observer dot the one fill (the nodes are their own station
  // marks); the below-resolution tower interior between the folds is
  // not drawn
  const bezC = recs.spc.filter(r => r[0] === 'bez').length;
  const onGrid = r => r[2] >= 0.1 - 1e-9 && r[2] <= 0.9 + 1e-9 &&
    Math.abs(r[2] - (0.1 + Math.round((r[2] - 0.1)*30)/30)) < 1e-9;
  const wLaw = (r, nom) =>
    Math.abs(r[3] - nom*(0.1 + 0.9*(r[2] - 0.1)/0.8)) < 1e-9;
  const accR = acc.filter(r => Math.abs(r[2] - 0.35) < 1e-9 &&
                               Math.abs(r[3] - 1) < 1e-9);
  const accB = acc.filter(r => !accR.includes(r));
  if (!(bezC > 1000 && accR.length === 4 && accB.length >= 8 &&
        accB.every(r => onGrid(r) && wLaw(r, 1.55)))) drawOK = false;
  const accF = recs.spc.filter(r => r[0] === 'fill' && r[1] === '#3987e5');
  if (accF.length !== 1) drawOK = false;
  // OWNERSHIP: the Subject's own locus is the frame origin, never
  // dressed -- every arc of both meridians anchors at the drawn
  // Observer (a = 0, 13), and the null self-echo bounces at the
  // centre (a = 13/2), at every clock state in both views
  let ancOK = true;
  for (const [vv, ss, cc] of [['subject',0,0],['carrier',0,58],
                              ['carrier',5,117],['carrier',2,110],
                              ['carrier',6,174],['carrier',3,231]]){
    const mx = +vm.runInContext(
      `(() => { view = "${vv}"; skyMode = "cone"; frac = 0; const S = skyState(${ss},${cc});
         let mx = 0;
         for (const e of [1,-1]) for (const a of [0, 6.5, 13]){
           mx = Math.max(mx, Math.hypot(...S.m0.pos(e, a)),
                             Math.hypot(...S.m3.pos(e, a)));
         } return mx; })()`, sandbox);
    if (mx > 1e-9) ancOK = false;
  }
  vm.runInContext('view = "subject"; tS = 0; tC = 0', sandbox);
  if (!ancOK) drawOK = false;
  // ONE Dirac flow across the three representations: the node images
  // are computed by the same flow law in helix, cone, and Hopf modes
  // -- the toggle changes the fibers, never the dynamics
  const modeEq = JSON.parse(vm.runInContext(
    `(() => { view = "carrier"; frac = 0;
       const im = m => { skyMode = m;
         return skyState(5, 117).nodes.map(n => n.wF.map(x => +x.toFixed(9))); };
       const a = JSON.stringify(im("helix"));
       const ok = a === JSON.stringify(im("cone")) &&
                  a === JSON.stringify(im("hopf"));
       view = "subject"; skyMode = "cone"; return JSON.stringify(ok); })()`,
    sandbox));
  if (!modeEq) drawOK = false;
  // M3, the momentum-quarter dual: the same meridian law at winding
  // five. The double-cover coordinate u = 5t mod 26 selects the lift
  // (k = u even half-winds with the ray's route, 26 - u odd with the
  // route flipped); the azimuth is the node law PH3 with continuous
  // arguments, the curl rides the row k(t): the twelve stations
  // (cells +-5t at the tent shells) are threaded at residual zero.
  // Drawn as depth-banded Bezier chains, the same four-ray assembly
  // as M0 in momentum red at nominal 1.35 (the subordination on the
  // nominal), plus exactly 4 fold ticks (alpha 0.3, width 1)
  const mer = recs.spc.filter(r => r[0] === 'stroke' && r[1] === '#d0453c');
  const merT = mer.filter(r => Math.abs(r[2] - 0.3) < 1e-9 &&
                               Math.abs(r[3] - 1) < 1e-9);
  const merB = mer.filter(r => !merT.includes(r));
  if (!(merT.length === 4 && merB.length >= 8 &&
        merB.every(r => onGrid(r) && wLaw(r, 1.35)))) drawOK = false;
  // THE DRIVE STEP FACTORS EXACTLY (the tower identity): the scale
  // step is the rung ladder x3 = g^4 (order kappa = 3), the quarter
  // is Ihat = g^{-kappa} = 5 = i (order 4, the M3/M9 direction), and
  // heights 4 - 3 = 1 give g = g^4 g^{-3} = 3 * 5 = 2 on F13:
  // one chronon = one scale step times one quarter turn -- the CRT
  // factorization C12 = C4 x C3 (00:C20's channel), so kappa scale
  // steps of four heights close one drive revolution (4 kappa = p-1)
  const md13f = x => ((x % 13) + 13) % 13;
  const powm = (b, e) => { let r = 1; for (let i = 0; i < e; i++) r = md13f(r*b); return r; };
  const facOK = powm(2,4) === 3 && powm(2,9) === 5 && md13f(3*5) === 2 &&
                powm(3,3) === 1 && powm(3,1) !== 1 &&
                powm(5,4) === 1 && powm(5,2) === 12;
  if (!facOK) drawOK = false;
  // THE COVERING (isotropy at the resolved mesh): the winding family
  // m = 1..12 under the ONE meridian law -- stations at t in
  // {1,2,3,10,11,12}, tent shells, the C26 double-cover fold with the
  // route flip on odd half-winds -- covers the node field completely:
  // 72 of 72 nodes, 24 per shell, multiplicity 1 on odd rows and 3 on
  // even rows (the sheet parity: 36 nodes once, 36 thrice, 144 slots).
  // Each drawn meridian is ONE LABEL of the covering family
  const covM = new Map();
  for (let m = 1; m <= 12; m++)
    for (const ray of [1, -1])
      for (const t of [1, 2, 3, 10, 11, 12]){
        const mW = Math.floor(m*t/13), even = mW % 2 === 0;
        const kk = even ? m*t - 13*mW : 13*(mW+1) - m*t;
        const ee = even ? ray : -ray;
        const s = t <= 3 ? t - 1 : 12 - t;
        const key = s + ',' + ee + ',' + kk;
        covM.set(key, (covM.get(key) || 0) + 1);
      }
  let covOK = covM.size === 72;
  for (const [key, mult] of covM){
    const kk = +key.split(',')[2];
    if (mult !== (kk % 2 === 1 ? 1 : 3)) covOK = false;
  }
  for (let s = 0; s < 3; s++)
    if ([...covM.keys()].filter(k => k.startsWith(s + ',')).length !== 24)
      covOK = false;
  if (!covOK) drawOK = false;
  // THE PAIR GEOMETRY IS EXACT: (a) the eight rays launch tangent to
  // the clock axis at the unregistered origin -- the drive direction:
  // the two quadratures of F = E + iB co-propagate, and no transverse
  // label exists at the origin (ownership; isotropy); (b) the quarter
  // fold enacts the quarter: the horizon ends fuse pairwise, M0(e)
  // retarded fold = M3(-e) advanced fold and M0(e) advanced fold =
  // M3(-e) retarded fold -- the duality exchange E <-> B, route and
  // time both flipped, four horizon points fusing eight ray-ends;
  // (c) the winding-5 family is ramified at the half cell: all four
  // M3 rays pass one point exactly at t = 13/10 and 13 - 13/10
  // (cell 13/2, the 1-algebra half: route and tent degenerate,
  // 6.5 = 13 - 6.5); M0's ramification point is the origin itself
  // (r(13/2) = 0, absorbed in the self-echo)
  let pairOK = true;
  for (const [vv, ss, cc] of [['subject',0,0],['carrier',5,117]]){
    const r = JSON.parse(vm.runInContext(
      `(() => { view = "${vv}"; skyMode = "cone"; frac = 0; const S = skyState(${ss},${cc});
         const d = (a,b) => Math.hypot(a[0]-b[0],a[1]-b[1],a[2]-b[2]);
         let mx = 0;
         for (const e of [1,-1]){
           mx = Math.max(mx, d(S.m0.pos(e,3.25), S.m3.pos(-e,9.75)));
           mx = Math.max(mx, d(S.m0.pos(e,9.75), S.m3.pos(-e,3.25)));
         }
         const P = S.m3.pos(1, 1.3);
         for (const ray of [1,-1]) for (const t of [1.3, 11.7])
           mx = Math.max(mx, d(S.m3.pos(ray,t), P));
         let tmx = 0;
         const h = 1e-4;
         for (const e of [1,-1])
           for (const [f, a0, dir] of [[S.m0.pos,0,1],[S.m0.pos,13,-1],
                                       [S.m3.pos,0,1],[S.m3.pos,13,-1]]){
             const p1 = f(e, a0 + dir*h), p2 = f(e, a0 + dir*2*h);
             const dv = [p2[0]-p1[0], p2[1]-p1[1], p2[2]-p1[2]];
             tmx = Math.max(tmx, Math.acos(Math.abs(dv[2])/Math.hypot(...dv)));
           }
         return JSON.stringify([mx, tmx]); })()`, sandbox));
    if (r[0] > 1e-9 || r[1] > 0.002) pairOK = false;
  }
  vm.runInContext('view = "subject"; tS = 0; tC = 0', sandbox);
  if (!pairOK) drawOK = false;

  const m3law = JSON.parse(vm.runInContext(
    `(() => { skyMode = "cone"; const S = skyState(0,0); const md13 = x => ((x%13)+13)%13;
       let good = true;
       for (const ray of [1,-1]) [1,2,3,10,11,12].forEach((t,i) => {
         const u = 5*t, mW = Math.floor(u/13), even = mW % 2 === 0;
         const kk = even ? u - 13*mW : 13*(mW+1) - u;
         const ee = even ? ray : -ray;
         const sh = t <= 3 ? t - 1 : 12 - t;
         const n = S.m3.st[ray][i];
         if (!n || n.e !== ee || n.k !== kk || n.s !== sh ||
             md13(n.e*n.k) !== md13(ray*5*t)) good = false;
       });
       return JSON.stringify(good); })()`, sandbox));
  if (!m3law) drawOK = false;
  // the spirals live in the light-cone mode alone; nodes identical
  for (const mm of ['helix', 'hopf']){
    render('subject', 0, 0, 0, mm);
    if (recs.spc.some(r => r[0] === 'stroke' && r[1] === '#3987e5'))
      drawOK = false;
  }
  ok('the observable meridian: the kappa-step trace threads the nodes '+
     'cell +-a on shell L_a exactly (capacity bound 4a < p: three steps), '+
     'alternating sides by exactly 11pi/12 + pi/13 + pi/232 per step '+
     '(residual from a flat great circle: pi/156 - pi/232, the leak '+
     'signature; route-minus mirrored), and the smooth retarded-meridian '+
     'spiral passes the nodes exactly (residual 0) and terminates at the '+
     'quarter-fold tick, one retarded flow law shared with the nodes '+
     '-- drawn in the light-cone mode alone',
     capOK && nodeOK && azOK && residOK && drawOK);
}

console.log(fails ? `\n${fails} FAILURES` : '\nall checks pass');
process.exit(fails ? 1 : 0);
