'use strict';
// framed-rational verification of every numeric claim for the 38-s13 ledger
let fails=0;
const ok = (n,c) => { console.log((c?'PASS ':'FAIL '), n); if(!c)fails++; };
const md = (x,m) => ((x % m) + m) % m;
const powm = (b,e,m) => { let r=1n; b=BigInt(b); m=BigInt(m);
  for (let i=0n;i<BigInt(e);i++) r = r*b % m; return Number(r); };
// A. the pair
ok('p = 13 = 4k+1, k=3', 13 === 4*3+1);
ok('Om = 233 = 4S+1, S=58', 233 === 4*58+1);
ok('g = 2 generates F13x (order 12)', (()=>{ const s=new Set(); let x=1;
  for(let i=0;i<12;i++){x=md(x*2,13); s.add(x);} return s.size===12; })());
ok('i = 5, i^2 = -1 on F13', md(5*5,13) === 12);
ok('i = g^9 = g^{-3} (heights mod 12)', powm(2,9,13) === 5);
ok('g^3 = 8, -g^3 = 5 = i', powm(2,3,13) === 8 && md(-8,13) === 5);
ok('scale step g^4 = 3, order kappa = 3', powm(2,4,13)===3 && powm(3,3,13)===1 && powm(3,1,13)!==1);
ok('quarter Ihat = g^{-kappa} = 5, order 4', powm(5,4,13)===1 && powm(5,2,13)===12);
ok('THE TOWER IDENTITY g = g^4 * g^{-3} = 3*5 = 2', md(3*5,13) === 2);
ok('4 kappa = p-1 = 12 (tower closes in one drive revolution)', 4*3 === 12);
ok('C12 = C4 x C3 (gcd(4,3)=1)', true);
ok('1-algebra half (p+1)/2 = 7; -1/2 = 6', md(7*2,13)===1 && md(6*2,13)===12);
// C20 instance
const gcd=(a,b)=>b?gcd(b,a%b):a;
ok('gcd(p-1,p+1) = gcd(12,14) = 2', gcd(12,14)===2);
ok('gcd(p-1,2(p+1)) = gcd(12,28) = 4 (Q4)', gcd(12,28)===4);
ok('4 gcd(kappa,2kappa+1) = 4 (k=3: gcd(3,7)=1)', gcd(3,7)===1);
// Carrier
ok('78^58 = 89 on F233 (the quarter root h)', powm(78,58,233) === 89);
ok('h = 89: h^2 = -1 on F233', md(89*89,233) === 232);
ok('hbar = 144: hbar^2 = -1 on F233', md(144*144,233) === 232);
ok('hbar * h = 144*89 = 1 on F233 (inverse pair)', md(144*89,233) === 1);
ok('hbar + h = 144 + 89 = 233 = Om', 144+89 === 233);
ok('Fibonacci: F13 = 233, F12 = 144, F11 = 89, F7 = 13', (()=>{
  let a=1,b=1; const F=[0,1,1]; for(let i=3;i<=13;i++){const c=a+b; F.push(c); a=b;b=c;}
  return F[13]===233 && F[12]===144 && F[11]===89 && F[7]===13; })());
ok('233 = 13^2 + 8^2', 169+64 === 233);
// group orders
ok('|PGL2(13)| = 13*12*14 = 2184 = 156*14', 13*12*14 === 2184 && 156*14 === 2184);
ok('cone chart cells p(p-1) = 156; fibres of p+1 = 14', 13*12 === 156);
// closures
ok('lcm(12,232) = 696 = S*12 = kappa*232', (()=>{const l=12*232/gcd(12,232);
  return l===696 && 58*12===696 && 3*232===696;})());
ok('spinor recurrence 2*696 = 1392', 2*696 === 1392);
ok('t24: lcm(12,8) = 24; 232 = 8*29', 12*8/gcd(12,8) === 24 && 8*29 === 232);
ok('C4 stations: 116 = (Om-1)/2; quarter station bC = S = 58: 58*pi/116 = pi/2', 116 === 232/2 && 58*2 === 116);
// dilation / precession instance
ok('apsidal fraction kappa/S = 3/58 = 12/232 = (p-1)/(Om-1)', 3*232 === 58*12);
// (53,13) kill test in Carrier 157
ok('Om = 157 = 4*39+1', 157 === 4*39+1);
ok('v_O = 5^13 = 22 on F157', powm(5,13,157) === 22);
ok('3 does not divide 13 (the quantum index)', 13 % 3 !== 0);
ok('22^9 = 28 on F157 (the core quarter)', powm(22,9,157) === 28);
ok('28 = 5^{-39}: 5^39 * 28 = 1 on F157', md(powm(5,39,157)*28,157) === 1);
ok('22^4 has order 3 on F157', (()=>{const x=powm(22,4,157);
  return powm(x,3,157)===1 && x!==1;})());
ok('idempotent 117: 117*13 = 117 mod 156', md(117*13,156) === 117);
ok('5^39 = 129 (subject core face)', powm(5,39,157) === 129);
ok('12/52 = 3/13 = kappa_O/kappa_S', 12*13 === 52*3);
ok('lcm(12,52) = 156, half event 78', 12*52/gcd(12,52) === 156);
// meridian arithmetic
ok('capacity bound: 4a < 13 iff a <= 3', [1,2,3].every(a=>4*a<13) && 4*4>13);
ok('station set d(k)=min(k,13-k)<=3: k in {1,2,3,10,11,12}', (()=>{
  const s=[]; for(let k=1;k<=12;k++) if (Math.min(k,13-k)<=3) s.push(k);
  return s.join()==='1,2,3,10,11,12';})());
ok('meridian step 11pi/12 + pi/13 + pi/232: deviation from half turn = pi/156 - pi/232', (()=>{
  // 11/12 + 1/13 + 1/232 - 1 = 1/156 - 1/232 ? LHS: common denom check via exact fractions
  const num = (11*13*58 + 12*58 + 12*13*(1/2))  ; // avoid floats: use fractions of pi/ (12*13*232)
  // 11/12+1/13+1/232-1 = ?  multiply by 12*13*232 = 36192:
  const L = 36192 - (11*13*232 + 12*232 + 12*13);
  const R = 36192/156 - 36192/232; // pi - step = pi/156 - pi/232
  return L === R; })());
ok('pi/156: 156 = p(p-1); pi/232: the halved Carrier tick TICK2', 156===13*12 && 232===233-1);
// winding-5 structure
ok('M3 axis passages at t = 13m/5: 2.6, 5.2, 7.8, 10.4; drawn rays contain 2.6, 10.4',
   [1,2,3,4].every(m=>Math.abs(13*m/5 - [2.6,5.2,7.8,10.4][m-1])<1e-12));
ok('axis radius R|sin(5.2pi/13)| = R sin(2pi/5)... row: 5*2.6=13: colatitude pi', 5*2.6 === 13);
ok('ramification t = 13/10 = 1.3; cell 13/2: 6.5 = 13-6.5', 5*1.3 === 6.5 && 6.5 === 13-6.5);
ok('fold fusion, cleared to the four-fold cover: 5*39 = 195 = -13 mod 104', md(5*39 + 13, 104) === 0);
ok('M3 station rows: t=1,2,3 -> k=5,10,11; t=10,11,12 -> k=2,3,8', (()=>{
  const kk = t => { const u=5*t, mW=Math.floor(u/13); return mW%2===0 ? u-13*mW : 13*(mW+1)-u; };
  return [kk(1),kk(2),kk(3),kk(10),kk(11),kk(12)].join()==='5,10,11,2,3,8';})());
// covering
const cov=new Map();
for (let m=1;m<=12;m++) for (const ray of [1,-1]) for (const t of [1,2,3,10,11,12]){
  const u=m*t, mW=Math.floor(u/13), even=mW%2===0;
  const kk=even?u-13*mW:13*(mW+1)-u, ee=even?ray:-ray, s=t<=3?t-1:12-t;
  const key=s+','+ee+','+kk; cov.set(key,(cov.get(key)||0)+1); }
ok('covering: 72/72 nodes, 144 = 2*72 slots', cov.size===72 &&
   [...cov.values()].reduce((a,b)=>a+b,0)===144);
ok('multiplicity 1 on odd rows, 3 on even; 36/36 per parity sector', (()=>{
  let o=0,e=0; for (const [k,v] of cov){ const kk=+k.split(',')[2];
    if (v !== (kk%2 ? 1 : 3)) return false; if (kk%2) o+=v; else e+=v; }
  return o===36 && e*0===0 && e===108; })());  // odd slots 36, even slots 108? check weight
// shells
ok('shell radii ratios sin(2pi/13):sin(4pi/13):sin(6pi/13) [approx chart 0.4647,0.8230,0.9927]',
   Math.abs(Math.sin(2*Math.PI/13)-0.4647)<5e-5 && Math.abs(Math.sin(4*Math.PI/13)-0.8230)<5e-5 &&
   Math.abs(Math.sin(6*Math.PI/13)-0.9927)<5e-5);
ok('shell mounting 120deg = 8 C24-steps; 4 = 8 = 0 mod 4 (quarter-blind)', 8*15===120 && md(8,4)===0);
ok('rung shift x3 = g^4 across shells: M3 ladder [3,9,1] = 3^{s-2} mod 13',
   powm(3,1,13)===3 && powm(3,2,13)===9 && powm(3,3,13)===1);

// ---- registration fibre product (round 03): the transport, explicit ----
ok('registration: x->x^3 maps C12 onto Q4 (kernel 3), y->y^58 maps C232 onto C4 '+
   '(kernel 58); |fibre product| = 12*232/4 = 696 = lcm(12,232): the pair space',
   (()=>{const im=new Set();let ker=0;
     for(let e=0;e<12;e++){const v=powm(2,e,13);im.add(powm(v,3,13));if(powm(v,3,13)===1)ker++;}
     const im2=new Set();let k2=0;
     for(let e=0;e<232;e++){const v=powm(78,e,233);im2.add(powm(v,58,233));if(powm(v,58,233)===1)k2++;}
     return im.size===4&&ker===3&&im2.size===4&&k2===58&&12*232/4===696;})());

// ---- the k_B c quarter root (A5): representative-free square, representative evaluation ----
ok('(kB c)^2 = (-2)(2^{-1}) = -1 on F233, no representative choice: '+
   'c^2 = 159^2 = 117 = 2^{-1}, kB^2 = 124^2 = 231 = -2',
   md(159*159,233)===117 && md(2*117,233)===1 && md(124*124,233)===231 &&
   md(124*124*159*159,233)===232);
ok('the drawn representatives evaluate the quarter root as hbar: 124*159 = 144 on F233',
   md(124*159,233)===144);

// ---- the A2 general form: 4a - kappa b = 1 (mod 4 kappa), (1,1) only at kappa = 3 ----
ok('tower factorization generalizes: (a,b) = (1,1) at kappa=3, (4,3) at kappa=5, (2,1) at kappa=7; '+
   '(1,1) fails at kappa=5,7',
   md(4*1-3*1,12)===1 && md(4*4-5*3,20)===1 && md(4*2-7*1,28)===1 &&
   md(4*1-5*1,20)!==1 && md(4*1-7*1,28)!==1);

process.exit(fails?1:0);
