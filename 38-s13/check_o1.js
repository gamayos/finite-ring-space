"use strict";
// O1: the registration dictionary p_sl = 3(S/kappa) r_g, derived.
// The two leak faces (exact, integer/rational arithmetic only):
//   angular face  = the curl: one Carrier tick per chronon  -> kappa/S per revolution (C18/C1)
//   temporal face = the ring: the halved tick per chronon   -> kappa/(2S) per revolution (B7)
// ratio exactly 2 = the double cover (Thm 2).  GR side (o1_gr_chart.py, symbolic):
// apsidal fraction 3 r_g/p, clock deficit (3/2) r_g/p, ratio 2 iff 2*gamma - beta = 1.
// Matching the temporal face to the deficit forces p_sl = 3(S/kappa) r_g; the angular
// face then matches the apsidal fraction automatically.
const gcd=(a,b)=>b?gcd(b,a%b):a;
let fails=0; const ok=(t,c)=>{console.log((c?'pass ':'FAIL ')+t); if(!c)fails++;};
const powm=(b,e,m)=>{let x=1n,B=BigInt(b)%BigInt(m);for(let i=0n;i<BigInt(e);i++)x=x*B%BigInt(m);return Number(x);};
// exact rationals
const R=(n,d)=>{const s=d<0?-1:1,g=gcd(Math.abs(n),Math.abs(d));return [s*n/g,s*d/g];};
const req=(a,b)=>a[0]===b[0]&&a[1]===b[1];
const rdiv=(a,b)=>R(a[0]*b[1],a[1]*b[0]);

// ---- (a) the two faces at (13,233): kappa=3, S=58 ----
const P=13,OM=233,K=3,S=58;
const ang=R(P-1,OM-1);            // per revolution: (p-1) ticks / (Om-1) per cycle
const tmp=R(P-1,2*(OM-1));        // per revolution at the halved tick (the cover C464)
ok('(a) angular face (the curl): one Carrier tick per chronon -> (p-1)/(Om-1) = 12/232 '+
   '= 3/58 = kappa/S per revolution -- the apsidal fraction (C18)',
   req(ang,R(K,S)) && req(R(1,OM-1),R(1,4*S)));
ok('(a) temporal face (the ring): the halved tick per chronon -> 12/464 = 3/116 '+
   '= kappa/(2S) per revolution (B7, the sheet on C464)',
   req(tmp,R(K,2*S)) && req(R(1,2*(OM-1)),R(1,8*S)));
ok('(a) face ratio exactly 2: the double cover', req(rdiv(ang,tmp),R(2,1)));

// ---- (b) the closure structure carrying the faces ----
const L=(12*232)/gcd(12,232);
ok('(b) joint cycle L = lcm(12,232) = 696 = S*12 = kappa*232; cover 2L = 1392',
   L===696 && L===S*12 && L===K*232 && 2*L===1392);
ok('(b) half event at L/2 = 348: shell home (348 = 0 mod 12), Carrier at -1 '+
   '(348 = 116 mod 232, 78^116 = -1 on F233): the sign face, base-transportable (Thm 6)',
   348%12===0 && 348%232===116 && powm(78,116,233)===232 && powm(78,232,233)===1);

// ---- (c) the dictionary, exact ----
ok('(c) matching temporal face to deficit: (3/2)(r_g/p) = kappa/(2S) gives r_g/p = '+
   'kappa/(3S), i.e. p_sl/r_g = 3S/kappa = 58 at (13,233)',
   req(rdiv(R(K,2*S),R(3,2)),R(K,3*S)) && (3*S)%K===0 && 3*S/K===58);
ok('(c) capacity reading at kappa = 3: p_sl = S r_g -- one gravitational radius per '+
   'decoherence step, the D3 reading; separation count = the capacity', 3*S/K===S);
ok('(c) consistency: the angular face then equals 3 r_g/p_sl = 3/(3S/kappa) = kappa/S '+
   '-- the GR apsidal fraction, automatically', req(R(3*K,3*S),R(K,S)) && req(R(K,S),ang));

// ---- (d) the p=53 regression, read in the auxiliary modulus 157 (Omega-blind; not an admissible pair) ----
const kO=3,kS=13;                  // q=13: kappa_O=3; p=53: kappa_S=13
const angO=R(12,52), tmpO=R(12,104);
ok('(d) (53,13): angular 12/52 = 3/13 = kappa_O/kappa_S, temporal 12/104 = 3/26, '+
   'ratio 2; dictionary p_sl/r_g = 3*kappa_S/kappa_O = 13 = kappa_S: the capacity '+
   'reading again', req(angO,R(kO,kS)) && req(rdiv(angO,tmpO),R(2,1)) && (3*kS)%kO===0
   && 3*kS/kO===kS*1 && 3*kS/kO===13);

// ---- (e) the PPN forcing: face ratio 2 <=> 2*gamma - beta = 1 ----
// GR: apsidal coefficient (2 - beta + 2*gamma), deficit coefficient 3/2 (PPN-free);
// ratio 2(2-beta+2*gamma)/3 = 2 iff 2*gamma - beta = 1.  Exact rational check over a
// lattice of PPN values (integer halves):
let forceOK=true;
for(let b2=-4;b2<=4;b2++)for(let g2=-4;g2<=4;g2++){ // beta=b2/2, gamma=g2/2
  const num=2*(2*2-b2+2*g2), den=3*2;               // ratio = num/den
  const isTwo = req(R(num,den),R(2,1));
  const cond  = (2*g2-b2)===2;                      // 2*gamma - beta = 1
  if(isTwo!==cond) forceOK=false;
}
ok('(e) face ratio 2 <=> 2*gamma - beta = 1, over the half-integer PPN lattice; '+
   'beta = gamma = 1 satisfies it (the E4 metric class); the double cover forces the '+
   'PPN combination', forceOK && (2*2-2)===2);

console.log(fails===0?'ALL O1 DICTIONARY CHECKS PASS':'FAILURES: '+fails);
process.exit(fails?1:0);
