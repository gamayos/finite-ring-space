"use strict";
// O2: the multiplicity grading of the meridian covering, derived.
// Ground rule (the lab's covering, check_s13.js): slot (m, ray, t) with
// u = m*t, sheet w = floor(u/p), lands on row k = u mod p (w even) or
// p - (u mod p) (w odd), route = ray * (-1)^w, shell = min(t, p-t) - 1.
// Structure: each node has four candidate slots (windings +-M, params +-a)
// whose wrap counts satisfy the REFLECTION IDENTITIES
//   w(M,a) + w(p-M,a) = a-1,   w(M,p-a) + w(p-M,p-a) = p-1-a,
//   w(M,a) + w(M,p-a) = M-1,   w(p-M,a) + w(p-M,p-a) = p-1-M,
// so the four-sum is p-2, ODD: an odd number of candidates match their
// required sheet parity -> multiplicity 1 or 3, never 0, 2, 4.
// Corollaries: the covering has no holes (mu >= 1: completeness is a
// theorem, not a check); the decider is the row parity: mu = 3 iff k even
// (proven in closed form at shell 1: w(p-k, p-1) = p-1-k; machine-complete
// per instance for the higher shells); odd rows are covered by their
// direct slot alone -- the echo (sheet-crossing) slots reach the even
// sector only.  The carrier O2 suspected -- the sheet parity of the
// double cover -- is confirmed: it is exactly the wrap-count parity.
const fl=Math.floor;
let fails=0; const ok=(t,c)=>{console.log((c?'pass ':'FAIL ')+t); if(!c)fails++;};
const w=(m,t,p)=>fl(m*t/p);

// ---- (a) the reflection identities, general ----
let refOK=true;
for(const p of [5,13,17,29]) for(let a=1;a<p;a++) for(let b=1;b<p;b++)
  if(w(a,b,p)+w(p-a,b,p)!==b-1) refOK=false;
ok('(a) reflection identity floor(ab/p) + floor((p-a)b/p) = b-1, all a,b, '+
   'p in {5,13,17,29}', refOK);

// ---- covering builder (the ground rule, general p = 4*kappa+1) ----
function cover(p){
  const K=(p-1)/4, cov=new Map(), slots=new Map();
  const params=[]; for(let t=1;t<=K;t++)params.push(t); for(let t=p-K;t<=p-1;t++)params.push(t);
  for(let m=1;m<p;m++) for(const ray of [1,-1]) for(const t of params){
    const u=m*t, mW=fl(u/p), even=mW%2===0;
    const kk=even?u-p*mW:p*(mW+1)-u, ee=even?ray:-ray, s=Math.min(t,p-t)-1;
    const key=s+','+ee+','+kk;
    cov.set(key,(cov.get(key)||0)+1);
    (slots.get(key)||slots.set(key,[]).get(key)).push([m,ray,t]);
  }
  return {K,cov,slots};
}

// ---- (b) the law at the instance p = 13 ----
{
  const p=13,{K,cov,slots}=cover(p);
  ok('(b) 72/72 nodes, 144 slots, mu in {1,3}', cov.size===72 &&
     [...cov.values()].reduce((x,y)=>x+y,0)===144 &&
     [...cov.values()].every(v=>v===1||v===3));
  ok('(b) decider: mu = 3 iff the row is even; 36 nodes once + 36 thrice '+
     '= 144 = 36 + 108',
     [...cov].every(([k,v])=>v===(+k.split(',')[2]%2?1:3)) &&
     [...cov.values()].filter(v=>v===1).length===36);
  ok('(b) the position law (shell-parity duality): every odd-row node has one '+
     'slot -- direct (t <= kappa) on the odd shells a = 1, 3, echo on the even '+
     'shell a = 2; every even-row node has three with the dual split (1 direct '+
     '+ 2 echo on odd shells, 2 direct + 1 echo on the even shell); direct and '+
     'echo slots balance 72/72',
     [...slots].every(([key,ss])=>{
       const [s,,kk]=key.split(',').map(Number), a=s+1;
       const odd=kk%2===1, d=ss.filter(([,,t])=>t<=K).length, e=ss.length-d;
       return odd ? (ss.length===1 && (a%2===1 ? d===1 : e===1))
                  : (ss.length===3 && (a%2===1 ? (d===1&&e===2) : (d===2&&e===1)));
     }) &&
     [...slots.values()].flat().filter(([,,t])=>t<=K).length===72);
}

// ---- (c) the four-candidate structure per node, p = 13 ----
{
  const p=13, inv=x=>{for(let y=1;y<p;y++)if(x*y%p===1)return y; };
  let idOK=true, muOK=true;
  for(let a=1;a<=3;a++) for(let k=1;k<p;k++){
    const M=(k*inv(a))%p===0?p:(k*inv(a))%p;
    const A=w(M,a,p),B=w(p-M,a,p),C=w(M,p-a,p),D=w(p-M,p-a,p);
    if(A+B!==a-1||C+D!==p-1-a||A+C!==M-1||B+D!==p-1-M||A+B+C+D!==p-2) idOK=false;
    // required parities: A even, B odd, C odd, D even; count matches:
    const mu=(A%2===0)+(B%2===1)+(C%2===1)+(D%2===0);
    if(mu!==(k%2?1:3)) muOK=false;
  }
  ok('(c) per-node candidate identities: A+B = a-1, C+D = p-1-a, A+C = M-1, '+
     'B+D = p-1-M, four-sum = p-2 (odd) -- all shells, all rows', idOK);
  ok('(c) the four-candidate parity count reproduces mu = 3 iff k even, '+
     'all shells, all rows', muOK);
}

// ---- (d) the closed-form decider at shell 1, general ----
{
  let d1=true;
  for(const p of [5,13,17,29]) for(let k=1;k<p;k++)
    if(w(p-k,p-1,p)!==p-1-k) d1=false;
  ok('(d) shell-1 decider in closed form: w(p-k, p-1) = p-1-k, so the '+
     'deciding sheet parity equals the row parity (p-1 even), every p', d1);
}

// ---- (e) Omega-blind: the full law at p = 5, 17, 29 ----
{
  let all=true, pos=true;
  for(const p of [5,17,29]){
    const {K,cov,slots}=cover(p), n=2*K*(p-1);
    const good=cov.size===n &&
      [...cov.values()].reduce((x,y)=>x+y,0)===2*n &&
      [...cov].every(([k,v])=>v===(+k.split(',')[2]%2?1:3));
    if(!good) all=false;
    for(const [key,ss] of slots){
      const [s,,kk]=key.split(',').map(Number), a=s+1;
      if(kk%2===1){ const d=ss.filter(([,,t])=>t<=K).length;
        if(!(ss.length===1 && (a%2===1 ? d===1 : d===0))) pos=false; }
    }
  }
  ok('(e) Omega-blind: mu in {1,3} with the row-parity decider at p = 5, 17, '+
     '29 (kappa = 1, 4, 7): the law is the pair structure, not the instance', all);
  ok('(e) the shell-parity position law holds at p = 5, 17, 29 as well', pos);
}

// ---- (f) the all-shell parity lemma (round-02, closes the theorem) ----
// With M = k a^-1, A = floor(aM/p), alpha = A%2: aM = pA + k exactly, so
// kbar = abar*Mbar + alpha; the candidates match iff alpha = 0, abar, Mbar,
// 1+abar+Mbar respectively; the 8-case table forces mu = 3 iff k even and
// the odd sector's match at parameter a (direct) iff a odd -- every shell.
{
  let tab=true;
  for(const ab of [0,1]) for(const Mb of [0,1]) for(const al of [0,1]){
    const kb=(ab*Mb+al)%2;
    const mu=(al===0?1:0)+(al===ab?1:0)+(al===Mb?1:0)+(al===(1+ab+Mb)%2?1:0);
    if(mu!==(kb===0?3:1)) tab=false;
  }
  ok('(f) the eight-case parity table: mu = 3 iff kbar = 0, at every shell', tab);
  let agree=true;
  for(const p of [5,13,17,29]){
    const K=(p-1)/4, inv=x=>{for(let y=1;y<p;y++)if(x*y%p===1)return y;};
    const w=(m,t)=>fl(m*t/p);
    for(let a=1;a<=K;a++) for(let k=1;k<p;k++){
      const M=(k*inv(a))%p||p, A=fl(a*M/p), al=A%2;
      if(k%2 !== (a*M%2+al)%2) agree=false;                    // kbar identity
      const act=((w(M,a)%2===0)?1:0)+((w(p-M,a)%2===1)?1:0)+
                ((w(M,p-a)%2===1)?1:0)+((w(p-M,p-a)%2===0)?1:0);
      const mu=(al===0?1:0)+(al===(a%2)?1:0)+(al===(M%2)?1:0)+(al===(1+a%2+M%2)%2?1:0);
      if(mu!==act || act!==((k%2===0)?3:1)) agree=false;
      if(k%2===1){                                             // position law
        const c=[[M,a,0],[p-M,a,1],[M,p-a,1],[p-M,p-a,0]];
        const hits=c.filter(([m,t,r])=>w(m,t)%2===r);
        if(hits.length!==1 || ((a%2===1)!==(hits[0][1]<=K))) agree=false;
      }
    }
  }
  ok('(f) the lemma agrees with the constructed covering and yields the '+
     'position law, all shells, p = 5, 13, 17, 29', agree);
}

console.log(fails===0?'ALL O2 MULTIPLICITY CHECKS PASS':'FAILURES: '+fails);
process.exit(fails?1:0);
