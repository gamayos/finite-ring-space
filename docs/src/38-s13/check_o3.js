"use strict";
// O3: the drawn winding-family layer, pinned.
// The page draws the ten sibling windings (m = 2..12, m != 5) ultra-faint
// behind the M0/M3 pair by the ONE meridian law baseMW (M0 = winding 1,
// M3 = winding 5), on-tick exact.  This audit pins the layer's arithmetic:
// the winding-1/5 identity with the drawn station tables, the containment
// of all 144 covering slots in the drawn observable sector, the covering
// multiset with the parity multiplicities, the axis passages 13j/m, and
// the ramification points 13/(2m) -- all framed-rational.
const fl=Math.floor;
let fails=0; const ok=(t,c)=>{console.log((c?'pass ':'FAIL ')+t); if(!c)fails++;};
const P=13, PARAMS=[1,2,3,10,11,12];
// the page's station law: tent fold of u = m*t with route flip on odd
// half-winds; shell from the parameter tent
const station=(m,ray,t)=>{
  const u=m*t, mW=fl(u/P), even=mW%2===0;
  const kk=even?u-P*mW:P*(mW+1)-u, ee=even?ray:-ray;
  const s=t<=3?t-1:12-t;
  return [s,ee,kk];
};

// ---- (a) the pair is two labels of the one law ----
ok('(a) winding 1 = M0: stations at rows 1,2,3 (direct) and 10,11,12 (echo), '+
   'no route flip (u = t never wraps)',
   PARAMS.every(t=>{const [s,ee,kk]=station(1,1,t); return kk===t && ee===1 &&
     s===(t<=3?t-1:12-t);}));
ok('(a) winding 5 = M3: t = 1,2,3 -> rows 5,10,11; t = 10,11,12 -> rows 2,3,8; '+
   'route flips on the odd half-winds',
   [1,2,3,10,11,12].map(t=>station(5,1,t)[2]).join()==='5,10,11,2,3,8' &&
   station(5,1,1)[1]===1 && station(5,1,2)[1]===1 &&
   station(5,1,3)[1]===-1 && station(5,1,10)[1]===-1 &&
   station(5,1,11)[1]===1 && station(5,1,12)[1]===1);

// ---- (b) the drawn sector contains the whole covering ----
ok('(b) every station parameter lies in the drawn observable segments '+
   '[0, 13/4] and [39/4, 13]: 4*3 <= 13 and 4*10 >= 39 -- the faint layer '+
   'shows all 144 slots', 4*3<=13 && 4*10>=39 &&
   PARAMS.every(t=>4*t<=13||4*t>=39));

// ---- (c) the drawn family IS the covering ----
{
  const cov=new Map();
  for(let m=1;m<=12;m++) for(const ray of [1,-1]) for(const t of PARAMS){
    const key=station(m,ray,t).join(','); cov.set(key,(cov.get(key)||0)+1);
  }
  ok('(c) the 24 drawn curves (12 windings x 2 rays) place their 144 stations '+
     'on 72/72 nodes with the parity multiplicities: 36 once (odd rows), 36 '+
     'thrice (even), 144 = 36 + 108 -- the covering parity law drawn',
     cov.size===72 && [...cov.values()].reduce((a,b)=>a+b,0)===144 &&
     [...cov].every(([k,v])=>v===(+k.split(',')[2]%2?1:3)));
}

// ---- (d) axis passages, framed-rational ----
// winding m crosses the clock axis where the folded row is 0 or 13:
// u = m*t = 13j, t = 13j/m.  Drawn passages = those inside the segments.
{
  const drawn=m=>{
    const out=[];
    for(let j=1;j<m;j++){ const num=13*j; // t = num/m
      if(4*num<=13*m || 4*num>=39*m) out.push([num,m]); }
    return out;
  };
  const d5=drawn(5);
  ok('(d) winding 5 has exactly two drawn axis passages, t = 13/5 and 52/5 '+
     '(the page: 2.6 and 10.4); winding 1 has none',
     d5.length===2 && d5[0][0]===13 && d5[1][0]===52 && drawn(1).length===0);
  ok('(d) a drawn axis passage exists iff m >= 4 (t = 13/m <= 13/4 iff '+
     '4 <= m): windings 2, 3 pass the axis only in the unobservable '+
     'mid-tower', (()=>{for(let m=2;m<=12;m++){
       const has=drawn(m).length>=1; if(has!==(m>=4))return false;}
     return true;})());
}

// ---- (e) ramification, framed-rational ----
// t_half = 13/(2m): inside the drawn first segment iff 13/(2m) <= 13/4
// iff m >= 2 -- every faint sibling shows its ramification point; M0's
// (m = 1: t = 13/2) is the origin bounce, outside the drawn sector.
ok('(e) ramification t = 13/(2m) is drawn for every sibling (2*2 >= 4) and '+
   'not for M0 (13/2 outside both segments)',
   (()=>{for(let m=2;m<=12;m++)if(!(4*13<=13*2*m))return false;
   return 4*13>13*2 && !(4*6.5<=13||4*6.5>=39);})());

console.log(fails===0?'ALL O3 FAMILY-LAYER CHECKS PASS':'FAILURES: '+fails);
process.exit(fails?1:0);
