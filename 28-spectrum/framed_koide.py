#!/usr/bin/env python3
# -*- coding: utf-8 -*-
"""
Koide over FRAMED RATIONALS (1-algebra), the most native FRC arena.
Not cyclotomic Q(omega,sqrt2) -- that is one continuum rung up -- but the finite field
F_p with a frame, where every residue is a framed rational r/s of bounded height, the
cube root omega lives in K=F_{p^2}, Frobenius sigma is the native conjugation, and the
'quarter-turn sqrt2 amplitude' is natively the framed RATIONAL N(b)/a^2 = 1/2 (a norm
condition), no irrational needed.  Q = 2/3 is then an exact identity in F_p.
"""
from math import isqrt

def ratrecon(x, p):
    """canonical framed rational r/s ≡ x (mod p), |r|,|s| <~ sqrt(p/2)."""
    x %= p; bound = isqrt(p//2)
    r0,r1 = p, x; s0,s1 = 0,1
    while r1 > bound:
        q = r0//r1
        r0,r1 = r1, r0-q*r1
        s0,s1 = s1, s0-q*s1
    r,s = r1,s1
    if s < 0: r,s = -r,-s
    return (r,s)
def fr(x,p):
    r,s = ratrecon(x,p); return f"{r}" if s==1 else f"{r}/{s}"

def run(p):
    assert p%12==5
    # non-residue n for K=F_{p^2}=F_p[t]/(t^2-n); Frobenius sigma: t->-t (native conjugation)
    n = next(m for m in range(2,p) if pow(m,(p-1)//2,p)==p-1)
    def mul(A,B):                       # (u,v) = u+v t
        (a,b),(c,d)=A,B
        return ((a*c+b*d*n)%p,(a*d+b*c)%p)
    def conj(A): return (A[0],(-A[1])%p)          # sigma = Frobenius
    def norm(A): return (A[0]*A[0]-n*A[1]*A[1])%p  # N(b)=b sigma(b) in F_p
    def order(A):
        o=1;X=A
        while X!=(1,0): X=mul(X,A);o+=1
        return o
    # cube root omega in K (order 3; exists since 3 | p+1)
    omega=None
    for u in range(p):
        for v in range(1,p):
            if order((u,v))==3: omega=(u,v); break
        if omega: break
    inv=lambda z: pow(z,p-2,p)
    # choose a in F_p, and b in K with N(b) = a^2 * (1/2)  == the quarter-turn condition
    a=1; target=(a*a*inv(2))%p
    b=None
    for u in range(p):
        for v in range(p):
            if norm((u,v))==target and (u,v)!=(0,0): b=(u,v); break
        if b: break
    # circulant amplitude eigenvalues  lambda_k = a + b omega^k + conj(b) omega^{2k}  in F_p
    A=(a,0)
    lam=[]
    for k in range(3):
        wk=(1,0)
        for _ in range(k): wk=mul(wk,omega)
        w2k=mul(wk,wk)
        val=( (A[0]+mul(b,wk)[0]+mul(conj(b),w2k)[0])%p ,
              (A[1]+mul(b,wk)[1]+mul(conj(b),w2k)[1])%p )
        lam.append(val)
    inF_p = all(L[1]==0 for L in lam)              # eigenvalues are framed rationals in F_p
    l=[L[0] for L in lam]
    Slam=sum(l)%p
    Slam2=sum((x*x)%p for x in l)%p
    Q=(Slam2*inv((Slam*Slam)%p))%p                 # Q = sum(lambda^2)/(sum lambda)^2
    Qrat=fr(Q,p); twothirds=(2*inv(3))%p
    print(f"  p={p}  (K=F_{{{p}^2}}, t^2={n}, Frobenius t->-t)")
    print(f"    omega (cube root, order 3) = {omega} = {fr(omega[0],p)} + {fr(omega[1],p)} t")
    print(f"    a = {fr(a,p)} ;  b = ({fr(b[0],p)}) + ({fr(b[1],p)}) t ;  "
          f"N(b)/a^2 = {fr(norm(b)*inv(a*a)%p,p)}  (= 1/2, the quarter-turn, a RATIONAL)")
    print(f"    sqrt-mass eigenvalues (framed rationals in F_p): "
          f"{', '.join(fr(x,p) for x in l)}   in F_p: {inF_p}")
    print(f"    Q = sum(lam^2)/(sum lam)^2 = {Q}  =  {Qrat}   (2/3 = {twothirds}): "
          f"{'EXACT 2/3' if Q==twothirds else 'NO'}")
    return Q==twothirds and inF_p

print("Koide over framed rationals (F_{p^2}/F_p, Frobenius conjugation), no cyclotomics:")
ok=all(run(p) for p in [17,53,89])
print(f"\n  ALL shells: Q = 2/3 exact over framed rationals  ->  {ok}")
print("  the 'sqrt2 amplitude' is the framed rational N(b)/a^2 = 1/2 ; sqrt2 is its")
print("  continuum reading.  omega is the finite cube root, not zeta_3 in C.")
