#!/usr/bin/env python3
# -*- coding: utf-8 -*-
"""
EXACT CORE -- the load-bearing flavour claims verified with ZERO continuum operations.
No float, no log, no numerical trig, no RNG, no tolerances.  Arena ladder (most native first):
  * FRAMED RATIONALS (1-algebra) : the Koide identity over F_{p^2}/F_p with Frobenius the
                        native conjugation; omega the finite cube root, the 'sqrt2 amplitude'
                        the framed RATIONAL N(b)/a^2=1/2, Q=2/3 exact in F_p (section E); and the
                        amplitude diagonal r^2=N(1-zeta_n)=2,3 as INTEGERS in F_p (section F).
  * cyclotomic Q(omega, sqrt2)   : one continuum rung up -- omega a complex cube root, sqrt2
                        =zeta_8+zeta_8^{-1} irrational (sections A, D).  A labelled reading.
  * rational multiples of pi     : the pi/12 boundary, and 1+sqrt2 cos(3pi/4)=0 (section B).
  * INTEGER group ring Z[Z/3 x Z/p] : Gauss-sum reality and pi/3-quantisation (section C).
Each continuum quantity used elsewhere (logs for lambda-powers, arccos for delta extraction,
RNG for robustness, float linalg for the mixing demo) is a labelled data-comparison or
sensitivity check, NOT a verification of an exact claim; see the finitism-audit note.
"""
import sympy as sp

ok=[]
def must(tag,cond,detail=""):
    ok.append((tag,bool(cond))); print(f"[{'EXACT' if cond else 'FAIL'}] {tag}: {detail}")

print("="*70); print("A. Koide / circulant in the cyclotomic field Q(omega, sqrt2)")
print("="*70)
# omega: primitive cube root of unity as an EXACT algebraic number (no pi, no float)
w  = sp.Rational(-1,2) + sp.sqrt(3)/2*sp.I
s2 = sp.sqrt(2)                                   # = zeta_8 + zeta_8^{-1}, cyclotomic
must("A.omega", sp.simplify(w**3-1)==0 and sp.simplify(1+w+w**2)==0,
     "omega^3=1 and 1+omega+omega^2=0 (exact)")
a, bx, by = sp.symbols('a b_x b_y', real=True)
b  = bx + sp.I*by; bc = bx - sp.I*by              # b and its conjugate
lam = [sp.expand(a + b*w**k + bc*w**(2*k)) for k in range(3)]   # circulant eigenvalues
S1 = sp.simplify(sum(lam))
S2 = sp.simplify(sum(l**2 for l in lam))
must("A.sum1", sp.simplify(S1-3*a)==0, f"sum_k lambda_k = {S1} = 3a")
must("A.sum2", sp.simplify(S2-(3*a**2+6*(bx**2+by**2)))==0,
     f"sum_k lambda_k^2 = 3a^2 + 6|b|^2  (exact; the omega-cross terms cancel)")
# Koide ratio Q = sum lambda^2 / (sum lambda)^2 = 1/3 + (2/3) rho^2,  rho^2=|b|^2/a^2
rho2 = sp.symbols('rho2', positive=True)          # |b|^2/a^2
Q = sp.Rational(1,3) + sp.Rational(2,3)*rho2
must("A.Qform", sp.simplify(Q-(3*a**2+6*a**2*rho2)/(9*a**2))==0,
     "Q = 1/3 + (2/3) rho^2  (exact)")
# r = 2|b|/a ; r = sqrt2  <=>  rho^2 = 1/2  <=>  Q = 2/3
must("A.koide", sp.simplify(Q.subs(rho2, sp.Rational(1,2))-sp.Rational(2,3))==0,
     "r = sqrt2  (rho=1/sqrt2, the quarter-turn diagonal)  =>  Q = 2/3 exactly")
# circulant eigen-identity & Hermiticity, exact symbolic matrix over Z[omega]
P = sp.Matrix([[0,1,0],[0,0,1],[1,0,0]])
M = a*sp.eye(3) + b*P + bc*P.T                      # P.T = P^2 = P^dagger
must("A.herm", sp.simplify(M - M.conjugate().T)==sp.zeros(3),
     "sqrt(M)=a*1+b*P+conj(b)*P^2 is Hermitian (P^2=P^dagger)")
F = sp.Matrix(3,3, lambda j,k: w**(j*k))            # Fourier (Vandermonde in omega)
D = sp.simplify(F.inv()*M*F)
diag_ok = all(sp.simplify(D[i,j])==0 for i in range(3) for j in range(3) if i!=j)
eig_ok  = all(sp.simplify(D[k,k]-(a+b*w**k+bc*w**(2*k)))==0 for k in range(3))
must("A.eig", diag_ok and eig_ok,
     "F^{-1} M F diagonal with entries a+b w^k+conj(b) w^{2k}  (exact eigenvalues)")

print("\n"+"="*70); print("B. The pi/12 boundary (exact rational-pi + algebraic)")
print("="*70)
must("B.pi12", sp.simplify(sp.Rational(3,4)*sp.pi - sp.Rational(2,3)*sp.pi - sp.pi/12)==0,
     "delta_LO = 3pi/4 - 2pi/3 = pi/12 (exact)")
# at the boundary the lightest eigenvalue vanishes EXACTLY: 1 + sqrt2*cos(3pi/4)=0
must("B.zero", sp.simplify(1 + s2*sp.cos(sp.Rational(3,4)*sp.pi))==0,
     "1 + sqrt2*cos(3pi/4) = 1 + sqrt2*(-1/sqrt2) = 0 (electron massless at boundary)")

print("\n"+"="*70); print("C. Gauss sums: reality & pi/3-quantisation as INTEGER identities")
print("="*70)
def isprime(n): return n>1 and all(n%k for k in range(2,int(n**0.5)+1))
def nonresidue(p): return next(n for n in range(2,p) if pow(n,(p-1)//2,p)==p-1)

def grp_overlap(p, drive):
    """Return the cubic overlap as an exact element of Z[Z/3 x Z/p]:
       C[r][s] = # { k : chi3(g^k)=omega^r  and  additive exponent = s }.
       No complex numbers -- only integer counts of roots of unity."""
    nqr=nonresidue(p)
    def mul(x,y):
        (A,B),(Cc,Dd)=x,y; return ((A*Cc+nqr*B*Dd)%p,(A*Dd+B*Cc)%p)
    U=[(A,B) for A in range(p) for B in range(p) if (A*A-nqr*B*B-1)%p==0]
    assert len(U)==p+1
    def order(x):
        o=1;y=x
        while y!=(1,0): y=mul(y,x);o+=1
        return o
    g=next(x for x in U if x!=(1,0) and order(x)==p+1)
    C=[[0]*p for _ in range(3)]
    cur=(1,0); w0=(1,1) if drive else (1,0)
    for k in range(p+1):
        A,B=mul(w0,cur); s=(2*A)%p                 # additive exponent Tr(w0 u)=2 Re(w0 u)
        C[k%3][s]+=1
        cur=mul(cur,g)
    return C

def conj(C,p):                                     # zeta_3 -> zeta_3^-1, zeta_p -> zeta_p^-1
    return [[C[(-r)%3][(-s)%p] for s in range(p)] for r in range(3)]
def equal(C,D): return C==D
def gmul(C,D,p):                                   # group-ring product over Z/3 x Z/p
    E=[[0]*p for _ in range(3)]
    for r1 in range(3):
        for s1 in range(p):
            c=C[r1][s1]
            if not c: continue
            for r2 in range(3):
                for s2 in range(p):
                    d=D[r2][s2]
                    if d: E[(r1+r2)%3][(s1+s2)%p]+=c*d
    return E

for p in [17,29,41,53]:
    assert isprime(p) and p%12==5
    Csym=grp_overlap(p,False)
    must(f"C.real_p{p}", equal(Csym,conj(Csym,p)),
         f"p={p}: symmetric cubic overlap b = conj(b) EXACTLY (integer-real); no phase")
for p in [17,29,41,53]:
    Cdrv=grp_overlap(p,True)
    b3=gmul(gmul(Cdrv,Cdrv,p),Cdrv,p)              # b^3
    must(f"C.cube_p{p}", equal(b3,conj(b3,p)),
         f"p={p}: drive-twisted b^3 = conj(b^3) EXACTLY  =>  arg(b) in (pi/3)Z")

print("\n"+"="*70); print("D. Leptonic CP: the magic matrix is maximal (cyclotomic Z[omega])")
print("="*70)
# the C3 eigenvector (DFT) matrix F = (1/sqrt3)[[1,1,1],[1,w,w^2],[1,w^2,w]]
Fm = sp.Matrix(3,3, lambda j,k: w**(j*k)) / sp.sqrt(3)
mod2 = [sp.simplify(sp.Abs(Fm[j,k])**2) for j in range(3) for k in range(3)]
must("D.trimaximal", all(sp.simplify(m-sp.Rational(1,3))==0 for m in mod2),
     "|F_jk|^2 = 1/3 for all 9 entries (trimaximal), exact")
# Jarlskog J = Im(F00 F11 conj(F01) conj(F10)) = Im(omega)/9 = 1/(6 sqrt3); compute exactly
J = sp.im(sp.simplify(Fm[0,0]*Fm[1,1]*sp.conjugate(Fm[0,1])*sp.conjugate(Fm[1,0])))
Jmax = 1/(6*sp.sqrt(3))
must("D.maxCP", sp.simplify(sp.Abs(J)-Jmax)==0,
     f"J(F) = {sp.simplify(J)} = +-1/(6 sqrt3): MAXIMAL CP (the cube-root phase Im(omega)=sqrt3/2)")

print("\n"+"="*70); print("E. Koide over FRAMED RATIONALS (1-algebra) -- the most native arena")
print("="*70)
# F_{p^2}/F_p, Frobenius the native conjugation; omega the finite cube root; the quarter-turn
# 'sqrt2' is the framed RATIONAL N(b)/a^2 = 1/2 (a norm condition).  Q=2/3 exact in F_p.
from math import isqrt
def _ratrecon(x,p):                       # canonical framed rational r/s = x (mod p)
    x%=p; B=isqrt(p//2); r0,r1,s0,s1=p,x,0,1
    while r1>B: q=r0//r1; r0,r1=r1,r0-q*r1; s0,s1=s1,s0-q*s1
    return (-r1,-s1) if s1<0 else (r1,s1)
def _framed_koide(p):
    n=next(m for m in range(2,p) if pow(m,(p-1)//2,p)==p-1)   # non-residue: t^2=n
    mul=lambda A,B:((A[0]*B[0]+A[1]*B[1]*n)%p,(A[0]*B[1]+A[1]*B[0])%p)
    conj=lambda A:(A[0],(-A[1])%p); norm=lambda A:(A[0]*A[0]-n*A[1]*A[1])%p
    inv=lambda z:pow(z,p-2,p)
    def order(A):
        o=1;X=A
        while X!=(1,0): X=mul(X,A); o+=1
        return o
    omega=next((u,v) for u in range(p) for v in range(1,p) if order((u,v))==3)
    a=1; tgt=(a*a*inv(2))%p                                   # N(b)=a^2/2 : the quarter-turn
    b=next((u,v) for u in range(p) for v in range(p) if (u,v)!=(0,0) and norm((u,v))==tgt)
    lam=[]
    for k in range(3):
        wk=(1,0)
        for _ in range(k): wk=mul(wk,omega)
        t=( (a if k==0 else 0)+0, 0 )
        L=((a+mul(b,wk)[0]+mul(conj(b),mul(wk,wk))[0])%p,
           (mul(b,wk)[1]+mul(conj(b),mul(wk,wk))[1])%p)
        lam.append(L)
    inFp=all(L[1]==0 for L in lam); l=[L[0] for L in lam]
    Q=(sum((x*x)%p for x in l)*inv((sum(l)%p)**2))%p
    amp=(norm(b)*inv(a*a))%p
    return Q==(2*inv(3))%p and inFp and amp==inv(2)%p, l, omega
for p in [17,53,89]:
    good,l,om=_framed_koide(p)
    must(f"E.framed_p{p}",good,
         f"p={p}: Q=2/3 exact in F_p; sqrt-mass eigenvalues framed rationals "
         f"{[_ratrecon(x,p) for x in l]}; omega={_ratrecon(om[0],p)}+{_ratrecon(om[1],p)}t; "
         f"quarter-turn = N(b)/a^2 = 1/2 (rational, not sqrt2)")

print("\n"+"="*70)
print("F. The amplitude diagonal over FRAMED RATIONALS: r^2 = N(1-zeta_n) = 2, 3 (integers in F_p)")
print("="*70)
# r^2 = N(1-zeta_n), the finite-field NORM of (1 - finite n-th root of unity): quarter-turn
# (i, i^2=-1) -> 2 (Q=2/3, four-fold, colourless); cube root (omega, omega^2+omega+1=0) -> 3
# (Q=5/6, three-fold, colour).  N(b)/a^2 = 1/2, 3/4 are framed rationals.  The 'sqrt2, sqrt3,
# 2 sin(pi/n)' are CONTINUUM readings of the integers 2, 3 -- one rung up.  No complex, no trig.
for p in [17,53,89]:
    i_=next(x for x in range(1,p) if (x*x+1)%p==0)             # quarter-turn i in F_p (i^2=-1)
    N1mi=((1-i_)*(1+i_))%p                                     # (1-i)(1+i)=1-i^2 = 2
    nq=next(m for m in range(2,p) if pow(m,(p-1)//2,p)==p-1)   # F_{p^2}=F_p[t]/(t^2-nq)
    mul=lambda A,B:((A[0]*B[0]+A[1]*B[1]*nq)%p,(A[0]*B[1]+A[1]*B[0])%p)
    def order(A):
        o=1;X=A
        while X!=(1,0):X=mul(X,A);o+=1
        return o
    om=next((u,v) for u in range(p) for v in range(1,p) if order((u,v))==3)   # cube root omega
    a1=((1-om[0])%p,(-om[1])%p); a2=((1-om[0])%p,(om[1])%p)    # (1-omega) and (1-conj omega)
    N1mw=mul(a1,a2)                                            # N(1-omega) = (3, 0) in F_p
    must(f"F.diag_p{p}", N1mi==2%p and N1mw==(3%p,0),
         f"p={p}: N(1-i)={N1mi} (=2: four-fold, r^2=2 -> Q=2/3); "
         f"N(1-omega)={N1mw[0]} (=3: three-fold/colour, r^2=3 -> Q=5/6) -- integers in F_p")

print("\n"+"="*70)
nfail=sum(1 for _,c in ok if not c)
print(f"EXACT CORE: {sum(1 for _,c in ok if c)}/{len(ok)} float-free verifications hold"
      + ("" if nfail==0 else f"  ({nfail} FAILED)"))
print("="*70)
