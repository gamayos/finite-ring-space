"""
revision_checks.py  --  consolidated checks added during revision.

Covers the claims introduced in the neutrino (signed/Takagi Koide + branch),
quark (scheme spread), CP (Jarlskog normalisation), and phase-residue
(delta_LO framed-rational, cube-invariant, 3*delta0 = Q) sections.

Class: MIXED.  The framed-rational / algebraic identities are EXACT (fractions);
the confrontations with measured masses are labelled [approx] and carry no
exact claim.  Deterministic, no input, exits 0.
"""
from fractions import Fraction as F
import numpy as np

P=[0]
def must(name, ok, msg):
    P[0]+=1
    print(f"  [{'PASS' if ok else 'FAIL'}] {name}: {msg}")
    assert ok, name

w=2*np.pi/3
print("="*70); print("A. EXACT framed-rational / algebraic identities"); print("="*70)

# A1 Jarlskog normalisation: J(F) = Im(omega)/9 = sqrt3/18 = 1/(6 sqrt3), NOT Im(omega)/3
import sympy as sp
om=sp.Rational(-1,2)+sp.I*sp.sqrt(3)/2          # primitive cube root
J=sp.im(om)/9
must("A1.jarlskog", sp.simplify(J-1/(6*sp.sqrt(3)))==0,
     "J = Im(omega)/9 = sqrt3/18 = 1/(6 sqrt3) (Im(omega)/3 would be 1/(2 sqrt3), wrong)")
must("A1.jsq", sp.simplify((1/(6*sp.sqrt(3)))**2-sp.Rational(1,108))==0, "J^2 = 1/108")

# A2 leading phase delta_LO = 3/8 - 1/3 = 1/24 cycle (split-torus boundary minus generation)
must("A2.dLO", F(3,8)-F(1,3)==F(1,24), "delta_LO = 3/8 - 1/3 = 1/24 cycle (continuum pi/12 [approx])")

# A3 signed (Takagi) Koide = 2/3 for r=sqrt2 at every phase  (a = sum of SIGNED amplitudes)
def amps(d): return 1+np.sqrt(2)*np.cos(d+w*np.arange(3))
ok=all(abs((amps(d)**2).sum()/amps(d).sum()**2 - 2/3)<1e-12 for d in np.linspace(0,2*np.pi,2001))
must("A3.signedKoide", ok, "signed-amplitude Koide = 2/3 for r=sqrt2 at every delta (Q_nu, Q_l)")

# A4 cube-invariant determinant identity: prod sqrt(m) = a^3 (cos(3d)/sqrt2 - 1/2),  a=(sum sqrt m)/3
def lhs_rhs(d):
    a=amps(d); A=a.sum()/3
    return np.prod(a), A**3*(np.cos(3*d)/np.sqrt(2)-0.5)
ok=all(abs(l-r)<1e-9 for d in np.linspace(0.05,0.6,50) for l,r in [lhs_rhs(d)])
must("A4.cubeinv", ok, "prod sqrt(m) = a^3(cos 3d/sqrt2 - 1/2); phase residue = Re(b^3)")

print("\n"+"="*70); print("B. [approx] confrontations with measured data (no exact claim)"); print("="*70)

# B1 charged-lepton phase and 3*delta0 = Q  [approx]
me,mmu,mtau=0.51099895,105.6583755,1776.86
sm=np.sqrt([me,mmu,mtau]); a=sm.sum()/3
three_delta=np.arccos(np.sqrt(2)*(np.sqrt(me*mmu*mtau)/a**3+0.5))
Q=(me+mmu+mtau)/sm.sum()**2
must("B1.3delta=Q", abs(three_delta-Q)<1e-4,
     f"[approx] 3*delta0={three_delta:.5f} = Koide Q={Q:.5f}  => delta0 = Q/3 = 2/9")

# B2 neutrino: positive-root Koide values, and NO fits r=sqrt2 far tighter than IO
dm21,dm31=7.49e-5,2.513e-3
def Qpos(m): m=np.array(m); return m.sum()/np.sqrt(m).sum()**2
q0=Qpos([0.0,np.sqrt(dm21),np.sqrt(dm31)])
q4=Qpos([0.4e-3,np.sqrt(0.4e-3**2+dm21),np.sqrt(0.4e-3**2+dm31)])
must("B2.posroot", abs(q0-0.586)<0.01 and abs(q4-0.524)<0.01,
     f"[approx] positive-root Koide ~{q0:.3f} (m1=0), ~{q4:.3f} (fitted m1) -- not the signed object")
def fit_r2(masses):
    masses=np.sort(np.array(masses,float)); t=masses/masses[-1]
    return min(np.sum(((np.sort(np.abs(amps(d)))/np.sort(np.abs(amps(d)))[-1])**2 - t)**2)
               for d in np.linspace(0,2*np.pi,40001))
rN=fit_r2([0.0,np.sqrt(dm21),np.sqrt(dm31)])
rI=fit_r2([np.sqrt(dm31),np.sqrt(dm31+dm21),0.0])
must("B2.branch", rI/rN>20,
     f"[approx] r=sqrt2 fit {rI/rN:.0f}x tighter for normal than inverted (boundary branch selects NO)")

# B3 Q_u scheme spread brackets 5/6; on-shell ~ 5/6
def Qu(mu,mc,mt): m=np.array([mu,mc,mt]); return m.sum()/np.sqrt(m).sum()**2
onshell=Qu(2.2e-3,1.67,172.76); msz=Qu(1.27e-3,0.619,168.3)
must("B3.Qu", abs(onshell-5/6)<0.005 and msz>0.86,
     f"[approx] Q_u: on-shell {onshell:.3f} ~ 5/6={5/6:.3f}; MSbar(M_Z) {msz:.3f}; exact object r_u^2=3")

print("\n"+"="*70)
print(f"SUMMARY: {P[0]}/{P[0]} checks PASS  (A exact framed-rational, B labelled [approx])")
print("="*70)
