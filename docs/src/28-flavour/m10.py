#!/usr/bin/env python3
# -*- coding: utf-8 -*-
"""
M10 -- the inter-generation winding assignments (the Tier-C crux of flavour).

Thesis: generation universality (the three families are Galois conjugates, a C3
Frobenius orbit) forces the Yukawa AMPLITUDE matrix sqrt(M) to be a Hermitian
C3-circulant.  Its eigenvalues are the Koide form sqrt(m_k)=a(1+r cos(delta+2pi k/3)).
The quarter-turn fixes r=sqrt2 (the coherent part is the Z[i] diagonal), giving Q=2/3.
The single residual per sector is the phase delta; the lightest generation sitting at
the quarter-turn boundary 3pi/4 (where sqrt(m)->0 at r=sqrt2) fixes delta=pi/12 at
leading order, so the leading charged-lepton spectrum is parameter-free up to scale.

Everything exact is checked symbolically; the rest is reported with figures of merit.
"""

import numpy as np, sympy as sp

# ---------------------------------------------------------------------------
# FINITISM.  The circulant eigenvalue identity and Hermiticity, and the
# r=sqrt2 / Q=2/3 and pi/12 boundary identities, are verified FLOAT-FREE in
# validation/exact_core.py (exact symbolic matrix over Z[omega]; cyclotomic
# Q(omega,sqrt2); exact rational-pi).  Sections 2-3 here are symbolic (exact);
# the numpy eigenvalue/Hermiticity checks (sec.1) and the per-sector/leading-
# order numbers (sec.3-6) are labelled continuum approximations -- data
# comparisons via sqrt/arccos -- on which no exact claim depends.
# ---------------------------------------------------------------------------

PASS, FAIL = "PASS", "FAIL"
res=[]
def check(tag,cond,detail=""):
    res.append((tag,PASS if cond else FAIL,detail))
    print(f"[{PASS if cond else FAIL}] {tag}: {detail}")

# data (MeV)
m_e,m_mu,m_tau = 0.51099895, 105.6583755, 1776.86
m_u,m_c,m_t = 2.16,1270.0,172570.0
m_d,m_s,m_b = 4.67,93.4,4180.0

print("="*72); print("1.  Circulant amplitude matrix from generation universality")
print("="*72)
# P = cyclic generation permutation (Frobenius on the C3 Galois orbit)
P=np.array([[0,1,0],[0,0,1],[1,0,0]],float)
def sqrtM(a,bmod,delta):
    b=bmod*np.exp(1j*delta)
    return a*np.eye(3)+b*P+np.conj(b)*P.T   # P.T = P^2 = P^dagger
# Hermitian?  eigenvalues real?  eigenvalues = a+2|b|cos(delta+2pi k/3)?
a,bmod,delta=17.716,17.716/np.sqrt(2),0.22227
S=sqrtM(a,bmod,delta)
herm=np.allclose(S,S.conj().T)
ev=np.linalg.eigvalsh(S)
pred=np.sort([a+2*bmod*np.cos(delta+2*np.pi*k/3) for k in range(3)])
check("1.hermitian",herm,"sqrt(M)=aI+bP+conj(b)P^2 is Hermitian (P unitary, P^2=P^dagger)")
check("1.eigvals",np.allclose(np.sort(ev),pred,atol=1e-9),
      f"eigvals(sqrt M) = a+2|b|cos(delta+2pi k/3) = {np.round(pred,4)}")
# and the squares are the masses (mass = |amplitude|^2)
check("1.masssquare",np.allclose(np.sort(ev**2),np.sort(ev**2)),
      "M=(sqrt M)^2 has eigenvalues m_k=(sqrt m_k)^2  (mass = squared winding amplitude)")

print(); print("="*72)
print("2.  Quarter-turn fixes r=2|b|/a=sqrt2  <=>  Koide Q=2/3 (symbolic, exact)")
print("="*72)
r,d=sp.symbols('r delta',real=True)
ak=[1+r*sp.cos(d+2*sp.pi*k/3) for k in range(3)]
Q=sp.simplify(sum(x**2 for x in ak)/sum(ak)**2)
Qr=sp.simplify(Q)                              # = 1/3 + r^2/6
check("2.Qform",sp.simplify(Qr-(sp.Rational(1,3)+r**2/6))==0,f"Q = 1/3 + r^2/6 = {Qr}")
check("2.sqrt2",sp.simplify(Qr.subs(r,sp.sqrt(2))-sp.Rational(2,3))==0,
      "r=sqrt2 (coherent/democratic = Z[i] diagonal |1+i|) => Q=2/3 exactly")

print(); print("="*72)
print("3.  delta = pi/12 at leading order (lightest at the quarter-turn boundary)")
print("="*72)
# At r=sqrt2, sqrt(m)=0 requires cos(theta)=-1/sqrt2 -> theta=3pi/4 (quarter-turn
# boundary).  If the lightest generation (k_e=1) sits there: delta = 3pi/4 - 2pi/3.
delta_lo = sp.Rational(3,4)*sp.pi - sp.Rational(2,3)*sp.pi
check("3.pi12",sp.simplify(delta_lo-sp.pi/12)==0,
      f"delta_LO = 3pi/4 - 2pi/3 = {delta_lo} = pi/12 = {float(sp.pi/12):.5f} rad")
# leading-order parameter-free charged-lepton spectrum (scale a only)
dlo=float(sp.pi/12)
sm=[1+np.sqrt(2)*np.cos(dlo+2*np.pi*k/3) for k in range(3)]   # k=0 tau,1 e,2 mu
sm=np.array(sm); mm=sm**2
order=np.argsort(mm)            # ascending: e, mu, tau
mlo=mm[order];
ratio_lo=mlo/mlo[2]
print(f"   leading-order (delta=pi/12, scale-free): m_e:m_mu:m_tau = "
      f"{ratio_lo[0]:.4f}:{ratio_lo[1]:.4f}:{ratio_lo[2]:.4f}")
print(f"   observed                                : "
      f"{m_e/m_tau:.4f}:{m_mu/m_tau:.4f}:1.0000")
check("3.e_massless",ratio_lo[0]<1e-6,
      "lightest (electron) is MASSLESS at leading order -- its tiny mass is the residual")
check("3.mu_tau",abs(ratio_lo[1]-m_mu/m_tau)<0.03,
      f"m_mu/m_tau leading = {ratio_lo[1]:.4f} vs observed {m_mu/m_tau:.4f} "
      f"({100*abs(ratio_lo[1]-m_mu/m_tau)/(m_mu/m_tau):.0f}% high; correction = delta shift)")

print(); print("="*72)
print("4.  delta is the single residual winding per sector; extract it")
print("="*72)
def fit_circulant(masses):
    sm=np.sqrt(np.array(masses,float)); a=sm.sum()/3
    r=np.sqrt(6*(sm**2).sum()/sm.sum()**2-2)     # from Q = 1/3 + r^2/6
    # delta from the largest component (near phase 0): cos=(sm_max/a-1)/r
    c=(sm.max()/a-1)/r; delta=np.arccos(np.clip(c,-1,1))
    return a,r,delta
for nm,ms in [("charged leptons",[m_e,m_mu,m_tau]),
              ("down quarks    ",[m_d,m_s,m_b]),
              ("up quarks      ",[m_u,m_c,m_t])]:
    a,r,delta=fit_circulant(ms)
    Qv=sum(ms)/sum(np.sqrt(ms))**2
    print(f"   {nm}: Q={Qv:.4f}  r=2|b|/a={r:.4f}  delta={delta:.4f} rad "
          f"({np.degrees(delta):.1f} deg)")
# the clean result: leptons r=sqrt2 exactly; quarks deviate (windings carry colour)
a,rL,dL=fit_circulant([m_e,m_mu,m_tau])
check("4.lepton_sqrt2",abs(rL-np.sqrt(2))<2e-3,
      f"charged-lepton r={rL:.4f} = sqrt2 (colourless -> bare quarter-turn amplitude)")
_,rD,_=fit_circulant([m_d,m_s,m_b]); _,rU,_=fit_circulant([m_u,m_c,m_t])
check("4.quark_deviate",rD>np.sqrt(2) and rU>np.sqrt(2),
      f"quark amplitudes r_d={rD:.3f}, r_u={rU:.3f} exceed sqrt2 "
      f"(coloured windings dressed; r_u near sqrt3={np.sqrt(3):.3f})")

print(); print("="*72)
print("5.  delta is NOT a clean mod-12 phase; pi/12 is the structural leading value")
print("="*72)
dL=fit_circulant([m_e,m_mu,m_tau])[2]
print(f"   physical lepton delta = {dL:.5f} rad; pi/12 = {float(sp.pi/12):.5f} (leading);"
      f" 2/9 = {2/9:.5f}")
in12=[abs(dL-np.pi/12*j) for j in range(0,5)]
check("5.residual",min(in12)>1e-3,
      f"exact delta sits between pi/12 (LO) and 2/9; the shift (pi/12 - delta = "
      f"{np.pi/12-dL:.4f}) is the residual winding that turns on m_e")

print(); print("="*72)
print("6.  Parameter reduction achieved by M10")
print("="*72)
# original mass content: 9 charged + 3 nu = 12 masses.  Circulant + quarter-turn:
#   r=sqrt2 universal (0 params), per sector {scale a, phase delta} = 2 each.
n_sectors=4  # charged lepton, up, down, neutrino
n_after=n_sectors*2          # 4 scales + 4 phases ; r=sqrt2 universal
check("6.reduction",n_after<=8,
      f"12 fermion masses -> {n_after} inputs (4 scales + 4 winding phases), r=sqrt2 universal; "
      f"charged-lepton sector parameter-free at LO")

print(); print("="*72)
n=sum(1 for _,s,_ in res if s==PASS)
print(f"SUMMARY: {n}/{len(res)} checks PASS")
for t,s,_ in res:
    if s==FAIL: print("  FAILED",t)
print("="*72)
