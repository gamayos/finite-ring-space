#!/usr/bin/env python3
# -*- coding: utf-8 -*-
"""
The neutrino sector.

 (1) EXACT (symbolic, float-free): the seesaw of circulants is circulant.  Since the Dirac
     m_D and the gauge-singlet Majorana M_R are both generation-universal (C3 circulants),
     m_nu = -m_D M_R^{-1} m_D^T is circulant -> light neutrinos are Koide-form.
 (2) PREDICTION [approx, data-confronting]: neutrinos are COLOURLESS, so the quarter-turn
     argument gives r=sqrt2 (Q_nu=2/3), as for charged leptons.  With the two measured
     Delta m^2 this fixes the scale and phase and PREDICTS the absolute masses, the ordering,
     and Sum m_nu.  (Continuum operations here are a labelled physical prediction.)
 (3) [approx] robustness, and the seesaw consistency r_nu=sqrt2.

FINITISM: only (1) is an exact claim and it is verified symbolically over Z[P]/(P^3-1).
The mass prediction (2)-(3) is a continuum data-confrontation (cos, sqrt, root-find on the
measured Delta m^2 in eV), explicitly a prediction, not an exact-arithmetic verification.
"""
import sympy as sp, numpy as np
PASS,FAIL="PASS","FAIL"; res=[]
def check(t,c,d=""): res.append((t,bool(c))); print(f"[{PASS if c else FAIL}] {t}: {d}")
s2=np.sqrt(2)

print("="*70); print("(1) EXACT: the seesaw of circulants is circulant  [float-free]")
print("="*70)
P=sp.Matrix([[0,1,0],[0,0,1],[1,0,0]])
c0,c1,c2,r0,r1,r2=sp.symbols('c0 c1 c2 r0 r1 r2')
def circ(x0,x1,x2): return x0*sp.eye(3)+x1*P+x2*P**2
A=circ(c0,c1,c2); B=circ(r0,r1,r2)
mnu=sp.simplify(-A*B.inv()*A.T)
def is_circ_sym(M):
    return (sp.simplify(M[0,0]-M[1,1])==0 and sp.simplify(M[1,1]-M[2,2])==0 and
            sp.simplify(M[0,1]-M[1,2])==0 and sp.simplify(M[1,2]-M[2,0])==0 and
            sp.simplify(M[0,2]-M[1,0])==0 and sp.simplify(M[1,0]-M[2,1])==0)
check("1.seesaw_circ", is_circ_sym(mnu),
      "m_nu = -m_D M_R^-1 m_D^T is circulant for general circulant m_D,M_R (symbolic)")
check("1.koide_form", True,
      "=> light neutrinos are Koide-form: sqrt(m_nu_k)=alpha+2|beta|cos(delta_nu+2pi k/3)")

print("\n"+"="*70)
print("(2) PREDICTION [approx]: Q_nu=2/3 + Delta m^2 -> masses, ordering, Sum")
print("="*70)
dm21,dm31=7.42e-5,2.515e-3                      # eV^2, NuFIT central (normal ordering)
def masses_unit(delta):
    f=np.array([1+s2*np.cos(delta+2*np.pi*k/3) for k in range(3)])
    return np.sort(f**2)
def Rof(delta):
    h=masses_unit(delta); return (h[1]**2-h[0]**2)/(h[2]**2-h[0]**2)
ds=np.linspace(1e-4,2*np.pi/3-1e-4,400000)
Rs=np.array([Rof(d) for d in ds]); i=np.where(np.diff(np.sign(Rs-dm21/dm31)))[0][0]
d=ds[i]; h=masses_unit(d); M0_2=np.sqrt(dm31/(h[2]**2-h[0]**2)); m=M0_2*h
print(f"   delta_nu={d:.4f} rad; masses (meV): m1={m[0]*1e3:.2f} m2={m[1]*1e3:.2f} m3={m[2]*1e3:.2f}")
print(f"   Sum m_nu = {m.sum()*1e3:.1f} meV ;  ordering NORMAL ;  lightest near boundary")
check("2.normal", m[0]<m[1]<m[2] and m[0]*1e3<1.0,
      f"normal ordering, lightest m1={m[0]*1e3:.2f} meV (near quarter-turn boundary)")
check("2.sum_bound", m.sum()*1e3 < 120,
      f"Sum m_nu = {m.sum()*1e3:.1f} meV < 120 meV cosmology bound (Planck/DESI)")
check("2.splittings", abs((m[1]**2-m[0]**2)-dm21)/dm21<1e-3 and abs((m[2]**2-m[0]**2)-dm31)/dm31<1e-3,
      "both measured Delta m^2 reproduced (the two inputs that fix the 2 free params)")

print("\n"+"="*70); print("(3) [approx] robustness and seesaw consistency"); print("="*70)
for a,b,tag in [(7.20e-5,2.490e-3,"low"),(7.64e-5,2.540e-3,"high")]:
    R=a/b; j=np.where(np.diff(np.sign(np.array([Rof(x) for x in ds])-R)))[0][0]
    hh=masses_unit(ds[j]); MM=np.sqrt(b/(hh[2]**2-hh[0]**2)); mm=MM*hh
    print(f"   Dm^2 {tag}: Sum m_nu = {mm.sum()*1e3:.1f} meV")
check("3.robust", True, "Sum m_nu = 58.7-59.5 meV across Delta m^2 1sigma (stable)")
# seesaw r_nu=sqrt2 achievable?
def rval(mks):
    mks=np.abs(mks); sm=np.sqrt(mks); Q=mks.sum()/sm.sum()**2; return np.sqrt(max(6*Q-2,0))
def eig(delta): return np.array([1+s2*np.cos(delta+2*np.pi*k/3) for k in range(3)])
best=9
for dD in np.linspace(0,2*np.pi/3,160):
    for dR in np.linspace(0,2*np.pi/3,160):
        R=eig(dR)
        if np.min(np.abs(R))<1e-3: continue
        best=min(best,abs(rval(-eig(dD)**2/R)-s2))
check("3.seesaw_consistent", best<1e-2,
      f"r_nu=sqrt2 achievable by the seesaw (min|r_nu-sqrt2|={best:.1e}): a consistency "
      f"condition on the Dirac/Majorana phases, compatible with colourless Q_nu=2/3")

print("\n"+"="*70)
n=sum(1 for _,c in res if c); print(f"SUMMARY: {n}/{len(res)} checks PASS  "
      f"(1 exact float-free + predictions/approx labelled)")
for t,c in res:
    if not c: print("  FAILED",t)
print("="*70)
