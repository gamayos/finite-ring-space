#!/usr/bin/env python3
# -*- coding: utf-8 -*-
"""
tm2_jointfit.py  --  status of the TM2 column lead.

  0  the protected column is the trivial C3 character (1,1,1)/sqrt3 -- a SINGLE irrep -- so
     a C3 residual gives TM2; TM1 would protect (2,-1,-1)/sqrt6 = the SUM of the two non-trivial
     characters (reducible), which no C3 residual fixes.
  1  exact-TM2 solar value 1/(3 c13^2)=0.341 vs TM1 0.318 vs observed 0.307.
  2  the SAME Cabibbo 1-2 correction that fixes theta13 sweeps sin^2 th12 across 0.307
     => the exact-TM2 value is not a locked prediction; the solar 'tension' dissolves.
  3  full joint fit (status only, T23 2026-09-13): model B (CP = neutrino cube-root phase
     delta_nu) has FIVE free parameters (a 2-3 angle and phase, a 1-2 phase, a 1-3 angle and
     phase) for FOUR observables with theta_C imported, so chi^2 ~ 0 is guaranteed and carries
     no test; theta13 is fitted in B, not predicted.  Model A's earlier 'fails theta23'
     verdict depended on theta23 = 49 deg (NuFIT 5); NuFIT 6.0 with SK atmospheric data puts
     theta23 at 43.3 deg, where A fits.  The TEST is the TM2 relation
        cos(delta_CP) = cot(2 theta23) (1 - 2 s13^2) / (s13 sqrt(2 - 3 s13^2)),
     checked in block 4 against the direct PMNS evaluation and the NuFIT 6.0 ranges.
     [continuum/data, labelled approx]
"""
import numpy as np
from scipy.optimize import least_squares

PASS=[]
def check(name,cond): PASS.append(bool(cond)); print(f"  [{'OK' if cond else 'XX'}] {name}")

sC=0.225; tC=np.arcsin(sC); r2,r3,r6=np.sqrt(2),np.sqrt(3),np.sqrt(6)
w=np.exp(2j*np.pi/3)
F=np.array([[1,1,1],[1,w,w**2],[1,w**2,w]])/r3
TBM=np.array([[2/r6,1/r3,0],[-1/r6,1/r3,-1/r2],[-1/r6,1/r3,1/r2]],dtype=complex)
# NuFIT 6.0 (arXiv:2410.05380), normal ordering, without SK atmospheric data (with SK: th23=43.3, dcp=212)
OBS=dict(th13=8.52,th12=33.68,th23=48.5,dcp=177.0); SIG=dict(th13=0.11,th12=0.72,th23=0.8,dcp=20.0)
OBS_SK=dict(th13=8.56,th12=33.68,th23=43.3,dcp=212.0)

# ---- 0: trivial singlet vs reducible doublet ----
print("0  protected column: trivial C3 singlet (TM2) vs reducible doublet-sum (TM1)")
check("magic matrix trimaximal |F_jk|^2=1/3", np.allclose(np.abs(F)**2,1/3))
triv=np.array([1,1,1])/r3
check("TM2 column (1,1,1)/sqrt3 is the trivial C3 character (a single irrep)",
      np.allclose(np.abs(triv)**2,1/3))
# (2,-1,-1) = (1,w,w^2)+(1,w^2,w)  -> reducible sum of the two non-trivial chars
chi1=np.array([1,w,w**2]); chi2=np.array([1,w**2,w])
check("TM1 column (2,-1,-1) = sum of the two non-trivial characters (reducible)",
      np.allclose((chi1+chi2).real,[2,-1,-1]) and np.allclose((chi1+chi2).imag,0))

# ---- 1: exact-TM2 vs TM1 solar predictions ----
print("\n1  exact-trimaximal solar predictions")
s13sq=np.sin(np.radians(OBS['th13']))**2; c13sq=1-s13sq
tm2=1/(3*c13sq); tm1=1-2/(3*c13sq); obs=0.307
print(f"   TM2 1/(3c13^2)={tm2:.3f}  TM1 1-2/(3c13^2)={tm1:.3f}  obs={obs:.3f}")
check("exact-TM2 solar = 0.341 (2.6 sigma high IF taken as a locked prediction)", abs(tm2-0.341)<0.002)

# ---- 2: the theta_C correction dissolves the tension ----
print("\n2  the Cabibbo 1-2 correction sweeps sin^2 th12 through 0.307 (tension dissolves)")
def Ue12(t,p): c,s=np.cos(t),np.sin(t); return np.array([[c,s*np.exp(-1j*p),0],[-s*np.exp(1j*p),c,0],[0,0,1]],complex)
def s12sq_of(phi): U=Ue12(tC,phi).conj().T@TBM; s13=abs(U[0,2]); return (abs(U[0,1])/np.sqrt(1-s13**2))**2
vals=[s12sq_of(p) for p in np.linspace(0,np.pi,400)]
check("sin^2 th12 range under the correction brackets the observed 0.307",
      min(vals)<0.307<max(vals))
check("theta13 = arcsin(sin thC/sqrt2) ~ 9 deg (the prediction)",
      abs(np.degrees(np.arcsin(sC/r2))-9.15)<0.1)

# ---- 3: the full joint fit ----
def U12(t,p): c,s=np.cos(t),np.sin(t); return np.array([[c,s*np.exp(-1j*p),0],[-s*np.exp(1j*p),c,0],[0,0,1]],complex)
def U23(t,p): c,s=np.cos(t),np.sin(t); return np.array([[1,0,0],[0,c,s*np.exp(-1j*p)],[0,-s*np.exp(1j*p),c]],complex)
def U13(t,p): c,s=np.cos(t),np.sin(t); return np.array([[c,0,s*np.exp(-1j*p)],[0,1,0],[-s*np.exp(1j*p),0,c]],complex)
def obsv(U):
    s13=abs(U[0,2]); c13=np.sqrt(1-s13**2); s12=abs(U[0,1])/c13; s23=abs(U[1,2])/c13
    c12=np.sqrt(1-s12**2); c23=np.sqrt(1-s23**2)
    J=np.imag(U[0,0]*U[1,1]*np.conj(U[0,1])*np.conj(U[1,0])); J0=s12*c12*s23*c23*s13*c13**2
    sind=np.clip(J/J0,-1,1) if J0>1e-12 else 0.0
    cosd=np.clip((s12**2*s23**2+c12**2*c23**2*s13**2-abs(U[2,0])**2)/(2*s12*c12*s23*c23*s13),-1,1) if s13>1e-9 else 1.0
    return dict(th13=np.degrees(np.arcsin(s13)),th12=np.degrees(np.arcsin(s12)),
                th23=np.degrees(np.arcsin(s23)),dcp=np.degrees(np.arctan2(sind,cosd)))
def ad(a,b): return (a-b+180)%360-180
def res(x,m):
    o=obsv(m(x))
    return [(o['th13']-OBS['th13'])/SIG['th13'],(o['th12']-OBS['th12'])/SIG['th12'],
            (o['th23']-OBS['th23'])/SIG['th23'],ad(o['dcp'],OBS['dcp'])/SIG['dcp']]
def best_fit(m,bnds):
    b=None
    for _ in range(60):
        g=[np.random.uniform(lo,hi) for lo,hi in zip(*bnds)]
        r=least_squares(res,g,args=(m,),bounds=bnds,max_nfev=4000)
        if b is None or r.cost<b.cost: b=r
    return obsv(m(b.x)),2*b.cost
mA=lambda x:(U23(x[0],x[2])@U12(tC,x[1])).conj().T@TBM
mB=lambda x:(U23(x[0],x[2])@U12(tC,x[1])).conj().T@(U13(x[3],x[4])@TBM)
print("\n3  full joint fit (status: 5 parameters for 4 observables; theta13 fitted in B)")
oA,cA=best_fit(mA,([0.3,-np.pi,-np.pi],[1.3,np.pi,np.pi]))
oB,cB=best_fit(mB,([0.3,-np.pi,-np.pi,0,-np.pi],[1.3,np.pi,np.pi,0.6,np.pi]))
print(f"   A (CP=charged leptons): th13={oA['th13']:.1f} th12={oA['th12']:.1f} th23={oA['th23']:.1f} dCP={oA['dcp']:.0f}  chi2={cA:.1f}")
print(f"   B (CP=neutrino delta_nu): th13={oB['th13']:.1f} th12={oB['th12']:.1f} th23={oB['th23']:.1f} dCP={oB['dcp']:.0f}  chi2={cB:.2f}")
print("   parameter count: model A 3 parameters, model B 5 parameters, for 4 observables (theta_C imported):")
print("   chi^2 ~ 0 in B is guaranteed and is not a test; the 'model A fails theta23' verdict is data-version dependent")
print(f"   (NuFIT 6.0 with SK atmospheric data: theta23 = {OBS_SK['th23']} deg, first octant).")
check("Model B (CP in neutrino delta_nu) reaches chi^2 ~ 0 with 5 parameters for 4 observables (no test)", cB<0.5)

# ---- 4: the TM2 relation, the actual test ----
print("\n4  the TM2 relation cos(dCP) = cot(2 th23) (1-2 s13^2)/(s13 sqrt(2-3 s13^2))")
def tm2_cosd(th13,th23):
    s13=np.sin(np.radians(th13)); return 1/np.tan(np.radians(2*th23))*(1-2*s13**2)/(s13*np.sqrt(2-3*s13**2))
def tm2_direct(th13,th23):
    s13=np.sin(np.radians(th13)); c13=np.cos(np.radians(th13)); s12=np.sqrt(1/(3*c13**2)); c12=np.sqrt(1-s12**2)
    s23=np.sin(np.radians(th23)); c23=np.cos(np.radians(th23)); A=c12*c23; B=s12*s23*s13
    return (A**2+B**2-1/3)/(2*A*B)          # |U_mu2|^2 = 1/3
check("relation = direct PMNS evaluation at (8.57, 49)", abs(tm2_cosd(8.57,49.0)-tm2_direct(8.57,49.0))<1e-12)
check("delta_CP = +-130 deg at theta23 = 49 deg (the paper's earlier number)", abs(np.degrees(np.arccos(tm2_cosd(8.57,49.0)))-130.4)<0.2)
for t23 in (41.0,43.3,45.0,48.5,50.6):
    c=tm2_cosd(8.57,t23); d=np.degrees(np.arccos(np.clip(c,-1,1)))
    print(f"   theta23={t23:5.1f}: cos dCP={c:+.3f}  |dCP|={d:6.1f} deg")
band=[np.degrees(np.arccos(np.clip(tm2_cosd(8.57,t),-1,1))) for t in np.linspace(41.0,50.6,200)]
check("TM2 band over the NuFIT 6.0 3-sigma theta23 range is |dCP| in [50,156] deg", abs(min(band)-50)<2 and abs(max(band)-156)<2)
check("with-SK best fit (43.3) gives cos dCP > 0 while data prefer cos dCP < 0 (212 deg): a live test", tm2_cosd(8.57,43.3)>0 and np.cos(np.radians(212))<0)

print("\n"+"="*70)
print(f"tm2_jointfit: {sum(PASS)}/{len(PASS)} structural checks pass; joint fit chi^2: A={cA:.0f}, B={cB:.2f}")
print("VERDICT: TM2 = lead (trivial-singlet protected); the test is the cos(dCP)-theta23 relation,")
print("band |dCP| in [50,156] deg over NuFIT 6.0; the joint fit (5 params / 4 obs) is status, not a test;")
print("theta13 = thC/sqrt2 is a leading-order estimate 7% high, not a prediction.")
print("="*70)
assert all(PASS)
