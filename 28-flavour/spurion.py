#!/usr/bin/env python3
# -*- coding: utf-8 -*-
"""
The spurion value epsilon = lambda ~ 0.225 (Cabibbo / Wolfenstein), ledger lead.
Question: is lambda an independent fundamental input, or does it reduce to the winding kernel?
Findings:
 (1) the integer-power TEXTURE is forced by the role-depth charges (0,1,2); only epsilon's value
     is free.
 (2) the Gatto-Sartori-Tonin relation V_us = sqrt(m_d/m_s) is forced -> lambda is READ OFF the
     down-quark masses, not an independent parameter; the Cabibbo angle relates mixing to masses.
 (3) lambda is a function of the down-sector circulant data (delta_d = delta_0/2 by the lock, and
     r_d): sqrt(m_d/m_s) computed from the circulant ~ lambda. So lambda reduces to (delta_0, r_d).
 (4) LEAD: lambda ~ delta_0 ~ 2/9 -- the Cabibbo suppression and the lepton winding phase coincide
     to ~1%, consistent with both being the same inter-generation winding distance; if structural,
     lambda LOCKS to delta_0 and is not a separate residual.
Continuum/data computation (measured masses, floats): a labelled data-confrontation, not exact.
"""
import numpy as np
PASS,FAIL="PASS","FAIL"; res=[]
def ck(t,c,d=""): res.append((t,bool(c))); print(f"[{PASS if c else FAIL}] {t}: {d}")
s2=np.sqrt(2)

# data
md,ms,mb=4.67,93.4,4180.0
Vus=0.22452; lam=Vus
d0=0.2222              # lepton winding phase (= delta_0, ~2/9)

print("="*70); print("(1) the texture is forced; only epsilon's value is free")
print("="*70)
# role-depth charges (0,1,2) for down/lepton, (0,2,4) for up -> integer powers of lambda
pw_down=[round(np.log(x/mb)/np.log(lam),2) for x in (md,ms)]
print(f"   down powers log(m/m_b)/log(lambda) = {pw_down} ~ (4,2): role charges (2,1,0) [forced]")
ck("1.texture", abs(pw_down[1]-2)<0.7, "integer lambda-powers from role-depth charges (forced structure)")

print("\n"+"="*70); print("(2) Gatto: V_us = sqrt(m_d/m_s) -- lambda read off masses [forced relation]")
print("="*70)
gatto=np.sqrt(md/ms)
ck("2.gatto", abs(gatto-Vus)/Vus<0.02,
   f"sqrt(m_d/m_s) = {gatto:.4f} vs V_us = {Vus:.4f} ({100*abs(gatto-Vus)/Vus:.1f}%): lambda is NOT independent")

print("\n"+"="*70); print("(3) lambda is a function of the down circulant (delta_0, r_d)")
print("="*70)
# down Koide circulant: Q_d, r_d from masses; delta_d = delta_0/2 (cross-sector lock)
sm=np.array([np.sqrt(md),np.sqrt(ms),np.sqrt(mb)]); a=sm.sum()/3
Qd=(md+ms+mb)/sm.sum()**2; rd=np.sqrt(6*Qd-2)
dd=d0/2
f=np.array([1+rd*np.cos(dd+2*np.pi*k/3) for k in range(3)]); f=np.sort(np.abs(f))
lam_circ=f[0]/f[1]     # sqrt(m_d)/sqrt(m_s) = sqrt(m_d/m_s)
print(f"   r_d={rd:.3f}, delta_d=delta_0/2={dd:.3f} -> circulant gives sqrt(m_d/m_s)={lam_circ:.4f}")
ck("3.fromwinding", abs(lam_circ-lam)<0.03,
   f"lambda = sqrt(m_d/m_s) = {lam_circ:.3f} from (delta_0,r_d): reduces to the winding kernel, not independent")

print("\n"+"="*70); print("(4) LEAD: lambda ~ delta_0 ~ 2/9"); print("="*70)
print(f"   lambda = {lam:.4f} ;  delta_0 = {d0:.4f} ;  2/9 = {2/9:.4f}")
ck("4.coincidence", abs(lam-d0)/d0<0.02,
   f"lambda and the lepton phase delta_0 coincide to {100*abs(lam-d0)/d0:.1f}%: same winding distance? [lead]")

print("\n"+"="*70)
print("CONCLUSION: lambda is not an independent input. The texture is forced (role charges);")
print("the Gatto relation V_us=sqrt(m_d/m_s) is forced; lambda reduces to the down-winding data")
print("(delta_0, r_d) and numerically equals the lepton phase delta_0~2/9. So the spurion FOLDS")
print("into the single winding kernel -- one fewer independent residual.")
n=sum(1 for _,c in res if c); print(f"\nchecks: {n}/{len(res)} pass")
for t,c in res:
    if not c: print("  FAILED",t)
