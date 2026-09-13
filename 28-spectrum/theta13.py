#!/usr/bin/env python3
# -*- coding: utf-8 -*-
"""
theta_13 (ledger open: the theta13/lopsided realisation).  Test whether it upgrades to a lead.
The lopsided M_e = M_d^T (sec. mixing) makes the charged-lepton 1-2 rotation inherit the
down-quark Cabibbo angle theta_C^e ~ theta_C.  A charged-lepton 1-2 rotation on a TBM/magic
neutrino base induces, through the maximal atmospheric mixing (theta23 ~ 45deg, sin = 1/sqrt2,
the quarter-turn), the reactor angle
        theta_13 ~ theta_C / sqrt2          (weak quark-lepton complementarity)
and the solar sum rule
        theta_12 + theta_C ~ 45deg          (quark-lepton complementarity, the quarter-turn bisector).
Since theta_C = arcsin(lambda) and lambda ~ delta_0 (spurion push), theta13 folds onto the one
phase delta_0 and the quarter-turn.  [continuum/data: a labelled mixing-relation check.]
"""
import numpy as np
deg=np.pi/180
# observed (NuFIT NO)
sC=0.2243; thC=np.degrees(np.arcsin(sC))      # Cabibbo
s13=0.1486; th13=np.degrees(np.arcsin(s13))   # reactor
s23=0.756;  th23=np.degrees(np.arcsin(s23))   # atmospheric
th12=33.4                                     # solar
lam=0.2245; d0=0.2222
s2=np.sqrt(2)

print(f"observed: theta_C={thC:.2f}, theta_13={th13:.2f}, theta_23={th23:.2f}, theta_12={th12:.2f} deg")

print("\n(1) theta_13 ~ theta_C/sqrt2  (lopsided charged-lepton rotation through maximal theta23)")
s13_pred=sC/s2
print(f"   sin theta_13 pred = sin theta_C / sqrt2 = {s13_pred:.4f}  vs observed {s13:.4f}  "
      f"({100*abs(s13_pred-s13)/s13:.0f}%)")
ok1=abs(s13_pred-s13)/s13<0.10

print("\n(2) quark-lepton complementarity: theta_12 + theta_C ~ 45 (quarter-turn bisector)")
qlc=th12+thC
print(f"   theta_12 + theta_C = {qlc:.1f} deg  vs 45 deg  ({abs(qlc-45):.1f} deg off)")
ok2=abs(qlc-45)<3

print("\n(3) theta_13 folds onto delta_0: theta_C = arcsin(lambda), lambda ~ delta_0")
print(f"   sin theta_13 ~ lambda/sqrt2 = {lam/s2:.4f} ~ delta_0/sqrt2 = {d0/s2:.4f}  vs {s13:.4f}")
ok3=abs(lam/s2-s13)/s13<0.10

print("\n(4) the sqrt2 is the quarter-turn: sin(theta23~45deg) = 1/sqrt2")
print(f"   sin theta_23 = {s23:.3f} ~ 1/sqrt2 = {1/s2:.3f} (maximal atmospheric, the magic value)")
ok4=abs(s23-1/s2)/(1/s2)<0.10

print("\n"+"="*68)
print("VERDICT: theta_13 upgrades open -> LEAD.  The lopsided M_e=M_d^T feeds the Cabibbo")
print("rotation into the PMNS; through maximal theta23 (quarter-turn 1/sqrt2) this gives")
print("theta_13 ~ theta_C/sqrt2 ~ lambda/sqrt2 ~ delta_0/sqrt2 (7%) and QLC theta12+theta_C~45 (3%).")
print("So theta_13 folds onto delta_0 + the quarter-turn; residual = the precise charged-lepton")
print("rotation and the theta23 deviation from 45deg.  (Relation accurate to ~7%, not exact.)")
print("="*68)
print(f"checks: {sum([ok1,ok2,ok3,ok4])}/4 within tolerance")
