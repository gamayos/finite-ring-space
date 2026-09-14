#!/usr/bin/env python3
# framed-rational status: [APPROX] -- continuum / degenerate-idealisation comparison layer (the finite-window correspondence and phenomenology); not an exact framed-rational claim by construction.
# =====================================================================
#  v_scale.py -- the electroweak scale v as a dimensional-transmutation
#  quantity: v = m_P exp(-c), the exponent c Omega-hard (27-fields,
#  Rem. masscons; ledger rows Z1, O1).
#
#  What this script establishes (2026-09-13 revision, task T22):
#    1. v is not a clean power of Omega.
#    2. The gauge transmutation formula  Lambda = M exp(-8 pi^2 / b)
#       at alpha_bare = 1/4pi lands on the weak band only for b = 2.00,
#       which is a FIT: the Standard-Model SU(2) coefficient is
#       b_2 = 19/6, which gives ~2e8 GeV, and the SU(2) coupling's own
#       infrared transmutation scale (one-loop from alpha_2(M_Z)) is
#       ~1e-24 GeV.  So the electroweak scale is not the SU(2) gauge
#       transmutation scale; the channel that condenses at v is the
#       non-split torus, whose coefficient is Omega-hard.
#    3. Control: the QCD sentence of Prop. af is consistent -- e^{-45}
#       with b_0 = 7 needs alpha_s(M_P) = 0.020, and one-loop running
#       from alpha_s(M_Z) = 0.118 gives 0.019.
#    4. The closed form m_P exp(-(2 pi)^2) = 87 GeV (9 % from M_W) is
#       recorded as a conjecture (row O1), not claimed.
# =====================================================================
import math

mP   = 1.220890e19      # Planck mass (GeV)
H0   = 1.437e-42        # Hubble (GeV)  ~67.4 km/s/Mpc
v    = 246.220          # Higgs VEV (GeV)
MW   = 80.377
MZ   = 91.1876
pi   = math.pi
fails = 0
def check(name, ok):
    global fails
    print(("  PASS  " if ok else "  FAIL  ") + name)
    if not ok: fails += 1

sqrtOmega = mP/H0
Omega     = sqrtOmega**2
print(f"sqrt(Omega) = mP/H0 = {sqrtOmega:.3e}   Omega = {Omega:.3e}  (~10^122)")
print(f"weak band: M_W={MW}, v={v} GeV;  v/mP = {v/mP:.3e}\n")

# 1. no clean power
print("== 1. power-law test  v = mP * Omega^(-k) ==")
k_v  = math.log(mP/v )/math.log(Omega)
k_MW = math.log(mP/MW)/math.log(Omega)
print(f"   k(v) = {k_v:.4f}   k(M_W) = {k_MW:.4f}   -> no simple rational power")

# 2. the gauge transmutation formula is a fit at b = 2, refuted by b_2 = 19/6
print("\n== 2. gauge transmutation  Lambda = mP * exp(-8 pi^2 / b),  alpha_bare = 1/4pi ==")
b_fit_MW = 8*pi**2/math.log(mP/MW)
b_fit_v  = 8*pi**2/math.log(mP/v)
b_fit_87 = 8*pi**2/math.log(mP/(mP*math.exp(-4*pi**2)))
print(f"   b that lands on M_W: {b_fit_MW:.3f};  on v: {b_fit_v:.3f};  on 87.4 GeV: {b_fit_87:.3f}")
b2 = 19/6
L_b2 = mP*math.exp(-8*pi**2/b2)
print(f"   Standard-Model SU(2) coefficient b_2 = 19/6:  mP*exp(-8pi^2/b_2) = {L_b2:.2e} GeV")
check("b = 2 is a fit (|b_fit(M_W) - 2| < 0.01)", abs(b_fit_MW-2) < 0.01)
check("b_2 = 19/6 gives 1e8..1e9 GeV, not the weak band", 1e8 < L_b2 < 1e9)

# SU(2) one-loop running from M_Z: alpha_2^{-1}(mu) = alpha_2^{-1}(M_Z) + (b_2/2pi) ln(mu/M_Z)
a2inv_MZ = 29.6
a2inv_MP = a2inv_MZ + (b2/(2*pi))*math.log(mP/MZ)
mu_IR    = MZ*math.exp(-2*pi*a2inv_MZ/b2)     # alpha_2^{-1} -> 0 (Landau/strong-coupling scale)
print(f"   alpha_2^-1(M_P) = {a2inv_MP:.1f};  SU(2) infrared strong-coupling scale = {mu_IR:.1e} GeV")
check("SU(2) infrared transmutation scale ~1e-24 GeV (< 1e-20 GeV)", mu_IR < 1e-20)

# 3. control: the QCD sentence is consistent
print("\n== 3. control: QCD dimensional transmutation ==")
b0_qcd = 7.0
as_MP_needed = 2*pi/(b0_qcd*45.0)               # e^{-45} = exp(-2pi/(b0 alpha_s(M_P)))
as_MZ = 0.118
as_MP_run = 1.0/(1.0/as_MZ + (b0_qcd/(2*pi))*math.log(mP/MZ))
print(f"   e^-45 with b_0=7 needs alpha_s(M_P) = {as_MP_needed:.4f};  one-loop from 0.118: {as_MP_run:.4f}")
print(f"   ln(mP / 0.2 GeV) = {math.log(mP/0.2):.1f}")
check("QCD exponent consistent (alpha_s(M_P) needed vs run within 10 %)", abs(as_MP_needed/as_MP_run-1) < 0.10)

# 4. the (2 pi)^2 closed form: recorded as conjecture O1
print("\n== 4. the closed form  mP * exp(-(2pi)^2)  (conjecture O1) ==")
vc = mP*math.exp(-(2*pi)**2)
print(f"   mP*exp(-(2pi)^2) = {vc:.2f} GeV;  ratio to M_W: {vc/MW:.3f} (+{100*(vc/MW-1):.0f} %);  ratio to v: {vc/v:.3f}")
check("closed form within 10 % of M_W (the conjecture's stated exposure)", abs(vc/MW-1) < 0.10)

print(f"""
   CLASSIFICATION (Rem. masscons; rows Z1, O1):
     * v = mP exp(-c) is the saturation scale of the non-split channel;
       the exponent c is the cross-scale beta-function, Omega-hard (Z1).
     * c is NOT the SU(2) gauge coefficient: b_2 = 19/6 gives {L_b2:.0e} GeV and
       the gauge coupling's own infrared scale is {mu_IR:.0e} GeV; the b = 2.00
       that lands on M_W is a fit.
     * the closed form mP exp(-(2pi)^2) = {vc:.0f} GeV is a conjecture without a
       derivation of the exponent, recorded as O1 and not claimed.
""")
print("v_scale.py:", "PASS" if fails == 0 else f"FAIL ({fails})")
raise SystemExit(1 if fails else 0)
