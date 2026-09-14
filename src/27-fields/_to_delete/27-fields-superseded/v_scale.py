#!/usr/bin/env python3
# framed-rational status: [APPROX] -- continuum / degenerate-idealisation comparison layer (the finite-window correspondence and phenomenology); not an exact framed-rational claim by construction.
# =====================================================================
#  v_scale.py -- a run at fixing the electroweak scale v from the
#  saturation capacity of the non-split synchronisation channel.
#
#  Inputs (corpus + measured):
#    * Theorem 5.6 (27-fields): a mass is the cardinality fraction
#      m/sqrt(Omega) of the totality;  sqrt(Omega) = m_P (Planck mass).
#    * Capacity of the phase channel  kappa <-> alpha_bare = 1/4pi
#      (Prop 5.5).  Saturation when |sin| = 1 (gravity Lemma 6.1).
#    * Strong analogue: sigma ~ ln(1/beta) fixes Lambda_QCD by
#      dimensional transmutation (27-fields Sec 7).
#
#  Question: is v a CLOSED sub-horizon combination of the horizons,
#  or does it reduce to the cross-scale running (Conjecture 4.2, Omega-hard)?
# =====================================================================
import math

GeV = 1.0
mP   = 1.220890e19      # Planck mass (GeV)
MP   = 2.435323e18      # reduced Planck mass (GeV)
H0   = 1.437e-42        # Hubble (GeV)  ~67.4 km/s/Mpc
v    = 246.220          # Higgs VEV (GeV)
MW   = 80.377
MZ   = 91.1876
fourpi = 4*math.pi

# Omega from the de Sitter / coherence-horizon reading sqrt(Omega)=mP/H0
sqrtOmega = mP/H0
Omega     = sqrtOmega**2
print(f"sqrt(Omega) = mP/H0 = {sqrtOmega:.3e}   Omega = {Omega:.3e}  (~10^122)")
print(f"weak scale band: M_W={MW}, v={v} GeV;  v/mP = {v/mP:.3e}  (the cardinality fraction)\n")

# ---------------------------------------------------------------------
# 1. Is v a clean power  v = mP * Omega^(-k) ?
# ---------------------------------------------------------------------
print("== 1. power-law test  v = mP * Omega^(-k) ==")
k_v  = math.log(mP/v )/math.log(Omega)
k_MW = math.log(mP/MW)/math.log(Omega)
print(f"   k(v)  = {k_v:.4f}   k(M_W) = {k_MW:.4f}   -> not a clean rational; no simple power.")
for k in (1/8, 1/9, 1/7, 0.137):
    print(f"     mP*Omega^-{k:.3f} = {mP*Omega**(-k):.3e} GeV")

# ---------------------------------------------------------------------
# 2. Dimensional transmutation from the phase-channel capacity 1/4pi.
#    Lambda/M_UV = exp(-2pi/(b0 * alpha)),  alpha = alpha_bare = 1/4pi.
#    => exponent 2pi/(b0/4pi) = 8 pi^2 / b0.   Test small integer b0.
# ---------------------------------------------------------------------
print("\n== 2. dimensional transmutation  v = mP * exp(-8 pi^2 / b0),  alpha=1/4pi ==")
target_exp_v  = math.log(mP/v)      # = 38.44
target_exp_MW = math.log(mP/MW)
print(f"   need exponent ln(mP/v)={target_exp_v:.3f}, ln(mP/M_W)={target_exp_MW:.3f}")
print(f"   8 pi^2 / b0 = exponent  ->  b0(v) = {8*math.pi**2/target_exp_v:.3f}, "
      f"b0(M_W) = {8*math.pi**2/target_exp_MW:.3f}")
for b0 in (1,2,3, 19/6):
    val = mP*math.exp(-8*math.pi**2/b0)
    print(f"     b0={b0:.3f}:  v_pred = {val:.3e} GeV   (8pi^2/b0={8*math.pi**2/b0:.2f})")

# the clean candidate: exponent = 4 pi^2  (i.e. b0 = 2)
print("\n   clean candidate  v = mP * exp(-(2pi)^2) = mP*exp(-4 pi^2):")
vc = mP*math.exp(-4*math.pi**2)
print(f"     = {vc:.3e} GeV    vs  M_W={MW},  v={v}")
print(f"     ratio to M_W: {vc/MW:.3f};  ratio to v: {vc/v:.3f}")
print(f"     (4 pi^2 = (2pi)^2, 2pi the synchronisation factor of a0=cH0/2pi;")
print(f"      8pi^2/b0 with b0=2 and the capacity alpha=1/4pi)")

# ---------------------------------------------------------------------
# 3. Saturation-core reading (gravity Prop 6.2): r* = sqrt(m/4pi kappa).
#    A channel at capacity defines a core scale; invert for the mass.
#    Geometric-mean horizon combinations natural to FRC:
# ---------------------------------------------------------------------
print("\n== 3. geometric-mean / horizon combinations ==")
cands = {
 "sqrt(mP*H0)            ": math.sqrt(mP*H0),
 "mP/4pi                 ": mP/fourpi,
 "mP/(4pi)^? ...         ": None,
 "mP*exp(-4pi^2)         ": mP*math.exp(-4*math.pi**2),
 "mP*exp(-4pi^2)/(4pi)   ": mP*math.exp(-4*math.pi**2)/fourpi,
 "mP*exp(-4pi^2)*4pi     ": mP*math.exp(-4*math.pi**2)*fourpi,
 "mP*Omega^(-1/8)/(4pi)  ": mP*Omega**(-1/8)/fourpi,
}
for name,val in cands.items():
    if val is None: continue
    print(f"   {name} = {val:.3e} GeV")

# ---------------------------------------------------------------------
# 4. Honest verdict: how much of v needs the running?
#    Compare the leading capacity estimate to the measured band, and
#    state the residual as the cross-scale running (Conjecture 4.2).
# ---------------------------------------------------------------------
print("\n== 4. verdict ==")
est = mP*math.exp(-4*math.pi**2)
print(f"   leading capacity estimate  v ~ mP*exp(-4pi^2) = {est:.1f} GeV")
print(f"   measured weak band         M_W..v = {MW} .. {v} GeV")
print(f"   the estimate lands IN the weak band (off M_W by {100*(est-MW)/MW:+.0f}%),")
print(f"   i.e. the saturation capacity fixes the SCALE; the exact value")
print(f"   (the O(1) exponent / b0) is the cross-scale beta-function = Omega-hard.")
print(f"""
   CLASSIFICATION:
     * v is a dimensional-transmutation scale: the saturation/condensation
       scale of the non-split channel (no fundamental scalar => no hierarchy
       problem; v is a transfer-operator gap, like Lambda_QCD).
     * its exact value reduces to the matched cross-scale running of the
       weak coupling (Conjecture 4.2), the SAME Omega-hard residue as the
       strong Lambda_QCD (D6) and the absolute fermion masses (E5/B7).
     * => v is Omega-HARD, not sub-horizon-closeable: the RATIO/rho=1/photon-kernel
       are the comprehensible small residues, while the absolute scale v is
       Omega-hard.
""")
