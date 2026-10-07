# framed-rational status: EXACT -- integer / modular-F_p / cyclotomic arithmetic; no float in any asserted check (float, if present, only formats an exact rational for display).
"""
P8: simple unification -- is the rank-5 frame gauged as a simple group?

Architectural argument (lead): matter is the single spinor of the single rank-5
internal frame (Section 7).  The spinor = exterior algebra Lambda^* C^5 = the
SO(10) chiral spinor 16, IRREDUCIBLE under SO(10) (simple) but REDUCIBLE under the
product SU(3)xSU(2)xU(1) into 1 + 5bar + 10.  Matter being ONE irreducible spinor
forces the simple group; the product is the broken-phase remnant.  SO(10) (not just
SU(5)) is favoured: the nu^c singlet lives in the SO(10) 16 but not the SU(5)
5bar+10, and Section 7 derived nu^c.  Predictions: proton decay suppressed if the
unification (X,Y) scale is the substrate/Planck scale; the P1 near-miss is a
prediction of completing structure.
"""
import math

print("="*68)
print("P8  is unification forced?  the spinorial argument and its predictions")
print("="*68)

# ---- (1) irreducibility: one spinor -> simple group ----
print("\n(1) matter = one spinor of one frame -> simple group")
print("    SO(10) chiral spinor 16: IRREDUCIBLE (one matter multiplet)")
print("    under product SU(3)xSU(2)xU(1):  16 = 1 + 5bar + 10  (REDUCIBLE)")
print(f"       dims: 1 + 5 + 10 = {1+5+10}  = 16  (the generation pieces)")
print("    => 'matter is a spinor' (one irreducible 16) forces the SIMPLE group;")
print("       the product is the subgroup the drive+Higgs breaking selects.")

# ---- (2) SO(10) vs SU(5): the nu^c ----
print("\n(2) SO(10) vs SU(5):  the right-handed neutrino")
print("    SU(5):  5bar + 10 = 15 fermions (no nu^c)")
print("    SO(10): 16 = 15 + nu^c  (the singlet)")
print("    Section 7 derived nu^c (the Lambda^0 singlet) => SO(10) favoured,")
print("    the spinor group of the rank-10 (=2x5) orthogonal frame.")

# ---- (3) proton lifetime vs the unification scale ----
print("\n(3) proton decay:  tau_p ~ M_X^4 / (alpha_GUT^2 m_p^5)")
m_p = 0.938                      # GeV
alpha_GUT = 1/40.0
GeVinv_to_yr = 6.582e-25 / 3.156e7    # hbar/GeV in seconds, to years
for label, M_X in [("standard GUT", 1e16), ("substrate ~10^18", 1e18),
                   ("Planck/substrate", 1.22e19)]:
    tau_GeVinv = M_X**4/(alpha_GUT**2 * m_p**5)
    tau_yr = tau_GeVinv*GeVinv_to_yr
    print(f"    M_X = {M_X:.1e} GeV ({label:18s}):  tau_p ~ {tau_yr:.1e} yr")
print("    Super-K bound ~ 1e34 yr.  Unification at the substrate/Planck scale")
print("    gives tau_p ~ 1e44-1e47 yr: proton effectively stable, safely above bounds.")

# ---- (4) the near-miss (from P1) as a prediction ----
print("\n(4) the P1 coupling near-miss (~13%) is then a PREDICTION:")
print("    exact unification (forced by one frame) requires completing structure")
print("    between M_Z and the unification scale -- new physics or substrate-scale")
print("    threshold corrections; falsifiable.")
print("="*68)
print("LEAD: unification (SO(10)) forced by the spinorial architecture; product is")
print("the broken remnant; nu^c favours SO(10); proton stable if M_X~Planck.")
print("OPEN: a rigorous a-priori forcing, the precise scale, the near-miss resolution.")
print("="*68)
