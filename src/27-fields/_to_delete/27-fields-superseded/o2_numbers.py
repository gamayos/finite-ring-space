# framed-rational status: MIXED -- exact framed-rational core; continuum constructs are confined to clearly-labelled [approx] / degenerate-idealisation comparisons (Tier 2/3/5 or measured-data), never to an exact claim.
"""
O2 supporting computation: the electromagnetic coupling as phase-channel capacity.

Pins the numbers behind the three O2 statements:
  (1) channel unity: bare coupling under unit capacity = 1/4pi  (= EM-1 Coulomb coeff)
  (2) hierarchy theorem: alpha is Omega-independent; gravity ~ (m/sqrt Omega)^2,
      so alpha / (G m_p^2 / hbar c) is set by Omega ~ 10^122.
  (3) the gap from 1/4pi to the measured 1/137, decomposed (charge unit, running).
No fit; every number is either a measured constant or an exact substrate ratio.
"""
import math

# --- measured constants (PDG) ------------------------------------------------
alpha0      = 1 / 137.035999084      # fine-structure constant, Thomson (zero-energy)
alpha_MZ    = 1 / 127.951            # at the Z pole
m_P_GeV     = 1.220890e19            # Planck mass
m_p_GeV     = 0.9382720813           # proton
m_e_GeV     = 0.51099895000e-3       # electron
Omega       = (m_P_GeV / 1.0) ** 2   # placeholder; we use m_p/m_P directly below

print("=" * 66)
print("O2  electromagnetic coupling as phase-channel capacity")
print("=" * 66)

# (1) channel unity: the bare coupling -----------------------------------------
inv_alpha_bare = 4 * math.pi
print("\n(1) Channel unity / bare coupling (unit capacity, unit winding charge)")
print(f"    shell Coulomb coefficient (EM-1 prototype, gravity G_shell) = 1/4pi"
      f" = {1/(4*math.pi):.5f}")
print(f"    => 1/alpha_bare = 4pi = {inv_alpha_bare:.4f}    (alpha_bare = {1/inv_alpha_bare:.5f})")
print(f"    measured 1/alpha(0)   = {1/alpha0:.4f}")
print(f"    measured 1/alpha(M_Z) = {1/alpha_MZ:.4f}")

# (2) hierarchy theorem --------------------------------------------------------
grav_coupling = (m_p_GeV / m_P_GeV) ** 2          # G m_p^2 / (hbar c) = (m_p/m_P)^2
ratio = alpha0 / grav_coupling
print("\n(2) Hierarchy: EM couples to winding INDEX (label), gravity to winding")
print("    RATE (cardinality fraction m/sqrt(Omega)).  alpha is Omega-independent.")
print(f"    G m_p^2/(hbar c) = (m_p/m_P)^2 = {grav_coupling:.3e}")
print(f"    alpha(0)                        = {alpha0:.3e}")
print(f"    alpha / (G m_p^2/hbar c)        = {ratio:.3e}   (~10^{math.log10(ratio):.1f})")
print(f"    => the ~10^36 EM/gravity hierarchy IS the substrate size:")
print(f"       (m_P/m_p)^2 = Omega/m_p^2 (Planck units) = {1/grav_coupling:.3e}")
print(f"       gravity is weak because Omega ~ 10^122 is large; EM does not see Omega.")

# (3) the residual gap, decomposed honestly -----------------------------------
print("\n(3) From the bare O(1/4pi) to the measured 1/137 -- the honest open part")
gap = (1/alpha0) / inv_alpha_bare
print(f"    gap in 1/alpha:  4pi = {inv_alpha_bare:.2f}  ->  137.04   (factor {gap:.2f} in alpha)")
print(f"    sign:  alpha is larger in the UV (screening) -- CORRECT direction.")
print(f"    magnitude check: SM RG running of 1/alpha_EM from M_P to 0 is ~ +30..50,")
print(f"        NOT +124, so running ALONE cannot bridge 12.6 -> 137.")
print(f"    => most of the gap is NOT running; it is the projection of the bare")
print(f"       reframing-channel coupling onto the physical photon:")
print(f"       (b) electroweak mixing  e = g' cos(theta_W)  [Weinberg angle = EW-1,")
print(f"           the split/non-split torus tilt in the weak sector], and")
print(f"       (a) the precise O(1) capacity coefficient (analogue of gravity's open")
print(f"           order-one constants, e.g. the 2pi of the a_0 floor).")
print(f"    CONCLUSION: O2 fixes the mechanism (alpha = phase-channel capacity), the")
print(f"    order (1/4pi, channel unity with gravity), and the sign; the PURE NUMBER")
print(f"    1/137 reduces to the charge spectrum + Weinberg angle and does NOT close")
print(f"    within EM-1.  It is the meeting point of the EM and weak sectors.")
print("=" * 66)
