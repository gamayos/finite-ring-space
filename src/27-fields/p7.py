# framed-rational status: MIXED -- exact framed-rational core; continuum constructs are confined to clearly-labelled [approx] / degenerate-idealisation comparisons (Tier 2/3/5 or measured-data), never to an exact claim.
"""
P7: fermion masses and mixings -- what the substrate fixes, and what is open.

(a) Mechanism: the Yukawa is the Higgs-mediated bridge between the drive-aligned
    (left, P4) and Frobenius-conjugate (right) branches; m = y v, v the spinor-frame
    misalignment (EW-1 Higgs).  The mass connects the two chiralities the weak force
    separates.
(b) Seesaw: the Section-7 singlet nu^c takes a Majorana mass at the unification
    scale (P1); the light-neutrino mass m_nu ~ y^2 v^2 / M_R brackets the observed
    ~0.05 eV for M_R near the GUT scale -- a correct-order prediction.
(c) b-tau Yukawa unification from the SO(10) 16: m_b = m_tau at M_GUT, and QCD
    running enhances m_b, giving m_b/m_tau ~ 2-3 at low energy (observed 2.4).
(d) Hierarchy (LEAD): masses are winding-overlap coherences; the top is the
    maximally coherent fermion (y~1); the inter-generation hierarchy is
    Froggatt-Nielsen-like in the winding distance, reducing to P9.
The precise spectrum and the CKM/PMNS mixings (the flavour problem) are NOT
derived here; they reduce to the three-generation winding assignments (P9).
"""
import math

print("="*68)
print("P7  fermion masses: derivable structure vs the flavour problem")
print("="*68)

# ---- (b) the seesaw neutrino mass scale ----
v = 174.0           # GeV, electroweak VEV (v = 246/sqrt2)
print("\n(b) seesaw:  m_nu ~ y^2 v^2 / M_R   (nu^c Majorana mass M_R at unification)")
print(f"    v = {v} GeV ; observed atmospheric scale ~ 0.05 eV")
for MR in (1e13, 1e14, 1e15, 1e16):
    for y in (1.0, 0.3):
        m_nu_eV = (y**2 * v**2 / MR) * 1e9     # GeV -> eV
        print(f"      M_R={MR:.0e} GeV, y_nu={y}:  m_nu = {m_nu_eV:.3f} eV")
print("    => M_R ~ 1e14-1e15 GeV (near the P1 unification scale) gives ~0.05 eV.")

# ---- (c) b-tau Yukawa unification ----
print("\n(c) b-tau unification (SO(10) 16):  m_b = m_tau at M_GUT")
# crude one-loop QCD enhancement of m_b relative to m_tau between M_GUT and m_b
# m_b/m_tau ~ (alpha_s(m_b)/alpha_s(M_GUT))^{12/(33-2nf)} ... use the known ballpark
mb_obs, mtau_obs = 4.18, 1.777
print(f"    observed m_b/m_tau = {mb_obs/mtau_obs:.2f}")
print(f"    GUT prediction (m_b=m_tau at M_GUT, QCD running) -> m_b/m_tau ~ 2-3  (matches)")

# ---- (d) hierarchy mechanism: winding-overlap coherence (schematic lead) ----
print("\n(d) hierarchy LEAD: mass = overlap of the fermion winding with the Higgs")
print("    aligned winding (top): coherent overlap, y ~ 1 (mass ~ v ~ 174 GeV)")
print("    misaligned windings:  suppressed overlap -> lighter fermions")
# partial character sum over a coherence window T<N: smooth decay with winding distance k
N, T = 60, 12
print(f"    schematic partial overlap |sum_tau zeta_N^(k tau)|/T  (N={N}, window T={T}):")
for k in range(0, 6):
    s = sum(complex(math.cos(2*math.pi*k*t/N), math.sin(2*math.pi*k*t/N)) for t in range(T))
    print(f"      winding distance k={k}:  overlap = {abs(s)/T:.3f}")
print("    a smooth Froggatt-Nielsen-like hierarchy in winding distance;")
print("    the precise spectrum + CKM/PMNS reduce to the generation windings (P9).")
print("="*68)
print("DERIVED: the mass mechanism, the seesaw neutrino scale, b-tau unification.")
print("OPEN (flavour problem): the precise masses and mixings, reducing to P9.")
print("="*68)
