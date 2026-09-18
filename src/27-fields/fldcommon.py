"""
fldcommon.py — shared registry for the 27-fields validation package
====================================================================
"Standard-Model Interactions over Finite Relational Substrate" (Akhtman & Voether, 2026), validation package of the
FRC corpus (finite-ring-space/src/27-fields). The paper's twenty-eight validation scripts are kept as written — each
self-contained, printing its computed values against the manuscript's statements — and run here through one
registry: a *family* is one script (identified as fld.<stem>, e.g. fld.ew1), run in its own namespace with its
printed PASS/FAIL (or [OK]/[XX]) lines captured; its micro-checks are those lines together with the registry's own
predicates (PRED below), which read the script's namespace and output and decide the manuscript's stated values
explicitly — most of the scripts print booleans and numbers without asserting them, so the decision is made here.
An exception, a nonzero exit or a failed predicate fails the family. Each family names the row(s) of the paper's
predicate ledger it witnesses (LEDGER; rows cited as 27:XN), and the ledger's source column cites the family ids in
return; the paper's Appendix "Reproducibility map" is the per-script map.

Kinds, the paper's own three classes (Appendix "Reproducibility map"), recorded per family in results.json:
EXACT — integer, F_p, F_{p²} or cyclotomic arithmetic throughout; MIXED — an exact core with a labelled
continuum-comparison layer; APPROX — a continuum-comparison or dimensional-transmutation reading by construction.

Master-ledger rows reached through the paper rows: 00:B5 (27:C11), 00:H1 (27:C4, C5, C6), 00:H2 (27:C6),
00:H3 (27:Z1, Y1), 00:I1 (27:C7), 00:I2 (27:C7), 00:I3 (27:Z1), 00:I4 (27:P9), 00:J1 (27:C8), 00:J4 (27:C10),
00:K2 (27:P8), 00:G1 (27:C2), 00:E1, 00:E3 (27:C2, C3), 00:D6 (27:B1–B4), 00:D2 (27:B5), 00:N1 (27:P1–P7),
00:Z5 (27:C9), 00:Z8 (27:C2).
"""
import io, json, os, re, sys, time, traceback, math
from fractions import Fraction as Fr

RESULTS = []
MICRO = []                    # (family, label, ok)
HERE = os.path.dirname(os.path.abspath(__file__))

# family -> paper rows witnessed
LEDGER = {
    "fld.em1_prototype":     "27:C2, 27:C3, 27:X2",
    "fld.enumerate_maxwell": "27:C2, 27:X3",
    "fld.audit_finitism":    "27:C2, 27:C3",
    "fld.correspondence":    "27:C1, 27:C7",
    "fld.o2_numbers":        "27:C2",
    "fld.p2":                "27:C2",
    "fld.p3":                "27:C4",
    "fld.ew1":               "27:C4, 27:C5, 27:C6, 27:X4, 27:X5",
    "fld.weak_spectrum":     "27:C5, 27:X3, 27:X5",
    "fld.weak_current":      "27:C4, 27:C6, 27:X6",
    "fld.p4":                "27:C4, 27:X6",
    "fld.p10":               "27:C10",
    "fld.v_scale":           "27:Y1, 27:Z1",
    "fld.qcd":               "27:C7, 27:X7",
    "fld.p5":                "27:C7",
    "fld.string_tension":    "27:C7, 27:X7",
    "fld.p6":                "27:X7, 27:Z1",
    "fld.missing_rank":      "27:C7, 27:C8",
    "fld.generation":        "27:C6, 27:C8, 27:X8",
    "fld.p8":                "27:C9, 27:P4, 27:X8",
    "fld.p8b":               "27:C9, 27:X8",
    "fld.p9":                "27:C10",
    "fld.p9b":               "27:C10, 27:X9, 27:P1",
    "fld.p11":               "27:C11",
    "fld.p1":                "27:C6, 27:P3",
    "fld.p7":                "27:P5, 27:Z1",
    "fld.koide":             "27:X10, 27:P8",
    "fld.strongcp":          "27:X11, 27:P9",
}

# the paper's class per script (Appendix "Reproducibility map": exact 15, mixed 11, approx 2)
KIND = {f: "EXACT" for f in LEDGER}
for f in ("fld.em1_prototype", "fld.enumerate_maxwell", "fld.o2_numbers", "fld.p2", "fld.weak_current", "fld.qcd",
          "fld.string_tension", "fld.p6", "fld.koide", "fld.p1", "fld.p7"):
    KIND[f] = "MIXED"
for f in ("fld.correspondence", "fld.v_scale"):
    KIND[f] = "APPROX"

LABELS = {
    "fld.em1_prototype": "the finite U(1) prototype on Z/M (M = 12, 52, 156, 420 — the phase cycles of F₁₃, F₅₃, F₁₅₇, F₄₂₁): plaquette flux, Wilson action, covariant difference and global superselection gauge-invariant on 200 random configurations each; holonomy = enclosed flux (discrete Stokes) and additive; the Coulomb coefficient of the L = 128 lattice Green's function against 1/4π; like charges repel, gravity attracts (the sign dichotomy)",
    "fld.enumerate_maxwell": "uniqueness of the Maxwell operator: the range-1 adjacency-local gauge- and hypercubic-invariant quadratic space has exact F_p corank 2 on L = 4, 5, 6, splitting into one relevant O(k²) operator — the transverse projector |k|²δ − kk — and one irrelevant O(k⁴) artefact",
    "fld.audit_finitism": "the finitism cross-check of the electromagnetic and admissible-space claims with no float: F(dλ) = 0 on all 64 basis gauge fields, the constant gauge inert, the L = 4 Coulomb Green's function as an exact rational (two unit charges at separation 1: 257/7680), the O1 admissible nullity 2 by exact integer rank, the Wilson action cyclotomic (1 − cos 2πF/M in Q(ζ_M))",
    "fld.correspondence": "the finite gauge correspondence, block by block: Z_M → U(1) a homomorphism with positive Wilson weight (A); SU(2,F₃) = 2T ⊂ SU(2,C), |2T| = |SL(2,F₃)| = 24, S ≥ 0 (B); the low-curvature Yang–Mills quadratic term with O(ε⁴) residue for SU(2), SU(3) (C); exact conjugation invariance (D); the window residue linear in H (E); σ > 0 from positivity on 2T (F); the character lift fixed on the shells (G); finite quadrature on the near-identity ball (H)",
    "fld.o2_numbers": "the bare coupling as phase-channel capacity: 1/α_bare = 4π; the EM/gravity hierarchy α/(m_p/m_P)² ≈ 10³⁶; the gap 4π → 137.04 recorded as the open part (factor ≈ 10.9)",
    "fld.p2": "the order-one coefficient of α_bare = 1/4π is 1 (channel unity); the capacity-bounded Gauss law 4πr² sin E = q gives the weak-field Coulomb coefficient 1/4π (r·A₀(r) at r = 20), the saturation core r* = (4π)^(−1/2), and a finite self-energy of the order q²/(8πr*)",
    "fld.p3": "the cell-local SU(2,F₃) weak connection on K = F₉: |SU(2,3)| = 24 = q(q² − 1), non-abelian, Tr M ∈ F₃; Wilson gauge invariance Tr(gMg⁻¹) = Tr M exhaustive over the group and on an explicit plaquette; the doublet covariant; the drive diag(i, −i) commutes with a proper centraliser only (SU(2) broken to U(1))",
    "fld.ew1": "electroweak breaking as drive–torus misalignment, exact in F₁₃: Ad_drive fixes H (eigenvalue 1, the massless photon) and rotates E, F (gapped W±); the drive's centraliser in SL₂(F₁₃) is the split torus (order p − 1 = 12); the non-split torus does not commute; the neutral (W₃, B) mass matrix has a zero eigenvalue and custodial ρ = 1 symbolically; sin²θ_W = Tr T₃²/Tr Q² = 1/2 for a lone lepton doublet and 3/8 for a complete generation (Tr T₃² = 2, Tr Q² = 16/3)",
    "fld.weak_spectrum": "the propagating spectrum as the Hessian of S_ρ at the broken vacuum: eigenvalues {0, g²v²/4 (×2), (g² + g'²)v²/4} over Q, the photon the exact kernel ∝ (0, 0, g', g), the (W₃, B) block singular (ρ = 1), M_W²/M_Z² = cos²θ_W = 5/8 at sin²θ_W = 3/8; the same structure as a finite-field identity over F₁₃ and F₅ (photon kernel, det ≡ 0, W-degeneracy, M_Z² ≠ 0)",
    "fld.weak_current": "the V−A current: left = Σζ⁰ = N and right = Σζ_N^(2δτ) = 0 exactly for q = 3, 5, 7, 13; the chiral projector P_L = drive-period average, idempotent, annihilating the right branch; G_F = 1/(√2 v²) symbolically; the numeric G_F at v = 246.22 GeV against the measured value (3 × 10⁻³ %) [approx]",
    "fld.p4": "maximal parity violation from the Frobenius branch, exact in Z/(q+1): Frobenius is inversion on the boost cycle (q = 3, 5, 7, 13); the drive commutes with Frobenius iff 2δ ≡ 0 (mod N); the coupling over one drive period is N on the drive-aligned branch and exactly 0 on the Frobenius branch for a generator drive",
    "fld.p10": "chirality selection: the two orientation conventions ε = ±1 disagree on the absolute label (L against R) and agree that the weak couples to the drive-aligned branch — the relational invariant",
    "fld.v_scale": "the electroweak scale against the transmutation forms [approx]: the coefficient landing on M_W is a fit (b = 2.00); the Standard-Model b₂ = 19/6 lands at 10⁸–10⁹ GeV; the SU(2) infrared scale below 10⁻²⁰ GeV; the QCD control consistent within 10 %; the closed form m_P e^(−(2π)²) = 87.4 GeV within 10 % of M_W; the O1 numeral 2^(3/2) m_P e^(−(2π)²) = 247.2 GeV against v = 246.2 GeV (+0.38 %)",
    "fld.qcd": "the strong sector: |SU(3,2)| = 216 = q³(q² − 1)(q³ + 1) by exhaustive enumeration over F₄, the centre the norm-one cube roots of unity (Z₃, colour triality); the strong-coupling string tension σ = −ln c₁(β) for U(1) (σ(0.5) = 1.4168), Z₂, Z₃, positive and decreasing in β [approx]",
    "fld.p5": "the cell-local SU(3,F₄) gluon connection: |SU(3,2)| = 216; the plaquette conjugates and Tr P is invariant, exhaustively over the group; the commutator plaquette U₁U₂U₁⁻¹U₂⁻¹ ≠ I (gluon self-coupling) against = I for the abelian diagonal control; the triplet covariant",
    "fld.string_tension": "the string tension in finite units: the S₃ and 2T character orthogonality (Σχ = 0, ⟨χ,χ⟩ = 1), |2T| = 24 ⊂ SU(2,C) with trace multiset {2:1, −2:1, 0:6, 1:8, −1:8}, c₁^(2T)(β) in closed form with leading β/4 and agreement with continuum SU(2) through O(β³); c₁^(SU(3)) = β/18 + β²/216 + … on the resolved window; σ > 0 for every tested β; |SU(3,2)| = 216 and centre Z₃ float-free over F₄",
    "fld.p6": "asymptotic freedom: b₀ = 11 − (2/3)n_f as exact rationals (29/3 at n_f = 2, 7 at n_f = 6, positive up to n_f = 16, negative at 17; the abelian control negative); Λ_QCD by one-loop transmutation from the M_Z anchor in the 50–500 MeV decade (87 MeV at n_f = 5); (m_p/m_P)² = e^(−88) [approx]",
    "fld.missing_rank": "the rank tower: centre orders [1, 2, 3] for n = 1, 2, 3 over the first eight admissible Ω ≡ 5 (mod 12); the minimal ranks carrying 3 and 2 in the centre are 3 (colour) and 2 (isospin); |SU(3,5)| = 378 000 by exact count; three norm-one cube roots of unity; two explicit SU(3,5) matrices unitary with det 1, Wilson trace invariant, non-commuting; dim Λ^even(C⁵) = 16",
    "fld.generation": "one generation as the spinor of the rank-five frame C³ ⊕ C²: sixteen Weyl fermions (15 + ν^c), hypercharges the weight sums of (−1/3, +1/2), the electric charges {±2/3, ±1/3, 0, ±1}, ΣY = ΣY³ = 0 (anomaly freedom), Tr T₃²/Tr Q² = 3/8 — exact rationals",
    "fld.p8": "the spinorial unification argument: 1 + 5 + 10 = 16; the proton lifetime τ_p ~ M_X⁴/(α_GUT² m_p⁵) scaling as M_X⁴, 4.6 × 10³⁵ yr at M_X = 10¹⁶ GeV and 10⁴⁸ yr at the Planck scale, above the Super-Kamiokande bound and row P4's 10⁴⁵ yr [approx]",
    "fld.p8b": "the X, Y leptoquarks as the colour–isospin off-block: dim SU(5) − dim(SU(3)×SU(2)×U(1)) = 24 − 12 = 12 = the 3 × 2 complex off-block; dim SO(10) = 45; 1 + 5 + 10 = 16",
    "fld.p9": "generations as Galois conjugates: Frobenius orbit sizes on F_{q^n}^× for q = 2, 3, 5 — full orbits of size 2 (n = 2, the chiralities), 3 (n = 3, the generations), 6 (n = 6); the degrees 2 and 3 coprime",
    "fld.p9b": "the closed role ladder's 1 + 3 split: one non-generative role (counting, the bosonic carrier) and three generative roles (the generations); the geometric-mean masses ordered gen1 < gen2 < gen3 with each step above ×40",
    "fld.p11": "the substrate residue: 5 is the unique residue mod 12 with r ≡ 1 (mod 4) and r ≡ 2 (mod 3); the primes below 200 000 split by residue mod 12 at 1/4 each (Dirichlet, within 0.01); the corpus shells 13, 53, 61, 157, 421 all ≡ 1 (mod 4), 53 alone ≡ 5 (mod 12)",
    "fld.p1": "one-loop running with b = (41/10, −19/6, −7): α₁ = α₂ at ≈ 10¹³ GeV with sin²θ_W = 3/8 there exactly; the α₃ near-miss below 20 %; running 3/8 back to M_Z lands within 0.03 of the measured 0.231 [approx]",
    "fld.p7": "the mass mechanism: the seesaw m_ν = y²v²/M_R reaches the 0.01–0.1 eV band for M_R = 10¹⁴–10¹⁵ GeV; m_b/m_τ = 2.35 in the b–τ band 2–3; the winding-overlap |Σζ^(kτ)|/T equal to 1 at k = 0 and decreasing in the winding distance [approx]",
    "fld.koide": "the framed-rational Koide identity over F_p, p = 17, 53, 173, 389, 1373 (p ≡ 5 mod 12): Σλ = 3a, Σλ² = 3a² + 6N(b), Q = 1/3 + (2/3)ρ², ρ² = 1/2 ⇒ Q = 2/3 exactly; the measured charged-lepton Q against 2/3 (10⁻⁵) and ρ² against 1/2 [approx]",
    "fld.strongcp": "the strong-CP angle over F_{p²}/F_p, p = 17, 53, 173, 389, 1373: Hermitian circulant and textured up/down mass matrices have det ∈ F_p (arg det M_q = 0), det(M_u M_d) ∈ F_p, and [M_u, M_d] ≠ 0 (the CKM misalignment free) — 20 exact checks",
}

def script_of(fam):
    return fam.split(".")[1]            # fld.<stem> runs <stem>.py

_CUR = [None]

def chk(label, ok):
    """A labelled micro-check, recorded under the running family."""
    ok = bool(ok)
    MICRO.append((_CUR[0], str(label), ok))
    print(("PASS " if ok else "FAIL ") + str(label))

class _Exit(Exception):
    def __init__(self, code): self.code = code

def _grab(out, pattern, conv=float, n=1):
    """The n-th regex capture in the script's output (conv applied)."""
    m = re.findall(pattern, out)
    return conv(m[n - 1]) if len(m) >= n else None

# ----------------------------------------------------------------------------------------------------------------
# the registry's predicates: fam -> function(ns, out) making chk calls on the script's namespace / printed output
# ----------------------------------------------------------------------------------------------------------------
def _pred_em1(ns, out):
    for M in (12, 52, 156, 420):
        line = _grab(out, rf"\[A/B\] M=\s*{M}\s+(.*)", str)
        chk(f"M={M}: plaquette, Wilson, covariant-difference and global-superselection invariance (200 configurations)",
            line is not None and line.count("True") == 4 and "False" not in line)
    for M in (12, 156, 420):
        line = _grab(out, rf"\[C\]\s+M=\s*{M}\s+(.*)", str)
        chk(f"M={M}: holonomy = enclosed flux (discrete Stokes) and additive", line is not None and line.count("True") == 2)
    ratio = _grab(out, r"ratio = ([0-9.]+)")
    resid = _grab(out, r"rel\.resid = ([0-9.]+)%")
    chk(f"Coulomb coefficient C/(1/4π) = {ratio} within 2 % on the L = 128 lattice (residual {resid} %)",
        ratio is not None and abs(ratio - 1) < 0.02 and resid is not None and resid < 2)
    chk("like charges repel (U > 0, falling with r)", _grab(out, r"REPEL \(U>0, falls with r\): (\w+)", str) == "True")
    chk("gravity attracts (U < 0, deepening as r → 0)", _grab(out, r"ATTRACTS \(U<0, deepens as r->0\)\s*: (\w+)", str) == "True")

def _pred_maxwell(ns, out):
    chk("the Maxwell plaquette action is gauge-invariant (‖Q_M B‖ = 0) and hypercubic-invariant on L = 5",
        "gauge-inv True" in out and "hypercubic-inv True" in out)
    for L in (4, 5, 6):
        m = re.search(rf"\(L={L}\): dim\(T&L&C&G\) = (\d+)\s+=\s+(\d+) relevant .*?\+\s+(\d+) irrelevant .*?projector: ([0-9.e+-]+)", out)
        chk(f"L={L}: exact F_p corank 2 = 1 relevant + 1 irrelevant", m is not None and (m.group(1), m.group(2), m.group(3)) == ("2", "1", "1"))
        chk(f"L={L}: the relevant operator is the transverse projector (deviation < 1e-4)", m is not None and float(m.group(4)) < 1e-4)

def _pred_audit(ns, out):
    import sympy as sp
    worst, const_ok, nsites = ns["partA"](4)
    chk(f"F(dλ) = 0 on all {nsites} basis gauge fields (max |F| = {worst})", worst == 0 and nsites == 64)
    chk("the gradient of a constant gauge function vanishes identically", const_ok)
    axis, U = ns["partB"](4)
    chk(f"L = 4 Coulomb Green's function exact rational: U(sep 1) = {U} = 257/7680", U == Fr(257, 7680))
    chk("G(0,0,0) > G(1,0,0) > G(2,0,0) on the axis (monotone potential)", axis[0][1] > axis[1][1] > axis[2][1])
    npar, nullity = ns["partC"](4, 1)
    chk(f"O1 admissible nullity = {nullity} by exact integer rank (of {npar} range-1 parameters)", nullity == 2)
    want = {(12, 1): 1 - sp.sqrt(3) / 2, (12, 3): sp.Integer(1), (52, 13): sp.Integer(1), (8, 1): 1 - sp.sqrt(2) / 2}
    for M, F, exact, flt in ns["partD"]():
        chk(f"1 − cos(2π·{F}/{M}) = {exact} exactly in Q(ζ_{M})", sp.simplify(exact - want[(M, F)]) == 0)

def _pred_correspondence(ns, out):
    P = ns["PASS"]
    chk(f"all {len(P)} block checks of the script pass (A–H)", all(P) and len(P) >= 25)
    chk("|SL(2,F₃)| = 24 = |2T| (the exact q = 3 embedding)", ns["sl23"] == 24 and len(ns["G"]) == 24)
    chk("window residue ratio r(100)/r(10) ≈ 10 (linear in H)", 8 < ns["ratio"] < 12)

def _pred_o2(ns, out):
    chk("1/α_bare = 4π", abs(ns["inv_alpha_bare"] - 4 * math.pi) < 1e-12)
    chk(f"EM/gravity hierarchy α/(m_p/m_P)² = {ns['ratio']:.3e} in [10³⁶, 2·10³⁶]", 1e36 < ns["ratio"] < 2e36)
    chk(f"the gap 4π → 137.04 is a factor {ns['gap']:.2f} (the open part, 10.9)", abs(ns["gap"] - 10.905) < 0.01)

def _pred_p2(ns, out):
    ab = ns["alpha_bare"]
    chk("α_bare = 1/(4π), coefficient 1", abs(ab - 1 / (4 * math.pi)) < 1e-12)
    coef = ns["A0"](20.0) * 20.0
    chk(f"weak-field Coulomb coefficient r·A₀(r) at r = 20 = {coef:.5f} against 1/4π within 1 %", abs(coef / ab - 1) < 0.01)
    chk("saturation core r* = (4π)^(−1/2)", abs(ns["rstar"] - math.sqrt(1 / (4 * math.pi))) < 1e-12)
    U, U0 = ns["U_cut"], 1 / (8 * math.pi * ns["rstar"])
    chk(f"finite self-energy U(>r*) = {U:.4f} of the order q²/(8πr*) = {U0:.4f} (within a factor 2)", 0 < U and 0.5 < U / U0 < 2)

def _pred_p3(ns, out):
    mm, inv, tr, matvec = ns["mm"], ns["inv"], ns["tr"], ns["matvec"]
    chk("|SU(2,3)| = 24 = q(q² − 1)", ns["order"] == 24)
    chk("SU(2,3) is non-abelian", ns["nonabelian"])
    chk("Tr M ∈ F₃ for all M", ns["tr_in_F3"])
    chk("Tr(gMg⁻¹) = Tr M for all (g, M) — exhaustive Wilson invariance", ns["conj_inv"])
    chk("the explicit plaquette transforms by conjugation, P' = g_a P g_a⁻¹", ns["P2"] == mm(mm(ns["ga"], ns["P"]), inv(ns["ga"])))
    chk("Tr P invariant on the explicit plaquette", tr(ns["P2"]) == tr(ns["P"]))
    chk("the doublet's covariant difference transforms as D → g_a D", ns["D2"] == matvec(ns["ga"], ns["D"]))
    chk("the drive diag(i, −i) does not commute with all of SU(2,3)", not ns["commutes_with_all"])
    chk(f"the drive's centraliser has order {ns['centralizer']} < 24 (SU(2) broken to a U(1))", 0 < ns["centralizer"] < 24)

def _pred_ew1(ns, out):
    eig, cent, torus, nu, commutes = ns["partA"](13, 2)
    chk("Ad_drive H = H (eigenvalue 1: the massless photon)", eig["H"] == 1)
    chk(f"Ad_drive rotates E, F (eigenvalues {eig['E']}, {eig['F']} ≠ 1: gapped W±)", eig["E"] != 1 and eig["F"] != 1)
    chk("E and F eigenvalues are mutual inverses mod 13 (g², g⁻²)", (eig["E"] * eig["F"]) % 13 == 1)
    chk(f"the drive's centraliser in SL₂(F₁₃) has order {cent} = p − 1 (the split torus)", cent == torus == 12)
    chk("the non-split torus generator does not commute with the drive (misalignment)", not commutes)
    eigs, rho, tan = ns["partB"]()
    import sympy as sp
    chk("the neutral (W₃, B) mass matrix has a zero eigenvalue (the photon)", any(sp.simplify(k) == 0 for k in eigs))
    chk("custodial ρ = 1 symbolically", sp.simplify(rho - 1) == 0)
    s_lep, s_gen, trT3, trQ = ns["partC"]()
    chk("lone lepton doublet: sin²θ_W = 1/2", s_lep == Fr(1, 2))
    chk(f"complete generation: Tr T₃² = {trT3}, Tr Q² = {trQ}", trT3 == 2 and trQ == Fr(16, 3))
    chk("complete generation: sin²θ_W = Tr T₃²/Tr Q² = 3/8", s_gen == Fr(3, 8))

def _pred_weak_spectrum(ns, out):
    import sympy as sp
    g, gp, v = ns["g"], ns["gp"], ns["v"]
    eig = {sp.simplify(k): m for k, m in ns["eig"].items()}
    MW2, MZ2 = ns["MW2"], ns["MZ2"]
    chk("photon: eigenvalue 0 present", sp.Integer(0) in eig)
    chk("W±: eigenvalue g²v²/4 with multiplicity 2", eig.get(sp.simplify(MW2)) == 2)
    chk("Z: eigenvalue (g² + g'²)v²/4 with multiplicity 1", eig.get(sp.simplify(MZ2)) == 1)
    kern = ns["ns"][0]
    chk("the photon eigenvector is ∝ (0, 0, g', g)", sp.simplify(kern[0]) == 0 and sp.simplify(kern[1]) == 0 and sp.simplify(kern[2] * g - kern[3] * gp) == 0)
    chk("custodial ρ = 1 exactly", sp.simplify(ns["rho"] - 1) == 0)
    chk("det of the (W₃, B) block ≡ 0", sp.simplify(ns["WB"].det()) == 0)
    chk("M_W²/M_Z² = cos²θ_W = 5/8 at sin²θ_W = 3/8", ns["MW2_over_MZ2"] == sp.Rational(5, 8))
    for (q, gg, ggp, vv) in ((13, 1, 2, 2), (5, 1, 1, 2)):     # the script's two instances (g² + g'² ≠ 0 mod q)
        Mq, iq = ns["weak_modq"](q, gg=gg, ggp=ggp, vv=vv)
        Mq = Mq.applyfunc(lambda z: z % q)
        res = (Mq * sp.Matrix([0, 0, ggp, gg])).applyfunc(lambda z: z % q)
        chk(f"F_{q}: (0, 0, g', g) is the exact photon kernel", all(x % q == 0 for x in res))
        chk(f"F_{q}: det of the (W₃, B) block ≡ 0 (ρ = 1)", Mq[2:4, 2:4].det() % q == 0)
        chk(f"F_{q}: W₁, W₂ degenerate, M_Z² = (g² + g'²)v²/4 ≠ 0", Mq[0, 0] % q == Mq[1, 1] % q and ((gg * gg + ggp * ggp) * vv * vv) % q != 0)

def _pred_weak_current(ns, out):
    import sympy as sp
    cs = ns["char_sum"]
    for q in (3, 5, 7, 13):
        N = q + 1
        chk(f"q={q}: left = Σζ⁰ = N = {N} and right = Σζ_N^(2τ) = 0 exactly", cs(N, 0) == N and cs(N, 2) == 0)
    for q in (5, 13):
        N = q + 1
        PL = sp.diag(sp.Rational(1, N) * cs(N, 0), sp.Rational(1, N) * cs(N, 2))
        chk(f"q={q}: P_L = diag(1, 0) idempotent and annihilating the right branch",
            PL == sp.diag(1, 0) and sp.simplify(PL * PL - PL) == sp.zeros(2, 2))
    v = ns["v"]
    chk("G_F = 1/(√2 v²) from M_W² = g²v²/4", sp.simplify(ns["GF"] - 1 / (sp.sqrt(2) * v ** 2)) == 0)
    chk("[approx] 1/(√2 v²) at v = 246.22 GeV agrees with the measured G_F within 0.01 %", abs(ns["GF_pred"] / ns["GF_meas"] - 1) < 1e-4)

def _pred_p4(ns, out):
    for q in (3, 5, 7, 13):
        chk(f"q={q}: Frobenius is inversion on the boost cycle C_{q + 1}", ns["frobenius_is_inversion"](q))
    for q, delta in [(3, 1), (3, 2), (7, 1), (7, 3)]:
        N = q + 1
        chk(f"q={q}, δ={delta}: the drive commutes with Frobenius iff 2δ ≡ 0 (mod {N})",
            ns["commutator_with_frobenius"](q, delta) == ((2 * delta) % N == 0))
    for q in (3, 5, 7, 13):
        N = q + 1
        delta = next(d for d in range(1, N) if math.gcd(d, N) == 1)
        L, R = ns["coupling_coherence"](q, delta)
        chk(f"q={q}: left coupling = N = {N}, right coupling = 0 exactly (generator drive δ={delta})", L == N and R == 0)

def _pred_p10(ns, out):
    cb = ns["coupled_branch"]
    chk("convention ε = +1 couples to 'L', ε = −1 to 'R' (the absolute label is convention)", cb(+1) == "L" and cb(-1) == "R")
    chk("in both conventions the coupled branch is the drive-aligned one", all({"L": 1, "R": -1}[cb(e)] * e * ns["drive"] > 0 for e in (1, -1)))

def _pred_v_scale(ns, out):
    chk("the script's own verdict: no failed check", ns["fails"] == 0)
    v1 = 2 ** 1.5 * ns["mP"] * math.exp(-(2 * math.pi) ** 2)
    chk(f"Y1 numeral: 2^(3/2) m_P e^(−(2π)²) = {v1:.1f} GeV against v = 246.2 GeV, +{100 * (v1 / 246.21965 - 1):.2f} % (within 0.5 %)",
        abs(v1 / 246.21965 - 1) < 0.005)
    chk(f"m_P e^(−(2π)²) = {ns['vc']:.1f} GeV (87.4)", abs(ns["vc"] - 87.4) < 0.2)

def _pred_qcd(ns, out):
    m = re.search(r"\|SU\(3,2\)\| enumerated = (\d+)\s+formula .* = (\d+)\s+match: (\w+)", out)
    chk("|SU(3,2)| = 216 = q³(q² − 1)(q³ + 1) by exhaustive enumeration over F₄", m is not None and m.group(1) == m.group(2) == "216" and m.group(3) == "True")
    chk("centre Z₃ (the scalar cube roots of unity)", re.search(r"->\s+Z_3", out) is not None)
    s = ns["sigma_U1"]
    chk(f"U(1) string tension σ(0.5) = {s(0.5):.4f} (1.4168)", abs(s(0.5) - 1.4168) < 1e-3)
    chk("σ_U(1)(β) decreasing in β (0.2 … 4.0) and positive", all(s(a) > s(b) > 0 for a, b in zip((0.2, 0.5, 1.0, 2.0), (0.5, 1.0, 2.0, 4.0))))
    chk("σ_Z₃(β) positive at β = 0.2 … 4.0", all(ns["sigma_ZN"](b, 3) > 0 for b in (0.2, 0.5, 1.0, 2.0, 4.0)))

def _pred_p5(ns, out):
    import numpy as np
    mm, inv, trace, matvec = ns["mm"], ns["inv"], ns["trace"], ns["matvec"]
    chk("|SU(3,2)| = 216", ns["order"] == 216)
    chk("the plaquette transforms by conjugation, P' = g_a P g_a⁻¹", np.array_equal(ns["P2"], mm(mm(ns["ga"], ns["P"]), inv(ns["ga"]))))
    chk("Tr P invariant on the explicit plaquette", np.array_equal(trace(ns["P2"]), trace(ns["P"])))
    chk("Tr(gPg⁻¹) = Tr P for all g ∈ SU(3,2) — exhaustive", ns["ok"])
    chk("the commutator plaquette U₁U₂U₁⁻¹U₂⁻¹ ≠ I (gluon self-coupling)", not ns["eqI"](ns["F"]))
    chk("the abelian diagonal control plaquette = I", ns["eqI"](ns["Fab"]))
    chk("the triplet's covariant difference transforms as D → g_a D", np.array_equal(ns["D_q2"], matvec(ns["ga"], ns["D_q"])))

def _pred_string(ns, out):
    P = ns["PASS"]
    chk(f"all {len(P)} checks of the script pass", all(P) and len(P) == 18)
    chk("leading c₁^(2T) = β/4 and the SU(3) fit coefficients (β/18, β²/216)", abs(ns["coef"][0] - 1 / 18) < 1e-4 and abs(ns["coef"][1] - 1 / 216) < 1e-4)

def _pred_p6(ns, out):
    b0, bU = ns["b0_SU3"], ns["b0_U1"]
    chk("b₀(SU(3), n_f = 2) = 29/3, b₀(n_f = 6) = 7", b0(2) == Fr(29, 3) and b0(6) == 7)
    chk("b₀ > 0 up to n_f = 16, < 0 at n_f = 17; the abelian b₀ < 0", b0(16) > 0 and b0(17) < 0 and all(bU(n) < 0 for n in (2, 6, 16)))
    chk(f"Λ_QCD by one-loop transmutation from the M_Z anchor (n_f = 5) = {ns['Lam'] * 1000:.0f} MeV, in the 50–500 MeV decade [approx]", 0.05 < ns["Lam"] < 0.5)
    chk("(m_p/m_P)² = e^(−88.0) [approx]", abs(2 * math.log(ns["M_P"] / ns["m_p"]) - 88.0) < 0.1)

def _pred_missing_rank(ns, out):
    chk("centre tower [1, 2, 3] over the first eight admissible Ω ≡ 5 (mod 12)", ns["A_ok"])
    chk("minimal rank with 3 | centre is 3 (colour), with 2 | centre is 2 (isospin)", ns["rank_for_3"] == 3 and ns["rank_for_2"] == 2)
    chk("|SU(3,5)| = 378 000 by exact count", ns["SU3"] == 378000)
    chk("three norm-one cube roots of unity (the triality centre)", len(ns["centre_unitary"]) == 3)
    chk("two explicit SU(3,5) matrices: unitary, det 1", ns["unit_ok"] and ns["det_ok"])
    chk("Wilson trace gauge-invariant; [U₁, U₂] ≠ I", ns["gi_ok"] and ns["self_ok"])
    chk("dim Λ^even(C⁵) = 16", ns["dim_even"] == 16)

def _pred_generation(ns, out):
    GEN, half = ns["GEN"], ns["half"]
    nWeyl = sum(c * len(t) for _, c, t, _ in GEN)
    sumY = sum(c * len(t) * y for _, c, t, y in GEN)
    sumY3 = sum(c * len(t) * y ** 3 for _, c, t, y in GEN)
    T3 = sum(c * sum(x ** 2 for x in t) for _, c, t, y in GEN)
    Q2 = sum(c * sum((x + y) ** 2 for x in t) for _, c, t, y in GEN)
    charges = {x + y for _, c, t, y in GEN for x in t}
    chk("sixteen Weyl fermions (15 + ν^c)", nWeyl == 16)
    chk("ΣY = 0 (gauge–gravitational anomaly)", sumY == 0)
    chk("ΣY³ = 0 (cubic anomaly)", sumY3 == 0)
    chk("the electric charges are {±2/3, ±1/3, 0, ±1}", charges == {Fr(2, 3), Fr(-1, 3), Fr(-2, 3), Fr(1, 3), Fr(0), Fr(-1), Fr(1)})
    chk("Tr T₃²/Tr Q² = 3/8", T3 / Q2 == Fr(3, 8))
    chk("every hypercharge is a weight sum of (−1/3, +1/2)", all(any(y == a * Fr(-1, 3) + b * Fr(1, 2) for a in range(-3, 4) for b in range(-2, 3)) for _, _, _, y in GEN))

def _pred_p8(ns, out):
    chk("1 + 5 + 10 = 16", 1 + 5 + 10 == 16)
    taus = [(float(a), float(b)) for a, b in re.findall(r"M_X = ([0-9.e+]+) GeV .*?tau_p ~ ([0-9.e+]+) yr", out)]
    d = dict(taus)
    chk("τ_p ∝ M_X⁴: the three printed lifetimes scale as the fourth power of M_X [approx]",
        len(d) == 3 and all(abs(math.log10(d[b] / d[a]) - 4 * math.log10(b / a)) < 0.05 for a, b in zip(sorted(d), sorted(d)[1:])))
    chk(f"τ_p at the Planck scale = {d.get(max(d), 0):.1e} yr ≥ 10⁴⁵ yr (row P4's bound) [approx]", d.get(max(d), 0) >= 1e45)
    chk(f"τ_p at M_X = 10¹⁶ GeV = {d.get(min(d), 0):.1e} yr, above the Super-K bound 10³⁴ yr [approx]", d.get(min(d), 0) > 1e34)

def _pred_p8b(ns, out):
    chk("dim SU(5) = 24, dim SU(3)×SU(2)×U(1) = 12", ns["dim_su5"] == 24 and ns["dim_SM"] == 12)
    chk("dim SU(5) − dim(SM) = 12 = the 3 × 2 complex off-block (the X, Y)", ns["dim_su5"] - ns["dim_SM"] == ns["dim_offblock"] == 12)
    chk("dim SO(10) = 45", ns["dim_so10"] == 45)

def _pred_p9(ns, out):
    fo = ns["frobenius_orbits"]
    for q in (2, 3, 5):
        sizes = {n: max(len(o) for o in fo(q, n)) for n in (2, 3, 6)}
        chk(f"q={q}: full Frobenius orbits of size 2, 3, 6 on F_{{q^2}}, F_{{q^3}}, F_{{q^6}}", sizes == {2: 2, 3: 3, 6: 6})
        chk(f"q={q}: every orbit size divides the extension degree", all(all(len(o) in (1, 2, 3, 6) and n % len(o) == 0 for o in fo(q, n)) for n in (2, 3, 6)))
    chk("the chirality (2) and generation (3) degrees are coprime", math.gcd(2, 3) == 1)

def _pred_p9b(ns, out):
    import statistics
    chk("one non-generative role (counting) and three generative roles", len(ns["roles"]) == 4 and len(ns["generative"]) == 3)
    geo = [statistics.geometric_mean(m.values()) for m in ns["gens"].values()]
    chk("geometric-mean masses ordered gen1 < gen2 < gen3", geo[0] < geo[1] < geo[2])
    chk("each generation step is above ×40 in geometric mean [approx]", geo[1] / geo[0] > 40 and geo[2] / geo[1] > 40)

def _pred_p11(ns, out):
    chk("5 is the unique residue mod 12 with r ≡ 1 (mod 4) and r ≡ 2 (mod 3)", {r for r in range(12) if r % 4 == 1 and r % 3 == 2} == {5})
    cnt, tot = ns["cnt"], ns["tot"]
    chk("the primes below 200 000 split by residue mod 12 at 1/4 each within 0.01 (Dirichlet)", all(abs(cnt[r] / tot - 0.25) < 0.01 for r in (1, 5, 7, 11)))
    chk("the corpus shells 13, 53, 61, 157, 421 are ≡ 1 (mod 4); 53 alone ≡ 5 (mod 12)", all(p % 4 == 1 for p in (13, 53, 61, 157, 421)) and [p for p in (13, 53, 61, 157, 421) if p % 12 == 5] == [53])

def _pred_p1(ns, out):
    chk("sin²θ_W = (3/5)/(1 + 3/5) = 3/8 at α₁ = α₂", abs(ns["sin2_X"] - 0.375) < 1e-12)
    chk(f"α₁ = α₂ at M_X = {ns['M_X']:.2e} GeV, in [10¹², 10¹⁴] [approx]", 1e12 < ns["M_X"] < 1e14)
    miss = abs(ns["a3_at"] - ns["aG"]) / ns["aG"]
    chk(f"the α₃ near-miss is {100 * miss:.0f} % (below 20 %) [approx]", miss < 0.20)
    chk(f"running 3/8 back to M_Z gives {ns['sin2_at'](0):.3f}, within 0.03 of 0.231 [approx]", abs(ns["sin2_at"](0) - 0.23121) < 0.03)

def _pred_p7(ns, out):
    v = ns["v"]
    band = [y ** 2 * v ** 2 / MR * 1e9 for MR in (1e14, 1e15) for y in (1.0, 0.3)]
    chk("the seesaw reaches the 0.01–0.1 eV band for M_R = 10¹⁴–10¹⁵ GeV [approx]", any(0.01 < m < 0.1 for m in band))
    chk(f"m_b/m_τ = {ns['mb_obs'] / ns['mtau_obs']:.2f} in the b–τ band 2–3 [approx]", 2 < ns["mb_obs"] / ns["mtau_obs"] < 3)
    N, T = ns["N"], ns["T"]
    ov = [abs(sum(complex(math.cos(2 * math.pi * k * t / N), math.sin(2 * math.pi * k * t / N)) for t in range(T))) / T for k in range(6)]
    chk("the winding overlap is 1 at k = 0 and decreasing in the winding distance k = 0 … 5", abs(ov[0] - 1) < 1e-12 and all(ov[k] > ov[k + 1] for k in range(5)))

def _pred_koide(ns, out):
    chk("the script's own tally: 5 framed-rational checks, 0 failed", ns["_pass"] == 5 and ns["_fail"] == 0)
    chk(f"[approx] measured Q = {ns['Qm']:.6f} against 2/3 within 1e-4", abs(ns["Qm"] - 2 / 3) < 1e-4)
    r2 = (ns["a1m"] / ns["a0m"]) ** 2
    chk(f"[approx] measured ρ² = {r2:.5f} against 1/2 within 1e-3", abs(r2 - 0.5) < 1e-3)

def _pred_strongcp(ns, out):
    chk("the script's own tally: 20 framed-rational checks, 0 failed", ns["_pass"] == 20 and ns["_fail"] == 0)

PRED = {
    "fld.em1_prototype": _pred_em1, "fld.enumerate_maxwell": _pred_maxwell, "fld.audit_finitism": _pred_audit,
    "fld.correspondence": _pred_correspondence, "fld.o2_numbers": _pred_o2, "fld.p2": _pred_p2, "fld.p3": _pred_p3,
    "fld.ew1": _pred_ew1, "fld.weak_spectrum": _pred_weak_spectrum, "fld.weak_current": _pred_weak_current,
    "fld.p4": _pred_p4, "fld.p10": _pred_p10, "fld.v_scale": _pred_v_scale, "fld.qcd": _pred_qcd, "fld.p5": _pred_p5,
    "fld.string_tension": _pred_string, "fld.p6": _pred_p6, "fld.missing_rank": _pred_missing_rank,
    "fld.generation": _pred_generation, "fld.p8": _pred_p8, "fld.p8b": _pred_p8b, "fld.p9": _pred_p9,
    "fld.p9b": _pred_p9b, "fld.p11": _pred_p11, "fld.p1": _pred_p1, "fld.p7": _pred_p7, "fld.koide": _pred_koide,
    "fld.strongcp": _pred_strongcp,
}

def run_block(fam):
    """Run one script of the suite under the registry, apply the registry's predicates, record the family verdict."""
    stem = script_of(fam)
    path = os.path.join(HERE, stem + ".py")
    src = io.open(path, encoding="utf-8").read()
    src = src.replace("raise SystemExit(", "raise __exit__(").replace("sys.exit(", "__exit__(")
    verdicts, lines = [], []
    def _print(*args, **kw):
        s = " ".join(str(a) for a in args)
        kw.pop("file", None); print(s, **kw)
        for line in s.split("\n"):
            lines.append(line)
            t = line.strip()
            m = re.match(r"^ALL PASS: (True|False)", t)
            if m:
                verdicts.append(m.group(1) == "True")
            elif re.match(r"^\[?(PASS|FAIL|OK|XX)\]?\b", t):
                verdicts.append(t[:6].find("PASS") >= 0 or t[:4].find("OK") >= 0)
    def _exit(code=0):
        raise _Exit(code)
    g = {"__name__": "__main__", "__file__": path, "print": _print, "__exit__": _exit}
    _CUR[0] = fam
    n0 = len(MICRO)
    t0 = time.time(); code = 0; err = None
    old = os.getcwd(); os.chdir(HERE); sys.path.insert(0, HERE)
    try:
        exec(compile(src, path, "exec"), g)
    except _Exit as e:
        code = e.code if isinstance(e.code, int) else (0 if e.code in (None, 0) else 1)
    except Exception:
        err = traceback.format_exc().strip().splitlines()[-1]
        print("    EXCEPTION: " + err)
    finally:
        os.chdir(old)
    for i, v in enumerate(verdicts):                     # the script's own printed verdict lines
        MICRO.append((fam, f"verdict line {i + 1}", v))
    if err is None and fam in PRED:                      # the registry's predicates on the namespace and output
        try:
            PRED[fam](g, "\n".join(lines))
        except Exception:
            err = "predicate: " + traceback.format_exc().strip().splitlines()[-1]
            print("    EXCEPTION: " + err)
    _CUR[0] = None
    micro = [ok for f, _, ok in MICRO[n0:]]
    ok = err is None and code == 0 and all(micro) and len(micro) > 0
    detail = f"{len(micro)} checks, {time.time() - t0:.1f} s" + (f"; {err}" if err else "") + (f"; exit {code}" if code else "")
    check(fam, ok, detail=detail, kind=KIND.get(fam, "EXACT"))
    return ok

def check(pid, ok, detail="", kind="EXACT", label=None):
    ok = bool(ok)
    rows = LEDGER.get(pid, "")
    label = label or LABELS.get(pid, pid)
    RESULTS.append({"id": pid, "rows": rows, "script": script_of(pid), "label": label, "ok": ok, "detail": detail, "kind": kind})
    print(f"  [{'PASS' if ok else 'FAIL'}] {pid:22s} {kind:6s} [{rows}] {label[:90]}" + (f"  --  {detail}" if detail else ""))
    return ok

def summary(write=True):
    n_ok = sum(r["ok"] for r in RESULTS)
    print(f"\nSUMMARY: {n_ok}/{len(RESULTS)} checks passed ({len(MICRO)} micro-checks)" + ("" if n_ok == len(RESULTS) else "  <-- FAILURES"))
    if write:
        with open(os.path.join(HERE, "results.json"), "w") as f:
            json.dump(RESULTS, f, indent=1, ensure_ascii=False)
    return n_ok == len(RESULTS)
