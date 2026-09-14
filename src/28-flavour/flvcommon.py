"""
flvcommon.py — shared registry for the 28-flavour validation package
=====================================================================
"Fermion Flavour Sector over Finite Relational Substrate" (Akhtman & Voether, 2026), validation package of the FRC
corpus (finite-ring-space/src/28-flavour). The paper's sixteen validation scripts are kept as written — twelve print a
labelled verdict per check ([PASS]/[FAIL], [OK]/[XX], [EXACT]/[FAIL]) and a pass count, four print their values without
a verdict — and run here through one registry: a *family* is one script (identified as flv.<stem>, e.g. flv.exact_core),
run in its own namespace with its printed verdict lines captured; its micro-checks are those lines together with the
registry's predicates (PRED below), which read the script's namespace and output and decide the manuscript's stated
values explicitly where the script prints without asserting (framed_koide, theta13, scale_a, coupling_anchor) and pin
the headline numerals elsewhere (the pass counts, Q_ℓ − 2/3, Σm_ν on both orderings, the Cabibbo relation). An
exception, a nonzero exit or a failed predicate fails the family. Each family names the row(s) of the paper's predicate
ledger it witnesses (LEDGER; rows cited as 28:XN), and the ledger's source column cites the family ids in return.

Kinds, the suite's own three classes (the paper's Reproducibility section and the suite README), recorded per family:
EXACT — integer, F_p, F_{p²} or cyclotomic arithmetic throughout, no float in any asserted claim; MIXED — the script
carries its own exact check for at least one claim, the continuum confined to labelled [approx] comparisons; APPROX —
continuum/numerical by construction (a numerical reconfirmation of an identity proven exactly elsewhere, a comparison
with measured data, or an Ω-hard reading).

Master-ledger rows reached through the paper rows: 00:K2 (28:C2, P1), 00:K3 (28:C4, C6, C10, P2, P6), 00:K4 (28:C12),
00:J2 (28:C12), 00:J4 (28:B2), 00:D2 (28:B1), 00:D8 (28:Z3), 00:Z6 (28:Z3), 00:Z8 (28:Z4), 00:C7 (28:C10, Z1),
00:B5 (28:A1).
"""
import io, json, os, re, sys, time, traceback, math
from fractions import Fraction as Fr

RESULTS = []
MICRO = []                    # (family, label, ok)
HERE = os.path.dirname(os.path.abspath(__file__))

# family -> paper rows witnessed
LEDGER = {
    "flv.exact_core":      "28:C1, 28:C2, 28:C3, 28:C4, 28:C10, 28:Z1",
    "flv.framed_koide":    "28:C2, 28:X1",
    "flv.tier_b":          "28:C2, 28:C6, 28:C8, 28:X3, 28:X5, 28:P1",
    "flv.m10":             "28:C1, 28:C2, 28:C3, 28:X7",
    "flv.delta":           "28:C3, 28:C5, 28:Z1, 28:Z2",
    "flv.neutrino":        "28:C11, 28:C11b, 28:P5, 28:P6, 28:X11",
    "flv.pmns_cp":         "28:C10, 28:P8, 28:X10",
    "flv.tm2_jointfit":    "28:C9, 28:C10, 28:P8",
    "flv.quark_amp":       "28:B4, 28:C4, 28:X2, 28:P2",
    "flv.revision_checks": "28:C3, 28:C10, 28:C11b, 28:P2, 28:Z1",
    "flv.up_doubling":     "28:B3, 28:C7, 28:X6",
    "flv.spurion":         "28:C6, 28:X4, 28:Z1",
    "flv.theta13":         "28:C9, 28:X9",
    "flv.scale_a":         "28:Z3",
    "flv.coupling_anchor": "28:Z4",
    "flv.alpha_probe":     "28:A2, 28:Z4",
}

# the suite's class per script (README: EXACT 2, MIXED 7, APPROX 7)
KIND = {f: "MIXED" for f in LEDGER}
for f in ("flv.exact_core", "flv.framed_koide"):
    KIND[f] = "EXACT"
for f in ("flv.pmns_cp", "flv.tm2_jointfit", "flv.spurion", "flv.theta13", "flv.scale_a", "flv.coupling_anchor", "flv.alpha_probe"):
    KIND[f] = "APPROX"

LABELS = {
    "flv.exact_core": "the float-free core, 25 verifications: the circulant Koide identities in Q(ω, √2) (Σλ = 3a, Σλ² = 3a² + 6|b|², Q = 1/3 + (2/3)ρ², ρ² = 1/2 ⇒ Q = 2/3, Hermitian √M with exact eigenvalues); the π/12 boundary as rational π with the electron amplitude vanishing; the cubic Gauss-sum reality and the π/3 quantisation of the drive-twisted overlap as integer identities in Z[Z/3 × Z/p] for p = 17, 29, 41, 53; the trimaximal magic matrix with maximal Jarlskog J = 1/(6√3) in Q(ω); Koide over framed rationals in F_{p²}/F_p (Q = 2/3 exact, the quarter-turn the rational N(b)/a² = 1/2) and the amplitude diagonal N(1 − i) = 2, N(1 − ω) = 3 as integers in F_p for p = 17, 53, 89",
    "flv.framed_koide": "the Koide identity natively over framed rationals (F_{p²}/F_p, Frobenius conjugation, no cyclotomics) on p = 17, 53, 89: the √-mass eigenvalues framed rationals in F_p, Q = 2/3 exactly, the '√2 amplitude' the rational N(b)/a² = 1/2, ω the finite cube root",
    "flv.tier_b": "the Tier-A/B figures: the measured charged-lepton Q against 2/3 (6 × 10⁻⁶), the symbolic Σa = 3, Σa² = 3 + (3/2)r², Q(√2) = 2/3 for all δ and Q = 2/3 ⇔ r = √2; ρ = |â₁|/|â₀| = 1/√2 and the 45° democratic angle; the λ-power texture (down/lepton λ^{4,2,0}, up λ^{8,4,0}) and the Gatto V_us = √(m_d/m_s) (within 5 %); the Wolfenstein CKM powers; the Georgi–Jarlskog double ratio against N_c² = 9 (within 20 %) and b–τ; the lopsided M_e = M_dᵀ giving a large PMNS θ₂₃ with a small CKM θ₂₃, against a seeded hierarchical-seesaw control",
    "flv.m10": "the winding kernel: the circulant √M Hermitian with eigenvalues a + 2|b| cos(δ + 2πk/3); Q = 1/3 + r²/6 symbolically and r = √2 ⇒ 2/3; δ_LO = 3π/4 − 2π/3 = π/12 with the electron massless at leading order and m_μ/m_τ = 0.072 against 0.060; the per-sector extraction (lepton r = √2 to 2 × 10⁻³, quark amplitudes above √2, r_u near √3); the physical δ off the π/12 grid; the parameter reduction",
    "flv.delta": "the cross-sector phase lock δ_ℓ : δ_d : δ_u = 1 : 1/2 : 1/3 in the working scheme (medians over 20 000 seeded mass draws); the symmetric cubic overlap real on every p ≡ 5 (mod 12) below 170 and the drive-twisted overlap complex; small-shell phases quantised to multiples of π/3; δ_LO = π/12",
    "flv.neutrino": "the seesaw of circulants circulant (symbolic, float-free); the signed Q_ν = 2/3 solved with the two measured Δm² on both orderings — normal (m₁ = 0.36, 8.62, 50.15 meV, Σ = 59.1 meV) and inverted (Σ = 102.3 meV) — the boundary branch selecting normal; the m₁ = 0 floor 58.8 meV at NuFIT 6.0; Σm_ν stable across the Δm² 1σ; r_ν = √2 reachable by the seesaw [approx]",
    "flv.pmns_cp": "the magic matrix trimaximal with maximal Jarlskog J = 1/(6√3) and the democratic column; over the TM2 family θ₂₃ = 45° ⇔ |δ_CP| = 90°; TM2 at the observed θ₁₃, θ₂₃ giving δ_CP ≈ −130° and sin²θ₁₂ ≈ 1/3 (numerical, numpy)",
    "flv.tm2_jointfit": "the TM2 status: the trivial-singlet column protected (TM1 reducible), the exact-TM2 solar 0.341, the Cabibbo correction sweeping sin²θ₁₂ through 0.307, θ₁₃ = arcsin(sin θ_C/√2) ≈ 9.15°, the joint fit's parameter count (five for four observables, status not test), the TM2 relation against the direct PMNS evaluation, |δ_CP| = 130.4° at θ₂₃ = 49°, the band [50°, 156°] over the NuFIT 6.0 3σ range, the with-SK best fit as a live test (scipy)",
    "flv.quark_amp": "the quark amplitudes: the Georgi–Jarlskog colour dressing shifts Q from 2/3 to 0.745 against the observed Q_d = 0.731; r_u = 1.759 against √3 (the cube-root colour diagonal, robust over the mass ranges); r² = N(1 − ζ_n) = 2, 3 as integers in F_p for p = 17, 53, 89; Q_u = 0.849 in the working scheme, 0.832 with the pole charm mass (the scheme band of 5/6)",
    "flv.revision_checks": "the revision identities: J = Im ω/9 = 1/(6√3) and J² = 1/108; δ_LO = 3/8 − 1/3 = 1/24 cycle; the signed-amplitude Koide = 2/3 at every δ for r = √2; the cube-invariant determinant ∏√m = a³(cos 3δ/√2 − 1/2) [exact]; 3δ₀ = Q (δ₀ = Q/3), the positive-root neutrino Koide values, the normal-branch preference (> 20×), the Q_u scheme spread [approx]",
    "flv.up_doubling": "the up-sector doubling: the effective Froggatt–Nielsen powers (8, 4) up against (4, 2) down and lepton, up = 2 × down at the integer level; the 10·10 against 10·5̄ structural map with the 10-charge a = (4, 2, 0); the winding self-pair reading",
    "flv.spurion": "the Cabibbo spurion: the down λ-powers from the role charges, the Gatto V_us = √(m_d/m_s) within 2 %, λ from the down circulant (δ₀/2, r_d) within 0.03, λ ≈ δ₀ ≈ 2/9 within 2 % [approx, data]",
    "flv.theta13": "the reactor angle as a leading-order estimate: sin θ₁₃ = sin θ_C/√2 = 0.159 against 0.149 (7 %), quark–lepton complementarity θ₁₂ + θ_C ≈ 45°, the fold onto δ₀/√2, sin θ₂₃ ≈ 1/√2 — four tolerances [approx, data]",
    "flv.scale_a": "the overall scale as transmutation: y_t = √2 m_t/v ≈ 1 (the forced trigger); the one-loop descent of the quartic λ to the scale-invariant point (crossing zero below M_P); the hierarchy v/M_P = e^(−38.4); the lepton scale a² ≈ 314 MeV ≈ y_τ v [approx, dimensional]",
    "flv.coupling_anchor": "the coupling anchor: α_bare⁻¹ = 4π against the unified continuum α_GUT⁻¹ ≈ 40 (the lattice–continuum matching Δ ≈ 27, the bare coupling stronger); α₁ = α₂ at ≈ 10¹³ GeV with the α₃ near-miss below 20 %; the couplings run to M_P [approx]",
    "flv.alpha_probe": "the fine-structure ledger: α_bare⁻¹ = 4π exact; α_EM⁻¹ = α₂⁻¹ + α_Y⁻¹ at M_Z; sin²θ_W → 3/8 at α₁ = α₂ (the derived generation content's b₁, b₂); 4π stronger than α_GUT so the bare-to-lab connection is a matching; the EM/gravity hierarchy α (m_P/m_p)² ≈ 1.2 × 10³⁶ [approx]",
}

def script_of(fam):
    return fam.split(".")[1]            # flv.<stem> runs <stem>.py

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
def _pred_exact_core(ns, out):
    ok = ns["ok"]
    chk(f"the script's own tally: {sum(1 for _, c in ok if c)}/{len(ok)} float-free verifications hold", len(ok) == 25 and all(c for _, c in ok))

def _pred_framed_koide(ns, out):
    chk("Q = 2/3 exact over framed rationals on all three shells p = 17, 53, 89 (the script's verdict)", ns["ok"] is True)
    for p in (17, 53, 89):
        chk(f"p={p}: Q = 2/3 in F_p with the √-mass eigenvalues in F_p (recomputed)", ns["run"](p) is True)

def _pred_tier_b(ns, out):
    r = ns["results"]
    chk(f"the script's own tally: {sum(1 for _, s, _ in r if s == 'PASS')}/{len(r)} checks", len(r) == 17 and all(s == "PASS" for _, s, _ in r))
    chk(f"[approx] measured Q_ℓ − 2/3 = {abs(ns['Q_lep'] - 2 / 3):.1e} < 1e-5 (the paper's 6 × 10⁻⁶)", abs(ns["Q_lep"] - 2 / 3) < 1e-5)
    chk(f"[approx] Gatto V_us = √(m_d/m_s) = {ns['Vus_pred']:.4f} against {ns['Vus']} within 0.5 % (the paper's 0.3 %)", abs(ns["Vus_pred"] - ns["Vus"]) / ns["Vus"] < 0.005)
    chk(f"[approx] Georgi–Jarlskog double ratio = {ns['gj_ratio']:.2f} against 9: the open excess in 10–20 % (the paper's 15 %)", 0.10 < (ns["gj_ratio"] - 9) / 9 < 0.20)
    chk(f"[approx] lopsided: PMNS θ₂₃ = {ns['th_pmns23']:.1f}°, CKM θ₂₃ = {ns['th_ckm23']:.1f}° (the paper's 52.5° and 1.4°)", abs(ns["th_pmns23"] - 52.5) < 0.5 and abs(ns["th_ckm23"] - 1.4) < 0.2)

def _pred_m10(ns, out):
    r = ns["res"]
    chk(f"the script's own tally: {sum(1 for _, s, _ in r if s == 'PASS')}/{len(r)} checks", len(r) == 12 and all(s == "PASS" for _, s, _ in r))
    chk(f"[approx] leading-order m_μ/m_τ = {ns['ratio_lo'][1]:.3f} (the paper's 0.072) against the observed 0.060", abs(ns["ratio_lo"][1] - 0.072) < 0.001)
    chk(f"[approx] charged-lepton circulant r = {ns['rL']:.4f} = √2 within 2 × 10⁻³", abs(ns["rL"] - math.sqrt(2)) < 2e-3)

def _pred_delta(ns, out):
    r = ns["res"]
    chk(f"the script's own tally: {sum(1 for _, s, _ in r if s == 'PASS')}/{len(r)} checks", len(r) == 10 and all(s == "PASS" for _, s, _ in r))
    chk(f"[approx] δ_ℓ = {ns['dl']:.4f} rad against 2/9 = 0.2222 within 0.001 (the paper's δ₀ ≈ 0.222)", abs(ns["dl"] - 2 / 9) < 1e-3)
    chk(f"[approx] the pole-charm up ratio = {ns['du_pole'] / ns['dl']:.3f} (the paper's 0.388)", abs(ns["du_pole"] / ns["dl"] - 0.388) < 0.002)
    chk(f"{len(ns['shells'])} shells p ≡ 5 (mod 12) below 170 scanned", len(ns["shells"]) >= 8)

def _pred_neutrino(ns, out):
    r = ns["res"]
    chk(f"the script's own tally: {sum(1 for _, c in r if c)}/{len(r)} checks", len(r) == 11 and all(c for _, c in r))
    m = ns["m"]; mI = ns["mI"]
    chk(f"[approx] normal ordering: Σm_ν = {m.sum() * 1e3:.1f} meV (the paper's 59.1) with m₁ = {m[0] * 1e3:.2f} meV", abs(m.sum() * 1e3 - 59.1) < 0.2 and m[0] * 1e3 < 0.5)
    chk(f"[approx] inverted root: Σm_ν = {mI.sum() * 1e3:.1f} meV (the paper's 102.3)", abs(mI.sum() * 1e3 - 102.3) < 0.3)
    chk(f"[approx] the m₁ = 0 floor at NuFIT 6.0 = {ns['floor']:.1f} meV (58.8)", abs(ns["floor"] - 58.8) < 0.15)

def _pred_pmns_cp(ns, out):
    r = ns["res"]
    chk(f"the script's own tally: {sum(1 for _, c in r if c)}/{len(r)} checks", len(r) == 6 and all(c for _, c in r))
    chk(f"[approx] TM2 at the observed angles: δ_CP = −{abs(ns['dCP']):.0f}° (the paper's ±124°/±130° band)", 120 <= abs(ns["dCP"]) <= 135)
    chk(f"[approx] J(F) = {abs(ns['jarlskog'](ns['F'])):.5f} = 1/(6√3)", abs(abs(ns["jarlskog"](ns["F"])) - 1 / (6 * math.sqrt(3))) < 1e-12)

def _pred_tm2(ns, out):
    P = ns["PASS"]
    chk(f"the script's own tally: {sum(P)}/{len(P)} structural checks", len(P) == 11 and all(P))
    chk(f"[approx] |δ_CP| = {math.degrees(math.acos(ns['tm2_cosd'](8.57, 49.0))):.1f}° at θ₂₃ = 49° (130.4)", abs(math.degrees(math.acos(ns["tm2_cosd"](8.57, 49.0))) - 130.4) < 0.2)
    chk(f"[approx] the TM2 band over 41°–50.6° is [{min(ns['band']):.0f}°, {max(ns['band']):.0f}°] ([50, 156])", abs(min(ns["band"]) - 50) < 2 and abs(max(ns["band"]) - 156) < 2)
    chk(f"[approx] the joint fit B reaches χ² = {ns['cB']:.2f} with five parameters for four observables (status, not a test)", ns["cB"] < 0.5)

def _pred_quark_amp(ns, out):
    r = ns["res"]
    chk(f"the script's own tally: {sum(1 for _, c in r if c)}/{len(r)} checks", len(r) == 6 and all(c for _, c in r))
    chk(f"[approx] Q_u = {ns['Qu']:.4f} in the working scheme (0.849) and {ns['Qu_pole']:.4f} with the pole charm mass (0.832)", abs(ns["Qu"] - 0.849) < 0.001 and abs(ns["Qu_pole"] - 0.832) < 0.001)
    chk(f"[approx] the GJ-dressed lepton Q = {ns['Qd_gj']:.3f} (0.745) against Q_d = {ns['Qd']:.3f} (0.731)", abs(ns["Qd_gj"] - 0.745) < 0.001 and abs(ns["Qd"] - 0.731) < 0.001)
    chk(f"[approx] r_u = {ns['ru']:.3f} against √3 within 3 %", abs(ns["ru"] - math.sqrt(3)) / math.sqrt(3) < 0.03)

def _pred_revision(ns, out):
    chk(f"the script's own tally: {ns['P'][0]} checks, none failed (each asserts)", ns["P"][0] == 9)
    chk(f"[approx] 3δ₀ = {ns['three_delta']:.5f} = Q = {ns['Q']:.5f} within 1e-4 (δ₀ = Q/3 = 2/9)", abs(ns["three_delta"] - ns["Q"]) < 1e-4)
    chk(f"[approx] on-shell Q_u = {ns['onshell']:.3f} = 5/6 within 0.005; MS̄(M_Z) Q_u = {ns['msz']:.3f} > 0.86", abs(ns["onshell"] - 5 / 6) < 0.005 and ns["msz"] > 0.86)

def _pred_up_doubling(ns, out):
    P = ns["PASS"]
    chk(f"the script's own tally: {sum(P)}/{len(P)} checks", len(P) == 11 and all(P))
    chk("integer exponents: up (8, 4), down (4, 2) = 2 × down", ns["up_int"] == (8, 4) and ns["down_int"] == (4, 2))

def _pred_spurion(ns, out):
    r = ns["res"]
    chk(f"the script's own tally: {sum(1 for _, c in r if c)}/{len(r)} checks", len(r) == 4 and all(c for _, c in r))
    chk(f"[approx] √(m_d/m_s) = {ns['gatto']:.4f} against V_us = {ns['Vus']} within 0.5 %", abs(ns["gatto"] - ns["Vus"]) / ns["Vus"] < 0.005)
    chk(f"[approx] λ = {ns['lam']:.4f} against δ₀ = {ns['d0']} within 2 %", abs(ns["lam"] - ns["d0"]) / ns["d0"] < 0.02)

def _pred_theta13(ns, out):
    chk(f"[approx] sin θ₁₃ = sin θ_C/√2 = {ns['s13_pred']:.4f} against {ns['s13']} within 10 % (the paper's 7 %, a leading-order estimate)", ns["ok1"] and abs(ns["s13_pred"] / ns["s13"] - 1.07) < 0.01)
    chk(f"[approx] θ₁₂ + θ_C = {ns['qlc']:.1f}° against 45° within 3°", ns["ok2"])
    chk(f"[approx] λ/√2 = {ns['lam'] / ns['s2']:.4f} ≈ δ₀/√2 = {ns['d0'] / ns['s2']:.4f} against sin θ₁₃ within 10 %", ns["ok3"])
    chk(f"[approx] sin θ₂₃ = {ns['s23']} against 1/√2 within 10 %", ns["ok4"])
    chk("the script's own count: 4/4 within tolerance", "checks: 4/4 within tolerance" in out)

def _pred_scale_a(ns, out):
    chk(f"[approx] y_t = √2 m_t/v = {ns['yt']:.4f}, within 0.02 of 1 (the forced trigger)", abs(ns["yt"] - 1) < 0.02)
    chk(f"[approx] the one-loop quartic crosses zero at ≈ {ns['MZ'] * math.exp(ns['lam_cross']):.1e} GeV, below M_P" if ns["lam_cross"] else "[approx] the one-loop quartic crosses zero below M_P", ns["lam_cross"] is not None and ns["MZ"] * math.exp(ns["lam_cross"]) < ns["MP"])
    chk(f"[approx] v/M_P = e^(−{ns['c']:.1f}) (the paper's e^(−38))", 38.0 < ns["c"] < 38.6)
    chk(f"[approx] the lepton scale a² = {ns['a2'] ** 2:.0f} MeV (314) and y_τ = {ns['ytau']:.4f} (0.0102)", abs(ns["a2"] ** 2 - 314) < 1 and abs(ns["ytau"] - 0.0102) < 1e-4)

def _pred_coupling(ns, out):
    chk("α_bare⁻¹ = 4π", abs(ns["abare_inv"] - 4 * math.pi) < 1e-12)
    chk(f"[approx] α₁ = α₂ at {ns['muU']:.1e} GeV, α_GUT⁻¹ = {ns['aGUT_inv']:.1f} > 4π: the bare coupling stronger, Δ(α⁻¹) = {ns['Delta']:.1f}", 1e12 < ns["muU"] < 1e14 and ns["aGUT_inv"] > ns["abare_inv"] and 20 < ns["Delta"] < 35)
    miss = abs(ns["aGUT_inv"] - ns["a3U"]) / ns["aGUT_inv"]
    chk(f"[approx] the α₃ near-miss = {100 * miss:.0f} % (below 20 %)", miss < 0.20)

def _pred_alpha_probe(ns, out):
    r = ns["res"]
    chk(f"the script's own tally: {sum(1 for _, c in r if c)}/{len(r)} figure checks", len(r) == 6 and all(c for _, c in r))
    chk(f"[approx] sin²θ_W = {ns['s2w_U']:.4f} at α₁ = α₂ (3/8 within 2 × 10⁻³)", abs(ns["s2w_U"] - 3 / 8) < 2e-3)
    chk(f"[approx] the one-loop fermion sum from 4π adds ≈ {ns['da_inv']:.0f}: α⁻¹ ≈ {ns['a_bare_inv'] + ns['da_inv']:.0f}, not 137 (row AL5)", abs(ns["da_inv"] - 87) < 1 and 95 < ns["a_bare_inv"] + ns["da_inv"] < 105)
    chk(f"[approx] α (m_P/m_p)² = {ns['hier']:.2e} in [10³⁶, 2 × 10³⁶]", 1e36 < ns["hier"] < 2e36)

PRED = {
    "flv.exact_core": _pred_exact_core, "flv.framed_koide": _pred_framed_koide, "flv.tier_b": _pred_tier_b,
    "flv.m10": _pred_m10, "flv.delta": _pred_delta, "flv.neutrino": _pred_neutrino, "flv.pmns_cp": _pred_pmns_cp,
    "flv.tm2_jointfit": _pred_tm2, "flv.quark_amp": _pred_quark_amp, "flv.revision_checks": _pred_revision,
    "flv.up_doubling": _pred_up_doubling, "flv.spurion": _pred_spurion, "flv.theta13": _pred_theta13,
    "flv.scale_a": _pred_scale_a, "flv.coupling_anchor": _pred_coupling, "flv.alpha_probe": _pred_alpha_probe,
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
            elif re.match(r"^(\[?(PASS|FAIL|OK|XX)\]?(?![A-Za-z])|\[EXACT\])", t):     # a script's per-check verdict line (not its summary line)
                verdicts.append(t[:6].find("PASS") >= 0 or t[:4].find("OK") >= 0 or t.startswith("[EXACT]"))
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
