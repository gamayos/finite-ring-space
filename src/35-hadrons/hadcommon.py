"""
hadcommon.py — shared registry for the 35-hadrons validation package
====================================================================
"Ground-State Light Hadron Spectroscopy over Finite Substrate" (Akhtman & Voether, 2026), validation package of the
FRC corpus (finite-ring-space/src/35-hadrons). The paper's fifteen validation scripts and its figure script are kept
as written — fourteen assert their exact claims and print their report, forward_eigenvalues prints one [PASS] line
per check — and run here through one registry: a *family* is one script (identified as had.<stem>, e.g.
had.su3f_relations), run in its own namespace, its printed verdict lines captured; its micro-checks are those lines
together with the registry's predicates (PRED below), which read the script's namespace and decide the manuscript's
stated values explicitly — the group order 216 and the centre Z_3, the colourless content (1,0,0,1), the identities
(Gell-Mann–Okubo, equal spacing, the third difference, Coleman–Glashow, the vector spacing) and their PDG residuals
0.57 %, 9.2 %, 0.36 %, 0.79 %, 2.4 %, 0.42 %, the colour factor −8 and the spin pattern ∓3/4, the charge structure
and the coefficients 1/18, 1/36, the absolute spectrum within 1.1 %, the Λ–N gap 176.8 MeV, the Airy tower, the
baryon eigenvalue E_0 = 2.232 (4.6 %), the forward landings 0.855/0.442. An exception, a failed assert, a nonzero
exit or a failed predicate fails the family. Each family names the row(s) of the paper's predicate ledger it
witnesses (LEDGER; rows cited as 35:XN), and the ledger's source column cites the family ids in return.

Kinds, recorded per family: EXACT — finite-field (F_4), integer or exact-rational identities only, no float in the
script; MIXED — an exact core (the asserted identity) with a labelled [approx] decimal display of the PDG
confrontation, verdict on the exact core and on the stated residual by tolerance; PROFINITE — additionally a labelled
[profinite approx] finite-grid eigenvalue (numpy linear algebra over a finite matrix), verdict by stated tolerance;
CHART — the figure script (matplotlib rendering of the exact values).

Master-ledger rows of the corpus sourced from this paper: 00:I5 (the hadron spectrum: 35:C1–C10, C14), 00:I6 (the
residue series: 35:B1, B5, C15, C18), 00:I7 (the baryon scale: 35:C16, C17, C19).
"""
import io, json, os, re, sys, time, traceback, math
from fractions import Fraction as Fr

RESULTS = []
MICRO = []                    # (family, label, ok)
HERE = os.path.dirname(os.path.abspath(__file__))

# family -> paper rows witnessed
LEDGER = {
    "had.su3_singlet":            "35:B1, 35:C1, 35:X2",
    "had.carrier_residue":        "35:B5, 35:C15, 35:X1, 35:X3, 35:X7",
    "had.su3f_relations":         "35:C2, 35:C3, 35:P1, 35:P2, 35:X4, 35:X5",
    "had.su3f_second_order":      "35:C11, 35:C12, 35:P8",
    "had.hyperfine_charsum":      "35:C4, 35:C5, 35:C6, 35:P3, 35:X6",
    "had.isospin_cottingham":     "35:C7, 35:C8, 35:C9, 35:P6, 35:X8, 35:X9, 35:X10",
    "had.heavy_flavour":          "35:C10, 35:P7, 35:X11",
    "had.em_heavy_cmag":          "35:C13, 35:C14, 35:C21, 35:C22",
    "had.absolute_masses":        "35:P10",
    "had.vector_nonet":           "35:C18, 35:P9, 35:X12",
    "had.subhorizon_resolution":  "35:C20, 35:C23, 35:X13",
    "had.confinement_completion": "35:C16, 35:P11",
    "had.final_resolution":       "35:C16, 35:C20, 35:X13",
    "had.confinement_closure":    "35:C17",
    "had.forward_eigenvalues":    "35:C17, 35:C19",
    "had.make_figures":           "35:V2",
}

KIND = {f: "MIXED" for f in LEDGER}
for f in ("had.su3_singlet", "had.carrier_residue"):
    KIND[f] = "EXACT"
for f in ("had.confinement_completion", "had.final_resolution", "had.confinement_closure", "had.forward_eigenvalues"):
    KIND[f] = "PROFINITE"
KIND["had.make_figures"] = "CHART"

LABELS = {
    "had.su3_singlet": "colour SU(3,F_2) built exactly over F_4: order 216, centre the scalars {I, ωI, ω²I} ≅ Z_3; the colour-singlet rule is centre neutrality, triality 0 (mod 3) — the baryon qqq and the meson qq̄ colourless, the quark and the diquark confined; det = 1 on the group, so ε_abc is the invariant (Λ³3 = 1)",
    "had.carrier_residue": "the baryon as the Carrier residue 1: no nonzero colour vector fixed by SU(3,F_2) (the fundamental carries no invariant line: a single quark has residue 0), det ≡ 1 (Λ³ = det the one-dimensional invariant), the colourless content of Λ^k(3) is (1,0,0,1) for k = 0…3 — the residue series photon 2, gluon 0, baryon 1; stability selects the minimal-wrap proton",
    "had.su3f_relations": "Gell-Mann–Okubo 2N + 2Ξ − 3Λ − Σ = 0 and the decuplet second differences Δ − 2Σ* + Ξ* = Σ* − 2Ξ* + Ω = 0 as exact identities in the (M₀, a, b) / (α, β) bases (the scale and the breaking parameters cancel); PDG residual 0.57 % (octet), spacing spread 9.2 % with β = 146.8 MeV [approx]",
    "had.su3f_second_order": "the decuplet third-difference relation M_Δ − 3M_Σ* + 3M_Ξ* − M_Ω = 0 and the octet–decuplet hyperfine links M_Σ − M_Λ = ⅔[(M_Δ − M_N) − (M_Σ* − M_Σ)], M_Σ* − M_Σ = M_Ξ* − M_Ξ vanish identically in (M₀, d, A, r) (sympy); PDG third difference +6.0 MeV (0.36 %) [approx]",
    "had.hyperfine_charsum": "the colour factor of the singlet Σ λ_i·λ_j = −8 (−8/3 per pair) from C₂(3) = 4/3, C₂(1) = 0; the spin structure g_spin = ½S(S+1) − 9/8: octet −3/4, decuplet +3/4, separation 3/2; the combined colour × spin eigenvalues +2, −2; A_light = ⅔(M_Δ − M_N) = 195.4 MeV [approx]",
    "had.isospin_cottingham": "Coleman–Glashow (n−p) + (Ξ⁻−Ξ⁰) − (Σ⁻−Σ⁺) = 0 as an exact one-body identity; M_n > M_p from the d−u seed against the charge-squared term (ΣQ² = 1 for p, 2/3 for n); M_Σ > M_Λ from the ud pair spin-1 vs spin-0 (S_u·S_d difference 1, the strange-to-pair term −1); PDG 0.79 %, n − p = 1.293 MeV, Σ⁰ − Λ = 77.0 MeV [approx]",
    "had.heavy_flavour": "heavy-quark spin decoupling: M(Λ_b) − M(Λ_c) = 3333.1 against M(B) − M(D) = 3414.8 MeV (−2.4 %); the 1/m_Q hyperfine ratio (Σ_c* − Σ_c)/(Σ* − Σ) = 0.339 ≈ m_s/m_c [approx]",
    "had.em_heavy_cmag": "the electromagnetic charge structure exact (p: ΣQ² = 1, ΣQ_iQ_j = 0; n: 2/3, −1/3; both differences 1/3), the magnitude α√σ × structure, no new residue; the heavy absolute masses m_Q + O(√σ); c_mag the adjoint plaquette sum (8 ⊂ 3⊗3̄, 8 ⊄ 3⊗3), leading β²/36 against the tension β/18",
    "had.absolute_masses": "the absolute octet and decuplet from one scale and two ratios anchored to N, Λ, Δ (m_l = 361.8 MeV, m_s/m_l = 1.4885, v_ll/m_l = 0.540): five parameter-free predictions Σ, Ξ, Σ*, Ξ*, Ω all within 1.1 % of PDG [approx]",
    "had.vector_nonet": "the meson as residue 1 (B = 0): the unitary contraction of 3⊗3̄ on SU(3,F_2) (order 216); the vector equal spacing 2M_K* − M_ρ − M_φ = 0 exact in the linear-strangeness basis; PDG −0.42 %, K* predicted 897.4 (0.42 %), ω = ρ (−0.95 %) [approx]",
    "had.subhorizon_resolution": "the Ω-stability discriminator: the colour rank N = 3 on every admissible shell (3 | Ω+1 for Ω = 53, 173, 389, 1373), the character-sum coefficients 1/18 and 1/36 Ω-free; the second-order residuals O(ε_s²) — GMO 27-plet 0.017, third difference 0.041 of the leading splitting — a convergent expansion; A_light/√σ sub-horizon",
    "had.confinement_completion": "the single-scale reduction: λ_l = 0.822, m_s/m_l = 1.489, λ_hf = 0.444 at √σ = 440 MeV; M_Λ − M_N = m_s − m_l = 176.8 MeV exactly (the hyperfine cancels); the linear-potential tower on the finite grid (N = 4000) reproducing the Airy zeros 2.338, 4.088, 5.521, 6.787 [profinite approx]",
    "had.final_resolution": "the terminal classification: the two kinds of sub-horizon residue (closed-form framed-rational, profinite eigenvalue), the bound-state problem Ω-free (N = 3 on every shell, the character sums, the operator −u'' + xu), the level ratio ε₁/ε₀ = 1.7484; the tally six T rows and two Ω-hard (√σ, α), nothing open",
    "had.confinement_closure": "the baryon scale as a finite eigenvalue: H_G = T_G^{1/2} + R_G (the matrix square root by finite eigendecomposition) across the grid tower N = 600…2200, E₀ = 2.2322 converged, E₁/E₀ = 1.4917; M_N = E₀√σ = 982 MeV against 938.9 (4.6 %); λ_l = 0.822, λ_hf = 0.444 the constituent decomposition of {M_N, M_Δ} [profinite approx]",
    "had.forward_eigenvalues": "the forward evaluation with no measured baryon mass: [EXACT] g_spin ∓3/4, the 3/2 lever, c₁ = β/18, c_adj = β²/36, the spin split inverted exactly; [profinite approx] |u'(0)|² = 1 (the Airy normalisation identity), E₀ = 2.2323, F_rel = 3.52; [approx] α_s(√σ) ≈ 1 by transmutation, the landings λ_hf = 0.442 and λ_l = 0.855 within 7 % of 0.444/0.822 — the script's ten checks",
    "had.make_figures": "the paper's two figures regenerated into figures/ from the exact values of absolute_masses and vector_nonet (fig_spectrum.pdf: FRC vs PDG for the octet, decuplet and vector nonet; fig_strangeness.pdf: mass against strangeness, the two equal spacings)",
}

def script_of(fam):
    return fam.split(".")[1]            # had.<stem> runs <stem>.py

_CUR = [None]

def chk(label, ok):
    """A labelled micro-check, recorded under the running family."""
    ok = bool(ok)
    MICRO.append((_CUR[0], str(label), ok))
    print(("PASS " if ok else "FAIL ") + str(label))

class _Exit(Exception):
    def __init__(self, code): self.code = code

def _fig(name):
    """A file the figure script wrote into figures/ (it runs with figures/ as the working directory)."""
    return os.path.exists(os.path.join(HERE, "figures", name))

def _show_pngs(pngs):
    """Inside a notebook, display the PNG copies of the figures a script saved; a no-op under plain python."""
    try:
        from IPython.display import display, Image
        get_ipython()                                     # NameError outside IPython
    except Exception:
        return
    for p in pngs:
        display(Image(filename=p))

def _near(x, v, tol):
    return abs(float(x) - v) <= tol


# ----------------------------------------------------------------------------------------------------------------
# the registry's predicates: fam -> function(ns, out) making chk calls on the script's namespace / printed output
# ----------------------------------------------------------------------------------------------------------------
def _pred_singlet(ns, out):
    chk("|SU(3,F_2)| = 216 = q³(q³+1)(q²−1) at q = 2, built exhaustively over F_4", ns["order"] == 216 and len(ns["G"]) == 216)
    chk("the centre is the three scalars {I, ωI, ω²I} ≅ Z_3", len(ns["centre"]) == 3 and set(ns["centre"]) == set(ns["scalars"]))
    tr = ns["triality"]
    chk("triality: quark 1, diquark 2 (confined); baryon qqq, meson qq̄, antibaryon 0 (colour-singlet)", tr(1, 0) == 1 and tr(2, 0) == 2 and tr(3, 0) == 0 and tr(1, 1) == 0 and tr(0, 3) == 0)
    chk("det g = 1 for every g: ε_abc (Λ³3) is the invariant, the baryon the unique three-quark singlet", ns["inv"] is True)

def _pred_residue(ns, out):
    chk("|SU(3,F_2)| = 216 (the non-split colour frame)", len(ns["G"]) == 216)
    chk("no nonzero colour vector is fixed by the group: the fundamental carries no invariant line (a quark has residue 0)", len(ns["fixed"]) == 0)
    chk("det ≡ 1 on the group: Λ³(3) = det is the one-dimensional invariant, residue 1 (baryon number)", ns["all_det1"] is True)
    chk("the colourless content of Λ^k(3), k = 0…3, is (1, 0, 0, 1): vacuum, quark 0, diquark 0, baryon 1", ns["triv"] == [1, 0, 0, 1])

def _pred_su3f(ns, out):
    chk("Gell-Mann–Okubo 2N + 2Ξ − 3Λ − Σ = 0 identically in (M₀, a, b)", ns["zero_vec"](ns["gmo"]))
    chk("decuplet equal spacing: both second differences vanish identically in (α, β)", ns["zero_vec"](ns["d1"]) and ns["zero_vec"](ns["d2"]))
    chk(f"[approx] PDG octet residual {float(ns['res']) * 100:+.2f} % (the paper's 0.57 %)", _near(ns["res"] * 100, 0.57, 0.02))
    chk(f"[approx] decuplet spacing spread {float(ns['spread']) * 100:.1f} % (9.2 %), β = {float(ns['mean']):.1f} MeV (146.8)", _near(ns["spread"] * 100, 9.2, 0.1) and _near(ns["mean"], 146.8, 0.1))

def _pred_second(ns, out):
    chk("the third difference M_Δ − 3M_Σ* + 3M_Ξ* − M_Ω vanishes identically in (M₀, d, A, r)", ns["third"] == 0)
    chk("the two octet–decuplet hyperfine links vanish identically", ns["rel1"] == 0 and ns["rel2"] == 0)
    tp = float(ns["third_pdg"]); scale = float(ns["mD"] + ns["mO"]) / 2
    chk(f"[approx] PDG third difference {tp:+.1f} MeV ({tp / scale * 100:.2f} % of the scale; the paper's 6 MeV, 0.36 %)", _near(tp, 6.0, 0.2))
    chk(f"[approx] the hyperfine links hold to ~12 %: {float(ns['lhs1']):.1f} vs {float(ns['rhs1']):.1f}, {float(ns['lhs2']):.1f} vs {float(ns['rhs2']):.1f} MeV", abs(float(ns["lhs1"] / ns["rhs1"]) - 1) < 0.15 and abs(float(ns["lhs2"] / ns["rhs2"]) - 1) < 0.15)

def _pred_hyperfine(ns, out):
    chk("the colour factor Σ λ_i·λ_j = −8, −8/3 per pair, from C₂(3) = 4/3 and C₂(1) = 0", ns["sum_ll"] == -8 and ns["per_pair_ll"] == Fr(-8, 3) and ns["C2f"] == Fr(4, 3))
    chk("g_spin = ½S(S+1) − 9/8: octet −3/4, decuplet +3/4, separation 3/2", ns["g_oct"] == Fr(-3, 4) and ns["g_dec"] == Fr(3, 4) and ns["sep_coeff"] == Fr(3, 2))
    chk("the combined colour × spin eigenvalues +2 (octet), −2 (decuplet): M₁₀ − M₈ = (3/2) A_light", ns["ev_oct"] == 2 and ns["ev_dec"] == -2)
    chk(f"[approx] A_light = ⅔(M_Δ − M_N) = {float(ns['A_light']):.1f} MeV (195)", _near(ns["A_light"], 195.4, 0.2))

def _pred_isospin(ns, out):
    chk("Coleman–Glashow (n−p) + (Ξ⁻−Ξ⁰) − (Σ⁻−Σ⁺) = 0 identically in the one-body δ", ns["zero"](ns["cg"]))
    chk("Σ–Λ: the ud pair S_u·S_d difference +1 (spin-1 vs spin-0), the strange-to-pair term −1: M_Σ − M_Λ = a_ll − a_ls > 0", ns["SuSd_S"] - ns["SuSd_L"] == 1 and ns["SsPair_S"] - ns["SsPair_L"] == -1)
    r = float((ns["lhs"] - ns["rhs"]) / ns["rhs"]) * 100
    chk(f"[approx] PDG Coleman–Glashow residual {r:+.2f} % (0.79 %)", _near(r, 0.79, 0.02))
    chk(f"[approx] n − p = {float(ns['n'] - ns['p']):.3f} MeV > 0 and Σ⁰ − Λ = {float(ns['S0'] - ns['L']):.1f} MeV > 0", ns["n"] > ns["p"] and ns["S0"] > ns["L"])

def _pred_heavy(ns, out):
    r = float((ns["bar"] - ns["mes"]) / ns["mes"]) * 100
    chk(f"[approx] M(Λ_b) − M(Λ_c) = {float(ns['bar']):.1f} vs M(B) − M(D) = {float(ns['mes']):.1f} MeV: {r:+.1f} % (−2.4 %)", _near(r, -2.4, 0.1))
    q = float(ns["heavy_hf"] / ns["light_hf"])
    chk(f"[approx] the 1/m_Q hyperfine ratio (Σ_c* − Σ_c)/(Σ* − Σ) = {q:.3f} ≈ m_s/m_c (~0.33)", _near(q, 0.339, 0.005))

def _pred_em(ns, out):
    ob, tb, p, n = ns["one_body"], ns["two_body"], ns["p"], ns["n"]
    chk("the charge structure exact: p (ΣQ², ΣQ_iQ_j) = (1, 0), n = (2/3, −1/3)", ob(p) == 1 and tb(p) == 0 and ob(n) == Fr(2, 3) and tb(n) == Fr(-1, 3))
    chk("both differences p − n equal 1/3: the electromagnetic term makes the proton heavier", ob(p) - ob(n) == Fr(1, 3) and tb(p) - tb(n) == Fr(1, 3))
    chk("the leading coefficients: tension c₁ = β/18 (fundamental), colour-magnetic c_adj = β²/36 (adjoint, one order finer)", ns["c1_lead"] == Fr(1, 18) and ns["c_adj_lead_coeff"] == Fr(1, 36))
    chk("the adjoint 8 sits in 3⊗3̄ = 1⊕8 and not in 3⊗3 = 6⊕3̄ (dimension counts 9 = 9)", "adjoint 8 absent" in out and "adjoint 8 present" in out)

def _pred_absolute(ns, out):
    m, P = ns["mass"], ns["PDG"]
    chk("the three anchors N, Λ, Δ reproduced exactly", all(m(t) == P[t] for t in ("N", "Lam", "Del")))
    chk(f"the ratios m_s/m_l = {float(ns['m_s'] / ns['m_l']):.4f} (1.4885), v_ll/m_l = {float(ns['v_ll'] / ns['m_l']):.4f} (0.540), m_l = {float(ns['m_l']):.1f} MeV", _near(ns["m_s"] / ns["m_l"], 1.4885, 5e-4) and _near(ns["v_ll"] / ns["m_l"], 0.540, 1e-3) and _near(ns["m_l"], 361.8, 0.1))
    dev = {t: float((m(t) - P[t]) / P[t]) * 100 for t in ("Sig", "Xi", "Sgs", "Xis", "Om")}
    chk(f"[approx] five parameter-free predictions within 1.1 %: max |Δ| = {ns['maxabs']:.2f} % ({', '.join(f'{k} {v:+.2f}' for k, v in dev.items())})", ns["maxabs"] < 1.15 and all(abs(v) < 1.15 for v in dev.values()))

def _pred_vector(ns, out):
    chk("|SU(3,F_2)| = 216; the q q̄ singlet is the unitary contraction of 3⊗3̄ (triality 0, B = 0, residue 1)", len(ns["G"]) == 216)
    chk("2M_K* − M_ρ − M_φ = 0 identically in the linear-strangeness basis (a, b)", all(x == 0 for x in ns["eq"]))
    r = float((ns["lhs"] - ns["rhs"]) / ns["rhs"]) * 100
    chk(f"[approx] PDG 2M_K* vs M_ρ + M_φ: {r:+.2f} % (−0.42 %)", _near(r, -0.42, 0.02))
    pr = ns["pred"]
    dk = float((pr["K*"][0] - pr["K*"][1]) / pr["K*"][1]) * 100; do = float((pr["omega"][0] - pr["omega"][1]) / pr["omega"][1]) * 100
    chk(f"[approx] K* predicted {float(pr['K*'][0]):.1f} MeV ({dk:+.2f} %), ω = ρ ({do:+.2f} %): both under 1 %", abs(dk) < 1 and abs(do) < 1 and _near(pr["K*"][0], 897.4, 0.1))

def _pred_subhorizon(ns, out):
    chk("Ω ≡ 5 (mod 12) and 3 | Ω+1 on every listed shell (53, 173, 389, 1373): the colour rank N = 3 is Ω-independent", all(o % 12 == 5 and (o + 1) % 3 == 0 for o in ns["shells"]) and ns["shells"] == [53, 173, 389, 1373])
    chk("the character-sum coefficients at N = 3: 1/18 and 1/36, functions of N only", ns["c1_lead"](3) == Fr(1, 18) and ns["cadj_lead"](3) == Fr(1, 36))
    chk(f"[approx] the second-order residuals are O(ε_s²): GMO 27-plet {ns['r_gmo']:.3f}, third difference {ns['r_third']:.3f} of the leading splitting (0.017, 0.041; ε_s ~ 0.2)", _near(ns["r_gmo"], 0.017, 0.002) and _near(ns["r_third"], 0.041, 0.002))

def _pred_completion(ns, out):
    chk(f"M_Λ − M_N = m_s − m_l exactly (Fraction identity), {float(ns['gap']):.1f} MeV (176.8)", ns["gap"] == ns["m_s"] - ns["m_l"] and _near(ns["gap"], 176.8, 0.05))
    ss = ns["sqrt_sigma"]
    chk(f"the ratios at √σ = 440 MeV: λ_l = {float(ns['m_l'] / ss):.3f} (0.822), m_s/m_l = {float(ns['m_s'] / ns['m_l']):.3f} (1.489), λ_hf = {float(ns['v_ll'] / ss):.3f} (0.444)", _near(ns["m_l"] / ss, 0.822, 1e-3) and _near(ns["m_s"] / ns["m_l"], 1.489, 1e-3) and _near(ns["v_ll"] / ss, 0.444, 1e-3))
    eps = ns["eps"]; airy = (2.33811, 4.08795, 5.52056, 6.78671)
    chk(f"[profinite approx] the finite-grid tower ε₀…ε₃ = {', '.join(f'{e:.4f}' for e in eps)} against the Airy zeros within 2 × 10⁻³", all(abs(float(e) - a) < 2e-3 for e, a in zip(eps, airy)))

def _pred_final(ns, out):
    chk("the bound-state inputs are Ω-free: N = 3 on every listed shell", all(o % 12 == 5 and (o + 1) % 3 == 0 for o in ns["shells"]))
    m = re.search(r"eps_1/eps_0 = ([0-9.]+)", out)
    chk(f"[profinite approx] the level ratio ε₁/ε₀ = {m.group(1) if m else '?'} (1.7484, scale-free)", m is not None and _near(m.group(1), 1.7484, 1e-3))
    rows = ns["rows"]
    chk("the tally: six sub-horizon T rows and two Ω-hard (√σ, α), nothing open", sum(t.startswith("T") for _, t in rows) == 6 and sum(t.startswith("Omega") for _, t in rows) == 2 and len(rows) == 8)

def _pred_closure(ns, out):
    E0, E1 = ns["E0"], ns["E1"]
    chk(f"[profinite approx] E₀ = {E0:.4f} converged across the tower (2.2322), E₁/E₀ = {E1 / E0:.4f} (1.4917)", _near(E0, 2.2322, 1e-3) and _near(E1 / E0, 1.4917, 1e-3))
    ratio = ns["MN"] / ns["sqsig"]
    chk(f"[approx] M_N = E₀√σ = {ns['MN_pred']:.0f} MeV at √σ = 440 against 938.9: {abs(E0 - ratio) / ratio * 100:.1f} % (4.6 %)", _near(ns["MN_pred"], 982, 1) and _near(abs(E0 - ratio) / ratio * 100, 4.6, 0.1))
    chk(f"λ_l = {float(ns['lam_l']):.3f} (0.822), λ_hf = {float(ns['lam_hf']):.3f} (0.444), v_ll/m_l = {float(ns['v_ll'] / ns['m_l']):.3f} (0.540)", _near(ns["lam_l"], 0.822, 1e-3) and _near(ns["lam_hf"], 0.444, 1e-3) and _near(ns["v_ll"] / ns["m_l"], 0.540, 1e-3))

def _pred_forward(ns, out):
    chk(f"the script's own tally: {ns['n']}/{ns['tot']} checks pass", ns["n"] == ns["tot"] == 10)
    chk(f"[profinite approx] |u'(0)|² = {ns['cn']:.4f} → 1 (Airy identity), E₀ = {ns['e0r']:.4f} (2.232), F_rel = {ns['Frel']:.3f} (3.52)", ns["NUMPY"] and _near(ns["cn"], 1.0, 2e-3) and _near(ns["e0r"], 2.2323, 1e-3) and _near(ns["Frel"], 3.52, 0.01))
    chk(f"[approx] the forward λ_l = {ns['ll_fwd']:.3f} (0.855, target 0.822)", _near(ns["ll_fwd"], 0.855, 2e-3))

def _pred_figures(ns, out):
    chk("fig_spectrum.pdf (and .png) regenerated in figures/", _fig("fig_spectrum.pdf") and _fig("fig_spectrum.png"))
    chk("fig_strangeness.pdf (and .png) regenerated in figures/", _fig("fig_strangeness.pdf") and _fig("fig_strangeness.png"))

PRED = {
    "had.su3_singlet": _pred_singlet, "had.carrier_residue": _pred_residue, "had.su3f_relations": _pred_su3f,
    "had.su3f_second_order": _pred_second, "had.hyperfine_charsum": _pred_hyperfine, "had.isospin_cottingham": _pred_isospin,
    "had.heavy_flavour": _pred_heavy, "had.em_heavy_cmag": _pred_em, "had.absolute_masses": _pred_absolute,
    "had.vector_nonet": _pred_vector, "had.subhorizon_resolution": _pred_subhorizon, "had.confinement_completion": _pred_completion,
    "had.final_resolution": _pred_final, "had.confinement_closure": _pred_closure, "had.forward_eigenvalues": _pred_forward,
    "had.make_figures": _pred_figures,
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
            elif re.match(r"^(\[?(PASS|FAIL|OK|XX)\]?(?![A-Za-z])|\[EXACT\])", t):     # a script's per-check verdict line
                verdicts.append(t[:6].find("PASS") >= 0 or t[:4].find("OK") >= 0 or t.startswith("[EXACT]"))
    def _exit(code=0):
        raise _Exit(code)
    g = {"__name__": "__main__", "__file__": path, "print": _print, "__exit__": _exit}
    pngs = []                                            # every figure a script saves gets a PNG sibling (shown inline in the notebook)
    _savefig = None
    if fam == "had.make_figures":
        import matplotlib; matplotlib.use("Agg")
        from matplotlib.figure import Figure
        _savefig = Figure.savefig
        def _savefig_png(fig, fname, *a, **kw):
            _savefig(fig, fname, *a, **kw)
            if isinstance(fname, (str, os.PathLike)):
                png = os.path.splitext(os.fspath(fname))[0] + ".png"
                _savefig(fig, png, dpi=130, bbox_inches="tight"); pngs.append(os.path.abspath(png))
        Figure.savefig = _savefig_png
    _CUR[0] = fam
    n0 = len(MICRO)
    t0 = time.time(); code = 0; err = None
    FIG = os.path.join(HERE, "figures"); os.makedirs(FIG, exist_ok=True)
    old = os.getcwd(); os.chdir(FIG if fam == "had.make_figures" else HERE); sys.path.insert(0, HERE)
    # forward_eigenvalues guards its own imports (assert "random" not in sys.modules); under the registry the process
    # may already hold the module through matplotlib/IPython, so it is set aside for the script's run and restored after.
    held = {m: sys.modules.pop(m) for m in ("random",) if m in sys.modules}
    try:
        exec(compile(src, path, "exec"), g)
    except _Exit as e:
        code = e.code if isinstance(e.code, int) else (0 if e.code in (None, 0) else 1)
    except Exception:
        err = traceback.format_exc().strip().splitlines()[-1]
        print("    EXCEPTION: " + err)
    finally:
        os.chdir(old)
        sys.modules.update(held)
        if _savefig is not None:
            from matplotlib.figure import Figure
            Figure.savefig = _savefig
            import matplotlib.pyplot as plt; plt.close("all")
    _show_pngs(pngs)
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
    print(f"  [{'PASS' if ok else 'FAIL'}] {pid:26s} {kind:9s} [{rows}] {label[:90]}" + (f"  --  {detail}" if detail else ""))
    return ok

def summary(write=True):
    n_ok = sum(r["ok"] for r in RESULTS)
    print(f"\nSUMMARY: {n_ok}/{len(RESULTS)} checks passed ({len(MICRO)} micro-checks)" + ("" if n_ok == len(RESULTS) else "  <-- FAILURES"))
    if write:
        with open(os.path.join(HERE, "results.json"), "w") as f:
            json.dump(RESULTS, f, indent=1, ensure_ascii=False)
    return n_ok == len(RESULTS)
