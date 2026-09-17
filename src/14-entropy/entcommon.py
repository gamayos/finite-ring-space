"""
entcommon.py — shared registry for the 14-entropy validation package
=====================================================================
"De Sitter Entropy Estimates over Finite Holographic Substrate" (Akhtman & Voether, 2026), validation package of the
FRC corpus (finite-ring-space/src/14-entropy). Two kinds of check: EXACT — integer counts on the instantiated
laboratory Carrier Ω = 2 408 561 (the admissibility congruences, the quarter identity, the octant count); CHART — a
one-line computation on published [approx] or [ΛCDM] data (the instrument table, the concordances, the audit
identities, the locus, the confrontations, the triangle's regression), reproduced to the precision the paper quotes.
No fitting of framework parameters and no random sampling anywhere; transcendental library calls (sqrt, atanh, tanh,
pi) are the labelled chart functions applied to chart quantities.

A check of the registry is a *family* of micro-checks — one labelled claim of a script (est.C1, tri.D, cap.K, …) —
and names the row(s) of the paper's predicate ledger it witnesses (LEDGER; rows cited as 14:XN). The ledger's source
column cites these check ids in return. Master-ledger rows reached through the paper rows: 00:A9 (14:A1, 14:A2),
00:L2 (14:C4, 14:B5, 14:Z1), 00:L3 (14:C5, 14:C7, 14:P2, 14:P3, 14:P4), 00:L4 (14:C9), 00:L5 (14:B9), 00:L6 (14:X8),
00:L7 (14:P1, 14:B4), 00:L1 (14:X2, 14:A6), 00:F7 (the additive window, 14:B10; formerly Y6).
"""
import os, json, sys
from collections import OrderedDict

RESULTS = []
MICRO = []             # (script tag, family, label, ok)

LEDGER = {
    # estimate_S.py
    "est.F1": "14:A2, 14:C6",
    "est.B9": "14:B9",
    "est.T1": "14:C1, 14:C4",
    "est.C1": "14:C4",
    "est.C2": "14:C8",
    "est.A1": "14:C3, 14:C7, 14:X3, 14:X6",
    "est.C3": "14:C8",
    "est.P3": "14:P3",
    "est.C4": "14:C4, 14:C7",
    "est.L1": "14:X2",
    "est.P2": "14:C5, 14:P2",
    "est.P1": "14:P1",
    # triangle.py (make-wedge-2)
    "tri.A": "14:C5, 14:C8, 14:C9",
    "tri.D": "14:C9, 14:X5",
    "tri.W": "14:C9",
    "tri.F": "14:V2",
    # capacity.py (make-wedge-3)
    "cap.A": "14:C9",
    "cap.K": "14:C10",
    "cap.F": "14:V2",
}

LABELS = {
    "est.F1": "the exact faces on the laboratory Carrier Ω = 2 408 561 (S = 602 140): Ω = 4S + 1, S even (the octant sector Z₈ exists), S ≡ 1 (mod 3), 4S + 1 prime, the octant count S/2 an integer — integer arithmetic, deterministic trial division",
    "est.B9": "the area law: the quarter identity 4S = Ω − 1 and the quarter-turn chain (4 | Ω − 1; the hydrogen shell q_H = 4κ_H + 1 = 13, prime) as counts; the chart face 4π n_A = 4S(r_H), n_A = (r_H/ℓ_P)², to 10⁻¹² [approx]",
    "est.T1": "the instrument table reproduced from the four public data and the laboratory constants: r_H = 1.66, 1.27, 1.33, 1.19, 1.29, 1.64 × 10²⁶ m, S = 3.3, 1.9, 2.1, 1.7, 2.0, 3.2 × 10¹²², σ_√S = 1, 1.4, 2.4, 20, 2.5, 2.5 % for rows 1, 2a, 2b, 3, 4a, 4b [approx]",
    "est.C1": "the two-face concordance over the five evidence readings (gauge row 4a excluded): √S = (1.3–1.8) × 10⁶¹, ±17 % half-range on the count face, a factor 1.9 on S; the conventional channels alone ±14 %, factor 1.7 [approx]",
    "est.C2": "the chart identity S_Λ/S_rate = (H_rate/H₀)²/Ω_Λ verified per ladder row to 0.2 % — the definition of Ω_Λ read on the rows; the cluster excess 1.68 against 1/Ω_Λ = 1.46 [ΛCDM]",
    "est.A1": "the circularity audit: t₀H_Λ = (2/3) artanh √Ω_Λ = 0.7871 at the fitted Ω_Λ = 0.685, within 0.2 % of π/4; the inversion π/4 ↦ Ω_Λ = tanh²(3π/8) = 0.6837, a 0.19σ landing on 0.685 ± 0.007 [ΛCDM]",
    "est.C3": "the channel-1 consistency: H_Λ = 55.7 km/s/Mpc from the fit's Λ (1/H_Λ = 17.55 Gyr), and the locus returns H₀ = H_Λ/tanh(3π/8) = 67.4, the fit's own value to 0.1 % [ΛCDM]",
    "est.P3": "the age–rate locus t_age H₀ = (π/4)/tanh(3π/8) = 0.950 (flat ΛCDM 0.951 at the fitted Ω_Λ); read on t⋆ = 13.61 ± 0.34 Gyr: H₀ = 68.2 ± 1.7 km/s/Mpc, 0.5σ from Planck, 0.65σ from TRGB, 2.4σ from the Cepheid ladder; the ladder pair (13.61 Gyr, 73) has t⋆H₀ = 1.016 [approx]",
    "est.C4": "the one-face concordance: rate rows carried to the Λ face by c/(H tanh(3π/8)) — r_H^Λ = 1.66, 1.53, 1.60, 1.44, 1.64 × 10²⁶ m — agree to ±7 % half-range over five readings and ±4 % over the conventional channels; the ladder–row-1 residual ≈ 8 % [approx]",
    "est.L1": "the floor landing cH₀/a₀ = 5.46 ± 1.1 at H₀ = 67.4, 0.8σ from 2π [approx]",
    "est.P2": "the octant bound (π/4) r_H/c = 13.79 Gyr at the channel-1 Λ, degenerate with the ΛCDM t₀ = 13.80 to 0.2 %; the oldest cluster population 13.61 ± 0.34 Gyr 0.5σ below the bound, the prior-dependent inferred age 13.81 straddling it within 0.1σ [ΛCDM]",
    "est.P1": "the running floor against Ciocan et al.: on the ∝ H(z) chord a₀(z = 1) = 2.15 × 10⁻¹⁰ (E(1) = 1.79), 0.5σ from the measured 2.38 ± 0.10 with the anchor's systematic band; the fitted linear rate 1.59 ± 0.10 exceeds the chord's 0.95 per unit redshift by ≈ 3σ before systematics [ΛCDM]",
    "tri.A": "the triangle's audit identities before drawing: the octant t_oct = (√π/4)√S t_P to 10⁻¹²; the two-cluster ratio 1.71 on S; the r_H split 1/√Ω_Λ = 1.208; H₀ = H_Λ/tanh(3π/8) = 67.4; the width identity log₁₀(r_H/ℓ_P) = log₁₀ √(S/π) exact [approx]",
    "tri.D": "the diagonal: ordinary least squares over the thirteen mid-triangle objects gives k = 3.032 with intercept 1.00 × 10³ at the metre pivot; the constrained k = 3 cubic coefficient c̃ = m/R³ = 0.97 × 10³ kg/m³ (not a density: a sphere's is 0.62 dex lower); the fifteen-object sensitivity k = 3.007; the Schwarzschild exit 1.8 × 10⁸ M☉ within the (1.4–2.8) × 10⁸ band across the four fit variants [approx]",
    "tri.W": "the wall residents and the slope decomposition: the electron on the Compton wall and Sgr A* on the Schwarzschild wall to < 0.01 dex; k = 3 + dc/d log R with mean c = 2.99 and drift 0.61 dex over the 19-decade baseline; the Compton entry 5.3 × 10⁻¹² m [approx]",
    "tri.F": "the figures written: the registrable triangle (with and without the channel inset) and the standalone wall-channels figure (Figure 3 of the paper)",
    "cap.A": "the audit and diagonal identities re-asserted in the capacity-axis variant (identical to tri.A, tri.D, tri.W)",
    "cap.K": "the capacity axis: the mass-axis pin (−45, 62) held after all children (no datalim drift); the one-gram horizontal lands on N_A = 6.022 × 10²³ hydrogen units to 0.0035 dex (tolerance 0.005) [approx]",
    "cap.F": "the figure written: the registrable triangle with the holographic-ring-capacity axis (Figure 4 of the paper)",
}

SCRIPT = {"est": "estimate_S", "tri": "triangle", "cap": "capacity"}
_FAM = [None, None]

def family(tag, fam):
    _FAM[0], _FAM[1] = tag, fam

def chk(label, ok, tag=None, fam=None):
    """A micro-check, recorded under the current (tag, family); never exits."""
    MICRO.append((tag or _FAM[0], fam or _FAM[1], label, bool(ok)))
    if not ok:
        print(f"    FAIL: {label}")

def flush(tag, order=None, details=None, kinds=None):
    fams = OrderedDict()
    for t, fam, label, ok in MICRO:
        if t == tag:
            fams.setdefault(fam, []).append(ok)
    for fam in (order or fams):
        oks = fams.get(fam, [])
        d = f"{len(oks)} micro-checks"
        if details and fam in details:
            d += "; " + details[fam]
        check(f"{tag}.{fam}", ok=bool(oks) and all(oks), detail=d, kind=(kinds or {}).get(fam, "CHART"))

def check(pid, ok, detail="", kind="CHART", label=None):
    ok = bool(ok)
    rows = LEDGER.get(pid, "")
    label = label or LABELS.get(pid, pid)
    RESULTS.append({"id": pid, "rows": rows, "script": SCRIPT.get(pid.split(".")[0], pid.split(".")[0]), "label": label, "ok": ok, "detail": detail, "kind": kind})
    print(f"  [{'PASS' if ok else 'FAIL'}] {pid:7s} {kind:11s} [{rows}] {label[:100]}" + (f"  --  {detail}" if detail else ""))
    return ok

def summary(write=True):
    n_ok = sum(r["ok"] for r in RESULTS)
    print(f"\nSUMMARY: {n_ok}/{len(RESULTS)} checks passed ({len(MICRO)} micro-checks)" + ("" if n_ok == len(RESULTS) else "  <-- FAILURES"))
    if write:
        with open("results.json", "w") as f:
            json.dump(RESULTS, f, indent=1, ensure_ascii=False)
    return n_ok == len(RESULTS)
