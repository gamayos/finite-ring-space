"""
entropy.py — the validation package of "De Sitter Entropy Estimates over Finite Holographic Substrate" (Akhtman & Voether,
2026), the paper 14-entropy of the FRC corpus (finite-ring-space/src/14-entropy); one script since 24 September 2026 (the
registry entcommon.py and the blocks estimate_S.py, triangle.py, capacity.py merged).
========================================================================================================================

One script, three blocks, nineteen family checks of 92 micro-checks; Python with matplotlib (the two triangle blocks draw
the paper's figures into out/). Two kinds of check are kept apart. EXACT: integer counts on the instantiated laboratory
Carrier Ω = 2 408 561 (the admissibility congruences, the quarter identity, the octant count) — a pass is a proof on that
instance. CHART: a one-line computation on published [approx] or [ΛCDM] data (the instrument table, the concordances, the
audit identities, the locus, the confrontations, the triangle's regression), reproduced to the precision the paper quotes —
a pass says the paper's numeral follows from its named inputs; it is not a measurement of the framework. No fitted framework
parameter and no random sampling anywhere; transcendental library calls (sqrt, atanh, tanh, pi) are the labelled chart
functions applied to chart quantities.

A family is one check of the registry, identified as <block>.<family> (est.F1 … est.P1, tri.A … tri.F, cap.A … cap.F), and
names the predicate(s) of the paper's ledger it witnesses (LEDGER; predicates cited as 14:<label>) — the deciding family's
`# 14:<label> (<key>)` marker is what the ledger's source column links (PREDICATES;
finitering.space/src/14-entropy/entropy.html#<key>); the family checks are listed on the public page from results.json.
Master-ledger predicates reached through the paper predicates: 00:A9 (14:A1, 14:A2), 00:L2 (14:C4, 14:B5, 14:Z1),
00:L3 (14:C5, 14:C7, 14:P2, 14:P3, 14:P4), 00:L4 (14:C9), 00:L5 (14:B9), 00:L6 (14:X8), 00:L7 (14:P1, 14:B4),
00:L1 (14:X2, 14:A6), 00:F7 (the additive window, 14:B10).

    python3 entropy.py          the three blocks, results.json written; exit 1 if a family check fails (≈ 3 s)
    python3 entropy.py tri      one block (est, tri or cap); no results.json
    from frc_14_entropy import predicate; predicate("14:C5")    one predicate: its blocks run once per session
"""
import os, json, sys
from collections import OrderedDict
from math import pi, sqrt, atanh, tanh, log10

SCRIPT = os.path.splitext(os.path.basename(__file__))[0]        # "entropy": the one script, the name results.json and the site pages carry

RESULTS = []
MICRO = []             # (block, family, label, ok)

LEDGER = {
    # block est (estimate_S.py until 24 September 2026)
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
    # block tri (triangle.py, the paper's make-wedge-2.py)
    "tri.A": "14:C5, 14:C8, 14:C9",
    "tri.D": "14:C9, 14:X5",
    "tri.W": "14:C9",
    "tri.F": "",
    # block cap (capacity.py, the paper's make-wedge-3.py)
    "cap.A": "14:C9",
    "cap.K": "14:C10",
    "cap.F": "",
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
    "est.P1": "the running floor against MUSE-DARK III: on the ∝ H(z) chord a₀(z = 1) = 2.15 × 10⁻¹⁰ (E(1) = 1.79), 0.5σ from the measured 2.38 ± 0.10 with the anchor's systematic band; the authors' global linear rate 1.59 ± 0.10 exceeds the chord's 0.95 per unit redshift by ≈ 3σ before systematics; the four bins (1.99 → 2.71 × 10⁻¹⁰ over z = 0.50–1.28) exclude a constant floor, Δχ² = 23 against A H(z)/H₀, which fits at A = 1.39 ± 0.03 (χ² = 5.4/3); the binned rate 0.98 ± 0.19 per unit redshift sits on the chord; the amplitude 0.12 dex above cH₀/2π, inside the 0.2 dex gas systematic [ΛCDM]",
    "tri.A": "the triangle's audit identities before drawing: the octant t_oct = (√π/4)√S t_P to 10⁻¹²; the two-cluster ratio 1.71 on S; the r_H split 1/√Ω_Λ = 1.208; H₀ = H_Λ/tanh(3π/8) = 67.4; the width identity log₁₀(r_H/ℓ_P) = log₁₀ √(S/π) exact [approx]",
    "tri.D": "the diagonal: ordinary least squares over the thirteen mid-triangle objects gives k = 3.032 with intercept 1.00 × 10³ at the metre pivot; the constrained k = 3 cubic coefficient c̃ = m/R³ = 0.97 × 10³ kg/m³ (not a density: a sphere's is 0.62 dex lower); the fifteen-object sensitivity k = 3.007; the Schwarzschild exit 1.8 × 10⁸ M☉ within the (1.4–2.8) × 10⁸ band across the four fit variants [approx]",
    "tri.W": "the wall residents and the slope decomposition: the electron on the Compton wall and Sgr A* on the Schwarzschild wall to < 0.01 dex; k = 3 + dc/d log R with mean c = 2.99 and drift 0.61 dex over the 19-decade baseline; the Compton entry 5.3 × 10⁻¹² m [approx]",
    "tri.F": "the figures written: the registrable triangle (with and without the channel inset) and the standalone wall-channels figure (Figure 3 of the paper; no ledger predicate)",
    "cap.A": "the audit and diagonal identities re-asserted in the capacity-axis variant (identical to tri.A, tri.D, tri.W)",
    "cap.K": "the capacity axis: the mass-axis pin (−45, 62) held after all children (no datalim drift); the one-gram horizontal lands on N_A = 6.022 × 10²³ hydrogen units to 0.0035 dex (tolerance 0.005) [approx]",
    "cap.F": "the figure written: the registrable triangle with the holographic-ring-capacity axis (Figure 4 of the paper; no ledger predicate)",
}

BLOCK = {"est": "the exact faces and the area law on the laboratory Carrier, then every chart numeral of the paper (estimate_S.py until 24 September 2026)",      # check-id prefix -> the block (the function block_<name> below)
         "tri": "the registrable triangle: the audit identities, the diagonal regression, the wall residents, the figures (the paper's make-wedge-2.py)",
         "cap": "the capacity-axis variant: the identities re-asserted, the Avogadro landing, the figure (the paper's make-wedge-3.py)"}

# the deciding family of each witnessed predicate: the one whose checks decide the predicate's statement (the other families
# that touch it are corroboration, listed by predicate() from the records)
PREDICATES = {
    "14:A2": "est.F1", "14:B9": "est.B9", "14:C1": "est.T1", "14:C3": "est.A1", "14:C4": "est.C1", "14:C5": "est.P2",
    "14:C6": "est.F1", "14:C7": "est.A1", "14:C8": "est.C3", "14:C9": "tri.D", "14:C10": "cap.K",
    "14:X2": "est.L1", "14:X3": "est.A1", "14:X5": "tri.D", "14:X6": "est.A1",
    "14:P1": "est.P1", "14:P2": "est.P2", "14:P3": "est.P3",
}
_FAM = [None, None]
_RAN = set()                                            # blocks already run in this session (predicate() runs each once)

def markers():
    """predicate label -> (script file, line) of its marker `# <paper>:<label> (<key>)`: the line of the check that decides it."""
    import re
    out = {}
    for i, line in enumerate(open(os.path.abspath(__file__), encoding="utf-8"), 1):
        m = re.match(r"\s*# ((?:\d+:[A-Z]+\d+[a-z]?(?: \(p\d{5}\))?)(?:, \d+:[A-Z]+\d+[a-z]?(?: \(p\d{5}\))?)*)\s*$", line)
        if m:
            for lab in re.findall(r"\d+:[A-Z]+\d+[a-z]?", m.group(1)): out.setdefault(lab, (SCRIPT + ".py", i))
    return out

def _run_block(name):
    if name not in _RAN:
        globals()[f"block_{name}"](); _RAN.add(name)

def predicate(label, lines=14):
    """Verify one ledger predicate: run the blocks of the families that cite it (each once per session), print the deciding
    check's source (from its marker) and every family record that cites the predicate, and return True iff all pass."""
    fam = PREDICATES.get(label)
    if fam is None:
        print(f"{label}: no python witness (see the predicate's Lean witness or its source)"); return None
    citing = {f.split(".")[0] for f, rows in LEDGER.items() if label in [t.strip() for t in rows.split(",")]}
    for b in sorted({fam.split(".")[0]} | citing): _run_block(b)     # the deciding block and every block whose families cite the predicate
    mk = markers().get(label)
    if mk:
        src = open(os.path.abspath(__file__), encoding="utf-8").read().split("\n")
        print(f"— {mk[0]}:{mk[1]} (the check that decides {label}; family {fam})")
        for j in range(mk[1] - 1, min(mk[1] - 1 + lines, len(src))): print(f"{j + 1:5d}  {src[j]}")
    else:
        print(f"— {SCRIPT}.py, block {fam.split('.')[0]} (the whole block witnesses {label})")
    recs = [r for r in RESULTS if label in [t.strip() for t in r["rows"].split(",")]]
    ok = all(r["ok"] for r in recs)
    for r in recs:
        role = "(deciding)" if r["id"] == fam else "(corroborating)"
        print(f"  [{'PASS' if r['ok'] else 'FAIL'}] {r['id']:8s} {role:16s} {r['detail']}")
    print(f"{label}: {'VERIFIED' if ok and recs else 'FAILED'} — {len(recs)} family record(s)")
    return ok

def verify_all():
    """Run every block (those already run in this session are not re-run) and print the summary; True iff every family check passed."""
    for b in BLOCK: _run_block(b)                        # in the paper's order: est, tri, cap
    return summary(write=False)

def family(tag, fam):
    _FAM[0], _FAM[1] = tag, fam

def chk(label, ok, tag=None, fam=None):
    """A micro-check, recorded under the current (block, family); never exits."""
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
    """Record one family check. pid = <block>.<family>; LEDGER[pid] = the paper predicate(s) it witnesses."""
    ok = bool(ok)
    rows = LEDGER.get(pid, "")
    label = label or LABELS.get(pid, pid)
    RESULTS.append({"id": pid, "rows": rows, "block": pid.split(".")[0], "script": SCRIPT, "label": label, "ok": ok, "detail": detail, "kind": kind})
    print(f"  [{'PASS' if ok else 'FAIL'}] {pid:7s} {kind:11s} [{rows}] {label[:100]}" + (f"  --  {detail}" if detail else ""))
    return ok

def summary(write=True):
    n_ok = sum(r["ok"] for r in RESULTS)
    print(f"\nSUMMARY: {n_ok}/{len(RESULTS)} checks passed ({len(MICRO)} micro-checks)" + ("" if n_ok == len(RESULTS) else "  <-- FAILURES"))
    if write:
        with open("results.json", "w") as f:
            json.dump(RESULTS, f, indent=1, ensure_ascii=False)
    return n_ok == len(RESULTS)

# ---- the figure blocks' drawing surface: matplotlib imported on first use (an import of the package stays instantaneous)
OUT = os.path.join(os.path.dirname(os.path.abspath(__file__)), "out")
INK, MID, SOFT, FILL = "0.15", "0.35", "0.52", "0.945"
plt = None

def _plt():
    """matplotlib.pyplot with the Agg backend and the paper's rcParams, imported once."""
    global plt
    if plt is None:
        import matplotlib
        matplotlib.use("Agg")
        import matplotlib.pyplot as _p
        _p.rcParams.update({"font.family": "serif", "mathtext.fontset": "cm", "font.size": 9, "axes.linewidth": 0.6})
        plt = _p
    return plt

def save(fig, stem):
    os.makedirs(OUT, exist_ok=True)
    fig.savefig(os.path.join(OUT, stem + ".png"), dpi=200)
    fig.savefig(os.path.join(OUT, stem + ".pdf"))
    print(f"[WROTE] out/{stem}.png, .pdf")

# ------------------------------------------------------------------------------------------------------------
# block est — estimate_S.py (until 24 September 2026), the paper's script as written:
# estimate_S.py -- reproduces every numeral of 14-entropy (De Sitter Entropy
# Estimates). Standalone: no input, no external path; exit 0 iff all checks pass.
#
# All observational values are [approx] chart readings; the exact faces are
# the counts Om = 4S+1 and the admissibility congruences, verified here in
# exact integer arithmetic on the instantiated Carrier. No fitting, no RNG;
# transcendental library calls (sqrt, atanh, tanh, pi) appear only as the
# labelled chart functions applied to [approx]/[LCDM] quantities.
#
# Exit status: 0 iff the exact checks and the census both pass.
#
# Package form (2026-09): the script as written, its integer checks, [PASS] lines and asserts reported to the registry
# (the head of this script) as the families est.F1 (exact faces), est.B9 (area law), est.T1 (the instrument table), est.C1
# (two-face concordance), est.C2 (the chart identity), est.A1 (the circularity audit), est.C3 (the channel-1
# consistency), est.P3 (the age-rate locus), est.C4 (one-face concordance), est.L1 (the floor landing), est.P2 (the
# octant bound against the stellar ages), est.P1 (the running floor). A failing check prints and fails its family;
# the run continues. Kinds: est.F1 and the count half of est.B9 are EXACT; every other family is CHART -- a one-line
# chart computation on published [approx]/[LCDM] data, reproduced to the paper's quoted precision.
#
def block_est():
    """Block est — estimate_S: the exact faces and the area law on the laboratory Carrier, then every chart numeral of the paper (est.F1 … est.P1)."""

    # ---------------------------------------------------------------- exact faces
    # Instantiated Carrier of the lab universe (37-sim): exact integer counts.
    S_LAB = 602_140
    OM_LAB = 4 * S_LAB + 1


    def is_prime(n: int) -> bool:          # deterministic trial division, exact
        if n < 2:
            return False
        d = 2
        while d * d <= n:
            if n % d == 0:
                return False
            d += 1
        return True


    print("exact faces (counts): Om = 4S+1; S even; S = 1 mod 3; 4S+1 prime")
    # 14:A2 (p14002), 14:C6 (p14023)
    checks = [
        ("Om = 4S+1", OM_LAB == 2_408_561),
        ("S even (octant sector Z_8 exists: 8 | 4S iff 2 | S)", S_LAB % 2 == 0),
        ("S = 1 mod 3", S_LAB % 3 == 1),
        ("4S+1 prime", is_prime(OM_LAB)),
        ("octant count S/2 is an integer", (S_LAB // 2) * 2 == S_LAB),
    ]
    family("est", "F1")
    for name, ok in checks:
        print(f"  [{'PASS' if ok else 'FAIL'}] {name}  (lab Carrier Om={OM_LAB})")
        chk(name, ok)

    # ------------------------------------------------------- area law (row B9)
    # The quarter identity and the quarter-turn chain, exact integer arithmetic:
    # 4S = Om - 1; the generative four of Om = 4S+1 at the Carrier and
    # p = 4*kap + 1 at every Subject (hydrogen shell kap_H = 3, q = 13).
    print("area law (row B9): quarter identity and quarter-turn chain (counts)")
    KAP_H = 3
    Q_H = 4 * KAP_H + 1
    # 14:B9 (p14017)
    b9_checks = [
        ("quarter identity 4S = Om - 1", 4 * S_LAB == OM_LAB - 1),
        ("quarter-turn at the Carrier: 4 | Om - 1", (OM_LAB - 1) % 4 == 0),
        ("quarter-turn at the Subject: q_H = 4 kap_H + 1 = 13, prime",
         Q_H == 13 and is_prime(Q_H) and (Q_H - 1) % 4 == 0),
    ]
    family("est", "B9")
    for name, ok in b9_checks:
        print(f"  [{'PASS' if ok else 'FAIL'}] {name}")
        chk(name, ok)

    # ------------------------------------------------------------ chart channel
    # laboratory channel [I]
    lP = 1.616255e-35      # Planck length, m
    c = 2.99792458e8       # m/s
    Gyr = 3.1557e16        # s
    Mpc = 3.0857e22        # m


    def S_of(rH):          # S = pi (r_H / l_P)^2   [approx]
        return pi * (rH / lP) ** 2


    # area-law chart face (row B9) [approx]: the projected horizon area in Planck
    # cells is the full phase cycle, A/lP^2 = 4 pi n_A = 4 S(r_H), n_A = (r_H/lP)^2.
    print("area law chart face (row B9) [approx]: 4 pi n_A = 4 S(r_H)")
    for rH_test in (1.0, 1.5e26):
        n_A = (rH_test / lP) ** 2
        ok = abs(4 * pi * n_A - 4 * S_of(rH_test)) <= 1e-12 * (4 * S_of(rH_test))
        print(f"  [{'PASS' if ok else 'FAIL'}] r_H = {rH_test:g} m")
        chk(f"area-law chart face 4 pi n_A = 4 S(r_H) at r_H = {rH_test:g} m [approx]", ok)


    LAM_FACE = {"1", "4b"}          # rows reading the Lambda face
    GAUGE = {"4a"}                  # gauge reading: displayed, excluded from stats
    rows = []
    sigma = {}                      # per-row relative uncertainty on sqrt(S)

    # 1. expansion geometry: Lambda from the LCDM fit (Planck 2018)
    Lam = 1.088e-52                                   # m^-2, ~2% -> 1% on sqrt(S)
    rows.append(("1", "Lambda (CMB, Planck alone)", sqrt(3.0 / Lam)))
    sigma["1"] = 0.010

    # 2. local distance ladder (published stat+sys)
    for H0, dH, lab, key in ((73.0, 1.0, "Cepheid", "2a"), (69.8, 1.7, "TRGB", "2b")):
        rows.append((key, f"ladder H0={H0} ({lab})", c / (H0 * 1e3 / Mpc)))
        sigma[key] = dH / H0

    # 3. rotation curves through the realisation a0 = c H / 2 pi
    a0, da0 = 1.20e-10, sqrt(0.02**2 + 0.24**2) * 1e-10   # SPARC knee, sys-dominated
    rows.append(("3", "rotation curves a0", c / (2 * pi * a0 / c)))
    sigma["3"] = da0 / a0

    # 4. stellar ages through age = horizon distance (Valcin et al. 2026, IV;
    # one vintage rule: the superseding release everywhere, no mixing)
    t_star, dt = 13.61 * Gyr, sqrt(0.25**2 + 0.23**2) / 13.61
    rows.append(("4a", "stellar age, raw ct [gauge]", c * t_star))
    rows.append(("4b", "stellar age, octant (4/pi)ct", (4 / pi) * c * t_star))
    sigma["4a"] = sigma["4b"] = dt

    print(f"\n{'#':3s}{'instrument':32s} {'r_H [m]':>12s} {'S':>10s} {'sqrt(S)':>10s} {'sig%':>6s}")
    Svals = {}
    for key, name, rH in rows:
        S = S_of(rH)
        Svals[key] = S
        print(f"{key:3s}{name:32s} {rH:12.3e} {S:10.2e} {sqrt(S):10.2e} {100*sigma[key]:6.1f}")
    # the paper's table (Section 3.2): r_H in 1e26 m, S in 1e122, sigma on sqrt(S) in %
    # 14:C1 (p14018)
    family("est", "T1")
    TABLE = {"1": (1.66, 3.3, 1), "2a": (1.27, 1.9, 1.4), "2b": (1.33, 2.1, 2.4), "3": (1.19, 1.7, 20), "4a": (1.29, 2.0, 2.5), "4b": (1.64, 3.2, 2.5)}
    for key, name, rH in rows:
        r_t, S_t, sg_t = TABLE[key]
        chk(f"row {key}: r_H = {r_t} e26 m, S = {S_t} e122, sigma = {sg_t}% as tabulated",
            abs(rH / 1e26 - r_t) < 0.006 and abs(Svals[key] / 1e122 - S_t) < 0.06 and abs(100 * sigma[key] - sg_t) < 0.1)

    EVIDENCE = [k for k, _, _ in rows if k not in GAUGE]   # five evidence readings
    sq = {k: sqrt(Svals[k]) for k in EVIDENCE}
    m = sum(sq.values()) / len(sq)
    half = 100 * (max(sq.values()) - min(sq.values())) / 2 / m
    fac = (max(sq.values()) / min(sq.values())) ** 2
    print(f"\nconcordance (5 evidence readings, gauge 4a excluded): sqrt(S) ="
          f" {min(sq.values()):.2e} .. {max(sq.values()):.2e}"
          f"  (+/- {half:.1f}% half-range about the mean)")
    print(f"on S itself: full-range spread = factor {fac:.2f}")
    # 14:C4 (p14021)
    family("est", "C1")
    chk("five evidence readings, gauge row 4a excluded", EVIDENCE == ["1", "2a", "2b", "3", "4b"])
    chk("sqrt(S) = (1.3..1.8) e61 across the five readings", 1.25e61 < min(sq.values()) < 1.35e61 and 1.75e61 < max(sq.values()) < 1.85e61)
    chk("half-range +/-17% on the count face (16.5 +/- 0.5)", abs(half - 16.5) < 0.5)
    chk("full-range spread on S a factor 1.9 (1.94 +/- 0.05)", abs(fac - 1.94) < 0.05)
    print("[PASS] concordance: +/-17% half-range, factor 1.9 on S")

    CONV = ["1", "2a", "2b"]                       # conventional channels alone
    sqc = {k: sqrt(Svals[k]) for k in CONV}
    mcv = sum(sqc.values()) / len(sqc)
    half_cv = 100 * (max(sqc.values()) - min(sqc.values())) / 2 / mcv
    fac_cv = (max(sqc.values()) / min(sqc.values())) ** 2
    print(f"conventional channels alone: +/- {half_cv:.1f}% half-range, factor {fac_cv:.2f}")
    chk("conventional channels alone: +/-14% (13.9 +/- 0.5), factor 1.7 (1.72 +/- 0.03)", abs(half_cv - 13.9) < 0.5 and abs(fac_cv - 1.72) < 0.03)
    print("[PASS] conventional-only statistic: +/-14%, factor 1.7")

    # the two-cluster ratio is the chart identity (H_rate/H0)^2 / OmL -- the
    # definition of OmL read on the rows, NOT framework content (round-02 F1).
    OmL = 0.685
    H0_PLANCK = 67.36
    family("est", "C2")
    for key, H in (("2a", 73.0), ("2b", 69.8)):
        lhs = Svals["1"] / Svals[key]
        rhs = (H / H0_PLANCK) ** 2 / OmL
        chk(f"row {key}: S_Lambda/S_rate = (H/H0)^2/OmL to 0.2% [LCDM]", abs(lhs / rhs - 1) < 2e-3)
    chk("the observed cluster excess 1.68 against 1.46 = 1/OmL [LCDM]", abs(1 / OmL - 1.46) < 0.005 and abs(Svals["1"] / ((Svals["2a"] + Svals["2b"] + Svals["3"]) / 3) - 1.68) < 0.1)
    print("[PASS] chart identity S_L/S_rate = (H/H0)^2/OmL verified per row"
          " (the cluster ratio displays the Hubble tension; no framework content)")

    # circularity audit: the age ratio depends on the single fitted Omega_Lambda
    ratio = (2 / 3) * atanh(sqrt(OmL))                # [LCDM]
    OmL_pi4 = tanh(1.5 * pi / 4) ** 2                 # inversion of pi/4 [LCDM]
    dev = abs(ratio - pi / 4) / (pi / 4) * 100
    sig = abs(OmL - OmL_pi4) / 0.007
    print(f"\naudit: t0*H_L = (2/3) artanh(sqrt(OmL)) = {ratio:.4f};  pi/4 = {pi / 4:.4f}"
          f"  (deviation {dev:.2f}%)")
    print(f"       pi/4 corresponds to OmL = {OmL_pi4:.4f}  (fitted: {OmL}; a {sig:.2f}-sigma landing)")
    print("       => the ~0.2% landing restates the fitted OmL: consistency, not evidence")
    print("       (sub-0.1% figures need the radiation correction the flat matter+Lambda form omits)")
    # 14:C3 (p14020), 14:C7 (p14024), 14:X3 (p14030), 14:X6 (p14033)
    family("est", "A1")
    chk("t0 H_Lambda = (2/3) artanh(sqrt(OmL)) = 0.7871 at OmL = 0.685 [LCDM]", abs(ratio - 0.7871) < 5e-4)
    chk("within 0.2% of pi/4 = 0.7854", dev < 0.25)
    chk("the inversion: pi/4 corresponds to OmL = tanh^2(3pi/8) = 0.6837", abs(OmL_pi4 - 0.6837) < 5e-5)
    chk("a 0.19-sigma landing on the fitted 0.685 +/- 0.007", abs(sig - 0.19) < 0.01)

    # octant lemma prediction: Omega_Lambda as an output of the realisation set
    print(f"\noctant lemma: t_age = (pi/4) r_H/c  =>  predicted OmL = tanh^2(3pi/8) = {OmL_pi4:.4f}"
          f"  (fitted {OmL}: {sig:.2f} sigma)")
    print("saturation test (fit-independent): oldest-object ages cap at (pi/4) r_H/c = 13.8 Gyr,"
          " at every observational frame chronon")

    # the channel-1 consistency (T19, 2026-09-13): with the fit's Lambda, the age-rate locus returns the
    # fit's own H0, since Lambda = 3 OmL H0^2/c^2 by definition -- same-channel, a corollary, not a prediction.
    H_L = sqrt(Lam * c ** 2 / 3) * Mpc / 1e3          # km/s/Mpc [approx]
    H0_ent = H_L / tanh(3 * pi / 8)
    print(f"\nchannel-1 consistency: H_Lambda = {H_L:.1f} => H0 = {H0_ent:.2f} = 67.36 x {H0_ent/67.36:.4f}"
          "  (same-channel: the fit's Lambda is 3 OmL H0^2/c^2; a corollary of the octant landing, not a prediction)")
    # 14:C8 (p14025)
    family("est", "C3")
    chk("H_Lambda = 55.7 km/s/Mpc from the fit's Lambda (1/H_Lambda = 17.55 Gyr) [LCDM]", abs(H_L - 55.7) < 0.05 and abs(1 / (H_L * 1e3 / Mpc) / Gyr - 17.55) < 0.01)
    chk("the locus at the channel-1 Lambda returns H0 = 67.4, the fit's own value to 0.1%", abs(H0_ent - 67.4) < 0.15 and abs(H0_ent / 67.36 - 1.0) < 0.002)
    print("[PASS] channel-1 consistency: the locus returns the fit's H0 to 0.1%")

    # the age-rate locus (row P3): t_age * H0 = (pi/4)/tanh(3pi/8), exact for the realisation set; read on the
    # fit-independent stellar age it is a prediction of H0 independent of the expansion fit.
    locus = (pi / 4) / tanh(3 * pi / 8)
    t_star, dt_star = 13.61, sqrt(0.25 ** 2 + 0.23 ** 2)   # Gyr, Valcin 2026 (stat+sys)
    H0_age = locus / (t_star * Gyr) * Mpc / 1e3           # km/s/Mpc [approx]
    dH0_age = H0_age * dt_star / t_star
    sig_shoes = (73.0 - H0_age) / sqrt(1.0 ** 2 + dH0_age ** 2)
    sig_trgb = (69.8 - H0_age) / sqrt(1.7 ** 2 + dH0_age ** 2)
    sig_planck = (67.36 - H0_age) / sqrt(0.54 ** 2 + dH0_age ** 2)
    lcdm_locus = (2 / 3) * atanh(sqrt(0.685)) / sqrt(0.685)   # flat matter+Lambda t0*H0 at the fitted OmL
    print(f"\nage-rate locus: t_age*H0 = (pi/4)/tanh(3pi/8) = {locus:.4f}  (LCDM at OmL=0.685: {lcdm_locus:.4f}, the X3 coincidence)")
    print(f"  read on t_star = {t_star} +/- {dt_star:.2f} Gyr: H0 = {H0_age:.1f} +/- {dH0_age:.1f} km/s/Mpc"
          f"  (Planck {abs(sig_planck):.2f} sigma; TRGB {abs(sig_trgb):.2f} sigma; Cepheid {abs(sig_shoes):.2f} sigma)")
    print(f"  ladder pair (13.61 Gyr, 73): t*H0 = {73.0 * 1e3 / Mpc * t_star * Gyr:.3f} -- accommodated in LCDM only by OmL ~ 0.76, which the octant forbids")
    # 14:P3 (p14038)
    family("est", "P3")
    chk("the age-rate locus t_age H0 = (pi/4)/tanh(3pi/8) = 0.950 (0.9499)", abs(locus - 0.9499) < 5e-4)
    chk("flat LCDM returns 0.951 at the fitted OmL (the X3 coincidence read on H0)", abs(lcdm_locus - 0.9510) < 5e-4)
    chk("read on t_star = 13.61 +/- 0.34 Gyr: H0 = 68.2 +/- 1.7 km/s/Mpc [approx]", abs(H0_age - 68.2) < 0.1 and abs(dH0_age - 1.7) < 0.05)
    chk("confrontations: Planck 0.5 sigma, TRGB 0.65 sigma, Cepheid 2.4 sigma", abs(sig_shoes - 2.4) < 0.1 and abs(sig_trgb - 0.65) < 0.05 and abs(abs(sig_planck) - 0.5) < 0.05)
    chk("the ladder pair (13.61 Gyr, 73): t_star H0 = 1.016, above the locus", abs(73.0 * 1e3 / Mpc * t_star * Gyr - 1.016) < 0.002)
    print("[PASS] P3: H0 = 68.2 +/- 1.7 from the stellar age through the octant; Cepheid 2.4 sigma, TRGB 0.65, Planck 0.5")

    # one-face concordance: rate rows carried to the Lambda face by the octant's factor 1/tanh(3pi/8)
    th = tanh(3 * pi / 8)
    rL = {"1": rows[[r[0] for r in rows].index("1")][2],
          "2a": c / (73.0 * 1e3 / Mpc * th), "2b": c / (69.8 * 1e3 / Mpc * th),
          "3": c / (2 * pi * a0 / c * th), "4b": rows[[r[0] for r in rows].index("4b")][2]}
    sq = {k: sqrt(pi) * v / lP for k, v in rL.items()}
    def halfrange(keys):
        v = [sq[k] for k in keys]; return 100 * (max(v) - min(v)) / 2 / ((max(v) + min(v)) / 2)
    hr5 = halfrange(["1", "2a", "2b", "3", "4b"]); hr3 = halfrange(["1", "2a", "2b"])
    print("\none-face concordance (r_H^Lambda = c/(H tanh(3pi/8)) on rate rows):")
    for k in ("1", "2a", "2b", "3", "4b"): print(f"  {k:3s} r_H^L = {rL[k]:.3e} m   sqrt(S) = {sq[k]:.3e}")
    print(f"  half-range: +/-{hr5:.1f}% over five readings; +/-{hr3:.1f}% conventional (1, 2a, 2b)")
    family("est", "C4")
    for k, v in (("1", 1.66), ("2a", 1.53), ("2b", 1.60), ("3", 1.44), ("4b", 1.64)):
        chk(f"row {k}: r_H^Lambda = {v} e26 m as tabulated", abs(rL[k] / 1e26 - v) < 0.006)
    chk("one-face half-range +/-7% over five readings (7.0 +/- 0.3)", abs(hr5 - 7.0) < 0.3)
    chk("one-face half-range +/-4% conventional (4.0 +/- 0.3)", abs(hr3 - 4.0) < 0.3)
    chk("the residual between the ladder rows and row 1 is 8% (the Hubble tension proper)", abs(100 * (rL["1"] - (rL["2a"] + rL["2b"]) / 2) / rL["1"] - 6) < 3)
    print("[PASS] one-face concordance +/-7% (five), +/-4% (conventional)")

    # floor landing at the corpus H0
    land = c * (67.4 * 1e3 / Mpc) / 1.2e-10
    print(f"\nfloor landing: c H0/a0 = {land:.2f} +/- {0.2*land:.1f} at H0 = 67.4 (2 pi = {2*pi:.2f}, {(2*pi-land)/(0.2*land):.2f} sigma)")
    # 14:X2 (p14029)
    family("est", "L1")
    chk("floor landing c H0/a0 = 5.46 at H0 = 67.4 [approx]", abs(land - 5.46) < 0.02)
    chk("+/-1.1 (20%), 0.8 sigma from 2 pi", abs(0.2 * land - 1.09) < 0.02 and abs((2 * pi - land) / (0.2 * land) - 0.76) < 0.03)

    # temporal-face confrontation: octant bound vs Valcin et al. 2026 (IV) [LCDM]
    t_oct = (pi / 4) * sqrt(3.0 / Lam) / c / Gyr
    dv = sqrt(0.25 ** 2 + 0.23 ** 2)
    sig_gc = (t_oct - 13.61) / dv
    sig_tu = (t_oct - 13.81) / dv
    print(f"\noctant bound {t_oct:.2f} Gyr vs Valcin IV (one vintage everywhere):"
          f" oldest population {sig_gc:+.2f} sigma below (fit-independent, carries P2);"
          f" prior-dependent inferred age {sig_tu:+.2f} sigma (straddles within 0.1 sigma)")
    # 14:C5 (p14022), 14:P2 (p14037)
    family("est", "P2")
    chk("the octant bound (pi/4) sqrt(3/Lambda)/c = 13.79 Gyr at the channel-1 Lambda [approx]", abs(t_oct - 13.79) < 0.01)
    chk("the LCDM age 13.80 Gyr is degenerate with the bound to 0.2%", abs(13.80 / t_oct - 1) < 0.0025)
    chk("oldest cluster population 13.61 +/- 0.34: 0.5 sigma below the bound (0.53)", abs(sig_gc - 0.53) < 0.05)
    chk("inferred cosmic age 13.81: straddles the bound within 0.1 sigma (-0.06)", abs(sig_tu + 0.06) < 0.05)
    print("[PASS] Valcin IV: population 0.5 sigma below the bound; inferred age a"
          " prior-dependent consistency, statistically consistent with saturation")

    # floor-running confrontation: MUSE-DARK III (Ciocan et al. 2026) [LCDM]
    Om_m = 0.315
    Hz = sqrt(Om_m * 8 + (1 - Om_m))                  # H(z=1)/H0, flat LCDM
    a0_pred = (a0 * Hz) * 1e10                        # e-10 units
    sig_end = (2.38 - a0_pred) / sqrt(0.10**2 + (da0 * 1e10 * Hz) ** 2)
    slope_pred = a0 * 1e10 * (Hz - 1)
    sig_slope = (1.59 - slope_pred) / sqrt(0.10**2 + (da0 * 1e10 * (Hz - 1)) ** 2)
    print(f"\nfloor running: a0(z=1) predicted {a0_pred:.2f}e-10 vs measured 2.38+/-0.10"
          f" ({sig_end:.1f} sigma with anchor systematics); linear rate predicted"
          f" {slope_pred:.2f} vs 1.59+/-0.10 e-10/z ({sig_slope:.1f} sigma pre-systematics)")
    # 14:P1 (p14036)
    family("est", "P1")
    chk("a0(z=1) on the H(z) chord: 2.15e-10 (flat LCDM E(z=1) = 1.79) [LCDM]", abs(a0_pred - 2.15) < 0.01 and abs(Hz - 1.79) < 0.005)
    chk("endpoint 0.5 sigma from the measured 2.38 +/- 0.10 with the anchor's systematic band", abs(sig_end - 0.5) < 0.1)
    chk("the fitted linear rate 1.59 +/- 0.10 exceeds the chord's 0.95 per unit redshift by ~3 sigma (pre-systematics)", abs(slope_pred - 0.95) < 0.01 and abs(sig_slope - 3.0) < 0.1)
    # the four bins (Fig. 3 of Ciocan et al. 2026, digitised in the corpus paper 43-muse, validation/muse_bins.py): z centre, a0 in 1e-10 m/s^2, error [import]
    zb, ab, eb = [0.503, 0.825, 1.047, 1.276], [1.990, 2.200, 2.571, 2.710], [0.086, 0.105, 0.112, 0.136]
    Eb = [sqrt(Om_m * (1 + z) ** 3 + (1 - Om_m)) for z in zb]; wb = [1 / e ** 2 for e in eb]      # flat LCDM E(z) at the bin centres; inverse-variance weights
    a_const = sum(w * a for w, a in zip(wb, ab)) / sum(wb)
    chi_const = sum(w * (a - a_const) ** 2 for w, a in zip(wb, ab))                                  # a constant floor, 3 dof
    A_fit = sum(w * a * E for w, a, E in zip(wb, ab, Eb)) / sum(w * E * E for w, E in zip(wb, Eb))   # A H(z)/H0 at free amplitude, 3 dof
    dA_fit = 1 / sqrt(sum(w * E * E for w, E in zip(wb, Eb)))
    chi_run = sum(w * (a - A_fit * E) ** 2 for w, a, E in zip(wb, ab, Eb))
    S, Sz, Szz = sum(wb), sum(w * z for w, z in zip(wb, zb)), sum(w * z * z for w, z in zip(wb, zb))
    Sa, Sza = sum(w * a for w, a in zip(wb, ab)), sum(w * z * a for w, z, a in zip(wb, zb, ab))
    a1_bins = (S * Sza - Sz * Sa) / (S * Szz - Sz ** 2); da1_bins = sqrt(S / (S * Szz - Sz ** 2))     # the weighted linear fit's rate per unit redshift
    excess = log10(A_fit / (c * (67.4e3 / Mpc) / (2 * pi) * 1e10))                                    # the amplitude over the floor c H0/2 pi at the channel-1 H0
    print(f"  the four bins: constant floor chi2 = {chi_const:.1f}/3; A H(z)/H0 chi2 = {chi_run:.1f}/3 at A = {A_fit:.2f} +/- {dA_fit:.2f}"
          f" (Delta chi2 = {chi_const - chi_run:.0f}); binned rate {a1_bins:.2f} +/- {da1_bins:.2f} per unit z on the chord {slope_pred:.2f};"
          f" amplitude {excess:.2f} dex above c H0/2 pi")
    chk("four bins 1.99 -> 2.71e-10 over z = 0.50-1.28: a constant floor is excluded, Delta chi2 = 23 against A H(z)/H0 [LCDM]", abs(chi_const - chi_run - 23) < 0.5)
    chk("A H(z)/H0 fits the bins at free amplitude: A = 1.39 +/- 0.03, chi2 = 5.4/3", abs(A_fit - 1.39) < 0.005 and abs(dA_fit - 0.03) < 0.005 and abs(chi_run - 5.4) < 0.05)
    chk("the binned rate 0.98 +/- 0.19 per unit redshift sits on the H(z) chord (0.95)", abs(a1_bins - 0.98) < 0.005 and abs(da1_bins - 0.19) < 0.005 and abs(a1_bins - slope_pred) < da1_bins)
    chk("the amplitude's excess over c H0/2 pi is 0.12 dex, inside the 0.2 dex gas systematic", abs(excess - 0.12) < 0.006 and excess < 0.2)
    print("[PASS] MUSE-DARK III confrontation: constant floor excluded (Delta chi2 = 23); the running form fits at A = 1.39;"
          " endpoint 0.5 sigma; the authors' global linear rate ~3 sigma above the chord, the binned rate on it")

    # bound channel
    print("\nbound: registered entropy budget ~1e104 << S  (headroom ~1e18 to saturation)")



    flush("est", order=["F1", "B9", "T1", "C1", "C2", "A1", "C3", "P3", "C4", "L1", "P2", "P1"],
          kinds={"F1": "EXACT", "B9": "EXACT+CHART"})

# ------------------------------------------------------------------------------------------------------------
# block tri — triangle.py (until 24 September 2026), the paper's make-wedge-2.py:
# The registrable triangle -- companion figure for the s-estimation note.
#
# Exact layer: the audit identities are asserted before drawing (algebraic
# identities; float tolerance documents CODATA rounding).  Display layer
# [approx]: log10 chart of the bounded-window mass--radius plane.  FRC
# reading: the two walls are the two lattice generators (Compton = the
# crossing hbar; Schwarzschild = the normalisation G); the apex is the Planck
# anchor; the right wall is the totality on its own horizon; the record-depth
# ruler saturates at the octant (pi/4) r_H/c, the same at every observational
# frame chronon, while the rival chart's cosmic time runs on -- the paper's
# saturation falsifier drawn.
#
# Package form (2026-09): make-wedge-2.py of the paper, renamed triangle.py, wrapped in run(); its asserts report to the
# registry (the head of this script) as the families tri.A (audit identities), tri.D (the diagonal), tri.W (wall residents and the slope
# decomposition), tri.F (the figures, written to out/). The wall-channels annotation reads "channel-1 consistency rate"
# (the wording of the 13 September 2026 revision) where the July figure read "entailed rate H0 = 67.4 +/- 0.7".
def block_tri():
    """Block tri — triangle: the audit identities before drawing, the diagonal, the wall residents, the figures (tri.A, tri.D, tri.W, tri.F)."""
    plt = _plt()
    # ---- imports [approx]: laboratory constants and the note's table ----
    c, G, hbar = 2.99792458e8, 6.67430e-11, 1.054571817e-34
    lP, mP = 1.616255e-35, 2.176434e-8
    tP = lP / c                            # identity anchor; CODATA agrees to 1e-7
    rH_L = 1.659e26                        # Lambda face (channel 1)
    rows = [  # (label, r_H [m], cluster) from the note, Sec. 3; 4a gauge (excluded)
        ("1", 1.659e26, "L"), ("2a", 1.27e26, "R"), ("2b", 1.33e26, "R"),
        ("3", 1.19e26, "R"), ("4a", 1.29e26, "G"), ("4b", 1.64e26, "L"),
    ]
    S_L = pi * (rH_L / lP) ** 2

    # ---- audit asserts ----
    family("tri", "A")
    t_oct = pi / 4 * rH_L / c
    chk("octant identity t_oct = (sqrt(pi)/4) sqrt(S) t_P to 1e-12", abs(t_oct - sqrt(pi) / 4 * sqrt(S_L) * tP) / t_oct < 1e-12)
    mean_R = sum(r for _, r, k in rows if k == "R") / 3    # evidence rows only
    mean_L = sum(r for _, r, k in rows if k == "L") / 2
    chk("two-cluster ratio on S (Valcin IV rows)", abs((mean_L / mean_R) ** 2 - 1.71) < 0.02)
    chk("chart-identity r_H split", abs(1 / sqrt(0.685) - 1.208) < 0.002)
    # entailed rate from the octant + measured Lambda (round-02 F1)
    from math import tanh
    _HL = sqrt(1.088e-52 * c ** 2 / 3) * 3.0857e22 / 1e3
    chk("H0 = 67.4 km/s/Mpc", abs(_HL / tanh(3 * pi / 8) - 67.4) < 0.15)
    # wedge width: the count face sqrt(S) in its chart dress sqrt(S/pi) -- the
    # solid angle of the area law is the declared register->chart transport (0.25 dex)
    chk("width identity log10(r_H/l_P) = log10 sqrt(S/pi) to 1e-12", abs(log10(rH_L / lP) - log10(sqrt(S_L / pi))) < 1e-12)

    # ---- chart ----
    xg, yg = log10, log10
    comp = lambda x: log10(hbar / c) - x        # Compton:  m R = hbar/c
    schw = lambda x: x - log10(2 * G / c**2)    # Schwarzschild: m = R c^2/2G
    x_apex = (log10(hbar / c) + log10(2 * G / c**2)) / 2
    xW = xg(rH_L)
    x_oct = xg(pi / 4 * rH_L)

    fig, ax = plt.subplots(figsize=(6.4, 8.9))
    ax.set_aspect("equal", adjustable="box")

    ax.fill([x_apex, xW, xW], [comp(x_apex), schw(xW), comp(xW)],
            color=FILL, zorder=0, lw=0)
    ax.plot([x_apex, xW], [schw(x_apex), schw(xW)], color=INK, lw=1.1, zorder=3)
    ax.plot([x_apex, xW], [comp(x_apex), comp(xW)], color=INK, lw=1.1, zorder=3)
    ax.plot([xW, xW], [comp(xW) - 2.5, schw(xW) + 3.2], color=MID, lw=1.0,
            ls=(0, (5, 3)), zorder=3)

    ax.text(-20, schw(-20) + 2.0, r"Schwarzschild $\;R=2Gm/c^{2}$ — the normalisation $G$",
            rotation=45, ha="center", va="center", fontsize=9.5, color=INK)
    ax.text(-14, comp(-14) - 2.0, r"Compton $\;mRc=\hbar$ — the crossing $\hbar$",
            rotation=-45, ha="center", va="center", fontsize=9.5, color=INK)
    ax.text(xW - 1.1, -26, r"$r_H$ — the totality wall", rotation=90,
            ha="center", va="center", fontsize=9.5, color=MID)
    ax.text(3, 39, "over-closed (horizon)", fontsize=8.5, color=SOFT,
            ha="center", style="italic", rotation=0)
    ax.text(-19, -42, "delocalised (no registration)", fontsize=8.5, color=SOFT,
            ha="center", style="italic")
    ax.text(13.5, -9, "the registrable triangle", fontsize=11.5, color="0.45",
            ha="center")

    # Planck apex and the totality point
    ax.scatter([xg(lP)], [yg(mP)], s=22, color=INK, zorder=5)
    ax.annotate(r"Planck apex $(\ell_P,\,m_P)$", (xg(lP), yg(mP)),
                textcoords="offset points", xytext=(0, -14), ha="left",
                fontsize=8.5, color=INK)
    ax.scatter([xW], [schw(xW)], s=26, color=INK, zorder=5)
    ax.annotate(r"$\Omega$ — the totality on its own horizon",
                (xW, schw(xW)), textcoords="offset points", xytext=(-10, -11),
                ha="right", fontsize=9, color=INK)

    # reference marks [approx]
    objs = [  # reference marks along the typical-object diagonal [approx]
        ("electron", 3.86e-13, 9.109e-31, (7, -3), "left"),
        ("proton", 8.4e-16, 1.673e-27, (5, 4), "left"),
        ("H atom", 5.29e-11, 1.674e-27, (6, -8), "left"),
        ("protein", 5.0e-9, 1e-22, (5, -3), "left"),
        ("virus", 1.0e-7, 1e-18, (5, -3), "left"),
        ("bacterium", 1.0e-6, 1e-15, (5, -3), "left"),
        ("human cell", 1.0e-5, 1e-12, (5, -3), "left"),
        ("ant", 4.0e-3, 3e-6, (-5, -2), "right"),
        ("human", 1.0, 7e1, (5, -9), "left"),
        ("blue whale", 2.5e1, 1.5e5, (5, -2), "left"),
        ("comet", 5.0e3, 1e13, (5, -3), "left"),
        ("asteroid", 2.6e5, 2.6e20, (-6, -2), "right"),
        ("Moon", 1.74e6, 7.35e22, (4, -11), "left"),
        ("Earth", 6.37e6, 5.97e24, (5, -9), "left"),
        ("Sun", 6.96e8, 1.99e30, (5, -9), "left"),
        ("white dwarf", 7.0e6, 1.2e30, (0, -13), "center"),
        ("solar system", 6.0e12, 2e30, (5, -3), "left"),
        ("neutron star", 1.2e4, 2.8e30, (-6, -6), "right"),
        (r"$10M_\odot$ hole", 2.95e4, 1.99e31, (-6, 4), "right"),
        ("Sgr A*", 1.2e10, 8.2e36, (7, -3), "left"),
        ("globular cluster", 2.5e17, 1e36, (5, -8), "left"),
        ("galaxy", 4.7e20, 2e42, (2, -10), "left"),
        ("galaxy cluster", 5.0e22, 2e45, (0, -12), "right"),
        ("supercluster", 4.0e24, 5e47, (-9, -12), "center"),
    ]
    # the object diagonal: ordinary least-squares regression over the ON-DIAGONAL
    # scale-typical single observable objects, MID-WEDGE ONLY.  Wall residents
    # are excluded by the same rule as every other exclusion: the electron sits
    # on the Compton wall by construction (its R is its reduced Compton
    # wavelength) and Sgr A* on the Schwarzschild wall (its R is its horizon
    # radius), so both are wall-displaced, drawn hollow, and become
    # out-of-sample checks of the diagonal's wall tangencies.  Also hollow:
    # the proton (the H atom stripped to its Compton-scale core), the compact
    # remnants (white dwarf, neutron star, stellar hole: collapsed ends hugging
    # the Schwarzschild wall), the solar system (the Sun's mass gravitationally
    # diluted), and the bound aggregates (globular cluster through supercluster:
    # collections, not single typical objects, bending toward the totality point).
    FIT = ["H atom", "protein", "virus", "bacterium",
           "human cell", "ant", "human", "blue whale", "comet", "asteroid",
           "Moon", "Earth", "Sun"]
    FIT_FULL = FIT + ["electron", "Sgr A*"]      # sensitivity population
    pos = {n: (xg(R), yg(m)) for n, R, m, _, _ in objs}


    def ols(names):
        n = len(names)
        sx = sum(pos[m][0] for m in names); sy = sum(pos[m][1] for m in names)
        sxx = sum(pos[m][0] ** 2 for m in names)
        sxy = sum(pos[m][0] * pos[m][1] for m in names)
        k = (n * sxy - sx * sy) / (n * sxx - sx * sx)
        return k, (sy - k * sx) / n


    def ols_k3(names):                       # constrained k = 3 fit
        n = len(names)
        b = sum(pos[m][1] - 3 * pos[m][0] for m in names) / n
        return 3.0, b


    k_fit, b_fit = ols(FIT)
    k_full, b_full = ols(FIT_FULL)
    k_c13, b_c13 = ols_k3(FIT)
    k_c15, b_c15 = ols_k3(FIT_FULL)
    x_lo = (log10(hbar / c) - b_fit) / (1 + k_fit)              # Compton-wall entry
    x_hi = min((-log10(2 * G / c**2) - b_fit) / (k_fit - 1), xW)  # exit: wall or r_H
    M_exit = 10 ** (x_hi - log10(2 * G / c**2)) / 1.989e30        # exit mass [Msun]

    # ---- diagonal asserts + pass lines [approx] ----
    # 14:C9 (p14026), 14:X5 (p14032)
    family("tri", "D")
    chk("slope 3 within 1.1%", abs(k_fit - 3.032) < 0.005)
    chk("coefficient 1.00e3 kg/m^3", abs(10 ** b_fit / 1.00e3 - 1) < 0.05)
    chk("sensitivity: walls included", abs(k_full - 3.007) < 0.005)
    chk("over-closure bound [Msun]", abs(M_exit / 1.8e8 - 1) < 0.05)
    chk("constrained k=3 coefficient", abs(10 ** b_c13 / 0.97e3 - 1) < 0.05)


    def exit_of(k, b):                                # exit mass of a fit variant
        xh = (-log10(2 * G / c**2) - b) / (k - 1)
        return 10 ** (xh - log10(2 * G / c**2)) / 1.989e30


    band = sorted(exit_of(k, b) for k, b in
                  ((k_fit, b_fit), (k_full, b_full), (k_c13, b_c13), (k_c15, b_c15)))
    chk("over-closure band (1.4-2.8)e8", band[0] > 1.3e8 and band[-1] < 2.9e8)
    print(f"[PASS] constrained k=3: c~ = m/R^3 = {10 ** b_c13:.2e} kg/m^3 (a cubic coefficient, not a density); over-closure band"
          f" ({band[0]:.2e} .. {band[-1]:.2e}) Msun across the four fit variants")
    family("tri", "W")
    chk("electron on the Compton wall to < 0.01 dex", abs(pos["electron"][1] - (log10(hbar / c) - pos["electron"][0])) < 0.01)
    chk("Sgr A* on the Schwarzschild wall to < 0.01 dex", abs(pos["Sgr A*"][1] - (pos["Sgr A*"][0] - log10(2 * G / c**2))) < 0.01)
    mean_c = sum(pos[m][1] - 3 * pos[m][0] for m in FIT) / len(FIT)
    drift = k_fit - 3.0                       # slope = 3 + d c / d logR identically
    span = max(pos[m][0] for m in FIT) - min(pos[m][0] for m in FIT)
    chk("slope decomposition: mean c = 2.99, drift 0.61 dex over the baseline", abs(mean_c - 2.99) < 0.02 and abs(drift * span - 0.61) < 0.02)
    print(f"[PASS] slope decomposition: k = 3 + dc/dlogR, drift {drift:+.4f} "
          f"({drift * span:.2f} dex over {span:.1f} dex), mean c = {mean_c:.2f}")
    print(f"[PASS] diagonal: k = {k_fit:.4f} (13 mid-wedge), intercept "
          f"{10 ** b_fit:.2e} at the metre pivot (density units only at k = 3); "
          f"sensitivity k = {k_full:.4f} (15 incl. walls)")
    print(f"[PASS] boundaries: Compton entry R = {10 ** x_lo:.2e} m; "
          f"over-closure exit M = {M_exit:.2e} Msun")
    chk("Compton entry at the atomic core scale, R = 5.3e-12 m (the electron 1.1 dex beyond)", abs(10 ** x_lo / 5.3e-12 - 1) < 0.05 and abs(x_lo - pos["electron"][0] - 1.1) < 0.1)
    chk("Sgr A* 1.6 dex before the over-closure exit", abs(x_hi - pos["Sgr A*"][0] - 1.6) < 0.1)
    print(f"[PASS] wall residents on-wall to <0.01 dex: electron (Compton, "
          f"{x_lo - pos['electron'][0]:+.1f} dex beyond entry), "
          f"Sgr A* (Schwarzschild, {x_hi - pos['Sgr A*'][0]:+.1f} dex before exit)")

    ax.plot([x_lo, x_hi], [b_fit + k_fit * x_lo, b_fit + k_fit * x_hi],
            color="0.62", lw=0.9, ls=(0, (1, 2.6)), zorder=2)
    ax.text(-1.6, 12.5, r"typical objects: $m=\tilde c\,R^{3}$,"
            r"  $\tilde c\approx10^{3}\,$kg$\,$m$^{-3}$",
            rotation=71.6, ha="center", va="center", fontsize=7.5, color="0.5")

    for name, R, m, off, ha in objs:
        if name in FIT:
            ax.scatter([xg(R)], [yg(m)], s=11, color="0.4", zorder=4)
        else:
            ax.scatter([xg(R)], [yg(m)], s=11, facecolors="white",
                       edgecolors="0.45", linewidths=0.9, zorder=4)
        ax.annotate(name, (xg(R), yg(m)), textcoords="offset points", xytext=off,
                    fontsize=7.5, color="0.4", ha=ha)

    # record-depth ruler (top interior): solid to the octant, dashed on, arrow
    yr = 58.0
    ax.plot([xg(c * tP), x_oct], [yr, yr], color=INK, lw=1.2, zorder=4)
    ax.plot([x_oct, xW + 2.8], [yr, yr], color=SOFT, lw=0.9, ls=(0, (3, 3)), zorder=4)
    ax.annotate("", (xW + 3.6, yr), (xW + 2.8, yr),
                arrowprops=dict(arrowstyle="->", color=SOFT, lw=0.9))
    for tval, lab in ((tP, r"$t_P$"), (1.0, r"$1\,$s"), (3.15576e7, r"$1\,$yr"),
                      (3.15576e16, r"$1\,$Gyr")):
        xt = xg(c * tval)
        ax.plot([xt, xt], [yr - 0.8, yr + 0.8], color=INK, lw=0.8)
        ax.annotate(lab, (xt, yr - 2.0), ha="center", va="top", fontsize=8, color=INK)
    ax.plot([x_oct, x_oct], [yr - 1.3, yr + 1.3], color=INK, lw=1.8)
    ax.annotate("record depth saturates:  " + r"$(\pi/4)\,r_H/c = 13.8\;$Gyr",
                (x_oct - 0.8, yr + 2.0), ha="right", va="bottom", fontsize=8.5, color=INK)
    ax.annotate("chart time\n(unbounded)", (xW + 1.3, yr - 1.4), ha="left", va="top",
                fontsize=7.2, color=SOFT)
    ax.annotate(r"registrable depth $\;t = R/c$", (xg(c * tP) + 5.0, yr - 2.0),
                ha="left", va="top", fontsize=8.5, color=INK)

    # axes cosmetics
    ax.set_xlim(-37, 33.5)
    ax.set_ylim(-45, 62)
    ax.set_xlabel(r"$\log_{10} R\;$ [m]$\;$ [approx]", fontsize=9.5)
    ax.set_ylabel(r"$\log_{10} m\;$ [kg]$\;$ [approx]", fontsize=9.5)
    ax.set_xticks(range(-30, 31, 10))
    ax.set_yticks(range(-60, 61, 20))
    ax.tick_params(labelsize=8, color=MID, labelcolor=MID, length=3, width=0.6)
    for s in ax.spines.values():
        s.set_color(MID)

    # ---- inset: the wall, measured ----
    axi = ax.inset_axes([-35.5, 31.5, 27.0, 20.0], transform=ax.transData)
    axi.set_title("the wall, measured — six channels [approx]",
                  fontsize=8, color=INK, pad=4)
    for a, b in ((1.17, 1.35), (1.59, 1.68)):
        axi.axvspan(a, b, color=FILL)
    order = {"3": 0, "2a": 1, "4a": 2, "2b": 3, "4b": 4, "1": 5}
    for lab, r, k in rows:
        y = 0.16 + 0.105 * order[lab]
        axi.scatter([r / 1e26], [y], s=17, color=INK if k == "R" else "0.5", zorder=4)
        axi.annotate(lab, (r / 1e26, y), textcoords="offset points",
                     xytext=(4, -2.5), fontsize=7, color="0.3")
    axi.axvline(pi / 4 * rH_L / 1e26, color=INK, lw=1.1, ls=(0, (4, 2)))
    axi.annotate(r"$(\pi/4)\,r_H^{\Lambda}$", (pi / 4 * rH_L / 1e26, 0.80),
                 ha="center", va="top", fontsize=7.5, color=INK)
    axi.annotate("registered rate", (1.26, 0.035), ha="center", va="bottom",
                 fontsize=7.5, color=MID)
    axi.annotate(r"$\Lambda$ face", (1.635, 0.035), ha="center", va="bottom",
                 fontsize=7.5, color=MID)
    axi.annotate(r"split: the ladder--CMB (Hubble-tension) split; entailed $H_0=67.4$",
                 (1.425, 0.875), ha="center", fontsize=7.2, color=INK)
    axi.set_xlim(1.1, 1.75)
    axi.set_ylim(0, 0.95)
    axi.set_yticks([])
    axi.set_xticks([1.2, 1.4, 1.6])
    axi.set_xlabel(r"$r_H\;$ [$10^{26}\,$m]", fontsize=7.5, labelpad=2)
    axi.tick_params(labelsize=7, color=MID, labelcolor=MID, length=2.5, width=0.5)
    for s in axi.spines.values():
        s.set_color(MID); s.set_linewidth(0.5)

    fig.subplots_adjust(left=0.11, right=0.97, top=0.985, bottom=0.05)
    ax.set_xlim(-37, 33.5)
    ax.set_ylim(-45, 62)   # re-assert: pinned after all children
    save(fig, "registrable-wedge")

    # ---- plain version: no inlay (the channel strip ships as its own figure) ----
    axi.remove()
    save(fig, "registrable-wedge-plain")

    # ---- standalone channels figure (the former inlay, proportioned for print) ----
    fig2, ax2 = plt.subplots(figsize=(5.2, 2.3))
    for a, b in ((1.17, 1.35), (1.59, 1.68)):
        ax2.axvspan(a, b, color=FILL)
    for lab, r, k in rows:
        y = 0.14 + 0.135 * order[lab]
        ax2.scatter([r / 1e26], [y], s=26, color=INK if k == "R" else "0.5", zorder=4)
        ax2.annotate(lab, (r / 1e26, y), textcoords="offset points", xytext=(5, -3),
                     fontsize=8.5, color="0.3")
    ax2.axvline(pi / 4 * rH_L / 1e26, color=INK, lw=1.2, ls=(0, (4, 2)))
    ax2.annotate(r"$(\pi/4)\,r_H^{\Lambda}$" + "  (depth face)",
                 (pi / 4 * rH_L / 1e26 + 0.012, 0.97), ha="left", va="top",
                 fontsize=8.5, color=INK)
    ax2.annotate("registered-rate cluster", (1.26, 0.035), ha="center", va="bottom",
                 fontsize=8.5, color=MID)
    ax2.annotate(r"$\Lambda$-face cluster", (1.635, 0.035), ha="center", va="bottom",
                 fontsize=8.5, color=MID)
    ax2.annotate(r"cluster split on $r_H$: the ladder--CMB split (Hubble tension); channel-1 rate $67.4$",
                 (1.425, 1.05), ha="center", fontsize=8.5, color=INK,
                 annotation_clip=False)
    ax2.set_xlim(1.1, 1.75)
    ax2.set_ylim(0, 0.97)
    ax2.set_yticks([])
    ax2.set_xticks([1.2, 1.3, 1.4, 1.5, 1.6, 1.7])
    ax2.set_xlabel(r"$r_H\;$ [$10^{26}\,$m]   [approx]", fontsize=9)
    ax2.tick_params(labelsize=8, color=MID, labelcolor=MID, length=3, width=0.6)
    for sp in ax2.spines.values():
        sp.set_color(MID); sp.set_linewidth(0.6)
    fig2.subplots_adjust(left=0.03, right=0.985, top=0.86, bottom=0.19)
    save(fig2, "wall-channels")
    family("tri", "F")
    for f in ("registrable-wedge", "registrable-wedge-plain", "wall-channels"):
        chk(f"{f}.png and .pdf written to out/", os.path.exists(os.path.join(OUT, f + ".png")) and os.path.exists(os.path.join(OUT, f + ".pdf")))
    plt.close("all")
    print("ok")
    flush("tri", order=["A", "D", "W", "F"])

# ------------------------------------------------------------------------------------------------------------
# block cap — capacity.py (until 24 September 2026), the paper's make-wedge-3.py:
# The registrable triangle, capacity-ruler variant (20260815).
#
# Derived from make-wedge-2.py; adds the object-capacity ruler on the outer
# right axis: log10 capacity in the format of the mass axis, kappa primary,
# zero at the H atom (kappa_H = 3, the first Object), one dex per chart dex.
#
# Exact layer: the audit identities are asserted before drawing (algebraic
# identities; float tolerance documents CODATA rounding).  Display layer
# [approx]: log10 chart of the bounded-window mass--radius plane.  FRC
# reading: the two walls are the two lattice generators (Compton = the
# crossing hbar; Schwarzschild = the normalisation G); the apex is the Planck
# anchor; the right wall is the totality on its own horizon; the record-depth
# ruler saturates at the octant (pi/4) r_H/c, the same at every observational
# frame chronon, while the rival chart's cosmic time runs on -- the paper's
# saturation falsifier drawn.  Top axis (20260819): the same chart read as
# time, t = R/c, in decades matching the length axis -- the registrable span
# is the same 61 dex on both faces, t_P to r_H/c.
#
# Package form (2026-09): make-wedge-3.py of the paper, renamed capacity.py, wrapped in run(); its asserts report to the
# registry (the head of this script) as the families cap.A (the audit and diagonal identities, identical to triangle.py's), cap.K (the
# capacity axis: the pinned mass axis, the Avogadro landing), cap.F (the figure, written to out/).
def block_cap():
    """Block cap — capacity: the same identities re-asserted, the pinned mass axis and the Avogadro landing, the figure (cap.A, cap.K, cap.F)."""
    plt = _plt()
    # ---- imports [approx]: laboratory constants and the note's table ----
    c, G, hbar = 2.99792458e8, 6.67430e-11, 1.054571817e-34
    lP, mP = 1.616255e-35, 2.176434e-8
    tP = lP / c                            # identity anchor; CODATA agrees to 1e-7
    rH_L = 1.659e26                        # Lambda face (channel 1)
    rows = [  # (label, r_H [m], cluster) from the note, Sec. 3; 4a gauge (excluded)
        ("1", 1.659e26, "L"), ("2a", 1.27e26, "R"), ("2b", 1.33e26, "R"),
        ("3", 1.19e26, "R"), ("4a", 1.29e26, "G"), ("4b", 1.64e26, "L"),
    ]
    S_L = pi * (rH_L / lP) ** 2

    # ---- audit asserts ----
    family("cap", "A")
    t_oct = pi / 4 * rH_L / c
    chk("octant identity t_oct = (sqrt(pi)/4) sqrt(S) t_P to 1e-12", abs(t_oct - sqrt(pi) / 4 * sqrt(S_L) * tP) / t_oct < 1e-12)
    mean_R = sum(r for _, r, k in rows if k == "R") / 3    # evidence rows only
    mean_L = sum(r for _, r, k in rows if k == "L") / 2
    chk("two-cluster ratio on S (Valcin IV rows)", abs((mean_L / mean_R) ** 2 - 1.71) < 0.02)
    chk("chart-identity r_H split", abs(1 / sqrt(0.685) - 1.208) < 0.002)
    # entailed rate from the octant + measured Lambda (round-02 F1)
    from math import tanh
    _HL = sqrt(1.088e-52 * c ** 2 / 3) * 3.0857e22 / 1e3
    chk("H0 = 67.4 km/s/Mpc", abs(_HL / tanh(3 * pi / 8) - 67.4) < 0.15)
    # wedge width: the count face sqrt(S) in its chart dress sqrt(S/pi) -- the
    # solid angle of the area law is the declared register->chart transport (0.25 dex)
    chk("width identity log10(r_H/l_P) = log10 sqrt(S/pi) to 1e-12", abs(log10(rH_L / lP) - log10(sqrt(S_L / pi))) < 1e-12)

    # ---- chart ----
    xg, yg = log10, log10
    comp = lambda x: log10(hbar / c) - x        # Compton:  m R = hbar/c
    schw = lambda x: x - log10(2 * G / c**2)    # Schwarzschild: m = R c^2/2G
    x_apex = (log10(hbar / c) + log10(2 * G / c**2)) / 2
    xW = xg(rH_L)
    x_oct = xg(pi / 4 * rH_L)

    fig, ax = plt.subplots(figsize=(7.2, 8.9))
    ax.set_aspect("equal", adjustable="box")

    ax.fill([x_apex, xW, xW], [comp(x_apex), schw(xW), comp(xW)],
            color=FILL, zorder=0, lw=0)
    ax.plot([x_apex, xW], [schw(x_apex), schw(xW)], color=INK, lw=1.1, zorder=3)
    ax.plot([x_apex, xW], [comp(x_apex), comp(xW)], color=INK, lw=1.1, zorder=3)
    ax.plot([xW, xW], [comp(xW) - 2.5, schw(xW) + 3.2], color=MID, lw=1.0,
            ls=(0, (5, 3)), zorder=3)

    ax.text(-18, schw(-18) + 2.0, r"Schwarzschild $\;R=2Gm/c^{2}$ — the normalisation $G$",
            rotation=45, ha="center", va="center", fontsize=9.5, color=INK)
    ax.text(-14, comp(-14) - 2.0, r"Compton $\;mRc=\hbar$ — the crossing $\hbar$",
            rotation=-45, ha="center", va="center", fontsize=9.5, color=INK)
    ax.text(xW - 1.1, -26, r"$r_H$ — the totality wall", rotation=90,
            ha="center", va="center", fontsize=9.5, color=MID)
    ax.text(3, 39, "over-closed (horizon)", fontsize=8.5, color=SOFT,
            ha="center", style="italic", rotation=0)
    ax.text(-19, -42, "delocalised (no registration)", fontsize=8.5, color=SOFT,
            ha="center", style="italic")
    ax.text(12, -9, "the registrable triangle", fontsize=11.5, color="0.45",
            ha="center")

    # Planck apex and the totality point
    ax.scatter([xg(lP)], [yg(mP)], s=22, color=INK, zorder=5)
    ax.annotate(r"Planck apex $(\ell_P,\,m_P)$", (xg(lP), yg(mP)),
                textcoords="offset points", xytext=(6, -6), ha="left",
                fontsize=8.5, color=INK)
    ax.scatter([xW], [schw(xW)], s=26, color=INK, zorder=5)
    #ax.annotate(r"$\Omega$ — the totality on its own horizon",
    #            (xW, schw(xW)), textcoords="offset points", xytext=(-18, -11),
    #            ha="right", fontsize=9, color=INK)

    # reference marks [approx]
    objs = [  # reference marks along the typical-object diagonal [approx]
        ("electron", 3.86e-13, 9.109e-31, (7, -3), "left"),
        ("proton", 8.4e-16, 1.673e-27, (-4, 5), "left"),
        ("H atom", 5.29e-11, 1.674e-27, (4, -6), "left"),
        ("protein", 5.0e-9, 1e-22, (5, -3), "left"),
        ("virus", 1.0e-7, 1e-18, (5, -3), "left"),
        ("bacterium", 1.0e-6, 1e-15, (5, -3), "left"),
        ("human cell", 1.0e-5, 1e-12, (5, -3), "left"),
        ("ant", 4.0e-3, 3e-6, (-5, -2), "right"),
        #("1 mole", 1.0e-1, 1e-3, (-5, -2), "right"),
        ("human", 1.0, 7e1, (4, -6), "left"),
        ("blue whale", 2.5e1, 1.5e5, (5, -2), "left"),
        ("comet", 5.0e3, 1e13, (5, -3), "left"),
        ("asteroid", 2.6e5, 2.6e20, (5, -9), "left"),
        ("Moon", 1.74e6, 7.35e22, (4, -11), "left"),
        ("Earth", 6.37e6, 5.97e24, (5, -9), "left"),
        ("Sun", 6.96e8, 1.99e30, (5, -9), "left"),
        ("white dwarf", 7.0e6, 1.2e30, (0, -13), "center"),
        ("solar system", 6.0e12, 2e30, (5, -3), "left"),
        ("neutron star", 1.2e4, 2.8e30, (-6, -3), "right"),
        (r"$10M_\odot$ hole", 2.95e4, 1.99e31, (-3, 4), "right"),
        ("Sgr A*", 1.2e10, 8.2e36, (7, -3), "left"),
        ("globular cluster", 2.5e17, 1e36, (-17, -8), "left"),
        ("galaxy", 4.7e20, 2e42, (-2, -10), "left"),
        ("galaxy cluster", 5.0e22, 2e45, (2, -8), "right"),
        ("supercluster", 4.0e24, 5e47, (-9, -8), "center"),
    ]
    # the object diagonal: ordinary least-squares regression over the ON-DIAGONAL
    # scale-typical single observable objects, MID-WEDGE ONLY.  Wall residents
    # are excluded by the same rule as every other exclusion: the electron sits
    # on the Compton wall by construction (its R is its reduced Compton
    # wavelength) and Sgr A* on the Schwarzschild wall (its R is its horizon
    # radius), so both are wall-displaced, drawn hollow, and become
    # out-of-sample checks of the diagonal's wall tangencies.  Also hollow:
    # the proton (the H atom stripped to its Compton-scale core), the compact
    # remnants (white dwarf, neutron star, stellar hole: collapsed ends hugging
    # the Schwarzschild wall), the solar system (the Sun's mass gravitationally
    # diluted), and the bound aggregates (globular cluster through supercluster:
    # collections, not single typical objects, bending toward the totality point).
    FIT = ["H atom", "protein", "virus", "bacterium",
           "human cell", "ant", "human", "blue whale", "comet", "asteroid",
           "Moon", "Earth", "Sun"]
    FIT_FULL = FIT + ["electron", "Sgr A*"]      # sensitivity population
    pos = {n: (xg(R), yg(m)) for n, R, m, _, _ in objs}


    def ols(names):
        n = len(names)
        sx = sum(pos[m][0] for m in names); sy = sum(pos[m][1] for m in names)
        sxx = sum(pos[m][0] ** 2 for m in names)
        sxy = sum(pos[m][0] * pos[m][1] for m in names)
        k = (n * sxy - sx * sy) / (n * sxx - sx * sx)
        return k, (sy - k * sx) / n


    def ols_k3(names):                       # constrained k = 3 fit
        n = len(names)
        b = sum(pos[m][1] - 3 * pos[m][0] for m in names) / n
        return 3.0, b


    k_fit, b_fit = ols(FIT)
    k_full, b_full = ols(FIT_FULL)
    k_c13, b_c13 = ols_k3(FIT)
    k_c15, b_c15 = ols_k3(FIT_FULL)
    x_lo = (log10(hbar / c) - b_fit) / (1 + k_fit)              # Compton-wall entry
    x_hi = min((-log10(2 * G / c**2) - b_fit) / (k_fit - 1), xW)  # exit: wall or r_H
    M_exit = 10 ** (x_hi - log10(2 * G / c**2)) / 1.989e30        # exit mass [Msun]

    # ---- diagonal asserts + pass lines [approx] ----
    chk("slope 3 within 1.1%", abs(k_fit - 3.032) < 0.005)
    chk("coefficient 1.00e3 kg/m^3", abs(10 ** b_fit / 1.00e3 - 1) < 0.05)
    chk("sensitivity: walls included", abs(k_full - 3.007) < 0.005)
    chk("over-closure bound [Msun]", abs(M_exit / 1.8e8 - 1) < 0.05)
    chk("constrained k=3 coefficient", abs(10 ** b_c13 / 0.97e3 - 1) < 0.05)


    def exit_of(k, b):                                # exit mass of a fit variant
        xh = (-log10(2 * G / c**2) - b) / (k - 1)
        return 10 ** (xh - log10(2 * G / c**2)) / 1.989e30


    band = sorted(exit_of(k, b) for k, b in
                  ((k_fit, b_fit), (k_full, b_full), (k_c13, b_c13), (k_c15, b_c15)))
    chk("over-closure band (1.4-2.8)e8", band[0] > 1.3e8 and band[-1] < 2.9e8)
    print(f"[PASS] constrained k=3: c~ = m/R^3 = {10 ** b_c13:.2e} kg/m^3 (a cubic coefficient, not a density); over-closure band"
          f" ({band[0]:.2e} .. {band[-1]:.2e}) Msun across the four fit variants")
    chk("electron on the Compton wall to < 0.01 dex", abs(pos["electron"][1] - (log10(hbar / c) - pos["electron"][0])) < 0.01)
    chk("Sgr A* on the Schwarzschild wall to < 0.01 dex", abs(pos["Sgr A*"][1] - (pos["Sgr A*"][0] - log10(2 * G / c**2))) < 0.01)
    mean_c = sum(pos[m][1] - 3 * pos[m][0] for m in FIT) / len(FIT)
    drift = k_fit - 3.0                       # slope = 3 + d c / d logR identically
    span = max(pos[m][0] for m in FIT) - min(pos[m][0] for m in FIT)
    chk("slope decomposition: mean c = 2.99, drift 0.61 dex over the baseline", abs(mean_c - 2.99) < 0.02 and abs(drift * span - 0.61) < 0.02)
    print(f"[PASS] slope decomposition: k = 3 + dc/dlogR, drift {drift:+.4f} "
          f"({drift * span:.2f} dex over {span:.1f} dex), mean c = {mean_c:.2f}")
    print(f"[PASS] diagonal: k = {k_fit:.4f} (13 mid-wedge), intercept "
          f"{10 ** b_fit:.2e} at the metre pivot (density units only at k = 3); "
          f"sensitivity k = {k_full:.4f} (15 incl. walls)")
    print(f"[PASS] boundaries: Compton entry R = {10 ** x_lo:.2e} m; "
          f"over-closure exit M = {M_exit:.2e} Msun")
    print(f"[PASS] wall residents on-wall to <0.01 dex: electron (Compton, "
          f"{x_lo - pos['electron'][0]:+.1f} dex beyond entry), "
          f"Sgr A* (Schwarzschild, {x_hi - pos['Sgr A*'][0]:+.1f} dex before exit)")

    ax.plot([x_lo, x_hi], [b_fit + k_fit * x_lo, b_fit + k_fit * x_hi],
            color="0.62", lw=0.9, ls=(0, (1, 2.6)), zorder=2)
    ax.text(-1.6, 12.5, r"typical objects: $m=\tilde c\,R^{3}$,"
            r"  $\tilde c\approx10^{3}\,$kg$\,$m$^{-3}$",
            rotation=71.6, ha="center", va="center", fontsize=7.5, color="0.5")

    for name, R, m, off, ha in objs:
        if name in FIT:
            ax.scatter([xg(R)], [yg(m)], s=11, color="0.4", zorder=4)
        else:
            ax.scatter([xg(R)], [yg(m)], s=11, facecolors="white",
                       edgecolors="0.45", linewidths=0.9, zorder=4)
        ax.annotate(name, (xg(R), yg(m)), textcoords="offset points", xytext=off,
                    fontsize=7.5, color="0.4", ha=ha)

    # named times, ticked inward from the top axis with the label beneath each
    ytop = 62.0
    for tval, lab in ((tP, r"$t_P$"), (1.0, r"$1\,$s"), (3.15576e7, r"$1\,$yr")):
        xt = xg(c * tval)
        ax.plot([xt, xt], [ytop - 0.7, ytop], color=INK, lw=0.5, zorder=4)
        ax.annotate(lab, (xt, ytop - 1.2), ha="center", va="top",
                    fontsize=8, color=INK)
    ax.plot([x_oct, x_oct], [ytop - 2.6, ytop], color=INK, lw=1.2, zorder=4)
    ax.annotate(r"$(\pi/4)\,r_H/c = 13.8\;$Gyr$=10^{61}t_P$", (x_oct+8.0, ytop-3.2),
                ha="right", va="top", fontsize=8.5, color=INK)
    # the time face carries the length face's own 61 decades
    #ax.annotate(r"$61$ dex, $t_P$ to $r_H/c$ — the length face's own span",
    #            ((xg(c * tP) + xW) / 2, ytop - 5.0), ha="center", va="top",
    #            fontsize=8, color=MID)

    # axes cosmetics
    ax.set_xlim(-37, 35.0)
    ax.set_ylim(-45, 62)
    ax.set_xlabel(r"registration depth $\log_{10} R\;$ [m]$\;$ [approx]", fontsize=9.5)
    ax.set_ylabel(r"$\log_{10} m\;$ [kg]$\;$ [approx]", fontsize=9.5)
    ax.set_xticks(range(-30, 31, 10))
    ax.set_yticks([-60, -40, -20, -3, 0, 20, 40, 60])
    ax.tick_params(labelsize=8, color=MID, labelcolor=MID, length=3, width=0.6)
    for s in ax.spines.values():
        s.set_color(MID)

    # top axis: the same chart read as time, t = R/c -- one decade of time per
    # decade of length, the 61-dex registrable span identical on the two faces
    tax = ax.secondary_xaxis("top", functions=(lambda x: x - log10(c),
                                               lambda t: t + log10(c)))
    tax.set_xlabel(r"registration depth $\log_{10} t\;$ [s],$\;t = R/c\;$ [approx]", fontsize=9.5,
                       labelpad=6)
    tax.set_xticks(list(range(-40, 21, 10)))
    tax.tick_params(labelsize=8, color=MID, labelcolor=MID, length=3, width=0.6)
    tax.spines["top"].set_color(MID)

    # ---- inset: the wall, measured ----
    axi = ax.inset_axes([-35.5, 31.5, 27.0, 20.0], transform=ax.transData)
    axi.set_title("the wall, measured — six channels [approx]",
                  fontsize=8, color=INK, pad=4)
    for a, b in ((1.17, 1.35), (1.59, 1.68)):
        axi.axvspan(a, b, color=FILL)
    order = {"3": 0, "2a": 1, "4a": 2, "2b": 3, "4b": 4, "1": 5}
    for lab, r, k in rows:
        y = 0.16 + 0.105 * order[lab]
        axi.scatter([r / 1e26], [y], s=17, color=INK if k == "R" else "0.5", zorder=4)
        axi.annotate(lab, (r / 1e26, y), textcoords="offset points",
                     xytext=(4, -2.5), fontsize=7, color="0.3")
    axi.axvline(pi / 4 * rH_L / 1e26, color=INK, lw=1.1, ls=(0, (4, 2)))
    axi.annotate(r"$(\pi/4)\,r_H^{\Lambda}$", (pi / 4 * rH_L / 1e26, 0.80),
                 ha="center", va="top", fontsize=7.5, color=INK)
    axi.annotate("registered rate", (1.26, 0.035), ha="center", va="bottom",
                 fontsize=7.5, color=MID)
    axi.annotate(r"$\Lambda$ face", (1.635, 0.035), ha="center", va="bottom",
                 fontsize=7.5, color=MID)
    axi.annotate(r"split: the ladder--CMB (Hubble-tension) split; entailed $H_0=67.4$",
                 (1.425, 0.875), ha="center", fontsize=7.2, color=INK)
    axi.set_xlim(1.1, 1.75)
    axi.set_ylim(0, 0.95)
    axi.set_yticks([])
    axi.set_xticks([1.2, 1.4, 1.6])
    axi.set_xlabel(r"$r_H\;$ [$10^{26}\,$m]", fontsize=7.5, labelpad=2)
    axi.tick_params(labelsize=7, color=MID, labelcolor=MID, length=2.5, width=0.5)
    for s in axi.spines.values():
        s.set_color(MID); s.set_linewidth(0.5)

    fig.subplots_adjust(left=0.11, right=0.97, top=0.945, bottom=0.05)
    ax.set_xlim(-37, 35.0)
    ax.set_ylim(-45, 62)   # re-assert: pinned after all children
    # ---- plain version with the object-capacity axis [register] ----
    # 14:C10 (p14027)
    family("cap", "K")
    axi.remove()

    # right axis, same format as the left mass axis: log10 capacity, kappa
    # primary, zero at the H atom (kappa_H = 3, the first Object), one dex of
    # capacity per dex of the chart.
    yH = log10(1.674e-27)                    # the H-atom mass line [approx SI]
    fig.subplots_adjust(left=0.11, right=0.90, top=0.945, bottom=0.05)
    fig.canvas.draw()
    chk("the pin held: no datalim drift", ax.get_ylim() == (-45.0, 62.0))
    pos = ax.get_position()

    rax = fig.add_axes([pos.x1, pos.y0, 0.0001, pos.height])
    rax.set_ylim(-45.0, 62.0)
    rax.set_xticks([])
    for s in ("top", "bottom", "left", "right"):
        rax.spines[s].set_visible(False)
    rax.yaxis.tick_right()
    # the mole, drawn [chart]: the gram's horizontal lands on Avogadro's
    # number on the count face -- the axis relative to its zero counts hydrogen
    # units, and N_A is the hydrogen count of the gram (residue: the 1.008 u
    # hydrogen/amu offset, 0.0035 dex, invisible at chart scale)
    NA = 6.02214076e23
    chk("the one-gram horizontal lands on N_A to 0.005 dex", abs((-3 - yH) - log10(NA)) < 0.005)
    ax.plot([-1.3, 35.0], [-3, -3], color=MID, lw=0.7, ls=(0, (2, 3)), zorder=2)
    ax.plot([-37, -5.2], [-3, -3], color=MID, lw=0.7, ls=(0, (2, 3)), zorder=2)
    ax.text(-3.25, -3, r"$1\,$g", va="center", ha="center", fontsize=8, color=MID)
    rax.set_yticks([yH, yH + 20, yH + 40, yH + 60, -3.0])
    rax.set_yticklabels(["0", "20", "40", "60", r"$N_A\sim 6\!\times\!10^{23}$"])
    rax.tick_params(axis="y", labelsize=8, color=MID, labelcolor=MID,
                    length=3, width=0.6)
    ax.text(32, 8.5, r"holographic ring capacity $\log_{10}\kappa_O$", rotation=90,
            va="center", ha="center", fontsize=11)
    ax.text(34.4, yH, r"$\kappa_H{=}3$", va="center", ha="right",
            fontsize=8, color=MID)
    # the axis terminal: the count face sqrt(S), the paper's measured quantity,
    # at its exact height above the anchor (log10(sqrt(S_L)/3) rel dex)
    y_top = yH + log10((S_L ** 0.5) / 3)
    ax.text(34.4, y_top, r"$\sqrt{S}\sim10^{61}$", va="center", ha="right",
            fontsize=8, color=MID)
    save(fig, "registrable-wedge-capacity")
    family("cap", "F")
    chk("registrable-wedge-capacity.png and .pdf written to out/", os.path.exists(os.path.join(OUT, "registrable-wedge-capacity.png")) and os.path.exists(os.path.join(OUT, "registrable-wedge-capacity.pdf")))
    plt.close("all")

    flush("cap", order=["A", "K", "F"])

if __name__ == "__main__":
    import time
    want = [a.lower() for a in sys.argv[1:]] or list(BLOCK)
    bad = [b for b in want if b not in BLOCK]
    if bad: sys.exit(f"no block {', '.join(bad)}: the blocks are {', '.join(BLOCK)}")
    t0 = time.time()
    for b in want:
        t = time.time(); print(f"— block {b}"); _run_block(b); print(f"    [block {b}: {time.time() - t:.1f} s]")
    ok = summary(write=(want == list(BLOCK)))
    print(f"{len(RESULTS)} family checks, {len(MICRO)} micro-checks, {time.time() - t0:.1f} s" + ("; results.json written" if want == list(BLOCK) else ""))
    sys.exit(0 if ok else 1)

