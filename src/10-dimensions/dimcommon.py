"""
dimcommon.py — shared registry for the 10-dimensions validation package
========================================================================
"Dimensional Analysis over Finite Holographic Substrate" (Akhtman, 2026), validation package of the FRC corpus
(finite-ring-space/src/10-dimensions). Every check is exact: integers, residues, exact rationals; no floats, no
random sampling. The suite verify_domains.py is organised in eight layers A–H, each a family of micro-checks; the
lift script check_lift.py decides the five claims L1–L5 of Proposition `lift` on two shells and two Carriers. A
family is one check of the registry, identified as <script tag>.<family> (dom.A … dom.H, lift.L1 … lift.L5), and
names the row(s) of the paper's predicate ledger it witnesses (LEDGER; rows cited as 10:XN). The ledger's source
column names the witness script; the family checks are listed on the public page from results.json. Master-ledger rows reached through the paper rows: 00:D7 (10:D7),
00:C12 (10:F3), 00:C13 (10:E9, 10:G2), 00:C8 (10:E4), 00:B10 (10:E5).

check_gates.py (105 source gates on the manuscript's text) runs in the corpus tree only, where sections/*.tex
live; it is not part of run_all.py.
"""
import os, json, sys
from collections import OrderedDict

RESULTS = []
MICRO = []             # (script tag, family, label, ok)

LEDGER = {
    "dom.A": "10:C2, 10:C3, 10:D2, 10:D6, 10:F2, 10:F4, 10:G1, 10:G3",
    "dom.B": "10:E2, 10:E3",
    "dom.C": "10:E4",
    "dom.D": "10:E4, 10:E5, 10:E9, 10:F3, 10:G1",
    "dom.E": "10:C5",
    "dom.F": "10:C5, 10:D1",
    "dom.G": "10:C5, 10:D2, 10:G2",
    "dom.H": "10:E4, 10:E5",
    "lift.L1": "10:D3", "lift.L2": "10:D3", "lift.L3": "10:D3", "lift.L4": "10:D3", "lift.L5": "10:C5, 10:D3",
}

LABELS = {
    "dom.A": "shell datum and domain algebra on F_13: frame datum (g = 2, i = −g^κ, π = 2κ, 4κ = p−1); the group law, inverses and grading of D_p = Z_p × Z_{p−1}; the internal flag I_q = [T]^κ unique of order four, no flag of space, horizon-inaccessible, covariant; realization a homomorphism; the derived domains (m, F, S, G, Compton, Planck area, Schwarzschild, orbital frequency); fibrewise addition and local recovery at H = 5",
    "dom.B": "the quartet at the unit face: exponent-vector relation lattice over {ℓ_P, t_P, ħ} (both faces of c and ħ differ by ℓp = tE; rank two; k_B and ℓE add nothing); exact-rational instantiation of every stated equality (|k_B|c = ħ, m_P, G, Θ_P, {c, ħ, G} ↔ quartet); 4 − 1 = 3 degrees of freedom; flag positions (0,0,1,1)",
    "dom.C": "the defining congruences on the lab Carrier Ω = 2 408 561 (S = 602 140): admissibility; 2G ≡ −1 unique; ħ² ≡ −1, k_B² ≡ −2, 2c² ≡ 1 with their exact root pairs; G ≡ −c², G² ≡ 4⁻¹, h ≡ −ħ; m_P² ≐ Ω ≡ 0",
    "dom.D": "both Carriers (233 and the lab Carrier): the congruence-and-closure system, ħcG⁻¹ landing in the k_B pair; the representative annex; the admissibility minimality scan certifying (13, 233) with the counterfactuals; [Θ] = [L][T]⁻² and the Unruh closure; the crossing-degree embedding injective and windowed-faithful",
    "dom.E": "covariance: the naive character ill-defined on the modular projection; (p−1, 0) trivial character yet non-neutral; the ε-composition failure; window covariance below the bound; pushforward-invariant labels {0, π}; the quarter-turn fix/swap criterion ε ≡ ±1 (mod 4); the index-two sublattice ⟨c, ħ, G⟩ (det −2)",
    "dom.F": "the (0, π) witness forcing H < 2κ; the σ-twisted action equivariant by full sweep on p = 13 and 229 with the plain-lift failure; σ multiplicative mod 4; δ_S, δ_C involutions, δ_C carrying [L] ↦ [p], [T] ↦ [E]",
    "dom.G": "realized action against the Z³-representative failure; the flagged label (0, 0; 1) moving under ε = −1; the window ladder 2√κ < κ/2 < κ < 2κ nested for every κ ≥ 17 and failing for κ = 3; (2√κ)² = p−1, (2√S)² = Ω−1; the flagged ratio F/a; meridian transport (L T^κ)^p = I_q on three shells; both roots on both Carriers",
    "dom.H": "the pair layer: pair multiplication well defined; the linkage {±k_B}{±c} = {±ħ} derived at pair level; ħcG⁻¹ in the k_B pair via (ħcG⁻¹)² ≡ −2; representative inertness — exactly the four assignments with σ_ħ = σ_c σ_k admissible, a (Z/2)², every identity holding on each; the ħ-flip relabelling of {ħ, h}",
    "lift.L1": "operator four-cycle: F = iW on F_p^{p−1}, F² = J, F⁴ = I, F² ≠ I (p = 13, 173)",
    "lift.L2": "chart shadow of order two: F exchanges the two dual charts, J exchanges none; the cardinal skeleton acts on charts as s mod 2",
    "lift.L3": "record map s ↦ I_q^s an isomorphism Z_4 → the flag subgroup {0, κ, 2κ, 3κ}; the quotient by {0, 2κ} returns s mod 2",
    "lift.L4": "Carrier face: ħ² = −1 (mod Ω), ħ⁴ = 1, ħ² ≠ 1 — the crossing quantum has order four, never two (Ω = 233, 2 408 561)",
    "lift.L5": "invariance on the realized lattice: {u : εu = u for every admissible ε} = {0, 2κ}; witnesses (κ,1) ↦ 2κ and (−κ,1) ↦ 0 invariant, (0,1) ↦ κ not, (0,2) ↦ 2κ invariant",
}

SCRIPT = {"dom": "verify_domains", "lift": "check_lift"}

# the deciding family of each witnessed row: the one whose checks decide the row's statement (the other families
# that touch the row are corroboration, listed by row() from the records)
ROWS = {
    "10:C2": "dom.A", "10:C3": "dom.A", "10:C5": "dom.E", "10:D1": "dom.F", "10:D2": "dom.A", "10:D3": "lift.L1",
    "10:D6": "dom.A", "10:E2": "dom.B", "10:E3": "dom.B", "10:E4": "dom.C", "10:E5": "dom.H", "10:E9": "dom.D",
    "10:F2": "dom.A", "10:F3": "dom.D", "10:F4": "dom.A", "10:G1": "dom.A", "10:G2": "dom.G", "10:G3": "dom.A",
}
_FAM = [None, None]
_RAN = set()                                            # scripts already run in this session (row() runs each once)

def markers():
    """row label -> (script file, line) of its `# row …` marker: the line of the check that decides the row."""
    import re
    out = {}
    for f in sorted(set(SCRIPT.values())):
        for i, line in enumerate(open(os.path.join(os.path.dirname(os.path.abspath(__file__)), f + ".py"), encoding="utf-8"), 1):
            m = re.match(r"\s*# row (.*)", line)
            if m:
                for lab in m.group(1).split(","): out.setdefault(lab.strip(), (f + ".py", i))
    return out

def row(label, lines=14):
    """Verify one ledger row: run the scripts of the families that cite it (each once per session), print the deciding
    check's source (from its `# row` marker) and every family record that cites the row, and return True iff all pass."""
    fam = ROWS.get(label)
    if fam is None:
        print(f"{label}: no python witness (see the row's Lean witness or its source)"); return None
    script = SCRIPT.get(fam.split(".")[0], fam)
    citing = {SCRIPT.get(f.split(".")[0], f) for f, rows in LEDGER.items() if label in [t.strip() for t in rows.split(",")]}
    for sc in sorted({script} | citing):                  # the deciding script and every script whose families cite the row, each once per sessionthe driver row runs every suite
        if sc not in _RAN:
            import importlib
            mod = importlib.import_module("." + sc, __package__) if __package__ else importlib.import_module(sc); mod.run(); _RAN.add(sc)
    here = os.path.dirname(os.path.abspath(__file__)); mk = markers().get(label)
    if mk:
        src = open(os.path.join(here, mk[0]), encoding="utf-8").read().split("\n")
        print(f"— {mk[0]}:{mk[1]} (the check that decides {label}; family {fam})")
        for j in range(mk[1] - 1, min(mk[1] - 1 + lines, len(src))): print(f"{j + 1:5d}  {src[j]}")
    else:
        print(f"— {script}.py (the whole script witnesses {label})")
    recs = [r for r in RESULTS if label in [t.strip() for t in r["rows"].split(",")]]
    ok = all(r["ok"] for r in recs)
    for r in recs:
        role = "(the script's family)" if "." not in fam else "(deciding)" if r["id"] == fam else "(corroborating)"
        print(f"  [{'PASS' if r['ok'] else 'FAIL'}] {r['id']:8s} {role:22s} {r['detail']}")
    print(f"{label}: {'VERIFIED' if ok and recs else 'FAILED'} — {len(recs)} family record(s)")
    return ok

def verify_all():
    """Run every script of the package (those already run in this session are not re-run) and print the summary;
    True iff every family check passed."""
    import importlib
    for sc in sorted(set(SCRIPT.values())):
        if sc not in _RAN:
            mod = importlib.import_module("." + sc, __package__) if __package__ else importlib.import_module(sc); mod.run(); _RAN.add(sc)
    return summary(write=False)

def family(tag, fam):
    _FAM[0], _FAM[1] = tag, fam

def chk(label, ok, tag=None, fam=None):
    """A micro-check, recorded under the current (tag, family); never exits."""
    MICRO.append((tag or _FAM[0], fam or _FAM[1], label, bool(ok)))
    if not ok:
        print(f"    FAIL: {label}")

def flush(tag, order=None):
    fams = OrderedDict()
    for t, fam, label, ok in MICRO:
        if t == tag:
            fams.setdefault(fam, []).append(ok)
    for fam in (order or fams):
        oks = fams.get(fam, [])
        check(f"{tag}.{fam}", ok=bool(oks) and all(oks), detail=f"{len(oks)} exact micro-checks")

def check(pid, ok, detail="", kind="EXACT", label=None):
    ok = bool(ok)
    rows = LEDGER.get(pid, "")
    label = label or LABELS.get(pid, pid)
    RESULTS.append({"id": pid, "rows": rows, "script": SCRIPT.get(pid.split(".")[0], pid.split(".")[0]), "label": label, "ok": ok, "detail": detail, "kind": kind})
    print(f"  [{'PASS' if ok else 'FAIL'}] {pid:8s} {kind:5s} [{rows}] {label[:110]}" + (f"  --  {detail}" if detail else ""))
    return ok

def summary(write=True):
    n_ok = sum(r["ok"] for r in RESULTS)
    print(f"\nSUMMARY: {n_ok}/{len(RESULTS)} checks passed ({len(MICRO)} exact micro-checks)" + ("" if n_ok == len(RESULTS) else "  <-- FAILURES"))
    if write:
        with open("results.json", "w") as f:
            json.dump(RESULTS, f, indent=1, ensure_ascii=False)
    return n_ok == len(RESULTS)
