# 10-dimensions validation package

Validation package of *Dimensional Analysis over Finite Holographic Substrate* (Akhtman, 2026), `10-dim` of the FRC
corpus. Two exact suites, 13 family checks over 210 exact micro-checks, driven by `10-dimensions-main.ipynb` (Google
Colab, *Runtime → Run all*, ≈ 10 s) or by `run_all.py`. Pure Python — integers, residues, exact rationals; no floats,
no random sampling.

Every family check is a layer of `verify_domains.py` (A–H) or a claim of `check_lift.py` (L1–L5) and names the row(s)
of the paper's predicate ledger it witnesses (the paper's Appendix B "Machine verification and predicate ledger", 45 rows
in blocks A–G, V, T, cited as `10:XN`; public copy `docs/10-dimensions/10-dimensions-ledger.html`); the ledger's source
column names the witness script (the family checks are listed on the public page from `results.json`). Where a row is proved in Lean (`lean/FrcCore/Dimensions.lean` with no axioms, or
`lean/FrcLedger/Dimensions.lean` on Mathlib), the check here is the instance the reader can run. Master-ledger rows of the corpus reached through the paper rows: `00:D7`, `00:C12`,
`00:C13`, `00:C8`, `00:B10`.

[![Open In Colab](https://colab.research.google.com/assets/colab-badge.svg)](https://colab.research.google.com/github/gamayos/finite-ring-space/blob/main/src/10-dimensions/10-dimensions-main.ipynb)

## In-tree

| script | families | micro-checks | claims backed |
|---|---|---|---|
| `verify_domains.py` | dom.A–H | 200 | A the shell datum and domain algebra on F_13 (32; 10:C2, C3, D2, D6, F2, F4, G1, G3); B the quartet at the unit face in exact rationals (30; 10:E2, E3); C the defining congruences on the lab Carrier (13; 10:E4); D both Carriers, faces, the minimality scan (13, 233) with counterfactuals, temperature and the Unruh closure, the crossing-degree embedding (50; 10:E4, E5, E9, F3, G1); E the covariance witnesses (18; 10:C5); F the window bound, the σ-twisted action, the dualities (15; 10:C5, D1); G realized action, the window ladder, meridian transport, pair canonicity (15; 10:C5, D2, G2); H the pair layer and representative inertness (27; 10:E4, E5) |
| `check_lift.py` | lift.L1–L5 | 10 | Proposition `lift`: the operator four-cycle, the chart shadow, the record map, the Carrier face of order four, the invariance classification — shells (13, 2), (173, 3), Carriers 233 and 2 408 561 (10:D3, C5) |
| `check_gates.py` | — | 105 gates | the manuscript's source gates (required tokens, verbatim bans) on `sections/*.tex` and `mdpi.tex`; runs in the corpus tree, where the manuscript lives — not part of `run_all.py` (10:V3) |
| `dimcommon.py` | — | — | the registry: micro-check collector, family aggregation, `LEDGER` (check → rows), `LABELS`, `results.json` |

Run: `python3 run_all.py`. Each suite also runs alone (`python3 verify_domains.py`). Rebuild the notebook:
`python3 make_notebook.py`.

## Provenance

`verify_domains.py` is the paper's suite as written (the 200 micro-check names unchanged), wrapped in a `run()` that
reports to the registry instead of asserting: a failing micro-check prints, the layer fails, the run continues.
`check_lift.py` is the corpus tree's current version (the public copy had lagged it), its five claims reported per
instance. Structures exercised: the toy shell F_13 (κ = 3), p = 29, 173, 229; the Carriers Ω = 233 (S = 58) and the
laboratory Carrier Ω = 2 408 561 (S = 602 140).

## Predicate ledger

Rows B1–B4, C1, C4, D4, E8 are definitions (C6 and E6 composite); A1–A6 imports; D5, D7, E1 realisations with
falsifiers; E7 the Ω-hard Carrier register; V1–V5 the verification rows (V5 the two Lean libraries); T1 the open electromagnetic domain (a task, block T).
Check → row: `dimcommon.LEDGER`.
