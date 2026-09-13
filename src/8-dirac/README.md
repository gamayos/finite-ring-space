# 8-dirac validation package

Validation package of *Schrödinger and Dirac Dynamics over Finite Substrate* (Akhtman, 2026), `8-dirac` of the
FRC corpus. Eight block scripts, 52 family checks over 3 848 exact micro-checks, driven by `8-dirac-main.ipynb`
(Google Colab, *Runtime → Run all*, ≈ 1 min) or by `run_all.py`. Pure Python, exact integer arithmetic over F_p and
K = F_p[w]/(w² − ν): no floats, no random sampling.

Every family check is the labelled claim of a script's docstring (`o2.C3`, `o8.X5`, …) and names the row(s) of the
paper's predicate ledger it witnesses (the paper's Section "Machine verification and predicate ledger", 46 rows in
blocks A–F, V, O, cited as `8:XN`; public copy `docs/8-dirac/8-dirac-ledger.html`); the ledger's source column cites
the check ids in return. Master-ledger rows of the corpus reached through the paper rows: `00:C3`, `00:C8`, `00:B10`.

[![Open In Colab](https://colab.research.google.com/assets/colab-badge.svg)](https://colab.research.google.com/github/gamayos/finite-ring-space/blob/main/src/8-dirac/8-dirac-main.ipynb)

## In-tree

| script | families | micro-checks | claims backed |
|---|---|---|---|
| `worked_checks.py` (over `finite_checks.py`) | fin.S1–S3 | — | the F_13 worked examples: power-map counts (Prop `power-map-count`, 8:E2); the Cayley step of H = −Δ, U¹³ = I, every trace-zero parameter admissible with order 13, unitarity (Ex `cayley-13`, Thm `cayley-preservation`, 8:C4, C6, E3); the Dirac example — Clifford, boost formulas, transported gammas with A = 10, B = 2, covariance on a sample field (Ex `dirac-13`, Props `clifford`, `spin-conjugation`, `transported-dirac-form`, Cor `boost-covariance`, 8:D2, D6–D8, D12) |
| `shell_checks.py` | shell.Z1–Z4 | 68 | Thm `zonal` exhaustively over windings and cycle points (8:F3), the sector separation (8:F4), the F_17 numbers (8:D5, D12) |
| `o2_checks.py` | o2.C1–C9 | 1048 | Lemmas `class-datum`, `canonical-nu`: the square classes of every named residue on all symmetry-complete shells p < 2000, the anchors F_13, F_17 and the lab Carrier (8:B2–B4, D5, D12) |
| `o7_checks.py` | o7.P1–P6 | 1735 | Thms `parity`, `even-transport`, Cor `two-seats`: the parity grading exhaustive over every primitive root of the worked shells, ν = c²·(2g), the chart-grading clause (8:B4–B6) |
| `o134_checks.py` | o134.O1a–O4d | 907 | Lemma `boost-torus` by exhaustive enumeration with Hilbert 90 per element, Thm `cayley-transform`, Thm `period-dichotomy` with attained orders, the quintic datum, the minimality of F_17 (8:C5, C6, D5, D12, E4) |
| `o8_checks.py` | o8.X1–X8 | 55 | Lemma `spinor-form` at p = 5, 13, 17 with the γ⁰-twist failure, Thm `dirac-evolution` in 1+1 at p = 5, the commuting composite of Cor `sectors`, the spin-lift transport of Prop `two-diracs` (8:D9–D11, F4) |
| `latitude_checks.py` | lat.L1–L5 | 35 | the latitude indices of the shell reading on F_13, F_17 and the lab Carrier (8:F2) |
| `o9_signature_counts.py` | o9.S1–S4 | — | Remark `signature-record`: zero counts of the Euclidean and Q_ν forms on p < 60, 2353/2041 at p = 13, the collapse over K (8:B7) |
| `dcommon.py` | — | — | the registry: micro-check collector, family aggregation, `LEDGER` (check → rows), `LABELS`, `results.json` |

Run: `python3 run_all.py`. Each block also runs alone (`python3 o8_checks.py`). Rebuild the notebook: `python3 make_notebook.py`.

## Provenance

The seven scripts of the paper's `supplement/` are kept as they were written, wrapped in a `run()` and reporting to the
registry instead of their own counters (their micro-check labels are unchanged; a failure prints and is recorded, the
family fails, the run continues). `o8_checks.py` is the supplement's current version (family X8, the spin-lift
transport of the spinor form, and one further X2 check — the public copy had lagged it); `o9_signature_counts.py`
was in the supplement and not in the package. `finite_checks.py` is unchanged and remains runnable on its own; its
booleans are made predicates by `worked_checks.py`.

## Predicate ledger

Rows B1, C1, C3, D1, D4, E1, F1 are definitions; A1–A6 imports; B8, D13, F5 realisations with falsifiers; V1–V3 the
verification rows; O1 the open classification of the admissible set. Check → row: see `dcommon.LEDGER`; every T row
of blocks B–F except the proof-only rows (C2, D3) names its witness.
