# 13-epi validation package

Validation package of *Finite Field Realisation of the Classical Constants π and e* (Akhtman, 2026), `13-epi` of the
FRC corpus. Five blocks, 40 family checks over ≈ 800 exact micro-checks, driven by `13-epi-main.ipynb` (Google Colab,
*Runtime → Run all*, ≈ 45 s) or by `run_all.py`. Integers, residues and exact rationals throughout: the external
targets e and π enter only as certified rational brackets of the paper's own chains (the subfactorial chain, the
Machin chain), and the binary64 constants only as the objects of study of the readout theorems, compared exactly
with correctly rounded framed rationals. No floating-point reference value of either constant decides a check.

Every family check is one labelled claim of a script and names the row(s) of the paper's predicate ledger it
witnesses (the paper's Section "Machine verification and predicate ledger", rows cited as `13:XN`; public copy
`docs/13-epi/13-epi-ledger.html`); the ledger's source column cites the check ids in return. Where a row is proved in
Lean (`lean/FrcCore/Epi.lean` with no axioms, or `lean/FrcLedger/Epi.lean` on Mathlib), the check here is the instance
the reader can run. Master-ledger rows of
the corpus reached through the paper rows: `00:B8`, `00:B9`, `00:C13`, `00:C14`, `00:B1`, `00:C24`, `00:C26` (the paper's hypotheses Y1–Y3 have no live master row: the former T7–T9 were withdrawn 17 Sep 2026).

[![Open In Colab](https://colab.research.google.com/assets/colab-badge.svg)](https://colab.research.google.com/github/gamayos/finite-ring-space/blob/main/src/13-epi/13-epi-main.ipynb)

## In-tree

| script | families | micro-checks | claims backed |
|---|---|---|---|
| `validate_e.py` | e.R1–R4, W1–W5, S1, A1, N1 | 82 | the derangement chain: enclosure with the sharper constant 8 (n ≤ 60), the binary64 readout ε_18 with ε_17 failing, the 100-digit determination at n = 70, the feasibility counts 11/18/70 (13:D3–D5); the wall of e on seven shells — Wilson reflection, !(p−1) ≡ K(p), K(p) ≢ 0, antiperiodicity, the series duals with the broken group law, the p = 13 residue line 2, 3, 7, 11, 1, 6, blind, 2, 8, 10, 9, the tail identity and the collision reading of the blind set (13:F1–F4, F6, F8); the blind-set distribution over 501 primes (13:F5); the radian-calibration scan over the 39 175 shells p ≡ 1 (mod 4) below 10⁶ — 260 shells within 0.01, the best six — decided with π as a Machin bracket (13:H4); the null experiment, 94 of 210 (13:H5) |
| `validate_pi.py` | pi.R1–R4, W1–W2, S1–S3, L1, V1 | 98 | the Wallis enclosure to n = 300 with the width identity, the p = 13 line 4, 5, 10, 9, 6, 11, the Machin readout M_10 with the bound and the 100-digit determination at N = 71, the Gregory brackets, the arcsin tail bound (13:E2–E4, G8); the legibility window and the −2 terminus on seven shells and for p ≡ 3 (mod 4) (13:G1, G2); Morley, the second-order formula, q_p(4) ≡ 2q_p(2), the π-Wieferich set {5, 45827} below 10⁶ (13:G4); the π-Wieferich condition in three forms with q_p(4) = 2q_p(2) + p·q_p(2)² exactly, Eisenstein's harmonic form and the OEIS A355959 form (13:G10); the Lucas revivals with [v_p] ≡ 8 (13:G5); the first-order arcsin vanishing on 428 primes with σ_3 = 1 (13:G6) |
| `validate_pi2.py` | pi2.A1–A2, B1–B2, C1–C4, D1–D2 | 551 | Gauss's congruence and the two-squares invariant on 211 primes (13:G3); Sun's supercongruence and the third-order Bernoulli law on sixty primes, the blind-range Euler congruence (13:G7); the proof ingredients of the first-order vanishing — binomial transfer, Lerch, the Wallis evaluation, A + B = 2L by formal-antiderivative bookkeeping (13:G6); the first revival to p² (13:G5) |
| `validate_towers.py` | tow.E, P, C, O, H, W | 72 | the fixed-shell towers of e and π on p = 13, 29 (13:F7, G9, B3); the Cayley composition law exhaustively (13:C3); orientation transport over the units (13:B2); the height run over all 500 shells p ≤ 8009 — the calibration pin at height 2, the band H ≤ 2√p, 68 small-height shells, the height-2 set {13, 1933, 4177, 5857} (13:J2, J3); the wrap-free window, the pinning relation, the half-turn tautology, the quarter-turn pin (13:J1, J2, G2, H2, I4) |
| `kurepa_wall.c` (via `kurepa_wall.py`) | kur.K1 | 3 | !(p−1) ≡ K(p) (mod p) and K(p) ≢ 0 (mod p) for all 22 043 odd primes p < 2.5·10⁵, one O(p) pass per prime in 128-bit modular arithmetic; compiled on the fly (a pure-Python pass to 2·10⁴ runs without a compiler and says so) (13:F2, Y1) |
| `pi_wieferich.c`, `pi_wieferich128.c` (standalone) | — | — | the π-Wieferich search 4^(p−1) ≡ 1 + p (mod p²), i.e. 2q_p(2) ≡ 1 (mod p): the 64-bit program covers p < 2³² (203 280 220 odd primes, hits {5, 45827}, 74 s); the 128-bit Montgomery program covers any range below 2⁶³ and self-checks against the 64-bit path — run over [2³², 2³⁵), 1 276 926 058 primes, no hit (43 min); the recorded runs are `results_wieferich.txt`. The OEIS entry A355959 records no third member below 1.08·10¹¹ (13:G10, Y2) |
| `epicommon.py` | — | — | the registry: micro-check collector, family aggregation, `LEDGER` (check → rows), `LABELS`, `results.json` |

Run: `python3 run_all.py` (≈ 40 s; 30 s of it the C pass). Each block also runs alone (`python3 validate_pi.py`).
Rebuild the notebook: `python3 make_notebook.py`. `results_e.txt`, `results_pi.txt`, `results_pi2.txt` are the
recorded outputs of the memorandum runs (July 2026) and stay as the source record; the package run writes
`results.json`.

## Provenance

`validate_e.py`, `validate_pi.py`, `validate_pi2.py` are the scripts of the source memoranda, renamed to the suite
form at the manuscript (round-01 and round-02 amendments of July 2026: the p = 13 showcase line, the p = 3 exception,
the mod-p² range to 300, the Bernoulli law, the formal-antiderivative route to m ≤ 60, the unified results files);
`validate_towers.py` is new with the manuscript (round-02: the full 500-shell height run); `kurepa_wall.c` is the
memorandum's C pass; `pi_wieferich.c` and `pi_wieferich128.c` are the search programs of 18 September 2026 (with G10). The package form (September 2026) keeps every computation as written and turns the scripts'
PASS/FAIL lines and the paper's stated figures into registry predicates: a failing micro-check prints and fails its
family without stopping the run. Two changes of substance: the radian-calibration scan now decides |θ − 1| < 0.01 and
the ordering of the best shells in exact rational arithmetic with π as a Machin bracket of width < 10⁻¹⁰⁰ (the paper's
stated protocol; the memorandum used `math.pi`), and the e-side p = 13 residue line, the arcsin tail bound and the
universality of [v_p] ≡ 8 are added as predicates. The pattern hunts and Gauss sums of `validate_pi.py` and the
Fermat-quotient moments are printed as the paper's [approx] diagnostics and decide nothing. The MIXED classification
of the memorandum README therefore no longer applies: every family is EXACT.

## Predicate ledger

Rows A1–A8 imports; B1, B4, C1, C4, D1, E1, H1, J4 definitions (the two selector normalisations C1, C4 are the
paper's two D moves); D2, H3 proof-only rows; Y1–Y3 the open walls (hypotheses, block Y, tag O) (Kurepa's hypothesis, the π-Wieferich infinitude
and the Bernoulli law beyond p < 300, the e–π dichotomy as theorem). Check → row: `epicommon.LEDGER`.
