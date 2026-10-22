# 13-epi validation package

Validation package of *Finite Field Realisation of the Classical Constants π and e* (Akhtman, 2026), `13-epi` of the
FRC corpus. One script, `epi.py` (since 24 September 2026; the registry and the six suites merged, the two C passes beside it), seven blocks, 47 family checks over 861 exact micro-checks, driven by `frc-13-epi.ipynb` (Google Colab: one cell per ledger predicate, any cell on its own, or
*Runtime → Run all*, ≈ 60 s) or run whole. Integers, residues and exact rationals throughout: the external
targets e and π enter only as certified rational brackets of the paper's own chains (the subfactorial chain, the
Machin chain), and the binary64 constants only as the objects of study of the readout theorems, compared exactly
with correctly rounded framed rationals. No floating-point reference value of either constant decides a check.

Every family check is one labelled claim of a block and names the predicate(s) of the paper's predicate ledger it
witnesses (Appendix A "Predicate ledger and machine verification", predicates cited as `13:XN`; public copy
`docs/13-epi/index.html`); the ledger's source column links, for each machine-verified predicate, the script at the deciding family's marker (`epi.py#<key>`) and the Lean module at the predicate's declaration. Where a predicate is proved in
Lean (`lean/FrcCore/Epi.lean` with no axioms, or `lean/FrcMathlib/Epi.lean` on Mathlib), the check here is the instance
the reader can run. Master-ledger rows of
the corpus reached through the paper rows: `00:B8`, `00:B9`, `00:C13`, `00:C14`, `00:B1`, `00:C24`, `00:C26`, and `00:Z4` through Z1, Kurepa's certificate (block Z since 12 October 2026: the former hypotheses Y1 and Y3 as the Ω-hard certificates Z1 and Z2, keys kept; Z2 has no master row).

[![Open In Colab](https://colab.research.google.com/assets/colab-badge.svg)](https://colab.research.google.com/github/gamayos/finite-ring-space/blob/main/src/13-epi/frc-13-epi.ipynb)

## In-tree

| block | families | micro-checks | claims backed |
|---|---|---|---|
| `e` | e.R1–R4, P1, T1, W1–W5, S1, A1, N1 | 99 | the rencontres census of S_n for n ≤ 8 and the polynomial identity to n = 60 (13:C2); the tail form !n = n!/e + (−1)ⁿδ_n with its strict bounds to n = 60 (13:D2); the derangement chain: enclosure with the sharper constant 8 (n ≤ 60), the binary64 readout ε_18 with ε_17 failing, the readout plateau thresholds below 200 bits exact (n1 ≤ n0 + 1, n1 = n0 + 1 at eight precisions), the 100-digit determination at n = 70, the feasibility counts 11/18/70 (13:D3–D5); the wall of e on seven shells — Wilson reflection, !(p−1) ≡ K(p), K(p) ≢ 0, antiperiodicity, the series duals with the broken group law, the p = 13 residue line 2, 3, 7, 11, 1, 6, blind, 2, 8, 10, 9, the tail identity and the collision reading of the blind set (13:F1–F4, F6, F8); the blind-set distribution over 501 primes (13:F5); the radian-calibration scan over the 39 175 shells p ≡ 1 (mod 4) below 10⁶ — 260 shells within 0.01, the best six — decided with π as a Machin bracket, and no shell below 10⁶ exactly calibrated (13:H4, H3); the null experiment, 94 of 210 with the orientation of the quarter-turn free, 54 with it tied to the generator (13:H5) |
| `pi` | pi.R1–R4, W1–W2, S1–S3, L1, V1 | 99 | the Wallis enclosure to n = 300 with the width identity, the p = 13 line 4, 5, 10, 9, 6, 11, the Machin readout M_10 with the bound and the 100-digit determination at N = 71, the Gregory brackets, the arcsin tail bound (13:E2–E4, G8); the legibility window and the −2 terminus on seven shells and for p ≡ 3 (mod 4) (13:G1, G2); Morley, the second-order formula, q_p(4) ≡ 2q_p(2), the π-Wieferich set {5, 45827} below 10⁶ (13:G4); the π-Wieferich condition in three forms with q_p(4) = 2q_p(2) + p·q_p(2)² exactly, Eisenstein's harmonic form and the OEIS A355959 form (13:G10); the Lucas revivals with [v_p] ≡ 8 (13:G5); the first-order arcsin vanishing on 428 primes with σ_3 = 1 (13:G6) |
| `pi2` | pi2.A1–A2, B1–B3, C1–C4, D1–D2 | 555 | Gauss's congruence and the two-squares invariant on 211 primes (13:G3); Sun's supercongruence and the third-order Bernoulli law on sixty primes in exact rational arithmetic, the law on all 1227 primes below 10⁴ modulo p³ with B_{p−3} by the power sum, the blind-range Euler congruence (13:G7); the proof ingredients of the first-order vanishing — binomial transfer, Lerch, the Wallis evaluation, A + B = 2L by formal-antiderivative bookkeeping (13:G6); the first revival to p² (13:G5) |
| `tow` | tow.E, P, C, O, H, W, D | 88 | the fixed-shell towers of e and π on p = 13, 29 (13:F7, G9, B3); the duality read on p = 13, 29 — the half-turn, the −2 terminus, the quarter invariant, the blind-free window, no exact calibration, the Kurepa residue, 1 in the blind set, K·A ≢ 1 (13:I3); the Cayley composition law exhaustively (13:C3); orientation transport over the units (13:B2); the height run over all 500 shells p ≤ 8009 — the calibration pin at height 2, the band H ≤ 2√p, 68 small-height shells, the height-2 set {13, 1933, 4177, 5857} (13:J2, J3); the wrap-free window, the pinning relation, the half-turn tautology, the quarter-turn pin (13:J1, J2, G2, H2, I4) |
| `kur` (`kurepa_wall.c`, compiled on the fly) | kur.K1 | 3 | !(p−1) ≡ K(p) (mod p) and K(p) ≢ 0 (mod p) for all 22 043 odd primes p < 2.5·10⁵, one O(p) pass per prime in 128-bit modular arithmetic; compiled on the fly (a pure-Python pass to 2·10⁴ runs without a compiler and says so) (13:F2, J6, Z1) |
| `frm` (`frame_invariants.c`, compiled on the fly) | frm.I1 | 7 | the three frame invariants of the two constants on the 4 783 shells p ≡ 1 (mod 4) below 10⁵ — K(p) mod p, q_p(4) mod p, p = a² + b² with a ≡ 1 (mod 4) — every triple exact (p = 13: 10, 6, −3+2i; 1093 the one shell with q_p(4) = 0), the 4×4×4 contingency table of (K/p, q_p(4)/p, φ/π) and its chi-square 59.6 on 63 df exact, the means and variances by certified rational bounds; the independence reading is the paper's [approx] statement (13:I5, Z2) |
| `lab` (pure Python) | lab.Z1, lab.Z2 | 11 | the certificates of block Z on the laboratory Carriers Ω = 233, 30089, 2 408 561 over their own shells, the odd primes p with p² < Ω (5, 39, 243 of them): Kurepa's certificate Z = 0 on each (every shell walked; the Carriers' own residues K(233) ≡ 69, K(30089) ≡ 5260, K(2408561) ≡ 435994), the blind-set sizes and the index condition on the same shells (13:Z1); the calibration minimum over the shells p ≡ 1 (mod 4) decided exactly with π as a Machin bracket — (13, 5), (37, 6), (397, 63) — against the nearest-hit scale, the three frame invariants exact on the 117 shells of 2 408 561 with their correlations as the [approx] reading (13:Z2) |
| `pi_wieferich.c`, `pi_wieferich128.c` (standalone; the record is read by pi.S2) | — | — | the π-Wieferich search 4^(p−1) ≡ 1 + p (mod p²), i.e. 2q_p(2) ≡ 1 (mod p): the 64-bit program covers p < 2³² (203 280 220 odd primes, hits {5, 45827}, 74 s); the 128-bit Montgomery program covers any range below 2⁶³ and self-checks against the 64-bit path — run over [2³², 2³⁵), 1 276 926 058 primes, no hit (43 min); the recorded runs are `results_wieferich.txt`. The OEIS entry A355959 records no third member below 1.08·10¹¹ (13:G4, G10) |

The registry (micro-check collector, family aggregation, `LEDGER` check → predicates, `LABELS`, `PREDICATES`, `results.json`) is the head of the script.

Run: `python3 epi.py` (≈ 45 s; 30 s of it the Kurepa C pass; `results.json` written), or the blocks named: `python3 epi.py pi tow lab`; installed, `python3 -m frc_13_epi`.
Rebuild the notebook: `python3 make_notebook.py`. `results_e.txt`, `results_pi.txt`, `results_pi2.txt` are the
recorded outputs of the memorandum runs (July 2026) and stay as the source record; the package run writes
`results.json`.

## Provenance

Blocks `e`, `pi`, `pi2` are the scripts `validate_e.py`, `validate_pi.py`, `validate_pi2.py` of the source memoranda, renamed to the suite
form at the manuscript (round-01 and round-02 amendments of July 2026: the p = 13 showcase line, the p = 3 exception,
the mod-p² range to 300, the Bernoulli law, the formal-antiderivative route to m ≤ 60, the unified results files);
block `tow` (`validate_towers.py`) is new with the manuscript (round-02: the full 500-shell height run); `kurepa_wall.c` is the
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
paper's two D moves); D2, H3 proof-only rows; Z1, Z2 the Ω-hard certificates (block Z, since 12 October 2026: Kurepa's certificate over the
shells p < √Ω of the totality, and the large-p laws over the same shells — the calibration rate, the joint law of the frame invariants, the
blind-set and index-condition laws — each shell deciding its own case, the check over all shells a count above √Ω that no Subject reaches,
decided on the laboratory Carriers over their own shells by block `lab`) — the π wall's persistence shells are certified one at a
time (13:G4, G10), their frequency a range reading; the e–π dichotomy is a split by kind of chain (13:E5), the three
frame invariants exact on every shell (13:I5). Check → predicate: `epi.LEDGER`; the deciding family per predicate: `epi.PREDICATES` (24 September 2026: `LEDGER` gained the citations the paper's ledger names — E5 for e.R4 and pi.R3, J5 for tow.H, J6 for kur.K1 and pi.S2).

## One cell per predicate

`frc-13-epi.ipynb` (built by `make_notebook.py`, executed) carries one cell per witnessed ledger predicate, addressable by
its stable id (the predicate's accession key, e.g. `p13028` for `13:F2`; the ledger page opens the notebook at the cell). Every cell is self-contained:
it installs the package from the site (`pip install frc-13-epi --find-links https://finitering.space/pkg/` — a named requirement, so pip reports it already satisfied once installed; the sdist `frc-13-epi-<version>.tar.gz`
`src/make_pkg.py` writes under `docs/pkg/` at each site build; import name `frc_13_epi`, `__init__.py` exporting
`predicate`; the sdist carries the `.py` files only, so the two C passes run their pure-python fallback there), states the predicate and runs `predicate("13:F2")`: the blocks of the families that cite the predicate run once per session (the deciding family is `epi.PREDICATES`), the check
that decides the predicate is printed from the script's own source — the line under its `# 13:F2 (p13028)` marker — and every family
record citing the predicate is listed with its verdict. The markers in `epi.py` are the lines the
ledger page's source glyph opens (`docs/py/epi.html#<key>`). The predicates' Lean counterparts are the
declarations named by their keys (`p13028`) at the end of `lean/FrcCore/Epi.lean` and `lean/FrcMathlib/Epi.lean`
(`lean/make_predicates.py`), one per predicate, with the paper's module as one executable file for the web editor.
