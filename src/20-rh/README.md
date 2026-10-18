# 20-rh validation package

Validation package of *Riemann Hypothesis over Finite Holographic Substrate* (Akhtman & Voether, 2026; the first version of the
preprint, *Riemann Hypothesis over the Holographic Substrate: a Finite-Field Dictionary and the Screen Reading*), `20-rh` of the
FRC corpus. One script, `rh.py`, three blocks, 107 checks (91 EXACT, 5 [approx], 11 [chart]), driven by `frc-20-rh.ipynb`
(Google Colab: one cell per python-witnessed ledger predicate, any cell on its own, or *Runtime → Run all*, under a minute) or run
whole; the paper's two drawn figures regenerated into `figures/paper/` as the blocks run.

The package was rewritten with the paper on 17 October 2026 (`20-rh-20260608/reports/blueprint-20261017.md`) and extended on
18 October (`reports/blueprint-20261018.md`): the drive theorem (A19; row 20:E15) and the energy domain as a circle (A20; row
20:B14), the names of the revision (the energy domain, the Parseval identity, the intensity), the figure `fig_plane`. The chart-side
blocks of the earlier versions — the de-framing dictionary's density and residue, the prime-side spectrum with its secular
condition, the GUE statistic, the χ-twist, Turing's count and certificate over the laboratory cycles, the resonance — went with
the rows they witnessed; the exact checks of the shell carry the paper, and the chart enters as one exhibit.

Every check names the predicate(s) of the paper's predicate ledger it witnesses (Appendix A "Predicate ledger, machine
verification and formalisation", predicates cited as `20:XN`; public copy `docs/20-rh/index.html`); the ledger's source column links, for each
machine-verified predicate, the script at the deciding check's marker (`src/20-rh/#<key>`) and the Lean module at the predicate's
declaration. Where a predicate is proved in Lean (the predicate module `lean/FrcCore/Rh.lean` on the theme files
`FrcCore/Theme/Horizon.lean` and `Theme/Zeros.lean`, with no axioms, or `lean/FrcLedger/Rh.lean` on Mathlib — A2–A4, B1, B2, B4–B6, B8–B10, B12, B13, E12–E14, F7, F10), the check here is the instance the reader can run.
Master-ledger predicates of the corpus reached through the paper's rows: `00:A2` (Finitude, 20:A2), `00:A3` (Completeness,
20:A3) and `00:A4` (Observation, 20:A4).

[![Open In Colab](https://colab.research.google.com/assets/colab-badge.svg)](https://colab.research.google.com/github/gamayos/finite-ring-space/blob/main/src/20-rh/frc-20-rh.ipynb)

Discipline: `EXACT` checks are integer-exact finite computations (a pass is a proof on the tested instances); `[approx]` checks
compare a floating-point observation with the value the paper states, to a stated tolerance; `[chart]` marks a continuum reading
of a finite object. Nothing in blocks B and C is a shell operation: the window's prime-power labels are read with the chart's
weight log ℓ, the taper, the scale n^{−1/2} and the height γ, and the classical heights enter as validation markers only — never
as inputs. ζ is never evaluated.

## In-tree

| block | checks | claims backed |
|---|---|---|
| `A` | A1–A7, A7b, A6b, A10–A20: 96 (91 EXACT, 5 [approx]) | predicates 20:A2–A4, 20:B1, B2, B4–B6, B8–B10, B12–B14, 20:E12–E15, 20:F7, F10, 20:O9: the zero-slot (Thm `zeroslot`, A1), slot complementarity (Thm `compl`, A2), the Hermitian phase calculus on F_{p²} (Lem `K`, A3), the finite critical line Tr = 1 with 2⁻¹ = 2κ+1 = −π (Prop `critical`, A4), the two agreement loci among all p(p+1) affine lines and the Klein four-group's fixed loci (Thm `agree`, A5), the Subject constants π = 2κ, i = g^{−κ}, e = g^i on the odd lift (§1.3, A6; the lift rule on every frame below 3000, Rem `frame`, A6b), the shell theorem's clauses (i), (iii), (iv), (v) on random vectors in F_p — the dual inverts, the drive's eigenvectors, W² = −J and F⁴ = 1, the explicit formula along the meridian (Thm `hp`, A7, EXACT; rows 20:E12 and 20:E14) — and its chart reading on ℓ²(F_p^×), the complex characters orthogonal with ‖χ_j‖² = p−1, the Parseval identity and the drive as a unitary permutation with the roots of unity as its eigenvalues (Rem `parseval`, Rem `chart-operator`, A7b, [approx]); the Parseval identity Σ v̂(k)v̂(−k) = −Σ v² (Thm `hp` (ii), A14); the shared quarter-turn core Q₄ and the non-existence of C_{232} ↠ C_{12} on (13, 233) (Def `shells`, A10); frame coincidence below the horizon on (p, Ω) pairs to (10009, 100180109) (Prop `coincide`, A11); the critical line as the energy domain — z_k = 2⁻¹ − ηg^k, the drive, the half-turn and the conjugation as k ↦ k+π, the norm even — on 13, 17, 29, 37, 41, 53, 173 (Prop `line`, A15); frame coincidence on the line on the three laboratory pairs, at every label of the Subject, the eigenvalue −θ under each frame's drive and no affine relation between the two frames' indices (Prop `coincideline`, Thm `drive` (vi), A16); the drive theorem — the modes the eigenvectors of (Dv)(x) = v(gx), the spectrum F_p^× simple and real, D orthogonal for the pairing and not symmetric, the modes isotropic, the readout minus the eigenvalue, the half-turn its negation — on 13, 17, 29, 37, 41, 173 (Thm `drive`, A19; row 20:E15); the energy domain as a circle under z/(1 − z), the conjugation the inversion, the drive no rotation, on 13, 17, 29, 37, 41 (Rem `cayley`, A20; row 20:B14); no zero off the line on (13, 233) and (173, 30089) — the lines kept by both involutions are the meridian and the critical line and no other tested line, every Subject zero a nontrivial mode in both frames, points off both lines on no line kept by both (Thm `noline`, A18; row 20:F10); the closure of the zeros on the laboratory Carriers Ω = 233, 30089, 2408561 (Thm `closure`, A12; rows 20:A2, 20:A4, 20:F7); completeness on the laboratory pairs (row 20:A3, A13); the generators of F_13, F_173, F_1549, F_30089 that order the window's primes by the discrete logarithm — 2 of 4, then none; the longest ordered run 5 of 6, 6 of 12, 7 of 40 (§ order, A17; row 20:O9). Shells 13, 17, 29, 37, 41 in full; 173 for A1, A4, A6, A7, A14, A15; 1009, 10009 for A11; the laboratory pairs for A12, A13, A16 |
| `B` | B3, B5, B6, B8: 10 ([chart]) | the de-framing limit (2κ+1)/p → ½ from above, in rationals (Prop `critical`, B3; row 20:B8); the exhibit (Obs `exhibit`; row 20:F9): the windows of depth 13, 39 and 173 put their five peaks (the five tallest on the range 10 to 36) at the first five classical heights within the resolution 2π/log H, the peaks to one decimal as the paper states them (B5); the pair agreement on (173, 30089) and (1549, 2408561), the Carrier's five peaks within the Subject's resolution of the Subject's, the distances as stated; the pair (13, 233) with a window of two labels and a flat intensity (B6); the window's labels read in the cycle's own scale coordinate, the discrete logarithm, loading the modes like a random sum on F_173, F_1549, F_30089 — on F_1549 at most 108 against a mean of 19 and a random-sum maximum of about 140 (§ order, B8; row 20:O9) |
| `C` | C1: 1 ([chart]) | the window of depth 10⁶: the ten tallest peaks on the range 10 to 52 are the first ten heights, each within 0.05 (Obs `exhibit`, row 20:F9); the figure `fig_primespec` |

The registry (`LEDGER` check → predicates, `BLOCK`, `PREDICATES`, `check()`, `results.json`), the shell's arithmetic (the least
primitive root, the least nonresidue, F_{p²} = F_p(η) as pairs, the dual, the affine lines) and the chart's intensity are the head of
the script.

Run: `python3 rh.py` (≈ 100 s on one core: A 75 s, B 1 s, C 20 s; exits nonzero on any failure; writes `results.json`;
regenerates `figures/paper/`), or the blocks named: `python3 rh.py A B`; installed, `python3 -m frc_20_rh`. Rebuild the
notebook: `python3 make_notebook.py`. Dependencies: numpy, matplotlib (`REQUIRES` in `__init__.py`; verified with numpy 2.4,
matplotlib 3.10); the exact checks are the standard library.

## Figures regenerated

| figure | paper | block |
|---|---|---|
| `figures/paper/fig_plane.pdf` | Fig `line` (the critical line is the energy domain, on F_13: the framed plane, the time domain, the line in the drive's order) | A |
| `figures/paper/fig_primespec.pdf` | Fig `primespec` (the exhibit) | C |

The illustration `four-domains.png` (§2, the four domains in both registers) is the dimensions paper's and is not regenerated.

## Predicate ledger

The paper carries its predicate ledger as Appendix A (32 predicates in blocks A, B, D, E, F, Z, O: 3 imported, 7 declared, 20
theorems, 1 Ω-hard, 1 open). Every check of this package names the ledger predicate(s) it witnesses (`LEDGER` in `rh.py`; the
`rows` field of each record in `results.json`, a machine field kept under that name; the check line prints it), and the ledger's
source column links, for each python-witnessed predicate, the check that decides it (`PREDICATES`: B4 ← A1, B12 ← A15, B14 ← A20, E15 ← A19, F9 ← B5, F10 ← A18,
…); the other checks citing a predicate are corroboration, listed by `predicate()` from the records (20:F9 is cited by B5, B6
and C1; 20:E13 by A14 and A7b; 20:E12 and 20:E14 both by A7). The master-ledger predicates of the corpus reached here are 00:A2, 00:A3 and 00:A4.

## Numbers the package fixes

1. **Obs `exhibit`, the windows' peaks (B5).** On the grid of step 0.02 the five peaks of the window of depth 13 are 14.48,
   20.52, 25.68, 29.04, 34.94; of depth 39: 14.20, 20.82, 25.36, 29.98, 33.46; of depth 173: 14.20, 20.94, 25.14, 30.18, 33.22.
   The paper states them to one decimal.
2. **Obs `exhibit`, the pair agreement (B6).** The distances between the Subject's and the Carrier's five peaks, from the
   unrounded positions: 0.3, 0.4, 0.5, 1.1, 1.7 on (173, 30089) and 0.0, 0.2, 0.3, 0.4, 0.4 on (1549, 2408561).
3. **Obs `exhibit`, the depth 10⁶ (C1).** On the grid of step 0.01 the ten tallest peaks on the range 10 to 52 lie within 0.035
   of the first ten heights; the paper states 0.05.
4. **§ order, the discrete logarithm (B8).** On F_1549 the 19 prime-power labels of the window load the 1547 nontrivial modes at
   most 108.5, mean 18.8 (exactly |P| − |P|(|P|−1)/(p−2)), against a random-sum maximum |P| log(p−1) ≈ 140.

## One cell per predicate

`frc-20-rh.ipynb` (built by `make_notebook.py`, executed) carries one cell per python-witnessed ledger predicate, addressable by
its stable id (the predicate's accession key, e.g. `p20085` for `20:B12`; the ledger page opens the notebook at the cell). Every
cell is self-contained: it installs the package from the site (`pip install frc-20-rh --find-links https://finitering.space/pkg/`
— a named requirement, so pip reports it already satisfied once installed; the sdist `frc-20-rh-<version>.tar.gz`
`src/make_pkg.py` writes under `docs/pkg/` at each site build; import name `frc_20_rh`, `__init__.py` exporting `predicate`),
states the predicate and runs `predicate("20:B12")`: the blocks of the checks that cite the predicate run once per session (the
deciding check is `rh.PREDICATES`), the check that decides the predicate is printed from the script's own source — the line under
its `# 20:B12 (p20085)` marker — and every record citing the predicate is listed with its verdict. The markers in `rh.py` are the
lines the ledger page's source glyph opens (`docs/src/20-rh/#<key>`). The predicates' Lean counterparts are the declarations
named by their keys (`p20089` has none; `p20085` for 20:B12) at the end of `lean/FrcCore/Rh.lean` and `lean/FrcLedger/Rh.lean`
(`lean/make_predicates.py`), one per predicate, with the paper's module as one executable file for the web editor.

## External witnesses

The framework's ledger file `frc/ledgers/p20_rh.py` reproduces blocks A and B record for record in the standard library (the
chart readings in `frc/chart_rh.py`); the Lean witnesses of the shell predicates are `lean/FrcLedger/Rh.lean` (Mathlib) and
`lean/FrcCore/Rh.lean` (no axioms), rendered at `docs/lean/Rh.html` and `docs/lean/core/Rh.html`. This package is the public
reproduction of the paper's checks and figures; the paper's ledger appendix links here.
