# 20-rh validation package

Validation package of *Riemann Hypothesis over Finite Holographic Substrate* (Akhtman, 2026; the first version of the
preprint, *Riemann Hypothesis over the Holographic Substrate: a Finite-Field Dictionary and the Screen Reading*), `20-rh` of the
FRC corpus. One script, `rh.py`, four blocks, 102 checks (92 EXACT, 10 [approx]), driven by `frc-20-rh.ipynb`
(Google Colab: one cell per python-witnessed ledger predicate, any cell on its own, or *Runtime → Run all*, under a minute) or run
whole.

The package was rewritten with the paper on 17 October 2026 (`20-rh-20260608/reports/blueprint-20261017.md`) and extended on
18 October (`reports/blueprint-20261018.md`): the drive theorem (A19; row 20:E15) and the names of that revision. It was revised
with the paper on 21 November 2026 (`20-rh-20260608/reports/revision-20261121/`): the count readout replaces the readout on the
framed plane. The checks A2 to A5, A15 to A18 and A20 and the chart blocks B and C went with the rows they witnessed, and the two
figure functions with them. A19 follows row 20:E15: its last two clauses left and the stride of a mode entered. Blocks G and X
entered, one check per row of the count readout and of the classical statements. On 22 November the critical circle entered
(rows 20:G13 and G14, checks G13 and G14), the labels of A11 and A12 took the observational horizon q, the largest label with
q² < p, and `make_figures.py` draws the paper's Figures 2 and 3. Since the same day the count of a window from its dual
has its row 20:D16 and its check D16, its bound has the row 20:D17 and the check D17, and `make_figures.py` draws Figure 4. On 23 November a mode near every height and the value of a mode
at one label entered (rows 20:D18 and D19, checks D18 and D19), and the Hilbert–Pólya operator (row 20:G15, check G15).

Every check cites the predicate(s) of the paper's predicate ledger it witnesses (Appendix A "Predicate ledger and machine
verification", predicates cited as `20:XN`; public copy `docs/20-rh/index.html`); the ledger's source column links, for each
machine-verified predicate, the script at the deciding check's marker (`docs/py/rh.html#<key>`) and the Lean module at the predicate's
declaration. Every python-witnessed predicate but one is proved in Lean: 27 in the core, with no axioms (the predicate module `lean/FrcCore/Rh.lean` on the theme files
`FrcCore/Theme/Horizon.lean`, `Theme/Zeros.lean`, `Theme/Count.lean`, `Theme/Circle.lean` and `Theme/Steps.lean`), six of those also on Mathlib in `lean/FrcMathlib/Rh.lean`
(B1, B2, B4, B10, E12, E13), and D14, D15, D17 and D18 on Mathlib alone. The exception is 20:D16, a definition with its numerical evaluation [approx]
and no Lean predicate (its definitions `dual` and `count` stand with the proof of 20:D17 in the chart theme). The check here is the instance the reader can run.

[![Open In Colab](https://colab.research.google.com/assets/colab-badge.svg)](https://colab.research.google.com/github/gamayos/finite-ring-space/blob/main/src/20-rh/frc-20-rh.ipynb)

Discipline: `EXACT` checks are integer-exact finite computations (a pass is a proof on the tested instances); `[approx]` checks
compare a floating-point observation with the value the paper states, to a stated tolerance. The ten [approx] checks are the
chart's characters of block A (A7b, one per shell) and the five evaluations of block D. ζ is never evaluated: Riemann's formula in D16 uses the eighty imported heights (20:A6).

## In-tree

| block | checks | claims backed |
|---|---|---|
| `A` | A1, A6, A6b, A7, A7b, A10–A14, A19: 54 (49 EXACT, 5 [approx]) | predicates 20:A2–A4, 20:B1, B2, B4, B10, 20:E12–E15, 20:F7: the zero-slot (A1), the Subject constants π = 2κ, i = g^{−κ}, e = g^i on the odd lift (A6; the lift rule on every frame below 3000, A6b), the shell theorem's clauses (i), (iii), (iv), (v) on random vectors in F_p (A7, EXACT; rows 20:E12 and 20:E14) and the Parseval identity (A14; its chart reading on the complex characters, A7b, [approx]; row 20:E13), the shared quarter-turn core and no projection of the cycles on (13, 233) (A10), frame coincidence within the observational horizon (A11), the closure on the Carriers 233, 30089, 2408561 (A12), completeness on the laboratory pairs (A13), the drive theorem with the stride of a mode (A19) |
| `D` | D14, D15, D16, D17, D18, D19: 6 (5 [approx], 1 EXACT) | predicates 20:D14, D15, D16, D17, D18, D19: the spectrum of the window's primes against the first classical heights, the deep window, the count of a window from its dual against the count of the primes and Riemann's formula, the bound of the count, a mode near every height [approx], and the value of a mode at one label (EXACT) |
| `G` | G2, G3, G5, G6, G7, G9, G10, G12, G13, G14, G15: 33 (EXACT) | predicates 20:G2, G3, G5–G7, G9, G10, G12–G15 (and 20:F7 by G6), on the pairs (13, 233), (173, 30089), (1549, 2408561): the count operator and its adjoint (G2), the forced half and the runs of counts (G3), the generator H = −i(N + 2⁻¹) (G5), the zeros ρ_k = k + 1 and the symmetry of origin and unit (G6), the centre 2⁻¹ = −π (G7), the order of the zeros (G9), the cardinal modes at 1, 3·4⁻¹, 2⁻¹, 4⁻¹ (G10), the Carrier's chart with the centre −G (G12), the critical circle on the orbital sphere, its parallels and the counts on its half-turn (G13), the places of the zeros on the latitude cycle (G14), the generator's self-adjointness for the pairing [v, w] = Σ v(x)w(x⁻¹) (G15) |
| `X` | X1, X2, X3: 9 (EXACT) | predicates 20:X1–X3, on the same pairs: the ½ of the critical line (X1), the pole and the functional equation (X2), the ½ of the dilation generator (X3) |

The registry (`LEDGER` check → predicates, `BLOCK`, `PREDICATES`, `check()`, `results.json`), the shell's arithmetic (the least
primitive root, the dual) and the functions of the count readout are the head of the script. The count functions are those of the
framework's count theme (`frc/count.py`), one per theorem of `lean/FrcCore/Theme/Count.lean` and `Theme/Circle.lean`, under its name.

Run: `python3 rh.py` (≈ 25 s on one core; exits nonzero on any failure; writes `results.json`), or the blocks named:
`python3 rh.py A G`; installed, `python3 -m frc_20_rh`. Rebuild the notebook: `python3 make_notebook.py`. Dependency: numpy
(`REQUIRES` in `__init__.py`; verified with numpy 2.4), for the chart's characters of A7b; the exact checks are the standard library.

## Figures

`make_figures.py` draws the paper's Figures 2, 3 and 4 from this package (`python3 make_figures.py`, needs matplotlib):
`figures/paper/fig_circle.pdf`, the critical circle of the Subject F_13 drawn on the sphere [chart], `figures/paper/fig_primespec.pdf`, the
spectrum of a window [chart], and `figures/paper/fig_primecount.pdf`, the count of the primes of a window from Riemann's formula and from
the window's own dual [chart]. `rh.py` draws no figure. `figures/paper/fig_plane.*` belongs to the version of 18 October 2026
and is no figure of the paper since 21 November.

## Predicate ledger

The paper has its predicate ledger as Appendix A (43 predicates in blocks A, B, D, E, F, G, X: 3 imported, 10 declared, 30
theorems). Every check of this package cites the ledger predicate(s) it witnesses (`LEDGER` in `rh.py`; the
`rows` field of each record in `results.json`, a machine field kept under that name; the check line prints it), and the ledger's
source column links, for each python-witnessed predicate, the check that decides it (`PREDICATES`: B4 ← A1, E15 ← A19, F7 ← A12,
G6 ← G6, X1 ← X1, …). A check of blocks G and X has the label of the row it decides. The other checks citing a predicate are
corroboration, listed by `predicate()` from the records (20:F7 is cited by A12 and G6; 20:E13 by A14 and A7b; 20:E12 and 20:E14
both by A7).

## Numbers the package fixes

1. **The centre of the zeros (G7, G12, X1).** 2⁻¹ = 7, 87, 775 on the Subjects 13, 173, 1549, with π = 6, 86, 774; and 2⁻¹ = 117,
   15045, 1204281 on the charts of the Carriers 233, 30089, 2408561, with G = 116, 15044, 1204280.
2. **The cardinal modes (G10).** The modes of count 0, κ, 2κ, 3κ stand at 1, 4, 7, 10 on F_13; at 1, 44, 87, 130 on F_173; at
   1, 388, 775, 1162 on F_1549.
3. **The ranges tried (G2, G5).** Every generator of 13 (4) and of 173 (84), the least three of 1549; every pair of indicators of a
   residue on 13 and 173 (144 and 29,584 pairs), seven indicators and three fixed sequences on 1549 (100 pairs).

## One cell per predicate

`frc-20-rh.ipynb` (built by `make_notebook.py`, executed) has one cell per python-witnessed ledger predicate, addressable by
its stable id (the predicate's accession key, e.g. `p20101` for `20:G6`; the ledger page opens the notebook at the cell). Every
cell is self-contained: it installs the package from the site (`pip install frc-20-rh --find-links https://finitering.space/pkg/`
— a named requirement, so pip reports it already satisfied once installed; the sdist `frc-20-rh-<version>.tar.gz`
`src/make_pkg.py` writes under `docs/pkg/` at each site build; import name `frc_20_rh`, `__init__.py` exporting `predicate`),
states the predicate and runs `predicate("20:G6")`: the blocks of the checks that cite the predicate run once per session (the
deciding check is `rh.PREDICATES`), the check that decides the predicate is printed from the script's own source — the line under
its `# 20:G6 (p20101)` marker — and every record citing the predicate is listed with its verdict. The markers in `rh.py` are the
lines the ledger page's source glyph opens (`docs/py/rh.html#<key>`). The predicates' Lean counterparts are the declarations
at the end of `lean/FrcCore/Rh.lean` and `lean/FrcMathlib/Rh.lean` (`lean/make_predicates.py`), one per predicate, named by the
row's declared name (`zeros_critical_line` for 20:G6), with the paper's module as one executable file for the web editor.

## External witnesses

The framework's ledger file `frc/ledgers/p20_rh.py` reproduces the four blocks record for record on the framework's themes
(`frc/horizon.py`, `frc/count.py`; the chart's characters in `frc/chart_rh.py`); the Lean witnesses of the predicates are
`lean/FrcCore/Rh.lean` (no axioms) and `lean/FrcMathlib/Rh.lean` (Mathlib), rendered at `docs/lean/core/Rh.html` and
`docs/lean/ml/Rh.html`. This package is the public reproduction of the paper's checks; the paper's ledger appendix links here.
