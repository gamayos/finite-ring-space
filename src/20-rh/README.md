# 20-rh validation package

Validation package of *The Riemann Hypothesis over the Holographic Substrate: a Finite-Field Dictionary and the Screen Reading*
(Akhtman & Voether, 2026), `20-rh` of the FRC corpus. One script, `rh.py` (since 24 September 2026; the registry `rhcommon.py`
and the seven block scripts merged), five blocks, 95 checks (58 EXACT, 34 [approx], 3 [chart]), driven by `frc-20-rh.ipynb`
(Google Colab: one cell per python-witnessed ledger predicate, any cell on its own, or *Runtime → Run all*, ≈ 8 min) or run whole;
every numerical figure of the paper regenerated into `figures/` as the blocks run.

Every check names the predicate(s) of the paper's predicate ledger it witnesses (Appendix A "Predicate ledger and machine
verification", predicates cited as `20:XN`; public copy `docs/20-rh/index.html`); the ledger's source column links, for each
machine-verified predicate, the script at the deciding check's marker (`src/20-rh/#<key>`) and the Lean module at the predicate's
declaration. Where a predicate is proved in Lean (`lean/FrcCore/Rh.lean` with no axioms, or `lean/FrcLedger/Rh.lean` on
Mathlib — B1, B2, B4–B10, C2, C5, E1, E12, E13), the check here is the instance the reader can run. Master-ledger predicates
of the corpus reached through the paper predicates: `00:D11` (the shell theorem, 20:E12) and `00:D12` (the screen reading,
20:F1–F2).

[![Open In Colab](https://colab.research.google.com/assets/colab-badge.svg)](https://colab.research.google.com/github/gamayos/finite-ring-space/blob/main/src/20-rh/frc-20-rh.ipynb)

Discipline: `EXACT` checks are integer-exact finite computations (a pass is a proof on the tested instances); `[approx]` checks
compare a floating-point observation with the value the paper states, to a stated tolerance; `[chart]` marks a continuum
reading of a finite object. The construction's own discipline — *ζ never evaluated* — binds blocks A–C: every construction
there uses only the sieved von Mangoldt comb, its logarithms, the raised-cosine taper and the archimedean phase from log Γ;
the Riemann heights appear as validation markers only. The control arms of block D evaluate Hurwitz zeta functions, as the
paper says they do.

## In-tree

| block | checks | claims backed |
|---|---|---|
| `A` (`a_shell.py` until 24 September 2026) | A1–A11, A6b, A7b: 62 (56 EXACT, 6 [approx]) | predicates 20:B1–B10, 20:E1, 20:E9, 20:E12–E13; master `00:D11` (the shell theorem): the zero-slot (Thm `zeroslot`, A1), slot complementarity (Thm `compl`, A2), the Hermitian phase calculus on F_{p²} (Lem `K`, A3), the finite critical line Tr = 1 with 2⁻¹ = 2κ+1 = −π (Prop `critical`, A4), the Klein four-group and its fixed loci (Thm `agree`, A5), the Subject constants π = 2κ, i = g^{−κ}, e = g^i on the odd lift (§1.3, A6; the lift rule on every frame below 3000, Rem `frame`, A6b), Thm `hp` (iii) in the F_p reading with Tr S^r, integer arithmetic (A7, EXACT), and (i), (iii) in the complex-character reading on ℓ²(F_p^×) — the mean on the trivial mode, orthonormality, Sχ_j = ω^j χ_j (A7b, [approx]); Def `jacobi` — self-adjointness free, Lanczos in floating point (A8, [approx]); the flat ground state c_p ≡ −1 as a Ramanujan sum in F_q, q ≡ 1 (mod p) (Prop `ground`, A9, EXACT); the shared quarter-turn core Q₄ and the non-existence of C_{232} ↠ C_{12} on (13, 233) (Def `shells`, A10), frame coincidence below the horizon on (p, Ω) pairs to (10009, 100180109) (Prop `coincide`, A11). Shells 13, 17, 29, 37, 41 in full; 173 for A1, A4, A6; 1009, 10009 for A11 |
| `B` (`b_deframe.py`) | B1–B4: 4 ([chart], [approx]) | predicates 20:D2–D4; the de-framing dictionary (Def `deframe`): zero density = shell scale-depth (Prop `density`, B1), the p^{−1/4} reconstruction residue (Obs `residue`, B2), the de-framing limit of the critical real part (B3), the horizon-length main sum tracks the zeros (B4) |
| `C` (`c_primeside.py`, `c_gue.py`, `c_chi.py`, in sequence) | C1–C7c: 12 ([approx], [chart]) | predicates 20:E3, 20:E5–E6, 20:E8–E11, 20:E14–E16; the spectrum from the prime side, ζ never evaluated: the scale-spectrum peaks (Obs `primespec`, C1), the raw secular condition to 4.4×10⁻⁵ at 10⁶ (Obs `trace`, C2), the pole-corrected secular condition to 3.4×10⁻⁵ at 10⁶ and 1.3×10⁻⁵ at 10⁸, falling with depth (Prop `combformula`, Obs `trace`, C2b), the raw condition stalling past 10⁷ (C2c), the colleague matrix of the corrected count (Obs `matrix`, C3), the comb-built Jacobi matrix and its stated coefficients (Def/Obs `jacobi`, C4), the additive injection is gauge-trivial, spacing std 0.08 (Prop `gauge`, C5); GUE level repulsion of the target spectrum, P(s<½) = 0.05, variance 0.13 (Obs `gue`, C6) and the count on the Berry–Keating smooth count (Fig `hp`, C6b); the χ_{−4}-twisted comb (Def `chi`, Obs `chi`): N_χ at the six L-zeros 0.4997 … 5.4998 (C7a), the twisted secular condition to 8.6×10⁻⁵, L never evaluated (C7b), the complex character χ mod 5, χ(2) = i — the half-phase W(χ)^{−1/2}Λ real on the line, the twisted count reading 1 … 14 between the fifteen zeros below 40, the fifteen heights recovered to 8.0×10⁻⁵ with brackets from the count alone (C7c) |
| `D` (`d_classification.py`) | D1–D4, D2a–D2g: 10 ([approx]) | predicates 20:F1, 20:F3–F5, 20:F8; master `00:D12` (the screen reading of the classical hypothesis): Turing's count read on the shell at T = 15, 30, 50.3 (Prop `turing`, Def `screen`, D1); the Davenport–Heilbronn discriminator with positive and negative controls (Obs `dh`): reality of Λ_f (D2a), the argument-principle strip count 45 against 43 on-line sign changes with the deficit of 2 confined to the band of the off-line pair, control L(s,χ) 45 = 45 (D2b), the phantom secular roots 85.63/85.76 and 85.65/85.75 (D2c), the unsettled raw count near the pair (D2d), the ζ comb at the pole s = 1 to depth 8×10⁷ (D2e); the smoothed explicit formula (Prop `combformula`): the pole-corrected ζ count settling at t = 1, 5, 10 (D2f), the DH drift as the zero term of the off-line zero (D2g), the corrected sum against log ζ (D3); the frame-exact count on the shells p = 97, 1009, 4801 at their own ceilings, deviations 0.079, 0.107, 0.164 (Prop `turing`, D4) |
| `E` (`e_resonance.py`) | E1a–E1c, E2a–E2b, E3, E4: 7 (EXACT, [approx]) | predicates 20:B11, 20:C2–C4, 20:C6; Λ = μ ∗ log, symbolic (Thm `resonance` (b), E1a); Hardy's limit and the intertwiner (Thm `resonance` (a), (c), E1b); the staircase from the modes (Def `resonance`, Fig `emergence`, E1c); the per-mode energy 1/φ(q) with its maximum at the antipode (Obs `antipode`, E2a) and the additive-transform band energies 1153 > 592 > 301 > 205 on Z/10007 (E2b); the resolving threshold at the horizon (Obs `horizon`, E3); the maximal chart-mode correlation within a small multiple of the exact 1/√(p−2) floor, 0.077 vs 0.0315 at p = 1009 and 0.0087 vs 0.0032 at p = 100049 (Prop/Obs `flat`, E4) |

The registry (`LEDGER` check → predicates, `BLOCK`, `PREDICATES`, `check()`, `results.json`) and the shared primitives — the sieve,
the tapered comb, θ(T) from log Γ, the raw and the pole-corrected count, the secular roots bracketed by the count itself, the
colleague and Jacobi matrices, the first heights as validation markers — are the head of the script; each block sets the mpmath
precision it runs at.

Run: `python3 rh.py` (≈ 8 min on one core: A 1 s, B 6 s, C 5 min — the secular roots to 10⁸, raw and corrected, are most of it —
D 3 min, E 15 s; exits nonzero on any failure; writes `results.json`; regenerates `figures/`), or the blocks named:
`python3 rh.py A E`; installed, `python3 -m frc_20_rh`. `RH_FAST=1 python3 rh.py` runs the same 95 checks at reduced depths
(the 10⁸ comb of C2b/C2c and the p = 4801 shell of D4 skipped; the records then differ from the paper's). Rebuild the notebook:
`python3 make_notebook.py`. Dependencies: numpy, scipy, mpmath, sympy, matplotlib (`REQUIRES` in `__init__.py`; verified with
numpy 2.4, scipy 1.17, mpmath 1.4, sympy 1.14, matplotlib 3.10).

## Figures regenerated

| figure | paper | block |
|---|---|---|
| `fig_deframing.pdf` | Fig `deframe` (§ de-framing) | B |
| `fig_prime_spectrum.pdf` | Fig `primespec` | C |
| `fig_operator_spectrum.pdf` | Fig `operator` | C |
| `fig_hilbert_polya.pdf` | Fig `hp` | C |
| `fig_dh.pdf` | Fig `dh` (with a third panel: the raw and the pole-corrected count against depth, D2d–D2f) | D |
| `fig_obstruction.pdf` | Fig `obstruction` | E |
| `fig_emergence_frc.pdf` | Fig `emergence` | E |

The qualitative illustration `carrier-domains.png` (§1) is not a computation and is not regenerated.

## Predicate ledger

The paper carries its predicate ledger as Appendix A (61 predicates in blocks A–F, Z: 12 imported, 12 declared, 34 theorems,
3 Ω-hard). Every check of this package names the ledger predicate(s) it witnesses (`LEDGER` in `rh.py`; the `rows` field of
each record in `results.json`, a machine field kept under that name; the check line prints it), and the ledger's source column
links, for each python-witnessed predicate, the check that decides it (`PREDICATES`: the first check the source column named
before the schema — B4 ← A1, E12 ← A7, F8 ← D2f, …); the other checks citing a predicate are corroboration, listed by
`predicate()` from the records (20:E12, the shell theorem, is cited by A7 and A7b on five shells). The two master-ledger
predicates of the corpus, 00:D11 and 00:D12, are 20:E12 and 20:F1–F2.

## Four figures the package fixes to the digit

1. **Prop `gauge` (C5).** On the paper's grid (U = 15, M = 2048, potential scale 5) the additive operator's spacing standard
   deviation is 0.078 on a mean spacing 0.72, i.e. 0.11 of the mean, against the zeros' 0.39 (std 1.54 on mean 3.96, first ten
   heights). The check fixes both numbers.
2. **Obs `dh`, the 4×10⁵ secular roots (D2c).** At depth 4×10⁵ the unsettled count on [85.3, 86.1] swings below 42.5 and above
   45.5 (excursion 42.35–45.65), adding two crossing pairs (85.35/85.52, 85.88/86.05) besides the roots 85.65/85.75; at 10⁵ the
   excursion stays inside (42.5, 45.5) and the two roots are the only crossings. The paper names the roots as the upward
   crossings of 43.5 and 44.5 and records the swing.
3. **Obs `dh`, the count at 85.3 (D2d).** The depths read 42.64, 42.65, 42.68 and 42.73; the paper states 42.64 to 42.73.
4. **Obs `antipode`, the band energies (E2b).** The band energy of the prime indicator on Z/10007, Parseval-normalised over the
   bins within three of each a/q, reads 1153 > 592 > 301 > 205, the law E_q ∝ 1/φ(q). The check fixes these to ±2.

## One cell per predicate

`frc-20-rh.ipynb` (built by `make_notebook.py`, executed) carries one cell per python-witnessed ledger predicate, addressable by
its stable id (the predicate's accession key, e.g. `p20037` for `20:E6`; the ledger page opens the notebook at the cell). Every
cell is self-contained: it installs the package from the site (`pip install frc-20-rh --find-links https://finitering.space/pkg/`
— a named requirement, so pip reports it already satisfied once installed; the sdist `frc-20-rh-<version>.tar.gz`
`src/make_pkg.py` writes under `docs/pkg/` at each site build; import name `frc_20_rh`, `__init__.py` exporting `predicate`),
states the predicate and runs `predicate("20:E6")`: the blocks of the checks that cite the predicate run once per session (the
deciding check is `rh.PREDICATES`), the check that decides the predicate is printed from the script's own source — the line under
its `# 20:E6 (p20037)` marker — and every record citing the predicate is listed with its verdict. The markers in `rh.py` are the
lines the ledger page's source glyph opens (`docs/src/20-rh/#<key>`). The predicates' Lean counterparts are the
declarations named by their keys (`p20037` has none; `p20011` for 20:B4) at the end of `lean/FrcCore/Rh.lean` and
`lean/FrcLedger/Rh.lean` (`lean/make_predicates.py`), one per predicate, with the paper's module as one executable file for the
web editor.

## External witnesses

The corpus witness of 00:D11 is `00-ledger-20260816/validation/check_rh_shell.py`; the Lean witnesses of the shell predicates are
`lean/FrcLedger/Rh.lean` (Mathlib) and `lean/FrcCore/Rh.lean` (no axioms), rendered at `docs/lean/Rh.html` and
`docs/lean/core/Rh.html`. This package is the public reproduction of the paper's figures; the paper's Reproducibility section
links here.
