# 20-rh validation package

Machine checks for *Riemann Hypothesis over Finite Holographic Substrate* (Akhtman & Voether, 2026),
paper `20-rh` of the FRC corpus. Seven block scripts, one driver, one notebook; 94 predicate checks (57 EXACT, 34 [approx], 3 [chart]), each keyed to a row of the
paper's predicate ledger (Appendix A, rows cited as `20:XN`; public copy `docs/20-rh/20-rh-ledger.html`); every numerical figure of the paper regenerated.
Where a row is proved in Lean (`lean/FrcCore/Rh.lean` with no axioms, or `lean/FrcLedger/Rh.lean` on Mathlib — the shell rows B2, B4–B10, C2, C5,
E1, E12, E13), the check here is the instance the reader can run.

[![Open In Colab](https://colab.research.google.com/assets/colab-badge.svg)](https://colab.research.google.com/github/gamayos/finite-ring-space/blob/main/src/20-rh/20-rh-main.ipynb)

Discipline: `EXACT` checks are integer-pinned finite computations (a pass is a proof on the tested
instances); `[approx]` checks compare a floating-point observation with the value the paper states, to
a stated tolerance; `[chart]` marks a continuum reading of a finite object. The construction's own
discipline — *ζ never evaluated* — binds blocks A–C: every construction there uses only the sieved von
Mangoldt comb, its logarithms, the raised-cosine taper and the archimedean phase from log Γ; the Riemann
heights appear as validation markers only. The control arms of block D evaluate Hurwitz zeta functions,
as the paper says they do.

## In-tree

| script | class | checks | claims backed |
|---|---|---|---|
| `a_shell.py` | EXACT / [approx] | 61/61 | paper rows 20:B1–B11, 20:E1, 20:E9, 20:E12–E13; master ledger **00:D11** (the shell theorem): the zero-slot (Thm `zeroslot`, A1), slot complementarity (Thm `compl`, A2), the Hermitian phase calculus on F_{p²} (Lem `K`, A3), the finite critical line Tr = 1 with 2⁻¹ = 2κ+1 = −π (Prop `critical`, A4), the Klein four-group and its fixed loci (Thm `agree`, A5), the Subject constants π = 2κ, i = g^{−κ}, e = g^i (§1.3, A6), Thm `hp` (iii) in the F_p reading with Tr S^r, integer arithmetic (A7, EXACT), and (i), (iii) in the complex-character reading on ℓ²(F_p^×) — the mean on the trivial mode, orthonormality, Sχ_j = ω^j χ_j (A7b, [approx]); Thm `hp` (iv) — self-adjointness free, Lanczos in floating point (A8, [approx]); the flat ground state c_p ≡ −1 as a Ramanujan sum in F_q, q ≡ 1 (mod p) (Prop `ground`, A9, EXACT); the shared quarter-turn core Q₄ and the non-existence of C_{232} ↠ C_{12} on (13, 233) (Def `shells`, A10), frame coincidence below the horizon on (p, Ω) pairs to (10009, 100180109) (Prop `coincide`, A11). Shells 13, 17, 29, 37, 41 in full; 173 for A1, A4, A6; 1009, 10009 for A11 |
| `b_deframe.py` | [chart] / [approx] | 4/4 | rows 20:D2–D4, 20:B8; the de-framing dictionary (Def `deframe`): zero density = shell scale-depth (Prop `density`, B1), the p^{−1/4} reconstruction residue (Obs `residue`, B2), the de-framing limit of the critical real part (B3), the horizon-length main sum tracks the zeros (B4) |
| `c_primeside.py` | [approx] | 7/7 | rows 20:E5–E6, 20:E8–E10; the spectrum from the prime side, ζ never evaluated: the scale-spectrum peaks (Obs `primespec`, C1), the raw secular condition to 4.4×10⁻⁵ at 10⁶ (Obs `trace`, C2), the pole-corrected secular condition to 3.4×10⁻⁵ at 10⁶ and 1.3×10⁻⁵ at 10⁸, falling with depth (Prop `combformula`, Obs `trace`, C2b), the raw condition stalling past 10⁷ (C2c), the colleague matrix of the corrected count (Obs `matrix`, C3), the comb-built Jacobi matrix and its stated coefficients (Def/Obs `jacobi`, C4), the additive injection is gauge-trivial, spacing std 0.08 (Prop `gauge`, C5) |
| `c_gue.py` | [approx] / [chart] | 2/2 | rows 20:E11, 20:E3; GUE level repulsion of the target spectrum, P(s<½) = 0.05, variance 0.13 (Obs `gue`, C6); the count on the Berry–Keating smooth count (Fig `hp`, C6b) |
| `c_chi.py` | [approx] | 3/3 | rows 20:E14–E16; the χ_{−4}-twisted comb (Prop `chi`, Obs `chi`): N_χ at the six L-zeros 0.4997 … 5.4998 (C7a); the twisted secular condition to 8.6×10⁻⁵, L never evaluated (C7b); the complex character χ mod 5, χ(2) = i: the half-phase W(χ)^{−1/2}Λ real on the line, the twisted count reading 1 … 14 between the fifteen zeros below 40, the fifteen heights recovered to 8.0×10⁻⁵ with brackets from the count alone (C7c) |
| `d_classification.py` | [approx] | 10/10 | rows 20:F1, 20:F3–F5, 20:F8; master ledger **00:D12** (the classical hypothesis is a screen value): Turing's count read on the shell at T = 15, 30, 50.3 (Thm `turing`, Cor `conditional`, D1); the Davenport–Heilbronn discriminator with positive and negative controls (Obs `dh`): reality of Λ_f (D2a), the argument-principle strip count 45 against 43 on-line sign changes with the deficit of 2 confined to the band of the off-line pair, control L(s,χ) 45 = 45 (D2b), the phantom secular roots 85.63/85.76 and 85.65/85.75 (D2c), the unsettled raw count near the pair (D2d), the ζ comb at the pole s = 1 to depth 8×10⁷ (D2e); the smoothed explicit formula (Prop `combformula`): the pole-corrected ζ count settling at t = 1, 5, 10 (D2f), the DH drift as the zero term of the off-line zero (D2g), the corrected sum against log ζ (D3); the frame-exact count on the shells p = 97, 1009, 4801 at their own ceilings, deviations 0.079, 0.107, 0.164 (Thm `turing`, D4) |
| `e_resonance.py` | EXACT / [approx] | 7/7 | rows 20:C2–C4, 20:C6, 20:B11; Λ = μ ∗ log, symbolic (Thm `resonance` (b), E1a); Hardy's limit and the intertwiner (Thm `resonance` (a), (c), E1b); the staircase from the modes (Def `resonance`, Fig `emergence`, E1c); the per-mode energy 1/φ(q) with its maximum at the antipode (Obs `antipode`, E2a) and the additive-transform band energies 1153 > 592 > 301 > 205 on Z/10007 (E2b); the resolving threshold at the horizon (Obs `horizon`, E3); the maximal chart-mode correlation within a small multiple of the exact 1/√(p−2) floor, 0.077 vs 0.0315 at p = 1009 and 0.0087 vs 0.0032 at p = 100049 (Prop/Obs `flat`, E4) |
| `rhcommon.py` | — | — | shared primitives: sieve, tapered comb, θ(T) from log Γ, raw count, secular roots, colleague and Jacobi matrices, the registry |

Run: `python3 run_all.py` (exits nonzero on any failure; writes `results.json`; regenerates `figures/`).
`RH_FAST=1 python3 run_all.py` runs the same 94 predicates at reduced depths (the 10⁸ comb of C2b/C2c and the p = 4801 shell of D4 skipped). Each block script also runs
standalone (`python3 d_classification.py`). Dependencies: `requirements.txt` — numpy, scipy, mpmath,
sympy, matplotlib (verified with numpy 2.4, scipy 1.17, mpmath 1.3, sympy 1.14, matplotlib 3.10).

Timing (full depths, one core): A 1 s, B 4 s, C 170 s (the secular roots to 10⁸, raw and corrected, 130 s), C6 1 s (240 zeros from `zetazero`, cached),
C7 23 s (the χ mod 5 validation arm 13 s), D 200 s (Hurwitz-zeta arms 130 s, the frame-exact shells 35 s, the 8×10⁷ comb 2 s), E 11 s — about 7 min in all.

## The notebook

`20-rh-main.ipynb` drives the same scripts cell by cell (`20-rh-validate.ipynb` is the same notebook under the name the paper's
Reproducibility section pins at commit `b2a3fcec`; `make_notebook.py` writes both). Each block's markdown cell names the paper's
labelled statements it checks (by `\label`, as printed in the paper), lists the paper-local predicate ids
the script registers, and gives the master-ledger row witnessed (`00:D11`, `00:D12`). The figures are
displayed inline after each block; the last cell writes `results.json` and raises on any failure. In
Colab, *Runtime → Run all* completes in about four minutes.

## Figures regenerated

| figure | paper | block |
|---|---|---|
| `fig_deframing.pdf` | Fig `deframe` (§ de-framing) | B |
| `fig_prime_spectrum.pdf` | Fig `primespec` | C |
| `fig_operator_spectrum.pdf` | Fig `operator` | C |
| `fig_hilbert_polya.pdf` | Fig `hp` | C6 |
| `fig_dh.pdf` | Fig `dh` (with a third panel: the raw and the pole-corrected count against depth, D2d–D2f) | D |
| `fig_obstruction.pdf` | Fig `obstruction` | E |
| `fig_emergence_frc.pdf` | Fig `emergence` | E |

The qualitative illustration `carrier-domains.png` (§1) is not a computation and is not regenerated.

## Predicate ledger

The paper carries its predicate ledger as Appendix A (66 rows in blocks A–F, V, Z). Every check of this package names the ledger row(s) it witnesses (`LEDGER` in `rhcommon.py`;
the `rows` field of each record in `results.json`; the check line prints it), and the ledger's source column
cites the check ids in return. The package ids A1 … E4 are therefore check ids, not predicate ids: a ledger row
may be witnessed by several checks (row 20:E12, the shell theorem, by A1–A9 and A7b on six shells) and a check may
witness two rows. The two master-ledger rows of the corpus, 00:D11 and 00:D12, are 20:E12 and 20:F1–F2.

## Four figures the package pins to the digit

1. **Prop `gauge` (C5).** On the paper's grid (U = 15, M = 2048, potential scale 5) the additive operator's spacing standard
   deviation is 0.078 on a mean spacing 0.72, i.e. 0.11 of the mean, against the zeros' 0.39 (std 1.54 on mean 3.96, first ten
   heights). The check pins both numbers.
2. **Obs `dh`, the 4×10⁵ secular roots (D2c).** At depth 4×10⁵ the unsettled count on [85.3, 86.1] swings below 42.5 and above
   45.5 (excursion 42.35–45.65), adding two crossing pairs (85.35/85.52, 85.88/86.05) besides the roots 85.65/85.75; at 10⁵ the
   excursion stays inside (42.5, 45.5) and the two roots are the only crossings. The paper names the roots as the upward
   crossings of 43.5 and 44.5 and records the swing.
3. **Obs `dh`, the count at 85.3 (D2d).** The depths read 42.64, 42.65, 42.68 and 42.73; the paper states 42.64 to 42.73.
4. **Obs `antipode`, the band energies (E2b).** The band energy of the prime indicator on Z/10007, Parseval-normalised over the
   bins within three of each a/q, reads 1153 > 592 > 301 > 205, the law E_q ∝ 1/φ(q). The check pins these to ±2.

## External witnesses

The corpus witness of 00:D11 is `00-ledger-20260816/validation/check_rh_shell.py`; the Lean witnesses of the shell rows are
`lean/FrcLedger/Rh.lean` (Mathlib) and `lean/FrcCore/Rh.lean` (no axioms), rendered at `docs/lean/Rh.html` and
`docs/lean/core/Rh.html`. This package is the public reproduction of the paper's figures; the paper's Reproducibility section
links here.
