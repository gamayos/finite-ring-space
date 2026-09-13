# 20-rh validation package

Machine checks for *Riemann Hypothesis over Finite Holographic Substrate* (Akhtman & Voether, 2026),
paper `20-rh` of the FRC corpus. Seven block scripts, one driver, one notebook; 75 predicate checks;
every numerical figure of the paper regenerated.

[![Open In Colab](https://colab.research.google.com/assets/colab-badge.svg)](https://colab.research.google.com/github/gamayos/frc-numerics/blob/main/20-rh/validate_20rh.ipynb)

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
| `a_shell.py` | EXACT | 49/49 | master ledger **00:D11** (the shell theorem): the zero-slot (Thm `zeroslot`, A1), slot complementarity (Thm `compl`, A2), the Hermitian phase calculus on F_{p²} (Lem `K`, A3), the finite critical line Tr = 1 with 2⁻¹ = 2κ+1 = −π (Prop `critical`, A4), the Klein four-group and its fixed loci (Thm `agree`, A5), the Subject constants π = 2κ, i = g^{−κ}, e = g^i (§1.3, A6), Thm `hp` (i) and (iii) in both character readings with Tr S^r (A7), Thm `hp` (iv) — self-adjointness free (A8), the flat ground state c_p ≡ −1 (Prop `ground`, A9), the shared quarter-turn core Q₄ and the non-existence of C_{232} ↠ C_{12} on (13, 233) (Def `shells`, A10). Shells 13, 17, 29, 37, 41 in full; 173 for A1, A4, A6 |
| `b_deframe.py` | [chart] / [approx] | 4/4 | the de-framing dictionary (Def `deframe`): zero density = shell scale-depth (Prop `density`, B1), the p^{−1/4} reconstruction residue (Obs `residue`, B2), the de-framing limit of the critical real part (B3), the horizon-length main sum tracks the zeros (B4) |
| `c_primeside.py` | [approx] | 5/5 | the spectrum from the prime side, ζ never evaluated: the scale-spectrum peaks (Obs `primespec`, C1), the secular condition to 4.4×10⁻⁵ (Obs `trace`, C2), the colleague matrix (Obs `matrix`, C3), the comb-built Jacobi matrix and its stated coefficients (Def/Obs `jacobi`, C4), the additive injection is gauge-trivial, spacing std 0.08 (Prop `gauge`, C5) |
| `c_gue.py` | [approx] / [chart] | 2/2 | GUE level repulsion of the target spectrum, P(s<½) = 0.05, variance 0.13 (Obs `gue`, C6); the count on the Berry–Keating smooth count (Fig `hp`, C6b) |
| `c_chi.py` | [approx] | 2/2 | the χ_{−4}-twisted comb (Prop `chi`, Obs `chi`): N_χ at the six L-zeros 0.4997 … 5.4998 (C7a); the twisted secular condition to 8.6×10⁻⁵, L never evaluated (C7b) |
| `d_classification.py` | [approx] | 6/6 | master ledger **00:D12** (the classical hypothesis is a screen value): Turing's count read on the shell at T = 15, 30, 50.3 (Thm `turing`, Cor `conditional`, D1); the Davenport–Heilbronn discriminator with positive and negative controls (Obs `dh`): reality of Λ_f (D2a), the argument-principle strip count 45 against 43 on-line sign changes with the deficit of 2 confined to the band of the off-line pair, control L(s,χ) 45 = 45 (D2b), the phantom secular roots 85.63/85.76 and 85.65/85.75 (D2c), the unsettled raw count near the pair (D2d), the ζ comb at the pole s = 1 to depth 8×10⁷ (D2e) |
| `e_resonance.py` | EXACT / [approx] | 7/7 | Λ = μ ∗ log, symbolic (Thm `resonance` (b), E1a); Hardy's limit and the intertwiner (Thm `resonance` (a), (c), E1b); the staircase from the modes (Def `resonance`, Fig `emergence`, E1c); the per-mode energy 1/φ(q) with its maximum at the antipode (Obs `antipode`, E2a) and the additive-transform band energies (E2b); the resolving threshold at the horizon (Obs `horizon`, E3); √p-flatness of every chart mode, 0.08 vs 0.03 at p = 1009 and 0.0087 vs 0.0032 at p ≈ 10⁵ (Prop/Obs `flat`, E4) |
| `rhcommon.py` | — | — | shared primitives: sieve, tapered comb, θ(T) from log Γ, raw count, secular roots, colleague and Jacobi matrices, the registry |

Run: `python3 run_all.py` (exits nonzero on any failure; writes `results.json`; regenerates `figures/`).
`RH_FAST=1 python3 run_all.py` runs the same 75 predicates at reduced depths. Each block script also runs
standalone (`python3 d_classification.py`). Dependencies: `requirements.txt` — numpy, scipy, mpmath,
sympy, matplotlib (verified with numpy 2.4, scipy 1.17, mpmath 1.3, sympy 1.14, matplotlib 3.10).

Timing (full depths, one core): A < 1 s, B 3 s, C 32 s, C6 25 s (240 zeros from `zetazero`, cached),
C7 6 s, D 120 s (Hurwitz-zeta arms 90 s, the 8×10⁷ comb 2 s), E 12 s — about 3.5 min in all.

## The notebook

`validate_20rh.ipynb` drives the same scripts cell by cell. Each block's markdown cell names the paper's
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
| `fig_dh.pdf` | Fig `dh` (with a third panel: the raw count against depth, D2d/D2e) | D |
| `fig_obstruction.pdf` | Fig `obstruction` | E |
| `fig_emergence_frc.pdf` | Fig `emergence` | E |

The qualitative illustration `carrier-domains.png` (§1) is not a computation and is not regenerated.

## Predicate ledger

20-rh does not yet carry an in-paper predicate ledger (the corpus convention adopted after its first
version); the ids A1 … E4 are therefore package-local, assigned in reading order of the paper and
mapped to the paper's `\label`s in each script's docstring and in the notebook cells. When the paper
reaches its release milestone the in-paper ledger is to be added and these ids re-keyed to it; the two
master-ledger rows the package witnesses, 00:D11 and 00:D12, are stable now.

## Findings for the paper (recorded, not silently absorbed)

Four places where the computation and the text of the current revision do not coincide to the digit.
None affects a claim; each is a wording item for the release pass.

1. **Prop `gauge` (C5).** "spacing standard deviation 0.08 of its mean against the zeros' 0.39" mixes
   two conventions: on the paper's own grid (U = 15, M = 2048, potential scale 5) the additive operator's
   spacings have absolute standard deviation 0.078 on a mean spacing 0.72, i.e. 0.11 of the mean, while
   the zeros' 0.39 is the ratio (std 1.54 on mean 3.96, first ten heights). Either convention supports
   the claim (uniform against irregular); the sentence should use one. The package pins both numbers.
2. **Obs `dh`, the 4×10⁵ secular roots (D2c).** At depth 4×10⁵ the unsettled count in [85.3, 86.1] also
   swings below 42.5 and above 45.5 (excursion 42.35 – 45.65), so the secular condition has two further
   crossing pairs there (at 85.35/85.52 and 85.88/86.05) besides the two roots 85.65/85.75 the paper
   names; at 10⁵ the excursion stays inside (42.5, 45.5) and the two roots are the only crossings. The
   package pins the roots as the upward crossings of the levels 43.5 and 44.5 (the two levels between the
   exact counts 43 below the pair and 45 above) and reports the rest. The paper's next sentence — the
   count does not settle with depth — is the same phenomenon; the sentence naming the roots should say so.
3. **Obs `dh`, the count at 85.3 (D2d).** "42.66 to 42.73" are the values at the first and last depth;
   the interior depths read 42.64, 42.65, 42.68.
4. **Obs `antipode`, the band energies (E2b).** The figures 1220 > 640 > 323 > 214 at p ≈ 10⁴ are not
   reproduced by any normalisation the text states. The law they follow, E_q ∝ μ²(q)/φ(q) with
   E_2 ≈ π(p), is reproduced (Parseval-normalised band energy of the prime indicator on Z/10007, ±3
   bins: 1153 > 592 > 301 > 205; φ(q)E_q/E_2 = 1.03, 1.04, 1.06). The paper should state the vector,
   the modulus and the band definition behind its four figures, or replace them by the law.

## External witnesses

The corpus-side checks that produced the numbers in the revision history of the paper are in
`finite-universe-3/20-rh-20260608/reviews/round-0N/` (secular-dh-check, r03check, r04check); the ledger
witness for 00:D11 is `00-ledger-20260816/validation/check_rh_shell.py`. This package supersedes the
paper's legacy `figures/*.py` scripts as the public reproduction.
