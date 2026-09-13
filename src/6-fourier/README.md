# 6-fourier validation package

Validation package of *Scale-Shift and Fractional Fourier Transform as Rotations over Finite Holographic
Substrate* (Akhtman, 2026), `6-fourier` of the FRC corpus. Five block scripts, 36 checks, one regenerated
figure, driven by `6-fourier-main.ipynb` (Google Colab, *Runtime → Run all*, ≈ 10 s) or by `run_all.py`.

The paper carries no predicate ledger; its machine-verified claims are the labelled statements of Sections
3–9 and Table `tab:checks`. Every check names the `\label`(s) it decides, and the master-ledger row of the
corpus it witnesses where one exists (`00:C2`, `00:C14`, `00:C7`).

[![Open In Colab](https://colab.research.google.com/assets/colab-badge.svg)](https://colab.research.google.com/github/gamayos/finite-ring-space/blob/main/src/6-fourier/6-fourier-main.ipynb)

## In-tree

| script | class | checks | claims backed |
|---|---|---|---|
| `a_shell.py` | EXACT | 6/6 | the frame datum p = 4κ+1, i = −g^κ, π = 2κ, e = g^i and Table `tab:checks` (A1); the Euler identity e^{iπ} ≡ −1 exactly on the odd quarter-turn, toggled by the conjugate reframing, on every primitive frame (§3, **00:C14**, A2); the u-relabelling of Remark `gt-covariance` with the p = 13, u = 5 instance (A3); W² = −J, (iW)² = J, (iW)⁴ = I (Lemma `W-square`, Proposition `F-cycle`, **00:C2**, A4); ±i the unitary normalisations (Remark `unitary-norm`, A5); the J-decomposition dimensions 2κ±1 (Lemma `JF-decomp`, A6) |
| `b_fractional.py` | EXACT | 10/10 | the projector idempotents (Lemma `projectors`, B1); additivity on all 4096 pairs and the cardinal values (Theorem `FRC-FrFT`, **00:C2**, B2–B3); faithfulness (Theorem `faithful`, B4); the multiplicity sums (Lemma `multiplicity`, B5); multiplicities as chart data, (3,3,4,2) vs (4,2,3,3) at p = 13 and the permutation conjugacy F(g) ~ F(g^{u²}) (Remark `multiplicities`, B6); the dichotomy G = ε(1+i) with both patterns, the conjugate and Jacobi laws and the even split on all 38 primitive frames of p ∈ {5,13,17,29,37} plus the 16 of p = 41 (Theorem `multiplicity`, B7) and the proof's identities G G* = −2, G² = 2i, the traces (B8); the exponent lifts and the non-commuting chart at p = 29, u = 5 (Remark `classification`, B9); the conjugate frame: relations, cardinal values, faithfulness kept, the tuple flipped, F' = −F⁻¹, Π'_ℓ = Π_{ℓ+2} (Remark `gt-covariance`, **00:C7** on the transform layer, B10) |
| `c_domains.py` | EXACT | 6/6 | invertibility (Definition `domain`, C1); the 4κ distinct framed bases (Corollary `distinct-domains`, C2); exactly 2κ unordered bases by parity (Remark `ordered-bases`, C3); S_r(M_m) = M_{m+r} on all pairs (Proposition `meridian-scale`, **00:C2**, C4); the effective step and the (p−1)-periodicity (Corollary `effective-step`, Remark `framed-rational`, C5); the p = 13 ladder and the no-wrap window (Example `zoom-13`, Theorem `zoom`, Remark `two-layers`, C6) |
| `d_weil.py` | EXACT | 7/7 | R_s ∈ SO(2, F_p) (Lemma `Rs-rotation`, D1); the isomorphism Z_{4κ} ≅ SO(2, F_p), \|SO(2)\| = p−1 (Proposition `rotation-isom`, D2); the cardinal matrices and the R_κ column of Table `tab:checks` (Theorem `Weil-equivalence`, D3); the spectral obstruction (Proposition `nogo`, D4); the common character sector and the intertwiner F^[s] T_v = T_v S_{−s} (Proposition `charsector`, D5); Heisenberg covariance and the expansion `conj-expansion` (Proposition `heisenberg`, D6); the 112-index monomial sweep (Conjecture `monomial`, D7) |
| `e_entropy.py` | EXACT / [approx] | 7/7 | Ĝ² = 2n X^κ in the readout algebra, exact modulo Φ_n(X), with both specialisations (Definition `readout`, E1); the entropic cardinal values for every δ_j (Proposition `entropy`, E2); mutually unbiased bases, Maassen–Uffink, the comb log 2 + log 6 = log 12 (E3); the closed form and the two-valued readout (Proposition `closedform`, E4); the p = 13 table and the figure (E5); the δ_1 curve 0.55 vs 0.44 and the odd-projector criterion (Remark `input-dep`, E6); the Galois twist on the δ_0 curve and the twist-invariance of the cardinal values (E7) |
| `fcommon.py` | — | — | shared primitives: the frame datum, exact F_p matrix arithmetic (numpy int64), W, F, Π_ℓ, F^[s], rank mod p, the meridians, R_s, the registry |
| `make_f13_C_figure.py` | figure | — | the framed complex-plane rendering of F_13 (`f13-C-check.png`), a drawing cross-checked against the manuscript figure; not a computation, kept from the paper's `code/` |

Blocks A–D are exact modular arithmetic on the six shells of Table `tab:checks` (p = 5, 13, 17, 29, 37, 41),
over every primitive frame where a statement ranges over frames. Block E is the cyclotomic observer readout on ℂⁿ
(floating point, tolerances 10⁻⁹) except E1, which is exact integer polynomial arithmetic.

Run: `python3 run_all.py` (numpy; matplotlib for the figure). Each block also runs alone: `python3 b_fractional.py`.
Rebuild the notebook: `python3 make_notebook.py`.

## The notebook

`6-fourier-main.ipynb` is the Colab driver: a setup cell (sparse clone of `src/6-fourier` when not already inside the
package), one markdown + code cell per block naming the statements decided, a summary cell that writes `results.json`
and raises on any failure. Committed executed, with outputs.

## Figures regenerated

| figure | paper | block |
|---|---|---|
| `figures/entropy-cycle-f13.pdf` (+ `.png`) | Fig. `entropy13` (§9, entropy on the meridian cycle) | E |

## Master ledger

| row | statement | witnessed by |
|---|---|---|
| `00:C2` (p0022) | scale-shift duality: dilation x ↦ gx is phase evolution of the frame; over the cycle it is the fractional Fourier transform, whose quarter-turn is the discrete Fourier transform | A4, B2, B3, C4 |
| `00:C14` (p0034) | the quarter-turn is the odd member of the ±√−1 pair: e^{iπ} ≡ −1 exactly on the odd member, toggled by the conjugate chart | A2 |
| `00:C7` (p0027) | orientation is derived: the joint flip (g, i) ↦ (g⁻¹, −i) preserves every registered count | B10 (the transform layer only: operator relations, cardinal values, faithfulness; the count-preservation of the other papers is not this package's) |

## Superseded

`frc_frft_finite_checks.py` and `entropy_meridian_cycle.py` (the paper's `code/`, pure-Python) are subsumed: every check
they made is a named check above (A1, A4, B2, B3, B5, B4, C4, B6, B7 and E4–E5), on the same shells and generators, with the
multiplicity dichotomy extended to p = 41.

## Findings recorded

- The Galois-twist sentence of Definition `readout` ("relabels the intermediate curve by s ↦ us while leaving the cardinal
  values invariant") holds as stated for the localized input δ_0 (and δ_{2κ}) on every unit u, and for every input under
  u = −1; for δ_j with j ∉ {0, 2κ} and u ≢ ±1 (mod n) the twisted curve is not the relabelled curve (at n = 12, δ_1,
  u = 5: H(1)/log n moves from 0.55 to 0.44), while the cardinal values stay invariant. The sentence's scope is the δ_0
  input of Proposition `closedform`; E7 checks it there.
- The conjugate frame's family is not a scalar twist of the inverse family (F'^[s] ≠ g^{−2s} F^[−s] off the cardinal
  indices); the exact relations are F' = −F⁻¹ and Π'_ℓ = Π_{ℓ+2}, with the conjugate family the principal lift of its own
  frame (B10).
