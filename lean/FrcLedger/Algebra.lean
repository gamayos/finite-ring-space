import Mathlib
import FrcLedger.Fourier

/-!
# 1-algebra — the ledger rows in Lean (2026-09-16)

Rows of the paper's predicate ledger (Appendix A of `1-algebra-axioms`, keys `p01001`–`p01024`), stated as the
revised paper states them (the corrections of `reports/1-algebra-evaluation-20260916.md` applied).
Every universal statement is over an arbitrary finite field `F` with `Fintype.card F = 4κ + 1`
(the shell); the window law is on `ZMod p`; instance checks and refutations are decided.
Every docstring opens with the ledger row(s) the declaration decides (`1:B2`); theorem numbers are the published paper's
(Axioms 2025, 14, 636).
-/

namespace FRC.Algebra

open Polynomial

section shell

variable {F : Type*} [Field F] [Fintype F] [DecidableEq F]

/-! ## Block B — the shell -/

/-- 1:B2 (Theorem 1, existence clause): on the shell `card F = 4κ+1` a quarter-turn `u` with
`u² = −1` exists. Mathlib: `FiniteField.isSquare_neg_one_iff`. -/
theorem quarter_turn_exists (κ : ℕ) (hκ : Fintype.card F = 4 * κ + 1) :
    ∃ u : F, u ^ 2 = -1 := by
  have h : IsSquare (-1 : F) := by
    rw [FiniteField.isSquare_neg_one_iff, hκ]; omega
  obtain ⟨u, hu⟩ := h
  exact ⟨u, by rw [sq, ← hu]⟩

/-- Helper: the shell has odd cardinality, so `2 ≠ 0` in `F`. -/
theorem two_ne_zero_shell (κ : ℕ) (hκ : Fintype.card F = 4 * κ + 1) : (2 : F) ≠ 0 := by
  intro h2
  have hdvd : ringChar F ∣ 2 := (ringChar.spec F 2).1 (by exact_mod_cast h2)
  have hchar : ringChar F = 2 :=
    ((Nat.dvd_prime Nat.prime_two).1 hdvd).resolve_left CharP.ringChar_ne_one
  have := FiniteField.even_card_of_char_two hchar
  omega

/-- 1:B2 (Theorem 1, orbit clause): for a unit `x` with `x² ≠ 1` and `x² ≠ −1` the four
elements `x, −x, x⁻¹, −x⁻¹` of the Klein-four orbit are pairwise distinct (any field of
characteristic `≠ 2`); the structural set `{1, i, −1, −i}` is exactly the complement. -/
theorem klein_orbit_four (hchar : (2 : F) ≠ 0) (x : F) (hx : x ≠ 0) (h1 : x ^ 2 ≠ 1)
    (hi : x ^ 2 ≠ -1) :
    x ≠ -x ∧ x ≠ x⁻¹ ∧ x ≠ -x⁻¹ ∧ -x ≠ x⁻¹ ∧ -x ≠ -x⁻¹ ∧ x⁻¹ ≠ -x⁻¹ := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro h; have : (2 : F) * x = 0 := by linear_combination h
    exact hx ((mul_eq_zero.1 this).resolve_left hchar)
  · intro h; apply h1; rw [sq]; nth_rewrite 2 [h]; exact mul_inv_cancel₀ hx
  · intro h; apply hi; rw [sq]; nth_rewrite 2 [h]; rw [mul_neg, mul_inv_cancel₀ hx]
  · intro h; apply hi; rw [sq]
    have h' : x = -x⁻¹ := by rw [← h, neg_neg]
    nth_rewrite 2 [h']; rw [mul_neg, mul_inv_cancel₀ hx]
  · intro h; apply h1; rw [sq]; have h' : x = x⁻¹ := neg_injective h
    nth_rewrite 2 [h']; exact mul_inv_cancel₀ hx
  · intro h; have : (2 : F) * x⁻¹ = 0 := by linear_combination h
    exact inv_ne_zero hx ((mul_eq_zero.1 this).resolve_left hchar)

/-- 1:B2 (Theorem 1, the structural set): the fourth roots of unity number exactly `4` on the
shell. Mathlib: `IsPrimitiveRoot.card_rootsOfUnity`. -/
theorem card_fourth_roots (κ : ℕ) (hκ : Fintype.card F = 4 * κ + 1) :
    Nat.card (rootsOfUnity 4 F) = 4 := by
  obtain ⟨u, hu⟩ := quarter_turn_exists κ hκ
  have h2 := two_ne_zero_shell κ hκ
  have hm1 : (-1 : F) ≠ 1 := by
    intro h; apply h2; linear_combination -h
  have hu4 : IsPrimitiveRoot u 4 := by
    refine IsPrimitiveRoot.mk_of_lt u (by norm_num) (by rw [show (4:ℕ) = 2 * 2 by rfl, pow_mul, hu]; ring) ?_
    intro l hl hl4
    interval_cases l
    · intro h; apply hm1; rw [← hu, pow_one] at *; rw [h]; ring
    · rw [hu]; exact hm1
    · intro h; apply hm1
      have : u = -1 := by
        have h3 : u ^ 3 = u ^ 2 * u := by ring
        rw [h3, hu] at h; linear_combination -h
      rw [← hu, this]; ring
  exact hu4.card_rootsOfUnity

/-- 1:B3 (convention 4, the oriented quarter-turn): `i := −g^κ` satisfies `i² = −1`; and
`g^(2κ) = −1`, the involution behind Definition 5. From `FrcLedger.Fourier`. -/
theorem quarter_turn (κ : ℕ) (hκ : Fintype.card F = 4 * κ + 1) (g : F)
    (hg : IsPrimitiveRoot g (Fintype.card F - 1)) :
    (-(g ^ κ)) ^ 2 = -1 ∧ g ^ (2 * κ) = -1 := by
  have h := FRC.Fourier.quarter_turn_sq κ hκ g hg
  refine ⟨h, ?_⟩
  rw [← h]; ring

/-- 1:B4 (Definition 2 corrected, Lemma 1): in the affine frame `(a, b)`, `φ x = a + b x`
carries `+` and `·` to `⊕` and `⊗`, is a bijection, and the multiplicative unit of the
relabelled field is `a + b`; `b` is the unit only when `a = 0`. -/
theorem affine_frame (a b : F) (hb : b ≠ 0) :
    let φ : F → F := fun x => a + b * x
    let oplus : F → F → F := fun x y => a + b * ((x - a) / b + (y - a) / b)
    let otimes : F → F → F := fun x y => a + b * ((x - a) / b * ((y - a) / b))
    (∀ x y, φ (x + y) = oplus (φ x) (φ y)) ∧
    (∀ x y, φ (x * y) = otimes (φ x) (φ y)) ∧
    Function.Bijective φ ∧
    (∀ y, otimes (a + b) y = y) ∧
    (a ≠ 0 → otimes b (a + b) ≠ a + b) := by
  intro φ oplus otimes
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · intro x y; simp only [φ, oplus]; field_simp; ring
  · intro x y; simp only [φ, otimes]; field_simp; ring
  · constructor
    · intro x y h; simp only [φ] at h
      exact mul_left_cancel₀ hb (add_left_cancel h)
    · intro y; exact ⟨(y - a) / b, by simp only [φ]; field_simp; ring⟩
  · intro y; simp only [otimes]; field_simp
    ring
  · intro ha h; simp only [otimes] at h
    -- a + b·((b−a)/b · b/b) = a + b  ⇒  ab = 0  ⇒  a = 0
    field_simp at h
    have hab : a * b = 0 := by linear_combination -h
    exact ha ((mul_eq_zero.1 hab).resolve_right hb)

/-- 1:C4 (Definition 5 (a)): the meridian involution `(−a)·g^(n + 2κ) = a·g^n`. -/
theorem meridian_involution (κ : ℕ) (hκ : Fintype.card F = 4 * κ + 1) (g : F)
    (hg : IsPrimitiveRoot g (Fintype.card F - 1)) (a : F) (n : ℕ) :
    (-a) * g ^ (n + 2 * κ) = a * g ^ n := by
  rw [pow_add, (quarter_turn κ hκ g hg).2]; ring

/-! ## Block D — framed numbers -/

/-- 1:D2 (Definition 6 made precise): the framed-integer window. Integers of absolute value
`≤ H` with `2H < card F` have distinct residues: the cast `ℤ → ZMod p` is injective on the
window. Stated on `ZMod p`. -/
theorem framed_integer_window (p : ℕ) [NeZero p] (H : ℕ) (hH : 2 * H < p) (x y : ℤ)
    (hx : |x| ≤ H) (hy : |y| ≤ H) (h : (x : ZMod p) = (y : ZMod p)) : x = y := by
  have hd : (p : ℤ) ∣ x - y := (ZMod.intCast_eq_intCast_iff_dvd_sub y x p).1 h.symm
  have hlt : |x - y| < (p : ℤ) := by
    calc |x - y| ≤ |x| + |y| := abs_sub _ _
      _ ≤ H + H := by omega
      _ < p := by omega
  have := Int.eq_zero_of_abs_lt_dvd hd hlt
  omega

/-- 1:D4 (Lemma 2 restated in the field — scale-periodicity): the scale map
`S n x = x · g^(−n)` on the shell is `(card F − 1)`-periodic in `n`: the residue grids
`G_n = S_n(0..p−1)` coincide as ordered lists. -/
theorem scale_periodic (g : F) (hg : IsPrimitiveRoot g (Fintype.card F - 1)) (n : ℕ) (x : F) :
    x * (g ^ (n + (Fintype.card F - 1)))⁻¹ = x * (g ^ n)⁻¹ := by
  rw [pow_add, hg.pow_eq_one, mul_one]

/-- 1:E2 (Proposition 5 reversed): adjoining a root of `X² + 1` to a field that already
contains one gives zero divisors — `F[X]/(X²+1)` is not a field on the shell. With `u² = −1`,
`(X + u)(X − u) = 0` in the quotient while both factors are nonzero. -/
theorem complex_chart_zero_divisor (u : F) (hu : u ^ 2 = -1) :
    let R := AdjoinRoot ((X : F[X]) ^ 2 + 1)
    ∃ α β : R, α ≠ 0 ∧ β ≠ 0 ∧ α * β = 0 := by
  intro R
  have hmonic : ((X : F[X]) ^ 2 + 1).Monic := by monicity!
  have hdeg : ((X : F[X]) ^ 2 + 1).natDegree = 2 := by compute_degree!
  refine ⟨AdjoinRoot.root _ + AdjoinRoot.of _ u, AdjoinRoot.root _ - AdjoinRoot.of _ u, ?_, ?_, ?_⟩
  · -- X + u is not divisible by X² + 1
    intro h
    have h' : AdjoinRoot.mk ((X : F[X]) ^ 2 + 1) (X + C u) = 0 := by
      rw [map_add, AdjoinRoot.mk_X, AdjoinRoot.mk_C]; exact h
    rw [AdjoinRoot.mk_eq_zero] at h'
    have hne : (X + C u : F[X]) ≠ 0 := X_add_C_ne_zero u
    have := Polynomial.natDegree_le_of_dvd h' hne
    rw [hdeg, natDegree_X_add_C] at this
    omega
  · intro h
    have h' : AdjoinRoot.mk ((X : F[X]) ^ 2 + 1) (X - C u) = 0 := by
      rw [map_sub, AdjoinRoot.mk_X, AdjoinRoot.mk_C]; exact h
    rw [AdjoinRoot.mk_eq_zero] at h'
    have hne : (X - C u : F[X]) ≠ 0 := X_sub_C_ne_zero u
    have := Polynomial.natDegree_le_of_dvd h' hne
    rw [hdeg, natDegree_X_sub_C] at this
    omega
  · -- (root + u)(root − u) = root² − u² = −1 − (−1) = 0
    have hroot : (AdjoinRoot.root ((X : F[X]) ^ 2 + 1)) ^ 2 = -1 := by
      have := AdjoinRoot.eval₂_root ((X : F[X]) ^ 2 + 1)
      simp only [eval₂_add, eval₂_pow, eval₂_X, eval₂_one] at this
      linear_combination this
    have hu' : (AdjoinRoot.of ((X : F[X]) ^ 2 + 1) u) ^ 2 = -1 := by
      rw [← map_pow, hu, map_neg, map_one]
    linear_combination hroot - hu'

/-- 1:F1 (Theorem 3): `2s = 0 ⇒ s = 0` in a field of characteristic `≠ 2`: the additive cycle
has no element of order two; the antipode of the origin is not a residue. -/
theorem no_south_pole (hchar : (2 : F) ≠ 0) (s : F) (h : 2 * s = 0) : s = 0 :=
  (mul_eq_zero.1 h).resolve_left hchar

end shell

/-! ## Instance rows on the prime shell `ZMod p` -/

/-- 1:B3 on `𝔽₁₃`: `g = 2`, `i = −2³ = 5`, `5² = −1`. -/
theorem s13_quarter_turn : (-(2 : ZMod 13) ^ 3) = 5 ∧ (5 : ZMod 13) ^ 2 = -1 := by decide

/-- 1:V1 Lemma 3 refuted: the number of non-zero remainders of the Euclidean algorithm on
`(987, 610)` is `13`, while `⌊log₂ 1009⌋ + 1 = 10`. The claimed bound fails at `p = 1009`
(and first at `p = 59`, where the pair `(55, 34)` needs `7 > 6`). -/
def euclidSteps : ℕ → ℕ → ℕ → ℕ
  | 0, _, _ => 0
  | fuel + 1, a, b => if b = 0 then 0 else (if a % b = 0 then 0 else 1) + euclidSteps fuel b (a % b)

theorem euclid_bound_refuted :
    euclidSteps 40 987 610 = 13 ∧ Nat.log 2 1009 + 1 = 10 ∧
    euclidSteps 40 55 34 = 7 ∧ Nat.log 2 59 + 1 = 6 := by
  decide

/-- 1:D5, the obstruction (Theorem 2 refuted) at `p = 13`, `g = 2`: every grid point
`x/2^n` with `0 ≤ x < 13` and `n ≥ 3` is `≤ 3/2`, so no grid point at resolution `1/8` lies
within `1/16` of `33/10`. (Instance of the range obstruction; the theorem is false as stated.) -/
theorem approx_theorem_refuted :
    ∀ n : ℕ, 3 ≤ n → ∀ x : ℕ, x < 13 → ((x : ℚ) / 2 ^ n) ≤ 3 / 2 := by
  intro n hn x hx
  have h2 : (8 : ℚ) ≤ 2 ^ n := by
    calc (8 : ℚ) = 2 ^ 3 := by norm_num
      _ ≤ 2 ^ n := pow_le_pow_right₀ (by norm_num) hn
  have hx' : (x : ℚ) ≤ 12 := by exact_mod_cast (by omega : x ≤ 12)
  rw [div_le_iff₀ (by positivity)]
  nlinarith

end FRC.Algebra
