import Mathlib
import FrcLedger.Theme.Fourier

/-!
# 1-algebra — the ledger predicates in Lean (2026-09-16)

Predicates of the paper's ledger (Appendix A of `1-algebra-axioms`, keys `p01001`–`p01033`), stated as the
paper's ledger states them.
Every universal statement is over an arbitrary finite field `F` with `Fintype.card F = 4κ + 1`
(the shell); the window law is on `ZMod p`; instance checks and counts are decided. The section
`conjecture` decides the conclusion's conjecture clause by clause (rows E3, D7, E4; E5, the `SO(3)` obstruction,
is numerical and imported). The section `lie` proves the counting clauses of the Lie-algebra layer: the axis group
of 1:E7, cyclic of order `p − (N|p)`, the window count `2H² + 2H`, and the heights and read-back of 1:E8.
Every docstring opens with the ledger predicate(s) the declaration decides (`1:B2`); theorem numbers are the paper's
(Axioms 2025, 14, 636).
-/

namespace FRC.Algebra

open Polynomial

section shell

variable {F : Type*} [Field F] [Fintype F] [DecidableEq F]

/-! ## Block B — the shell -/

omit [DecidableEq F] in
/-- 1:B2 (Theorem 1, existence clause): on the shell `card F = 4κ+1` a quarter-turn `u` with
`u² = −1` exists. Mathlib: `FiniteField.isSquare_neg_one_iff`. -/
theorem quarter_turn_exists (κ : ℕ) (hκ : Fintype.card F = 4 * κ + 1) :
    ∃ u : F, u ^ 2 = -1 := by
  have h : IsSquare (-1 : F) := by
    rw [FiniteField.isSquare_neg_one_iff, hκ]; omega
  obtain ⟨u, hu⟩ := h
  exact ⟨u, by rw [sq, ← hu]⟩

omit [DecidableEq F] in
/-- Helper: the shell has odd cardinality, so `2 ≠ 0` in `F`. -/
theorem two_ne_zero_shell (κ : ℕ) (hκ : Fintype.card F = 4 * κ + 1) : (2 : F) ≠ 0 := by
  intro h2
  have hdvd : ringChar F ∣ 2 := (ringChar.spec F 2).1 (by exact_mod_cast h2)
  have hchar : ringChar F = 2 :=
    ((Nat.dvd_prime Nat.prime_two).1 hdvd).resolve_left CharP.ringChar_ne_one
  have := FiniteField.even_card_of_char_two hchar
  omega

omit [Fintype F] [DecidableEq F] in
/-- 1:B2 (Theorem 1, orbit clause), 2:D7: for a unit `x` with `x² ≠ 1` and `x² ≠ −1` the four
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

omit [DecidableEq F] in
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

omit [DecidableEq F] in
/-- 1:B3 (convention 4, the oriented quarter-turn): `i := −g^κ` satisfies `i² = −1`; and
`g^(2κ) = −1`, the involution behind Definition 5. From `FrcLedger.Fourier`. -/
theorem quarter_turn (κ : ℕ) (hκ : Fintype.card F = 4 * κ + 1) (g : F)
    (hg : IsPrimitiveRoot g (Fintype.card F - 1)) :
    (-(g ^ κ)) ^ 2 = -1 ∧ g ^ (2 * κ) = -1 := by
  have h := FRC.DFT.quarter_turn_sq κ hκ g hg
  refine ⟨h, ?_⟩
  rw [← h]; ring

omit [Fintype F] [DecidableEq F] in
/-- 1:B4 (Definition 2, Lemma 1): in the affine frame `(a, b)`, `φ x = a + b x`
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

omit [DecidableEq F] in
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

omit [DecidableEq F] in
/-- 1:D4 (Lemma 2 restated in the field — scale-periodicity): the scale map
`S n x = x · g^(−n)` on the shell is `(card F − 1)`-periodic in `n`: the residue grids
`G_n = S_n(0..p−1)` coincide as ordered lists. -/
theorem scale_periodic (g : F) (hg : IsPrimitiveRoot g (Fintype.card F - 1)) (n : ℕ) (x : F) :
    x * (g ^ (n + (Fintype.card F - 1)))⁻¹ = x * (g ^ n)⁻¹ := by
  rw [pow_add, hg.pow_eq_one, mul_one]

omit [Fintype F] [DecidableEq F] in
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

omit [Fintype F] [DecidableEq F] in
/-- 1:Z1 (Theorem 3): `2s = 0 ⇒ s = 0` in a field of characteristic `≠ 2`: the additive cycle
has no element of order two; the antipode of the origin is not a residue. -/
theorem no_south_pole (hchar : (2 : F) ≠ 0) (s : F) (h : 2 * s = 0) : s = 0 :=
  (mul_eq_zero.1 h).resolve_left hchar

end shell

/-! ## Instance predicates on the prime shell `ZMod p` -/

/-- 1:B3 on `𝔽₁₃`: `g = 2`, `i = −2³ = 5`, `5² = −1`. -/
theorem s13_quarter_turn : (-(2 : ZMod 13) ^ 3) = 5 ∧ (5 : ZMod 13) ^ 2 = -1 := by decide

/-- 1:V1 the Euclidean step count: the number of non-zero remainders of the Euclidean algorithm on
`(987, 610)` is `13`, against `⌊log₂ 1009⌋ + 1 = 10`; the pair `(55, 34)` needs `7` against
`⌊log₂ 59⌋ + 1 = 6`, the first prime where the count exceeds the logarithmic bound. -/
def euclidSteps : ℕ → ℕ → ℕ → ℕ
  | 0, _, _ => 0
  | fuel + 1, a, b => if b = 0 then 0 else (if a % b = 0 then 0 else 1) + euclidSteps fuel b (a % b)

theorem euclid_step_count :
    euclidSteps 40 987 610 = 13 ∧ Nat.log 2 1009 + 1 = 10 ∧
    euclidSteps 40 55 34 = 7 ∧ Nat.log 2 59 + 1 = 6 := by
  decide

/-- 1:D6 (Theorem approx, the range at `p = 13`, `g = 2`): every grid point
`x/2^n` with `0 ≤ x < 13` and `n ≥ 3` is `≤ 3/2`, so no grid point at resolution `1/8` lies
within `1/16` of `33/10`: range and resolution trade off at fixed window. -/
theorem approx_obstruction :
    ∀ n : ℕ, 3 ≤ n → ∀ x : ℕ, x < 13 → ((x : ℚ) / 2 ^ n) ≤ 3 / 2 := by
  intro n hn x hx
  have h2 : (8 : ℚ) ≤ 2 ^ n := by
    calc (8 : ℚ) = 2 ^ 3 := by norm_num
      _ ≤ 2 ^ n := pow_le_pow_right₀ (by norm_num) hn
  have hx' : (x : ℚ) ≤ 12 := by exact_mod_cast (by omega : x ≤ 12)
  rw [div_le_iff₀ (by positivity)]
  nlinarith

section conjecture

open Real

/-- 1:E3 (the conjecture's first clause, solving): `f ∈ F_p[X]` has a root in `F_p` iff `f` and
`X^p − X = ∏_a (X − a)` are not coprime — the root test is a gcd, exact in the substrate. -/
theorem root_iff_not_coprime (p : ℕ) [hp : Fact p.Prime] (f : (ZMod p)[X]) :
    (∃ a : ZMod p, f.eval a = 0) ↔ ¬ IsCoprime f (X ^ p - X) := by
  constructor
  · rintro ⟨a, ha⟩ hcop
    have h1 : (X - C a) ∣ f := dvd_iff_isRoot.mpr ha
    have h2 : (X - C a) ∣ (X ^ p - X : (ZMod p)[X]) := by
      rw [dvd_iff_isRoot]
      simp [IsRoot, ZMod.pow_card]
    exact (not_isUnit_X_sub_C a) (hcop.isUnit_of_dvd' h1 h2)
  · intro h
    by_contra hno
    push Not at hno
    apply h
    have hprod : (X ^ p - X : (ZMod p)[X]) = ∏ a : ZMod p, (X - C a) := by
      have hroots : (X ^ p - X : (ZMod p)[X]).roots = Finset.univ.val := by
        have := FiniteField.roots_X_pow_card_sub_X (ZMod p); rwa [ZMod.card] at this
      have hmon : (X ^ p - X : (ZMod p)[X]).Monic := by
        apply monic_X_pow_sub
        simpa using hp.out.one_lt
      have hdeg : (X ^ p - X : (ZMod p)[X]).natDegree = p := FiniteField.X_pow_card_sub_X_natDegree_eq (ZMod p) hp.out.one_lt
      have := (prod_multiset_X_sub_C_of_monic_of_roots_card_eq hmon (by rw [hroots, hdeg]; simp)).symm
      rw [this, hroots]
      rfl
    rw [hprod]
    refine IsCoprime.prod_right fun a _ => ?_
    have hirr : Irreducible (X - C a : (ZMod p)[X]) := irreducible_X_sub_C a
    exact (hirr.coprime_iff_not_dvd.mpr (fun hd => hno a (dvd_iff_isRoot.mp hd))).symm

/-- 1:D7 (second clause, limit-like approximation): the tower of shells resolves every real — for every
`r` and `ε > 0` some shell `p = 4κ + 1` carries a framed rational `x / 2^n`, `|x| ≤ 2κ`, within `ε` of `r`
(Dirichlet for primes `≡ 1 (mod 4)`, `Nat.exists_prime_gt_modEq_one`). -/
theorem tower_density (r ε : ℝ) (hε : 0 < ε) :
    ∃ p κ n : ℕ, ∃ x : ℤ, p.Prime ∧ p = 4 * κ + 1 ∧ |x| ≤ 2 * κ ∧ |r - x / 2 ^ n| < ε := by
  obtain ⟨n, hn⟩ := exists_pow_lt_of_lt_one hε (by norm_num : (1 / 2 : ℝ) < 1)
  set x : ℤ := round (r * 2 ^ n) with hx
  obtain ⟨p, hp, hgt, hmod⟩ := Nat.exists_prime_gt_modEq_one (2 * x.natAbs + 1) (by norm_num : (4 : ℕ) ≠ 0)
  have hmod' : p % 4 = 1 := by
    have := hmod; unfold Nat.ModEq at this; simpa using this
  refine ⟨p, p / 4, n, x, hp, ?_, ?_, ?_⟩
  · have := Nat.div_add_mod p 4; omega
  · have h1 : x.natAbs < 2 * (p / 4) := by omega
    have h2 : (|x| : ℤ) = x.natAbs := (Int.natCast_natAbs x).symm
    rw [h2]; exact_mod_cast h1.le
  · have hr : |r * 2 ^ n - x| ≤ 1 / 2 := abs_sub_round (r * 2 ^ n)
    have h2n : (0 : ℝ) < 2 ^ n := by positivity
    have : r - x / 2 ^ n = (r * 2 ^ n - x) / 2 ^ n := by field_simp
    rw [this, abs_div, abs_of_pos h2n]
    calc |r * 2 ^ n - x| / 2 ^ n ≤ (1 / 2) / 2 ^ n := by gcongr
      _ = (1 / 2) ^ n / 2 := by rw [one_div_pow]; ring
      _ < ε := by linarith

/-- 1:E4 (third clause, the abelian case): the rounding `k(θ) = round(Nθ/2π)` puts `2πk/N` within `π/N`
of `θ` — `C_N ≅ F_p^×` (`N = p − 1`) is a `π/N`-net of `U(1)`. -/
theorem circle_net (N : ℕ) (hN : 0 < N) (θ : ℝ) :
    |θ - 2 * π * (round (N * θ / (2 * π)) : ℝ) / N| ≤ π / N := by
  have hπ : (0 : ℝ) < π := pi_pos
  have hN' : (0 : ℝ) < N := by exact_mod_cast hN
  set t := N * θ / (2 * π) with ht
  have hθ : θ = 2 * π * t / N := by rw [ht]; field_simp
  have hr : |t - round t| ≤ 1 / 2 := abs_sub_round t
  have : θ - 2 * π * (round t : ℝ) / N = (2 * π / N) * (t - round t) := by rw [hθ]; field_simp
  rw [this, abs_mul, abs_of_pos (by positivity : (0 : ℝ) < 2 * π / N)]
  calc 2 * π / N * |t - round t| ≤ 2 * π / N * (1 / 2) := by gcongr
    _ = π / N := by ring

/-- 1:E4 (third clause): the group-law defect of the rounding is at most one step. -/
theorem group_law_defect (N : ℕ) (θ₁ θ₂ : ℝ) :
    |round (N * θ₁ / (2 * π)) + round (N * θ₂ / (2 * π)) - round (N * (θ₁ + θ₂) / (2 * π))| ≤ 1 := by
  set t₁ := N * θ₁ / (2 * π) with ht₁
  set t₂ := N * θ₂ / (2 * π) with ht₂
  have hsum : N * (θ₁ + θ₂) / (2 * π) = (t₁ - round t₁) + (t₂ - round t₂) + ((round t₁ + round t₂ : ℤ) : ℝ) := by
    rw [ht₁, ht₂]; push_cast; ring
  rw [hsum, round_add_intCast]
  have h1 : |t₁ - round t₁| ≤ 1 / 2 := abs_sub_round t₁
  have h2 : |t₂ - round t₂| ≤ 1 / 2 := abs_sub_round t₂
  set z := (t₁ - round t₁) + (t₂ - round t₂) with hz
  have hz1 : |z| ≤ 1 := by rw [hz]; calc |_| ≤ |t₁ - round t₁| + |t₂ - round t₂| := abs_add_le _ _
    _ ≤ 1 := by linarith
  have hrz : |z - round z| ≤ 1 / 2 := abs_sub_round z
  have hlt : (|round z| : ℝ) < 2 := by
    have : |(round z : ℝ)| ≤ |z| + |z - round z| := by
      calc |(round z : ℝ)| = |z - (z - round z)| := by ring_nf
        _ ≤ |z| + |z - round z| := abs_sub _ _
    linarith
  have hlt' : |round z| < 2 := by exact_mod_cast hlt
  have hz' : round t₁ + round t₂ - (round z + (round t₁ + round t₂)) = -round z := by ring
  rw [hz', abs_neg]; omega

end conjecture

section lie

/-! ### 1:E7, 1:E8 — the Lie-algebra layer: the axis group, the window count, the heights and the read-back -/

open QuadraticAlgebra

variable (p : ℕ) [Fact p.Prime]

/-- The axis algebra of a pure quaternion `v` with `N(v) = d`: the pairs `a + t v`, with `v² = −d`. -/
abbrev AxisAlg (d : ZMod p) := QuadraticAlgebra (ZMod p) (-d) 0

/-- The scalars inside the axis group. -/
noncomputable def scalars (d : ZMod p) : Subgroup (AxisAlg p d)ˣ :=
  (Units.map (algebraMap (ZMod p) (AxisAlg p d) : ZMod p →* AxisAlg p d)).range

instance (d : ZMod p) : Finite (AxisAlg p d) := Finite.of_equiv _ (QuadraticAlgebra.equivProd (-d) 0).symm

theorem card_axisAlg (d : ZMod p) : Nat.card (AxisAlg p d) = p * p := by
  rw [Nat.card_congr (QuadraticAlgebra.equivProd (-d) 0), Nat.card_prod, Nat.card_zmod]

theorem card_scalars (d : ZMod p) : Nat.card (scalars p d) = p - 1 := by
  unfold scalars
  rw [MonoidHom.range_eq_map, Subgroup.card_map_of_injective, Subgroup.card_top, Nat.card_eq_fintype_card, ZMod.card_units]
  intro x y h
  apply Units.ext
  have := congrArg Units.val h
  simpa using (algebraMap (ZMod p) (AxisAlg p d)).injective this

/-- 1:E7, the axis group when `−d` is not a square: cyclic of order `p + 1`. -/
theorem axis_field (d : ZMod p) [Fact (¬ IsSquare (-d))] :
    IsCyclic ((AxisAlg p d)ˣ ⧸ scalars p d) ∧ Nat.card ((AxisAlg p d)ˣ ⧸ scalars p d) = p + 1 := by
  refine ⟨isCyclic_of_surjective (QuotientGroup.mk' _) (QuotientGroup.mk'_surjective _), ?_⟩
  have hU : Nat.card (AxisAlg p d)ˣ = p * p - 1 := by
    rw [Nat.card_units, card_axisAlg]
  have hL := Subgroup.card_eq_card_quotient_mul_card_subgroup (scalars p d)
  rw [hU, card_scalars] at hL
  have h2 : 2 ≤ p := (Fact.out : p.Prime).two_le
  have : p * p - 1 = (p + 1) * (p - 1) := by
    have := Nat.mul_self_sub_mul_self_eq p 1
    simpa using this
  rw [this] at hL
  exact (Nat.eq_of_mul_eq_mul_right (by omega) hL).symm

/-- The reading of the axis algebra at a square root `r` of `−d`: `a + t v ↦ a + r t`, a ring map. -/
def psiK {K : Type*} [Field K] (d r : K) (hr : r * r = -d) : QuadraticAlgebra K (-d) 0 →+* K where
  toFun z := z.re + r * z.im
  map_one' := by simp
  map_mul' x y := by
    simp only [QuadraticAlgebra.re_mul, QuadraticAlgebra.im_mul]
    linear_combination (-(x.im * y.im)) * hr
  map_zero' := by simp
  map_add' x y := by simp; ring

theorem psiK_apply {K : Type*} [Field K] (d r : K) (hr : r * r = -d) (z : QuadraticAlgebra K (-d) 0) :
    psiK d r hr z = z.re + r * z.im := rfl

/-- 1:E7, the axis group when `−d = r²` with `r ≠ 0` (characteristic not two): the units modulo the scalars are
isomorphic to `Kˣ`. -/
theorem axis_split_equiv {K : Type*} [Field K] (h2 : (2 : K) ≠ 0) (d r : K) (hr : r * r = -d) (hr0 : r ≠ 0) :
    Nonempty ((QuadraticAlgebra K (-d) 0)ˣ ⧸
      (Units.map (algebraMap K (QuadraticAlgebra K (-d) 0) : K →* QuadraticAlgebra K (-d) 0)).range ≃* Kˣ) := by
  have hr' : (-r) * (-r) = -d := by linear_combination hr
  let f₁ : (QuadraticAlgebra K (-d) 0)ˣ →* Kˣ := Units.map (psiK d r hr : QuadraticAlgebra K (-d) 0 →* K)
  let f₂ : (QuadraticAlgebra K (-d) 0)ˣ →* Kˣ := Units.map (psiK d (-r) hr' : QuadraticAlgebra K (-d) 0 →* K)
  let φ : (QuadraticAlgebra K (-d) 0)ˣ →* Kˣ := f₁ * f₂⁻¹
  have h2r : (2 * r) ≠ 0 := mul_ne_zero h2 hr0
  have hdet : ∀ x y : QuadraticAlgebra K (-d) 0, psiK d r hr x = psiK d r hr y → psiK d (-r) hr' x = psiK d (-r) hr' y → x = y := by
    intro x y h1 h2'
    rw [psiK_apply, psiK_apply] at h1 h2'
    have him : x.im = y.im := by
      have : (2 * r) * (x.im - y.im) = 0 := by linear_combination h1 - h2'
      rcases mul_eq_zero.mp this with h | h
      · exact absurd h h2r
      · exact sub_eq_zero.mp h
    have hre : x.re = y.re := by rw [him] at h1; linear_combination h1
    exact QuadraticAlgebra.ext hre him
  have hker : φ.ker = (Units.map (algebraMap K (QuadraticAlgebra K (-d) 0) : K →* QuadraticAlgebra K (-d) 0)).range := by
    ext z
    rw [MonoidHom.mem_ker, MonoidHom.mem_range]
    constructor
    · intro h
      have h' : f₁ z = f₂ z := by
        have := congrArg (· * f₂ z) h
        simpa [φ] using this
      have hv := congrArg Units.val h'
      simp only [f₁, f₂, Units.coe_map, MonoidHom.coe_ofClass, psiK_apply] at hv
      have him : (z : QuadraticAlgebra K (-d) 0).im = 0 := by
        have : (2 * r) * (z : QuadraticAlgebra K (-d) 0).im = 0 := by linear_combination hv
        rcases mul_eq_zero.mp this with h | h
        · exact absurd h h2r
        · exact h
      have hre0 : (z : QuadraticAlgebra K (-d) 0).re ≠ 0 := by
        intro h0
        exact z.ne_zero (QuadraticAlgebra.ext (by simpa using h0) (by simpa using him))
      refine ⟨Units.mk0 _ hre0, ?_⟩
      apply Units.ext
      exact QuadraticAlgebra.ext (by simp) (by simp [him])
    · rintro ⟨c, rfl⟩
      apply Units.ext
      simp [φ, f₁, f₂, psiK_apply]
  have hsurj : Function.Surjective φ := by
    intro y
    let zf : Kˣ → QuadraticAlgebra K (-d) 0 := fun y => ⟨((y : K) + 1) / 2, ((y : K) - 1) / (2 * r)⟩
    have e1 : ∀ y : Kˣ, psiK d r hr (zf y) = y := by
      intro y; rw [psiK_apply]; show ((y : K) + 1) / 2 + r * (((y : K) - 1) / (2 * r)) = y; field_simp; ring
    have e2 : ∀ y : Kˣ, psiK d (-r) hr' (zf y) = 1 := by
      intro y; rw [psiK_apply]; show ((y : K) + 1) / 2 + -r * (((y : K) - 1) / (2 * r)) = 1; field_simp; ring
    have hmul : zf y * zf y⁻¹ = 1 :=
      hdet _ _ (by rw [map_mul, map_one, e1, e1]; simp) (by rw [map_mul, map_one, e2, e2, mul_one])
    have hmul' : zf y⁻¹ * zf y = 1 := by rw [mul_comm]; exact hmul
    let u : (QuadraticAlgebra K (-d) 0)ˣ := ⟨zf y, zf y⁻¹, hmul, hmul'⟩
    have hu1 : f₁ u = y := Units.ext (e1 y)
    have hu2 : f₂ u = 1 := Units.ext (e2 y)
    exact ⟨u, by simp [φ, hu1, hu2]⟩
  exact ⟨(QuotientGroup.quotientMulEquivOfEq hker.symm).trans (QuotientGroup.quotientKerEquivOfSurjective φ hsurj)⟩

/-- 1:E7, the axis group on the shell when `−d = r²`, `r ≠ 0`: cyclic of order `p − 1`. -/
theorem axis_split (hp2 : p ≠ 2) (d r : ZMod p) (hr : r * r = -d) (hr0 : r ≠ 0) :
    IsCyclic ((AxisAlg p d)ˣ ⧸ scalars p d) ∧ Nat.card ((AxisAlg p d)ˣ ⧸ scalars p d) = p - 1 := by
  have h2 : (2 : ZMod p) ≠ 0 := Ring.two_ne_zero (by rw [ZMod.ringChar_zmod_n]; exact hp2)
  obtain ⟨e⟩ := axis_split_equiv h2 d r hr hr0
  refine ⟨isCyclic_of_surjective e.symm.toMonoidHom e.symm.surjective, ?_⟩
  exact (Nat.card_congr e.toEquiv).trans (by rw [Nat.card_eq_fintype_card, ZMod.card_units])

/-- 1:E7, the rotation group of an axis `v` on a shell `p ≡ 1 (mod 4)`, `N(v) = N ≢ 0`: the pairs `a + t v` modulo
the scalars form a cyclic group of order `p − (N|p)`. -/
theorem axis_group (hp4 : p % 4 = 1) (N : ℤ) (hN : (N : ZMod p) ≠ 0) :
    IsCyclic ((AxisAlg p N)ˣ ⧸ scalars p N) ∧ (Nat.card ((AxisAlg p N)ˣ ⧸ scalars p N) : ℤ) = p - legendreSym p N := by
  have hp2 : p ≠ 2 := by omega
  have hneg : legendreSym p (-N) = legendreSym p N := by
    rw [show -N = (-1) * N by ring, legendreSym.mul, legendreSym.at_neg_one hp2, ZMod.χ₄_nat_one_mod_four hp4, one_mul]
  have hNn : ((-N : ℤ) : ZMod p) ≠ 0 := by push_cast; exact neg_ne_zero.mpr hN
  by_cases hs : IsSquare (-(N : ZMod p))
  · obtain ⟨r, hr⟩ := hs
    have hr0 : r ≠ 0 := by rintro rfl; exact hN (neg_eq_zero.mp (hr.trans (mul_zero 0)))
    obtain ⟨hc, hcard⟩ := axis_split p hp2 (N : ZMod p) r hr.symm hr0
    refine ⟨hc, ?_⟩
    have h1 : legendreSym p (-N) = 1 := (legendreSym.eq_one_iff p hNn).mpr (by push_cast; exact ⟨r, hr⟩)
    rw [hcard, ← hneg, h1]
    have := (Fact.out : p.Prime).two_le
    omega
  · have : Fact (¬ IsSquare (-(N : ZMod p))) := ⟨hs⟩
    obtain ⟨hc, hcard⟩ := axis_field p (N : ZMod p)
    refine ⟨hc, ?_⟩
    have h1 : legendreSym p (-N) = -1 := (legendreSym.eq_neg_one_iff p).mpr (by push_cast; exact hs)
    rw [hcard, ← hneg, h1]
    push_cast; ring

/-- The window pairs `(a, t)`, `|a|, |t| ≤ H`, not both zero. -/
def winPairs (H : ℕ) : Finset (ℤ × ℤ) := ((Finset.Icc (-(H : ℤ)) H) ×ˢ (Finset.Icc (-(H : ℤ)) H)).erase 0

/-- One pair of each sign class `±(a, t)`: `t > 0`, or `t = 0` and `a > 0`. -/
def halfPairs (H : ℕ) : Finset (ℤ × ℤ) :=
  ((Finset.Icc (-(H : ℤ)) H) ×ˢ (Finset.Icc (1 : ℤ) H)) ∪ ((Finset.Icc (1 : ℤ) H) ×ˢ {0})

theorem card_halfPairs (H : ℕ) : (halfPairs H).card = 2 * H * H + 2 * H := by
  unfold halfPairs
  rw [Finset.card_union_of_disjoint]
  · simp only [Finset.card_product, Int.card_Icc, Finset.card_singleton]
    have h1 : ((H : ℤ) + 1 - -(H : ℤ)).toNat = 2 * H + 1 := by omega
    have h2 : ((H : ℤ) + 1 - 1).toNat = H := by omega
    rw [h1, h2]; ring
  · rw [Finset.disjoint_left]
    rintro ⟨a, t⟩ h1 h2
    simp only [Finset.mem_product, Finset.mem_Icc, Finset.mem_singleton] at h1 h2
    omega

/-- 1:E7, the window count: a map of the window pairs that takes `x` and `−x` to the same value (the rotation
`ρ_{a + t v₀}`: `ρ_{−q} = ρ_q`) takes at most `2H² + 2H` values. -/
theorem card_image_le_of_neg {β : Type*} [DecidableEq β] (H : ℕ) (f : ℤ × ℤ → β) (hf : ∀ x, f (-x) = f x) :
    ((winPairs H).image f).card ≤ 2 * H * H + 2 * H := by
  rw [← card_halfPairs H]
  refine le_trans (Finset.card_le_card (t := (halfPairs H).image f) ?_) Finset.card_image_le
  intro y hy
  simp only [Finset.mem_image, winPairs, Finset.mem_erase, Finset.mem_product, Finset.mem_Icc] at hy ⊢
  obtain ⟨⟨a, t⟩, ⟨hne, ⟨ha1, ha2⟩, ⟨ht1, ht2⟩⟩, rfl⟩ := hy
  by_cases hpos : 0 < t ∨ (t = 0 ∧ 0 < a)
  · refine ⟨(a, t), ?_, rfl⟩
    simp only [halfPairs, Finset.mem_union, Finset.mem_product, Finset.mem_Icc, Finset.mem_singleton]
    omega
  · refine ⟨(-a, -t), ?_, ?_⟩
    · have hne' : (a, t) ≠ (0, 0) := hne
      simp only [halfPairs, Finset.mem_union, Finset.mem_product, Finset.mem_Icc, Finset.mem_singleton]
      have : ¬ (a = 0 ∧ t = 0) := fun h => hne' (by rw [h.1, h.2])
      omega
    · exact hf (a, t)

section heights

open Quaternion

/-- 1:E8, the height law: a window quaternion `q` (integer coordinates of size at most `H`) has every coordinate
of `q^m` of size at most `(2H)^m` — the norm is multiplicative and at most `4H²` on the window. -/
theorem quat_pow_height (H : ℤ) (q : ℍ[ℤ]) (hr : |q.re| ≤ H) (hi : |q.imI| ≤ H) (hj : |q.imJ| ≤ H) (hk : |q.imK| ≤ H) (m : ℕ) :
    |(q ^ m).re| ≤ (2 * H) ^ m ∧ |(q ^ m).imI| ≤ (2 * H) ^ m ∧ |(q ^ m).imJ| ≤ (2 * H) ^ m ∧ |(q ^ m).imK| ≤ (2 * H) ^ m := by
  have hH : 0 ≤ H := le_trans (abs_nonneg _) hr
  have hn : normSq q ≤ (2 * H) ^ 2 := by
    rw [normSq_def']
    have h1 := sq_le_sq' (abs_le.mp hr).1 (abs_le.mp hr).2
    have h2 := sq_le_sq' (abs_le.mp hi).1 (abs_le.mp hi).2
    have h3 := sq_le_sq' (abs_le.mp hj).1 (abs_le.mp hj).2
    have h4 := sq_le_sq' (abs_le.mp hk).1 (abs_le.mp hk).2
    nlinarith
  have hpow : normSq (q ^ m) ≤ ((2 * H) ^ m) ^ 2 := by
    rw [map_pow, ← pow_mul, mul_comm m 2, pow_mul]
    exact pow_le_pow_left₀ (normSq_nonneg) hn m
  have hb : 0 ≤ (2 * H) ^ m := pow_nonneg (by linarith) m
  have key : ∀ c : ℤ, c ^ 2 ≤ normSq (q ^ m) → |c| ≤ (2 * H) ^ m := fun c hc =>
    abs_le_of_sq_le_sq' (le_trans hc hpow) hb |> fun h => abs_le.mpr h
  rw [normSq_def'] at hpow
  refine ⟨key _ ?_, key _ ?_, key _ ?_, key _ ?_⟩ <;> rw [normSq_def'] <;> nlinarith [sq_nonneg (q ^ m).re, sq_nonneg (q ^ m).imI, sq_nonneg (q ^ m).imJ, sq_nonneg (q ^ m).imK]

/-- 1:E8, read-back (the window law D2 coordinate by coordinate): an integer `c` is the signed reading of its residue
on the shell `p` (odd) exactly when `2|c| < p`. -/
theorem readback_iff (p : ℕ) [Fact p.Prime] (hp : p ≠ 2) (c : ℤ) : ((c : ZMod p).valMinAbs = c) ↔ 2 * |c| < p := by
  rw [ZMod.valMinAbs_spec]
  have hodd : (p : ℤ) % 2 = 1 := by
    have := (Fact.out : p.Prime).eq_one_or_self_of_dvd 2
    omega
  constructor
  · rintro ⟨_, h1, h2⟩
    rcases abs_cases c with ⟨h, _⟩ | ⟨h, _⟩ <;> rw [h] <;> omega
  · intro h
    refine ⟨rfl, ?_, ?_⟩ <;> rcases abs_cases c with ⟨h', _⟩ | ⟨h', _⟩ <;> rw [h'] at h <;> omega

end heights

end lie

-- Ledger predicates of 1-algebra (generated by make_predicates.py from docs/1-algebra/1-algebra-ledger.json; edit the ledger, not this section)
/-- 1:B2 (p01004) — Symmetry completeness (Thm.~\ref{thm:symmetric-completeness}): the fourth roots of unity form the unique order-four subgroup $Q_4=\{1,\im,-1,-\im\}$; under the Klein four-group $\langle x\mapsto-x,\,x\mapsto x^{-1}\rangle$, $Q_4$ is the union of the two size-two orbits $\{\pm1\}$, $\{\pm\im\}$, and $\Fpx\setminus Q_4$ splits into exactly $\kap-1$ orbits of size four. For $\p\equiv3\pmod4$ no $\im$ exists. -/
theorem p01004 : (∀ {F : Type u_1} [Field F] [Fintype F] (κ : ℕ), Fintype.card F = (4 : ℕ) * κ + (1 : ℕ) → ∃ u, u ^ (2 : ℕ) = (-1 : F)) ∧ (∀ {F : Type u_2} [Field F], (2 : F) ≠ (0 : F) → ∀ (x : F), x ≠ (0 : F) → x ^ (2 : ℕ) ≠ (1 : F) → x ^ (2 : ℕ) ≠ (-1 : F) → x ≠ -x ∧ x ≠ x⁻¹ ∧ x ≠ -x⁻¹ ∧ -x ≠ x⁻¹ ∧ -x ≠ -x⁻¹ ∧ x⁻¹ ≠ -x⁻¹) ∧ ∀ {F : Type u_3} [Field F] [Fintype F] (κ : ℕ), Fintype.card F = (4 : ℕ) * κ + (1 : ℕ) → Nat.card ↥(rootsOfUnity (4 : ℕ) F) = (4 : ℕ) :=
  And.intro @FRC.Algebra.quarter_turn_exists (And.intro @FRC.Algebra.klein_orbit_four (@FRC.Algebra.card_fourth_roots))
/-- 1:B3 (p01005) — The oriented quarter-turn: $\im=-\gen^{\kap}$ satisfies $\im^{2}=-1$ for every primitive root $\gen$; the two square roots of $-1$ are $\{-\gen^{\kap},\gen^{\kap}\}$, so the drive fixes which is $\im$. On $\F_{13}$, $\gen=2$: $\im=5$. -/
theorem p01005 : (∀ {F : Type u_1} [Field F] [Fintype F] (κ : ℕ), Fintype.card F = (4 : ℕ) * κ + (1 : ℕ) → ∀ (g : F), IsPrimitiveRoot g (Fintype.card F - (1 : ℕ)) → (-g ^ κ) ^ (2 : ℕ) = (-1 : F) ∧ g ^ ((2 : ℕ) * κ) = (-1 : F)) ∧ -(2 : ZMod (13 : ℕ)) ^ (3 : ℕ) = (5 : ZMod (13 : ℕ)) ∧ (5 : ZMod (13 : ℕ)) ^ (2 : ℕ) = (-1 : ZMod (13 : ℕ)) :=
  And.intro @FRC.Algebra.quarter_turn (@FRC.Algebra.s13_quarter_turn)
/-- 1:B4 (p01006) — Affine reframing (Def.~\ref{def:framed-field}, Lemma~\ref{lem:affine-invariance}): $\varphi_{a,b}(x)=a+bx$, $b\neq0$, is a ring isomorphism $(\Fp,+,\cdot)\to(\Fp,\oplus,\otimes)$ with origin $a$ and unit $a+b$; every polynomial identity is frame-covariant. -/
theorem p01006 : ∀ {F : Type u_1} [Field F] (a b : F), b ≠ (0 : F) → have φ := fun x => a + b * x; have oplus := fun x y => a + b * ((x - a) / b + (y - a) / b); have otimes := fun x y => a + b * ((x - a) / b * ((y - a) / b)); (∀ (x y : F), φ (x + y) = oplus (φ x) (φ y)) ∧ (∀ (x y : F), φ (x * y) = otimes (φ x) (φ y)) ∧ Function.Bijective φ ∧ (∀ (y : F), otimes (a + b) y = y) ∧ (a ≠ (0 : F) → otimes b (a + b) ≠ a + b) :=
  @FRC.Algebra.affine_frame
/-- 1:C4 (p01011) — Involutions and counts (Def.~\ref{def:orbit-sphere}\,(a)--(c)): $M_n(a)=M_{n+2\kap}(-a)$ and $L_a(m)=L_{-a}(m+2\kap)$ since $\gen^{2\kap}=-1$; $\p-1$ distinct meridian lists in $2\kap$ great circles; $2\kap$ latitude pairs; one-sided vertex count $(\p-1)^{2}/2+1$, the double cover $(\p-1)^{2}$ (00:B11). -/
theorem p01011 : ∀ {F : Type u_1} [Field F] [Fintype F] (κ : ℕ), Fintype.card F = (4 : ℕ) * κ + (1 : ℕ) → ∀ (g : F), IsPrimitiveRoot g (Fintype.card F - (1 : ℕ)) → ∀ (a : F) (n : ℕ), -a * g ^ (n + (2 : ℕ) * κ) = a * g ^ n :=
  @FRC.Algebra.meridian_involution
/-- 1:D2 (p01013) — The window law: $z\mapsto z\bmod\p$ is injective on $W_H$ when $2H<\p$; for $x,y\in W_H$ the residue of $x\pm y$ reads back the integer when $4H<\p$, and that of $xy$ when $2H^{2}<\p$ (the same injectivity on the windows $2H$ and $H^{2}$). -/
theorem p01013 : ∀ (p : Nat) [@NeZero Nat (@MulZeroClass.toZero Nat Nat.instMulZeroClass) p] (H : Nat), @LT.lt Nat instLTNat (@HMul.hMul Nat Nat Nat (@instHMul Nat instMulNat) (@OfNat.ofNat Nat (nat_lit 2) (instOfNatNat (nat_lit 2))) H) p → ∀ (x y : Int), @LE.le Int Int.instLEInt (@abs Int instLatticeInt Int.instAddGroup x) (@Nat.cast Int instNatCastInt H) → @LE.le Int Int.instLEInt (@abs Int instLatticeInt Int.instAddGroup y) (@Nat.cast Int instNatCastInt H) → @Eq (ZMod p) (@Int.cast (ZMod p) (@AddGroupWithOne.toIntCast (ZMod p) (@Ring.toAddGroupWithOne (ZMod p) (@CommRing.toRing (ZMod p) (ZMod.commRing p)))) x) (@Int.cast (ZMod p) (@AddGroupWithOne.toIntCast (ZMod p) (@Ring.toAddGroupWithOne (ZMod p) (@CommRing.toRing (ZMod p) (ZMod.commRing p)))) y) → @Eq Int x y :=
  @FRC.Algebra.framed_integer_window
/-- 1:D4 (p01015) — Scale-periodicity (Lemma~\ref{thm:scale-periodicity}, in the field): $S_n(x)=x\gen^{-n}$ satisfies $S_{n+(\p-1)}=S_n$; the grids $G_n$ are $(\p-1)$-periodic as ordered lists; the zoom $[x,n]\mapsto[x,n+1]$ has order $\p-1$. As lists of rationals $x/\gen^{n}$ ($\gen$ lifted to $\Z$) the grids are not periodic: the periodicity is a relation of the field. -/
theorem p01015 : ∀ {F : Type u_1} [Field F] [Fintype F] (g : F), IsPrimitiveRoot g (Fintype.card F - (1 : ℕ)) → ∀ (n : ℕ) (x : F), x * (g ^ (n + (Fintype.card F - (1 : ℕ))))⁻¹ = x * (g ^ n)⁻¹ :=
  @FRC.Algebra.scale_periodic
/-- 1:D7 (p01027) — Limit-like approximation (second clause), across the tower: for every real $r$ and $\varepsilon>0$ some shell $\p=4\kap+1$ carries a framed rational $x/2^{n}$, $|x|\le2\kap$, within $\varepsilon$ of $r$ (primes $\equiv1\pmod4$ beyond every bound). One shell trades range for resolution; the limit is the tower, not a completion. -/
theorem p01027 : ∀ (r ε : ℝ), (0 : ℝ) < ε → ∃ p κ n x, Nat.Prime p ∧ p = (4 : ℕ) * κ + (1 : ℕ) ∧ |x| ≤ (2 : ℤ) * ↑κ ∧ |r - ↑x / (2 : ℝ) ^ n| < ε :=
  @FRC.Algebra.tower_density
/-- 1:E2 (p01019) — The extension by $X^{2}+1$ is trivial (Prop.~\ref{prop:Cp-field} reversed): on the shell $\Fp[X]/(X^{2}+1)\cong\Fp\times\Fp$ has zero divisors, $(X+\im)(X-\im)=0$, so it is not a field; $\Fp[X]/(X^{2}+1)$ is a field exactly when $\p\equiv3\pmod4$; the quadratic extension of the shell is $\Fp[\eta]$, $\eta^{2}=\nu$ a non-square (8-dirac B6). -/
theorem p01019 : ∀ {F : Type u_1} [Field F] (u : F), u ^ (2 : ℕ) = (-1 : F) → let R := AdjoinRoot (Polynomial.X ^ (2 : ℕ) + (1 : Polynomial F)); ∃ α β, α ≠ (0 : R) ∧ β ≠ (0 : R) ∧ α * β = (0 : R) :=
  @FRC.Algebra.complex_chart_zero_divisor
/-- 1:E3 (p01026) — Solving in the substrate (first clause): $f\in\Fp[X]$ has a root in $\Fp$ iff $f$ and $X^{\p}-X=\prod_{a}(X-a)$ are not coprime; the gcd counts the distinct roots and Cantor--Zassenhaus splitting finds them, exactly. An equation without a root in $\Fp$ is recognised, not extended (E2). -/
theorem p01026 : ∀ (p : ℕ) [hp : Fact (Nat.Prime p)] (f : Polynomial (ZMod p)), (∃ a, Polynomial.eval a f = (0 : ZMod p)) ↔ ¬IsCoprime f (Polynomial.X ^ p - Polynomial.X) :=
  @FRC.Algebra.root_iff_not_coprime
/-- 1:E4 (p01028) — Continuous symmetry, the abelian case (third clause): $\Fpx\simeq C_{\p-1}\simeq SO(2,\Fp)$ (6:E2) is a $\pi/(\p-1)$-net of $U(1)$ under $k\mapsto e^{2\pi\im k/(\p-1)}$; the rounding $k(\theta)=\lfloor(\p-1)\theta/2\pi+\tfrac12\rfloor$ has angle and chord error $\le\pi/(\p-1)$ and group-law defect at most one step. -/
theorem p01028 : (∀ (N : ℕ), (0 : ℕ) < N → ∀ (θ : ℝ), |θ - (2 : ℝ) * Real.pi * ↑(round (↑N * θ / ((2 : ℝ) * Real.pi))) / ↑N| ≤ Real.pi / ↑N) ∧ ∀ (N : ℕ) (θ₁ θ₂ : ℝ), |round (↑N * θ₁ / ((2 : ℝ) * Real.pi)) + round (↑N * θ₂ / ((2 : ℝ) * Real.pi)) - round (↑N * (θ₁ + θ₂) / ((2 : ℝ) * Real.pi))| ≤ (1 : ℤ) :=
  And.intro @FRC.Algebra.circle_net (@FRC.Algebra.group_law_defect)
/-- 1:E7 (p01032) — The Lie-algebra layer, one axis: on a shell $\p>8H^{2}$, for $q=a+v\in W_H^{4}$ with $v\ne0$, the rotation $\rho_q\colon x\mapsto qxq^{-1}$ is the Cayley step (8:C3) of the self-adjoint $\eta S_v$ (E2's $\eta$, $S_vx=v\times x$, $N(v)=v\cdot v$) at $\alpha=\eta/(\nu a)$, and the half-turn $U_\infty=I+2N(v)^{-1}S_v^{2}$ at $a=0$. With $U_\infty$ these steps form a cyclic group of order $\p-\bigl(\tfrac{N(v)}{\p}\bigr)$ containing every iterate; at most $2H^{2}+2H$ of its elements are window rotations. -/
theorem p01032 : (∀ (p : ℕ) [Fact (Nat.Prime p)], p % (4 : ℕ) = (1 : ℕ) → ∀ (N : ℤ), ↑N ≠ (0 : ZMod p) → IsCyclic ((FRC.Algebra.AxisAlg p ↑N)ˣ ⧸ FRC.Algebra.scalars p ↑N) ∧ ↑(Nat.card ((FRC.Algebra.AxisAlg p ↑N)ˣ ⧸ FRC.Algebra.scalars p ↑N)) = ↑p - legendreSym p N) ∧ ∀ {β : Type u_1} [DecidableEq β] (H : ℕ) (f : ℤ × ℤ → β), (∀ (x : ℤ × ℤ), f (-x) = f x) → (Finset.image f (FRC.Algebra.winPairs H)).card ≤ (2 : ℕ) * H * H + (2 : ℕ) * H :=
  And.intro @FRC.Algebra.axis_group (@FRC.Algebra.card_image_le_of_neg)
set_option linter.defProp false in
/-- 1:E8 (p01033) — The Lie-algebra layer, two axes and range: for pure quaternions $u,w$ with $1+N(u)$, $1+N(w)$ and $1-u\cdot w$ nonzero, $\rho_{1+u}\rho_{1+w}=\rho_{1+u\circ w}$ with $u\circ w=(u+w+u\times w)/(1-u\cdot w)$, the bracket being $[u,w]=2u\times w$; at $u\cdot w=1$ the product is the half-turn about $u+w+u\times w$. The entries of $q^{m}$, $q\in W_H^{4}$, are at most $(2H)^{m}$, and $q^{m}$ reads back from the shell iff $2\|q^{m}\|_\infty<\p$ (D2). -/
def p01033 := And.intro @FRC.Algebra.quat_pow_height (@FRC.Algebra.readback_iff)
/-- 1:Z1 (p01020) — No element of additive order two (Thm.~\ref{thm:no-south-pole}): $2s=0$ forces $s=0$; the antipode of the origin on the additive cycle is not a residue; it sits between $2\kap=(\p-1)/2$ and $2\kap+1=(\p+1)/2=2^{-1}$ (20-rh B8). -/
theorem p01020 : ∀ {F : Type u_1} [Field F], (2 : F) ≠ (0 : F) → ∀ (s : F), (2 : F) * s = (0 : F) → s = (0 : F) :=
  @FRC.Algebra.no_south_pole
-- end ledger predicates

end FRC.Algebra
