import Mathlib
import FrcLedger.Fourier

/-!
# 3-causality — the Euclidean–Lorentzian dichotomy, Mathlib witnesses

Rows of the predicate ledger of *Euclidean–Lorentzian Dichotomy and Algebraic Causality in Finite Ring Continuum*
(Entropy 2025, 27, 1098; tree `3-causality-20260510`), over an arbitrary finite
field `F` with `card F ≢ 3 (mod 4)` (so `−1` is a square, the shells `p = 4κ + 1` among them).  Classical
(tier 2) on Mathlib's hierarchy; the same rows are proved with no axioms in `FrcCore/Causality.lean`.
-/

namespace FRC.Causality

variable {F : Type*} [Field F]

/-- 3:B2 (Thm. nonexistence, first clause): `c² = ν` makes `ν` a square, so a nonsquare `ν` has no root. -/
theorem no_causal_root (ν c : F) (h : ¬IsSquare ν) : c ^ 2 ≠ ν := fun e => h ⟨c, by rw [← e, sq]⟩

/-- 3:B2 (the consequence): when `−1` is a square (`card F ≢ 3 mod 4`) so is `−c²`, and every coefficient of
`−c² t² + x² + y² + z²` lies in the class of squares — a Euclidean form for every `c ≠ 0`. -/
theorem neg_sq_is_square [Fintype F] (hF : Fintype.card F % 4 ≠ 3) (c : F) : IsSquare (-(c ^ 2)) := by
  obtain ⟨i, hi⟩ := FiniteField.isSquare_neg_one_iff.mpr hF
  exact ⟨i * c, by rw [show -(c ^ 2) = (-1) * c ^ 2 by ring, hi]; ring⟩

/-- 3:B3 (Lemma absorption): coefficients `a_i = w_i² a_0` are absorbed by `x_i ↦ w_i x_i`. -/
theorem absorb (a0 a1 a2 a3 w1 w2 w3 x0 x1 x2 x3 : F) (h1 : w1 ^ 2 * a0 = a1) (h2 : w2 ^ 2 * a0 = a2)
    (h3 : w3 ^ 2 * a0 = a3) :
    a0 * x0 ^ 2 + a1 * x1 ^ 2 + a2 * x2 ^ 2 + a3 * x3 ^ 2 =
    a0 * (x0 ^ 2 + (w1 * x1) ^ 2 + (w2 * x2) ^ 2 + (w3 * x3) ^ 2) := by
  rw [← h1, ← h2, ← h3]; ring

/-- 3:B5: `x² − ν t²` is anisotropic for a nonsquare `ν`. -/
theorem aniso_tx (ν t x : F) (hν : ¬IsSquare ν) (e : x ^ 2 = ν * t ^ 2) : t = 0 ∧ x = 0 := by
  by_cases ht : t = 0
  · subst ht; simp at e; exact ⟨rfl, e⟩
  · exact absurd ⟨x / t, by field_simp; linear_combination (-1 : F) * e⟩ hν

/-- 3:C2 (the finite Lorentz boost): `Λ(γ, b) = !![γ, b; νb, γ]` with `γ² − νb² = 1` preserves `x² − ν t²`. -/
theorem boost_preserves (ν γ b t x : F) (h : γ ^ 2 - ν * b ^ 2 = 1) :
    (γ * x + ν * b * t) ^ 2 - ν * (γ * t + b * x) ^ 2 = x ^ 2 - ν * t ^ 2 := by
  linear_combination (x ^ 2 - ν * t ^ 2) * h

/-- 3:C2: the boosts compose as the norm-one elements of `F(√ν)` multiply. -/
theorem boost_comp (ν γ1 b1 γ2 b2 : F) :
    !![γ1, b1; ν * b1, γ1] * !![γ2, b2; ν * b2, γ2] =
    !![γ1 * γ2 + ν * (b1 * b2), γ1 * b2 + b1 * γ2; ν * (γ1 * b2 + b1 * γ2), γ1 * γ2 + ν * (b1 * b2)] := by
  ext i j; fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_two] <;> ring

/-- 3:C2: `Λ(γ, b)` is orthogonal for the Gram matrix `diag(−ν, 1)` of `Q_ν`: `Λᵀ G Λ = G`. -/
theorem boost_orthogonal (ν γ b : F) (h : γ ^ 2 - ν * b ^ 2 = 1) :
    (!![γ, b; ν * b, γ]).transpose * !![-ν, 0; 0, 1] * !![γ, b; ν * b, γ] = !![-ν, 0; 0, 1] := by
  ext i j; fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_two] <;>
    first | ring1 | linear_combination (-ν) * h | linear_combination h

/-- 3:C3: `γ ≠ 0` on every boost of the Lorentzian plane (`γ = 0` would make `ν = (i/b)²`). -/
theorem gamma_ne_zero [Fintype F] (hF : Fintype.card F % 4 ≠ 3) (ν γ b : F) (hν : ¬IsSquare ν)
    (h : γ ^ 2 - ν * b ^ 2 = 1) : γ ≠ 0 := by
  rintro rfl
  obtain ⟨i, hi⟩ := FiniteField.isSquare_neg_one_iff.mpr hF
  have hb : b ≠ 0 := by rintro rfl; simp at h
  have hνb : ν * b ^ 2 = -1 := by linear_combination -h
  exact hν ⟨i / b, by field_simp; linear_combination hνb + hi⟩

/-- 3:C3: the velocity `v = −νb/γ` satisfies `γ² (ν − v²) = ν` — `γ = 1/√(1 − β²)` with `β² = v²/ν`. -/
theorem gamma_velocity (ν γ b v : F) (h : γ ^ 2 - ν * b ^ 2 = 1) (hv : v * γ = -(ν * b)) :
    γ ^ 2 * (ν - v ^ 2) = ν := by
  linear_combination ν * h - (v * γ - ν * b) * hv

/-- 3:C3 (Einstein's addition law, exact): `v₁₂ (ν + v₁v₂) = ν (v₁ + v₂)`. -/
theorem velocity_addition (ν γ1 b1 γ2 b2 v1 v2 v12 : F) (hγ : γ1 * γ2 ≠ 0)
    (hv1 : v1 * γ1 = -(ν * b1)) (hv2 : v2 * γ2 = -(ν * b2))
    (hv12 : v12 * (γ1 * γ2 + ν * (b1 * b2)) = -(ν * (γ1 * b2 + b1 * γ2))) :
    v12 * (ν + v1 * v2) = ν * (v1 + v2) := by
  have : γ1 * γ2 * (v12 * (ν + v1 * v2) - ν * (v1 + v2)) = 0 := by
    linear_combination ν * hv12 + (-v12 * ν * b2 - ν * γ2 + v12 * (v2 * γ2 + ν * b2)) * hv1 +
      (-v12 * ν * b1 - ν * γ1) * hv2
  rcases mul_eq_zero.mp this with h | h
  · exact absurd h hγ
  · exact sub_eq_zero.mp h

end FRC.Causality
