import Mathlib
import FrcLedger.Theme.Chart

/-!
# FrcLedger.Theme.Fields — the chart theme's readings of the interactions (27-fields, 16 October 2026)

The clauses of 27-fields that read the continuum: the phase cycle `ℤ/M` inside `U(1)` as the `M`-th roots of unity
(`roots_inclusion`, 27:C1), the Wilson weight `1 − Re ζ ≥ 0` on the unit circle, zero at the identity alone
(`wilson_weight_nonneg`, 27:C1), the `2T` area-law coefficient `c₁ = (x⁴ + 4x³ − 4x − 1)/(x⁴ + 8x³ + 6x² + 8x + 1)` in
`(0, 1)` for `x = e^{β/2} > 1` (`area_law_positive`, 27:C1, C7, X7), the Fermi constant `G_F = 1/(√2 v²)` from
`G_F/√2 = g²/(8 M_W²)` and `M_W² = g² v²/4` (`fermi_constant`, 27:C6). Classical (tier 2) on Mathlib's hierarchy. The finite content of the same rows is
proved with no axioms in the core (`FrcCore/Theme/Interactions.lean`, `Theme/Unitary.lean`, `FrcCore/Fields.lean`).
-/

namespace FRC.FieldsML

open Real

/-- 27:C1 — the phase cycle inside `U(1)`: `ζ_M = exp(2πi/M)` is a primitive `M`-th root of unity, `k ↦ ζ_M^k` is a
homomorphism of the cycle (`ζ^{j+k} = ζ^j ζ^k`), injective on `0 ≤ k < M`, and every image is an `M`-th root. -/
theorem roots_inclusion (M : ℕ) (hM : M ≠ 0) :
    IsPrimitiveRoot (Complex.exp (2 * π * Complex.I / M)) M ∧
    (∀ j k : ℕ, Complex.exp (2 * π * Complex.I / M) ^ (j + k) =
      Complex.exp (2 * π * Complex.I / M) ^ j * Complex.exp (2 * π * Complex.I / M) ^ k) ∧
    (∀ j k : ℕ, j < M → k < M →
      Complex.exp (2 * π * Complex.I / M) ^ j = Complex.exp (2 * π * Complex.I / M) ^ k → j = k) ∧
    (∀ k : ℕ, (Complex.exp (2 * π * Complex.I / M) ^ k) ^ M = 1) := by
  have h := Complex.isPrimitiveRoot_exp M hM
  refine ⟨h, fun j k => pow_add _ _ _, fun j k hj hk e => h.pow_inj hj hk e, fun k => ?_⟩
  rw [← pow_mul, Nat.mul_comm k M, pow_mul, h.pow_eq_one, one_pow]

/-- 27:C1 — the Wilson weight on the unit circle: for `‖ζ‖ = 1`, `0 ≤ 1 − Re ζ`, with equality exactly at `ζ = 1`. -/
theorem wilson_weight_nonneg (ζ : ℂ) (h : ‖ζ‖ = 1) : 0 ≤ 1 - ζ.re ∧ (1 - ζ.re = 0 ↔ ζ = 1) := by
  have hre : ζ.re ≤ 1 := h ▸ Complex.re_le_norm ζ
  refine ⟨by linarith, ⟨fun h0 => ?_, fun h1 => by rw [h1]; simp⟩⟩
  have hre1 : ζ.re = 1 := by linarith
  have h2 : ζ.re * ζ.re + ζ.im * ζ.im = 1 := by
    rw [← Complex.normSq_apply, Complex.normSq_eq_norm_sq, h, one_pow]
  have him : ζ.im = 0 := by nlinarith
  exact Complex.ext (by simpa using hre1) (by simpa using him)

/-- 27:C1, 27:C7, 27:X7 — the area law from positivity on `2T`: for `x = e^{β/2} > 1` the coefficient
`c₁ = (x⁴ + 4x³ − 4x − 1)/(x⁴ + 8x³ + 6x² + 8x + 1)` lies in `(0, 1)`, so the string tension `σ = −ln c₁` is positive. -/
theorem area_law_positive (x : ℝ) (hx : 1 < x) :
    0 < (x ^ 4 + 4 * x ^ 3 - 4 * x - 1) / (x ^ 4 + 8 * x ^ 3 + 6 * x ^ 2 + 8 * x + 1) ∧
    (x ^ 4 + 4 * x ^ 3 - 4 * x - 1) / (x ^ 4 + 8 * x ^ 3 + 6 * x ^ 2 + 8 * x + 1) < 1 := by
  have hx0 : 0 < x := by linarith
  have hD : 0 < x ^ 4 + 8 * x ^ 3 + 6 * x ^ 2 + 8 * x + 1 := by positivity
  have hN : 0 < x ^ 4 + 4 * x ^ 3 - 4 * x - 1 := by
    have e : x ^ 4 + 4 * x ^ 3 - 4 * x - 1 = (x - 1) * (x ^ 3 + 5 * x ^ 2 + 5 * x + 1) := by ring
    rw [e]; exact mul_pos (by linarith) (by positivity)
  refine ⟨div_pos hN hD, (div_lt_one hD).2 ?_⟩
  nlinarith

/-- 27:C6 — the Fermi constant: with `M_W² = g² v²/4` and `G_F/√2 = g²/(8 M_W²)`, `G_F = 1/(√2 v²)`. -/
theorem fermi_constant (g v G MW2 : ℝ) (hg : g ≠ 0) (hv : v ≠ 0) (hM : MW2 = g ^ 2 * v ^ 2 / 4)
    (hG : G / √2 = g ^ 2 / (8 * MW2)) : G = 1 / (√2 * v ^ 2) := by
  have hv2 : v ^ 2 ≠ 0 := pow_ne_zero 2 hv
  have hg2 : g ^ 2 ≠ 0 := pow_ne_zero 2 hg
  have hs : (√2 : ℝ) ≠ 0 := by positivity
  have h2 : (√2 : ℝ) * √2 = 2 := Real.mul_self_sqrt (by norm_num)
  have e : G / √2 = 1 / (2 * v ^ 2) := by rw [hG, hM]; field_simp; ring
  calc G = √2 * (G / √2) := by field_simp
    _ = √2 * (1 / (2 * v ^ 2)) := by rw [e]
    _ = 1 / (√2 * v ^ 2) := by
        rw [mul_one_div, div_eq_div_iff (mul_ne_zero two_ne_zero hv2) (mul_ne_zero hs hv2), ← mul_assoc, h2, one_mul]

end FRC.FieldsML
