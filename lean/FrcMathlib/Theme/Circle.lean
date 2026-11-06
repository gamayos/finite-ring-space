import Mathlib

/-!
# FrcMathlib.Theme.Circle — 1-algebra's circle read against the reals (the chart theme)

The chart clause of 1:E4: the drive's cycle `C_N`, read in `U(1)` by `k ↦ e^{2πik/N}`, is a `π/N`-net, and the rounding
`k(θ) = round(Nθ/2π)` respects the group law up to one step. The exact content of the row, the rounding of a framed
turn within half a step and its defect `−1`, `0` or `1`, is the core's (`FrcCore/Theme/Framed.lean`, `round_exists`,
`round_defect`). Moved from `FrcMathlib/Algebra.lean` on 6 November 2026: a Mathlib theme outside the chart holds no
reals (gate G09). The names stay in `FRC.AlgebraML`, so the paper module's aliases `FRC.Algebra.circle_net` and
`FRC.Algebra.group_law_defect` resolve as before.
-/

namespace FRC.AlgebraML

open Real

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

end FRC.AlgebraML
