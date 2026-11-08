import Mathlib
import FrcMathlib.Theme.Hadrons

/-!
# FrcMathlib.Theme.YangMills — the yangmills theme's readings on Mathlib (46-yangmills, 8 November 2026)

The two clauses of 46-yangmills that Mathlib states beyond the core without leaving the integers and the rationals: the
Faulhaber identity of the scalar loop for every `N` (46:C13; the core proves it to `N = 400` and as residues on the shell
`173`), and the radial ratio's confrontations as rational brackets (46:P3) with the Airy ratio of the hadrons theme. The
chart clauses of the paper on the reals — the running coupling, the Herbst comparison, the plaquette channel, the operator
family — live in the chart theme's `FrcMathlib/Theme/Gauge.lean` (gate G09: a Mathlib theme outside the chart holds no
reals). The exact content of the paper is the core's (`FrcCore/Theme/YangMills.lean`, no axioms). Classical (tier 2).
-/

namespace FRC.YangMillsML

open Finset

/-! ## 46:C13 — the Faulhaber identity for every `N` -/

/-- The midpoint sum of the scalar loop, `Σ_{k<N} (N − 2k − 1)²`, as a sum over `Finset.range`. -/
def sq (N : ℕ) : ℤ := ∑ k ∈ range N, ((N : ℤ) - 2 * (k : ℤ) - 1) ^ 2

/-- The two-step recursion: the terms of `sq (N + 2)` are `(N + 1)²` at `k = 0`, the terms of `sq N` shifted by one, and
`(N + 1)²` at `k = N + 1`. -/
lemma sq_succ_succ (N : ℕ) : sq (N + 2) = sq N + 2 * ((N : ℤ) + 1) ^ 2 := by
  unfold sq
  rw [sum_range_succ, sum_range_succ']
  push_cast
  have h : ∀ k ∈ range N, ((N : ℤ) + 2 - 2 * ((k : ℤ) + 1) - 1) ^ 2 = ((N : ℤ) - 2 * (k : ℤ) - 1) ^ 2 := by
    intro k _; ring
  rw [sum_congr rfl h]
  ring

/-- 46:C13 — the Faulhaber identity for every `N`: `3 Σ_{k<N} (N − 2k − 1)² = N (N² − 1)`. -/
theorem faulhaber_third_all (N : ℕ) : 3 * sq N = (N : ℤ) * ((N : ℤ) ^ 2 - 1) := by
  induction N using Nat.twoStepInduction with
  | zero => simp [sq]
  | one => simp [sq]
  | more N ih0 _ =>
    rw [sq_succ_succ, mul_add, ih0]
    push_cast
    ring

/-! ## 46:P3 — the radial ratio's confrontations -/

/-- 46:P3 [chart] — **the radial ratio against the lattice**, as rational brackets. With the chart's reading
`E₁/E₀ = 1.4915` of the operator form (`chart_yangmills.wrap_spectrum`, the same on every `a`, `ϰ`): it lies within half a
standard deviation of the 1999 ratio `1.544(112)` (`6.50(44)/4.21(11)`, Morningstar–Peardon); the 2020 ratio `1.720(16)`
(`5.855(41)/3.405(21)`, Athenodorou–Teper) excludes it by more than `14` standard deviations, while the nonrelativistic
Airy ratio `4.08795/2.33811` (`FRC.HadronsML.airy_ratio`, in `(1.748, 1.7485)`) lies within two of them; the nucleon's
`1440/939` lies within `3 %` of the reading. -/
theorem radial_ratio_confrontation (r : ℚ) (hr : r = 1.4915) :
    |r - 1.544| < 0.5 * 0.112 ∧ 14 * 0.016 < 1.720 - r ∧ |(4.08795 : ℚ) / 2.33811 - 1.720| < 2 * 0.016 ∧
    (1.748 : ℚ) < 4.08795 / 2.33811 ∧ |(1440 : ℚ) / 939 - r| < 0.03 * r := by
  subst hr
  have h := FRC.HadronsML.airy_ratio
  refine ⟨by rw [abs_lt]; constructor <;> norm_num, by norm_num, by rw [abs_lt]; constructor <;> linarith [h.1, h.2], h.1, ?_⟩
  rw [abs_lt]; constructor <;> norm_num

end FRC.YangMillsML
