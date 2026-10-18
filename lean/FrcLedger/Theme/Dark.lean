import Mathlib
import FrcLedger.Theme.Chart
import FrcLedger.Theme.Strong

/-!
# FrcLedger.Theme.Dark — the chart theme's readings of the dark sector (32-dark, 18 October 2026)

The clauses of 32-dark that read the continuum law or measured data against the exact content of
`FrcCore/Theme/Dark.lean`. Every measured input enters as a hypothesis (the Hubble rate, the cosmological parameters,
the SPARC-derived accelerations), every conclusion is a rational bound or an inequality, and the exponentials are
bracketed by their Taylor sums (`Real.exp_bound`) as `FRC.Strong.interpolant_discriminant` does. The first-passage
factor as an algebraic identity (`passage_factor`, 32:C7); the reduction `arcosh e^s = √(2s)(1 + O(s))` as a bracket
(`passage_reduction`, 32:C7); the registration theorem's conditional count and chart angle (`rar_from_count`, 32:C6);
the relation as a strictly increasing function of the one variable (`rar_monotone`, 32:X11, P6); the external field
lowering the boost (`nu_antitone`, `collinear_bound`, 32:C9, X6); the scatter's deep rise (`scatter_deep`, 32:C8, X5,
P2); the coherence weight in `[0, 1]` and the bounds `1 ≤ N_eff ≤ N` (`coherence_weight`, `neff_bounds`, 32:C10, X7,
X8); the small-tilt slope one of an odd response (`odd_linear_response`, 32:C4); the sign of `Λ` (`lambda_positive`,
32:C11, X9); the Tully–Fisher zero-point at redshift (`ez_quarter_brackets`, 32:P1); the wide-binary enhancement
(`wide_binary_band`, 32:P3); the pressure-supported offset (`coherence_offset`, 32:P4); the Λ-face floor
(`floor_lambda_face`, 32:C2).
-/

namespace FRC.DarkML

open Real

/-! ## The first-passage law (32:C7, B8) -/

/-- 32:C7, 32:B8 — the first-passage factor is algebraic: for `u ≥ 1` (`u = e^s`), the root `f(1/u) = (1 − √(1 − 1/u²))·u`
of `(z/2)f² − f + z/2 = 0` equals `u − √(u² − 1)`, and `(u − √(u² − 1))(u + √(u² − 1)) = 1`: the factor is
`e^{−δ}` for the `δ` with `e^{δ} = u + √(u² − 1)`, that is `δ = arcosh u`. -/
theorem passage_factor (u : ℝ) (hu : 1 ≤ u) :
    (1 - √(1 - (1 / u) ^ 2)) / (1 / u) = u - √(u ^ 2 - 1) ∧
    (u - √(u ^ 2 - 1)) * (u + √(u ^ 2 - 1)) = 1 ∧
    exp (-Real.log (u + √(u ^ 2 - 1))) = u - √(u ^ 2 - 1) := by
  have hu0 : 0 < u := by linarith
  have hsq : 0 ≤ u ^ 2 - 1 := by nlinarith
  have hs := Real.sq_sqrt hsq
  have hpos : 0 < u + √(u ^ 2 - 1) := by positivity
  have hprod : (u - √(u ^ 2 - 1)) * (u + √(u ^ 2 - 1)) = 1 := by nlinarith [hs]
  refine ⟨?_, hprod, ?_⟩
  · have h1 : 1 - (1 / u) ^ 2 = (u ^ 2 - 1) / u ^ 2 := by field_simp
    rw [h1, Real.sqrt_div hsq, Real.sqrt_sq hu0.le]
    field_simp
  · rw [Real.exp_neg, Real.exp_log hpos]
    field_simp
    linarith [hprod]

/-- 32:C7 — the resolvable reading of the exact transform: for `0 < s` the `δ` with `cosh δ = e^s`, that is
`δ = log(e^s + √(e^{2s} − 1))`, lies between `√(2s)` and `√(2s)·e^{s/2}`, so `arcosh(e^s) = √(2s)(1 + O(s))`
(`cosh δ ≤ e^{δ²/2}` for the lower bound, `cosh δ ≥ 1 + δ²/2` and `e^s − 1 ≤ s e^s` for the upper). -/
theorem passage_reduction (s : ℝ) (hs : 0 < s) :
    √(2 * s) ≤ Real.log (exp s + √(exp s ^ 2 - 1)) ∧
    Real.log (exp s + √(exp s ^ 2 - 1)) ≤ √(2 * s) * exp (s / 2) := by
  set δ := Real.log (exp s + √(exp s ^ 2 - 1)) with hδ
  have hu : 1 < exp s := by rw [← Real.exp_zero]; exact Real.exp_lt_exp.mpr hs
  have hsq : 0 ≤ exp s ^ 2 - 1 := by nlinarith
  have hr := Real.sq_sqrt hsq
  have hpos : 0 < exp s + √(exp s ^ 2 - 1) := by positivity
  have hδ0 : 0 ≤ δ := Real.log_nonneg (by linarith [Real.sqrt_nonneg (exp s ^ 2 - 1)])
  -- cosh δ = e^s
  have hcosh : cosh δ = exp s := by
    rw [Real.cosh_eq, hδ, Real.exp_log hpos, Real.exp_neg, Real.exp_log hpos]
    have hprod : (exp s - √(exp s ^ 2 - 1)) * (exp s + √(exp s ^ 2 - 1)) = 1 := by nlinarith [hr]
    have hinv : (exp s + √(exp s ^ 2 - 1))⁻¹ = exp s - √(exp s ^ 2 - 1) :=
      inv_eq_of_mul_eq_one_right (by rw [mul_comm]; exact hprod)
    rw [hinv]; ring
  constructor
  · -- e^s = cosh δ ≤ e^{δ²/2}, so 2s ≤ δ²
    have h := Real.cosh_le_exp_half_sq δ
    rw [hcosh] at h
    have h2 : s ≤ δ ^ 2 / 2 := Real.exp_le_exp.mp h
    exact Real.sqrt_le_iff.mpr ⟨hδ0, by nlinarith⟩
  · -- cosh δ = 1 + 2 sinh²(δ/2) ≥ 1 + δ²/2, so δ² ≤ 2(e^s − 1) ≤ 2 s e^s
    have hsinh : δ / 2 ≤ sinh (δ / 2) := Real.self_le_sinh_iff.mpr (by linarith)
    have hc2 : cosh δ = 1 + 2 * sinh (δ / 2) ^ 2 := by
      have := Real.cosh_two_mul (δ / 2)
      rw [show 2 * (δ / 2) = δ by ring, Real.cosh_sq'] at this
      linarith
    have hlow : 1 + δ ^ 2 / 2 ≤ exp s := by
      rw [← hcosh, hc2]; nlinarith [hsinh, show 0 ≤ δ / 2 by linarith]
    have hexp : exp s - 1 ≤ s * exp s := by
      have := Real.add_one_le_exp (-s)
      have := mul_le_mul_of_nonneg_left this (Real.exp_pos s).le
      rw [← Real.exp_add, add_neg_cancel, Real.exp_zero] at this
      nlinarith
    have hδ2 : δ ^ 2 ≤ 2 * s * exp s := by nlinarith
    have hsqe : √(exp s) = exp (s / 2) := by
      have h2 : exp (s / 2) ^ 2 = exp s := by
        rw [← Real.exp_nat_mul]; congr 1; push_cast; ring
      rw [← h2, Real.sqrt_sq (Real.exp_pos _).le]
    have hrhs : √(2 * s * exp s) = √(2 * s) * exp (s / 2) := by
      rw [Real.sqrt_mul (by positivity : (0 : ℝ) ≤ 2 * s), hsqe]
    rw [← hrhs]
    exact Real.le_sqrt_of_sq_le hδ2

/-! ## The registration theorem (32:C6, X4, X11, P6) -/

/-- 32:C6, 32:X4 — the conditional count: with `f = 1 − e^{−√x} > 0`, `f · g_obs = g_b ↔ g_obs = g_b / f`; and the chart
angle `α = arcsin(√(e^{−√x}))` has `sin²α = e^{−√x}` and `cos²α = 1 − e^{−√x} = f`, the resolved fraction. -/
theorem rar_from_count (x gb gobs : ℝ) (hx : 0 < x) :
    0 < 1 - exp (-√x) ∧
    ((1 - exp (-√x)) * gobs = gb ↔ gobs = gb / (1 - exp (-√x))) ∧
    sin (arcsin (√(exp (-√x)))) ^ 2 = exp (-√x) ∧
    cos (arcsin (√(exp (-√x)))) ^ 2 = 1 - exp (-√x) := by
  have hsx : 0 < √x := Real.sqrt_pos.mpr hx
  have he : exp (-√x) < 1 := by rw [← Real.exp_zero]; exact Real.exp_lt_exp.mpr (by linarith)
  have hf : 0 < 1 - exp (-√x) := by linarith
  have he0 : 0 ≤ exp (-√x) := (Real.exp_pos _).le
  have hsq : √(exp (-√x)) ≤ 1 := Real.sqrt_le_one.mpr he.le
  have hsin : sin (arcsin (√(exp (-√x)))) = √(exp (-√x)) :=
    Real.sin_arcsin (by linarith [Real.sqrt_nonneg (exp (-√x))]) hsq
  refine ⟨hf, ⟨fun h => ?_, fun h => ?_⟩, ?_, ?_⟩
  · rw [eq_div_iff hf.ne', mul_comm]; exact h
  · rw [h, mul_div_cancel₀ _ hf.ne']
  · rw [hsin, Real.sq_sqrt he0]
  · rw [Real.cos_sq', hsin, Real.sq_sqrt he0]

/-- 32:X11, 32:P6 — the relation is a strictly increasing function of the one variable: `t ↦ t²/(1 − e^{−t})` is
strictly increasing on `t > 0` (its derivative `(2t(1 − e^{−t}) − t² e^{−t})/(1 − e^{−t})²` is positive, because
`2(e^t − 1) > t`), so `x ↦ x/(1 − e^{−√x})` is strictly increasing on `x > 0`: one registered acceleration fixes one
baryonic acceleration, with no second component and no direction in the law. -/
theorem rar_monotone : StrictMonoOn (fun x : ℝ => x / (1 - exp (-√x))) (Set.Ioi 0) := by
  have hφ : StrictMonoOn (fun t : ℝ => t ^ 2 / (1 - exp (-t))) (Set.Ioi 0) := by
    apply strictMonoOn_of_deriv_pos (convex_Ioi 0)
    · apply ContinuousOn.div (by fun_prop) (by fun_prop)
      intro t ht
      have : exp (-t) < 1 := by rw [← Real.exp_zero]; exact Real.exp_lt_exp.mpr (by simpa using ht)
      linarith
    · intro t ht
      rw [interior_Ioi] at ht
      have ht0 : 0 < t := ht
      have he : exp (-t) < 1 := by rw [← Real.exp_zero]; exact Real.exp_lt_exp.mpr (by linarith)
      have hd : HasDerivAt (fun t : ℝ => t ^ 2 / (1 - exp (-t)))
          ((2 * t * (1 - exp (-t)) - t ^ 2 * exp (-t)) / (1 - exp (-t)) ^ 2) t := by
        have h1 : HasDerivAt (fun t : ℝ => t ^ 2) (2 * t) t := by
          simpa using hasDerivAt_pow 2 t
        have h2 : HasDerivAt (fun t : ℝ => 1 - exp (-t)) (exp (-t)) t := by
          have := ((Real.hasDerivAt_exp (-t)).comp t (hasDerivAt_neg t))
          have h3 := this.const_sub 1
          simpa using h3
        have := h1.div h2 (by linarith)
        convert this using 1
      rw [hd.deriv]
      apply div_pos
      · -- 2(1 − e^{−t}) − t e^{−t} > 0 ⟺ 2(e^t − 1) > t
        have h3 : t + 1 < exp t := Real.add_one_lt_exp ht0.ne'
        have h4 : exp (-t) * exp t = 1 := by rw [← Real.exp_add]; simp
        have h5 : 0 < exp (-t) := Real.exp_pos _
        nlinarith [h3, h4, h5, mul_pos ht0 h5]
      · positivity
  intro x hx y hy hxy
  have hx0 : (0 : ℝ) < x := hx
  have hy0 : (0 : ℝ) < y := hy
  have hsx : 0 < √x := Real.sqrt_pos.mpr hx0
  have hsy : 0 < √y := Real.sqrt_pos.mpr hy0
  have := hφ (show √x ∈ Set.Ioi 0 from hsx) (show √y ∈ Set.Ioi 0 from hsy) (Real.sqrt_lt_sqrt hx0.le hxy)
  simpa [Real.sq_sqrt hx0.le, Real.sq_sqrt hy0.le] using this

/-! ## The external field (32:C9, X6) -/

/-- 32:C9, 32:X6 — a stronger total field lowers the boost: `ν(y) = 1/(1 − e^{−√y})` is strictly decreasing, so the
environment uses up the deep enhancement. -/
theorem nu_antitone (y₁ y₂ : ℝ) (h0 : 0 < y₁) (h : y₁ < y₂) :
    1 / (1 - exp (-√y₂)) < 1 / (1 - exp (-√y₁)) := by
  have hs1 : 0 < √y₁ := Real.sqrt_pos.mpr h0
  have hs : √y₁ < √y₂ := Real.sqrt_lt_sqrt h0.le h
  have he1 : exp (-√y₁) < 1 := by rw [← Real.exp_zero]; exact Real.exp_lt_exp.mpr (by linarith)
  have he : exp (-√y₂) < exp (-√y₁) := Real.exp_lt_exp.mpr (by linarith)
  exact one_div_lt_one_div_of_lt (by linarith) (by linarith)

/-- 32:C9 — the argument of the registration is the magnitude of the vector total field, bounded by the collinear
sum `|g_in| + |g_ext|` (the triangle inequality), the estimate the text uses. -/
theorem collinear_bound (gin gext : EuclideanSpace ℝ (Fin 3)) : ‖gin + gext‖ ≤ ‖gin‖ + ‖gext‖ :=
  norm_add_le gin gext

/-! ## The scatter (32:C8, X5, P2) -/

/-- 32:C8, 32:X5, 32:P2 — the scatter's deep rise: `tan²α = 1/(e^{√x} − 1)` is strictly decreasing in `x` (the
scatter is smallest at high acceleration), and for `0 < x ≤ 1` it is bracketed by `(1 − √x)/√x` and `1/√x`, so
`tan α` rises as `x^{−1/4}` into the deep regime. -/
theorem scatter_deep (x y : ℝ) (hx : 0 < x) (hxy : x < y) :
    1 / (exp (√y) - 1) < 1 / (exp (√x) - 1) ∧
    (x ≤ 1 → (1 - √x) / √x ≤ 1 / (exp (√x) - 1) ∧ 1 / (exp (√x) - 1) < 1 / √x) := by
  have hsx : 0 < √x := Real.sqrt_pos.mpr hx
  have hsxy : √x < √y := Real.sqrt_lt_sqrt hx.le hxy
  have hex : 1 < exp (√x) := by rw [← Real.exp_zero]; exact Real.exp_lt_exp.mpr hsx
  have hey : exp (√x) < exp (√y) := Real.exp_lt_exp.mpr hsxy
  refine ⟨?_, fun hx1 => ⟨?_, ?_⟩⟩
  · apply one_div_lt_one_div_of_lt (by linarith) (by linarith)
  · -- (1 − t)(e^t − 1) ≤ t, from e^t(1 − t) ≤ e^t e^{−t} = 1 (e^{−t} ≥ 1 − t)
    have hneg := Real.add_one_le_exp (-√x)
    have hprod : exp (√x) * (1 - √x) ≤ 1 := by
      have := mul_le_mul_of_nonneg_left hneg (Real.exp_pos (√x)).le
      rw [← Real.exp_add, add_neg_cancel, Real.exp_zero] at this
      linarith
    rw [div_le_div_iff₀ hsx (by linarith)]
    nlinarith [hprod]
  · -- e^t − 1 > t for t > 0
    have := Real.add_one_lt_exp (ne_of_gt hsx)
    exact one_div_lt_one_div_of_lt hsx (by linarith)

/-! ## The coherence law (32:C10, X7, X8, B9) -/

/-- 32:C10, 32:X7, 32:B9 — the bulk-coherence weight of unit phasors is at most one, `‖Σ z_k / n‖² ≤ 1`, and equals one
for a clump sharing one phase. -/
theorem coherence_weight (n : ℕ) (hn : 0 < n) (z : Fin n → ℂ) (h : ∀ k, ‖z k‖ = 1) (z₀ : ℂ) (h₀ : ‖z₀‖ = 1) :
    ‖(∑ k, z k) / n‖ ^ 2 ≤ 1 ∧ ‖(∑ _k : Fin n, z₀) / n‖ ^ 2 = 1 := by
  have hn' : (0 : ℝ) < n := by exact_mod_cast hn
  constructor
  · have h1 : ‖∑ k, z k‖ ≤ n := by
      calc ‖∑ k, z k‖ ≤ ∑ k, ‖z k‖ := norm_sum_le _ _
        _ = ∑ _k : Fin n, (1 : ℝ) := Finset.sum_congr rfl (fun k _ => h k)
        _ = n := by simp
    have h2 : ‖(∑ k, z k) / n‖ ≤ 1 := by
      rw [norm_div, Complex.norm_natCast, div_le_one hn']; exact h1
    nlinarith [norm_nonneg ((∑ k, z k) / n)]
  · have hnz : (n : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr hn.ne'
    rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul, mul_div_assoc,
      show (n : ℂ) * (z₀ / n) = z₀ by field_simp, h₀]; norm_num

/-- 32:X8, 32:C10 — the effective number of coherent composites, `N_eff = (Σ√g_i)²/Σ g_i`, lies between one and `N`:
`Σ g ≤ (Σ √g)² ≤ N · Σ g` for non-negative `g` (the cross terms non-negative; Cauchy–Schwarz). -/
theorem neff_bounds (n : ℕ) (g : Fin n → ℝ) (hg : ∀ k, 0 ≤ g k) :
    ∑ k, g k ≤ (∑ k, √(g k)) ^ 2 ∧ (∑ k, √(g k)) ^ 2 ≤ n * ∑ k, g k := by
  constructor
  · have : ∑ k, g k = ∑ k, √(g k) ^ 2 := Finset.sum_congr rfl (fun k _ => (Real.sq_sqrt (hg k)).symm)
    rw [this]
    exact Finset.sum_sq_le_sq_sum_of_nonneg (fun k _ => Real.sqrt_nonneg _)
  · have := sq_sum_le_card_mul_sum_sq (s := Finset.univ) (f := fun k => √(g k))
    simp only [Finset.card_univ, Fintype.card_fin] at this
    calc (∑ k, √(g k)) ^ 2 ≤ n * ∑ k, √(g k) ^ 2 := this
      _ = n * ∑ k, g k := by
        congr 1; exact Finset.sum_congr rfl (fun k _ => Real.sq_sqrt (hg k))

/-! ## The deep regime (32:C4) -/

/-- 32:C4 — the small-tilt response is linear: an odd function `f` (the transmitted flux against the tilt) with
derivative `χ ≠ 0` at zero has `f(T)/(χT) → 1` as `T → 0`, the log-slope one of the stationary mean — the mean force
Newtonian at leading order, the square root a registration, not a force law. -/
theorem odd_linear_response (f : ℝ → ℝ) (χ : ℝ) (hodd : ∀ T, f (-T) = -f T) (hd : HasDerivAt f χ 0)
    (hχ : χ ≠ 0) :
    Filter.Tendsto (fun T : ℝ => f T / (χ * T)) (nhdsWithin 0 {0}ᶜ) (nhds 1) := by
  have hf0 : f 0 = 0 := by
    have := hodd 0; simp at this; linarith
  have h := (hasDerivAt_iff_tendsto_slope_zero.mp hd)
  simp only [zero_add, hf0, sub_zero, smul_eq_mul] at h
  have h2 : Filter.Tendsto (fun t : ℝ => t⁻¹ * f t / χ) (nhdsWithin 0 {0}ᶜ) (nhds (χ / χ)) :=
    h.div_const χ
  rw [div_self hχ] at h2
  refine h2.congr' ?_
  filter_upwards [self_mem_nhdsWithin] with t ht
  have ht0 : t ≠ 0 := ht
  field_simp

/-! ## The cosmological constant (32:C11, X9, X10) -/

/-- 32:C11, 32:X9, 32:X10 — the curvature of the finite chart is positive: `Λ = 3/r² > 0` for `r ≠ 0`, and with
`r² = S/π` the product `Λ · S` is `3π`, the one cardinality read twice (`lambda_face`). -/
theorem lambda_positive (r S : ℝ) (hr : r ≠ 0) (hS : r ^ 2 = S / π) : 0 < 3 / r ^ 2 ∧ 3 / r ^ 2 * S = 3 * π := by
  have hπ := Real.pi_pos
  have hr2 : 0 < r ^ 2 := by positivity
  have hS0 : S ≠ 0 := by
    intro h0; rw [h0, zero_div] at hS; exact hr (pow_eq_zero_iff two_ne_zero |>.mp hS)
  refine ⟨by positivity, ?_⟩
  rw [hS]; field_simp

/-! ## The predictions (32:P1, P3, P4) and the Λ-face floor (32:C2) -/

/-- A bracket of `√a` from a bracket of `a` and the squares of the ends. -/
theorem sqrt_step (a lo hi lo' hi' : ℝ) (h1 : lo < a) (h2 : a < hi) (h3 : lo' ^ 2 ≤ lo) (h4 : hi ≤ hi' ^ 2)
    (h5 : 0 ≤ lo') (h6 : 0 < hi') : lo' < √a ∧ √a < hi' :=
  ⟨(Real.lt_sqrt h5).mpr (by nlinarith), (Real.sqrt_lt' h6).mpr (by nlinarith)⟩

/-- 32:P1 — the Tully–Fisher zero-point at redshift: `E(z)^{1/4}` with `E(z)² = Ω_m(1+z)³ + 1 − Ω_m` at `Ω_m = 0.315`
(Planck 2018) is between `1.072` and `1.073` at `z = 0.5`, between `1.156` and `1.158` at `z = 1`, between `1.319` and
`1.320` at `z = 2` — the paper's `+7 %`, `+16 %`, `+32 %` (`v_flat ∝ a₀^{1/4} ∝ E(z)^{1/4}`, `running_floor`). -/
theorem ez_quarter_brackets :
    (1.072 : ℝ) < √(√(√(0.315 * 1.5 ^ 3 + 0.685))) ∧ √(√(√(0.315 * 1.5 ^ 3 + 0.685))) < 1.073 ∧
    (1.156 : ℝ) < √(√(√(0.315 * 2 ^ 3 + 0.685))) ∧ √(√(√(0.315 * 2 ^ 3 + 0.685))) < 1.158 ∧
    (1.319 : ℝ) < √(√(√(0.315 * 3 ^ 3 + 0.685))) ∧ √(√(√(0.315 * 3 ^ 3 + 0.685))) < 1.320 := by
  have b1 : (1.3221 : ℝ) < √(0.315 * 1.5 ^ 3 + 0.685) ∧ √(0.315 * 1.5 ^ 3 + 0.685) < 1.3222 :=
    ⟨(Real.lt_sqrt (by norm_num)).mpr (by norm_num), (Real.sqrt_lt' (by norm_num)).mpr (by norm_num)⟩
  have b2 : (1.7902 : ℝ) < √(0.315 * 2 ^ 3 + 0.685) ∧ √(0.315 * 2 ^ 3 + 0.685) < 1.7903 :=
    ⟨(Real.lt_sqrt (by norm_num)).mpr (by norm_num), (Real.sqrt_lt' (by norm_num)).mpr (by norm_num)⟩
  have b3 : (3.0315 : ℝ) < √(0.315 * 3 ^ 3 + 0.685) ∧ √(0.315 * 3 ^ 3 + 0.685) < 3.0316 :=
    ⟨(Real.lt_sqrt (by norm_num)).mpr (by norm_num), (Real.sqrt_lt' (by norm_num)).mpr (by norm_num)⟩
  have c1 := sqrt_step _ _ _ 1.1498 1.1499 b1.1 b1.2 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c2 := sqrt_step _ _ _ 1.3379 1.3381 b2.1 b2.2 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c3 := sqrt_step _ _ _ 1.7411 1.7412 b3.1 b3.2 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have d1 := sqrt_step _ _ _ 1.072 1.073 c1.1 c1.2 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have d2 := sqrt_step _ _ _ 1.156 1.158 c2.1 c2.2 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have d3 := sqrt_step _ _ _ 1.319 1.320 c3.1 c3.2 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  exact ⟨d1.1, d1.2, d2.1, d2.2, d3.1, d3.2⟩

/-- The Taylor brackets of `e^t` below one: a lower bound of `e^{t₁}` and an upper bound of `e^{t₂}` for
`0 ≤ t₁ < t₂ ≤ 1`, by `Real.exp_bound` at order nine. -/
theorem exp_tail_bounds (t₁ t₂ lo hi : ℝ) (h1 : 0 ≤ t₁) (h2 : t₁ ≤ 1) (h3 : 0 ≤ t₂) (h4 : t₂ ≤ 1)
    (hlo : lo ≤ (∑ i ∈ Finset.range 9, t₁ ^ i / (Nat.factorial i)) - t₁ ^ 9 * ((9 : ℕ).succ / ((Nat.factorial 9) * 9)))
    (hhi : (∑ i ∈ Finset.range 9, t₂ ^ i / (Nat.factorial i)) + t₂ ^ 9 * ((9 : ℕ).succ / ((Nat.factorial 9) * 9)) ≤ hi) :
    lo ≤ exp t₁ ∧ exp t₂ ≤ hi := by
  constructor
  · have h := abs_le.1 (Real.exp_bound (x := t₁) (by rw [abs_of_nonneg h1]; exact h2) (n := 9) (by norm_num))
    rw [abs_of_nonneg h1] at h
    linarith [h.1]
  · have h := abs_le.1 (Real.exp_bound (x := t₂) (by rw [abs_of_nonneg h3]; exact h4) (n := 9) (by norm_num))
    rw [abs_of_nonneg h3] at h
    linarith [h.2]

/-- The chain from a bracket of `√y` to a bracket of `√ν − 1`, `ν = 1/(1 − e^{−√y})`, through `e^{−√y} = e^{−1} e^{−(√y − 1)}`. -/
theorem nu_chain (y s₁ s₂ lo hi a b : ℝ) (hs1 : 1 ≤ s₁) (hy1 : s₁ ^ 2 < y) (hy2 : y < s₂ ^ 2) (hs20 : 1 ≤ s₂)
    (elo : lo ≤ exp (s₁ - 1)) (ehi : exp (s₂ - 1) ≤ hi) (hlo : 0 < lo)
    (ha : 0 ≤ a) (hab : a < b)
    (hA : 1 - 1 / (1 + a) ^ 2 ≤ 0.36787944116 / hi) (hB : 0.3678794412 / lo ≤ 1 - 1 / (1 + b) ^ 2) :
    a < √(1 / (1 - exp (-√y))) - 1 ∧ √(1 / (1 - exp (-√y))) - 1 < b := by
  have hs1' : s₁ < √y := (Real.lt_sqrt (by linarith)).mpr hy1
  have hs2' : √y < s₂ := (Real.sqrt_lt' (by linarith)).mpr hy2
  have hm1 := Real.exp_neg_one_gt_d9
  have hm2 := Real.exp_neg_one_lt_d9
  have hsplit : exp (-√y) = exp (-1) * exp (-(√y - 1)) := by rw [← Real.exp_add]; ring_nf
  have he1 : exp (-(√y - 1)) ≤ 1 / lo := by
    rw [Real.exp_neg, inv_eq_one_div]
    apply one_div_le_one_div_of_le hlo
    calc lo ≤ exp (s₁ - 1) := elo
      _ ≤ exp (√y - 1) := Real.exp_le_exp.mpr (by linarith)
  have he2 : 1 / hi ≤ exp (-(√y - 1)) := by
    rw [Real.exp_neg, inv_eq_one_div]
    apply one_div_le_one_div_of_le (Real.exp_pos _)
    calc exp (√y - 1) ≤ exp (s₂ - 1) := Real.exp_le_exp.mpr (by linarith)
      _ ≤ hi := ehi
  have hhi : 0 < hi := lt_of_lt_of_le (Real.exp_pos _) ehi
  have hE1 : exp (-√y) < 0.3678794412 / lo := by
    rw [hsplit]
    calc exp (-1) * exp (-(√y - 1)) ≤ exp (-1) * (1 / lo) := mul_le_mul_of_nonneg_left he1 (Real.exp_pos _).le
      _ < 0.3678794412 * (1 / lo) := by apply mul_lt_mul_of_pos_right hm2; positivity
      _ = 0.3678794412 / lo := by ring
  have hE2 : 0.36787944116 / hi < exp (-√y) := by
    rw [hsplit]
    calc (0.36787944116 : ℝ) / hi = 0.36787944116 * (1 / hi) := by ring
      _ < exp (-1) * (1 / hi) := by apply mul_lt_mul_of_pos_right hm1; positivity
      _ ≤ exp (-1) * exp (-(√y - 1)) := mul_le_mul_of_nonneg_left he2 (Real.exp_pos _).le
  have hlt1 : exp (-√y) < 1 := by rw [← Real.exp_zero]; exact Real.exp_lt_exp.mpr (by linarith)
  have hden : 0 < 1 - exp (-√y) := by linarith
  -- (1 + a)² < ν < (1 + b)², with ν = 1/(1 − e^{−√y})
  have hb0 : 0 < 1 + b := by linarith
  have ha0 : 0 < 1 + a := by linarith
  have hν1 : (1 + a) ^ 2 < 1 / (1 - exp (-√y)) := by
    rw [lt_div_iff₀ hden]
    have : 1 - 1 / (1 + a) ^ 2 < exp (-√y) := lt_of_le_of_lt hA hE2
    have h' : (1 + a) ^ 2 * (1 - exp (-√y)) < (1 + a) ^ 2 * (1 / (1 + a) ^ 2) := by
      apply mul_lt_mul_of_pos_left _ (by positivity); linarith
    rw [mul_one_div_cancel (by positivity)] at h'
    exact h'
  have hν2 : 1 / (1 - exp (-√y)) < (1 + b) ^ 2 := by
    rw [div_lt_iff₀ hden]
    have : exp (-√y) < 1 - 1 / (1 + b) ^ 2 := lt_of_lt_of_le hE1 hB
    have h' : (1 + b) ^ 2 * (1 / (1 + b) ^ 2) < (1 + b) ^ 2 * (1 - exp (-√y)) := by
      apply mul_lt_mul_of_pos_left _ (by positivity); linarith
    rw [mul_one_div_cancel (by positivity)] at h'
    exact h'
  constructor
  · have := (Real.lt_sqrt ha0.le).mpr hν1; linarith
  · have := (Real.sqrt_lt' hb0).mpr hν2; linarith

/-- 32:P3 — wide binaries with the Galactic field `g_ext = 1.8a₀`: at the total `y = (g_b + g_ext)/a₀` of `2.6535`,
`2.0134` and `1.8533` (10, 20 and 40 kAU for `1.5 M_⊙`) the velocity enhancement `√ν − 1` lies between `0.115` and
`0.116`, between `0.148` and `0.149`, and between `0.159` and `0.160`: the paper's `12–16 %`. -/
theorem wide_binary_band :
    (0.115 : ℝ) < √(1 / (1 - exp (-√2.6535))) - 1 ∧ √(1 / (1 - exp (-√2.6535))) - 1 < 0.116 ∧
    (0.148 : ℝ) < √(1 / (1 - exp (-√2.0134))) - 1 ∧ √(1 / (1 - exp (-√2.0134))) - 1 < 0.149 ∧
    (0.159 : ℝ) < √(1 / (1 - exp (-√1.8533))) - 1 ∧ √(1 / (1 - exp (-√1.8533))) - 1 < 0.160 := by
  have e1 := exp_tail_bounds 0.6289 0.6290 1.875545 1.875735 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [Finset.sum_range_succ, Nat.factorial]) (by norm_num [Finset.sum_range_succ, Nat.factorial])
  have e2 := exp_tail_bounds 0.4189 0.4190 1.520287 1.520441 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [Finset.sum_range_succ, Nat.factorial]) (by norm_num [Finset.sum_range_succ, Nat.factorial])
  have e3 := exp_tail_bounds 0.3613 0.3614 1.435193 1.435338 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [Finset.sum_range_succ, Nat.factorial]) (by norm_num [Finset.sum_range_succ, Nat.factorial])
  have c1 := nu_chain 2.6535 1.6289 1.6290 1.875545 1.875735 0.115 0.116 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num at e1 ⊢; exact e1.1) (by norm_num at e1 ⊢; exact e1.2) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num)
  have c2 := nu_chain 2.0134 1.4189 1.4190 1.520287 1.520441 0.148 0.149 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num at e2 ⊢; exact e2.1) (by norm_num at e2 ⊢; exact e2.2) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num)
  have c3 := nu_chain 1.8533 1.3613 1.3614 1.435193 1.435338 0.159 0.160 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num at e3 ⊢; exact e3.1) (by norm_num at e3 ⊢; exact e3.2) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num)
  exact ⟨c1.1, c1.2, c2.1, c2.2, c3.1, c3.2⟩

/-- `log 1.25` by the series of `−log(1 − 0.2)` to eight terms: between `0.2231428` and `0.2231443`. -/
theorem log_five_fourths_bounds : (0.2231428 : ℝ) < Real.log 1.25 ∧ Real.log 1.25 < 0.2231443 := by
  have h := Real.abs_log_sub_add_sum_range_le (x := 0.2) (by rw [abs_of_pos (by norm_num)]; norm_num) 8
  rw [abs_of_pos (by norm_num : (0 : ℝ) < 0.2)] at h
  have e : (1 : ℝ) - 0.2 = 1 / 1.25 := by norm_num
  rw [e, Real.log_div one_ne_zero (by norm_num), Real.log_one, zero_sub] at h
  rw [abs_le] at h
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith [h.1, h.2]

/-- `log 10 = 3 log 2 + log 1.25`: between `2.3025843` and `2.3025859`. -/
theorem log_ten_bounds : (2.3025843 : ℝ) < Real.log 10 ∧ Real.log 10 < 2.3025859 := by
  have h2a := Real.log_two_gt_d9
  have h2b := Real.log_two_lt_d9
  have h5 := log_five_fourths_bounds
  have e : Real.log 10 = 3 * Real.log 2 + Real.log 1.25 := by
    rw [← Real.log_rpow (by norm_num), ← Real.log_mul (by norm_num) (by norm_num)]
    norm_num
  rw [e]
  constructor <;> linarith [h5.1, h5.2]

/-- 32:P4 — pressure-supported systems lie below the cold-disk relation by `log₁₀ √w`, `w = 1/(1 + (σ_v/v)²)`:
between `−0.0485` and `−0.0484` at `σ_v/v = 1/2` and between `−0.1506` and `−0.1505` at `σ_v/v = 1`
(`log₁₀ √w = −log(1 + r²)/(2 log 10)`): the paper's `−0.05` to `−0.15 dex`. -/
theorem coherence_offset :
    (-0.0485 : ℝ) < -Real.log (1 + (1 / 2) ^ 2) / (2 * Real.log 10) ∧ -Real.log (1 + (1 / 2) ^ 2) / (2 * Real.log 10) < -0.0484 ∧
    (-0.1506 : ℝ) < -Real.log (1 + 1 ^ 2) / (2 * Real.log 10) ∧ -Real.log (1 + 1 ^ 2) / (2 * Real.log 10) < -0.1505 := by
  have h10 := log_ten_bounds
  have h5 := log_five_fourths_bounds
  have h2a := Real.log_two_gt_d9
  have h2b := Real.log_two_lt_d9
  have e1 : (1 : ℝ) + (1 / 2) ^ 2 = 1.25 := by norm_num
  have e2 : (1 : ℝ) + 1 ^ 2 = 2 := by norm_num
  rw [e1, e2]
  have hpos : 0 < 2 * Real.log 10 := by linarith [h10.1]
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [lt_div_iff₀ hpos]; nlinarith [h5.2, h10.1]
  · rw [div_lt_iff₀ hpos]; nlinarith [h5.1, h10.2]
  · rw [lt_div_iff₀ hpos]; nlinarith [h2b, h10.1]
  · rw [div_lt_iff₀ hpos]; nlinarith [h2a, h10.2]

/-- 32:C2, 32:X2, 32:X10 — the Λ-face floor: with the Carrier's horizon `r_H = √(S/π)·ℓ_P` at `S = 3.3 × 10¹²²` [data] and
`H_Λ = c/r_H`, the constant floor `cH_Λ/2π = c²/(2ℓ_P√(πS))` lies between `8.63` and `8.64 × 10⁻¹¹ m s⁻²` (the
text's `0.86 × 10⁻¹⁰`), the branch the running floor excludes. -/
theorem floor_lambda_face (c lP S : ℝ) (hc : c = 299792458) (hl : lP = 1.616255e-35) (hS : S = 3.3e122) :
    (8.63e-11 : ℝ) < c ^ 2 / (2 * lP * √(π * S)) ∧ c ^ 2 / (2 * lP * √(π * S)) < 8.64e-11 := by
  subst hc hl hS
  have hπ1 := Real.pi_gt_d6
  have hπ2 := Real.pi_lt_d6
  have hA1 : (1.0367253e123 : ℝ) < π * 3.3e122 := by nlinarith
  have hA2 : π * 3.3e122 < (1.0367257e123 : ℝ) := by nlinarith
  have hs1 : (3.219821e61 : ℝ) < √(π * 3.3e122) := (Real.lt_sqrt (by norm_num)).mpr (by nlinarith)
  have hs2 : √(π * 3.3e122) < (3.219823e61 : ℝ) := (Real.sqrt_lt' (by norm_num)).mpr (by nlinarith)
  have hden : (0 : ℝ) < 2 * 1.616255e-35 * √(π * 3.3e122) := by positivity
  constructor
  · rw [lt_div_iff₀ hden]; nlinarith
  · rw [div_lt_iff₀ hden]; nlinarith

end FRC.DarkML
