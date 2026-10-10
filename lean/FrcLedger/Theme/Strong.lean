import Mathlib
import FrcLedger.Theme.Chart

/-!
# FrcLedger.Theme.Strong — the chart theme's strong field, crossover and series (10 October 2026)

The readings of 21-gravity on the reals, moved from the paper module `FrcLedger/Gravity.lean` (which keeps every old
name as an alias), every numeral re-anchored to the ledger's scale import (00:A7: `ln Ω = 283.5`, `Ω = 1.3 × 10¹²³`;
`Theme/Chart.lean`'s `ln_omega_ledger`). The strong field: the operational cut `e^{2M/r_f} = Ω` with the ordering
`r_* < r_f < M` exactly when `M > (ln Ω/2)²` (21:C12, P7); the photon sphere at `r = 2Gm` with `b_c = 2e·Gm` as the
minimum of `r e^{2Gm/r}` (21:C12, P1); the shadow `+4.6 %` and ringdown `−4.4 %` bracketed from `e` and `√3` (21:P1);
the innermost stable orbit at `r = 3 + √5` and the efficiency `5.48 %` against Schwarzschild's `5.72 %` (21:P1); the
capacity ratio `1/ln²Ω = 1.24 × 10⁻⁵` at `283.5` (21:C13); the redshift's linear form (21:C4). The crossover: the
registration root `η` of `wη² − 2η + w = 0` in `(0, 1)`, the crossover squeezed between its deep and Newtonian
limits, the Tully–Fisher algebra (21:C19, P4, X2); the discriminant `0.051` at `g_N = 5a₀` against the simple
interpolant (21:P4). The primordial fixed point `n_s = 1` (21:C18; the tilt at `283.5` is `Chart.tilt_ledger`).
The dispersion symbol and the locked sum on `ℂ` (21:C15, C1). The series: the exponential reading composes and the
isotropic Schwarzschild factor is `e^{−2 artanh(U/2)}` (21:C11); the post-Newtonian Taylor brackets (21:C8, P6); the
preferred-frame scale `1/√Ω` at `1.3 × 10¹²³` (21:P2, C10); cardinality dilution (21:X8, C5). Classical (tier 2) on
Mathlib's hierarchy; every bracket from `π` to six places, `e` to nine and the Taylor tail of `exp`. The finite
content is proved with no axioms in the core (`FrcCore/Theme/Drift.lean`, `Theme/Lattice.lean`); the exact Mathlib
variants are `Theme/Gravity.lean`'s.
-/

namespace FRC.Strong

open Real

/-! ## Cardinality dilution (21:X8, C5) -/
section register

/-- 21:X8, 21:C5 — the weakness of gravity as cardinality dilution: with the Planck mass the
locality horizon, `m_P = √Ω`, the dimensionless coupling of two masses `m` is `(m/m_P)² = m²/Ω`, small because
`Ω` is large. C5's frame covariance is not formal content. -/
theorem dilution (m Ω : ℝ) (hΩ : 0 < Ω) : (m / √Ω) ^ 2 = m ^ 2 / Ω := by
  rw [div_pow, sq_sqrt hΩ.le]

end register

/-! ## The strong field (21:C4, C12, C13, P1, P7) -/
section strongfield

/-- 21:C12, 21:P7 — the operational cut and the slip core in the substrate coordinate (`G = 1`, `M` in Planck
masses, `L = ln Ω`): `r_f = 2M/L` carries `e^{2M/r_f} = Ω` (the round-trip delay's factor); `r_* = √M < r_f`
exactly when `M > (L/2)²`, and `r_f < M` exactly when `L > 2` (master E10). -/
theorem operational_cut (M L Ω : ℝ) (hM : 0 < M) (hL : 0 < L) (hΩ : L = log Ω) (hΩ0 : 0 < Ω) :
    exp (2 * M / (2 * M / L)) = Ω ∧
    (√M < 2 * M / L ↔ (L / 2) ^ 2 < M) ∧ (2 * M / L < M ↔ 2 < L) := by
  refine ⟨?_, ?_, ?_⟩
  · have : 2 * M / (2 * M / L) = L := by field_simp
    rw [this, hΩ, exp_log hΩ0]
  · rw [Real.sqrt_lt' (by positivity), div_pow, lt_div_iff₀ (by positivity)]
    constructor <;> intro h <;> nlinarith
  · rw [div_lt_iff₀ hL]
    constructor <;> intro h <;> nlinarith

/-- 21:P1 — the photon sphere (`prop:shadow`, `rem:exponential`): the impact parameter `b(r) = r e^{2Gm/r}` of the exponential metric
satisfies `b(r) ≥ 2e·Gm` for every `r > 0`, with equality exactly at `r = 2Gm` (from `x + 1 ≤ eˣ`, strict off
`x = 0`): the photon sphere is at `r_ph = 2Gm`, the critical impact parameter `b_c = 2e·Gm`. -/
theorem photon_sphere (Gm r : ℝ) (hG : 0 < Gm) (hr : 0 < r) :
    2 * exp 1 * Gm ≤ r * exp (2 * Gm / r) ∧ (r * exp (2 * Gm / r) = 2 * exp 1 * Gm ↔ r = 2 * Gm) := by
  have hsplit : exp (2 * Gm / r) = exp 1 * exp (2 * Gm / r - 1) := by
    rw [← exp_add]; ring_nf
  have hx := Real.add_one_le_exp (2 * Gm / r - 1)
  have hkey : 2 * exp 1 * Gm = r * exp 1 * (2 * Gm / r - 1 + 1) := by field_simp; ring
  have hpos : 0 < r * exp 1 := by positivity
  constructor
  · rw [hsplit, hkey]
    calc r * exp 1 * (2 * Gm / r - 1 + 1) ≤ r * exp 1 * exp (2 * Gm / r - 1) :=
          mul_le_mul_of_nonneg_left hx hpos.le
      _ = r * (exp 1 * exp (2 * Gm / r - 1)) := by ring
  · constructor
    · intro h
      by_contra hne
      have hx' : 2 * Gm / r - 1 ≠ 0 := by
        intro h0
        apply hne
        have : 2 * Gm / r = 1 := by linarith
        rw [div_eq_one_iff_eq hr.ne'] at this
        linarith
      have hlt := Real.add_one_lt_exp hx'
      have : r * exp 1 * (2 * Gm / r - 1 + 1) < r * exp 1 * exp (2 * Gm / r - 1) :=
        mul_lt_mul_of_pos_left hlt hpos
      rw [hsplit, ← mul_assoc] at h
      linarith
    · rintro rfl
      have : 2 * Gm / (2 * Gm) = 1 := by field_simp
      rw [this]; ring

/-- `√3` to seven places. -/
theorem sqrt_three_bounds : (1.7320508 : ℝ) < √3 ∧ √3 < 1.7320509 :=
  ⟨(Real.lt_sqrt (by norm_num)).mpr (by norm_num), (Real.sqrt_lt' (by norm_num)).mpr (by norm_num)⟩

/-- 21:P1 — the shadow and the ringdown against general relativity, bracketed from `e` (nine places) and `√3`:
the critical impact parameters `b_c = 2e·Gm` (this work) and `3√3·Gm` (Schwarzschild) have ratio
`2e/(3√3)` between `1.0462` and `1.0463` (the shadow `+4.6 %`), and the eikonal ringdown frequency, `∝ 1/b_c`,
ratio `3√3/(2e)` between `0.9557` and `0.9558` (`−4.4 %`); the Sgr A* excess `(4e − 6√3) θ_g` at the
GRAVITY `θ_g = 5.12 µas` [data, A8] lies between `2.46` and `2.47 µas` (the `2.5 µas` of the text). -/
theorem shadow_bracket :
    (1.0462 : ℝ) < 2 * exp 1 / (3 * √3) ∧ 2 * exp 1 / (3 * √3) < 1.0463 ∧
    (0.9557 : ℝ) < 3 * √3 / (2 * exp 1) ∧ 3 * √3 / (2 * exp 1) < 0.9558 ∧
    (2.46 : ℝ) < (4 * exp 1 - 6 * √3) * 5.12 ∧ (4 * exp 1 - 6 * √3) * 5.12 < 2.47 := by
  have e1 := Real.exp_one_gt_d9
  have e2 := Real.exp_one_lt_d9
  obtain ⟨s1, s2⟩ := sqrt_three_bounds
  have hs : (0 : ℝ) < √3 := by positivity
  have he : (0 : ℝ) < exp 1 := exp_pos 1
  refine ⟨?_, ?_, ?_, ?_, by nlinarith, by nlinarith⟩
  · rw [lt_div_iff₀ (by positivity)]; nlinarith
  · rw [div_lt_iff₀ (by positivity)]; nlinarith
  · rw [lt_div_iff₀ (by positivity)]; nlinarith
  · rw [div_lt_iff₀ (by positivity)]; nlinarith

/-- 21:P1 — the innermost stable circular orbit of the exponential metric (`G = m = 1`, isotropic radius),
with the circular-orbit relations of the paper's `prop:isco` taken as given and not formalised
(`L² = e^{2/r} r²/(r − 2)` and `E² = e^{−2/r}(r − 1)/(r − 2)` for a circular orbit at `r > 2`): what is
proved is that `log L²` has derivative `(r² − 6r + 4)/(r²(r − 2))`, that `r_ISCO = 3 + √5` is the root of
`r² − 6r + 4` above `2`, and that `(r − 1)/(r − 2) = r/4` there, so `E² = e^{−2/r} r/4` at the orbit. -/
theorem isco (r : ℝ) (hr : 2 < r) :
    HasDerivAt (fun r : ℝ => 2 / r + 2 * log r - log (r - 2))
      ((r ^ 2 - 6 * r + 4) / (r ^ 2 * (r - 2))) r ∧
    (3 + √5) ^ 2 - 6 * (3 + √5) + 4 = 0 ∧ 2 < 3 + √5 ∧
    (3 + √5 - 1) / (3 + √5 - 2) = (3 + √5) / 4 := by
  have h5 := Real.sq_sqrt (show (0 : ℝ) ≤ 5 by norm_num)
  have hs5 : (0 : ℝ) < √5 := by positivity
  refine ⟨?_, by linear_combination h5, by linarith, ?_⟩
  · have hr0 : r ≠ 0 := by linarith
    have hr2 : r - 2 ≠ 0 := by linarith
    have d1 : HasDerivAt (fun r : ℝ => 2 / r) (-(2 / r ^ 2)) r := by
      have := (hasDerivAt_inv hr0).const_mul 2
      convert this using 1 <;> [funext x; skip] <;> ring
    have d2 : HasDerivAt (fun r : ℝ => 2 * log r) (2 * r⁻¹) r :=
      (Real.hasDerivAt_log hr0).const_mul 2
    have d3 : HasDerivAt (fun r : ℝ => log (r - 2)) (1 / (r - 2)) r :=
      ((hasDerivAt_id' r).sub_const 2).log hr2
    convert (d1.add d2).sub d3 using 1
    field_simp
    ring
  · rw [div_eq_div_iff (by linarith) (by norm_num)]
    linear_combination -h5

/-- A bracket of `e^{−x}` from `x₁ < x < x₂`, a lower bound of `e^{x₁}` and an upper bound of `e^{x₂}`. -/
theorem exp_neg_bracket {x x₁ x₂ lo hi : ℝ} (hx₁ : x₁ < x) (hx₂ : x < x₂) (hlo : 0 < lo)
    (h1 : lo < exp x₁) (h2 : exp x₂ < hi) : hi⁻¹ < exp (-x) ∧ exp (-x) < lo⁻¹ := by
  constructor
  · calc hi⁻¹ < (exp x₂)⁻¹ := inv_strictAnti₀ (exp_pos _) h2
      _ = exp (-x₂) := (exp_neg _).symm
      _ < exp (-x) := exp_lt_exp.mpr (by linarith)
  · calc exp (-x) < exp (-x₁) := exp_lt_exp.mpr (by linarith)
      _ = (exp x₁)⁻¹ := exp_neg _
      _ < lo⁻¹ := inv_strictAnti₀ hlo h1

/-- The Taylor brackets of `e^t` at the two ends of `t = 2/r_ISCO = (3 − √5)/2`. -/
theorem exp_isco_tail_bounds :
    (1.465161 : ℝ) < exp 0.381966 ∧ exp (0.3819661 : ℝ) < 1.465163 := by
  constructor
  · have h := abs_le.1 (Real.exp_bound (x := 0.381966) (by rw [abs_of_pos (by norm_num)]; norm_num)
      (n := 7) (by norm_num))
    rw [abs_of_pos (by norm_num : (0 : ℝ) < 0.381966)] at h
    have h1 := h.1
    norm_num [Finset.sum_range_succ, Nat.factorial] at h1 ⊢
    linarith
  · have h := Real.exp_bound' (x := 0.3819661) (by norm_num) (by norm_num) (n := 7) (by norm_num)
    norm_num [Finset.sum_range_succ, Nat.factorial] at h ⊢
    linarith

/-- `√5` to seven places. -/
theorem sqrt_five_bounds : (2.2360679 : ℝ) < √5 ∧ √5 < 2.2360680 :=
  ⟨(Real.lt_sqrt (by norm_num)).mpr (by norm_num), (Real.sqrt_lt' (by norm_num)).mpr (by norm_num)⟩

/-- 21:P1 — the accretion efficiency bracketed: at `r_ISCO = 3 + √5` the orbital energy `E = √(e^{−2/r} r/4)`
lies between `0.9452` and `0.9453`, so `1 − E` is between `5.47 %` and `5.48 %` (the text's `5.48 %`),
against Schwarzschild's `1 − √(8/9)` between `5.71 %` and `5.72 %`. -/
theorem isco_efficiency :
    (0.0547 : ℝ) < 1 - √(exp (-(2 / (3 + √5))) * (3 + √5) / 4) ∧
    1 - √(exp (-(2 / (3 + √5))) * (3 + √5) / 4) < 0.0548 ∧
    (0.0571 : ℝ) < 1 - √(8 / 9) ∧ 1 - √(8 / 9) < (0.0572 : ℝ) := by
  obtain ⟨s1, s2⟩ := sqrt_five_bounds
  obtain ⟨t1, t2⟩ := exp_isco_tail_bounds
  have hx : 2 / (3 + √5) = (3 - √5) / 2 := by
    have h5 := Real.sq_sqrt (show (0 : ℝ) ≤ 5 by norm_num)
    rw [div_eq_div_iff (by positivity) (by norm_num)]
    linear_combination h5
  obtain ⟨hlo, hhi⟩ := exp_neg_bracket (x := 2 / (3 + √5)) (x₁ := 0.381966) (x₂ := 0.3819661)
    (by rw [hx]; linarith) (by rw [hx]; linarith) (by norm_num) t1 t2
  norm_num at hlo hhi
  have hE := exp_pos (-(2 / (3 + √5)))
  have hv1 : (0.89341 : ℝ) < exp (-(2 / (3 + √5))) * (3 + √5) / 4 := by nlinarith
  have hv2 : exp (-(2 / (3 + √5))) * (3 + √5) / 4 < (0.89345 : ℝ) := by nlinarith
  have hq1 : (0.9452 : ℝ) < √(exp (-(2 / (3 + √5))) * (3 + √5) / 4) :=
    (Real.lt_sqrt (by norm_num)).mpr (by nlinarith)
  have hq2 : √(exp (-(2 / (3 + √5))) * (3 + √5) / 4) < (0.9453 : ℝ) :=
    (Real.sqrt_lt' (by norm_num)).mpr (by nlinarith)
  have hs1 : (0.9428 : ℝ) < √(8 / 9) := (Real.lt_sqrt (by norm_num)).mpr (by norm_num)
  have hs2 : √(8 / 9 : ℝ) < 0.9429 := (Real.sqrt_lt' (by norm_num)).mpr (by norm_num)
  refine ⟨by linarith, by linarith, by linarith, by linarith⟩

/-- The arithmetic behind 21:C13's capacity ratio: for `r_f = r_s/L` the square of `r_f/r_s` is `1/L²`, and at
`L = ln Ω = 283.5` (the scale import) the ratio lies between `1.24 × 10⁻⁵` and `1.25 × 10⁻⁵` (the text's `1.24 × 10⁻⁵`); that the
externally resolvable capacity scales as `(r_f/r_s)²` is the paper's count, not formal content. -/
theorem capacity_ratio (rs L : ℝ) (hrs : rs ≠ 0) (hL : L ≠ 0) : (rs / L / rs) ^ 2 = 1 / L ^ 2 := by
  field_simp

theorem capacity_ratio_numeral : (1.24e-5 : ℝ) < 1 / 283.5 ^ 2 ∧ (1 / 283.5 ^ 2 : ℝ) < 1.25e-5 := by
  norm_num

/-- 21:C4 — the redshift as clock rate: the bias field `e^{−u}` with `u = Gm/rc²` gives
`Δf/f = 1 − e^{−u} = u + O(u²)`, `|1 − e^{−u} − u| ≤ u²` on `0 ≤ u ≤ 1`. -/
theorem redshift_linear (u : ℝ) (h0 : 0 ≤ u) (h1 : u ≤ 1) : |1 - exp (-u) - u| ≤ u ^ 2 := by
  have h := Real.exp_bound (x := -u) (by rw [abs_neg, abs_of_nonneg h0]; exact h1) (n := 2) (by norm_num)
  norm_num [Finset.sum_range_succ, Nat.factorial, abs_neg, abs_of_nonneg h0] at h
  rw [abs_le] at h ⊢
  constructor <;> nlinarith [sq_nonneg u]

end strongfield

/-! ## The floor and the crossover (21:C19, P4, X2) -/
section floor

/-- 21:C19, 21:P4 — the registration root: for `0 < w < 1` the quadratic `wη² − 2η + w = 0` (rational in the
paper's `w`, here over `ℝ`) has
exactly the roots `(1 ∓ √(1 − w²))/w`; the smaller, `η = (1 − √(1 − w²))/w`, lies in `(0, 1)` and the larger
exceeds `1`, so the in-`(0, 1)` root that fixes the resolved fraction `f = 1 − η^a` is unique. -/
theorem registration_root (w : ℝ) (hw0 : 0 < w) (hw1 : w < 1) :
    w * ((1 - √(1 - w ^ 2)) / w) ^ 2 - 2 * ((1 - √(1 - w ^ 2)) / w) + w = 0 ∧
    0 < (1 - √(1 - w ^ 2)) / w ∧ (1 - √(1 - w ^ 2)) / w < 1 ∧
    1 < (1 + √(1 - w ^ 2)) / w ∧
    (∀ x : ℝ, w * x ^ 2 - 2 * x + w = 0 →
      x = (1 - √(1 - w ^ 2)) / w ∨ x = (1 + √(1 - w ^ 2)) / w) := by
  have hw2 : 0 ≤ 1 - w ^ 2 := by nlinarith
  set s := √(1 - w ^ 2) with hs
  have hs2 : s ^ 2 = 1 - w ^ 2 := Real.sq_sqrt hw2
  have hs0 : 0 ≤ s := Real.sqrt_nonneg _
  have hs1 : s < 1 := by
    rw [hs, Real.sqrt_lt' (by norm_num)]; nlinarith
  have hsw : 1 - w < s := by nlinarith [mul_pos hw0 (sub_pos.mpr hw1)]
  have hab : (1 - s) / w + (1 + s) / w = 2 / w := by rw [← add_div]; ring_nf
  have hsum : w * (2 / w) = 2 := by field_simp
  have hprod : w * ((1 - s) / w * ((1 + s) / w)) = w := by
    rw [div_mul_div_comm, ← mul_div_assoc, div_eq_iff (by positivity)]
    linear_combination (-w) * hs2
  have hquad : ∀ x : ℝ, w * x ^ 2 - 2 * x + w = w * (x - (1 - s) / w) * (x - (1 + s) / w) := by
    intro x
    have e : w * (x - (1 - s) / w) * (x - (1 + s) / w)
        = w * x ^ 2 - w * ((1 - s) / w + (1 + s) / w) * x + w * ((1 - s) / w * ((1 + s) / w)) := by ring
    rw [e, hab, hsum, hprod]
  refine ⟨?_, div_pos (by linarith) hw0, ?_, ?_, ?_⟩
  · rw [hquad]; ring
  · rw [div_lt_one hw0]; linarith
  · rw [lt_div_iff₀ hw0]; linarith
  · intro x hx
    rw [hquad] at hx
    rcases mul_eq_zero.mp hx with h | h
    · rcases mul_eq_zero.mp h with h | h
      · exact absurd h hw0.ne'
      · left; linarith
    · right; linarith

/-- 21:C19, 21:P4 — the crossover `g_obs = g_N/(1 − e^{−√x})`, `x = g_N/a₀`, squeezed: with `t = √x > 0`,
`1 ≤ t/(1 − e^{−t})`, and `t/(1 − e^{−t}) ≤ 1/(1 − 3t/4)` for `t ≤ 1`; and the Tully–Fisher algebra is
exact: `v² = g_obs r` with `g_obs = √(g_N a₀)`, `g_N = GM/r²`, gives `v⁴ = GMa₀`. -/
theorem crossover_limits (t : ℝ) (ht : 0 < t) :
    0 < 1 - exp (-t) ∧ 1 ≤ t / (1 - exp (-t)) ∧
    (t ≤ 1 → t / (1 - exp (-t)) ≤ 1 / (1 - 3 * t / 4)) ∧
    (∀ G M r a₀ v : ℝ, 0 < r → 0 ≤ G * M → 0 ≤ a₀ →
      v ^ 2 = √(G * M / r ^ 2 * a₀) * r → v ^ 4 = G * M * a₀) := by
  have hpos : 0 < 1 - exp (-t) := by
    have : exp (-t) < exp 0 := exp_lt_exp.mpr (by linarith)
    rw [exp_zero] at this
    linarith
  refine ⟨hpos, ?_, ?_, ?_⟩
  · rw [le_div_iff₀ hpos]
    have := Real.add_one_le_exp (-t)
    linarith
  · intro ht1
    have h := Real.exp_bound (x := -t) (by rw [abs_neg, abs_of_pos ht]; exact ht1) (n := 2) (by norm_num)
    norm_num [Finset.sum_range_succ, Nat.factorial, abs_neg, abs_of_pos ht] at h
    rw [abs_le] at h
    have h34 : 0 < 1 - 3 * t / 4 := by linarith
    rw [div_le_div_iff₀ hpos h34]
    nlinarith
  · intro G M r a₀ v hr hGM ha v2
    have hnn : 0 ≤ G * M / r ^ 2 * a₀ := by positivity
    calc v ^ 4 = (v ^ 2) ^ 2 := by ring
      _ = (√(G * M / r ^ 2 * a₀)) ^ 2 * r ^ 2 := by rw [v2]; ring
      _ = G * M / r ^ 2 * a₀ * r ^ 2 := by rw [Real.sq_sqrt hnn]
      _ = G * M * a₀ := by field_simp

/-- 21:C19, 21:P4, 21:X2 — the deep limit: `t/(1 − e^{−t}) → 1` as `t → 0⁺`, so `g_obs/√(g_N a₀) → 1` — the
deep regime `g_obs = √(g_N a₀)`, the floor read as noise with no dark sector. -/
theorem crossover_deep_limit :
    Filter.Tendsto (fun t : ℝ => t / (1 - exp (-t))) (nhdsWithin 0 (Set.Ioi 0)) (nhds 1) := by
  have hc : ContinuousAt (fun t : ℝ => 1 / (1 - 3 * t / 4)) 0 := by
    apply ContinuousAt.div continuousAt_const
    · fun_prop
    · norm_num
  have hup : Filter.Tendsto (fun t : ℝ => 1 / (1 - 3 * t / 4)) (nhdsWithin 0 (Set.Ioi 0)) (nhds 1) := by
    have := hc.tendsto.mono_left (nhdsWithin_le_nhds : nhdsWithin (0 : ℝ) (Set.Ioi 0) ≤ nhds 0)
    simpa using this
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds hup ?_ ?_
  · filter_upwards [self_mem_nhdsWithin] with t ht
    exact (crossover_limits t ht).2.1
  · filter_upwards [Ioo_mem_nhdsGT (show (0 : ℝ) < 1 by norm_num)] with t ht
    exact (crossover_limits t ht.1).2.2.1 ht.2.le

/-- 21:C19, 21:P4 — the Newtonian limit: `1 − e^{−t} → 1` as `t → ∞`, so `g_obs/g_N → 1` for `x → ∞`. -/
theorem crossover_newton_limit :
    Filter.Tendsto (fun t : ℝ => 1 - exp (-t)) Filter.atTop (nhds 1) := by
  have := Real.tendsto_exp_neg_atTop_nhds_zero
  simpa using tendsto_const_nhds.sub this

/-- The Taylor brackets of `e^t` at the two ends of `t = √5 − 2`. -/
theorem exp_root_five_tail_bounds :
    (1.2662602 : ℝ) < exp 0.2360679 ∧ exp (0.2360680 : ℝ) < 1.2662605 := by
  constructor
  · have h := abs_le.1 (Real.exp_bound (x := 0.2360679) (by rw [abs_of_pos (by norm_num)]; norm_num)
      (n := 7) (by norm_num))
    rw [abs_of_pos (by norm_num : (0 : ℝ) < 0.2360679)] at h
    have h1 := h.1
    norm_num [Finset.sum_range_succ, Nat.factorial] at h1 ⊢
    linarith
  · have h := Real.exp_bound' (x := 0.2360680) (by norm_num) (by norm_num) (n := 7) (by norm_num)
    norm_num [Finset.sum_range_succ, Nat.factorial] at h ⊢
    linarith

/-- 21:P4 — the discriminant against the simple interpolant at `g_N = 5a₀`: the crossover
`ν(5) = 1/(1 − e^{−√5})` lies between `1.11966` and `1.11967`, the simple interpolant
`ν_s(5) = 1/2 + √(1/4 + 1/5)` between `1.17082` and `1.17083`, so they part by between `0.0511` and `0.0512` in
`g_obs/g_N` (the text's `0.05`). -/
theorem interpolant_discriminant :
    (1.11966 : ℝ) < 1 / (1 - exp (-√5)) ∧ 1 / (1 - exp (-√5)) < 1.11967 ∧
    (1.17082 : ℝ) < 1 / 2 + √(1 / 4 + 1 / 5) ∧ 1 / 2 + √(1 / 4 + 1 / 5) < 1.17083 ∧
    (0.0511 : ℝ) < (1 / 2 + √(1 / 4 + 1 / 5)) - 1 / (1 - exp (-√5)) ∧
    (1 / 2 + √(1 / 4 + 1 / 5)) - 1 / (1 - exp (-√5)) < 0.0512 := by
  obtain ⟨s1, s2⟩ := sqrt_five_bounds
  obtain ⟨t1, t2⟩ := exp_root_five_tail_bounds
  have hm1 := Real.exp_neg_one_gt_d9
  have hm2 := Real.exp_neg_one_lt_d9
  have hsplit : exp (-√5) = exp (-1) * exp (-1) * exp (2 - √5) := by
    rw [← exp_add, ← exp_add]; ring_nf
  obtain ⟨hlo, hhi⟩ := exp_neg_bracket (x := √5 - 2) (x₁ := 0.2360679) (x₂ := 0.2360680)
    (by linarith) (by linarith) (by norm_num) t1 t2
  norm_num at hlo hhi
  have hm : (0 : ℝ) < exp (-1) := exp_pos _
  have hq1 : (0.106877 : ℝ) < exp (-√5) := by rw [hsplit]; nlinarith [mul_pos hm hm]
  have hq2 : exp (-√5) < (0.106878 : ℝ) := by rw [hsplit]; nlinarith [mul_pos hm hm]
  have hden : (0 : ℝ) < 1 - exp (-√5) := by linarith
  have hr1 : (1.11966 : ℝ) < 1 / (1 - exp (-√5)) := by rw [lt_div_iff₀ hden]; linarith
  have hr2 : 1 / (1 - exp (-√5)) < (1.11967 : ℝ) := by rw [div_lt_iff₀ hden]; linarith
  have hs1 : (0.67082 : ℝ) < √(1 / 4 + 1 / 5) := (Real.lt_sqrt (by norm_num)).mpr (by norm_num)
  have hs2 : √(1 / 4 + 1 / 5 : ℝ) < 0.67083 := (Real.sqrt_lt' (by norm_num)).mpr (by norm_num)
  refine ⟨hr1, hr2, by linarith, by linarith, by linarith, by linarith⟩

end floor

/-! ## The primordial fixed point (21:C18) -/
section primordial

/-- 21:C18 — the fixed point: for a power law `P(k) = k^n` the dimensionless `k³P(k)` is the
same at every scale `k > 0` exactly when `n = −3`, i.e. `n_s − 1 = n + 3 = 0`, the Harrison–Zel'dovich
`n_s = 1`, uniquely; that the drive's jitter spectrum is this fixed point is the paper's argument. -/
theorem scale_invariance_iff (n : ℝ) :
    (∀ k : ℝ, 0 < k → k ^ 3 * k ^ n = 1) ↔ n = -3 := by
  constructor
  · intro h
    have h2 := h 2 (by norm_num)
    have h3 : (2 : ℝ) ^ (n + 3) = 1 := by
      rw [rpow_add (by norm_num : (0 : ℝ) < 2), show (2 : ℝ) ^ (3 : ℝ) = 2 ^ (3 : ℕ) by
        exact_mod_cast rpow_natCast 2 3]
      linarith
    have hl := congrArg Real.log h3
    rw [Real.log_rpow (by norm_num), Real.log_one] at hl
    rcases mul_eq_zero.mp hl with h | h
    · linarith
    · exact absurd h (Real.log_pos (by norm_num)).ne'
  · rintro rfl k hk
    rw [Real.rpow_neg hk.le, show (3 : ℝ) = (3 : ℕ) by norm_num, rpow_natCast]
    exact mul_inv_cancel₀ (pow_ne_zero 3 hk.ne')

end primordial

/-! ## The dispersion symbol and the locked sum (21:C1, C15) -/
section lattice

/-- 21:C15 — the dispersion symbol: the central second difference acts on the plane wave
`e^{ikx}` by `−(2 − 2 cos k) = −4 sin²(k/2)`; the wave equation, its two polarisations and the speed `c` are
the package's. -/
theorem dispersion_symbol (k : ℝ) : 2 - 2 * cos k = 4 * sin (k / 2) ^ 2 := by
  have h := Real.cos_two_mul (k / 2)
  rw [show 2 * (k / 2) = k by ring] at h
  rw [h, Real.cos_sq']; ring

/-- 21:C1 — the coherent coefficient: a locked cluster of `m` cells with one phase sums with
coefficient exactly `m`, `‖Σ_{j<m} z‖ = m ‖z‖`; the incoherent `O(√m)` and the gradient flow are not formal
content. -/
theorem locked_sum (m : ℕ) (z : ℂ) : ‖∑ _j : Fin m, z‖ = m * ‖z‖ := by
  simp [Finset.sum_const, Finset.card_univ, Fintype.card_fin]

end lattice

/-! ## The series (21:C8, C10, C11, P2, P6) -/
section series

/-- 21:C11 — the exponential reading is the multiplicative one, `e^{−(a+b)} = e^{−a} e^{−b}`; the isotropic
Schwarzschild factor `R(U) = (1 − U/2)/(1 + U/2)` is `e^{−2 artanh(U/2)}`, the exponential reading of the
self-sourced `ψ = 2 artanh(U/2)`, and it violates the composition law: `R(1) = 1/3 ≠ 9/25 = R(1/2)²`. -/
theorem exponential_reading (a b : ℝ) :
    exp (-(a + b)) = exp (-a) * exp (-b) ∧
    (∀ U : ℝ, -2 < U → U < 2 → exp (-(2 * artanh (U / 2))) = (1 - U / 2) / (1 + U / 2)) ∧
    (1 - (1 : ℝ) / 2) / (1 + 1 / 2) ≠ ((1 - (1 / 2 : ℝ) / 2) / (1 + (1 / 2) / 2)) ^ 2 := by
  refine ⟨by rw [← exp_add]; ring_nf, ?_, by norm_num⟩
  intro U h1 h2
  have hx : U / 2 ∈ Set.Icc (-1 : ℝ) 1 := ⟨by linarith, by linarith⟩
  rw [Real.artanh_eq_half_log hx]
  have hpos : 0 < (1 + U / 2) / (1 - U / 2) := by apply div_pos <;> linarith
  rw [show -(2 * (1 / 2 * log ((1 + U / 2) / (1 - U / 2)))) = -log ((1 + U / 2) / (1 - U / 2)) by ring,
    exp_neg, exp_log hpos, inv_div]

/-- 21:C8, 21:P6 — the post-Newtonian inputs as Taylor brackets on `|U| ≤ 1/2`: the exponential metric's
`A = e^{−2U}`, `B = e^{2U}` against the isotropic Schwarzschild `A_S = ((1 − U/2)/(1 + U/2))²`,
`B_S = (1 + U/2)⁴` satisfy `|A − A_S − U³/6| ≤ 3U⁴` and `|B − B_S − U²/2| ≤ 3|U|³`: the single-potential
inputs consumed by C23 coincide through first post-Newtonian order (`A` to `O(U²)`, `B` to `O(U)`) and part at
2PN with `δA = U³/6`, `δB = U²/2`; the two-body superposition of C23 is the package's. -/
theorem pn_series (U : ℝ) (hU : |U| ≤ 1 / 2) :
    |exp (-(2 * U)) - ((1 - U / 2) / (1 + U / 2)) ^ 2 - U ^ 3 / 6| ≤ 3 * U ^ 4 ∧
    |exp (2 * U) - (1 + U / 2) ^ 4 - U ^ 2 / 2| ≤ 3 * |U| ^ 3 := by
  have hU' := abs_le.1 hU
  have hden : 1 + U / 2 ≠ 0 := by intro h; linarith [hU'.1]
  have hden2 : (9 / 16 : ℝ) ≤ (1 + U / 2) ^ 2 := by nlinarith [hU'.1]
  have hU4 : 0 ≤ U ^ 4 := by positivity
  have habs4 : |U| ^ 4 = U ^ 4 := by rw [← abs_pow, abs_of_nonneg hU4]
  have habs3 : |U| ^ 3 * |U| = U ^ 4 := by
    rw [← pow_succ, ← abs_pow, abs_of_nonneg (by positivity)]
  have hU3 : 0 ≤ |U| ^ 3 := by positivity
  constructor
  · have h := Real.exp_bound (x := -(2 * U)) (by rw [abs_neg, abs_mul, abs_two]; linarith) (n := 4)
      (by norm_num)
    rw [abs_neg, abs_mul, abs_two] at h
    norm_num [Finset.sum_range_succ, Nat.factorial] at h
    rw [abs_le] at h
    have hpow : (2 * |U|) ^ 4 = 16 * U ^ 4 := by rw [mul_pow, habs4]; norm_num
    rw [hpow] at h
    have hA : ((1 - U / 2) / (1 + U / 2)) ^ 2 - (1 - 2 * U + 2 * U ^ 2 - 3 / 2 * U ^ 3)
        = U ^ 4 * (1 + 3 * U / 8) / (1 + U / 2) ^ 2 := by
      rw [div_pow, eq_div_iff (pow_ne_zero 2 hden), sub_mul, div_mul_cancel₀ _ (pow_ne_zero 2 hden)]
      ring
    have hrem : |U ^ 4 * (1 + 3 * U / 8) / (1 + U / 2) ^ 2| ≤ 2.12 * U ^ 4 := by
      rw [abs_div, abs_mul, abs_of_nonneg hU4, abs_of_pos (by positivity : (0 : ℝ) < (1 + U / 2) ^ 2),
        div_le_iff₀ (by positivity)]
      have : |1 + 3 * U / 8| ≤ 1.1875 := by rw [abs_le]; constructor <;> linarith [hU'.1, hU'.2]
      nlinarith [abs_nonneg (1 + 3 * U / 8)]
    rw [abs_le] at hrem
    have hA' : ((1 - U / 2) / (1 + U / 2)) ^ 2
        = 1 - 2 * U + 2 * U ^ 2 - 3 / 2 * U ^ 3 + U ^ 4 * (1 + 3 * U / 8) / (1 + U / 2) ^ 2 := by
      linarith [hA]
    rw [hA', abs_le]
    constructor <;> nlinarith [hrem.1, hrem.2, h.1, h.2]
  · have h := Real.exp_bound (x := 2 * U) (by rw [abs_mul, abs_two]; linarith) (n := 3) (by norm_num)
    rw [abs_mul, abs_two] at h
    norm_num [Finset.sum_range_succ, Nat.factorial] at h
    rw [abs_le] at h ⊢
    have hpow : (2 * |U|) ^ 3 = 8 * |U| ^ 3 := by rw [mul_pow]; norm_num
    rw [hpow] at h
    have hU4' : U ^ 4 ≤ |U| ^ 3 / 2 := by rw [← habs3]; nlinarith
    have hcube : U ^ 3 ≤ |U| ^ 3 ∧ -(|U| ^ 3) ≤ U ^ 3 := by
      constructor
      · calc U ^ 3 ≤ |U ^ 3| := le_abs_self _
          _ = |U| ^ 3 := abs_pow U 3
      · calc -(|U| ^ 3) = -|U ^ 3| := by rw [abs_pow]
          _ ≤ U ^ 3 := neg_abs_le _
    constructor <;> nlinarith [h.1, h.2, hcube.1, hcube.2]

/-- 21:P2, 21:C10 — the numeral behind the preferred-frame scale: the drive's signature is `O(1/√Ω)` (the paper's
`α₁, α₂`), and at the scale import's `Ω = 1.3 × 10¹²³` (00:A7) this lies between `2.7` and `2.8 × 10⁻⁶²` (the row's
`3 × 10⁻⁶²`). -/
theorem preferred_frame_scale : (2.7e-62 : ℝ) < 1 / √(1.3e123) ∧ 1 / √(1.3e123) < 2.8e-62 := by
  have hs : 0 < √(1.3e123 : ℝ) := Real.sqrt_pos.2 (by norm_num)
  constructor
  · rw [lt_one_div (by norm_num) hs, Real.sqrt_lt' (by norm_num)]; norm_num
  · rw [one_div_lt hs (by norm_num), Real.lt_sqrt (by norm_num)]; norm_num

end series

end FRC.Strong
