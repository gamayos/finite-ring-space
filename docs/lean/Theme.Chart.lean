import Mathlib

/-!
# FrcLedger.Theme.Chart — the chart theme: the readings against the continuum (ledger migration, task LM30)

The chart theme holds the readings of the finite results against the continuum, the only theme with the reals
(`frc/themes.py`, rank 30). It serves the chart clauses of the master's cosmology and prediction rows: the
floor `a₀ = cH₀/2π` (00:L1), the octant record depth and its outputs (00:L3), the primordial tilt (00:L8) and the
running floor (00:P1). The chart's numerals — the speed of light, the megaparsec, the Julian year, the fitted
values and their errors — are declared data. The octant's theorems moved here from 14-entropy and the floor's
from 21-gravity (6 October 2026); those modules keep the old names as aliases.

Classical (tier 2) on Mathlib's hierarchy. Every bracket is certified from `π` to six places (`Real.pi_gt_d6`,
`Real.pi_lt_d6`), `e` to nine (`Real.exp_one_gt_d9`, `Real.exp_one_lt_d9`) and the Taylor tail of `exp`
(`Real.exp_bound`, `Real.exp_bound'`). The realisation content behind each reading — that the octant is the
record depth, that the floor is the synchronisation threshold, that `ln Ω` is the tilt's e-fold count — is the
rows' realisation clause, not formal content.
-/

namespace FRC.Chart

open Real

/-! ## The octant record depth and its outputs (00:L3; 14:C5, C7, P3) -/
section octant

/-- 00:L3, 14:C5 [chart] — the chart conversion of the octant: the count `S/2` out of the `4S`-cycle, read on
the meridian circle `2π r_H/c`, is the depth `(π/4) r_H/c`. -/
theorem octant_chart (S r c : ℝ) (hS : S ≠ 0) :
    (S / 2) / (4 * S) * (2 * π * r / c) = (π / 4) * r / c := by
  rcases eq_or_ne c 0 with rfl | hc
  · simp
  · field_simp

/-- The octant's rate factor `tanh(3π/8)` is positive. -/
theorem tanh_octant_pos : 0 < tanh (3 * π / 8) := by
  rw [Real.tanh_eq_sinh_div_cosh]
  exact div_pos (Real.sinh_pos_iff.2 (by positivity)) (Real.cosh_pos _)

/-- 00:L3, 14:P3 [ΛCDM] — the algebraic locus: with `t H_Λ = π/4` (the octant), `H_Λ = H₀ √Ω_Λ` and
`Ω_Λ = tanh²(3π/8)`, `t H₀ = (π/4)/tanh(3π/8)`; the numeral `0.950` is bracketed in `locus_bracket`. -/
theorem age_rate_locus (t H0 HΛ Ω : ℝ) (hoct : t * HΛ = π / 4) (hΛ : HΛ = H0 * √Ω)
    (hΩ : Ω = tanh (3 * π / 8) ^ 2) : t * H0 = (π / 4) / tanh (3 * π / 8) := by
  have hpos := tanh_octant_pos
  rw [hΩ, Real.sqrt_sq hpos.le] at hΛ
  rw [eq_div_iff hpos.ne', ← hoct, hΛ]; ring

/-- `tanh x = (e^{2x} − 1)/(e^{2x} + 1)`. -/
theorem tanh_eq_exp_two_mul (x : ℝ) : tanh x = (exp (2 * x) - 1) / (exp (2 * x) + 1) := by
  rw [Real.tanh_eq, Real.exp_neg, two_mul, Real.exp_add]
  have h := Real.exp_pos x
  field_simp

/-- The Taylor brackets of `e^t` at the two ends of `t = 3π/4 − 2`: seven terms of the series with the tail
bound of Mathlib's `Real.exp_bound`. -/
theorem exp_tail_bounds :
    (1.427884 : ℝ) < exp 0.356194 ∧ exp (0.35619475 : ℝ) < 1.4278857 := by
  constructor
  · have h := abs_le.1 (Real.exp_bound (x := 0.356194) (by rw [abs_of_pos (by norm_num)]; norm_num)
      (n := 7) (by norm_num))
    rw [abs_of_pos (by norm_num : (0 : ℝ) < 0.356194)] at h
    have h1 := h.1
    norm_num [Finset.sum_range_succ, Nat.factorial] at h1 ⊢
    linarith
  · have h := Real.exp_bound' (x := 0.35619475) (by norm_num) (by norm_num) (n := 7) (by norm_num)
    norm_num [Finset.sum_range_succ, Nat.factorial] at h ⊢
    linarith

/-- `e^{3π/4}` bracketed: `10.55071 < e^{3π/4} < 10.55073`, from `π` to six places, `e` to nine, and the
Taylor tail. -/
theorem exp_three_pi_four_bounds : (10.55071 : ℝ) < exp (3 * π / 4) ∧ exp (3 * π / 4) < 10.55073 := by
  have hpi1 := Real.pi_gt_d6
  have hpi2 := Real.pi_lt_d6
  have he1 := Real.exp_one_gt_d9
  have he2 := Real.exp_one_lt_d9
  have ht := exp_tail_bounds
  have hsplit : exp (3 * π / 4) = exp 1 * exp 1 * exp (3 * π / 4 - 2) := by
    rw [← Real.exp_add, ← Real.exp_add]; congr 1; ring
  have hlo : exp 0.356194 < exp (3 * π / 4 - 2) := Real.exp_lt_exp.2 (by linarith)
  have hhi : exp (3 * π / 4 - 2) < exp 0.35619475 := Real.exp_lt_exp.2 (by linarith)
  have hpos : (0 : ℝ) < exp 1 := Real.exp_pos 1
  rw [hsplit]
  constructor
  · nlinarith [mul_pos hpos hpos, Real.exp_pos (3 * π / 4 - 2)]
  · nlinarith [mul_pos hpos hpos, Real.exp_pos (3 * π / 4 - 2)]

/-- `tanh(3π/8)` bracketed: `0.82685 < tanh(3π/8) < 0.826851`, from `exp_three_pi_four_bounds`. -/
theorem tanh_octant_bounds : (0.82685 : ℝ) < tanh (3 * π / 8) ∧ tanh (3 * π / 8) < 0.826851 := by
  obtain ⟨hE1, hE2⟩ := exp_three_pi_four_bounds
  have htanh : tanh (3 * π / 8) = (exp (3 * π / 4) - 1) / (exp (3 * π / 4) + 1) := by
    rw [tanh_eq_exp_two_mul]; congr 2 <;> ring_nf
  have hden : (0 : ℝ) < exp (3 * π / 4) + 1 := by linarith
  constructor
  · rw [htanh, lt_div_iff₀ hden]; linarith
  · rw [htanh, div_lt_iff₀ hden]; linarith

/-- 00:L3, 14:P3 — the locus's numeral bracketed: `0.9498 < (π/4)/tanh(3π/8) < 0.9499`, the paper's `0.950`. -/
theorem locus_bracket : (0.9498 : ℝ) < (π / 4) / tanh (3 * π / 8) ∧ (π / 4) / tanh (3 * π / 8) < 0.9499 := by
  obtain ⟨hl, hu⟩ := tanh_octant_bounds
  have hpi1 := Real.pi_gt_d6
  have hpi2 := Real.pi_lt_d6
  have hpos : (0 : ℝ) < tanh (3 * π / 8) := by linarith
  constructor
  · rw [lt_div_iff₀ hpos]; nlinarith
  · rw [div_lt_iff₀ hpos]; nlinarith

/-- 00:L3, 14:C7, 14:X3 — the landing bracketed: `0.68368 < tanh²(3π/8) < 0.68369` (the numeral `0.684`) is
certified from `π` to six places, `e` to nine and the Taylor tail; and, with the Planck numerals
`0.685 ± 0.007` taken as data, the deviation lies between `0.18σ` and `0.19σ`. -/
theorem landing_bracket :
    (0.68368 : ℝ) < tanh (3 * π / 8) ^ 2 ∧ tanh (3 * π / 8) ^ 2 < 0.68369 ∧
    0.18 * 0.007 < 0.685 - tanh (3 * π / 8) ^ 2 ∧ 0.685 - tanh (3 * π / 8) ^ 2 < 0.19 * 0.007 := by
  obtain ⟨hl, hu⟩ := tanh_octant_bounds
  have hsq1 : (0.82685 : ℝ) ^ 2 < tanh (3 * π / 8) ^ 2 := by
    apply pow_lt_pow_left₀ hl (by norm_num) (by norm_num)
  have hsq2 : tanh (3 * π / 8) ^ 2 < (0.826851 : ℝ) ^ 2 := by
    apply pow_lt_pow_left₀ hu (by linarith) (by norm_num)
  norm_num at hsq1 hsq2
  refine ⟨by linarith, by linarith, by linarith, by linarith⟩

/-- 00:L3 [chart] — the entailed rate: read on the octant depth `t = 13.79` Gyr (the channel-1 anchor, a Julian
year of `365.25` days; data), the locus `t H₀ = (π/4)/tanh(3π/8)` gives `67.34 < H₀ < 67.36` km s⁻¹ Mpc⁻¹ (the
megaparsec `3.0856775814913673 × 10¹⁹` km; data): the row's `67.4`. With 14-entropy's error `±0.7` and the Cepheid
ladder's `73.0 ± 1.0` (data), errors combined, the ladder lies between `4.6σ` and `4.7σ` above it: the row's `4.6σ`
adverse. -/
theorem hubble_landing (t H0 : ℝ) (ht : t = 13.79e9 * (365.25 * 86400))
    (hloc : t * H0 = (π / 4) / tanh (3 * π / 8)) :
    (67.34 : ℝ) < H0 * 3.0856775814913673e19 ∧ H0 * 3.0856775814913673e19 < 67.36 ∧
    (4.6 : ℝ) < (73.0 - H0 * 3.0856775814913673e19) / √(0.7 ^ 2 + 1.0 ^ 2) ∧
    (73.0 - H0 * 3.0856775814913673e19) / √(0.7 ^ 2 + 1.0 ^ 2) < 4.7 := by
  obtain ⟨hl, hu⟩ := locus_bracket
  have htpos : (0 : ℝ) < t := by rw [ht]; norm_num
  have hH : H0 = (π / 4) / tanh (3 * π / 8) / t := by
    rw [eq_div_iff htpos.ne', mul_comm, hloc]
  have h1 : (67.34 : ℝ) < H0 * 3.0856775814913673e19 := by
    rw [hH, ht, div_mul_eq_mul_div, lt_div_iff₀ (by norm_num)]; nlinarith
  have h2 : H0 * 3.0856775814913673e19 < (67.36 : ℝ) := by
    rw [hH, ht, div_mul_eq_mul_div, div_lt_iff₀ (by norm_num)]; nlinarith
  have hs1 : (1.2206 : ℝ) < √(0.7 ^ 2 + 1.0 ^ 2) := by
    rw [Real.lt_sqrt (by norm_num)]; norm_num
  have hs2 : √(0.7 ^ 2 + 1.0 ^ 2 : ℝ) < 1.2207 := by
    rw [Real.sqrt_lt' (by norm_num)]; norm_num
  have hspos : (0 : ℝ) < √(0.7 ^ 2 + 1.0 ^ 2) := by linarith
  refine ⟨h1, h2, ?_, ?_⟩
  · rw [lt_div_iff₀ hspos]; nlinarith
  · rw [div_lt_iff₀ hspos]; nlinarith

end octant

/-! ## The floor and its running (00:L1, P1; 21:P3) -/
section floor

/-- 00:L1, 21:P3 — the weak-acceleration floor `a₀ = cH₀/2π` at the entailed `H₀ = 67.4 km s⁻¹ Mpc⁻¹` (the
speed of light and the megaparsec declared numerals [data]): `a₀` lies between `1.04` and `1.05 × 10⁻¹⁰ m s⁻²`;
against the fitted `1.20 × 10⁻¹⁰` it is between `13.0 %` and `13.2 %` low, and the deficit is between `0.65` and
`0.67` of the systematic `0.24 × 10⁻¹⁰` (the text's `13 %`, `0.7σ`). -/
theorem floor_value (c H0 : ℝ) (hc : c = 299792458) (hH : H0 = 67.4e3 / 3.0856775814913673e22) :
    (1.04e-10 : ℝ) < c * H0 / (2 * π) ∧ c * H0 / (2 * π) < 1.05e-10 ∧
    (0.868 : ℝ) < c * H0 / (2 * π) / 1.2e-10 ∧ c * H0 / (2 * π) / 1.2e-10 < 0.870 ∧
    (0.65 : ℝ) < (1.2e-10 - c * H0 / (2 * π)) / 0.24e-10 ∧
    (1.2e-10 - c * H0 / (2 * π)) / 0.24e-10 < 0.67 := by
  have hpi1 := Real.pi_gt_d6
  have hpi2 := Real.pi_lt_d6
  subst hc hH
  have hA : (1.042e-10 : ℝ) < 299792458 * (67.4e3 / 3.0856775814913673e22) / (2 * π) := by
    rw [lt_div_iff₀ (by positivity)]; nlinarith
  have hB : 299792458 * (67.4e3 / 3.0856775814913673e22) / (2 * π) < (1.0423e-10 : ℝ) := by
    rw [div_lt_iff₀ (by positivity)]; nlinarith
  refine ⟨by linarith, by linarith, ?_, ?_, ?_, ?_⟩
  · rw [lt_div_iff₀ (by norm_num)]; linarith
  · rw [div_lt_iff₀ (by norm_num)]; linarith
  · rw [lt_div_iff₀ (by norm_num)]; linarith
  · rw [div_lt_iff₀ (by norm_num)]; linarith

/-- 00:P1 [chart] — the running floor: if the floor is read at every redshift on the registered rate,
`a₀(z) = cH(z)/2π`, and the deep-regime Tully–Fisher law `v⁴ = G M a₀` holds at fixed baryonic mass `M`, then
`a₀(z)/a₀(0) = H(z)/H(0) = E(z)` and the zero-point evolves as `v(z)/v(0) = E(z)^{1/4}`. That the floor tracks the
registered rate (the gravity realisation, 00:D5) is the row's realisation clause, not formal content. -/
theorem running_floor (c G M : ℝ) (H a v : ℝ → ℝ) (hc : 0 < c) (hG : 0 < G) (hM : 0 < M)
    (hH : ∀ z, 0 < H z) (ha : ∀ z, a z = c * H z / (2 * π)) (hv : ∀ z, 0 < v z)
    (htf : ∀ z, v z ^ 4 = G * M * a z) (z : ℝ) :
    a z / a 0 = H z / H 0 ∧ v z / v 0 = (H z / H 0) ^ (1 / 4 : ℝ) := by
  have hpi := Real.pi_pos
  have h0 := hH 0
  have hz := hH z
  have hratio : a z / a 0 = H z / H 0 := by
    rw [ha z, ha 0]; field_simp
  refine ⟨hratio, ?_⟩
  have ha0 : 0 < a 0 := by rw [ha 0]; positivity
  have hv0 := hv 0
  have hvz := hv z
  have h4 : (v z / v 0) ^ 4 = H z / H 0 := by
    rw [div_pow, htf z, htf 0, ← hratio]; field_simp
  rw [← h4, show (1 / 4 : ℝ) = ((4 : ℕ) : ℝ)⁻¹ by norm_num]
  exact (Real.pow_rpow_inv_natCast (div_pos hvz hv0).le (by norm_num)).symm

end floor

/-! ## The primordial tilt (00:L8) -/
section tilt

/-- 00:L8 [chart] — the tilt at the ledger's `ln Ω = 283.5` (00:A9; data): `n_s − 1 = −π²/ln Ω` has magnitude
between `0.03481` and `0.03482` (the row's `−0.0348`); against Planck 2018's `−0.0351 ± 0.0042` (data) the
deviation is between `+0.068σ` and `+0.069σ` (the row's `+0.07σ`); the count `½ ln Ω` gives `−π²/(ln Ω/2)`, off
by between `8.2σ` and `8.3σ` (the row's exclusion at `8.2σ`). That `ln Ω` is the e-fold count of the frame's scale
range is the row's realisation clause, not formal content. -/
theorem tilt_ledger :
    (0.03481 : ℝ) < π ^ 2 / 283.5 ∧ π ^ 2 / 283.5 < 0.03482 ∧
    (0.068 * 0.0042 : ℝ) < 0.0351 - π ^ 2 / 283.5 ∧ 0.0351 - π ^ 2 / 283.5 < 0.069 * 0.0042 ∧
    (8.2 * 0.0042 : ℝ) < π ^ 2 / (283.5 / 2) - 0.0351 ∧ π ^ 2 / (283.5 / 2) - 0.0351 < 8.3 * 0.0042 := by
  have hpi1 := Real.pi_gt_d6
  have hpi2 := Real.pi_lt_d6
  have hsq1 : (3.141592 : ℝ) ^ 2 < π ^ 2 := pow_lt_pow_left₀ hpi1 (by norm_num) (by norm_num)
  have hsq2 : π ^ 2 < (3.141593 : ℝ) ^ 2 := pow_lt_pow_left₀ hpi2 (by linarith) (by norm_num)
  norm_num at hsq1 hsq2
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [lt_div_iff₀ (by norm_num)]; linarith
  · rw [div_lt_iff₀ (by norm_num)]; linarith
  · have : π ^ 2 / 283.5 < (0.0351 - 0.068 * 0.0042 : ℝ) := by rw [div_lt_iff₀ (by norm_num)]; norm_num; linarith
    linarith
  · have : (0.0351 - 0.069 * 0.0042 : ℝ) < π ^ 2 / 283.5 := by rw [lt_div_iff₀ (by norm_num)]; norm_num; linarith
    linarith
  · have : (8.2 * 0.0042 + 0.0351 : ℝ) < π ^ 2 / (283.5 / 2) := by rw [lt_div_iff₀ (by norm_num)]; norm_num; linarith
    linarith
  · have : π ^ 2 / (283.5 / 2) < (8.3 * 0.0042 + 0.0351 : ℝ) := by rw [div_lt_iff₀ (by norm_num)]; norm_num; linarith
    linarith

end tilt

end FRC.Chart
