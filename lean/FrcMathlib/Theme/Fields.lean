import Mathlib
import FrcMathlib.Theme.Chart

/-!
# FrcMathlib.Theme.Fields — the chart theme's readings of the interactions (27-fields, 16 October 2026)

The clauses of 27-fields that read the continuum: the phase cycle `ℤ/M` inside `U(1)` as the `M`-th roots of unity
(`roots_inclusion`, 27:C1), the Wilson weight `1 − Re ζ ≥ 0` on the unit circle, zero at the identity alone
(`wilson_weight_nonneg`, 27:C1), the `2T` area-law coefficient `c₁ = (x⁴ + 4x³ − 4x − 1)/(x⁴ + 8x³ + 6x² + 8x + 1)` in
`(0, 1)` for `x = e^{β/2} > 1` (`area_law_positive`, 27:C1, C7, X7), the Fermi constant `G_F = 1/(√2 v²)` from
`G_F/√2 = g²/(8 M_W²)` and `M_W² = g² v²/4` (`fermi_constant`, 27:C6); and, since 17 October 2026, the chart readings of the three exclusion rows: the one-loop running of the measured couplings to the meeting `α₁ = α₂` with the strong coupling's near-miss (`running_near_miss`, 27:P3), the proton lifetime `M_X⁴/(α² m_p⁵)` at the substrate and the GUT scales (`proton_lifetime`, 27:P4), the seesaw band and `m_b/m_τ` (`seesaw_band`, 27:P5). Classical (tier 2) on Mathlib's hierarchy. The finite content of the same rows is
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

/-- 27:P3 [chart] — the one-loop running of the measured couplings with the Standard-Model coefficients
`b = (41/10, −19/6, −7)`: at the meeting `α₁ = α₂` the strong coupling misses by less than a fifth, and the meeting
scale `M_Z e^{2πu}` lies in `[10¹², 10¹⁴]` GeV. The inputs are the measured `α⁻¹(M_Z) = 127.951`, `sin²θ_W = 0.23121`,
`α_s = 0.1179` and `M_Z = 91.1876` GeV (the paper's A6). -/
theorem running_near_miss (ainv s2 as b1 b2 b3 MZ : ℝ) (h1 : ainv = 127.951) (h2 : s2 = 0.23121)
    (h3 : as = 0.1179) (hb1 : b1 = 41 / 10) (hb2 : b2 = -19 / 6) (hb3 : b3 = -7) (hZ : MZ = 91.1876) :
    |1 / as - b3 * ((3 / 5 * (1 - s2) * ainv - s2 * ainv) / (b1 - b2)) - (s2 * ainv - b2 * ((3 / 5 * (1 - s2) * ainv - s2 * ainv) / (b1 - b2)))| / (s2 * ainv - b2 * ((3 / 5 * (1 - s2) * ainv - s2 * ainv) / (b1 - b2))) < 1 / 5 ∧
    (10 : ℝ) ^ 12 < MZ * exp (2 * π * ((3 / 5 * (1 - s2) * ainv - s2 * ainv) / (b1 - b2))) ∧
    MZ * exp (2 * π * ((3 / 5 * (1 - s2) * ainv - s2 * ainv) / (b1 - b2))) < (10 : ℝ) ^ 14 := by
  set u : ℝ := ((3 / 5 * (1 - s2) * ainv - s2 * ainv) / (b1 - b2)) with hudef
  have hu : u = (3 / 5 * (1 - 0.23121) * 127.951 - 0.23121 * 127.951) / (41 / 10 - -19 / 6) := by
    rw [hudef, h1, h2, hb1, hb2]
  have hu25 : 25 < 2 * π * u := by
    rw [hu]; nlinarith [pi_gt_d2]
  have hu26 : 2 * π * u < 26 := by
    rw [hu]; nlinarith [pi_lt_d2]
  have e25 : (2.7182818283 : ℝ) ^ 25 < exp (2 * π * u) := by
    calc (2.7182818283 : ℝ) ^ 25 < exp 1 ^ 25 := by
          exact pow_lt_pow_left₀ exp_one_gt_d9 (by norm_num) (by norm_num)
      _ = exp 25 := by rw [← exp_nat_mul]; norm_num
      _ < exp (2 * π * u) := exp_lt_exp.2 hu25
  have e26 : exp (2 * π * u) < (2.7182818286 : ℝ) ^ 26 := by
    calc exp (2 * π * u) < exp 26 := exp_lt_exp.2 hu26
      _ = exp 1 ^ 26 := by rw [← exp_nat_mul]; norm_num
      _ < (2.7182818286 : ℝ) ^ 26 := pow_lt_pow_left₀ exp_one_lt_d9 (exp_pos 1).le (by norm_num)
  refine ⟨?_, ?_, ?_⟩
  · rw [hu, h1, h2, h3, hb2, hb3]; norm_num [abs_lt]
  · rw [hZ]; nlinarith [e25]
  · rw [hZ]; nlinarith [e26]

/-- 27:P4 [chart] — the proton lifetime `τ_p = M_X⁴/(α² m_p⁵)` in years, with `m_p = 0.938` GeV, `α_GUT = 1/40`,
`ħ = 6.582 × 10⁻²⁵` GeV s and the year `3.156 × 10⁷` s: at the Planck scale `M_X = 1.22 × 10¹⁹` GeV it exceeds `10⁴⁵` yr,
at `M_X = 10¹⁶` GeV it exceeds the Super-Kamiokande bound `10³⁴` yr, and two lifetimes stand in the ratio `(M′/M)⁴`. -/
theorem proton_lifetime (mp a hbar yr : ℚ) (hm : mp = 0.938) (ha : a = 1 / 40) (hh : hbar = 6.582e-25)
    (hy : yr = 3.156e7) :
    (10 : ℚ) ^ 45 ≤ (1.22e19 : ℚ) ^ 4 / (a ^ 2 * mp ^ 5) * hbar / yr ∧
    (10 : ℚ) ^ 34 < (1e16 : ℚ) ^ 4 / (a ^ 2 * mp ^ 5) * hbar / yr ∧
    ∀ M M' : ℚ, 0 < M → 0 < M' →
      (M' ^ 4 / (a ^ 2 * mp ^ 5) * hbar / yr) / (M ^ 4 / (a ^ 2 * mp ^ 5) * hbar / yr) = (M' / M) ^ 4 := by
  subst hm ha hh hy
  refine ⟨by norm_num, by norm_num, fun M M' hM hM' => ?_⟩
  have hM0 : M ≠ 0 := hM.ne'
  field_simp

/-- 27:P5 [chart] — the seesaw `m_ν = y² v²/M_R` with `v = 174` GeV: for `y = 0.3` at `M_R = 10¹⁴` GeV and for `y = 1`
at `M_R = 10¹⁵` GeV the light mass lies in `(0.01, 0.1)` eV; and `m_b/m_τ = 4.18/1.777` lies in `(2, 3)`. -/
theorem seesaw_band (v mb mt : ℚ) (hv : v = 174) (hb : mb = 4.18) (ht : mt = 1.777) :
    (0.01 : ℚ) < (0.3 : ℚ) ^ 2 * v ^ 2 / 1e14 * 1e9 ∧ (0.3 : ℚ) ^ 2 * v ^ 2 / 1e14 * 1e9 < 0.1 ∧
    (0.01 : ℚ) < (1 : ℚ) ^ 2 * v ^ 2 / 1e15 * 1e9 ∧ (1 : ℚ) ^ 2 * v ^ 2 / 1e15 * 1e9 < 0.1 ∧
    (2 : ℚ) < mb / mt ∧ mb / mt < 3 := by
  subst hv hb ht
  norm_num

end FRC.FieldsML
