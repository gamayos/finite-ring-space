import Mathlib

/-!
# FrcMathlib.Theme.Gauge — the chart theme's readings of the gauge sector (46-yangmills, 8 November 2026)

The chart clauses of 46-yangmills on Mathlib's reals, beside the core's window-fraction brackets (`FrcCore/Theme/YangMills.lean`,
no axioms): the two-loop run of the coupling as the exact implicit solution of the two-loop equation and the one-loop law
over `ℝ` (46:P2), the Herbst comparison of the declared coupling and the couplings at the chart's fixed points (46:C10), the
plaquette channel at the chart's cells with `Real.log` (46:C11), the operator family's values with `Real.sqrt` (46:C12) and the gap
of the transfer tally at the classical `π` (46:C21). The chart's
own numbers that no formula fixes — the eigenvalue reading `2.232` and the fixed-point roots `3.541`, `3.085`, `2.611` of the
grid operator — enter as hypotheses or literals, the chart's readings, as `35:C17`'s `2.2322` does in
`FrcMathlib/Theme/Hadrons.lean`; the theorems certify every number built on them. Every bracket is certified from `π` to
six places (`Real.pi_gt_d6`, `Real.pi_lt_d6`), `ln 2` to nine (`Real.log_two_gt_d9`, `Real.log_two_lt_d9`) and the series of
`log (1 − x)` with its tail (`Real.abs_log_sub_add_sum_range_le`); every numeric bracket is its own lemma (`logb_*`, `Fb_*`),
cited by the theorems. The names stay in `FRC.YangMillsML`, so the paper module `FrcMathlib/YangMills.lean` aliases them
beside the yangmills theme's. Classical (tier 2).
-/

namespace FRC.YangMillsML

open Finset Real

/-! ## The logarithm brackets -/

/-- The series bracket of `log (1 − x)` for `0 ≤ x < 1` after `n` terms, from Mathlib's tail bound:
with `S_n = Σ_{i<n} x^{i+1}/(i+1)`, `−S_n − x^{n+1}/(1−x) ≤ log (1 − x) ≤ −S_n + x^{n+1}/(1−x)`. -/
theorem log_series_bracket (x : ℝ) (h0 : 0 ≤ x) (h1 : x < 1) (n : ℕ) :
    -(∑ i ∈ range n, x ^ (i + 1) / (i + 1)) - x ^ (n + 1) / (1 - x) ≤ log (1 - x) ∧
    log (1 - x) ≤ -(∑ i ∈ range n, x ^ (i + 1) / (i + 1)) + x ^ (n + 1) / (1 - x) := by
  have hx : |x| < 1 := by rw [abs_of_nonneg h0]; exact h1
  have h := Real.abs_log_sub_add_sum_range_le hx n
  rw [abs_of_nonneg h0, abs_le] at h
  constructor <;> linarith [h.1, h.2]

/-- `log q = log (q 2^k) − k log 2`, the mantissa `q 2^k ∈ (0, 1]` bracketed by the series after `n` terms: for rational
ends `lo ≤ −S_n − x^{n+1}/(q 2^k)` and `−S_n + x^{n+1}/(q 2^k) ≤ hi` with `x = 1 − q 2^k` (decided by `norm_num`),
`lo − k log 2 ≤ log q ≤ hi − k log 2`. -/
theorem log_mantissa_bracket (q : ℝ) (k n : ℕ) (lo hi : ℝ) (hq : 0 < q) (hq1 : q * 2 ^ k ≤ 1)
    (hlo : lo ≤ -(∑ i ∈ range n, (1 - q * 2 ^ k) ^ (i + 1) / (i + 1)) - (1 - q * 2 ^ k) ^ (n + 1) / (q * 2 ^ k))
    (hhi : -(∑ i ∈ range n, (1 - q * 2 ^ k) ^ (i + 1) / (i + 1)) + (1 - q * 2 ^ k) ^ (n + 1) / (q * 2 ^ k) ≤ hi) :
    lo - k * log 2 ≤ log q ∧ log q ≤ hi - k * log 2 := by
  have hr : 0 < q * 2 ^ k := by positivity
  have hx0 : 0 ≤ 1 - q * 2 ^ k := by linarith
  have hx1 : 1 - q * 2 ^ k < 1 := by linarith
  have h := log_series_bracket (1 - q * 2 ^ k) hx0 hx1 n
  have e2 : (1 : ℝ) - (1 - q * 2 ^ k) = q * 2 ^ k := by ring
  rw [e2] at h
  have e : log q = log (q * 2 ^ k) - k * log 2 := by
    rw [log_mul hq.ne' (by positivity), log_pow]; ring
  rw [e]
  constructor <;> linarith [h.1, h.2]

/-! ## 46:P2 — the running coupling: the two-loop equation's exact solution and the one-loop law over `ℝ` -/

/-- The two-loop integral: for `a = α/4π` the two-loop equation `da/d ln μ = −2 b₀ a² − 2 b₁ a³` has the exact solution
`F (a(μ)) = F (a(μ₀)) + ln (μ/μ₀)` with `F a = 1/(2 b₀ a) + (b₁/2b₀²) log (a/(b₀ + b₁ a))`, since `dF/da = −1/(2a²(b₀ + b₁ a))`
is the reciprocal of the equation's right side. -/
noncomputable def F (b₀ b₁ a : ℝ) : ℝ := 1 / (2 * b₀ * a) + b₁ / (2 * b₀ ^ 2) * log (a / (b₀ + b₁ * a))

/-- `F` is strictly decreasing on `a > 0` (for `b₀, b₁ > 0`), without calculus: with `z = a(b₀ + b₁a')/(a'(b₀ + b₁a))`,
`F a − F a' = (a' − a)/(2aa'(b₀ + b₁a')) + (b₁/2b₀²)(log z − (1 − 1/z))`, both terms positive (`1 − 1/z ≤ log z`). -/
theorem F_lt_of_lt (b₀ b₁ : ℝ) (h0 : 0 < b₀) (h1 : 0 < b₁) {a a' : ℝ} (ha : 0 < a) (haa : a < a') :
    F b₀ b₁ a' < F b₀ b₁ a := by
  have ha' : 0 < a' := lt_trans ha haa
  have hd : 0 < b₀ + b₁ * a := by positivity
  have hd' : 0 < b₀ + b₁ * a' := by positivity
  have hzpos : 0 < (a * (b₀ + b₁ * a')) / (a' * (b₀ + b₁ * a)) := by positivity
  have hlogz : log ((a * (b₀ + b₁ * a')) / (a' * (b₀ + b₁ * a))) = log (a / (b₀ + b₁ * a)) - log (a' / (b₀ + b₁ * a')) := by
    rw [← log_div (by positivity) (by positivity)]
    congr 1
    field_simp
  have hbound := one_sub_inv_le_log_of_pos hzpos
  rw [hlogz, inv_div] at hbound
  have key : F b₀ b₁ a - F b₀ b₁ a' = (a' - a) / (2 * a * a' * (b₀ + b₁ * a')) +
      b₁ / (2 * b₀ ^ 2) * ((log (a / (b₀ + b₁ * a)) - log (a' / (b₀ + b₁ * a'))) - (1 - (a' * (b₀ + b₁ * a)) / (a * (b₀ + b₁ * a')))) := by
    unfold F
    field_simp
    ring
  have hpos1 : 0 < (a' - a) / (2 * a * a' * (b₀ + b₁ * a')) := by
    apply div_pos
    · linarith
    · positivity
  have hpos2 : 0 ≤ b₁ / (2 * b₀ ^ 2) * ((log (a / (b₀ + b₁ * a)) - log (a' / (b₀ + b₁ * a'))) - (1 - (a' * (b₀ + b₁ * a)) / (a * (b₀ + b₁ * a')))) := by
    apply mul_nonneg
    · positivity
    · linarith
  linarith

/-- `F` is antitone on `a > 0`. -/
theorem F_le_of_le (b₀ b₁ : ℝ) (h0 : 0 < b₀) (h1 : 0 < b₁) {a a' : ℝ} (ha : 0 < a) (haa : a ≤ a') :
    F b₀ b₁ a' ≤ F b₀ b₁ a := by
  rcases lt_or_eq_of_le haa with h | h
  · exact le_of_lt (F_lt_of_lt b₀ b₁ h0 h1 ha h)
  · rw [h]

/-- The solution of `F a = T` lies in `(lo, hi)` when `F hi < T < F lo`. -/
theorem a_of_F_bracket (b₀ b₁ : ℝ) (h0 : 0 < b₀) (h1 : 0 < b₁) {a lo hi T : ℝ} (hhi : 0 < hi) (ha : 0 < a)
    (hF : F b₀ b₁ a = T) (hT1 : T < F b₀ b₁ lo) (hT2 : F b₀ b₁ hi < T) : lo < a ∧ a < hi := by
  constructor
  · by_contra h
    rw [not_lt] at h
    have := F_le_of_le b₀ b₁ h0 h1 ha h
    linarith
  · by_contra h
    rw [not_lt] at h
    have := F_le_of_le b₀ b₁ h0 h1 hhi h
    linarith

/-- `F` at a rational point, bracketed through a bracket of its logarithm: with `c₁ = 1/(2 b₀ r)` and `c₂ = b₁/(2 b₀²)`,
`c₁ + c₂ lo ≤ F r ≤ c₁ + c₂ hi` when `lo ≤ log (r/(b₀ + b₁ r)) ≤ hi`. -/
theorem F_bracket (b₀ b₁ r c₁ c₂ lo hi : ℝ) (h0 : 0 < b₀) (h1 : 0 ≤ b₁) (hc₁ : c₁ = 1 / (2 * b₀ * r))
    (hc₂ : c₂ = b₁ / (2 * b₀ ^ 2)) (hL : lo ≤ log (r / (b₀ + b₁ * r)) ∧ log (r / (b₀ + b₁ * r)) ≤ hi) :
    c₁ + c₂ * lo ≤ F b₀ b₁ r ∧ F b₀ b₁ r ≤ c₁ + c₂ * hi := by
  unfold F
  rw [← hc₁, ← hc₂]
  have hc : 0 ≤ c₂ := by rw [hc₂]; positivity
  constructor
  · linarith [mul_le_mul_of_nonneg_left hL.1 hc]
  · linarith [mul_le_mul_of_nonneg_left hL.2 hc]

set_option maxHeartbeats 2000000 in
/-- The series bracket of `log (4.18 / 91.1876)` after `15` terms, mantissa `2^4`. -/
theorem logb_mb_MZ : (-0.310018955 : ℝ) - 4 * log 2 ≤ log (4.18 / 91.1876) ∧ log (4.18 / 91.1876) ≤ (-0.3100189532 : ℝ) - 4 * log 2 := by
  simpa using log_mantissa_bracket (4.18 / 91.1876) 4 15 (-0.310018955 : ℝ) (-0.3100189532 : ℝ) (by norm_num) (by norm_num)
    (by norm_num [sum_range_succ]) (by norm_num [sum_range_succ])

set_option maxHeartbeats 2000000 in
/-- The series bracket of `log (1.77686 / 4.18)` after `11` terms, mantissa `2^1`. -/
theorem logb_mtau_mb : (-0.1623163046 : ℝ) - log 2 ≤ log (1.77686 / 4.18) ∧ log (1.77686 / 4.18) ≤ (-0.1623163042 : ℝ) - log 2 := by
  simpa using log_mantissa_bracket (1.77686 / 4.18) 1 11 (-0.1623163046 : ℝ) (-0.1623163042 : ℝ) (by norm_num) (by norm_num)
    (by norm_num [sum_range_succ]) (by norm_num [sum_range_succ])

set_option maxHeartbeats 2000000 in
/-- The series bracket of `log ((29500 / 3141593 : ℝ) / ((23 / 3 : ℝ) + (116 / 3 : ℝ) * (29500 / 3141593 : ℝ)))` after `23` terms, mantissa `2^9`. -/
theorem logb_Fa0lo : (-0.5129240434 : ℝ) - 9 * log 2 ≤ log ((29500 / 3141593 : ℝ) / ((23 / 3 : ℝ) + (116 / 3 : ℝ) * (29500 / 3141593 : ℝ))) ∧ log ((29500 / 3141593 : ℝ) / ((23 / 3 : ℝ) + (116 / 3 : ℝ) * (29500 / 3141593 : ℝ))) ≤ (-0.5129240423 : ℝ) - 9 * log 2 := by
  simpa using log_mantissa_bracket ((29500 / 3141593 : ℝ) / ((23 / 3 : ℝ) + (116 / 3 : ℝ) * (29500 / 3141593 : ℝ))) 9 23 (-0.5129240434 : ℝ) (-0.5129240423 : ℝ) (by norm_num) (by norm_num)
    (by norm_num [sum_range_succ]) (by norm_num [sum_range_succ])

/-- `F` at `a = 29500/3141593` (`b₀ = 23/3`, `b₁ = 116/3`), bracketed through `logb_Fa0lo`. -/
theorem Fb_a0lo : (409773 / 59000 : ℝ) + (174 / 529 : ℝ) * ((-0.5129240434 : ℝ) - 9 * log 2) ≤ F (23 / 3 : ℝ) (116 / 3 : ℝ) (29500 / 3141593 : ℝ) ∧
    F (23 / 3 : ℝ) (116 / 3 : ℝ) (29500 / 3141593 : ℝ) ≤ (409773 / 59000 : ℝ) + (174 / 529 : ℝ) * ((-0.5129240423 : ℝ) - 9 * log 2) :=
  F_bracket (23 / 3 : ℝ) (116 / 3 : ℝ) (29500 / 3141593 : ℝ) (409773 / 59000 : ℝ) (174 / 529 : ℝ) _ _ (by norm_num) (by norm_num) (by norm_num) (by norm_num) logb_Fa0lo

set_option maxHeartbeats 2000000 in
/-- The series bracket of `log ((7375 / 785398 : ℝ) / ((23 / 3 : ℝ) + (116 / 3 : ℝ) * (7375 / 785398 : ℝ)))` after `23` terms, mantissa `2^9`. -/
theorem logb_Fa0hi : (-0.5129237395 : ℝ) - 9 * log 2 ≤ log ((7375 / 785398 : ℝ) / ((23 / 3 : ℝ) + (116 / 3 : ℝ) * (7375 / 785398 : ℝ))) ∧ log ((7375 / 785398 : ℝ) / ((23 / 3 : ℝ) + (116 / 3 : ℝ) * (7375 / 785398 : ℝ))) ≤ (-0.5129237384 : ℝ) - 9 * log 2 := by
  simpa using log_mantissa_bracket ((7375 / 785398 : ℝ) / ((23 / 3 : ℝ) + (116 / 3 : ℝ) * (7375 / 785398 : ℝ))) 9 23 (-0.5129237395 : ℝ) (-0.5129237384 : ℝ) (by norm_num) (by norm_num)
    (by norm_num [sum_range_succ]) (by norm_num [sum_range_succ])

/-- `F` at `a = 7375/785398` (`b₀ = 23/3`, `b₁ = 116/3`), bracketed through `logb_Fa0hi`. -/
theorem Fb_a0hi : (1178097 / 169625 : ℝ) + (174 / 529 : ℝ) * ((-0.5129237395 : ℝ) - 9 * log 2) ≤ F (23 / 3 : ℝ) (116 / 3 : ℝ) (7375 / 785398 : ℝ) ∧
    F (23 / 3 : ℝ) (116 / 3 : ℝ) (7375 / 785398 : ℝ) ≤ (1178097 / 169625 : ℝ) + (174 / 529 : ℝ) * ((-0.5129237384 : ℝ) - 9 * log 2) :=
  F_bracket (23 / 3 : ℝ) (116 / 3 : ℝ) (7375 / 785398 : ℝ) (1178097 / 169625 : ℝ) (174 / 529 : ℝ) _ _ (by norm_num) (by norm_num) (by norm_num) (by norm_num) logb_Fa0hi

set_option maxHeartbeats 2000000 in
/-- The series bracket of `log ((1779 / 100000 : ℝ) / ((23 / 3 : ℝ) + (116 / 3 : ℝ) * (1779 / 100000 : ℝ)))` after `27` terms, mantissa `2^8`. -/
theorem logb_F5lob : (-0.606747235 : ℝ) - 8 * log 2 ≤ log ((1779 / 100000 : ℝ) / ((23 / 3 : ℝ) + (116 / 3 : ℝ) * (1779 / 100000 : ℝ))) ∧ log ((1779 / 100000 : ℝ) / ((23 / 3 : ℝ) + (116 / 3 : ℝ) * (1779 / 100000 : ℝ))) ≤ (-0.6067472339 : ℝ) - 8 * log 2 := by
  simpa using log_mantissa_bracket ((1779 / 100000 : ℝ) / ((23 / 3 : ℝ) + (116 / 3 : ℝ) * (1779 / 100000 : ℝ))) 8 27 (-0.606747235 : ℝ) (-0.6067472339 : ℝ) (by norm_num) (by norm_num)
    (by norm_num [sum_range_succ]) (by norm_num [sum_range_succ])

/-- `F` at `a = 1779/100000` (`b₀ = 23/3`, `b₁ = 116/3`), bracketed through `logb_F5lob`. -/
theorem Fb_5lob : (50000 / 13639 : ℝ) + (174 / 529 : ℝ) * ((-0.606747235 : ℝ) - 8 * log 2) ≤ F (23 / 3 : ℝ) (116 / 3 : ℝ) (1779 / 100000 : ℝ) ∧
    F (23 / 3 : ℝ) (116 / 3 : ℝ) (1779 / 100000 : ℝ) ≤ (50000 / 13639 : ℝ) + (174 / 529 : ℝ) * ((-0.6067472339 : ℝ) - 8 * log 2) :=
  F_bracket (23 / 3 : ℝ) (116 / 3 : ℝ) (1779 / 100000 : ℝ) (50000 / 13639 : ℝ) (174 / 529 : ℝ) _ _ (by norm_num) (by norm_num) (by norm_num) (by norm_num) logb_F5lob

set_option maxHeartbeats 2000000 in
/-- The series bracket of `log ((8897 / 500000 : ℝ) / ((23 / 3 : ℝ) + (116 / 3 : ℝ) * (8897 / 500000 : ℝ)))` after `27` terms, mantissa `2^8`. -/
theorem logb_F5hib : (-0.6065409275 : ℝ) - 8 * log 2 ≤ log ((8897 / 500000 : ℝ) / ((23 / 3 : ℝ) + (116 / 3 : ℝ) * (8897 / 500000 : ℝ))) ∧ log ((8897 / 500000 : ℝ) / ((23 / 3 : ℝ) + (116 / 3 : ℝ) * (8897 / 500000 : ℝ))) ≤ (-0.6065409265 : ℝ) - 8 * log 2 := by
  simpa using log_mantissa_bracket ((8897 / 500000 : ℝ) / ((23 / 3 : ℝ) + (116 / 3 : ℝ) * (8897 / 500000 : ℝ))) 8 27 (-0.6065409275 : ℝ) (-0.6065409265 : ℝ) (by norm_num) (by norm_num)
    (by norm_num [sum_range_succ]) (by norm_num [sum_range_succ])

/-- `F` at `a = 8897/500000` (`b₀ = 23/3`, `b₁ = 116/3`), bracketed through `logb_F5hib`. -/
theorem Fb_5hib : (750000 / 204631 : ℝ) + (174 / 529 : ℝ) * ((-0.6065409275 : ℝ) - 8 * log 2) ≤ F (23 / 3 : ℝ) (116 / 3 : ℝ) (8897 / 500000 : ℝ) ∧
    F (23 / 3 : ℝ) (116 / 3 : ℝ) (8897 / 500000 : ℝ) ≤ (750000 / 204631 : ℝ) + (174 / 529 : ℝ) * ((-0.6065409265 : ℝ) - 8 * log 2) :=
  F_bracket (23 / 3 : ℝ) (116 / 3 : ℝ) (8897 / 500000 : ℝ) (750000 / 204631 : ℝ) (174 / 529 : ℝ) _ _ (by norm_num) (by norm_num) (by norm_num) (by norm_num) logb_F5hib

set_option maxHeartbeats 2000000 in
/-- The series bracket of `log ((1779 / 100000 : ℝ) / ((25 / 3 : ℝ) + (154 / 3 : ℝ) * (1779 / 100000 : ℝ)))` after `4` terms, mantissa `2^9`. -/
theorem logb_F4lob : (-0.0150450224 : ℝ) - 9 * log 2 ≤ log ((1779 / 100000 : ℝ) / ((25 / 3 : ℝ) + (154 / 3 : ℝ) * (1779 / 100000 : ℝ))) ∧ log ((1779 / 100000 : ℝ) / ((25 / 3 : ℝ) + (154 / 3 : ℝ) * (1779 / 100000 : ℝ))) ≤ (-0.0150450208 : ℝ) - 9 * log 2 := by
  simpa using log_mantissa_bracket ((1779 / 100000 : ℝ) / ((25 / 3 : ℝ) + (154 / 3 : ℝ) * (1779 / 100000 : ℝ))) 9 4 (-0.0150450224 : ℝ) (-0.0150450208 : ℝ) (by norm_num) (by norm_num)
    (by norm_num [sum_range_succ]) (by norm_num [sum_range_succ])

/-- `F` at `a = 1779/100000` (`b₀ = 25/3`, `b₁ = 154/3`), bracketed through `logb_F4lob`. -/
theorem Fb_4lob : (2000 / 593 : ℝ) + (231 / 625 : ℝ) * ((-0.0150450224 : ℝ) - 9 * log 2) ≤ F (25 / 3 : ℝ) (154 / 3 : ℝ) (1779 / 100000 : ℝ) ∧
    F (25 / 3 : ℝ) (154 / 3 : ℝ) (1779 / 100000 : ℝ) ≤ (2000 / 593 : ℝ) + (231 / 625 : ℝ) * ((-0.0150450208 : ℝ) - 9 * log 2) :=
  F_bracket (25 / 3 : ℝ) (154 / 3 : ℝ) (1779 / 100000 : ℝ) (2000 / 593 : ℝ) (231 / 625 : ℝ) _ _ (by norm_num) (by norm_num) (by norm_num) (by norm_num) logb_F4lob

set_option maxHeartbeats 2000000 in
/-- The series bracket of `log ((8897 / 500000 : ℝ) / ((25 / 3 : ℝ) + (154 / 3 : ℝ) * (8897 / 500000 : ℝ)))` after `4` terms, mantissa `2^9`. -/
theorem logb_F4hib : (-0.0148424084 : ℝ) - 9 * log 2 ≤ log ((8897 / 500000 : ℝ) / ((25 / 3 : ℝ) + (154 / 3 : ℝ) * (8897 / 500000 : ℝ))) ∧ log ((8897 / 500000 : ℝ) / ((25 / 3 : ℝ) + (154 / 3 : ℝ) * (8897 / 500000 : ℝ))) ≤ (-0.0148424069 : ℝ) - 9 * log 2 := by
  simpa using log_mantissa_bracket ((8897 / 500000 : ℝ) / ((25 / 3 : ℝ) + (154 / 3 : ℝ) * (8897 / 500000 : ℝ))) 9 4 (-0.0148424084 : ℝ) (-0.0148424069 : ℝ) (by norm_num) (by norm_num)
    (by norm_num [sum_range_succ]) (by norm_num [sum_range_succ])

/-- `F` at `a = 8897/500000` (`b₀ = 25/3`, `b₁ = 154/3`), bracketed through `logb_F4hib`. -/
theorem Fb_4hib : (30000 / 8897 : ℝ) + (231 / 625 : ℝ) * ((-0.0148424084 : ℝ) - 9 * log 2) ≤ F (25 / 3 : ℝ) (154 / 3 : ℝ) (8897 / 500000 : ℝ) ∧
    F (25 / 3 : ℝ) (154 / 3 : ℝ) (8897 / 500000 : ℝ) ≤ (30000 / 8897 : ℝ) + (231 / 625 : ℝ) * ((-0.0148424069 : ℝ) - 9 * log 2) :=
  F_bracket (25 / 3 : ℝ) (154 / 3 : ℝ) (8897 / 500000 : ℝ) (30000 / 8897 : ℝ) (231 / 625 : ℝ) _ _ (by norm_num) (by norm_num) (by norm_num) (by norm_num) logb_F4hib

set_option maxHeartbeats 2000000 in
/-- The series bracket of `log ((24927 / 1000000 : ℝ) / ((25 / 3 : ℝ) + (154 / 3 : ℝ) * (24927 / 1000000 : ℝ)))` after `19` terms, mantissa `2^8`. -/
theorem logb_F4lot : (-0.4097342393 : ℝ) - 8 * log 2 ≤ log ((24927 / 1000000 : ℝ) / ((25 / 3 : ℝ) + (154 / 3 : ℝ) * (24927 / 1000000 : ℝ))) ∧ log ((24927 / 1000000 : ℝ) / ((25 / 3 : ℝ) + (154 / 3 : ℝ) * (24927 / 1000000 : ℝ))) ≤ (-0.4097342382 : ℝ) - 8 * log 2 := by
  simpa using log_mantissa_bracket ((24927 / 1000000 : ℝ) / ((25 / 3 : ℝ) + (154 / 3 : ℝ) * (24927 / 1000000 : ℝ))) 8 19 (-0.4097342393 : ℝ) (-0.4097342382 : ℝ) (by norm_num) (by norm_num)
    (by norm_num [sum_range_succ]) (by norm_num [sum_range_succ])

/-- `F` at `a = 24927/1000000` (`b₀ = 25/3`, `b₁ = 154/3`), bracketed through `logb_F4lot`. -/
theorem Fb_4lot : (20000 / 8309 : ℝ) + (231 / 625 : ℝ) * ((-0.4097342393 : ℝ) - 8 * log 2) ≤ F (25 / 3 : ℝ) (154 / 3 : ℝ) (24927 / 1000000 : ℝ) ∧
    F (25 / 3 : ℝ) (154 / 3 : ℝ) (24927 / 1000000 : ℝ) ≤ (20000 / 8309 : ℝ) + (231 / 625 : ℝ) * ((-0.4097342382 : ℝ) - 8 * log 2) :=
  F_bracket (25 / 3 : ℝ) (154 / 3 : ℝ) (24927 / 1000000 : ℝ) (20000 / 8309 : ℝ) (231 / 625 : ℝ) _ _ (by norm_num) (by norm_num) (by norm_num) (by norm_num) logb_F4lot

set_option maxHeartbeats 2000000 in
/-- The series bracket of `log ((24937 / 1000000 : ℝ) / ((25 / 3 : ℝ) + (154 / 3 : ℝ) * (24937 / 1000000 : ℝ)))` after `19` terms, mantissa `2^8`. -/
theorem logb_F4hit : (-0.4093865473 : ℝ) - 8 * log 2 ≤ log ((24937 / 1000000 : ℝ) / ((25 / 3 : ℝ) + (154 / 3 : ℝ) * (24937 / 1000000 : ℝ))) ∧ log ((24937 / 1000000 : ℝ) / ((25 / 3 : ℝ) + (154 / 3 : ℝ) * (24937 / 1000000 : ℝ))) ≤ (-0.4093865462 : ℝ) - 8 * log 2 := by
  simpa using log_mantissa_bracket ((24937 / 1000000 : ℝ) / ((25 / 3 : ℝ) + (154 / 3 : ℝ) * (24937 / 1000000 : ℝ))) 8 19 (-0.4093865473 : ℝ) (-0.4093865462 : ℝ) (by norm_num) (by norm_num)
    (by norm_num [sum_range_succ]) (by norm_num [sum_range_succ])

/-- `F` at `a = 24937/1000000` (`b₀ = 25/3`, `b₁ = 154/3`), bracketed through `logb_F4hit`. -/
theorem Fb_4hit : (60000 / 24937 : ℝ) + (231 / 625 : ℝ) * ((-0.4093865473 : ℝ) - 8 * log 2) ≤ F (25 / 3 : ℝ) (154 / 3 : ℝ) (24937 / 1000000 : ℝ) ∧
    F (25 / 3 : ℝ) (154 / 3 : ℝ) (24937 / 1000000 : ℝ) ≤ (60000 / 24937 : ℝ) + (231 / 625 : ℝ) * ((-0.4093865462 : ℝ) - 8 * log 2) :=
  F_bracket (25 / 3 : ℝ) (154 / 3 : ℝ) (24937 / 1000000 : ℝ) (60000 / 24937 : ℝ) (231 / 625 : ℝ) _ _ (by norm_num) (by norm_num) (by norm_num) (by norm_num) logb_F4hit

set_option maxHeartbeats 1000000 in
/-- 46:P2 [chart] — **the two-loop run as the equation's exact solution.** From `α_s(M_Z) = 0.1180` at `M_Z = 91.1876` GeV
through `m_b = 4.18` (five flavours, `b₀ = 23/3`, `b₁ = 116/3`) to `m_τ = 1.77686` (four flavours, `b₀ = 25/3`, `b₁ = 154/3`),
with `a = α/4π` and the two-loop integral `F`: `α_s(m_b)` lies in `(0.2235, 0.2237)` and `α_s(m_τ)` in `(0.3132, 0.3134)` —
the chart's Runge–Kutta reading `0.313` (`chart_yangmills.two_loop`), against the τ-decay `0.312(15)`. Each solution is
bracketed by `F`'s monotonicity between rational ends, the logarithms by the series after `n` terms and `ln 2` to nine
places, `π` to six. -/
theorem two_loop_tau (a₀ a_b a_τ : ℝ) (h₀ : a₀ = 0.1180 / (4 * π)) (hb : 0 < a_b) (hτ : 0 < a_τ)
    (hFb : F (23 / 3) (116 / 3) a_b = F (23 / 3) (116 / 3) a₀ + log (4.18 / 91.1876))
    (hFτ : F (25 / 3) (154 / 3) a_τ = F (25 / 3) (154 / 3) a_b + log (1.77686 / 4.18)) :
    (0.2235 : ℝ) < 4 * π * a_b ∧ 4 * π * a_b < 0.2237 ∧ (0.3132 : ℝ) < 4 * π * a_τ ∧ 4 * π * a_τ < 0.3134 := by
  have hpi1 := pi_gt_d6
  have hpi2 := pi_lt_d6
  have hl1 := log_two_gt_d9
  have hl2 := log_two_lt_d9
  have hb0 : (0 : ℝ) < 23 / 3 := by norm_num
  have hb1 : (0 : ℝ) < 116 / 3 := by norm_num
  have hb0' : (0 : ℝ) < 25 / 3 := by norm_num
  have hb1' : (0 : ℝ) < 154 / 3 := by norm_num
  have ha₀lo : (29500 / 3141593 : ℝ) < a₀ := by
    rw [h₀, lt_div_iff₀ (by positivity)]; linarith
  have ha₀hi : a₀ < (7375 / 785398 : ℝ) := by
    rw [h₀, div_lt_iff₀ (by positivity)]; linarith
  have ha₀ : 0 < a₀ := lt_trans (by norm_num) ha₀lo
  have hLb := logb_mb_MZ
  have hLt := logb_mtau_mb
  have hFa0lo := Fb_a0lo
  have hFa0hi := Fb_a0hi
  have hF5lob := Fb_5lob
  have hF5hib := Fb_5hib
  have hF4lob := Fb_4lob
  have hF4hib := Fb_4hib
  have hF4lot := Fb_4lot
  have hF4hit := Fb_4hit
  have hFa₀1 := F_lt_of_lt (23 / 3) (116 / 3) hb0 hb1 ha₀ ha₀hi
  have hFa₀2 := F_lt_of_lt (23 / 3) (116 / 3) hb0 hb1 (by norm_num) ha₀lo
  have hab := a_of_F_bracket (23 / 3) (116 / 3) hb0 hb1 (lo := (1779 / 100000 : ℝ)) (hi := (8897 / 500000 : ℝ)) (by norm_num) hb hFb
    (by linarith) (by linarith)
  have hF4b1 := F_le_of_le (25 / 3) (154 / 3) hb0' hb1' hb (le_of_lt hab.2)
  have hF4b2 := F_le_of_le (25 / 3) (154 / 3) hb0' hb1' (by norm_num) (le_of_lt hab.1)
  have hat := a_of_F_bracket (25 / 3) (154 / 3) hb0' hb1' (lo := (24927 / 1000000 : ℝ)) (hi := (24937 / 1000000 : ℝ)) (by norm_num) hτ hFτ
    (by linarith) (by linarith)
  have hm1 := mul_lt_mul'' (by linarith : (4 : ℝ) * 3.141592 < 4 * π) hab.1 (by norm_num) (by norm_num)
  have hm2 := mul_lt_mul'' (by linarith : (4 : ℝ) * π < 4 * 3.141593) hab.2 (by positivity) hb.le
  have hm3 := mul_lt_mul'' (by linarith : (4 : ℝ) * 3.141592 < 4 * π) hat.1 (by norm_num) (by norm_num)
  have hm4 := mul_lt_mul'' (by linarith : (4 : ℝ) * π < 4 * 3.141593) hat.2 (by positivity) hτ.le
  norm_num at hm1 hm2 hm3 hm4
  exact ⟨by linarith, by linarith, by linarith, by linarith⟩

set_option maxHeartbeats 1000000 in
/-- 46:P2 [chart] — **the one-loop law over `ℝ`**: `1/α(μ) = 1/α(μ₀) + (b₀/2π) ln (μ/μ₀)` across the same thresholds gives
`α_s(m_τ)` in `(0.2785, 0.2795)`, the row's `0.279`, `2.2` standard deviations below `0.312(15)`. -/
theorem one_loop_tau (α : ℝ)
    (h : 1 / α = 1 / 0.1180 + (23 / 3) / (2 * π) * log (4.18 / 91.1876) + (25 / 3) / (2 * π) * log (1.77686 / 4.18)) :
    (0.2785 : ℝ) < α ∧ α < 0.2795 ∧ (2.1 : ℝ) < (0.312 - 0.279) / 0.015 ∧ ((0.312 : ℝ) - 0.279) / 0.015 < 2.3 := by
  have hpi1 := pi_gt_d6
  have hpi2 := pi_lt_d6
  have hl1 := log_two_gt_d9
  have hl2 := log_two_lt_d9
  have hLb := logb_mb_MZ
  have hLt := logb_mtau_mb
  have hpos : 0 < 2 * π := by positivity
  have hp1 : (1 : ℝ) / (2 * 3.141593) < 1 / (2 * π) := one_div_lt_one_div_of_lt (by positivity) (by linarith)
  have hp2 : (1 : ℝ) / (2 * π) < 1 / (2 * 3.141592) := one_div_lt_one_div_of_lt (by positivity) (by linarith)
  have hLb' : log (4.18 / 91.1876) < 0 := by linarith [hLb.2]
  have hLt' : log (1.77686 / 4.18) < 0 := by linarith [hLt.2]
  have e : 1 / α = 1 / 0.1180 + 1 / (2 * π) * ((23 / 3) * log (4.18 / 91.1876) + (25 / 3) * log (1.77686 / 4.18)) := by
    rw [h]; ring
  set S := (23 / 3) * log (4.18 / 91.1876) + (25 / 3) * log (1.77686 / 4.18) with hS
  have hSneg : S < 0 := by rw [hS]; linarith
  have hS1 : ((-38452734889) / 1250000000 : ℝ) < S := by rw [hS]; linarith
  have hS2 : S < ((-922865636237) / 30000000000 : ℝ) := by rw [hS]; linarith
  have hm1 := mul_lt_mul_of_neg_right hp2 hSneg
  have hm2 := mul_lt_mul_of_pos_left hS1 (by positivity : (0 : ℝ) < 1 / (2 * 3.141592))
  have hm3 := mul_lt_mul_of_neg_right hp1 hSneg
  have hm4 := mul_lt_mul_of_pos_left hS2 (by positivity : (0 : ℝ) < 1 / (2 * 3.141593))
  norm_num at hm1 hm2 hm3 hm4
  have hinv1 : (3.5786 : ℝ) < 1 / α := by rw [e]; norm_num; linarith
  have hinv2 : 1 / α < (3.5787 : ℝ) := by rw [e]; norm_num; linarith
  have hαpos : 0 < α := by
    by_contra hneg
    rw [not_lt] at hneg
    have : 1 / α ≤ 0 := by
      rcases lt_or_eq_of_le hneg with h' | h'
      · exact le_of_lt (one_div_neg.mpr h')
      · rw [h']; simp
    linarith
  have hα : α = 1 / (1 / α) := (one_div_one_div α).symm
  refine ⟨?_, ?_, by norm_num, by norm_num⟩
  · rw [hα]; rw [lt_div_iff₀ (by positivity)]; nlinarith
  · rw [hα]; rw [div_lt_iff₀ (by positivity)]; nlinarith

/-! ## 46:C10 — the Herbst comparison and the couplings at the chart's fixed points -/

/-- 46:C10 [chart] — the declared coupling `α_s(√σ) = 2π/(9 ln 2)` lies in `(1.0065, 1.0075)` (the row's `1.007`), the
two-adjoint term's `C = C_A α_s` in `(3.015, 3.025)` (the row's `3.02`), above the Herbst bound `4/π` of the two-body form,
itself above the one-body bound `2/π`: `π² > 6 ln 2`. -/
theorem herbst_real : (1.0065 : ℝ) < 2 * π / (9 * log 2) ∧ 2 * π / (9 * log 2) < 1.0075 ∧
    (3.015 : ℝ) < 3 * (2 * π / (9 * log 2)) ∧ 3 * (2 * π / (9 * log 2)) < 3.025 ∧
    4 / π < 3 * (2 * π / (9 * log 2)) ∧ 2 / π < 4 / π ∧ 6 * log 2 < π ^ 2 := by
  have hpi1 := pi_gt_d6
  have hpi2 := pi_lt_d6
  have hl1 := log_two_gt_d9
  have hl2 := log_two_lt_d9
  have hlpos : 0 < 9 * log 2 := by linarith
  have h1 : (1.0065 : ℝ) < 2 * π / (9 * log 2) := by rw [lt_div_iff₀ hlpos]; nlinarith
  have h2 : 2 * π / (9 * log 2) < (1.0075 : ℝ) := by rw [div_lt_iff₀ hlpos]; nlinarith
  refine ⟨h1, h2, by linarith, by linarith, ?_, ?_, by nlinarith⟩
  · rw [div_lt_iff₀ (by positivity)]
    have : 3 * (2 * π / (9 * log 2)) * π = 2 * π ^ 2 / (3 * log 2) := by field_simp; ring
    rw [this, lt_div_iff₀ (by positivity)]
    nlinarith
  · exact div_lt_div_of_pos_right (by norm_num) (by positivity)

set_option maxHeartbeats 2000000 in
/-- The series bracket of `log (1 / (2 * 3.541))` after `25` terms, mantissa `2^2`. -/
theorem logb_E3541 : (-0.5712619933 : ℝ) - 2 * log 2 ≤ log (1 / (2 * 3.541)) ∧ log (1 / (2 * 3.541)) ≤ (-0.5712619918 : ℝ) - 2 * log 2 := by
  simpa using log_mantissa_bracket (1 / (2 * 3.541)) 2 25 (-0.5712619933 : ℝ) (-0.5712619918 : ℝ) (by norm_num) (by norm_num)
    (by norm_num [sum_range_succ]) (by norm_num [sum_range_succ])

set_option maxHeartbeats 2000000 in
/-- The series bracket of `log (1 / (2 * 3.085))` after `20` terms, mantissa `2^2`. -/
theorem logb_E3085 : (-0.4334044773 : ℝ) - 2 * log 2 ≤ log (1 / (2 * 3.085)) ∧ log (1 / (2 * 3.085)) ≤ (-0.4334044763 : ℝ) - 2 * log 2 := by
  simpa using log_mantissa_bracket (1 / (2 * 3.085)) 2 20 (-0.4334044773 : ℝ) (-0.4334044763 : ℝ) (by norm_num) (by norm_num)
    (by norm_num [sum_range_succ]) (by norm_num [sum_range_succ])

set_option maxHeartbeats 2000000 in
/-- The series bracket of `log (1 / (2 * 2.611))` after `14` terms, mantissa `2^2`. -/
theorem logb_E2611 : (-0.2665861096 : ℝ) - 2 * log 2 ≤ log (1 / (2 * 2.611)) ∧ log (1 / (2 * 2.611)) ≤ (-0.2665861086 : ℝ) - 2 * log 2 := by
  simpa using log_mantissa_bracket (1 / (2 * 2.611)) 2 14 (-0.2665861096 : ℝ) (-0.2665861086 : ℝ) (by norm_num) (by norm_num)
    (by norm_num [sum_range_succ]) (by norm_num [sum_range_succ])

/-- 46:C10 [chart] — the couplings at the chart's fixed points. The two-body fixed points of `2|p| + 2r − C/max(r, r_c)`
with `C = C_A α_s(E)` read at the bound state's own mass are the chart's roots `E = 3.541`, `3.085`, `2.611` at `r_c = 1`,
`1/2`, `1/4` cells (the Lanczos grid of `chart_yangmills.fixed_point_bisect`; none at `1/8`). At these roots the coupling
`C(E) = 2π/(3 ln 2E)` lies in `(1.0698, 1.0700)`, `(1.1508, 1.1511)`, `(1.2670, 1.2672)`: every fixed point sits below the
Herbst bound `4/π = 1.2732` of the two-body form, the quarter-cell one within `0.5 %` of it. -/
theorem fixed_point_couplings :
    (1.0698 : ℝ) < 2 * π / (3 * log (2 * 3.541)) ∧ 2 * π / (3 * log (2 * 3.541)) < (1.07 : ℝ) ∧
    (1.1508 : ℝ) < 2 * π / (3 * log (2 * 3.085)) ∧ 2 * π / (3 * log (2 * 3.085)) < (1.1511 : ℝ) ∧
    (1.267 : ℝ) < 2 * π / (3 * log (2 * 2.611)) ∧ 2 * π / (3 * log (2 * 2.611)) < (1.2672 : ℝ) ∧
    2 * π / (3 * log (2 * 2.611)) < 4 / π ∧ 0.995 * (4 / π) < 2 * π / (3 * log (2 * 2.611)) := by
  have hpi1 := pi_gt_d6
  have hpi2 := pi_lt_d6
  have hl1 := log_two_gt_d9
  have hl2 := log_two_lt_d9
  have hq0 := logb_E3541
  have hln0 : log (2 * 3.541) = -log (1 / (2 * 3.541)) := by rw [one_div, log_inv, neg_neg]
  have hL0 : (4893890881 / 2500000000 : ℝ) < log (2 * 3.541) ∧ log (2 * 3.541) < (19575563549 / 10000000000 : ℝ) := by
    rw [hln0]; constructor <;> linarith [hq0.1, hq0.2]
  have hpos0 : 0 < 3 * log (2 * 3.541) := by linarith [hL0.1]
  have hC0 : (1.0698 : ℝ) < 2 * π / (3 * log (2 * 3.541)) ∧ 2 * π / (3 * log (2 * 3.541)) < (1.07 : ℝ) := by
    constructor
    · rw [lt_div_iff₀ hpos0]; nlinarith [hL0.1, hL0.2]
    · rw [div_lt_iff₀ hpos0]; nlinarith [hL0.1, hL0.2]
  have hq1 := logb_E3085
  have hln1 : log (2 * 3.085) = -log (1 / (2 * 3.085)) := by rw [one_div, log_inv, neg_neg]
  have hL1 : (18196988369 / 10000000000 : ℝ) < log (2 * 3.085) ∧ log (2 * 3.085) < (18196988389 / 10000000000 : ℝ) := by
    rw [hln1]; constructor <;> linarith [hq1.1, hq1.2]
  have hpos1 : 0 < 3 * log (2 * 3.085) := by linarith [hL1.1]
  have hC1 : (1.1508 : ℝ) < 2 * π / (3 * log (2 * 3.085)) ∧ 2 * π / (3 * log (2 * 3.085)) < (1.1511 : ℝ) := by
    constructor
    · rw [lt_div_iff₀ hpos1]; nlinarith [hL1.1, hL1.2]
    · rw [div_lt_iff₀ hpos1]; nlinarith [hL1.1, hL1.2]
  have hq2 := logb_E2611
  have hln2 : log (2 * 2.611) = -log (1 / (2 * 2.611)) := by rw [one_div, log_inv, neg_neg]
  have hL2 : (4132201173 / 2500000000 : ℝ) < log (2 * 2.611) ∧ log (2 * 2.611) < (2066100589 / 1250000000 : ℝ) := by
    rw [hln2]; constructor <;> linarith [hq2.1, hq2.2]
  have hpos2 : 0 < 3 * log (2 * 2.611) := by linarith [hL2.1]
  have hC2 : (1.267 : ℝ) < 2 * π / (3 * log (2 * 2.611)) ∧ 2 * π / (3 * log (2 * 2.611)) < (1.2672 : ℝ) := by
    constructor
    · rw [lt_div_iff₀ hpos2]; nlinarith [hL2.1, hL2.2]
    · rw [div_lt_iff₀ hpos2]; nlinarith [hL2.1, hL2.2]
  have h4pi1 : (1.2672 : ℝ) < 4 / π := by rw [lt_div_iff₀ (by positivity)]; nlinarith
  have h4pi2 : 0.995 * (4 / π) < (1.2670 : ℝ) := by
    have : (0.995 : ℝ) * (4 / π) = 3.98 / π := by ring
    rw [this, div_lt_iff₀ (by positivity)]; nlinarith
  exact ⟨hC0.1, hC0.2, hC1.1, hC1.2, hC2.1, hC2.2, by linarith [hC2.2], by linarith [hC2.1]⟩

/-! ## 46:C11 — the imported series and the ratio -/

/-- The imported `0⁺⁺` series of the strong-coupling expansion to order `u^n` (Münster 1981, as quoted by Langelage,
Münster and Philipsen 2007, eq. 2.16): `Σ_{k=1}^{n} M_k u^k` with `M = (−3, 9, −27/2, −7, −297/2, 858827/10240, 47641149/71680)`. -/
noncomputable def P3 (u : ℝ) : ℝ := -3 * u + 9 * u ^ 2 - 27 / 2 * u ^ 3
noncomputable def P5 (u : ℝ) : ℝ := P3 u - 7 * u ^ 4 - 297 / 2 * u ^ 5
noncomputable def P7 (u : ℝ) : ℝ := P5 u + 858827 / 10240 * u ^ 6 + 47641149 / 71680 * u ^ 7

/-- The channel's mass over the leading-order tension, `m/√σ = (−4 ln u + P)/√(−ln u)`. -/
noncomputable def ratio (u P : ℝ) : ℝ := (4 * (-log u) + P) / √(-log u)

/-- A bracket of `ratio u P` from a bracket `Llo ≤ −log u ≤ Lhi` and rational square-root ends `slo² < Llo`, `Lhi < shi²`. -/
theorem ratio_bracket (u P Llo Lhi slo shi lo hi : ℝ) (hL : Llo ≤ -log u ∧ -log u ≤ Lhi)
    (hslo : 0 < slo) (hs1 : slo ^ 2 < Llo) (hshi : 0 < shi) (hs2 : Lhi < shi ^ 2) (hP : 0 < 4 * Llo + P)
    (hlo : lo ≤ (4 * Llo + P) / shi) (hhi : (4 * Lhi + P) / slo ≤ hi) : lo ≤ ratio u P ∧ ratio u P ≤ hi := by
  have hsq : 0 < slo ^ 2 := by positivity
  have hLpos : 0 < -log u := by linarith [hL.1]
  have hs_lo : slo < √(-log u) := by rw [lt_sqrt hslo.le]; linarith [hL.1]
  have hs_hi : √(-log u) < shi := by rw [sqrt_lt' hshi]; linarith [hL.2]
  have hspos : 0 < √(-log u) := lt_trans hslo hs_lo
  unfold ratio
  constructor
  · refine le_trans hlo ?_
    rw [div_le_div_iff₀ hshi hspos]
    nlinarith [hs_hi, hL.1, hP, hspos]
  · refine le_trans ?_ hhi
    rw [div_le_div_iff₀ hspos hslo]
    nlinarith [hs_lo, hL.2, hP, hspos, hLpos]

/-! ## 46:C11 — the plaquette channel at the chart's cells -/

/-- The step of the chart's cells in the stiffness (46:B6): the one-loop law of powers with `b₀ = 11` and the drive `g = 2`
lowers the stiffness by `11 ln 2/(8π²)` from one cell to the next. -/
noncomputable def cellStep : ℝ := 11 * log 2 / (8 * π ^ 2)

/-- The stiffness of the chart's cell `n` (46:B6): `ϑ_n = 1 − n · 11 ln 2/(8π²)`; the cell `0` is channel unity. -/
noncomputable def cellStiffness (n : ℕ) : ℝ := 1 - n * cellStep

/-- The computed terms of the frame's fundamental plaquette coefficient, through `ϑ⁷` (46:C7):
`ϑ/3 + ϑ²/6 − 5ϑ⁴/72 − ϑ⁵/24 + 7ϑ⁶/720 + 59ϑ⁷/2160`. -/
noncomputable def c3terms (t : ℝ) : ℝ :=
  t / 3 + t ^ 2 / 6 - 5 / 72 * t ^ 4 - 1 / 24 * t ^ 5 + 7 / 720 * t ^ 6 + 59 / 2160 * t ^ 7

/-- The chart's `u` at the cell `n`: the sum of the computed terms at the cell's stiffness. -/
noncomputable def cellU (n : ℕ) : ℝ := c3terms (cellStiffness n)

/-- The step between `0.096566906` and `0.0965669688`, from Mathlib's brackets of `ln 2` and of `π`. -/
theorem cellStep_bracket : (0.096566906 : ℝ) ≤ cellStep ∧ cellStep ≤ (0.0965669688 : ℝ) := by
  have hl1 := log_two_gt_d9
  have hl2 := log_two_lt_d9
  have hp1 := pi_gt_d6
  have hp2 := pi_lt_d6
  have hp0 : (0 : ℝ) < π := pi_pos
  have hsq1 : (9.8696002 : ℝ) < π ^ 2 := by nlinarith [hp1, hp0]
  have hsq2 : π ^ 2 < (9.8696066 : ℝ) := by nlinarith [hp2, hp0]
  have hpos : (0 : ℝ) < 8 * π ^ 2 := by positivity
  unfold cellStep
  constructor
  · rw [le_div_iff₀ hpos]; linarith
  · rw [div_le_iff₀ hpos]; linarith

/-- The stiffness of the cell `n` between `1 − n · 0.0965669688` and `1 − n · 0.096566906`. -/
theorem cellStiffness_bracket (n : ℕ) :
    1 - n * (0.0965669688 : ℝ) ≤ cellStiffness n ∧ cellStiffness n ≤ 1 - n * (0.096566906 : ℝ) := by
  have h := cellStep_bracket
  have hn : (0 : ℝ) ≤ n := Nat.cast_nonneg n
  have h1 := mul_le_mul_of_nonneg_left h.1 hn
  have h2 := mul_le_mul_of_nonneg_left h.2 hn
  unfold cellStiffness
  constructor <;> linarith

/-- The computed terms on an interval `0 ≤ a ≤ t ≤ b`: each term at the end its sign selects. -/
theorem c3terms_bracket (t a b : ℝ) (ha : 0 ≤ a) (hat : a ≤ t) (htb : t ≤ b) :
    a / 3 + a ^ 2 / 6 - 5 / 72 * b ^ 4 - 1 / 24 * b ^ 5 + 7 / 720 * a ^ 6 + 59 / 2160 * a ^ 7 ≤ c3terms t ∧
    c3terms t ≤ b / 3 + b ^ 2 / 6 - 5 / 72 * a ^ 4 - 1 / 24 * a ^ 5 + 7 / 720 * b ^ 6 + 59 / 2160 * b ^ 7 := by
  have ht : 0 ≤ t := le_trans ha hat
  have a2 := pow_le_pow_left₀ ha hat 2
  have a4 := pow_le_pow_left₀ ha hat 4
  have a5 := pow_le_pow_left₀ ha hat 5
  have a6 := pow_le_pow_left₀ ha hat 6
  have a7 := pow_le_pow_left₀ ha hat 7
  have b2 := pow_le_pow_left₀ ht htb 2
  have b4 := pow_le_pow_left₀ ht htb 4
  have b5 := pow_le_pow_left₀ ht htb 5
  have b6 := pow_le_pow_left₀ ht htb 6
  have b7 := pow_le_pow_left₀ ht htb 7
  unfold c3terms
  constructor <;> linarith

/-- The three orders of the imported series on an interval `0 ≤ a ≤ u ≤ b`: each term at the end its sign selects. -/
theorem P_bracket (u a b : ℝ) (ha : 0 ≤ a) (hau : a ≤ u) (hub : u ≤ b) :
    (-3 * b + 9 * a ^ 2 - 27 / 2 * b ^ 3 ≤ P3 u ∧ P3 u ≤ -3 * a + 9 * b ^ 2 - 27 / 2 * a ^ 3) ∧
    (-3 * b + 9 * a ^ 2 - 27 / 2 * b ^ 3 - 7 * b ^ 4 - 297 / 2 * b ^ 5 ≤ P5 u ∧
      P5 u ≤ -3 * a + 9 * b ^ 2 - 27 / 2 * a ^ 3 - 7 * a ^ 4 - 297 / 2 * a ^ 5) ∧
    (-3 * b + 9 * a ^ 2 - 27 / 2 * b ^ 3 - 7 * b ^ 4 - 297 / 2 * b ^ 5 + 858827 / 10240 * a ^ 6 + 47641149 / 71680 * a ^ 7 ≤ P7 u ∧
      P7 u ≤ -3 * a + 9 * b ^ 2 - 27 / 2 * a ^ 3 - 7 * a ^ 4 - 297 / 2 * a ^ 5 + 858827 / 10240 * b ^ 6 + 47641149 / 71680 * b ^ 7) := by
  have hu : 0 ≤ u := le_trans ha hau
  have a2 := pow_le_pow_left₀ ha hau 2
  have a3 := pow_le_pow_left₀ ha hau 3
  have a4 := pow_le_pow_left₀ ha hau 4
  have a5 := pow_le_pow_left₀ ha hau 5
  have a6 := pow_le_pow_left₀ ha hau 6
  have a7 := pow_le_pow_left₀ ha hau 7
  have b2 := pow_le_pow_left₀ hu hub 2
  have b3 := pow_le_pow_left₀ hu hub 3
  have b4 := pow_le_pow_left₀ hu hub 4
  have b5 := pow_le_pow_left₀ hu hub 5
  have b6 := pow_le_pow_left₀ hu hub 6
  have b7 := pow_le_pow_left₀ hu hub 7
  unfold P7 P5 P3
  refine ⟨⟨by linarith, by linarith⟩, ⟨by linarith, by linarith⟩, ⟨by linarith, by linarith⟩⟩

/-- A bracket of `ratio u P` from brackets `Llo ≤ −log u ≤ Lhi` and `Plo ≤ P ≤ Phi` and rational square-root ends
`slo² < Llo`, `Lhi < shi²`. -/
theorem ratio_bracket_Icc (u P Llo Lhi Plo Phi slo shi lo hi : ℝ) (hL : Llo ≤ -log u ∧ -log u ≤ Lhi)
    (hPb : Plo ≤ P ∧ P ≤ Phi) (hslo : 0 < slo) (hs1 : slo ^ 2 < Llo) (hshi : 0 < shi) (hs2 : Lhi < shi ^ 2)
    (hP : 0 < 4 * Llo + Plo) (hlo : lo ≤ (4 * Llo + Plo) / shi) (hhi : (4 * Lhi + Phi) / slo ≤ hi) :
    lo ≤ ratio u P ∧ ratio u P ≤ hi := by
  have hs_lo : slo < √(-log u) := by rw [lt_sqrt hslo.le]; linarith [hL.1]
  have hs_hi : √(-log u) < shi := by rw [sqrt_lt' hshi]; linarith [hL.2]
  have hspos : 0 < √(-log u) := lt_trans hslo hs_lo
  have hnum : 0 < 4 * (-log u) + P := by linarith [hL.1, hPb.1]
  unfold ratio
  constructor
  · refine le_trans hlo ?_
    rw [div_le_div_iff₀ hshi hspos]
    nlinarith [mul_nonneg hP.le (sub_nonneg.2 hs_hi.le),
      mul_nonneg (by linarith [hL.1, hPb.1] : (0 : ℝ) ≤ 4 * (-log u) + P - (4 * Llo + Plo)) hshi.le]
  · refine le_trans ?_ hhi
    rw [div_le_div_iff₀ hspos hslo]
    nlinarith [mul_nonneg hnum.le (sub_nonneg.2 hs_lo.le),
      mul_nonneg (by linarith [hL.2, hPb.2] : (0 : ℝ) ≤ 4 * Lhi + Phi - (4 * (-log u) + P)) hspos.le]

set_option maxHeartbeats 4000000 in
/-- The series bracket of `log (0.04646)` after `12` terms, mantissa `2^4`. -/
theorem logb_cell9a : (-0.2965748555 : ℝ) - 4 * log 2 ≤ log (0.04646) ∧ log (0.04646) ≤ (-0.296574799 : ℝ) - 4 * log 2 := by
  simpa using log_mantissa_bracket (0.04646) 4 12 (-0.2965748555 : ℝ) (-0.296574799 : ℝ) (by norm_num) (by norm_num)
    (by norm_num [sum_range_succ]) (by norm_num [sum_range_succ])

set_option maxHeartbeats 4000000 in
/-- The series bracket of `log (0.04647)` after `12` terms, mantissa `2^4`. -/
theorem logb_cell9b : (-0.2963596395 : ℝ) - 4 * log 2 ≤ log (0.04647) ∧ log (0.04647) ≤ (-0.2963595835 : ℝ) - 4 * log 2 := by
  simpa using log_mantissa_bracket (0.04647) 4 12 (-0.2963596395 : ℝ) (-0.2963595835 : ℝ) (by norm_num) (by norm_num)
    (by norm_num [sum_range_succ]) (by norm_num [sum_range_succ])

set_option maxHeartbeats 4000000 in
/-- The series bracket of `log (0.08423)` after `14` terms, mantissa `2^3`. -/
theorem logb_cell8a : (-0.3947626548 : ℝ) - 3 * log 2 ≤ log (0.08423) ∧ log (0.08423) ≤ (-0.3947625055 : ℝ) - 3 * log 2 := by
  simpa using log_mantissa_bracket (0.08423) 3 14 (-0.3947626548 : ℝ) (-0.3947625055 : ℝ) (by norm_num) (by norm_num)
    (by norm_num [sum_range_succ]) (by norm_num [sum_range_succ])

set_option maxHeartbeats 4000000 in
/-- The series bracket of `log (0.08424)` after `14` terms, mantissa `2^3`. -/
theorem logb_cell8b : (-0.3946439391 : ℝ) - 3 * log 2 ≤ log (0.08424) ∧ log (0.08424) ≤ (-0.3946437903 : ℝ) - 3 * log 2 := by
  simpa using log_mantissa_bracket (0.08424) 3 14 (-0.3946439391 : ℝ) (-0.3946437903 : ℝ) (by norm_num) (by norm_num)
    (by norm_num [sum_range_succ]) (by norm_num [sum_range_succ])

set_option maxHeartbeats 4000000 in
/-- The series bracket of `log (0.12461)` after `2` terms, mantissa `2^3`. -/
theorem logb_cell7a : (-0.0031248977 : ℝ) - 3 * log 2 ≤ log (0.12461) ∧ log (0.12461) ≤ (-0.0031248367 : ℝ) - 3 * log 2 := by
  simpa using log_mantissa_bracket (0.12461) 3 2 (-0.0031248977 : ℝ) (-0.0031248367 : ℝ) (by norm_num) (by norm_num)
    (by norm_num [sum_range_succ]) (by norm_num [sum_range_succ])

set_option maxHeartbeats 4000000 in
/-- The series bracket of `log (0.12462)` after `2` terms, mantissa `2^3`. -/
theorem logb_cell7b : (-0.003044649 : ℝ) - 3 * log 2 ≤ log (0.12462) ∧ log (0.12462) ≤ (-0.0030445926 : ℝ) - 3 * log 2 := by
  simpa using log_mantissa_bracket (0.12462) 3 2 (-0.003044649 : ℝ) (-0.0030445926 : ℝ) (by norm_num) (by norm_num)
    (by norm_num [sum_range_succ]) (by norm_num [sum_range_succ])

set_option maxHeartbeats 4000000 in
/-- The series bracket of `log (0.16707)` after `14` terms, mantissa `2^2`. -/
theorem logb_cell6a : (-0.4030481223 : ℝ) - 2 * log 2 ≤ log (0.16707) ∧ log (0.16707) ≤ (-0.4030479283 : ℝ) - 2 * log 2 := by
  simpa using log_mantissa_bracket (0.16707) 2 14 (-0.4030481223 : ℝ) (-0.4030479283 : ℝ) (by norm_num) (by norm_num)
    (by norm_num [sum_range_succ]) (by norm_num [sum_range_succ])

set_option maxHeartbeats 4000000 in
/-- The series bracket of `log (0.16708)` after `14` terms, mantissa `2^2`. -/
theorem logb_cell6b : (-0.4029882688 : ℝ) - 2 * log 2 ≤ log (0.16708) ∧ log (0.16708) ≤ (-0.4029880751 : ℝ) - 2 * log 2 := by
  simpa using log_mantissa_bracket (0.16708) 2 14 (-0.4029882688 : ℝ) (-0.4029880751 : ℝ) (by norm_num) (by norm_num)
    (by norm_num [sum_range_succ]) (by norm_num [sum_range_succ])

set_option maxHeartbeats 4000000 in
/-- The series bracket of `log (0.25528)` after `23` terms, mantissa `2^1`. -/
theorem logb_cell4a : (-0.6722471836 : ℝ) - log 2 ≤ log (0.25528) ∧ log (0.25528) ≤ (-0.6722470436 : ℝ) - log 2 := by
  simpa using log_mantissa_bracket (0.25528) 1 23 (-0.6722471836 : ℝ) (-0.6722470436 : ℝ) (by norm_num) (by norm_num)
    (by norm_num [sum_range_succ]) (by norm_num [sum_range_succ])

set_option maxHeartbeats 4000000 in
/-- The series bracket of `log (0.2553)` after `23` terms, mantissa `2^1`. -/
theorem logb_cell4b : (-0.6721688412 : ℝ) - log 2 ≤ log (0.2553) ∧ log (0.2553) ≤ (-0.6721687015 : ℝ) - log 2 := by
  simpa using log_mantissa_bracket (0.2553) 1 23 (-0.6721688412 : ℝ) (-0.6721687015 : ℝ) (by norm_num) (by norm_num)
    (by norm_num [sum_range_succ]) (by norm_num [sum_range_succ])

set_option maxHeartbeats 4000000 in
/-- The series bracket of `log (0.29938)` after `18` terms, mantissa `2^1`. -/
theorem logb_cell3a : (-0.5128944752 : ℝ) - log 2 ≤ log (0.29938) ∧ log (0.29938) ≤ (-0.5128943777 : ℝ) - log 2 := by
  simpa using log_mantissa_bracket (0.29938) 1 18 (-0.5128944752 : ℝ) (-0.5128943777 : ℝ) (by norm_num) (by norm_num)
    (by norm_num [sum_range_succ]) (by norm_num [sum_range_succ])

set_option maxHeartbeats 4000000 in
/-- The series bracket of `log (0.29939)` after `18` terms, mantissa `2^1`. -/
theorem logb_cell3b : (-0.5128610733 : ℝ) - log 2 ≤ log (0.29939) ∧ log (0.29939) ≤ (-0.512860976 : ℝ) - log 2 := by
  simpa using log_mantissa_bracket (0.29939) 1 18 (-0.5128610733 : ℝ) (-0.512860976 : ℝ) (by norm_num) (by norm_num)
    (by norm_num [sum_range_succ]) (by norm_num [sum_range_succ])

set_option maxHeartbeats 4000000 in
/-- The series bracket of `log (0.34254)` after `14` terms, mantissa `2^1`. -/
theorem logb_cell2a : (-0.3782196998 : ℝ) - log 2 ≤ log (0.34254) ∧ log (0.34254) ≤ (-0.378219613 : ℝ) - log 2 := by
  simpa using log_mantissa_bracket (0.34254) 1 14 (-0.3782196998 : ℝ) (-0.378219613 : ℝ) (by norm_num) (by norm_num)
    (by norm_num [sum_range_succ]) (by norm_num [sum_range_succ])

set_option maxHeartbeats 4000000 in
/-- The series bracket of `log (0.34255)` after `14` terms, mantissa `2^1`. -/
theorem logb_cell2b : (-0.3781905065 : ℝ) - log 2 ≤ log (0.34255) ∧ log (0.34255) ≤ (-0.3781904198 : ℝ) - log 2 := by
  simpa using log_mantissa_bracket (0.34255) 1 14 (-0.3781905065 : ℝ) (-0.3781904198 : ℝ) (by norm_num) (by norm_num)
    (by norm_num [sum_range_succ]) (by norm_num [sum_range_succ])

set_option maxHeartbeats 4000000 in
/-- The series bracket of `log (23 / 54)` after `8` terms, mantissa `2^1`. -/
theorem logb_cell0a : (-0.1603426861 : ℝ) - log 2 ≤ log (23 / 54) ∧ log (23 / 54) ≤ (-0.1603426053 : ℝ) - log 2 := by
  simpa using log_mantissa_bracket (23 / 54) 1 8 (-0.1603426861 : ℝ) (-0.1603426053 : ℝ) (by norm_num) (by norm_num)
    (by norm_num [sum_range_succ]) (by norm_num [sum_range_succ])

set_option maxHeartbeats 1000000 in
/-- The cell `n = 9`: the stiffness lies in `[0.13089728, 0.130897846]`, `u` in `[0.04646, 0.04647]`, and the orders `3`, `5`, `7` in the stated brackets. -/
theorem cell9_ratios :
    ((6.93 : ℝ) ≤ ratio (cellU 9) (P3 (cellU 9)) ∧ ratio (cellU 9) (P3 (cellU 9)) ≤ (6.94 : ℝ)) ∧
    ((6.93 : ℝ) ≤ ratio (cellU 9) (P5 (cellU 9)) ∧ ratio (cellU 9) (P5 (cellU 9)) ≤ (6.94 : ℝ)) ∧
    ((6.93 : ℝ) ≤ ratio (cellU 9) (P7 (cellU 9)) ∧ ratio (cellU 9) (P7 (cellU 9)) ≤ (6.94 : ℝ)) := by
  have hθ : (0.13089728 : ℝ) ≤ cellStiffness 9 ∧ cellStiffness 9 ≤ (0.130897846 : ℝ) := by
    have h := cellStiffness_bracket 9
    push_cast at h
    constructor <;> linarith [h.1, h.2]
  have hc := c3terms_bracket (cellStiffness 9) (0.13089728 : ℝ) (0.130897846 : ℝ) (by norm_num) hθ.1 hθ.2
  have hu : (0.04646 : ℝ) ≤ cellU 9 ∧ cellU 9 ≤ (0.04647 : ℝ) := by
    unfold cellU
    constructor
    · refine le_trans ?_ hc.1; norm_num
    · refine le_trans hc.2 ?_; norm_num
  have hua : (0 : ℝ) < 0.04646 := by norm_num
  have hla := Real.log_le_log hua hu.1
  have hlb := Real.log_le_log (lt_of_lt_of_le hua hu.1) hu.2
  have hl1 := log_two_gt_d9
  have hl2 := log_two_lt_d9
  have hA := logb_cell9a
  have hB := logb_cell9b
  have hL : (3.0689483047 : ℝ) ≤ -log (cellU 9) ∧ -log (cellU 9) ≤ (3.0691635787 : ℝ) := by
    constructor <;> linarith [hA.1, hA.2, hB.1, hB.2]
  have hP := P_bracket (cellU 9) (0.04646 : ℝ) (0.04647 : ℝ) (by norm_num) hu.1 hu.2
  have hP3 : (-0.1213379426 : ℝ) ≤ P3 (cellU 9) ∧ P3 (cellU 9) ≤ (-0.1212987045 : ℝ) := by
    constructor
    · refine le_trans ?_ hP.1.1; norm_num
    · refine le_trans hP.1.2 ?_; norm_num
  have hr3 := ratio_bracket_Icc (cellU 9) (P3 (cellU 9)) (3.0689483047 : ℝ) (3.0691635787 : ℝ) (-0.1213379426 : ℝ) (-0.1212987045 : ℝ) (1.7518413 : ℝ) (1.751903 : ℝ) (6.93 : ℝ) (6.94 : ℝ) hL hP3
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have hP5 : (-0.1214027658 : ℝ) ≤ P5 (cellU 9) ∧ P5 (cellU 9) ≤ (-0.1213634649 : ℝ) := by
    constructor
    · refine le_trans ?_ hP.2.1.1; norm_num
    · refine le_trans hP.2.1.2 ?_; norm_num
  have hr5 := ratio_bracket_Icc (cellU 9) (P5 (cellU 9)) (3.0689483047 : ℝ) (3.0691635787 : ℝ) (-0.1214027658 : ℝ) (-0.1213634649 : ℝ) (1.7518413 : ℝ) (1.751903 : ℝ) (6.93 : ℝ) (6.94 : ℝ) hL hP5
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have hP7 : (-0.1214016118 : ℝ) ≤ P7 (cellU 9) ∧ P7 (cellU 9) ≤ (-0.1213623093 : ℝ) := by
    constructor
    · refine le_trans ?_ hP.2.2.1; norm_num
    · refine le_trans hP.2.2.2 ?_; norm_num
  have hr7 := ratio_bracket_Icc (cellU 9) (P7 (cellU 9)) (3.0689483047 : ℝ) (3.0691635787 : ℝ) (-0.1214016118 : ℝ) (-0.1213623093 : ℝ) (1.7518413 : ℝ) (1.751903 : ℝ) (6.93 : ℝ) (6.94 : ℝ) hL hP7
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  exact ⟨hr3, hr5, hr7⟩

set_option maxHeartbeats 1000000 in
/-- The cell `n = 8`: the stiffness lies in `[0.227464249, 0.227464752]`, `u` in `[0.08423, 0.08424]`, and the orders `3`, `5`, `7` in the stated brackets. -/
theorem cell8_ratios :
    ((6.16 : ℝ) ≤ ratio (cellU 8) (P3 (cellU 8)) ∧ ratio (cellU 8) (P3 (cellU 8)) ≤ (6.17 : ℝ)) ∧
    ((6.16 : ℝ) ≤ ratio (cellU 8) (P5 (cellU 8)) ∧ ratio (cellU 8) (P5 (cellU 8)) ≤ (6.17 : ℝ)) ∧
    ((6.16 : ℝ) ≤ ratio (cellU 8) (P7 (cellU 8)) ∧ ratio (cellU 8) (P7 (cellU 8)) ≤ (6.17 : ℝ)) := by
  have hθ : (0.227464249 : ℝ) ≤ cellStiffness 8 ∧ cellStiffness 8 ≤ (0.227464752 : ℝ) := by
    have h := cellStiffness_bracket 8
    push_cast at h
    constructor <;> linarith [h.1, h.2]
  have hc := c3terms_bracket (cellStiffness 8) (0.227464249 : ℝ) (0.227464752 : ℝ) (by norm_num) hθ.1 hθ.2
  have hu : (0.08423 : ℝ) ≤ cellU 8 ∧ cellU 8 ≤ (0.08424 : ℝ) := by
    unfold cellU
    constructor
    · refine le_trans ?_ hc.1; norm_num
    · refine le_trans hc.2 ?_; norm_num
  have hua : (0 : ℝ) < 0.08423 := by norm_num
  have hla := Real.log_le_log hua hu.1
  have hlb := Real.log_le_log (lt_of_lt_of_le hua hu.1) hu.2
  have hl1 := log_two_gt_d9
  have hl2 := log_two_lt_d9
  have hA := logb_cell8a
  have hB := logb_cell8b
  have hL : (2.4740853312 : ℝ) ≤ -log (cellU 8) ∧ -log (cellU 8) ≤ (2.4742041972 : ℝ) := by
    constructor <;> linarith [hA.1, hA.2, hB.1, hB.2]
  have hP := P_bracket (cellU 8) (0.08423 : ℝ) (0.08424 : ℝ) (by norm_num) hu.1 hu.2
  have hP3 : (-0.1969380484 : ℝ) ≤ P3 (cellU 8) ∧ P3 (cellU 8) ≤ (-0.1968900123 : ℝ) := by
    constructor
    · refine le_trans ?_ hP.1.1; norm_num
    · refine le_trans hP.1.2 ?_; norm_num
  have hr3 := ratio_bracket_Icc (cellU 8) (P3 (cellU 8)) (2.4740853312 : ℝ) (2.4742041972 : ℝ) (-0.1969380484 : ℝ) (-0.1968900123 : ℝ) (1.5729224 : ℝ) (1.5729605 : ℝ) (6.16 : ℝ) (6.17 : ℝ) hL hP3
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have hP5 : (-0.1979205261 : ℝ) ≤ P5 (cellU 8) ∧ P5 (cellU 8) ≤ (-0.1978719488 : ℝ) := by
    constructor
    · refine le_trans ?_ hP.2.1.1; norm_num
    · refine le_trans hP.2.1.2 ?_; norm_num
  have hr5 := ratio_bracket_Icc (cellU 8) (P5 (cellU 8)) (2.4740853312 : ℝ) (2.4742041972 : ℝ) (-0.1979205261 : ℝ) (-0.1978719488 : ℝ) (1.5729224 : ℝ) (1.5729605 : ℝ) (6.16 : ℝ) (6.17 : ℝ) hL hP5
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have hP7 : (-0.1978705836 : ℝ) ≤ P7 (cellU 8) ∧ P7 (cellU 8) ≤ (-0.1978219684 : ℝ) := by
    constructor
    · refine le_trans ?_ hP.2.2.1; norm_num
    · refine le_trans hP.2.2.2 ?_; norm_num
  have hr7 := ratio_bracket_Icc (cellU 8) (P7 (cellU 8)) (2.4740853312 : ℝ) (2.4742041972 : ℝ) (-0.1978705836 : ℝ) (-0.1978219684 : ℝ) (1.5729224 : ℝ) (1.5729605 : ℝ) (6.16 : ℝ) (6.17 : ℝ) hL hP7
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  exact ⟨hr3, hr5, hr7⟩

set_option maxHeartbeats 1000000 in
/-- The cell `n = 7`: the stiffness lies in `[0.324031218, 0.324031658]`, `u` in `[0.12461, 0.12462]`, and the orders `3`, `5`, `7` in the stated brackets. -/
theorem cell7_ratios :
    ((5.59 : ℝ) ≤ ratio (cellU 7) (P3 (cellU 7)) ∧ ratio (cellU 7) (P3 (cellU 7)) ≤ (5.6 : ℝ)) ∧
    ((5.58 : ℝ) ≤ ratio (cellU 7) (P5 (cellU 7)) ∧ ratio (cellU 7) (P5 (cellU 7)) ≤ (5.59 : ℝ)) ∧
    ((5.58 : ℝ) ≤ ratio (cellU 7) (P7 (cellU 7)) ∧ ratio (cellU 7) (P7 (cellU 7)) ≤ (5.59 : ℝ)) := by
  have hθ : (0.324031218 : ℝ) ≤ cellStiffness 7 ∧ cellStiffness 7 ≤ (0.324031658 : ℝ) := by
    have h := cellStiffness_bracket 7
    push_cast at h
    constructor <;> linarith [h.1, h.2]
  have hc := c3terms_bracket (cellStiffness 7) (0.324031218 : ℝ) (0.324031658 : ℝ) (by norm_num) hθ.1 hθ.2
  have hu : (0.12461 : ℝ) ≤ cellU 7 ∧ cellU 7 ≤ (0.12462 : ℝ) := by
    unfold cellU
    constructor
    · refine le_trans ?_ hc.1; norm_num
    · refine le_trans hc.2 ?_; norm_num
  have hua : (0 : ℝ) < 0.12461 := by norm_num
  have hla := Real.log_le_log hua hu.1
  have hlb := Real.log_le_log (lt_of_lt_of_le hua hu.1) hu.2
  have hl1 := log_two_gt_d9
  have hl2 := log_two_lt_d9
  have hA := logb_cell7a
  have hB := logb_cell7b
  have hL : (2.0824861335 : ℝ) ≤ -log (cellU 7) ∧ -log (cellU 7) ≤ (2.0825664401 : ℝ) := by
    constructor <;> linarith [hA.1, hA.2, hB.1, hB.2]
  have hP := P_bracket (cellU 7) (0.12461 : ℝ) (0.12462 : ℝ) (by norm_num) hu.1 hu.2
  have hP3 : (-0.2602385802 : ℝ) ≤ P3 (cellU 7) ∧ P3 (cellU 7) ≤ (-0.2601798602 : ℝ) := by
    constructor
    · refine le_trans ?_ hP.1.1; norm_num
    · refine le_trans hP.1.2 ?_; norm_num
  have hr3 := ratio_bracket_Icc (cellU 7) (P3 (cellU 7)) (2.0824861335 : ℝ) (2.0825664401 : ℝ) (-0.2602385802 : ℝ) (-0.2601798602 : ℝ) (1.443082 : ℝ) (1.4431101 : ℝ) (5.59 : ℝ) (5.6 : ℝ) hL hP3
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have hP5 : (-0.2663902715 : ℝ) ≤ P5 (cellU 7) ∧ P5 (cellU 7) ≤ (-0.2663292191 : ℝ) := by
    constructor
    · refine le_trans ?_ hP.2.1.1; norm_num
    · refine le_trans hP.2.1.2 ?_; norm_num
  have hr5 := ratio_bracket_Icc (cellU 7) (P5 (cellU 7)) (2.0824861335 : ℝ) (2.0825664401 : ℝ) (-0.2663902715 : ℝ) (-0.2663292191 : ℝ) (1.443082 : ℝ) (1.4431101 : ℝ) (5.58 : ℝ) (5.59 : ℝ) hL hP5
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have hP7 : (-0.26576621 : ℝ) ≤ P7 (cellU 7) ∧ P7 (cellU 7) ≤ (-0.2657048322 : ℝ) := by
    constructor
    · refine le_trans ?_ hP.2.2.1; norm_num
    · refine le_trans hP.2.2.2 ?_; norm_num
  have hr7 := ratio_bracket_Icc (cellU 7) (P7 (cellU 7)) (2.0824861335 : ℝ) (2.0825664401 : ℝ) (-0.26576621 : ℝ) (-0.2657048322 : ℝ) (1.443082 : ℝ) (1.4431101 : ℝ) (5.58 : ℝ) (5.59 : ℝ) hL hP7
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  exact ⟨hr3, hr5, hr7⟩

set_option maxHeartbeats 1000000 in
/-- The cell `n = 6`: the stiffness lies in `[0.420598187, 0.420598564]`, `u` in `[0.16707, 0.16708]`, and the orders `3`, `5`, `7` in the stated brackets. -/
theorem cell6_ratios :
    ((5.11 : ℝ) ≤ ratio (cellU 6) (P3 (cellU 6)) ∧ ratio (cellU 6) (P3 (cellU 6)) ≤ (5.12 : ℝ)) ∧
    ((5.09 : ℝ) ≤ ratio (cellU 6) (P5 (cellU 6)) ∧ ratio (cellU 6) (P5 (cellU 6)) ≤ (5.1 : ℝ)) ∧
    ((5.1 : ℝ) ≤ ratio (cellU 6) (P7 (cellU 6)) ∧ ratio (cellU 6) (P7 (cellU 6)) ≤ (5.11 : ℝ)) := by
  have hθ : (0.420598187 : ℝ) ≤ cellStiffness 6 ∧ cellStiffness 6 ≤ (0.420598564 : ℝ) := by
    have h := cellStiffness_bracket 6
    push_cast at h
    constructor <;> linarith [h.1, h.2]
  have hc := c3terms_bracket (cellStiffness 6) (0.420598187 : ℝ) (0.420598564 : ℝ) (by norm_num) hθ.1 hθ.2
  have hu : (0.16707 : ℝ) ≤ cellU 6 ∧ cellU 6 ≤ (0.16708 : ℝ) := by
    unfold cellU
    constructor
    · refine le_trans ?_ hc.1; norm_num
    · refine le_trans hc.2 ?_; norm_num
  have hua : (0 : ℝ) < 0.16707 := by norm_num
  have hla := Real.log_le_log hua hu.1
  have hlb := Real.log_le_log (lt_of_lt_of_le hua hu.1) hu.2
  have hl1 := log_two_gt_d9
  have hl2 := log_two_lt_d9
  have hA := logb_cell6a
  have hB := logb_cell6b
  have hL : (1.7892824357 : ℝ) ≤ -log (cellU 6) ∧ -log (cellU 6) ≤ (1.7893424839 : ℝ) := by
    constructor <;> linarith [hA.1, hA.2, hB.1, hB.2]
  have hP := P_bracket (cellU 6) (0.16707 : ℝ) (0.16708 : ℝ) (by norm_num) hu.1 hu.2
  have hP3 : (-0.3129946901 : ℝ) ≤ P3 (cellU 6) ∧ P3 (cellU 6) ≤ (-0.3129233113 : ℝ) := by
    constructor
    · refine le_trans ?_ hP.1.1; norm_num
    · refine le_trans hP.1.2 ?_; norm_num
  have hr3 := ratio_bracket_Icc (cellU 6) (P3 (cellU 6)) (1.7892824357 : ℝ) (1.7893424839 : ℝ) (-0.3129946901 : ℝ) (-0.3129233113 : ℝ) (1.3376405 : ℝ) (1.3376632 : ℝ) (5.11 : ℝ) (5.12 : ℝ) hL hP3
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have hP5 : (-0.3377849098 : ℝ) ≤ P5 (cellU 6) ∧ P5 (cellU 6) ≤ (-0.3377064397 : ℝ) := by
    constructor
    · refine le_trans ?_ hP.2.1.1; norm_num
    · refine le_trans hP.2.1.2 ?_; norm_num
  have hr5 := ratio_bracket_Icc (cellU 6) (P5 (cellU 6)) (1.7892824357 : ℝ) (1.7893424839 : ℝ) (-0.3377849098 : ℝ) (-0.3377064397 : ℝ) (1.3376405 : ℝ) (1.3376632 : ℝ) (5.09 : ℝ) (5.1 : ℝ) hL hP5
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have hP7 : (-0.3335462709 : ℝ) ≤ P7 (cellU 6) ∧ P7 (cellU 6) ≤ (-0.3334661337 : ℝ) := by
    constructor
    · refine le_trans ?_ hP.2.2.1; norm_num
    · refine le_trans hP.2.2.2 ?_; norm_num
  have hr7 := ratio_bracket_Icc (cellU 6) (P7 (cellU 6)) (1.7892824357 : ℝ) (1.7893424839 : ℝ) (-0.3335462709 : ℝ) (-0.3334661337 : ℝ) (1.3376405 : ℝ) (1.3376632 : ℝ) (5.1 : ℝ) (5.11 : ℝ) hL hP7
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  exact ⟨hr3, hr5, hr7⟩

set_option maxHeartbeats 1000000 in
/-- The cell `n = 4`: the stiffness lies in `[0.613732124, 0.613732376]`, `u` in `[0.25528, 0.2553]`, and the orders `3`, `5`, `7` in the stated brackets. -/
theorem cell4_ratios :
    ((4.32 : ℝ) ≤ ratio (cellU 4) (P3 (cellU 4)) ∧ ratio (cellU 4) (P3 (cellU 4)) ≤ (4.33 : ℝ)) ∧
    ((4.16 : ℝ) ≤ ratio (cellU 4) (P5 (cellU 4)) ∧ ratio (cellU 4) (P5 (cellU 4)) ≤ (4.17 : ℝ)) ∧
    ((4.22 : ℝ) ≤ ratio (cellU 4) (P7 (cellU 4)) ∧ ratio (cellU 4) (P7 (cellU 4)) ≤ (4.23 : ℝ)) := by
  have hθ : (0.613732124 : ℝ) ≤ cellStiffness 4 ∧ cellStiffness 4 ≤ (0.613732376 : ℝ) := by
    have h := cellStiffness_bracket 4
    push_cast at h
    constructor <;> linarith [h.1, h.2]
  have hc := c3terms_bracket (cellStiffness 4) (0.613732124 : ℝ) (0.613732376 : ℝ) (by norm_num) hθ.1 hθ.2
  have hu : (0.25528 : ℝ) ≤ cellU 4 ∧ cellU 4 ≤ (0.2553 : ℝ) := by
    unfold cellU
    constructor
    · refine le_trans ?_ hc.1; norm_num
    · refine le_trans hc.2 ?_; norm_num
  have hua : (0 : ℝ) < 0.25528 := by norm_num
  have hla := Real.log_le_log hua hu.1
  have hlb := Real.log_le_log (lt_of_lt_of_le hua hu.1) hu.2
  have hl1 := log_two_gt_d9
  have hl2 := log_two_lt_d9
  have hA := logb_cell4a
  have hB := logb_cell4b
  have hL : (1.3653158818 : ℝ) ≤ -log (cellU 4) ∧ -log (cellU 4) ≤ (1.3653943644 : ℝ) := by
    constructor <;> linarith [hA.1, hA.2, hB.1, hB.2]
  have hP := P_bracket (cellU 4) (0.25528 : ℝ) (0.2553 : ℝ) (by norm_num) hu.1 hu.2
  have hP3 : (-0.4040286405 : ℝ) ≤ P3 (cellU 4) ∧ P3 (cellU 4) ≤ (-0.4038239459 : ℝ) := by
    constructor
    · refine le_trans ?_ hP.1.1; norm_num
    · refine le_trans hP.1.2 ?_; norm_num
  have hr3 := ratio_bracket_Icc (cellU 4) (P3 (cellU 4)) (1.3653158818 : ℝ) (1.3653943644 : ℝ) (-0.4040286405 : ℝ) (-0.4038239459 : ℝ) (1.1684672 : ℝ) (1.1685011 : ℝ) (4.32 : ℝ) (4.33 : ℝ) hL hP3
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have hP5 : (-0.5948232665 : ℝ) ≤ P5 (cellU 4) ∧ P5 (cellU 4) ≤ (-0.594546179 : ℝ) := by
    constructor
    · refine le_trans ?_ hP.2.1.1; norm_num
    · refine le_trans hP.2.1.2 ?_; norm_num
  have hr5 := ratio_bracket_Icc (cellU 4) (P5 (cellU 4)) (1.3653158818 : ℝ) (1.3653943644 : ℝ) (-0.5948232665 : ℝ) (-0.594546179 : ℝ) (1.1684672 : ℝ) (1.1685011 : ℝ) (4.16 : ℝ) (4.17 : ℝ) hL hP5
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have hP7 : (-0.5246544374 : ℝ) ≤ P7 (cellU 4) ∧ P7 (cellU 4) ≤ (-0.5243406784 : ℝ) := by
    constructor
    · refine le_trans ?_ hP.2.2.1; norm_num
    · refine le_trans hP.2.2.2 ?_; norm_num
  have hr7 := ratio_bracket_Icc (cellU 4) (P7 (cellU 4)) (1.3653158818 : ℝ) (1.3653943644 : ℝ) (-0.5246544374 : ℝ) (-0.5243406784 : ℝ) (1.1684672 : ℝ) (1.1685011 : ℝ) (4.22 : ℝ) (4.23 : ℝ) hL hP7
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  exact ⟨hr3, hr5, hr7⟩

set_option maxHeartbeats 1000000 in
/-- The cell `n = 3`: the stiffness lies in `[0.710299093, 0.710299282]`, `u` in `[0.29938, 0.29939]`, and the orders `3`, `5`, `7` in the stated brackets. -/
theorem cell3_ratios :
    ((3.97 : ℝ) ≤ ratio (cellU 3) (P3 (cellU 3)) ∧ ratio (cellU 3) (P3 (cellU 3)) ≤ (3.98 : ℝ)) ∧
    ((3.6 : ℝ) ≤ ratio (cellU 3) (P5 (cellU 3)) ∧ ratio (cellU 3) (P5 (cellU 3)) ≤ (3.61 : ℝ)) ∧
    ((3.78 : ℝ) ≤ ratio (cellU 3) (P7 (cellU 3)) ∧ ratio (cellU 3) (P7 (cellU 3)) ≤ (3.79 : ℝ)) := by
  have hθ : (0.710299093 : ℝ) ≤ cellStiffness 3 ∧ cellStiffness 3 ≤ (0.710299282 : ℝ) := by
    have h := cellStiffness_bracket 3
    push_cast at h
    constructor <;> linarith [h.1, h.2]
  have hc := c3terms_bracket (cellStiffness 3) (0.710299093 : ℝ) (0.710299282 : ℝ) (by norm_num) hθ.1 hθ.2
  have hu : (0.29938 : ℝ) ≤ cellU 3 ∧ cellU 3 ≤ (0.29939 : ℝ) := by
    unfold cellU
    constructor
    · refine le_trans ?_ hc.1; norm_num
    · refine le_trans hc.2 ?_; norm_num
  have hua : (0 : ℝ) < 0.29938 := by norm_num
  have hla := Real.log_le_log hua hu.1
  have hlb := Real.log_le_log (lt_of_lt_of_le hua hu.1) hu.2
  have hl1 := log_two_gt_d9
  have hl2 := log_two_lt_d9
  have hA := logb_cell3a
  have hB := logb_cell3b
  have hL : (1.2060081563 : ℝ) ≤ -log (cellU 3) ∧ -log (cellU 3) ≤ (1.206041656 : ℝ) := by
    constructor <;> linarith [hA.1, hA.2, hB.1, hB.2]
  have hP := P_bracket (cellU 3) (0.29938 : ℝ) (0.29939 : ℝ) (by norm_num) hu.1 hu.2
  have hP3 : (-0.4537956084 : ℝ) ≤ P3 (cellU 3) ∧ P3 (cellU 3) ≤ (-0.4536754183 : ℝ) := by
    constructor
    · refine le_trans ?_ hP.1.1; norm_num
    · refine le_trans hP.1.2 ?_; norm_num
  have hr3 := ratio_bracket_Icc (cellU 3) (P3 (cellU 3)) (1.2060081563 : ℝ) (1.206041656 : ℝ) (-0.4537956084 : ℝ) (-0.4536754183 : ℝ) (1.0981839 : ℝ) (1.0981994 : ℝ) (3.97 : ℝ) (3.98 : ℝ) hL hP3
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have hP5 : (-0.8672370496 : ℝ) ≤ P5 (cellU 3) ∧ P5 (cellU 3) ≤ (-0.867049695 : ℝ) := by
    constructor
    · refine le_trans ?_ hP.2.1.1; norm_num
    · refine le_trans hP.2.1.2 ?_; norm_num
  have hr5 := ratio_bracket_Icc (cellU 3) (P5 (cellU 3)) (1.2060081563 : ℝ) (1.206041656 : ℝ) (-0.8672370496 : ℝ) (-0.867049695 : ℝ) (1.0981839 : ℝ) (1.0981994 : ℝ) (3.6 : ℝ) (3.61 : ℝ) hL hP5
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have hP7 : (-0.6635839986 : ℝ) ≤ P7 (cellU 3) ∧ P7 (cellU 3) ≤ (-0.6633510393 : ℝ) := by
    constructor
    · refine le_trans ?_ hP.2.2.1; norm_num
    · refine le_trans hP.2.2.2 ?_; norm_num
  have hr7 := ratio_bracket_Icc (cellU 3) (P7 (cellU 3)) (1.2060081563 : ℝ) (1.206041656 : ℝ) (-0.6635839986 : ℝ) (-0.6633510393 : ℝ) (1.0981839 : ℝ) (1.0981994 : ℝ) (3.78 : ℝ) (3.79 : ℝ) hL hP7
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  exact ⟨hr3, hr5, hr7⟩

set_option maxHeartbeats 1000000 in
/-- The cell `n = 2`: the stiffness lies in `[0.806866062, 0.806866188]`, `u` in `[0.34254, 0.34255]`, and the orders `3`, `5`, `7` in the stated brackets. -/
theorem cell2_ratios :
    ((3.64 : ℝ) ≤ ratio (cellU 2) (P3 (cellU 2)) ∧ ratio (cellU 2) (P3 (cellU 2)) ≤ (3.65 : ℝ)) ∧
    ((2.87 : ℝ) ≤ ratio (cellU 2) (P5 (cellU 2)) ∧ ratio (cellU 2) (P5 (cellU 2)) ≤ (2.88 : ℝ)) ∧
    ((3.35 : ℝ) ≤ ratio (cellU 2) (P7 (cellU 2)) ∧ ratio (cellU 2) (P7 (cellU 2)) ≤ (3.37 : ℝ)) := by
  have hθ : (0.806866062 : ℝ) ≤ cellStiffness 2 ∧ cellStiffness 2 ≤ (0.806866188 : ℝ) := by
    have h := cellStiffness_bracket 2
    push_cast at h
    constructor <;> linarith [h.1, h.2]
  have hc := c3terms_bracket (cellStiffness 2) (0.806866062 : ℝ) (0.806866188 : ℝ) (by norm_num) hθ.1 hθ.2
  have hu : (0.34254 : ℝ) ≤ cellU 2 ∧ cellU 2 ≤ (0.34255 : ℝ) := by
    unfold cellU
    constructor
    · refine le_trans ?_ hc.1; norm_num
    · refine le_trans hc.2 ?_; norm_num
  have hua : (0 : ℝ) < 0.34254 := by norm_num
  have hla := Real.log_le_log hua hu.1
  have hlb := Real.log_le_log (lt_of_lt_of_le hua hu.1) hu.2
  have hl1 := log_two_gt_d9
  have hl2 := log_two_lt_d9
  have hA := logb_cell2a
  have hB := logb_cell2b
  have hL : (1.0713376001 : ℝ) ≤ -log (cellU 2) ∧ -log (cellU 2) ≤ (1.0713668806 : ℝ) := by
    constructor <;> linarith [hA.1, hA.2, hB.1, hB.2]
  have hP := P_bracket (cellU 2) (0.34254 : ℝ) (0.34255 : ℝ) (by norm_num) hu.1 hu.2
  have hP3 : (-0.5142794889 : ℝ) ≤ P3 (cellU 2) ∧ P3 (cellU 2) ≤ (-0.5141403092 : ℝ) := by
    constructor
    · refine le_trans ?_ hP.1.1; norm_num
    · refine le_trans hP.1.2 ?_; norm_num
  have hr3 := ratio_bracket_Icc (cellU 2) (P3 (cellU 2)) (1.0713376001 : ℝ) (1.0713668806 : ℝ) (-0.5142794889 : ℝ) (-0.5141403092 : ℝ) (1.0350542 : ℝ) (1.0350687 : ℝ) (3.64 : ℝ) (3.65 : ℝ) hL hP3
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have hP5 : (-1.3110613267 : ℝ) ≤ P5 (cellU 2) ∧ P5 (cellU 2) ≤ (-1.3108086655 : ℝ) := by
    constructor
    · refine le_trans ?_ hP.2.1.1; norm_num
    · refine le_trans hP.2.1.2 ?_; norm_num
  have hr5 := ratio_bracket_Icc (cellU 2) (P5 (cellU 2)) (1.0713376001 : ℝ) (1.0713668806 : ℝ) (-1.3110613267 : ℝ) (-1.3108086655 : ℝ) (1.0350542 : ℝ) (1.0350687 : ℝ) (2.87 : ℝ) (2.88 : ℝ) hL hP5
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have hP7 : (-0.807822877 : ℝ) ≤ P7 (cellU 2) ∧ P7 (cellU 2) ≤ (-0.8074713231 : ℝ) := by
    constructor
    · refine le_trans ?_ hP.2.2.1; norm_num
    · refine le_trans hP.2.2.2 ?_; norm_num
  have hr7 := ratio_bracket_Icc (cellU 2) (P7 (cellU 2)) (1.0713376001 : ℝ) (1.0713668806 : ℝ) (-0.807822877 : ℝ) (-0.8074713231 : ℝ) (1.0350542 : ℝ) (1.0350687 : ℝ) (3.35 : ℝ) (3.37 : ℝ) hL hP7
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  exact ⟨hr3, hr5, hr7⟩

set_option maxHeartbeats 1000000 in
/-- Channel unity, the cell `n = 0`: the stiffness is `1`, the computed terms sum to `u = 23/54`, and the orders `3`, `5`, `7` lie in the stated brackets. -/
theorem cell0_ratios :
    ((2.95 : ℝ) ≤ ratio (cellU 0) (P3 (cellU 0)) ∧ ratio (cellU 0) (P3 (cellU 0)) ≤ (2.96 : ℝ)) ∧
    ((0.44 : ℝ) ≤ ratio (cellU 0) (P5 (cellU 0)) ∧ ratio (cellU 0) (P5 (cellU 0)) ≤ (0.45 : ℝ)) ∧
    ((2.81 : ℝ) ≤ ratio (cellU 0) (P7 (cellU 0)) ∧ ratio (cellU 0) (P7 (cellU 0)) ≤ (2.82 : ℝ)) := by
  have he : cellU 0 = 23 / 54 := by norm_num [cellU, cellStiffness, c3terms]
  have hu : (23 / 54 : ℝ) ≤ cellU 0 ∧ cellU 0 ≤ (23 / 54 : ℝ) := ⟨he.ge, he.le⟩
  have hua : (0 : ℝ) < 23 / 54 := by norm_num
  have hla := Real.log_le_log hua hu.1
  have hlb := Real.log_le_log (lt_of_lt_of_le hua hu.1) hu.2
  have hl1 := log_two_gt_d9
  have hl2 := log_two_lt_d9
  have hA := logb_cell0a
  have hB := logb_cell0a
  have hL : (0.8534897856 : ℝ) ≤ -log (cellU 0) ∧ -log (cellU 0) ≤ (0.8534898669 : ℝ) := by
    constructor <;> linarith [hA.1, hA.2, hB.1, hB.2]
  have hP := P_bracket (cellU 0) (23 / 54 : ℝ) (23 / 54 : ℝ) (by norm_num) hu.1 hu.2
  have hP3 : (-0.6881858711 : ℝ) ≤ P3 (cellU 0) ∧ P3 (cellU 0) ≤ (-0.688185871 : ℝ) := by
    constructor
    · refine le_trans ?_ hP.1.1; norm_num
    · refine le_trans hP.1.2 ?_; norm_num
  have hr3 := ratio_bracket_Icc (cellU 0) (P3 (cellU 0)) (0.8534897856 : ℝ) (0.8534898669 : ℝ) (-0.6881858711 : ℝ) (-0.688185871 : ℝ) (0.923845 : ℝ) (0.9238453 : ℝ) (2.95 : ℝ) (2.96 : ℝ) hL hP3
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have hP5 : (-3.0001582079 : ℝ) ≤ P5 (cellU 0) ∧ P5 (cellU 0) ≤ (-3.0001582078 : ℝ) := by
    constructor
    · refine le_trans ?_ hP.2.1.1; norm_num
    · refine le_trans hP.2.1.2 ?_; norm_num
  have hr5 := ratio_bracket_Icc (cellU 0) (P5 (cellU 0)) (0.8534897856 : ℝ) (0.8534898669 : ℝ) (-3.0001582079 : ℝ) (-3.0001582078 : ℝ) (0.923845 : ℝ) (0.9238453 : ℝ) (0.44 : ℝ) (0.45 : ℝ) hL hP5
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have hP7 : (-0.8092802977 : ℝ) ≤ P7 (cellU 0) ∧ P7 (cellU 0) ≤ (-0.8092802976 : ℝ) := by
    constructor
    · refine le_trans ?_ hP.2.2.1; norm_num
    · refine le_trans hP.2.2.2 ?_; norm_num
  have hr7 := ratio_bracket_Icc (cellU 0) (P7 (cellU 0)) (0.8534897856 : ℝ) (0.8534898669 : ℝ) (-0.8092802977 : ℝ) (-0.8092802976 : ℝ) (0.923845 : ℝ) (0.9238453 : ℝ) (2.81 : ℝ) (2.82 : ℝ) hL hP7
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  exact ⟨hr3, hr5, hr7⟩

/-- 46:C11 [chart] — **the plaquette channel at the chart's cells.** With the stiffness `ϑ_n = 1 − n · 11 ln 2/(8π²)` of the cell
`n` (46:B6), `u` the sum of the computed terms of the frame's `c₃` through `ϑ⁷` at that stiffness (46:C7), the imported series
to the orders `3`, `5`, `7` (46:A11) and the tension at leading order, `m/√σ = (−4 ln u + P)/√(−ln u)` lies, order by order, in
`(6.93, 6.94)`, `(6.93, 6.94)`, `(6.93, 6.94)` at `n = 9`,
`(6.16, 6.17)`, `(6.16, 6.17)`, `(6.16, 6.17)` at `n = 8`,
`(5.59, 5.6)`, `(5.58, 5.59)`, `(5.58, 5.59)` at `n = 7`,
`(5.11, 5.12)`, `(5.09, 5.1)`, `(5.1, 5.11)` at `n = 6`,
`(4.32, 4.33)`, `(4.16, 4.17)`, `(4.22, 4.23)` at `n = 4`,
`(3.97, 3.98)`, `(3.6, 3.61)`, `(3.78, 3.79)` at `n = 3`,
`(3.64, 3.65)`, `(2.87, 2.88)`, `(3.35, 3.37)` at `n = 2`,
and at channel unity, where `u = 23/54`, in `(2.95, 2.96)`, `(0.44, 0.45)`, `(2.81, 2.82)`.
At the cells `n = 9, 8, 7, 6` the orders `3` and `5` lie within `1 %` of the seventh; at `n = 4` the three orders lie above `3.7`;
at `n = 3` the fifth order alone lies in the lattice bracket `(3.4, 3.7)`; at `n = 2` the third order alone does. -/
theorem plaquette_cells_values :
    (cellU 0 = 23 / 54) ∧
    ((6.93 : ℝ) ≤ ratio (cellU 9) (P3 (cellU 9)) ∧ ratio (cellU 9) (P3 (cellU 9)) ≤ (6.94 : ℝ) ∧ (6.93 : ℝ) ≤ ratio (cellU 9) (P5 (cellU 9)) ∧ ratio (cellU 9) (P5 (cellU 9)) ≤ (6.94 : ℝ) ∧ (6.93 : ℝ) ≤ ratio (cellU 9) (P7 (cellU 9)) ∧ ratio (cellU 9) (P7 (cellU 9)) ≤ (6.94 : ℝ)) ∧
    ((6.16 : ℝ) ≤ ratio (cellU 8) (P3 (cellU 8)) ∧ ratio (cellU 8) (P3 (cellU 8)) ≤ (6.17 : ℝ) ∧ (6.16 : ℝ) ≤ ratio (cellU 8) (P5 (cellU 8)) ∧ ratio (cellU 8) (P5 (cellU 8)) ≤ (6.17 : ℝ) ∧ (6.16 : ℝ) ≤ ratio (cellU 8) (P7 (cellU 8)) ∧ ratio (cellU 8) (P7 (cellU 8)) ≤ (6.17 : ℝ)) ∧
    ((5.59 : ℝ) ≤ ratio (cellU 7) (P3 (cellU 7)) ∧ ratio (cellU 7) (P3 (cellU 7)) ≤ (5.6 : ℝ) ∧ (5.58 : ℝ) ≤ ratio (cellU 7) (P5 (cellU 7)) ∧ ratio (cellU 7) (P5 (cellU 7)) ≤ (5.59 : ℝ) ∧ (5.58 : ℝ) ≤ ratio (cellU 7) (P7 (cellU 7)) ∧ ratio (cellU 7) (P7 (cellU 7)) ≤ (5.59 : ℝ)) ∧
    ((5.11 : ℝ) ≤ ratio (cellU 6) (P3 (cellU 6)) ∧ ratio (cellU 6) (P3 (cellU 6)) ≤ (5.12 : ℝ) ∧ (5.09 : ℝ) ≤ ratio (cellU 6) (P5 (cellU 6)) ∧ ratio (cellU 6) (P5 (cellU 6)) ≤ (5.1 : ℝ) ∧ (5.1 : ℝ) ≤ ratio (cellU 6) (P7 (cellU 6)) ∧ ratio (cellU 6) (P7 (cellU 6)) ≤ (5.11 : ℝ)) ∧
    ((4.32 : ℝ) ≤ ratio (cellU 4) (P3 (cellU 4)) ∧ ratio (cellU 4) (P3 (cellU 4)) ≤ (4.33 : ℝ) ∧ (4.16 : ℝ) ≤ ratio (cellU 4) (P5 (cellU 4)) ∧ ratio (cellU 4) (P5 (cellU 4)) ≤ (4.17 : ℝ) ∧ (4.22 : ℝ) ≤ ratio (cellU 4) (P7 (cellU 4)) ∧ ratio (cellU 4) (P7 (cellU 4)) ≤ (4.23 : ℝ)) ∧
    ((3.97 : ℝ) ≤ ratio (cellU 3) (P3 (cellU 3)) ∧ ratio (cellU 3) (P3 (cellU 3)) ≤ (3.98 : ℝ) ∧ (3.6 : ℝ) ≤ ratio (cellU 3) (P5 (cellU 3)) ∧ ratio (cellU 3) (P5 (cellU 3)) ≤ (3.61 : ℝ) ∧ (3.78 : ℝ) ≤ ratio (cellU 3) (P7 (cellU 3)) ∧ ratio (cellU 3) (P7 (cellU 3)) ≤ (3.79 : ℝ)) ∧
    ((3.64 : ℝ) ≤ ratio (cellU 2) (P3 (cellU 2)) ∧ ratio (cellU 2) (P3 (cellU 2)) ≤ (3.65 : ℝ) ∧ (2.87 : ℝ) ≤ ratio (cellU 2) (P5 (cellU 2)) ∧ ratio (cellU 2) (P5 (cellU 2)) ≤ (2.88 : ℝ) ∧ (3.35 : ℝ) ≤ ratio (cellU 2) (P7 (cellU 2)) ∧ ratio (cellU 2) (P7 (cellU 2)) ≤ (3.37 : ℝ)) ∧
    ((2.95 : ℝ) ≤ ratio (cellU 0) (P3 (cellU 0)) ∧ ratio (cellU 0) (P3 (cellU 0)) ≤ (2.96 : ℝ) ∧ (0.44 : ℝ) ≤ ratio (cellU 0) (P5 (cellU 0)) ∧ ratio (cellU 0) (P5 (cellU 0)) ≤ (0.45 : ℝ) ∧ (2.81 : ℝ) ≤ ratio (cellU 0) (P7 (cellU 0)) ∧ ratio (cellU 0) (P7 (cellU 0)) ≤ (2.82 : ℝ)) ∧
    (|ratio (cellU 9) (P3 (cellU 9)) - ratio (cellU 9) (P7 (cellU 9))| < 0.01 * ratio (cellU 9) (P7 (cellU 9)) ∧ |ratio (cellU 9) (P5 (cellU 9)) - ratio (cellU 9) (P7 (cellU 9))| < 0.01 * ratio (cellU 9) (P7 (cellU 9))) ∧
    (|ratio (cellU 8) (P3 (cellU 8)) - ratio (cellU 8) (P7 (cellU 8))| < 0.01 * ratio (cellU 8) (P7 (cellU 8)) ∧ |ratio (cellU 8) (P5 (cellU 8)) - ratio (cellU 8) (P7 (cellU 8))| < 0.01 * ratio (cellU 8) (P7 (cellU 8))) ∧
    (|ratio (cellU 7) (P3 (cellU 7)) - ratio (cellU 7) (P7 (cellU 7))| < 0.01 * ratio (cellU 7) (P7 (cellU 7)) ∧ |ratio (cellU 7) (P5 (cellU 7)) - ratio (cellU 7) (P7 (cellU 7))| < 0.01 * ratio (cellU 7) (P7 (cellU 7))) ∧
    (|ratio (cellU 6) (P3 (cellU 6)) - ratio (cellU 6) (P7 (cellU 6))| < 0.01 * ratio (cellU 6) (P7 (cellU 6)) ∧ |ratio (cellU 6) (P5 (cellU 6)) - ratio (cellU 6) (P7 (cellU 6))| < 0.01 * ratio (cellU 6) (P7 (cellU 6))) ∧
    ((3.7 : ℝ) < ratio (cellU 4) (P3 (cellU 4)) ∧ (3.7 : ℝ) < ratio (cellU 4) (P5 (cellU 4)) ∧ (3.7 : ℝ) < ratio (cellU 4) (P7 (cellU 4))) ∧
    ((3.4 : ℝ) < ratio (cellU 3) (P5 (cellU 3)) ∧ ratio (cellU 3) (P5 (cellU 3)) < (3.7 : ℝ) ∧ (3.7 : ℝ) < ratio (cellU 3) (P3 (cellU 3)) ∧ (3.7 : ℝ) < ratio (cellU 3) (P7 (cellU 3))) ∧
    ((3.4 : ℝ) < ratio (cellU 2) (P3 (cellU 2)) ∧ ratio (cellU 2) (P3 (cellU 2)) < (3.7 : ℝ) ∧ ratio (cellU 2) (P5 (cellU 2)) < (3.4 : ℝ) ∧ ratio (cellU 2) (P7 (cellU 2)) < (3.4 : ℝ)) := by
  have h9 := cell9_ratios
  have h8 := cell8_ratios
  have h7 := cell7_ratios
  have h6 := cell6_ratios
  have h4 := cell4_ratios
  have h3 := cell3_ratios
  have h2 := cell2_ratios
  have h0 := cell0_ratios
  have he : cellU 0 = 23 / 54 := by norm_num [cellU, cellStiffness, c3terms]
  refine ⟨he, ⟨h9.1.1, h9.1.2, h9.2.1.1, h9.2.1.2, h9.2.2.1, h9.2.2.2⟩, ⟨h8.1.1, h8.1.2, h8.2.1.1, h8.2.1.2, h8.2.2.1, h8.2.2.2⟩, ⟨h7.1.1, h7.1.2, h7.2.1.1, h7.2.1.2, h7.2.2.1, h7.2.2.2⟩, ⟨h6.1.1, h6.1.2, h6.2.1.1, h6.2.1.2, h6.2.2.1, h6.2.2.2⟩, ⟨h4.1.1, h4.1.2, h4.2.1.1, h4.2.1.2, h4.2.2.1, h4.2.2.2⟩, ⟨h3.1.1, h3.1.2, h3.2.1.1, h3.2.1.2, h3.2.2.1, h3.2.2.2⟩, ⟨h2.1.1, h2.1.2, h2.2.1.1, h2.2.1.2, h2.2.2.1, h2.2.2.2⟩, ⟨h0.1.1, h0.1.2, h0.2.1.1, h0.2.1.2, h0.2.2.1, h0.2.2.2⟩, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · constructor <;> rw [abs_lt] <;> constructor <;> linarith [h9.1.1, h9.1.2, h9.2.1.1, h9.2.1.2, h9.2.2.1, h9.2.2.2]
  · constructor <;> rw [abs_lt] <;> constructor <;> linarith [h8.1.1, h8.1.2, h8.2.1.1, h8.2.1.2, h8.2.2.1, h8.2.2.2]
  · constructor <;> rw [abs_lt] <;> constructor <;> linarith [h7.1.1, h7.1.2, h7.2.1.1, h7.2.1.2, h7.2.2.1, h7.2.2.2]
  · constructor <;> rw [abs_lt] <;> constructor <;> linarith [h6.1.1, h6.1.2, h6.2.1.1, h6.2.1.2, h6.2.2.1, h6.2.2.2]
  · exact ⟨by linarith [h4.1.1], by linarith [h4.2.1.1], by linarith [h4.2.2.1]⟩
  · exact ⟨by linarith [h3.2.1.1], by linarith [h3.2.1.2], by linarith [h3.1.1], by linarith [h3.2.2.1]⟩
  · exact ⟨by linarith [h2.1.1], by linarith [h2.1.2], by linarith [h2.2.1.2], by linarith [h2.2.2.2]⟩

/-! ## 46:C21 — the gap of the transfer tally at the classical `π` -/

/-- 46:C21 [chart] — **the gap at the classical `π`.** The gap of the transfer tally is `1/(2π + 2)` in the shell's `2π = p − 1`;
read at the classical `π` the expression lies in `(0.12072, 0.12073)`, the row's `0.1207`. -/
theorem gap_at_classical_pi : (0.12072 : ℝ) < 1 / (2 * π + 2) ∧ 1 / (2 * π + 2) < (0.12073 : ℝ) := by
  have hp1 := pi_gt_d4
  have hp2 := pi_lt_d4
  have hpos : (0 : ℝ) < 2 * π + 2 := by positivity
  constructor
  · rw [lt_div_iff₀ hpos]; linarith
  · rw [div_lt_iff₀ hpos]; linarith

/-! ## 46:C12 — the operator family's values -/

/-- 46:C12 [chart] — **the family against the lattice.** With the chart's eigenvalue `E₀ = 2.232` of `|p| + r` (the reading of
35:C17) and the dilation `E₀(a|p| + ϰr) = √(aϰ) E₀`, the six candidates `a ∈ {1, 2}`, `ϰ ∈ {1, 2, 9/4}` read `2.232`,
`(3.156, 3.157)`, `3.348`, `(3.156, 3.157)`, `4.464`, `(4.734, 4.735)` (the row's `2.232`, `3.157`, `3.348`, `3.157`, `4.464`,
`4.735`); none lies inside any determination's error, `3.70(6)`, `3.63(10)`, `3.405(21)`, and the nearest, `3.348`, lies
`1.7 %` below the direct value. -/
theorem wrap_family_values (E₀ : ℝ) (hE : E₀ = 2.232) :
    (3.156 : ℝ) < √2 * E₀ ∧ √2 * E₀ < 3.157 ∧ √(9 / 4) * E₀ = 3.348 ∧ √4 * E₀ = 4.464 ∧
    (4.734 : ℝ) < √(9 / 2) * E₀ ∧ √(9 / 2) * E₀ < 4.735 ∧
    E₀ < 3.384 ∧ √2 * E₀ < 3.384 ∧ √(9 / 4) * E₀ < 3.384 ∧ 3.76 < √4 * E₀ ∧ 3.76 < √(9 / 2) * E₀ ∧
    (0.016 : ℝ) < (3.405 - √(9 / 4) * E₀) / 3.405 ∧ (3.405 - √(9 / 4) * E₀) / 3.405 < 0.018 := by
  subst hE
  have h2a : (1.4142 : ℝ) < √2 := by rw [lt_sqrt (by norm_num)]; norm_num
  have h2b : √2 < (1.4143 : ℝ) := by rw [sqrt_lt' (by norm_num)]; norm_num
  have h94 : √(9 / 4 : ℝ) = 3 / 2 := by
    rw [show (9 / 4 : ℝ) = (3 / 2) ^ 2 by norm_num, sqrt_sq (by norm_num)]
  have h4 : √(4 : ℝ) = 2 := by
    rw [show (4 : ℝ) = 2 ^ 2 by norm_num, sqrt_sq (by norm_num)]
  have h92a : (2.1213 : ℝ) < √(9 / 2) := by rw [lt_sqrt (by norm_num)]; norm_num
  have h92b : √(9 / 2 : ℝ) < (2.1214 : ℝ) := by rw [sqrt_lt' (by norm_num)]; norm_num
  rw [h94, h4]
  refine ⟨by nlinarith, by nlinarith, by norm_num, by norm_num, by nlinarith, by nlinarith, by norm_num, by nlinarith,
    by norm_num, by norm_num, by nlinarith, ?_, ?_⟩
  · rw [lt_div_iff₀ (by norm_num)]; norm_num
  · rw [div_lt_iff₀ (by norm_num)]; norm_num

end FRC.YangMillsML
