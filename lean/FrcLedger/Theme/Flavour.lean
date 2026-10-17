import Mathlib
import FrcLedger.Theme.Chart

/-!
# FrcLedger.Theme.Flavour — the chart theme's readings of the flavour sector (28-flavour, 17 October 2026)

The clauses of 28-flavour that read measured data against the exact content of `FrcCore/Theme/Flavour.lean`. Every
measured input enters as a hypothesis (the masses in MeV as the paper's validation suite states them, the NuFIT 6.0 splittings in eV² and angles, `V_us`),
every conclusion is a rational bound, and the square roots are bracketed by their squares (`Real.lt_sqrt`,
`Real.sqrt_lt'`), so that `norm_num` and `nlinarith` decide the reading. The charged-lepton Koide value to `10⁻⁵`
(`koide_measured`, 28:P1, X1); the up-quark Koide value in three schemes, all inside the band `[0.83, 0.89]` that holds
`5/6` (`koide_up_band`, 28:C4, X2, P2); the Gatto relation's leading term within `0.3 %` of `V_us` and its value at
`φ = π/2` (`gatto_leading`, 28:C6, X4, P3); the effective Froggatt–Nielsen powers bracketed by the integers `(4, 2)`,
`(4, 2)`, `(8, 4)` (`texture_powers`, 28:C7, X3, X6); the Georgi–Jarlskog double ratio and its `10–20 %` excess over `9`
(`gj_ratio`, 28:X5); the leading-order mass ratio `7 − 4√3` (`lo_ratio`, 28:C3, X7); the reactor-angle estimate `6–7 %`
above the measured value (`theta13_estimate`, 28:C9, X9); the maximal Jarlskog `1/(6√3)` and `J² = 1/108` (`jarlskog`,
28:C10, X10, P8); the TM2 relation at maximal atmospheric mixing (`tm2_at_maximal`, 28:C10, P8); the exact-TM2 solar
value (`exact_tm2_solar`, 28:C10); the `m₁ = 0` floor of the neutrino mass sum (`neutrino_floor`, 28:P5, P6, X11); and
the effective Majorana mass band at `m₁ = 0` (`majorana_band`, 28:P7).
-/

namespace FRC.FlavourML

open Real

/-- 28:P1, 28:X1 — the measured charged-lepton Koide value: with the PDG masses `m_e = 0.51099895`, `m_μ = 105.6583755`,
`m_τ = 1776.86` MeV, `|Q − 2/3| < 10⁻⁵` (the paper's `−6 × 10⁻⁶`); the square roots bracketed to seven digits. -/
theorem koide_measured (me mmu mtau : ℝ) (h1 : me = 0.51099895) (h2 : mmu = 105.6583755) (h3 : mtau = 1776.86) :
    |(me + mmu + mtau) / (sqrt me + sqrt mmu + sqrt mtau) ^ 2 - 2 / 3| < 1 / 100000 := by
  subst h1 h2 h3
  have e1 : 0.7148419 < sqrt 0.51099895 := by rw [Real.lt_sqrt (by norm_num)]; norm_num
  have e2 : sqrt 0.51099895 < 0.7148420 := by rw [Real.sqrt_lt' (by norm_num)]; norm_num
  have m1 : 10.2790259 < sqrt 105.6583755 := by rw [Real.lt_sqrt (by norm_num)]; norm_num
  have m2 : sqrt 105.6583755 < 10.2790261 := by rw [Real.sqrt_lt' (by norm_num)]; norm_num
  have t1 : 42.1528172 < sqrt 1776.86 := by rw [Real.lt_sqrt (by norm_num)]; norm_num
  have t2 : sqrt 1776.86 < 42.1528173 := by rw [Real.sqrt_lt' (by norm_num)]; norm_num
  set S := sqrt 0.51099895 + sqrt 105.6583755 + sqrt 1776.86 with hS
  have lo : 53.146685 < S := by rw [hS]; linarith
  have hi : S < 53.1466854 := by rw [hS]; linarith
  have Spos : 0 < S ^ 2 := by positivity
  rw [abs_lt]
  constructor
  · rw [lt_sub_iff_add_lt, lt_div_iff₀ Spos]; nlinarith
  · rw [sub_lt_iff_lt_add, div_lt_iff₀ Spos]; nlinarith

/-- The Koide value of three masses from brackets of their square roots: `Q = Σm/S²` with `S = Σ√m` between `lo` and
`hi`, so `Σm/hi² < Q < Σm/lo²`. -/
theorem koide_of_brackets (m1 m2 m3 lo hi : ℝ) (hm : 0 < m1 + m2 + m3) (hlo : 0 < lo)
    (h1 : lo < sqrt m1 + sqrt m2 + sqrt m3) (h2 : sqrt m1 + sqrt m2 + sqrt m3 < hi) :
    (m1 + m2 + m3) / hi ^ 2 < (m1 + m2 + m3) / (sqrt m1 + sqrt m2 + sqrt m3) ^ 2 ∧
    (m1 + m2 + m3) / (sqrt m1 + sqrt m2 + sqrt m3) ^ 2 < (m1 + m2 + m3) / lo ^ 2 := by
  have hS : 0 < sqrt m1 + sqrt m2 + sqrt m3 := lt_trans hlo h1
  constructor
  · apply div_lt_div_of_pos_left hm (by positivity)
    exact pow_lt_pow_left₀ h2 hS.le (by norm_num)
  · apply div_lt_div_of_pos_left hm (by positivity)
    exact pow_lt_pow_left₀ h1 hlo.le (by norm_num)

/-- 28:C4, 28:X2, 28:P2 — the up-quark Koide value in three schemes, each inside the band `[0.83, 0.89]` that holds the
framed value `5/6`: the working scheme (`m_u = 2.16`, `m_c = 1270`, `m_t = 172570` MeV) gives `Q_u ∈ (0.8489, 0.8490)`,
the pole masses (`2.2`, `1670`, `172800`) give `(0.8316, 0.8317)`, and MS-bar at `M_Z` (`1.27`, `619`, `168300`) gives
`(0.8875, 0.8876)`. -/
theorem koide_up_band :
    (0.8489 < (2.16 + 1270 + 172570) / (sqrt 2.16 + sqrt 1270 + sqrt 172570) ^ 2 ∧
      (2.16 + 1270 + 172570) / (sqrt 2.16 + sqrt 1270 + sqrt 172570) ^ 2 < (0.8490 : ℝ)) ∧
    (0.8316 < (2.2 + 1670 + 172800) / (sqrt 2.2 + sqrt 1670 + sqrt 172800) ^ 2 ∧
      (2.2 + 1670 + 172800) / (sqrt 2.2 + sqrt 1670 + sqrt 172800) ^ 2 < (0.8317 : ℝ)) ∧
    (0.8875 < (1.27 + 619 + 168300) / (sqrt 1.27 + sqrt 619 + sqrt 168300) ^ 2 ∧
      (1.27 + 619 + 168300) / (sqrt 1.27 + sqrt 619 + sqrt 168300) ^ 2 < (0.8876 : ℝ)) ∧
    (0.83 : ℝ) < 5 / 6 ∧ (5 / 6 : ℝ) < 0.89 := by
  have w1 : 1.4696938 < sqrt 2.16 := by rw [Real.lt_sqrt (by norm_num)]; norm_num
  have w2 : sqrt 2.16 < 1.4696939 := by rw [Real.sqrt_lt' (by norm_num)]; norm_num
  have w3 : 35.6370593 < sqrt 1270 := by rw [Real.lt_sqrt (by norm_num)]; norm_num
  have w4 : sqrt 1270 < 35.6370594 := by rw [Real.sqrt_lt' (by norm_num)]; norm_num
  have w5 : 415.4154546 < sqrt 172570 := by rw [Real.lt_sqrt (by norm_num)]; norm_num
  have w6 : sqrt 172570 < 415.4154547 := by rw [Real.sqrt_lt' (by norm_num)]; norm_num
  have p1 : 1.4832396 < sqrt 2.2 := by rw [Real.lt_sqrt (by norm_num)]; norm_num
  have p2 : sqrt 2.2 < 1.4832397 := by rw [Real.sqrt_lt' (by norm_num)]; norm_num
  have p3 : 40.8656334 < sqrt 1670 := by rw [Real.lt_sqrt (by norm_num)]; norm_num
  have p4 : sqrt 1670 < 40.8656335 := by rw [Real.sqrt_lt' (by norm_num)]; norm_num
  have p5 : 415.6921938 < sqrt 172800 := by rw [Real.lt_sqrt (by norm_num)]; norm_num
  have p6 : sqrt 172800 < 415.6921939 := by rw [Real.sqrt_lt' (by norm_num)]; norm_num
  have z1 : 1.1269427 < sqrt 1.27 := by rw [Real.lt_sqrt (by norm_num)]; norm_num
  have z2 : sqrt 1.27 < 1.1269428 := by rw [Real.sqrt_lt' (by norm_num)]; norm_num
  have z3 : 24.8797106 < sqrt 619 := by rw [Real.lt_sqrt (by norm_num)]; norm_num
  have z4 : sqrt 619 < 24.8797107 := by rw [Real.sqrt_lt' (by norm_num)]; norm_num
  have z5 : 410.2438299 < sqrt 168300 := by rw [Real.lt_sqrt (by norm_num)]; norm_num
  have z6 : sqrt 168300 < 410.2438300 := by rw [Real.sqrt_lt' (by norm_num)]; norm_num
  have W := koide_of_brackets 2.16 1270 172570 452.5222077 452.5222080 (by norm_num) (by norm_num) (by linarith) (by linarith)
  have P := koide_of_brackets 2.2 1670 172800 458.0410668 458.0410671 (by norm_num) (by norm_num) (by linarith) (by linarith)
  have Z := koide_of_brackets 1.27 619 168300 436.2504832 436.2504835 (by norm_num) (by norm_num) (by linarith) (by linarith)
  refine ⟨⟨?_, ?_⟩, ⟨?_, ?_⟩, ⟨?_, ?_⟩, by norm_num, by norm_num⟩
  · exact lt_trans (by norm_num) W.1
  · exact lt_trans W.2 (by norm_num)
  · exact lt_trans (by norm_num) P.1
  · exact lt_trans P.2 (by norm_num)
  · exact lt_trans (by norm_num) Z.1
  · exact lt_trans Z.2 (by norm_num)

/-- 28:C6, 28:X4, 28:P3 — the Gatto relation's leading term: with `m_d = 4.67`, `m_s = 93.4` MeV (the suite's values),
`√(m_d/m_s) ∈ (0.2236, 0.22361)`, within `0.35 %` of `V_us = 0.2243` (the paper's `0.3 %`); and at `φ = π/2`, with
`m_u = 2.16`, `m_c = 1270`, `√(m_d/m_s + m_u/m_c) ∈ (0.2273, 0.2275)` (the paper's `0.228`). -/
theorem gatto_leading (md ms mu mc Vus : ℝ) (hd : md = 4.67) (hs : ms = 93.4) (hu : mu = 2.16) (hc : mc = 1270)
    (hV : Vus = 0.2243) :
    0.2236 < sqrt (md / ms) ∧ sqrt (md / ms) < 0.22361 ∧ |sqrt (md / ms) - Vus| < 0.0035 * Vus ∧
    0.2273 < sqrt (md / ms + mu / mc) ∧ sqrt (md / ms + mu / mc) < 0.2275 := by
  subst hd hs hu hc hV
  have a1 : 0.2236 < sqrt (4.67 / 93.4) := by rw [Real.lt_sqrt (by norm_num)]; norm_num
  have a2 : sqrt (4.67 / 93.4) < 0.22361 := by rw [Real.sqrt_lt' (by norm_num)]; norm_num
  have b1 : 0.2273 < sqrt (4.67 / 93.4 + 2.16 / 1270) := by rw [Real.lt_sqrt (by norm_num)]; norm_num
  have b2 : sqrt (4.67 / 93.4 + 2.16 / 1270) < 0.2275 := by rw [Real.sqrt_lt' (by norm_num)]; norm_num
  refine ⟨a1, a2, ?_, b1, b2⟩
  rw [abs_lt]; constructor <;> linarith

/-- 28:C7, 28:X3, 28:X6 — the effective Froggatt–Nielsen powers bracketed by the integers of the role depths, at
`λ = V_us = 0.2243`: `λ⁵ < m_d/m_b < λ⁴`, `λ³ < m_s/m_b < λ²` (down `(4, 2)`), `λ⁶ < m_e/m_τ < λ⁵`, `λ² < m_μ/m_τ < λ`
(lepton, the electron the Georgi–Jarlskog outlier one power below), `λ⁸ < m_u/m_t < λ⁷`, `λ⁴ < m_c/m_t < λ³` (up
`(8, 4)`, the doubled exponents). -/
theorem texture_powers (lam md ms mb me mmu mtau mu mc mt : ℚ) (hl : lam = 0.2243) (hd : md = 4.67) (hs : ms = 93.4)
    (hb : mb = 4180) (he : me = 0.51099895) (hmu : mmu = 105.6583755) (ht : mtau = 1776.86) (hu : mu = 2.16)
    (hc : mc = 1270) (htop : mt = 172570) :
    (lam ^ 5 < md / mb ∧ md / mb < lam ^ 4) ∧ (lam ^ 3 < ms / mb ∧ ms / mb < lam ^ 2) ∧
    (lam ^ 6 < me / mtau ∧ me / mtau < lam ^ 5) ∧ (lam ^ 2 < mmu / mtau ∧ mmu / mtau < lam) ∧
    (lam ^ 8 < mu / mt ∧ mu / mt < lam ^ 7) ∧ (lam ^ 4 < mc / mt ∧ mc / mt < lam ^ 3) := by
  subst hl hd hs hb he hmu ht hu hc htop
  norm_num

/-- 28:X5, 00:P3 — the Georgi–Jarlskog double ratio `(m_μ/m_e)/(m_s/m_d)` at the measured masses lies in `(10.3, 10.5)`, between
`10 %` and `20 %` above the colour count's `N_c² = 9`: the open excess of the minimal Clebsch. -/
theorem gj_ratio (me mmu md ms : ℚ) (he : me = 0.51099895) (hmu : mmu = 105.6583755) (hd : md = 4.67) (hs : ms = 93.4) :
    10.3 < (mmu / me) / (ms / md) ∧ (mmu / me) / (ms / md) < 10.5 ∧
    9 * 1.10 < (mmu / me) / (ms / md) ∧ (mmu / me) / (ms / md) < 9 * 1.20 := by
  subst he hmu hd hs
  norm_num

/-- 28:C3, 28:X7 — the leading-order mass ratio `m_μ/m_τ = 7 − 4√3 ∈ (0.0717, 0.0719)`, against the observed
`m_μ/m_τ = 105.6583755/1776.86 ∈ (0.0594, 0.0595)`. -/
theorem lo_ratio (mmu mtau : ℝ) (h2 : mmu = 105.6583755) (h3 : mtau = 1776.86) :
    (0.0717 : ℝ) < 7 - 4 * sqrt 3 ∧ 7 - 4 * sqrt 3 < 0.0719 ∧ 0.0594 < mmu / mtau ∧ mmu / mtau < 0.0595 := by
  subst h2 h3
  have s1 : 1.732050 < sqrt 3 := by rw [Real.lt_sqrt (by norm_num)]; norm_num
  have s2 : sqrt 3 < 1.732051 := by rw [Real.sqrt_lt' (by norm_num)]; norm_num
  refine ⟨by linarith, by linarith, by norm_num, by norm_num⟩

/-- 28:C9, 28:X9 — the reactor angle at leading order: `sin θ_C/√2` with `sin θ_C = V_us = 0.2243` lies in
`(0.1585, 0.1587)`, between `6 %` and `7 %` above the measured `sin θ₁₃ = 0.1488`: an estimate, not a prediction. -/
theorem theta13_estimate (Vus s13 : ℝ) (hV : Vus = 0.2243) (hs : s13 = 0.1488) :
    0.1585 < Vus / sqrt 2 ∧ Vus / sqrt 2 < 0.1587 ∧ 1.06 * s13 < Vus / sqrt 2 ∧ Vus / sqrt 2 < 1.07 * s13 := by
  subst hV hs
  have r1 : 1.4142135 < sqrt 2 := by rw [Real.lt_sqrt (by norm_num)]; norm_num
  have r2 : sqrt 2 < 1.4142136 := by rw [Real.sqrt_lt' (by norm_num)]; norm_num
  have hpos : (0 : ℝ) < sqrt 2 := by positivity
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [lt_div_iff₀ hpos]; nlinarith
  · rw [div_lt_iff₀ hpos]; nlinarith
  · rw [lt_div_iff₀ hpos]; nlinarith
  · rw [div_lt_iff₀ hpos]; nlinarith

/-- 28:C10, 28:X10, 28:P8 — the maximal Jarlskog invariant: `1/(6√3) = √3/18` and `(1/(6√3))² = 1/108`. -/
theorem jarlskog : (1 : ℝ) / (6 * sqrt 3) = sqrt 3 / 18 ∧ ((1 : ℝ) / (6 * sqrt 3)) ^ 2 = 1 / 108 := by
  have h3 : sqrt 3 * sqrt 3 = 3 := Real.mul_self_sqrt (by norm_num)
  have hne : sqrt 3 ≠ 0 := by positivity
  constructor
  · field_simp; linarith
  · field_simp; nlinarith

/-- 28:C10, 28:P8 — the TM2 relation at maximal atmospheric mixing: `cos δ_CP = cot 2θ₂₃ · (1 − 2s₁₃²)/(s₁₃ √(2 − 3s₁₃²))`
vanishes at `θ₂₃ = π/4`, where `cos 2θ₂₃ = 0`, so `|δ_CP| = π/2`. -/
theorem tm2_at_maximal (s13 : ℝ) :
    Real.cos (2 * (π / 4)) / Real.sin (2 * (π / 4)) * ((1 - 2 * s13 ^ 2) / (s13 * sqrt (2 - 3 * s13 ^ 2))) = 0 ∧
    Real.arccos 0 = π / 2 := by
  refine ⟨?_, Real.arccos_zero⟩
  rw [show 2 * (π / 4) = π / 2 by ring, Real.cos_pi_div_two, zero_div, zero_mul]

/-- 28:C10 — the exact-TM2 solar value: `sin²θ₁₂ = 1/(3 c₁₃²)` at `sin²θ₁₃ = 0.02215` lies in `(0.3408, 0.3410)`, above
the measured `0.307`. -/
theorem exact_tm2_solar (s13sq : ℚ) (h : s13sq = 0.02215) :
    0.3408 < 1 / (3 * (1 - s13sq)) ∧ 1 / (3 * (1 - s13sq)) < 0.3410 ∧ (0.307 : ℚ) < 1 / (3 * (1 - s13sq)) := by
  subst h; norm_num

/-- 28:P5, 28:P6, 28:X11, 00:P3 — the `m₁ = 0` floor of the neutrino mass sum at NuFIT 6.0 (`Δm²₂₁ = 7.49 × 10⁻⁵`,
`Δm²₃₁ = 2.513 × 10⁻³` eV²): `√Δm²₂₁ + √Δm²₃₁ ∈ (0.0587, 0.0589)` eV, the `58.8` meV of the row. -/
theorem neutrino_floor (dm21 dm31 : ℝ) (h21 : dm21 = 7.49e-5) (h31 : dm31 = 2.513e-3) :
    0.0587 < sqrt dm21 + sqrt dm31 ∧ sqrt dm21 + sqrt dm31 < 0.0589 := by
  subst h21 h31
  have a1 : 0.0086544 < sqrt 7.49e-5 := by rw [Real.lt_sqrt (by norm_num)]; norm_num
  have a2 : sqrt 7.49e-5 < 0.0086545 := by rw [Real.sqrt_lt' (by norm_num)]; norm_num
  have b1 : 0.0501298 < sqrt 2.513e-3 := by rw [Real.lt_sqrt (by norm_num)]; norm_num
  have b2 : sqrt 2.513e-3 < 0.0501299 := by rw [Real.sqrt_lt' (by norm_num)]; norm_num
  constructor <;> linarith

/-- 28:P7 — the effective Majorana mass at `m₁ = 0` on the normal ordering: with `s₁₂² = 0.307`, `s₁₃² = 0.02215` and the
NuFIT 6.0 splittings, the two terms `c₁₃² s₁₂² m₂` and `s₁₃² m₃` lie in `(2.59, 2.61)` and `(1.10, 1.12)` meV, so
`m_ββ = |c₁₃² s₁₂² m₂ + e^{iα} s₁₃² m₃|` lies between `1.47` and `3.71` meV over the Majorana phase: the row's
`1.5–3.7` meV. -/
theorem majorana_band (dm21 dm31 s12sq s13sq : ℝ) (h21 : dm21 = 7.49e-5) (h31 : dm31 = 2.513e-3)
    (h12 : s12sq = 0.307) (h13 : s13sq = 0.02215) :
    2.59 < (1 - s13sq) * s12sq * (1000 * sqrt dm21) ∧ (1 - s13sq) * s12sq * (1000 * sqrt dm21) < 2.61 ∧
    1.10 < s13sq * (1000 * sqrt dm31) ∧ s13sq * (1000 * sqrt dm31) < 1.12 ∧
    1.47 < (1 - s13sq) * s12sq * (1000 * sqrt dm21) - s13sq * (1000 * sqrt dm31) ∧
    (1 - s13sq) * s12sq * (1000 * sqrt dm21) + s13sq * (1000 * sqrt dm31) < 3.71 := by
  subst h21 h31 h12 h13
  have a1 : 0.0086544 < sqrt 7.49e-5 := by rw [Real.lt_sqrt (by norm_num)]; norm_num
  have a2 : sqrt 7.49e-5 < 0.0086545 := by rw [Real.sqrt_lt' (by norm_num)]; norm_num
  have b1 : 0.0501298 < sqrt 2.513e-3 := by rw [Real.lt_sqrt (by norm_num)]; norm_num
  have b2 : sqrt 2.513e-3 < 0.0501299 := by rw [Real.sqrt_lt' (by norm_num)]; norm_num
  refine ⟨by nlinarith, by nlinarith, by nlinarith, by nlinarith, by nlinarith, by nlinarith⟩

end FRC.FlavourML
