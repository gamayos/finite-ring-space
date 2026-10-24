import Mathlib
import FrcMathlib.Theme.Chart

/-!
# 16-octant — registrable depth and the dark-energy output: the ledger predicates on Mathlib (2026-10-23)

Rows of the predicate ledger of *Registrable depth and the dark-energy output over finite holographic substrate*
(tree `16-octant-20261022`). The paper carries the octant lemma and its outputs under the keys of 14-entropy, whose
declarations live in `FrcMathlib/Entropy.lean` and `FrcCore/Entropy.lean` and are linked at that origin. This module
holds five rows new to the paper: the confrontation of the output `Ω_Λ = tanh²(3π/8)` with the four flat-ΛCDM
determinations (C5, p16003), the matter fraction with its DESI falsifier (P4, p16004), the instance clause B9
(p16006, `section instance_173`: the instantiated Carrier (173, 30089), its octant mark, and the exchange count at the
instance for C2), and the coincidence of the exchange reading with the octant mark (C6, p16009; X4, p16010: the exchange
equivalence on the stations and the ring roots of the count `4S` at the exponents `S/2`, `S`, `2S` under the generator `3`)
— integer rows decided by `norm_num`/`omega`. The chart numerals are declared data: the determinations are those of Planck 2018 (Table 2, TT,TE,EE+lowE+lensing alone and with
BAO) and DESI DR2 (Section VI, BAO alone and BAO with the CMB), and the pulls follow from the bracket of
`tanh²(3π/8)` proved in the chart theme (`FRC.Chart.landing_bracket`). Classical (tier 2) on Mathlib's hierarchy.
-/

namespace FRC.Octant

open Real

/-! ## The confrontation (16:C5) -/
section confrontation

/-- 16:C5, 16:C3, 16:X1 [ΛCDM] — the output `Ω_Λ = tanh²(3π/8)` against the four flat-ΛCDM determinations [data]: the landing in
units of each determination's error. Planck 2018 alone, `0.6847 ± 0.0073`: between `0.13σ` and `0.15σ` (the row's
`0.14σ`); Planck 2018 with BAO, `0.6889 ± 0.0056`: between `0.92σ` and `0.94σ` (`0.93σ`); DESI DR2 BAO alone,
`0.7025 ± 0.0086`: between `2.1σ` and `2.3σ` (`2.2σ`); DESI DR2 BAO with the CMB, `0.6973 ± 0.0036`: between `3.7σ`
and `3.9σ` (`3.8σ`). From the bracket `0.68368 < tanh²(3π/8) < 0.68369` of the chart theme. -/
theorem confrontation_pulls :
    (0.13 : ℝ) < (0.6847 - tanh (3 * π / 8) ^ 2) / 0.0073 ∧ (0.6847 - tanh (3 * π / 8) ^ 2) / 0.0073 < 0.15 ∧
    (0.92 : ℝ) < (0.6889 - tanh (3 * π / 8) ^ 2) / 0.0056 ∧ (0.6889 - tanh (3 * π / 8) ^ 2) / 0.0056 < 0.94 ∧
    (2.1 : ℝ) < (0.7025 - tanh (3 * π / 8) ^ 2) / 0.0086 ∧ (0.7025 - tanh (3 * π / 8) ^ 2) / 0.0086 < 2.3 ∧
    (3.7 : ℝ) < (0.6973 - tanh (3 * π / 8) ^ 2) / 0.0036 ∧ (0.6973 - tanh (3 * π / 8) ^ 2) / 0.0036 < 3.9 := by
  obtain ⟨h1, h2, -, -⟩ := FRC.Chart.landing_bracket
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [lt_div_iff₀ (by norm_num)]; linarith
  · rw [div_lt_iff₀ (by norm_num)]; linarith
  · rw [lt_div_iff₀ (by norm_num)]; linarith
  · rw [div_lt_iff₀ (by norm_num)]; linarith
  · rw [lt_div_iff₀ (by norm_num)]; linarith
  · rw [div_lt_iff₀ (by norm_num)]; linarith
  · rw [lt_div_iff₀ (by norm_num)]; linarith
  · rw [div_lt_iff₀ (by norm_num)]; linarith

/-- 16:C5 [ΛCDM] — the age–de Sitter ratio of the chart, `t H_Λ = (2/3) artanh √Ω_Λ`, reaches `π/4` only at the
output (the chart theme's inversion), so at every other determination the ratio deviates from `π/4`: the function is
strictly increasing in `Ω_Λ` on `[0, 1)`, and each of the four determinations lies above the output, so the ratio lies
above `π/4` at each. -/
theorem ratio_above_octant (Ω : ℝ) (_h0 : 0 ≤ Ω) (h1 : Ω < 1) (hΩ : tanh (3 * π / 8) ^ 2 < Ω) :
    π / 4 < FRC.Chart.lcdmAge Ω := by
  obtain ⟨hid, -⟩ := FRC.Chart.octant_inversion
  have hpos := FRC.Chart.tanh_octant_pos
  have hroot : Real.sqrt (tanh (3 * π / 8) ^ 2) < Real.sqrt Ω := Real.sqrt_lt_sqrt (by positivity) hΩ
  have hlt1 : Real.sqrt Ω < 1 := by
    rw [Real.sqrt_lt' one_pos]; simpa using h1
  have hgt : -1 < Real.sqrt (tanh (3 * π / 8) ^ 2) := by linarith [Real.sqrt_nonneg (tanh (3 * π / 8) ^ 2)]
  have hmono : Real.artanh (Real.sqrt (tanh (3 * π / 8) ^ 2)) < Real.artanh (Real.sqrt Ω) :=
    Real.artanh_lt_artanh hgt hlt1 hroot
  unfold FRC.Chart.lcdmAge at hid ⊢
  linarith

end confrontation

/-! ## The matter fraction and its falsifier (16:P4) -/
section prediction

/-- 16:P4 [ΛCDM] — the matter fraction in the declared flat chart, `Ω_m = 1 − tanh²(3π/8)`: between `0.31631` and
`0.31632` (the row's `0.3163`); its distance from the DESI DR2 BAO with CMB determination `Ω_m = 0.3027 ± 0.0036`
[data] lies between `3.7σ` and `3.9σ` (the row's `3.8σ`). -/
theorem matter_fraction :
    (0.31631 : ℝ) < 1 - tanh (3 * π / 8) ^ 2 ∧ 1 - tanh (3 * π / 8) ^ 2 < 0.31632 ∧
    (3.7 : ℝ) < ((1 - tanh (3 * π / 8) ^ 2) - 0.3027) / 0.0036 ∧
    ((1 - tanh (3 * π / 8) ^ 2) - 0.3027) / 0.0036 < 3.9 := by
  obtain ⟨h1, h2, -, -⟩ := FRC.Chart.landing_bracket
  refine ⟨by linarith, by linarith, ?_, ?_⟩
  · rw [lt_div_iff₀ (by norm_num)]; linarith
  · rw [div_lt_iff₀ (by norm_num)]; linarith

/-- 16:P4 [ΛCDM] — the octant bound at the DESI DR2 BAO with CMB pair, `H₀ = 68.17 km s⁻¹ Mpc⁻¹`, `Ω_Λ = 0.6973`
[data]: with `H_Λ = H₀ √Ω_Λ`, the bound `(π/4)/H_Λ` lies between `13.48` and `13.50` Gyr (the row's `13.49`; the
megaparsec `3.0856775814913673 × 10¹⁹` km and a Julian year of `365.25` days declared [data]). -/
theorem desi_bound (HΛ : ℝ) (hH : HΛ = 68.17 * Real.sqrt 0.6973 / 3.0856775814913673e19) :
    (13.48e9 * (365.25 * 86400) : ℝ) < (π / 4) / HΛ ∧ (π / 4) / HΛ < 13.50e9 * (365.25 * 86400) := by
  have hs1 : (0.8350 : ℝ) < Real.sqrt 0.6973 := by
    rw [Real.lt_sqrt (by norm_num)]; norm_num
  have hs2 : Real.sqrt (0.6973 : ℝ) < 0.8351 := by
    rw [Real.sqrt_lt' (by norm_num)]; norm_num
  have hpi1 := Real.pi_gt_d6
  have hpi2 := Real.pi_lt_d6
  have hHpos : 0 < HΛ := by rw [hH]; positivity
  constructor
  · rw [lt_div_iff₀ hHpos, hH]; nlinarith
  · rw [div_lt_iff₀ hHpos, hH]; nlinarith

/-- 16:P1, 16:C2 [approx] — the octant bound at the Planck 2018 pair, `H₀ = 67.36 km s⁻¹ Mpc⁻¹`, `Ω_Λ = 0.6847` [data]: with
`H_Λ = H₀ √Ω_Λ`, the bound `(π/4)/H_Λ` lies between `13.77` and `13.79` Gyr (the row's `13.78`; the megaparsec and the
Julian year as in `desi_bound`). -/
theorem planck_bound (HΛ : ℝ) (hH : HΛ = 67.36 * Real.sqrt 0.6847 / 3.0856775814913673e19) :
    (13.77e9 * (365.25 * 86400) : ℝ) < (π / 4) / HΛ ∧ (π / 4) / HΛ < 13.79e9 * (365.25 * 86400) := by
  have hs1 : (0.8274 : ℝ) < Real.sqrt 0.6847 := by
    rw [Real.lt_sqrt (by norm_num)]; norm_num
  have hs2 : Real.sqrt (0.6847 : ℝ) < 0.8275 := by
    rw [Real.sqrt_lt' (by norm_num)]; norm_num
  have hpi1 := Real.pi_gt_d6
  have hpi2 := Real.pi_lt_d6
  have hHpos : 0 < HΛ := by rw [hH]; positivity
  constructor
  · rw [lt_div_iff₀ hHpos, hH]; nlinarith
  · rw [div_lt_iff₀ hHpos, hH]; nlinarith

end prediction

section instance_173
/-! ### The instantiated Carrier (173, 30089): the instance clause B9 and the exchange reading's count -/

/-- 16:B9, 16:C1 — the instantiated Carrier `(p, Ω) = (173, 30089)`, the minimal saturating tower (00:F5): `Ω` prime,
`Ω = 4·7522 + 1`, `S ≡ 2 (mod 4)` and `S ≡ 1 (mod 3)`, `p² < Ω ≤ (p+1)²`; the octant mark `ζ₈ = 14004` with `ζ₈² = h = 22003`
and `h² = −1`, and the quarter roots `ħ + h = Ω` (`ħ = 8086`). -/
theorem lab_carrier_173 :
    Nat.Prime 30089 ∧ 30089 = 4 * 7522 + 1 ∧ 7522 % 4 = 2 ∧ 7522 % 3 = 1 ∧
    173 * 173 < 30089 ∧ 30089 ≤ 174 * 174 ∧
    (14004 * 14004) % 30089 = 22003 ∧ (22003 * 22003) % 30089 = 30088 ∧ (22003 + 8086) % 30089 = 0 := by
  refine ⟨by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num⟩

/-- 16:B9 — the `2`-part of the cycle is exactly the octant: `Ω − 1 = 8 · 3761` with `3761` prime, so the octant exponent
`S/2 = 3761` is odd and no sixteenth exists. -/
theorem octant_two_part_173 : 30089 - 1 = 8 * 3761 ∧ Nat.Prime 3761 ∧ 3761 % 2 = 1 := by
  refine ⟨by norm_num, by norm_num, by norm_num⟩

/-- 16:B9, 16:C2 — the exchange reading's count at the instance: the count `2x` of an exchange of depth `x` is a station,
`4·(2x) < Ω`, exactly when `x ≤ S/2 = 3761`. -/
theorem exchange_station_173 (x : ℕ) : 4 * (2 * x) < 30089 ↔ x ≤ 3761 := by omega

/-- 16:C6, 16:X4 — the exchange reading and the octant mark coincide, for every even `S`: on the cycle `C_{4S}` the exchange
count `2x` of a station `x ≤ S` is the quarter `S` exactly when `x = S/2`. -/
theorem exchange_octant_iff_gen (S x : ℕ) (hS : S % 2 = 0) (h0 : 0 < S) (hx : x ≤ S) :
    (2 * x) % (4 * S) = S ↔ x = S / 2 := by
  rw [Nat.mod_eq_of_lt (by omega)]; omega

/-- 16:C6, 16:X4 — the same at the instance: for a station `x ≤ S = 7522` the exchange count `2x` is the quarter `S` on the
cycle `C_{4S}` (`4S = 30088`) exactly when `x = S/2 = 3761`. -/
theorem exchange_octant_iff (x : ℕ) (hx : x ≤ 7522) : (2 * x) % 30088 = 7522 ↔ x = 3761 := by omega

/-- 16:X4, 16:C6 — the ring roots of the count `4S ≡ −1` at the instance under the laboratory's declared generator `3`, in
`ZMod 30089`: the fourth root `ζ₈ = 3^{S/2} = 14004` at exponent `S/2 = 3761`, the square root `h = 3^{S} = 22003` at exponent
`S = 7522`, and `−1 = 3^{2S}` at exponent `2S = 15044`, with `ζ₈² = h` and `ζ₈⁴ = −1`; the cardinality strictly between the squares
`173² < Ω < 174²` (the weak form is in `lab_carrier_173`) and between the fourth powers `13⁴ < Ω < 14⁴`. The powers are reduced
modulo `30089` at every step (`reduce_mod_char`), so no numeral above the cardinality is formed. -/
theorem octant_ladder_173 :
    (3 : ZMod 30089) ^ 3761 = 14004 ∧ (3 : ZMod 30089) ^ 7522 = 22003 ∧ (3 : ZMod 30089) ^ 15044 = -1 ∧
    (14004 : ZMod 30089) ^ 2 = 22003 ∧ (14004 : ZMod 30089) ^ 4 = -1 ∧
    173 * 173 < 30089 ∧ 30089 < 174 * 174 ∧ 13 ^ 4 < 30089 ∧ 30089 < 14 ^ 4 := by
  refine ⟨by reduce_mod_char, by reduce_mod_char, by reduce_mod_char, by reduce_mod_char, by reduce_mod_char,
    by norm_num, by norm_num, by norm_num, by norm_num⟩

end instance_173

/-! ## Ledger predicates of 16-octant (hand-written pending the paper's posting; make_predicates.py rewrites them) -/

set_option linter.defProp false in
/-- 16:C5 (p16003) — The confrontation: against the four flat-ΛCDM determinations the output 0.6837 lands at 0.14σ,
0.93σ, 2.2σ and 3.8σ; the ratio exceeds π/4 at every Ω_Λ above the output, hence at each of the four; the radiation root is
checked in python only. -/
def p16003 := And.intro @FRC.Octant.confrontation_pulls (@FRC.Octant.ratio_above_octant)

set_option linter.defProp false in
/-- 16:P4 (p16004) — The matter fraction in the declared chart, 0.3163, 3.8σ from the DESI DR2 BAO with CMB value;
the bound at that pair 13.49 Gyr. -/
def p16004 := And.intro @FRC.Octant.matter_fraction (@FRC.Octant.desi_bound)

set_option linter.defProp false in
/-- 16:B9 (p16006) — The instance clause: the instantiated Carrier (173, 30089) declares S ≡ 2 (mod 4); its octant sector is
the whole 2-part of the cycle, Ω − 1 = 8·3761 with 3761 prime, and no sixteenth exists; the octant mark ζ₈ = 14004, ζ₈² = h;
the exchange count at the instance, 4·(2x) < Ω ↔ x ≤ 3761. -/
def p16006 := And.intro @FRC.Octant.lab_carrier_173 (And.intro @FRC.Octant.octant_two_part_173 (@FRC.Octant.exchange_station_173))

set_option linter.defProp false in
/-- 16:C6 (p16009) — The exchange reading and the octant mark coincide: on the cycle C_{4S}, S even, the exchange count 2x of a
station x ≤ S is the quarter S exactly when x = S/2; under any generator g the element g^{S/2} has order eight and its square is a
square root of −1; on the instance the generator 3 draws ζ₈, h and −1 at the exponents S/2, S, 2S, and the cardinality lies between
the squares 173², 174² and the fourth powers 13⁴, 14⁴. -/
def p16009 := And.intro @FRC.Octant.exchange_octant_iff_gen (And.intro @FRC.Octant.exchange_octant_iff (@FRC.Octant.octant_ladder_173))

set_option linter.defProp false in
/-- 16:X4 (p16010) — The halving is a step of the window ladder: the age datum S/2 is the exponent of a ring fourth root of the
count 4S, the octant mark under the declared generator, and its two-way count S the exponent of h, a ring square root of −1; under
the horizon pairing B10 that is the step from the coherence horizon to the decidability horizon on the ring. -/
def p16010 := And.intro @FRC.Octant.octant_ladder_173 (And.intro @FRC.Octant.exchange_octant_iff (@FRC.Octant.exchange_octant_iff_gen))

end FRC.Octant
