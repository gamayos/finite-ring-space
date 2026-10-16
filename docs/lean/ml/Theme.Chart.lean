import Mathlib
import FrcLedger.Theme.Horizon

/-!
# FrcLedger.Theme.Chart — the chart theme: the readings against the continuum (ledger migration, task LM30)

The chart theme holds the readings of the finite results against the continuum, the only theme with the reals
(`frc/themes.py`, rank 30). It serves the chart clauses of the master's scale import (00:A7, `scale_import`; the ledger's `ln Ω` for L8,
`ln_omega_ledger`), its cosmology and prediction rows: the
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

/-! ## The scale import's chart numerals (00:A7; 14:A1, C1) -/
section scale

/-- 00:A7 [chart] — the scale import's numerals: with the fit's `Λ = 1.088 × 10⁻⁵² m⁻²` (Planck 2018) and the Planck
length `ℓ_P = 1.616255 × 10⁻³⁵ m` declared [data], the de Sitter radius `r_H = c/H_Λ`, `r_H² = 3/Λ`, gives
`S = π (r_H/ℓ_P)²` between `3.31` and `3.32 × 10¹²²` (the row's `3.3 × 10¹²²`) and `Ω = 4S + 1` between `1.32` and
`1.33 × 10¹²³` (the row's `1.3 × 10¹²³`). That the datum fixes the cardinality is the import; nothing here derives the
datum. -/
theorem scale_import (Λ ℓP r S Ω : ℝ) (hΛ : Λ = 1.088e-52) (hℓ : ℓP = 1.616255e-35)
    (hr2 : r ^ 2 = 3 / Λ) (hS : S = π * (r / ℓP) ^ 2) (hΩ : Ω = 4 * S + 1) :
    (3.31e122 : ℝ) < S ∧ S < 3.32e122 ∧ (1.32e123 : ℝ) < Ω ∧ Ω < 1.33e123 := by
  have hpi1 := Real.pi_gt_d6
  have hpi2 := Real.pi_lt_d6
  have hK : S = π * (3 / (Λ * ℓP ^ 2)) := by
    rw [hS, div_pow, hr2]; subst hΛ hℓ; field_simp
  subst hΛ hℓ
  have hKpos : (0 : ℝ) < 3 / (1.088e-52 * (1.616255e-35) ^ 2) := by positivity
  have hSlo : (3.3160599e122 : ℝ) < S := by
    rw [hK]; have := mul_lt_mul_of_pos_right hpi1 hKpos; norm_num at this ⊢; linarith
  have hShi : S < (3.3160611e122 : ℝ) := by
    rw [hK]; have := mul_lt_mul_of_pos_right hpi2 hKpos; norm_num at this ⊢; linarith
  subst hΩ
  refine ⟨by linarith, by linarith, by linarith, by linarith⟩

set_option exponentiation.threshold 512 in
/-- 00:L8 [chart] — the ledger's `ln Ω = 283.5`, the numeral the tilt reads, derived from the scale import: with the
same `Λ`, `ℓ_P`, `r_H² = 3/Λ`, `S = π (r_H/ℓ_P)²` and `Ω = 4S + 1`, `ln Ω` lies between `283.50` and `283.51`. The
logarithm is bracketed by `409 ln 2` (`Real.log_two_gt_d9`, `log_two_lt_d9`) and `1 − 1/m ≤ ln m ≤ m − 1` on the
mantissa `m = Ω/2⁴⁰⁹`. -/
theorem ln_omega_ledger (Λ ℓP r S Ω : ℝ) (hΛ : Λ = 1.088e-52) (hℓ : ℓP = 1.616255e-35)
    (hr2 : r ^ 2 = 3 / Λ) (hS : S = π * (r / ℓP) ^ 2) (hΩ : Ω = 4 * S + 1) :
    (283.50 : ℝ) < Real.log Ω ∧ Real.log Ω < 283.51 := by
  have hpi1 := Real.pi_gt_d6
  have hpi2 := Real.pi_lt_d6
  have hK : S = π * (3 / (Λ * ℓP ^ 2)) := by
    rw [hS, div_pow, hr2]; subst hΛ hℓ; field_simp
  subst hΛ hℓ
  have hKpos : (0 : ℝ) < 3 / (1.088e-52 * (1.616255e-35) ^ 2) := by positivity
  have hSlo : (3.3160599e122 : ℝ) < S := by
    rw [hK]; have := mul_lt_mul_of_pos_right hpi1 hKpos; norm_num at this ⊢; linarith
  have hShi : S < (3.3160611e122 : ℝ) := by
    rw [hK]; have := mul_lt_mul_of_pos_right hpi2 hKpos; norm_num at this ⊢; linarith
  subst hΩ
  have hΩpos : (0 : ℝ) < 4 * S + 1 := by linarith
  have hmpos : (0 : ℝ) < (4 * S + 1) / 2 ^ 409 := by positivity
  have hlog : Real.log (4 * S + 1) = 409 * Real.log 2 + Real.log ((4 * S + 1) / 2 ^ 409) := by
    have e : (4 * S + 1 : ℝ) = 2 ^ 409 * ((4 * S + 1) / 2 ^ 409) := by field_simp
    conv_lhs => rw [e]
    rw [Real.log_mul (by positivity) (by positivity), Real.log_pow]; push_cast; ring
  have hl1 := Real.log_two_gt_d9
  have hl2 := Real.log_two_lt_d9
  have hm1 : (1.0032614 : ℝ) < (4 * S + 1) / 2 ^ 409 := by
    rw [lt_div_iff₀ (by positivity)]; norm_num; linarith
  have hm2 : (4 * S + 1) / 2 ^ 409 < (1.0032619 : ℝ) := by
    rw [div_lt_iff₀ (by positivity)]; norm_num; linarith
  have hup := Real.log_le_sub_one_of_pos hmpos
  have hlo := Real.one_sub_inv_le_log_of_pos hmpos
  have hinv : 1 / ((4 * S + 1) / 2 ^ 409) < 1 / (1.0032614 : ℝ) := one_div_lt_one_div_of_lt (by norm_num) hm1
  rw [inv_eq_one_div] at hlo
  have hA : (0.00325 : ℝ) < Real.log ((4 * S + 1) / 2 ^ 409) := by
    have : (1 : ℝ) - 1 / 1.0032614 > 0.00325 := by norm_num
    linarith
  have hB : Real.log ((4 * S + 1) / 2 ^ 409) < (0.003262 : ℝ) := by linarith
  rw [hlog]
  exact ⟨by linarith, by linarith⟩

set_option exponentiation.threshold 512 in
/-- 22:C14, P5 [chart] — **the granularity ceiling at the anchor**: with the scale import's `Ω = 4S + 1`
(`S = π (r_H/ℓ_P)²`, the same hypotheses as `scale_import`), `2⁴⁰⁸ < Ω` and `Ω/4 < 2⁴⁰⁸`, so the largest depth `k`
with `T(k) = 2^{k + [k odd]} < Ω` is `k* = 408` (the odd `409` would need `4 · 2⁴⁰⁸ < Ω`); and `2²⁰⁴ < √Ω`,
`√Ω/4 < 2²⁰⁴`, so at the coherence horizon `k* = 204`. Every quantity compared is below `Ω`. -/
theorem ceiling_bracket (Λ ℓP r S Ω : ℝ) (hΛ : Λ = 1.088e-52) (hℓ : ℓP = 1.616255e-35)
    (hr2 : r ^ 2 = 3 / Λ) (hS : S = π * (r / ℓP) ^ 2) (hΩ : Ω = 4 * S + 1) :
    (2 : ℝ) ^ 408 < Ω ∧ Ω / 4 < (2 : ℝ) ^ 408 ∧ (2 : ℝ) ^ 204 < √Ω ∧ √Ω / 4 < (2 : ℝ) ^ 204 := by
  have hpi1 := Real.pi_gt_d6
  have hpi2 := Real.pi_lt_d6
  have hK : S = π * (3 / (Λ * ℓP ^ 2)) := by
    rw [hS, div_pow, hr2]; subst hΛ hℓ; field_simp
  subst hΛ hℓ
  have hKpos : (0 : ℝ) < 3 / (1.088e-52 * (1.616255e-35) ^ 2) := by positivity
  have hSlo : (3.3160599e122 : ℝ) < S := by
    rw [hK]; have := mul_lt_mul_of_pos_right hpi1 hKpos; norm_num at this ⊢; linarith
  have hShi : S < (3.3160611e122 : ℝ) := by
    rw [hK]; have := mul_lt_mul_of_pos_right hpi2 hKpos; norm_num at this ⊢; linarith
  subst hΩ
  have h1 : (2 : ℝ) ^ 408 < 4 * S + 1 := by norm_num; linarith
  have h2 : (4 * S + 1) / 4 < (2 : ℝ) ^ 408 := by norm_num; linarith
  have hΩpos : (0 : ℝ) < 4 * S + 1 := by linarith
  refine ⟨h1, h2, ?_, ?_⟩
  · rw [Real.lt_sqrt (by positivity)]
    calc ((2 : ℝ) ^ 204) ^ 2 = 2 ^ 408 := by norm_num
      _ < 4 * S + 1 := h1
  · have hsq : (√(4 * S + 1) / 4) ^ 2 < ((2 : ℝ) ^ 204) ^ 2 := by
      rw [div_pow, Real.sq_sqrt (le_of_lt hΩpos)]
      calc (4 * S + 1) / 4 ^ 2 = (4 * S + 1) / 4 / 4 := by ring
        _ < (2 : ℝ) ^ 408 / 4 := by
            exact div_lt_div_of_pos_right h2 (by norm_num)
        _ < (2 : ℝ) ^ 408 := by
            have : (0 : ℝ) < 2 ^ 408 := by positivity
            linarith
        _ = ((2 : ℝ) ^ 204) ^ 2 := by norm_num
    exact lt_of_pow_lt_pow_left₀ 2 (by positivity) hsq

/-- 22:A5, Z2 [chart] — **the Ω ledger's floors**: every null channel's floor lies below the anchor — the Riemann
height `(3 × 10¹²)⁴ = 8.1 × 10⁴⁹` (the binding floor, through the decidability horizon `Ω^{1/4}`), the Sorkin and
Born tallies `10²²` (one floor, cited twice by the paper's ledger file), the granularity `2⁶⁰` — with the same hypotheses
as `scale_import`. -/
theorem omega_floors (Λ ℓP r S Ω : ℝ) (hΛ : Λ = 1.088e-52) (hℓ : ℓP = 1.616255e-35)
    (hr2 : r ^ 2 = 3 / Λ) (hS : S = π * (r / ℓP) ^ 2) (hΩ : Ω = 4 * S + 1) :
    (3e12 : ℝ) ^ 4 = 8.1e49 ∧ (3e12 : ℝ) ^ 4 < Ω ∧ (1e22 : ℝ) < Ω ∧ (2 : ℝ) ^ 60 < Ω := by
  obtain ⟨-, -, hlo, -⟩ := scale_import Λ ℓP r S Ω hΛ hℓ hr2 hS hΩ
  refine ⟨by norm_num, ?_, ?_, ?_⟩ <;> norm_num <;> linarith

end scale

/-! ## 22-quantum: the Tsirelson value, the singlet law and the channel against the continuum (22:C17, X7, P3, C25;
C19, P1; 15 October 2026) -/
section quantum

/-- The primitive eighth root `ζ₈ = e^{iπ/4}`. -/
noncomputable def zeta8 : ℂ := Complex.exp ((π / 4 : ℝ) * Complex.I)

theorem zeta8_pow_four : zeta8 ^ 4 = -1 := by
  unfold zeta8
  rw [← Complex.exp_nat_mul]
  have : (4 : ℕ) * ((π / 4 : ℝ) * Complex.I) = (π : ℂ) * Complex.I := by push_cast; ring
  rw [this, Complex.exp_pi_mul_I]

theorem zeta8_inv : zeta8⁻¹ = Complex.exp (-((π / 4 : ℝ) * Complex.I)) := by
  unfold zeta8; rw [← Complex.exp_neg]

/-- 22:C17, X7, P3, C25 — **the Tsirelson value is `2√2`**: `ζ₈ + ζ₈⁻¹ = 2 cos(π/4) = √2`, so `S = 2(ζ₈ + ζ₈⁻¹) = 2√2`
as a real number and `S² = 8`. -/
theorem tsirelson_real :
    zeta8 + zeta8⁻¹ = (Real.sqrt 2 : ℂ) ∧ 2 * (zeta8 + zeta8⁻¹) = (2 * Real.sqrt 2 : ℝ) ∧
    (2 * (zeta8 + zeta8⁻¹)) ^ 2 = 8 := by
  have hcos : zeta8 + zeta8⁻¹ = 2 * Complex.cos ((π / 4 : ℝ) : ℂ) := by
    rw [zeta8_inv, Complex.two_cos, neg_mul]; rfl
  have hval : zeta8 + zeta8⁻¹ = (Real.sqrt 2 : ℂ) := by
    rw [hcos, ← Complex.ofReal_cos, Real.cos_pi_div_four]
    push_cast; ring
  refine ⟨hval, ?_, ?_⟩
  · rw [hval]; push_cast; ring
  · rw [hval]
    have : ((Real.sqrt 2 : ℝ) : ℂ) ^ 2 = 2 := by
      rw [← Complex.ofReal_pow, Real.sq_sqrt (by norm_num)]; push_cast; ring
    calc (2 * (Real.sqrt 2 : ℂ)) ^ 2 = 4 * ((Real.sqrt 2 : ℝ) : ℂ) ^ 2 := by ring
      _ = 8 := by rw [this]; norm_num

/-- 22:C17 — the singlet law: the correlator at `Δ` setting steps is the real part of `ζ₈₀^Δ = e^{2πiΔ/80}`,
`E(Δ) = cos(πΔ/40)`. -/
theorem singlet_law (Δ : ℕ) :
    (Complex.exp ((2 * π * Δ / 80 : ℝ) * Complex.I)).re = Real.cos (π * Δ / 40) := by
  rw [Complex.exp_ofReal_mul_I_re]
  congr 1
  ring

/-- 22:C19, P1 — the channel's chart: with the branch phase `φ`, the visibility `V = (x + x⁻¹)/2 = cos(φ/2)` and the
concurrence `C = (x − x⁻¹)/(2i) = sin(φ/2)` for `x = e^{iφ/2}`, so `V² + C² = 1` and `C² = sin²(φ/2)`; at `φ = 0`
the concurrence vanishes. -/
theorem channel_chart (φ : ℝ) :
    (Complex.exp ((φ / 2 : ℝ) * Complex.I) + Complex.exp (-((φ / 2 : ℝ) * Complex.I))) / 2 =
      (Real.cos (φ / 2) : ℂ) ∧
    (Complex.exp ((φ / 2 : ℝ) * Complex.I) - Complex.exp (-((φ / 2 : ℝ) * Complex.I))) / (2 * Complex.I) =
      (Real.sin (φ / 2) : ℂ) ∧
    Real.cos (φ / 2) ^ 2 + Real.sin (φ / 2) ^ 2 = 1 ∧ Real.sin (0 / 2) = 0 := by
  refine ⟨?_, ?_, Real.cos_sq_add_sin_sq _, by simp⟩
  · rw [Complex.ofReal_cos, Complex.cos, neg_mul]
  · rw [Complex.ofReal_sin, Complex.sin, neg_mul]
    have hI : Complex.I ≠ 0 := Complex.I_ne_zero
    field_simp
    linear_combination (Complex.exp ((φ / 2 : ℝ) * Complex.I) - Complex.exp (-((φ / 2 : ℝ) * Complex.I))) * Complex.I_sq

/-- 22:C19 — the channel entangles: off the trivial phase, `0 < φ < 2π`, the concurrence `C = sin(φ/2)` is not zero. -/
theorem channel_entangles (φ : ℝ) (h0 : 0 < φ) (h1 : φ < 2 * π) : Real.sin (φ / 2) ≠ 0 :=
  ne_of_gt (Real.sin_pos_of_pos_of_lt_pi (by linarith) (by linarith))

end quantum

/-! ## 26-pnp: the carrier family, the table beyond the horizon and the dilation generator (26:C2, B4) -/

section pnp

set_option exponentiation.threshold 512 in
/-- 26:C2 [chart] — **the family's size and the table beyond the horizon**: with the scale import's `Ω = 4S + 1` (the
hypotheses of `scale_import`), `2²⁰⁴ < √Ω < 2²⁰⁵`, so the shells of the family `P² < Ω` have at most `205` bits, and
`2¹⁰² < Ω^{1/4} < 2¹⁰³`, so a decision table with one entry per input of `204` bits has `2²⁰⁴` entries, below `√Ω` and
beyond the absolute horizon `Ω^{1/4}` by more than `2¹⁰¹`. No numeral formed exceeds `Ω` (the largest is `2⁴⁰⁸`). -/
theorem family_bits (Λ ℓP r S Ω : ℝ) (hΛ : Λ = 1.088e-52) (hℓ : ℓP = 1.616255e-35)
    (hr2 : r ^ 2 = 3 / Λ) (hS : S = π * (r / ℓP) ^ 2) (hΩ : Ω = 4 * S + 1) :
    (2 : ℝ) ^ 204 < √Ω ∧ √Ω < (2 : ℝ) ^ 205 ∧ (2 : ℝ) ^ 102 < √(√Ω) ∧ √(√Ω) < (2 : ℝ) ^ 103 := by
  obtain ⟨h1, h2, h3, -⟩ := ceiling_bracket Λ ℓP r S Ω hΛ hℓ hr2 hS hΩ
  have hΩpos : (0 : ℝ) < Ω := lt_trans (by positivity) h1
  -- `√Ω / 2 = √(Ω / 4) < 2²⁰⁴` from `Ω / 4 < 2⁴⁰⁸ = (2²⁰⁴)²`: the largest numeral formed is `2⁴⁰⁸ < Ω` (the G18 round of
  -- 16 October 2026: the first proof bounded `Ω` by a power of two above it, a numeral the corpus does not form)
  have hhalf : √Ω / 2 < (2 : ℝ) ^ 204 := by
    have e : √Ω / 2 = √(Ω / 4) := by
      rw [Real.sqrt_div' _ (by norm_num : (0 : ℝ) ≤ 4), show √(4 : ℝ) = 2 by
        rw [show (4 : ℝ) = 2 ^ 2 by norm_num, Real.sqrt_sq (by norm_num)]]
    rw [e, Real.sqrt_lt' (by positivity)]
    calc Ω / 4 < (2 : ℝ) ^ 408 := h2
      _ = ((2 : ℝ) ^ 204) ^ 2 := by norm_num
  have h5 : √Ω < (2 : ℝ) ^ 205 := by
    have : (2 : ℝ) ^ 205 = 2 * 2 ^ 204 := by norm_num
    rw [this]; linarith
  refine ⟨h3, h5, ?_, ?_⟩
  · rw [Real.lt_sqrt (by positivity)]
    calc ((2 : ℝ) ^ 102) ^ 2 = 2 ^ 204 := by norm_num
      _ < √Ω := h3
  · rw [Real.sqrt_lt' (by positivity)]
    calc √Ω < (2 : ℝ) ^ 205 := h5
      _ < ((2 : ℝ) ^ 103) ^ 2 := by norm_num

/-- 26:B5 — **the Gauss-sum modulus**: over `ℂ`, on a finite field `F`, for a nontrivial multiplicative character `χ`
and a primitive additive character `ψ`, `g(χ⁻¹, ψ⁻¹)` is the complex conjugate of `g(χ, ψ)` (Mathlib's
`star_gaussSum_eq`), so with the horizon theme's `gauss_product`, `g(χ) · conj g(χ) = |g(χ)|² = |F|`: on the prime
shell `𝔽_P`, `P`. -/
theorem gauss_modulus {F : Type*} [Field F] [Fintype F] {χ : MulChar F ℂ} (hχ : χ ≠ 1) {ψ : AddChar F ℂ}
    (hψ : ψ.IsPrimitive) :
    gaussSum χ ψ * star (gaussSum χ ψ) = Fintype.card F ∧ Complex.normSq (gaussSum χ ψ) = Fintype.card F := by
  have h := FRC.HorizonML.gauss_product hχ hψ
  rw [← star_gaussSum_eq] at h
  refine ⟨h, ?_⟩
  have h2 : (Complex.normSq (gaussSum χ ψ) : ℂ) = (Fintype.card F : ℂ) := by rw [← Complex.mul_conj, ← h]; rfl
  exact_mod_cast h2

/-- 26:B4 [chart] — **the dilation generator**: `Ĥ = −i(x ∂ₓ + ½)` has `x^{−1/2 + iν}` as eigenfunction of eigenvalue
`ν` on `x > 0`; the frequency index is the spectrum of `Ĥ` in the continuum reading of the scale shift (20:E1). -/
theorem dilation_eigen (ν x : ℝ) (hx : 0 < x) :
    -Complex.I * ((x : ℂ) * deriv (fun t : ℝ => (t : ℂ) ^ (-(1 / 2 : ℂ) + Complex.I * ν)) x
      + (1 / 2 : ℂ) * (x : ℂ) ^ (-(1 / 2 : ℂ) + Complex.I * ν))
      = ν * (x : ℂ) ^ (-(1 / 2 : ℂ) + Complex.I * ν) := by
  set s : ℂ := -(1 / 2 : ℂ) + Complex.I * ν with hs
  have hx0 : (x : ℂ) ≠ 0 := by exact_mod_cast hx.ne'
  have hslit : (x : ℂ) ∈ Complex.slitPlane := Complex.ofReal_mem_slitPlane.2 hx
  have hd : HasDerivAt (fun t : ℝ => (t : ℂ) ^ s) (s * (x : ℂ) ^ (s - 1)) x :=
    (Complex.hasStrictDerivAt_cpow_const hslit).hasDerivAt.comp_ofReal
  rw [hd.deriv]
  have hpow : (x : ℂ) * (x : ℂ) ^ (s - 1) = (x : ℂ) ^ s := by
    rw [Complex.cpow_sub _ _ hx0, Complex.cpow_one, mul_div_cancel₀ _ hx0]
  have hcoef : -Complex.I * (s + 1 / 2) = ν := by
    rw [hs]; ring_nf; rw [Complex.I_sq]; ring
  calc -Complex.I * ((x : ℂ) * (s * (x : ℂ) ^ (s - 1)) + (1 / 2 : ℂ) * (x : ℂ) ^ s)
      = -Complex.I * (s + 1 / 2) * (x : ℂ) ^ s := by rw [← hpow]; ring
    _ = ν * (x : ℂ) ^ s := by rw [hcoef]

end pnp

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

/-- 00:L3, 14:A8 [ΛCDM] — the rival chart's age identity as the import it is: in flat matter-plus-`Λ` the product of
the age and the asymptotic rate is `t₀H_Λ = (2/3) artanh √Ω_Λ`, a function of the one fitted parameter; outside
`[0, 1)` the value is junk. Moved here from 14-entropy (task LM30's repair, 7 October 2026), which keeps the name. -/
noncomputable def lcdmAge (Ω : ℝ) : ℝ := 2 / 3 * artanh (√Ω)

/-- 00:L3, 14:C7, 14:X3 [ΛCDM] — the octant inversion: the rival chart's identity gives `t₀H_Λ = π/4` at
`Ω_Λ = tanh²(3π/8)` and, for `0 ≤ Ω_Λ < 1`, only there. Moved here from 14-entropy, which keeps the name. -/
theorem octant_inversion :
    lcdmAge (tanh (3 * π / 8) ^ 2) = π / 4 ∧
    ∀ Ω : ℝ, 0 ≤ Ω → Ω < 1 → lcdmAge Ω = π / 4 → Ω = tanh (3 * π / 8) ^ 2 := by
  have hpos := tanh_octant_pos
  constructor
  · unfold lcdmAge
    rw [Real.sqrt_sq hpos.le, Real.artanh_tanh]; ring
  · intro Ω h0 h1 h
    unfold lcdmAge at h
    have hart : artanh (√Ω) = 3 * π / 8 := by linarith
    have hΩ : √Ω ∈ Set.Ioo (-1 : ℝ) 1 := by
      refine ⟨by linarith [Real.sqrt_nonneg Ω], ?_⟩
      rw [Real.sqrt_lt' one_pos]; simpa using h1
    have := Real.tanh_artanh hΩ
    rw [hart] at this
    rw [this, Real.sq_sqrt h0]

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

/-- The locus to six places: `0.949866 < (π/4)/tanh(3π/8) < 0.949868`, for the rates read on it. -/
theorem locus_fine : (0.949866 : ℝ) < (π / 4) / tanh (3 * π / 8) ∧ (π / 4) / tanh (3 * π / 8) < 0.949868 := by
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

/-- 00:L3 — the deviation fixed to the row's rounded `0.19σ`: between `0.186σ` and `0.19σ` below Planck's
`0.685 ± 0.007` (data). -/
theorem landing_fine :
    0.186 * 0.007 < 0.685 - tanh (3 * π / 8) ^ 2 ∧ 0.685 - tanh (3 * π / 8) ^ 2 < (0.19 * 0.007 : ℝ) := by
  obtain ⟨h1, h2, _, h4⟩ := landing_bracket
  exact ⟨by linarith, h4⟩

/-- 00:L3 [chart] — the channel-1 consistency: read on the depth `t = 13.79` Gyr (the row's depth numeral, a Julian
year of `365.25` days; data), the locus `t H₀ = (π/4)/tanh(3π/8)` gives `67.35 < H₀ < 67.36` km s⁻¹ Mpc⁻¹ (the
megaparsec `3.0856775814913673 × 10¹⁹` km; data): the channel-1 rate `67.4` to `0.1 %` (14:P3, "a consistency, not a
prediction"). -/
theorem hubble_landing (t H0 : ℝ) (ht : t = 13.79e9 * (365.25 * 86400))
    (hloc : t * H0 = (π / 4) / tanh (3 * π / 8)) :
    (67.35 : ℝ) < H0 * 3.0856775814913673e19 ∧ H0 * 3.0856775814913673e19 < 67.36 := by
  obtain ⟨hl, hu⟩ := locus_fine
  have htpos : (0 : ℝ) < t := by rw [ht]; norm_num
  have hH : H0 = (π / 4) / tanh (3 * π / 8) / t := by
    rw [eq_div_iff htpos.ne', mul_comm, hloc]
  constructor
  · rw [hH, ht, div_mul_eq_mul_div, lt_div_iff₀ (by norm_num)]; nlinarith
  · rw [hH, ht, div_mul_eq_mul_div, div_lt_iff₀ (by norm_num)]; nlinarith

/-- 00:L3, 14:P3 [chart] — the locus read on the fit-independent stellar age `t★ = 13.61 ± 0.34` Gyr (data; a Julian
year of `365.25` days): `68.24 < H₀ < 68.25` km s⁻¹ Mpc⁻¹ (the row's `68.2`); the age's error carried to the rate,
`H₀ · 0.34/13.61`, lies between `1.70` and `1.71` (the row's `±1.7`); and the Cepheid ladder's `73.0 ± 1.0` (data),
errors combined with `±1.7`, lies between `2.40σ` and `2.42σ` above it (the row's `2.4σ`). -/
theorem hubble_stellar (t H0 : ℝ) (ht : t = 13.61e9 * (365.25 * 86400))
    (hloc : t * H0 = (π / 4) / tanh (3 * π / 8)) :
    (68.24 : ℝ) < H0 * 3.0856775814913673e19 ∧ H0 * 3.0856775814913673e19 < 68.25 ∧
    (1.70 : ℝ) < H0 * 3.0856775814913673e19 * (0.34 / 13.61) ∧ H0 * 3.0856775814913673e19 * (0.34 / 13.61) < 1.71 ∧
    (2.40 : ℝ) < (73.0 - H0 * 3.0856775814913673e19) / √(1.7 ^ 2 + 1.0 ^ 2) ∧
    (73.0 - H0 * 3.0856775814913673e19) / √(1.7 ^ 2 + 1.0 ^ 2) < 2.42 := by
  obtain ⟨hl, hu⟩ := locus_fine
  have htpos : (0 : ℝ) < t := by rw [ht]; norm_num
  have hH : H0 = (π / 4) / tanh (3 * π / 8) / t := by
    rw [eq_div_iff htpos.ne', mul_comm, hloc]
  have h1 : (68.24 : ℝ) < H0 * 3.0856775814913673e19 := by
    rw [hH, ht, div_mul_eq_mul_div, lt_div_iff₀ (by norm_num)]; nlinarith
  have h2 : H0 * 3.0856775814913673e19 < (68.25 : ℝ) := by
    rw [hH, ht, div_mul_eq_mul_div, div_lt_iff₀ (by norm_num)]; nlinarith
  have hs1 : (1.9723 : ℝ) < √(1.7 ^ 2 + 1.0 ^ 2) := by
    rw [Real.lt_sqrt (by norm_num)]; norm_num
  have hs2 : √(1.7 ^ 2 + 1.0 ^ 2 : ℝ) < 1.9724 := by
    rw [Real.sqrt_lt' (by norm_num)]; norm_num
  have hspos : (0 : ℝ) < √(1.7 ^ 2 + 1.0 ^ 2) := by linarith
  refine ⟨h1, h2, by nlinarith, by nlinarith, ?_, ?_⟩
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

/-- 00:L1 — the floor fixed to the row's rounded `1.04 × 10⁻¹⁰`: at the channel-1 rate `H₀ = 67.4 km s⁻¹ Mpc⁻¹`,
`1.04 × 10⁻¹⁰ < a₀ < 1.045 × 10⁻¹⁰ m s⁻²`. -/
theorem floor_fine (c H0 : ℝ) (hc : c = 299792458) (hH : H0 = 67.4e3 / 3.0856775814913673e22) :
    (1.04e-10 : ℝ) < c * H0 / (2 * π) ∧ c * H0 / (2 * π) < 1.045e-10 := by
  have hpi1 := Real.pi_gt_d6
  have hpi2 := Real.pi_lt_d6
  subst hc hH
  constructor
  · rw [lt_div_iff₀ (by positivity)]; nlinarith
  · rw [div_lt_iff₀ (by positivity)]; nlinarith

/-- 00:P1 [chart] — the running floor: if the floor is read at every redshift on the registered rate,
`a₀(z) = cH(z)/2π`, and the deep-regime Tully–Fisher law `v⁴ = G M a₀` holds at fixed baryonic mass `M`, then
`a₀(z)/a₀(0) = H(z)/H(0) = E(z)` and the zero-point evolves as `v(z)/v(0) = E(z)^{1/4}`; the rates and speeds are
asked positive at `0` and `z` only. The law `v⁴ = G M a₀` is the deep regime's import. That the floor tracks the
registered rate (the gravity realisation, 00:D5) is the row's realisation clause, not formal content. -/
theorem running_floor (c G M : ℝ) (H a v : ℝ → ℝ) (z : ℝ) (hc : 0 < c) (hG : 0 < G) (hM : 0 < M)
    (h0 : 0 < H 0) (hz : 0 < H z) (ha : ∀ z, a z = c * H z / (2 * π)) (hv0 : 0 < v 0) (hvz : 0 < v z)
    (htf : ∀ z, v z ^ 4 = G * M * a z) :
    a z / a 0 = H z / H 0 ∧ v z / v 0 = (H z / H 0) ^ (1 / 4 : ℝ) := by
  have hpi := Real.pi_pos
  have hratio : a z / a 0 = H z / H 0 := by
    rw [ha z, ha 0]; field_simp
  refine ⟨hratio, ?_⟩
  have ha0 : 0 < a 0 := by rw [ha 0]; positivity
  have h4 : (v z / v 0) ^ 4 = H z / H 0 := by
    rw [div_pow, htf z, htf 0, ← hratio]; field_simp
  rw [← h4, show (1 / 4 : ℝ) = ((4 : ℕ) : ℝ)⁻¹ by norm_num]
  exact (Real.pow_rpow_inv_natCast (div_pos hvz hv0).le (by norm_num)).symm

end floor

/-! ## The radial ladder of the minimal pair (38:B2) -/
section ladder

/-- 38:B2 [chart] — the radial ladder of the sky: the shell radii `R sin(2aπ/13)`, `a = 1, 2, 3`, are positive,
strictly increasing, and inside the rim `R` (the chart flattening of the latitude circles; the capacity `4a < p ⇔ a ≤ κ`
is the core's `FRC.Pair.window`). -/
theorem ladder_monotone (R : ℝ) (hR : 0 < R) :
    0 < R * Real.sin (2 * π / 13) ∧ R * Real.sin (2 * π / 13) < R * Real.sin (4 * π / 13) ∧
    R * Real.sin (4 * π / 13) < R * Real.sin (6 * π / 13) ∧ R * Real.sin (6 * π / 13) < R := by
  have hpi := Real.pi_pos
  have mono : ∀ x y : ℝ, 0 ≤ x → x < y → y ≤ π / 2 → Real.sin x < Real.sin y := fun x y hx hxy hy =>
    Real.sin_lt_sin_of_lt_of_le_pi_div_two (by linarith) hy hxy
  refine ⟨mul_pos hR (Real.sin_pos_of_pos_of_lt_pi (by positivity) (by linarith)), ?_, ?_, ?_⟩
  · exact mul_lt_mul_of_pos_left (mono _ _ (by positivity) (by linarith) (by linarith)) hR
  · exact mul_lt_mul_of_pos_left (mono _ _ (by positivity) (by linarith) (by linarith)) hR
  · have h := mono (6 * π / 13) (π / 2) (by positivity) (by linarith) le_rfl
    rw [Real.sin_pi_div_two] at h
    calc R * Real.sin (6 * π / 13) < R * 1 := mul_lt_mul_of_pos_left h hR
      _ = R := mul_one R

end ladder

/-! ## The primordial tilt (00:L8) -/
section tilt

/-- 00:L8 [chart] — the tilt at the ledger's `ln Ω = 283.5` (`ln_omega_ledger`, from the scale import 00:A7; data): `n_s − 1 = −π²/ln Ω` has magnitude
between `0.03481` and `0.03482` (the row's `−0.0348`); against Planck 2018's `−0.0351 ± 0.0042` (data) the
deviation is between `+0.068σ` and `+0.069σ` (the row's `+0.07σ`); the count `½ ln Ω` gives `−π²/(ln Ω/2)`, off
by between `8.2σ` and `8.25σ` (the row's exclusion at `8.2σ`). That `ln Ω` is the e-fold count of the frame's scale
range is the row's realisation clause, not formal content. -/
theorem tilt_ledger :
    (0.03481 : ℝ) < π ^ 2 / 283.5 ∧ π ^ 2 / 283.5 < 0.03482 ∧
    (0.068 * 0.0042 : ℝ) < 0.0351 - π ^ 2 / 283.5 ∧ 0.0351 - π ^ 2 / 283.5 < 0.069 * 0.0042 ∧
    (8.2 * 0.0042 : ℝ) < π ^ 2 / (283.5 / 2) - 0.0351 ∧ π ^ 2 / (283.5 / 2) - 0.0351 < 8.25 * 0.0042 := by
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
  · have : π ^ 2 / (283.5 / 2) < (8.25 * 0.0042 + 0.0351 : ℝ) := by rw [div_lt_iff₀ (by norm_num)]; norm_num; linarith
    linarith

/-- 00:L8 — the e-fold count of the frame's scale range: from `1/√Ω` to `√Ω` the logarithm spans `ln Ω`. -/
theorem efold_count (Ω : ℝ) (hΩ : 0 < Ω) : Real.log (√Ω / (1 / √Ω)) = Real.log Ω := by
  have hs : 0 < √Ω := Real.sqrt_pos.2 hΩ
  have e : √Ω / (1 / √Ω) = Ω := by
    rw [div_div_eq_mul_div, div_one, Real.mul_self_sqrt hΩ.le]
  rw [e]

end tilt

/-! ## 20-rh: the complex characters of the cycle, the characters as eigenvectors of the scale-shift, and the von
Mangoldt weight (20:E1, E12, E13, C5, C2; task LM36)

Moved here from 20-rh's `FrcLedger/Rh.lean` under the same names; that module keeps the old names as aliases. The
exact shell arithmetic of the same rows is the horizon theme's (`Theme/Horizon.lean`, `FRC.HorizonML`). -/

section characters

open Complex Finset

variable {n : ℕ} [NeZero n]

/-- The `j`-th chart mode of the cycle `C_n`: `χ_j(m) = e^{2πi·jm/n}`. On the shell, `m` is the discrete
logarithm of the residue `g^m` and `n = p − 1`. -/
noncomputable def chi (j m : ZMod n) : ℂ := ZMod.stdAddChar (j * m)

/-- The coefficient of `v` on the mode `χ_j`: `⟨v, χ_j⟩ = Σ_m v(m) χ_j(m)̄`. -/
noncomputable def coef (v : ZMod n → ℂ) (j : ZMod n) : ℂ := ∑ m, v m * (starRingEnd ℂ) (chi j m)

lemma chi_conj (j m : ZMod n) : (starRingEnd ℂ) (chi j m) = ZMod.stdAddChar (-(j * m)) := by
  rw [chi, AddChar.map_neg_eq_conj]

/-- 20:E13 — orthogonality of the chart modes: `Σ_m χ_j(m) χ_k(m)̄ = n·[j = k]`, each of squared norm
`n = p − 1` (with `chi_inversion`, the `p − 1` characters are an orthogonal basis of `ℂ^{F^×}`; the orthonormal
system is `χ_j/√n`). -/
theorem chi_orthogonal (j k : ZMod n) :
    ∑ m, chi j m * (starRingEnd ℂ) (chi k m) = if j = k then (n : ℂ) else 0 := by
  have : ∀ m, chi j m * (starRingEnd ℂ) (chi k m) = ZMod.stdAddChar (m * (j - k)) := fun m => by
    rw [chi_conj, chi, ← AddChar.map_add_eq_mul]
    congr 1; ring
  simp_rw [this]
  rw [AddChar.sum_mulShift _ (ZMod.isPrimitive_stdAddChar n), ZMod.card]
  simp only [sub_eq_zero]
  split_ifs <;> simp

/-- 20:E12, 20:E1 — clause (iii): the scale-shift `m ↦ m + 1` (the residue `g^m ↦ g^{m+1}`) has every chart mode
as an eigenvector, with eigenphase `e^{2πi·j/n}` independent of the vector: `χ_j(m + 1) = e^{2πi j/n} χ_j(m)`. -/
theorem chi_shift (j m : ZMod n) :
    chi j (m + 1) = ZMod.stdAddChar j * chi j m ∧
    ZMod.stdAddChar (j : ZMod n) = Complex.exp (2 * Real.pi * I * j.val / n) := by
  constructor
  · rw [chi, chi, mul_add, mul_one, AddChar.map_add_eq_mul, mul_comm]
  · rw [ZMod.stdAddChar_apply, ZMod.toCircle_apply]

/-- 20:E12, 20:E13 — clause (i): Fourier inversion on the cycle, `v = (1/n) Σ_j ⟨v, χ_j⟩ χ_j`, with the constant
mode carrying the mean, `⟨v, χ_0⟩ = Σ_m v(m)`, so the nontrivial modes carry `v − v̄·1`. -/
theorem chi_inversion (v : ZMod n → ℂ) :
    (∀ m, v m = (n : ℂ)⁻¹ * ∑ j, coef v j * chi j m) ∧ coef v 0 = ∑ m, v m ∧
    ∀ m, v m - (n : ℂ)⁻¹ * ∑ m', v m' = (n : ℂ)⁻¹ * ∑ j ∈ univ.erase 0, coef v j * chi j m := by
  have hn : (n : ℂ) ≠ 0 := by exact_mod_cast NeZero.ne n
  have hkey : ∀ m, ∑ j, coef v j * chi j m = (n : ℂ) * v m := by
    intro m
    simp only [coef, sum_mul]
    rw [sum_comm]
    have : ∀ m', ∑ j, v m' * (starRingEnd ℂ) (chi j m') * chi j m
        = v m' * ∑ j, chi j m * (starRingEnd ℂ) (chi j m') := fun m' => by
      rw [mul_sum]; exact sum_congr rfl fun j _ => by ring
    simp_rw [this]
    have horth : ∀ m', ∑ j, chi j m * (starRingEnd ℂ) (chi j m') = if m' = m then (n : ℂ) else 0 := by
      intro m'
      have : ∀ j, chi j m * (starRingEnd ℂ) (chi j m') = ZMod.stdAddChar (j * (m - m')) := fun j => by
        rw [chi_conj, chi, ← AddChar.map_add_eq_mul]
        congr 1; ring
      simp_rw [this]
      rw [AddChar.sum_mulShift _ (ZMod.isPrimitive_stdAddChar n), ZMod.card]
      by_cases h : m' = m
      · subst h; simp
      · rw [ite_eq_right (fun e => h (sub_eq_zero.1 e).symm), ite_eq_right h]; simp
    simp_rw [horth]
    simp [mul_comm]
  have hmean : coef v 0 = ∑ m, v m := by
    simp only [coef, chi, zero_mul, AddChar.map_zero_eq_one, map_one, mul_one]
  refine ⟨fun m => ?_, hmean, fun m => ?_⟩
  · rw [hkey, ← mul_assoc, inv_mul_cancel₀ hn, one_mul]
  · have hsplit := sum_erase_add univ (fun j => coef v j * chi j m) (mem_univ 0)
    rw [hkey] at hsplit
    have h0 : coef v 0 * chi 0 m = ∑ m', v m' := by
      rw [hmean, chi, zero_mul, AddChar.map_zero_eq_one, mul_one]
    rw [h0] at hsplit
    have : ∑ j ∈ univ.erase 0, coef v j * chi j m = (n : ℂ) * v m - ∑ m', v m' := by
      linear_combination hsplit
    rw [this, mul_sub, ← mul_assoc, inv_mul_cancel₀ hn, one_mul]

/-- 20:E13, 20:C5 — Parseval on the cycle: `Σ_j |⟨v, χ_j⟩|² = n Σ_m |v(m)|²`; the chart modes are complete. -/
theorem chi_parseval (v : ZMod n → ℂ) :
    ∑ j, normSq (coef v j) = n * ∑ m, normSq (v m) := by
  have h := (chi_inversion v).1
  apply Complex.ofReal_injective
  push_cast
  simp_rw [← Complex.mul_conj]
  have hc : ∀ j, (starRingEnd ℂ) (coef v j) = ∑ m, (starRingEnd ℂ) (v m) * chi j m := fun j => by
    simp only [coef, map_sum, map_mul, Complex.conj_conj]
  calc ∑ j, coef v j * (starRingEnd ℂ) (coef v j)
      = ∑ j, ∑ m, (starRingEnd ℂ) (v m) * (coef v j * chi j m) := by
        refine sum_congr rfl fun j _ => ?_
        rw [hc, mul_sum]; exact sum_congr rfl fun m _ => by ring
    _ = ∑ m, (starRingEnd ℂ) (v m) * ∑ j, coef v j * chi j m := by
        rw [sum_comm]; exact sum_congr rfl fun m _ => by rw [mul_sum]
    _ = ∑ m, (starRingEnd ℂ) (v m) * ((n : ℂ) * v m) := by
        refine sum_congr rfl fun m _ => ?_
        congr 1
        have hn : (n : ℂ) ≠ 0 := by exact_mod_cast NeZero.ne n
        have := h m
        rw [this, ← mul_assoc, mul_inv_cancel₀ hn, one_mul]
    _ = (n : ℂ) * ∑ m, v m * (starRingEnd ℂ) (v m) := by
        rw [mul_sum]; exact sum_congr rfl fun m _ => by ring

/-- 20:C5 — mean-square flatness: for a mean-removed vector `u ≠ 0` on the cycle (`Σ_m u(m) = 0`), the
normalised correlations `r_j = |⟨u, χ_j⟩|/(‖u‖ ‖χ_j‖)` with the nonconstant modes satisfy `Σ_{j≠0} r_j² = 1`
exactly, so their mean square over the `n − 1 = p − 2` nonconstant modes is `1/(p − 2)`: the root-mean-square
correlation is `1/√(p − 2)`. -/
theorem flatness (u : ZMod n → ℂ) (hmean : ∑ m, u m = 0) (hu : u ≠ 0) :
    ∑ j ∈ univ.erase 0, normSq (coef u j) / (n * ∑ m, normSq (u m)) = 1 ∧
    (∑ j ∈ univ.erase 0, normSq (coef u j) / (n * ∑ m, normSq (u m))) / ((n : ℝ) - 1) = 1 / ((n : ℝ) - 1) := by
  have hpos : 0 < ∑ m, normSq (u m) := by
    obtain ⟨m, hm⟩ : ∃ m, u m ≠ 0 := by
      by_contra h; push Not at h; exact hu (funext h)
    exact sum_pos' (fun m _ => normSq_nonneg _) ⟨m, mem_univ _, normSq_pos.2 hm⟩
  have hn : (0 : ℝ) < n := by exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne n)
  have hden : (n : ℝ) * ∑ m, normSq (u m) ≠ 0 := (mul_pos hn hpos).ne'
  have h0 : coef u 0 = 0 := by rw [(chi_inversion u).2.1, hmean]
  have hsplit := sum_erase_add univ (fun j => normSq (coef u j)) (mem_univ 0)
  rw [chi_parseval, h0, normSq_zero, add_zero] at hsplit
  have h1 : ∑ j ∈ univ.erase 0, normSq (coef u j) / (n * ∑ m, normSq (u m)) = 1 := by
    rw [← sum_div, hsplit, div_self hden]
  exact ⟨h1, by rw [h1]⟩

end characters

section eigen

/-- 20:E12, 20:E1 — the multiplicative characters of the shell are eigenvectors of the scale-shift in the
abstract reading: `χ(g^r x) = χ(g)^r χ(x)` for every `χ : F^× →* ℂ^×`. -/
theorem character_eigen {F : Type*} [Field F] (χ : Fˣ →* ℂˣ) (g x : Fˣ) (r : ℕ) : χ (g ^ r * x) = χ g ^ r * χ x := by
  rw [map_mul, map_pow]

end eigen

/-! ## The resonance: the von Mangoldt weight (row C2) -/

section resonance

open ArithmeticFunction Finset

/-- 20:C2 — `Λ = μ ∗ log` exactly on the divisor lattice: `Λ(n) = Σ_{d ∣ n} μ(d) log(n/d)`; and the support of
`Λ` is the prime powers. (Hardy's limit `R_L → (φ(n)/n) Λ(n)` is the import A3.) -/
theorem vonMangoldt_moebius (m : ℕ) :
    vonMangoldt m = ∑ d ∈ m.divisors, (moebius d : ℝ) * Real.log ((m : ℝ) / d) ∧
    (vonMangoldt m ≠ 0 ↔ IsPrimePow m) := by
  refine ⟨?_, vonMangoldt_ne_zero_iff⟩
  rw [← moebius_mul_log_eq_vonMangoldt, mul_apply,
    Nat.sum_divisorsAntidiagonal (fun a b => (moebius : ArithmeticFunction ℝ) a * ArithmeticFunction.log b)]
  refine sum_congr rfl fun d hd => ?_
  simp only [intCoe_apply, log_apply]
  rw [Nat.cast_div (Nat.dvd_of_mem_divisors hd) (by
    exact_mod_cast (Nat.pos_of_mem_divisors hd).ne')]

end resonance

/-! ## The strip (20:D8): the Euler product excludes zeros with real part at least one, and the functional equation
confines the nontrivial zeros to the open strip, in orbits of the Klein four-group `s ↦ 1 − s`, `s ↦ s̄` (13 October 2026). -/
section strip

open ComplexConjugate

/-- A zero of `ζ` with real part at most zero is a trivial zero `−2(n+1)`: at `s' = 1 − s` the functional equation reads
`ζ s = 2 (2π)^{−s'} Γ(s') cos(π s'/2) ζ(s')` with `Re s' ≥ 1`, where `ζ(s') ≠ 0` (the Euler product), so `cos(π s'/2) = 0`,
`s'` an odd integer and `s` an even integer `≤ 0`; `s = 0` is excluded by `ζ 0 = −1/2`. -/
theorem zero_re_nonpos_trivial {s : ℂ} (h0 : riemannZeta s = 0) (hre : s.re ≤ 0) :
    ∃ n : ℕ, s = -2 * (n + 1) := by
  have hs0 : s ≠ 0 := fun h => by rw [h, riemannZeta_zero] at h0; norm_num at h0
  set s' := 1 - s with hs'
  have hre' : 1 ≤ s'.re := by simp only [hs', Complex.sub_re, Complex.one_re]; linarith
  have hne : ∀ n : ℕ, s' ≠ -n := fun n h => by
    have := congrArg Complex.re h
    simp only [Complex.neg_re, Complex.natCast_re] at this
    have : (0 : ℝ) ≤ n := Nat.cast_nonneg n
    linarith
  have hne1 : s' ≠ 1 := fun h => hs0 (by rw [hs'] at h; linear_combination -h)
  have hfe := riemannZeta_one_sub hne hne1
  have h1s : 1 - s' = s := by rw [hs']; ring
  rw [h1s, h0] at hfe
  have hz : riemannZeta s' ≠ 0 := riemannZeta_ne_zero_of_one_le_re hre'
  have hΓ : Complex.Gamma s' ≠ 0 := Complex.Gamma_ne_zero_of_re_pos (by linarith)
  have hpow : (2 * (Real.pi : ℂ)) ^ (-s') ≠ 0 := by
    rw [Complex.cpow_ne_zero_iff]; left
    exact mul_ne_zero two_ne_zero (Complex.ofReal_ne_zero.2 Real.pi_ne_zero)
  have hcos : Complex.cos ((Real.pi : ℂ) * s' / 2) = 0 := by
    have h := hfe.symm
    simp only [mul_eq_zero, two_ne_zero, false_or, hpow, hΓ, hz, or_false] at h
    exact h
  obtain ⟨k, hk⟩ := Complex.cos_eq_zero_iff.1 hcos
  have hπ : (Real.pi : ℂ) ≠ 0 := Complex.ofReal_ne_zero.2 Real.pi_ne_zero
  have hs'k : s' = 2 * k + 1 := by
    have : (Real.pi : ℂ) * s' = (Real.pi : ℂ) * (2 * k + 1) := by linear_combination 2 * hk
    exact mul_left_cancel₀ hπ this
  have hsk : s = -2 * k := by rw [← h1s, hs'k]; ring
  have hk0 : 0 ≤ k := by
    have := congrArg Complex.re hsk
    simp only [neg_mul, Complex.neg_re, Complex.mul_re, Complex.re_ofNat, Complex.im_ofNat, Complex.intCast_re, Complex.intCast_im, mul_zero, sub_zero] at this
    have : (0 : ℝ) ≤ k := by linarith
    exact_mod_cast this
  have hk1 : k ≠ 0 := fun h => hs0 (by rw [hsk, h]; simp)
  refine ⟨(k - 1).toNat, ?_⟩
  have hk1' : 1 ≤ k := by omega
  have : ((k - 1).toNat : ℤ) = k - 1 := Int.toNat_of_nonneg (by omega)
  rw [hsk]
  have hcast : ((((k - 1).toNat : ℕ) : ℂ)) = (k : ℂ) - 1 := by
    rw [← Int.cast_natCast, this]; push_cast; ring
  rw [hcast]; ring

/-- 20:D8, the strip: a nontrivial zero of `ζ` lies in the open strip `0 < Re s < 1`, and its Klein-four orbit under
`s ↦ 1 − s` and `s ↦ s̄` consists of zeros: `Re s < 1` by the Euler product (`riemannZeta_ne_zero_of_one_le_re`),
`0 < Re s` by the functional equation with the Euler product on the reflected side, `ζ(1 − s) = 0` by the functional
equation (`riemannZeta_one_sub`) and `ζ(s̄) = 0` by `riemannZeta_conj`. -/
theorem zeros_in_strip {s : ℂ} (h0 : riemannZeta s = 0) (htriv : ¬∃ n : ℕ, s = -2 * (n + 1)) (h1 : s ≠ 1) :
    0 < s.re ∧ s.re < 1 ∧ riemannZeta (1 - s) = 0 ∧ riemannZeta (conj s) = 0 := by
  have hlt : s.re < 1 := by
    by_contra h
    exact riemannZeta_ne_zero_of_one_le_re (not_lt.1 h) h0
  have hpos : 0 < s.re := by
    by_contra h
    exact htriv (zero_re_nonpos_trivial h0 (not_lt.1 h))
  refine ⟨hpos, hlt, ?_, ?_⟩
  · have hne : ∀ n : ℕ, s ≠ -n := fun n h => by
      have := congrArg Complex.re h
      simp only [Complex.neg_re, Complex.natCast_re] at this
      have : (0 : ℝ) ≤ n := Nat.cast_nonneg n
      linarith
    rw [riemannZeta_one_sub hne h1, h0, mul_zero]
  · rw [riemannZeta_conj, h0, map_zero]

end strip

/-! ## Turing's count (20:F1; 15 October 2026): the completed zeta is real on the line, and a sign change of it between
two heights is a zero of `ζ` on the line between them — the analytic half of the certificate, whose finite half is
`FRC.Horizon.turing_chain`, `turing_equal`, `turing_phantom`. -/
section turing

open ComplexConjugate

theorem line_ne_zero (t : ℝ) : (1 / 2 + t * Complex.I : ℂ) ≠ 0 := by
  intro h
  have := congrArg Complex.re h
  simp at this

theorem line_ne_one (t : ℝ) : (1 / 2 + t * Complex.I : ℂ) ≠ 1 := by
  intro h
  have := congrArg Complex.re h
  norm_num at this

/-- The factor `π^{−w/2} Γ(w/2)` does not vanish for `Re w > 0`. -/
theorem scale_ne_zero {w : ℂ} (hw : 0 < w.re) :
    ((Real.pi : ℂ) ^ (-w / 2) * Complex.Gamma (w / 2)) ≠ 0 := by
  refine mul_ne_zero ?_ ?_
  · exact Complex.cpow_ne_zero_iff.mpr (Or.inl (by exact_mod_cast Real.pi_ne_zero))
  · exact Complex.Gamma_ne_zero_of_re_pos (by simp; linarith)

/-- 20:F1 — `Λ(w) = ζ(w) π^{−w/2} Γ(w/2)` for `Re w > 0` (Mathlib's `riemannZeta_eq_completedRiemannZeta₀` with
`completedRiemannZeta_eq`). -/
theorem completed_eq_mul {w : ℂ} (hw : 0 < w.re) :
    completedRiemannZeta w = riemannZeta w * ((Real.pi : ℂ) ^ (-w / 2) * Complex.Gamma (w / 2)) := by
  have hw0 : w ≠ 0 := fun h => by simp [h] at hw
  rw [riemannZeta_eq_completedRiemannZeta₀ hw0, ← completedRiemannZeta_eq, div_mul_cancel₀ _ (scale_ne_zero hw)]

/-- 20:F1 — `Λ(s̄) = conj Λ(s)` for `Re s > 0`: `ζ`, `Γ` and the real power commute with conjugation. -/
theorem completed_conj {s : ℂ} (hs : 0 < s.re) :
    completedRiemannZeta (conj s) = conj (completedRiemannZeta s) := by
  have hs' : 0 < (conj s).re := by simpa using hs
  rw [completed_eq_mul hs', completed_eq_mul hs, map_mul, map_mul, riemannZeta_conj, ← Complex.Gamma_conj]
  congr 2
  · have h1 : (-(conj s) / 2 : ℂ) = conj (-s / 2) := by rw [map_div₀, map_neg, map_ofNat]
    have hπ : (Real.pi : ℂ).arg ≠ Real.pi := by
      rw [Complex.arg_ofReal_of_nonneg Real.pi_pos.le]; exact Real.pi_ne_zero.symm
    rw [h1, Complex.cpow_conj _ _ hπ, Complex.conj_ofReal]
  · congr 1; rw [map_div₀, map_ofNat]

/-- 20:F1 — the completed zeta is real on the line: `1 − s = s̄` there, so `Λ(s) = Λ(1 − s) = Λ(s̄) = conj Λ(s)`. -/
theorem completed_im_line (t : ℝ) : (completedRiemannZeta (1 / 2 + t * Complex.I)).im = 0 := by
  set s : ℂ := 1 / 2 + t * Complex.I with hs
  have hre : 0 < s.re := by simp [hs]
  have h1 : conj s = 1 - s := by
    apply Complex.ext <;> simp [hs]; norm_num
  have h2 : conj (completedRiemannZeta s) = completedRiemannZeta s := by
    rw [← completed_conj hre, h1, completedRiemannZeta_one_sub]
  exact Complex.conj_eq_iff_im.mp h2

/-- The real part of the completed zeta along the line is continuous in the height. -/
theorem continuous_line_re :
    Continuous (fun t : ℝ => (completedRiemannZeta (1 / 2 + t * Complex.I)).re) := by
  have hline : Continuous (fun t : ℝ => (1 / 2 + t * Complex.I : ℂ)) := by fun_prop
  refine Complex.continuous_re.comp (continuous_iff_continuousAt.mpr fun t => ?_)
  exact ContinuousAt.comp (f := fun t : ℝ => (1 / 2 + t * Complex.I : ℂ)) (g := completedRiemannZeta)
    (differentiableAt_completedZeta (line_ne_zero t) (line_ne_one t)).continuousAt hline.continuousAt

/-- 20:F1 — Turing's count, the analytic clause: a sign change of `Re Λ(1/2 + it)` between the heights `a < b` is
a zero of `ζ` on the line strictly between them (the intermediate value theorem on the real function
`completed_im_line`, divided by the non-vanishing factor `scale_ne_zero`). Each certified sign change of the
package's main sum is such a zero; the finite count is `FRC.Horizon.turing_chain`. -/
theorem zero_of_sign_change {a b : ℝ} (hab : a < b)
    (h : (completedRiemannZeta (1 / 2 + a * Complex.I)).re * (completedRiemannZeta (1 / 2 + b * Complex.I)).re < 0) :
    ∃ t : ℝ, a < t ∧ t < b ∧ riemannZeta (1 / 2 + t * Complex.I) = 0 := by
  set f : ℝ → ℝ := fun t => (completedRiemannZeta (1 / 2 + t * Complex.I)).re with hf
  have hc : ContinuousOn f (Set.Icc a b) := continuous_line_re.continuousOn
  have key : ∀ t : ℝ, f t = 0 → riemannZeta (1 / 2 + t * Complex.I) = 0 := by
    intro t ht
    have hre : 0 < (1 / 2 + t * Complex.I : ℂ).re := by simp
    have hΛ : completedRiemannZeta (1 / 2 + t * Complex.I) = 0 :=
      Complex.ext (by simpa [hf] using ht) (by simpa using completed_im_line t)
    have := completed_eq_mul hre
    rw [hΛ] at this
    exact (mul_eq_zero.mp this.symm).resolve_right (scale_ne_zero hre)
  rcases mul_neg_iff.mp h with ⟨ha, hb⟩ | ⟨ha, hb⟩
  · obtain ⟨t, ⟨hta, htb⟩, hft⟩ := intermediate_value_Ioo' hab.le hc ⟨hb, ha⟩
    exact ⟨t, hta, htb, key t hft⟩
  · obtain ⟨t, ⟨hta, htb⟩, hft⟩ := intermediate_value_Ioo hab.le hc ⟨ha, hb⟩
    exact ⟨t, hta, htb, key t hft⟩

end turing

end FRC.Chart
