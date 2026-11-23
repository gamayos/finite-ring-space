import Mathlib
import FrcMathlib.Theme.Horizon
import FrcMathlib.Theme.Chart
import FrcMathlib.Keys.Chart
import FrcMathlib.Keys.Horizon

/-!
# 20-rh — Riemann Hypothesis over Finite Holographic Substrate: the shell predicates in Lean (2026-09-19)

The exact arithmetic of the paper's block B, the constants of its Subject register, and the two character
readings of the shell theorem — rows B2, B4–B10 (B8's shell clauses), C2's identity `Λ = μ ∗ log`, C5, E1's shell
clause, E12 (i) and (iii), and E13's orthogonality, inversion and Parseval — proved for every shell: an arbitrary
finite field `F` with `4κ + 1` elements and a primitive root `g`, or `ZMod p` where the prime is needed, and, for
the analytic identities, over any integral domain or over `ℂ`; the laboratory pair `(13, 233)` of B1 decided.
Classical (tier 2) on Mathlib's hierarchy; the shell arithmetic is also in the core (`FrcCore/Rh.lean`) with no axioms.

Since the ledger migration (task LM36, 7 October 2026) the theorems live in the themes: the exact shell arithmetic in
the horizon theme (`FrcMathlib/Theme/Horizon.lean`, `FRC.HorizonML`), and the complex characters of the cycle, the
characters as eigenvectors and the von Mangoldt weight in the chart theme (`FrcMathlib/Theme/Chart.lean`, `FRC.Chart`).
The old names below are aliases, and the predicate declarations are the aliases of their keys.
-/

namespace FRC.Rh

/-! ## Old names (ledger migration, task LM36): the theorems moved to the horizon theme (`FRC.HorizonML`) and the chart
theme (`FRC.Chart`), each under its old name -/

open Finset

section shell

variable {F : Type*} [Field F] [Fintype F] [DecidableEq F]

/-- 20:B4 — 20-rh's name; the theorem is `FRC.HorizonML.zero_slot` (task LM36). -/
theorem zero_slot :
    (∀ k, 1 ≤ k → k ≤ Fintype.card F - 2 → ∑ x : Fˣ, ((x : F) ^ k) = 0) ∧
    ∑ x : Fˣ, ((x : F) ^ (Fintype.card F - 1)) = -1 := by
  apply FRC.HorizonML.zero_slot <;> assumption

omit [DecidableEq F] in
/-- 20:B5 — 20-rh's name; the theorem is `FRC.HorizonML.slot_complementarity` (task LM36). -/
theorem slot_complementarity (g : F) (hg : IsPrimitiveRoot g (Fintype.card F - 1)) :
    Set.InjOn (fun k : ℕ => -(g ^ k)) (Set.Icc 1 (Fintype.card F - 2)) ∧
    (fun k : ℕ => -(g ^ k)) '' Set.Icc 1 (Fintype.card F - 2) = {y : F | y ≠ 0 ∧ y ≠ -1} := by
  apply FRC.HorizonML.slot_complementarity <;> assumption

end shell

section ramanujan

variable {R : Type*} [CommRing R] [IsDomain R]

/-- 20:B7 — 20-rh's name; the theorem is `FRC.HorizonML.ramanujan_sum` (task LM36). -/
theorem ramanujan_sum {p : ℕ} (hp : 0 < p) {ω : R} (hω : IsPrimitiveRoot ω p) (n : ℕ) :
    (¬ p ∣ n → ∑ a ∈ Ico 1 p, ω ^ (a * n) = -1) ∧
    (p ∣ n → ∑ a ∈ Ico 1 p, ω ^ (a * n) = ((p - 1 : ℕ) : R)) := by
  apply FRC.HorizonML.ramanujan_sum <;> assumption

end ramanujan

section constants

variable {F : Type*} [Field F] [Fintype F]

/-- 20:B8, 20:B10 — 20-rh's name; the theorem is `FRC.HorizonML.half_turn` (task LM36). -/
theorem half_turn (κ : ℕ) (hκ : Fintype.card F = 4 * κ + 1) :
    (2 : F) * ((2 * κ : ℕ) : F) = -1 ∧ (2 : F) * ((2 * κ + 1 : ℕ) : F) = 1 ∧
    ((2 * κ + 1 : ℕ) : F) = -((2 * κ : ℕ) : F) ∧ (2 : F)⁻¹ = ((2 * κ + 1 : ℕ) : F) := by
  apply FRC.HorizonML.half_turn <;> assumption

/-- 20:B10 — 20-rh's name; the theorem is `FRC.HorizonML.subject_constants` (task LM36). -/
theorem subject_constants (κ : ℕ) (hκ : Fintype.card F = 4 * κ + 1) (g : F)
    (hg : IsPrimitiveRoot g (Fintype.card F - 1)) :
    (2 : F) * ((2 * κ : ℕ) : F) = -1 ∧ g ^ (3 * κ) = -(g ^ κ) ∧ (g ^ (3 * κ)) ^ 2 = -1 ∧
    g ^ (2 * κ) = -1 ∧ ∀ m : ℕ, m % 2 = 1 → (g ^ m) ^ (m * (2 * κ)) = -1 := by
  apply FRC.HorizonML.subject_constants <;> assumption

/-- 20:B10 [value] — 20-rh's name; the theorem is `FRC.HorizonML.constants13` (task LM36). -/
theorem constants13 :
    (2 : ZMod 13) * 6 = -1 ∧ (2 : ZMod 13) ^ 9 = 5 ∧ (5 : ZMod 13) ^ 2 = -1 ∧ (2 : ZMod 13) ^ 5 = 6 ∧
    (2 : ZMod 13) ^ 6 = -1 ∧ (6 : ZMod 13) ^ (5 * 6) = -1 := by
  apply FRC.HorizonML.constants13 <;> assumption

end constants

section extension

variable {F : Type*} [Field F] (ν : F)

local notation "K" => QuadraticAlgebra F ν 0

/-- 20:B9 — 20-rh's name; the theorem is `FRC.HorizonML.klein_four` (task LM36). -/
theorem klein_four (z : K) :
    star (star z) = z ∧ (1 - (1 - z)) = z ∧ star (1 - z) = 1 - star z := by
  apply FRC.HorizonML.klein_four <;> assumption

/-- 20:B9 — 20-rh's name; the theorem is `FRC.HorizonML.fixed_frobenius` (task LM36). -/
theorem fixed_frobenius (h2 : (2 : F) ≠ 0) (z : K) : star z = z ↔ z.im = 0 := by
  apply FRC.HorizonML.fixed_frobenius <;> assumption

/-- 20:B8, 20:B9 — 20-rh's name; the theorem is `FRC.HorizonML.trace_eq_one_iff` (task LM36). -/
theorem trace_eq_one_iff (h2 : (2 : F) ≠ 0) (z : K) :
    (QuadraticAlgebra.trace z = 1 ↔ z.re = 2⁻¹) ∧ (1 - star z = z ↔ z.re = 2⁻¹) := by
  apply FRC.HorizonML.trace_eq_one_iff <;> assumption

/-- 20:B9 — 20-rh's name; the theorem is `FRC.HorizonML.fixed_half_turn` (task LM36). -/
theorem fixed_half_turn (h2 : (2 : F) ≠ 0) (z : K) :
    (1 - z = z ↔ z = ⟨2⁻¹, 0⟩) ∧ (z.im = 0 ∧ z.re = 2⁻¹ ↔ z = ⟨2⁻¹, 0⟩) := by
  apply FRC.HorizonML.fixed_half_turn <;> assumption

/-- 20:B8 — 20-rh's name; the theorem is `FRC.HorizonML.norm_on_line` (task LM36). -/
theorem norm_on_line (z : K) (hz : z.re = 2⁻¹) :
    QuadraticAlgebra.norm z = (4 : F)⁻¹ - ν * z.im ^ 2 := by
  apply FRC.HorizonML.norm_on_line <;> assumption

/-- 20:E12, 20:B8 — 20-rh's name; the theorem is `FRC.HorizonML.readout_on_line` (task LM36). -/
theorem readout_on_line (h2 : (2 : F) ≠ 0) (θ : F) :
    QuadraticAlgebra.trace (FRC.HorizonML.readout ν θ) = 1 ∧ (FRC.HorizonML.readout ν θ).re = 2⁻¹ ∧
    Function.Injective (FRC.HorizonML.readout ν) := by
  apply FRC.HorizonML.readout_on_line <;> assumption

variable [Fintype F] [DecidableEq F]

/-- 20:B8 — 20-rh's name; the theorem is `FRC.HorizonML.card_critical_line` (task LM36). -/
theorem card_critical_line (h2 : (2 : F) ≠ 0) :
    (univ.filter (fun z : K => QuadraticAlgebra.trace z = 1)).card = Fintype.card F := by
  apply FRC.HorizonML.card_critical_line <;> assumption

omit [DecidableEq F] in
/-- 20:E12 — 20-rh's name; the theorem is `FRC.HorizonML.readout_slot_index` (task LM36). -/
theorem readout_slot_index (g : F) (hg : IsPrimitiveRoot g (Fintype.card F - 1)) (k : ℕ)
    (hk1 : 1 ≤ k) (hk2 : k ≤ Fintype.card F - 2) : -(g ^ k) ≠ 0 ∧ -(g ^ k) ≠ -1 := by
  apply FRC.HorizonML.readout_slot_index <;> assumption

end extension

section frobenius

variable {F : Type*} [Field F] [Fintype F] [DecidableEq F] {p : ℕ} [hp : Fact p.Prime] [CharP F p]
  (hcard : Fintype.card F = p) (ν : F) [hν : Fact (¬ IsSquare ν)]

local notation "K" => QuadraticAlgebra F ν 0

omit [DecidableEq F] in
include hcard in
/-- 20:B6 — 20-rh's name; the theorem is `FRC.HorizonML.frobenius_eq_star` (task LM36). -/
theorem frobenius_eq_star (z : K) : z ^ p = star z := by
  apply FRC.HorizonML.frobenius_eq_star <;> assumption

omit [DecidableEq F] in
include hcard in
/-- 20:B6 — 20-rh's name; the theorem is `FRC.HorizonML.norm_eq_pow` (task LM36). -/
theorem norm_eq_pow (z : K) : algebraMap F K (QuadraticAlgebra.norm z) = z ^ (p + 1) := by
  apply FRC.HorizonML.norm_eq_pow <;> assumption

include hcard in
/-- 20:B6 — 20-rh's name; the theorem is `FRC.HorizonML.phase_circle` (task LM36). -/
theorem phase_circle :
    (univ.filter (fun z : K => QuadraticAlgebra.norm z = 1)).card = p + 1 ∧
    ∀ z : K, QuadraticAlgebra.norm z = 1 → star z = z⁻¹ := by
  apply FRC.HorizonML.phase_circle <;> assumption

omit [DecidableEq F] in
include hcard in
/-- 20:B6 — 20-rh's name; the theorem is `FRC.HorizonML.quarter_turn_off_circle` (task LM36). -/
theorem quarter_turn_off_circle (i : F) (hi : i ^ 2 = -1) :
    star (algebraMap F K i) = algebraMap F K i ∧ QuadraticAlgebra.norm (algebraMap F K i) = -1 ∧
    QuadraticAlgebra.norm (algebraMap F K i) ≠ 1 := by
  apply FRC.HorizonML.quarter_turn_off_circle <;> assumption

end frobenius

section spectrum

variable {F : Type*} [Field F] [Fintype F] [DecidableEq F]

/-- 20:E1, 20:E12 — 20-rh's name; the theorem is `FRC.HorizonML.scale_shift` (task LM36). -/
theorem scale_shift (g : F) (hg : IsPrimitiveRoot g (Fintype.card F - 1)) (r : ℕ) :
    Function.Bijective (fun x : Fˣ => (Units.mk0 g (hg.ne_zero (Nat.sub_ne_zero_of_lt Fintype.one_lt_card))) ^ r * x) ∧
    (∀ (k : ℕ) (x : F), (g ^ r * x) ^ k = (g ^ r) ^ k * x ^ k) ∧
    (univ.filter (fun x : Fˣ => g ^ r * (x : F) = x)).card =
      if (Fintype.card F - 1) ∣ r then Fintype.card F - 1 else 0 := by
  apply FRC.HorizonML.scale_shift <;> assumption

/-- 20:E12, 20:E13 — 20-rh's name; the theorem is `FRC.HorizonML.power_characters_not_orthonormal` (task LM36). -/
theorem power_characters_not_orthonormal (h2 : (2 : F) ≠ 0) (j : ℕ) :
    ∑ x : Fˣ, ((x : F) ^ j * (x : F) ^ j) ≠ 1 := by
  apply FRC.HorizonML.power_characters_not_orthonormal <;> assumption

omit [Fintype F] [DecidableEq F] in
/-- 20:E12, 20:E1 — 20-rh's name; the theorem is `FRC.Chart.character_eigen` (task LM36). -/
theorem character_eigen (χ : Fˣ →* ℂˣ) (g x : Fˣ) (r : ℕ) : χ (g ^ r * x) = χ g ^ r * χ x := by
  apply FRC.Chart.character_eigen <;> assumption

end spectrum

section characters

open Complex

variable {n : ℕ} [NeZero n]

/-- 20:E13 — 20-rh's name; the theorem is `FRC.Chart.chi_orthogonal` (task LM36). -/
theorem chi_orthogonal (j k : ZMod n) :
    ∑ m, FRC.Chart.chi j m * (starRingEnd ℂ) (FRC.Chart.chi k m) = if j = k then (n : ℂ) else 0 := by
  apply FRC.Chart.chi_orthogonal <;> assumption

/-- 20:E12, 20:E1 — 20-rh's name; the theorem is `FRC.Chart.chi_shift` (task LM36). -/
theorem chi_shift (j m : ZMod n) :
    FRC.Chart.chi j (m + 1) = ZMod.stdAddChar j * FRC.Chart.chi j m ∧
    ZMod.stdAddChar (j : ZMod n) = Complex.exp (2 * Real.pi * I * j.val / n) := by
  apply FRC.Chart.chi_shift <;> assumption

/-- 20:E12, 20:E13 — 20-rh's name; the theorem is `FRC.Chart.chi_inversion` (task LM36). -/
theorem chi_inversion (v : ZMod n → ℂ) :
    (∀ m, v m = (n : ℂ)⁻¹ * ∑ j, FRC.Chart.coef v j * FRC.Chart.chi j m) ∧ FRC.Chart.coef v 0 = ∑ m, v m ∧
    ∀ m, v m - (n : ℂ)⁻¹ * ∑ m', v m' = (n : ℂ)⁻¹ * ∑ j ∈ univ.erase 0, FRC.Chart.coef v j * FRC.Chart.chi j m := by
  apply FRC.Chart.chi_inversion <;> assumption

/-- 20:E13, 20:C5 — 20-rh's name; the theorem is `FRC.Chart.chi_parseval` (task LM36). -/
theorem chi_parseval (v : ZMod n → ℂ) :
    ∑ j, normSq (FRC.Chart.coef v j) = n * ∑ m, normSq (v m) := by
  apply FRC.Chart.chi_parseval <;> assumption

/-- 20:C5 — 20-rh's name; the theorem is `FRC.Chart.flatness` (task LM36). -/
theorem flatness (u : ZMod n → ℂ) (hmean : ∑ m, u m = 0) (hu : u ≠ 0) :
    ∑ j ∈ univ.erase 0, normSq (FRC.Chart.coef u j) / (n * ∑ m, normSq (u m)) = 1 ∧
    (∑ j ∈ univ.erase 0, normSq (FRC.Chart.coef u j) / (n * ∑ m, normSq (u m))) / ((n : ℝ) - 1) = 1 / ((n : ℝ) - 1) := by
  apply FRC.Chart.flatness <;> assumption

end characters

section window

open Complex Finset

/-- 20:D14 — 20-rh's name; the theorem is `FRC.Chart.mean_free` (21 November 2026). -/
theorem mean_free (H : ℕ) (hH : 0 < H) (w : ℕ → ℝ) :
    ∑ n ∈ Icc 1 H, (w n - (∑ m ∈ Icc 1 H, w m) / H) = 0 :=
  FRC.Chart.mean_free H hH w

/-- 20:D14 — 20-rh's name; the theorem is `FRC.Chart.spectrum_even` (21 November 2026). -/
theorem spectrum_even (H : ℕ) (a : ℕ → ℝ) (σ t : ℝ) :
    FRC.Chart.spectrum H a σ (-t) = FRC.Chart.spectrum H a σ t :=
  FRC.Chart.spectrum_even H a σ t

/-- 20:D15 — 20-rh's name; the theorem is `FRC.Chart.mode_norm` (21 November 2026). -/
theorem mode_norm {n : ℕ} (hn : 0 < n) (σ t : ℝ) :
    ‖(n : ℂ) ^ ((σ : ℂ) + (t : ℂ) * I)‖ = (n : ℝ) ^ σ :=
  FRC.Chart.mode_norm hn σ t

/-- 20:D15 — 20-rh's name; the theorem is `FRC.Chart.spectrum_le` (21 November 2026). -/
theorem spectrum_le (H : ℕ) (a : ℕ → ℝ) (σ t : ℝ) :
    FRC.Chart.spectrum H a σ t ≤ ∑ n ∈ Icc 1 H, |a n| * (n : ℝ) ^ σ :=
  FRC.Chart.spectrum_le H a σ t

/-- 20:D17 — 20-rh's name; the theorem is `FRC.Chart.Perron.step_bound` (22 November 2026). -/
theorem step_bound {T u : ℝ} (hT : 0 < T) (hu : u ≠ 0) :
    ‖FRC.Chart.Perron.step T u - (if 0 < u then 1 else 0)‖ ≤ Real.exp (u / 2) / (Real.pi * T * |u|) :=
  FRC.Chart.Perron.step_bound hT hu

/-- 20:D17 — 20-rh's name; the theorem is `FRC.Chart.Perron.count_bound` (22 November 2026). -/
theorem count_bound (s : Finset ℕ) (w : ℕ → ℝ) {T x : ℝ} (hT : 0 < T) (hx : 0 < x)
    (hs : ∀ n ∈ s, 0 < n) (hne : ∀ n ∈ s, (n : ℝ) ≠ x) :
    ‖FRC.Chart.Perron.count s w T x - ((∑ n ∈ s.filter (fun n : ℕ => (n : ℝ) < x), w n : ℝ) : ℂ)‖ ≤
      1 / (Real.pi * T) * ∑ n ∈ s, |w n| * (Real.sqrt (x / n) / |Real.log (x / n)|) :=
  FRC.Chart.Perron.count_bound s w hT hx hs hne

end window

section resonance

open ArithmeticFunction

/-- 20:C2 — 20-rh's name; the theorem is `FRC.Chart.vonMangoldt_moebius` (task LM36). -/
theorem vonMangoldt_moebius (m : ℕ) :
    vonMangoldt m = ∑ d ∈ m.divisors, (moebius d : ℝ) * Real.log ((m : ℝ) / d) ∧
    (vonMangoldt m ≠ 0 ↔ IsPrimePow m) := by
  apply FRC.Chart.vonMangoldt_moebius <;> assumption

end resonance

section strip

open ComplexConjugate

/-- 20:D8 — 20-rh's name; the theorem is `FRC.Chart.zeros_in_strip`: a nontrivial zero of `ζ` lies in the open strip
`0 < Re s < 1`, and `1 − s` and `s̄` are zeros. -/
theorem zeros_in_strip {s : ℂ} (h0 : riemannZeta s = 0) (htriv : ¬∃ n : ℕ, s = -2 * (n + 1)) (h1 : s ≠ 1) :
    0 < s.re ∧ s.re < 1 ∧ riemannZeta (1 - s) = 0 ∧ riemannZeta (conj s) = 0 :=
  FRC.Chart.zeros_in_strip h0 htriv h1

/-- 20:F1 — 20-rh's name; the theorem is `FRC.Chart.zero_of_sign_change`: a sign change of the real completed zeta
`Re Λ(1/2 + it)` between two heights is a zero of `ζ` on the line between them (Turing's count, the analytic clause). -/
theorem zero_of_sign_change {a b : ℝ} (hab : a < b)
    (h : (completedRiemannZeta (1 / 2 + a * Complex.I)).re * (completedRiemannZeta (1 / 2 + b * Complex.I)).re < 0) :
    ∃ t : ℝ, a < t ∧ t < b ∧ riemannZeta (1 / 2 + t * Complex.I) = 0 :=
  FRC.Chart.zero_of_sign_change hab h

end strip

section coincidence

/-- 20:B2 — 20-rh's name; the theorem is `FRC.HorizonML.window_readback` (task LM36). -/
theorem window_readback {q : ℕ} [NeZero q] {H : ℕ} (hH : H * H < q) :
    (∀ m, m ≤ H → ((m : ZMod q)).val = m) ∧
    ∀ a b, a ≤ H → b ≤ H → ((a : ZMod q) * b).val = a * b := by
  apply FRC.HorizonML.window_readback <;> assumption

/-- 20:B2 — 20-rh's name; the theorem is `FRC.HorizonML.prime_iff_window_irreducible` (task LM36). -/
theorem prime_iff_window_irreducible {q : ℕ} [NeZero q] {H : ℕ} (hH : H * H < q) (m : ℕ) (hm2 : 2 ≤ m)
    (hmH : m ≤ H) :
    Nat.Prime m ↔ ¬ ∃ a b, 2 ≤ a ∧ 2 ≤ b ∧ a ≤ H ∧ b ≤ H ∧ (a : ZMod q) * b = m := by
  apply FRC.HorizonML.prime_iff_window_irreducible <;> assumption

/-- 20-rh's name; the theorem is `FRC.HorizonML.sqrt_sq_lt_prime` (task LM36). -/
theorem sqrt_sq_lt_prime {p : ℕ} (hp : p.Prime) : Nat.sqrt p * Nat.sqrt p < p := by
  apply FRC.HorizonML.sqrt_sq_lt_prime <;> assumption

end coincidence

section lab

/-- 20:B1 [value] — 20-rh's name; the theorem is `FRC.HorizonML.lab_pair` (task LM36). -/
theorem lab_pair :
    13 * 13 < 233 ∧ Nat.gcd 12 232 = 4 ∧ (5 : ZMod 13) ^ 2 = -1 ∧ (89 : ZMod 233) ^ 2 = -1 ∧ ¬ 12 ∣ 232 := by
  apply FRC.HorizonML.lab_pair <;> assumption

/-- 20:B1 — 20-rh's name; the theorem is `FRC.HorizonML.no_cycle_projection` (task LM36). -/
theorem no_cycle_projection :
    ¬ ∃ f : Multiplicative (ZMod 232) →* Multiplicative (ZMod 12), Function.Surjective f := by
  apply FRC.HorizonML.no_cycle_projection <;> assumption

end lab

-- Ledger predicates of 20-rh (generated by make_predicates.py from docs/20-rh/20-rh-ledger.json; edit the ledger, not this section)
set_option linter.defProp false in
/-- 20:B1 (p20008) — The two frames and their alignment: the Carrier's chart $\F_\Omega$, held by no embedded observer, and the Subject $\Fp$, $\p^{2}<\Omega$. Shared: the origin, the unit and the rules of arithmetic, so the labels of the window and the counts of the modes. Not shared: the generator and the drive; the cycles admit no projection ($12\nmid232$). -/
def two_frames_alignment := @FRC.LedgerML.p20008
/-- 20:B2 (p20009) — Frame coincidence within the observational horizon $\q$, the largest label with $\q^{2}<\p$: for $n\le\q$ the residue $n$ is the same integer in $\Fp$ and $\F_\Omega$, and primality of $n$ equals irreducibility in the Subject chart; the Subject-realised primes $\Pi_\p$ are the primes to $\q$. A prime is a label on the prime meridian within the horizon. -/
theorem frame_coincidence_below_horizon : And (∀ {q : Nat} [@NeZero Nat (@MulZeroClass.toZero Nat Nat.instMulZeroClass) q] {H : Nat}, @LT.lt Nat instLTNat (@HMul.hMul Nat Nat Nat (@instHMul Nat instMulNat) H H) q → And (∀ (m : Nat), @LE.le Nat instLENat m H → @Eq Nat (@ZMod.val q (@Nat.cast (ZMod q) (@AddMonoidWithOne.toNatCast (ZMod q) (@AddGroupWithOne.toAddMonoidWithOne (ZMod q) (@Ring.toAddGroupWithOne (ZMod q) (@CommRing.toRing (ZMod q) (ZMod.commRing q))))) m)) m) (∀ (a b : Nat), @LE.le Nat instLENat a H → @LE.le Nat instLENat b H → @Eq Nat (@ZMod.val q (@HMul.hMul (ZMod q) (ZMod q) (ZMod q) (@instHMul (ZMod q) (@Distrib.toMul (ZMod q) (@instDistribOfSemiring (ZMod q) (@CommSemiring.toSemiring (ZMod q) (@CommRing.toCommSemiring (ZMod q) (ZMod.commRing q)))))) (@Nat.cast (ZMod q) (@AddMonoidWithOne.toNatCast (ZMod q) (@AddGroupWithOne.toAddMonoidWithOne (ZMod q) (@Ring.toAddGroupWithOne (ZMod q) (@CommRing.toRing (ZMod q) (ZMod.commRing q))))) a) (@Nat.cast (ZMod q) (@AddMonoidWithOne.toNatCast (ZMod q) (@AddGroupWithOne.toAddMonoidWithOne (ZMod q) (@Ring.toAddGroupWithOne (ZMod q) (@CommRing.toRing (ZMod q) (ZMod.commRing q))))) b))) (@HMul.hMul Nat Nat Nat (@instHMul Nat instMulNat) a b))) (∀ {q : Nat} [@NeZero Nat (@MulZeroClass.toZero Nat Nat.instMulZeroClass) q] {H : Nat}, @LT.lt Nat instLTNat (@HMul.hMul Nat Nat Nat (@instHMul Nat instMulNat) H H) q → ∀ (m : Nat), @LE.le Nat instLENat (@OfNat.ofNat Nat (nat_lit 2) (instOfNatNat (nat_lit 2))) m → @LE.le Nat instLENat m H → Iff (Nat.Prime m) (Not (∃ a b, And (@LE.le Nat instLENat (@OfNat.ofNat Nat (nat_lit 2) (instOfNatNat (nat_lit 2))) a) (And (@LE.le Nat instLENat (@OfNat.ofNat Nat (nat_lit 2) (instOfNatNat (nat_lit 2))) b) (And (@LE.le Nat instLENat a H) (And (@LE.le Nat instLENat b H) (@Eq (ZMod q) (@HMul.hMul (ZMod q) (ZMod q) (ZMod q) (@instHMul (ZMod q) (@Distrib.toMul (ZMod q) (@instDistribOfSemiring (ZMod q) (@CommSemiring.toSemiring (ZMod q) (@CommRing.toCommSemiring (ZMod q) (ZMod.commRing q)))))) (@Nat.cast (ZMod q) (@AddMonoidWithOne.toNatCast (ZMod q) (@AddGroupWithOne.toAddMonoidWithOne (ZMod q) (@Ring.toAddGroupWithOne (ZMod q) (@CommRing.toRing (ZMod q) (ZMod.commRing q))))) a) (@Nat.cast (ZMod q) (@AddMonoidWithOne.toNatCast (ZMod q) (@AddGroupWithOne.toAddMonoidWithOne (ZMod q) (@Ring.toAddGroupWithOne (ZMod q) (@CommRing.toRing (ZMod q) (ZMod.commRing q))))) b)) (@Nat.cast (ZMod q) (@AddMonoidWithOne.toNatCast (ZMod q) (@AddGroupWithOne.toAddMonoidWithOne (ZMod q) (@Ring.toAddGroupWithOne (ZMod q) (@CommRing.toRing (ZMod q) (ZMod.commRing q))))) m)))))))) :=
  @FRC.LedgerML.p20009
set_option linter.defProp false in
/-- 20:B4 (p20011) — Zero-slot: on every shell $Z_\p(k)=\sum_{x\in\Fx{\p}}x^{k}$ vanishes at every nonconstant mode, $1\le k\le\p-2$, and equals $-1$ at the constant mode; it uses no generator and holds on the chart of the Carrier. -/
def zero_slot_vanishing := @FRC.LedgerML.p20011
/-- 20:B10 (p20017) — The Subject constants on the shell: $\pi=2\kp$, $2\pi\equiv-1$, $\im=\gen^{-\kp}$, $\im^{2}\equiv-1$, $\E=\gen^{\,\im}$ on the odd lift, $\gen^{\,\pi}\equiv-1$, $\E^{\,\im\pi}\equiv-1$; on $\F_{13}$: $\gen=2$, $\im=5$, $\E=6$, $\pi=6$. -/
theorem subject_constants_shell : (∀ {F : Type u_1} [Field F] [Fintype F] (κ : ℕ), Fintype.card F = (4 : ℕ) * κ + (1 : ℕ) → ∀ (g : F), IsPrimitiveRoot g (Fintype.card F - (1 : ℕ)) → (2 : F) * ↑((2 : ℕ) * κ) = (-1 : F) ∧ g ^ ((3 : ℕ) * κ) = -g ^ κ ∧ (g ^ ((3 : ℕ) * κ)) ^ (2 : ℕ) = (-1 : F) ∧ g ^ ((2 : ℕ) * κ) = (-1 : F) ∧ ∀ (m : ℕ), m % (2 : ℕ) = (1 : ℕ) → (g ^ m) ^ (m * ((2 : ℕ) * κ)) = (-1 : F)) ∧ (2 : ZMod (13 : ℕ)) * (6 : ZMod (13 : ℕ)) = (-1 : ZMod (13 : ℕ)) ∧ (2 : ZMod (13 : ℕ)) ^ (9 : ℕ) = (5 : ZMod (13 : ℕ)) ∧ (5 : ZMod (13 : ℕ)) ^ (2 : ℕ) = (-1 : ZMod (13 : ℕ)) ∧ (2 : ZMod (13 : ℕ)) ^ (5 : ℕ) = (6 : ZMod (13 : ℕ)) ∧ (2 : ZMod (13 : ℕ)) ^ (6 : ℕ) = (-1 : ZMod (13 : ℕ)) ∧ (6 : ZMod (13 : ℕ)) ^ ((5 : ℕ) * (6 : ℕ)) = (-1 : ZMod (13 : ℕ)) :=
  @FRC.LedgerML.p20017
/-- 20:D14 (p20113) — The window's primes show the heights [chart]: for every window and weight the mean-removed weights sum to $0$, and $E(-t)=E(t)$. Reading [approx]: the five peaks at depth $13$, $39$, $173$ and $1551$ lie within $0.18$, $0.21$, $0.27$ and $0.21$ of the first five heights (A6); at depth $13$ no other of the $4095$ pairs of complementary subsets lies within $0.18$. -/
theorem window_heights : (∀ (H : ℕ), (0 : ℕ) < H → ∀ (w : ℕ → ℝ), ∑ n ∈ Finset.Icc (1 : ℕ) H, (w n - (∑ m ∈ Finset.Icc (1 : ℕ) H, w m) / ↑H) = (0 : ℝ)) ∧ ∀ (H : ℕ) (a : ℕ → ℝ) (σ t : ℝ), FRC.Chart.spectrum H a σ (-t) = FRC.Chart.spectrum H a σ t :=
  @FRC.LedgerML.p20113
/-- 20:D15 (p20114) — The deep window [chart]: a label reads with the modulus $n^{\sigma}$, and $E(t)\le\sum_{n\le\q}|\lambda(n)-\bar\lambda|\,n^{\sigma}$. Reading [approx], von Mangoldt weight, depth $10^{6}$: the ten tallest peaks on $10\le t\le52$ lie within $0.045$ of the first ten heights (A6). -/
theorem deep_window : And (∀ {n : Nat}, @LT.lt Nat instLTNat (@OfNat.ofNat Nat (nat_lit 0) (instOfNatNat (nat_lit 0))) n → ∀ (σ t : Real), @Eq Real (@norm Complex Complex.instNorm (@HPow.hPow Complex Complex Complex (@instHPow Complex Complex Complex.instPow) (@Nat.cast Complex Complex.instNatCast n) (@HAdd.hAdd Complex Complex Complex (@instHAdd Complex Complex.instAdd) (↑σ) (@HMul.hMul Complex Complex Complex (@instHMul Complex Complex.instMul) (↑t) Complex.I)))) (@HPow.hPow Real Real Real (@instHPow Real Real Real.instPow) (@Nat.cast Real Real.instNatCast n) σ)) (∀ (H : Nat) (a : Nat → Real) (σ t : Real), @LE.le Real Real.instLE (FRC.Chart.spectrum H a σ t) (∑ n ∈ @Finset.Icc Nat Nat.instPreorder Nat.instLocallyFiniteOrder (@OfNat.ofNat Nat (nat_lit 1) (instOfNatNat (nat_lit 1))) H, @HMul.hMul Real Real Real (@instHMul Real Real.instMul) (@abs Real Real.lattice Real.instAddGroup (a n)) (@HPow.hPow Real Real Real (@instHPow Real Real Real.instPow) (@Nat.cast Real Real.instNatCast n) σ))) :=
  @FRC.LedgerML.p20114
set_option linter.defProp false in
/-- 20:D17 (p20117) — The bound of the count [chart]: for every window, every real vector $w$ on its labels, every position $x>0$ that is no label and every height $T>0$, $|C_T(x)-\sum_{n<x}w(n)|\le B(x)/T$ with $B(x)=\frac1\pi\sum_{n\le\q}|w(n)|\sqrt{x/n}/|\log(x/n)|$ (D16). Reading [approx], prime vector, depth $39$, half-integers: $B(x)\le33.14$, so the bound is below one half from the height $67$ on. -/
def bound_of_count := @FRC.LedgerML.p20117
set_option linter.defProp false in
/-- 20:E12 (p20043) — \textbf{The shell theorem.} On every shell, for every vector, in $\Fp$: (i) the dual $\hat v(k)=\sum v(x)x^{k}$ inverts exactly, $v(y)=-\sum\hat v(k)y^{-k}$, the constant mode the mean term; (ii) the Parseval identity (E13); (iii) every mode is an eigenvector of the drive (E15), each nonconstant one with its zero at $k+1$ (G1); (iv) the parity and (v) the explicit formula along the meridian (E14). -/
def shell_theorem := @FRC.LedgerML.p20043
/-- 20:E13 (p20044) — The Parseval identity: $\sum_k\hat v(k)\hat v(-k)=-\sum_x v(x)^{2}$ on every shell, the finite Parseval identity of the cycle with the self-pairing $-1$ instead of the complex norm; in the chart of the cycle the $\p-1$ complex characters are an orthogonal basis with $\lVert\chi_j\rVert^{2}=\p-1$ and the same identity reads $\sum_j|\hat v_{\mathbb C}(j)|^{2}=(\p-1)\sum|v|^{2}$ [chart]. -/
theorem parseval_identity : (∀ {n : ℕ} [NeZero n] (j k : ZMod n), ∑ m, FRC.Chart.chi j m * (starRingEnd ℂ) (FRC.Chart.chi k m) = if j = k then ↑n else (0 : ℂ)) ∧ (∀ {n : ℕ} [NeZero n] (v : ZMod n → ℂ), ∑ j, Complex.normSq (FRC.Chart.coef v j) = ↑n * ∑ m, Complex.normSq (v m)) ∧ ∀ {n : ℕ} [NeZero n] (v : ZMod n → ℂ), (∀ (m : ZMod n), v m = (↑n)⁻¹ * ∑ j, FRC.Chart.coef v j * FRC.Chart.chi j m) ∧ FRC.Chart.coef v (0 : ZMod n) = ∑ m, v m ∧ ∀ (m : ZMod n), v m - (↑n)⁻¹ * ∑ m', v m' = (↑n)⁻¹ * ∑ j ∈ Finset.univ.erase (0 : ZMod n), FRC.Chart.coef v j * FRC.Chart.chi j m :=
  @FRC.LedgerML.p20044
-- end ledger predicates

end FRC.Rh
