import Mathlib
import FrcLedger.Theme.Horizon
import FrcLedger.Theme.Chart
import FrcLedger.Keys.Chart
import FrcLedger.Keys.Horizon

/-!
# 20-rh — the Riemann Hypothesis over the holographic substrate: the shell predicates in Lean (2026-09-19)

The exact arithmetic of the paper's block B, the constants of its Subject register, and the two character
readings of the shell theorem — rows B2, B4–B10 (B8's shell clauses), C2's identity `Λ = μ ∗ log`, C5, E1's shell
clause, E12 (i) and (iii), and E13's orthogonality, inversion and Parseval — proved for every shell: an arbitrary
finite field `F` with `4κ + 1` elements and a primitive root `g`, or `ZMod p` where the prime is needed, and, for
the analytic identities, over any integral domain or over `ℂ`; the laboratory pair `(13, 233)` of B1 decided.
Classical (tier 2) on Mathlib's hierarchy; the shell arithmetic is also in the core (`FrcCore/Rh.lean`) with no axioms.

Since the ledger migration (task LM36, 7 October 2026) the theorems live in the themes: the exact shell arithmetic in
the horizon theme (`FrcLedger/Theme/Horizon.lean`, `FRC.HorizonML`), and the complex characters of the cycle, the
characters as eigenvectors and the von Mangoldt weight in the chart theme (`FrcLedger/Theme/Chart.lean`, `FRC.Chart`).
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

section resonance

open ArithmeticFunction

/-- 20:C2 — 20-rh's name; the theorem is `FRC.Chart.vonMangoldt_moebius` (task LM36). -/
theorem vonMangoldt_moebius (m : ℕ) :
    vonMangoldt m = ∑ d ∈ m.divisors, (moebius d : ℝ) * Real.log ((m : ℝ) / d) ∧
    (vonMangoldt m ≠ 0 ↔ IsPrimePow m) := by
  apply FRC.Chart.vonMangoldt_moebius <;> assumption

end resonance

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

/-- 20:B2 — 20-rh's name; the theorem is `FRC.HorizonML.sqrt_sq_lt_prime` (task LM36). -/
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
/-- 20:B1 (p20008) — The two frames on one substrate: the Carrier chart $\F_\Omega$, held by no embedded observer, and the Subject $\Fp$ embedded with $\Omega\gg \p^{2}$; what they share is the quarter-turn core $Q_4$ and nothing else, on the laboratory pair $(13,233)$ the cycles $C_{12}$ and $C_{232}$ admit no projection ($12\nmid232$); hardness by register ($\p$-hard, $\Omega$-hard). -/
def p20008 := @FRC.LedgerML.p20008
/-- 20:B2 (p20009) — Frame coincidence below the horizon: for $n\le\sqrt \p$ the residue $n$ is the same integer in $\Fp$ and $\F_\Omega$, and primality of $n$ equals irreducibility in the Subject chart; the Subject-realised primes $\Pi_\p$ are the primes to $\sqrt \p$. -/
theorem p20009 : And (∀ {q : Nat} [@NeZero Nat (@MulZeroClass.toZero Nat Nat.instMulZeroClass) q] {H : Nat}, @LT.lt Nat instLTNat (@HMul.hMul Nat Nat Nat (@instHMul Nat instMulNat) H H) q → And (∀ (m : Nat), @LE.le Nat instLENat m H → @Eq Nat (@ZMod.val q (@Nat.cast (ZMod q) (@AddMonoidWithOne.toNatCast (ZMod q) (@AddGroupWithOne.toAddMonoidWithOne (ZMod q) (@Ring.toAddGroupWithOne (ZMod q) (@CommRing.toRing (ZMod q) (ZMod.commRing q))))) m)) m) (∀ (a b : Nat), @LE.le Nat instLENat a H → @LE.le Nat instLENat b H → @Eq Nat (@ZMod.val q (@HMul.hMul (ZMod q) (ZMod q) (ZMod q) (@instHMul (ZMod q) (@Distrib.toMul (ZMod q) (@instDistribOfSemiring (ZMod q) (@CommSemiring.toSemiring (ZMod q) (@CommRing.toCommSemiring (ZMod q) (ZMod.commRing q)))))) (@Nat.cast (ZMod q) (@AddMonoidWithOne.toNatCast (ZMod q) (@AddGroupWithOne.toAddMonoidWithOne (ZMod q) (@Ring.toAddGroupWithOne (ZMod q) (@CommRing.toRing (ZMod q) (ZMod.commRing q))))) a) (@Nat.cast (ZMod q) (@AddMonoidWithOne.toNatCast (ZMod q) (@AddGroupWithOne.toAddMonoidWithOne (ZMod q) (@Ring.toAddGroupWithOne (ZMod q) (@CommRing.toRing (ZMod q) (ZMod.commRing q))))) b))) (@HMul.hMul Nat Nat Nat (@instHMul Nat instMulNat) a b))) (And (∀ {q : Nat} [@NeZero Nat (@MulZeroClass.toZero Nat Nat.instMulZeroClass) q] {H : Nat}, @LT.lt Nat instLTNat (@HMul.hMul Nat Nat Nat (@instHMul Nat instMulNat) H H) q → ∀ (m : Nat), @LE.le Nat instLENat (@OfNat.ofNat Nat (nat_lit 2) (instOfNatNat (nat_lit 2))) m → @LE.le Nat instLENat m H → Iff (Nat.Prime m) (Not (∃ a b, And (@LE.le Nat instLENat (@OfNat.ofNat Nat (nat_lit 2) (instOfNatNat (nat_lit 2))) a) (And (@LE.le Nat instLENat (@OfNat.ofNat Nat (nat_lit 2) (instOfNatNat (nat_lit 2))) b) (And (@LE.le Nat instLENat a H) (And (@LE.le Nat instLENat b H) (@Eq (ZMod q) (@HMul.hMul (ZMod q) (ZMod q) (ZMod q) (@instHMul (ZMod q) (@Distrib.toMul (ZMod q) (@instDistribOfSemiring (ZMod q) (@CommSemiring.toSemiring (ZMod q) (@CommRing.toCommSemiring (ZMod q) (ZMod.commRing q)))))) (@Nat.cast (ZMod q) (@AddMonoidWithOne.toNatCast (ZMod q) (@AddGroupWithOne.toAddMonoidWithOne (ZMod q) (@Ring.toAddGroupWithOne (ZMod q) (@CommRing.toRing (ZMod q) (ZMod.commRing q))))) a) (@Nat.cast (ZMod q) (@AddMonoidWithOne.toNatCast (ZMod q) (@AddGroupWithOne.toAddMonoidWithOne (ZMod q) (@Ring.toAddGroupWithOne (ZMod q) (@CommRing.toRing (ZMod q) (ZMod.commRing q))))) b)) (@Nat.cast (ZMod q) (@AddMonoidWithOne.toNatCast (ZMod q) (@AddGroupWithOne.toAddMonoidWithOne (ZMod q) (@Ring.toAddGroupWithOne (ZMod q) (@CommRing.toRing (ZMod q) (ZMod.commRing q))))) m)))))))) (∀ {p : Nat}, Nat.Prime p → @LT.lt Nat instLTNat (@HMul.hMul Nat Nat Nat (@instHMul Nat instMulNat) p.sqrt p.sqrt) p)) :=
  @FRC.LedgerML.p20009
set_option linter.defProp false in
/-- 20:B4 (p20011) — Zero-slot: $Z_\Omega(k)=\sum_{x\in\Fx{\Omega}}x^{k}$ vanishes on every nonterminal exponent $1\le k\le\Omega-2$ and equals $-1$ on the full cycle; the nonterminal slots are the universal mode basis. -/
def p20011 := @FRC.LedgerML.p20011
/-- 20:B5 (p20012) — Slot complementarity: $\Phi(k)=-\gen^{\,k}$ bijects the nontrivial spectral slots onto the nonterminal additive slots $\Fx{\Omega}\setminus\{-1\}$, the two removed points being $\mu_2$, the intertwiner the half-cycle element. -/
theorem p20012 : ∀ {F : Type u_1} [Field F] [Fintype F] (g : F), IsPrimitiveRoot g (Fintype.card F - (1 : ℕ)) → Set.InjOn (fun k => -g ^ k) (Set.Icc (1 : ℕ) (Fintype.card F - (2 : ℕ))) ∧ (fun k => -g ^ k) '' Set.Icc (1 : ℕ) (Fintype.card F - (2 : ℕ)) = {y | y ≠ (0 : F) ∧ y ≠ (-1 : F)} :=
  @FRC.LedgerML.p20012
set_option linter.defProp false in
/-- 20:B6 (p20013) — Hermitian phase calculus on $K=\F_{\p^{2}}$: norm and trace $\Fp$-valued, the phase circle $U_{\p+1}$ of order $\p+1$ with Frobenius as inversion, the quarter-turn $\im$ Frobenius-fixed and off the circle ($\Nm(\im)=-1$), the trace-zero $\eta$ with $\eta^{2}=\nu$ a nonsquare, $\Tr(a+b\eta)=2a$, $\Nm=a^{2}-\nu b^{2}$. -/
def p20013 := @FRC.LedgerML.p20013
/-- 20:B7 (p20014) — Flat ground state: the full-modulus Ramanujan sum $c_\p(n)\equiv-1$ for every $n\not\equiv0$; the mode at the spectral origin carries no prime information. -/
theorem p20014 : ∀ {R : Type u_1} [CommRing R] [IsDomain R] {p : ℕ}, (0 : ℕ) < p → ∀ {ω : R}, IsPrimitiveRoot ω p → ∀ (n : ℕ), (¬p ∣ n → ∑ a ∈ Finset.Ico (1 : ℕ) p, ω ^ (a * n) = (-1 : R)) ∧ (p ∣ n → ∑ a ∈ Finset.Ico (1 : ℕ) p, ω ^ (a * n) = ↑(p - (1 : ℕ))) :=
  @FRC.LedgerML.p20014
set_option linter.defProp false in
/-- 20:B8 (p20015) — The finite critical line: the half-turn $2^{-1}=2\kp+1=-\pi$; $\Tr(z)=1$ exactly on the $\p$ points $z=2^{-1}+\eta\theta$, with energy $\Nm(z)=\tfrac14-\nu\theta^{2}$; de-framed, $2^{-1}/\p=(2\kp+1)/\p\to\half$ from above [chart]. -/
def p20015 := @FRC.LedgerML.p20015
/-- 20:B9 (p20016) — The two agreement loci: the Klein four-group $\langle\phi,\rho\rangle$ of Frobenius and the functional-equation half-turn fixes exactly $\Fp$ (the prime meridian), $L_{1/2}$ (the critical line) and their meeting $\{2^{-1}\}$; no other line is fixed. -/
theorem p20016 : (∀ {F : Type u_1} [Field F] (ν : F) (z : QuadraticAlgebra F ν (0 : F)), star (star z) = z ∧ (1 : QuadraticAlgebra F ν (0 : F)) - ((1 : QuadraticAlgebra F ν (0 : F)) - z) = z ∧ star ((1 : QuadraticAlgebra F ν (0 : F)) - z) = (1 : QuadraticAlgebra F ν (0 : F)) - star z) ∧ (∀ {F : Type u_2} [Field F] (ν : F), (2 : F) ≠ (0 : F) → ∀ (z : QuadraticAlgebra F ν (0 : F)), star z = z ↔ z.im = (0 : F)) ∧ (∀ {F : Type u_3} [Field F] (ν : F), (2 : F) ≠ (0 : F) → ∀ (z : QuadraticAlgebra F ν (0 : F)), (QuadraticAlgebra.trace z = (1 : F) ↔ z.re = (2 : F)⁻¹) ∧ ((1 : QuadraticAlgebra F ν (0 : F)) - star z = z ↔ z.re = (2 : F)⁻¹)) ∧ ∀ {F : Type u_4} [Field F] (ν : F), (2 : F) ≠ (0 : F) → ∀ (z : QuadraticAlgebra F ν (0 : F)), ((1 : QuadraticAlgebra F ν (0 : F)) - z = z ↔ z = { re := (2 : F)⁻¹, im := (0 : F) }) ∧ (z.im = (0 : F) ∧ z.re = (2 : F)⁻¹ ↔ z = { re := (2 : F)⁻¹, im := (0 : F) }) :=
  @FRC.LedgerML.p20016
/-- 20:B10 (p20017) — The Subject constants on the shell: $\pi=2\kp$, $2\pi\equiv-1$, $\im=\gen^{-\kp}$, $\im^{2}\equiv-1$, $\E=\gen^{\,\im}$ on the odd lift, $\gen^{\,\pi}\equiv-1$, $\E^{\,\im\pi}\equiv-1$; on $\F_{13}$: $\gen=2$, $\im=5$, $\E=6$, $\pi=6$. -/
theorem p20017 : (∀ {F : Type u_1} [Field F] [Fintype F] (κ : ℕ), Fintype.card F = (4 : ℕ) * κ + (1 : ℕ) → ∀ (g : F), IsPrimitiveRoot g (Fintype.card F - (1 : ℕ)) → (2 : F) * ↑((2 : ℕ) * κ) = (-1 : F) ∧ g ^ ((3 : ℕ) * κ) = -g ^ κ ∧ (g ^ ((3 : ℕ) * κ)) ^ (2 : ℕ) = (-1 : F) ∧ g ^ ((2 : ℕ) * κ) = (-1 : F) ∧ ∀ (m : ℕ), m % (2 : ℕ) = (1 : ℕ) → (g ^ m) ^ (m * ((2 : ℕ) * κ)) = (-1 : F)) ∧ (2 : ZMod (13 : ℕ)) * (6 : ZMod (13 : ℕ)) = (-1 : ZMod (13 : ℕ)) ∧ (2 : ZMod (13 : ℕ)) ^ (9 : ℕ) = (5 : ZMod (13 : ℕ)) ∧ (5 : ZMod (13 : ℕ)) ^ (2 : ℕ) = (-1 : ZMod (13 : ℕ)) ∧ (2 : ZMod (13 : ℕ)) ^ (5 : ℕ) = (6 : ZMod (13 : ℕ)) ∧ (2 : ZMod (13 : ℕ)) ^ (6 : ℕ) = (-1 : ZMod (13 : ℕ)) ∧ (6 : ZMod (13 : ℕ)) ^ ((5 : ℕ) * (6 : ℕ)) = (-1 : ZMod (13 : ℕ)) :=
  @FRC.LedgerML.p20017
/-- 20:C2 (p20020) — Resonance and the von Mangoldt weight: $R_L\to\frac{\varphi(n)}{n}\Lambda(n)$ (Hardy, A3); $\Lambda=\mu\ast\log$ exactly on the divisor lattice; the intertwiner $\Lambda=\frac{n}{\varphi(n)}R$; support the prime powers in every form. -/
theorem p20020 : ∀ (m : ℕ), ArithmeticFunction.vonMangoldt m = ∑ d ∈ m.divisors, ↑(ArithmeticFunction.moebius d) * Real.log (↑m / ↑d) ∧ (ArithmeticFunction.vonMangoldt m ≠ (0 : ℝ) ↔ IsPrimePow m) :=
  @FRC.LedgerML.p20020
/-- 20:C5 (p20023) — Mean-square flatness: with $r_j$ the normalised correlation of the mean-removed prime indicator with the nonconstant chart mode $\chi_j$, $\sum_{j\ne0}r_j^{2}=1$ exactly (Parseval), so the root-mean-square correlation is $1/\sqrt{\p-2}$. -/
theorem p20023 : (∀ {n : ℕ} [NeZero n] (v : ZMod n → ℂ), ∑ j, Complex.normSq (FRC.Chart.coef v j) = ↑n * ∑ m, Complex.normSq (v m)) ∧ ∀ {n : ℕ} [NeZero n] (u : ZMod n → ℂ), ∑ m, u m = (0 : ℂ) → u ≠ (0 : ZMod n → ℂ) → ∑ j ∈ Finset.univ.erase (0 : ZMod n), Complex.normSq (FRC.Chart.coef u j) / (↑n * ∑ m, Complex.normSq (u m)) = (1 : ℝ) ∧ (∑ j ∈ Finset.univ.erase (0 : ZMod n), Complex.normSq (FRC.Chart.coef u j) / (↑n * ∑ m, Complex.normSq (u m))) / (↑n - (1 : ℝ)) = (1 : ℝ) / (↑n - (1 : ℝ)) :=
  @FRC.LedgerML.p20023
set_option linter.defProp false in
/-- 20:E1 (p20032) — The scale-evolution generator: on the shell the scale-shift $x\mapsto\gen^{\,r}x$ is a unitary permutation of $\Fx{\p}$ with the complex characters as eigenvectors; in the analytic chart [chart] the dilation group $U_r=e^{ir\Hh}$ has the self-adjoint generator $\Hh=-i(x\partial_x+\half)$ with generalised eigenfunctions $x^{-\bar\rho}$, $\rho=\half+i\gamma$, the symmetrizing $\half$ the half-turn of B8; the chart assignment is used nowhere as a shell identity. -/
def p20032 := @FRC.LedgerML.p20032
set_option linter.defProp false in
/-- 20:E12 (p20043) — \textbf{The shell theorem.} On every shell, with no hypothesis: (i) $v$ expands in the constant mode and the nonterminal modes of the quarter-turn meridian; (ii) every readout lies on $\Tr=1$, real part $2^{-1}=2\kp+1=-\pi$; (iii) the scale-shift has the modes as eigenvectors, eigenphases $2\pi j/(\p-1)$ independent of $v$. No off-line mode; true of every vector, the Davenport--Heilbronn vector included. -/
def p20043 := @FRC.LedgerML.p20043
set_option linter.defProp false in
/-- 20:E13 (p20044) — Shell-basis completeness is not a clause of E12: the $\p-1$ complex characters are an orthogonal basis of $\mathbb C^{\Fx{\p}}$ ($\lVert\chi_j\rVert^{2}=\p-1$; finite Parseval), true of every vector, the trivial character carrying the mean $\psi(\p-1)/(\p-1)$; the $\Fp$-valued power characters are never orthonormal and do not expand $v$; completeness for the zero set of $\zeta$ is D5, a different clause. -/
def p20044 := @FRC.LedgerML.p20044
-- end ledger predicates

end FRC.Rh
