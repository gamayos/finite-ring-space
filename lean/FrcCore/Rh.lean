import FrcCore.Sum
import FrcCore.Instances
import FrcCore.Poly
import FrcCore.Theme.Extension
import FrcCore.Theme.Horizon
import FrcCore.Keys.Horizon

/-!
# FrcCore.Rh — the shell predicates of 20-rh with no axioms

The exact arithmetic of *Riemann Hypothesis over the Holographic Substrate* (20-rh), block B and the `𝔽_p`
reading of the shell theorem, on the kernel alone. For every frame `(τ; 0, 1, g)` of capacity `κ`
(`p = 4κ + 1`): the zero-slot `Σ_{x≠0} x^k = 0` on the nonterminal exponents and `−1` on the full cycle (20:B4);
slot complementarity `k ↦ −g^k`, injective on the nontrivial spectral slots and onto `F^× ∖ {−1}` (20:B5);
the half-turn arithmetic `2⁻¹ = 2κ + 1 = −π` (20:B8) and the Subject constants `π = 2κ`, `i = g^{−κ} = −g^κ`,
`i² = −1`, `g^π = −1`, `e^{iπ} = −1` on every odd representative (20:B10); the scale-shift on the power
characters and its fixed-point count `(p − 1)·[(p − 1) ∣ r]` — the `𝔽_p` reading of 20:E1 and 20:E12 (iii); the Ramanujan sum
`c_p(n) = −1` off the origin in any shell carrying a root of unity of order `p` (20:B7); the quadratic
extension `F(η)`, `η² = ν`, as pairs of residues — the Klein four-group of conjugation and the half-turn
`z ↦ 1 − z` with its three fixed loci (20:B9, with Frobenius read as conjugation: `z^p = z̄` is decided on `𝔽₁₃`
here and proved for every prime shell on Mathlib), the critical line `Tr z = 1 ⟺ Re z = 2⁻¹` with its energy
`(2⁻¹)² − νb²` (20:B8), conjugation as inversion on the norm-one circle and the quarter-turn
conjugation-fixed and off the circle (20:B6); frame coincidence below the horizon — window products read
back exactly and a residue `m ≤ H` factors on the shell exactly when it factors as an integer, on the Subject
and on the Carrier alike (20:B2). On `𝔽₁₃` and `𝔽₅₃`, decided by the kernel: the phase circle of `𝔽₁₃(√2)`
has `14` points and Frobenius `z ↦ z^{13}` is conjugation on all `169` of them, the Ramanujan sums of
`𝔽₅₃` with `ω = 16` of order `13`, the constants of `𝔽₁₃(τ; 0, 1, 2)`, and the laboratory pair `(13, 233)`
(20:B1). No axioms.

Since the ledger migration (task LM17) the quadratic extension is the extension theme's `FRC.Extension.Ext p ν`
(`Theme/Extension.lean`): 20-rh's pairs `Ext p`, with `ν` passed to each operation, became the one type with `ν` its
parameter, and the product, powers and the norm became its instances. The half-turn, the critical line and the readout
stay here on that type; `readout` takes `ν`. The sums, the counting lemmas and the deciders went to the frame theme.
Since task LM26 the shell theorem's clauses (the zero-slot, the half-turn `2⁻¹ = 2κ + 1`, the scale-shift's characters and
trace, the readout on the trace-one line and the slot index) live in the horizon theme (`Theme/Horizon.lean`), the home of
00:Z10. Every old name stays as an alias. Since task LM36 (20-rh's ledger file) the rest of the paper's shell arithmetic
lives there too: slot complementarity, the Subject constants, the Ramanujan sum, the half-turn, the Klein four-group, the
critical line and its fixed loci, the quarter-turn off the circle, frame coincidence and the values on `𝔽₁₃`, `𝔽₅₃` and
`(13, 233)`. This module keeps their old names as aliases, the frame of `𝔽₅₃`, and the predicate declarations, each the
alias of its key.
-/

namespace FRC.Rh

open FRC.Shell FRC.Shell.Frame

variable {p : Nat} [Pos p]

/-- A residue `l + 1 < p` is nonzero. -/
theorem ofNat_succ_ne_zero {l : Nat} (hl : l + 1 < p) : (ofNat (l + 1) : Shell p) ≠ 0 := fun h => by
  have := val_injective h
  rw [val_ofNat, val_zero, FRC.Nat.mod_eq_of_lt hl] at this
  exact Nat.noConfusion this

/-! ## The frame of `𝔽₅₃` (00:C1) -/

/-- 00:C1 on `𝔽₅₃`: the frame `(τ; 0, 1, 2)` of capacity `13`, and `ω = 2^4 = 16` of order `13`. -/
theorem frame53 : Frame 53 13 (2 : Shell 53) ∧ IsPrimitive (16 : Shell 53) 13 ∧ (2 : Shell 53) ^ 4 = 16 :=
  ⟨⟨rfl, Nat.zero_lt_succ 12, by decide⟩, by decide, by decide⟩


/-! ## Old names (ledger migration, task LM17): the declarations moved to the themes, each under its old name -/
section aliases
variable {κ : Nat} {g : Shell p}

/-- `p ≡ 0` on the shell (20-rh's name; the lemma is `FRC.Shell.Frame.ofNat_self`). -/
theorem ofNat_p : (ofNat p : Shell p) = 0 :=
  FRC.Shell.Frame.ofNat_self

/-- `n + p ≡ n` on the shell (20-rh's name; the lemma is `FRC.Shell.Frame.ofNat_add_self`). -/
theorem ofNat_add_p (n : Nat) : (ofNat (n + p) : Shell p) = ofNat n :=
  FRC.Shell.Frame.ofNat_add_self n

/-- Counting where nothing satisfies the predicate. -/
theorem natCount_eq_zero (P : Nat → Prop) [DecidablePred P] : ∀ n, (∀ x, x < n → ¬ P x) → natCount P n = 0 :=
  FRC.Shell.Frame.natCount_eq_zero P

/-- Counting through an equivalent predicate. -/
theorem natCount_congr (P Q : Nat → Prop) [DecidablePred P] [DecidablePred Q] :
    ∀ n, (∀ x, x < n → (P x ↔ Q x)) → natCount P n = natCount Q n :=
  FRC.Shell.Frame.natCount_congr P Q

/-- `Σ_{l<n+1} f l = f 0 + Σ_{l<n} f (l + 1)`. -/
theorem sumRange_succ' (f : Nat → Shell p) : ∀ n, sumRange f (n + 1) = f 0 + sumRange (fun l => f (l + 1)) n :=
  FRC.Shell.sumRange_succ' f

/-- The sum over the nonzero residues equals the sum over the powers of the drive: `x = g^m` reindexes. -/
theorem sum_units_eq_sum_pow (F : Frame p κ g) (f : Shell p → Shell p) :
    sumRange (fun l => f (ofNat (l + 1))) (p - 1) = sumRange (fun m => f (g ^ m)) (p - 1) :=
  FRC.Shell.Frame.sum_units_eq_sum_pow F f

/-- 20:B4 — the zero-slot (20-rh's name; the theorem is `FRC.Horizon.zero_slot`, LM26). -/
theorem zero_slot (F : Frame p κ g) :
    (∀ k, 0 < k → k < p - 1 → sumRange (fun l => (ofNat (l + 1) : Shell p) ^ k) (p - 1) = 0) ∧
    sumRange (fun l => (ofNat (l + 1) : Shell p) ^ (p - 1)) (p - 1) = -1 :=
  FRC.Horizon.zero_slot F

/-- 20:B8 — `2⁻¹ = 2κ + 1 = −π` (20-rh's name; the theorem is `FRC.Horizon.half_inverse`, LM26). -/
theorem half_inverse (F : Frame p κ g) :
    (2 : Shell p) * ofNat (2 * κ + 1) = 1 ∧ (ofNat (2 * κ + 1) : Shell p) = -(ofNat (2 * κ)) :=
  FRC.Horizon.half_inverse F

/-- 20:E1, 20:E12 — the power characters under the scale-shift (20-rh's name; the theorem is
`FRC.Horizon.shift_power_character`, LM26). -/
theorem shift_power_character (r k : Nat) (x : Shell p) : (g ^ r * x) ^ k = (g ^ r) ^ k * x ^ k :=
  FRC.Horizon.shift_power_character r k x

/-- 20:E12, 20:E1 — the fixed-point count of the scale-shift (20-rh's name; the theorem is `FRC.Horizon.shift_trace`,
LM26). -/
theorem shift_trace (F : Frame p κ g) (r : Nat) :
    natCount (fun x => x ≠ 0 ∧ g ^ r * ofNat x = ofNat x) p = if r % (p - 1) = 0 then p - 1 else 0 :=
  FRC.Horizon.shift_trace F r

/-! The declarations moved to the horizon theme by task LM36 (`FRC.Horizon`, `Theme/Horizon.lean`), each under its old
name: slot complementarity, the Subject constants, the Ramanujan sum, frame coincidence and the laboratory pair. -/

/-- 20:B5 — slot complementarity (20-rh's name; the theorem is `FRC.Horizon.slot_complementarity`, LM36). -/
theorem slot_complementarity (F : Frame p κ g) :
    (∀ i j, i < p - 1 → j < p - 1 → -(g ^ i) = -(g ^ j) → i = j) ∧
    (∀ k, 0 < k → k < p - 1 → -(g ^ k) ≠ 0 ∧ -(g ^ k) ≠ -1) ∧
    (∀ y : Shell p, y ≠ 0 → y ≠ -1 → ∃ k, 0 < k ∧ k < p - 1 ∧ -(g ^ k) = y) :=
  FRC.Horizon.slot_complementarity F

/-- 20:B10 — `i = g^{−κ}` is `−g^κ` (20-rh's name; the theorem is `FRC.Horizon.quarter_turn_eq_pow`, LM36). -/
theorem quarter_turn_eq_pow (F : Frame p κ g) : g ^ (3 * κ) = quarterTurn g κ :=
  FRC.Horizon.quarter_turn_eq_pow F

/-- 20:B10 — the Subject constants (20-rh's name; the theorem is `FRC.Horizon.subject_constants`, LM36). -/
theorem subject_constants (F : Frame p κ g) :
    (ofNat (2 * halfPeriod κ) : Shell p) = -1 ∧ g ^ (3 * κ) = quarterTurn g κ ∧
    quarterTurn g κ * quarterTurn g κ = -1 ∧ g ^ (2 * κ) = -1 ∧
    ∀ m : Nat, m % 2 = 1 → (g ^ m) ^ (m * (2 * κ)) = -1 :=
  FRC.Horizon.subject_constants F

/-- 20:B10 [value] — the constants on `𝔽₁₃` (20-rh's name; the theorem is `FRC.Horizon.constants13`, LM36). -/
theorem constants13 :
    (2 : Shell 13) * 6 = -1 ∧ (2 : Shell 13) ^ 9 = 5 ∧ quarterTurn (2 : Shell 13) 3 = 5 ∧
    (5 : Shell 13) * 5 = -1 ∧ (2 : Shell 13) ^ 5 = 6 ∧ (2 : Shell 13) ^ 6 = -1 ∧
    (6 : Shell 13) ^ (5 * 6) = -1 :=
  FRC.Horizon.constants13

/-- Powers reduce modulo the order (20-rh's name; the theorem is `FRC.Horizon.pow_mod_of_pow_eq_one`, LM36). -/
theorem pow_mod_of_pow_eq_one {q : Nat} [Pos q] {ω : Shell q} {m : Nat} (hm : 0 < m) (hω : ω ^ m = 1) (l : Nat) :
    ω ^ l = ω ^ (l % m) :=
  FRC.Horizon.pow_mod_of_pow_eq_one hm hω l

/-- 20:B7 — the Ramanujan sum (20-rh's name; the theorem is `FRC.Horizon.ramanujan_sum`, LM36). -/
theorem ramanujan_sum {q : Nat} [Pos q] {κ' : Nat} {h : Shell q} (F : Frame q κ' h) {m : Nat} (hm : 0 < m)
    {ω : Shell q} (hω : IsPrimitive ω m) (n : Nat) (hn : n % m ≠ 0) :
    sumRange (fun a => ω ^ (n * (a + 1))) (m - 1) = -1 :=
  FRC.Horizon.ramanujan_sum F hm hω n hn

/-- 20:B7 [value] — the Ramanujan sums of `𝔽₅₃` (20-rh's name; the theorem is `FRC.Horizon.ramanujan53`, LM36). -/
theorem ramanujan53 :
    (∀ n, n < 13 → 0 < n → sumRange (fun a => (16 : Shell 53) ^ (n * (a + 1))) 12 = -1) ∧
    sumRange (fun a => (16 : Shell 53) ^ (0 * (a + 1))) 12 = 12 :=
  FRC.Horizon.ramanujan53

/-- `H ≤ H²` (20-rh's name; the theorem is `FRC.Horizon.le_mul_self`, LM36). -/
theorem le_mul_self (H : Nat) : H ≤ H * H :=
  FRC.Horizon.le_mul_self H

/-- 20:B2 — the window reads back (20-rh's name; the theorem is `FRC.Horizon.window_readback`, LM36). -/
theorem window_readback {H : Nat} (hH : H * H < p) :
    (∀ m, m ≤ H → (ofNat m : Shell p).val = m) ∧
    ∀ a b, a ≤ H → b ≤ H → (ofNat a * ofNat b : Shell p).val = a * b :=
  FRC.Horizon.window_readback hH

/-- 20:B2 — primality equals irreducibility in the window (20-rh's name; the theorem is
`FRC.Horizon.factorisation_iff`, LM36). -/
theorem factorisation_iff {H : Nat} (hH : H * H < p) (m : Nat) (hm : m ≤ H) :
    (∃ a b, 2 ≤ a ∧ 2 ≤ b ∧ a ≤ H ∧ b ≤ H ∧ (ofNat a * ofNat b : Shell p) = ofNat m) ↔
    ∃ a b, 2 ≤ a ∧ 2 ≤ b ∧ a * b = m :=
  FRC.Horizon.factorisation_iff hH m hm

/-- 20:B2 — frame coincidence (20-rh's name; the theorem is `FRC.Horizon.frame_coincidence`, LM36). -/
theorem frame_coincidence {Ω : Nat} [Pos Ω] {H : Nat} (hp : H * H < p) (hΩ : H * H < Ω) (m : Nat) (hm : m ≤ H) :
    (∃ a b, 2 ≤ a ∧ 2 ≤ b ∧ a ≤ H ∧ b ≤ H ∧ (ofNat a * ofNat b : Shell p) = ofNat m) ↔
    (∃ a b, 2 ≤ a ∧ 2 ≤ b ∧ a ≤ H ∧ b ≤ H ∧ (ofNat a * ofNat b : Shell Ω) = ofNat m) :=
  FRC.Horizon.frame_coincidence hp hΩ m hm

/-- 20:B1 [value] — the laboratory pair (20-rh's name; the theorem is `FRC.Horizon.lab_pair`, LM36). -/
theorem lab_pair :
    13 * 13 < 233 ∧ 12 % 4 = 0 ∧ 232 % 4 = 0 ∧ 232 % 3 ≠ 0 ∧ (5 : Shell 13) * 5 = -1 ∧
    (89 : Shell 233) * 89 = -1 ∧ 232 % 12 ≠ 0 ∧ 3 * 3 < 13 ∧ 3 * 3 < 233 :=
  FRC.Horizon.lab_pair

/-- 20-rh's quadratic extension: `FRC.Extension.Ext p ν`, its `ν` now a parameter of the type. -/
@[reducible] def Ext (p : Nat) [Pos p] (ν : Shell p) : Type := FRC.Extension.Ext p ν

namespace Ext
variable {ν : Shell p}
open FRC.Extension.Ext (ofShell)

theorem ext {z z' : Ext p ν} (h1 : z.re = z'.re) (h2 : z.im = z'.im) : z = z' :=
  FRC.Extension.Ext.ext h1 h2

theorem re_congr {a b : Ext p ν} (h : a = b) : a.re = b.re :=
  FRC.Extension.Ext.re_congr h

theorem im_congr {a b : Ext p ν} (h : a = b) : a.im = b.im :=
  FRC.Extension.Ext.im_congr h

/-- Conjugation `a + bη ↦ a − bη` (Frobenius on the extension). -/
@[reducible] def conj (z : Ext p ν) : Ext p ν :=
  FRC.Extension.Ext.conj z

/-- The trace `Tr(a + bη) = 2a`. -/
@[reducible] def trace (z : Ext p ν) : Shell p :=
  FRC.Extension.Ext.trace z

/-- The norm `N(a + bη) = a² − νb²`. -/
@[reducible] def norm (z : Ext p ν) : Shell p :=
  FRC.Extension.Ext.norm z

/-- Powers, by repeated multiplication. -/
@[reducible] def pow (z : Ext p ν) : Nat → Ext p ν :=
  FRC.Extension.Ext.pow z

/-- 20:B6 — `z z̄ = N(z)`: conjugation is inversion on the norm-one circle. -/
theorem mul_conj (z : Ext p ν) : z * conj z = ofShell (norm z) :=
  FRC.Extension.Ext.mul_conj z

/-- 20:B6 — on the circle `N(z) = 1` the conjugate is the inverse: `z z̄ = 1`. -/
theorem conj_inv_of_norm_one (z : Ext p ν) (hz : norm z = 1) : z * conj z = 1 :=
  FRC.Extension.Ext.conj_inv_of_norm_one z hz

/-- 20:B9 — the fixed locus of conjugation is the prime meridian: `z̄ = z ⟺ b = 0`. -/
theorem fixed_conj (F : Frame p κ g) (z : Ext p ν) : conj z = z ↔ z.im = 0 :=
  FRC.Extension.Ext.fixed_conj F z

/-- The functional-equation half-turn `ρ : z ↦ 1 − z` (20-rh's name; the definition is `FRC.Horizon.rho`, LM36). -/
@[reducible] def rho (z : Ext p ν) : Ext p ν := FRC.Horizon.rho z

/-- `σ = ρ ∘ φ : z ↦ 1 − z̄` (20-rh's name; the definition is `FRC.Horizon.sigma`, LM36). -/
@[reducible] def sigma (z : Ext p ν) : Ext p ν := FRC.Horizon.sigma z

/-- 20:B9 — the Klein four-group (20-rh's name; the theorem is `FRC.Horizon.klein_four`, LM36). -/
theorem klein_four (z : Ext p ν) :
    FRC.Extension.Ext.conj (FRC.Extension.Ext.conj z) = z ∧ FRC.Horizon.rho (FRC.Horizon.rho z) = z ∧
    FRC.Extension.Ext.conj (FRC.Horizon.rho z) = FRC.Horizon.rho (FRC.Extension.Ext.conj z) :=
  FRC.Horizon.klein_four z

/-- 20:B8, 20:B9 — the finite critical line (20-rh's name; the theorem is `FRC.Horizon.critical_line`, LM36). -/
theorem critical_line {κ : Nat} {g : Shell p} (F : Frame p κ g) (z : Ext p ν) :
    (FRC.Extension.Ext.trace z = 1 ↔ z.re = ofNat (2 * κ + 1)) ∧
    (FRC.Horizon.sigma z = z ↔ z.re = ofNat (2 * κ + 1)) ∧
    ∀ b : Shell p, FRC.Extension.Ext.trace (⟨ofNat (2 * κ + 1), b⟩ : Ext p ν) = 1 :=
  FRC.Horizon.critical_line F z

/-- 20:B9 — the fixed locus of the half-turn (20-rh's name; the theorem is `FRC.Horizon.fixed_half_turn`, LM36). -/
theorem fixed_half_turn {κ : Nat} {g : Shell p} (F : Frame p κ g) (z : Ext p ν) :
    (FRC.Horizon.rho z = z ↔ (FRC.Extension.Ext.conj z = z ∧ FRC.Horizon.sigma z = z)) ∧
    (FRC.Horizon.rho z = z ↔ z = ⟨ofNat (2 * κ + 1), 0⟩) :=
  FRC.Horizon.fixed_half_turn F z

/-- 20:B8 — the energy on the critical line (20-rh's name; the theorem is `FRC.Horizon.norm_on_line`, LM36). -/
theorem norm_on_line {κ : Nat} {g : Shell p} (F : Frame p κ g) (z : Ext p ν) (hz : z.re = ofNat (2 * κ + 1)) :
    FRC.Extension.Ext.norm z = ofNat (2 * κ + 1) * ofNat (2 * κ + 1) + -(ν * (z.im * z.im)) ∧
    (2 : Shell p) * ofNat (2 * κ + 1) = 1 :=
  FRC.Horizon.norm_on_line F z hz

/-- 20:B6 — the quarter-turn off the circle (20-rh's name; the theorem is `FRC.Horizon.quarter_turn_off_circle`,
LM36). -/
theorem quarter_turn_off_circle {κ : Nat} {g : Shell p} (F : Frame p κ g) (ν : Shell p) :
    FRC.Extension.Ext.conj (⟨quarterTurn g κ, 0⟩ : Ext p ν) = ⟨quarterTurn g κ, 0⟩ ∧
    FRC.Extension.Ext.norm (⟨quarterTurn g κ, 0⟩ : Ext p ν) = -1 ∧
    FRC.Extension.Ext.norm (⟨quarterTurn g κ, 0⟩ : Ext p ν) ≠ 1 :=
  FRC.Horizon.quarter_turn_off_circle F ν

/-- 20:B6 [value] — the circle of `𝔽₁₃(√2)` (20-rh's name; the theorem is `FRC.Horizon.circle13`, LM36). -/
theorem circle13 :
    natCount (fun k => FRC.Extension.Ext.norm (⟨ofNat (k / 13), ofNat (k % 13)⟩ : FRC.Extension.Ext 13 2) = 1) 169 = 14 ∧
    (∀ k, k < 169 → (⟨ofNat (k / 13), ofNat (k % 13)⟩ : FRC.Extension.Ext 13 2) ^ 13 =
      FRC.Extension.Ext.conj ⟨ofNat (k / 13), ofNat (k % 13)⟩) ∧
    (∀ x : Nat, x < 13 → 0 < x → (ofNat x : Shell 13) * ofNat x ≠ 2) :=
  FRC.Horizon.circle13

/-- 20-rh's product, the instance `z * w` of `FRC.Extension.Ext p ν`. -/
@[reducible] def mul (z w : Ext p ν) : Ext p ν := z * w

/-- 20-rh's unit, `1`. -/
@[reducible] def one : Ext p ν := 1

/-- 20:E12, 20:B8 — the spectral readout (20-rh's name; the definition is `FRC.Horizon.readout`, LM26). -/
@[reducible] def readout (ν : Shell p) (κ : Nat) (θ : Shell p) : Ext p ν := FRC.Horizon.readout ν κ θ

/-- 20:E12 (ii) — every readout on the trace-one line (20-rh's name; the theorem is `FRC.Horizon.readout_on_line`, LM26). -/
theorem readout_on_line {κ : Nat} {g : Shell p} (F : Frame p κ g) (ν θ : Shell p) :
    trace (readout ν κ θ) = 1 ∧ (readout ν κ θ).re = ofNat (2 * κ + 1) ∧
    ∀ θ' : Shell p, readout ν κ θ = readout ν κ θ' → θ = θ' :=
  FRC.Horizon.readout_on_line F ν θ

/-- 20:E12 — the slot index of a nontrivial slot (20-rh's name; the theorem is `FRC.Horizon.readout_slot_index`, LM26). -/
theorem readout_slot_index {κ : Nat} {g : Shell p} (F : Frame p κ g) (k : Nat) (hk1 : 1 ≤ k) (hk2 : k ≤ p - 2) :
    -(g ^ k) ≠ 0 ∧ -(g ^ k) ≠ -1 :=
  FRC.Horizon.readout_slot_index F k hk1 hk2

end Ext

/-- Bounded universal quantifiers, decided by search (no axioms). -/
@[reducible] def decForallLT (P : Nat → Prop) [DecidablePred P] : (n : Nat) → Decidable (∀ m, m < n → P m) :=
  FRC.Shell.decForallLT P

@[reducible] def instDecForallLT (P : Nat → Prop) [DecidablePred P] (n : Nat) : Decidable (∀ m, m < n → P m) :=
  FRC.Shell.instDecForallLT P n

end aliases

-- Ledger predicates of 20-rh (generated by make_predicates.py from docs/20-rh/20-rh-ledger.json; edit the ledger, not this section)
/-- 20:B1 (p20008) — The two frames on one substrate: the Carrier chart $\F_\Omega$, held by no embedded observer, and the Subject $\Fp$ embedded with $\Omega\gg \p^{2}$; what they share is the quarter-turn core $Q_4$ and nothing else, on the laboratory pair $(13,233)$ the cycles $C_{12}$ and $C_{232}$ admit no projection ($12\nmid232$); hardness by register ($\p$-hard, $\Omega$-hard). -/
theorem p20008 : (13 : Nat) * (13 : Nat) < (233 : Nat) ∧ (12 : Nat) % (4 : Nat) = (0 : Nat) ∧ (232 : Nat) % (4 : Nat) = (0 : Nat) ∧ (232 : Nat) % (3 : Nat) ≠ (0 : Nat) ∧ (5 : FRC.Shell (13 : Nat)) * (5 : FRC.Shell (13 : Nat)) = (-1 : FRC.Shell (13 : Nat)) ∧ (89 : FRC.Shell (233 : Nat)) * (89 : FRC.Shell (233 : Nat)) = (-1 : FRC.Shell (233 : Nat)) ∧ (232 : Nat) % (12 : Nat) ≠ (0 : Nat) ∧ (3 : Nat) * (3 : Nat) < (13 : Nat) ∧ (3 : Nat) * (3 : Nat) < (233 : Nat) :=
  @FRC.Ledger.p20008
set_option linter.defProp false in
/-- 20:B2 (p20009) — Frame coincidence below the horizon: for $n\le\sqrt \p$ the residue $n$ is the same integer in $\Fp$ and $\F_\Omega$, and primality of $n$ equals irreducibility in the Subject chart; the Subject-realised primes $\Pi_\p$ are the primes to $\sqrt \p$. -/
def p20009 := @FRC.Ledger.p20009
/-- 20:B4 (p20011) — Zero-slot: $Z_\Omega(k)=\sum_{x\in\Fx{\Omega}}x^{k}$ vanishes on every nonterminal exponent $1\le k\le\Omega-2$ and equals $-1$ on the full cycle; the nonterminal slots are the universal mode basis. -/
theorem p20011 : ∀ {p : Nat} [FRC.Pos p] {κ : Nat} {g : FRC.Shell p}, FRC.Shell.Frame p κ g → (∀ (k : Nat), (0 : Nat) < k → k < p - (1 : Nat) → FRC.Shell.sumRange (fun l => FRC.Shell.ofNat (l + (1 : Nat)) ^ k) (p - (1 : Nat)) = (0 : FRC.Shell p)) ∧ FRC.Shell.sumRange (fun l => FRC.Shell.ofNat (l + (1 : Nat)) ^ (p - (1 : Nat))) (p - (1 : Nat)) = (-1 : FRC.Shell p) :=
  @FRC.Ledger.p20011
/-- 20:B5 (p20012) — Slot complementarity: $\Phi(k)=-\gen^{\,k}$ bijects the nontrivial spectral slots onto the nonterminal additive slots $\Fx{\Omega}\setminus\{-1\}$, the two removed points being $\mu_2$, the intertwiner the half-cycle element. -/
theorem p20012 : ∀ {p : Nat} [FRC.Pos p] {κ : Nat} {g : FRC.Shell p}, FRC.Shell.Frame p κ g → (∀ (i j : Nat), i < p - (1 : Nat) → j < p - (1 : Nat) → -g ^ i = -g ^ j → i = j) ∧ (∀ (k : Nat), (0 : Nat) < k → k < p - (1 : Nat) → -g ^ k ≠ (0 : FRC.Shell p) ∧ -g ^ k ≠ (-1 : FRC.Shell p)) ∧ ∀ (y : FRC.Shell p), y ≠ (0 : FRC.Shell p) → y ≠ (-1 : FRC.Shell p) → ∃ k, (0 : Nat) < k ∧ k < p - (1 : Nat) ∧ -g ^ k = y :=
  @FRC.Ledger.p20012
set_option linter.defProp false in
/-- 20:B6 (p20013) — Hermitian phase calculus on $K=\F_{\p^{2}}$: norm and trace $\Fp$-valued, the phase circle $U_{\p+1}$ of order $\p+1$ with Frobenius as inversion, the quarter-turn $\im$ Frobenius-fixed and off the circle ($\Nm(\im)=-1$), the trace-zero $\eta$ with $\eta^{2}=\nu$ a nonsquare, $\Tr(a+b\eta)=2a$, $\Nm=a^{2}-\nu b^{2}$. -/
def p20013 := @FRC.Ledger.p20013
/-- 20:B7 (p20014) — Flat ground state: the full-modulus Ramanujan sum $c_\p(n)\equiv-1$ for every $n\not\equiv0$; the mode at the spectral origin carries no prime information. -/
theorem p20014 : (∀ {q : Nat} [FRC.Pos q] {κ' : Nat} {h : FRC.Shell q}, FRC.Shell.Frame q κ' h → ∀ {m : Nat}, (0 : Nat) < m → ∀ {ω : FRC.Shell q}, ω.IsPrimitive m → ∀ (n : Nat), n % m ≠ (0 : Nat) → FRC.Shell.sumRange (fun a => ω ^ (n * (a + (1 : Nat)))) (m - (1 : Nat)) = (-1 : FRC.Shell q)) ∧ (∀ (n : Nat), n < (13 : Nat) → (0 : Nat) < n → FRC.Shell.sumRange (fun a => (16 : FRC.Shell (53 : Nat)) ^ (n * (a + (1 : Nat)))) (12 : Nat) = (-1 : FRC.Shell (53 : Nat))) ∧ FRC.Shell.sumRange (fun a => (16 : FRC.Shell (53 : Nat)) ^ ((0 : Nat) * (a + (1 : Nat)))) (12 : Nat) = (12 : FRC.Shell (53 : Nat)) :=
  @FRC.Ledger.p20014
set_option linter.defProp false in
/-- 20:B8 (p20015) — The finite critical line: the half-turn $2^{-1}=2\kp+1=-\pi$; $\Tr(z)=1$ exactly on the $\p$ points $z=2^{-1}+\eta\theta$, with energy $\Nm(z)=\tfrac14-\nu\theta^{2}$; de-framed, $2^{-1}/\p=(2\kp+1)/\p\to\half$ from above [chart]. -/
def p20015 := @FRC.Ledger.p20015
set_option linter.defProp false in
/-- 20:B9 (p20016) — The two agreement loci: the Klein four-group $\langle\phi,\rho\rangle$ of Frobenius and the functional-equation half-turn fixes exactly $\Fp$ (the prime meridian), $L_{1/2}$ (the critical line) and their meeting $\{2^{-1}\}$; no other line is fixed. -/
def p20016 := @FRC.Ledger.p20016
/-- 20:B10 (p20017) — The Subject constants on the shell: $\pi=2\kp$, $2\pi\equiv-1$, $\im=\gen^{-\kp}$, $\im^{2}\equiv-1$, $\E=\gen^{\,\im}$ on the odd lift, $\gen^{\,\pi}\equiv-1$, $\E^{\,\im\pi}\equiv-1$; on $\F_{13}$: $\gen=2$, $\im=5$, $\E=6$, $\pi=6$. -/
theorem p20017 : (∀ {p : Nat} [FRC.Pos p] {κ : Nat} {g : FRC.Shell p}, FRC.Shell.Frame p κ g → FRC.Shell.ofNat ((2 : Nat) * FRC.Shell.Frame.halfPeriod κ) = (-1 : FRC.Shell p) ∧ g ^ ((3 : Nat) * κ) = FRC.Shell.Frame.quarterTurn g κ ∧ FRC.Shell.Frame.quarterTurn g κ * FRC.Shell.Frame.quarterTurn g κ = (-1 : FRC.Shell p) ∧ g ^ ((2 : Nat) * κ) = (-1 : FRC.Shell p) ∧ ∀ (m : Nat), m % (2 : Nat) = (1 : Nat) → (g ^ m) ^ (m * ((2 : Nat) * κ)) = (-1 : FRC.Shell p)) ∧ ((2 : FRC.Shell (13 : Nat)) * (6 : FRC.Shell (13 : Nat)) = (-1 : FRC.Shell (13 : Nat)) ∧ (2 : FRC.Shell (13 : Nat)) ^ (9 : Nat) = (5 : FRC.Shell (13 : Nat)) ∧ FRC.Shell.Frame.quarterTurn (2 : FRC.Shell (13 : Nat)) (3 : Nat) = (5 : FRC.Shell (13 : Nat)) ∧ (5 : FRC.Shell (13 : Nat)) * (5 : FRC.Shell (13 : Nat)) = (-1 : FRC.Shell (13 : Nat)) ∧ (2 : FRC.Shell (13 : Nat)) ^ (5 : Nat) = (6 : FRC.Shell (13 : Nat)) ∧ (2 : FRC.Shell (13 : Nat)) ^ (6 : Nat) = (-1 : FRC.Shell (13 : Nat)) ∧ (6 : FRC.Shell (13 : Nat)) ^ ((5 : Nat) * (6 : Nat)) = (-1 : FRC.Shell (13 : Nat))) ∧ FRC.Shell.Frame (13 : Nat) (3 : Nat) (2 : FRC.Shell (13 : Nat)) :=
  @FRC.Ledger.p20017
/-- 20:E1 (p20032) — The scale-evolution generator: on the shell the scale-shift $x\mapsto\gen^{\,r}x$ is a unitary permutation of $\Fx{\p}$ with the complex characters as eigenvectors; in the analytic chart [chart] the dilation group $U_r=e^{ir\Hh}$ has the self-adjoint generator $\Hh=-i(x\partial_x+\half)$ with generalised eigenfunctions $x^{-\bar\rho}$, $\rho=\half+i\gamma$, the symmetrizing $\half$ the half-turn of B8; the chart assignment is used nowhere as a shell identity. -/
theorem p20032 : (∀ {p : Nat} [FRC.Pos p] {g : FRC.Shell p} (r k : Nat) (x : FRC.Shell p), (g ^ r * x) ^ k = (g ^ r) ^ k * x ^ k) ∧ ∀ {p : Nat} [FRC.Pos p] {κ : Nat} {g : FRC.Shell p}, FRC.Shell.Frame p κ g → ∀ (r : Nat), FRC.Shell.Frame.natCount (fun x => x ≠ (0 : Nat) ∧ g ^ r * FRC.Shell.ofNat x = FRC.Shell.ofNat x) p = if r % (p - (1 : Nat)) = (0 : Nat) then p - (1 : Nat) else (0 : Nat) :=
  @FRC.Ledger.p20032
/-- 20:E12 (p20043) — \textbf{The shell theorem.} On every shell, with no hypothesis: (i) $v$ expands in the constant mode and the nonterminal modes of the quarter-turn meridian; (ii) every readout lies on $\Tr=1$, real part $2^{-1}=2\kp+1=-\pi$; (iii) the scale-shift has the modes as eigenvectors, eigenphases $2\pi j/(\p-1)$ independent of $v$. No off-line mode; true of every vector, the Davenport--Heilbronn vector included. -/
theorem p20043 : (∀ {p : Nat} [FRC.Pos p] {κ : Nat} {g : FRC.Shell p}, FRC.Shell.Frame p κ g → (∀ (k : Nat), (0 : Nat) < k → k < p - (1 : Nat) → FRC.Shell.sumRange (fun l => FRC.Shell.ofNat (l + (1 : Nat)) ^ k) (p - (1 : Nat)) = (0 : FRC.Shell p)) ∧ FRC.Shell.sumRange (fun l => FRC.Shell.ofNat (l + (1 : Nat)) ^ (p - (1 : Nat))) (p - (1 : Nat)) = (-1 : FRC.Shell p)) ∧ (∀ {p : Nat} [FRC.Pos p] {κ : Nat} {g : FRC.Shell p}, FRC.Shell.Frame p κ g → ∀ (v : Nat → FRC.Shell p) {j : Nat}, j < p - (1 : Nat) → v j = FRC.Shell.sumRange (fun k => FRC.Horizon.modeCoeff g v k * (g ^ j) ^ k) (p - (1 : Nat))) ∧ (∀ {p : Nat} [FRC.Pos p] {g : FRC.Shell p} (r k : Nat) (x : FRC.Shell p), (g ^ r * x) ^ k = (g ^ r) ^ k * x ^ k) ∧ (∀ {p : Nat} [FRC.Pos p] {κ : Nat} {g : FRC.Shell p}, FRC.Shell.Frame p κ g → ∀ (r k : Nat), ((g ^ r) ^ k) ^ (p - (1 : Nat)) = (1 : FRC.Shell p)) ∧ (∀ {p : Nat} [FRC.Pos p] {κ : Nat} {g : FRC.Shell p}, FRC.Shell.Frame p κ g → ∀ (r : Nat), FRC.Shell.Frame.natCount (fun x => x ≠ (0 : Nat) ∧ g ^ r * FRC.Shell.ofNat x = FRC.Shell.ofNat x) p = if r % (p - (1 : Nat)) = (0 : Nat) then p - (1 : Nat) else (0 : Nat)) ∧ (∀ {p : Nat} [FRC.Pos p] {κ : Nat} {g : FRC.Shell p}, FRC.Shell.Frame p κ g → ∀ (ν θ : FRC.Shell p), (FRC.Horizon.readout ν κ θ).trace = (1 : FRC.Shell p) ∧ (FRC.Horizon.readout ν κ θ).re = FRC.Shell.ofNat ((2 : Nat) * κ + (1 : Nat)) ∧ ∀ (θ' : FRC.Shell p), FRC.Horizon.readout ν κ θ = FRC.Horizon.readout ν κ θ' → θ = θ') ∧ ∀ {p : Nat} [FRC.Pos p] {κ : Nat} {g : FRC.Shell p}, FRC.Shell.Frame p κ g → ∀ (k : Nat), (1 : Nat) ≤ k → k ≤ p - (2 : Nat) → -g ^ k ≠ (0 : FRC.Shell p) ∧ -g ^ k ≠ (-1 : FRC.Shell p) :=
  @FRC.Ledger.p20043
-- end ledger predicates

end FRC.Rh
