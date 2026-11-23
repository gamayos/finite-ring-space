import FrcCore.Sum
import FrcCore.Instances
import FrcCore.Poly
import FrcCore.Theme.Extension
import FrcCore.Theme.Horizon
import FrcCore.Keys.Horizon
import FrcCore.Keys.Foundation
import FrcCore.Keys.Count

/-!
# FrcCore.Rh — the shell predicates of 20-rh with no axioms

The exact arithmetic of *Riemann Hypothesis over Finite Holographic Substrate* (20-rh), block B and the `𝔽_p`
reading of the shell theorem, on the kernel alone. For every frame `(τ; 0, 1, g)` of capacity `κ`
(`p = 4κ + 1`): the zero-slot `Σ_{x≠0} x^k = 0` on the nonterminal exponents and `−1` on the full cycle (20:B4);
slot complementarity `k ↦ −g^k`, injective on the nontrivial spectral slots and onto `F^× ∖ {−1}` (20:B5);
the centre's arithmetic `2⁻¹ = 2κ + 1 = −π` (20:B8) and the Subject constants `π = 2κ`, `i = g^{−κ} = −g^κ`,
`i² = −1`, `g^π = −1`, `e^{iπ} = −1` on every odd representative (20:B10); the scale-shift on the power
characters and its fixed-point count `(p − 1)·[(p − 1) ∣ r]` — the `𝔽_p` reading of 20:E1 and 20:E12 (iii); the Ramanujan sum
`c_p(n) = −1` off the origin in any shell carrying a root of unity of order `p` (20:B7); the quadratic
extension `F(η)`, `η² = ν`, as pairs of residues — the Klein four-group of conjugation and the reflection
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
parameter, and the product, powers and the norm became its instances. The reflection, the critical line and the readout
stay here on that type; `readout` takes `ν`. The sums, the counting lemmas and the deciders went to the frame theme.
Since task LM26 the shell theorem's clauses (the zero-slot, the centre `2⁻¹ = 2κ + 1`, the scale-shift's characters and
trace, the readout on the trace-one line and the slot index) live in the horizon theme (`Theme/Horizon.lean`), the home of
00:Z10. Every old name stays as an alias. Since task LM36 (20-rh's ledger file) the rest of the paper's shell arithmetic
lives there too: slot complementarity, the Subject constants, the Ramanujan sum, the reflection, the Klein four-group, the
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

/-- 20:B4, 20:X2 — the zero-slot (20-rh's name; the theorem is `FRC.Horizon.zero_slot`, LM26). -/
theorem zero_slot (F : Frame p κ g) :
    (∀ k, 0 < k → k < p - 1 → sumRange (fun l => (ofNat (l + 1) : Shell p) ^ k) (p - 1) = 0) ∧
    sumRange (fun l => (ofNat (l + 1) : Shell p) ^ (p - 1)) (p - 1) = -1 :=
  FRC.Horizon.zero_slot F

/-- 20:G7, 20:X1 — `2⁻¹ = 2κ + 1 = −π` (20-rh's name; the theorem is `FRC.Horizon.half_inverse`, LM26). -/
theorem half_inverse (F : Frame p κ g) :
    (2 : Shell p) * ofNat (2 * κ + 1) = 1 ∧ (ofNat (2 * κ + 1) : Shell p) = -(ofNat (2 * κ)) :=
  FRC.Horizon.half_inverse F

/-- 20:E12, 20:E15 — the power characters under the drive, the modes its eigenvectors with eigenvalue `g^k` (20-rh's
name; the theorem is `FRC.Horizon.shift_power_character`, LM26; the row 20:E1 that first cited it is retired). -/
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

/-- The reflection `ρ : z ↦ 1 − z` (20-rh's name; the definition is `FRC.Horizon.rho`, LM36). -/
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

/-- 20:B9 — the fixed locus of the reflection (20-rh's name; the theorem is `FRC.Horizon.fixed_half_turn`, LM36). -/
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

/-- 20:F7 (Theorem closure), the foundation clauses: the wrap of the height reading and the return of the cycle
(00:A5), Finitude (00:A2), Observation (00:A4). Lives in the horizon theme since 13 October 2026. -/
theorem closure :
    (∀ {p : Nat} [Pos p] (T : Nat), (ofNat (T + p) : Shell p) = ofNat T) ∧
    (∀ {p : Nat} [Pos p], 2 ≤ p → ∀ y : Shell p, ∃ k, k < p ∧ FRC.Foundation.succIter (0 : Shell p) k = y) ∧
    (∀ {U : Type} (Ω : Nat) [Pos Ω] (ρ : U → Nat), (∀ u, ρ u < Ω) →
      ∃ ι : FRC.Foundation.Registered ρ → Shell Ω, ∀ a b, ι a = ι b → a = b) ∧
    (∀ {Ω o : Nat} [Pos Ω], o < Ω → ∀ ρ : Shell Ω → Nat, (∀ x, ρ x < o) → ∃ x y : Shell Ω, x ≠ y ∧ ρ x = ρ y) ∧
    (∀ {Ω o : Nat} [Pos Ω] (ρ : Shell Ω → Nat), (∀ x, ρ x < o) → (∀ x y, ρ x = ρ y → x = y) → Ω ≤ o) :=
  FRC.Horizon.closure

/-- 20:F7, 20:F2, the laboratory instances of the closure (`FRC.Horizon.closure_lab`): the largest admissible Subject
`13, 173, 1549` of `Ω = 233, 30089, 2408561`, the control `Ω = 401` (the prime `19` is no Subject; `17` is), and `Ω = 13`
without one. -/
theorem closure_lab :
    (FRC.Horizon.largestSubject 233 13 ∧ 233 % 4 = 1 ∧ FRC.Nat.isPrime 233) ∧
    (FRC.Horizon.largestSubject 30089 173 ∧ 30089 % 4 = 1 ∧ FRC.Nat.isPrime 30089) ∧
    (FRC.Horizon.largestSubject 2408561 1549 ∧ 2408561 % 4 = 1 ∧ FRC.Nat.isPrime 2408561) ∧
    (FRC.Horizon.largestSubject 401 17 ∧ FRC.Nat.isPrime 19 ∧ 19 * 19 < 401 ∧ 19 % 4 = 3) ∧
    (∀ q, q < 4 → q % 4 = 1 → 5 < q → ¬ FRC.Nat.isPrime q) ∧ 13 ≤ 4 * 4 :=
  FRC.Horizon.closure_lab

end aliases

-- Ledger predicates of 20-rh (generated by make_predicates.py from docs/20-rh/20-rh-ledger.json; edit the ledger, not this section)
/-- 20:A2 (p00004) — Finitude: for any reading of capacity $R$ the registered Universe embeds in the shell of $R$ members, and among $R+1$ members two share a residue; the totality is finite, its cardinality $\Omega$. -/
theorem finitude : And (∀ {U : Type} (R : Nat) [FRC.Pos R] (ρ : U → Nat), (∀ (u : U), @LT.lt Nat instLTNat (ρ u) R) → @Exists (@FRC.Foundation.Registered U ρ → FRC.Shell R) fun ι => ∀ (a b : @FRC.Foundation.Registered U ρ), @Eq (FRC.Shell R) (ι a) (ι b) → @Eq (@FRC.Foundation.Registered U ρ) a b) (And (∀ {U : Type} (R : Nat) (ρ : U → Nat), (∀ (u : U), @LT.lt Nat instLTNat (ρ u) R) → ∀ (f : Nat → U), @Exists Nat fun i => @Exists Nat fun j => And (@LT.lt Nat instLTNat i (@HAdd.hAdd Nat Nat Nat (@instHAdd Nat instAddNat) R (@OfNat.ofNat Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))) (And (@LT.lt Nat instLTNat j (@HAdd.hAdd Nat Nat Nat (@instHAdd Nat instAddNat) R (@OfNat.ofNat Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))) (And (@Ne Nat i j) (@Eq Nat (ρ (f i)) (ρ (f j)))))) (∀ (s K : Nat), @LE.le Nat instLENat (@OfNat.ofNat Nat (nat_lit 2) (instOfNatNat (nat_lit 2))) s → ∀ {N : Nat} [FRC.Pos N] (ρ : FRC.Shell N → Nat), (∀ (x : FRC.Shell N), @LT.lt Nat instLTNat (ρ x) (FRC.Logic.records s K)) → (∀ (x y : FRC.Shell N), @Eq Nat (ρ x) (ρ y) → @Eq (FRC.Shell N) x y) → And (@LE.le Nat instLENat N (FRC.Logic.records s K)) (@LT.lt Nat instLTNat (FRC.Logic.records s K) (@HPow.hPow Nat Nat Nat (@instHPow Nat Nat (@instPowNat Nat instNatPowNat)) s (@HAdd.hAdd Nat Nat Nat (@instHAdd Nat instAddNat) K (@OfNat.ofNat Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))))) :=
  @FRC.Ledger.p00004
/-- 20:A3 (p00003) — Completeness: whatever exists is registered within, the registration of any totality being onto its registered Universe, so there is no outside and no host; two totalities each registered whole within the other have one count. -/
theorem completeness_of_totality : (∀ {U : Type} (ρ : U → Nat) (a : FRC.Foundation.Registered ρ), ∃ u, FRC.Foundation.register ρ u = a) ∧ ∀ (m n : Nat) [FRC.Pos m] [FRC.Pos n] (f : FRC.Shell m → FRC.Shell n), (∀ (x y : FRC.Shell m), f x = f y → x = y) → ∀ (g : FRC.Shell n → FRC.Shell m), (∀ (x y : FRC.Shell n), g x = g y → x = y) → m = n :=
  @FRC.Ledger.p00003
/-- 20:A4 (p00197) — Observation: every observation is a registration by an embedded part of $o<\Omega$ states; every reading identifies two members, and a complete reading needs the whole count; one translation carries each member to each. -/
theorem incompleteness_of_observation : (∀ {Ω o : Nat} [FRC.Pos Ω], o < Ω → ∀ (ρ : FRC.Shell Ω → Nat), (∀ (x : FRC.Shell Ω), ρ x < o) → ∃ x y, x ≠ y ∧ ρ x = ρ y) ∧ (∀ {Ω o : Nat} [FRC.Pos Ω] (ρ : FRC.Shell Ω → Nat), (∀ (x : FRC.Shell Ω), ρ x < o) → (∀ (x y : FRC.Shell Ω), ρ x = ρ y → x = y) → Ω ≤ o) ∧ ∀ {Ω : Nat} [FRC.Pos Ω] (x y : FRC.Shell Ω), ∃ t, x + t = y ∧ ∀ (t' : FRC.Shell Ω), x + t' = y → t' = t :=
  @FRC.Ledger.p00197
/-- 20:B1 (p20008) — The two frames and their alignment: the Carrier's chart $\F_\Omega$, held by no embedded observer, and the Subject $\Fp$, $\p^{2}<\Omega$. Shared: the origin, the unit and the rules of arithmetic, so the labels of the window and the counts of the modes. Not shared: the generator and the drive; the cycles admit no projection ($12\nmid232$). -/
theorem two_frames_alignment : (13 : Nat) * (13 : Nat) < (233 : Nat) ∧ (12 : Nat) % (4 : Nat) = (0 : Nat) ∧ (232 : Nat) % (4 : Nat) = (0 : Nat) ∧ (232 : Nat) % (3 : Nat) ≠ (0 : Nat) ∧ (5 : FRC.Shell (13 : Nat)) * (5 : FRC.Shell (13 : Nat)) = (-1 : FRC.Shell (13 : Nat)) ∧ (89 : FRC.Shell (233 : Nat)) * (89 : FRC.Shell (233 : Nat)) = (-1 : FRC.Shell (233 : Nat)) ∧ (232 : Nat) % (12 : Nat) ≠ (0 : Nat) ∧ (3 : Nat) * (3 : Nat) < (13 : Nat) ∧ (3 : Nat) * (3 : Nat) < (233 : Nat) :=
  @FRC.Ledger.p20008
set_option linter.defProp false in
/-- 20:B2 (p20009) — Frame coincidence within the observational horizon $\q$, the largest label with $\q^{2}<\p$: for $n\le\q$ the residue $n$ is the same integer in $\Fp$ and $\F_\Omega$, and primality of $n$ equals irreducibility in the Subject chart; the Subject-realised primes $\Pi_\p$ are the primes to $\q$. A prime is a label on the prime meridian within the horizon. -/
def frame_coincidence_below_horizon := @FRC.Ledger.p20009
/-- 20:B4 (p20011) — Zero-slot: on every shell $Z_\p(k)=\sum_{x\in\Fx{\p}}x^{k}$ vanishes at every nonconstant mode, $1\le k\le\p-2$, and equals $-1$ at the constant mode; it uses no generator and holds on the chart of the Carrier. -/
theorem zero_slot_vanishing : ∀ {p : Nat} [FRC.Pos p] {κ : Nat} {g : FRC.Shell p}, FRC.Shell.Frame p κ g → (∀ (k : Nat), (0 : Nat) < k → k < p - (1 : Nat) → FRC.Shell.sumRange (fun l => FRC.Shell.ofNat (l + (1 : Nat)) ^ k) (p - (1 : Nat)) = (0 : FRC.Shell p)) ∧ FRC.Shell.sumRange (fun l => FRC.Shell.ofNat (l + (1 : Nat)) ^ (p - (1 : Nat))) (p - (1 : Nat)) = (-1 : FRC.Shell p) :=
  @FRC.Ledger.p20011
/-- 20:B10 (p20017) — The Subject constants on the shell: $\pi=2\kp$, $2\pi\equiv-1$, $\im=\gen^{-\kp}$, $\im^{2}\equiv-1$, $\E=\gen^{\,\im}$ on the odd lift, $\gen^{\,\pi}\equiv-1$, $\E^{\,\im\pi}\equiv-1$; on $\F_{13}$: $\gen=2$, $\im=5$, $\E=6$, $\pi=6$. -/
theorem subject_constants_shell : (∀ {p : Nat} [FRC.Pos p] {κ : Nat} {g : FRC.Shell p}, FRC.Shell.Frame p κ g → FRC.Shell.ofNat ((2 : Nat) * FRC.Shell.Frame.halfPeriod κ) = (-1 : FRC.Shell p) ∧ g ^ ((3 : Nat) * κ) = FRC.Shell.Frame.quarterTurn g κ ∧ FRC.Shell.Frame.quarterTurn g κ * FRC.Shell.Frame.quarterTurn g κ = (-1 : FRC.Shell p) ∧ g ^ ((2 : Nat) * κ) = (-1 : FRC.Shell p) ∧ ∀ (m : Nat), m % (2 : Nat) = (1 : Nat) → (g ^ m) ^ (m * ((2 : Nat) * κ)) = (-1 : FRC.Shell p)) ∧ ((2 : FRC.Shell (13 : Nat)) * (6 : FRC.Shell (13 : Nat)) = (-1 : FRC.Shell (13 : Nat)) ∧ (2 : FRC.Shell (13 : Nat)) ^ (9 : Nat) = (5 : FRC.Shell (13 : Nat)) ∧ FRC.Shell.Frame.quarterTurn (2 : FRC.Shell (13 : Nat)) (3 : Nat) = (5 : FRC.Shell (13 : Nat)) ∧ (5 : FRC.Shell (13 : Nat)) * (5 : FRC.Shell (13 : Nat)) = (-1 : FRC.Shell (13 : Nat)) ∧ (2 : FRC.Shell (13 : Nat)) ^ (5 : Nat) = (6 : FRC.Shell (13 : Nat)) ∧ (2 : FRC.Shell (13 : Nat)) ^ (6 : Nat) = (-1 : FRC.Shell (13 : Nat)) ∧ (6 : FRC.Shell (13 : Nat)) ^ ((5 : Nat) * (6 : Nat)) = (-1 : FRC.Shell (13 : Nat))) ∧ FRC.Shell.Frame (13 : Nat) (3 : Nat) (2 : FRC.Shell (13 : Nat)) :=
  @FRC.Ledger.p20017
/-- 20:D19 (p20119) — The value of a mode at one label: on every framed shell, for a label $\ell\ge2$ and integers $M\ge1$ with $\ell^{M}<\p$ and $V\ge1$ with $MV\ge\p-1$, every nonzero residue is $\ell^{k}\gen^{\,r}$ with a count $k$ (G1) and $r<V$ (E15): $r$ steps of the drive after the mode's value. For the label $3$ on the Subject $\F_{1549}$: largest $M=6$, least $V=258$. -/
theorem steps_after_mode : ∀ {p : Nat} [FRC.Pos p] {κ : Nat} {g : FRC.Shell p}, FRC.Shell.Frame p κ g → ∀ {ℓ N W : Nat}, (1 : Nat) < ℓ → (0 : Nat) < N → ℓ ^ N < p → (0 : Nat) < W → p - (1 : Nat) ≤ N * W → ∀ (y : FRC.Shell p), y ≠ (0 : FRC.Shell p) → ∃ k r, k < p - (1 : Nat) ∧ r < W ∧ FRC.Shell.ofNat ℓ ^ k * g ^ r = y :=
  @FRC.Ledger.p20119
/-- 20:E12 (p20043) — \textbf{The shell theorem.} On every shell, for every vector, in $\Fp$: (i) the dual $\hat v(k)=\sum v(x)x^{k}$ inverts exactly, $v(y)=-\sum\hat v(k)y^{-k}$, the constant mode the mean term; (ii) the Parseval identity (E13); (iii) every mode is an eigenvector of the drive (E15), each nonconstant one with its zero at $k+1$ (G1); (iv) the parity and (v) the explicit formula along the meridian (E14). -/
theorem shell_theorem : (∀ {p : Nat} [FRC.Pos p] {κ : Nat} {g : FRC.Shell p}, FRC.Shell.Frame p κ g → (∀ (k : Nat), (0 : Nat) < k → k < p - (1 : Nat) → FRC.Shell.sumRange (fun l => FRC.Shell.ofNat (l + (1 : Nat)) ^ k) (p - (1 : Nat)) = (0 : FRC.Shell p)) ∧ FRC.Shell.sumRange (fun l => FRC.Shell.ofNat (l + (1 : Nat)) ^ (p - (1 : Nat))) (p - (1 : Nat)) = (-1 : FRC.Shell p)) ∧ (∀ {p : Nat} [FRC.Pos p] {κ : Nat} {g : FRC.Shell p}, FRC.Shell.Frame p κ g → ∀ (v : Nat → FRC.Shell p) {j : Nat}, j < p - (1 : Nat) → v j = FRC.Shell.sumRange (fun k => FRC.Horizon.modeCoeff g v k * (g ^ j) ^ k) (p - (1 : Nat))) ∧ (∀ {p : Nat} [FRC.Pos p] {g : FRC.Shell p} (r k : Nat) (x : FRC.Shell p), (g ^ r * x) ^ k = (g ^ r) ^ k * x ^ k) ∧ (∀ {p : Nat} [FRC.Pos p] {κ : Nat} {g : FRC.Shell p}, FRC.Shell.Frame p κ g → ∀ (r k : Nat), ((g ^ r) ^ k) ^ (p - (1 : Nat)) = (1 : FRC.Shell p)) ∧ (∀ {p : Nat} [FRC.Pos p] {κ : Nat} {g : FRC.Shell p}, FRC.Shell.Frame p κ g → ∀ (r : Nat), FRC.Shell.Frame.natCount (fun x => x ≠ (0 : Nat) ∧ g ^ r * FRC.Shell.ofNat x = FRC.Shell.ofNat x) p = if r % (p - (1 : Nat)) = (0 : Nat) then p - (1 : Nat) else (0 : Nat)) ∧ (∀ {p : Nat} [FRC.Pos p] {κ : Nat} {g : FRC.Shell p}, FRC.Shell.Frame p κ g → ∀ (ν θ : FRC.Shell p), (FRC.Horizon.readout ν κ θ).trace = (1 : FRC.Shell p) ∧ (FRC.Horizon.readout ν κ θ).re = FRC.Shell.ofNat ((2 : Nat) * κ + (1 : Nat)) ∧ ∀ (θ' : FRC.Shell p), FRC.Horizon.readout ν κ θ = FRC.Horizon.readout ν κ θ' → θ = θ') ∧ ∀ {p : Nat} [FRC.Pos p] {κ : Nat} {g : FRC.Shell p}, FRC.Shell.Frame p κ g → ∀ (k : Nat), (1 : Nat) ≤ k → k ≤ p - (2 : Nat) → -g ^ k ≠ (0 : FRC.Shell p) ∧ -g ^ k ≠ (-1 : FRC.Shell p) :=
  @FRC.Ledger.p20043
/-- 20:E13 (p20044) — The Parseval identity: $\sum_k\hat v(k)\hat v(-k)=-\sum_x v(x)^{2}$ on every shell, the finite Parseval identity of the cycle with the self-pairing $-1$ instead of the complex norm; in the chart of the cycle the $\p-1$ complex characters are an orthogonal basis with $\lVert\chi_j\rVert^{2}=\p-1$ and the same identity becomes $\sum_j|\hat v_{\mathbb C}(j)|^{2}=(\p-1)\sum|v|^{2}$. -/
theorem parseval_identity : ∀ {p : Nat} [FRC.Pos p] {κ : Nat} {g : FRC.Shell p}, FRC.Shell.Frame p κ g → ∀ (v : Nat → FRC.Shell p), FRC.Shell.sumRange (fun k => FRC.Horizon.dual g v k * FRC.Horizon.modeCoeff g v k) (p - (1 : Nat)) = FRC.Shell.sumRange (fun l => v l * v l) (p - (1 : Nat)) :=
  @FRC.Ledger.p20044
set_option linter.defProp false in
/-- 20:E14 (p20092) — The parity and the explicit formula: (iv) $W^{2}=-J$, $F^{2}=J$, $F^{4}=1$; (v) for every vector and every $x\le\p-1$, $\sum_{y\le x}v(y)=-\sum_k\hat v(k)S_k(x)$ with $S_k(x)=\sum_{y\le x}y^{-k}$ and $S_0(x)=x$, along the meridian, from the inversion on the residues with the self-pairing $-1$. -/
def parity_explicit_formula := @FRC.Ledger.p20092
/-- 20:E15 (p20094) — \textbf{The drive theorem.} The drive $(Dv)(x)=v(\gen x)$ permutes the residues and is orthogonal for the pairing of E12 (i); its eigenvectors are the modes $x^{k}$ and their nonzero multiples, eigenvalue $\gen^{k}$, the spectrum $\Fx{\p}$, simple; the modes are isotropic for $k\ne0,\pi$; at $x=\gen^{m}$ the mode $k$ has the value $\gen^{km}$. -/
theorem drive_theorem : (∀ {p : Nat} [FRC.Pos p] {g : FRC.Shell p} (r k : Nat) (x : FRC.Shell p), (g ^ r * x) ^ k = (g ^ r) ^ k * x ^ k) ∧ (∀ {p : Nat} [FRC.Pos p] {κ : Nat} {g : FRC.Shell p}, FRC.Shell.Frame p κ g → ∀ (v w : Nat → FRC.Shell p), FRC.Shell.sumRange (fun l => v ((l + (1 : Nat)) % (p - (1 : Nat))) * w l) (p - (1 : Nat)) = FRC.Shell.sumRange (fun l => v l * w ((l + (p - (2 : Nat))) % (p - (1 : Nat)))) (p - (1 : Nat))) ∧ (∀ {p : Nat} [FRC.Pos p] {κ : Nat} {g : FRC.Shell p}, FRC.Shell.Frame p κ g → ∀ {i j : Nat}, i < p - (1 : Nat) → j < p - (1 : Nat) → g ^ i = g ^ j → i = j) ∧ (∀ {p : Nat} [FRC.Pos p] {κ : Nat} {g : FRC.Shell p}, FRC.Shell.Frame p κ g → ∀ {k : Nat}, g ^ ((2 : Nat) * k) ≠ (1 : FRC.Shell p) → FRC.Shell.sumRange (fun l => (g ^ l) ^ k * (g ^ l) ^ k) (p - (1 : Nat)) = (0 : FRC.Shell p)) ∧ ∀ {p : Nat} [FRC.Pos p] (g : FRC.Shell p) (m k : Nat), (g ^ m) ^ k = (g ^ k) ^ m ∧ (g ^ m) ^ k = g ^ (k * m) :=
  @FRC.Ledger.p20094
set_option linter.defProp false in
/-- 20:F7 (p20079) — \textbf{The closure.} The zeros of a shell are its residues other than $0$ and $1$, and there are no others (G6). ``All the zeros'' of the Carrier is one complete list, the $\Omega-2$ residues of its chart other than $0$ and $1$ (A2, A3). No embedded Subject holds it whole (A4): every reading into its $\p<\Omega-2$ states identifies two zeros. -/
def zeros_closure := @FRC.Ledger.p20079
/-- 20:G2 (p20097) — The count operator: $N$ multiplies the mode of count $k$ by $k$. A count $k\ge1$ and its conjugate add to $-1$. For all vectors $\langle Nv,w\rangle+\langle v,Nw\rangle+\langle v,w\rangle=-c_0d_0$, with $c_0$, $d_0$ the constant parts. So the adjoint of $N$ is $-1-N$ on the vectors with no constant part. Rests on B4, G1. -/
theorem count_operator : (∀ {p : Nat} [FRC.Pos p] {k : Nat}, (0 : Nat) < k → k < p - (1 : Nat) → ((0 : Nat) < p - (1 : Nat) - k ∧ p - (1 : Nat) - k < p - (1 : Nat)) ∧ FRC.Shell.ofNat k + FRC.Shell.ofNat (p - (1 : Nat) - k) + (1 : FRC.Shell p) = (0 : FRC.Shell p)) ∧ (∀ {p : Nat} [FRC.Pos p] {κ : Nat} {g : FRC.Shell p}, FRC.Shell.Frame p κ g → ∀ {k m : Nat}, (0 : Nat) < k → k < p - (1 : Nat) → m < p - (1 : Nat) → (FRC.Shell.ofNat k + FRC.Shell.ofNat m + (1 : FRC.Shell p)) * FRC.Shell.sumRange (fun l => FRC.Shell.ofNat (l + (1 : Nat)) ^ k * FRC.Shell.ofNat (l + (1 : Nat)) ^ m) (p - (1 : Nat)) = (0 : FRC.Shell p)) ∧ ∀ {p : Nat} [FRC.Pos p] {κ : Nat} {g : FRC.Shell p}, FRC.Shell.Frame p κ g → ∀ (c d : Nat → FRC.Shell p), FRC.Horizon.pairing (FRC.Horizon.modeVector fun k => FRC.Shell.ofNat k * c k) (FRC.Horizon.modeVector d) + FRC.Horizon.pairing (FRC.Horizon.modeVector c) (FRC.Horizon.modeVector fun k => FRC.Shell.ofNat k * d k) + FRC.Horizon.pairing (FRC.Horizon.modeVector c) (FRC.Horizon.modeVector d) = -(c (0 : Nat) * d (0 : Nat)) :=
  @FRC.Ledger.p20097
/-- 20:G3 (p20098) — The half is forced: $N+c$ is skew on the nonconstant modes exactly when $2c\equiv1$. In a run of $\p-1$ consecutive counts that starts at $m(\p-1)$ or one above, the condition holds exactly for $c=2^{-1}+m$; in every other run it holds for no $c$. Rests on G2. -/
theorem forced_half : (∀ {p : Nat} [FRC.Pos p], (2 : Nat) < p → ∀ (c : FRC.Shell p), (∀ (k : Nat), (0 : Nat) < k → k < p - (1 : Nat) → FRC.Shell.ofNat k + c + (FRC.Shell.ofNat (p - (1 : Nat) - k) + c) = (0 : FRC.Shell p)) ↔ (2 : FRC.Shell p) * c = (1 : FRC.Shell p)) ∧ (∀ {p : Nat} [FRC.Pos p] (m : Nat) {k : Nat}, k ≤ p - (1 : Nat) → FRC.Shell.ofNat (m * (p - (1 : Nat)) + k) + FRC.Shell.ofNat (m * (p - (1 : Nat)) + (p - (1 : Nat) - k)) + FRC.Shell.ofNat ((2 : Nat) * m + (1 : Nat)) = (0 : FRC.Shell p)) ∧ ∀ {p : Nat} [FRC.Pos p] {κ : Nat} {g : FRC.Shell p}, FRC.Shell.Frame p κ g → ∀ (m : Nat) {r : Nat}, (2 : Nat) ≤ r → r + (1 : Nat) ≤ p - (1 : Nat) → ∀ (c : FRC.Shell p), ¬∀ (a b : Nat), m * (p - (1 : Nat)) + r ≤ a → a < m * (p - (1 : Nat)) + r + (p - (1 : Nat)) → m * (p - (1 : Nat)) + r ≤ b → b < m * (p - (1 : Nat)) + r + (p - (1 : Nat)) → a % (p - (1 : Nat)) ≠ (0 : Nat) → (a + b) % (p - (1 : Nat)) = (0 : Nat) → FRC.Shell.ofNat a + c + (FRC.Shell.ofNat b + c) = (0 : FRC.Shell p) :=
  @FRC.Ledger.p20098
/-- 20:G5 (p20100) — The generator: $H$ and $\im H=N+2^{-1}$ are skew for the pairing on the vectors with no constant part, $(\gamma_k+\gamma_m)\langle x^{k},x^{m}\rangle=0$ unless both modes are constant, and the conjugate of a nonconstant mode has the frequency $-\gamma_k$. Rests on G2, G3, G4. -/
theorem skew_generator : (∀ {p : Nat} [FRC.Pos p] {κ : Nat} {g : FRC.Shell p}, FRC.Shell.Frame p κ g → ∀ {k m : Nat}, k < p - (1 : Nat) → m < p - (1 : Nat) → (0 : Nat) < k ∨ (0 : Nat) < m → (FRC.Horizon.frequency g κ k + FRC.Horizon.frequency g κ m) * FRC.Horizon.gram p k m = (0 : FRC.Shell p)) ∧ ∀ {p : Nat} [FRC.Pos p] {κ : Nat} {g : FRC.Shell p}, FRC.Shell.Frame p κ g → ∀ {k : Nat}, k ≤ p - (1 : Nat) → FRC.Shell.ofNat (p - (1 : Nat) - k + (1 : Nat)) = (1 : FRC.Shell p) + -FRC.Shell.ofNat (k + (1 : Nat)) ∧ FRC.Horizon.frequency g κ (p - (1 : Nat) - k) = -FRC.Horizon.frequency g κ k :=
  @FRC.Ledger.p20100
/-- 20:G6 (p20101) — The zeros: the zero of the nonconstant mode $k$ is $2^{-1}+\im\gamma_k=k+1$. The zeros of the nonconstant modes are the residues other than $0$ and $1$, one each. The conjugate mode has the zero $1-\rho_k$, and $\rho\mapsto1-\rho$ is the one affine map besides the identity that keeps the pair of origin and unit. Rests on B4, G1, G4, G5. -/
theorem zeros_critical_line : (∀ {p : Nat} [FRC.Pos p] {κ : Nat} {g : FRC.Shell p}, FRC.Shell.Frame p κ g → ∀ (k : Nat), FRC.Shell.ofNat ((2 : Nat) * κ + (1 : Nat)) + FRC.Shell.Frame.quarterTurn g κ * FRC.Horizon.frequency g κ k = FRC.Shell.ofNat (k + (1 : Nat))) ∧ (∀ {p : Nat} [FRC.Pos p], (1 : Nat) < p → ∀ (r : FRC.Shell p), r ≠ (0 : FRC.Shell p) ∧ r ≠ (1 : FRC.Shell p) ↔ ∃ k, (0 : Nat) < k ∧ k < p - (1 : Nat) ∧ r = FRC.Shell.ofNat (k + (1 : Nat))) ∧ (∀ {p : Nat} [FRC.Pos p] {κ : Nat} {g : FRC.Shell p}, FRC.Shell.Frame p κ g → ∀ {k : Nat}, k ≤ p - (1 : Nat) → FRC.Shell.ofNat (p - (1 : Nat) - k + (1 : Nat)) = (1 : FRC.Shell p) + -FRC.Shell.ofNat (k + (1 : Nat)) ∧ FRC.Horizon.frequency g κ (p - (1 : Nat) - k) = -FRC.Horizon.frequency g κ k) ∧ ∀ {p : Nat} [FRC.Pos p] (a b : FRC.Shell p), (a * (0 : FRC.Shell p) + b = (0 : FRC.Shell p) ∧ a * (1 : FRC.Shell p) + b = (1 : FRC.Shell p) ∨ a * (0 : FRC.Shell p) + b = (1 : FRC.Shell p) ∧ a * (1 : FRC.Shell p) + b = (0 : FRC.Shell p) ↔ a = (1 : FRC.Shell p) ∧ b = (0 : FRC.Shell p) ∨ a = (-1 : FRC.Shell p) ∧ b = (1 : FRC.Shell p)) ∧ ∀ (x : FRC.Shell p), x = (1 : FRC.Shell p) + -x ↔ (2 : FRC.Shell p) * x = (1 : FRC.Shell p) :=
  @FRC.Ledger.p20101
set_option linter.defProp false in
/-- 20:G7 (p20102) — The centre: the mode of count $\pi$ is its own conjugate. Its zero is $2^{-1}=2\kp+1=-\pi$, the one fixed point of $\rho\mapsto1-\rho$. Its frequency is $0$, alone among the modes. For a conjugate pair $\rho(1-\rho)=2^{-2}+\gamma^{2}=-k(k+1)$. Rests on G6. -/
def centre_of_zeros := @FRC.Ledger.p20102
set_option linter.defProp false in
/-- 20:G9 (p20104) — The order of the zeros: the pair of energy $\pi-j$ has its zeros at $2^{-1}\pm j$, for $j=0,\dots,\pi-1$. From the centre outward the energy falls by one at each step. Rests on G7, G8. -/
def order_of_zeros := @FRC.Ledger.p20104
/-- 20:G10 (p20105) — The cardinal domains: a mode takes all its values in $\{1,\im,-1,-\im\}$ exactly when its count is $0$, $\kp$, $2\kp$ or $3\kp$. These modes stand at $1$, $3\cdot4^{-1}$, $2^{-1}$ and $4^{-1}$. So the energy latitude $L_{\kp+1}$ is the time latitude $L_1$ one quarter-turn of the count on. Rests on G1. -/
theorem cardinal_domains : (∀ {p : Nat} [FRC.Pos p] {κ : Nat} {g : FRC.Shell p}, FRC.Shell.Frame p κ g → ∀ {k : Nat}, k < p - (1 : Nat) → ((∀ (x : FRC.Shell p), x ≠ (0 : FRC.Shell p) → x ^ k = (1 : FRC.Shell p) ∨ x ^ k = (-1 : FRC.Shell p) ∨ x ^ k = FRC.Shell.Frame.quarterTurn g κ ∨ x ^ k = -FRC.Shell.Frame.quarterTurn g κ) ↔ k = (0 : Nat) ∨ k = κ ∨ k = (2 : Nat) * κ ∨ k = (3 : Nat) * κ)) ∧ ∀ {p : Nat} [FRC.Pos p] {κ : Nat}, p = (4 : Nat) * κ + (1 : Nat) → FRC.Shell.ofNat ((0 : Nat) + (1 : Nat)) = (1 : FRC.Shell p) ∧ (4 : FRC.Shell p) * FRC.Shell.ofNat (κ + (1 : Nat)) = (3 : FRC.Shell p) ∧ (2 : FRC.Shell p) * FRC.Shell.ofNat ((2 : Nat) * κ + (1 : Nat)) = (1 : FRC.Shell p) ∧ (4 : FRC.Shell p) * FRC.Shell.ofNat ((3 : Nat) * κ + (1 : Nat)) = (1 : FRC.Shell p) :=
  @FRC.Ledger.p20105
set_option linter.defProp false in
/-- 20:G12 (p20107) — The Carrier's chart, with $\Omega$, $\dS$, $G=2\dS$ for $\p$, $\kp$, $\pi$: the conjugate of a count $1\le k\le\Omega-2$ is $\Omega-1-k$, the centre of the zeros is $2^{-1}=2\dS+1=-G$, and the counts $0$, $\dS$, $2\dS$, $3\dS$ stand at $1$, $3\cdot4^{-1}$, $2^{-1}$, $4^{-1}$. A Subject's nonconstant mode has the same count and zero there. Rests on G2, G6, G10, G11. -/
def carrier_chart := @FRC.Ledger.p20107
/-- 20:G13 (p20111) — The critical circle $\mathcal C$, the points $(a,m)$ of the orbital sphere with $a\,(\gen^{m}+\gen^{-m})=1$: a point and its mirror represent a zero and its conjugate exactly there, with $a^{2}=\rho(1-\rho)$. $\mathcal C$ has one point at each phase $m<\pi$ but $\kp$, and the centre alone on the prime meridian. Its half-turn, the points with $a\,(\gen^{m}+\gen^{-m})=-1$, represents the counts, disjoint from it. -/
theorem critical_circle : (∀ {p : Nat} [FRC.Pos p] {κ : Nat} {g : FRC.Shell p}, FRC.Shell.Frame p κ g → ∀ {a u v : FRC.Shell p}, u * v = (1 : FRC.Shell p) → a * u + a * v = (1 : FRC.Shell p) → (a * u ≠ (0 : FRC.Shell p) ∧ a * u ≠ (1 : FRC.Shell p)) ∧ a * v = (1 : FRC.Shell p) + -(a * u) ∧ a * a = a * u * ((1 : FRC.Shell p) + -(a * u))) ∧ (∀ {p : Nat} [FRC.Pos p] {κ : Nat} {g : FRC.Shell p}, FRC.Shell.Frame p κ g → ∀ (k : Nat), FRC.Shell.ofNat (k + (1 : Nat)) + -((1 : FRC.Shell p) + -FRC.Shell.ofNat (k + (1 : Nat))) = (2 : FRC.Shell p) * (FRC.Shell.Frame.quarterTurn g κ * FRC.Horizon.frequency g κ k)) ∧ (∀ {p : Nat} [FRC.Pos p] {κ : Nat} {g : FRC.Shell p}, FRC.Shell.Frame p κ g → (∀ (a u v : FRC.Shell p), u * v = (1 : FRC.Shell p) → u * u = (-1 : FRC.Shell p) → a * u + a * v ≠ (1 : FRC.Shell p)) ∧ (∀ (u v : FRC.Shell p), (0 : FRC.Shell p) * u + (0 : FRC.Shell p) * v ≠ (1 : FRC.Shell p)) ∧ (∀ (x : FRC.Shell p), x + x = (1 : FRC.Shell p) ↔ x = FRC.Shell.ofNat ((2 : Nat) * κ + (1 : Nat))) ∧ FRC.Horizon.frequency g κ ((2 : Nat) * κ) = (0 : FRC.Shell p)) ∧ (∀ {p : Nat} [FRC.Pos p] {κ : Nat} {g : FRC.Shell p}, FRC.Shell.Frame p κ g → (∀ (r : FRC.Shell p), r ≠ (0 : FRC.Shell p) → r ≠ (1 : FRC.Shell p) → ((∃ a u v, u * v = (1 : FRC.Shell p) ∧ a * u = r ∧ a * v = (1 : FRC.Shell p) + -r) ↔ ∃ a, a * a = r * ((1 : FRC.Shell p) + -r))) ∧ ∀ (a b u v u' v' : FRC.Shell p), a ≠ (0 : FRC.Shell p) → u * v = (1 : FRC.Shell p) → u' * v' = (1 : FRC.Shell p) → a * u = b * u' → a * v = b * v' → b = a ∧ u' = u ∨ b = -a ∧ u' = -u) ∧ (∀ {p : Nat} [FRC.Pos p] {κ : Nat} {g : FRC.Shell p}, FRC.Shell.Frame p κ g → (∀ (m m' : Nat), m + m' = p - (1 : Nat) → ((∃ a, a * g ^ m + a * g ^ m' = (1 : FRC.Shell p)) ↔ g ^ m * g ^ m ≠ (-1 : FRC.Shell p))) ∧ (∀ (m : Nat), m < (2 : Nat) * κ → (g ^ m * g ^ m = (-1 : FRC.Shell p) ↔ m = κ)) ∧ (∀ (a : FRC.Shell p) (m : Nat), -a * g ^ (m + (2 : Nat) * κ) = a * g ^ m) ∧ ∀ (a b : FRC.Shell p) (m m' n n' : Nat), m < (2 : Nat) * κ → n < (2 : Nat) * κ → m + m' = p - (1 : Nat) → n + n' = p - (1 : Nat) → a * g ^ m + a * g ^ m' = (1 : FRC.Shell p) → b * g ^ n + b * g ^ n' = (1 : FRC.Shell p) → a * g ^ m = b * g ^ n → m = n) ∧ (∀ {p : Nat} [FRC.Pos p] {κ : Nat} {g : FRC.Shell p}, FRC.Shell.Frame p κ g → (∀ (a u v : FRC.Shell p), a * u + a * v = (1 : FRC.Shell p) → -a * v = a * u + (-1 : FRC.Shell p) ∧ -a * u = -(a * u) ∧ -a * v + -a * u = (-1 : FRC.Shell p)) ∧ (∀ (k : Nat), FRC.Shell.ofNat (k + (1 : Nat)) + (-1 : FRC.Shell p) = FRC.Shell.ofNat k) ∧ ∀ (x : FRC.Shell p), x + x = (-1 : FRC.Shell p) ↔ x = FRC.Shell.ofNat ((2 : Nat) * κ)) ∧ (∀ {p : Nat} [FRC.Pos p], (∀ (a b u v : FRC.Shell p), a * u + a * v = (1 : FRC.Shell p) → b * u + b * v = (1 : FRC.Shell p) → a = b) ∧ ∀ (a u v : FRC.Shell p), a * v = (1 : FRC.Shell p) + -(a * u) → a * u + a * v = (1 : FRC.Shell p)) ∧ ∀ {p : Nat} [FRC.Pos p] {κ : Nat} {g : FRC.Shell p}, FRC.Shell.Frame p κ g → (∀ (a c u v : FRC.Shell p), c ≠ (0 : FRC.Shell p) → (a * u + a * v = (1 : FRC.Shell p) ↔ c * a * u + c * a * v = c)) ∧ (∀ (a c u v : FRC.Shell p), a * u + a * v = c → -a * u + -a * v = -c) ∧ (∀ (a u v : FRC.Shell p), u * v = (1 : FRC.Shell p) → (a * u + a * v = (0 : FRC.Shell p) ↔ a = (0 : FRC.Shell p) ∨ u * u = (-1 : FRC.Shell p))) ∧ (∀ (c x : FRC.Shell p), x + x = c ↔ x = c * FRC.Shell.ofNat ((2 : Nat) * κ + (1 : Nat))) ∧ ∀ (a u v : FRC.Shell p), a * u + a * v = (1 : FRC.Shell p) → a * u + a * v ≠ (-1 : FRC.Shell p) :=
  @FRC.Ledger.p20111
/-- 20:G14 (p20115) — The places of the zeros: every zero is $z/(1+z)$ for one $z=\rho/(1-\rho)\ne0,-1$. With $z=\gen^{j}$ the zeros stand on the latitude cycle $C_{\p-1}$, one at each place but $j=\pi$: the centre at $0$, the conjugate at $-j$, the points of the circle at the even places $j=2m$. $2\rho-1=(z-1)/(z+1)$, and $x\mapsto(x-1)/(x+1)$ has the square $x\mapsto-1/x$ and fixes $\pm\im$. -/
theorem zeros_on_latitude_cycle : (∀ {p : Nat} [FRC.Pos p] {κ : Nat} {g : FRC.Shell p}, FRC.Shell.Frame p κ g → (∀ (r : FRC.Shell p), r ≠ (0 : FRC.Shell p) → r ≠ (1 : FRC.Shell p) → ∃ t, (t ≠ (0 : FRC.Shell p) ∧ (1 : FRC.Shell p) + t ≠ (0 : FRC.Shell p)) ∧ r * ((1 : FRC.Shell p) + t) = t ∧ ∀ (s : FRC.Shell p), r * ((1 : FRC.Shell p) + s) = s → s = t) ∧ (∀ (r t : FRC.Shell p), t ≠ (0 : FRC.Shell p) → (1 : FRC.Shell p) + t ≠ (0 : FRC.Shell p) → r * ((1 : FRC.Shell p) + t) = t → r ≠ (0 : FRC.Shell p) ∧ r ≠ (1 : FRC.Shell p)) ∧ ∀ (r t t' : FRC.Shell p), t * t' = (1 : FRC.Shell p) → r * ((1 : FRC.Shell p) + t) = t → ((1 : FRC.Shell p) + -r) * ((1 : FRC.Shell p) + t') = t') ∧ (∀ {p : Nat} [FRC.Pos p] {κ : Nat} {g : FRC.Shell p}, FRC.Shell.Frame p κ g → (∀ (t : FRC.Shell p), t ≠ (0 : FRC.Shell p) → (1 : FRC.Shell p) + t ≠ (0 : FRC.Shell p) → ∃ j, j < p - (1 : Nat) ∧ j ≠ (2 : Nat) * κ ∧ g ^ j = t ∧ ∀ (i : Nat), i < p - (1 : Nat) → g ^ i = t → i = j) ∧ (1 : FRC.Shell p) + g ^ ((2 : Nat) * κ) = (0 : FRC.Shell p) ∧ ∀ (r : FRC.Shell p), r * ((1 : FRC.Shell p) + g ^ (0 : Nat)) = g ^ (0 : Nat) ↔ r = FRC.Shell.ofNat ((2 : Nat) * κ + (1 : Nat))) ∧ (∀ {p : Nat} [FRC.Pos p] {κ : Nat} {g : FRC.Shell p}, FRC.Shell.Frame p κ g → (∀ (r t : FRC.Shell p), r * ((1 : FRC.Shell p) + t) = t → ((∃ b, b * b = t) ↔ ∃ a, a * a = r * ((1 : FRC.Shell p) + -r))) ∧ ∀ (j : Nat), j < p - (1 : Nat) → ((∃ b, b * b = g ^ j) ↔ j % (2 : Nat) = (0 : Nat))) ∧ (∀ {p : Nat} [FRC.Pos p] {κ : Nat} {g : FRC.Shell p}, FRC.Shell.Frame p κ g → (∀ (r t : FRC.Shell p), r * ((1 : FRC.Shell p) + t) = t → (r + r + (-1 : FRC.Shell p)) * (t + (1 : FRC.Shell p)) = t + (-1 : FRC.Shell p)) ∧ (∀ (x y z : FRC.Shell p), y * (x + (1 : FRC.Shell p)) = x + (-1 : FRC.Shell p) → z * (y + (1 : FRC.Shell p)) = y + (-1 : FRC.Shell p) → z * x = (-1 : FRC.Shell p)) ∧ ∀ (x : FRC.Shell p), x * (x + (1 : FRC.Shell p)) = x + (-1 : FRC.Shell p) ↔ x * x = (-1 : FRC.Shell p)) ∧ (∀ {p : Nat} [FRC.Pos p] (a u v : FRC.Shell p), u * v = (1 : FRC.Shell p) → a * u + a * v = (1 : FRC.Shell p) → a * u * ((1 : FRC.Shell p) + u * u) = u * u) ∧ ∀ {p : Nat} [FRC.Pos p], (∀ (x z w : FRC.Shell p), z * x = (-1 : FRC.Shell p) → w * z = (-1 : FRC.Shell p) → w = x) ∧ ∀ (x z : FRC.Shell p), z * x = (-1 : FRC.Shell p) → (z = x ↔ x * x = (-1 : FRC.Shell p)) :=
  @FRC.Ledger.p20115
set_option linter.defProp false in
/-- 20:X1 (p20108) — The $\half$ of the critical line: the centre of the zeros of a shell is the inverse of $2$, the negative of the half-period: $2^{-1}=-\pi$ on a Subject and $-G$ on the Carrier's chart. Rests on G7, G12; compared with A6. -/
def half_of_critical_line := @FRC.Ledger.p20108
/-- 20:X2 (p20109) — The pole and the functional equation: the constant mode stands at $1$ and is no zero, the shell's form of the pole at $1$. The symmetry $s\mapsto1-s$ is the exchange of a mode with its conjugate, the symmetry of origin and unit. Rests on B4, G6; compared with A6. -/
theorem pole_and_functional_equation : (∀ {p : Nat} [FRC.Pos p] {κ : Nat} {g : FRC.Shell p}, FRC.Shell.Frame p κ g → (∀ (k : Nat), (0 : Nat) < k → k < p - (1 : Nat) → FRC.Shell.sumRange (fun l => FRC.Shell.ofNat (l + (1 : Nat)) ^ k) (p - (1 : Nat)) = (0 : FRC.Shell p)) ∧ FRC.Shell.sumRange (fun l => FRC.Shell.ofNat (l + (1 : Nat)) ^ (p - (1 : Nat))) (p - (1 : Nat)) = (-1 : FRC.Shell p)) ∧ (∀ {p : Nat} [FRC.Pos p] {κ : Nat} {g : FRC.Shell p}, FRC.Shell.Frame p κ g → ∀ {k : Nat}, k ≤ p - (1 : Nat) → FRC.Shell.ofNat (p - (1 : Nat) - k + (1 : Nat)) = (1 : FRC.Shell p) + -FRC.Shell.ofNat (k + (1 : Nat)) ∧ FRC.Horizon.frequency g κ (p - (1 : Nat) - k) = -FRC.Horizon.frequency g κ k) ∧ ∀ {p : Nat} [FRC.Pos p] (a b : FRC.Shell p), (a * (0 : FRC.Shell p) + b = (0 : FRC.Shell p) ∧ a * (1 : FRC.Shell p) + b = (1 : FRC.Shell p) ∨ a * (0 : FRC.Shell p) + b = (1 : FRC.Shell p) ∧ a * (1 : FRC.Shell p) + b = (0 : FRC.Shell p) ↔ a = (1 : FRC.Shell p) ∧ b = (0 : FRC.Shell p) ∨ a = (-1 : FRC.Shell p) ∧ b = (1 : FRC.Shell p)) ∧ ∀ (x : FRC.Shell p), x = (1 : FRC.Shell p) + -x ↔ (2 : FRC.Shell p) * x = (1 : FRC.Shell p) :=
  @FRC.Ledger.p20109
/-- 20:X3 (p20110) — The $\half$ of the dilation generator: the shift that makes the count operator skew on the nonconstant modes is forced, $2c\equiv1$, and the generator is $H=-\im\,(N+2^{-1})$. In the continuum chart it takes the form $-i(x\partial_x+\half)$. Rests on G3, G5; compared with A6. -/
theorem half_of_dilation_generator : (∀ {p : Nat} [FRC.Pos p], (2 : Nat) < p → ∀ (c : FRC.Shell p), (∀ (k : Nat), (0 : Nat) < k → k < p - (1 : Nat) → FRC.Shell.ofNat k + c + (FRC.Shell.ofNat (p - (1 : Nat) - k) + c) = (0 : FRC.Shell p)) ↔ (2 : FRC.Shell p) * c = (1 : FRC.Shell p)) ∧ ∀ {p : Nat} [FRC.Pos p] {κ : Nat} {g : FRC.Shell p}, FRC.Shell.Frame p κ g → ∀ {k m : Nat}, k < p - (1 : Nat) → m < p - (1 : Nat) → (0 : Nat) < k ∨ (0 : Nat) < m → (FRC.Horizon.frequency g κ k + FRC.Horizon.frequency g κ m) * FRC.Horizon.gram p k m = (0 : FRC.Shell p) :=
  @FRC.Ledger.p20110
-- end ledger predicates

end FRC.Rh
