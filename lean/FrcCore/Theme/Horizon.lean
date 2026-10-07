import FrcCore.Sum
import FrcCore.Theme.Quadratic

/-!
# FrcCore.Theme.Horizon — the horizon theme: the shell theorem (ledger migration, task LM26)

The master's block Z, the limits of the bounded observer, where its rows are exact on every shell. The shell theorem
(00:Z10, 20:E12) in the `𝔽_p` reading, on a frame `(τ; 0, 1, g)` of capacity `κ` (`p = 4κ + 1`, `n = p − 1`):

* the finite zeta `Z(k) = Σ_{x≠0} x^k` vanishes on every nonterminal mode `0 < k < n` and is `−1` on the full
  cycle (`zero_slot`, 20:B4);
* every vector on the cycle expands in the power modes `x ↦ x^k`, `k < n`: the constant mode and the nonterminal
  ones (`mode_expansion`);
* the scale-shift `x ↦ g^r x` has the modes as eigenvectors, `(g^r x)^k = (g^r)^k x^k`, with an `n`-th root of unity
  as eigenvalue (`shift_power_character`, `eigenphase`), and fixes `n·[n ∣ r]` points (`shift_trace`);
* every readout `z(θ) = 2⁻¹ + θη` lies on the self-dual line `Tr z = 1`, `2⁻¹ = 2κ + 1` (`readout_on_line`), and a
  nontrivial slot's index is neither `0` nor `−1` (`readout_slot_index`).

No hypothesis on the vector and none on the shell beyond the frame: no off-line mode, `Ω`-blind. `half_inverse`,
`zero_slot`, `shift_power_character`, `shift_trace`, `readout`, `readout_on_line` and `readout_slot_index` moved here
from `FrcCore/Rh.lean` (20-rh), which keeps each under its old name. No axioms.
-/

namespace FRC.Horizon

open FRC.Shell FRC.Shell.Frame
open FRC.Extension (Ext)

variable {p : Nat} [Pos p] {κ : Nat} {g : Shell p}

/-- Double sums commute: `Σ_{i<n} Σ_{j<m} f i j = Σ_{j<m} Σ_{i<n} f i j`. -/
theorem sum_comm (f : Nat → Nat → Shell p) (m : Nat) : ∀ n,
    sumRange (fun i => sumRange (fun j => f i j) m) n = sumRange (fun j => sumRange (fun i => f i j) n) m
  | 0 => (sum_zero m (fun _ _ => rfl)).symm
  | n + 1 => by
    rw [sumRange_succ, sum_comm f m n, ← sum_add]
    rfl

/-! ## The half-turn (20:B8) -/

/-- 20:B8 — `2⁻¹ = 2κ + 1 = −π` on every shell: `2·(2κ + 1) = 1` and `2κ + 1 = −(2κ)`. -/
theorem half_inverse (F : Frame p κ g) :
    (2 : Shell p) * ofNat (2 * κ + 1) = 1 ∧ (ofNat (2 * κ + 1) : Shell p) = -(ofNat (2 * κ)) := by
  have e : 2 * (2 * κ + 1) = 1 + p := by
    rw [F.cap]
    calc 2 * (2 * κ + 1) = 2 * (2 * κ) + 2 * 1 := Nat.mul_add 2 (2 * κ) 1
      _ = 4 * κ + 2 := by rw [← FRC.Nat.mul_assoc]
      _ = 1 + (4 * κ + 1) := by rw [Nat.add_comm 1, Nat.add_assoc]
  constructor
  · show ofNat 2 * ofNat (2 * κ + 1) = 1
    rw [ofNat_mul, e, ofNat_add_self]
    rfl
  · have e2 : 2 * κ + (2 * κ + 1) = p := by
      rw [← Nat.add_assoc, F.four_kappa]; exact FRC.Nat.sub_add_cancel Pos.pos
    have h : (ofNat (2 * κ) : Shell p) + ofNat (2 * κ + 1) = 0 := by
      rw [ofNat_add, e2]; exact ofNat_self
    exact (neg_eq_of_add_eq_zero h).symm

/-! ## The modes: the finite zeta and the expansion (20:B4, 20:E12 (i)) -/

/-- 20:B4, Z10 — the finite zeta on every shell: over the nonzero residues `x = l + 1`, `l < p − 1`,
`Σ x^k = 0` for every nonterminal exponent `0 < k < p − 1`, and `Σ x^{p−1} = −1` on the full cycle. -/
theorem zero_slot (F : Frame p κ g) :
    (∀ k, 0 < k → k < p - 1 → sumRange (fun l => (ofNat (l + 1) : Shell p) ^ k) (p - 1) = 0) ∧
    sumRange (fun l => (ofNat (l + 1) : Shell p) ^ (p - 1)) (p - 1) = -1 := by
  constructor
  · intro k hk0 hk
    rw [sum_units_eq_sum_pow F (fun x => x ^ k)]
    have e : ∀ m, m < p - 1 → (fun m => (g ^ m) ^ k) m = (fun m => (g ^ k) ^ m) m := fun m _ =>
      pow_mul_comm g m k
    rw [sum_congr (p - 1) e]
    exact (F.principal_root k hk0 hk).2.1
  · rw [sum_units_eq_sum_pow F (fun x => x ^ (p - 1))]
    have e : ∀ m, m < p - 1 → (fun m => (g ^ m) ^ (p - 1)) m = (fun _ => (1 : Shell p)) m := fun m _ => by
      show (g ^ m) ^ (p - 1) = 1
      rw [pow_mul_comm, F.pow_n, one_pow]
    rw [sum_congr (p - 1) e, sum_const, mul_one, F.ofNat_n]

/-- The coefficient of the mode `k` in a vector `v` on the cycle: `c_k = −Σ_{l<n} v_l g^{(n−l)k}`. -/
def modeCoeff (g : Shell p) (v : Nat → Shell p) (k : Nat) : Shell p :=
  sumRange (fun l => v l * -(g ^ ((p - 1 - l) * k))) (p - 1)

/-- 20:E12 (i), Z10 — every vector on the cycle expands in the power modes: at the point `x = g^j`,
`v_j = Σ_{k<p−1} c_k x^k`, the constant mode `k = 0` and the nonterminal modes `0 < k < p − 1`. -/
theorem mode_expansion (F : Frame p κ g) (v : Nat → Shell p) {j : Nat} (hj : j < p - 1) :
    v j = sumRange (fun k => modeCoeff g v k * (g ^ j) ^ k) (p - 1) := by
  have h1 : sumRange (fun k => modeCoeff g v k * (g ^ j) ^ k) (p - 1)
      = sumRange (fun k => sumRange (fun l => v l * (g ^ (k * j) * -(g ^ ((p - 1 - l) * k)))) (p - 1)) (p - 1) := by
    apply sum_congr; intro k _
    unfold modeCoeff
    rw [← sum_mul_right]
    apply sum_congr; intro l _
    rw [← pow_mul, Nat.mul_comm j k, mul_assoc, mul_comm (-(g ^ ((p - 1 - l) * k))) (g ^ (k * j))]
  rw [h1, sum_comm (fun k l => v l * (g ^ (k * j) * -(g ^ ((p - 1 - l) * k)))) (p - 1) (p - 1)]
  have h2 : ∀ l, l < p - 1 → sumRange (fun k => v l * (g ^ (k * j) * -(g ^ ((p - 1 - l) * k)))) (p - 1)
      = v l * (if j = l then 1 else 0) := fun l hl => by
    rw [sum_mul_left, F.dft_inverse hj hl]
  rw [sum_congr (p - 1) h2, sum_eq_single hj (fun l _ hne => by rw [ite_eq_right (fun e => hne e.symm), mul_zero]),
    ite_eq_left rfl, mul_one]

/-! ## The scale-shift (20:E1, 20:E12 (iii)) -/

/-- 20:E1, 20:E12 — the power characters are eigenvectors of the scale-shift `x ↦ g^r x` in the `𝔽_p` reading:
`(g^r x)^k = (g^r)^k · x^k`. -/
theorem shift_power_character (r k : Nat) (x : Shell p) : (g ^ r * x) ^ k = (g ^ r) ^ k * x ^ k :=
  mul_pow _ _ _

/-- 20:E12 (iii), Z10 — the eigenvalue `(g^r)^k` of the mode `k` under the scale-shift is a `(p − 1)`-th root of
unity, independent of the vector. -/
theorem eigenphase (F : Frame p κ g) (r k : Nat) : ((g ^ r) ^ k) ^ (p - 1) = 1 := by
  rw [pow_mul_comm, pow_mul_comm g r (p - 1), F.pow_n, one_pow, one_pow]

/-- 20:E12, 20:E1 — clause (iii) in the `𝔽_p` reading: the fixed-point count of the scale-shift, the trace of its
permutation matrix: `x ↦ g^r x` fixes every nonzero residue when `(p − 1) ∣ r` and none otherwise,
`Tr S^r = (p − 1)·[(p − 1) ∣ r]`; the shell's trace carries no prime data. -/
theorem shift_trace (F : Frame p κ g) (r : Nat) :
    natCount (fun x => x ≠ 0 ∧ g ^ r * ofNat x = ofNat x) p = if r % (p - 1) = 0 then p - 1 else 0 := by
  have hn : p = (p - 1) + 1 := (FRC.Nat.sub_add_cancel Pos.pos).symm
  match (inferInstance : Decidable (r % (p - 1) = 0)) with
  | isTrue h =>
    rw [ite_eq_left h]
    have h1 : g ^ r = 1 := F.pow_eq_one_of_mod h
    have e : ∀ x, x < p → ((x ≠ 0 ∧ g ^ r * ofNat x = ofNat x) ↔ x ≠ 0) := fun x _ =>
      ⟨fun h => h.1, fun h => ⟨h, by rw [h1, one_mul]⟩⟩
    have hc := natCount_ne_zero (p - 1)
    rw [← hn] at hc
    rw [natCount_congr _ _ p e]
    exact hc
  | isFalse h =>
    rw [ite_eq_right h]
    apply natCount_eq_zero
    intro x hx hP
    apply h
    apply F.mod_eq_zero_of_pow_eq_one
    have hx0 : (ofNat x : Shell p) ≠ 0 := fun h0 => by
      have := val_injective h0
      rw [val_ofNat, val_zero, FRC.Nat.mod_eq_of_lt hx] at this
      exact hP.1 this
    apply F.mul_left_cancel hx0
    rw [mul_comm, hP.2, mul_one]

/-! ## The readout on the self-dual line (20:B8, 20:E12 (ii)) -/

variable {ν : Shell p}

/-- 20:E12, 20:B8 — the spectral readout in the core: the mode index `θ` is read at `z(θ) = 2⁻¹ + θη`,
`2⁻¹ = 2κ + 1`, in the quadratic extension `𝔽_p(η)`, `η² = ν`. -/
def readout (ν : Shell p) (κ : Nat) (θ : Shell p) : Ext p ν := ⟨ofNat (2 * κ + 1), θ⟩

/-- 20:E12 (ii), Z10 — every readout lies on the self-dual line `Tr z = 1`, its real part the half-turn
`2⁻¹ = 2κ + 1`, and `θ ↦ z(θ)` is injective: no off-line mode. -/
theorem readout_on_line (F : Frame p κ g) (ν θ : Shell p) :
    Ext.trace (readout ν κ θ) = 1 ∧ (readout ν κ θ).re = ofNat (2 * κ + 1) ∧
    ∀ θ' : Shell p, readout ν κ θ = readout ν κ θ' → θ = θ' := by
  refine ⟨?_, rfl, fun θ' h => Ext.im_congr h⟩
  show ofNat (2 * κ + 1) + ofNat (2 * κ + 1) = 1
  rw [← two_mul', (half_inverse F).1]

/-- 20:E12 — the slot index of a nontrivial slot: for `1 ≤ k ≤ p − 2` the index `θ = Φ(k) = −g^k` is neither
`0` (the centre `2⁻¹`) nor `−1` (the full-cycle exponent), on every shell and with no axioms. -/
theorem readout_slot_index (F : Frame p κ g) (k : Nat) (hk1 : 1 ≤ k) (hk2 : k ≤ p - 2) :
    -(g ^ k) ≠ 0 ∧ -(g ^ k) ≠ -1 := by
  refine ⟨fun h => F.pow_ne_zero k ?_, fun h => ?_⟩
  · calc g ^ k = - -(g ^ k) := (neg_neg _).symm
      _ = -0 := by rw [h]
      _ = 0 := neg_zero
  · have h1 : g ^ k = 1 := by
      calc g ^ k = - -(g ^ k) := (neg_neg _).symm
        _ = - -1 := by rw [h]
        _ = 1 := neg_neg 1
    have hmod := F.mod_eq_zero_of_pow_eq_one h1
    have hlt : k < p - 1 :=
      Nat.lt_of_le_of_lt hk2 (Nat.pred_lt (Nat.ne_of_gt F.n_pos))
    rw [FRC.Nat.mod_eq_of_lt hlt] at hmod
    exact Nat.not_succ_le_zero 0 (by rw [hmod] at hk1; exact hk1)

end FRC.Horizon
