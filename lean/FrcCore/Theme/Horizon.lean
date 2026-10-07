import FrcCore.Transform
import FrcCore.Theme.Extension

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
from `FrcCore/Rh.lean` (20-rh), which keeps each under its old name.

Since task LM36 the theme also holds the rest of 20-rh's shell arithmetic, moved from `Rh.lean` under the same names
(the extension's `Ext.*` without the prefix): slot complementarity (20:B5); the Subject constants (20:B10); the
Ramanujan sum (20:B7); the half-turn `ρ`, the Klein four-group, the critical line, the fixed loci and the energy on the
line in the quadratic extension, and the quarter-turn off the circle (20:B6, B8, B9); frame coincidence below the
horizon (20:B2); and the values on `𝔽₁₃`, `𝔽₅₃` and the laboratory pair `(13, 233)` (20:B1). The theme imports the
transform and the extension, not the orbits, so that its key file stays within the budget of gate G10. No axioms.
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

/-! ## 20-rh's shell arithmetic (task LM36): slot complementarity, the Subject constants (20:B5, 20:B10) -/

/-- 20:B5 — slot complementarity on every shell: `Φ(k) = −g^k` is injective on the nontrivial spectral slots
`0 < k < p − 1`, its values avoid `0` and `−1`, and every residue off `{0, −1}` is `Φ(k)` for one such `k`. -/
theorem slot_complementarity (F : Frame p κ g) :
    (∀ i j, i < p - 1 → j < p - 1 → -(g ^ i) = -(g ^ j) → i = j) ∧
    (∀ k, 0 < k → k < p - 1 → -(g ^ k) ≠ 0 ∧ -(g ^ k) ≠ -1) ∧
    (∀ y : Shell p, y ≠ 0 → y ≠ -1 → ∃ k, 0 < k ∧ k < p - 1 ∧ -(g ^ k) = y) := by
  refine ⟨fun i j hi hj h => ?_, fun k hk0 hk => ⟨fun h => ?_, fun h => ?_⟩, fun y hy0 hy1 => ?_⟩
  · apply F.pow_inj hi hj
    rw [← neg_neg (g ^ i), h, neg_neg]
  · apply F.pow_ne_zero k
    rw [← neg_neg (g ^ k), h, neg_zero]
  · have h1 : g ^ k = 1 := by rw [← neg_neg (g ^ k), h, neg_neg]
    have := F.mod_eq_zero_of_pow_eq_one h1
    rw [FRC.Nat.mod_eq_of_lt hk] at this
    exact Nat.lt_irrefl 0 (this ▸ hk0)
  · have hny : -y ≠ 0 := fun h => hy0 (by rw [← neg_neg y, h, neg_zero])
    match F.eq_pow_of_ne_zero hny with
    | ⟨m, hm, e⟩ =>
      refine ⟨m, Nat.pos_of_ne_zero (fun h0 => ?_), hm, by rw [e, neg_neg]⟩
      rw [h0, pow_zero] at e
      exact hy1 (by rw [← neg_neg y, ← e])

/-- 20:B10 — `i = g^{−κ}`, read as `g^{3κ}` on the cycle of length `4κ`, is the quarter-turn `−g^κ`. -/
theorem quarter_turn_eq_pow (F : Frame p κ g) : g ^ (3 * κ) = quarterTurn g κ := by
  unfold quarterTurn
  have e : 3 * κ = κ + 2 * κ := by
    rw [show (3 : Nat) = 1 + 2 from rfl, FRC.Nat.add_mul, Nat.one_mul]
  rw [e, pow_add, F.half_period, ← mul_neg, mul_one]

/-- 20:B10 — the Subject constants on every shell: `2π = −1` with `π = 2κ`; `i = g^{−κ} = −g^κ` with `i² = −1`;
`g^π = −1`; and `e^{iπ} = (g^m)^{m·π} = −1` for every odd `m` — the convention "`e = g^m` on the odd
representative `m` of `i`" fixes the parity of the exponent, and the identity uses nothing else about `m`. -/
theorem subject_constants (F : Frame p κ g) :
    (ofNat (2 * halfPeriod κ) : Shell p) = -1 ∧ g ^ (3 * κ) = quarterTurn g κ ∧
    quarterTurn g κ * quarterTurn g κ = -1 ∧ g ^ (2 * κ) = -1 ∧
    ∀ m : Nat, m % 2 = 1 → (g ^ m) ^ (m * (2 * κ)) = -1 := by
  refine ⟨F.two_pi, quarter_turn_eq_pow F, F.quarter_turn_sq, F.half_period, fun m hm => ?_⟩
  have h0 : m % 2 ≠ 0 := by rw [hm]; exact fun h => Nat.noConfusion h
  rw [F.euler_identity, ite_eq_right h0]

/-- 20:B10 [value] — on `𝔽₁₃(τ; 0, 1, 2)`: `π = 6`, `2π = −1`, `i = 2^9 = 5 = −2^3`, `i² = −1`, `e = 2^5 = 6`,
`2^π = −1`, `e^{iπ} = 6^{30} = −1`. -/
theorem constants13 :
    (2 : Shell 13) * 6 = -1 ∧ (2 : Shell 13) ^ 9 = 5 ∧ quarterTurn (2 : Shell 13) 3 = 5 ∧
    (5 : Shell 13) * 5 = -1 ∧ (2 : Shell 13) ^ 5 = 6 ∧ (2 : Shell 13) ^ 6 = -1 ∧
    (6 : Shell 13) ^ (5 * 6) = -1 := by decide

/-! ## The Ramanujan sum (20:B7) -/

section ramanujan
variable {q : Nat} [Pos q] {κ' : Nat} {h : Shell q}

/-- Powers of an element of finite order reduce modulo the order. -/
theorem pow_mod_of_pow_eq_one {ω : Shell q} {m : Nat} (hm : 0 < m) (hω : ω ^ m = 1) (l : Nat) :
    ω ^ l = ω ^ (l % m) := by
  match FRC.Nat.mod_spec m hm l with
  | ⟨c, hc⟩ =>
    calc ω ^ l = ω ^ (m * c + l % m) := by rw [← hc]
      _ = (ω ^ m) ^ c * ω ^ (l % m) := by rw [pow_add, pow_mul]
      _ = ω ^ (l % m) := by rw [hω, one_pow, one_mul]

/-- 20:B7 — the flat ground state: in a shell `𝔽_q` with a frame (no zero divisors) and an element `ω` of
order exactly `m`, the Ramanujan sum `Σ_{a=1}^{m−1} ω^{an}` equals `−1` for every `n ≢ 0 (mod m)`. With
`m = p` this is `c_p(n) ≡ −1`: the mode at the spectral origin carries no prime information. -/
theorem ramanujan_sum (F : Frame q κ' h) {m : Nat} (hm : 0 < m) {ω : Shell q} (hω : IsPrimitive ω m)
    (n : Nat) (hn : n % m ≠ 0) :
    sumRange (fun a => ω ^ (n * (a + 1))) (m - 1) = -1 := by
  have hx1 : ω ^ n ≠ 1 := by
    rw [pow_mod_of_pow_eq_one hm hω.1 n]
    exact hω.2 (n % m) (Nat.mod_lt n hm) (Nat.pos_of_ne_zero hn)
  have hxm : (ω ^ n) ^ m = 1 := by rw [pow_mul_comm, hω.1, one_pow]
  have h0 := F.geom_sum_eq_zero m hxm hx1
  have hm' : m = (m - 1) + 1 := (FRC.Nat.sub_add_cancel hm).symm
  rw [hm', sumRange_succ', pow_zero] at h0
  have e : ∀ a, a < m - 1 → (fun a => ω ^ (n * (a + 1))) a = (fun l => (ω ^ n) ^ (l + 1)) a := fun a _ =>
    pow_mul ω n (a + 1)
  rw [sum_congr (m - 1) e]
  rw [add_comm] at h0
  exact eq_neg_of_add_eq_zero h0

/-- 20:B7 [value] — on `𝔽₅₃` with `ω = 16` of order `13`: `c_{13}(n) = Σ_{a=1}^{12} ω^{an} = −1` for every
`0 < n < 13`, and `12 = m − 1` at `n = 0`. -/
theorem ramanujan53 :
    (∀ n, n < 13 → 0 < n → sumRange (fun a => (16 : Shell 53) ^ (n * (a + 1))) 12 = -1) ∧
    sumRange (fun a => (16 : Shell 53) ^ (0 * (a + 1))) 12 = 12 := by decide

end ramanujan

/-! ## The quadratic extension: the half-turn, the critical line, the two loci of agreement (20:B6, 20:B8, 20:B9) -/

section extension
open FRC.Extension.Ext

/-- The functional-equation half-turn `ρ : z ↦ 1 − z`. -/
def rho (z : Ext p ν) : Ext p ν := ⟨1 + -z.re, -z.im⟩

/-- The product `σ = ρ ∘ φ : z ↦ 1 − z̄`. -/
def sigma (z : Ext p ν) : Ext p ν := rho (conj z)

/-- 20:B9 — conjugation `φ` and the half-turn `ρ` generate a Klein four-group: both are involutions and they
commute, `φ ρ = ρ φ = σ`. -/
theorem klein_four (z : Ext p ν) :
    conj (conj z) = z ∧ rho (rho z) = z ∧ conj (rho z) = rho (conj z) := by
  refine ⟨Ext.ext rfl (neg_neg z.im), Ext.ext ?_ (neg_neg z.im), rfl⟩
  show 1 + -(1 + -z.re) = z.re
  rw [neg_add_rev, neg_neg, ← add_assoc, add_neg, zero_add]

/-- 20:B8, 20:B9 — the finite critical line: `Tr z = 1` exactly when `Re z = 2⁻¹ = 2κ + 1`; it is the fixed locus
of `σ = ρ ∘ φ`; every `2⁻¹ + bη` lies on it, one point per residue `b` — `p` points. -/
theorem critical_line (F : Frame p κ g) (z : Ext p ν) :
    (trace z = 1 ↔ z.re = ofNat (2 * κ + 1)) ∧ (sigma z = z ↔ z.re = ofNat (2 * κ + 1)) ∧
    ∀ b : Shell p, trace (⟨ofNat (2 * κ + 1), b⟩ : Ext p ν) = 1 := by
  have hinv := (half_inverse F).1
  have key : z.re + z.re = 1 ↔ z.re = ofNat (2 * κ + 1) := by
    constructor
    · intro h
      apply F.mul_left_cancel F.two_ne_zero
      rw [two_mul', h, hinv]
    · intro h
      rw [h, ← two_mul', hinv]
  refine ⟨key, ?_, fun b => ?_⟩
  · constructor
    · intro h
      have h1 : 1 + -z.re = z.re := re_congr h
      apply key.1
      show z.re + z.re = 1
      calc z.re + z.re = (1 + -z.re) + z.re := by rw [h1]
        _ = 1 := by rw [add_assoc, neg_add, add_zero]
    · intro h
      apply Ext.ext
      · show 1 + -z.re = z.re
        have h1 := key.2 h
        calc 1 + -z.re = (z.re + z.re) + -z.re := by rw [h1]
          _ = z.re := by rw [add_assoc, add_neg, add_zero]
      · exact neg_neg z.im
  · show ofNat (2 * κ + 1) + ofNat (2 * κ + 1) = 1
    rw [← two_mul', hinv]

/-- 20:B9 — the fixed locus of the half-turn `ρ` is the single point `2⁻¹`, the meeting of the prime meridian
and the critical line: `ρ z = z ⟺ (φ z = z ∧ σ z = z) ⟺ z = 2⁻¹ + 0η`. -/
theorem fixed_half_turn (F : Frame p κ g) (z : Ext p ν) :
    (rho z = z ↔ (conj z = z ∧ sigma z = z)) ∧ (rho z = z ↔ z = ⟨ofNat (2 * κ + 1), 0⟩) := by
  have hc := fixed_conj F z
  have hs := (critical_line F z).2.1
  have hr : rho z = z ↔ (z.im = 0 ∧ z.re = ofNat (2 * κ + 1)) := by
    constructor
    · intro h
      have h1 := re_congr h
      have h2 := im_congr h
      refine ⟨F.eq_zero_of_eq_neg h2.symm, hs.1 ?_⟩
      exact Ext.ext (show (sigma z).re = z.re from h1) (show (sigma z).im = z.im from neg_neg z.im)
    · intro h
      apply Ext.ext
      · have := hs.2 h.2
        exact (re_congr this : (sigma z).re = z.re)
      · show -z.im = z.im
        rw [h.1, neg_zero]
  exact ⟨⟨fun h => ⟨hc.2 (hr.1 h).1, hs.2 (hr.1 h).2⟩, fun h => hr.2 ⟨hc.1 h.1, hs.1 h.2⟩⟩,
    hr.trans ⟨fun h => Ext.ext h.2 h.1, fun h => ⟨im_congr h, re_congr h⟩⟩⟩

/-- 20:B8 — the energy on the critical line: `N(2⁻¹ + bη) = (2⁻¹)² − νb²`, with `2 · 2⁻¹ = 1`. -/
theorem norm_on_line (F : Frame p κ g) (z : Ext p ν) (hz : z.re = ofNat (2 * κ + 1)) :
    norm z = ofNat (2 * κ + 1) * ofNat (2 * κ + 1) + -(ν * (z.im * z.im)) ∧
    (2 : Shell p) * ofNat (2 * κ + 1) = 1 := by
  refine ⟨?_, (half_inverse F).1⟩
  show z.re * z.re + -(ν * (z.im * z.im)) = _
  rw [hz]

/-- 20:B6 — the quarter-turn `i = −g^κ`, as the element `i + 0η`, is fixed by conjugation and lies off the
circle: `N(i) = i² = −1 ≠ 1`. -/
theorem quarter_turn_off_circle (F : Frame p κ g) (ν : Shell p) :
    conj (⟨quarterTurn g κ, 0⟩ : Ext p ν) = ⟨quarterTurn g κ, 0⟩ ∧ norm (⟨quarterTurn g κ, 0⟩ : Ext p ν) = -1 ∧
    norm (⟨quarterTurn g κ, 0⟩ : Ext p ν) ≠ 1 := by
  have hn : norm (⟨quarterTurn g κ, 0⟩ : Ext p ν) = -1 := by
    show quarterTurn g κ * quarterTurn g κ + -(ν * (0 * 0)) = -1
    rw [F.quarter_turn_sq, zero_mul, mul_zero, neg_zero, add_zero]
  refine ⟨Ext.ext rfl neg_zero, hn, fun h => ?_⟩
  rw [hn] at h
  exact F.one_ne_zero (F.eq_zero_of_eq_neg h.symm)

/-- 20:B6 [value] — on `𝔽₁₃(√2)` (`2` a nonsquare mod `13`): the norm-one circle has `13 + 1 = 14` points
among the `169` elements, and Frobenius `z ↦ z^{13}` is conjugation on every element. -/
theorem circle13 :
    natCount (fun k => norm (⟨ofNat (k / 13), ofNat (k % 13)⟩ : Ext 13 2) = 1) 169 = 14 ∧
    (∀ k, k < 169 → (⟨ofNat (k / 13), ofNat (k % 13)⟩ : Ext 13 2) ^ 13 =
      conj ⟨ofNat (k / 13), ofNat (k % 13)⟩) ∧
    (∀ x : Nat, x < 13 → 0 < x → (ofNat x : Shell 13) * ofNat x ≠ 2) := by decide +kernel

end extension

/-! ## Frame coincidence below the horizon (20:B2) -/

section coincidence

theorem le_mul_self : ∀ H : Nat, H ≤ H * H
  | 0 => Nat.le_refl 0
  | H + 1 => by
    show H + 1 ≤ (H + 1) * H + (H + 1)
    exact Nat.le_add_left (H + 1) ((H + 1) * H)

/-- 20:B2 — below the horizon the reading is frame-exact: on any shell with `H² < p`, a residue `m ≤ H` is
the integer `m`, and the product of two window residues reads back as the integer product. -/
theorem window_readback {H : Nat} (hH : H * H < p) :
    (∀ m, m ≤ H → (ofNat m : Shell p).val = m) ∧
    ∀ a b, a ≤ H → b ≤ H → (ofNat a * ofNat b : Shell p).val = a * b := by
  have hlt : ∀ m, m ≤ H → m < p := fun m hm =>
    Nat.lt_of_le_of_lt (Nat.le_trans hm (le_mul_self H)) hH
  refine ⟨fun m hm => by rw [val_ofNat, FRC.Nat.mod_eq_of_lt (hlt m hm)], fun a b ha hb => ?_⟩
  rw [ofNat_mul, val_ofNat, FRC.Nat.mod_eq_of_lt (Nat.lt_of_le_of_lt (Nat.mul_le_mul ha hb) hH)]

/-- 20:B2 — primality equals irreducibility in the window: for `m ≤ H` on a shell with `H² < p`, `m` factors
as `a · b` with `2 ≤ a, b ≤ H` read on the shell exactly when it factors so as an integer. The statement is the
same on every shell above the window — the Subject `𝔽_p` and the Carrier `𝔽_Ω` read the same primes. -/
theorem factorisation_iff {H : Nat} (hH : H * H < p) (m : Nat) (hm : m ≤ H) :
    (∃ a b, 2 ≤ a ∧ 2 ≤ b ∧ a ≤ H ∧ b ≤ H ∧ (ofNat a * ofNat b : Shell p) = ofNat m) ↔
    ∃ a b, 2 ≤ a ∧ 2 ≤ b ∧ a * b = m := by
  have hrb := window_readback (p := p) hH
  constructor
  · intro h
    match h with
    | ⟨a, b, ha, hb, haH, hbH, e⟩ =>
      refine ⟨a, b, ha, hb, ?_⟩
      have := val_injective e
      rw [hrb.2 a b haH hbH, hrb.1 m hm] at this
      exact this
  · intro h
    match h with
    | ⟨a, b, ha, hb, e⟩ =>
      have hm' : a * b ≤ H := by rw [e]; exact hm
      have haab : a ≤ a * b := by
        have := Nat.mul_le_mul_left a (Nat.le_trans (Nat.le_succ 1) hb)
        rw [Nat.mul_one] at this; exact this
      have hbab : b ≤ a * b := by
        have := Nat.mul_le_mul_right b (Nat.le_trans (Nat.le_succ 1) ha)
        rw [Nat.one_mul] at this; exact this
      exact ⟨a, b, ha, hb, Nat.le_trans haab hm', Nat.le_trans hbab hm', by rw [ofNat_mul, e]⟩

/-- 20:B2 — frame coincidence: on the Subject `𝔽_p` and the Carrier `𝔽_Ω`, both above the window `H² < p`,
`H² < Ω`, a window residue factors on one shell exactly when it factors on the other. -/
theorem frame_coincidence {Ω : Nat} [Pos Ω] {H : Nat} (hp : H * H < p) (hΩ : H * H < Ω) (m : Nat) (hm : m ≤ H) :
    (∃ a b, 2 ≤ a ∧ 2 ≤ b ∧ a ≤ H ∧ b ≤ H ∧ (ofNat a * ofNat b : Shell p) = ofNat m) ↔
    (∃ a b, 2 ≤ a ∧ 2 ≤ b ∧ a ≤ H ∧ b ≤ H ∧ (ofNat a * ofNat b : Shell Ω) = ofNat m) :=
  (factorisation_iff hp m hm).trans (factorisation_iff hΩ m hm).symm

end coincidence

/-! ## The laboratory pair (20:B1) -/

/-- 20:B1 [value] — the pair `(13, 233)`: nested, `13² < 233`; both cycles carry the quarter-turn core
(`4 ∣ 12`, `4 ∣ 232`; `5² = −1` on `𝔽₁₃`, `89² = −1` on `𝔽₂₃₃`) and share nothing else (`3 ∤ 232`, so
`gcd(12, 232) = 4`); the Carrier's cycle does not project onto the Subject's (`12 ∤ 232`); the horizon window
`H = 3` is wrap-free on both (`9 < 13`, `9 < 233`). -/
theorem lab_pair :
    13 * 13 < 233 ∧ 12 % 4 = 0 ∧ 232 % 4 = 0 ∧ 232 % 3 ≠ 0 ∧ (5 : Shell 13) * 5 = -1 ∧
    (89 : Shell 233) * 89 = -1 ∧ 232 % 12 ≠ 0 ∧ 3 * 3 < 13 ∧ 3 * 3 < 233 := by decide

end FRC.Horizon
