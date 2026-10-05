import FrcCore.Sum
import FrcCore.Instances
import FrcCore.Poly
import FrcCore.Theme.Extension

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
Every old name stays as an alias.
-/

namespace FRC.Rh

open FRC.Shell FRC.Shell.Frame

variable {p : Nat} [Pos p]

/-- A residue `l + 1 < p` is nonzero. -/
theorem ofNat_succ_ne_zero {l : Nat} (hl : l + 1 < p) : (ofNat (l + 1) : Shell p) ≠ 0 := fun h => by
  have := val_injective h
  rw [val_ofNat, val_zero, FRC.Nat.mod_eq_of_lt hl] at this
  exact Nat.noConfusion this

section frame
variable {κ : Nat} {g : Shell p}

/-! ## The zero-slot and slot complementarity (20:B4, 20:B5) -/

/-- 20:B4 — the zero-slot on every shell: over the nonzero residues `x = l + 1`, `l < p − 1`,
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

/-! ## The half-turn arithmetic and the Subject constants (20:B8, 20:B10) -/

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

/-! ## The scale-shift in the `𝔽_p` reading (20:E1, 20:E12 (iii)) -/

/-- 20:E1, 20:E12 — the power characters are eigenvectors of the scale-shift `x ↦ g^r x` in the `𝔽_p` reading:
`(g^r x)^k = (g^r)^k · x^k`. -/
theorem shift_power_character (r k : Nat) (x : Shell p) : (g ^ r * x) ^ k = (g ^ r) ^ k * x ^ k :=
  mul_pow _ _ _

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

end frame

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

/-- 00:C1 on `𝔽₅₃`: the frame `(τ; 0, 1, 2)` of capacity `13`, and `ω = 2^4 = 16` of order `13`. -/
theorem frame53 : Frame 53 13 (2 : Shell 53) ∧ IsPrimitive (16 : Shell 53) 13 ∧ (2 : Shell 53) ^ 4 = 16 :=
  ⟨⟨rfl, Nat.zero_lt_succ 12, by decide⟩, by decide, by decide⟩

/-- 20:B7 [value] — on `𝔽₅₃` with `ω = 16` of order `13`: `c_{13}(n) = Σ_{a=1}^{12} ω^{an} = −1` for every
`0 < n < 13`, and `12 = m − 1` at `n = 0`. -/
theorem ramanujan53 :
    (∀ n, n < 13 → 0 < n → sumRange (fun a => (16 : Shell 53) ^ (n * (a + 1))) 12 = -1) ∧
    sumRange (fun a => (16 : Shell 53) ^ (0 * (a + 1))) 12 = 12 := by decide

end ramanujan

/-! ## The quadratic extension `F(η)`, `η² = ν`, as pairs of residues (20:B6, 20:B8, 20:B9) -/

namespace Ext

open FRC.Extension (Ext)
open FRC.Extension.Ext
variable {ν : Shell p}

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

section frame
variable {κ : Nat} {g : Shell p}

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

/-- 20:E12, 20:B8 — the spectral readout in the core: the mode index `θ` is read at `z(θ) = 2⁻¹ + θη`,
`2⁻¹ = 2κ + 1`. -/
def readout (ν : Shell p) (κ : Nat) (θ : Shell p) : Ext p ν := ⟨ofNat (2 * κ + 1), θ⟩

/-- 20:E12, 20:B8 — clause (ii) of the shell theorem, no axioms: every readout lies on the trace-one line, its
real part is the half-turn `2⁻¹ = 2κ + 1`, and `θ ↦ z(θ)` is injective. -/
theorem readout_on_line (F : Frame p κ g) (ν θ : Shell p) :
    trace (readout ν κ θ) = 1 ∧ (readout ν κ θ).re = ofNat (2 * κ + 1) ∧
    ∀ θ' : Shell p, readout ν κ θ = readout ν κ θ' → θ = θ' := by
  refine ⟨(critical_line F (readout ν κ θ)).2.2 θ, rfl, fun θ' h => im_congr h⟩

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

end frame

/-- 20:B6 [value] — on `𝔽₁₃(√2)` (`2` a nonsquare mod `13`): the norm-one circle has `13 + 1 = 14` points
among the `169` elements, and Frobenius `z ↦ z^{13}` is conjugation on every element. -/
theorem circle13 :
    natCount (fun k => norm (⟨ofNat (k / 13), ofNat (k % 13)⟩ : Ext 13 2) = 1) 169 = 14 ∧
    (∀ k, k < 169 → (⟨ofNat (k / 13), ofNat (k % 13)⟩ : Ext 13 2) ^ 13 =
      conj ⟨ofNat (k / 13), ofNat (k % 13)⟩) ∧
    (∀ x : Nat, x < 13 → 0 < x → (ofNat x : Shell 13) * ofNat x ≠ 2) := by decide +kernel

end Ext

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

/-- 20-rh's product, the instance `z * w` of `FRC.Extension.Ext p ν`. -/
@[reducible] def mul (z w : Ext p ν) : Ext p ν := z * w

/-- 20-rh's unit, `1`. -/
@[reducible] def one : Ext p ν := 1

end Ext

/-- Bounded universal quantifiers, decided by search (no axioms). -/
@[reducible] def decForallLT (P : Nat → Prop) [DecidablePred P] : (n : Nat) → Decidable (∀ m, m < n → P m) :=
  FRC.Shell.decForallLT P

@[reducible] def instDecForallLT (P : Nat → Prop) [DecidablePred P] (n : Nat) : Decidable (∀ m, m < n → P m) :=
  FRC.Shell.instDecForallLT P n

end aliases

-- Ledger predicates of 20-rh (generated by make_predicates.py from docs/20-rh/20-rh-ledger.json; edit the ledger, not this section)
/-- 20:B1 (p20008) — The two frames on one substrate: the Carrier chart $\F_\Omega$, held by no embedded observer, and the Subject $\Fp$ embedded with $\Omega\gg p^{2}$; what they share is the quarter-turn core $Q_4$ and nothing else, on the laboratory pair $(13,233)$ the cycles $C_{12}$ and $C_{232}$ admit no projection ($12\nmid232$); hardness by register ($p$-hard, $\Omega$-hard). -/
theorem p20008 : (13 : Nat) * (13 : Nat) < (233 : Nat) ∧ (12 : Nat) % (4 : Nat) = (0 : Nat) ∧ (232 : Nat) % (4 : Nat) = (0 : Nat) ∧ (232 : Nat) % (3 : Nat) ≠ (0 : Nat) ∧ (5 : FRC.Shell (13 : Nat)) * (5 : FRC.Shell (13 : Nat)) = (-1 : FRC.Shell (13 : Nat)) ∧ (89 : FRC.Shell (233 : Nat)) * (89 : FRC.Shell (233 : Nat)) = (-1 : FRC.Shell (233 : Nat)) ∧ (232 : Nat) % (12 : Nat) ≠ (0 : Nat) ∧ (3 : Nat) * (3 : Nat) < (13 : Nat) ∧ (3 : Nat) * (3 : Nat) < (233 : Nat) :=
  @FRC.Rh.lab_pair
set_option linter.defProp false in
/-- 20:B2 (p20009) — Frame coincidence below the horizon: for $n\le\sqrt p$ the residue $n$ is the same integer in $\Fp$ and $\F_\Omega$, and primality of $n$ equals irreducibility in the Subject chart; the Subject-realised primes $\Pi_p$ are the primes to $\sqrt p$. -/
def p20009 := And.intro @FRC.Rh.window_readback (And.intro @FRC.Rh.factorisation_iff (@FRC.Rh.frame_coincidence))
/-- 20:B4 (p20011) — Zero-slot: $Z_\Omega(k)=\sum_{x\in\Fx{\Omega}}x^{k}$ vanishes on every nonterminal exponent $1\le k\le\Omega-2$ and equals $-1$ on the full cycle; the nonterminal slots are the universal mode basis. -/
theorem p20011 : ∀ {p : Nat} [FRC.Pos p] {κ : Nat} {g : FRC.Shell p}, FRC.Shell.Frame p κ g → (∀ (k : Nat), (0 : Nat) < k → k < p - (1 : Nat) → FRC.Shell.sumRange (fun l => FRC.Shell.ofNat (l + (1 : Nat)) ^ k) (p - (1 : Nat)) = (0 : FRC.Shell p)) ∧ FRC.Shell.sumRange (fun l => FRC.Shell.ofNat (l + (1 : Nat)) ^ (p - (1 : Nat))) (p - (1 : Nat)) = (-1 : FRC.Shell p) :=
  @FRC.Rh.zero_slot
/-- 20:B5 (p20012) — Slot complementarity: $\Phi(k)=-\gen^{\,k}$ bijects the nontrivial spectral slots onto the nonterminal additive slots $\Fx{\Omega}\setminus\{-1\}$, the two removed points being $\mu_2$, the intertwiner the half-cycle element. -/
theorem p20012 : ∀ {p : Nat} [FRC.Pos p] {κ : Nat} {g : FRC.Shell p}, FRC.Shell.Frame p κ g → (∀ (i j : Nat), i < p - (1 : Nat) → j < p - (1 : Nat) → -g ^ i = -g ^ j → i = j) ∧ (∀ (k : Nat), (0 : Nat) < k → k < p - (1 : Nat) → -g ^ k ≠ (0 : FRC.Shell p) ∧ -g ^ k ≠ (-1 : FRC.Shell p)) ∧ ∀ (y : FRC.Shell p), y ≠ (0 : FRC.Shell p) → y ≠ (-1 : FRC.Shell p) → ∃ k, (0 : Nat) < k ∧ k < p - (1 : Nat) ∧ -g ^ k = y :=
  @FRC.Rh.slot_complementarity
set_option linter.defProp false in
/-- 20:B6 (p20013) — Hermitian phase calculus on $K=\F_{p^{2}}$: norm and trace $\F_p$-valued, the phase circle $U_{p+1}$ of order $p+1$ with Frobenius as inversion, the quarter-turn $\It$ Frobenius-fixed and off the circle ($\Nm(\It)=-1$), the trace-zero $\eta$ with $\eta^{2}=\nu$ a nonsquare, $\Tr(a+b\eta)=2a$, $\Nm=a^{2}-\nu b^{2}$. -/
def p20013 := And.intro @FRC.Rh.Ext.mul_conj (And.intro @FRC.Rh.Ext.conj_inv_of_norm_one (And.intro @FRC.Rh.Ext.quarter_turn_off_circle (@FRC.Rh.Ext.circle13)))
/-- 20:B7 (p20014) — Flat ground state: the full-modulus Ramanujan sum $c_p(n)\equiv-1$ for every $n\not\equiv0$; the mode at the spectral origin carries no prime information. -/
theorem p20014 : (∀ {q : Nat} [FRC.Pos q] {κ' : Nat} {h : FRC.Shell q}, FRC.Shell.Frame q κ' h → ∀ {m : Nat}, (0 : Nat) < m → ∀ {ω : FRC.Shell q}, ω.IsPrimitive m → ∀ (n : Nat), n % m ≠ (0 : Nat) → FRC.Shell.sumRange (fun a => ω ^ (n * (a + (1 : Nat)))) (m - (1 : Nat)) = (-1 : FRC.Shell q)) ∧ (∀ (n : Nat), n < (13 : Nat) → (0 : Nat) < n → FRC.Shell.sumRange (fun a => (16 : FRC.Shell (53 : Nat)) ^ (n * (a + (1 : Nat)))) (12 : Nat) = (-1 : FRC.Shell (53 : Nat))) ∧ FRC.Shell.sumRange (fun a => (16 : FRC.Shell (53 : Nat)) ^ ((0 : Nat) * (a + (1 : Nat)))) (12 : Nat) = (12 : FRC.Shell (53 : Nat)) :=
  And.intro @FRC.Rh.ramanujan_sum (@FRC.Rh.ramanujan53)
set_option linter.defProp false in
/-- 20:B8 (p20015) — The finite critical line: the half-turn $2^{-1}=2\kp+1=-\pi$; $\Tr(z)=1$ exactly on the $p$ points $z=2^{-1}+\eta\theta$, with energy $\Nm(z)=\tfrac14-\nu\theta^{2}$; de-framed, $2^{-1}/p=(2\kp+1)/p\to\half$ from above [chart]. -/
def p20015 := And.intro @FRC.Rh.half_inverse (And.intro @FRC.Rh.Ext.critical_line (@FRC.Rh.Ext.norm_on_line))
set_option linter.defProp false in
/-- 20:B9 (p20016) — The two agreement loci: the Klein four-group $\langle\phi,\rho\rangle$ of Frobenius and the functional-equation half-turn fixes exactly $\F_p$ (the prime meridian), $L_{1/2}$ (the critical line) and their meeting $\{2^{-1}\}$; no other line is fixed. -/
def p20016 := And.intro @FRC.Rh.Ext.klein_four (And.intro @FRC.Rh.Ext.fixed_conj (And.intro @FRC.Rh.Ext.critical_line (@FRC.Rh.Ext.fixed_half_turn)))
/-- 20:B10 (p20017) — The Subject constants on the shell: $\pi=2\kp$, $2\pi\equiv-1$, $\It=\gen^{-\kp}$, $\It^{2}\equiv-1$, $\Et=\gen^{\,\It}$ on the odd lift, $\gen^{\,\pi}\equiv-1$, $\Et^{\,\It\pi}\equiv-1$; on $\F_{13}$: $\gen=2$, $\It=5$, $\Et=6$, $\pi=6$. -/
theorem p20017 : (∀ {p : Nat} [FRC.Pos p] {κ : Nat} {g : FRC.Shell p}, FRC.Shell.Frame p κ g → FRC.Shell.ofNat ((2 : Nat) * FRC.Shell.Frame.halfPeriod κ) = (-1 : FRC.Shell p) ∧ g ^ ((3 : Nat) * κ) = FRC.Shell.Frame.quarterTurn g κ ∧ FRC.Shell.Frame.quarterTurn g κ * FRC.Shell.Frame.quarterTurn g κ = (-1 : FRC.Shell p) ∧ g ^ ((2 : Nat) * κ) = (-1 : FRC.Shell p) ∧ ∀ (m : Nat), m % (2 : Nat) = (1 : Nat) → (g ^ m) ^ (m * ((2 : Nat) * κ)) = (-1 : FRC.Shell p)) ∧ ((2 : FRC.Shell (13 : Nat)) * (6 : FRC.Shell (13 : Nat)) = (-1 : FRC.Shell (13 : Nat)) ∧ (2 : FRC.Shell (13 : Nat)) ^ (9 : Nat) = (5 : FRC.Shell (13 : Nat)) ∧ FRC.Shell.Frame.quarterTurn (2 : FRC.Shell (13 : Nat)) (3 : Nat) = (5 : FRC.Shell (13 : Nat)) ∧ (5 : FRC.Shell (13 : Nat)) * (5 : FRC.Shell (13 : Nat)) = (-1 : FRC.Shell (13 : Nat)) ∧ (2 : FRC.Shell (13 : Nat)) ^ (5 : Nat) = (6 : FRC.Shell (13 : Nat)) ∧ (2 : FRC.Shell (13 : Nat)) ^ (6 : Nat) = (-1 : FRC.Shell (13 : Nat)) ∧ (6 : FRC.Shell (13 : Nat)) ^ ((5 : Nat) * (6 : Nat)) = (-1 : FRC.Shell (13 : Nat))) ∧ FRC.Shell.Frame (13 : Nat) (3 : Nat) (2 : FRC.Shell (13 : Nat)) :=
  And.intro @FRC.Rh.subject_constants (And.intro @FRC.Rh.constants13 (@FRC.Shell.frame13))
/-- 20:E1 (p20032) — The scale-evolution generator: on the shell the scale-shift $x\mapsto\gen^{\,r}x$ is a unitary permutation of $\Fx{p}$ with the complex characters as eigenvectors; in the analytic chart [chart] the dilation group $U_r=e^{ir\Hh}$ has the self-adjoint generator $\Hh=-i(x\partial_x+\half)$ with generalised eigenfunctions $x^{-\bar\rho}$, $\rho=\half+i\gamma$, the symmetrizing $\half$ the half-turn of B8; the chart assignment is used nowhere as a shell identity. -/
theorem p20032 : (∀ {p : Nat} [FRC.Pos p] {g : FRC.Shell p} (r k : Nat) (x : FRC.Shell p), (g ^ r * x) ^ k = (g ^ r) ^ k * x ^ k) ∧ ∀ {p : Nat} [FRC.Pos p] {κ : Nat} {g : FRC.Shell p}, FRC.Shell.Frame p κ g → ∀ (r : Nat), FRC.Shell.Frame.natCount (fun x => x ≠ (0 : Nat) ∧ g ^ r * FRC.Shell.ofNat x = FRC.Shell.ofNat x) p = if r % (p - (1 : Nat)) = (0 : Nat) then p - (1 : Nat) else (0 : Nat) :=
  And.intro @FRC.Rh.shift_power_character (@FRC.Rh.shift_trace)
/-- 20:E12 (p20043) — \textbf{The shell theorem.} On every shell, with no hypothesis: (i) $v$ expands in the constant mode and the nonterminal modes of the quarter-turn meridian; (ii) every readout lies on $\Tr=1$, real part $2^{-1}=2\kp+1=-\pi$; (iii) the scale-shift has the modes as eigenvectors, eigenphases $2\pi j/(p-1)$ independent of $v$. No off-line mode; true of every vector, the Davenport--Heilbronn vector included. -/
theorem p20043 : (∀ {p : Nat} [FRC.Pos p] {g : FRC.Shell p} (r k : Nat) (x : FRC.Shell p), (g ^ r * x) ^ k = (g ^ r) ^ k * x ^ k) ∧ (∀ {p : Nat} [FRC.Pos p] {κ : Nat} {g : FRC.Shell p}, FRC.Shell.Frame p κ g → ∀ (r : Nat), FRC.Shell.Frame.natCount (fun x => x ≠ (0 : Nat) ∧ g ^ r * FRC.Shell.ofNat x = FRC.Shell.ofNat x) p = if r % (p - (1 : Nat)) = (0 : Nat) then p - (1 : Nat) else (0 : Nat)) ∧ (∀ {p : Nat} [FRC.Pos p] {κ : Nat} {g : FRC.Shell p}, FRC.Shell.Frame p κ g → ∀ (ν θ : FRC.Shell p), (FRC.Rh.Ext.readout ν κ θ).trace = (1 : FRC.Shell p) ∧ (FRC.Rh.Ext.readout ν κ θ).re = FRC.Shell.ofNat ((2 : Nat) * κ + (1 : Nat)) ∧ ∀ (θ' : FRC.Shell p), FRC.Rh.Ext.readout ν κ θ = FRC.Rh.Ext.readout ν κ θ' → θ = θ') ∧ ∀ {p : Nat} [FRC.Pos p] {κ : Nat} {g : FRC.Shell p}, FRC.Shell.Frame p κ g → ∀ (k : Nat), (1 : Nat) ≤ k → k ≤ p - (2 : Nat) → -g ^ k ≠ (0 : FRC.Shell p) ∧ -g ^ k ≠ (-1 : FRC.Shell p) :=
  And.intro @FRC.Rh.shift_power_character (And.intro @FRC.Rh.shift_trace (And.intro @FRC.Rh.Ext.readout_on_line (@FRC.Rh.Ext.readout_slot_index)))
-- end ledger predicates

end FRC.Rh
