import FrcCore.Theme.Horizon

/-!
# FrcCore.Theme.Zeros — the horizon theme's second file: the zeros of the shell (20-rh's rewrite, 17 October 2026)

The critical line as the frequency domain (20:B12): the readout of the mode `k` at `θ = −g^k`, the drive about the
centre as the step `k ↦ k + 1`, the half-turn and the conjugation as the step `k ↦ k + π` across the line, the energy a
function of `k` alone, even under the half-turn. The dual of a vector with the energy identity (20:E13, the finite
Parseval identity, self-pairing `−1`); the parity `W² = −J` and the explicit formula, on the cycle and along the
meridian with the inversion on the residues (20:E14). The two agreement loci in the invariant-line form (20:B9): among
the `p(p + 1)` affine lines of the extension, `H_b = {Im z = b}` and `S_{c,a} = {Re z = a + c·Im z}`, conjugation keeps
`H_b` exactly when `b = 0` and `S_{c,a}` exactly when `c = 0`, the half-turn keeps `H_b` exactly when `b = 0` and
`S_{c,a}` exactly when `a = 2⁻¹`, so exactly two lines are kept by both, the meridian `H_0` and the critical line
`S_{0,2⁻¹}`. Frame coincidence on the critical line for every label of the Subject (20:B13): on two shells `p ≤ Ω` every
label `1 ≤ θ ≤ p − 2` reads back as the integer `θ` in both frames and is the readout of a nontrivial mode on the critical
line of each. These, with `readout_on_line` and `off_line_unregistered` (a point off both lines lies on no line kept by
both involutions), are the witnesses of the paper's Theorem noline (20:F10). The declarations keep
the theme's namespace `FRC.Horizon`; the file is the theme's second core file, as `Theme/Ladder.lean` is its third,
within the file budget of gate G10. No axioms.
-/

namespace FRC.Horizon

open FRC.Shell FRC.Shell.Frame
open FRC.Extension (Ext)

variable {p : Nat} [Pos p] {κ : Nat} {g : Shell p}

section rewrite20261017

/-- 20:E12 (i) — the dual of a vector on the cycle: `v̂(k) = Σ_{l<n} v_l (g^l)^k`, the shell Fourier transform `W` on the
phase cycle (6:B5); the mode coefficient of `mode_expansion` is `c_k = −v̂(−k)`. -/
def dual (g : Shell p) (v : Nat → Shell p) (k : Nat) : Shell p :=
  sumRange (fun l => v l * (g ^ l) ^ k) (p - 1)

/-- A product of two sums as a double sum: `(Σ_l a_l) (Σ_m b_m) = Σ_l Σ_m a_l b_m`. -/
theorem sum_mul_sum (a b : Nat → Shell p) (n m : Nat) :
    sumRange a n * sumRange b m = sumRange (fun l => sumRange (fun j => a l * b j) m) n := by
  rw [← sum_mul_right]
  apply sum_congr; intro l _
  exact (sum_mul_left b (a l) m).symm

/-- 20:E12 (ii), 20:E13 — the energy identity on the cycle: `Σ_{k<n} v̂(k) c_k = Σ_{l<n} v_l²` with `c_k = −v̂(−k)` the mode
coefficient, that is `Σ_k v̂(k) v̂(−k) = −Σ_l v_l²`: the finite Parseval identity of the cycle, the self-pairing `−1` of
the power characters in place of the complex norm. -/
theorem parseval_cycle (F : Frame p κ g) (v : Nat → Shell p) :
    sumRange (fun k => dual g v k * modeCoeff g v k) (p - 1) = sumRange (fun l => v l * v l) (p - 1) := by
  have h1 : ∀ k, k < p - 1 → dual g v k * modeCoeff g v k
      = sumRange (fun l => sumRange (fun m => v l * v m * (g ^ (k * l) * -(g ^ ((p - 1 - m) * k)))) (p - 1)) (p - 1) := by
    intro k _
    unfold dual modeCoeff
    rw [sum_mul_sum]
    apply sum_congr; intro l _
    apply sum_congr; intro m _
    rw [← pow_mul, Nat.mul_comm l k]
    calc v l * g ^ (k * l) * (v m * -(g ^ ((p - 1 - m) * k)))
        = v l * (g ^ (k * l) * (v m * -(g ^ ((p - 1 - m) * k)))) := mul_assoc _ _ _
      _ = v l * (g ^ (k * l) * v m * -(g ^ ((p - 1 - m) * k))) := by rw [mul_assoc (g ^ (k * l))]
      _ = v l * (v m * g ^ (k * l) * -(g ^ ((p - 1 - m) * k))) := by rw [mul_comm (g ^ (k * l)) (v m)]
      _ = v l * (v m * (g ^ (k * l) * -(g ^ ((p - 1 - m) * k)))) := by rw [mul_assoc (v m)]
      _ = v l * v m * (g ^ (k * l) * -(g ^ ((p - 1 - m) * k))) := (mul_assoc _ _ _).symm
  rw [sum_congr (p - 1) h1,
    sum_comm (fun k l => sumRange (fun m => v l * v m * (g ^ (k * l) * -(g ^ ((p - 1 - m) * k)))) (p - 1)) (p - 1) (p - 1)]
  apply sum_congr; intro l hl
  rw [sum_comm (fun k m => v l * v m * (g ^ (k * l) * -(g ^ ((p - 1 - m) * k)))) (p - 1) (p - 1)]
  have h3 : ∀ m, m < p - 1 → sumRange (fun k => v l * v m * (g ^ (k * l) * -(g ^ ((p - 1 - m) * k)))) (p - 1)
      = v l * v m * (if l = m then 1 else 0) := fun m hm => by
    rw [sum_mul_left, F.dft_inverse hl hm]
  rw [sum_congr (p - 1) h3, sum_eq_single hl (fun m _ hne => by rw [ite_eq_right (fun e => hne e.symm), mul_zero]),
    ite_eq_left rfl, mul_one]

/-- 20:E14, 20:E12 (v) — the explicit formula on the cycle: the count of `v` over the first `x` points of the cycle is the mode
sum, `Σ_{j<x} v_j = Σ_{k<n} c_k S_k(x)` with `S_k(x) = Σ_{j<x} (g^j)^k` the cumulative read of the mode `k`, and the
constant mode's read is the main term, `S_0(x) = x`. -/
theorem explicit_formula_cycle (F : Frame p κ g) (v : Nat → Shell p) {x : Nat} (hx : x ≤ p - 1) :
    sumRange v x = sumRange (fun k => modeCoeff g v k * sumRange (fun j => (g ^ j) ^ k) x) (p - 1) ∧
    sumRange (fun j => (g ^ j) ^ 0) x = ofNat x := by
  refine ⟨?_, ?_⟩
  · have h1 : sumRange v x = sumRange (fun j => sumRange (fun k => modeCoeff g v k * (g ^ j) ^ k) (p - 1)) x :=
      sum_congr x (fun j hj => mode_expansion F v (Nat.lt_of_lt_of_le hj hx))
    rw [h1, sum_comm (fun j k => modeCoeff g v k * (g ^ j) ^ k) (p - 1) x]
    apply sum_congr; intro k _
    exact sum_mul_left (fun j => (g ^ j) ^ k) (modeCoeff g v k) x
  · have e : ∀ j, j < x → (g ^ j) ^ 0 = (1 : Shell p) := fun j _ => rfl
    rw [sum_congr x e, sum_const, mul_one]

/-- 20:E14, 20:E12 (iv) — the transform's square is the parity: `(W²)_{jl} = Σ_k g^{jk} g^{kl}` is `−1` when `j + l ≡ 0`
and `0` otherwise, `W² = −J`; with `F = iW` and `i² = −1`, `F² = J` and `F⁴ = 1` (6:B5). -/
theorem transform_square (F : Frame p κ g) (j l : Nat) :
    sumRange (fun k => g ^ (j * k) * g ^ (k * l)) (p - 1) = if (j + l) % (p - 1) = 0 then -1 else 0 := by
  have hterm : ∀ k, k < p - 1 → g ^ (j * k) * g ^ (k * l) = (g ^ ((j + l) % (p - 1))) ^ k := fun k _ => by
    rw [← pow_add, Nat.mul_comm k l, ← Nat.add_mul, pow_mul, F.pow_mod (j + l)]
  rw [sum_congr (p - 1) hterm]
  exact match Nat.decEq ((j + l) % (p - 1)) 0 with
    | .isTrue e => by
        rw [ite_eq_left e, e, pow_zero]
        have e1 : ∀ k, k < p - 1 → (1 : Shell p) ^ k = 1 := fun k _ => one_pow k
        rw [sum_congr (p - 1) e1, sum_const, mul_one, F.ofNat_n]
    | .isFalse ne => by
        rw [ite_eq_right ne]
        exact (F.principal_root _ (Nat.pos_of_ne_zero ne) (Nat.mod_lt _ F.n_pos)).2.1

/-- 20:B12 (ii) — the drive about the centre: on the critical line the dilation `z ↦ 2⁻¹ + g (z − 2⁻¹)` carries the
readout of the mode `k` to the readout of the mode `k + 1`. -/
theorem drive_on_line (ν : Shell p) (κ k : Nat) :
    (⟨(readout ν κ (-(g ^ k))).re, g * (readout ν κ (-(g ^ k))).im⟩ : Ext p ν) = readout ν κ (-(g ^ (k + 1))) := by
  refine Ext.ext ?_ ?_
  · rfl
  · show g * -(g ^ k) = -(g ^ (k + 1))
    rw [← mul_neg, mul_comm, ← pow_succ]

/-- 20:B12 (iii) — the half-turn `ρ : z ↦ 1 − z` and the conjugation agree on the critical line and carry the readout
of the mode `k` to the readout of the mode `k + π`, `π = 2κ`: the half-turn of the frequency cycle. -/
theorem reflection_on_line (F : Frame p κ g) (ν : Shell p) (k : Nat) :
    rho (readout ν κ (-(g ^ k))) = readout ν κ (-(g ^ (k + 2 * κ))) ∧
    Ext.conj (readout ν κ (-(g ^ k))) = readout ν κ (-(g ^ (k + 2 * κ))) := by
  have hpow : g ^ (k + 2 * κ) = -(g ^ k) := by
    rw [FRC.Shell.pow_add, F.half_period, ← mul_neg, mul_one]
  have hre : (1 : Shell p) + -(ofNat (2 * κ + 1)) = ofNat (2 * κ + 1) := by
    have h2 : (ofNat (2 * κ + 1) : Shell p) + ofNat (2 * κ + 1) = 1 := by
      rw [← two_mul', (half_inverse F).1]
    calc (1 : Shell p) + -(ofNat (2 * κ + 1))
        = (ofNat (2 * κ + 1) + ofNat (2 * κ + 1)) + -(ofNat (2 * κ + 1)) := by rw [h2]
      _ = ofNat (2 * κ + 1) := by rw [add_assoc, add_neg, add_zero]
  refine ⟨Ext.ext hre ?_, Ext.ext rfl ?_⟩
  · show - -(g ^ k) = -(g ^ (k + 2 * κ))
    rw [hpow, neg_neg]
  · show - -(g ^ k) = -(g ^ (k + 2 * κ))
    rw [hpow, neg_neg]

/-- 20:B12 (iv) — the energy on the critical line is a function of the frequency coordinate alone and is even under
the half-turn: `N(z_k) = N(z_{k+π})`. -/
theorem line_energy_even (F : Frame p κ g) (ν : Shell p) (k : Nat) :
    Ext.norm (readout ν κ (-(g ^ k))) = Ext.norm (readout ν κ (-(g ^ (k + 2 * κ)))) := by
  have hpow : g ^ (k + 2 * κ) = -(g ^ k) := by
    rw [FRC.Shell.pow_add, F.half_period, ← mul_neg, mul_one]
  show ofNat (2 * κ + 1) * ofNat (2 * κ + 1) + -(ν * (-(g ^ k) * -(g ^ k))) =
    ofNat (2 * κ + 1) * ofNat (2 * κ + 1) + -(ν * (-(g ^ (k + 2 * κ)) * -(g ^ (k + 2 * κ))))
  rw [hpow, neg_neg, neg_mul_neg]

/-- 20:B9, 20:F10, the invariant-line form — the affine lines of the extension are `H_b = {Im z = b}` (`p` lines) and
`S_{c,a} = {Re z = a + c·Im z}` (`p²` lines). Conjugation keeps `H_b` exactly when `b = 0` (the meridian) and `S_{c,a}`
exactly when `c = 0` (the lines of direction `η`); the half-turn keeps `H_b` exactly when `b = 0` and `S_{c,a}` exactly
when `a = 2⁻¹` (the lines through the centre). Hence a line kept by both is the meridian `H_0` or the critical line
`S_{0,2⁻¹}`: exactly two. -/
theorem invariant_lines (F : Frame p κ g) (ν : Shell p) :
    (∀ b : Shell p, (∀ z : Ext p ν, z.im = b → (Ext.conj z).im = b) ↔ b = 0) ∧
    (∀ c a : Shell p, (∀ z : Ext p ν, z.re = a + z.im * c → (Ext.conj z).re = a + (Ext.conj z).im * c) ↔ c = 0) ∧
    (∀ b : Shell p, (∀ z : Ext p ν, z.im = b → (rho z).im = b) ↔ b = 0) ∧
    (∀ c a : Shell p, (∀ z : Ext p ν, z.re = a + z.im * c → (rho z).re = a + (rho z).im * c) ↔
      a = ofNat (2 * κ + 1)) ∧
    (∀ b : Shell p, (∀ z : Ext p ν, z.im = b → (Ext.conj z).im = b) → (∀ z : Ext p ν, z.im = b → (rho z).im = b) →
      b = 0) ∧
    (∀ c a : Shell p, (∀ z : Ext p ν, z.re = a + z.im * c → (Ext.conj z).re = a + (Ext.conj z).im * c) →
      (∀ z : Ext p ν, z.re = a + z.im * c → (rho z).re = a + (rho z).im * c) → c = 0 ∧ a = ofNat (2 * κ + 1)) := by
  have hH : ∀ b : Shell p, (∀ z : Ext p ν, z.im = b → (Ext.conj z).im = b) ↔ b = 0 := fun b => by
    constructor
    · intro h
      have := h ⟨0, b⟩ rfl
      exact F.eq_zero_of_eq_neg this.symm
    · intro hb z hz
      show -z.im = b
      rw [hz, hb, neg_zero]
  have hS : ∀ c a : Shell p, (∀ z : Ext p ν, z.re = a + z.im * c → (Ext.conj z).re = a + (Ext.conj z).im * c) ↔ c = 0 :=
    fun c a => by
    constructor
    · intro h
      have := h ⟨a + 1 * c, 1⟩ rfl
      have h1 : a + 1 * c = a + -1 * c := this
      have h2 : 1 * c = -1 * c := by
        apply add_right_cancel (c := a)
        rw [add_comm (1 * c) a, add_comm (-1 * c) a]
        exact h1
      rw [one_mul, neg_one_mul] at h2
      exact F.eq_zero_of_eq_neg h2
    · intro hc z hz
      show z.re = a + -z.im * c
      rw [hc, mul_zero, add_zero] at hz
      rw [hc, mul_zero, add_zero]
      exact hz
  have hRH : ∀ b : Shell p, (∀ z : Ext p ν, z.im = b → (rho z).im = b) ↔ b = 0 := fun b => by
    constructor
    · intro h
      have := h ⟨0, b⟩ rfl
      exact F.eq_zero_of_eq_neg this.symm
    · intro hb z hz
      show -z.im = b
      rw [hz, hb, neg_zero]
  have hRS : ∀ c a : Shell p, (∀ z : Ext p ν, z.re = a + z.im * c → (rho z).re = a + (rho z).im * c) ↔
      a = ofNat (2 * κ + 1) := fun c a => by
    have hinv : (2 : Shell p) * ofNat (2 * κ + 1) = 1 := (half_inverse F).1
    constructor
    · intro h
      have := h ⟨a + 0 * c, 0⟩ rfl
      have h1 : 1 + -(a + 0 * c) = a + -0 * c := this
      rw [zero_mul, add_zero, neg_zero, zero_mul, add_zero] at h1
      apply F.mul_left_cancel F.two_ne_zero
      rw [hinv, two_mul']
      calc a + a = (1 + -a) + a := by rw [h1]
        _ = 1 := by rw [add_assoc, neg_add, add_zero]
    · intro ha z hz
      show 1 + -z.re = a + -z.im * c
      have h2 : (1 : Shell p) = a + a := by rw [ha, ← two_mul', hinv]
      rw [hz, h2, neg_add_rev, ← add_assoc, add_assoc a a, add_neg, add_zero, ← neg_mul]
  refine ⟨hH, hS, hRH, hRS, fun b h1 _ => (hH b).1 h1, fun c a h1 h2 => ⟨(hS c a).1 h1, (hRS c a).1 h2⟩⟩

/-- 20:F10 (iii) — a point of the framed plane off both lines (`Im z ≠ 0` and `Re z ≠ 2⁻¹`) lies on no line kept by
both involutions: a horizontal line `H_b` through it kept by both has `b = 0`, against `Im z ≠ 0`; a line `S_{c,a}`
through it kept by both has `c = 0` and `a = 2⁻¹`, so `Re z = 2⁻¹`, against the hypothesis. The clause of Theorem noline
that the python check A18 tests point by point, derived from `invariant_lines`. -/
theorem off_line_unregistered (F : Frame p κ g) (ν : Shell p) (z : Ext p ν) (hz1 : z.im ≠ 0)
    (hz2 : z.re ≠ ofNat (2 * κ + 1)) :
    (∀ b : Shell p, z.im = b → (∀ w : Ext p ν, w.im = b → (Ext.conj w).im = b) →
      (∀ w : Ext p ν, w.im = b → (rho w).im = b) → False) ∧
    (∀ c a : Shell p, z.re = a + z.im * c →
      (∀ w : Ext p ν, w.re = a + w.im * c → (Ext.conj w).re = a + (Ext.conj w).im * c) →
      (∀ w : Ext p ν, w.re = a + w.im * c → (rho w).re = a + (rho w).im * c) → False) := by
  obtain ⟨-, -, -, -, h5, h6⟩ := invariant_lines F ν
  refine ⟨fun b hb hc hr => hz1 (hb.trans (h5 b hc hr)), fun c a hz hc hr => ?_⟩
  obtain ⟨hc0, ha⟩ := h6 c a hc hr
  apply hz2
  rw [hz, hc0, mul_zero, add_zero, ha]


/-! ### The dual on the residues, the explicit formula along the meridian, and the zeros of every label
(20:E14, 20:B13, 20:F10; the audit of 17 October 2026) -/

/-- Fermat's inverse: a nonzero residue `y` has `y · y^{p−2} = y^{p−1} = 1`. -/
theorem pow_pred_inv (F : Frame p κ g) {y : Shell p} (hy : y ≠ 0) : y * y ^ (p - 2) = 1 := by
  have hp : p - 1 = (p - 2) + 1 := by
    have := F.one_lt_p
    match p, this with
    | k + 2, _ => rfl
  match F.eq_pow_of_ne_zero hy with
  | ⟨m, _, e⟩ =>
    rw [mul_comm, ← pow_succ, ← hp, ← e, pow_mul_comm, F.pow_n, one_pow]

/-- 20:E14 — the geometric sum of a nonzero residue over the cycle, the self-pairing of the modes: `Σ_{k<p−1} u^k` is
`−1` when `u = 1` and `0` otherwise. -/
theorem geom_sum_unit (F : Frame p κ g) {u : Shell p} (hu : u ≠ 0) :
    sumRange (fun k => u ^ k) (p - 1) = if u = 1 then -1 else 0 := by
  match F.eq_pow_of_ne_zero hu with
  | ⟨m, hm, e⟩ =>
    rw [← e]
    match m, hm with
    | 0, _ =>
      rw [pow_zero, ite_eq_left rfl]
      have h1 : ∀ k, k < p - 1 → (fun k => (1 : Shell p) ^ k) k = (fun _ => (1 : Shell p)) k := fun k _ => one_pow k
      rw [sum_congr (p - 1) h1, sum_const, mul_one, F.ofNat_n]
    | m + 1, hm =>
      have hne : g ^ (m + 1) ≠ 1 := fun h1 => by
        have := F.pow_inj hm (Nat.lt_of_le_of_lt (Nat.zero_le _) hm) (h1.trans (pow_zero g).symm)
        exact Nat.succ_ne_zero m this
      rw [ite_eq_right hne]
      exact (F.principal_root (m + 1) (Nat.succ_pos m) hm).2.1

/-- 20:E14 — the dual of a vector `w` on the nonzero residues (`w y` its value at the residue `y`, `1 ≤ y ≤ p − 1`):
`ŵ(k) = Σ_{y≠0} w(y) y^k`, the power sum of Theorem hp (i). -/
def dualRes (w : Nat → Shell p) (k : Nat) : Shell p :=
  sumRange (fun l => w (l + 1) * (ofNat (l + 1) : Shell p) ^ k) (p - 1)

/-- 20:E14, 20:E12 (i) — the inversion on the residues: `w(y) = −Σ_{k<p−1} ŵ(k) y^{−k}` with `y^{−1} = y^{p−2}`, the sign the
self-pairing `−1` of the power characters (`geom_sum_unit`). -/
theorem inversion_res (F : Frame p κ g) (w : Nat → Shell p) {y : Nat} (hy0 : 0 < y) (hy : y < p) :
    w y = -(sumRange (fun k => dualRes w k * ((ofNat y : Shell p) ^ (p - 2)) ^ k) (p - 1)) := by
  have hyv : (ofNat y : Shell p).val = y := by rw [val_ofNat, FRC.Nat.mod_eq_of_lt hy]
  have hy' : (ofNat y : Shell p) ≠ 0 := fun h0 => by
    have := congrArg Shell.val h0
    rw [hyv, val_zero] at this
    exact Nat.ne_of_gt hy0 this
  have hyi : (ofNat y : Shell p) * (ofNat y : Shell p) ^ (p - 2) = 1 := pow_pred_inv F hy'
  have hyi' : (ofNat y : Shell p) ^ (p - 2) ≠ 0 := fun h0 => by
    rw [h0, mul_zero] at hyi
    exact F.one_ne_zero hyi.symm
  -- the double sum, summed first over the modes: `Σ_l w(l+1) Σ_k (x_l y⁻¹)^k`
  have h1 : sumRange (fun k => dualRes w k * ((ofNat y : Shell p) ^ (p - 2)) ^ k) (p - 1)
      = sumRange (fun l => w (l + 1) * sumRange (fun k => ((ofNat (l + 1) : Shell p) * (ofNat y : Shell p) ^ (p - 2)) ^ k) (p - 1)) (p - 1) := by
    have e : ∀ k, k < p - 1 → (fun k => dualRes w k * ((ofNat y : Shell p) ^ (p - 2)) ^ k) k
        = (fun k => sumRange (fun l => w (l + 1) * ((ofNat (l + 1) : Shell p) * (ofNat y : Shell p) ^ (p - 2)) ^ k) (p - 1)) k := by
      intro k _
      show dualRes w k * ((ofNat y : Shell p) ^ (p - 2)) ^ k = _
      unfold dualRes
      rw [← sum_mul_right]
      apply sum_congr; intro l _
      rw [mul_pow, mul_assoc]
    rw [sum_congr (p - 1) e, sum_comm (fun k l => w (l + 1) * ((ofNat (l + 1) : Shell p) * (ofNat y : Shell p) ^ (p - 2)) ^ k) (p - 1) (p - 1)]
    apply sum_congr; intro l _
    exact sum_mul_left (fun k => ((ofNat (l + 1) : Shell p) * (ofNat y : Shell p) ^ (p - 2)) ^ k) (w (l + 1)) (p - 1)
  -- the inner sum is `−1` at the residue `y` and `0` elsewhere
  have h2 : ∀ l, l < p - 1 → (fun l => w (l + 1) * sumRange (fun k => ((ofNat (l + 1) : Shell p) * (ofNat y : Shell p) ^ (p - 2)) ^ k) (p - 1)) l
      = (fun l => if l = y - 1 then -(w y) else (0 : Shell p)) l := by
    intro l hl
    show w (l + 1) * sumRange (fun k => ((ofNat (l + 1) : Shell p) * (ofNat y : Shell p) ^ (p - 2)) ^ k) (p - 1)
      = if l = y - 1 then -(w y) else (0 : Shell p)
    have hlp : l + 1 < p := by
      have h : l + 1 < p - 1 + 1 := Nat.succ_lt_succ hl
      rw [FRC.Nat.sub_add_cancel Pos.pos] at h
      exact h
    have hl1 : (ofNat (l + 1) : Shell p) ≠ 0 := fun h0 => by
      have := congrArg Shell.val h0
      rw [val_ofNat, val_zero, FRC.Nat.mod_eq_of_lt hlp] at this
      exact Nat.succ_ne_zero l this
    rw [geom_sum_unit F (F.mul_ne_zero hl1 hyi')]
    match Nat.decEq l (y - 1) with
    | isTrue hly =>
      have hly' : l + 1 = y := by rw [hly]; exact FRC.Nat.sub_add_cancel hy0
      rw [ite_eq_left hly, hly', ite_eq_left hyi, ← mul_neg, mul_one]
    | isFalse hly =>
      rw [ite_eq_right hly]
      have hne : (ofNat (l + 1) : Shell p) * (ofNat y : Shell p) ^ (p - 2) ≠ 1 := fun h1 => by
        have hx : (ofNat (l + 1) : Shell p) = ofNat y := by
          calc (ofNat (l + 1) : Shell p) = ofNat (l + 1) * ((ofNat y : Shell p) * (ofNat y : Shell p) ^ (p - 2)) := by rw [hyi, mul_one]
            _ = (ofNat (l + 1) * (ofNat y : Shell p) ^ (p - 2)) * ofNat y := by rw [mul_assoc, mul_comm ((ofNat y : Shell p) ^ (p - 2)), ← mul_assoc]
            _ = ofNat y := by rw [h1, one_mul]
        have hv := congrArg Shell.val hx
        rw [val_ofNat, val_ofNat, FRC.Nat.mod_eq_of_lt hy, FRC.Nat.mod_eq_of_lt hlp] at hv
        exact hly (by rw [← hv]; rfl)
      rw [ite_eq_right hne, mul_zero]
  have hy1 : y - 1 < p - 1 := by
    apply Nat.lt_of_succ_lt_succ
    show y - 1 + 1 < p - 1 + 1
    rw [FRC.Nat.sub_add_cancel hy0, FRC.Nat.sub_add_cancel Pos.pos]
    exact hy
  have h3 : ∀ l, l < p - 1 → l ≠ y - 1 → (fun l => if l = y - 1 then -(w y) else (0 : Shell p)) l = 0 :=
    fun l _ hne => ite_eq_right hne
  rw [h1, sum_congr (p - 1) h2, sum_eq_single hy1 h3, ite_eq_left rfl, neg_neg]

/-- The cumulative read of the mode `k` along the meridian, `S_k(x) = Σ_{y≤x} y^{−k}` with `y^{−1} = y^{p−2}`. -/
def meridianRead (k x : Nat) : Shell p :=
  sumRange (fun l => ((ofNat (l + 1) : Shell p) ^ (p - 2)) ^ k) x

/-- 20:E14 — the explicit formula along the meridian: for `x ≤ p − 1` the count of `w` over the positions `1, …, x` is
the mode sum, `Σ_{y≤x} w(y) = −Σ_{k<p−1} ŵ(k) S_k(x)`, and the constant mode's read is the main term, `S_0(x) = x`. -/
theorem explicit_formula_meridian (F : Frame p κ g) (w : Nat → Shell p) {x : Nat} (hx : x ≤ p - 1) :
    sumRange (fun l => w (l + 1)) x = -(sumRange (fun k => dualRes w k * (meridianRead k x : Shell p)) (p - 1)) ∧
    (meridianRead 0 x : Shell p) = ofNat x := by
  refine ⟨?_, ?_⟩
  · have h1 : ∀ l, l < x → (fun l => w (l + 1)) l
        = (fun l => -(sumRange (fun k => dualRes w k * ((ofNat (l + 1) : Shell p) ^ (p - 2)) ^ k) (p - 1))) l := by
      intro l hl
      have hlp : l + 1 < p := by
        have h : l + 1 < p - 1 + 1 := Nat.succ_lt_succ (Nat.lt_of_lt_of_le hl hx)
        rw [FRC.Nat.sub_add_cancel Pos.pos] at h
        exact h
      exact inversion_res F w (Nat.succ_pos l) hlp
    rw [sum_congr x h1, sum_neg]
    congr 1
    rw [sum_comm (fun l k => dualRes w k * ((ofNat (l + 1) : Shell p) ^ (p - 2)) ^ k) (p - 1) x]
    apply sum_congr; intro k _
    exact sum_mul_left (fun l => ((ofNat (l + 1) : Shell p) ^ (p - 2)) ^ k) (dualRes w k) x
  · unfold meridianRead
    have e : ∀ l, l < x → ((ofNat (l + 1) : Shell p) ^ (p - 2)) ^ 0 = (1 : Shell p) := fun l _ => rfl
    rw [sum_congr x e, sum_const, mul_one]

/-- 20:B13, 20:F10 — every label other than `0` and `−1` is the readout of a nontrivial mode: `θ ≠ 0, −1` is `−g^k` for
some `1 ≤ k ≤ p − 2`; the label `−1` carries the constant mode `k = 0` and `0` is the centre. -/
theorem mode_at_label (F : Frame p κ g) {θ : Shell p} (hθ : θ ≠ 0) (hθ1 : θ ≠ -1) :
    ∃ k, 1 ≤ k ∧ k ≤ p - 2 ∧ -(g ^ k) = θ := by
  have hneg : -θ ≠ 0 := fun h0 => hθ (by rw [← neg_neg θ, h0, neg_zero])
  have hp : p - 1 = (p - 2) + 1 := by
    have := F.one_lt_p
    match p, this with
    | k + 2, _ => rfl
  match F.eq_pow_of_ne_zero hneg with
  | ⟨k, hk, e⟩ =>
    have hk0 : k ≠ 0 := fun h0 => hθ1 (by rw [h0, pow_zero] at e; rw [← neg_neg θ, ← e])
    refine ⟨k, Nat.pos_of_ne_zero hk0, ?_, by rw [e, neg_neg]⟩
    rw [hp] at hk
    exact Nat.le_of_lt_succ hk

/-- 20:B13, 20:F10 — frame coincidence on the critical line for every zero of the Subject: on two shells `p ≤ Ω` (the
Subject's residues the Carrier's residues below `p`), every label `1 ≤ θ ≤ p − 2` reads back as the integer `θ` in both
frames, the point `2⁻¹ + ηθ` has trace one in both with the half-turn as its real part, and it is the readout of a
nontrivial mode in both: the Subject's zero at `θ` and the Carrier's zero at `θ` are one zero. -/
theorem line_coincidence_all {Ω : Nat} [Pos Ω] {κ' : Nat} {h : Shell Ω} (F : Frame p κ g) (F' : Frame Ω κ' h)
    (hpΩ : p ≤ Ω) (ν : Shell p) (ν' : Shell Ω) (θ : Nat) (hθ0 : 0 < θ) (hθ : θ + 1 < p) :
    (ofNat θ : Shell p).val = θ ∧ (ofNat θ : Shell Ω).val = θ ∧
    Ext.trace (readout ν κ (ofNat θ)) = 1 ∧ Ext.trace (readout ν' κ' (ofNat θ)) = 1 ∧
    (readout ν κ (ofNat θ)).re = ofNat (2 * κ + 1) ∧ (readout ν' κ' (ofNat θ)).re = ofNat (2 * κ' + 1) ∧
    (∃ k, 1 ≤ k ∧ k ≤ p - 2 ∧ -(g ^ k) = (ofNat θ : Shell p)) ∧
    (∃ k', 1 ≤ k' ∧ k' ≤ Ω - 2 ∧ -(h ^ k') = (ofNat θ : Shell Ω)) := by
  have hθp : θ < p := Nat.lt_of_succ_lt hθ
  have hθΩ : θ < Ω := Nat.lt_of_lt_of_le hθp hpΩ
  have v1 : (ofNat θ : Shell p).val = θ := by rw [val_ofNat, FRC.Nat.mod_eq_of_lt hθp]
  have v2 : (ofNat θ : Shell Ω).val = θ := by rw [val_ofNat, FRC.Nat.mod_eq_of_lt hθΩ]
  have n1 : (ofNat θ : Shell p) ≠ 0 := fun h0 => by
    have := congrArg Shell.val h0; rw [v1, val_zero] at this; exact Nat.ne_of_gt hθ0 this
  have n2 : (ofNat θ : Shell Ω) ≠ 0 := fun h0 => by
    have := congrArg Shell.val h0; rw [v2, val_zero] at this; exact Nat.ne_of_gt hθ0 this
  have m1 : (ofNat θ : Shell p) ≠ -1 := fun h1 => by
    have := congrArg Shell.val (h1.trans F.ofNat_n.symm)
    rw [v1, val_ofNat, FRC.Nat.mod_eq_of_lt (Nat.sub_lt Pos.pos Nat.one_pos)] at this
    have h2 : θ + 1 < p - 1 + 1 := by rw [FRC.Nat.sub_add_cancel Pos.pos]; exact hθ
    exact Nat.ne_of_lt (Nat.lt_of_succ_lt_succ h2) this
  have m2 : (ofNat θ : Shell Ω) ≠ -1 := fun h1 => by
    have := congrArg Shell.val (h1.trans F'.ofNat_n.symm)
    rw [v2, val_ofNat, FRC.Nat.mod_eq_of_lt (Nat.sub_lt Pos.pos Nat.one_pos)] at this
    have h2 : θ + 1 < Ω - 1 + 1 := by rw [FRC.Nat.sub_add_cancel Pos.pos]; exact Nat.lt_of_lt_of_le hθ hpΩ
    exact Nat.ne_of_lt (Nat.lt_of_succ_lt_succ h2) this
  exact ⟨v1, v2, (readout_on_line F ν (ofNat θ)).1, (readout_on_line F' ν' (ofNat θ)).1, rfl, rfl,
    mode_at_label F n1 m1, mode_at_label F' n2 m2⟩

end rewrite20261017

end FRC.Horizon
