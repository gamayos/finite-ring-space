import FrcCore.Poly
import FrcCore.Orbit

/-!
# FrcCore.Theme.Numbers — the root criterion on a frame (the numbers theme, task LM22)

1:E3 on a frame `(τ; 0, 1, g)`: the root bound (`Frame.root_bound`, the case of `Poly.root_bound_of` that the frame's
lack of zero divisors gives), `X^p − X` vanishing everywhere (Fermat), and the criterion: `f` has a root iff `f` and
`X^p − X` share a factor of positive degree (`root_iff_common_factor`). The reverse direction is constructive — the
root is found by deciding `∃ i < p, d(i) = 0`.

Moved here from `Poly.lean` by task LM22, names unchanged, so that the polynomials stand without the frame. No axioms.
-/

namespace FRC
namespace Shell

variable {p : Nat} [Pos p]

namespace Poly

namespace Frame
variable {κ : Nat} {g : Shell p}

/-- 1:E3, the root bound — a polynomial of degree at most `n` that vanishes at `n + 1` distinct points is
zero: the distinct roots are counted by the degree. -/
theorem root_bound (F : Frame p κ g) : ∀ (n : Nat) (f : Poly p), Bound f n → ∀ (r : Nat → Shell p),
    (∀ i j, i ≤ n → j ≤ n → r i = r j → i = j) → (∀ i, i ≤ n → eval f n (r i) = 0) → ∀ i, f i = 0 :=
  root_bound_of (fun h => F.mul_eq_zero h)

theorem xpx_bound : Bound (xpx : Poly p) p := by
  intro i hi
  show (if i = p then 1 else if i = 1 then -1 else 0 : Shell p) = 0
  rw [ite_eq_right (Nat.ne_of_gt hi), ite_eq_right (fun e => absurd hi (by rw [e]; exact Nat.not_lt_of_le (Pos.pos : 0 < p)))]

theorem xpx_p : (xpx : Poly p) p = 1 := by
  show (if p = p then 1 else if p = 1 then -1 else 0 : Shell p) = 1
  rw [ite_eq_left rfl]

/-- `X^p − X` vanishes everywhere: Fermat. -/
theorem eval_xpx (F : Frame p κ g) (a : Shell p) : eval (xpx : Poly p) p a = 0 := by
  have h2 : 2 ≤ p := Nat.le_of_lt F.two_lt_p
  have e : p + 1 = 2 + (p - 1) := by
    calc p + 1 = 1 + (p - 1) + 1 := by rw [FRC.Nat.add_sub_of_le Pos.pos]
      _ = 2 + (p - 1) := by rw [Nat.add_right_comm]
  unfold eval
  rw [e, sum_split, sumRange_succ, sumRange_succ, sumRange_zero, zero_add]
  have hp1 : p ≠ 1 := fun h => absurd (h ▸ h2 : 2 ≤ 1) (Nat.not_le_of_lt (Nat.lt_succ_self 1))
  have t0 : (xpx : Poly p) 0 * a ^ 0 = 0 := by
    show (if 0 = p then 1 else if 0 = 1 then -1 else 0 : Shell p) * a ^ 0 = 0
    rw [ite_eq_right (fun h => by have := (Pos.pos : 0 < p); rw [← h] at this; exact Nat.lt_irrefl 0 this),
      ite_eq_right (fun h => FRC.Nat.succ_ne_zero 0 h.symm), zero_mul]
  have t1 : (xpx : Poly p) 1 * a ^ 1 = -a := by
    show (if 1 = p then 1 else if 1 = 1 then -1 else 0 : Shell p) * a ^ 1 = -a
    rw [ite_eq_right (fun h => hp1 h.symm), ite_eq_left rfl, pow_one, neg_one_mul]
  have t2 : sumRange (fun t => (xpx : Poly p) (2 + t) * a ^ (2 + t)) (p - 1) = a ^ p := by
    have hl : p - 2 < p - 1 := by
      have e : p = (p - 2) + 2 := (FRC.Nat.sub_add_cancel h2).symm
      rw [e]
      exact Nat.lt_succ_self (p - 2)
    rw [sum_eq_single hl (fun t _ ht => by
      show (if 2 + t = p then 1 else if 2 + t = 1 then -1 else 0 : Shell p) * a ^ (2 + t) = 0
      rw [ite_eq_right (fun h => ht (by rw [← h, Nat.add_comm, FRC.Nat.add_sub_cancel])),
        ite_eq_right (fun h => FRC.Nat.succ_ne_zero t (Nat.succ.inj (by rw [Nat.add_comm] at h; exact h))), zero_mul])]
    show (if 2 + (p - 2) = p then 1 else if 2 + (p - 2) = 1 then -1 else 0 : Shell p) * a ^ (2 + (p - 2)) = a ^ p
    rw [FRC.Nat.add_sub_of_le h2, ite_eq_left rfl, one_mul]
  show (xpx : Poly p) 0 * a ^ 0 + (xpx : Poly p) 1 * a ^ 1 + sumRange (fun t => (xpx : Poly p) (2 + t) * a ^ (2 + t)) (p - 1) = 0
  rw [t0, t1, t2, zero_add, F.fermat, neg_add]

/-- A common factor of positive degree `m`: `d` with `d m ≠ 0` dividing both, with cofactors of the
complementary degrees. -/
def CommonFactor (f : Poly p) (n : Nat) (h : Poly p) (k : Nat) : Prop :=
  ∃ (d : Poly p) (m : Nat) (q1 q2 : Poly p), 1 ≤ m ∧ Bound d m ∧ d m ≠ 0 ∧ Bound q1 (n - m) ∧
    Bound q2 (k - m) ∧ (∀ i, f i = mul d q1 i) ∧ (∀ i, h i = mul d q2 i)

/-- 1:E3, the root criterion — `f` has a root in the shell iff `f` and `X^p − X` share a factor of positive
degree.  Forward: the factor is `X − a` (synthetic division, Fermat).  Backward: a common factor `d` of
degree `m ≥ 1` with no root would force its cofactor in `X^p − X`, of degree `p − m < p`, to vanish at
all `p` residues, hence to be zero (`root_bound`), against `X^p − X ≠ 0`; the root of `d` is found by
deciding `∃ i < p, d(i) = 0`. -/
theorem root_iff_common_factor (F : Frame p κ g) {f : Poly p} {n : Nat} (hf : Bound f n) :
    (∃ a, eval f n a = 0) ↔ CommonFactor f n (xpx : Poly p) p := by
  constructor
  · intro ⟨a, ha⟩
    have s1 := quot_linear_spec hf ha
    have s2 := quot_linear_spec (xpx_bound (p := p)) (eval_xpx F a)
    exact ⟨linear a, 1, quotLinear f n a, quotLinear xpx p a, Nat.le_refl 1, linear_bound a, F.one_ne_zero,
      s1.1, s2.1, s1.2, s2.2⟩
  · intro ⟨d, m, q1, q2, hm, hd, hdm, hq1, hq2, e1, e2⟩
    -- every residue is a root of `d · q2`
    have hprod : ∀ a, eval d m a * eval q2 (p - m) a = 0 := fun a => by
      rw [← eval_mul hd hq2, ← eval_bound (mul_bound hd hq2) (Nat.add_le_add_left (Nat.sub_le p m) m) a,
        ← eval_congr e2, eval_bound xpx_bound (Nat.le_add_left p m), eval_xpx F]
    have : ∀ v, Decidable (∃ i, i < p ∧ eval d m (ofNat i) = v) :=
      fun v => decExistsLT (fun i => eval d m (ofNat i) = v) p
    match this 0 with
    | .isTrue ⟨i, _, hi⟩ =>
      refine ⟨ofNat i, ?_⟩
      rw [← eval_bound hf (Nat.le_add_right n m), eval_congr e1,
        eval_bound (mul_bound hd hq1) (by rw [Nat.add_comm n m]; exact Nat.add_le_add_left (Nat.sub_le n m) m),
        eval_mul hd hq1, hi, zero_mul]
    | .isFalse hno =>
      -- `q2` vanishes at the `p − m + 1 ≤ p` residues `0, …, p − m`, so it is zero
      have hk : p - m < p := Nat.sub_lt Pos.pos hm
      have hz : ∀ i, q2 i = 0 := by
        apply root_bound F (p - m) q2 hq2 (fun i => ofNat i)
        · intro i j hi hj e
          exact ofNat_inj_lt (Nat.lt_of_le_of_lt hi hk) (Nat.lt_of_le_of_lt hj hk) e
        · intro i hi
          match F.mul_eq_zero (hprod (ofNat i)) with
          | .inl e => exact absurd ⟨i, Nat.lt_of_le_of_lt hi hk, e⟩ hno
          | .inr e => exact e
      have : (xpx : Poly p) p = 0 := by
        rw [e2 p]
        apply sum_zero
        intro j _
        show d j * q2 (p - j) = 0
        rw [hz, mul_zero]
      rw [xpx_p] at this
      exact absurd this F.one_ne_zero

end Frame
end Poly
end Shell
end FRC
