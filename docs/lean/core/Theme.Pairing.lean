import FrcCore.Theme.WindowModes
import FrcCore.Theme.Steps

/-!
# The reflected pairing of two modes

20-rh's row G20 (26 November 2026). The reflection `ρ ↦ 1 − ρ` of the zeros acts on the residues as `x ↦ 1 − x`.
The reflected pairing of the modes of counts `k` and `m` is `R(k, m) = Σ_{x ≠ 0, 1} x^k (1 − x)^m`. By the
recurrence `R(k, m + 1) = R(k, m) − R(k + 1, m)` and the zero slot, `R(k, m) = −(−1)^k · C(m, p − 1 − k)` for two
nonconstant modes. So `R(k, m) = 0` when `k + m < p − 1`, and it is not `0` otherwise. A mode and its conjugate have
`−(−1)^k`. For `k + m ≠ p − 1` exactly one of `R(k, m)` and the pairing of the conjugates is `0`.
-/

namespace FRC
namespace Nat

/-- The binomial coefficient, by Pascal's rule. -/
def choose : Nat → Nat → Nat
  | _, 0 => 1
  | 0, _ + 1 => 0
  | n + 1, j + 1 => choose n j + choose n (j + 1)

theorem choose_zero_right (n : Nat) : choose n 0 = 1 := by cases n <;> rfl

theorem choose_succ_succ (n j : Nat) : choose (n + 1) (j + 1) = choose n j + choose n (j + 1) := rfl

theorem choose_eq_zero_of_lt : ∀ {n j : Nat}, n < j → choose n j = 0
  | _, 0, h => absurd h (Nat.not_lt_zero _)
  | 0, _ + 1, _ => rfl
  | n + 1, j + 1, h => by
    have h1 : n < j := Nat.lt_of_succ_lt_succ h
    rw [choose_succ_succ, choose_eq_zero_of_lt h1, choose_eq_zero_of_lt (Nat.lt_succ_of_lt h1)]

theorem choose_self : ∀ n : Nat, choose n n = 1
  | 0 => rfl
  | n + 1 => by rw [choose_succ_succ, choose_self n, choose_eq_zero_of_lt (Nat.lt_succ_self n)]

/-- The absorption rule `(j + 1) · C(n + 1, j + 1) = (n + 1) · C(n, j)`. -/
theorem succ_mul_choose : ∀ n j : Nat, (j + 1) * choose (n + 1) (j + 1) = (n + 1) * choose n j
  | 0, 0 => rfl
  | 0, j + 1 => by
    rw [choose_succ_succ, choose_eq_zero_of_lt (Nat.zero_lt_succ j), choose_eq_zero_of_lt (Nat.zero_lt_succ (j + 1))]
    rfl
  | n + 1, 0 => by
    have h1 : choose (n + 1) 1 = n + 1 := by
      have := succ_mul_choose n 0
      rw [choose_zero_right, Nat.mul_one, Nat.zero_add, Nat.one_mul] at this
      exact this
    rw [choose_succ_succ, choose_zero_right, Nat.mul_one, Nat.zero_add, Nat.one_mul, h1, Nat.add_comm]
  | n + 1, j + 1 => by
    have ihA := succ_mul_choose n j
    have ihB := succ_mul_choose n (j + 1)
    calc (j + 1 + 1) * choose (n + 1 + 1) (j + 1 + 1)
        = (j + 1 + 1) * (choose (n + 1) (j + 1) + choose (n + 1) (j + 1 + 1)) := rfl
      _ = (j + 1 + 1) * choose (n + 1) (j + 1) + (j + 1 + 1) * choose (n + 1) (j + 1 + 1) := Nat.mul_add _ _ _
      _ = ((j + 1) * choose (n + 1) (j + 1) + choose (n + 1) (j + 1)) + (n + 1) * choose n (j + 1) := by
        rw [ihB, add_mul (j + 1) 1, Nat.one_mul]
      _ = ((n + 1) * choose n j + choose (n + 1) (j + 1)) + (n + 1) * choose n (j + 1) := by rw [ihA]
      _ = ((n + 1) * choose n j + (n + 1) * choose n (j + 1)) + choose (n + 1) (j + 1) := Nat.add_right_comm _ _ _
      _ = (n + 1) * choose (n + 1) (j + 1) + choose (n + 1) (j + 1) := by rw [← Nat.mul_add, ← choose_succ_succ]
      _ = (n + 1 + 1) * choose (n + 1) (j + 1) := by rw [add_mul (n + 1) 1, Nat.one_mul]

/-- A difference is positive when the subtrahend is smaller. -/
theorem sub_pos_lt {a b : Nat} (h : b < a) : 0 < a - b :=
  le_sub_of_add_le (by rw [Nat.add_comm]; exact h)

end Nat

namespace Horizon

open FRC.Shell FRC.Shell.Frame

variable {p : Nat} [Pos p] {κ : Nat} {g : Shell p}

section pairing20261126

/-- The binomial coefficient `C(m, d)` with `d ≤ m < p` is not `0` on the shell. -/
theorem choose_ne_zero (F : Frame p κ g) : ∀ d m : Nat, d ≤ m → m < p → (ofNat (Nat.choose m d) : Shell p) ≠ 0
  | 0, m, _, _ => by rw [Nat.choose_zero_right]; exact F.one_ne_zero
  | _ + 1, 0, h, _ => absurd h (Nat.not_succ_le_zero _)
  | d + 1, m + 1, h, hm => fun h0 => by
    have ih := choose_ne_zero F d m (Nat.le_of_succ_le_succ h) (Nat.lt_of_succ_lt hm)
    have hprod := F.mul_ne_zero (label_ne_zero (Nat.zero_lt_succ m) hm) ih
    rw [ofNat_mul, ← Nat.succ_mul_choose, ← ofNat_mul, h0, mul_zero] at hprod
    exact hprod rfl

/-- The pairing summed over the nonzero residues, `Σ_{x ≠ 0} x^k (1 − x)^m`. -/
def sumPairing (p : Nat) [Pos p] (k m : Nat) : Shell p :=
  sumRange (fun l => (ofNat (l + 1) : Shell p) ^ k * (1 + -(ofNat (l + 1))) ^ m) (p - 1)

/-- The reflected pairing of the modes of counts `k` and `m`, `R(k, m) = Σ_{x ≠ 0, 1} x^k (1 − x)^m`. -/
def reflected (p : Nat) [Pos p] (k m : Nat) : Shell p :=
  sumRange (fun l => (ofNat (l + 2) : Shell p) ^ k * (1 + -(ofNat (l + 2))) ^ m) (p - 2)

/-- For a nonconstant second mode the term at `x = 1` is `0`. -/
theorem reflected_eq_sum_pairing {k m : Nat} (hm : 0 < m) (hp : 0 < p - 1) : reflected p k m = sumPairing p k m := by
  have hp1 : p - 2 + 1 = p - 1 := Nat.sub_add_cancel hp
  have h0 : ((ofNat (0 + 1) : Shell p) ^ k * (1 + -(ofNat (0 + 1))) ^ m) = 0 := by
    cases m with
    | zero => exact absurd hm (Nat.lt_irrefl 0)
    | succ m =>
      show (1 : Shell p) ^ k * ((1 + -1) ^ m * (1 + -1)) = 0
      rw [add_neg, mul_zero, mul_zero]
  show _ = sumRange _ (p - 1)
  rw [← hp1, sumRange_succ', h0, zero_add]
  rfl

theorem sum_pairing_succ (k m : Nat) : sumPairing p k (m + 1) = sumPairing p k m + -(sumPairing p (k + 1) m) := by
  show sumRange _ (p - 1) = sumRange _ (p - 1) + -(sumRange _ (p - 1))
  rw [← sum_neg, ← sum_add]
  refine sum_congr _ (fun l _ => ?_)
  show (ofNat (l + 1) : Shell p) ^ k * ((1 + -(ofNat (l + 1))) ^ m * (1 + -(ofNat (l + 1)))) =
    (ofNat (l + 1) : Shell p) ^ k * (1 + -(ofNat (l + 1))) ^ m +
      -((ofNat (l + 1) : Shell p) ^ k * ofNat (l + 1) * (1 + -(ofNat (l + 1))) ^ m)
  rw [left_distrib ((1 + -(ofNat (l + 1) : Shell p)) ^ m), mul_one, left_distrib, mul_assoc ((ofNat (l + 1) : Shell p) ^ k),
    mul_comm (ofNat (l + 1) : Shell p), ← mul_neg ((1 + -(ofNat (l + 1) : Shell p)) ^ m), ← mul_neg ((ofNat (l + 1) : Shell p) ^ k)]

theorem sum_pairing_zero (k : Nat) : sumPairing p k 0 = sumRange (fun l => (ofNat (l + 1) : Shell p) ^ k) (p - 1) :=
  sum_congr _ (fun _ _ => mul_one _)

/-- The count `p − 1 + 1` gives the mode of count `1`. -/
theorem sum_pairing_period (F : Frame p κ g) (m : Nat) : sumPairing p (p - 1 + 1) m = sumPairing p 1 m := by
  refine sum_congr _ (fun l hl => ?_)
  have hl1 : l + 1 < p :=
    Nat.lt_of_lt_of_le (Nat.succ_lt_succ hl) (Nat.le_of_eq (Nat.sub_add_cancel (Pos.pos : 0 < p)))
  show (ofNat (l + 1) : Shell p) ^ (p - 1) * ofNat (l + 1) * _ = (ofNat (l + 1) : Shell p) ^ 1 * _
  rw [unit_pow_card F (label_ne_zero (Nat.zero_lt_succ l) hl1), one_mul, pow_one]

theorem neg_one_pow_succ' (d : Nat) : (-1 : Shell p) ^ (d + 1) = -((-1) ^ d) := by
  rw [pow_succ, ← mul_neg, mul_one]

/-- The value of the pairing: for a count `k ≥ 1` with `k + d = p − 1` and a count `m < p − 1`,
`Σ_{x ≠ 0} x^k (1 − x)^m = −(−1)^d · C(m, d)`. -/
theorem sum_pairing_choose (F : Frame p κ g) : ∀ m : Nat, m < p - 1 → ∀ k d : Nat, 0 < k → k + d = p - 1 →
    sumPairing p k m = -((-1 : Shell p) ^ d * ofNat (Nat.choose m d))
  | 0, _, k, d, hk, hkd => by
    rw [sum_pairing_zero]
    cases d with
    | zero =>
      have hk' : k = p - 1 := hkd
      rw [hk', (zero_slot F).2]
      show (-1 : Shell p) = -((1 : Shell p) * 1)
      rw [one_mul]
    | succ d =>
      have hk' : k < p - 1 := by rw [← hkd]; exact Nat.lt_add_of_pos_right (Nat.zero_lt_succ d)
      rw [(zero_slot F).1 k hk hk']
      show (0 : Shell p) = -((-1 : Shell p) ^ (d + 1) * 0)
      rw [mul_zero, neg_zero]
  | m + 1, hm, k, d, hk, hkd => by
    have hm' : m < p - 1 := Nat.lt_of_succ_lt hm
    rw [sum_pairing_succ]
    cases d with
    | zero =>
      have hk' : k = p - 1 := hkd
      have hd : 1 + (p - 1 - 1) = p - 1 := Nat.add_sub_of_le (Nat.lt_of_le_of_lt (Nat.zero_le _) hm)
      have hlt : m < p - 1 - 1 := FRC.Nat.le_sub_of_add_le hm
      rw [sum_pairing_choose F m hm' k 0 hk hkd, hk', sum_pairing_period F m,
        sum_pairing_choose F m hm' 1 (p - 1 - 1) (Nat.zero_lt_succ 0) hd, Nat.choose_eq_zero_of_lt hlt]
      show -((-1 : Shell p) ^ 0 * ofNat (Nat.choose m 0)) + -(-((-1 : Shell p) ^ (p - 1 - 1) * 0)) =
        -((-1 : Shell p) ^ 0 * ofNat (Nat.choose (m + 1) 0))
      rw [mul_zero, neg_zero, neg_zero, add_zero, Nat.choose_zero_right, Nat.choose_zero_right]
    | succ d =>
      have hkd' : k + 1 + d = p - 1 := by rw [Nat.add_right_comm]; exact hkd
      rw [sum_pairing_choose F m hm' k (d + 1) hk hkd, sum_pairing_choose F m hm' (k + 1) d (Nat.zero_lt_succ k) hkd',
        Nat.choose_succ_succ, ← ofNat_add, neg_one_pow_succ']
      have e1 : -(-((-1 : Shell p) ^ d) * ofNat (Nat.choose m (d + 1))) =
          (-1 : Shell p) ^ d * ofNat (Nat.choose m (d + 1)) := by rw [← neg_mul, neg_neg]
      have e2 : -(-((-1 : Shell p) ^ d) * (ofNat (Nat.choose m d) + ofNat (Nat.choose m (d + 1)))) =
          (-1 : Shell p) ^ d * ofNat (Nat.choose m d) + (-1 : Shell p) ^ d * ofNat (Nat.choose m (d + 1)) := by
        rw [← neg_mul, neg_neg, left_distrib]
      rw [e1, e2, neg_neg]
      exact add_comm _ _

/-- The signs of a count and of its conjugate agree. -/
theorem neg_one_pow_conj (F : Frame p κ g) {k d : Nat} (hkd : k + d = p - 1) : (-1 : Shell p) ^ d = (-1) ^ k := by
  have h1 : (-1 : Shell p) ^ k * (-1) ^ d = 1 := by
    rw [← pow_add, hkd, ← F.four_kappa, pow_add]; exact neg_one_pow_sq _
  calc (-1 : Shell p) ^ d = ((-1) ^ k * (-1) ^ k) * (-1) ^ d := by rw [neg_one_pow_sq, one_mul]
    _ = (-1) ^ k * ((-1) ^ k * (-1) ^ d) := mul_assoc _ _ _
    _ = (-1) ^ k := by rw [h1, mul_one]

/-- 20:G20 — the value of the reflected pairing of two nonconstant modes: `R(k, m) = −(−1)^k · C(m, p − 1 − k)`. -/
theorem reflected_value (F : Frame p κ g) {k m : Nat} (hk : 0 < k) (hk1 : k < p - 1) (hm : 0 < m)
    (hm1 : m < p - 1) : reflected p k m = -((-1 : Shell p) ^ k * ofNat (Nat.choose m (p - 1 - k))) := by
  have hkd : k + (p - 1 - k) = p - 1 := Nat.add_sub_of_le (Nat.le_of_lt hk1)
  rw [reflected_eq_sum_pairing hm (Nat.lt_of_le_of_lt (Nat.zero_le _) hk1), sum_pairing_choose F m hm1 k _ hk hkd,
    neg_one_pow_conj F hkd]

/-- 20:G20 — the reflected pairing of two nonconstant modes is `0` when `k + m < p − 1`. -/
theorem reflected_zero (F : Frame p κ g) {k m : Nat} (hk : 0 < k) (hm : 0 < m) (h : k + m < p - 1) :
    reflected p k m = 0 := by
  have hk1 : k < p - 1 := Nat.lt_of_le_of_lt (Nat.le_add_right k m) h
  have hm1 : m < p - 1 := Nat.lt_of_le_of_lt (Nat.le_add_left m k) h
  have hkd : k + (p - 1 - k) = p - 1 := Nat.add_sub_of_le (Nat.le_of_lt hk1)
  have hlt : m < p - 1 - k := Nat.lt_of_add_lt_add_left (by rw [hkd]; exact h)
  rw [reflected_value F hk hk1 hm hm1, Nat.choose_eq_zero_of_lt hlt]
  show -((-1 : Shell p) ^ k * 0) = 0
  rw [mul_zero, neg_zero]

/-- 20:G20 — the reflected pairing of two nonconstant modes is not `0` when `k + m ≥ p − 1`. -/
theorem reflected_ne_zero (F : Frame p κ g) {k m : Nat} (hk : 0 < k) (hk1 : k < p - 1) (hm : 0 < m)
    (hm1 : m < p - 1) (h : p - 1 ≤ k + m) : reflected p k m ≠ 0 := fun h0 => by
  have hkd : k + (p - 1 - k) = p - 1 := Nat.add_sub_of_le (Nat.le_of_lt hk1)
  have hle : p - 1 - k ≤ m := Nat.le_of_add_le_add_left (by rw [hkd]; exact h)
  have hmp : m < p := Nat.lt_of_lt_of_le hm1 (Nat.sub_le p 1)
  rw [reflected_value F hk hk1 hm hm1] at h0
  exact F.mul_ne_zero (pow_ne_zero_of F (neg_one_ne_zero F) k) (choose_ne_zero F _ m hle hmp) (neg_eq_zero h0)

/-- 20:G20 — a nonconstant mode and its conjugate have the reflected pairing `−(−1)^k`. -/
theorem reflected_conjugate (F : Frame p κ g) {k : Nat} (hk : 0 < k) (hk1 : k < p - 1) :
    reflected p k (p - 1 - k) = -((-1 : Shell p) ^ k) := by
  have hpos : 0 < p - 1 := Nat.lt_of_le_of_lt (Nat.zero_le _) hk1
  rw [reflected_value F hk hk1 (Nat.sub_pos_lt hk1) (Nat.sub_lt hpos hk), Nat.choose_self]
  show -((-1 : Shell p) ^ k * 1) = _
  rw [mul_one]

/-- 20:G20 — for two nonconstant modes with `k + m ≠ p − 1` exactly one of `R(k, m)` and the pairing of the
conjugates `R(p − 1 − k, p − 1 − m)` is `0`: the first when `k + m < p − 1`, the second when `k + m > p − 1`. -/
theorem reflected_exclusive (F : Frame p κ g) {k m : Nat} (hk : 0 < k) (hk1 : k < p - 1) (hm : 0 < m)
    (hm1 : m < p - 1) :
    (k + m < p - 1 → reflected p k m = 0 ∧ reflected p (p - 1 - k) (p - 1 - m) ≠ 0) ∧
    (p - 1 < k + m → reflected p k m ≠ 0 ∧ reflected p (p - 1 - k) (p - 1 - m) = 0) := by
  have hpos : 0 < p - 1 := Nat.lt_of_le_of_lt (Nat.zero_le _) hk1
  have hkd : k + (p - 1 - k) = p - 1 := Nat.add_sub_of_le (Nat.le_of_lt hk1)
  have hmd : m + (p - 1 - m) = p - 1 := Nat.add_sub_of_le (Nat.le_of_lt hm1)
  have hsum : (k + m) + ((p - 1 - k) + (p - 1 - m)) = (p - 1) + (p - 1) := by
    rw [Nat.add_add_add_comm, hkd, hmd]
  have hk' : 0 < p - 1 - k := Nat.sub_pos_lt hk1
  have hm' : 0 < p - 1 - m := Nat.sub_pos_lt hm1
  have hk1' : p - 1 - k < p - 1 := Nat.sub_lt hpos hk
  have hm1' : p - 1 - m < p - 1 := Nat.sub_lt hpos hm
  constructor
  · intro h
    refine ⟨reflected_zero F hk hm h, reflected_ne_zero F hk' hk1' hm' hm1' (Nat.le_of_not_lt (fun h' => ?_))⟩
    have := Nat.add_lt_add h h'
    rw [hsum] at this
    exact Nat.lt_irrefl _ this
  · intro h
    refine ⟨reflected_ne_zero F hk hk1 hm hm1 (Nat.le_of_lt h), reflected_zero F hk' hm' (Nat.lt_of_not_le (fun h' => ?_))⟩
    have := Nat.add_lt_add_of_lt_of_le h h'
    rw [hsum] at this
    exact Nat.lt_irrefl _ this

end pairing20261126

end Horizon
end FRC
