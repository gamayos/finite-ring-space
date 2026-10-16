import FrcCore.Theme.Field
import FrcCore.Ring

/-!
# FrcCore.Theme.Interference — the quantum theme: the interference hierarchy and the splitting depth (22-quantum, 15 October 2026)

Two laws of the ledger read on every shell, where the ledger's conjugation is any additive map `c` (the shadow of
`ζ ↦ ζ⁻¹` on the windings, extended additively) and the weight is `w(x) = x · c(x)`:

* the Sorkin hierarchy: the `k`-fold mixed difference of the weight vanishes for every `k ≥ 3` and every base point,
  while the second difference is the cross term `a c(b) + b c(a)`, nonzero at `a = b = 1` with `c` the identity
  (`sorkin_hierarchy`, `sorkin_second`, `sorkin_second_witness`, 22:C8, X8, P2): the interference term `I_k`
  (inclusion–exclusion of the pair count over the paths, the mixed difference at the origin) is zero exactly for
  `k ≥ 3` and generically nonzero for `k = 2`;
* the Hadamard layers: on a shell with a quarter-turn `i² = −1`, `(1 + i)² = 2i`, so `k` balanced layers give the
  amplitude `(1 + i)^k = 2^m i^m` (`k = 2m`) or `2^m i^m (1 + i)` (`k = 2m + 1`) (`hadamard_even`, `hadamard_odd`,
  22:C14); the minimal tally norm `T(k) = 2^{k + [k odd]}` is monotone and the ceiling `k* = max{k : d T(k) < Ω}` is
  decided on the worked carrier `Ω = 641`: `8` for the unit core, `6` for the Bell core `d = 8` (`tally_norm_mono`,
  `ceiling_641`, 22:C14, P5).

No axioms.
-/

namespace FRC.Interference

open FRC.Shell
open FRC.Shell.Prime

variable {q : Nat} [Pos q]

/-! ## The Sorkin hierarchy -/

/-- A conjugation on the shell: an additive map (the shadow of the ledger's conjugation). -/
def Additive (c : Shell q → Shell q) : Prop := ∀ x y, c (x + y) = c x + c y

/-- The weight `w(x) = x · c(x)`, the shadow of the squared amplitude `x x̄`. -/
def weight (c : Shell q → Shell q) (x : Shell q) : Shell q := x * c x

/-- The `k`-fold mixed difference of `f` along the directions `a 0, …, a (k−1)`:
`Δ_{a_{k−1}} ⋯ Δ_{a_0} f (x)`, with `Δ_a f (x) = f (x + a) − f (x)`. The Sorkin term `I_k` of the paths `a_0, …, a_{k−1}`
is the difference at the origin. -/
def mixedDiff (a : Nat → Shell q) (f : Shell q → Shell q) : Nat → Shell q → Shell q
  | 0, x => f x
  | k + 1, x => mixedDiff a f k (x + a k) + -(mixedDiff a f k x)

theorem mixedDiff_zero (a : Nat → Shell q) (f : Shell q → Shell q) (x : Shell q) : mixedDiff a f 0 x = f x := rfl

theorem mixedDiff_succ (a : Nat → Shell q) (f : Shell q → Shell q) (k : Nat) (x : Shell q) :
    mixedDiff a f (k + 1) x = mixedDiff a f k (x + a k) + -(mixedDiff a f k x) := rfl

/-- The first difference of the weight: `Δ_a w (x) = x c(a) + a c(x) + a c(a)`. -/
theorem weight_diff1 {c : Shell q → Shell q} (hc : Additive c) (a : Nat → Shell q) (x : Shell q) :
    mixedDiff a (weight c) 1 x = x * c (a 0) + a 0 * c x + a 0 * c (a 0) := by
  rw [mixedDiff_succ, mixedDiff_zero, mixedDiff_zero]
  unfold weight
  rw [hc]
  exact Shell.Frame.RE.sound (Shell.Frame.look [x, a 0, c x, c (a 0)])
    (.add (.mul (.add (.var 0) (.var 1)) (.add (.var 2) (.var 3))) (.neg (.mul (.var 0) (.var 2))))
    (.add (.add (.mul (.var 0) (.var 3)) (.mul (.var 1) (.var 2))) (.mul (.var 1) (.var 3)))
    (by decide +kernel)

/-- 22:C8 — the second difference is the cross term: `Δ_b Δ_a w (x) = b c(a) + a c(b)`, independent of `x`. -/
theorem sorkin_second {c : Shell q → Shell q} (hc : Additive c) (a : Nat → Shell q) (x : Shell q) :
    mixedDiff a (weight c) 2 x = a 1 * c (a 0) + a 0 * c (a 1) := by
  rw [mixedDiff_succ, weight_diff1 hc, weight_diff1 hc, hc]
  exact Shell.Frame.RE.sound (Shell.Frame.look [x, a 0, a 1, c x, c (a 0), c (a 1)])
    (.add (.add (.add (.mul (.add (.var 0) (.var 2)) (.var 4)) (.mul (.var 1) (.add (.var 3) (.var 5)))) (.mul (.var 1) (.var 4)))
      (.neg (.add (.add (.mul (.var 0) (.var 4)) (.mul (.var 1) (.var 3))) (.mul (.var 1) (.var 4)))))
    (.add (.mul (.var 2) (.var 4)) (.mul (.var 1) (.var 5)))
    (by decide +kernel)

/-- The third difference vanishes identically. -/
theorem sorkin_third {c : Shell q → Shell q} (hc : Additive c) (a : Nat → Shell q) (x : Shell q) :
    mixedDiff a (weight c) 3 x = 0 := by
  rw [mixedDiff_succ, sorkin_second hc, sorkin_second hc, add_neg]

/-- 22:C8, 22:X8, 22:P2 — **the Sorkin hierarchy**: for every additive conjugation `c`, every family of paths `a` and every
base point `x`, the `k`-fold mixed difference of the weight `w(x) = x c(x)` is zero for every `k ≥ 3`; so the
interference terms `I_k = Δ_{a_{k−1}} ⋯ Δ_{a_0} w (0)` vanish exactly from the third order on, on every channel and
outcome (the ledger's value reduces to the shadow, and a vanishing shadow lifts to a multiple of `Ω`). -/
theorem sorkin_hierarchy {c : Shell q → Shell q} (hc : Additive c) (a : Nat → Shell q) :
    ∀ k, ∀ x, mixedDiff a (weight c) (k + 3) x = 0
  | 0, x => sorkin_third hc a x
  | k + 1, x => by
    rw [mixedDiff_succ, sorkin_hierarchy hc a k, sorkin_hierarchy hc a k, add_neg]

/-- The identity is additive. -/
theorem additive_id : Additive (fun x : Shell q => x) := fun _ _ => rfl

/-- 22:C8 — `I₂` is generically nonzero: with `c` the identity and the paths `a = b = 1`, `I₂ = 2 ≠ 0` on every
shell `q > 2`. -/
theorem sorkin_second_witness (h2 : 2 < q) :
    mixedDiff (fun _ => (1 : Shell q)) (weight fun x => x) 2 0 ≠ 0 := by
  rw [sorkin_second additive_id]
  show (1 : Shell q) * 1 + 1 * 1 ≠ 0
  rw [mul_one, ← two_eq]
  exact ofNat_ne_zero (by decide) h2

/-! ## The Hadamard layers and the splitting depth -/

/-- `ofNat` of a power is the power of `ofNat`. -/
theorem ofNat_pow (a : Nat) : ∀ m, (ofNat (a ^ m) : Shell q) = ofNat a ^ m
  | 0 => rfl
  | m + 1 => by rw [Nat.pow_succ, ← ofNat_mul, ofNat_pow a m, pow_succ]

/-- One balanced layer squared: `(1 + i)² = 2i` for a quarter-turn `i² = −1`. -/
theorem hadamard_sq {i : Shell q} (hi : i * i = -1) : (1 + i) * (1 + i) = 2 * i := by
  have e : (1 + i) * (1 + i) = 1 + (i + i) + i * i :=
    Shell.Frame.RE.sound (Shell.Frame.look [i])
      (.mul (.add .one (.var 0)) (.add .one (.var 0)))
      (.add (.add .one (.add (.var 0) (.var 0))) (.mul (.var 0) (.var 0)))
      (by decide +kernel)
  rw [e, hi, add_assoc, add_comm (i + i), ← add_assoc, add_neg, zero_add, two_eq, right_distrib, one_mul]

/-- 22:C14, 22:P5 — `2m` balanced layers give the amplitude `(1 + i)^{2m} = 2^m i^m`. -/
theorem hadamard_even {i : Shell q} (hi : i * i = -1) (m : Nat) : (1 + i) ^ (2 * m) = ofNat (2 ^ m) * i ^ m := by
  rw [pow_mul, pow_two, hadamard_sq hi, mul_pow, ofNat_pow]; rfl

/-- 22:C14 — `2m + 1` balanced layers give the amplitude `(1 + i)^{2m+1} = 2^m i^m (1 + i)`. -/
theorem hadamard_odd {i : Shell q} (hi : i * i = -1) (m : Nat) :
    (1 + i) ^ (2 * m + 1) = ofNat (2 ^ m) * i ^ m * (1 + i) := by
  rw [pow_succ, hadamard_even hi]

/-- The minimal tally norm after `k` balanced layers: `T(k) = 2^{k + [k odd]}`, that is `2^k` for even `k` and
`2^{k+1}` for odd `k`. -/
def tallyNorm (k : Nat) : Nat := 2 ^ (k + k % 2)

/-- 22:C14, 22:P5 — the tally norm is monotone in the depth. -/
theorem tally_norm_mono {k k' : Nat} (h : k ≤ k') : tallyNorm k ≤ tallyNorm k' := by
  unfold tallyNorm
  refine Nat.pow_le_pow_right (by decide) ?_
  match Nat.eq_or_lt_of_le h with
  | .inl e => rw [e]; exact Nat.le_refl _
  | .inr hlt =>
    have h1 : k % 2 ≤ 1 := Nat.le_of_lt_succ (Nat.mod_lt k (by decide))
    calc k + k % 2 ≤ k + 1 := Nat.add_le_add_left h1 k
      _ ≤ k' := hlt
      _ ≤ k' + k' % 2 := Nat.le_add_right k' _

/-- 22:C14, 22:P5 — **the ceiling on the worked carrier** `Ω = 641`: the largest depth with `T(k) < Ω` is `k* = 8` for the
unit core (`T(8) = 256`, `T(9) = 1024`), and with the Bell core `d = 8` it is `6` (`8 T(6) = 512`, `8 T(7) = 2048`). -/
theorem ceiling_641 : (∀ k, tallyNorm k < 641 ↔ k ≤ 8) ∧ (∀ k, 8 * tallyNorm k < 641 ↔ k ≤ 6) := by
  have t8 : tallyNorm 8 = 256 := by decide
  have t9 : tallyNorm 9 = 1024 := by decide
  have t6 : tallyNorm 6 = 64 := by decide
  have t7 : tallyNorm 7 = 256 := by decide
  constructor
  · intro k
    constructor
    · intro h
      match Nat.lt_or_ge 8 k with
      | .inl hlt =>
        have := tally_norm_mono (Nat.succ_le_of_lt hlt)
        rw [t9] at this
        exact absurd (Nat.lt_of_le_of_lt this h) (by decide)
      | .inr hge => exact hge
    · intro h
      have := tally_norm_mono h
      rw [t8] at this
      exact Nat.lt_of_le_of_lt this (by decide)
  · intro k
    constructor
    · intro h
      match Nat.lt_or_ge 6 k with
      | .inl hlt =>
        have := Nat.mul_le_mul_left 8 (tally_norm_mono (Nat.succ_le_of_lt hlt))
        rw [t7] at this
        exact absurd (Nat.lt_of_le_of_lt this h) (by decide)
      | .inr hge => exact hge
    · intro h
      have := Nat.mul_le_mul_left 8 (tally_norm_mono h)
      rw [t6] at this
      exact Nat.lt_of_le_of_lt this (by decide)

end FRC.Interference
