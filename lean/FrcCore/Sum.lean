import FrcCore.Frame

/-!
# FrcCore.Sum — finite sums on the shell, the geometric sum, the Fourier inversion

Sums over `l < n` are defined by structural recursion (`sumRange f (n+1) = sumRange f n + f n`): no
`Finset`, no quotient, no function extensionality — a congruence lemma (`sum_congr`) replaces `funext`.
The geometric sum gives the principal-root identity (2:F1, Prop. 6.1 of 2-geometry) and the entrywise
inversion of the shell Fourier matrix `W k j = g^{jk}`: `Σ_l W k l · (−g^{−lj}) = [k = j]` (2:F3,
Prop. 6.3; 6:B5 in matrix form). No axioms.
-/

namespace FRC
namespace Shell

variable {p : Nat} [Pos p]

/-- `sumRange f n = f 0 + f 1 + ⋯ + f (n−1)`. -/
def sumRange (f : Nat → Shell p) : Nat → Shell p
  | 0 => 0
  | n + 1 => sumRange f n + f n

theorem sumRange_zero (f : Nat → Shell p) : sumRange f 0 = 0 := rfl
theorem sumRange_succ (f : Nat → Shell p) (n : Nat) : sumRange f (n + 1) = sumRange f n + f n := rfl

theorem sum_congr {f h : Nat → Shell p} (n : Nat) (e : ∀ l, l < n → f l = h l) :
    sumRange f n = sumRange h n := by
  induction n with
  | zero => rfl
  | succ n ih =>
    rw [sumRange_succ, sumRange_succ, ih (fun l hl => e l (Nat.lt_succ_of_lt hl)),
      e n (Nat.lt_succ_self n)]

theorem sum_add (f h : Nat → Shell p) (n : Nat) :
    sumRange (fun l => f l + h l) n = sumRange f n + sumRange h n := by
  induction n with
  | zero => rw [sumRange_zero, sumRange_zero, sumRange_zero, add_zero]
  | succ n ih =>
    rw [sumRange_succ, sumRange_succ, sumRange_succ, ih, add_add_add_comm]

theorem sum_mul_right (f : Nat → Shell p) (c : Shell p) (n : Nat) :
    sumRange (fun l => f l * c) n = sumRange f n * c := by
  induction n with
  | zero => rw [sumRange_zero, sumRange_zero, zero_mul]
  | succ n ih => rw [sumRange_succ, sumRange_succ, ih, right_distrib]

theorem sum_mul_left (f : Nat → Shell p) (c : Shell p) (n : Nat) :
    sumRange (fun l => c * f l) n = c * sumRange f n := by
  induction n with
  | zero => rw [sumRange_zero, sumRange_zero, mul_zero]
  | succ n ih => rw [sumRange_succ, sumRange_succ, ih, left_distrib]

theorem sum_neg (f : Nat → Shell p) (n : Nat) : sumRange (fun l => -(f l)) n = -(sumRange f n) := by
  induction n with
  | zero => rw [sumRange_zero, sumRange_zero, neg_zero]
  | succ n ih => rw [sumRange_succ, sumRange_succ, ih, neg_add_rev]

theorem sum_const (c : Shell p) (n : Nat) : sumRange (fun _ => c) n = ofNat n * c := by
  induction n with
  | zero => rw [sumRange_zero]; exact (zero_mul c).symm
  | succ n ih =>
    rw [sumRange_succ, ih]
    have : (ofNat (n + 1) : Shell p) = ofNat n + 1 := ext (by
      rw [val_ofNat, val_add, val_ofNat, val_one, FRC.Nat.mod_add_mod _ _ _ hp, FRC.Nat.add_mod_mod _ _ _ hp])
    rw [this, right_distrib, one_mul]

/-- The telescoping geometric sum: `(Σ_{l<n} x^l)·(x − 1) = x^n − 1`. -/
theorem geom_sum_mul (x : Shell p) (n : Nat) :
    sumRange (fun l => x ^ l) n * (x + -1) = x ^ n + -1 := by
  induction n with
  | zero => rw [sumRange_zero, zero_mul, pow_zero, add_neg]
  | succ n ih =>
    rw [sumRange_succ, right_distrib, ih, left_distrib, ← mul_neg, mul_one, ← pow_succ]
    rw [add_add_add_comm, add_comm (x ^ n) (x ^ (n + 1)), add_comm (-1) (-(x ^ n)), add_assoc,
      ← add_assoc (x ^ n), add_neg, zero_add]

namespace Frame
variable {κ : Nat} {g : Shell p}

/-- `Σ_{l<n} x^l = 0` when `x^n = 1` and `x ≠ 1` (the field has no zero divisors). -/
theorem geom_sum_eq_zero (F : Frame p κ g) {x : Shell p} (n : Nat) (hn : x ^ n = 1) (hx : x ≠ 1) :
    sumRange (fun l => x ^ l) n = 0 := by
  have h := geom_sum_mul x n
  rw [hn, add_neg] at h
  match F.mul_eq_zero h with
  | .inl e => exact e
  | .inr e => exact absurd (by
      calc x = x + 0 := (add_zero x).symm
        _ = x + (-1 + 1) := by rw [neg_add]
        _ = (x + -1) + 1 := (add_assoc _ _ _).symm
        _ = 1 := by rw [e, zero_add]) hx

theorem ofNat_n (F : Frame p κ g) : (ofNat (p - 1) : Shell p) = -1 := by
  apply ext
  rw [val_ofNat, val_neg, val_one, FRC.Nat.mod_eq_of_lt F.one_lt_p,
    FRC.Nat.mod_eq_of_lt (Nat.sub_lt Pos.pos (Nat.zero_lt_succ 0))]

/-- 2:F1 (Prop. 6.1) — `g` is a principal root of unity: `g^n = 1`, `Σ_{j<n} (g^k)^j = 0` for
`0 < k < n`, and `n = p − 1` reads as `−1` in the shell. -/
theorem principal_root (F : Frame p κ g) (k : Nat) (hk0 : 0 < k) (hk : k < p - 1) :
    g ^ (p - 1) = 1 ∧ sumRange (fun j => (g ^ k) ^ j) (p - 1) = 0 ∧ (ofNat (p - 1) : Shell p) = -1 := by
  refine ⟨F.pow_n, ?_, F.ofNat_n⟩
  apply F.geom_sum_eq_zero
  · rw [pow_mul_comm, F.pow_n, one_pow]
  · exact F.prim.2 k hk hk0

/-- `g^{k + (n − j)} = 1` exactly when `k = j`, for `k, j < n`. -/
theorem pow_shift_eq_one_iff (F : Frame p κ g) {k j : Nat} (hk : k < p - 1) (hj : j < p - 1) :
    g ^ (k + (p - 1 - j)) = 1 ↔ k = j := by
  have hn := F.n_pos
  have hjn : p - 1 - j + j = p - 1 := FRC.Nat.sub_add_cancel (Nat.le_of_lt hj)
  constructor
  · intro h
    have hm := F.mod_eq_zero_of_pow_eq_one h
    match Nat.lt_or_ge k j with
    | .inl hlt =>
      have hlt' : k + (p - 1 - j) < p - 1 := by
        have := Nat.add_lt_add_right hlt (p - 1 - j)
        rw [Nat.add_comm j, hjn] at this
        exact this
      rw [FRC.Nat.mod_eq_of_lt hlt'] at hm
      have hpos : 0 < p - 1 - j := by
        refine Nat.lt_of_add_lt_add_right (n := j) ?_
        rw [Nat.zero_add, hjn]; exact hj
      exact absurd hm (Nat.ne_of_gt (Nat.lt_of_lt_of_le hpos (Nat.le_add_left _ _)))
    | .inr hge =>
      have e : k + (p - 1 - j) = (p - 1) * 1 + (k - j) := by
        rw [Nat.mul_one]
        calc k + (p - 1 - j) = (j + (k - j)) + (p - 1 - j) := by rw [FRC.Nat.add_sub_of_le hge]
          _ = (p - 1 - j + j) + (k - j) := by
              rw [Nat.add_comm j (k - j), Nat.add_assoc, Nat.add_comm (k - j), Nat.add_comm j (p - 1 - j)]
          _ = p - 1 + (k - j) := by rw [hjn]
      rw [e, FRC.Nat.add_mul_mod_self_left _ _ _ hn,
        FRC.Nat.mod_eq_of_lt (Nat.lt_of_le_of_lt (Nat.sub_le k j) hk)] at hm
      have := FRC.Nat.add_sub_of_le hge
      rw [hm, Nat.add_zero] at this
      exact this.symm
  · intro e
    rw [e, FRC.Nat.add_sub_of_le (Nat.le_of_lt hj), F.pow_n]

/-- 2:F3 (Prop. 6.3), 6:B5 — the inversion of the shell Fourier matrix, entrywise: with
`W k j = g^{jk}` and `W' l j = −g^{(n−j)l}` (`= −g^{−lj}`), `Σ_{l<n} W k l · W' l j = [k = j]`. -/
theorem dft_inverse (F : Frame p κ g) {k j : Nat} (hk : k < p - 1) (hj : j < p - 1) :
    sumRange (fun l => g ^ (l * k) * -(g ^ ((p - 1 - j) * l))) (p - 1) = if k = j then 1 else 0 := by
  have hsum : sumRange (fun l => g ^ (l * k) * -(g ^ ((p - 1 - j) * l))) (p - 1)
      = -(sumRange (fun l => (g ^ (k + (p - 1 - j))) ^ l) (p - 1)) := by
    rw [← sum_neg]
    apply sum_congr
    intro l _
    rw [← mul_neg, ← pow_add, ← pow_mul, Nat.mul_comm l k, ← FRC.Nat.add_mul]
  rw [hsum]
  exact match Nat.decEq k j with
    | .isTrue e => by
        rw [if_pos e]
        have h1 : g ^ (k + (p - 1 - j)) = 1 := (F.pow_shift_eq_one_iff hk hj).2 e
        have : sumRange (fun l => (g ^ (k + (p - 1 - j))) ^ l) (p - 1) = ofNat (p - 1) * 1 := by
          rw [← sum_const]; apply sum_congr; intro l _; rw [h1, one_pow]
        rw [this, F.ofNat_n, mul_one, neg_neg]
    | .isFalse e => by
        rw [if_neg e]
        have h1 : g ^ (k + (p - 1 - j)) ≠ 1 := fun h => e ((F.pow_shift_eq_one_iff hk hj).1 h)
        rw [F.geom_sum_eq_zero _ (by rw [pow_mul_comm, F.pow_n, one_pow]) h1, neg_zero]

/-- `g^{k + j} = 1` exactly when `(k + j) % n = 0`, i.e. `j` is the reversal `−k` of `k` (`k, j < n`). -/
theorem pow_add_eq_one_iff (F : Frame p κ g) (k j : Nat) : g ^ (k + j) = 1 ↔ (k + j) % (p - 1) = 0 :=
  ⟨F.mod_eq_zero_of_pow_eq_one, F.pow_eq_one_of_mod⟩

/-- 6:B5 (the shell Fourier matrix squares to the reversal, entrywise): with `W k j = g^{jk}` and
`J k j = [(k + j) % n = 0]`, `Σ_{l<n} W k l · W l j = −J k j` on every shell (`n = p − 1 ≡ −1`). -/
theorem W_sq (F : Frame p κ g) (k j : Nat) :
    sumRange (fun l => g ^ (l * k) * g ^ (j * l)) (p - 1)
      = -(if (k + j) % (p - 1) = 0 then 1 else 0) := by
  have hsum : sumRange (fun l => g ^ (l * k) * g ^ (j * l)) (p - 1)
      = sumRange (fun l => (g ^ (k + j)) ^ l) (p - 1) := by
    apply sum_congr; intro l _
    rw [← pow_add, ← pow_mul, Nat.mul_comm l k, ← FRC.Nat.add_mul]
  rw [hsum]
  exact match Nat.decEq ((k + j) % (p - 1)) 0 with
    | .isTrue e => by
        rw [if_pos e]
        have h1 : g ^ (k + j) = 1 := F.pow_eq_one_of_mod e
        have : sumRange (fun l => (g ^ (k + j)) ^ l) (p - 1) = ofNat (p - 1) * 1 := by
          rw [← sum_const]; apply sum_congr; intro l _; rw [h1, one_pow]
        rw [this, F.ofNat_n, mul_one]
    | .isFalse e => by
        rw [if_neg e, neg_zero]
        exact F.geom_sum_eq_zero _ (by rw [pow_mul_comm, F.pow_n, one_pow]) (fun h => e (F.mod_eq_zero_of_pow_eq_one h))

end Frame

end Shell
end FRC
