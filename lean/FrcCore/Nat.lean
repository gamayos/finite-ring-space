/-!
# FrcCore.Nat — the arithmetic the shells stand on, from first principles

No Mathlib, no `simp`, no `omega`: every theorem here is checked by `#print axioms` to depend on no
axiom at all. Lean's own core library proves most of these with `propext` for convenience (see
`reports/lean-axioms-probe-20260917/core_probe.log`); they are re-derived here by induction from the
axiom-free primitives (`Nat.rec`, `Nat.add_comm`, `Nat.mul_comm`, `Nat.left_distrib`, `Nat.mod_lt`,
`Nat.le.dest`, `ite_eq_left`, `ite_eq_right`, `Decidable.em`).

The division algorithm is obtained from the definition of `Nat.mod` in `Init.Prelude` (the wrapper
around `Nat.modCore`, itself a fuel recursion): `mod_eq_of_lt`, `mod_eq_sub_mod`, `mod_spec`
(`x = p·q + x % p`) and `mod_unique` (the remainder is determined by any such decomposition). Everything
about residues mod `p` follows from those four.
-/

namespace FRC.Nat

/-! ## Cancellation and subtraction -/

theorem add_left_cancel {a b c : Nat} (h : a + b = a + c) : b = c := by
  induction a with
  | zero => rw [Nat.zero_add, Nat.zero_add] at h; exact h
  | succ a ih =>
    apply ih
    rw [Nat.succ_add, Nat.succ_add] at h
    exact Nat.succ.inj h

theorem add_right_cancel {a b c : Nat} (h : a + c = b + c) : a = b :=
  add_left_cancel (a := c) (by rw [Nat.add_comm c a, Nat.add_comm c b]; exact h)

theorem add_sub_cancel (n m : Nat) : n + m - m = n := by
  induction m with
  | zero => rfl
  | succ m ih => rw [Nat.add_succ, Nat.succ_sub_succ]; exact ih

theorem add_sub_cancel_left (n m : Nat) : n + m - n = m := by
  rw [Nat.add_comm]; exact add_sub_cancel m n

theorem sub_add_cancel {n m : Nat} (h : m ≤ n) : n - m + m = n := by
  match Nat.le.dest h with
  | ⟨k, hk⟩ => rw [← hk, add_sub_cancel_left, Nat.add_comm]

theorem sub_add_self_eq_zero (m : Nat) : ∀ k, m - (m + k) = 0
  | 0 => Nat.sub_self m
  | k + 1 => by show Nat.pred (m - (m + k)) = 0; rw [sub_add_self_eq_zero m k]; rfl

theorem sub_eq_zero_of_le {m n : Nat} (h : m ≤ n) : m - n = 0 :=
  match Nat.le.dest h with
  | ⟨k, hk⟩ => by rw [← hk]; exact sub_add_self_eq_zero m k

theorem add_sub_of_le {n m : Nat} (h : m ≤ n) : m + (n - m) = n := by
  rw [Nat.add_comm]; exact sub_add_cancel h

theorem sub_lt_of_lt_add {x y z : Nat} (h : x < y + z) (hy : y ≤ x) : x - y < z := by
  refine Nat.lt_of_add_lt_add_right (n := y) ?_
  rw [sub_add_cancel hy, Nat.add_comm z y]
  exact h

theorem le_of_add_le_add_left {a b c : Nat} (h : a + b ≤ a + c) : b ≤ c := by
  induction a with
  | zero => rw [Nat.zero_add, Nat.zero_add] at h; exact h
  | succ a ih => apply ih; rw [Nat.succ_add, Nat.succ_add] at h; exact Nat.le_of_succ_le_succ h

theorem le_of_add_le_add_right {a b c : Nat} (h : b + a ≤ c + a) : b ≤ c :=
  le_of_add_le_add_left (a := a) (by rw [Nat.add_comm a b, Nat.add_comm a c]; exact h)

theorem sub_le_of_le_add {a b c : Nat} (h : a ≤ c + b) : a - b ≤ c := by
  have := Nat.sub_le_sub_right h b
  rw [add_sub_cancel] at this; exact this

theorem le_add_of_sub_le {a b c : Nat} (hb : b ≤ a) (h : a - b ≤ c) : a ≤ c + b := by
  have := Nat.add_le_add_right h b
  rw [sub_add_cancel hb] at this; exact this

theorem le_sub_of_add_le {a b c : Nat} (h : c + b ≤ a) : c ≤ a - b := by
  have := Nat.sub_le_sub_right h b
  rw [add_sub_cancel] at this; exact this

theorem succ_ne_zero (n : Nat) : n + 1 ≠ 0 := fun h => Nat.noConfusion h

theorem pos_of_lt {a b : Nat} (h : a < b) : 0 < b :=
  Nat.lt_of_le_of_lt (Nat.zero_le a) h

/-! ## Multiplication -/

theorem mul_assoc (a b c : Nat) : a * b * c = a * (b * c) := by
  induction c with
  | zero => rfl
  | succ c ih => rw [Nat.mul_succ, Nat.mul_succ, ih, Nat.left_distrib]

theorem add_mul (a b c : Nat) : (a + b) * c = a * c + b * c := by
  rw [Nat.mul_comm, Nat.left_distrib, Nat.mul_comm c a, Nat.mul_comm c b]

theorem add_add_add_comm (a b c d : Nat) : a + b + (c + d) = a + c + (b + d) := by
  rw [Nat.add_assoc, Nat.add_assoc, Nat.add_left_comm b]

theorem mul_left_comm (a b c : Nat) : a * (b * c) = b * (a * c) := by
  rw [← mul_assoc, Nat.mul_comm a b, mul_assoc]

theorem mul_lt_mul_of_lt_of_pos {a b c : Nat} (h : a < b) (hc : 0 < c) : a * c < b * c := by
  rw [Nat.mul_comm a c, Nat.mul_comm b c]
  exact Nat.mul_lt_mul_of_pos_left h hc

/-! ## The division algorithm, from the definition of `Nat.mod` -/

section mod

/-- The fuel of `Nat.modCore.go` does not matter once it exceeds the dividend. -/
theorem modCore_go_fuel {y : Nat} (hy : 0 < y) : ∀ (f1 f2 x : Nat) (h1 : x < f1) (h2 : x < f2),
    Nat.modCore.go y hy f1 x h1 = Nat.modCore.go y hy f2 x h2 := by
  intro f1
  induction f1 with
  | zero => intro f2 x h1; exact absurd h1 (Nat.not_lt_zero x)
  | succ f1 ih =>
    intro f2 x h1 h2
    cases f2 with
    | zero => exact absurd h2 (Nat.not_lt_zero x)
    | succ f2 =>
      show (if h : y ≤ x then Nat.modCore.go y hy f1 (x - y) _ else x)
          = (if h : y ≤ x then Nat.modCore.go y hy f2 (x - y) _ else x)
      exact match Nat.decLe y x with
        | .isTrue h => by rw [dite_eq_left h, dite_eq_left h]; exact ih f2 (x - y) _ _
        | .isFalse h => by rw [dite_eq_right h, dite_eq_right h]

theorem modCore_eq' (x y : Nat) (hy : 0 < y) :
    Nat.modCore x y = if y ≤ x then Nat.modCore (x - y) y else x := by
  unfold Nat.modCore
  rw [dite_eq_left hy]
  show (if h : y ≤ x then Nat.modCore.go y hy x (x - y) _ else x) = _
  exact match Nat.decLe y x with
    | .isTrue h => by
        rw [dite_eq_left h, ite_eq_left h, dite_eq_left hy]
        exact modCore_go_fuel hy x (x - y + 1) (x - y) _ _
    | .isFalse h => by rw [dite_eq_right h, ite_eq_right h]

theorem modCore_eq_mod' (n m : Nat) (hm : 0 < m) : Nat.modCore n m = n % m := by
  cases n with
  | zero =>
    show Nat.modCore 0 m = 0
    rw [modCore_eq' 0 m hm, ite_eq_right (Nat.not_le_of_lt hm)]
  | succ n =>
    show Nat.modCore (n + 1) m = ite (m ≤ n + 1) (Nat.modCore (n + 1) m) (n + 1)
    exact match Nat.decLe m (n + 1) with
      | .isTrue h => by rw [ite_eq_left h]
      | .isFalse h => by rw [ite_eq_right h, modCore_eq' _ _ hm, ite_eq_right h]

theorem mod_eq_of_lt {x y : Nat} (h : x < y) : x % y = x := by
  cases x with
  | zero => rfl
  | succ n =>
    show ite (y ≤ n + 1) (Nat.modCore (n + 1) y) (n + 1) = n + 1
    rw [ite_eq_right (Nat.not_le_of_lt h)]

theorem mod_eq_sub_mod {x y : Nat} (hy : 0 < y) (h : y ≤ x) : x % y = (x - y) % y := by
  rw [← modCore_eq_mod' x y hy, modCore_eq' x y hy, ite_eq_left h, modCore_eq_mod' _ _ hy]

/-- The division algorithm: `x = p·q + x % p` for some `q`. -/
theorem mod_spec (p : Nat) (hp : 0 < p) : ∀ x : Nat, ∃ q, x = p * q + x % p := by
  intro x
  induction x using Nat.strongRecOn with
  | _ x ih =>
    exact match Nat.decLe p x with
      | .isTrue h =>
          match ih (x - p) (Nat.sub_lt (Nat.lt_of_lt_of_le hp h) hp) with
          | ⟨q, hq⟩ => ⟨q + 1, by
              rw [mod_eq_sub_mod hp h, Nat.mul_succ, Nat.add_assoc, Nat.add_comm p, ← Nat.add_assoc,
                ← hq, sub_add_cancel h]⟩
      | .isFalse h => ⟨0, by rw [mod_eq_of_lt (Nat.lt_of_not_le h), Nat.mul_zero, Nat.zero_add]⟩

/-- Uniqueness of the decomposition: the quotients agree. -/
theorem quot_unique {p q q' r r' : Nat} (hr : r < p) (hr' : r' < p) (h : p * q + r = p * q' + r') :
    q = q' := by
  have key : ∀ {q q' r r' : Nat}, r < p → r' < p → p * q + r = p * q' + r' → ¬ q < q' := by
    intro q q' r r' hr hr' h hlt
    have h1 : p * (q + 1) ≤ p * q' := Nat.mul_le_mul_left p hlt
    have h2 : p * q + r < p * q + p := Nat.add_lt_add_left hr _
    rw [Nat.mul_succ] at h1
    have h3 : p * q + r < p * q' + r' := Nat.lt_of_lt_of_le h2 (Nat.le_trans h1 (Nat.le_add_right _ _))
    rw [h] at h3
    exact Nat.lt_irrefl _ h3
  exact match Nat.lt_or_ge q q' with
    | .inl hlt => absurd hlt (key hr hr' h)
    | .inr hge => match Nat.lt_or_ge q' q with
      | .inl hlt => absurd hlt (key hr' hr h.symm)
      | .inr hge' => Nat.le_antisymm hge' hge

/-- The remainder is determined: if `x = p·q + r` with `r < p`, then `r = x % p`. -/
theorem mod_unique {p x q r : Nat} (hr : r < p) (h : x = p * q + r) : x % p = r := by
  have hp : 0 < p := pos_of_lt hr
  match mod_spec p hp x with
  | ⟨q', hq'⟩ =>
    have hqq : q' = q := quot_unique (Nat.mod_lt x hp) hr (by rw [← hq', ← h])
    rw [hqq] at hq'
    rw [h] at hq'
    rw [h]
    exact (add_left_cancel hq').symm

theorem mod_mod (x p : Nat) (hp : 0 < p) : x % p % p = x % p :=
  mod_eq_of_lt (Nat.mod_lt x hp)

theorem add_mod (a b p : Nat) (hp : 0 < p) : (a + b) % p = (a % p + b % p) % p := by
  match mod_spec p hp a, mod_spec p hp b, mod_spec p hp (a % p + b % p) with
  | ⟨qa, ha⟩, ⟨qb, hb⟩, ⟨qc, hc⟩ =>
    apply mod_unique (q := qa + qb + qc) (Nat.mod_lt _ hp)
    rw [Nat.left_distrib, Nat.left_distrib, Nat.add_assoc, ← hc]
    rw [Nat.add_assoc, Nat.add_left_comm (p * qb), ← Nat.add_assoc, ← ha, ← hb]

theorem add_mul_mod_self_left (x k p : Nat) (hp : 0 < p) : (p * k + x) % p = x % p := by
  match mod_spec p hp x with
  | ⟨q, hq⟩ =>
    apply mod_unique (q := k + q) (Nat.mod_lt x hp)
    rw [Nat.left_distrib, Nat.add_assoc, ← hq]

theorem mul_mod_left' (a b p : Nat) (hp : 0 < p) : (a * b) % p = (a % p * b) % p := by
  match mod_spec p hp a with
  | ⟨qa, ha⟩ =>
    have e : a * b = p * (qa * b) + a % p * b := by
      rw [← mul_assoc, ← add_mul, ← ha]
    rw [e, add_mul_mod_self_left _ _ _ hp]

theorem mul_mod (a b p : Nat) (hp : 0 < p) : (a * b) % p = (a % p * (b % p)) % p := by
  rw [mul_mod_left' a b p hp, Nat.mul_comm (a % p) b, mul_mod_left' b (a % p) p hp,
    Nat.mul_comm (b % p) (a % p)]

theorem mod_self (p : Nat) (hp : 0 < p) : p % p = 0 :=
  mod_unique hp (by rw [Nat.mul_one, Nat.add_zero])

theorem zero_mod (p : Nat) : 0 % p = 0 := rfl

theorem mod_add_mod (a b p : Nat) (hp : 0 < p) : (a % p + b) % p = (a + b) % p := by
  rw [add_mod a b p hp, add_mod (a % p) b p hp, mod_mod _ _ hp]

theorem add_mod_mod (a b p : Nat) (hp : 0 < p) : (a + b % p) % p = (a + b) % p := by
  rw [add_mod a b p hp, add_mod a (b % p) p hp, mod_mod _ _ hp]

theorem mod_mul_mod (a b p : Nat) (hp : 0 < p) : (a % p * b) % p = (a * b) % p :=
  (mul_mod_left' a b p hp).symm

theorem mul_mod_mod (a b p : Nat) (hp : 0 < p) : (a * (b % p)) % p = (a * b) % p := by
  rw [mul_mod a (b % p) p hp, mod_mod _ _ hp, ← mul_mod a b p hp]

theorem mod_lt' (x : Nat) {p : Nat} (hp : 0 < p) : x % p < p := Nat.mod_lt x hp

end mod

/-! ## Powers -/

theorem pow_succ' (a n : Nat) : a ^ (n + 1) = a ^ n * a := rfl

theorem pow_add (a m n : Nat) : a ^ (m + n) = a ^ m * a ^ n := by
  induction n with
  | zero => rw [Nat.add_zero, Nat.pow_zero, Nat.mul_one]
  | succ n ih => rw [Nat.add_succ, Nat.pow_succ, ih, Nat.pow_succ, mul_assoc]

theorem pow_mul (a m n : Nat) : a ^ (m * n) = (a ^ m) ^ n := by
  induction n with
  | zero => rw [Nat.mul_zero, Nat.pow_zero, Nat.pow_zero]
  | succ n ih => rw [Nat.mul_succ, pow_add, ih, Nat.pow_succ]

theorem pos_pow_of_pos {a : Nat} (n : Nat) (h : 0 < a) : 0 < a ^ n := Nat.pow_pos h

end FRC.Nat
