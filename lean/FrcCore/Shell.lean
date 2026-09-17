import FrcCore.Nat

/-!
# FrcCore.Shell — the residues of a shell, from first principles

`Shell p` is the set of residues mod `p`, carried by their canonical representatives `val < p` — no
quotient type, so no `Quot.sound`; every identity below is an identity of representatives, decided by
`Nat` arithmetic. The operations reduce by `%`, so `decide` computes on any concrete shell through the
kernel's accelerated `Nat` arithmetic, and every theorem is checked to depend on no axiom.

The ring laws are derived from `FrcCore.Nat`'s division algorithm (`mod_unique`); negation is
characterised by `add_neg : a + -a = 0`, and everything about `-` follows from the uniqueness of
additive inverses (`neg_unique`), never from `Nat` subtraction.
-/

namespace FRC

/-- A residue mod `p`: its representative and the bound. -/
structure Shell (p : Nat) where
  val : Nat
  lt : val < p

/-- `Pos p`: the modulus is positive. Instances for literals `n + 1` are found automatically. -/
class Pos (p : Nat) : Prop where
  pos : 0 < p

instance (n : Nat) : Pos (n + 1) := ⟨Nat.zero_lt_succ n⟩

namespace Shell

variable {p : Nat}

theorem ext {a b : Shell p} (h : a.val = b.val) : a = b := by
  cases a; cases b; cases h; rfl

theorem val_injective {a b : Shell p} (h : a = b) : a.val = b.val := by cases h; rfl

instance : DecidableEq (Shell p) := fun a b =>
  if h : a.val = b.val then isTrue (ext h) else isFalse (fun e => h (val_injective e))

section ops
variable [Pos p]

/-- The residue of a natural number. -/
def ofNat (n : Nat) : Shell p := ⟨n % p, Nat.mod_lt n Pos.pos⟩

instance (n : Nat) : OfNat (Shell p) n := ⟨ofNat n⟩
instance : Add (Shell p) := ⟨fun a b => ofNat (a.val + b.val)⟩
instance : Mul (Shell p) := ⟨fun a b => ofNat (a.val * b.val)⟩
instance : Neg (Shell p) := ⟨fun a => ofNat (p - a.val)⟩

/-- Powers by structural recursion (`a ^ 0 = 1`, `a ^ (n+1) = a ^ n * a`). -/
def pow (a : Shell p) : Nat → Shell p
  | 0 => 1
  | n + 1 => pow a n * a

instance : Pow (Shell p) Nat := ⟨pow⟩

theorem hp : 0 < p := Pos.pos

@[simp] theorem val_ofNat (n : Nat) : (ofNat n : Shell p).val = n % p := rfl
theorem val_add (a b : Shell p) : (a + b).val = (a.val + b.val) % p := rfl
theorem val_mul (a b : Shell p) : (a * b).val = (a.val * b.val) % p := rfl
theorem val_neg (a : Shell p) : (-a).val = (p - a.val) % p := rfl
theorem val_lit (n : Nat) : (OfNat.ofNat n : Shell p).val = n % p := rfl
theorem val_zero : (0 : Shell p).val = 0 := rfl
theorem val_one : (1 : Shell p).val = 1 % p := rfl
theorem pow_zero (a : Shell p) : a ^ 0 = 1 := rfl
theorem pow_succ (a : Shell p) (n : Nat) : a ^ (n + 1) = a ^ n * a := rfl

theorem ofNat_val (a : Shell p) : ofNat a.val = a :=
  ext (FRC.Nat.mod_eq_of_lt a.lt)

theorem ofNat_mod (n : Nat) : (ofNat (n % p) : Shell p) = ofNat n :=
  ext (FRC.Nat.mod_mod n p hp)

/-! ### The additive laws -/

theorem add_comm (a b : Shell p) : a + b = b + a :=
  ext (by rw [val_add, val_add, Nat.add_comm])

theorem add_assoc (a b c : Shell p) : a + b + c = a + (b + c) :=
  ext (by
    rw [val_add, val_add, val_add, val_add, FRC.Nat.mod_add_mod _ _ _ hp, FRC.Nat.add_mod_mod _ _ _ hp,
      Nat.add_assoc])

theorem zero_add (a : Shell p) : 0 + a = a :=
  ext (by rw [val_add, val_zero, Nat.zero_add]; exact FRC.Nat.mod_eq_of_lt a.lt)

theorem add_zero (a : Shell p) : a + 0 = a := by rw [add_comm]; exact zero_add a

theorem add_left_comm (a b c : Shell p) : a + (b + c) = b + (a + c) := by
  rw [← add_assoc, add_comm a b, add_assoc]

theorem add_add_add_comm (a b c d : Shell p) : a + b + (c + d) = a + c + (b + d) := by
  rw [add_assoc, add_assoc, add_left_comm b]

/-! ### The multiplicative laws -/

theorem mul_comm (a b : Shell p) : a * b = b * a :=
  ext (by rw [val_mul, val_mul, Nat.mul_comm])

theorem mul_assoc (a b c : Shell p) : a * b * c = a * (b * c) :=
  ext (by
    rw [val_mul, val_mul, val_mul, val_mul, FRC.Nat.mod_mul_mod _ _ _ hp, FRC.Nat.mul_mod_mod _ _ _ hp,
      FRC.Nat.mul_assoc])

theorem one_mul (a : Shell p) : 1 * a = a :=
  ext (by rw [val_mul, val_one, FRC.Nat.mod_mul_mod _ _ _ hp, Nat.one_mul]; exact FRC.Nat.mod_eq_of_lt a.lt)

theorem mul_one (a : Shell p) : a * 1 = a := by rw [mul_comm]; exact one_mul a

theorem zero_mul (a : Shell p) : 0 * a = 0 :=
  ext (by rw [val_mul, val_zero, Nat.zero_mul]; rfl)

theorem mul_zero (a : Shell p) : a * 0 = 0 := by rw [mul_comm]; exact zero_mul a

theorem mul_left_comm (a b c : Shell p) : a * (b * c) = b * (a * c) := by
  rw [← mul_assoc, mul_comm a b, mul_assoc]

theorem left_distrib (a b c : Shell p) : a * (b + c) = a * b + a * c :=
  ext (by
    rw [val_mul, val_add, val_add, val_mul, val_mul, FRC.Nat.mul_mod_mod _ _ _ hp,
      FRC.Nat.add_mod _ _ _ hp, FRC.Nat.mod_mod _ _ hp, FRC.Nat.mod_mod _ _ hp, ← FRC.Nat.add_mod _ _ _ hp,
      Nat.left_distrib])

theorem right_distrib (a b c : Shell p) : (a + b) * c = a * c + b * c := by
  rw [mul_comm, left_distrib, mul_comm c a, mul_comm c b]

/-! ### Negation, characterised by `add_neg` -/

theorem add_neg (a : Shell p) : a + -a = 0 :=
  ext (by
    rw [val_add, val_neg, FRC.Nat.add_mod_mod _ _ _ hp, FRC.Nat.add_sub_of_le (Nat.le_of_lt a.lt),
      FRC.Nat.mod_self p hp]; rfl)

theorem neg_add (a : Shell p) : -a + a = 0 := by rw [add_comm]; exact add_neg a

/-- Additive inverses are unique. -/
theorem neg_unique {a x y : Shell p} (hx : a + x = 0) (hy : a + y = 0) : x = y := by
  calc x = x + 0 := (add_zero x).symm
    _ = x + (a + y) := by rw [hy]
    _ = (x + a) + y := (add_assoc _ _ _).symm
    _ = (a + x) + y := by rw [add_comm x a]
    _ = 0 + y := by rw [hx]
    _ = y := zero_add y

theorem neg_eq_of_add_eq_zero {a b : Shell p} (h : a + b = 0) : -a = b :=
  neg_unique (add_neg a) h

theorem neg_neg (a : Shell p) : - -a = a :=
  neg_eq_of_add_eq_zero (neg_add a)

theorem neg_zero : (-0 : Shell p) = 0 :=
  neg_eq_of_add_eq_zero (add_zero 0)

theorem neg_mul (a b : Shell p) : -(a * b) = -a * b :=
  neg_eq_of_add_eq_zero (by rw [← right_distrib, add_neg, zero_mul])

theorem mul_neg (a b : Shell p) : -(a * b) = a * -b := by
  rw [mul_comm, neg_mul, mul_comm]

theorem neg_mul_neg (a b : Shell p) : -a * -b = a * b := by
  rw [← neg_mul, ← mul_neg, neg_neg]

theorem neg_add_rev (a b : Shell p) : -(a + b) = -a + -b :=
  neg_eq_of_add_eq_zero (by
    rw [add_assoc, add_left_comm b, ← add_assoc, add_neg, zero_add, add_neg])

theorem add_right_cancel {a b c : Shell p} (h : a + c = b + c) : a = b := by
  have : a + c + -c = b + c + -c := by rw [h]
  rw [add_assoc, add_neg, add_zero, add_assoc, add_neg, add_zero] at this
  exact this

theorem eq_neg_of_add_eq_zero {a b : Shell p} (h : a + b = 0) : a = -b := by
  rw [← neg_neg a, neg_eq_of_add_eq_zero h]

theorem neg_one_mul (a : Shell p) : -1 * a = -a := by rw [← neg_mul, one_mul]

/-! ### Powers -/

theorem pow_one (a : Shell p) : a ^ 1 = a := by rw [pow_succ, pow_zero, one_mul]

theorem one_pow (n : Nat) : (1 : Shell p) ^ n = 1 := by
  induction n with
  | zero => rfl
  | succ n ih => rw [pow_succ, ih, mul_one]

theorem pow_add (a : Shell p) (m n : Nat) : a ^ (m + n) = a ^ m * a ^ n := by
  induction n with
  | zero => rw [Nat.add_zero, pow_zero, mul_one]
  | succ n ih => rw [Nat.add_succ, pow_succ, ih, pow_succ, mul_assoc]

theorem pow_mul (a : Shell p) (m n : Nat) : a ^ (m * n) = (a ^ m) ^ n := by
  induction n with
  | zero => rw [Nat.mul_zero, pow_zero, pow_zero]
  | succ n ih => rw [Nat.mul_succ, pow_add, ih, pow_succ]

theorem pow_mul_comm (a : Shell p) (m n : Nat) : (a ^ m) ^ n = (a ^ n) ^ m := by
  rw [← pow_mul, Nat.mul_comm, pow_mul]

theorem mul_pow (a b : Shell p) (n : Nat) : (a * b) ^ n = a ^ n * b ^ n := by
  induction n with
  | zero => rw [pow_zero, pow_zero, pow_zero, mul_one]
  | succ n ih =>
    rw [pow_succ, pow_succ, pow_succ, ih, mul_assoc, mul_assoc, mul_left_comm (b ^ n) a b]

theorem pow_two (a : Shell p) : a ^ 2 = a * a := by rw [pow_succ, pow_one]

theorem neg_pow_two (a : Shell p) : (-a) ^ 2 = a ^ 2 := by rw [pow_two, pow_two, neg_mul_neg]

/-- `(-1)^n` by the parity of `n`. -/
theorem neg_one_pow (n : Nat) : (-1 : Shell p) ^ n = if n % 2 = 0 then 1 else -1 := by
  induction n with
  | zero => rfl
  | succ n ih =>
    rw [pow_succ, ih]
    exact match Nat.decEq (n % 2) 0 with
      | .isTrue h => by
          rw [ite_eq_left h, one_mul]
          have : (n + 1) % 2 = 1 := by
            rw [← FRC.Nat.mod_add_mod _ _ _ (Nat.zero_lt_succ 1), h]
          rw [ite_eq_right (by rw [this]; exact fun e => Nat.noConfusion e)]
      | .isFalse h => by
          rw [ite_eq_right h, neg_mul_neg, one_mul]
          have h1 : n % 2 = 1 := by
            have := Nat.mod_lt n (Nat.zero_lt_succ 1)
            exact match n % 2, this, h with
              | 0, _, h => absurd rfl h
              | 1, _, _ => rfl
              | k + 2, hk, _ => absurd hk (Nat.not_lt_of_le (Nat.le_add_left 2 k))
          have : (n + 1) % 2 = 0 := by
            rw [← FRC.Nat.mod_add_mod _ _ _ (Nat.zero_lt_succ 1), h1]
          rw [ite_eq_left this]

end ops

end Shell
end FRC
