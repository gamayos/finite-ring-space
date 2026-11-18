/-!
# The ring of operators up to a congruence — no axioms

An `OpRing` is a type with `+`, `*`, `−`, `0`, `1` and a congruence `≈` (an equivalence respected by the three
operations) satisfying the ring laws up to `≈`. The congruence lets matrices read as functions of two indices form a ring
without function extensionality: two matrices are congruent when their entries agree on the range. This file holds the
class, the lemmas every ring has (cancellation, the negative, the products with `0` and `−1`), and the commuting, the
central and the anticommuting elements. It imports nothing. The operator layer of 8-dirac (`Theme/Operator.lean`) and the
chirality of 27-fields (`Theme/Chirality.lean`) are built on it. No axioms.
-/

namespace FRC.Dirac.Operator

/-! ## The ring up to a congruence -/

/-- A ring of operators up to a congruence `eq`: the equivalence, its compatibility with the operations, and the
ring laws (commutative addition, associative multiplication, the unit, the two distributive laws), all up to `eq`. -/
class OpRing (R : Type) [Add R] [Mul R] [Neg R] [OfNat R 0] [OfNat R 1] where
  eq : R → R → Prop
  refl : ∀ x, eq x x
  symm : ∀ {x y}, eq x y → eq y x
  trans : ∀ {x y z}, eq x y → eq y z → eq x z
  add_congr : ∀ {x x' y y'}, eq x x' → eq y y' → eq (x + y) (x' + y')
  mul_congr : ∀ {x x' y y'}, eq x x' → eq y y' → eq (x * y) (x' * y')
  neg_congr : ∀ {x x'}, eq x x' → eq (-x) (-x')
  add_comm : ∀ x y, eq (x + y) (y + x)
  add_assoc : ∀ x y z, eq (x + y + z) (x + (y + z))
  zero_add : ∀ x, eq (0 + x) x
  add_neg : ∀ x, eq (x + -x) 0
  mul_assoc : ∀ x y z, eq (x * y * z) (x * (y * z))
  one_mul : ∀ x, eq (1 * x) x
  mul_one : ∀ x, eq (x * 1) x
  left_distrib : ∀ x y z, eq (x * (y + z)) (x * y + x * z)
  right_distrib : ∀ x y z, eq ((x + y) * z) (x * z + y * z)

variable {R : Type} [Add R] [Mul R] [Neg R] [OfNat R 0] [OfNat R 1] [OpRing R]

instance : HasEquiv R := ⟨OpRing.eq⟩

instance : Trans (α := R) (β := R) (γ := R) (· ≈ ·) (· ≈ ·) (· ≈ ·) := ⟨OpRing.trans⟩

open OpRing (add_congr mul_congr neg_congr add_comm add_assoc zero_add add_neg mul_assoc one_mul mul_one left_distrib right_distrib)

theorem eq_refl (x : R) : x ≈ x := OpRing.refl x
theorem eq_symm {x y : R} (h : x ≈ y) : y ≈ x := OpRing.symm h
theorem eq_trans {x y z : R} (h : x ≈ y) (h' : y ≈ z) : x ≈ z := OpRing.trans h h'
theorem eq_of_eq {x y : R} (h : x = y) : x ≈ y := h ▸ OpRing.refl x

theorem add_congr_left {x x' : R} (y : R) (h : x ≈ x') : x + y ≈ x' + y := add_congr h (eq_refl y)
theorem add_congr_right (x : R) {y y' : R} (h : y ≈ y') : x + y ≈ x + y' := add_congr (eq_refl x) h
theorem mul_congr_left {x x' : R} (y : R) (h : x ≈ x') : x * y ≈ x' * y := mul_congr h (eq_refl y)
theorem mul_congr_right (x : R) {y y' : R} (h : y ≈ y') : x * y ≈ x * y' := mul_congr (eq_refl x) h

theorem add_zero (x : R) : x + 0 ≈ x := eq_trans (add_comm x 0) (zero_add x)
theorem neg_add (x : R) : -x + x ≈ 0 := eq_trans (add_comm (-x) x) (add_neg x)
theorem add_left_comm (x y z : R) : x + (y + z) ≈ y + (x + z) :=
  calc x + (y + z) ≈ x + y + z := eq_symm (add_assoc x y z)
    _ ≈ y + x + z := add_congr_left z (add_comm x y)
    _ ≈ y + (x + z) := add_assoc y x z
theorem add_add_add_comm (a b c d : R) : a + b + (c + d) ≈ a + c + (b + d) :=
  calc a + b + (c + d) ≈ a + (b + (c + d)) := add_assoc a b (c + d)
    _ ≈ a + (c + (b + d)) := add_congr_right a (add_left_comm b c d)
    _ ≈ a + c + (b + d) := eq_symm (add_assoc a c (b + d))

/-- Cancellation on the left: `x + y ≈ x + z → y ≈ z`. -/
theorem add_left_cancel {x y z : R} (h : x + y ≈ x + z) : y ≈ z :=
  calc y ≈ 0 + y := eq_symm (zero_add y)
    _ ≈ -x + x + y := add_congr_left y (eq_symm (neg_add x))
    _ ≈ -x + (x + y) := add_assoc _ _ _
    _ ≈ -x + (x + z) := add_congr_right _ h
    _ ≈ -x + x + z := eq_symm (add_assoc _ _ _)
    _ ≈ 0 + z := add_congr_left z (neg_add x)
    _ ≈ z := zero_add z

theorem add_right_cancel {x y z : R} (h : y + x ≈ z + x) : y ≈ z :=
  add_left_cancel (eq_trans (add_comm x y) (eq_trans h (add_comm z x)))

theorem neg_eq_of_add_eq_zero {x y : R} (h : x + y ≈ 0) : -x ≈ y :=
  add_left_cancel (eq_trans (add_neg x) (eq_symm h))

theorem neg_neg (x : R) : - -x ≈ x := neg_eq_of_add_eq_zero (neg_add x)
theorem neg_zero : (-0 : R) ≈ 0 := neg_eq_of_add_eq_zero (zero_add 0)
theorem neg_add_rev (x y : R) : -(x + y) ≈ -x + -y :=
  neg_eq_of_add_eq_zero <|
    calc x + y + (-x + -y) ≈ x + -x + (y + -y) := add_add_add_comm x y (-x) (-y)
      _ ≈ 0 + 0 := add_congr (add_neg x) (add_neg y)
      _ ≈ 0 := zero_add 0

theorem mul_zero (x : R) : x * 0 ≈ 0 :=
  add_left_cancel (x := x * 0) <|
    calc x * 0 + x * 0 ≈ x * (0 + 0) := eq_symm (left_distrib x 0 0)
      _ ≈ x * 0 := mul_congr_right x (zero_add 0)
      _ ≈ x * 0 + 0 := eq_symm (add_zero _)
theorem zero_mul (x : R) : 0 * x ≈ 0 :=
  add_left_cancel (x := 0 * x) <|
    calc 0 * x + 0 * x ≈ (0 + 0) * x := eq_symm (right_distrib 0 0 x)
      _ ≈ 0 * x := mul_congr_left x (zero_add 0)
      _ ≈ 0 * x + 0 := eq_symm (add_zero _)
theorem neg_mul (x y : R) : -(x * y) ≈ -x * y :=
  neg_eq_of_add_eq_zero <|
    calc x * y + -x * y ≈ (x + -x) * y := eq_symm (right_distrib x (-x) y)
      _ ≈ 0 * y := mul_congr_left y (add_neg x)
      _ ≈ 0 := zero_mul y
theorem mul_neg (x y : R) : -(x * y) ≈ x * -y :=
  neg_eq_of_add_eq_zero <|
    calc x * y + x * -y ≈ x * (y + -y) := eq_symm (left_distrib x y (-y))
      _ ≈ x * 0 := mul_congr_right x (add_neg y)
      _ ≈ 0 := mul_zero x
theorem neg_one_mul (x : R) : (-1 : R) * x ≈ -x := eq_trans (eq_symm (neg_mul 1 x)) (neg_congr (one_mul x))
theorem mul_neg_one (x : R) : x * (-1 : R) ≈ -x := eq_trans (eq_symm (mul_neg x 1)) (neg_congr (mul_one x))
theorem neg_mul_neg (x y : R) : -x * -y ≈ x * y :=
  calc -x * -y ≈ -(x * -y) := eq_symm (neg_mul x (-y))
    _ ≈ - -(x * y) := neg_congr (eq_symm (mul_neg x y))
    _ ≈ x * y := neg_neg _
theorem sub_self (x : R) : x + -x ≈ 0 := add_neg x
theorem eq_of_sub_eq_zero {x y : R} (h : x + -y ≈ 0) : x ≈ y :=
  calc x ≈ x + 0 := eq_symm (add_zero x)
    _ ≈ x + (-y + y) := add_congr_right x (eq_symm (neg_add y))
    _ ≈ x + -y + y := eq_symm (add_assoc _ _ _)
    _ ≈ 0 + y := add_congr_left y h
    _ ≈ y := zero_add y
theorem sub_eq_zero_of_eq {x y : R} (h : x ≈ y) : x + -y ≈ 0 :=
  eq_trans (add_congr_left (-y) h) (add_neg y)
/-- `x − (y + z) = (x − y) − z`. -/
theorem sub_add (x y z : R) : x + -(y + z) ≈ x + -y + -z :=
  calc x + -(y + z) ≈ x + (-y + -z) := add_congr_right x (neg_add_rev y z)
    _ ≈ x + -y + -z := eq_symm (add_assoc _ _ _)
/-- `(x + y) − y = x`. -/
theorem add_sub_cancel (x y : R) : x + y + -y ≈ x :=
  calc x + y + -y ≈ x + (y + -y) := add_assoc _ _ _
    _ ≈ x + 0 := add_congr_right x (add_neg y)
    _ ≈ x := add_zero x

/-! ## Commuting and central elements -/

/-- `x` and `y` commute. -/
def Comm (x y : R) : Prop := x * y ≈ y * x
/-- `c` commutes with everything. -/
def Central (c : R) : Prop := ∀ x, c * x ≈ x * c

theorem Comm.symm {x y : R} (h : Comm x y) : Comm y x := OpRing.symm h
theorem Central.comm {c : R} (hc : Central c) (x : R) : Comm c x := hc x
theorem Comm.mul_left {x y z : R} (hx : Comm x z) (hy : Comm y z) : Comm (x * y) z :=
  calc x * y * z ≈ x * (y * z) := mul_assoc _ _ _
    _ ≈ x * (z * y) := mul_congr_right x hy
    _ ≈ x * z * y := eq_symm (mul_assoc _ _ _)
    _ ≈ z * x * y := mul_congr_left y hx
    _ ≈ z * (x * y) := mul_assoc _ _ _
theorem Comm.mul_right {x y z : R} (hx : Comm z x) (hy : Comm z y) : Comm z (x * y) :=
  (Comm.mul_left hx.symm hy.symm).symm
theorem Comm.add_left {x y z : R} (hx : Comm x z) (hy : Comm y z) : Comm (x + y) z :=
  calc (x + y) * z ≈ x * z + y * z := right_distrib _ _ _
    _ ≈ z * x + z * y := add_congr hx hy
    _ ≈ z * (x + y) := eq_symm (left_distrib _ _ _)
theorem Comm.add_right {x y z : R} (hx : Comm z x) (hy : Comm z y) : Comm z (x + y) :=
  (Comm.add_left hx.symm hy.symm).symm
theorem Comm.neg_left {x z : R} (hx : Comm x z) : Comm (-x) z :=
  calc -x * z ≈ -(x * z) := eq_symm (neg_mul x z)
    _ ≈ -(z * x) := neg_congr hx
    _ ≈ z * -x := mul_neg z x
theorem Comm.neg_right {x z : R} (hx : Comm z x) : Comm z (-x) := (Comm.neg_left hx.symm).symm
theorem Comm.one_left (x : R) : Comm 1 x := eq_trans (one_mul x) (eq_symm (mul_one x))
theorem Comm.zero_left (x : R) : Comm 0 x := eq_trans (zero_mul x) (eq_symm (mul_zero x))
theorem Comm.refl (x : R) : Comm x x := OpRing.refl _
theorem Comm.congr {x x' y y' : R} (hx : x ≈ x') (hy : y ≈ y') (h : Comm x y) : Comm x' y' :=
  eq_trans (mul_congr (eq_symm hx) (eq_symm hy)) (eq_trans h (mul_congr hy hx))
theorem Central.mul {c d : R} (hc : Central c) (hd : Central d) : Central (c * d) :=
  fun x => Comm.mul_left (hc x) (hd x)
theorem Central.add {c d : R} (hc : Central c) (hd : Central d) : Central (c + d) :=
  fun x => Comm.add_left (hc x) (hd x)
theorem Central.neg {c : R} (hc : Central c) : Central (-c) := fun x => Comm.neg_left (hc x)
theorem Central.one : Central (1 : R) := Comm.one_left
theorem Central.zero : Central (0 : R) := Comm.zero_left
theorem Central.congr {c c' : R} (h : c ≈ c') (hc : Central c) : Central c' :=
  fun x => Comm.congr h (eq_refl x) (hc x)

/-! ## Anticommuting elements -/

/-- `A` and `B` anticommute. -/
def Anticomm (A B : R) : Prop := A * B + B * A ≈ 0

theorem Anticomm.symm {A B : R} (h : Anticomm A B) : Anticomm B A := eq_trans (add_comm _ _) h
end FRC.Dirac.Operator
