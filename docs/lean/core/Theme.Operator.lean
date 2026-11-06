import FrcCore.Orbit
import FrcCore.Theme.Quadratic

/-!
# The operator layer of 8-dirac — a ring of operators up to a congruence, no axioms

The fourth file of the dirac theme (5 November 2026, the core-proof programme, decision D2): the general form of the
operator rows. An `OpRing` is a type with `+`, `*`, `−`, `0`, `1` and a congruence `≈` (an equivalence respected by the
three operations) satisfying the ring laws up to `≈`. The congruence is what lets the matrices of the spinor file —
functions of two indices read below the dimension — form a ring without function extensionality: two matrices are
congruent when their entries agree on the range, and nothing here needs more. Every theorem of the layer is stated up to
`≈` and holds in every `OpRing`: the Cayley step of a symmetric operator at an admissible parameter is unitary (C4); a
nilpotent operator has the geometric series as the inverse of `1 − N`, so the static massive equation has only the zero
solution (X3, F7); the Cayley step of a nilpotent shift minus a mass is a unit congruent, modulo a nilpotent, to the
scalar phase (D10); a two-sided unit is injective and surjective (E3, E6); conjugation by a unit preserves the
anticommutator (D17); the square of a sum of pairwise anticommuting operators is the sum of the squares, so the Dirac
operator factorises, `(𝒟 − m)(𝒟 + m) = □_η − m²` (D3, D18); and in characteristic `p`, `t^p = 1` forces `(t − 1)^p = 0`,
the translations unipotent (F7), by the binomial theorem and `p ∣ C(p, k)` on the shell. No axioms.
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

/-! ## Powers -/

/-- `x ^ n` by structural recursion, `x ^ (n+1) = x ^ n * x`. -/
def opow (x : R) : Nat → R
  | 0 => 1
  | n + 1 => opow x n * x

omit [Add R] [Neg R] [OfNat R 0] [OpRing R] in
theorem opow_zero (x : R) : opow x 0 = 1 := rfl
omit [Add R] [Neg R] [OfNat R 0] [OpRing R] in
theorem opow_succ (x : R) (n : Nat) : opow x (n + 1) = opow x n * x := rfl
theorem opow_one (x : R) : opow x 1 ≈ x := one_mul x

theorem opow_congr {x x' : R} (h : x ≈ x') : ∀ n, opow x n ≈ opow x' n
  | 0 => eq_refl 1
  | n + 1 => mul_congr (opow_congr h n) h

theorem opow_comm {x y : R} (h : Comm x y) : ∀ n, Comm (opow x n) y
  | 0 => Comm.one_left y
  | n + 1 => Comm.mul_left (opow_comm h n) h

theorem opow_self_comm (x : R) (n : Nat) : Comm (opow x n) x := opow_comm (Comm.refl x) n

theorem opow_add (x : R) (m : Nat) : ∀ n, opow x (m + n) ≈ opow x m * opow x n
  | 0 => eq_symm (mul_one _)
  | n + 1 =>
    calc opow x (m + n) * x ≈ opow x m * opow x n * x := mul_congr_left x (opow_add x m n)
      _ ≈ opow x m * (opow x n * x) := mul_assoc _ _ _

theorem opow_succ' (x : R) (n : Nat) : opow x (n + 1) ≈ x * opow x n :=
  calc opow x n * x ≈ x * opow x n := opow_self_comm x n

/-- `(x y)^n = x^n y^n` for commuting `x`, `y`. -/
theorem mul_opow {x y : R} (h : Comm x y) : ∀ n, opow (x * y) n ≈ opow x n * opow y n
  | 0 => eq_symm (one_mul 1)
  | n + 1 =>
    calc opow (x * y) n * (x * y) ≈ opow x n * opow y n * (x * y) := mul_congr_left _ (mul_opow h n)
      _ ≈ opow x n * (opow y n * (x * y)) := mul_assoc _ _ _
      _ ≈ opow x n * (opow y n * x * y) := mul_congr_right _ (eq_symm (mul_assoc _ _ _))
      _ ≈ opow x n * (x * opow y n * y) := mul_congr_right _ (mul_congr_left y (opow_comm h.symm n))
      _ ≈ opow x n * (x * (opow y n * y)) := mul_congr_right _ (mul_assoc _ _ _)
      _ ≈ opow x n * x * (opow y n * y) := eq_symm (mul_assoc _ _ _)

theorem opow_one_left : ∀ n, opow (1 : R) n ≈ 1
  | 0 => eq_refl 1
  | n + 1 => eq_trans (mul_one _) (opow_one_left n)

theorem opow_zero_of_zero : ∀ n, opow (0 : R) (n + 1) ≈ 0
  | _ => mul_zero _

/-- A power past a vanishing power vanishes. -/
theorem opow_eq_zero_of {x : R} {k : Nat} (h : opow x k ≈ 0) (j : Nat) : opow x (k + j) ≈ 0 :=
  calc opow x (k + j) ≈ opow x k * opow x j := opow_add x k j
    _ ≈ 0 * opow x j := mul_congr_left _ h
    _ ≈ 0 := zero_mul _

theorem Central.opow {c : R} (hc : Central c) (n : Nat) : Central (opow c n) := fun x => opow_comm (hc x) n

/-! ## Natural multiples -/

/-- `n • x = x + ⋯ + x` (`n` terms). -/
def nsmul : Nat → R → R
  | 0, _ => 0
  | n + 1, x => nsmul n x + x

omit [Mul R] [Neg R] [OfNat R 1] [OpRing R] in
theorem nsmul_zero (x : R) : nsmul 0 x = 0 := rfl
omit [Mul R] [Neg R] [OfNat R 1] [OpRing R] in
theorem nsmul_succ (n : Nat) (x : R) : nsmul (n + 1) x = nsmul n x + x := rfl

theorem nsmul_congr {x x' : R} (h : x ≈ x') : ∀ n, nsmul n x ≈ nsmul n x'
  | 0 => eq_refl 0
  | n + 1 => add_congr (nsmul_congr h n) h

theorem nsmul_add (x y : R) : ∀ n, nsmul n (x + y) ≈ nsmul n x + nsmul n y
  | 0 => eq_symm (zero_add 0)
  | n + 1 =>
    calc nsmul n (x + y) + (x + y) ≈ nsmul n x + nsmul n y + (x + y) := add_congr_left _ (nsmul_add x y n)
      _ ≈ nsmul n x + x + (nsmul n y + y) := add_add_add_comm _ _ _ _

theorem add_nsmul (m : Nat) (x : R) : ∀ n, nsmul (m + n) x ≈ nsmul m x + nsmul n x
  | 0 => eq_symm (add_zero _)
  | n + 1 =>
    calc nsmul (m + n) x + x ≈ nsmul m x + nsmul n x + x := add_congr_left x (add_nsmul m x n)
      _ ≈ nsmul m x + (nsmul n x + x) := add_assoc _ _ _

theorem nsmul_mul_left (x y : R) : ∀ n, nsmul n x * y ≈ nsmul n (x * y)
  | 0 => zero_mul y
  | n + 1 =>
    calc (nsmul n x + x) * y ≈ nsmul n x * y + x * y := right_distrib _ _ _
      _ ≈ nsmul n (x * y) + x * y := add_congr_left _ (nsmul_mul_left x y n)

theorem mul_nsmul_right (x y : R) : ∀ n, x * nsmul n y ≈ nsmul n (x * y)
  | 0 => mul_zero x
  | n + 1 =>
    calc x * (nsmul n y + y) ≈ x * nsmul n y + x * y := left_distrib _ _ _
      _ ≈ nsmul n (x * y) + x * y := add_congr_left _ (mul_nsmul_right x y n)

theorem mul_nsmul (m : Nat) (x : R) : ∀ n, nsmul (m * n) x ≈ nsmul m (nsmul n x)
  | 0 => by rw [Nat.mul_zero]; exact eq_symm (nsmul_zero_right m)
  | n + 1 =>
    calc nsmul (m * n + m) x ≈ nsmul (m * n) x + nsmul m x := add_nsmul _ x m
      _ ≈ nsmul m (nsmul n x) + nsmul m x := add_congr_left _ (mul_nsmul m x n)
      _ ≈ nsmul m (nsmul n x + x) := eq_symm (nsmul_add _ _ m)
where
  nsmul_zero_right : ∀ m, nsmul m (0 : R) ≈ 0
    | 0 => eq_refl 0
    | m + 1 => eq_trans (add_zero _) (nsmul_zero_right m)

theorem nsmul_zero_right : ∀ m, nsmul m (0 : R) ≈ 0 := mul_nsmul.nsmul_zero_right

theorem nsmul_eq_mul_one (x : R) (n : Nat) : nsmul n x ≈ nsmul n 1 * x :=
  eq_symm (eq_trans (nsmul_mul_left 1 x n) (nsmul_congr (one_mul x) n))

/-- A natural multiple of a vanishing element vanishes. -/
theorem nsmul_of_eq_zero {x : R} (h : x ≈ 0) (n : Nat) : nsmul n x ≈ 0 :=
  eq_trans (nsmul_congr h n) (nsmul_zero_right n)

theorem nsmul_comm_of {x y : R} (h : Comm x y) (n : Nat) : Comm (nsmul n x) y :=
  calc nsmul n x * y ≈ nsmul n (x * y) := nsmul_mul_left x y n
    _ ≈ nsmul n (y * x) := nsmul_congr h n
    _ ≈ y * nsmul n x := eq_symm (mul_nsmul_right y x n)

/-! ## Sums -/

/-- `Σ_{j<n} f j` in the ring. -/
def osum (f : Nat → R) : Nat → R
  | 0 => 0
  | n + 1 => osum f n + f n

omit [Mul R] [Neg R] [OfNat R 1] [OpRing R] in
theorem osum_zero (f : Nat → R) : osum f 0 = 0 := rfl
omit [Mul R] [Neg R] [OfNat R 1] [OpRing R] in
theorem osum_succ (f : Nat → R) (n : Nat) : osum f (n + 1) = osum f n + f n := rfl

theorem osum_congr {f h : Nat → R} : ∀ n, (∀ j, j < n → f j ≈ h j) → osum f n ≈ osum h n
  | 0, _ => eq_refl 0
  | n + 1, e => add_congr (osum_congr n fun j hj => e j (Nat.lt_succ_of_lt hj)) (e n (Nat.lt_succ_self n))

theorem osum_add (f h : Nat → R) : ∀ n, osum (fun j => f j + h j) n ≈ osum f n + osum h n
  | 0 => eq_symm (zero_add 0)
  | n + 1 =>
    calc osum (fun j => f j + h j) n + (f n + h n) ≈ osum f n + osum h n + (f n + h n) :=
          add_congr_left _ (osum_add f h n)
      _ ≈ osum f n + f n + (osum h n + h n) := add_add_add_comm _ _ _ _

theorem osum_mul_left (c : R) (f : Nat → R) : ∀ n, c * osum f n ≈ osum (fun j => c * f j) n
  | 0 => mul_zero c
  | n + 1 =>
    calc c * (osum f n + f n) ≈ c * osum f n + c * f n := left_distrib _ _ _
      _ ≈ osum (fun j => c * f j) n + c * f n := add_congr_left _ (osum_mul_left c f n)

theorem osum_mul_right (c : R) (f : Nat → R) : ∀ n, osum f n * c ≈ osum (fun j => f j * c) n
  | 0 => zero_mul c
  | n + 1 =>
    calc (osum f n + f n) * c ≈ osum f n * c + f n * c := right_distrib _ _ _
      _ ≈ osum (fun j => f j * c) n + f n * c := add_congr_left _ (osum_mul_right c f n)

theorem osum_eq_zero {f : Nat → R} : ∀ n, (∀ j, j < n → f j ≈ 0) → osum f n ≈ 0
  | 0, _ => eq_refl 0
  | n + 1, h =>
    calc osum f n + f n ≈ 0 + 0 := add_congr (osum_eq_zero n fun j hj => h j (Nat.lt_succ_of_lt hj)) (h n (Nat.lt_succ_self n))
      _ ≈ 0 := zero_add 0

theorem osum_neg (f : Nat → R) : ∀ n, osum (fun j => -(f j)) n ≈ -(osum f n)
  | 0 => eq_symm neg_zero
  | n + 1 =>
    calc osum (fun j => -(f j)) n + -(f n) ≈ -(osum f n) + -(f n) := add_congr_left _ (osum_neg f n)
      _ ≈ -(osum f n + f n) := eq_symm (neg_add_rev _ _)

theorem osum_comm {f : Nat → R} {y : R} : ∀ n, (∀ j, j < n → Comm (f j) y) → Comm (osum f n) y
  | 0, _ => Comm.zero_left y
  | n + 1, h => Comm.add_left (osum_comm n fun j hj => h j (Nat.lt_succ_of_lt hj)) (h n (Nat.lt_succ_self n))

/-! ## Units (8:E3, 8:E6) -/

/-- `v` is a two-sided inverse of `u`. -/
def Inverse (u v : R) : Prop := u * v ≈ 1 ∧ v * u ≈ 1

theorem Inverse.symm {u v : R} (h : Inverse u v) : Inverse v u := ⟨h.2, h.1⟩

theorem Inverse.congr {u u' v v' : R} (hu : u ≈ u') (hv : v ≈ v') (h : Inverse u v) : Inverse u' v' :=
  ⟨eq_trans (mul_congr (eq_symm hu) (eq_symm hv)) h.1, eq_trans (mul_congr (eq_symm hv) (eq_symm hu)) h.2⟩

theorem Inverse.one : Inverse (1 : R) 1 := ⟨one_mul 1, one_mul 1⟩

theorem Inverse.mul {u v u' v' : R} (h : Inverse u v) (h' : Inverse u' v') : Inverse (u * u') (v' * v) := by
  refine ⟨?_, ?_⟩
  · calc u * u' * (v' * v) ≈ u * (u' * v' * v) := eq_trans (mul_assoc _ _ _) (mul_congr_right u (eq_symm (mul_assoc _ _ _)))
      _ ≈ u * (1 * v) := mul_congr_right u (mul_congr_left v h'.1)
      _ ≈ u * v := mul_congr_right u (one_mul v)
      _ ≈ 1 := h.1
  · calc v' * v * (u * u') ≈ v' * (v * u * u') := eq_trans (mul_assoc _ _ _) (mul_congr_right v' (eq_symm (mul_assoc _ _ _)))
      _ ≈ v' * (1 * u') := mul_congr_right v' (mul_congr_left u' h.2)
      _ ≈ v' * u' := mul_congr_right v' (one_mul u')
      _ ≈ 1 := h'.2

/-- The inverse of an element commuting with `x` commutes with `x`. -/
theorem Inverse.comm_of_comm {u v x : R} (h : Inverse u v) (hx : Comm u x) : Comm v x :=
  calc v * x ≈ v * x * 1 := eq_symm (mul_one _)
    _ ≈ v * x * (u * v) := mul_congr_right _ (eq_symm h.1)
    _ ≈ v * (x * u) * v := eq_trans (eq_symm (mul_assoc _ _ _)) (mul_congr_left v (mul_assoc _ _ _))
    _ ≈ v * (u * x) * v := mul_congr_left v (mul_congr_right v (eq_symm hx))
    _ ≈ v * u * x * v := mul_congr_left v (eq_symm (mul_assoc _ _ _))
    _ ≈ 1 * x * v := mul_congr_left v (mul_congr_left x h.2)
    _ ≈ x * v := mul_congr_left v (one_mul x)

theorem Inverse.central {u v : R} (h : Inverse u v) (hu : Central u) : Central v :=
  fun x => h.comm_of_comm (hu x)

/-- 8:E3, 8:E6 — a unit is injective: `u x ≈ u y → x ≈ y` when `u` has a left inverse. -/
theorem unit_injective {u v : R} (h : v * u ≈ 1) {x y : R} (e : u * x ≈ u * y) : x ≈ y :=
  calc x ≈ 1 * x := eq_symm (one_mul x)
    _ ≈ v * u * x := mul_congr_left x (eq_symm h)
    _ ≈ v * (u * x) := mul_assoc _ _ _
    _ ≈ v * (u * y) := mul_congr_right v e
    _ ≈ v * u * y := eq_symm (mul_assoc _ _ _)
    _ ≈ 1 * y := mul_congr_left y h
    _ ≈ y := one_mul y

/-- 8:E3, 8:E6 — a unit is surjective: every `y` is `u x` when `u` has a right inverse. -/
theorem unit_surjective {u v : R} (h : u * v ≈ 1) (y : R) : ∃ x, u * x ≈ y :=
  ⟨v * y, calc u * (v * y) ≈ u * v * y := eq_symm (mul_assoc _ _ _)
    _ ≈ 1 * y := mul_congr_left y h
    _ ≈ y := one_mul y⟩

/-- A unit has trivial kernel: `u x ≈ 0 → x ≈ 0`. -/
theorem unit_kernel {u v : R} (h : v * u ≈ 1) {x : R} (e : u * x ≈ 0) : x ≈ 0 :=
  unit_injective h (eq_trans e (eq_symm (mul_zero u)))

/-! ## The geometric series and nilpotent operators (8:X3, 8:F7) -/

/-- `1 + N + ⋯ + N^{k−1}`. -/
def geom (N : R) (k : Nat) : R := osum (fun j => opow N j) k

theorem geom_comm {N x : R} (h : Comm N x) (k : Nat) : Comm (geom N k) x :=
  osum_comm k fun j _ => opow_comm h j

theorem geom_congr {N N' : R} (h : N ≈ N') (k : Nat) : geom N k ≈ geom N' k :=
  osum_congr k fun j _ => opow_congr h j

/-- `(1 − N)(1 + N + ⋯ + N^{k−1}) = 1 − N^k`, the telescoping product. -/
theorem one_sub_mul_geom (N : R) : ∀ k, (1 + -N) * geom N k ≈ 1 + -(opow N k)
  | 0 => eq_trans (mul_zero _) (eq_symm (add_neg 1))
  | k + 1 =>
    calc (1 + -N) * (geom N k + opow N k) ≈ (1 + -N) * geom N k + (1 + -N) * opow N k := left_distrib _ _ _
      _ ≈ 1 + -(opow N k) + (opow N k + -(opow N (k + 1))) := by
          refine add_congr (one_sub_mul_geom N k) ?_
          calc (1 + -N) * opow N k ≈ 1 * opow N k + -N * opow N k := right_distrib _ _ _
            _ ≈ opow N k + -(N * opow N k) := add_congr (one_mul _) (eq_symm (neg_mul _ _))
            _ ≈ opow N k + -(opow N (k + 1)) := add_congr_right _ (neg_congr (eq_symm (opow_succ' N k)))
      _ ≈ 1 + (-(opow N k) + opow N k) + -(opow N (k + 1)) :=
          eq_trans (eq_symm (add_assoc _ _ _)) (add_congr_left _ (add_assoc _ _ _))
      _ ≈ 1 + 0 + -(opow N (k + 1)) := add_congr_left _ (add_congr_right _ (neg_add _))
      _ ≈ 1 + -(opow N (k + 1)) := add_congr_left _ (add_zero 1)

theorem geom_mul_one_sub (N : R) (k : Nat) : geom N k * (1 + -N) ≈ 1 + -(opow N k) :=
  eq_trans (geom_comm (Comm.add_right (eq_symm (Comm.one_left N)) (Comm.neg_right (Comm.refl N))) k)
    (one_sub_mul_geom N k)

/-- 8:X3 — the series inverse: for a nilpotent `N` (`N^k ≈ 0`), `1 − N` is a unit with inverse the geometric series. -/
theorem series_inverse {N : R} {k : Nat} (h : opow N k ≈ 0) : Inverse (1 + -N) (geom N k) :=
  ⟨eq_trans (one_sub_mul_geom N k) (eq_trans (add_congr_right 1 (neg_congr h)) (eq_trans (add_congr_right 1 neg_zero) (add_zero 1))),
   eq_trans (geom_mul_one_sub N k) (eq_trans (add_congr_right 1 (neg_congr h)) (eq_trans (add_congr_right 1 neg_zero) (add_zero 1)))⟩

/-- `geom N (j + 1) ≈ 1 + N · geom N j`. -/
theorem geom_succ_left (N : R) : ∀ j, geom N (j + 1) ≈ 1 + N * geom N j
  | 0 => eq_trans (zero_add 1) (eq_symm (eq_trans (add_congr_right 1 (mul_zero N)) (add_zero 1)))
  | j + 1 =>
    calc geom N (j + 1) + opow N (j + 1) ≈ 1 + N * geom N j + N * opow N j :=
          add_congr (geom_succ_left N j) (opow_succ' N j)
      _ ≈ 1 + (N * geom N j + N * opow N j) := add_assoc _ _ _
      _ ≈ 1 + N * (geom N j + opow N j) := add_congr_right 1 (eq_symm (left_distrib _ _ _))

/-- 8:X3, 8:F7 — the static massive equation has only the zero solution: with `N` nilpotent and the mass `m` a
unit of central inverse (`m m' ≈ 1`, `m'` central), `N − m` is a unit — its inverse `geom (m' N) k · (−m')` — so
`(N − m) ψ ≈ 0` forces `ψ ≈ 0`. -/
theorem static_inverse {N m m' : R} {k : Nat} (h : opow N k ≈ 0) (hm' : Central m')
    (hmm : m * m' ≈ 1) : Inverse (N + -m) (geom (m' * N) k * -m') := by
  have hX : opow (m' * N) k ≈ 0 :=
    calc opow (m' * N) k ≈ opow m' k * opow N k := mul_opow (hm' N) k
      _ ≈ opow m' k * 0 := mul_congr_right _ h
      _ ≈ 0 := mul_zero _
  have hG := series_inverse hX
  have hm'm : m' * m ≈ 1 := eq_trans (hm' m) hmm
  have hfac : N + -m ≈ -m * (1 + -(m' * N)) :=
    calc N + -m ≈ -m + N := add_comm _ _
      _ ≈ -m + 1 * N := add_congr_right _ (eq_symm (one_mul N))
      _ ≈ -m + m * m' * N := add_congr_right _ (mul_congr_left N (eq_symm hmm))
      _ ≈ -m + m * (m' * N) := add_congr_right _ (mul_assoc _ _ _)
      _ ≈ -m * 1 + -m * -(m' * N) := add_congr (eq_symm (mul_one _)) (eq_symm (neg_mul_neg _ _))
      _ ≈ -m * (1 + -(m' * N)) := eq_symm (left_distrib _ _ _)
  have hneg : Inverse (-m) (-m') := ⟨eq_trans (neg_mul_neg _ _) hmm, eq_trans (neg_mul_neg _ _) hm'm⟩
  exact (hneg.mul hG).congr (eq_symm hfac) (eq_refl _)

/-- 8:X3, 8:F7 — the static massive equation `(N − m) ψ ≈ 0` has only the zero solution, `N − m` being a unit. -/
theorem static_unique {N m m' : R} {k : Nat} (h : opow N k ≈ 0) (hm' : Central m')
    (hmm : m * m' ≈ 1) {ψ : R} (e : (N + -m) * ψ ≈ 0) : ψ ≈ 0 :=
  unit_kernel (static_inverse h hm' hmm).2 e

/-! ## The Cayley step (8:C4, 8:D10) -/

/-- An anti-automorphism of the ring up to the congruence — the adjoint `†`. -/
structure Adjoint (σ : R → R) : Prop where
  congr : ∀ {x y : R}, x ≈ y → σ x ≈ σ y
  mul : ∀ x y : R, σ (x * y) ≈ σ y * σ x
  add : ∀ x y : R, σ (x + y) ≈ σ x + σ y
  one : σ (1 : R) ≈ 1
  neg : ∀ x : R, σ (-x) ≈ -(σ x)

/-- The adjoint of `1 + a h` is `1 − a h` when `h` is symmetric and `a` central with `σ a ≈ −a`. -/
theorem Adjoint.one_add {σ : R → R} (hσ : Adjoint σ) {h a : R} (hh : σ h ≈ h) (ha : σ a ≈ -a) (hc : Central a) :
    σ (1 + a * h) ≈ 1 + -(a * h) :=
  calc σ (1 + a * h) ≈ σ 1 + σ (a * h) := hσ.add _ _
    _ ≈ 1 + σ h * σ a := add_congr hσ.one (hσ.mul _ _)
    _ ≈ 1 + h * -a := add_congr_right 1 (mul_congr hh ha)
    _ ≈ 1 + -(h * a) := add_congr_right 1 (eq_symm (mul_neg _ _))
    _ ≈ 1 + -(a * h) := add_congr_right 1 (neg_congr (eq_symm (hc h)))

theorem Adjoint.one_sub {σ : R → R} (hσ : Adjoint σ) {h a : R} (hh : σ h ≈ h) (ha : σ a ≈ -a) (hc : Central a) :
    σ (1 + -(a * h)) ≈ 1 + a * h :=
  calc σ (1 + -(a * h)) ≈ σ 1 + σ (-(a * h)) := hσ.add _ _
    _ ≈ 1 + -(σ (a * h)) := add_congr hσ.one (hσ.neg _)
    _ ≈ 1 + -(σ h * σ a) := add_congr_right 1 (neg_congr (hσ.mul _ _))
    _ ≈ 1 + -(h * -a) := add_congr_right 1 (neg_congr (mul_congr hh ha))
    _ ≈ 1 + - -(h * a) := add_congr_right 1 (neg_congr (eq_symm (mul_neg _ _)))
    _ ≈ 1 + h * a := add_congr_right 1 (neg_neg _)
    _ ≈ 1 + a * h := add_congr_right 1 (eq_symm (hc h))

/-- The adjoint of an inverse pair is an inverse pair. -/
theorem Adjoint.inverse {σ : R → R} (hσ : Adjoint σ) {u v : R} (h : Inverse u v) : Inverse (σ u) (σ v) :=
  ⟨eq_trans (eq_symm (hσ.mul v u)) (eq_trans (hσ.congr h.2) hσ.one),
   eq_trans (eq_symm (hσ.mul u v)) (eq_trans (hσ.congr h.1) hσ.one)⟩

/-- The twist of an adjoint by a unit: `τ a = X' σ(a) X` with `X X' ≈ 1`, `X' X ≈ 1` is an adjoint again — the
`X`-adjoint of the spinor form, for which the Cayley step preserves the `X`-form (8:D10). -/
theorem Adjoint.twist {σ : R → R} (hσ : Adjoint σ) {X X' : R} (hX : Inverse X X') :
    Adjoint (fun a => X' * σ a * X) where
  congr := fun h => mul_congr_left _ (mul_congr_right _ (hσ.congr h))
  mul := fun a b =>
    calc X' * σ (a * b) * X ≈ X' * (σ b * σ a) * X := mul_congr_left _ (mul_congr_right _ (hσ.mul a b))
      _ ≈ X' * σ b * σ a * X := mul_congr_left _ (eq_symm (mul_assoc _ _ _))
      _ ≈ X' * σ b * (1 * σ a) * X := mul_congr_left _ (mul_congr_right _ (eq_symm (one_mul _)))
      _ ≈ X' * σ b * (X * X' * σ a) * X := mul_congr_left _ (mul_congr_right _ (mul_congr_left _ (eq_symm hX.1)))
      _ ≈ X' * σ b * (X * (X' * σ a)) * X := mul_congr_left _ (mul_congr_right _ (mul_assoc _ _ _))
      _ ≈ X' * σ b * X * (X' * σ a) * X := mul_congr_left _ (eq_symm (mul_assoc _ _ _))
      _ ≈ X' * σ b * X * (X' * σ a * X) := mul_assoc _ _ _
  add := fun a b =>
    calc X' * σ (a + b) * X ≈ X' * (σ a + σ b) * X := mul_congr_left _ (mul_congr_right _ (hσ.add a b))
      _ ≈ (X' * σ a + X' * σ b) * X := mul_congr_left _ (left_distrib _ _ _)
      _ ≈ X' * σ a * X + X' * σ b * X := right_distrib _ _ _
  one :=
    calc X' * σ 1 * X ≈ X' * 1 * X := mul_congr_left _ (mul_congr_right _ hσ.one)
      _ ≈ X' * X := mul_congr_left _ (mul_one _)
      _ ≈ 1 := hX.2
  neg := fun a =>
    calc X' * σ (-a) * X ≈ X' * -(σ a) * X := mul_congr_left _ (mul_congr_right _ (hσ.neg a))
      _ ≈ -(X' * σ a) * X := mul_congr_left _ (eq_symm (mul_neg _ _))
      _ ≈ -(X' * σ a * X) := eq_symm (neg_mul _ _)

/-- 8:C4, 8:D10, 8:X3 — the Cayley step is unitary: for `h` symmetric (`σ h ≈ h`), `a` central with `σ a ≈ −a`, and `v` the inverse
of `1 − a h`, the step `u = v (1 + a h)` satisfies `σ(u) u ≈ 1`. The adjoint of `1 − a h` is `1 + a h`, so `σ v` is the
inverse of `1 + a h`; `v` commutes with `1 + a h`; and `σ(u) u = (1 − a h) σ(v) v (1 + a h) = (1 − a h) σ(v) (1 + a h) v`. -/
theorem cayley_unitary {σ : R → R} (hσ : Adjoint σ) {h a v : R} (hh : σ h ≈ h) (ha : σ a ≈ -a) (hc : Central a)
    (hv : Inverse (1 + -(a * h)) v) : σ (v * (1 + a * h)) * (v * (1 + a * h)) ≈ 1 := by
  have hσv : Inverse (1 + a * h) (σ v) := (hσ.inverse hv).congr (hσ.one_sub hh ha hc) (eq_refl _)
  have hMP : Comm (1 + -(a * h)) (1 + a * h) :=
    Comm.add_left (Comm.one_left _) (Comm.neg_left (Comm.add_right (Comm.one_left _).symm (Comm.refl _)))
  have hvP : Comm v (1 + a * h) := hv.comm_of_comm hMP
  calc σ (v * (1 + a * h)) * (v * (1 + a * h)) ≈ σ (1 + a * h) * σ v * (v * (1 + a * h)) :=
        mul_congr_left _ (hσ.mul _ _)
    _ ≈ (1 + -(a * h)) * σ v * ((1 + a * h) * v) := mul_congr (mul_congr_left _ (hσ.one_add hh ha hc)) hvP
    _ ≈ (1 + -(a * h)) * (σ v * ((1 + a * h) * v)) := mul_assoc _ _ _
    _ ≈ (1 + -(a * h)) * (σ v * (1 + a * h) * v) := mul_congr_right _ (eq_symm (mul_assoc _ _ _))
    _ ≈ (1 + -(a * h)) * (1 * v) := mul_congr_right _ (mul_congr_left v hσv.2)
    _ ≈ (1 + -(a * h)) * v := mul_congr_right _ (one_mul v)
    _ ≈ 1 := hv.1

/-- 8:D10 — the Cayley step of a nilpotent shift minus a mass. With `α`, `m` central, `a = 1 + α m` a central unit
of inverse `a'`, `b = 1 − α m`, and `N` nilpotent (`N^{k+1} ≈ 0`): `1 − α(N − m) = a (1 − a' α N)` is a unit, with
inverse `V = geom (a' α N) (k+1) · a'`, and the step `U = V (1 + α(N − m))` differs from the scalar phase `b a'` by
`N c` with `c` commuting with `N`. The massless step (`m = 0`, `b = a = a' = 1`) is `1 + N c`. -/
theorem cayley_nilpotent_shift {α m a' N : R} {k : Nat} (hα : Central α) (hm : Central m) (ha' : Central a')
    (ha : Inverse (1 + α * m) a') (hN : opow N (k + 1) ≈ 0) :
    Inverse (1 + -(α * (N + -m))) (geom (a' * (α * N)) (k + 1) * a') ∧
    ∃ c, Comm N c ∧ geom (a' * (α * N)) (k + 1) * a' * (1 + α * (N + -m)) + -((1 + -(α * m)) * a') ≈ N * c := by
  have hca : Central (a' * α) := ha'.mul hα
  have hXN : a' * (α * N) ≈ N * (a' * α) := eq_trans (eq_symm (mul_assoc _ _ _)) (hca N)
  have hCXN : Comm (a' * (α * N)) N := Comm.mul_left (ha' N) (Comm.mul_left (hα N) (Comm.refl N))
  have hX : opow (a' * (α * N)) (k + 1) ≈ 0 :=
    calc opow (a' * (α * N)) (k + 1) ≈ opow (N * (a' * α)) (k + 1) := opow_congr hXN _
      _ ≈ opow N (k + 1) * opow (a' * α) (k + 1) := mul_opow (eq_symm (hca N)) _
      _ ≈ 0 * opow (a' * α) (k + 1) := mul_congr_left _ hN
      _ ≈ 0 := zero_mul _
  have hG := series_inverse hX
  have haX : (1 + α * m) * (a' * (α * N)) ≈ α * N :=
    calc (1 + α * m) * (a' * (α * N)) ≈ (1 + α * m) * a' * (α * N) := eq_symm (mul_assoc _ _ _)
      _ ≈ 1 * (α * N) := mul_congr_left _ ha.1
      _ ≈ α * N := one_mul _
  have hMfac : 1 + -(α * (N + -m)) ≈ (1 + α * m) * (1 + -(a' * (α * N))) :=
    calc 1 + -(α * (N + -m)) ≈ 1 + -(α * N + α * -m) := add_congr_right 1 (neg_congr (left_distrib _ _ _))
      _ ≈ 1 + -(α * N + -(α * m)) := add_congr_right 1 (neg_congr (add_congr_right _ (eq_symm (mul_neg _ _))))
      _ ≈ 1 + (-(α * N) + - -(α * m)) := add_congr_right 1 (neg_add_rev _ _)
      _ ≈ 1 + (-(α * N) + α * m) := add_congr_right 1 (add_congr_right _ (neg_neg _))
      _ ≈ 1 + (α * m + -(α * N)) := add_congr_right 1 (add_comm _ _)
      _ ≈ 1 + α * m + -(α * N) := eq_symm (add_assoc _ _ _)
      _ ≈ (1 + α * m) * 1 + -((1 + α * m) * (a' * (α * N))) :=
          add_congr (eq_symm (mul_one _)) (neg_congr (eq_symm haX))
      _ ≈ (1 + α * m) * 1 + (1 + α * m) * -(a' * (α * N)) := add_congr_right _ (mul_neg _ _)
      _ ≈ (1 + α * m) * (1 + -(a' * (α * N))) := eq_symm (left_distrib _ _ _)
  refine ⟨(ha.mul hG).congr (eq_symm hMfac) (eq_refl _), ?_⟩
  -- the step minus the phase
  have hb : Central (1 + -(α * m)) := Central.add Central.one (Central.neg (hα.mul hm))
  have hP : 1 + α * (N + -m) ≈ 1 + -(α * m) + α * N :=
    calc 1 + α * (N + -m) ≈ 1 + (α * N + α * -m) := add_congr_right 1 (left_distrib _ _ _)
      _ ≈ 1 + (α * N + -(α * m)) := add_congr_right 1 (add_congr_right _ (eq_symm (mul_neg _ _)))
      _ ≈ 1 + (-(α * m) + α * N) := add_congr_right 1 (add_comm _ _)
      _ ≈ 1 + -(α * m) + α * N := eq_symm (add_assoc _ _ _)
  have hGk : geom (a' * (α * N)) (k + 1) ≈ 1 + a' * (α * N) * geom (a' * (α * N)) k := geom_succ_left _ k
  have hGX : Comm (geom (a' * (α * N)) (k + 1)) (a' * (α * N)) := geom_comm (Comm.refl _) _
  have hGkN : Comm N (geom (a' * (α * N)) k) := (geom_comm hCXN k).symm
  have hGN : Comm N (geom (a' * (α * N)) (k + 1)) := (geom_comm hCXN (k + 1)).symm
  refine ⟨a' * α * (geom (a' * (α * N)) k * (a' * (1 + -(α * m)))) + a' * α * geom (a' * (α * N)) (k + 1), ?_, ?_⟩
  · exact Comm.add_right
      (Comm.mul_right (eq_symm (hca N)) (Comm.mul_right hGkN (Comm.mul_right (eq_symm (ha' N)) (eq_symm (hb N)))))
      (Comm.mul_right (eq_symm (hca N)) hGN)
  · -- `U = G a' P = G (a' b) + G (a' α N)`; `G (a' b) = a' b + X G_k (a' b)`; `a' b = b a'`
    have hU : geom (a' * (α * N)) (k + 1) * a' * (1 + α * (N + -m)) ≈
        (1 + -(α * m)) * a' +
          (a' * (α * N) * geom (a' * (α * N)) k * (a' * (1 + -(α * m))) +
            geom (a' * (α * N)) (k + 1) * (a' * (α * N))) :=
      calc geom (a' * (α * N)) (k + 1) * a' * (1 + α * (N + -m))
          ≈ geom (a' * (α * N)) (k + 1) * (a' * (1 + -(α * m) + α * N)) :=
            eq_trans (mul_assoc _ _ _) (mul_congr_right _ (mul_congr_right _ hP))
        _ ≈ geom (a' * (α * N)) (k + 1) * (a' * (1 + -(α * m)) + a' * (α * N)) :=
            mul_congr_right _ (left_distrib _ _ _)
        _ ≈ geom (a' * (α * N)) (k + 1) * (a' * (1 + -(α * m))) + geom (a' * (α * N)) (k + 1) * (a' * (α * N)) :=
            left_distrib _ _ _
        _ ≈ (1 + a' * (α * N) * geom (a' * (α * N)) k) * (a' * (1 + -(α * m))) +
              geom (a' * (α * N)) (k + 1) * (a' * (α * N)) := add_congr_left _ (mul_congr_left _ hGk)
        _ ≈ 1 * (a' * (1 + -(α * m))) + a' * (α * N) * geom (a' * (α * N)) k * (a' * (1 + -(α * m))) +
              geom (a' * (α * N)) (k + 1) * (a' * (α * N)) := add_congr_left _ (right_distrib _ _ _)
        _ ≈ (1 + -(α * m)) * a' + a' * (α * N) * geom (a' * (α * N)) k * (a' * (1 + -(α * m))) +
              geom (a' * (α * N)) (k + 1) * (a' * (α * N)) :=
            add_congr_left _ (add_congr_left _ (eq_trans (one_mul _) (ha' _)))
        _ ≈ (1 + -(α * m)) * a' +
              (a' * (α * N) * geom (a' * (α * N)) k * (a' * (1 + -(α * m))) +
                geom (a' * (α * N)) (k + 1) * (a' * (α * N))) := add_assoc _ _ _
    calc geom (a' * (α * N)) (k + 1) * a' * (1 + α * (N + -m)) + -((1 + -(α * m)) * a')
        ≈ (1 + -(α * m)) * a' +
            (a' * (α * N) * geom (a' * (α * N)) k * (a' * (1 + -(α * m))) +
              geom (a' * (α * N)) (k + 1) * (a' * (α * N))) + -((1 + -(α * m)) * a') := add_congr_left _ hU
      _ ≈ a' * (α * N) * geom (a' * (α * N)) k * (a' * (1 + -(α * m))) +
            geom (a' * (α * N)) (k + 1) * (a' * (α * N)) + (1 + -(α * m)) * a' + -((1 + -(α * m)) * a') :=
          add_congr_left _ (add_comm _ _)
      _ ≈ a' * (α * N) * geom (a' * (α * N)) k * (a' * (1 + -(α * m))) +
            geom (a' * (α * N)) (k + 1) * (a' * (α * N)) := add_sub_cancel _ _
      _ ≈ N * (a' * α * (geom (a' * (α * N)) k * (a' * (1 + -(α * m))))) +
            N * (a' * α * geom (a' * (α * N)) (k + 1)) := by
          refine add_congr ?_ ?_
          · calc a' * (α * N) * geom (a' * (α * N)) k * (a' * (1 + -(α * m)))
                ≈ N * (a' * α) * geom (a' * (α * N)) k * (a' * (1 + -(α * m))) :=
                  mul_congr_left _ (mul_congr_left _ hXN)
              _ ≈ N * (a' * α * geom (a' * (α * N)) k) * (a' * (1 + -(α * m))) :=
                  mul_congr_left _ (mul_assoc _ _ _)
              _ ≈ N * (a' * α * geom (a' * (α * N)) k * (a' * (1 + -(α * m)))) := mul_assoc _ _ _
              _ ≈ N * (a' * α * (geom (a' * (α * N)) k * (a' * (1 + -(α * m))))) :=
                  mul_congr_right _ (mul_assoc _ _ _)
          · calc geom (a' * (α * N)) (k + 1) * (a' * (α * N))
                ≈ a' * (α * N) * geom (a' * (α * N)) (k + 1) := hGX
              _ ≈ N * (a' * α) * geom (a' * (α * N)) (k + 1) := mul_congr_left _ hXN
              _ ≈ N * (a' * α * geom (a' * (α * N)) (k + 1)) := mul_assoc _ _ _
      _ ≈ N * (a' * α * (geom (a' * (α * N)) k * (a' * (1 + -(α * m)))) + a' * α * geom (a' * (α * N)) (k + 1)) :=
          eq_symm (left_distrib _ _ _)

/-- 8:D10 — the step minus the phase is nilpotent: `(U − b a')^{k+1} ≈ 0` when `U − b a' ≈ N c`, `N c ≈ c N`,
`N^{k+1} ≈ 0`. With the phase central, `U^{(k+1)} ≈ (b a')^{k+1}` follows in characteristic `p` for `k + 1 = p`
(the unipotent file); the massless step has `b a' = 1`. -/
theorem nilpotent_of_eq_mul {u N c : R} {k : Nat} (hu : u ≈ N * c) (hc : Comm N c) (hN : opow N (k + 1) ≈ 0) :
    opow u (k + 1) ≈ 0 :=
  calc opow u (k + 1) ≈ opow (N * c) (k + 1) := opow_congr hu _
    _ ≈ opow N (k + 1) * opow c (k + 1) := mul_opow hc _
    _ ≈ 0 * opow c (k + 1) := mul_congr_left _ hN
    _ ≈ 0 := zero_mul _

/-! ## Conjugation and the anticommutator (8:D17) -/

/-- Conjugation `a ↦ S a S'` by a unit `S` of inverse `S'`. -/
def conjBy (S S' a : R) : R := S * a * S'

theorem conjBy_mul {S S' : R} (h : Inverse S S') (a b : R) : conjBy S S' a * conjBy S S' b ≈ conjBy S S' (a * b) :=
  calc S * a * S' * (S * b * S') ≈ S * a * (S' * (S * b * S')) := mul_assoc _ _ _
    _ ≈ S * a * (S' * (S * b) * S') := mul_congr_right _ (eq_symm (mul_assoc _ _ _))
    _ ≈ S * a * (S' * S * b * S') := mul_congr_right _ (mul_congr_left _ (eq_symm (mul_assoc _ _ _)))
    _ ≈ S * a * (1 * b * S') := mul_congr_right _ (mul_congr_left _ (mul_congr_left _ h.2))
    _ ≈ S * a * (b * S') := mul_congr_right _ (mul_congr_left _ (one_mul b))
    _ ≈ S * a * b * S' := eq_symm (mul_assoc _ _ _)
    _ ≈ S * (a * b) * S' := mul_congr_left _ (mul_assoc _ _ _)

theorem conjBy_add (S S' a b : R) : conjBy S S' (a + b) ≈ conjBy S S' a + conjBy S S' b :=
  calc S * (a + b) * S' ≈ (S * a + S * b) * S' := mul_congr_left _ (left_distrib _ _ _)
    _ ≈ S * a * S' + S * b * S' := right_distrib _ _ _

/-- 8:D17, 8:D18 — conjugation by a unit preserves the anticommutator: `{S a S', S b S'} ≈ S {a, b} S'`, so the transported
gammas satisfy the Clifford relations the originals do. -/
theorem conj_anticomm {S S' : R} (h : Inverse S S') (a b : R) :
    conjBy S S' a * conjBy S S' b + conjBy S S' b * conjBy S S' a ≈ conjBy S S' (a * b + b * a) :=
  eq_trans (add_congr (conjBy_mul h a b) (conjBy_mul h b a)) (eq_symm (conjBy_add _ _ _ _))

/-- Conjugation preserves central values: `S c S' ≈ c` for central `c`. -/
theorem conjBy_central {S S' : R} (h : Inverse S S') {c : R} (hc : Central c) : conjBy S S' c ≈ c :=
  calc S * c * S' ≈ c * S * S' := mul_congr_left _ (eq_symm (hc S))
    _ ≈ c * (S * S') := mul_assoc _ _ _
    _ ≈ c * 1 := mul_congr_right _ h.1
    _ ≈ c := mul_one c

/-! ## The square of a sum of anticommuting operators and the Dirac factorisation (8:D3, 8:D18) -/

/-- `A` and `B` anticommute. -/
def Anticomm (A B : R) : Prop := A * B + B * A ≈ 0

theorem Anticomm.symm {A B : R} (h : Anticomm A B) : Anticomm B A := eq_trans (add_comm _ _) h

theorem Anticomm.add_left {A B C : R} (hA : Anticomm A C) (hB : Anticomm B C) : Anticomm (A + B) C :=
  calc (A + B) * C + C * (A + B) ≈ A * C + B * C + (C * A + C * B) := add_congr (right_distrib _ _ _) (left_distrib _ _ _)
    _ ≈ A * C + C * A + (B * C + C * B) := add_add_add_comm _ _ _ _
    _ ≈ 0 + 0 := add_congr hA hB
    _ ≈ 0 := zero_add 0

/-- `(A + B)² ≈ A² + B²` when `A`, `B` anticommute. -/
theorem sq_add_of_anticomm {A B : R} (h : Anticomm A B) : (A + B) * (A + B) ≈ A * A + B * B :=
  calc (A + B) * (A + B) ≈ (A + B) * A + (A + B) * B := left_distrib _ _ _
    _ ≈ A * A + B * A + (A * B + B * B) := add_congr (right_distrib _ _ _) (right_distrib _ _ _)
    _ ≈ A * A + (B * A + (A * B + B * B)) := add_assoc _ _ _
    _ ≈ A * A + (B * A + A * B + B * B) := add_congr_right _ (eq_symm (add_assoc _ _ _))
    _ ≈ A * A + (0 + B * B) := add_congr_right _ (add_congr_left _ h.symm)
    _ ≈ A * A + B * B := add_congr_right _ (zero_add _)

/-- The square of a sum of pairwise anticommuting operators is the sum of the squares. -/
theorem sq_osum {A : Nat → R} : ∀ n, (∀ i j, i < n → j < n → i ≠ j → Anticomm (A i) (A j)) →
    osum A n * osum A n ≈ osum (fun i => A i * A i) n
  | 0, _ => mul_zero 0
  | n + 1, h => by
    have hS : Anticomm (osum A n) (A n) := by
      show osum A n * A n + A n * osum A n ≈ 0
      calc osum A n * A n + A n * osum A n ≈ osum (fun i => A i * A n) n + osum (fun i => A n * A i) n :=
            add_congr (osum_mul_right _ _ n) (osum_mul_left _ _ n)
        _ ≈ osum (fun i => A i * A n + A n * A i) n := eq_symm (osum_add _ _ n)
        _ ≈ 0 := osum_eq_zero n fun i hi =>
            h i n (Nat.lt_succ_of_lt hi) (Nat.lt_succ_self n) (Nat.ne_of_lt hi)
    calc (osum A n + A n) * (osum A n + A n) ≈ osum A n * osum A n + A n * A n := sq_add_of_anticomm hS
      _ ≈ osum (fun i => A i * A i) n + A n * A n :=
          add_congr_left _ (sq_osum n fun i j hi hj hij => h i j (Nat.lt_succ_of_lt hi) (Nat.lt_succ_of_lt hj) hij)

/-- `(d g)(d' g') ≈ (d d')(g g')` when `g` commutes with `d'`. -/
theorem mul_mul_swap {d g d' g' : R} (hgd : Comm g d') : d * g * (d' * g') ≈ d * d' * (g * g') :=
  calc d * g * (d' * g') ≈ d * (g * (d' * g')) := mul_assoc _ _ _
    _ ≈ d * (g * d' * g') := mul_congr_right _ (eq_symm (mul_assoc _ _ _))
    _ ≈ d * (d' * g * g') := mul_congr_right _ (mul_congr_left _ hgd)
    _ ≈ d * (d' * (g * g')) := mul_congr_right _ (mul_assoc _ _ _)
    _ ≈ d * d' * (g * g') := eq_symm (mul_assoc _ _ _)

/-- The summands `∇_μ γ_μ` of a Dirac operator anticommute when the differences commute with each other and with
the gammas and the gammas anticommute. -/
theorem anticomm_of_clifford {d d' g g' : R} (hdd : Comm d d') (hdg : Comm d g') (hd'g : Comm d' g)
    (hgg : Anticomm g g') : Anticomm (d * g) (d' * g') :=
  calc d * g * (d' * g') + d' * g' * (d * g) ≈ d * d' * (g * g') + d' * d * (g' * g) :=
        add_congr (mul_mul_swap hd'g.symm) (mul_mul_swap hdg.symm)
    _ ≈ d * d' * (g * g') + d * d' * (g' * g) := add_congr_right _ (mul_congr_left _ (eq_symm hdd))
    _ ≈ d * d' * (g * g' + g' * g) := eq_symm (left_distrib _ _ _)
    _ ≈ d * d' * 0 := mul_congr_right _ hgg
    _ ≈ 0 := mul_zero _

/-- 8:D3, 8:D18 — the Dirac factorisation. For `𝒟 = Σ_{μ<n} ∇_μ γ_μ` with the differences commuting with each other
and with the gammas, the gammas anticommuting and squaring to central `η_μ`, and the mass `m` central:
`(𝒟 − m)(𝒟 + m) ≈ Σ_μ η_μ ∇_μ² − m²`. The cross terms pair into anticommutators, which vanish (`sq_osum`). -/
theorem dirac_factorisation {n : Nat} {del γ η : Nat → R} {m : R}
    (hdd : ∀ μ ν, μ < n → ν < n → Comm (del μ) (del ν)) (hdg : ∀ μ ν, μ < n → ν < n → Comm (del μ) (γ ν))
    (hgg : ∀ μ ν, μ < n → ν < n → μ ≠ ν → Anticomm (γ μ) (γ ν)) (hsq : ∀ μ, μ < n → γ μ * γ μ ≈ η μ)
    (hη : ∀ μ, μ < n → Central (η μ)) (hm : Central m) :
    (osum (fun μ => del μ * γ μ) n + -m) * (osum (fun μ => del μ * γ μ) n + m) ≈
      osum (fun μ => η μ * (del μ * del μ)) n + -(m * m) := by
  have hDD : osum (fun μ => del μ * γ μ) n * osum (fun μ => del μ * γ μ) n ≈ osum (fun μ => η μ * (del μ * del μ)) n :=
    calc osum (fun μ => del μ * γ μ) n * osum (fun μ => del μ * γ μ) n ≈ osum (fun μ => del μ * γ μ * (del μ * γ μ)) n :=
          sq_osum n fun i j hi hj hij => anticomm_of_clifford (hdd i j hi hj) (hdg i j hi hj) (hdg j i hj hi) (hgg i j hi hj hij)
      _ ≈ osum (fun μ => η μ * (del μ * del μ)) n := osum_congr n fun μ hμ =>
          calc del μ * γ μ * (del μ * γ μ) ≈ del μ * del μ * (γ μ * γ μ) := mul_mul_swap (hdg μ μ hμ hμ).symm
            _ ≈ del μ * del μ * η μ := mul_congr_right _ (hsq μ hμ)
            _ ≈ η μ * (del μ * del μ) := eq_symm (hη μ hμ _)
  calc (osum (fun μ => del μ * γ μ) n + -m) * (osum (fun μ => del μ * γ μ) n + m)
      ≈ (osum (fun μ => del μ * γ μ) n + -m) * osum (fun μ => del μ * γ μ) n + (osum (fun μ => del μ * γ μ) n + -m) * m :=
        left_distrib _ _ _
    _ ≈ osum (fun μ => del μ * γ μ) n * osum (fun μ => del μ * γ μ) n + -m * osum (fun μ => del μ * γ μ) n +
          (osum (fun μ => del μ * γ μ) n * m + -m * m) := add_congr (right_distrib _ _ _) (right_distrib _ _ _)
    _ ≈ osum (fun μ => del μ * γ μ) n * osum (fun μ => del μ * γ μ) n + -(osum (fun μ => del μ * γ μ) n * m) +
          (osum (fun μ => del μ * γ μ) n * m + -(m * m)) :=
        add_congr (add_congr_right _ (eq_trans (eq_symm (neg_mul _ _)) (neg_congr (hm _))))
          (add_congr_right _ (eq_symm (neg_mul _ _)))
    _ ≈ osum (fun μ => del μ * γ μ) n * osum (fun μ => del μ * γ μ) n +
          (-(osum (fun μ => del μ * γ μ) n * m) + osum (fun μ => del μ * γ μ) n * m + -(m * m)) :=
        eq_trans (add_assoc _ _ _) (add_congr_right _ (eq_symm (add_assoc _ _ _)))
    _ ≈ osum (fun μ => del μ * γ μ) n * osum (fun μ => del μ * γ μ) n + (0 + -(m * m)) :=
        add_congr_right _ (add_congr_left _ (neg_add _))
    _ ≈ osum (fun μ => η μ * (del μ * del μ)) n + -(m * m) := add_congr hDD (zero_add _)

end FRC.Dirac.Operator
