import FrcCore.Ring
import FrcCore.Theme.Quadratic

/-!
# FrcCore.Theme.Unitary — SU(3) of a three-form over the quadratic extension, by elements (task LM41)

The exact clauses of master row G4 (p00069, 27:C7), stated by elements and never by counting the group (decision Q20).

* **The rank forced as the minimal triality frame.** Take a shell without zero divisors whose base has no root of
  `x² + x + 1`. On a prime `Ω > 3` with a quarter-turn this is B5's structural face, which holds iff `Ω ≡ 5 (mod 12)`
  (p00015, `Carrier.substrate_shell`). Then `−3` is not a square, so `Ext p (−3)` is the quadratic extension, and
  `ω = −h + h w` with `h = 1/2` is a root there. Every root `ω` of `x² + x + 1` in an extension `Ext p ν` lies off the
  base, has `ω̄ = ω²` and norm one, and `ωⁿ = 1` exactly when `3 ∣ n` (`triality_frame`). The scalar `ω Iₙ` is unitary
  for every `n`, since `ω̄ ω = 1`. Its determinant is `ωⁿ`, which is one exactly when `3 ∣ n`, so `n = 3` is the least
  rank whose special unitary group holds the triality scalar. At `n = 3` the scalar `ω I₃` lies in `SU(H)` for every
  three-form `H`. The file imports neither the Carrier nor the prime field, so that the interactions key file can bind
  it within the closure budget (G10). The binding supplies the hypotheses: `Shell.Prime.mul_eq_zero` (or a frame's
  `mul_eq_zero`) for the zero divisors, p00015 for the missing root, and `Carrier.csq` for the half.
* **The group of a three-form.** Over `Ext p ν`, the `3 × 3` matrices `U` with `U† H U = H` and `det U = 1` hold the
  identity and every scalar `c I₃` with `c̄ c = 1` and `c³ = 1`. They are closed under the product, and each has its
  adjugate as a two-sided inverse in the same set (`su_group`). The proof never uses `H† = H`, so it holds for the
  Hermitian forms of the row in particular.

The identities over the extension are decided by a copy of the base normaliser's evaluation (`Ring.lean`) read in
`Ext p ν`. Its expansion and comparison are the base's, unchanged. Matrix associativity, `(AB)† = B†A†`,
`det (AB) = det A det B`, `U adj U = adj U U = det U · I` and `det (adj U) = (det U)²` are its instances. No axioms.
-/

namespace FRC.Unitary

open FRC.Shell FRC.Shell.Frame FRC.Extension

variable {p : Nat} [Pos p] {ν : Shell p}

/-! ## The ring laws of the quadratic extension, on components -/

theorem x_add_comm (a b : Ext p ν) : a + b = b + a := Ext.ext (Shell.add_comm _ _) (Shell.add_comm _ _)
theorem x_add_assoc (a b c : Ext p ν) : a + b + c = a + (b + c) := Ext.ext (Shell.add_assoc _ _ _) (Shell.add_assoc _ _ _)
theorem x_add_left_comm (a b c : Ext p ν) : a + (b + c) = b + (a + c) :=
  Ext.ext (Shell.add_left_comm _ _ _) (Shell.add_left_comm _ _ _)
theorem x_zero_add (a : Ext p ν) : 0 + a = a := Ext.ext (Shell.zero_add _) (Shell.zero_add _)
theorem x_add_zero (a : Ext p ν) : a + 0 = a := Ext.ext (Shell.add_zero _) (Shell.add_zero _)
theorem x_neg_add (a : Ext p ν) : -a + a = 0 := Ext.ext (Shell.neg_add _) (Shell.neg_add _)
theorem x_neg_neg (a : Ext p ν) : - -a = a := Ext.ext (Shell.neg_neg _) (Shell.neg_neg _)
theorem x_neg_zero : (-0 : Ext p ν) = 0 := Ext.ext Shell.neg_zero Shell.neg_zero
theorem x_neg_add_rev (a b : Ext p ν) : -(a + b) = -a + -b := Ext.ext (Shell.neg_add_rev _ _) (Shell.neg_add_rev _ _)
theorem x_add_right_cancel {a b c : Ext p ν} (h : a + c = b + c) : a = b :=
  Ext.ext (Shell.add_right_cancel (Ext.re_congr h : a.re + c.re = b.re + c.re))
    (Shell.add_right_cancel (Ext.im_congr h : a.im + c.im = b.im + c.im))

theorem x_zero_mul (a : Ext p ν) : 0 * a = 0 :=
  Ext.ext (RE.sound (look [ν, a.re, a.im]) (.add (.mul .zero (.var 1)) (.mul (.var 0) (.mul .zero (.var 2)))) .zero (by decide +kernel))
    (RE.sound (look [ν, a.re, a.im]) (.add (.mul .zero (.var 2)) (.mul .zero (.var 1))) .zero (by decide +kernel))

theorem x_left_distrib (a b c : Ext p ν) : a * (b + c) = a * b + a * c :=
  Ext.ext (RE.sound (look [ν, a.re, a.im, b.re, b.im, c.re, c.im]) (.add (.mul (.var 1) (.add (.var 3) (.var 5))) (.mul (.var 0) (.mul (.var 2) (.add (.var 4) (.var 6))))) (.add (.add (.mul (.var 1) (.var 3)) (.mul (.var 0) (.mul (.var 2) (.var 4)))) (.add (.mul (.var 1) (.var 5)) (.mul (.var 0) (.mul (.var 2) (.var 6))))) (by decide +kernel))
    (RE.sound (look [ν, a.re, a.im, b.re, b.im, c.re, c.im]) (.add (.mul (.var 1) (.add (.var 4) (.var 6))) (.mul (.var 2) (.add (.var 3) (.var 5)))) (.add (.add (.mul (.var 1) (.var 4)) (.mul (.var 2) (.var 3))) (.add (.mul (.var 1) (.var 6)) (.mul (.var 2) (.var 5)))) (by decide +kernel))

theorem x_neg_mul (a b : Ext p ν) : -(a * b) = -a * b :=
  Ext.ext (RE.sound (look [ν, a.re, a.im, b.re, b.im]) (.neg (.add (.mul (.var 1) (.var 3)) (.mul (.var 0) (.mul (.var 2) (.var 4))))) (.add (.mul (.neg (.var 1)) (.var 3)) (.mul (.var 0) (.mul (.neg (.var 2)) (.var 4)))) (by decide +kernel))
    (RE.sound (look [ν, a.re, a.im, b.re, b.im]) (.neg (.add (.mul (.var 1) (.var 4)) (.mul (.var 2) (.var 3)))) (.add (.mul (.neg (.var 1)) (.var 4)) (.mul (.neg (.var 2)) (.var 3))) (by decide +kernel))

theorem x_mul_zero (a : Ext p ν) : a * 0 = 0 := by rw [Ext.mul_comm]; exact x_zero_mul a
theorem x_right_distrib (a b c : Ext p ν) : (a + b) * c = a * c + b * c := by
  rw [Ext.mul_comm (a + b) c, x_left_distrib, Ext.mul_comm c a, Ext.mul_comm c b]
theorem x_mul_neg (a b : Ext p ν) : -(a * b) = a * -b := by rw [Ext.mul_comm a b, x_neg_mul, Ext.mul_comm (-b) a]
theorem x_neg_mul_neg (a b : Ext p ν) : -a * -b = a * b := by rw [← x_neg_mul, ← x_mul_neg, x_neg_neg]
theorem x_mul_left_comm (a b c : Ext p ν) : a * (b * c) = b * (a * c) := by
  rw [← Ext.mul_assoc, Ext.mul_comm a b, Ext.mul_assoc]

/-- Conjugation is additive. -/
theorem conj_add (a b : Ext p ν) : Ext.conj (a + b) = Ext.conj a + Ext.conj b := Ext.ext rfl (Shell.neg_add_rev _ _)

/-! ## The normaliser read in the extension

The expansion `RE.toP`, the normal form `nfP` and the comparison `pbeq` are the base's (`Ring.lean`). Only the evaluation
changes: an expression is read in `Ext p ν`, and soundness follows from the ring laws above. -/

/-- An expression of the normaliser evaluated in the extension. -/
def xeval (env : Nat → Ext p ν) : RE → Ext p ν
  | .var i => env i
  | .zero => 0
  | .one => 1
  | .add a b => xeval env a + xeval env b
  | .mul a b => xeval env a * xeval env b
  | .neg a => -(xeval env a)

/-- The assignment of extension values to the variables `0, 1, 2, …` of an expression. -/
def xlook : List (Ext p ν) → Nat → Ext p ν
  | [], _ => 0
  | x :: _, 0 => x
  | _ :: l, n + 1 => xlook l n

def xmEval (env : Nat → Ext p ν) : List Nat → Ext p ν
  | [] => 1
  | i :: m => env i * xmEval env m

def xpEval (env : Nat → Ext p ν) : List (List Nat) → Ext p ν
  | [] => 0
  | m :: P => xmEval env m + xpEval env P

theorem xmEval_append (env : Nat → Ext p ν) (m n : List Nat) : xmEval env (m ++ n) = xmEval env m * xmEval env n := by
  induction m with
  | nil => exact (Ext.one_mul _).symm
  | cons i m ih => show env i * xmEval env (m ++ n) = env i * xmEval env m * xmEval env n; rw [ih, Ext.mul_assoc]

theorem xpEval_append (env : Nat → Ext p ν) (P Q : List (List Nat)) :
    xpEval env (P ++ Q) = xpEval env P + xpEval env Q := by
  induction P with
  | nil => exact (x_zero_add _).symm
  | cons m P ih =>
    show xmEval env m + xpEval env (P ++ Q) = xmEval env m + xpEval env P + xpEval env Q; rw [ih, x_add_assoc]

theorem xpEval_row (env : Nat → Ext p ν) (m : List Nat) (Q : List (List Nat)) :
    xpEval env (pRow m Q) = xmEval env m * xpEval env Q := by
  induction Q with
  | nil => exact (x_mul_zero _).symm
  | cons n Q ih =>
    show xmEval env (m ++ n) + xpEval env (pRow m Q) = xmEval env m * (xmEval env n + xpEval env Q)
    rw [ih, xmEval_append, x_left_distrib]

theorem xpEval_mul (env : Nat → Ext p ν) (P Q : List (List Nat)) :
    xpEval env (pMul P Q) = xpEval env P * xpEval env Q := by
  induction P with
  | nil => exact (x_zero_mul _).symm
  | cons m P ih =>
    show xpEval env (pRow m Q ++ pMul P Q) = (xmEval env m + xpEval env P) * xpEval env Q
    rw [xpEval_append, xpEval_row, ih, x_right_distrib]

theorem xring_add (A B C D : Ext p ν) : A + -B + (C + -D) = A + C + -(B + D) := by
  rw [x_neg_add_rev, x_add_assoc, x_add_assoc, x_add_left_comm (-B) C (-D)]

theorem xring_mul (A B C D : Ext p ν) : (A + -B) * (C + -D) = A * C + B * D + -(A * D + B * C) := by
  rw [x_right_distrib, x_left_distrib, x_left_distrib, ← x_mul_neg, ← x_neg_mul, x_neg_mul_neg, x_neg_add_rev,
    x_add_assoc, x_add_assoc]
  refine congrArg (A * C + ·) ?_
  rw [x_add_comm (-(B * C)) (B * D), x_add_left_comm]

theorem xring_neg (A B : Ext p ν) : -(A + -B) = B + -A := by rw [x_neg_add_rev, x_neg_neg, x_add_comm]

theorem xtoP_eval (env : Nat → Ext p ν) (e : RE) : xeval env e = xpEval env e.toP.1 + -(xpEval env e.toP.2) := by
  induction e with
  | var i =>
    show env i = (env i * 1 + 0) + -(0 : Ext p ν)
    rw [Ext.mul_one, x_add_zero, x_neg_zero, x_add_zero]
  | zero => show (0 : Ext p ν) = 0 + -0; rw [x_neg_zero, x_add_zero]
  | one => show (1 : Ext p ν) = (1 + 0) + -(0 : Ext p ν); rw [x_add_zero, x_neg_zero, x_add_zero]
  | add a b iha ihb =>
    show xeval env a + xeval env b = xpEval env (a.toP.1 ++ b.toP.1) + -(xpEval env (a.toP.2 ++ b.toP.2))
    rw [iha, ihb, xpEval_append, xpEval_append, xring_add]
  | mul a b iha ihb =>
    show xeval env a * xeval env b = xpEval env (pMul a.toP.1 b.toP.1 ++ pMul a.toP.2 b.toP.2) +
      -(xpEval env (pMul a.toP.1 b.toP.2 ++ pMul a.toP.2 b.toP.1))
    rw [iha, ihb, xpEval_append, xpEval_append, xpEval_mul, xpEval_mul, xpEval_mul, xpEval_mul, xring_mul]
  | neg a iha =>
    show -(xeval env a) = xpEval env a.toP.2 + -(xpEval env a.toP.1)
    rw [iha, xring_neg]

theorem xmEval_insM (env : Nat → Ext p ν) (i : Nat) (m : List Nat) : xmEval env (insM i m) = env i * xmEval env m := by
  induction m with
  | nil => rfl
  | cons j m ih =>
    show xmEval env (if Nat.ble i j then i :: j :: m else j :: insM i m) = env i * (env j * xmEval env m)
    cases Nat.ble i j with
    | true => rfl
    | false => show env j * xmEval env (insM i m) = _; rw [ih, x_mul_left_comm]

theorem xmEval_sortM (env : Nat → Ext p ν) (m : List Nat) : xmEval env (sortM m) = xmEval env m := by
  induction m with
  | nil => rfl
  | cons i m ih => show xmEval env (insM i (sortM m)) = env i * xmEval env m; rw [xmEval_insM, ih]

theorem xpEval_insP (env : Nat → Ext p ν) (m : List Nat) (P : List (List Nat)) :
    xpEval env (insP m P) = xmEval env m + xpEval env P := by
  induction P with
  | nil => rfl
  | cons n P ih =>
    show xpEval env (if lexLe m n then m :: n :: P else n :: insP m P) = xmEval env m + (xmEval env n + xpEval env P)
    cases lexLe m n with
    | true => rfl
    | false => show xmEval env n + xpEval env (insP m P) = _; rw [ih, x_add_left_comm]

theorem xpEval_nfP (env : Nat → Ext p ν) (P : List (List Nat)) : xpEval env (nfP P) = xpEval env P := by
  induction P with
  | nil => rfl
  | cons m P ih =>
    show xpEval env (insP (sortM m) (nfP P)) = xmEval env m + xpEval env P; rw [xpEval_insP, ih, xmEval_sortM]

/-- The normaliser's soundness in the extension: if the two cross lists agree after normalisation, the two sides are
equal on every assignment of extension values to the variables. -/
theorem xsound (env : Nat → Ext p ν) (l r : RE)
    (hb : pbeq (nfP (l.toP.1 ++ r.toP.2)) (nfP (r.toP.1 ++ l.toP.2)) = true) : xeval env l = xeval env r := by
  have h := pbeq_eq hb
  have h1 : xpEval env l.toP.1 + xpEval env r.toP.2 = xpEval env r.toP.1 + xpEval env l.toP.2 := by
    rw [← xpEval_append, ← xpEval_append, ← xpEval_nfP env (l.toP.1 ++ r.toP.2),
      ← xpEval_nfP env (r.toP.1 ++ l.toP.2), h]
  rw [xtoP_eval env l, xtoP_eval env r]
  apply x_add_right_cancel (c := xpEval env l.toP.2 + xpEval env r.toP.2)
  rw [← x_add_assoc, x_add_assoc (xpEval env l.toP.1), x_neg_add, x_add_zero,
      ← x_add_assoc, x_add_comm (xpEval env r.toP.1 + -(xpEval env r.toP.2)) (xpEval env l.toP.2), ← x_add_assoc,
      x_add_comm (xpEval env l.toP.2) (xpEval env r.toP.1), x_add_assoc, x_neg_add, x_add_zero, h1]

/-! ## The triality frame: the cube roots of unity of the extension -/

theorem red1 {L R A X : Shell p} (e : L = R + A * X) (ha : A = 0) : L = R :=
  e.trans ((congrArg (R + ·) (show A * X = 0 by rw [ha]; exact Shell.zero_mul _)).trans (Shell.add_zero R))

theorem red2 {L R A B X Y : Shell p} (e : L = R + A * X + B * Y) (ha : A = 0) (hb : B = 0) : L = R :=
  red1 (red1 e hb) ha

theorem red3 {L R A B C X Y Z : Shell p} (e : L = R + A * X + B * Y + C * Z) (ha : A = 0) (hb : B = 0) (hc : C = 0) :
    L = R :=
  red2 (red1 e hc) ha hb

/-- Off the base: where the shell has no root of `x² + x + 1`, a root `z` in the extension has `z.im ≠ 0`. -/
theorem root_off_base (hno : ¬ ∃ a : Shell p, a * a + a + 1 = 0) {z : Ext p ν} (hz : z * z + z + 1 = 0) :
    z.im ≠ 0 := fun hb =>
  hno ⟨z.re, (red1 (RE.sound (look [ν, z.re, z.im]) (.add (.add (.mul (.var 1) (.var 1)) (.var 1)) .one) (.add (.add (.add (.add (.mul (.var 1) (.var 1)) (.mul (.var 0) (.mul (.var 2) (.var 2)))) (.var 1)) .one) (.mul (.var 2) (.neg (.mul (.var 0) (.var 2))))) (by decide +kernel) :
    z.re * z.re + z.re + 1 = z.re * z.re + ν * (z.im * z.im) + z.re + 1 + z.im * -(ν * z.im)) hb).trans (Ext.re_congr hz)⟩

/-- Let `z` be a root of `x² + x + 1` off the base of a shell without zero divisors. Then `2 Re z + 1 = 0`, the
conjugate is the square, `z̄ = z²`, and the norm is one. -/
theorem cube_root_conj (hdom : ∀ a b : Shell p, a * b = 0 → a = 0 ∨ b = 0) {z : Ext p ν} (hz : z * z + z + 1 = 0) (hb : z.im ≠ 0) :
    z.re + z.re + 1 = 0 ∧ Ext.conj z = z * z ∧ Ext.norm z = 1 := by
  have er : z.re * z.re + ν * (z.im * z.im) + z.re + 1 = 0 := Ext.re_congr hz
  have ei : z.re * z.im + z.im * z.re + z.im + 0 = 0 := Ext.im_congr hz
  have hT : z.re + z.re + 1 = 0 :=
    match hdom _ _ ((RE.sound (look [ν, z.re, z.im]) (.mul (.var 2) (.add (.add (.var 1) (.var 1)) .one)) (.add (.add (.add (.mul (.var 1) (.var 2)) (.mul (.var 2) (.var 1))) (.var 2)) .zero) (by decide +kernel) :
        z.im * (z.re + z.re + 1) = z.re * z.im + z.im * z.re + z.im + 0).trans ei) with
    | .inl e => absurd e hb
    | .inr e => e
  refine ⟨hT, Ext.ext ?_ ?_, ?_⟩
  · exact red2 (RE.sound (look [ν, z.re, z.im]) (.var 1) (.add (.add (.add (.mul (.var 1) (.var 1)) (.mul (.var 0) (.mul (.var 2) (.var 2)))) (.mul (.add (.add (.var 1) (.var 1)) .one) .one)) (.mul (.add (.add (.add (.mul (.var 1) (.var 1)) (.mul (.var 0) (.mul (.var 2) (.var 2)))) (.var 1)) .one) (.neg .one))) (by decide +kernel) :
      z.re = z.re * z.re + ν * (z.im * z.im) + (z.re + z.re + 1) * 1 + (z.re * z.re + ν * (z.im * z.im) + z.re + 1) * -1)
      hT er
  · exact red1 (RE.sound (look [ν, z.re, z.im]) (.neg (.var 2)) (.add (.add (.mul (.var 1) (.var 2)) (.mul (.var 2) (.var 1))) (.mul (.add (.add (.var 1) (.var 1)) .one) (.neg (.var 2)))) (by decide +kernel) :
      -z.im = z.re * z.im + z.im * z.re + (z.re + z.re + 1) * -z.im) hT
  · exact red2 (RE.sound (look [ν, z.re, z.im]) (.add (.mul (.var 1) (.var 1)) (.neg (.mul (.var 0) (.mul (.var 2) (.var 2))))) (.add (.add .one (.mul (.add (.add (.var 1) (.var 1)) .one) (.var 1))) (.mul (.add (.add (.add (.mul (.var 1) (.var 1)) (.mul (.var 0) (.mul (.var 2) (.var 2)))) (.var 1)) .one) (.neg .one))) (by decide +kernel) :
      z.re * z.re + -(ν * (z.im * z.im)) = 1 + (z.re + z.re + 1) * z.re + (z.re * z.re + ν * (z.im * z.im) + z.re + 1) * -1)
      hT er

/-- A root of `x² + x + 1` is a cube root of unity: `z³ = 1 + (z − 1)(z² + z + 1)`. -/
theorem cube_one {z : Ext p ν} (hz : z * z + z + 1 = 0) : z ^ 3 = 1 := by
  have e : z ^ 3 = 1 + (z + -1) * (z * z + z + 1) := xsound (xlook [z]) (.mul (.mul (.mul .one (.var 0)) (.var 0)) (.var 0)) (.add .one (.mul (.add (.var 0) (.neg .one)) (.add (.add (.mul (.var 0) (.var 0)) (.var 0)) .one))) (by decide +kernel)
  rw [e, hz, x_mul_zero, x_add_zero]

theorem mod3_step (n : Nat) : (n + 3) % 3 = n % 3 := by
  rw [Nat.add_comm]; exact FRC.Nat.add_mul_mod_self_left n 1 3 (by decide)

theorem pow_mod_three {z : Ext p ν} (h3 : z ^ 3 = 1) : ∀ n : Nat, z ^ n = z ^ (n % 3)
  | 0 => rfl
  | 1 => rfl
  | 2 => rfl
  | n + 3 => by rw [Ext.pow_add z n 3, h3, Ext.mul_one, mod3_step n]; exact pow_mod_three h3 n

/-- The order three: with `z³ = 1`, `z ≠ 1` and `z² ≠ 1`, `zⁿ = 1` exactly when `3 ∣ n`. -/
theorem pow_eq_one_iff {z : Ext p ν} (h3 : z ^ 3 = 1) (h1 : z ^ 1 ≠ 1) (h2 : z ^ 2 ≠ 1) (n : Nat) :
    z ^ n = 1 ↔ n % 3 = 0 := by
  rw [pow_mod_three h3 n]
  have hlt := Nat.mod_lt n (by decide : 0 < 3)
  generalize n % 3 = r at hlt ⊢
  match r, hlt with
  | 0, _ => exact ⟨fun _ => rfl, fun _ => rfl⟩
  | 1, _ => exact ⟨fun e => absurd e h1, fun e => absurd e (by decide)⟩
  | 2, _ => exact ⟨fun e => absurd e h2, fun e => absurd e (by decide)⟩
  | k + 3, hlt => exact absurd hlt (Nat.not_lt_of_le (Nat.le_add_left 3 k))

/-- The triality scalar on a shell without zero divisors whose base has no root of `x² + x + 1`. Every root `ω` in the extension lies
off the base, with `ω̄ = ω²` and norm one. So `ω̄ ω = 1`, and the scalar `ω Iₙ` is unitary. Its determinant `ωⁿ` is one
exactly when `3 ∣ n`: `ω¹ ≠ 1`, `ω² ≠ 1` and `ω³ = 1`. -/
theorem triality_scalar (hdom : ∀ a b : Shell p, a * b = 0 → a = 0 ∨ b = 0) (hno : ¬ ∃ a : Shell p, a * a + a + 1 = 0) {ω : Ext p ν}
    (hω : ω * ω + ω + 1 = 0) :
    ω.im ≠ 0 ∧ Ext.conj ω = ω * ω ∧ Ext.norm ω = 1 ∧ Ext.conj ω * ω = 1 ∧
      ω ^ 1 ≠ 1 ∧ ω ^ 2 ≠ 1 ∧ ω ^ 3 = 1 ∧ ∀ n : Nat, ω ^ n = 1 ↔ n % 3 = 0 := by
  have hb := root_off_base hno hω
  obtain ⟨_, hc, hn⟩ := cube_root_conj hdom hω hb
  have h3 := cube_one hω
  have h1 : ω ^ 1 ≠ 1 := fun e => hb (Ext.im_congr ((Ext.one_mul ω).symm.trans e))
  have h2 : ω ^ 2 ≠ 1 := fun e =>
    hb (Ext.im_congr ((Ext.one_mul ω).symm.trans ((congrArg (· * ω) e).symm.trans h3)))
  have hu : Ext.conj ω * ω = 1 := by rw [Ext.mul_comm]; exact Ext.conj_inv_of_norm_one ω hn
  exact ⟨hb, hc, hn, hu, h1, h2, h3, pow_eq_one_iff h3 h1 h2⟩

/-- `ω = −h + h w`. With `h = 1/2` and `ν = −3` it is a root of `x² + x + 1`. -/
def omega (h : Shell p) : Ext p ν := ⟨-h, h⟩

theorem omega_root {h : Shell p} (hh : h + h = 1) (hν : ν + 1 + 1 + 1 = 0) :
    (omega h : Ext p ν) * omega h + omega h + 1 = 0 := by
  have hA : h + h + -1 = 0 := by rw [hh, Shell.add_neg]
  exact Ext.ext
    (red2 (RE.sound (look [ν, h]) (.add (.add (.add (.mul (.neg (.var 1)) (.neg (.var 1))) (.mul (.var 0) (.mul (.var 1) (.var 1)))) (.neg (.var 1))) .one) (.add (.add .zero (.mul (.add (.add (.var 1) (.var 1)) (.neg .one)) (.neg (.add (.var 1) .one)))) (.mul (.add (.add (.add (.var 0) .one) .one) .one) (.mul (.var 1) (.var 1)))) (by decide +kernel) :
      -h * -h + ν * (h * h) + -h + 1 = 0 + (h + h + -1) * -(h + 1) + (ν + 1 + 1 + 1) * (h * h)) hA hν)
    (red1 (RE.sound (look [ν, h]) (.add (.add (.add (.mul (.neg (.var 1)) (.var 1)) (.mul (.var 1) (.neg (.var 1)))) (.var 1)) .zero) (.add .zero (.mul (.add (.add (.var 1) (.var 1)) (.neg .one)) (.neg (.var 1)))) (by decide +kernel) :
      -h * h + h * -h + h + 0 = 0 + (h + h + -1) * -h) hA)

/-- Where the shell has no root of `x² + x + 1`, `ν = −3` is not a square. A root `s` of `s² = −3` would give the root
`−h + h s` of `x² + x + 1` in the base. -/
theorem nonsquare (hno : ¬ ∃ a : Shell p, a * a + a + 1 = 0) {h : Shell p} (hh : h + h = 1) (hν : ν + 1 + 1 + 1 = 0) :
    ¬ ∃ s : Shell p, s * s = ν := fun ⟨s, hs⟩ => by
  have hA : h + h + -1 = 0 := by rw [hh, Shell.add_neg]
  have hs' : s * s + -ν = 0 := by rw [hs, Shell.add_neg]
  exact hno ⟨-h + h * s, red3 (RE.sound (look [ν, h, s]) (.add (.add (.mul (.add (.neg (.var 1)) (.mul (.var 1) (.var 2))) (.add (.neg (.var 1)) (.mul (.var 1) (.var 2)))) (.add (.neg (.var 1)) (.mul (.var 1) (.var 2)))) .one) (.add (.add (.add .zero (.mul (.add (.add (.var 1) (.var 1)) (.neg .one)) (.add (.neg (.add (.var 1) .one)) (.neg (.mul (.var 2) (.var 1)))))) (.mul (.add (.add (.add (.var 0) .one) .one) .one) (.mul (.var 1) (.var 1)))) (.mul (.add (.mul (.var 2) (.var 2)) (.neg (.var 0))) (.mul (.var 1) (.var 1)))) (by decide +kernel) :
    (-h + h * s) * (-h + h * s) + (-h + h * s) + 1 =
      0 + (h + h + -1) * (-(h + 1) + -(s * h)) + (ν + 1 + 1 + 1) * (h * h) + (s * s + -ν) * (h * h)) hA hν hs'⟩

theorem three_eq : (3 : Shell p) = 1 + 1 + 1 :=
  Shell.ext (by
    show 3 % p = ((1 % p + 1 % p) % p + 1 % p) % p
    rw [← FRC.Nat.add_mod 1 1 p Pos.pos, ← FRC.Nat.add_mod (1 + 1) 1 p Pos.pos])

theorem neg_three : (-3 : Shell p) + 1 + 1 + 1 = 0 := by
  rw [three_eq]
  exact RE.sound (look ([] : List (Shell p))) (.add (.add (.add (.neg (.add (.add .one .one) .one)) .one) .one) .one) .zero (by decide +kernel)

/-! ## Three-forms over the extension: the group `SU(H)` by elements -/

/-- A `3 × 3` matrix over the extension, by its nine entries. -/
structure M3 (p : Nat) [Pos p] (ν : Shell p) where
  a00 : Ext p ν
  a01 : Ext p ν
  a02 : Ext p ν
  a10 : Ext p ν
  a11 : Ext p ν
  a12 : Ext p ν
  a20 : Ext p ν
  a21 : Ext p ν
  a22 : Ext p ν

theorem mext {A B : M3 p ν} (h00 : A.a00 = B.a00) (h01 : A.a01 = B.a01) (h02 : A.a02 = B.a02)
    (h10 : A.a10 = B.a10) (h11 : A.a11 = B.a11) (h12 : A.a12 = B.a12) (h20 : A.a20 = B.a20) (h21 : A.a21 = B.a21)
    (h22 : A.a22 = B.a22) : A = B := by
  cases A; cases B; cases h00; cases h01; cases h02; cases h10; cases h11; cases h12; cases h20; cases h21; cases h22
  rfl

/-- The product of matrices. -/
def mmul (A B : M3 p ν) : M3 p ν :=
  ⟨A.a00 * B.a00 + A.a01 * B.a10 + A.a02 * B.a20, A.a00 * B.a01 + A.a01 * B.a11 + A.a02 * B.a21,
    A.a00 * B.a02 + A.a01 * B.a12 + A.a02 * B.a22,
   A.a10 * B.a00 + A.a11 * B.a10 + A.a12 * B.a20, A.a10 * B.a01 + A.a11 * B.a11 + A.a12 * B.a21,
    A.a10 * B.a02 + A.a11 * B.a12 + A.a12 * B.a22,
   A.a20 * B.a00 + A.a21 * B.a10 + A.a22 * B.a20, A.a20 * B.a01 + A.a21 * B.a11 + A.a22 * B.a21,
    A.a20 * B.a02 + A.a21 * B.a12 + A.a22 * B.a22⟩

/-- The conjugate transpose `A†`. -/
def dag (A : M3 p ν) : M3 p ν :=
  ⟨Ext.conj A.a00, Ext.conj A.a10, Ext.conj A.a20, Ext.conj A.a01, Ext.conj A.a11, Ext.conj A.a21,
   Ext.conj A.a02, Ext.conj A.a12, Ext.conj A.a22⟩

/-- The determinant, by the first row. -/
def det (A : M3 p ν) : Ext p ν :=
  A.a00 * (A.a11 * A.a22 + -(A.a12 * A.a21)) + -(A.a01 * (A.a10 * A.a22 + -(A.a12 * A.a20))) +
    A.a02 * (A.a10 * A.a21 + -(A.a11 * A.a20))

/-- The adjugate, the transpose of the cofactors. -/
def adj (A : M3 p ν) : M3 p ν :=
  ⟨A.a11 * A.a22 + -(A.a12 * A.a21), A.a02 * A.a21 + -(A.a01 * A.a22), A.a01 * A.a12 + -(A.a02 * A.a11),
   A.a12 * A.a20 + -(A.a10 * A.a22), A.a00 * A.a22 + -(A.a02 * A.a20), A.a02 * A.a10 + -(A.a00 * A.a12),
   A.a10 * A.a21 + -(A.a11 * A.a20), A.a01 * A.a20 + -(A.a00 * A.a21), A.a00 * A.a11 + -(A.a01 * A.a10)⟩

/-- The scalar matrix `c I₃`. -/
def scal (c : Ext p ν) : M3 p ν := ⟨c, 0, 0, 0, c, 0, 0, 0, c⟩

/-- The identity `I₃`. -/
def mone : M3 p ν := scal 1

/-- Every entry multiplied by `c`. -/
def smul (c : Ext p ν) (A : M3 p ν) : M3 p ν :=
  ⟨c * A.a00, c * A.a01, c * A.a02, c * A.a10, c * A.a11, c * A.a12, c * A.a20, c * A.a21, c * A.a22⟩

/-- The nine entries in reading order, the variables of the normaliser. -/
def ents (A : M3 p ν) : List (Ext p ν) := [A.a00, A.a01, A.a02, A.a10, A.a11, A.a12, A.a20, A.a21, A.a22]

/-- `U ∈ SU(H)`: `U` preserves the three-form `H`, `U† H U = H`, and has determinant one. -/
def SU (H U : M3 p ν) : Prop := mmul (mmul (dag U) H) U = H ∧ det U = 1

theorem assoc_entry (x0 x1 x2 b00 b01 b02 b10 b11 b12 b20 b21 b22 y0 y1 y2 : Ext p ν) :
    (x0 * b00 + x1 * b10 + x2 * b20) * y0 + (x0 * b01 + x1 * b11 + x2 * b21) * y1 + (x0 * b02 + x1 * b12 + x2 * b22) * y2 =
      x0 * (b00 * y0 + b01 * y1 + b02 * y2) + x1 * (b10 * y0 + b11 * y1 + b12 * y2) + x2 * (b20 * y0 + b21 * y1 + b22 * y2) :=
  xsound (xlook [x0, x1, x2, b00, b01, b02, b10, b11, b12, b20, b21, b22, y0, y1, y2]) (.add (.add (.mul (.add (.add (.mul (.var 0) (.var 3)) (.mul (.var 1) (.var 6))) (.mul (.var 2) (.var 9))) (.var 12)) (.mul (.add (.add (.mul (.var 0) (.var 4)) (.mul (.var 1) (.var 7))) (.mul (.var 2) (.var 10))) (.var 13))) (.mul (.add (.add (.mul (.var 0) (.var 5)) (.mul (.var 1) (.var 8))) (.mul (.var 2) (.var 11))) (.var 14))) (.add (.add (.mul (.var 0) (.add (.add (.mul (.var 3) (.var 12)) (.mul (.var 4) (.var 13))) (.mul (.var 5) (.var 14)))) (.mul (.var 1) (.add (.add (.mul (.var 6) (.var 12)) (.mul (.var 7) (.var 13))) (.mul (.var 8) (.var 14))))) (.mul (.var 2) (.add (.add (.mul (.var 9) (.var 12)) (.mul (.var 10) (.var 13))) (.mul (.var 11) (.var 14)))))
    (by decide +kernel)

/-- The product of matrices is associative. -/
theorem mmul_assoc (A B C : M3 p ν) : mmul (mmul A B) C = mmul A (mmul B C) :=
  mext (assoc_entry _ _ _ _ _ _ _ _ _ _ _ _ _ _ _) (assoc_entry _ _ _ _ _ _ _ _ _ _ _ _ _ _ _)
    (assoc_entry _ _ _ _ _ _ _ _ _ _ _ _ _ _ _) (assoc_entry _ _ _ _ _ _ _ _ _ _ _ _ _ _ _)
    (assoc_entry _ _ _ _ _ _ _ _ _ _ _ _ _ _ _) (assoc_entry _ _ _ _ _ _ _ _ _ _ _ _ _ _ _)
    (assoc_entry _ _ _ _ _ _ _ _ _ _ _ _ _ _ _) (assoc_entry _ _ _ _ _ _ _ _ _ _ _ _ _ _ _)
    (assoc_entry _ _ _ _ _ _ _ _ _ _ _ _ _ _ _)

theorem conj_dot (a0 a1 a2 b0 b1 b2 : Ext p ν) :
    Ext.conj (a0 * b0 + a1 * b1 + a2 * b2) =
      Ext.conj b0 * Ext.conj a0 + Ext.conj b1 * Ext.conj a1 + Ext.conj b2 * Ext.conj a2 := by
  rw [conj_add, conj_add, Ext.conj_mul, Ext.conj_mul, Ext.conj_mul, Ext.mul_comm (Ext.conj a0),
    Ext.mul_comm (Ext.conj a1), Ext.mul_comm (Ext.conj a2)]

/-- `(A B)† = B† A†`. -/
theorem dag_mul (A B : M3 p ν) : dag (mmul A B) = mmul (dag B) (dag A) :=
  mext (conj_dot _ _ _ _ _ _) (conj_dot _ _ _ _ _ _) (conj_dot _ _ _ _ _ _) (conj_dot _ _ _ _ _ _)
    (conj_dot _ _ _ _ _ _) (conj_dot _ _ _ _ _ _) (conj_dot _ _ _ _ _ _) (conj_dot _ _ _ _ _ _) (conj_dot _ _ _ _ _ _)

/-- The determinant is multiplicative: `det (A B) = det A · det B`. -/
theorem det_mul (A B : M3 p ν) : det (mmul A B) = det A * det B :=
  xsound (xlook (ents A ++ ents B)) (.add (.add (.mul (.add (.add (.mul (.var 0) (.var 9)) (.mul (.var 1) (.var 12))) (.mul (.var 2) (.var 15))) (.add (.mul (.add (.add (.mul (.var 3) (.var 10)) (.mul (.var 4) (.var 13))) (.mul (.var 5) (.var 16))) (.add (.add (.mul (.var 6) (.var 11)) (.mul (.var 7) (.var 14))) (.mul (.var 8) (.var 17)))) (.neg (.mul (.add (.add (.mul (.var 3) (.var 11)) (.mul (.var 4) (.var 14))) (.mul (.var 5) (.var 17))) (.add (.add (.mul (.var 6) (.var 10)) (.mul (.var 7) (.var 13))) (.mul (.var 8) (.var 16))))))) (.neg (.mul (.add (.add (.mul (.var 0) (.var 10)) (.mul (.var 1) (.var 13))) (.mul (.var 2) (.var 16))) (.add (.mul (.add (.add (.mul (.var 3) (.var 9)) (.mul (.var 4) (.var 12))) (.mul (.var 5) (.var 15))) (.add (.add (.mul (.var 6) (.var 11)) (.mul (.var 7) (.var 14))) (.mul (.var 8) (.var 17)))) (.neg (.mul (.add (.add (.mul (.var 3) (.var 11)) (.mul (.var 4) (.var 14))) (.mul (.var 5) (.var 17))) (.add (.add (.mul (.var 6) (.var 9)) (.mul (.var 7) (.var 12))) (.mul (.var 8) (.var 15))))))))) (.mul (.add (.add (.mul (.var 0) (.var 11)) (.mul (.var 1) (.var 14))) (.mul (.var 2) (.var 17))) (.add (.mul (.add (.add (.mul (.var 3) (.var 9)) (.mul (.var 4) (.var 12))) (.mul (.var 5) (.var 15))) (.add (.add (.mul (.var 6) (.var 10)) (.mul (.var 7) (.var 13))) (.mul (.var 8) (.var 16)))) (.neg (.mul (.add (.add (.mul (.var 3) (.var 10)) (.mul (.var 4) (.var 13))) (.mul (.var 5) (.var 16))) (.add (.add (.mul (.var 6) (.var 9)) (.mul (.var 7) (.var 12))) (.mul (.var 8) (.var 15)))))))) (.mul (.add (.add (.mul (.var 0) (.add (.mul (.var 4) (.var 8)) (.neg (.mul (.var 5) (.var 7))))) (.neg (.mul (.var 1) (.add (.mul (.var 3) (.var 8)) (.neg (.mul (.var 5) (.var 6))))))) (.mul (.var 2) (.add (.mul (.var 3) (.var 7)) (.neg (.mul (.var 4) (.var 6)))))) (.add (.add (.mul (.var 9) (.add (.mul (.var 13) (.var 17)) (.neg (.mul (.var 14) (.var 16))))) (.neg (.mul (.var 10) (.add (.mul (.var 12) (.var 17)) (.neg (.mul (.var 14) (.var 15))))))) (.mul (.var 11) (.add (.mul (.var 12) (.var 16)) (.neg (.mul (.var 13) (.var 15))))))) (by decide +kernel)

/-- The form carried by a product: `(U V)† H (U V) = V† (U† H U) V`. -/
theorem sandwich (U V H : M3 p ν) :
    mmul (mmul (dag (mmul U V)) H) (mmul U V) = mmul (mmul (dag V) (mmul (mmul (dag U) H) U)) V := by
  rw [dag_mul, mmul_assoc (mmul (dag V) (dag U)) H (mmul U V), mmul_assoc (dag V) (dag U), mmul_assoc (dag V) _ V,
    mmul_assoc (mmul (dag U) H) U V, mmul_assoc (dag U) H (mmul U V)]

theorem e0 (d x y w : Ext p ν) : d * x + 0 * y + 0 * w = d * x :=
  xsound (xlook [d, x, y, w]) (.add (.add (.mul (.var 0) (.var 1)) (.mul .zero (.var 2))) (.mul .zero (.var 3))) (.mul (.var 0) (.var 1)) (by decide +kernel)
theorem e1 (d x y w : Ext p ν) : 0 * x + d * y + 0 * w = d * y :=
  xsound (xlook [d, x, y, w]) (.add (.add (.mul .zero (.var 1)) (.mul (.var 0) (.var 2))) (.mul .zero (.var 3))) (.mul (.var 0) (.var 2)) (by decide +kernel)
theorem e2 (d x y w : Ext p ν) : 0 * x + 0 * y + d * w = d * w :=
  xsound (xlook [d, x, y, w]) (.add (.add (.mul .zero (.var 1)) (.mul .zero (.var 2))) (.mul (.var 0) (.var 3))) (.mul (.var 0) (.var 3)) (by decide +kernel)
theorem f0 (d x y w : Ext p ν) : x * d + y * 0 + w * 0 = d * x :=
  xsound (xlook [d, x, y, w]) (.add (.add (.mul (.var 1) (.var 0)) (.mul (.var 2) .zero)) (.mul (.var 3) .zero)) (.mul (.var 0) (.var 1)) (by decide +kernel)
theorem f1 (d x y w : Ext p ν) : x * 0 + y * d + w * 0 = d * y :=
  xsound (xlook [d, x, y, w]) (.add (.add (.mul (.var 1) .zero) (.mul (.var 2) (.var 0))) (.mul (.var 3) .zero)) (.mul (.var 0) (.var 2)) (by decide +kernel)
theorem f2 (d x y w : Ext p ν) : x * 0 + y * 0 + w * d = d * w :=
  xsound (xlook [d, x, y, w]) (.add (.add (.mul (.var 1) .zero) (.mul (.var 2) .zero)) (.mul (.var 3) (.var 0))) (.mul (.var 0) (.var 3)) (by decide +kernel)

theorem scal_mul (d : Ext p ν) (A : M3 p ν) : mmul (scal d) A = smul d A :=
  mext (e0 _ _ _ _) (e0 _ _ _ _) (e0 _ _ _ _) (e1 _ _ _ _) (e1 _ _ _ _) (e1 _ _ _ _) (e2 _ _ _ _) (e2 _ _ _ _)
    (e2 _ _ _ _)

theorem mul_scal (A : M3 p ν) (d : Ext p ν) : mmul A (scal d) = smul d A :=
  mext (f0 _ _ _ _) (f1 _ _ _ _) (f2 _ _ _ _) (f0 _ _ _ _) (f1 _ _ _ _) (f2 _ _ _ _) (f0 _ _ _ _) (f1 _ _ _ _)
    (f2 _ _ _ _)

theorem smul_smul (c d : Ext p ν) (A : M3 p ν) : smul c (smul d A) = smul (c * d) A :=
  mext (Ext.mul_assoc _ _ _).symm (Ext.mul_assoc _ _ _).symm (Ext.mul_assoc _ _ _).symm (Ext.mul_assoc _ _ _).symm
    (Ext.mul_assoc _ _ _).symm (Ext.mul_assoc _ _ _).symm (Ext.mul_assoc _ _ _).symm (Ext.mul_assoc _ _ _).symm
    (Ext.mul_assoc _ _ _).symm

theorem one_smul (A : M3 p ν) : smul 1 A = A :=
  mext (Ext.one_mul _) (Ext.one_mul _) (Ext.one_mul _) (Ext.one_mul _) (Ext.one_mul _) (Ext.one_mul _) (Ext.one_mul _)
    (Ext.one_mul _) (Ext.one_mul _)

theorem conj_zero : Ext.conj (0 : Ext p ν) = 0 := Ext.ext rfl Shell.neg_zero

theorem conj_one : Ext.conj (1 : Ext p ν) = 1 := Ext.ext rfl Shell.neg_zero

theorem one_cube : (1 : Ext p ν) ^ 3 = 1 :=
  xsound (xlook ([] : List (Ext p ν))) (.mul (.mul (.mul .one .one) .one) .one) .one (by decide +kernel)

theorem dag_scal (c : Ext p ν) : dag (scal c) = scal (Ext.conj c) :=
  mext rfl conj_zero conj_zero conj_zero rfl conj_zero conj_zero conj_zero rfl

theorem det_scal (c : Ext p ν) : det (scal c) = c ^ 3 :=
  xsound (xlook [c]) (.add (.add (.mul (.var 0) (.add (.mul (.var 0) (.var 0)) (.neg (.mul .zero .zero)))) (.neg (.mul .zero (.add (.mul .zero (.var 0)) (.neg (.mul .zero .zero)))))) (.mul .zero (.add (.mul .zero .zero) (.neg (.mul (.var 0) .zero))))) (.mul (.mul (.mul .one (.var 0)) (.var 0)) (.var 0)) (by decide +kernel)

/-- A scalar `c I₃` with `c̄ c = 1` and `c³ = 1` lies in `SU(H)` for every three-form `H`. -/
theorem scal_SU (H : M3 p ν) {c : Ext p ν} (hu : Ext.conj c * c = 1) (h3 : c ^ 3 = 1) : SU H (scal c) := by
  refine ⟨?_, by rw [det_scal, h3]⟩
  rw [dag_scal, scal_mul, mul_scal, smul_smul, Ext.mul_comm, hu, one_smul]

/-- `U adj U = det U · I₃`. -/
theorem mul_adj (U : M3 p ν) : mmul U (adj U) = scal (det U) :=
  mext (xsound (xlook (ents U)) (.add (.add (.mul (.var 0) (.add (.mul (.var 4) (.var 8)) (.neg (.mul (.var 5) (.var 7))))) (.mul (.var 1) (.add (.mul (.var 5) (.var 6)) (.neg (.mul (.var 3) (.var 8)))))) (.mul (.var 2) (.add (.mul (.var 3) (.var 7)) (.neg (.mul (.var 4) (.var 6)))))) (.add (.add (.mul (.var 0) (.add (.mul (.var 4) (.var 8)) (.neg (.mul (.var 5) (.var 7))))) (.neg (.mul (.var 1) (.add (.mul (.var 3) (.var 8)) (.neg (.mul (.var 5) (.var 6))))))) (.mul (.var 2) (.add (.mul (.var 3) (.var 7)) (.neg (.mul (.var 4) (.var 6)))))) (by decide +kernel))
    (xsound (xlook (ents U)) (.add (.add (.mul (.var 0) (.add (.mul (.var 2) (.var 7)) (.neg (.mul (.var 1) (.var 8))))) (.mul (.var 1) (.add (.mul (.var 0) (.var 8)) (.neg (.mul (.var 2) (.var 6)))))) (.mul (.var 2) (.add (.mul (.var 1) (.var 6)) (.neg (.mul (.var 0) (.var 7)))))) .zero (by decide +kernel))
    (xsound (xlook (ents U)) (.add (.add (.mul (.var 0) (.add (.mul (.var 1) (.var 5)) (.neg (.mul (.var 2) (.var 4))))) (.mul (.var 1) (.add (.mul (.var 2) (.var 3)) (.neg (.mul (.var 0) (.var 5)))))) (.mul (.var 2) (.add (.mul (.var 0) (.var 4)) (.neg (.mul (.var 1) (.var 3)))))) .zero (by decide +kernel))
    (xsound (xlook (ents U)) (.add (.add (.mul (.var 3) (.add (.mul (.var 4) (.var 8)) (.neg (.mul (.var 5) (.var 7))))) (.mul (.var 4) (.add (.mul (.var 5) (.var 6)) (.neg (.mul (.var 3) (.var 8)))))) (.mul (.var 5) (.add (.mul (.var 3) (.var 7)) (.neg (.mul (.var 4) (.var 6)))))) .zero (by decide +kernel))
    (xsound (xlook (ents U)) (.add (.add (.mul (.var 3) (.add (.mul (.var 2) (.var 7)) (.neg (.mul (.var 1) (.var 8))))) (.mul (.var 4) (.add (.mul (.var 0) (.var 8)) (.neg (.mul (.var 2) (.var 6)))))) (.mul (.var 5) (.add (.mul (.var 1) (.var 6)) (.neg (.mul (.var 0) (.var 7)))))) (.add (.add (.mul (.var 0) (.add (.mul (.var 4) (.var 8)) (.neg (.mul (.var 5) (.var 7))))) (.neg (.mul (.var 1) (.add (.mul (.var 3) (.var 8)) (.neg (.mul (.var 5) (.var 6))))))) (.mul (.var 2) (.add (.mul (.var 3) (.var 7)) (.neg (.mul (.var 4) (.var 6)))))) (by decide +kernel))
    (xsound (xlook (ents U)) (.add (.add (.mul (.var 3) (.add (.mul (.var 1) (.var 5)) (.neg (.mul (.var 2) (.var 4))))) (.mul (.var 4) (.add (.mul (.var 2) (.var 3)) (.neg (.mul (.var 0) (.var 5)))))) (.mul (.var 5) (.add (.mul (.var 0) (.var 4)) (.neg (.mul (.var 1) (.var 3)))))) .zero (by decide +kernel))
    (xsound (xlook (ents U)) (.add (.add (.mul (.var 6) (.add (.mul (.var 4) (.var 8)) (.neg (.mul (.var 5) (.var 7))))) (.mul (.var 7) (.add (.mul (.var 5) (.var 6)) (.neg (.mul (.var 3) (.var 8)))))) (.mul (.var 8) (.add (.mul (.var 3) (.var 7)) (.neg (.mul (.var 4) (.var 6)))))) .zero (by decide +kernel))
    (xsound (xlook (ents U)) (.add (.add (.mul (.var 6) (.add (.mul (.var 2) (.var 7)) (.neg (.mul (.var 1) (.var 8))))) (.mul (.var 7) (.add (.mul (.var 0) (.var 8)) (.neg (.mul (.var 2) (.var 6)))))) (.mul (.var 8) (.add (.mul (.var 1) (.var 6)) (.neg (.mul (.var 0) (.var 7)))))) .zero (by decide +kernel))
    (xsound (xlook (ents U)) (.add (.add (.mul (.var 6) (.add (.mul (.var 1) (.var 5)) (.neg (.mul (.var 2) (.var 4))))) (.mul (.var 7) (.add (.mul (.var 2) (.var 3)) (.neg (.mul (.var 0) (.var 5)))))) (.mul (.var 8) (.add (.mul (.var 0) (.var 4)) (.neg (.mul (.var 1) (.var 3)))))) (.add (.add (.mul (.var 0) (.add (.mul (.var 4) (.var 8)) (.neg (.mul (.var 5) (.var 7))))) (.neg (.mul (.var 1) (.add (.mul (.var 3) (.var 8)) (.neg (.mul (.var 5) (.var 6))))))) (.mul (.var 2) (.add (.mul (.var 3) (.var 7)) (.neg (.mul (.var 4) (.var 6)))))) (by decide +kernel))

/-- `adj U · U = det U · I₃`. -/
theorem adj_mul (U : M3 p ν) : mmul (adj U) U = scal (det U) :=
  mext (xsound (xlook (ents U)) (.add (.add (.mul (.add (.mul (.var 4) (.var 8)) (.neg (.mul (.var 5) (.var 7)))) (.var 0)) (.mul (.add (.mul (.var 2) (.var 7)) (.neg (.mul (.var 1) (.var 8)))) (.var 3))) (.mul (.add (.mul (.var 1) (.var 5)) (.neg (.mul (.var 2) (.var 4)))) (.var 6))) (.add (.add (.mul (.var 0) (.add (.mul (.var 4) (.var 8)) (.neg (.mul (.var 5) (.var 7))))) (.neg (.mul (.var 1) (.add (.mul (.var 3) (.var 8)) (.neg (.mul (.var 5) (.var 6))))))) (.mul (.var 2) (.add (.mul (.var 3) (.var 7)) (.neg (.mul (.var 4) (.var 6)))))) (by decide +kernel))
    (xsound (xlook (ents U)) (.add (.add (.mul (.add (.mul (.var 4) (.var 8)) (.neg (.mul (.var 5) (.var 7)))) (.var 1)) (.mul (.add (.mul (.var 2) (.var 7)) (.neg (.mul (.var 1) (.var 8)))) (.var 4))) (.mul (.add (.mul (.var 1) (.var 5)) (.neg (.mul (.var 2) (.var 4)))) (.var 7))) .zero (by decide +kernel))
    (xsound (xlook (ents U)) (.add (.add (.mul (.add (.mul (.var 4) (.var 8)) (.neg (.mul (.var 5) (.var 7)))) (.var 2)) (.mul (.add (.mul (.var 2) (.var 7)) (.neg (.mul (.var 1) (.var 8)))) (.var 5))) (.mul (.add (.mul (.var 1) (.var 5)) (.neg (.mul (.var 2) (.var 4)))) (.var 8))) .zero (by decide +kernel))
    (xsound (xlook (ents U)) (.add (.add (.mul (.add (.mul (.var 5) (.var 6)) (.neg (.mul (.var 3) (.var 8)))) (.var 0)) (.mul (.add (.mul (.var 0) (.var 8)) (.neg (.mul (.var 2) (.var 6)))) (.var 3))) (.mul (.add (.mul (.var 2) (.var 3)) (.neg (.mul (.var 0) (.var 5)))) (.var 6))) .zero (by decide +kernel))
    (xsound (xlook (ents U)) (.add (.add (.mul (.add (.mul (.var 5) (.var 6)) (.neg (.mul (.var 3) (.var 8)))) (.var 1)) (.mul (.add (.mul (.var 0) (.var 8)) (.neg (.mul (.var 2) (.var 6)))) (.var 4))) (.mul (.add (.mul (.var 2) (.var 3)) (.neg (.mul (.var 0) (.var 5)))) (.var 7))) (.add (.add (.mul (.var 0) (.add (.mul (.var 4) (.var 8)) (.neg (.mul (.var 5) (.var 7))))) (.neg (.mul (.var 1) (.add (.mul (.var 3) (.var 8)) (.neg (.mul (.var 5) (.var 6))))))) (.mul (.var 2) (.add (.mul (.var 3) (.var 7)) (.neg (.mul (.var 4) (.var 6)))))) (by decide +kernel))
    (xsound (xlook (ents U)) (.add (.add (.mul (.add (.mul (.var 5) (.var 6)) (.neg (.mul (.var 3) (.var 8)))) (.var 2)) (.mul (.add (.mul (.var 0) (.var 8)) (.neg (.mul (.var 2) (.var 6)))) (.var 5))) (.mul (.add (.mul (.var 2) (.var 3)) (.neg (.mul (.var 0) (.var 5)))) (.var 8))) .zero (by decide +kernel))
    (xsound (xlook (ents U)) (.add (.add (.mul (.add (.mul (.var 3) (.var 7)) (.neg (.mul (.var 4) (.var 6)))) (.var 0)) (.mul (.add (.mul (.var 1) (.var 6)) (.neg (.mul (.var 0) (.var 7)))) (.var 3))) (.mul (.add (.mul (.var 0) (.var 4)) (.neg (.mul (.var 1) (.var 3)))) (.var 6))) .zero (by decide +kernel))
    (xsound (xlook (ents U)) (.add (.add (.mul (.add (.mul (.var 3) (.var 7)) (.neg (.mul (.var 4) (.var 6)))) (.var 1)) (.mul (.add (.mul (.var 1) (.var 6)) (.neg (.mul (.var 0) (.var 7)))) (.var 4))) (.mul (.add (.mul (.var 0) (.var 4)) (.neg (.mul (.var 1) (.var 3)))) (.var 7))) .zero (by decide +kernel))
    (xsound (xlook (ents U)) (.add (.add (.mul (.add (.mul (.var 3) (.var 7)) (.neg (.mul (.var 4) (.var 6)))) (.var 2)) (.mul (.add (.mul (.var 1) (.var 6)) (.neg (.mul (.var 0) (.var 7)))) (.var 5))) (.mul (.add (.mul (.var 0) (.var 4)) (.neg (.mul (.var 1) (.var 3)))) (.var 8))) (.add (.add (.mul (.var 0) (.add (.mul (.var 4) (.var 8)) (.neg (.mul (.var 5) (.var 7))))) (.neg (.mul (.var 1) (.add (.mul (.var 3) (.var 8)) (.neg (.mul (.var 5) (.var 6))))))) (.mul (.var 2) (.add (.mul (.var 3) (.var 7)) (.neg (.mul (.var 4) (.var 6)))))) (by decide +kernel))

/-- `det (adj U) = (det U)²`. -/
theorem det_adj (U : M3 p ν) : det (adj U) = det U * det U :=
  xsound (xlook (ents U)) (.add (.add (.mul (.add (.mul (.var 4) (.var 8)) (.neg (.mul (.var 5) (.var 7)))) (.add (.mul (.add (.mul (.var 0) (.var 8)) (.neg (.mul (.var 2) (.var 6)))) (.add (.mul (.var 0) (.var 4)) (.neg (.mul (.var 1) (.var 3))))) (.neg (.mul (.add (.mul (.var 2) (.var 3)) (.neg (.mul (.var 0) (.var 5)))) (.add (.mul (.var 1) (.var 6)) (.neg (.mul (.var 0) (.var 7)))))))) (.neg (.mul (.add (.mul (.var 2) (.var 7)) (.neg (.mul (.var 1) (.var 8)))) (.add (.mul (.add (.mul (.var 5) (.var 6)) (.neg (.mul (.var 3) (.var 8)))) (.add (.mul (.var 0) (.var 4)) (.neg (.mul (.var 1) (.var 3))))) (.neg (.mul (.add (.mul (.var 2) (.var 3)) (.neg (.mul (.var 0) (.var 5)))) (.add (.mul (.var 3) (.var 7)) (.neg (.mul (.var 4) (.var 6)))))))))) (.mul (.add (.mul (.var 1) (.var 5)) (.neg (.mul (.var 2) (.var 4)))) (.add (.mul (.add (.mul (.var 5) (.var 6)) (.neg (.mul (.var 3) (.var 8)))) (.add (.mul (.var 1) (.var 6)) (.neg (.mul (.var 0) (.var 7))))) (.neg (.mul (.add (.mul (.var 0) (.var 8)) (.neg (.mul (.var 2) (.var 6)))) (.add (.mul (.var 3) (.var 7)) (.neg (.mul (.var 4) (.var 6))))))))) (.mul (.add (.add (.mul (.var 0) (.add (.mul (.var 4) (.var 8)) (.neg (.mul (.var 5) (.var 7))))) (.neg (.mul (.var 1) (.add (.mul (.var 3) (.var 8)) (.neg (.mul (.var 5) (.var 6))))))) (.mul (.var 2) (.add (.mul (.var 3) (.var 7)) (.neg (.mul (.var 4) (.var 6)))))) (.add (.add (.mul (.var 0) (.add (.mul (.var 4) (.var 8)) (.neg (.mul (.var 5) (.var 7))))) (.neg (.mul (.var 1) (.add (.mul (.var 3) (.var 8)) (.neg (.mul (.var 5) (.var 6))))))) (.mul (.var 2) (.add (.mul (.var 3) (.var 7)) (.neg (.mul (.var 4) (.var 6))))))) (by decide +kernel)

/-- **G4, the group of a three-form, by elements.** For every three-form `H` over the extension, the set `SU(H)` of the
`U` with `U† H U = H` and `det U = 1` holds the identity and every scalar `c I₃` with `c̄ c = 1` and `c³ = 1`. It is
closed under the product. Each member's adjugate is a two-sided inverse and a member. The proof never uses `H† = H`, so
it covers the Hermitian forms of the row. -/
theorem su_group (H : M3 p ν) :
    SU H mone ∧
    (∀ c : Ext p ν, Ext.conj c * c = 1 → c ^ 3 = 1 → SU H (scal c)) ∧
    (∀ U V : M3 p ν, SU H U → SU H V → SU H (mmul U V)) ∧
    ∀ U : M3 p ν, SU H U → SU H (adj U) ∧ mmul U (adj U) = mone ∧ mmul (adj U) U = mone := by
  have hone : SU H mone := scal_SU H (by rw [conj_one]; exact Ext.one_mul 1) one_cube
  refine ⟨hone, fun c hu h3 => scal_SU H hu h3, fun U V hU hV => ⟨?_, ?_⟩, fun U hU => ?_⟩
  · rw [sandwich, hU.1, hV.1]
  · rw [det_mul, hU.2, hV.2, Ext.one_mul]
  · have hr : mmul U (adj U) = mone := by rw [mul_adj, hU.2]; rfl
    have hl : mmul (adj U) U = mone := by rw [adj_mul, hU.2]; rfl
    have s := sandwich U (adj U) H
    rw [hr, hU.1, hone.1] at s
    exact ⟨⟨s.symm, by rw [det_adj, hU.2, Ext.one_mul]⟩, hr, hl⟩

/-! ## G4: the rank forced as the minimal triality frame -/

/-- **G4, the rank forced as the minimal triality frame.** Take a shell without zero divisors whose base has no root of
`x² + x + 1` (on the Carrier, B5: p00015), with a half `h + h = 1`. Then `−3` is not a square, and `Ext p (−3)` is the
quadratic extension. It holds a root `ω` of `x² + x + 1`. In every extension `Ext p ν`, each such root lies off the
base, with `ω̄ = ω²`, norm one and `ω̄ ω = 1`. So `ω Iₙ` is unitary for every `n`. Its determinant `ωⁿ` is one exactly
when `3 ∣ n`, with `ω¹ ≠ 1`, `ω² ≠ 1` and `ω³ = 1`. The least rank is therefore three, and `ω I₃` lies in `SU(H)` for
every three-form `H`. -/
theorem triality_frame (hdom : ∀ a b : Shell p, a * b = 0 → a = 0 ∨ b = 0)
    (hno : ¬ ∃ a : Shell p, a * a + a + 1 = 0) {h : Shell p} (hh : h + h = 1) :
    (¬ ∃ s : Shell p, s * s = -3) ∧ (∃ ω : Ext p (-3), ω * ω + ω + 1 = 0) ∧
    ∀ (ν : Shell p) (ω : Ext p ν), ω * ω + ω + 1 = 0 →
      ω.im ≠ 0 ∧ Ext.conj ω = ω * ω ∧ Ext.norm ω = 1 ∧ Ext.conj ω * ω = 1 ∧
      ω ^ 1 ≠ 1 ∧ ω ^ 2 ≠ 1 ∧ ω ^ 3 = 1 ∧ (∀ n : Nat, ω ^ n = 1 ↔ n % 3 = 0) ∧
      ∀ H : M3 p ν, SU H (scal ω) := by
  refine ⟨nonsquare hno hh neg_three, ⟨omega h, omega_root hh neg_three⟩, fun ν ω hω => ?_⟩
  obtain ⟨a, b, c, d, e, f, g, k⟩ := triality_scalar hdom hno hω
  exact ⟨a, b, c, d, e, f, g, k, fun H => scal_SU H d g⟩

end FRC.Unitary
