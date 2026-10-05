import FrcCore.Frame
import FrcCore.Orbit

/-!
# FrcCore.Theme.Extension — the quadratic extension of the shell and the quaternion norm (the extension theme, task LM17)

`FRC.Extension.Ext p ν`: the elements `a + b w` of `𝔽_p[w]/(w² − ν)` on components, with addition, the product
`(a + bw)(c + dw) = (ac + νbd) + (ad + bc)w`, powers, Frobenius conjugation, the trace and the norm `N = a² − νb²`;
`z z̄ = N(z)`, conjugation is a ring map and an involution, the norm scales by squares, on the circle `N = 1` the
conjugate is the inverse, and conjugation fixes exactly the prime meridian. One structure for 8-dirac's coefficient
field and 20-rh's extension, which keep their old names as aliases. Then the quaternions over the shell, the
Hamilton product, conjugation and the norm, with the normaliser that decides ring identities on the shell and the
multiplicativity of the norm `N(qr) = N(q) N(r)` (1-algebra's Quaternion.lean, names unchanged). Last, the
Lorentzian plane of the shell: the square classes, the diagonal form `Q_ν = −ν t² + x² + y² + z²`, the boosts
`Λ(γ, b)` with `γ² − νb² = 1` (the norm-one elements of `𝔽_p(√ν)`), their velocities and the counts of the null cone
and of the boosts (3-causality's Causality.lean, task LM20, names unchanged). No axioms.
-/

namespace FRC.Extension

open FRC.Shell

variable {p : Nat} [Pos p]


/-- 8:B1 — an element `a + b w` of the coefficient field, on components. -/
structure Ext (p : Nat) [Pos p] (ν : Shell p) where
  re : Shell p
  im : Shell p

namespace Ext
variable {ν : Shell p}

theorem ext {z z' : Ext p ν} (h1 : z.re = z'.re) (h2 : z.im = z'.im) : z = z' := by
  cases z; cases z'; cases h1; cases h2; rfl

theorem re_congr {a b : Ext p ν} (h : a = b) : a.re = b.re := by cases h; rfl
theorem im_congr {a b : Ext p ν} (h : a = b) : a.im = b.im := by cases h; rfl

instance : DecidableEq (Ext p ν) := fun a b =>
  if h1 : a.re = b.re then
    if h2 : a.im = b.im then isTrue (ext h1 h2) else isFalse (fun e => h2 (by cases e; rfl))
  else isFalse (fun e => h1 (by cases e; rfl))

/-- The base field inside `K`. -/
def ofShell (a : Shell p) : Ext p ν := ⟨a, 0⟩
/-- The adjoined root `w`, `w² = ν`. -/
def w : Ext p ν := ⟨0, 1⟩
instance (n : Nat) : OfNat (Ext p ν) n := ⟨ofShell (OfNat.ofNat n)⟩
instance : Add (Ext p ν) := ⟨fun z z' => ⟨z.re + z'.re, z.im + z'.im⟩⟩
instance : Neg (Ext p ν) := ⟨fun z => ⟨-z.re, -z.im⟩⟩
instance : Mul (Ext p ν) := ⟨fun z z' => ⟨z.re * z'.re + ν * (z.im * z'.im), z.re * z'.im + z.im * z'.re⟩⟩
/-- Frobenius conjugation `a + b w ↦ a − b w`. -/
def conj (z : Ext p ν) : Ext p ν := ⟨z.re, -z.im⟩
/-- The trace `Tr(a + b w) = 2a`. -/
def trace (z : Ext p ν) : Shell p := z.re + z.re
/-- The norm `N(z) = z z̄ = a² − ν b²`. -/
def norm (z : Ext p ν) : Shell p := z.re * z.re + -(ν * (z.im * z.im))
/-- Powers by structural recursion. -/
def pow (z : Ext p ν) : Nat → Ext p ν
  | 0 => 1
  | n + 1 => pow z n * z
instance : Pow (Ext p ν) Nat := ⟨pow⟩

theorem mul_re (z z' : Ext p ν) : (z * z').re = z.re * z'.re + ν * (z.im * z'.im) := rfl
theorem mul_im (z z' : Ext p ν) : (z * z').im = z.re * z'.im + z.im * z'.re := rfl
theorem ofShell_re (a : Shell p) : (ofShell a : Ext p ν).re = a := rfl
theorem ofShell_im (a : Shell p) : (ofShell a : Ext p ν).im = 0 := rfl
theorem conj_re (z : Ext p ν) : (conj z).re = z.re := rfl
theorem conj_im (z : Ext p ν) : (conj z).im = -z.im := rfl

/-- 8:A2 — `w² = ν`. -/
theorem w_sq : (w : Ext p ν) * w = ofShell ν :=
  ext (by show 0 * 0 + ν * (1 * 1) = ν; rw [Shell.zero_mul, Shell.one_mul, Shell.mul_one, Shell.zero_add])
      (by show 0 * 1 + 1 * 0 = 0; rw [Shell.zero_mul, Shell.mul_zero, Shell.zero_add])

/-- 8:A2 — the norm is the product with the conjugate: `z z̄ = N(z)`, a base-field element. -/
theorem mul_conj (z : Ext p ν) : z * conj z = ofShell (norm z) :=
  ext (by show z.re * z.re + ν * (z.im * -z.im) = z.re * z.re + -(ν * (z.im * z.im))
          rw [← Shell.mul_neg, ← Shell.mul_neg])
      (by show z.re * -z.im + z.im * z.re = 0
          rw [← Shell.mul_neg, Shell.mul_comm z.im z.re, Shell.neg_add])

/-- 8:A2 — conjugation is multiplicative (the Frobenius involution is a ring map). -/
theorem conj_mul (z z' : Ext p ν) : conj (z * z') = conj z * conj z' :=
  ext (by show z.re * z'.re + ν * (z.im * z'.im) = z.re * z'.re + ν * (-z.im * -z'.im)
          rw [Shell.neg_mul_neg])
      (by show -(z.re * z'.im + z.im * z'.re) = z.re * -z'.im + -z.im * z'.re
          rw [Shell.neg_add_rev, ← Shell.mul_neg, ← Shell.neg_mul])

/-- 8:B6 — norm growth: `N(c z) = c² N(z)` for every base residue `c`; one chronon of drive multiplies every
norm by `g²`, a square. -/
theorem norm_scale (c : Shell p) (z : Ext p ν) : norm (ofShell c * z) = c * c * norm z := by
  unfold norm
  rw [mul_re, mul_im, ofShell_re, ofShell_im, Shell.zero_mul, Shell.mul_zero, Shell.add_zero,
    Shell.zero_mul, Shell.add_zero, FRC.Shell.mul_mul_mul_comm, FRC.Shell.mul_mul_mul_comm c z.im c z.im,
    Shell.mul_left_comm ν (c * c), Shell.left_distrib, ← Shell.mul_neg]

/-- 20:B9 — conjugation is an involution. -/
theorem conj_conj (z : Ext p ν) : conj (conj z) = z := ext rfl (Shell.neg_neg z.im)

/-- 20:B6 — on the circle `N(z) = 1` the conjugate is the inverse: `z z̄ = 1`. -/
theorem conj_inv_of_norm_one (z : Ext p ν) (hz : norm z = 1) : z * conj z = 1 := by
  rw [mul_conj, hz]; rfl

section frame
variable {κ : Nat} {g : Shell p}

/-- 20:B9 — the fixed locus of conjugation is the prime meridian: `z̄ = z ⟺ b = 0`. -/
theorem fixed_conj (F : Frame p κ g) (z : Ext p ν) : conj z = z ↔ z.im = 0 := by
  constructor
  · intro h
    exact F.eq_zero_of_eq_neg (im_congr h).symm
  · intro h
    exact ext rfl (show -z.im = z.im by rw [h, Shell.neg_zero])

end frame

end Ext

end FRC.Extension

namespace FRC
namespace Shell
namespace Frame

variable {p : Nat} [Pos p]

/-- A quaternion over the shell. -/
structure Quat (p : Nat) [Pos p] where
  a : Shell p
  b : Shell p
  c : Shell p
  d : Shell p

/-- The Hamilton product on the shell. -/
def Quat.mul (q r : Quat p) : Quat p :=
  ⟨(q.a * r.a + -(q.b * r.b)) + (-(q.c * r.c) + -(q.d * r.d)),
   (q.a * r.b + q.b * r.a) + (q.c * r.d + -(q.d * r.c)),
   (q.a * r.c + -(q.b * r.d)) + (q.c * r.a + q.d * r.b),
   (q.a * r.d + q.b * r.c) + (-(q.c * r.b) + q.d * r.a)⟩


/-! ## A normaliser for ring identities on the shell (no axioms)

An identity between two polynomial expressions is decided by expanding each side into a positive and a negative
list of monomials, sorting, and comparing `P_l ++ N_r` with `P_r ++ N_l`; `RE.sound` turns a successful comparison
(a kernel computation, `decide`) into the equation on the shell. -/

inductive RE where
  | var : Nat → RE
  | zero : RE
  | one : RE
  | add : RE → RE → RE
  | mul : RE → RE → RE
  | neg : RE → RE

def RE.eval (env : Nat → Shell p) : RE → Shell p
  | .var i => env i
  | .zero => 0
  | .one => 1
  | .add a b => a.eval env + b.eval env
  | .mul a b => a.eval env * b.eval env
  | .neg a => -(a.eval env)

/-- The assignment of shell values to the variables `0, 1, 2, …` of an expression. -/
def look : List (Shell p) → Nat → Shell p
  | [], _ => 0
  | x :: _, 0 => x
  | _ :: l, n + 1 => look l n

def mEval (env : Nat → Shell p) : List Nat → Shell p
  | [] => 1
  | i :: m => env i * mEval env m

def pEval (env : Nat → Shell p) : List (List Nat) → Shell p
  | [] => 0
  | m :: P => mEval env m + pEval env P

def pRow (m : List Nat) : List (List Nat) → List (List Nat)
  | [] => []
  | n :: Q => (m ++ n) :: pRow m Q

def pMul : List (List Nat) → List (List Nat) → List (List Nat)
  | [], _ => []
  | m :: P, Q => pRow m Q ++ pMul P Q

def RE.toP : RE → List (List Nat) × List (List Nat)
  | .var i => ([[i]], [])
  | .zero => ([], [])
  | .one => ([[]], [])
  | .add a b => (a.toP.1 ++ b.toP.1, a.toP.2 ++ b.toP.2)
  | .mul a b => (pMul a.toP.1 b.toP.1 ++ pMul a.toP.2 b.toP.2, pMul a.toP.1 b.toP.2 ++ pMul a.toP.2 b.toP.1)
  | .neg a => (a.toP.2, a.toP.1)

def insM (i : Nat) : List Nat → List Nat
  | [] => [i]
  | j :: m => if Nat.ble i j then i :: j :: m else j :: insM i m

def sortM : List Nat → List Nat
  | [] => []
  | i :: m => insM i (sortM m)

def lexLe : List Nat → List Nat → Bool
  | [], _ => true
  | _ :: _, [] => false
  | i :: m, j :: n => if i = j then lexLe m n else Nat.ble i j

def insP (m : List Nat) : List (List Nat) → List (List Nat)
  | [] => [m]
  | n :: P => if lexLe m n then m :: n :: P else n :: insP m P

def sortP : List (List Nat) → List (List Nat)
  | [] => []
  | m :: P => insP m (sortP P)

def nfP : List (List Nat) → List (List Nat)
  | [] => []
  | m :: P => insP (sortM m) (nfP P)

theorem mEval_append (env : Nat → Shell p) (m n : List Nat) : mEval env (m ++ n) = mEval env m * mEval env n := by
  induction m with
  | nil => exact (one_mul _).symm
  | cons i m ih => show env i * mEval env (m ++ n) = env i * mEval env m * mEval env n; rw [ih, mul_assoc]

theorem pEval_append (env : Nat → Shell p) (P Q : List (List Nat)) : pEval env (P ++ Q) = pEval env P + pEval env Q := by
  induction P with
  | nil => exact (zero_add _).symm
  | cons m P ih => show mEval env m + pEval env (P ++ Q) = mEval env m + pEval env P + pEval env Q; rw [ih, add_assoc]

theorem pEval_row (env : Nat → Shell p) (m : List Nat) (Q : List (List Nat)) : pEval env (pRow m Q) = mEval env m * pEval env Q := by
  induction Q with
  | nil => exact (mul_zero _).symm
  | cons n Q ih =>
    show mEval env (m ++ n) + pEval env (pRow m Q) = mEval env m * (mEval env n + pEval env Q)
    rw [ih, mEval_append, left_distrib]

theorem pEval_mul (env : Nat → Shell p) (P Q : List (List Nat)) : pEval env (pMul P Q) = pEval env P * pEval env Q := by
  induction P with
  | nil => exact (zero_mul _).symm
  | cons m P ih =>
    show pEval env (pRow m Q ++ pMul P Q) = (mEval env m + pEval env P) * pEval env Q
    rw [pEval_append, pEval_row, ih, right_distrib]

theorem ring_add (A B C D : Shell p) : A + -B + (C + -D) = A + C + -(B + D) := by
  rw [neg_add_rev, add_assoc, add_assoc, add_left_comm (-B) C (-D)]

theorem ring_mul (A B C D : Shell p) : (A + -B) * (C + -D) = A * C + B * D + -(A * D + B * C) := by
  rw [right_distrib, left_distrib, left_distrib, ← mul_neg, ← neg_mul, neg_mul_neg, neg_add_rev, add_assoc, add_assoc]
  refine congrArg (A * C + ·) ?_
  rw [add_comm (-(B * C)) (B * D), add_left_comm]

theorem ring_neg (A B : Shell p) : -(A + -B) = B + -A := by rw [neg_add_rev, neg_neg, add_comm]

theorem RE.toP_eval (env : Nat → Shell p) (e : RE) : e.eval env = pEval env e.toP.1 + -(pEval env e.toP.2) := by
  induction e with
  | var i =>
    show env i = (env i * 1 + 0) + -(0 : Shell p)
    rw [mul_one, add_zero, neg_zero, add_zero]
  | zero => show (0 : Shell p) = 0 + -0; rw [neg_zero, add_zero]
  | one => show (1 : Shell p) = (1 + 0) + -(0 : Shell p); rw [add_zero, neg_zero, add_zero]
  | add a b iha ihb =>
    show a.eval env + b.eval env = pEval env (a.toP.1 ++ b.toP.1) + -(pEval env (a.toP.2 ++ b.toP.2))
    rw [iha, ihb, pEval_append, pEval_append, ring_add]
  | mul a b iha ihb =>
    show a.eval env * b.eval env = pEval env (pMul a.toP.1 b.toP.1 ++ pMul a.toP.2 b.toP.2) +
      -(pEval env (pMul a.toP.1 b.toP.2 ++ pMul a.toP.2 b.toP.1))
    rw [iha, ihb, pEval_append, pEval_append, pEval_mul, pEval_mul, pEval_mul, pEval_mul, ring_mul]
  | neg a iha =>
    show -(a.eval env) = pEval env a.toP.2 + -(pEval env a.toP.1)
    rw [iha, ring_neg]

theorem mEval_insM (env : Nat → Shell p) (i : Nat) (m : List Nat) : mEval env (insM i m) = env i * mEval env m := by
  induction m with
  | nil => rfl
  | cons j m ih =>
    show mEval env (if Nat.ble i j then i :: j :: m else j :: insM i m) = env i * (env j * mEval env m)
    cases Nat.ble i j with
    | true => rfl
    | false => show env j * mEval env (insM i m) = _; rw [ih, mul_left_comm]

theorem mEval_sortM (env : Nat → Shell p) (m : List Nat) : mEval env (sortM m) = mEval env m := by
  induction m with
  | nil => rfl
  | cons i m ih => show mEval env (insM i (sortM m)) = env i * mEval env m; rw [mEval_insM, ih]

theorem pEval_insP (env : Nat → Shell p) (m : List Nat) (P : List (List Nat)) : pEval env (insP m P) = mEval env m + pEval env P := by
  induction P with
  | nil => rfl
  | cons n P ih =>
    show pEval env (if lexLe m n then m :: n :: P else n :: insP m P) = mEval env m + (mEval env n + pEval env P)
    cases lexLe m n with
    | true => rfl
    | false => show mEval env n + pEval env (insP m P) = _; rw [ih, add_left_comm]

theorem pEval_nfP (env : Nat → Shell p) (P : List (List Nat)) : pEval env (nfP P) = pEval env P := by
  induction P with
  | nil => rfl
  | cons m P ih => show pEval env (insP (sortM m) (nfP P)) = mEval env m + pEval env P; rw [pEval_insP, ih, mEval_sortM]

def nbeq : List Nat → List Nat → Bool
  | [], [] => true
  | [], _ :: _ => false
  | _ :: _, [] => false
  | i :: m, j :: n => Nat.beq i j && nbeq m n

def pbeq : List (List Nat) → List (List Nat) → Bool
  | [], [] => true
  | [], _ :: _ => false
  | _ :: _, [] => false
  | m :: P, n :: Q => nbeq m n && pbeq P Q

theorem and_true_left {a b : Bool} (h : (a && b) = true) : a = true := by
  cases a with
  | false => exact absurd h (fun h' => Bool.noConfusion h')
  | true => rfl

theorem and_true_right {a b : Bool} (h : (a && b) = true) : b = true := by
  cases a with
  | false => exact absurd h (fun h' => Bool.noConfusion h')
  | true => exact h

theorem nbeq_eq : ∀ {m n : List Nat}, nbeq m n = true → m = n
  | [], [], _ => rfl
  | i :: m, j :: n, h => by
    have e1 : i = j := Nat.eq_of_beq_eq_true (and_true_left h)
    have e2 : m = n := nbeq_eq (and_true_right h)
    rw [e1, e2]
  | [], _ :: _, h => Bool.noConfusion h
  | _ :: _, [], h => Bool.noConfusion h

theorem pbeq_eq : ∀ {P Q : List (List Nat)}, pbeq P Q = true → P = Q
  | [], [], _ => rfl
  | m :: P, n :: Q, h => by
    have e1 : m = n := nbeq_eq (and_true_left h)
    have e2 : P = Q := pbeq_eq (and_true_right h)
    rw [e1, e2]
  | [], _ :: _, h => Bool.noConfusion h
  | _ :: _, [], h => Bool.noConfusion h

/-- The normaliser's soundness: if the two cross lists agree after normalisation, the two sides are equal on
every assignment of shell values to the variables. -/
theorem RE.sound (env : Nat → Shell p) (l r : RE) (hb : pbeq (nfP (l.toP.1 ++ r.toP.2)) (nfP (r.toP.1 ++ l.toP.2)) = true) :
    l.eval env = r.eval env := by
  have h := pbeq_eq hb
  have h1 : pEval env l.toP.1 + pEval env r.toP.2 = pEval env r.toP.1 + pEval env l.toP.2 := by
    rw [← pEval_append, ← pEval_append, ← pEval_nfP env (l.toP.1 ++ r.toP.2), ← pEval_nfP env (r.toP.1 ++ l.toP.2), h]
  rw [RE.toP_eval env l, RE.toP_eval env r]
  apply add_right_cancel (c := pEval env l.toP.2 + pEval env r.toP.2)
  rw [← add_assoc, add_assoc (pEval env l.toP.1), neg_add, add_zero,
      ← add_assoc, add_comm (pEval env r.toP.1 + -(pEval env r.toP.2)) (pEval env l.toP.2), ← add_assoc,
      add_comm (pEval env l.toP.2) (pEval env r.toP.1), add_assoc, neg_add, add_zero, h1]


/-! ## Quaternions over the shell: conjugation, norm, cross and dot products, and their expression twins -/

def Quat.conj (q : Quat p) : Quat p := ⟨q.a, -q.b, -q.c, -q.d⟩
def Quat.nrm (q : Quat p) : Shell p := q.a * q.a + q.b * q.b + (q.c * q.c + q.d * q.d)
def Quat.vec (q : Quat p) : Quat p := ⟨0, q.b, q.c, q.d⟩
def Quat.sc (s : Shell p) : Quat p := ⟨s, 0, 0, 0⟩
def Quat.smul (s : Shell p) (q : Quat p) : Quat p := ⟨s * q.a, s * q.b, s * q.c, s * q.d⟩
def Quat.add (q r : Quat p) : Quat p := ⟨q.a + r.a, q.b + r.b, q.c + r.c, q.d + r.d⟩
def Quat.neg (q : Quat p) : Quat p := ⟨-q.a, -q.b, -q.c, -q.d⟩
def Quat.cross (v x : Quat p) : Quat p := ⟨0, v.c * x.d + -(v.d * x.c), v.d * x.b + -(v.b * x.d), v.b * x.c + -(v.c * x.b)⟩
def Quat.dot (v x : Quat p) : Shell p := v.b * x.b + v.c * x.c + v.d * x.d
/-- Conjugation by `q`, not yet divided by the norm: `x ↦ q x q̄`. -/
def Quat.conjBy (q x : Quat p) : Quat p := Quat.mul (Quat.mul q x) (Quat.conj q)

theorem Quat.ext4 {q r : Quat p} (ha : q.a = r.a) (hb : q.b = r.b) (hc : q.c = r.c) (hd : q.d = r.d) : q = r :=
  match q, r, ha, hb, hc, hd with
  | ⟨_, _, _, _⟩, ⟨_, _, _, _⟩, rfl, rfl, rfl, rfl => rfl

theorem Quat.pure_eq {x : Quat p} (hx : x.a = 0) : x = ⟨0, x.b, x.c, x.d⟩ :=
  match x, hx with
  | ⟨_, _, _, _⟩, rfl => rfl

structure QR where
  a : RE
  b : RE
  c : RE
  d : RE

def QR.eval (env : Nat → Shell p) (q : QR) : Quat p := ⟨q.a.eval env, q.b.eval env, q.c.eval env, q.d.eval env⟩
def QR.mul (q r : QR) : QR :=
  ⟨.add (.add (.mul q.a r.a) (.neg (.mul q.b r.b))) (.add (.neg (.mul q.c r.c)) (.neg (.mul q.d r.d))),
   .add (.add (.mul q.a r.b) (.mul q.b r.a)) (.add (.mul q.c r.d) (.neg (.mul q.d r.c))),
   .add (.add (.mul q.a r.c) (.neg (.mul q.b r.d))) (.add (.mul q.c r.a) (.mul q.d r.b)),
   .add (.add (.mul q.a r.d) (.mul q.b r.c)) (.add (.neg (.mul q.c r.b)) (.mul q.d r.a))⟩
def QR.conj (q : QR) : QR := ⟨q.a, .neg q.b, .neg q.c, .neg q.d⟩
def QR.nrm (q : QR) : RE := .add (.add (.mul q.a q.a) (.mul q.b q.b)) (.add (.mul q.c q.c) (.mul q.d q.d))
def QR.vec (q : QR) : QR := ⟨.zero, q.b, q.c, q.d⟩
def QR.sc (s : RE) : QR := ⟨s, .zero, .zero, .zero⟩
def QR.smul (s : RE) (q : QR) : QR := ⟨.mul s q.a, .mul s q.b, .mul s q.c, .mul s q.d⟩
def QR.add (q r : QR) : QR := ⟨.add q.a r.a, .add q.b r.b, .add q.c r.c, .add q.d r.d⟩
def QR.neg (q : QR) : QR := ⟨.neg q.a, .neg q.b, .neg q.c, .neg q.d⟩
def QR.cross (v x : QR) : QR :=
  ⟨.zero, .add (.mul v.c x.d) (.neg (.mul v.d x.c)), .add (.mul v.d x.b) (.neg (.mul v.b x.d)), .add (.mul v.b x.c) (.neg (.mul v.c x.b))⟩
def QR.dot (v x : QR) : RE := .add (.add (.mul v.b x.b) (.mul v.c x.c)) (.mul v.d x.d)
def QR.conjBy (q x : QR) : QR := QR.mul (QR.mul q x) (QR.conj q)
/-- A quaternion of variables `i, i+1, i+2, i+3`; a pure one of variables `i, i+1, i+2`. -/
def QR.v (i : Nat) : QR := ⟨.var i, .var (i + 1), .var (i + 2), .var (i + 3)⟩
def QR.pv (i : Nat) : QR := ⟨.zero, .var i, .var (i + 1), .var (i + 2)⟩

def RE.check (l r : RE) : Bool := pbeq (nfP (l.toP.1 ++ r.toP.2)) (nfP (r.toP.1 ++ l.toP.2))
def QR.check (l r : QR) : Bool := RE.check l.a r.a && RE.check l.b r.b && (RE.check l.c r.c && RE.check l.d r.d)

theorem QR.sound (env : Nat → Shell p) (l r : QR) (h : QR.check l r = true) : l.eval env = r.eval env :=
  Quat.ext4 (RE.sound env _ _ (and_true_left (and_true_left h))) (RE.sound env _ _ (and_true_right (and_true_left h)))
    (RE.sound env _ _ (and_true_left (and_true_right h))) (RE.sound env _ _ (and_true_right (and_true_right h)))


/-- 1:E8, the norm is multiplicative: `N(qr) = N(q) N(r)`. -/
theorem nrm_mul (q r : Quat p) : Quat.nrm (Quat.mul q r) = Quat.nrm q * Quat.nrm r :=
  RE.sound (look [q.a, q.b, q.c, q.d, r.a, r.b, r.c, r.d]) (QR.nrm (QR.mul (QR.v 0) (QR.v 4))) (.mul (QR.nrm (QR.v 0)) (QR.nrm (QR.v 4))) (by decide +kernel)

end Frame
end Shell
end FRC

/-! ## The Lorentzian plane of the shell: the square classes, the diagonal form and the boosts (3-causality's
`Causality.lean`, moved by the ledger migration, task LM20, names unchanged) -/

namespace FRC
namespace Shell
namespace Frame

variable {p : Nat} [Pos p] {κ : Nat} {g : Shell p}

/-- `x` is a square: `x = y·y` for some residue `y`. -/
def IsSquare (x : Shell p) : Prop := ∃ y : Shell p, y * y = x

/-- 3:B2 (Thm. nonexistence, first clause) — `c² = ν` makes `ν` a square, so a nonsquare `ν` has no root `c`. -/
theorem no_causal_root {ν : Shell p} (h : ¬IsSquare ν) (c : Shell p) : c * c ≠ ν := fun e => h ⟨c, e⟩

theorem sq_mul (a b : Shell p) : (a * b) * (a * b) = (a * a) * (b * b) := mul_mul_mul_comm a b a b

/-- 3:B2 (Thm. nonexistence, the consequence) — `−c²` is a square on every shell: `−c² = (i·c)²` with `i² = −1`;
so with `c ≠ 0` every coefficient of `−c² t² + x² + y² + z²` is a square and the form is Euclidean. -/
theorem neg_sq_is_square (F : Frame p κ g) (c : Shell p) : IsSquare (-(c * c)) :=
  ⟨quarterTurn g κ * c, by rw [sq_mul, F.quarter_turn_sq, neg_one_mul]⟩

/-- 3:B2 — `−1` itself is a square (`i²`): the paper's hypothesis `p ≡ 1 (mod 4)` in the shell's own terms. -/
theorem neg_one_is_square (F : Frame p κ g) : IsSquare (-1 : Shell p) := ⟨quarterTurn g κ, F.quarter_turn_sq⟩

/-- 3:B3 (Lemma absorption) — if `a_i = w_i² a_0` for `i = 1, 2, 3` then
`a_0 x_0² + a_1 x_1² + a_2 x_2² + a_3 x_3² = a_0 (x_0² + (w_1 x_1)² + (w_2 x_2)² + (w_3 x_3)²)`: a common square
class is absorbed by the rescaling `x_i ↦ w_i x_i`, with no square root of `a_0` itself required. -/
theorem absorb (a0 a1 a2 a3 w1 w2 w3 x0 x1 x2 x3 : Shell p) (h1 : w1 * w1 * a0 = a1) (h2 : w2 * w2 * a0 = a2)
    (h3 : w3 * w3 * a0 = a3) :
    a0 * (x0 * x0) + a1 * (x1 * x1) + a2 * (x2 * x2) + a3 * (x3 * x3) =
    a0 * (x0 * x0 + (w1 * x1) * (w1 * x1) + (w2 * x2) * (w2 * x2) + (w3 * x3) * (w3 * x3)) := by
  rw [← h1, ← h2, ← h3, sq_mul w1 x1, sq_mul w2 x2, sq_mul w3 x3, left_distrib, left_distrib, left_distrib,
    mul_left_comm a0 (w1 * w1), mul_left_comm a0 (w2 * w2), mul_left_comm a0 (w3 * w3),
    mul_assoc (w1 * w1), mul_assoc (w2 * w2), mul_assoc (w3 * w3)]

/-! ### The binary form `x² − ν t²`, the norm of `K = F_p(√ν)` -/

/-- The `(t, x)`-plane form `Q₂(t, x) = x² − ν t²`, the norm `N(x + t√ν)`. -/
def Q2 (ν t x : Shell p) : Shell p := x * x + -(ν * (t * t))

/-- 3:B5 — the plane `x² − ν t²` is anisotropic when `ν` is a nonsquare: `x² = ν t²` forces `t = x = 0`
(else `ν = (x/t)²`).  This is the Witt kernel of the Lorentzian form, its index one. -/
theorem aniso_tx (F : Frame p κ g) {ν : Shell p} (h : ¬IsSquare ν) {t x : Shell p} (e : x * x = ν * (t * t)) :
    t = 0 ∧ x = 0 := by
  match Shell.instDecidableEq t 0 with
  | .isTrue ht =>
    refine ⟨ht, ?_⟩
    rw [ht, mul_zero, mul_zero] at e
    match F.mul_eq_zero e with
    | .inl hx => exact hx
    | .inr hx => exact hx
  | .isFalse ht =>
    match F.exists_inv ht with
    | ⟨s, hs⟩ =>
      exact absurd ⟨x * s, by
        calc (x * s) * (x * s) = (x * x) * (s * s) := sq_mul x s
          _ = ν * ((t * t) * (s * s)) := by rw [e, mul_assoc]
          _ = ν * ((t * s) * (t * s)) := by rw [sq_mul t s]
          _ = ν := by rw [hs, one_mul, mul_one]⟩ h

/-- 3:B5 — the `(y, z)`-plane `y² + z²` is hyperbolic on every shell: `(1, i)` is null. -/
theorem null_yz (F : Frame p κ g) : (1 : Shell p) * 1 + quarterTurn g κ * quarterTurn g κ = 0 := by
  rw [F.quarter_turn_sq, one_mul, add_neg]

/-- 3:B5 — for a square `ν = w²` the `(t, x)`-plane is hyperbolic too: `(1, w)` is null; the form is then
`H ⊥ H`, Witt index two — the Euclidean type. -/
theorem null_tx_of_square (w : Shell p) : Q2 (w * w) 1 w = 0 := by
  unfold Q2; rw [mul_one, mul_one, add_neg]

/-! ### The boosts -/

theorem sq_add (u v : Shell p) : (u + v) * (u + v) = u * u + (u * v + u * v) + v * v := by
  rw [right_distrib, left_distrib, left_distrib, mul_comm v u, ← add_assoc, add_assoc (u * u)]

theorem regroup (P R S T X : Shell p) : P + (X + X) + R + (S + -(X + X) + T) = P + S + T + R := by
  rw [add_add_add_comm, add_assoc P, add_left_comm (X + X), add_neg, add_zero, add_comm R T, ← add_assoc]

/-- The norm is multiplicative: `N((a + b√ν)(c + d√ν)) = N(a + b√ν) N(c + d√ν)`, i.e.
`(ac + νbd)² − ν(ad + bc)² = (a² − νb²)(c² − νd²)` — the identity behind every boost. -/
theorem norm_mul (ν a b c d : Shell p) :
    Q2 ν (a * d + b * c) (a * c + ν * (b * d)) = (a * a + -(ν * (b * b))) * (c * c + -(ν * (d * d))) := by
  unfold Q2
  have cross : (a * c) * (b * d) = (a * d) * (b * c) := by
    rw [mul_assoc, mul_left_comm c, ← mul_assoc, mul_assoc a d, mul_left_comm d, ← mul_assoc a b (d * c), mul_comm d c]
  have e1 : (a * c + ν * (b * d)) * (a * c + ν * (b * d)) =
      (a * c) * (a * c) + (ν * ((a * c) * (b * d)) + ν * ((a * c) * (b * d))) + (ν * ν) * ((b * d) * (b * d)) := by
    rw [sq_add, mul_left_comm (a * c) ν (b * d), sq_mul ν (b * d)]
  have e2 : -(ν * ((a * d + b * c) * (a * d + b * c))) =
      -(ν * ((a * d) * (a * d))) + -(ν * ((a * d) * (b * c)) + ν * ((a * d) * (b * c))) + -(ν * ((b * c) * (b * c))) := by
    rw [sq_add, left_distrib, left_distrib, left_distrib, neg_add_rev, neg_add_rev]
  rw [e1, e2, cross, regroup]
  rw [right_distrib, left_distrib, left_distrib, ← mul_neg, ← neg_mul, neg_mul_neg, ← add_assoc,
    ← sq_mul a c, mul_left_comm (a * a) ν (d * d), ← sq_mul a d, mul_assoc ν (b * b) (c * c), ← sq_mul b c,
    mul_assoc ν (b * b) (ν * (d * d)), mul_left_comm (b * b) ν (d * d), ← mul_assoc ν ν, ← sq_mul b d]

/-- The boost `Λ(γ, b)` of `(t, x)`: `t ↦ γ t + b x`, `x ↦ γ x + ν b t` (multiplication by `γ + b√ν` in `K`). -/
def boostT (_ν γ b t x : Shell p) : Shell p := γ * t + b * x
def boostX (ν γ b t x : Shell p) : Shell p := γ * x + ν * (b * t)

/-- 3:C2 (the finite Lorentz boost) — with `γ² − νb² = 1`, `Λ(γ, b)` preserves `x² − ν t²` exactly, on every shell. -/
theorem boost_preserves {ν γ b : Shell p} (h : γ * γ + -(ν * (b * b)) = 1) (t x : Shell p) :
    Q2 ν (boostT ν γ b t x) (boostX ν γ b t x) = Q2 ν t x := by
  unfold boostT boostX
  have := norm_mul ν γ b x t
  unfold Q2 at this ⊢
  rw [this, h, one_mul]

/-- 3:C2 — boosts compose as their parameters multiply in `K`:
`Λ(γ₁, b₁) Λ(γ₂, b₂) = Λ(γ₁γ₂ + νb₁b₂, γ₁b₂ + b₁γ₂)`, the `t`-row. -/
theorem boost_comp_t (ν γ1 b1 γ2 b2 t x : Shell p) :
    boostT ν γ1 b1 (boostT ν γ2 b2 t x) (boostX ν γ2 b2 t x) =
    boostT ν (γ1 * γ2 + ν * (b1 * b2)) (γ1 * b2 + b1 * γ2) t x := by
  unfold boostT boostX
  rw [left_distrib, left_distrib, right_distrib, right_distrib, ← mul_assoc γ1 γ2 t, ← mul_assoc γ1 b2 x,
    ← mul_assoc b1 γ2 x, mul_left_comm b1 ν (b2 * t), ← mul_assoc b1 b2 t, ← mul_assoc ν (b1 * b2) t,
    add_comm (b1 * γ2 * x) (ν * (b1 * b2) * t), add_add_add_comm]

/-- 3:C2 — the composition, the `x`-row. -/
theorem boost_comp_x (ν γ1 b1 γ2 b2 t x : Shell p) :
    boostX ν γ1 b1 (boostT ν γ2 b2 t x) (boostX ν γ2 b2 t x) =
    boostX ν (γ1 * γ2 + ν * (b1 * b2)) (γ1 * b2 + b1 * γ2) t x := by
  unfold boostT boostX
  rw [left_distrib, left_distrib, left_distrib, right_distrib, right_distrib, left_distrib,
    ← mul_assoc γ1 γ2 x, mul_left_comm γ1 ν (b2 * t), ← mul_assoc γ1 b2 t, ← mul_assoc b1 γ2 t,
    ← mul_assoc b1 b2 x, ← mul_assoc ν (b1 * b2) x,
    add_comm (ν * (b1 * γ2 * t)) (ν * (b1 * b2) * x), add_add_add_comm]

/-- 3:C2 — the norm-one elements form a group: `N(z₁z₂) = N(z₁)N(z₂) = 1`. -/
theorem norm_one_mul {ν γ1 b1 γ2 b2 : Shell p} (h1 : γ1 * γ1 + -(ν * (b1 * b1)) = 1)
    (h2 : γ2 * γ2 + -(ν * (b2 * b2)) = 1) :
    (γ1 * γ2 + ν * (b1 * b2)) * (γ1 * γ2 + ν * (b1 * b2)) +
      -(ν * ((γ1 * b2 + b1 * γ2) * (γ1 * b2 + b1 * γ2))) = 1 := by
  have := norm_mul ν γ1 b1 γ2 b2
  unfold Q2 at this
  rw [this, h1, h2, one_mul]

/-- 3:C3 — `γ ≠ 0` on every boost of the Lorentzian plane: `γ = 0` would give `ν b² = −1`, i.e.
`ν = (i/b)²`, a square. -/
theorem gamma_ne_zero (F : Frame p κ g) {ν γ b : Shell p} (hν : ¬IsSquare ν) (h : γ * γ + -(ν * (b * b)) = 1) :
    γ ≠ 0 := fun hγ => by
  rw [hγ, mul_zero, zero_add] at h
  have hb : b ≠ 0 := fun hb => by
    rw [hb, mul_zero, mul_zero, neg_zero] at h
    exact F.one_ne_zero h.symm
  have hνb : ν * (b * b) = -1 := by rw [← neg_neg (ν * (b * b)), h]
  match F.exists_inv hb with
  | ⟨s, hs⟩ =>
    exact hν ⟨quarterTurn g κ * s, by
      calc quarterTurn g κ * s * (quarterTurn g κ * s) = (quarterTurn g κ * quarterTurn g κ) * (s * s) := sq_mul _ _
        _ = -1 * (s * s) := by rw [F.quarter_turn_sq]
        _ = (ν * (b * b)) * (s * s) := by rw [hνb]
        _ = ν * ((b * s) * (b * s)) := by rw [mul_assoc, sq_mul b s]
        _ = ν := by rw [hs, one_mul, mul_one]⟩

/-- 3:C3 — the velocity of the boost, `v = −νb/γ` (`vγ = −νb`), satisfies `γ² (ν − v²) = ν`: the finite form of
`γ = 1/√(1 − β²)` with `β² = v²/ν`. -/
theorem gamma_velocity {ν γ b v : Shell p} (hz : γ * γ + -(ν * (b * b)) = 1) (hv : v * γ = -(ν * b)) :
    γ * γ * (ν + -(v * v)) = ν := by
  calc γ * γ * (ν + -(v * v)) = γ * γ * ν + -((v * γ) * (v * γ)) := by
        rw [left_distrib, ← mul_neg, sq_mul v γ, mul_comm (v * v)]
    _ = ν * (γ * γ) + -(ν * (ν * (b * b))) := by
        rw [hv, neg_mul_neg, sq_mul ν b, mul_assoc ν ν (b * b), mul_comm (γ * γ) ν]
    _ = ν * (γ * γ + -(ν * (b * b))) := by rw [left_distrib, ← mul_neg]
    _ = ν := by rw [hz, mul_one]

/-- 3:C3 (the velocity addition law) — for boosts with velocities `v₁, v₂` (`v_i γ_i = −ν b_i`) and the composed
boost's velocity `v₁₂`, `v₁₂ (ν + v₁v₂) = ν (v₁ + v₂)`: Einstein's law `v₁₂ = (v₁ + v₂)/(1 + v₁v₂/ν)`, exact. -/
theorem velocity_addition (F : Frame p κ g) {ν γ1 b1 γ2 b2 v1 v2 v12 : Shell p} (hν : ¬IsSquare ν)
    (hz1 : γ1 * γ1 + -(ν * (b1 * b1)) = 1) (hz2 : γ2 * γ2 + -(ν * (b2 * b2)) = 1)
    (hv1 : v1 * γ1 = -(ν * b1)) (hv2 : v2 * γ2 = -(ν * b2))
    (hv12 : v12 * (γ1 * γ2 + ν * (b1 * b2)) = -(ν * (γ1 * b2 + b1 * γ2))) :
    v12 * (ν + v1 * v2) = ν * (v1 + v2) := by
  have hγ : γ1 * γ2 ≠ 0 := F.mul_ne_zero (gamma_ne_zero F hν hz1) (gamma_ne_zero F hν hz2)
  apply F.mul_left_cancel hγ
  calc γ1 * γ2 * (v12 * (ν + v1 * v2)) = v12 * (γ1 * γ2 * ν + (v1 * γ1) * (v2 * γ2)) := by
        rw [mul_left_comm (γ1 * γ2) v12, left_distrib, mul_mul_mul_comm γ1 γ2 v1 v2, mul_comm γ1 v1, mul_comm γ2 v2]
    _ = v12 * (ν * (γ1 * γ2 + ν * (b1 * b2))) := by
        rw [hv1, hv2, neg_mul_neg, mul_mul_mul_comm ν b1 ν b2, mul_assoc ν ν (b1 * b2), mul_comm (γ1 * γ2) ν,
          ← left_distrib]
    _ = ν * (v12 * (γ1 * γ2 + ν * (b1 * b2))) := mul_left_comm _ _ _
    _ = -(ν * (ν * (γ1 * b2 + b1 * γ2))) := by rw [hv12, ← mul_neg]
    _ = ν * (-(γ2 * (ν * b1)) + -(γ1 * (ν * b2))) := by
        rw [mul_left_comm γ2 ν b1, mul_left_comm γ1 ν b2, ← neg_add_rev, ← left_distrib, mul_comm γ2 b1, ← mul_neg,
          add_comm (b1 * γ2) (γ1 * b2)]
    _ = ν * (γ2 * (v1 * γ1) + γ1 * (v2 * γ2)) := by rw [hv1, hv2, ← mul_neg, ← mul_neg]
    _ = γ1 * γ2 * (ν * (v1 + v2)) := by
        rw [mul_left_comm (γ1 * γ2) ν]
        refine congrArg (ν * ·) ?_
        rw [left_distrib, mul_comm v1 γ1, mul_comm v2 γ2, ← mul_assoc γ2 γ1 v1, mul_comm γ2 γ1, ← mul_assoc γ1 γ2 v2]

/-! ### The counts, decided by the kernel -/

/-- `Σ_{i<n} f i` on naturals. -/
def sumTo (f : Nat → Nat) : Nat → Nat
  | 0 => 0
  | n + 1 => sumTo f n + f n

/-- The number of `(t, x, y, z) ∈ [0, p)⁴` with `−ν t² + x² + y² + z² ≡ 0 (mod p)`. -/
def nullCount (p ν : Nat) : Nat :=
  sumTo (fun t => sumTo (fun x => sumTo (fun y => sumTo (fun z =>
    if (x * x + y * y + z * z + (p - ν) * (t * t)) % p = 0 then 1 else 0) p) p) p) p

/-- The number of `(γ, b) ∈ [0, p)²` with `γ² − ν b² ≡ 1 (mod p)`: the boosts. -/
def normOneCount (p ν : Nat) : Nat :=
  sumTo (fun γ => sumTo (fun b => if (γ * γ + (p - ν) * (b * b)) % p = 1 then 1 else 0) p) p

/-- 3:B4, 3:D1 [value] — the null cone of `Q_2` on `𝔽₁₃` has `2041 = 13³ − 13² + 13` points: the elliptic type. -/
theorem null13 : nullCount 13 2 = 2041 := by decide +kernel
/-- 3:B4 [value] — the Euclidean form (`ν = 1`) on `𝔽₁₃` has `2353 = 13³ + 13² − 13` zeros: the hyperbolic type. -/
theorem euclid13 : nullCount 13 1 = 2353 := by decide +kernel
/-- 3:B4 [value] — `𝔽₅`, `ν = 2`: `105 = 5³ − 5² + 5` null points; `ν = 1`: `145`. -/
theorem null5 : nullCount 5 2 = 105 ∧ nullCount 5 1 = 145 := by decide +kernel
/-- 3:B4 [value] — `𝔽₁₇`, `ν = 3`: `4641 = 17³ − 17² + 17` null points. -/
theorem null17 : nullCount 17 3 = 4641 := by decide +kernel
/-- 3:C2, 3:D1 [value] — the boosts number `p + 1`: `6`, `14`, `18`, `30` on `𝔽₅`, `𝔽₁₃`, `𝔽₁₇`, `𝔽₂₉`. -/
theorem normOne_values : normOneCount 5 2 = 6 ∧ normOneCount 13 2 = 14 ∧ normOneCount 17 3 = 18 ∧
    normOneCount 29 2 = 30 := by decide +kernel

end Frame
end Shell
end FRC
