import FrcCore.Shell

/-!
# FrcCore.Ring — a normaliser for ring identities on the shell (the base theme)

An identity between two polynomial expressions over the shell is decided by expanding each side into a positive and a
negative list of monomials, sorting, and comparing; `RE.sound` turns a successful comparison, a kernel computation
(`decide +kernel`), into the equation on the shell. Moved by the ledger migration (task LM24) from
`Theme/Extension.lean`, where the quaternion norm uses it, every name unchanged (`FRC.Shell.Frame.RE`, `look`,
`RE.sound`, `RE.check`), so that every theme can decide its ring identities. No axioms.
-/

namespace FRC
namespace Shell
namespace Frame

variable {p : Nat} [Pos p]

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

/-- The normaliser's test: the two cross lists agree after normalisation. -/
def RE.check (l r : RE) : Bool := pbeq (nfP (l.toP.1 ++ r.toP.2)) (nfP (r.toP.1 ++ l.toP.2))

end Frame
end Shell
end FRC
