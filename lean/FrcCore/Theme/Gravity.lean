import FrcCore.Frame
import FrcCore.Series
import FrcCore.Ring

/-!
# FrcCore.Theme.Gravity — the gravity theme: the horizon's count (ledger migration, task LM27)

The master's block E where its rows are exact. On a frame `(τ; 0, 1, g)` of capacity `κ` (`p = 4κ + 1`):

* the registration sphere `x² + y² + z² = κ²` of `𝔽_p³` has exactly `A = p(p + 1)` points, and so has the sphere at every
  nonzero square rung (`sphere_area`, `sphere_area_rung`): the plane conic `x² + y² = c` has `p − 1` points for `c ≠ 0`
  and `2p − 1` for `c = 0` (`pair_count`), since `−1 = i²` turns it into `uv = c`;
* the record `S = κ(p + 1)` against the area: `4S + 1 = p²` (the record law, the `Q₄` quotient of `𝔽_{p²}^×`, and
  `(Ω − 1)/4` at `p² = Ω`), `S p = κ A` (`S/A = κ/p`), `4 S p = A (p − 1)` (`S = (A/4)(1 − 1/p)`) (`count_identity`, moved
  from 21-gravity's `Gravity.lean`, which keeps the name), and `S = M(M − 1)` on the rate face `M = (p + 1)/2`
  (`record_mass`);
* the response: `S(M + h) = S(M) + p h + h²` (`dS/dM = p`, `T_resp = 1/p`; `record_response`); the registration rate
  `T = A/p³ = (p + 1)/p²` (`temperature_rate`); the two Smarr relations `2 T_resp S = M(1 − 1/p)` and
  `2 T S = M(1 − 1/p²)` (`smarr`);
* the merger law on the count face `A = M(M + 1)`: `ΔA = 2 M₁ M₂` (`merger_area`).

The counts are natural numbers: `count P` counts the residues satisfying `P`, and `nsum` adds natural numbers; both are
invariant under a bijection of the residues (`count_bij`, `nsum_perm`). The identities between natural numbers are
decided by the ring normaliser, read in the natural numbers (`nat_sound`): no shell is built for them. No axioms.
-/

namespace FRC.Grav

open FRC.Shell FRC.Shell.Frame

/-! ## Identities between natural numbers, by the ring normaliser -/

/-- An expression read in the natural numbers (a negation reads `0`; the identities below have none). -/
def natEval (env : Nat → Nat) : RE → Nat
  | .var i => env i
  | .zero => 0
  | .one => 1
  | .add a b => natEval env a + natEval env b
  | .mul a b => natEval env a * natEval env b
  | .neg _ => 0

/-- The expression has no negation. -/
def negFree : RE → Bool
  | .var _ => true
  | .zero => true
  | .one => true
  | .add a b => negFree a && negFree b
  | .mul a b => negFree a && negFree b
  | .neg _ => false

/-- The assignment of natural numbers to the variables `0, 1, 2, …`. -/
def nlook : List Nat → Nat → Nat
  | [], _ => 0
  | x :: _, 0 => x
  | _ :: l, n + 1 => nlook l n

/-- A monomial and a polynomial read in the natural numbers. -/
def mEvalN (env : Nat → Nat) : List Nat → Nat
  | [] => 1
  | i :: m => env i * mEvalN env m

def pEvalN (env : Nat → Nat) : List (List Nat) → Nat
  | [] => 0
  | m :: P => mEvalN env m + pEvalN env P

theorem mEvalN_append (env : Nat → Nat) (m n : List Nat) : mEvalN env (m ++ n) = mEvalN env m * mEvalN env n := by
  induction m with
  | nil => exact (Nat.one_mul _).symm
  | cons i m ih => show env i * mEvalN env (m ++ n) = env i * mEvalN env m * mEvalN env n; rw [ih, FRC.Nat.mul_assoc]

theorem pEvalN_append (env : Nat → Nat) (P Q : List (List Nat)) : pEvalN env (P ++ Q) = pEvalN env P + pEvalN env Q := by
  induction P with
  | nil => exact (Nat.zero_add _).symm
  | cons m P ih => show mEvalN env m + pEvalN env (P ++ Q) = mEvalN env m + pEvalN env P + pEvalN env Q; rw [ih, Nat.add_assoc]

theorem pEvalN_row (env : Nat → Nat) (m : List Nat) (Q : List (List Nat)) : pEvalN env (pRow m Q) = mEvalN env m * pEvalN env Q := by
  induction Q with
  | nil => exact (Nat.mul_zero _).symm
  | cons n Q ih =>
    show mEvalN env (m ++ n) + pEvalN env (pRow m Q) = mEvalN env m * (mEvalN env n + pEvalN env Q)
    rw [ih, mEvalN_append, Nat.left_distrib]

theorem pEvalN_mul (env : Nat → Nat) (P Q : List (List Nat)) : pEvalN env (pMul P Q) = pEvalN env P * pEvalN env Q := by
  induction P with
  | nil => exact (Nat.zero_mul _).symm
  | cons m P ih =>
    show pEvalN env (pRow m Q ++ pMul P Q) = (mEvalN env m + pEvalN env P) * pEvalN env Q
    rw [pEvalN_append, pEvalN_row, ih, FRC.Nat.add_mul]

theorem pMul_nil : ∀ P : List (List Nat), pMul P [] = []
  | [] => rfl
  | _ :: P => by show [] ++ pMul P [] = []; rw [pMul_nil P]; rfl

theorem toP_neg_nil : ∀ e : RE, negFree e = true → e.toP.2 = []
  | .var _, _ => rfl
  | .zero, _ => rfl
  | .one, _ => rfl
  | .add a b, h => by
    show a.toP.2 ++ b.toP.2 = []
    rw [toP_neg_nil a (and_true_left h), toP_neg_nil b (and_true_right h)]; rfl
  | .mul a b, h => by
    show pMul a.toP.1 b.toP.2 ++ pMul a.toP.2 b.toP.1 = []
    rw [toP_neg_nil a (and_true_left h), toP_neg_nil b (and_true_right h), pMul_nil]; rfl
  | .neg _, h => Bool.noConfusion h

theorem natEval_toP (env : Nat → Nat) : ∀ e : RE, negFree e = true → natEval env e = pEvalN env e.toP.1
  | .var i, _ => by show env i = env i * 1 + 0; rw [Nat.mul_one, Nat.add_zero]
  | .zero, _ => rfl
  | .one, _ => rfl
  | .add a b, h => by
    show natEval env a + natEval env b = pEvalN env (a.toP.1 ++ b.toP.1)
    rw [pEvalN_append, ← natEval_toP env a (and_true_left h), ← natEval_toP env b (and_true_right h)]
  | .mul a b, h => by
    show natEval env a * natEval env b = pEvalN env (pMul a.toP.1 b.toP.1 ++ pMul a.toP.2 b.toP.2)
    rw [toP_neg_nil a (and_true_left h), pEvalN_append, pEvalN_mul, ← natEval_toP env a (and_true_left h),
      ← natEval_toP env b (and_true_right h)]
    show _ = _ + pEvalN env (pMul [] b.toP.2)
    rfl

theorem mEvalN_insM (env : Nat → Nat) (i : Nat) (m : List Nat) : mEvalN env (insM i m) = env i * mEvalN env m := by
  induction m with
  | nil => rfl
  | cons j m ih =>
    show mEvalN env (if Nat.ble i j then i :: j :: m else j :: insM i m) = env i * (env j * mEvalN env m)
    cases Nat.ble i j with
    | true => rfl
    | false => show env j * mEvalN env (insM i m) = _; rw [ih, FRC.Nat.mul_left_comm]

theorem mEvalN_sortM (env : Nat → Nat) (m : List Nat) : mEvalN env (sortM m) = mEvalN env m := by
  induction m with
  | nil => rfl
  | cons i m ih => show mEvalN env (insM i (sortM m)) = env i * mEvalN env m; rw [mEvalN_insM, ih]

theorem add_left_comm' (a b c : Nat) : a + (b + c) = b + (a + c) := by
  rw [← Nat.add_assoc, Nat.add_comm a b, Nat.add_assoc]

theorem pEvalN_insP (env : Nat → Nat) (m : List Nat) (P : List (List Nat)) : pEvalN env (insP m P) = mEvalN env m + pEvalN env P := by
  induction P with
  | nil => rfl
  | cons n P ih =>
    show pEvalN env (if lexLe m n then m :: n :: P else n :: insP m P) = mEvalN env m + (mEvalN env n + pEvalN env P)
    cases lexLe m n with
    | true => rfl
    | false => show mEvalN env n + pEvalN env (insP m P) = _; rw [ih, add_left_comm']

theorem pEvalN_nfP (env : Nat → Nat) (P : List (List Nat)) : pEvalN env (nfP P) = pEvalN env P := by
  induction P with
  | nil => rfl
  | cons m P ih => show pEvalN env (insP (sortM m) (nfP P)) = mEvalN env m + pEvalN env P; rw [pEvalN_insP, ih, mEvalN_sortM]

/-- The normaliser's soundness on the natural numbers, read in the naturals themselves. No shell is built, and the
kernel's decision runs over the expressions' monomials, never over the values of their variables (Q20). -/
theorem nat_sound (env : Nat → Nat) (l r : RE) (hl : negFree l = true) (hr : negFree r = true)
    (hb : RE.check l r = true) : natEval env l = natEval env r := by
  have h := pbeq_eq hb
  have e := congrArg (pEvalN env) h
  rw [pEvalN_nfP, pEvalN_nfP, pEvalN_append, pEvalN_append] at e
  have zl : pEvalN env l.toP.2 = 0 := congrArg (pEvalN env) (toP_neg_nil l hl)
  have zr : pEvalN env r.toP.2 = 0 := congrArg (pEvalN env) (toP_neg_nil r hr)
  rw [zl, zr, Nat.add_zero, Nat.add_zero] at e
  rw [natEval_toP env l hl, natEval_toP env r hr]
  exact e

/-! ## Sums of natural numbers -/

/-- `Σ_{l<n} f l` in the natural numbers. -/
def nsum (f : Nat → Nat) : Nat → Nat
  | 0 => 0
  | n + 1 => nsum f n + f n

theorem nsum_congr {f h : Nat → Nat} : ∀ n, (∀ l, l < n → f l = h l) → nsum f n = nsum h n
  | 0, _ => rfl
  | n + 1, e => by
    show nsum f n + f n = nsum h n + h n
    rw [nsum_congr n (fun l hl => e l (Nat.lt_succ_of_lt hl)), e n (Nat.lt_succ_self n)]

theorem nsum_add (f h : Nat → Nat) : ∀ n, nsum (fun l => f l + h l) n = nsum f n + nsum h n
  | 0 => rfl
  | n + 1 => by
    show nsum (fun l => f l + h l) n + (f n + h n) = (nsum f n + f n) + (nsum h n + h n)
    rw [nsum_add f h n, FRC.Nat.add_add_add_comm]

theorem nsum_zero : ∀ n, nsum (fun _ => 0) n = 0
  | 0 => rfl
  | n + 1 => by show nsum (fun _ => 0) n + 0 = 0; rw [nsum_zero n]

theorem nsum_const (c : Nat) : ∀ n, nsum (fun _ => c) n = n * c
  | 0 => (Nat.zero_mul c).symm
  | n + 1 => by show nsum (fun _ => c) n + c = (n + 1) * c; rw [nsum_const c n, Nat.succ_mul]

theorem nsum_mul_left (c : Nat) (f : Nat → Nat) : ∀ n, nsum (fun l => c * f l) n = c * nsum f n
  | 0 => (Nat.mul_zero c).symm
  | n + 1 => by show nsum (fun l => c * f l) n + c * f n = c * (nsum f n + f n); rw [nsum_mul_left c f n, Nat.mul_add]

/-- Double sums commute. -/
theorem nsum_comm (f : Nat → Nat → Nat) (m : Nat) : ∀ n,
    nsum (fun i => nsum (fun j => f i j) m) n = nsum (fun j => nsum (fun i => f i j) n) m
  | 0 => (nsum_zero m).symm
  | n + 1 => by
    show nsum (fun i => nsum (fun j => f i j) m) n + nsum (fun j => f n j) m = _
    rw [nsum_comm f m n, ← nsum_add]
    rfl

/-- Splitting off the first term. -/
theorem nsum_succ' (f : Nat → Nat) : ∀ n, nsum f (n + 1) = f 0 + nsum (fun l => f (l + 1)) n
  | 0 => (Nat.add_comm _ _).trans rfl
  | n + 1 => by
    show nsum f (n + 1) + f (n + 1) = f 0 + (nsum (fun l => f (l + 1)) n + f (n + 1))
    rw [nsum_succ' f n, Nat.add_assoc]

/-- The sum of `F` over a list of indices. -/
def nsumList (F : Nat → Nat) : List Nat → Nat
  | [] => 0
  | a :: l => F a + nsumList F l

theorem nsumList_imageList (F : Nat → Nat) (σ : Nat → Nat) : ∀ n,
    nsumList F (imageList σ n) = nsum (fun j => F (σ j)) n
  | 0 => rfl
  | n + 1 => by
    show F (σ n) + nsumList F (imageList σ n) = nsum (fun j => F (σ j)) n + F (σ n)
    rw [nsumList_imageList F σ n, Nat.add_comm]

theorem nsumList_erase (F : Nat → Nat) {v : Nat} : ∀ {l : List Nat}, Pigeonhole.mem v l →
    nsumList F l = F v + nsumList F (Pigeonhole.erase v l)
  | [], h => absurd h id
  | a :: l, h => by
    exact match Nat.decEq a v with
      | isTrue e => by rw [show Pigeonhole.erase v (a :: l) = l from ite_eq_left e, e]; rfl
      | isFalse e => by
          rw [show Pigeonhole.erase v (a :: l) = a :: Pigeonhole.erase v l from ite_eq_right e]
          have hm : Pigeonhole.mem v l := match h with
            | Or.inl h' => absurd h'.symm e
            | Or.inr h' => h'
          show F a + nsumList F l = F v + (F a + nsumList F (Pigeonhole.erase v l))
          rw [nsumList_erase F hm, Nat.add_left_comm]

theorem nsumList_eq_nsum (F : Nat → Nat) : ∀ (n : Nat) (l : List Nat), Pigeonhole.NoDup l →
    (∀ e, Pigeonhole.mem e l → e < n) → l.length = n → nsumList F l = nsum F n
  | 0, [], _, _, _ => rfl
  | 0, a :: l, _, hb, _ => absurd (hb a (Or.inl rfl)) (Nat.not_lt_zero a)
  | n + 1, l, hnd, hb, hlen => by
    have hm : Pigeonhole.mem n l := Pigeonhole.mem_of_nodup_of_length_lt (n + 1) l hnd hb hlen n (Nat.lt_succ_self n)
    rw [nsumList_erase F hm]
    show F n + nsumList F (Pigeonhole.erase n l) = nsum F n + F n
    rw [Nat.add_comm]
    have hb' : ∀ e, Pigeonhole.mem e (Pigeonhole.erase n l) → e < n := fun e he =>
      match Nat.lt_or_ge e n with
      | Or.inl hlt => hlt
      | Or.inr hge =>
        have : e = n := Nat.le_antisymm (Nat.le_of_lt_succ (hb e (Pigeonhole.mem_of_mem_erase he))) hge
        absurd (this ▸ he) (Pigeonhole.not_mem_erase_self n hnd)
    have hlen' : (Pigeonhole.erase n l).length = n := by
      have := Pigeonhole.length_erase_of_mem hm; rw [hlen] at this; exact Nat.succ.inj this
    rw [nsumList_eq_nsum F n (Pigeonhole.erase n l) (Pigeonhole.nodup_erase n hnd) hb' hlen']

/-- Permutation invariance: for `σ` injective on `[0, n)` with values below `n`, `Σ_{j<n} F (σ j) = Σ_{l<n} F l`. -/
theorem nsum_perm (F : Nat → Nat) (σ : Nat → Nat) (n : Nat) (hlt : ∀ j, j < n → σ j < n)
    (hinj : ∀ i j, i < n → j < n → σ i = σ j → i = j) :
    nsum (fun j => F (σ j)) n = nsum F n := by
  rw [← nsumList_imageList]
  exact nsumList_eq_nsum F n (imageList σ n) (imageList_nodup hinj (Nat.le_refl n))
    (fun e he => match mem_imageList he with | ⟨j, hj, e'⟩ => e' ▸ hlt j hj) (imageList_length σ n)

/-! ## Counting residues -/

theorem natCount_eq_nsum (P : Nat → Prop) [DecidablePred P] : ∀ n, natCount P n = nsum (fun x => if P x then 1 else 0) n
  | 0 => rfl
  | n + 1 => by
    show natCount P n + (if P n then 1 else 0) = nsum (fun x => if P x then 1 else 0) n + (if P n then 1 else 0)
    rw [natCount_eq_nsum P n]

/-- A predicate holding at exactly one point below `n` counts `1`. -/
theorem natCount_single (P : Nat → Prop) [DecidablePred P] {x₀ : Nat} (h₀ : P x₀) :
    ∀ n, x₀ < n → (∀ x, x < n → P x → x = x₀) → natCount P n = 1
  | 0, h, _ => absurd h (Nat.not_lt_zero _)
  | n + 1, h, hu => by
    show natCount P n + (if P n then 1 else 0) = 1
    exact match Nat.decEq x₀ n with
      | isTrue e => by
        have h0 : natCount P n = 0 := natCount_eq_zero P n (fun x hx hP => by
          have h1 := hu x (Nat.lt_succ_of_lt hx) hP
          rw [h1, e] at hx
          exact Nat.lt_irrefl n hx)
        rw [ite_eq_left (e ▸ h₀), h0]
      | isFalse e => by
        rw [natCount_single P h₀ n (Nat.lt_of_le_of_ne (Nat.le_of_lt_succ h) e)
            (fun x hx hP => hu x (Nat.lt_succ_of_lt hx) hP),
          ite_eq_right (fun hn => e (hu n (Nat.lt_succ_self n) hn).symm)]

/-- Disjoint predicates count additively. -/
theorem natCount_or (P Q : Nat → Prop) [DecidablePred P] [DecidablePred Q] (hd : ∀ x, P x → ¬ Q x) :
    ∀ n, natCount (fun x => P x ∨ Q x) n = natCount P n + natCount Q n
  | 0 => rfl
  | n + 1 => by
    show natCount (fun x => P x ∨ Q x) n + (if P n ∨ Q n then 1 else 0)
      = (natCount P n + (if P n then 1 else 0)) + (natCount Q n + (if Q n then 1 else 0))
    rw [natCount_or P Q hd n, FRC.Nat.add_add_add_comm]
    congr 1
    exact match (inferInstance : Decidable (P n)), (inferInstance : Decidable (Q n)) with
      | isTrue hp, _ => by rw [ite_eq_left (Or.inl hp), ite_eq_left hp, ite_eq_right (hd n hp)]
      | isFalse hp, isTrue hq => by rw [ite_eq_left (Or.inr hq), ite_eq_right hp, ite_eq_left hq]
      | isFalse hp, isFalse hq => by
        rw [ite_eq_right (fun h => h.elim hp hq), ite_eq_right hp, ite_eq_right hq]

theorem natCount_true : ∀ n, natCount (fun _ => True) n = n
  | 0 => rfl
  | n + 1 => by show natCount (fun _ => True) n + (if True then 1 else 0) = n + 1; rw [natCount_true n, ite_eq_left trivial]

variable {p : Nat} [Pos p]

/-- The residues of the shell satisfying `P`, counted. -/
def count (P : Shell p → Prop) [DecidablePred P] : Nat := natCount (fun x => P (ofNat x)) p

theorem count_congr {P Q : Shell p → Prop} [DecidablePred P] [DecidablePred Q] (h : ∀ x, P x ↔ Q x) :
    count P = count Q :=
  natCount_congr _ _ p (fun x _ => h (ofNat x))

theorem ofNat_inj {i j : Nat} (hi : i < p) (hj : j < p) (h : (ofNat i : Shell p) = ofNat j) : i = j := by
  have := val_injective h
  rw [val_ofNat, val_ofNat, FRC.Nat.mod_eq_of_lt hi, FRC.Nat.mod_eq_of_lt hj] at this
  exact this

/-- A bijection of the residues preserves counts. -/
theorem count_bij (f g : Shell p → Shell p) (hgf : ∀ x, g (f x) = x) (P : Shell p → Prop) [DecidablePred P] :
    count (fun x => P (f x)) = count P := by
  unfold count
  rw [natCount_eq_nsum, natCount_eq_nsum]
  have e : ∀ x, x < p → (fun x => if P (f (ofNat x)) then 1 else 0) x
      = (fun y => if P (ofNat y) then 1 else 0) ((f (ofNat x)).val) := fun x _ => by
    show (if P (f (ofNat x)) then 1 else 0) = (if P (ofNat (f (ofNat x)).val) then 1 else 0)
    rw [ofNat_val]
  rw [nsum_congr p e]
  exact nsum_perm (fun y => if P (ofNat y) then 1 else 0) (fun x => (f (ofNat x)).val) p (fun x _ => (f (ofNat x)).lt)
    (fun i j hi hj h => ofNat_inj hi hj (by rw [← hgf (ofNat i), ← hgf (ofNat j), ext h]))

/-- Exactly one residue equals `c`. -/
theorem count_eq (c : Shell p) : count (fun x => x = c) = 1 :=
  natCount_single (fun x => (ofNat x : Shell p) = c) (ofNat_val c) p c.lt
    (fun _ hx h => ofNat_inj hx c.lt (h.trans (ofNat_val c).symm))

theorem count_true : count (fun _ : Shell p => True) = p := natCount_true p

theorem count_false : count (fun _ : Shell p => False) = 0 := natCount_eq_zero _ p (fun _ _ h => h)


/-- Equivalent conditions select the same branch. -/
theorem ite_iff {α : Type} {P Q : Prop} [Decidable P] [Decidable Q] (h : P ↔ Q) (x y : α) :
    (if P then x else y) = (if Q then x else y) :=
  match (inferInstance : Decidable P) with
  | isTrue hp => by rw [ite_eq_left hp, ite_eq_left (h.1 hp)]
  | isFalse hp => by rw [ite_eq_right hp, ite_eq_right (fun hq => hp (h.2 hq))]

theorem red1 {L T a X : Shell p} (h : L = T + a * X) (ha : a = 0) : L = T := by
  rw [h, ha, zero_mul, add_zero]

/-! ## The registration sphere (00:E6) -/

section frame
variable {κ : Nat} {g : Shell p}

/-- Through `u = a + i y` (`i² = −1`) the conic row `a² + y² = c` becomes `u (2a − u) = c`: the same count. -/
theorem conic_row (F : Frame p κ g) (a c : Shell p) :
    count (fun y => a * a + y * y = c) = count (fun u => u * (a + a + -u) = c) := by
  have hi : quarterTurn g κ * quarterTurn g κ + 1 = 0 := by rw [F.quarter_turn_sq, neg_add]
  have e : ∀ i y : Shell p, i * i + 1 = 0 → (a + i * y) * (a + a + -(a + i * y)) = a * a + y * y := fun i y h =>
    red1 (Shell.Frame.RE.sound (Shell.Frame.look [a, i, y]) (.mul (.add (.var 0) (.mul (.var 1) (.var 2))) (.add (.add (.var 0) (.var 0)) (.neg (.add (.var 0) (.mul (.var 1) (.var 2)))))) (.add (.add (.mul (.var 0) (.var 0)) (.mul (.var 2) (.var 2))) (.mul (.add (.mul (.var 1) (.var 1)) .one) (.neg (.mul (.var 2) (.var 2))))) (by decide +kernel)) h
  have hP : ∀ y, a * a + y * y = c ↔ (fun u => u * (a + a + -u) = c) (a + quarterTurn g κ * y) := fun y => by
    show a * a + y * y = c ↔ (a + quarterTurn g κ * y) * (a + a + -(a + quarterTurn g κ * y)) = c
    rw [e _ y hi]
  rw [count_congr hP]
  exact count_bij (fun y => a + quarterTurn g κ * y) (fun u => (u + -a) * -(quarterTurn g κ))
    (fun y => red1 ((fun i => Shell.Frame.RE.sound (Shell.Frame.look [a, i, y]) (.mul (.add (.add (.var 0) (.mul (.var 1) (.var 2))) (.neg (.var 0))) (.neg (.var 1))) (.add (.var 2) (.mul (.add (.mul (.var 1) (.var 1)) .one) (.neg (.var 2)))) (by decide +kernel)) (quarterTurn g κ)) hi) (fun u => u * (a + a + -u) = c)

/-- 00:E6 — the plane conic `x² + y² = c` on every frame: `p − 1` points for `c ≠ 0`, `2p − 1` for `c = 0`. -/
theorem conic_count (F : Frame p κ g) (c : Shell p) :
    nsum (fun x => count (fun y => ofNat x * ofNat x + y * y = c)) p = (p - 1) + (if c = 0 then p else 0) := by
  rw [nsum_congr p (fun x _ => conic_row F (ofNat x) c)]
  have hswap : nsum (fun x => count (fun u => u * ((ofNat x : Shell p) + ofNat x + -u) = c)) p
      = nsum (fun u => count (fun a => (ofNat u : Shell p) * (a + a + -(ofNat u)) = c)) p := by
    unfold count
    rw [nsum_congr p (fun x _ => natCount_eq_nsum _ p), nsum_congr p (fun u _ => natCount_eq_nsum _ p)]
    exact nsum_comm (fun x u => if (ofNat u : Shell p) * (ofNat x + ofNat x + -(ofNat u)) = c then 1 else 0) p p
  rw [hswap]
  have hcol : ∀ u, u < p → count (fun a => (ofNat u : Shell p) * (a + a + -(ofNat u)) = c)
      = (fun u => if u = 0 then (if c = 0 then p else 0) else 1) u := fun u hu => by
    show _ = if u = 0 then (if c = 0 then p else 0) else 1
    match Nat.decEq u 0 with
    | isTrue e0 =>
      rw [ite_eq_left e0, e0]
      have h0 : ∀ a : Shell p, (ofNat 0 : Shell p) * (a + a + -(ofNat 0)) = c ↔ c = 0 := fun a =>
        ⟨fun h => h ▸ zero_mul _, fun h => by rw [h]; exact zero_mul _⟩
      rw [count_congr h0]
      match (inferInstance : Decidable (c = 0)) with
      | isTrue hc => rw [ite_eq_left hc, count_congr (fun _ => ⟨fun _ => trivial, fun _ => hc⟩), count_true]
      | isFalse hc => rw [ite_eq_right hc, count_congr (fun _ => ⟨fun h => hc h, fun h => h.elim⟩), count_false]
    | isFalse e0 =>
      rw [ite_eq_right e0]
      have hw : (ofNat u : Shell p) ≠ 0 := fun h => e0 (ofNat_inj hu Pos.pos h)
      have hs : (ofNat u : Shell p) + ofNat u ≠ 0 := by
        rw [← two_mul']; exact F.mul_ne_zero F.two_ne_zero hw
      obtain ⟨t, ht⟩ := F.exists_inv hs
      have h1 : ∀ a : Shell p, (ofNat u : Shell p) * (a + a + -(ofNat u)) = c ↔
          a = (c + ofNat u * ofNat u) * t := fun a => by
        constructor
        · intro h
          calc a = a * ((ofNat u + ofNat u) * t) := by rw [ht, mul_one]
            _ = (ofNat u * (a + a + -(ofNat u)) + ofNat u * ofNat u) * t :=
                (fun a w t => Shell.Frame.RE.sound (Shell.Frame.look [a, w, t]) (.mul (.var 0) (.mul (.add (.var 1) (.var 1)) (.var 2))) (.mul (.add (.mul (.var 1) (.add (.add (.var 0) (.var 0)) (.neg (.var 1)))) (.mul (.var 1) (.var 1))) (.var 2)) (by decide +kernel)) a (ofNat u) t
            _ = (c + ofNat u * ofNat u) * t := by rw [h]
        · intro h
          rw [h]
          calc (ofNat u : Shell p) * ((c + ofNat u * ofNat u) * t + (c + ofNat u * ofNat u) * t + -(ofNat u))
              = (ofNat u + ofNat u) * t * (c + ofNat u * ofNat u) + -(ofNat u * ofNat u) :=
                (fun w t X => Shell.Frame.RE.sound (Shell.Frame.look [w, t, X]) (.mul (.var 0) (.add (.add (.mul (.var 2) (.var 1)) (.mul (.var 2) (.var 1))) (.neg (.var 0)))) (.add (.mul (.mul (.add (.var 0) (.var 0)) (.var 1)) (.var 2)) (.neg (.mul (.var 0) (.var 0)))) (by decide +kernel)) (ofNat u) t (c + ofNat u * ofNat u)
            _ = c := by rw [ht, one_mul, add_assoc, add_neg, add_zero]
      rw [count_congr h1, count_eq]
  rw [nsum_congr p hcol]
  have hp : (p - 1) + 1 = p := FRC.Nat.sub_add_cancel Pos.pos
  calc nsum (fun u => if u = 0 then (if c = 0 then p else 0) else 1) p
      = nsum (fun u => if u = 0 then (if c = 0 then p else 0) else 1) ((p - 1) + 1) := by rw [hp]
    _ = (if c = 0 then p else 0) + nsum (fun _ => 1) (p - 1) := by
        rw [nsum_succ']
        exact congrArg _ (nsum_congr (p - 1) (fun l _ => ite_eq_right (Nat.succ_ne_zero l)))
    _ = (p - 1) + (if c = 0 then p else 0) := by rw [nsum_const, Nat.mul_one, Nat.add_comm]

/-- 00:E6 — the sphere `x² + y² + z² = a` of `𝔽_p³`: `p(p − 1) + p · #{z : z² = a}` points. -/
theorem sphere_count (F : Frame p κ g) (a : Shell p) :
    nsum (fun z => nsum (fun x => count (fun y => ofNat x * ofNat x + y * y + ofNat z * ofNat z = a)) p) p
      = p * (p - 1) + p * count (fun z => z * z = a) := by
  have hz : ∀ z, z < p → nsum (fun x => count (fun y => ofNat x * ofNat x + y * y + ofNat z * ofNat z = a)) p
      = (p - 1) + (if (ofNat z : Shell p) * ofNat z = a then p else 0) := fun z _ => by
    have hc : ∀ x, count (fun y => (ofNat x : Shell p) * ofNat x + y * y + ofNat z * ofNat z = a)
        = count (fun y => (ofNat x : Shell p) * ofNat x + y * y = a + -(ofNat z * ofNat z)) := fun x =>
      count_congr (fun y => ⟨fun h => by rw [← h, add_assoc, add_neg, add_zero],
        fun h => by rw [h, add_assoc, neg_add, add_zero]⟩)
    rw [nsum_congr p (fun x _ => hc x), conic_count F]
    congr 1
    exact ite_iff ⟨fun h => by
        calc (ofNat z : Shell p) * ofNat z = ofNat z * ofNat z + (a + -(ofNat z * ofNat z)) := by rw [h, add_zero]
          _ = a := by rw [add_left_comm, add_neg, add_zero],
      fun h => by rw [h, add_neg]⟩ p 0
  rw [nsum_congr p hz, nsum_add, nsum_const]
  congr 1
  unfold count
  rw [natCount_eq_nsum, ← nsum_mul_left]
  exact nsum_congr p (fun z _ => match (inferInstance : Decidable ((ofNat z : Shell p) * ofNat z = a)) with
    | isTrue h => by rw [ite_eq_left h, ite_eq_left h, Nat.mul_one]
    | isFalse h => by rw [ite_eq_right h, ite_eq_right h, Nat.mul_zero])

/-- A nonzero square has exactly two square roots, `±b`. -/
theorem count_sq (F : Frame p κ g) {b : Shell p} (hb : b ≠ 0) : count (fun z => z * z = b * b) = 2 := by
  have hne : b ≠ -b := fun e => by
    have h2 : b + b = 0 := by
      calc b + b = b + -b := by rw [← e]
        _ = 0 := add_neg b
    rw [← two_mul'] at h2
    exact F.mul_ne_zero F.two_ne_zero hb h2
  have h : ∀ z, z * z = b * b ↔ (z = b ∨ z = -b) := fun z => by
    constructor
    · intro hz
      have e : (z + -b) * (z + b) = 0 := by
        have e1 : (z + -b) * (z + b) = z * z + -(b * b) := (fun z b => Shell.Frame.RE.sound (Shell.Frame.look [z, b]) (.mul (.add (.var 0) (.neg (.var 1))) (.add (.var 0) (.var 1))) (.add (.mul (.var 0) (.var 0)) (.neg (.mul (.var 1) (.var 1)))) (by decide +kernel)) z b
        rw [e1, hz, add_neg]
      match F.mul_eq_zero e with
      | .inl h1 => exact .inl (by
          calc z = z + -b + b := by rw [add_assoc, neg_add, add_zero]
            _ = b := by rw [h1, zero_add])
      | .inr h1 => exact .inr (eq_neg_of_add_eq_zero h1)
    · intro hz
      match hz with
      | .inl e => rw [e]
      | .inr e => rw [e, neg_mul_neg]
  rw [count_congr h]
  unfold count
  rw [natCount_or (fun x => (ofNat x : Shell p) = b) (fun x => (ofNat x : Shell p) = -b)
    (fun x h1 h2 => hne (h1.symm.trans h2))]
  show count (fun x => x = b) + count (fun x => x = -b) = 2
  rw [count_eq, count_eq]

/-- The quadratic form `x² + y² + z²` of `𝔽_p³`. -/
def quad (x y z : Shell p) : Shell p := x * x + y * y + z * z

/-- The points of the sphere `x² + y² + z² = a` in `𝔽_p³`, counted. -/
def sphereCount (p : Nat) [Pos p] (a : Shell p) : Nat :=
  nsum (fun z => nsum (fun x => count (fun y => quad (ofNat x) y (ofNat z) = a)) p) p

/-- 00:E6 — the area of the sphere at every nonzero square rung `a = b²`: `p(p + 1)`. -/
theorem sphere_area_rung (F : Frame p κ g) {b : Shell p} (hb : b ≠ 0) : sphereCount p (b * b) = p * (p + 1) := by
  show nsum (fun z => nsum (fun x => count (fun y => ofNat x * ofNat x + y * y + ofNat z * ofNat z = b * b)) p) p = _
  rw [sphere_count F, count_sq F hb, ← Nat.mul_add]
  have hp : (p - 1) + 1 = p := FRC.Nat.sub_add_cancel Pos.pos
  congr 1
  calc p - 1 + 2 = (p - 1 + 1) + 1 := rfl
    _ = p + 1 := by rw [hp]

/-- 00:E6, 37:C6 — the registration sphere `x² + y² + z² = κ²` at the capacity has area `A = p(p + 1)`. -/
theorem sphere_area (F : Frame p κ g) : sphereCount p (ofNat κ * ofNat κ) = p * (p + 1) := by
  have hκ : κ < p := by
    rw [F.cap]; exact Nat.lt_of_le_of_lt (Nat.le_mul_of_pos_left κ (Nat.zero_lt_succ 3)) (Nat.lt_succ_self _)
  exact sphere_area_rung F (fun h => Nat.ne_of_gt F.cap_pos (ofNat_inj hκ Pos.pos h))

end frame

/-! ## The record, the response and the merger law (00:E6, 00:E7) -/

/-- 00:E6, 00:E7, 21:C13 — the record `S = κ(p + 1) = κ(4κ + 2)` on `p = 4κ + 1`, against the area `A = p(p + 1)`:
`4S + 1 = p²` (the record law: `S = (p² − 1)/4`, the `Q₄` quotient of `𝔽_{p²}^×`, and `S = (Ω − 1)/4` at `p² = Ω`);
`S p = κ A` (`S/A = κ/p`); `4 S p = A (p − 1)` (`S = (A/4)(1 − 1/p)`). Moved here from 21-gravity's `Gravity.lean` (task
LM27), which keeps the name. -/
theorem count_identity (κ : Nat) :
    4 * (κ * (4 * κ + 2)) + 1 = (4 * κ + 1) * (4 * κ + 1) ∧
    κ * (4 * κ + 2) * (4 * κ + 1) = κ * ((4 * κ + 1) * (4 * κ + 2)) ∧
    4 * (κ * (4 * κ + 2)) * (4 * κ + 1) = ((4 * κ + 1) * (4 * κ + 2)) * (4 * κ) :=
  ⟨nat_sound (nlook [κ]) (.add (.mul (.add (.add (.add .one .one) .one) .one) (.mul (.var 0) (.add (.mul (.add (.add (.add .one .one) .one) .one) (.var 0)) (.add .one .one)))) .one) (.mul (.add (.mul (.add (.add (.add .one .one) .one) .one) (.var 0)) .one) (.add (.mul (.add (.add (.add .one .one) .one) .one) (.var 0)) .one)) rfl rfl (by decide +kernel),
   nat_sound (nlook [κ]) (.mul (.mul (.var 0) (.add (.mul (.add (.add (.add .one .one) .one) .one) (.var 0)) (.add .one .one))) (.add (.mul (.add (.add (.add .one .one) .one) .one) (.var 0)) .one)) (.mul (.var 0) (.mul (.add (.mul (.add (.add (.add .one .one) .one) .one) (.var 0)) .one) (.add (.mul (.add (.add (.add .one .one) .one) .one) (.var 0)) (.add .one .one)))) rfl rfl (by decide +kernel),
   nat_sound (nlook [κ]) (.mul (.mul (.add (.add (.add .one .one) .one) .one) (.mul (.var 0) (.add (.mul (.add (.add (.add .one .one) .one) .one) (.var 0)) (.add .one .one)))) (.add (.mul (.add (.add (.add .one .one) .one) .one) (.var 0)) .one)) (.mul (.mul (.add (.mul (.add (.add (.add .one .one) .one) .one) (.var 0)) .one) (.add (.mul (.add (.add (.add .one .one) .one) .one) (.var 0)) (.add .one .one))) (.mul (.add (.add (.add .one .one) .one) .one) (.var 0))) rfl rfl (by decide +kernel)⟩

/-- 00:E7, 37:B5 — the record on the rate face `M = (p + 1)/2 = 2κ + 1`: `S = M (M − 1)`. -/
theorem record_mass (κ : Nat) : κ * (4 * κ + 2) = (2 * κ + 1) * (2 * κ) :=
  nat_sound (nlook [κ]) (.mul (.var 0) (.add (.mul (.add (.add (.add .one .one) .one) .one) (.var 0)) (.add .one .one))) (.mul (.add (.mul (.add .one .one) (.var 0)) .one) (.mul (.add .one .one) (.var 0))) rfl rfl (by decide +kernel)

/-- 00:E7 — the response: `S(M) = M (M − 1)` grows as `S(M + h) = S(M) + (2M − 1) h + h²`, here with `M = m + 1`; on the
rate face `M = 2κ + 1` the coefficient `2M − 1` is `p`: `dS/dM = p` exactly, `T_resp = 1/p`. -/
theorem record_response (m h : Nat) : (m + 1 + h) * (m + h) = (m + 1) * m + (2 * m + 1) * h + h * h :=
  nat_sound (nlook [m, h]) (.mul (.add (.add (.var 0) .one) (.var 1)) (.add (.var 0) (.var 1))) (.add (.add (.mul (.add (.var 0) .one) (.var 0)) (.mul (.add (.mul (.add .one .one) (.var 0)) .one) (.var 1))) (.mul (.var 1) (.var 1))) rfl rfl (by decide +kernel)

/-- 00:E7 — the response on the rate face `M = 2κ + 1` (`m = 2κ`): the coefficient of `h` is `p = 4κ + 1`, so
`dS/dM = p` exactly and `T_resp = 1/p`. -/
theorem record_response_rate (κ h : Nat) :
    (2 * κ + 1 + h) * (2 * κ + h) = (2 * κ + 1) * (2 * κ) + (4 * κ + 1) * h + h * h := by
  have e := record_response (2 * κ) h
  have c : 2 * (2 * κ) + 1 = 4 * κ + 1 := by rw [← FRC.Nat.mul_assoc]
  rw [c] at e
  exact e

/-- 00:E7 — the registration rate `T = A/p³` is `(p + 1)/p²`: `A p² = (p + 1) p³`. -/
theorem temperature_rate (κ : Nat) :
    ((4 * κ + 1) * (4 * κ + 2)) * ((4 * κ + 1) * (4 * κ + 1)) = (4 * κ + 2) * ((4 * κ + 1) * (4 * κ + 1) * (4 * κ + 1)) :=
  nat_sound (nlook [κ]) (.mul (.mul (.add (.mul (.add (.add (.add .one .one) .one) .one) (.var 0)) .one) (.add (.mul (.add (.add (.add .one .one) .one) .one) (.var 0)) (.add .one .one))) (.mul (.add (.mul (.add (.add (.add .one .one) .one) .one) (.var 0)) .one) (.add (.mul (.add (.add (.add .one .one) .one) .one) (.var 0)) .one))) (.mul (.add (.mul (.add (.add (.add .one .one) .one) .one) (.var 0)) (.add .one .one)) (.mul (.mul (.add (.mul (.add (.add (.add .one .one) .one) .one) (.var 0)) .one) (.add (.mul (.add (.add (.add .one .one) .one) .one) (.var 0)) .one)) (.add (.mul (.add (.add (.add .one .one) .one) .one) (.var 0)) .one))) rfl rfl (by decide +kernel)

/-- 00:E7 — the two Smarr relations on the rate face `M = 2κ + 1`: `2 T_resp S = M (1 − 1/p)` with `T_resp = 1/p`, that is
`2S = M (p − 1)`; and `2 T S = M (1 − 1/p²)` with `T = (p + 1)/p²`, that is `2 (p + 1) S = M (p − 1)(p + 1)`. -/
theorem smarr (κ : Nat) :
    2 * (κ * (4 * κ + 2)) = (2 * κ + 1) * (4 * κ) ∧
    2 * (4 * κ + 2) * (κ * (4 * κ + 2)) = (2 * κ + 1) * ((4 * κ) * (4 * κ + 2)) :=
  ⟨nat_sound (nlook [κ]) (.mul (.add .one .one) (.mul (.var 0) (.add (.mul (.add (.add (.add .one .one) .one) .one) (.var 0)) (.add .one .one)))) (.mul (.add (.mul (.add .one .one) (.var 0)) .one) (.mul (.add (.add (.add .one .one) .one) .one) (.var 0))) rfl rfl (by decide +kernel),
   nat_sound (nlook [κ]) (.mul (.mul (.add .one .one) (.add (.mul (.add (.add (.add .one .one) .one) .one) (.var 0)) (.add .one .one))) (.mul (.var 0) (.add (.mul (.add (.add (.add .one .one) .one) .one) (.var 0)) (.add .one .one)))) (.mul (.add (.mul (.add .one .one) (.var 0)) .one) (.mul (.mul (.add (.add (.add .one .one) .one) .one) (.var 0)) (.add (.mul (.add (.add (.add .one .one) .one) .one) (.var 0)) (.add .one .one)))) rfl rfl (by decide +kernel)⟩

/-- 00:E6, 37:C20 — the merger law on the count face `A = M (M + 1)`: `ΔA = 2 M₁ M₂`. -/
theorem merger_area (M₁ M₂ : Nat) :
    (M₁ + M₂) * (M₁ + M₂ + 1) = M₁ * (M₁ + 1) + M₂ * (M₂ + 1) + 2 * (M₁ * M₂) :=
  nat_sound (nlook [M₁, M₂]) (.mul (.add (.var 0) (.var 1)) (.add (.add (.var 0) (.var 1)) .one)) (.add (.add (.mul (.var 0) (.add (.var 0) .one)) (.mul (.var 1) (.add (.var 1) .one))) (.mul (.add .one .one) (.mul (.var 0) (.var 1)))) rfl rfl (by decide +kernel)

/-! ## The register on every frame (21:A1, C2, C5, C16; 00:C1): moved from 21-gravity's `Gravity.lean`, 10 October 2026 -/
section register
variable {κ : Nat} {g : Shell p}

/-- 21:C16, 21:A1 — the calibration congruence on every frame: the full cycle `2π ↦ 4κ = p − 1` is `−1`,
and `(4κ)² = 1`. -/
theorem calibration (F : Frame p κ g) :
    (ofNat (4 * κ) : Shell p) = -1 ∧ (ofNat (4 * κ) : Shell p) * ofNat (4 * κ) = 1 := by
  have h : (ofNat (4 * κ) : Shell p) = -1 := by
    have h2 := F.two_pi
    have e : 2 * Frame.halfPeriod κ = 4 * κ := (FRC.Nat.mul_assoc 2 2 κ).symm
    rw [e] at h2
    exact h2
  exact ⟨h, by rw [h, Shell.neg_mul_neg, Shell.one_mul]⟩

/-- 21:C2, 21:C5, 21:C16 — the register value of the Newton constant on every frame, `G = 2κ`, the half-cycle:
`2G = −1`; `(−2) G = 1` (the face convention `4π ↦ −2`, `G = (−2)⁻¹`); the Gauss count `(2 · 4κ) G = 1`;
`c² = 2⁻¹ = 2κ + 1` with `2c² = 1`; and `G = −c²`. -/
theorem newton_residue (F : Frame p κ g) :
    (2 : Shell p) * ofNat (2 * κ) = -1 ∧ (-2 : Shell p) * ofNat (2 * κ) = 1 ∧
    (2 * ofNat (4 * κ) : Shell p) * ofNat (2 * κ) = 1 ∧
    (2 : Shell p) * ofNat (2 * κ + 1) = 1 ∧ (ofNat (2 * κ) : Shell p) = -ofNat (2 * κ + 1) := by
  obtain ⟨h4, _⟩ := calibration F
  have hG : (2 : Shell p) * ofNat (2 * κ) = -1 := by
    show ofNat 2 * ofNat (2 * κ) = -1
    rw [Frame.ofNat_mul, ← FRC.Nat.mul_assoc]
    exact h4
  have hG' : (-2 : Shell p) * ofNat (2 * κ) = 1 := by
    rw [← Shell.neg_mul, hG, Shell.neg_neg]
  have hc : (2 : Shell p) * ofNat (2 * κ + 1) = 1 := by
    show ofNat 2 * ofNat (2 * κ + 1) = 1
    rw [Frame.ofNat_mul, Nat.mul_add, ← FRC.Nat.mul_assoc, Nat.mul_one, ← Frame.ofNat_add, h4]
    show -1 + ofNat 2 = 1
    rw [show (ofNat 2 : Shell p) = 1 + 1 from Frame.two_eq_one_add_one, ← Shell.add_assoc, Shell.neg_add,
      Shell.zero_add]
  refine ⟨hG, hG', ?_, hc, ?_⟩
  · rw [h4, ← Shell.mul_neg, Shell.mul_one, hG']
  · apply Shell.eq_neg_of_add_eq_zero
    rw [Frame.ofNat_add, ← Nat.add_assoc, F.four_kappa, F.n_eq, ← F.cap]
    exact Frame.ofNat_self

/-- 21:C5 — the action quantum on every frame: `ħ = g^κ` is a member of the quarter-turn pair (`−i`, the
frame's `quarterTurn` being `−g^κ`), `ħ² = −1`; with `c² = 2κ + 1` the residue `r = ħ c²` is a square root of
the capacity, `r² = κ`, and `ħ = 2r` — the paper's `ħ = 2√S` read on the shell. -/
theorem hbar_root (F : Frame p κ g) :
    (g ^ κ) ^ 2 = -1 ∧ (g ^ κ * ofNat (2 * κ + 1)) * (g ^ κ * ofNat (2 * κ + 1)) = ofNat κ ∧
    (2 : Shell p) * (g ^ κ * ofNat (2 * κ + 1)) = g ^ κ := by
  obtain ⟨hq, _⟩ := F.quarter_turn_order
  obtain ⟨_, _, _, hc, _⟩ := newton_residue F
  obtain ⟨h4, _⟩ := calibration F
  have h2r : (2 : Shell p) * (g ^ κ * ofNat (2 * κ + 1)) = g ^ κ := by
    rw [Shell.mul_left_comm, hc, Shell.mul_one]
  refine ⟨hq, ?_, h2r⟩
  -- `4 (r² − κ) = (2r)² − 4κ = ħ² + 1 = 0`, and `4 ≠ 0` on the shell
  have h4ne : (4 : Shell p) ≠ 0 := by
    rw [show (4 : Shell p) = 2 * 2 from (Frame.ofNat_mul 2 2).symm]
    exact F.mul_ne_zero F.two_ne_zero F.two_ne_zero
  have h4κ : (4 : Shell p) * ofNat κ = -1 := by
    show ofNat 4 * ofNat κ = -1
    rw [Frame.ofNat_mul]; exact h4
  have h4r : (4 : Shell p) * ((g ^ κ * ofNat (2 * κ + 1)) * (g ^ κ * ofNat (2 * κ + 1))) = -1 := by
    rw [show (4 : Shell p) = 2 * 2 from (Frame.ofNat_mul 2 2).symm, FRC.Shell.mul_mul_mul_comm, h2r,
      ← Shell.pow_two, hq]
  have key : (4 : Shell p) * ((g ^ κ * ofNat (2 * κ + 1)) * (g ^ κ * ofNat (2 * κ + 1)) + -ofNat κ) = 0 := by
    rw [Shell.left_distrib, h4r, ← Shell.mul_neg, h4κ, Shell.neg_neg]
    exact Shell.neg_add 1
  rcases F.mul_eq_zero key with h | h
  · exact absurd h h4ne
  · have := Shell.eq_neg_of_add_eq_zero h
    rw [Shell.neg_neg] at this
    exact this

end register

/-- 21:A9 — the two-face count: the angular face `κ/S` against the temporal face `κ/(2S)` has ratio `2`
(`κ · 2S = 2 · κS`), and the registration fibre product has `(p − 1)(Ω − 1) = 4 · 4κS` for `p = 4κ + 1`,
`Ω = 4S + 1`. -/
theorem two_face_count (κ S : Nat) :
    κ * (2 * S) = 2 * (κ * S) ∧ (4 * κ) * (4 * S) = 4 * (4 * (κ * S)) := by
  refine ⟨Nat.mul_left_comm κ 2 S, ?_⟩
  rw [Nat.mul_assoc 4 κ, Nat.mul_left_comm κ 4]

/-! ## The values decided by the kernel (21:C2, C5, C13, C16): moved from 21-gravity's `Gravity.lean`, 10 October 2026 -/
section values

/-- 21:C2, 21:C5, 21:C16 — the register on `𝔽₁₃` (`κ = 3`, drive `2`): `4κ = 12 = −1`, `G = 6` with
`2G = −1`, `c² = 7` with `2c² = 1`, `ħ = 2³ = 8 = −i` with `ħ² = −1` (the frame's `quarterTurn` is `5`), the root `r = 8 · 7 = 4` with `r² = 3 = κ` and
`2r = ħ`; and on `𝔽₁₇` (`κ = 4`, drive `3`): `4κ = 16 = −1`, `G = 8`, `c² = 9`, `ħ = 3⁴ = 13 = −i` (`quarterTurn`
`4`), `r = 15` with `r² = 4 = κ`, `2r = 13`. -/
theorem register13_17 :
    (12 : Shell 13) = -1 ∧ 2 * (6 : Shell 13) = -1 ∧ 2 * (7 : Shell 13) = 1 ∧ (6 : Shell 13) = -7 ∧
    (2 : Shell 13) ^ 3 = 8 ∧ (8 : Shell 13) * 8 = -1 ∧ (4 : Shell 13) * 4 = 3 ∧ 2 * (4 : Shell 13) = 8 ∧
    (16 : Shell 17) = -1 ∧ 2 * (8 : Shell 17) = -1 ∧ 2 * (9 : Shell 17) = 1 ∧ (8 : Shell 17) = -9 ∧
    (3 : Shell 17) ^ 4 = 13 ∧ (13 : Shell 17) * 13 = -1 ∧ (15 : Shell 17) * 15 = 4 ∧
    2 * (15 : Shell 17) = 13 := by decide +kernel

/-- 21:C13 — the merger law's instance on the count face `A = M(M + 1)`: `27 811 + 1 596 → 29 407` gives
`ΔA = 2 · 27 811 · 1 596 = 88 772 712`. -/
theorem merger_instance :
    29407 * (29407 + 1) = 27811 * (27811 + 1) + 1596 * (1596 + 1) + 88772712 ∧
    2 * (27811 * 1596) = 88772712 ∧ 27811 + 1596 = 29407 := by decide

/-- 21:C2, 21:C5, 21:C16 — the laboratory Carrier `Ω = 2 408 561` (`S = 602 140`), host-decided: `4S = 2 408 560 = −1`
and `(4S)² = 1` (the calibration congruence); `G = 1 204 280 = 2S` with `2G = −1`, `(−2) G = 1` and the Gauss
count `(2 · 4S) G = 1`; `ħ = 18 688` with `ħ² = −1`, `ħ = 2 · 9 344` and `9 344² = S`. -/
theorem lab_register :
    4 * 602140 = 2408560 ∧ (2408560 : Shell 2408561) = -1 ∧
    (2408560 : Shell 2408561) * 2408560 = 1 ∧
    2 * (1204280 : Shell 2408561) = -1 ∧ (-2 : Shell 2408561) * 1204280 = 1 ∧
    (2 * (2408560 : Shell 2408561)) * 1204280 = 1 ∧
    (18688 : Shell 2408561) * 18688 = -1 ∧ 2 * (9344 : Shell 2408561) = 18688 ∧
    (9344 : Shell 2408561) * 9344 = 602140 := by decide +kernel

end values

end FRC.Grav
