import FrcCore.Nat
import FrcCore.Pigeonhole
import FrcCore.Shell
import FrcCore.Sum
import FrcCore.Reductio

/-!
# 25-göd — incompleteness without infinity: the ledger predicates with no axioms

Predicates of the ledger of *Incompleteness Without Infinity* (tree `25-godel-20260614`). What the paper proves
about a fixed finite structure is finite mathematics, and its counting core is proved here on the kernel alone.

* 25:C1 — on a finite carrier an injective map is onto, so no successor of `Q` lives there.
* 25:C5 — `m + 1` sentences admit no injective numbering into `m` elements.
* 25:D1 — a part with fewer storage states than the structure has elements identifies two of them.
* 25:D4 — a term evaluated by table lookups takes the same value in every table that agrees on the entries
  consulted (the trace argument of the wrap lemma).
* 25:E1 — every closed term over `1` and `+` with `ℓ` leaves has the value `ℓ mod p`.
* 25:E2 — the records of length at most `B` number fewer than `a^(B+1)`, and the certified fraction falls below
  every `1/N`.
* 25:F1, 25:F3 — a formula's truth depends only on variables that occur in it. It depends on fewer coordinates
  than it has symbols, and no sentence has a subformula that reads a tuple as long as the sentence.
* 25:F2 — the diagonal formula is longer than the scale of its bound tuple and than the scale its matrix reads.
* 25:F4 — an injective coding of `a^n` strings into `k`-tuples needs `a^n ≤ m^k`.
* 25:G4 — the uniform pairing prefix decides what the coded prefix decides.

The formulas are those of the signature of `M_p` (`0`, `1`, `+`, `×`). Every declaration prints "does not depend
on any axioms".
-/

namespace FRC.Godel

open FRC.Reductio (allBelow allBelow_congr cons)

/-! ### Boolean bookkeeping, from the definitions -/

theorem or_intro_left {a b : Bool} (h : a = true) : (a || b) = true := by rw [h]; rfl
theorem or_intro_right {a b : Bool} (h : b = true) : (a || b) = true := by rw [h]; cases a <;> rfl
theorem and_true' (c : Bool) : (c && true) = c := by cases c <;> rfl
theorem and_false' (c : Bool) : (c && false) = false := by cases c <;> rfl
theorem and_self' (c : Bool) : (c && c) = c := by cases c <;> rfl
theorem or_false' (c : Bool) : (c || false) = c := by cases c <;> rfl
theorem and_assoc' (a b c : Bool) : ((a && b) && c) = (a && (b && c)) := by cases a <;> rfl

/-! ### 25:C1 — on a finite carrier an injective map is onto -/

/-- 25:C1 (Proposition noQ, the pigeonhole) — on `[0, n)` an injective map is onto: every `z < n` is a value. -/
theorem inj_onto (n : Nat) (S : Nat → Nat) (hS : ∀ x, x < n → S x < n)
    (hinj : ∀ x y, x < n → y < n → S x = S y → x = y) (z : Nat) (hz : z < n) : ∃ x, x < n ∧ S x = z :=
  have hnd := FRC.Shell.imageList_nodup hinj (Nat.le_refl n)
  have hlen := FRC.Shell.imageList_length S n
  have hb : ∀ e, Pigeonhole.mem e (FRC.Shell.imageList S n) → e < n := fun _ he =>
    match FRC.Shell.mem_imageList he with
    | ⟨j, hj, ej⟩ => ej ▸ hS j hj
  FRC.Shell.mem_imageList (Pigeonhole.mem_of_nodup_of_length_lt n _ hnd hb hlen z hz)

/-- 25:C1 (Proposition noQ) — no successor of `Q` on a finite carrier: no map of `[0, n)` into itself is
injective and omits an element, so no finite structure is a model of `Q`. -/
theorem no_finite_successor (n : Nat) (S : Nat → Nat) (hS : ∀ x, x < n → S x < n)
    (hinj : ∀ x y, x < n → y < n → S x = S y → x = y) (z : Nat) (hz : z < n) : ¬ ∀ x, x < n → S x ≠ z :=
  fun hmiss => match inj_onto n S hS hinj z hz with
    | ⟨x, hx, e⟩ => hmiss x hx e

/-! ### 25:D1 — the part cannot hold the whole -/

/-- 25:D1 (Theorem part) — an agent with `R` storage states in a structure of `m > R` elements has no injective
encoding: every reading `ρ : [0, m) → [0, R)` identifies two elements. -/
theorem part_collides {m R : Nat} (hR : R < m) (ρ : Nat → Nat) (hρ : ∀ i, i < m → ρ i < R) :
    ¬ ∀ i j, i < m → j < m → ρ i = ρ j → i = j :=
  fun hinj => FRC.Reductio.no_mirror hR ρ hρ hinj

/-- 25:C5 (Remark Tarski scoped, the count) — `m + 1` sentences, indexed `0, …, m` (the row's sentences
`φ, ¬φ, …, ¬^m φ`), admit no injective numbering into a structure of `m` elements. -/
theorem sentences_outnumber (m : Nat) (g : Nat → Nat) (hg : ∀ i, i < m + 1 → g i < m) :
    ¬ ∀ i j, i < m + 1 → j < m + 1 → g i = g j → i = j :=
  part_collides (Nat.lt_succ_self m) g hg

/-! ### 25:D4, 25:E1 — closed terms, their values, and the entries an evaluation consults -/

/-- Closed terms over one constant and one binary operation: the full binary trees. -/
inductive Tm where
  | one : Tm
  | op : Tm → Tm → Tm

/-- The value of a term in the structure with the constant read as `u` and the operation's table `f`. -/
def val (u : Nat) (f : Nat → Nat → Nat) : Tm → Nat
  | .one => u
  | .op s t => f (val u f s) (val u f t)

/-- `g` agrees with `f` on every table entry the evaluation of the term in `(u, f)` consults. -/
def Agree (u : Nat) (f g : Nat → Nat → Nat) : Tm → Prop
  | .one => True
  | .op s t => Agree u f g s ∧ Agree u f g t ∧ g (val u f s) (val u f t) = f (val u f s) (val u f t)

/-- The number of leaves of a term. -/
def leaves : Tm → Nat
  | .one => 1
  | .op s t => leaves s + leaves t

/-- The number of table lookups the evaluation of a term performs: one per operation. -/
def lookups : Tm → Nat
  | .one => 0
  | .op s t => lookups s + lookups t + 1

/-- 25:D4 (Lemma wrap (2), the trace argument) — a structure that agrees with `M` on the entries the evaluation
consults gives the term the same value: the verification succeeds there step for step. -/
theorem trace_transport (u : Nat) (f g : Nat → Nat → Nat) : ∀ t : Tm, Agree u f g t → val u g t = val u f t
  | .one, _ => rfl
  | .op s t, ⟨hs, ht, e⟩ => by
    show g (val u g s) (val u g t) = f (val u f s) (val u f t)
    rw [trace_transport u f g s hs, trace_transport u f g t ht]; exact e

/-- 25:D4 (Lemma wrap (2), the end sentence) — an equation verified by evaluation in `M` is true in every other
table that agrees with `M` on the cited entries: the certificate keeps its warrant in the small world. -/
theorem wrap_equation (u : Nat) (f g : Nat → Nat → Nat) (s t : Tm) (hs : Agree u f g s) (ht : Agree u f g t)
    (h : val u f s = val u f t) : val u g s = val u g t := by
  rw [trace_transport u f g s hs, trace_transport u f g t ht]; exact h

/-- 25:D4 (Lemma wrap (2), the size of the trace) — the evaluation of a term with `ℓ` leaves performs `ℓ − 1`
lookups. -/
theorem lookups_succ : ∀ t : Tm, lookups t + 1 = leaves t
  | .one => rfl
  | .op s t => by
    show lookups s + lookups t + 1 + 1 = leaves s + leaves t
    rw [← lookups_succ s, ← lookups_succ t]
    exact (FRC.Nat.add_add_add_comm (lookups s) 1 (lookups t) 1).symm

/-- 25:E1 (Lemma abundance, the value) — in `M_p` the closed term over `1` and `+` with `ℓ` leaves has the
value `ℓ mod p`, whatever its shape. -/
theorem value_leaves (p : Nat) (hp : 0 < p) :
    ∀ t : Tm, val (1 % p) (fun x y => (x + y) % p) t = leaves t % p
  | .one => rfl
  | .op s t => by
    show (val (1 % p) (fun x y => (x + y) % p) s + val (1 % p) (fun x y => (x + y) % p) t) % p = (leaves s + leaves t) % p
    rw [value_leaves p hp s, value_leaves p hp t]
    exact (FRC.Nat.add_mod (leaves s) (leaves t) p hp).symm

/-- 25:E1 (Lemma abundance, the cohort) — any two terms with the same number of leaves give a true equation
of `M_p`. -/
theorem equal_leaves_equal_value (p : Nat) (hp : 0 < p) (s t : Tm) (h : leaves s = leaves t) :
    val (1 % p) (fun x y => (x + y) % p) s = val (1 % p) (fun x y => (x + y) % p) t := by
  rw [value_leaves p hp s, value_leaves p hp t, h]

/-! ### 25:E2 — the reach bound -/

/-- 25:E2 (Proposition reach, the count) — the records of length at most `B` over `a ≥ 2` letters number fewer
than `a^(B+1)`. -/
theorem records_lt (a : Nat) (ha : 2 ≤ a) (B : Nat) : FRC.Reductio.records a B < a ^ (B + 1) :=
  FRC.Reductio.records_lt a ha B

/-- 25:E2 (Proposition reach, the vanishing fraction in finite form) — against a cohort of `2^L` truths the
records of length at most `B` certify a fraction below `1/N` once `L ≥ a^(B+1)·N`: their number times `N` is
below `2^L`. -/
theorem reach_vanishes (a : Nat) (ha : 2 ≤ a) (B N L : Nat) (h : a ^ (B + 1) * N ≤ L) :
    FRC.Reductio.records a B * N < 2 ^ L :=
  Nat.lt_of_le_of_lt
    (Nat.le_trans (Nat.mul_le_mul_right N (Nat.le_of_lt (FRC.Reductio.records_lt a ha B))) h)
    Nat.lt_two_pow_self

/-! ### 25:F1, 25:F3 — mention cost: truth depends only on variables that occur -/

/-- Terms with variables (de Bruijn indices) over the signature of `M_p`. -/
inductive VTm where
  | var : Nat → VTm
  | zero : VTm
  | one : VTm
  | add : VTm → VTm → VTm
  | mul : VTm → VTm → VTm

/-- First-order formulas: equations, negation, conjunction, and the quantifier over the whole structure
(the bound variable is variable `0` of the body, the others shift up). -/
inductive Fm where
  | eq : VTm → VTm → Fm
  | neg : Fm → Fm
  | conj : Fm → Fm → Fm
  | all : Fm → Fm

/-- The value of a term in `M_p` under an assignment. -/
def tval (p : Nat) (env : Nat → Nat) : VTm → Nat
  | .var i => env i
  | .zero => 0
  | .one => 1 % p
  | .add s t => (tval p env s + tval p env t) % p
  | .mul s t => (tval p env s * tval p env t) % p

/-- Truth in `M_p` under an assignment: the quantifier ranges over the `p` elements. -/
def holds (p : Nat) (env : Nat → Nat) : Fm → Bool
  | .eq s t => decide (tval p env s = tval p env t)
  | .neg φ => !(holds p env φ)
  | .conj φ ψ => holds p env φ && holds p env ψ
  | .all φ => allBelow (fun x => holds p (cons x env) φ) p

/-- Variable `i` occurs in the term. -/
def occT (i : Nat) : VTm → Bool
  | .var j => decide (j = i)
  | .zero => false
  | .one => false
  | .add s t => occT i s || occT i t
  | .mul s t => occT i s || occT i t

/-- Variable `i` occurs free in the formula. -/
def occ (i : Nat) : Fm → Bool
  | .eq s t => occT i s || occT i t
  | .neg φ => occ i φ
  | .conj φ ψ => occ i φ || occ i ψ
  | .all φ => occ (i + 1) φ

/-- The length of a term, in symbols. -/
def tsize : VTm → Nat
  | .var _ => 1
  | .zero => 1
  | .one => 1
  | .add s t => tsize s + tsize t + 1
  | .mul s t => tsize s + tsize t + 1

/-- The length of a formula, in symbols. -/
def size : Fm → Nat
  | .eq s t => tsize s + tsize t + 1
  | .neg φ => size φ + 1
  | .conj φ ψ => size φ + size ψ + 1
  | .all φ => size φ + 1

theorem tval_congr (p : Nat) {env env' : Nat → Nat} :
    ∀ t : VTm, (∀ i, occT i t = true → env i = env' i) → tval p env t = tval p env' t
  | .var j, h => h j (decide_eq_true rfl)
  | .zero, _ => rfl
  | .one, _ => rfl
  | .add s t, h => by
    show (tval p env s + tval p env t) % p = (tval p env' s + tval p env' t) % p
    rw [tval_congr p s (fun i hi => h i (or_intro_left hi)), tval_congr p t (fun i hi => h i (or_intro_right hi))]
  | .mul s t, h => by
    show (tval p env s * tval p env t) % p = (tval p env' s * tval p env' t) % p
    rw [tval_congr p s (fun i hi => h i (or_intro_left hi)), tval_congr p t (fun i hi => h i (or_intro_right hi))]

/-- 25:F1 (Lemma mention, the coincidence form) — two assignments that agree on the variables occurring free in
a formula give it the same truth value in `M_p`. -/
theorem holds_congr (p : Nat) : ∀ (φ : Fm) {env env' : Nat → Nat},
    (∀ i, occ i φ = true → env i = env' i) → holds p env φ = holds p env' φ
  | .eq s t, env, env', h => by
    show decide (tval p env s = tval p env t) = decide (tval p env' s = tval p env' t)
    rw [tval_congr p s (fun i hi => h i (or_intro_left hi)), tval_congr p t (fun i hi => h i (or_intro_right hi))]
  | .neg φ, env, env', h => by
    show (!(holds p env φ)) = (!(holds p env' φ))
    rw [holds_congr p φ h]
  | .conj φ ψ, env, env', h => by
    show (holds p env φ && holds p env ψ) = (holds p env' φ && holds p env' ψ)
    rw [holds_congr p φ (fun i hi => h i (or_intro_left hi)), holds_congr p ψ (fun i hi => h i (or_intro_right hi))]
  | .all φ, env, env', h => by
    show allBelow (fun x => holds p (cons x env) φ) p = allBelow (fun x => holds p (cons x env') φ) p
    exact allBelow_congr (fun x _ => holds_congr p φ (fun i hi =>
      match i, hi with
      | 0, _ => rfl
      | j + 1, hj => h j hj))

/-- The assignment changed at one coordinate. -/
def upd (env : Nat → Nat) (i v : Nat) : Nat → Nat := fun j => if j = i then v else env j

/-- 25:F1 (Lemma mention) — if the truth of a formula in `M_p` depends on coordinate `i` (reassigning it changes
the truth value), then variable `i` occurs in the formula. -/
theorem mention (p : Nat) (φ : Fm) (env : Nat → Nat) (i v : Nat)
    (hdep : holds p (upd env i v) φ ≠ holds p env φ) : occ i φ = true :=
  match h : occ i φ with
  | true => rfl
  | false => absurd (holds_congr p φ (fun j hj =>
      match Nat.decEq j i with
      | isTrue e => Bool.noConfusion ((e ▸ hj : occ i φ = true).symm.trans h)
      | isFalse e => (ite_eq_right e : (if j = i then v else env j) = env j))) hdep

/-! #### counting the coordinates a formula can read -/

/-- The number of `i < n` with `f i = true`. -/
def count (f : Nat → Bool) : Nat → Nat
  | 0 => 0
  | n + 1 => count f n + cond (f n) 1 0

theorem count_full {f : Nat → Bool} : ∀ {n : Nat}, (∀ i, i < n → f i = true) → count f n = n
  | 0, _ => rfl
  | n + 1, h => by
    show count f n + cond (f n) 1 0 = n + 1
    rw [h n (Nat.lt_succ_self n), count_full (fun i hi => h i (Nat.lt_succ_of_lt hi))]; rfl

theorem cond_or_le (a b : Bool) : cond (a || b) 1 0 ≤ cond a 1 0 + cond b 1 0 := by
  cases a <;> cases b <;> decide

theorem count_or_le (f g : Nat → Bool) : ∀ n, count (fun i => f i || g i) n ≤ count f n + count g n
  | 0 => Nat.le_refl 0
  | n + 1 => by
    show count (fun i => f i || g i) n + cond (f n || g n) 1 0 ≤ (count f n + cond (f n) 1 0) + (count g n + cond (g n) 1 0)
    rw [FRC.Nat.add_add_add_comm (count f n) (cond (f n) 1 0) (count g n) (cond (g n) 1 0)]
    exact Nat.add_le_add (count_or_le f g n) (cond_or_le (f n) (g n))

theorem count_shift (f : Nat → Bool) : ∀ n, count (fun i => f (i + 1)) n ≤ count f (n + 1)
  | 0 => Nat.zero_le _
  | n + 1 => by
    show count (fun i => f (i + 1)) n + cond (f (n + 1)) 1 0 ≤ count f (n + 1) + cond (f (n + 1)) 1 0
    exact Nat.add_le_add_right (count_shift f n) _

theorem count_false : ∀ n, count (fun _ => false) n = 0
  | 0 => rfl
  | n + 1 => by
    show count (fun _ => false) n + 0 = 0
    rw [count_false n]

theorem count_single (j : Nat) : ∀ n, count (fun i => decide (j = i)) n ≤ 1 ∧ (n ≤ j → count (fun i => decide (j = i)) n = 0)
  | 0 => ⟨Nat.zero_le 1, fun _ => rfl⟩
  | n + 1 =>
    match Nat.decEq j n with
    | isTrue e => by
      have h0 : count (fun i => decide (j = i)) n = 0 := (count_single j n).2 (e ▸ Nat.le_refl j)
      refine ⟨?_, fun hle => absurd (e ▸ hle : n + 1 ≤ n) (Nat.not_succ_le_self n)⟩
      show count (fun i => decide (j = i)) n + cond (decide (j = n)) 1 0 ≤ 1
      rw [h0, decide_eq_true e]; exact Nat.le_refl 1
    | isFalse e => by
      refine ⟨?_, fun hle => ?_⟩
      · show count (fun i => decide (j = i)) n + cond (decide (j = n)) 1 0 ≤ 1
        rw [decide_eq_false e]; exact (count_single j n).1
      · show count (fun i => decide (j = i)) n + cond (decide (j = n)) 1 0 = 0
        rw [decide_eq_false e]; exact (count_single j n).2 (Nat.le_of_succ_le hle)

theorem tcount_le : ∀ (t : VTm) (N : Nat), count (fun i => occT i t) N ≤ tsize t
  | .var j, N => (count_single j N).1
  | .zero, N => by show count (fun _ => false) N ≤ 1; rw [count_false N]; exact Nat.zero_le 1
  | .one, N => by show count (fun _ => false) N ≤ 1; rw [count_false N]; exact Nat.zero_le 1
  | .add s t, N =>
    Nat.le_trans (count_or_le (fun i => occT i s) (fun i => occT i t) N)
      (Nat.le_succ_of_le (Nat.add_le_add (tcount_le s N) (tcount_le t N)))
  | .mul s t, N =>
    Nat.le_trans (count_or_le (fun i => occT i s) (fun i => occT i t) N)
      (Nat.le_succ_of_le (Nat.add_le_add (tcount_le s N) (tcount_le t N)))

theorem fcount_le : ∀ (φ : Fm) (N : Nat), count (fun i => occ i φ) N ≤ size φ
  | .eq s t, N =>
    Nat.le_trans (count_or_le (fun i => occT i s) (fun i => occT i t) N)
      (Nat.le_succ_of_le (Nat.add_le_add (tcount_le s N) (tcount_le t N)))
  | .neg φ, N => Nat.le_succ_of_le (fcount_le φ N)
  | .conj φ ψ, N =>
    Nat.le_trans (count_or_le (fun i => occ i φ) (fun i => occ i ψ) N)
      (Nat.le_succ_of_le (Nat.add_le_add (fcount_le φ N) (fcount_le ψ N)))
  | .all φ, N =>
    Nat.le_succ_of_le (Nat.le_trans (count_shift (fun i => occ i φ) N) (fcount_le φ (N + 1)))

/-- 25:F1 (Lemma mention, the arity) — a formula in which the `N` variables `0, …, N − 1` occur has length at
least `N`. -/
theorem arity_le_size (φ : Fm) (N : Nat) (h : ∀ i, i < N → occ i φ = true) : N ≤ size φ :=
  (count_full h) ▸ fcount_le φ N

/-- 25:F1, 25:F2 (Lemma mention, the cost) — a formula whose truth in `M_p` depends on all `N` coordinates of a
tuple (the variables `0, …, N − 1`) has length at least `N`. -/
theorem mention_cost (p : Nat) (φ : Fm) (N : Nat)
    (h : ∀ i, i < N → ∃ env v, holds p (upd env i v) φ ≠ holds p env φ) : N ≤ size φ :=
  arity_le_size φ N (fun i hi => match h i hi with
    | ⟨env, v, hdep⟩ => mention p φ env i v hdep)

theorem fcount_lt : ∀ (φ : Fm) (N : Nat), count (fun i => occ i φ) N < size φ
  | .eq s t, N =>
    Nat.lt_succ_of_le (Nat.le_trans (count_or_le (fun i => occT i s) (fun i => occT i t) N)
      (Nat.add_le_add (tcount_le s N) (tcount_le t N)))
  | .neg φ, N => Nat.lt_succ_of_lt (fcount_lt φ N)
  | .conj φ ψ, N =>
    Nat.lt_succ_of_le (Nat.le_trans (count_or_le (fun i => occ i φ) (fun i => occ i ψ) N)
      (Nat.add_le_add (Nat.le_of_lt (fcount_lt φ N)) (Nat.le_of_lt (fcount_lt ψ N))))
  | .all φ, N =>
    Nat.lt_succ_of_lt (Nat.lt_of_le_of_lt (count_shift (fun i => occ i φ) N) (fcount_lt φ (N + 1)))

theorem count_shift_by : ∀ (j : Nat) (f : Nat → Bool) (N : Nat), count (fun i => f (i + j)) N ≤ count f (N + j)
  | 0, _, _ => Nat.le_refl _
  | j + 1, f, N => Nat.le_trans (count_shift_by j (fun k => f (k + 1)) N) (count_shift f (N + j))

/-- 25:F3 (Corollary quotation, the arity) — a formula in which the `N` variables `j, …, j + N − 1` occur has more
than `N` symbols: a formula's arity is below its length. -/
theorem arity_lt_size (φ : Fm) (j N : Nat) (h : ∀ i, i < N → occ (i + j) φ = true) : N < size φ :=
  have h1 : count (fun i => occ (i + j) φ) N = N := count_full h
  Nat.lt_of_le_of_lt (Nat.le_trans (Nat.le_of_eq h1.symm) (count_shift_by j (fun i => occ i φ) N)) (fcount_lt φ (N + j))

/-- 25:F3 (Corollary quotation, the cost) — a formula whose truth in `M_p` depends on all `N` coordinates of a
tuple, the variables `j, …, j + N − 1`, has more than `N` symbols. -/
theorem mention_cost_lt (p : Nat) (φ : Fm) (j N : Nat)
    (h : ∀ i, i < N → ∃ env v, holds p (upd env (i + j) v) φ ≠ holds p env φ) : N < size φ :=
  arity_lt_size φ j N (fun i hi => match h i hi with
    | ⟨env, v, hdep⟩ => mention p φ env (i + j) v hdep)

/-- `Subformula ψ φ`: `ψ` is a subformula of `φ`. -/
inductive Subformula (ψ : Fm) : Fm → Prop where
  | refl : Subformula ψ ψ
  | neg {φ : Fm} : Subformula ψ φ → Subformula ψ (.neg φ)
  | conjL {φ χ : Fm} : Subformula ψ φ → Subformula ψ (.conj φ χ)
  | conjR {φ χ : Fm} : Subformula ψ χ → Subformula ψ (.conj φ χ)
  | all {φ : Fm} : Subformula ψ φ → Subformula ψ (.all φ)

theorem sub_size {ψ : Fm} : ∀ {φ : Fm}, Subformula ψ φ → size ψ ≤ size φ
  | _, .refl => Nat.le_refl _
  | _, .neg h => Nat.le_succ_of_le (sub_size h)
  | .conj φ χ, .conjL h => Nat.le_succ_of_le (Nat.le_trans (sub_size h) (Nat.le_add_right (size φ) (size χ)))
  | .conj φ χ, .conjR h => Nat.le_succ_of_le (Nat.le_trans (sub_size h) (Nat.le_add_left (size χ) (size φ)))
  | _, .all h => Nat.le_succ_of_le (sub_size h)

/-- 25:F3 (Corollary quotation) — no sentence `lam` contains a subformula whose truth depends on all coordinates
of a tuple of arity `N ≥ |lam|`, wherever the tuple's variables `j, …, j + N − 1` sit in the subformula's frame:
the subformula would have more than `N` symbols, and it is no longer than `lam`. -/
theorem no_self_reading (p : Nat) {ψ lam : Fm} (hsub : Subformula ψ lam) (j N : Nat) (hN : size lam ≤ N) :
    ¬ ∀ i, i < N → ∃ env v, holds p (upd env (i + j) v) ψ ≠ holds p env ψ := fun h =>
  Nat.lt_irrefl N (Nat.lt_of_lt_of_le (mention_cost_lt p ψ j N h) (Nat.le_trans (sub_size hsub) hN))

/-! ### 25:F2 — the diagonal template does not fit at any scale -/

/-- `∃ x, φ`, written with the language's one quantifier: `¬ ∀ x, ¬ φ`. -/
def ex (φ : Fm) : Fm := .neg (.all (.neg φ))

/-- A block of `n` existential quantifiers in front of a formula. -/
def exBlock : Nat → Fm → Fm
  | 0, φ => φ
  | n + 1, φ => ex (exBlock n φ)

/-- 25:F1 (Lemma mention, the quantifier block) — a block binding an `n`-tuple contributes `3n` symbols in this
syntax, at least `n`. -/
theorem size_exBlock : ∀ (n : Nat) (φ : Fm), size (exBlock n φ) = size φ + 3 * n
  | 0, _ => rfl
  | n + 1, φ => by
    show size (exBlock n φ) + 1 + 1 + 1 = size φ + 3 * (n + 1)
    rw [size_exBlock n φ, Nat.mul_succ]; rfl

/-- 25:F2 (Theorem nocompress, the accounting) — the diagonal formula `δ = ∃ v (Diag_N ∧ θ)`, with a block of `N`
quantifiers and a diagonal relation whose truth depends on all `2N` coordinates, has length at least
`2N + |θ| + 3N`: `2N` for the relation (mention cost), then `θ`, and three symbols for each quantifier of the
block (the paper counts one, which gives its `3N + |θ|`). -/
theorem template_size (p N : Nat) (diag θ : Fm)
    (hdep : ∀ i, i < 2 * N → ∃ env v, holds p (upd env i v) diag ≠ holds p env diag) :
    2 * N + size θ + 3 * N ≤ size (exBlock N (.conj diag θ)) := by
  have h2 : 2 * N ≤ size diag := mention_cost p diag (2 * N) hdep
  rw [size_exBlock]
  show 2 * N + size θ + 3 * N ≤ size diag + size θ + 1 + 3 * N
  exact Nat.add_le_add_right (Nat.le_trans (Nat.add_le_add_right h2 (size θ)) (Nat.le_succ _)) (3 * N)

/-- 25:F2 (Theorem nocompress, the scale) — a formula that binds an `N`-tuple, `N ≥ 1`, is longer than `N`: the
diagonal formula `∃ v (Diag_N ∧ θ)` has no code in `M^N`.  The block alone gives this clause; no hypothesis on
`Diag_N` or `θ` enters. -/
theorem no_template (N : Nat) (hN : 1 ≤ N) (φ : Fm) : ¬ size (exBlock N φ) ≤ N := fun hle => by
  rw [size_exBlock] at hle
  have h3 : 3 * N ≤ N := Nat.le_trans (Nat.le_add_left (3 * N) (size φ)) hle
  have h4 : N + 1 ≤ 3 * N := by
    have : N + N ≤ 3 * N := by rw [← Nat.two_mul]; exact Nat.mul_le_mul_right N (by decide)
    exact Nat.le_trans (Nat.add_le_add_left hN N) this
  exact Nat.not_succ_le_self N (Nat.le_trans h4 h3)

/-- 25:F2 (Theorem nocompress, splitting the scales) — if `θ` reads all `N₂` coordinates of its argument (the
non-degeneracy clause, at the scale `N₂` of the code of the fixed point), the diagonal formula is longer than
`N₂`, whatever the scale `N` of its own block: here the mention cost is what excludes the instance. -/
theorem split_scale (p N N₂ : Nat) (diag θ : Fm)
    (hθ : ∀ i, i < N₂ → ∃ env v, holds p (upd env i v) θ ≠ holds p env θ) :
    N₂ < size (exBlock N (.conj diag θ)) := by
  have h : N₂ ≤ size θ := mention_cost p θ N₂ hθ
  rw [size_exBlock]
  show N₂ < size diag + size θ + 1 + 3 * N
  exact Nat.lt_of_le_of_lt h (Nat.lt_of_lt_of_le (Nat.lt_succ_of_le (Nat.le_add_left (size θ) (size diag))) (Nat.le_add_right _ (3 * N)))

/-! ### 25:F4 — density does not rescue the template -/

/-- 25:F4 (Lemma density, the count) — an injective coding of the `a^n` strings of length `n` into `k`-tuples
over `m` elements needs `a^n ≤ m^k`.  (The paper's `k ≥ n log a / log m` is this inequality with logarithms taken.) -/
theorem dense_coding {a n m k : Nat} (c : Nat → Nat) (hc : ∀ i, i < a ^ n → c i < m ^ k)
    (hinj : ∀ i j, i < a ^ n → j < a ^ n → c i = c j → i = j) : a ^ n ≤ m ^ k :=
  match Nat.lt_or_ge (m ^ k) (a ^ n) with
  | Or.inl h => absurd hinj (part_collides h c hc)
  | Or.inr h => h

/-! ### 25:G4 — the prefix simulation -/

/-- `f 0 || … || f (n − 1)`. -/
def anyBelow (f : Nat → Bool) : Nat → Bool
  | 0 => false
  | n + 1 => f n || anyBelow f n

theorem anyBelow_congr {f g : Nat → Bool} : ∀ {n : Nat}, (∀ x, x < n → f x = g x) → anyBelow f n = anyBelow g n
  | 0, _ => rfl
  | n + 1, h => by
    show (f n || anyBelow f n) = (g n || anyBelow g n)
    rw [h n (Nat.lt_succ_self n), anyBelow_congr (fun x hx => h x (Nat.lt_succ_of_lt hx))]

theorem anyBelow_false : ∀ n, anyBelow (fun _ => false) n = false
  | 0 => rfl
  | n + 1 => by
    show (false || anyBelow (fun _ => false) n) = false
    rw [anyBelow_false n]; rfl

theorem allBelow_const (b : Bool) : ∀ n, 0 < n → allBelow (fun _ => b) n = b
  | 0, h => absurd h (Nat.lt_irrefl 0)
  | 1, _ => and_true' b
  | n + 2, _ => by
    show (b && allBelow (fun _ => b) (n + 1)) = b
    rw [allBelow_const b (n + 1) (Nat.succ_pos n)]; exact and_self' b

theorem anyBelow_and_const (c : Bool) (F : Nat → Bool) (n : Nat) :
    anyBelow (fun x => c && F x) n = (c && anyBelow F n) := by
  cases c
  · exact anyBelow_false n
  · rfl

theorem allBelow_and_const (c : Bool) (F : Nat → Bool) (n : Nat) (hn : 0 < n) :
    allBelow (fun y => c && F y) n = (c && allBelow F n) := by
  cases c
  · exact allBelow_const false n hn
  · rfl

/-- Among the `x < n`, the clause `x = y` picks `y`: `∃ x < n, (c ∧ x = y ∧ F x)` is `c ∧ F y` for `y < n`. -/
theorem anyBelow_pick (c : Bool) (F : Nat → Bool) (y : Nat) :
    ∀ n, anyBelow (fun x => (c && decide (x = y)) && F x) n = (if y < n then c && F y else false)
  | 0 => rfl
  | n + 1 => by
    show (((c && decide (n = y)) && F n) || anyBelow (fun x => (c && decide (x = y)) && F x) n) = (if y < n + 1 then c && F y else false)
    rw [anyBelow_pick c F y n]
    exact match Nat.decEq n y with
    | isTrue e => by
      rw [decide_eq_true e, and_true' c, ite_eq_right (e ▸ Nat.lt_irrefl n : ¬ y < n), or_false', ite_eq_left (e ▸ Nat.lt_succ_self n : y < n + 1), e]
    | isFalse e => by
      rw [decide_eq_false e, and_false' c]
      show (if y < n then c && F y else false) = (if y < n + 1 then c && F y else false)
      exact match Nat.decLt y n with
      | isTrue hlt => by rw [ite_eq_left hlt, ite_eq_left (Nat.lt_succ_of_lt hlt)]
      | isFalse hge => by
        have hne : ¬ y < n + 1 := fun h => hge (Nat.lt_of_le_of_ne (Nat.le_of_lt_succ h) (fun e' => e e'.symm))
        rw [ite_eq_right hge, ite_eq_right hne]

/-- The coded prefix evaluated directly over a structure of `m` elements: `true` codes `∀`, `false` codes `∃`;
the matrix `ψ` reads the chosen values (the last chosen first). -/
def direct (m : Nat) (ψ : List Nat → Bool) : List Bool → List Nat → Bool
  | [], acc => ψ acc
  | true :: pat, acc => allBelow (fun x => direct m ψ pat (x :: acc)) m
  | false :: pat, acc => anyBelow (fun x => direct m ψ pat (x :: acc)) m

/-- The uniform prefix `∀ y₁ ∃ x₁ … ∀ y_d ∃ x_d` with the clause `x_i = y_i` conjoined at the coded universal
positions and the matrix read on the `x`s; `c` carries the clauses collected so far. -/
def paired (m : Nat) (ψ : List Nat → Bool) : List Bool → List Nat → Bool → Bool
  | [], acc, c => c && ψ acc
  | q :: pat, acc, c =>
    allBelow (fun y => anyBelow (fun x => paired m ψ pat (x :: acc) (c && (!q || decide (x = y)))) m) m

/-- 25:G4 (Lemma prefix) — the prefix simulation: over a structure of `m ≥ 1` elements the uniform pairing
prefix with the copy clauses decides exactly what the coded prefix `Q₁ … Q_d` decides, for every pattern and
every matrix. -/
theorem prefix_simulation (m : Nat) (hm : 0 < m) (ψ : List Nat → Bool) :
    ∀ (pat : List Bool) (acc : List Nat) (c : Bool), paired m ψ pat acc c = (c && direct m ψ pat acc)
  | [], _, _ => rfl
  | true :: pat, acc, c => by
    show allBelow (fun y => anyBelow (fun x => paired m ψ pat (x :: acc) (c && (!true || decide (x = y)))) m) m
        = (c && allBelow (fun x => direct m ψ pat (x :: acc)) m)
    rw [← allBelow_and_const c (fun x => direct m ψ pat (x :: acc)) m hm]
    refine allBelow_congr (fun y hy => ?_)
    have h1 : anyBelow (fun x => paired m ψ pat (x :: acc) (c && (!true || decide (x = y)))) m
        = anyBelow (fun x => (c && decide (x = y)) && direct m ψ pat (x :: acc)) m :=
      anyBelow_congr (fun x _ => prefix_simulation m hm ψ pat (x :: acc) (c && decide (x = y)))
    rw [h1, anyBelow_pick c (fun x => direct m ψ pat (x :: acc)) y m, ite_eq_left hy]
  | false :: pat, acc, c => by
    show allBelow (fun y => anyBelow (fun x => paired m ψ pat (x :: acc) (c && (!false || decide (x = y)))) m) m
        = (c && anyBelow (fun x => direct m ψ pat (x :: acc)) m)
    have h1 : ∀ y, anyBelow (fun x => paired m ψ pat (x :: acc) (c && (!false || decide (x = y)))) m
        = (c && anyBelow (fun x => direct m ψ pat (x :: acc)) m) := fun y => by
      rw [← anyBelow_and_const c (fun x => direct m ψ pat (x :: acc)) m]
      refine anyBelow_congr (fun x _ => ?_)
      have h2 : paired m ψ pat (x :: acc) (c && (!false || decide (x = y))) = ((c && true) && direct m ψ pat (x :: acc)) :=
        prefix_simulation m hm ψ pat (x :: acc) (c && true)
      rw [and_true' c] at h2
      exact h2
    rw [allBelow_congr (fun y _ => h1 y)]
    exact allBelow_const _ m hm

/-- 25:G4 (Lemma prefix, the statement) — with no clause collected, the pairing prefix equals the coded prefix. -/
theorem prefix_simulation_closed (m : Nat) (hm : 0 < m) (ψ : List Nat → Bool) (pat : List Bool) :
    paired m ψ pat [] true = direct m ψ pat [] :=
  prefix_simulation m hm ψ pat [] true




-- Ledger predicates of 25-godel (generated by make_predicates.py from docs/25-godel/25-godel-ledger.json; edit the ledger, not this section)
/-- 25:C1 (p25010) — No finite structure interprets $\mathsf{Q}$: a model of $\mathsf{Q}$ has an injective successor with $0$ outside its range, and on a finite set an injective map is onto. -/
theorem p25010 : (∀ (n : Nat) (S : Nat → Nat), (∀ (x : Nat), x < n → S x < n) → (∀ (x y : Nat), x < n → y < n → S x = S y → x = y) → ∀ (z : Nat), z < n → ∃ x, x < n ∧ S x = z) ∧ ∀ (n : Nat) (S : Nat → Nat), (∀ (x : Nat), x < n → S x < n) → (∀ (x y : Nat), x < n → y < n → S x = S y → x = y) → ∀ (z : Nat), z < n → ¬∀ (x : Nat), x < n → S x ≠ z :=
  And.intro @FRC.Godel.inj_onto (@FRC.Godel.no_finite_successor)
/-- 25:C5 (p25014) — Tarski scoped: the $m+1$ sentences $\varphi,\neg\varphi,\dots,\neg^{m}\varphi$ outnumber the $m$ elements of $\M$, so every numbering of the sentences by elements of $\M$ gives two of them the same number. Truth in $\M$ is defined externally by a finite table with the evaluation procedure of C2. What fails is the internalisation of truth. -/
theorem p25014 : ∀ (m : Nat) (g : Nat → Nat), (∀ (i : Nat), i < m + (1 : Nat) → g i < m) → ¬∀ (i j : Nat), i < m + (1 : Nat) → j < m + (1 : Nat) → g i = g j → i = j :=
  @FRC.Godel.sentences_outnumber
/-- 25:D1 (p25015) — Relational diagonal: an agent of storage capacity $K$ with $a^{K}<m$ has no injective encoding of the elements of $\M$ into its storage states. Every internal representation identifies distinct elements. A fortiori the agent holds no faithful model of $\M$ that also represents the model's own encoding map. -/
theorem p25015 : ∀ {m R : Nat}, R < m → ∀ (ρ : Nat → Nat), (∀ (i : Nat), i < m → ρ i < R) → ¬∀ (i j : Nat), i < m → j < m → ρ i = ρ j → i = j :=
  @FRC.Godel.part_collides
/-- 25:D4 (p25018) — Wrap, no internal trace: the steps that verify a certificate succeed in a finite $\M'$ built on its cited table entries, $\lvert \M'\rvert\le(r+1)\,p_{\D}(B)$, $r$ the largest arity. Under locally sound rules its end sentence is true there. An axiom asserted on syntactic recognition transports as a record, not as a truth. If $(r+1)\,p_{\D}(B)\le a^{K}$, no certificate marks a reading exact. -/
theorem p25018 : (∀ (u : Nat) (f g : Nat → Nat → Nat) (t : FRC.Godel.Tm), FRC.Godel.Agree u f g t → FRC.Godel.val u g t = FRC.Godel.val u f t) ∧ (∀ (u : Nat) (f g : Nat → Nat → Nat) (s t : FRC.Godel.Tm), FRC.Godel.Agree u f g s → FRC.Godel.Agree u f g t → FRC.Godel.val u f s = FRC.Godel.val u f t → FRC.Godel.val u g s = FRC.Godel.val u g t) ∧ ∀ (t : FRC.Godel.Tm), FRC.Godel.lookups t + (1 : Nat) = FRC.Godel.leaves t :=
  And.intro @FRC.Godel.trace_transport (And.intro @FRC.Godel.wrap_equation (@FRC.Godel.lookups_succ))
/-- 25:E1 (p25019) — Abundance: the closed terms over $\{1,+\}$ with $\ell$ leaves are the full binary trees, $C_{\ell-1}\ge2^{\ell-2}$ in number. In $\M_p$ all have the value $\ell\bmod p$, so any two give a true equation of length $O(\ell)$, at least $2^{\ell}$ of them for $\ell\ge6$. The true sentences of length at most $L$ number at least $2^{\alpha L}$ for large $L$, $\alpha>0$ constant. -/
theorem p25019 : (∀ (p : Nat), (0 : Nat) < p → ∀ (t : FRC.Godel.Tm), FRC.Godel.val ((1 : Nat) % p) (fun x y => (x + y) % p) t = FRC.Godel.leaves t % p) ∧ ∀ (p : Nat), (0 : Nat) < p → ∀ (s t : FRC.Godel.Tm), FRC.Godel.leaves s = FRC.Godel.leaves t → FRC.Godel.val ((1 : Nat) % p) (fun x y => (x + y) % p) s = FRC.Godel.val ((1 : Nat) % p) (fun x y => (x + y) % p) t :=
  And.intro @FRC.Godel.value_leaves (@FRC.Godel.equal_leaves_equal_value)
/-- 25:E2 (p25020) — Vanishing reach: an agent of capacity $(K,H)$ certifies at most $a^{B+1}$ sentences over all its runs, the records being strings of length at most $B$. The certified fraction of the truths of length at most $L$ (E1) is at most $a^{B+1}/2^{\alpha L}$, below $1/N$ for every $N$ once $L$ is large enough. -/
theorem p25020 : (∀ (a : Nat), (2 : Nat) ≤ a → ∀ (B : Nat), FRC.Reductio.records a B < a ^ (B + (1 : Nat))) ∧ ∀ (a : Nat), (2 : Nat) ≤ a → ∀ (B N L : Nat), a ^ (B + (1 : Nat)) * N ≤ L → FRC.Reductio.records a B * N < (2 : Nat) ^ L :=
  And.intro @FRC.Godel.records_lt (@FRC.Godel.reach_vanishes)
/-- 25:F1 (p25023) — Mention cost: if the truth of a formula in $\M$ depends on coordinate $i$ of a tuple of variables, then $v_{i}$ occurs in it. A formula whose truth depends on all $N$ coordinates has length at least $N$. A quantifier block binding an $N$-tuple contributes at least $N$ symbols. -/
theorem p25023 : (∀ (p : Nat) (φ : FRC.Godel.Fm) {env env' : Nat → Nat}, (∀ (i : Nat), FRC.Godel.occ i φ = true → env i = env' i) → FRC.Godel.holds p env φ = FRC.Godel.holds p env' φ) ∧ (∀ (p : Nat) (φ : FRC.Godel.Fm) (env : Nat → Nat) (i v : Nat), FRC.Godel.holds p (FRC.Godel.upd env i v) φ ≠ FRC.Godel.holds p env φ → FRC.Godel.occ i φ = true) ∧ (∀ (φ : FRC.Godel.Fm) (N : Nat), (∀ (i : Nat), i < N → FRC.Godel.occ i φ = true) → N ≤ FRC.Godel.size φ) ∧ (∀ (p : Nat) (φ : FRC.Godel.Fm) (N : Nat), (∀ (i : Nat), i < N → ∃ env v, FRC.Godel.holds p (FRC.Godel.upd env i v) φ ≠ FRC.Godel.holds p env φ) → N ≤ FRC.Godel.size φ) ∧ ∀ (n : Nat) (φ : FRC.Godel.Fm), FRC.Godel.size (FRC.Godel.exBlock n φ) = FRC.Godel.size φ + (3 : Nat) * n :=
  And.intro @FRC.Godel.holds_congr (And.intro @FRC.Godel.mention (And.intro @FRC.Godel.arity_le_size (And.intro @FRC.Godel.mention_cost (@FRC.Godel.size_exBlock))))
/-- 25:F2 (p25024) — No compression: code strings of length at most $N$ as tuples in $\M^{N}$, one coordinate per symbol, signature and alphabet fixed independently of $N$, $\theta$ non-degenerate. The G\"odel template has no instance at any scale. The diagonal formula needs $\lvert \delta\rvert\ge3N+\lvert \theta\rvert>N$ symbols, so its code is not in $\M^{N}$. Splitting the scales fails: $\delta$ outgrows the scale $\theta$ reads. -/
theorem p25024 : (∀ (p N : Nat) (diag θ : FRC.Godel.Fm), (∀ (i : Nat), i < (2 : Nat) * N → ∃ env v, FRC.Godel.holds p (FRC.Godel.upd env i v) diag ≠ FRC.Godel.holds p env diag) → (2 : Nat) * N + FRC.Godel.size θ + (3 : Nat) * N ≤ FRC.Godel.size (FRC.Godel.exBlock N (diag.conj θ))) ∧ (∀ (N : Nat), (1 : Nat) ≤ N → ∀ (φ : FRC.Godel.Fm), ¬FRC.Godel.size (FRC.Godel.exBlock N φ) ≤ N) ∧ (∀ (p N N₂ : Nat) (diag θ : FRC.Godel.Fm), (∀ (i : Nat), i < N₂ → ∃ env v, FRC.Godel.holds p (FRC.Godel.upd env i v) θ ≠ FRC.Godel.holds p env θ) → N₂ < FRC.Godel.size (FRC.Godel.exBlock N (diag.conj θ))) ∧ ∀ (p : Nat) (φ : FRC.Godel.Fm) (N : Nat), (∀ (i : Nat), i < N → ∃ env v, FRC.Godel.holds p (FRC.Godel.upd env i v) φ ≠ FRC.Godel.holds p env φ) → N ≤ FRC.Godel.size φ :=
  And.intro @FRC.Godel.template_size (And.intro @FRC.Godel.no_template (And.intro @FRC.Godel.split_scale (@FRC.Godel.mention_cost)))
/-- 25:F3 (p25025) — Quotation exceeds mention: a formula's arity is below its length. No sentence $\lambda$ contains a subformula whose truth depends on all coordinates of a tuple of arity at least $\lvert \lambda\rvert$. Under any coding that spends at least $\lvert \lambda\rvert$ coordinates on $\lambda$, per-symbol coding included, no sentence's truth is sensitive to every coordinate of its own code. -/
theorem p25025 : (∀ (φ : FRC.Godel.Fm) (j N : Nat), (∀ (i : Nat), i < N → FRC.Godel.occ (i + j) φ = true) → N < FRC.Godel.size φ) ∧ (∀ (p : Nat) (φ : FRC.Godel.Fm) (j N : Nat), (∀ (i : Nat), i < N → ∃ env v, FRC.Godel.holds p (FRC.Godel.upd env (i + j) v) φ ≠ FRC.Godel.holds p env φ) → N < FRC.Godel.size φ) ∧ ∀ (p : Nat) {ψ lam : FRC.Godel.Fm}, FRC.Godel.Subformula ψ lam → ∀ (j N : Nat), FRC.Godel.size lam ≤ N → ¬∀ (i : Nat), i < N → ∃ env v, FRC.Godel.holds p (FRC.Godel.upd env (i + j) v) ψ ≠ FRC.Godel.holds p env ψ :=
  And.intro @FRC.Godel.arity_lt_size (And.intro @FRC.Godel.mention_cost_lt (@FRC.Godel.no_self_reading))
/-- 25:F4 (p25026) — Density: an injective coding of length-$n$ strings into $\M$-tuples needs $k\ge n\log a/\log m$ coordinates ($m^{k}\ge a^{n}$). The variable names alone cost order $k\log_{a}k$ symbols. The template therefore fails at every scale beyond a threshold $t(\M)$ of order $m\log_{a}m$: at $a=2$, about $10^{32}$ symbols at $m=2^{100}$, beyond $10^{300}$ at $m=2^{1000}$. -/
theorem p25026 : ∀ {a n m k : Nat} (c : Nat → Nat), (∀ (i : Nat), i < a ^ n → c i < m ^ k) → (∀ (i j : Nat), i < a ^ n → j < a ^ n → c i = c j → i = j) → a ^ n ≤ m ^ k :=
  @FRC.Godel.dense_coding
/-- 25:G4 (p25031) — Prefix simulation: $Q_{1}z_{1}\cdots Q_{d}z_{d}\,\psi(\bar z)$ holds in $\M$ exactly when $\forall y_{1}\exists x_{1}\cdots\forall y_{d}\exists x_{d}\,[\bigwedge_{i:Q_{i}=\forall}x_{i}=y_{i}\wedge\psi(\bar x)]$ does: one uniform prefix simulates every coded quantifier pattern. -/
theorem p25031 : (∀ (m : Nat), (0 : Nat) < m → ∀ (ψ : List Nat → Bool) (pat : List Bool) (acc : List Nat) (c : Bool), FRC.Godel.paired m ψ pat acc c = (c && FRC.Godel.direct m ψ pat acc)) ∧ ∀ (m : Nat), (0 : Nat) < m → ∀ (ψ : List Nat → Bool) (pat : List Bool), FRC.Godel.paired m ψ pat [] true = FRC.Godel.direct m ψ pat [] :=
  And.intro @FRC.Godel.prefix_simulation (@FRC.Godel.prefix_simulation_closed)
-- end ledger predicates

end FRC.Godel
