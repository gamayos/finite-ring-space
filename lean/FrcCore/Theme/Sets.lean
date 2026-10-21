import FrcCore.Theme.Logic

/-!
# The logic theme — finite sets: the antinomy as a theorem, counting measure, no doubling, principal ultrafilters

The finite witnesses of 5-reductio's normal forms (21 October 2026): the antinomy normal form as a theorem of
separation, abstractly for any membership relation and on hereditarily finite sets built as finite trees (5:D2,
5:D5); the iterated singletons `∅, {∅}, {{∅}}, …`, pairwise distinct and outrunning every set (5:D9); counting
measure on `[0, n)` — total, additive, invariant under every bijection (5:E8, 5:D9, 5:D5); no injection of `X ⊔ X`
into `X` (5:E8); every ultrafilter on a finite set is principal (5:E8). No Mathlib, no axioms, no classical logic:
the ultrafilter is Boolean-valued and its point is found by bounded search.
-/

namespace FRC.Sets

open FRC.Logic

/-! ### 5:D2 — Russell's argument as a theorem of separation -/

/-- 5:D2, 5:D5 (Proposition antinomy-NF, the theorem) — for any membership relation `M`, no class `r` satisfies
`x ∈ r ↔ x ∉ x` for every `x`: `r ∈ r ↔ r ∉ r` is contradictory. The antinomy is a theorem about the Russell class,
and a paradox only where comprehension forms it. -/
theorem no_russell_class {α : Type} (M : α → α → Prop) : ¬ ∃ r, ∀ x, M x r ↔ ¬ M x x :=
  fun ⟨r, h⟩ =>
    have hn : ¬ M r r := fun hr => (h r).mp hr hr
    hn ((h r).mpr hn)

/-- 5:D2, 5:D5 (Proposition antinomy-NF, the inconsistent bundle) — with separation (`sep u` is `{x ∈ u | x ∉ x}` for
every `u`) no set is universal: the Russell class of a universal set would be the class of all `x ∉ x`. This is
Cns + AT + comprehension inconsistent, read on separation. -/
theorem no_universal_of_separation {α : Type} (M : α → α → Prop) (sep : α → α)
    (hsep : ∀ u x, M x (sep u) ↔ (M x u ∧ ¬ M x x)) : ¬ ∃ v, ∀ x, M x v :=
  fun ⟨v, hv⟩ => no_russell_class M ⟨sep v, fun x =>
    ⟨fun h => ((hsep v x).mp h).2, fun h => (hsep v x).mpr ⟨hv x, h⟩⟩⟩

/-- 5:D2, 5:D5 (Proposition antinomy-NF, the witness) — bounded comprehension has no antinomy: for every set `u` the
class `r = {x ∈ u | x ∉ x}` is a set that is not a member of `u` (were `r ∈ u`, then `r ∈ r ↔ r ∉ r`). -/
theorem russell_not_mem {α : Type} (M : α → α → Prop) (u r : α) (hr : ∀ x, M x r ↔ (M x u ∧ ¬ M x x)) : ¬ M r u :=
  fun hru =>
    have hn : ¬ M r r := fun hrr => ((hr r).mp hrr).2 hrr
    hn ((hr r).mpr ⟨hru, hn⟩)

/-! ### Hereditarily finite sets as finite trees -/

/-- A hereditarily finite set: the finite list of its members. -/
inductive HF where
  | mk : List HF → HF

/-- Membership in a list of sets, as a proposition. -/
def memList (x : HF) : List HF → Prop
  | [] => False
  | y :: ys => x = y ∨ memList x ys

/-- The members of a set. -/
def HF.members : HF → List HF
  | .mk l => l

/-- `x ∈ u`. -/
def HF.Mem (x u : HF) : Prop := memList x u.members

mutual
/-- The rank: one more than the largest rank of a member, `0` for the empty set. -/
def HF.rank : HF → Nat
  | .mk l => rankList l
/-- The least bound above the ranks of the members of a list. -/
def rankList : List HF → Nat
  | [] => 0
  | x :: xs => mx (HF.rank x + 1) (rankList xs)
end

theorem rank_lt_of_memList {x : HF} : ∀ {l : List HF}, memList x l → HF.rank x < rankList l
  | [], h => absurd h id
  | y :: ys, h => match h with
    | Or.inl e => by
        show HF.rank x < mx (HF.rank y + 1) (rankList ys)
        rw [e]; exact Nat.lt_of_lt_of_le (Nat.lt_succ_self _) (le_mx_left _ _)
    | Or.inr h' => by
        show HF.rank x < mx (HF.rank y + 1) (rankList ys)
        exact Nat.lt_of_lt_of_le (rank_lt_of_memList h') (le_mx_right _ _)

/-- A member has smaller rank. -/
theorem rank_lt_of_mem {x u : HF} (h : HF.Mem x u) : HF.rank x < HF.rank u := by
  match u with
  | .mk l => exact rank_lt_of_memList h

/-- 5:D2 (Proposition antinomy-NF, the witness on hereditarily finite sets) — no set is a member of itself. -/
theorem not_mem_self (x : HF) : ¬ HF.Mem x x :=
  fun h => Nat.lt_irrefl _ (rank_lt_of_mem h)

/-- The Russell class of `u`, `{x ∈ u | x ∉ x}`: on hereditarily finite sets it is `u` itself, since no set is a
member of itself (`mem_russell`). -/
def russell (u : HF) : HF := u

/-- 5:D2 — the Russell class of `u` is exactly the separation `{x ∈ u | x ∉ x}`. -/
theorem mem_russell (u x : HF) : HF.Mem x (russell u) ↔ (HF.Mem x u ∧ ¬ HF.Mem x x) :=
  ⟨fun h => ⟨h, not_mem_self x⟩, fun h => h.1⟩

/-- 5:D2, 5:D5 — every set `u` has a subset, its Russell class, that is not a member of `u`. -/
theorem russell_not_mem_hf (u : HF) : ¬ HF.Mem (russell u) u :=
  russell_not_mem HF.Mem u (russell u) (mem_russell u)

/-- 5:D2, 5:D5 — no hereditarily finite set is universal: `v` itself is not a member of `v`. -/
theorem no_universal (v : HF) : ∃ x, ¬ HF.Mem x v := ⟨v, not_mem_self v⟩

/-! ### 5:D9 — the iterated singletons -/

/-- The singleton `{x}`. -/
def single (x : HF) : HF := .mk [x]

/-- The chain `∅, {∅}, {{∅}}, …`. -/
def chain : Nat → HF
  | 0 => .mk []
  | n + 1 => single (chain n)

theorem rank_single (x : HF) : HF.rank (single x) = HF.rank x + 1 := by
  show mx (HF.rank x + 1) 0 = HF.rank x + 1
  unfold mx; exact ite_eq_right (Nat.not_lt_zero _)

/-- 5:D9 (Corollary AT-det) — the `n`-th iterated singleton has rank `n`. -/
theorem rank_chain : ∀ n, HF.rank (chain n) = n
  | 0 => rfl
  | n + 1 => by show HF.rank (single (chain n)) = n + 1; rw [rank_single, rank_chain n]

/-- 5:D9 (Corollary AT-det) — the iterated singletons are pairwise distinct. -/
theorem chain_injective {a b : Nat} (h : chain a = chain b) : a = b := by
  have := congrArg HF.rank h; rwa [rank_chain, rank_chain] at this

/-- 5:D9 (Corollary AT-det, the finite form of "a universal set is infinite") — no set holds every iterated
singleton: the one of its own rank is not among its members, since members have smaller rank. -/
theorem chain_not_mem (v : HF) : ¬ HF.Mem (chain (HF.rank v)) v :=
  fun h => Nat.lt_irrefl _ (rank_chain (HF.rank v) ▸ rank_lt_of_mem h)

/-! ### 5:E8, 5:D9, 5:D5 — counting measure on `[0, n)` -/

/-- The counting measure of a subset of `[0, n)`, the subset a Boolean predicate. -/
def measure (A : Nat → Bool) (n : Nat) : Nat := count A n

theorem measure_zero (A : Nat → Bool) : measure A 0 = 0 := rfl

theorem measure_succ (A : Nat → Bool) (n : Nat) : measure A (n + 1) = measure A n + cond (A n) 1 0 := rfl

/-- 5:E8, 5:D9 — counting measure is total: every subset has one, at most the size of the set. -/
theorem measure_le (A : Nat → Bool) : ∀ n, measure A n ≤ n
  | 0 => Nat.le_refl 0
  | n + 1 => by
    rw [measure_succ]
    exact match h : A n with
      | true => Nat.add_le_add_right (measure_le A n) 1
      | false => Nat.le_succ_of_le (measure_le A n)

/-- 5:E8 — the whole set has measure `n` and the empty set measure `0`. -/
theorem measure_univ (n : Nat) : measure (fun _ => true) n = n := count_full (fun _ _ => rfl)

theorem measure_empty (n : Nat) : measure (fun _ => false) n = 0 := count_false n

/-- 5:E8, 5:D5 (counting measure is finitely additive) — on disjoint subsets the measure of the union is the sum. -/
theorem measure_add (A B : Nat → Bool) : ∀ n, (∀ x, x < n → ¬ (A x = true ∧ B x = true)) →
    measure (fun x => A x || B x) n = measure A n + measure B n
  | 0, _ => rfl
  | n + 1, h => by
    rw [measure_succ, measure_succ, measure_succ, measure_add A B n (fun x hx => h x (Nat.lt_succ_of_lt hx))]
    cases ha : A n <;> cases hb : B n
    · rfl
    · show measure A n + measure B n + 1 = measure A n + (measure B n + 1)
      exact Nat.add_assoc _ _ _
    · show measure A n + measure B n + 1 = measure A n + 1 + measure B n
      exact Nat.add_right_comm _ _ _
    · exact absurd ⟨ha, hb⟩ (h n (Nat.lt_succ_self n))

/-- 5:E8 — a subset and its complement share the set: `|A| + |Aᶜ| = n`. -/
theorem measure_compl (A : Nat → Bool) : ∀ n, measure A n + measure (fun x => !A x) n = n
  | 0 => rfl
  | n + 1 => by
    rw [measure_succ, measure_succ]
    cases h : A n
    · show measure A n + (measure (fun x => !A x) n + 1) = n + 1
      rw [← Nat.add_assoc, measure_compl A n]
    · show measure A n + 1 + measure (fun x => !A x) n = n + 1
      rw [Nat.add_right_comm, measure_compl A n]

/-- The count of `A` over a list of positions. -/
def countList (A : Nat → Bool) : List Nat → Nat
  | [] => 0
  | a :: l => cond (A a) 1 0 + countList A l

theorem countList_imageList (A : Nat → Bool) (σ : Nat → Nat) : ∀ n,
    countList A (FRC.Shell.imageList σ n) = count (fun j => A (σ j)) n
  | 0 => rfl
  | n + 1 => by
    show cond (A (σ n)) 1 0 + countList A (FRC.Shell.imageList σ n) = count (fun j => A (σ j)) n + cond (A (σ n)) 1 0
    rw [countList_imageList A σ n, Nat.add_comm]

theorem countList_erase (A : Nat → Bool) {v : Nat} : ∀ {l : List Nat}, Pigeonhole.mem v l →
    countList A l = cond (A v) 1 0 + countList A (Pigeonhole.erase v l)
  | [], h => absurd h id
  | a :: l, h =>
    match Nat.decEq a v with
    | isTrue e => by rw [show Pigeonhole.erase v (a :: l) = l from ite_eq_left e, e]; rfl
    | isFalse e => by
        rw [show Pigeonhole.erase v (a :: l) = a :: Pigeonhole.erase v l from ite_eq_right e]
        have hm : Pigeonhole.mem v l := match h with
          | Or.inl h' => absurd h'.symm e
          | Or.inr h' => h'
        show cond (A a) 1 0 + countList A l = cond (A v) 1 0 + (cond (A a) 1 0 + countList A (Pigeonhole.erase v l))
        rw [countList_erase A hm, Nat.add_left_comm]

/-- A count over any list of `n` distinct positions below `n` is the count over `[0, n)`. -/
theorem countList_eq_count (A : Nat → Bool) : ∀ (n : Nat) (l : List Nat), Pigeonhole.NoDup l →
    (∀ e, Pigeonhole.mem e l → e < n) → l.length = n → countList A l = count A n
  | 0, [], _, _, _ => rfl
  | 0, a :: _, _, hb, _ => absurd (hb a (Or.inl rfl)) (Nat.not_lt_zero a)
  | n + 1, l, hnd, hb, hlen => by
    have hm : Pigeonhole.mem n l := Pigeonhole.mem_of_nodup_of_length_lt (n + 1) l hnd hb hlen n (Nat.lt_succ_self n)
    rw [countList_erase A hm]
    have hb' : ∀ e, Pigeonhole.mem e (Pigeonhole.erase n l) → e < n := fun e he =>
      match Nat.lt_or_ge e n with
      | Or.inl hlt => hlt
      | Or.inr hge =>
        have : e = n := Nat.le_antisymm (Nat.le_of_lt_succ (hb e (Pigeonhole.mem_of_mem_erase he))) hge
        absurd (this ▸ he) (Pigeonhole.not_mem_erase_self n hnd)
    have hlen' : (Pigeonhole.erase n l).length = n := by
      have := Pigeonhole.length_erase_of_mem hm; rw [hlen] at this; exact Nat.succ.inj this
    rw [countList_eq_count A n (Pigeonhole.erase n l) (Pigeonhole.nodup_erase n hnd) hb' hlen']
    show cond (A n) 1 0 + count A n = count A n + cond (A n) 1 0
    exact Nat.add_comm _ _

/-- 5:E8, 5:D9, 5:D5 (counting measure is invariant) — a bijection `σ` of `[0, n)` (injective, with values below `n`) carries
every subset to one of the same measure: `|σ⁻¹ A| = |A|`. -/
theorem measure_perm (A : Nat → Bool) (σ : Nat → Nat) (n : Nat) (hlt : ∀ j, j < n → σ j < n)
    (hinj : ∀ i j, i < n → j < n → σ i = σ j → i = j) :
    measure (fun j => A (σ j)) n = measure A n := by
  show count (fun j => A (σ j)) n = count A n
  rw [← countList_imageList]
  exact countList_eq_count A n (FRC.Shell.imageList σ n) (FRC.Shell.imageList_nodup hinj (Nat.le_refl n))
    (fun e he => match FRC.Shell.mem_imageList he with | ⟨j, hj, e'⟩ => e' ▸ hlt j hj) (FRC.Shell.imageList_length σ n)

/-! ### 5:E8 — no decomposition doubles a finite set -/

/-- 5:E8, 5:D5 (no paradoxical decomposition) — `X ⊔ X` does not inject into `X`: no map from `[0, 2n)` into `[0, n)`, `n ≥ 1`,
is injective. The restriction to `[0, n)` is onto (`inj_onto`), so `f n` already has a preimage below `n`. -/
theorem no_doubling (n : Nat) (hn : 0 < n) (f : Nat → Nat) (hf : ∀ x, x < 2 * n → f x < n) :
    ¬ ∀ x y, x < 2 * n → y < 2 * n → f x = f y → x = y :=
  fun hinj =>
    have hn2 : n < 2 * n := by rw [Nat.two_mul]; exact Nat.lt_add_of_pos_left hn
    have hlt : ∀ x, x < n → f x < n := fun x hx => hf x (Nat.lt_trans hx hn2)
    have hinj' : ∀ x y, x < n → y < n → f x = f y → x = y :=
      fun x y hx hy e => hinj x y (Nat.lt_trans hx hn2) (Nat.lt_trans hy hn2) e
    match inj_onto n f hlt hinj' (f n) (hf n hn2) with
    | ⟨x, hx, e⟩ => Nat.lt_irrefl n (hinj x n (Nat.lt_trans hx hn2) hn2 e ▸ hx)

/-! ### 5:E8 — every ultrafilter on a finite set is principal -/

/-- An ultrafilter on `[0, n)`, Boolean-valued on the subsets of `[0, n)` (Boolean predicates read below `n`): it
respects equality below `n`, excludes the empty set, is closed upward and under intersection, and holds a set or
its complement. -/
structure Ultra (n : Nat) where
  U : (Nat → Bool) → Bool
  congr : ∀ A B, (∀ x, x < n → A x = B x) → U A = true → U B = true
  proper : U (fun _ => false) = false
  up : ∀ A B, (∀ x, x < n → A x = true → B x = true) → U A = true → U B = true
  inter : ∀ A B, U A = true → U B = true → U (fun x => A x && B x) = true
  ultra : ∀ A, U A = true ∨ U (fun x => !A x) = true

/-- The positions from `k` on, `[k, n)` within `[0, n)`. -/
def above (k : Nat) : Nat → Bool := fun y => decide (k ≤ y)

/-- The singleton `{x}` as a predicate. -/
def pt (x : Nat) : Nat → Bool := fun y => decide (x = y)

theorem Ultra.univ {n : Nat} (F : Ultra n) : F.U (fun _ => true) = true :=
  match F.ultra (fun _ => false) with
  | Or.inl h => absurd h (by rw [F.proper]; exact Bool.false_ne_true)
  | Or.inr h => h

/-- `[k, n) ∖ {k} = [k + 1, n)`, pointwise. -/
theorem above_succ (k y : Nat) : (above k y && !pt k y) = above (k + 1) y :=
  match Nat.lt_or_ge y k with
  | Or.inl hlt => by
      show (decide (k ≤ y) && !decide (k = y)) = decide (k + 1 ≤ y)
      rw [decide_eq_false (Nat.not_le_of_lt hlt), decide_eq_false (Nat.not_le_of_lt (Nat.lt_succ_of_lt hlt))]; rfl
  | Or.inr hge => match Nat.eq_or_lt_of_le hge with
    | Or.inl e => by
        subst e
        show (decide (k ≤ k) && !decide (k = k)) = decide (k + 1 ≤ k)
        rw [decide_eq_true (Nat.le_refl k), decide_eq_true rfl, decide_eq_false (Nat.not_le_of_lt (Nat.lt_succ_self k))]; rfl
    | Or.inr hlt => by
        show (decide (k ≤ y) && !decide (k = y)) = decide (k + 1 ≤ y)
        have h1 : decide (k + 1 ≤ y) = true := decide_eq_true hlt
        rw [decide_eq_true (Nat.le_of_lt hlt), h1, decide_eq_false (fun e : k = y => Nat.lt_irrefl k (e ▸ hlt))]; rfl

/-- The search: below `k` some point is in the ultrafilter, or the tail `[k, n)` is. -/
theorem Ultra.search {n : Nat} (F : Ultra n) : ∀ k, (∃ x, x < k ∧ F.U (pt x) = true) ∨ F.U (above k) = true
  | 0 => Or.inr (F.congr (fun _ => true) (above 0) (fun _ _ => rfl) F.univ)
  | k + 1 =>
    match F.search k with
    | Or.inl ⟨x, hx, h⟩ => Or.inl ⟨x, Nat.lt_succ_of_lt hx, h⟩
    | Or.inr hk =>
      match F.ultra (pt k) with
      | Or.inl h => Or.inl ⟨k, Nat.lt_succ_self k, h⟩
      | Or.inr hc =>
        Or.inr (F.congr (fun y => above k y && !pt k y) (above (k + 1)) (fun y _ => above_succ k y)
          (F.inter (above k) (fun y => !pt k y) hk hc))

theorem and_not_self' (b : Bool) : (b && !b) = false := by cases b <;> rfl

/-- 5:E8 (every ultrafilter on a finite set is principal) — an ultrafilter on `[0, n)` holds a point `x`, and holds a
subset exactly when the subset holds `x`. -/
theorem ultra_principal {n : Nat} (F : Ultra n) : ∃ x, x < n ∧ ∀ A, F.U A = true ↔ A x = true :=
  match F.search n with
  | Or.inr h =>
    absurd (F.congr (above n) (fun _ => false) (fun y hy => decide_eq_false (Nat.not_le_of_lt hy)) h)
      (by rw [F.proper]; exact Bool.false_ne_true)
  | Or.inl ⟨x, hx, hpt⟩ => ⟨x, hx, fun A =>
    ⟨fun hA => match h : A x with
      | true => rfl
      | false =>
        have hc : F.U (fun y => !A y) = true :=
          F.up (pt x) (fun y => !A y) (fun y _ e => by
            have e' : x = y := of_decide_eq_true e
            rw [← e', h]; rfl) hpt
        have h0 : F.U (fun y => A y && !A y) = true := F.inter A (fun y => !A y) hA hc
        absurd (F.congr (fun y => A y && !A y) (fun _ => false) (fun y _ => and_not_self' (A y)) h0)
          (by rw [F.proper]; exact Bool.false_ne_true),
     fun hAx => F.up (pt x) A (fun y _ e => by have e' : x = y := of_decide_eq_true e; rw [← e']; exact hAx) hpt⟩⟩

end FRC.Sets
