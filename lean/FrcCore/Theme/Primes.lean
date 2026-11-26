import FrcCore.Theme.WindowModes

/-!
# The primes and the modes

20-rh's row G18 (26 November 2026), above the modes on the window (`Theme/WindowModes.lean`). A product of primes is
written as a list of primes, a prime of exponent `e` standing `e` times. Two lists of primes with one product hold
every number the same number of times (unique factorisation, by Euclid's lemma of `Theme/Field.lean`). So products
of primes below `p` with different exponents are different residues, and every relation between primes on the shell
has a product that has passed `p`. The primes of the window are the one set of labels that generates the labels of
the window with this property. Residues `X` at the primes of the window are the values of a mode exactly when they
satisfy every relation between those primes.
-/

namespace FRC
namespace Nat

open Pigeonhole

/-- The product of a list of numbers. -/
def listProd : List Nat → Nat
  | [] => 1
  | a :: l => a * listProd l

/-- Every member of the list has the property. -/
def ListAll (P : Nat → Prop) : List Nat → Prop
  | [] => True
  | a :: l => P a ∧ ListAll P l

/-- The number of times `n` stands in the list: the exponent of `n` in the product. -/
def listCount (n : Nat) : List Nat → Nat
  | [] => 0
  | a :: l => if a = n then listCount n l + 1 else listCount n l

theorem listCount_cons_eq {n a : Nat} (l : List Nat) (h : a = n) : listCount n (a :: l) = listCount n l + 1 :=
  ite_eq_left h

theorem listCount_cons_ne {n a : Nat} (l : List Nat) (h : ¬ a = n) : listCount n (a :: l) = listCount n l :=
  ite_eq_right h

theorem listAll_mono {P Q : Nat → Prop} (h : ∀ a, P a → Q a) : ∀ {l : List Nat}, ListAll P l → ListAll Q l
  | [], _ => True.intro
  | _ :: _, hl => ⟨h _ hl.1, listAll_mono h hl.2⟩

theorem listAll_append {P : Nat → Prop} : ∀ {l m : List Nat}, ListAll P l → ListAll P m → ListAll P (l ++ m)
  | [], _, _, hm => hm
  | _ :: _, _, hl, hm => ⟨hl.1, listAll_append hl.2 hm⟩

theorem listProd_append : ∀ l m : List Nat, listProd (l ++ m) = listProd l * listProd m
  | [], _ => (Nat.one_mul _).symm
  | a :: l, m => by
    show a * listProd (l ++ m) = a * listProd l * listProd m
    rw [listProd_append l m, mul_assoc]

theorem listProd_pos : ∀ {l : List Nat}, ListAll (fun a => 0 < a) l → 0 < listProd l
  | [], _ => Nat.zero_lt_succ 0
  | _ :: _, hl => Nat.mul_pos hl.1 (listProd_pos hl.2)

theorem le_listProd_cons {a : Nat} {l : List Nat} (hl : 0 < listProd l) : a ≤ listProd (a :: l) := by
  have := Nat.mul_le_mul_left a hl
  rw [Nat.mul_one] at this; exact this

theorem listProd_erase {v : Nat} : ∀ {l : List Nat}, mem v l → listProd l = v * listProd (erase v l)
  | [], h => absurd h id
  | a :: l, h => by
    exact match Nat.decEq a v with
      | isTrue e => by rw [show erase v (a :: l) = l from ite_eq_left e, e]; rfl
      | isFalse e => by
          rw [show erase v (a :: l) = a :: erase v l from ite_eq_right e]
          have hm : mem v l := match h with
            | Or.inl h' => absurd h'.symm e
            | Or.inr h' => h'
          show a * listProd l = v * (a * listProd (erase v l))
          rw [listProd_erase hm, mul_left_comm]

theorem listAll_erase {P : Nat → Prop} (v : Nat) : ∀ {l : List Nat}, ListAll P l → ListAll P (erase v l)
  | [], _ => True.intro
  | a :: l, hl => by
    exact match Nat.decEq a v with
      | isTrue e => by rw [show erase v (a :: l) = l from ite_eq_left e]; exact hl.2
      | isFalse e => by
          rw [show erase v (a :: l) = a :: erase v l from ite_eq_right e]
          exact ⟨hl.1, listAll_erase v hl.2⟩

theorem listCount_erase_self {v : Nat} : ∀ {l : List Nat}, mem v l → listCount v l = listCount v (erase v l) + 1
  | [], h => absurd h id
  | a :: l, h => by
    exact match Nat.decEq a v with
      | isTrue e => by rw [show erase v (a :: l) = l from ite_eq_left e, listCount_cons_eq l e]
      | isFalse e => by
          rw [show erase v (a :: l) = a :: erase v l from ite_eq_right e, listCount_cons_ne l e,
            listCount_cons_ne _ e]
          exact listCount_erase_self (match h with
            | Or.inl h' => absurd h'.symm e
            | Or.inr h' => h')

theorem listCount_erase_ne {n v : Nat} (hn : ¬ v = n) : ∀ l : List Nat, listCount n l = listCount n (erase v l)
  | [] => rfl
  | a :: l => by
    exact match Nat.decEq a v with
      | isTrue e => by
          rw [show erase v (a :: l) = l from ite_eq_left e, listCount_cons_ne l (fun h => hn (e.symm.trans h))]
      | isFalse e => by
          rw [show erase v (a :: l) = a :: erase v l from ite_eq_right e]
          exact match Nat.decEq a n with
            | isTrue e' => by rw [listCount_cons_eq l e', listCount_cons_eq _ e', listCount_erase_ne hn l]
            | isFalse e' => by rw [listCount_cons_ne l e', listCount_cons_ne _ e', listCount_erase_ne hn l]

/-- A prime that divides a product of primes is one of them. -/
theorem prime_mem_of_dvd {ℓ : Nat} (hℓ : isPrime ℓ) :
    ∀ {l : List Nat}, ListAll isPrime l → listProd l % ℓ = 0 → mem ℓ l
  | [], _, h => by
    have h1 : (1 : Nat) % ℓ = 1 := mod_eq_of_lt hℓ.1
    exact absurd (h1.symm.trans h) (succ_ne_zero 0)
  | a :: l, hl, h => by
    have h' : (a * listProd l) % ℓ = 0 := h
    cases prime_mul_mod hℓ h' with
    | inr h2 => exact Or.inr (prime_mem_of_dvd hℓ hl.2 h2)
    | inl h1 =>
      have ha := hl.1
      cases Nat.lt_or_ge ℓ a with
      | inl hlt => exact absurd h1 (ha.2 ℓ hlt hℓ.1)
      | inr hge =>
        cases Nat.lt_or_eq_of_le hge with
        | inl hlt =>
          have e : a % ℓ = a := mod_eq_of_lt hlt
          rw [e] at h1
          have ha0 : 0 < a := Nat.lt_of_lt_of_le (Nat.zero_lt_succ 1) ha.1
          rw [h1] at ha0
          exact absurd ha0 (Nat.lt_irrefl 0)
        | inr heq => exact Or.inl heq.symm

theorem listProd_eq_one : ∀ {l : List Nat}, ListAll isPrime l → listProd l = 1 → l = []
  | [], _, _ => rfl
  | a :: l, hl, h => by
    have hpos : 0 < listProd l :=
      listProd_pos (listAll_mono (fun _ hb => Nat.lt_of_lt_of_le (Nat.zero_lt_succ 1) hb.1) hl.2)
    have h2 : 2 ≤ listProd (a :: l) := Nat.le_trans hl.1.1 (le_listProd_cons hpos)
    rw [h] at h2
    exact absurd h2 (by decide)

/-- Unique factorisation: two lists of primes with one product hold every number the same number of times. -/
theorem prime_lists_unique : ∀ (L M : List Nat), ListAll isPrime L → ListAll isPrime M →
    listProd L = listProd M → ∀ n, listCount n L = listCount n M
  | [], M, _, hM, h, n => by rw [listProd_eq_one hM h.symm]
  | ℓ :: L, M, hL, hM, h, n => by
    have hℓ := hL.1
    have hℓ0 : 0 < ℓ := Nat.lt_of_lt_of_le (Nat.zero_lt_succ 1) hℓ.1
    have hdiv : listProd M % ℓ = 0 := by
      rw [← h]
      show (ℓ * listProd L) % ℓ = 0
      exact mul_mod_eq_zero_left hℓ0 (mod_self ℓ hℓ0)
    have hmem := prime_mem_of_dvd hℓ hM hdiv
    have hprod : listProd L = listProd (erase ℓ M) :=
      Nat.eq_of_mul_eq_mul_left hℓ0 (h.trans (listProd_erase hmem))
    have ih := prime_lists_unique L (erase ℓ M) hL.2 (listAll_erase ℓ hM) hprod
    exact match Nat.decEq ℓ n with
      | isTrue e => by rw [listCount_cons_eq L e, ← e, listCount_erase_self hmem, ih ℓ]
      | isFalse e => by rw [listCount_cons_ne L e, listCount_erase_ne e M, ih n]

end Nat

namespace Horizon

open FRC.Shell FRC.Shell.Frame

variable {p : Nat} [Pos p] {κ : Nat} {g : Shell p}

section primes20261126

/-- The residue of a label. -/
abbrev labelRes (p : Nat) [Pos p] (n : Nat) : Shell p := ofNat n

/-- A prime of the window. -/
abbrev WPrime (q n : Nat) : Prop := Nat.isPrime n ∧ n ≤ q

/-- `t` copies of a list, one after another: the `t`-th power of its product. -/
def repList : Nat → List Nat → List Nat
  | 0, _ => []
  | t + 1, l => l ++ repList t l

theorem prodList_append (G : Nat → Shell p) : ∀ l m : List Nat, prodList G (l ++ m) = prodList G l * prodList G m
  | [], _ => (one_mul _).symm
  | a :: l, m => by
    show G a * prodList G (l ++ m) = G a * prodList G l * prodList G m
    rw [prodList_append G l m, mul_assoc]

theorem prodList_repList (G : Nat → Shell p) (l : List Nat) : ∀ t : Nat, prodList G (repList t l) = prodList G l ^ t
  | 0 => rfl
  | t + 1 => by
    show prodList G (l ++ repList t l) = prodList G l ^ t * prodList G l
    rw [prodList_append, prodList_repList G l t, mul_comm]

theorem listAll_repList {P : Nat → Prop} {l : List Nat} (hl : Nat.ListAll P l) : ∀ t : Nat, Nat.ListAll P (repList t l)
  | 0 => True.intro
  | t + 1 => Nat.listAll_append hl (listAll_repList hl t)

theorem ofNat_listProd : ∀ l : List Nat, (ofNat (Nat.listProd l) : Shell p) = prodList (labelRes p) l
  | [] => rfl
  | a :: l => by
    show (ofNat (a * Nat.listProd l) : Shell p) = ofNat a * prodList (labelRes p) l
    rw [← ofNat_mul, ofNat_listProd l]

theorem prodList_pow (G : Nat → Shell p) (k : Nat) :
    ∀ l : List Nat, prodList (fun n => G n ^ k) l = prodList G l ^ k
  | [] => (one_pow k).symm
  | a :: l => by
    show G a ^ k * prodList (fun n => G n ^ k) l = (G a * prodList G l) ^ k
    rw [prodList_pow G k l, mul_pow]

theorem prodList_congr {P : Nat → Prop} {G H : Nat → Shell p} (h : ∀ a, P a → G a = H a) :
    ∀ {l : List Nat}, Nat.ListAll P l → prodList G l = prodList H l
  | [], _ => rfl
  | a :: l, hl => by
    show G a * prodList G l = H a * prodList H l
    rw [h a hl.1, prodList_congr h hl.2]

theorem prodList_window_ne_zero (F : Frame p κ g) {q : Nat} (hq1 : q * q < p) :
    ∀ {l : List Nat}, Nat.ListAll (WPrime q) l → prodList (labelRes p) l ≠ 0
  | [], _ => F.one_ne_zero
  | _ :: _, hl =>
    F.mul_ne_zero (window_label_ne_zero hq1 (Nat.lt_of_lt_of_le (Nat.zero_lt_succ 1) hl.1.1.1) hl.1.2)
      (prodList_window_ne_zero F hq1 hl.2)

/-- 20:G18 — products of primes below `p` with different exponents are different residues: two lists of primes
whose products are below `p` and are one residue hold every prime the same number of times. -/
theorem prime_products_distinct {L M : List Nat} (hL : Nat.ListAll Nat.isPrime L) (hM : Nat.ListAll Nat.isPrime M)
    (hLp : Nat.listProd L < p) (hMp : Nat.listProd M < p)
    (h : prodList (labelRes p) L = prodList (labelRes p) M) : ∀ n, Nat.listCount n L = Nat.listCount n M :=
  Nat.prime_lists_unique L M hL hM (eq_of_ofNat_eq hLp hMp (by rw [ofNat_listProd, ofNat_listProd]; exact h))

/-- 20:G18 — every relation between primes has wrapped: when two lists of primes with different exponents have
one product on the shell, one of the two products has passed `p`. -/
theorem relation_wrapped {L M : List Nat} (hL : Nat.ListAll Nat.isPrime L) (hM : Nat.ListAll Nat.isPrime M)
    (h : prodList (labelRes p) L = prodList (labelRes p) M) {n : Nat}
    (hn : Nat.listCount n L ≠ Nat.listCount n M) : p ≤ Nat.listProd L ∨ p ≤ Nat.listProd M :=
  match Nat.lt_or_ge (Nat.listProd L) p with
  | Or.inr h1 => Or.inl h1
  | Or.inl h1 =>
    match Nat.lt_or_ge (Nat.listProd M) p with
    | Or.inr h2 => Or.inr h2
    | Or.inl h2 => absurd (prime_products_distinct hL hM h1 h2 h n) hn

/-- 20:G18 — the primes are the one generating set of labels with this property. Let `S` be a set of labels
`2 ≤ s ≤ q` such that every label of the window is a product of members of `S`, and two products of members of
`S` below `p` that are one residue have the same exponents. Then `S` is the set of the primes of the window. -/
theorem primes_unique_generators {q : Nat} (hq1 : q * q < p) (S : Nat → Prop) (hS : ∀ s, S s → 2 ≤ s ∧ s ≤ q)
    (gen : ∀ n, 0 < n → n ≤ q → ∃ L, Nat.ListAll S L ∧ Nat.listProd L = n)
    (free : ∀ L M, Nat.ListAll S L → Nat.ListAll S M → Nat.listProd L < p → Nat.listProd M < p →
      prodList (labelRes p) L = prodList (labelRes p) M → ∀ n, Nat.listCount n L = Nat.listCount n M) :
    ∀ n, S n ↔ (Nat.isPrime n ∧ n ≤ q) := by
  have hpos : ∀ {l : List Nat}, Nat.ListAll S l → 0 < Nat.listProd l := fun hl =>
    Nat.listProd_pos (Nat.listAll_mono (fun s hs => Nat.lt_of_lt_of_le (Nat.zero_lt_succ 1) (hS s hs).1) hl)
  intro n
  constructor
  · intro hs
    have h2 := (hS n hs).1
    have hnq := (hS n hs).2
    refine ⟨?_, hnq⟩
    cases Nat.prime_or_divisor n h2 with
    | inl hpr => exact hpr
    | inr hd =>
      match hd with
      | ⟨d, hd2, hdn, hd0⟩ =>
        have hdpos : 0 < d := Nat.lt_of_lt_of_le (Nat.zero_lt_succ 1) hd2
        match Nat.dvd_factor hdpos hd0 with
        | ⟨e, he⟩ =>
          have hn0 : 0 < n := Nat.lt_of_lt_of_le (Nat.zero_lt_succ 1) h2
          have he0 : 0 < e := by
            cases e with
            | zero => rw [he, Nat.mul_zero] at hn0; exact absurd hn0 (Nat.lt_irrefl 0)
            | succ e => exact Nat.zero_lt_succ e
          have hen : e ≤ n := by
            have := Nat.mul_le_mul_right e hdpos
            rw [Nat.one_mul, ← he] at this; exact this
          have hq0 : 0 < q := Nat.lt_of_lt_of_le hn0 hnq
          have hnp : n < p := by
            have := Nat.mul_le_mul_left q hq0
            rw [Nat.mul_one] at this
            exact Nat.lt_of_le_of_lt (Nat.le_trans hnq this) hq1
          match gen d hdpos (Nat.le_trans (Nat.le_of_lt hdn) hnq), gen e he0 (Nat.le_trans hen hnq) with
          | ⟨Ld, hLd, ed⟩, ⟨Le, hLe, ee⟩ =>
            match Ld, hLd, ed with
            | [], _, ed => exact absurd (show 2 ≤ 1 from Nat.le_trans hd2 (Nat.le_of_eq ed.symm)) (by decide)
            | x :: Ld', hLd, ed =>
              have hprod1 : Nat.listProd [n] = n := Nat.mul_one n
              have hprod2 : Nat.listProd ((x :: Ld') ++ Le) = n := by
                rw [Nat.listProd_append, ed, ee, ← he]
              have hc := free [n] ((x :: Ld') ++ Le) ⟨hs, True.intro⟩ (Nat.listAll_append hLd hLe)
                (by rw [hprod1]; exact hnp) (by rw [hprod2]; exact hnp)
                (by rw [← ofNat_listProd, ← ofNat_listProd, hprod1, hprod2]) x
              have hxd : x ≤ d := by
                have := Nat.le_listProd_cons (a := x) (hpos hLd.2)
                rw [ed] at this; exact this
              have hc2 : Nat.listCount x ((x :: Ld') ++ Le) = Nat.listCount x (Ld' ++ Le) + 1 :=
                Nat.listCount_cons_eq _ rfl
              exact match Nat.decEq n x with
                | isTrue e' => absurd (Nat.lt_of_le_of_lt hxd hdn) (by rw [e']; exact Nat.lt_irrefl x)
                | isFalse e' => by
                    rw [hc2, Nat.listCount_cons_ne [] e'] at hc
                    exact absurd hc.symm (Nat.succ_ne_zero _)
  · intro hn
    match gen n (Nat.lt_of_lt_of_le (Nat.zero_lt_succ 1) hn.1.1) hn.2 with
    | ⟨L, hL, eL⟩ =>
      match L, hL, eL with
      | [], _, eL => exact absurd (show 2 ≤ 1 from Nat.le_trans hn.1.1 (Nat.le_of_eq eL.symm)) (by decide)
      | x :: L', hL, eL =>
        have hx0 : 0 < x := Nat.lt_of_lt_of_le (Nat.zero_lt_succ 1) (hS x hL.1).1
        have hxn : x ≤ n := by
          have := Nat.le_listProd_cons (a := x) (hpos hL.2)
          rw [eL] at this; exact this
        cases Nat.lt_or_eq_of_le hxn with
        | inl hlt =>
          have hmod : n % x = 0 := by
            rw [← eL]
            show (x * Nat.listProd L') % x = 0
            exact Nat.mul_mod_eq_zero_left hx0 (Nat.mod_self x hx0)
          exact absurd hmod (hn.1.2 x hlt (hS x hL.1).1)
        | inr heq => rw [← heq]; exact hL.1

/-- Every label of the window is the product of a list of primes of the window. -/
theorem exists_prime_list (q : Nat) :
    ∀ n, 0 < n → n ≤ q → ∃ L, Nat.ListAll (WPrime q) L ∧ Nat.listProd L = n :=
  Nat.label_induction (fun n => ∃ L, Nat.ListAll (WPrime q) L ∧ Nat.listProd L = n) ⟨[], True.intro, rfl⟩
    (fun _ _ ha hb =>
      match ha, hb with
      | ⟨La, hLa, ea⟩, ⟨Lb, hLb, eb⟩ =>
        ⟨La ++ Lb, Nat.listAll_append hLa hLb, by rw [Nat.listProd_append, ea, eb]⟩)
    (fun ℓ hℓ hℓq => ⟨[ℓ], ⟨⟨hℓ, hℓq⟩, True.intro⟩, Nat.mul_one ℓ⟩)

/-- The generator is a quotient of two products of primes of the window. -/
theorem generator_quotient (F : Frame p κ g) {q : Nat} (hq1 : q * q < p) (hq2 : p < (q + 1) * (q + 1)) :
    ∃ LA LB, Nat.ListAll (WPrime q) LA ∧ Nat.ListAll (WPrime q) LB ∧
      prodList (labelRes p) LA = g * prodList (labelRes p) LB := by
  match thue_ne_zero F hq1 hq2 F.g_ne_zero with
  | ⟨a, b, ha0, ha, hb0, hb, hab⟩ =>
    match exists_prime_list q a ha0 ha, exists_prime_list q b hb0 hb with
    | ⟨La, hLa, ea⟩, ⟨Lb, hLb, eb⟩ =>
      have eA : prodList (labelRes p) La = ofNat a := by rw [← ofNat_listProd, ea]
      have eB : prodList (labelRes p) Lb = ofNat b := by rw [← ofNat_listProd, eb]
      cases hab with
      | inl h => exact ⟨La, Lb, hLa, hLb, by rw [eA, eB]; exact h⟩
      | inr h =>
        refine ⟨repList (2 * κ + 1) La, repList (2 * κ + 1) Lb, listAll_repList hLa _, listAll_repList hLb _, ?_⟩
        have hsq : ((-1 : Shell p) ^ 2) = 1 := by
          show ((-1 : Shell p) ^ 1) * (-1) = 1
          rw [pow_one, neg_mul_neg, one_mul]
        have hodd : (-1 : Shell p) ^ (2 * κ + 1) = -1 := by rw [pow_succ, pow_mul, hsq, one_pow, one_mul]
        have hg : g ^ (2 * κ + 1) = -g := by rw [pow_succ, F.half_period, neg_one_mul]
        rw [prodList_repList, prodList_repList, eA, eB, h,
          show -(g * ofNat b) = -1 * (g * ofNat b) from (neg_one_mul _).symm, mul_pow, mul_pow, hodd, hg, neg_one_mul,
          ← neg_mul, neg_neg]

/-- 20:G18 — residues `X` at the primes of the window are the values of a mode exactly when they satisfy every
relation between those primes: whenever two products of primes of the window are one residue, the two products of
the `X` are one residue. -/
theorem mode_iff_relations (F : Frame p κ g) {q : Nat} (hq1 : q * q < p) (hq2 : p < (q + 1) * (q + 1))
    (X : Nat → Shell p) :
    (∀ L M, Nat.ListAll (WPrime q) L → Nat.ListAll (WPrime q) M →
        prodList (labelRes p) L = prodList (labelRes p) M → prodList X L = prodList X M) ↔
      ∃ k, k < p - 1 ∧ ∀ ℓ, Nat.isPrime ℓ → ℓ ≤ q → X ℓ = (ofNat ℓ : Shell p) ^ k := by
  constructor
  · intro hrel
    match generator_quotient F hq1 hq2 with
    | ⟨LA, LB, hLA, hLB, hAB⟩ =>
      have hpos : 0 < p - 1 := Nat.lt_of_le_of_lt (Nat.zero_le _) F.two_kappa_lt
      have hcard : p - 1 - 1 + 1 = p - 1 := Nat.sub_add_cancel hpos
      have hper : ∀ L, Nat.ListAll (WPrime q) L → prodList X L ^ (p - 1) = 1 := by
        intro L hL
        have := hrel (repList (p - 1) L) [] (listAll_repList hL _) True.intro
          (by rw [prodList_repList]; exact unit_pow_card F (prodList_window_ne_zero F hq1 hL))
        rw [prodList_repList] at this; exact this
      have hXA := hper LA hLA
      have hXB := hper LB hLB
      have hinv : prodList X LB * prodList X LB ^ (p - 1 - 1) = 1 := by
        rw [mul_comm, ← pow_succ, hcard]; exact hXB
      have hne : ∀ {x : Shell p}, x ^ (p - 1) = 1 → x ≠ 0 := by
        intro x hx h0
        rw [h0, ← hcard, pow_succ, mul_zero] at hx
        exact F.one_ne_zero hx.symm
      have hW : prodList X LA * prodList X LB ^ (p - 1 - 1) ≠ 0 :=
        F.mul_ne_zero (hne hXA) (pow_ne_zero_of F (hne hXB) _)
      match F.eq_pow_of_ne_zero hW with
      | ⟨k, hk, hgk⟩ =>
        refine ⟨k, hk, fun ℓ hℓ hℓq => ?_⟩
        have hx : (ofNat ℓ : Shell p) ≠ 0 :=
          window_label_ne_zero hq1 (Nat.lt_of_lt_of_le (Nat.zero_lt_succ 1) hℓ.1) hℓq
        match F.eq_pow_of_ne_zero hx with
        | ⟨t, _, hgt⟩ =>
          have hr := hrel (repList t LA) (ℓ :: repList t LB) (listAll_repList hLA t)
            ⟨⟨hℓ, hℓq⟩, listAll_repList hLB t⟩
            (by
              show prodList (labelRes p) (repList t LA) = ofNat ℓ * prodList (labelRes p) (repList t LB)
              rw [prodList_repList, prodList_repList, hAB, mul_pow, hgt])
          have hr' : prodList X LA ^ t = X ℓ * prodList X LB ^ t := by
            rw [← prodList_repList, ← prodList_repList]; exact hr
          calc X ℓ = X ℓ * (prodList X LB * prodList X LB ^ (p - 1 - 1)) ^ t := by rw [hinv, one_pow, mul_one]
            _ = (X ℓ * prodList X LB ^ t) * (prodList X LB ^ (p - 1 - 1)) ^ t := by rw [mul_pow, mul_assoc]
            _ = (prodList X LA * prodList X LB ^ (p - 1 - 1)) ^ t := by rw [← hr', mul_pow]
            _ = (g ^ k) ^ t := by rw [hgk]
            _ = (g ^ t) ^ k := pow_mul_comm g k t
            _ = (ofNat ℓ : Shell p) ^ k := by rw [hgt]
  · intro hk L M hL hM h
    match hk with
    | ⟨k, _, hX⟩ =>
      have e : ∀ {l : List Nat}, Nat.ListAll (WPrime q) l → prodList X l = prodList (labelRes p) l ^ k := by
        intro l hl
        rw [← prodList_pow]
        exact prodList_congr (fun a ha => hX a ha.1 ha.2) hl
      rw [e hL, e hM, h]

end primes20261126

end Horizon
end FRC
