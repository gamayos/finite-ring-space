import FrcCore.Pigeonhole
import FrcCore.Frame

/-!
# FrcCore.Theme.Thue — every nonzero residue is a signed quotient of two labels of the window (20-rh, 26 November 2026)

Thue's lemma by the pigeonhole on pairs. With `q` the largest label whose square is below `p`, the `(q + 1)²` pairs
`(a, b)`, `0 ≤ a, b ≤ q`, are more than the `p` residues, so two of them give one residue `a − r·b`; their difference
is a pair of labels with `a = ±r·b`. The pairs are counted by a counter (`pairOf`), with no division. With `r` the
quarter-turn the two labels have `a² + b² = p`. No axioms.
-/

namespace FRC
namespace Thue

open Pigeonhole

/-! ## The pigeonhole on a function -/

/-- The table of the first `m` values of `f`, the last first. -/
def tab (f : Nat → Nat) : Nat → List Nat
  | 0 => []
  | m + 1 => f m :: tab f m

theorem tab_length (f : Nat → Nat) : ∀ m, (tab f m).length = m
  | 0 => rfl
  | m + 1 => congrArg Nat.succ (tab_length f m)

theorem mem_tab {f : Nat → Nat} {v : Nat} : ∀ {m : Nat}, mem v (tab f m) → ∃ i, i < m ∧ f i = v
  | 0, h => absurd h id
  | m + 1, h => match h with
    | Or.inl e => ⟨m, Nat.lt_succ_self m, e.symm⟩
    | Or.inr h' => match mem_tab h' with
      | ⟨i, hi, e⟩ => ⟨i, Nat.lt_succ_of_lt hi, e⟩

/-- Two of the first `m` values coincide, or the table has no duplicates. -/
theorem collision_or_nodup (f : Nat → Nat) : ∀ m, (∃ i j, i < j ∧ j < m ∧ f i = f j) ∨ NoDup (tab f m)
  | 0 => Or.inr trivial
  | m + 1 => match collision_or_nodup f m with
    | Or.inl ⟨i, j, hij, hj, e⟩ => Or.inl ⟨i, j, hij, Nat.lt_succ_of_lt hj, e⟩
    | Or.inr hnd => match decMem (f m) (tab f m) with
      | isTrue hm => match mem_tab hm with
        | ⟨i, hi, e⟩ => Or.inl ⟨i, m, hi, Nat.lt_succ_self m, e⟩
      | isFalse hm => Or.inr ⟨hm, hnd⟩

/-- The pigeonhole: `N` values below `n < N` have two equal. -/
theorem collision (f : Nat → Nat) {n N : Nat} (hf : ∀ i, i < N → f i < n) (hN : n < N) :
    ∃ i j, i < j ∧ j < N ∧ f i = f j :=
  match collision_or_nodup f N with
  | Or.inl h => h
  | Or.inr hnd =>
    have hb : ∀ e, mem e (tab f N) → e < n := fun _ he => match mem_tab he with
      | ⟨i, hi, e'⟩ => e' ▸ hf i hi
    have h1 : (tab f N).length ≤ n := length_le_of_nodup_lt n (tab f N) hnd hb
    have h2 : N ≤ n := tab_length f N ▸ h1
    absurd (Nat.lt_of_lt_of_le hN h2) (Nat.lt_irrefl n)

/-! ## The counter of pairs -/

/-- The counter: `pairOf n t = (a, b)` with `t = n·a + b` and `b < n`. -/
def pairOf (n : Nat) : Nat → Nat × Nat
  | 0 => (0, 0)
  | t + 1 => if (pairOf n t).2 + 1 < n then ((pairOf n t).1, (pairOf n t).2 + 1) else ((pairOf n t).1 + 1, 0)

theorem pairOf_succ_lt {n t : Nat} (h : (pairOf n t).2 + 1 < n) :
    pairOf n (t + 1) = ((pairOf n t).1, (pairOf n t).2 + 1) := ite_eq_left h

theorem pairOf_succ_ge {n t : Nat} (h : ¬ (pairOf n t).2 + 1 < n) :
    pairOf n (t + 1) = ((pairOf n t).1 + 1, 0) := ite_eq_right h

theorem pairOf_spec {n : Nat} (hn : 0 < n) : ∀ t, n * (pairOf n t).1 + (pairOf n t).2 = t ∧ (pairOf n t).2 < n
  | 0 => ⟨by show n * 0 + 0 = 0; rw [Nat.mul_zero], hn⟩
  | t + 1 =>
    have ih := pairOf_spec hn t
    match Nat.decLt ((pairOf n t).2 + 1) n with
    | isTrue h => by
        rw [pairOf_succ_lt h]
        exact ⟨by show n * (pairOf n t).1 + ((pairOf n t).2 + 1) = t + 1; rw [← Nat.add_assoc, ih.1], h⟩
    | isFalse h => by
        rw [pairOf_succ_ge h]
        have e : (pairOf n t).2 + 1 = n := Nat.le_antisymm ih.2 (Nat.le_of_not_lt h)
        exact ⟨by
          show n * ((pairOf n t).1 + 1) + 0 = t + 1
          calc n * ((pairOf n t).1 + 1) + 0 = n * (pairOf n t).1 + n := by rw [Nat.add_zero, Nat.mul_succ]
            _ = n * (pairOf n t).1 + ((pairOf n t).2 + 1) := by rw [e]
            _ = n * (pairOf n t).1 + (pairOf n t).2 + 1 := (Nat.add_assoc _ _ _).symm
            _ = t + 1 := by rw [ih.1], hn⟩

theorem pairOf_fst_lt {n t : Nat} (hn : 0 < n) (ht : t < n * n) : (pairOf n t).1 < n :=
  match Nat.lt_or_ge (pairOf n t).1 n with
  | Or.inl h => h
  | Or.inr h =>
    have h1 : n * n ≤ n * (pairOf n t).1 := Nat.mul_le_mul_left n h
    have h2 : n * (pairOf n t).1 ≤ n * (pairOf n t).1 + (pairOf n t).2 := Nat.le_add_right _ _
    have h3 : n * (pairOf n t).1 ≤ t := Nat.le_trans h2 (Nat.le_of_eq (pairOf_spec hn t).1)
    absurd (Nat.lt_of_lt_of_le ht (Nat.le_trans h1 h3)) (Nat.lt_irrefl t)

/-- Different indices have different pairs. -/
theorem pairOf_inj {n i j : Nat} (hn : 0 < n) (h1 : (pairOf n i).1 = (pairOf n j).1) (h2 : (pairOf n i).2 = (pairOf n j).2) :
    i = j := by
  have ei := (pairOf_spec hn i).1
  have ej := (pairOf_spec hn j).1
  rw [h1, h2] at ei
  exact ei.symm.trans ej

end Thue

namespace Horizon

open FRC.Shell FRC.Shell.Frame FRC.Thue

variable {p : Nat} [Pos p] {κ : Nat} {g : Shell p}

section thue20261126

/-! ## The ring steps -/

theorem sub_eq_sub {x y u v : Shell p} (h : x + -u = y + -v) : x + v = y + u := by
  have e1 : x + -u + (u + v) = x + v := by
    rw [← add_assoc, add_assoc x, neg_add, add_zero]
  have e2 : y + -v + (u + v) = y + u := by
    rw [add_comm u v, ← add_assoc, add_assoc y, neg_add, add_zero]
  rw [← e1, ← e2, h]

/-- Both differences on one side: from `(a' + A) + r·b' = a' + r·(b' + B)` follows `A = r·B`. -/
theorem same_dir (r : Shell p) {a' A b' B : Nat}
    (H : (ofNat (a' + A) : Shell p) + r * ofNat b' = ofNat a' + r * ofNat (b' + B)) :
    (ofNat A : Shell p) = r * ofNat B := by
  rw [← ofNat_add, ← ofNat_add, left_distrib] at H
  have e1 : (ofNat a' : Shell p) + ofNat A + r * ofNat b' = ofNat A + (ofNat a' + r * ofNat b') := by
    rw [add_comm (ofNat a') (ofNat A), add_assoc]
  have e2 : (ofNat a' : Shell p) + (r * ofNat b' + r * ofNat B) = r * ofNat B + (ofNat a' + r * ofNat b') := by
    rw [add_comm (r * ofNat b') (r * ofNat B), add_left_comm, add_comm (r * ofNat B)]
  rw [e1, e2] at H
  exact add_right_cancel H

/-- The differences on opposite sides: from `(a' + A) + r·(b + B) = a' + r·b` follows `A = −(r·B)`. -/
theorem opp_dir (r : Shell p) {a' A b B : Nat}
    (H : (ofNat (a' + A) : Shell p) + r * ofNat (b + B) = ofNat a' + r * ofNat b) :
    (ofNat A : Shell p) = -(r * ofNat B) := by
  rw [← ofNat_add, ← ofNat_add, left_distrib] at H
  have e1 : (ofNat a' : Shell p) + ofNat A + (r * ofNat b + r * ofNat B)
      = ofNat A + r * ofNat B + (ofNat a' + r * ofNat b) := by
    rw [add_add_add_comm, add_comm (ofNat a' + r * ofNat b)]
  have e2 : (ofNat a' : Shell p) + r * ofNat b = 0 + (ofNat a' + r * ofNat b) := (zero_add _).symm
  rw [e1] at H
  have H' := add_right_cancel (H.trans e2)
  exact eq_neg_of_add_eq_zero H'

/-! ## Thue's lemma -/

/-- The residue `a − r·b` of the pair with the index `t`. -/
def gap (r : Shell p) (n t : Nat) : Nat := (ofNat (pairOf n t).1 + -(r * ofNat (pairOf n t).2)).val

/-- Two different pairs of labels with one residue `a − r·b` give labels `A`, `B` with `A = ±r·B`. -/
theorem thue_step (r : Shell p) {q a b a' b' : Nat} (ha : a ≤ q) (hb : b ≤ q) (ha' : a' ≤ q) (hb' : b' ≤ q)
    (hne : ¬ (a = a' ∧ b = b')) (H : (ofNat a : Shell p) + r * ofNat b' = ofNat a' + r * ofNat b) :
    ∃ A B, A ≤ q ∧ B ≤ q ∧ (0 < A ∨ 0 < B) ∧
      ((ofNat A : Shell p) = r * ofNat B ∨ (ofNat A : Shell p) = -(r * ofNat B)) :=
  have pos : ∀ {A B : Nat}, ¬ (A = 0 ∧ B = 0) → 0 < A ∨ 0 < B := fun {A B} h =>
    match Nat.eq_zero_or_pos A with
    | Or.inr hA => Or.inl hA
    | Or.inl hA => match Nat.eq_zero_or_pos B with
      | Or.inr hB => Or.inr hB
      | Or.inl hB => absurd ⟨hA, hB⟩ h
  match Nat.le_total a' a, Nat.le_total b' b with
  | Or.inl h1, Or.inl h2 =>
    match Nat.le.dest h1, Nat.le.dest h2 with
    | ⟨A, hA⟩, ⟨B, hB⟩ => by
      subst hA; subst hB
      exact ⟨A, B, Nat.le_trans (Nat.le_add_left A a') ha, Nat.le_trans (Nat.le_add_left B b') hb,
        pos (fun ⟨eA, eB⟩ => hne ⟨by rw [eA]; rfl, by rw [eB]; rfl⟩), Or.inl (same_dir r H)⟩
  | Or.inl h1, Or.inr h2 =>
    match Nat.le.dest h1, Nat.le.dest h2 with
    | ⟨A, hA⟩, ⟨B, hB⟩ => by
      subst hA; subst hB
      exact ⟨A, B, Nat.le_trans (Nat.le_add_left A a') ha, Nat.le_trans (Nat.le_add_left B b) hb',
        pos (fun ⟨eA, eB⟩ => hne ⟨by rw [eA]; rfl, by rw [eB]; rfl⟩), Or.inr (opp_dir r H)⟩
  | Or.inr h1, Or.inr h2 =>
    match Nat.le.dest h1, Nat.le.dest h2 with
    | ⟨A, hA⟩, ⟨B, hB⟩ => by
      subst hA; subst hB
      exact ⟨A, B, Nat.le_trans (Nat.le_add_left A a) ha', Nat.le_trans (Nat.le_add_left B b) hb',
        pos (fun ⟨eA, eB⟩ => hne ⟨by rw [eA]; rfl, by rw [eB]; rfl⟩), Or.inl (same_dir r H.symm)⟩
  | Or.inr h1, Or.inl h2 =>
    match Nat.le.dest h1, Nat.le.dest h2 with
    | ⟨A, hA⟩, ⟨B, hB⟩ => by
      subst hA; subst hB
      exact ⟨A, B, Nat.le_trans (Nat.le_add_left A a) ha', Nat.le_trans (Nat.le_add_left B b') hb,
        pos (fun ⟨eA, eB⟩ => hne ⟨by rw [eA]; rfl, by rw [eB]; rfl⟩), Or.inr (opp_dir r H.symm)⟩

/-- 20:G17 — Thue's lemma. With `p < (q + 1)²`, for every residue `r` there are labels `a, b ≤ q`, not both `0`,
with `a = r·b` or `a = −r·b` on the shell. -/
theorem thue {q : Nat} (hq : p < (q + 1) * (q + 1)) (r : Shell p) :
    ∃ a b, a ≤ q ∧ b ≤ q ∧ (0 < a ∨ 0 < b) ∧
      ((ofNat a : Shell p) = r * ofNat b ∨ (ofNat a : Shell p) = -(r * ofNat b)) :=
  have hn : 0 < q + 1 := Nat.succ_pos q
  match collision (gap r (q + 1))
      (fun i _ => (ofNat (pairOf (q + 1) i).1 + -(r * ofNat (pairOf (q + 1) i).2) : Shell p).lt) hq with
  | ⟨i, j, hij, hj, e⟩ =>
    have hi : i < (q + 1) * (q + 1) := Nat.lt_trans hij hj
    have E : (ofNat (pairOf (q + 1) i).1 : Shell p) + -(r * ofNat (pairOf (q + 1) i).2)
        = ofNat (pairOf (q + 1) j).1 + -(r * ofNat (pairOf (q + 1) j).2) := Shell.ext e
    thue_step r (Nat.le_of_lt_succ (pairOf_fst_lt hn hi)) (Nat.le_of_lt_succ (pairOf_spec hn i).2)
      (Nat.le_of_lt_succ (pairOf_fst_lt hn hj)) (Nat.le_of_lt_succ (pairOf_spec hn j).2)
      (fun ⟨h1, h2⟩ => Nat.ne_of_lt hij (pairOf_inj hn h1 h2)) (sub_eq_sub E)

/-- A positive label of the window is no multiple of `p`. -/
theorem window_label_ne_zero {q a : Nat} (hq : q * q < p) (ha : 0 < a) (haq : a ≤ q) : (ofNat a : Shell p) ≠ 0 := fun h =>
  have hq1 : 1 ≤ q := Nat.le_trans ha haq
  have hqq : q ≤ q * q := Nat.le_trans (Nat.le_of_eq (Nat.mul_one q).symm) (Nat.mul_le_mul_left q hq1)
  have hap : a < p := Nat.lt_of_le_of_lt (Nat.le_trans haq hqq) hq
  have hv : a % p = 0 := val_injective h
  absurd ((FRC.Nat.mod_eq_of_lt hap).symm.trans hv) (Nat.ne_of_gt ha)

theorem neg_eq_zero {x : Shell p} (h : -x = 0) : x = 0 := by
  rw [← neg_neg x, h, neg_zero]

/-- 20:G17 — every nonzero residue is a signed quotient of two labels of the window: with `q² < p < (q + 1)²` and
`r ≠ 0` there are labels `0 < a, b ≤ q` with `a = r·b` or `a = −r·b`. -/
theorem thue_ne_zero (F : Frame p κ g) {q : Nat} (hq1 : q * q < p) (hq2 : p < (q + 1) * (q + 1)) {r : Shell p}
    (hr : r ≠ 0) :
    ∃ a b, 0 < a ∧ a ≤ q ∧ 0 < b ∧ b ≤ q ∧
      ((ofNat a : Shell p) = r * ofNat b ∨ (ofNat a : Shell p) = -(r * ofNat b)) :=
  match thue hq2 r with
  | ⟨a, b, ha, hb, hpos, e⟩ =>
    have zero : (ofNat 0 : Shell p) = 0 := rfl
    match Nat.eq_zero_or_pos a, Nat.eq_zero_or_pos b with
    | Or.inr ha0, Or.inr hb0 => ⟨a, b, ha0, ha, hb0, hb, e⟩
    | Or.inl ha0, Or.inl hb0 => match hpos with
      | Or.inl h => absurd ha0 (Nat.ne_of_gt h)
      | Or.inr h => absurd hb0 (Nat.ne_of_gt h)
    | Or.inl ha0, Or.inr hb0 => by
      subst ha0
      have hrb : r * ofNat b = 0 := match e with
        | Or.inl e' => (zero.symm.trans e').symm
        | Or.inr e' => neg_eq_zero (zero.symm.trans e').symm
      exact match F.mul_eq_zero hrb with
        | Or.inl h => absurd h hr
        | Or.inr h => absurd h (window_label_ne_zero hq1 hb0 hb)
    | Or.inr ha0, Or.inl hb0 => by
      subst hb0
      have ha' : (ofNat a : Shell p) = 0 := match e with
        | Or.inl e' => by rw [e', zero, mul_zero]
        | Or.inr e' => by rw [e', zero, mul_zero, neg_zero]
      exact absurd ha' (window_label_ne_zero hq1 ha0 ha)

/-! ## The two squares -/

/-- A positive number below `2m` that `m` divides is `m`. -/
theorem eq_of_mod_zero {m x : Nat} (hm : 0 < m) (h0 : 0 < x) (h2 : x < m + m) (h : x % m = 0) : x = m :=
  match FRC.Nat.mod_spec m hm x with
  | ⟨k, hk⟩ =>
    have hk' : x = m * k := by rw [h, Nat.add_zero] at hk; exact hk
    match k, hk' with
    | 0, e => absurd (e.trans (Nat.mul_zero m)) (Nat.ne_of_gt h0)
    | 1, e => e.trans (Nat.mul_one m)
    | k + 2, e =>
      have h3 : m + m ≤ m * (k + 1 + 1) := by
        rw [Nat.mul_succ, Nat.mul_succ]
        exact Nat.add_le_add_right (Nat.le_add_left m (m * k)) m
      absurd (Nat.lt_of_lt_of_le h2 (Nat.le_trans h3 (Nat.le_of_eq e.symm))) (Nat.lt_irrefl x)

theorem neg_one_ne_zero (F : Frame p κ g) : (-1 : Shell p) ≠ 0 := fun h => F.one_ne_zero (neg_eq_zero h)

theorem quarter_turn_ne_zero (F : Frame p κ g) : quarterTurn g κ ≠ 0 := fun h =>
  neg_one_ne_zero F (by rw [← F.quarter_turn_sq, h, mul_zero])

/-- 20:G19 — the two squares. With `q² < p < (q + 1)²` the cardinality is `a² + b²` for two labels `0 < a, b ≤ q` of
the window, and the quarter-turn is their signed quotient: `a = i·b` or `a = −i·b` on the shell. -/
theorem two_squares (F : Frame p κ g) {q : Nat} (hq1 : q * q < p) (hq2 : p < (q + 1) * (q + 1)) :
    ∃ a b, 0 < a ∧ a ≤ q ∧ 0 < b ∧ b ≤ q ∧ a * a + b * b = p ∧
      ((ofNat a : Shell p) = quarterTurn g κ * ofNat b ∨ (ofNat a : Shell p) = -(quarterTurn g κ * ofNat b)) :=
  match thue_ne_zero F hq1 hq2 (quarter_turn_ne_zero F) with
  | ⟨a, b, ha0, ha, hb0, hb, e⟩ =>
    have h1 : (quarterTurn g κ * ofNat b) * (quarterTurn g κ * ofNat b) = -((ofNat b : Shell p) * ofNat b) := by
      rw [mul_mul_mul_comm, F.quarter_turn_sq, neg_one_mul]
    have sq : (ofNat a : Shell p) * ofNat a = -(ofNat b * ofNat b) := match e with
      | Or.inl e' => by rw [e', h1]
      | Or.inr e' => by rw [e', neg_mul_neg, h1]
    have hz : (ofNat (a * a + b * b) : Shell p) = 0 := by
      rw [← ofNat_add, ← ofNat_mul, ← ofNat_mul, sq, neg_add]
    have hmod : (a * a + b * b) % p = 0 := val_injective hz
    have hpos : 0 < a * a + b * b := Nat.lt_of_lt_of_le (Nat.mul_pos ha0 ha0) (Nat.le_add_right _ _)
    have hlt : a * a + b * b < p + p :=
      Nat.lt_of_le_of_lt (Nat.add_le_add (Nat.mul_le_mul ha ha) (Nat.mul_le_mul hb hb)) (Nat.add_lt_add hq1 hq1)
    ⟨a, b, ha0, ha, hb0, hb, eq_of_mod_zero Pos.pos hpos hlt hmod, e⟩

/-! ## The two squares are unique -/

/-- A number whose square is below `p` is a label of the window. -/
theorem le_of_sq_lt {m q c : Nat} (hq2 : m < (q + 1) * (q + 1)) (hc : c * c < m) : c ≤ q :=
  match Nat.lt_or_ge c (q + 1) with
  | Or.inl h => Nat.le_of_lt_succ h
  | Or.inr h => absurd (Nat.lt_trans (Nat.lt_of_le_of_lt (Nat.mul_le_mul h h) hc) hq2) (Nat.lt_irrefl _)

/-- Two numbers below `p` with one residue are equal. -/
theorem eq_of_ofNat_eq {x y : Nat} (hx : x < p) (hy : y < p) (h : (ofNat x : Shell p) = ofNat y) : x = y := by
  have := val_injective h
  rw [val_ofNat, val_ofNat, FRC.Nat.mod_eq_of_lt hx, FRC.Nat.mod_eq_of_lt hy] at this
  exact this

/-- From `a² + b² = p` with `b` a positive label: `a = i·b` or `a = −i·b` on the shell. -/
theorem quotient_of_squares (F : Frame p κ g) {q a b : Nat} (hq1 : q * q < p) (hb0 : 0 < b) (hb : b ≤ q)
    (h : a * a + b * b = p) :
    (ofNat a : Shell p) = quarterTurn g κ * ofNat b ∨ (ofNat a : Shell p) = -(quarterTurn g κ * ofNat b) := by
  have hz : (ofNat a : Shell p) * ofNat a + ofNat b * ofNat b = 0 := by
    rw [ofNat_mul, ofNat_mul, ofNat_add, h]; exact ofNat_self
  have e1 : (ofNat a : Shell p) * ofNat a = -(ofNat b * ofNat b) := eq_neg_of_add_eq_zero hz
  have e2 : (quarterTurn g κ * ofNat b) * (quarterTurn g κ * ofNat b) = -((ofNat b : Shell p) * ofNat b) := by
    rw [mul_mul_mul_comm, F.quarter_turn_sq, neg_one_mul]
  have hx0 : quarterTurn g κ * ofNat b ≠ 0 := F.mul_ne_zero (quarter_turn_ne_zero F) (window_label_ne_zero hq1 hb0 hb)
  exact ((F.root_pair _ _ e2 hx0).1 (ofNat a)).mp e1

/-- The count behind the uniqueness, one side: from `a·d = b·c` and `a·c + b·d = a² + b²` follows `a = c` and `b = d`. -/
theorem squares_same {a b c d m : Nat} (ha0 : 0 < a) (hm : 0 < m) (hab : a * a + b * b = m)
    (had : a * d = b * c) (hac : a * c + b * d = m) : c = a ∧ d = b := by
  have h1 : a * m = c * m :=
    calc a * m = a * (a * c + b * d) := by rw [hac]
      _ = a * (a * c) + b * (a * d) := by rw [Nat.left_distrib, Nat.mul_left_comm a b d]
      _ = a * (a * c) + b * (b * c) := by rw [had]
      _ = c * (a * a) + c * (b * b) := by
          rw [← FRC.Nat.mul_assoc a a c, Nat.mul_comm (a * a) c, ← FRC.Nat.mul_assoc b b c, Nat.mul_comm (b * b) c]
      _ = c * m := by rw [← Nat.left_distrib, hab]
  have hca : c = a := (Nat.eq_of_mul_eq_mul_right hm h1).symm
  subst hca
  exact ⟨rfl, Nat.eq_of_mul_eq_mul_left ha0 (had.trans (Nat.mul_comm b c))⟩

/-- 20:G19 — the two squares are unique up to their order: `p = a² + b² = c² + d²` with positive integers gives
`(c, d) = (a, b)` or `(c, d) = (b, a)`. -/
theorem two_squares_unique (F : Frame p κ g) {q : Nat} (hq1 : q * q < p) (hq2 : p < (q + 1) * (q + 1))
    {a b c d : Nat} (ha0 : 0 < a) (hb0 : 0 < b) (hc0 : 0 < c) (hd0 : 0 < d)
    (hab : a * a + b * b = p) (hcd : c * c + d * d = p) : (c = a ∧ d = b) ∨ (c = b ∧ d = a) := by
  have hp : 0 < p := Pos.pos
  have la : a ≤ q := le_of_sq_lt hq2 (Nat.lt_of_lt_of_le (Nat.lt_add_of_pos_right (Nat.mul_pos hb0 hb0)) (Nat.le_of_eq hab))
  have lb : b ≤ q := le_of_sq_lt hq2 (Nat.lt_of_lt_of_le (Nat.lt_add_of_pos_left (Nat.mul_pos ha0 ha0)) (Nat.le_of_eq hab))
  have lc : c ≤ q := le_of_sq_lt hq2 (Nat.lt_of_lt_of_le (Nat.lt_add_of_pos_right (Nat.mul_pos hd0 hd0)) (Nat.le_of_eq hcd))
  have ld : d ≤ q := le_of_sq_lt hq2 (Nat.lt_of_lt_of_le (Nat.lt_add_of_pos_left (Nat.mul_pos hc0 hc0)) (Nat.le_of_eq hcd))
  have lt2 : ∀ {x y : Nat}, x ≤ q → y ≤ q → x * y < p := fun hx hy => Nat.lt_of_le_of_lt (Nat.mul_le_mul hx hy) hq1
  have lt4 : ∀ {x y z w : Nat}, x ≤ q → y ≤ q → z ≤ q → w ≤ q → x * y + z * w < p + p := fun hx hy hz hw =>
    Nat.add_lt_add (lt2 hx hy) (lt2 hz hw)
  -- the residues of the four products
  have same : ∀ {a b c d : Nat} (u : Shell p), u * u = -1 →
      (ofNat a : Shell p) = u * ofNat b → (ofNat c : Shell p) = u * ofNat d →
      (ofNat (a * d) : Shell p) = ofNat (b * c) ∧ (ofNat (a * c + b * d) : Shell p) = 0 := fun {a b c d} u hu ea ec => by
    refine ⟨?_, ?_⟩
    · rw [← ofNat_mul, ← ofNat_mul, ea, ec, mul_assoc, mul_left_comm (ofNat b)]
    · rw [← ofNat_add, ← ofNat_mul, ← ofNat_mul, ea, ec, mul_mul_mul_comm, hu, neg_one_mul, neg_add]
  have opp : ∀ {a b c d : Nat} (u v : Shell p), u * v = 1 → u + v = 0 →
      (ofNat a : Shell p) = u * ofNat b → (ofNat c : Shell p) = v * ofNat d →
      (ofNat (a * c) : Shell p) = ofNat (b * d) ∧ (ofNat (a * d + b * c) : Shell p) = 0 := fun {a b c d} u v huv hs ea ec => by
    refine ⟨?_, ?_⟩
    · rw [← ofNat_mul, ← ofNat_mul, ea, ec, mul_mul_mul_comm, huv, one_mul]
    · rw [← ofNat_add, ← ofNat_mul, ← ofNat_mul, ea, ec, mul_assoc, mul_left_comm (ofNat b), ← right_distrib, hs, zero_mul]
  have u2 := F.quarter_turn_sq
  have nu2 : (-(quarterTurn g κ)) * (-(quarterTurn g κ)) = -1 := by rw [neg_mul_neg]; exact u2
  have negl : ∀ (x : Shell p), -(quarterTurn g κ * x) = -(quarterTurn g κ) * x := fun x => neg_mul _ _
  have finish_same : (ofNat (a * d) : Shell p) = ofNat (b * c) ∧ (ofNat (a * c + b * d) : Shell p) = 0 →
      (c = a ∧ d = b) ∨ (c = b ∧ d = a) := fun ⟨h1, h2⟩ =>
    have had : a * d = b * c := eq_of_ofNat_eq (lt2 la ld) (lt2 lb lc) h1
    have hac : a * c + b * d = p := eq_of_mod_zero hp
      (Nat.lt_of_lt_of_le (Nat.mul_pos ha0 hc0) (Nat.le_add_right _ _)) (lt4 la lc lb ld) (val_injective h2)
    Or.inl (squares_same ha0 hp hab had hac)
  have finish_opp : (ofNat (a * c) : Shell p) = ofNat (b * d) ∧ (ofNat (a * d + b * c) : Shell p) = 0 →
      (c = a ∧ d = b) ∨ (c = b ∧ d = a) := fun ⟨h1, h2⟩ =>
    have hac : a * c = b * d := eq_of_ofNat_eq (lt2 la lc) (lt2 lb ld) h1
    have had : a * d + b * c = p := eq_of_mod_zero hp
      (Nat.lt_of_lt_of_le (Nat.mul_pos ha0 hd0) (Nat.le_add_right _ _)) (lt4 la ld lb lc) (val_injective h2)
    match squares_same ha0 hp hab hac had with
    | ⟨e1, e2⟩ => Or.inr ⟨e2, e1⟩
  match quotient_of_squares F hq1 hb0 lb hab, quotient_of_squares F hq1 hd0 ld hcd with
  | Or.inl ea, Or.inl ec => exact finish_same (same _ u2 ea ec)
  | Or.inr ea, Or.inr ec => exact finish_same (same _ nu2 ((negl _) ▸ ea) ((negl _) ▸ ec))
  | Or.inl ea, Or.inr ec =>
    exact finish_opp (opp _ _ (by rw [← mul_neg, u2, neg_neg]) (add_neg _) ea ((negl _) ▸ ec))
  | Or.inr ea, Or.inl ec =>
    exact finish_opp (opp _ _ (by rw [← neg_mul, u2, neg_neg]) (neg_add _) ((negl _) ▸ ea) ec)

end thue20261126

end Horizon
end FRC
