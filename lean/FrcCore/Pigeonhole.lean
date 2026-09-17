import FrcCore.Nat

/-!
# FrcCore.Pigeonhole — a list of `n` distinct numbers in `[1, n]` is all of `[1, n]`

The counting fact behind "the drive generates": its `p − 1` powers are distinct nonzero residues, and there
are only `p − 1` of those. Lists of naturals with their own membership, no-duplicates and erase (Lean's
`List` lemmas carry `propext`); everything by induction. No axioms.
-/

namespace FRC
namespace Pigeonhole

/-- Membership, by recursion (decidable). -/
def mem (v : Nat) : List Nat → Prop
  | [] => False
  | a :: l => v = a ∨ mem v l

def decMem (v : Nat) : (l : List Nat) → Decidable (mem v l)
  | [] => isFalse id
  | a :: l => match Nat.decEq v a, decMem v l with
    | isTrue h, _ => isTrue (Or.inl h)
    | isFalse _, isTrue h' => isTrue (Or.inr h')
    | isFalse h, isFalse h' => isFalse (fun e => match e with | Or.inl e => h e | Or.inr e => h' e)

instance (v : Nat) (l : List Nat) : Decidable (mem v l) := decMem v l

/-- No duplicates, by recursion. -/
def NoDup : List Nat → Prop
  | [] => True
  | a :: l => ¬ mem a l ∧ NoDup l

/-- Remove the first occurrence of `v`. -/
def erase (v : Nat) : List Nat → List Nat
  | [] => []
  | a :: l => if a = v then l else a :: erase v l

theorem length_erase_of_mem {v : Nat} : ∀ {l : List Nat}, mem v l → (erase v l).length + 1 = l.length
  | [], h => absurd h id
  | a :: l, h => by
    show (if a = v then l else a :: erase v l).length + 1 = l.length + 1
    exact match Nat.decEq a v with
      | isTrue e => by rw [ite_eq_left e]
      | isFalse e => by
          rw [ite_eq_right e]
          show (erase v l).length + 1 + 1 = l.length + 1
          have hm : mem v l := match h with
            | Or.inl h' => absurd h'.symm e
            | Or.inr h' => h'
          rw [length_erase_of_mem hm]

theorem mem_of_mem_erase {w v : Nat} : ∀ {l : List Nat}, mem w (erase v l) → mem w l
  | [], h => absurd h id
  | a :: l, h => by
    show w = a ∨ mem w l
    exact match Nat.decEq a v with
      | isTrue e => by
          rw [show erase v (a :: l) = l from ite_eq_left e] at h
          exact Or.inr h
      | isFalse e => by
          rw [show erase v (a :: l) = a :: erase v l from ite_eq_right e] at h
          exact match h with
            | Or.inl h' => Or.inl h'
            | Or.inr h' => Or.inr (mem_of_mem_erase h')

theorem mem_erase_of_ne {w v : Nat} (hwv : w ≠ v) : ∀ {l : List Nat}, mem w l → mem w (erase v l)
  | [], h => absurd h id
  | a :: l, h => by
    exact match Nat.decEq a v with
      | isTrue e => by
          rw [show erase v (a :: l) = l from ite_eq_left e]
          exact match h with
            | Or.inl h' => absurd (h'.trans e) hwv
            | Or.inr h' => h'
      | isFalse e => by
          rw [show erase v (a :: l) = a :: erase v l from ite_eq_right e]
          exact match h with
            | Or.inl h' => Or.inl h'
            | Or.inr h' => Or.inr (mem_erase_of_ne hwv h')

theorem nodup_erase (v : Nat) : ∀ {l : List Nat}, NoDup l → NoDup (erase v l)
  | [], _ => trivial
  | a :: l, ⟨ha, hl⟩ => by
    exact match Nat.decEq a v with
      | isTrue e => by rw [show erase v (a :: l) = l from ite_eq_left e]; exact hl
      | isFalse e => by
          rw [show erase v (a :: l) = a :: erase v l from ite_eq_right e]
          exact ⟨fun h => ha (mem_of_mem_erase h), nodup_erase v hl⟩

theorem not_mem_erase_self (v : Nat) : ∀ {l : List Nat}, NoDup l → ¬ mem v (erase v l)
  | [], _, h => h
  | a :: l, ⟨ha, hl⟩, h => by
    exact match Nat.decEq a v with
      | isTrue e => by
          rw [show erase v (a :: l) = l from ite_eq_left e] at h
          exact ha (e ▸ h)
      | isFalse e => by
          rw [show erase v (a :: l) = a :: erase v l from ite_eq_right e] at h
          exact match h with
            | Or.inl h' => e h'.symm
            | Or.inr h' => not_mem_erase_self v hl h'

/-- The bound: a list of distinct numbers in `[1, n]` has at most `n` entries. -/
theorem length_le_of_nodup : ∀ (n : Nat) (l : List Nat), NoDup l → (∀ e, mem e l → 1 ≤ e ∧ e ≤ n) →
    l.length ≤ n
  | 0, [], _, _ => Nat.le_refl 0
  | 0, a :: l, _, hb => absurd (hb a (Or.inl rfl)) (fun ⟨h1, h0⟩ => Nat.lt_irrefl 0 (Nat.lt_of_lt_of_le h1 h0))
  | n + 1, l, hnd, hb =>
    match (inferInstance : Decidable (mem (n + 1) l)) with
    | isTrue hm =>
      have h1 : (erase (n + 1) l).length ≤ n :=
        length_le_of_nodup n (erase (n + 1) l) (nodup_erase _ hnd) (fun e he =>
          have hb' := hb e (mem_of_mem_erase he)
          ⟨hb'.1, match Nat.lt_or_ge e (n + 1) with
            | Or.inl hlt => Nat.le_of_lt_succ hlt
            | Or.inr hge =>
              have : e = n + 1 := Nat.le_antisymm hb'.2 hge
              absurd (this ▸ he) (not_mem_erase_self (n + 1) hnd)⟩)
      by rw [← length_erase_of_mem hm]; exact Nat.succ_le_succ h1
    | isFalse hm =>
      Nat.le_succ_of_le (length_le_of_nodup n l hnd (fun e he =>
        have hb' := hb e he
        ⟨hb'.1, match Nat.lt_or_ge e (n + 1) with
          | Or.inl hlt => Nat.le_of_lt_succ hlt
          | Or.inr hge => absurd he ((Nat.le_antisymm hb'.2 hge) ▸ hm)⟩))

/-- The pigeonhole: `n` distinct numbers in `[1, n]` are all of them. -/
theorem mem_of_nodup_of_length (n : Nat) (l : List Nat) (hnd : NoDup l) (hb : ∀ e, mem e l → 1 ≤ e ∧ e ≤ n)
    (hlen : l.length = n) (v : Nat) (hv1 : 1 ≤ v) (hvn : v ≤ n) : mem v l :=
  match decMem v l with
  | isTrue h => h
  | isFalse h =>
    have hnd' : NoDup (v :: l) := ⟨h, hnd⟩
    have hb' : ∀ e, mem e (v :: l) → 1 ≤ e ∧ e ≤ n := fun e he => match he with
      | Or.inl e' => e' ▸ ⟨hv1, hvn⟩
      | Or.inr e' => hb e e'
    have := length_le_of_nodup n (v :: l) hnd' hb'
    absurd (hlen ▸ this : n + 1 ≤ n) (Nat.not_succ_le_self n)

/-- The same with the range `[0, n)`: a list of distinct numbers below `n` has at most `n` entries. -/
theorem length_le_of_nodup_lt : ∀ (n : Nat) (l : List Nat), NoDup l → (∀ e, mem e l → e < n) → l.length ≤ n
  | 0, [], _, _ => Nat.le_refl 0
  | 0, a :: l, _, hb => absurd (hb a (Or.inl rfl)) (Nat.not_lt_zero a)
  | n + 1, l, hnd, hb =>
    match decMem n l with
    | isTrue hm =>
      have h1 : (erase n l).length ≤ n :=
        length_le_of_nodup_lt n (erase n l) (nodup_erase _ hnd) (fun e he =>
          match Nat.lt_or_ge e n with
          | Or.inl hlt => hlt
          | Or.inr hge =>
            have : e = n := Nat.le_antisymm (Nat.le_of_lt_succ (hb e (mem_of_mem_erase he))) hge
            absurd (this ▸ he) (not_mem_erase_self n hnd))
      by rw [← length_erase_of_mem hm]; exact Nat.succ_le_succ h1
    | isFalse hm =>
      Nat.le_succ_of_le (length_le_of_nodup_lt n l hnd (fun e he =>
        match Nat.lt_or_ge e n with
        | Or.inl hlt => hlt
        | Or.inr hge => absurd he ((Nat.le_antisymm (Nat.le_of_lt_succ (hb e he)) hge) ▸ hm)))

/-- `n` distinct numbers below `n` are all of them. -/
theorem mem_of_nodup_of_length_lt (n : Nat) (l : List Nat) (hnd : NoDup l) (hb : ∀ e, mem e l → e < n)
    (hlen : l.length = n) (v : Nat) (hv : v < n) : mem v l :=
  match decMem v l with
  | isTrue h => h
  | isFalse h =>
    have hb' : ∀ e, mem e (v :: l) → e < n := fun e he => match he with
      | Or.inl e' => e' ▸ hv
      | Or.inr e' => hb e e'
    have := length_le_of_nodup_lt n (v :: l) ⟨h, hnd⟩ hb'
    absurd (hlen ▸ this : n + 1 ≤ n) (Nat.not_succ_le_self n)

end Pigeonhole
end FRC
