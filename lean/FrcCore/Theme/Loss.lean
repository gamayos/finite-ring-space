import FrcCore.Pigeonhole

/-!
# The loss file of 8-dirac — a self-map of a finite set is bijective exactly when its image count is the whole count

The seventh file of the dirac theme (5 November 2026, the core-proof programme): 8:E2 on the register `[0, n)` with the
base theme's lists (`Pigeonhole.mem`, `NoDup`, `erase`). The image count of `f : [0, n) → [0, n)` is the number of values
below `n` that `f` hits; it is `n` exactly when `f` is injective and surjective — the loss factor (the count over the image
count) is one. The surjective direction counts the hit values; injectivity follows from surjectivity by the pigeonhole in
the form "a list holding every number below `m` has at least `m` entries": with a collision `f i = f j`, `i ≠ j`, the
values of `f` on the `n − 1` indices other than `j` still cover `[0, n)`. No axioms.
-/

namespace FRC.Dirac.Loss

open FRC.Pigeonhole

/-- The register `[0, n)` as a list, `n − 1, …, 0`. -/
def ran : Nat → List Nat
  | 0 => []
  | n + 1 => n :: ran n

theorem mem_ran : ∀ n v, mem v (ran n) ↔ v < n
  | 0, v => ⟨fun h => absurd h id, fun h => absurd h (Nat.not_lt_zero v)⟩
  | n + 1, v => by
    show v = n ∨ mem v (ran n) ↔ v < n + 1
    constructor
    · intro h
      cases h with
      | inl e => exact e ▸ Nat.lt_succ_self n
      | inr h' => exact Nat.lt_succ_of_lt ((mem_ran n v).1 h')
    · intro h
      cases Nat.lt_or_ge v n with
      | inl hlt => exact Or.inr ((mem_ran n v).2 hlt)
      | inr hge => exact Or.inl (Nat.le_antisymm (Nat.le_of_lt_succ h) hge)

theorem length_ran : ∀ n, (ran n).length = n
  | 0 => rfl
  | n + 1 => by show (ran n).length + 1 = n + 1; rw [length_ran n]

theorem mem_map (f : Nat → Nat) (v : Nat) : ∀ l : List Nat, mem v (List.map f l) ↔ ∃ i, mem i l ∧ f i = v
  | [] => ⟨fun h => absurd h id, fun ⟨_, h, _⟩ => absurd h id⟩
  | a :: l => by
    show v = f a ∨ mem v (List.map f l) ↔ ∃ i, (i = a ∨ mem i l) ∧ f i = v
    constructor
    · intro h
      cases h with
      | inl e => exact ⟨a, Or.inl rfl, e.symm⟩
      | inr h' =>
        obtain ⟨i, hi, e⟩ := (mem_map f v l).1 h'
        exact ⟨i, Or.inr hi, e⟩
    · intro ⟨i, hi, e⟩
      cases hi with
      | inl e' => exact Or.inl (by rw [← e, e'])
      | inr hi' => exact Or.inr ((mem_map f v l).2 ⟨i, hi', e⟩)

theorem length_map (f : Nat → Nat) : ∀ l : List Nat, (List.map f l).length = l.length
  | [] => rfl
  | _ :: l => by show (List.map f l).length + 1 = l.length + 1; rw [length_map f l]

/-- A list holding every number below `m` has at least `m` entries (erase `m − 1` and recurse). -/
theorem length_ge_of_contains : ∀ (m : Nat) (l : List Nat), (∀ v, v < m → mem v l) → m ≤ l.length
  | 0, _, _ => Nat.zero_le _
  | m + 1, l, h => by
    have hm : mem m l := h m (Nat.lt_succ_self m)
    have h' : ∀ v, v < m → mem v (erase m l) := fun v hv =>
      mem_erase_of_ne (Nat.ne_of_lt hv) (h v (Nat.lt_succ_of_lt hv))
    have := length_ge_of_contains m (erase m l) h'
    rw [← length_erase_of_mem hm]
    exact Nat.succ_le_succ this

/-- The number of values below `n` satisfying `A`. -/
def cnt (A : Nat → Bool) : Nat → Nat
  | 0 => 0
  | n + 1 => cnt A n + if A n then 1 else 0

theorem cnt_full (A : Nat → Bool) : ∀ n, (∀ v, v < n → A v = true) → cnt A n = n
  | 0, _ => rfl
  | n + 1, h => by
    show cnt A n + (if A n then 1 else 0) = n + 1
    rw [cnt_full A n fun v hv => h v (Nat.lt_succ_of_lt hv), h n (Nat.lt_succ_self n)]
    rfl

theorem cnt_le (A : Nat → Bool) : ∀ n, cnt A n ≤ n
  | 0 => Nat.le_refl 0
  | n + 1 => by
    show cnt A n + (if A n then 1 else 0) ≤ n + 1
    cases A n with
    | true => exact Nat.succ_le_succ (cnt_le A n)
    | false => exact Nat.le_succ_of_le (cnt_le A n)

/-- A value below `n` missed by `A` keeps the count below `n`. -/
theorem cnt_lt_of_false (A : Nat → Bool) : ∀ n v, v < n → A v = false → cnt A n < n
  | 0, _, hv, _ => absurd hv (Nat.not_lt_zero _)
  | n + 1, v, hv, hA => by
    show cnt A n + (if A n then 1 else 0) < n + 1
    cases Nat.lt_or_ge v n with
    | inl hlt =>
      have := cnt_lt_of_false A n v hlt hA
      cases A n with
      | true => exact Nat.succ_lt_succ this
      | false => exact Nat.lt_succ_of_lt this
    | inr hge =>
      have e : v = n := Nat.le_antisymm (Nat.le_of_lt_succ hv) hge
      rw [← e, hA]
      exact Nat.lt_succ_of_le (cnt_le A v)

/-- `v` is a value of `f` on `[0, n)`. -/
def hit (f : Nat → Nat) (n v : Nat) : Bool := decide (mem v (List.map f (ran n)))

/-- The image count of `f` on `[0, n)`: the number of values below `n` that `f` takes. -/
def imageCount (f : Nat → Nat) (n : Nat) : Nat := cnt (hit f n) n

theorem hit_iff (f : Nat → Nat) (n v : Nat) : hit f n v = true ↔ ∃ i, i < n ∧ f i = v := by
  constructor
  · intro h
    obtain ⟨i, hi, e⟩ := (mem_map f v _).1 (of_decide_eq_true h)
    exact ⟨i, (mem_ran n i).1 hi, e⟩
  · intro ⟨i, hi, e⟩
    exact decide_eq_true ((mem_map f v _).2 ⟨i, (mem_ran n i).2 hi, e⟩)

/-- 8:E2 — a self-map of `[0, n)` is bijective exactly when its image count is `n` (the loss factor, the count over
the image count, is one): surjectivity is the count of the hit values, and injectivity follows from surjectivity by
the pigeonhole — with a collision `f i = f j`, `i ≠ j`, the `n − 1` values of `f` off `j` would still cover `[0, n)`. -/
theorem bijective_iff_image_count (f : Nat → Nat) (n : Nat) :
    imageCount f n = n ↔
      ((∀ i j, i < n → j < n → f i = f j → i = j) ∧ (∀ v, v < n → ∃ i, i < n ∧ f i = v)) := by
  constructor
  · intro hc
    have hsurj : ∀ v, v < n → ∃ i, i < n ∧ f i = v := by
      intro v hv
      apply (hit_iff f n v).1
      cases e : hit f n v with
      | true => rfl
      | false => exact absurd hc (Nat.ne_of_lt (cnt_lt_of_false (hit f n) n v hv e))
    refine ⟨?_, hsurj⟩
    intro i j hi hj e
    cases Nat.decEq i j with
    | isTrue h => exact h
    | isFalse h =>
      -- the values of `f` on the indices other than `j` still cover `[0, n)`, on `n − 1` indices
      have hj' : mem j (ran n) := (mem_ran n j).2 hj
      have hcover : ∀ v, v < n → mem v (List.map f (erase j (ran n))) := by
        intro v hv
        obtain ⟨k, hk, ek⟩ := hsurj v hv
        apply (mem_map f v _).2
        cases Nat.decEq k j with
        | isFalse hkj => exact ⟨k, mem_erase_of_ne hkj ((mem_ran n k).2 hk), ek⟩
        | isTrue hkj => exact ⟨i, mem_erase_of_ne h ((mem_ran n i).2 hi), by rw [e, ← hkj, ek]⟩
      have hlen := length_ge_of_contains n _ hcover
      rw [length_map] at hlen
      have hlen' : n + 1 ≤ (erase j (ran n)).length + 1 := Nat.succ_le_succ hlen
      rw [length_erase_of_mem hj', length_ran] at hlen'
      exact absurd hlen' (Nat.not_succ_le_self n)
  · intro ⟨_, hsurj⟩
    exact cnt_full _ n fun v hv => (hit_iff f n v).2 (hsurj v hv)

end FRC.Dirac.Loss
