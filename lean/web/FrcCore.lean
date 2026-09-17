/-! FrcCore — the FRC substrate from first principles, one file for the live instance (no Mathlib,
no axioms). Generated from FrcCore/*.lean in the order Nat, Pigeonhole, Shell, Frame, Orbit, Sum,
Algebra, Geometry, Instances by make_core_web.py; the modules' own headers follow. Check any declaration with `#print axioms`. -/

/-! inlined: FrcCore/Nat.lean -/
/-!
# FrcCore.Nat — the arithmetic the shells stand on, from first principles

No Mathlib, no `simp`, no `omega`: every theorem here is checked by `#print axioms` to depend on no
axiom at all. Lean's own core library proves most of these with `propext` for convenience (see
`reports/lean-axioms-probe-20260917/core_probe.log`); they are re-derived here by induction from the
axiom-free primitives (`Nat.rec`, `Nat.add_comm`, `Nat.mul_comm`, `Nat.left_distrib`, `Nat.mod_lt`,
`Nat.le.dest`, `if_pos`, `if_neg`, `Decidable.em`).

The division algorithm is obtained from the definition of `Nat.mod` in `Init.Prelude` (the wrapper
around `Nat.modCore`, itself a fuel recursion): `mod_eq_of_lt`, `mod_eq_sub_mod`, `mod_spec`
(`x = p·q + x % p`) and `mod_unique` (the remainder is determined by any such decomposition). Everything
about residues mod `p` follows from those four.
-/

namespace FRC.Nat

/-! ## Cancellation and subtraction -/

theorem add_left_cancel {a b c : Nat} (h : a + b = a + c) : b = c := by
  induction a with
  | zero => rw [Nat.zero_add, Nat.zero_add] at h; exact h
  | succ a ih =>
    apply ih
    rw [Nat.succ_add, Nat.succ_add] at h
    exact Nat.succ.inj h

theorem add_right_cancel {a b c : Nat} (h : a + c = b + c) : a = b :=
  add_left_cancel (a := c) (by rw [Nat.add_comm c a, Nat.add_comm c b]; exact h)

theorem add_sub_cancel (n m : Nat) : n + m - m = n := by
  induction m with
  | zero => rfl
  | succ m ih => rw [Nat.add_succ, Nat.succ_sub_succ]; exact ih

theorem add_sub_cancel_left (n m : Nat) : n + m - n = m := by
  rw [Nat.add_comm]; exact add_sub_cancel m n

theorem sub_add_cancel {n m : Nat} (h : m ≤ n) : n - m + m = n := by
  match Nat.le.dest h with
  | ⟨k, hk⟩ => rw [← hk, add_sub_cancel_left, Nat.add_comm]

theorem sub_add_self_eq_zero (m : Nat) : ∀ k, m - (m + k) = 0
  | 0 => Nat.sub_self m
  | k + 1 => by show Nat.pred (m - (m + k)) = 0; rw [sub_add_self_eq_zero m k]; rfl

theorem sub_eq_zero_of_le {m n : Nat} (h : m ≤ n) : m - n = 0 :=
  match Nat.le.dest h with
  | ⟨k, hk⟩ => by rw [← hk]; exact sub_add_self_eq_zero m k

theorem add_sub_of_le {n m : Nat} (h : m ≤ n) : m + (n - m) = n := by
  rw [Nat.add_comm]; exact sub_add_cancel h

theorem sub_lt_of_lt_add {x y z : Nat} (h : x < y + z) (hy : y ≤ x) : x - y < z := by
  refine Nat.lt_of_add_lt_add_right (n := y) ?_
  rw [sub_add_cancel hy, Nat.add_comm z y]
  exact h

theorem le_of_add_le_add_left {a b c : Nat} (h : a + b ≤ a + c) : b ≤ c := by
  induction a with
  | zero => rw [Nat.zero_add, Nat.zero_add] at h; exact h
  | succ a ih => apply ih; rw [Nat.succ_add, Nat.succ_add] at h; exact Nat.le_of_succ_le_succ h

theorem le_of_add_le_add_right {a b c : Nat} (h : b + a ≤ c + a) : b ≤ c :=
  le_of_add_le_add_left (a := a) (by rw [Nat.add_comm a b, Nat.add_comm a c]; exact h)

theorem sub_le_of_le_add {a b c : Nat} (h : a ≤ c + b) : a - b ≤ c := by
  have := Nat.sub_le_sub_right h b
  rw [add_sub_cancel] at this; exact this

theorem le_add_of_sub_le {a b c : Nat} (hb : b ≤ a) (h : a - b ≤ c) : a ≤ c + b := by
  have := Nat.add_le_add_right h b
  rw [sub_add_cancel hb] at this; exact this

theorem le_sub_of_add_le {a b c : Nat} (h : c + b ≤ a) : c ≤ a - b := by
  have := Nat.sub_le_sub_right h b
  rw [add_sub_cancel] at this; exact this

theorem succ_ne_zero (n : Nat) : n + 1 ≠ 0 := fun h => Nat.noConfusion h

theorem pos_of_lt {a b : Nat} (h : a < b) : 0 < b :=
  Nat.lt_of_le_of_lt (Nat.zero_le a) h

/-! ## Multiplication -/

theorem mul_assoc (a b c : Nat) : a * b * c = a * (b * c) := by
  induction c with
  | zero => rfl
  | succ c ih => rw [Nat.mul_succ, Nat.mul_succ, ih, Nat.left_distrib]

theorem add_mul (a b c : Nat) : (a + b) * c = a * c + b * c := by
  rw [Nat.mul_comm, Nat.left_distrib, Nat.mul_comm c a, Nat.mul_comm c b]

theorem add_add_add_comm (a b c d : Nat) : a + b + (c + d) = a + c + (b + d) := by
  rw [Nat.add_assoc, Nat.add_assoc, Nat.add_left_comm b]

theorem mul_left_comm (a b c : Nat) : a * (b * c) = b * (a * c) := by
  rw [← mul_assoc, Nat.mul_comm a b, mul_assoc]

theorem mul_lt_mul_of_lt_of_pos {a b c : Nat} (h : a < b) (hc : 0 < c) : a * c < b * c := by
  rw [Nat.mul_comm a c, Nat.mul_comm b c]
  exact Nat.mul_lt_mul_of_pos_left h hc

/-! ## The division algorithm, from the definition of `Nat.mod` -/

section mod

/-- The fuel of `Nat.modCore.go` does not matter once it exceeds the dividend. -/
theorem modCore_go_fuel {y : Nat} (hy : 0 < y) : ∀ (f1 f2 x : Nat) (h1 : x < f1) (h2 : x < f2),
    Nat.modCore.go y hy f1 x h1 = Nat.modCore.go y hy f2 x h2 := by
  intro f1
  induction f1 with
  | zero => intro f2 x h1; exact absurd h1 (Nat.not_lt_zero x)
  | succ f1 ih =>
    intro f2 x h1 h2
    cases f2 with
    | zero => exact absurd h2 (Nat.not_lt_zero x)
    | succ f2 =>
      show (if h : y ≤ x then Nat.modCore.go y hy f1 (x - y) _ else x)
          = (if h : y ≤ x then Nat.modCore.go y hy f2 (x - y) _ else x)
      exact match Nat.decLe y x with
        | .isTrue h => by rw [dif_pos h, dif_pos h]; exact ih f2 (x - y) _ _
        | .isFalse h => by rw [dif_neg h, dif_neg h]

theorem modCore_eq' (x y : Nat) (hy : 0 < y) :
    Nat.modCore x y = if y ≤ x then Nat.modCore (x - y) y else x := by
  unfold Nat.modCore
  rw [dif_pos hy]
  show (if h : y ≤ x then Nat.modCore.go y hy x (x - y) _ else x) = _
  exact match Nat.decLe y x with
    | .isTrue h => by
        rw [dif_pos h, if_pos h, dif_pos hy]
        exact modCore_go_fuel hy x (x - y + 1) (x - y) _ _
    | .isFalse h => by rw [dif_neg h, if_neg h]

theorem modCore_eq_mod' (n m : Nat) (hm : 0 < m) : Nat.modCore n m = n % m := by
  cases n with
  | zero =>
    show Nat.modCore 0 m = 0
    rw [modCore_eq' 0 m hm, if_neg (Nat.not_le_of_lt hm)]
  | succ n =>
    show Nat.modCore (n + 1) m = ite (m ≤ n + 1) (Nat.modCore (n + 1) m) (n + 1)
    exact match Nat.decLe m (n + 1) with
      | .isTrue h => by rw [if_pos h]
      | .isFalse h => by rw [if_neg h, modCore_eq' _ _ hm, if_neg h]

theorem mod_eq_of_lt {x y : Nat} (h : x < y) : x % y = x := by
  cases x with
  | zero => rfl
  | succ n =>
    show ite (y ≤ n + 1) (Nat.modCore (n + 1) y) (n + 1) = n + 1
    rw [if_neg (Nat.not_le_of_lt h)]

theorem mod_eq_sub_mod {x y : Nat} (hy : 0 < y) (h : y ≤ x) : x % y = (x - y) % y := by
  rw [← modCore_eq_mod' x y hy, modCore_eq' x y hy, if_pos h, modCore_eq_mod' _ _ hy]

/-- The division algorithm: `x = p·q + x % p` for some `q`. -/
theorem mod_spec (p : Nat) (hp : 0 < p) : ∀ x : Nat, ∃ q, x = p * q + x % p := by
  intro x
  induction x using Nat.strongRecOn with
  | _ x ih =>
    exact match Nat.decLe p x with
      | .isTrue h =>
          match ih (x - p) (Nat.sub_lt (Nat.lt_of_lt_of_le hp h) hp) with
          | ⟨q, hq⟩ => ⟨q + 1, by
              rw [mod_eq_sub_mod hp h, Nat.mul_succ, Nat.add_assoc, Nat.add_comm p, ← Nat.add_assoc,
                ← hq, sub_add_cancel h]⟩
      | .isFalse h => ⟨0, by rw [mod_eq_of_lt (Nat.lt_of_not_le h), Nat.mul_zero, Nat.zero_add]⟩

/-- Uniqueness of the decomposition: the quotients agree. -/
theorem quot_unique {p q q' r r' : Nat} (hr : r < p) (hr' : r' < p) (h : p * q + r = p * q' + r') :
    q = q' := by
  have key : ∀ {q q' r r' : Nat}, r < p → r' < p → p * q + r = p * q' + r' → ¬ q < q' := by
    intro q q' r r' hr hr' h hlt
    have h1 : p * (q + 1) ≤ p * q' := Nat.mul_le_mul_left p hlt
    have h2 : p * q + r < p * q + p := Nat.add_lt_add_left hr _
    rw [Nat.mul_succ] at h1
    have h3 : p * q + r < p * q' + r' := Nat.lt_of_lt_of_le h2 (Nat.le_trans h1 (Nat.le_add_right _ _))
    rw [h] at h3
    exact Nat.lt_irrefl _ h3
  exact match Nat.lt_or_ge q q' with
    | .inl hlt => absurd hlt (key hr hr' h)
    | .inr hge => match Nat.lt_or_ge q' q with
      | .inl hlt => absurd hlt (key hr' hr h.symm)
      | .inr hge' => Nat.le_antisymm hge' hge

/-- The remainder is determined: if `x = p·q + r` with `r < p`, then `r = x % p`. -/
theorem mod_unique {p x q r : Nat} (hr : r < p) (h : x = p * q + r) : x % p = r := by
  have hp : 0 < p := pos_of_lt hr
  match mod_spec p hp x with
  | ⟨q', hq'⟩ =>
    have hqq : q' = q := quot_unique (Nat.mod_lt x hp) hr (by rw [← hq', ← h])
    rw [hqq] at hq'
    rw [h] at hq'
    rw [h]
    exact (add_left_cancel hq').symm

theorem mod_mod (x p : Nat) (hp : 0 < p) : x % p % p = x % p :=
  mod_eq_of_lt (Nat.mod_lt x hp)

theorem add_mod (a b p : Nat) (hp : 0 < p) : (a + b) % p = (a % p + b % p) % p := by
  match mod_spec p hp a, mod_spec p hp b, mod_spec p hp (a % p + b % p) with
  | ⟨qa, ha⟩, ⟨qb, hb⟩, ⟨qc, hc⟩ =>
    apply mod_unique (q := qa + qb + qc) (Nat.mod_lt _ hp)
    rw [Nat.left_distrib, Nat.left_distrib, Nat.add_assoc, ← hc]
    rw [Nat.add_assoc, Nat.add_left_comm (p * qb), ← Nat.add_assoc, ← ha, ← hb]

theorem add_mul_mod_self_left (x k p : Nat) (hp : 0 < p) : (p * k + x) % p = x % p := by
  match mod_spec p hp x with
  | ⟨q, hq⟩ =>
    apply mod_unique (q := k + q) (Nat.mod_lt x hp)
    rw [Nat.left_distrib, Nat.add_assoc, ← hq]

theorem mul_mod_left' (a b p : Nat) (hp : 0 < p) : (a * b) % p = (a % p * b) % p := by
  match mod_spec p hp a with
  | ⟨qa, ha⟩ =>
    have e : a * b = p * (qa * b) + a % p * b := by
      rw [← mul_assoc, ← add_mul, ← ha]
    rw [e, add_mul_mod_self_left _ _ _ hp]

theorem mul_mod (a b p : Nat) (hp : 0 < p) : (a * b) % p = (a % p * (b % p)) % p := by
  rw [mul_mod_left' a b p hp, Nat.mul_comm (a % p) b, mul_mod_left' b (a % p) p hp,
    Nat.mul_comm (b % p) (a % p)]

theorem mod_self (p : Nat) (hp : 0 < p) : p % p = 0 :=
  mod_unique hp (by rw [Nat.mul_one, Nat.add_zero])

theorem zero_mod (p : Nat) : 0 % p = 0 := rfl

theorem mod_add_mod (a b p : Nat) (hp : 0 < p) : (a % p + b) % p = (a + b) % p := by
  rw [add_mod a b p hp, add_mod (a % p) b p hp, mod_mod _ _ hp]

theorem add_mod_mod (a b p : Nat) (hp : 0 < p) : (a + b % p) % p = (a + b) % p := by
  rw [add_mod a b p hp, add_mod a (b % p) p hp, mod_mod _ _ hp]

theorem mod_mul_mod (a b p : Nat) (hp : 0 < p) : (a % p * b) % p = (a * b) % p :=
  (mul_mod_left' a b p hp).symm

theorem mul_mod_mod (a b p : Nat) (hp : 0 < p) : (a * (b % p)) % p = (a * b) % p := by
  rw [mul_mod a (b % p) p hp, mod_mod _ _ hp, ← mul_mod a b p hp]

theorem mod_lt' (x : Nat) {p : Nat} (hp : 0 < p) : x % p < p := Nat.mod_lt x hp

end mod

/-! ## Powers -/

theorem pow_succ' (a n : Nat) : a ^ (n + 1) = a ^ n * a := rfl

theorem pow_add (a m n : Nat) : a ^ (m + n) = a ^ m * a ^ n := by
  induction n with
  | zero => rw [Nat.add_zero, Nat.pow_zero, Nat.mul_one]
  | succ n ih => rw [Nat.add_succ, Nat.pow_succ, ih, Nat.pow_succ, mul_assoc]

theorem pow_mul (a m n : Nat) : a ^ (m * n) = (a ^ m) ^ n := by
  induction n with
  | zero => rw [Nat.mul_zero, Nat.pow_zero, Nat.pow_zero]
  | succ n ih => rw [Nat.mul_succ, pow_add, ih, Nat.pow_succ]

theorem pos_pow_of_pos {a : Nat} (n : Nat) (h : 0 < a) : 0 < a ^ n := Nat.pow_pos h

end FRC.Nat

/-! inlined: FrcCore/Pigeonhole.lean -/

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
      | isTrue e => by rw [if_pos e]
      | isFalse e => by
          rw [if_neg e]
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
          rw [show erase v (a :: l) = l from if_pos e] at h
          exact Or.inr h
      | isFalse e => by
          rw [show erase v (a :: l) = a :: erase v l from if_neg e] at h
          exact match h with
            | Or.inl h' => Or.inl h'
            | Or.inr h' => Or.inr (mem_of_mem_erase h')

theorem mem_erase_of_ne {w v : Nat} (hwv : w ≠ v) : ∀ {l : List Nat}, mem w l → mem w (erase v l)
  | [], h => absurd h id
  | a :: l, h => by
    exact match Nat.decEq a v with
      | isTrue e => by
          rw [show erase v (a :: l) = l from if_pos e]
          exact match h with
            | Or.inl h' => absurd (h'.trans e) hwv
            | Or.inr h' => h'
      | isFalse e => by
          rw [show erase v (a :: l) = a :: erase v l from if_neg e]
          exact match h with
            | Or.inl h' => Or.inl h'
            | Or.inr h' => Or.inr (mem_erase_of_ne hwv h')

theorem nodup_erase (v : Nat) : ∀ {l : List Nat}, NoDup l → NoDup (erase v l)
  | [], _ => trivial
  | a :: l, ⟨ha, hl⟩ => by
    exact match Nat.decEq a v with
      | isTrue e => by rw [show erase v (a :: l) = l from if_pos e]; exact hl
      | isFalse e => by
          rw [show erase v (a :: l) = a :: erase v l from if_neg e]
          exact ⟨fun h => ha (mem_of_mem_erase h), nodup_erase v hl⟩

theorem not_mem_erase_self (v : Nat) : ∀ {l : List Nat}, NoDup l → ¬ mem v (erase v l)
  | [], _, h => h
  | a :: l, ⟨ha, hl⟩, h => by
    exact match Nat.decEq a v with
      | isTrue e => by
          rw [show erase v (a :: l) = l from if_pos e] at h
          exact ha (e ▸ h)
      | isFalse e => by
          rw [show erase v (a :: l) = a :: erase v l from if_neg e] at h
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

/-! inlined: FrcCore/Shell.lean -/

/-!
# FrcCore.Shell — the residues of a shell, from first principles

`Shell p` is the set of residues mod `p`, carried by their canonical representatives `val < p` — no
quotient type, so no `Quot.sound`; every identity below is an identity of representatives, decided by
`Nat` arithmetic. The operations reduce by `%`, so `decide` computes on any concrete shell through the
kernel's accelerated `Nat` arithmetic, and every theorem is checked to depend on no axiom.

The ring laws are derived from `FrcCore.Nat`'s division algorithm (`mod_unique`); negation is
characterised by `add_neg : a + -a = 0`, and everything about `-` follows from the uniqueness of
additive inverses (`neg_unique`), never from `Nat` subtraction.
-/

namespace FRC

/-- A residue mod `p`: its representative and the bound. -/
structure Shell (p : Nat) where
  val : Nat
  lt : val < p

/-- `Pos p`: the modulus is positive. Instances for literals `n + 1` are found automatically. -/
class Pos (p : Nat) : Prop where
  pos : 0 < p

instance (n : Nat) : Pos (n + 1) := ⟨Nat.zero_lt_succ n⟩

namespace Shell

variable {p : Nat}

theorem ext {a b : Shell p} (h : a.val = b.val) : a = b := by
  cases a; cases b; cases h; rfl

theorem val_injective {a b : Shell p} (h : a = b) : a.val = b.val := by cases h; rfl

instance : DecidableEq (Shell p) := fun a b =>
  if h : a.val = b.val then isTrue (ext h) else isFalse (fun e => h (val_injective e))

section ops
variable [Pos p]

/-- The residue of a natural number. -/
def ofNat (n : Nat) : Shell p := ⟨n % p, Nat.mod_lt n Pos.pos⟩

instance (n : Nat) : OfNat (Shell p) n := ⟨ofNat n⟩
instance : Add (Shell p) := ⟨fun a b => ofNat (a.val + b.val)⟩
instance : Mul (Shell p) := ⟨fun a b => ofNat (a.val * b.val)⟩
instance : Neg (Shell p) := ⟨fun a => ofNat (p - a.val)⟩

/-- Powers by structural recursion (`a ^ 0 = 1`, `a ^ (n+1) = a ^ n * a`). -/
def pow (a : Shell p) : Nat → Shell p
  | 0 => 1
  | n + 1 => pow a n * a

instance : Pow (Shell p) Nat := ⟨pow⟩

theorem hp : 0 < p := Pos.pos

@[simp] theorem val_ofNat (n : Nat) : (ofNat n : Shell p).val = n % p := rfl
theorem val_add (a b : Shell p) : (a + b).val = (a.val + b.val) % p := rfl
theorem val_mul (a b : Shell p) : (a * b).val = (a.val * b.val) % p := rfl
theorem val_neg (a : Shell p) : (-a).val = (p - a.val) % p := rfl
theorem val_lit (n : Nat) : (OfNat.ofNat n : Shell p).val = n % p := rfl
theorem val_zero : (0 : Shell p).val = 0 := rfl
theorem val_one : (1 : Shell p).val = 1 % p := rfl
theorem pow_zero (a : Shell p) : a ^ 0 = 1 := rfl
theorem pow_succ (a : Shell p) (n : Nat) : a ^ (n + 1) = a ^ n * a := rfl

theorem ofNat_val (a : Shell p) : ofNat a.val = a :=
  ext (FRC.Nat.mod_eq_of_lt a.lt)

theorem ofNat_mod (n : Nat) : (ofNat (n % p) : Shell p) = ofNat n :=
  ext (FRC.Nat.mod_mod n p hp)

/-! ### The additive laws -/

theorem add_comm (a b : Shell p) : a + b = b + a :=
  ext (by rw [val_add, val_add, Nat.add_comm])

theorem add_assoc (a b c : Shell p) : a + b + c = a + (b + c) :=
  ext (by
    rw [val_add, val_add, val_add, val_add, FRC.Nat.mod_add_mod _ _ _ hp, FRC.Nat.add_mod_mod _ _ _ hp,
      Nat.add_assoc])

theorem zero_add (a : Shell p) : 0 + a = a :=
  ext (by rw [val_add, val_zero, Nat.zero_add]; exact FRC.Nat.mod_eq_of_lt a.lt)

theorem add_zero (a : Shell p) : a + 0 = a := by rw [add_comm]; exact zero_add a

theorem add_left_comm (a b c : Shell p) : a + (b + c) = b + (a + c) := by
  rw [← add_assoc, add_comm a b, add_assoc]

theorem add_add_add_comm (a b c d : Shell p) : a + b + (c + d) = a + c + (b + d) := by
  rw [add_assoc, add_assoc, add_left_comm b]

/-! ### The multiplicative laws -/

theorem mul_comm (a b : Shell p) : a * b = b * a :=
  ext (by rw [val_mul, val_mul, Nat.mul_comm])

theorem mul_assoc (a b c : Shell p) : a * b * c = a * (b * c) :=
  ext (by
    rw [val_mul, val_mul, val_mul, val_mul, FRC.Nat.mod_mul_mod _ _ _ hp, FRC.Nat.mul_mod_mod _ _ _ hp,
      FRC.Nat.mul_assoc])

theorem one_mul (a : Shell p) : 1 * a = a :=
  ext (by rw [val_mul, val_one, FRC.Nat.mod_mul_mod _ _ _ hp, Nat.one_mul]; exact FRC.Nat.mod_eq_of_lt a.lt)

theorem mul_one (a : Shell p) : a * 1 = a := by rw [mul_comm]; exact one_mul a

theorem zero_mul (a : Shell p) : 0 * a = 0 :=
  ext (by rw [val_mul, val_zero, Nat.zero_mul]; rfl)

theorem mul_zero (a : Shell p) : a * 0 = 0 := by rw [mul_comm]; exact zero_mul a

theorem mul_left_comm (a b c : Shell p) : a * (b * c) = b * (a * c) := by
  rw [← mul_assoc, mul_comm a b, mul_assoc]

theorem left_distrib (a b c : Shell p) : a * (b + c) = a * b + a * c :=
  ext (by
    rw [val_mul, val_add, val_add, val_mul, val_mul, FRC.Nat.mul_mod_mod _ _ _ hp,
      FRC.Nat.add_mod _ _ _ hp, FRC.Nat.mod_mod _ _ hp, FRC.Nat.mod_mod _ _ hp, ← FRC.Nat.add_mod _ _ _ hp,
      Nat.left_distrib])

theorem right_distrib (a b c : Shell p) : (a + b) * c = a * c + b * c := by
  rw [mul_comm, left_distrib, mul_comm c a, mul_comm c b]

/-! ### Negation, characterised by `add_neg` -/

theorem add_neg (a : Shell p) : a + -a = 0 :=
  ext (by
    rw [val_add, val_neg, FRC.Nat.add_mod_mod _ _ _ hp, FRC.Nat.add_sub_of_le (Nat.le_of_lt a.lt),
      FRC.Nat.mod_self p hp]; rfl)

theorem neg_add (a : Shell p) : -a + a = 0 := by rw [add_comm]; exact add_neg a

/-- Additive inverses are unique. -/
theorem neg_unique {a x y : Shell p} (hx : a + x = 0) (hy : a + y = 0) : x = y := by
  calc x = x + 0 := (add_zero x).symm
    _ = x + (a + y) := by rw [hy]
    _ = (x + a) + y := (add_assoc _ _ _).symm
    _ = (a + x) + y := by rw [add_comm x a]
    _ = 0 + y := by rw [hx]
    _ = y := zero_add y

theorem neg_eq_of_add_eq_zero {a b : Shell p} (h : a + b = 0) : -a = b :=
  neg_unique (add_neg a) h

theorem neg_neg (a : Shell p) : - -a = a :=
  neg_eq_of_add_eq_zero (neg_add a)

theorem neg_zero : (-0 : Shell p) = 0 :=
  neg_eq_of_add_eq_zero (add_zero 0)

theorem neg_mul (a b : Shell p) : -(a * b) = -a * b :=
  neg_eq_of_add_eq_zero (by rw [← right_distrib, add_neg, zero_mul])

theorem mul_neg (a b : Shell p) : -(a * b) = a * -b := by
  rw [mul_comm, neg_mul, mul_comm]

theorem neg_mul_neg (a b : Shell p) : -a * -b = a * b := by
  rw [← neg_mul, ← mul_neg, neg_neg]

theorem neg_add_rev (a b : Shell p) : -(a + b) = -a + -b :=
  neg_eq_of_add_eq_zero (by
    rw [add_assoc, add_left_comm b, ← add_assoc, add_neg, zero_add, add_neg])

theorem add_right_cancel {a b c : Shell p} (h : a + c = b + c) : a = b := by
  have : a + c + -c = b + c + -c := by rw [h]
  rw [add_assoc, add_neg, add_zero, add_assoc, add_neg, add_zero] at this
  exact this

theorem eq_neg_of_add_eq_zero {a b : Shell p} (h : a + b = 0) : a = -b := by
  rw [← neg_neg a, neg_eq_of_add_eq_zero h]

theorem neg_one_mul (a : Shell p) : -1 * a = -a := by rw [← neg_mul, one_mul]

/-! ### Powers -/

theorem pow_one (a : Shell p) : a ^ 1 = a := by rw [pow_succ, pow_zero, one_mul]

theorem one_pow (n : Nat) : (1 : Shell p) ^ n = 1 := by
  induction n with
  | zero => rfl
  | succ n ih => rw [pow_succ, ih, mul_one]

theorem pow_add (a : Shell p) (m n : Nat) : a ^ (m + n) = a ^ m * a ^ n := by
  induction n with
  | zero => rw [Nat.add_zero, pow_zero, mul_one]
  | succ n ih => rw [Nat.add_succ, pow_succ, ih, pow_succ, mul_assoc]

theorem pow_mul (a : Shell p) (m n : Nat) : a ^ (m * n) = (a ^ m) ^ n := by
  induction n with
  | zero => rw [Nat.mul_zero, pow_zero, pow_zero]
  | succ n ih => rw [Nat.mul_succ, pow_add, ih, pow_succ]

theorem pow_mul_comm (a : Shell p) (m n : Nat) : (a ^ m) ^ n = (a ^ n) ^ m := by
  rw [← pow_mul, Nat.mul_comm, pow_mul]

theorem mul_pow (a b : Shell p) (n : Nat) : (a * b) ^ n = a ^ n * b ^ n := by
  induction n with
  | zero => rw [pow_zero, pow_zero, pow_zero, mul_one]
  | succ n ih =>
    rw [pow_succ, pow_succ, pow_succ, ih, mul_assoc, mul_assoc, mul_left_comm (b ^ n) a b]

theorem pow_two (a : Shell p) : a ^ 2 = a * a := by rw [pow_succ, pow_one]

theorem neg_pow_two (a : Shell p) : (-a) ^ 2 = a ^ 2 := by rw [pow_two, pow_two, neg_mul_neg]

/-- `(-1)^n` by the parity of `n`. -/
theorem neg_one_pow (n : Nat) : (-1 : Shell p) ^ n = if n % 2 = 0 then 1 else -1 := by
  induction n with
  | zero => rfl
  | succ n ih =>
    rw [pow_succ, ih]
    exact match Nat.decEq (n % 2) 0 with
      | .isTrue h => by
          rw [if_pos h, one_mul]
          have : (n + 1) % 2 = 1 := by
            rw [← FRC.Nat.mod_add_mod _ _ _ (Nat.zero_lt_succ 1), h]
          rw [if_neg (by rw [this]; exact fun e => Nat.noConfusion e)]
      | .isFalse h => by
          rw [if_neg h, neg_mul_neg, one_mul]
          have h1 : n % 2 = 1 := by
            have := Nat.mod_lt n (Nat.zero_lt_succ 1)
            exact match n % 2, this, h with
              | 0, _, h => absurd rfl h
              | 1, _, _ => rfl
              | k + 2, hk, _ => absurd hk (Nat.not_lt_of_le (Nat.le_add_left 2 k))
          have : (n + 1) % 2 = 0 := by
            rw [← FRC.Nat.mod_add_mod _ _ _ (Nat.zero_lt_succ 1), h1]
          rw [if_pos this]

end ops

end Shell
end FRC

/-! inlined: FrcCore/Frame.lean -/

/-!
# FrcCore.Frame — the frame `(τ; 0, 1, g)` and the Euclidean datum, from first principles

The shell of capacity `κ` has modulus `p = 4κ + 1`; its frame carries the drive `g` (00:A8, 00:C1).
One decidable predicate states what the frame's generator is: `IsPrimitive g n` (`g^n = 1`, no positive
power below `n` is `1`). That `g` then *generates* — every nonzero residue is a power of `g`
(`Generates g n`, also decidable) — is proved by the pigeonhole (`FrcCore.Pigeonhole`): the `n` powers are
distinct nonzero residues and there are `n` of those. Primality of `p` is neither assumed nor used; the
classical equivalence ("a primitive root of order `p − 1` exists iff `p` is prime") is a theorem for later.

From primitivity alone: inverses (`exists_inv`), no zero divisors (`mul_eq_zero`), the square roots
of one (`sq_eq_one`), the half-period `g^{2κ} = −1` (2:D1, 00:C1), the quarter-turn `i = −g^κ` with
`i² = −1` (1:B3, 2:D2), its orientation classes under `g ↦ g^u` (2:D5), and the Euler identity
`(g^i)^{i·2κ} = (−1)^i` (2:D6, 00:C14). No axioms.
-/

namespace FRC
namespace Shell

variable {p : Nat} [Pos p]

/-- 00:A8 — the drive generator is primitive of order `n`: `g^n = 1` and `g^l ≠ 1` for `0 < l < n`. -/
def IsPrimitive (g : Shell p) (n : Nat) : Prop :=
  g ^ n = 1 ∧ ∀ l, l < n → 0 < l → g ^ l ≠ 1

instance (g : Shell p) (n : Nat) : Decidable (IsPrimitive g n) := by
  unfold IsPrimitive; exact inferInstance

/-- 00:A8 — the drive generates the shell: every nonzero residue `v < p` is `g^m` for some `m < n`. -/
def Generates (g : Shell p) (n : Nat) : Prop :=
  ∀ v, v < p → 0 < v → ∃ m, m < n ∧ (g ^ m).val = v

/-- Bounded existence `∃ m < n, P m`, decided by search — Lean's own `Nat.decidableExistsLT` carries
`propext` and `Quot.sound`; this one carries nothing. -/
def decExistsLT (P : Nat → Prop) [DecidablePred P] : (n : Nat) → Decidable (∃ m, m < n ∧ P m)
  | 0 => isFalse (fun ⟨m, hm, _⟩ => Nat.not_lt_zero m hm)
  | n + 1 =>
    match decExistsLT P n with
    | isTrue h => isTrue (match h with | ⟨m, hm, hp⟩ => ⟨m, Nat.lt_succ_of_lt hm, hp⟩)
    | isFalse hno =>
      if h : P n then isTrue ⟨n, Nat.lt_succ_self n, h⟩
      else isFalse (fun ⟨m, hm, hp⟩ =>
        match Nat.lt_or_ge m n with
        | .inl hlt => hno ⟨m, hlt, hp⟩
        | .inr hge => h ((Nat.le_antisymm (Nat.le_of_lt_succ hm) hge) ▸ hp))

instance (g : Shell p) (n : Nat) : Decidable (Generates g n) := by
  unfold Generates
  have : ∀ v, Decidable (∃ m, m < n ∧ (g ^ m).val = v) := fun v => decExistsLT (fun m => (g ^ m).val = v) n
  exact inferInstance

/-- 00:C1 — the frame `(τ; 0, 1, g)` on the shell of capacity `κ`: `p = 4κ + 1`, `κ` positive, and the
drive `g` a primitive generator of the `p − 1` nonzero residues. -/
structure Frame (p : Nat) [Pos p] (κ : Nat) (g : Shell p) : Prop where
  cap : p = 4 * κ + 1
  cap_pos : 0 < κ
  prim : IsPrimitive g (p - 1)

namespace Frame
variable {κ : Nat} {g : Shell p}

theorem n_eq (F : Frame p κ g) : p - 1 = 4 * κ := by rw [F.cap]; rfl

theorem n_pos (F : Frame p κ g) : 0 < p - 1 := by
  rw [F.n_eq]; exact Nat.mul_pos (Nat.zero_lt_succ 3) F.cap_pos

theorem one_lt_p (F : Frame p κ g) : 1 < p := by
  rw [F.cap]; exact Nat.succ_lt_succ (Nat.mul_pos (Nat.zero_lt_succ 3) F.cap_pos)

theorem one_ne_zero (F : Frame p κ g) : (1 : Shell p) ≠ 0 := fun h => by
  have := val_injective h
  rw [val_one, val_zero, FRC.Nat.mod_eq_of_lt F.one_lt_p] at this
  exact Nat.noConfusion this

theorem pow_n (F : Frame p κ g) : g ^ (p - 1) = 1 := F.prim.1

/-- Powers of the drive are periodic with period `p − 1`. -/
theorem pow_mod (F : Frame p κ g) (l : Nat) : g ^ l = g ^ (l % (p - 1)) := by
  match FRC.Nat.mod_spec (p - 1) F.n_pos l with
  | ⟨q, hq⟩ =>
    calc g ^ l = g ^ ((p - 1) * q + l % (p - 1)) := by rw [← hq]
      _ = (g ^ (p - 1)) ^ q * g ^ (l % (p - 1)) := by rw [pow_add, pow_mul]
      _ = g ^ (l % (p - 1)) := by rw [F.pow_n, one_pow, one_mul]

theorem pow_eq_one_of_mod (F : Frame p κ g) {l : Nat} (h : l % (p - 1) = 0) : g ^ l = 1 := by
  rw [F.pow_mod, h, pow_zero]

theorem mod_eq_zero_of_pow_eq_one (F : Frame p κ g) {l : Nat} (h : g ^ l = 1) : l % (p - 1) = 0 := by
  rw [F.pow_mod] at h
  exact match Nat.decEq (l % (p - 1)) 0 with
    | .isTrue h0 => h0
    | .isFalse h0 => absurd h (F.prim.2 _ (Nat.mod_lt l F.n_pos) (Nat.pos_of_ne_zero h0))

theorem pow_inj (F : Frame p κ g) {i j : Nat} (hi : i < p - 1) (hj : j < p - 1) (h : g ^ i = g ^ j) :
    i = j := by
  have key : ∀ {i j : Nat}, i ≤ j → j < p - 1 → g ^ i = g ^ j → i = j := by
    intro i j hij hj h
    have hji : j - i < p - 1 := Nat.lt_of_le_of_lt (Nat.sub_le j i) hj
    have e : g ^ j = g ^ i * g ^ (j - i) := by rw [← pow_add, FRC.Nat.add_sub_of_le hij]
    have hinv : g ^ i * g ^ (p - 1 - i) = 1 := by
      rw [← pow_add, FRC.Nat.add_sub_of_le (Nat.le_of_lt (Nat.lt_of_le_of_lt hij hj)), F.pow_n]
    have h1 : g ^ (j - i) = 1 := by
      calc g ^ (j - i) = 1 * g ^ (j - i) := (one_mul _).symm
        _ = g ^ (p - 1 - i) * g ^ i * g ^ (j - i) := by rw [mul_comm (g ^ (p - 1 - i)), hinv]
        _ = g ^ (p - 1 - i) * g ^ j := by rw [mul_assoc, ← e]
        _ = g ^ (p - 1 - i) * g ^ i := by rw [h]
        _ = 1 := by rw [mul_comm, hinv]
    have h2 := F.mod_eq_zero_of_pow_eq_one h1
    rw [FRC.Nat.mod_eq_of_lt hji] at h2
    have : j = i + (j - i) := (FRC.Nat.add_sub_of_le hij).symm
    rw [h2, Nat.add_zero] at this
    exact this.symm
  exact match Nat.lt_or_ge i j with
    | .inl hlt => key (Nat.le_of_lt hlt) hj h
    | .inr hge => (key hge hi h.symm).symm

theorem g_ne_zero (F : Frame p κ g) : g ≠ 0 := fun h0 => by
  have hn := F.pow_n
  have : p - 1 = (p - 2) + 1 := by
    have := F.one_lt_p
    match p, this with
    | k + 2, _ => rfl
  rw [this, pow_succ, h0, mul_zero] at hn
  exact F.one_ne_zero hn.symm

/-- No power of the drive is zero: `g^m · g^{(n−1)m} = g^{nm} = 1`. -/
theorem pow_ne_zero (F : Frame p κ g) (m : Nat) : g ^ m ≠ 0 := fun h0 => by
  have hn := F.n_pos
  have e : m + (p - 1 - 1) * m = (p - 1) * m := by
    calc m + (p - 1 - 1) * m = 1 * m + (p - 1 - 1) * m := by rw [Nat.one_mul]
      _ = (1 + (p - 1 - 1)) * m := (FRC.Nat.add_mul _ _ _).symm
      _ = (p - 1) * m := by rw [FRC.Nat.add_sub_of_le hn]
  have : g ^ m * g ^ ((p - 1 - 1) * m) = 1 := by
    rw [← pow_add, e, pow_mul, F.pow_n, one_pow]
  rw [h0, zero_mul] at this
  exact F.one_ne_zero this.symm

/-- The representatives of `g^0, …, g^{n−1}`, as a list (latest first). -/
def powList (g : Shell p) : Nat → List Nat
  | 0 => []
  | m + 1 => (g ^ m).val :: powList g m

theorem powList_length (g : Shell p) (n : Nat) : (powList g n).length = n := by
  induction n with
  | zero => rfl
  | succ n ih => show (powList g n).length + 1 = n + 1; rw [ih]

theorem mem_powList {g : Shell p} {v : Nat} : ∀ {n : Nat}, Pigeonhole.mem v (powList g n) → ∃ m, m < n ∧ (g ^ m).val = v
  | 0, h => absurd h id
  | n + 1, h => match h with
    | Or.inl e => ⟨n, Nat.lt_succ_self n, e.symm⟩
    | Or.inr h' => match mem_powList h' with
      | ⟨m, hm, e⟩ => ⟨m, Nat.lt_succ_of_lt hm, e⟩

theorem powList_nodup (F : Frame p κ g) : ∀ {n : Nat}, n ≤ p - 1 → Pigeonhole.NoDup (powList g n)
  | 0, _ => trivial
  | n + 1, hn => ⟨fun h => match mem_powList h with
      | ⟨m, hm, e⟩ =>
        have : m = n := F.pow_inj (Nat.lt_trans hm hn) hn (ext e)
        Nat.lt_irrefl n (this ▸ hm),
    powList_nodup F (Nat.le_of_lt hn)⟩

/-- 00:A8 — the drive generates: every nonzero residue is a power `g^m`, `m < p − 1` (the pigeonhole). -/
theorem generates (F : Frame p κ g) : Generates g (p - 1) := by
  intro v hv hv0
  have hb : ∀ e, Pigeonhole.mem e (powList g (p - 1)) → 1 ≤ e ∧ e ≤ p - 1 := fun e he =>
    match mem_powList he with
    | ⟨m, _, hm⟩ =>
      ⟨Nat.pos_of_ne_zero (fun h0 => F.pow_ne_zero m (ext (by rw [hm, h0]; rfl))),
       by rw [← hm]; exact Nat.le_of_lt_succ (Nat.lt_of_lt_of_le (g ^ m).lt (Nat.le_of_eq (FRC.Nat.sub_add_cancel Pos.pos).symm))⟩
  exact mem_powList (Pigeonhole.mem_of_nodup_of_length (p - 1) (powList g (p - 1)) (F.powList_nodup (Nat.le_refl _))
    hb (powList_length g (p - 1)) v hv0 (Nat.le_of_lt_succ (Nat.lt_of_lt_of_le hv (Nat.le_of_eq (FRC.Nat.sub_add_cancel Pos.pos).symm))))

/-- Every nonzero residue is a power of the drive, on residues. -/
theorem eq_pow_of_ne_zero (F : Frame p κ g) {x : Shell p} (hx : x ≠ 0) :
    ∃ m, m < p - 1 ∧ g ^ m = x := by
  have hv : 0 < x.val := Nat.pos_of_ne_zero (fun h => hx (ext h))
  match F.generates x.val x.lt hv with
  | ⟨m, hm, e⟩ => exact ⟨m, hm, ext e⟩

theorem exists_inv (F : Frame p κ g) {x : Shell p} (hx : x ≠ 0) : ∃ y, x * y = 1 := by
  match F.eq_pow_of_ne_zero hx with
  | ⟨m, hm, e⟩ =>
    refine ⟨g ^ (p - 1 - m), ?_⟩
    rw [← e, ← pow_add, FRC.Nat.add_sub_of_le (Nat.le_of_lt hm), F.pow_n]

theorem mul_eq_zero (F : Frame p κ g) {a b : Shell p} (h : a * b = 0) : a = 0 ∨ b = 0 :=
  match Shell.instDecidableEq a 0 with
  | .isTrue ha => .inl ha
  | .isFalse ha => .inr (by
      match F.exists_inv ha with
      | ⟨y, hy⟩ =>
        calc b = 1 * b := (one_mul b).symm
          _ = y * a * b := by rw [mul_comm y a, hy]
          _ = y * (a * b) := mul_assoc _ _ _
          _ = 0 := by rw [h, mul_zero])

theorem mul_ne_zero (F : Frame p κ g) {a b : Shell p} (ha : a ≠ 0) (hb : b ≠ 0) : a * b ≠ 0 :=
  fun h => match F.mul_eq_zero h with
    | .inl e => ha e
    | .inr e => hb e

/-- Cancellation: `a * b = a * c` with `a ≠ 0` gives `b = c`. -/
theorem mul_left_cancel (F : Frame p κ g) {a b c : Shell p} (ha : a ≠ 0) (h : a * b = a * c) : b = c := by
  have : a * (b + -c) = 0 := by rw [left_distrib, ← mul_neg, h, add_neg]
  match F.mul_eq_zero this with
  | .inl e => exact absurd e ha
  | .inr e =>
    calc b = b + 0 := (add_zero b).symm
      _ = b + (-c + c) := by rw [neg_add]
      _ = (b + -c) + c := (add_assoc _ _ _).symm
      _ = c := by rw [e, zero_add]

/-- The square roots of one are `±1`. -/
theorem sq_eq_one (F : Frame p κ g) {x : Shell p} (h : x * x = 1) : x = 1 ∨ x = -1 := by
  have e : (x + -1) * (x + 1) = 0 := by
    rw [right_distrib, left_distrib, left_distrib, h, mul_one, neg_one_mul, neg_one_mul]
    rw [add_assoc, ← add_assoc x (-x), add_neg, zero_add, add_neg]
  match F.mul_eq_zero e with
  | .inl e1 => exact .inl (by
      calc x = x + 0 := (add_zero x).symm
        _ = x + (-1 + 1) := by rw [neg_add]
        _ = (x + -1) + 1 := (add_assoc _ _ _).symm
        _ = 1 := by rw [e1, zero_add])
  | .inr e2 => exact .inr (eq_neg_of_add_eq_zero e2)

/-! ### The Euclidean datum (00:C1) -/

/-- The half-period `π = 2κ`. -/
def halfPeriod (κ : Nat) : Nat := 2 * κ

/-- The oriented quarter-turn `i = −g^κ` (00:C7). -/
def quarterTurn (g : Shell p) (κ : Nat) : Shell p := -(g ^ κ)

theorem two_kappa_lt (F : Frame p κ g) : 2 * κ < p - 1 := by
  rw [F.n_eq]; exact FRC.Nat.mul_lt_mul_of_lt_of_pos (Nat.succ_lt_succ (Nat.succ_lt_succ (Nat.zero_lt_succ 1))) F.cap_pos

theorem two_kappa_pos (F : Frame p κ g) : 0 < 2 * κ := Nat.mul_pos (Nat.zero_lt_succ 1) F.cap_pos

theorem four_kappa (F : Frame p κ g) : 2 * κ + 2 * κ = p - 1 := by
  rw [F.n_eq]
  show 2 * κ + 2 * κ = 2 * 2 * κ
  rw [FRC.Nat.mul_assoc, ← Nat.two_mul (2 * κ)]

/-- 2:D1, 00:C1 — the half-period: `g^{2κ} = −1` for the drive of every frame. -/
theorem half_period (F : Frame p κ g) : g ^ (2 * κ) = -1 := by
  have hsq : g ^ (2 * κ) * g ^ (2 * κ) = 1 := by rw [← pow_add, F.four_kappa, F.pow_n]
  match F.sq_eq_one hsq with
  | .inr e => exact e
  | .inl e => exact absurd e (F.prim.2 (2 * κ) F.two_kappa_lt F.two_kappa_pos)

/-- 1:B3, 2:D2 — the quarter-turn `i = −g^κ` squares to `−1`. -/
theorem quarter_turn_sq (F : Frame p κ g) : quarterTurn g κ * quarterTurn g κ = -1 := by
  unfold quarterTurn
  rw [neg_mul_neg, ← pow_add, ← Nat.two_mul, F.half_period]

/-- 2:D2 — `g^κ` has order four: `(g^κ)^2 = −1` and `(g^κ)^4 = 1`. -/
theorem quarter_turn_order (F : Frame p κ g) : (g ^ κ) ^ 2 = -1 ∧ (g ^ κ) ^ 4 = 1 := by
  have h2 : (g ^ κ) ^ 2 = -1 := by rw [← pow_mul, Nat.mul_comm, F.half_period]
  refine ⟨h2, ?_⟩
  show (g ^ κ) ^ (2 * 2) = 1
  rw [pow_mul, h2, neg_pow_two, one_pow]

/-- 2:D5, 6:B3 — the orientation classes: for `g' = g^u`, the quarter-turn `−g'^κ` is `−g^κ` when
`u ≡ 1 (mod 4)` and `−(−g^κ)` when `u ≡ 3 (mod 4)`. -/
theorem orientation_class (F : Frame p κ g) (u : Nat) :
    (u % 4 = 1 → -((g ^ u) ^ κ) = -(g ^ κ)) ∧ (u % 4 = 3 → -((g ^ u) ^ κ) = -(-(g ^ κ))) := by
  have h4 : (g ^ κ) ^ 4 = 1 := (F.quarter_turn_order).2
  have h2 : (g ^ κ) ^ 2 = -1 := (F.quarter_turn_order).1
  have key : (g ^ u) ^ κ = (g ^ κ) ^ u := pow_mul_comm g u κ
  have hu : (g ^ κ) ^ u = (g ^ κ) ^ (u % 4) := by
    match FRC.Nat.mod_spec 4 (Nat.zero_lt_succ 3) u with
    | ⟨q, hq⟩ =>
      calc (g ^ κ) ^ u = (g ^ κ) ^ (4 * q + u % 4) := by rw [← hq]
        _ = ((g ^ κ) ^ 4) ^ q * (g ^ κ) ^ (u % 4) := by rw [pow_add, pow_mul]
        _ = (g ^ κ) ^ (u % 4) := by rw [h4, one_pow, one_mul]
  constructor
  · intro h1; rw [key, hu, h1, pow_one]
  · intro h3
    rw [key, hu, h3]
    show -((g ^ κ) ^ (2 + 1)) = -(-(g ^ κ))
    rw [pow_add, h2, pow_one, neg_one_mul]

theorem sq_mod_two (i : Nat) : (i * i) % 2 = i % 2 := by
  rw [FRC.Nat.mul_mod i i 2 (Nat.zero_lt_succ 1)]
  have := Nat.mod_lt i (Nat.zero_lt_succ 1)
  match i % 2, this with
  | 0, _ => rfl
  | 1, _ => rfl
  | k + 2, hk => exact absurd hk (Nat.not_lt_of_le (Nat.le_add_left 2 k))

/-- 2:D6, 6:B2, 00:C14 — the Euler identity on the shell: with `e = g^i` and `π = 2κ`,
`(g^i)^{i·2κ} = (−1)^i` for every natural reading `i` of the quarter-turn — `−1` exactly when `i` is odd. -/
theorem euler_identity (F : Frame p κ g) (i : Nat) :
    (g ^ i) ^ (i * (2 * κ)) = if i % 2 = 0 then 1 else -1 := by
  have e1 : (g ^ i) ^ (i * (2 * κ)) = (g ^ (2 * κ)) ^ (i * i) := by
    rw [← pow_mul, ← pow_mul]
    show g ^ (i * (i * (2 * κ))) = g ^ (2 * κ * (i * i))
    rw [← FRC.Nat.mul_assoc, Nat.mul_comm (i * i)]
  rw [e1, F.half_period, neg_one_pow, sq_mod_two]

/-- 00:C1 — the web closes: `2π ≡ −1` on every shell (`4κ = p − 1`). -/
theorem two_pi (F : Frame p κ g) : (ofNat (2 * halfPeriod κ) : Shell p) = -1 := by
  apply ext
  rw [val_ofNat, val_neg, val_one, FRC.Nat.mod_eq_of_lt F.one_lt_p]
  unfold halfPeriod
  rw [← FRC.Nat.mul_assoc]
  show (4 * κ) % p = (p - 1) % p
  rw [F.n_eq]

/-! ### Two is invertible on every shell -/

theorem two_lt_p (F : Frame p κ g) : 2 < p := by
  rw [F.cap]
  have h : 4 * 1 ≤ 4 * κ := Nat.mul_le_mul_left 4 F.cap_pos
  exact Nat.lt_of_lt_of_le (by decide : 2 < 4 * 1 + 1) (Nat.succ_le_succ h)

theorem two_ne_zero (F : Frame p κ g) : (2 : Shell p) ≠ 0 := fun h => by
  have := val_injective h
  rw [val_lit, val_zero, FRC.Nat.mod_eq_of_lt F.two_lt_p] at this
  exact Nat.noConfusion this

theorem two_eq_one_add_one : (2 : Shell p) = 1 + 1 :=
  ext (by rw [val_add, val_one, val_lit, FRC.Nat.mod_add_mod _ _ _ hp, FRC.Nat.add_mod_mod _ _ _ hp])

theorem two_mul' (x : Shell p) : (2 : Shell p) * x = x + x := by
  rw [two_eq_one_add_one, right_distrib, one_mul]

theorem eq_zero_of_eq_neg (F : Frame p κ g) {x : Shell p} (h : x = -x) : x = 0 := by
  have h2 : (2 : Shell p) * x = 0 := by
    rw [two_mul']
    calc x + x = x + -x := by rw [← h]
      _ = 0 := add_neg x
  match F.mul_eq_zero h2 with
  | .inl e => exact absurd e F.two_ne_zero
  | .inr e => exact e

/-- 1:F1 (Theorem 3) — `2s = 0 ⇒ s = 0`: the additive cycle has no element of order two; the antipode of
the origin is not a residue. -/
theorem no_south_pole (F : Frame p κ g) (s : Shell p) (h : (2 : Shell p) * s = 0) : s = 0 :=
  match F.mul_eq_zero h with
  | .inl e => absurd e F.two_ne_zero
  | .inr e => e

end Frame
end Shell
end FRC

/-! inlined: FrcCore/Orbit.lean -/

/-!
# FrcCore.Orbit — the generators form one orbit (2:B3; 1-algebra's torsor of primitive roots)

`Coprime u n` is taken in its invertible form — some `a < n` has `a·u ≡ 1 (mod n)` — which is decidable by
search and, for `n ≥ 1`, the same as `gcd(u, n) = 1` (Bezout); it is what every proof uses. Theorem:
`h` is primitive of order `n = p − 1` exactly when `h = g^u` with `u < n` coprime to `n`. No axioms.
-/

namespace FRC
namespace Shell

/-- `u` is invertible mod `n`: some `a < n` has `a·u % n = 1`. -/
def Coprime (u n : Nat) : Prop := ∃ a, a < n ∧ (a * u) % n = 1

instance (u n : Nat) : Decidable (Coprime u n) := decExistsLT (fun a => (a * u) % n = 1) n

namespace Frame
variable {p : Nat} [Pos p] {κ : Nat} {g : Shell p}

/-- A power of the drive with an invertible exponent is again primitive. -/
theorem primitive_pow_of_coprime (F : Frame p κ g) {u : Nat} (hu : Coprime u (p - 1)) :
    IsPrimitive (g ^ u) (p - 1) := by
  have hn := F.n_pos
  match hu with
  | ⟨a, _, ha⟩ =>
    refine ⟨by rw [pow_mul_comm, F.pow_n, one_pow], ?_⟩
    intro l hl hl0 hpow
    -- (g^u)^l = 1 gives (u·l) % n = 0; with a·u = n·q + 1, g^l = g^{l·a·u} = ((g^u)^l)^a = 1
    have h1 : (u * l) % (p - 1) = 0 := F.mod_eq_zero_of_pow_eq_one (by rw [pow_mul]; exact hpow)
    match FRC.Nat.mod_spec (p - 1) hn (a * u) with
    | ⟨q, hq⟩ =>
      rw [ha] at hq
      have e : l * (a * u) = (p - 1) * (q * l) + l := by
        rw [hq, Nat.left_distrib, Nat.mul_one, FRC.Nat.mul_left_comm, Nat.mul_comm l q]
      have h2 : g ^ (l * (a * u)) = 1 := by
        rw [show l * (a * u) = (u * l) * a by rw [Nat.mul_comm u l, FRC.Nat.mul_assoc, Nat.mul_comm a u]]
        rw [pow_mul, F.pow_eq_one_of_mod h1, one_pow]
      rw [e, pow_add, pow_mul, F.pow_n, one_pow, one_mul] at h2
      have := F.mod_eq_zero_of_pow_eq_one h2
      rw [FRC.Nat.mod_eq_of_lt hl] at this
      exact Nat.lt_irrefl 0 (this ▸ hl0)

/-- The frame of another primitive drive on the same shell. -/
theorem of_primitive (F : Frame p κ g) {h : Shell p} (hh : IsPrimitive h (p - 1)) : Frame p κ h :=
  ⟨F.cap, F.cap_pos, hh⟩

/-- 2:B3 (Props. 2.7, 4.5), 1-algebra's torsor — the primitive generators form one orbit: `h` is primitive
of order `p − 1` exactly when `h = g^u` for some `u < p − 1` coprime to `p − 1`. -/
theorem generator_orbit (F : Frame p κ g) (h : Shell p) :
    IsPrimitive h (p - 1) ↔ ∃ u, u < p - 1 ∧ Coprime u (p - 1) ∧ h = g ^ u := by
  have hn := F.n_pos
  constructor
  · intro hh
    have Fh : Frame p κ h := F.of_primitive hh
    have hh0 : h ≠ 0 := Fh.g_ne_zero
    match F.eq_pow_of_ne_zero hh0 with
    | ⟨u, hu, e⟩ =>
      refine ⟨u, hu, ?_, e.symm⟩
      -- g is a power of h: g = h^v; then g^{u v} = g, so u·v ≡ 1 (mod n)
      match Fh.eq_pow_of_ne_zero F.g_ne_zero with
      | ⟨v, hv, ev⟩ =>
        refine ⟨v, hv, ?_⟩
        have e1 : g ^ (v * u) = g ^ 1 := by
          rw [pow_one, Nat.mul_comm v u, pow_mul, e, ev]
        have h1n : 1 < p - 1 := by
          rw [F.n_eq]; exact Nat.lt_of_lt_of_le (by decide : 1 < 4 * 1) (Nat.mul_le_mul_left 4 F.cap_pos)
        have := F.pow_inj (Nat.mod_lt _ hn) h1n (by rw [← F.pow_mod, e1])
        exact this
  · intro ⟨u, _, hu, e⟩
    rw [e]; exact F.primitive_pow_of_coprime hu

/-- 1:G1, the finitary core (Fermat): every residue satisfies `x^p = x` — the polynomial `X^p − X` vanishes on
the whole shell, which is what the root test of 1:G1 rests on. -/
theorem fermat (F : Frame p κ g) (x : Shell p) : x ^ p = x := by
  have hp1 : x ^ p = x ^ (p - 1) * x :=
    congrArg (fun k => x ^ k) (FRC.Nat.sub_add_cancel Pos.pos).symm
  rw [hp1]
  exact match Shell.instDecidableEq x 0 with
    | isTrue e => by rw [e, mul_zero]
    | isFalse e => by
        match F.eq_pow_of_ne_zero e with
        | ⟨m, _, em⟩ => rw [← em, pow_mul_comm, F.pow_n, one_pow, one_mul]

end Frame
end Shell
end FRC

/-! inlined: FrcCore/Sum.lean -/

/-!
# FrcCore.Sum — finite sums on the shell, the geometric sum, the Fourier inversion

Sums over `l < n` are defined by structural recursion (`sumRange f (n+1) = sumRange f n + f n`): no
`Finset`, no quotient, no function extensionality — a congruence lemma (`sum_congr`) replaces `funext`.
The geometric sum gives the principal-root identity (2:F1, Prop. 6.1 of 2-geometry) and the entrywise
inversion of the shell Fourier matrix `W k j = g^{jk}`: `Σ_l W k l · (−g^{−lj}) = [k = j]` (2:F3,
Prop. 6.3; 6:B5 in matrix form). No axioms.
-/

namespace FRC
namespace Shell

variable {p : Nat} [Pos p]

/-- `sumRange f n = f 0 + f 1 + ⋯ + f (n−1)`. -/
def sumRange (f : Nat → Shell p) : Nat → Shell p
  | 0 => 0
  | n + 1 => sumRange f n + f n

theorem sumRange_zero (f : Nat → Shell p) : sumRange f 0 = 0 := rfl
theorem sumRange_succ (f : Nat → Shell p) (n : Nat) : sumRange f (n + 1) = sumRange f n + f n := rfl

theorem sum_congr {f h : Nat → Shell p} (n : Nat) (e : ∀ l, l < n → f l = h l) :
    sumRange f n = sumRange h n := by
  induction n with
  | zero => rfl
  | succ n ih =>
    rw [sumRange_succ, sumRange_succ, ih (fun l hl => e l (Nat.lt_succ_of_lt hl)),
      e n (Nat.lt_succ_self n)]

theorem sum_add (f h : Nat → Shell p) (n : Nat) :
    sumRange (fun l => f l + h l) n = sumRange f n + sumRange h n := by
  induction n with
  | zero => rw [sumRange_zero, sumRange_zero, sumRange_zero, add_zero]
  | succ n ih =>
    rw [sumRange_succ, sumRange_succ, sumRange_succ, ih, add_add_add_comm]

theorem sum_mul_right (f : Nat → Shell p) (c : Shell p) (n : Nat) :
    sumRange (fun l => f l * c) n = sumRange f n * c := by
  induction n with
  | zero => rw [sumRange_zero, sumRange_zero, zero_mul]
  | succ n ih => rw [sumRange_succ, sumRange_succ, ih, right_distrib]

theorem sum_mul_left (f : Nat → Shell p) (c : Shell p) (n : Nat) :
    sumRange (fun l => c * f l) n = c * sumRange f n := by
  induction n with
  | zero => rw [sumRange_zero, sumRange_zero, mul_zero]
  | succ n ih => rw [sumRange_succ, sumRange_succ, ih, left_distrib]

theorem sum_neg (f : Nat → Shell p) (n : Nat) : sumRange (fun l => -(f l)) n = -(sumRange f n) := by
  induction n with
  | zero => rw [sumRange_zero, sumRange_zero, neg_zero]
  | succ n ih => rw [sumRange_succ, sumRange_succ, ih, neg_add_rev]

theorem sum_const (c : Shell p) (n : Nat) : sumRange (fun _ => c) n = ofNat n * c := by
  induction n with
  | zero => rw [sumRange_zero]; exact (zero_mul c).symm
  | succ n ih =>
    rw [sumRange_succ, ih]
    have : (ofNat (n + 1) : Shell p) = ofNat n + 1 := ext (by
      rw [val_ofNat, val_add, val_ofNat, val_one, FRC.Nat.mod_add_mod _ _ _ hp, FRC.Nat.add_mod_mod _ _ _ hp])
    rw [this, right_distrib, one_mul]

theorem sum_zero {f : Nat → Shell p} (n : Nat) (h : ∀ l, l < n → f l = 0) : sumRange f n = 0 := by
  induction n with
  | zero => rfl
  | succ n ih => rw [sumRange_succ, ih (fun l hl => h l (Nat.lt_succ_of_lt hl)), h n (Nat.lt_succ_self n), add_zero]

/-- A sum with a single nonzero term. -/
theorem sum_eq_single {f : Nat → Shell p} {l₀ : Nat} : ∀ {n : Nat}, l₀ < n → (∀ l, l < n → l ≠ l₀ → f l = 0) →
    sumRange f n = f l₀
  | 0, h, _ => absurd h (Nat.not_lt_zero _)
  | n + 1, hl₀, h => by
    rw [sumRange_succ]
    exact match Nat.decEq l₀ n with
      | isTrue e => by
          rw [sum_zero n (fun l hl => h l (Nat.lt_succ_of_lt hl) (fun e' => absurd hl (by rw [e', e]; exact Nat.lt_irrefl n))),
            zero_add, e]
      | isFalse e => by
          rw [sum_eq_single (Nat.lt_of_le_of_ne (Nat.le_of_lt_succ hl₀) (fun e' => e e')) (fun l hl hne => h l (Nat.lt_succ_of_lt hl) hne),
            h n (Nat.lt_succ_self n) (fun e' => e e'.symm), add_zero]

/-- The telescoping geometric sum: `(Σ_{l<n} x^l)·(x − 1) = x^n − 1`. -/
theorem geom_sum_mul (x : Shell p) (n : Nat) :
    sumRange (fun l => x ^ l) n * (x + -1) = x ^ n + -1 := by
  induction n with
  | zero => rw [sumRange_zero, zero_mul, pow_zero, add_neg]
  | succ n ih =>
    rw [sumRange_succ, right_distrib, ih, left_distrib, ← mul_neg, mul_one, ← pow_succ]
    rw [add_add_add_comm, add_comm (x ^ n) (x ^ (n + 1)), add_comm (-1) (-(x ^ n)), add_assoc,
      ← add_assoc (x ^ n), add_neg, zero_add]

namespace Frame
variable {κ : Nat} {g : Shell p}

/-- `Σ_{l<n} x^l = 0` when `x^n = 1` and `x ≠ 1` (the field has no zero divisors). -/
theorem geom_sum_eq_zero (F : Frame p κ g) {x : Shell p} (n : Nat) (hn : x ^ n = 1) (hx : x ≠ 1) :
    sumRange (fun l => x ^ l) n = 0 := by
  have h := geom_sum_mul x n
  rw [hn, add_neg] at h
  match F.mul_eq_zero h with
  | .inl e => exact e
  | .inr e => exact absurd (by
      calc x = x + 0 := (add_zero x).symm
        _ = x + (-1 + 1) := by rw [neg_add]
        _ = (x + -1) + 1 := (add_assoc _ _ _).symm
        _ = 1 := by rw [e, zero_add]) hx

/-- 6:B6 — the normalization constant read in the field: `n = p − 1 ≡ −1`. -/
theorem ofNat_n (F : Frame p κ g) : (ofNat (p - 1) : Shell p) = -1 := by
  apply ext
  rw [val_ofNat, val_neg, val_one, FRC.Nat.mod_eq_of_lt F.one_lt_p,
    FRC.Nat.mod_eq_of_lt (Nat.sub_lt Pos.pos (Nat.zero_lt_succ 0))]

/-- 2:F1 (Prop. 6.1) — `g` is a principal root of unity: `g^n = 1`, `Σ_{j<n} (g^k)^j = 0` for
`0 < k < n`, and `n = p − 1` reads as `−1` in the shell. -/
theorem principal_root (F : Frame p κ g) (k : Nat) (hk0 : 0 < k) (hk : k < p - 1) :
    g ^ (p - 1) = 1 ∧ sumRange (fun j => (g ^ k) ^ j) (p - 1) = 0 ∧ (ofNat (p - 1) : Shell p) = -1 := by
  refine ⟨F.pow_n, ?_, F.ofNat_n⟩
  apply F.geom_sum_eq_zero
  · rw [pow_mul_comm, F.pow_n, one_pow]
  · exact F.prim.2 k hk hk0

/-- `g^{k + (n − j)} = 1` exactly when `k = j`, for `k, j < n`. -/
theorem pow_shift_eq_one_iff (F : Frame p κ g) {k j : Nat} (hk : k < p - 1) (hj : j < p - 1) :
    g ^ (k + (p - 1 - j)) = 1 ↔ k = j := by
  have hn := F.n_pos
  have hjn : p - 1 - j + j = p - 1 := FRC.Nat.sub_add_cancel (Nat.le_of_lt hj)
  constructor
  · intro h
    have hm := F.mod_eq_zero_of_pow_eq_one h
    match Nat.lt_or_ge k j with
    | .inl hlt =>
      have hlt' : k + (p - 1 - j) < p - 1 := by
        have := Nat.add_lt_add_right hlt (p - 1 - j)
        rw [Nat.add_comm j, hjn] at this
        exact this
      rw [FRC.Nat.mod_eq_of_lt hlt'] at hm
      have hpos : 0 < p - 1 - j := by
        refine Nat.lt_of_add_lt_add_right (n := j) ?_
        rw [Nat.zero_add, hjn]; exact hj
      exact absurd hm (Nat.ne_of_gt (Nat.lt_of_lt_of_le hpos (Nat.le_add_left _ _)))
    | .inr hge =>
      have e : k + (p - 1 - j) = (p - 1) * 1 + (k - j) := by
        rw [Nat.mul_one]
        calc k + (p - 1 - j) = (j + (k - j)) + (p - 1 - j) := by rw [FRC.Nat.add_sub_of_le hge]
          _ = (p - 1 - j + j) + (k - j) := by
              rw [Nat.add_comm j (k - j), Nat.add_assoc, Nat.add_comm (k - j), Nat.add_comm j (p - 1 - j)]
          _ = p - 1 + (k - j) := by rw [hjn]
      rw [e, FRC.Nat.add_mul_mod_self_left _ _ _ hn,
        FRC.Nat.mod_eq_of_lt (Nat.lt_of_le_of_lt (Nat.sub_le k j) hk)] at hm
      have := FRC.Nat.add_sub_of_le hge
      rw [hm, Nat.add_zero] at this
      exact this.symm
  · intro e
    rw [e, FRC.Nat.add_sub_of_le (Nat.le_of_lt hj), F.pow_n]

/-- 2:F3 (Prop. 6.3), 6:B5 — the inversion of the shell Fourier matrix, entrywise: with
`W k j = g^{jk}` and `W' l j = −g^{(n−j)l}` (`= −g^{−lj}`), `Σ_{l<n} W k l · W' l j = [k = j]`. -/
theorem dft_inverse (F : Frame p κ g) {k j : Nat} (hk : k < p - 1) (hj : j < p - 1) :
    sumRange (fun l => g ^ (l * k) * -(g ^ ((p - 1 - j) * l))) (p - 1) = if k = j then 1 else 0 := by
  have hsum : sumRange (fun l => g ^ (l * k) * -(g ^ ((p - 1 - j) * l))) (p - 1)
      = -(sumRange (fun l => (g ^ (k + (p - 1 - j))) ^ l) (p - 1)) := by
    rw [← sum_neg]
    apply sum_congr
    intro l _
    rw [← mul_neg, ← pow_add, ← pow_mul, Nat.mul_comm l k, ← FRC.Nat.add_mul]
  rw [hsum]
  exact match Nat.decEq k j with
    | .isTrue e => by
        rw [if_pos e]
        have h1 : g ^ (k + (p - 1 - j)) = 1 := (F.pow_shift_eq_one_iff hk hj).2 e
        have : sumRange (fun l => (g ^ (k + (p - 1 - j))) ^ l) (p - 1) = ofNat (p - 1) * 1 := by
          rw [← sum_const]; apply sum_congr; intro l _; rw [h1, one_pow]
        rw [this, F.ofNat_n, mul_one, neg_neg]
    | .isFalse e => by
        rw [if_neg e]
        have h1 : g ^ (k + (p - 1 - j)) ≠ 1 := fun h => e ((F.pow_shift_eq_one_iff hk hj).1 h)
        rw [F.geom_sum_eq_zero _ (by rw [pow_mul_comm, F.pow_n, one_pow]) h1, neg_zero]

/-- `g^{k + j} = 1` exactly when `(k + j) % n = 0`, i.e. `j` is the reversal `−k` of `k` (`k, j < n`). -/
theorem pow_add_eq_one_iff (F : Frame p κ g) (k j : Nat) : g ^ (k + j) = 1 ↔ (k + j) % (p - 1) = 0 :=
  ⟨F.mod_eq_zero_of_pow_eq_one, F.pow_eq_one_of_mod⟩

/-- 6:B5 (the shell Fourier matrix squares to the reversal, entrywise): with `W k j = g^{jk}` and
`J k j = [(k + j) % n = 0]`, `Σ_{l<n} W k l · W l j = −J k j` on every shell (`n = p − 1 ≡ −1`). -/
theorem W_sq (F : Frame p κ g) (k j : Nat) :
    sumRange (fun l => g ^ (l * k) * g ^ (j * l)) (p - 1)
      = -(if (k + j) % (p - 1) = 0 then 1 else 0) := by
  have hsum : sumRange (fun l => g ^ (l * k) * g ^ (j * l)) (p - 1)
      = sumRange (fun l => (g ^ (k + j)) ^ l) (p - 1) := by
    apply sum_congr; intro l _
    rw [← pow_add, ← pow_mul, Nat.mul_comm l k, ← FRC.Nat.add_mul]
  rw [hsum]
  exact match Nat.decEq ((k + j) % (p - 1)) 0 with
    | .isTrue e => by
        rw [if_pos e]
        have h1 : g ^ (k + j) = 1 := F.pow_eq_one_of_mod e
        have : sumRange (fun l => (g ^ (k + j)) ^ l) (p - 1) = ofNat (p - 1) * 1 := by
          rw [← sum_const]; apply sum_congr; intro l _; rw [h1, one_pow]
        rw [this, F.ofNat_n, mul_one]
    | .isFalse e => by
        rw [if_neg e, neg_zero]
        exact F.geom_sum_eq_zero _ (by rw [pow_mul_comm, F.pow_n, one_pow]) (fun h => e (F.mod_eq_zero_of_pow_eq_one h))

/-! ### The reversal, the Fourier matrix `W`, the quarter-turn transform `F = i·W` (6:B5, B7) -/

/-- The reversal `rev n k = (n − k) % n`: the index `l` with `(k + l) % n = 0`. -/
def rev (n k : Nat) : Nat := (n - k) % n

theorem rev_lt {n : Nat} (hn : 0 < n) (k : Nat) : rev n k < n := Nat.mod_lt _ hn

theorem rev_zero (n : Nat) (hn : 0 < n) : rev n 0 = 0 := by
  unfold rev; rw [Nat.sub_zero]; exact FRC.Nat.mod_self n hn

theorem rev_of_pos {n k : Nat} (hk : k < n) (hk0 : 0 < k) : rev n k = n - k := by
  unfold rev; exact FRC.Nat.mod_eq_of_lt (Nat.sub_lt (Nat.lt_of_lt_of_le hk0 (Nat.le_of_lt hk)) hk0)

theorem rev_add_mod {n k : Nat} (hk : k < n) : (rev n k + k) % n = 0 := by
  have hn : 0 < n := Nat.lt_of_le_of_lt (Nat.zero_le k) hk
  exact match Nat.decEq k 0 with
    | isTrue e => by rw [e, rev_zero n hn]; rfl
    | isFalse e => by
        rw [rev_of_pos hk (Nat.pos_of_ne_zero e), FRC.Nat.sub_add_cancel (Nat.le_of_lt hk)]
        exact FRC.Nat.mod_self n hn

theorem rev_rev {n k : Nat} (hk : k < n) : rev n (rev n k) = k := by
  have hn : 0 < n := Nat.lt_of_le_of_lt (Nat.zero_le k) hk
  exact match Nat.decEq k 0 with
    | isTrue e => by rw [e, rev_zero n hn, rev_zero n hn]
    | isFalse e => by
        have hk0 := Nat.pos_of_ne_zero e
        rw [rev_of_pos hk hk0]
        have hnk : n - k < n := Nat.sub_lt (Nat.lt_of_lt_of_le hk0 (Nat.le_of_lt hk)) hk0
        have hnk0 : 0 < n - k := by
          refine Nat.lt_of_add_lt_add_right (n := k) ?_
          rw [Nat.zero_add, FRC.Nat.sub_add_cancel (Nat.le_of_lt hk)]; exact hk
        rw [rev_of_pos hnk hnk0]
        calc n - (n - k) = (n - k + k) - (n - k) := by rw [FRC.Nat.sub_add_cancel (Nat.le_of_lt hk)]
          _ = k := FRC.Nat.add_sub_cancel_left _ _

/-- `(k + l) % n = 0` exactly when `l` is the reversal of `k` (`k, l < n`). -/
theorem add_mod_eq_zero_iff {n k l : Nat} (hk : k < n) (hl : l < n) : (k + l) % n = 0 ↔ l = rev n k := by
  have hn : 0 < n := Nat.lt_of_le_of_lt (Nat.zero_le k) hk
  constructor
  · intro h
    exact match Nat.decEq k 0 with
      | isTrue e => by
          rw [e, Nat.zero_add, FRC.Nat.mod_eq_of_lt hl] at h
          rw [e, rev_zero n hn, h]
      | isFalse e => by
          have hk0 := Nat.pos_of_ne_zero e
          rw [rev_of_pos hk hk0]
          exact match Nat.lt_or_ge l (n - k) with
            | Or.inl hlt => by
                have : k + l < n := by
                  have := Nat.add_lt_add_left hlt k
                  rw [FRC.Nat.add_sub_of_le (Nat.le_of_lt hk)] at this; exact this
                rw [FRC.Nat.mod_eq_of_lt this] at h
                exact absurd h (Nat.ne_of_gt (Nat.lt_of_lt_of_le hk0 (Nat.le_add_right k l)))
            | Or.inr hge => by
                have e1 : k + l = n * 1 + (l - (n - k)) := by
                  rw [Nat.mul_one]
                  calc k + l = k + ((n - k) + (l - (n - k))) := by rw [FRC.Nat.add_sub_of_le hge]
                    _ = (k + (n - k)) + (l - (n - k)) := (Nat.add_assoc _ _ _).symm
                    _ = n + (l - (n - k)) := by rw [FRC.Nat.add_sub_of_le (Nat.le_of_lt hk)]
                rw [e1, FRC.Nat.add_mul_mod_self_left _ _ _ hn,
                  FRC.Nat.mod_eq_of_lt (Nat.lt_of_le_of_lt (Nat.sub_le _ _) hl)] at h
                have := FRC.Nat.add_sub_of_le hge
                rw [h, Nat.add_zero] at this
                exact this.symm
  · intro e; rw [e, Nat.add_comm]; exact rev_add_mod hk

/-- The shell Fourier matrix, `W k j = g^{jk}` (6:B5's convention). -/
def W (g : Shell p) (k j : Nat) : Shell p := g ^ (j * k)

/-- The reversal matrix `J k j = [(k + j) % n = 0]`. -/
def J (n k j : Nat) : Shell p := if (k + j) % n = 0 then 1 else 0

/-- The quarter-turn transform `F = i·W`, `i = −g^κ`. -/
def Fmat (g : Shell p) (κ k j : Nat) : Shell p := quarterTurn g κ * W g k j

theorem J_eq {n k l : Nat} (hk : k < n) (hl : l < n) :
    (J n k l : Shell p) = (if l = rev n k then (1 : Shell p) else 0) := by
  unfold J
  exact match Nat.decEq l (rev n k) with
    | isTrue e => by rw [if_pos e, if_pos ((add_mod_eq_zero_iff hk hl).2 e)]
    | isFalse e => by rw [if_neg e, if_neg (fun h => e ((add_mod_eq_zero_iff hk hl).1 h))]

/-- 6:B5 (`W² = −J`, entrywise), in the matrix notation. -/
theorem W_sq' (F : Frame p κ g) (k j : Nat) :
    sumRange (fun l => W g k l * W g l j) (p - 1) = -(J (p - 1) k j) := F.W_sq k j

/-- 6:B5, 6:B7 (`J² = 1`, entrywise): the reversal is an involution, so `F⁴ = J² = 1`. -/
theorem J_sq (F : Frame p κ g) {k j : Nat} (hk : k < p - 1) (hj : j < p - 1) :
    sumRange (fun l => (J (p - 1) k l : Shell p) * J (p - 1) l j) (p - 1) = (if k = j then (1 : Shell p) else 0) := by
  have hn := F.n_pos
  have hr : rev (p - 1) k < p - 1 := rev_lt hn k
  rw [sum_eq_single hr (fun l hl hne => by rw [J_eq hk hl, if_neg hne, zero_mul])]
  rw [J_eq hk hr, if_pos rfl, one_mul, J_eq hr hj, rev_rev hk]
  exact match Nat.decEq k j with
    | isTrue e => by rw [if_pos e, if_pos e.symm]
    | isFalse e => by rw [if_neg e, if_neg (fun h => e h.symm)]

/-- 6:B5, 6:B7 (`F² = J`, entrywise): the quarter-turn transform squares to the reversal. -/
theorem F_sq (F : Frame p κ g) (k j : Nat) :
    sumRange (fun l => Fmat g κ k l * Fmat g κ l j) (p - 1) = J (p - 1) k j := by
  have e : ∀ l, Fmat g κ k l * Fmat g κ l j = (quarterTurn g κ * quarterTurn g κ) * (W g k l * W g l j) := by
    intro l; unfold Fmat
    rw [mul_assoc, mul_left_comm (W g k l), ← mul_assoc]
  rw [sum_congr _ (fun l _ => e l), sum_mul_left, F.W_sq' k j, F.quarter_turn_sq, ← neg_mul, one_mul, neg_neg]

theorem inv_unique {x x' y : Shell p} (h : x * y = 1) (h' : x' * y = 1) : x = x' := by
  calc x = x * (x' * y) := by rw [h', mul_one]
    _ = x' * (x * y) := mul_left_comm _ _ _
    _ = x' := by rw [h, mul_one]

/-- 6:B7 (`W J = J W`, entrywise). -/
theorem W_J_comm (F : Frame p κ g) {k j : Nat} (hk : k < p - 1) (hj : j < p - 1) :
    sumRange (fun l => W g k l * J (p - 1) l j) (p - 1) = sumRange (fun l => J (p - 1) k l * W g l j) (p - 1) := by
  have hn := F.n_pos
  have hrj : rev (p - 1) j < p - 1 := rev_lt hn j
  have hrk : rev (p - 1) k < p - 1 := rev_lt hn k
  rw [sum_eq_single hrj (fun l hl hne => by
        rw [J_eq hl hj, if_neg (fun e => hne (by rw [e, rev_rev hl])), mul_zero])]
  rw [sum_eq_single hrk (fun l hl hne => by rw [J_eq hk hl, if_neg hne, zero_mul])]
  rw [J_eq hrj hj, if_pos (rev_rev hj).symm, mul_one, J_eq hk hrk, if_pos rfl, one_mul]
  unfold W
  -- both are the inverse of g^{jk}
  apply inv_unique (y := g ^ (j * k))
  · rw [← pow_add, ← FRC.Nat.add_mul, F.pow_mod, ← FRC.Nat.mod_mul_mod _ _ _ hn, rev_add_mod hj, Nat.zero_mul,
      FRC.Nat.zero_mod, pow_zero]
  · rw [← pow_add, ← Nat.left_distrib, F.pow_mod, ← FRC.Nat.mul_mod_mod _ _ _ hn, rev_add_mod hk, Nat.mul_zero,
      FRC.Nat.zero_mod, pow_zero]

/-! ### Sums over lists, permutation invariance (the reindexing `j ↦ u·j` of 2:F5) -/

end Frame

/-- The sum of `F` over a list of indices. -/
def sumList (F : Nat → Shell p) : List Nat → Shell p
  | [] => 0
  | a :: l => F a + sumList F l

/-- `[n−1, …, 0]`. -/
def listRange : Nat → List Nat
  | 0 => []
  | n + 1 => n :: listRange n

/-- `[σ (n−1), …, σ 0]`. -/
def imageList (σ : Nat → Nat) : Nat → List Nat
  | 0 => []
  | n + 1 => σ n :: imageList σ n

theorem sumList_imageList (F : Nat → Shell p) (σ : Nat → Nat) (n : Nat) :
    sumList F (imageList σ n) = sumRange (fun j => F (σ j)) n := by
  induction n with
  | zero => rfl
  | succ n ih => show F (σ n) + sumList F (imageList σ n) = sumRange (fun j => F (σ j)) n + F (σ n); rw [ih, add_comm]

theorem sumList_erase (F : Nat → Shell p) {v : Nat} : ∀ {l : List Nat}, Pigeonhole.mem v l →
    sumList F l = F v + sumList F (Pigeonhole.erase v l)
  | [], h => absurd h id
  | a :: l, h => by
    exact match Nat.decEq a v with
      | isTrue e => by rw [show Pigeonhole.erase v (a :: l) = l from if_pos e, e]; rfl
      | isFalse e => by
          rw [show Pigeonhole.erase v (a :: l) = a :: Pigeonhole.erase v l from if_neg e]
          have hm : Pigeonhole.mem v l := match h with
            | Or.inl h' => absurd h'.symm e
            | Or.inr h' => h'
          show F a + sumList F l = F v + (F a + sumList F (Pigeonhole.erase v l))
          rw [sumList_erase F hm, add_left_comm]

theorem imageList_length (σ : Nat → Nat) (n : Nat) : (imageList σ n).length = n := by
  induction n with
  | zero => rfl
  | succ n ih => show (imageList σ n).length + 1 = n + 1; rw [ih]

theorem mem_imageList {σ : Nat → Nat} {v : Nat} : ∀ {n : Nat}, Pigeonhole.mem v (imageList σ n) → ∃ j, j < n ∧ σ j = v
  | 0, h => absurd h id
  | n + 1, h => match h with
    | Or.inl e => ⟨n, Nat.lt_succ_self n, e.symm⟩
    | Or.inr h' => match mem_imageList h' with
      | ⟨j, hj, e⟩ => ⟨j, Nat.lt_succ_of_lt hj, e⟩

theorem imageList_nodup {σ : Nat → Nat} {n : Nat} (hinj : ∀ i j, i < n → j < n → σ i = σ j → i = j) :
    ∀ {m : Nat}, m ≤ n → Pigeonhole.NoDup (imageList σ m)
  | 0, _ => trivial
  | m + 1, hm => ⟨fun h => match mem_imageList h with
      | ⟨j, hj, e⟩ => Nat.lt_irrefl j (hinj j m (Nat.lt_of_lt_of_le hj (Nat.le_of_lt hm)) hm e ▸ hj),
    imageList_nodup hinj (Nat.le_of_lt hm)⟩

/-- A sum over any list of `n` distinct indices below `n` is the sum over `0, …, n−1`. -/
theorem sumList_eq_sumRange (F : Nat → Shell p) : ∀ (n : Nat) (l : List Nat), Pigeonhole.NoDup l →
    (∀ e, Pigeonhole.mem e l → e < n) → l.length = n → sumList F l = sumRange F n
  | 0, [], _, _, _ => rfl
  | 0, a :: l, _, hb, _ => absurd (hb a (Or.inl rfl)) (Nat.not_lt_zero a)
  | n + 1, l, hnd, hb, hlen => by
    have hm : Pigeonhole.mem n l := Pigeonhole.mem_of_nodup_of_length_lt (n + 1) l hnd hb hlen n (Nat.lt_succ_self n)
    rw [sumList_erase F hm, sumRange_succ, add_comm]
    have hb' : ∀ e, Pigeonhole.mem e (Pigeonhole.erase n l) → e < n := fun e he =>
      match Nat.lt_or_ge e n with
      | Or.inl hlt => hlt
      | Or.inr hge =>
        have : e = n := Nat.le_antisymm (Nat.le_of_lt_succ (hb e (Pigeonhole.mem_of_mem_erase he))) hge
        absurd (this ▸ he) (Pigeonhole.not_mem_erase_self n hnd)
    have hlen' : (Pigeonhole.erase n l).length = n := by
      have := Pigeonhole.length_erase_of_mem hm; rw [hlen] at this; exact Nat.succ.inj this
    rw [sumList_eq_sumRange F n (Pigeonhole.erase n l) (Pigeonhole.nodup_erase n hnd) hb' hlen']

/-- Permutation invariance: for `σ` injective on `[0, n)` with values below `n`,
`Σ_{j<n} F (σ j) = Σ_{l<n} F l`. -/
theorem sum_perm (F : Nat → Shell p) (σ : Nat → Nat) (n : Nat) (hlt : ∀ j, j < n → σ j < n)
    (hinj : ∀ i j, i < n → j < n → σ i = σ j → i = j) :
    sumRange (fun j => F (σ j)) n = sumRange F n := by
  rw [← sumList_imageList]
  exact sumList_eq_sumRange F n (imageList σ n) (imageList_nodup hinj (Nat.le_refl n))
    (fun e he => match mem_imageList he with | ⟨j, hj, e'⟩ => e' ▸ hlt j hj) (imageList_length σ n)

namespace Frame
variable {κ : Nat} {g : Shell p}

/-- The shell Fourier transform of `v` at `k`: `Σ_{j<n} v_j g^{jk}`. -/
def dft (g : Shell p) (n : Nat) (v : Nat → Shell p) (k : Nat) : Shell p := sumRange (fun j => v j * g ^ (j * k)) n

/-- The polynomial `P_v(x) = Σ_{j<n} v_j x^j`. -/
def polyEval (n : Nat) (v : Nat → Shell p) (x : Shell p) : Shell p := sumRange (fun j => v j * x ^ j) n

/-- 2:F4 (Prop. 6.5) — the polynomial reading: `F_g(v)_k = P_v(g^k)`. -/
theorem dft_eq_polyEval (g : Shell p) (n : Nat) (v : Nat → Shell p) (k : Nat) :
    dft g n v k = polyEval n v (g ^ k) := by
  unfold dft polyEval
  apply sum_congr; intro j _
  rw [Nat.mul_comm j k, pow_mul]

/-- The reindexing `j ↦ u·j mod n` is injective on `[0, n)` when `u` is invertible mod `n`. -/
theorem mul_mod_inj (F : Frame p κ g) {u : Nat} (hu : Coprime u (p - 1)) {i j : Nat} (hi : i < p - 1) (hj : j < p - 1)
    (h : (u * i) % (p - 1) = (u * j) % (p - 1)) : i = j := by
  have hn := F.n_pos
  match hu with
  | ⟨a, _, ha⟩ =>
    have key : ∀ i, i < p - 1 → (a * (u * i)) % (p - 1) = i := by
      intro i hi
      match FRC.Nat.mod_spec (p - 1) hn (a * u) with
      | ⟨q, hq⟩ =>
        rw [ha] at hq
        rw [← FRC.Nat.mul_assoc, hq, FRC.Nat.add_mul, Nat.one_mul, FRC.Nat.mul_assoc,
          FRC.Nat.add_mul_mod_self_left _ _ _ hn, FRC.Nat.mod_eq_of_lt hi]
    rw [← key i hi, ← key j hj, ← FRC.Nat.mul_mod_mod _ _ _ hn, h, FRC.Nat.mul_mod_mod _ _ _ hn]

/-- 2:F5 (Prop. 6.7) — covariance under generator change: for `g' = g^u` (`u` invertible mod `n`) and
`v'_j = v_{u·j mod n}`, `F_{g'}(v')_k = F_g(v)_k`. -/
theorem dft_covariance (F : Frame p κ g) {u : Nat} (hu : Coprime u (p - 1)) (v : Nat → Shell p) (k : Nat) :
    dft (g ^ u) (p - 1) (fun j => v ((u * j) % (p - 1))) k = dft g (p - 1) v k := by
  have hn := F.n_pos
  unfold dft
  have e : ∀ j, v ((u * j) % (p - 1)) * (g ^ u) ^ (j * k) = v ((u * j) % (p - 1)) * g ^ (((u * j) % (p - 1)) * k) := by
    intro j
    rw [← pow_mul, F.pow_mod (u * (j * k)), F.pow_mod (((u * j) % (p - 1)) * k), FRC.Nat.mod_mul_mod _ _ _ hn,
      ← FRC.Nat.mul_assoc]
  rw [sum_congr _ (fun j _ => e j)]
  exact sum_perm (fun l => v l * g ^ (l * k)) (fun j => (u * j) % (p - 1)) (p - 1)
    (fun j _ => Nat.mod_lt _ hn) (fun i j hi hj h => F.mul_mod_inj hu hi hj h)

/-! ### 6:B7 — the eigenspaces of the reversal: `V = V⁺ ⊕ V⁻`, `dim V⁺ = 2κ + 1`, `dim V⁻ = 2κ − 1` -/

/-- `v` is symmetric under the reversal: `v (rev k) = v k` for `k < n`. -/
def Symm (n : Nat) (v : Nat → Shell p) : Prop := ∀ k, k < n → v (rev n k) = v k

/-- `v` is antisymmetric under the reversal: `v (rev k) = −v k` for `k < n`. -/
def Antisymm (n : Nat) (v : Nat → Shell p) : Prop := ∀ k, k < n → v (rev n k) = -(v k)

theorem rev_eq_sub {n k : Nat} (hk : k < n) (hk0 : 0 < k) : rev n k = n - k := rev_of_pos hk hk0

/-- 6:B7 — a symmetric vector is determined by its `2κ + 1` coordinates `v 0, …, v (2κ)`. -/
theorem symm_determined (F : Frame p κ g) {v w : Nat → Shell p} (hv : Symm (p - 1) v) (hw : Symm (p - 1) w)
    (h : ∀ k, k ≤ 2 * κ → v k = w k) : ∀ k, k < p - 1 → v k = w k := by
  intro k hk
  exact match Nat.lt_or_ge k (2 * κ + 1) with
    | Or.inl hlt => h k (Nat.le_of_lt_succ hlt)
    | Or.inr hge =>
      -- k > 2κ: rev k = n − k ≤ 2κ − 1
      have hk0 : 0 < k := Nat.lt_of_lt_of_le (Nat.zero_lt_succ _) hge
      have hr : rev (p - 1) k ≤ 2 * κ := by
        rw [rev_eq_sub hk hk0]
        apply FRC.Nat.sub_le_of_le_add
        rw [← F.four_kappa]
        exact Nat.add_le_add_left (Nat.le_of_lt hge) _
      calc v k = v (rev (p - 1) k) := (hv k hk).symm
        _ = w (rev (p - 1) k) := h _ hr
        _ = w k := hw k hk

/-- 6:B7 — every assignment of the `2κ + 1` coordinates extends to a symmetric vector. -/
theorem symm_extend (F : Frame p κ g) (c : Nat → Shell p) :
    ∃ v : Nat → Shell p, Symm (p - 1) v ∧ ∀ k, k ≤ 2 * κ → v k = c k := by
  refine ⟨fun k => if k ≤ 2 * κ then c k else c (rev (p - 1) k), ?_, fun k hk => by
    show (if k ≤ 2 * κ then c k else c (rev (p - 1) k)) = c k
    rw [if_pos hk]⟩
  intro k hk
  show (if rev (p - 1) k ≤ 2 * κ then c (rev (p - 1) k) else c (rev (p - 1) (rev (p - 1) k)))
      = (if k ≤ 2 * κ then c k else c (rev (p - 1) k))
  rw [rev_rev hk]
  exact match Nat.decLe k (2 * κ), Nat.decLe (rev (p - 1) k) (2 * κ) with
    | isTrue h1, isTrue h2 => by
        rw [if_pos h1, if_pos h2]
        -- both k and n − k are ≤ 2κ: k = 0 (rev 0 = 0) or k = 2κ (rev = 2κ)
        exact match Nat.decEq k 0 with
          | isTrue e => by rw [e, rev_zero _ F.n_pos]
          | isFalse e => by
              have hk0 := Nat.pos_of_ne_zero e
              rw [rev_eq_sub hk hk0] at h2 ⊢
              -- n − k ≤ 2κ and k ≤ 2κ force k = 2κ
              have h3 : p - 1 ≤ 2 * κ + k := FRC.Nat.le_add_of_sub_le (Nat.le_of_lt hk) h2
              rw [← F.four_kappa] at h3
              have hk2 : k = 2 * κ := Nat.le_antisymm h1 (FRC.Nat.le_of_add_le_add_left h3)
              rw [hk2, ← F.four_kappa, FRC.Nat.add_sub_cancel]
    | isTrue h1, isFalse h2 => by rw [if_pos h1, if_neg h2]
    | isFalse h1, isTrue h2 => by rw [if_neg h1, if_pos h2]
    | isFalse h1, isFalse h2 => by
        rw [if_neg h1, if_neg h2]
        -- impossible: k > 2κ and n − k > 2κ would give n > 4κ
        exact absurd (by
          have hk0 : 0 < k := Nat.lt_of_lt_of_le (Nat.zero_lt_succ _) (Nat.lt_of_not_le h1)
          rw [rev_eq_sub hk hk0] at h2
          have a1 := Nat.lt_of_not_le h1
          have a2 := Nat.lt_of_not_le h2
          have := Nat.add_lt_add a1 a2
          rw [FRC.Nat.add_sub_of_le (Nat.le_of_lt hk), F.four_kappa] at this
          exact this) (Nat.lt_irrefl _)

/-- 6:B7 — an antisymmetric vector vanishes at the two fixed points of the reversal, `0` and `2κ`. -/
theorem antisymm_fixed (F : Frame p κ g) {v : Nat → Shell p} (hv : Antisymm (p - 1) v) :
    v 0 = 0 ∧ v (2 * κ) = 0 := by
  have hn := F.n_pos
  have h0 : v 0 = -(v 0) := by rw [← hv 0 hn, rev_zero _ hn]
  have h2 : v (2 * κ) = -(v (2 * κ)) := by
    rw [← hv (2 * κ) F.two_kappa_lt, rev_eq_sub F.two_kappa_lt F.two_kappa_pos, ← F.four_kappa, FRC.Nat.add_sub_cancel]
  exact ⟨F.eq_zero_of_eq_neg h0, F.eq_zero_of_eq_neg h2⟩

/-- 6:B7 — an antisymmetric vector is determined by its `2κ − 1` coordinates `v 1, …, v (2κ − 1)`. -/
theorem antisymm_determined (F : Frame p κ g) {v w : Nat → Shell p} (hv : Antisymm (p - 1) v)
    (hw : Antisymm (p - 1) w) (h : ∀ k, 0 < k → k < 2 * κ → v k = w k) : ∀ k, k < p - 1 → v k = w k := by
  intro k hk
  exact match Nat.decEq k 0 with
    | isTrue e => by rw [e, (F.antisymm_fixed hv).1, (F.antisymm_fixed hw).1]
    | isFalse e0 => match Nat.decEq k (2 * κ) with
      | isTrue e => by rw [e, (F.antisymm_fixed hv).2, (F.antisymm_fixed hw).2]
      | isFalse e2 => match Nat.lt_or_ge k (2 * κ) with
        | Or.inl hlt => h k (Nat.pos_of_ne_zero e0) hlt
        | Or.inr hge =>
          have hgt : 2 * κ < k := Nat.lt_of_le_of_ne hge (fun e => e2 e.symm)
          have hk0 : 0 < k := Nat.lt_of_lt_of_le F.two_kappa_pos hge
          have hr1 : 0 < rev (p - 1) k := by
            rw [rev_eq_sub hk hk0]
            refine Nat.lt_of_add_lt_add_right (n := k) ?_
            rw [Nat.zero_add, FRC.Nat.sub_add_cancel (Nat.le_of_lt hk)]; exact hk
          have hr2 : rev (p - 1) k < 2 * κ := by
            rw [rev_eq_sub hk hk0]
            refine Nat.lt_of_add_lt_add_right (n := k) ?_
            rw [FRC.Nat.sub_add_cancel (Nat.le_of_lt hk), ← F.four_kappa]
            exact Nat.add_lt_add_left hgt _
          calc v k = -(-(v k)) := (neg_neg _).symm
            _ = -(v (rev (p - 1) k)) := by rw [hv k hk]
            _ = -(w (rev (p - 1) k)) := by rw [h _ hr1 hr2]
            _ = -(-(w k)) := by rw [hw k hk]
            _ = w k := neg_neg _

/-- 6:B7 — every assignment of the `2κ − 1` inner coordinates extends to an antisymmetric vector. -/
theorem antisymm_extend (F : Frame p κ g) (c : Nat → Shell p) :
    ∃ v : Nat → Shell p, Antisymm (p - 1) v ∧ ∀ k, 0 < k → k < 2 * κ → v k = c k := by
  refine ⟨fun k => if k = 0 then 0 else if k = 2 * κ then 0 else if k < 2 * κ then c k else -(c (rev (p - 1) k)),
    ?_, fun k hk0 hk2 => by
      show (if k = 0 then 0 else if k = 2 * κ then 0 else if k < 2 * κ then c k else -(c (rev (p - 1) k))) = c k
      rw [if_neg (Nat.ne_of_gt hk0), if_neg (Nat.ne_of_lt hk2), if_pos hk2]⟩
  intro k hk
  have hn := F.n_pos
  show (if rev (p - 1) k = 0 then 0 else if rev (p - 1) k = 2 * κ then 0 else if rev (p - 1) k < 2 * κ then c (rev (p - 1) k) else -(c (rev (p - 1) (rev (p - 1) k))))
      = -(if k = 0 then 0 else if k = 2 * κ then 0 else if k < 2 * κ then c k else -(c (rev (p - 1) k)))
  match Nat.decEq k 0 with
  | isTrue e => rw [e, rev_zero _ hn, if_pos rfl, if_pos rfl, neg_zero]
  | isFalse e0 =>
    have hk0 := Nat.pos_of_ne_zero e0
    have hrk : rev (p - 1) k = p - 1 - k := rev_eq_sub hk hk0
    have hr0 : rev (p - 1) k ≠ 0 := fun h => by
      rw [hrk] at h
      have := FRC.Nat.sub_add_cancel (Nat.le_of_lt hk)
      rw [h, Nat.zero_add] at this
      exact Nat.lt_irrefl _ (this ▸ hk)
    match Nat.decEq k (2 * κ) with
    | isTrue e =>
      have : rev (p - 1) k = 2 * κ := by rw [hrk, e, ← F.four_kappa, FRC.Nat.add_sub_cancel]
      rw [if_neg hr0, if_pos this, if_neg e0, if_pos e, neg_zero]
    | isFalse e2 =>
      have hr2 : rev (p - 1) k ≠ 2 * κ := fun h => e2 (by
        have := rev_rev hk
        rw [h] at this
        rw [← this, rev_eq_sub F.two_kappa_lt F.two_kappa_pos, ← F.four_kappa, FRC.Nat.add_sub_cancel])
      rw [if_neg hr0, if_neg hr2, if_neg e0, if_neg e2]
      match Nat.lt_or_ge k (2 * κ) with
      | Or.inl hlt =>
        have hge : ¬ rev (p - 1) k < 2 * κ := fun h => by
          rw [hrk] at h
          have := Nat.add_lt_add h hlt
          rw [FRC.Nat.sub_add_cancel (Nat.le_of_lt hk), F.four_kappa] at this
          exact Nat.lt_irrefl _ this
        rw [if_neg hge, if_pos hlt, rev_rev hk]
      | Or.inr hge =>
        have hlt' : ¬ k < 2 * κ := Nat.not_lt_of_le hge
        have hgt : 2 * κ < k := Nat.lt_of_le_of_ne hge (fun e => e2 e.symm)
        have hr : rev (p - 1) k < 2 * κ := by
          rw [hrk]
          refine Nat.lt_of_add_lt_add_right (n := k) ?_
          rw [FRC.Nat.sub_add_cancel (Nat.le_of_lt hk), ← F.four_kappa]
          exact Nat.add_lt_add_left hgt _
        rw [if_pos hr, if_neg hlt', neg_neg]

/-- 6:B7 — the decomposition `V = V⁺ ⊕ V⁻`: with `h = 2⁻¹`, `v = v⁺ + v⁻` where `v⁺ k = h(v k + v (rev k))`
is symmetric and `v⁻ k = h(v k − v (rev k))` antisymmetric; the decomposition is unique. -/
theorem symm_antisymm_decomp (F : Frame p κ g) (v : Nat → Shell p) :
    ∃ vp vm : Nat → Shell p, Symm (p - 1) vp ∧ Antisymm (p - 1) vm ∧ ∀ k, k < p - 1 → v k = vp k + vm k := by
  match F.exists_inv F.two_ne_zero with
  | ⟨h, hh⟩ =>
    refine ⟨fun k => h * (v k + v (rev (p - 1) k)), fun k => h * (v k + -(v (rev (p - 1) k))), ?_, ?_, ?_⟩
    · intro k hk; show h * (v (rev (p - 1) k) + v (rev (p - 1) (rev (p - 1) k))) = h * (v k + v (rev (p - 1) k))
      rw [rev_rev hk, add_comm]
    · intro k hk; show h * (v (rev (p - 1) k) + -(v (rev (p - 1) (rev (p - 1) k)))) = -(h * (v k + -(v (rev (p - 1) k))))
      rw [rev_rev hk, mul_neg, neg_add_rev, neg_neg, add_comm]
    · intro k _
      show v k = h * (v k + v (rev (p - 1) k)) + h * (v k + -(v (rev (p - 1) k)))
      rw [← left_distrib, add_add_add_comm, add_neg, add_zero, ← two_mul', ← mul_assoc, mul_comm h, hh, one_mul]

/-- 6:B7 — the decomposition is unique: a vector that is both symmetric and antisymmetric is zero, so the
symmetric and antisymmetric parts of `v` are determined. -/
theorem symm_antisymm_unique (F : Frame p κ g) {a b : Nat → Shell p} (ha : Symm (p - 1) a) (hb : Antisymm (p - 1) b)
    (h : ∀ k, k < p - 1 → a k + b k = 0) : ∀ k, k < p - 1 → a k = 0 ∧ b k = 0 := by
  intro k hk
  have h1 := h k hk
  have h2 := h (rev (p - 1) k) (rev_lt F.n_pos k)
  rw [ha k hk, hb k hk] at h2
  -- a k + b k = 0 and a k − b k = 0 give 2 a k = 0
  have ha0 : a k = 0 := F.no_south_pole _ (by
    rw [two_mul']
    calc a k + a k = (a k + b k) + (a k + -(b k)) := by
          rw [add_add_add_comm, add_neg, add_zero]
      _ = 0 := by rw [h1, h2, add_zero])
  refine ⟨ha0, ?_⟩
  rw [ha0, zero_add] at h1; exact h1

end Frame

end Shell
end FRC

/-! inlined: FrcCore/Algebra.lean -/

/-!
# FrcCore.Algebra — 1-algebra rows on the core

1:B2 (the quarter-turn exists; the fourth roots of unity are exactly `{1, i, −1, −i}`; the Klein orbits
`{x, −x, x⁻¹, −x⁻¹}` have four elements off them), 1:B4 (the affine unit), 1:C4 (the meridian involution),
1:D2 (the window law), 1:D4 (scale periodicity), 1:D5 (the range obstruction at `(13, 2)`), 1:E2 (the complex
chart has a zero divisor), 1:F1 (no south pole). No axioms.
-/

namespace FRC
namespace Shell
namespace Frame

variable {p : Nat} [Pos p] {κ : Nat} {g : Shell p}

/-- 1:B2 (Theorem 1 of 1-algebra), 2:D7 — off the fourth roots of unity, `x`, `−x`, `x⁻¹`, `−x⁻¹` are four
distinct residues (`y` stands for the inverse: `x·y = 1`). -/
theorem klein_orbit_four (F : Frame p κ g) {x y : Shell p} (hxy : x * y = 1) (h4 : x ^ 4 ≠ 1) :
    x ≠ -x ∧ x ≠ y ∧ x ≠ -y ∧ -x ≠ y ∧ -x ≠ -y ∧ y ≠ -y := by
  have hx0 : x ≠ 0 := fun h => F.one_ne_zero (by rw [← hxy, h, zero_mul])
  have hy0 : y ≠ 0 := fun h => F.one_ne_zero (by rw [← hxy, h, mul_zero])
  have h4' : x ^ 4 = (x * x) * (x * x) := by
    rw [show (4 : Nat) = 2 * 2 from rfl, pow_mul, pow_two, pow_two]
  have hsq : x * x ≠ 1 := fun h => h4 (by rw [h4', h, one_mul])
  have hsqn : x * x ≠ -1 := fun h => h4 (by rw [h4', h, neg_mul_neg, one_mul])
  have hxy' : x = y → False := fun e => hsq (by rw [← hxy, e])
  have hxny : x = -y → False := fun e => hsqn (by
    have : x * x = x * -y := by rw [← e]
    rw [this, ← mul_neg, hxy])
  refine ⟨fun h => hx0 (F.eq_zero_of_eq_neg h), hxy', hxny, ?_, ?_, ?_⟩
  · intro h; exact hxny (by rw [← neg_neg x, h])
  · intro h; exact hxy' (by rw [← neg_neg x, h, neg_neg])
  · intro h; exact hy0 (F.eq_zero_of_eq_neg h)

/-- 1:D4 (Lemma 2 of 1-algebra, scale periodicity) — the residue grid repeats with the period `p − 1`
of the drive: `g^{n + (p−1)} = g^n`, hence `x·g^{n + (p−1)} = x·g^n` for every `x`. -/
theorem scale_periodic (F : Frame p κ g) (x : Shell p) (n : Nat) :
    x * g ^ (n + (p - 1)) = x * g ^ n := by
  rw [pow_add, F.pow_n, mul_one]

/-- The affine frame `(a, b)` of 1-algebra (Definition 2): the transported product
`x ⊗ z := a + b·((x − a)/b)·((z − a)/b)`, written with `y` the inverse of `b`. -/
def affineMul (a b y x z : Shell p) : Shell p := a + b * ((x + -a) * y) * ((z + -a) * y)

/-- 1:B4 (Definition 2 of 1-algebra) — in the affine frame `(a, b)` the multiplicative unit
is `a + b`, not `b`: `(a + b) ⊗ z = z` for every `z`. -/
theorem affine_frame_unit {a b y : Shell p} (hby : b * y = 1) (z : Shell p) :
    affineMul a b y (a + b) z = z := by
  unfold affineMul
  have e1 : a + b + -a = b := by rw [add_comm a b, add_assoc, add_neg, add_zero]
  rw [e1, hby, mul_one, mul_left_comm b, hby, mul_one, add_comm z (-a), ← add_assoc, add_neg, zero_add]

/-- 1:D2 (the window law, injectivity) — two window integers `x, y ≤ H` with `2H < p` that read as the same
residue are equal: `ofNat x = ofNat y → x = y`. (Both are below `p`, so the residues are the integers.) -/
theorem window_injective {H x y : Nat} (hH : 2 * H < p) (hx : x ≤ H) (hy : y ≤ H)
    (h : (ofNat x : Shell p) = ofNat y) : x = y := by
  have hxp : x < p := Nat.lt_of_le_of_lt hx (Nat.lt_of_le_of_lt (Nat.le_add_left H H) (Nat.two_mul H ▸ hH))
  have hyp : y < p := Nat.lt_of_le_of_lt hy (Nat.lt_of_le_of_lt (Nat.le_add_left H H) (Nat.two_mul H ▸ hH))
  have := val_injective h
  rw [val_ofNat, val_ofNat, FRC.Nat.mod_eq_of_lt hxp, FRC.Nat.mod_eq_of_lt hyp] at this
  exact this

theorem ofNat_add (x y : Nat) : (ofNat x : Shell p) + ofNat y = ofNat (x + y) :=
  ext (by rw [val_add, val_ofNat, val_ofNat, val_ofNat, FRC.Nat.mod_add_mod _ _ _ hp, FRC.Nat.add_mod_mod _ _ _ hp])

theorem ofNat_mul (x y : Nat) : (ofNat x : Shell p) * ofNat y = ofNat (x * y) :=
  ext (by rw [val_mul, val_ofNat, val_ofNat, val_ofNat, FRC.Nat.mod_mul_mod _ _ _ hp, FRC.Nat.mul_mod_mod _ _ _ hp])

/-- 1:D2, the read-back of sums: for `x, y ≤ H` and `4H < p`, the residue of `x + y` determines the integer
`x + y` among the integers `z ≤ 2H`. -/
theorem window_add_readback {H x y z : Nat} (hH : 2 * (2 * H) < p) (hx : x ≤ H) (hy : y ≤ H) (hz : z ≤ 2 * H)
    (h : (ofNat x : Shell p) + ofNat y = ofNat z) : x + y = z := by
  rw [ofNat_add] at h
  exact window_injective hH (by rw [Nat.two_mul]; exact Nat.add_le_add hx hy) hz h

/-- 1:D2, the read-back of products: for `x, y ≤ H` and `2H² < p`, the residue of `x·y` determines the integer
`x·y` among the integers `z ≤ H²`. -/
theorem window_mul_readback {H x y z : Nat} (hH : 2 * (H * H) < p) (hx : x ≤ H) (hy : y ≤ H) (hz : z ≤ H * H)
    (h : (ofNat x : Shell p) * ofNat y = ofNat z) : x * y = z := by
  rw [ofNat_mul] at h
  exact window_injective hH (Nat.mul_le_mul hx hy) hz h

/-- 1:D2, the signed window: `x` and `−y` (`x, y ≤ H`, `2H < p`) read as the same residue only when both
are zero — the window's positive and negative halves do not overlap. -/
theorem window_signed {H x y : Nat} (hH : 2 * H < p) (hx : x ≤ H) (hy : y ≤ H)
    (h : (ofNat x : Shell p) = -(ofNat y)) : x = 0 ∧ y = 0 := by
  have hxp : x < p := Nat.lt_of_le_of_lt hx (Nat.lt_of_le_of_lt (Nat.le_add_left H H) (Nat.two_mul H ▸ hH))
  have hyp : y < p := Nat.lt_of_le_of_lt hy (Nat.lt_of_le_of_lt (Nat.le_add_left H H) (Nat.two_mul H ▸ hH))
  have hv := val_injective h
  rw [val_ofNat, val_neg, val_ofNat, FRC.Nat.mod_eq_of_lt hxp, FRC.Nat.mod_eq_of_lt hyp] at hv
  -- hv : x = (p - y) % p
  match Nat.decEq y 0 with
  | .isTrue hy0 =>
    rw [hy0, Nat.sub_zero, FRC.Nat.mod_self p hp] at hv
    exact ⟨hv, hy0⟩
  | .isFalse hy0 =>
    have hpy : p - y < p := Nat.sub_lt hp (Nat.pos_of_ne_zero hy0)
    rw [FRC.Nat.mod_eq_of_lt hpy] at hv
    -- x = p − y with x ≤ H, y ≤ H gives p = x + y ≤ 2H < p
    have : p = x + y := by rw [hv, FRC.Nat.sub_add_cancel (Nat.le_of_lt hyp)]
    have hle : x + y ≤ 2 * H := by rw [Nat.two_mul]; exact Nat.add_le_add hx hy
    exact absurd (Nat.lt_of_le_of_lt (this ▸ hle) hH) (Nat.lt_irrefl p)

/-- 1:B2 (Theorem 1, existence clause) — a quarter-turn `u` with `u² = −1` exists on every shell. -/
theorem quarter_turn_exists (F : Frame p κ g) : ∃ u : Shell p, u * u = -1 :=
  ⟨quarterTurn g κ, F.quarter_turn_sq⟩

/-- 1:B2 (Theorem 1, the structural set) — the fourth roots of unity are exactly `1, −1, i, −i`. -/
theorem fourth_roots (F : Frame p κ g) (x : Shell p) :
    x ^ 4 = 1 ↔ x = 1 ∨ x = -1 ∨ x = quarterTurn g κ ∨ x = -(quarterTurn g κ) := by
  have h4 : x ^ 4 = (x * x) * (x * x) := by
    rw [show (4 : Nat) = 2 * 2 from rfl, pow_mul, pow_two, pow_two]
  have hi := F.quarter_turn_sq
  constructor
  · intro h
    rw [h4] at h
    match F.sq_eq_one h with
    | .inl e => match F.sq_eq_one e with
      | .inl e1 => exact .inl e1
      | .inr e1 => exact .inr (.inl e1)
    | .inr e =>
      -- x² = −1 = i²: (x + −i)(x + i) = 0
      have e2 : (x + -(quarterTurn g κ)) * (x + quarterTurn g κ) = 0 := by
        rw [right_distrib, left_distrib, left_distrib, e, ← neg_mul, ← neg_mul, hi, neg_neg, mul_comm (quarterTurn g κ) x]
        rw [add_assoc, ← add_assoc (x * quarterTurn g κ), add_neg, zero_add, neg_add]
      match F.mul_eq_zero e2 with
      | .inl e3 => exact .inr (.inr (.inl (by
          calc x = x + 0 := (add_zero x).symm
            _ = x + (-(quarterTurn g κ) + quarterTurn g κ) := by rw [neg_add]
            _ = (x + -(quarterTurn g κ)) + quarterTurn g κ := (add_assoc _ _ _).symm
            _ = quarterTurn g κ := by rw [e3, zero_add])))
      | .inr e3 => exact .inr (.inr (.inr (eq_neg_of_add_eq_zero e3)))
  · intro h
    match h with
    | .inl e => rw [e, one_pow]
    | .inr (.inl e) => rw [h4, e, neg_mul_neg, one_mul, one_mul]
    | .inr (.inr (.inl e)) => rw [h4, e, hi, neg_mul_neg, one_mul]
    | .inr (.inr (.inr e)) => rw [h4, e, neg_mul_neg, hi, neg_mul_neg, one_mul]

/-- 1:C4 (Definition 5 (a)) — the meridian involution: `(−a)·g^{n + 2κ} = a·g^n`. -/
theorem meridian_involution (F : Frame p κ g) (a : Shell p) (n : Nat) :
    -a * g ^ (n + 2 * κ) = a * g ^ n := by
  rw [pow_add, F.half_period, mul_comm (g ^ n), ← mul_assoc, neg_mul_neg, mul_one]

/-- The complex chart: pairs `(a, b)` read as `a + b·X` with `X² = −1`, multiplied as
`(a, b)(c, d) = (ac − bd, ad + bc)`. -/
def cmul (x y : Shell p × Shell p) : Shell p × Shell p :=
  (x.1 * y.1 + -(x.2 * y.2), x.1 * y.2 + x.2 * y.1)

/-- 1:E2 (Proposition 5 reversed) — on a shell that already has a square root of `−1` the complex chart is
not a field: `(i, 1)·(−i, 1) = (0, 0)` with both factors nonzero (`X + i` and `X − i` are zero divisors). -/
theorem complex_chart_zero_divisor (F : Frame p κ g) :
    cmul (quarterTurn g κ, (1 : Shell p)) (-(quarterTurn g κ), 1) = (0, 0) ∧
    (quarterTurn g κ, (1 : Shell p)) ≠ (0, 0) ∧ (-(quarterTurn g κ), (1 : Shell p)) ≠ (0, 0) := by
  refine ⟨?_, fun h => F.one_ne_zero (congrArg Prod.snd h), fun h => F.one_ne_zero (congrArg Prod.snd h)⟩
  unfold cmul
  show (quarterTurn g κ * -(quarterTurn g κ) + -(1 * 1), quarterTurn g κ * 1 + 1 * -(quarterTurn g κ)) = (0, 0)
  rw [← mul_neg, F.quarter_turn_sq, neg_neg, one_mul, add_neg, mul_one, one_mul, add_neg]

/-- 1:D5, the range obstruction at `p = 13`, `g = 2`: every grid point
`x / 2^n` with `x < 13` and `n ≥ 3` is at most `3/2` — as the integer statement `2x ≤ 3·2^n`. -/
theorem approx_obstruction (n x : Nat) (hn : 3 ≤ n) (hx : x < 13) : 2 * x ≤ 3 * 2 ^ n := by
  have h8 : 2 ^ 3 ≤ 2 ^ n := Nat.pow_le_pow_right (Nat.zero_lt_succ 1) hn
  have h1 : 2 * x ≤ 2 * 12 := Nat.mul_le_mul_left 2 (Nat.le_of_lt_succ hx)
  have h2 : 3 * 2 ^ 3 ≤ 3 * 2 ^ n := Nat.mul_le_mul_left 3 h8
  exact Nat.le_trans h1 h2

/-! ### 1:B2, the count: the Klein orbits off `Q₄` are exactly `κ − 1`, represented by `g^r`, `1 ≤ r < κ` -/

/-- `y` lies in the Klein orbit of `x`: `y ∈ {x, −x, x⁻¹, −x⁻¹}` (the inverse written as `x·y = 1`). -/
def InOrbit (x y : Shell p) : Prop := y = x ∨ y = -x ∨ x * y = 1 ∨ x * -y = 1

theorem two_mul_eq (κ : Nat) : 2 * κ = κ + κ := Nat.two_mul κ
theorem three_mul_eq (κ : Nat) : 3 * κ = κ + κ + κ := by rw [Nat.succ_mul, Nat.two_mul]
theorem four_mul_eq (κ : Nat) : 4 * κ = κ + κ + κ + κ := by rw [Nat.succ_mul, three_mul_eq]

/-- The exponent `m` of `x = g^m` reduced to its orbit representative in `[1, κ)`. -/
theorem orbit_rep_of_exp (F : Frame p κ g) {m : Nat} (hm : m < p - 1) (h0 : m ≠ 0) (h1 : m ≠ κ)
    (h2 : m ≠ 2 * κ) (h3 : m ≠ 3 * κ) :
    ∃ r, 1 ≤ r ∧ r < κ ∧ InOrbit (g ^ r) (g ^ m) := by
  have hn := F.n_eq
  have hπ := F.half_period
  rw [hn, four_mul_eq] at hm
  rw [two_mul_eq] at h2 hπ
  rw [three_mul_eq] at h3
  match Nat.lt_or_ge m κ with
  | Or.inl hlt => exact ⟨m, Nat.pos_of_ne_zero h0, hlt, Or.inl rfl⟩
  | Or.inr hge1 => match Nat.lt_or_ge m (κ + κ) with
    | Or.inl hlt =>
      -- κ < m < 2κ: r = 2κ − m, and g^m · (−g^r) = −g^{2κ} = 1
      have hgt : κ < m := Nat.lt_of_le_of_ne hge1 (fun e => h1 e.symm)
      refine ⟨κ + κ - m, ?_, ?_, Or.inr (Or.inr (Or.inr ?_))⟩
      · refine Nat.lt_of_add_lt_add_right (n := m) ?_
        rw [Nat.zero_add, FRC.Nat.sub_add_cancel (Nat.le_of_lt hlt)]; exact hlt
      · refine Nat.lt_of_add_lt_add_right (n := m) ?_
        rw [FRC.Nat.sub_add_cancel (Nat.le_of_lt hlt)]; exact Nat.add_lt_add_left hgt κ
      · rw [← mul_neg, ← pow_add, FRC.Nat.sub_add_cancel (Nat.le_of_lt hlt), hπ, neg_neg]
    | Or.inr hge2 => match Nat.lt_or_ge m (κ + κ + κ) with
      | Or.inl hlt =>
        -- 2κ < m < 3κ: r = m − 2κ, and g^m = −g^r
        have hgt : κ + κ < m := Nat.lt_of_le_of_ne hge2 (fun e => h2 e.symm)
        refine ⟨m - (κ + κ), ?_, ?_, Or.inr (Or.inl ?_)⟩
        · refine Nat.lt_of_add_lt_add_right (n := κ + κ) ?_
          rw [Nat.zero_add, FRC.Nat.sub_add_cancel hge2]; exact hgt
        · refine Nat.lt_of_add_lt_add_right (n := κ + κ) ?_
          rw [FRC.Nat.sub_add_cancel hge2, Nat.add_comm κ (κ + κ)]; exact hlt
        · have : m = κ + κ + (m - (κ + κ)) := (FRC.Nat.add_sub_of_le hge2).symm
          rw [this, pow_add, hπ, neg_one_mul, FRC.Nat.add_sub_cancel_left]
      | Or.inr hge3 =>
        -- 3κ < m < 4κ: r = 4κ − m, and g^m · g^r = g^{4κ} = 1
        have hgt : κ + κ + κ < m := Nat.lt_of_le_of_ne hge3 (fun e => h3 e.symm)
        refine ⟨κ + κ + κ + κ - m, ?_, ?_, Or.inr (Or.inr (Or.inl ?_))⟩
        · refine Nat.lt_of_add_lt_add_right (n := m) ?_
          rw [Nat.zero_add, FRC.Nat.sub_add_cancel (Nat.le_of_lt hm)]; exact hm
        · refine Nat.lt_of_add_lt_add_right (n := m) ?_
          rw [FRC.Nat.sub_add_cancel (Nat.le_of_lt hm), Nat.add_comm κ m]
          exact Nat.add_lt_add_right hgt κ
        · rw [← pow_add, FRC.Nat.sub_add_cancel (Nat.le_of_lt hm), ← four_mul_eq, ← hn, F.pow_n]

/-- Off the fourth roots of unity, `x = g^m` has `m ∉ {0, κ, 2κ, 3κ}`. -/
theorem exp_not_fourth (F : Frame p κ g) {m : Nat} (h4 : (g ^ m) ^ 4 ≠ 1) :
    m ≠ 0 ∧ m ≠ κ ∧ m ≠ 2 * κ ∧ m ≠ 3 * κ := by
  have hi := (F.quarter_turn_order).2
  refine ⟨fun e => h4 (by rw [e, pow_zero, one_pow]), fun e => h4 (by rw [e, hi]), fun e => h4 ?_, fun e => h4 ?_⟩
  · rw [e, Nat.mul_comm 2 κ, pow_mul, ← pow_mul, show (2 : Nat) * 4 = 4 * 2 from rfl, pow_mul, hi, one_pow]
  · rw [e, Nat.mul_comm 3 κ, pow_mul, ← pow_mul, show (3 : Nat) * 4 = 4 * 3 from rfl, pow_mul, hi, one_pow]

/-- 1:B2 (Theorem 1, the count, existence), 2:D7 — every residue off `Q₄` lies in the Klein orbit of some `g^r`
with `1 ≤ r < κ`. -/
theorem orbit_rep (F : Frame p κ g) {x : Shell p} (hx : x ≠ 0) (h4 : x ^ 4 ≠ 1) :
    ∃ r, 1 ≤ r ∧ r < κ ∧ InOrbit (g ^ r) x := by
  match F.eq_pow_of_ne_zero hx with
  | ⟨m, hm, e⟩ =>
    rw [← e] at h4 ⊢
    match F.exp_not_fourth h4 with
    | ⟨h0, h1, h2, h3⟩ => exact F.orbit_rep_of_exp hm h0 h1 h2 h3

theorem neg_mul_of_mul_neg {a b : Shell p} (e : a * -b = 1) : -a * b = 1 := by
  rw [← neg_mul, mul_neg]; exact e

/-- The orbit relation is symmetric. -/
theorem inOrbit_symm {a b : Shell p} (h : InOrbit a b) : InOrbit b a :=
  match h with
  | Or.inl e => Or.inl e.symm
  | Or.inr (Or.inl e) => Or.inr (Or.inl (by rw [e, neg_neg]))
  | Or.inr (Or.inr (Or.inl e)) => Or.inr (Or.inr (Or.inl (by rw [mul_comm]; exact e)))
  | Or.inr (Or.inr (Or.inr e)) => Or.inr (Or.inr (Or.inr (by rw [← mul_neg, mul_comm, mul_neg]; exact e)))

theorem neg_eq_neg {a b : Shell p} (h : -a = -b) : a = b := by rw [← neg_neg a, h, neg_neg]

/-- The orbit relation is transitive. -/
theorem inOrbit_trans {a b c : Shell p} (h1 : InOrbit a b) (h2 : InOrbit b c) : InOrbit a c := by
  have hab : b = a ∨ b = -a ∨ a * b = 1 ∨ a * -b = 1 := h1
  have hbc : c = b ∨ c = -b ∨ b * c = 1 ∨ b * -c = 1 := h2
  unfold InOrbit
  match hab, hbc with
  | Or.inl e, h => exact e ▸ h
  | Or.inr (Or.inl e), Or.inl e' => exact Or.inr (Or.inl (e' ▸ e))
  | Or.inr (Or.inl e), Or.inr (Or.inl e') => exact Or.inl (by rw [e', e, neg_neg])
  | Or.inr (Or.inl e), Or.inr (Or.inr (Or.inl e')) => exact Or.inr (Or.inr (Or.inr (by rw [← mul_neg, neg_mul, ← e]; exact e')))
  | Or.inr (Or.inl e), Or.inr (Or.inr (Or.inr e')) => exact Or.inr (Or.inr (Or.inl (by rw [← neg_mul_neg, ← e]; exact e')))
  | Or.inr (Or.inr (Or.inl e)), Or.inl e' => exact Or.inr (Or.inr (Or.inl (e' ▸ e)))
  | Or.inr (Or.inr (Or.inl e)), Or.inr (Or.inl e') => exact Or.inr (Or.inr (Or.inr (by rw [e', neg_neg]; exact e)))
  | Or.inr (Or.inr (Or.inl e)), Or.inr (Or.inr (Or.inl e')) =>
    exact Or.inl (inv_unique (x := c) (x' := a) (y := b) (by rw [mul_comm]; exact e') e)
  | Or.inr (Or.inr (Or.inl e)), Or.inr (Or.inr (Or.inr e')) =>
    exact Or.inr (Or.inl (by
      have := inv_unique (x := -c) (x' := a) (y := b) (by rw [mul_comm]; exact e') e
      rw [← this, neg_neg]))
  | Or.inr (Or.inr (Or.inr e)), Or.inl e' => exact Or.inr (Or.inr (Or.inr (e' ▸ e)))
  | Or.inr (Or.inr (Or.inr e)), Or.inr (Or.inl e') => exact Or.inr (Or.inr (Or.inl (by rw [e']; exact e)))
  | Or.inr (Or.inr (Or.inr e)), Or.inr (Or.inr (Or.inl e')) =>
    exact Or.inr (Or.inl (inv_unique (x := -a) (x' := c) (y := b) (neg_mul_of_mul_neg e) (by rw [mul_comm]; exact e')).symm)
  | Or.inr (Or.inr (Or.inr e)), Or.inr (Or.inr (Or.inr e')) =>
    exact Or.inl (neg_eq_neg (inv_unique (x := -a) (x' := -c) (y := b) (neg_mul_of_mul_neg e) (by rw [mul_comm]; exact e'))).symm

/-- The exponents of the orbit of `g^r`: `g^s ∈ orbit(g^r)`, `s < n`, forces `s ∈ {r, r + 2κ, 4κ − r, 2κ − r}`
(for `1 ≤ r < κ`). -/
theorem orbit_exponent (F : Frame p κ g) {r s : Nat} (hr1 : 1 ≤ r) (hrκ : r < κ) (hs : s < p - 1)
    (h : InOrbit (g ^ r) (g ^ s)) : s = r ∨ s = r + (κ + κ) ∨ s = κ + κ + κ + κ - r ∨ s = κ + κ - r := by
  have hn := F.n_eq
  have hπ := F.half_period
  rw [two_mul_eq] at hπ
  rw [hn, four_mul_eq] at hs
  have hr2 : r < κ + κ := Nat.lt_of_lt_of_le hrκ (Nat.le_add_right κ κ)
  have hr4 : r < κ + κ + κ + κ := Nat.lt_of_lt_of_le hr2 (Nat.le_trans (Nat.le_add_right _ κ) (Nat.le_add_right _ κ))
  have hpow_inj : ∀ {i j : Nat}, i < κ + κ + κ + κ → j < κ + κ + κ + κ → g ^ i = g ^ j → i = j :=
    fun hi hj e => F.pow_inj (by rw [hn, four_mul_eq]; exact hi) (by rw [hn, four_mul_eq]; exact hj) e
  have hpn : g ^ (κ + κ + κ + κ) = 1 := by rw [← four_mul_eq, ← hn]; exact F.pow_n
  match h with
  | Or.inl e => exact Or.inl (hpow_inj hs hr4 e)
  | Or.inr (Or.inl e) =>
    have e' : g ^ s = g ^ (r + (κ + κ)) := by rw [e, pow_add, hπ, mul_comm, neg_one_mul]
    have hlt : r + (κ + κ) < κ + κ + κ + κ := by
      rw [show κ + κ + κ + κ = (κ + κ) + (κ + κ) by rw [Nat.add_assoc]]
      exact Nat.add_lt_add_right hr2 _
    exact Or.inr (Or.inl (hpow_inj hs hlt e'))
  | Or.inr (Or.inr (Or.inl e)) =>
    have hlt : κ + κ + κ + κ - r < κ + κ + κ + κ := Nat.sub_lt (Nat.lt_of_lt_of_le (Nat.zero_lt_succ 0) (Nat.le_trans hr1 (Nat.le_of_lt hr4))) hr1
    have e2 : g ^ r * g ^ (κ + κ + κ + κ - r) = 1 := by rw [← pow_add, FRC.Nat.add_sub_of_le (Nat.le_of_lt hr4), hpn]
    have e' : g ^ s = g ^ (κ + κ + κ + κ - r) := F.mul_left_cancel (F.pow_ne_zero r) (e.trans e2.symm)
    exact Or.inr (Or.inr (Or.inl (hpow_inj hs hlt e')))
  | Or.inr (Or.inr (Or.inr e)) =>
    have hlt : κ + κ - r < κ + κ + κ + κ := Nat.lt_of_le_of_lt (Nat.sub_le _ _)
      (Nat.lt_of_lt_of_le (Nat.lt_add_of_pos_right F.cap_pos) (Nat.le_add_right _ κ))
    have e2 : g ^ r * -(g ^ (κ + κ - r)) = 1 := by
      rw [← mul_neg, ← pow_add, FRC.Nat.add_sub_of_le (Nat.le_of_lt hr2), hπ, neg_neg]
    have e' : -(g ^ s) = -(g ^ (κ + κ - r)) := F.mul_left_cancel (F.pow_ne_zero r) (e.trans e2.symm)
    exact Or.inr (Or.inr (Or.inr (hpow_inj hs hlt (neg_eq_neg e'))))

/-- 1:B2 (Theorem 1, the count, uniqueness), 2:D7 — two representatives `g^r`, `g^{r'}` with `1 ≤ r, r' < κ` whose
orbits meet are the same: the Klein orbits off `Q₄` are exactly `κ − 1`, one for each `r ∈ [1, κ)`. -/
theorem orbit_rep_unique (F : Frame p κ g) {r r' : Nat} (hr1 : 1 ≤ r) (hrκ : r < κ) (_hr1' : 1 ≤ r')
    (hrκ' : r' < κ) {x : Shell p} (hx : InOrbit (g ^ r) x) (hx' : InOrbit (g ^ r') x) : r = r' := by
  have hn := F.n_eq
  have hr' : r' < p - 1 := by
    rw [hn, four_mul_eq]
    exact Nat.lt_of_lt_of_le hrκ' (Nat.le_trans (Nat.le_add_right κ κ) (Nat.le_trans (Nat.le_add_right _ κ) (Nat.le_add_right _ κ)))
  have h := inOrbit_trans hx (inOrbit_symm hx')
  match F.orbit_exponent hr1 hrκ hr' h with
  | Or.inl e => exact e.symm
  | Or.inr (Or.inl e) =>
    exact absurd hrκ' (Nat.not_lt_of_le (by rw [e]; exact Nat.le_trans (Nat.le_add_right κ κ) (Nat.le_add_left _ r)))
  | Or.inr (Or.inr (Or.inl e)) =>
    -- 4κ − r > κ since r < κ
    have : κ ≤ κ + κ + κ + κ - r := by
      apply FRC.Nat.le_sub_of_add_le
      rw [Nat.add_assoc, Nat.add_assoc]
      exact Nat.add_le_add_left (Nat.le_trans (Nat.le_of_lt hrκ) (Nat.le_add_right κ _)) κ
    exact absurd hrκ' (Nat.not_lt_of_le (e ▸ this))
  | Or.inr (Or.inr (Or.inr e)) =>
    -- 2κ − r > κ since r < κ
    have : κ ≤ κ + κ - r := by
      apply FRC.Nat.le_sub_of_add_le
      exact Nat.add_le_add_left (Nat.le_of_lt hrκ) κ
    exact absurd hrκ' (Nat.not_lt_of_le (e ▸ this))

/-! ### 1:C2 — the frame group: the affine maps `x ↦ a + b·x`, `b ≠ 0`, act simply transitively on the frames -/

/-- An affine map of the shell, `x ↦ a + b·x` with `b ≠ 0`. -/
structure Affine (p : Nat) [Pos p] where
  a : Shell p
  b : Shell p
  hb : b ≠ 0

namespace Affine

def apply (φ : Affine p) (x : Shell p) : Shell p := φ.a + φ.b * x

theorem ext' {φ ψ : Affine p} (ha : φ.a = ψ.a) (hb : φ.b = ψ.b) : φ = ψ := by
  cases φ; cases ψ; cases ha; cases hb; rfl

/-- The identity `x ↦ 0 + 1·x`. -/
def one (F : Frame p κ g) : Affine p := ⟨0, 1, F.one_ne_zero⟩

/-- Composition: `(a, b) ∘ (c, d) = (a + b·c, b·d)`. -/
def comp (F : Frame p κ g) (φ ψ : Affine p) : Affine p := ⟨φ.a + φ.b * ψ.a, φ.b * ψ.b, F.mul_ne_zero φ.hb ψ.hb⟩

theorem comp_apply (F : Frame p κ g) (φ ψ : Affine p) (x : Shell p) :
    (comp F φ ψ).apply x = φ.apply (ψ.apply x) := by
  unfold comp apply
  show φ.a + φ.b * ψ.a + φ.b * ψ.b * x = φ.a + φ.b * (ψ.a + ψ.b * x)
  rw [left_distrib, add_assoc, mul_assoc]

theorem one_apply (F : Frame p κ g) (x : Shell p) : (one F).apply x = x := by
  unfold one apply; show 0 + 1 * x = x; rw [one_mul, zero_add]

theorem comp_assoc (F : Frame p κ g) (φ ψ χ : Affine p) : comp F (comp F φ ψ) χ = comp F φ (comp F ψ χ) :=
  ext' (by show φ.a + φ.b * ψ.a + φ.b * ψ.b * χ.a = φ.a + φ.b * (ψ.a + ψ.b * χ.a); rw [left_distrib, add_assoc, mul_assoc])
    (by show φ.b * ψ.b * χ.b = φ.b * (ψ.b * χ.b); exact mul_assoc _ _ _)

/-- The inverse of `(a, b)`: `(−a·b⁻¹, b⁻¹)`, with `y` the inverse of `b`. -/
def inv (F : Frame p κ g) (φ : Affine p) (y : Shell p) (hy : φ.b * y = 1) : Affine p :=
  ⟨-(φ.a * y), y, fun h => F.one_ne_zero (by rw [← hy, h, mul_zero])⟩

theorem comp_inv (F : Frame p κ g) (φ : Affine p) (y : Shell p) (hy : φ.b * y = 1) :
    comp F φ (inv F φ y hy) = one F :=
  ext' (by
      show φ.a + φ.b * -(φ.a * y) = 0
      calc φ.a + φ.b * -(φ.a * y) = φ.a + -(φ.b * (φ.a * y)) := by rw [← mul_neg]
        _ = φ.a + -(φ.a * (φ.b * y)) := by rw [mul_left_comm]
        _ = φ.a + -φ.a := by rw [hy, mul_one]
        _ = 0 := add_neg _)
    (by show φ.b * y = 1; exact hy)

/-- 1:C2 (Prop. of the frame group), simple transitivity — for frames `(a, b)` and `(c, d)` (`b, d ≠ 0`) there
is exactly one affine map carrying the first to the second: `φ (a, b) := (φ.apply a, φ.b · b)`. -/
theorem simply_transitive (F : Frame p κ g) (a b c d : Shell p) (hb : b ≠ 0) (hd : d ≠ 0) :
    (∃ φ : Affine p, φ.apply a = c ∧ φ.b * b = d) ∧
    (∀ φ ψ : Affine p, φ.apply a = c → φ.b * b = d → ψ.apply a = c → ψ.b * b = d → φ = ψ) := by
  match F.exists_inv hb with
  | ⟨y, hy⟩ =>
    constructor
    · refine ⟨⟨c + -(d * y * a), d * y, ?_⟩, ?_, ?_⟩
      · exact F.mul_ne_zero hd (fun h => F.one_ne_zero (by rw [← hy, h, mul_zero]))
      · show c + -(d * y * a) + d * y * a = c
        rw [add_assoc, neg_add, add_zero]
      · show d * y * b = d
        rw [mul_assoc, mul_comm y b, hy, mul_one]
    · intro φ ψ h1 h2 h3 h4
      have eb : φ.b = ψ.b := by
        calc φ.b = φ.b * (b * y) := by rw [hy, mul_one]
          _ = (φ.b * b) * y := (mul_assoc _ _ _).symm
          _ = (ψ.b * b) * y := by rw [h2, h4]
          _ = ψ.b := by rw [mul_assoc, hy, mul_one]
      have ea : φ.a = ψ.a := by
        have e1 : φ.a + φ.b * a = c := h1
        have e2 : ψ.a + ψ.b * a = c := h3
        rw [← eb] at e2
        exact add_right_cancel (e1.trans e2.symm)
      exact ext' ea eb

end Affine

/-- The number of `x < n` with `P x`, as a sum of `0`s and `1`s. -/
def natCount (P : Nat → Prop) [DecidablePred P] : Nat → Nat
  | 0 => 0
  | n + 1 => natCount P n + if P n then 1 else 0

theorem natCount_ne_zero (n : Nat) : natCount (fun x => x ≠ 0) (n + 1) = n := by
  induction n with
  | zero => rfl
  | succ n ih =>
    show natCount (fun x => x ≠ 0) (n + 1) + (if n + 1 ≠ 0 then 1 else 0) = n + 1
    rw [ih, if_pos (Nat.succ_ne_zero n)]

/-- 1:C2, the order — the frames `(a, b)`, `b ≠ 0`, number `p·(p − 1)`: `p` choices of the origin, `p − 1`
of the unit. -/
theorem frame_count (_F : Frame p κ g) :
    natCount (fun _ => True) p * natCount (fun b => b ≠ 0) p = p * (p - 1) := by
  have h1 : ∀ n, natCount (fun _ => True) n = n := fun n => by
    induction n with
    | zero => rfl
    | succ n ih => show natCount (fun _ => True) n + (if True then 1 else 0) = n + 1; rw [ih, if_pos trivial]
  have hp : p = (p - 1) + 1 := (FRC.Nat.sub_add_cancel Pos.pos).symm
  rw [h1]
  have h2 : natCount (fun b => b ≠ 0) p = p - 1 := by
    have := natCount_ne_zero (p - 1)
    rw [← hp] at this; exact this
  rw [h2]

end Frame
end Shell
end FRC

/-! inlined: FrcCore/Poly.lean -/

/-!
# FrcCore.Poly — polynomials over the shell and the root criterion (1:G1)

A polynomial is its coefficient sequence `Nat → Shell p` with a degree bound (`Bound f n`: the coefficients
beyond `n` vanish); equality is coefficientwise, so no function extensionality is needed.  The Cauchy
product, evaluation as a finite sum, the evaluation homomorphism (`eval_mul`, by a triangular reindexing of
sums), synthetic division by `X − a` at a root (`quot_linear_spec`), the root bound (a polynomial of degree
`n` vanishing at `n + 1` distinct points is zero, `root_bound`), and 1:G1's criterion: `f` has a root iff `f`
and `X^p − X` share a factor of positive degree (`root_iff_common_factor`).  The reverse direction is
constructive — the root is found by deciding `∃ i < p, d(i) = 0`.  No axioms.
-/

namespace FRC
namespace Shell

variable {p : Nat} [Pos p]

theorem sum_split (f : Nat → Shell p) (n k : Nat) :
    sumRange f (n + k) = sumRange f n + sumRange (fun t => f (n + t)) k := by
  induction k with
  | zero => rw [Nat.add_zero, sumRange_zero, add_zero]
  | succ k ih =>
    show sumRange f (n + k + 1) = _
    rw [sumRange_succ, sumRange_succ, ih, add_assoc]

/-- The triangular reindexing `Σ_{l<N} Σ_{j≤l} F j (l − j) = Σ_{j<N} Σ_{k<N−j} F j k`. -/
theorem sum_triangle (F : Nat → Nat → Shell p) (N : Nat) :
    sumRange (fun l => sumRange (fun j => F j (l - j)) (l + 1)) N =
    sumRange (fun j => sumRange (fun k => F j k) (N - j)) N := by
  induction N with
  | zero => rfl
  | succ N ih =>
    rw [sumRange_succ, ih, sumRange_succ (fun j => sumRange (fun k => F j k) (N + 1 - j)) N]
    have h1 : sumRange (fun j => sumRange (fun k => F j k) (N + 1 - j)) N =
        sumRange (fun j => sumRange (fun k => F j k) (N - j) + F j (N - j)) N := by
      apply sum_congr
      intro j hj
      show sumRange (fun k => F j k) (N + 1 - j) = sumRange (fun k => F j k) (N - j) + F j (N - j)
      have e : N + 1 - j = (N - j) + 1 := by
        have := FRC.Nat.add_sub_of_le (Nat.le_of_lt hj)
        -- this : j + (N - j) = N
        calc N + 1 - j = j + (N - j) + 1 - j := by rw [this]
          _ = (N - j) + 1 + j - j := by rw [Nat.add_comm j (N - j), Nat.add_right_comm (N - j) j 1]
          _ = (N - j) + 1 := FRC.Nat.add_sub_cancel _ _
      rw [e, sumRange_succ]
    rw [h1, sum_add]
    have e2 : N + 1 - N = 1 := FRC.Nat.add_sub_cancel_left N 1
    rw [e2, sumRange_succ (fun k => F N k) 0, sumRange_zero, zero_add,
      sumRange_succ (fun j => F j (N - j)) N, Nat.sub_self, add_assoc]

/-- A polynomial as its coefficient sequence. -/
abbrev Poly (p : Nat) [Pos p] := Nat → Shell p

namespace Poly

/-- `f` has degree at most `n`: the coefficients beyond `n` vanish. -/
def Bound (f : Poly p) (n : Nat) : Prop := ∀ i, n < i → f i = 0

/-- The Cauchy product `(f·g) i = Σ_{j ≤ i} f j · g (i − j)`. -/
def mul (f g : Poly p) : Poly p := fun i => sumRange (fun j => f j * g (i - j)) (i + 1)

/-- `f(a)` summed to the bound `n`: `Σ_{i ≤ n} f i · a^i`. -/
def eval (f : Poly p) (n : Nat) (a : Shell p) : Shell p := sumRange (fun i => f i * a ^ i) (n + 1)

/-- `X − a`. -/
def linear (a : Shell p) : Poly p
  | 0 => -a
  | 1 => 1
  | _ + 2 => 0

/-- `X^p − X`. -/
def xpx : Poly p := fun i => if i = p then 1 else if i = 1 then -1 else 0

theorem eval_congr {f h : Poly p} (e : ∀ i, f i = h i) (n : Nat) (a : Shell p) : eval f n a = eval h n a :=
  sum_congr (n + 1) (fun i _ => by show f i * a ^ i = h i * a ^ i; rw [e i])

theorem eval_bound {f : Poly p} {n N : Nat} (hf : Bound f n) (hN : n ≤ N) (a : Shell p) :
    eval f N a = eval f n a := by
  unfold eval
  have e : N + 1 = (n + 1) + (N - n) := by
    rw [Nat.add_right_comm, FRC.Nat.add_sub_of_le hN]
  rw [e, sum_split, sum_zero (N - n) (fun t _ => by
    show f (n + 1 + t) * a ^ (n + 1 + t) = 0
    rw [hf _ (Nat.lt_of_lt_of_le (Nat.lt_succ_self n) (Nat.le_add_right (n + 1) t)), zero_mul]), add_zero]

theorem mul_bound {d q : Poly p} {m k : Nat} (hd : Bound d m) (hq : Bound q k) : Bound (mul d q) (m + k) := by
  intro i hi
  apply sum_zero
  intro j hj
  show d j * q (i - j) = 0
  match Nat.decLe j m with
  | .isTrue hjm =>
    have : k < i - j := by
      apply FRC.Nat.le_sub_of_add_le
      -- k + 1 + j ≤ i  from  m + k < i and j ≤ m
      show k + 1 + j ≤ i
      calc k + 1 + j ≤ k + 1 + m := Nat.add_le_add_left hjm _
        _ = m + k + 1 := by rw [Nat.add_comm (k + 1) m, Nat.add_assoc]
        _ ≤ i := hi
    rw [hq _ this, mul_zero]
  | .isFalse hjm => rw [hd j (Nat.lt_of_not_le hjm), zero_mul]

/-- The evaluation is multiplicative: `(f·g)(a) = f(a)·g(a)`, with the bounds added. -/
theorem eval_mul {f g : Poly p} {n m : Nat} (hf : Bound f n) (hg : Bound g m) (a : Shell p) :
    eval (mul f g) (n + m) a = eval f n a * eval g m a := by
  unfold eval mul
  have h1 : sumRange (fun l => sumRange (fun j => f j * g (l - j)) (l + 1) * a ^ l) (n + m + 1) =
      sumRange (fun l => sumRange (fun j => f j * a ^ j * (g (l - j) * a ^ (l - j))) (l + 1)) (n + m + 1) := by
    apply sum_congr
    intro l _
    show sumRange (fun j => f j * g (l - j)) (l + 1) * a ^ l =
      sumRange (fun j => f j * a ^ j * (g (l - j) * a ^ (l - j))) (l + 1)
    rw [← sum_mul_right]
    apply sum_congr
    intro j hj
    show f j * g (l - j) * a ^ l = f j * a ^ j * (g (l - j) * a ^ (l - j))
    have : a ^ l = a ^ j * a ^ (l - j) := by rw [← pow_add, FRC.Nat.add_sub_of_le (Nat.le_of_lt_succ hj)]
    rw [this, mul_assoc, mul_assoc, mul_left_comm (g (l - j))]
  rw [h1, sum_triangle (fun j k => f j * a ^ j * (g k * a ^ k)) (n + m + 1)]
  have h2 : sumRange (fun j => sumRange (fun k => f j * a ^ j * (g k * a ^ k)) (n + m + 1 - j)) (n + m + 1) =
      sumRange (fun j => f j * a ^ j * sumRange (fun i => g i * a ^ i) (m + 1)) (n + m + 1) := by
    apply sum_congr
    intro j hj
    show sumRange (fun k => f j * a ^ j * (g k * a ^ k)) (n + m + 1 - j) =
      f j * a ^ j * sumRange (fun i => g i * a ^ i) (m + 1)
    rw [sum_mul_left]
    match Nat.decLe j n with
    | .isTrue hjn =>
      have e : n + m + 1 - j = (n + m - j) + 1 := by
        have := FRC.Nat.add_sub_of_le (Nat.le_trans hjn (Nat.le_add_right n m))
        calc n + m + 1 - j = j + (n + m - j) + 1 - j := by rw [this]
          _ = (n + m - j) + 1 + j - j := by rw [Nat.add_comm j (n + m - j), Nat.add_right_comm (n + m - j) j 1]
          _ = (n + m - j) + 1 := FRC.Nat.add_sub_cancel _ _
      rw [e]
      have hm : m ≤ n + m - j := by
        apply FRC.Nat.le_sub_of_add_le
        rw [Nat.add_comm n m]; exact Nat.add_le_add_left hjn m
      exact congrArg (f j * a ^ j * ·) (eval_bound hg hm a)
    | .isFalse hjn =>
      rw [hf j (Nat.lt_of_not_le hjn), zero_mul, zero_mul, zero_mul]
  rw [h2, sum_mul_right]
  exact congrArg (· * sumRange (fun i => g i * a ^ i) (m + 1)) (eval_bound hf (Nat.le_add_right n m) a)

theorem linear_bound (a : Shell p) : Bound (linear a) 1 := by
  intro i hi
  match i, hi with
  | _ + 2, _ => rfl

theorem mul_linear_zero (a : Shell p) (q : Poly p) : mul (linear a) q 0 = -(a * q 0) := by
  show sumRange (fun j => linear a j * q (0 - j)) 1 = _
  rw [sumRange_succ, sumRange_zero, zero_add]
  show -a * q 0 = -(a * q 0)
  exact (neg_mul a (q 0)).symm

theorem mul_linear_succ (a : Shell p) (q : Poly p) (i : Nat) :
    mul (linear a) q (i + 1) = q i + -(a * q (i + 1)) := by
  show sumRange (fun j => linear a j * q (i + 1 - j)) (i + 1 + 1) = _
  have e : i + 1 + 1 = 2 + i := Nat.add_comm i 2
  rw [e, sum_split, sum_zero i (fun t _ => by
    show linear a (2 + t) * q (i + 1 - (2 + t)) = 0
    rw [Nat.add_comm 2 t]
    show (0 : Shell p) * _ = 0
    exact zero_mul _), add_zero, sumRange_succ, sumRange_succ, sumRange_zero, zero_add]
  show -a * q (i + 1) + 1 * q i = q i + -(a * q (i + 1))
  rw [← neg_mul, one_mul, add_comm]

/-- The quotient of `f` (bound `n`) by `X − a`: `q i = Σ_{t < n − i} f (i + 1 + t) · a^t`. -/
def quotLinear (f : Poly p) (n : Nat) (a : Shell p) : Poly p :=
  fun i => sumRange (fun t => f (i + 1 + t) * a ^ t) (n - i)

/-- Synthetic division: at a root `a` of `f`, `f = (X − a)·q` with `q` of degree one less. -/
theorem quot_linear_spec {f : Poly p} {n : Nat} (hf : Bound f n) {a : Shell p} (ha : eval f n a = 0) :
    Bound (quotLinear f n a) (n - 1) ∧ ∀ i, f i = mul (linear a) (quotLinear f n a) i := by
  constructor
  · intro i hi
    have hni : n ≤ i := by
      match n, hi with
      | 0, _ => exact Nat.zero_le i
      | n' + 1, hi => exact Nat.succ_le_of_lt hi
    show sumRange (fun t => f (i + 1 + t) * a ^ t) (n - i) = 0
    rw [FRC.Nat.sub_eq_zero_of_le hni]
    rfl
  · intro i
    match i with
    | 0 =>
      rw [mul_linear_zero]
      -- f 0 + a · q 0 = f(a) = 0
      have e1 : n + 1 = 1 + n := Nat.add_comm n 1
      unfold eval at ha
      rw [e1, sum_split, sumRange_succ, sumRange_zero, zero_add] at ha
      have ha' : f 0 * a ^ 0 + sumRange (fun t => f (1 + t) * a ^ (1 + t)) n = 0 := ha
      rw [pow_zero, mul_one] at ha'
      have h2 : sumRange (fun t => f (1 + t) * a ^ (1 + t)) n = a * quotLinear f n a 0 := by
        show _ = a * sumRange (fun t => f (0 + 1 + t) * a ^ t) (n - 0)
        rw [← sum_mul_left]
        apply sum_congr
        intro t _
        show f (1 + t) * a ^ (1 + t) = a * (f (0 + 1 + t) * a ^ t)
        rw [pow_add, pow_one, mul_left_comm]
      rw [h2] at ha'
      exact eq_neg_of_add_eq_zero ha'
    | i + 1 =>
      rw [mul_linear_succ]
      match Nat.decLt i n with
      | .isTrue hin =>
        -- n − i = (n − (i + 1)) + 1
        have hk := FRC.Nat.add_sub_of_le (Nat.succ_le_of_lt hin)
        -- hk : i + 1 + (n - (i + 1)) = n
        have e : n - i = (n - (i + 1)) + 1 := by
          calc n - i = i + 1 + (n - (i + 1)) - i := by rw [hk]
            _ = i + ((n - (i + 1)) + 1) - i := by rw [Nat.add_assoc, Nat.add_comm 1]
            _ = (n - (i + 1)) + 1 := FRC.Nat.add_sub_cancel_left _ _
        show f (i + 1) = sumRange (fun t => f (i + 1 + t) * a ^ t) (n - i) +
          -(a * sumRange (fun t => f (i + 1 + 1 + t) * a ^ t) (n - (i + 1)))
        rw [e, Nat.add_comm (n - (i + 1)) 1, sum_split, sumRange_succ, sumRange_zero, zero_add]
        show f (i + 1) = f (i + 1 + 0) * a ^ 0 + sumRange (fun t => f (i + 1 + (1 + t)) * a ^ (1 + t)) (n - (i + 1)) +
          -(a * sumRange (fun t => f (i + 1 + 1 + t) * a ^ t) (n - (i + 1)))
        have h3 : sumRange (fun t => f (i + 1 + (1 + t)) * a ^ (1 + t)) (n - (i + 1)) =
            a * sumRange (fun t => f (i + 1 + 1 + t) * a ^ t) (n - (i + 1)) := by
          rw [← sum_mul_left]
          apply sum_congr
          intro t _
          show f (i + 1 + (1 + t)) * a ^ (1 + t) = a * (f (i + 1 + 1 + t) * a ^ t)
          rw [← Nat.add_assoc, pow_add, pow_one, mul_left_comm]
        rw [h3, Nat.add_zero, pow_zero, mul_one, add_assoc, add_neg, add_zero]
      | .isFalse hin =>
        have hni : n ≤ i := Nat.le_of_not_lt hin
        have z1 : n - i = 0 := FRC.Nat.sub_eq_zero_of_le hni
        have z2 : n - (i + 1) = 0 := FRC.Nat.sub_eq_zero_of_le (Nat.le_succ_of_le hni)
        show f (i + 1) = sumRange (fun t => f (i + 1 + t) * a ^ t) (n - i) +
          -(a * sumRange (fun t => f (i + 1 + 1 + t) * a ^ t) (n - (i + 1)))
        rw [z1, z2, sumRange_zero, sumRange_zero, mul_zero, neg_zero, add_zero]
        exact hf _ (Nat.lt_succ_of_le hni)

theorem eval_linear (a b : Shell p) : eval (linear a) 1 b = b + -a := by
  show sumRange (fun i => linear a i * b ^ i) 2 = _
  rw [sumRange_succ, sumRange_succ, sumRange_zero, zero_add]
  show -a * b ^ 0 + 1 * b ^ 1 = b + -a
  rw [pow_zero, mul_one, pow_one, one_mul, add_comm]

theorem eval_mul_linear {q : Poly p} {n : Nat} (hq : Bound q n) (a b : Shell p) :
    eval (mul (linear a) q) (n + 1) b = (b + -a) * eval q n b := by
  rw [Nat.add_comm n 1, eval_mul (linear_bound a) hq, eval_linear]

namespace Frame
variable {κ : Nat} {g : Shell p}

/-- 1:G1, the root bound — a polynomial of degree at most `n` that vanishes at `n + 1` distinct points is
zero: the distinct roots are counted by the degree. -/
theorem root_bound (F : Frame p κ g) : ∀ (n : Nat) (f : Poly p), Bound f n → ∀ (r : Nat → Shell p),
    (∀ i j, i ≤ n → j ≤ n → r i = r j → i = j) → (∀ i, i ≤ n → eval f n (r i) = 0) → ∀ i, f i = 0 := by
  intro n
  induction n with
  | zero =>
    intro f hf r _ hroot i
    have h0 := hroot 0 (Nat.le_refl 0)
    unfold eval at h0
    rw [sumRange_succ, sumRange_zero, zero_add] at h0
    have h0' : f 0 * r 0 ^ 0 = 0 := h0
    rw [pow_zero, mul_one] at h0'
    match i with
    | 0 => exact h0'
    | i + 1 => exact hf _ (Nat.zero_lt_succ i)
  | succ n ih =>
    intro f hf r hinj hroot
    have ha := hroot 0 (Nat.zero_le _)
    have spec := quot_linear_spec hf ha
    have hq : Bound (quotLinear f (n + 1) (r 0)) n := spec.1
    have hf' : ∀ b, eval f (n + 1) b = (b + -(r 0)) * eval (quotLinear f (n + 1) (r 0)) n b := fun b => by
      rw [eval_congr spec.2, eval_mul_linear hq]
    have hz : ∀ i, quotLinear f (n + 1) (r 0) i = 0 := by
      apply ih _ hq (fun k => r (k + 1))
      · intro i j hi hj e
        exact Nat.succ.inj (hinj (i + 1) (j + 1) (Nat.succ_le_succ hi) (Nat.succ_le_succ hj) e)
      · intro k hk
        have h := hroot (k + 1) (Nat.succ_le_succ hk)
        rw [hf'] at h
        match F.mul_eq_zero h with
        | .inl e =>
          have : r (k + 1) = r 0 := by
            calc r (k + 1) = r (k + 1) + 0 := (add_zero _).symm
              _ = r (k + 1) + (-(r 0) + r 0) := by rw [neg_add]
              _ = (r (k + 1) + -(r 0)) + r 0 := (add_assoc _ _ _).symm
              _ = r 0 := by rw [e, zero_add]
          exact absurd (hinj (k + 1) 0 (Nat.succ_le_succ hk) (Nat.zero_le _) this) (FRC.Nat.succ_ne_zero k)
        | .inr e => exact e
    intro i
    rw [spec.2 i]
    match i with
    | 0 => rw [mul_linear_zero, hz, mul_zero, neg_zero]
    | i + 1 => rw [mul_linear_succ, hz, hz, mul_zero, neg_zero, add_zero]

theorem xpx_bound : Bound (xpx : Poly p) p := by
  intro i hi
  show (if i = p then 1 else if i = 1 then -1 else 0 : Shell p) = 0
  rw [if_neg (Nat.ne_of_gt hi), if_neg (fun e => absurd hi (by rw [e]; exact Nat.not_lt_of_le (Pos.pos : 0 < p)))]

theorem xpx_p : (xpx : Poly p) p = 1 := by
  show (if p = p then 1 else if p = 1 then -1 else 0 : Shell p) = 1
  rw [if_pos rfl]

/-- `X^p − X` vanishes everywhere: Fermat. -/
theorem eval_xpx (F : Frame p κ g) (a : Shell p) : eval (xpx : Poly p) p a = 0 := by
  have h2 : 2 ≤ p := Nat.le_of_lt F.two_lt_p
  have e : p + 1 = 2 + (p - 1) := by
    calc p + 1 = 1 + (p - 1) + 1 := by rw [FRC.Nat.add_sub_of_le Pos.pos]
      _ = 2 + (p - 1) := by rw [Nat.add_right_comm]
  unfold eval
  rw [e, sum_split, sumRange_succ, sumRange_succ, sumRange_zero, zero_add]
  have hp1 : p ≠ 1 := fun h => absurd (h ▸ h2 : 2 ≤ 1) (Nat.not_le_of_lt (Nat.lt_succ_self 1))
  have t0 : (xpx : Poly p) 0 * a ^ 0 = 0 := by
    show (if 0 = p then 1 else if 0 = 1 then -1 else 0 : Shell p) * a ^ 0 = 0
    rw [if_neg (fun h => by have := (Pos.pos : 0 < p); rw [← h] at this; exact Nat.lt_irrefl 0 this),
      if_neg (fun h => FRC.Nat.succ_ne_zero 0 h.symm), zero_mul]
  have t1 : (xpx : Poly p) 1 * a ^ 1 = -a := by
    show (if 1 = p then 1 else if 1 = 1 then -1 else 0 : Shell p) * a ^ 1 = -a
    rw [if_neg (fun h => hp1 h.symm), if_pos rfl, pow_one, neg_one_mul]
  have t2 : sumRange (fun t => (xpx : Poly p) (2 + t) * a ^ (2 + t)) (p - 1) = a ^ p := by
    have hl : p - 2 < p - 1 := by
      have e : p = (p - 2) + 2 := (FRC.Nat.sub_add_cancel h2).symm
      rw [e]
      exact Nat.lt_succ_self (p - 2)
    rw [sum_eq_single hl (fun t _ ht => by
      show (if 2 + t = p then 1 else if 2 + t = 1 then -1 else 0 : Shell p) * a ^ (2 + t) = 0
      rw [if_neg (fun h => ht (by rw [← h, Nat.add_comm, FRC.Nat.add_sub_cancel])),
        if_neg (fun h => FRC.Nat.succ_ne_zero t (Nat.succ.inj (by rw [Nat.add_comm] at h; exact h))), zero_mul])]
    show (if 2 + (p - 2) = p then 1 else if 2 + (p - 2) = 1 then -1 else 0 : Shell p) * a ^ (2 + (p - 2)) = a ^ p
    rw [FRC.Nat.add_sub_of_le h2, if_pos rfl, one_mul]
  show (xpx : Poly p) 0 * a ^ 0 + (xpx : Poly p) 1 * a ^ 1 + sumRange (fun t => (xpx : Poly p) (2 + t) * a ^ (2 + t)) (p - 1) = 0
  rw [t0, t1, t2, zero_add, F.fermat, neg_add]

/-- A common factor of positive degree `m`: `d` with `d m ≠ 0` dividing both, with cofactors of the
complementary degrees. -/
def CommonFactor (f : Poly p) (n : Nat) (h : Poly p) (k : Nat) : Prop :=
  ∃ (d : Poly p) (m : Nat) (q1 q2 : Poly p), 1 ≤ m ∧ Bound d m ∧ d m ≠ 0 ∧ Bound q1 (n - m) ∧
    Bound q2 (k - m) ∧ (∀ i, f i = mul d q1 i) ∧ (∀ i, h i = mul d q2 i)

theorem ofNat_inj_lt {i j : Nat} (hi : i < p) (hj : j < p) (h : (ofNat i : Shell p) = ofNat j) : i = j := by
  have := val_injective h
  rw [val_ofNat, val_ofNat, FRC.Nat.mod_eq_of_lt hi, FRC.Nat.mod_eq_of_lt hj] at this
  exact this

/-- 1:G1, the root criterion — `f` has a root in the shell iff `f` and `X^p − X` share a factor of positive
degree.  Forward: the factor is `X − a` (synthetic division, Fermat).  Backward: a common factor `d` of
degree `m ≥ 1` with no root would force its cofactor in `X^p − X`, of degree `p − m < p`, to vanish at
all `p` residues, hence to be zero (`root_bound`), against `X^p − X ≠ 0`; the root of `d` is found by
deciding `∃ i < p, d(i) = 0`. -/
theorem root_iff_common_factor (F : Frame p κ g) {f : Poly p} {n : Nat} (hf : Bound f n) :
    (∃ a, eval f n a = 0) ↔ CommonFactor f n (xpx : Poly p) p := by
  constructor
  · intro ⟨a, ha⟩
    have s1 := quot_linear_spec hf ha
    have s2 := quot_linear_spec (xpx_bound (p := p)) (eval_xpx F a)
    exact ⟨linear a, 1, quotLinear f n a, quotLinear xpx p a, Nat.le_refl 1, linear_bound a, F.one_ne_zero,
      s1.1, s2.1, s1.2, s2.2⟩
  · intro ⟨d, m, q1, q2, hm, hd, hdm, hq1, hq2, e1, e2⟩
    -- every residue is a root of `d · q2`
    have hprod : ∀ a, eval d m a * eval q2 (p - m) a = 0 := fun a => by
      rw [← eval_mul hd hq2, ← eval_bound (mul_bound hd hq2) (Nat.add_le_add_left (Nat.sub_le p m) m) a,
        ← eval_congr e2, eval_bound xpx_bound (Nat.le_add_left p m), eval_xpx F]
    have : ∀ v, Decidable (∃ i, i < p ∧ eval d m (ofNat i) = v) :=
      fun v => decExistsLT (fun i => eval d m (ofNat i) = v) p
    match this 0 with
    | .isTrue ⟨i, _, hi⟩ =>
      refine ⟨ofNat i, ?_⟩
      rw [← eval_bound hf (Nat.le_add_right n m), eval_congr e1,
        eval_bound (mul_bound hd hq1) (by rw [Nat.add_comm n m]; exact Nat.add_le_add_left (Nat.sub_le n m) m),
        eval_mul hd hq1, hi, zero_mul]
    | .isFalse hno =>
      -- `q2` vanishes at the `p − m + 1 ≤ p` residues `0, …, p − m`, so it is zero
      have hk : p - m < p := Nat.sub_lt Pos.pos hm
      have hz : ∀ i, q2 i = 0 := by
        apply root_bound F (p - m) q2 hq2 (fun i => ofNat i)
        · intro i j hi hj e
          exact ofNat_inj_lt (Nat.lt_of_le_of_lt hi hk) (Nat.lt_of_le_of_lt hj hk) e
        · intro i hi
          match F.mul_eq_zero (hprod (ofNat i)) with
          | .inl e => exact absurd ⟨i, Nat.lt_of_le_of_lt hi hk, e⟩ hno
          | .inr e => exact e
      have : (xpx : Poly p) p = 0 := by
        rw [e2 p]
        apply sum_zero
        intro j _
        show d j * q2 (p - j) = 0
        rw [hz, mul_zero]
      rw [xpx_p] at this
      exact absurd this F.one_ne_zero

end Frame
end Poly
end Shell
end FRC

/-! inlined: FrcCore/Quaternion.lean -/

/-!
# FrcCore.Quaternion — the framed quaternions and the window (1:G5, the finitary clause)

A signed window integer is a pair of naturals `(u, v)` read as `u − v` in the shell (no `Int`: the core's
integers are the shell's own readings).  A framed quaternion is four such pairs; the Hamilton product is
computed on the pairs, and `read_mul` says the product of the readings is the reading of the product — the
composition is exact.  `quaternion_window` adds the bounds: with coordinates in the window `H` and a shell
`p > 8H²`, the product's coordinates lie in the window `4H²`, and the shell reading determines the integer
product among the window's quaternions.  No axioms.
-/

namespace FRC
namespace Shell
namespace Frame

variable {p : Nat} [Pos p]

/-- A signed window integer: `(u, v)` stands for `u − v`. -/
abbrev SInt := Nat × Nat

def sread (x : SInt) : Shell p := ofNat x.1 + -(ofNat x.2)
def sadd (x y : SInt) : SInt := (x.1 + y.1, x.2 + y.2)
def sneg (x : SInt) : SInt := (x.2, x.1)
def smul (x y : SInt) : SInt := (x.1 * y.1 + x.2 * y.2, x.1 * y.2 + x.2 * y.1)
/-- The canonical pair of the same value: one component zero. -/
def snorm (x : SInt) : SInt := (x.1 - x.2, x.2 - x.1)

theorem prod_ext {x y : SInt} (h1 : x.1 = y.1) (h2 : x.2 = y.2) : x = y :=
  match x, y, h1, h2 with
  | (_, _), (_, _), h1, h2 => by cases h1; cases h2; rfl

theorem sread_add (x y : SInt) : (sread (sadd x y) : Shell p) = sread x + sread y := by
  unfold sread sadd
  show ofNat (x.1 + y.1) + -(ofNat (x.2 + y.2)) = ofNat x.1 + -(ofNat x.2) + (ofNat y.1 + -(ofNat y.2))
  rw [← ofNat_add, ← ofNat_add, neg_add_rev, add_assoc, add_assoc, ← add_assoc (-(ofNat x.2)),
    add_comm (-(ofNat x.2)) (ofNat y.1), add_assoc]

theorem sread_neg (x : SInt) : (sread (sneg x) : Shell p) = -(sread x) := by
  unfold sread sneg
  show ofNat x.2 + -(ofNat x.1) = -(ofNat x.1 + -(ofNat x.2))
  rw [neg_add_rev, neg_neg, add_comm]

theorem sread_mul (x y : SInt) : (sread (smul x y) : Shell p) = sread x * sread y := by
  unfold sread smul
  show ofNat (x.1 * y.1 + x.2 * y.2) + -(ofNat (x.1 * y.2 + x.2 * y.1)) =
    (ofNat x.1 + -(ofNat x.2)) * (ofNat y.1 + -(ofNat y.2))
  rw [right_distrib, left_distrib, left_distrib, ← mul_neg, ← neg_mul, neg_mul_neg, ← ofNat_add, ← ofNat_add,
    ← ofNat_mul, ← ofNat_mul, ← ofNat_mul, ← ofNat_mul, neg_add_rev]
  -- a + d + (-b + -c) = a + -b + (-c + d)
  rw [add_assoc, add_assoc]
  refine congrArg (ofNat x.1 * ofNat y.1 + ·) ?_
  rw [← add_assoc, add_comm (ofNat x.2 * ofNat y.2), add_assoc, add_comm (ofNat x.2 * ofNat y.2)]

theorem sread_norm (x : SInt) : (sread (snorm x) : Shell p) = sread x := by
  unfold sread snorm
  match Nat.decLe x.2 x.1 with
  | .isTrue h =>
    have e : x.2 - x.1 = 0 := FRC.Nat.sub_eq_zero_of_le h
    show ofNat (x.1 - x.2) + -(ofNat (x.2 - x.1)) = ofNat x.1 + -(ofNat x.2)
    rw [e]
    have e0 : (ofNat 0 : Shell p) = 0 := rfl
    rw [e0, neg_zero, add_zero]
    have e1 : x.1 = (x.1 - x.2) + x.2 := (FRC.Nat.sub_add_cancel h).symm
    calc ofNat (x.1 - x.2) = ofNat (x.1 - x.2) + 0 := (add_zero _).symm
      _ = ofNat (x.1 - x.2) + (ofNat x.2 + -(ofNat x.2)) := by rw [add_neg]
      _ = ofNat (x.1 - x.2 + x.2) + -(ofNat x.2) := by rw [← add_assoc, ofNat_add]
      _ = ofNat x.1 + -(ofNat x.2) := by rw [← e1]
  | .isFalse h =>
    have h' : x.1 ≤ x.2 := Nat.le_of_lt (Nat.lt_of_not_le h)
    have e : x.1 - x.2 = 0 := FRC.Nat.sub_eq_zero_of_le h'
    show ofNat (x.1 - x.2) + -(ofNat (x.2 - x.1)) = ofNat x.1 + -(ofNat x.2)
    rw [e]
    have e0 : (ofNat 0 : Shell p) = 0 := rfl
    rw [e0, zero_add]
    have e1 : x.2 = (x.2 - x.1) + x.1 := (FRC.Nat.sub_add_cancel h').symm
    calc (-(ofNat (x.2 - x.1)) : Shell p) = (0 : Shell p) + -(ofNat (x.2 - x.1)) := (zero_add _).symm
      _ = (ofNat x.1 + -(ofNat x.1)) + -(ofNat (x.2 - x.1)) := by rw [add_neg]
      _ = ofNat x.1 + -((ofNat (x.2 - x.1) : Shell p) + ofNat x.1) := by
          rw [add_assoc, neg_add_rev, add_comm (-(ofNat x.1))]
      _ = ofNat x.1 + -(ofNat x.2) := by rw [ofNat_add, ← e1]

/-- The window bound: both components at most `H`, one of them zero. -/
def SBound (H : Nat) (x : SInt) : Prop := x.1 ≤ H ∧ x.2 ≤ H ∧ (x.1 = 0 ∨ x.2 = 0)

theorem sneg_bound {H : Nat} {x : SInt} (h : SBound H x) : SBound H (sneg x) :=
  ⟨h.2.1, h.1, match h.2.2 with | Or.inl e => Or.inr e | Or.inr e => Or.inl e⟩

theorem smul_bound {H : Nat} {x y : SInt} (hx : SBound H x) (hy : SBound H y) : SBound (H * H) (smul x y) := by
  unfold smul
  have b11 := Nat.mul_le_mul hx.1 hy.1
  have b22 := Nat.mul_le_mul hx.2.1 hy.2.1
  have b12 := Nat.mul_le_mul hx.1 hy.2.1
  have b21 := Nat.mul_le_mul hx.2.1 hy.1
  match hx.2.2, hy.2.2 with
  | Or.inl e, Or.inl f =>
    refine ⟨?_, ?_, Or.inr ?_⟩
    · show x.1 * y.1 + x.2 * y.2 ≤ H * H
      rw [e, Nat.zero_mul, Nat.zero_add]; exact b22
    · show x.1 * y.2 + x.2 * y.1 ≤ H * H
      rw [e, f, Nat.zero_mul, Nat.mul_zero]; exact Nat.zero_le _
    · show x.1 * y.2 + x.2 * y.1 = 0
      rw [e, f, Nat.zero_mul, Nat.mul_zero]
  | Or.inl e, Or.inr f =>
    refine ⟨?_, ?_, Or.inl ?_⟩
    · show x.1 * y.1 + x.2 * y.2 ≤ H * H
      rw [e, f, Nat.zero_mul, Nat.mul_zero]; exact Nat.zero_le _
    · show x.1 * y.2 + x.2 * y.1 ≤ H * H
      rw [e, Nat.zero_mul, Nat.zero_add]; exact b21
    · show x.1 * y.1 + x.2 * y.2 = 0
      rw [e, f, Nat.zero_mul, Nat.mul_zero]
  | Or.inr e, Or.inl f =>
    refine ⟨?_, ?_, Or.inl ?_⟩
    · show x.1 * y.1 + x.2 * y.2 ≤ H * H
      rw [e, f, Nat.mul_zero, Nat.zero_mul]; exact Nat.zero_le _
    · show x.1 * y.2 + x.2 * y.1 ≤ H * H
      rw [e, Nat.zero_mul, Nat.add_zero]; exact b12
    · show x.1 * y.1 + x.2 * y.2 = 0
      rw [e, f, Nat.mul_zero, Nat.zero_mul]
  | Or.inr e, Or.inr f =>
    refine ⟨?_, ?_, Or.inr ?_⟩
    · show x.1 * y.1 + x.2 * y.2 ≤ H * H
      rw [e, Nat.zero_mul, Nat.add_zero]; exact b11
    · show x.1 * y.2 + x.2 * y.1 ≤ H * H
      rw [e, f, Nat.mul_zero, Nat.zero_mul]; exact Nat.zero_le _
    · show x.1 * y.2 + x.2 * y.1 = 0
      rw [e, f, Nat.mul_zero, Nat.zero_mul]

/-- Four window terms of size `M` add to a pair with both components at most `4M`. -/
theorem sum4_bound {M : Nat} {t1 t2 t3 t4 : SInt} (h1 : SBound M t1) (h2 : SBound M t2) (h3 : SBound M t3)
    (h4 : SBound M t4) :
    (sadd (sadd t1 t2) (sadd t3 t4)).1 ≤ 4 * M ∧ (sadd (sadd t1 t2) (sadd t3 t4)).2 ≤ 4 * M := by
  unfold sadd
  rw [four_mul_eq, Nat.add_assoc (M + M) M M]
  exact ⟨Nat.add_le_add (Nat.add_le_add h1.1 h2.1) (Nat.add_le_add h3.1 h4.1),
    Nat.add_le_add (Nat.add_le_add h1.2.1 h2.2.1) (Nat.add_le_add h3.2.1 h4.2.1)⟩

theorem snorm_bound {M : Nat} {x : SInt} (h1 : x.1 ≤ M) (h2 : x.2 ≤ M) : SBound M (snorm x) := by
  unfold snorm
  refine ⟨Nat.le_trans (Nat.sub_le _ _) h1, Nat.le_trans (Nat.sub_le _ _) h2, ?_⟩
  match Nat.decLe x.2 x.1 with
  | .isTrue h => exact Or.inr (FRC.Nat.sub_eq_zero_of_le h)
  | .isFalse h => exact Or.inl (FRC.Nat.sub_eq_zero_of_le (Nat.le_of_lt (Nat.lt_of_not_le h)))

/-- The signed window law: two canonical pairs of size `M`, `2M < p`, with the same reading are equal. -/
theorem sread_inj {M : Nat} (hM : 2 * M < p) {x y : SInt} (hx : SBound M x) (hy : SBound M y)
    (h : (sread x : Shell p) = sread y) : x = y := by
  unfold sread at h
  have h' : (ofNat (x.1 + y.2) : Shell p) = ofNat (y.1 + x.2) := by
    rw [← ofNat_add, ← ofNat_add]
    calc ofNat x.1 + ofNat y.2 = ofNat x.1 + -(ofNat x.2) + (ofNat x.2 + ofNat y.2) := by
          rw [add_assoc, ← add_assoc (-(ofNat x.2)), neg_add, zero_add]
      _ = ofNat y.1 + -(ofNat y.2) + (ofNat x.2 + ofNat y.2) := by rw [h]
      _ = ofNat y.1 + ofNat x.2 := by
          rw [add_assoc, add_comm (ofNat x.2), ← add_assoc (-(ofNat y.2)), neg_add, zero_add]
  have hv := val_injective h'
  rw [val_ofNat, val_ofNat] at hv
  have l1 : x.1 + y.2 < p := Nat.lt_of_le_of_lt (Nat.add_le_add hx.1 hy.2.1) (Nat.two_mul M ▸ hM)
  have l2 : y.1 + x.2 < p := Nat.lt_of_le_of_lt (Nat.add_le_add hy.1 hx.2.1) (Nat.two_mul M ▸ hM)
  rw [FRC.Nat.mod_eq_of_lt l1, FRC.Nat.mod_eq_of_lt l2] at hv
  -- hv : x.1 + y.2 = y.1 + x.2
  match hx.2.2, hy.2.2 with
  | Or.inl e, Or.inl f =>
    rw [e, f, Nat.zero_add, Nat.zero_add] at hv
    exact prod_ext (e.trans f.symm) hv.symm
  | Or.inl e, Or.inr f =>
    rw [e, f, Nat.zero_add] at hv
    -- hv : 0 = y.1 + x.2
    have hy1 : y.1 = 0 := Nat.eq_zero_of_add_eq_zero_right hv.symm
    have hx2 : x.2 = 0 := Nat.eq_zero_of_add_eq_zero_left hv.symm
    exact prod_ext (e.trans hy1.symm) (hx2.trans f.symm)
  | Or.inr e, Or.inl f =>
    rw [e, f, Nat.zero_add] at hv
    -- hv : x.1 + y.2 = 0
    have hx1 : x.1 = 0 := Nat.eq_zero_of_add_eq_zero_right hv
    have hy2 : y.2 = 0 := Nat.eq_zero_of_add_eq_zero_left hv
    exact prod_ext (hx1.trans f.symm) (e.trans hy2.symm)
  | Or.inr e, Or.inr f =>
    rw [e, f, Nat.add_zero, Nat.add_zero] at hv
    exact prod_ext hv (e.trans f.symm)

/-- A framed quaternion with signed window coordinates. -/
structure IQuat where
  a : SInt
  b : SInt
  c : SInt
  d : SInt

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

/-- The Hamilton product on the window pairs, the same formula. -/
def IQuat.mul (q r : IQuat) : IQuat :=
  ⟨sadd (sadd (smul q.a r.a) (sneg (smul q.b r.b))) (sadd (sneg (smul q.c r.c)) (sneg (smul q.d r.d))),
   sadd (sadd (smul q.a r.b) (smul q.b r.a)) (sadd (smul q.c r.d) (sneg (smul q.d r.c))),
   sadd (sadd (smul q.a r.c) (sneg (smul q.b r.d))) (sadd (smul q.c r.a) (smul q.d r.b)),
   sadd (sadd (smul q.a r.d) (smul q.b r.c)) (sadd (sneg (smul q.c r.b)) (smul q.d r.a))⟩

def IQuat.read (q : IQuat) : Quat p := ⟨sread q.a, sread q.b, sread q.c, sread q.d⟩
def IQuat.norm (q : IQuat) : IQuat := ⟨snorm q.a, snorm q.b, snorm q.c, snorm q.d⟩
def QBound (H : Nat) (q : IQuat) : Prop := SBound H q.a ∧ SBound H q.b ∧ SBound H q.c ∧ SBound H q.d

theorem IQuat.ext' {q r : IQuat} (ha : q.a = r.a) (hb : q.b = r.b) (hc : q.c = r.c) (hd : q.d = r.d) : q = r := by
  cases q; cases r; cases ha; cases hb; cases hc; cases hd; rfl

/-- 1:G5, exact composition — the reading of the integer product is the product of the readings. -/
theorem read_mul (q r : IQuat) : ((IQuat.mul q r).read : Quat p) = Quat.mul q.read r.read := by
  unfold IQuat.mul IQuat.read Quat.mul
  rw [sread_add, sread_add, sread_add, sread_add, sread_add, sread_add, sread_add, sread_add, sread_add,
    sread_add, sread_add, sread_add, sread_neg, sread_neg, sread_neg, sread_neg, sread_neg, sread_neg,
    sread_mul, sread_mul, sread_mul, sread_mul, sread_mul, sread_mul, sread_mul, sread_mul, sread_mul,
    sread_mul, sread_mul, sread_mul, sread_mul, sread_mul, sread_mul, sread_mul]

theorem read_norm (q : IQuat) : (q.norm.read : Quat p) = q.read := by
  unfold IQuat.norm IQuat.read
  rw [sread_norm, sread_norm, sread_norm, sread_norm]

theorem norm_bound {H : Nat} {q r : IQuat} (hq : QBound H q) (hr : QBound H r) :
    QBound (4 * (H * H)) (IQuat.mul q r).norm := by
  have m := fun {x y : SInt} (hx : SBound H x) (hy : SBound H y) => smul_bound hx hy
  refine ⟨?_, ?_, ?_, ?_⟩
  · have := sum4_bound (m hq.1 hr.1) (sneg_bound (m hq.2.1 hr.2.1)) (sneg_bound (m hq.2.2.1 hr.2.2.1))
      (sneg_bound (m hq.2.2.2 hr.2.2.2))
    exact snorm_bound this.1 this.2
  · have := sum4_bound (m hq.1 hr.2.1) (m hq.2.1 hr.1) (m hq.2.2.1 hr.2.2.2) (sneg_bound (m hq.2.2.2 hr.2.2.1))
    exact snorm_bound this.1 this.2
  · have := sum4_bound (m hq.1 hr.2.2.1) (sneg_bound (m hq.2.1 hr.2.2.2)) (m hq.2.2.1 hr.1) (m hq.2.2.2 hr.2.1)
    exact snorm_bound this.1 this.2
  · have := sum4_bound (m hq.1 hr.2.2.2) (m hq.2.1 hr.2.2.1) (sneg_bound (m hq.2.2.1 hr.2.1)) (m hq.2.2.2 hr.1)
    exact snorm_bound this.1 this.2

/-- 1:G5, the finitary clause — framed quaternions with window coordinates `≤ H`, read in a shell `p > 8H²`,
compose exactly: the product of the readings is the reading of the integer product; that product's
coordinates lie in the window `4H²`; and the reading determines it among the window's quaternions. -/
theorem quaternion_window {H : Nat} (hH : 8 * (H * H) < p) {q r : IQuat} (hq : QBound H q) (hr : QBound H r) :
    ((IQuat.mul q r).read : Quat p) = Quat.mul q.read r.read ∧
    QBound (4 * (H * H)) (IQuat.mul q r).norm ∧
    ∀ s : IQuat, QBound (4 * (H * H)) s → (s.read : Quat p) = (IQuat.mul q r).read → s = (IQuat.mul q r).norm := by
  refine ⟨read_mul q r, norm_bound hq hr, ?_⟩
  intro s hs he
  have hn := norm_bound hq hr
  have hM : 2 * (4 * (H * H)) < p := by rw [← Nat.mul_assoc]; exact hH
  rw [← read_norm (IQuat.mul q r)] at he
  unfold IQuat.read at he
  exact IQuat.ext' (sread_inj hM hs.1 hn.1 (congrArg Quat.a he)) (sread_inj hM hs.2.1 hn.2.1 (congrArg Quat.b he))
    (sread_inj hM hs.2.2.1 hn.2.2.1 (congrArg Quat.c he)) (sread_inj hM hs.2.2.2 hn.2.2.2 (congrArg Quat.d he))

end Frame
end Shell
end FRC

/-! inlined: FrcCore/Causality.lean -/

/-!
# FrcCore.Causality — the Euclidean–Lorentzian dichotomy on the shell (3-causality)

The square classes of the shell, the diagonal form `Q_ν = −ν t² + x² + y² + z²`, and the boosts of its `(t, x)`
plane, from first principles.  3:B2: a nonsquare `ν` has no root, and with `c ≠ 0` the coefficient `−c²` is a square
(`−1 = i²`).  3:B3: the absorption of a common square class by rescaling.  3:B5: `x² − ν t²` is anisotropic for a
nonsquare `ν` (the Witt kernel of the Lorentzian form), while `y² + z²` and `x² − w² t²` are hyperbolic planes.
3:C2, C3: the boost `Λ(γ, b) = [[γ, b], [νb, γ]]` with `γ² − νb² = 1` preserves `x² − ν t²` (the norm of `K = F_p(√ν)`
is multiplicative), boosts compose as norm-one elements multiply, `γ` is never zero, and the velocities
`v = −νb/γ` obey the Einstein addition law exactly.  The counts — the null cone `p³ − p² + p` on the Lorentzian form,
`p³ + p² − p` on the Euclidean one, `p + 1` boosts — are decided by the kernel on `𝔽₅`, `𝔽₁₃`, `𝔽₁₇`.  No axioms.
-/

namespace FRC
namespace Shell
namespace Frame

variable {p : Nat} [Pos p] {κ : Nat} {g : Shell p}

/-- `x` is a square: `x = y·y` for some residue `y`. -/
def IsSquare (x : Shell p) : Prop := ∃ y : Shell p, y * y = x

/-- 3:B2 (Thm. nonexistence, first clause) — `c² = ν` makes `ν` a square, so a nonsquare `ν` has no root `c`. -/
theorem no_causal_root {ν : Shell p} (h : ¬IsSquare ν) (c : Shell p) : c * c ≠ ν := fun e => h ⟨c, e⟩

theorem mul_mul_mul_comm (a b c d : Shell p) : (a * b) * (c * d) = (a * c) * (b * d) := by
  rw [mul_assoc, mul_left_comm b, ← mul_assoc]

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
def boostT (ν γ b t x : Shell p) : Shell p := γ * t + b * x
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

/-! inlined: FrcCore/Geometry.lean -/

/-!
# FrcCore.Geometry — 2-geometry rows on the core

2:C2 (the cell counts of the orbital shell and its completion, as identities of natural numbers), 2:E3 (the
fixed-shell bound, every shell, and the `(13, 2)` gap), 2:B4 (the reindexing `m ↦ u·m` preserves the phase
cycle's adjacency exactly when `u ≡ ±1`; the dihedral maps do), 2:C4 (the frame moves the labels of one complex),
and 2:C3 with the automorphism census of B4 decided on the coded complex for `p = 5, 13, 17` (the completion is a
closed surface: every edge in two faces, every vertex link one cycle). No axioms.
-/

namespace FRC
namespace Geometry

/-- 2:C2 (Remark 3.4) — the counts: with `π = m + 1` phases-deep and `n = p − 1` phases,
`|V| − |E| + |F| = 1` for the shell and `2` for its completion, written without subtraction:
`(πn + 1) + πn = 2πn + 1` and `((π−1)n + 2) + πn = (2π−1)n + 2`. -/
theorem euler_characteristic (m n : Nat) :
    ((m + 1) * n + 1) + (m + 1) * n = 2 * ((m + 1) * n) + 1 ∧
    (m * n + 2) + (m + 1) * n = (2 * m + 1) * n + 2 := by
  constructor
  · rw [Nat.two_mul, Nat.add_right_comm]
  · rw [FRC.Nat.add_mul, FRC.Nat.add_mul, Nat.one_mul, FRC.Nat.mul_assoc, Nat.two_mul,
      FRC.Nat.add_add_add_comm, Nat.add_comm 2 n, ← Nat.add_assoc]

/-- 2:E3 — the fixed-shell gap at `p = 13`, `g = 2` (window `x ≤ 6`): no grid point `x / 2^n`
lies strictly between `3/4` and `1` at any depth `n` — the covering radius of the fixed-shell
refinement in `[0, 1]` is at least `1/8` for every depth. -/
theorem fixed_shell_gap (n x : Nat) (hx : x ≤ 6) : ¬ (3 * 2 ^ n < 4 * x ∧ x < 2 ^ n) := by
  intro h
  match Nat.lt_or_ge n 3 with
  | .inl hn =>
    exact (by decide : ∀ n, n < 3 → ∀ x, x ≤ 6 → ¬ (3 * 2 ^ n < 4 * x ∧ x < 2 ^ n)) n hn x hx h
  | .inr hn =>
    have h8 : 2 ^ 3 ≤ 2 ^ n := Nat.pow_le_pow_right (Nat.zero_lt_succ 1) hn
    have h24 : 4 * x ≤ 4 * 6 := Nat.mul_le_mul_left 4 hx
    have h24' : 3 * 2 ^ 3 ≤ 3 * 2 ^ n := Nat.mul_le_mul_left 3 h8
    exact Nat.lt_irrefl _ (Nat.lt_of_lt_of_le (Nat.lt_of_le_of_lt h24' h.1) h24)

/-- 2:E3 (the fixed-shell bound, every shell) — for `g ≥ 2`, any cut `m`, depth `n` and `x ≤ 2κ` with
`x < g^n` (the grid point `x/g^n` below `1`): either `x/g^n ≤ 1 − g^{−m}`, i.e. `x·g^m + g^n ≤ g^m·g^n`,
or `x/g^n ≤ 2κ·g^{−(m+1)}`, i.e. `x·g^{m+1} ≤ 2κ·g^n`. With `2κ + 1 < g^{m+1}` both bounds are below `1`, so the
covering radius of the fixed-shell refinement in `[0, 1]` is bounded below at every depth. -/
theorem fixed_shell_bound (g κ m n x : Nat) (hg : 2 ≤ g) (hx : x ≤ 2 * κ) (hlt : x < g ^ n) :
    x * g ^ m + g ^ n ≤ g ^ m * g ^ n ∨ x * g ^ (m + 1) ≤ 2 * κ * g ^ n := by
  have hg1 : 1 ≤ g := Nat.le_trans (Nat.le_succ 1) hg
  match Nat.lt_or_ge n (m + 1) with
  | .inl hnm =>
    -- n ≤ m: x + 1 ≤ g^n, so x·g^m + g^m ≤ g^n·g^m, and g^n ≤ g^m
    refine .inl ?_
    have hn : n ≤ m := Nat.le_of_lt_succ hnm
    have h1 : (x + 1) * g ^ m ≤ g ^ n * g ^ m := Nat.mul_le_mul_right _ hlt
    have h2 : g ^ n ≤ g ^ m := Nat.pow_le_pow_right (Nat.lt_of_lt_of_le (Nat.zero_lt_succ 0) hg1) hn
    rw [FRC.Nat.add_mul, Nat.one_mul] at h1
    calc x * g ^ m + g ^ n ≤ x * g ^ m + g ^ m := Nat.add_le_add_left h2 _
      _ ≤ g ^ n * g ^ m := h1
      _ = g ^ m * g ^ n := Nat.mul_comm _ _
  | .inr hnm =>
    refine .inr ?_
    have h1 : g ^ (m + 1) ≤ g ^ n := Nat.pow_le_pow_right (Nat.lt_of_lt_of_le (Nat.zero_lt_succ 0) hg1) hnm
    exact Nat.mul_le_mul hx h1

/-- The cut `m = ⌊log_g(2κ+1)⌋`, i.e. `2κ + 1 < g^{m+1}`, puts the second bound below `1`
(`2κ·g^n < g^{m+1}·g^n`); the first is below `1` for every `m` (`g^m·g^n − g^n < g^m·g^n`). -/
theorem fixed_shell_bound_lt_one (g κ m n : Nat) (hg : 2 ≤ g) (hm : 2 * κ + 1 < g ^ (m + 1)) :
    2 * κ * g ^ n < g ^ (m + 1) * g ^ n ∧ 0 < g ^ n := by
  have hg1 : 1 ≤ g := Nat.le_trans (Nat.le_succ 1) hg
  have hpos : 0 < g ^ n := Nat.pow_pos (Nat.lt_of_lt_of_le (Nat.zero_lt_succ 0) hg1)
  exact ⟨FRC.Nat.mul_lt_mul_of_lt_of_pos (Nat.lt_of_le_of_lt (Nat.le_succ _) hm) hpos, hpos⟩

/-! ### 2:B4 — which reindexings of the phase cycle are cellular -/

/-- `m` and `m'` are adjacent on the phase cycle of length `n`. -/
def Adj (n m m' : Nat) : Prop := (m + 1) % n = m' ∨ (m' + 1) % n = m

/-- The reindexing `ρ_u : m ↦ u·m mod n`. -/
def rho (n u m : Nat) : Nat := (u * m) % n

/-- 2:B4 (Prop. 2.8) — `ρ_u` preserves the adjacency of the phase cycle (`n ≥ 3`) exactly when
`u ≡ 1` or `u ≡ −1 (mod n)`. -/
theorem rho_adj_iff (n u : Nat) (hn : 3 ≤ n) :
    (∀ m, m < n → Adj n (rho n u m) (rho n u ((m + 1) % n))) ↔ (u % n = 1 ∨ u % n = n - 1) := by
  have hn0 : 0 < n := Nat.lt_of_lt_of_le (Nat.zero_lt_succ 2) hn
  have h1n : 1 < n := Nat.lt_of_lt_of_le (Nat.lt_succ_self 1) (Nat.le_trans (Nat.le_succ 2) hn)
  constructor
  · intro h
    have h0 := h 0 hn0
    unfold rho at h0
    rw [Nat.mul_zero, FRC.Nat.zero_mod, Nat.zero_add, FRC.Nat.mod_eq_of_lt h1n, Nat.mul_one] at h0
    -- Adj n 0 (u % n): (0 + 1) % n = u % n, or (u % n + 1) % n = 0
    match h0 with
    | Or.inl e => exact Or.inl (by rw [Nat.zero_add, FRC.Nat.mod_eq_of_lt h1n] at e; exact e.symm)
    | Or.inr e =>
      refine Or.inr ?_
      have hu := Nat.mod_lt u hn0
      exact match Nat.lt_or_ge (u % n + 1) n with
        | Or.inl hlt => by
            rw [FRC.Nat.mod_eq_of_lt hlt] at e
            exact absurd e (Nat.succ_ne_zero _)
        | Or.inr hge =>
            have : u % n + 1 = n := Nat.le_antisymm hu hge
            calc u % n = (u % n + 1) - 1 := (FRC.Nat.add_sub_cancel _ _).symm
              _ = n - 1 := by rw [this]
  · intro h m hm
    unfold rho Adj
    match h with
    | Or.inl e =>
      -- u ≡ 1: ρ is the identity on residues
      have e1 : ∀ x, x < n → (u * x) % n = x := fun x hx => by
        rw [← FRC.Nat.mod_mul_mod _ _ _ hn0, e, Nat.one_mul, FRC.Nat.mod_eq_of_lt hx]
      rw [e1 m hm, e1 _ (Nat.mod_lt _ hn0)]
      exact Or.inl rfl
    | Or.inr e =>
      -- u ≡ −1: ρ is the reflection m ↦ (n − m) % n, and rev (m+1) + 1 ≡ rev m
      have e1 : ∀ x, x < n → (u * x) % n = Shell.Frame.rev n x := fun x hx => by
        unfold Shell.Frame.rev
        rw [← FRC.Nat.mod_mul_mod _ _ _ hn0, e]
        exact match Nat.decEq x 0 with
          | isTrue hx0 => by rw [hx0, Nat.mul_zero, Nat.sub_zero, FRC.Nat.zero_mod, FRC.Nat.mod_self n hn0]
          | isFalse hx0 => by
              have hx0' := Nat.pos_of_ne_zero hx0
              -- (n − 1)·x = n·(x − 1) + (n − x)
              have : (n - 1) * x = n * (x - 1) + (n - x) := by
                have h1 : (n - 1) * x + x = n * x := by
                  rw [← Nat.succ_mul, Nat.succ_eq_add_one, FRC.Nat.sub_add_cancel (Nat.le_of_lt h1n)]
                have h2 : n * (x - 1) + n = n * x := by
                  rw [← Nat.mul_succ, Nat.succ_eq_add_one, FRC.Nat.sub_add_cancel hx0']
                have h3 : n * (x - 1) + (n - x) + x = n * x := by
                  rw [Nat.add_assoc, FRC.Nat.sub_add_cancel (Nat.le_of_lt hx), h2]
                exact FRC.Nat.add_right_cancel (h1.trans h3.symm)
              rw [this, FRC.Nat.add_mul_mod_self_left _ _ _ hn0]
      rw [e1 m hm, e1 _ (Nat.mod_lt _ hn0)]
      -- rev (m+1 mod n) + 1 ≡ rev m: both ≡ −m
      refine Or.inr ?_
      exact match Nat.lt_or_ge (m + 1) n with
        | Or.inl hlt => by
            rw [FRC.Nat.mod_eq_of_lt hlt]
            exact match Nat.decEq m 0 with
              | isTrue e0 => by
                  rw [e0] at hlt ⊢
                  rw [Shell.Frame.rev_zero _ hn0, Shell.Frame.rev_of_pos hlt (Nat.zero_lt_succ 0), Nat.zero_add,
                    FRC.Nat.sub_add_cancel (Nat.le_of_lt h1n)]
                  exact FRC.Nat.mod_self n hn0
              | isFalse e0 => by
                  have hm0 := Nat.pos_of_ne_zero e0
                  rw [Shell.Frame.rev_of_pos hlt (Nat.zero_lt_succ m), Shell.Frame.rev_of_pos hm hm0]
                  -- (n − (m+1)) + 1 = n − m, below n
                  have : n - (m + 1) + 1 = n - m := by
                    have h1 : n - (m + 1) + (m + 1) = n := FRC.Nat.sub_add_cancel (Nat.le_of_lt hlt)
                    have h2 : n - m + m = n := FRC.Nat.sub_add_cancel (Nat.le_of_lt hm)
                    apply FRC.Nat.add_right_cancel (c := m)
                    rw [h2, Nat.add_assoc, Nat.add_comm 1 m, h1]
                  rw [this]
                  exact FRC.Nat.mod_eq_of_lt (Nat.sub_lt hn0 hm0)
        | Or.inr hge => by
            -- m + 1 = n: m = n − 1, rev 0 + 1 = 1, rev (n−1) = 1
            have hmn : m + 1 = n := Nat.le_antisymm hm hge
            rw [hmn, FRC.Nat.mod_self _ hn0, Shell.Frame.rev_zero _ hn0, Nat.zero_add, FRC.Nat.mod_eq_of_lt h1n]
            have hm0 : 0 < m := by
              refine Nat.lt_of_add_lt_add_right (n := 1) ?_
              rw [Nat.zero_add, hmn]; exact h1n
            rw [Shell.Frame.rev_of_pos hm hm0, ← hmn, FRC.Nat.add_sub_cancel_left]

/-- The rotations `m ↦ m + c` preserve adjacency (with `ρ_{±1}` they generate the dihedral maps of B4). -/
theorem rotation_adj (n c m : Nat) (hn : 0 < n) : Adj n ((m + c) % n) (((m + 1) % n + c) % n) := by
  unfold Adj
  refine Or.inl ?_
  rw [FRC.Nat.mod_add_mod _ _ _ hn, FRC.Nat.mod_add_mod _ _ _ hn, Nat.add_right_comm]

/-! ### 2:C4 — the frame moves the labels of one complex -/

variable {p : Nat} [Pos p]

/-- The action reading of the vertex `(a, m)` in the frame with drive `g`: `a · g^m`. -/
def label (g : Shell p) (a : Shell p) (m : Nat) : Shell p := a * g ^ m

/-- 2:C4 (Prop. 3.5) — the complex is one for every generator; the frame `g' = g^u` moves the
labels by the reindexing `ρ_u`: `label g' (a, m) = label g (a, u·m mod n)`. -/
theorem label_covariance {κ : Nat} {g : Shell p} (F : Shell.Frame p κ g) (u : Nat) (a : Shell p) (m : Nat) :
    label (g ^ u) a m = label g a (rho (p - 1) u m) := by
  unfold label rho
  rw [← Shell.pow_mul, F.pow_mod (u * m)]

end Geometry
end FRC

/-! inlined: FrcCore/Complex.lean -/

/-!
# FrcCore.Complex — the orbital shell and its spherical completion, coded and decided

The completion of the orbital shell `S_p` (Def. 3.1 of 2-geometry) as a finite cell complex on vertex codes:
`N = 0`, the interior vertices `(a, m)` for `1 ≤ a ≤ π − 1`, `m < n`, and `S`; the faces as cyclic vertex lists
(north triangles, quadrilaterals, south triangles); the edges as the faces' sides. `closed p` checks that every
edge lies in exactly two faces and that every vertex link is a single cycle (2:C3, the exhaustive incidence of
the ledger); `cellular p u` checks whether the reindexing `ρ_u` carries faces to faces (2:B4); `poleExchange`
checks the meridian reversal on the completion. Everything is a computation the kernel evaluates by `decide`.
No axioms.
-/

namespace FRC
namespace Complex

/-- The vertex code of `(a, m)` on the shell with `n` phases: `1 + (a − 1)·n + m`. -/
def vtx (n a m : Nat) : Nat := 1 + (a - 1) * n + m % n

/-- The south pole: the vertex after the last interior latitude `a = π − 1`. -/
def south (n pi : Nat) : Nat := 1 + (pi - 1) * n

/-- The faces of the completion, as vertex lists. -/
def faces (n pi : Nat) : List (List Nat) :=
  let north := (List.range n).map fun m => [0, vtx n 1 m, vtx n 1 (m + 1)]
  let quads := ((List.range (pi - 2)).map fun a' => (List.range n).map fun m =>
      [vtx n (a' + 1) m, vtx n (a' + 2) m, vtx n (a' + 2) (m + 1), vtx n (a' + 1) (m + 1)]).foldr (· ++ ·) []
  let souths := (List.range n).map fun m => [vtx n (pi - 1) m, south n pi, vtx n (pi - 1) (m + 1)]
  north ++ quads ++ souths

/-- The sides of a face, as unordered pairs `(min, max)`. -/
def sides : List Nat → List (Nat × Nat)
  | [] => []
  | f@(v :: _) =>
    let rec go : List Nat → List (Nat × Nat)
      | [] => []
      | [w] => [(min w v, max w v)]
      | w :: (w' :: rest) => (min w w', max w w') :: go (w' :: rest)
    go f

def vertexCount (n pi : Nat) : Nat := south n pi + 1

/-- A face with its sides computed once: `(vertices, sides)`. -/
abbrev Face := List Nat × List (Nat × Nat)

def withSides (fs : List (List Nat)) : List Face := fs.map fun f => (f, sides f)

/-- Two faces are adjacent around `v` when they share a side through `v`. -/
def adjacentAt (v : Nat) (f f' : Face) : Bool :=
  f.2.any fun s => (s.1 == v || s.2 == v) && f'.2.contains s

/-- The neighbours of `cur` around `v` other than `prev` (and `cur` itself). -/
def nextFaces (v : Nat) (L : List Face) (prev cur : Face) : List Face :=
  L.filter fun f' => !(f'.1 == cur.1) && !(f'.1 == prev.1) && adjacentAt v cur f'

/-- Walk the link from `f0` along `cur`, never turning back, for `fuel` steps; the number of steps taken until
`f0` is reached again (`fuel` if never). -/
def walk (v : Nat) (L : List Face) (f0 : Face) : Nat → Face → Face → Nat → Nat
  | 0, _, _, k => k
  | fuel + 1, prev, cur, k =>
    match nextFaces v L prev cur with
    | f' :: [] => if f'.1 == f0.1 then k + 1 else walk v L f0 fuel cur f' (k + 1)
    | [] => fuel + k + 1
    | _ :: _ :: _ => fuel + k + 1

/-- The link of `v` is a single cycle: every face around `v` has exactly two neighbours there, and the walk from
the first face returns to it after exactly `|L|` steps. -/
def linkIsCycle (fs : List Face) (v : Nat) : Bool :=
  let L := fs.filter fun f => f.1.contains v
  match L with
  | [] => false
  | f0 :: _ =>
    L.all (fun f => (L.filter (fun f' => !(f'.1 == f.1) && adjacentAt v f f')).length == 2) &&
    (match nextFaces v L f0 f0 with
     | f1 :: _ => walk v L f0 L.length f0 f1 1 == L.length
     | [] => false)

/-- The number of occurrences of `s` in `E`. -/
def count (s : Nat × Nat) : List (Nat × Nat) → Nat
  | [] => 0
  | e :: E => (if e == s then 1 else 0) + count s E

/-- Every side of every face lies in exactly two faces: the sides are bucketed by their smaller vertex and each
side occurs exactly twice in its bucket. -/
def edgesInTwoFaces (fs : List (List Nat)) : Bool :=
  let E := (withSides fs).foldr (fun f acc => f.2 ++ acc) []
  let V := fs.foldr (fun f acc => f.foldr (fun w acc' => if acc'.contains w then acc' else w :: acc') acc) []
  V.all fun v =>
    let B := E.filter fun s => s.1 == v
    B.all fun s => count s B == 2

/-- 2:C3, the exhaustive incidence: the completion is a closed surface. -/
def closed (p : Nat) : Bool :=
  let n := p - 1
  let pi := n / 2
  let fs := faces n pi
  edgesInTwoFaces fs && (List.range (vertexCount n pi)).all fun v => linkIsCycle (withSides fs) v

/-- The reindexing `ρ_u` on vertex codes: `(a, m) ↦ (a, u·m mod n)`, the poles fixed. -/
def rhoV (n pi u : Nat) (v : Nat) : Nat :=
  if v == 0 then 0 else if v == south n pi then v else
    let a := (v - 1) / n + 1
    let m := (v - 1) % n
    vtx n a (u * m)

/-- The meridian reversal on the completion: `N ↔ S`, `(a, m) ↦ (π − a, m)`. -/
def sigmaV (n pi : Nat) (v : Nat) : Nat :=
  if v == 0 then south n pi else if v == south n pi then 0 else
    let a := (v - 1) / n + 1
    let m := (v - 1) % n
    vtx n (pi - a) m

/-- A vertex map is cellular when it carries every face onto a face (as vertex sets). -/
def cellularMap (fs : List (List Nat)) (φ : Nat → Nat) : Bool :=
  fs.all fun f => fs.any fun f' => (f.map φ).all (fun w => f'.contains w) && f'.all (fun w => (f.map φ).contains w)

/-- 2:B4 — whether `ρ_u` is a cellular automorphism of the completion. -/
def cellular (p u : Nat) : Bool :=
  let n := p - 1
  let pi := n / 2
  cellularMap (faces n pi) (rhoV n pi u)

/-- 2:B4 — whether the pole exchange is cellular on the completion. -/
def poleExchange (p : Nat) : Bool :=
  let n := p - 1
  let pi := n / 2
  cellularMap (faces n pi) (sigmaV n pi)

/-- 2:C2 [value] — the counts on `𝔽₁₃`: `62` vertices, `72` faces of the completion. -/
theorem counts13 : vertexCount 12 6 = 62 ∧ (faces 12 6).length = 72 := by decide +kernel

/-- 2:C3 [value] — the completion is a closed surface on `𝔽₅`, by exhaustive incidence. -/
theorem closed5 : closed 5 = true := by decide +kernel
/-- 2:C3 [value] — the completion is a closed surface on `𝔽₁₃` (62 vertices, 72 faces). -/
theorem closed13 : closed 13 = true := by decide +kernel
/-- 2:C3 [value] — the completion is a closed surface on `𝔽₁₇` (114 vertices, 128 faces); the kernel decides
it in a few seconds. -/
theorem closed17 : closed 17 = true := by decide +kernel


/-- The orbital shell before the collapse: the terminal latitude `a = π` kept, so the last ring of quadrilaterals
ends on it and nothing closes over it. -/
def facesOpen (n pi : Nat) : List (List Nat) :=
  let north := (List.range n).map fun m => [0, vtx n 1 m, vtx n 1 (m + 1)]
  let quads := ((List.range (pi - 1)).map fun a' => (List.range n).map fun m =>
      [vtx n (a' + 1) m, vtx n (a' + 2) m, vtx n (a' + 2) (m + 1), vtx n (a' + 1) (m + 1)]).foldr (· ++ ·) []
  north ++ quads

/-- 2:C3, 2:B4 [value] — the shell itself is not closed (its terminal latitude is a boundary: those sides lie in
one face only), so the meridian reversal has nothing to act on before the collapse. -/
theorem open13 : edgesInTwoFaces (facesOpen 12 6) = false ∧ (facesOpen 12 6).length = 72 := by decide +kernel

/-- 2:B4, 2:C4 [value] — on `𝔽₁₃` (`n = 12`) the reindexing `ρ_u` is cellular exactly for `u ∈ {1, 11}` among the
units `{1, 5, 7, 11}`, and the pole exchange is cellular on the completion. -/
theorem census13 :
    cellular 13 1 = true ∧ cellular 13 5 = false ∧ cellular 13 7 = false ∧ cellular 13 11 = true ∧
    poleExchange 13 = true := by decide +kernel

end Complex
end FRC

/-! inlined: FrcCore/Instances.lean -/

/-!
# FrcCore.Instances — concrete shells, decided by computation

Every statement here is closed by `decide`: the kernel evaluates the shell arithmetic (through its
accelerated `Nat` operations) and the proof term is `of_decide_eq_true rfl`. No axiom, no library.
-/

namespace FRC
namespace Shell

/-- 00:C1 on `𝔽₁₃`: the frame `(τ; 0, 1, 2)` of capacity `3` — `2` is primitive (decided). -/
theorem frame13 : Frame 13 3 (2 : Shell 13) := ⟨rfl, Nat.zero_lt_succ 2, by decide⟩

/-- 00:A8 on `𝔽₁₃`: the drive generates — checked directly, and proved for every frame by `Frame.generates`. -/
theorem generates13 : Generates (2 : Shell 13) 12 := by decide

/-- 1:B3, 2:D3 [value] — on `𝔽₁₃(τ; 0, 1, 2)`: `i = −2³ = 5`, `i² = −1`, `−i = 8`, `π = 6`, `2^6 = −1`,
`e = 2^5 = 6`. -/
theorem s13_datum :
    Frame.quarterTurn (2 : Shell 13) 3 = 5 ∧ (5 : Shell 13) * 5 = -1 ∧ -(5 : Shell 13) = 8 ∧
    (2 : Shell 13) ^ 6 = -1 ∧ (2 : Shell 13) ^ 5 = 6 := by decide

/-- 2:D6 [value] — the Euler identity on `𝔽₁₃`: the representative `5` of `i` is odd, `e^{iπ} = −1`. -/
theorem s13_euler : ((2 : Shell 13) ^ 5) ^ (5 * 6) = -1 := by decide

/-- 00:C1 on `𝔽₁₇`: two frames, `g = 3` and `g = 6`. -/
theorem frame17a : Frame 17 4 (3 : Shell 17) := ⟨rfl, Nat.zero_lt_succ 3, by decide⟩
theorem frame17b : Frame 17 4 (6 : Shell 17) := ⟨rfl, Nat.zero_lt_succ 3, by decide⟩

set_option maxRecDepth 20000 in
/-- 2:D6 [value], 00:C14 — on `𝔽₁₇` the frame `g = 3` reads `i = 4` (even: `e^{iπ} = +1`) and the frame
`g = 6` reads `i = 13` (odd: `e^{iπ} = −1`); `6 = 3^{15}` with `15 ≡ 3 (mod 4)` flips the orientation. -/
theorem s17_orientation :
    Frame.quarterTurn (3 : Shell 17) 4 = 4 ∧ Frame.quarterTurn (6 : Shell 17) 4 = 13 ∧
    ((3 : Shell 17) ^ 4) ^ (4 * 8) = 1 ∧ ((6 : Shell 17) ^ 13) ^ (13 * 8) = -1 ∧
    (3 : Shell 17) ^ 15 = 6 := by decide

/-- 00:C1 on `𝔽₂₉`: the frame `(τ; 0, 1, 2)`, capacity `7`. -/
theorem frame29 : Frame 29 7 (2 : Shell 29) := ⟨rfl, Nat.zero_lt_succ 6, by decide⟩

/-- 1:B2 [value] — on `𝔽₁₃` the fourth roots of unity are `{1, 5, 12, 8}`, and every other nonzero
residue has four distinct companions `{x, −x, x⁻¹, −x⁻¹}`: the two Klein orbits `{2, 11, 7, 6}` and
`{3, 10, 9, 4}`. -/
theorem s13_klein :
    (∀ x : Fin 13, (x.val = 1 ∨ x.val = 5 ∨ x.val = 12 ∨ x.val = 8) ↔ (ofNat x.val : Shell 13) ^ 4 = 1) ∧
    (2 : Shell 13) * 7 = 1 ∧ (3 : Shell 13) * 9 = 1 := by decide

/-- 2:B3 [value] — on `𝔽₁₃` the generators are `2^u` with `u ∈ {1, 5, 7, 11}` (the units mod `12`): `6 = 2^5`
is primitive, `4 = 2^2` is not; `5, 7, 11` are invertible mod `12`, `2` is not. -/
theorem s13_orbit :
    Coprime 5 12 ∧ Coprime 7 12 ∧ Coprime 11 12 ∧ ¬ Coprime 2 12 ∧
    IsPrimitive (6 : Shell 13) 12 ∧ ¬ IsPrimitive (4 : Shell 13) 12 ∧ (2 : Shell 13) ^ 5 = 6 := by decide

end Shell
end FRC
