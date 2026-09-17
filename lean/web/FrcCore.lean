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

theorem add_sub_of_le {n m : Nat} (h : m ≤ n) : m + (n - m) = n := by
  rw [Nat.add_comm]; exact sub_add_cancel h

theorem sub_lt_of_lt_add {x y z : Nat} (h : x < y + z) (hy : y ≤ x) : x - y < z := by
  refine Nat.lt_of_add_lt_add_right (n := y) ?_
  rw [sub_add_cancel hy, Nat.add_comm z y]
  exact h

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

/-- 1:B2 (Theorem 1 of 1-algebra) — off the fourth roots of unity, `x`, `−x`, `x⁻¹`, `−x⁻¹` are four
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

/-- 1:B4 (Definition 2 of 1-algebra, corrected) — in the affine frame `(a, b)` the multiplicative unit
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

/-- 1:F1 (Theorem 3) — `2s = 0 ⇒ s = 0`: the additive cycle has no element of order two; the antipode of
the origin is not a residue. -/
theorem no_south_pole (F : Frame p κ g) (s : Shell p) (h : (2 : Shell p) * s = 0) : s = 0 :=
  match F.mul_eq_zero h with
  | .inl e => absurd e F.two_ne_zero
  | .inr e => e

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

/-- 1:D5, the range obstruction (Theorem 2 of 1-algebra refuted) at `p = 13`, `g = 2`: every grid point
`x / 2^n` with `x < 13` and `n ≥ 3` is at most `3/2` — as the integer statement `2x ≤ 3·2^n`. -/
theorem approx_theorem_refuted (n x : Nat) (hn : 3 ≤ n) (hx : x < 13) : 2 * x ≤ 3 * 2 ^ n := by
  have h8 : 2 ^ 3 ≤ 2 ^ n := Nat.pow_le_pow_right (Nat.zero_lt_succ 1) hn
  have h1 : 2 * x ≤ 2 * 12 := Nat.mul_le_mul_left 2 (Nat.le_of_lt_succ hx)
  have h2 : 3 * 2 ^ 3 ≤ 3 * 2 ^ n := Nat.mul_le_mul_left 3 h8
  exact Nat.le_trans h1 h2

end Frame
end Shell
end FRC

/-! inlined: FrcCore/Geometry.lean -/

/-!
# FrcCore.Geometry — 2-geometry rows on the core

2:C2 (the cell counts of the orbital shell and its completion, as identities of natural numbers) and
2:E3 (the fixed-shell refutation at `(13, 2)`: no grid point `x/2^n`, `x ≤ 6`, lies in `(3/4, 1)`, as
the integer statement `¬(3·2^n < 4x ∧ x < 2^n)`). No axioms.
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

/-- 2:E3 — the fixed-shell refutation at `p = 13`, `g = 2` (window `x ≤ 6`): no grid point `x / 2^n`
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

end Geometry
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
