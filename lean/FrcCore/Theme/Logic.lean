import FrcCore.Nat
import FrcCore.Pigeonhole
import FrcCore.Shell
import FrcCore.Series

/-!
# FrcCore.Theme.Logic — the bounded language over a finite structure and its counting (the logic theme, task LM17)

An explicit language of `Δ₀` formulas with two evaluators, over `ℕ` and in a frame `W_N` where overflow makes an atom
false, and the bounded stability schema: every formula takes its standard value in every frame above its bound (5:B6).
The counting behind the paradoxes of infinity and finite Gödel: fewer than `s^(K+1)` records of length `≤ K` and no
mirror of a larger frame (5:C2; `no_mirror` is in the base's `Series.lean` since task LM23); an iteration on `n`
states repeats within `n` steps (5:C5, 5:E5); Cantor on the finite frame (5:D3); the least element (5:E1, 5:E2); on a
finite carrier an injective map is onto, a part with fewer states identifies two elements, `m + 1` sentences outnumber
`m` elements (25:C1, 25:C5, 25:D1); the count of a Boolean predicate; dense codings need `a^n ≤ m^k` (25:F4). Moved
from 5-reductio and 25-godel, whose modules keep every old name. No axioms.
-/

namespace FRC.Logic

/-! ### the maximum, from its definition -/

/-- `mx a b`, the larger of two naturals, with its two bounds proved from the definition. -/
def mx (a b : Nat) : Nat := if a ≤ b then b else a

theorem le_mx_left (a b : Nat) : a ≤ mx a b := by
  unfold mx
  match Nat.decLe a b with
  | isTrue h => rw [ite_eq_left h]; exact h
  | isFalse h => rw [ite_eq_right h]; exact Nat.le_refl a

theorem le_mx_right (a b : Nat) : b ≤ mx a b := by
  unfold mx
  match Nat.decLe a b with
  | isTrue h => rw [ite_eq_left h]; exact Nat.le_refl b
  | isFalse h => rw [ite_eq_right h]; exact Nat.le_of_lt (Nat.lt_of_not_le h)

theorem lt_of_mx_lt_left {a b N : Nat} (h : mx a b < N) : a < N := Nat.lt_of_le_of_lt (le_mx_left a b) h
theorem lt_of_mx_lt_right {a b N : Nat} (h : mx a b < N) : b < N := Nat.lt_of_le_of_lt (le_mx_right a b) h

/-! ### 5:B6 — the bounded stability schema for an explicit `Δ₀` language -/

/-- Terms: variables (de Bruijn indices), `0`, `1`, sum, product. -/
inductive Term where
  | var : Nat → Term
  | zero : Term
  | one : Term
  | add : Term → Term → Term
  | mul : Term → Term → Term

/-- `Δ₀` formulas: atoms `s = t`, `s < t`, negation, conjunction, and the bounded quantifier `∀ x ≤ t, φ`
(`x` is variable `0` in `φ`, the other variables shift up; `t` is read in the outer environment). -/
inductive Form where
  | eq : Term → Term → Form
  | lt : Term → Term → Form
  | neg : Form → Form
  | conj : Form → Form → Form
  | ball : Term → Form → Form

/-- The environment extended by a value for variable `0`. -/
def cons (x : Nat) (env : Nat → Nat) : Nat → Nat
  | 0 => x
  | i + 1 => env i

/-- Terms over `ℕ`. -/
def evalT (env : Nat → Nat) : Term → Nat
  | .var i => env i
  | .zero => 0
  | .one => 1
  | .add s t => evalT env s + evalT env t
  | .mul s t => evalT env s * evalT env t

/-- `f 0 && … && f (n − 1)`. -/
def allBelow (f : Nat → Bool) : Nat → Bool
  | 0 => true
  | n + 1 => f n && allBelow f n

/-- Formulas over `ℕ` (the standard value). -/
def evalF (env : Nat → Nat) : Form → Bool
  | .eq s t => decide (evalT env s = evalT env t)
  | .lt s t => decide (evalT env s < evalT env t)
  | .neg φ => !(evalF env φ)
  | .conj φ ψ => evalF env φ && evalF env ψ
  | .ball t φ => allBelow (fun x => evalF (cons x env) φ) (evalT env t + 1)

/-- Terms in the frame `W_N`: a value is defined only while every intermediate value stays below `N`
(overflow: `A(x, y, z)` fails for `x + y ≥ N`). -/
def evalT? (N : Nat) (env : Nat → Nat) : Term → Option Nat
  | .var i => if env i < N then some (env i) else none
  | .zero => if 0 < N then some 0 else none
  | .one => if 1 < N then some 1 else none
  | .add s t => match evalT? N env s, evalT? N env t with
      | some a, some b => if a + b < N then some (a + b) else none
      | some _, none => none
      | none, some _ => none
      | none, none => none
  | .mul s t => match evalT? N env s, evalT? N env t with
      | some a, some b => if a * b < N then some (a * b) else none
      | some _, none => none
      | none, some _ => none
      | none, none => none

/-- Formulas in the frame `W_N`: an atom with an undefined term is false, a bounded quantifier is guarded by
the definedness of its bound (the transcription `φ*` of the paper). -/
def evalF? (N : Nat) (env : Nat → Nat) : Form → Bool
  | .eq s t => match evalT? N env s, evalT? N env t with
      | some a, some b => decide (a = b)
      | some _, none => false
      | none, some _ => false
      | none, none => false
  | .lt s t => match evalT? N env s, evalT? N env t with
      | some a, some b => decide (a < b)
      | some _, none => false
      | none, some _ => false
      | none, none => false
  | .neg φ => !(evalF? N env φ)
  | .conj φ ψ => evalF? N env φ && evalF? N env ψ
  | .ball t φ => match evalT? N env t with
      | some b => allBelow (fun x => evalF? N (cons x env) φ) (b + 1)
      | none => false

/-- The largest value a term's evaluation touches. -/
def boundT (env : Nat → Nat) : Term → Nat
  | .var i => env i
  | .zero => 0
  | .one => 1
  | .add s t => mx (mx (boundT env s) (boundT env t)) (evalT env s + evalT env t)
  | .mul s t => mx (mx (boundT env s) (boundT env t)) (evalT env s * evalT env t)

/-- `max (f 0, …, f (n − 1))`. -/
def maxBelow (f : Nat → Nat) : Nat → Nat
  | 0 => 0
  | n + 1 => mx (f n) (maxBelow f n)

/-- `t(φ)`, the largest integer referenced in the evaluation of `φ` over `ℕ`. -/
def boundF (env : Nat → Nat) : Form → Nat
  | .eq s t => mx (boundT env s) (boundT env t)
  | .lt s t => mx (boundT env s) (boundT env t)
  | .neg φ => boundF env φ
  | .conj φ ψ => mx (boundF env φ) (boundF env ψ)
  | .ball t φ => mx (boundT env t) (maxBelow (fun x => boundF (cons x env) φ) (evalT env t + 1))

theorem le_maxBelow (f : Nat → Nat) : ∀ {n x : Nat}, x < n → f x ≤ maxBelow f n
  | 0, x, hx => absurd hx (Nat.not_lt_zero x)
  | n + 1, x, hx =>
    match Nat.decEq x n with
    | isTrue e => by rw [e]; exact le_mx_left _ _
    | isFalse e =>
      have hlt : x < n := Nat.lt_of_le_of_ne (Nat.le_of_lt_succ hx) e
      Nat.le_trans (le_maxBelow f hlt) (le_mx_right _ _)

theorem allBelow_congr {f g : Nat → Bool} : ∀ {n : Nat}, (∀ x, x < n → f x = g x) → allBelow f n = allBelow g n
  | 0, _ => rfl
  | n + 1, h => by
    show (f n && allBelow f n) = (g n && allBelow g n)
    rw [h n (Nat.lt_succ_self n), allBelow_congr (fun x hx => h x (Nat.lt_succ_of_lt hx))]

/-- 5:B6 (terms) — below its bound a term is defined in the frame, with its standard value. -/
theorem evalT_frame (N : Nat) (env : Nat → Nat) : ∀ (t : Term), boundT env t < N → evalT? N env t = some (evalT env t)
  | .var i, h => by
    have h' : env i < N := h
    show (if env i < N then some (env i) else none) = some (env i); rw [ite_eq_left h']
  | .zero, h => by
    have h' : 0 < N := h
    show (if 0 < N then some 0 else none) = some 0; rw [ite_eq_left h']
  | .one, h => by
    have h' : 1 < N := h
    show (if 1 < N then some 1 else none) = some 1; rw [ite_eq_left h']
  | .add s t, h => by
    have hs := evalT_frame N env s (lt_of_mx_lt_left (lt_of_mx_lt_left h))
    have ht := evalT_frame N env t (lt_of_mx_lt_right (lt_of_mx_lt_left h))
    show (match evalT? N env s, evalT? N env t with
      | some a, some b => if a + b < N then some (a + b) else none
      | some _, none => none
      | none, some _ => none
      | none, none => none) = some (evalT env s + evalT env t)
    rw [hs, ht]
    show (if evalT env s + evalT env t < N then some (evalT env s + evalT env t) else none) = some (evalT env s + evalT env t)
    rw [ite_eq_left (lt_of_mx_lt_right h)]
  | .mul s t, h => by
    have hs := evalT_frame N env s (lt_of_mx_lt_left (lt_of_mx_lt_left h))
    have ht := evalT_frame N env t (lt_of_mx_lt_right (lt_of_mx_lt_left h))
    show (match evalT? N env s, evalT? N env t with
      | some a, some b => if a * b < N then some (a * b) else none
      | some _, none => none
      | none, some _ => none
      | none, none => none) = some (evalT env s * evalT env t)
    rw [hs, ht]
    show (if evalT env s * evalT env t < N then some (evalT env s * evalT env t) else none) = some (evalT env s * evalT env t)
    rw [ite_eq_left (lt_of_mx_lt_right h)]

/-- 5:B6 (Theorem stability, schema form) — every `Δ₀` formula takes its standard value in every frame `W_N`
with `N > t(φ)`: `W_N ⊨ φ* ⟺ ℕ ⊨ φ`, for every environment, by induction on the formula. -/
theorem stable (N : Nat) : ∀ (φ : Form) (env : Nat → Nat), boundF env φ < N → evalF? N env φ = evalF env φ
  | .eq s t, env, h => by
    show (match evalT? N env s, evalT? N env t with
      | some a, some b => decide (a = b)
      | some _, none => false
      | none, some _ => false
      | none, none => false) = decide (evalT env s = evalT env t)
    rw [evalT_frame N env s (lt_of_mx_lt_left h), evalT_frame N env t (lt_of_mx_lt_right h)]
  | .lt s t, env, h => by
    show (match evalT? N env s, evalT? N env t with
      | some a, some b => decide (a < b)
      | some _, none => false
      | none, some _ => false
      | none, none => false) = decide (evalT env s < evalT env t)
    rw [evalT_frame N env s (lt_of_mx_lt_left h), evalT_frame N env t (lt_of_mx_lt_right h)]
  | .neg φ, env, h => by
    show (!(evalF? N env φ)) = !(evalF env φ)
    rw [stable N φ env h]
  | .conj φ ψ, env, h => by
    show (evalF? N env φ && evalF? N env ψ) = (evalF env φ && evalF env ψ)
    rw [stable N φ env (lt_of_mx_lt_left h), stable N ψ env (lt_of_mx_lt_right h)]
  | .ball t φ, env, h => by
    show (match evalT? N env t with
      | some b => allBelow (fun x => evalF? N (cons x env) φ) (b + 1)
      | none => false) = allBelow (fun x => evalF (cons x env) φ) (evalT env t + 1)
    rw [evalT_frame N env t (lt_of_mx_lt_left h)]
    show allBelow (fun x => evalF? N (cons x env) φ) (evalT env t + 1) = allBelow (fun x => evalF (cons x env) φ) (evalT env t + 1)
    exact allBelow_congr (fun x hx =>
      stable N φ (cons x env) (Nat.lt_of_le_of_lt (le_maxBelow (fun x => boundF (cons x env) φ) hx) (lt_of_mx_lt_right h)))

/-! ### 5:C2 — records and the mirror -/

/-- The number of strings of length at most `K` over `s` letters, `Σ_{i ≤ K} s^i`. -/
def records (s : Nat) : Nat → Nat
  | 0 => 1
  | K + 1 => records s K + s ^ (K + 1)

/-- 5:C2 (the count) — fewer than `s^(K+1)` records exist for an alphabet of `s ≥ 2` letters. -/
theorem records_lt (s : Nat) (hs : 2 ≤ s) : ∀ K, records s K < s ^ (K + 1)
  | 0 => by
    show 1 < s ^ 1
    rw [Nat.pow_succ, Nat.pow_zero, Nat.one_mul]
    exact Nat.lt_of_lt_of_le (Nat.lt_succ_self 1) hs
  | K + 1 => by
    show records s K + s ^ (K + 1) < s ^ (K + 1 + 1)
    have h1 : records s K + s ^ (K + 1) < s ^ (K + 1) + s ^ (K + 1) := Nat.add_lt_add_right (records_lt s hs K) _
    have h2 : s ^ (K + 1) + s ^ (K + 1) ≤ s ^ (K + 1) * s := by
      rw [← Nat.mul_two]; exact Nat.mul_le_mul_left _ hs
    exact Nat.lt_of_lt_of_le h1 h2

/-! ### 5:C5, 5:E5 — an iteration on finitely many states repeats: periodic König and bounded halting -/

/-- `iter f x k = f^k x`. -/
def iter (f : Nat → Nat) (x : Nat) : Nat → Nat
  | 0 => x
  | k + 1 => f (iter f x k)

theorem iter_lt (f : Nat → Nat) {n : Nat} (hf : ∀ y, y < n → f y < n) {x : Nat} (hx : x < n) :
    ∀ k, iter f x k < n
  | 0 => hx
  | k + 1 => hf _ (iter_lt f hf hx k)

theorem iter_add (f : Nat → Nat) (x : Nat) (i : Nat) : ∀ k, iter f x (i + k) = iter f (iter f x i) k
  | 0 => rfl
  | k + 1 => by show f (iter f x (i + k)) = f (iter f (iter f x i) k); rw [iter_add f x i k]

/-- 5:E5, 5:C5 (Lemma periodic König, the pigeonhole) — on `n` states the iteration from `x` revisits a state within
`n` steps: some `i < j ≤ n` have `f^i x = f^j x`. -/
theorem repeat_below (f : Nat → Nat) (n : Nat) (hf : ∀ y, y < n → f y < n) (x : Nat) (hx : x < n) :
    ∃ i j, i < j ∧ j ≤ n ∧ iter f x i = iter f x j :=
  have dec : Decidable (∃ j, j < n + 1 ∧ ∃ i, i < j ∧ iter f x i = iter f x j) :=
    @FRC.Shell.decExistsLT (fun j => ∃ i, i < j ∧ iter f x i = iter f x j)
      (fun j => FRC.Shell.decExistsLT (fun i => iter f x i = iter f x j) j) (n + 1)
  match dec with
  | isTrue ⟨j, hj, i, hij, e⟩ => ⟨i, j, hij, Nat.le_of_lt_succ hj, e⟩
  | isFalse hno =>
    have hinj : ∀ i j, i < n + 1 → j < n + 1 → iter f x i = iter f x j → i = j := fun i j hi hj e =>
      match Nat.lt_or_ge i j with
      | Or.inl hlt => absurd ⟨j, hj, i, hlt, e⟩ hno
      | Or.inr hge => match Nat.lt_or_ge j i with
        | Or.inl hlt => absurd ⟨i, hi, j, hlt, e.symm⟩ hno
        | Or.inr hge' => Nat.le_antisymm hge' hge
    have hnd := FRC.Shell.imageList_nodup hinj (Nat.le_refl (n + 1))
    have hb : ∀ e, Pigeonhole.mem e (FRC.Shell.imageList (iter f x) (n + 1)) → e < n := fun _ he =>
      match FRC.Shell.mem_imageList he with
      | ⟨k, _, ek⟩ => ek ▸ iter_lt f hf hx k
    have := Pigeonhole.length_le_of_nodup_lt n _ hnd hb
    by rw [FRC.Shell.imageList_length] at this; exact absurd this (Nat.not_succ_le_self n)

theorem sub_pos {i j : Nat} (h : i < j) : 0 < j - i :=
  match Nat.decEq (j - i) 0 with
  | isTrue e =>
    have hj : j = i := by rw [← FRC.Nat.add_sub_of_le (Nat.le_of_lt h), e, Nat.add_zero]
    absurd (hj ▸ h) (Nat.lt_irrefl i)
  | isFalse e => Nat.pos_of_ne_zero e

/-- 5:E5 — the walk is eventually periodic: from step `i` on, period `p = j − i` with `0 < p ≤ n`,
`f^(i+k+p) x = f^(i+k) x` for every `k`. -/
theorem eventually_periodic (f : Nat → Nat) (n : Nat) (hf : ∀ y, y < n → f y < n) (x : Nat) (hx : x < n) :
    ∃ i p, 0 < p ∧ p ≤ n ∧ ∀ k, iter f x (i + k + p) = iter f x (i + k) :=
  match repeat_below f n hf x hx with
  | ⟨i, j, hij, hjn, e⟩ =>
    ⟨i, j - i, sub_pos hij, Nat.le_trans (Nat.sub_le j i) hjn, fun k => by
      rw [Nat.add_right_comm, FRC.Nat.add_sub_of_le (Nat.le_of_lt hij), iter_add f x j k, iter_add f x i k, e]⟩

/-- 5:C5 (horizon separation) — a run on `n` states reaches a state `h` iff it reaches it within `n` steps: halting for bounded space is decided from above by `n` steps of simulation. -/
theorem halts_iff_halts_below (f : Nat → Nat) (n : Nat) (hf : ∀ y, y < n → f y < n) (h : Nat)
    (x : Nat) (hx : x < n) : (∃ k, iter f x k = h) ↔ ∃ k, k ≤ n ∧ iter f x k = h :=
  ⟨fun ⟨k, hk⟩ =>
    match repeat_below f n hf x hx with
    | ⟨i, j, hij, hjn, e⟩ =>
      match Nat.lt_or_ge k j with
      | Or.inl hkj => ⟨k, Nat.le_of_lt (Nat.lt_of_lt_of_le hkj hjn), hk⟩
      | Or.inr hjk =>
        -- the run is periodic from `i` with period `p = j − i`; reduce `k − i` modulo `p`
        have hp : 0 < j - i := sub_pos hij
        have per : ∀ q r, iter f x (i + (r + (j - i) * q)) = iter f x (i + r) := fun q r => by
          induction q with
          | zero => rw [Nat.mul_zero, Nat.add_zero]
          | succ q ih =>
            rw [Nat.mul_succ, ← Nat.add_assoc r ((j - i) * q) (j - i), Nat.add_comm (r + (j - i) * q) (j - i),
              ← Nat.add_assoc i (j - i) (r + (j - i) * q), FRC.Nat.add_sub_of_le (Nat.le_of_lt hij), iter_add f x j,
              ← e, ← iter_add f x i, ih]
        match FRC.Nat.mod_spec (j - i) hp (k - i) with
        | ⟨q, hq⟩ =>
          have hr : (k - i) % (j - i) < j - i := Nat.mod_lt _ hp
          have hk' : k = i + ((k - i) % (j - i) + (j - i) * q) := by
            rw [Nat.add_comm ((k - i) % (j - i)) _, ← hq, FRC.Nat.add_sub_of_le (Nat.le_trans (Nat.le_of_lt hij) hjk)]
          ⟨i + (k - i) % (j - i),
            Nat.le_of_lt (Nat.lt_of_lt_of_le (Nat.add_lt_add_left hr i)
              (by rw [FRC.Nat.add_sub_of_le (Nat.le_of_lt hij)]; exact hjn)),
            by rw [← per q, ← hk']; exact hk⟩,
   fun ⟨k, _, hk⟩ => ⟨k, hk⟩⟩

/-! ### 5:D3 — Cantor's theorem on the finite frame -/

/-- 5:D3 (Remark, the external diagonal) — Cantor's theorem holds in every finite frame: `n < 2^n`. -/
theorem cantor_finite (n : Nat) : n < 2 ^ n := Nat.lt_two_pow_self

/-! ### 5:E1, 5:E2 — definable choice by the least element -/

/-- The least `x < n` with `P x`, if any: the choice function `ch(A) = min A` of Definition global-choice. -/
def leastBelow (P : Nat → Bool) : Nat → Option Nat
  | 0 => none
  | n + 1 => match leastBelow P n with
    | some x => some x
    | none => if P n then some n else none

/-- 5:E1 — a nonempty family has a choice: if some `x < n` has `P x`, `leastBelow P n` is defined. -/
theorem leastBelow_some (P : Nat → Bool) : ∀ (n x : Nat), x < n → P x = true → ∃ y, leastBelow P n = some y
  | 0, x, hx, _ => absurd hx (Nat.not_lt_zero x)
  | n + 1, x, hx, hP =>
    match hl : leastBelow P n with
    | some y => ⟨y, by
        show (match leastBelow P n with
          | some x => some x
          | none => if P n then some n else none) = some y
        rw [hl]⟩
    | none =>
      match Nat.decEq x n with
      | isTrue e => ⟨n, by
          show (match leastBelow P n with
            | some x => some x
            | none => if P n then some n else none) = some n
          rw [hl]
          show (if P n then some n else none) = some n
          have hPn : P n = true := e ▸ hP
          rw [hPn, ite_eq_left rfl]⟩
      | isFalse e =>
        absurd (leastBelow_some P n x (Nat.lt_of_le_of_ne (Nat.le_of_lt_succ hx) e) hP)
          (fun ⟨z, hz⟩ => nomatch (hl ▸ hz : (none : Option Nat) = some z))

/-- 5:E1 (Proposition finite-choice) — the choice is a member, below the bound, and the least one. -/
theorem leastBelow_spec (P : Nat → Bool) : ∀ (n x : Nat), leastBelow P n = some x →
    x < n ∧ P x = true ∧ ∀ y, y < x → P y = false
  | 0, x, h => nomatch (h : (none : Option Nat) = some x)
  | n + 1, x, h => by
    have h' : (match leastBelow P n with
      | some x => some x
      | none => if P n then some n else none) = some x := h
    clear h
    revert h'
    match hl : leastBelow P n with
    | some y =>
      intro h'
      have e : y = x := Option.some.inj h'
      have := leastBelow_spec P n y hl
      exact ⟨Nat.lt_succ_of_lt (e ▸ this.1), e ▸ this.2.1, e ▸ this.2.2⟩
    | none =>
      intro h'
      have h'' : (if P n then some n else none) = some x := h'
      match hP : P n with
      | true =>
        rw [hP, ite_eq_left rfl] at h''
        have e : n = x := Option.some.inj h''
        refine ⟨Nat.lt_succ_of_le (Nat.le_of_eq e.symm), e ▸ hP, fun y hy => ?_⟩
        match hPy : P y with
        | false => rfl
        | true =>
          exact absurd (leastBelow_some P n y (e.symm ▸ hy) hPy)
            (fun ⟨z, hz⟩ => nomatch (hl ▸ hz : (none : Option Nat) = some z))
      | false =>
        rw [hP, ite_eq_right Bool.false_ne_true] at h''
        exact nomatch (h'' : (none : Option Nat) = some x)

/-- 5:E2 (Lemma periodic choice) — the choice depends on the set alone: pointwise equal families choose alike,
so an equality-periodic family `A_{i+N} = A_i` has a choice function of the same period. -/
theorem leastBelow_congr {P Q : Nat → Bool} : ∀ {n : Nat}, (∀ x, x < n → P x = Q x) → leastBelow P n = leastBelow Q n
  | 0, _ => rfl
  | n + 1, h => by
    show (match leastBelow P n with
      | some x => some x
      | none => if P n then some n else none) = (match leastBelow Q n with
      | some x => some x
      | none => if Q n then some n else none)
    rw [leastBelow_congr (fun x hx => h x (Nat.lt_succ_of_lt hx)), h n (Nat.lt_succ_self n)]

/-! ### The counting core of 25-godel -/

theorem or_intro_left {a b : Bool} (h : a = true) : (a || b) = true := by rw [h]; rfl

theorem or_intro_right {a b : Bool} (h : b = true) : (a || b) = true := by rw [h]; cases a <;> rfl

theorem and_true' (c : Bool) : (c && true) = c := by cases c <;> rfl

theorem and_false' (c : Bool) : (c && false) = false := by cases c <;> rfl

theorem and_self' (c : Bool) : (c && c) = c := by cases c <;> rfl

theorem or_false' (c : Bool) : (c || false) = c := by cases c <;> rfl

theorem and_assoc' (a b c : Bool) : ((a && b) && c) = (a && (b && c)) := by cases a <;> rfl

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

/-- 25:D1 (Theorem part) — an agent with `R` storage states in a structure of `m > R` elements has no injective
encoding: every reading `ρ : [0, m) → [0, R)` identifies two elements. -/
theorem part_collides {m R : Nat} (hR : R < m) (ρ : Nat → Nat) (hρ : ∀ i, i < m → ρ i < R) :
    ¬ ∀ i j, i < m → j < m → ρ i = ρ j → i = j :=
  fun hinj => no_mirror hR ρ hρ hinj

/-- 25:C5 (Remark Tarski scoped, the count) — `m + 1` sentences, indexed `0, …, m` (the row's sentences
`φ, ¬φ, …, ¬^m φ`), admit no injective numbering into a structure of `m` elements. -/
theorem sentences_outnumber (m : Nat) (g : Nat → Nat) (hg : ∀ i, i < m + 1 → g i < m) :
    ¬ ∀ i j, i < m + 1 → j < m + 1 → g i = g j → i = j :=
  part_collides (Nat.lt_succ_self m) g hg

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

theorem count_shift_by : ∀ (j : Nat) (f : Nat → Bool) (N : Nat), count (fun i => f (i + j)) N ≤ count f (N + j)
  | 0, _, _ => Nat.le_refl _
  | j + 1, f, N => Nat.le_trans (count_shift_by j (fun k => f (k + 1)) N) (count_shift f (N + j))

/-- 25:F4 (Lemma density, the count) — an injective coding of the `a^n` strings of length `n` into `k`-tuples
over `m` elements needs `a^n ≤ m^k`. -/
theorem dense_coding {a n m k : Nat} (c : Nat → Nat) (hc : ∀ i, i < a ^ n → c i < m ^ k)
    (hinj : ∀ i j, i < a ^ n → j < a ^ n → c i = c j → i = j) : a ^ n ≤ m ^ k :=
  match Nat.lt_or_ge (m ^ k) (a ^ n) with
  | Or.inl h => absurd hinj (part_collides h c hc)
  | Or.inr h => h

/-- A strict power step: `m < b` gives `m^(k+1) < b^(k+1)`. -/
theorem pow_lt_pow_base {m b : Nat} (h : m < b) : ∀ k : Nat, m ^ (k + 1) < b ^ (k + 1)
  | 0 => show m ^ 0 * m < b ^ 0 * b from Nat.mul_lt_mul_of_le_of_lt (Nat.le_refl 1) h (Nat.zero_lt_succ 0)
  | k + 1 => show m ^ (k + 1) * m < b ^ (k + 1) * b from Nat.mul_lt_mul_of_lt_of_lt (pow_lt_pow_base h k) h

/-- 25:F4 (Lemma density, the digit form) — if `m` has at most `d` digits in base `a` (`m < a^d`), a coding of
the strings of length `n` by tuples of `k+1` coordinates with `a^n ≤ m^(k+1)` has `n < d·(k+1)`: a tuple carries
fewer letters than `d` times its coordinates. -/
theorem digit_bound {a n m k d : Nat} (ha : 0 < a) (hm : m < a ^ d) (h : a ^ n ≤ m ^ (k + 1)) :
    n < d * (k + 1) :=
  match Nat.lt_or_ge n (d * (k + 1)) with
  | Or.inl hlt => hlt
  | Or.inr hge =>
    have h1 : m ^ (k + 1) < (a ^ d) ^ (k + 1) := pow_lt_pow_base hm k
    have h2 : a ^ (d * (k + 1)) = (a ^ d) ^ (k + 1) := FRC.Nat.pow_mul a d (k + 1)
    have h3 : a ^ (d * (k + 1)) ≤ a ^ n := Nat.pow_le_pow_right ha hge
    absurd (Nat.lt_of_le_of_lt h (h2 ▸ h1)) (Nat.not_lt.mpr h3)

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

/-! ### 25:C2, 25:C3, 00:Z1 — the first-order theory of a finite structure: decidable, complete, consistent -/

/-- A finite relational structure: the elements `0, …, m − 1` and decidable relations, `rel r xs` the truth of the
relation symbol `r` on the arguments `xs`. A function symbol enters through its graph. -/
structure FinStr where
  m : Nat
  rel : Nat → List Nat → Bool

/-- First-order formulas over a relational signature: the atoms `R_r(x_{i₁}, …)` and `x_i = x_j` (variables as de
Bruijn indices), negation, conjunction and the quantifier `∀`, which binds variable `0`. -/
inductive FForm where
  | rel : Nat → List Nat → FForm
  | eq : Nat → Nat → FForm
  | neg : FForm → FForm
  | conj : FForm → FForm → FForm
  | all : FForm → FForm

/-- Satisfaction, the standard semantics: the quantifier ranges over the structure's elements. -/
def Sat (M : FinStr) : (Nat → Nat) → FForm → Prop
  | env, .rel r xs => M.rel r (xs.map env) = true
  | env, .eq i j => env i = env j
  | env, .neg φ => ¬ Sat M env φ
  | env, .conj φ ψ => Sat M env φ ∧ Sat M env ψ
  | env, .all φ => ∀ x, x < M.m → Sat M (cons x env) φ

/-- Exhaustive evaluation: each quantifier tries the `m` elements. -/
def fval (M : FinStr) : (Nat → Nat) → FForm → Bool
  | env, .rel r xs => M.rel r (xs.map env)
  | env, .eq i j => decide (env i = env j)
  | env, .neg φ => !(fval M env φ)
  | env, .conj φ ψ => fval M env φ && fval M env ψ
  | env, .all φ => allBelow (fun x => fval M (cons x env) φ) M.m

theorem allBelow_iff (f : Nat → Bool) : ∀ n, allBelow f n = true ↔ ∀ x, x < n → f x = true
  | 0 => ⟨fun _ _ h => absurd h (Nat.not_lt_zero _), fun _ => rfl⟩
  | n + 1 => by
    show (f n && allBelow f n) = true ↔ _
    have ih := allBelow_iff f n
    match hf : f n with
    | true => exact ⟨fun h x hx => match Nat.lt_or_ge x n with
        | .inl hlt => ih.1 h x hlt
        | .inr hge => (Nat.le_antisymm (Nat.le_of_lt_succ hx) hge) ▸ hf,
        fun h => ih.2 (fun x hx => h x (Nat.lt_succ_of_lt hx))⟩
    | false => exact ⟨fun h => Bool.noConfusion h, fun h => Bool.noConfusion (hf ▸ h n (Nat.lt_succ_self n))⟩

/-- 25:C2, Z1 — decidable by exhaustive evaluation: a formula holds in the finite structure exactly when its
evaluation is `true`. -/
theorem fin_theory_decidable (M : FinStr) : ∀ (φ : FForm) (env : Nat → Nat), fval M env φ = true ↔ Sat M env φ
  | .rel _ _, _ => Iff.rfl
  | .eq i j, env => show decide (env i = env j) = true ↔ env i = env j from ⟨of_decide_eq_true, decide_eq_true⟩
  | .neg φ, env => by
    show (!(fval M env φ)) = true ↔ ¬ Sat M env φ
    have ih := fin_theory_decidable M φ env
    match h : fval M env φ with
    | true => exact ⟨fun e => Bool.noConfusion e, fun hn => absurd (ih.1 h) hn⟩
    | false => exact ⟨fun _ hs => Bool.noConfusion (h ▸ ih.2 hs), fun _ => rfl⟩
  | .conj φ ψ, env => by
    show (fval M env φ && fval M env ψ) = true ↔ Sat M env φ ∧ Sat M env ψ
    have i1 := fin_theory_decidable M φ env
    have i2 := fin_theory_decidable M ψ env
    match h1 : fval M env φ, h2 : fval M env ψ with
    | true, true => exact ⟨fun _ => ⟨i1.1 h1, i2.1 h2⟩, fun _ => rfl⟩
    | true, false => exact ⟨fun e => Bool.noConfusion e, fun hs => Bool.noConfusion (h2 ▸ i2.2 hs.2)⟩
    | false, _ => exact ⟨fun e => Bool.noConfusion e, fun hs => Bool.noConfusion (h1 ▸ i1.2 hs.1)⟩
  | .all φ, env => by
    show allBelow (fun x => fval M (cons x env) φ) M.m = true ↔ ∀ x, x < M.m → Sat M (cons x env) φ
    exact (allBelow_iff _ M.m).trans ⟨fun h x hx => (fin_theory_decidable M φ (cons x env)).1 (h x hx),
      fun h x hx => (fin_theory_decidable M φ (cons x env)).2 (h x hx)⟩

/-- 25:C2, Z1 — the theory is complete: every formula or its negation holds, decided by the evaluation, with no
appeal to excluded middle. -/
theorem fin_theory_complete (M : FinStr) (φ : FForm) (env : Nat → Nat) : Sat M env φ ∨ Sat M env (.neg φ) :=
  match h : fval M env φ with
  | true => .inl ((fin_theory_decidable M φ env).1 h)
  | false => .inr (fun hs => Bool.noConfusion (h ▸ (fin_theory_decidable M φ env).2 hs))

/-- 25:C2, 25:C3, Z1 — the theory is consistent: no formula holds together with its negation. -/
theorem fin_theory_consistent (M : FinStr) (φ : FForm) (env : Nat → Nat) : ¬ (Sat M env φ ∧ Sat M env (.neg φ)) :=
  fun h => h.2 h.1

/-! ### 00:Z1 — no finite structure interprets Robinson's `Q` -/

/-- The successor an interpretation defines: on the domain `D`, the least `y` in `D` with `Sg x y`; the identity off it. -/
def succOf (D : Nat → Bool) (Sg : Nat → Nat → Bool) (n x : Nat) : Nat :=
  if D x then (match leastBelow (fun y => D y && Sg x y) n with | some y => y | none => x) else x

theorem band_l {a b : Bool} (h : (a && b) = true) : a = true := by cases a <;> cases b <;> first | rfl | exact h
theorem band_r {a b : Bool} (h : (a && b) = true) : b = true := by cases a <;> cases b <;> first | rfl | exact h

/-- 00:Z1, 25:C1 — no finite structure carries Robinson's successor: on `[0, n)`, a domain `D`, a successor relation
`Sg` total on `D`, injective (Q2) and never reaching a zero `Z` of `D` (Q1) cannot exist. A `k`-dimensional
interpretation is the case `n = mᵏ`, its tuples coded below `mᵏ`. -/
theorem no_finite_Q (n : Nat) (D Z : Nat → Bool) (Sg : Nat → Nat → Bool)
    (htot : ∀ x, x < n → D x = true → ∃ y, y < n ∧ D y = true ∧ Sg x y = true)
    (hinj : ∀ x x' y, x < n → x' < n → D x = true → D x' = true → Sg x y = true → Sg x' y = true → x = x')
    (hz : ∃ z, z < n ∧ D z = true ∧ Z z = true)
    (h1 : ∀ x y, x < n → y < n → D x = true → D y = true → Sg x y = true → Z y = false) : False := by
  have hS : ∀ x, x < n → D x = true →
      ∃ y, y < n ∧ D y = true ∧ Sg x y = true ∧ succOf D Sg n x = y := fun x hx hD => by
    obtain ⟨y, hy, hDy, hSy⟩ := htot x hx hD
    obtain ⟨y0, h0⟩ := leastBelow_some (fun y => D y && Sg x y) n y hy (by rw [hDy, hSy]; rfl)
    have sp := leastBelow_spec _ n y0 h0
    refine ⟨y0, sp.1, band_l sp.2.1, band_r sp.2.1, ?_⟩
    show (if D x = true then (match leastBelow (fun y => D y && Sg x y) n with | some y => y | none => x) else x) = y0
    rw [ite_eq_left hD, h0]
  have hoff : ∀ x, D x = false → succOf D Sg n x = x := fun x hD => by
    show (if D x = true then _ else x) = x
    rw [hD, ite_eq_right Bool.false_ne_true]
  obtain ⟨z, hzn, hDz, hZz⟩ := hz
  refine no_finite_successor n (succOf D Sg n) (fun x hx => ?_) (fun x x' hx hx' e => ?_) z hzn (fun x hx e => ?_)
  · match hD : D x with
    | true => obtain ⟨y, hy, _, _, ey⟩ := hS x hx hD; rw [ey]; exact hy
    | false => rw [hoff x hD]; exact hx
  · match hD : D x, hD' : D x' with
    | true, true =>
      obtain ⟨y, _, _, hSy, ey⟩ := hS x hx hD
      obtain ⟨y', _, _, hSy', ey'⟩ := hS x' hx' hD'
      rw [ey, ey'] at e
      exact hinj x x' y hx hx' hD hD' hSy (e ▸ hSy')
    | true, false =>
      obtain ⟨y, _, hDy, _, ey⟩ := hS x hx hD
      rw [ey, hoff x' hD'] at e
      rw [e] at hDy; rw [hDy] at hD'; exact Bool.noConfusion hD'
    | false, true =>
      obtain ⟨y', _, hDy', _, ey'⟩ := hS x' hx' hD'
      rw [ey', hoff x hD] at e
      rw [← e] at hDy'; rw [hDy'] at hD; exact Bool.noConfusion hD
    | false, false => rw [hoff x hD, hoff x' hD'] at e; exact e
  · match hD : D x with
    | true =>
      obtain ⟨y, hy, hDy, hSy, ey⟩ := hS x hx hD
      rw [ey] at e
      have := h1 x y hx hy hD hDy hSy
      rw [e, hZz] at this; exact Bool.noConfusion this
    | false => rw [hoff x hD] at e; rw [e, hDz] at hD; exact Bool.noConfusion hD

/-- 00:Z1, 25:C1 — a finite structure interprets no Robinson `Q`: for formulas `δ` (the domain, in variable `0`),
`σ` (the successor's graph, `x` in variable `1` and `y` in `0`) and `ζ` (zero), the relativised successor axioms —
`S` total on the domain, Q2 (`S x = S x' → x = x'`), a zero in the domain, and Q1 (`S x ≠ 0`) — never all hold. -/
theorem no_interpretation (M : FinStr) (env : Nat → Nat) (δ σ ζ : FForm) :
    ¬ ((∀ x, x < M.m → Sat M (cons x env) δ →
        ∃ y, y < M.m ∧ Sat M (cons y env) δ ∧ Sat M (cons y (cons x env)) σ) ∧
      (∀ x x' y, x < M.m → x' < M.m → Sat M (cons x env) δ → Sat M (cons x' env) δ →
        Sat M (cons y (cons x env)) σ → Sat M (cons y (cons x' env)) σ → x = x') ∧
      (∃ z, z < M.m ∧ Sat M (cons z env) δ ∧ Sat M (cons z env) ζ) ∧
      (∀ x y, x < M.m → y < M.m → Sat M (cons x env) δ → Sat M (cons y env) δ → Sat M (cons y (cons x env)) σ →
        ¬ Sat M (cons y env) ζ)) := fun ⟨htot, hinj, ⟨z, hz, hDz, hZz⟩, h1⟩ => by
  have dec := fin_theory_decidable M
  refine no_finite_Q M.m (fun x => fval M (cons x env) δ) (fun x => fval M (cons x env) ζ)
    (fun x y => fval M (cons y (cons x env)) σ) (fun x hx hD => ?_) (fun x x' y hx hx' hD hD' hS hS' => ?_)
    ⟨z, hz, (dec δ _).2 hDz, (dec ζ _).2 hZz⟩ (fun x y hx hy hD hDy hS => ?_)
  · obtain ⟨y, hy, hDy, hSy⟩ := htot x hx ((dec δ _).1 hD)
    exact ⟨y, hy, (dec δ _).2 hDy, (dec σ _).2 hSy⟩
  · exact hinj x x' y hx hx' ((dec δ _).1 hD) ((dec δ _).1 hD') ((dec σ _).1 hS) ((dec σ _).1 hS')
  · match hZ : fval M (cons y env) ζ with
    | false => rfl
    | true => exact absurd ((dec ζ _).1 hZ) (h1 x y hx hy ((dec δ _).1 hD) ((dec δ _).1 hDy) ((dec σ _).1 hS))

end FRC.Logic
