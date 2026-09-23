import FrcCore.Nat
import FrcCore.Pigeonhole
import FrcCore.Shell
import FrcCore.Frame
import FrcCore.Sum

/-!
# 5-red — paradoxes of infinity as reductio: the ledger predicates with no axioms

Rows of the predicate ledger of *Paradoxes of Infinity as Reductio ad Absurdum* (tree `5-reductio-20260706`).
What the finite exit asserts is finite mathematics, and it is proved here on the kernel alone: the bounded
stability schema for an explicit language of `Δ₀` formulas with two evaluators (over `ℕ`, and in a frame `W_N`
where overflow makes an atom false) — every formula takes its standard value in every frame above its bound;
the counting behind the migration (fewer than `s^(K+1)` records of length `≤ K`, so a bounded part cannot mirror
a larger frame); the pigeonhole behind periodic König and the horizon separation of bounded halting (an
iteration on `n` states repeats within `n` steps, so halting is decided by `n` steps); Cantor's theorem on the
finite frame; definable choice by the least element; the equivariant obstruction on `𝔽₅`.  Every declaration
prints "does not depend on any axioms".
-/

namespace FRC.Reductio

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


/-! ### 5:B6 — the worked instance: Goldbach below 10 in the frames -/

/-- The numeral `n` as a term, `((0 + 1) + 1) + …`. -/
def num : Nat → Term
  | 0 => Term.zero
  | n + 1 => Term.add (num n) Term.one

/-- `∃ x ≤ t, φ` as `¬∀ x ≤ t, ¬φ`. -/
def bex (t : Term) (φ : Form) : Form := Form.neg (Form.ball t (Form.neg φ))

/-- "variable `i` is prime": `1 < x ∧ ∀ d ≤ x, ∀ e ≤ x, ¬(d·e = x ∧ d ≠ 1 ∧ d ≠ x)`. -/
def prime (i : Nat) : Form :=
  Form.conj (Form.lt Term.one (Term.var i))
    (Form.ball (Term.var i) (Form.ball (Term.var (i + 1))
      (Form.neg (Form.conj (Form.eq (Term.mul (Term.var 1) (Term.var 0)) (Term.var (i + 2)))
        (Form.conj (Form.neg (Form.eq (Term.var 1) Term.one)) (Form.neg (Form.eq (Term.var 1) (Term.var (i + 2)))))))))

/-- "variable `0` is even": `∃ k ≤ m, k + k = m`. -/
def even0 : Form := bex (Term.var 0) (Form.eq (Term.add (Term.var 0) (Term.var 0)) (Term.var 1))

/-- Goldbach below `M`: every even `m ≤ M` with `4 ≤ m` is a sum of two primes `x, y ≤ m` — a `Δ₀` sentence. -/
def goldbach (M : Nat) : Form :=
  Form.ball (num M) (Form.neg (Form.conj (Form.conj even0 (Form.neg (Form.lt (Term.var 0) (num 4))))
    (Form.neg (bex (Term.var 0) (bex (Term.var 1)
      (Form.conj (prime 1) (Form.conj (prime 0) (Form.eq (Term.add (Term.var 1) (Term.var 0)) (Term.var 2)))))))))

/-- 5:B6 (Example schema-instance) — Goldbach below `10` is true over `ℕ`, decided by the kernel. -/
theorem goldbach_ten : evalF (fun _ => 0) (goldbach 10) = true := by decide +kernel

/-- 5:B6 (Example schema-instance) — its bound: the evaluation touches `100 = 10·10` and nothing larger. -/
theorem goldbach_ten_bound : boundF (fun _ => 0) (goldbach 10) = 100 := by decide +kernel

/-- 5:B6 (Example schema-instance) — hence, by `stable`, every frame `W_N` with `N > 100` gives the sentence its
standard value; `W_101` does so by direct evaluation as well. -/
theorem goldbach_ten_frame : evalF? 101 (fun _ => 0) (goldbach 10) = true := by decide +kernel

/-- 5:B6 — the schema instance `St(goldbach 10, M)` for every `M`: all frames `100 < N` agree with `ℕ`. -/
theorem goldbach_ten_stable (N : Nat) (hN : 100 < N) : evalF? N (fun _ => 0) (goldbach 10) = true := by
  rw [stable N (goldbach 10) (fun _ => 0) (goldbach_ten_bound ▸ hN)]; exact goldbach_ten

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

/-- 5:C2 (Proposition mirror) — a part with fewer records than the frame has elements holds no injective
representation of the frame's domain: no `f : [0, N) → [0, R)` is injective when `R < N`. -/
theorem no_mirror {N R : Nat} (hR : R < N) (f : Nat → Nat) (hf : ∀ i, i < N → f i < R)
    (hinj : ∀ i j, i < N → j < N → f i = f j → i = j) : False :=
  have hnd := FRC.Shell.imageList_nodup hinj (Nat.le_refl N)
  have hlen := FRC.Shell.imageList_length f N
  have hb : ∀ e, Pigeonhole.mem e (FRC.Shell.imageList f N) → e < R := fun _ he =>
    match FRC.Shell.mem_imageList he with
    | ⟨j, hj, ej⟩ => ej ▸ hf j hj
  have := Pigeonhole.length_le_of_nodup_lt R _ hnd hb
  Nat.lt_irrefl N (Nat.lt_of_le_of_lt (hlen ▸ this) hR)

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

/-! ### 5:E4 — the equivariant obstruction on `𝔽₅` -/

/-- 5:E4 (Example basis-obstruction) — on the line over `𝔽₅` the map `v ↦ −v` fixes no basis: `−v ≠ v` for every
`v ≠ 0`; over `𝔽₂` it fixes `1`, so the obstruction is arithmetic. -/
theorem obstruction_five :
    (-(1 : Shell 5) ≠ 1) ∧ (-(2 : Shell 5) ≠ 2) ∧ (-(3 : Shell 5) ≠ 3) ∧ (-(4 : Shell 5) ≠ 4) ∧ (-(1 : Shell 2) = 1) := by
  decide

end FRC.Reductio
