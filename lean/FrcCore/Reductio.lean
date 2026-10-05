import FrcCore.Nat
import FrcCore.Pigeonhole
import FrcCore.Shell
import FrcCore.Frame
import FrcCore.Sum
import FrcCore.Theme.Logic

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

Since the ledger migration (task LM17) the language, its evaluation, the stability schema and the counting live in
the logic theme (`Theme/Logic.lean`, namespace `FRC.Logic`); this module keeps the worked instance, the obstruction on
`𝔽₅` and every old name as an alias.
-/

namespace FRC.Reductio

section
open FRC.Logic

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

/-! ### 5:E4 — the equivariant obstruction on `𝔽₅` -/

/-- 5:E4 (Example basis-obstruction) — on the line over `𝔽₅` the map `v ↦ −v` fixes no basis: `−v ≠ v` for every
`v ≠ 0`; over `𝔽₂` it fixes `1`, so the obstruction is arithmetic. -/
theorem obstruction_five :
    (-(1 : Shell 5) ≠ 1) ∧ (-(2 : Shell 5) ≠ 2) ∧ (-(3 : Shell 5) ≠ 3) ∧ (-(4 : Shell 5) ≠ 4) ∧ (-(1 : Shell 2) = 1) := by
  decide

/-! ## Old names (ledger migration, task LM17): the declarations moved to the themes, each under its old name -/
end

section aliases
variable {p : Nat} [Pos p] {κ : Nat} {g : Shell p}

/-- `mx a b`, the larger of two naturals, with its two bounds proved from the definition. -/
@[reducible] def mx (a b : Nat) : Nat :=
  FRC.Logic.mx a b

theorem le_mx_left (a b : Nat) : a ≤ mx a b :=
  FRC.Logic.le_mx_left a b

theorem le_mx_right (a b : Nat) : b ≤ mx a b :=
  FRC.Logic.le_mx_right a b

theorem lt_of_mx_lt_left {a b N : Nat} (h : mx a b < N) : a < N :=
  FRC.Logic.lt_of_mx_lt_left h

theorem lt_of_mx_lt_right {a b N : Nat} (h : mx a b < N) : b < N :=
  FRC.Logic.lt_of_mx_lt_right h

/-- Terms: variables (de Bruijn indices), `0`, `1`, sum, product. -/
@[reducible] def Term := @FRC.Logic.Term

/-- `Δ₀` formulas: atoms `s = t`, `s < t`, negation, conjunction, and the bounded quantifier `∀ x ≤ t, φ`
(`x` is variable `0` in `φ`, the other variables shift up; `t` is read in the outer environment). -/
@[reducible] def Form := @FRC.Logic.Form

/-- The environment extended by a value for variable `0`. -/
@[reducible] def cons (x : Nat) (env : Nat → Nat) : Nat → Nat :=
  FRC.Logic.cons x env

/-- Terms over `ℕ`. -/
@[reducible] def evalT (env : Nat → Nat) : Term → Nat :=
  FRC.Logic.evalT env

/-- `f 0 && … && f (n − 1)`. -/
@[reducible] def allBelow (f : Nat → Bool) : Nat → Bool :=
  FRC.Logic.allBelow f

/-- Formulas over `ℕ` (the standard value). -/
@[reducible] def evalF (env : Nat → Nat) : Form → Bool :=
  FRC.Logic.evalF env

/-- Terms in the frame `W_N`: a value is defined only while every intermediate value stays below `N`
(overflow: `A(x, y, z)` fails for `x + y ≥ N`). -/
@[reducible] def evalT? (N : Nat) (env : Nat → Nat) : Term → Option Nat :=
  FRC.Logic.evalT? N env

/-- Formulas in the frame `W_N`: an atom with an undefined term is false, a bounded quantifier is guarded by
the definedness of its bound (the transcription `φ*` of the paper). -/
@[reducible] def evalF? (N : Nat) (env : Nat → Nat) : Form → Bool :=
  FRC.Logic.evalF? N env

/-- The largest value a term's evaluation touches. -/
@[reducible] def boundT (env : Nat → Nat) : Term → Nat :=
  FRC.Logic.boundT env

/-- `max (f 0, …, f (n − 1))`. -/
@[reducible] def maxBelow (f : Nat → Nat) : Nat → Nat :=
  FRC.Logic.maxBelow f

/-- `t(φ)`, the largest integer referenced in the evaluation of `φ` over `ℕ`. -/
@[reducible] def boundF (env : Nat → Nat) : Form → Nat :=
  FRC.Logic.boundF env

theorem le_maxBelow (f : Nat → Nat) : ∀ {n x : Nat}, x < n → f x ≤ maxBelow f n :=
  FRC.Logic.le_maxBelow f

theorem allBelow_congr {f g : Nat → Bool} : ∀ {n : Nat}, (∀ x, x < n → f x = g x) → allBelow f n = allBelow g n :=
  FRC.Logic.allBelow_congr

/-- 5:B6 (terms) — below its bound a term is defined in the frame, with its standard value. -/
theorem evalT_frame (N : Nat) (env : Nat → Nat) : ∀ (t : Term), boundT env t < N → evalT? N env t = some (evalT env t) :=
  FRC.Logic.evalT_frame N env

/-- 5:B6 (Theorem stability, schema form) — every `Δ₀` formula takes its standard value in every frame `W_N`
with `N > t(φ)`: `W_N ⊨ φ* ⟺ ℕ ⊨ φ`, for every environment, by induction on the formula. -/
theorem stable (N : Nat) : ∀ (φ : Form) (env : Nat → Nat), boundF env φ < N → evalF? N env φ = evalF env φ :=
  FRC.Logic.stable N

/-- The number of strings of length at most `K` over `s` letters, `Σ_{i ≤ K} s^i`. -/
@[reducible] def records (s : Nat) : Nat → Nat :=
  FRC.Logic.records s

/-- 5:C2 (the count) — fewer than `s^(K+1)` records exist for an alphabet of `s ≥ 2` letters. -/
theorem records_lt (s : Nat) (hs : 2 ≤ s) : ∀ K, records s K < s ^ (K + 1) :=
  FRC.Logic.records_lt s hs

/-- 5:C2 (Proposition mirror) — a part with fewer records than the frame has elements holds no injective
representation of the frame's domain: no `f : [0, N) → [0, R)` is injective when `R < N`. -/
theorem no_mirror {N R : Nat} (hR : R < N) (f : Nat → Nat) (hf : ∀ i, i < N → f i < R)
    (hinj : ∀ i j, i < N → j < N → f i = f j → i = j) : False :=
  FRC.Logic.no_mirror hR f hf hinj

/-- `iter f x k = f^k x`. -/
@[reducible] def iter (f : Nat → Nat) (x : Nat) : Nat → Nat :=
  FRC.Logic.iter f x

theorem iter_lt (f : Nat → Nat) {n : Nat} (hf : ∀ y, y < n → f y < n) {x : Nat} (hx : x < n) :
    ∀ k, iter f x k < n :=
  FRC.Logic.iter_lt f hf hx

theorem iter_add (f : Nat → Nat) (x : Nat) (i : Nat) : ∀ k, iter f x (i + k) = iter f (iter f x i) k :=
  FRC.Logic.iter_add f x i

/-- 5:E5, 5:C5 (Lemma periodic König, the pigeonhole) — on `n` states the iteration from `x` revisits a state within
`n` steps: some `i < j ≤ n` have `f^i x = f^j x`. -/
theorem repeat_below (f : Nat → Nat) (n : Nat) (hf : ∀ y, y < n → f y < n) (x : Nat) (hx : x < n) :
    ∃ i j, i < j ∧ j ≤ n ∧ iter f x i = iter f x j :=
  FRC.Logic.repeat_below f n hf x hx

theorem sub_pos {i j : Nat} (h : i < j) : 0 < j - i :=
  FRC.Logic.sub_pos h

/-- 5:E5 — the walk is eventually periodic: from step `i` on, period `p = j − i` with `0 < p ≤ n`,
`f^(i+k+p) x = f^(i+k) x` for every `k`. -/
theorem eventually_periodic (f : Nat → Nat) (n : Nat) (hf : ∀ y, y < n → f y < n) (x : Nat) (hx : x < n) :
    ∃ i p, 0 < p ∧ p ≤ n ∧ ∀ k, iter f x (i + k + p) = iter f x (i + k) :=
  FRC.Logic.eventually_periodic f n hf x hx

/-- 5:C5 (horizon separation) — a run on `n` states reaches a state `h` iff it reaches it within `n` steps: halting for bounded space is decided from above by `n` steps of simulation. -/
theorem halts_iff_halts_below (f : Nat → Nat) (n : Nat) (hf : ∀ y, y < n → f y < n) (h : Nat)
    (x : Nat) (hx : x < n) : (∃ k, iter f x k = h) ↔ ∃ k, k ≤ n ∧ iter f x k = h :=
  FRC.Logic.halts_iff_halts_below f n hf h x hx

/-- 5:D3 (Remark, the external diagonal) — Cantor's theorem holds in every finite frame: `n < 2^n`. -/
theorem cantor_finite (n : Nat) : n < 2 ^ n :=
  FRC.Logic.cantor_finite n

/-- The least `x < n` with `P x`, if any: the choice function `ch(A) = min A` of Definition global-choice. -/
@[reducible] def leastBelow (P : Nat → Bool) : Nat → Option Nat :=
  FRC.Logic.leastBelow P

/-- 5:E1 — a nonempty family has a choice: if some `x < n` has `P x`, `leastBelow P n` is defined. -/
theorem leastBelow_some (P : Nat → Bool) : ∀ (n x : Nat), x < n → P x = true → ∃ y, leastBelow P n = some y :=
  FRC.Logic.leastBelow_some P

/-- 5:E1 (Proposition finite-choice) — the choice is a member, below the bound, and the least one. -/
theorem leastBelow_spec (P : Nat → Bool) : ∀ (n x : Nat), leastBelow P n = some x →
    x < n ∧ P x = true ∧ ∀ y, y < x → P y = false :=
  FRC.Logic.leastBelow_spec P

/-- 5:E2 (Lemma periodic choice) — the choice depends on the set alone: pointwise equal families choose alike,
so an equality-periodic family `A_{i+N} = A_i` has a choice function of the same period. -/
theorem leastBelow_congr {P Q : Nat → Bool} : ∀ {n : Nat}, (∀ x, x < n → P x = Q x) → leastBelow P n = leastBelow Q n :=
  FRC.Logic.leastBelow_congr

end aliases

-- Ledger predicates of 5-reductio (generated by make_predicates.py from docs/5-reductio/5-reductio-ledger.json; edit the ledger, not this section)
/-- 5:B6 (p05010) — Bounded stability, schema form: a $\Delta_0$ sentence $\varphi$ with bound $t(\varphi)$ has $W_N\models\varphi^{*}\iff\N\models\varphi$ for every $N>t(\varphi)$, each instance $\mathrm{St}(\varphi,M)$ a finite conjunction of finite checks; proved for an explicit $\Delta_0$ language with $t(\varphi)$ computed; Goldbach below $20$ has $t=400$ and value true (below $10$, $t=100$, decided by the kernel). -/
theorem p05010 : (∀ (N : Nat) (φ : FRC.Reductio.Form) (env : Nat → Nat), FRC.Reductio.boundF env φ < N → FRC.Reductio.evalF? N env φ = FRC.Reductio.evalF env φ) ∧ (∀ (N : Nat) (env : Nat → Nat) (t : FRC.Reductio.Term), FRC.Reductio.boundT env t < N → FRC.Reductio.evalT? N env t = some (FRC.Reductio.evalT env t)) ∧ ∀ (N : Nat), (100 : Nat) < N → FRC.Reductio.evalF? N (fun x => (0 : Nat)) (FRC.Reductio.goldbach (10 : Nat)) = true :=
  And.intro @FRC.Reductio.stable (And.intro @FRC.Reductio.evalT_frame (@FRC.Reductio.goldbach_ten_stable))
/-- 5:C2 (p05013) — No internal mirror: fewer than $s^{K+1}$ records exist, so an agent with $s^{K+1}<N$ holds no injective representation of the domain of $W_N$ --- a proper part cannot mirror the whole (pigeonhole). -/
theorem p05013 : (∀ (s : Nat), (2 : Nat) ≤ s → ∀ (K : Nat), FRC.Reductio.records s K < s ^ (K + (1 : Nat))) ∧ ∀ {N R : Nat}, R < N → ∀ (f : Nat → Nat), (∀ (i : Nat), i < N → f i < R) → (∀ (i j : Nat), i < N → j < N → f i = f j → i = j) → False :=
  And.intro @FRC.Reductio.records_lt (@FRC.Reductio.no_mirror)
/-- 5:C5 (p05016) — Horizon separation: halting for machines of bounded space $K$ is decided from above within $|Q|\,K\,s^{K}$ steps (a configuration repeats) and never from within (diagonalisation); Turing's theorem is an external non-existence theorem, classified with Cantor's, not an instance of the bundle. -/
theorem p05016 : (∀ (f : Nat → Nat) (n : Nat), (∀ (y : Nat), y < n → f y < n) → ∀ (x : Nat), x < n → ∃ i j, i < j ∧ j ≤ n ∧ FRC.Reductio.iter f x i = FRC.Reductio.iter f x j) ∧ ∀ (f : Nat → Nat) (n : Nat), (∀ (y : Nat), y < n → f y < n) → ∀ (h x : Nat), x < n → ((∃ k, FRC.Reductio.iter f x k = h) ↔ ∃ k, k ≤ n ∧ FRC.Reductio.iter f x k = h) :=
  And.intro @FRC.Reductio.repeat_below (@FRC.Reductio.halts_iff_halts_below)
/-- 5:D3 (p05019) — Diagonal normal form: $\{$Eff, Cns, Cmp, IR$\}$ inconsistent (B2), Tarski a variant with the truth predicate for Cmp; the diagonal is a theorem when external --- Cantor's theorem, $n<2^{n}$ on every frame, uncountability, halting --- and a paradox engine only over an internalised registry with completeness demanded. -/
theorem p05019 : ∀ (n : Nat), n < (2 : Nat) ^ n :=
  @FRC.Reductio.cantor_finite
/-- 5:E1 (p05027) — Global choice on a finite universe: with a canonical order, $\operatorname{ch}(A)=\min A$ is a uniform pointwise choice rule; over a fixed finite base AC is a definable theorem; finite products are nonempty without it. -/
theorem p05027 : (∀ (P : Nat → Bool) (n x : Nat), FRC.Reductio.leastBelow P n = some x → x < n ∧ P x = true ∧ ∀ (y : Nat), y < x → P y = false) ∧ ∀ (P : Nat → Bool) (n x : Nat), x < n → P x = true → ∃ y, FRC.Reductio.leastBelow P n = some y :=
  And.intro @FRC.Reductio.leastBelow_spec (@FRC.Reductio.leastBelow_some)
/-- 5:E2 (p05028) — Periodic choice: an equality-periodic family $A_{i+N}=A_i$ has the choice $f(i)=\operatorname{ch}(A_i)$ of the same period; group-periodic families as equivariant surjections $\pi:A\to I$ with equivariant sections. -/
theorem p05028 : ∀ {P Q : Nat → Bool} {n : Nat}, (∀ (x : Nat), x < n → P x = Q x) → FRC.Reductio.leastBelow P n = FRC.Reductio.leastBelow Q n :=
  @FRC.Reductio.leastBelow_congr
/-- 5:E4 (p05030) — The definable basis: every subspace of a finite vector space has the greedy $\min$-basis, one definable function on all subspaces; the equivariant obstruction --- $\Z/2$ acting by $v\mapsto-v$ on the line over $\F_5$ fixes no basis ($-v\neq v$), over $\F_2$ it does: arithmetic, not formal. -/
theorem p05030 : (-1 : FRC.Shell (5 : Nat)) ≠ (1 : FRC.Shell (5 : Nat)) ∧ (-2 : FRC.Shell (5 : Nat)) ≠ (2 : FRC.Shell (5 : Nat)) ∧ (-3 : FRC.Shell (5 : Nat)) ≠ (3 : FRC.Shell (5 : Nat)) ∧ (-4 : FRC.Shell (5 : Nat)) ≠ (4 : FRC.Shell (5 : Nat)) ∧ (-1 : FRC.Shell (2 : Nat)) = (1 : FRC.Shell (2 : Nat)) :=
  @FRC.Reductio.obstruction_five
/-- 5:E5 (p05031) — Periodic K\H{o}nig: in a finite digraph with out-degree $\ge1$ the greedy walk repeats a vertex within $|D|+1$ steps and is eventually periodic with period $\le|D|$ --- the pigeonhole on an iteration over finitely many states. -/
theorem p05031 : (∀ (f : Nat → Nat) (n : Nat), (∀ (y : Nat), y < n → f y < n) → ∀ (x : Nat), x < n → ∃ i j, i < j ∧ j ≤ n ∧ FRC.Reductio.iter f x i = FRC.Reductio.iter f x j) ∧ ∀ (f : Nat → Nat) (n : Nat), (∀ (y : Nat), y < n → f y < n) → ∀ (x : Nat), x < n → ∃ i p, (0 : Nat) < p ∧ p ≤ n ∧ ∀ (k : Nat), FRC.Reductio.iter f x (i + k + p) = FRC.Reductio.iter f x (i + k) :=
  And.intro @FRC.Reductio.repeat_below (@FRC.Reductio.eventually_periodic)
-- end ledger predicates

end FRC.Reductio
