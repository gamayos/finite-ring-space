import FrcCore.Nat
import FrcCore.Pigeonhole
import FrcCore.Shell
import FrcCore.Frame
import FrcCore.Sum
import FrcCore.Theme.Logic
import FrcCore.Keys.Logic
import FrcCore.Theme.Equivariant
import FrcCore.Theme.Sets
import FrcCore.Theme.Transfer

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

/-! ## Old names (ledger migration, task LM17; the worked instances since 21 October 2026): the declarations moved to the themes, each under its old name -/

section
open FRC.Logic

/-! ### 5:B6 — the worked instance: Goldbach below 10 in the frames (in the theme since 21 October 2026; the names kept) -/

/-- The numeral `n` as a term, `((0 + 1) + 1) + …`. -/
@[reducible] def num (n : Nat) : Term := FRC.Logic.num n

/-- `∃ x ≤ t, φ` as `¬∀ x ≤ t, ¬φ`. -/
@[reducible] def bex (t : Term) (φ : Form) : Form := FRC.Logic.bex t φ

/-- "variable `i` is prime": `1 < x ∧ ∀ d ≤ x, ∀ e ≤ x, ¬(d·e = x ∧ d ≠ 1 ∧ d ≠ x)`. -/
@[reducible] def prime (i : Nat) : Form := FRC.Logic.prime i

/-- "variable `0` is even": `∃ k ≤ m, k + k = m`. -/
@[reducible] def even0 : Form := FRC.Logic.even0

/-- Goldbach below `M`: every even `m ≤ M` with `4 ≤ m` is a sum of two primes `x, y ≤ m` — a `Δ₀` sentence. -/
@[reducible] def goldbach (M : Nat) : Form := FRC.Logic.goldbach M

/-- 5:B6 (Example schema-instance) — Goldbach below `10` is true over `ℕ`, decided by the kernel. -/
theorem goldbach_ten : evalF (fun _ => 0) (goldbach 10) = true := FRC.Logic.goldbach_ten

/-- 5:B6 (Example schema-instance) — its bound: the evaluation touches `100 = 10·10` and nothing larger. -/
theorem goldbach_ten_bound : boundF (fun _ => 0) (goldbach 10) = 100 := FRC.Logic.goldbach_ten_bound

/-- 5:B6 (Example schema-instance) — hence, by `stable`, every frame `W_N` with `N > 100` gives the sentence its
standard value; `W_101` does so by direct evaluation as well. -/
theorem goldbach_ten_frame : evalF? 101 (fun _ => 0) (goldbach 10) = true := FRC.Logic.goldbach_ten_frame

/-- 5:B6 — the schema instance `St(goldbach 10, M)` for every `M`: all frames `100 < N` agree with `ℕ`. -/
theorem goldbach_ten_stable (N : Nat) (hN : 100 < N) : evalF? N (fun _ => 0) (goldbach 10) = true :=
  FRC.Logic.goldbach_ten_stable N hN

/-! ### 5:E4 — the equivariant obstruction on `𝔽₅` (in `Theme/Equivariant` since 21 October 2026; the name kept) -/

/-- 5:E4 (Example basis-obstruction) — on the line over `𝔽₅` the map `v ↦ −v` fixes no basis: `−v ≠ v` for every
`v ≠ 0`; over `𝔽₂` it fixes `1`, so the obstruction is arithmetic. -/
theorem obstruction_five :
    (-(1 : Shell 5) ≠ 1) ∧ (-(2 : Shell 5) ≠ 2) ∧ (-(3 : Shell 5) ≠ 3) ∧ (-(4 : Shell 5) ≠ 4) ∧ (-(1 : Shell 2) = 1) :=
  FRC.Equivariant.obstruction_five

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
/-- 5:B3 (p05007) — Witnessed independence: every three-element subset is satisfiable --- $Q$ itself ($\neg$Cmp, consistent by finitary means, the superexponential cost exact); $\mathrm{Th}(W_N)$ ($\neg$IR: consistent, complete, decidable, singly axiomatised, interpreting no $Q$ since every model of $Q$ is infinite); the inconsistent extension ($\neg$Cns); true arithmetic ($\neg$Eff). Four legs, all load-bearing. -/
theorem p05007 : (∀ (n : Nat) (D Z : Nat → Bool) (Sg : Nat → Nat → Bool), (∀ (x : Nat), x < n → D x = true → ∃ y, y < n ∧ D y = true ∧ Sg x y = true) → (∀ (x x' y : Nat), x < n → x' < n → D x = true → D x' = true → Sg x y = true → Sg x' y = true → x = x') → (∃ z, z < n ∧ D z = true ∧ Z z = true) → (∀ (x y : Nat), x < n → y < n → D x = true → D y = true → Sg x y = true → Z y = false) → False) ∧ (∀ (M : FRC.Logic.FinStr) (env : Nat → Nat) (δ σ ζ : FRC.Logic.FForm), ¬((∀ (x : Nat), x < M.m → FRC.Logic.Sat M (FRC.Logic.cons x env) δ → ∃ y, y < M.m ∧ FRC.Logic.Sat M (FRC.Logic.cons y env) δ ∧ FRC.Logic.Sat M (FRC.Logic.cons y (FRC.Logic.cons x env)) σ) ∧ (∀ (x x' y : Nat), x < M.m → x' < M.m → FRC.Logic.Sat M (FRC.Logic.cons x env) δ → FRC.Logic.Sat M (FRC.Logic.cons x' env) δ → FRC.Logic.Sat M (FRC.Logic.cons y (FRC.Logic.cons x env)) σ → FRC.Logic.Sat M (FRC.Logic.cons y (FRC.Logic.cons x' env)) σ → x = x') ∧ (∃ z, z < M.m ∧ FRC.Logic.Sat M (FRC.Logic.cons z env) δ ∧ FRC.Logic.Sat M (FRC.Logic.cons z env) ζ) ∧ ∀ (x y : Nat), x < M.m → y < M.m → FRC.Logic.Sat M (FRC.Logic.cons x env) δ → FRC.Logic.Sat M (FRC.Logic.cons y env) δ → FRC.Logic.Sat M (FRC.Logic.cons y (FRC.Logic.cons x env)) σ → ¬FRC.Logic.Sat M (FRC.Logic.cons y env) ζ)) ∧ (∀ (M : FRC.Logic.FinStr) (φ : FRC.Logic.FForm) (env : Nat → Nat), FRC.Logic.fval M env φ = true ↔ FRC.Logic.Sat M env φ) ∧ (∀ (M : FRC.Logic.FinStr) (φ : FRC.Logic.FForm) (env : Nat → Nat), FRC.Logic.Sat M env φ ∨ FRC.Logic.Sat M env φ.neg) ∧ ∀ (M : FRC.Logic.FinStr) (φ : FRC.Logic.FForm) (env : Nat → Nat), ¬(FRC.Logic.Sat M env φ ∧ FRC.Logic.Sat M env φ.neg) :=
  @FRC.Ledger.p05007
/-- 5:B5 (p05009) — Per-frame completeness: $\mathrm{Th}(W_N)$ is consistent, complete and decidable, axiomatised by the categorical sentence $\sigma_N$; truth in any finite structure is decided by evaluation, and the theory of any structure is complete. -/
theorem p05009 : (∀ (M : FRC.Logic.FinStr) (φ : FRC.Logic.FForm) (env : Nat → Nat), FRC.Logic.fval M env φ = true ↔ FRC.Logic.Sat M env φ) ∧ (∀ (M : FRC.Logic.FinStr) (φ : FRC.Logic.FForm) (env : Nat → Nat), FRC.Logic.Sat M env φ ∨ FRC.Logic.Sat M env φ.neg) ∧ ∀ (M : FRC.Logic.FinStr) (φ : FRC.Logic.FForm) (env : Nat → Nat), ¬(FRC.Logic.Sat M env φ ∧ FRC.Logic.Sat M env φ.neg) :=
  @FRC.Ledger.p05009
/-- 5:B6 (p05010) — Bounded stability, schema form: a $\Delta_0$ sentence $\varphi$ with bound $t(\varphi)$ has $W_N\models\varphi^{*}\iff\N\models\varphi$ for every $N>t(\varphi)$, each instance $\mathrm{St}(\varphi,M)$ a finite conjunction of finite checks; proved for an explicit $\Delta_0$ language with $t(\varphi)$ computed; Goldbach below $20$ has $t=400$ and value true (below $10$, $t=100$, decided by the kernel). -/
theorem p05010 : (∀ (N : Nat) (φ : FRC.Reductio.Form) (env : Nat → Nat), FRC.Reductio.boundF env φ < N → FRC.Reductio.evalF? N env φ = FRC.Reductio.evalF env φ) ∧ (∀ (N : Nat) (env : Nat → Nat) (t : FRC.Reductio.Term), FRC.Reductio.boundT env t < N → FRC.Reductio.evalT? N env t = some (FRC.Reductio.evalT env t)) ∧ ∀ (N : Nat), (100 : Nat) < N → FRC.Reductio.evalF? N (fun x => (0 : Nat)) (FRC.Reductio.goldbach (10 : Nat)) = true :=
  @FRC.Ledger.p05010
/-- 5:C2 (p05013) — No internal mirror: fewer than $s^{K+1}$ records exist, so an agent with $s^{K+1}<N$ holds no injective representation of the domain of $W_N$ --- a proper part cannot mirror the whole (pigeonhole). -/
theorem p05013 : (∀ (s : Nat), (2 : Nat) ≤ s → ∀ (K : Nat), FRC.Reductio.records s K < s ^ (K + (1 : Nat))) ∧ ∀ {N R : Nat}, R < N → ∀ (f : Nat → Nat), (∀ (i : Nat), i < N → f i < R) → (∀ (i j : Nat), i < N → j < N → f i = f j → i = j) → False :=
  @FRC.Ledger.p05013
/-- 5:C3 (p05014) — Vanishing certified fraction: at least $c^{L}$ normal-form sentences of length $\le L$, half of each cohort frame truths by completeness, fewer than $s^{K+1}$ certified, so the certified fraction is at most $s^{K+1}/\lfloor c^{L}/2\rfloor$, below $1/N$ as soon as $2s^{K+1}N\le c^{L}$. -/
theorem p05014 : (∀ (s K N C T : Nat), (2 : Nat) ≤ s → (0 : Nat) < N → C ≤ (2 : Nat) * T → (2 : Nat) * (s ^ (K + (1 : Nat)) * N) ≤ C → FRC.Logic.records s K * N < T) ∧ (∀ (s : Nat), (2 : Nat) ≤ s → ∀ (K : Nat), FRC.Logic.records s K < s ^ (K + (1 : Nat))) ∧ ∀ (M : FRC.Logic.FinStr) (φ : FRC.Logic.FForm) (env : Nat → Nat), FRC.Logic.Sat M env φ ∨ FRC.Logic.Sat M env φ.neg :=
  @FRC.Ledger.p05014
/-- 5:C5 (p05016) — Horizon separation: halting for machines of bounded space $K$ is decided from above within $|Q|\,K\,s^{K}$ steps (a configuration repeats) and never from within (diagonalisation); Turing's theorem is an external non-existence theorem, classified with Cantor's, not an instance of the bundle. -/
theorem p05016 : (∀ (f : Nat → Nat) (n : Nat), (∀ (y : Nat), y < n → f y < n) → ∀ (x : Nat), x < n → ∃ i j, i < j ∧ j ≤ n ∧ FRC.Reductio.iter f x i = FRC.Reductio.iter f x j) ∧ ∀ (f : Nat → Nat) (n : Nat), (∀ (y : Nat), y < n → f y < n) → ∀ (h x : Nat), x < n → ((∃ k, FRC.Reductio.iter f x k = h) ↔ ∃ k, k ≤ n ∧ FRC.Reductio.iter f x k = h) :=
  @FRC.Ledger.p05016
/-- 5:D2 (p05018) — Antinomy normal form: Cns $+$ AT $+$ comprehension is inconsistent (Russell, Burali--Forti); the witness of Cns $+\neg$AT is bounded comprehension --- every set $u$ has a subset not among its members and no universal set exists, decided on $V_4$. -/
theorem p05018 : And (∀ {α : Type} (M : α → α → Prop), Not (@Exists α fun r => ∀ (x : α), Iff (M x r) (Not (M x x)))) (And (∀ {α : Type} (M : α → α → Prop) (sep : α → α), (∀ (u x : α), Iff (M x (sep u)) (And (M x u) (Not (M x x)))) → Not (@Exists α fun v => ∀ (x : α), M x v)) (And (∀ {α : Type} (M : α → α → Prop) (u r : α), (∀ (x : α), Iff (M x r) (And (M x u) (Not (M x x)))) → Not (M r u)) (And (∀ (x : FRC.Sets.HF), Not (x.Mem x)) (And (∀ (u : FRC.Sets.HF), Not ((FRC.Sets.russell u).Mem u)) (∀ (v : FRC.Sets.HF), @Exists FRC.Sets.HF fun x => Not (x.Mem v)))))) :=
  @FRC.Ledger.p05018
/-- 5:D3 (p05019) — Diagonal normal form: $\{$Eff, Cns, Cmp, IR$\}$ inconsistent (B2), Tarski a variant with the truth predicate for Cmp; the diagonal is a theorem when external --- Cantor's theorem, $n<2^{n}$ on every frame, uncountability, halting --- and a paradox engine only over an internalised registry with completeness demanded. -/
theorem p05019 : ∀ (n : Nat), n < (2 : Nat) ^ n :=
  @FRC.Ledger.p05019
/-- 5:D5 (p05021) — The reductio principle: for each normal form a baseline $B$ and one infinitary premise $I$ with $B+I$ contradictory and $B+\neg I$ satisfiable by an explicit witness --- bounded ranks, $\mathrm{Th}(W_N)$, counting measure (Solovay's model as classical corroboration); the rejection of $I$ is coherent and witnessed. -/
theorem p05021 : And (∀ (M : FRC.Logic.FinStr) (φ : FRC.Logic.FForm) (env : Nat → Nat), Iff (@Eq Bool (FRC.Logic.fval M env φ) true) (FRC.Logic.Sat M env φ)) (And (∀ (M : FRC.Logic.FinStr) (φ : FRC.Logic.FForm) (env : Nat → Nat), Or (FRC.Logic.Sat M env φ) (FRC.Logic.Sat M env φ.neg)) (And (∀ (M : FRC.Logic.FinStr) (φ : FRC.Logic.FForm) (env : Nat → Nat), Not (And (FRC.Logic.Sat M env φ) (FRC.Logic.Sat M env φ.neg))) (And (∀ (M : FRC.Logic.FinStr) (env : Nat → Nat) (δ σ ζ : FRC.Logic.FForm), Not (And (∀ (x : Nat), @LT.lt Nat instLTNat x M.m → FRC.Logic.Sat M (FRC.Logic.cons x env) δ → @Exists Nat fun y => And (@LT.lt Nat instLTNat y M.m) (And (FRC.Logic.Sat M (FRC.Logic.cons y env) δ) (FRC.Logic.Sat M (FRC.Logic.cons y (FRC.Logic.cons x env)) σ))) (And (∀ (x x' y : Nat), @LT.lt Nat instLTNat x M.m → @LT.lt Nat instLTNat x' M.m → FRC.Logic.Sat M (FRC.Logic.cons x env) δ → FRC.Logic.Sat M (FRC.Logic.cons x' env) δ → FRC.Logic.Sat M (FRC.Logic.cons y (FRC.Logic.cons x env)) σ → FRC.Logic.Sat M (FRC.Logic.cons y (FRC.Logic.cons x' env)) σ → @Eq Nat x x') (And (@Exists Nat fun z => And (@LT.lt Nat instLTNat z M.m) (And (FRC.Logic.Sat M (FRC.Logic.cons z env) δ) (FRC.Logic.Sat M (FRC.Logic.cons z env) ζ))) (∀ (x y : Nat), @LT.lt Nat instLTNat x M.m → @LT.lt Nat instLTNat y M.m → FRC.Logic.Sat M (FRC.Logic.cons x env) δ → FRC.Logic.Sat M (FRC.Logic.cons y env) δ → FRC.Logic.Sat M (FRC.Logic.cons y (FRC.Logic.cons x env)) σ → Not (FRC.Logic.Sat M (FRC.Logic.cons y env) ζ)))))) (And (∀ {α : Type} (M : α → α → Prop), Not (@Exists α fun r => ∀ (x : α), Iff (M x r) (Not (M x x)))) (And (∀ {α : Type} (M : α → α → Prop) (sep : α → α), (∀ (u x : α), Iff (M x (sep u)) (And (M x u) (Not (M x x)))) → Not (@Exists α fun v => ∀ (x : α), M x v)) (And (∀ (u : FRC.Sets.HF), Not ((FRC.Sets.russell u).Mem u)) (And (∀ (v : FRC.Sets.HF), @Exists FRC.Sets.HF fun x => Not (x.Mem v)) (And (∀ (A B : Nat → Bool) (n : Nat), (∀ (x : Nat), @LT.lt Nat instLTNat x n → Not (And (@Eq Bool (A x) true) (@Eq Bool (B x) true))) → @Eq Nat (FRC.Sets.measure (fun x => (A x).or (B x)) n) (@HAdd.hAdd Nat Nat Nat (@instHAdd Nat instAddNat) (FRC.Sets.measure A n) (FRC.Sets.measure B n))) (And (∀ (A : Nat → Bool) (σ : Nat → Nat) (n : Nat), (∀ (j : Nat), @LT.lt Nat instLTNat j n → @LT.lt Nat instLTNat (σ j) n) → (∀ (i j : Nat), @LT.lt Nat instLTNat i n → @LT.lt Nat instLTNat j n → @Eq Nat (σ i) (σ j) → @Eq Nat i j) → @Eq Nat (FRC.Sets.measure (fun j => A (σ j)) n) (FRC.Sets.measure A n)) (∀ (n : Nat), @LT.lt Nat instLTNat (@OfNat.ofNat Nat (nat_lit 0) (instOfNatNat (nat_lit 0))) n → ∀ (f : Nat → Nat), (∀ (x : Nat), @LT.lt Nat instLTNat x (@HMul.hMul Nat Nat Nat (@instHMul Nat instMulNat) (@OfNat.ofNat Nat (nat_lit 2) (instOfNatNat (nat_lit 2))) n) → @LT.lt Nat instLTNat (f x) n) → Not (∀ (x y : Nat), @LT.lt Nat instLTNat x (@HMul.hMul Nat Nat Nat (@instHMul Nat instMulNat) (@OfNat.ofNat Nat (nat_lit 2) (instOfNatNat (nat_lit 2))) n) → @LT.lt Nat instLTNat y (@HMul.hMul Nat Nat Nat (@instHMul Nat instMulNat) (@OfNat.ofNat Nat (nat_lit 2) (instOfNatNat (nat_lit 2))) n) → @Eq Nat (f x) (f y) → @Eq Nat x y))))))))))) :=
  @FRC.Ledger.p05021
/-- 5:D8 (p05024) — Finiteness of determinate totalities: in ZF with every infinite set Dedekind-infinite, a structure satisfies Det iff it is finite --- finite: the full higher-order theory decided by exhaustive evaluation; infinite: a copy of $\N$ inside gives an effective reduction of true second-order arithmetic, which is not arithmetical. The real field's first-order tameness is silence about its subsets. -/
theorem p05024 : (∀ (M : FRC.Logic.FinStr) (φ : FRC.Logic.SForm) (env senv renv : Nat → Nat), FRC.Logic.sval2 M env senv renv φ = true ↔ FRC.Logic.Sat2 M env senv renv φ) ∧ ∀ (M : FRC.Logic.FinStr) (φ : FRC.Logic.SForm) (env senv renv : Nat → Nat), FRC.Logic.Sat2 M env senv renv φ ∨ FRC.Logic.Sat2 M env senv renv φ.neg :=
  @FRC.Ledger.p05024
/-- 5:D9 (p05025) — Corollaries: no absolute totality is determinate (a universal set is infinite by the iterated singletons); Meas is decided content --- a Det totality decides every measure question, trivially on a finite one (counting measure). The totalising conjuncts of two normal forms follow from D8. -/
theorem p05025 : (∀ (n : Nat), (FRC.Sets.chain n).rank = n) ∧ (∀ {a b : Nat}, FRC.Sets.chain a = FRC.Sets.chain b → a = b) ∧ (∀ (v : FRC.Sets.HF), ¬(FRC.Sets.chain v.rank).Mem v) ∧ (∀ (A : Nat → Bool) (n : Nat), FRC.Sets.measure A n ≤ n) ∧ ∀ (A : Nat → Bool) (σ : Nat → Nat) (n : Nat), (∀ (j : Nat), j < n → σ j < n) → (∀ (i j : Nat), i < n → j < n → σ i = σ j → i = j) → FRC.Sets.measure (fun j => A (σ j)) n = FRC.Sets.measure A n :=
  @FRC.Ledger.p05025
/-- 5:E1 (p05027) — Global choice on a finite universe: with a canonical order, $\operatorname{ch}(A)=\min A$ is a uniform pointwise choice rule; over a fixed finite base AC is a definable theorem; finite products are nonempty without it. -/
theorem p05027 : (∀ (P : Nat → Bool) (n x : Nat), FRC.Reductio.leastBelow P n = some x → x < n ∧ P x = true ∧ ∀ (y : Nat), y < x → P y = false) ∧ ∀ (P : Nat → Bool) (n x : Nat), x < n → P x = true → ∃ y, FRC.Reductio.leastBelow P n = some y :=
  @FRC.Ledger.p05027
/-- 5:E2 (p05028) — Periodic choice: an equality-periodic family $A_{i+N}=A_i$ has the choice $f(i)=\operatorname{ch}(A_i)$ of the same period; group-periodic families as equivariant surjections $\pi:A\to I$ with equivariant sections. -/
theorem p05028 : ∀ {P Q : Nat → Bool} {n : Nat}, (∀ (x : Nat), x < n → P x = Q x) → FRC.Reductio.leastBelow P n = FRC.Reductio.leastBelow Q n :=
  @FRC.Ledger.p05028
/-- 5:E3 (p05029) — Equivariant periodic choice: a $G$-equivariant section exists iff each stabiliser action $G_i\curvearrowright A_i$ has a fixed point (one orbit at a time); the Fraenkel--Mostowski mechanism in positive form. -/
theorem p05029 : And (∀ {G I A : Type} {Γ : FRC.Equivariant.Group G} (ρI : @FRC.Equivariant.Action G Γ I) (ρA : @FRC.Equivariant.Action G Γ A) (π : A → I), @FRC.Equivariant.Equivariant G I A Γ ρI ρA π → ∀ (i₀ : I) (tr : I → G), (∀ (i : I), @Eq I (@FRC.Equivariant.Action.act G Γ I ρI (tr i) i₀) i) → Iff (@Exists (I → A) fun s => And (@FRC.Equivariant.IsSection I A π s) (@FRC.Equivariant.EquivariantMap G I A Γ ρI ρA s)) (@Exists A fun a => And (@Eq I (π a) i₀) (∀ (g : G), @FRC.Equivariant.Stab G I Γ ρI i₀ g → @Eq A (@FRC.Equivariant.Action.act G Γ A ρA g a) a))) (∀ {G I A : Type} {Γ : FRC.Equivariant.Group G} (ρI : @FRC.Equivariant.Action G Γ I) (ρA : @FRC.Equivariant.Action G Γ A) (π : A → I), @FRC.Equivariant.Equivariant G I A Γ ρI ρA π → ∀ (rep : I → I), (∀ (g : G) (i : I), @Eq I (rep (@FRC.Equivariant.Action.act G Γ I ρI g i)) (rep i)) → ∀ (tr : I → G), (∀ (i : I), @Eq I (@FRC.Equivariant.Action.act G Γ I ρI (tr i) (rep i)) i) → Iff (@Exists (I → A) fun s => And (@FRC.Equivariant.IsSection I A π s) (@FRC.Equivariant.EquivariantMap G I A Γ ρI ρA s)) (@Exists (I → A) fun a => And (∀ (g : G) (i : I), @Eq A (a (@FRC.Equivariant.Action.act G Γ I ρI g i)) (a i)) (∀ (i : I), And (@Eq I (π (a i)) (rep i)) (∀ (g : G), @FRC.Equivariant.Stab G I Γ ρI (rep i) g → @Eq A (@FRC.Equivariant.Action.act G Γ A ρA g (a i)) (a i))))) :=
  @FRC.Ledger.p05029
/-- 5:E4 (p05030) — The definable basis: every subspace of a finite vector space has the greedy $\min$-basis, one definable function on all subspaces; the equivariant obstruction --- $\Z/2$ acting by $v\mapsto-v$ on the line over $\F_5$ fixes no basis ($-v\neq v$), over $\F_2$ it does: arithmetic, not formal. -/
theorem p05030 : (-1 : FRC.Shell (5 : Nat)) ≠ (1 : FRC.Shell (5 : Nat)) ∧ (-2 : FRC.Shell (5 : Nat)) ≠ (2 : FRC.Shell (5 : Nat)) ∧ (-3 : FRC.Shell (5 : Nat)) ≠ (3 : FRC.Shell (5 : Nat)) ∧ (-4 : FRC.Shell (5 : Nat)) ≠ (4 : FRC.Shell (5 : Nat)) ∧ (-1 : FRC.Shell (2 : Nat)) = (1 : FRC.Shell (2 : Nat)) :=
  @FRC.Ledger.p05030
/-- 5:E5 (p05031) — Periodic K\H{o}nig: in a finite digraph with out-degree $\ge1$ the greedy walk repeats a vertex within $|D|+1$ steps and is eventually periodic with period $\le|D|$ --- the pigeonhole on an iteration over finitely many states. -/
theorem p05031 : (∀ (f : Nat → Nat) (n : Nat), (∀ (y : Nat), y < n → f y < n) → ∀ (x : Nat), x < n → ∃ i j, i < j ∧ j ≤ n ∧ FRC.Reductio.iter f x i = FRC.Reductio.iter f x j) ∧ ∀ (f : Nat → Nat) (n : Nat), (∀ (y : Nat), y < n → f y < n) → ∀ (x : Nat), x < n → ∃ i p, (0 : Nat) < p ∧ p ≤ n ∧ ∀ (k : Nat), FRC.Reductio.iter f x (i + k + p) = FRC.Reductio.iter f x (i + k) :=
  @FRC.Ledger.p05031
/-- 5:E6 (p05032) — Periodic de~Bruijn--Erd\H{o}s, dimension one: a $\sigma$-periodic graph of bounded range whose finite subgraphs are $c$-colourable admits a definable $\sigma^{m}$-periodic $c$-colouring (the transfer digraph $D_c$, its sub-digraph of vertices beginning walks of every length, E5). -/
theorem p05032 : And (∀ {edge : Nat → Nat → Bool} {n : Nat}, (∀ (k : Nat), @Exists Nat fun v => And (@LT.lt Nat instLTNat v n) (@Eq Bool (FRC.Transfer.walks edge n v k) true)) → @Exists Nat fun v => And (@LT.lt Nat instLTNat v n) (FRC.Transfer.AllGood edge n v)) (And (∀ {edge : Nat → Nat → Bool} {n v : Nat}, @LT.lt Nat instLTNat v n → FRC.Transfer.AllGood edge n v → @Exists Nat fun w => And (@LT.lt Nat instLTNat w n) (And (@Eq Bool (edge v w) true) (FRC.Transfer.AllGood edge n w))) (∀ {edge : Nat → Nat → Bool} {n : Nat}, (∀ (k : Nat), @Exists Nat fun v => And (@LT.lt Nat instLTNat v n) (@Eq Bool (FRC.Transfer.walks edge n v k) true)) → @Exists (Nat → Nat) fun w => @Exists Nat fun m => And (@LT.lt Nat instLTNat (@OfNat.ofNat Nat (nat_lit 0) (instOfNatNat (nat_lit 0))) m) (And (@LE.le Nat instLENat m n) (And (∀ (i : Nat), @LT.lt Nat instLTNat (w i) n) (And (∀ (i : Nat), @Eq Bool (edge (w i) (w (@HAdd.hAdd Nat Nat Nat (@instHAdd Nat instAddNat) i (@OfNat.ofNat Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))) true) (∀ (i : Nat), @Eq Nat (w (@HAdd.hAdd Nat Nat Nat (@instHAdd Nat instAddNat) i m)) (w i))))))) :=
  @FRC.Ledger.p05032
/-- 5:E8 (p05034) — The choice paradoxes vanish: on a finite set counting measure is complete and invariant, no decomposition doubles the set ($X\sqcup X$ does not inject into $X$), and every ultrafilter is principal; periodic variants inherit this on one period. -/
theorem p05034 : (∀ (A : Nat → Bool) (n : Nat), FRC.Sets.measure A n ≤ n) ∧ (∀ (A B : Nat → Bool) (n : Nat), (∀ (x : Nat), x < n → ¬(A x = true ∧ B x = true)) → FRC.Sets.measure (fun x => A x || B x) n = FRC.Sets.measure A n + FRC.Sets.measure B n) ∧ (∀ (A : Nat → Bool) (n : Nat), FRC.Sets.measure A n + FRC.Sets.measure (fun x => !A x) n = n) ∧ (∀ (A : Nat → Bool) (σ : Nat → Nat) (n : Nat), (∀ (j : Nat), j < n → σ j < n) → (∀ (i j : Nat), i < n → j < n → σ i = σ j → i = j) → FRC.Sets.measure (fun j => A (σ j)) n = FRC.Sets.measure A n) ∧ (∀ (n : Nat), (0 : Nat) < n → ∀ (f : Nat → Nat), (∀ (x : Nat), x < (2 : Nat) * n → f x < n) → ¬∀ (x y : Nat), x < (2 : Nat) * n → y < (2 : Nat) * n → f x = f y → x = y) ∧ ∀ {n : Nat} (F : FRC.Sets.Ultra n), ∃ x, x < n ∧ ∀ (A : Nat → Bool), F.U A = true ↔ A x = true :=
  @FRC.Ledger.p05034
-- end ledger predicates

end FRC.Reductio
