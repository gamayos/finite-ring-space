import FrcCore.Theme.Logic

/-!
# The full second-order theory of a finite structure (the logic theme; 29-finitism, 9 October 2026)

A finite relational structure `FinStr` (`Theme/Logic.lean`) has finitely many subsets and finitely many relations of
each arity. A subset of its `m` elements is coded by a number below `2^m` (bit `x` for element `x`), and a relation of
arity `a` by a number below `2^(m^a)` (one bit per tuple, the tuple coded in base `m`). Second-order formulas add set
and relation variables, their atoms and their quantifiers to the first-order formulas; satisfaction ranges over the
codes, and exhaustive evaluation tries them all. `so_theory_decidable` is the second-order form of
`fin_theory_decidable`: the full second-order theory of a finite structure is decided by evaluation (29-finitism,
Corollary determinacy, the finite direction; 5-reductio D8). No axioms.
-/

namespace FRC.Logic

/-- Bit `x` of the code `n`: whether element `x` belongs to the subset coded by `n`. -/
def memBit (n x : Nat) : Bool := decide (n / 2 ^ x % 2 = 1)

/-- The code of a tuple of elements in base `m`: `x₀ + m x₁ + m² x₂ + …`. -/
def tupleIndex (m : Nat) : List Nat → Nat
  | [] => 0
  | x :: xs => x + m * tupleIndex m xs

/-- Second-order formulas: the first-order atoms, the set atom `X_k(x_i)`, the relation atom `R_k(x_{i₁}, …)`,
negation, conjunction, and the three quantifiers — over elements, over subsets (binding set variable `0`), over
relations of arity `a` (binding relation variable `0`). Variables are de Bruijn indices in three sorts. -/
inductive SForm where
  | rel : Nat → List Nat → SForm
  | eq : Nat → Nat → SForm
  | setMem : Nat → Nat → SForm
  | relApp : Nat → List Nat → SForm
  | neg : SForm → SForm
  | conj : SForm → SForm → SForm
  | all : SForm → SForm
  | allSet : SForm → SForm
  | allRel : Nat → SForm → SForm

/-- Satisfaction: the element quantifier ranges over the `m` elements, the set quantifier over the `2^m` codes of
subsets, the relation quantifier of arity `a` over the `2^(m^a)` codes of relations. -/
def Sat2 (M : FinStr) : (Nat → Nat) → (Nat → Nat) → (Nat → Nat) → SForm → Prop
  | env, _, _, .rel r xs => M.rel r (xs.map env) = true
  | env, _, _, .eq i j => env i = env j
  | env, senv, _, .setMem k i => memBit (senv k) (env i) = true
  | env, _, renv, .relApp k xs => memBit (renv k) (tupleIndex M.m (xs.map env)) = true
  | env, senv, renv, .neg φ => ¬ Sat2 M env senv renv φ
  | env, senv, renv, .conj φ ψ => Sat2 M env senv renv φ ∧ Sat2 M env senv renv ψ
  | env, senv, renv, .all φ => ∀ x, x < M.m → Sat2 M (cons x env) senv renv φ
  | env, senv, renv, .allSet φ => ∀ S, S < 2 ^ M.m → Sat2 M env (cons S senv) renv φ
  | env, senv, renv, .allRel a φ => ∀ R, R < 2 ^ (M.m ^ a) → Sat2 M env senv (cons R renv) φ

/-- Exhaustive evaluation: each quantifier tries every code below its bound. -/
def sval2 (M : FinStr) : (Nat → Nat) → (Nat → Nat) → (Nat → Nat) → SForm → Bool
  | env, _, _, .rel r xs => M.rel r (xs.map env)
  | env, _, _, .eq i j => decide (env i = env j)
  | env, senv, _, .setMem k i => memBit (senv k) (env i)
  | env, _, renv, .relApp k xs => memBit (renv k) (tupleIndex M.m (xs.map env))
  | env, senv, renv, .neg φ => !(sval2 M env senv renv φ)
  | env, senv, renv, .conj φ ψ => sval2 M env senv renv φ && sval2 M env senv renv ψ
  | env, senv, renv, .all φ => allBelow (fun x => sval2 M (cons x env) senv renv φ) M.m
  | env, senv, renv, .allSet φ => allBelow (fun S => sval2 M env (cons S senv) renv φ) (2 ^ M.m)
  | env, senv, renv, .allRel a φ => allBelow (fun R => sval2 M env senv (cons R renv) φ) (2 ^ (M.m ^ a))

/-- 29:E4 — Corollary determinacy, the finite direction (5:D8): the full second-order theory of a finite structure is
decided by exhaustive evaluation, a formula holds exactly when its evaluation is `true`. -/
theorem so_theory_decidable (M : FinStr) : ∀ (φ : SForm) (env senv renv : Nat → Nat),
    sval2 M env senv renv φ = true ↔ Sat2 M env senv renv φ
  | .rel _ _, _, _, _ => Iff.rfl
  | .eq i j, env, _, _ => show decide (env i = env j) = true ↔ env i = env j from ⟨of_decide_eq_true, decide_eq_true⟩
  | .setMem _ _, _, _, _ => Iff.rfl
  | .relApp _ _, _, _, _ => Iff.rfl
  | .neg φ, env, senv, renv => by
    show (!(sval2 M env senv renv φ)) = true ↔ ¬ Sat2 M env senv renv φ
    have ih := so_theory_decidable M φ env senv renv
    match h : sval2 M env senv renv φ with
    | true => exact ⟨fun e => Bool.noConfusion e, fun hn => absurd (ih.1 h) hn⟩
    | false => exact ⟨fun _ hs => Bool.noConfusion (h ▸ ih.2 hs), fun _ => rfl⟩
  | .conj φ ψ, env, senv, renv => by
    show (sval2 M env senv renv φ && sval2 M env senv renv ψ) = true ↔ Sat2 M env senv renv φ ∧ Sat2 M env senv renv ψ
    have i1 := so_theory_decidable M φ env senv renv
    have i2 := so_theory_decidable M ψ env senv renv
    match h1 : sval2 M env senv renv φ, h2 : sval2 M env senv renv ψ with
    | true, true => exact ⟨fun _ => ⟨i1.1 h1, i2.1 h2⟩, fun _ => rfl⟩
    | true, false => exact ⟨fun e => Bool.noConfusion e, fun hs => Bool.noConfusion (h2 ▸ i2.2 hs.2)⟩
    | false, _ => exact ⟨fun e => Bool.noConfusion e, fun hs => Bool.noConfusion (h1 ▸ i1.2 hs.1)⟩
  | .all φ, env, senv, renv => by
    show allBelow (fun x => sval2 M (cons x env) senv renv φ) M.m = true ↔ ∀ x, x < M.m → Sat2 M (cons x env) senv renv φ
    exact (allBelow_iff _ M.m).trans ⟨fun h x hx => (so_theory_decidable M φ (cons x env) senv renv).1 (h x hx),
      fun h x hx => (so_theory_decidable M φ (cons x env) senv renv).2 (h x hx)⟩
  | .allSet φ, env, senv, renv => by
    show allBelow (fun S => sval2 M env (cons S senv) renv φ) (2 ^ M.m) = true ↔
      ∀ S, S < 2 ^ M.m → Sat2 M env (cons S senv) renv φ
    exact (allBelow_iff _ (2 ^ M.m)).trans ⟨fun h S hS => (so_theory_decidable M φ env (cons S senv) renv).1 (h S hS),
      fun h S hS => (so_theory_decidable M φ env (cons S senv) renv).2 (h S hS)⟩
  | .allRel a φ, env, senv, renv => by
    show allBelow (fun R => sval2 M env senv (cons R renv) φ) (2 ^ (M.m ^ a)) = true ↔
      ∀ R, R < 2 ^ (M.m ^ a) → Sat2 M env senv (cons R renv) φ
    exact (allBelow_iff _ (2 ^ (M.m ^ a))).trans ⟨fun h R hR => (so_theory_decidable M φ env senv (cons R renv)).1 (h R hR),
      fun h R hR => (so_theory_decidable M φ env senv (cons R renv)).2 (h R hR)⟩

/-- 29:E4 — Corollary determinacy, the finite direction: the full second-order theory is complete, every formula or its
negation holds, decided by the evaluation. -/
theorem so_theory_complete (M : FinStr) (φ : SForm) (env senv renv : Nat → Nat) :
    Sat2 M env senv renv φ ∨ Sat2 M env senv renv (.neg φ) :=
  match h : sval2 M env senv renv φ with
  | true => .inl ((so_theory_decidable M φ env senv renv).1 h)
  | false => .inr (fun hs => Bool.noConfusion (h ▸ (so_theory_decidable M φ env senv renv).2 hs))

/-- 29:E4 — the full second-order theory is consistent: no formula holds together with its negation. -/
theorem so_theory_consistent (M : FinStr) (φ : SForm) (env senv renv : Nat → Nat) :
    ¬ (Sat2 M env senv renv φ ∧ Sat2 M env senv renv (.neg φ)) :=
  fun h => h.2 h.1

/-- The subsets of `m` elements are `2^m` codes and the relations of arity `a` are `2^(m^a)`: both finite, and every
code below the bound is a subset or a relation (every bit pattern is one). The quantifiers of `Sat2` range over exactly
these, so the evaluation is uniform in the structure: `sval2` is a terminating computation on `M` presented as data. -/
theorem so_evaluation_terminates (M : FinStr) (φ : SForm) (env senv renv : Nat → Nat) :
    sval2 M env senv renv φ = true ∨ sval2 M env senv renv φ = false :=
  match sval2 M env senv renv φ with
  | true => .inl rfl
  | false => .inr rfl

end FRC.Logic
