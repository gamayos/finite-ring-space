import FrcCore.Theme.Reach

/-!
# FrcCore.Theme.Diagonal — the diagonal under finitude (the logic theme; 25-godel's migration, 20 October 2026)

The syntax of `M_p` (`0`, `1`, `+`, `×`, equations, negation, conjunction, the quantifier over the structure) and what
the diagonal construction costs in it, with no axioms:

* mention cost: a formula's truth depends only on the variables that occur in it, so a formula reading all `N`
  coordinates of a tuple has at least `N` symbols, and more than `N` (25:F1, 25:F3);
* the template: the diagonal formula `∃ v (Diag ∧ θ)` is longer than the scale of its bound tuple and than the scale its
  matrix reads, so it has no instance per symbol at any scale and the scales cannot be split (25:F2); no sentence has a
  subformula that reads a tuple as long as the sentence (25:F3, 25:G6);
* the threshold: the `k` shortest names over `a` letters cost `c(k)` symbols with `kJ + 2 ≤ c(k) + 2a^J` for every `J`;
  a dense instance with `k` coordinates in `v` and `k₁` in `u` needs `2c(k) + c(k + k₁) < d k₁` and `3c(k) + k₁ < d k`,
  which force `k < 6a^{⌊d/3⌋+1}` (so `k` has at most `⌊d/3⌋ + 4` base-`a` digits), `k < 6a^{⌊d/4⌋+1}` at one scale,
  nothing at `d ≤ 4`, and the threshold `t = d·k*` below `a^{d−1} ≤ m` in every structure (25:F6);
* the decoders: `Int_J(x)` of linear length defines `{0, …, 2^J − 1}` in `M_p` when `2^J ≤ p` (25:F7);
* the prefix simulation: one uniform pairing prefix decides what every coded quantifier pattern decides (25:G4);
* the window's digits: an element coding `1,024` base-32 symbols needs more base-32 digits than the chart's bound of
  `Ω` has, which is `82` (00:Z9).

The paper module `FrcCore/Godel.lean` keeps every old name as an alias.
-/

namespace FRC.Diagonal

open FRC.Logic FRC.Reach

/-! ### 25:F1, 25:F3 — mention cost: truth depends only on variables that occur -/

/-- Terms with variables (de Bruijn indices) over the signature of `M_p`. -/
inductive VTm where
  | var : Nat → VTm
  | zero : VTm
  | one : VTm
  | add : VTm → VTm → VTm
  | mul : VTm → VTm → VTm

/-- First-order formulas: equations, negation, conjunction, and the quantifier over the whole structure
(the bound variable is variable `0` of the body, the others shift up). -/
inductive Fm where
  | eq : VTm → VTm → Fm
  | neg : Fm → Fm
  | conj : Fm → Fm → Fm
  | all : Fm → Fm

/-- The value of a term in `M_p` under an assignment. -/
def tval (p : Nat) (env : Nat → Nat) : VTm → Nat
  | .var i => env i
  | .zero => 0
  | .one => 1 % p
  | .add s t => (tval p env s + tval p env t) % p
  | .mul s t => (tval p env s * tval p env t) % p

/-- Truth in `M_p` under an assignment: the quantifier ranges over the `p` elements. -/
def holds (p : Nat) (env : Nat → Nat) : Fm → Bool
  | .eq s t => decide (tval p env s = tval p env t)
  | .neg φ => !(holds p env φ)
  | .conj φ ψ => holds p env φ && holds p env ψ
  | .all φ => allBelow (fun x => holds p (cons x env) φ) p

/-- Variable `i` occurs in the term. -/
def occT (i : Nat) : VTm → Bool
  | .var j => decide (j = i)
  | .zero => false
  | .one => false
  | .add s t => occT i s || occT i t
  | .mul s t => occT i s || occT i t

/-- Variable `i` occurs free in the formula. -/
def occ (i : Nat) : Fm → Bool
  | .eq s t => occT i s || occT i t
  | .neg φ => occ i φ
  | .conj φ ψ => occ i φ || occ i ψ
  | .all φ => occ (i + 1) φ

/-- The length of a term, in symbols. -/
def tsize : VTm → Nat
  | .var _ => 1
  | .zero => 1
  | .one => 1
  | .add s t => tsize s + tsize t + 1
  | .mul s t => tsize s + tsize t + 1

/-- The length of a formula, in symbols. -/
def size : Fm → Nat
  | .eq s t => tsize s + tsize t + 1
  | .neg φ => size φ + 1
  | .conj φ ψ => size φ + size ψ + 1
  | .all φ => size φ + 1

theorem tval_congr (p : Nat) {env env' : Nat → Nat} :
    ∀ t : VTm, (∀ i, occT i t = true → env i = env' i) → tval p env t = tval p env' t
  | .var j, h => h j (decide_eq_true rfl)
  | .zero, _ => rfl
  | .one, _ => rfl
  | .add s t, h => by
    show (tval p env s + tval p env t) % p = (tval p env' s + tval p env' t) % p
    rw [tval_congr p s (fun i hi => h i (or_intro_left hi)), tval_congr p t (fun i hi => h i (or_intro_right hi))]
  | .mul s t, h => by
    show (tval p env s * tval p env t) % p = (tval p env' s * tval p env' t) % p
    rw [tval_congr p s (fun i hi => h i (or_intro_left hi)), tval_congr p t (fun i hi => h i (or_intro_right hi))]

/-- 25:F1 (Lemma mention, the coincidence form) — two assignments that agree on the variables occurring free in
a formula give it the same truth value in `M_p`. -/
theorem holds_congr (p : Nat) : ∀ (φ : Fm) {env env' : Nat → Nat},
    (∀ i, occ i φ = true → env i = env' i) → holds p env φ = holds p env' φ
  | .eq s t, env, env', h => by
    show decide (tval p env s = tval p env t) = decide (tval p env' s = tval p env' t)
    rw [tval_congr p s (fun i hi => h i (or_intro_left hi)), tval_congr p t (fun i hi => h i (or_intro_right hi))]
  | .neg φ, env, env', h => by
    show (!(holds p env φ)) = (!(holds p env' φ))
    rw [holds_congr p φ h]
  | .conj φ ψ, env, env', h => by
    show (holds p env φ && holds p env ψ) = (holds p env' φ && holds p env' ψ)
    rw [holds_congr p φ (fun i hi => h i (or_intro_left hi)), holds_congr p ψ (fun i hi => h i (or_intro_right hi))]
  | .all φ, env, env', h => by
    show allBelow (fun x => holds p (cons x env) φ) p = allBelow (fun x => holds p (cons x env') φ) p
    exact allBelow_congr (fun x _ => holds_congr p φ (fun i hi =>
      match i, hi with
      | 0, _ => rfl
      | j + 1, hj => h j hj))

/-- The assignment changed at one coordinate. -/
def upd (env : Nat → Nat) (i v : Nat) : Nat → Nat := fun j => if j = i then v else env j

/-- 25:F1 (Lemma mention) — if the truth of a formula in `M_p` depends on coordinate `i` (reassigning it changes
the truth value), then variable `i` occurs in the formula. -/
theorem mention (p : Nat) (φ : Fm) (env : Nat → Nat) (i v : Nat)
    (hdep : holds p (upd env i v) φ ≠ holds p env φ) : occ i φ = true :=
  match h : occ i φ with
  | true => rfl
  | false => absurd (holds_congr p φ (fun j hj =>
      match Nat.decEq j i with
      | isTrue e => Bool.noConfusion ((e ▸ hj : occ i φ = true).symm.trans h)
      | isFalse e => (ite_eq_right e : (if j = i then v else env j) = env j))) hdep

/-! #### counting the coordinates a formula can read -/

theorem tcount_le : ∀ (t : VTm) (N : Nat), count (fun i => occT i t) N ≤ tsize t
  | .var j, N => (count_single j N).1
  | .zero, N => by show count (fun _ => false) N ≤ 1; rw [count_false N]; exact Nat.zero_le 1
  | .one, N => by show count (fun _ => false) N ≤ 1; rw [count_false N]; exact Nat.zero_le 1
  | .add s t, N =>
    Nat.le_trans (count_or_le (fun i => occT i s) (fun i => occT i t) N)
      (Nat.le_succ_of_le (Nat.add_le_add (tcount_le s N) (tcount_le t N)))
  | .mul s t, N =>
    Nat.le_trans (count_or_le (fun i => occT i s) (fun i => occT i t) N)
      (Nat.le_succ_of_le (Nat.add_le_add (tcount_le s N) (tcount_le t N)))

theorem fcount_le : ∀ (φ : Fm) (N : Nat), count (fun i => occ i φ) N ≤ size φ
  | .eq s t, N =>
    Nat.le_trans (count_or_le (fun i => occT i s) (fun i => occT i t) N)
      (Nat.le_succ_of_le (Nat.add_le_add (tcount_le s N) (tcount_le t N)))
  | .neg φ, N => Nat.le_succ_of_le (fcount_le φ N)
  | .conj φ ψ, N =>
    Nat.le_trans (count_or_le (fun i => occ i φ) (fun i => occ i ψ) N)
      (Nat.le_succ_of_le (Nat.add_le_add (fcount_le φ N) (fcount_le ψ N)))
  | .all φ, N =>
    Nat.le_succ_of_le (Nat.le_trans (count_shift (fun i => occ i φ) N) (fcount_le φ (N + 1)))

/-- 25:F1 (Lemma mention, the arity) — a formula in which the `N` variables `0, …, N − 1` occur has length at
least `N`. -/
theorem arity_le_size (φ : Fm) (N : Nat) (h : ∀ i, i < N → occ i φ = true) : N ≤ size φ :=
  (count_full h) ▸ fcount_le φ N

/-- 25:F1, 25:F2, 00:Z9 (Lemma mention, the cost) — a formula whose truth in `M_p` depends on all `N` coordinates of a
tuple (the variables `0, …, N − 1`) has length at least `N`. -/
theorem mention_cost (p : Nat) (φ : Fm) (N : Nat)
    (h : ∀ i, i < N → ∃ env v, holds p (upd env i v) φ ≠ holds p env φ) : N ≤ size φ :=
  arity_le_size φ N (fun i hi => match h i hi with
    | ⟨env, v, hdep⟩ => mention p φ env i v hdep)

theorem fcount_lt : ∀ (φ : Fm) (N : Nat), count (fun i => occ i φ) N < size φ
  | .eq s t, N =>
    Nat.lt_succ_of_le (Nat.le_trans (count_or_le (fun i => occT i s) (fun i => occT i t) N)
      (Nat.add_le_add (tcount_le s N) (tcount_le t N)))
  | .neg φ, N => Nat.lt_succ_of_lt (fcount_lt φ N)
  | .conj φ ψ, N =>
    Nat.lt_succ_of_le (Nat.le_trans (count_or_le (fun i => occ i φ) (fun i => occ i ψ) N)
      (Nat.add_le_add (Nat.le_of_lt (fcount_lt φ N)) (Nat.le_of_lt (fcount_lt ψ N))))
  | .all φ, N =>
    Nat.lt_succ_of_lt (Nat.lt_of_le_of_lt (count_shift (fun i => occ i φ) N) (fcount_lt φ (N + 1)))

/-- 25:F3, 25:G6 (Corollary quotation, the arity) — a formula in which the `N` variables `j, …, j + N − 1` occur has more
than `N` symbols: a formula's arity is below its length. -/
theorem arity_lt_size (φ : Fm) (j N : Nat) (h : ∀ i, i < N → occ (i + j) φ = true) : N < size φ :=
  have h1 : count (fun i => occ (i + j) φ) N = N := count_full h
  Nat.lt_of_le_of_lt (Nat.le_trans (Nat.le_of_eq h1.symm) (count_shift_by j (fun i => occ i φ) N)) (fcount_lt φ (N + j))

/-- 25:F3, 25:G6 (Corollary quotation, the cost) — a formula whose truth in `M_p` depends on all `N` coordinates of a
tuple, the variables `j, …, j + N − 1`, has more than `N` symbols. -/
theorem mention_cost_lt (p : Nat) (φ : Fm) (j N : Nat)
    (h : ∀ i, i < N → ∃ env v, holds p (upd env (i + j) v) φ ≠ holds p env φ) : N < size φ :=
  arity_lt_size φ j N (fun i hi => match h i hi with
    | ⟨env, v, hdep⟩ => mention p φ env (i + j) v hdep)

/-- `Subformula ψ φ`: `ψ` is a subformula of `φ`. -/
inductive Subformula (ψ : Fm) : Fm → Prop where
  | refl : Subformula ψ ψ
  | neg {φ : Fm} : Subformula ψ φ → Subformula ψ (.neg φ)
  | conjL {φ χ : Fm} : Subformula ψ φ → Subformula ψ (.conj φ χ)
  | conjR {φ χ : Fm} : Subformula ψ χ → Subformula ψ (.conj φ χ)
  | all {φ : Fm} : Subformula ψ φ → Subformula ψ (.all φ)

theorem sub_size {ψ : Fm} : ∀ {φ : Fm}, Subformula ψ φ → size ψ ≤ size φ
  | _, .refl => Nat.le_refl _
  | _, .neg h => Nat.le_succ_of_le (sub_size h)
  | .conj φ χ, .conjL h => Nat.le_succ_of_le (Nat.le_trans (sub_size h) (Nat.le_add_right (size φ) (size χ)))
  | .conj φ χ, .conjR h => Nat.le_succ_of_le (Nat.le_trans (sub_size h) (Nat.le_add_left (size χ) (size φ)))
  | _, .all h => Nat.le_succ_of_le (sub_size h)

/-- 25:F3, 25:G6, 25:G7, 00:Z9 (Corollary quotation) — no sentence `lam` contains a subformula whose truth depends on all coordinates
of a tuple of arity `N ≥ |lam|`, wherever the tuple's variables `j, …, j + N − 1` sit in the subformula's frame:
the subformula would have more than `N` symbols, and it is no longer than `lam`. -/
theorem no_self_reading (p : Nat) {ψ lam : Fm} (hsub : Subformula ψ lam) (j N : Nat) (hN : size lam ≤ N) :
    ¬ ∀ i, i < N → ∃ env v, holds p (upd env (i + j) v) ψ ≠ holds p env ψ := fun h =>
  Nat.lt_irrefl N (Nat.lt_of_lt_of_le (mention_cost_lt p ψ j N h) (Nat.le_trans (sub_size hsub) hN))

/-! ### 25:F2 — the diagonal template does not fit at any scale -/

/-- `∃ x, φ`, written with the language's one quantifier: `¬ ∀ x, ¬ φ`. -/
def ex (φ : Fm) : Fm := .neg (.all (.neg φ))

/-- A block of `n` existential quantifiers in front of a formula. -/
def exBlock : Nat → Fm → Fm
  | 0, φ => φ
  | n + 1, φ => ex (exBlock n φ)

/-- 25:F1 (Lemma mention, the quantifier block) — a block binding an `n`-tuple contributes `3n` symbols in this
syntax, at least `n`. -/
theorem size_exBlock : ∀ (n : Nat) (φ : Fm), size (exBlock n φ) = size φ + 3 * n
  | 0, _ => rfl
  | n + 1, φ => by
    show size (exBlock n φ) + 1 + 1 + 1 = size φ + 3 * (n + 1)
    rw [size_exBlock n φ, Nat.mul_succ]; rfl

/-- 25:F2, 25:G7, 00:Z9 (Theorem nocompress, the accounting) — the diagonal formula `δ = ∃ v (Diag_N ∧ θ)`, with a block of `N`
quantifiers and a diagonal relation whose truth depends on all `2N` coordinates, has length at least
`2N + |θ| + 3N`: `2N` for the relation (mention cost), then `θ`, and three symbols for each quantifier of the
block (the paper counts one, which gives its `3N + |θ|`). -/
theorem template_size (p N : Nat) (diag θ : Fm)
    (hdep : ∀ i, i < 2 * N → ∃ env v, holds p (upd env i v) diag ≠ holds p env diag) :
    2 * N + size θ + 3 * N ≤ size (exBlock N (.conj diag θ)) := by
  have h2 : 2 * N ≤ size diag := mention_cost p diag (2 * N) hdep
  rw [size_exBlock]
  show 2 * N + size θ + 3 * N ≤ size diag + size θ + 1 + 3 * N
  exact Nat.add_le_add_right (Nat.le_trans (Nat.add_le_add_right h2 (size θ)) (Nat.le_succ _)) (3 * N)

/-- 25:F2, 00:Z9 (Theorem nocompress, the scale) — a formula that binds an `N`-tuple, `N ≥ 1`, is longer than `N`: the
diagonal formula `∃ v (Diag_N ∧ θ)` has no code in `M^N`.  The block alone gives this clause; no hypothesis on
`Diag_N` or `θ` enters. -/
theorem no_template (N : Nat) (hN : 1 ≤ N) (φ : Fm) : ¬ size (exBlock N φ) ≤ N := fun hle => by
  rw [size_exBlock] at hle
  have h3 : 3 * N ≤ N := Nat.le_trans (Nat.le_add_left (3 * N) (size φ)) hle
  have h4 : N + 1 ≤ 3 * N := by
    have : N + N ≤ 3 * N := by rw [← Nat.two_mul]; exact Nat.mul_le_mul_right N (by decide)
    exact Nat.le_trans (Nat.add_le_add_left hN N) this
  exact Nat.not_succ_le_self N (Nat.le_trans h4 h3)

/-- 25:F2, 00:Z9 (Theorem nocompress, splitting the scales) — if `θ` reads all `N₂` coordinates of its argument (the
non-degeneracy clause, at the scale `N₂` of the code of the fixed point), the diagonal formula is longer than
`N₂`, whatever the scale `N` of its own block: here the mention cost is what excludes the instance. -/
theorem split_scale (p N N₂ : Nat) (diag θ : Fm)
    (hθ : ∀ i, i < N₂ → ∃ env v, holds p (upd env i v) θ ≠ holds p env θ) :
    N₂ < size (exBlock N (.conj diag θ)) := by
  have h : N₂ ≤ size θ := mention_cost p θ N₂ hθ
  rw [size_exBlock]
  show N₂ < size diag + size θ + 1 + 3 * N
  exact Nat.lt_of_le_of_lt h (Nat.lt_of_lt_of_le (Nat.lt_succ_of_le (Nat.le_add_left (size θ) (size diag))) (Nat.le_add_right _ (3 * N)))

/-! ### 25:F4 — density does not rescue the template -/

/-! ### 25:G4 — the prefix simulation -/

/-- The coded prefix evaluated directly over a structure of `m` elements: `true` codes `∀`, `false` codes `∃`;
the matrix `ψ` reads the chosen values (the last chosen first). -/
def direct (m : Nat) (ψ : List Nat → Bool) : List Bool → List Nat → Bool
  | [], acc => ψ acc
  | true :: pat, acc => allBelow (fun x => direct m ψ pat (x :: acc)) m
  | false :: pat, acc => anyBelow (fun x => direct m ψ pat (x :: acc)) m

/-- The uniform prefix `∀ y₁ ∃ x₁ … ∀ y_d ∃ x_d` with the clause `x_i = y_i` conjoined at the coded universal
positions and the matrix read on the `x`s; `c` carries the clauses collected so far. -/
def paired (m : Nat) (ψ : List Nat → Bool) : List Bool → List Nat → Bool → Bool
  | [], acc, c => c && ψ acc
  | q :: pat, acc, c =>
    allBelow (fun y => anyBelow (fun x => paired m ψ pat (x :: acc) (c && (!q || decide (x = y)))) m) m

/-- 25:G4 (Lemma prefix) — the prefix simulation: over a structure of `m ≥ 1` elements the uniform pairing
prefix with the copy clauses decides exactly what the coded prefix `Q₁ … Q_d` decides, for every pattern and
every matrix. -/
theorem prefix_simulation (m : Nat) (hm : 0 < m) (ψ : List Nat → Bool) :
    ∀ (pat : List Bool) (acc : List Nat) (c : Bool), paired m ψ pat acc c = (c && direct m ψ pat acc)
  | [], _, _ => rfl
  | true :: pat, acc, c => by
    show allBelow (fun y => anyBelow (fun x => paired m ψ pat (x :: acc) (c && (!true || decide (x = y)))) m) m
        = (c && allBelow (fun x => direct m ψ pat (x :: acc)) m)
    rw [← allBelow_and_const c (fun x => direct m ψ pat (x :: acc)) m hm]
    refine allBelow_congr (fun y hy => ?_)
    have h1 : anyBelow (fun x => paired m ψ pat (x :: acc) (c && (!true || decide (x = y)))) m
        = anyBelow (fun x => (c && decide (x = y)) && direct m ψ pat (x :: acc)) m :=
      anyBelow_congr (fun x _ => prefix_simulation m hm ψ pat (x :: acc) (c && decide (x = y)))
    rw [h1, anyBelow_pick c (fun x => direct m ψ pat (x :: acc)) y m, ite_eq_left hy]
  | false :: pat, acc, c => by
    show allBelow (fun y => anyBelow (fun x => paired m ψ pat (x :: acc) (c && (!false || decide (x = y)))) m) m
        = (c && anyBelow (fun x => direct m ψ pat (x :: acc)) m)
    have h1 : ∀ y, anyBelow (fun x => paired m ψ pat (x :: acc) (c && (!false || decide (x = y)))) m
        = (c && anyBelow (fun x => direct m ψ pat (x :: acc)) m) := fun y => by
      rw [← anyBelow_and_const c (fun x => direct m ψ pat (x :: acc)) m]
      refine anyBelow_congr (fun x _ => ?_)
      have h2 : paired m ψ pat (x :: acc) (c && (!false || decide (x = y))) = ((c && true) && direct m ψ pat (x :: acc)) :=
        prefix_simulation m hm ψ pat (x :: acc) (c && true)
      rw [and_true' c] at h2
      exact h2
    rw [allBelow_congr (fun y _ => h1 y)]
    exact allBelow_const _ m hm

/-- 25:G4 (Lemma prefix, the statement) — with no clause collected, the pairing prefix equals the coded prefix. -/
theorem prefix_simulation_closed (m : Nat) (hm : 0 < m) (ψ : List Nat → Bool) (pat : List Bool) :
    paired m ψ pat [] true = direct m ψ pat [] :=
  prefix_simulation m hm ψ pat [] true

/-! ### 25:F7 — the decoders: `Int_J(x)` defines `{0, …, 2^J − 1}` -/

/-- `φ ∨ ψ`, with the language's connectives: `¬(¬φ ∧ ¬ψ)`. -/
def orF (φ ψ : Fm) : Fm := .neg (.conj (.neg φ) (.neg ψ))

theorem holds_conj_iff (p : Nat) (env : Nat → Nat) (φ ψ : Fm) :
    holds p env (.conj φ ψ) = true ↔ holds p env φ = true ∧ holds p env ψ = true :=
  ⟨fun h => ⟨band_l h, band_r h⟩, fun ⟨h1, h2⟩ => by show (holds p env φ && holds p env ψ) = true; rw [h1, h2]; rfl⟩

theorem holds_orF_iff (p : Nat) (env : Nat → Nat) (φ ψ : Fm) :
    holds p env (orF φ ψ) = true ↔ holds p env φ = true ∨ holds p env ψ = true := by
  show (!(!(holds p env φ) && !(holds p env ψ))) = true ↔ _
  match holds p env φ, holds p env ψ with
  | true, _ => exact ⟨fun _ => .inl rfl, fun _ => rfl⟩
  | false, true => exact ⟨fun _ => .inr rfl, fun _ => rfl⟩
  | false, false => exact ⟨fun h => Bool.noConfusion h, fun h => match h with | .inl e => Bool.noConfusion e | .inr e => Bool.noConfusion e⟩

theorem not_allBelow_not (f : Nat → Bool) : ∀ n, (!(allBelow (fun y => !(f y)) n)) = anyBelow f n
  | 0 => rfl
  | n + 1 => by
    show (!((!(f n)) && allBelow (fun y => !(f y)) n)) = (f n || anyBelow f n)
    rw [← not_allBelow_not f n]
    cases f n <;> cases allBelow (fun y => !(f y)) n <;> rfl

theorem holds_ex_iff (p : Nat) (env : Nat → Nat) (φ : Fm) :
    holds p env (ex φ) = true ↔ ∃ y, y < p ∧ holds p (cons y env) φ = true := by
  show (!(allBelow (fun y => !(holds p (cons y env) φ)) p)) = true ↔ _
  rw [not_allBelow_not]
  exact anyBelow_true_iff _ p

theorem holds_eq_iff (p : Nat) (env : Nat → Nat) (s t : VTm) :
    holds p env (.eq s t) = true ↔ tval p env s = tval p env t :=
  ⟨of_decide_eq_true, decide_eq_true⟩

/-- `seg_J(x, w)`: `x ∈ {0, w, 2w, …, (2^J − 1) w}` in `M_p`, written with two reused bound variables per level:
`seg_0(x, w) := x = 0`; `seg_{J+1}(x, w) := ∃ y ((x = y ∨ x = y + w) ∧ ∃ w' (w' = w + w ∧ seg_J(y, w')))`. The arguments
are variable indices; under each quantifier the outer variables shift up by one. -/
def seg : Nat → Nat → Nat → Fm
  | 0, x, _ => .eq (.var x) .zero
  | J + 1, x, w =>
    ex (.conj (orF (.eq (.var (x + 1)) (.var 0)) (.eq (.var (x + 1)) (.add (.var 0) (.var (w + 1)))))
      (ex (.conj (.eq (.var 0) (.add (.var (w + 2)) (.var (w + 2)))) (seg J 1 0))))

/-- `Int_J(x) := ∃ w (w = 1 ∧ seg_J(x, w))`. -/
def IntJ (J x : Nat) : Fm := ex (.conj (.eq (.var 0) .one) (seg J (x + 1) 0))

/-- The values `seg_J(·, w)` admits, in the arithmetic of `M_p`: the multiples `c·w mod p` for `c < 2^J`, built level by
level. -/
def InSeg (p : Nat) : Nat → Nat → Nat → Prop
  | 0, _, x => x = 0
  | J + 1, w, x => ∃ y, y < p ∧ InSeg p J ((w + w) % p) y ∧ (x = y ∨ x = (y + w) % p)

/-- 25:F7 (Lemma decoders, the semantics of `seg`) — `seg_J(x, w)` holds exactly when `x` is among the values the levels
admit. -/
theorem holds_seg_iff (p : Nat) : ∀ (J : Nat) (env : Nat → Nat) (x w : Nat),
    holds p env (seg J x w) = true ↔ InSeg p J (env w) (env x)
  | 0, env, x, w => by
    show decide (env x = 0) = true ↔ env x = 0
    exact ⟨of_decide_eq_true, decide_eq_true⟩
  | J + 1, env, x, w => by
    show holds p env (ex (.conj (orF (.eq (.var (x + 1)) (.var 0)) (.eq (.var (x + 1)) (.add (.var 0) (.var (w + 1)))))
      (ex (.conj (.eq (.var 0) (.add (.var (w + 2)) (.var (w + 2)))) (seg J 1 0))))) = true
      ↔ ∃ y, y < p ∧ InSeg p J ((env w + env w) % p) y ∧ (env x = y ∨ env x = (y + env w) % p)
    refine (holds_ex_iff p env _).trans ⟨?_, ?_⟩
    · intro ⟨y, hy, h⟩
      have h' := (holds_conj_iff _ _ _ _).1 h
      have hor := (holds_orF_iff _ _ _ _).1 h'.1
      have hin := (holds_ex_iff _ _ _).1 h'.2
      match hin with
      | ⟨w', hw', h2⟩ =>
        have h2' := (holds_conj_iff _ _ _ _).1 h2
        have ew' : w' = (env w + env w) % p := (holds_eq_iff _ _ _ _).1 h2'.1
        have hseg := (holds_seg_iff p J (cons w' (cons y env)) 1 0).1 h2'.2
        -- cons w' (cons y env) reads 0 ↦ w', 1 ↦ y
        have hseg' : InSeg p J ((env w + env w) % p) y := by
          have e : InSeg p J (cons w' (cons y env) 0) (cons w' (cons y env) 1) = InSeg p J w' y := rfl
          rw [e, ew'] at hseg; exact hseg
        refine ⟨y, hy, hseg', ?_⟩
        match hor with
        | .inl e => exact .inl ((holds_eq_iff _ _ _ _).1 e)
        | .inr e => exact .inr ((holds_eq_iff _ _ _ _).1 e)
    · intro ⟨y, hy, hseg, hor⟩
      refine ⟨y, hy, (holds_conj_iff _ _ _ _).2 ⟨(holds_orF_iff _ _ _ _).2 ?_, (holds_ex_iff _ _ _).2
        ⟨(env w + env w) % p, FRC.Nat.mod_lt' _ (Nat.lt_of_le_of_lt (Nat.zero_le _) hy),
          (holds_conj_iff _ _ _ _).2 ⟨(holds_eq_iff _ _ _ _).2 rfl, (holds_seg_iff p J _ 1 0).2 hseg⟩⟩⟩⟩
      match hor with
      | .inl e => exact .inl ((holds_eq_iff _ _ _ _).2 e)
      | .inr e => exact .inr ((holds_eq_iff _ _ _ _).2 e)

/-- Every natural is `2c' + r` with `r < 2`, by induction (no division). -/
theorem half_decomp : ∀ c : Nat, ∃ c' r, r < 2 ∧ c = 2 * c' + r
  | 0 => ⟨0, 0, Nat.zero_lt_two, rfl⟩
  | c + 1 =>
    match half_decomp c with
    | ⟨c', 0, _, e⟩ => ⟨c', 1, Nat.lt_succ_self 1, by rw [e]⟩
    | ⟨c', 1, _, e⟩ => ⟨c' + 1, 0, Nat.zero_lt_two, by rw [e, Nat.mul_succ]⟩
    | ⟨_, r + 2, hr, _⟩ => absurd hr (Nat.not_lt_of_ge (Nat.le_add_left 2 r))

theorem lt_of_two_mul_lt {a b : Nat} (h : 2 * a < 2 * b) : a < b :=
  Nat.lt_of_not_ge (fun hge => Nat.lt_irrefl _ (Nat.lt_of_lt_of_le h (Nat.mul_le_mul_left 2 hge)))

/-- 25:F7 (Lemma decoders, the arithmetic of the levels) — the values `seg_J(·, w)` admits are exactly the multiples
`c·w mod p` with `c < 2^J`. -/
theorem inSeg_iff (p : Nat) (hp : 0 < p) : ∀ (J w x : Nat), InSeg p J w x ↔ ∃ c, c < 2 ^ J ∧ x = (c * w) % p
  | 0, w, x => by
    show x = 0 ↔ ∃ c, c < 2 ^ 0 ∧ x = (c * w) % p
    exact ⟨fun e => ⟨0, Nat.lt_succ_self 0, by rw [e, Nat.zero_mul]; rfl⟩,
      fun ⟨c, hc, e⟩ => by
        have e0 : c = 0 := Nat.le_zero.1 (Nat.le_of_lt_succ hc)
        rw [e, e0, Nat.zero_mul]; rfl⟩
  | J + 1, w, x => by
    show (∃ y, y < p ∧ InSeg p J ((w + w) % p) y ∧ (x = y ∨ x = (y + w) % p)) ↔ ∃ c, c < 2 ^ (J + 1) ∧ x = (c * w) % p
    have key : ∀ c', (c' * ((w + w) % p)) % p = (2 * c' * w) % p := fun c' => by
      rw [FRC.Nat.mul_mod_mod _ _ _ hp, ← Nat.two_mul, FRC.Nat.mul_left_comm, ← FRC.Nat.mul_assoc]
    constructor
    · intro ⟨y, _, hy, hor⟩
      match (inSeg_iff p hp J _ y).1 hy with
      | ⟨c', hc', ey⟩ =>
        rw [key c'] at ey
        have hc'2 : 2 * c' < 2 * 2 ^ J := Nat.mul_lt_mul_of_pos_left hc' Nat.zero_lt_two
        match hor with
        | .inl e => exact ⟨2 * c', by rw [Nat.pow_succ, Nat.mul_comm (2 ^ J) 2]; exact hc'2, e.trans ey⟩
        | .inr e =>
          have h21 : 2 * c' + 1 < 2 * 2 ^ J := by
            have : 2 * (c' + 1) ≤ 2 * 2 ^ J := Nat.mul_le_mul_left 2 (Nat.succ_le_of_lt hc')
            rw [Nat.mul_succ] at this
            exact Nat.lt_of_lt_of_le (Nat.lt_succ_self _) this
          exact ⟨2 * c' + 1, by rw [Nat.pow_succ, Nat.mul_comm (2 ^ J) 2]; exact h21,
            by rw [e, ey, FRC.Nat.mod_add_mod _ _ _ hp, FRC.Nat.add_mul, Nat.one_mul]⟩
    · intro ⟨c, hc, ex⟩
      match half_decomp c with
      | ⟨c', r, hr, ec⟩ =>
        have hc' : c' < 2 ^ J := by
          have : 2 * c' < 2 * 2 ^ J := by
            rw [Nat.pow_succ, Nat.mul_comm (2 ^ J) 2] at hc
            exact Nat.lt_of_le_of_lt (Nat.le_add_right _ r) (ec ▸ hc)
          exact lt_of_two_mul_lt this
        refine ⟨(c' * ((w + w) % p)) % p, FRC.Nat.mod_lt' _ hp, (inSeg_iff p hp J _ _).2 ⟨c', hc', rfl⟩, ?_⟩
        rw [key c', ex, ec]
        match r, hr with
        | 0, _ => exact .inl (by rw [Nat.add_zero])
        | 1, _ => exact .inr (by rw [FRC.Nat.mod_add_mod _ _ _ hp, FRC.Nat.add_mul, Nat.one_mul])
        | r + 2, hr => exact absurd hr (Nat.not_lt_of_ge (Nat.le_add_left 2 r))

/-- 25:F7 (Lemma decoders) — over `M_p` with `2^J ≤ p`, `Int_J(x)` holds exactly when `x < 2^J`: the formula defines
`{0, …, 2^J − 1}` by writing the binary expansion along `J` doublings of the unit. -/
theorem intJ_defines (p : Nat) (hp : 2 ≤ p) (J : Nat) (hJ : 2 ^ J ≤ p) (env : Nat → Nat) (x : Nat) (hx : env x < p) :
    holds p env (IntJ J x) = true ↔ env x < 2 ^ J := by
  have hp0 : 0 < p := Nat.lt_of_lt_of_le Nat.zero_lt_two hp
  show holds p env (ex (.conj (.eq (.var 0) .one) (seg J (x + 1) 0))) = true ↔ _
  refine (holds_ex_iff p env _).trans ⟨?_, ?_⟩
  · intro ⟨w, _, h⟩
    have h' := (holds_conj_iff _ _ _ _).1 h
    have ew : w = 1 % p := (holds_eq_iff _ _ _ _).1 h'.1
    rw [FRC.Nat.mod_eq_of_lt (Nat.lt_of_lt_of_le Nat.one_lt_two hp)] at ew
    have hseg := (holds_seg_iff p J (cons w env) (x + 1) 0).1 h'.2
    have e : InSeg p J (cons w env 0) (cons w env (x + 1)) = InSeg p J w (env x) := rfl
    rw [e, ew] at hseg
    match (inSeg_iff p hp0 J 1 (env x)).1 hseg with
    | ⟨c, hc, ec⟩ =>
      rw [Nat.mul_one, FRC.Nat.mod_eq_of_lt (Nat.lt_of_lt_of_le hc hJ)] at ec
      rw [ec]; exact hc
  · intro hlt
    refine ⟨1, Nat.lt_of_lt_of_le Nat.one_lt_two hp, (holds_conj_iff _ _ _ _).2
      ⟨(holds_eq_iff _ _ _ _).2 (FRC.Nat.mod_eq_of_lt (Nat.lt_of_lt_of_le Nat.one_lt_two hp)).symm, ?_⟩⟩
    refine (holds_seg_iff p J (cons 1 env) (x + 1) 0).2 ?_
    show InSeg p J 1 (env x)
    exact (inSeg_iff p hp0 J 1 (env x)).2 ⟨env x, hlt, by rw [Nat.mul_one, FRC.Nat.mod_eq_of_lt hx]⟩

/-- 25:F7 (Lemma decoders, the length) — `seg_J` has `25J + 3` symbols in this syntax (a variable is one symbol here; the
row's `50J + 29` counts the alphabet of 25:F8, where the names are spelt out). -/
theorem size_seg : ∀ (J x w : Nat), size (seg J x w) = 25 * J + 3
  | 0, _, _ => rfl
  | J + 1, x, w => by
    have e : size (seg (J + 1) x w) = 12 + (5 + size (seg J 1 0) + 1 + 1 + 1 + 1) + 1 + 1 + 1 + 1 := rfl
    rw [e, Nat.add_comm 12, Nat.add_comm 5, size_seg J 1 0, Nat.mul_succ]

/-- 25:F7 (Lemma decoders, the length) — `Int_J` has `25J + 10` symbols: linear in `J`. -/
theorem size_IntJ (J x : Nat) : size (IntJ J x) = 25 * J + 10 := by
  have e : size (IntJ J x) = 3 + size (seg J (x + 1) 0) + 1 + 1 + 1 + 1 := rfl
  rw [e, Nat.add_comm 3, size_seg]

/-! ### 00:Z9 — the window's digits against the totality -/

/-- 00:Z9 (the window, in digit counts) — the chart's bound of `Ω` (`00:A7`, `Ω < 1.33 × 10^123`) has `82` base-32 digits
(`32^81 ≤ 1.32 × 10^123` and `1.33 × 10^123 < 32^82`), fewer than the `1,024` base-32 symbols an element of the
dense-coded instance of 25:F8 holds: that instance exists in no shell of the totality. No number above `Ω`'s digit bound
is named. -/
theorem window_beyond_totality : 32 ^ 81 ≤ 132 * 10 ^ 121 ∧ 133 * 10 ^ 121 < 32 ^ 82 ∧ 82 < 1024 := by decide

end FRC.Diagonal
