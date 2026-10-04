import Mathlib
import FrcLedger.Reductio

/-!
# 25-göd — incompleteness without infinity: the ledger predicates on Mathlib

Predicates of the ledger of *Incompleteness Without Infinity* (tree `25-godel-20260614`) stated on Mathlib's
hierarchy.

* 25:C1 — a carrier with an injective successor that omits an element is not finite, so every model of `Q` is
  infinite.
* 25:C2 — the theory of a structure is complete, and a finite structure decides each sentence.
* 25:C5 — among `m + 1` sentences of a first-order language two receive the same number in a structure of `m`
  elements.
* 25:D1, 25:D3 — an agent with fewer storage states than the structure has elements has no injective encoding.
  Some reading stands for at least `⌈m / a^K⌉ ≥ 2` elements. Every element outside a maximal faithfully read
  range is an alias of one inside it.
* 25:E1 — the binary trees with `n + 1` inner nodes number at least `2^n`, and the equations between two of them
  at least `2^ℓ` from `ℓ = 6` leaves on.
* 25:E2 — the records of length at most `B` number fewer than `a^(B+1)`.
* 25:F4 — an injective coding of strings into tuples needs `a^n ≤ m^k`.
* 25:H2 — over a finite domain a second-order quantifier ranges over `2^(m^k)` relations.

The axioms of each declaration are in `lean/axioms.log`.
-/

open FirstOrder FirstOrder.Language

namespace FRC.Godel

/-! ### 25:C1, 25:C2, 25:C5 — Gödel's hypotheses over a finite structure -/

section vacuity

/-- 25:C1 (Proposition noQ, the finite form) — on a finite carrier an injective map is onto: no successor is
injective and omits an element. -/
theorem finite_succ_onto {A : Type*} [Finite A] (S : A → A) (hinj : Function.Injective S) (z : A) : ∃ x, S x = z :=
  Finite.surjective_of_injective hinj z

/-- 25:C1 (Proposition noQ) — every model of `Q` is infinite: a carrier with an injective successor `S` and an
element outside its range is not finite, so no finite structure interprets `Q`. -/
theorem infinite_of_succ {A : Type*} (S : A → A) (z : A) (hinj : Function.Injective S) (hz : ∀ x, S x ≠ z) :
    Infinite A :=
  not_finite_iff_infinite.mp (fun _ => (finite_succ_onto S hinj z).elim (fun x hx => hz x hx))

variable {L : Language} {M : Type*} [L.Structure M]

/-- 25:C2 (Proposition complete) — the theory of a structure is complete: satisfiable, and deciding every
sentence one way or the other. -/
theorem theory_complete [Nonempty M] : (L.completeTheory M).IsComplete := completeTheory.isComplete L M

/-- 25:C2 (Proposition complete, decidability) — in a finite structure with decidable relations, membership in
the theory is decided by evaluating the sentence, each quantifier ranging over the finitely many elements. -/
@[instance_reducible] def decTheory [Fintype M] [DecidableEq M]
    (hR : ∀ (n : ℕ) (R : L.Relations n) (x : Fin n → M), Decidable (Structure.RelMap R x)) :
    DecidablePred (· ∈ L.completeTheory M) := FRC.Reductio.decTheory hR

/-- The sentences `⊥, ¬⊥, ¬¬⊥, …`. -/
def nots (L : Language) : ℕ → L.Sentence
  | 0 => (⊥ : L.Sentence)
  | n + 1 => (nots L n).not

theorem nots_injective (L : Language) : Function.Injective (nots L) := by
  intro a
  induction a with
  | zero =>
    intro b h
    cases b with
    | zero => rfl
    | succ b => exact absurd h (by simp [nots, BoundedFormula.not])
  | succ a ih =>
    intro b h
    cases b with
    | zero => exact absurd h (by simp [nots, BoundedFormula.not])
    | succ b =>
      have h' : (nots L a).imp ⊥ = (nots L b).imp ⊥ := h
      rw [BoundedFormula.imp.injEq] at h'
      exact congrArg Nat.succ (ih h'.1)

omit [L.Structure M] in
/-- Remark Tarski scoped, the classical form (cited by no row; the row's finite form is `nots_collide`) — no
numbering of all the sentences of a first-order language into a finite structure is injective. -/
theorem no_goedel_numbering [Finite M] (f : L.Sentence → M) : ¬ Function.Injective f := fun hf =>
  haveI : Infinite L.Sentence := Infinite.of_injective (nots L) (nots_injective L)
  not_injective_infinite_finite f hf

end vacuity

/-- 25:C5 (Remark Tarski scoped, the row's finite form) — among the `m + 1` sentences `⊥, ¬⊥, …, ¬^m ⊥` two
distinct ones receive the same number, whatever the numbering into a structure of `m` elements. -/
theorem nots_collide {L : Language} {M : Type*} [Fintype M] (f : L.Sentence → M) :
    ∃ i j, i < j ∧ j ≤ Fintype.card M ∧ nots L i ≠ nots L j ∧ f (nots L i) = f (nots L j) := by
  have h : Fintype.card M < Fintype.card (Fin (Fintype.card M + 1)) := by simp
  obtain ⟨a, b, hab, hf⟩ := Fintype.exists_ne_map_eq_of_card_lt (fun k : Fin (Fintype.card M + 1) => f (nots L k)) h
  rcases lt_or_gt_of_ne (Fin.val_ne_of_ne hab) with hlt | hgt
  · exact ⟨a, b, hlt, Nat.lt_succ_iff.mp b.isLt, fun e => (Nat.ne_of_lt hlt) (nots_injective L e), hf⟩
  · exact ⟨b, a, hgt, Nat.lt_succ_iff.mp a.isLt, fun e => (Nat.ne_of_lt hgt) (nots_injective L e), hf.symm⟩

/-! ### 25:D1, 25:D3 — the part cannot hold the whole -/

section part

/-- 25:D1 (Theorem part (1)) — an agent whose storage takes `a^K` states (strings of length `K` over an alphabet
of `a` letters) in a structure of more than `a^K` elements has no injective encoding of the elements. -/
theorem no_injective_encoding {A Alph : Type*} [Fintype A] [Fintype Alph] (K : ℕ)
    (h : Fintype.card Alph ^ K < Fintype.card A) (ρ : A → (Fin K → Alph)) : ¬ Function.Injective ρ := fun hinj => by
  have := Fintype.card_le_of_injective ρ hinj
  rw [Fintype.card_pi_const] at this
  exact absurd this (Nat.not_le.mpr h)

/-- 25:D3 (Lemma wrap (1), aliasing) — every total reading identifies distinct elements when the states are
fewer than the elements. -/
theorem reading_identifies {A R : Type*} [Fintype A] [Fintype R] (h : Fintype.card R < Fintype.card A) (ρ : A → R) :
    ∃ x y, x ≠ y ∧ ρ x = ρ y :=
  Fintype.exists_ne_map_eq_of_card_lt ρ h

/-- 25:D3 (Lemma wrap (1), the multiplicity) — some reading stands for at least `⌈m / a^K⌉` elements: its
fibre, multiplied by the number of states, covers the structure. -/
theorem alias_fibre {A R : Type*} [Fintype A] [Fintype R] [DecidableEq R] [Nonempty R] (ρ : A → R) :
    ∃ y, Fintype.card A ≤ Fintype.card R * Fintype.card {x // ρ x = y} := by
  by_contra h
  simp only [not_exists, not_le] at h
  have hsum : Fintype.card A = ∑ y : R, (Finset.univ.filter (fun x => ρ x = y)).card := by
    rw [← Finset.card_univ]; exact Finset.card_eq_sum_card_fiberwise (fun x _ => Finset.mem_univ (ρ x))
  obtain ⟨y0⟩ := ‹Nonempty R›
  have hlt : ∑ y : R, Fintype.card R * (Finset.univ.filter (fun x => ρ x = y)).card < ∑ _y : R, Fintype.card A :=
    Finset.sum_lt_sum_of_nonempty ⟨y0, Finset.mem_univ _⟩ (fun y _ => by
      have := h y; rwa [Fintype.card_subtype] at this)
  rw [← Finset.mul_sum, ← hsum, Finset.sum_const, Finset.card_univ, smul_eq_mul] at hlt
  exact lt_irrefl _ hlt

/-- 25:D3 (Lemma wrap (1), at least two) — with fewer states than elements some reading stands for at least two
elements. -/
theorem alias_two {A R : Type*} [Fintype A] [Fintype R] [DecidableEq R] [Nonempty R]
    (h : Fintype.card R < Fintype.card A) (ρ : A → R) : ∃ y, 2 ≤ Fintype.card {x // ρ x = y} := by
  obtain ⟨y, hy⟩ := alias_fibre ρ
  refine ⟨y, ?_⟩
  by_contra hlt
  have h1 : Fintype.card {x // ρ x = y} ≤ 1 := by omega
  have h2 : Fintype.card R * Fintype.card {x // ρ x = y} ≤ Fintype.card R * 1 := Nat.mul_le_mul_left _ h1
  omega

/-- 25:D3 (Lemma wrap (1), the aliases) — every element outside a maximal faithfully represented range (a set
on which the reading is injective and which no larger set with that property contains) is read as an element
inside it. -/
theorem alias_outside {A R : Type*} (ρ : A → R) (S : Set A) (hS : Set.InjOn ρ S)
    (hmax : ∀ T : Set A, S ⊆ T → Set.InjOn ρ T → T = S) (x : A) (hx : x ∉ S) : ∃ s ∈ S, ρ s = ρ x := by
  by_contra h
  have h' : ∀ s ∈ S, ρ s ≠ ρ x := fun s hs he => h ⟨s, hs, he⟩
  have hT : Set.InjOn ρ (insert x S) := by
    intro a ha b hb hab
    rcases Set.mem_insert_iff.mp ha with rfl | ha' <;> rcases Set.mem_insert_iff.mp hb with rfl | hb'
    · rfl
    · exact absurd hab.symm (h' b hb')
    · exact absurd hab (h' a ha')
    · exact hS ha' hb' hab
  have hEq := hmax (insert x S) (Set.subset_insert x S) hT
  have hx' : x ∈ insert x S := Set.mem_insert x S
  rw [hEq] at hx'
  exact hx hx'

end part

/-! ### 25:E1, 25:E2 — the reach bound -/

section reach

theorem two_mul_catalan_le (n : ℕ) : 2 * catalan (n + 1) ≤ catalan (n + 2) := by
  rw [catalan_succ (n + 1), Fin.sum_univ_succ, Fin.sum_univ_castSucc]
  simp only [Fin.val_zero, Fin.val_succ, Fin.val_last, Fin.val_castSucc, catalan_zero, Nat.sub_zero, one_mul,
    Nat.sub_self, mul_one]
  omega

/-- 25:E1 (Lemma abundance, the Catalan bound) — `C_{ℓ−1} ≥ 2^{ℓ−2}` for `ℓ ≥ 2`: `2^n ≤ catalan (n + 1)`. -/
theorem two_pow_le_catalan : ∀ n : ℕ, 2 ^ n ≤ catalan (n + 1)
  | 0 => by simp
  | n + 1 => by
    calc 2 ^ (n + 1) = 2 * 2 ^ n := by ring
      _ ≤ 2 * catalan (n + 1) := Nat.mul_le_mul_left 2 (two_pow_le_catalan n)
      _ ≤ catalan (n + 2) := two_mul_catalan_le n

/-- 25:E1 (Lemma abundance, the cohort) — from `ℓ = n + 6` leaves on, the pairs of distinct terms with `ℓ` leaves
number at least `2^ℓ`: `2^(n+6) ≤ C(C_{n+5}, 2)`. -/
theorem cohort_lower (n : ℕ) : 2 ^ (n + 6) ≤ (catalan (n + 5)).choose 2 := by
  have h1 : 2 ^ (n + 4) ≤ catalan (n + 5) := two_pow_le_catalan (n + 4)
  refine le_trans ?_ (Nat.choose_le_choose 2 h1)
  have h16 : 16 ≤ 2 ^ (n + 4) := by
    calc 16 = 2 ^ 4 := by norm_num
      _ ≤ 2 ^ (n + 4) := Nat.pow_le_pow_right (by norm_num) (by omega)
  obtain ⟨y, hy⟩ : ∃ y, 2 ^ (n + 4) = y + 1 := ⟨2 ^ (n + 4) - 1, by omega⟩
  have e : 2 ^ (n + 6) = 4 * (y + 1) := by rw [← hy]; ring
  rw [e, hy, Nat.choose_two_right, Nat.add_sub_cancel, Nat.le_div_iff_mul_le (by norm_num)]
  nlinarith

/-- 25:E1 (Lemma abundance, the count) — the binary trees with `n + 1` inner nodes number at least `2^n`.  They
are the shapes of the closed terms with `ℓ = n + 2` leaves; that identification is the lemma's and is not proved
here. -/
theorem abundance (n : ℕ) : 2 ^ n ≤ (BinaryTree.treesOfNumNodesEq (n + 1)).card := by
  rw [BinaryTree.treesOfNumNodesEq_card_eq_catalan]; exact two_pow_le_catalan n

/-- 25:E2 (Proposition reach, the count) — the records of length at most `B` over `a ≥ 2` letters number fewer
than `a^(B+1)`. -/
theorem records_lt (a B : ℕ) (ha : 2 ≤ a) : ∑ i ∈ Finset.range (B + 1), a ^ i < a ^ (B + 1) :=
  Nat.geomSum_lt ha (fun _ hk => Finset.mem_range.mp hk)

end reach

/-! ### 25:F4 — density -/

/-- 25:F4 (Lemma density, the count) — an injective coding of the strings of length `n` over an alphabet of `a`
letters into `k`-tuples over a structure of `m` elements needs `a^n ≤ m^k`. -/
theorem dense_coding {A M : Type*} [Fintype A] [Fintype M] (n k : ℕ) (c : (Fin n → A) → (Fin k → M))
    (hc : Function.Injective c) : Fintype.card A ^ n ≤ Fintype.card M ^ k := by
  have := Fintype.card_le_of_injective c hc
  rwa [Fintype.card_pi_const, Fintype.card_pi_const] at this

/-! ### 25:H2 — second-order quantifiers over a finite domain -/

section finiteness

/-- 25:H2 (Theorem finiteness, the finite direction, the procedure) — a second-order statement over the `k`-ary
relations of a finite structure is decided by exhaustive evaluation. -/
def decideAllRelations {M : Type*} [Fintype M] [DecidableEq M] (k : ℕ) (P : Finset (Fin k → M) → Prop)
    [DecidablePred P] : Decidable (∀ R, P R) := inferInstance

/-- 25:H2 (Theorem finiteness, the finite direction) — over a structure of `m` elements a second-order
quantifier over `k`-ary relations ranges over the `2^(m^k)` subsets of `M^k`, a finite set. -/
theorem card_relations (M : Type*) [Fintype M] [DecidableEq M] (k : ℕ) :
    Fintype.card (Finset (Fin k → M)) = 2 ^ (Fintype.card M ^ k) := by
  rw [Fintype.card_finset, Fintype.card_pi_const]

end finiteness




-- Ledger predicates of 25-godel (generated by make_predicates.py from docs/25-godel/25-godel-ledger.json; edit the ledger, not this section)
/-- 25:C1 (p25010) — No finite structure interprets $\mathsf{Q}$: a model of $\mathsf{Q}$ has an injective successor with $0$ outside its range, and on a finite set an injective map is onto. -/
theorem p25010 : (∀ {A : Type u_1} [Finite A] (S : A → A), Function.Injective S → ∀ (z : A), ∃ x, S x = z) ∧ ∀ {A : Type u_2} (S : A → A) (z : A), Function.Injective S → (∀ (x : A), S x ≠ z) → Infinite A :=
  And.intro @FRC.Godel.finite_succ_onto (@FRC.Godel.infinite_of_succ)
/-- 25:C2 (p25011) — Completeness and decidability: for finite $\M$ the theory $\Th(\M)$ is complete, consistent and decidable by exhaustive evaluation. A sentence of quantifier depth $q$ takes at most $c\,m^{q}$ atomic evaluations, $c$ depending on its length. One first-order sentence $\sigma_{\M}$ characterises $\M$ up to isomorphism. Cited definitions (not proofs): FRC.Godel.decTheory. -/
theorem p25011 : ∀ {L : FirstOrder.Language} {M : Type u_1} [L.Structure M] [Nonempty M], (L.completeTheory M).IsComplete :=
  @FRC.Godel.theory_complete
/-- 25:C5 (p25014) — Tarski scoped: the $m+1$ sentences $\varphi,\neg\varphi,\dots,\neg^{m}\varphi$ outnumber the $m$ elements of $\M$, so every numbering of the sentences by elements of $\M$ gives two of them the same number. Truth in $\M$ is defined externally by a finite table with the evaluation procedure of C2. What fails is the internalisation of truth. -/
theorem p25014 : ∀ {L : FirstOrder.Language} {M : Type u_1} [Fintype M] (f : L.Sentence → M), ∃ i j, i < j ∧ j ≤ Fintype.card M ∧ FRC.Godel.nots L i ≠ FRC.Godel.nots L j ∧ f (FRC.Godel.nots L i) = f (FRC.Godel.nots L j) :=
  @FRC.Godel.nots_collide
/-- 25:D1 (p25015) — Relational diagonal: an agent of storage capacity $K$ with $a^{K}<m$ has no injective encoding of the elements of $\M$ into its storage states. Every internal representation identifies distinct elements. A fortiori the agent holds no faithful model of $\M$ that also represents the model's own encoding map. -/
theorem p25015 : ∀ {A : Type u_1} {Alph : Type u_2} [Fintype A] [Fintype Alph] (K : ℕ), Fintype.card Alph ^ K < Fintype.card A → ∀ (ρ : A → Fin K → Alph), ¬Function.Injective ρ :=
  @FRC.Godel.no_injective_encoding
/-- 25:D3 (p25017) — Wrap, aliasing: every total assignment of storage readings to the elements of $\M$ identifies distinct elements when $a^{K}<m$. Some reading stands for at least $\lceil m/a^{K}\rceil\ge2$ elements. Every element outside a maximal faithfully represented range is read as an alias of one inside it. -/
theorem p25017 : (∀ {A : Type u_1} {R : Type u_2} [Fintype A] [Fintype R], Fintype.card R < Fintype.card A → ∀ (ρ : A → R), ∃ x y, x ≠ y ∧ ρ x = ρ y) ∧ (∀ {A : Type u_3} {R : Type u_4} [Fintype A] [Fintype R] [DecidableEq R] [Nonempty R] (ρ : A → R), ∃ y, Fintype.card A ≤ Fintype.card R * Fintype.card { x // ρ x = y }) ∧ (∀ {A : Type u_5} {R : Type u_6} [Fintype A] [Fintype R] [DecidableEq R] [Nonempty R], Fintype.card R < Fintype.card A → ∀ (ρ : A → R), ∃ y, (2 : ℕ) ≤ Fintype.card { x // ρ x = y }) ∧ ∀ {A : Type u_7} {R : Type u_8} (ρ : A → R) (S : Set A), Set.InjOn ρ S → (∀ (T : Set A), S ⊆ T → Set.InjOn ρ T → T = S) → ∀ x ∉ S, ∃ s ∈ S, ρ s = ρ x :=
  And.intro @FRC.Godel.reading_identifies (And.intro @FRC.Godel.alias_fibre (And.intro @FRC.Godel.alias_two (@FRC.Godel.alias_outside)))
/-- 25:E1 (p25019) — Abundance: the closed terms over $\{1,+\}$ with $\ell$ leaves are the full binary trees, $C_{\ell-1}\ge2^{\ell-2}$ in number. In $\M_p$ all have the value $\ell\bmod p$, so any two give a true equation of length $O(\ell)$, at least $2^{\ell}$ of them for $\ell\ge6$. The true sentences of length at most $L$ number at least $2^{\alpha L}$ for large $L$, $\alpha>0$ constant. -/
theorem p25019 : (∀ (n : ℕ), (2 : ℕ) ^ n ≤ catalan (n + (1 : ℕ))) ∧ (∀ (n : ℕ), (2 : ℕ) ^ (n + (6 : ℕ)) ≤ (catalan (n + (5 : ℕ))).choose (2 : ℕ)) ∧ ∀ (n : ℕ), (2 : ℕ) ^ n ≤ (BinaryTree.treesOfNumNodesEq (n + (1 : ℕ))).card :=
  And.intro @FRC.Godel.two_pow_le_catalan (And.intro @FRC.Godel.cohort_lower (@FRC.Godel.abundance))
/-- 25:E2 (p25020) — Vanishing reach: an agent of capacity $(K,H)$ certifies at most $a^{B+1}$ sentences over all its runs, the records being strings of length at most $B$. The certified fraction of the truths of length at most $L$ (E1) is at most $a^{B+1}/2^{\alpha L}$, below $1/N$ for every $N$ once $L$ is large enough. -/
theorem p25020 : ∀ (a B : ℕ), (2 : ℕ) ≤ a → ∑ i ∈ Finset.range (B + (1 : ℕ)), a ^ i < a ^ (B + (1 : ℕ)) :=
  @FRC.Godel.records_lt
/-- 25:F4 (p25048) — Density: $m$ has $d$ base-$a$ digits. An injective coding of length-$n$ strings by $k$-tuples, $k\ge1$, needs $m^{k}\ge a^{n}$, so $n<dk$. In F2's $\delta(u)=\exists v\,(\mathrm{Diag}(u,v)\wedge\theta(v))$ let $v$ have $k$ coordinates and $u$ have $k_{1}$. Each coordinate of $v$ is named three times, each of $u$ once. So $\lvert\delta\rvert\ge2c(k)+c(k+k_{1})$, and $\lambda=\delta(\ulcorner\delta\urcorner)$ has $\lvert\lambda\rvert\ge3c(k)+k_{1}$, $c(j)$ the total length of the $j$ shortest names. -/
theorem p25048 : ∀ {A : Type u_1} {M : Type u_2} [Fintype A] [Fintype M] (n k : ℕ) (c : (Fin n → A) → Fin k → M), Function.Injective c → Fintype.card A ^ n ≤ Fintype.card M ^ k :=
  @FRC.Godel.dense_coding
/-- 25:H2 (p25036) — Finiteness, the finite direction: for finite $\M$ the full second-order theory $\ThSO(\M)$ is decidable. A second-order quantifier over $k$-ary relations ranges over the $2^{m^{k}}$ subsets of $\M^{k}$, and exhaustive evaluation decides every second-order sentence. Cited definitions (not proofs): FRC.Godel.decideAllRelations. -/
theorem p25036 : ∀ (M : Type u_1) [Fintype M] [DecidableEq M] (k : ℕ), Fintype.card (Finset (Fin k → M)) = (2 : ℕ) ^ Fintype.card M ^ k :=
  @FRC.Godel.card_relations
-- end ledger predicates

end FRC.Godel
