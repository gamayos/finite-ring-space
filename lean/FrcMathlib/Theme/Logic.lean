import Mathlib

/-!
# FrcMathlib.Theme.Logic — truth in a finite structure and the finite counting (the logic theme, task LM17)

The complete theory of a structure is complete; on a finite structure with decidable equality truth is decided by
evaluation (`decRealize`, `decTheory`); an injective successor missing a point forces an infinite carrier; Cantor's
theorem and its finite form; fewer than `s^(K+1)` records of length `≤ K`, and no injection into fewer states.
Moved from 5-reductio's module, which keeps every old name as an alias. Since 20 October 2026 (25-godel's migration) also
the paper's Mathlib side: the pigeonhole on a finite carrier, the `m + 1` sentences `⊥, ¬⊥, …`, the storage encodings and
aliasing, the Catalan bound of the abundance lemma, the dense coding, the second-order quantifier over a finite domain
(25:C1, C3, C5, D1, D3, E1, F4, H2, H4); `FrcMathlib/Godel.lean` keeps the old names. Since 21 October 2026 (5-reductio's
migration) the rest of that paper's Mathlib side: definable and periodic choice, the equivariant section criterion, the
obstruction on `𝔽₅`, no doubling and principal ultrafilters, the second-order quantifier over a finite domain and Dedekind's
embedding (5:D8, E1–E4, E8); `FrcMathlib/Reductio.lean` keeps the old names (and the paper's limit over the reals, which an
exact theme does not admit). Classical, on Mathlib's hierarchy.
-/

open FirstOrder FirstOrder.Language

namespace FRC.Logic

section frames

variable {L : Language} {M : Type*} [L.Structure M]

/-- 5:B5, 5:B3, 25:C2, 25:C3 (Proposition frame-complete, completeness): the theory of any structure — a finite frame `W_N` among
them — is complete: every sentence or its negation is in it. -/
theorem theory_complete [Nonempty M] : (L.completeTheory M).IsComplete := completeTheory.isComplete L M

/-- 5:B5 (decidability): in a finite structure with decidable relations, the truth of every bounded formula is
decided by evaluation — the quantifiers range over the finitely many elements. -/
def decRealize {α : Type*} [Fintype M] [DecidableEq M]
    (hR : ∀ (n : ℕ) (R : L.Relations n) (x : Fin n → M), Decidable (Structure.RelMap R x)) :
    ∀ {n : ℕ} (φ : L.BoundedFormula α n) (v : α → M) (xs : Fin n → M), Decidable (φ.Realize v xs)
  | _, .falsum, _, _ => isFalse id
  | _, .equal t₁ t₂, v, xs =>
    decidable_of_iff (t₁.realize (Sum.elim v xs) = t₂.realize (Sum.elim v xs)) Iff.rfl
  | _, .rel R ts, v, xs =>
    haveI := hR _ R fun i => (ts i).realize (Sum.elim v xs)
    decidable_of_iff (Structure.RelMap R fun i => (ts i).realize (Sum.elim v xs)) Iff.rfl
  | _, .imp f₁ f₂, v, xs =>
    haveI := decRealize hR f₁ v xs
    haveI := decRealize hR f₂ v xs
    decidable_of_iff (f₁.Realize v xs → f₂.Realize v xs) Iff.rfl
  | _, .all f, v, xs =>
    haveI : ∀ x : M, Decidable (f.Realize v (Fin.snoc xs x)) := fun x => decRealize hR f v (Fin.snoc xs x)
    decidable_of_iff (∀ x : M, f.Realize v (Fin.snoc xs x)) Iff.rfl

/-- 5:B5, 25:C2 (Proposition frame-complete, decidability): membership in the theory of a finite structure is decided
by evaluating the sentence. -/
@[instance_reducible] def decTheory [Fintype M] [DecidableEq M]
    (hR : ∀ (n : ℕ) (R : L.Relations n) (x : Fin n → M), Decidable (Structure.RelMap R x)) :
    DecidablePred (· ∈ L.completeTheory M) := fun φ =>
  haveI := decRealize hR (α := Empty) φ default default
  decidable_of_iff (BoundedFormula.Realize φ default default) Iff.rfl

/-- 5:B3, 25:C1 (Theorem witnessed, exit 2 — `Th(W_N)` does not interpret `Q`): a structure with an injective
successor that never reaches zero is infinite; every model of `Q` is such a structure, and a finite frame's
definable quotients are finite. -/
theorem infinite_of_succ {A : Type*} (S : A → A) (z : A) (hinj : Function.Injective S) (hz : ∀ x, S x ≠ z) :
    Infinite A := by
  by_contra hfin
  have : Finite A := not_infinite_iff_finite.mp hfin
  obtain ⟨x, hx⟩ := Finite.injective_iff_surjective.mp hinj z
  exact hz x hx

end frames

section diagonal

/-- 5:D3 (Remark cantor-diagonal): Cantor's theorem is an external diagonal — no map from a set onto its power
set, in every finite frame as `n < 2^n`. -/
theorem cantor (α : Type*) (f : α → Set α) : ¬ Function.Surjective f := Function.cantor_surjective f

/-- 5:D3: on the frame, `n < 2^n`. -/
theorem cantor_finite (n : ℕ) : n < 2 ^ n := Nat.lt_two_pow_self

end diagonal

section migration

/-- 5:C2, 25:E2 (Proposition mirror, the count): fewer than `s^(K+1)` strings of length at most `K` exist over an
alphabet of `s ≥ 2` letters. -/
theorem records_lt (s K : ℕ) (hs : 2 ≤ s) : ∑ i ∈ Finset.range (K + 1), s ^ i < s ^ (K + 1) :=
  Nat.geomSum_lt hs fun _ hk => Finset.mem_range.mp hk

/-- 5:C2 (Proposition mirror): a part with fewer distinguishable records than the frame has elements admits no
injective representation of the frame's domain. -/
theorem no_mirror {A R : Type*} [Fintype A] [Fintype R] (h : Fintype.card R < Fintype.card A) (f : A → R) :
    ¬ Function.Injective f := fun hf => absurd (Fintype.card_le_of_injective f hf) (not_le.mpr h)

end migration

/-! ## 25-godel's rows (moved from the paper module on 20 October 2026) -/

section godel
variable {L : Language} {M : Type*} [L.Structure M]

/-! ### 25:C1, 25:C2, 25:C5 — Gödel's hypotheses over a finite structure -/

section vacuity

/-- 25:C1, 25:C3 (Proposition noQ, the finite form) — on a finite carrier an injective map is onto: no successor is
injective and omits an element. -/
theorem finite_succ_onto {A : Type*} [Finite A] (S : A → A) (hinj : Function.Injective S) (z : A) : ∃ x, S x = z :=
  Finite.surjective_of_injective hinj z

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

/-- 25:H2, 25:H4 (Theorem finiteness, the finite direction) — over a structure of `m` elements a second-order
quantifier over `k`-ary relations ranges over the `2^(m^k)` subsets of `M^k`, a finite set. -/
theorem card_relations (M : Type*) [Fintype M] [DecidableEq M] (k : ℕ) :
    Fintype.card (Finset (Fin k → M)) = 2 ^ (Fintype.card M ^ k) := by
  rw [Fintype.card_finset, Fintype.card_pi_const]

end finiteness

end godel

/-! ## 5-reductio's rows (moved from the paper module on 21 October 2026) -/

section reductio

section choice

variable {U : Type*} [LinearOrder U]

/-- 5:E1 (Proposition finite-choice): on a finite universe with a canonical order, `ch(A) = min A` is a member of
every nonempty `A` — choice is a definable theorem, not a postulate. -/
theorem finite_choice (A : Finset U) (hA : A.Nonempty) : A.min' hA ∈ A := Finset.min'_mem A hA

/-- 5:E2 (Lemma periodic-equality): for an equality-periodic family `A (i + N) = A i` the choice `min A i` is
periodic with the same period. -/
theorem periodic_choice (A : ℤ → Finset U) (N : ℤ) (hN : ∀ i, A (i + N) = A i) (i : ℤ) :
    (A (i + N)).min = (A i).min := by rw [hN]

variable {G I A : Type*} [Group G] [MulAction G I] [MulAction G A]

/-- 5:E3 (Theorem equivariant-choice, one orbit): for a `G`-family `π : A → I` over a transitive `G`-set `I`, an
equivariant section exists iff the stabiliser of a base point `i₀` fixes some point of its fibre. -/
theorem equivariant_section_iff [MulAction.IsPretransitive G I] (π : A → I)
    (hπ : ∀ (g : G) (a : A), π (g • a) = g • π a) (i₀ : I) :
    (∃ s : I → A, (∀ i, π (s i) = i) ∧ ∀ (g : G) (i : I), s (g • i) = g • s i) ↔
      ∃ a, π a = i₀ ∧ ∀ g ∈ MulAction.stabilizer G i₀, g • a = a := by
  constructor
  · rintro ⟨s, hs, heq⟩
    refine ⟨s i₀, hs i₀, fun g hg => ?_⟩
    rw [← heq, MulAction.mem_stabilizer_iff.mp hg]
  · rintro ⟨a, ha, hfix⟩
    classical
    choose g hg using fun i => MulAction.exists_smul_eq G i₀ i
    -- `s i := g i • a`, where `g i • i₀ = i`; independence of the choice is the stabiliser condition
    have key : ∀ (h : G) (i : I), h • i₀ = i → h • a = g i • a := by
      intro h i hi
      have hst : (g i)⁻¹ * h ∈ MulAction.stabilizer G i₀ := by
        rw [MulAction.mem_stabilizer_iff, mul_smul, hi]
        have e := inv_smul_smul (g i) i₀
        rw [hg i] at e
        exact e
      have := hfix _ hst
      rw [mul_smul] at this
      calc h • a = g i • (g i)⁻¹ • h • a := (smul_inv_smul _ _).symm
        _ = g i • a := by rw [this]
    refine ⟨fun i => g i • a, fun i => ?_, fun h i => ?_⟩
    · rw [hπ, ha, hg]
    · show g (h • i) • a = h • (g i • a)
      rw [← mul_smul]
      exact (key (h * g i) (h • i) (by rw [mul_smul, hg])).symm

/-- 5:E4 (Example basis-obstruction): on the line over `𝔽₅` the involution `v ↦ −v` fixes no basis — `−v ≠ v`
for every `v ≠ 0` — while over `𝔽₂` it fixes `1`: the obstruction is arithmetic. -/
theorem obstruction_five : (∀ v : ZMod 5, v ≠ 0 → -v ≠ v) ∧ (-(1 : ZMod 2) = 1) := by decide

/-- 5:E8 (Banach–Tarski disappears): a finite nonempty set cannot be doubled — there is no injection
`X ⊕ X ↪ X`, so no decomposition reassembles two copies of `X` from pieces of `X`. -/
theorem no_doubling {X : Type*} [Fintype X] [Nonempty X] : IsEmpty (X ⊕ X ↪ X) := by
  constructor
  intro f
  have h := Fintype.card_le_of_embedding f
  rw [Fintype.card_sum] at h
  have : 0 < Fintype.card X := Fintype.card_pos
  omega

/-- 5:E8 (ultrafilters): on a finite set every ultrafilter is principal. -/
theorem ultrafilter_principal {X : Type*} [Finite X] (f : Ultrafilter X) : ∃ a, f = pure a :=
  Ultrafilter.eq_pure_of_finite f

end choice

section determinacy

/-- 5:D8 (Proposition finiteness, the finite direction): over a finite domain a second-order quantifier over all
subsets is a finite conjunction — decided by exhaustive evaluation. -/
def decideAllSubsets {M : Type*} [Fintype M] [DecidableEq M] (P : Finset M → Prop) [DecidablePred P] :
    Decidable (∀ S : Finset M, P S) := Fintype.decidableForallFintype

/-- 5:D8 (the infinite direction, its first step): an infinite domain carries a copy of `ℕ` — Dedekind's
embedding, from which the reduction of true second-order arithmetic proceeds. -/
theorem nat_embeds {M : Type*} [Infinite M] : Nonempty (ℕ ↪ M) := ⟨Infinite.natEmbedding M⟩

end determinacy

end reductio

end FRC.Logic
