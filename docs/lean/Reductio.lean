import Mathlib

/-!
# 5-red — paradoxes of infinity as reductio: the ledger predicates in Lean (2026-09-17)

Rows of the predicate ledger of *Paradoxes of Infinity as Reductio ad Absurdum* (tree `5-reductio-20260706`).
The finite exit's properties for any finite structure in any language (the complete theory is complete, and
truth is decided by evaluation); the infinitude of every structure with an injective successor missing zero
(no finite frame interprets `Q`); Cantor's theorem; the counting of the migration propositions and the vanishing
certified fraction; definable and periodic choice; the equivariant section criterion on an orbit; the
obstruction on `𝔽₅`; the finite disappearance of the choice paradoxes; Dedekind's embedding.  Classical (tier 2)
on Mathlib's hierarchy; the finite content is proved with no axioms in `FrcCore/Reductio.lean`.
-/

open FirstOrder FirstOrder.Language

namespace FRC.Reductio

section frames

variable {L : Language} {M : Type*} [L.Structure M]

/-- 5:B5, 5:B3 (Proposition frame-complete, completeness): the theory of any structure — a finite frame `W_N` among
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

/-- 5:B5 (Proposition frame-complete, decidability): membership in the theory of a finite structure is decided
by evaluating the sentence. -/
@[instance_reducible] def decTheory [Fintype M] [DecidableEq M]
    (hR : ∀ (n : ℕ) (R : L.Relations n) (x : Fin n → M), Decidable (Structure.RelMap R x)) :
    DecidablePred (· ∈ L.completeTheory M) := fun φ =>
  haveI := decRealize hR (α := Empty) φ default default
  decidable_of_iff (BoundedFormula.Realize φ default default) Iff.rfl

/-- 5:B3 (Theorem witnessed, exit 2 — `Th(W_N)` does not interpret `Q`): a structure with an injective
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

/-- 5:C2 (Proposition mirror, the count): fewer than `s^(K+1)` strings of length at most `K` exist over an
alphabet of `s ≥ 2` letters. -/
theorem records_lt (s K : ℕ) (hs : 2 ≤ s) : ∑ i ∈ Finset.range (K + 1), s ^ i < s ^ (K + 1) :=
  Nat.geomSum_lt hs fun _ hk => Finset.mem_range.mp hk

/-- 5:C2 (Proposition mirror): a part with fewer distinguishable records than the frame has elements admits no
injective representation of the frame's domain. -/
theorem no_mirror {A R : Type*} [Fintype A] [Fintype R] (h : Fintype.card R < Fintype.card A) (f : A → R) :
    ¬ Function.Injective f := fun hf => absurd (Fintype.card_le_of_injective f hf) (not_le.mpr h)

open Filter Topology in
/-- 5:C3 (Proposition fraction): the certified fraction `s^(K+1) / ⌊c^L/2⌋` of a bounded agent tends to zero as
the cohort length `L` grows, for any capacity and any `c > 1`. -/
theorem certified_fraction_tendsto (A c : ℝ) (hc : 1 < c) :
    Tendsto (fun L : ℕ => A / c ^ L) atTop (𝓝 0) :=
  tendsto_const_nhds.div_atTop (tendsto_pow_atTop_atTop_of_one_lt hc)

end migration

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

-- Ledger predicates of 5-reductio (generated by make_predicates.py from docs/5-reductio/5-reductio-ledger.json; edit the ledger, not this section)
/-- 5:B3 (p05007) — Witnessed independence: every three-element subset is satisfiable --- $Q$ itself ($\neg$Cmp, consistent by finitary means, the superexponential cost exact); $\mathrm{Th}(W_N)$ ($\neg$IR: consistent, complete, decidable, singly axiomatised, interpreting no $Q$ since every model of $Q$ is infinite); the inconsistent extension ($\neg$Cns); true arithmetic ($\neg$Eff). Four legs, all load-bearing. -/
theorem p05007 : (∀ {A : Type u_1} (S : A → A) (z : A), Function.Injective S → (∀ (x : A), S x ≠ z) → Infinite A) ∧ ∀ {L : FirstOrder.Language} {M : Type u_4} [L.Structure M] [Nonempty M], (L.completeTheory M).IsComplete :=
  And.intro @FRC.Reductio.infinite_of_succ (@FRC.Reductio.theory_complete)
/-- 5:B5 (p05009) — Per-frame completeness: $\mathrm{Th}(W_N)$ is consistent, complete and decidable, axiomatised by the categorical sentence $\sigma_N$; truth in any finite structure is decided by evaluation, and the theory of any structure is complete. Cited definitions (not proofs): FRC.Reductio.decRealize, FRC.Reductio.decTheory. -/
theorem p05009 : ∀ {L : FirstOrder.Language} {M : Type u_3} [L.Structure M] [Nonempty M], (L.completeTheory M).IsComplete :=
  @FRC.Reductio.theory_complete
/-- 5:C2 (p05013) — No internal mirror: fewer than $s^{K+1}$ records exist, so an agent with $s^{K+1}<N$ holds no injective representation of the domain of $W_N$ --- a proper part cannot mirror the whole (pigeonhole). -/
theorem p05013 : (∀ (s K : ℕ), (2 : ℕ) ≤ s → ∑ i ∈ Finset.range (K + (1 : ℕ)), s ^ i < s ^ (K + (1 : ℕ))) ∧ ∀ {A : Type u_1} {R : Type u_2} [Fintype A] [Fintype R], Fintype.card R < Fintype.card A → ∀ (f : A → R), ¬Function.Injective f :=
  And.intro @FRC.Reductio.records_lt (@FRC.Reductio.no_mirror)
/-- 5:C3 (p05014) — Vanishing certified fraction: at least $c^{L}$ normal-form sentences of length $\le L$, half of each cohort frame truths by completeness, fewer than $s^{K+1}$ certified, so the certified fraction is at most $s^{K+1}/\lfloor c^{L}/2\rfloor\to0$. -/
theorem p05014 : ∀ (A c : ℝ), (1 : ℝ) < c → Filter.Tendsto (fun L => A / c ^ L) Filter.atTop (nhds (0 : ℝ)) :=
  @FRC.Reductio.certified_fraction_tendsto
/-- 5:D3 (p05019) — Diagonal normal form: $\{$Eff, Cns, Cmp, IR$\}$ inconsistent (B2), Tarski a variant with the truth predicate for Cmp; the diagonal is a theorem when external --- Cantor's theorem, $n<2^{n}$ on every frame, uncountability, halting --- and a paradox engine only over an internalised registry with completeness demanded. -/
theorem p05019 : (∀ (α : Type u_1) (f : α → Set α), ¬Function.Surjective f) ∧ ∀ (n : ℕ), n < (2 : ℕ) ^ n :=
  And.intro @FRC.Reductio.cantor (@FRC.Reductio.cantor_finite)
/-- 5:D8 (p05024) — Finiteness of determinate totalities: in ZF with every infinite set Dedekind-infinite, a structure satisfies Det iff it is finite --- finite: the full higher-order theory decided by exhaustive evaluation; infinite: a copy of $\N$ inside gives an effective reduction of true second-order arithmetic, which is not arithmetical. The real field's first-order tameness is silence about its subsets. Cited definitions (not proofs): FRC.Reductio.decideAllSubsets. -/
theorem p05024 : ∀ {M : Type u_1} [Infinite M], Nonempty (ℕ ↪ M) :=
  @FRC.Reductio.nat_embeds
/-- 5:E1 (p05027) — Global choice on a finite universe: with a canonical order, $\operatorname{ch}(A)=\min A$ is a uniform pointwise choice rule; over a fixed finite base AC is a definable theorem; finite products are nonempty without it. -/
theorem p05027 : ∀ {U : Type u_1} [LinearOrder U] (A : Finset U) (hA : A.Nonempty), A.min' hA ∈ A :=
  @FRC.Reductio.finite_choice
/-- 5:E2 (p05028) — Periodic choice: an equality-periodic family $A_{i+N}=A_i$ has the choice $f(i)=\operatorname{ch}(A_i)$ of the same period; group-periodic families as equivariant surjections $\pi:A\to I$ with equivariant sections. -/
theorem p05028 : ∀ {U : Type u_1} [LinearOrder U] (A : ℤ → Finset U) (N : ℤ), (∀ (i : ℤ), A (i + N) = A i) → ∀ (i : ℤ), (A (i + N)).min = (A i).min :=
  @FRC.Reductio.periodic_choice
set_option linter.defProp false in
/-- 5:E3 (p05029) — Equivariant periodic choice: a $G$-equivariant section exists iff each stabiliser action $G_i\curvearrowright A_i$ has a fixed point (one orbit at a time); the Fraenkel--Mostowski mechanism in positive form. -/
def p05029 := @FRC.Reductio.equivariant_section_iff
/-- 5:E4 (p05030) — The definable basis: every subspace of a finite vector space has the greedy $\min$-basis, one definable function on all subspaces; the equivariant obstruction --- $\Z/2$ acting by $v\mapsto-v$ on the line over $\F_5$ fixes no basis ($-v\neq v$), over $\F_2$ it does: arithmetic, not formal. -/
theorem p05030 : (∀ (v : ZMod (5 : ℕ)), v ≠ (0 : ZMod (5 : ℕ)) → -v ≠ v) ∧ (-1 : ZMod (2 : ℕ)) = (1 : ZMod (2 : ℕ)) :=
  @FRC.Reductio.obstruction_five
/-- 5:E8 (p05034) — The choice paradoxes vanish: on a finite set counting measure is complete and invariant, no decomposition doubles the set ($X\sqcup X$ does not inject into $X$), and every ultrafilter is principal; periodic variants inherit this on one period. -/
theorem p05034 : (∀ {X : Type u_1} [Fintype X] [Nonempty X], IsEmpty (X ⊕ X ↪ X)) ∧ ∀ {X : Type u_2} [Finite X] (f : Ultrafilter X), ∃ a, f = pure a :=
  And.intro @FRC.Reductio.no_doubling (@FRC.Reductio.ultrafilter_principal)
-- end ledger predicates

end FRC.Reductio
