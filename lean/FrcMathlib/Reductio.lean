import Mathlib
import FrcMathlib.Theme.Logic
import FrcMathlib.Keys.Logic

/-!
# 5-red — paradoxes of infinity as reductio: the ledger predicates in Lean (2026-09-17)

Rows of the predicate ledger of *Paradoxes of Infinity as Reductio ad Absurdum* (tree `5-reductio-20260706`).
The finite exit's properties for any finite structure in any language (the complete theory is complete, and
truth is decided by evaluation); the infinitude of every structure with an injective successor missing zero
(no finite frame interprets `Q`); Cantor's theorem; the counting of the migration propositions and the vanishing
certified fraction; definable and periodic choice; the equivariant section criterion on an orbit; the
obstruction on `𝔽₅`; the finite disappearance of the choice paradoxes; Dedekind's embedding.  Classical (tier 2)
on Mathlib's hierarchy; every ledger theorem lives in `FrcMathlib/Theme/Logic.lean` (the logic theme) since 21 October
2026, this module keeping the names as aliases and the limit over the reals (5:C3's continuum reading, outside the ledger);
the finite content is proved with no axioms in the core's logic theme.
-/

open FirstOrder FirstOrder.Language

namespace FRC.Reductio

/-! ## Old names (ledger migration, task LM17; the worked instances since 21 October 2026): the declarations moved to the themes, each under its old name -/

section
open FRC.Logic

/-! ### 5:D8, 5:E1–5:E4, 5:E8 — in the theme since 21 October 2026; the names kept. 5:C3's limit over the reals stays here -/

section migration

open Filter Topology in
/-- 5:C3 (Proposition fraction), the continuum reading, outside the ledger since 21 October 2026 (the row's Lean witness is the
core's finite form `FRC.Reach.certified_fraction_vanishes`; an exact theme admits no statement over the reals): the certified
fraction `s^(K+1) / ⌊c^L/2⌋` of a bounded agent tends to zero as the cohort length `L` grows, for any capacity and any `c > 1`. -/
theorem certified_fraction_tendsto (A c : ℝ) (hc : 1 < c) :
    Tendsto (fun L : ℕ => A / c ^ L) atTop (𝓝 0) :=
  tendsto_const_nhds.div_atTop (tendsto_pow_atTop_atTop_of_one_lt hc)

end migration

section choice

variable {U : Type*} [LinearOrder U]

/-- 5:E1 (Proposition finite-choice): on a finite universe with a canonical order, `ch(A) = min A` is a member of
every nonempty `A` — choice is a definable theorem, not a postulate. -/
theorem finite_choice (A : Finset U) (hA : A.Nonempty) : A.min' hA ∈ A := FRC.Logic.finite_choice A hA

/-- 5:E2 (Lemma periodic-equality): for an equality-periodic family `A (i + N) = A i` the choice `min A i` is
periodic with the same period. -/
theorem periodic_choice (A : ℤ → Finset U) (N : ℤ) (hN : ∀ i, A (i + N) = A i) (i : ℤ) :
    (A (i + N)).min = (A i).min :=
  FRC.Logic.periodic_choice A N hN i

variable {G I A : Type*} [Group G] [MulAction G I] [MulAction G A]

/-- 5:E3 (Theorem equivariant-choice, one orbit): for a `G`-family `π : A → I` over a transitive `G`-set `I`, an
equivariant section exists iff the stabiliser of a base point `i₀` fixes some point of its fibre. -/
theorem equivariant_section_iff [MulAction.IsPretransitive G I] (π : A → I)
    (hπ : ∀ (g : G) (a : A), π (g • a) = g • π a) (i₀ : I) :
    (∃ s : I → A, (∀ i, π (s i) = i) ∧ ∀ (g : G) (i : I), s (g • i) = g • s i) ↔
      ∃ a, π a = i₀ ∧ ∀ g ∈ MulAction.stabilizer G i₀, g • a = a :=
  FRC.Logic.equivariant_section_iff π hπ i₀

/-- 5:E4 (Example basis-obstruction): on the line over `𝔽₅` the involution `v ↦ −v` fixes no basis — `−v ≠ v`
for every `v ≠ 0` — while over `𝔽₂` it fixes `1`: the obstruction is arithmetic. -/
theorem obstruction_five : (∀ v : ZMod 5, v ≠ 0 → -v ≠ v) ∧ (-(1 : ZMod 2) = 1) := FRC.Logic.obstruction_five

/-- 5:E8 (Banach–Tarski disappears): a finite nonempty set cannot be doubled — there is no injection
`X ⊕ X ↪ X`, so no decomposition reassembles two copies of `X` from pieces of `X`. -/
theorem no_doubling {X : Type*} [Fintype X] [Nonempty X] : IsEmpty (X ⊕ X ↪ X) := FRC.Logic.no_doubling

/-- 5:E8 (ultrafilters): on a finite set every ultrafilter is principal. -/
theorem ultrafilter_principal {X : Type*} [Finite X] (f : Ultrafilter X) : ∃ a, f = pure a :=
  FRC.Logic.ultrafilter_principal f

end choice

section determinacy

/-- 5:D8 (Proposition finiteness, the finite direction): over a finite domain a second-order quantifier over all
subsets is a finite conjunction — decided by exhaustive evaluation. -/
@[reducible] def decideAllSubsets {M : Type*} [Fintype M] [DecidableEq M] (P : Finset M → Prop) [DecidablePred P] :
    Decidable (∀ S : Finset M, P S) := FRC.Logic.decideAllSubsets P

/-- 5:D8 (the infinite direction, its first step): an infinite domain carries a copy of `ℕ` — Dedekind's
embedding, from which the reduction of true second-order arithmetic proceeds. -/
theorem nat_embeds {M : Type*} [Infinite M] : Nonempty (ℕ ↪ M) := FRC.Logic.nat_embeds

end determinacy

end


section frames_aliases
variable {L : Language} {M : Type*} [L.Structure M]

/-- 5:B5, 5:B3 (Proposition frame-complete, completeness): the theory of any structure — a finite frame `W_N` among
them — is complete: every sentence or its negation is in it. -/
theorem theory_complete [Nonempty M] : (L.completeTheory M).IsComplete :=
  FRC.Logic.theory_complete

/-- 5:B5 (decidability): in a finite structure with decidable relations, the truth of every bounded formula is
decided by evaluation — the quantifiers range over the finitely many elements. -/
@[reducible] def decRealize {α : Type*} [Fintype M] [DecidableEq M]
    (hR : ∀ (n : ℕ) (R : L.Relations n) (x : Fin n → M), Decidable (Structure.RelMap R x)) :
    ∀ {n : ℕ} (φ : L.BoundedFormula α n) (v : α → M) (xs : Fin n → M), Decidable (φ.Realize v xs) :=
  FRC.Logic.decRealize hR

/-- 5:B5 (Proposition frame-complete, decidability): membership in the theory of a finite structure is decided
by evaluating the sentence. -/
@[reducible] def decTheory [Fintype M] [DecidableEq M]
    (hR : ∀ (n : ℕ) (R : L.Relations n) (x : Fin n → M), Decidable (Structure.RelMap R x)) :
    DecidablePred (· ∈ L.completeTheory M) :=
  FRC.Logic.decTheory hR

/-- 5:B3 (Theorem witnessed, exit 2 — `Th(W_N)` does not interpret `Q`): a structure with an injective
successor that never reaches zero is infinite; every model of `Q` is such a structure, and a finite frame's
definable quotients are finite. -/
theorem infinite_of_succ {A : Type*} (S : A → A) (z : A) (hinj : Function.Injective S) (hz : ∀ x, S x ≠ z) :
    Infinite A :=
  FRC.Logic.infinite_of_succ S z hinj hz

end frames_aliases

/-- 5:D3 (Remark cantor-diagonal): Cantor's theorem is an external diagonal — no map from a set onto its power
set, in every finite frame as `n < 2^n`. -/
theorem cantor (α : Type*) (f : α → Set α) : ¬ Function.Surjective f :=
  FRC.Logic.cantor α f

/-- 5:D3: on the frame, `n < 2^n`. -/
theorem cantor_finite (n : ℕ) : n < 2 ^ n :=
  FRC.Logic.cantor_finite n

/-- 5:C2 (Proposition mirror, the count): fewer than `s^(K+1)` strings of length at most `K` exist over an
alphabet of `s ≥ 2` letters. -/
theorem records_lt (s K : ℕ) (hs : 2 ≤ s) : ∑ i ∈ Finset.range (K + 1), s ^ i < s ^ (K + 1) :=
  FRC.Logic.records_lt s K hs

/-- 5:C2 (Proposition mirror): a part with fewer distinguishable records than the frame has elements admits no
injective representation of the frame's domain. -/
theorem no_mirror {A R : Type*} [Fintype A] [Fintype R] (h : Fintype.card R < Fintype.card A) (f : A → R) :
    ¬ Function.Injective f :=
  FRC.Logic.no_mirror h f


-- Ledger predicates of 5-reductio (generated by make_predicates.py from docs/5-reductio/5-reductio-ledger.json; edit the ledger, not this section)
/-- 5:B3 (p05007) — Witnessed independence: every three-element subset is satisfiable --- $Q$ itself ($\neg$Cmp, consistent by finitary means, the superexponential cost exact); $\mathrm{Th}(W_N)$ ($\neg$IR: consistent, complete, decidable, singly axiomatised, interpreting no $Q$ since every model of $Q$ is infinite); the inconsistent extension ($\neg$Cns); true arithmetic ($\neg$Eff). Four legs, all load-bearing. -/
theorem p05007 : (∀ {A : Type u_1} (S : A → A) (z : A), Function.Injective S → (∀ (x : A), S x ≠ z) → Infinite A) ∧ ∀ {L : FirstOrder.Language} {M : Type u_2} [L.Structure M] [Nonempty M], (L.completeTheory M).IsComplete :=
  @FRC.LedgerML.p05007
/-- 5:B5 (p05009) — Per-frame completeness: $\mathrm{Th}(W_N)$ is consistent, complete and decidable, axiomatised by the categorical sentence $\sigma_N$; truth in any finite structure is decided by evaluation, and the theory of any structure is complete. Cited definitions (not proofs): FRC.Reductio.decRealize, FRC.Reductio.decTheory. -/
theorem p05009 : ∀ {L : FirstOrder.Language} {M : Type u_1} [L.Structure M] [Nonempty M], (L.completeTheory M).IsComplete :=
  @FRC.LedgerML.p05009
/-- 5:C2 (p05013) — No internal mirror: fewer than $s^{K+1}$ records exist, so an agent with $s^{K+1}<N$ holds no injective representation of the domain of $W_N$ --- a proper part cannot mirror the whole (pigeonhole). -/
theorem p05013 : (∀ (s K : ℕ), (2 : ℕ) ≤ s → ∑ i ∈ Finset.range (K + (1 : ℕ)), s ^ i < s ^ (K + (1 : ℕ))) ∧ ∀ {A : Type u_1} {R : Type u_2} [Fintype A] [Fintype R], Fintype.card R < Fintype.card A → ∀ (f : A → R), ¬Function.Injective f :=
  @FRC.LedgerML.p05013
/-- 5:D3 (p05019) — Diagonal normal form: $\{$Eff, Cns, Cmp, IR$\}$ inconsistent (B2), Tarski a variant with the truth predicate for Cmp; the diagonal is a theorem when external --- Cantor's theorem, $n<2^{n}$ on every frame, uncountability, halting --- and a paradox engine only over an internalised registry with completeness demanded. -/
theorem p05019 : (∀ (α : Type u_1) (f : α → Set α), ¬Function.Surjective f) ∧ ∀ (n : ℕ), n < (2 : ℕ) ^ n :=
  @FRC.LedgerML.p05019
/-- 5:D8 (p05024) — Finiteness of determinate totalities: in ZF with every infinite set Dedekind-infinite, a structure satisfies Det iff it is finite --- finite: the full higher-order theory decided by exhaustive evaluation; infinite: a copy of $\N$ inside gives an effective reduction of true second-order arithmetic, which is not arithmetical. The real field's first-order tameness is silence about its subsets. Cited definitions (not proofs): FRC.Reductio.decideAllSubsets. -/
theorem p05024 : ∀ {M : Type u_1} [Infinite M], Nonempty (ℕ ↪ M) :=
  @FRC.LedgerML.p05024
/-- 5:E1 (p05027) — Global choice on a finite universe: with a canonical order, $\operatorname{ch}(A)=\min A$ is a uniform pointwise choice rule; over a fixed finite base AC is a definable theorem; finite products are nonempty without it. -/
theorem p05027 : ∀ {U : Type u_1} [LinearOrder U] (A : Finset U) (hA : A.Nonempty), A.min' hA ∈ A :=
  @FRC.LedgerML.p05027
/-- 5:E2 (p05028) — Periodic choice: an equality-periodic family $A_{i+N}=A_i$ has the choice $f(i)=\operatorname{ch}(A_i)$ of the same period; group-periodic families as equivariant surjections $\pi:A\to I$ with equivariant sections. -/
theorem p05028 : ∀ {U : Type u_1} [LinearOrder U] (A : ℤ → Finset U) (N : ℤ), (∀ (i : ℤ), A (i + N) = A i) → ∀ (i : ℤ), (A (i + N)).min = (A i).min :=
  @FRC.LedgerML.p05028
set_option linter.defProp false in
/-- 5:E3 (p05029) — Equivariant periodic choice: a $G$-equivariant section exists iff each stabiliser action $G_i\curvearrowright A_i$ has a fixed point (one orbit at a time); the Fraenkel--Mostowski mechanism in positive form. -/
def p05029 := @FRC.LedgerML.p05029
/-- 5:E4 (p05030) — The definable basis: every subspace of a finite vector space has the greedy $\min$-basis, one definable function on all subspaces; the equivariant obstruction --- $\Z/2$ acting by $v\mapsto-v$ on the line over $\F_5$ fixes no basis ($-v\neq v$), over $\F_2$ it does: arithmetic, not formal. -/
theorem p05030 : (∀ (v : ZMod (5 : ℕ)), v ≠ (0 : ZMod (5 : ℕ)) → -v ≠ v) ∧ (-1 : ZMod (2 : ℕ)) = (1 : ZMod (2 : ℕ)) :=
  @FRC.LedgerML.p05030
/-- 5:E8 (p05034) — The choice paradoxes vanish: on a finite set counting measure is complete and invariant, no decomposition doubles the set ($X\sqcup X$ does not inject into $X$), and every ultrafilter is principal; periodic variants inherit this on one period. -/
theorem p05034 : (∀ {X : Type u_1} [Fintype X] [Nonempty X], IsEmpty (X ⊕ X ↪ X)) ∧ ∀ {X : Type u_2} [Finite X] (f : Ultrafilter X), ∃ a, f = pure a :=
  @FRC.LedgerML.p05034
-- end ledger predicates

end FRC.Reductio
