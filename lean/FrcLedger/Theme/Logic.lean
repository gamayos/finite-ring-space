import Mathlib

/-!
# FrcLedger.Theme.Logic — truth in a finite structure and the finite counting (the logic theme, task LM17)

The complete theory of a structure is complete; on a finite structure with decidable equality truth is decided by
evaluation (`decRealize`, `decTheory`); an injective successor missing a point forces an infinite carrier; Cantor's
theorem and its finite form; fewer than `s^(K+1)` records of length `≤ K`, and no injection into fewer states.
Moved from 5-reductio's module, which keeps every old name as an alias. Classical, on Mathlib's hierarchy.
-/

open FirstOrder FirstOrder.Language

namespace FRC.Logic

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

end migration

end FRC.Logic
