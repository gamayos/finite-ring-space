import Mathlib

/-!
# 4-rep — universal latent representation: the ledger predicates in Lean (2026-09-17)

Rows of the predicate ledger of *Universal Latent Representation in Finite Ring Continuum* (Entropy 2026, 28, 40;
tree `4-deepfrc-20251217`).  The representation rows (B4–C4) are set theory and hold for arbitrary types; the
finiteness of the latent domain enters through the embedding into the shell (B6) only.  The hypersphere row (E1)
is stated for a symmetry acting transitively on the domain and by linear isometries on the space; the Gödel row
(E3) by unique factorisation.  Classical (tier 2) on Mathlib's hierarchy; the same rows are proved with no axioms in
`FrcCore/Representation.lean`.
-/

namespace FRC.Representation

section maps

variable {Z X W W₁ W₂ U : Type*}

/-- 4:B3 (Definition 2): `E : X → W` is adequate for the observation map `g : Z → X` when `E ∘ g` is a bijection
`Z → W`; minimality (`W = φ(Z)`) is contained in the bijection. -/
abbrev Adequate (g : Z → X) (E : X → W) : Prop := Function.Bijective (E ∘ g)

/-- 4:B4: adequacy makes the observation map injective on the latent domain. -/
theorem adequate_inj {g : Z → X} {E : X → W} (h : Adequate g E) : Function.Injective g := h.1.of_comp

/-- 4:B5 (Lemma 2): two adequate representations of one observation map are related by the bijection
`ψ = φ₂ ∘ φ₁⁻¹ : W₁ ≃ W₂` on the resolved observations, `E₂ ∘ g = ψ ∘ E₁ ∘ g`. -/
theorem transition_exists {g : Z → X} {E₁ : X → W₁} {E₂ : X → W₂} (h₁ : Adequate g E₁) (h₂ : Adequate g E₂) :
    ∃ ψ : W₁ ≃ W₂, ∀ z, E₂ (g z) = ψ (E₁ (g z)) := by
  refine ⟨(Equiv.ofBijective _ h₁).symm.trans (Equiv.ofBijective _ h₂), fun z => ?_⟩
  show E₂ (g z) = Equiv.ofBijective (E₂ ∘ g) h₂ ((Equiv.ofBijective (E₁ ∘ g) h₁).symm ((E₁ ∘ g) z))
  rw [Equiv.ofBijective_symm_apply_apply (E₁ ∘ g) h₁ z]
  rfl

/-- 4:B5 (the uniqueness clause): a map with that property is determined by it, since `E₁ ∘ g` is onto `W₁`. -/
theorem transition_unique {g : Z → X} {E₁ : X → W₁} {E₂ : X → W₂} (h₁ : Adequate g E₁) (ψ ψ' : W₁ → W₂)
    (h : ∀ z, E₂ (g z) = ψ (E₁ (g z))) (h' : ∀ z, E₂ (g z) = ψ' (E₁ (g z))) : ψ = ψ' := by
  funext w
  obtain ⟨z, rfl⟩ := h₁.2 w
  exact (h z).symm.trans (h' z)

/-- 4:B6: a representation space of the cardinality of the latent domain embeds injectively in the shell — the
one place where finiteness enters. -/
theorem embeds_in_shell [Fintype W] [Fintype U] (h : Fintype.card W ≤ Fintype.card U) : Nonempty (W ↪ U) :=
  Function.Embedding.nonempty_of_card_le h

/-- 4:B6, 4:C2 (Theorem 1 (iii), the canonical choice): with `incl : Z → U` the inclusion of the latent domain and
`φ = E ∘ g`, the embedding `ι := incl ∘ φ⁻¹` is injective and `ι ∘ φ = incl` — the chart `ψ_m` is the inclusion. -/
theorem canonical_iota {incl : Z → U} (hincl : Function.Injective incl) {g : Z → X} {E : X → W}
    (h : Adequate g E) :
    Function.Injective (incl ∘ (Equiv.ofBijective _ h).symm) ∧
      ∀ z, (incl ∘ (Equiv.ofBijective _ h).symm) (E (g z)) = incl z := by
  refine ⟨hincl.comp (Equiv.ofBijective _ h).symm.injective, fun z => ?_⟩
  show incl ((Equiv.ofBijective (E ∘ g) h).symm ((E ∘ g) z)) = incl z
  rw [Equiv.ofBijective_symm_apply_apply (E ∘ g) h z]

/-- 4:C1 (Theorem 1 (i)): the chart `ψ_m = ι_m ∘ φ_m` is injective for every injective `ι_m`. -/
theorem chart_injective {ι : W → U} (hι : Function.Injective ι) {g : Z → X} {E : X → W} (h : Adequate g E) :
    Function.Injective (ι ∘ (E ∘ g)) := hι.comp h.1

/-- 4:C1 (Theorem 1 (ii)): the transition `Ψ_{m→n} = ψ_n ∘ ψ_m⁻¹` is a bijection between the images, carrying
`ψ_m z` to `ψ_n z`. -/
theorem transition_images {ψm ψn : Z → U} (hm : Function.Injective ψm) (hn : Function.Injective ψn) :
    ∃ Ψ : Set.range ψm ≃ Set.range ψn, ∀ z, (Ψ ⟨ψm z, z, rfl⟩ : U) = ψn z := by
  refine ⟨(Equiv.ofInjective ψm hm).symm.trans (Equiv.ofInjective ψn hn), fun z => ?_⟩
  show ((Equiv.ofInjective ψn hn) ((Equiv.ofInjective ψm hm).symm ⟨ψm z, z, rfl⟩) : U) = ψn z
  rw [show (⟨ψm z, z, rfl⟩ : Set.range ψm) = Equiv.ofInjective ψm hm z from rfl, Equiv.symm_apply_apply]
  rfl

/-- 4:C3 (Corollary 1): the lift `L = φ⁻¹ ∘ E : X → Z` recovers the latent state, `L ∘ g = id`, and `L x` is the
unique `z` with `E x = φ z`. -/
theorem lift {g : Z → X} {E : X → W} (h : Adequate g E) :
    (∀ z, (Equiv.ofBijective _ h).symm (E (g z)) = z) ∧
      ∀ x z, E x = (E ∘ g) z ↔ (Equiv.ofBijective _ h).symm (E x) = z := by
  refine ⟨fun z => Equiv.ofBijective_symm_apply_apply _ h z, fun x z => ⟨fun hx => ?_, fun hz => ?_⟩⟩
  · rw [hx]; exact Equiv.ofBijective_symm_apply_apply _ h z
  · rw [← hz]
    exact (Equiv.apply_symm_apply (Equiv.ofBijective (E ∘ g) h) (E x)).symm

/-- 4:C4 (Corollary 2): the lifts of two modalities' observations of one latent state agree, so the canonical
charts `ψ ∘ L_m ∘ g_m` and `ψ ∘ L_n ∘ g_n` both equal `ψ`. -/
theorem consistency {Xm Xn Wm Wn : Type*} {gm : Z → Xm} {gn : Z → Xn} {Em : Xm → Wm} {En : Xn → Wn}
    (hm : Adequate gm Em) (hn : Adequate gn En) (z : Z) :
    (Equiv.ofBijective _ hm).symm (Em (gm z)) = (Equiv.ofBijective _ hn).symm (En (gn z)) := by
  rw [(lift hm).1 z, (lift hn).1 z]

end maps

section sphere

variable {Z : Type*} {G : Type*} [Group G] [MulAction G Z] [MulAction.IsPretransitive G Z]
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- 4:E1 (the hypersphere): a Euclidean chart `emb : Z → E` equivariant for a symmetry that acts transitively on
the domain and by linear isometries on the space has constant norm — its image lies on one sphere about the origin. -/
theorem sphere_of_equivariant (ρ : G → E ≃ₗᵢ[ℝ] E) (emb : Z → E)
    (hequiv : ∀ (σ : G) (z : Z), emb (σ • z) = ρ σ (emb z)) (z₀ z : Z) : ‖emb z‖ = ‖emb z₀‖ := by
  obtain ⟨σ, hσ⟩ := MulAction.exists_smul_eq G z₀ z
  rw [← hσ, hequiv, LinearIsometryEquiv.norm_map]

end sphere

section godel

/-- 4:E3 (Gödel encoding): over distinct primes `p₁, …, p_d` the code `x ↦ ∏ pᵢ^{xᵢ}` is injective on
`ℕ^d` — unique factorisation. -/
theorem godel_injective {d : ℕ} (p : Fin d → ℕ) (hp : ∀ i, (p i).Prime) (hinj : Function.Injective p) :
    Function.Injective (fun x : Fin d → ℕ => ∏ i, p i ^ x i) := by
  intro x y hxy
  have key : ∀ (x : Fin d → ℕ) (j : Fin d), (∏ i, p i ^ x i).factorization (p j) = x j := by
    intro x j
    rw [Nat.factorization_prod (fun i _ => pow_ne_zero _ (hp i).ne_zero), Finsupp.finsetSum_apply,
      Finset.sum_eq_single j]
    · rw [Nat.factorization_pow, Finsupp.smul_apply, (hp j).factorization, Finsupp.single_eq_same, smul_eq_mul,
        mul_one]
    · intro i _ hij
      rw [Nat.factorization_pow, Finsupp.smul_apply, (hp i).factorization, Finsupp.single_apply,
        ite_eq_right (fun h => hij (hinj h)), smul_eq_mul, mul_zero]
    · intro h; exact absurd (Finset.mem_univ j) h
  funext j
  have := congrArg (fun n => n.factorization (p j)) hxy
  simpa only [key] using this

/-- 4:E3 (the reduction into one field): an injective integer code with values below `q` stays injective
modulo `q`. -/
theorem mod_injective {α : Type*} (f : α → ℕ) (hf : Function.Injective f) (q : ℕ) (hq : ∀ a, f a < q) :
    Function.Injective (fun a => f a % q) := by
  intro a b h
  apply hf
  simpa only [Nat.mod_eq_of_lt (hq a), Nat.mod_eq_of_lt (hq b)] using h

/-- 4:E3 (the instance of the package): with `d = 3`, exponents `≤ 4` and the primes `2, 3, 5`, the code is at most
`2⁴3⁴5⁴ = 810 000`, and `q = 810 013` is the least prime above it. -/
theorem godel_instance : 2 ^ 4 * 3 ^ 4 * 5 ^ 4 = 810000 ∧ Nat.Prime 810013 := ⟨by norm_num, by norm_num⟩

end godel

end FRC.Representation
