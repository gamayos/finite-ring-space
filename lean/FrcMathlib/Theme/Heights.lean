import Mathlib

/-!
# FrcMathlib.Theme.Heights — a mode near every height (20-rh, 23 November 2026)

For distinct primes `ℓ_j` with `(∏ ℓ_j) ^ B < p`, an injective character `ψ` of the group of the nonzero residues of
`ZMod p` into `ℂˣ` (a chart of the cycle) and any complex numbers `u_j` of modulus one, some mode `k < p - 1` has
`(∑ ‖ψ(ℓ_j)^k - u_j‖²) * ((B+1)² + 1) ≤ 10 m` (`mode_near_height`, 20:D18). With `u_j = ℓ_j^{it}` every height `t` of
the chart of a mode is near a mode of the shell at these primes. The proof is the Parseval identity over the modes,
applied to a product of polynomials (`parseval_roots`, `parseval_prod`), with the polynomial `∑_{s<B} (s+1)(B-s) x^s`
(`sq_bound`, `sq_bound_roots`). An injective character exists on every shell (`chart_exists`), and the primes are
nonzero residues of the shell (`label_nonzero`). The chart theme's file for this theorem, on Mathlib alone. Its
evaluation on the laboratory Subjects is the python check D18 of `frc/ledgers/p20_rh.py`.
-/

open Finset BigOperators ComplexConjugate

namespace FRC.Chart.Heights

/-- The geometric sum of a nontrivial `n`-th root of unity vanishes. -/
lemma geom_root {q : ℂ} {n : ℕ} (hq : q ^ n = 1) (hq1 : q ≠ 1) : ∑ k ∈ range n, q ^ k = 0 := by
  have h := geom_sum_mul q n
  rw [hq, sub_self] at h
  exact (mul_eq_zero.mp h).resolve_right (sub_ne_zero.mpr hq1)

/-- Parseval for a combination of distinct `n`-th roots of unity, summed over the exponents. -/
theorem parseval_roots {α : Type*} [DecidableEq α] (R : Finset α) (n : ℕ) (hn : 0 < n)
    (Z C : α → ℂ) (hZ : ∀ r ∈ R, Z r ^ n = 1)
    (hinj : ∀ r ∈ R, ∀ r' ∈ R, Z r = Z r' → r = r') :
    ∑ k ∈ range n, ‖∑ r ∈ R, C r * Z r ^ k‖ ^ 2 = n * ∑ r ∈ R, ‖C r‖ ^ 2 := by
  have hnorm : ∀ r ∈ R, Z r * conj (Z r) = 1 := fun r hr => by
    rw [Complex.mul_conj', Complex.norm_eq_one_of_pow_eq_one (hZ r hr) hn.ne']; simp
  have hgeom : ∀ r ∈ R, ∀ r' ∈ R,
      ∑ k ∈ range n, (Z r * conj (Z r')) ^ k = if r = r' then (n : ℂ) else 0 := by
    intro r hr r' hr'
    split_ifs with h
    · subst h; rw [hnorm r hr]; simp
    · apply geom_root
      · rw [mul_pow, ← map_pow, hZ r hr, hZ r' hr']; simp
      · intro h1
        apply h
        apply hinj r hr r' hr'
        have h2 := congrArg (· * Z r') h1
        simp only [one_mul] at h2
        rw [mul_assoc, mul_comm (conj (Z r')), hnorm r' hr', mul_one] at h2
        exact h2
  apply Complex.ofReal_injective
  push_cast
  have key : ∀ k, ((‖∑ r ∈ R, C r * Z r ^ k‖ : ℂ)) ^ 2
      = ∑ r ∈ R, ∑ r' ∈ R, C r * conj (C r') * (Z r * conj (Z r')) ^ k := by
    intro k
    rw [← Complex.mul_conj', map_sum, Finset.sum_mul_sum]
    refine Finset.sum_congr rfl fun r _ => Finset.sum_congr rfl fun r' _ => ?_
    simp only [map_mul, map_pow, mul_pow]
    ring
  simp_rw [key]
  rw [Finset.sum_comm]
  have hrow : ∀ r ∈ R, ∑ k ∈ range n, ∑ r' ∈ R, C r * conj (C r') * (Z r * conj (Z r')) ^ k
      = n * (‖C r‖ : ℂ) ^ 2 := by
    intro r hr
    rw [Finset.sum_comm]
    have hcol : ∀ r' ∈ R, ∑ k ∈ range n, C r * conj (C r') * (Z r * conj (Z r')) ^ k
        = if r = r' then C r * conj (C r') * n else 0 := by
      intro r' hr'
      rw [← Finset.mul_sum, hgeom r hr r' hr']
      split_ifs <;> simp
    rw [Finset.sum_congr rfl hcol, Finset.sum_ite_eq R r, ite_eq_left hr, Complex.mul_conj']
    ring
  rw [Finset.sum_congr rfl hrow, ← Finset.mul_sum]

/-- Parseval for a product of polynomials in the numbers `z i ^ k * w i`, the `w i` of modulus one. -/
theorem parseval_prod {ι : Type*} [Fintype ι] [DecidableEq ι] (n : ℕ) (hn : 0 < n)
    (z w : ι → ℂ) (hz : ∀ i, z i ^ n = 1) (hw : ∀ i, ‖w i‖ = 1)
    (T : ι → Finset ℕ) (c : ι → ℕ → ℂ)
    (hind : ∀ r ∈ Fintype.piFinset T, ∀ r' ∈ Fintype.piFinset T,
      ∏ i, z i ^ r i = ∏ i, z i ^ r' i → r = r') :
    ∑ k ∈ range n, ∏ i, ‖∑ s ∈ T i, c i s * (z i ^ k * w i) ^ s‖ ^ 2
      = n * ∏ i, ∑ s ∈ T i, ‖c i s‖ ^ 2 := by
  have h1 : ∀ k, ∏ i, ‖∑ s ∈ T i, c i s * (z i ^ k * w i) ^ s‖ ^ 2
      = ‖∑ r ∈ Fintype.piFinset T, (∏ i, c i (r i) * w i ^ r i) * (∏ i, z i ^ r i) ^ k‖ ^ 2 := by
    intro k
    have h2 : ∏ i, ∑ s ∈ T i, c i s * (z i ^ k * w i) ^ s
        = ∑ r ∈ Fintype.piFinset T, (∏ i, c i (r i) * w i ^ r i) * (∏ i, z i ^ r i) ^ k := by
      rw [Finset.prod_univ_sum]
      refine Finset.sum_congr rfl fun r _ => ?_
      rw [← Finset.prod_pow, ← Finset.prod_mul_distrib]
      refine Finset.prod_congr rfl fun i _ => ?_
      have h3 : (z i ^ k) ^ r i = (z i ^ r i) ^ k := by rw [← pow_mul, ← pow_mul, mul_comm]
      rw [mul_pow, h3]
      ring
    rw [Finset.prod_pow, ← norm_prod, h2]
  rw [Finset.sum_congr rfl (fun k _ => h1 k)]
  have hroot : ∀ r ∈ Fintype.piFinset T, (∏ i, z i ^ r i) ^ n = 1 := by
    intro r _
    rw [← Finset.prod_pow]
    refine Finset.prod_eq_one fun i _ => ?_
    rw [← pow_mul, mul_comm, pow_mul, hz i, one_pow]
  have hP := parseval_roots (Fintype.piFinset T) n hn (fun r => ∏ i, z i ^ r i)
    (fun r => ∏ i, c i (r i) * w i ^ r i) hroot hind
  rw [hP]
  congr 1
  rw [Finset.prod_univ_sum]
  refine Finset.sum_congr rfl fun r _ => ?_
  rw [norm_prod, ← Finset.prod_pow]
  refine Finset.prod_congr rfl fun i _ => ?_
  rw [norm_mul, norm_pow, hw i, one_pow, mul_one]

/-- A product with one factor replaced. -/
lemma prod_ite_single {ι : Type*} [Fintype ι] [DecidableEq ι] {M : Type*} [CommMonoid M]
    (i0 : ι) (f g : ι → M) :
    ∏ i, (if i = i0 then g i else f i) = g i0 * ∏ i ∈ univ.erase i0, f i := by
  rw [← Finset.mul_prod_erase univ _ (mem_univ i0), ite_eq_left rfl]
  congr 1
  refine Finset.prod_congr rfl fun i hi => ?_
  rw [ite_eq_right (Finset.ne_of_mem_erase hi)]

/-- The bound on the sum of squared distances, for a polynomial `a` on `S` with `(1 - x)` times it equal to `a'` on
`S'`. -/
theorem sq_bound_aux {ι : Type*} [Fintype ι] [DecidableEq ι] (n : ℕ) (hn : 0 < n)
    (z u : ι → ℂ) (hz : ∀ i, z i ^ n = 1) (hu : ∀ i, ‖u i‖ = 1)
    (S S' : Finset ℕ) (a a' : ℕ → ℂ)
    (hker : ∀ x : ℂ, (1 - x) * ∑ s ∈ S, a s * x ^ s = ∑ s ∈ S', a' s * x ^ s)
    (hind : ∀ r r' : ι → ℕ, (∀ i, r i ∈ S ∪ S') → (∀ i, r' i ∈ S ∪ S') →
      ∏ i, z i ^ r i = ∏ i, z i ^ r' i → r = r')
    (A A' : ℝ) (hA : ∑ s ∈ S, ‖a s‖ ^ 2 = A) (hA' : ∑ s ∈ S', ‖a' s‖ ^ 2 = A') :
    ∃ k < n, (∑ i, ‖z i ^ k - u i‖ ^ 2) * A ≤ Fintype.card ι * A' := by
  have hA0 : 0 ≤ A := hA ▸ Finset.sum_nonneg fun s _ => sq_nonneg _
  have hA'0 : 0 ≤ A' := hA' ▸ Finset.sum_nonneg fun s _ => sq_nonneg _
  let w : ι → ℂ := fun i => conj (u i)
  have hw : ∀ i, ‖w i‖ = 1 := fun i => by simp [w, hu i]
  let F : ι → ℕ → ℂ := fun i k => ∑ s ∈ S, a s * (z i ^ k * w i) ^ s
  let Q : ℕ → ℝ := fun k => ∏ i, ‖F i k‖ ^ 2
  have hQ0 : ∀ k, 0 ≤ Q k := fun k => Finset.prod_nonneg fun i _ => sq_nonneg _
  have hdist : ∀ i k, ‖z i ^ k - u i‖ = ‖1 - z i ^ k * w i‖ := by
    intro i k
    have h1 : u i * conj (u i) = 1 := by rw [Complex.mul_conj', hu i]; simp
    have h2 : z i ^ k - u i = -(u i * (1 - z i ^ k * w i)) := by
      simp only [w]
      linear_combination (-(z i ^ k)) * h1
    rw [h2, norm_neg, norm_mul, hu i, one_mul]
  have hE1 : ∑ k ∈ range n, Q k = n * ∏ _i : ι, A := by
    have hP := parseval_prod n hn z w hz hw (fun _ => S) (fun _ => a) (by
      intro r hr r' hr' h
      rw [Fintype.mem_piFinset] at hr hr'
      exact hind r r' (fun i => Finset.mem_union_left _ (hr i))
        (fun i => Finset.mem_union_left _ (hr' i)) h)
    rw [hA] at hP
    exact hP
  have hE2 : ∀ i0, ∑ k ∈ range n, ‖1 - z i0 ^ k * w i0‖ ^ 2 * Q k
      = n * ∏ i, (if i = i0 then A' else A) := by
    intro i0
    have hP := parseval_prod n hn z w hz hw (fun i => if i = i0 then S' else S)
      (fun i => if i = i0 then a' else a) (by
        intro r hr r' hr' h
        rw [Fintype.mem_piFinset] at hr hr'
        refine hind r r' (fun i => ?_) (fun i => ?_) h
        · have h0 := hr i
          by_cases hi : i = i0
          · rw [ite_eq_left hi] at h0; exact Finset.mem_union_right _ h0
          · rw [ite_eq_right hi] at h0; exact Finset.mem_union_left _ h0
        · have h0 := hr' i
          by_cases hi : i = i0
          · rw [ite_eq_left hi] at h0; exact Finset.mem_union_right _ h0
          · rw [ite_eq_right hi] at h0; exact Finset.mem_union_left _ h0)
    have hR : (∏ i, ∑ s ∈ (if i = i0 then S' else S), ‖(if i = i0 then a' else a) s‖ ^ 2)
        = ∏ i, (if i = i0 then A' else A) := by
      refine Finset.prod_congr rfl fun i _ => ?_
      by_cases hi : i = i0
      · simp only [ite_eq_left hi]; exact hA'
      · simp only [ite_eq_right hi]; exact hA
    rw [← hR, ← hP]
    refine Finset.sum_congr rfl fun k _ => ?_
    have hL : ∀ i, ‖∑ s ∈ (if i = i0 then S' else S),
          (if i = i0 then a' else a) s * (z i ^ k * w i) ^ s‖ ^ 2
        = if i = i0 then ‖1 - z i ^ k * w i‖ ^ 2 * ‖F i k‖ ^ 2 else ‖F i k‖ ^ 2 := by
      intro i
      by_cases hi : i = i0
      · simp only [ite_eq_left hi]
        rw [← hker, norm_mul, mul_pow]
      · simp only [ite_eq_right hi]
        rfl
    rw [Finset.prod_congr rfl (fun i _ => hL i),
      prod_ite_single i0 (fun i => ‖F i k‖ ^ 2) (fun i => ‖1 - z i ^ k * w i‖ ^ 2 * ‖F i k‖ ^ 2),
      mul_assoc, Finset.mul_prod_erase univ (fun i => ‖F i k‖ ^ 2) (mem_univ i0)]
  have hE3 : ∀ i0 : ι, (∏ i, (if i = i0 then A' else A)) * A = A' * ∏ _i : ι, A := by
    intro i0
    rw [prod_ite_single i0 (fun _ => A) (fun _ => A'), mul_assoc, mul_comm _ A,
      Finset.mul_prod_erase univ (fun _ => A) (mem_univ i0)]
  by_contra hcon0
  have hcon : ∀ k, k < n → (Fintype.card ι : ℝ) * A' < (∑ i, ‖z i ^ k - u i‖ ^ 2) * A :=
    fun k hk => not_le.mp fun h => hcon0 ⟨k, hk, h⟩
  have hApos : 0 < A := by
    have h0 := hcon 0 hn
    have h00 : 0 ≤ (Fintype.card ι : ℝ) * A' := mul_nonneg (Nat.cast_nonneg _) hA'0
    have h1 : 0 < (∑ i, ‖z i ^ 0 - u i‖ ^ 2) * A := lt_of_le_of_lt h00 h0
    rcases hA0.lt_or_eq with h | h
    · exact h
    · rw [← h, mul_zero] at h1; exact absurd h1 (lt_irrefl _)
  have hPA : 0 < ∏ _i : ι, A := Finset.prod_pos (s := (univ : Finset ι)) fun _ _ => hApos
  have hsum : ∑ k ∈ range n, Q k * ((∑ i, ‖z i ^ k - u i‖ ^ 2) * A - Fintype.card ι * A') = 0 := by
    have h1 : ∑ k ∈ range n, Q k * (∑ i, ‖z i ^ k - u i‖ ^ 2)
        = ∑ i0 : ι, n * ∏ i, (if i = i0 then A' else A) := by
      have h11 : ∀ k ∈ range n, Q k * (∑ i, ‖z i ^ k - u i‖ ^ 2)
          = ∑ i0, ‖1 - z i0 ^ k * w i0‖ ^ 2 * Q k := by
        intro k _
        rw [Finset.mul_sum]
        refine Finset.sum_congr rfl fun i _ => ?_
        rw [hdist i k, mul_comm]
      rw [Finset.sum_congr rfl h11, Finset.sum_comm]
      exact Finset.sum_congr rfl fun i0 _ => hE2 i0
    have h2 : ∑ k ∈ range n, Q k * ((∑ i, ‖z i ^ k - u i‖ ^ 2) * A - Fintype.card ι * A')
        = (∑ k ∈ range n, Q k * (∑ i, ‖z i ^ k - u i‖ ^ 2)) * A
          - (∑ k ∈ range n, Q k) * (Fintype.card ι * A') := by
      rw [Finset.sum_mul, Finset.sum_mul, ← Finset.sum_sub_distrib]
      refine Finset.sum_congr rfl fun k _ => by ring
    rw [h2, h1, hE1, Finset.sum_mul]
    have h3 : ∀ i0 ∈ (univ : Finset ι), (n * ∏ i, (if i = i0 then A' else A)) * A
        = n * (A' * ∏ _i : ι, A) := by
      intro i0 _
      rw [mul_assoc, hE3 i0]
    rw [Finset.sum_congr rfl h3, Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
    ring
  have hterm : ∀ k ∈ range n,
      0 ≤ Q k * ((∑ i, ‖z i ^ k - u i‖ ^ 2) * A - Fintype.card ι * A') :=
    fun k hk => mul_nonneg (hQ0 k) (sub_nonneg.mpr (hcon k (Finset.mem_range.mp hk)).le)
  have hzero := (Finset.sum_eq_zero_iff_of_nonneg hterm).mp hsum
  have hQz : ∀ k ∈ range n, Q k = 0 := by
    intro k hk
    rcases mul_eq_zero.mp (hzero k hk) with h | h
    · exact h
    · have h5 := hcon k (Finset.mem_range.mp hk); linarith
  have hQs : ∑ k ∈ range n, Q k = 0 := Finset.sum_eq_zero hQz
  rw [hE1] at hQs
  have hn' : (0 : ℝ) < n := by exact_mod_cast hn
  have h6 := mul_pos hn' hPA
  linarith

/-- The bound on the sum of squared distances: for roots of unity `z i` whose monomials with exponents in `S ∪ S'`
are distinct and any complex numbers `u i` of modulus one, at some exponent `k < n` the sum of `‖z i ^ k - u i‖²`
times the squared norm of `a` is at most the number of the `z i` times the squared norm of `a'`. -/
theorem sq_bound {ι : Type*} [Fintype ι] [DecidableEq ι] (n : ℕ) (hn : 0 < n)
    (z u : ι → ℂ) (hz : ∀ i, z i ^ n = 1) (hu : ∀ i, ‖u i‖ = 1)
    (S S' : Finset ℕ) (a a' : ℕ → ℂ)
    (hker : ∀ x : ℂ, (1 - x) * ∑ s ∈ S, a s * x ^ s = ∑ s ∈ S', a' s * x ^ s)
    (hind : ∀ r r' : ι → ℕ, (∀ i, r i ∈ S ∪ S') → (∀ i, r' i ∈ S ∪ S') →
      ∏ i, z i ^ r i = ∏ i, z i ^ r' i → r = r') :
    ∃ k < n, (∑ i, ‖z i ^ k - u i‖ ^ 2) * ∑ s ∈ S, ‖a s‖ ^ 2
      ≤ Fintype.card ι * ∑ s ∈ S', ‖a' s‖ ^ 2 :=
  sq_bound_aux n hn z u hz hu S S' a a' hker hind _ _ rfl rfl

/-- The polynomial identity: `(1 - x) ∑_{s<N} (s+1)(c-s) x^s = ∑_{s<N} (c-2s) x^s - N(c-N+1) x^N`. -/
lemma poly_identity (c x : ℂ) (N : ℕ) :
    (1 - x) * ∑ s ∈ range N, ((s : ℂ) + 1) * (c - s) * x ^ s
      = ∑ s ∈ range N, (c - 2 * s) * x ^ s - N * (c - N + 1) * x ^ N := by
  induction N with
  | zero => simp
  | succ N ih =>
    rw [Finset.sum_range_succ, mul_add, ih, Finset.sum_range_succ]
    push_cast
    ring

/-- The sum of the squares of the coefficients `(s+1)(c-s)`. -/
lemma poly_sq (c : ℝ) (N : ℕ) :
    ∑ s ∈ range N, (((s : ℝ) + 1) * (c - s)) ^ 2
      = (c + 1) ^ 2 * (N * (N + 1) * (2 * N + 1) / 6) - 2 * (c + 1) * (N * (N + 1) / 2) ^ 2
        + N * (N + 1) * (2 * N + 1) * (3 * N ^ 2 + 3 * N - 1) / 30 := by
  induction N with
  | zero => simp
  | succ N ih => rw [Finset.sum_range_succ, ih]; push_cast; ring

/-- The sum of the squares of the coefficients `c - 2s`. -/
lemma diff_sq (c : ℝ) (N : ℕ) :
    ∑ s ∈ range N, (c - 2 * s) ^ 2
      = c ^ 2 * N - 2 * c * (N * (N - 1)) + 2 * (N * (N - 1) * (2 * N - 1)) / 3 := by
  induction N with
  | zero => simp
  | succ N ih => rw [Finset.sum_range_succ, ih]; push_cast; ring

lemma norm_sq_ofReal (r : ℝ) : ‖(r : ℂ)‖ ^ 2 = r ^ 2 := by
  rw [Complex.norm_real, Real.norm_eq_abs, sq_abs]

/-- The bound with the polynomial `∑_{s<B} (s+1)(B-s) x^s`: for roots of unity `z i` whose monomials of exponents up
to `B` are distinct and any complex numbers `u i` of modulus one, at some exponent `k < n` the sum of the squared
distances `‖z i ^ k - u i‖²` is at most `10 m / ((B + 1)² + 1)`. -/
theorem sq_bound_roots {ι : Type*} [Fintype ι] [DecidableEq ι] (n : ℕ) (hn : 0 < n)
    (z u : ι → ℂ) (hz : ∀ i, z i ^ n = 1) (hu : ∀ i, ‖u i‖ = 1) (B : ℕ) (hB : 0 < B)
    (hind : ∀ r r' : ι → ℕ, (∀ i, r i ≤ B) → (∀ i, r' i ≤ B) →
      ∏ i, z i ^ r i = ∏ i, z i ^ r' i → r = r') :
    ∃ k < n, (∑ i, ‖z i ^ k - u i‖ ^ 2) * ((B + 1 : ℝ) ^ 2 + 1) ≤ 10 * Fintype.card ι := by
  let a : ℕ → ℂ := fun s => ((((s : ℝ) + 1) * ((B : ℝ) - s) : ℝ) : ℂ)
  let a' : ℕ → ℂ := fun s => ((((B : ℝ) - 2 * s : ℝ)) : ℂ)
  have hker : ∀ x : ℂ, (1 - x) * ∑ s ∈ range B, a s * x ^ s
      = ∑ s ∈ range (B + 1), a' s * x ^ s := by
    intro x
    have h := poly_identity (B : ℂ) x B
    simp only [a, a']
    push_cast
    rw [h, Finset.sum_range_succ]
    ring
  have hle : ∀ (r : ι → ℕ), (∀ i, r i ∈ range B ∪ range (B + 1)) → ∀ i, r i ≤ B := by
    intro r hr i
    have h0 := hr i
    rw [Finset.mem_union, Finset.mem_range, Finset.mem_range] at h0
    omega
  obtain ⟨k, hk, hkl⟩ := sq_bound n hn z u hz hu (range B) (range (B + 1)) a a' hker
    (fun r r' hr hr' h => hind r r' (hle r hr) (hle r' hr') h)
  refine ⟨k, hk, ?_⟩
  have hA : ∑ s ∈ range B, ‖a s‖ ^ 2
      = (B : ℝ) * (B + 1) * (B + 2) * ((B + 1) ^ 2 + 1) / 30 := by
    rw [Finset.sum_congr rfl (fun s _ => norm_sq_ofReal _), poly_sq]; ring
  have hA' : ∑ s ∈ range (B + 1), ‖a' s‖ ^ 2 = (B : ℝ) * (B + 1) * (B + 2) / 3 := by
    rw [Finset.sum_congr rfl (fun s _ => norm_sq_ofReal _), diff_sq]; push_cast; ring
  rw [hA, hA'] at hkl
  have hB' : (0 : ℝ) < B := by exact_mod_cast hB
  have hpos : (0 : ℝ) < (B : ℝ) * (B + 1) * (B + 2) :=
    mul_pos (mul_pos hB' (by linarith)) (by linarith)
  by_contra hc
  have hc' : 0 < (∑ i, ‖z i ^ k - u i‖ ^ 2) * ((B + 1 : ℝ) ^ 2 + 1) - 10 * Fintype.card ι := by
    linarith [not_le.mp hc]
  have h1 := mul_pos hc' hpos
  have h2 : ((∑ i, ‖z i ^ k - u i‖ ^ 2) * ((B + 1 : ℝ) ^ 2 + 1) - 10 * Fintype.card ι)
      * ((B : ℝ) * (B + 1) * (B + 2))
      = 30 * ((∑ i, ‖z i ^ k - u i‖ ^ 2) * ((B : ℝ) * (B + 1) * (B + 2) * ((B + 1) ^ 2 + 1) / 30)
        - Fintype.card ι * ((B : ℝ) * (B + 1) * (B + 2) / 3)) := by ring
  rw [h2] at h1
  linarith

/-- Distinct primes: the exponents of a product of prime powers are determined. -/
lemma prime_exponents {ι : Type*} [Fintype ι] [DecidableEq ι] (ℓ : ι → ℕ)
    (hp : ∀ i, (ℓ i).Prime) (hinj : Function.Injective ℓ) (r r' : ι → ℕ)
    (h : ∏ i, ℓ i ^ r i = ∏ i, ℓ i ^ r' i) : r = r' := by
  funext j
  have key : ∀ e : ι → ℕ, (∏ i, ℓ i ^ e i).factorization (ℓ j) = e j := by
    intro e
    rw [Nat.factorization_prod (fun i _ => pow_ne_zero _ (hp i).ne_zero)]
    simp only [Nat.factorization_pow, Finsupp.coe_finsetSum, Finset.sum_apply,
      Finsupp.smul_apply, smul_eq_mul]
    rw [Finset.sum_eq_single j]
    · rw [(hp j).factorization, Finsupp.single_eq_same, mul_one]
    · intro i _ hij
      rw [(hp i).factorization, Finsupp.single_apply, ite_eq_right (fun h => hij (hinj h)), mul_zero]
    · intro h; exact absurd (mem_univ j) h
  rw [← key r, ← key r', h]

/-- 20:D18 — a mode near every height. On the shell `ZMod p`, for distinct primes `ℓ i` with `(∏ ℓ i) ^ B < p`, an
injective character `ψ` of the group of the nonzero residues into `ℂˣ` and any complex numbers `u i` of modulus one,
one mode `k < p - 1` has `(∑ ‖ψ(ℓ i) ^ k - u i‖²) * ((B + 1)² + 1) ≤ 10 m`. With `u i = (ℓ i)^{it}` it is the paper's
statement at the height `t`. -/
theorem mode_near_height {p : ℕ} [Fact p.Prime] {ι : Type*} [Fintype ι] [DecidableEq ι]
    (ψ : (ZMod p)ˣ →* ℂˣ) (hψ : Function.Injective ψ)
    (ℓ : ι → ℕ) (hℓ : ∀ i, (ℓ i).Prime) (hinj : Function.Injective ℓ)
    (x : ι → (ZMod p)ˣ) (hx : ∀ i, ((x i : (ZMod p)ˣ) : ZMod p) = (ℓ i : ZMod p))
    (B : ℕ) (hB : 0 < B) (hpow : (∏ i, ℓ i) ^ B < p)
    (u : ι → ℂ) (hu : ∀ i, ‖u i‖ = 1) :
    ∃ k < p - 1, (∑ i, ‖((ψ (x i) : ℂˣ) : ℂ) ^ k - u i‖ ^ 2) * ((B + 1 : ℝ) ^ 2 + 1)
      ≤ 10 * Fintype.card ι := by
  have hp1 : 0 < p - 1 := Nat.sub_pos_of_lt (Fact.out : p.Prime).one_lt
  refine sq_bound_roots (p - 1) hp1 (fun i => ((ψ (x i) : ℂˣ) : ℂ)) u ?_ hu B hB ?_
  · intro i
    rw [← Units.val_pow_eq_pow_val, ← map_pow, ZMod.units_pow_card_sub_one_eq_one, map_one,
      Units.val_one]
  · intro r r' hr hr' h
    have h1 : ∏ i, x i ^ r i = ∏ i, x i ^ r' i := by
      apply hψ
      apply Units.ext
      simp only [map_prod, map_pow, Units.coe_prod, Units.val_pow_eq_pow_val]
      exact h
    have h2 : ((∏ i, ℓ i ^ r i : ℕ) : ZMod p) = ((∏ i, ℓ i ^ r' i : ℕ) : ZMod p) := by
      have h0 := congrArg (fun y : (ZMod p)ˣ => (y : ZMod p)) h1
      simp only [Units.coe_prod, Units.val_pow_eq_pow_val, hx] at h0
      push_cast
      exact h0
    have hlt : ∀ e : ι → ℕ, (∀ i, e i ≤ B) → ∏ i, ℓ i ^ e i < p := by
      intro e he
      refine lt_of_le_of_lt ?_ hpow
      rw [← Finset.prod_pow]
      exact Finset.prod_le_prod (fun i _ => Nat.pow_le_pow_right (hℓ i).pos (he i))
    have h3 : ∏ i, ℓ i ^ r i = ∏ i, ℓ i ^ r' i := by
      have h0 := (ZMod.natCast_eq_natCast_iff' _ _ p).mp h2
      rwa [Nat.mod_eq_of_lt (hlt r hr), Nat.mod_eq_of_lt (hlt r' hr')] at h0
    exact prime_exponents ℓ hℓ hinj r r' h3

/-- A chart of the cycle exists: an injective character of the group of the nonzero residues into `ℂˣ`. -/
theorem chart_exists (p : ℕ) [Fact p.Prime] :
    ∃ ψ : (ZMod p)ˣ →* ℂˣ, Function.Injective ψ := by
  have : NeZero (p - 1) := ⟨(Nat.sub_pos_of_lt (Fact.out : p.Prime).one_lt).ne'⟩
  have hcard : Nat.card (ZMod p)ˣ = Nat.card (rootsOfUnity (p - 1) ℂ) := by
    rw [Nat.card_eq_fintype_card, ZMod.card_units, Complex.card_rootsOfUnity]
  let e := mulEquivOfCyclicCardEq hcard
  exact ⟨(rootsOfUnity (p - 1) ℂ).subtype.comp e.toMonoidHom,
    (Subgroup.subtype_injective _).comp e.injective⟩

/-- Under the condition `(∏ ℓ i) ^ B < p` every prime `ℓ i` is a nonzero residue of the shell. -/
theorem label_nonzero {p : ℕ} [Fact p.Prime] {ι : Type*} [Fintype ι] [DecidableEq ι]
    (ℓ : ι → ℕ) (hℓ : ∀ i, (ℓ i).Prime) (B : ℕ) (hB : 0 < B) (hpow : (∏ i, ℓ i) ^ B < p)
    (i : ι) : ∃ x : (ZMod p)ˣ, (x : ZMod p) = (ℓ i : ZMod p) := by
  have hpos : 0 < ∏ j, ℓ j := Finset.prod_pos fun j _ => (hℓ j).pos
  have h1 : ℓ i ≤ ∏ j, ℓ j := Nat.le_of_dvd hpos (Finset.dvd_prod_of_mem ℓ (mem_univ i))
  have h2 : ∏ j, ℓ j ≤ (∏ j, ℓ j) ^ B := Nat.le_self_pow hB.ne' _
  have hlt : ℓ i < p := lt_of_le_of_lt (le_trans h1 h2) hpow
  have hne : (ℓ i : ZMod p) ≠ 0 := by
    rw [Ne, ZMod.natCast_eq_zero_iff]
    exact Nat.not_dvd_of_pos_of_lt (hℓ i).pos hlt
  exact ⟨Units.mk0 _ hne, rfl⟩

end FRC.Chart.Heights
