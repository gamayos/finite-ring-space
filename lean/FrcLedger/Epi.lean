import Mathlib

/-!
# 13-epi — the classical constants on the shell: the ledger predicates in Lean (2026-09-18)

Rows of the predicate ledger of *Finite Field Realisation of the Classical Constants π and e* (tree
`13-epi-20260713`).  The wall of `e`: Wilson reflection, the wall identity `!(p−1) ≡ !p`, the terminal residue
`−(!p)⁻¹`, antiperiodicity `!(n+p) ≡ −!n`, the series duals, the fixed-shell tower exact at every grade
(F1–F4, F7); the wall hierarchy of `π`: the legibility window, the half-wall terminus `−2`, the quarter-wall
two-squares invariant given Gauss's congruence, Lucas on the tower `C(2p^r, p^r) ≡ 2`, the first revival `8`,
the tower of `π` exact (G1–G3, G5, G9); the Cayley quarter-turn map and its composition law (C3); the Wallis
pair: strict monotonicity, the width identity and the enclosure `v_n < π < w_n` (E2, with Mathlib's Wallis
product); the impossibility of exact calibration of `e` from the irrationality of `π` (H3); the index condition
of the null experiment (H5); the wall of `π` at second order: the π-Wieferich condition of G4 in its three
forms with the exact identity `q_p(4) = 2q_p(2) + p·q_p(2)²`, Eisenstein's congruence `2q_p(2) ≡ −H_{(p−1)/2}`,
the identification with OEIS A355959 (G10), and G4's second-order clause from Morley's congruence; the Machin chain:
the alternating bound and pairing of the arctangent series, the error `17/((2N+3)5^{2N+3})`, the binary64 readout at
`N = 10`, the hundred digits at `N = 71`, the rational bracket of `π` at `m = 12` read by the core (E3, E4), the Gregory
brackets and the rounding chain (E5).  Classical (tier 2) on Mathlib's hierarchy; the finite content — the derangement
recurrence, antiperiodicity, the tower, orientation transport, the wrap-free window and the value rows on
`𝔽₁₃` and the six wall shells — is proved with no axioms in `FrcCore/Epi.lean`.

The ring arithmetic of the wall is proved once over an arbitrary field `K` with `p = 0`, `(p−1)! = −1` and
`k! ≠ 0` (`k ≤ p−1`); the sections `prime` and `primepi` instantiate `K := ZMod p`.
-/

namespace FRC.Epi

open Finset Nat
/-! ## The Wallis pair (13:E1, E2) -/
section wallis

variable {K : Type*} [Field K]

/-- 13:E1 — the Wallis pair on the framed rationals: `v n = 2·16^n/((2n+1)·C(2n,n)²)` (the doubled Wallis
partial product) and `w n = 16^n/(n·C(2n,n)²)` (the joint-return tally). -/
noncomputable def wallisV (n : ℕ) : K := 2 * (16 : K) ^ n / ((2 * (n : K) + 1) * ((centralBinom n : ℕ) : K) ^ 2)

/-- The Wallis chain on a field: `w n = 16^n / (n · C(2n,n)²)`. -/
noncomputable def wallisW (n : ℕ) : K := (16 : K) ^ n / ((n : K) * ((centralBinom n : ℕ) : K) ^ 2)

end wallis

section rencontres
open Equiv

variable {α : Type*} [Fintype α] [DecidableEq α]

/-- The fixed-point set of a permutation, as a finset. -/
def fixSet (σ : Perm α) : Finset α := univ.filter (fun a => σ a = a)

/-- The permutations fixing `F` pointwise number `(card α − |F|)!`: they are the permutations of the complement. -/
theorem card_fixing (F : Finset α) :
    (univ.filter (fun σ : Perm α => ∀ a ∈ F, σ a = a)).card = (Fintype.card α - F.card).factorial := by
  have e : {f : Perm α // ∀ a, ¬ (a ∉ F) → f a = a} ≃ Perm {a // a ∉ F} :=
    (Perm.subtypeEquivSubtypePerm (fun a => a ∉ F)).symm
  rw [← Fintype.card_subtype]
  have h : Fintype.card {σ : Perm α // ∀ a ∈ F, σ a = a} = Fintype.card {f : Perm α // ∀ a, ¬ (a ∉ F) → f a = a} := by
    apply Fintype.card_congr
    exact Equiv.subtypeEquivRight (fun σ => by simp)
  rw [h, Fintype.card_congr e, Fintype.card_perm, Fintype.card_subtype_compl, Fintype.card_coe]

/-- `x^|Fix σ| = Σ_{F ⊆ Fix σ} (x − 1)^|F|`: the binomial expansion of `((x − 1) + 1)^|Fix σ|`. -/
theorem pow_card_fixSet {R : Type*} [CommRing R] (x : R) (σ : Perm α) :
    x ^ (fixSet σ).card = ∑ F ∈ (fixSet σ).powerset, (x - 1) ^ F.card := by
  have := sum_pow_mul_eq_add_pow (x - 1) 1 (fixSet σ)
  simp only [one_pow, mul_one, sub_add_cancel] at this
  exact this.symm

/-- 13:C2 — the rencontres identity (the derangement selector, Prop. selector-e): `Σ_{σ ∈ S_n} x^{fix σ} = Σ_{k ≤ n} C(n,k)(n−k)! (x − 1)^k`, `n = card α`, over any
commutative ring, by double counting the pairs `(σ, F)` with `F` a set of fixed points of `σ`. -/
theorem rencontres {R : Type*} [CommRing R] (x : R) :
    ∑ σ : Perm α, x ^ (fixSet σ).card
      = ∑ k ∈ range (Fintype.card α + 1),
          (((Fintype.card α).choose k * (Fintype.card α - k).factorial : ℕ) : R) * (x - 1) ^ k := by
  simp_rw [pow_card_fixSet]
  rw [sum_comm' (t' := (univ : Finset α).powerset)
      (s' := fun F => univ.filter (fun σ : Perm α => ∀ a ∈ F, σ a = a))]
  · simp_rw [sum_const, nsmul_eq_mul, card_fixing]
    rw [sum_powerset_apply_card (fun m => ((Fintype.card α - m).factorial : R) * (x - 1) ^ m)]
    rw [Finset.card_univ]
    refine sum_congr rfl fun k _ => ?_
    rw [nsmul_eq_mul, Nat.cast_mul]; ring
  · intro σ F
    simp only [mem_univ, true_and, mem_powerset, mem_filter, fixSet, subset_iff]
    exact ⟨fun h => ⟨h, fun _ _ => trivial⟩, fun h => h.1⟩

/-- 13:C2 — the ledger's form of the rencontres identity, `P_n(x) = n! Σ_{k ≤ n} (x−1)^k/k!`: the coefficient `C(n,k)(n−k)!` is `n!/k!`. -/
theorem rencontres_rat (x : ℚ) :
    ∑ σ : Perm α, x ^ (fixSet σ).card
      = (Fintype.card α).factorial * ∑ k ∈ range (Fintype.card α + 1), (x - 1) ^ k / k.factorial := by
  rw [rencontres, mul_sum]
  refine sum_congr rfl fun k hk => ?_
  have hk' : k ≤ Fintype.card α := Nat.lt_succ_iff.mp (mem_range.mp hk)
  have h := Nat.choose_mul_factorial_mul_factorial hk'
  have hkf : (k.factorial : ℚ) ≠ 0 := by positivity
  have h' : ((Fintype.card α).factorial : ℚ) = (((Fintype.card α).choose k * (Fintype.card α - k).factorial : ℕ) : ℚ) * k.factorial := by
    rw [← Nat.cast_mul, ← h]; push_cast; ring
  rw [h']; field_simp

/-- 13:C2 — `P_n(1) = n!`: the normalised kernel `Z_n = P_n/n!` takes the value one at `x = 1`. -/
theorem rencontres_one : ∑ σ : Perm α, (1 : ℚ) ^ (fixSet σ).card = (Fintype.card α).factorial := by
  simp [Fintype.card_perm]

/-- 13:C2 — `P_n(0) = !n`: the value at `x = 0` is the number of derangements, so `Z_n(0) = !n/n!` and the unit registration ratio `Z_n(1)/Z_n(0)` is `n!/!n`. -/
theorem rencontres_zero : ∑ σ : Perm α, (0 : ℚ) ^ (fixSet σ).card = numDerangements (Fintype.card α) := by
  rw [← card_derangements_eq_numDerangements α]
  have : ∀ σ : Perm α, (0 : ℚ) ^ (fixSet σ).card = if σ ∈ derangements α then 1 else 0 := by
    intro σ
    by_cases h : σ ∈ derangements α
    · have : fixSet σ = ∅ := by
        rw [fixSet, filter_eq_empty_iff]; intro a _; exact h a
      simp [this, h]
    · have : (fixSet σ).card ≠ 0 := by
        rw [Ne, Finset.card_eq_zero, fixSet, filter_eq_empty_iff]
        intro hall; exact h (fun a => hall (mem_univ a))
      simp [h, zero_pow this]
  simp_rw [this]
  rw [sum_boole, Fintype.card_subtype]

end rencontres

section tailAndReadout
open Filter Topology

/-- The partial sums `expNegOneSum m = Σ_{i<m} (−1)^i/i!` of the alternating series of `e⁻¹`. -/
noncomputable def expNegOneSum (m : ℕ) : ℝ := ∑ i ∈ range m, (-1 : ℝ) ^ i * (1 / (i.factorial : ℝ))

theorem expNegOneSum_succ (m : ℕ) : expNegOneSum (m + 1) = expNegOneSum m + (-1 : ℝ) ^ m * (1 / (m.factorial : ℝ)) := by
  simp [expNegOneSum, sum_range_succ]

/-- The alternating series sums to `e⁻¹`. -/
theorem hasSum_expNegOneSum : HasSum (fun i : ℕ => (-1 : ℝ) ^ i * (1 / (i.factorial : ℝ))) (Real.exp (-1)) := by
  have h := NormedSpace.expSeries_div_hasSum_exp (-1 : ℝ)
  rw [← Real.exp_eq_exp_ℝ] at h
  convert h using 1
  ext i; ring

theorem tendsto_expNegOneSum : Tendsto expNegOneSum atTop (𝓝 (Real.exp (-1))) := hasSum_expNegOneSum.tendsto_sum_nat

theorem antitone_inv_factorial : Antitone (fun i : ℕ => (1 / (i.factorial : ℝ))) := by
  intro i j hij
  have : (i.factorial : ℝ) ≤ j.factorial := by exact_mod_cast Nat.factorial_le hij
  exact one_div_le_one_div_of_le (by positivity) this

theorem expNegOneSum_even_le (k : ℕ) : expNegOneSum (2 * k) ≤ Real.exp (-1) :=
  Antitone.alternating_series_le_tendsto tendsto_expNegOneSum antitone_inv_factorial k

theorem le_expNegOneSum_odd (k : ℕ) : Real.exp (-1) ≤ expNegOneSum (2 * k + 1) :=
  Antitone.tendsto_le_alternating_series tendsto_expNegOneSum antitone_inv_factorial k

/-- `!n = n! · expNegOneSum(n+1)`: the inclusion–exclusion sum of the derangement number. -/
theorem numDerangements_eq_sum (n : ℕ) : (numDerangements n : ℝ) = n.factorial * expNegOneSum (n + 1) := by
  have h := numDerangements_sum n
  have h' : (numDerangements n : ℝ) = ∑ k ∈ range (n + 1), (-1 : ℝ) ^ k * ((k + 1).ascFactorial (n - k) : ℝ) := by
    exact_mod_cast h
  rw [h', expNegOneSum, mul_sum]
  refine sum_congr rfl fun k hk => ?_
  have hk' : k ≤ n := Nat.lt_succ_iff.mp (mem_range.mp hk)
  have hf : (k.factorial : ℝ) * ((k + 1).ascFactorial (n - k) : ℝ) = n.factorial := by
    rw [← Nat.cast_mul, Nat.factorial_mul_ascFactorial, Nat.add_sub_cancel' hk']
  have hkf : (k.factorial : ℝ) ≠ 0 := by positivity
  field_simp
  linear_combination hf

/-- `δ_n = (−1)^n (!n − n!/e)`, the signed tail. -/
noncomputable def tailDelta (n : ℕ) : ℝ := (-1 : ℝ) ^ n * (numDerangements n - n.factorial * Real.exp (-1))

/-- `δ_n = (−1)^{n+1} n! (e⁻¹ − expNegOneSum(n+1))`. -/
theorem tailDelta_eq (n : ℕ) : tailDelta n = (-1 : ℝ) ^ (n + 1) * n.factorial * (Real.exp (-1) - expNegOneSum (n + 1)) := by
  rw [tailDelta, numDerangements_eq_sum, pow_succ]; ring

/-- 13:D2 — the closed tail bounds `1/(n+2) ≤ δ_n ≤ 1/(n+1)`, from the alternating series of `e⁻¹`. -/
theorem tailDelta_bounds (n : ℕ) : 1 / ((n : ℝ) + 2) ≤ tailDelta n ∧ tailDelta n ≤ 1 / ((n : ℝ) + 1) := by
  rw [tailDelta_eq]
  have hf : (0 : ℝ) < n.factorial := by positivity
  have h1 : ((n + 1).factorial : ℝ) = (n + 1) * n.factorial := by push_cast [Nat.factorial_succ]; ring
  have h2 : ((n + 2).factorial : ℝ) = (n + 2) * (n + 1) * n.factorial := by
    rw [show n + 2 = (n + 1) + 1 from rfl, Nat.factorial_succ, Nat.factorial_succ]; push_cast; ring
  rcases Nat.even_or_odd n with ⟨k, hk⟩ | ⟨k, hk⟩
  · -- n = 2k even: n + 1 = 2k + 1 odd; e⁻¹ ≤ expNegOneSum(n+1), expNegOneSum(n+2) ≤ e⁻¹, e⁻¹ ≤ expNegOneSum(n+3)
    have hA := le_expNegOneSum_odd k            -- e⁻¹ ≤ expNegOneSum (2k+1)
    have hB := expNegOneSum_even_le (k + 1)     -- expNegOneSum (2k+2) ≤ e⁻¹
    have hC := le_expNegOneSum_odd (k + 1)      -- e⁻¹ ≤ expNegOneSum (2k+3)
    have e1 : 2 * k + 1 = n + 1 := by omega
    have e2 : 2 * (k + 1) = n + 2 := by omega
    have e3 : 2 * (k + 1) + 1 = n + 3 := by omega
    rw [e1] at hA; rw [e2] at hB; rw [e3] at hC
    rw [show n + 2 = (n + 1) + 1 from rfl, expNegOneSum_succ] at hB
    rw [show n + 3 = (n + 1) + 1 + 1 from rfl, expNegOneSum_succ, expNegOneSum_succ] at hC
    have hs : (-1 : ℝ) ^ (n + 1) = -1 := by rw [hk]; simp [pow_succ, pow_mul]
    have hs2 : (-1 : ℝ) ^ (n + 1 + 1) = 1 := by rw [hk]; simp [pow_succ, pow_mul]
    rw [hs] at hB hC ⊢
    rw [hs2] at hC
    rw [h1] at hB hC; rw [h2] at hC
    constructor
    · rw [div_le_iff₀ (by positivity)]
      have : Real.exp (-1) - expNegOneSum (n + 1) ≤ -(1 / ((n + 1) * n.factorial)) + 1 / ((n + 2) * (n + 1) * n.factorial) := by linarith
      calc (1 : ℝ) = (n.factorial * (1 / ((n + 1) * n.factorial) - 1 / ((n + 2) * (n + 1) * n.factorial))) * (n + 2) := by
              field_simp; ring
        _ ≤ _ := by nlinarith [this]
    · rw [le_div_iff₀ (by positivity)]
      have : -(1 / ((n + 1) * (n.factorial : ℝ))) ≤ Real.exp (-1) - expNegOneSum (n + 1) := by linarith
      calc (-1 * (n.factorial : ℝ) * (Real.exp (-1) - expNegOneSum (n + 1))) * (n + 1) ≤ (n.factorial * (1 / ((n + 1) * n.factorial))) * (n + 1) := by nlinarith [this]
        _ = 1 := by field_simp
  · -- n = 2k + 1 odd: n + 1 = 2k + 2 even; expNegOneSum(n+1) ≤ e⁻¹ ≤ expNegOneSum(n+2); expNegOneSum(n+3) ≤ e⁻¹
    have hA := expNegOneSum_even_le (k + 1)     -- expNegOneSum (2k+2) ≤ e⁻¹
    have hB := le_expNegOneSum_odd (k + 1)      -- e⁻¹ ≤ expNegOneSum (2k+3)
    have hC := expNegOneSum_even_le (k + 2)     -- expNegOneSum (2k+4) ≤ e⁻¹
    have e1 : 2 * (k + 1) = n + 1 := by omega
    have e2 : 2 * (k + 1) + 1 = n + 2 := by omega
    have e3 : 2 * (k + 2) = n + 3 := by omega
    rw [e1] at hA; rw [e2] at hB; rw [e3] at hC
    rw [show n + 2 = (n + 1) + 1 from rfl, expNegOneSum_succ] at hB
    rw [show n + 3 = (n + 1) + 1 + 1 from rfl, expNegOneSum_succ, expNegOneSum_succ] at hC
    have hs : (-1 : ℝ) ^ (n + 1) = 1 := by rw [hk]; simp [pow_succ, pow_mul]
    have hs2 : (-1 : ℝ) ^ (n + 1 + 1) = -1 := by rw [hk]; simp [pow_succ, pow_mul]
    rw [hs] at hB hC ⊢
    rw [hs2] at hC
    rw [h1] at hB hC; rw [h2] at hC
    constructor
    · rw [div_le_iff₀ (by positivity)]
      have : 1 / ((n + 1) * (n.factorial : ℝ)) - 1 / ((n + 2) * (n + 1) * n.factorial) ≤ Real.exp (-1) - expNegOneSum (n + 1) := by linarith
      calc (1 : ℝ) = (n.factorial * (1 / ((n + 1) * n.factorial) - 1 / ((n + 2) * (n + 1) * n.factorial))) * (n + 2) := by
              field_simp; ring
        _ ≤ _ := by nlinarith [this]
    · rw [le_div_iff₀ (by positivity)]
      have : Real.exp (-1) - expNegOneSum (n + 1) ≤ 1 / ((n + 1) * (n.factorial : ℝ)) := by linarith
      calc (1 * (n.factorial : ℝ) * (Real.exp (-1) - expNegOneSum (n + 1))) * (n + 1) ≤ (n.factorial * (1 / ((n + 1) * n.factorial))) * (n + 1) := by nlinarith [this]
        _ = 1 := by field_simp

/-- The recursion `δ_n = (1 − δ_{n+1})/(n+1)`. -/
theorem tailDelta_succ (n : ℕ) : tailDelta n = (1 - tailDelta (n + 1)) / ((n : ℝ) + 1) := by
  rw [tailDelta_eq, tailDelta_eq, expNegOneSum_succ (n + 1)]
  have h1 : ((n + 1).factorial : ℝ) = (n + 1) * n.factorial := by push_cast [Nat.factorial_succ]; ring
  rw [h1]
  have hf : (0 : ℝ) < n.factorial := by positivity
  have hs1 : (-1 : ℝ) ^ (n + 1) = -((-1 : ℝ) ^ n) := by rw [pow_succ]; ring
  have hs2 : (-1 : ℝ) ^ (n + 1 + 1) = (-1 : ℝ) ^ n := by rw [pow_succ, pow_succ]; ring
  have hsq : ((-1 : ℝ) ^ n) ^ 2 = 1 := by rw [← pow_mul, mul_comm, pow_mul]; norm_num
  rw [hs1, hs2]
  field_simp
  linear_combination (1 : ℝ) * hsq

/-- 13:D2 — the tail form: `!n = n!/e + (−1)^n δ_n` with `δ_n ∈ (1/(n+2), 1/(n+1))` strictly, so `!n` is the nearest integer to `n!/e`. -/
theorem tailDelta_strict (n : ℕ) : 1 / ((n : ℝ) + 2) < tailDelta n ∧ tailDelta n < 1 / ((n : ℝ) + 1) := by
  have hb := tailDelta_bounds (n + 1)
  have hb2 := tailDelta_bounds (n + 2)
  have hpos : 0 < tailDelta (n + 2) := lt_of_lt_of_le (by positivity) hb2.1
  have hlt : tailDelta (n + 1) < 1 / ((n : ℝ) + 2) := by
    rw [tailDelta_succ (n + 1)]
    push_cast
    rw [div_lt_div_iff₀ (by positivity) (by positivity)]
    nlinarith [hpos]
  have hpos1 : 0 < tailDelta (n + 1) := lt_of_lt_of_le (by positivity) hb.1
  have hlt' : tailDelta (n + 1) * ((n : ℝ) + 2) < 1 := (lt_div_iff₀ (by positivity)).mp hlt
  rw [tailDelta_succ n]
  constructor
  · rw [div_lt_div_iff₀ (by positivity) (by positivity)]
    nlinarith [hlt']
  · rw [div_lt_div_iff₀ (by positivity) (by positivity)]
    nlinarith [hpos1]

/-! ### 13:D3 — the superexponential enclosure -/

/-- The derangement chain `ε_n = n!/!n`. -/
noncomputable def epsChain (n : ℕ) : ℝ := n.factorial / numDerangements n

theorem exp_neg_one_eq : Real.exp (-1) = (Real.exp 1)⁻¹ := by rw [Real.exp_neg]

/-- 13:D2 — `!n = n!·e⁻¹ + (−1)^n δ_n`, the tail form itself. -/
theorem numDerangements_eq_tailDelta (n : ℕ) :
    (numDerangements n : ℝ) = n.factorial * Real.exp (-1) + (-1 : ℝ) ^ n * tailDelta n := by
  have hsq : ((-1 : ℝ) ^ n) ^ 2 = 1 := by rw [← pow_mul, mul_comm, pow_mul]; norm_num
  rw [tailDelta]; linear_combination (-(numDerangements n : ℝ) + n.factorial * Real.exp (-1)) * hsq

theorem tailDelta_pos (n : ℕ) : 0 < tailDelta n := lt_of_lt_of_le (by positivity) (tailDelta_bounds n).1

/-- `!n > 0` for `n ≥ 2`. -/
theorem numDerangements_pos_real (n : ℕ) (hn : 2 ≤ n) : (0 : ℝ) < numDerangements n := by
  rw [numDerangements_eq_tailDelta]
  have hE : (2 : ℝ) < Real.exp 1 := Real.exp_one_gt_two
  have hE' : Real.exp 1 < 2.7182818286 := Real.exp_one_lt_d9
  have hinv : (1 : ℝ) / 2.7182818286 < Real.exp (-1) := by
    rw [exp_neg_one_eq, ← one_div]; exact one_div_lt_one_div_of_lt (by positivity) hE'
  have hf : (2 : ℝ) ≤ n.factorial := by exact_mod_cast Nat.self_le_factorial n |>.trans' hn
  have hd := tailDelta_bounds n
  have hd1 : tailDelta n ≤ 1 / 3 := hd.2.trans (by
    rw [div_le_div_iff₀ (by positivity) (by positivity)]; have : (2 : ℝ) ≤ n := by exact_mod_cast hn
    linarith)
  have hsgn : -(tailDelta n) ≤ (-1 : ℝ) ^ n * tailDelta n := by
    rcases neg_one_pow_eq_or ℝ n with h | h <;> rw [h] <;> nlinarith [tailDelta_pos n]
  nlinarith [hinv, hf, hd1, hsgn, tailDelta_pos n]

/-- `ε_n − e = (−1)^{n+1} e δ_n / !n`. -/
theorem epsChain_sub_exp (n : ℕ) (hn : 2 ≤ n) :
    epsChain n - Real.exp 1 = (-1 : ℝ) ^ (n + 1) * Real.exp 1 * tailDelta n / numDerangements n := by
  have hD := numDerangements_pos_real n hn
  have hE : (0 : ℝ) < Real.exp 1 := Real.exp_pos 1
  rw [epsChain, eq_div_iff hD.ne', sub_mul, div_mul_cancel₀ _ hD.ne']
  have h := numDerangements_eq_tailDelta n
  have hsq : ((-1 : ℝ) ^ n) ^ 2 = 1 := by rw [← pow_mul, mul_comm, pow_mul]; norm_num
  have hinv : Real.exp 1 * Real.exp (-1) = 1 := by rw [exp_neg_one_eq, mul_inv_cancel₀ hE.ne']
  rw [pow_succ]
  linear_combination (-(Real.exp 1)) * h + (-(n.factorial : ℝ)) * hinv

/-- 13:D3 — the sign `sign(ε_n − e) = (−1)^{n+1}`: `ε_{2m} < e < ε_{2m+1}`. -/
theorem epsChain_sign (n : ℕ) (hn : 2 ≤ n) : 0 < (-1 : ℝ) ^ (n + 1) * (epsChain n - Real.exp 1) := by
  rw [epsChain_sub_exp n hn]
  have hsq : ((-1 : ℝ) ^ (n + 1)) ^ 2 = 1 := by rw [← pow_mul, mul_comm, pow_mul]; norm_num
  have : (-1 : ℝ) ^ (n + 1) * ((-1) ^ (n + 1) * Real.exp 1 * tailDelta n / numDerangements n)
      = Real.exp 1 * tailDelta n / numDerangements n := by
    rw [mul_div_assoc', ← mul_assoc, ← mul_assoc, ← sq, hsq, one_mul]
  rw [this]
  exact div_pos (mul_pos (Real.exp_pos 1) (tailDelta_pos n)) (numDerangements_pos_real n hn)

/-- `ε_n ≤ e + 1` for `n ≥ 2`. -/
theorem epsChain_le (n : ℕ) (hn : 2 ≤ n) : epsChain n ≤ Real.exp 1 + 1 := by
  have hD := numDerangements_pos_real n hn
  rw [epsChain, div_le_iff₀ hD, numDerangements_eq_tailDelta]
  have hE : (2 : ℝ) < Real.exp 1 := Real.exp_one_gt_two
  have hE' : Real.exp 1 < 2.7182818286 := Real.exp_one_lt_d9
  have hinv : Real.exp 1 * Real.exp (-1) = 1 := by rw [exp_neg_one_eq, mul_inv_cancel₀ (Real.exp_pos 1).ne']
  have hd := tailDelta_bounds n
  have hdp := tailDelta_pos n
  have hsgn : -(tailDelta n) ≤ (-1 : ℝ) ^ n * tailDelta n := by
    rcases neg_one_pow_eq_or ℝ n with h | h <;> rw [h] <;> nlinarith
  have hd1 : tailDelta n * ((n : ℝ) + 1) ≤ 1 := (le_div_iff₀ (by positivity)).mp hd.2
  rcases Nat.lt_or_ge n 3 with h3 | h3
  · -- n = 2: !2 = 1 and 2 ≤ e + 1
    have : n = 2 := by omega
    subst this
    have h2 : (numDerangements 2 : ℝ) = 1 := by norm_num [numDerangements_add_two]
    rw [← numDerangements_eq_tailDelta, h2]; norm_num; linarith
  · -- n ≥ 3: n!/e − 1/(n+1) ≥ n!/(e+1) since (n+1)! ≥ 24 > e(e+1)
    have hf : (6 : ℝ) ≤ n.factorial := by
      have := Nat.factorial_le h3; exact_mod_cast (by norm_num : 6 ≤ Nat.factorial 3).trans this
    have hn3 : (3 : ℝ) ≤ n := by exact_mod_cast h3
    have hne : Real.exp (-1) = (Real.exp 1)⁻¹ := exp_neg_one_eq
    have hEinv : (1 : ℝ) / 2.7182818286 < Real.exp (-1) := by
      rw [hne, ← one_div]; exact one_div_lt_one_div_of_lt (by positivity) hE'
    nlinarith [hinv, hsgn, hd1, hf, hn3, hEinv, Real.exp_pos 1, mul_pos (Real.exp_pos 1) hdp]

/-- 13:D3 — the superexponential enclosure `|ε_n − e| ≤ e(e+1)/(n+1)! < 10.2/(n+1)!` for `n ≥ 2`. -/
theorem epsChain_enclosure (n : ℕ) (hn : 2 ≤ n) :
    |epsChain n - Real.exp 1| ≤ Real.exp 1 * (Real.exp 1 + 1) / ((n + 1).factorial : ℝ) ∧
      Real.exp 1 * (Real.exp 1 + 1) / ((n + 1).factorial : ℝ) < 10.2 / ((n + 1).factorial : ℝ) := by
  have hD := numDerangements_pos_real n hn
  have hE := Real.exp_pos 1
  have hE' : Real.exp 1 < 2.7182818286 := Real.exp_one_lt_d9
  have h1 : ((n + 1).factorial : ℝ) = (n + 1) * n.factorial := by push_cast [Nat.factorial_succ]; ring
  constructor
  · rw [epsChain_sub_exp n hn, abs_div, abs_mul, abs_mul, abs_of_pos hE, abs_of_pos (tailDelta_pos n), abs_of_pos hD]
    have hs : |(-1 : ℝ) ^ (n + 1)| = 1 := by simp
    rw [hs, one_mul, h1, div_le_div_iff₀ hD (by positivity)]
    have hd : tailDelta n * ((n : ℝ) + 1) ≤ 1 := (le_div_iff₀ (by positivity)).mp (tailDelta_bounds n).2
    have hl := epsChain_le n hn
    rw [epsChain, div_le_iff₀ hD] at hl
    nlinarith [mul_nonneg hE.le (tailDelta_pos n).le, mul_le_mul_of_nonneg_left hd hE.le, mul_le_mul_of_nonneg_left hl hE.le, mul_pos hE hD]
  · rw [div_lt_div_iff_of_pos_right (by positivity)]; nlinarith

/-! ### 13:D4 — the binary64 readout -/

theorem numDerangements_2 : numDerangements 2 = 1 := by decide
theorem numDerangements_3 : numDerangements 3 = 2 := by decide
theorem numDerangements_4 : numDerangements 4 = 9 := by decide
theorem numDerangements_5 : numDerangements 5 = 44 := by decide
theorem numDerangements_6 : numDerangements 6 = 265 := by decide
theorem numDerangements_7 : numDerangements 7 = 1854 := by decide
theorem numDerangements_8 : numDerangements 8 = 14833 := by decide
theorem numDerangements_9 : numDerangements 9 = 133496 := by decide
theorem numDerangements_10 : numDerangements 10 = 1334961 := by decide
theorem numDerangements_11 : numDerangements 11 = 14684570 := by decide
theorem numDerangements_12 : numDerangements 12 = 176214841 := by decide
theorem numDerangements_13 : numDerangements 13 = 2290792932 := by decide
theorem numDerangements_14 : numDerangements 14 = 32071101049 := by decide
theorem numDerangements_15 : numDerangements 15 = 481066515734 := by decide
theorem numDerangements_16 : numDerangements 16 = 7697064251745 := by decide
theorem numDerangements_17 : numDerangements 17 = 130850092279664 := by decide
theorem numDerangements_18 : numDerangements 18 = 2355301661033953 := by decide

/-- The binary64 constant nearest `e`: `6121026514868073 / 2^51`. -/
noncomputable def binary64E : ℝ := 6121026514868073 / 2 ^ 51

/-- 13:D4, 13:I1 — `e` lies within the half-ulp `2⁻⁵²` of the binary64 constant (from Mathlib's twenty-digit bracket of `e`),
`ε_18` lies within the same half-ulp, and no `ε_n` with `2 ≤ n ≤ 17` does: `n = 18` is the minimal readout grade. -/
theorem readout_binary64 :
    |Real.exp 1 - binary64E| < 1 / 2 ^ 52 ∧ |epsChain 18 - binary64E| < 1 / 2 ^ 52 ∧
      ∀ n, 2 ≤ n → n ≤ 17 → 1 / 2 ^ 52 < |epsChain n - binary64E| := by
  refine ⟨?_, ?_, ?_⟩
  · have h := Real.exp_one_near_20
    have h2 : |(363916618873 : ℝ) / 133877442384 - binary64E| < 1 / 2 ^ 52 - 1 / 10 ^ 20 := by
      rw [binary64E, abs_lt]; constructor <;> norm_num
    calc |Real.exp 1 - binary64E| = |(Real.exp 1 - 363916618873 / 133877442384) + (363916618873 / 133877442384 - binary64E)| := by ring_nf
      _ ≤ |Real.exp 1 - 363916618873 / 133877442384| + |(363916618873 : ℝ) / 133877442384 - binary64E| := abs_add_le _ _
      _ < 1 / 2 ^ 52 := by linarith
  · rw [epsChain, binary64E, numDerangements_18, abs_lt]; constructor <;> norm_num [Nat.factorial]
  · intro n h2 h17
    interval_cases n <;> rw [epsChain, binary64E] <;> simp only [numDerangements_2, numDerangements_3, numDerangements_4, numDerangements_5, numDerangements_6, numDerangements_7, numDerangements_8, numDerangements_9, numDerangements_10, numDerangements_11, numDerangements_12, numDerangements_13, numDerangements_14, numDerangements_15, numDerangements_16, numDerangements_17, numDerangements_18] <;> rw [lt_abs] <;> norm_num [Nat.factorial]

/-! ### 13:D5 — feasibility -/

/-- 13:D5 — the derangement chain's step counts: `n = 11, 18, 70` are the least `n` with `8/(n+1)! < 2^{−k}` for
`k = 24, 53, 333` (the enclosure bound of D3 with the sharper constant `8`; `8/(m+1)!` falls with `m`). -/
theorem derangement_cost :
    ((8 : ℚ) / (Nat.factorial 12) < 1 / 2 ^ 24 ∧ ∀ m < 11, ¬ ((8 : ℚ) / (Nat.factorial (m + 1)) < 1 / 2 ^ 24)) ∧
    ((8 : ℚ) / (Nat.factorial 19) < 1 / 2 ^ 53 ∧ ∀ m < 18, ¬ ((8 : ℚ) / (Nat.factorial (m + 1)) < 1 / 2 ^ 53)) ∧
    ((8 : ℚ) / (Nat.factorial 71) < 1 / 2 ^ 333 ∧ ∀ m < 70, ¬ ((8 : ℚ) / (Nat.factorial (m + 1)) < 1 / 2 ^ 333)) := by
  have mono : ∀ m n : ℕ, m ≤ n → (8 : ℚ) / (Nat.factorial n) ≤ 8 / (Nat.factorial m) := fun m n h =>
    div_le_div_of_nonneg_left (by norm_num) (by positivity) (by exact_mod_cast Nat.factorial_le h)
  have lt_iff : ∀ (n k : ℕ), ((8 : ℚ) / (Nat.factorial n) < 1 / 2 ^ k ↔ 8 * 2 ^ k < Nat.factorial n) := fun n k => by
    rw [div_lt_div_iff₀ (by positivity) (by positivity), one_mul]; exact_mod_cast Iff.rfl
  refine ⟨⟨?_, fun m hm h => ?_⟩, ⟨?_, fun m hm h => ?_⟩, ⟨?_, fun m hm h => ?_⟩⟩
  · rw [lt_iff]; decide
  · have := mono (m + 1) 11 (by omega); have h11 : ¬ ((8 : ℚ) / (Nat.factorial 11) < 1 / 2 ^ 24) := by
      rw [lt_iff]; decide
    exact h11 (lt_of_le_of_lt this h)
  · rw [lt_iff]; decide
  · have := mono (m + 1) 18 (by omega); have h18 : ¬ ((8 : ℚ) / (Nat.factorial 18) < 1 / 2 ^ 53) := by
      rw [lt_iff]; decide
    exact h18 (lt_of_le_of_lt this h)
  · rw [lt_iff]; decide
  · have := mono (m + 1) 70 (by omega); have h70 : ¬ ((8 : ℚ) / (Nat.factorial 70) < 1 / 2 ^ 333) := by
      rw [lt_iff]; decide
    exact h70 (lt_of_le_of_lt this h)

/-- `log(1 + 1/n) ≤ 1/n − 1/(4n²)` for `n ≥ 5` (the cubic Taylor bound of Mathlib). -/
theorem log_one_add_inv_le (n : ℕ) (hn : 5 ≤ n) :
    Real.log (1 + 1 / (n : ℝ)) ≤ 1 / n - 1 / (4 * (n : ℝ) ^ 2) := by
  have hn' : (5 : ℝ) ≤ n := by exact_mod_cast hn
  have hx : |(-1 : ℝ) / n| < 1 := by
    rw [abs_div, abs_neg, abs_one, abs_of_pos (by positivity : (0 : ℝ) < n), div_lt_one (by positivity)]; linarith
  have h := Real.abs_log_sub_add_sum_range_le hx 2
  have hsum : (∑ i ∈ Finset.range 2, ((-1 : ℝ) / n) ^ (i + 1) / (i + 1)) = -1 / n + 1 / (2 * (n : ℝ) ^ 2) := by
    simp [Finset.sum_range_succ]; field_simp; ring
  have hlog : (1 : ℝ) - (-1) / n = 1 + 1 / n := by ring
  rw [hsum, hlog] at h
  have habs : |(-1 : ℝ) / n| = 1 / n := by
    rw [abs_div, abs_neg, abs_one, abs_of_pos (by positivity : (0 : ℝ) < n)]
  rw [habs] at h
  have hn0 : (n : ℝ) ≠ 0 := by positivity
  have hn1 : (n : ℝ) - 1 ≠ 0 := by linarith
  have hrem : (1 / (n : ℝ)) ^ (2 + 1) / (1 - 1 / n) ≤ 1 / (4 * (n : ℝ) ^ 2) := by
    have ht0 : (0 : ℝ) < 1 / n := by positivity
    have ht5 : 1 / (n : ℝ) ≤ 1 / 5 := one_div_le_one_div_of_le (by norm_num) hn'
    have e : 1 / (4 * (n : ℝ) ^ 2) = (1 / n) ^ 2 / 4 := by field_simp
    rw [e, div_le_iff₀ (by linarith)]
    nlinarith [mul_pos ht0 ht0, mul_pos (mul_pos ht0 ht0) ht0]
  have h' := (abs_le.mp h).2
  have e2 : 1 / (2 * (n : ℝ) ^ 2) = 2 * (1 / (4 * (n : ℝ) ^ 2)) := by field_simp; ring
  linarith

/-- 13:D5, 13:E5, 13:I3 — the compound chain is slow: `(1 + 1/n)^n ≤ e · 4n/(4n+1)` for `n ≥ 5`, so the gap `e − (1+1/n)^n`
is at least `e/(4n+1)`: `k` bits cost `n ≍ 2^k` steps. -/
theorem compound_cost (n : ℕ) (hn : 5 ≤ n) :
    (1 + 1 / (n : ℝ)) ^ n ≤ Real.exp 1 * (4 * n) / (4 * n + 1) := by
  have hn' : (5 : ℝ) ≤ n := by exact_mod_cast hn
  have hpos : (0 : ℝ) < 1 + 1 / n := by positivity
  have hl := log_one_add_inv_le n hn
  have h1 : (1 + 1 / (n : ℝ)) ^ n = Real.exp (n * Real.log (1 + 1 / n)) := by
    rw [Real.exp_nat_mul, Real.exp_log hpos]
  have h2 : (n : ℝ) * Real.log (1 + 1 / n) ≤ 1 - 1 / (4 * n) := by
    have := mul_le_mul_of_nonneg_left hl (by positivity : (0 : ℝ) ≤ n)
    calc (n : ℝ) * Real.log (1 + 1 / n) ≤ n * (1 / n - 1 / (4 * (n : ℝ) ^ 2)) := this
      _ = 1 - 1 / (4 * n) := by field_simp
  have h3 : Real.exp (1 - 1 / (4 * (n : ℝ))) = Real.exp 1 * Real.exp (-(1 / (4 * n))) := by
    rw [← Real.exp_add]; ring_nf
  have h4 : Real.exp (-(1 / (4 * (n : ℝ)))) ≤ (4 * n) / (4 * n + 1) := by
    have := Real.add_one_le_exp (1 / (4 * (n : ℝ)))
    rw [Real.exp_neg, inv_le_comm₀ (Real.exp_pos _) (by positivity)]
    calc ((4 * (n : ℝ)) / (4 * n + 1))⁻¹ = 1 / (4 * n) + 1 := by field_simp; ring
      _ ≤ Real.exp (1 / (4 * n)) := this
  calc (1 + 1 / (n : ℝ)) ^ n = Real.exp (n * Real.log (1 + 1 / n)) := h1
    _ ≤ Real.exp (1 - 1 / (4 * n)) := Real.exp_le_exp.mpr h2
    _ = Real.exp 1 * Real.exp (-(1 / (4 * n))) := h3
    _ ≤ Real.exp 1 * ((4 * n) / (4 * n + 1)) := by gcongr
    _ = Real.exp 1 * (4 * n) / (4 * n + 1) := by ring

/-! ### 13:C5 — the joint-return tally -/

/-- 13:C5 — the returning `±1` histories of length `2n` in one direction (the sets of `n` up-steps among `2n`) number
`C(2n,n)`, the paired histories in the two directions `16^n`, and the joint returns `C(2n,n)²`. -/
theorem joint_return_tally (n : ℕ) :
    ((Finset.univ : Finset (Finset (Fin (2 * n)))).filter (fun expNegOneSum => expNegOneSum.card = n)).card = Nat.centralBinom n ∧
    Fintype.card (Finset (Fin (2 * n)) × Finset (Fin (2 * n))) = 16 ^ n ∧
    (((Finset.univ : Finset (Finset (Fin (2 * n)))).filter (fun expNegOneSum => expNegOneSum.card = n)) ×ˢ
      ((Finset.univ : Finset (Finset (Fin (2 * n)))).filter (fun expNegOneSum => expNegOneSum.card = n))).card = (Nat.centralBinom n) ^ 2 := by
  have h1 : ((Finset.univ : Finset (Finset (Fin (2 * n)))).filter (fun expNegOneSum => expNegOneSum.card = n)).card = Nat.centralBinom n := by
    rw [← Finset.powerset_univ, ← Finset.powersetCard_eq_filter, Finset.card_powersetCard, Finset.card_univ,
      Fintype.card_fin, Nat.centralBinom_eq_two_mul_choose]
  refine ⟨h1, ?_, ?_⟩
  · rw [Fintype.card_prod, Fintype.card_finset, Fintype.card_fin, ← pow_add, show 2 * n + 2 * n = 4 * n by ring, pow_mul]; norm_num
  · rw [Finset.card_product, h1, sq]

/-- `C(2n,n) · (n!)² = (2n)!`. -/
theorem centralBinom_mul_factorial_sq (n : ℕ) : Nat.centralBinom n * (n.factorial) ^ 2 = (2 * n).factorial := by
  have h := Nat.choose_mul_factorial_mul_factorial (show n ≤ 2 * n by omega)
  rw [show 2 * n - n = n by omega] at h
  rw [Nat.centralBinom_eq_two_mul_choose, sq, ← mul_assoc]; exact h

/-- `16^n/(n C_n²) = W_n · (2n+1)/n` for `n ≥ 1`, `W_n` Mathlib's Wallis product. -/
theorem wallis_chain_eq (n : ℕ) (hn : 1 ≤ n) :
    (16 : ℝ) ^ n / (n * (Nat.centralBinom n : ℝ) ^ 2) = Real.Wallis.W n * ((2 * n + 1) / n) := by
  rw [Real.Wallis.W_eq_factorial_ratio]
  have hc : (Nat.centralBinom n : ℝ) * (n.factorial : ℝ) ^ 2 = ((2 * n).factorial : ℝ) := by
    exact_mod_cast centralBinom_mul_factorial_sq n
  have hn' : (0 : ℝ) < n := by exact_mod_cast hn
  have hf : (0 : ℝ) < n.factorial := by positivity
  have hcb : (0 : ℝ) < Nat.centralBinom n := by exact_mod_cast Nat.centralBinom_pos n
  rw [← hc]
  have h16 : (2 : ℝ) ^ (4 * n) = 16 ^ n := by rw [pow_mul]; norm_num
  rw [h16]
  field_simp

/-- 13:C5 — `π = lim 16^n/(n C_n²)`: the joint-return ratio converges to `π` (Mathlib's Wallis product). -/
theorem tendsto_wallis_chain :
    Filter.Tendsto (fun n : ℕ => (16 : ℝ) ^ n / (n * (Nat.centralBinom n : ℝ) ^ 2)) Filter.atTop (𝓝 Real.pi) := by
  have hW := Real.Wallis.tendsto_W_nhds_pi_div_two
  have hr : Filter.Tendsto (fun n : ℕ => ((2 * n + 1 : ℝ) / n)) Filter.atTop (𝓝 2) := by
    have h0 : Filter.Tendsto (fun n : ℕ => (1 : ℝ) / n) Filter.atTop (𝓝 0) := tendsto_one_div_atTop_nhds_zero_nat
    have : Filter.Tendsto (fun n : ℕ => (2 : ℝ) + 1 / n) Filter.atTop (𝓝 (2 + 0)) := tendsto_const_nhds.add h0
    rw [add_zero] at this
    refine this.congr' ?_
    filter_upwards [Filter.eventually_ge_atTop 1] with n hn
    have hn' : (n : ℝ) ≠ 0 := by positivity
    field_simp
  have hprod := hW.mul hr
  rw [show Real.pi / 2 * 2 = Real.pi by ring] at hprod
  refine hprod.congr' ?_
  filter_upwards [Filter.eventually_ge_atTop 1] with n hn
  exact (wallis_chain_eq n hn).symm

end tailAndReadout

/-! ## The Machin chain, the Gregory brackets and the rounding chain (13:E3, E4, E5)

The arctangent series as a `ℚ`-native chain: the alternating bound and the alternating pairing (two-sided
enclosures at every truncation), Machin's formula `π/4 = 4 arctan(1/5) − arctan(1/239)` (Mathlib), the binary64
readout of `π` at `N = 10`, the hundred digits at `N = 71`, the rational bracket at `m = 12` that the core's
`arcsin_tail_bound` reads (E3), the Gregory brackets of the Leibniz series (the base case), and the factorial-rate
chain by rounding that exists for every real (E5). -/
section machin
open Filter Topology Real

/-- The partial sums of the arctangent series, `S_x(N) = Σ_{n ≤ N} (−1)^n x^{2n+1}/(2n+1)`. -/
noncomputable def arctanSum (x : ℝ) (N : ℕ) : ℝ := ∑ n ∈ range (N + 1), (-1 : ℝ) ^ n * (x ^ (2 * n + 1) / (2 * n + 1))

/-- The terms of the arctangent series decrease for `0 ≤ x ≤ 1`. -/
theorem arctanTerm_antitone {x : ℝ} (hx0 : 0 ≤ x) (hx1 : x ≤ 1) :
    Antitone (fun n : ℕ => x ^ (2 * n + 1) / (2 * n + 1)) := by
  intro m n hmn
  apply div_le_div₀ (by positivity) (pow_le_pow_of_le_one hx0 hx1 (by omega)) (by positivity)
  have : (m : ℝ) ≤ n := by exact_mod_cast hmn
  linarith

/-- The arctangent series sums to `arctan x` for `0 ≤ x < 1` (Mathlib's `Real.hasSum_arctan`). -/
theorem arctanTerm_hasSum {x : ℝ} (hx0 : 0 ≤ x) (hx1 : x < 1) :
    HasSum (fun n : ℕ => (-1 : ℝ) ^ n * (x ^ (2 * n + 1) / (2 * n + 1))) (arctan x) := by
  have h := Real.hasSum_arctan (x := x) (by rw [Real.norm_eq_abs, abs_of_nonneg hx0]; exact hx1)
  convert h using 1
  ext n; push_cast; ring

/-- The error of the arctangent series for `0 ≤ x < 1` is at most the first omitted term. -/
theorem arctanSum_error {x : ℝ} (hx0 : 0 ≤ x) (hx1 : x < 1) (N : ℕ) :
    |arctan x - arctanSum x N| ≤ x ^ (2 * N + 3) / (2 * N + 3) := by
  set f : ℕ → ℝ := fun n => x ^ (2 * n + 1) / (2 * n + 1) with hf
  have hfa : Antitone f := arctanTerm_antitone hx0 hx1.le
  have hsum : HasSum (fun n : ℕ => (-1 : ℝ) ^ n * f n) (arctan x) := arctanTerm_hasSum hx0 hx1
  have hfs : Summable f := by
    refine Summable.of_nonneg_of_le (fun n => by positivity) (fun n => ?_) (summable_geometric_of_lt_one hx0 hx1)
    simp only [hf]
    calc x ^ (2 * n + 1) / (2 * n + 1) ≤ x ^ (2 * n + 1) / 1 := by
            apply div_le_div_of_nonneg_left (by positivity) (by norm_num) (by linarith [(by positivity : (0:ℝ) ≤ 2 * n)])
      _ ≤ x ^ n := by rw [div_one]; exact pow_le_pow_of_le_one hx0 hx1.le (by omega)
  have h := alternating_series_error_bound f hfa hfs (N + 1)
  rw [hsum.tsum_eq] at h
  simpa [arctanSum, hf, show 2 * (N + 1) + 1 = 2 * N + 3 by ring, show ((2 : ℝ) * (N + 1) + 1) = 2 * N + 3 by ring] using h

/-- 13:E4 — the alternating pairing of the arctangent series: for `0 ≤ x < 1`, `S_x(2k+1) ≤ arctan x ≤ S_x(2k)`,
a certified two-sided enclosure at every truncation. -/
theorem arctan_pairing {x : ℝ} (hx0 : 0 ≤ x) (hx1 : x < 1) (k : ℕ) :
    arctanSum x (2 * k + 1) ≤ arctan x ∧ arctan x ≤ arctanSum x (2 * k) := by
  have hfa := arctanTerm_antitone hx0 hx1.le
  have hT := (arctanTerm_hasSum hx0 hx1).tendsto_sum_nat
  refine ⟨?_, ?_⟩
  · have h := Antitone.alternating_series_le_tendsto hT hfa (k + 1)
    rw [show 2 * (k + 1) = 2 * k + 1 + 1 by ring] at h
    exact h
  · exact Antitone.tendsto_le_alternating_series hT hfa k

/-- The Machin chain `M_N = 4(4 S_{1/5}(N) − S_{1/239}(N))`. -/
noncomputable def machin (N : ℕ) : ℝ := 4 * (4 * arctanSum (1 / 5) N - arctanSum (1 / 239) N)

/-- 13:E4, 13:E5, 13:I3 — the Machin chain's error: `|M_N − π| < 17/((2N+3)·5^{2N+3})` for every `N`, from
Machin's formula `π/4 = 4 arctan(1/5) − arctan(1/239)` and the alternating bound on each arctangent series: the
geometric `ℚ`-rate of `π`. -/
theorem machin_bound (N : ℕ) : |machin N - π| < 17 / ((2 * N + 3) * 5 ^ (2 * N + 3)) := by
  have hM := Real.four_mul_arctan_inv_5_sub_arctan_inv_239
  have h5 := arctanSum_error (x := 1 / 5) (by norm_num) (by norm_num) N
  have h239 := arctanSum_error (x := 1 / 239) (by norm_num) (by norm_num) N
  have hpi : π = 4 * (4 * arctan (1 / 5) - arctan (1 / 239)) := by
    rw [one_div, one_div, hM]; ring
  have e : machin N - π = 4 * (4 * (arctanSum (1 / 5) N - arctan (1 / 5)) - (arctanSum (1 / 239) N - arctan (1 / 239))) := by
    rw [machin, hpi]; ring
  rw [e]
  have hN : (0 : ℝ) < 2 * N + 3 := by positivity
  have h5' : |arctanSum (1 / 5) N - arctan (1 / 5)| ≤ (1 / 5) ^ (2 * N + 3) / (2 * N + 3) := by rw [abs_sub_comm]; exact h5
  have h239' : |arctanSum (1 / 239) N - arctan (1 / 239)| ≤ (1 / 239) ^ (2 * N + 3) / (2 * N + 3) := by rw [abs_sub_comm]; exact h239
  have hsmall : (1 / 239 : ℝ) ^ (2 * N + 3) < (1 / 4) * (1 / 5) ^ (2 * N + 3) := by
    have : (1 / 239 : ℝ) ^ (2 * N + 3) ≤ (1 / 239) ^ 1 * (1 / 5) ^ (2 * N + 2) := by
      rw [show 2 * N + 3 = 1 + (2 * N + 2) by ring, pow_add]
      gcongr; norm_num
    calc (1 / 239 : ℝ) ^ (2 * N + 3) ≤ (1 / 239) ^ 1 * (1 / 5) ^ (2 * N + 2) := this
      _ < (1 / 4) * (1 / 5) ^ (2 * N + 3) := by
          have hp := pow_pos (by norm_num : (0:ℝ) < 1 / 5) (2 * N + 2)
          have e3 : (1 / 5 : ℝ) ^ (2 * N + 3) = (1 / 5) ^ (2 * N + 2) * (1 / 5) := by rw [pow_succ]
          rw [e3]; norm_num; nlinarith [hp]
  calc |4 * (4 * (arctanSum (1 / 5) N - arctan (1 / 5)) - (arctanSum (1 / 239) N - arctan (1 / 239)))|
      ≤ 4 * (4 * |arctanSum (1 / 5) N - arctan (1 / 5)| + |arctanSum (1 / 239) N - arctan (1 / 239)|) := by
        rw [abs_mul, abs_of_pos (by norm_num : (0:ℝ) < 4)]
        gcongr
        calc |4 * (arctanSum (1 / 5) N - arctan (1 / 5)) - (arctanSum (1 / 239) N - arctan (1 / 239))|
            ≤ |4 * (arctanSum (1 / 5) N - arctan (1 / 5))| + |arctanSum (1 / 239) N - arctan (1 / 239)| := abs_sub _ _
          _ = 4 * |arctanSum (1 / 5) N - arctan (1 / 5)| + |arctanSum (1 / 239) N - arctan (1 / 239)| := by
              rw [abs_mul, abs_of_pos (by norm_num : (0:ℝ) < 4)]
    _ ≤ 4 * (4 * ((1 / 5) ^ (2 * N + 3) / (2 * N + 3)) + (1 / 239) ^ (2 * N + 3) / (2 * N + 3)) := by gcongr
    _ < 4 * (4 * ((1 / 5) ^ (2 * N + 3) / (2 * N + 3)) + (1 / 4) * (1 / 5) ^ (2 * N + 3) / (2 * N + 3)) := by
        gcongr
    _ = 17 / ((2 * N + 3) * 5 ^ (2 * N + 3)) := by
        rw [one_div_pow]; field_simp; ring

/-- 13:E4 — the first hundred decimal digits are fixed by `M_71`: `|M_71 − π| < 10⁻¹⁰⁰`. -/
theorem machin_hundred_digits : |machin 71 - π| < 1 / 10 ^ 100 := by
  refine lt_trans (machin_bound 71) ?_
  norm_num

/-- The pairing enclosure of the Machin chain, lower end: `4(4 S_{1/5}(2m+1) − S_{1/239}(2m))`. -/
noncomputable def machinLo (m : ℕ) : ℝ := 4 * (4 * arctanSum (1 / 5) (2 * m + 1) - arctanSum (1 / 239) (2 * m))

/-- The pairing enclosure of the Machin chain, upper end: `4(4 S_{1/5}(2m) − S_{1/239}(2m+1))`. -/
noncomputable def machinHi (m : ℕ) : ℝ := 4 * (4 * arctanSum (1 / 5) (2 * m) - arctanSum (1 / 239) (2 * m + 1))

/-- 13:E4 — the alternating pairing of the two arctangent series encloses `π` at every truncation:
`machinLo m ≤ π ≤ machinHi m`, a certified two-sided `ℚ`-enclosure. -/
theorem machin_pairing (m : ℕ) : machinLo m ≤ π ∧ π ≤ machinHi m := by
  have hM := Real.four_mul_arctan_inv_5_sub_arctan_inv_239
  have hpi : π = 4 * (4 * arctan (1 / 5) - arctan (1 / 239)) := by
    rw [one_div, one_div, hM]; ring
  have h5 := arctan_pairing (x := 1 / 5) (by norm_num) (by norm_num) m
  have h239 := arctan_pairing (x := 1 / 239) (by norm_num) (by norm_num) m
  rw [machinLo, machinHi, hpi]
  constructor <;> linarith [h5.1, h5.2, h239.1, h239.2]

/-- 13:E3 — the rational bracket of `π` at `m = 12`, the ends of the pairing enclosure as reduced fractions
(width below `10⁻³⁶`): the bracket on which the core's `arcsin_tail_bound` decides the tail bound of the arcsin
chain for `1 ≤ n ≤ 40`. -/
theorem pi_bracket_24 :
    (56982451095683495439374565467485478486061627198245408555021816811556209980957932490824931053425856737444302864615815079280095539452134822710663747992660383090256176690756 : ℝ) / 18138077522740431478132504469278196026908888402936691374051205499784758924249616118578433027852823624088713136757082253607690672547607224629473421373404562473297119140625 ≤ π ∧
    π ≤ (130195783561461477719700582162729520693370052310728319298679169305810308737653928066126520396560009514814646871106941551053006194003594103465911391825667397563687081581706376 : ℝ) / 41442605047058247458496271511585593410122504578565869919087156374128208580482492892372746919359245529262855323388051816332995956263674891122406052090809680521488189697265625 := by
  have h := machin_pairing 12
  have hLo : machinLo 12 = (56982451095683495439374565467485478486061627198245408555021816811556209980957932490824931053425856737444302864615815079280095539452134822710663747992660383090256176690756 : ℝ) / 18138077522740431478132504469278196026908888402936691374051205499784758924249616118578433027852823624088713136757082253607690672547607224629473421373404562473297119140625 := by
    rw [machinLo, arctanSum, arctanSum]; simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hHi : machinHi 12 = (130195783561461477719700582162729520693370052310728319298679169305810308737653928066126520396560009514814646871106941551053006194003594103465911391825667397563687081581706376 : ℝ) / 41442605047058247458496271511585593410122504578565869919087156374128208580482492892372746919359245529262855323388051816332995956263674891122406052090809680521488189697265625 := by
    rw [machinHi, arctanSum, arctanSum]; simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  rw [hLo] at h; rw [hHi] at h
  exact h

/-- The binary64 constant nearest `π`: `884279719003555 / 2^48`. -/
noncomputable def binary64Pi : ℝ := 884279719003555 / 2 ^ 48

/-- 13:E4, 13:I2 — the binary64 readout of `π`: `π` and `M_10` lie within the half-ulp `2⁻⁵²` of the binary64 constant
(Mathlib's twenty-digit bracket of `π`), and no `M_N` with `N ≤ 9` does: `N = 10` is minimal. -/
theorem readout_binary64_pi :
    |π - binary64Pi| < 1 / 2 ^ 52 ∧ |machin 10 - binary64Pi| < 1 / 2 ^ 52 ∧ ∀ N ≤ 9, 1 / 2 ^ 52 < |machin N - binary64Pi| := by
  refine ⟨?_, ?_, ?_⟩
  · have h1 := Real.pi_gt_d20; have h2 := Real.pi_lt_d20
    rw [binary64Pi, abs_lt]; constructor <;> norm_num at h1 h2 ⊢ <;> linarith
  · rw [machin, arctanSum, arctanSum, binary64Pi, abs_lt]; simp only [Finset.sum_range_succ, Finset.sum_range_zero]
    constructor <;> norm_num
  · intro N hN
    interval_cases N <;> rw [machin, arctanSum, arctanSum, binary64Pi, lt_abs] <;> simp only [Finset.sum_range_succ, Finset.sum_range_zero] <;> norm_num

/-- The Leibniz partial sums `S_m = Σ_{n < m} (−1)^n/(2n+1)`. -/
noncomputable def leibnizSum (m : ℕ) : ℝ := ∑ n ∈ range m, (-1 : ℝ) ^ n * (1 / (2 * n + 1))

/-- 13:E4, 13:E5 — the Gregory brackets, the base case of the pairing: `S_{2m} ≤ π/4 ≤ S_{2m+1}`, of width
`1/(4m+1)` — the Leibniz chain's `2^k` steps per `k` binary digits. -/
theorem gregory_brackets (m : ℕ) : leibnizSum (2 * m) ≤ π / 4 ∧ π / 4 ≤ leibnizSum (2 * m + 1) ∧
    leibnizSum (2 * m + 1) - leibnizSum (2 * m) = 1 / (4 * m + 1) := by
  have hT : Tendsto leibnizSum atTop (𝓝 (π / 4)) := by
    have h := Real.tendsto_sum_pi_div_four
    refine h.congr' (Eventually.of_forall fun m => ?_)
    simp only [leibnizSum]; refine sum_congr rfl fun i _ => ?_; rw [mul_one_div]
  have hfa : Antitone (fun n : ℕ => (1 : ℝ) / (2 * n + 1)) := by
    intro a b hab; apply one_div_le_one_div_of_le (by positivity)
    have : (a : ℝ) ≤ b := by exact_mod_cast hab
    linarith
  refine ⟨Antitone.alternating_series_le_tendsto hT hfa m, Antitone.tendsto_le_alternating_series hT hfa m, ?_⟩
  rw [leibnizSum, leibnizSum, sum_range_succ]
  have : (-1 : ℝ) ^ (2 * m) = 1 := by rw [pow_mul]; norm_num
  rw [this]; push_cast; ring

/-- 13:E5 — a factorial-rate chain exists for every real by rounding: `|x − ⌊x·n!⌋/n!| < 1/n!`, so the
feasibility split is by kind of chain, not by rate. -/
theorem rounding_chain (x : ℝ) (n : ℕ) : |x - (⌊x * n.factorial⌋ : ℝ) / n.factorial| < 1 / n.factorial := by
  have hf : (0 : ℝ) < n.factorial := by positivity
  have h1 := Int.floor_le (x * n.factorial)
  have h2 := Int.lt_floor_add_one (x * n.factorial)
  have e : x - (⌊x * n.factorial⌋ : ℝ) / n.factorial = (x * n.factorial - ⌊x * n.factorial⌋) / n.factorial := by
    field_simp
  rw [e, abs_div, abs_of_pos hf, div_lt_div_iff_of_pos_right hf, abs_lt]
  constructor <;> linarith

end machin


/-- Kurepa's left factorial `!n = Σ_{k<n} k!`. -/
def kurepa (n : ℕ) : ℕ := ∑ k ∈ range n, k !

/-- The alternating factorial sum `A(n) = Σ_{k<n} (−1)^k k!`. -/
def altFact (n : ℕ) : ℤ := ∑ k ∈ range n, (-1 : ℤ) ^ k * (k ! : ℤ)

/-! ## The wall, over any field of characteristic `p` with Wilson's value

Everything is proved once over a field `K` in which `p = 0`, `(p−1)! = −1` and `k! ≠ 0` for `k ≤ p − 1`;
the section `prime` instantiates `K := ZMod p` (whose instances under `Fact p.Prime` are not `ring`-friendly). -/
section wall

variable {K : Type*} [Field K]

theorem neg_one_pow_mul_self (k : ℕ) : (-1 : K) ^ k * (-1) ^ k = 1 := by
  rw [← pow_add, ← two_mul, pow_mul]; simp

theorem neg_one_pow_sub_of_pow_eq_one {a k : ℕ} (h : (-1 : K) ^ a = 1) (hk : k ≤ a) :
    (-1 : K) ^ (a - k) = (-1) ^ k := by
  have : (-1 : K) ^ (a - k) * ((-1) ^ k * (-1) ^ k) = (-1) ^ a * (-1) ^ k := by
    rw [← mul_assoc, ← pow_add, Nat.sub_add_cancel hk]
  rwa [neg_one_pow_mul_self, mul_one, h, one_mul] at this

theorem natCast_pred_sub (p : ℕ) (hp0 : (p : K) = 0) (h1 : 1 ≤ p) (k : ℕ) (hk : k ≤ p - 1) :
    ((p - 1 - k : ℕ) : K) = -((k : K) + 1) := by
  rw [Nat.cast_sub hk, Nat.cast_sub h1, hp0]; ring

theorem factorial_mul_reflect (p : ℕ) (hp0 : (p : K) = 0) (hw : (((p - 1) ! : ℕ) : K) = -1)
    (h1 : 1 ≤ p) (k : ℕ) (hk : k ≤ p - 1) :
    ((k ! : ℕ) : K) * (((p - 1 - k) ! : ℕ) : K) = -(-1) ^ k := by
  induction k with
  | zero => rw [Nat.factorial_zero, Nat.cast_one, one_mul, Nat.sub_zero, hw, pow_zero]
  | succ k ih =>
    have hk' : k ≤ p - 1 := Nat.le_of_succ_le hk
    have e : p - 1 - k = (p - 1 - (k + 1)) + 1 := by omega
    have := ih hk'
    rw [e, Nat.factorial_succ, ← e, Nat.cast_mul, natCast_pred_sub p hp0 h1 k hk'] at this
    rw [Nat.factorial_succ, Nat.cast_mul, Nat.cast_add, Nat.cast_one]
    linear_combination -this

theorem wilson_reflection (p : ℕ) (hp0 : (p : K) = 0) (hw : (((p - 1) ! : ℕ) : K) = -1)
    (h1 : 1 ≤ p) (k : ℕ) (hk : k ≤ p - 1) :
    ((k ! : ℕ) : K)⁻¹ = -(-1) ^ k * (((p - 1 - k) ! : ℕ) : K) := by
  apply inv_eq_of_mul_eq_one_right
  linear_combination -(-1 : K) ^ k * factorial_mul_reflect p hp0 hw h1 k hk + neg_one_pow_mul_self (K := K) k

theorem ascFactorial_reflect (p : ℕ) (hp0 : (p : K) = 0) (hw : (((p - 1) ! : ℕ) : K) = -1)
    (hfac : ∀ k, k ≤ p - 1 → ((k ! : ℕ) : K) ≠ 0) (h1 : 1 ≤ p) (k : ℕ) (hk : k ≤ p - 1) :
    (((k + 1).ascFactorial (p - 1 - k) : ℕ) : K) = (-1) ^ k * (((p - 1 - k) ! : ℕ) : K) := by
  apply mul_left_cancel₀ (hfac k hk)
  have hA : ((k ! : ℕ) : K) * ((k + 1).ascFactorial (p - 1 - k) : ℕ) = -1 := by
    rw [← Nat.cast_mul, Nat.factorial_mul_ascFactorial, Nat.add_sub_cancel' hk, hw]
  linear_combination hA - (-1 : K) ^ k * factorial_mul_reflect p hp0 hw h1 k hk + neg_one_pow_mul_self (K := K) k

theorem derangements_wall (p : ℕ) (hp0 : (p : K) = 0) (hw : (((p - 1) ! : ℕ) : K) = -1)
    (hfac : ∀ k, k ≤ p - 1 → ((k ! : ℕ) : K) ≠ 0) (h1 : 1 ≤ p) :
    ((numDerangements (p - 1) : ℕ) : K) = (kurepa p : K) := by
  have h := numDerangements_sum (p - 1)
  have hcast : ((numDerangements (p - 1) : ℕ) : K) = ((numDerangements (p - 1) : ℤ) : K) := by
    rw [Int.cast_natCast]
  rw [hcast, h, Int.cast_sum]
  simp only [Int.cast_mul, Int.cast_pow, Int.cast_neg, Int.cast_one, Int.cast_natCast]
  rw [Nat.sub_add_cancel h1]
  unfold kurepa
  rw [Nat.cast_sum, ← sum_range_reflect (fun j => ((j ! : ℕ) : K)) p]
  apply sum_congr rfl
  intro k hk
  have hk' : k ≤ p - 1 := by have := mem_range.1 hk; omega
  rw [ascFactorial_reflect p hp0 hw hfac h1 k hk', ← mul_assoc, neg_one_pow_mul_self, one_mul]

theorem derangements_succ_cast (n : ℕ) :
    ((numDerangements (n + 1) : ℕ) : K) = ((n : K) + 1) * (numDerangements n : ℕ) - (-1) ^ n := by
  have := congrArg (fun z : ℤ => (z : K)) (numDerangements_succ n)
  simp only [Int.cast_natCast, Int.cast_sub, Int.cast_mul, Int.cast_add, Int.cast_one, Int.cast_pow,
    Int.cast_neg] at this
  exact this

theorem neg_one_pow_pred_of_odd (p : ℕ) (hodd : Odd p) : (-1 : K) ^ (p - 1) = 1 := by
  obtain ⟨m, hm⟩ := hodd
  rw [hm, Nat.add_sub_cancel, pow_mul]; simp

theorem derangements_antiperiodic (p : ℕ) (hp0 : (p : K) = 0) (hodd : Odd p) (n : ℕ) :
    ((numDerangements (n + p) : ℕ) : K) = -((numDerangements n : ℕ) : K) := by
  have hneg : (-1 : K) ^ p = -1 := hodd.neg_one_pow
  have h1 : 1 ≤ p := hodd.pos
  induction n with
  | zero =>
    have h := derangements_succ_cast (K := K) (p - 1)
    rw [Nat.sub_add_cancel h1] at h
    rw [zero_add, h, neg_one_pow_pred_of_odd p hodd, numDerangements_zero, Nat.cast_one,
      Nat.cast_sub h1, hp0]
    ring
  | succ n ih =>
    rw [show n + 1 + p = (n + p) + 1 by omega, derangements_succ_cast, ih,
      derangements_succ_cast, pow_add, hneg, Nat.cast_add, hp0]
    ring

theorem series_duals (p : ℕ) (hp0 : (p : K) = 0) (hw : (((p - 1) ! : ℕ) : K) = -1) (hodd : Odd p) :
    (∑ k ∈ range p, (-1 : K) ^ k * ((k ! : ℕ) : K)⁻¹) = -(kurepa p : K) ∧
    (∑ k ∈ range p, ((k ! : ℕ) : K)⁻¹) = -((altFact p : ℤ) : K) := by
  have h1 : 1 ≤ p := hodd.pos
  constructor
  · unfold kurepa
    rw [Nat.cast_sum, ← sum_range_reflect (fun j => ((j ! : ℕ) : K)) p, ← sum_neg_distrib]
    apply sum_congr rfl
    intro k hk
    have hk' : k ≤ p - 1 := by have := mem_range.1 hk; omega
    rw [wilson_reflection p hp0 hw h1 k hk']
    linear_combination -((((p - 1 - k) ! : ℕ) : K)) * neg_one_pow_mul_self (K := K) k
  · unfold altFact
    rw [Int.cast_sum]
    simp only [Int.cast_mul, Int.cast_pow, Int.cast_neg, Int.cast_one, Int.cast_natCast]
    rw [← sum_range_reflect (fun j => (-1 : K) ^ j * ((j ! : ℕ) : K)) p, ← sum_neg_distrib]
    apply sum_congr rfl
    intro k hk
    have hk' : k ≤ p - 1 := by have := mem_range.1 hk; omega
    rw [wilson_reflection p hp0 hw h1 k hk',
      neg_one_pow_sub_of_pow_eq_one (neg_one_pow_pred_of_odd p hodd) hk']
    ring

theorem tower_e_exact (p : ℕ) (hp0 : (p : K) = 0) (hodd : Odd p)
    (hfacp : ∀ m, 1 ≤ m → (((m * p) ! : ℕ) : K) = 0) (m : ℕ) (hm : 1 ≤ m) (e δ : K)
    (hδ : δ = (-1) ^ m * e) :
    (((m * p) ! : ℕ) : K) = 0 ∧ ((numDerangements (m * p) : ℕ) : K) = (-1) ^ m ∧
    ((((m * p) ! : ℕ) : K) + δ) / ((numDerangements (m * p) : ℕ) : K) = e := by
  have hder : ∀ m, ((numDerangements (m * p) : ℕ) : K) = (-1) ^ m := by
    intro m
    induction m with
    | zero => rw [Nat.zero_mul, numDerangements_zero, Nat.cast_one, pow_zero]
    | succ m ih => rw [Nat.succ_mul, derangements_antiperiodic p hp0 hodd, ih, pow_succ, mul_neg_one]
  refine ⟨hfacp m hm, hder m, ?_⟩
  rw [hfacp m hm, hder, zero_add, hδ]
  exact mul_div_cancel_left₀ e (pow_ne_zero m (neg_ne_zero.2 one_ne_zero))

/-- The tail identity: `j! · !(p−1−j) = (−1)^j · (K(p) − K(j))` for `0 ≤ j ≤ p − 1` — the derangement residue
line read from the wall is the sequence of tails `Σ_{m=j}^{p−1} m!` of Kurepa's left factorial. -/
theorem tail_identity (p : ℕ) (hp0 : (p : K) = 0) (hw : (((p - 1) ! : ℕ) : K) = -1)
    (hfac : ∀ k, k ≤ p - 1 → ((k ! : ℕ) : K) ≠ 0) (h1 : 1 ≤ p) (j : ℕ) (hj : j ≤ p - 1) :
    ((j ! : ℕ) : K) * ((numDerangements (p - 1 - j) : ℕ) : K) = (-1) ^ j * ((kurepa p : K) - (kurepa j : K)) := by
  have hcast : ((numDerangements (p - 1 - j) : ℕ) : K) = ((numDerangements (p - 1 - j) : ℤ) : K) := by
    rw [Int.cast_natCast]
  rw [hcast, numDerangements_sum, Int.cast_sum]
  simp only [Int.cast_mul, Int.cast_pow, Int.cast_neg, Int.cast_one, Int.cast_natCast]
  rw [Finset.mul_sum]
  have hterm : ∀ k ∈ range (p - 1 - j + 1),
      ((j ! : ℕ) : K) * ((-1) ^ k * (((k + 1).ascFactorial (p - 1 - j - k) : ℕ) : K)) =
        (-1) ^ j * (((p - 1 - k) ! : ℕ) : K) := by
    intro k hk
    have hk' : k ≤ p - 1 - j := by have := mem_range.1 hk; omega
    have hA : ((k ! : ℕ) : K) * (((k + 1).ascFactorial (p - 1 - j - k) : ℕ) : K) = (((p - 1 - j) ! : ℕ) : K) := by
      rw [← Nat.cast_mul, Nat.factorial_mul_ascFactorial, Nat.add_sub_cancel' hk']
    have hjr := factorial_mul_reflect p hp0 hw h1 j hj
    have hkr := factorial_mul_reflect p hp0 hw h1 k (by omega)
    apply mul_left_cancel₀ (hfac k (by omega))
    linear_combination (-1 : K) ^ k * ((j ! : ℕ) : K) * hA + (-1 : K) ^ k * hjr - (-1 : K) ^ j * hkr
  rw [Finset.sum_congr rfl hterm, ← Finset.mul_sum]
  congr 1
  have hn : p - 1 - j + 1 = p - j := by omega
  rw [hn]
  have hre : ∀ k ∈ range (p - j), (((p - 1 - k) ! : ℕ) : K) = (fun i => (((j + i) ! : ℕ) : K)) ((p - j) - 1 - k) := by
    intro k hk
    have := mem_range.1 hk
    show (((p - 1 - k) ! : ℕ) : K) = (((j + ((p - j) - 1 - k)) ! : ℕ) : K)
    congr 2; omega
  rw [Finset.sum_congr rfl hre, Finset.sum_range_reflect (fun i => (((j + i) ! : ℕ) : K)) (p - j),
    ← Finset.sum_Ico_eq_sum_range (fun m => ((m ! : ℕ) : K)) j p]
  unfold kurepa
  rw [Nat.cast_sum, Nat.cast_sum, eq_sub_iff_add_eq, add_comm, Finset.sum_range_add_sum_Ico _ (by omega)]

end wall

/-! ## The prime shell: `K := ZMod p` -/
section prime

variable (p : ℕ) [hp : Fact p.Prime]

theorem factorial_ne_zero_zmod (k : ℕ) (hk : k ≤ p - 1) : ((k ! : ℕ) : ZMod p) ≠ 0 := by
  rw [Ne, ZMod.natCast_eq_zero_iff]
  intro h
  have := (hp.out.dvd_factorial).1 h
  have := hp.out.two_le
  omega

theorem factorial_mul_prime_eq_zero (m : ℕ) (hm : 1 ≤ m) : (((m * p) ! : ℕ) : ZMod p) = 0 := by
  rw [ZMod.natCast_eq_zero_iff]
  exact (hp.out.dvd_factorial).2 (Nat.le_mul_of_pos_left p hm)

/-- 13:F1 — Wilson reflection: `1/k! ≡ −(−1)^k (p−1−k)! (mod p)` for `0 ≤ k ≤ p − 1`, from Wilson's
theorem `(p−1)! ≡ −1` and `p − j ≡ −j`. -/
theorem wilson_reflection_zmod (k : ℕ) (hk : k ≤ p - 1) :
    ((k ! : ℕ) : ZMod p)⁻¹ = -(-1) ^ k * (((p - 1 - k) ! : ℕ) : ZMod p) :=
  wilson_reflection p (ZMod.natCast_self p) (ZMod.wilsons_lemma p) hp.out.one_le k hk

/-- 13:F2, 13:J6 — the wall identity: `!(p−1) ≡ !p (mod p)` for every prime `p` — the derangement number at the wall
is Kurepa's left factorial (the odd-prime case of the Mijajlović–Šami congruence), from Wilson reflection. -/
theorem derangements_wall_zmod : ((numDerangements (p - 1) : ℕ) : ZMod p) = (kurepa p : ZMod p) :=
  derangements_wall p (ZMod.natCast_self p) (ZMod.wilsons_lemma p) (factorial_ne_zero_zmod p) hp.out.one_le

/-- 13:F2 — the terminal residue of `e`: `⟦ε_{p−1}⟧ = (p−1)!/!(p−1) = −(!p)⁻¹`, and the terminal link exists
(`!(p−1) ≢ 0`) exactly when `p ∤ !p`. -/
theorem terminal_residue :
    (((p - 1) ! : ℕ) : ZMod p) / ((numDerangements (p - 1) : ℕ) : ZMod p) = -(kurepa p : ZMod p)⁻¹ ∧
    (((numDerangements (p - 1) : ℕ) : ZMod p) ≠ 0 ↔ ¬ p ∣ kurepa p) := by
  rw [derangements_wall_zmod, ZMod.wilsons_lemma, div_eq_mul_inv, neg_one_mul, Ne,
    ZMod.natCast_eq_zero_iff]
  exact ⟨rfl, Iff.rfl⟩

/-- 13:F3 — antiperiodicity: `!(n + p) ≡ −!n (mod p)` for every odd prime `p` and every `n ≥ 0`, so
`!n mod p` depends on `n mod 2p`; the blind set always contains `n = 1` (`!1 = 0`). -/
theorem derangements_antiperiodic_zmod (hp2 : p ≠ 2) (n : ℕ) :
    ((numDerangements (n + p) : ℕ) : ZMod p) = -((numDerangements n : ℕ) : ZMod p) ∧
    numDerangements 1 = 0 :=
  ⟨derangements_antiperiodic p (ZMod.natCast_self p) (hp.out.odd_of_ne_two hp2) n, numDerangements_one⟩

/-- 13:F4 — the series duals at the wall: `Σ_{k<p} (−1)^k/k! ≡ −!p` and `Σ_{k<p} 1/k! ≡ −A(p)`, `A(p)` the
alternating factorial sum, for every odd prime `p`. -/
theorem series_duals_zmod (hp2 : p ≠ 2) :
    (∑ k ∈ range p, (-1 : ZMod p) ^ k * ((k ! : ℕ) : ZMod p)⁻¹) = -(kurepa p : ZMod p) ∧
    (∑ k ∈ range p, ((k ! : ℕ) : ZMod p)⁻¹) = -((altFact p : ℤ) : ZMod p) :=
  series_duals p (ZMod.natCast_self p) (ZMod.wilsons_lemma p) (hp.out.odd_of_ne_two hp2)

/-- 13:F7 — the fixed-shell tower of `e` is exact at every grade: `(mp)! ≡ 0` and `!(mp) ≡ (−1)^m (mod p)`
for `m ≥ 1`, so `q_m = ((mp)! + δ_m)/!(mp)` reads `e_p` on the shell whenever `δ_m ≡ (−1)^m e_p`. -/
theorem tower_e_exact_zmod (hp2 : p ≠ 2) (m : ℕ) (hm : 1 ≤ m) (e δ : ZMod p) (hδ : δ = (-1) ^ m * e) :
    (((m * p) ! : ℕ) : ZMod p) = 0 ∧ ((numDerangements (m * p) : ℕ) : ZMod p) = (-1) ^ m ∧
    ((((m * p) ! : ℕ) : ZMod p) + δ) / ((numDerangements (m * p) : ℕ) : ZMod p) = e :=
  tower_e_exact p (ZMod.natCast_self p) (hp.out.odd_of_ne_two hp2) (factorial_mul_prime_eq_zero p) m hm e δ hδ

/-- 13:F8, 13:Z1 — the tail identity on the shell: `j! · !(p−1−j) ≡ (−1)^j (!p − !j) (mod p)`, `0 ≤ j ≤ p − 1`. -/
theorem tail_identity_zmod (j : ℕ) (hj : j ≤ p - 1) :
    ((j ! : ℕ) : ZMod p) * ((numDerangements (p - 1 - j) : ℕ) : ZMod p) =
      (-1) ^ j * ((kurepa p : ZMod p) - (kurepa j : ZMod p)) :=
  tail_identity p (ZMod.natCast_self p) (ZMod.wilsons_lemma p) (factorial_ne_zero_zmod p) hp.out.one_le j hj

/-- 13:F8, 13:Z1 — the collision reading of the blind set: for `n ≤ p − 1`, `!n ≡ 0 (mod p)` exactly when the partial
sum `!(p−1−n)` of the left factorial collides with `!p`; Kurepa's hypothesis at `p` is the case `n = p − 1`,
`!(0) = 0 ≢ !p`; the universal blind scale `n = 1` is `!(p−2) ≡ !p` (the tail `(p−2)! + (p−1)! ≡ 0`). -/
theorem blind_iff_collision (n : ℕ) (hn : n ≤ p - 1) :
    (((numDerangements n : ℕ) : ZMod p) = 0 ↔ (kurepa (p - 1 - n) : ZMod p) = (kurepa p : ZMod p)) ∧
    (kurepa (p - 2) : ZMod p) = (kurepa p : ZMod p) := by
  have key : ∀ n, n ≤ p - 1 →
      (((numDerangements n : ℕ) : ZMod p) = 0 ↔ (kurepa (p - 1 - n) : ZMod p) = (kurepa p : ZMod p)) := by
    intro n hn
    have h := tail_identity_zmod p (p - 1 - n) (by omega)
    rw [show p - 1 - (p - 1 - n) = n by omega] at h
    have hf := factorial_ne_zero_zmod p (p - 1 - n) (by omega)
    have hs : ((-1 : ZMod p) ^ (p - 1 - n)) ≠ 0 := by
      apply pow_ne_zero; intro h1
      exact (one_ne_zero : (1 : ZMod p) ≠ 0) (neg_eq_zero.1 h1)
    constructor
    · intro h0
      rw [h0, mul_zero] at h
      have := (mul_eq_zero.1 h.symm).resolve_left hs
      exact (sub_eq_zero.1 this).symm
    · intro hc
      have : ((-1 : ZMod p) ^ (p - 1 - n)) * ((kurepa p : ZMod p) - (kurepa (p - 1 - n) : ZMod p)) = 0 := by
        rw [hc, sub_self, mul_zero]
      rw [← h] at this
      exact (mul_eq_zero.1 this).resolve_left hf
  refine ⟨key n hn, ?_⟩
  have h2 := hp.out.two_le
  have := (key 1 (by omega)).1 (by rw [numDerangements_one, Nat.cast_zero])
  rwa [show p - 1 - 1 = p - 2 by omega] at this

end prime



/-! ## The wall hierarchy of `π`: the Wallis chain `w_n = 16^n/(n C_n²)` on the shell -/
section wallpi

variable {K : Type*} [Field K]

theorem sq_eq_one_of_eq_neg_one_pow (c : K) (m : ℕ) (h : c = (-1) ^ m) : c ^ 2 = 1 := by
  rw [h, ← pow_mul, mul_comm, pow_mul]; norm_num

/-- `C(p−1, k) ≡ (−1)^k`, from `C(n, k+1)(k+1) = C(n, k)(n − k)` and `p − 1 − k ≡ −(k+1)`. -/
theorem choose_pred_eq_neg_one_pow (p : ℕ) (hp0 : (p : K) = 0) (h1 : 1 ≤ p)
    (hunit : ∀ j, 1 ≤ j → j ≤ p - 1 → (j : K) ≠ 0) (k : ℕ) (hk : k ≤ p - 1) :
    ((choose (p - 1) k : ℕ) : K) = (-1) ^ k := by
  induction k with
  | zero => rw [choose_zero_right, Nat.cast_one, pow_zero]
  | succ k ih =>
    have hk' : k ≤ p - 1 := Nat.le_of_succ_le hk
    have h := congrArg (fun m : ℕ => (m : K)) (Nat.choose_succ_right_eq (p - 1) k)
    simp only [Nat.cast_mul, Nat.cast_add, Nat.cast_one] at h
    rw [ih hk', Nat.cast_sub hk', Nat.cast_sub h1, hp0] at h
    have hne : ((k : K) + 1) ≠ 0 := by
      have := hunit (k + 1) (by omega) hk
      rwa [Nat.cast_add, Nat.cast_one] at this
    apply mul_right_cancel₀ hne
    rw [h, pow_succ]; ring

theorem half_wall_generic (m : K) (h2m : (2 : K) * m = -1) (x c : K)
    (hx : x = 1) (hc : c ^ 2 = 1) :
    x / (m * c ^ 2) = -2 ∧ m⁻¹ = -2 ∧ (4 : K) * m = -2 := by
  have hinv : m⁻¹ = -2 := inv_eq_of_mul_eq_one_right (by linear_combination -h2m)
  refine ⟨?_, hinv, by linear_combination 2 * h2m⟩
  rw [hx, hc, mul_one, one_div, hinv]

theorem quarter_wall_generic (κ a b c : K) (hκ : (4 : K) * κ = -1) (h2 : (2 : K) ≠ 0)
    (hC : c = 2 * a) (ha : a ≠ 0) (hab : a ^ 2 + b ^ 2 = 0) (x : K) (hx : x = 1) :
    x / (κ * c ^ 2) = -(a ^ 2)⁻¹ ∧ -(a ^ 2)⁻¹ = (b ^ 2)⁻¹ := by
  have hκ0 : κ ≠ 0 := by
    intro h; rw [h, mul_zero] at hκ; exact one_ne_zero (by linear_combination hκ)
  have hc0 : c ≠ 0 := by rw [hC]; exact mul_ne_zero h2 ha
  have hinv : (a ^ 2)⁻¹ * a ^ 2 = 1 := inv_mul_cancel₀ (pow_ne_zero 2 ha)
  constructor
  · rw [div_eq_iff (mul_ne_zero hκ0 (pow_ne_zero 2 hc0)), hx, hC]
    linear_combination 4 * κ * hinv + hκ
  · rw [neg_inv]; congr 1; linear_combination -hab

theorem first_revival_generic (x c d : K) (h2 : (2 : K) ≠ 0) (hx : x = 16) (hc : c = 2) (hd : d = 1) :
    2 * x / (d * c ^ 2) = 8 := by
  subst hx hc hd; field_simp; ring

theorem tower_pi_generic (x c d δ κ : K) (h2 : (2 : K) ≠ 0) (hx : x = 16) (hc : c = 2) (hd : d = 1)
    (hδ : δ = -34) (hκ : (4 : K) * κ = -1) :
    (2 * x + δ) / (d * c ^ 2) = 2 * κ := by
  subst hx hc hd hδ; field_simp; linear_combination -2 * hκ

end wallpi

section primepi

variable (p : ℕ) [hp : Fact p.Prime]

theorem natCast_ne_zero_of_lt (j : ℕ) (hj0 : 1 ≤ j) (hj : j < p) : (j : ZMod p) ≠ 0 := by
  rw [Ne, ZMod.natCast_eq_zero_iff]
  intro h
  have := Nat.le_of_dvd (by omega) h
  omega

theorem two_ne_zero_zmod (hp2 : p ≠ 2) : (2 : ZMod p) ≠ 0 := by
  have := natCast_ne_zero_of_lt p 2 (by omega) (lt_of_le_of_ne hp.out.two_le (Ne.symm hp2))
  rwa [Nat.cast_ofNat] at this

/-- 13:G1 — the legibility window: `p ∤ C(2n,n)` for `1 ≤ n ≤ (p−1)/2` and `p ∣ C(2n,n)` for
`(p−1)/2 < n < p` — the residue line of the Wallis chain is defined exactly on `[1, (p−1)/2]`. -/
theorem legibility_window (n : ℕ) :
    (2 * n ≤ p - 1 → ¬ p ∣ centralBinom n) ∧ (p ≤ 2 * n → n < p → p ∣ centralBinom n) := by
  have hfac : centralBinom n * n ! * n ! = (2 * n) ! := by
    have := Nat.choose_mul_factorial_mul_factorial (show n ≤ 2 * n by omega)
    rwa [show 2 * n - n = n by omega, ← centralBinom_eq_two_mul_choose] at this
  constructor
  · intro hn hdvd
    have : p ∣ (2 * n) ! := hfac ▸ Dvd.dvd.mul_right (Dvd.dvd.mul_right hdvd _) _
    have := (hp.out.dvd_factorial).1 this
    have := hp.out.pos
    omega
  · intro hn hnp
    have h1 : p ∣ (2 * n) ! := (hp.out.dvd_factorial).2 hn
    rw [← hfac] at h1
    have hnf : ¬ p ∣ n ! := fun h => by have := (hp.out.dvd_factorial).1 h; omega
    rcases (hp.out.dvd_mul).1 h1 with h | h
    · rcases (hp.out.dvd_mul).1 h with h | h
      · exact h
      · exact absurd h hnf
    · exact absurd h hnf

/-- 13:G2 — the half-wall terminus, the calibration face: with `m = (p−1)/2`, `16^m ≡ 1`,
`C(2m,m)² ≡ 1`, and `⟦w_m⟧ = m⁻¹ = −2` for every odd prime; the identity `4·π_A ≡ −2` beside it. -/
theorem half_wall_terminus (hp2 : p ≠ 2) (m : ℕ) (hm : p = 2 * m + 1) :
    (16 : ZMod p) ^ m = 1 ∧ ((centralBinom m : ℕ) : ZMod p) ^ 2 = 1 ∧
    wallisW m = (-2 : ZMod p) ∧ (m : ZMod p)⁻¹ = -2 ∧ (4 : ZMod p) * m = -2 := by
  have h2 : (2 : ZMod p) ≠ 0 := two_ne_zero_zmod p hp2
  have h4 : (4 : ZMod p) ≠ 0 := by
    have : (4 : ZMod p) = 2 * 2 := by norm_num
    rw [this]; exact mul_ne_zero h2 h2
  have h16 : (16 : ZMod p) ^ m = 1 := by
    have : (16 : ZMod p) ^ m = (4 : ZMod p) ^ (p - 1) := by
      rw [show p - 1 = 2 * m by omega, pow_mul]; norm_num
    rw [this]; exact ZMod.pow_card_sub_one_eq_one h4
  have hC : ((centralBinom m : ℕ) : ZMod p) = (-1) ^ m := by
    have hm' : m ≤ p - 1 := by omega
    have := choose_pred_eq_neg_one_pow (K := ZMod p) p (ZMod.natCast_self p) hp.out.one_le
      (fun j hj0 hj => natCast_ne_zero_of_lt p j hj0 (by omega)) m hm'
    rw [centralBinom_eq_two_mul_choose, show 2 * m = p - 1 by omega]; exact this
  have hC2 : ((centralBinom m : ℕ) : ZMod p) ^ 2 = 1 := by
    exact sq_eq_one_of_eq_neg_one_pow _ m hC
  have h2m : (2 : ZMod p) * m = -1 := by
    have : ((2 * m + 1 : ℕ) : ZMod p) = 0 := by rw [← hm]; exact ZMod.natCast_self p
    push_cast at this
    exact eq_neg_of_add_eq_zero_left this
  obtain ⟨hw, hinv, h4m⟩ := half_wall_generic (K := ZMod p) m h2m _ _ h16 hC2
  exact ⟨h16, hC2, hw, hinv, h4m⟩

/-- 13:G3 — the quarter-wall two-squares invariant: on `p = 4κ + 1 = a² + b²`, given Gauss's congruence
`C(2κ,κ) ≡ 2a` (the import A3), `⟦w_κ⟧ = −(a²)⁻¹ = (b²)⁻¹`. -/
theorem quarter_wall_invariant (κ a b : ℕ) (hκ : p = 4 * κ + 1) (hab : a ^ 2 + b ^ 2 = p)
    (ha : 0 < a) (hb : 0 < b) (hG : ((centralBinom κ : ℕ) : ZMod p) = 2 * a) :
    wallisW κ = -((a : ZMod p) ^ 2)⁻¹ ∧ -((a : ZMod p) ^ 2)⁻¹ = ((b : ZMod p) ^ 2)⁻¹ := by
  have hp2 : p ≠ 2 := by omega
  have h2 : (2 : ZMod p) ≠ 0 := two_ne_zero_zmod p hp2
  have hκ' : (4 : ZMod p) * κ = -1 := by
    have : ((4 * κ + 1 : ℕ) : ZMod p) = 0 := by rw [← hκ]; exact ZMod.natCast_self p
    push_cast at this
    exact eq_neg_of_add_eq_zero_left this
  have h16 : (16 : ZMod p) ^ κ = 1 := by
    have : (16 : ZMod p) ^ κ = (2 : ZMod p) ^ (p - 1) := by
      rw [show p - 1 = 4 * κ by omega, pow_mul]; norm_num
    rw [this]; exact ZMod.pow_card_sub_one_eq_one h2
  have hab' : (a : ZMod p) ^ 2 + (b : ZMod p) ^ 2 = 0 := by
    have : ((a ^ 2 + b ^ 2 : ℕ) : ZMod p) = 0 := by rw [hab]; exact ZMod.natCast_self p
    push_cast at this; exact this
  have ha2 : a ≤ a ^ 2 := Nat.le_self_pow (by norm_num) a
  have hb2 : 1 ≤ b ^ 2 := Nat.one_le_pow _ _ hb
  have ha' : (a : ZMod p) ≠ 0 := natCast_ne_zero_of_lt p a ha (by omega)
  exact quarter_wall_generic (K := ZMod p) κ a b _ hκ' h2 hG ha' hab' _ h16

/-- Lucas at the first revival and up the tower: `C(2p^{r+1}, p^{r+1}) ≡ C(2p^r, p^r) (mod p)`. -/
theorem choose_two_mul_pow_succ (r : ℕ) :
    ((choose (2 * p ^ (r + 1)) (p ^ (r + 1)) : ℕ) : ZMod p) = ((choose (2 * p ^ r) (p ^ r) : ℕ) : ZMod p) := by
  have hpos : 0 < p := hp.out.pos
  have h := Choose.choose_modEq_choose_mod_mul_choose_div (p := p) (n := 2 * p ^ (r + 1)) (k := p ^ (r + 1))
  have e1 : 2 * p ^ (r + 1) % p = 0 := by rw [pow_succ, ← mul_assoc]; exact Nat.mul_mod_left _ _
  have e2 : p ^ (r + 1) % p = 0 := by rw [pow_succ]; exact Nat.mul_mod_left _ _
  have e3 : 2 * p ^ (r + 1) / p = 2 * p ^ r := by rw [pow_succ, ← mul_assoc]; exact Nat.mul_div_cancel _ hpos
  have e4 : p ^ (r + 1) / p = p ^ r := by rw [pow_succ]; exact Nat.mul_div_cancel _ hpos
  rw [e1, e2, e3, e4, choose_zero_right] at h
  simp only [Nat.cast_one, one_mul] at h
  have := (ZMod.intCast_eq_intCast_iff _ _ p).2 h
  exact_mod_cast this

/-- 13:G5, 13:G9 — Lucas on the tower: `C(2p^r, p^r) ≡ 2 (mod p)` for every `r` (the first revival is `r = 1`). -/
theorem choose_two_mul_pow (r : ℕ) : ((choose (2 * p ^ r) (p ^ r) : ℕ) : ZMod p) = 2 := by
  induction r with
  | zero => norm_num
  | succ r ih => rw [choose_two_mul_pow_succ p r, ih]

/-- 13:G5 — the first revival: `⟦v_p⟧ = 2·16^p/((2p+1)·C(2p,p)²) ≡ 8` on every odd prime shell, by Lucas
(`C(2p,p) ≡ 2`), Fermat (`16^p ≡ 16`) and `2p + 1 ≡ 1`. -/
theorem first_revival (hp2 : p ≠ 2) :
    (2 : ZMod p) * 16 ^ p / (((2 * p + 1 : ℕ) : ZMod p) * ((centralBinom p : ℕ) : ZMod p) ^ 2) = 8 := by
  apply first_revival_generic _ _ _ (two_ne_zero_zmod p hp2)
  · exact ZMod.pow_card 16
  · rw [centralBinom_eq_two_mul_choose]
    have := choose_two_mul_pow p 1
    rwa [pow_one] at this
  · push_cast; rw [ZMod.natCast_self]; ring

/-- 13:G9 — the fixed-shell tower of `π`: for `n = p^r`, `r ≥ 1`, `16^n ≡ 16`, `C(2n,n) ≡ 2` and `2n + 1 ≡ 1`,
so `π̂_{p,r} = (2·16^n + δ)/((2n+1)·C(2n,n)²)` reads `π_A = 2κ` exactly, whenever `δ ≡ −34`. -/
theorem tower_pi_exact (κ : ℕ) (hκ : p = 4 * κ + 1) (r : ℕ) (hr : 1 ≤ r) (δ : ZMod p) (hδ : δ = -34) :
    (2 * (16 : ZMod p) ^ (p ^ r) + δ) /
      (((2 * p ^ r + 1 : ℕ) : ZMod p) * ((centralBinom (p ^ r) : ℕ) : ZMod p) ^ 2) = 2 * κ := by
  have hp2 : p ≠ 2 := by omega
  apply tower_pi_generic _ _ _ _ _ (two_ne_zero_zmod p hp2)
  · exact ZMod.pow_card_pow 16
  · rw [centralBinom_eq_two_mul_choose]; exact choose_two_mul_pow p r
  · push_cast
    rw [ZMod.natCast_self, zero_pow (by omega)]; ring
  · exact hδ
  · have : ((4 * κ + 1 : ℕ) : ZMod p) = 0 := by rw [← hκ]; exact ZMod.natCast_self p
    push_cast at this
    exact eq_neg_of_add_eq_zero_left this

end primepi

/-! ## The Cayley quarter-turn map (13:C3) -/
section cayley

variable {K : Type*} [Field K]

/-- The Cayley quarter-turn map `C(x) = (1 + i x)/(1 − i x)`. -/
noncomputable def cayley (i x : K) : K := (1 + i * x) / (1 - i * x)

/-- 13:C3 — `C(0) = 1` and `C(1) = i` for a quarter turn `i` (`i² = −1`) in characteristic `≠ 2`. -/
theorem cayley_values (i : K) (hi : i * i = -1) (h2 : (2 : K) ≠ 0) :
    cayley i 0 = 1 ∧ cayley i 1 = i := by
  constructor
  · simp [cayley]
  · have h1 : 1 - i * 1 ≠ 0 := by
      intro h; apply h2
      have : i = 1 := by linear_combination -h
      rw [this] at hi; linear_combination hi
    unfold cayley
    rw [div_eq_iff h1]; linear_combination hi

/-- 13:C3 — the composition law `C(x)·C(y) = C((x + y)/(1 − xy))`: the rational law is the half-angle form
of phase composition, with denominators units. -/
theorem cayley_mul (i x y : K) (hi : i * i = -1) (hx : 1 - i * x ≠ 0) (hy : 1 - i * y ≠ 0)
    (hxy : 1 - x * y ≠ 0) :
    cayley i x * cayley i y = cayley i ((x + y) / (1 - x * y)) := by
  have key : (1 - i * x) * (1 - i * y) = (1 - x * y) - i * (x + y) := by linear_combination x * y * hi
  have hden : 1 - i * ((x + y) / (1 - x * y)) ≠ 0 := by
    rw [show 1 - i * ((x + y) / (1 - x * y)) = ((1 - x * y) - i * (x + y)) / (1 - x * y) by
      field_simp]
    rw [← key]
    exact div_ne_zero (mul_ne_zero hx hy) hxy
  unfold cayley
  rw [eq_div_iff hden]
  field_simp
  linear_combination (-2 * i * x * y * (x + y)) * hi

end cayley

/-! ## Angular structure: exact calibration of `e` is impossible (13:H3) -/
section angular

open Real

/-- 13:H3, 13:I1, 13:I3 — `θ = 2πλ/(p−1) ≠ 1` for every label `λ ≥ 1` and every `p`: `θ = 1` would make `π` rational. -/
theorem calibration_ne_one (n l : ℕ) (hl : 0 < l) : 2 * π * l / n ≠ 1 := by
  intro h
  have hn : (n : ℝ) ≠ 0 := by intro hn; rw [hn, div_zero] at h; exact zero_ne_one h
  have hl' : (l : ℝ) ≠ 0 := by exact_mod_cast hl.ne'
  have : π = (n : ℝ) / (2 * l) := by
    field_simp at h ⊢; linarith
  exact irrational_pi.ne_rat ((n : ℚ) / (2 * l)) (by rw [this]; push_cast; ring)

/-- 13:H3 — `e^{i n} ≠ 1` for every `n ≥ 1`: `e^{i}` is not a root of unity (while `χ(e_p)` is one). -/
theorem exp_I_ne_one (n : ℕ) (hn : 0 < n) : Complex.exp (n * Complex.I) ≠ 1 := by
  rw [Ne, Complex.exp_eq_one_iff]
  rintro ⟨k, hk⟩
  have h2 : (n : ℂ) * Complex.I = (k * (2 * π)) * Complex.I := by rw [hk]; ring
  have h1 : (n : ℂ) = k * (2 * π) := mul_right_cancel₀ Complex.I_ne_zero h2
  have h3 : (n : ℝ) = k * (2 * π) := by exact_mod_cast h1
  have hk0 : (k : ℝ) ≠ 0 := by
    intro h0; rw [h0, zero_mul] at h3
    exact (Nat.cast_pos.2 hn).ne' h3
  exact irrational_pi.ne_rat ((n : ℚ) / (2 * k)) (by push_cast; field_simp; linarith)

end angular

/-! ## The null experiment: the index condition (13:H5) -/
section index

/-- 13:H5 — the index condition: `u·l ≡ s (mod n)` is solvable with `u` coprime to `n` exactly when
`gcd(l, n) = gcd(s, n)`. -/
theorem index_condition (n l s : ℕ) [NeZero n] :
    (∃ u : ℕ, u.Coprime n ∧ u * l ≡ s [MOD n]) ↔ Nat.gcd l n = Nat.gcd s n := by
  constructor
  · rintro ⟨u, hu, h⟩
    rw [← Nat.ModEq.gcd_eq h, Nat.Coprime.gcd_mul_left_cancel l hu]
  · intro hg
    obtain ⟨d, hd⟩ : ∃ d, Nat.gcd l n = d := ⟨_, rfl⟩
    have hd0 : 0 < d := hd ▸ Nat.gcd_pos_of_pos_right l (NeZero.pos n)
    obtain ⟨n', hn'⟩ : d ∣ n := hd ▸ Nat.gcd_dvd_right l n
    obtain ⟨l', hl'⟩ : d ∣ l := hd ▸ Nat.gcd_dvd_left l n
    obtain ⟨s', hs'⟩ : d ∣ s := (hd ▸ hg : d = Nat.gcd s n) ▸ Nat.gcd_dvd_left s n
    have hl'c : Nat.Coprime l' n' := by
      have := Nat.coprime_div_gcd_div_gcd (m := l) (n := n) (hd ▸ hd0)
      rw [hd] at this
      rwa [hl', hn', Nat.mul_div_cancel_left _ hd0, Nat.mul_div_cancel_left _ hd0] at this
    have hs'c : Nat.Coprime s' n' := by
      have hg' : Nat.gcd s n = d := hd ▸ hg.symm
      have := Nat.coprime_div_gcd_div_gcd (m := s) (n := n) (hg' ▸ hd0)
      rw [hg'] at this
      rwa [hs', hn', Nat.mul_div_cancel_left _ hd0, Nat.mul_div_cancel_left _ hd0] at this
    have : NeZero n' := ⟨fun h0 => NeZero.ne n (by rw [hn', h0, mul_zero])⟩
    have hdvd : n' ∣ n := ⟨d, by rw [hn', mul_comm]⟩
    let U' : (ZMod n')ˣ := ZMod.unitOfCoprime s' hs'c * (ZMod.unitOfCoprime l' hl'c)⁻¹
    obtain ⟨U, hU⟩ := ZMod.unitsMap_surjective hdvd U'
    refine ⟨(U : ZMod n).val, ZMod.val_coe_unit_coprime U, ?_⟩
    have key : (U : ZMod n).val * l' ≡ s' [MOD n'] := by
      rw [← ZMod.natCast_eq_natCast_iff, Nat.cast_mul, ZMod.natCast_val]
      have hcast : ((U : ZMod n).cast : ZMod n') = (U' : ZMod n') := by
        rw [← ZMod.unitsMap_val hdvd, hU]
      rw [hcast]
      simp only [U', Units.val_mul, ZMod.coe_unitOfCoprime]
      rw [mul_assoc, ← ZMod.coe_unitOfCoprime l' hl'c, Units.inv_mul, mul_one]
    have := Nat.ModEq.mul_left' d key
    rw [← hn'] at this
    rw [hl', hs', mul_left_comm]
    exact this

/-- 13:H5 — for an element `g` of order `n` in a monoid: `(g^u)^l = g^s` for some `u` coprime to `n` — some other
generator of the cycle raised to the label — exactly when `gcd(l, n) = gcd(s, n)`. -/
theorem index_condition_pow {G : Type*} [Monoid G] (g : G) (hfin : IsOfFinOrder g) (n : ℕ) [NeZero n]
    (hn : orderOf g = n) (l s : ℕ) :
    (∃ u : ℕ, u.Coprime n ∧ (g ^ u) ^ l = g ^ s) ↔ Nat.gcd l n = Nat.gcd s n := by
  rw [← index_condition n l s]
  apply exists_congr; intro u
  rw [← pow_mul, hfin.pow_eq_pow_iff_modEq, hn]

/-- 13:H5 — the null experiment's index condition on the shell: for a primitive root `g` of `ZMod p`, the
target `g^s` is `h^l` for some primitive root `h = g^u` (either chirality, `u` coprime to `p − 1`) exactly when
`gcd(l, p−1) = gcd(s, p−1)`. -/
theorem index_condition_shell (p : ℕ) [hp : Fact p.Prime] (g : ZMod p) (hg : IsPrimitiveRoot g (p - 1))
    (l s : ℕ) :
    (∃ u : ℕ, u.Coprime (p - 1) ∧ (g ^ u) ^ l = g ^ s) ↔ Nat.gcd l (p - 1) = Nat.gcd s (p - 1) := by
  have h2 := hp.out.two_le
  have : NeZero (p - 1) := ⟨by omega⟩
  have hfin : IsOfFinOrder g := orderOf_pos_iff.1 (by rw [← hg.eq_orderOf]; omega)
  exact index_condition_pow g hfin (p - 1) hg.eq_orderOf.symm l s

end index


section calibration
open Real

/-- 13:H4, 13:I1 — the best radian-calibrated shell below `10⁶` (Prop. calib): on `p = 778933`, prime, the residue
`123966` is a quarter-turn (`123966² ≡ −1 (mod p)`), and the frame angle `θ = 2π·123966/(p − 1)` it labels lies
within `4·10⁻⁵` of one radian and not within `3.9·10⁻⁵` — the calibration inequality decided from the rational
bounds `3.141592 < π < 3.141593` of Mathlib, no floating-point value of `π` entering; the count of calibrated shells
and the nearest-hit comparison are the package's (`e.A1`). -/
theorem calibrated_778933 :
    Nat.Prime 778933 ∧ (123966 : ZMod 778933) ^ 2 = -1 ∧
      |2 * π * 123966 / 778932 - 1| < 4 / 100000 ∧ 39 / 1000000 < |2 * π * 123966 / 778932 - 1| := by
  have h1 := pi_gt_d6
  have h2 := pi_lt_d6
  refine ⟨by norm_num, by decide, ?_, ?_⟩
  · rw [abs_lt]; constructor <;> nlinarith
  · rw [lt_abs]; right; nlinarith

end calibration


section wallisQ

theorem centralBinom_succ_rat (n : ℕ) :
    ((centralBinom (n + 1) : ℕ) : ℚ) = 2 * (2 * n + 1) * (centralBinom n : ℚ) / (n + 1) := by
  have h := congrArg (fun m : ℕ => (m : ℚ)) (Nat.succ_mul_centralBinom_succ n)
  push_cast at h
  rw [eq_div_iff (by positivity)]
  linear_combination h

theorem centralBinom_pos_rat (n : ℕ) : (0 : ℚ) < (centralBinom n : ℕ) := by
  exact_mod_cast centralBinom_pos n

/-- 13:E2 — the exact width identity `w_n − v_n = w_n/(2n+1)` for `n ≥ 1`. -/
theorem wallis_width (n : ℕ) (hn : 1 ≤ n) :
    wallisW n - wallisV n = (wallisW n : ℚ) / (2 * n + 1) := by
  have hn' : (0 : ℚ) < n := by exact_mod_cast hn
  have hC := centralBinom_pos_rat n
  unfold wallisW wallisV
  field_simp
  ring

/-- 13:E2 — `v_{n+1} = v_n · 4(n+1)²/((2n+3)(2n+1))`. -/
theorem wallisV_succ (n : ℕ) :
    (wallisV (n + 1) : ℚ) = wallisV n * (4 * (n + 1) ^ 2 / ((2 * n + 3) * (2 * n + 1))) := by
  have hC := centralBinom_pos_rat n
  unfold wallisV
  rw [centralBinom_succ_rat]
  push_cast
  field_simp
  ring

theorem wallisV_pos (n : ℕ) : (0 : ℚ) < wallisV n := by
  have hC := centralBinom_pos_rat n
  unfold wallisV; positivity

/-- 13:E2 — the Wallis lower chain `v_n` is strictly increasing. -/
theorem wallisV_strictMono (n : ℕ) : (wallisV n : ℚ) < wallisV (n + 1) := by
  rw [wallisV_succ]
  apply lt_mul_of_one_lt_right (wallisV_pos n)
  rw [one_lt_div (by positivity)]
  nlinarith

/-- 13:E2 — `w_{n+1} = w_n · 4n(n+1)/(2n+1)²`. -/
theorem wallisW_succ (n : ℕ) (hn : 1 ≤ n) :
    (wallisW (n + 1) : ℚ) = wallisW n * (4 * n * (n + 1) / (2 * n + 1) ^ 2) := by
  have hn' : (0 : ℚ) < n := by exact_mod_cast hn
  have hC := centralBinom_pos_rat n
  unfold wallisW
  rw [centralBinom_succ_rat]
  push_cast
  field_simp
  ring

theorem wallisW_pos (n : ℕ) (hn : 1 ≤ n) : (0 : ℚ) < wallisW n := by
  have hn' : (0 : ℚ) < n := by exact_mod_cast hn
  have hC := centralBinom_pos_rat n
  unfold wallisW; positivity

/-- 13:E2 — the Wallis upper chain `w_n` is strictly decreasing from `n = 1`. -/
theorem wallisW_strictAnti (n : ℕ) (hn : 1 ≤ n) : (wallisW (n + 1) : ℚ) < wallisW n := by
  rw [wallisW_succ n hn]
  apply mul_lt_of_lt_one_right (wallisW_pos n hn)
  rw [div_lt_one (by positivity)]
  nlinarith

end wallisQ

section wallisR

open Real

theorem centralBinom_real (n : ℕ) :
    ((centralBinom n : ℕ) : ℝ) = ((2 * n) ! : ℝ) / ((n ! : ℝ) ^ 2) := by
  have h : centralBinom n * n ! * n ! = (2 * n) ! := by
    have := Nat.choose_mul_factorial_mul_factorial (show n ≤ 2 * n by omega)
    rwa [show 2 * n - n = n by omega, ← centralBinom_eq_two_mul_choose] at this
  have h' := congrArg (fun m : ℕ => (m : ℝ)) h
  push_cast at h'
  rw [eq_div_iff (by positivity)]
  linear_combination h'

theorem wallisV_real (n : ℕ) : ((wallisV n : ℚ) : ℝ) = 2 * Real.Wallis.W n := by
  rw [Real.Wallis.W_eq_factorial_ratio]
  unfold wallisV
  push_cast
  rw [centralBinom_real]
  have h1 : (0 : ℝ) < (n ! : ℝ) := by positivity
  have h2 : (0 : ℝ) < ((2 * n) ! : ℝ) := by positivity
  rw [show (16 : ℝ) ^ n = 2 ^ (4 * n) by rw [pow_mul]; norm_num]
  field_simp

theorem wallisW_real (n : ℕ) (hn : 1 ≤ n) :
    ((wallisW n : ℚ) : ℝ) = Real.Wallis.W n * (2 * n + 1) / n := by
  rw [Real.Wallis.W_eq_factorial_ratio]
  unfold wallisW
  push_cast
  rw [centralBinom_real]
  have h1 : (0 : ℝ) < (n ! : ℝ) := by positivity
  have h2 : (0 : ℝ) < ((2 * n) ! : ℝ) := by positivity
  have hn' : (0 : ℝ) < n := by exact_mod_cast hn
  rw [show (16 : ℝ) ^ n = 2 ^ (4 * n) by rw [pow_mul]; norm_num]
  field_simp

/-- 13:E2, 13:I2 — the two-sided enclosure `v_n < π < w_n` for every `n ≥ 1`: the lower chain is the doubled Wallis
partial product `2W_n < 2W_{n+1} ≤ π`, the upper chain is `W_n(2n+1)/n ≥ π(2n+1)²/(4n(n+1)) > π`. -/
theorem wallis_enclosure (n : ℕ) (hn : 1 ≤ n) :
    ((wallisV n : ℚ) : ℝ) < π ∧ π < ((wallisW n : ℚ) : ℝ) := by
  have hn' : (0 : ℝ) < n := by exact_mod_cast hn
  constructor
  · rw [wallisV_real]
    have hs := Real.Wallis.W_succ n
    have hpos := Real.Wallis.W_pos n
    have hlt : Real.Wallis.W n < Real.Wallis.W (n + 1) := by
      rw [hs]
      apply lt_mul_of_one_lt_right hpos
      rw [_root_.div_mul_div_comm, one_lt_div (by positivity)]
      nlinarith
    have := Real.Wallis.W_le (n + 1)
    linarith
  · rw [wallisW_real n hn]
    have hle := Real.Wallis.le_W n
    have hpi := Real.pi_pos
    rw [lt_div_iff₀ hn']
    have key : π * n < ((2 * n + 1) / (2 * n + 2) * (π / 2)) * (2 * n + 1) := by
      rw [_root_.div_mul_div_comm, div_mul_eq_mul_div, lt_div_iff₀ (by positivity)]
      nlinarith
    calc π * n < ((2 * n + 1) / (2 * n + 2) * (π / 2)) * (2 * n + 1) := key
      _ ≤ Real.Wallis.W n * (2 * n + 1) := by
        apply mul_le_mul_of_nonneg_right hle; positivity

end wallisR



/-! ## The Fermat quotient and the π-Wieferich condition (13:G4, 13:G10)

The wall of `π` at second order.  The condition `4^{p−1} ≡ 1 + p (mod p²)` of G4 in its three forms, the exact
identity `q_p(4) = 2q_p(2) + p·q_p(2)²`, Eisenstein's congruence `2q_p(2) ≡ −H_{(p−1)/2}`, G4's second-order
clause from Morley's congruence, and the identification of the set with OEIS A355959, `(p+2)^{p−1} ≡ 1 (mod p²)`.
The ring steps are proved once over any commutative ring with `p² = 0` (section `wieferich`); the sections
`wieferichp` instantiate `ZMod (p²)` and `ZMod p`. -/

/-- The Fermat quotient `q_p(a) = (a^{p−1} − 1)/p` as a natural number. -/
def fq (a p : ℕ) : ℕ := (a ^ (p - 1) - 1) / p

theorem fq_spec {a p : ℕ} (ha : 1 ≤ a) (hdvd : p ∣ a ^ (p - 1) - 1) :
    a ^ (p - 1) = 1 + p * fq a p := by
  unfold fq
  have h1 : 1 ≤ a ^ (p - 1) := Nat.one_le_pow _ _ ha
  rw [Nat.mul_div_cancel' hdvd]; omega

/-- 13:G10 — `q_p(4) = 2 q_p(2) + p q_p(2)²` exactly, from `4^{p−1} = (2^{p−1})²`. -/
theorem fq_four_eq {p : ℕ} (hp : 0 < p) (h2 : p ∣ 2 ^ (p - 1) - 1) :
    fq 4 p = 2 * fq 2 p + p * fq 2 p ^ 2 ∧ p ∣ 4 ^ (p - 1) - 1 := by
  have e2 := fq_spec (a := 2) (by norm_num) h2
  have e4 : 4 ^ (p - 1) = (2 ^ (p - 1)) ^ 2 := by rw [← pow_mul, mul_comm, pow_mul]; norm_num
  have key : 4 ^ (p - 1) - 1 = p * (2 * fq 2 p + p * fq 2 p ^ 2) := by
    rw [e4, e2]; ring_nf; omega
  refine ⟨?_, ⟨_, key⟩⟩
  show (4 ^ (p - 1) - 1) / p = _
  rw [key, Nat.mul_div_cancel_left _ hp]

section wieferich

variable {R : Type*} [CommRing R]

/-- 13:G4 — the second order at the half wall from Morley's congruence, the ring step: with
`x = 4^{p−1} = 1 + p q`, `c² = x²` (`C(p−1,m) ≡ (−1)^m 4^{p−1}`), `2m = p − 1` and `p² = 0`:
`2·x = 2·(−2 + 2p(q − 1))·m·c²`. -/
theorem second_order_generic (p q m c x : R) (hpp : p * p = 0) (hx : x = 1 + p * q) (hc2 : c ^ 2 = x ^ 2)
    (h2m : 2 * m = -1 + p) : 2 * x = 2 * ((-2 + 2 * p * (q - 1)) * (m * c ^ 2)) := by
  rw [hc2]
  subst hx
  linear_combination (-(-2 + 2 * p * (q - 1)) * (1 + p * q) ^ 2) * h2m + (-2 * p ^ 2 * q ^ 3 + 2 * p ^ 2 * q ^ 2 + 2 * p * q ^ 3 - 4 * p * q ^ 2 + 4 * p * q + 2 * q ^ 2 - 2 * q + 2) * hpp

/-- `(1 + p u)^n = 1 + n p u` when `p² = 0`. -/
theorem one_add_mul_pow (p u : R) (hpp : p * p = 0) : ∀ n : ℕ, (1 + p * u) ^ n = 1 + n * (p * u)
  | 0 => by simp
  | n + 1 => by
    rw [pow_succ, one_add_mul_pow p u hpp n]
    push_cast
    linear_combination (n * u * u) * hpp

/-- The OEIS step: `x (1 + n p i) − 1 = p (q − i)` for `x = 1 + p q`, `n = p − 1`, `p² = 0` (with `i = 2⁻¹` in use). -/
theorem oeis_generic (p q i n : R) (hpp : p * p = 0) (hn : n = p - 1) (x : R) (hx : x = 1 + p * q) :
    x * (1 + n * (p * i)) - 1 = p * (q - i) := by
  subst hx hn
  linear_combination (i * (1 + p * q) - q * i) * hpp

theorem sum_range_two_mul {M : Type*} [AddCommMonoid M] (f : ℕ → M) :
    ∀ m, ∑ k ∈ Finset.range (2 * m), f k = ∑ j ∈ Finset.range m, (f (2 * j) + f (2 * j + 1))
  | 0 => rfl
  | m + 1 => by
    rw [Finset.sum_range_succ, ← sum_range_two_mul f m, show 2 * (m + 1) = 2 * m + 1 + 1 by ring,
      Finset.sum_range_succ, Finset.sum_range_succ, add_assoc]

end wieferich

section wieferichK

variable {K : Type*} [Field K]

/-- `H_{p−1} = Σ_{k<p−1} (k+1)⁻¹ = 0` over a field with `p = 0` and `2 ≠ 0` (the terms pair off as `k ↔ p − k`). -/
theorem harmonic_generic (p : ℕ) (hp0 : (p : K) = 0) (h1 : 1 ≤ p) (h2 : (2 : K) ≠ 0) :
    ∑ k ∈ Finset.range (p - 1), ((k + 1 : ℕ) : K)⁻¹ = 0 := by
  have hr := Finset.sum_range_reflect (fun k => ((k + 1 : ℕ) : K)⁻¹) (p - 1)
  have hterm : ∀ k ∈ Finset.range (p - 1), ((p - 1 - 1 - k + 1 : ℕ) : K)⁻¹ = -((k + 1 : ℕ) : K)⁻¹ := by
    intro k hk
    have := Finset.mem_range.1 hk
    rw [show p - 1 - 1 - k + 1 = p - 1 - k by omega, natCast_pred_sub p hp0 h1 k (by omega), inv_neg, Nat.cast_add,
      Nat.cast_one]
  rw [Finset.sum_congr rfl hterm, Finset.sum_neg_distrib] at hr
  have : (2 : K) * ∑ k ∈ Finset.range (p - 1), ((k + 1 : ℕ) : K)⁻¹ = 0 := by linear_combination -hr
  exact (mul_eq_zero.1 this).resolve_left h2

/-- Eisenstein's congruence, the field step: from `a = Σ_{k<2m} (−1)^k (k+1)⁻¹` and `H_{2m} = 0`, `a = −H_m`
(the alternating sum over `[1, 2m]` is `H_{2m} − H_m`). -/
theorem eisenstein_generic (m : ℕ) (a : K) (h2 : (2 : K) ≠ 0)
    (hH : ∑ k ∈ Finset.range (2 * m), ((k + 1 : ℕ) : K)⁻¹ = 0)
    (hc : a = ∑ k ∈ Finset.range (2 * m), (-1) ^ k * ((k + 1 : ℕ) : K)⁻¹) :
    a = -∑ j ∈ Finset.range m, ((j + 1 : ℕ) : K)⁻¹ := by
  rw [sum_range_two_mul] at hc hH
  have key : ∀ j ∈ Finset.range m,
      ((-1) ^ (2 * j) * ((2 * j + 1 : ℕ) : K)⁻¹ + (-1) ^ (2 * j + 1) * ((2 * j + 1 + 1 : ℕ) : K)⁻¹) =
      (((2 * j + 1 : ℕ) : K)⁻¹ + ((2 * j + 1 + 1 : ℕ) : K)⁻¹) - ((j + 1 : ℕ) : K)⁻¹ := by
    intro j hj
    have e : ((2 * j + 1 + 1 : ℕ) : K)⁻¹ = 2⁻¹ * ((j + 1 : ℕ) : K)⁻¹ := by
      rw [show 2 * j + 1 + 1 = 2 * (j + 1) by ring, Nat.cast_mul, mul_inv, Nat.cast_ofNat]
    rw [pow_mul, neg_one_sq, one_pow, one_mul, pow_succ, pow_mul, neg_one_sq, one_pow, one_mul, e]
    have := mul_inv_cancel₀ h2
    linear_combination (-((j + 1 : ℕ) : K)⁻¹) * this
  rw [Finset.sum_congr rfl key, Finset.sum_sub_distrib, hH, zero_sub] at hc
  exact hc

end wieferichK


/-! ### On the shell lifted to `p²`: the three forms, the half wall at second order, Eisenstein, OEIS -/
section wieferichp

variable (p : ℕ) [hp : Fact p.Prime]

/-- Fermat: `p ∣ 2^{p−1} − 1` for every odd prime. -/
theorem two_pow_pred_dvd (hp2 : p ≠ 2) : p ∣ 2 ^ (p - 1) - 1 := by
  rw [← ZMod.natCast_eq_zero_iff, Nat.cast_sub (Nat.one_le_two_pow), Nat.cast_pow, Nat.cast_ofNat, Nat.cast_one]
  rw [ZMod.pow_card_sub_one_eq_one (two_ne_zero_zmod p hp2), sub_self]

omit hp in
theorem p_sq_eq_zero : ((p : ZMod (p ^ 2)) * p) = 0 := by
  rw [← Nat.cast_mul, ← pow_two, ZMod.natCast_self]

theorem p_mul_natCast_eq_zero_iff (a : ℕ) : ((p : ZMod (p ^ 2)) * a) = 0 ↔ (a : ZMod p) = 0 := by
  rw [← Nat.cast_mul, ZMod.natCast_eq_zero_iff, ZMod.natCast_eq_zero_iff, pow_two,
    Nat.mul_dvd_mul_iff_left hp.out.pos]

theorem p_mul_intCast_eq_zero_iff (a : ℤ) : ((p : ZMod (p ^ 2)) * a) = 0 ↔ (a : ZMod p) = 0 := by
  have : ((p : ZMod (p ^ 2)) * a) = ((p * a : ℤ) : ZMod (p ^ 2)) := by push_cast; ring
  rw [this, ZMod.intCast_zmod_eq_zero_iff_dvd, ZMod.intCast_zmod_eq_zero_iff_dvd, pow_two, Nat.cast_mul,
    Int.mul_dvd_mul_iff_left (by exact_mod_cast hp.out.ne_zero)]

/-- 13:G10 — `4^{p−1} = 1 + p·q_p(4)` in `ZMod (p²)`, and `q_p(4) = 2q_p(2) + p·q_p(2)²`. -/
theorem four_pow_pred (hp2 : p ≠ 2) :
    (4 : ZMod (p ^ 2)) ^ (p - 1) = 1 + p * fq 4 p ∧ fq 4 p = 2 * fq 2 p + p * fq 2 p ^ 2 := by
  obtain ⟨e, h4⟩ := fq_four_eq hp.out.pos (two_pow_pred_dvd p hp2)
  refine ⟨?_, e⟩
  have := congrArg (Nat.cast : ℕ → ZMod (p ^ 2)) (fq_spec (a := 4) (by norm_num) h4)
  push_cast at this
  exact this

/-- 13:G10 — the π-Wieferich condition in its three forms: `4^{p−1} ≡ 1 + p (mod p²)` ⟺
`q_p(4) ≡ 1 (mod p)` ⟺ `2·q_p(2) ≡ 1 (mod p)` — a prescribed value of the Fermat quotient of `2`. -/
theorem piWieferich_iff (hp2 : p ≠ 2) :
    ((4 : ZMod (p ^ 2)) ^ (p - 1) = 1 + p ↔ (fq 4 p : ZMod p) = 1) ∧
    ((fq 4 p : ZMod p) = 1 ↔ (2 * fq 2 p : ZMod p) = 1) := by
  obtain ⟨h4, e⟩ := four_pow_pred p hp2
  constructor
  · rw [h4]
    have key : (1 : ZMod (p ^ 2)) + p * fq 4 p = 1 + p ↔ (p : ZMod (p ^ 2)) * (((fq 4 p : ℤ) - 1 : ℤ) : ZMod (p ^ 2)) = 0 := by
      push_cast
      constructor
      · intro h; linear_combination h
      · intro h; linear_combination h
    rw [key, p_mul_intCast_eq_zero_iff]
    push_cast
    exact sub_eq_zero
  · rw [e]; push_cast; rw [ZMod.natCast_self]; simp

/-- 13:G4, 13:I2, 13:J6 — the second order at the half wall: with `m = (p−1)/2` and Morley's congruence
`C(p−1, m) ≡ (−1)^m 4^{p−1}` taken modulo `p²` (the import A3), `16^m ≡ (−2 + 2p(q_p(4) − 1))·m·C(2m,m)²
(mod p²)`, i.e. `w_m ≡ −2 + 2p(q_p(4) − 1)`; the universal `−2` persists to `p²` exactly when `q_p(4) ≡ 1`,
the π-Wieferich condition. -/
theorem half_wall_second_order (hp2 : p ≠ 2) (m : ℕ) (hm : p = 2 * m + 1)
    (hM : ((centralBinom m : ℕ) : ZMod (p ^ 2)) = (-1) ^ m * 4 ^ (p - 1)) :
    (2 : ZMod (p ^ 2)) * 16 ^ m =
      2 * ((-2 + 2 * p * ((fq 4 p : ZMod (p ^ 2)) - 1)) * (m * ((centralBinom m : ℕ) : ZMod (p ^ 2)) ^ 2)) ∧
    ((2 : ZMod (p ^ 2)) * 16 ^ m = 2 * (-2 * (m * ((centralBinom m : ℕ) : ZMod (p ^ 2)) ^ 2)) ↔
      (fq 4 p : ZMod p) = 1) := by
  obtain ⟨h4, _⟩ := four_pow_pred p hp2
  have h16 : (16 : ZMod (p ^ 2)) ^ m = 4 ^ (p - 1) := by
    rw [show p - 1 = 2 * m by omega, pow_mul]; norm_num
  have hc2 : (((centralBinom m : ℕ) : ZMod (p ^ 2))) ^ 2 = ((4 : ZMod (p ^ 2)) ^ (p - 1)) ^ 2 := by
    rw [hM, mul_pow, ← pow_mul, mul_comm m 2, pow_mul, neg_one_sq, one_pow, one_mul]
  have h2m : (2 : ZMod (p ^ 2)) * m = -1 + p := by
    have : ((2 * m + 1 : ℕ) : ZMod (p ^ 2)) = p := by rw [← hm]
    push_cast at this
    linear_combination this
  have key := second_order_generic (p : ZMod (p ^ 2)) (fq 4 p) m _ _ (p_sq_eq_zero p) h4 hc2 h2m
  rw [h16]
  refine ⟨key, ?_⟩
  rw [key]
  have hm1 : 1 ≤ m := by have := hp.out.two_le; omega
  have hcop4 : Nat.Coprime 4 p := by
    rw [Nat.coprime_comm, hp.out.coprime_iff_not_dvd]
    intro h
    exact hp2 ((Nat.prime_dvd_prime_iff_eq hp.out Nat.prime_two).1 (hp.out.dvd_of_dvd_pow (show p ∣ 2 ^ 2 by norm_num; exact h)))
  have hcopm : Nat.Coprime m p := by
    rw [Nat.coprime_comm, hp.out.coprime_iff_not_dvd]
    exact Nat.not_dvd_of_pos_of_lt hm1 (by omega)
  have hcopC : Nat.Coprime (centralBinom m) p := by
    rw [Nat.coprime_comm, hp.out.coprime_iff_not_dvd]
    intro hdvd
    have hfac : centralBinom m * m ! * m ! = (2 * m) ! := by
      have := Nat.choose_mul_factorial_mul_factorial (show m ≤ 2 * m by omega)
      rwa [show 2 * m - m = m by omega, ← centralBinom_eq_two_mul_choose] at this
    have : p ∣ (2 * m) ! := hfac ▸ Dvd.dvd.mul_right (Dvd.dvd.mul_right hdvd _) _
    have := (hp.out.dvd_factorial).1 this
    omega
  have hu4 : IsUnit ((4 : ℕ) : ZMod (p ^ 2)) := (ZMod.isUnit_iff_coprime 4 (p ^ 2)).2 (hcop4.pow_right 2)
  have hum : IsUnit ((m : ℕ) : ZMod (p ^ 2)) := (ZMod.isUnit_iff_coprime m (p ^ 2)).2 (hcopm.pow_right 2)
  have huC : IsUnit ((centralBinom m : ℕ) : ZMod (p ^ 2)) :=
    (ZMod.isUnit_iff_coprime _ (p ^ 2)).2 (hcopC.pow_right 2)
  have hunit : IsUnit (((4 : ℕ) : ZMod (p ^ 2)) * (m * ((centralBinom m : ℕ) : ZMod (p ^ 2)) ^ 2)) :=
    hu4.mul (hum.mul (huC.pow 2))
  have hiff := p_mul_intCast_eq_zero_iff p ((fq 4 p : ℤ) - 1)
  push_cast at hiff
  rw [sub_eq_zero] at hiff
  constructor
  · intro h
    have h0 : ((p : ZMod (p ^ 2)) * ((fq 4 p : ZMod (p ^ 2)) - 1)) *
        (((4 : ℕ) : ZMod (p ^ 2)) * (m * ((centralBinom m : ℕ) : ZMod (p ^ 2)) ^ 2)) = 0 := by
      push_cast; linear_combination h
    exact hiff.1 ((hunit.mul_left_eq_zero).1 h0)
  · intro h
    have h0 := hiff.2 h
    linear_combination (4 * (m * ((centralBinom m : ℕ) : ZMod (p ^ 2)) ^ 2)) * h0

/-- `C(p−1, k) ≡ (−1)^k (mod p)`. -/
theorem choose_pred_zmod (k : ℕ) (hk : k ≤ p - 1) : ((choose (p - 1) k : ℕ) : ZMod p) = (-1) ^ k :=
  choose_pred_eq_neg_one_pow (K := ZMod p) p (ZMod.natCast_self p) hp.out.one_le
    (fun j hj0 hj => natCast_ne_zero_of_lt p j hj0 (by omega)) k hk

/-- The lift: `a ≡ b (mod p)` gives `p·a = p·b` in `ZMod (p²)`. -/
theorem p_mul_congr (a b : ℤ) (h : (a : ZMod p) = b) : (p : ZMod (p ^ 2)) * a = p * b := by
  have := (p_mul_intCast_eq_zero_iff p (a - b)).2 (by push_cast; rw [h, sub_self])
  push_cast at this; linear_combination this

/-- `C(p, k+1)·(k+1) = p·(−1)^k` in `ZMod (p²)` for `k + 1 ≤ p − 1`. -/
theorem choose_succ_mul_eq (k : ℕ) (hk : k + 1 ≤ p - 1) :
    ((choose p (k + 1) : ℕ) : ZMod (p ^ 2)) * ((k + 1 : ℕ) : ZMod (p ^ 2)) = p * (-1) ^ k := by
  have h := Nat.add_one_mul_choose_eq (p - 1) k
  rw [Nat.sub_add_cancel hp.out.one_le] at h
  have hc := choose_pred_zmod p k (by omega)
  have hl := p_mul_congr p (choose (p - 1) k : ℕ) ((-1) ^ k) (by push_cast; exact hc)
  push_cast at hl
  have := congrArg (fun m : ℕ => (m : ZMod (p ^ 2))) h
  push_cast at this ⊢
  rw [← this, hl]

theorem coprime_succ_sq (k : ℕ) (hk : k + 1 ≤ p - 1) : Nat.Coprime (k + 1) (p ^ 2) := by
  apply Nat.Coprime.pow_right
  rw [Nat.coprime_comm, hp.out.coprime_iff_not_dvd]
  exact Nat.not_dvd_of_pos_of_lt (by omega) (by omega)

/-- `C(p, k+1) = p·(−1)^k·(k+1)⁻¹` in `ZMod (p²)`. -/
theorem choose_succ_eq (k : ℕ) (hk : k + 1 ≤ p - 1) :
    ((choose p (k + 1) : ℕ) : ZMod (p ^ 2)) = p * (-1) ^ k * ((k + 1 : ℕ) : ZMod (p ^ 2))⁻¹ := by
  have hu := ZMod.coe_mul_inv_eq_one (k + 1) (coprime_succ_sq p k hk)
  have h := choose_succ_mul_eq p k hk
  calc ((choose p (k + 1) : ℕ) : ZMod (p ^ 2))
      = ((choose p (k + 1) : ℕ) : ZMod (p ^ 2)) * (((k + 1 : ℕ) : ZMod (p ^ 2)) * ((k + 1 : ℕ) : ZMod (p ^ 2))⁻¹) := by
        rw [hu, mul_one]
    _ = p * (-1) ^ k * ((k + 1 : ℕ) : ZMod (p ^ 2))⁻¹ := by rw [← mul_assoc, h]

/-- `2^p − 2 = p · Σ_{k<p−1} (−1)^k (k+1)⁻¹` in `ZMod (p²)`. -/
theorem two_pow_sub_two (hp2 : p ≠ 2) :
    (2 : ZMod (p ^ 2)) * p * fq 2 p = p * ∑ k ∈ Finset.range (p - 1), (-1) ^ k * ((k + 1 : ℕ) : ZMod (p ^ 2))⁻¹ := by
  have hsum := Nat.sum_range_choose p
  have h1 : p + 1 = (p - 1) + 1 + 1 := by have := hp.out.one_le; omega
  rw [h1, Finset.sum_range_succ, Finset.sum_range_succ', show p - 1 + 1 = p by have := hp.out.one_le; omega,
    choose_self, choose_zero_right] at hsum
  have hc := congrArg (fun m : ℕ => (m : ZMod (p ^ 2))) hsum
  push_cast at hc
  have hq := congrArg (fun m : ℕ => (m : ZMod (p ^ 2))) (fq_spec (a := 2) (by norm_num) (two_pow_pred_dvd p hp2))
  push_cast at hq
  have h2p : (2 : ZMod (p ^ 2)) ^ p = 2 * 2 ^ (p - 1) := by
    have := pow_succ' (2 : ZMod (p ^ 2)) (p - 1)
    rwa [Nat.sub_add_cancel hp.out.one_le] at this
  rw [Finset.mul_sum]
  have hterm : ∀ k ∈ Finset.range (p - 1), ((choose p (k + 1) : ℕ) : ZMod (p ^ 2)) =
      (p : ZMod (p ^ 2)) * ((-1) ^ k * ((k + 1 : ℕ) : ZMod (p ^ 2))⁻¹) := by
    intro k hk
    have := Finset.mem_range.1 hk
    rw [choose_succ_eq p k (by omega), mul_assoc]
  rw [Finset.sum_congr rfl hterm] at hc
  linear_combination -hc - 2 * hq - h2p

/-- `p·x = 0` in `ZMod (p²)` exactly when `x` reduces to `0` in `ZMod p`. -/
theorem p_mul_eq_zero_iff_cast (x : ZMod (p ^ 2)) :
    (p : ZMod (p ^ 2)) * x = 0 ↔ ((x.cast : ZMod p) = 0) := by
  conv_lhs => rw [← ZMod.natCast_zmod_val x]
  rw [p_mul_natCast_eq_zero_iff, ZMod.natCast_val]

theorem cast_inv_succ (k : ℕ) (hk : k + 1 ≤ p - 1) :
    ((((k + 1 : ℕ) : ZMod (p ^ 2))⁻¹).cast : ZMod p) = ((k + 1 : ℕ) : ZMod p)⁻¹ := by
  have hu := ZMod.coe_mul_inv_eq_one (k + 1) (coprime_succ_sq p k hk)
  have hdvd : p ∣ p ^ 2 := dvd_pow_self p two_ne_zero
  have := congrArg (ZMod.castHom hdvd (ZMod p)) hu
  rw [map_mul, map_one, ZMod.castHom_apply, ZMod.castHom_apply, ZMod.cast_natCast hdvd] at this
  exact eq_inv_of_mul_eq_one_right this

/-- `H_{p−1} = Σ_{k<p−1} (k+1)⁻¹ = 0` in `ZMod p`. -/
theorem harmonic_pred_eq_zero (hp2 : p ≠ 2) : ∑ k ∈ Finset.range (p - 1), ((k + 1 : ℕ) : ZMod p)⁻¹ = 0 :=
  harmonic_generic p (ZMod.natCast_self p) hp.out.one_le (two_ne_zero_zmod p hp2)

/-- `p·x = p·y` in `ZMod (p²)` exactly when `x` and `y` agree in `ZMod p`. -/
theorem p_mul_eq_iff_cast (x y : ZMod (p ^ 2)) :
    (p : ZMod (p ^ 2)) * x = (p : ZMod (p ^ 2)) * y ↔ (x.cast : ZMod p) = y.cast := by
  have hdvd : p ∣ p ^ 2 := dvd_pow_self p two_ne_zero
  have e : ((x - y).cast : ZMod p) = x.cast - y.cast := ZMod.cast_sub hdvd x y
  constructor
  · intro h
    have h0 := (p_mul_eq_zero_iff_cast p (x - y)).1 (by rw [mul_sub, h, sub_self])
    rw [e] at h0
    exact sub_eq_zero.1 h0
  · intro h
    have h0 : ((x - y).cast : ZMod p) = 0 := by rw [e, h]; exact sub_self _
    have := (p_mul_eq_zero_iff_cast p (x - y)).2 h0
    rw [mul_sub, sub_eq_zero] at this
    exact this

/-- 13:G10 — Eisenstein's congruence: `2 q_p(2) ≡ −H_{(p−1)/2} (mod p)`, `H_m = Σ_{j<m} (j+1)⁻¹`. -/
theorem eisenstein (m : ℕ) (hm : p = 2 * m + 1) :
    (2 * fq 2 p : ZMod p) = -∑ j ∈ Finset.range m, ((j + 1 : ℕ) : ZMod p)⁻¹ := by
  have hp2 : p ≠ 2 := by omega
  have hdvd : p ∣ p ^ 2 := dvd_pow_self p two_ne_zero
  have h := two_pow_sub_two p hp2
  have h0 : (p : ZMod (p ^ 2)) * ((2 * fq 2 p : ℕ) : ZMod (p ^ 2)) =
      p * ∑ k ∈ Finset.range (p - 1), (-1) ^ k * ((k + 1 : ℕ) : ZMod (p ^ 2))⁻¹ := by
    rw [Nat.cast_mul, Nat.cast_ofNat]; linear_combination h
  have hc := (p_mul_eq_iff_cast p ((2 * fq 2 p : ℕ) : ZMod (p ^ 2)) _).1 h0
  rw [← ZMod.castHom_apply (h := hdvd), ← ZMod.castHom_apply (h := hdvd), map_natCast, map_sum] at hc
  have hterm : ∀ k ∈ Finset.range (p - 1), ZMod.castHom hdvd (ZMod p) ((-1) ^ k * ((k + 1 : ℕ) : ZMod (p ^ 2))⁻¹) =
      (-1) ^ k * ((k + 1 : ℕ) : ZMod p)⁻¹ := by
    intro k hk
    have := Finset.mem_range.1 hk
    rw [map_mul, map_pow, map_neg, map_one, ZMod.castHom_apply, cast_inv_succ p k (by omega)]
  rw [Finset.sum_congr rfl hterm] at hc
  have hH := harmonic_pred_eq_zero p hp2
  rw [show p - 1 = 2 * m by omega] at hc hH
  have key := eisenstein_generic (K := ZMod p) m _ (two_ne_zero_zmod p hp2) hH hc
  exact_mod_cast key

/-- 13:G10 — the π-Wieferich condition in harmonic form: `4^{p−1} ≡ 1 + p (mod p²)` exactly when
`H_{(p−1)/2} = Σ_{j=1}^{(p−1)/2} 1/j ≡ −1 (mod p)`. -/
theorem piWieferich_iff_harmonic (m : ℕ) (hm : p = 2 * m + 1) :
    (4 : ZMod (p ^ 2)) ^ (p - 1) = 1 + p ↔ ∑ j ∈ Finset.range m, ((j + 1 : ℕ) : ZMod p)⁻¹ = -1 := by
  have hp2 : p ≠ 2 := by omega
  obtain ⟨h1, h2⟩ := piWieferich_iff p hp2
  rw [h1, h2, eisenstein p m hm]
  exact neg_eq_iff_eq_neg

/-- 13:G10 — the π-Wieferich set is OEIS A355959: `(p + 2)^{p−1} ≡ 1 (mod p²)` exactly when
`2 q_p(2) ≡ 1 (mod p)`, i.e. exactly when `4^{p−1} ≡ 1 + p (mod p²)`. -/
theorem piWieferich_iff_oeis (hp2 : p ≠ 2) :
    ((p : ZMod (p ^ 2)) + 2) ^ (p - 1) = 1 ↔ (2 * fq 2 p : ZMod p) = 1 := by
  have hcop : Nat.Coprime 2 (p ^ 2) := by
    apply Nat.Coprime.pow_right
    rw [Nat.coprime_comm, hp.out.coprime_iff_not_dvd]
    intro h; exact hp2 ((Nat.prime_dvd_prime_iff_eq hp.out Nat.prime_two).1 h)
  have h2i := ZMod.coe_mul_inv_eq_one 2 hcop
  set i : ZMod (p ^ 2) := ((2 : ℕ) : ZMod (p ^ 2))⁻¹ with hi
  have h2i' : (2 : ZMod (p ^ 2)) * i = 1 := by rw [hi]; exact_mod_cast h2i
  have hu2 : IsUnit (2 : ZMod (p ^ 2)) := ⟨⟨2, i, h2i', by rw [mul_comm]; exact h2i'⟩, rfl⟩
  have hq := congrArg (Nat.cast : ℕ → ZMod (p ^ 2)) (fq_spec (a := 2) (by norm_num) (two_pow_pred_dvd p hp2))
  push_cast at hq
  have hfac : ((p : ZMod (p ^ 2)) + 2) = 2 * (1 + p * i) := by linear_combination (-(p : ZMod (p ^ 2))) * h2i'
  have hn : ((p - 1 : ℕ) : ZMod (p ^ 2)) = p - 1 := by rw [Nat.cast_sub hp.out.one_le, Nat.cast_one]
  have key : ((p : ZMod (p ^ 2)) + 2) ^ (p - 1) - 1 = p * ((fq 2 p : ZMod (p ^ 2)) - i) := by
    rw [hfac, mul_pow, one_add_mul_pow _ _ (p_sq_eq_zero p), hn]
    exact oeis_generic (p : ZMod (p ^ 2)) (fq 2 p) i _ (p_sq_eq_zero p) rfl _ hq
  have hiff := p_mul_intCast_eq_zero_iff p (2 * (fq 2 p : ℤ) - 1)
  push_cast at hiff
  rw [sub_eq_zero] at hiff
  rw [← sub_eq_zero, key, ← hiff]
  constructor
  · intro h
    have : (2 : ZMod (p ^ 2)) * ((p : ZMod (p ^ 2)) * ((fq 2 p : ZMod (p ^ 2)) - i)) = 0 := by rw [h, mul_zero]
    linear_combination this + (p : ZMod (p ^ 2)) * h2i'
  · intro h
    have h' : (2 : ZMod (p ^ 2)) * ((p : ZMod (p ^ 2)) * ((fq 2 p : ZMod (p ^ 2)) - i)) = 0 := by
      linear_combination h - (p : ZMod (p ^ 2)) * h2i'
    exact (hu2.mul_right_eq_zero).1 h'

end wieferichp

-- Ledger predicates of 13-epi (generated by make_predicates.py from docs/13-epi/13-epi-ledger.json; edit the ledger, not this section)
set_option linter.defProp false in
/-- 13:C2 (p13013) — The derangement selector: the registration statistics are generated by the rencontres polynomial $P_n(X)=n!\sum_{k\le n}(X-1)^{k}/k!$ (an exact double-counting identity), the normalised kernel $Z_n$ has $Z_n(1)=1$, $Z_n(0)=\dr{n}/n!$, and the unit registration ratio $R_n=n!/\dr{n}$ is forced; relative to the declared completion of $Z_n$ to $e^{X-1}$ the external value of the chain is uniquely $\eR$. -/
def p13013 := And.intro @FRC.Epi.rencontres (And.intro @FRC.Epi.rencontres_rat (And.intro @FRC.Epi.rencontres_one (@FRC.Epi.rencontres_zero)))
/-- 13:C3 (p13014) — The Cayley quarter-turn map $C(x)=(1+\im x)/(1-\im x)$ on $\Fp$ (denominators units): $C(0)=1$, $C(1)=\im$, and $C(x)C(y)=C\bigl((x+y)/(1-xy)\bigr)$, the rational composition law being the half-angle form of phase composition; shell arithmetic only. -/
theorem p13014 : (∀ {K : Type u_1} [Field K] (i : K), i * i = (-1 : K) → (2 : K) ≠ (0 : K) → FRC.Epi.cayley i (0 : K) = (1 : K) ∧ FRC.Epi.cayley i (1 : K) = i) ∧ ∀ {K : Type u_2} [Field K] (i x y : K), i * i = (-1 : K) → (1 : K) - i * x ≠ (0 : K) → (1 : K) - i * y ≠ (0 : K) → (1 : K) - x * y ≠ (0 : K) → FRC.Epi.cayley i x * FRC.Epi.cayley i y = FRC.Epi.cayley i ((x + y) / ((1 : K) - x * y)) :=
  And.intro @FRC.Epi.cayley_values (@FRC.Epi.cayley_mul)
set_option linter.defProp false in
/-- 13:C5 (p13016) — The joint-return tally: with $C_n=\Cb{n}$ the returning $\pm1$ histories of length $2n$ in one direction, the paired histories in the directions $1$ and $\im$ number $16^{n}$ and the joint returns $C_n^{2}$, and $\piR=\lim16^{n}/(nC_n^{2})$ by the Wallis bounds (E2). -/
def p13016 := And.intro @FRC.Epi.joint_return_tally (@FRC.Epi.tendsto_wallis_chain)
/-- 13:D2 (p13018) — The tail form: $\dr{n}=n!/\eR+(-1)^{n}\delta_n$ with $\delta_n\in(1/(n+2),1/(n+1))$, so $\dr{n}$ is the nearest integer to $n!/\eR$. -/
theorem p13018 : (∀ (n : ℕ), (1 : ℝ) / (↑n + (2 : ℝ)) < FRC.Epi.tailDelta n ∧ FRC.Epi.tailDelta n < (1 : ℝ) / (↑n + (1 : ℝ))) ∧ ∀ (n : ℕ), ↑(numDerangements n) = ↑n.factorial * Real.exp (-1 : ℝ) + (-1 : ℝ) ^ n * FRC.Epi.tailDelta n :=
  And.intro @FRC.Epi.tailDelta_strict (@FRC.Epi.numDerangements_eq_tailDelta)
/-- 13:D3 (p13019) — Superexponential enclosure: $|\varepsilon_n-\eR|\le\eR(\eR+1)/(n+1)!<10.2/(n+1)!$ with $\operatorname{sign}(\varepsilon_n-\eR)=(-1)^{n+1}$, hence $\varepsilon_{2m}<\eR<\varepsilon_{2m+1}$, a nested sequence of $\fQ$-native intervals; the sharper constant $8$ for $2\le n\le60$. -/
theorem p13019 : (∀ (n : ℕ), (2 : ℕ) ≤ n → |FRC.Epi.epsChain n - Real.exp (1 : ℝ)| ≤ Real.exp (1 : ℝ) * (Real.exp (1 : ℝ) + (1 : ℝ)) / ↑(n + (1 : ℕ)).factorial ∧ Real.exp (1 : ℝ) * (Real.exp (1 : ℝ) + (1 : ℝ)) / ↑(n + (1 : ℕ)).factorial < 10.2 / ↑(n + (1 : ℕ)).factorial) ∧ ∀ (n : ℕ), (2 : ℕ) ≤ n → (0 : ℝ) < (-1 : ℝ) ^ (n + (1 : ℕ)) * (FRC.Epi.epsChain n - Real.exp (1 : ℝ)) :=
  And.intro @FRC.Epi.epsChain_enclosure (@FRC.Epi.epsChain_sign)
/-- 13:D4 (p13020) — Horizon determination of the readout: $\ro(\varepsilon_n)=\ro(\eR)$ for $n\ge n_0(k)=\Theta(k/\log k)$; the binary64 constant for $e$ is the readout of $\varepsilon_{18}=18!/\dr{18}=6402373705728000/2355301661033953$ and $n=18$ is minimal ($\varepsilon_{17}$ fails readout equality, $|\varepsilon_{17}-\eR|=1.10\times10^{-15}$ above the half-ulp); the first $100$ significant digits of $\eR$ are those of $\varepsilon_{70}$; every floating-point value of $e$ is a plateau readout. -/
theorem p13020 : |Real.exp (1 : ℝ) - FRC.Epi.binary64E| < (1 : ℝ) / (2 : ℝ) ^ (52 : ℕ) ∧ |FRC.Epi.epsChain (18 : ℕ) - FRC.Epi.binary64E| < (1 : ℝ) / (2 : ℝ) ^ (52 : ℕ) ∧ ∀ (n : ℕ), (2 : ℕ) ≤ n → n ≤ (17 : ℕ) → (1 : ℝ) / (2 : ℝ) ^ (52 : ℕ) < |FRC.Epi.epsChain n - FRC.Epi.binary64E| :=
  @FRC.Epi.readout_binary64
/-- 13:D5 (p13021) — Feasibility selection: the compound chain $(1+1/n)^{n}$ costs $n\asymp2^{k}$ steps for $k$ bits against $n_0(k)=\Theta(k/\log k)$ for the derangement chain ($n=11,18,70$ at $k=24,53,333$); within a horizon $H$ the compound chain realises $O(\log H)$ bits and the factorial chain $\Theta(H\log H)$; under the feasibility principle the derangement representation is the canonical finite definition of $e$. -/
theorem p13021 : (((8 : ℚ) / ↑(Nat.factorial (12 : ℕ)) < (1 : ℚ) / (2 : ℚ) ^ (24 : ℕ) ∧ ∀ m < (11 : ℕ), ¬(8 : ℚ) / ↑(m + (1 : ℕ)).factorial < (1 : ℚ) / (2 : ℚ) ^ (24 : ℕ)) ∧ ((8 : ℚ) / ↑(Nat.factorial (19 : ℕ)) < (1 : ℚ) / (2 : ℚ) ^ (53 : ℕ) ∧ ∀ m < (18 : ℕ), ¬(8 : ℚ) / ↑(m + (1 : ℕ)).factorial < (1 : ℚ) / (2 : ℚ) ^ (53 : ℕ)) ∧ (8 : ℚ) / ↑(Nat.factorial (71 : ℕ)) < (1 : ℚ) / (2 : ℚ) ^ (333 : ℕ) ∧ ∀ m < (70 : ℕ), ¬(8 : ℚ) / ↑(m + (1 : ℕ)).factorial < (1 : ℚ) / (2 : ℚ) ^ (333 : ℕ)) ∧ ∀ (n : ℕ), (5 : ℕ) ≤ n → ((1 : ℝ) + (1 : ℝ) / ↑n) ^ n ≤ Real.exp (1 : ℝ) * ((4 : ℝ) * ↑n) / ((4 : ℝ) * ↑n + (1 : ℝ)) :=
  And.intro @FRC.Epi.derangement_cost (@FRC.Epi.compound_cost)
/-- 13:E2 (p13023) — Two-sided monotone enclosure: $v_n$ strictly increasing, $w_n$ strictly decreasing, $v_n<\piR<w_n$, and the exact width identity $w_n-v_n=w_n/(2n+1)$, certifying $\approx\log_2n$ bits by nested $\fQ$-intervals; the identification of the common limit with $\piR$ is the Wallis import (A6); verified for $n\le300$ against Machin brackets of width below $10^{-420}$. -/
theorem p13023 : And (∀ (n : Nat), @LE.le Nat instLENat (@OfNat.ofNat Nat (nat_lit 1) (instOfNatNat (nat_lit 1))) n → And (@LT.lt Real Real.instLT (@Rat.cast Real Real.instRatCast (@FRC.Epi.wallisV Rat Rat.instField n)) Real.pi) (@LT.lt Real Real.instLT Real.pi (@Rat.cast Real Real.instRatCast (@FRC.Epi.wallisW Rat Rat.instField n)))) (And (∀ (n : Nat), @LE.le Nat instLENat (@OfNat.ofNat Nat (nat_lit 1) (instOfNatNat (nat_lit 1))) n → @Eq Rat (@HSub.hSub Rat Rat Rat (@instHSub Rat Rat.instSub) (@FRC.Epi.wallisW Rat Rat.instField n) (@FRC.Epi.wallisV Rat Rat.instField n)) (@HDiv.hDiv Rat Rat Rat (@instHDiv Rat Rat.instDiv) (@FRC.Epi.wallisW Rat Rat.instField n) (@HAdd.hAdd Rat Rat Rat (@instHAdd Rat Rat.instAdd) (@HMul.hMul Rat Rat Rat (@instHMul Rat Rat.instMul) (@OfNat.ofNat Rat (nat_lit 2) (@Rat.instOfNat (nat_lit 2))) (@Nat.cast Rat Rat.instNatCast n)) (@OfNat.ofNat Rat (nat_lit 1) (@Rat.instOfNat (nat_lit 1)))))) (And (∀ (n : Nat), @LT.lt Rat Rat.instLT (@FRC.Epi.wallisV Rat Rat.instField n) (@FRC.Epi.wallisV Rat Rat.instField (@HAdd.hAdd Nat Nat Nat (@instHAdd Nat instAddNat) n (@OfNat.ofNat Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))) (∀ (n : Nat), @LE.le Nat instLENat (@OfNat.ofNat Nat (nat_lit 1) (instOfNatNat (nat_lit 1))) n → @LT.lt Rat Rat.instLT (@FRC.Epi.wallisW Rat Rat.instField (@HAdd.hAdd Nat Nat Nat (@instHAdd Nat instAddNat) n (@OfNat.ofNat Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))) (@FRC.Epi.wallisW Rat Rat.instField n)))) :=
  And.intro @FRC.Epi.wallis_enclosure (And.intro @FRC.Epi.wallis_width (And.intro @FRC.Epi.wallisV_strictMono (@FRC.Epi.wallisW_strictAnti)))
/-- 13:F1 (p13027) — Wilson reflection: for an odd prime $\p$ and $0\le k\le\p-1$, $1/k!\equiv-(-1)^{k}(\p-1-k)!\pmod\p$. -/
theorem p13027 : ∀ (p : ℕ) [hp : Fact (Nat.Prime p)], ∀ k ≤ p - (1 : ℕ), (↑k.factorial)⁻¹ = -(-1 : ZMod p) ^ k * ↑(p - (1 : ℕ) - k).factorial :=
  @FRC.Epi.wilson_reflection_zmod
set_option linter.defProp false in
/-- 13:F2 (p13028) — The wall identity and the terminal residue of $e$: $\dr{(\p-1)}\equiv\Ku{\p}\pmod\p$ (the odd-prime case of the Mijajlovi\'c--\v Sami congruence, A4), hence $\rep{\varepsilon_{\p-1}}=-(\Ku{\p})^{-1}$ whenever $\p\nmid\Ku{\p}$; existence of the terminal link on a shell is equivalent to $\p\nmid\Ku{\p}$, universal existence over the shells of the totality to the vanishing of Kurepa's certificate (Z1); re-verified in the derangement form for all $121{,}126$ odd primes $\p<1.6\times10^{6}$ with zero failures of either condition. Beyond the wall $n!\equiv0$: $n=\p-1$ is the factorial horizon. -/
def p13028 := And.intro @FRC.Epi.derangements_wall_zmod (@FRC.Epi.terminal_residue)
set_option linter.defProp false in
/-- 13:F3 (p13029) — Antiperiodicity: $\dr{(n+\p)}\equiv-\dr{n}\pmod\p$ for every odd prime $\p$ and every $n\ge0$ of the totality, so $\dr{n}\bmod\p$ depends on $n\bmod2\p$; the blind set $Z_0(\p)=\{n<\p:\dr{n}\equiv0\}$ always contains $1$, and Kurepa's hypothesis is $\p-1\notin Z_0(\p)$ for every odd prime $\p$ of the totality. -/
def p13029 := @FRC.Epi.derangements_antiperiodic_zmod
set_option linter.defProp false in
/-- 13:F4 (p13030) — Series duals at the wall: $\sum_{k<\p}(-1)^{k}/k!\equiv-\Ku{\p}$ and $\sum_{k<\p}1/k!\equiv-A(\p)$, $A(\p)$ the alternating factorial sum; the group law $\exp(1)\exp(-1)=1$ does not survive, $\Ku{\p}A(\p)\equiv3,0,21,28,132,258$ at $\p=7,13,29,101,257,1009$; on $\p=13$ the direct series residue vanishes ($A(13)\equiv0$) while the derangement side survives ($\Ku{13}\equiv10$) --- a second ground for the canonicity of D5. -/
def p13030 := @FRC.Epi.series_duals_zmod
/-- 13:F7 (p13033) — The fixed-shell tower of $e$: with $\delta_m=\ctr{(-1)^{m}\eP}$ and $q_m=((m\p)!+\delta_m)/\dr{(m\p)}$, $\rep{q_m}=\eP$ exactly at every grade (since $(m\p)!\equiv0$ and $\dr{(m\p)}\equiv(-1)^{m}$ by F3) while $q_m\to\eR$ with the certificate $|q_m-\eR|<(m\p)!/(\dr{(m\p)}\dr{(m\p+1)})+2\kap/\dr{(m\p)}$; on $\p=13$, $q_2$ differs from $\eR$ by $3.98\times10^{-26}$ and every member reads $6$. Compatibility, not selection. -/
theorem p13033 : ∀ (p : ℕ) [hp : Fact (Nat.Prime p)], p ≠ (2 : ℕ) → ∀ (m : ℕ), (1 : ℕ) ≤ m → ∀ (e δ : ZMod p), δ = (-1 : ZMod p) ^ m * e → ↑(m * p).factorial = (0 : ZMod p) ∧ ↑(numDerangements (m * p)) = (-1 : ZMod p) ^ m ∧ (↑(m * p).factorial + δ) / ↑(numDerangements (m * p)) = e :=
  @FRC.Epi.tower_e_exact_zmod
set_option linter.defProp false in
/-- 13:F8 (p13066) — The tail identity: $j!\,\dr{(\p-1-j)}\equiv(-1)^{j}\bigl(\Ku{\p}-\Ku{j}\bigr)\pmod\p$ for $0\le j\le\p-1$ ($j=0$ is F2); hence $n\in Z_0(\p)$ iff $\Ku{(\p-1-n)}\equiv\Ku{\p}$: the blind set counts the collisions of the partial sums of the left factorial with their total, $n=1$ is the forced collision $\Ku{(\p-2)}\equiv\Ku{\p}$, and Kurepa's hypothesis is the return-to-origin question of the walk with steps $j!$. -/
def p13066 := And.intro @FRC.Epi.tail_identity_zmod (@FRC.Epi.blind_iff_collision)
/-- 13:G1 (p13034) — The legibility window: with $m=(\p-1)/2$, $\p\nmid\Cb{n}$ for $1\le n\le m$ and $\p\mid\Cb{n}$ for $m<n<\p$ (Kummer, A3): the residue line of the Wallis chain is defined on exactly $[1,m]$, blind-free below the wall and totally blind on $(m,\p)$; on a frame shell the last legible scale $n=2\kap$ is the angular address of $-1$. -/
theorem p13034 : ∀ (p : ℕ) [hp : Fact (Nat.Prime p)] (n : ℕ), ((2 : ℕ) * n ≤ p - (1 : ℕ) → ¬p ∣ n.centralBinom) ∧ (p ≤ (2 : ℕ) * n → n < p → p ∣ n.centralBinom) :=
  @FRC.Epi.legibility_window
/-- 13:G2 (p13035) — The half-wall terminus, the calibration face: $\rep{w_m}=m^{-1}=\piA^{-1}=4\piA\equiv-2$ for every odd prime of the totality, the return statistics trivialising at the wall ($16^{m}\equiv1$, $\Cb{m}^{2}\equiv1$) and exposing the naked inverse scale; the identities are the calibration web of $2\piA\equiv-1$, and $\rep{w_{\piA}}\piA\equiv1\iff(4\kap)^{2}\equiv1$; the lower chain is blind at the wall and nowhere below. -/
theorem p13035 : ∀ (p : ℕ) [hp : Fact (Nat.Prime p)], p ≠ (2 : ℕ) → ∀ (m : ℕ), p = (2 : ℕ) * m + (1 : ℕ) → (16 : ZMod p) ^ m = (1 : ZMod p) ∧ ↑m.centralBinom ^ (2 : ℕ) = (1 : ZMod p) ∧ FRC.Epi.wallisW m = (-2 : ZMod p) ∧ (↑m)⁻¹ = (-2 : ZMod p) ∧ (4 : ZMod p) * ↑m = (-2 : ZMod p) :=
  @FRC.Epi.half_wall_terminus
set_option linter.defProp false in
/-- 13:G3 (p13036) — The quarter-wall two-squares invariant: for $\p\equiv1\pmod4$, $\p=a^{2}+b^{2}$ with $a$ odd, $a\equiv1\pmod4$, at the quarter scale $n=\kap$ (the address of $\im$) $\rep{w_\kap}=\kap^{-1}(2a)^{-2}=-(a^{2})^{-1}=(b^{2})^{-1}$, by Gauss's congruence (A3) with $\kap\equiv-4^{-1}$; the invariant exists precisely under the frame condition; verified for all $211$ primes $\p\equiv1\pmod4$ below $3000$. -/
def p13036 := @FRC.Epi.quarter_wall_invariant
/-- 13:G4 (p13037) — Second order at the half wall: $w_m\equiv-2+2\p(q_\p(4)-1)\pmod{\p^{2}}$ with $q_\p(4)\equiv2q_\p(2)$, exact to $\p^{3}$ through Morley (A3); the universal $-2$ persists to $\p^{2}$ exactly for the $\pi$-Wieferich primes $4^{\p-1}\equiv1+\p\pmod{\p^{2}}$ (OEIS A355959, G10), which are exactly $5$ and $45827$ below $1.08\times10^{11}$ \cite{oeisA355959}, re-verified here to $2^{35}$ (\src{pi\_wieferich128}; $45827\equiv3\pmod4$, so $\p=5$ is the only Subject shell among them; two below $10^{6}$ against the range frequency $\sum_{\p<10^{6}}1/\p\approx2.4$); the normalised quotients equidistribute empirically \apx. -/
theorem p13037 : ∀ (p : ℕ) [hp : Fact (Nat.Prime p)], p ≠ (2 : ℕ) → ∀ (m : ℕ), p = (2 : ℕ) * m + (1 : ℕ) → ↑m.centralBinom = (-1 : ZMod (p ^ (2 : ℕ))) ^ m * (4 : ZMod (p ^ (2 : ℕ))) ^ (p - (1 : ℕ)) → (2 : ZMod (p ^ (2 : ℕ))) * (16 : ZMod (p ^ (2 : ℕ))) ^ m = (2 : ZMod (p ^ (2 : ℕ))) * (((-2 : ZMod (p ^ (2 : ℕ))) + (2 : ZMod (p ^ (2 : ℕ))) * ↑p * (↑(FRC.Epi.fq (4 : ℕ) p) - (1 : ZMod (p ^ (2 : ℕ))))) * (↑m * ↑m.centralBinom ^ (2 : ℕ))) ∧ ((2 : ZMod (p ^ (2 : ℕ))) * (16 : ZMod (p ^ (2 : ℕ))) ^ m = (2 : ZMod (p ^ (2 : ℕ))) * ((-2 : ZMod (p ^ (2 : ℕ))) * (↑m * ↑m.centralBinom ^ (2 : ℕ))) ↔ ↑(FRC.Epi.fq (4 : ℕ) p) = (1 : ZMod p)) :=
  @FRC.Epi.half_wall_second_order
/-- 13:G5 (p13038) — Lucas revivals and self-similarity: beyond the wall $n\ge\p$ is legible for $w$ precisely when every base-$\p$ digit of $n$ is at most $m$ and $\p\nmid n$ (on $\p=13$ the two-digit revivals number $(2\kap)^{2}=36$); on revival scales $\Cb{n}$ factorises digitwise (Lucas, A3); at the first revival $\rep{v_\p}\equiv8$ universally and $v_\p\equiv8+16\p(2q_\p(2)-1)\pmod{\p^{2}}$ by Wolstenholme. -/
theorem p13038 : (∀ (p : ℕ) [hp : Fact (Nat.Prime p)], p ≠ (2 : ℕ) → (2 : ZMod p) * (16 : ZMod p) ^ p / (↑((2 : ℕ) * p + (1 : ℕ)) * ↑p.centralBinom ^ (2 : ℕ)) = (8 : ZMod p)) ∧ ∀ (p : ℕ) [hp : Fact (Nat.Prime p)] (r : ℕ), ↑(((2 : ℕ) * p ^ r).choose (p ^ r)) = (2 : ZMod p) :=
  And.intro @FRC.Epi.first_revival (@FRC.Epi.choose_two_mul_pow)
/-- 13:G9 (p13042) — The fixed-shell tower of $\pi$: for $n=\p^{r}$, with $\delta_\p=\ctr{\piA B_n-A_n}=\ctr{-34}$, the member $\widehat\pi_{\p,r}=(2\cdot16^{\p^{r}}+\delta_\p)/((2\p^{r}+1)\Cb{\p^{r}}^{2})$ reads $\rep{\widehat\pi_{\p,r}}=\piA$ exactly for every $r$ (Lucas and Fermat give $\Cb{n}\equiv2$, $16^{n}\equiv16$, $B_n\equiv4$) while converging externally to $\piR$; on $\p=13$, $\delta_{13}=5$. -/
theorem p13042 : (∀ (p : ℕ) [hp : Fact (Nat.Prime p)] (κ : ℕ), p = (4 : ℕ) * κ + (1 : ℕ) → ∀ (r : ℕ), (1 : ℕ) ≤ r → ∀ (δ : ZMod p), δ = (-34 : ZMod p) → ((2 : ZMod p) * (16 : ZMod p) ^ p ^ r + δ) / (↑((2 : ℕ) * p ^ r + (1 : ℕ)) * ↑(p ^ r).centralBinom ^ (2 : ℕ)) = (2 : ZMod p) * ↑κ) ∧ ∀ (p : ℕ) [hp : Fact (Nat.Prime p)] (r : ℕ), ↑(((2 : ℕ) * p ^ r).choose (p ^ r)) = (2 : ZMod p) :=
  And.intro @FRC.Epi.tower_pi_exact (@FRC.Epi.choose_two_mul_pow)
/-- 13:G10 (p13067) — The $\pi$-Wieferich condition in three forms: $4^{\p-1}\equiv1+\p\pmod{\p^{2}}$ iff $q_\p(4)\equiv1$ iff $2q_\p(2)\equiv1\pmod\p$, with $q_\p(4)=2q_\p(2)+\p\,q_\p(2)^{2}$ exactly; Eisenstein's $2q_\p(2)\equiv-H_{(\p-1)/2}\pmod\p$ ($H_m=\sum_{j\le m}1/j$) makes it $H_{(\p-1)/2}\equiv-1$, and $(\p+2)^{\p-1}\equiv1\pmod{\p^{2}}$ identifies it with OEIS A355959 \cite{oeisA355959}. -/
theorem p13067 : (∀ (p : ℕ) [hp : Fact (Nat.Prime p)], p ≠ (2 : ℕ) → ((4 : ZMod (p ^ (2 : ℕ))) ^ (p - (1 : ℕ)) = (1 : ZMod (p ^ (2 : ℕ))) + ↑p ↔ ↑(FRC.Epi.fq (4 : ℕ) p) = (1 : ZMod p)) ∧ (↑(FRC.Epi.fq (4 : ℕ) p) = (1 : ZMod p) ↔ (2 : ZMod p) * ↑(FRC.Epi.fq (2 : ℕ) p) = (1 : ZMod p))) ∧ (∀ (p : ℕ) [hp : Fact (Nat.Prime p)] (m : ℕ), p = (2 : ℕ) * m + (1 : ℕ) → (2 : ZMod p) * ↑(FRC.Epi.fq (2 : ℕ) p) = -∑ j ∈ Finset.range m, (↑(j + (1 : ℕ)))⁻¹) ∧ (∀ (p : ℕ) [hp : Fact (Nat.Prime p)] (m : ℕ), p = (2 : ℕ) * m + (1 : ℕ) → ((4 : ZMod (p ^ (2 : ℕ))) ^ (p - (1 : ℕ)) = (1 : ZMod (p ^ (2 : ℕ))) + ↑p ↔ ∑ j ∈ Finset.range m, (↑(j + (1 : ℕ)))⁻¹ = (-1 : ZMod p))) ∧ ∀ (p : ℕ) [hp : Fact (Nat.Prime p)], p ≠ (2 : ℕ) → ((↑p + (2 : ZMod (p ^ (2 : ℕ)))) ^ (p - (1 : ℕ)) = (1 : ZMod (p ^ (2 : ℕ))) ↔ (2 : ZMod p) * ↑(FRC.Epi.fq (2 : ℕ) p) = (1 : ZMod p)) :=
  And.intro @FRC.Epi.piWieferich_iff (And.intro @FRC.Epi.eisenstein (And.intro @FRC.Epi.piWieferich_iff_harmonic (@FRC.Epi.piWieferich_iff_oeis)))
/-- 13:H3 (p13045) — Exact calibration of $e$ is impossible: with $\theta=2\piR\lambda(\im)/(\p-1)$ the frame angle of $\eP$, $\theta\ne1$ in every shell ($\theta=1$ would make $\piR$ rational, A2); $\chi(\eP)$ is a root of unity while $e^{\imR}$ is not, so the identification is intrinsically horizon-limited. -/
theorem p13045 : (∀ (n l : ℕ), (0 : ℕ) < l → (2 : ℝ) * Real.pi * ↑l / ↑n ≠ (1 : ℝ)) ∧ ∀ (n : ℕ), (0 : ℕ) < n → Complex.exp (↑n * Complex.I) ≠ (1 : ℂ) :=
  And.intro @FRC.Epi.calibration_ne_one (@FRC.Epi.exp_I_ne_one)
/-- 13:H4 (p13069) — Calibrated shells at every precision the totality resolves: the $\varepsilon$-calibrated shells are a fraction $2\varepsilon/\piR$ \apx{} of the shells $\p\equiv1\pmod4$ below any bound of the totality, for every $\varepsilon$ above the nearest-hit scale $\piR/(2N)$, and $\chi(\eP)$ approaches $e^{\imR}$ along them. Below $10^{6}$: $260$ shells within $0.01$ against $249$ predicted; the best, $\p=778933$, within $4\times10^{-5}$, decided exactly. -/
theorem p13069 : Nat.Prime (778933 : ℕ) ∧ (123966 : ZMod (778933 : ℕ)) ^ (2 : ℕ) = (-1 : ZMod (778933 : ℕ)) ∧ |(2 : ℝ) * Real.pi * (123966 : ℝ) / (778932 : ℝ) - (1 : ℝ)| < (4 / 100000 : ℝ) ∧ (39 / 1000000 : ℝ) < |(2 : ℝ) * Real.pi * (123966 : ℝ) / (778932 : ℝ) - (1 : ℝ)| :=
  @FRC.Epi.calibrated_778933
/-- 13:H5 (p13047) — The null experiment: whether $\gen^{\lambda(\im)}\equiv-(\Ku{\p})^{-1}$ for some primitive root of either chirality is the index condition $\gcd(s,\p-1)=\gcd(\lambda(\pm\im),\p-1)$; over the $210$ primes $\p\equiv1\pmod4$, $5<\p<3000$, it is solvable for $94$ ($44.8\%$, against $96.0\pm6.6$ expected under independence), the correlation of the two angular addresses $-0.10$ at deviation $\approx0.07$ \apx: no invariant pointwise identification of the angular and radial carriers of $e$; the naive reading of $\eP$ as the number $2.71828\ldots$ is refuted. -/
theorem p13047 : (∀ (p : ℕ) [hp : Fact (Nat.Prime p)] (g : ZMod p), IsPrimitiveRoot g (p - (1 : ℕ)) → ∀ (l s : ℕ), (∃ u, u.Coprime (p - (1 : ℕ)) ∧ (g ^ u) ^ l = g ^ s) ↔ l.gcd (p - (1 : ℕ)) = s.gcd (p - (1 : ℕ))) ∧ ∀ (n l s : ℕ) [NeZero n], (∃ u, u.Coprime n ∧ u * l ≡ s [MOD n]) ↔ l.gcd n = s.gcd n :=
  And.intro @FRC.Epi.index_condition_shell (@FRC.Epi.index_condition)
-- end ledger predicates

end FRC.Epi
