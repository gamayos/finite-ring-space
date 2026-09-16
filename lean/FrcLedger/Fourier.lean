import Mathlib

/-!
# 6-fourier — the shell Fourier operator: rows B5/B7 for every shell (2026-09-15)

The shell Fourier matrix `W k j = g^(jk)` on `V = 𝔽_p^{Z_{p−1}}`, `g` a primitive root,
the reversal `J`, and the normalised operator `F = i W` with `i = −g^κ` (`i² = −1`).
Claims (6-fourier rows B5, B7; master C2 transform layer):
  `W² = −J`, `F² = J`, `F⁴ = I`, `W J = J W`.
The paper's witness checks these on six shells; here they are proved for every prime `p`
with `p = 4κ + 1` and every primitive root `g`.
-/

namespace FRC.Fourier

open Matrix Finset

variable {K : Type*} [Field K] {n : ℕ} [NeZero n]

/-- The geometric sum of an `n`-th root of unity `ζ ≠ 1` over `Fin n` vanishes. -/
lemma sum_pow_eq_zero_of_ne_one {ζ : K} (hζn : ζ ^ n = 1) (hζ : ζ ≠ 1) :
    ∑ j : Fin n, ζ ^ (j : ℕ) = 0 := by
  have h := geom_sum_mul ζ n
  rw [hζn, sub_self] at h
  rw [Fin.sum_univ_eq_sum_range (fun j => ζ ^ j) n]
  exact (mul_eq_zero.1 h).resolve_right (sub_ne_zero.2 hζ)

/-- The shell Fourier matrix, `W k j = g^(j·k)`. -/
def W (g : K) : Matrix (Fin n) (Fin n) K := fun k j => g ^ ((j : ℕ) * (k : ℕ))

/-- The reversal `J k l = [l = −k]`. -/
def J : Matrix (Fin n) (Fin n) K := fun k l => if l = -k then 1 else 0

lemma W_apply (g : K) (k j : Fin n) : (W g : Matrix (Fin n) (Fin n) K) k j = g ^ ((j : ℕ) * (k : ℕ)) := rfl
lemma J_apply (k l : Fin n) : (J : Matrix (Fin n) (Fin n) K) k l = if l = -k then 1 else 0 := rfl

/-- `g^((-j).val) = (g^(j.val))⁻¹` for an `n`-th root of unity `g`. -/
lemma pow_neg_val {g : K} (hg : g ^ n = 1) (j : Fin n) :
    g ^ ((-j : Fin n) : ℕ) = (g ^ (j : ℕ))⁻¹ := by
  have hne : g ≠ 0 := by rintro rfl; simp [NeZero.ne n] at hg
  apply eq_inv_of_mul_eq_one_left
  rw [← pow_add]
  have hdvd : n ∣ ((-j : Fin n) : ℕ) + (j : ℕ) := by
    have h : (-j : Fin n) + j = 0 := neg_add_cancel j
    have := congrArg Fin.val h
    rw [Fin.val_add, Fin.val_zero] at this
    exact Nat.dvd_of_mod_eq_zero this
  obtain ⟨c, hc⟩ := hdvd
  rw [hc, pow_mul, hg, one_pow]

/-- `J² = 1`. -/
theorem J_sq : (J : Matrix (Fin n) (Fin n) K) ^ 2 = 1 := by
  ext k l
  rw [sq, Matrix.mul_apply, Matrix.one_apply]
  simp only [J_apply, mul_ite, mul_one, mul_zero]
  rw [Finset.sum_eq_single (-k)]
  · simp [neg_neg, eq_comm]
  · intro x _ hx; simp [hx]
  · intro h; exact absurd (Finset.mem_univ _) h

/-- `W² = n • J` for any primitive `n`-th root of unity `g` (the general identity). -/
theorem W_sq (g : K) (hg : IsPrimitiveRoot g n) :
    (W g : Matrix (Fin n) (Fin n) K) ^ 2 = (n : K) • J := by
  ext k l
  rw [sq, Matrix.mul_apply, Matrix.smul_apply, J_apply]
  simp only [W_apply]
  have hrw : ∀ j : Fin n, g ^ ((j : ℕ) * (k : ℕ)) * g ^ ((l : ℕ) * (j : ℕ))
      = (g ^ ((k : ℕ) + (l : ℕ))) ^ (j : ℕ) := by
    intro j; rw [← pow_add, ← pow_mul]; congr 1; ring
  simp_rw [hrw]
  have hdvd_iff : n ∣ (k : ℕ) + (l : ℕ) ↔ l = -k := by
    constructor
    · intro hd
      rw [eq_neg_iff_add_eq_zero, add_comm]
      apply Fin.ext
      rw [Fin.val_add, Fin.val_zero]
      exact Nat.mod_eq_zero_of_dvd hd
    · intro hl
      have h : k + l = 0 := by rw [hl, add_neg_cancel]
      have := congrArg Fin.val h
      rw [Fin.val_add, Fin.val_zero] at this
      exact Nat.dvd_of_mod_eq_zero this
  by_cases hkl : l = -k
  · obtain ⟨c, hc⟩ := hdvd_iff.2 hkl
    rw [hc, pow_mul, hg.pow_eq_one, one_pow]
    simp [hkl]
  · have hne : g ^ ((k : ℕ) + (l : ℕ)) ≠ 1 := by
      intro h1
      exact hkl (hdvd_iff.1 (hg.dvd_of_pow_eq_one _ h1))
    have hpow : (g ^ ((k : ℕ) + (l : ℕ))) ^ n = 1 := by
      rw [← pow_mul, mul_comm, pow_mul, hg.pow_eq_one, one_pow]
    rw [sum_pow_eq_zero_of_ne_one hpow hne]
    simp [hkl]

/-- `W J = J W` for any `n`-th root of unity `g`. -/
theorem W_mul_J_comm (g : K) (hg : g ^ n = 1) :
    (W g : Matrix (Fin n) (Fin n) K) * J = J * W g := by
  ext k l
  rw [Matrix.mul_apply, Matrix.mul_apply]
  simp only [W_apply, J_apply, mul_ite, ite_mul, mul_one, mul_zero, one_mul, zero_mul]
  rw [Finset.sum_eq_single (-l), Finset.sum_eq_single (-k)]
  · simp only [neg_neg, ite_true]
    -- g^((-l)·k) = g^(l·(-k))
    have hl : (g ^ (l : ℕ)) ^ n = 1 := by rw [← pow_mul, mul_comm, pow_mul, hg, one_pow]
    rw [pow_mul, pow_mul, pow_neg_val hg l, inv_pow, pow_neg_val hl k]
  · intro x _ hx; simp [hx]
  · intro h; exact absurd (Finset.mem_univ _) h
  · intro x _ hx
    have : l ≠ -x := fun h => hx (by rw [h, neg_neg])
    simp [this]
  · intro h; exact absurd (Finset.mem_univ _) h

/-! ## The shell: a field with `p = 4κ + 1` elements, `g` a primitive root, `i = −g^κ` -/

section shell

variable {F : Type*} [Field F] [Fintype F]

/-- `(card F − 1 : ℕ) = −1` in a finite field `F`. -/
lemma natCast_card_pred_eq_neg_one : ((Fintype.card F - 1 : ℕ) : F) = -1 := by
  have h2 : 1 ≤ Fintype.card F := Fintype.card_pos
  rw [Nat.cast_sub h2, FiniteField.cast_card_eq_zero, Nat.cast_one, zero_sub]

/-- The quarter-turn `i = −g^κ` squares to `−1` (`g^{2κ}` is a primitive square root of unity). -/
lemma quarter_turn_sq (κ : ℕ) (hκ : Fintype.card F = 4 * κ + 1) (g : F)
    (hg : IsPrimitiveRoot g (Fintype.card F - 1)) :
    (-(g ^ κ)) ^ 2 = -1 := by
  have hκ' : Fintype.card F - 1 = 4 * κ := by omega
  have hκpos : κ ≠ 0 := by
    intro h; subst h; have := Fintype.one_lt_card (α := F); omega
  have hsq : (-(g ^ κ)) ^ 2 = g ^ (2 * κ) := by ring
  rw [hsq]
  have h2 : IsPrimitiveRoot (g ^ (2 * κ)) 2 := by
    have hd : 2 * κ ∣ Fintype.card F - 1 := by rw [hκ']; exact ⟨2, by ring⟩
    have := hg.pow_of_dvd (show 2 * κ ≠ 0 by omega) hd
    have hq : (Fintype.card F - 1) / (2 * κ) = 2 := by
      rw [hκ', show 4 * κ = 2 * κ * 2 by ring]; exact Nat.mul_div_cancel_left _ (by omega)
    rwa [hq] at this
  exact h2.eq_neg_one_of_two_right

/-- 6:B5, 6:B7 — every shell: on a field with `p = 4κ + 1` elements, `n = p − 1`,
`g` a primitive root and `F = i • W`: `W² = −J`, `F² = J`, `F⁴ = 1`, `W J = J W`. -/
theorem shell_relations (κ : ℕ) (hκ : Fintype.card F = 4 * κ + 1) (g : F)
    (hg : IsPrimitiveRoot g (Fintype.card F - 1)) :
    haveI : NeZero (Fintype.card F - 1) := ⟨by have := Fintype.one_lt_card (α := F); omega⟩
    (W g : Matrix (Fin (Fintype.card F - 1)) (Fin (Fintype.card F - 1)) F) ^ 2 = -J ∧
    ((-(g ^ κ)) • W g : Matrix (Fin (Fintype.card F - 1)) (Fin (Fintype.card F - 1)) F) ^ 2 = J ∧
    ((-(g ^ κ)) • W g : Matrix (Fin (Fintype.card F - 1)) (Fin (Fintype.card F - 1)) F) ^ 4 = 1 ∧
    (W g : Matrix (Fin (Fintype.card F - 1)) (Fin (Fintype.card F - 1)) F) * J = J * W g := by
  haveI : NeZero (Fintype.card F - 1) := ⟨by have := Fintype.one_lt_card (α := F); omega⟩
  have hW : (W g : Matrix (Fin (Fintype.card F - 1)) (Fin (Fintype.card F - 1)) F) ^ 2 = -J := by
    rw [W_sq g hg, natCast_card_pred_eq_neg_one, neg_one_smul]
  have hi := quarter_turn_sq κ hκ g hg
  have hF : ((-(g ^ κ)) • W g : Matrix (Fin (Fintype.card F - 1)) (Fin (Fintype.card F - 1)) F) ^ 2
      = J := by
    rw [smul_pow, hW, hi, neg_one_smul, neg_neg]
  refine ⟨hW, hF, ?_, W_mul_J_comm g hg.pow_eq_one⟩
  rw [show (4 : ℕ) = 2 * 2 by norm_num, pow_mul, hF, J_sq]

/-- 6:B5, 6:B7 on the prime shell `𝔽_p = ZMod p`, an instance: the relations hold there for every prime
`p = 4κ + 1` and primitive root `g`. -/
theorem shell_relations_zmod (p κ : ℕ) [hp : Fact (Nat.Prime p)] (hκ : p = 4 * κ + 1)
    (g : ZMod p) (hg : IsPrimitiveRoot g (p - 1)) :
    haveI : NeZero (Fintype.card (ZMod p) - 1) :=
      ⟨by have := Fintype.one_lt_card (α := ZMod p); omega⟩
    ((-(g ^ κ)) • W g : Matrix (Fin (Fintype.card (ZMod p) - 1))
      (Fin (Fintype.card (ZMod p) - 1)) (ZMod p)) ^ 2 = J := by
  have hc : Fintype.card (ZMod p) = p := ZMod.card p
  exact (shell_relations κ (by rw [hc, hκ]) g (by rw [hc]; exact hg)).2.1

end shell

end FRC.Fourier
