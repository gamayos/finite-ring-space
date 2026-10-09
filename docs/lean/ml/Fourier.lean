import Mathlib
import FrcLedger.Theme.Fourier
import FrcLedger.Theme.Fractional
import FrcLedger.Keys.Fourier

/-!
# 6-fourier — the shell Fourier operator and its fractional family, for every shell (2026-09-15, extended 2026-09-17)

The shell Fourier matrix `W k j = g^(jk)` on `V = 𝔽_p^{Z_{p−1}}`, `g` a primitive root, the reversal `J`, and the
normalised operator `F = i W` with `i = −g^κ` (`i² = −1`): `W² = −J`, `F² = J`, `F⁴ = I`, `W J = J W` (predicates B5, B7).
The fractional family of the paper — the projectors `Π_ℓ = ¼ Σ_r i^{−ℓr} F^r`, the family `F^{[s]} = Σ_ℓ g^{−ℓs} Π_ℓ`
on `ZMod (4κ)` with its additivity, cardinal values, faithfulness and character sector (C2–C4, C8, C9, E6), the
multiplicities as traces and ranks with their parity sums and the dichotomy from the Gauss sign (C5, C7), the
parity permutation (D2), the rotation group `SO(2, 𝔽_p) ≃ 𝔽_p^×` with its cardinal values and eigenline (E2, E3),
the spectral obstruction (E5) and the shift–modulation covariance (E7) — proved for every prime shell `p = 4κ + 1`
and every primitive root, and where the algebra allows, for any element `f` with `f⁴ = 1` of any algebra over a
field with a quarter-turn. The paper's witness checks these on six shells. Classical (tier 2) on Mathlib's
hierarchy; predicates B2, B3, B5–B7 are also in the core with no axioms.

Since the ledger migration (task LM36, 7 October 2026) the theorems live in the fourier theme: the shell DFT in
`FrcLedger/Theme/Fourier.lean` (`FRC.DFT`, task LM17) and the fractional family in `FrcLedger/Theme/Fractional.lean`
(`FRC.Fractional`). The old names below are aliases, and the predicate declarations are the aliases of their keys.
-/

namespace FRC.Fourier

/-! ## Old names (ledger migration, task LM17): the declarations moved to the themes, each under its old name -/

section base_aliases
variable {K : Type*} [Field K] {n : ℕ} [NeZero n]

omit [NeZero n] in
/-- The geometric sum of an `n`-th root of unity `ζ ≠ 1` over `Fin n` vanishes. -/
lemma sum_pow_eq_zero_of_ne_one {ζ : K} (hζn : ζ ^ n = 1) (hζ : ζ ≠ 1) :
    ∑ j : Fin n, ζ ^ (j : ℕ) = 0 :=
  FRC.DFT.sum_pow_eq_zero_of_ne_one hζn hζ

/-- The shell Fourier matrix, `W k j = g^(j·k)`. -/
@[reducible] def W (g : K) : Matrix (Fin n) (Fin n) K :=
  FRC.DFT.W g

/-- The reversal `J k l = [l = −k]`. -/
@[reducible] def J : Matrix (Fin n) (Fin n) K :=
  FRC.DFT.J

omit [NeZero n] in
lemma W_apply (g : K) (k j : Fin n) : (W g : Matrix (Fin n) (Fin n) K) k j = g ^ ((j : ℕ) * (k : ℕ)) :=
  FRC.DFT.W_apply g k j

omit [NeZero n] in
lemma J_apply (k l : Fin n) : (J : Matrix (Fin n) (Fin n) K) k l = if l = -k then 1 else 0 :=
  FRC.DFT.J_apply k l

/-- `g^((-j).val) = (g^(j.val))⁻¹` for an `n`-th root of unity `g`. -/
lemma pow_neg_val {g : K} (hg : g ^ n = 1) (j : Fin n) :
    g ^ ((-j : Fin n) : ℕ) = (g ^ (j : ℕ))⁻¹ :=
  FRC.DFT.pow_neg_val hg j

omit [NeZero n] in
/-- `J² = 1`. -/
theorem J_sq : (J : Matrix (Fin n) (Fin n) K) ^ 2 = 1 :=
  FRC.DFT.J_sq

omit [NeZero n] in
/-- 6:D2 — `J` is a permutation matrix: `(M J) k j = M k (−j)`, so `M J` has the columns of `M`, reindexed by
the parity involution `j ↦ −j`. -/
theorem mul_J_apply (M : Matrix (Fin n) (Fin n) K) (k j : Fin n) :
    (M * (J : Matrix (Fin n) (Fin n) K)) k j = M k (-j) :=
  FRC.DFT.mul_J_apply M k j

/-- `W² = n • J` for any primitive `n`-th root of unity `g` (the general identity). -/
theorem W_sq (g : K) (hg : IsPrimitiveRoot g n) :
    (W g : Matrix (Fin n) (Fin n) K) ^ 2 = (n : K) • J :=
  FRC.DFT.W_sq g hg

/-- `W J = J W` for any `n`-th root of unity `g`. -/
theorem W_mul_J_comm (g : K) (hg : g ^ n = 1) :
    (W g : Matrix (Fin n) (Fin n) K) * J = J * W g :=
  FRC.DFT.W_mul_J_comm g hg

end base_aliases

section shell_aliases
variable {F : Type*} [Field F] [Fintype F]

/-- `(card F − 1 : ℕ) = −1` in a finite field `F`. -/
lemma natCast_card_pred_eq_neg_one : ((Fintype.card F - 1 : ℕ) : F) = -1 :=
  FRC.DFT.natCast_card_pred_eq_neg_one

/-- The quarter-turn `i = −g^κ` squares to `−1` (`g^{2κ}` is a primitive square root of unity). -/
lemma quarter_turn_sq (κ : ℕ) (hκ : Fintype.card F = 4 * κ + 1) (g : F)
    (hg : IsPrimitiveRoot g (Fintype.card F - 1)) :
    (-(g ^ κ)) ^ 2 = -1 :=
  FRC.DFT.quarter_turn_sq κ hκ g hg

/-- 6:B5, 6:B7 — every shell: on a field with `p = 4κ + 1` elements, `n = p − 1`,
`g` a primitive root and `F = i • W`: `W² = −J`, `F² = J`, `F⁴ = 1`, `W J = J W`. -/
theorem shell_relations (κ : ℕ) (hκ : Fintype.card F = 4 * κ + 1) (g : F)
    (hg : IsPrimitiveRoot g (Fintype.card F - 1)) [NeZero (Fintype.card F - 1)] :
    (W g : Matrix (Fin (Fintype.card F - 1)) (Fin (Fintype.card F - 1)) F) ^ 2 = -J ∧
    ((-(g ^ κ)) • W g : Matrix (Fin (Fintype.card F - 1)) (Fin (Fintype.card F - 1)) F) ^ 2 = J ∧
    ((-(g ^ κ)) • W g : Matrix (Fin (Fintype.card F - 1)) (Fin (Fintype.card F - 1)) F) ^ 4 = 1 ∧
    (W g : Matrix (Fin (Fintype.card F - 1)) (Fin (Fintype.card F - 1)) F) * J = J * W g :=
  FRC.DFT.shell_relations κ hκ g hg

/-- 6:B5, 6:B7 on the prime shell `𝔽_p = ZMod p`, an instance: the relations hold there for every prime
`p = 4κ + 1` and primitive root `g`. -/
theorem shell_relations_zmod (p κ : ℕ) [hp : Fact (Nat.Prime p)] (hκ : p = 4 * κ + 1)
    (g : ZMod p) (hg : IsPrimitiveRoot g (p - 1)) :
    haveI : NeZero (Fintype.card (ZMod p) - 1) :=
      ⟨by have := Fintype.one_lt_card (α := ZMod p); omega⟩
    ((-(g ^ κ)) • W g : Matrix (Fin (Fintype.card (ZMod p) - 1))
      (Fin (Fintype.card (ZMod p) - 1)) (ZMod p)) ^ 2 = J :=
  FRC.DFT.shell_relations_zmod p κ hκ g hg

end shell_aliases

/-! The declarations moved to the fourier theme's `Theme/Fractional.lean` by task LM36 (`FRC.Fractional`), each under
its old name. -/

section lm36_aliases
open FRC.Fractional
section
open FRC.DFT

open Matrix hiding J
open Finset


section algebra

variable {K : Type*} [Field K] {A : Type*} [Ring A] [Algebra K A]

variable (i : K) (f : A)

/-- 6:C2 — 6-fourier's name; the theorem is `FRC.Fractional.proj_mul_proj` (task LM36). -/
theorem proj_mul_proj (hi : i ^ 4 = 1) (hne : ∀ d : ZMod 4, d ≠ 0 → chi i d ≠ 1) (h4 : (4 : K) ≠ 0)
    (hf : f ^ 4 = 1) (ℓ m : ZMod 4) :
    proj i f ℓ * proj i f m = if ℓ = m then proj i f ℓ else 0 := by
  apply FRC.Fractional.proj_mul_proj <;> assumption

/-- 6:C2 — 6-fourier's name; the theorem is `FRC.Fractional.sum_proj` (task LM36). -/
theorem sum_proj (hi : i ^ 4 = 1) (hne : ∀ d : ZMod 4, d ≠ 0 → chi i d ≠ 1) (h4 : (4 : K) ≠ 0) :
    ∑ ℓ : ZMod 4, proj i f ℓ = 1 := by
  apply FRC.Fractional.sum_proj <;> assumption

end algebra

section family

variable {K : Type*} [Field K] {A : Type*} [Ring A] [Algebra K A] {n : ℕ} [NeZero n]

variable (i z : K) (f : A)

omit [NeZero n] in
/-- 6:E6 — 6-fourier's name; the theorem is `FRC.Fractional.frft_mul_proj_one` (task LM36). -/
theorem frft_mul_proj_one (hi : i ^ 4 = 1) (hne : ∀ d : ZMod 4, d ≠ 0 → chi i d ≠ 1) (h4 : (4 : K) ≠ 0)
    (hf : f ^ 4 = 1) (s : ZMod n) :
    frft i z f s * proj i f 1 = psi z s • proj i f 1 := by
  apply FRC.Fractional.frft_mul_proj_one <;> assumption

end family

section rotation

variable {K : Type*} [Field K]

variable (i : K)

/-- 6:E2 — 6-fourier's name; the theorem is `FRC.Fractional.circle` (task LM36). -/
theorem circle (hi : i ^ 2 = -1) (h2 : (2 : K) ≠ 0) (z : K) (hz : z ≠ 0) : cc z ^ 2 + dd i z ^ 2 = 1 := by
  apply FRC.Fractional.circle <;> assumption

/-- 6:E2 — 6-fourier's name; the theorem is `FRC.Fractional.rot_mul` (task LM36). -/
theorem rot_mul (hi : i ^ 2 = -1) (h2 : (2 : K) ≠ 0) (z w : K) (hz : z ≠ 0) (hw : w ≠ 0) :
    rot i (z * w) = rot i z * rot i w := by
  apply FRC.Fractional.rot_mul <;> assumption

/-- 6:E3 — 6-fourier's name; the theorem is `FRC.Fractional.rot_cardinal` (task LM36). -/
theorem rot_cardinal (hi : i ^ 2 = -1) (h2 : (2 : K) ≠ 0) :
    rot i 1 = 1 ∧ rot i i = !![0, -1; 1, 0] ∧ rot i (-1) = -1 ∧ rot i (-i) = !![0, 1; -1, 0] := by
  apply FRC.Fractional.rot_cardinal <;> assumption

/-- 6:E6 — 6-fourier's name; the theorem is `FRC.Fractional.rot_eigenline` (task LM36). -/
theorem rot_eigenline (hi : i ^ 2 = -1) (h2 : (2 : K) ≠ 0) (z : K) (hz : z ≠ 0) :
    (rot i z).mulVec ![1, -i] = z • ![1, -i] := by
  apply FRC.Fractional.rot_eigenline <;> assumption

/-- 6:E2 — 6-fourier's name; the definition is `FRC.Fractional.unitsEquivCircle` (task LM36). -/
@[reducible] noncomputable def unitsEquivCircle (hi : i ^ 2 = -1) (h2 : (2 : K) ≠ 0) : Kˣ ≃ Circle K :=
  FRC.Fractional.unitsEquivCircle i hi h2

/-- 6:E2 — 6-fourier's name; the theorem is `FRC.Fractional.card_circle` (task LM36). -/
theorem card_circle [Fintype K] [DecidableEq K] (hi : i ^ 2 = -1) (h2 : (2 : K) ≠ 0) :
    Fintype.card (Circle K) = Fintype.card K - 1 := by
  apply FRC.Fractional.card_circle <;> assumption

end rotation

section gauss

variable {K : Type*} [Field K] {n : ℕ} [NeZero n]

open Fin.CommRing in
/-- 6:C7 — 6-fourier's name; the theorem is `FRC.Fractional.gauss_mul_gauss_inv` (task LM36). -/
theorem gauss_mul_gauss_inv (κ : ℕ) [NeZero κ] (g : K) (hg : IsPrimitiveRoot g (4 * κ))
    (hnK : ((4 * κ : ℕ) : K) = -1) : gauss (4 * κ) g * gauss (4 * κ) g⁻¹ = -2 := by
  apply FRC.Fractional.gauss_mul_gauss_inv <;> assumption

omit [NeZero n] in
/-- 6:C7 — 6-fourier's name; the theorem is `FRC.Fractional.gauss_inv_of_sign` (task LM36). -/
theorem gauss_inv_of_sign {g i : K} (hGG : gauss n g * gauss n g⁻¹ = -2) (hi : i ^ 2 = -1) (h2 : (2 : K) ≠ 0)
    (ε : K) (hε : ε = 1 ∨ ε = -1) (hG : gauss n g = ε * (1 + i)) : gauss n g⁻¹ = -ε * (1 + -i) := by
  apply FRC.Fractional.gauss_inv_of_sign <;> assumption

end gauss


section shellFamily

variable {F : Type*} [Field F] [Fintype F] (κ : ℕ) [NeZero κ] (g : F)

variable (hκ : Fintype.card F = 4 * κ + 1) (hg : IsPrimitiveRoot g (4 * κ))
include hκ hg

/-- 6:C2 — 6-fourier's name; the theorem is `FRC.Fractional.shell_proj` (task LM36). -/
theorem shell_proj (ℓ m : ZMod 4) :
    Fmat κ g * shellProj κ g ℓ = chi (-(g ^ κ)) ℓ • shellProj κ g ℓ ∧
    shellProj κ g ℓ * shellProj κ g m = (if ℓ = m then shellProj κ g ℓ else 0) ∧
    ∑ ℓ : ZMod 4, shellProj κ g ℓ = 1 := by
  apply FRC.Fractional.shell_proj <;> assumption

/-- 6:C3 — 6-fourier's name; the theorem is `FRC.Fractional.shell_frft_add` (task LM36). -/
theorem shell_frft_add (s r : ZMod (4 * κ)) :
    shellFrft κ g (s + r) = shellFrft κ g s * shellFrft κ g r := by
  apply FRC.Fractional.shell_frft_add <;> assumption

/-- 6:C3 — 6-fourier's name; the theorem is `FRC.Fractional.shell_frft_cardinal` (task LM36). -/
theorem shell_frft_cardinal (m : ℕ) :
    shellFrft κ g (m • (κ : ZMod (4 * κ))) = Fmat κ g ^ m := by
  apply FRC.Fractional.shell_frft_cardinal <;> assumption

/-- 6:C3 — 6-fourier's name; the theorem is `FRC.Fractional.shell_frft_values` (task LM36). -/
theorem shell_frft_values :
    shellFrft κ g (κ : ZMod (4 * κ)) = Fmat κ g ∧
    shellFrft κ g (2 • (κ : ZMod (4 * κ))) = J ∧
    shellFrft κ g (1 : ZMod (4 * κ)) ^ κ = Fmat κ g := by
  apply FRC.Fractional.shell_frft_values <;> assumption

/-- 6:C8 — 6-fourier's name; the theorem is `FRC.Fractional.shell_frftLift` (task LM36). -/
theorem shell_frftLift (a : ZMod 4 → ℕ) (ha : ∀ ℓ, a ℓ % 4 = ℓ.val) (s r : ZMod (4 * κ)) (m : ℕ) :
    frftLift (-(g ^ κ)) g⁻¹ (Fmat κ g) a (s + r)
      = frftLift (-(g ^ κ)) g⁻¹ (Fmat κ g) a s * frftLift (-(g ^ κ)) g⁻¹ (Fmat κ g) a r ∧
    frftLift (-(g ^ κ)) g⁻¹ (Fmat κ g) a (m • (κ : ZMod (4 * κ))) = Fmat κ g ^ m := by
  apply FRC.Fractional.shell_frftLift <;> assumption

/-- 6:C9 — 6-fourier's name; the theorem is `FRC.Fractional.shell_conj` (task LM36). -/
theorem shell_conj (ℓ : ZMod 4) :
    (-(-(g ^ κ))) • W g⁻¹ = -(Fmat κ g ^ 3) ∧
    proj (-(-(g ^ κ))) (-(Fmat κ g ^ 3)) ℓ = shellProj κ g (ℓ + 2) := by
  apply FRC.Fractional.shell_conj <;> assumption

/-- 6:D2 — 6-fourier's name; the theorem is `FRC.Fractional.shell_frft_add_two_kappa` (task LM36). -/
theorem shell_frft_add_two_kappa (s : ZMod (4 * κ)) :
    shellFrft κ g (s + 2 • (κ : ZMod (4 * κ))) = shellFrft κ g s * J := by
  apply FRC.Fractional.shell_frft_add_two_kappa <;> assumption

/-- 6:E7 — 6-fourier's name; the theorem is `FRC.Fractional.shell_heisenberg` (task LM36). -/
theorem shell_heisenberg :
    Fmat κ g * shift = modul g * Fmat κ g ∧ Fmat κ g * modul g = shift' * Fmat κ g ∧
    (shift : Matrix (Fin (4 * κ)) (Fin (4 * κ)) F) * shift' = 1 := by
  apply FRC.Fractional.shell_heisenberg <;> assumption

/-- 6:E5 — 6-fourier's name; the theorem is `FRC.Fractional.shell_spectral_obstruction` (task LM36). -/
theorem shell_spectral_obstruction [DecidableEq F] (hκ2 : 2 ≤ κ) (s : ZMod (4 * κ)) :
    ¬ ∃ T : Matrix (Fin (4 * κ)) (Fin (4 * κ)) F, IsUnit T ∧ T * shift * T⁻¹ = shellFrft κ g s := by
  apply FRC.Fractional.shell_spectral_obstruction <;> assumption

/-- 6:C5 — 6-fourier's name; the theorem is `FRC.Fractional.shell_odd_proj_ne_zero` (task LM36). -/
theorem shell_odd_proj_ne_zero (hκ2 : 2 ≤ κ) : shellProj κ g 1 ≠ 0 ∧ shellProj κ g 3 ≠ 0 := by
  apply FRC.Fractional.shell_odd_proj_ne_zero <;> assumption

/-- 6:C5 — 6-fourier's name; the theorem is `FRC.Fractional.shell_even_proj_ne_zero` (task LM36). -/
theorem shell_even_proj_ne_zero : shellProj κ g 0 ≠ 0 ∧ shellProj κ g 2 ≠ 0 := by
  apply FRC.Fractional.shell_even_proj_ne_zero <;> assumption

/-- 6:C4, 6:D2 — 6-fourier's name; the theorem is `FRC.Fractional.shell_frft_injective` (task LM36). -/
theorem shell_frft_injective : Function.Injective (shellFrft κ g) := by
  apply FRC.Fractional.shell_frft_injective <;> assumption

end shellFamily

section prime

variable (p κ : ℕ) [hp : Fact p.Prime] [NeZero κ] (hpκ : p = 4 * κ + 1)
include hpκ

variable (g : ZMod p) (hg : IsPrimitiveRoot g (4 * κ))
include hg

/-- 6:C5 — 6-fourier's name; the theorem is `FRC.Fractional.shell_multiplicity_sums` (task LM36). -/
theorem shell_multiplicity_sums :
    (shellProj κ g 0).rank + (shellProj κ g 2).rank = 2 * κ + 1 ∧
    (shellProj κ g 1).rank + (shellProj κ g 3).rank = 2 * κ - 1 := by
  apply FRC.Fractional.shell_multiplicity_sums <;> assumption

/-- 6:C7 — 6-fourier's name; the theorem is `FRC.Fractional.shell_multiplicity_tuple` (task LM36). -/
theorem shell_multiplicity_tuple (ε : ZMod p) (hε : ε = 1 ∨ ε = -1)
    (hG : gauss (4 * κ) g = ε * (1 + -(g ^ κ))) :
    (ε = 1 → (shellProj κ g 0).rank = κ ∧ (shellProj κ g 1).rank = κ ∧
      (shellProj κ g 2).rank = κ + 1 ∧ (shellProj κ g 3).rank = κ - 1) ∧
    (ε = -1 → (shellProj κ g 0).rank = κ + 1 ∧ (shellProj κ g 1).rank = κ - 1 ∧
      (shellProj κ g 2).rank = κ ∧ (shellProj κ g 3).rank = κ) := by
  apply FRC.Fractional.shell_multiplicity_tuple <;> assumption

end prime

end

end lm36_aliases

-- Ledger predicates of 6-fourier (generated by make_predicates.py from docs/6-fourier/6-fourier-ledger.json; edit the ledger, not this section)
set_option linter.defProp false in
/-- 6:B5 (p06012) — $\Wt^{2}=-J$, $\Ft^{2}=J$, $\Ft^{4}=I$: the normalized operator generates the four-cycle, on the six shells of Table~\ref{tab:checks}. -/
def p06012 := @FRC.LedgerML.p06012
set_option linter.defProp false in
/-- 6:B7 (p06014) — $\Wt J=J\Wt$, hence $\Ft J=J\Ft$; every $v$ is uniquely $v^{+}+v^{-}$ with $Jv^{\pm}=\pm v^{\pm}$, a symmetric vector determined by its $2\kap+1$ entries at $0,\dots,2\kap$ and an antisymmetric one by its $2\kap-1$ entries at $1,\dots,2\kap-1$. -/
def p06014 := @FRC.LedgerML.p06014
/-- 6:C2 (p06016) — $\Pi_\ell^{2}=\Pi_\ell$, $\Pi_\ell\Pi_m=0$ for $\ell\neq m$, $\sum_\ell\Pi_\ell=I$, $\Ft\Pi_\ell=\im^{\ell}\Pi_\ell$. -/
theorem p06016 : (∀ {F : Type u_1} [Field F] [Fintype F] (κ : ℕ) [NeZero κ] (g : F), Fintype.card F = (4 : ℕ) * κ + (1 : ℕ) → IsPrimitiveRoot g ((4 : ℕ) * κ) → ∀ (ℓ m : ZMod (4 : ℕ)), FRC.Fractional.Fmat κ g * FRC.Fractional.shellProj κ g ℓ = FRC.Fractional.chi (-g ^ κ) ℓ • FRC.Fractional.shellProj κ g ℓ ∧ (FRC.Fractional.shellProj κ g ℓ * FRC.Fractional.shellProj κ g m = if ℓ = m then FRC.Fractional.shellProj κ g ℓ else (0 : Matrix (Fin ((4 : ℕ) * κ)) (Fin ((4 : ℕ) * κ)) F)) ∧ ∑ ℓ, FRC.Fractional.shellProj κ g ℓ = (1 : Matrix (Fin ((4 : ℕ) * κ)) (Fin ((4 : ℕ) * κ)) F)) ∧ (∀ {K : Type u_2} [Field K] {A : Type u_3} [Ring A] [Algebra K A] (i : K) (f : A), i ^ (4 : ℕ) = (1 : K) → (∀ (d : ZMod (4 : ℕ)), d ≠ (0 : ZMod (4 : ℕ)) → FRC.Fractional.chi i d ≠ (1 : K)) → (4 : K) ≠ (0 : K) → f ^ (4 : ℕ) = (1 : A) → ∀ (ℓ m : ZMod (4 : ℕ)), FRC.Fractional.proj i f ℓ * FRC.Fractional.proj i f m = if ℓ = m then FRC.Fractional.proj i f ℓ else (0 : A)) ∧ ∀ {K : Type u_4} [Field K] {A : Type u_5} [Ring A] [Algebra K A] (i : K) (f : A), i ^ (4 : ℕ) = (1 : K) → (∀ (d : ZMod (4 : ℕ)), d ≠ (0 : ZMod (4 : ℕ)) → FRC.Fractional.chi i d ≠ (1 : K)) → (4 : K) ≠ (0 : K) → ∑ ℓ, FRC.Fractional.proj i f ℓ = (1 : A) :=
  @FRC.LedgerML.p06016
/-- 6:C3 (p06017) — The exact finite-field FrFT: $s\mapsto\Ft^{[s]}$ is a representation of $\Phit$, $\Ft^{[s+r]}=\Ft^{[s]}\Ft^{[r]}$ for all $s,r$ (every pair on the six shells by the package), with the cardinal values $\Ft^{[0]}=I$, $\Ft^{[\kap]}=\Ft$, $\Ft^{[2\kap]}=J$, $\Ft^{[3\kap]}=\Ft^{-1}$, and $(\Ft^{[1]})^{\kap}=\Ft$. -/
theorem p06017 : (∀ {F : Type u_1} [Field F] [Fintype F] (κ : ℕ) [NeZero κ] (g : F), Fintype.card F = (4 : ℕ) * κ + (1 : ℕ) → IsPrimitiveRoot g ((4 : ℕ) * κ) → ∀ (s r : ZMod ((4 : ℕ) * κ)), FRC.Fractional.shellFrft κ g (s + r) = FRC.Fractional.shellFrft κ g s * FRC.Fractional.shellFrft κ g r) ∧ (∀ {F : Type u_2} [Field F] [Fintype F] (κ : ℕ) [NeZero κ] (g : F), Fintype.card F = (4 : ℕ) * κ + (1 : ℕ) → IsPrimitiveRoot g ((4 : ℕ) * κ) → ∀ (m : ℕ), FRC.Fractional.shellFrft κ g (m • ↑κ) = FRC.Fractional.Fmat κ g ^ m) ∧ ∀ {F : Type u_3} [Field F] [Fintype F] (κ : ℕ) [NeZero κ] (g : F), Fintype.card F = (4 : ℕ) * κ + (1 : ℕ) → IsPrimitiveRoot g ((4 : ℕ) * κ) → FRC.Fractional.shellFrft κ g ↑κ = FRC.Fractional.Fmat κ g ∧ FRC.Fractional.shellFrft κ g ((2 : ℕ) • ↑κ) = FRC.DFT.J ∧ FRC.Fractional.shellFrft κ g (1 : ZMod ((4 : ℕ) * κ)) ^ κ = FRC.Fractional.Fmat κ g :=
  @FRC.LedgerML.p06017
/-- 6:C4 (p06018) — Faithfulness: $s\mapsto\Ft^{[s]}$ is injective on $\Z_{4\kap}$ for every $\kap\ge1$; at $\p=5$ the surviving odd projector carries the faithful character. -/
theorem p06018 : ∀ {F : Type u_1} [Field F] [Fintype F] (κ : ℕ) [NeZero κ] (g : F), Fintype.card F = (4 : ℕ) * κ + (1 : ℕ) → IsPrimitiveRoot g ((4 : ℕ) * κ) → Function.Injective (FRC.Fractional.shellFrft κ g) :=
  @FRC.LedgerML.p06018
/-- 6:C5 (p06019) — The projector sums $\Pi_0+\Pi_2=\tfrac12(I+J)$ and $\Pi_1+\Pi_3=\tfrac12(I-J)$; $\Pi_0,\Pi_2\neq0$ for every $\kap\ge1$ and $\Pi_1,\Pi_3\neq0$ for $\kap\ge2$, each by one explicit entry; at $\p=5$ exactly one of $\Pi_1,\Pi_3$ vanishes. -/
theorem p06019 : (∀ {F : Type u_1} [Field F] [Fintype F] (κ : ℕ) [NeZero κ] (g : F), Fintype.card F = (4 : ℕ) * κ + (1 : ℕ) → IsPrimitiveRoot g ((4 : ℕ) * κ) → (2 : ℕ) ≤ κ → FRC.Fractional.shellProj κ g (1 : ZMod (4 : ℕ)) ≠ (0 : Matrix (Fin ((4 : ℕ) * κ)) (Fin ((4 : ℕ) * κ)) F) ∧ FRC.Fractional.shellProj κ g (3 : ZMod (4 : ℕ)) ≠ (0 : Matrix (Fin ((4 : ℕ) * κ)) (Fin ((4 : ℕ) * κ)) F)) ∧ (∀ {F : Type u_2} [Field F] [Fintype F] (κ : ℕ) [NeZero κ] (g : F), Fintype.card F = (4 : ℕ) * κ + (1 : ℕ) → IsPrimitiveRoot g ((4 : ℕ) * κ) → FRC.Fractional.shellProj κ g (0 : ZMod (4 : ℕ)) ≠ (0 : Matrix (Fin ((4 : ℕ) * κ)) (Fin ((4 : ℕ) * κ)) F) ∧ FRC.Fractional.shellProj κ g (2 : ZMod (4 : ℕ)) ≠ (0 : Matrix (Fin ((4 : ℕ) * κ)) (Fin ((4 : ℕ) * κ)) F)) ∧ ∀ (p κ : ℕ) [hp : Fact (Nat.Prime p)] [NeZero κ], p = (4 : ℕ) * κ + (1 : ℕ) → ∀ (g : ZMod p), IsPrimitiveRoot g ((4 : ℕ) * κ) → (FRC.Fractional.shellProj κ g (0 : ZMod (4 : ℕ))).rank + (FRC.Fractional.shellProj κ g (2 : ZMod (4 : ℕ))).rank = (2 : ℕ) * κ + (1 : ℕ) ∧ (FRC.Fractional.shellProj κ g (1 : ZMod (4 : ℕ))).rank + (FRC.Fractional.shellProj κ g (3 : ZMod (4 : ℕ))).rank = (2 : ℕ) * κ - (1 : ℕ) :=
  @FRC.LedgerML.p06019
/-- 6:C7 (p06021) — The multiplicity dichotomy in trace form: with $G=\sum_{k}\gen^{k^{2}}$ and $G^{*}=\sum_k\gen^{-k^{2}}$ the traces are $\operatorname{Tr}\Ft=\im G$, $\operatorname{Tr}\Ft^{2}=2$, $\operatorname{Tr}\Ft^{3}=\im G^{*}$ and $\operatorname{Tr}\Pi_\ell=\tfrac14\sum_r\im^{-\ell r}\operatorname{Tr}\Ft^{r}$; $GG^{*}=-2$ and $\varepsilon(\gen^{-1})=-\varepsilon(\gen)$; when $G=\varepsilon(1+\im)$ (A3) the tuple of traces is $(\kap,\kap,\kap+1,\kap-1)$ for $\varepsilon=+1$ and $(\kap+1,\kap-1,\kap,\kap)$ for $\varepsilon=-1$, read in $\Fp$; the sign and the tuples on the six shells of Table~\ref{tab:checks}. Exact on the $38$ primitive frames of $\p\in\{5,13,17,29,37\}$ and the $16$ of $\p=41$. -/
theorem p06021 : (∀ {K : Type u_1} [Field K] (κ : ℕ) [NeZero κ] (g : K), IsPrimitiveRoot g ((4 : ℕ) * κ) → ↑((4 : ℕ) * κ) = (-1 : K) → FRC.Fractional.gauss ((4 : ℕ) * κ) g * FRC.Fractional.gauss ((4 : ℕ) * κ) g⁻¹ = (-2 : K)) ∧ (∀ {K : Type u_2} [Field K] {n : ℕ} {g i : K}, FRC.Fractional.gauss n g * FRC.Fractional.gauss n g⁻¹ = (-2 : K) → i ^ (2 : ℕ) = (-1 : K) → (2 : K) ≠ (0 : K) → ∀ (ε : K), ε = (1 : K) ∨ ε = (-1 : K) → FRC.Fractional.gauss n g = ε * ((1 : K) + i) → FRC.Fractional.gauss n g⁻¹ = -ε * ((1 : K) + -i)) ∧ ∀ (p κ : ℕ) [hp : Fact (Nat.Prime p)] [NeZero κ], p = (4 : ℕ) * κ + (1 : ℕ) → ∀ (g : ZMod p), IsPrimitiveRoot g ((4 : ℕ) * κ) → ∀ (ε : ZMod p), ε = (1 : ZMod p) ∨ ε = (-1 : ZMod p) → FRC.Fractional.gauss ((4 : ℕ) * κ) g = ε * ((1 : ZMod p) + -g ^ κ) → (ε = (1 : ZMod p) → (FRC.Fractional.shellProj κ g (0 : ZMod (4 : ℕ))).rank = κ ∧ (FRC.Fractional.shellProj κ g (1 : ZMod (4 : ℕ))).rank = κ ∧ (FRC.Fractional.shellProj κ g (2 : ZMod (4 : ℕ))).rank = κ + (1 : ℕ) ∧ (FRC.Fractional.shellProj κ g (3 : ZMod (4 : ℕ))).rank = κ - (1 : ℕ)) ∧ (ε = (-1 : ZMod p) → (FRC.Fractional.shellProj κ g (0 : ZMod (4 : ℕ))).rank = κ + (1 : ℕ) ∧ (FRC.Fractional.shellProj κ g (1 : ZMod (4 : ℕ))).rank = κ - (1 : ℕ) ∧ (FRC.Fractional.shellProj κ g (2 : ZMod (4 : ℕ))).rank = κ ∧ (FRC.Fractional.shellProj κ g (3 : ZMod (4 : ℕ))).rank = κ) :=
  @FRC.LedgerML.p06021
set_option linter.defProp false in
/-- 6:C8 (p06022) — Exponent lifts: every lift $a_\ell\equiv\ell\pmod4$, $U^{(a)}_s=\sum_\ell\gen^{-a_\ell s}\Pi_\ell$, is additive with the same cardinal skeleton, $U^{(a)}_{s+r}=U^{(a)}_sU^{(a)}_r$ and $U^{(a)}_{m\kap}=\Ft^{m}$. -/
def p06022 := @FRC.LedgerML.p06022
/-- 6:C9 (p06023) — The conjugate chart $(\gen,\im)\mapsto(\gen^{-1},-\im)$: exactly $\Ft'=-\Ft^{-1}$ and $\Pi'_\ell=\Pi_{\ell+2}$; the operator relations, cardinal values, additivity and faithfulness hold on the conjugate frame, and its trace tuple is the other pattern of C7. -/
theorem p06023 : ∀ {F : Type u_1} [Field F] [Fintype F] (κ : ℕ) [NeZero κ] (g : F), Fintype.card F = (4 : ℕ) * κ + (1 : ℕ) → IsPrimitiveRoot g ((4 : ℕ) * κ) → ∀ (ℓ : ZMod (4 : ℕ)), - -g ^ κ • FRC.DFT.W g⁻¹ = -FRC.Fractional.Fmat κ g ^ (3 : ℕ) ∧ FRC.Fractional.proj (- -g ^ κ) (-FRC.Fractional.Fmat κ g ^ (3 : ℕ)) ℓ = FRC.Fractional.shellProj κ g (ℓ + (2 : ZMod (4 : ℕ))) :=
  @FRC.LedgerML.p06023
set_option linter.defProp false in
/-- 6:D2 (p06025) — The $4\kap$ framed domains are pairwise distinct; read as unordered bases $B_{s+2\kap}=B_s$, since $\Ft^{[s+2\kap]}=\Ft^{[s]}J$ and $J$ permutes the standard basis. -/
def p06025 := @FRC.LedgerML.p06025
/-- 6:E2 (p06031) — $R_s\in SO(2,\Fp)$, and $s\mapsto R_s$ is an isomorphism $\Phit\simeq SO(2,\Fp)$ with $|SO(2,\Fp)|=\p-1=4\kap$: the full rotation group of the $\p^{2}$-point plane is the phase cycle. Cited definitions (not proofs): FRC.Fourier.unitsEquivCircle. -/
theorem p06031 : (∀ {K : Type u_1} [Field K] (i : K), i ^ (2 : ℕ) = (-1 : K) → (2 : K) ≠ (0 : K) → ∀ (z : K), z ≠ (0 : K) → FRC.Fractional.cc z ^ (2 : ℕ) + FRC.Fractional.dd i z ^ (2 : ℕ) = (1 : K)) ∧ (∀ {K : Type u_2} [Field K] (i : K), i ^ (2 : ℕ) = (-1 : K) → (2 : K) ≠ (0 : K) → ∀ (z w : K), z ≠ (0 : K) → w ≠ (0 : K) → FRC.Fractional.rot i (z * w) = FRC.Fractional.rot i z * FRC.Fractional.rot i w) ∧ ∀ {K : Type u_3} [Field K] (i : K) [Fintype K] [DecidableEq K], i ^ (2 : ℕ) = (-1 : K) → (2 : K) ≠ (0 : K) → Fintype.card (FRC.Fractional.Circle K) = Fintype.card K - (1 : ℕ) :=
  @FRC.LedgerML.p06031
/-- 6:E3 (p06032) — The cardinal-skeleton dictionary $M_s\leftrightarrow s\leftrightarrow z_s\leftrightarrow R_s$ with $R_0=I$, $R_\kap=w$, $R_{2\kap}=-I$, $R_{3\kap}=w^{-1}$ (the $R_\kap$ column of Table~\ref{tab:checks}), $z_\kap=\im$; the shell's family and the Weil family stand in cardinal Weil correspondence, the Weil side by the normalization of A2 (an import). -/
theorem p06032 : ∀ {K : Type u_1} [Field K] (i : K), i ^ (2 : ℕ) = (-1 : K) → (2 : K) ≠ (0 : K) → FRC.Fractional.rot i (1 : K) = (1 : Matrix (Fin (2 : ℕ)) (Fin (2 : ℕ)) K) ∧ FRC.Fractional.rot i i = !![(0 : K), (-1 : K); (1 : K), (0 : K)] ∧ FRC.Fractional.rot i (-1 : K) = (-1 : Matrix (Fin (2 : ℕ)) (Fin (2 : ℕ)) K) ∧ FRC.Fractional.rot i (-i) = !![(0 : K), (1 : K); (-1 : K), (0 : K)] :=
  @FRC.LedgerML.p06032
set_option linter.defProp false in
/-- 6:E5 (p06034) — Spectral obstruction: for $\kap\ge2$ no invertible $T$ on $\Vt$ satisfies $T\sigma T^{-1}=\Ft^{[s]}$ for any $s$; the cyclic groups $\langle\sigma\rangle$ and $\langle\Ft^{[1]}\rangle$, each of order $4\kap$ ($\Ft^{[1]}$ by C4; $\sigma$ permutes the $4\kap$ labels cyclically), are not conjugate. -/
def p06034 := @FRC.LedgerML.p06034
/-- 6:E6 (p06035) — Common character sector: $\Ft^{[s]}\Pi_1=\gen^{-s}\Pi_1$, so on $E_1=\operatorname{im}\Pi_1\neq0$ ($\kap\ge2$) the family acts by the meridian character; the intertwiner $\Ft^{[s]}T_v=T_vS_{-s}$ on every $x\in\Fp$ and $s$, and $R_s(1,-\im)^{\mathsf T}=\gen^{-s}(1,-\im)^{\mathsf T}$. -/
theorem p06035 : (∀ {K : Type u_1} [Field K] {A : Type u_2} [Ring A] [Algebra K A] {n : ℕ} (i z : K) (f : A), i ^ (4 : ℕ) = (1 : K) → (∀ (d : ZMod (4 : ℕ)), d ≠ (0 : ZMod (4 : ℕ)) → FRC.Fractional.chi i d ≠ (1 : K)) → (4 : K) ≠ (0 : K) → f ^ (4 : ℕ) = (1 : A) → ∀ (s : ZMod n), FRC.Fractional.frft i z f s * FRC.Fractional.proj i f (1 : ZMod (4 : ℕ)) = FRC.Fractional.psi z s • FRC.Fractional.proj i f (1 : ZMod (4 : ℕ))) ∧ ∀ {K : Type u_3} [Field K] (i : K), i ^ (2 : ℕ) = (-1 : K) → (2 : K) ≠ (0 : K) → ∀ (z : K), z ≠ (0 : K) → (FRC.Fractional.rot i z).mulVec ![(1 : K), -i] = z • ![(1 : K), -i] :=
  @FRC.LedgerML.p06035
/-- 6:E7 (p06036) — Cardinal Heisenberg covariance: $\Ft\sigma\Ft^{-1}=D_1$, $\Ft D_1\Ft^{-1}=\sigma^{-1}$; $\Ft^{r}\sigma=\sigma_r\Ft^{r}$ with $(\sigma,D_1,\sigma^{-1},D_1^{-1})$; the expansion \eqref{eq:conj-expansion}, $\Ft^{[s]}=\sum_r c_r(s)\Ft^{r}$ with $c_r(s)=\tfrac14\sum_\ell(\gen^{r\kap-s})^{\ell}$. -/
theorem p06036 : ∀ {F : Type u_1} [Field F] [Fintype F] (κ : ℕ) [NeZero κ] (g : F), Fintype.card F = (4 : ℕ) * κ + (1 : ℕ) → IsPrimitiveRoot g ((4 : ℕ) * κ) → FRC.Fractional.Fmat κ g * FRC.Fractional.shift = FRC.Fractional.modul g * FRC.Fractional.Fmat κ g ∧ FRC.Fractional.Fmat κ g * FRC.Fractional.modul g = FRC.Fractional.shift' * FRC.Fractional.Fmat κ g ∧ FRC.Fractional.shift * FRC.Fractional.shift' = (1 : Matrix (Fin ((4 : ℕ) * κ)) (Fin ((4 : ℕ) * κ)) F) :=
  @FRC.LedgerML.p06036
-- end ledger predicates

end FRC.Fourier
