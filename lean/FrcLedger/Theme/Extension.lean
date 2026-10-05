import Mathlib

/-!
# FrcLedger.Theme.Extension — the quadratic extension (the extension theme, ledger migration task LM17)

`Ext F ν`: the elements `a + b w` of `F[w]/(w² − ν)` over a commutative ring, with its commutative ring structure,
the embedding of the base, conjugation `a + bw ↦ a − bw`, the norm `N = a² − νb²` (multiplicative, `z z̄ = N(z)`),
the star ring, and the field when `ν` is a nonsquare. Moved from 8-dirac's module, which keeps every old name as an
alias. Classical, on Mathlib's hierarchy.
-/

namespace FRC.Extension

@[ext]
structure Ext (F : Type*) (ν : F) where
  re : F
  im : F

namespace Ext
variable {F : Type*} [CommRing F] {ν : F}

instance : Zero (Ext F ν) := ⟨⟨0, 0⟩⟩
instance : One (Ext F ν) := ⟨⟨1, 0⟩⟩
instance : Add (Ext F ν) := ⟨fun z z' => ⟨z.re + z'.re, z.im + z'.im⟩⟩
instance : Neg (Ext F ν) := ⟨fun z => ⟨-z.re, -z.im⟩⟩
instance : Sub (Ext F ν) := ⟨fun z z' => ⟨z.re - z'.re, z.im - z'.im⟩⟩
instance : Mul (Ext F ν) := ⟨fun z z' => ⟨z.re * z'.re + ν * (z.im * z'.im), z.re * z'.im + z.im * z'.re⟩⟩
instance : SMul ℕ (Ext F ν) := ⟨fun n z => ⟨n • z.re, n • z.im⟩⟩
instance : SMul ℤ (Ext F ν) := ⟨fun n z => ⟨n • z.re, n • z.im⟩⟩

@[simp] theorem zero_re : (0 : Ext F ν).re = 0 := rfl
@[simp] theorem zero_im : (0 : Ext F ν).im = 0 := rfl
@[simp] theorem one_re : (1 : Ext F ν).re = 1 := rfl
@[simp] theorem one_im : (1 : Ext F ν).im = 0 := rfl
@[simp] theorem add_re (z z' : Ext F ν) : (z + z').re = z.re + z'.re := rfl
@[simp] theorem add_im (z z' : Ext F ν) : (z + z').im = z.im + z'.im := rfl
@[simp] theorem neg_re (z : Ext F ν) : (-z).re = -z.re := rfl
@[simp] theorem neg_im (z : Ext F ν) : (-z).im = -z.im := rfl
@[simp] theorem sub_re (z z' : Ext F ν) : (z - z').re = z.re - z'.re := rfl
@[simp] theorem sub_im (z z' : Ext F ν) : (z - z').im = z.im - z'.im := rfl
@[simp] theorem mul_re (z z' : Ext F ν) : (z * z').re = z.re * z'.re + ν * (z.im * z'.im) := rfl
@[simp] theorem mul_im (z z' : Ext F ν) : (z * z').im = z.re * z'.im + z.im * z'.re := rfl
@[simp] theorem nsmul_re (n : ℕ) (z : Ext F ν) : (n • z).re = n • z.re := rfl
@[simp] theorem nsmul_im (n : ℕ) (z : Ext F ν) : (n • z).im = n • z.im := rfl
@[simp] theorem zsmul_re (n : ℤ) (z : Ext F ν) : (n • z).re = n • z.re := rfl
@[simp] theorem zsmul_im (n : ℤ) (z : Ext F ν) : (n • z).im = n • z.im := rfl

instance : CommRing (Ext F ν) where
  add_assoc _ _ _ := by ext <;> simp [add_assoc]
  zero_add _ := by ext <;> simp
  add_zero _ := by ext <;> simp
  add_comm _ _ := by ext <;> simp [add_comm]
  nsmul := (· • ·)
  nsmul_zero _ := by ext <;> simp
  nsmul_succ _ _ := by ext <;> simp [add_smul]
  zsmul := (· • ·)
  zsmul_zero' _ := by ext <;> simp
  zsmul_succ' _ _ := by ext <;> simp [add_smul]
  zsmul_neg' _ _ := by ext <;> simp [add_smul] <;> ring
  neg_add_cancel _ := by ext <;> simp
  sub_eq_add_neg _ _ := by ext <;> simp [sub_eq_add_neg]
  mul_assoc _ _ _ := by ext <;> simp <;> ring
  one_mul _ := by ext <;> simp
  mul_one _ := by ext <;> simp
  left_distrib _ _ _ := by ext <;> simp <;> ring
  right_distrib _ _ _ := by ext <;> simp <;> ring
  zero_mul _ := by ext <;> simp
  mul_zero _ := by ext <;> simp
  mul_comm _ _ := by ext <;> simp <;> ring

def ofBase (a : F) : Ext F ν := ⟨a, 0⟩
def w : Ext F ν := ⟨0, 1⟩
def conj (z : Ext F ν) : Ext F ν := ⟨z.re, -z.im⟩
def norm (z : Ext F ν) : F := z.re * z.re - ν * (z.im * z.im)

@[simp] theorem ofBase_re (a : F) : (ofBase a : Ext F ν).re = a := rfl
@[simp] theorem ofBase_im (a : F) : (ofBase a : Ext F ν).im = 0 := rfl
@[simp] theorem w_re : (w : Ext F ν).re = 0 := rfl
@[simp] theorem w_im : (w : Ext F ν).im = 1 := rfl
@[simp] theorem conj_re (z : Ext F ν) : (conj z).re = z.re := rfl
@[simp] theorem conj_im (z : Ext F ν) : (conj z).im = -z.im := rfl

theorem w_sq : (w : Ext F ν) ^ 2 = ofBase ν := by ext <;> simp [sq]
theorem conj_mul (z z' : Ext F ν) : conj (z * z') = conj z * conj z' := by ext <;> simp <;> ring
theorem conj_add (z z' : Ext F ν) : conj (z + z') = conj z + conj z' := by ext <;> simp [add_comm]
theorem conj_conj (z : Ext F ν) : conj (conj z) = z := by ext <;> simp
theorem conj_one : conj (1 : Ext F ν) = 1 := by ext <;> simp
theorem mul_conj (z : Ext F ν) : z * conj z = ofBase (norm z) := by ext <;> simp [norm] <;> ring
/-- 8:A2 — the norm is multiplicative: `N(zz') = N(z)N(z')`. -/
theorem norm_mul (z z' : Ext F ν) : norm (z * z') = norm z * norm z' := by
  simp only [norm, mul_re, mul_im]; ring
theorem ofBase_mul (a b : F) : (ofBase (a * b) : Ext F ν) = ofBase a * ofBase b := by ext <;> simp
theorem ofBase_add (a b : F) : (ofBase (a + b) : Ext F ν) = ofBase a + ofBase b := by ext <;> simp
theorem ofBase_one : (ofBase 1 : Ext F ν) = 1 := rfl
theorem ofBase_zero : (ofBase 0 : Ext F ν) = 0 := rfl
theorem ofBase_injective : Function.Injective (ofBase : F → Ext F ν) := fun a b h => by
  simpa using congrArg re h
theorem conj_ofBase (a : F) : conj (ofBase a : Ext F ν) = ofBase a := by ext <;> simp
theorem conj_w : conj (w : Ext F ν) = -w := by ext <;> simp
theorem conj_eq_self_iff (z : Ext F ν) (h2 : (2 : F) ≠ 0) [NoZeroDivisors F] :
    conj z = z ↔ z.im = 0 := by
  constructor
  · intro h
    have := congrArg im h
    simp at this
    have h' : (2 : F) * z.im = 0 := by linear_combination -this
    rcases mul_eq_zero.1 h' with h0 | h0
    · exact absurd h0 h2
    · exact h0
  · intro h; ext <;> simp [h]
theorem conj_eq_neg_iff (z : Ext F ν) (h2 : (2 : F) ≠ 0) [NoZeroDivisors F] :
    conj z = -z ↔ z.re = 0 := by
  constructor
  · intro h
    have := congrArg re h
    simp at this
    have h' : (2 : F) * z.re = 0 := by linear_combination this
    rcases mul_eq_zero.1 h' with h0 | h0
    · exact absurd h0 h2
    · exact h0
  · intro h; ext <;> simp [h]

instance : StarRing (Ext F ν) where
  star := conj
  star_involutive := conj_conj
  star_mul z z' := by rw [conj_mul, mul_comm]
  star_add z z' := conj_add z z'

theorem star_def (z : Ext F ν) : star z = conj z := rfl

/-- `w` generates: `z = re + im · w`. -/
theorem eq_re_add_im_w (z : Ext F ν) : z = ofBase z.re + ofBase z.im * w := by ext <;> simp

end Ext

/-! ## The field: `ν` a nonsquare makes `K` a field -/
namespace Ext
variable {F : Type*} [Field F] {ν : F}

theorem norm_eq_zero_iff (hν : ¬ IsSquare ν) (z : Ext F ν) : norm z = 0 ↔ z = 0 := by
  constructor
  · intro h
    by_cases hb : z.im = 0
    · have : z.re * z.re = 0 := by simpa [norm, hb] using h
      ext <;> simp [hb, mul_self_eq_zero.1 this]
    · exfalso; apply hν
      refine ⟨z.re / z.im, ?_⟩
      have : z.re * z.re = ν * (z.im * z.im) := by
        simpa [norm, sub_eq_zero] using h
      rw [div_mul_div_comm, eq_div_iff (mul_ne_zero hb hb), this]
  · rintro rfl; simp [norm]

noncomputable instance instInv : Inv (Ext F ν) := ⟨fun z => ofBase (norm z)⁻¹ * conj z⟩

theorem inv_def (z : Ext F ν) : z⁻¹ = ofBase (norm z)⁻¹ * conj z := rfl

theorem mul_inv_cancel' (hν : ¬ IsSquare ν) (z : Ext F ν) (hz : z ≠ 0) : z * z⁻¹ = 1 := by
  rw [inv_def, mul_left_comm, mul_conj, ← ofBase_mul, inv_mul_cancel₀ ((norm_eq_zero_iff hν z).not.2 hz)]
  rfl

/-- 8:A2 — the field structure under `¬ IsSquare ν`, `z⁻¹ = z̄/N(z)` (a `def`, not an instance: the hypothesis is
not a class). -/
@[instance_reducible] noncomputable def field (hν : ¬ IsSquare ν) : Field (Ext F ν) where
  __ := (inferInstance : CommRing (Ext F ν))
  inv := (·⁻¹)
  exists_pair_ne := ⟨0, 1, fun h => by simpa using congrArg re h⟩
  mul_inv_cancel z hz := mul_inv_cancel' hν z hz
  inv_zero := by ext <;> simp [inv_def, norm]
  nnqsmul := _
  nnqsmul_def _ _ := rfl
  qsmul := _
  qsmul_def _ _ := rfl

end Ext

/-! ## The Lorentzian plane: the square classes and the boosts of `x² − ν t²` (3-causality's theorems, moved by the
ledger migration, task LM20; the old names `FRC.Causality.*` stay as aliases) -/

section lorentz

variable {F : Type*} [Field F]

/-- 3:B2 (Thm. nonexistence, first clause): `c² = ν` makes `ν` a square, so a nonsquare `ν` has no root. -/
theorem no_causal_root (ν c : F) (h : ¬IsSquare ν) : c ^ 2 ≠ ν := fun e => h ⟨c, by rw [← e, sq]⟩

/-- 3:B2 (the consequence): when `−1` is a square (`card F ≢ 3 mod 4`) so is `−c²`, and every coefficient of
`−c² t² + x² + y² + z²` lies in the class of squares — a Euclidean form for every `c ≠ 0`. -/
theorem neg_sq_is_square [Fintype F] (hF : Fintype.card F % 4 ≠ 3) (c : F) : IsSquare (-(c ^ 2)) := by
  obtain ⟨i, hi⟩ := FiniteField.isSquare_neg_one_iff.mpr hF
  exact ⟨i * c, by rw [show -(c ^ 2) = (-1) * c ^ 2 by ring, hi]; ring⟩

/-- 3:B3 (Lemma absorption): coefficients `a_i = w_i² a_0` are absorbed by `x_i ↦ w_i x_i`. -/
theorem absorb (a0 a1 a2 a3 w1 w2 w3 x0 x1 x2 x3 : F) (h1 : w1 ^ 2 * a0 = a1) (h2 : w2 ^ 2 * a0 = a2)
    (h3 : w3 ^ 2 * a0 = a3) :
    a0 * x0 ^ 2 + a1 * x1 ^ 2 + a2 * x2 ^ 2 + a3 * x3 ^ 2 =
    a0 * (x0 ^ 2 + (w1 * x1) ^ 2 + (w2 * x2) ^ 2 + (w3 * x3) ^ 2) := by
  rw [← h1, ← h2, ← h3]; ring

/-- 3:B5: `x² − ν t²` is anisotropic for a nonsquare `ν`. -/
theorem aniso_tx (ν t x : F) (hν : ¬IsSquare ν) (e : x ^ 2 = ν * t ^ 2) : t = 0 ∧ x = 0 := by
  by_cases ht : t = 0
  · subst ht; simp at e; exact ⟨rfl, e⟩
  · exact absurd ⟨x / t, by field_simp; linear_combination (-1 : F) * e⟩ hν

/-- 3:C2 (the finite Lorentz boost): `Λ(γ, b) = !![γ, b; νb, γ]` with `γ² − νb² = 1` preserves `x² − ν t²`. -/
theorem boost_preserves (ν γ b t x : F) (h : γ ^ 2 - ν * b ^ 2 = 1) :
    (γ * x + ν * b * t) ^ 2 - ν * (γ * t + b * x) ^ 2 = x ^ 2 - ν * t ^ 2 := by
  linear_combination (x ^ 2 - ν * t ^ 2) * h

/-- 3:C2: the boosts compose as the norm-one elements of `F(√ν)` multiply. -/
theorem boost_comp (ν γ1 b1 γ2 b2 : F) :
    !![γ1, b1; ν * b1, γ1] * !![γ2, b2; ν * b2, γ2] =
    !![γ1 * γ2 + ν * (b1 * b2), γ1 * b2 + b1 * γ2; ν * (γ1 * b2 + b1 * γ2), γ1 * γ2 + ν * (b1 * b2)] := by
  ext i j; fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_two] <;> ring

/-- 3:C2: `Λ(γ, b)` is orthogonal for the Gram matrix `diag(−ν, 1)` of `Q_ν`: `Λᵀ G Λ = G`. -/
theorem boost_orthogonal (ν γ b : F) (h : γ ^ 2 - ν * b ^ 2 = 1) :
    (!![γ, b; ν * b, γ]).transpose * !![-ν, 0; 0, 1] * !![γ, b; ν * b, γ] = !![-ν, 0; 0, 1] := by
  ext i j; fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_two] <;>
    first | ring1 | linear_combination (-ν) * h | linear_combination h

/-- 3:C3: `γ ≠ 0` on every boost of the Lorentzian plane (`γ = 0` would make `ν = (i/b)²`). -/
theorem gamma_ne_zero [Fintype F] (hF : Fintype.card F % 4 ≠ 3) (ν γ b : F) (hν : ¬IsSquare ν)
    (h : γ ^ 2 - ν * b ^ 2 = 1) : γ ≠ 0 := by
  rintro rfl
  obtain ⟨i, hi⟩ := FiniteField.isSquare_neg_one_iff.mpr hF
  have hb : b ≠ 0 := by rintro rfl; simp at h
  have hνb : ν * b ^ 2 = -1 := by linear_combination -h
  exact hν ⟨i / b, by field_simp; linear_combination hνb + hi⟩

/-- 3:C3: the velocity `v = −νb/γ` satisfies `γ² (ν − v²) = ν` — `γ = 1/√(1 − β²)` with `β² = v²/ν`. -/
theorem gamma_velocity (ν γ b v : F) (h : γ ^ 2 - ν * b ^ 2 = 1) (hv : v * γ = -(ν * b)) :
    γ ^ 2 * (ν - v ^ 2) = ν := by
  linear_combination ν * h - (v * γ - ν * b) * hv

/-- 3:C3 (Einstein's addition law, exact): `v₁₂ (ν + v₁v₂) = ν (v₁ + v₂)`. -/
theorem velocity_addition (ν γ1 b1 γ2 b2 v1 v2 v12 : F) (hγ : γ1 * γ2 ≠ 0)
    (hv1 : v1 * γ1 = -(ν * b1)) (hv2 : v2 * γ2 = -(ν * b2))
    (hv12 : v12 * (γ1 * γ2 + ν * (b1 * b2)) = -(ν * (γ1 * b2 + b1 * γ2))) :
    v12 * (ν + v1 * v2) = ν * (v1 + v2) := by
  have : γ1 * γ2 * (v12 * (ν + v1 * v2) - ν * (v1 + v2)) = 0 := by
    linear_combination ν * hv12 + (-v12 * ν * b2 - ν * γ2 + v12 * (v2 * γ2 + ν * b2)) * hv1 +
      (-v12 * ν * b1 - ν * γ1) * hv2
  rcases mul_eq_zero.mp this with h | h
  · exact absurd h hγ
  · exact sub_eq_zero.mp h

end lorentz

end FRC.Extension
