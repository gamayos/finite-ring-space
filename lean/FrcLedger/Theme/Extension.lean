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

end FRC.Extension
