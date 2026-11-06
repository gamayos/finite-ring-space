import FrcCore.Cycle
import FrcCore.Theme.Dirac

/-!
# The Hermitian layer of 8-dirac — sums in the extension, the form, the translations, the Laplacian, no axioms

The third file of the dirac theme (5 November 2026, the core-proof programme): the Hermitian form on fields of the
register with values in the coefficient field `K = 𝔽_p(√ν)`, on every shell. A field is a function `Nat → Ext p ν`
read on the register `[0, p)`; a sum of field values is the pair of the base theme's `sumRange` sums of the components
(`esum`), so every identity of sums reduces to the base theme's (`sum_add`, `sum_neg`, `sum_mul_left`, `sum_eq_single`,
and the cycle's `sum_shift`). The form `⟨ψ, φ⟩ = Σ_x ψ̄(x) φ(x)` is Hermitian, `conj ⟨ψ, φ⟩ = ⟨φ, ψ⟩`, sesquilinear, and
nondegenerate — a field orthogonal to every field vanishes at every register site, by the delta fields (C2). The
translation `(T_s ψ)(x) = ψ(x + s)` preserves the form, and its adjoint is the opposite translation (C8, by the shift
invariance of the cycle sum); the Laplacian `Δψ = T_1 ψ + T_{p−1} ψ − 2ψ` is self-adjoint (C9); a finite Hamiltonian
`H = −ϰΔ + V` with `ϰ` and `V` Frobenius-fixed is self-adjoint (C11). Frame covariance: an additive bijection of the
coordinate points (the boost) pulls fields back, and the pullback intertwines the translations and the differences of
the two frames (C13, D7). Nothing here needs function extensionality: equalities of fields are stated at every site. No
axioms.
-/

namespace FRC.Dirac.Hermitian

open FRC FRC.Shell FRC.Extension

variable {p : Nat} [Pos p] {ν : Shell p}

/-! ## The ring identities of the extension on components -/
section ext
open FRC.Extension.Ext (conj ofShell)

theorem add_re (z z' : Ext p ν) : (z + z').re = z.re + z'.re := rfl
theorem add_im (z z' : Ext p ν) : (z + z').im = z.im + z'.im := rfl
theorem neg_re (z : Ext p ν) : (-z).re = -z.re := rfl
theorem neg_im (z : Ext p ν) : (-z).im = -z.im := rfl
theorem zero_re : (0 : Ext p ν).re = 0 := rfl
theorem zero_im : (0 : Ext p ν).im = 0 := rfl
theorem one_re : (1 : Ext p ν).re = 1 := rfl
theorem one_im : (1 : Ext p ν).im = 0 := rfl

theorem add_comm (z z' : Ext p ν) : z + z' = z' + z := FRC.Extension.Ext.ext (Shell.add_comm _ _) (Shell.add_comm _ _)
theorem add_assoc (a b c : Ext p ν) : a + b + c = a + (b + c) := FRC.Extension.Ext.ext (Shell.add_assoc _ _ _) (Shell.add_assoc _ _ _)
theorem zero_add (z : Ext p ν) : 0 + z = z := FRC.Extension.Ext.ext (Shell.zero_add _) (Shell.zero_add _)
theorem add_zero (z : Ext p ν) : z + 0 = z := FRC.Extension.Ext.ext (Shell.add_zero _) (Shell.add_zero _)
theorem add_neg (z : Ext p ν) : z + -z = 0 := FRC.Extension.Ext.ext (Shell.add_neg _) (Shell.add_neg _)
theorem neg_add (z : Ext p ν) : -z + z = 0 := FRC.Extension.Ext.ext (Shell.neg_add _) (Shell.neg_add _)
theorem neg_neg (z : Ext p ν) : - -z = z := FRC.Extension.Ext.ext (Shell.neg_neg _) (Shell.neg_neg _)
theorem neg_add_rev (z z' : Ext p ν) : -(z + z') = -z + -z' := FRC.Extension.Ext.ext (Shell.neg_add_rev _ _) (Shell.neg_add_rev _ _)
theorem zero_mul (z : Ext p ν) : (0 : Ext p ν) * z = 0 := by
  apply FRC.Extension.Ext.ext
  · show 0 * z.re + ν * (0 * z.im) = 0
    rw [Shell.zero_mul, Shell.zero_mul, Shell.mul_zero, Shell.add_zero]
  · show 0 * z.im + 0 * z.re = 0
    rw [Shell.zero_mul, Shell.zero_mul, Shell.add_zero]
theorem mul_zero (z : Ext p ν) : z * 0 = 0 := by rw [FRC.Extension.Ext.mul_comm]; exact zero_mul z
theorem mul_add (a b c : Ext p ν) : a * (b + c) = a * b + a * c := by
  apply FRC.Extension.Ext.ext
  · show a.re * (b.re + c.re) + ν * (a.im * (b.im + c.im)) = a.re * b.re + ν * (a.im * b.im) + (a.re * c.re + ν * (a.im * c.im))
    rw [Shell.left_distrib, Shell.left_distrib, Shell.left_distrib, Shell.add_add_add_comm]
  · show a.re * (b.im + c.im) + a.im * (b.re + c.re) = a.re * b.im + a.im * b.re + (a.re * c.im + a.im * c.re)
    rw [Shell.left_distrib, Shell.left_distrib, Shell.add_add_add_comm]
theorem add_mul (a b c : Ext p ν) : (a + b) * c = a * c + b * c := by
  rw [FRC.Extension.Ext.mul_comm, mul_add, FRC.Extension.Ext.mul_comm c a, FRC.Extension.Ext.mul_comm c b]
theorem neg_mul (a b : Ext p ν) : -(a * b) = -a * b := by
  apply FRC.Extension.Ext.ext
  · show -(a.re * b.re + ν * (a.im * b.im)) = -a.re * b.re + ν * (-a.im * b.im)
    rw [Shell.neg_add_rev, Shell.neg_mul, ← Shell.neg_mul, Shell.mul_neg ν, Shell.neg_mul a.im]
  · show -(a.re * b.im + a.im * b.re) = -a.re * b.im + -a.im * b.re
    rw [Shell.neg_add_rev, Shell.neg_mul, Shell.neg_mul]
theorem mul_neg (a b : Ext p ν) : -(a * b) = a * -b := by rw [FRC.Extension.Ext.mul_comm, neg_mul, FRC.Extension.Ext.mul_comm]
theorem conj_add (z z' : Ext p ν) : conj (z + z') = conj z + conj z' := FRC.Extension.Ext.ext rfl (Shell.neg_add_rev _ _)
theorem conj_neg (z : Ext p ν) : conj (-z) = -conj z := FRC.Extension.Ext.ext rfl rfl
theorem conj_zero : conj (0 : Ext p ν) = 0 := FRC.Extension.Ext.ext rfl Shell.neg_zero
theorem conj_one : conj (1 : Ext p ν) = 1 := FRC.Extension.Ext.ext rfl Shell.neg_zero
theorem conj_ofShell (c : Shell p) : conj (ofShell c : Ext p ν) = ofShell c := FRC.Extension.Ext.ext rfl Shell.neg_zero
/-- `(a + b) + (c + d) = (a + c) + (b + d)` in the extension. -/
theorem add_add_add_comm (a b c d : Ext p ν) : a + b + (c + d) = a + c + (b + d) :=
  FRC.Extension.Ext.ext (Shell.add_add_add_comm _ _ _ _) (Shell.add_add_add_comm _ _ _ _)
end ext

/-! ## Sums in the extension, on components -/
section sums

/-- `Σ_{j<n} f j` in the extension: the pair of the component sums. -/
def esum (f : Nat → Ext p ν) (n : Nat) : Ext p ν :=
  ⟨sumRange (fun j => (f j).re) n, sumRange (fun j => (f j).im) n⟩

theorem esum_re (f : Nat → Ext p ν) (n : Nat) : (esum f n).re = sumRange (fun j => (f j).re) n := rfl
theorem esum_im (f : Nat → Ext p ν) (n : Nat) : (esum f n).im = sumRange (fun j => (f j).im) n := rfl
theorem esum_zero (f : Nat → Ext p ν) : esum f 0 = 0 := rfl
theorem esum_succ (f : Nat → Ext p ν) (n : Nat) : esum f (n + 1) = esum f n + f n := rfl

theorem esum_congr {f h : Nat → Ext p ν} (n : Nat) (e : ∀ j, j < n → f j = h j) : esum f n = esum h n :=
  FRC.Extension.Ext.ext (sum_congr n fun j hj => FRC.Extension.Ext.re_congr (e j hj)) (sum_congr n fun j hj => FRC.Extension.Ext.im_congr (e j hj))

theorem esum_add (f h : Nat → Ext p ν) (n : Nat) : esum (fun j => f j + h j) n = esum f n + esum h n :=
  FRC.Extension.Ext.ext (sum_add _ _ n) (sum_add _ _ n)

theorem esum_neg (f : Nat → Ext p ν) (n : Nat) : esum (fun j => -(f j)) n = -(esum f n) :=
  FRC.Extension.Ext.ext (sum_neg _ n) (sum_neg _ n)

theorem esum_conj (f : Nat → Ext p ν) (n : Nat) : FRC.Extension.Ext.conj (esum f n) = esum (fun j => FRC.Extension.Ext.conj (f j)) n :=
  FRC.Extension.Ext.ext rfl (by show -(sumRange (fun j => (f j).im) n) = sumRange (fun j => -(f j).im) n; rw [sum_neg])

theorem esum_zero_of (f : Nat → Ext p ν) (n : Nat) (h : ∀ j, j < n → f j = 0) : esum f n = 0 :=
  FRC.Extension.Ext.ext (sum_zero n fun j hj => FRC.Extension.Ext.re_congr (h j hj)) (sum_zero n fun j hj => FRC.Extension.Ext.im_congr (h j hj))

/-- A sum with one term: `Σ_{j<n} f j = f j₀` when every other term vanishes. -/
theorem esum_eq_single (f : Nat → Ext p ν) {j₀ n : Nat} (hj : j₀ < n) (h : ∀ j, j < n → j ≠ j₀ → f j = 0) :
    esum f n = f j₀ :=
  FRC.Extension.Ext.ext (sum_eq_single hj fun j hjn hne => FRC.Extension.Ext.re_congr (h j hjn hne))
    (sum_eq_single hj fun j hjn hne => FRC.Extension.Ext.im_congr (h j hjn hne))

/-- A scalar pulls out of the sum on the left. -/
theorem esum_mul_left (c : Ext p ν) (f : Nat → Ext p ν) (n : Nat) : c * esum f n = esum (fun j => c * f j) n := by
  apply FRC.Extension.Ext.ext
  · show c.re * sumRange (fun j => (f j).re) n + ν * (c.im * sumRange (fun j => (f j).im) n) =
      sumRange (fun j => c.re * (f j).re + ν * (c.im * (f j).im)) n
    rw [sum_add, ← sum_mul_left, ← sum_mul_left, ← sum_mul_left]
  · show c.re * sumRange (fun j => (f j).im) n + c.im * sumRange (fun j => (f j).re) n =
      sumRange (fun j => c.re * (f j).im + c.im * (f j).re) n
    rw [sum_add, ← sum_mul_left, ← sum_mul_left]

theorem esum_mul_right (c : Ext p ν) (f : Nat → Ext p ν) (n : Nat) : esum f n * c = esum (fun j => f j * c) n := by
  rw [FRC.Extension.Ext.mul_comm, esum_mul_left]; exact esum_congr n fun j _ => FRC.Extension.Ext.mul_comm _ _

/-- The sum over the register is invariant under the shift of its index (the cycle's `sum_shift`). -/
theorem esum_shift (f : Nat → Ext p ν) (s : Nat) : esum (fun j => f ((j + s) % p)) p = esum f p :=
  FRC.Extension.Ext.ext (Cycle.sum_shift p (Pos.pos : 0 < p) (fun j => (f j).re) s) (Cycle.sum_shift p (Pos.pos : 0 < p) (fun j => (f j).im) s)

end sums

/-! ## The Hermitian form (8:C2) -/
section form

/-- A field on the register with values in `K`, read on `[0, p)`. -/
abbrev Fld (p : Nat) [Pos p] (ν : Shell p) := Nat → Ext p ν

/-- The Hermitian form `⟨ψ, φ⟩ = Σ_{x<p} ψ̄(x) φ(x)`, antilinear in the first slot. -/
def herm (ψ φ : Fld p ν) : Ext p ν := esum (fun j => FRC.Extension.Ext.conj (ψ j) * φ j) p

/-- 8:C2 — the form is Hermitian: `conj ⟨ψ, φ⟩ = ⟨φ, ψ⟩`. -/
theorem herm_star (ψ φ : Fld p ν) : FRC.Extension.Ext.conj (herm ψ φ) = herm φ ψ := by
  unfold herm; rw [esum_conj]
  exact esum_congr p fun j _ => by rw [FRC.Extension.Ext.conj_mul, FRC.Extension.Ext.conj_conj, FRC.Extension.Ext.mul_comm]

theorem herm_add_right (ψ φ φ' : Fld p ν) : herm ψ (fun j => φ j + φ' j) = herm ψ φ + herm ψ φ' := by
  unfold herm; rw [← esum_add]; exact esum_congr p fun j _ => mul_add _ _ _

theorem herm_add_left (ψ ψ' φ : Fld p ν) : herm (fun j => ψ j + ψ' j) φ = herm ψ φ + herm ψ' φ := by
  unfold herm; rw [← esum_add]
  exact esum_congr p fun j _ => by
    show FRC.Extension.Ext.conj (ψ j + ψ' j) * φ j = _
    rw [conj_add, add_mul]

theorem herm_neg_right (ψ φ : Fld p ν) : herm ψ (fun j => -(φ j)) = -(herm ψ φ) := by
  unfold herm; rw [← esum_neg]; exact esum_congr p fun j _ => (mul_neg _ _).symm

theorem herm_neg_left (ψ φ : Fld p ν) : herm (fun j => -(ψ j)) φ = -(herm ψ φ) := by
  unfold herm; rw [← esum_neg]
  exact esum_congr p fun j _ => by
    show FRC.Extension.Ext.conj (-(ψ j)) * φ j = _
    rw [conj_neg, ← neg_mul]

theorem herm_smul_right (c : Ext p ν) (ψ φ : Fld p ν) : herm ψ (fun j => c * φ j) = c * herm ψ φ := by
  unfold herm; rw [esum_mul_left]
  exact esum_congr p fun j _ => by
    show FRC.Extension.Ext.conj (ψ j) * (c * φ j) = c * (FRC.Extension.Ext.conj (ψ j) * φ j)
    rw [← FRC.Extension.Ext.mul_assoc, FRC.Extension.Ext.mul_comm (FRC.Extension.Ext.conj (ψ j)) c,
      FRC.Extension.Ext.mul_assoc]

theorem herm_smul_left (c : Ext p ν) (ψ φ : Fld p ν) : herm (fun j => c * ψ j) φ = FRC.Extension.Ext.conj c * herm ψ φ := by
  unfold herm; rw [esum_mul_left]
  exact esum_congr p fun j _ => by
    show FRC.Extension.Ext.conj (c * ψ j) * φ j = _
    rw [FRC.Extension.Ext.conj_mul, FRC.Extension.Ext.mul_assoc]

/-- The delta field at the site `x`. -/
def delta (x : Nat) : Fld p ν := fun j => if j = x then 1 else 0

theorem herm_delta (ψ : Fld p ν) {x : Nat} (hx : x < p) : herm ψ (delta x) = FRC.Extension.Ext.conj (ψ x) := by
  unfold herm
  rw [esum_eq_single (fun j => FRC.Extension.Ext.conj (ψ j) * delta x j) hx]
  · show FRC.Extension.Ext.conj (ψ x) * (if x = x then 1 else 0) = FRC.Extension.Ext.conj (ψ x)
    rw [ite_eq_left rfl]; exact FRC.Extension.Ext.mul_one _
  · intro j _ hne
    show FRC.Extension.Ext.conj (ψ j) * (if j = x then 1 else 0) = 0
    rw [ite_eq_right hne]; exact mul_zero _

/-- 8:C2 — the form is nondegenerate: a field orthogonal to every field vanishes at every site of the register
(its conjugate against the delta field is the site's value). -/
theorem herm_nondegenerate (ψ : Fld p ν) (h : ∀ φ : Fld p ν, herm ψ φ = 0) : ∀ x, x < p → ψ x = 0 := by
  intro x hx
  have e := h (delta x)
  rw [herm_delta ψ hx] at e
  rw [← FRC.Extension.Ext.conj_conj (ψ x), e, conj_zero]

end form

/-! ## Translations, the Laplacian and the Hamiltonians (8:C8, C9, C11) -/
section translations

/-- The translation `(T_s ψ)(x) = ψ(x + s)` on the register. -/
def translate (s : Nat) (ψ : Fld p ν) : Fld p ν := fun j => ψ ((j + s) % p)

/-- 8:C8 — translations are unitary: `⟨T_s ψ, T_s φ⟩ = ⟨ψ, φ⟩`. -/
theorem herm_translate (s : Nat) (ψ φ : Fld p ν) : herm (translate s ψ) (translate s φ) = herm ψ φ :=
  esum_shift (fun j => FRC.Extension.Ext.conj (ψ j) * φ j) s

/-- `((j + s) % p + (p − s)) % p = j` for `j < p` and `s < p`: the shift and its opposite cancel on the register. -/
theorem shift_cancel {s j : Nat} (hs : s < p) (hj : j < p) : ((j + s) % p + (p - s)) % p = j := by
  have h := FRC.Nat.add_mul_mod_self_left j 1 p (Pos.pos : 0 < p)
  rw [Nat.mul_one] at h
  rw [FRC.Nat.mod_add_mod _ _ _ (Pos.pos : 0 < p), Nat.add_assoc, FRC.Nat.add_sub_of_le (Nat.le_of_lt hs), Nat.add_comm j p,
    h, FRC.Nat.mod_eq_of_lt hj]

/-- 8:C8 — the adjoint of a translation is the opposite translation: `⟨T_s ψ, φ⟩ = ⟨ψ, T_{p−s} φ⟩` for `s < p`. -/
theorem herm_translate_adjoint {s : Nat} (hs : s < p) (ψ φ : Fld p ν) :
    herm (translate s ψ) φ = herm ψ (translate (p - s) φ) := by
  unfold herm translate
  rw [← esum_shift (fun j => FRC.Extension.Ext.conj (ψ j) * φ ((j + (p - s)) % p)) s]
  apply esum_congr p
  intro j hj
  show FRC.Extension.Ext.conj (ψ ((j + s) % p)) * φ j = FRC.Extension.Ext.conj (ψ ((j + s) % p)) * φ (((j + s) % p + (p - s)) % p)
  rw [shift_cancel hs hj]

/-- The Laplacian `Δψ = T_1 ψ + T_{p−1} ψ − 2ψ` (the second difference on the cycle). -/
def laplacian (ψ : Fld p ν) : Fld p ν := fun j => translate 1 ψ j + translate (p - 1) ψ j + -(ψ j + ψ j)

theorem sub_one_lt : p - 1 < p := Nat.sub_lt (Pos.pos : 0 < p) Nat.one_pos

omit [Pos p] in
/-- `p − (p − 1) = 1` on a register of more than one site. -/
theorem sub_sub_one (h2 : 1 < p) : p - (p - 1) = 1 := by
  have h1 : p - 1 + 1 = p := FRC.Nat.sub_add_cancel (Nat.le_of_lt h2)
  calc p - (p - 1) = p - 1 + 1 - (p - 1) := by rw [h1]
    _ = 1 := FRC.Nat.add_sub_cancel_left _ _

/-- 8:C9 — the Laplacian is self-adjoint, each of its summands being self-adjoint: `T_1` and `T_{p−1}` are
adjoint to each other and the diagonal term is real. -/
theorem herm_laplacian (h2 : 1 < p) (ψ φ : Fld p ν) : herm (laplacian ψ) φ = herm ψ (laplacian φ) := by
  unfold laplacian
  rw [herm_add_left, herm_add_left, herm_neg_left, herm_add_left, herm_add_right, herm_add_right, herm_neg_right,
    herm_add_right, herm_translate_adjoint h2, herm_translate_adjoint sub_one_lt,
    sub_sub_one h2, add_comm (herm ψ (translate (p - 1) φ))]

/-- The finite Hamiltonian `Hψ = −ϰ Δψ + V ψ` of stiffness `ϰ` and potential `V`. -/
def hamiltonian (ϰ : Ext p ν) (V : Fld p ν) (ψ : Fld p ν) : Fld p ν :=
  fun j => -(ϰ * laplacian ψ j) + V j * ψ j

/-- A real potential is symmetric for the form: `⟨Vψ, φ⟩ = ⟨ψ, Vφ⟩` when `conj (V x) = V x` at every site. -/
theorem herm_potential (V : Fld p ν) (hV : ∀ j, FRC.Extension.Ext.conj (V j) = V j) (ψ φ : Fld p ν) :
    herm (fun j => V j * ψ j) φ = herm ψ (fun j => V j * φ j) := by
  unfold herm
  apply esum_congr p
  intro j _
  show FRC.Extension.Ext.conj (V j * ψ j) * φ j = FRC.Extension.Ext.conj (ψ j) * (V j * φ j)
  rw [FRC.Extension.Ext.conj_mul, hV j, FRC.Extension.Ext.mul_assoc, ← FRC.Extension.Ext.mul_assoc,
    FRC.Extension.Ext.mul_comm (V j) (FRC.Extension.Ext.conj (ψ j)), FRC.Extension.Ext.mul_assoc]

/-- 8:C11 — every finite Hamiltonian is self-adjoint: the Laplacian is, the potential is real, and the stiffness
is Frobenius-fixed. -/
theorem herm_hamiltonian (h2 : 1 < p) (ϰ : Ext p ν) (hϰ : FRC.Extension.Ext.conj ϰ = ϰ) (V : Fld p ν) (hV : ∀ j, FRC.Extension.Ext.conj (V j) = V j)
    (ψ φ : Fld p ν) : herm (hamiltonian ϰ V ψ) φ = herm ψ (hamiltonian ϰ V φ) := by
  unfold hamiltonian
  rw [herm_add_left, herm_add_right, herm_neg_left, herm_neg_right, herm_smul_left, herm_smul_right, hϰ,
    herm_laplacian h2, herm_potential V hV]

end translations

/-! ## Frame covariance: the pullback intertwines the translations and the differences (8:C13, D7) -/
section covariance

/-- A point of the coordinate shell `𝔽_p⁴`. -/
structure Pt (p : Nat) [Pos p] where
  t : Shell p
  x : Shell p
  y : Shell p
  z : Shell p

theorem Pt.ext {a b : Pt p} (ht : a.t = b.t) (hx : a.x = b.x) (hy : a.y = b.y) (hz : a.z = b.z) : a = b := by
  cases a; cases b; cases ht; cases hx; cases hy; cases hz; rfl

instance : Add (Pt p) := ⟨fun a b => ⟨a.t + b.t, a.x + b.x, a.y + b.y, a.z + b.z⟩⟩
instance : Neg (Pt p) := ⟨fun a => ⟨-a.t, -a.x, -a.y, -a.z⟩⟩
instance : OfNat (Pt p) 0 := ⟨⟨0, 0, 0, 0⟩⟩

theorem Pt.zero_add (a : Pt p) : (0 : Pt p) + a = a :=
  Pt.ext (Shell.zero_add _) (Shell.zero_add _) (Shell.zero_add _) (Shell.zero_add _)
theorem Pt.add_neg (a : Pt p) : a + -a = 0 :=
  Pt.ext (Shell.add_neg _) (Shell.add_neg _) (Shell.add_neg _) (Shell.add_neg _)
theorem Pt.add_right_cancel {a b c : Pt p} (h : a + c = b + c) : a = b :=
  Pt.ext (Shell.add_right_cancel (congrArg Pt.t h)) (Shell.add_right_cancel (congrArg Pt.x h))
    (Shell.add_right_cancel (congrArg Pt.y h)) (Shell.add_right_cancel (congrArg Pt.z h))
theorem Pt.neg_eq_of_add_eq_zero {a b : Pt p} (h : a + b = 0) : -a = b :=
  Pt.ext (Shell.neg_eq_of_add_eq_zero (congrArg Pt.t h)) (Shell.neg_eq_of_add_eq_zero (congrArg Pt.x h))
    (Shell.neg_eq_of_add_eq_zero (congrArg Pt.y h)) (Shell.neg_eq_of_add_eq_zero (congrArg Pt.z h))

/-- A spinor-free field on the coordinate shell. -/
abbrev Fld4 (p : Nat) [Pos p] (ν : Shell p) := Pt p → Ext p ν

/-- A change of frame: an additive bijection `A` of the points, given with its inverse (the boosts of `Plane`,
read on the coordinates, are such changes). -/
structure Change (p : Nat) [Pos p] where
  A : Pt p → Pt p
  Ainv : Pt p → Pt p
  inv_left : ∀ q, Ainv (A q) = q
  inv_right : ∀ q, A (Ainv q) = q
  add : ∀ q r, A (q + r) = A q + A r

theorem Change.map_zero (C : Change p) : C.A 0 = 0 := by
  have h := C.add 0 0
  rw [Pt.zero_add] at h
  exact (Pt.add_right_cancel ((Pt.zero_add (C.A 0)).trans h)).symm

theorem Change.map_neg (C : Change p) (e : Pt p) : C.A (-e) = -(C.A e) := by
  have h := C.add e (-e)
  rw [Pt.add_neg, C.map_zero] at h
  exact (Pt.neg_eq_of_add_eq_zero h.symm).symm

/-- The inverse of a change is additive against the image: `A⁻¹(q + A e) = A⁻¹ q + e`. -/
theorem Change.inv_add (C : Change p) (q e : Pt p) : C.Ainv (q + C.A e) = C.Ainv q + e := by
  have h : q + C.A e = C.A (C.Ainv q + e) := by rw [C.add, C.inv_right]
  rw [h, C.inv_left]

/-- The pullback `(A_* ψ)(q) = ψ(A⁻¹ q)` of a field under the change of frame. -/
def pullback (C : Change p) (ψ : Fld4 p ν) : Fld4 p ν := fun q => ψ (C.Ainv q)

/-- The translation `(T_e ψ)(q) = ψ(q + e)` on the coordinate shell. -/
def translate4 (e : Pt p) (ψ : Fld4 p ν) : Fld4 p ν := fun q => ψ (q + e)

/-- The forward difference `(∂_e ψ)(q) = ψ(q + e) − ψ(q)`. -/
def fwdDiff (e : Pt p) (ψ : Fld4 p ν) : Fld4 p ν := fun q => translate4 e ψ q + -(ψ q)

/-- The symmetric difference `(∂^s_e ψ)(q) = ψ(q + e) − ψ(q − e)`. -/
def symDiff (e : Pt p) (ψ : Fld4 p ν) : Fld4 p ν := fun q => translate4 e ψ q + -(translate4 (-e) ψ q)

/-- 8:C13, 8:D7 — the pullback intertwines the translations: `T_{Ae} (A_* ψ) = A_* (T_e ψ)` at every point. -/
theorem pullback_translate (C : Change p) (e : Pt p) (ψ : Fld4 p ν) (q : Pt p) :
    translate4 (C.A e) (pullback C ψ) q = pullback C (translate4 e ψ) q := by
  show ψ (C.Ainv (q + C.A e)) = ψ (C.Ainv q + e)
  rw [C.inv_add]

/-- 8:C13, 8:D7 — the pullback intertwines the forward differences: `∂_{Ae} (A_* ψ) = A_* (∂_e ψ)` at every
point, so the transported difference operator is the difference along the transported direction. -/
theorem pullback_fwdDiff (C : Change p) (e : Pt p) (ψ : Fld4 p ν) (q : Pt p) :
    fwdDiff (C.A e) (pullback C ψ) q = pullback C (fwdDiff e ψ) q := by
  show translate4 (C.A e) (pullback C ψ) q + -(pullback C ψ q) = translate4 e ψ (C.Ainv q) + -(ψ (C.Ainv q))
  rw [pullback_translate]; rfl

/-- 8:C13, 8:D7, 8:D8 — the pullback intertwines the symmetric differences: `∂^s_{Ae} (A_* ψ) = A_* (∂^s_e ψ)` at
every point (the change is additive, so it sends `−e` to `−Ae`). -/
theorem pullback_symDiff (C : Change p) (e : Pt p) (ψ : Fld4 p ν) (q : Pt p) :
    symDiff (C.A e) (pullback C ψ) q = pullback C (symDiff e ψ) q := by
  show translate4 (C.A e) (pullback C ψ) q + -(translate4 (-(C.A e)) (pullback C ψ) q) =
    translate4 e ψ (C.Ainv q) + -(translate4 (-e) ψ (C.Ainv q))
  rw [← C.map_neg, pullback_translate, pullback_translate]; rfl

end covariance

end FRC.Dirac.Hermitian
