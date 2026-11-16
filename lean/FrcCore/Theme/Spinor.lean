import FrcCore.Theme.Packed
import FrcCore.Theme.Unipotent
import FrcCore.Theme.Hermitian
import FrcCore.Theme.Dirac
import FrcCore.Theme.Unitary

/-!
# The spinor file of 8-dirac — the matrices as an operator ring, and the decided witnesses, no axioms

The sixth file of the dirac theme (5 November 2026, the core-proof programme): the `n × n` matrices over the coefficient
field `K = 𝔽_p(√ν)`, read as functions of two indices below `n`, form an `OpRing` (`MatE p ν n`) — two matrices are
congruent when their entries agree on the range, so no function extensionality is needed — with the conjugate transpose
as an `Adjoint`. The general theorems of the operator layer therefore hold for the Dirac operators of the paper as
matrices: the Cayley step of a self-adjoint matrix is unitary (C4), the nilpotent shift (D10, X3), the factorisation
(D3, D18), the transported Clifford relations (D17), the unipotent translations (F7). The decided witnesses on the
standard shells `𝔽₁₃`, `𝔽₁₇₃` (and `𝔽₁₅₄₉` where cheap), in the list form of the theme file: the translation and the
symmetric difference nilpotent on the cycle (`(T − 1)^p = 0`, `(∇^s)^p = 0`, by squaring), the Cayley step of `−Δ`
unitary, the factorisation `(𝒟^s − m)(𝒟^s + m) = ν(∇^s)² ⊗ I₄ − m²` on the `52 × 52` matrices of `0+1` at `p = 13`, and
the mixed step `−Δ + V_id` of E8 with `U^{13} ≠ I`, `U^{14} ≠ I`, `U^{182} ≠ I` on `𝔽₁₃` (its exact order, `(13¹³ + 1)/2`,
is the package's certificate). No axioms.
-/

namespace FRC.Dirac.Spinor

open FRC FRC.Shell FRC.Extension FRC.Dirac.Operator FRC.Dirac.Hermitian

variable {p : Nat} [Pos p] {ν : Shell p}

/-! ## The matrix ring -/

/-- An `n × n` matrix over `K`, as a function of two indices read below `n`. -/
structure MatE (p : Nat) [Pos p] (ν : Shell p) (n : Nat) where
  f : Nat → Nat → Ext p ν

namespace MatE

variable {n : Nat}

instance : Add (MatE p ν n) := ⟨fun A B => ⟨fun i j => A.f i j + B.f i j⟩⟩
instance : Neg (MatE p ν n) := ⟨fun A => ⟨fun i j => -(A.f i j)⟩⟩
instance : Mul (MatE p ν n) := ⟨fun A B => ⟨fun i j => esum (fun k => A.f i k * B.f k j) n⟩⟩
instance : OfNat (MatE p ν n) 0 := ⟨⟨fun _ _ => 0⟩⟩
instance : OfNat (MatE p ν n) 1 := ⟨⟨fun i j => if i = j then 1 else 0⟩⟩

theorem add_f (A B : MatE p ν n) (i j : Nat) : (A + B).f i j = A.f i j + B.f i j := rfl
theorem neg_f (A : MatE p ν n) (i j : Nat) : (-A).f i j = -(A.f i j) := rfl
theorem mul_f (A B : MatE p ν n) (i j : Nat) : (A * B).f i j = esum (fun k => A.f i k * B.f k j) n := rfl
theorem zero_f (i j : Nat) : (0 : MatE p ν n).f i j = 0 := rfl
theorem one_f (i j : Nat) : (1 : MatE p ν n).f i j = if i = j then 1 else 0 := rfl

/-- Congruence: equal entries on the range. -/
def eq (A B : MatE p ν n) : Prop := ∀ i, i < n → ∀ j, j < n → A.f i j = B.f i j

/-- Double sums in the extension commute. -/
theorem esum_comm (F : Nat → Nat → Ext p ν) (m : Nat) : ∀ k,
    esum (fun i => esum (fun j => F i j) m) k = esum (fun j => esum (fun i => F i j) k) m
  | 0 => (esum_zero_of _ m fun _ _ => rfl).symm
  | k + 1 => by rw [esum_succ, esum_comm F m k, ← esum_add]; rfl

theorem mul_assoc_f (A B C : MatE p ν n) (i j : Nat) : (A * B * C).f i j = (A * (B * C)).f i j := by
  show esum (fun k => esum (fun l => A.f i l * B.f l k) n * C.f k j) n =
    esum (fun l => A.f i l * esum (fun k => B.f l k * C.f k j) n) n
  calc esum (fun k => esum (fun l => A.f i l * B.f l k) n * C.f k j) n
      = esum (fun k => esum (fun l => A.f i l * B.f l k * C.f k j) n) n :=
        esum_congr n fun k _ => esum_mul_right _ _ n
    _ = esum (fun l => esum (fun k => A.f i l * B.f l k * C.f k j) n) n := esum_comm _ n n
    _ = esum (fun l => A.f i l * esum (fun k => B.f l k * C.f k j) n) n :=
        esum_congr n fun l _ => by
          rw [esum_mul_left]
          exact esum_congr n fun k _ => FRC.Extension.Ext.mul_assoc _ _ _

theorem one_mul_f (A : MatE p ν n) {i j : Nat} (hi : i < n) : (1 * A).f i j = A.f i j := by
  show esum (fun k => (if i = k then 1 else 0) * A.f k j) n = A.f i j
  rw [esum_eq_single _ hi]
  · show (if i = i then 1 else 0) * A.f i j = A.f i j
    rw [ite_eq_left rfl]; exact FRC.Extension.Ext.one_mul _
  · intro k _ hk
    show (if i = k then 1 else 0) * A.f k j = 0
    rw [ite_eq_right (fun e => hk e.symm)]; exact Hermitian.zero_mul _

theorem mul_one_f (A : MatE p ν n) {i j : Nat} (hj : j < n) : (A * 1).f i j = A.f i j := by
  show esum (fun k => A.f i k * if k = j then 1 else 0) n = A.f i j
  rw [esum_eq_single _ hj]
  · show A.f i j * (if j = j then 1 else 0) = A.f i j
    rw [ite_eq_left rfl]; exact FRC.Extension.Ext.mul_one _
  · intro k _ hk
    show A.f i k * (if k = j then 1 else 0) = 0
    rw [ite_eq_right hk]; exact Hermitian.mul_zero _

instance instOpRing : OpRing (MatE p ν n) where
  eq := eq
  refl := fun _ _ _ _ _ => rfl
  symm := fun h i hi j hj => (h i hi j hj).symm
  trans := fun h h' i hi j hj => (h i hi j hj).trans (h' i hi j hj)
  add_congr := fun h h' i hi j hj => by rw [add_f, add_f, h i hi j hj, h' i hi j hj]
  mul_congr := fun h h' i hi j hj => by
    rw [mul_f, mul_f]; exact esum_congr n fun k hk => by rw [h i hi k hk, h' k hk j hj]
  neg_congr := fun h i hi j hj => by rw [neg_f, neg_f, h i hi j hj]
  add_comm := fun _ _ _ _ _ _ => Hermitian.add_comm _ _
  add_assoc := fun _ _ _ _ _ _ _ => Hermitian.add_assoc _ _ _
  zero_add := fun _ _ _ _ _ => Hermitian.zero_add _
  add_neg := fun _ _ _ _ _ => Hermitian.add_neg _
  mul_assoc := fun A B C i _ j _ => mul_assoc_f A B C i j
  one_mul := fun A i hi j _ => one_mul_f A hi
  mul_one := fun A i _ j hj => mul_one_f A hj
  left_distrib := fun A B C i _ j _ => by
    show esum (fun k => A.f i k * (B.f k j + C.f k j)) n =
      esum (fun k => A.f i k * B.f k j) n + esum (fun k => A.f i k * C.f k j) n
    rw [← esum_add]; exact esum_congr n fun k _ => Hermitian.mul_add _ _ _
  right_distrib := fun A B C i _ j _ => by
    show esum (fun k => (A.f i k + B.f i k) * C.f k j) n =
      esum (fun k => A.f i k * C.f k j) n + esum (fun k => B.f i k * C.f k j) n
    rw [← esum_add]; exact esum_congr n fun k _ => Hermitian.add_mul _ _ _

/-! ### The conjugate transpose is an adjoint -/

/-- The conjugate transpose `A† = conj Aᵀ`. -/
def dagger (A : MatE p ν n) : MatE p ν n := ⟨fun i j => FRC.Extension.Ext.conj (A.f j i)⟩

theorem dagger_f (A : MatE p ν n) (i j : Nat) : (dagger A).f i j = FRC.Extension.Ext.conj (A.f j i) := rfl

/-- 8:C4 — the conjugate transpose is an anti-automorphism of the matrix ring: `(AB)† = B†A†`, `(A+B)† = A†+B†`,
`1† = 1`, `(−A)† = −A†`, respecting the congruence. -/
theorem adjoint_dagger : Adjoint (dagger : MatE p ν n → MatE p ν n) where
  congr := fun h i hi j hj => by rw [dagger_f, dagger_f, h j hj i hi]
  mul := fun A B i _ j _ => by
    show FRC.Extension.Ext.conj (esum (fun k => A.f j k * B.f k i) n) =
      esum (fun k => FRC.Extension.Ext.conj (B.f k i) * FRC.Extension.Ext.conj (A.f j k)) n
    rw [esum_conj]
    exact esum_congr n fun k _ => by rw [FRC.Extension.Ext.conj_mul, FRC.Extension.Ext.mul_comm]
  add := fun A B i _ j _ => Hermitian.conj_add _ _
  one := fun i _ j _ => by
    show FRC.Extension.Ext.conj (if j = i then 1 else 0) = if i = j then 1 else 0
    cases Nat.decEq j i with
    | isTrue h => rw [ite_eq_left h, ite_eq_left h.symm]; exact Hermitian.conj_one
    | isFalse h => rw [ite_eq_right h, ite_eq_right (fun e => h e.symm)]; exact Hermitian.conj_zero
  neg := fun A i _ j _ => Hermitian.conj_neg _

/-- 8:C4, 8:D10 — the `X`-adjoint `A ↦ X' A† X` of a unit `X` (`X X' ≈ 1`) is an adjoint too: the spinor form's
adjoint is an anti-automorphism, so the Cayley step of an `X`-self-adjoint operator preserves the `X`-form
(`cayley_unitary` with this adjoint). -/
theorem adjoint_twist {X X' : MatE p ν n} (hX : Inverse X X') :
    Adjoint (fun A : MatE p ν n => X' * dagger A * X) :=
  Adjoint.twist adjoint_dagger hX

/-! ### The translation and the characteristic -/

/-- The translation `T` on `n` sites: `(T ψ)(i) = ψ(i + 1)`, the matrix `T_{ij} = [j = i + 1 mod n]`. -/
def shift (n : Nat) : MatE p ν n := ⟨fun i j => if j = (i + 1) % n then 1 else 0⟩

/-- `T^k` is the translation by `k`: `(T^k)_{ij} = [j = i + k mod n]`, on the range. -/
theorem shift_pow (hn : 0 < n) : ∀ k, opow (shift n : MatE p ν n) k ≈ ⟨fun i j => if j = (i + k) % n then 1 else 0⟩
  | 0 => fun i hi j _ => by
    show (if i = j then 1 else 0) = if j = (i + 0) % n then 1 else 0
    rw [Nat.add_zero, FRC.Nat.mod_eq_of_lt hi]
    cases Nat.decEq i j with
    | isTrue h => rw [ite_eq_left h, ite_eq_left h.symm]
    | isFalse h => rw [ite_eq_right h, ite_eq_right (fun e => h e.symm)]
  | k + 1 => by
    refine OpRing.trans (mul_congr_left (shift n) (shift_pow hn k)) ?_
    intro i hi j _
    show esum (fun l => (if l = (i + k) % n then 1 else 0) * (if j = (l + 1) % n then 1 else 0)) n =
      if j = (i + (k + 1)) % n then 1 else 0
    rw [esum_eq_single _ (FRC.Nat.mod_lt' (i + k) hn)]
    · show (if (i + k) % n = (i + k) % n then 1 else 0) * (if j = ((i + k) % n + 1) % n then 1 else 0) =
        if j = (i + (k + 1)) % n then 1 else 0
      rw [ite_eq_left rfl, FRC.Extension.Ext.one_mul, FRC.Nat.mod_add_mod _ _ _ hn, Nat.add_assoc]
    · intro l _ hl
      show (if l = (i + k) % n then 1 else 0) * (if j = (l + 1) % n then 1 else 0) = 0
      rw [ite_eq_right hl]; exact Hermitian.zero_mul _

/-- 8:F7 — the translation on the cycle of `p` sites has `T^p ≈ 1`, on every shell. -/
theorem shift_pow_self : opow (shift p : MatE p ν p) p ≈ 1 := by
  refine OpRing.trans (shift_pow Pos.pos p) ?_
  intro i hi j _
  show (if j = (i + p) % p then 1 else 0) = if i = j then 1 else 0
  have h := FRC.Nat.add_mul_mod_self_left i 1 p Pos.pos
  rw [Nat.mul_one, Nat.add_comm p i] at h
  rw [h, FRC.Nat.mod_eq_of_lt hi]
  cases Nat.decEq i j with
  | isTrue e => rw [ite_eq_left e, ite_eq_left e.symm]
  | isFalse e => rw [ite_eq_right e, ite_eq_right (fun e' => e e'.symm)]

/-- `k • 1` is the scalar `k` on the diagonal. -/
theorem nsmul_one_f : ∀ k, ∀ i j, (nsmul k (1 : MatE p ν n)).f i j = if i = j then FRC.Extension.Ext.ofShell (ofNat k) else 0
  | 0, i, j => by
    show (0 : Ext p ν) = if i = j then FRC.Extension.Ext.ofShell (ofNat 0) else 0
    cases Nat.decEq i j with
    | isTrue e => rw [ite_eq_left e]; exact FRC.Extension.Ext.ext rfl rfl
    | isFalse e => rw [ite_eq_right e]
  | k + 1, i, j => by
    show (nsmul k (1 : MatE p ν n)).f i j + (if i = j then 1 else 0) = if i = j then FRC.Extension.Ext.ofShell (ofNat (k + 1)) else 0
    rw [nsmul_one_f k i j]
    cases Nat.decEq i j with
    | isTrue e =>
      rw [ite_eq_left e, ite_eq_left e, ite_eq_left e]
      apply FRC.Extension.Ext.ext
      · show ofNat k + 1 = ofNat (k + 1)
        apply Shell.ext
        show (k % p + 1 % p) % p = (k + 1) % p
        rw [← FRC.Nat.add_mod _ _ _ Pos.pos]
      · exact Shell.add_zero 0
    | isFalse e => rw [ite_eq_right e, ite_eq_right e, ite_eq_right e]; exact Hermitian.add_zero 0

/-- 8:F7, 8:D10 — the matrix ring has characteristic `p`: `p • 1 ≈ 0`. -/
theorem char_p : nsmul p (1 : MatE p ν n) ≈ 0 := fun i _ j _ => by
  rw [nsmul_one_f, ofNat_self]
  cases Nat.decEq i j with
  | isTrue e => rw [ite_eq_left e]; rfl
  | isFalse e => rw [ite_eq_right e]; rfl

/-- 8:F7 — the translations are unipotent on every frame: `(T − 1)^p ≈ 0` on the cycle of `p` sites, by
`translation_nilpotent` with `T^p ≈ 1` and the characteristic. -/
theorem translation_unipotent {κ : Nat} {g : Shell p} (F : Frame p κ g) :
    opow (shift p + -1 : MatE p ν p) p ≈ 0 :=
  translation_nilpotent F char_p shift_pow_self

/-- 8:D10, 8:X3 — the symmetric difference `∇^s = h (T − T⁻¹)` is nilpotent on every frame, `(∇^s)^p ≈ 0`:
`(T − T⁻¹)^p ≈ T^p + (−T⁻¹)^p ≈ 1 − 1` by the Frobenius, `T⁻¹ = T^{p−1}`, and the central `h` factors out. -/
theorem symdiff_nilpotent {κ : Nat} {g : Shell p} (F : Frame p κ g) {h : MatE p ν p} (hh : Central h) :
    opow (h * (shift p + -(opow (shift p) (p - 1))) : MatE p ν p) p ≈ 0 := by
  have hT : Comm (shift p : MatE p ν p) (-(opow (shift p) (p - 1))) :=
    Comm.neg_right (opow_self_comm (shift p) (p - 1)).symm
  have hinv : opow (opow (shift p : MatE p ν p) (p - 1)) p ≈ 1 := by
    have e : (p - 1) * p = p * (p - 1) := Nat.mul_comm _ _
    calc opow (opow (shift p : MatE p ν p) (p - 1)) p ≈ opow (shift p) ((p - 1) * p) := eq_symm (opow_mul _ _ _)
      _ ≈ opow (shift p) (p * (p - 1)) := eq_of_eq (by rw [e])
      _ ≈ opow (opow (shift p) p) (p - 1) := opow_mul _ _ _
      _ ≈ opow 1 (p - 1) := opow_congr shift_pow_self _
      _ ≈ 1 := opow_one_left _
  have hodd : opow (-1 : MatE p ν p) p ≈ -1 := by
    have e : p = 2 * (2 * κ) + 1 := by rw [F.cap, ← Nat.mul_assoc]
    exact OpRing.trans (eq_of_eq (congrArg (opow (-1 : MatE p ν p)) e)) (opow_neg_one_odd _)
  have hneg : opow (-(opow (shift p : MatE p ν p) (p - 1))) p ≈ -1 :=
    calc opow (-(opow (shift p : MatE p ν p) (p - 1))) p ≈ opow (-1 * opow (shift p) (p - 1)) p :=
          opow_congr (eq_symm (neg_one_mul _)) p
      _ ≈ opow (-1) p * opow (opow (shift p) (p - 1)) p := mul_opow (Central.neg Central.one _) p
      _ ≈ -1 * 1 := OpRing.mul_congr hodd hinv
      _ ≈ -1 := OpRing.mul_one _
  calc opow (h * (shift p + -(opow (shift p) (p - 1)))) p
      ≈ opow h p * opow (shift p + -(opow (shift p) (p - 1))) p := mul_opow (hh _) p
    _ ≈ opow h p * (opow (shift p) p + opow (-(opow (shift p) (p - 1))) p) :=
        mul_congr_right _ (frobenius_add F char_p hT)
    _ ≈ opow h p * (1 + -1) := mul_congr_right _ (OpRing.add_congr shift_pow_self hneg)
    _ ≈ opow h p * 0 := mul_congr_right _ (OpRing.add_neg 1)
    _ ≈ 0 := Operator.mul_zero _

/-! ### The exact index of the symmetric difference (D20) -/
/-- The entries of an operator sum are the sums of the entries. -/
theorem osum_f (f : Nat → MatE p ν n) (i j : Nat) : ∀ m, (osum f m).f i j = esum (fun k => (f k).f i j) m
  | 0 => rfl
  | m + 1 => by
    show (osum f m + f m).f i j = esum (fun k => (f k).f i j) m + (f m).f i j
    rw [add_f, osum_f f i j m]

/-- The sum of the translates of the cycle has the entry `1` at `(0, 0)`: `(Σ_{k<p} T^k)_{00} = 1`. -/
theorem geom_shift_f00 : (geom (shift p : MatE p ν p) p).f 0 0 = 1 := by
  show (osum (fun k => opow (shift p : MatE p ν p) k) p).f 0 0 = 1
  rw [osum_f]
  have hk : ∀ k, k < p → (opow (shift p : MatE p ν p) k).f 0 0 = if k = 0 then (1 : Ext p ν) else 0 := fun k hk => by
    rw [shift_pow Pos.pos k 0 Pos.pos 0 Pos.pos]
    show (if 0 = (0 + k) % p then (1 : Ext p ν) else 0) = if k = 0 then 1 else 0
    rw [Nat.zero_add, FRC.Nat.mod_eq_of_lt hk]
    cases Nat.decEq k 0 with
    | isTrue e => rw [ite_eq_left e.symm, ite_eq_left e]
    | isFalse e => rw [ite_eq_right (fun e' => e e'.symm), ite_eq_right e]
  rw [esum_congr p hk, esum_eq_single _ (Pos.pos : 0 < p) (fun k _ hk0 => by rw [ite_eq_right hk0])]
  exact ite_eq_left rfl

/-- The sum of the translates is not congruent to zero. -/
theorem geom_shift_ne_zero {κ : Nat} {g : Shell p} (F : Frame p κ g) : ¬ (geom (shift p : MatE p ν p) p ≈ 0) := fun h => by
  have e := h 0 Pos.pos 0 Pos.pos
  rw [geom_shift_f00] at e
  exact F.one_ne_zero (FRC.Extension.Ext.re_congr e)

/-- `T^{p−1}` is the inverse of the translation `T`. -/
theorem shift_inverse : Inverse (shift p : MatE p ν p) (opow (shift p) (p - 1)) := by
  have hp : p = (p - 1) + 1 := (FRC.Nat.sub_add_cancel (Pos.pos : 0 < p)).symm
  have h1 : opow (shift p : MatE p ν p) (p - 1) * shift p ≈ 1 :=
    eq_trans (eq_of_eq (by rw [← opow_succ, ← hp])) shift_pow_self
  exact ⟨eq_trans (opow_self_comm (shift p) (p - 1)).symm h1, h1⟩

/-- 8:D20 — the exact index of the symmetric difference in `0+1`, on every frame: `(T − T⁻¹)^{p−1} ≈ Σ_{k<p} T^k`,
the sum of the translates, which is not zero, while `(T − T⁻¹)^p ≈ 0` (`symdiff_nilpotent`). With the central unit `h`
(`h = 2⁻¹`): `(∇^s)^{p−1} ≈ h^{p−1} Σ_k T^k ≉ 0` and `(∇^s)^p ≈ 0`, so the nilpotency index of `∇^s` is exactly `p`. The
Dirac operator of `0+1` is `∇^s ⊗ γ⁰` with `γ⁰` a unit, `𝒟^k = (∇^s)^k ⊗ (γ⁰)^k`, so its index is `p` as well. -/
theorem symdiff_index {κ : Nat} {g : Shell p} (F : Frame p κ g) {h h' : MatE p ν p} (hh : Central h)
    (hinv : Inverse h h') :
    opow (shift p + -(opow (shift p) (p - 1)) : MatE p ν p) (p - 1) ≈ geom (shift p) p ∧
    ¬ (opow (h * (shift p + -(opow (shift p) (p - 1))) : MatE p ν p) (p - 1) ≈ 0) ∧
    opow (h * (shift p + -(opow (shift p) (p - 1))) : MatE p ν p) p ≈ 0 := by
  have hid : opow (shift p + -(opow (shift p) (p - 1)) : MatE p ν p) (p - 1) ≈ geom (shift p) p :=
    symdiff_pred_eq_geom F char_p shift_pow_self shift_inverse
  refine ⟨hid, fun hz => ?_, symdiff_nilpotent F hh⟩
  have hpow : opow (h * (shift p + -(opow (shift p) (p - 1)))) (p - 1) ≈ opow h (p - 1) * geom (shift p) p :=
    eq_trans (mul_opow (hh _) _) (mul_congr_right _ hid)
  have hinvp := inverse_opow hinv (p - 1)
  apply geom_shift_ne_zero F
  calc geom (shift p : MatE p ν p) p ≈ 1 * geom (shift p) p := eq_symm (OpRing.one_mul _)
    _ ≈ opow h' (p - 1) * opow h (p - 1) * geom (shift p) p := mul_congr_left _ (eq_symm hinvp.2)
    _ ≈ opow h' (p - 1) * (opow h (p - 1) * geom (shift p) p) := OpRing.mul_assoc _ _ _
    _ ≈ opow h' (p - 1) * opow (h * (shift p + -(opow (shift p) (p - 1)))) (p - 1) := mul_congr_right _ (eq_symm hpow)
    _ ≈ opow h' (p - 1) * 0 := mul_congr_right _ hz
    _ ≈ 0 := Operator.mul_zero _

/-- 8:D20 — the exact index of the forward difference in `0+1`, on every frame: `(T − 1)^{p−1} ≈ Σ_{k<p} T^k`, the sum of
the translates, which is not zero, while `(T − 1)^p ≈ 0` (`translation_nilpotent`), so the nilpotency index of `∇ = T − 1`
is exactly `p`. The forward Dirac operator of `0+1` is `∇ ⊗ γ⁰` with `γ⁰` a unit, so its index is `p` as well. -/
theorem fwddiff_index {κ : Nat} {g : Shell p} (F : Frame p κ g) :
    opow (shift p + -1 : MatE p ν p) (p - 1) ≈ geom (shift p) p ∧
    ¬ (opow (shift p + -1 : MatE p ν p) (p - 1) ≈ 0) ∧
    opow (shift p + -1 : MatE p ν p) p ≈ 0 := by
  have hid : opow (shift p + -1 : MatE p ν p) (p - 1) ≈ geom (shift p) p := opow_sub_one_pred F char_p _
  exact ⟨hid, fun hz => geom_shift_ne_zero F (eq_trans (eq_symm hid) hz), translation_nilpotent F char_p shift_pow_self⟩

/-! ### The twist is unique up to sign (D21) -/
/-! ### The extension's arithmetic on explicit pairs -/

theorem mk_mul_mk (a b c d : Shell p) : (⟨a, b⟩ : Ext p ν) * ⟨c, d⟩ = ⟨a * c + ν * (b * d), a * d + b * c⟩ := rfl
theorem mk_add_mk (a b c d : Shell p) : (⟨a, b⟩ : Ext p ν) + ⟨c, d⟩ = ⟨a + c, b + d⟩ := rfl
theorem neg_mk (a b : Shell p) : -(⟨a, b⟩ : Ext p ν) = ⟨-a, -b⟩ := rfl
theorem conj_mk (a b : Shell p) : Ext.conj (⟨a, b⟩ : Ext p ν) = ⟨a, -b⟩ := rfl
theorem zero_mk : (0 : Ext p ν) = ⟨0, 0⟩ := rfl
theorem one_mk : (1 : Ext p ν) = ⟨1, 0⟩ := rfl
theorem mk_one_mul (x : Ext p ν) : (⟨1, 0⟩ : Ext p ν) * x = x := Ext.one_mul x
theorem mul_mk_one (x : Ext p ν) : x * (⟨1, 0⟩ : Ext p ν) = x := Ext.mul_one x
theorem mk_zero_mul (x : Ext p ν) : (⟨0, 0⟩ : Ext p ν) * x = 0 := Hermitian.zero_mul x
theorem mul_mk_zero (x : Ext p ν) : x * (⟨0, 0⟩ : Ext p ν) = 0 := Hermitian.mul_zero x
theorem mk_zero_add (x : Ext p ν) : (⟨0, 0⟩ : Ext p ν) + x = x := Hermitian.zero_add x
theorem add_mk_zero (x : Ext p ν) : x + (⟨0, 0⟩ : Ext p ν) = x := Hermitian.add_zero x
theorem neg_one_mul' (x : Ext p ν) : (⟨-1, 0⟩ : Ext p ν) * x = -x := by
  rw [show (⟨-1, 0⟩ : Ext p ν) = -1 from Ext.ext rfl Shell.neg_zero.symm, ← Hermitian.neg_mul, Ext.one_mul]
theorem mul_neg_one' (x : Ext p ν) : x * (⟨-1, 0⟩ : Ext p ν) = -x := by rw [Ext.mul_comm]; exact neg_one_mul' x

theorem esum4 (f : Nat → Ext p ν) : esum f 4 = f 0 + f 1 + f 2 + f 3 := by
  show 0 + f 0 + f 1 + f 2 + f 3 = f 0 + f 1 + f 2 + f 3
  rw [Hermitian.zero_add]

theorem neg_inj' {x y : Ext p ν} (h : -x = -y) : x = y := by rw [← Hermitian.neg_neg x, h, Hermitian.neg_neg]

/-- Cancellation of a nonzero scalar of the shell. -/
theorem cancel_scalar {κ : Nat} {g : Shell p} (F : Frame p κ g) {c : Shell p} (hc : c ≠ 0) {x y : Ext p ν}
    (h : Ext.ofShell c * x = Ext.ofShell c * y) : x = y := by
  rw [Ext.ofShell_mul_eq, Ext.ofShell_mul_eq] at h
  exact Ext.ext (F.mul_left_cancel hc (Ext.re_congr h)) (F.mul_left_cancel hc (Ext.im_congr h))

/-- `i² = −1` read in the extension: `⟨i, 0⟩ * ⟨i, 0⟩ = −1`. -/
theorem ii_sq {i : Shell p} (hi : i * i = -1) : (⟨i, 0⟩ : Ext p ν) * ⟨i, 0⟩ = ⟨-1, 0⟩ := by
  rw [mk_mul_mk, hi, Shell.mul_zero, Shell.mul_zero, Shell.add_zero, Shell.mul_zero, Shell.zero_mul, Shell.add_zero]

/-- `(i w)² = −ν` read in the extension. -/
theorem iw_sq {i : Shell p} (hi : i * i = -1) : (⟨0, i⟩ : Ext p ν) * ⟨0, i⟩ = ⟨-ν, 0⟩ := by
  rw [mk_mul_mk, hi, Shell.zero_mul, Shell.zero_add, Shell.zero_mul, Shell.mul_zero, Shell.add_zero, ← Shell.mul_neg,
    Shell.mul_one]

/-- Cancellation of `i`: `⟨i, 0⟩ x = ⟨i, 0⟩ y → x = y`. -/
theorem cancel_ii {i : Shell p} (hi : i * i = -1) {x y : Ext p ν} (h : (⟨i, 0⟩ : Ext p ν) * x = ⟨i, 0⟩ * y) : x = y := by
  have h2 := congrArg (fun z => (⟨i, 0⟩ : Ext p ν) * z) h
  simp only [← Ext.mul_assoc, ii_sq hi, neg_one_mul'] at h2
  exact neg_inj' h2

/-- Cancellation of `i w`: `⟨0, i⟩ x = ⟨0, i⟩ y → x = y` when `ν ≠ 0`. -/
theorem cancel_iw {κ : Nat} {g : Shell p} (F : Frame p κ g) {i : Shell p} (hi : i * i = -1) (hν : ν ≠ 0) {x y : Ext p ν}
    (h : (⟨0, i⟩ : Ext p ν) * x = ⟨0, i⟩ * y) : x = y := by
  have h2 := congrArg (fun z => (⟨0, i⟩ : Ext p ν) * z) h
  simp only [← Ext.mul_assoc, iw_sq hi] at h2
  exact cancel_scalar F (fun e => hν (by rw [← Shell.neg_neg ν, e, Shell.neg_zero])) h2

/-- `x = −x → x = 0` in the extension on a frame. -/
theorem eq_zero_of_eq_neg' {κ : Nat} {g : Shell p} (F : Frame p κ g) {x : Ext p ν} (h : x = -x) : x = 0 :=
  Ext.ext (F.eq_zero_of_eq_neg (Ext.re_congr h)) (F.eq_zero_of_eq_neg (Ext.im_congr h))

/-! ### The gamma matrices as functions, the spinor form `X = γ⁰γ¹γ³` and the integer matrix `E` -/

/-- The gamma matrices of `gamma` read as functions of two indices: `γ⁰ = i w β`, `γ^k = i ρ^k` (`γ²`'s entries
`∓i² = ±1`). -/
def gE (i : Shell p) : Nat → MatE p ν 4
  | 0 => ⟨fun a b => if a = 0 ∧ b = 2 then ⟨0, i⟩ else if a = 1 ∧ b = 3 then ⟨0, i⟩ else
      if a = 2 ∧ b = 0 then ⟨0, i⟩ else if a = 3 ∧ b = 1 then ⟨0, i⟩ else 0⟩
  | 1 => ⟨fun a b => if a = 0 ∧ b = 3 then ⟨i, 0⟩ else if a = 1 ∧ b = 2 then ⟨i, 0⟩ else
      if a = 2 ∧ b = 1 then -⟨i, 0⟩ else if a = 3 ∧ b = 0 then -⟨i, 0⟩ else 0⟩
  | 2 => ⟨fun a b => if a = 0 ∧ b = 3 then -(⟨i, 0⟩ * ⟨i, 0⟩) else if a = 1 ∧ b = 2 then ⟨i, 0⟩ * ⟨i, 0⟩ else
      if a = 2 ∧ b = 1 then ⟨i, 0⟩ * ⟨i, 0⟩ else if a = 3 ∧ b = 0 then -(⟨i, 0⟩ * ⟨i, 0⟩) else 0⟩
  | _ => ⟨fun a b => if a = 0 ∧ b = 2 then ⟨i, 0⟩ else if a = 1 ∧ b = 3 then -⟨i, 0⟩ else
      if a = 2 ∧ b = 0 then -⟨i, 0⟩ else if a = 3 ∧ b = 1 then ⟨i, 0⟩ else 0⟩

/-- The integer matrix `E` with `E₀₃ = 1`, `E₁₂ = −1`, `E₂₁ = 1`, `E₃₀ = −1`: the spinor form is `X = −i w E`. -/
def E4 : MatE p ν 4 :=
  ⟨fun a b => if a = 0 ∧ b = 3 then 1 else if a = 1 ∧ b = 2 then -1 else if a = 2 ∧ b = 1 then 1 else
    if a = 3 ∧ b = 0 then -1 else 0⟩

/-- A scalar multiple of a matrix. -/
def smulE (c : Ext p ν) (A : MatE p ν n) : MatE p ν n := ⟨fun a b => c * A.f a b⟩

theorem smulE_f (c : Ext p ν) (A : MatE p ν n) (a b : Nat) : (smulE c A).f a b = c * A.f a b := rfl

/-- The twist equations `(γ^μ)† X = −X γ^μ` for the four gamma matrices. -/
def Twists (i : Shell p) (X : MatE p ν 4) : Prop := ∀ μ, μ < 4 → dagger (gE i μ) * X ≈ -(X * gE i μ)

/-- 8:D21 — the transcription `gE` is the paper's `gamma` of Dirac.lean, entry by entry on the `4 × 4` range, for every `i`:
the twist theorems below are about the paper's gamma matrices. -/
theorem gE_eq_gamma (i : Shell p) : ∀ (μ a b : Nat), a < 4 → b < 4 →
    (gE i μ : MatE p ν 4).f a b = Mat.nth 0 (Mat.nth [] (gamma i μ) a) b
  | 0, 0, 0 => fun _ _ => rfl
  | 0, 0, 1 => fun _ _ => rfl
  | 0, 0, 2 => fun _ _ => rfl
  | 0, 0, 3 => fun _ _ => rfl
  | 0, 1, 0 => fun _ _ => rfl
  | 0, 1, 1 => fun _ _ => rfl
  | 0, 1, 2 => fun _ _ => rfl
  | 0, 1, 3 => fun _ _ => rfl
  | 0, 2, 0 => fun _ _ => rfl
  | 0, 2, 1 => fun _ _ => rfl
  | 0, 2, 2 => fun _ _ => rfl
  | 0, 2, 3 => fun _ _ => rfl
  | 0, 3, 0 => fun _ _ => rfl
  | 0, 3, 1 => fun _ _ => rfl
  | 0, 3, 2 => fun _ _ => rfl
  | 0, 3, 3 => fun _ _ => rfl
  | 0, a + 4, _ => fun ha _ => absurd ha (Nat.not_lt.mpr (Nat.le_add_left 4 a))
  | 0, 0, b + 4 => fun _ hb => absurd hb (Nat.not_lt.mpr (Nat.le_add_left 4 b))
  | 0, 1, b + 4 => fun _ hb => absurd hb (Nat.not_lt.mpr (Nat.le_add_left 4 b))
  | 0, 2, b + 4 => fun _ hb => absurd hb (Nat.not_lt.mpr (Nat.le_add_left 4 b))
  | 0, 3, b + 4 => fun _ hb => absurd hb (Nat.not_lt.mpr (Nat.le_add_left 4 b))
  | 1, 0, 0 => fun _ _ => rfl
  | 1, 0, 1 => fun _ _ => rfl
  | 1, 0, 2 => fun _ _ => rfl
  | 1, 0, 3 => fun _ _ => rfl
  | 1, 1, 0 => fun _ _ => rfl
  | 1, 1, 1 => fun _ _ => rfl
  | 1, 1, 2 => fun _ _ => rfl
  | 1, 1, 3 => fun _ _ => rfl
  | 1, 2, 0 => fun _ _ => rfl
  | 1, 2, 1 => fun _ _ => rfl
  | 1, 2, 2 => fun _ _ => rfl
  | 1, 2, 3 => fun _ _ => rfl
  | 1, 3, 0 => fun _ _ => rfl
  | 1, 3, 1 => fun _ _ => rfl
  | 1, 3, 2 => fun _ _ => rfl
  | 1, 3, 3 => fun _ _ => rfl
  | 1, a + 4, _ => fun ha _ => absurd ha (Nat.not_lt.mpr (Nat.le_add_left 4 a))
  | 1, 0, b + 4 => fun _ hb => absurd hb (Nat.not_lt.mpr (Nat.le_add_left 4 b))
  | 1, 1, b + 4 => fun _ hb => absurd hb (Nat.not_lt.mpr (Nat.le_add_left 4 b))
  | 1, 2, b + 4 => fun _ hb => absurd hb (Nat.not_lt.mpr (Nat.le_add_left 4 b))
  | 1, 3, b + 4 => fun _ hb => absurd hb (Nat.not_lt.mpr (Nat.le_add_left 4 b))
  | 2, 0, 0 => fun _ _ => rfl
  | 2, 0, 1 => fun _ _ => rfl
  | 2, 0, 2 => fun _ _ => rfl
  | 2, 0, 3 => fun _ _ => rfl
  | 2, 1, 0 => fun _ _ => rfl
  | 2, 1, 1 => fun _ _ => rfl
  | 2, 1, 2 => fun _ _ => rfl
  | 2, 1, 3 => fun _ _ => rfl
  | 2, 2, 0 => fun _ _ => rfl
  | 2, 2, 1 => fun _ _ => rfl
  | 2, 2, 2 => fun _ _ => rfl
  | 2, 2, 3 => fun _ _ => rfl
  | 2, 3, 0 => fun _ _ => rfl
  | 2, 3, 1 => fun _ _ => rfl
  | 2, 3, 2 => fun _ _ => rfl
  | 2, 3, 3 => fun _ _ => rfl
  | 2, a + 4, _ => fun ha _ => absurd ha (Nat.not_lt.mpr (Nat.le_add_left 4 a))
  | 2, 0, b + 4 => fun _ hb => absurd hb (Nat.not_lt.mpr (Nat.le_add_left 4 b))
  | 2, 1, b + 4 => fun _ hb => absurd hb (Nat.not_lt.mpr (Nat.le_add_left 4 b))
  | 2, 2, b + 4 => fun _ hb => absurd hb (Nat.not_lt.mpr (Nat.le_add_left 4 b))
  | 2, 3, b + 4 => fun _ hb => absurd hb (Nat.not_lt.mpr (Nat.le_add_left 4 b))
  | _ + 3, 0, 0 => fun _ _ => rfl
  | _ + 3, 0, 1 => fun _ _ => rfl
  | _ + 3, 0, 2 => fun _ _ => rfl
  | _ + 3, 0, 3 => fun _ _ => rfl
  | _ + 3, 1, 0 => fun _ _ => rfl
  | _ + 3, 1, 1 => fun _ _ => rfl
  | _ + 3, 1, 2 => fun _ _ => rfl
  | _ + 3, 1, 3 => fun _ _ => rfl
  | _ + 3, 2, 0 => fun _ _ => rfl
  | _ + 3, 2, 1 => fun _ _ => rfl
  | _ + 3, 2, 2 => fun _ _ => rfl
  | _ + 3, 2, 3 => fun _ _ => rfl
  | _ + 3, 3, 0 => fun _ _ => rfl
  | _ + 3, 3, 1 => fun _ _ => rfl
  | _ + 3, 3, 2 => fun _ _ => rfl
  | _ + 3, 3, 3 => fun _ _ => rfl
  | _ + 3, a + 4, _ => fun ha _ => absurd ha (Nat.not_lt.mpr (Nat.le_add_left 4 a))
  | _ + 3, 0, b + 4 => fun _ hb => absurd hb (Nat.not_lt.mpr (Nat.le_add_left 4 b))
  | _ + 3, 1, b + 4 => fun _ hb => absurd hb (Nat.not_lt.mpr (Nat.le_add_left 4 b))
  | _ + 3, 2, b + 4 => fun _ hb => absurd hb (Nat.not_lt.mpr (Nat.le_add_left 4 b))
  | _ + 3, 3, b + 4 => fun _ hb => absurd hb (Nat.not_lt.mpr (Nat.le_add_left 4 b))

/-- The `γ⁰` step: `⟨0, −i⟩ x = −(y ⟨0, i⟩)` gives `x = y`. -/
theorem g0_step {κ : Nat} {g : Shell p} (F : Frame p κ g) {i : Shell p} (hi : i * i = -1) (hν : ν ≠ 0) {x y : Ext p ν}
    (h : (⟨0, -i⟩ : Ext p ν) * x = -(y * ⟨0, i⟩)) : x = y := by
  have e1 : (⟨0, -i⟩ : Ext p ν) = -⟨0, i⟩ := Ext.ext Shell.neg_zero.symm rfl
  rw [e1, ← Hermitian.neg_mul, Ext.mul_comm y] at h
  exact cancel_iw F hi hν (neg_inj' h)

/-- The `γ³` step with the sign `−i`: `⟨−i, 0⟩ x = −(x ⟨−i, 0⟩)` gives `x = 0`. -/
theorem g3_neg_step {κ : Nat} {g : Shell p} (F : Frame p κ g) {i : Shell p} (hi : i * i = -1) {x : Ext p ν}
    (h : (⟨-i, 0⟩ : Ext p ν) * x = -(x * ⟨-i, 0⟩)) : x = 0 := by
  have e1 : (⟨-i, 0⟩ : Ext p ν) = -⟨i, 0⟩ := Ext.ext rfl Shell.neg_zero.symm
  rw [e1, Ext.mul_comm x] at h
  have h2 : (⟨i, 0⟩ : Ext p ν) * x = -(⟨i, 0⟩ * x) := by
    have := congrArg (- ·) h
    simp only [Hermitian.neg_neg] at this
    rw [Hermitian.neg_mul, ← this, ← Hermitian.neg_mul, Hermitian.neg_neg]
  have h3 : (⟨i, 0⟩ : Ext p ν) * x = ⟨i, 0⟩ * 0 := by rw [Hermitian.mul_zero]; exact eq_zero_of_eq_neg' F h2
  exact cancel_ii hi h3

/-- The `γ³` step with the sign `i`: `⟨i, 0⟩ x = −(x ⟨i, 0⟩)` gives `x = 0`. -/
theorem g3_pos_step {κ : Nat} {g : Shell p} (F : Frame p κ g) {i : Shell p} (hi : i * i = -1) {x : Ext p ν}
    (h : (⟨i, 0⟩ : Ext p ν) * x = -(x * ⟨i, 0⟩)) : x = 0 := by
  rw [Ext.mul_comm x] at h
  have h3 : (⟨i, 0⟩ : Ext p ν) * x = ⟨i, 0⟩ * 0 := by rw [Hermitian.mul_zero]; exact eq_zero_of_eq_neg' F h
  exact cancel_ii hi h3

/-- The `γ¹` step tying the anti-diagonal: `⟨−i, 0⟩ x = −(y ⟨−i, 0⟩)` gives `x = −y`. -/
theorem g1_neg_step {i : Shell p} (hi : i * i = -1) {x y : Ext p ν}
    (h : (⟨-i, 0⟩ : Ext p ν) * x = -(y * ⟨-i, 0⟩)) : x = -y := by
  have e1 : (⟨-i, 0⟩ : Ext p ν) = -⟨i, 0⟩ := Ext.ext rfl Shell.neg_zero.symm
  rw [e1, Ext.mul_comm y, ← Hermitian.neg_mul, ← Hermitian.neg_mul, Hermitian.neg_neg] at h
  have h' : (⟨i, 0⟩ : Ext p ν) * x = ⟨i, 0⟩ * -y := by rw [← Hermitian.mul_neg, ← h, Hermitian.neg_neg]
  exact cancel_ii hi h'

/-- The `γ¹` step tying the diagonal: `⟨−i, 0⟩ x = −(y ⟨i, 0⟩)` gives `x = y`. -/
theorem g1_pos_step {i : Shell p} (hi : i * i = -1) {x y : Ext p ν}
    (h : (⟨-i, 0⟩ : Ext p ν) * x = -(y * ⟨i, 0⟩)) : x = y := by
  have e1 : (⟨-i, 0⟩ : Ext p ν) = -⟨i, 0⟩ := Ext.ext rfl Shell.neg_zero.symm
  rw [e1, Ext.mul_comm y, ← Hermitian.neg_mul] at h
  exact cancel_ii hi (neg_inj' h)

/-- 8:D21 — the twist is unique up to a scalar, on every frame with `i² = −1` and `ν ≠ 0`: a solution `X'` of the four
twist equations `(γ^μ)† X' = −X' γ^μ` is `X'₀₃ · E`, so the solutions form the line of `E` (and of `X = −i w E`). The
proof reads fifteen of the sixty-four entry equations: `γ⁰` makes `X'` block-symmetric, `γ³` kills four entries, `γ¹`
ties the diagonal and the anti-diagonal, `γ²` kills the diagonal. -/
theorem twist_unique {κ : Nat} {g : Shell p} (F : Frame p κ g) {i : Shell p} (hi : i * i = -1) (hν : ν ≠ 0)
    (X : MatE p ν 4) (h : Twists i X) : X ≈ smulE (X.f 0 3) E4 := by
  have h0 := h 0 (by decide); have h1 := h 1 (by decide); have h2 := h 2 (by decide); have h3 := h 3 (by decide)
  have e20 := h0 0 (by decide) 0 (by decide)
  change 0 + Ext.conj 0 * X.f 0 0 + Ext.conj 0 * X.f 1 0 + Ext.conj ⟨0, i⟩ * X.f 2 0 + Ext.conj 0 * X.f 3 0 =
      -(0 + X.f 0 0 * 0 + X.f 0 1 * 0 + X.f 0 2 * ⟨0, i⟩ + X.f 0 3 * 0) at e20
  have e21 := h0 0 (by decide) 1 (by decide)
  change 0 + Ext.conj 0 * X.f 0 1 + Ext.conj 0 * X.f 1 1 + Ext.conj ⟨0, i⟩ * X.f 2 1 + Ext.conj 0 * X.f 3 1 =
      -(0 + X.f 0 0 * 0 + X.f 0 1 * 0 + X.f 0 2 * 0 + X.f 0 3 * ⟨0, i⟩) at e21
  have e22 := h0 0 (by decide) 2 (by decide)
  change 0 + Ext.conj 0 * X.f 0 2 + Ext.conj 0 * X.f 1 2 + Ext.conj ⟨0, i⟩ * X.f 2 2 + Ext.conj 0 * X.f 3 2 =
      -(0 + X.f 0 0 * ⟨0, i⟩ + X.f 0 1 * 0 + X.f 0 2 * 0 + X.f 0 3 * 0) at e22
  have e23 := h0 0 (by decide) 3 (by decide)
  change 0 + Ext.conj 0 * X.f 0 3 + Ext.conj 0 * X.f 1 3 + Ext.conj ⟨0, i⟩ * X.f 2 3 + Ext.conj 0 * X.f 3 3 =
      -(0 + X.f 0 0 * 0 + X.f 0 1 * ⟨0, i⟩ + X.f 0 2 * 0 + X.f 0 3 * 0) at e23
  have e30 := h0 1 (by decide) 0 (by decide)
  change 0 + Ext.conj 0 * X.f 0 0 + Ext.conj 0 * X.f 1 0 + Ext.conj 0 * X.f 2 0 + Ext.conj ⟨0, i⟩ * X.f 3 0 =
      -(0 + X.f 1 0 * 0 + X.f 1 1 * 0 + X.f 1 2 * ⟨0, i⟩ + X.f 1 3 * 0) at e30
  have e31 := h0 1 (by decide) 1 (by decide)
  change 0 + Ext.conj 0 * X.f 0 1 + Ext.conj 0 * X.f 1 1 + Ext.conj 0 * X.f 2 1 + Ext.conj ⟨0, i⟩ * X.f 3 1 =
      -(0 + X.f 1 0 * 0 + X.f 1 1 * 0 + X.f 1 2 * 0 + X.f 1 3 * ⟨0, i⟩) at e31
  have e32 := h0 1 (by decide) 2 (by decide)
  change 0 + Ext.conj 0 * X.f 0 2 + Ext.conj 0 * X.f 1 2 + Ext.conj 0 * X.f 2 2 + Ext.conj ⟨0, i⟩ * X.f 3 2 =
      -(0 + X.f 1 0 * ⟨0, i⟩ + X.f 1 1 * 0 + X.f 1 2 * 0 + X.f 1 3 * 0) at e32
  have e33 := h0 1 (by decide) 3 (by decide)
  change 0 + Ext.conj 0 * X.f 0 3 + Ext.conj 0 * X.f 1 3 + Ext.conj 0 * X.f 2 3 + Ext.conj ⟨0, i⟩ * X.f 3 3 =
      -(0 + X.f 1 0 * 0 + X.f 1 1 * ⟨0, i⟩ + X.f 1 2 * 0 + X.f 1 3 * 0) at e33
  have f00 := h3 0 (by decide) 0 (by decide)
  change 0 + Ext.conj 0 * X.f 0 0 + Ext.conj 0 * X.f 1 0 + Ext.conj (-⟨i, 0⟩) * X.f 2 0 + Ext.conj 0 * X.f 3 0 =
      -(0 + X.f 0 0 * 0 + X.f 0 1 * 0 + X.f 0 2 * (-⟨i, 0⟩) + X.f 0 3 * 0) at f00
  have f11 := h3 1 (by decide) 1 (by decide)
  change 0 + Ext.conj 0 * X.f 0 1 + Ext.conj 0 * X.f 1 1 + Ext.conj 0 * X.f 2 1 + Ext.conj ⟨i, 0⟩ * X.f 3 1 =
      -(0 + X.f 1 0 * 0 + X.f 1 1 * 0 + X.f 1 2 * 0 + X.f 1 3 * ⟨i, 0⟩) at f11
  have f03 := h3 0 (by decide) 3 (by decide)
  change 0 + Ext.conj 0 * X.f 0 3 + Ext.conj 0 * X.f 1 3 + Ext.conj (-⟨i, 0⟩) * X.f 2 3 + Ext.conj 0 * X.f 3 3 =
      -(0 + X.f 0 0 * 0 + X.f 0 1 * (-⟨i, 0⟩) + X.f 0 2 * 0 + X.f 0 3 * 0) at f03
  have f12 := h3 1 (by decide) 2 (by decide)
  change 0 + Ext.conj 0 * X.f 0 2 + Ext.conj 0 * X.f 1 2 + Ext.conj 0 * X.f 2 2 + Ext.conj ⟨i, 0⟩ * X.f 3 2 =
      -(0 + X.f 1 0 * ⟨i, 0⟩ + X.f 1 1 * 0 + X.f 1 2 * 0 + X.f 1 3 * 0) at f12
  have k00 := h1 0 (by decide) 0 (by decide)
  change 0 + Ext.conj 0 * X.f 0 0 + Ext.conj 0 * X.f 1 0 + Ext.conj 0 * X.f 2 0 + Ext.conj (-⟨i, 0⟩) * X.f 3 0 =
      -(0 + X.f 0 0 * 0 + X.f 0 1 * 0 + X.f 0 2 * 0 + X.f 0 3 * (-⟨i, 0⟩)) at k00
  have k03 := h1 0 (by decide) 3 (by decide)
  change 0 + Ext.conj 0 * X.f 0 3 + Ext.conj 0 * X.f 1 3 + Ext.conj 0 * X.f 2 3 + Ext.conj (-⟨i, 0⟩) * X.f 3 3 =
      -(0 + X.f 0 0 * ⟨i, 0⟩ + X.f 0 1 * 0 + X.f 0 2 * 0 + X.f 0 3 * 0) at k03
  have m03 := h2 0 (by decide) 3 (by decide)
  change 0 + Ext.conj 0 * X.f 0 3 + Ext.conj 0 * X.f 1 3 + Ext.conj 0 * X.f 2 3 + Ext.conj (-(⟨i, 0⟩ * ⟨i, 0⟩)) * X.f 3 3 =
      -(0 + X.f 0 0 * (-(⟨i, 0⟩ * ⟨i, 0⟩)) + X.f 0 1 * 0 + X.f 0 2 * 0 + X.f 0 3 * 0) at m03
  simp only [Hermitian.conj_zero, conj_mk, Shell.neg_zero, Hermitian.zero_mul, Hermitian.mul_zero, Hermitian.zero_add, Hermitian.add_zero, ii_sq hi, neg_mk, Shell.neg_neg, mk_one_mul, mul_mk_one] at e20 e21 e22 e23 e30 e31 e32 e33 f00 f11 f03 f12 k00 k03 m03
  -- the block symmetry
  have x20 : X.f 2 0 = X.f 0 2 := g0_step F hi hν e20
  have x21 : X.f 2 1 = X.f 0 3 := g0_step F hi hν e21
  have x22 : X.f 2 2 = X.f 0 0 := g0_step F hi hν e22
  have x23 : X.f 2 3 = X.f 0 1 := g0_step F hi hν e23
  have x30 : X.f 3 0 = X.f 1 2 := g0_step F hi hν e30
  have x31 : X.f 3 1 = X.f 1 3 := g0_step F hi hν e31
  have x32 : X.f 3 2 = X.f 1 0 := g0_step F hi hν e32
  have x33 : X.f 3 3 = X.f 1 1 := g0_step F hi hν e33
  -- the four vanishing entries of `γ³`
  rw [x20] at f00; rw [x31] at f11; rw [x23] at f03; rw [x32] at f12
  have x02 : X.f 0 2 = 0 := g3_neg_step F hi f00
  have x13 : X.f 1 3 = 0 := g3_pos_step F hi f11
  have x01 : X.f 0 1 = 0 := g3_neg_step F hi f03
  have x10 : X.f 1 0 = 0 := g3_pos_step F hi f12
  -- `γ¹`: the anti-diagonal and the diagonal
  rw [x30] at k00; rw [x33] at k03
  have x12 : X.f 1 2 = -X.f 0 3 := g1_neg_step hi k00
  have x11 : X.f 1 1 = X.f 0 0 := g1_pos_step hi k03
  -- `γ²`: the diagonal vanishes
  rw [x33, x11] at m03
  have x00 : X.f 0 0 = 0 := eq_zero_of_eq_neg' F m03
  -- the sixteen entries
  intro a ha b hb
  rw [smulE_f]
  match a, ha, b, hb with
  | 0, _, 0, _ => change X.f 0 0 = X.f 0 3 * 0; rw [Hermitian.mul_zero]; exact x00
  | 0, _, 1, _ => change X.f 0 1 = X.f 0 3 * 0; rw [Hermitian.mul_zero]; exact x01
  | 0, _, 2, _ => change X.f 0 2 = X.f 0 3 * 0; rw [Hermitian.mul_zero]; exact x02
  | 0, _, 3, _ => change X.f 0 3 = X.f 0 3 * 1; rw [Ext.mul_one]
  | 1, _, 0, _ => change X.f 1 0 = X.f 0 3 * 0; rw [Hermitian.mul_zero]; exact x10
  | 1, _, 1, _ => change X.f 1 1 = X.f 0 3 * 0; rw [Hermitian.mul_zero]; rw [x11]; exact x00
  | 1, _, 2, _ => change X.f 1 2 = X.f 0 3 * -1; rw [← Hermitian.mul_neg, Ext.mul_one]; exact x12
  | 1, _, 3, _ => change X.f 1 3 = X.f 0 3 * 0; rw [Hermitian.mul_zero]; exact x13
  | 2, _, 0, _ => change X.f 2 0 = X.f 0 3 * 0; rw [Hermitian.mul_zero]; rw [x20]; exact x02
  | 2, _, 1, _ => change X.f 2 1 = X.f 0 3 * 1; rw [Ext.mul_one]; exact x21
  | 2, _, 2, _ => change X.f 2 2 = X.f 0 3 * 0; rw [Hermitian.mul_zero]; rw [x22]; exact x00
  | 2, _, 3, _ => change X.f 2 3 = X.f 0 3 * 0; rw [Hermitian.mul_zero]; rw [x23]; exact x01
  | 3, _, 0, _ => change X.f 3 0 = X.f 0 3 * -1; rw [← Hermitian.mul_neg, Ext.mul_one]; rw [x30]; exact x12
  | 3, _, 1, _ => change X.f 3 1 = X.f 0 3 * 0; rw [Hermitian.mul_zero]; rw [x31]; exact x13
  | 3, _, 2, _ => change X.f 3 2 = X.f 0 3 * 0; rw [Hermitian.mul_zero]; rw [x32]; exact x10
  | 3, _, 3, _ => change X.f 3 3 = X.f 0 3 * 0; rw [Hermitian.mul_zero]; rw [x33, x11]; exact x00
  | a + 4, ha, _, _ => exact absurd ha (Nat.not_lt.mpr (Nat.le_add_left 4 a))
  | _, _, b + 4, hb => exact absurd hb (Nat.not_lt.mpr (Nat.le_add_left 4 b))

/-- 8:D21 — the spinor form `X = γ⁰ γ¹ γ³` is `−i w E`, on every shell with `i² = −1`: the sixteen entries of the triple
product, normalised as ring expressions in `i w` and `i` and read off with `i² = −1`. -/
theorem gE_prod {i : Shell p} (hi : i * i = -1) : (gE i 0 * gE i 1 * gE i 3 : MatE p ν 4) ≈ smulE (-⟨0, i⟩) E4 := by
  intro a ha b hb
  match a, ha, b, hb with
  | 0, _, 0, _ =>
    change (0 + (0 + 0 * 0 + 0 * 0 + ⟨0, i⟩ * 0 + 0 * (-⟨i, 0⟩)) * 0 + (0 + 0 * 0 + 0 * 0 + ⟨0, i⟩ * (-⟨i, 0⟩) + 0 * 0) * 0 + (0 + 0 * 0 + 0 * ⟨i, 0⟩ + ⟨0, i⟩ * 0 + 0 * 0) * (-⟨i, 0⟩) + (0 + 0 * ⟨i, 0⟩ + 0 * 0 + ⟨0, i⟩ * 0 + 0 * 0) * 0 : Ext p ν) =
      (-⟨0, i⟩ * 0 : Ext p ν)
    exact FRC.Unitary.xsound (FRC.Unitary.xlook [⟨0, i⟩, ⟨i, 0⟩]) (.add (.add (.add (.add .zero (.mul (.add (.add (.add (.add .zero (.mul .zero .zero)) (.mul .zero .zero)) (.mul (.var 0) .zero)) (.mul .zero (.neg (.var 1)))) .zero)) (.mul (.add (.add (.add (.add .zero (.mul .zero .zero)) (.mul .zero .zero)) (.mul (.var 0) (.neg (.var 1)))) (.mul .zero .zero)) .zero)) (.mul (.add (.add (.add (.add .zero (.mul .zero .zero)) (.mul .zero (.var 1))) (.mul (.var 0) .zero)) (.mul .zero .zero)) (.neg (.var 1)))) (.mul (.add (.add (.add (.add .zero (.mul .zero (.var 1))) (.mul .zero .zero)) (.mul (.var 0) .zero)) (.mul .zero .zero)) .zero)) (.mul (.neg (.var 0)) .zero) (by decide +kernel)
  | 0, _, 1, _ =>
    change (0 + (0 + 0 * 0 + 0 * 0 + ⟨0, i⟩ * 0 + 0 * (-⟨i, 0⟩)) * 0 + (0 + 0 * 0 + 0 * 0 + ⟨0, i⟩ * (-⟨i, 0⟩) + 0 * 0) * 0 + (0 + 0 * 0 + 0 * ⟨i, 0⟩ + ⟨0, i⟩ * 0 + 0 * 0) * 0 + (0 + 0 * ⟨i, 0⟩ + 0 * 0 + ⟨0, i⟩ * 0 + 0 * 0) * ⟨i, 0⟩ : Ext p ν) =
      (-⟨0, i⟩ * 0 : Ext p ν)
    exact FRC.Unitary.xsound (FRC.Unitary.xlook [⟨0, i⟩, ⟨i, 0⟩]) (.add (.add (.add (.add .zero (.mul (.add (.add (.add (.add .zero (.mul .zero .zero)) (.mul .zero .zero)) (.mul (.var 0) .zero)) (.mul .zero (.neg (.var 1)))) .zero)) (.mul (.add (.add (.add (.add .zero (.mul .zero .zero)) (.mul .zero .zero)) (.mul (.var 0) (.neg (.var 1)))) (.mul .zero .zero)) .zero)) (.mul (.add (.add (.add (.add .zero (.mul .zero .zero)) (.mul .zero (.var 1))) (.mul (.var 0) .zero)) (.mul .zero .zero)) .zero)) (.mul (.add (.add (.add (.add .zero (.mul .zero (.var 1))) (.mul .zero .zero)) (.mul (.var 0) .zero)) (.mul .zero .zero)) (.var 1))) (.mul (.neg (.var 0)) .zero) (by decide +kernel)
  | 0, _, 2, _ =>
    change (0 + (0 + 0 * 0 + 0 * 0 + ⟨0, i⟩ * 0 + 0 * (-⟨i, 0⟩)) * ⟨i, 0⟩ + (0 + 0 * 0 + 0 * 0 + ⟨0, i⟩ * (-⟨i, 0⟩) + 0 * 0) * 0 + (0 + 0 * 0 + 0 * ⟨i, 0⟩ + ⟨0, i⟩ * 0 + 0 * 0) * 0 + (0 + 0 * ⟨i, 0⟩ + 0 * 0 + ⟨0, i⟩ * 0 + 0 * 0) * 0 : Ext p ν) =
      (-⟨0, i⟩ * 0 : Ext p ν)
    exact FRC.Unitary.xsound (FRC.Unitary.xlook [⟨0, i⟩, ⟨i, 0⟩]) (.add (.add (.add (.add .zero (.mul (.add (.add (.add (.add .zero (.mul .zero .zero)) (.mul .zero .zero)) (.mul (.var 0) .zero)) (.mul .zero (.neg (.var 1)))) (.var 1))) (.mul (.add (.add (.add (.add .zero (.mul .zero .zero)) (.mul .zero .zero)) (.mul (.var 0) (.neg (.var 1)))) (.mul .zero .zero)) .zero)) (.mul (.add (.add (.add (.add .zero (.mul .zero .zero)) (.mul .zero (.var 1))) (.mul (.var 0) .zero)) (.mul .zero .zero)) .zero)) (.mul (.add (.add (.add (.add .zero (.mul .zero (.var 1))) (.mul .zero .zero)) (.mul (.var 0) .zero)) (.mul .zero .zero)) .zero)) (.mul (.neg (.var 0)) .zero) (by decide +kernel)
  | 0, _, 3, _ =>
    change (0 + (0 + 0 * 0 + 0 * 0 + ⟨0, i⟩ * 0 + 0 * (-⟨i, 0⟩)) * 0 + (0 + 0 * 0 + 0 * 0 + ⟨0, i⟩ * (-⟨i, 0⟩) + 0 * 0) * (-⟨i, 0⟩) + (0 + 0 * 0 + 0 * ⟨i, 0⟩ + ⟨0, i⟩ * 0 + 0 * 0) * 0 + (0 + 0 * ⟨i, 0⟩ + 0 * 0 + ⟨0, i⟩ * 0 + 0 * 0) * 0 : Ext p ν) =
      (-⟨0, i⟩ * 1 : Ext p ν)
    calc _ = (⟨0, i⟩ : Ext p ν) * (⟨i, 0⟩ * ⟨i, 0⟩) :=
          FRC.Unitary.xsound (FRC.Unitary.xlook [⟨0, i⟩, ⟨i, 0⟩]) (.add (.add (.add (.add .zero (.mul (.add (.add (.add (.add .zero (.mul .zero .zero)) (.mul .zero .zero)) (.mul (.var 0) .zero)) (.mul .zero (.neg (.var 1)))) .zero)) (.mul (.add (.add (.add (.add .zero (.mul .zero .zero)) (.mul .zero .zero)) (.mul (.var 0) (.neg (.var 1)))) (.mul .zero .zero)) (.neg (.var 1)))) (.mul (.add (.add (.add (.add .zero (.mul .zero .zero)) (.mul .zero (.var 1))) (.mul (.var 0) .zero)) (.mul .zero .zero)) .zero)) (.mul (.add (.add (.add (.add .zero (.mul .zero (.var 1))) (.mul .zero .zero)) (.mul (.var 0) .zero)) (.mul .zero .zero)) .zero)) (.mul (.var 0) (.mul (.var 1) (.var 1))) (by decide +kernel)
      _ = -⟨0, i⟩ * 1 := by rw [ii_sq hi, mul_neg_one', Ext.mul_one]
  | 1, _, 0, _ =>
    change (0 + (0 + 0 * 0 + 0 * 0 + 0 * 0 + ⟨0, i⟩ * (-⟨i, 0⟩)) * 0 + (0 + 0 * 0 + 0 * 0 + 0 * (-⟨i, 0⟩) + ⟨0, i⟩ * 0) * 0 + (0 + 0 * 0 + 0 * ⟨i, 0⟩ + 0 * 0 + ⟨0, i⟩ * 0) * (-⟨i, 0⟩) + (0 + 0 * ⟨i, 0⟩ + 0 * 0 + 0 * 0 + ⟨0, i⟩ * 0) * 0 : Ext p ν) =
      (-⟨0, i⟩ * 0 : Ext p ν)
    exact FRC.Unitary.xsound (FRC.Unitary.xlook [⟨0, i⟩, ⟨i, 0⟩]) (.add (.add (.add (.add .zero (.mul (.add (.add (.add (.add .zero (.mul .zero .zero)) (.mul .zero .zero)) (.mul .zero .zero)) (.mul (.var 0) (.neg (.var 1)))) .zero)) (.mul (.add (.add (.add (.add .zero (.mul .zero .zero)) (.mul .zero .zero)) (.mul .zero (.neg (.var 1)))) (.mul (.var 0) .zero)) .zero)) (.mul (.add (.add (.add (.add .zero (.mul .zero .zero)) (.mul .zero (.var 1))) (.mul .zero .zero)) (.mul (.var 0) .zero)) (.neg (.var 1)))) (.mul (.add (.add (.add (.add .zero (.mul .zero (.var 1))) (.mul .zero .zero)) (.mul .zero .zero)) (.mul (.var 0) .zero)) .zero)) (.mul (.neg (.var 0)) .zero) (by decide +kernel)
  | 1, _, 1, _ =>
    change (0 + (0 + 0 * 0 + 0 * 0 + 0 * 0 + ⟨0, i⟩ * (-⟨i, 0⟩)) * 0 + (0 + 0 * 0 + 0 * 0 + 0 * (-⟨i, 0⟩) + ⟨0, i⟩ * 0) * 0 + (0 + 0 * 0 + 0 * ⟨i, 0⟩ + 0 * 0 + ⟨0, i⟩ * 0) * 0 + (0 + 0 * ⟨i, 0⟩ + 0 * 0 + 0 * 0 + ⟨0, i⟩ * 0) * ⟨i, 0⟩ : Ext p ν) =
      (-⟨0, i⟩ * 0 : Ext p ν)
    exact FRC.Unitary.xsound (FRC.Unitary.xlook [⟨0, i⟩, ⟨i, 0⟩]) (.add (.add (.add (.add .zero (.mul (.add (.add (.add (.add .zero (.mul .zero .zero)) (.mul .zero .zero)) (.mul .zero .zero)) (.mul (.var 0) (.neg (.var 1)))) .zero)) (.mul (.add (.add (.add (.add .zero (.mul .zero .zero)) (.mul .zero .zero)) (.mul .zero (.neg (.var 1)))) (.mul (.var 0) .zero)) .zero)) (.mul (.add (.add (.add (.add .zero (.mul .zero .zero)) (.mul .zero (.var 1))) (.mul .zero .zero)) (.mul (.var 0) .zero)) .zero)) (.mul (.add (.add (.add (.add .zero (.mul .zero (.var 1))) (.mul .zero .zero)) (.mul .zero .zero)) (.mul (.var 0) .zero)) (.var 1))) (.mul (.neg (.var 0)) .zero) (by decide +kernel)
  | 1, _, 2, _ =>
    change (0 + (0 + 0 * 0 + 0 * 0 + 0 * 0 + ⟨0, i⟩ * (-⟨i, 0⟩)) * ⟨i, 0⟩ + (0 + 0 * 0 + 0 * 0 + 0 * (-⟨i, 0⟩) + ⟨0, i⟩ * 0) * 0 + (0 + 0 * 0 + 0 * ⟨i, 0⟩ + 0 * 0 + ⟨0, i⟩ * 0) * 0 + (0 + 0 * ⟨i, 0⟩ + 0 * 0 + 0 * 0 + ⟨0, i⟩ * 0) * 0 : Ext p ν) =
      (-⟨0, i⟩ * -1 : Ext p ν)
    calc _ = -((⟨0, i⟩ : Ext p ν) * (⟨i, 0⟩ * ⟨i, 0⟩)) :=
          FRC.Unitary.xsound (FRC.Unitary.xlook [⟨0, i⟩, ⟨i, 0⟩]) (.add (.add (.add (.add .zero (.mul (.add (.add (.add (.add .zero (.mul .zero .zero)) (.mul .zero .zero)) (.mul .zero .zero)) (.mul (.var 0) (.neg (.var 1)))) (.var 1))) (.mul (.add (.add (.add (.add .zero (.mul .zero .zero)) (.mul .zero .zero)) (.mul .zero (.neg (.var 1)))) (.mul (.var 0) .zero)) .zero)) (.mul (.add (.add (.add (.add .zero (.mul .zero .zero)) (.mul .zero (.var 1))) (.mul .zero .zero)) (.mul (.var 0) .zero)) .zero)) (.mul (.add (.add (.add (.add .zero (.mul .zero (.var 1))) (.mul .zero .zero)) (.mul .zero .zero)) (.mul (.var 0) .zero)) .zero)) (.neg (.mul (.var 0) (.mul (.var 1) (.var 1)))) (by decide +kernel)
      _ = -⟨0, i⟩ * -1 := by rw [ii_sq hi, mul_neg_one', Hermitian.neg_neg, ← Hermitian.neg_mul, ← Hermitian.mul_neg, Hermitian.neg_neg, Ext.mul_one]
  | 1, _, 3, _ =>
    change (0 + (0 + 0 * 0 + 0 * 0 + 0 * 0 + ⟨0, i⟩ * (-⟨i, 0⟩)) * 0 + (0 + 0 * 0 + 0 * 0 + 0 * (-⟨i, 0⟩) + ⟨0, i⟩ * 0) * (-⟨i, 0⟩) + (0 + 0 * 0 + 0 * ⟨i, 0⟩ + 0 * 0 + ⟨0, i⟩ * 0) * 0 + (0 + 0 * ⟨i, 0⟩ + 0 * 0 + 0 * 0 + ⟨0, i⟩ * 0) * 0 : Ext p ν) =
      (-⟨0, i⟩ * 0 : Ext p ν)
    exact FRC.Unitary.xsound (FRC.Unitary.xlook [⟨0, i⟩, ⟨i, 0⟩]) (.add (.add (.add (.add .zero (.mul (.add (.add (.add (.add .zero (.mul .zero .zero)) (.mul .zero .zero)) (.mul .zero .zero)) (.mul (.var 0) (.neg (.var 1)))) .zero)) (.mul (.add (.add (.add (.add .zero (.mul .zero .zero)) (.mul .zero .zero)) (.mul .zero (.neg (.var 1)))) (.mul (.var 0) .zero)) (.neg (.var 1)))) (.mul (.add (.add (.add (.add .zero (.mul .zero .zero)) (.mul .zero (.var 1))) (.mul .zero .zero)) (.mul (.var 0) .zero)) .zero)) (.mul (.add (.add (.add (.add .zero (.mul .zero (.var 1))) (.mul .zero .zero)) (.mul .zero .zero)) (.mul (.var 0) .zero)) .zero)) (.mul (.neg (.var 0)) .zero) (by decide +kernel)
  | 2, _, 0, _ =>
    change (0 + (0 + ⟨0, i⟩ * 0 + 0 * 0 + 0 * 0 + 0 * (-⟨i, 0⟩)) * 0 + (0 + ⟨0, i⟩ * 0 + 0 * 0 + 0 * (-⟨i, 0⟩) + 0 * 0) * 0 + (0 + ⟨0, i⟩ * 0 + 0 * ⟨i, 0⟩ + 0 * 0 + 0 * 0) * (-⟨i, 0⟩) + (0 + ⟨0, i⟩ * ⟨i, 0⟩ + 0 * 0 + 0 * 0 + 0 * 0) * 0 : Ext p ν) =
      (-⟨0, i⟩ * 0 : Ext p ν)
    exact FRC.Unitary.xsound (FRC.Unitary.xlook [⟨0, i⟩, ⟨i, 0⟩]) (.add (.add (.add (.add .zero (.mul (.add (.add (.add (.add .zero (.mul (.var 0) .zero)) (.mul .zero .zero)) (.mul .zero .zero)) (.mul .zero (.neg (.var 1)))) .zero)) (.mul (.add (.add (.add (.add .zero (.mul (.var 0) .zero)) (.mul .zero .zero)) (.mul .zero (.neg (.var 1)))) (.mul .zero .zero)) .zero)) (.mul (.add (.add (.add (.add .zero (.mul (.var 0) .zero)) (.mul .zero (.var 1))) (.mul .zero .zero)) (.mul .zero .zero)) (.neg (.var 1)))) (.mul (.add (.add (.add (.add .zero (.mul (.var 0) (.var 1))) (.mul .zero .zero)) (.mul .zero .zero)) (.mul .zero .zero)) .zero)) (.mul (.neg (.var 0)) .zero) (by decide +kernel)
  | 2, _, 1, _ =>
    change (0 + (0 + ⟨0, i⟩ * 0 + 0 * 0 + 0 * 0 + 0 * (-⟨i, 0⟩)) * 0 + (0 + ⟨0, i⟩ * 0 + 0 * 0 + 0 * (-⟨i, 0⟩) + 0 * 0) * 0 + (0 + ⟨0, i⟩ * 0 + 0 * ⟨i, 0⟩ + 0 * 0 + 0 * 0) * 0 + (0 + ⟨0, i⟩ * ⟨i, 0⟩ + 0 * 0 + 0 * 0 + 0 * 0) * ⟨i, 0⟩ : Ext p ν) =
      (-⟨0, i⟩ * 1 : Ext p ν)
    calc _ = (⟨0, i⟩ : Ext p ν) * (⟨i, 0⟩ * ⟨i, 0⟩) :=
          FRC.Unitary.xsound (FRC.Unitary.xlook [⟨0, i⟩, ⟨i, 0⟩]) (.add (.add (.add (.add .zero (.mul (.add (.add (.add (.add .zero (.mul (.var 0) .zero)) (.mul .zero .zero)) (.mul .zero .zero)) (.mul .zero (.neg (.var 1)))) .zero)) (.mul (.add (.add (.add (.add .zero (.mul (.var 0) .zero)) (.mul .zero .zero)) (.mul .zero (.neg (.var 1)))) (.mul .zero .zero)) .zero)) (.mul (.add (.add (.add (.add .zero (.mul (.var 0) .zero)) (.mul .zero (.var 1))) (.mul .zero .zero)) (.mul .zero .zero)) .zero)) (.mul (.add (.add (.add (.add .zero (.mul (.var 0) (.var 1))) (.mul .zero .zero)) (.mul .zero .zero)) (.mul .zero .zero)) (.var 1))) (.mul (.var 0) (.mul (.var 1) (.var 1))) (by decide +kernel)
      _ = -⟨0, i⟩ * 1 := by rw [ii_sq hi, mul_neg_one', Ext.mul_one]
  | 2, _, 2, _ =>
    change (0 + (0 + ⟨0, i⟩ * 0 + 0 * 0 + 0 * 0 + 0 * (-⟨i, 0⟩)) * ⟨i, 0⟩ + (0 + ⟨0, i⟩ * 0 + 0 * 0 + 0 * (-⟨i, 0⟩) + 0 * 0) * 0 + (0 + ⟨0, i⟩ * 0 + 0 * ⟨i, 0⟩ + 0 * 0 + 0 * 0) * 0 + (0 + ⟨0, i⟩ * ⟨i, 0⟩ + 0 * 0 + 0 * 0 + 0 * 0) * 0 : Ext p ν) =
      (-⟨0, i⟩ * 0 : Ext p ν)
    exact FRC.Unitary.xsound (FRC.Unitary.xlook [⟨0, i⟩, ⟨i, 0⟩]) (.add (.add (.add (.add .zero (.mul (.add (.add (.add (.add .zero (.mul (.var 0) .zero)) (.mul .zero .zero)) (.mul .zero .zero)) (.mul .zero (.neg (.var 1)))) (.var 1))) (.mul (.add (.add (.add (.add .zero (.mul (.var 0) .zero)) (.mul .zero .zero)) (.mul .zero (.neg (.var 1)))) (.mul .zero .zero)) .zero)) (.mul (.add (.add (.add (.add .zero (.mul (.var 0) .zero)) (.mul .zero (.var 1))) (.mul .zero .zero)) (.mul .zero .zero)) .zero)) (.mul (.add (.add (.add (.add .zero (.mul (.var 0) (.var 1))) (.mul .zero .zero)) (.mul .zero .zero)) (.mul .zero .zero)) .zero)) (.mul (.neg (.var 0)) .zero) (by decide +kernel)
  | 2, _, 3, _ =>
    change (0 + (0 + ⟨0, i⟩ * 0 + 0 * 0 + 0 * 0 + 0 * (-⟨i, 0⟩)) * 0 + (0 + ⟨0, i⟩ * 0 + 0 * 0 + 0 * (-⟨i, 0⟩) + 0 * 0) * (-⟨i, 0⟩) + (0 + ⟨0, i⟩ * 0 + 0 * ⟨i, 0⟩ + 0 * 0 + 0 * 0) * 0 + (0 + ⟨0, i⟩ * ⟨i, 0⟩ + 0 * 0 + 0 * 0 + 0 * 0) * 0 : Ext p ν) =
      (-⟨0, i⟩ * 0 : Ext p ν)
    exact FRC.Unitary.xsound (FRC.Unitary.xlook [⟨0, i⟩, ⟨i, 0⟩]) (.add (.add (.add (.add .zero (.mul (.add (.add (.add (.add .zero (.mul (.var 0) .zero)) (.mul .zero .zero)) (.mul .zero .zero)) (.mul .zero (.neg (.var 1)))) .zero)) (.mul (.add (.add (.add (.add .zero (.mul (.var 0) .zero)) (.mul .zero .zero)) (.mul .zero (.neg (.var 1)))) (.mul .zero .zero)) (.neg (.var 1)))) (.mul (.add (.add (.add (.add .zero (.mul (.var 0) .zero)) (.mul .zero (.var 1))) (.mul .zero .zero)) (.mul .zero .zero)) .zero)) (.mul (.add (.add (.add (.add .zero (.mul (.var 0) (.var 1))) (.mul .zero .zero)) (.mul .zero .zero)) (.mul .zero .zero)) .zero)) (.mul (.neg (.var 0)) .zero) (by decide +kernel)
  | 3, _, 0, _ =>
    change (0 + (0 + 0 * 0 + ⟨0, i⟩ * 0 + 0 * 0 + 0 * (-⟨i, 0⟩)) * 0 + (0 + 0 * 0 + ⟨0, i⟩ * 0 + 0 * (-⟨i, 0⟩) + 0 * 0) * 0 + (0 + 0 * 0 + ⟨0, i⟩ * ⟨i, 0⟩ + 0 * 0 + 0 * 0) * (-⟨i, 0⟩) + (0 + 0 * ⟨i, 0⟩ + ⟨0, i⟩ * 0 + 0 * 0 + 0 * 0) * 0 : Ext p ν) =
      (-⟨0, i⟩ * -1 : Ext p ν)
    calc _ = -((⟨0, i⟩ : Ext p ν) * (⟨i, 0⟩ * ⟨i, 0⟩)) :=
          FRC.Unitary.xsound (FRC.Unitary.xlook [⟨0, i⟩, ⟨i, 0⟩]) (.add (.add (.add (.add .zero (.mul (.add (.add (.add (.add .zero (.mul .zero .zero)) (.mul (.var 0) .zero)) (.mul .zero .zero)) (.mul .zero (.neg (.var 1)))) .zero)) (.mul (.add (.add (.add (.add .zero (.mul .zero .zero)) (.mul (.var 0) .zero)) (.mul .zero (.neg (.var 1)))) (.mul .zero .zero)) .zero)) (.mul (.add (.add (.add (.add .zero (.mul .zero .zero)) (.mul (.var 0) (.var 1))) (.mul .zero .zero)) (.mul .zero .zero)) (.neg (.var 1)))) (.mul (.add (.add (.add (.add .zero (.mul .zero (.var 1))) (.mul (.var 0) .zero)) (.mul .zero .zero)) (.mul .zero .zero)) .zero)) (.neg (.mul (.var 0) (.mul (.var 1) (.var 1)))) (by decide +kernel)
      _ = -⟨0, i⟩ * -1 := by rw [ii_sq hi, mul_neg_one', Hermitian.neg_neg, ← Hermitian.neg_mul, ← Hermitian.mul_neg, Hermitian.neg_neg, Ext.mul_one]
  | 3, _, 1, _ =>
    change (0 + (0 + 0 * 0 + ⟨0, i⟩ * 0 + 0 * 0 + 0 * (-⟨i, 0⟩)) * 0 + (0 + 0 * 0 + ⟨0, i⟩ * 0 + 0 * (-⟨i, 0⟩) + 0 * 0) * 0 + (0 + 0 * 0 + ⟨0, i⟩ * ⟨i, 0⟩ + 0 * 0 + 0 * 0) * 0 + (0 + 0 * ⟨i, 0⟩ + ⟨0, i⟩ * 0 + 0 * 0 + 0 * 0) * ⟨i, 0⟩ : Ext p ν) =
      (-⟨0, i⟩ * 0 : Ext p ν)
    exact FRC.Unitary.xsound (FRC.Unitary.xlook [⟨0, i⟩, ⟨i, 0⟩]) (.add (.add (.add (.add .zero (.mul (.add (.add (.add (.add .zero (.mul .zero .zero)) (.mul (.var 0) .zero)) (.mul .zero .zero)) (.mul .zero (.neg (.var 1)))) .zero)) (.mul (.add (.add (.add (.add .zero (.mul .zero .zero)) (.mul (.var 0) .zero)) (.mul .zero (.neg (.var 1)))) (.mul .zero .zero)) .zero)) (.mul (.add (.add (.add (.add .zero (.mul .zero .zero)) (.mul (.var 0) (.var 1))) (.mul .zero .zero)) (.mul .zero .zero)) .zero)) (.mul (.add (.add (.add (.add .zero (.mul .zero (.var 1))) (.mul (.var 0) .zero)) (.mul .zero .zero)) (.mul .zero .zero)) (.var 1))) (.mul (.neg (.var 0)) .zero) (by decide +kernel)
  | 3, _, 2, _ =>
    change (0 + (0 + 0 * 0 + ⟨0, i⟩ * 0 + 0 * 0 + 0 * (-⟨i, 0⟩)) * ⟨i, 0⟩ + (0 + 0 * 0 + ⟨0, i⟩ * 0 + 0 * (-⟨i, 0⟩) + 0 * 0) * 0 + (0 + 0 * 0 + ⟨0, i⟩ * ⟨i, 0⟩ + 0 * 0 + 0 * 0) * 0 + (0 + 0 * ⟨i, 0⟩ + ⟨0, i⟩ * 0 + 0 * 0 + 0 * 0) * 0 : Ext p ν) =
      (-⟨0, i⟩ * 0 : Ext p ν)
    exact FRC.Unitary.xsound (FRC.Unitary.xlook [⟨0, i⟩, ⟨i, 0⟩]) (.add (.add (.add (.add .zero (.mul (.add (.add (.add (.add .zero (.mul .zero .zero)) (.mul (.var 0) .zero)) (.mul .zero .zero)) (.mul .zero (.neg (.var 1)))) (.var 1))) (.mul (.add (.add (.add (.add .zero (.mul .zero .zero)) (.mul (.var 0) .zero)) (.mul .zero (.neg (.var 1)))) (.mul .zero .zero)) .zero)) (.mul (.add (.add (.add (.add .zero (.mul .zero .zero)) (.mul (.var 0) (.var 1))) (.mul .zero .zero)) (.mul .zero .zero)) .zero)) (.mul (.add (.add (.add (.add .zero (.mul .zero (.var 1))) (.mul (.var 0) .zero)) (.mul .zero .zero)) (.mul .zero .zero)) .zero)) (.mul (.neg (.var 0)) .zero) (by decide +kernel)
  | 3, _, 3, _ =>
    change (0 + (0 + 0 * 0 + ⟨0, i⟩ * 0 + 0 * 0 + 0 * (-⟨i, 0⟩)) * 0 + (0 + 0 * 0 + ⟨0, i⟩ * 0 + 0 * (-⟨i, 0⟩) + 0 * 0) * (-⟨i, 0⟩) + (0 + 0 * 0 + ⟨0, i⟩ * ⟨i, 0⟩ + 0 * 0 + 0 * 0) * 0 + (0 + 0 * ⟨i, 0⟩ + ⟨0, i⟩ * 0 + 0 * 0 + 0 * 0) * 0 : Ext p ν) =
      (-⟨0, i⟩ * 0 : Ext p ν)
    exact FRC.Unitary.xsound (FRC.Unitary.xlook [⟨0, i⟩, ⟨i, 0⟩]) (.add (.add (.add (.add .zero (.mul (.add (.add (.add (.add .zero (.mul .zero .zero)) (.mul (.var 0) .zero)) (.mul .zero .zero)) (.mul .zero (.neg (.var 1)))) .zero)) (.mul (.add (.add (.add (.add .zero (.mul .zero .zero)) (.mul (.var 0) .zero)) (.mul .zero (.neg (.var 1)))) (.mul .zero .zero)) (.neg (.var 1)))) (.mul (.add (.add (.add (.add .zero (.mul .zero .zero)) (.mul (.var 0) (.var 1))) (.mul .zero .zero)) (.mul .zero .zero)) .zero)) (.mul (.add (.add (.add (.add .zero (.mul .zero (.var 1))) (.mul (.var 0) .zero)) (.mul .zero .zero)) (.mul .zero .zero)) .zero)) (.mul (.neg (.var 0)) .zero) (by decide +kernel)
  | a + 4, ha, _, _ => exact absurd ha (Nat.not_lt.mpr (Nat.le_add_left 4 a))
  | _, _, b + 4, hb => exact absurd hb (Nat.not_lt.mpr (Nat.le_add_left 4 b))

/-! ### The extension has no zero divisors when `ν` is a nonsquare -/

/-- `norm z = 0 → z = 0` when `ν` is a nonsquare: `z.re² = ν z.im²`, and `z.im ≠ 0` would make `ν = (z.re/z.im)²` a square. -/
theorem eq_zero_of_norm_eq_zero {κ : Nat} {g : Shell p} (F : Frame p κ g) (hns : ¬ ∃ r : Shell p, r * r = ν) {z : Ext p ν}
    (h : Ext.norm z = 0) : z = 0 := by
  have hsq : z.re * z.re = ν * (z.im * z.im) := by
    have := Shell.eq_neg_of_add_eq_zero h
    rw [Shell.neg_neg] at this; exact this
  cases Nat.decEq z.im.val 0 with
  | isTrue e0 =>
    have him : z.im = 0 := Shell.ext e0
    rw [him, Shell.mul_zero, Shell.mul_zero] at hsq
    have hre : z.re = 0 := by
      rcases F.mul_eq_zero hsq with h1 | h1 <;> exact h1
    exact Ext.ext hre him
  | isFalse e0 =>
    have him : z.im ≠ 0 := fun e => e0 (congrArg Shell.val e)
    obtain ⟨u, hu⟩ := F.exists_inv him
    exfalso; apply hns
    refine ⟨z.re * u, ?_⟩
    have h1 : z.re * u * (z.re * u) = z.re * z.re * (u * u) :=
      Shell.Frame.RE.sound (Shell.Frame.look [z.re, u]) (.mul (.mul (.var 0) (.var 1)) (.mul (.var 0) (.var 1)))
        (.mul (.mul (.var 0) (.var 0)) (.mul (.var 1) (.var 1))) (by decide +kernel)
    have h2 : ν * (z.im * z.im) * (u * u) = ν * ((z.im * u) * (z.im * u)) :=
      Shell.Frame.RE.sound (Shell.Frame.look [ν, z.im, u]) (.mul (.mul (.var 0) (.mul (.var 1) (.var 1))) (.mul (.var 2) (.var 2)))
        (.mul (.var 0) (.mul (.mul (.var 1) (.var 2)) (.mul (.var 1) (.var 2)))) (by decide +kernel)
    rw [h1, hsq, h2, hu, Shell.mul_one, Shell.mul_one]

/-- No zero divisors in the extension of a nonsquare `ν`. -/
theorem ext_mul_eq_zero {κ : Nat} {g : Shell p} (F : Frame p κ g) (hns : ¬ ∃ r : Shell p, r * r = ν) {z z' : Ext p ν}
    (h : z * z' = 0) : z = 0 ∨ z' = 0 := by
  have hn : Ext.norm z * Ext.norm z' = 0 := by
    rw [← Ext.norm_mul, h]; show (0 : Shell p) * 0 + -(ν * (0 * 0)) = 0
    rw [Shell.mul_zero, Shell.mul_zero, Shell.neg_zero, Shell.add_zero]
  rcases F.mul_eq_zero hn with h1 | h1
  · exact Or.inl (eq_zero_of_norm_eq_zero F hns h1)
  · exact Or.inr (eq_zero_of_norm_eq_zero F hns h1)

/-- 8:D21 — the normalisation leaves the sign: a twist `X'` with `X'² = ν I` is `X` or `−X`, `X = −i w E` the spinor
form, on every frame with `i² = −1` and `ν` a nonsquare. The `(0,0)` entry of `X'² = ν I` reads `−X'₀₃² = ν`, so
`X'₀₃² = (i w)²` and `(X'₀₃ − i w)(X'₀₃ + i w) = 0` in the field `K`. -/
theorem twist_unique_sign {κ : Nat} {g : Shell p} (F : Frame p κ g) {i : Shell p} (hi : i * i = -1)
    (hns : ¬ ∃ r : Shell p, r * r = ν) (X : MatE p ν 4) (h : Twists i X) (hX : X * X ≈ smulE ⟨ν, 0⟩ 1) :
    X ≈ smulE (-⟨0, i⟩) E4 ∨ X ≈ smulE ⟨0, i⟩ E4 := by
  have hν : ν ≠ 0 := fun e => hns ⟨0, by rw [e, Shell.mul_zero]⟩
  have hX' := twist_unique F hi hν X h
  have x00 : X.f 0 0 = 0 := by have := hX' 0 (by decide) 0 (by decide); change X.f 0 0 = X.f 0 3 * 0 at this; rw [Hermitian.mul_zero] at this; exact this
  have x01 : X.f 0 1 = 0 := by have := hX' 0 (by decide) 1 (by decide); change X.f 0 1 = X.f 0 3 * 0 at this; rw [Hermitian.mul_zero] at this; exact this
  have x10 : X.f 1 0 = 0 := by have := hX' 1 (by decide) 0 (by decide); change X.f 1 0 = X.f 0 3 * 0 at this; rw [Hermitian.mul_zero] at this; exact this
  have x02 : X.f 0 2 = 0 := by have := hX' 0 (by decide) 2 (by decide); change X.f 0 2 = X.f 0 3 * 0 at this; rw [Hermitian.mul_zero] at this; exact this
  have x20 : X.f 2 0 = 0 := by have := hX' 2 (by decide) 0 (by decide); change X.f 2 0 = X.f 0 3 * 0 at this; rw [Hermitian.mul_zero] at this; exact this
  have x30 : X.f 3 0 = -X.f 0 3 := by
    have := hX' 3 (by decide) 0 (by decide); change X.f 3 0 = X.f 0 3 * -1 at this
    rw [← Hermitian.mul_neg, Ext.mul_one] at this; exact this
  have e := hX 0 (by decide) 0 (by decide)
  change 0 + X.f 0 0 * X.f 0 0 + X.f 0 1 * X.f 1 0 + X.f 0 2 * X.f 2 0 + X.f 0 3 * X.f 3 0 = ⟨ν, 0⟩ * 1 at e
  rw [x00, x01, x10, x02, x20, x30] at e
  simp only [Hermitian.mul_zero, Hermitian.zero_add, ← Hermitian.mul_neg, Ext.mul_one] at e
  -- `e : -(f f) = ⟨ν, 0⟩`, so `f f = (i w)²`
  have hff : X.f 0 3 * X.f 0 3 = ⟨0, i⟩ * ⟨0, i⟩ := by
    rw [iw_sq hi]
    have := congrArg (- ·) e
    rw [Hermitian.neg_neg, neg_mk, Shell.neg_zero] at this
    exact this
  have hprod : (X.f 0 3 + -⟨0, i⟩) * (X.f 0 3 + ⟨0, i⟩) = 0 := by
    have hid : (X.f 0 3 + -⟨0, i⟩) * (X.f 0 3 + ⟨0, i⟩) = X.f 0 3 * X.f 0 3 + -(⟨0, i⟩ * ⟨0, i⟩) :=
      FRC.Unitary.xsound (FRC.Unitary.xlook [X.f 0 3, ⟨0, i⟩]) (.mul (.add (.var 0) (.neg (.var 1))) (.add (.var 0) (.var 1)))
        (.add (.mul (.var 0) (.var 0)) (.neg (.mul (.var 1) (.var 1)))) (by decide +kernel)
    rw [hid, hff, Hermitian.add_neg]
  rcases ext_mul_eq_zero F hns hprod with h1 | h1
  · right
    have hf : X.f 0 3 = ⟨0, i⟩ := by
      have := Shell.eq_neg_of_add_eq_zero (Ext.re_congr h1)
      have h' := Shell.eq_neg_of_add_eq_zero (Ext.im_congr h1)
      exact Ext.ext (by rw [this]; exact Shell.neg_neg _) (by rw [h']; exact Shell.neg_neg _)
    rw [← hf]; exact hX'
  · left
    have hf : X.f 0 3 = -⟨0, i⟩ := Ext.ext (Shell.eq_neg_of_add_eq_zero (Ext.re_congr h1)) (Shell.eq_neg_of_add_eq_zero (Ext.im_congr h1))
    rw [← hf]; exact hX'

end MatE

/-! ## The decided witnesses on the standard shells, on the packed arithmetic -/
section witnesses
open FRC.Dirac Mat FRC.Dirac.Packed

/-! ### Rows of the cycle as rows of residues, kept packed between the products -/

/-- A real row of the cycle (a row of residues), a row over `K` as the pair of its residue rows (the real and the
`w` parts), and their packed forms. -/
abbrev RRow := List Nat
abbrev NRow := List Nat × List Nat
abbrev PRow := Nat × Nat
def packRow (a : NRow) : PRow := (pack a.1, pack a.2)
def unpackRow (p n : Nat) (A : PRow) : NRow := (unpack p n A.1, unpack p n A.2)

/-- The zero row, the identity, the translation `T` (first row `(0, 1, 0, …)`), `T − 1`, the symmetric difference
`h (T − T⁻¹)` and `−Δ = 2 − T − T⁻¹` (the theme's `kineticRow`) on the cycle of `p` sites, as rows of residues. -/
def zeroR (n : Nat) : RRow := List.replicate n 0
def idR (n : Nat) : RRow := (List.range n).map fun j => if j = 0 then 1 else 0
def shiftR (n : Nat) : RRow := (List.range n).map fun j => if j = 1 then 1 else 0
def shiftMinusOneR (p : Nat) : RRow := (List.range p).map fun j => if j = 0 then p - 1 else if j = 1 then 1 else 0
def symDiffR (p h : Nat) : RRow := (List.range p).map fun j => if j = 1 then h else if j + 1 = p then p - h else 0
def kineticR (p : Nat) : RRow :=
  (List.range p).map fun j => if j = 0 then 2 else if j = 1 ∨ j + 1 = p then p - 1 else 0
def idN (n : Nat) : NRow := (idR n, zeroR n)
/-- `α H` for `α = λ w` and a real row `H`: the real part zero, the `w` part `λ H`. -/
def wsmul (p lam : Nat) (H : RRow) : NRow := (List.replicate H.length 0, H.map fun x => lam * x % p)

/-- The products and the sum on the cycle of `n` sites, on packed rows (`Packed.rmul`, `Packed.pmul`, `Packed.padd`;
sound by `Packed.rmul_eq`, `Packed.pmul_eq`, `Packed.padd_eq`, the slots by `Packed.le_two_pow_slots`), and the
product of two rows over `K`. -/
def rmulN (p n : Nat) (A C : Nat) : Nat := rmul p n (slots n) A C
def pmulN (p ν n : Nat) (A C : PRow) : PRow := pmul p ν n (slots n) A C
def paddN (p n : Nat) (A C : PRow) : PRow := (padd p (slots n) A.1 C.1, padd p (slots n) A.2 C.2)
def cmul (p ν n : Nat) (a b : NRow) : NRow := unpackRow p n (pmulN p ν n (packRow a) (packRow b))

/-- Powers by squaring on packed rows (the exponent as its own fuel): real rows and rows over `K`. -/
def rpowP (p n : Nat) (A : Nat) : Nat → Nat → Nat
  | 0, _ => pack (idR n)
  | fuel + 1, e =>
    if e = 0 then pack (idR n)
    else
      let h := rpowP p n A fuel (e / 2)
      let sq := rmulN p n h h
      if e % 2 = 0 then sq else rmulN p n sq A
def rpow (p n : Nat) (a : RRow) (e : Nat) : RRow := unpack p n (rpowP p n (pack a) e e)
def cpowP (p ν n : Nat) (A : PRow) : Nat → Nat → PRow
  | 0, _ => packRow (idN n)
  | fuel + 1, e =>
    if e = 0 then packRow (idN n)
    else
      let h := cpowP p ν n A fuel (e / 2)
      let sq := pmulN p ν n h h
      if e % 2 = 0 then sq else pmulN p ν n sq A
def cpow (p ν n : Nat) (a : NRow) (e : Nat) : NRow := unpackRow p n (cpowP p ν n (packRow a) e e)

/-- `(Π_{i<k} (1 + X^{2^i}), X^{2^k})`: the first is `Σ_{j<2^k} X^j`, the inverse of `1 − X` when `X^{2^k} = 0`, in
`2k` products. -/
def geomInvP (p ν n : Nat) (X : PRow) : Nat → PRow × PRow
  | 0 => (packRow (idN n), X)
  | k + 1 =>
    let r := geomInvP p ν n X k
    (pmulN p ν n r.1 (paddN p n (packRow (idN n)) r.2), pmulN p ν n r.2 r.2)

/-- The Cayley step `U = (1 − αH)⁻¹(1 + αH)` of a real row `H` at `α = λ w` on the cycle of `p` sites, the inverse
by `geomInvP` over `slots p + 4` doublings (`2^{slots p + 4} = 16 · 2^{slots p} ≥ p` by `Packed.le_two_pow_slots`;
`(αH)^p = 0` is decided alongside). -/
def cayleyN (p ν lam : Nat) (H : RRow) : NRow :=
  let N := packRow (wsmul p lam H)
  unpackRow p p (pmulN p ν p (geomInvP p ν p N (slots p + 4)).1 (paddN p p (packRow (idN p)) N))

/-- The conjugate transpose of a circulant, by its first row: `b_k = conj a_{−k}`, the row reversed past its
first entry and the `w` part negated. -/
def daggerN (p : Nat) (a : NRow) : NRow :=
  match a.1 with
  | x :: xs =>
    match a.2 with
    | y :: ys => (x :: xs.reverse, ((p - y) % p) :: (ys.reverse.map fun v => (p - v) % p))
    | [] => a
  | [] => a

/-! ### The cycles: the translation, the differences and `−Δ` at 13, 173 and 1549 -/

/-- 8:F7, 8:D10, 8:X3 [value] — on the cycle of `𝔽₁₃`: `T^p = 1`, `(T − 1)^p = 0`, the symmetric difference
`∇^s = 2⁻¹(T − T⁻¹)` has `(∇^s)^p = 0`, and `(−Δ)^p = 0` (the kinetic sector unipotent; the general statements
`translation_unipotent`, `symdiff_nilpotent`). -/
theorem translation_values13 :
    rpow 13 13 (shiftR 13) 13 = idR 13 ∧ rpow 13 13 (shiftMinusOneR 13) 13 = zeroR 13 ∧
      rpow 13 13 (symDiffR 13 7) 13 = zeroR 13 ∧ (2 : Shell 13) * 7 = 1 ∧ rpow 13 13 (kineticR 13) 13 = zeroR 13 := by
  decide +kernel

/-- 8:F7, 8:D10, 8:X3 [value] — the same on the cycle of `𝔽₁₇₃`. -/
theorem translation_values173 :
    rpow 173 173 (shiftR 173) 173 = idR 173 ∧ rpow 173 173 (shiftMinusOneR 173) 173 = zeroR 173 ∧
      rpow 173 173 (symDiffR 173 87) 173 = zeroR 173 ∧ (2 : Shell 173) * 87 = 1 ∧
      rpow 173 173 (kineticR 173) 173 = zeroR 173 := by
  decide +kernel

/-- 8:F7, 8:D10, 8:X3 [value] — on the cycle of `𝔽₁₅₄₉`: `T^p = 1` and `(T − 1)^p = 0`. -/
theorem translation_values1549 :
    rpow 1549 1549 (shiftR 1549) 1549 = idR 1549 ∧ rpow 1549 1549 (shiftMinusOneR 1549) 1549 = zeroR 1549 := by
  decide +kernel

/-- 8:F7, 8:D10, 8:X3 [value] — on the cycle of `𝔽₁₅₄₉`: `(∇^s)^p = 0` with `2⁻¹ = 775`, and `(−Δ)^p = 0`. -/
theorem kinetic_values1549 :
    rpow 1549 1549 (symDiffR 1549 775) 1549 = zeroR 1549 ∧ (2 : Shell 1549) * 775 = 1 ∧
      rpow 1549 1549 (kineticR 1549) 1549 = zeroR 1549 := by
  decide +kernel

/-! ### The Cayley step of `−Δ` at 173 and 1549 -/

/-- 8:C4, 8:C6, 8:C15, 8:E4, 8:E7 [value] — the Cayley step `U = (1 − αH)⁻¹(1 + αH)` of `H = −Δ` on the cycle of
`𝔽₁₇₃`, at `α = w` and at `α = c = λw` with `λ = 87`, `c² = 87 = 2⁻¹`: `(wH)^p = 0` (so `geomInvP` is the inverse,
for `α = λw` too), `U ≠ 1` and `U^p = 1`, so the order is exactly `p`, and `U†U = 1` at `α = w` — the 173 sibling of
`cayley13_values`. -/
theorem cayley_values173 :
    cpow 173 2 173 (wsmul 173 1 (kineticR 173)) 173 = (zeroR 173, zeroR 173) ∧
      cayleyN 173 2 1 (kineticR 173) ≠ idN 173 ∧ cpow 173 2 173 (cayleyN 173 2 1 (kineticR 173)) 173 = idN 173 ∧
      cmul 173 2 173 (daggerN 173 (cayleyN 173 2 1 (kineticR 173))) (cayleyN 173 2 1 (kineticR 173)) = idN 173 ∧
      cayleyN 173 2 87 (kineticR 173) ≠ idN 173 ∧ cpow 173 2 173 (cayleyN 173 2 87 (kineticR 173)) 173 = idN 173 ∧
      ((⟨0, 87⟩ : Ext 173 2) * ⟨0, 87⟩ = 87 ∧ (2 : Shell 173) * 87 = 1) := by
  decide +kernel

/-- 8:C4, 8:C6, 8:C15, 8:E4, 8:E7 [value] — on the cycle of `𝔽₁₅₄₉`, in four declarations (each decided within the
budget of a kernel call): `(wH)^p = 0` for `H = −Δ`, and the data of `c = λw`, `λ = 775`, `c² = 775 = 2⁻¹`. -/
theorem cayley_nilpotent1549 :
    cpow 1549 2 1549 (wsmul 1549 1 (kineticR 1549)) 1549 = (zeroR 1549, zeroR 1549) ∧
      ((⟨0, 775⟩ : Ext 1549 2) * ⟨0, 775⟩ = 775 ∧ (2 : Shell 1549) * 775 = 1) := by
  decide +kernel

/-- 8:C4, 8:C6, 8:C15, 8:E4, 8:E7 [value] — on `𝔽₁₅₄₉`, the Cayley step of `−Δ` at `α = w`: `U ≠ 1`, `U^p = 1`. -/
theorem cayley_step1549 :
    cayleyN 1549 2 1 (kineticR 1549) ≠ idN 1549 ∧
      cpow 1549 2 1549 (cayleyN 1549 2 1 (kineticR 1549)) 1549 = idN 1549 := by
  decide +kernel

/-- 8:C4, 8:C6, 8:E4 [value] — on `𝔽₁₅₄₉`, the Cayley step of `−Δ` at `α = w` is unitary: `U†U = 1`. -/
theorem cayley_unitary1549 :
    cmul 1549 2 1549 (daggerN 1549 (cayleyN 1549 2 1 (kineticR 1549))) (cayleyN 1549 2 1 (kineticR 1549)) =
      idN 1549 := by
  decide +kernel

/-- 8:C15, 8:E7 [value] — on `𝔽₁₅₄₉`, the Cayley step of `−Δ` at `α = c = 775 w`: `U ≠ 1`, `U^p = 1`. -/
theorem cayley_step_c1549 :
    cayleyN 1549 2 775 (kineticR 1549) ≠ idN 1549 ∧
      cpow 1549 2 1549 (cayleyN 1549 2 775 (kineticR 1549)) 1549 = idN 1549 := by
  decide +kernel

/-! ### Matrices as pairs of residue matrices, and their packed products -/

/-- A matrix over `K` as the pair of its residue matrices; the residue matrices of a matrix of the theme file. -/
abbrev NMat := List (List Nat) × List (List Nat)
def toN (M : Mat p ν) : NMat := (M.map (·.map fun z => z.re.val), M.map (·.map fun z => z.im.val))

/-- The product, by the packed combinations of rows (`Packed.mulExtPacked`, sound by `Packed.mulExtPacked_eq`). -/
def mmulN (p ν n : Nat) (A B : NMat) : NMat := mulExtPacked p ν n A (B.1.map pack, B.2.map pack)

def identN (n : Nat) : NMat :=
  ((List.range n).map fun i => (List.range n).map fun j => if i = j then 1 else 0,
   (List.range n).map fun _ => List.replicate n 0)

def mpowAux (p ν n : Nat) (A : NMat) : Nat → Nat → NMat
  | 0, _ => identN n
  | fuel + 1, e =>
    if e = 0 then identN n
    else
      let h := mpowAux p ν n A fuel (e / 2)
      let sq := mmulN p ν n h h
      if e % 2 = 0 then sq else mmulN p ν n sq A
def mpowN (p ν n : Nat) (A : NMat) (e : Nat) : NMat := mpowAux p ν n A e e

/-- The circulant `n × n` matrix of a first row, and the Kronecker product of two list matrices (the theme's
matrices over `K`). -/
def circMat (n : Nat) (a : List (Ext p ν)) : Mat p ν :=
  (List.range n).map fun i => (List.range n).map fun j => nth 0 a ((j + n - i) % n)
def kron (A B : Mat p ν) : Mat p ν :=
  A.flatMap fun r => B.map fun s => r.flatMap fun x => s.map fun y => x * y
def symDiffRow (n : Nat) (h : Ext p ν) : List (Ext p ν) :=
  (List.range n).map fun j => if j = 1 then h else if j + 1 = n then -h else 0

/-- 8:D3 [value] — the factorisation in `0+1` on `𝔽₁₃` (`ν = 2`, `i = 5`), on the `52 × 52` matrices: for
`𝒟^s = ∇^s ⊗ γ⁰` and `m = 1`, `(𝒟^s − 1)(𝒟^s + 1) = −ν (∇^s)² ⊗ I₄ − I₅₂`, as `dirac_factorisation` states with
`η₀ = γ⁰γ⁰ = −ν`; the product on the packed rows. -/
theorem factorisation_value :
    let d : List (Ext 13 2) := symDiffRow 13 7
    let D : Mat 13 2 := kron (circMat 13 d) (gamma0 5)
    mmulN 13 2 52 (toN (add D (neg (ident 52)))) (toN (add D (ident 52))) =
      toN (add (smul (-(2 : Ext 13 2)) (kron (circMat 13 (cyc 13 d d)) (ident 4))) (neg (ident 52))) := by
  decide +kernel

/-- 8:E8 [value] — the three cycles in dynamical roles: `lcm(13, 14) = 182`, and the mixed step `U = M⁻¹P` of
`H = −Δ + V_id` on `𝔽₁₃` (`M = 1 − wH`, `P = 1 + wH`, commuting) has `U^{13} ≠ 1`, `U^{14} ≠ 1`, `U^{182} ≠ 1`,
since `U^k = 1` exactly when `P^k = M^k`: it closes on neither the register nor the third cycle nor their least common
period (`mixed_step_closure` has every cycle of the shell). -/
theorem mixed_step_values :
    Nat.lcm 13 14 = 182 ∧
    let H : Mat 13 2 := add (circMat 13 (kineticRow 13 2))
      ((List.range 13).map fun i => (List.range 13).map fun j => if i = j then ⟨ofNat i, 0⟩ else 0)
    let M : NMat := toN (add (ident 13) (neg (smul ⟨0, 1⟩ H)))
    let P : NMat := toN (add (ident 13) (smul ⟨0, 1⟩ H))
    mmulN 13 2 13 M P = mmulN 13 2 13 P M ∧ mpowN 13 2 13 P 13 ≠ mpowN 13 2 13 M 13 ∧
      mpowN 13 2 13 P 14 ≠ mpowN 13 2 13 M 14 ∧ mpowN 13 2 13 P 182 ≠ mpowN 13 2 13 M 182 := by
  decide +kernel

/-- 8:E8 [value] — the mixed step of `H = −Δ + V_id` on `𝔽₁₃` has no eigenvalue in `K` and closes on no cycle of the shell.
The monic `q = x¹³ − x + 2` (the package's `χ_H`) annihilates `H`, `q(H) = 0` by Horner on the matrices, and has no root in
`K`, so an eigenvalue `λ ∈ K` (`Hv = λv`, `q(λ)v = q(H)v = 0`) is impossible. `P^{2184} ≠ M^{2184}`, i.e. `U^{2184} ≠ 1`
for `2184 = p(p² − 1)`, the least common period of the register, the drive cycle, the third cycle and `K^×`: a closure
`U^t = 1` at a divisor `t` of `2184` would give `U^{2184} = 1`, so the step closes on no cycle of the shell, as Lemma
eigenphase-law (iii) requires of a step with an eigenvalue of degree three or more. The irreducibility of `q` over `𝔽₁₃`
is the package's record. -/
theorem mixed_step_closure :
    let H : Mat 13 2 := add (circMat 13 (kineticRow 13 2))
      ((List.range 13).map fun i => (List.range 13).map fun j => if i = j then ⟨ofNat i, 0⟩ else 0)
    let M : NMat := toN (add (ident 13) (neg (smul ⟨0, 1⟩ H)))
    let P : NMat := toN (add (ident 13) (smul ⟨0, 1⟩ H))
    let q : List (Ext 13 2) := [2, 12, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1]
    q.reverse.foldl (fun acc c => add (mul acc H) (smul c (ident 13))) (smul (0 : Ext 13 2) (ident 13)) =
      smul (0 : Ext 13 2) (ident 13) ∧
    (∀ a b : Shell 13, q.foldr (fun c acc => c + (⟨a, b⟩ : Ext 13 2) * acc) 0 ≠ 0) ∧
    mmulN 13 2 13 M P = mmulN 13 2 13 P M ∧ mpowN 13 2 13 P 2184 ≠ mpowN 13 2 13 M 2184 := by
  decide +kernel

/-- 8:D11 [value] — the spinor form transports by the norm of the lift: `S† X S = N(z) X` for `S = x I₄ + y γ⁰γ¹`,
`X = γ⁰γ¹γ³`, at `x = y = 1` (`N = 1 − ν = −1`) on `𝔽₁₃`, `𝔽₁₇₃` and `𝔽₁₅₄₉`. -/
theorem lift_transport_values :
    (dagger (spinLift 5 1 1) * (gamma0 5 * gamma1 5 * gamma3 5) * spinLift 5 1 1 : Mat 13 2) =
      smul (-1) (gamma0 5 * gamma1 5 * gamma3 5) ∧
    (dagger (spinLift 93 1 1) * (gamma0 93 * gamma1 93 * gamma3 93) * spinLift 93 1 1 : Mat 173 2) =
      smul (-1) (gamma0 93 * gamma1 93 * gamma3 93) ∧
    (dagger (spinLift 1461 1 1) * (gamma0 1461 * gamma1 1461 * gamma3 1461) * spinLift 1461 1 1 : Mat 1549 2) =
      smul (-1) (gamma0 1461 * gamma1 1461 * gamma3 1461) := by
  decide +kernel

/-- 8:D13 [value] — mass is winding rate, on `𝔽₁₃` in `0+1` (`ν = 2`, `i = 5`, `2⁻¹ = 7`), on the `52 × 52` matrices: the
symmetric Dirac operator `𝒟^s = ∇^s ⊗ γ⁰` develops the translation-invariant spinor `ψ₀` by nothing, and for `m = 1, 2`
the Cayley step of `𝒟^s − m` acts on it as the mass phase alone, `P ψ₀ = φ(−m) M ψ₀` for `M = 1 − w(𝒟^s − m)`,
`P = 1 + w(𝒟^s − m)` (so `U ψ₀ = M⁻¹ P ψ₀ = φ(−m) ψ₀`), with `φ(−1) = 10 + 2w` and `φ(−2) = 8 + 8w` on the norm-one
cycle (`drive_eigen` is the drive's side of the balance, `dirac_factorisation` its square). -/
theorem mass_winding_values :
    let D : Mat 13 2 := kron (circMat 13 (symDiffRow 13 7)) (gamma0 5)
    let psi : Mat 13 2 := (List.range 52).map fun r => [if r % 4 = 0 then 1 else 0]
    let M (m : Ext 13 2) : Mat 13 2 := add (ident 52) (neg (smul ⟨0, 1⟩ (add D (neg (smul m (ident 52))))))
    let P (m : Ext 13 2) : Mat 13 2 := add (ident 52) (smul ⟨0, 1⟩ (add D (neg (smul m (ident 52)))))
    (2 : Shell 13) * 7 = 1 ∧ mul D psi = (List.range 52).map (fun _ => [0]) ∧
    mul (P 1) psi = smul (phi 2 12) (mul (M 1) psi) ∧ (phi 2 12 : Ext 13 2) = ⟨10, 2⟩ ∧
    mul (P 2) psi = smul (phi 2 11) (mul (M 2) psi) ∧ (phi 2 11 : Ext 13 2) = ⟨8, 8⟩ := by
  decide +kernel

/-- 8:E9 [value] — the closure of a Cayley step at the instance: the step `U = M⁻¹P` of `H = −Δ + M_V`, `V = (1, 1, 0, …, 0)`,
on `𝔽₁₃` (`M = 1 − wH`, `P = 1 + wH`, commuting) has the eigenvector of the degree-two eigenvalue `2 + 2w` exhibited,
`H v = (2 + 2w) v`, and closes on no cycle of the shell: `P^{2184} ≠ M^{2184}`, i.e. `U^{2184} ≠ 1` for
`2184 = p(p² − 1)`, so `U^t ≠ 1` for every divisor `t` of `2184` (a closure at `t` would close `2184`), as Lemma
eigenphase-law (iii) requires of a step with an eigenvalue of degree three or more (the two cubic factors of `χ_H` are
the package's record). -/
theorem eigenphase_closure_values :
    let V : Mat 13 2 := (List.range 13).map fun i => (List.range 13).map fun j => if i = j ∧ i < 2 then 1 else 0
    let H : Mat 13 2 := add (circMat 13 (kineticRow 13 2)) V
    let M : NMat := toN (add (ident 13) (neg (smul ⟨0, 1⟩ H)))
    let P : NMat := toN (add (ident 13) (smul ⟨0, 1⟩ H))
    let v : Mat 13 2 := [[⟨0, 3⟩], [⟨0, 3⟩], [⟨1, 0⟩], [⟨0, 8⟩], [⟨6, 0⟩], [⟨0, 6⟩], [⟨9, 0⟩], [⟨0, 2⟩], [⟨9, 0⟩], [⟨0, 6⟩],
      [⟨6, 0⟩], [⟨0, 8⟩], [⟨1, 0⟩]]
    mul H v = smul ⟨2, 2⟩ v ∧
    mmulN 13 2 13 M P = mmulN 13 2 13 P M ∧ mpowN 13 2 13 P 2184 ≠ mpowN 13 2 13 M 2184 := by
  decide +kernel

/-- 8:D20 [value] — the square bound at the instance: on `𝔽₁₃` in `0+1`, on the `52 × 52` matrices, `(𝒟^s)^{13} = 0` and
`(𝒟^s)^{12} ≠ 0`, the nilpotency index `13 = p` within the bound `2p = 26` of `dirac_square_nilpotent` (the indices `25`,
`26`, `26` on two, three and four coordinate directions are the package's records). -/
theorem dirac_square_values :
    let D : NMat := toN (kron (circMat 13 (symDiffRow 13 7)) (gamma0 5) : Mat 13 2)
    let Z : NMat := toN (smul (0 : Ext 13 2) (ident 52))
    mpowN 13 2 52 D 13 = Z ∧ mpowN 13 2 52 D 12 ≠ Z := by
  decide +kernel

end witnesses

end FRC.Dirac.Spinor
