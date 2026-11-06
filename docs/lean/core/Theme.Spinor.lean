import FrcCore.Theme.Unipotent
import FrcCore.Theme.Hermitian
import FrcCore.Theme.Dirac

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

end MatE

/-! ## The decided witnesses on the standard shells -/
section witnesses
open FRC.Dirac Mat

/-- The cyclic convolution of two first rows, row `k` as the dot product of `a` with `b` read backwards from `k`
(`b_k, b_{k−1}, …, b_0, b_{n−1}, …, b_{k+1}`): the theme's `cyc` by rotations instead of indexed access, which the
kernel evaluates in `n²` steps. -/
def cycR (n : Nat) (a b : List (Ext p ν)) : List (Ext p ν) :=
  (List.range n).map fun k => dot a ((b.take (k + 1)).reverse ++ (b.drop (k + 1)).reverse)

/-- Powers of a circulant by squaring (fuel the exponent itself; `e / 2 < e` for `e > 0`). -/
def cycPowAux (n : Nat) (a : List (Ext p ν)) : Nat → Nat → List (Ext p ν)
  | 0, _ => cycId n
  | fuel + 1, e =>
    if e = 0 then cycId n
    else
      let h := cycPowAux n a fuel (e / 2)
      let sq := cycR n h h
      if e % 2 = 0 then sq else cycR n sq a
def cycPowBin (n : Nat) (a : List (Ext p ν)) (e : Nat) : List (Ext p ν) := cycPowAux n a e e

/-- The transpose of a list matrix by structural recursion (the theme's `transpose` indexes its columns). -/
def transposeL {α : Type} : List (List α) → List (List α)
  | [] => []
  | r :: rs =>
    match rs with
    | [] => r.map fun x => [x]
    | _ :: _ => List.zipWith (· :: ·) r (transposeL rs)

/-- The product `A B` as the dot products of the rows of `A` with the rows of `Bᵀ`. -/
def mulL (A B : Mat p ν) : Mat p ν :=
  let Bt := transposeL B
  A.map fun r => Bt.map fun c => dot r c

/-- Powers of a matrix by squaring. -/
def powAux (A : Mat p ν) (n : Nat) : Nat → Nat → Mat p ν
  | 0, _ => ident n
  | fuel + 1, e =>
    if e = 0 then ident n
    else
      let h := powAux A n fuel (e / 2)
      let sq := mulL h h
      if e % 2 = 0 then sq else mulL sq A
def powBin (A : Mat p ν) (n e : Nat) : Mat p ν := powAux A n e e

/-- The zero row, the translation `T` (first row `(0, 1, 0, …)`), `T − 1`, and the symmetric difference
`∇^s = h (T − T⁻¹)` with `h = 2⁻¹` supplied. -/
def zeroRow (n : Nat) : List (Ext p ν) := (List.range n).map fun _ => 0
def shiftRow (n : Nat) : List (Ext p ν) := (List.range n).map fun j => if j = 1 then 1 else 0
def shiftMinusOne (n : Nat) : List (Ext p ν) := cycAdd (shiftRow n) (cycSmul (-1) (cycId n))
def symDiffRow (n : Nat) (h : Ext p ν) : List (Ext p ν) :=
  (List.range n).map fun j => if j = 1 then h else if j + 1 = n then -h else 0

/-- The conjugate transpose of a circulant, by its first row: `b_k = conj a_{−k}`. -/
def cycDagger (n : Nat) (a : List (Ext p ν)) : List (Ext p ν) :=
  (List.range n).map fun k => FRC.Extension.Ext.conj (nth 0 a ((n - k) % n))

/-- The circulant `n × n` matrix of a first row, and the Kronecker product of two list matrices. -/
def circMat (n : Nat) (a : List (Ext p ν)) : Mat p ν :=
  (List.range n).map fun i => (List.range n).map fun j => nth 0 a ((j + n - i) % n)
def kron (A B : Mat p ν) : Mat p ν :=
  A.flatMap fun r => B.map fun s => r.flatMap fun x => s.map fun y => x * y

/-- 8:F7, 8:D10, 8:X3 [value] — on the cycle of `𝔽₁₃`: the translation has `T^p = 1`, `T − 1` is nilpotent,
`(T − 1)^p = 0`, and the symmetric difference `∇^s = 2⁻¹(T − T⁻¹)` is nilpotent, `(∇^s)^p = 0` (the kinetic sector
unipotent; the general statements `translation_nilpotent` and `series_inverse`). -/
theorem translation_values13 :
    cycPowBin 13 (shiftRow 13 : List (Ext 13 2)) 13 = cycId 13 ∧
    cycPowBin 13 (shiftMinusOne 13 : List (Ext 13 2)) 13 = zeroRow 13 ∧
    cycPowBin 13 (symDiffRow 13 (7 : Ext 13 2)) 13 = zeroRow 13 ∧ (2 : Shell 13) * 7 = 1 := by
  decide +kernel

/-- 8:C4 [value] — the Cayley step `U = (1 − wH)⁻¹(1 + wH)` of `H = −Δ` on `𝔽₁₃` (`α = w`, `w̄ = −w`) is unitary,
`U†U = 1` (the general statement `cayley_unitary` with `adjoint_dagger`). -/
theorem cayley_unitary_value :
    cycR 13 (cycDagger 13 (cayleyRow ⟨0, 1⟩ (kineticRow 13 2))) (cayleyRow ⟨0, 1⟩ (kineticRow 13 2)) = cycId 13 := by
  decide +kernel

/-- A translation-invariant operator of `0+1` by its kernel: the list of its `4 × 4` blocks at the offsets
`0, …, n−1` (the package's representation); the product is the block convolution, the sum blockwise. -/
def bconv (n : Nat) (A B : List (Mat p ν)) : List (Mat p ν) :=
  (List.range n).map fun k =>
    (List.zipWith mul A ((B.take (k + 1)).reverse ++ (B.drop (k + 1)).reverse)).foldl add
      ((List.range 4).map fun _ => (List.range 4).map fun _ => 0)
def badd (A B : List (Mat p ν)) : List (Mat p ν) := List.zipWith add A B
/-- The scalar kernel `c · 1` (the block `c I₄` at the offset `0`). -/
def bscalar (n : Nat) (c : Ext p ν) : List (Mat p ν) :=
  (List.range n).map fun k => if k = 0 then smul c (ident 4) else (List.range 4).map fun _ => (List.range 4).map fun _ => 0
/-- The kernel of `𝒟^s = ∇^s ⊗ γ⁰` with `∇^s = h (T − T⁻¹)`: `h γ⁰` at the offset `1`, `−h γ⁰` at `n − 1`. -/
def diracKernel (n : Nat) (h : Ext p ν) (G : Mat p ν) : List (Mat p ν) :=
  (List.range n).map fun k =>
    if k = 1 then smul h G else if k + 1 = n then smul (-h) G else (List.range 4).map fun _ => (List.range 4).map fun _ => 0

/-- 8:D3 [value] — the factorisation in `0+1` on `𝔽₁₃` (`ν = 2`, `i = 5`), on the kernels of the translation-invariant
operators: for `𝒟^s = ∇^s ⊗ γ⁰` and `m = 1`, `(𝒟^s − m)(𝒟^s + m) = −ν (∇^s)² ⊗ I₄ − m²`, as `dirac_factorisation`
states with `η₀ = γ⁰γ⁰ = −ν`. -/
theorem factorisation_value :
    let d : List (Ext 13 2) := symDiffRow 13 7
    let D : List (Mat 13 2) := diracKernel 13 7 (gamma0 5)
    bconv 13 (badd D (bscalar 13 (-1))) (badd D (bscalar 13 1)) =
      badd ((cycR 13 d d).map fun c => smul (-(2 : Ext 13 2) * c) (ident 4)) (bscalar 13 (-1)) := by
  decide +kernel

/-- 8:E8 [value] — the three cycles in dynamical roles: `lcm(13, 14) = 182`, and the mixed step `U = M⁻¹P` of
`H = −Δ + V_id` on `𝔽₁₃` (`M = 1 − wH`, `P = 1 + wH`, commuting) has `U^{13} ≠ 1`, `U^{14} ≠ 1`, `U^{182} ≠ 1`,
since `U^k = 1` exactly when `P^k = M^k`: neither cycle, nor their least common period, is its period (the exact
order `(13¹³ + 1)/2` is the package's certificate). -/
theorem mixed_step_values :
    Nat.lcm 13 14 = 182 ∧
    let H : Mat 13 2 := add (circMat 13 (kineticRow 13 2))
      ((List.range 13).map fun i => (List.range 13).map fun j => if i = j then ⟨ofNat i, 0⟩ else 0)
    let M : Mat 13 2 := add (ident 13) (neg (smul ⟨0, 1⟩ H))
    let P : Mat 13 2 := add (ident 13) (smul ⟨0, 1⟩ H)
    let M13 := powBin M 13 13
    let P13 := powBin P 13 13
    let M14 := mulL M13 M
    let P14 := mulL P13 P
    mulL M P = mulL P M ∧ P13 ≠ M13 ∧ P14 ≠ M14 ∧ powBin P14 13 13 ≠ powBin M14 13 13 := by
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

end witnesses

end FRC.Dirac.Spinor
