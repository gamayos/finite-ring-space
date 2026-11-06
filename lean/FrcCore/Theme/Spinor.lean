import FrcCore.Theme.Packed
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
since `U^k = 1` exactly when `P^k = M^k`: neither cycle, nor their least common period, is its period (the exact
order `(13¹³ + 1)/2` is the package's certificate). -/
theorem mixed_step_values :
    Nat.lcm 13 14 = 182 ∧
    let H : Mat 13 2 := add (circMat 13 (kineticRow 13 2))
      ((List.range 13).map fun i => (List.range 13).map fun j => if i = j then ⟨ofNat i, 0⟩ else 0)
    let M : NMat := toN (add (ident 13) (neg (smul ⟨0, 1⟩ H)))
    let P : NMat := toN (add (ident 13) (smul ⟨0, 1⟩ H))
    mmulN 13 2 13 M P = mmulN 13 2 13 P M ∧ mpowN 13 2 13 P 13 ≠ mpowN 13 2 13 M 13 ∧
      mpowN 13 2 13 P 14 ≠ mpowN 13 2 13 M 14 ∧ mpowN 13 2 13 P 182 ≠ mpowN 13 2 13 M 182 := by
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
