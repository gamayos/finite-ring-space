import FrcCore.Theme.Spinor
import FrcCore.Theme.Window

/-!
# The Kronecker file of 8-dirac — the Kronecker product and the shell lattice on two coordinate directions, no axioms

The Dirac operator on `r` coordinate directions acts on the functions of the lattice `C_p^r` with values in the spinor
space: its matrix is a sum of Kronecker products `∇_μ ⊗ γ_μ`. This file gives the Kronecker product of two `MatE`
matrices, `(A ⊗ B)_{(a n + b)(c n + d)} = A_{ac} B_{bd}`, as a ring map in each factor (`kron_mul`, `kron_add`,
`kron_neg`, `kron_opow`), the index arithmetic it needs (the quotient `(a n + b) / n = a`, from the division algorithm
`div_spec`, `div_unique` of Window.lean, which belong in `FrcCore.Nat` at the next refactor), the non-vanishing of a Kronecker product of two matrices with a nonzero
entry each, and the two commuting translations `T₀ = S ⊗ 1`, `T₁ = 1 ⊗ S` of the lattice `C_p × C_p`. With the generic
identity `dirac_two_index` of Unipotent.lean this decides the lower bound of row D20 on two directions:
`∇₀^{p−1} ∇₁^{p−1} ≉ 0` on the lattice, the `(0, 0)` entry of `Σ T₀^k · Σ T₁^k` being `1`. No axioms.
-/

namespace FRC.Nat

/-! ## The index of a pair in the block layout (the quotient lemmas `div_spec`, `div_unique` are Window.lean's) -/

/-- The index of the pair `(a, b)` with `b < n` in the block layout: `(a n + b) / n = a` and `(a n + b) % n = b`. -/
theorem pair_div {n a b : Nat} (hb : b < n) : (a * n + b) / n = a := div_unique hb (by rw [Nat.mul_comm a n])

theorem pair_mod {n a b : Nat} (hb : b < n) : (a * n + b) % n = b := by
  rw [Nat.mul_comm a n, add_mul_mod_self_left b a n (pos_of_lt hb), mod_eq_of_lt hb]

theorem pair_lt {m n a b : Nat} (ha : a < m) (hb : b < n) : a * n + b < m * n :=
  Nat.lt_of_lt_of_le (Nat.add_lt_add_left hb _) (by rw [← Nat.succ_mul]; exact Nat.mul_le_mul_right n ha)

/-- Every `i` decomposes as `(i / n) n + i % n`, and `i < m n` forces `i / n < m`. -/
theorem div_add_mod' {n : Nat} (hn : 0 < n) (i : Nat) : i = (i / n) * n + i % n := by
  rw [Nat.mul_comm]; exact div_spec n hn i

theorem div_lt_of_lt_mul' {m n i : Nat} (hn : 0 < n) (h : i < m * n) : i / n < m := by
  have hi := div_add_mod' hn i
  have h2 : i / n * n ≤ i / n * n + i % n := Nat.le_add_right _ _
  rw [← hi] at h2
  cases Nat.lt_or_ge (i / n) m with
  | inl hlt => exact hlt
  | inr hge => exact absurd (Nat.lt_of_lt_of_le h (Nat.le_trans (Nat.mul_le_mul_right n hge) h2)) (Nat.lt_irrefl _)

end FRC.Nat

namespace FRC.Dirac.Spinor

open FRC FRC.Shell FRC.Extension FRC.Dirac.Operator FRC.Dirac.Hermitian

variable {p : Nat} [Pos p] {ν : Shell p}

/-! ## Sums over a block range -/

theorem mul_mul_mul_comm' (x y z w : Ext p ν) : x * y * (z * w) = x * z * (y * w) := by
  rw [Ext.mul_assoc x y (z * w), ← Ext.mul_assoc y z w, Ext.mul_comm y z, Ext.mul_assoc z y w, ← Ext.mul_assoc x z (y * w)]

theorem esum_add_range (F : Nat → Ext p ν) (x : Nat) : ∀ y, esum F (x + y) = esum F x + esum (fun b => F (x + b)) y
  | 0 => (Hermitian.add_zero _).symm
  | y + 1 => by
    show esum F (x + y) + F (x + y) = esum F x + (esum (fun b => F (x + b)) y + F (x + y))
    rw [esum_add_range F x y, Hermitian.add_assoc]

/-- A sum over `m n` indices as a double sum over the blocks. -/
theorem esum_mul_range (F : Nat → Ext p ν) (n : Nat) : ∀ m, esum F (m * n) = esum (fun a => esum (fun b => F (a * n + b)) n) m
  | 0 => by rw [Nat.zero_mul]; rfl
  | m + 1 => by
    rw [Nat.succ_mul, esum_add_range, esum_mul_range F n m]; rfl

namespace MatE

variable {m n : Nat}

/-! ## The Kronecker product -/

/-- `(A ⊗ B)_{ij} = A_{(i/n)(j/n)} B_{(i%n)(j%n)}` on `m n` indices. -/
def kron (A : MatE p ν m) (B : MatE p ν n) : MatE p ν (m * n) :=
  ⟨fun i j => A.f (i / n) (j / n) * B.f (i % n) (j % n)⟩

theorem kron_f (A : MatE p ν m) (B : MatE p ν n) (i j : Nat) :
    (kron A B).f i j = A.f (i / n) (j / n) * B.f (i % n) (j % n) := rfl

theorem kron_f_pair (A : MatE p ν m) (B : MatE p ν n) {a b c d : Nat} (hb : b < n) (hd : d < n) :
    (kron A B).f (a * n + b) (c * n + d) = A.f a c * B.f b d := by
  rw [kron_f, FRC.Nat.pair_div hb, FRC.Nat.pair_div hd, FRC.Nat.pair_mod hb, FRC.Nat.pair_mod hd]

theorem kron_congr (hn : 0 < n) {A A' : MatE p ν m} {B B' : MatE p ν n} (hA : A ≈ A') (hB : B ≈ B') :
    kron A B ≈ kron A' B' := fun i hi j hj => by
  rw [kron_f, kron_f, hA _ (FRC.Nat.div_lt_of_lt_mul' hn hi) _ (FRC.Nat.div_lt_of_lt_mul' hn hj),
    hB _ (FRC.Nat.mod_lt' i hn) _ (FRC.Nat.mod_lt' j hn)]

theorem kron_add_left (A A' : MatE p ν m) (B : MatE p ν n) : kron (A + A') B ≈ kron A B + kron A' B :=
  fun _ _ _ _ => Hermitian.add_mul _ _ _

theorem kron_add_right (A : MatE p ν m) (B B' : MatE p ν n) : kron A (B + B') ≈ kron A B + kron A B' :=
  fun _ _ _ _ => Hermitian.mul_add _ _ _

theorem kron_neg_left (A : MatE p ν m) (B : MatE p ν n) : kron (-A) B ≈ -(kron A B) :=
  fun _ _ _ _ => (Hermitian.neg_mul _ _).symm

theorem kron_neg_right (A : MatE p ν m) (B : MatE p ν n) : kron A (-B) ≈ -(kron A B) :=
  fun _ _ _ _ => (Hermitian.mul_neg _ _).symm

/-- The Kronecker product is multiplicative: `(A ⊗ B)(C ⊗ D) ≈ (AC) ⊗ (BD)`. -/
theorem kron_mul (A C : MatE p ν m) (B D : MatE p ν n) : kron A B * kron C D ≈ kron (A * C) (B * D) := by
  intro i _ j _
  rw [mul_f, kron_f, mul_f, mul_f, esum_mul_range _ n m, esum_mul_right]
  refine esum_congr m fun a _ => ?_
  rw [esum_mul_left]
  refine esum_congr n fun b hb => ?_
  rw [kron_f, kron_f, FRC.Nat.pair_div hb, FRC.Nat.pair_mod hb]
  -- `(A_{ia} B_{ib}) (C_{aj} D_{bj}) = (A_{ia} C_{aj}) (B_{ib} D_{bj})`
  exact mul_mul_mul_comm' _ _ _ _

/-- Powers of a Kronecker product with the identity: `(A ⊗ 1)^k ≈ A^k ⊗ 1` and `(1 ⊗ B)^k ≈ 1 ⊗ B^k`. -/
theorem kron_opow_left (hn : 0 < n) (A : MatE p ν m) : ∀ k, opow (kron A (1 : MatE p ν n)) k ≈ kron (opow A k) 1
  | 0 => fun i hi j hj => by
    show (if i = j then (1 : Ext p ν) else 0) = (if i / n = j / n then (1 : Ext p ν) else 0) * (if i % n = j % n then 1 else 0)
    exact match Nat.decEq i j with
      | .isTrue h => by subst h; rw [ite_eq_left rfl, ite_eq_left rfl, ite_eq_left rfl, Ext.one_mul]
      | .isFalse h =>
        match Nat.decEq (i / n) (j / n) with
        | .isTrue h1 =>
          match Nat.decEq (i % n) (j % n) with
          | .isTrue h2 => absurd (by rw [FRC.Nat.div_add_mod' hn i, FRC.Nat.div_add_mod' hn j, h1, h2]) h
          | .isFalse h2 => by rw [ite_eq_right h, ite_eq_right h2, Hermitian.mul_zero]
        | .isFalse h1 => by rw [ite_eq_right h, ite_eq_right h1, Hermitian.zero_mul]
  | k + 1 =>
    calc opow (kron A 1) k * kron A 1 ≈ kron (opow A k) 1 * kron A 1 := mul_congr_left _ (kron_opow_left hn A k)
      _ ≈ kron (opow A k * A) (1 * 1) := kron_mul _ _ _ _
      _ ≈ kron (opow A (k + 1)) 1 := kron_congr hn (eq_refl _) (OpRing.one_mul 1)

theorem kron_opow_right (hn : 0 < n) (B : MatE p ν n) : ∀ k, opow (kron (1 : MatE p ν m) B) k ≈ kron 1 (opow B k)
  | 0 => kron_opow_left hn (1 : MatE p ν m) 0
  | k + 1 =>
    calc opow (kron 1 B) k * kron 1 B ≈ kron 1 (opow B k) * kron 1 B := mul_congr_left _ (kron_opow_right hn B k)
      _ ≈ kron (1 * 1) (opow B k * B) := kron_mul _ _ _ _
      _ ≈ kron 1 (opow B (k + 1)) := kron_congr hn (OpRing.one_mul 1) (eq_refl _)

/-- `A ⊗ 1` and `1 ⊗ B` commute, both products being `A ⊗ B`. -/
theorem kron_comm (hn : 0 < n) (A : MatE p ν m) (B : MatE p ν n) : Comm (kron A (1 : MatE p ν n)) (kron (1 : MatE p ν m) B) :=
  calc kron A 1 * kron 1 B ≈ kron (A * 1) (1 * B) := kron_mul _ _ _ _
    _ ≈ kron A B := kron_congr hn (OpRing.mul_one A) (OpRing.one_mul B)
    _ ≈ kron (1 * A) (B * 1) := kron_congr hn (eq_symm (OpRing.one_mul A)) (eq_symm (OpRing.mul_one B))
    _ ≈ kron 1 B * kron A 1 := eq_symm (kron_mul _ _ _ _)

/-- A Kronecker product of two matrices with a nonzero entry each is not zero, `K` having no zero divisors when `ν`
is a nonsquare. -/
theorem kron_ne_zero {κ : Nat} {g : Shell p} (F : Frame p κ g) (hns : ¬ ∃ r : Shell p, r * r = ν)
    {A : MatE p ν m} {B : MatE p ν n} {a c b d : Nat} (ha : a < m) (hc : c < m) (hb : b < n) (hd : d < n)
    (hA : A.f a c ≠ 0) (hB : B.f b d ≠ 0) : ¬ (kron A B ≈ 0) := fun h => by
  have e := h (a * n + b) (FRC.Nat.pair_lt ha hb) (c * n + d) (FRC.Nat.pair_lt hc hd)
  rw [kron_f_pair _ _ hb hd, zero_f] at e
  exact (ext_mul_eq_zero F hns e).elim hA hB

/-! ## The lattice `C_p × C_p`: two commuting translations -/

/-- The translations of the two directions, `T₀ = S ⊗ 1` and `T₁ = 1 ⊗ S`, on `p · p` sites. -/
def shift0 : MatE p ν (p * p) := kron (shift p) (1 : MatE p ν p)
def shift1 : MatE p ν (p * p) := kron (1 : MatE p ν p) (shift p)

theorem shift0_comm_shift1 : Comm (shift0 : MatE p ν (p * p)) shift1 := kron_comm Pos.pos _ _

theorem shift0_pow_self : opow (shift0 : MatE p ν (p * p)) p ≈ 1 :=
  eq_trans (kron_opow_left Pos.pos _ p) (eq_trans (kron_congr Pos.pos shift_pow_self (eq_refl _)) (eq_symm (kron_opow_left Pos.pos 1 0)))

theorem shift1_pow_self : opow (shift1 : MatE p ν (p * p)) p ≈ 1 :=
  eq_trans (kron_opow_right Pos.pos _ p) (eq_trans (kron_congr Pos.pos (eq_refl _) shift_pow_self) (eq_symm (kron_opow_left Pos.pos 1 0)))

theorem inverse_of_opow_self {R : Type} [Add R] [Mul R] [Neg R] [OfNat R 0] [OfNat R 1] [OpRing R] {t : R}
    (ht : opow t p ≈ 1) : Inverse t (opow t (p - 1)) :=
  have hp1 : p - 1 + 1 = p := FRC.Nat.sub_add_cancel (Pos.pos : 0 < p)
  ⟨eq_trans (eq_symm (opow_succ' t (p - 1))) (eq_trans (eq_of_eq (congrArg (opow t) hp1)) ht),
   eq_trans (eq_of_eq ((opow_succ t (p - 1)).symm.trans (congrArg (opow t) hp1))) ht⟩

theorem shift0_inverse : Inverse (shift0 : MatE p ν (p * p)) (opow shift0 (p - 1)) := inverse_of_opow_self shift0_pow_self
theorem shift1_inverse : Inverse (shift1 : MatE p ν (p * p)) (opow shift1 (p - 1)) := inverse_of_opow_self shift1_pow_self

/-- `0 ⊗ B ≈ 0`, and a sum of Kronecker products with the identity is the Kronecker product of the sum. -/
theorem kron_zero_left (B : MatE p ν n) : kron (0 : MatE p ν m) B ≈ 0 := fun _ _ _ _ => Hermitian.zero_mul _
theorem kron_zero_right (A : MatE p ν m) : kron A (0 : MatE p ν n) ≈ 0 := fun _ _ _ _ => Hermitian.mul_zero _

theorem osum_kron_left (f : Nat → MatE p ν m) : ∀ k, osum (fun j => kron (f j) (1 : MatE p ν n)) k ≈ kron (osum f k) 1
  | 0 => eq_symm (kron_zero_left 1)
  | k + 1 =>
    calc osum (fun j => kron (f j) 1) k + kron (f k) 1 ≈ kron (osum f k) 1 + kron (f k) 1 :=
          add_congr_left _ (osum_kron_left f k)
      _ ≈ kron (osum f k + f k) 1 := eq_symm (kron_add_left _ _ _)

theorem osum_kron_right (f : Nat → MatE p ν n) : ∀ k, osum (fun j => kron (1 : MatE p ν m) (f j)) k ≈ kron 1 (osum f k)
  | 0 => eq_symm (kron_zero_right 1)
  | k + 1 =>
    calc osum (fun j => kron 1 (f j)) k + kron 1 (f k) ≈ kron 1 (osum f k) + kron 1 (f k) :=
          add_congr_left _ (osum_kron_right f k)
      _ ≈ kron 1 (osum f k + f k) := eq_symm (kron_add_right _ _ _)

/-- `Σ_k (A ⊗ 1)^k ≈ (Σ_k A^k) ⊗ 1` and `Σ_k (1 ⊗ B)^k ≈ 1 ⊗ Σ_k B^k`. -/
theorem geom_kron_left (hn : 0 < n) (A : MatE p ν m) (k : Nat) : geom (kron A (1 : MatE p ν n)) k ≈ kron (geom A k) 1 :=
  eq_trans (osum_congr k fun j _ => kron_opow_left hn A j) (osum_kron_left _ k)

theorem geom_kron_right (hn : 0 < n) (B : MatE p ν n) (k : Nat) : geom (kron (1 : MatE p ν m) B) k ≈ kron 1 (geom B k) :=
  eq_trans (osum_congr k fun j _ => kron_opow_right hn B j) (osum_kron_right _ k)

/-- 8:D20 — the product of the two direction sums is not zero: `(Σ_k T₀^k)(Σ_k T₁^k) ≈ (Σ_k S^k) ⊗ (Σ_k S^k)`, whose
`(0, 0)` entry is `1 · 1`. -/
theorem geom_shift0_mul_geom_shift1_ne_zero {κ : Nat} {g : Shell p} (F : Frame p κ g) (hns : ¬ ∃ r : Shell p, r * r = ν) :
    ¬ (geom (shift0 : MatE p ν (p * p)) p * geom shift1 p ≈ 0) := by
  have hprod : geom (shift0 : MatE p ν (p * p)) p * geom shift1 p ≈ kron (geom (shift p) p) (geom (shift p) p) :=
    calc geom (shift0 : MatE p ν (p * p)) p * geom shift1 p ≈ kron (geom (shift p) p) 1 * kron 1 (geom (shift p) p) :=
          OpRing.mul_congr (geom_kron_left Pos.pos _ p) (geom_kron_right Pos.pos _ p)
      _ ≈ kron (geom (shift p) p * 1) (1 * geom (shift p) p) := kron_mul _ _ _ _
      _ ≈ kron (geom (shift p) p) (geom (shift p) p) := kron_congr Pos.pos (OpRing.mul_one _) (OpRing.one_mul _)
  have hne : (1 : Ext p ν) ≠ 0 := fun h => F.one_ne_zero (congrArg Ext.re h)
  intro h
  exact kron_ne_zero F hns Pos.pos Pos.pos Pos.pos Pos.pos (by rw [geom_shift_f00]; exact hne)
    (by rw [geom_shift_f00]; exact hne) (eq_trans (eq_symm hprod) h)


/-! ## The two symmetric differences of the lattice and the exact index of their square -/

/-- The symmetric difference `h (t − t⁻¹)` of a translation of order `p` is nilpotent, `(h (t − t^{p−1}))^p ≈ 0`, for
central `h`, in every operator ring of characteristic `p` on a frame (the generic form of `symdiff_nilpotent`). -/
theorem symdiff_nilpotent' {R : Type} [Add R] [Mul R] [Neg R] [OfNat R 0] [OfNat R 1] [OpRing R]
    {κ : Nat} {g : Shell p} (F : Frame p κ g) (hch : nsmul p (1 : R) ≈ 0) {t h : R} (hh : Central h) (ht : opow t p ≈ 1) :
    opow (h * (t + -(opow t (p - 1)))) p ≈ 0 := by
  have hT : Comm t (-(opow t (p - 1))) := Comm.neg_right (opow_self_comm t (p - 1)).symm
  have hinv : opow (opow t (p - 1)) p ≈ 1 :=
    calc opow (opow t (p - 1)) p ≈ opow t ((p - 1) * p) := eq_symm (opow_mul _ _ _)
      _ ≈ opow t (p * (p - 1)) := eq_of_eq (by rw [Nat.mul_comm])
      _ ≈ opow (opow t p) (p - 1) := opow_mul _ _ _
      _ ≈ opow 1 (p - 1) := opow_congr ht _
      _ ≈ 1 := opow_one_left _
  have hodd : opow (-1 : R) p ≈ -1 := by
    have e : p = 2 * (2 * κ) + 1 := by rw [F.cap, ← Nat.mul_assoc]
    exact OpRing.trans (eq_of_eq (congrArg (opow (-1 : R)) e)) (opow_neg_one_odd _)
  have hneg : opow (-(opow t (p - 1))) p ≈ -1 :=
    calc opow (-(opow t (p - 1))) p ≈ opow (-1 * opow t (p - 1)) p := opow_congr (eq_symm (neg_one_mul _)) p
      _ ≈ opow (-1) p * opow (opow t (p - 1)) p := mul_opow (Central.neg Central.one _) p
      _ ≈ -1 * 1 := OpRing.mul_congr hodd hinv
      _ ≈ -1 := OpRing.mul_one _
  calc opow (h * (t + -(opow t (p - 1)))) p ≈ opow h p * opow (t + -(opow t (p - 1))) p := mul_opow (hh _) p
    _ ≈ opow h p * (opow t p + opow (-(opow t (p - 1))) p) := mul_congr_right _ (frobenius_add F hch hT)
    _ ≈ opow h p * (1 + -1) := mul_congr_right _ (OpRing.add_congr ht hneg)
    _ ≈ opow h p * 0 := mul_congr_right _ (OpRing.add_neg 1)
    _ ≈ 0 := Operator.mul_zero _

/-- The symmetric differences of the two directions, `∇_μ = h (T_μ − T_μ^{p−1})` with `h` central (`h = 2⁻¹`). -/
def sdiff0 (h : MatE p ν (p * p)) : MatE p ν (p * p) := h * (shift0 + -(opow shift0 (p - 1)))
def sdiff1 (h : MatE p ν (p * p)) : MatE p ν (p * p) := h * (shift1 + -(opow shift1 (p - 1)))

theorem sdiff_comm {h : MatE p ν (p * p)} (hh : Central h) : Comm (sdiff0 h) (sdiff1 h) := by
  have c01 : Comm (shift0 : MatE p ν (p * p)) shift1 := shift0_comm_shift1
  have c0p : Comm (shift0 : MatE p ν (p * p)) (opow shift1 (p - 1)) := (opow_comm c01.symm (p - 1)).symm
  have cp1 : Comm (opow (shift0 : MatE p ν (p * p)) (p - 1)) shift1 := opow_comm c01 (p - 1)
  have cpp : Comm (opow (shift0 : MatE p ν (p * p)) (p - 1)) (opow shift1 (p - 1)) := (opow_comm cp1.symm (p - 1)).symm
  have hA : Comm (shift0 : MatE p ν (p * p)) (shift1 + -(opow shift1 (p - 1))) := Comm.add_right c01 (Comm.neg_right c0p)
  have hB : Comm (opow (shift0 : MatE p ν (p * p)) (p - 1)) (shift1 + -(opow shift1 (p - 1))) :=
    Comm.add_right cp1 (Comm.neg_right cpp)
  have hT : Comm (shift0 + -(opow shift0 (p - 1)) : MatE p ν (p * p)) (shift1 + -(opow shift1 (p - 1))) :=
    Comm.add_left hA (Comm.neg_left hB)
  have hhT : Comm h (shift1 + -(opow shift1 (p - 1)) : MatE p ν (p * p)) := hh _
  have hhT0 : Comm (shift0 + -(opow shift0 (p - 1)) : MatE p ν (p * p)) h := Comm.symm (hh _)
  show Comm (h * (shift0 + -(opow shift0 (p - 1)))) (h * (shift1 + -(opow shift1 (p - 1))))
  exact Comm.mul_left (Comm.mul_right (hh _) hhT) (Comm.mul_right hhT0 hT)

theorem sdiff0_nilpotent {κ : Nat} {g : Shell p} (F : Frame p κ g) {h : MatE p ν (p * p)} (hh : Central h) :
    opow (sdiff0 h) p ≈ 0 := symdiff_nilpotent' F char_p hh shift0_pow_self
theorem sdiff1_nilpotent {κ : Nat} {g : Shell p} (F : Frame p κ g) {h : MatE p ν (p * p)} (hh : Central h) :
    opow (sdiff1 h) p ≈ 0 := symdiff_nilpotent' F char_p hh shift1_pow_self

/-- `∇_μ^{p−1} ≈ h^{p−1} Σ_k T_μ^k` on the lattice. -/
theorem sdiff0_pow_pred {κ : Nat} {g : Shell p} (F : Frame p κ g) {h : MatE p ν (p * p)} (hh : Central h) :
    opow (sdiff0 h) (p - 1) ≈ opow h (p - 1) * geom shift0 p :=
  eq_trans (mul_opow (hh _) _) (mul_congr_right _ (symdiff_pred_eq_geom F char_p shift0_pow_self shift0_inverse))
theorem sdiff1_pow_pred {κ : Nat} {g : Shell p} (F : Frame p κ g) {h : MatE p ν (p * p)} (hh : Central h) :
    opow (sdiff1 h) (p - 1) ≈ opow h (p - 1) * geom shift1 p :=
  eq_trans (mul_opow (hh _) _) (mul_congr_right _ (symdiff_pred_eq_geom F char_p shift1_pow_self shift1_inverse))

/-- 8:D20 — `∇₀^{p−1} ∇₁^{p−1} ≉ 0` on the lattice `C_p × C_p`, for a central unit `h`: the product is
`h^{2(p−1)} (Σ T₀^k)(Σ T₁^k)`, and the direction sums' product is not zero. -/
theorem sdiff_prod_ne_zero {κ : Nat} {g : Shell p} (F : Frame p κ g) (hns : ¬ ∃ r : Shell p, r * r = ν)
    {h h' : MatE p ν (p * p)} (hh : Central h) (hinv : Inverse h h') :
    ¬ (opow (sdiff0 h) (p - 1) * opow (sdiff1 h) (p - 1) ≈ 0) := by
  intro hz
  have hc : Central (opow h (p - 1)) := Central.opow hh _
  have hprod : opow (sdiff0 h) (p - 1) * opow (sdiff1 h) (p - 1) ≈
      opow h (p - 1) * opow h (p - 1) * (geom shift0 p * geom shift1 p) :=
    calc opow (sdiff0 h) (p - 1) * opow (sdiff1 h) (p - 1)
        ≈ opow h (p - 1) * geom shift0 p * (opow h (p - 1) * geom shift1 p) :=
          OpRing.mul_congr (sdiff0_pow_pred F hh) (sdiff1_pow_pred F hh)
      _ ≈ opow h (p - 1) * (geom shift0 p * opow h (p - 1)) * geom shift1 p :=
          eq_trans (eq_symm (OpRing.mul_assoc _ _ _)) (mul_congr_left _ (OpRing.mul_assoc _ _ _))
      _ ≈ opow h (p - 1) * (opow h (p - 1) * geom shift0 p) * geom shift1 p :=
          mul_congr_left _ (mul_congr_right _ (eq_symm (hc _)))
      _ ≈ opow h (p - 1) * opow h (p - 1) * (geom shift0 p * geom shift1 p) :=
          eq_trans (mul_congr_left _ (eq_symm (OpRing.mul_assoc _ _ _))) (OpRing.mul_assoc _ _ _)
  have hu : Inverse (opow h (p - 1) * opow h (p - 1)) (opow h' (p - 1) * opow h' (p - 1)) :=
    Inverse.mul (inverse_opow hinv _) (inverse_opow hinv _)
  apply geom_shift0_mul_geom_shift1_ne_zero F hns
  exact unit_kernel hu.2 (eq_trans (eq_symm hprod) hz)

/-- 8:D20 — the exact index of the square on two coordinate directions, on the lattice `C_p × C_p`: with central units
`h`, `η₀`, `η₁`, the operator `□ = η₀ ∇₀² + η₁ ∇₁²` has `□^{p−1} ≉ 0` while `□^{p−1} ∇₀ ≈ 0`, `□^{p−1} ∇₁ ≈ 0` and
`□^p ≈ 0`; for the Dirac operator `𝒟 = ∇₀ γ₀ + ∇₁ γ₁` with `𝒟² = □` this is the index `2p − 1` (`dirac_two_index`). -/
theorem box_two_lattice_index {κ : Nat} {g : Shell p} (F : Frame p κ g) (hns : ¬ ∃ r : Shell p, r * r = ν)
    {h h' η0 η0' η1 η1' : MatE p ν (p * p)} (hh : Central h) (hinv : Inverse h h')
    (hη0 : Central η0) (hη0' : Inverse η0 η0') (hη1 : Central η1) (hη1' : Inverse η1 η1') :
    ¬ (opow (η0 * (sdiff0 h * sdiff0 h) + η1 * (sdiff1 h * sdiff1 h)) (p - 1) ≈ 0) ∧
      opow (η0 * (sdiff0 h * sdiff0 h) + η1 * (sdiff1 h * sdiff1 h)) (p - 1) * sdiff0 h ≈ 0 ∧
      opow (η0 * (sdiff0 h * sdiff0 h) + η1 * (sdiff1 h * sdiff1 h)) (p - 1) * sdiff1 h ≈ 0 ∧
      opow (η0 * (sdiff0 h * sdiff0 h) + η1 * (sdiff1 h * sdiff1 h)) p ≈ 0 := by
  have h01 := sdiff_comm hh
  have hn0 := sdiff0_nilpotent F hh
  have hn1 := sdiff1_nilpotent F hh
  obtain ⟨hk0, hk1⟩ := box_two_pow_pred_mul F char_p h01 hη0 hη1 hn0 hn1
  refine ⟨fun hz => ?_, hk0, hk1, ?_⟩
  · -- `□^{p−1} ≈ η₀^{2κ} η₁^{2κ} ∇₀^{p−1} ∇₁^{p−1}`, and the scalar is a unit
    have hb := box_two_pow_pred F char_p h01 hη0 hη1 hn0 hn1
    have hu : Inverse (opow η0 (2 * κ) * opow η1 (2 * κ)) (opow η1' (2 * κ) * opow η0' (2 * κ)) :=
      Inverse.mul (inverse_opow hη0' _) (inverse_opow hη1' _)
    exact sdiff_prod_ne_zero F hns hh hinv (unit_kernel hu.2 (eq_trans (eq_symm hb) hz))
  · -- `□^p ≈ (η₀ ∇₀²)^p + (η₁ ∇₁²)^p ≈ 0`
    have hab : Comm (η0 * (sdiff0 h * sdiff0 h)) (η1 * (sdiff1 h * sdiff1 h)) :=
      Comm.mul_left (hη0 _) (Comm.mul_left (Comm.mul_right (Comm.symm (hη1 _)) (Comm.mul_right h01 h01))
        (Comm.mul_right (Comm.symm (hη1 _)) (Comm.mul_right h01 h01)))
    have hterm : ∀ (η d : MatE p ν (p * p)), Central η → opow d p ≈ 0 → opow (η * (d * d)) p ≈ 0 := fun η d hη hd =>
      calc opow (η * (d * d)) p ≈ opow η p * opow d (p + p) := opow_central_sq hη p
        _ ≈ opow η p * 0 := mul_congr_right _ (opow_eq_zero_of hd p)
        _ ≈ 0 := Operator.mul_zero _
    calc opow (η0 * (sdiff0 h * sdiff0 h) + η1 * (sdiff1 h * sdiff1 h)) p
        ≈ opow (η0 * (sdiff0 h * sdiff0 h)) p + opow (η1 * (sdiff1 h * sdiff1 h)) p := frobenius_add F char_p hab
      _ ≈ 0 + 0 := OpRing.add_congr (hterm _ _ hη0 hn0) (hterm _ _ hη1 hn1)
      _ ≈ 0 := OpRing.zero_add 0

end MatE

end FRC.Dirac.Spinor
