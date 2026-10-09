import FrcCore.Theme.Rotations
import FrcCore.Theme.Dichotomy

/-!
# FrcCore.Theme.Heisenberg — the character sector and the cardinal Heisenberg covariance (the fourier theme)

The sixth file of the fourier theme (6-fourier's blueprint of 8 October 2026, task T07). On the range of `Π₁` the
family acts by the meridian character, `F^{[s]} Π₁ = z^s Π₁` (`frft_proj`), so `F^{[s]} T_v = T_v S_{−s}` for
`T_v(x) = x v`, and the rotation `R_s` carries the same character on its eigenline `(1, −i)` (6:E6). The shift
`(σ v)_k = v_{k−1}` and the modulation `D₁ = diag(g^k)` are intertwined by the cardinal skeleton: `F σ = D₁ F`,
`F D₁ = σ⁻¹ F`, `J σ = σ⁻¹ J`, `F J σ = D₁⁻¹ F J`, the quarter-rotation `σ ↦ D₁ ↦ σ⁻¹ ↦ D₁⁻¹` (6:E7); and
`F^{[s]} = Σ_r c_r(s) F^r` with `c_r(s) = ¼ Σ_ℓ (g^{rκ−s})^ℓ` is `frft_eq` of `Theme/Fourier.lean` with its
coefficients written as geometric sums. No axioms.
-/

namespace FRC
namespace Shell
namespace Frame

variable {p : Nat} [Pos p]

/-! ## Ring identities (generated; `RE.sound`, decided by the kernel) -/

theorem shift_id (i A B : Shell p) :
    i * (A * B) = B * (i * A) :=
  RE.sound (look [i, A, B])
    (.mul (.var 0) (.mul (.var 1) (.var 2)))
    (.mul (.var 2) (.mul (.var 0) (.var 1))) (by decide +kernel)

theorem modul_id (i A B : Shell p) :
    (i * A) * B = 1 * (i * (A * B)) :=
  RE.sound (look [i, A, B])
    (.mul (.mul (.var 0) (.var 1)) (.var 2))
    (.mul .one (.mul (.var 0) (.mul (.var 1) (.var 2)))) (by decide +kernel)

theorem assoc4_id (Z A B C : Shell p) :
    (Z * A) * (B * C) = (Z * C) * (A * B) :=
  RE.sound (look [Z, A, B, C])
    (.mul (.mul (.var 0) (.var 1)) (.mul (.var 2) (.var 3)))
    (.mul (.mul (.var 0) (.var 3)) (.mul (.var 1) (.var 2))) (by decide +kernel)

theorem coeff1_id (q i u : Shell p) :
    q * (1 + -i * u + -(u * u) + -(-i * ((u * u) * u))) = q * (1 + u * -i + (u * -i) * (u * -i) + ((u * -i) * (u * -i)) * (u * -i)) + (i * i + 1) * (q * i * u * u * u + -(q * u * u)) :=
  RE.sound (look [q, i, u])
    (.mul (.var 0) (.add (.add (.add .one (.mul (.neg (.var 1)) (.var 2))) (.neg (.mul (.var 2) (.var 2)))) (.neg (.mul (.neg (.var 1)) (.mul (.mul (.var 2) (.var 2)) (.var 2))))))
    (.add (.mul (.var 0) (.add (.add (.add .one (.mul (.var 2) (.neg (.var 1)))) (.mul (.mul (.var 2) (.neg (.var 1))) (.mul (.var 2) (.neg (.var 1))))) (.mul (.mul (.mul (.var 2) (.neg (.var 1))) (.mul (.var 2) (.neg (.var 1)))) (.mul (.var 2) (.neg (.var 1)))))) (.mul (.add (.mul (.var 1) (.var 1)) .one) (.add (.mul (.mul (.mul (.mul (.var 0) (.var 1)) (.var 2)) (.var 2)) (.var 2)) (.neg (.mul (.mul (.var 0) (.var 2)) (.var 2)))))) (by decide +kernel)

theorem coeff2_id (q i u : Shell p) :
    q * (1 + -u + u * u + -((u * u) * u)) = q * (1 + u * (-i * -i) + (u * (-i * -i)) * (u * (-i * -i)) + ((u * (-i * -i)) * (u * (-i * -i))) * (u * (-i * -i))) + (i * i + 1) * (-(q * i * i * i * i * u * u * u) + q * i * i * u * u * u + -(q * i * i * u * u) + -(q * u * u * u) + q * u * u + -(q * u)) :=
  RE.sound (look [q, i, u])
    (.mul (.var 0) (.add (.add (.add .one (.neg (.var 2))) (.mul (.var 2) (.var 2))) (.neg (.mul (.mul (.var 2) (.var 2)) (.var 2)))))
    (.add (.mul (.var 0) (.add (.add (.add .one (.mul (.var 2) (.mul (.neg (.var 1)) (.neg (.var 1))))) (.mul (.mul (.var 2) (.mul (.neg (.var 1)) (.neg (.var 1)))) (.mul (.var 2) (.mul (.neg (.var 1)) (.neg (.var 1)))))) (.mul (.mul (.mul (.var 2) (.mul (.neg (.var 1)) (.neg (.var 1)))) (.mul (.var 2) (.mul (.neg (.var 1)) (.neg (.var 1))))) (.mul (.var 2) (.mul (.neg (.var 1)) (.neg (.var 1))))))) (.mul (.add (.mul (.var 1) (.var 1)) .one) (.add (.add (.add (.add (.add (.neg (.mul (.mul (.mul (.mul (.mul (.mul (.mul (.var 0) (.var 1)) (.var 1)) (.var 1)) (.var 1)) (.var 2)) (.var 2)) (.var 2))) (.mul (.mul (.mul (.mul (.mul (.var 0) (.var 1)) (.var 1)) (.var 2)) (.var 2)) (.var 2))) (.neg (.mul (.mul (.mul (.mul (.var 0) (.var 1)) (.var 1)) (.var 2)) (.var 2)))) (.neg (.mul (.mul (.mul (.var 0) (.var 2)) (.var 2)) (.var 2)))) (.mul (.mul (.var 0) (.var 2)) (.var 2))) (.neg (.mul (.var 0) (.var 2)))))) (by decide +kernel)

theorem coeff3_id (q i u : Shell p) :
    q * (1 + -(-i * u) + -(u * u) + -i * ((u * u) * u)) = q * (1 + u * ((-i * -i) * -i) + (u * ((-i * -i) * -i)) * (u * ((-i * -i) * -i)) + ((u * ((-i * -i) * -i)) * (u * ((-i * -i) * -i))) * (u * ((-i * -i) * -i))) + (i * i + 1) * (q * i * i * i * i * i * i * i * u * u * u + -(q * i * i * i * i * i * u * u * u) + -(q * i * i * i * i * u * u) + q * i * i * i * u * u * u + q * i * i * u * u + -(q * i * u * u * u) + q * i * u + -(q * u * u)) :=
  RE.sound (look [q, i, u])
    (.mul (.var 0) (.add (.add (.add .one (.neg (.mul (.neg (.var 1)) (.var 2)))) (.neg (.mul (.var 2) (.var 2)))) (.mul (.neg (.var 1)) (.mul (.mul (.var 2) (.var 2)) (.var 2)))))
    (.add (.mul (.var 0) (.add (.add (.add .one (.mul (.var 2) (.mul (.mul (.neg (.var 1)) (.neg (.var 1))) (.neg (.var 1))))) (.mul (.mul (.var 2) (.mul (.mul (.neg (.var 1)) (.neg (.var 1))) (.neg (.var 1)))) (.mul (.var 2) (.mul (.mul (.neg (.var 1)) (.neg (.var 1))) (.neg (.var 1)))))) (.mul (.mul (.mul (.var 2) (.mul (.mul (.neg (.var 1)) (.neg (.var 1))) (.neg (.var 1)))) (.mul (.var 2) (.mul (.mul (.neg (.var 1)) (.neg (.var 1))) (.neg (.var 1))))) (.mul (.var 2) (.mul (.mul (.neg (.var 1)) (.neg (.var 1))) (.neg (.var 1))))))) (.mul (.add (.mul (.var 1) (.var 1)) .one) (.add (.add (.add (.add (.add (.add (.add (.mul (.mul (.mul (.mul (.mul (.mul (.mul (.mul (.mul (.mul (.var 0) (.var 1)) (.var 1)) (.var 1)) (.var 1)) (.var 1)) (.var 1)) (.var 1)) (.var 2)) (.var 2)) (.var 2)) (.neg (.mul (.mul (.mul (.mul (.mul (.mul (.mul (.mul (.var 0) (.var 1)) (.var 1)) (.var 1)) (.var 1)) (.var 1)) (.var 2)) (.var 2)) (.var 2)))) (.neg (.mul (.mul (.mul (.mul (.mul (.mul (.var 0) (.var 1)) (.var 1)) (.var 1)) (.var 1)) (.var 2)) (.var 2)))) (.mul (.mul (.mul (.mul (.mul (.mul (.var 0) (.var 1)) (.var 1)) (.var 1)) (.var 2)) (.var 2)) (.var 2))) (.mul (.mul (.mul (.mul (.var 0) (.var 1)) (.var 1)) (.var 2)) (.var 2))) (.neg (.mul (.mul (.mul (.mul (.var 0) (.var 1)) (.var 2)) (.var 2)) (.var 2)))) (.mul (.mul (.var 0) (.var 1)) (.var 2))) (.neg (.mul (.mul (.var 0) (.var 2)) (.var 2)))))) (by decide +kernel)

theorem eigenline_a_id (i c d : Shell p) :
    c * 1 + -(d * -i) = (c + i * d) * 1 :=
  RE.sound (look [i, c, d])
    (.add (.mul (.var 1) .one) (.neg (.mul (.var 2) (.neg (.var 0)))))
    (.mul (.add (.var 1) (.mul (.var 0) (.var 2))) .one) (by decide +kernel)

theorem eigenline_b_id (i c d : Shell p) :
    d * 1 + c * -i = (c + i * d) * -i + (i * i + 1) * (d) :=
  RE.sound (look [i, c, d])
    (.add (.mul (.var 2) .one) (.mul (.var 1) (.neg (.var 0))))
    (.add (.mul (.add (.var 1) (.mul (.var 0) (.var 2))) (.neg (.var 0))) (.mul (.add (.mul (.var 0) (.var 0)) .one) (.var 2))) (by decide +kernel)

variable {κ : Nat} {g : Shell p}

/-! ## The common character sector (6:E6) -/

/-- 6:E6, the intertwiner: `F^{[s]} T_v = T_v S_{−s}` with `v` a column of `Π₁` and `T_v(x) = x v`, `S_{−s} x = z^s x`. -/
theorem frft_intertwine (F : Frame p κ g) (z : Shell p) (s : Nat) (x : Shell p) {k j : Nat} (hk : k < p - 1)
    (hj : j < p - 1) :
    sumRange (fun l => frft g κ z s k l * (x * proj g κ 1 l j)) (p - 1) = x * (z ^ s * proj g κ 1 k j) := by
  rw [sum_congr _ (fun l _ => mul_left_comm (frft g κ z s k l) x (proj g κ 1 l j)), sum_mul_left,
    frft_proj F z s (by decide : (1 : Nat) < 4) hk hj, pow_one]

/-- 6:E6, the eigenline: `R_s (1, −i)ᵀ = z_s (1, −i)ᵀ`. -/
theorem rot_eigenline (F : Frame p κ g) (z : Shell p) (s : Nat) :
    cs g κ z s * 1 + -(ds g κ z s * -(quarterTurn g κ)) = z ^ s * 1 ∧
      ds g κ z s * 1 + cs g κ z s * -(quarterTurn g κ) = z ^ s * -(quarterTurn g κ) :=
  ⟨by rw [eigenline_a_id, (rot_eq F z s).1], by rw [red1 (eigenline_b_id _ _ _) (hii F), (rot_eq F z s).1]⟩

/-! ## The shift and the modulation -/

/-- The shift `(σ v)_k = v_{k−1}`: `σ_{kj} = [j + 1 ≡ k]`. -/
def shift (p : Nat) [Pos p] (k j : Nat) : Shell p := if (j + 1) % (p - 1) = k then 1 else 0

/-- Its inverse `(σ⁻¹ v)_k = v_{k+1}`: `σ⁻¹_{kj} = [k + 1 ≡ j]`. -/
def shiftInv (p : Nat) [Pos p] (k j : Nat) : Shell p := if (k + 1) % (p - 1) = j then 1 else 0

/-- The modulation `D₁ = diag(g^k)`; `D₁⁻¹ = diag(z^k)` is `modul z`. -/
def modul (g : Shell p) (k j : Nat) : Shell p := if k = j then g ^ k else 0

theorem shift_single (F : Frame p κ g) (X : Nat → Nat → Shell p) (k j : Nat) :
    sumRange (fun l => X k l * shift p l j) (p - 1) = X k ((j + 1) % (p - 1)) := by
  rw [sum_eq_single (FRC.Nat.mod_lt' _ F.n_pos) (fun l _ hne => by
    show X k l * (if (j + 1) % (p - 1) = l then 1 else 0) = 0
    rw [ite_eq_right (fun e => hne e.symm), mul_zero])]
  show X k ((j + 1) % (p - 1)) * (if (j + 1) % (p - 1) = (j + 1) % (p - 1) then 1 else 0) = _
  rw [ite_eq_left rfl, mul_one]

theorem shiftInv_single (F : Frame p κ g) (X : Nat → Nat → Shell p) (k j : Nat) :
    sumRange (fun l => shiftInv p k l * X l j) (p - 1) = X ((k + 1) % (p - 1)) j := by
  rw [sum_eq_single (FRC.Nat.mod_lt' _ F.n_pos) (fun l _ hne => by
    show (if (k + 1) % (p - 1) = l then 1 else 0) * X l j = 0
    rw [ite_eq_right (fun e => hne e.symm), zero_mul])]
  show (if (k + 1) % (p - 1) = (k + 1) % (p - 1) then 1 else 0) * X ((k + 1) % (p - 1)) j = _
  rw [ite_eq_left rfl, one_mul]

theorem modul_left (a : Shell p) (X : Nat → Nat → Shell p) {k : Nat} (hk : k < p - 1) (j : Nat) :
    sumRange (fun l => modul a k l * X l j) (p - 1) = a ^ k * X k j := by
  rw [sum_eq_single hk (fun l _ hne => by
    show (if k = l then a ^ k else 0) * X l j = 0
    rw [ite_eq_right (fun e => hne e.symm), zero_mul])]
  show (if k = k then a ^ k else 0) * X k j = _
  rw [ite_eq_left rfl]

theorem modul_right (a : Shell p) (X : Nat → Nat → Shell p) (k : Nat) {j : Nat} (hj : j < p - 1) :
    sumRange (fun l => X k l * modul a l j) (p - 1) = X k j * a ^ j := by
  rw [sum_eq_single hj (fun l _ hne => by
    show X k l * (if l = j then a ^ l else 0) = 0
    rw [ite_eq_right hne, mul_zero])]
  show X k j * (if j = j then a ^ j else 0) = _
  rw [ite_eq_left rfl]

theorem add_n_mod (F : Frame p κ g) {x : Nat} (hx : x < p - 1) : (x + (p - 1)) % (p - 1) = x := by
  have e := FRC.Nat.add_mul_mod_self_left x 1 (p - 1) F.n_pos
  rw [Nat.mul_one] at e
  rw [Nat.add_comm, e, FRC.Nat.mod_eq_of_lt hx]

theorem succ_pred_mod (F : Frame p κ g) {k : Nat} (hk : k < p - 1) : ((k + (p - 1 - 1)) % (p - 1) + 1) % (p - 1) = k := by
  rw [FRC.Nat.mod_add_mod _ _ _ F.n_pos, Nat.add_assoc, FRC.Nat.sub_add_cancel F.n_pos, add_n_mod F hk]

theorem pred_succ_mod (F : Frame p κ g) {l : Nat} (hl : l < p - 1) : ((l + 1) % (p - 1) + (p - 1 - 1)) % (p - 1) = l := by
  rw [FRC.Nat.mod_add_mod _ _ _ F.n_pos, Nat.add_assoc, Nat.add_comm 1 (p - 1 - 1), FRC.Nat.sub_add_cancel F.n_pos,
    add_n_mod F hl]

/-- `g^{((j+1) mod n) k} = g^{jk} g^k`. -/
theorem pow_succ_mod (F : Frame p κ g) (j k : Nat) : g ^ ((j + 1) % (p - 1) * k) = g ^ (j * k) * g ^ k := by
  rw [F.pow_mod, FRC.Nat.mod_mul_mod _ _ _ F.n_pos, ← F.pow_mod, Nat.add_mul, Nat.one_mul, pow_add]

/-- 6:E7, `F σ = D₁ F`: the transform turns the shift into the modulation. -/
theorem Fmat_shift (F : Frame p κ g) {k j : Nat} (hk : k < p - 1) (_hj : j < p - 1) :
    sumRange (fun l => Fmat g κ k l * shift p l j) (p - 1) = sumRange (fun l => modul g k l * Fmat g κ l j) (p - 1) := by
  rw [shift_single F, modul_left g (Fmat g κ) hk j]
  show quarterTurn g κ * g ^ ((j + 1) % (p - 1) * k) = g ^ k * (quarterTurn g κ * g ^ (j * k))
  rw [pow_succ_mod F]; exact shift_id _ _ _

/-- `g^{j ((k+1) mod n)} = g^{jk} g^j`. -/
theorem pow_mod_succ (F : Frame p κ g) (j k : Nat) : g ^ (j * ((k + 1) % (p - 1))) = g ^ (j * k) * g ^ j := by
  rw [F.pow_mod, FRC.Nat.mul_mod_mod _ _ _ F.n_pos, ← F.pow_mod, Nat.mul_add, Nat.mul_one, pow_add]

/-- 6:E7, `F D₁ = σ⁻¹ F`: the transform turns the modulation into the inverse shift. -/
theorem Fmat_modul (F : Frame p κ g) {k j : Nat} (_hk : k < p - 1) (hj : j < p - 1) :
    sumRange (fun l => Fmat g κ k l * modul g l j) (p - 1) = sumRange (fun l => shiftInv p k l * Fmat g κ l j) (p - 1) := by
  rw [modul_right g (Fmat g κ) k hj, shiftInv_single F]
  show quarterTurn g κ * g ^ (j * k) * g ^ j = quarterTurn g κ * g ^ (j * ((k + 1) % (p - 1)))
  rw [pow_mod_succ F]; exact (modul_id _ _ _).trans (one_mul _)

theorem ite_iff {c1 c2 : Prop} [Decidable c1] [Decidable c2] (h : c1 ↔ c2) :
    (if c1 then (1 : Shell p) else 0) = if c2 then 1 else 0 :=
  match Decidable.em c1 with
  | Or.inl e => by rw [ite_eq_left e, ite_eq_left (h.1 e)]
  | Or.inr e => by rw [ite_eq_right e, ite_eq_right (fun e2 => e (h.2 e2))]

/-- 6:E7, `J σ = σ⁻¹ J`: the reversal conjugates the shift to its inverse. -/
theorem J_shift (F : Frame p κ g) {k j : Nat} (_hk : k < p - 1) (_hj : j < p - 1) :
    sumRange (fun l => (J (p - 1) k l : Shell p) * shift p l j) (p - 1) =
      sumRange (fun l => shiftInv p k l * J (p - 1) l j) (p - 1) := by
  have hn := F.n_pos
  rw [shift_single F (fun k l => (J (p - 1) k l : Shell p)), shiftInv_single F (fun l j => (J (p - 1) l j : Shell p))]
  show (if (k + (j + 1) % (p - 1)) % (p - 1) = 0 then (1 : Shell p) else 0) =
    if ((k + 1) % (p - 1) + j) % (p - 1) = 0 then 1 else 0
  apply ite_iff
  rw [FRC.Nat.add_mod_mod _ _ _ hn, FRC.Nat.mod_add_mod _ _ _ hn, ← Nat.add_assoc, Nat.add_right_comm k j 1]

/-- 6:E7, `σ σ⁻¹ = I = σ⁻¹ σ` on the cycle: `shiftInv` is the inverse shift. -/
theorem shift_inverse (F : Frame p κ g) {k j : Nat} (hk : k < p - 1) (hj : j < p - 1) :
    sumRange (fun l => shift p k l * shiftInv p l j) (p - 1) = idm k j ∧
      sumRange (fun l => shiftInv p k l * shift p l j) (p - 1) = idm k j := by
  have hn := F.n_pos
  constructor
  · rw [sum_eq_single (l₀ := (k + (p - 1 - 1)) % (p - 1)) (FRC.Nat.mod_lt' _ hn) (fun l hl hne => by
      show (if (l + 1) % (p - 1) = k then (1 : Shell p) else 0) * shiftInv p l j = 0
      rw [ite_eq_right (fun e => hne (by rw [← pred_succ_mod F hl, e])), zero_mul])]
    show (if ((k + (p - 1 - 1)) % (p - 1) + 1) % (p - 1) = k then (1 : Shell p) else 0) *
      (if ((k + (p - 1 - 1)) % (p - 1) + 1) % (p - 1) = j then (1 : Shell p) else 0) = idm k j
    rw [succ_pred_mod F hk, ite_eq_left rfl, one_mul]
    rfl
  · rw [shiftInv_single F (fun k l => shift p k l) k j]
    show (if (j + 1) % (p - 1) = (k + 1) % (p - 1) then (1 : Shell p) else 0) = idm k j
    exact ite_iff ⟨fun e => (shift_inj F (one_lt_n F) j k hj hk (by rw [Nat.add_comm 1 j, Nat.add_comm 1 k]; exact e)).symm,
      fun e => by rw [e]⟩

/-- `g^{(−a) k} g^{a k} = 1` for `a < n`, with `−a = rev a`. -/
theorem pow_rev_mul (F : Frame p κ g) {a : Nat} (ha : a < p - 1) (k : Nat) :
    g ^ (rev (p - 1) a * k) * g ^ (a * k) = 1 := by
  rw [← pow_add, ← FRC.Nat.add_mul, F.pow_mod, ← FRC.Nat.mod_mul_mod _ _ _ F.n_pos, rev_add_mod ha, Nat.zero_mul,
    FRC.Nat.zero_mod, pow_zero]

/-- 6:E7, `F J σ = D₁⁻¹ F J`: the inverse transform turns the shift into the inverse modulation. -/
theorem FJ_shift (F : Frame p κ g) {z : Shell p} (hz : g * z = 1) {k j : Nat} (hk : k < p - 1) (hj : j < p - 1) :
    sumRange (fun l => FJ g κ k l * shift p l j) (p - 1) = sumRange (fun l => modul z k l * FJ g κ l j) (p - 1) := by
  have hn := F.n_pos
  rw [shift_single F, modul_left z (FJ g κ) hk j]
  show quarterTurn g κ * g ^ (rev (p - 1) ((j + 1) % (p - 1)) * k) = z ^ k * (quarterTurn g κ * g ^ (rev (p - 1) j * k))
  have e : g ^ (rev (p - 1) ((j + 1) % (p - 1)) * k) = z ^ k * g ^ (rev (p - 1) j * k) := by
    apply inv_unique (y := g ^ ((j + 1) % (p - 1) * k))
    · exact pow_rev_mul F (FRC.Nat.mod_lt' _ hn) k
    · rw [pow_succ_mod F, assoc4_id, ← mul_pow, mul_comm z g, hz, one_pow, one_mul, pow_rev_mul F hj]
  rw [e]; exact mul_left_comm _ _ _

/-- 6:E7, the quarter-rotation of the Heisenberg pair: `F σ = D₁ F`, `F D₁ = σ⁻¹ F`, `J σ = σ⁻¹ J`, `FJ σ = D₁⁻¹ FJ`. -/
theorem heisenberg (F : Frame p κ g) {z : Shell p} (hz : g * z = 1) {k j : Nat} (hk : k < p - 1) (hj : j < p - 1) :
    sumRange (fun l => Fmat g κ k l * shift p l j) (p - 1) = sumRange (fun l => modul g k l * Fmat g κ l j) (p - 1) ∧
    sumRange (fun l => Fmat g κ k l * modul g l j) (p - 1) = sumRange (fun l => shiftInv p k l * Fmat g κ l j) (p - 1) ∧
    sumRange (fun l => (J (p - 1) k l : Shell p) * shift p l j) (p - 1) =
      sumRange (fun l => shiftInv p k l * J (p - 1) l j) (p - 1) ∧
    sumRange (fun l => FJ g κ k l * shift p l j) (p - 1) = sumRange (fun l => modul z k l * FJ g κ l j) (p - 1) :=
  ⟨Fmat_shift F hk hj, Fmat_modul F hk hj, J_shift F hk hj, FJ_shift F hz hk hj⟩

/-! ## The expansion `F^{[s]} = Σ_r c_r(s) F^r` -/

/-- 6:E7, the coefficients of `frft_eq` are the geometric sums `c_r(s) = ¼ Σ_{ℓ<4} (u w^r)^ℓ`, `u = z^s`, `w = g^κ = −i`:
`c_r(s) = ¼ Σ_ℓ (g^{rκ−s})^ℓ`. -/
theorem frft_coeff (F : Frame p κ g) (u : Shell p) :
    NF0 (-(ofNat κ)) (-(quarterTurn g κ)) u = -(ofNat κ) * (1 + u + u * u + u * u * u) ∧
    NF1 (-(ofNat κ)) (-(quarterTurn g κ)) u =
      -(ofNat κ) * (1 + u * -(quarterTurn g κ) + u * -(quarterTurn g κ) * (u * -(quarterTurn g κ)) +
        u * -(quarterTurn g κ) * (u * -(quarterTurn g κ)) * (u * -(quarterTurn g κ))) ∧
    NF2 (-(ofNat κ)) (-(quarterTurn g κ)) u =
      -(ofNat κ) * (1 + u * (-(quarterTurn g κ) * -(quarterTurn g κ)) +
        u * (-(quarterTurn g κ) * -(quarterTurn g κ)) * (u * (-(quarterTurn g κ) * -(quarterTurn g κ))) +
        u * (-(quarterTurn g κ) * -(quarterTurn g κ)) * (u * (-(quarterTurn g κ) * -(quarterTurn g κ))) *
          (u * (-(quarterTurn g κ) * -(quarterTurn g κ)))) ∧
    NF3 (-(ofNat κ)) (-(quarterTurn g κ)) u =
      -(ofNat κ) * (1 + u * (-(quarterTurn g κ) * -(quarterTurn g κ) * -(quarterTurn g κ)) +
        u * (-(quarterTurn g κ) * -(quarterTurn g κ) * -(quarterTurn g κ)) *
          (u * (-(quarterTurn g κ) * -(quarterTurn g κ) * -(quarterTurn g κ))) +
        u * (-(quarterTurn g κ) * -(quarterTurn g κ) * -(quarterTurn g κ)) *
          (u * (-(quarterTurn g κ) * -(quarterTurn g κ) * -(quarterTurn g κ))) *
          (u * (-(quarterTurn g κ) * -(quarterTurn g κ) * -(quarterTurn g κ)))) :=
  ⟨rfl, red1 (coeff1_id _ _ _) (hii F), red1 (coeff2_id _ _ _) (hii F), red1 (coeff3_id _ _ _) (hii F)⟩

/-- 6:E7, `g^κ = −w = −i`: the coefficient base of `frft_coeff` is `u w^r = z^s (g^κ)^r = g^{rκ − s}`. -/
theorem w_eq_pow_kappa : -(quarterTurn g κ) = g ^ κ := neg_neg _

end Frame
end Shell
end FRC
