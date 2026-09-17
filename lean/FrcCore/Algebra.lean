import FrcCore.Frame

/-!
# FrcCore.Algebra — 1-algebra rows on the core

1:B2 (the Klein orbits `{x, −x, x⁻¹, −x⁻¹}` have four elements off the fourth roots of unity) and
1:D4 (scale periodicity of the residue grid, `g^{n + (p−1)} = g^n`). No axioms.
-/

namespace FRC
namespace Shell
namespace Frame

variable {p : Nat} [Pos p] {κ : Nat} {g : Shell p}

theorem two_lt_p (F : Frame p κ g) : 2 < p := by
  rw [F.cap]
  have h : 4 * 1 ≤ 4 * κ := Nat.mul_le_mul_left 4 F.cap_pos
  exact Nat.lt_of_lt_of_le (by decide : 2 < 4 * 1 + 1) (Nat.succ_le_succ h)

theorem two_ne_zero (F : Frame p κ g) : (2 : Shell p) ≠ 0 := fun h => by
  have := val_injective h
  rw [val_lit, val_zero, FRC.Nat.mod_eq_of_lt F.two_lt_p] at this
  exact Nat.noConfusion this

theorem two_eq_one_add_one : (2 : Shell p) = 1 + 1 :=
  ext (by rw [val_add, val_one, val_lit, FRC.Nat.mod_add_mod _ _ _ hp, FRC.Nat.add_mod_mod _ _ _ hp])

theorem two_mul' (x : Shell p) : (2 : Shell p) * x = x + x := by
  rw [two_eq_one_add_one, right_distrib, one_mul]

theorem eq_zero_of_eq_neg (F : Frame p κ g) {x : Shell p} (h : x = -x) : x = 0 := by
  have h2 : (2 : Shell p) * x = 0 := by
    rw [two_mul']
    calc x + x = x + -x := by rw [← h]
      _ = 0 := add_neg x
  match F.mul_eq_zero h2 with
  | .inl e => exact absurd e F.two_ne_zero
  | .inr e => exact e

/-- 1:B2 (Theorem 1 of 1-algebra) — off the fourth roots of unity, `x`, `−x`, `x⁻¹`, `−x⁻¹` are four
distinct residues (`y` stands for the inverse: `x·y = 1`). -/
theorem klein_orbit_four (F : Frame p κ g) {x y : Shell p} (hxy : x * y = 1) (h4 : x ^ 4 ≠ 1) :
    x ≠ -x ∧ x ≠ y ∧ x ≠ -y ∧ -x ≠ y ∧ -x ≠ -y ∧ y ≠ -y := by
  have hx0 : x ≠ 0 := fun h => F.one_ne_zero (by rw [← hxy, h, zero_mul])
  have hy0 : y ≠ 0 := fun h => F.one_ne_zero (by rw [← hxy, h, mul_zero])
  have h4' : x ^ 4 = (x * x) * (x * x) := by
    rw [show (4 : Nat) = 2 * 2 from rfl, pow_mul, pow_two, pow_two]
  have hsq : x * x ≠ 1 := fun h => h4 (by rw [h4', h, one_mul])
  have hsqn : x * x ≠ -1 := fun h => h4 (by rw [h4', h, neg_mul_neg, one_mul])
  have hxy' : x = y → False := fun e => hsq (by rw [← hxy, e])
  have hxny : x = -y → False := fun e => hsqn (by
    have : x * x = x * -y := by rw [← e]
    rw [this, ← mul_neg, hxy])
  refine ⟨fun h => hx0 (F.eq_zero_of_eq_neg h), hxy', hxny, ?_, ?_, ?_⟩
  · intro h; exact hxny (by rw [← neg_neg x, h])
  · intro h; exact hxy' (by rw [← neg_neg x, h, neg_neg])
  · intro h; exact hy0 (F.eq_zero_of_eq_neg h)

/-- 1:D4 (Lemma 2 of 1-algebra, scale periodicity) — the residue grid repeats with the period `p − 1`
of the drive: `g^{n + (p−1)} = g^n`, hence `x·g^{n + (p−1)} = x·g^n` for every `x`. -/
theorem scale_periodic (F : Frame p κ g) (x : Shell p) (n : Nat) :
    x * g ^ (n + (p - 1)) = x * g ^ n := by
  rw [pow_add, F.pow_n, mul_one]

/-- The affine frame `(a, b)` of 1-algebra (Definition 2): the transported product
`x ⊗ z := a + b·((x − a)/b)·((z − a)/b)`, written with `y` the inverse of `b`. -/
def affineMul (a b y x z : Shell p) : Shell p := a + b * ((x + -a) * y) * ((z + -a) * y)

/-- 1:B4 (Definition 2 of 1-algebra, corrected) — in the affine frame `(a, b)` the multiplicative unit
is `a + b`, not `b`: `(a + b) ⊗ z = z` for every `z`. -/
theorem affine_frame_unit {a b y : Shell p} (hby : b * y = 1) (z : Shell p) :
    affineMul a b y (a + b) z = z := by
  unfold affineMul
  have e1 : a + b + -a = b := by rw [add_comm a b, add_assoc, add_neg, add_zero]
  rw [e1, hby, mul_one, mul_left_comm b, hby, mul_one, add_comm z (-a), ← add_assoc, add_neg, zero_add]

/-- 1:D2 (the window law, injectivity) — two window integers `x, y ≤ H` with `2H < p` that read as the same
residue are equal: `ofNat x = ofNat y → x = y`. (Both are below `p`, so the residues are the integers.) -/
theorem window_injective {H x y : Nat} (hH : 2 * H < p) (hx : x ≤ H) (hy : y ≤ H)
    (h : (ofNat x : Shell p) = ofNat y) : x = y := by
  have hxp : x < p := Nat.lt_of_le_of_lt hx (Nat.lt_of_le_of_lt (Nat.le_add_left H H) (Nat.two_mul H ▸ hH))
  have hyp : y < p := Nat.lt_of_le_of_lt hy (Nat.lt_of_le_of_lt (Nat.le_add_left H H) (Nat.two_mul H ▸ hH))
  have := val_injective h
  rw [val_ofNat, val_ofNat, FRC.Nat.mod_eq_of_lt hxp, FRC.Nat.mod_eq_of_lt hyp] at this
  exact this

/-- 1:D2, the signed window: `x` and `−y` (`x, y ≤ H`, `2H < p`) read as the same residue only when both
are zero — the window's positive and negative halves do not overlap. -/
theorem window_signed {H x y : Nat} (hH : 2 * H < p) (hx : x ≤ H) (hy : y ≤ H)
    (h : (ofNat x : Shell p) = -(ofNat y)) : x = 0 ∧ y = 0 := by
  have hxp : x < p := Nat.lt_of_le_of_lt hx (Nat.lt_of_le_of_lt (Nat.le_add_left H H) (Nat.two_mul H ▸ hH))
  have hyp : y < p := Nat.lt_of_le_of_lt hy (Nat.lt_of_le_of_lt (Nat.le_add_left H H) (Nat.two_mul H ▸ hH))
  have hv := val_injective h
  rw [val_ofNat, val_neg, val_ofNat, FRC.Nat.mod_eq_of_lt hxp, FRC.Nat.mod_eq_of_lt hyp] at hv
  -- hv : x = (p - y) % p
  match Nat.decEq y 0 with
  | .isTrue hy0 =>
    rw [hy0, Nat.sub_zero, FRC.Nat.mod_self p hp] at hv
    exact ⟨hv, hy0⟩
  | .isFalse hy0 =>
    have hpy : p - y < p := Nat.sub_lt hp (Nat.pos_of_ne_zero hy0)
    rw [FRC.Nat.mod_eq_of_lt hpy] at hv
    -- x = p − y with x ≤ H, y ≤ H gives p = x + y ≤ 2H < p
    have : p = x + y := by rw [hv, FRC.Nat.sub_add_cancel (Nat.le_of_lt hyp)]
    have hle : x + y ≤ 2 * H := by rw [Nat.two_mul]; exact Nat.add_le_add hx hy
    exact absurd (Nat.lt_of_le_of_lt (this ▸ hle) hH) (Nat.lt_irrefl p)

end Frame
end Shell
end FRC
