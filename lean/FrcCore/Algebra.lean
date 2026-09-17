import FrcCore.Frame

/-!
# FrcCore.Algebra — 1-algebra rows on the core

1:B2 (the quarter-turn exists; the fourth roots of unity are exactly `{1, i, −1, −i}`; the Klein orbits
`{x, −x, x⁻¹, −x⁻¹}` have four elements off them), 1:B4 (the affine unit), 1:C4 (the meridian involution),
1:D2 (the window law), 1:D4 (scale periodicity), 1:D5 (the range obstruction at `(13, 2)`), 1:E2 (the complex
chart has a zero divisor), 1:F1 (no south pole). No axioms.
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

theorem ofNat_add (x y : Nat) : (ofNat x : Shell p) + ofNat y = ofNat (x + y) :=
  ext (by rw [val_add, val_ofNat, val_ofNat, val_ofNat, FRC.Nat.mod_add_mod _ _ _ hp, FRC.Nat.add_mod_mod _ _ _ hp])

theorem ofNat_mul (x y : Nat) : (ofNat x : Shell p) * ofNat y = ofNat (x * y) :=
  ext (by rw [val_mul, val_ofNat, val_ofNat, val_ofNat, FRC.Nat.mod_mul_mod _ _ _ hp, FRC.Nat.mul_mod_mod _ _ _ hp])

/-- 1:D2, the read-back of sums: for `x, y ≤ H` and `4H < p`, the residue of `x + y` determines the integer
`x + y` among the integers `z ≤ 2H`. -/
theorem window_add_readback {H x y z : Nat} (hH : 2 * (2 * H) < p) (hx : x ≤ H) (hy : y ≤ H) (hz : z ≤ 2 * H)
    (h : (ofNat x : Shell p) + ofNat y = ofNat z) : x + y = z := by
  rw [ofNat_add] at h
  exact window_injective hH (by rw [Nat.two_mul]; exact Nat.add_le_add hx hy) hz h

/-- 1:D2, the read-back of products: for `x, y ≤ H` and `2H² < p`, the residue of `x·y` determines the integer
`x·y` among the integers `z ≤ H²`. -/
theorem window_mul_readback {H x y z : Nat} (hH : 2 * (H * H) < p) (hx : x ≤ H) (hy : y ≤ H) (hz : z ≤ H * H)
    (h : (ofNat x : Shell p) * ofNat y = ofNat z) : x * y = z := by
  rw [ofNat_mul] at h
  exact window_injective hH (Nat.mul_le_mul hx hy) hz h

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

/-- 1:B2 (Theorem 1, existence clause) — a quarter-turn `u` with `u² = −1` exists on every shell. -/
theorem quarter_turn_exists (F : Frame p κ g) : ∃ u : Shell p, u * u = -1 :=
  ⟨quarterTurn g κ, F.quarter_turn_sq⟩

/-- 1:B2 (Theorem 1, the structural set) — the fourth roots of unity are exactly `1, −1, i, −i`. -/
theorem fourth_roots (F : Frame p κ g) (x : Shell p) :
    x ^ 4 = 1 ↔ x = 1 ∨ x = -1 ∨ x = quarterTurn g κ ∨ x = -(quarterTurn g κ) := by
  have h4 : x ^ 4 = (x * x) * (x * x) := by
    rw [show (4 : Nat) = 2 * 2 from rfl, pow_mul, pow_two, pow_two]
  have hi := F.quarter_turn_sq
  constructor
  · intro h
    rw [h4] at h
    match F.sq_eq_one h with
    | .inl e => match F.sq_eq_one e with
      | .inl e1 => exact .inl e1
      | .inr e1 => exact .inr (.inl e1)
    | .inr e =>
      -- x² = −1 = i²: (x + −i)(x + i) = 0
      have e2 : (x + -(quarterTurn g κ)) * (x + quarterTurn g κ) = 0 := by
        rw [right_distrib, left_distrib, left_distrib, e, ← neg_mul, ← neg_mul, hi, neg_neg, mul_comm (quarterTurn g κ) x]
        rw [add_assoc, ← add_assoc (x * quarterTurn g κ), add_neg, zero_add, neg_add]
      match F.mul_eq_zero e2 with
      | .inl e3 => exact .inr (.inr (.inl (by
          calc x = x + 0 := (add_zero x).symm
            _ = x + (-(quarterTurn g κ) + quarterTurn g κ) := by rw [neg_add]
            _ = (x + -(quarterTurn g κ)) + quarterTurn g κ := (add_assoc _ _ _).symm
            _ = quarterTurn g κ := by rw [e3, zero_add])))
      | .inr e3 => exact .inr (.inr (.inr (eq_neg_of_add_eq_zero e3)))
  · intro h
    match h with
    | .inl e => rw [e, one_pow]
    | .inr (.inl e) => rw [h4, e, neg_mul_neg, one_mul, one_mul]
    | .inr (.inr (.inl e)) => rw [h4, e, hi, neg_mul_neg, one_mul]
    | .inr (.inr (.inr e)) => rw [h4, e, neg_mul_neg, hi, neg_mul_neg, one_mul]

/-- 1:C4 (Definition 5 (a)) — the meridian involution: `(−a)·g^{n + 2κ} = a·g^n`. -/
theorem meridian_involution (F : Frame p κ g) (a : Shell p) (n : Nat) :
    -a * g ^ (n + 2 * κ) = a * g ^ n := by
  rw [pow_add, F.half_period, mul_comm (g ^ n), ← mul_assoc, neg_mul_neg, mul_one]

/-- 1:F1 (Theorem 3) — `2s = 0 ⇒ s = 0`: the additive cycle has no element of order two; the antipode of
the origin is not a residue. -/
theorem no_south_pole (F : Frame p κ g) (s : Shell p) (h : (2 : Shell p) * s = 0) : s = 0 :=
  match F.mul_eq_zero h with
  | .inl e => absurd e F.two_ne_zero
  | .inr e => e

/-- The complex chart: pairs `(a, b)` read as `a + b·X` with `X² = −1`, multiplied as
`(a, b)(c, d) = (ac − bd, ad + bc)`. -/
def cmul (x y : Shell p × Shell p) : Shell p × Shell p :=
  (x.1 * y.1 + -(x.2 * y.2), x.1 * y.2 + x.2 * y.1)

/-- 1:E2 (Proposition 5 reversed) — on a shell that already has a square root of `−1` the complex chart is
not a field: `(i, 1)·(−i, 1) = (0, 0)` with both factors nonzero (`X + i` and `X − i` are zero divisors). -/
theorem complex_chart_zero_divisor (F : Frame p κ g) :
    cmul (quarterTurn g κ, (1 : Shell p)) (-(quarterTurn g κ), 1) = (0, 0) ∧
    (quarterTurn g κ, (1 : Shell p)) ≠ (0, 0) ∧ (-(quarterTurn g κ), (1 : Shell p)) ≠ (0, 0) := by
  refine ⟨?_, fun h => F.one_ne_zero (congrArg Prod.snd h), fun h => F.one_ne_zero (congrArg Prod.snd h)⟩
  unfold cmul
  show (quarterTurn g κ * -(quarterTurn g κ) + -(1 * 1), quarterTurn g κ * 1 + 1 * -(quarterTurn g κ)) = (0, 0)
  rw [← mul_neg, F.quarter_turn_sq, neg_neg, one_mul, add_neg, mul_one, one_mul, add_neg]

/-- 1:D5, the range obstruction (Theorem 2 of 1-algebra refuted) at `p = 13`, `g = 2`: every grid point
`x / 2^n` with `x < 13` and `n ≥ 3` is at most `3/2` — as the integer statement `2x ≤ 3·2^n`. -/
theorem approx_theorem_refuted (n x : Nat) (hn : 3 ≤ n) (hx : x < 13) : 2 * x ≤ 3 * 2 ^ n := by
  have h8 : 2 ^ 3 ≤ 2 ^ n := Nat.pow_le_pow_right (Nat.zero_lt_succ 1) hn
  have h1 : 2 * x ≤ 2 * 12 := Nat.mul_le_mul_left 2 (Nat.le_of_lt_succ hx)
  have h2 : 3 * 2 ^ 3 ≤ 3 * 2 ^ n := Nat.mul_le_mul_left 3 h8
  exact Nat.le_trans h1 h2

end Frame
end Shell
end FRC
