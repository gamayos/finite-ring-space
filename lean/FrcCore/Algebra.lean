import FrcCore.Sum

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

/-- 1:B2 (Theorem 1 of 1-algebra), 2:D7 — off the fourth roots of unity, `x`, `−x`, `x⁻¹`, `−x⁻¹` are four
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

/-! ### 1:B2, the count: the Klein orbits off `Q₄` are exactly `κ − 1`, represented by `g^r`, `1 ≤ r < κ` -/

/-- `y` lies in the Klein orbit of `x`: `y ∈ {x, −x, x⁻¹, −x⁻¹}` (the inverse written as `x·y = 1`). -/
def InOrbit (x y : Shell p) : Prop := y = x ∨ y = -x ∨ x * y = 1 ∨ x * -y = 1

theorem two_mul_eq (κ : Nat) : 2 * κ = κ + κ := Nat.two_mul κ
theorem three_mul_eq (κ : Nat) : 3 * κ = κ + κ + κ := by rw [Nat.succ_mul, Nat.two_mul]
theorem four_mul_eq (κ : Nat) : 4 * κ = κ + κ + κ + κ := by rw [Nat.succ_mul, three_mul_eq]

/-- The exponent `m` of `x = g^m` reduced to its orbit representative in `[1, κ)`. -/
theorem orbit_rep_of_exp (F : Frame p κ g) {m : Nat} (hm : m < p - 1) (h0 : m ≠ 0) (h1 : m ≠ κ)
    (h2 : m ≠ 2 * κ) (h3 : m ≠ 3 * κ) :
    ∃ r, 1 ≤ r ∧ r < κ ∧ InOrbit (g ^ r) (g ^ m) := by
  have hn := F.n_eq
  have hπ := F.half_period
  rw [hn, four_mul_eq] at hm
  rw [two_mul_eq] at h2 hπ
  rw [three_mul_eq] at h3
  match Nat.lt_or_ge m κ with
  | Or.inl hlt => exact ⟨m, Nat.pos_of_ne_zero h0, hlt, Or.inl rfl⟩
  | Or.inr hge1 => match Nat.lt_or_ge m (κ + κ) with
    | Or.inl hlt =>
      -- κ < m < 2κ: r = 2κ − m, and g^m · (−g^r) = −g^{2κ} = 1
      have hgt : κ < m := Nat.lt_of_le_of_ne hge1 (fun e => h1 e.symm)
      refine ⟨κ + κ - m, ?_, ?_, Or.inr (Or.inr (Or.inr ?_))⟩
      · refine Nat.lt_of_add_lt_add_right (n := m) ?_
        rw [Nat.zero_add, FRC.Nat.sub_add_cancel (Nat.le_of_lt hlt)]; exact hlt
      · refine Nat.lt_of_add_lt_add_right (n := m) ?_
        rw [FRC.Nat.sub_add_cancel (Nat.le_of_lt hlt)]; exact Nat.add_lt_add_left hgt κ
      · rw [← mul_neg, ← pow_add, FRC.Nat.sub_add_cancel (Nat.le_of_lt hlt), hπ, neg_neg]
    | Or.inr hge2 => match Nat.lt_or_ge m (κ + κ + κ) with
      | Or.inl hlt =>
        -- 2κ < m < 3κ: r = m − 2κ, and g^m = −g^r
        have hgt : κ + κ < m := Nat.lt_of_le_of_ne hge2 (fun e => h2 e.symm)
        refine ⟨m - (κ + κ), ?_, ?_, Or.inr (Or.inl ?_)⟩
        · refine Nat.lt_of_add_lt_add_right (n := κ + κ) ?_
          rw [Nat.zero_add, FRC.Nat.sub_add_cancel hge2]; exact hgt
        · refine Nat.lt_of_add_lt_add_right (n := κ + κ) ?_
          rw [FRC.Nat.sub_add_cancel hge2, Nat.add_comm κ (κ + κ)]; exact hlt
        · have : m = κ + κ + (m - (κ + κ)) := (FRC.Nat.add_sub_of_le hge2).symm
          rw [this, pow_add, hπ, neg_one_mul, FRC.Nat.add_sub_cancel_left]
      | Or.inr hge3 =>
        -- 3κ < m < 4κ: r = 4κ − m, and g^m · g^r = g^{4κ} = 1
        have hgt : κ + κ + κ < m := Nat.lt_of_le_of_ne hge3 (fun e => h3 e.symm)
        refine ⟨κ + κ + κ + κ - m, ?_, ?_, Or.inr (Or.inr (Or.inl ?_))⟩
        · refine Nat.lt_of_add_lt_add_right (n := m) ?_
          rw [Nat.zero_add, FRC.Nat.sub_add_cancel (Nat.le_of_lt hm)]; exact hm
        · refine Nat.lt_of_add_lt_add_right (n := m) ?_
          rw [FRC.Nat.sub_add_cancel (Nat.le_of_lt hm), Nat.add_comm κ m]
          exact Nat.add_lt_add_right hgt κ
        · rw [← pow_add, FRC.Nat.sub_add_cancel (Nat.le_of_lt hm), ← four_mul_eq, ← hn, F.pow_n]

/-- Off the fourth roots of unity, `x = g^m` has `m ∉ {0, κ, 2κ, 3κ}`. -/
theorem exp_not_fourth (F : Frame p κ g) {m : Nat} (h4 : (g ^ m) ^ 4 ≠ 1) :
    m ≠ 0 ∧ m ≠ κ ∧ m ≠ 2 * κ ∧ m ≠ 3 * κ := by
  have hi := (F.quarter_turn_order).2
  refine ⟨fun e => h4 (by rw [e, pow_zero, one_pow]), fun e => h4 (by rw [e, hi]), fun e => h4 ?_, fun e => h4 ?_⟩
  · rw [e, Nat.mul_comm 2 κ, pow_mul, ← pow_mul, show (2 : Nat) * 4 = 4 * 2 from rfl, pow_mul, hi, one_pow]
  · rw [e, Nat.mul_comm 3 κ, pow_mul, ← pow_mul, show (3 : Nat) * 4 = 4 * 3 from rfl, pow_mul, hi, one_pow]

/-- 1:B2 (Theorem 1, the count, existence), 2:D7 — every residue off `Q₄` lies in the Klein orbit of some `g^r`
with `1 ≤ r < κ`. -/
theorem orbit_rep (F : Frame p κ g) {x : Shell p} (hx : x ≠ 0) (h4 : x ^ 4 ≠ 1) :
    ∃ r, 1 ≤ r ∧ r < κ ∧ InOrbit (g ^ r) x := by
  match F.eq_pow_of_ne_zero hx with
  | ⟨m, hm, e⟩ =>
    rw [← e] at h4 ⊢
    match F.exp_not_fourth h4 with
    | ⟨h0, h1, h2, h3⟩ => exact F.orbit_rep_of_exp hm h0 h1 h2 h3

theorem neg_mul_of_mul_neg {a b : Shell p} (e : a * -b = 1) : -a * b = 1 := by
  rw [← neg_mul, mul_neg]; exact e

/-- The orbit relation is symmetric. -/
theorem inOrbit_symm {a b : Shell p} (h : InOrbit a b) : InOrbit b a :=
  match h with
  | Or.inl e => Or.inl e.symm
  | Or.inr (Or.inl e) => Or.inr (Or.inl (by rw [e, neg_neg]))
  | Or.inr (Or.inr (Or.inl e)) => Or.inr (Or.inr (Or.inl (by rw [mul_comm]; exact e)))
  | Or.inr (Or.inr (Or.inr e)) => Or.inr (Or.inr (Or.inr (by rw [← mul_neg, mul_comm, mul_neg]; exact e)))

theorem neg_eq_neg {a b : Shell p} (h : -a = -b) : a = b := by rw [← neg_neg a, h, neg_neg]

/-- The orbit relation is transitive. -/
theorem inOrbit_trans {a b c : Shell p} (h1 : InOrbit a b) (h2 : InOrbit b c) : InOrbit a c := by
  have hab : b = a ∨ b = -a ∨ a * b = 1 ∨ a * -b = 1 := h1
  have hbc : c = b ∨ c = -b ∨ b * c = 1 ∨ b * -c = 1 := h2
  unfold InOrbit
  match hab, hbc with
  | Or.inl e, h => exact e ▸ h
  | Or.inr (Or.inl e), Or.inl e' => exact Or.inr (Or.inl (e' ▸ e))
  | Or.inr (Or.inl e), Or.inr (Or.inl e') => exact Or.inl (by rw [e', e, neg_neg])
  | Or.inr (Or.inl e), Or.inr (Or.inr (Or.inl e')) => exact Or.inr (Or.inr (Or.inr (by rw [← mul_neg, neg_mul, ← e]; exact e')))
  | Or.inr (Or.inl e), Or.inr (Or.inr (Or.inr e')) => exact Or.inr (Or.inr (Or.inl (by rw [← neg_mul_neg, ← e]; exact e')))
  | Or.inr (Or.inr (Or.inl e)), Or.inl e' => exact Or.inr (Or.inr (Or.inl (e' ▸ e)))
  | Or.inr (Or.inr (Or.inl e)), Or.inr (Or.inl e') => exact Or.inr (Or.inr (Or.inr (by rw [e', neg_neg]; exact e)))
  | Or.inr (Or.inr (Or.inl e)), Or.inr (Or.inr (Or.inl e')) =>
    exact Or.inl (inv_unique (x := c) (x' := a) (y := b) (by rw [mul_comm]; exact e') e)
  | Or.inr (Or.inr (Or.inl e)), Or.inr (Or.inr (Or.inr e')) =>
    exact Or.inr (Or.inl (by
      have := inv_unique (x := -c) (x' := a) (y := b) (by rw [mul_comm]; exact e') e
      rw [← this, neg_neg]))
  | Or.inr (Or.inr (Or.inr e)), Or.inl e' => exact Or.inr (Or.inr (Or.inr (e' ▸ e)))
  | Or.inr (Or.inr (Or.inr e)), Or.inr (Or.inl e') => exact Or.inr (Or.inr (Or.inl (by rw [e']; exact e)))
  | Or.inr (Or.inr (Or.inr e)), Or.inr (Or.inr (Or.inl e')) =>
    exact Or.inr (Or.inl (inv_unique (x := -a) (x' := c) (y := b) (neg_mul_of_mul_neg e) (by rw [mul_comm]; exact e')).symm)
  | Or.inr (Or.inr (Or.inr e)), Or.inr (Or.inr (Or.inr e')) =>
    exact Or.inl (neg_eq_neg (inv_unique (x := -a) (x' := -c) (y := b) (neg_mul_of_mul_neg e) (by rw [mul_comm]; exact e'))).symm

/-- The exponents of the orbit of `g^r`: `g^s ∈ orbit(g^r)`, `s < n`, forces `s ∈ {r, r + 2κ, 4κ − r, 2κ − r}`
(for `1 ≤ r < κ`). -/
theorem orbit_exponent (F : Frame p κ g) {r s : Nat} (hr1 : 1 ≤ r) (hrκ : r < κ) (hs : s < p - 1)
    (h : InOrbit (g ^ r) (g ^ s)) : s = r ∨ s = r + (κ + κ) ∨ s = κ + κ + κ + κ - r ∨ s = κ + κ - r := by
  have hn := F.n_eq
  have hπ := F.half_period
  rw [two_mul_eq] at hπ
  rw [hn, four_mul_eq] at hs
  have hr2 : r < κ + κ := Nat.lt_of_lt_of_le hrκ (Nat.le_add_right κ κ)
  have hr4 : r < κ + κ + κ + κ := Nat.lt_of_lt_of_le hr2 (Nat.le_trans (Nat.le_add_right _ κ) (Nat.le_add_right _ κ))
  have hpow_inj : ∀ {i j : Nat}, i < κ + κ + κ + κ → j < κ + κ + κ + κ → g ^ i = g ^ j → i = j :=
    fun hi hj e => F.pow_inj (by rw [hn, four_mul_eq]; exact hi) (by rw [hn, four_mul_eq]; exact hj) e
  have hpn : g ^ (κ + κ + κ + κ) = 1 := by rw [← four_mul_eq, ← hn]; exact F.pow_n
  match h with
  | Or.inl e => exact Or.inl (hpow_inj hs hr4 e)
  | Or.inr (Or.inl e) =>
    have e' : g ^ s = g ^ (r + (κ + κ)) := by rw [e, pow_add, hπ, mul_comm, neg_one_mul]
    have hlt : r + (κ + κ) < κ + κ + κ + κ := by
      rw [show κ + κ + κ + κ = (κ + κ) + (κ + κ) by rw [Nat.add_assoc]]
      exact Nat.add_lt_add_right hr2 _
    exact Or.inr (Or.inl (hpow_inj hs hlt e'))
  | Or.inr (Or.inr (Or.inl e)) =>
    have hlt : κ + κ + κ + κ - r < κ + κ + κ + κ := Nat.sub_lt (Nat.lt_of_lt_of_le (Nat.zero_lt_succ 0) (Nat.le_trans hr1 (Nat.le_of_lt hr4))) hr1
    have e2 : g ^ r * g ^ (κ + κ + κ + κ - r) = 1 := by rw [← pow_add, FRC.Nat.add_sub_of_le (Nat.le_of_lt hr4), hpn]
    have e' : g ^ s = g ^ (κ + κ + κ + κ - r) := F.mul_left_cancel (F.pow_ne_zero r) (e.trans e2.symm)
    exact Or.inr (Or.inr (Or.inl (hpow_inj hs hlt e')))
  | Or.inr (Or.inr (Or.inr e)) =>
    have hlt : κ + κ - r < κ + κ + κ + κ := Nat.lt_of_le_of_lt (Nat.sub_le _ _)
      (Nat.lt_of_lt_of_le (Nat.lt_add_of_pos_right F.cap_pos) (Nat.le_add_right _ κ))
    have e2 : g ^ r * -(g ^ (κ + κ - r)) = 1 := by
      rw [← mul_neg, ← pow_add, FRC.Nat.add_sub_of_le (Nat.le_of_lt hr2), hπ, neg_neg]
    have e' : -(g ^ s) = -(g ^ (κ + κ - r)) := F.mul_left_cancel (F.pow_ne_zero r) (e.trans e2.symm)
    exact Or.inr (Or.inr (Or.inr (hpow_inj hs hlt (neg_eq_neg e'))))

/-- 1:B2 (Theorem 1, the count, uniqueness), 2:D7 — two representatives `g^r`, `g^{r'}` with `1 ≤ r, r' < κ` whose
orbits meet are the same: the Klein orbits off `Q₄` are exactly `κ − 1`, one for each `r ∈ [1, κ)`. -/
theorem orbit_rep_unique (F : Frame p κ g) {r r' : Nat} (hr1 : 1 ≤ r) (hrκ : r < κ) (_hr1' : 1 ≤ r')
    (hrκ' : r' < κ) {x : Shell p} (hx : InOrbit (g ^ r) x) (hx' : InOrbit (g ^ r') x) : r = r' := by
  have hn := F.n_eq
  have hr' : r' < p - 1 := by
    rw [hn, four_mul_eq]
    exact Nat.lt_of_lt_of_le hrκ' (Nat.le_trans (Nat.le_add_right κ κ) (Nat.le_trans (Nat.le_add_right _ κ) (Nat.le_add_right _ κ)))
  have h := inOrbit_trans hx (inOrbit_symm hx')
  match F.orbit_exponent hr1 hrκ hr' h with
  | Or.inl e => exact e.symm
  | Or.inr (Or.inl e) =>
    exact absurd hrκ' (Nat.not_lt_of_le (by rw [e]; exact Nat.le_trans (Nat.le_add_right κ κ) (Nat.le_add_left _ r)))
  | Or.inr (Or.inr (Or.inl e)) =>
    -- 4κ − r > κ since r < κ
    have : κ ≤ κ + κ + κ + κ - r := by
      apply FRC.Nat.le_sub_of_add_le
      rw [Nat.add_assoc, Nat.add_assoc]
      exact Nat.add_le_add_left (Nat.le_trans (Nat.le_of_lt hrκ) (Nat.le_add_right κ _)) κ
    exact absurd hrκ' (Nat.not_lt_of_le (e ▸ this))
  | Or.inr (Or.inr (Or.inr e)) =>
    -- 2κ − r > κ since r < κ
    have : κ ≤ κ + κ - r := by
      apply FRC.Nat.le_sub_of_add_le
      exact Nat.add_le_add_left (Nat.le_of_lt hrκ) κ
    exact absurd hrκ' (Nat.not_lt_of_le (e ▸ this))

/-! ### 1:C2 — the frame group: the affine maps `x ↦ a + b·x`, `b ≠ 0`, act simply transitively on the frames -/

/-- An affine map of the shell, `x ↦ a + b·x` with `b ≠ 0`. -/
structure Affine (p : Nat) [Pos p] where
  a : Shell p
  b : Shell p
  hb : b ≠ 0

namespace Affine

def apply (φ : Affine p) (x : Shell p) : Shell p := φ.a + φ.b * x

theorem ext' {φ ψ : Affine p} (ha : φ.a = ψ.a) (hb : φ.b = ψ.b) : φ = ψ := by
  cases φ; cases ψ; cases ha; cases hb; rfl

/-- The identity `x ↦ 0 + 1·x`. -/
def one (F : Frame p κ g) : Affine p := ⟨0, 1, F.one_ne_zero⟩

/-- Composition: `(a, b) ∘ (c, d) = (a + b·c, b·d)`. -/
def comp (F : Frame p κ g) (φ ψ : Affine p) : Affine p := ⟨φ.a + φ.b * ψ.a, φ.b * ψ.b, F.mul_ne_zero φ.hb ψ.hb⟩

theorem comp_apply (F : Frame p κ g) (φ ψ : Affine p) (x : Shell p) :
    (comp F φ ψ).apply x = φ.apply (ψ.apply x) := by
  unfold comp apply
  show φ.a + φ.b * ψ.a + φ.b * ψ.b * x = φ.a + φ.b * (ψ.a + ψ.b * x)
  rw [left_distrib, add_assoc, mul_assoc]

theorem one_apply (F : Frame p κ g) (x : Shell p) : (one F).apply x = x := by
  unfold one apply; show 0 + 1 * x = x; rw [one_mul, zero_add]

theorem comp_assoc (F : Frame p κ g) (φ ψ χ : Affine p) : comp F (comp F φ ψ) χ = comp F φ (comp F ψ χ) :=
  ext' (by show φ.a + φ.b * ψ.a + φ.b * ψ.b * χ.a = φ.a + φ.b * (ψ.a + ψ.b * χ.a); rw [left_distrib, add_assoc, mul_assoc])
    (by show φ.b * ψ.b * χ.b = φ.b * (ψ.b * χ.b); exact mul_assoc _ _ _)

/-- The inverse of `(a, b)`: `(−a·b⁻¹, b⁻¹)`, with `y` the inverse of `b`. -/
def inv (F : Frame p κ g) (φ : Affine p) (y : Shell p) (hy : φ.b * y = 1) : Affine p :=
  ⟨-(φ.a * y), y, fun h => F.one_ne_zero (by rw [← hy, h, mul_zero])⟩

theorem comp_inv (F : Frame p κ g) (φ : Affine p) (y : Shell p) (hy : φ.b * y = 1) :
    comp F φ (inv F φ y hy) = one F :=
  ext' (by
      show φ.a + φ.b * -(φ.a * y) = 0
      calc φ.a + φ.b * -(φ.a * y) = φ.a + -(φ.b * (φ.a * y)) := by rw [← mul_neg]
        _ = φ.a + -(φ.a * (φ.b * y)) := by rw [mul_left_comm]
        _ = φ.a + -φ.a := by rw [hy, mul_one]
        _ = 0 := add_neg _)
    (by show φ.b * y = 1; exact hy)

/-- 1:C2 (Prop. of the frame group), simple transitivity — for frames `(a, b)` and `(c, d)` (`b, d ≠ 0`) there
is exactly one affine map carrying the first to the second: `φ (a, b) := (φ.apply a, φ.b · b)`. -/
theorem simply_transitive (F : Frame p κ g) (a b c d : Shell p) (hb : b ≠ 0) (hd : d ≠ 0) :
    (∃ φ : Affine p, φ.apply a = c ∧ φ.b * b = d) ∧
    (∀ φ ψ : Affine p, φ.apply a = c → φ.b * b = d → ψ.apply a = c → ψ.b * b = d → φ = ψ) := by
  match F.exists_inv hb with
  | ⟨y, hy⟩ =>
    constructor
    · refine ⟨⟨c + -(d * y * a), d * y, ?_⟩, ?_, ?_⟩
      · exact F.mul_ne_zero hd (fun h => F.one_ne_zero (by rw [← hy, h, mul_zero]))
      · show c + -(d * y * a) + d * y * a = c
        rw [add_assoc, neg_add, add_zero]
      · show d * y * b = d
        rw [mul_assoc, mul_comm y b, hy, mul_one]
    · intro φ ψ h1 h2 h3 h4
      have eb : φ.b = ψ.b := by
        calc φ.b = φ.b * (b * y) := by rw [hy, mul_one]
          _ = (φ.b * b) * y := (mul_assoc _ _ _).symm
          _ = (ψ.b * b) * y := by rw [h2, h4]
          _ = ψ.b := by rw [mul_assoc, hy, mul_one]
      have ea : φ.a = ψ.a := by
        have e1 : φ.a + φ.b * a = c := h1
        have e2 : ψ.a + ψ.b * a = c := h3
        rw [← eb] at e2
        exact add_right_cancel (e1.trans e2.symm)
      exact ext' ea eb

end Affine

/-- The number of `x < n` with `P x`, as a sum of `0`s and `1`s. -/
def natCount (P : Nat → Prop) [DecidablePred P] : Nat → Nat
  | 0 => 0
  | n + 1 => natCount P n + if P n then 1 else 0

theorem natCount_ne_zero (n : Nat) : natCount (fun x => x ≠ 0) (n + 1) = n := by
  induction n with
  | zero => rfl
  | succ n ih =>
    show natCount (fun x => x ≠ 0) (n + 1) + (if n + 1 ≠ 0 then 1 else 0) = n + 1
    rw [ih, if_pos (Nat.succ_ne_zero n)]

/-- 1:C2, the order — the frames `(a, b)`, `b ≠ 0`, number `p·(p − 1)`: `p` choices of the origin, `p − 1`
of the unit. -/
theorem frame_count (_F : Frame p κ g) :
    natCount (fun _ => True) p * natCount (fun b => b ≠ 0) p = p * (p - 1) := by
  have h1 : ∀ n, natCount (fun _ => True) n = n := fun n => by
    induction n with
    | zero => rfl
    | succ n ih => show natCount (fun _ => True) n + (if True then 1 else 0) = n + 1; rw [ih, if_pos trivial]
  have hp : p = (p - 1) + 1 := (FRC.Nat.sub_add_cancel Pos.pos).symm
  rw [h1]
  have h2 : natCount (fun b => b ≠ 0) p = p - 1 := by
    have := natCount_ne_zero (p - 1)
    rw [← hp] at this; exact this
  rw [h2]

end Frame
end Shell
end FRC
