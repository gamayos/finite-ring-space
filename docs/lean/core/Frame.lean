import FrcCore.FrameCore

/-!
# FrcCore.Frame — the frame's arithmetic (the frame theme)

The frame itself, `IsPrimitive`, `Generates`, `Frame`, the half-period, the quarter-turn, the orientation classes and
the Euler identity, is `FrameCore.lean` (split off by task LM24, every name unchanged); this file imports it, so a module
that imports `Frame` sees both.

Since the ledger migration (task LM17) it holds the frame's arithmetic from 1-algebra (scale periodicity, the affine
frame, the window law and its read-backs, `ofNat_add`, `ofNat_mul`, the quarter-turn and the fourth roots, the meridian
involution, the complex chart, Theorem approx, `natCount`), `ofNat_self` and `ofNat_add_self` (from 13-epi), the root pair
(from 10-dimensions) and the counting lemmas of 20-rh, all under their old names in `FRC.Shell` and `FRC.Shell.Frame`.
The bounded quantifiers' deciders (from 10-dimensions and 20-rh) are in `Series.lean` since task LM22. No axioms.
-/

namespace FRC
namespace Shell

variable {p : Nat} [Pos p]

namespace Frame
variable {κ : Nat} {g : Shell p}

/-! ## The frame's arithmetic (moved from 1-algebra by the ledger migration, task LM17) -/

/-- 1:D4 (Lemma 2 of 1-algebra, scale periodicity) — the residue grid repeats with the period `p − 1`
of the drive: `g^{n + (p−1)} = g^n`, hence `x·g^{n + (p−1)} = x·g^n` for every `x`. -/
theorem scale_periodic (F : Frame p κ g) (x : Shell p) (n : Nat) :
    x * g ^ (n + (p - 1)) = x * g ^ n := by
  rw [pow_add, F.pow_n, mul_one]

/-- The affine frame `(a, b)` of 1-algebra (Definition 2): the transported product
`x ⊗ z := a + b·((x − a)/b)·((z − a)/b)`, written with `y` the inverse of `b`. -/
def affineMul (a b y x z : Shell p) : Shell p := a + b * ((x + -a) * y) * ((z + -a) * y)

/-- 1:B4 (Definition 2 of 1-algebra) — in the affine frame `(a, b)` the multiplicative unit
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

/-- `p ≡ 0` on the shell. -/
theorem ofNat_self : (ofNat p : Shell p) = 0 := by
  apply ext; show p % p = 0; exact FRC.Nat.mod_self p Pos.pos

theorem ofNat_add_self (n : Nat) : (ofNat (n + p) : Shell p) = ofNat n := by
  rw [← ofNat_add, ofNat_self, add_zero]

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

/-- 1:D6 (Theorem approx, the range at `p = 13`, `g = 2`): every grid point
`x / 2^n` with `x < 13` and `n ≥ 3` is at most `3/2` — as the integer statement `2x ≤ 3·2^n`. -/
theorem approx_obstruction (n x : Nat) (hn : 3 ≤ n) (hx : x < 13) : 2 * x ≤ 3 * 2 ^ n := by
  have h8 : 2 ^ 3 ≤ 2 ^ n := Nat.pow_le_pow_right (Nat.zero_lt_succ 1) hn
  have h1 : 2 * x ≤ 2 * 12 := Nat.mul_le_mul_left 2 (Nat.le_of_lt_succ hx)
  have h2 : 3 * 2 ^ 3 ≤ 3 * 2 ^ n := Nat.mul_le_mul_left 3 h8
  exact Nat.le_trans h1 h2

/-- The number of `x < n` with `P x`, as a sum of `0`s and `1`s. -/
def natCount (P : Nat → Prop) [DecidablePred P] : Nat → Nat
  | 0 => 0
  | n + 1 => natCount P n + if P n then 1 else 0

theorem natCount_ne_zero (n : Nat) : natCount (fun x => x ≠ 0) (n + 1) = n := by
  induction n with
  | zero => rfl
  | succ n ih =>
    show natCount (fun x => x ≠ 0) (n + 1) + (if n + 1 ≠ 0 then 1 else 0) = n + 1
    rw [ih, ite_eq_left (Nat.succ_ne_zero n)]

/-- 10:E4, 10:P2 — the root pair: if `x² = a` with `x ≠ 0` then `y² = a` iff `y = x` or `y = −x`, and `−x ≠ x`;
each quadratic defining congruence has exactly two roots on a framed Carrier. -/
theorem root_pair (F : Frame p κ g) (a x : Shell p) (hx : x * x = a) (hx0 : x ≠ 0) :
    (∀ y : Shell p, y * y = a ↔ (y = x ∨ y = -x)) ∧ -x ≠ x := by
  refine ⟨fun y => ⟨fun hy => ?_, fun hy => ?_⟩, fun h => hx0 (F.eq_zero_of_eq_neg h.symm)⟩
  · have h0 : (y + -x) * (y + x) = 0 := by
      rw [Shell.right_distrib, Shell.left_distrib, Shell.left_distrib, ← Shell.neg_mul, ← Shell.neg_mul,
        Shell.mul_comm y x, Shell.add_assoc, ← Shell.add_assoc (x * y), Shell.add_neg, Shell.zero_add,
        hy, hx, Shell.add_neg]
    rcases F.mul_eq_zero h0 with h | h
    · left; exact (Shell.eq_neg_of_add_eq_zero h).trans (Shell.neg_neg x)
    · right; exact Shell.eq_neg_of_add_eq_zero h
  · rcases hy with rfl | rfl
    · exact hx
    · rw [Shell.neg_mul_neg]; exact hx

/-- Counting where nothing satisfies the predicate. -/
theorem natCount_eq_zero (P : Nat → Prop) [DecidablePred P] : ∀ n, (∀ x, x < n → ¬ P x) → natCount P n = 0
  | 0, _ => rfl
  | n + 1, h => by
    show natCount P n + (if P n then 1 else 0) = 0
    rw [natCount_eq_zero P n (fun x hx => h x (Nat.lt_succ_of_lt hx)), ite_eq_right (h n (Nat.lt_succ_self n))]

/-- Counting through an equivalent predicate. -/
theorem natCount_congr (P Q : Nat → Prop) [DecidablePred P] [DecidablePred Q] :
    ∀ n, (∀ x, x < n → (P x ↔ Q x)) → natCount P n = natCount Q n
  | 0, _ => rfl
  | n + 1, h => by
    show natCount P n + (if P n then 1 else 0) = natCount Q n + (if Q n then 1 else 0)
    rw [natCount_congr P Q n (fun x hx => h x (Nat.lt_succ_of_lt hx))]
    have e := h n (Nat.lt_succ_self n)
    match (inferInstance : Decidable (Q n)) with
    | isTrue hq => rw [ite_eq_left hq, ite_eq_left (e.2 hq)]
    | isFalse hq => rw [ite_eq_right hq, ite_eq_right (fun hp => hq (e.1 hp))]

end Frame
end Shell
end FRC
