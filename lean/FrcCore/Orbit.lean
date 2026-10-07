import FrcCore.Frame
import FrcCore.Parity

/-!
# FrcCore.Orbit — the generators form one orbit (2:B3; 1-algebra's torsor of primitive roots)

`Coprime u n` is taken in its invertible form — some `a < n` has `a·u ≡ 1 (mod n)` — which is decidable by
search and, for `n ≥ 1`, the same as `gcd(u, n) = 1` (Bezout); it is what every proof uses. Theorem:
`h` is primitive of order `n = p − 1` exactly when `h = g^u` with `u < n` coprime to `n`. No axioms.

Since the ledger migration (task LM17) it also holds the Klein orbits off the fourth roots of unity (from 1-algebra),
the octant character of `2` (from 14-entropy: `2` is a square exactly on the frames of even capacity) and the parity of
the drive (from 8-dirac: `g^m` is a square exactly when `m` is even); the parity is `Parity.lean` since task LM24.
-/

namespace FRC
namespace Shell

/-- `u` is invertible mod `n`: some `a < n` has `a·u % n = 1`. -/
def Coprime (u n : Nat) : Prop := ∃ a, a < n ∧ (a * u) % n = 1

instance (u n : Nat) : Decidable (Coprime u n) := decExistsLT (fun a => (a * u) % n = 1) n

namespace Frame
variable {p : Nat} [Pos p] {κ : Nat} {g : Shell p}

/-- A power of the drive with an invertible exponent is again primitive. -/
theorem primitive_pow_of_coprime (F : Frame p κ g) {u : Nat} (hu : Coprime u (p - 1)) :
    IsPrimitive (g ^ u) (p - 1) := by
  have hn := F.n_pos
  match hu with
  | ⟨a, _, ha⟩ =>
    refine ⟨by rw [pow_mul_comm, F.pow_n, one_pow], ?_⟩
    intro l hl hl0 hpow
    -- (g^u)^l = 1 gives (u·l) % n = 0; with a·u = n·q + 1, g^l = g^{l·a·u} = ((g^u)^l)^a = 1
    have h1 : (u * l) % (p - 1) = 0 := F.mod_eq_zero_of_pow_eq_one (by rw [pow_mul]; exact hpow)
    match FRC.Nat.mod_spec (p - 1) hn (a * u) with
    | ⟨q, hq⟩ =>
      rw [ha] at hq
      have e : l * (a * u) = (p - 1) * (q * l) + l := by
        rw [hq, Nat.left_distrib, Nat.mul_one, FRC.Nat.mul_left_comm, Nat.mul_comm l q]
      have h2 : g ^ (l * (a * u)) = 1 := by
        rw [show l * (a * u) = (u * l) * a by rw [Nat.mul_comm u l, FRC.Nat.mul_assoc, Nat.mul_comm a u]]
        rw [pow_mul, F.pow_eq_one_of_mod h1, one_pow]
      rw [e, pow_add, pow_mul, F.pow_n, one_pow, one_mul] at h2
      have := F.mod_eq_zero_of_pow_eq_one h2
      rw [FRC.Nat.mod_eq_of_lt hl] at this
      exact Nat.lt_irrefl 0 (this ▸ hl0)

/-- The frame of another primitive drive on the same shell. -/
theorem of_primitive (F : Frame p κ g) {h : Shell p} (hh : IsPrimitive h (p - 1)) : Frame p κ h :=
  ⟨F.cap, F.cap_pos, hh⟩

/-- 2:B3 (Props. 2.7, 4.5), 1-algebra's torsor — the primitive generators form one orbit: `h` is primitive
of order `p − 1` exactly when `h = g^u` for some `u < p − 1` coprime to `p − 1`. -/
theorem generator_orbit (F : Frame p κ g) (h : Shell p) :
    IsPrimitive h (p - 1) ↔ ∃ u, u < p - 1 ∧ Coprime u (p - 1) ∧ h = g ^ u := by
  have hn := F.n_pos
  constructor
  · intro hh
    have Fh : Frame p κ h := F.of_primitive hh
    have hh0 : h ≠ 0 := Fh.g_ne_zero
    match F.eq_pow_of_ne_zero hh0 with
    | ⟨u, hu, e⟩ =>
      refine ⟨u, hu, ?_, e.symm⟩
      -- g is a power of h: g = h^v; then g^{u v} = g, so u·v ≡ 1 (mod n)
      match Fh.eq_pow_of_ne_zero F.g_ne_zero with
      | ⟨v, hv, ev⟩ =>
        refine ⟨v, hv, ?_⟩
        have e1 : g ^ (v * u) = g ^ 1 := by
          rw [pow_one, Nat.mul_comm v u, pow_mul, e, ev]
        have h1n : 1 < p - 1 := by
          rw [F.n_eq]; exact Nat.lt_of_lt_of_le (by decide : 1 < 4 * 1) (Nat.mul_le_mul_left 4 F.cap_pos)
        have := F.pow_inj (Nat.mod_lt _ hn) h1n (by rw [← F.pow_mod, e1])
        exact this
  · intro ⟨u, _, hu, e⟩
    rw [e]; exact F.primitive_pow_of_coprime hu

/-- 1:E3, the finitary core (Fermat): every residue satisfies `x^p = x` — the polynomial `X^p − X` vanishes on
the whole shell, which is what the root test of 1:E3 rests on. -/
theorem fermat (F : Frame p κ g) (x : Shell p) : x ^ p = x := by
  have hp1 : x ^ p = x ^ (p - 1) * x :=
    congrArg (fun k => x ^ k) (FRC.Nat.sub_add_cancel Pos.pos).symm
  rw [hp1]
  exact match Shell.instDecidableEq x 0 with
    | isTrue e => by rw [e, mul_zero]
    | isFalse e => by
        match F.eq_pow_of_ne_zero e with
        | ⟨m, _, em⟩ => rw [← em, pow_mul_comm, F.pow_n, one_pow, one_mul]

/-! ## The Klein orbits off the fourth roots of unity (moved from 1-algebra, task LM17) -/

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

/-! ## The octant character of `2` (moved from 14-entropy, task LM17) -/

/-! ## The octant character on every framed shell of even capacity (14:C6, X4) -/


/-- Literals multiply as their values: `a · b = ab` on every shell. -/
theorem lit_mul (a b : Nat) : (OfNat.ofNat a : Shell p) * OfNat.ofNat b = (OfNat.ofNat (a * b) : Shell p) :=
  Shell.ext (by
    show (a % p * (b % p)) % p = (a * b) % p
    exact (FRC.Nat.mul_mod a b p Pos.pos).symm)

/-- `a + 1 + (1 − a) = 2` on every shell. -/
theorem add_one_add_one_neg (a : Shell p) : a + 1 + (1 + -a) = 2 := by
  rw [Shell.add_assoc, ← Shell.add_assoc 1 1 (-a), Shell.add_comm (1 + 1) (-a),
    ← Shell.add_assoc a (-a) (1 + 1), Shell.add_neg a, Shell.zero_add]
  exact Frame.two_eq_one_add_one.symm

/-- On a frame of capacity `κ = 2m`: `g^{4m} = −1` (the half-period) and `g^{8m} = 1`. -/
theorem even_capacity_powers (F : Frame p κ g) (m : Nat) (hm : κ = 2 * m) :
    g ^ (4 * m) = -1 ∧ g ^ (8 * m) = 1 := by
  have h4 : 4 * m = 2 * κ := by rw [hm, ← FRC.Nat.mul_assoc]
  have h8 : 8 * m = p - 1 := by rw [F.n_eq, hm, ← FRC.Nat.mul_assoc]
  exact ⟨by rw [h4]; exact F.half_period, by rw [h8]; exact F.pow_n⟩

/-- 14:C6 — the octant character: on every frame `(τ; 0, 1, g)` of even capacity `κ = 2m`, `ζ = g^m` has
`ζ⁴ = −1` and `ζ⁸ = 1` — the sector `C₈ ⊂ C_{4κ}` is realised and `ζ` is its residue `ζ₈`. -/
theorem octant_residue (F : Frame p κ g) (m : Nat) (hm : κ = 2 * m) :
    (g ^ m) ^ 4 = -1 ∧ (g ^ m) ^ 8 = 1 := by
  obtain ⟨h4, h8⟩ := even_capacity_powers F m hm
  constructor
  · rw [← Shell.pow_mul, Nat.mul_comm m 4]; exact h4
  · rw [← Shell.pow_mul, Nat.mul_comm m 8]; exact h8

/-- 14:C6, 14:X4 — the Tsirelson square: with `ζ = g^m` and `ζ' = g^{7m}` its inverse (`ζζ' = 1`),
`(ζ + ζ')² = 2` and `(2(ζ + ζ'))² = 8` on every frame of capacity `κ = 2m`; hence `2` is a square on every
such shell — the direction "octant ⇒ c-square" of X4's second face (the converse is
`even_capacity_of_two_square` below; the equivalence `two_is_square_iff`). -/
theorem tsirelson_square (F : Frame p κ g) (m : Nat) (hm : κ = 2 * m) :
    g ^ m * g ^ (7 * m) = 1 ∧ (g ^ m + g ^ (7 * m)) ^ 2 = 2 ∧
    (2 * (g ^ m + g ^ (7 * m))) ^ 2 = 8 := by
  obtain ⟨h4, h8⟩ := even_capacity_powers F m hm
  have hz : g ^ m * g ^ (7 * m) = 1 := by
    rw [← Shell.pow_add, show m + 7 * m = 8 * m by
      rw [Nat.mul_comm 8 m, Nat.mul_succ, Nat.mul_comm m 7, Nat.add_comm]]
    exact h8
  -- `ζ'² = −ζ²`: `g^{14m} = g^{8m} g^{4m} g^{2m} = (−1) g^{2m}`
  have h14 : 7 * m + 7 * m = 8 * m + (4 * m + (m + m)) := by
    calc 7 * m + 7 * m = (7 + 7) * m := (FRC.Nat.add_mul 7 7 m).symm
      _ = (8 + (4 + (1 + 1))) * m := rfl
      _ = 8 * m + (4 * m + (1 * m + 1 * m)) := by
        rw [FRC.Nat.add_mul, FRC.Nat.add_mul, FRC.Nat.add_mul]
      _ = 8 * m + (4 * m + (m + m)) := by rw [Nat.one_mul]
  have hz' : g ^ (7 * m) * g ^ (7 * m) = -(g ^ m * g ^ m) := by
    rw [← Shell.pow_add, h14, Shell.pow_add, Shell.pow_add, Shell.pow_add, h8, h4, Shell.one_mul,
      Shell.neg_one_mul]
  -- `(ζ + ζ')² = ζ² + ζζ' + ζ'ζ + ζ'² = ζ² + 1 + (1 − ζ²) = 2`
  have hsq : (g ^ m + g ^ (7 * m)) ^ 2 = 2 := by
    rw [Shell.pow_two, Shell.left_distrib, Shell.right_distrib, Shell.right_distrib, hz,
      Shell.mul_comm (g ^ (7 * m)) (g ^ m), hz, hz']
    exact add_one_add_one_neg _
  refine ⟨hz, hsq, ?_⟩
  rw [Shell.mul_pow, hsq, Shell.pow_two, lit_mul 2 2, lit_mul 4 2]

/-- 14:X4 — the direction "even capacity ⇒ `2` a square" at tier 0: on every frame of even capacity `2` is a
square, `(ζ + ζ⁻¹)² = 2`; the converse is `even_capacity_of_two_square`, the equivalence `two_is_square_iff`. -/
theorem two_is_square (F : Frame p κ g) (m : Nat) (hm : κ = 2 * m) : ∃ r : Shell p, r * r = 2 :=
  ⟨g ^ m + g ^ (7 * m), by rw [← Shell.pow_two]; exact (tsirelson_square F m hm).2.1⟩


/-! ## The converse: `2` a square ⇒ even capacity, on every frame (14:X4) -/


/-- Literals add as their values: `a + b = (a + b)` on every shell. -/
theorem lit_add (a b : Nat) : (OfNat.ofNat a : Shell p) + OfNat.ofNat b = (OfNat.ofNat (a + b) : Shell p) :=
  Shell.ext (by
    show (a % p + b % p) % p = (a + b) % p
    exact (FRC.Nat.add_mod a b p Pos.pos).symm)

/-- `−1 ≠ 1` on every frame (`2 ≠ 0`). -/
theorem neg_one_ne_one (F : Frame p κ g) : (-1 : Shell p) ≠ 1 := fun h => by
  have h2 : (1 : Shell p) + 1 = 0 := by
    have := Shell.neg_add (1 : Shell p); rw [h] at this; exact this
  exact F.two_ne_zero (by rw [Frame.two_eq_one_add_one]; exact h2)

/-- `−1 ≠ 0` on every frame. -/
theorem neg_one_ne_zero (F : Frame p κ g) : (-1 : Shell p) ≠ 0 := fun h => by
  have : (1 : Shell p) = 0 := by
    have h' : -(-1 : Shell p) = -0 := congrArg Neg.neg h
    rw [Shell.neg_neg, Shell.neg_zero] at h'
    exact h'
  exact F.one_ne_zero this

/-- A square root of `2` gives a square root of the quarter-turn: with `i² = −1`, `2h = 1` and `r² = 2`,
`ζ = (r + i r) h` has `ζ² = i`, hence `ζ⁴ = −1` and `ζ⁸ = 1` — an element of order eight wherever `−1 ≠ 1`,
that is on every frame. -/
theorem octant_of_two_square {r i h : Shell p} (hr : r * r = 2) (hi : i * i = -1)
    (hh : 2 * h = 1) :
    ∃ ζ : Shell p, ζ * ζ = i ∧ ζ ^ 4 = -1 ∧ ζ ^ 8 = 1 := by
  -- `(r + i r)² = 4 i`
  have hA : (r + i * r) * (r + i * r) = i * 4 := by
    rw [Shell.left_distrib, Shell.right_distrib, Shell.right_distrib, hr,
      Shell.mul_assoc i r r, hr, Shell.mul_left_comm r i r, hr,
      Shell.mul_assoc i r (i * r), Shell.mul_left_comm r i r, ← Shell.mul_assoc i i (r * r), hi, hr,
      Shell.neg_one_mul, Shell.add_comm 2 (i * 2), Shell.add_assoc, Shell.add_comm 2 (i * 2 + -2),
      Shell.add_assoc, Shell.neg_add, Shell.add_zero, ← Shell.left_distrib, lit_add 2 2]
  -- `4 h² = (2h)² = 1`
  have h4 : (4 : Shell p) * (h * h) = 1 := by
    rw [← lit_mul 2 2, ← mul_mul_mul_comm, hh, Shell.one_mul]
  have hz : ((r + i * r) * h) * ((r + i * r) * h) = i := by
    rw [mul_mul_mul_comm, hA, Shell.mul_assoc, h4, Shell.mul_one]
  refine ⟨(r + i * r) * h, hz, ?_, ?_⟩
  · rw [show (4 : Nat) = 2 * 2 from rfl, Shell.pow_mul, Shell.pow_two, Shell.pow_two, hz, hi]
  · rw [show (8 : Nat) = 2 * 2 * 2 from rfl, Shell.pow_mul, Shell.pow_mul, Shell.pow_two, Shell.pow_two,
      Shell.pow_two, hz, hi, Shell.neg_mul_neg, Shell.one_mul]

/-- The arithmetic of the order: `(k · 8) % 4κ = 0` and `(k · 4) % 4κ ≠ 0` force `κ` even (a divisor `4κ` of
`8k` that misses `4k` cannot be `4 · odd`; `0 < κ` is only what `mod_spec` needs). -/
theorem even_of_order_eight {κ k : Nat} (hκ : 0 < κ) (h8 : (k * 8) % (4 * κ) = 0)
    (h4 : (k * 4) % (4 * κ) ≠ 0) : ∃ m, κ = 2 * m := by
  have h4κ : 0 < 4 * κ := Nat.mul_pos (Nat.zero_lt_succ 3) hκ
  obtain ⟨q, hq⟩ := FRC.Nat.mod_spec (4 * κ) h4κ (k * 8)
  rw [h8, Nat.add_zero] at hq
  -- `2k = κ q`
  have h2k : 2 * k = κ * q := by
    apply Nat.eq_of_mul_eq_mul_left (Nat.zero_lt_succ 3)
    rw [← FRC.Nat.mul_assoc, ← FRC.Nat.mul_assoc, Nat.mul_comm 4 2, Nat.mul_comm (2 * 4) k, ← hq]
  have h2 : 0 < 2 := Nat.zero_lt_succ 1
  obtain ⟨m, hm⟩ := FRC.Nat.mod_spec 2 h2 κ
  have hlt : κ % 2 < 2 := FRC.Nat.mod_lt' κ h2
  match hκ2 : κ % 2 with
  | 0 => rw [hκ2, Nat.add_zero] at hm; exact ⟨m, hm⟩
  | 1 =>
    -- `κ` odd: `q` is even, `k = κ q'`, so `4κ ∣ 4k`, contradicting `h4`
    have hq2 : q % 2 = 0 := by
      have e1 : (κ * q) % 2 = q % 2 := by
        rw [FRC.Nat.mul_mod κ q 2 h2, hκ2, Nat.one_mul, FRC.Nat.mod_mod q 2 h2]
      have e2 : (2 * k) % 2 = 0 := by
        rw [Nat.mul_comm 2 k]
        exact (FRC.Nat.mod_unique (Nat.zero_lt_succ 1) (by rw [Nat.add_zero, Nat.mul_comm k 2]) : (k * 2) % 2 = 0)
      rw [← e1, ← h2k]; exact e2
    obtain ⟨q', hq'⟩ := FRC.Nat.mod_spec 2 h2 q
    rw [hq2, Nat.add_zero] at hq'
    have hk : k = κ * q' := by
      apply Nat.eq_of_mul_eq_mul_left h2
      rw [h2k, hq', Nat.mul_left_comm κ 2 q']
    exact absurd (FRC.Nat.mod_unique h4κ
      (by rw [hk, Nat.add_zero, Nat.mul_comm (κ * q') 4, ← FRC.Nat.mul_assoc])) h4
  | n + 2 => exact absurd hlt (by rw [hκ2]; exact Nat.not_lt_of_ge (Nat.le_add_left 2 n))

/-- 14:C6 — the octant forces even capacity: on every frame, an element `ζ` with `ζ⁴ = −1` and `ζ⁸ = 1` (an
element of order eight) gives `8 ∣ 4κ`, so the capacity is even. -/
theorem even_capacity_of_octant (F : Frame p κ g) {ζ : Shell p} (hz4 : ζ ^ 4 = -1) (hz8 : ζ ^ 8 = 1) :
    ∃ m, κ = 2 * m := by
  have hζ0 : ζ ≠ 0 := fun h0 => by
    rw [h0, show (4 : Nat) = 3 + 1 from rfl, Shell.pow_succ, Shell.mul_zero] at hz4
    exact neg_one_ne_zero F hz4.symm
  obtain ⟨k, hk, hgk⟩ := F.eq_pow_of_ne_zero hζ0
  have e8 : (k * 8) % (p - 1) = 0 :=
    F.mod_eq_zero_of_pow_eq_one (by rw [Shell.pow_mul, hgk]; exact hz8)
  have e4 : (k * 4) % (p - 1) ≠ 0 := fun e => by
    have := F.pow_eq_one_of_mod e
    rw [Shell.pow_mul, hgk, hz4] at this
    exact neg_one_ne_one F this
  rw [F.n_eq] at e8 e4
  exact even_of_order_eight F.cap_pos e8 e4

/-- 14:C6 — the octant sector at tier 0, as an equivalence: on every frame, an element with `ζ⁴ = −1` and
`ζ⁸ = 1` exists exactly when the capacity is even. -/
theorem octant_iff (F : Frame p κ g) : (∃ ζ : Shell p, ζ ^ 4 = -1 ∧ ζ ^ 8 = 1) ↔ ∃ m, κ = 2 * m :=
  ⟨fun ⟨_, h4, h8⟩ => even_capacity_of_octant F h4 h8,
   fun ⟨m, hm⟩ => ⟨g ^ m, octant_residue F m hm⟩⟩

/-- 14:X4 — the converse of the second face at tier 0: on every frame, a square root of `2` forces the
capacity even — `ζ = (r + i r)/2` has `ζ² = i`, so an element of order eight exists and `8 ∣ 4κ`. -/
theorem even_capacity_of_two_square (F : Frame p κ g) {r : Shell p} (hr : r * r = 2) :
    ∃ m, κ = 2 * m := by
  obtain ⟨h, hh⟩ := F.exists_inv F.two_ne_zero
  obtain ⟨ζ, _, hz4, hz8⟩ := octant_of_two_square hr F.quarter_turn_sq hh
  exact even_capacity_of_octant F hz4 hz8

/-- 14:X4 — the second face as an equivalence at tier 0: on every frame `(τ; 0, 1, g)`, `2` is a square
exactly when the capacity is even — the c-square congruence and the octant sector are one condition. -/
theorem two_is_square_iff (F : Frame p κ g) : (∃ r : Shell p, r * r = 2) ↔ ∃ m, κ = 2 * m :=
  ⟨fun ⟨_, hr⟩ => even_capacity_of_two_square F hr, fun ⟨m, hm⟩ => two_is_square F m hm⟩


end Frame
end Shell
end FRC
