import FrcCore.Theme.Fractional

/-!
# FrcCore.Theme.Lifts — exponent lifts, charts and the normalization constant (the fourier theme)

The third file of the fourier theme (6-fourier's blueprint of 8 October 2026, task T04). The exponent lifts
`U^{(a)}_s = Σ_ℓ z^{a_ℓ s} Π_ℓ` of the fractional family are additive for every choice of exponents, by the projector
algebra of `Theme/Fractional.lean`, and have the family's cardinal skeleton when `a_ℓ ≡ ℓ (mod 4)` (6:C8). The chart
`g^u` has the Fourier matrix `W(g^u) = W P_u` (the index relabelling `j ↦ uj`), `W · W(g^u) = −J P_u` and
`W(g^u) · W = −J P_{u⁻¹}` by the geometric sum, so the two do not commute when `u² ≢ 1 (mod 4κ)` (6:C11); the chart
`g^{u²}` of an odd `u` is the coordinate relabelling `m ↦ um` of `F` (6:C6), and the frames `g = 2, 6` of `p = 13`
carry the two multiplicity tuples, read as traces by the kernel. The normalization: the square roots of `−1 = 1/n`
in the field are exactly `±i`, and `(cW)² = J` exactly when `c = ±i` (6:B6). No axioms.
-/

namespace FRC
namespace Shell
namespace Frame

variable {p : Nat} [Pos p]

/-! ## Ring identities (generated; `RE.sound`, decided by the kernel) -/

theorem mul_lift_id (X d0 d1 d2 d3 P0 P1 P2 P3 : Shell p) :
    X * (d0 * P0 + d1 * P1 + d2 * P2 + d3 * P3) = d0 * (X * P0) + d1 * (X * P1) + d2 * (X * P2) + d3 * (X * P3) :=
  RE.sound (look [X, d0, d1, d2, d3, P0, P1, P2, P3])
    (.mul (.var 0) (.add (.add (.add (.mul (.var 1) (.var 5)) (.mul (.var 2) (.var 6))) (.mul (.var 3) (.var 7))) (.mul (.var 4) (.var 8))))
    (.add (.add (.add (.mul (.var 1) (.mul (.var 0) (.var 5))) (.mul (.var 2) (.mul (.var 0) (.var 6)))) (.mul (.var 3) (.mul (.var 0) (.var 7)))) (.mul (.var 4) (.mul (.var 0) (.var 8)))) (by decide +kernel)

theorem lift_add_id (c0 c1 c2 c3 d0 d1 d2 d3 P0 P1 P2 P3 : Shell p) :
    d0 * (c0 * P0) + d1 * (c1 * P1) + d2 * (c2 * P2) + d3 * (c3 * P3) = (c0 * d0) * P0 + (c1 * d1) * P1 + (c2 * d2) * P2 + (c3 * d3) * P3 :=
  RE.sound (look [c0, c1, c2, c3, d0, d1, d2, d3, P0, P1, P2, P3])
    (.add (.add (.add (.mul (.var 4) (.mul (.var 0) (.var 8))) (.mul (.var 5) (.mul (.var 1) (.var 9)))) (.mul (.var 6) (.mul (.var 2) (.var 10)))) (.mul (.var 7) (.mul (.var 3) (.var 11))))
    (.add (.add (.add (.mul (.mul (.var 0) (.var 4)) (.var 8)) (.mul (.mul (.var 1) (.var 5)) (.var 9))) (.mul (.mul (.var 2) (.var 6)) (.var 10))) (.mul (.mul (.var 3) (.var 7)) (.var 11))) (by decide +kernel)

theorem scaled_id (c a b : Shell p) :
    (c * a) * (c * b) = (c * c) * (a * b) :=
  RE.sound (look [c, a, b])
    (.mul (.mul (.var 0) (.var 1)) (.mul (.var 0) (.var 2)))
    (.mul (.mul (.var 0) (.var 0)) (.mul (.var 1) (.var 2))) (by decide +kernel)

theorem diff_sq_id (x i : Shell p) :
    (x + -i) * (x + i) = x * x + -(i * i) :=
  RE.sound (look [x, i])
    (.mul (.add (.var 0) (.neg (.var 1))) (.add (.var 0) (.var 1)))
    (.add (.mul (.var 0) (.var 0)) (.neg (.mul (.var 1) (.var 1)))) (by decide +kernel)

variable {κ : Nat} {g : Shell p}

/-- A fourth root of unity's powers repeat with period 4. -/
theorem pow_four_mod {x : Shell p} (hx : x ^ 4 = 1) (l : Nat) : x ^ l = x ^ (l % 4) := by
  obtain ⟨m, hm⟩ := FRC.Nat.mod_spec 4 (by decide) l
  rw [congrArg (fun e => x ^ e) hm, pow_add, pow_mul, hx, one_pow, one_mul]

theorem quarter_four (F : Frame p κ g) : quarterTurn g κ ^ 4 = 1 := by
  rw [show (4 : Nat) = 2 * 2 from rfl, pow_mul, pow_two, pow_two, F.quarter_turn_sq, neg_mul_neg, one_mul]

/-- The selection of the `m`-th term of a four-term sum with `[ℓ = m]` factors, `m < 4`. -/
theorem four_select (c P : Nat → Shell p) : ∀ {m : Nat}, m < 4 →
    c 0 * (if 0 = m then P 0 else 0) + c 1 * (if 1 = m then P 1 else 0) + c 2 * (if 2 = m then P 2 else 0) +
      c 3 * (if 3 = m then P 3 else 0) = c m * P m
  | 0, _ => by
    rw [ite_eq_left rfl, ite_eq_right (by decide), ite_eq_right (by decide), ite_eq_right (by decide), mul_zero, mul_zero,
      mul_zero, add_zero, add_zero, add_zero]
  | 1, _ => by
    rw [ite_eq_right (by decide), ite_eq_left rfl, ite_eq_right (by decide), ite_eq_right (by decide), mul_zero, mul_zero,
      mul_zero, zero_add, add_zero, add_zero]
  | 2, _ => by
    rw [ite_eq_right (by decide), ite_eq_right (by decide), ite_eq_left rfl, ite_eq_right (by decide), mul_zero, mul_zero,
      mul_zero, zero_add, zero_add, add_zero]
  | 3, _ => by
    rw [ite_eq_right (by decide), ite_eq_right (by decide), ite_eq_right (by decide), ite_eq_left rfl, mul_zero, mul_zero,
      mul_zero, zero_add, zero_add, zero_add]
  | n + 4, h => absurd (Nat.lt_of_lt_of_le h (Nat.le_add_left 4 n)) (Nat.lt_irrefl _)

/-! ## Exponent lifts (6:C8) -/

/-- The lift `U^{(a)}_s = Σ_ℓ z^{a_ℓ s} Π_ℓ` of the family by the exponents `a`; the family itself is `a = id`. -/
def lift (g : Shell p) (κ : Nat) (z : Shell p) (a : Nat → Nat) (s : Nat) (k j : Nat) : Shell p :=
  (z ^ s) ^ a 0 * proj g κ 0 k j + (z ^ s) ^ a 1 * proj g κ 1 k j + (z ^ s) ^ a 2 * proj g κ 2 k j +
    (z ^ s) ^ a 3 * proj g κ 3 k j

theorem lift_mul_pt (z : Shell p) (a : Nat → Nat) (s m k j l : Nat) :
    lift g κ z a s k l * proj g κ m l j =
      (z ^ s) ^ a 0 * (proj g κ 0 k l * proj g κ m l j) + (z ^ s) ^ a 1 * (proj g κ 1 k l * proj g κ m l j) +
      (z ^ s) ^ a 2 * (proj g κ 2 k l * proj g κ m l j) + (z ^ s) ^ a 3 * (proj g κ 3 k l * proj g κ m l j) :=
  frft_mul_id _ _ _ _ _ _ _ _ _

/-- The lift acts on `Π_m` by `z^{a_m s}`. -/
theorem lift_proj (F : Frame p κ g) (z : Shell p) (a : Nat → Nat) (s : Nat) {m : Nat} (hm : m < 4) {k j : Nat}
    (hk : k < p - 1) (hj : j < p - 1) :
    sumRange (fun l => lift g κ z a s k l * proj g κ m l j) (p - 1) = (z ^ s) ^ a m * proj g κ m k j := by
  rw [sum_congr _ (fun l _ => lift_mul_pt z a s m k j l), sum_add, sum_add, sum_add, sum_mul_left, sum_mul_left,
    sum_mul_left, sum_mul_left, proj_mul F (Nat.zero_lt_succ 3) hm hk hj, proj_mul F (by decide : (1 : Nat) < 4) hm hk hj,
    proj_mul F (by decide : (2 : Nat) < 4) hm hk hj, proj_mul F (by decide : (3 : Nat) < 4) hm hk hj]
  exact four_select (fun ℓ => (z ^ s) ^ a ℓ) (fun ℓ => proj g κ ℓ k j) hm

theorem lift_mul_lift_pt (z : Shell p) (a : Nat → Nat) (s r k j l : Nat) :
    lift g κ z a s k l * lift g κ z a r l j =
      (z ^ r) ^ a 0 * (lift g κ z a s k l * proj g κ 0 l j) + (z ^ r) ^ a 1 * (lift g κ z a s k l * proj g κ 1 l j) +
      (z ^ r) ^ a 2 * (lift g κ z a s k l * proj g κ 2 l j) + (z ^ r) ^ a 3 * (lift g κ z a s k l * proj g κ 3 l j) :=
  mul_lift_id _ _ _ _ _ _ _ _ _

/-- 6:C8, every lift is additive: `U^{(a)}_{s+r} = U^{(a)}_s U^{(a)}_r`, by the projector algebra alone. -/
theorem lift_add (F : Frame p κ g) (z : Shell p) (a : Nat → Nat) (s r : Nat) {k j : Nat} (hk : k < p - 1)
    (hj : j < p - 1) :
    sumRange (fun l => lift g κ z a s k l * lift g κ z a r l j) (p - 1) = lift g κ z a (s + r) k j := by
  rw [sum_congr _ (fun l _ => lift_mul_lift_pt z a s r k j l), sum_add, sum_add, sum_add, sum_mul_left, sum_mul_left, sum_mul_left, sum_mul_left,
    lift_proj F z a s (Nat.zero_lt_succ 3) hk hj, lift_proj F z a s (by decide : (1 : Nat) < 4) hk hj,
    lift_proj F z a s (by decide : (2 : Nat) < 4) hk hj, lift_proj F z a s (by decide : (3 : Nat) < 4) hk hj]
  show _ = (z ^ (s + r)) ^ a 0 * proj g κ 0 k j + (z ^ (s + r)) ^ a 1 * proj g κ 1 k j +
    (z ^ (s + r)) ^ a 2 * proj g κ 2 k j + (z ^ (s + r)) ^ a 3 * proj g κ 3 k j
  rw [pow_add, mul_pow, mul_pow, mul_pow, mul_pow]
  exact lift_add_id _ _ _ _ _ _ _ _ _ _ _ _

/-- 6:C8, the cardinal skeleton: with `a_ℓ ≡ ℓ (mod 4)` the lift agrees with the family at the multiples of `κ`,
`U^{(a)}_{mκ} = F^{[mκ]} = F^m` (`frft_pow`, `frft_cardinal`), since `z^{mκ} = i^m` is a fourth root of unity. -/
theorem lift_cardinal (F : Frame p κ g) {z : Shell p} (hz : g * z = 1) (a : Nat → Nat)
    (ha : ∀ ℓ, ℓ < 4 → a ℓ % 4 = ℓ) (m k j : Nat) : lift g κ z a (m * κ) k j = frft g κ z (m * κ) k j := by
  have hx : (z ^ (m * κ)) ^ 4 = 1 := by
    rw [Nat.mul_comm, pow_mul, inv_pow_kappa F hz, pow_mul_comm, quarter_four F, one_pow]
  show (z ^ (m * κ)) ^ a 0 * proj g κ 0 k j + (z ^ (m * κ)) ^ a 1 * proj g κ 1 k j +
      (z ^ (m * κ)) ^ a 2 * proj g κ 2 k j + (z ^ (m * κ)) ^ a 3 * proj g κ 3 k j =
    (z ^ (m * κ)) ^ 0 * proj g κ 0 k j + (z ^ (m * κ)) ^ 1 * proj g κ 1 k j +
      (z ^ (m * κ)) ^ 2 * proj g κ 2 k j + (z ^ (m * κ)) ^ 3 * proj g κ 3 k j
  rw [pow_four_mod hx (a 0), pow_four_mod hx (a 1), pow_four_mod hx (a 2), pow_four_mod hx (a 3),
    ha 0 (by decide), ha 1 (by decide), ha 2 (by decide), ha 3 (by decide)]

/-- 6:C8, the lift at the multiples of `κ` is the power of the transform: `U^{(a)}_{mκ} = F^m`. -/
theorem lift_pow (F : Frame p κ g) {z : Shell p} (hz : g * z = 1) (a : Nat → Nat) (ha : ∀ ℓ, ℓ < 4 → a ℓ % 4 = ℓ)
    (m : Nat) {k j : Nat} (hk : k < p - 1) (hj : j < p - 1) : lift g κ z a (m * κ) k j = mpow (Fmat g κ) m k j := by
  rw [lift_cardinal F hz a ha m k j, frft_pow F hz κ m k j hk hj]
  exact mpow_congr (fun k j hk hj => (frft_cardinal F hz k j).2.1) m k j hk hj
where
  mpow_congr {A B : Nat → Nat → Shell p} (e : ∀ k j, k < p - 1 → j < p - 1 → A k j = B k j) :
      ∀ m k j, k < p - 1 → j < p - 1 → mpow A m k j = mpow B m k j
    | 0, _, _, _, _ => rfl
    | m + 1, k, j, hk, hj => by
      show sumRange (fun l => mpow A m k l * A l j) (p - 1) = sumRange (fun l => mpow B m k l * B l j) (p - 1)
      exact sum_congr _ (fun l hl => by rw [mpow_congr e m k l hk hl, e l j hl hj])

/-! ## Charts: the relabelling `j ↦ uj` (6:C11, 6:C6) -/

/-- 6:C11, the chart's Fourier matrix is the relabelled one: `W(g^u)_{kj} = W(g)_{k, uj}`, the index read mod `n`
(`W(g^u) = W P_u`). -/
theorem W_chart (F : Frame p κ g) (u k j : Nat) : W (g ^ u) k j = W g k ((u * j) % (p - 1)) := by
  show (g ^ u) ^ (j * k) = g ^ ((u * j) % (p - 1) * k)
  rw [← pow_mul, F.pow_mod (u * (j * k)), F.pow_mod ((u * j) % (p - 1) * k), FRC.Nat.mod_mul_mod _ _ _ F.n_pos,
    Nat.mul_assoc]

/-- 6:C11, `W · W(g^u) = −J P_u`: entrywise `−[k + uj ≡ 0 (mod n)]`, by the geometric sum. -/
theorem W_mul_chart (F : Frame p κ g) (u k j : Nat) :
    sumRange (fun l => W g k l * W (g ^ u) l j) (p - 1) = -(if (k + u * j) % (p - 1) = 0 then 1 else 0) := by
  rw [sum_congr _ (fun l _ => by
    show g ^ (l * k) * (g ^ u) ^ (j * l) = g ^ (l * k) * g ^ (u * j * l)
    rw [← pow_mul, ← Nat.mul_assoc])]
  exact F.W_sq k (u * j)

/-- 6:C11, `W(g^u) · W = −J P_{u⁻¹}` for `u` a unit mod `4κ`: entrywise `−[uk + j ≡ 0 (mod n)]`, for every `u`. -/
theorem chart_mul_W (F : Frame p κ g) (u k j : Nat) :
    sumRange (fun l => W (g ^ u) k l * W g l j) (p - 1) = -(if (u * k + j) % (p - 1) = 0 then 1 else 0) := by
  rw [sum_congr _ (fun l _ => by
    show (g ^ u) ^ (l * k) * g ^ (j * l) = g ^ (l * (u * k)) * g ^ (j * l)
    rw [← pow_mul, Nat.mul_left_comm])]
  exact F.W_sq (u * k) j

theorem one_lt_n (F : Frame p κ g) : 1 < p - 1 := by
  rw [F.n_eq]; exact Nat.lt_of_lt_of_le (by decide) (Nat.mul_le_mul_left 4 F.cap_pos)

theorem minus_one_ne_zero (F : Frame p κ g) : (-1 : Shell p) ≠ 0 := fun h =>
  F.one_ne_zero (by rw [← neg_neg (1 : Shell p), h, neg_zero])

/-- 6:C11, the non-commutation: when `u² ≢ 1 (mod n)` the entry `(−u, 1)` of `W · W(g^u)` is `−1` and that of
`W(g^u) · W` is `0`, so the chart `g^u` does not commute with the frame's `W`. -/
theorem chart_noncommute (F : Frame p κ g) {u : Nat} (hu : (u * u) % (p - 1) ≠ 1) :
    sumRange (fun l => W g (rev (p - 1) (u % (p - 1))) l * W (g ^ u) l 1) (p - 1) ≠
      sumRange (fun l => W (g ^ u) (rev (p - 1) (u % (p - 1))) l * W g l 1) (p - 1) := by
  have hn := F.n_pos
  have hr : u % (p - 1) < p - 1 := FRC.Nat.mod_lt' u hn
  rw [W_mul_chart F, chart_mul_W F]
  have e1 : (rev (p - 1) (u % (p - 1)) + u * 1) % (p - 1) = 0 := by
    rw [Nat.mul_one, ← FRC.Nat.add_mod_mod _ _ _ hn, rev_add_mod hr]
  have e2 : (u * rev (p - 1) (u % (p - 1)) + 1) % (p - 1) ≠ 0 := fun h => hu (by
    have hsum : (u * rev (p - 1) (u % (p - 1)) + 1 + u * (u % (p - 1))) % (p - 1) = 1 := by
      rw [Nat.add_right_comm, ← Nat.mul_add, ← FRC.Nat.mod_add_mod _ _ _ hn, ← FRC.Nat.mul_mod_mod _ _ _ hn,
        rev_add_mod hr, Nat.mul_zero, FRC.Nat.zero_mod, Nat.zero_add, FRC.Nat.mod_eq_of_lt (one_lt_n F)]
    rw [← FRC.Nat.mod_add_mod _ _ _ hn, h, Nat.zero_add, FRC.Nat.mul_mod_mod _ _ _ hn] at hsum
    exact hsum)
  rw [ite_eq_left e1, ite_eq_right e2, neg_zero]
  exact minus_one_ne_zero F

/-- An odd `u` has `u² ≡ 1 (mod 4)`. -/
theorem odd_sq_mod_four {u : Nat} (hu : u % 2 = 1) : (u * u) % 4 = 1 := by
  obtain ⟨m, hm⟩ := FRC.Nat.mod_spec 2 (by decide) u
  rw [hu] at hm
  apply FRC.Nat.mod_unique (by decide : 1 < 4) (q := m * m + m)
  rw [hm, Nat.mul_add, Nat.add_mul, Nat.add_mul, Nat.mul_one, Nat.one_mul, Nat.mul_add, Nat.mul_assoc 2 m,
    Nat.mul_left_comm m 2 m, ← Nat.mul_assoc 2 2, ← Nat.add_assoc, Nat.add_assoc (2 * 2 * (m * m)), ← Nat.two_mul,
    ← Nat.mul_assoc 2 2]

/-- 6:C6, the chart `g^{u²}` of an odd `u` is the coordinate relabelling `m ↦ um`: `F(g^{u²})_{kj} = F(g)_{uk, uj}`,
the indices read mod `n`; the quarter-turn is unchanged since `u² ≡ 1 (mod 4)`. -/
theorem Fmat_chart (F : Frame p κ g) {u : Nat} (hu : u % 2 = 1) (k j : Nat) :
    Fmat (g ^ (u * u)) κ k j = Fmat g κ ((u * k) % (p - 1)) ((u * j) % (p - 1)) := by
  have hn := F.n_pos
  have hq : quarterTurn (g ^ (u * u)) κ = quarterTurn g κ := by
    show -((g ^ (u * u)) ^ κ) = -(g ^ κ)
    rw [pow_mul_comm, pow_four_mod F.quarter_turn_order.2 (u * u), odd_sq_mod_four hu, pow_one]
  show quarterTurn (g ^ (u * u)) κ * (g ^ (u * u)) ^ (j * k) =
    quarterTurn g κ * g ^ ((u * j) % (p - 1) * ((u * k) % (p - 1)))
  rw [hq, ← pow_mul, F.pow_mod (u * u * (j * k)), F.pow_mod ((u * j) % (p - 1) * ((u * k) % (p - 1))),
    FRC.Nat.mod_mul_mod _ _ _ hn, FRC.Nat.mul_mod_mod _ _ _ hn, Nat.mul_assoc u u, Nat.mul_left_comm u j k,
    Nat.mul_assoc u j]

/-- The trace on the cycle. -/
def trace (A : Nat → Nat → Shell p) (n : Nat) : Shell p := sumRange (fun k => A k k) n

theorem frame13_six : Frame 13 3 (6 : Shell 13) := ⟨rfl, Nat.zero_lt_succ 2, by decide⟩

/-- 6:C6, the two frames `g = 2` and `g = 6` of `p = 13`: the traces of the projectors read `(3, 3, 4, 2)` and
`(4, 2, 3, 3)`, the multiplicity tuples, and `Tr F = 4, 9`. -/
theorem thirteen_tuples :
    trace (proj (2 : Shell 13) 3 0) 12 = 3 ∧ trace (proj (2 : Shell 13) 3 1) 12 = 3 ∧
    trace (proj (2 : Shell 13) 3 2) 12 = 4 ∧ trace (proj (2 : Shell 13) 3 3) 12 = 2 ∧
    trace (proj (6 : Shell 13) 3 0) 12 = 4 ∧ trace (proj (6 : Shell 13) 3 1) 12 = 2 ∧
    trace (proj (6 : Shell 13) 3 2) 12 = 3 ∧ trace (proj (6 : Shell 13) 3 3) 12 = 3 ∧
    trace (Fmat (2 : Shell 13) 3) 12 = 4 ∧ trace (Fmat (6 : Shell 13) 3) 12 = 9 := by decide +kernel

/-! ## The normalization constant (6:B6) -/

/-- 6:B6, the square roots of `−1 = 1/n` in the field are exactly `±i`. -/
theorem sqrt_neg_one (F : Frame p κ g) (x : Shell p) :
    x * x = -1 ↔ x = quarterTurn g κ ∨ x = -(quarterTurn g κ) := by
  constructor
  · intro h
    have e : (x + -(quarterTurn g κ)) * (x + quarterTurn g κ) = 0 := by
      rw [diff_sq_id, h, F.quarter_turn_sq, neg_neg, neg_add]
    match F.mul_eq_zero e with
    | Or.inl e1 => exact Or.inl (by rw [← neg_neg (quarterTurn g κ)]; exact eq_neg_of_add_eq_zero e1)
    | Or.inr e2 => exact Or.inr (eq_neg_of_add_eq_zero e2)
  · intro h
    match h with
    | Or.inl e => rw [e]; exact F.quarter_turn_sq
    | Or.inr e => rw [e, neg_mul_neg]; exact F.quarter_turn_sq

/-- 6:B6, `(c W)² = J` exactly when `c = ±i`: `(cW)² = c² W² = −c² J`. -/
theorem scaled_W_sq_iff (F : Frame p κ g) (c : Shell p) :
    (∀ k j, k < p - 1 → j < p - 1 → sumRange (fun l => c * W g k l * (c * W g l j)) (p - 1) = J (p - 1) k j) ↔
      (c = quarterTurn g κ ∨ c = -(quarterTurn g κ)) := by
  have key : ∀ k j, sumRange (fun l => c * W g k l * (c * W g l j)) (p - 1) = c * c * -(J (p - 1) k j) :=
    fun k j => by rw [sum_congr _ (fun l _ => scaled_id c (W g k l) (W g l j)), sum_mul_left, F.W_sq' k j]
  constructor
  · intro h
    have h00 := h 0 0 F.n_pos F.n_pos
    rw [key, J_zero_zero, ← mul_neg, mul_one] at h00
    exact (sqrt_neg_one F c).1 (by rw [← neg_neg (c * c), h00])
  · intro h k j _ _
    rw [key, (sqrt_neg_one F c).2 h, neg_mul_neg, one_mul]

end Frame
end Shell
end FRC
