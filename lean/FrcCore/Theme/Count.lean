import FrcCore.Theme.Zeros

/-!
# FrcCore.Theme.Count — the count readout of a shell (20-rh's revision, 21 November 2026)

The modes of a shell are the powers `x ↦ x^k` on the nonzero residues, `k = 0, …, p − 2`. The count of a mode is `k`.
For a count `k ≥ 1` the zero is `k + 1` and the conjugate count is `p − 1 − k`. Because `p − 1 ≡ −1`, such a count and its
conjugate add to `−1`, the count operator `N·x^k = k·x^k` has the adjoint `−1 − N` on the nonconstant modes, and `N + c` is skew
exactly for `2c = 1`. With the Subject's quarter-turn `i`, the frequency of the count `k` is `γ_k = −i(k + ½)` and
`½ + iγ_k = k + 1`, the zero of a count `k ≥ 1`. The statements that use no generator (the count, the zero, the pair invariant, the
cardinal zeros, the centre) take no frame, and so hold on a Carrier's chart as on a Subject. No axioms.
-/

namespace FRC.Horizon

open FRC.Shell FRC.Shell.Frame

variable {p : Nat} [Pos p] {κ : Nat} {g : Shell p}

section count20261121

/-! ## Residues of counts -/

/-- The successor of a count on the shell. -/
theorem count_succ (n : Nat) : (ofNat (n + 1) : Shell p) = ofNat n + 1 :=
  (ofNat_add n 1).symm

/-- `p − 1 ≡ −1`: the top count and one add to zero. -/
theorem count_top : (ofNat (p - 1) : Shell p) + 1 = 0 := by
  have h : (ofNat (p - 1) : Shell p) + ofNat 1 = ofNat (p - 1 + 1) := ofNat_add _ _
  have e : p - 1 + 1 = p := FRC.Nat.sub_add_cancel Pos.pos
  rw [e, ofNat_self] at h
  exact h

/-- A multiple of `p` is zero on the shell. -/
theorem count_add_mul_self (n m : Nat) : (ofNat (n + m * p) : Shell p) = ofNat n := by
  rw [← ofNat_add, ← ofNat_mul, ofNat_self, mul_zero, add_zero]

/-- Two counts that add to `p − 1` add to `−1` on the shell. -/
theorem count_pair {k k' : Nat} (h : k + k' = p - 1) : (ofNat k : Shell p) + ofNat k' + 1 = 0 := by
  rw [ofNat_add, h]; exact count_top

theorem count_pair_neg {k k' : Nat} (h : k + k' = p - 1) : (ofNat k : Shell p) + ofNat k' = -1 :=
  eq_neg_of_add_eq_zero (count_pair h)

/-- A common shift `c` of a conjugate pair: the two shifted counts add to `2c − 1`. -/
theorem count_pair_shift {k k' : Nat} (h : k + k' = p - 1) (c : Shell p) :
    ((ofNat k : Shell p) + c) + (ofNat k' + c) = -1 + (2 : Shell p) * c := by
  rw [add_add_add_comm, count_pair_neg h, two_mul']

theorem eq_add_neg_of_add_eq {a b c : Shell p} (h : a + b = c) : b = c + -a := by
  calc b = 0 + b := (zero_add b).symm
    _ = (-a + a) + b := by rw [neg_add]
    _ = -a + (a + b) := add_assoc _ _ _
    _ = -a + c := by rw [h]
    _ = c + -a := add_comm _ _

omit [Pos p] in
/-- `a + 1 < p` gives `a < p − 1`, and conversely. -/
theorem lt_pred_of_succ_lt {a : Nat} (h : a + 1 < p) : a < p - 1 := FRC.Nat.le_sub_of_add_le h

theorem succ_lt_of_lt_pred {a : Nat} (h : a < p - 1) : a + 1 < p := by
  have e : p - 1 + 1 = p := FRC.Nat.sub_add_cancel Pos.pos
  have h2 : a + 1 < p - 1 + 1 := Nat.add_lt_add_right h 1
  rw [e] at h2
  exact h2

/-- A nonzero label is a nonzero residue. -/
theorem count_ne_zero {l : Nat} (hl : l + 1 < p) : (ofNat (l + 1) : Shell p) ≠ 0 := fun h => by
  have := val_injective h
  rw [val_ofNat, val_zero, FRC.Nat.mod_eq_of_lt hl] at this
  exact Nat.noConfusion this

/-- Every nonzero residue has the period `p − 1`. -/
theorem unit_pow_card (F : Frame p κ g) {x : Shell p} (hx : x ≠ 0) : x ^ (p - 1) = 1 := by
  match F.eq_pow_of_ne_zero hx with
  | ⟨t, _, e⟩ => rw [← e, pow_mul_comm, F.pow_n, one_pow]

/-! ## The modes read the latitude `L_1` at every `k`-th step -/

/-- 20:E15 — at `x = g^m` the mode of count `k` reads `g^{km}`: the latitude `L_1` read at every `k`-th step. -/
theorem mode_stride (g : Shell p) (m k : Nat) : (g ^ m) ^ k = (g ^ k) ^ m ∧ (g ^ m) ^ k = g ^ (k * m) := by
  refine ⟨pow_mul_comm g m k, ?_⟩
  rw [← pow_mul, Nat.mul_comm]

/-! ## The generator: the conjugate count, the adjoint, the half, the runs of counts -/

/-- 20:G2, 20:G12 — the conjugate of a count `1 ≤ k ≤ p − 2` is `p − 1 − k`, again in `1, …, p − 2`, and the two counts add
to `−1`: `k + (p − 1 − k) + 1 ≡ 0`. No generator. -/
theorem count_conjugate {k : Nat} (hk0 : 0 < k) (hk : k < p - 1) :
    (0 < p - 1 - k ∧ p - 1 - k < p - 1) ∧ (ofNat k : Shell p) + ofNat (p - 1 - k) + 1 = 0 :=
  ⟨⟨FRC.Nat.le_sub_of_add_le (by rw [Nat.add_comm]; exact hk), Nat.sub_lt (Nat.lt_trans hk0 hk) hk0⟩,
   count_pair (FRC.Nat.add_sub_of_le (Nat.le_of_lt hk))⟩

/-- 20:G2 — the count operator on the nonconstant modes: `⟨N x^k, x^m⟩ + ⟨x^k, N x^m⟩ = −⟨x^k, x^m⟩`, in the
form `(k + m + 1)·Σ_{x≠0} x^k·x^m = 0` for `1 ≤ k, m ≤ p − 2`. So the adjoint of `N` is `−1 − N` there. -/
theorem count_adjoint (F : Frame p κ g) {k m : Nat} (hk0 : 0 < k) (hk : k < p - 1) (hm : m < p - 1) :
    ((ofNat k : Shell p) + ofNat m + 1) *
      sumRange (fun l => (ofNat (l + 1) : Shell p) ^ k * (ofNat (l + 1) : Shell p) ^ m) (p - 1) = 0 := by
  have hs : sumRange (fun l => (ofNat (l + 1) : Shell p) ^ k * (ofNat (l + 1) : Shell p) ^ m) (p - 1)
      = sumRange (fun l => (ofNat (l + 1) : Shell p) ^ (k + m)) (p - 1) :=
    sum_congr (p - 1) (fun l _ => (pow_add _ k m).symm)
  rw [hs]
  have hkm0 : 0 < k + m := Nat.lt_of_lt_of_le hk0 (Nat.le_add_right k m)
  match Nat.lt_trichotomy (k + m) (p - 1) with
  | .inl h => rw [(zero_slot F).1 (k + m) hkm0 h, mul_zero]
  | .inr (.inl h) => rw [count_pair h, zero_mul]
  | .inr (.inr h) =>
    match Nat.le.dest (Nat.le_of_lt h) with
    | ⟨j, hj⟩ =>
      have hj0 : 0 < j := by
        have : p - 1 + 0 < p - 1 + j := by rw [hj]; exact h
        exact Nat.lt_of_add_lt_add_left this
      have hjn : j < p - 1 := by
        have : p - 1 + j < p - 1 + (p - 1) := by rw [hj]; exact Nat.add_lt_add hk hm
        exact Nat.lt_of_add_lt_add_left this
      have hs2 : sumRange (fun l => (ofNat (l + 1) : Shell p) ^ (p - 1 + j)) (p - 1)
          = sumRange (fun l => (ofNat (l + 1) : Shell p) ^ j) (p - 1) :=
        sum_congr (p - 1) (fun l hl => by
          rw [pow_add, unit_pow_card F (count_ne_zero (succ_lt_of_lt_pred hl)), one_mul])
      rw [← hj, hs2, (zero_slot F).1 j hj0 hjn, mul_zero]

/-- 20:G3, 20:X3 — the shift is forced: `N + c` is skew on the nonconstant modes exactly when `2c = 1`. No generator. -/
theorem half_forced (h3 : 2 < p) (c : Shell p) :
    (∀ k, 0 < k → k < p - 1 → ((ofNat k : Shell p) + c) + (ofNat (p - 1 - k) + c) = 0) ↔
      (2 : Shell p) * c = 1 := by
  constructor
  · intro h
    have h1 : 1 < p - 1 := lt_pred_of_succ_lt h3
    have e := h 1 (Nat.zero_lt_succ 0) h1
    rw [count_pair_shift (FRC.Nat.add_sub_of_le (Nat.le_of_lt h1))] at e
    have e2 := neg_eq_of_add_eq_zero e
    rw [neg_neg] at e2
    exact e2.symm
  · intro h k _ hk
    rw [count_pair_shift (FRC.Nat.add_sub_of_le (Nat.le_of_lt hk)), h]
    exact neg_add 1

/-- 20:G3 — the run of counts that starts at `m(p − 1)`: its counts at `k` and at `p − 1 − k` add to `−(2m + 1)`, so the
skew shift of the run is `½ + m`. No generator. -/
theorem count_run (m : Nat) {k : Nat} (hk : k ≤ p - 1) :
    (ofNat (m * (p - 1) + k) : Shell p) + ofNat (m * (p - 1) + (p - 1 - k)) + ofNat (2 * m + 1) = 0 := by
  have hN : (ofNat (p - 1) : Shell p) = -1 := eq_neg_of_add_eq_zero count_top
  have hd : (ofNat k : Shell p) + ofNat (p - 1 - k) = -1 := count_pair_neg (FRC.Nat.add_sub_of_le hk)
  rw [← ofNat_add (m * (p - 1)) k, ← ofNat_add (m * (p - 1)) (p - 1 - k), ← ofNat_mul m (p - 1), hN,
    count_succ (2 * m), ← ofNat_mul 2 m]
  have e : (ofNat m * -1 + ofNat k) + (ofNat m * -1 + ofNat (p - 1 - k)) + (ofNat 2 * ofNat m + 1)
      = ((ofNat k : Shell p) + ofNat (p - 1 - k)) + 1 := by
    rw [show (ofNat 2 : Shell p) = 1 + 1 from two_eq_one_add_one]
    exact RE.sound (look [ofNat m, ofNat k, ofNat (p - 1 - k)])
      (.add (.add (.add (.mul (.var 0) (.neg .one)) (.var 1)) (.add (.mul (.var 0) (.neg .one)) (.var 2)))
        (.add (.mul (.add .one .one) (.var 0)) .one))
      (.add (.add (.var 1) (.var 2)) .one) (by decide +kernel)
  rw [e, hd]
  exact neg_add 1

/-! ## The zeros -/

/-- 20:G4 — the frequency of the count `k`: `γ_k = −i(k + ½)`, with `i` the Subject's quarter-turn and
`½ = 2κ + 1`. -/
def frequency (g : Shell p) (κ k : Nat) : Shell p :=
  -(quarterTurn g κ * (ofNat k + ofNat (2 * κ + 1)))

theorem half_add_half (F : Frame p κ g) : (ofNat (2 * κ + 1) : Shell p) + ofNat (2 * κ + 1) = 1 := by
  rw [← two_mul']; exact (half_inverse F).1

/-- 20:G7 — the inverse of `2` is unique: `2x = 1` exactly when `x = 2κ + 1`. -/
theorem half_unique (F : Frame p κ g) (x : Shell p) : (2 : Shell p) * x = 1 ↔ x = ofNat (2 * κ + 1) :=
  ⟨fun h => F.mul_left_cancel F.two_ne_zero (h.trans (half_inverse F).1.symm), fun h => h ▸ (half_inverse F).1⟩

/-- 20:G6 — `½ + iγ_k = k + 1` for every count `k`; for `k ≥ 1` this residue is the zero of the mode. -/
theorem zero_count (F : Frame p κ g) (k : Nat) :
    (ofNat (2 * κ + 1) : Shell p) + quarterTurn g κ * frequency g κ k = ofNat (k + 1) := by
  unfold frequency
  rw [mul_neg, ← mul_assoc, F.quarter_turn_sq, neg_one_mul, neg_neg, add_comm (ofNat k), ← add_assoc,
    half_add_half F, add_comm, count_succ]

/-- 20:G6, 20:F7 — the zeros `ρ_k = k + 1`, `1 ≤ k ≤ p − 2`, are the residues other than `0` and `1`. No generator. -/
theorem zeros_fill (h1 : 1 < p) (r : Shell p) :
    (r ≠ 0 ∧ r ≠ 1) ↔ ∃ k, 0 < k ∧ k < p - 1 ∧ r = ofNat (k + 1) := by
  constructor
  · intro ⟨h0, h1'⟩
    have hv0 : r.val ≠ 0 := fun h => h0 (ext h)
    have hv1 : r.val ≠ 1 := fun h => h1' (ext (by rw [h, val_one, FRC.Nat.mod_eq_of_lt h1]))
    have hlt : r.val < p := r.lt
    have e : (ofNat r.val : Shell p) = r := ofNat_val r
    match hr : r.val with
    | 0 => exact absurd hr hv0
    | 1 => exact absurd hr hv1
    | n + 2 =>
      rw [hr] at hlt e
      exact ⟨n + 1, Nat.zero_lt_succ n, lt_pred_of_succ_lt hlt, e.symm⟩
  · intro ⟨k, hk0, hk, e⟩
    have hlt : k + 1 < p := succ_lt_of_lt_pred hk
    constructor
    · rw [e]; exact count_ne_zero hlt
    · intro h
      rw [e] at h
      have hv := val_injective h
      rw [val_ofNat, val_one, FRC.Nat.mod_eq_of_lt hlt, FRC.Nat.mod_eq_of_lt h1] at hv
      exact absurd (Nat.succ.inj hv) (Nat.ne_of_gt hk0)

/-- 20:G5, 20:G6, 20:X2 — for every `k ≤ p − 1`, `(p − 1 − k) + 1 = 1 − (k + 1)` and `γ_{p−1−k} = −γ_k` as residues; for
`1 ≤ k ≤ p − 2` these are the zero and the frequency of the conjugate mode. -/
theorem zero_conjugate (F : Frame p κ g) {k : Nat} (hk : k ≤ p - 1) :
    (ofNat (p - 1 - k + 1) : Shell p) = 1 + -(ofNat (k + 1)) ∧
      frequency g κ (p - 1 - k) = -(frequency g κ k) := by
  have hkk : k + (p - 1 - k) = p - 1 := FRC.Nat.add_sub_of_le hk
  have hK' : (ofNat (p - 1 - k) : Shell p) = -1 + -(ofNat k) := eq_add_neg_of_add_eq (count_pair_neg hkk)
  constructor
  · rw [count_succ, count_succ, hK']
    exact RE.sound (look [ofNat k])
      (.add (.add (.neg .one) (.neg (.var 0))) .one) (.add .one (.neg (.add (.var 0) .one))) (by decide +kernel)
  · have hs : ((ofNat k : Shell p) + ofNat (2 * κ + 1)) + (ofNat (p - 1 - k) + ofNat (2 * κ + 1)) = 0 := by
      rw [count_pair_shift hkk, (half_inverse F).1]; exact neg_add 1
    unfold frequency
    rw [← neg_eq_of_add_eq_zero hs, ← mul_neg]

/-! ## The centre and the order of the pairs -/

/-- 20:G7 — the mode of count `π = 2κ` is its own conjugate, its zero is `2⁻¹`, its frequency is `0`, and it is the
only count below `p − 1` with the frequency `0`. -/
theorem centre_mode (F : Frame p κ g) :
    2 * κ + 2 * κ = p - 1 ∧ (2 : Shell p) * ofNat (2 * κ + 1) = 1 ∧ frequency g κ (2 * κ) = 0 ∧
      ∀ k, k < p - 1 → frequency g κ k = 0 → k = 2 * κ := by
  have hi : quarterTurn g κ ≠ 0 := fun h0 => by
    have e := F.quarter_turn_sq
    rw [h0, zero_mul] at e
    have e1 : (1 : Shell p) = 0 := by rw [← neg_neg (1 : Shell p), ← e, neg_zero]
    exact F.one_ne_zero e1
  refine ⟨F.four_kappa, (half_inverse F).1, ?_, ?_⟩
  · unfold frequency
    rw [(half_inverse F).2, add_neg, mul_zero, neg_zero]
  · intro k hk h
    unfold frequency at h
    have h2 : quarterTurn g κ * ((ofNat k : Shell p) + ofNat (2 * κ + 1)) = 0 := by
      rw [← neg_neg (quarterTurn g κ * ((ofNat k : Shell p) + ofNat (2 * κ + 1))), h, neg_zero]
    match F.mul_eq_zero h2 with
    | .inl e => exact absurd e hi
    | .inr e =>
      have e3 : (ofNat k : Shell p) = ofNat (2 * κ) := by
        rw [eq_neg_of_add_eq_zero e, (half_inverse F).2, neg_neg]
      have hv := val_injective e3
      rw [val_ofNat, val_ofNat, FRC.Nat.mod_eq_of_lt (Nat.lt_of_lt_of_le hk (Nat.sub_le p 1)),
        FRC.Nat.mod_eq_of_lt (Nat.lt_of_lt_of_le F.two_kappa_lt (Nat.sub_le p 1))] at hv
      exact hv

/-- 20:G7, 20:G9 — the invariant of a conjugate pair: `ρ(1 − ρ) = ¼ + γ² = −k(k + 1)`, the same for a count and its
conjugate. -/
theorem pair_invariant (F : Frame p κ g) (k : Nat) :
    (ofNat (k + 1) : Shell p) * (1 + -(ofNat (k + 1))) = -(ofNat k * ofNat (k + 1)) ∧
      (ofNat (2 * κ + 1) : Shell p) * ofNat (2 * κ + 1) + frequency g κ k * frequency g κ k
        = -(ofNat k * ofNat (k + 1)) ∧
      ∀ k', k + k' = p - 1 → (ofNat k' : Shell p) * ofNat (k' + 1) = ofNat k * ofNat (k + 1) := by
  refine ⟨?_, ?_, ?_⟩
  · rw [count_succ]
    exact RE.sound (look [ofNat k])
      (.mul (.add (.var 0) .one) (.add .one (.neg (.add (.var 0) .one))))
      (.neg (.mul (.var 0) (.add (.var 0) .one))) (by decide +kernel)
  · unfold frequency
    rw [neg_mul_neg, mul_mul_mul_comm, F.quarter_turn_sq, neg_one_mul, count_succ k, ← half_add_half F]
    exact RE.sound (look [ofNat k, ofNat (2 * κ + 1)])
      (.add (.mul (.var 1) (.var 1)) (.neg (.mul (.add (.var 0) (.var 1)) (.add (.var 0) (.var 1)))))
      (.neg (.mul (.var 0) (.add (.var 0) (.add (.var 1) (.var 1))))) (by decide +kernel)
  · intro k' h
    rw [count_succ, count_succ, eq_add_neg_of_add_eq (count_pair_neg h)]
    exact RE.sound (look [ofNat k])
      (.mul (.add (.neg .one) (.neg (.var 0))) (.add (.add (.neg .one) (.neg (.var 0))) .one))
      (.mul (.var 0) (.add (.var 0) .one)) (by decide +kernel)

/-- 20:G9 — the order: the counts `2κ − j` and `2κ + j` are conjugate, their zeros are `2⁻¹ − j` and
`2⁻¹ + j`, and the smaller of the two is `2κ − j`, the energy of the pair. No generator: the statement takes the
cardinality `p = 4κ + 1` alone. -/
theorem energy_order (hc : p = 4 * κ + 1) {j : Nat} (hj : j ≤ 2 * κ) :
    (2 * κ - j) + (2 * κ + j) = p - 1 ∧
      (ofNat (2 * κ + j + 1) : Shell p) = ofNat (2 * κ + 1) + ofNat j ∧
      (ofNat (2 * κ - j + 1) : Shell p) + ofNat j = ofNat (2 * κ + 1) ∧
      2 * κ - j ≤ 2 * κ + j := by
  refine ⟨?_, ?_, ?_, Nat.le_trans (Nat.sub_le _ _) (Nat.le_add_right _ _)⟩
  · have h4 : 2 * κ + 2 * κ = p - 1 := by
      rw [hc]
      show 2 * κ + 2 * κ = 2 * 2 * κ
      rw [FRC.Nat.mul_assoc, ← Nat.two_mul (2 * κ)]
    rw [Nat.add_comm (2 * κ) j, ← Nat.add_assoc, FRC.Nat.sub_add_cancel hj, h4]
  · rw [ofNat_add, Nat.add_right_comm]
  · rw [ofNat_add, Nat.add_right_comm, FRC.Nat.sub_add_cancel hj]

/-! ## The cardinal modes and their zeros -/

/-- The counts below `p − 1` whose fourfold is a multiple of `p − 1`. -/
theorem cardinal_counts (F : Frame p κ g) {k : Nat} (hk : k < p - 1) :
    (k * 4) % (p - 1) = 0 ↔ (k = 0 ∨ k = κ ∨ k = 2 * κ ∨ k = 3 * κ) := by
  have key : ∀ j : Nat, (j * κ) * 4 = (p - 1) * j + 0 := fun j => by
    rw [F.n_eq, Nat.add_zero, Nat.mul_comm (j * κ) 4, FRC.Nat.mul_left_comm 4 j κ, Nat.mul_comm j (4 * κ)]
  constructor
  · intro h0
    match FRC.Nat.mod_spec (p - 1) F.n_pos (k * 4) with
    | ⟨q, hq⟩ =>
      rw [h0, Nat.add_zero, F.n_eq, Nat.mul_comm k 4, FRC.Nat.mul_assoc 4 κ q] at hq
      have hkq : k = κ * q := Nat.eq_of_mul_eq_mul_left (Nat.zero_lt_succ 3) hq
      have hq4 : q < 4 := by
        have h2 : κ * q < κ * 4 := by rw [← hkq, Nat.mul_comm κ 4, ← F.n_eq]; exact hk
        match Nat.lt_or_ge q 4 with
        | .inl h => exact h
        | .inr h => exact absurd h2 (Nat.not_lt_of_le (Nat.mul_le_mul_left κ h))
      match q, hq4, hkq with
      | 0, _, e => exact .inl e
      | 1, _, e => exact .inr (.inl (by rw [e, Nat.mul_one]))
      | 2, _, e => exact .inr (.inr (.inl (by rw [e, Nat.mul_comm])))
      | 3, _, e => exact .inr (.inr (.inr (by rw [e, Nat.mul_comm])))
      | q + 4, h, _ => exact absurd h (Nat.not_lt_of_le (Nat.le_add_left 4 q))
  · intro h
    match h with
    | .inl e => rw [e]; rfl
    | .inr (.inl e) =>
      have := key 1; rw [Nat.one_mul] at this
      rw [e]; exact FRC.Nat.mod_unique F.n_pos this
    | .inr (.inr (.inl e)) => rw [e]; exact FRC.Nat.mod_unique F.n_pos (key 2)
    | .inr (.inr (.inr e)) => rw [e]; exact FRC.Nat.mod_unique F.n_pos (key 3)

/-- 20:G10 — a mode has all its values in `{1, −1, i, −i}` exactly when its count is `0`, `κ`, `2κ` or `3κ`. -/
theorem cardinal_modes (F : Frame p κ g) {k : Nat} (hk : k < p - 1) :
    (∀ x : Shell p, x ≠ 0 →
        x ^ k = 1 ∨ x ^ k = -1 ∨ x ^ k = quarterTurn g κ ∨ x ^ k = -(quarterTurn g κ)) ↔
      (k = 0 ∨ k = κ ∨ k = 2 * κ ∨ k = 3 * κ) := by
  constructor
  · intro h
    have h4 : (g ^ k) ^ 4 = 1 := (F.fourth_roots (g ^ k)).mpr (h g F.g_ne_zero)
    rw [← pow_mul] at h4
    exact (cardinal_counts F hk).mp (F.mod_eq_zero_of_pow_eq_one h4)
  · intro h x hx
    apply (F.fourth_roots (x ^ k)).mp
    match F.eq_pow_of_ne_zero hx with
    | ⟨t, _, e⟩ =>
      rw [← e, ← pow_mul, pow_mul_comm, F.pow_eq_one_of_mod ((cardinal_counts F hk).mpr h), one_pow]

/-- 20:G10, 20:G12 — the zeros of the counts `0`, `κ`, `2κ`, `3κ` are `1`, `¾`, `½`, `¼`. No generator: the statement
takes the cardinality `p = 4κ + 1` alone, a Subject's or a Carrier's. -/
theorem cardinal_zeros (hc : p = 4 * κ + 1) :
    (ofNat (0 + 1) : Shell p) = 1 ∧ (4 : Shell p) * ofNat (κ + 1) = 3 ∧
      (2 : Shell p) * ofNat (2 * κ + 1) = 1 ∧ (4 : Shell p) * ofNat (3 * κ + 1) = 1 := by
  refine ⟨rfl, ?_, ?_, ?_⟩
  · have e : 4 * (κ + 1) = 3 + 1 * p := by rw [hc, Nat.one_mul, Nat.add_comm 3]; rfl
    show ofNat 4 * ofNat (κ + 1) = ofNat 3
    rw [ofNat_mul, e, count_add_mul_self]
  · have e : 2 * (2 * κ + 1) = 1 + 1 * p := by
      rw [hc, Nat.one_mul]
      calc 2 * (2 * κ + 1) = 2 * (2 * κ) + 2 * 1 := Nat.mul_add 2 (2 * κ) 1
        _ = 4 * κ + 2 := by rw [← FRC.Nat.mul_assoc]
        _ = 1 + (4 * κ + 1) := by rw [Nat.add_comm 1, Nat.add_assoc]
    show ofNat 2 * ofNat (2 * κ + 1) = ofNat 1
    rw [ofNat_mul, e, count_add_mul_self]
  · have e : 4 * (3 * κ + 1) = 1 + 3 * p := by
      calc 4 * (3 * κ + 1) = 4 * (3 * κ) + 4 := Nat.mul_add 4 (3 * κ) 1
        _ = 3 * (4 * κ) + 4 := by rw [FRC.Nat.mul_left_comm]
        _ = 1 + (3 * (4 * κ) + 3) := by rw [Nat.add_comm 1]
        _ = 1 + 3 * (4 * κ + 1) := by rw [Nat.mul_add 3 (4 * κ) 1]
        _ = 1 + 3 * p := by rw [hc]
    show ofNat 4 * ofNat (3 * κ + 1) = ofNat 1
    rw [ofNat_mul, e, count_add_mul_self]

/-! ## The Carrier's chart -/

/-- 20:G12, 20:X1 — on a shell of cardinality `4S + 1`, with no frame: the centre of the counts is `−½ = 2S`, in the
form `2·(2S) + 1 = 0`, and `k + (p − 1 − k)` is twice the centre for every `k ≤ p − 1`; for a count `k ≥ 1` the
second term is its conjugate. -/
theorem carrier_centre {S : Nat} (hΩ : p = 4 * S + 1) :
    (2 : Shell p) * ofNat (2 * S) + 1 = 0 ∧
      ∀ k, k ≤ p - 1 → (ofNat k : Shell p) + ofNat (p - 1 - k) = (2 : Shell p) * ofNat (2 * S) := by
  have h0 : (2 : Shell p) * ofNat (2 * S) + 1 = 0 := by
    have e : 2 * (2 * S) + 1 = p := by rw [hΩ, ← FRC.Nat.mul_assoc]
    show ofNat 2 * ofNat (2 * S) + ofNat 1 = 0
    rw [ofNat_mul, ofNat_add, e, ofNat_self]
  refine ⟨h0, fun k hk => ?_⟩
  rw [count_pair_neg (FRC.Nat.add_sub_of_le hk), eq_neg_of_add_eq_zero h0]

/-! ## The count operator on vectors, the generator, and the runs of counts without a skew shift -/

/-- The Gram entry of two modes: `⟨x^k, x^m⟩ = Σ_{x≠0} x^k·x^m`. -/
def gram (p : Nat) [Pos p] (k m : Nat) : Shell p :=
  sumRange (fun l => (ofNat (l + 1) : Shell p) ^ k * (ofNat (l + 1) : Shell p) ^ m) (p - 1)

/-- The vector with the mode coefficients `c`: `v(x) = Σ_{k<p−1} c_k·x^k`, read at the label `x = l + 1`. -/
def modeVector (c : Nat → Shell p) (l : Nat) : Shell p :=
  sumRange (fun k => c k * (ofNat (l + 1) : Shell p) ^ k) (p - 1)

/-- The pairing `⟨v, w⟩ = Σ_{x≠0} v(x)·w(x)`. -/
def pairing (v w : Nat → Shell p) : Shell p := sumRange (fun l => v l * w l) (p - 1)

/-- The pairing of two vectors through their mode coefficients. -/
theorem pairing_modes (c d : Nat → Shell p) :
    pairing (modeVector c) (modeVector d)
      = sumRange (fun k => sumRange (fun m => c k * d m * gram p k m) (p - 1)) (p - 1) := by
  unfold pairing modeVector gram
  have h1 : sumRange (fun l => sumRange (fun k => c k * (ofNat (l + 1) : Shell p) ^ k) (p - 1) *
        sumRange (fun m => d m * (ofNat (l + 1) : Shell p) ^ m) (p - 1)) (p - 1)
      = sumRange (fun l => sumRange (fun k => sumRange (fun m =>
          c k * (ofNat (l + 1) : Shell p) ^ k * (d m * (ofNat (l + 1) : Shell p) ^ m)) (p - 1)) (p - 1)) (p - 1) :=
    sum_congr (p - 1) (fun l _ => sum_mul_sum _ _ _ _)
  rw [h1, sum_comm]
  apply sum_congr; intro k _
  rw [sum_comm]
  apply sum_congr; intro m _
  rw [← sum_mul_left]
  apply sum_congr; intro l _
  exact mul_mul_mul_comm _ _ _ _

/-- The Gram entry is symmetric, and `(k + m + 1)·⟨x^k, x^m⟩ = 0` unless both modes are constant. -/
theorem gram_skew (F : Frame p κ g) {k m : Nat} (hk : k < p - 1) (hm : m < p - 1) (h : 0 < k ∨ 0 < m) :
    ((ofNat k : Shell p) + ofNat m + 1) * gram p k m = 0 :=
  match h with
  | .inl hk0 => count_adjoint F hk0 hk hm
  | .inr hm0 => by
    have e : gram p k m = gram p m k := sum_congr (p - 1) (fun l _ => mul_comm _ _)
    rw [e, add_comm (ofNat k) (ofNat m)]
    exact count_adjoint F hm0 hm hk

/-- The constant mode pairs with itself to `p − 1 ≡ −1`. -/
theorem gram_constant : gram p 0 0 = -1 := by
  have e : gram p 0 0 = sumRange (fun _ => (1 : Shell p)) (p - 1) :=
    sum_congr (p - 1) (fun l _ => mul_one _)
  rw [e, sum_const, mul_one]
  exact eq_neg_of_add_eq_zero count_top

/-- 20:G2 — the count operator on vectors. With `N` acting on the mode coefficients by `c_k ↦ k·c_k`:
`⟨Nv, w⟩ + ⟨v, Nw⟩ + ⟨v, w⟩ = −c_0·d_0`. So `N* = −1 − N` on the vectors with no constant part. -/
theorem count_adjoint_vector (F : Frame p κ g) (c d : Nat → Shell p) :
    pairing (modeVector (fun k => ofNat k * c k)) (modeVector d)
      + pairing (modeVector c) (modeVector (fun k => ofNat k * d k))
      + pairing (modeVector c) (modeVector d) = -(c 0 * d 0) := by
  rw [pairing_modes, pairing_modes, pairing_modes, ← sum_add, ← sum_add]
  have hterm : ∀ k m, ofNat k * c k * d m * gram p k m + c k * (ofNat m * d m) * gram p k m
        + c k * d m * gram p k m
      = c k * d m * (((ofNat k : Shell p) + ofNat m + 1) * gram p k m) := fun k m =>
    RE.sound (look [ofNat k, ofNat m, c k, d m, gram p k m])
      (.add (.add (.mul (.mul (.mul (.var 0) (.var 2)) (.var 3)) (.var 4))
          (.mul (.mul (.var 2) (.mul (.var 1) (.var 3))) (.var 4)))
        (.mul (.mul (.var 2) (.var 3)) (.var 4)))
      (.mul (.mul (.var 2) (.var 3)) (.mul (.add (.add (.var 0) (.var 1)) .one) (.var 4))) (by decide +kernel)
  have hin : ∀ k,
      sumRange (fun m => ofNat k * c k * d m * gram p k m) (p - 1)
        + sumRange (fun m => c k * (ofNat m * d m) * gram p k m) (p - 1)
        + sumRange (fun m => c k * d m * gram p k m) (p - 1)
      = sumRange (fun m => c k * d m * (((ofNat k : Shell p) + ofNat m + 1) * gram p k m)) (p - 1) := fun k => by
    rw [← sum_add, ← sum_add]
    exact sum_congr (p - 1) (fun m _ => hterm k m)
  have hout : sumRange (fun k => sumRange (fun m => ofNat k * c k * d m * gram p k m) (p - 1)
        + sumRange (fun m => c k * (ofNat m * d m) * gram p k m) (p - 1)
        + sumRange (fun m => c k * d m * gram p k m) (p - 1)) (p - 1)
      = sumRange (fun k => sumRange (fun m =>
          c k * d m * (((ofNat k : Shell p) + ofNat m + 1) * gram p k m)) (p - 1)) (p - 1) :=
    sum_congr (p - 1) (fun k _ => hin k)
  refine Eq.trans hout ?_
  have hk0 : ∀ k, k < p - 1 → k ≠ 0 →
      sumRange (fun m => c k * d m * (((ofNat k : Shell p) + ofNat m + 1) * gram p k m)) (p - 1) = 0 :=
    fun k hk hne => sum_zero (p - 1) (fun m hm => by
      rw [gram_skew F hk hm (.inl (Nat.pos_of_ne_zero hne)), mul_zero])
  rw [sum_eq_single F.n_pos hk0]
  have hm0 : ∀ m, m < p - 1 → m ≠ 0 →
      c 0 * d m * (((ofNat 0 : Shell p) + ofNat m + 1) * gram p 0 m) = 0 :=
    fun m hm hne => by rw [gram_skew F F.n_pos hm (.inr (Nat.pos_of_ne_zero hne)), mul_zero]
  rw [sum_eq_single F.n_pos hm0, gram_constant]
  show c 0 * d 0 * ((0 + 0 + 1) * -1) = -(c 0 * d 0)
  rw [add_zero, zero_add, one_mul, ← mul_neg, mul_one]

/-- 20:G5, 20:X3 — the generator `H = −i(N + ½)` on the modes: `(γ_k + γ_m)·⟨x^k, x^m⟩ = 0` unless both modes are
constant. `H` is skew for the pairing, as `N + ½` is. -/
theorem generator_skew (F : Frame p κ g) {k m : Nat} (hk : k < p - 1) (hm : m < p - 1) (h : 0 < k ∨ 0 < m) :
    (frequency g κ k + frequency g κ m) * gram p k m = 0 := by
  have e : frequency g κ k + frequency g κ m
      = -(quarterTurn g κ) * ((ofNat k : Shell p) + ofNat m + 1) := by
    unfold frequency
    rw [← half_add_half F]
    exact RE.sound (look [quarterTurn g κ, ofNat k, ofNat m, ofNat (2 * κ + 1)])
      (.add (.neg (.mul (.var 0) (.add (.var 1) (.var 3)))) (.neg (.mul (.var 0) (.add (.var 2) (.var 3)))))
      (.mul (.neg (.var 0)) (.add (.add (.var 1) (.var 2)) (.add (.var 3) (.var 3)))) (by decide +kernel)
  rw [e, mul_assoc, gram_skew F hk hm h, mul_zero]

/-- A pair of counts whose sum is `q(p − 1)`: a common shift `c` that makes the pair skew has `2c = q`. -/
theorem run_pair_shift {a b q : Nat} (hab : a + b = (p - 1) * q + 0) (c : Shell p)
    (h : ((ofNat a : Shell p) + c) + (ofNat b + c) = 0) : (2 : Shell p) * c = ofNat q := by
  have hN : (ofNat (p - 1) : Shell p) = -1 := eq_neg_of_add_eq_zero count_top
  rw [add_add_add_comm, ofNat_add, hab, Nat.add_zero, ← ofNat_mul, hN, neg_one_mul, ← two_mul'] at h
  have e := neg_eq_of_add_eq_zero h
  rw [neg_neg] at e
  exact e.symm

/-- 20:G3 — the runs without a skew shift. A run of `p − 1` consecutive counts that starts at
`m(p − 1) + r` with `2 ≤ r ≤ p − 2` has no shift `c` that makes `N + c` skew on its nonconstant modes: the classes
`1` and `p − 2` ask for `2c = 2m + 2`, and the self-conjugate class `2κ` asks for `2c = 2m + 1` or `2m + 3`. -/
theorem count_run_only (F : Frame p κ g) (m : Nat) {r : Nat} (hr : 2 ≤ r) (hr' : r + 1 ≤ p - 1) (c : Shell p) :
    ¬ ∀ a b, m * (p - 1) + r ≤ a → a < m * (p - 1) + r + (p - 1) →
        m * (p - 1) + r ≤ b → b < m * (p - 1) + r + (p - 1) →
        a % (p - 1) ≠ 0 → (a + b) % (p - 1) = 0 → ((ofNat a : Shell p) + c) + (ofNat b + c) = 0 := by
  intro h
  have hN1 : 1 ≤ p - 1 := F.n_pos
  have h1N : 1 < p - 1 := Nat.lt_of_lt_of_le (Nat.lt_of_lt_of_le (Nat.lt_succ_self 1) hr) (Nat.le_of_succ_le hr')
  have hrN : r ≤ p - 1 := Nat.le_of_succ_le hr'
  have hs : (m + 1) * (p - 1) = m * (p - 1) + (p - 1) := Nat.succ_mul m (p - 1)
  have hone : (1 : Shell p) ≠ 0 := F.one_ne_zero
  -- the pair of the classes 1 and p − 2
  have hA : (2 : Shell p) * c = ofNat (2 * m + 2) := by
    have hab : ((m + 1) * (p - 1) + 1) + (m * (p - 1) + (p - 1 - 1)) = (p - 1) * (2 * m + 2) + 0 := by
      have h1 : 1 + (p - 1 - 1) = p - 1 := FRC.Nat.add_sub_of_le hN1
      calc ((m + 1) * (p - 1) + 1) + (m * (p - 1) + (p - 1 - 1))
          = ((m + 1) * (p - 1) + m * (p - 1)) + (1 + (p - 1 - 1)) := FRC.Nat.add_add_add_comm _ _ _ _
        _ = (m + 1) * (p - 1) + (m * (p - 1) + (p - 1)) := by rw [h1, Nat.add_assoc]
        _ = (m + 1) * (p - 1) + (m + 1) * (p - 1) := by rw [← hs]
        _ = 2 * ((m + 1) * (p - 1)) := (Nat.two_mul _).symm
        _ = 2 * (m + 1) * (p - 1) := (FRC.Nat.mul_assoc 2 (m + 1) (p - 1)).symm
        _ = (p - 1) * (2 * m + 2) + 0 := Nat.mul_comm _ _
    refine run_pair_shift hab c (h _ _ ?_ ?_ ?_ ?_ ?_ ?_)
    · rw [hs]
      exact Nat.add_le_add_left (Nat.le_trans (Nat.le_succ r) (Nat.le_trans hr' (Nat.le_succ (p - 1)))) _
    · rw [hs, Nat.add_right_comm (m * (p - 1)) r (p - 1)]
      exact Nat.add_le_add_left hr (m * (p - 1) + (p - 1))
    · exact Nat.add_le_add_left (FRC.Nat.le_sub_of_add_le hr') _
    · rw [Nat.add_assoc]
      exact Nat.add_lt_add_left (Nat.lt_of_le_of_lt (Nat.sub_le (p - 1) 1)
        (Nat.lt_of_lt_of_le (Nat.lt_succ_self (p - 1))
          (by rw [Nat.add_comm r]; exact Nat.add_le_add_left (Nat.le_trans (Nat.le_succ 1) hr) (p - 1)))) _
    · have e : (m + 1) * (p - 1) + 1 = (p - 1) * (m + 1) + 1 := by rw [Nat.mul_comm]
      rw [FRC.Nat.mod_unique h1N e]
      exact Nat.succ_ne_zero 0
    · exact FRC.Nat.mod_unique F.n_pos hab
  -- the self-conjugate class 2κ
  have h2κ : ∀ t q : Nat, t + t = q * (p - 1) →
      (t + 2 * κ) + (t + 2 * κ) = (p - 1) * (q + 1) + 0 := fun t q e => by
    calc (t + 2 * κ) + (t + 2 * κ) = (t + t) + (2 * κ + 2 * κ) := FRC.Nat.add_add_add_comm _ _ _ _
      _ = q * (p - 1) + (p - 1) := by rw [e, F.four_kappa]
      _ = (q + 1) * (p - 1) := (Nat.succ_mul q (p - 1)).symm
      _ = (p - 1) * (q + 1) + 0 := Nat.mul_comm _ _
  have hmod : ∀ j : Nat, (j * (p - 1) + 2 * κ) % (p - 1) ≠ 0 := fun j => by
    have e : j * (p - 1) + 2 * κ = (p - 1) * j + 2 * κ := by rw [Nat.mul_comm]
    rw [FRC.Nat.mod_unique F.two_kappa_lt e]
    exact Nat.ne_of_gt F.two_kappa_pos
  match Nat.lt_or_ge (2 * κ) r with
  | .inr hle =>
    -- r ≤ 2κ: the count m(p − 1) + 2κ lies in the run
    have hab := h2κ (m * (p - 1)) (2 * m) (by rw [← Nat.two_mul, FRC.Nat.mul_assoc])
    have hB : (2 : Shell p) * c = ofNat (2 * m + 1) :=
      run_pair_shift hab c (h _ _ (Nat.add_le_add_left hle _)
        (by rw [Nat.add_assoc]; exact Nat.add_lt_add_left (Nat.lt_of_lt_of_le F.two_kappa_lt (Nat.le_add_left _ _)) _)
        (Nat.add_le_add_left hle _)
        (by rw [Nat.add_assoc]; exact Nat.add_lt_add_left (Nat.lt_of_lt_of_le F.two_kappa_lt (Nat.le_add_left _ _)) _)
        (hmod m) (FRC.Nat.mod_unique F.n_pos hab))
    rw [hA, count_succ (2 * m + 1)] at hB
    have e0 : (1 : Shell p) + ofNat (2 * m + 1) = 0 + ofNat (2 * m + 1) := by rw [zero_add, add_comm]; exact hB
    exact hone (add_right_cancel e0)
  | .inl hlt =>
    -- 2κ < r: the count (m + 1)(p − 1) + 2κ lies in the run
    have hab := h2κ ((m + 1) * (p - 1)) (2 * (m + 1)) (by rw [← Nat.two_mul, FRC.Nat.mul_assoc])
    have hin1 : m * (p - 1) + r ≤ (m + 1) * (p - 1) + 2 * κ := by
      rw [hs, Nat.add_assoc]
      exact Nat.add_le_add_left (Nat.le_trans hrN (Nat.le_add_right _ _)) _
    have hin2 : (m + 1) * (p - 1) + 2 * κ < m * (p - 1) + r + (p - 1) := by
      rw [hs, Nat.add_right_comm (m * (p - 1)) r (p - 1)]
      exact Nat.add_lt_add_left hlt _
    have hB : (2 : Shell p) * c = ofNat (2 * (m + 1) + 1) :=
      run_pair_shift hab c (h _ _ hin1 hin2 hin1 hin2 (hmod (m + 1)) (FRC.Nat.mod_unique F.n_pos hab))
    rw [hA] at hB
    have hB' : (ofNat (2 * m + 2) : Shell p) = ofNat (2 * m + 2) + 1 := hB.trans (count_succ (2 * m + 2))
    have e0 : (0 : Shell p) + ofNat (2 * m + 2) = 1 + ofNat (2 * m + 2) := by rw [zero_add, add_comm 1]; exact hB'
    exact hone (add_right_cancel e0).symm

/-! ## The symmetry of origin and unit, and the shared zeros -/

/-- 20:G6, 20:G7, 20:X2 — the symmetry of origin and unit. An affine map `x ↦ a·x + b` of the shell keeps the pair `{0, 1}`
exactly when it is the identity or `x ↦ 1 − x`, and `x ↦ 1 − x` fixes `x` exactly when `2x = 1`. No generator. -/
theorem origin_unit_symmetry (a b : Shell p) :
    (((a * 0 + b = 0 ∧ a * 1 + b = 1) ∨ (a * 0 + b = 1 ∧ a * 1 + b = 0)) ↔
        ((a = 1 ∧ b = 0) ∨ (a = -1 ∧ b = 1))) ∧
      ∀ x : Shell p, x = 1 + -x ↔ (2 : Shell p) * x = 1 := by
  refine ⟨⟨?_, ?_⟩, fun x => ⟨?_, ?_⟩⟩
  · intro h
    match h with
    | .inl ⟨h0, h1⟩ =>
      rw [mul_zero, zero_add] at h0
      rw [mul_one, h0, add_zero] at h1
      exact .inl ⟨h1, h0⟩
    | .inr ⟨h0, h1⟩ =>
      rw [mul_zero, zero_add] at h0
      rw [mul_one, h0] at h1
      exact .inr ⟨eq_neg_of_add_eq_zero h1, h0⟩
  · intro h
    match h with
    | .inl ⟨ha, hb⟩ => rw [ha, hb]; exact .inl ⟨by rw [mul_zero, add_zero], by rw [mul_one, add_zero]⟩
    | .inr ⟨ha, hb⟩ =>
      rw [ha, hb]
      exact .inr ⟨by rw [mul_zero, zero_add], by rw [mul_one]; exact neg_add 1⟩
  · intro h
    have e : x + x = 1 := by
      calc x + x = x + (1 + -x) := by rw [← h]
        _ = 1 + (x + -x) := add_left_comm _ _ _
        _ = 1 := by rw [add_neg, add_zero]
    rw [two_mul']; exact e
  · intro h
    rw [two_mul'] at h
    exact eq_add_neg_of_add_eq h

/-- 20:G12 — a zero below `p` is the same integer on every larger shell: the Subject's zero `k + 1` and the
zero `k + 1` on a Carrier's chart are one label. At `k = 0` the label is `1`, where the constant mode stands on both.
No generator. -/
theorem zero_shared {q : Nat} [Pos q] {k : Nat} (hk : k + 1 < p) (hpq : p ≤ q) :
    (ofNat (k + 1) : Shell p).val = k + 1 ∧ (ofNat (k + 1) : Shell q).val = k + 1 :=
  ⟨by rw [val_ofNat, FRC.Nat.mod_eq_of_lt hk],
   by rw [val_ofNat, FRC.Nat.mod_eq_of_lt (Nat.lt_of_lt_of_le hk hpq)]⟩

/-! ## The zeros against a Subject's states (20:F7 (iii); 22 November 2026) -/

/-- 20:F7 — a reading of a shell's residues into `o < n` states identifies two of the labels `2, …, n + 1`. Read at
`n + 2 = Ω`, these labels are the zeros of the Carrier's chart, and a reading into fewer than `Ω − 2` states identifies
two zeros (the pigeonhole `FRC.Logic.no_mirror` on these labels; the two are found by search). -/
theorem zeros_collide {Ω o n : Nat} [Pos Ω] (ho : o < n) (ρ : Shell Ω → Nat) (hρ : ∀ x, ρ x < o) :
    ∃ i j : Nat, i < j ∧ j < n ∧ ρ (ofNat (i + 2)) = ρ (ofNat (j + 2)) :=
  match @decExistsLT (fun j => ∃ i, i < j ∧ ρ (ofNat (i + 2)) = ρ (ofNat (j + 2)))
      (fun j => decExistsLT (fun i => ρ (ofNat (i + 2)) = ρ (ofNat (j + 2))) j) n with
  | .isTrue ⟨j, hj, i, hij, e⟩ => ⟨i, j, hij, hj, e⟩
  | .isFalse hno => (FRC.Logic.no_mirror ho (fun i => ρ (ofNat (i + 2))) (fun _ _ => hρ _) (fun i j hi hj e =>
      match Nat.lt_or_ge i j with
      | .inl hlt => absurd ⟨j, hj, i, hlt, e⟩ hno
      | .inr hge => match Nat.lt_or_ge j i with
        | .inl hlt => absurd ⟨i, hi, j, hlt, e.symm⟩ hno
        | .inr hge' => Nat.le_antisymm hge' hge)).elim

/-- 20:F7 (iii) — no embedded Subject holds the Carrier's list of zeros whole: for `2 ≤ p` and `p² < Ω`, every reading
of the Carrier's residues into `p` states identifies two zeros `k + 1` and `m + 1` of distinct counts
`1 ≤ k < m ≤ Ω − 2`. The Subject has `p < Ω − 2` states, fewer than the zeros. -/
theorem zeros_not_held {Ω p : Nat} [Pos Ω] (hp : 2 ≤ p) (hpΩ : p * p < Ω) (ρ : Shell Ω → Nat) (hρ : ∀ x, ρ x < p) :
    ∃ k m : Nat, 0 < k ∧ k < m ∧ m < Ω - 1 ∧ ρ (ofNat (k + 1)) = ρ (ofNat (m + 1)) :=
  have h2 : p + 2 ≤ p * p :=
    Nat.le_trans (Nat.add_le_add_left hp p) (Nat.two_mul p ▸ Nat.mul_le_mul_right p hp)
  have h3 : p + 2 < Ω := Nat.lt_of_le_of_lt h2 hpΩ
  match Nat.le.dest (Nat.succ_le_of_lt h3) with
  | ⟨d, hd⟩ =>
    have hn : p + 1 + d + 2 = Ω := by rw [Nat.add_right_comm (p + 1) d 2]; exact hd
    match zeros_collide (n := p + 1 + d) (Nat.lt_of_lt_of_le (Nat.lt_succ_self p) (Nat.le_add_right (p + 1) d)) ρ hρ with
    | ⟨i, j, hij, hj, e⟩ =>
      have hm : j + 1 < p + 1 + d + 2 - 1 := Nat.succ_lt_succ hj
      ⟨i + 1, j + 1, Nat.succ_pos i, Nat.succ_lt_succ hij, hn ▸ hm, e⟩

end count20261121

end FRC.Horizon
