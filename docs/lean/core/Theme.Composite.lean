import FrcCore.Theme.Observation

/-!
# FrcCore.Theme.Composite — the quantum theme: composites, correlations and the channel (22-quantum, 15 October 2026)

The composite formalism of 22-quantum in the shadow: a reading Subject's one drive acts diagonally on a cluster, the
offset is its conserved label, and the Bell configuration's identities are ring identities on every shell.

* the `m`-body cluster: the offset vector is drive-invariant and two configurations share an orbit exactly when their
  offset vectors agree (`offset_invariant`, `cluster_offset`, 22:C15); the winding `s` on `C_n` has period
  `n/gcd(s, n)` (`winding_period`, 22:C26);
* the synchronised orbit adds coherently, `|Σ_i χ(u_i)|² = m²`, against the offset-uniform average `m`
  (`locked_norm`, `spread_average`, 22:C15, C22); the field of `m` locked sources is `m` times one, and the
  acceleration of a test cluster is mass-free, `η = 0` (`field_linear`, `eta_zero`, 22:C22);
* the doublet readout is `σ_x` through the half-turn `v⁸ = −1` (`half_turn_sixteen`, `doublet_readout`, 22:C16);
* the Tsirelson square `S² = 8` for `S = 2(ζ + ζ⁷)`, `ζ⁴ = −1`, and no-signalling (`singlet_square`, `no_signalling`,
  22:C17, X7, P3);
* the channel complementarity `V² + C² = 1` on every shell, the product at zero coupling (`channel_complementarity`,
  `channel_product_at_zero`, 22:C19, P1);
* the drive conserves the ledger norm and the visibility revives at the recurrence (`drive_norm`, `revival`, 22:C20);
* the coherent fraction: the branch phase of `m_c` synchronised cells, the pairwise product law, the complete spread
  cancels, and the reduced channel factorises (`branch_phase`, `pair_product`, `spread_cancels`, `channel_assembly`,
  22:C21);
* inter-Subject consistency: the channels of two Subjects agree on the common core, and the joint refinement is the
  common core's partition (`order_independence`, `joint_refinement`, 22:C23, X4).

No axioms.
-/

namespace FRC.Composite

open FRC.Shell
open FRC.Shell.Prime
open FRC.Quantum
open FRC.Observation

variable {q : Nat} [Pos q]

/-! ## 22:C15 — the cluster's offset is a conserved label -/

/-- 22:C15 — the offset vector of a cluster on `(ℤ/N)^m` is invariant under the diagonal drive by `t` chronons:
in the cross form, `x_j + (x_0 + t) ≡ (x_j + t) + x_0 (mod N)`. -/
theorem offset_invariant {N : Nat} (hN : 0 < N) (t : Nat) (x : Nat → Nat) (j : Nat) :
    (x j + (x 0 + t) % N) % N = ((x j + t) % N + x 0) % N := by
  rw [FRC.Nat.add_mod_mod _ _ _ hN, FRC.Nat.mod_add_mod _ _ _ hN, ← Nat.add_assoc, Nat.add_right_comm]

/-- 22:C15, lem:mbody (i)–(ii), 22:C18 — the offset is the orbit label: two configurations `x, y` of the cluster `(ℤ/N)^m`
(`0 < m`, `y` reduced) lie on one orbit of the diagonal drive exactly when their offset vectors agree,
`x_j − x_0 ≡ y_j − y_0 (mod N)` for every cell `j`; the drive time `t` is a residue, `t < N`, and no drive evolution
connects distinct offsets. -/
theorem cluster_offset {N m : Nat} (hN : 0 < N) (hm : 0 < m) (x y : Nat → Nat) (hy : ∀ j, j < m → y j < N) :
    (∃ t, t < N ∧ ∀ j, j < m → (x j + t) % N = y j) ↔ ∀ j, j < m → (x j + y 0) % N = (y j + x 0) % N := by
  constructor
  · intro ⟨t, _, ht⟩ j hj
    rw [← ht 0 hm, ← ht j hj]
    exact offset_invariant hN t x j
  · intro h
    refine ⟨(y 0 + (N - x 0 % N)) % N, Nat.mod_lt _ hN, fun j hj => ?_⟩
    rw [FRC.Nat.add_mod_mod _ _ _ hN]
    match FRC.Nat.mod_spec N hN (x 0) with
    | ⟨k, hk⟩ =>
      have hr : x 0 % N < N := Nat.mod_lt _ hN
      calc (x j + (y 0 + (N - x 0 % N))) % N = ((x j + y 0) % N + (N - x 0 % N)) % N := by
            rw [FRC.Nat.mod_add_mod _ _ _ hN, Nat.add_assoc]
        _ = ((y j + x 0) % N + (N - x 0 % N)) % N := by rw [h j hj]
        _ = (y j + x 0 + (N - x 0 % N)) % N := FRC.Nat.mod_add_mod _ _ _ hN
        _ = (N * (k + 1) + y j) % N := by
            congr 1
            calc y j + x 0 + (N - x 0 % N) = y j + (N * k + x 0 % N + (N - x 0 % N)) := by rw [← hk, Nat.add_assoc]
              _ = y j + (N * k + N) := by rw [Nat.add_assoc (N * k), FRC.Nat.add_sub_of_le (Nat.le_of_lt hr)]
              _ = N * (k + 1) + y j := by rw [Nat.mul_succ, Nat.add_comm]
        _ = y j := by rw [FRC.Nat.add_mul_mod_self_left _ _ _ hN, FRC.Nat.mod_eq_of_lt (hy j hj)]

/-! ## 22:C26 — the period of a winding -/

/-- 22:C26 — the winding `s` on the cycle `C_n` has period `n/gcd(s, n)`: with `n = d n'`, `s = d s'` and `d` the gcd
(`s' u = n' v + 1` the Bezout witness of coprimality), the drive `x ↦ x + s` returns, `s t ≡ 0 (mod n)`, exactly when
`n' ∣ t`; the joint recurrence of a composite is then the lcm of these periods (`FRC.Quantum.joint_recurrence`). -/
theorem winding_period {n s d n' s' u v : Nat} (hd : 0 < d) (hn' : 0 < n') (hn : n = d * n') (hs : s = d * s')
    (hbez : s' * u = n' * v + 1) (t : Nat) : (s * t) % n = 0 ↔ t % n' = 0 := by
  have hn0 : 0 < n := by rw [hn]; exact Nat.mul_pos hd hn'
  constructor
  · intro h
    obtain ⟨c, hc⟩ := eq_mul_of_mod_zero hn0 h
    rw [hn, hs, FRC.Nat.mul_assoc, FRC.Nat.mul_assoc] at hc
    have e1 : s' * t = n' * c := Nat.eq_of_mul_eq_mul_left hd hc
    have e : n' * (v * t) + t = n' * (u * c) := by
      calc n' * (v * t) + t = (n' * v + 1) * t := by rw [FRC.Nat.add_mul, Nat.one_mul, FRC.Nat.mul_assoc]
        _ = s' * u * t := by rw [hbez]
        _ = u * (s' * t) := by rw [Nat.mul_comm s' u, FRC.Nat.mul_assoc]
        _ = n' * (u * c) := by rw [e1, FRC.Nat.mul_left_comm]
    calc t % n' = (n' * (v * t) + t) % n' := (FRC.Nat.add_mul_mod_self_left _ _ _ hn').symm
      _ = 0 := by rw [e]; exact mod_zero_of_eq_mul hn' rfl
  · intro h
    obtain ⟨c, hc⟩ := eq_mul_of_mod_zero hn' h
    refine mod_zero_of_eq_mul (q := s' * c) hn0 ?_
    rw [hc, hs, hn, FRC.Nat.mul_assoc, FRC.Nat.mul_assoc, FRC.Nat.mul_left_comm s']

/-! ## The locked cluster against the spread: `m²` against `m` -/

/-- lem:mbody (iii), 22:C15, 22:C22 — on the synchronised orbit the amplitudes add coherently: `Σ_{i<m} χ = m χ`, and the
weight `(m χ)(m χ̄) = m²` when `χ χ̄ = 1`. -/
theorem locked_norm (m : Nat) {χ χbar : Shell q} (h : χ * χbar = 1) :
    sumRange (fun _ => χ) m = ofNat m * χ ∧ sumRange (fun _ => χ) m * sumRange (fun _ => χbar) m = ofNat (m * m) := by
  refine ⟨sum_const χ m, ?_⟩
  rw [sum_const, sum_const, mul_mul_mul_comm, h, mul_one, ofNat_mul]

/-- The sum of `F` over all configurations `v : Nat → Nat` of the cluster with `v_j < n` for `j < m` and `v_j = 0`
beyond, by recursion on the number of cells. -/
def tsum (n : Nat) (F : (Nat → Nat) → Shell q) : Nat → Shell q
  | 0 => F (fun _ => 0)
  | m + 1 => sumRange (fun θ => tsum n (fun v => F (fun j => if j = m then θ else v j)) m) n

theorem tsum_zero (n : Nat) (F : (Nat → Nat) → Shell q) : tsum n F 0 = F (fun _ => 0) := rfl

theorem tsum_succ (n : Nat) (F : (Nat → Nat) → Shell q) (m : Nat) :
    tsum n F (m + 1) = sumRange (fun θ => tsum n (fun v => F (fun j => if j = m then θ else v j)) m) n := rfl

/-- The configuration sum depends on `F` pointwise. -/
theorem tsum_congr (n : Nat) {F G : (Nat → Nat) → Shell q} (h : ∀ v, F v = G v) : ∀ m, tsum n F m = tsum n G m
  | 0 => h _
  | m + 1 => by
    rw [tsum_succ, tsum_succ]
    exact sum_congr n (fun θ _ => tsum_congr n (fun v => h _) m)

/-- The configuration sum is additive. -/
theorem tsum_add (n : Nat) (F G : (Nat → Nat) → Shell q) : ∀ m, tsum n (fun v => F v + G v) m = tsum n F m + tsum n G m
  | 0 => rfl
  | m + 1 => by
    rw [tsum_succ, tsum_succ, tsum_succ, ← sum_add]
    exact sum_congr n (fun θ _ => tsum_add n _ _ m)

/-- The configuration sum of a constant: `n^m c`. -/
theorem tsum_const (n : Nat) (c : Shell q) : ∀ m, tsum n (fun _ => c) m = ofNat (n ^ m) * c
  | 0 => by rw [tsum_zero]; exact (one_mul c).symm
  | m + 1 => by
    rw [tsum_succ, sum_congr n (fun θ _ => tsum_const n c m), sum_const, ← mul_assoc, ofNat_mul, Nat.pow_succ,
      Nat.mul_comm]

/-- The configuration sum of a scalar multiple. -/
theorem tsum_mul_left (n : Nat) (c : Shell q) (F : (Nat → Nat) → Shell q) :
    ∀ m, tsum n (fun v => c * F v) m = c * tsum n F m
  | 0 => rfl
  | m + 1 => by
    rw [tsum_succ, tsum_succ, ← sum_mul_left]
    exact sum_congr n (fun θ _ => tsum_mul_left n c _ m)

theorem tsum_mul_right (n : Nat) (c : Shell q) (F : (Nat → Nat) → Shell q) (m : Nat) :
    tsum n (fun v => F v * c) m = tsum n F m * c := by
  rw [tsum_congr n (fun v => mul_comm (F v) c), tsum_mul_left, mul_comm]

/-- The configuration sum of a sum over cells. -/
theorem tsum_sum (n m : Nat) (G : Nat → (Nat → Nat) → Shell q) :
    ∀ k, tsum n (fun v => sumRange (fun i => G i v) k) m = sumRange (fun i => tsum n (G i) m) k
  | 0 => by rw [tsum_congr n (fun v => sumRange_zero (fun i => G i v)), tsum_const, mul_zero, sumRange_zero]
  | k + 1 => by
    rw [sumRange_succ, tsum_congr n (fun v => sumRange_succ (fun i => G i v) k), tsum_add, tsum_sum n m G k]

/-- A character of one cell `i < m` sums to zero over the configurations: `Σ_v ζ^{c + v_i} = 0` for `ζ` of order `n`,
`ζ ≠ 1`. -/
theorem tsum_cell (hq : FRC.Nat.isPrime q) {ζ : Shell q} {n : Nat} (hζ : HasOrder ζ n) (hζ1 : ζ ≠ 1) (c : Nat) :
    ∀ m i, i < m → tsum n (fun v => ζ ^ (c + v i)) m = 0
  | 0, i, hi => absurd hi (Nat.not_lt_zero i)
  | m + 1, i, hi => by
    rw [tsum_succ]
    match Nat.decEq i m with
    | .isTrue e =>
      subst e
      have e1 : ∀ θ, θ < n → tsum n (fun v => ζ ^ (c + (fun j => if j = i then θ else v j) i)) i =
          ofNat (n ^ i) * (ζ ^ c * ζ ^ θ) := fun θ _ => by
        dsimp only
        rw [tsum_congr n (fun v => by rw [if_pos rfl, pow_add]), tsum_const]
      rw [sum_congr n e1, sum_mul_left, sum_mul_left, geom_sum_zero hq n hζ.2.1 hζ1, mul_zero, mul_zero]
    | .isFalse e =>
      have hi' : i < m := Nat.lt_of_le_of_ne (Nat.le_of_lt_succ hi) e
      have e1 : ∀ θ, θ < n → tsum n (fun v => ζ ^ (c + (fun j => if j = m then θ else v j) i)) m = 0 := fun θ _ => by
        dsimp only
        rw [tsum_congr n (fun v => by rw [if_neg e]), tsum_cell hq hζ hζ1 c m i hi']
      rw [sum_congr n e1]
      exact sum_zero n (fun _ _ => rfl)

/-- Two distinct cells `i ≠ j` carrying the characters `ζ`, `η` of order `n` (neither `1`) sum to zero over the
configurations. -/
theorem tsum_cross (hq : FRC.Nat.isPrime q) {ζ η : Shell q} {n : Nat} (hζ : HasOrder ζ n) (hζ1 : ζ ≠ 1)
    (hη : HasOrder η n) (hη1 : η ≠ 1) (c c' : Nat) :
    ∀ m i j, i < m → j < m → i ≠ j → tsum n (fun v => ζ ^ (c + v i) * η ^ (c' + v j)) m = 0
  | 0, i, _, hi, _, _ => absurd hi (Nat.not_lt_zero i)
  | m + 1, i, j, hi, hj, hij => by
    rw [tsum_succ]
    match Nat.decEq i m, Nat.decEq j m with
    | .isTrue ei, _ =>
      subst ei
      have hj' : j < i := Nat.lt_of_le_of_ne (Nat.le_of_lt_succ hj) (fun e => hij e.symm)
      have e1 : ∀ θ, θ < n → tsum n (fun v => ζ ^ (c + (fun l => if l = i then θ else v l) i) *
          η ^ (c' + (fun l => if l = i then θ else v l) j)) i = ζ ^ (c + θ) * 0 := fun θ _ => by
        dsimp only
        rw [tsum_congr n (fun v => by rw [if_pos rfl, if_neg (Nat.ne_of_lt hj')]), tsum_mul_left,
          tsum_cell hq hη hη1 c' i j hj']
      rw [sum_congr n e1]
      exact sum_zero n (fun _ _ => mul_zero _)
    | .isFalse ei, .isTrue ej =>
      subst ej
      have hi' : i < j := Nat.lt_of_le_of_ne (Nat.le_of_lt_succ hi) ei
      have e1 : ∀ θ, θ < n → tsum n (fun v => ζ ^ (c + (fun l => if l = j then θ else v l) i) *
          η ^ (c' + (fun l => if l = j then θ else v l) j)) j = 0 * η ^ (c' + θ) := fun θ _ => by
        dsimp only
        rw [tsum_congr n (fun v => by rw [if_pos rfl, if_neg ei]), tsum_mul_right, tsum_cell hq hζ hζ1 c j i hi']
      rw [sum_congr n e1]
      exact sum_zero n (fun _ _ => zero_mul _)
    | .isFalse ei, .isFalse ej =>
      have hi' : i < m := Nat.lt_of_le_of_ne (Nat.le_of_lt_succ hi) ei
      have hj' : j < m := Nat.lt_of_le_of_ne (Nat.le_of_lt_succ hj) ej
      have e1 : ∀ θ, θ < n → tsum n (fun v => ζ ^ (c + (fun l => if l = m then θ else v l) i) *
          η ^ (c' + (fun l => if l = m then θ else v l) j)) m = 0 := fun θ _ => by
        dsimp only
        rw [tsum_congr n (fun v => by rw [if_neg ei, if_neg ej]), tsum_cross hq hζ hζ1 hη hη1 c c' m i j hi' hj' hij]
      rw [sum_congr n e1]
      exact sum_zero n (fun _ _ => rfl)

/-- lem:mbody (iii), 22:C22, 22:C15 — **the offset-uniform average is `m`**: for `m` cells with independent uniform phases
on a cycle of order `n` (`ζ` of order `n`, `η = ζ⁻¹`, neither `1`), the sum over all `n^m` configurations of
`|Σ_i ζ^{v_i}|² = (Σ_i ζ^{v_i})(Σ_j η^{v_j})` is `m n^m`, the average `m`, against `m²` on the synchronised orbit:
the `√m` lives only in amplitude-coherent observables. -/
theorem spread_average (hq : FRC.Nat.isPrime q) {ζ η : Shell q} {n : Nat} (hζ : HasOrder ζ n) (hζ1 : ζ ≠ 1)
    (hη : HasOrder η n) (hη1 : η ≠ 1) (hζη : ζ * η = 1) (m : Nat) :
    tsum n (fun v => sumRange (fun i => ζ ^ (v i)) m * sumRange (fun j => η ^ (v j)) m) m = ofNat m * ofNat (n ^ m) := by
  rw [tsum_congr n (fun v => sum_mul_sum _ _ m m), tsum_sum]
  have e1 : ∀ i, i < m → tsum n (fun v => sumRange (fun j => ζ ^ (v i) * η ^ (v j)) m) m = ofNat (n ^ m) := fun i hi => by
    rw [tsum_sum]
    have e2 : ∀ j, j < m → tsum n (fun v => ζ ^ (v i) * η ^ (v j)) m = if j = i then ofNat (n ^ m) else 0 := fun j hj => by
      match Nat.decEq j i with
      | .isTrue e =>
        subst e
        rw [if_pos rfl, tsum_congr n (fun v => by rw [← mul_pow, hζη, one_pow]), tsum_const, mul_one]
      | .isFalse e =>
        rw [if_neg e]
        have := tsum_cross hq hζ hζ1 hη hη1 0 0 m i j hi hj (fun e' => e e'.symm)
        rw [tsum_congr n (fun v => by rw [Nat.zero_add, Nat.zero_add]) m] at this
        exact this
    rw [sum_congr m e2, sum_eq_single (f := fun j => if j = i then ofNat (n ^ m) else 0) hi
      (fun j _ hne => if_neg hne), if_pos rfl]
  rw [sum_congr m e1, sum_const]

/-- 22:C22 (i) — the stationary field is linear in its sources with coefficient exactly `m` per locked cluster of `m`
cells: `Σ_{i<m} u = m u`. -/
theorem field_linear (m : Nat) (u : Shell q) : sumRange (fun _ => u) m = ofNat m * u := sum_const u m

/-- 22:C22 (ii) — the exact equivalence-principle null: the pull `m_t ∇u` on a locked test cluster against its inertia
`m_t` gives the acceleration `∇u` for every `m_t` (`w = m_t⁻¹`), so `η = 0` identically. -/
theorem eta_zero (mt w g : Shell q) (hw : mt * w = 1) : (mt * g) * w = g := by
  rw [mul_assoc, mul_comm g w, ← mul_assoc, hw, one_mul]

/-! ## 22:C16 — the doublet readout is `σ_x` -/

/-- 22:C16 — an element of order `16` has `v⁸ = −1`: the half-turn supplies the sign. -/
theorem half_turn_sixteen (hq : FRC.Nat.isPrime q) {v : Shell q} (hv : HasOrder v 16) : v ^ 8 = -1 := by
  have hsq : v ^ 8 * v ^ 8 = 1 := by rw [← pow_add]; exact hv.2.1
  match sq_eq_one hq hsq with
  | .inl e => exact absurd e (hv.2.2 8 (by decide) (by decide))
  | .inr e => exact e

/-- The square of an element of order `16` has order `8`. -/
theorem order_eight_of_sixteen (hq : FRC.Nat.isPrime q) {v : Shell q} (hv : HasOrder v 16) : HasOrder (v ^ 2) 8 := by
  refine ⟨by decide, by rw [← pow_mul]; exact hv.2.1, fun l hl hl0 e => ?_⟩
  rw [← pow_mul] at e
  exact hv.2.2 (2 * l) (Nat.mul_lt_mul_of_pos_left hl (by decide)) (Nat.mul_pos (by decide) hl0) e

/-- 22:C16 — **the forced readout is `σ_x`**: on the `C_{16}` Object `⟨v⟩` read by a core-`C_8` Subject
(`ω = v²` the core's generator), the doublet state `u^k + λ u^{k+8}` registers on the matched channel `r = k mod 8`
over the two cosets `s ∈ {0, 1}` (the fibre `v^s ⟨ω⟩`) as `Ψ(s) = 8 v^{sk} (1 + λ (v⁸)^s)`, that is `Ψ(0) = 8(1 + λ)`
and `Ψ(1) = 8 v^k (1 − λ)` by the half-turn `v⁸ = −1` (`half_turn_sixteen`). -/
theorem doublet_readout (hq : FRC.Nat.isPrime q) {v : Shell q} (hv : HasOrder v 16) (k s : Nat) (lam : Shell q) :
    sumRange (fun j => ((v ^ s * (v ^ 2) ^ j) ^ k + lam * (v ^ s * (v ^ 2) ^ j) ^ (k + 8)) *
      (v ^ 2) ^ ((8 - k % 8) * j)) 8 = ofNat 8 * (v ^ (s * k) * (1 + lam * (v ^ 8) ^ s)) := by
  have hω := order_eight_of_sixteen hq hv
  have e1 : ∀ j, ((v ^ s * (v ^ 2) ^ j) ^ k + lam * (v ^ s * (v ^ 2) ^ j) ^ (k + 8)) * (v ^ 2) ^ ((8 - k % 8) * j) =
      (v ^ (s * k) * (1 + lam * (v ^ 8) ^ s)) * ((v ^ 2) ^ (k * j) * (v ^ 2) ^ ((8 - k % 8) * j)) := fun j => by
    have h8 : ((v ^ 2) ^ j) ^ 8 = 1 := by rw [pow_mul_comm, hω.2.1, one_pow]
    have ha : (v ^ s * (v ^ 2) ^ j) ^ k = v ^ (s * k) * (v ^ 2) ^ (k * j) := by
      rw [mul_pow, ← pow_mul v s k, ← pow_mul (v ^ 2) j k, Nat.mul_comm j k]
    have hb : (v ^ s * (v ^ 2) ^ j) ^ (k + 8) = v ^ (s * k) * (v ^ 8) ^ s * (v ^ 2) ^ (k * j) := by
      rw [mul_pow, pow_add, pow_add, h8, mul_one, ← pow_mul v s k, ← pow_mul v s 8, ← pow_mul (v ^ 2) j k,
        Nat.mul_comm s 8, pow_mul v 8 s, Nat.mul_comm j k]
    rw [ha, hb]
    exact Shell.Frame.RE.sound (Shell.Frame.look [v ^ (s * k), (v ^ 2) ^ (k * j), lam, (v ^ 8) ^ s,
      (v ^ 2) ^ ((8 - k % 8) * j)])
      (.mul (.add (.mul (.var 0) (.var 1)) (.mul (.var 2) (.mul (.mul (.var 0) (.var 3)) (.var 1)))) (.var 4))
      (.mul (.mul (.var 0) (.add .one (.mul (.var 2) (.var 3)))) (.mul (.var 1) (.var 4)))
      (by decide +kernel)
  rw [sum_congr 8 (fun j _ => e1 j), sum_mul_left, selection hq hω k (Nat.mod_lt k (by decide)), if_pos rfl,
    mul_comm]

/-! ## 22:C17, X7, P3 — the Tsirelson square and no-signalling -/

/-- 22:C17, 22:X7, 22:C25, 22:P3 — the Tsirelson square: `S = 2(ζ + ζ⁷)` for `ζ⁴ = −1` has `S² = 8` on every shell, the shadow of the
ring identity `S² = 8` in `ℤ[ζ₈]`. -/
theorem singlet_square {ζ : Shell q} (h4 : ζ ^ 4 = -1) : (2 * (ζ + ζ ^ 7)) * (2 * (ζ + ζ ^ 7)) = 8 := by
  rw [mul_mul_mul_comm, tsirelson h4]
  show ofNat 2 * ofNat 2 * ofNat 2 = ofNat 8
  rw [ofNat_mul, ofNat_mul]

/-- 22:C17 — no-signalling: the marginal of one wing, `c(1 + E) + c(1 − E)` over the two outcomes of the other
(`c = 1/4`), is `2c`, independent of the correlator and so of the far setting. -/
theorem no_signalling (c E : Shell q) : c * (1 + E) + c * (1 + -E) = c * 2 := by
  rw [two_eq]
  exact Shell.Frame.RE.sound (Shell.Frame.look [c, E])
    (.add (.mul (.var 0) (.add .one (.var 1))) (.mul (.var 0) (.add .one (.neg (.var 1)))))
    (.mul (.var 0) (.add .one .one)) (by decide +kernel)

/-! ## 22:C19, P1 — the channel complementarity -/

/-- 22:C19, 22:P1 — **`V² + C² = 1`** on every shell: for a unit phase `x` with inverse `y`, the visibility
`V = (x + y)/2` and the concurrence `C = (x − y)/(2i)` (`h = 1/2`, `i² = −1`, `1/i = −i`) satisfy `V² + C² = 1`
exactly, the which-path complementarity of the pure gravitational channel. -/
theorem channel_complementarity {h x y i : Shell q} (hh : h * 2 = 1) (hxy : x * y = 1) (hi : i * i = -1) :
    (h * (x + y)) * (h * (x + y)) + (h * (x + -y) * -i) * (h * (x + -y) * -i) = 1 := by
  have e : (h * (x + y)) * (h * (x + y)) + (h * (x + -y) * -i) * (h * (x + -y) * -i) =
      (h * 2) * (h * 2) * (x * y) + h * h * ((x + -y) * (x + -y)) * (i * i + 1) := by
    rw [two_eq]
    exact Shell.Frame.RE.sound (Shell.Frame.look [h, x, y, i]) (.add (.mul (.mul (.var 0) (.add (.var 1) (.var 2))) (.mul (.var 0) (.add (.var 1) (.var 2)))) (.mul (.mul (.mul (.var 0) (.add (.var 1) (.neg (.var 2)))) (.neg (.var 3))) (.mul (.mul (.var 0) (.add (.var 1) (.neg (.var 2)))) (.neg (.var 3))))) (.add (.mul (.mul (.mul (.var 0) (.add .one .one)) (.mul (.var 0) (.add .one .one))) (.mul (.var 1) (.var 2))) (.mul (.mul (.mul (.var 0) (.var 0)) (.mul (.add (.var 1) (.neg (.var 2))) (.add (.var 1) (.neg (.var 2))))) (.add (.mul (.var 3) (.var 3)) .one))) (by decide +kernel)
  rw [e, hh, hxy, hi, neg_add, mul_zero, mul_one, mul_one, add_zero]

/-- 22:C19 — at zero coupling the branch state is a product: the concurrence vanishes, `C = h (x − x)(−i) = 0`. -/
theorem channel_product_at_zero (h x i : Shell q) : h * (x + -x) * -i = 0 := by
  rw [add_neg, mul_zero, zero_mul]

/-! ## 22:C20 — no collapse, exact revival -/

/-- 22:C20 — the drive conserves the ledger norm: a unit phase `u` (`u ū = 1`) leaves `a ā` unchanged, so an isolated
superposition keeps unit fringe contrast at every drive time. -/
theorem drive_norm {u ub : Shell q} (hu : u * ub = 1) (a ab : Shell q) : (u * a) * (ub * ab) = a * ab := by
  rw [mul_mul_mul_comm, hu, one_mul]

/-- 22:C20 — the exact revival: the visibility `V(t) = Σ_E p_E ζ^{E t}` returns to `Σ_E p_E` at the recurrence `n`
(`ζ^n = 1`): dephasing, never collapse. -/
theorem revival {ζ : Shell q} {n : Nat} (hn : ζ ^ n = 1) (p : Nat → Shell q) (M : Nat) :
    sumRange (fun E => p E * ζ ^ (E * n)) M = sumRange p M :=
  sum_congr M (fun E _ => by rw [Nat.mul_comm, pow_mul, hn, one_pow, mul_one])

/-! ## 22:C21 — the coherent-fraction channel -/

/-- A constant product is a power. -/
theorem prodRange_const (x : Shell q) : ∀ m, prodRange (fun _ => x) m = x ^ m
  | 0 => rfl
  | m + 1 => by show prodRange (fun _ => x) m * x = x ^ (m + 1); rw [prodRange_const x m, pow_succ]

/-- 22:C21 (ii), 22:P1 — the branch phase of `m_c` synchronised cells is the coherent product `ζ^{m_c a}`. -/
theorem branch_phase (ζ : Shell q) (a mc : Nat) : prodRange (fun _ => ζ ^ a) mc = ζ ^ (mc * a) := by
  rw [prodRange_const, ← pow_mul, Nat.mul_comm]

/-- 22:C21 (ii) — the pairwise law: the phase of `m₁` against `m₂` synchronised cells is `ζ^{m₁ m₂ a}`. -/
theorem pair_product (ζ : Shell q) (a m1 m2 : Nat) : (ζ ^ (m1 * a)) ^ m2 = ζ ^ (m1 * m2 * a) := by
  rw [← pow_mul, FRC.Nat.mul_assoc, Nat.mul_comm a m2, ← FRC.Nat.mul_assoc]

/-- 22:C21 (iii) — a complete sector sum vanishes: the offset-spread cells' phases cancel over one cycle. -/
theorem spread_cancels (hq : FRC.Nat.isPrime q) {ζ : Shell q} {n : Nat} (hζ : HasOrder ζ n) (hζ1 : ζ ≠ 1) :
    sumRange (fun θ => ζ ^ θ) n = 0 := geom_sum_zero hq n hζ.2.1 hζ1

/-- 22:C21 (iii), 22:P1 — the reduced channel factorises: the offset distribution's partial sum times the coherent phase,
`Σ_θ p_θ ζ^{θ + c} = (Σ_θ p_θ ζ^θ) ζ^c = χ_inc · ζ^{f φ}`. -/
theorem channel_assembly (ζ : Shell q) (p : Nat → Shell q) (n c : Nat) :
    sumRange (fun θ => p θ * ζ ^ (θ + c)) n = sumRange (fun θ => p θ * ζ ^ θ) n * ζ ^ c := by
  rw [← sum_mul_right]
  exact sum_congr n (fun θ _ => by rw [pow_add, mul_assoc])

/-! ## 22:C23, X4 — inter-Subject consistency -/

/-- 22:C23 (ii), 22:X4 — shared-core agreement: with the common core of order `e` dividing both cores `a`, `b`, the channels
`r ≡ k (mod a)` of `S` and `r' ≡ k (mod b)` of `S'` agree on the common core, `r ≡ r' (mod e)`: both induce the one
character `η_{k mod e}`. -/
theorem order_independence {a b e r r' k : Nat} (he : 0 < e) (ha : 0 < a) (hb : 0 < b) (hae : a % e = 0)
    (hbe : b % e = 0) (hr : r % a = k % a) (hr' : r' % b = k % b) : r % e = r' % e := by
  rw [← mod_mod_of_dvd (n := r) he ha hae, hr, mod_mod_of_dvd he ha hae, ← mod_mod_of_dvd (n := r') he hb hbe, hr',
    mod_mod_of_dvd he hb hbe]

/-- 22:C23 (i), 22:X4 — joint refinement: the common cosets of two cores (classes modulo `α` and modulo `β` on the Object
cycle) are the classes modulo one period `T`, the common core's, in either order; `T` lies below the product
`αβ` (`FRC.Quantum.joint_recurrence` on the two parts, the search bounded by `αβ`). -/
theorem joint_refinement (α β : Nat) (hα : 0 < α) (hβ : 0 < β) :
    ∃ T, T ≤ α * β ∧ 0 < T ∧ ∀ x, (x % α = 0 ∧ x % β = 0) ↔ x % T = 0 := by
  let n : Nat → Nat := fun j => if j = 0 then α else β
  have hn : ∀ j, 0 < n j := fun j => by
    show 0 < (if j = 0 then α else β)
    match Nat.decEq j 0 with
    | .isTrue e => rw [if_pos e]; exact hα
    | .isFalse e => rw [if_neg e]; exact hβ
  have hL : Joint n 2 (α * β) := fun j hj => by
    show (α * β) % (if j = 0 then α else β) = 0
    match j with
    | 0 => rw [if_pos rfl]; exact mod_zero_of_eq_mul hα rfl
    | 1 => rw [if_neg (by decide), Nat.mul_comm]; exact mod_zero_of_eq_mul hβ rfl
    | j + 2 => exact absurd hj (Nat.not_lt_of_le (Nat.le_add_left 2 j))
  obtain ⟨T, hTL, hT0, _, hiff, _⟩ := joint_recurrence n hn 2 (α * β) (Nat.mul_pos hα hβ) hL
  refine ⟨T, hTL, hT0, fun x => Iff.trans ?_ (hiff x)⟩
  constructor
  · intro ⟨h0, h1⟩ j hj
    show x % (if j = 0 then α else β) = 0
    match j with
    | 0 => rw [if_pos rfl]; exact h0
    | 1 => rw [if_neg (by decide)]; exact h1
    | j + 2 => exact absurd hj (Nat.not_lt_of_le (Nat.le_add_left 2 j))
  · intro h
    constructor
    · have := h 0 (by decide)
      exact (show x % (if 0 = 0 then α else β) = 0 from this) |> fun e => by rwa [if_pos rfl] at e
    · have := h 1 (by decide)
      exact (show x % (if 1 = 0 then α else β) = 0 from this) |> fun e => by rwa [if_neg (by decide)] at e

/-! ## The worked carriers (Table `tab:configs`), decided by the kernel -/

instance decHasOrder {p : Nat} [Pos p] (x : Shell p) (n : Nat) : Decidable (HasOrder x n) :=
  have : Decidable (∀ l, l < n → 0 < l → x ^ l ≠ 1) := FRC.Shell.decForallLT (fun l => 0 < l → x ^ l ≠ 1) n
  inferInstanceAs (Decidable (0 < n ∧ x ^ n = 1 ∧ ∀ l, l < n → 0 < l → x ^ l ≠ 1))

/-- 22:C24, the worked carrier `𝔽₁₅₇` (`κ = 39`): `g = 5` is primitive, the quarter-turn `I = g^{−39} = g^{117} = 28`,
`I² = −1`; the Subject `S₅₃` has the cycle `C₅₂ = ⟨g³ = 125⟩`, the Object `O₁₃` the cycle `C₁₂ = ⟨g¹³ = 22⟩`, the core
`Q₄` (`gcd(52, 12) = 4`), three outcomes (`12/4 = 3`). -/
theorem carrier_157 :
    (157 : Nat) = 4 * 39 + 1 ∧ HasOrder (5 : Shell 157) 156 ∧ (5 : Shell 157) ^ 117 = 28 ∧
    (28 : Shell 157) * 28 = -1 ∧ (5 : Shell 157) ^ 3 = 125 ∧ HasOrder (125 : Shell 157) 52 ∧
    (5 : Shell 157) ^ 13 = 22 ∧ HasOrder (22 : Shell 157) 12 ∧
    (52 % 4 = 0 ∧ 12 % 4 = 0 ∧ ∀ e, e < 53 → 52 % e = 0 → 12 % e = 0 → 4 % e = 0) ∧ 12 = 4 * 3 := by
  decide +kernel

/-- 22:C24, 22:X5 — the worked carrier `𝔽₄₂₁` (`κ = 105`): `g = 2` is primitive, `I = g^{−105} = g^{315} = 392`, `I² = −1`;
the Subject `S₆₁` (`C₆₀`) resolves `O₂₉` (`C₂₈`) through the core `Q₄` (`gcd(60, 28) = 4`) in seven outcomes
(`28 = 4 · 7`) and absorbs `O₁₃` (`C₁₂`, `gcd(60, 12) = 12`, one outcome): quantumness is the subgroup index. -/
theorem carrier_421 :
    (421 : Nat) = 4 * 105 + 1 ∧ HasOrder (2 : Shell 421) 420 ∧ (2 : Shell 421) ^ 315 = 392 ∧
    (392 : Shell 421) * 392 = -1 ∧
    (60 % 4 = 0 ∧ 28 % 4 = 0 ∧ ∀ e, e < 61 → 60 % e = 0 → 28 % e = 0 → 4 % e = 0) ∧ 28 = 4 * 7 ∧
    (60 % 12 = 0 ∧ 12 % 12 = 0 ∧ ∀ e, e < 61 → 60 % e = 0 → 12 % e = 0 → 12 % e = 0) ∧ 12 = 12 * 1 := by
  decide +kernel

/-- 22:C16, 22:C17 — the worked carrier `𝔽₆₄₁` (`κ = 160`): `g = 3` is primitive; the Object generator `g_O = g⁴⁰ = 601`
has order `16` and `g_O⁸ = −1` (the doublet's sign); the setting step `ζ₈₀ = g⁸ = 151` has order `80`; the octant
`ζ₈ = g⁸⁰ = 318` has `ζ₈⁴ = −1`, `(ζ₈ + ζ₈⁷)² = 2` and `S² = 8`; the Bell core is `C₈` (`gcd(40, 16) = 8`). -/
theorem carrier_641 :
    (641 : Nat) = 4 * 160 + 1 ∧ HasOrder (3 : Shell 641) 640 ∧ (3 : Shell 641) ^ 40 = 601 ∧
    HasOrder (601 : Shell 641) 16 ∧ (601 : Shell 641) ^ 8 = -1 ∧ (3 : Shell 641) ^ 8 = 151 ∧
    HasOrder (151 : Shell 641) 80 ∧ (3 : Shell 641) ^ 80 = 318 ∧ (318 : Shell 641) ^ 4 = -1 ∧
    (318 + (318 : Shell 641) ^ 7) * (318 + (318 : Shell 641) ^ 7) = 2 ∧
    (2 * (318 + (318 : Shell 641) ^ 7)) * (2 * (318 + (318 : Shell 641) ^ 7)) = 8 ∧
    (40 % 8 = 0 ∧ 16 % 8 = 0 ∧ ∀ e, e < 41 → 40 % e = 0 → 16 % e = 0 → 8 % e = 0) := by
  decide +kernel

end FRC.Composite
