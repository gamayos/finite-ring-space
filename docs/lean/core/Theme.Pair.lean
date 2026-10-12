import FrcCore.Theme.Subject

/-!
# FrcCore.Theme.Pair — the pair `(p, Ω)`: the window, the leak rate, the joint cycle, the tick arithmetic and the
covering parity theorem (the subject theme's second file; 38-s13, 12 October 2026)

The arithmetic of a Subject `p = 4κ + 1` hosted by a Carrier `Ω = 4S + 1`, from *The Light Cone of the Minimal Pair*
(tree `38-s13-20260801`), on the naturals and on the shell:

* **38:A2** the tower congruence `4a − κb = 1` has a solution for every odd `κ` (`tower_solvable`);
* **38:A8, 38:B2** the resolvable window: `4k < p` exactly when `k ≤ κ`, and two window heights conserve exactly,
  `k₁ + k₂ ≤ 2κ < 4κ` (`window`, `window_sum`);
* **38:C10, 38:X1, 38:X3** the per-chronon leak rate `(κ/S)/(p − 1) = 1/(4S) = 1/(Ω − 1)`, `κ`-free, as integer
  identities (`leak_rate`);
* **38:C14, 38:B5, 38:B7** the joint cycle of a `κ`-odd pair with `S ≡ 2 (mod 4)`: for `ℓ` an odd common multiple of
  `κ = 2a + 1` and `S/2 = 2b + 1`, the shell is home and the Carrier reads the half at `4ℓ` ticks, both home at `8ℓ`
  (`joint_cycle`); on frames, `g^{4ℓ} = 1` and `h^{4ℓ} = −1` (`joint_cycle_frame`);
* **38:C1, 38:C4, 38:C5** the flow law as a tick count on the cycle, home at the row's own clock and the parity image
  half a cycle on (`tick`, `tick_home`, `tick_half`); the half turn as the point reflection (`half_turn`);
* **38:D12** the covering parity theorem: the reflection identity `⌊ab/p⌋ + ⌊(p − a)b/p⌋ = b − 1` on a prime shell
  (`reflection_identity`), the four candidate identities and the multiplicity `μ ∈ {1, 3}` with `μ = 3` exactly on the
  even rows and the position law of the odd sector (`covering_parity`), the quotients taken as the division
  algorithm's (`FRC.Nat.mod_spec`, `quot_unique`), the parities decided by the kernel on the eight-case table.

No prelude division lemma is used (they carry `propext`); the quotients are named by their defining equations. No axioms.
-/

namespace FRC.Pair

open FRC.Shell

/-! ## 38:A2 — the tower congruence -/

/-- 38:A2 — the tower congruence `4a − κb = 1` is solvable for every odd `κ`: `(a, b) = ((3κ + 1)/4, 3)` for
`κ ≡ 1 (mod 4)` and `((κ + 1)/4, 1)` for `κ ≡ 3 (mod 4)` — the instances `(1, 1)` at `κ = 3`, `(4, 3)` at `κ = 5`,
`(2, 1)` at `κ = 7`. -/
theorem tower_solvable (κ : Nat) (hκ : κ % 2 = 1) : ∃ a b : Nat, 4 * a = κ * b + 1 := by
  obtain ⟨q, hq⟩ := FRC.Nat.mod_spec 4 (by decide) κ
  have hr : κ % 4 = 1 ∨ κ % 4 = 3 := by
    have h2 : (4 * q + κ % 4) % 2 = 1 := by rw [← hq]; exact hκ
    have e4 : 4 * q = 2 * (2 * q) := by rw [← FRC.Nat.mul_assoc]
    rw [e4, FRC.Nat.add_mul_mod_self_left (κ % 4) (2 * q) 2 (by decide)] at h2
    have key : ∀ r, r < 4 → r % 2 = 1 → r = 1 ∨ r = 3 := by decide
    exact key _ (Nat.mod_lt κ (by decide)) h2
  match hr with
  | .inl h1 =>
    refine ⟨3 * q + 1, 3, ?_⟩
    rw [hq, h1]
    calc 4 * (3 * q + 1) = 4 * (3 * q) + 4 := Nat.mul_add 4 (3 * q) 1
      _ = 4 * q * 3 + 4 := by rw [Nat.mul_comm 3 q, ← FRC.Nat.mul_assoc]
      _ = (4 * q + 1) * 3 + 1 := by rw [FRC.Nat.add_mul, Nat.one_mul, Nat.add_assoc]
  | .inr h3 =>
    refine ⟨q + 1, 1, ?_⟩
    rw [hq, h3, Nat.mul_one, Nat.mul_add, Nat.mul_one]

/-! ## 38:A8, 38:B2 — the resolvable window -/

/-- 38:A8, 38:B2, 38:D1 — the capacity clause: `4k < p = 4κ + 1` exactly when `k ≤ κ`; the window `|k̂| ≤ κ`, and the
radial ladder's `κ` shells. -/
theorem window (κ k : Nat) : 4 * k < 4 * κ + 1 ↔ k ≤ κ :=
  ⟨fun h => Nat.le_of_mul_le_mul_left (Nat.le_of_lt_succ h) (by decide : 0 < 4),
   fun h => Nat.lt_succ_of_le (Nat.mul_le_mul_left 4 h)⟩

/-- 38:A8 — pairwise conservation on the window is exact: two heights of magnitude at most `κ` sum to at most `2κ`,
strictly inside one period `4κ = p − 1`. -/
theorem window_sum {κ k₁ k₂ : Nat} (hκ : 0 < κ) (h₁ : k₁ ≤ κ) (h₂ : k₂ ≤ κ) :
    k₁ + k₂ ≤ 2 * κ ∧ 2 * κ < 4 * κ := by
  refine ⟨by rw [Nat.two_mul]; exact Nat.add_le_add h₁ h₂, ?_⟩
  have e : 4 * κ = 2 * κ + 2 * κ := FRC.Nat.add_mul 2 2 κ
  rw [e]; exact Nat.lt_add_of_pos_right (Nat.mul_pos (by decide) hκ)

/-! ## 38:C10 — the per-chronon leak rate -/

/-- 38:C10, 38:C7, 38:C13, 38:C14, 38:X1, 38:X3 — the leak rate per chronon is `κ`-free: `(κ/S)/(p − 1) = 1/(4S) = 1/(Ω − 1)`, as the integer
identities `κ · 4S = S · (p − 1)`, `4S = Ω − 1`, and the temporal face on the cover `2(Ω − 1) = 8S`. -/
theorem leak_rate {p Ω κ S : Nat} (hp : p = 4 * κ + 1) (hΩ : Ω = 4 * S + 1) :
    κ * (4 * S) = S * (p - 1) ∧ 4 * S = Ω - 1 ∧ 2 * (Ω - 1) = 8 * S := by
  have e1 : p - 1 = 4 * κ := by rw [hp]; exact FRC.Nat.add_sub_cancel (4 * κ) 1
  have e2 : Ω - 1 = 4 * S := by rw [hΩ]; exact FRC.Nat.add_sub_cancel (4 * S) 1
  refine ⟨?_, e2.symm, ?_⟩
  · rw [e1]
    calc κ * (4 * S) = 4 * S * κ := Nat.mul_comm κ (4 * S)
      _ = 4 * (S * κ) := FRC.Nat.mul_assoc 4 S κ
      _ = S * (4 * κ) := FRC.Nat.mul_left_comm 4 S κ
  · rw [e2, ← FRC.Nat.mul_assoc]

/-- A multiple of the modulus is `0` modulo it. -/
theorem mod_mul_self (p q : Nat) (hp : 0 < p) : (p * q) % p = 0 :=
  FRC.Nat.mod_unique hp (Nat.add_zero (p * q)).symm

/-! ## 38:C14 — the joint cycle -/

/-- 38:C14, 38:B5, 38:B7 — the joint cycle of a `κ`-odd pair with `S ≡ 2 (mod 4)`. With `κ = 2a + 1`, `S = 2(2b + 1)`
and `ℓ` an odd common multiple of `2a + 1` and `2b + 1` (`ℓ = (2a + 1)(2u + 1) = (2b + 1)(2v + 1)`): at `4ℓ` ticks the
shell is home (`4ℓ ≡ 0 mod 4κ = p − 1`) and the Carrier count reads the half (`4ℓ ≡ (Ω − 1)/2 mod Ω − 1 = 8(2b + 1)`);
at `8ℓ` both are home. At the instance `ℓ = 87 = 3 · 29`: `348` and `696`. -/
theorem joint_cycle {a b u v ℓ : Nat} (hu : ℓ = (2 * a + 1) * (2 * u + 1)) (hv : ℓ = (2 * b + 1) * (2 * v + 1)) :
    (4 * ℓ) % (4 * (2 * a + 1)) = 0 ∧ (4 * ℓ) % (8 * (2 * b + 1)) = 4 * (2 * b + 1) ∧
    (8 * ℓ) % (4 * (2 * a + 1)) = 0 ∧ (8 * ℓ) % (8 * (2 * b + 1)) = 0 := by
  have ha0 : 0 < 4 * (2 * a + 1) := Nat.mul_pos (by decide) (Nat.zero_lt_succ _)
  have hb0 : 0 < 8 * (2 * b + 1) := Nat.mul_pos (by decide) (Nat.zero_lt_succ _)
  have hb4 : 4 * (2 * b + 1) < 8 * (2 * b + 1) :=
    Nat.mul_lt_mul_of_pos_right (by decide : 4 < 8) (Nat.zero_lt_succ _)
  -- `4ℓ = (4(2a + 1)) (2u + 1)` and `8ℓ = (4(2a + 1)) (2(2u + 1))`
  have e1 : 4 * ℓ = 4 * (2 * a + 1) * (2 * u + 1) := by rw [hu, FRC.Nat.mul_assoc]
  have e3 : 8 * ℓ = 4 * (2 * a + 1) * (2 * (2 * u + 1)) := by
    rw [hu]
    calc 8 * ((2 * a + 1) * (2 * u + 1)) = 4 * (2 * ((2 * a + 1) * (2 * u + 1))) := FRC.Nat.mul_assoc 4 2 _
      _ = 4 * ((2 * a + 1) * (2 * (2 * u + 1))) := by rw [FRC.Nat.mul_left_comm 2 (2 * a + 1)]
      _ = 4 * (2 * a + 1) * (2 * (2 * u + 1)) := (FRC.Nat.mul_assoc 4 _ _).symm
  -- `4ℓ = 8(2b + 1) v + 4(2b + 1)` and `8ℓ = (8(2b + 1)) (2v + 1)`
  have e2 : 4 * ℓ = 8 * (2 * b + 1) * v + 4 * (2 * b + 1) := by
    rw [hv]
    calc 4 * ((2 * b + 1) * (2 * v + 1)) = 4 * ((2 * b + 1) * (2 * v) + (2 * b + 1)) := by
            rw [Nat.mul_add, Nat.mul_one]
      _ = 4 * ((2 * b + 1) * (2 * v)) + 4 * (2 * b + 1) := Nat.mul_add 4 _ _
      _ = 4 * (2 * ((2 * b + 1) * v)) + 4 * (2 * b + 1) := by rw [FRC.Nat.mul_left_comm (2 * b + 1) 2 v]
      _ = 4 * 2 * ((2 * b + 1) * v) + 4 * (2 * b + 1) := by rw [FRC.Nat.mul_assoc 4 2]
      _ = 8 * (2 * b + 1) * v + 4 * (2 * b + 1) := by rw [← FRC.Nat.mul_assoc 8]
  have e4 : 8 * ℓ = 8 * (2 * b + 1) * (2 * v + 1) := by rw [hv, FRC.Nat.mul_assoc]
  refine ⟨by rw [e1, mod_mul_self _ _ ha0], FRC.Nat.mod_unique hb4 e2, by rw [e3, mod_mul_self _ _ ha0],
    by rw [e4, mod_mul_self _ _ hb0]⟩

/-- 38:C14 on the frames: a Subject frame of odd capacity `κ = 2a + 1` and a Carrier frame of capacity `S = 4b + 2`
return together — at `4ℓ` the Subject's drive is home, `g^{4ℓ} = 1`, and the Carrier's reads the half, `h^{4ℓ} = −1`
(the sign event); at `8ℓ` both are home. -/
theorem joint_cycle_frame {p Ω : Nat} [Pos p] [Pos Ω] {a b : Nat} {g : Shell p} {h : Shell Ω}
    (F : Frame p (2 * a + 1) g) (G : Frame Ω (4 * b + 2) h) {u v ℓ : Nat}
    (hu : ℓ = (2 * a + 1) * (2 * u + 1)) (hv : ℓ = (2 * b + 1) * (2 * v + 1)) :
    g ^ (4 * ℓ) = 1 ∧ h ^ (4 * ℓ) = -1 ∧ g ^ (8 * ℓ) = 1 ∧ h ^ (8 * ℓ) = 1 := by
  obtain ⟨c1, c2, c3, c4⟩ := joint_cycle hu hv
  have eS : Ω - 1 = 8 * (2 * b + 1) := by
    rw [G.n_eq]; show 4 * (4 * b + 2) = 8 * (2 * b + 1)
    rw [Nat.mul_add, Nat.mul_add, ← FRC.Nat.mul_assoc, ← FRC.Nat.mul_assoc]
  have eH : 2 * (4 * b + 2) = 4 * (2 * b + 1) := by
    rw [Nat.mul_add, Nat.mul_add, ← FRC.Nat.mul_assoc, ← FRC.Nat.mul_assoc]
  refine ⟨F.pow_eq_one_of_mod (by rw [F.n_eq]; exact c1), ?_, F.pow_eq_one_of_mod (by rw [F.n_eq]; exact c3),
    G.pow_eq_one_of_mod (by rw [eS]; exact c4)⟩
  rw [G.pow_mod, eS, c2, ← eH]; exact G.half_period

/-- 38:C14 — the joint returns are exactly the common multiples of the two periods, so the least is `lcm(p − 1, Ω − 1)`;
for `κ` odd and `S ≡ 2 (mod 4)` it is `8ℓ`, `ℓ` the least odd common multiple of `κ` and `S/2` (`joint_cycle_frame`). -/
theorem joint_return_iff {p Ω : Nat} [Pos p] [Pos Ω] {κ S : Nat} {g : Shell p} {h : Shell Ω}
    (F : Frame p κ g) (G : Frame Ω S h) (n : Nat) :
    g ^ n = 1 ∧ h ^ n = 1 ↔ n % (p - 1) = 0 ∧ n % (Ω - 1) = 0 :=
  ⟨fun ⟨hg, hh⟩ => ⟨F.mod_eq_zero_of_pow_eq_one hg, G.mod_eq_zero_of_pow_eq_one hh⟩,
   fun ⟨hg, hh⟩ => ⟨F.pow_eq_one_of_mod hg, G.pow_eq_one_of_mod hh⟩⟩

/-- 38:C14 — every common multiple of the periods `4κ` (`κ = 2a + 1` odd) and `8·(S/2)` (`S/2 = 2b + 1`) is eight times a
common multiple of `κ` and `S/2`: with `joint_return_iff`, the least joint return is `8ℓ` for `ℓ` the least common
multiple of `κ` and `S/2` (odd), and its half `4ℓ` is `joint_cycle_frame`'s sign event. -/
theorem joint_return_eight {a b n : Nat} (h4 : n % (4 * (2 * a + 1)) = 0) (h8 : n % (8 * (2 * b + 1)) = 0) :
    ∃ m, n = 8 * m ∧ m % (2 * a + 1) = 0 ∧ m % (2 * b + 1) = 0 := by
  have ha0 : 0 < 4 * (2 * a + 1) := Nat.mul_pos (by decide) (Nat.zero_lt_succ _)
  have hb0 : 0 < 8 * (2 * b + 1) := Nat.mul_pos (by decide) (Nat.zero_lt_succ _)
  obtain ⟨v, hv⟩ := FRC.Nat.mod_spec _ hb0 n
  obtain ⟨u, hu⟩ := FRC.Nat.mod_spec _ ha0 n
  rw [h8, Nat.add_zero] at hv
  rw [h4, Nat.add_zero] at hu
  refine ⟨(2 * b + 1) * v, by rw [hv, FRC.Nat.mul_assoc], ?_, mod_mul_self _ _ (Nat.zero_lt_succ _)⟩
  have e : (2 * a + 1) * u = 2 * ((2 * b + 1) * v) := by
    apply Nat.eq_of_mul_eq_mul_left (show 0 < 4 by decide)
    calc 4 * ((2 * a + 1) * u) = 4 * (2 * a + 1) * u := (FRC.Nat.mul_assoc _ _ _).symm
      _ = 8 * (2 * b + 1) * v := hu.symm.trans hv
      _ = 4 * (2 * ((2 * b + 1) * v)) := by
        show 4 * 2 * (2 * b + 1) * v = 4 * (2 * ((2 * b + 1) * v))
        rw [FRC.Nat.mul_assoc (4 * 2), FRC.Nat.mul_assoc 4 2]
  obtain ⟨k, hk⟩ := FRC.Nat.mod_spec 2 (by decide) u
  rcases FRC.Nat.mod_two_cases u with h0 | h1
  · rw [h0, Nat.add_zero] at hk
    rw [hk, FRC.Nat.mul_left_comm] at e
    rw [← Nat.eq_of_mul_eq_mul_left (show 0 < 2 by decide) e]
    exact mod_mul_self _ _ (Nat.zero_lt_succ _)
  · rw [h1] at hk
    rw [hk, Nat.mul_add, Nat.mul_one, FRC.Nat.mul_left_comm, ← Nat.add_assoc, Nat.add_comm (2 * ((2 * a + 1) * k)) (2 * a),
      ← Nat.mul_add] at e
    -- `2 (a + (2a + 1) k) + 1 = 2 m'`: odd against even
    have h1' : (2 * (a + (2 * a + 1) * k) + 1) % 2 = 1 := FRC.Nat.mod_unique (by decide) rfl
    rw [e, mod_mul_self _ _ (by decide)] at h1'
    exact absurd h1' (by decide)

/-! ## 38:C1, 38:C4, 38:C5 — the tick arithmetic of the flow -/

/-- 38:C1 — the flow law as a tick count: on the cycle of `n` ticks, row `k` at clock `b` stands at
`(k − b) mod n`, read as `(k + (n − b mod n)) mod n`; the law `φ(k) = −(b_C − k)π/116` is this count in units of
`2π/232`. -/
def tick (n k b : Nat) : Nat := (k + (n - b % n)) % n

/-- 38:C1, 38:C5 — home: at the row's own clock the count is `0`. -/
theorem tick_home (n : Nat) (hn : 0 < n) (k : Nat) : tick n k k = 0 := by
  obtain ⟨q, hq⟩ := FRC.Nat.mod_spec n hn k
  have hle : k % n ≤ n := Nat.le_of_lt (FRC.Nat.mod_lt' k hn)
  have e : k + (n - k % n) = n * (q + 1) + 0 := by
    rw [Nat.add_zero, Nat.mul_add, Nat.mul_one]
    calc k + (n - k % n) = n * q + k % n + (n - k % n) := by rw [← hq]
      _ = n * q + (k % n + (n - k % n)) := Nat.add_assoc _ _ _
      _ = n * q + n := by rw [FRC.Nat.add_sub_of_le hle]
  exact FRC.Nat.mod_unique hn e

/-- 38:C5, 38:B7 — the parity image: half a cycle on from the row's own clock the count is the half, `m` on `2m` ticks
(`116` on `C₂₃₂`: `b_C = 116 + k`). -/
theorem tick_half (m : Nat) (hm : 0 < m) (k : Nat) : tick (2 * m) k (k + m) = m := by
  have h2 : 0 < 2 * m := Nat.mul_pos (by decide) hm
  obtain ⟨q, hq⟩ := FRC.Nat.mod_spec (2 * m) h2 (k + m)
  have hle : (k + m) % (2 * m) ≤ 2 * m := Nat.le_of_lt (FRC.Nat.mod_lt' (k + m) h2)
  -- `tick + m ≡ 0`: `k + (2m − r) + m = (k + m) + (2m − r) = 2m q + r + (2m − r) = 2m (q + 1)`
  have e : k + (2 * m - (k + m) % (2 * m)) + m = 2 * m * (q + 1) + 0 := by
    rw [Nat.add_zero, Nat.mul_add, Nat.mul_one, Nat.add_right_comm]
    calc k + m + (2 * m - (k + m) % (2 * m))
        = 2 * m * q + (k + m) % (2 * m) + (2 * m - (k + m) % (2 * m)) := by rw [← hq]
      _ = 2 * m * q + ((k + m) % (2 * m) + (2 * m - (k + m) % (2 * m))) := Nat.add_assoc _ _ _
      _ = 2 * m * q + 2 * m := by rw [FRC.Nat.add_sub_of_le hle]
  have hz : (k + (2 * m - (k + m) % (2 * m)) + m) % (2 * m) = 0 := FRC.Nat.mod_unique h2 e
  -- the count `t < 2m` with `(t + m) % 2m = 0` is `m`
  unfold tick
  obtain ⟨s, hs⟩ := FRC.Nat.mod_spec (2 * m) h2 (k + (2 * m - (k + m) % (2 * m)))
  have ht := FRC.Nat.mod_lt' (k + (2 * m - (k + m) % (2 * m))) h2
  generalize (k + (2 * m - (k + m) % (2 * m))) % (2 * m) = t at hs ht hz
  generalize k + (2 * m - (k + m) % (2 * m)) = x at hs hz
  rw [hs, Nat.add_assoc, FRC.Nat.add_mul_mod_self_left _ _ _ h2] at hz
  obtain ⟨c, hc⟩ := FRC.Nat.mod_spec (2 * m) h2 (t + m)
  rw [hz, Nat.add_zero] at hc
  -- `t + m = 2m c` with `m ≤ t + m < 3m`: `c = 1`
  match c with
  | 0 => exact absurd (hc.trans (Nat.mul_zero _)) (Nat.ne_of_gt (Nat.lt_of_lt_of_le hm (Nat.le_add_left m t)))
  | 1 =>
    rw [Nat.mul_one, Nat.two_mul] at hc
    exact Nat.add_right_cancel hc
  | c + 2 =>
    have h3 : 2 * m * 2 ≤ 2 * m * (c + 2) := Nat.mul_le_mul_left _ (Nat.le_add_left 2 c)
    have hmle : m ≤ 2 * m := by rw [Nat.two_mul]; exact Nat.le_add_left m m
    have h4 : t + m < 2 * m * 2 := by
      rw [Nat.mul_comm (2 * m) 2, Nat.two_mul (2 * m)]
      exact Nat.lt_of_lt_of_le (Nat.add_lt_add_right ht m) (Nat.add_le_add_left hmle (2 * m))
    exact absurd (hc ▸ Nat.lt_of_lt_of_le h4 h3) (Nat.lt_irrefl _)

/-- 38:C4 — the half turn on the cycle of `2m` ticks is the point reflection: two half turns are the identity, the
reflection `x ↦ 2m − x` is the negation (`x + (2m − x) ≡ 0`), and the rim `m` is its own reflection (the rim kiss). -/
theorem half_turn (m : Nat) (hm : 0 < m) (x : Nat) :
    (x + m + m) % (2 * m) = x % (2 * m) ∧ (x + (2 * m - x % (2 * m))) % (2 * m) = 0 ∧
    (2 * m - m % (2 * m)) % (2 * m) = m % (2 * m) := by
  have h2 : 0 < 2 * m := Nat.mul_pos (by decide) hm
  have hm2 : m < 2 * m := by rw [Nat.two_mul]; exact Nat.lt_add_of_pos_right hm
  refine ⟨?_, tick_home (2 * m) h2 x, ?_⟩
  · rw [Nat.add_assoc, ← Nat.two_mul, FRC.Nat.add_mod x (2 * m) (2 * m) h2, FRC.Nat.mod_self _ h2, Nat.add_zero,
      FRC.Nat.mod_mod x _ h2]
  · rw [FRC.Nat.mod_eq_of_lt hm2]
    have e : 2 * m - m = m := by rw [Nat.two_mul]; exact FRC.Nat.add_sub_cancel m m
    rw [e, FRC.Nat.mod_eq_of_lt hm2]

/-! ## 38:D12 — the reflection identity and the covering parity theorem -/

/-- 38:D12 — the reflection identity on a prime shell: for `0 < a, b < p` the quotients of `ab` and `(p − a)b` by `p`
sum to `b − 1`, `⌊ab/p⌋ + ⌊(p − a)b/p⌋ + 1 = b`. The quotients are the division algorithm's: `ab = p q₁ + (ab mod p)`
and `(p − a)b = p q₂ + ((p − a)b mod p)` (`FRC.Nat.mod_spec` names them, `quot_unique` makes them unique). -/
theorem reflection_identity {p a b q₁ q₂ : Nat} (hp : FRC.Nat.isPrime p) (ha0 : 0 < a) (ha : a < p)
    (hb0 : 0 < b) (hb : b < p) (h₁ : a * b = p * q₁ + (a * b) % p)
    (h₂ : (p - a) * b = p * q₂ + ((p - a) * b) % p) : q₁ + q₂ + 1 = b := by
  have hp0 : 0 < p := Nat.lt_of_lt_of_le (by decide) hp.1
  have hr1 := FRC.Nat.mod_lt' (a * b) hp0
  have hr2 := FRC.Nat.mod_lt' ((p - a) * b) hp0
  -- `ab mod p ≠ 0`: `p` prime, `a, b` nonzero residues
  have hne : (a * b) % p ≠ 0 := fun h0 =>
    match FRC.Nat.prime_mul_mod hp h0 with
    | .inl h => Nat.ne_of_gt ha0 (by rw [FRC.Nat.mod_eq_of_lt ha] at h; exact h)
    | .inr h => Nat.ne_of_gt hb0 (by rw [FRC.Nat.mod_eq_of_lt hb] at h; exact h)
  -- `pb = p (q₁ + q₂) + (r₁ + r₂)`
  have hsum : p * b = p * (q₁ + q₂) + ((a * b) % p + ((p - a) * b) % p) := by
    calc p * b = (a + (p - a)) * b := by rw [FRC.Nat.add_sub_of_le (Nat.le_of_lt ha)]
      _ = a * b + (p - a) * b := FRC.Nat.add_mul a (p - a) b
      _ = p * q₁ + (a * b) % p + (p * q₂ + ((p - a) * b) % p) := by rw [← h₁, ← h₂]
      _ = p * (q₁ + q₂) + ((a * b) % p + ((p - a) * b) % p) := by
        rw [Nat.mul_add, FRC.Nat.add_add_add_comm]
  -- the residues sum to `0` or `p`; not `0`
  have hmod : ((a * b) % p + ((p - a) * b) % p) % p = 0 := by
    have := FRC.Nat.add_mul_mod_self_left ((a * b) % p + ((p - a) * b) % p) (q₁ + q₂) p hp0
    rw [← hsum] at this
    rw [← this]; exact mod_mul_self p b hp0
  obtain ⟨c, hc⟩ := FRC.Nat.mod_spec p hp0 ((a * b) % p + ((p - a) * b) % p)
  rw [hmod, Nat.add_zero] at hc
  have hlt2 : (a * b) % p + ((p - a) * b) % p < p * 2 := by
    rw [Nat.mul_two]; exact Nat.add_lt_add hr1 hr2
  match c with
  | 0 =>
    rw [Nat.mul_zero] at hc
    exact absurd (Nat.eq_zero_of_le_zero (hc ▸ Nat.le_add_right _ _)) hne
  | 1 =>
    rw [Nat.mul_one] at hc
    rw [hc] at hsum
    have e : p * b = p * (q₁ + q₂ + 1) := by rw [hsum, Nat.mul_succ]
    exact (Nat.eq_of_mul_eq_mul_left hp0 e).symm
  | c + 2 =>
    have h3 : p * 2 ≤ p * (c + 2) := Nat.mul_le_mul_left p (Nat.le_add_left 2 c)
    exact absurd (hc ▸ Nat.lt_of_lt_of_le hlt2 h3) (Nat.lt_irrefl _)

/-- The multiplicity of a node from the wrap counts of its four candidate slots `(M, a)`, `(p − M, a)`, `(M, p − a)`,
`(p − M, p − a)`, which must be even, odd, odd, even in turn to land on the node's route. -/
def mu (A B C D : Nat) : Nat :=
  (if A % 2 = 0 then 1 else 0) + (if B % 2 = 1 then 1 else 0) + (if C % 2 = 1 then 1 else 0) +
    (if D % 2 = 0 then 1 else 0)

theorem mu_mod (A B C D : Nat) : mu A B C D = mu (A % 2) (B % 2) (C % 2) (D % 2) := by
  unfold mu
  rw [FRC.Nat.mod_mod A 2 (by decide), FRC.Nat.mod_mod B 2 (by decide), FRC.Nat.mod_mod C 2 (by decide),
    FRC.Nat.mod_mod D 2 (by decide)]

/-- 38:D12 — the eight-case parity table, decided by the kernel on the residues: with `x = ā`, `y = M̄`, `z = α = A mod 2`,
`u, v, t` the parities of `B, C, D` and `w = k̄`, the relations `k̄ = ā M̄ + α`, `A + B + 1 = a`, `A + C + 1 = M`,
`C + D + 1 = p − a` force `μ = 3` exactly when `k̄ = 0`, `μ ∈ {1, 3}`, and on an odd row the single match is a direct
slot (wrap `A` even or `B` odd, parameter `a`) exactly when `a` is odd. -/
theorem parity_table : ∀ x, x < 2 → ∀ y, y < 2 → ∀ z, z < 2 → ∀ u, u < 2 → ∀ v, v < 2 → ∀ t, t < 2 →
    ∀ w, w < 2 → (z + w) % 2 = (x * y) % 2 → (z + u + 1) % 2 = x → (z + v + 1) % 2 = y → (v + t + 1) % 2 = (1 + x) % 2 →
    (mu z u v t = 3 ↔ w = 0) ∧ (mu z u v t = 1 ∨ mu z u v t = 3) ∧ (w = 1 → (x = 1 ↔ (z = 0 ∨ u = 1))) := by
  decide

/-- Two residues mod 2 from a sum: `(s + x) % 2 = 1` with `s, x < 2` gives `s = (1 + x) % 2`. -/
theorem odd_sum_residue : ∀ s, s < 2 → ∀ x, x < 2 → (s + x) % 2 = 1 → s = (1 + x) % 2 := by decide

/-- 38:D12, 38:D7 — **the covering parity theorem** (Theorem *The covering parity theorem*, Lemma *The all-shell parity
table*). On an odd prime shell `p`, a node of shell `a` and row `k` (`0 < a, k < p`) with `M = k a⁻¹` (`aM ≡ k`,
`0 < M < p`) has the four candidate slots with wrap counts `A = ⌊aM/p⌋`, `B = ⌊(p − M)a/p⌋`, `C = ⌊M(p − a)/p⌋`,
`D = ⌊(p − M)(p − a)/p⌋`, the quotients of the division algorithm. Then the reflection identity four ways,
`A + B + 1 = a`, `A + C + 1 = M`, `C + D + 1 = p − a`, `B + D + 1 = p − M`; `aM = pA + k` exactly; and the multiplicity
`μ = mu A B C D` of the node satisfies `μ = 3` exactly when `k` is even, `μ ∈ {1, 3}` (so no node is missed), and on an
odd row the single match is direct (`A` even or `B` odd, parameter `a`) exactly when the shell `a` is odd. -/
theorem covering_parity {p a k M A B C D : Nat} (hp : FRC.Nat.isPrime p) (hodd : p % 2 = 1)
    (ha0 : 0 < a) (ha : a < p) (_hk0 : 0 < k) (hk : k < p) (hM0 : 0 < M) (hM : M < p)
    (hA : a * M = p * A + k)
    (hB : (p - M) * a = p * B + ((p - M) * a) % p)
    (hC : M * (p - a) = p * C + (M * (p - a)) % p)
    (hD : (p - M) * (p - a) = p * D + ((p - M) * (p - a)) % p) :
    (A + B + 1 = a ∧ A + C + 1 = M ∧ C + D + 1 = p - a ∧ B + D + 1 = p - M) ∧
    (mu A B C D = 3 ↔ k % 2 = 0) ∧ (mu A B C D = 1 ∨ mu A B C D = 3) ∧
    (k % 2 = 1 → (a % 2 = 1 ↔ (A % 2 = 0 ∨ B % 2 = 1))) := by
  have hp0 : 0 < p := Nat.lt_of_lt_of_le (by decide) hp.1
  have hpa0 : 0 < p - a := FRC.Nat.le_sub_of_add_le (by rw [Nat.add_comm]; exact Nat.succ_le_of_lt ha)
  have hpa : p - a < p := Nat.sub_lt hp0 ha0
  have hpM0 : 0 < p - M := FRC.Nat.le_sub_of_add_le (by rw [Nat.add_comm]; exact Nat.succ_le_of_lt hM)
  have hpM : p - M < p := Nat.sub_lt hp0 hM0
  -- `A` is the quotient of `aM`: `aM mod p = k`
  have hA' : a * M = p * A + (a * M) % p := by rw [FRC.Nat.mod_unique hk hA]; exact hA
  have hMa : M * a = p * A + (M * a) % p := by rw [Nat.mul_comm M a]; exact hA'
  have hB' : (p - M) * a = p * B + ((p - M) * a) % p := hB
  have hCb : (p - a) * M = p * C + ((p - a) * M) % p := by rw [Nat.mul_comm (p - a) M]; exact hC
  have hDb : (p - a) * (p - M) = p * D + ((p - a) * (p - M)) % p := by
    rw [Nat.mul_comm (p - a) (p - M)]; exact hD
  have haM : a * (p - M) = p * B + (a * (p - M)) % p := by rw [Nat.mul_comm a (p - M)]; exact hB'
  have hMpa : M * (p - a) = p * C + (M * (p - a)) % p := hC
  have i1 : A + B + 1 = a := reflection_identity hp hM0 hM ha0 ha hMa hB'
  have i2 : A + C + 1 = M := reflection_identity hp ha0 ha hM0 hM hA' hCb
  have i3 : C + D + 1 = p - a := reflection_identity hp hM0 hM hpa0 hpa hMpa hD
  have i4 : B + D + 1 = p - M := reflection_identity hp ha0 ha hpM0 hpM haM hDb
  refine ⟨⟨i1, i2, i3, i4⟩, ?_⟩
  -- the parities: every relation read modulo `2`
  have two : 0 < 2 := by decide
  have r1 : (A % 2 + k % 2) % 2 = (a % 2 * (M % 2)) % 2 := by
    have e : (a * M) % 2 = (p * A + k) % 2 := by rw [hA]
    rw [FRC.Nat.mul_mod a M 2 two, FRC.Nat.add_mod (p * A) k 2 two, FRC.Nat.mul_mod p A 2 two, hodd, Nat.one_mul,
      FRC.Nat.mod_mod A 2 two] at e
    exact e.symm
  have r2 : (A % 2 + B % 2 + 1) % 2 = a % 2 := by
    rw [← i1, FRC.Nat.add_mod (A + B) 1 2 two, FRC.Nat.add_mod A B 2 two, FRC.Nat.mod_add_mod _ _ 2 two]
  have r3 : (A % 2 + C % 2 + 1) % 2 = M % 2 := by
    rw [← i2, FRC.Nat.add_mod (A + C) 1 2 two, FRC.Nat.add_mod A C 2 two, FRC.Nat.mod_add_mod _ _ 2 two]
  have r4 : (C % 2 + D % 2 + 1) % 2 = (1 + a % 2) % 2 := by
    have e : ((p - a) % 2 + a % 2) % 2 = 1 := by
      rw [← FRC.Nat.add_mod (p - a) a 2 two, FRC.Nat.sub_add_cancel (Nat.le_of_lt ha)]; exact hodd
    rw [← odd_sum_residue _ (FRC.Nat.mod_lt' (p - a) two) _ (FRC.Nat.mod_lt' a two) e, ← i3,
      FRC.Nat.add_mod (C + D) 1 2 two, FRC.Nat.add_mod C D 2 two, FRC.Nat.mod_add_mod _ _ 2 two]
  have t := parity_table (a % 2) (FRC.Nat.mod_lt' a two) (M % 2) (FRC.Nat.mod_lt' M two) (A % 2)
    (FRC.Nat.mod_lt' A two) (B % 2) (FRC.Nat.mod_lt' B two) (C % 2) (FRC.Nat.mod_lt' C two) (D % 2)
    (FRC.Nat.mod_lt' D two) (k % 2) (FRC.Nat.mod_lt' k two) r1 r2 r3 r4
  rw [mu_mod]
  exact t


/-! ## The instance (13, 233): the pair, the sky, the flow and the meridians, decided by the kernel (38-s13) -/

/-- The number of `x < n` with `P x` (as `Frame.natCount`, restated so that the subject theme stands without the frame file). -/
def count (P : Nat → Prop) [DecidablePred P] : Nat → Nat
  | 0 => 0
  | n + 1 => count P n + if P n then 1 else 0

/-- 38:A1 — the Subject frame `(13; 3, 2)`: `2` generates `𝔽₁₃^×`. -/
theorem pair_frame : Frame 13 3 (2 : Shell 13) := ⟨rfl, Nat.zero_lt_succ 2, by decide +kernel⟩


/-- 38:A1, 38:A2 — the pair `(13, 233)`: `p = 13 = 4·3 + 1`, `Ω = 233 = 4·58 + 1`, the drive `g = 2` (`pair_frame`),
`i = 5 = −g³ = g⁹`, `i² = −1`, and the tower identity `g = 3·5` with `3 = g⁴`, `3³ = 1`, `5⁴ = 1`; the frame is `pair_frame`. -/
theorem pair_register :
    (13 : Nat) = 4 * 3 + 1 ∧ (233 : Nat) = 4 * 58 + 1 ∧ (12 : Nat) = 4 * 3 ∧ 58 % 4 = 2 ∧ 58 % 3 = 1 ∧ 13 * 13 < 233 ∧
    (5 : Shell 13) = -(2 ^ 3) ∧ (2 : Shell 13) ^ 9 = 5 ∧ (5 : Shell 13) * 5 = -1 ∧ (2 : Shell 13) ^ 4 = 3 ∧
    (3 : Shell 13) * 5 = 2 ∧ (3 : Shell 13) ^ 3 = 1 ∧ (5 : Shell 13) ^ 4 = 1 ∧ (2 : Shell 13) ^ 12 = 1 ∧
    (2 : Shell 13) ^ 6 = -1 ∧ 4 * 1 = 3 * 1 + 1 := by decide +kernel

/-- 38:A3 — the channel at the instance: `gcd(12, 14) = 2`, `gcd(12, 28) = 4`, `N(i) = i² = −1` — as the divisor
facts the kernel decides: `2 ∣ 12, 14` and no `d > 2` divides both; `4 ∣ 12, 28` and no `d > 4` divides both. -/
theorem channel_instance :
    12 % 2 = 0 ∧ 14 % 2 = 0 ∧ (∀ d, d < 15 → 2 < d → ¬ (12 % d = 0 ∧ 14 % d = 0)) ∧
    12 % 4 = 0 ∧ 28 % 4 = 0 ∧ (∀ d, d < 29 → 4 < d → ¬ (12 % d = 0 ∧ 28 % d = 0)) ∧
    (5 : Shell 13) * 5 = -1 ∧ (5 : Shell 13) ^ 13 = 5 := by decide +kernel

/-- 38:A4 — the Carrier frame `(233; 58, 78)` and its quarter roots: `78⁵⁸ = 89 = h`, `h² = −1`, `ħ = 144 = −h`,
`ħh = 1`, `ħ + h = 0` (`= Ω`), `78¹¹⁶ = −1`, `78²³² = 1`; the octant `ζ₈ = 97`: `97² = 89`, `97⁴ = −1`, `97⁸ = 1`;
the Fibonacci convergents `h = 13/8`, `ħ = 8/13` on `𝔽₂₃₃` and `233 = 13² + 8²`. -/
theorem carrier_frame : Frame 233 58 (78 : Shell 233) := ⟨rfl, Nat.zero_lt_succ 57, by decide +kernel⟩

/-- 38:A4 — the Carrier quarter roots as the kernel decides them (the clauses of `carrier_frame`'s docstring), with
`78²⁹ = 97` and the Fibonacci steps `233 = 144 + 89`, `144 = 89 + 55`, `89 = 55 + 34`, `13 = 8 + 5`. -/
theorem carrier_roots :
    (78 : Shell 233) ^ 58 = 89 ∧ (89 : Shell 233) * 89 = -1 ∧ (144 : Shell 233) = -89 ∧ (144 : Shell 233) * 89 = 1 ∧
    (144 : Shell 233) + 89 = 0 ∧ (78 : Shell 233) ^ 116 = -1 ∧ (78 : Shell 233) ^ 232 = 1 ∧
    (97 : Shell 233) ^ 2 = 89 ∧ (97 : Shell 233) ^ 4 = -1 ∧ (97 : Shell 233) ^ 8 = 1 ∧ (78 : Shell 233) ^ 29 = 97 ∧
    (89 : Shell 233) * 8 = 13 ∧ (144 : Shell 233) * 13 = 8 ∧ (233 : Nat) = 13 * 13 + 8 * 8 ∧
    (233 : Nat) = 144 + 89 ∧ (144 : Nat) = 89 + 55 ∧ (89 : Nat) = 55 + 34 ∧ (13 : Nat) = 8 + 5 := by decide +kernel

/-- 38:A6 — the FRC algebra half on `𝔽₁₃`: `2⁻¹ = 7`, `−2⁻¹ = 6`, `2·6 = −1`; the seam `13/2` lies between the rows
`6` and `7`. -/
theorem half_instance :
    (2 : Shell 13) * 7 = 1 ∧ (6 : Shell 13) = -7 ∧ (2 : Shell 13) * 6 = -1 ∧ 6 * 2 < 13 ∧ 13 < 7 * 2 := by
  decide +kernel

/-- 38:A8, 38:B2 — the resolvable window at the instance: `4|k̂| < 13` exactly for `|k̂| ≤ 3`, the window `{0, ±1, ±2, ±3}`;
the symmetric heights `k̂ ∈ {−5, …, 6}` of `C₁₂`; two window heights sum within `6 < 12`. -/
theorem window_instance :
    (∀ k, k < 13 → (4 * k < 13 ↔ k ≤ 3)) ∧ (∀ k₁, k₁ < 4 → ∀ k₂, k₂ < 4 → k₁ + k₂ ≤ 6) ∧ 6 < 12 ∧
    (2 * 3 - 1 : Nat) = 5 ∧ (2 * 3 : Nat) = 6 := by decide +kernel

/-! ## B. The sky -/

/-- The retarded label of row `k` at chronon `t` on the Subject: the cell's residue times the drive state `t − k`,
one chronon of lookback per row. -/
def label (k t : Nat) : Shell 13 := ofNat k * 2 ^ ((t + 12 - k % 12) % 12)

/-- 38:B1 — the node field `72 = 3·2·12` (three shells, two routes, twelve rows) and the retarded labels: every row's
label advances by the drive each chronon and returns after twelve. -/
theorem node_field :
    (3 : Nat) * 2 * 12 = 72 ∧
    (∀ k, k < 13 → ∀ t, t < 12 → label k (t + 1) = 2 * label k t ∧ label k (t + 12) = label k t) ∧
    (∀ k, k < 13 → label k k = ofNat k) := by decide +kernel

/-- 38:B3 — the mounting: `×3 = g⁴` (four drive steps, `3³ = 1`), `120° = 8` steps of `C₂₄` (`8 = 24/3`),
quarter-blind (`8 ≡ 4 ≡ 0 mod 4`, `4 ≡ 1 mod 3`); the count `3·48 + 12 = 156 = 13·12`. -/
theorem mounting :
    (2 : Shell 13) ^ 4 = 3 ∧ (3 : Shell 13) ^ 3 = 1 ∧ (3 : Shell 13) ^ 2 = 9 ∧ (8 : Nat) * 15 = 120 ∧
    (3 : Nat) * 8 = 24 ∧ 8 % 4 = 0 ∧ 4 % 4 = 0 ∧ 4 % 3 = 1 ∧ (3 : Nat) * 48 + 12 = 156 ∧ (156 : Nat) = 13 * 12 := by
  decide +kernel

/-- 38:B4 — the sky chronon `C₂₄` is the fibre product of `C₁₂` and `C₈` over `C₄`: the class-compatible pairs
number `12·8/4 = 24`, the map `C₂₄ → C₁₂ ×_{C₄} C₈` is injective, antipodal at `+12`, closed at `+24`; `232 = 8·29`. -/
theorem sky_chronon :
    count (fun n => (n / 8) % 4 = (n % 8) % 4) 96 = 24 ∧ (12 : Nat) * 8 = 24 * 4 ∧
    (∀ s, s < 24 → ∀ t, t < 24 → s % 12 = t % 12 → s % 8 = t % 8 → s = t) ∧
    (∀ s, s < 24 → (s + 12) % 24 ≠ s ∧ (s + 12 + 12) % 24 = s) ∧ (232 : Nat) = 8 * 29 := by decide +kernel

/-- 38:B5, 38:C14 — the recurrence data at the instance: `696 = lcm(12, 232) = 58·12 = 3·232` is the least common
return, `1392 = 2·696` the spinor recurrence; the joint cycle's `ℓ = 87 = 3·29`: at `4ℓ = 348` the shell is home
(`348 ≡ 0 mod 12`) and the Carrier reads the half (`348 ≡ 116 mod 232`, `78³⁴⁸ = −1`), at `8ℓ = 696` both are home. -/
theorem recurrence :
    (696 : Nat) % 12 = 0 ∧ (696 : Nat) % 232 = 0 ∧ (696 : Nat) = 58 * 12 ∧ (696 : Nat) = 3 * 232 ∧
    (1392 : Nat) = 2 * 696 ∧ (∀ n, n < 696 → 0 < n → n % 12 = 0 → n % 232 ≠ 0) ∧
    (87 : Nat) = 3 * 29 ∧ (87 : Nat) = (2 * 1 + 1) * (2 * 14 + 1) ∧ (87 : Nat) = (2 * 14 + 1) * (2 * 1 + 1) ∧
    (4 * 87 : Nat) % 12 = 0 ∧ (4 * 87 : Nat) % 232 = 116 ∧ (2 : Shell 13) ^ 348 = 1 ∧ (78 : Shell 233) ^ 348 = -1 ∧
    (2 : Shell 13) ^ 696 = 1 ∧ (78 : Shell 233) ^ 696 = 1 := by decide +kernel

/-- 38:B7 — the frame leak: the tick `π/116` reaches `π/2` at the quarter station `b_C = 58` (`58·4 = 232`), the halved
tick `π/232` being its reading on `C₄₆₄` (`1/464` of the turn); the composed rate `1/12 + 1/232 = 61/696`; between two (home, home) events every
class-compatible pair `(s mod 12, c mod 232)` occurs once: the pairs number `12·232/4 = 696` and the map
`t ↦ (t mod 12, t mod 232)` has trivial kernel on `[0, 696)`. -/
theorem frame_leak :
    (58 : Nat) * 4 = 232 ∧ (58 : Nat) * 2 = 116 ∧ (232 : Nat) * 2 = 464 ∧ (61 : Nat) * (12 * 232) = 696 * (232 + 12) ∧
    (12 : Nat) * 232 = 4 * 696 ∧
    count (fun n => (n / 232) % 4 = (n % 232) % 4) (12 * 232) = 696 ∧
    (∀ t, t < 696 → t % 12 = 0 → t % 232 = 0 → t = 0) := by decide +kernel

/-! ## C. The flow -/

/-- 38:C1, 38:C5, 38:D1 — the flow law as tick counts on `C₂₃₂` (`tick`): row `k` is home at `b_C = k` and at its
parity image (`116`) at `b_C = 116 + k`, for every row; the count returns the row at every clock state. -/
theorem flow_stations :
    (∀ k, k < 232 → tick 232 k k = 0 ∧ tick 232 k (116 + k) = 116) ∧
    (∀ b, b < 232 → ∀ k, k < 13 → (tick 232 k b + b) % 232 = k) ∧ (116 : Nat) = 232 / 2 := by
  decide +kernel

/-- 38:C3 — ownership: the origin is no station (the capacity stations are `d` with `0 < d` and `4d < 13` or
`4(13 − d) < 13`, the set `{1, 2, 3, 10, 11, 12}`), and at every clock state the origin's count is the clock's own:
the rays anchor at the Observer. -/
theorem ownership :
    (∀ d, d < 13 → ((0 < d ∧ (4 * d < 13 ∨ 4 * (13 - d) < 13)) ↔
      (d = 1 ∨ d = 2 ∨ d = 3 ∨ d = 10 ∨ d = 11 ∨ d = 12))) ∧
    (∀ b, b < 232 → (tick 232 0 b + b) % 232 = 0) := by decide +kernel

/-- 38:C4 — the half turn on `C₄₆₄` at the instance: two half turns are the identity and the rim `232` is its own
reflection (`FRC.Pair.half_turn` in general). -/
theorem half_turn_instance :
    (∀ x, x < 464 → (x + 232 + 232) % 464 = x ∧ (x + (464 - x % 464)) % 464 = 0) ∧
    (464 - 232 % 464) % 464 = 232 := by decide +kernel

/-- 38:C6 — the dilation instance `3/58 = 12/232` and the `(53, 13)` kill test in the auxiliary modulus `157`
(`53 = 4·13 + 1`; `S = 39 ≡ 3 mod 4`, not admissible): `5` primitive mod `157` (`5⁷⁸, 5⁵², 5¹² ≠ 1`, `5¹⁵⁶ = 1`), `5¹³ = 22`, `3 ∤ 13`, `22⁹ = 28 = 5⁻³⁹`, `22⁴` of order `3`, the idempotent
`117·13 ≡ 117 mod 156`, `5³⁹ = 129`; `12/52 = 3/13`, `lcm(12, 52) = 156` with the half event at `78`. -/
theorem kill_test :
    (3 : Nat) * 232 = 58 * 12 ∧ (53 : Nat) = 4 * 13 + 1 ∧ (157 : Nat) = 4 * 39 + 1 ∧ 39 % 4 = 3 ∧
    (5 : Shell 157) ^ 78 ≠ 1 ∧ (5 : Shell 157) ^ 52 ≠ 1 ∧ (5 : Shell 157) ^ 12 ≠ 1 ∧ (5 : Shell 157) ^ 156 = 1 ∧
    (5 : Shell 157) ^ 13 = 22 ∧ 13 % 3 ≠ 0 ∧
    (22 : Shell 157) ^ 9 = 28 ∧ (5 : Shell 157) ^ 39 * 28 = 1 ∧ (22 : Shell 157) ^ 4 ≠ 1 ∧
    ((22 : Shell 157) ^ 4) ^ 3 = 1 ∧ (117 : Nat) * 13 % 156 = 117 ∧ (5 : Shell 157) ^ 39 = 129 ∧
    (12 : Nat) * 13 = 52 * 3 ∧ (156 : Nat) % 12 = 0 ∧ (156 : Nat) % 52 = 0 ∧
    (∀ n, n < 156 → 0 < n → n % 12 = 0 → n % 52 ≠ 0) ∧ (78 : Nat) * 2 = 156 := by decide +kernel

/-- 38:C7, 38:C10, 38:X1 — the two faces at the instance: the angular face `12/232 = 3/58 = κ/S`, the temporal face
`12/464 = 3/116 = κ/(2S)`, their ratio `2`; the per-chronon rate `1/232` at `(13, 233)` and at `(5, 233)`. -/
theorem two_faces :
    (12 : Nat) * 58 = 3 * 232 ∧ (12 : Nat) * 116 = 3 * 464 ∧ (3 : Nat) * 116 = 2 * (3 * 58) ∧
    (3 : Nat) * (4 * 58) = 58 * (13 - 1) ∧ (1 : Nat) * (4 * 58) = 58 * (5 - 1) ∧ (4 : Nat) * 58 = 233 - 1 ∧
    (3 : Nat) * 58 = 174 := by decide +kernel

/-! ## D. The meridians and the covering -/

/-- The tent fold of `u = mt` on `𝔽₁₃`: the row `u − 13w` on an even sheet `w = ⌊u/13⌋`, `13(w + 1) − u` on an odd one. -/
def tent (p u : Nat) : Nat := if (u / p) % 2 = 0 then u - p * (u / p) else p * (u / p + 1) - u

/-- The sheet parity of the slot `(m, t)`: the route flips on odd sheets. -/
def sheet (p m t : Nat) : Nat := (m * t / p) % 2

/-- The shell of the parameter `t`: `min(t, p − t) − 1`. -/
def shellOf (p t : Nat) : Nat := (if t ≤ p - t then t else p - t) - 1

/-- A parameter is a station of capacity `κ`: `1 ≤ t ≤ κ` or `p − κ ≤ t ≤ p − 1`. -/
def isParam (p κ t : Nat) : Bool := (1 ≤ t && t ≤ κ) || (p - κ ≤ t && t ≤ p - 1)

/-- The multiplicity of the node (shell `s`, route `e`, row `k`) under the covering by the windings `1..p − 1`, both
rays and the stations: the slots are indexed by `n < (p − 1)·2·p` as `m = n / (2p) + 1`, ray `= (n / p) % 2`,
`t = n % p`. -/
def mult (p κ s e k : Nat) : Nat :=
  count (fun n => isParam p κ (n % p) = true ∧ shellOf p (n % p) = s ∧
    ((n / p) % 2 + sheet p (n / (2 * p) + 1) (n % p)) % 2 = e ∧ tent p ((n / (2 * p) + 1) * (n % p)) = k)
    ((p - 1) * 2 * p)

/-- 38:D1 — the capacity stations `4d < 13` select `{1, 2, 3, 10, 11, 12}` (shells `0, 1, 2` twice); the threading
on all `232` states is `flow_stations`. -/
theorem stations :
    (∀ t, t < 13 → (isParam 13 3 t = true ↔ (t = 1 ∨ t = 2 ∨ t = 3 ∨ t = 10 ∨ t = 11 ∨ t = 12))) ∧
    shellOf 13 1 = 0 ∧ shellOf 13 2 = 1 ∧ shellOf 13 3 = 2 ∧ shellOf 13 10 = 2 ∧ shellOf 13 11 = 1 ∧
    shellOf 13 12 = 0 ∧ count (fun t => isParam 13 3 t = true) 13 = 6 := by decide +kernel

/-- 38:D2 — the step law `11π/12 + π/13 + π/232 = π − (π/156 − π/232)` as exact fractions of `π/9048`
(`9048 = lcm(12, 13, 232)`): `8294 + 696 + 39 = 9029 = 9048 − (58 − 39)`; `156 = 13·12`. -/
theorem step_law :
    (9048 : Nat) = 12 * 754 ∧ (11 : Nat) * 754 = 8294 ∧ (13 : Nat) * 696 = 9048 ∧ (232 : Nat) * 39 = 9048 ∧
    (156 : Nat) * 58 = 9048 ∧ (8294 : Nat) + 696 + 39 = 9029 ∧ (9048 : Nat) - (58 - 39) = 9029 ∧
    (156 : Nat) = 13 * 12 ∧ (232 : Nat) = 233 - 1 ∧ (9048 : Nat) % 12 = 0 ∧ (9048 : Nat) % 13 = 0 ∧
    (9048 : Nat) % 232 = 0 := by decide +kernel

/-- 38:D3 — the scale-tower circuit: the tower's period is the drive's, `4κ = 12 = p − 1`, with the period points
`0`, `13/2` (the seam, `2·6 < 13 < 2·7`) and `13`. -/
theorem tower_period :
    (4 : Nat) * 3 = 12 ∧ (12 : Nat) = 13 - 1 ∧ (2 : Shell 13) ^ 12 = 1 ∧ (∀ k, k < 12 → 0 < k → (2 : Shell 13) ^ k ≠ 1) ∧
    2 * 6 < 13 ∧ 13 < 2 * 7 := by decide +kernel

/-- 38:D5 — the four rays and the four quarter classes on `𝔽₁₃`: the classes of `dlog mod 4` number three cells
each, the quarter `i = g⁹` carries class `1` and `−1 = g⁶` class `2`; the quarter fold `a = 13/4` lies between
`3` and `4` (`4·3 < 13 < 4·4`). -/
theorem quarter_classes :
    (∀ c, c < 4 → count (fun j => j % 4 = c) 12 = 3) ∧ 9 % 4 = 1 ∧ 6 % 4 = 2 ∧ (2 : Shell 13) ^ 9 = 5 ∧
    (2 : Shell 13) ^ 6 = -1 ∧ 4 * 3 < 13 ∧ 13 < 4 * 4 := by decide +kernel

/-- 38:D6, 38:D13 — the momentum dual `M₃` at winding `5 = g⁹ = −g³`: its stations on the tent shells are the rows
`5, 10, 11` (direct, `t = 1, 2, 3`) and `2, 3, 8` (echo, `t = 10, 11, 12`), the route flipping on the odd sheets
(`t = 3, 10`); the fold is `C₂₆`-periodic; the axis passages `t = 13j/5` drawn are `13/5` and `52/5`. -/
theorem momentum_dual :
    (2 : Shell 13) ^ 9 = 5 ∧ (5 : Shell 13) = -(2 ^ 3) ∧
    tent 13 (5 * 1) = 5 ∧ tent 13 (5 * 2) = 10 ∧ tent 13 (5 * 3) = 11 ∧ tent 13 (5 * 10) = 2 ∧
    tent 13 (5 * 11) = 3 ∧ tent 13 (5 * 12) = 8 ∧
    sheet 13 5 1 = 0 ∧ sheet 13 5 2 = 0 ∧ sheet 13 5 3 = 1 ∧ sheet 13 5 10 = 1 ∧ sheet 13 5 11 = 0 ∧
    sheet 13 5 12 = 0 ∧ (∀ u, u < 200 → tent 13 (u + 26) = tent 13 u) ∧
    4 * 13 ≤ 13 * 5 ∧ 39 * 5 ≤ 4 * 52 ∧ ¬ (4 * 26 ≤ 13 * 5 ∨ 39 * 5 ≤ 4 * 26) ∧
    ¬ (4 * 39 ≤ 13 * 5 ∨ 39 * 5 ≤ 4 * 39) := by decide +kernel

/-- 38:D7, 38:D13 — the covering at the instance: `144` slots (twelve windings, two rays, six stations) over the
`72` nodes, every node of multiplicity `3` on the even rows and `1` on the odd rows: `36` once and `36` thrice,
`144 = 36 + 108`; winding `1` is `M₀` (rows `t`, no flip) and winding `5` is `M₃`. -/
theorem covering_instance :
    count (fun n => isParam 13 3 (n % 13) = true) (12 * 2 * 13) = 144 ∧ (3 : Nat) * 2 * 12 = 72 ∧
    (∀ s, s < 3 → ∀ e, e < 2 → ∀ k, k < 13 → 0 < k → mult 13 3 s e k = if k % 2 = 0 then 3 else 1) ∧
    (36 : Nat) * 1 + 36 * 3 = 144 ∧ (3 : Nat) * 2 * 6 = 36 ∧
    (∀ t, t < 13 → isParam 13 3 t = true → tent 13 (1 * t) = t ∧ sheet 13 1 t = 0) := by decide +kernel

/-- 38:D8 — the half-cell ramification `t_{1/2} = 13/(2m)` lies in the drawn first segment `[0, 13/4]` for every
sibling `m ≥ 2` (`4·13 ≤ 13·2m`) and not for `M₀` (`m = 1`, `13/2` the seam); the axis passage `13/m` is drawn
exactly for `m ≥ 4`. -/
theorem ramification :
    (∀ m, m < 13 → 2 ≤ m → 4 * 13 ≤ 13 * (2 * m)) ∧ ¬ (4 * 13 ≤ 13 * 2) ∧ (2 * 6 < 13 ∧ 13 < 2 * 7) ∧
    (∀ m, m < 13 → 1 ≤ m → (4 * 13 ≤ 13 * m ↔ 4 ≤ m)) := by decide +kernel

/-- 38:D9 — the horizon fold fusion `5·39 ≡ −13 (mod 104)`: `5·39 + 13 = 208 = 2·104`, `104 = 8·13`, `39 = 3·13`;
eight ray ends fuse into four points (`8 = 2·4`). -/
theorem fusion :
    (5 : Nat) * 39 + 13 = 2 * 104 ∧ (5 * 39 + 13 : Nat) % 104 = 0 ∧ (104 : Nat) = 8 * 13 ∧ (39 : Nat) = 3 * 13 ∧
    (8 : Nat) = 2 * 4 := by decide +kernel

/-- The inverse of a shell index `a ∈ {1, 2, 3}` on `𝔽₁₃`: `1, 7, 9`. -/
def inv13 (a : Nat) : Nat := if a = 1 then 1 else if a = 2 then 7 else 9

/-- 38:D12 at the instance — the reflection identity `⌊ab/13⌋ + ⌊(13 − a)b/13⌋ + 1 = b` for all `0 < a, b < 13`,
and the parity decider: for every node (shell `a ∈ {1, 2, 3}`, row `k`), with `M = k a⁻¹`, the four candidate wraps
give `μ = 3` on the even rows and `1` on the odd rows (`FRC.Pair.mu`); the general theorem is
`covering_parity`. -/
theorem parity_instance :
    (∀ a, a < 13 → 0 < a → ∀ b, b < 13 → 0 < b → a * b / 13 + (13 - a) * b / 13 + 1 = b) ∧
    (∀ a, a < 4 → 0 < a → a * inv13 a % 13 = 1) ∧
    (∀ a, a < 4 → 0 < a → ∀ k, k < 13 → 0 < k →
      mu (a * (k * inv13 a % 13) / 13) ((13 - k * inv13 a % 13) * a / 13)
        ((k * inv13 a % 13) * (13 - a) / 13) ((13 - k * inv13 a % 13) * (13 - a) / 13) =
        if k % 2 = 0 then 3 else 1) := by decide +kernel

end FRC.Pair
