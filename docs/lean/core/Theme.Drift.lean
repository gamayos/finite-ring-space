import FrcCore.Theme.Symbol
import FrcCore.Theme.Gravity

/-!
# FrcCore.Theme.Drift — the exact faces of frame drift (the gravity theme; 21-gravity, 10 October 2026)

The arithmetic behind the drift rows of *Gravitation as Phase Synchronisation* (21-gravity), on every shell and with
no axioms:

* **The mass–energy channel** (21:A9): a residue in both the split cycle (`x^{p−1} = 1`, `p − 1 = 4κ`) and the doubled
  non-split one (`x^{2(p+1)} = 1`) has `x⁴ = 1`, and conversely — the channel is the quarter-turn core `Q₄`
  (`channel_q4`), stated on the shell, with no gcd.
* **The cover triangle** (21:C25, C7, C8): `2γ − β = 1` and `γ = 1` give `β = 1` (`cover_triangle`); the deviation
  `2γ − β − 1` vanishes there (`cover_deviation`).
* **The relative-cycle defect** (21:C21): on the quotient cycle of order `L` the shift by `a` first returns at
  `firstReturn L a`, every return is a multiple of it (`return_iff`), the corpus instance `C₆₀–C₂₈` (`L = 420`,
  `q = 4`, `a = 8`, `T_def = 105`) decided (`defect_instance`).
* **The pair tally** (21:C21, C1): on an exact link ratio `z` with mate `w` (`zw = 1`) the failure tally
  `E = 2 − z − w`, the coincidence weight `W = 2 + z + w`, `E + W = 4`, and the oriented mate `(z − w)² = −E·W`
  (`pair_tally`, `tally_weight`).
* **The locked sum** (21:C1): `m` cells of one phase sum to `m·z` (`locked_sum`).
* **The character composition** (21:C11, 00:C21): the exponential reading composes, `g^{a+b} = g^a g^b`
  (`character_composition`).
* **The Gauss law from transfer antisymmetry** (21:C11): for antisymmetric link currents `J_xy = −J_yx` on `n` sites,
  the divergence summed over a region equals the flux through its boundary, the interior links cancelling in pairs
  (`gauss_law`; the double sum of an antisymmetric function vanishes, `antisymmetric_sum`).
* **The post-Newtonian coefficients** (21:C8, P6): `e^{−2U}` against the isotropic Schwarzschild `((1 − U/2)/(1 + U/2))²`
  differ first at `U³` by `1/6`, and `e^{2U}` against `(1 + U/2)⁴` at `U²` by `1/2`, as exact integer identities on the
  scaled coefficients (`pn_coefficients`).
* **The dust tensor's trace** (21:C6): the Frobenius pairing of `m (w ⊗ w)`, `w = a + bη`, is `m (a² − ν b²) = m N(w)`
  (`frobenius_trace`).
* **The registration root** (21:C19): where `1 − w² = s²` is a square and `w ≠ 0`, `η` with `wη = 1 − s` solves
  `wη² − 2η + w = 0` (`registration_root`).

The ring identities are decided by the core's normaliser (`RE.sound`); the sums by `sumRange` and `Symbol.sum_swap`;
the kernel decides the integer instances. No axioms.
-/

namespace FRC.Drift

open FRC.Shell FRC.Shell.Frame

variable {p : Nat} [Pos p]

/-! ## 21:A9 — the mass–energy channel -/

/-- 21:A9 — the channel `C_{p−1} ∩ C_{2(p+1)} = Q₄` on every shell: with `p − 1 = 4κ`, a residue has
`x^{4κ} = 1` and `x^{2(4κ + 2)} = 1` exactly when `x⁴ = 1`. -/
theorem channel_q4 (κ : Nat) (x : Shell p) :
    (x ^ (4 * κ) = 1 ∧ x ^ (2 * (4 * κ + 2)) = 1 ↔ x ^ 4 = 1) := by
  have e : 2 * (4 * κ + 2) = (4 * κ) * 2 + 4 := by rw [Nat.mul_add, Nat.mul_comm 2 (4 * κ)]
  constructor
  · intro ⟨h1, h2⟩
    rw [e, pow_add, pow_mul, h1, one_pow, one_mul] at h2
    exact h2
  · intro h4
    have e1 : x ^ (4 * κ) = 1 := by rw [pow_mul, h4, one_pow]
    refine ⟨e1, ?_⟩
    rw [e, pow_add, pow_mul, e1, one_pow, one_mul, h4]

/-! ## 21:C25 — the cover triangle -/

/-- 21:C25, 21:C7, 21:C8 — on every shell: `2γ − β = 1` and `γ = 1` give `β = 1`. -/
theorem cover_triangle {β γ : Shell p} (h1 : (1 + 1) * γ + -β = 1) (h2 : γ = 1) : β = 1 := by
  subst h2
  have h : (1 + 1) * (1 : Shell p) + -β = 1 := h1
  rw [mul_one] at h
  have h' : (1 + -β) + (1 : Shell p) = 0 + 1 := by rw [zero_add, add_comm, ← add_assoc]; exact h
  have h'' : (1 : Shell p) + -β = 0 := add_right_cancel h'
  have := eq_neg_of_add_eq_zero h''
  rw [neg_neg] at this
  exact this.symm

/-- 21:C25 — the deviation `2γ − β − 1` vanishes on the triangle. -/
theorem cover_deviation {β γ : Shell p} (h1 : (1 + 1) * γ + -β = 1) : (1 + 1) * γ + -β + -1 = 0 := by
  rw [h1]; exact add_neg 1

/-! ## 21:C21 — the relative-cycle defect and its recurrence -/

/-- The least `u ≥ t` with `P u` within `f` steps, else `t + f`. -/
def least (P : Nat → Bool) : Nat → Nat → Nat
  | 0, t => t
  | f + 1, t => if P t then t else least P f (t + 1)

theorem least_le (P : Nat → Bool) : ∀ (f t : Nat), t ≤ least P f t
  | 0, t => Nat.le_refl t
  | f + 1, t => by
    unfold least
    match h : P t with
    | true => rw [if_pos rfl]; exact Nat.le_refl t
    | false => rw [if_neg Bool.false_ne_true]; exact Nat.le_trans (Nat.le_succ t) (least_le P f (t + 1))

theorem least_bound (P : Nat → Bool) : ∀ (f t : Nat), least P f t ≤ t + f
  | 0, t => Nat.le_refl t
  | f + 1, t => by
    unfold least
    match h : P t with
    | true => rw [if_pos rfl]; exact Nat.le_add_right t (f + 1)
    | false =>
      rw [if_neg Bool.false_ne_true]
      have e : t + 1 + f = t + (f + 1) := by rw [Nat.add_right_comm, Nat.add_assoc]
      rw [← e]; exact least_bound P f (t + 1)

theorem least_min (P : Nat → Bool) : ∀ (f t u : Nat), t ≤ u → u < least P f t → P u = false
  | 0, t, u, htu, hu => absurd (Nat.lt_of_le_of_lt htu hu) (Nat.lt_irrefl t)
  | f + 1, t, u, htu, hu => by
    unfold least at hu
    match h : P t with
    | true => rw [h, if_pos rfl] at hu; exact absurd (Nat.lt_of_le_of_lt htu hu) (Nat.lt_irrefl t)
    | false =>
      rw [h, if_neg Bool.false_ne_true] at hu
      rcases Nat.lt_or_ge u (t + 1) with hlt | hge
      · have e : u = t := Nat.le_antisymm (Nat.le_of_lt_succ hlt) htu
        rw [e]; exact h
      · exact least_min P f (t + 1) u hge hu

theorem least_hit (P : Nat → Bool) : ∀ (f t : Nat), (∃ u, t ≤ u ∧ u < t + f ∧ P u = true) → P (least P f t) = true
  | 0, t, ⟨u, htu, hu, _⟩ => absurd (Nat.lt_of_le_of_lt htu hu) (Nat.lt_irrefl t)
  | f + 1, t, ⟨u, htu, hu, hP⟩ => by
    unfold least
    match h : P t with
    | true => rw [if_pos rfl]; exact h
    | false =>
      rw [if_neg Bool.false_ne_true]
      apply least_hit P f (t + 1)
      refine ⟨u, ?_, ?_, hP⟩
      · rcases Nat.lt_or_ge u (t + 1) with hlt | hge
        · have e : u = t := Nat.le_antisymm (Nat.le_of_lt_succ hlt) htu
          rw [e] at hP; rw [hP] at h; exact absurd h (Bool.noConfusion)
        · exact hge
      · rw [Nat.add_succ, ← Nat.succ_add] at hu; exact hu

/-- The return test on the cycle of order `L`: `(t·a) mod L = 0`. -/
def isReturn (L a t : Nat) : Bool := decide ((t * a) % L = 0)

theorem isReturn_iff (L a t : Nat) : isReturn L a t = true ↔ (t * a) % L = 0 :=
  ⟨fun h => of_decide_eq_true h, fun h => decide_eq_true h⟩

/-- The period of the defect: the first return `t ≥ 1` of the shift by `a` on the cycle of order `L` (`L` itself returns). -/
def firstReturn (L a : Nat) : Nat := least (isReturn L a) L 1

theorem firstReturn_pos (L a : Nat) : 1 ≤ firstReturn L a := least_le _ L 1

theorem firstReturn_le (L a : Nat) : firstReturn L a ≤ L + 1 := by
  have := least_bound (isReturn L a) L 1; rw [Nat.add_comm] at this; exact this

/-- 21:C21 — the first return is a return. -/
theorem firstReturn_returns (L a : Nat) (hL : 0 < L) : (firstReturn L a * a) % L = 0 := by
  apply (isReturn_iff _ _ _).mp
  apply least_hit
  refine ⟨L, Nat.succ_le_of_lt hL, by rw [Nat.add_comm]; exact Nat.lt_succ_self L, ?_⟩
  apply (isReturn_iff _ _ _).mpr
  rw [Nat.mul_comm, FRC.Nat.mul_mod a L L hL, FRC.Nat.mod_self L hL, Nat.mul_zero]; rfl

/-- 21:C21 — nothing returns before the first return. -/
theorem firstReturn_min (L a u : Nat) (hu1 : 1 ≤ u) (hu : u < firstReturn L a) : (u * a) % L ≠ 0 := by
  have h := least_min (isReturn L a) L 1 u hu1 hu
  intro e; have e' := (isReturn_iff L a u).mpr e; rw [e'] at h; exact Bool.noConfusion h

/-- 21:C21 — the defect recurs exactly at the multiples of its period: `(t·a) mod L = 0 ↔ T ∣ t`, `T = firstReturn L a`. -/
theorem return_iff (L a t : Nat) (hL : 0 < L) : (t * a) % L = 0 ↔ firstReturn L a ∣ t := by
  have hT : 0 < firstReturn L a := firstReturn_pos L a
  have hTa : (firstReturn L a * a) % L = 0 := firstReturn_returns L a hL
  constructor
  · intro h
    obtain ⟨q, hq⟩ := FRC.Nat.mod_spec (firstReturn L a) hT t
    -- `t = T q + r`; `(T q a) mod L = 0`, so `(r a) mod L = 0`, so `r = 0` by minimality
    have hq0 : (firstReturn L a * q * a) % L = 0 := by
      rw [FRC.Nat.mul_assoc, Nat.mul_comm q a, ← FRC.Nat.mul_assoc, FRC.Nat.mul_mod_left' _ q L hL, hTa, Nat.zero_mul]; rfl
    have hr : ((t % firstReturn L a) * a) % L = 0 := by
      have e : t * a = firstReturn L a * q * a + (t % firstReturn L a) * a := by
        rw [hq, FRC.Nat.add_mul]
        rw [← hq]
      rw [e, FRC.Nat.add_mod _ _ L hL, hq0, Nat.zero_add, FRC.Nat.mod_mod _ L hL] at h
      exact h
    have hr0 : t % firstReturn L a = 0 := by
      rcases Nat.lt_or_ge (t % firstReturn L a) 1 with hlt | hge
      · exact Nat.eq_zero_of_le_zero (Nat.le_of_lt_succ hlt)
      · exact absurd hr (firstReturn_min L a _ hge (FRC.Nat.mod_lt' t hT))
    exact ⟨q, by rw [hq, hr0, Nat.add_zero]⟩
  · intro ⟨q, hq⟩
    rw [hq, FRC.Nat.mul_assoc, Nat.mul_comm q a, ← FRC.Nat.mul_assoc, FRC.Nat.mul_mod_left' _ q L hL, hTa, Nat.zero_mul]; rfl

/-- 21:C21 — the corpus instance `C₆₀–C₂₈`: `L = lcm = 420`, `q = gcd = 4`, `a = 15 − 7 = 8`, and the period on the
quotient cycle `L/q = 105` is `105` (the shift by `8` first returns after `105` steps). -/
theorem defect_instance :
    420 / 28 = 15 ∧ 420 / 60 = 7 ∧ 420 % 28 = 0 ∧ 420 % 60 = 0 ∧ 60 % 4 = 0 ∧ 28 % 4 = 0 ∧ (15 - 7) % 420 = 8 ∧
    firstReturn 105 8 = 105 ∧ firstReturn 420 8 = 105 := by decide

/-! ## 21:C21, 21:C1 — the pair tally -/

/-- 21:C21, 21:C1 — on an exact link ratio `z` with mate `w` (`zw = 1`): the oriented mate squared is minus the
product of the failure tally and the coincidence weight, `(z − w)² = −(2 − z − w)(2 + z + w)`. -/
theorem pair_tally (z w : Shell p) (h : z * w = 1) :
    (z + -w) * (z + -w) = -((1 + 1 + -z + -w) * (1 + 1 + z + w)) := by
  have key : (z + -w) * (z + -w) = -((1 + 1 + -z + -w) * (1 + 1 + z + w)) + (1 + 1 + 1 + 1) * (1 + -(z * w)) :=
    RE.sound (look [z, w])
      (.mul (.add (.var 0) (.neg (.var 1))) (.add (.var 0) (.neg (.var 1))))
      (.add (.neg (.mul (.add (.add (.add .one .one) (.neg (.var 0))) (.neg (.var 1)))
                        (.add (.add (.add .one .one) (.var 0)) (.var 1))))
            (.mul (.add (.add (.add .one .one) .one) .one) (.add .one (.neg (.mul (.var 0) (.var 1))))))
      (by decide +kernel)
  rw [key, h, add_neg 1, mul_zero, add_zero]

/-- 21:C21 — the failure tally and the coincidence weight sum to `4`: `E + W = (2 − z − w) + (2 + z + w) = 4`. -/
theorem tally_weight (z w : Shell p) : (1 + 1 + -z + -w) + (1 + 1 + z + w) = 1 + 1 + 1 + 1 :=
  RE.sound (look [z, w])
    (.add (.add (.add (.add .one .one) (.neg (.var 0))) (.neg (.var 1))) (.add (.add (.add .one .one) (.var 0)) (.var 1)))
    (.add (.add (.add .one .one) .one) .one) (by decide +kernel)

/-! ## 21:C1 — the locked sum; 21:C11 — the character composition -/

/-- 21:C1 — `m` cells of one phase `z` sum to `m·z`, the coherent coefficient. -/
theorem locked_sum (z : Shell p) (m : Nat) : sumRange (fun _ => z) m = ofNat m * z := sum_const z m

/-- 21:C11, 00:C21 — the exponential reading is the character: `g^{a+b} = g^a g^b`. -/
theorem character_composition (g : Shell p) (a b : Nat) : g ^ (a + b) = g ^ a * g ^ b := pow_add g a b

/-! ## 21:C11 — the Gauss law from transfer antisymmetry -/

/-- The region's indicator. -/
def ind (R : Nat → Bool) (x : Nat) : Shell p := if R x then 1 else 0

/-- The double sum of an antisymmetric function over `n × n` vanishes on every frame (`2 ≠ 0`). -/
theorem antisymmetric_sum {κ : Nat} {g : Shell p} (F : Frame p κ g) (n : Nat) (A : Nat → Nat → Shell p)
    (hA : ∀ x y, A x y = -(A y x)) :
    sumRange (fun x => sumRange (fun y => A x y) n) n = 0 := by
  have swap := FRC.Symbol.sum_swap A n n
  have neg : sumRange (fun y => sumRange (fun x => A x y) n) n = -(sumRange (fun x => sumRange (fun y => A x y) n) n) := by
    rw [← sum_neg]; apply sum_congr; intro y _
    rw [← sum_neg]; apply sum_congr; intro x _
    exact hA x y
  rw [neg] at swap
  -- `S = −S` gives `(1 + 1) S = 0`, so `S = 0` since `2 ≠ 0`
  have h2 : (1 + 1 : Shell p) * sumRange (fun x => sumRange (fun y => A x y) n) n = 0 := by
    rw [right_distrib, one_mul]
    calc sumRange (fun x => sumRange (fun y => A x y) n) n + sumRange (fun x => sumRange (fun y => A x y) n) n
        = sumRange (fun x => sumRange (fun y => A x y) n) n + -(sumRange (fun x => sumRange (fun y => A x y) n) n) := by
          rw [← swap]
      _ = 0 := add_neg _
  rcases F.mul_eq_zero h2 with h | h
  · exact absurd (by rw [two_eq_one_add_one]; exact h) F.two_ne_zero
  · exact h

/-- 21:C11 — the Gauss law: for antisymmetric link currents `J_xy = −J_yx` on `n` sites, the divergence
`Σ_y J_xy` summed over a region `R` equals the flux through its boundary, `Σ_{x ∈ R} Σ_{y ∉ R} J_xy`:
the interior links cancel in pairs. -/
theorem gauss_law {κ : Nat} {g : Shell p} (F : Frame p κ g) (n : Nat) (J : Nat → Nat → Shell p)
    (hJ : ∀ x y, J x y = -(J y x)) (R : Nat → Bool) :
    sumRange (fun x => ind R x * sumRange (fun y => J x y) n) n =
      sumRange (fun x => ind R x * sumRange (fun y => (1 + -(ind R y)) * J x y) n) n := by
  -- the right side is the left minus the interior double sum, which vanishes by antisymmetry
  have interior : sumRange (fun x => sumRange (fun y => ind R x * ind R y * J x y) n) n = 0 :=
    antisymmetric_sum F n (fun x y => ind R x * ind R y * J x y) (fun x y => by
      rw [hJ x y, mul_neg, mul_comm (ind R x) (ind R y)])
  have split : ∀ x, ind R x * sumRange (fun y => (1 + -(ind R y)) * J x y) n =
      ind R x * sumRange (fun y => J x y) n + -(sumRange (fun y => ind R x * ind R y * J x y) n) := by
    intro x
    rw [← sum_neg, ← sum_mul_left, ← sum_mul_left, ← sum_add]; apply sum_congr; intro y _
    exact RE.sound (look [ind R x, ind R y, J x y])
      (.mul (.var 0) (.mul (.add .one (.neg (.var 1))) (.var 2)))
      (.add (.mul (.var 0) (.var 2)) (.neg (.mul (.mul (.var 0) (.var 1)) (.var 2)))) (by decide +kernel)
  rw [sum_congr n (fun x _ => split x), sum_add, sum_neg, interior, neg_zero, add_zero]

/-! ## 21:C8, 21:P6 — the post-Newtonian coefficients, exact -/

/-- 21:C8, 21:P6 — `e^{−2U} = 1 − 2U + 2U² − (4/3)U³ + …` against the isotropic Schwarzschild
`((1 − U/2)/(1 + U/2))² = 1 − 2U + 2U² − (3/2)U³ + …`: equal through `U²`, apart at `U³` by `1/6`
(`6·(−4/3) − 6·(−3/2) = 1`); `e^{2U} = 1 + 2U + 2U² + …` against `(1 + U/2)⁴ = 1 + 2U + (3/2)U² + …`: apart at
`U²` by `1/2` (`2·2 − 3 = 1`); the binomial expansion behind the Schwarzschild coefficients:
`(1 − 2x + x²)(1 − 2x + 3x² − 4x³)` has `x²`-coefficient `8` and `x³`-coefficient `−12`, read at `x = U/2`
as `2` and `−3/2`. Exact integers, decided by the kernel. -/
theorem pn_coefficients :
    (6 : Int) * (-4) / 3 - 6 * (-3) / 2 = 1 ∧ (2 : Int) * 2 - 3 = 1 ∧
    (3 : Int) + 4 + 1 = 8 ∧ (-4 : Int) - 6 - 2 = -12 ∧ (8 : Int) / 4 = 2 ∧ (-12 : Int) * 2 / 8 = -3 := by decide

/-! ## 21:C6 — the dust tensor's trace -/

/-- 21:C6 — the Frobenius pairing of the symmetric square `m (w ⊗ w)`, `w = a + bη` with `η² = ν`, is
`m a² − ν m b² = m (a² − ν b²) = m N(w)`: the rest cardinality. -/
theorem frobenius_trace (m a b ν : Shell p) :
    m * (a * a) + -(ν * (m * (b * b))) = m * (a * a + -(ν * (b * b))) :=
  RE.sound (look [m, a, b, ν])
    (.add (.mul (.var 0) (.mul (.var 1) (.var 1))) (.neg (.mul (.var 3) (.mul (.var 0) (.mul (.var 2) (.var 2))))))
    (.mul (.var 0) (.add (.mul (.var 1) (.var 1)) (.neg (.mul (.var 3) (.mul (.var 2) (.var 2))))))
    (by decide +kernel)

/-! ## 21:C19 — the registration root -/

/-- 21:C19 — where `1 − w² = s²` is a square and `w ≠ 0`, the residue `η` with `wη = 1 − s` solves the registration
quadratic `wη² − 2η + w = 0`, on every frame. -/
theorem registration_root {κ : Nat} {g : Shell p} (F : Frame p κ g) {w s η : Shell p}
    (hs : s * s = 1 + -(w * w)) (hw : w ≠ 0) (hη : w * η = 1 + -s) :
    w * (η * η) + -((1 + 1) * η) + w = 0 := by
  -- `w · (wη² − 2η + w) = (wη)² − 2(wη) + w² = (1 − s)² − 2(1 − s) + w² = s² − 1 + w² = 0`
  have key : w * (w * (η * η) + -((1 + 1) * η) + w) = (w * η) * (w * η) + -((1 + 1) * (w * η)) + w * w :=
    RE.sound (look [w, η])
      (.mul (.var 0) (.add (.add (.mul (.var 0) (.mul (.var 1) (.var 1))) (.neg (.mul (.add .one .one) (.var 1)))) (.var 0)))
      (.add (.add (.mul (.mul (.var 0) (.var 1)) (.mul (.var 0) (.var 1))) (.neg (.mul (.add .one .one) (.mul (.var 0) (.var 1))))) (.mul (.var 0) (.var 0)))
      (by decide +kernel)
  have expand : (1 + -s) * (1 + -s) + -((1 + 1) * (1 + -s)) + w * w = s * s + -1 + w * w :=
    RE.sound (look [s, w])
      (.add (.add (.mul (.add .one (.neg (.var 0))) (.add .one (.neg (.var 0)))) (.neg (.mul (.add .one .one) (.add .one (.neg (.var 0)))))) (.mul (.var 1) (.var 1)))
      (.add (.add (.mul (.var 0) (.var 0)) (.neg .one)) (.mul (.var 1) (.var 1)))
      (by decide +kernel)
  have hz : w * (w * (η * η) + -((1 + 1) * η) + w) = 0 := by
    rw [key, hη, expand, hs]
    -- `(1 − w²) + (w² − 1) = 0`
    exact RE.sound (look [w])
      (.add (.add (.add .one (.neg (.mul (.var 0) (.var 0)))) (.neg .one)) (.mul (.var 0) (.var 0))) .zero
      (by decide +kernel)
  rcases F.mul_eq_zero hz with h | h
  · exact absurd h hw
  · exact h

end FRC.Drift
