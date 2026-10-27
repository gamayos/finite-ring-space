import FrcCore.Theme.Symbol
import FrcCore.Theme.Gravity
import FrcCore.Theme.Quadratic
import FrcCore.Theme.Shift

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
  (`character_composition`); the PPN form's defect `4ab` and its failure to be a character (`ppn_defect`,
  `ppn_no_character`, 00:C21).
* **The Gauss law from transfer antisymmetry** (21:C11): for antisymmetric link currents `J_xy = −J_yx` on `n` sites,
  the divergence summed over a region equals the flux through its boundary, the interior links cancelling in pairs
  (`gauss_law`; the double sum of an antisymmetric function vanishes, `antisymmetric_sum`).
* **The post-Newtonian coefficients** (21:C8, P6): `e^{−2U}` against the isotropic Schwarzschild `((1 − U/2)/(1 + U/2))²`
  differ first at `U³` by `1/6`, and `e^{2U}` against `(1 + U/2)⁴` at `U²` by `1/2`, as exact integer identities on the
  scaled coefficients (`pn_coefficients`).
* **The dust tensor's trace** (21:C6): the Frobenius pairing of `m (w ⊗ w)`, `w = a + bη`, is `m (a² − ν b²) = m N(w)`
  (`frobenius_trace`).
* **The single arrow** (21:C3, 00:E3): `conj (zⁿ) = (conj z)ⁿ` and `zⁿ · (conj z)ⁿ = 1` on the norm-one circle (`conj_pow`, `conj_branch`).
* **The compression identity** (21:X3, C21): on the cycle the drive step moves a sector's weight into the sector and the
  offset sector exactly, `Σ P·(U(Pf))² + Σ (1 − P)·(U(Pf))² = Σ P·f²` (`compression`), and returns it after `n` steps.
* **The registration root** (21:C19): where `1 − w² = s²` is a square and `w ≠ 0`, `η` with `wη = 1 − s` solves
  `wη² − 2η + w = 0` (`registration_root`).

The ring identities are decided by the core's normaliser (`RE.sound`); the sums by `sumRange` and `Symbol.sum_swap`;
the kernel decides the integer instances. No axioms.
-/

namespace FRC.Drift

open FRC.Shell FRC.Shell.Frame

variable {p : Nat} [Pos p]

/-! ## 21:A9 — the mass–energy channel -/

/-- 21:A9, 38:D5 — the channel `C_{p−1} ∩ C_{2(p+1)} = Q₄` on every shell: with `p − 1 = 4κ`, a residue has
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

/-- 21:C25, 21:C7, 21:C8, 00:E4 — on every shell: `2γ − β = 1` and `γ = 1` give `β = 1`. -/
theorem cover_triangle {β γ : Shell p} (h1 : (1 + 1) * γ + -β = 1) (h2 : γ = 1) : β = 1 := by
  subst h2
  have h : (1 + 1) * (1 : Shell p) + -β = 1 := h1
  rw [mul_one] at h
  have h' : (1 + -β) + (1 : Shell p) = 0 + 1 := by rw [zero_add, add_comm, ← add_assoc]; exact h
  have h'' : (1 : Shell p) + -β = 0 := add_right_cancel h'
  have := eq_neg_of_add_eq_zero h''
  rw [neg_neg] at this
  exact this.symm

/-- 21:C25, 00:E4 — the deviation `2γ − β − 1` vanishes on the triangle. -/
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
    | true => rw [ite_eq_left rfl]; exact Nat.le_refl t
    | false => rw [ite_eq_right Bool.false_ne_true]; exact Nat.le_trans (Nat.le_succ t) (least_le P f (t + 1))

theorem least_bound (P : Nat → Bool) : ∀ (f t : Nat), least P f t ≤ t + f
  | 0, t => Nat.le_refl t
  | f + 1, t => by
    unfold least
    match h : P t with
    | true => rw [ite_eq_left rfl]; exact Nat.le_add_right t (f + 1)
    | false =>
      rw [ite_eq_right Bool.false_ne_true]
      have e : t + 1 + f = t + (f + 1) := by rw [Nat.add_right_comm, Nat.add_assoc]
      rw [← e]; exact least_bound P f (t + 1)

theorem least_min (P : Nat → Bool) : ∀ (f t u : Nat), t ≤ u → u < least P f t → P u = false
  | 0, t, u, htu, hu => absurd (Nat.lt_of_le_of_lt htu hu) (Nat.lt_irrefl t)
  | f + 1, t, u, htu, hu => by
    unfold least at hu
    match h : P t with
    | true => rw [h, ite_eq_left rfl] at hu; exact absurd (Nat.lt_of_le_of_lt htu hu) (Nat.lt_irrefl t)
    | false =>
      rw [h, ite_eq_right Bool.false_ne_true] at hu
      rcases Nat.lt_or_ge u (t + 1) with hlt | hge
      · have e : u = t := Nat.le_antisymm (Nat.le_of_lt_succ hlt) htu
        rw [e]; exact h
      · exact least_min P f (t + 1) u hge hu

theorem least_hit (P : Nat → Bool) : ∀ (f t : Nat), (∃ u, t ≤ u ∧ u < t + f ∧ P u = true) → P (least P f t) = true
  | 0, t, ⟨u, htu, hu, _⟩ => absurd (Nat.lt_of_le_of_lt htu hu) (Nat.lt_irrefl t)
  | f + 1, t, ⟨u, htu, hu, hP⟩ => by
    unfold least
    match h : P t with
    | true => rw [ite_eq_left rfl]; exact h
    | false =>
      rw [ite_eq_right Bool.false_ne_true]
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

/-- 21:C1, 21:C2, 32:C10, 32:X7, 32:P5 — `m` cells of one phase `z` sum to `m·z`, the coherent coefficient (a virialised clump's weight one). -/
theorem locked_sum (z : Shell p) (m : Nat) : sumRange (fun _ => z) m = ofNat m * z := sum_const z m

/-- 21:C11, 21:C8, 00:C21, 00:E4 — the exponential reading is the character: `g^{a+b} = g^a g^b`. -/
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

/-- 21:C11, 21:C2, 21:X4, 00:E3, 00:E4, 32:C1, 32:X1, 32:C4 — the Gauss law: for antisymmetric link currents `J_xy = −J_yx` on `n` sites, the divergence
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

/-- 21:C8, 21:P6, 00:E4 — `e^{−2U} = 1 − 2U + 2U² − (4/3)U³ + …` against the isotropic Schwarzschild
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

/-! ## The single arrow (21:C3, 00:E3): the conjugate branch runs the cycle backwards (11 October 2026) -/
open FRC.Extension FRC.Extension.Ext
variable {ν : Shell p}

/-- 21:C3, 00:E3 — the conjugate of a power is the power of the conjugate, `conj (zⁿ) = (conj z)ⁿ`, on `𝔽_p[w]/(w² − ν)`. -/
theorem conj_pow (z : Ext p ν) : ∀ n : Nat, conj (z ^ n) = (conj z) ^ n
  | 0 => Ext.ext rfl Shell.neg_zero
  | n + 1 => by
      show conj (z ^ n * z) = (conj z) ^ n * conj z
      rw [conj_mul, conj_pow z n]

/-- 21:C3, 00:E3 — the single arrow: on the norm-one circle `N(z) = 1`, `zⁿ · (conj z)ⁿ = 1` for every `n`, so the conjugate
(Frobenius) branch of a clock is its orbit run backwards (`conj (zⁿ)` inverts `zⁿ`, with `conj_pow`): a time-reversed clock
is the conjugation, not a step of the drive — the row's reading is that a repulsive source would need that branch. -/
theorem conj_branch (z : Ext p ν) (hz : norm z = 1) : ∀ n : Nat, z ^ n * (conj z) ^ n = 1
  | 0 => Ext.one_mul 1
  | n + 1 => by
      show z ^ n * z * ((conj z) ^ n * conj z) = 1
      rw [Ext.mul_assoc, ← Ext.mul_assoc z, Ext.mul_comm z ((conj z) ^ n), Ext.mul_assoc, ← Ext.mul_assoc,
        conj_branch z hz n, Ext.one_mul, conj_inv_of_norm_one z hz]


/-! ## The compression identity (21:X3, C21): the offset sector holds what the drive moves, exactly (11 October 2026) -/
open FRC.Cycle in
/-- 21:X3, 21:C21, 21:C22, 00:E5 — the compression identity on the cycle of `n` sites: for the drive step `U f (x) = f ((x + 1) mod n)`
and a sector `P` with `P x · P x = P x`, the sector's weight `Σ P x · f x²` equals what the step keeps in the sector,
`Σ P x · (U(Pf) x)²`, plus what it moves to the offset sector, `Σ (1 − P x) · (U(Pf) x)²`: relaxation is unresolved
leakage held by the offset sector, and the drive, a permutation of the cycle, returns it after `n` steps (`cyc_add_n`).
The interior data of a horizonless body live in that sector; nothing is lost. -/
theorem compression (n : Nat) (hn : 0 < n) (P f : Nat → Shell p) (hP : ∀ x, P x * P x = P x) :
    sumRange (fun x => P x * (P ((x + 1) % n) * f ((x + 1) % n) * (P ((x + 1) % n) * f ((x + 1) % n)))) n
      + sumRange (fun x => (1 + -(P x)) * (P ((x + 1) % n) * f ((x + 1) % n) * (P ((x + 1) % n) * f ((x + 1) % n)))) n
      = sumRange (fun x => P x * (f x * f x)) n := by
  have whole : ∀ x, P x * (P ((x + 1) % n) * f ((x + 1) % n) * (P ((x + 1) % n) * f ((x + 1) % n)))
      + (1 + -(P x)) * (P ((x + 1) % n) * f ((x + 1) % n) * (P ((x + 1) % n) * f ((x + 1) % n)))
      = (fun y => P y * f y * (P y * f y)) ((x + 1) % n) := fun x =>
    RE.sound (look [P x, P ((x + 1) % n) * f ((x + 1) % n)])
      (.add (.mul (.var 0) (.mul (.var 1) (.var 1))) (.mul (.add .one (.neg (.var 0))) (.mul (.var 1) (.var 1))))
      (.mul (.var 1) (.var 1)) (by decide +kernel)
  have square : ∀ x, P x * f x * (P x * f x) = P x * (f x * f x) := fun x => by
    rw [show P x * f x * (P x * f x) = P x * P x * (f x * f x) from
      RE.sound (look [P x, f x]) (.mul (.mul (.var 0) (.var 1)) (.mul (.var 0) (.var 1)))
        (.mul (.mul (.var 0) (.var 0)) (.mul (.var 1) (.var 1))) (by decide +kernel), hP x]
  rw [← sum_add, sum_congr n (fun x _ => whole x), sum_shift n hn (fun y => P y * f y * (P y * f y)) 1]
  exact sum_congr n (fun x _ => square x)

/-! ## The master's block E: the completion, the floor's faces and the fold (00:E4, 00:E5, 00:E10; 12 October 2026) -/

/-- 00:E4, 21:C11, 21:X4 — the exponential reading is the unique scale-covariant one: a function of the drive's steps with the
composition law `f (a + b) = f a · f b` and `f 0 = 1` is the character `f a = (f 1)^a`. -/
theorem character_unique (f : Nat → Shell p) (h0 : f 0 = 1) (hf : ∀ a b, f (a + b) = f a * f b) :
    ∀ a, f a = (f 1) ^ a
  | 0 => h0
  | a + 1 => by rw [hf a 1, character_unique f h0 hf a, pow_succ]

/-- 00:C21 — the PPN temporal form is no character: clock comparison composes as `R(a + b) = R(a) R(b)`, and the form
`1 − 2u` fails it by exactly `4ab`: `(1 − 2a)(1 − 2b) − (1 − 2(a + b)) = 4ab` on every shell (the dilation rigidity
theorem's transitivity defect; 20 October 2026). -/
theorem ppn_defect (a b : Shell p) :
    (1 + -((1 + 1) * a)) * (1 + -((1 + 1) * b)) + -(1 + -((1 + 1) * (a + b))) = (1 + 1 + 1 + 1) * a * b :=
  RE.sound (look [a, b]) (.add (.mul (.add .one (.neg (.mul (.add .one .one) (.var 0)))) (.add .one (.neg (.mul (.add .one .one) (.var 1))))) (.neg (.add .one (.neg (.mul (.add .one .one) (.add (.var 0) (.var 1))))))) (.mul (.mul (.add (.add (.add .one .one) .one) .one) (.var 0)) (.var 1)) (by decide +kernel)

/-- 00:C21 — no register character matches the PPN form beyond first order: a character `n ↦ cⁿ` with `c = 1 − 2u`
(the match at `n = 1`) and `c² = 1 − 4u` (the match at `n = 2`) has `4u² = 0`, so `u = 0` on a frame (an odd prime
shell): the strong-field dilation law is the exponential character alone, with zero coefficient freedom. -/
theorem ppn_no_character {κ : Nat} {g : Shell p} (F : Frame p κ g) {u c : Shell p}
    (h1 : c = 1 + -((1 + 1) * u)) (h2 : c * c = 1 + -((1 + 1 + 1 + 1) * u)) : u = 0 := by
  have e : (1 + -((1 + 1) * u)) * (1 + -((1 + 1) * u)) + -(1 + -((1 + 1 + 1 + 1) * u)) = (1 + 1 + 1 + 1) * (u * u) :=
    RE.sound (look [u]) (.add (.mul (.add .one (.neg (.mul (.add .one .one) (.var 0)))) (.add .one (.neg (.mul (.add .one .one) (.var 0))))) (.neg (.add .one (.neg (.mul (.add (.add (.add .one .one) .one) .one) (.var 0)))))) (.mul (.add (.add (.add .one .one) .one) .one) (.mul (.var 0) (.var 0))) (by decide +kernel)
  rw [← h1, h2, Shell.add_neg] at e
  have h4 : (1 + 1 + 1 + 1 : Shell p) ≠ 0 := fun h0 => by
    have e4 : (1 + 1 + 1 + 1 : Shell p) = (1 + 1) * (1 + 1) :=
      RE.sound (look []) (.add (.add (.add .one .one) .one) .one) (.mul (.add .one .one) (.add .one .one)) (by decide +kernel)
    rw [e4] at h0
    exact match F.mul_eq_zero h0 with
      | Or.inl h => F.two_ne_zero (by rw [two_eq_one_add_one]; exact h)
      | Or.inr h => F.two_ne_zero (by rw [two_eq_one_add_one]; exact h)
  exact match F.mul_eq_zero e.symm with
    | Or.inl h => absurd h h4
    | Or.inr h => match F.mul_eq_zero h with
      | Or.inl h' => h'
      | Or.inr h' => h'

/-- 00:E5, 00:E10, 21:C12 — the operational cut sits between the slip core and the mass, `r_* < r_f < M`, in the chart's own
numbers: with `r_* = √M`, `r_f = 2M/L` (`L = ln Ω`) and `M > (L/2)²`, that is `L² < 4M`, the squares order as
`L² M < (2M)²`; and `r_f < M` reads `2M < L M` once `2 < L`. -/
theorem cut_ordering (L M : Nat) (hM : L * L < 4 * M) (hL : 2 < L) (h0 : 0 < M) :
    L * L * M < 2 * M * (2 * M) ∧ 2 * M < L * M := by
  have e : 2 * M * (2 * M) = 4 * M * M := FRC.Grav.nat_sound (FRC.Grav.nlook [M]) (.mul (.mul (.add .one .one) (.var 0)) (.mul (.add .one .one) (.var 0))) (.mul (.mul (.add (.add (.add .one .one) .one) .one) (.var 0)) (.var 0)) rfl rfl (by decide +kernel)
  exact ⟨by rw [e]; exact Nat.mul_lt_mul_of_pos_right hM h0, Nat.mul_lt_mul_of_pos_right hL h0⟩

/-- 38:C13 — **the apsidal bound is the nesting condition.** A nested Subject `p = q + 1` on a Carrier `Ω` registers the
apsidal fraction `κ/S = (p − 1)/(Ω − 1)` (`Pair.leak_rate`), and the bound `κ/S < 1/(√Ω + 1)` is, squared and cleared
of its root, `(p − 1)²Ω < (Ω − p)²`, which holds exactly when `p² < Ω`: with `Ω = p² + d`, `(Ω − p)² − (p − 1)²Ω =
d(Ω − 1) > 0` for `d ≥ 1`, and with `p² = Ω + d`, `Ω = m + q + 1`, `(Ω − p)² + d(Ω − 1) = (p − 1)²Ω`, so the bound fails.
On the physical Carrier no hosted Subject registers an observed precession (the paper's C13). -/
theorem nesting_bound (q d : Nat) :
    ((q + 1) * (q + 1) + d) - (q + 1) = q * q + q + d ∧
    q * q * ((q + 1) * (q + 1) + d) + d * (q * q + 2 * q + d) = (q * q + q + d) * (q * q + q + d) ∧
    (0 < d → q * q * ((q + 1) * (q + 1) + d) < (q * q + q + d) * (q * q + q + d)) ∧
    (∀ m : Nat, (q + 1) * (q + 1) = m + q + 1 + d →
      m * m + d * (m + q) = q * q * (m + q + 1) ∧ m * m ≤ q * q * (m + q + 1)) := by
  have e0 : (q + 1) * (q + 1) + d = (q * q + q + d) + (q + 1) := FRC.Grav.nat_sound (FRC.Grav.nlook [q, d]) (.add (.mul (.add (.var 0) .one) (.add (.var 0) .one)) (.var 1)) (.add (.add (.add (.mul (.var 0) (.var 0)) (.var 0)) (.var 1)) (.add (.var 0) .one)) rfl rfl (by decide +kernel)
  have e1 : q * q * ((q + 1) * (q + 1) + d) + d * (q * q + 2 * q + d) = (q * q + q + d) * (q * q + q + d) := FRC.Grav.nat_sound (FRC.Grav.nlook [q, d]) (.add (.mul (.mul (.var 0) (.var 0)) (.add (.mul (.add (.var 0) .one) (.add (.var 0) .one)) (.var 1))) (.mul (.var 1) (.add (.add (.mul (.var 0) (.var 0)) (.mul (.add .one .one) (.var 0))) (.var 1)))) (.mul (.add (.add (.mul (.var 0) (.var 0)) (.var 0)) (.var 1)) (.add (.add (.mul (.var 0) (.var 0)) (.var 0)) (.var 1))) rfl rfl (by decide +kernel)
  refine ⟨by rw [e0]; exact FRC.Nat.add_sub_cancel _ _, e1, fun hd => ?_, fun m h => ?_⟩
  · rw [← e1]
    exact Nat.lt_add_of_pos_right (Nat.mul_pos hd (Nat.lt_of_lt_of_le hd (Nat.le_add_left d _)))
  · have i1 : m * m + (m + q) * ((q + 1) * (q + 1)) = q * q * (m + q + 1) + (m + q + 1) * (m + q) := FRC.Grav.nat_sound (FRC.Grav.nlook [q, d, m]) (.add (.mul (.var 2) (.var 2)) (.mul (.add (.var 2) (.var 0)) (.mul (.add (.var 0) .one) (.add (.var 0) .one)))) (.add (.mul (.mul (.var 0) (.var 0)) (.add (.add (.var 2) (.var 0)) .one)) (.mul (.add (.add (.var 2) (.var 0)) .one) (.add (.var 2) (.var 0)))) rfl rfl (by decide +kernel)
    rw [h] at i1
    have i2 : m * m + (m + q) * (m + q + 1 + d) = (m * m + d * (m + q)) + (m + q + 1) * (m + q) := FRC.Grav.nat_sound (FRC.Grav.nlook [q, d, m]) (.add (.mul (.var 2) (.var 2)) (.mul (.add (.var 2) (.var 0)) (.add (.add (.add (.var 2) (.var 0)) .one) (.var 1)))) (.add (.add (.mul (.var 2) (.var 2)) (.mul (.var 1) (.add (.var 2) (.var 0)))) (.mul (.add (.add (.var 2) (.var 0)) .one) (.add (.var 2) (.var 0)))) rfl rfl (by decide +kernel)
    rw [i2] at i1
    have e : m * m + d * (m + q) = q * q * (m + q + 1) := Nat.add_right_cancel i1
    exact ⟨e, by rw [← e]; exact Nat.le_add_right _ _⟩

/-- 00:E10 — the cut area of the graph balls of `ℤ³`, `A_r = 6(2r² + 2r + 1)` (the links between the balls of radii `r` and
`r + 1`; the ledger file's check counts them), grows at every step, `A_{r+1} = A_r + 24(r + 1)`, so the cut current
`Q/A_r` of a fixed enclosed charge recovers `r` from any exterior reading. -/
theorem cut_area_monotone (r : Nat) :
    6 * (2 * (r + 1) * (r + 1) + 2 * (r + 1) + 1) = 6 * (2 * r * r + 2 * r + 1) + 24 * (r + 1) ∧
    6 * (2 * r * r + 2 * r + 1) < 6 * (2 * (r + 1) * (r + 1) + 2 * (r + 1) + 1) := by
  have e : 6 * (2 * (r + 1) * (r + 1) + 2 * (r + 1) + 1) = 6 * (2 * r * r + 2 * r + 1) + 24 * (r + 1) :=
    FRC.Grav.nat_sound (FRC.Grav.nlook [r]) (.mul (.add (.add (.add (.add (.add .one .one) .one) .one) .one) .one) (.add (.add (.mul (.mul (.add .one .one) (.add (.var 0) .one)) (.add (.var 0) .one)) (.mul (.add .one .one) (.add (.var 0) .one))) .one)) (.add (.mul (.add (.add (.add (.add (.add .one .one) .one) .one) .one) .one) (.add (.add (.mul (.mul (.add .one .one) (.var 0)) (.var 0)) (.mul (.add .one .one) (.var 0))) .one)) (.mul (.add (.add (.add (.add (.add (.add (.add (.add (.add (.add (.add (.add (.add (.add (.add (.add (.add (.add (.add (.add (.add (.add (.add .one .one) .one) .one) .one) .one) .one) .one) .one) .one) .one) .one) .one) .one) .one) .one) .one) .one) .one) .one) .one) .one) .one) .one) (.add (.var 0) .one))) rfl rfl (by decide +kernel)
  exact ⟨e, by rw [e]; exact Nat.lt_add_of_pos_right (Nat.mul_pos (Nat.zero_lt_succ 23) (Nat.zero_lt_succ r))⟩

/-- 00:E10 — the two chart branches are two Carrier data: on every frame, for nonzero positions `r₁`, `r₂` the residue
products `r₁ g^Δ` and `r₂` coincide at exactly one lift `Δ < p − 1` (the drive generates, and `g^Δ` is injective below
the full cycle), while the pair `(r, g^{−Δ})` never collides, its first entry being `r`. -/
theorem fold_collision {κ : Nat} {g : Shell p} (F : Frame p κ g) {r₁ r₂ : Shell p} (h₁ : r₁ ≠ 0) (h₂ : r₂ ≠ 0) :
    (∃ Δ, Δ < p - 1 ∧ r₁ * g ^ Δ = r₂) ∧
    (∀ Δ Δ', Δ < p - 1 → Δ' < p - 1 → r₁ * g ^ Δ = r₂ → r₁ * g ^ Δ' = r₂ → Δ = Δ') := by
  refine ⟨?_, fun Δ Δ' hΔ hΔ' e e' => F.pow_inj hΔ hΔ' (F.mul_left_cancel h₁ (e.trans e'.symm))⟩
  obtain ⟨a, ha, hga⟩ := F.generates r₁.val r₁.lt (Nat.pos_of_ne_zero (fun h => h₁ (Shell.ext h)))
  obtain ⟨b, hb, hgb⟩ := F.generates r₂.val r₂.lt (Nat.pos_of_ne_zero (fun h => h₂ (Shell.ext h)))
  have e₁ : g ^ a = r₁ := Shell.ext hga
  have e₂ : g ^ b = r₂ := Shell.ext hgb
  have hab : a ≤ b + (p - 1) := Nat.le_of_lt (Nat.lt_of_lt_of_le ha (Nat.le_add_left (p - 1) b))
  have key : (a + (b + (p - 1) - a) % (p - 1)) % (p - 1) = b := by
    rw [FRC.Nat.add_mod_mod _ _ _ F.n_pos, FRC.Nat.add_sub_of_le hab, FRC.Nat.add_mod b (p - 1) (p - 1) F.n_pos,
      FRC.Nat.mod_self (p - 1) F.n_pos, Nat.add_zero, FRC.Nat.mod_mod b (p - 1) F.n_pos, FRC.Nat.mod_eq_of_lt hb]
  refine ⟨(b + (p - 1) - a) % (p - 1), FRC.Nat.mod_lt' _ F.n_pos, ?_⟩
  calc r₁ * g ^ ((b + (p - 1) - a) % (p - 1)) = g ^ (a + (b + (p - 1) - a) % (p - 1)) := by
        rw [← e₁]; exact (FRC.Shell.pow_add g a _).symm
    _ = g ^ ((a + (b + (p - 1) - a) % (p - 1)) % (p - 1)) := FRC.Cycle.pow_mod (p - 1) F.n_pos F.pow_n _
    _ = g ^ b := by rw [key]
    _ = r₂ := e₂

open FRC.Cycle in
/-- 00:E10 — the fold is a chart projection. On the cycle of `N` sites with the exterior `E`, an interior chart is a map
`F` on cycle functions that returns the exterior values unchanged, with an inverse `Finv` that fixes every function
supported on the exterior. The exterior return through the fold is the bare return, term by term:
`(F (Uⁿ (Finv (P_E f)))) x = (Uⁿ (P_E f)) x` on `x ∈ E`; its period sum is the exterior total, the uniform floor `N⁻¹ J_E`;
and the full period returns, `U^N (P_E f) = P_E f`: no echo criterion. -/
theorem fold_return (N : Nat) (hN : 0 < N) (E : Nat → Bool) (F Finv : (Nat → Shell p) → (Nat → Shell p))
    (hF : ∀ h x, E x = true → F h x = h x) (hFinv : ∀ h, (∀ y, E y = false → h y = 0) → Finv h = h)
    (f : Nat → Shell p) :
    (∀ n x, E x = true →
      F (fun y => cyc N (Finv (fun y => ind E y * f y)) (y + n)) x = cyc N (fun y => ind E y * f y) (x + n)) ∧
    (∀ x, sumRange (fun n => cyc N (fun y => ind E y * f y) (x + n)) N = sumRange (fun y => ind E y * f y) N) ∧
    (∀ x, cyc N (fun y => ind E y * f y) (x + N) = cyc N (fun y => ind E y * f y) x) := by
  have hsupp : ∀ y, E y = false → ind E y * f y = 0 := fun y hy => by
    show (if E y = true then (1 : Shell p) else 0) * f y = 0
    rw [hy, ite_eq_right Bool.false_ne_true, zero_mul]
  refine ⟨fun n x hx => ?_, fun x => ?_, fun x => cyc_add_n N hN _ x⟩
  · rw [hF _ x hx, hFinv _ hsupp]
  · show sumRange (fun n => (fun y => ind E y * f y) ((x + n) % N)) N = _
    have e : ∀ n, n < N → (fun y => (ind E y : Shell p) * f y) ((x + n) % N) = (fun y => (ind E y : Shell p) * f y) ((n + x) % N) :=
      fun n _ => by rw [Nat.add_comm x n]
    rw [FRC.Shell.sum_congr N e]
    exact sum_shift N hN (fun y => (ind E y : Shell p) * f y) x

end FRC.Drift
