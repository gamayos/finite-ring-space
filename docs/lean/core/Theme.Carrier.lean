import FrcCore.Theme.Field
import FrcCore.Theme.Foundation

/-!
# FrcCore.Theme.Carrier — the Carrier on its chart, without a generator (the carrier theme, task LM22)

Master block B on the Carrier's chart `Ω = 4S + 1`, `Ω` prime (`FRC.Nat.isPrime`), and no drive assumed. Every
residue below is found by the prime shell's arithmetic (`Theme/Field.lean`): Fermat's little theorem, the root
bound, the quarter-turn criterion.

* **B5, the substrate residue.** `4 ∣ Ω − 1` and `3 ∣ Ω + 1` jointly hold iff `Ω ≡ 5 (mod 12)`; on a prime
  `Ω > 3` the same as structure: a quarter-turn `ħ² = −1` and no triality root `ω² + ω + 1 = 0` iff `Ω ≡ 5 (mod 12)`.
* **B7, the register in `S` alone.** `c² := 2S + 1 = 2⁻¹`; `G := 2S = −c²`, `2G = −1`, `G` the only solution;
  `ħ² = −1` solvable; `c` exists iff `S` is even; `k_B c = ħ` forces `k_B² = −2`; each defining square fixes its
  root up to sign; `h := −ħ` the distinct partner of `ħ`.
* **B8, the window ladder.** A nested Subject `p² < Ω` has its horizon below the Carrier's quarter-root and its
  shell below the coherence horizon; the saturating Subject `p² < Ω ≤ (p + 1)²` locks both; one square root per
  embedding; the laboratory nesting `37 → 1373 → 2 408 561`.
* **B10, one gauge bit.** `−1` a square; the square class blind to the pair `x ↔ −x`; integer parity flipped by it;
  the faces `x²` pair-invariant and `{ħ, −ħ}` two distinct roots of `−1`.
* **B14, the octant sector.** An element of order eight exists iff `S` is even.

Since task LM24 the chart's generic lemmas (`chart_gt_two`, the octant sector, the Tsirelson square, the half-square
behind `c_exists_iff`, the parity flip) are `Shell.Prime`'s in `Theme/Field.lean`; the old names here are aliases.
No axioms.
-/

namespace FRC
namespace Carrier

open Shell Shell.Prime

/-! ## B5: the substrate residue -/

theorem mod_of_eq {n d k t : Nat} (hd : 0 < d) (h : n = d * k + t) : n % d = t % d := by
  rw [h]; exact FRC.Nat.add_mul_mod_self_left t k d hd

/-- The residues mod `12` of `Ω − 1 ≡ 0 (mod 4)` and `Ω + 1 ≡ 0 (mod 3)`, written for `Ω = n + 1`. -/
theorem mod12_table : ∀ r, r < 12 → ((r % 4 = 0 ∧ (r + 2) % 3 = 0) ↔ (r + 1) % 12 = 5)
  | 0, _ => by decide | 1, _ => by decide | 2, _ => by decide | 3, _ => by decide
  | 4, _ => by decide | 5, _ => by decide | 6, _ => by decide | 7, _ => by decide
  | 8, _ => by decide | 9, _ => by decide | 10, _ => by decide | 11, _ => by decide
  | k + 12, h => absurd h (Nat.not_lt_of_le (Nat.le_add_left 12 k))

/-- B5, the congruence: `4 ∣ Ω − 1` and `3 ∣ Ω + 1` jointly hold iff `Ω ≡ 5 (mod 12)`. -/
theorem substrate_arith (Ω : Nat) : (4 ∣ Ω - 1 ∧ 3 ∣ Ω + 1) ↔ Ω % 12 = 5 := by
  match Ω with
  | 0 => exact ⟨fun h => absurd ((FRC.Nat.dvd_iff_mod (by decide)).1 h.2) (by decide), fun h => absurd h (by decide)⟩
  | n + 1 =>
    rw [FRC.Nat.add_sub_cancel]
    obtain ⟨q, hq⟩ := FRC.Nat.mod_spec 12 (by decide) n
    have hr := Nat.mod_lt n (by decide : 0 < 12)
    generalize n % 12 = r at hq hr
    subst hq
    have e4 : (12 * q + r) % 4 = r % 4 := mod_of_eq (k := 3 * q) (by decide) (by rw [← FRC.Nat.mul_assoc])
    have e3 : (12 * q + r + 1 + 1) % 3 = (r + 2) % 3 :=
      mod_of_eq (k := 4 * q) (by decide) (by rw [← FRC.Nat.mul_assoc, Nat.add_assoc, Nat.add_assoc])
    have e12 : (12 * q + r + 1) % 12 = (r + 1) % 12 := mod_of_eq (k := q) (by decide) (by rw [Nat.add_assoc])
    have key := mod12_table r hr
    constructor
    · intro ⟨h4, h3⟩
      exact e12.trans (key.1 ⟨e4.symm.trans ((FRC.Nat.dvd_iff_mod (by decide)).1 h4),
        e3.symm.trans ((FRC.Nat.dvd_iff_mod (by decide)).1 h3)⟩)
    · intro h
      have k := key.2 (e12.symm.trans h)
      exact ⟨(FRC.Nat.dvd_iff_mod (by decide)).2 (e4.trans k.1), (FRC.Nat.dvd_iff_mod (by decide)).2 (e3.trans k.2)⟩

theorem mod12_table' : ∀ r, r < 12 → ((r % 4 = 1 ∧ r % 3 = 2) ↔ r = 5)
  | 0, _ => by decide | 1, _ => by decide | 2, _ => by decide | 3, _ => by decide
  | 4, _ => by decide | 5, _ => by decide | 6, _ => by decide | 7, _ => by decide
  | 8, _ => by decide | 9, _ => by decide | 10, _ => by decide | 11, _ => by decide
  | k + 12, h => absurd h (Nat.not_lt_of_le (Nat.le_add_left 12 k))

/-- `Ω ≡ 1 (mod 4)` and `Ω ≡ 2 (mod 3)` iff `Ω ≡ 5 (mod 12)`. -/
theorem mod12_iff (n : Nat) : (n % 4 = 1 ∧ n % 3 = 2) ↔ n % 12 = 5 := by
  obtain ⟨q, hq⟩ := FRC.Nat.mod_spec 12 (by decide) n
  have hr := Nat.mod_lt n (by decide : 0 < 12)
  have e4 : n % 4 = n % 12 % 4 := mod_of_eq (k := 3 * q) (by decide) (by rw [← FRC.Nat.mul_assoc]; exact hq)
  have e3 : n % 3 = n % 12 % 3 := mod_of_eq (k := 4 * q) (by decide) (by rw [← FRC.Nat.mul_assoc]; exact hq)
  have key := mod12_table' (n % 12) hr
  exact ⟨fun ⟨h4, h3⟩ => key.1 ⟨e4.symm.trans h4, e3.symm.trans h3⟩,
    fun h => have k := key.2 h; ⟨e4.trans k.1, e3.trans k.2⟩⟩

variable {Ω : Nat} [Pos Ω]

/-- `(x² + x + 1)(x − 1) = x³ − 1`. -/
theorem cube_identity (x : Shell Ω) : (x * x + x + 1) * (x + -1) = x ^ 3 + -1 := by
  have h := geom_sum_mul x 3
  rw [show sumRange (fun l => x ^ l) 3 = x * x + x + 1 by
    show 0 + x ^ 0 + x ^ 1 + x ^ 2 = x * x + x + 1
    rw [zero_add, pow_zero, pow_one, pow_two, add_comm 1 x, add_comm (x + 1) (x * x), ← add_assoc]] at h
  exact h

theorem three_ne_zero (h3 : 3 < Ω) : (1 : Shell Ω) + 1 + 1 ≠ 0 := fun h => by
  have v := val_injective h
  change ((1 % Ω + 1 % Ω) % Ω + 1 % Ω) % Ω = 0 at v
  rw [FRC.Nat.mod_eq_of_lt (Nat.lt_trans (by decide : 1 < 3) h3)] at v
  change (2 % Ω + 1) % Ω = 0 at v
  rw [FRC.Nat.mod_eq_of_lt (Nat.lt_trans (by decide : 2 < 3) h3)] at v
  change 3 % Ω = 0 at v
  rw [FRC.Nat.mod_eq_of_lt h3] at v
  exact absurd v (by decide)

/-- B4's criterion, the triality root: on a prime `Ω > 3`, `ω² + ω + 1 = 0` is solvable iff `Ω ≡ 1 (mod 3)`.
Forward, `ω³ = 1` with `ω ≠ 1`, so `ω^{(Ω−1) mod 3} = 1` leaves only `3 ∣ Ω − 1`; backward, `ω = a^{(Ω−1)/3}` for a
residue `a` that `X^{(Ω−1)/3} − 1` misses. -/
theorem triality_iff (hp : FRC.Nat.isPrime Ω) (h3 : 3 < Ω) :
    (∃ ω : Shell Ω, ω * ω + ω + 1 = 0) ↔ Ω % 3 = 1 := by
  have h1Ω : 1 ≤ Ω := Nat.le_of_lt (Nat.lt_trans (by decide : 1 < 3) h3)
  constructor
  · intro ⟨ω, hω⟩
    have hc : ω ^ 3 = 1 := by
      have e := cube_identity ω
      rw [hω, zero_mul] at e
      exact eq_of_sub_eq_zero e.symm
    have h0 : ω ≠ 0 := fun e => by
      rw [e, mul_zero, zero_add, zero_add] at hω; exact one_ne_zero hp hω
    have h1 : ω ≠ 1 := fun e => by rw [e, mul_one] at hω; exact three_ne_zero h3 hω
    have hcase : (Ω - 1) % 3 = 0 := by
      have hr := pow_mod_eq_one hp h0 (by decide : 0 < 3) hc
      have hlt := Nat.mod_lt (Ω - 1) (by decide : 0 < 3)
      generalize (Ω - 1) % 3 = r at hr hlt
      match r, hr, hlt with
      | 0, _, _ => rfl
      | 1, hr, _ => rw [pow_one] at hr; exact absurd hr h1
      | 2, hr, _ =>
        rw [show (3 : Nat) = 2 + 1 from rfl, pow_succ, hr, one_mul] at hc; exact absurd hc h1
      | k + 3, _, hlt => exact absurd hlt (Nat.not_lt_of_le (Nat.le_add_left 3 k))
    obtain ⟨q, hq⟩ := FRC.Nat.mod_spec 3 (by decide) (Ω - 1)
    rw [hcase, Nat.add_zero] at hq
    exact FRC.Nat.mod_unique (by decide) (by rw [← hq, FRC.Nat.sub_add_cancel h1Ω])
  · intro h
    obtain ⟨m, hm⟩ := FRC.Nat.mod_spec 3 (by decide) Ω
    rw [h] at hm
    have hm0 : 0 < m := by
      match m, hm with
      | 0, hm => rw [hm] at h3; exact absurd h3 (by decide)
      | k + 1, _ => exact Nat.zero_lt_succ k
    have hΩ1 : Ω - 1 = 3 * m := by rw [hm, FRC.Nat.add_sub_cancel]
    have hlt : m < Ω - 1 := by
      rw [hΩ1]
      have := FRC.Nat.mul_lt_mul_of_lt_of_pos (by decide : 1 < 3) hm0
      rw [Nat.one_mul] at this; exact this
    obtain ⟨a, ha, ham⟩ := exists_pow_ne_one hp hm0 hlt
    have hc : (a ^ m) ^ 3 = 1 := by rw [← pow_mul, Nat.mul_comm m 3, ← hΩ1, fermat hp ha]
    have e := cube_identity (a ^ m)
    rw [hc, add_neg] at e
    refine ⟨a ^ m, ?_⟩
    match mul_eq_zero hp e with
    | .inl e1 => exact e1
    | .inr e2 => exact absurd (eq_of_sub_eq_zero e2) ham

/-- B5 as structure: on a prime `Ω > 3`, the quarter-turn (`ħ² = −1` solvable, B3) and the triality centre (no root
of `ω² + ω + 1`, B4) jointly hold iff `Ω ≡ 5 (mod 12)`. -/
theorem substrate_shell (hp : FRC.Nat.isPrime Ω) (h3 : 3 < Ω) :
    ((∃ ħ : Shell Ω, ħ * ħ = -1) ∧ ¬ ∃ ω : Shell Ω, ω * ω + ω + 1 = 0) ↔ Ω % 12 = 5 := by
  have h2 : 2 < Ω := Nat.lt_trans (by decide) h3
  have hq := quarter_turn_iff hp h2
  have ht := triality_iff hp h3
  have h30 : Ω % 3 ≠ 0 := hp.2 3 h3 (by decide)
  have hlt := Nat.mod_lt Ω (by decide : 0 < 3)
  constructor
  · intro ⟨hħ, hω⟩
    refine (mod12_iff Ω).1 ⟨hq.1 hħ, ?_⟩
    have h31 : Ω % 3 ≠ 1 := fun e => hω (ht.2 e)
    generalize Ω % 3 = r at h30 h31 hlt
    match r, h30, h31, hlt with
    | 0, h, _, _ => exact absurd rfl h
    | 1, _, h, _ => exact absurd rfl h
    | 2, _, _, _ => rfl
    | k + 3, _, _, hlt => exact absurd hlt (Nat.not_lt_of_le (Nat.le_add_left 3 k))
  · intro h
    have k := (mod12_iff Ω).2 h
    exact ⟨hq.2 k.1, fun hω => absurd ((ht.1 hω).symm.trans k.2) (by decide)⟩

/-- **B5 (p00015), the substrate residue.** The congruences: `4 ∣ Ω − 1` and `3 ∣ Ω + 1` jointly hold iff
`Ω ≡ 5 (mod 12)`. The structure: on every prime `Ω > 3`, a quarter-turn exists and the triality polynomial has no
root iff `Ω ≡ 5 (mod 12)`. -/
theorem substrate_residue :
    (∀ Ω : Nat, (4 ∣ Ω - 1 ∧ 3 ∣ Ω + 1) ↔ Ω % 12 = 5) ∧
    ∀ {Ω : Nat} [Pos Ω], FRC.Nat.isPrime Ω → 3 < Ω →
      (((∃ ħ : Shell Ω, ħ * ħ = -1) ∧ ¬ ∃ ω : Shell Ω, ω * ω + ω + 1 = 0) ↔ Ω % 12 = 5) :=
  ⟨substrate_arith, fun hp h3 => substrate_shell hp h3⟩

/-! ## B7: the register in `S` alone -/

/-- `G := 2S`, the Carrier's half-period, as a residue of the chart `Ω = 4S + 1`. -/
def grav (Ω : Nat) [Pos Ω] (S : Nat) : Shell Ω := ofNat (2 * S)

/-- `c² := 2S + 1`, the residue the register names `c²` (B7: `c² = 2⁻¹`). -/
def csq (Ω : Nat) [Pos Ω] (S : Nat) : Shell Ω := ofNat (2 * S + 1)

/-- `c² := 2S + 1` is `2⁻¹` on the chart. -/
theorem two_mul_half {S : Nat} (hS : Ω = 4 * S + 1) : (2 : Shell Ω) * csq Ω S = 1 := ext (by
  show (2 % Ω * ((2 * S + 1) % Ω)) % Ω = 1 % Ω
  rw [← FRC.Nat.mul_mod _ _ _ Pos.pos,
    show 2 * (2 * S + 1) = Ω * 1 + 1 by rw [hS, Nat.mul_one, Nat.left_distrib, ← FRC.Nat.mul_assoc],
    FRC.Nat.add_mul_mod_self_left 1 1 Ω Pos.pos])

/-- `G := 2S` is `−c²`. -/
theorem grav_eq {S : Nat} (hS : Ω = 4 * S + 1) : grav Ω S = -csq Ω S := by
  have e : csq Ω S + grav Ω S = 0 := ext (by
    show ((2 * S + 1) % Ω + (2 * S) % Ω) % Ω = 0
    rw [← FRC.Nat.add_mod _ _ _ Pos.pos,
      show 2 * S + 1 + 2 * S = Ω by rw [hS, Nat.add_right_comm, ← Nat.two_mul, ← FRC.Nat.mul_assoc],
      FRC.Nat.mod_self Ω Pos.pos])
  exact (neg_eq_of_add_eq_zero e).symm

theorem two_ne_zero {S : Nat} (hS : Ω = 4 * S + 1) (hp : FRC.Nat.isPrime Ω) : (2 : Shell Ω) ≠ 0 := fun e => by
  have h := two_mul_half hS
  rw [e, zero_mul] at h; exact one_ne_zero hp h.symm

/-- `k_B c = ħ` with `c² = 2⁻¹` and `ħ² = −1` forces `k_B² = −2`. -/
theorem kB_sq {S : Nat} (hS : Ω = 4 * S + 1) {c ħ k : Shell Ω} (hc : c * c = csq Ω S)
    (hħ : ħ * ħ = -1) (hk : k * c = ħ) : k * k = -2 :=
  calc k * k = k * k * 1 := (mul_one _).symm
    _ = k * k * ((2 : Shell Ω) * csq Ω S) := by rw [two_mul_half hS]
    _ = 2 * (k * k * (c * c)) := by rw [hc, mul_left_comm]
    _ = 2 * (ħ * ħ) := by rw [mul_mul_mul_comm, hk]
    _ = -2 := by rw [hħ, ← mul_neg, mul_one]

/-- The root-pair partner: `h := −ħ` is a second, distinct root of `−1`. -/
theorem partner (hp : FRC.Nat.isPrime Ω) (h2 : 2 < Ω) {ħ : Shell Ω} (hh : ħ * ħ = -1) :
    (-ħ) * (-ħ) = -1 ∧ -ħ ≠ ħ := by
  refine ⟨by rw [neg_mul_neg]; exact hh, fun e => ?_⟩
  have h0 := ne_zero_of_mul_self (neg_one_ne_zero hp) hh
  have hs : (1 + 1) * ħ = 0 := by
    rw [right_distrib, one_mul]
    calc ħ + ħ = -ħ + ħ := by rw [e]
      _ = 0 := neg_add ħ
  match mul_eq_zero hp hs with
  | .inl e1 => exact neg_one_ne_one h2 (neg_eq_of_add_eq_zero e1)
  | .inr e2 => exact h0 e2

/-- `c` exists iff `S` is even (`Shell.Prime.half_square_iff`, task LM24): a root `c` of `c² = 2⁻¹` gives `ζ = c (1 + i)`
with `ζ² = i`, an element of order eight; conversely the octant's `ζ` gives `(ζ + ζ⁷)² = 2` and `c = (ζ + ζ⁷)/2`. -/
theorem c_exists_iff (hp : FRC.Nat.isPrime Ω) {S : Nat} (hS : Ω = 4 * S + 1) :
    (∃ c : Shell Ω, c * c = csq Ω S) ↔ S % 2 = 0 :=
  half_square_iff hp hS

/-- **B7 (p00165), the register in `S` alone**, on the chart `Ω = 4S + 1`, `Ω` prime, without a generator:
`c² := 2S + 1` (`csq`) is `2⁻¹`; `G := 2S` (`grav`) is `−c²`, `2G = −1`, and `G` is the only solution (exact);
`ħ² = −1` has a solution; `c` exists iff `S` is even; `k_B c = ħ` forces `k_B² = −2`; a square fixes its root up to
sign; `h := −ħ` is a second, distinct root of `−1`. -/
theorem register {Ω : Nat} [Pos Ω] (S : Nat) (hp : FRC.Nat.isPrime Ω) (hS : Ω = 4 * S + 1) :
    (2 : Shell Ω) * csq Ω S = 1 ∧
    grav Ω S = -csq Ω S ∧
    (2 : Shell Ω) * grav Ω S = -1 ∧ (∀ x : Shell Ω, 2 * x = -1 → x = grav Ω S) ∧
    (∃ ħ : Shell Ω, ħ * ħ = -1) ∧
    ((∃ c : Shell Ω, c * c = csq Ω S) ↔ S % 2 = 0) ∧
    (∀ c ħ k : Shell Ω, c * c = csq Ω S → ħ * ħ = -1 → k * c = ħ → k * k = -2) ∧
    (∀ x y : Shell Ω, x * x = y * y → x = y ∨ x = -y) ∧
    (∀ ħ : Shell Ω, ħ * ħ = -1 → (-ħ) * (-ħ) = -1 ∧ -ħ ≠ ħ) := by
  have hG2 : (2 : Shell Ω) * grav Ω S = -1 := by rw [grav_eq hS, ← mul_neg, two_mul_half hS]
  exact ⟨two_mul_half hS, grav_eq hS, hG2,
    fun x hx => mul_left_cancel hp (two_ne_zero hS hp) (hx.trans hG2.symm),
    exists_quarter_turn hp hS, c_exists_iff hp hS,
    fun _ _ _ hc hħ hk => kB_sq hS hc hħ hk,
    fun _ _ h => sq_eq_sq hp h,
    fun _ hh => partner hp (chart_gt_two hp hS) hh⟩

/-! ## B8: the window ladder -/

theorem lt_of_mul_self_lt {a b : Nat} (h : a * a < b * b) : a < b :=
  match Nat.lt_or_ge a b with
  | .inl hl => hl
  | .inr hge => absurd h (Nat.not_lt_of_le (Nat.mul_le_mul hge hge))

/-- A nested Subject `p² < Ω`: its horizon `√p` lies below the Carrier's quarter-root (`x² ≤ p ⇒ x⁴ < Ω`) and its
shell below the coherence horizon (`x ≤ p ⇒ x² < Ω`). -/
theorem nested_windows {p Ω : Nat} (h : p * p < Ω) :
    (∀ x, x * x ≤ p → x * x * (x * x) < Ω) ∧ (∀ x, x ≤ p → x * x < Ω) :=
  ⟨fun _ hx => Nat.lt_of_le_of_lt (Nat.mul_le_mul hx hx) h,
   fun _ hx => Nat.lt_of_le_of_lt (Nat.mul_le_mul hx hx) h⟩

/-- The saturating Subject `p² < Ω ≤ (p + 1)²` locks the ladder: its horizon is the Carrier's quarter-root window
and its shell the coherence window, exactly. -/
theorem saturated_windows {p Ω : Nat} (h : p * p < Ω) (hs : Ω ≤ (p + 1) * (p + 1)) :
    (∀ x, x * x ≤ p ↔ x * x * (x * x) < Ω) ∧ (∀ x, x ≤ p ↔ x * x < Ω) :=
  ⟨fun x => ⟨(nested_windows h).1 x, fun hx => Nat.le_of_lt_succ (lt_of_mul_self_lt (Nat.lt_of_lt_of_le hx hs))⟩,
   fun x => ⟨(nested_windows h).2 x, fun hx => Nat.le_of_lt_succ (lt_of_mul_self_lt (Nat.lt_of_lt_of_le hx hs))⟩⟩

/-- One square-root horizon per embedding: `q² < p` and `p² < Ω` give `q⁴ < Ω`. -/
theorem nesting {q p Ω : Nat} (hq : q * q < p) (hp : p * p < Ω) : q * q * (q * q) < Ω :=
  (nested_windows hp).1 q (Nat.le_of_lt hq)

/-- The laboratory ladder: `37 → 1373 → 2 408 561`, each prime, `37² < 1373`, `1373² < 2 408 561`. -/
theorem lab_ladder :
    FRC.Nat.isPrime 37 ∧ FRC.Nat.isPrime 1373 ∧ FRC.Nat.isPrime 2408561 ∧ 37 * 37 < 1373 ∧
    1373 * 1373 < 2408561 :=
  ⟨by decide, FRC.Nat.isPrime_of_bounded 1373 37 (by decide) (by decide) (by decide +kernel),
    FRC.Nat.isPrime_of_bounded 2408561 1552 (by decide) (by decide) (by decide +kernel), by decide, by decide⟩

/-- **B8 (p00166), the window ladder.** A nested Subject `p² < Ω` has its horizon below the Carrier's quarter-root
and its shell below the coherence horizon; the saturating Subject `p² < Ω ≤ (p + 1)²` locks both windows; one
square-root horizon per embedding; laboratory-verified on `Ω = 2 408 561` with the nesting `37 → 1373`. -/
theorem window_ladder :
    (∀ p Ω : Nat, p * p < Ω → (∀ x, x * x ≤ p → x * x * (x * x) < Ω) ∧ (∀ x, x ≤ p → x * x < Ω)) ∧
    (∀ p Ω : Nat, p * p < Ω → Ω ≤ (p + 1) * (p + 1) →
      (∀ x, x * x ≤ p ↔ x * x * (x * x) < Ω) ∧ (∀ x, x ≤ p ↔ x * x < Ω)) ∧
    (∀ q p Ω : Nat, q * q < p → p * p < Ω → q * q * (q * q) < Ω) ∧
    (FRC.Nat.isPrime 37 ∧ FRC.Nat.isPrime 1373 ∧ FRC.Nat.isPrime 2408561 ∧ 37 * 37 < 1373 ∧
      1373 * 1373 < 2408561) :=
  ⟨fun _ _ h => nested_windows h, fun _ _ h hs => saturated_windows h hs, fun _ _ _ hq hp => nesting hq hp,
    lab_ladder⟩

/-! ## B10: one gauge bit closes the sign sector -/

/-- The square class is pair-blind: `x` is a square iff `−x` is (`(ħy)² = −y²`). -/
theorem square_pair_blind (hp : FRC.Nat.isPrime Ω) {S : Nat} (hS : Ω = 4 * S + 1) (x : Shell Ω) :
    (∃ y : Shell Ω, y * y = x) ↔ (∃ y : Shell Ω, y * y = -x) := by
  obtain ⟨h, hh⟩ := exists_quarter_turn hp hS
  exact ⟨fun ⟨y, hy⟩ => ⟨h * y, by rw [mul_mul_mul_comm, hh, hy, neg_one_mul]⟩,
    fun ⟨y, hy⟩ => ⟨h * y, by rw [mul_mul_mul_comm, hh, hy, neg_one_mul, neg_neg]⟩⟩

/-- **B10 (p00168), one gauge bit closes the sign sector**, on the chart `Ω = 4S + 1`, `Ω` prime: `−1` is a
square; the square class is blind to the pair `x ↔ −x`; integer parity is flipped by it, so it is frame data; the
registered faces are pair-invariant, `(−x)² = x²`, and `{ħ, −ħ}` are two distinct roots of `−1`. -/
theorem sign_sector {Ω : Nat} [Pos Ω] (S : Nat) (hp : FRC.Nat.isPrime Ω) (hS : Ω = 4 * S + 1) :
    (∃ ħ : Shell Ω, ħ * ħ = -1) ∧
    (∀ x : Shell Ω, (∃ y : Shell Ω, y * y = x) ↔ (∃ y : Shell Ω, y * y = -x)) ∧
    (∀ x : Shell Ω, x ≠ 0 → (x.val % 2 = 0 ↔ ¬ (-x).val % 2 = 0)) ∧
    (∀ x : Shell Ω, (-x) * (-x) = x * x) ∧
    (∀ ħ : Shell Ω, ħ * ħ = -1 → (-ħ) * (-ħ) = -1 ∧ -ħ ≠ ħ) :=
  ⟨exists_quarter_turn hp hS, square_pair_blind hp hS, fun _ hx => parity_flips hS hx, fun x => neg_mul_neg x x,
    fun _ hh => partner hp (chart_gt_two hp hS) hh⟩

/-- **B14 (p00170)**, as a key: on the chart, `C₈ ⊂ C_{4S}` exists exactly when `S` is even. -/
theorem octant {Ω : Nat} [Pos Ω] (S : Nat) (hp : FRC.Nat.isPrime Ω) (hS : Ω = 4 * S + 1) :
    (∃ ζ : Shell Ω, ζ ^ 8 = 1 ∧ ζ ^ 4 ≠ 1) ↔ S % 2 = 0 :=
  octant_sector hp hS

/-! ## Old names (task LM24): the chart's lemmas are `Shell.Prime`'s, in `Theme/Field.lean` -/

omit [Pos Ω] in
theorem chart_gt_two (hp : FRC.Nat.isPrime Ω) {S : Nat} (hS : Ω = 4 * S + 1) : 2 < Ω := Prime.chart_gt_two hp hS
theorem two_eq : (2 : Shell Ω) = 1 + 1 := Prime.two_eq
theorem add_one_add_one_neg (a : Shell Ω) : a + 1 + (1 + -a) = 1 + 1 := Prime.add_one_add_one_neg a
theorem octant_sector (hp : FRC.Nat.isPrime Ω) {S : Nat} (hS : Ω = 4 * S + 1) :
    (∃ ζ : Shell Ω, ζ ^ 8 = 1 ∧ ζ ^ 4 ≠ 1) ↔ S % 2 = 0 := Prime.octant_sector hp hS
theorem tsirelson {ζ : Shell Ω} (h4 : ζ ^ 4 = -1) : (ζ + ζ ^ 7) * (ζ + ζ ^ 7) = 2 := Prime.tsirelson h4
theorem parity_flips {S : Nat} (hS : Ω = 4 * S + 1) {x : Shell Ω} (hx : x ≠ 0) :
    x.val % 2 = 0 ↔ ¬ (-x).val % 2 = 0 := Prime.parity_flips hS hx

end Carrier
end FRC
