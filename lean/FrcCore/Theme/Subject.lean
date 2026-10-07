import FrcCore.Theme.Field
import FrcCore.FrameCore
import FrcCore.Parity
import FrcCore.Theme.Quadratic

/-!
# FrcCore.Theme.Subject — the Subject: the frame, the signature, the square class, the chirality (the subject theme)

Master block C, task LM24, on the Subject's frame `(τ; 0, 1, g)` (`FrameCore.lean`, `Parity.lean`) and on the prime
shell without a generator (`Theme/Field.lean`, `Theme/Quadratic.lean`):

* **C1** the frame's web: `2π ≡ −1`, `g^π = −1`, `−π = 2⁻¹`, `i² = −1`, `g` the one nonsquare datum (`frame_web`);
* **C3** the signature: the norm form `x² − ν t²` is isotropic iff `ν` is a square, `ν = 2⁻¹ · 2g`, the classes of
  `2⁻¹` and `2g` fixed by the parity of `κ` (`signature`);
* **C8** the square class is chronon parity (`square_class`);
* **C13** its part 10:G2, the exponent-window ladder on every capacity, the threshold `κ ≥ 17` exact (`exponent_ladder`);
* **C14** the quarter-turn is the odd member of the `±√−1` pair, the conjugate chart toggles it, and the parity names
  the chirality class of the generator (`quarter_turn_odd`);
* **C16** the spinor dichotomy: `κ` odd iff `v₂(p − 1) = 2` iff the fold `(r, s) ↦ iʳ g^{4s}` is a bijection
  `C₄ × C_κ → 𝔽_p^×` iff `3κr + 4s ≡ 1 (mod 4κ)` is solvable; the shared 2-part and the cover degree (`spinor`);
* **C20** the mass–energy channel: `C_{p−1}` meets `C_{p+1}` in `±1` and `C_{2(p+1)}` in `Q₄`, `N(i) = −1` (`channel`);
* **C25** the horizon is the origin's antipode on the boost torus: the torsor map `P¹ → C_{p+1}`, `P ↦ u_P/ū_P`, is an
  equivariant bijection sending the origin to `1` and the horizon to `−1`, exchanged by the torus's one involution
  `q ↦ ν/q`; the additive antipode is no residue (`horizon_antipode`). No axioms.
-/

namespace FRC.Subject

open FRC.Shell

variable {p : Nat} [Pos p]

/-! ## Two helpers: a frame's shell is prime, and the inverse on a prime shell -/

/-- A frame's shell is prime: it has no zero divisors, and completeness is primality. -/
theorem frame_isPrime {κ : Nat} {g : Shell p} (F : Frame p κ g) : FRC.Nat.isPrime p :=
  Prime.isPrime_of_no_zero_divisors (Nat.le_of_lt F.two_lt_p) (fun h => F.mul_eq_zero h)

/-- The inverse on a prime shell, `a⁻¹ = a^{p−2}` (Fermat). -/
def inv (a : Shell p) : Shell p := a ^ (p - 2)

theorem mul_inv (hp : FRC.Nat.isPrime p) {a : Shell p} (ha : a ≠ 0) : a * inv a = 1 := by
  have e : p - 1 = p - 2 + 1 := by
    match p, hp.1 with
    | k + 2, _ => rfl
  rw [mul_comm, inv, ← pow_succ, ← e, Prime.fermat hp ha]

theorem inv_ne_zero (hp : FRC.Nat.isPrime p) {a : Shell p} (ha : a ≠ 0) : inv a ≠ 0 := fun h => by
  have := mul_inv hp ha; rw [h, mul_zero] at this; exact Prime.one_ne_zero hp this.symm

theorem even_add {a b : Nat} (h : (a + b) % 2 = 0) : a % 2 = 0 ↔ b % 2 = 0 := by
  rw [FRC.Nat.add_mod _ _ _ (Nat.zero_lt_succ 1)] at h
  constructor
  · intro ha; rw [ha, Nat.zero_add, FRC.Nat.mod_mod _ _ (Nat.zero_lt_succ 1)] at h; exact h
  · intro hb; rw [hb, Nat.add_zero, FRC.Nat.mod_mod _ _ (Nat.zero_lt_succ 1)] at h; exact h

/-! ## C1: the frame's web -/

/-- **C1 (p00021), the frame's web.** On every frame, `π = 2κ` and `i = −g^κ`: `2π ≡ −1`, `g^π = −1`, `−π = 2⁻¹`,
`i² = −1`; `0` and `1` are squares and the drive is not, the one nonsquare frame datum. -/
theorem frame_web {κ : Nat} {g : Shell p} (F : Frame p κ g) :
    (ofNat (2 * Frame.halfPeriod κ) : Shell p) = -1 ∧ g ^ Frame.halfPeriod κ = -1 ∧
    -(ofNat (Frame.halfPeriod κ) : Shell p) * 2 = 1 ∧ Frame.quarterTurn g κ * Frame.quarterTurn g κ = -1 ∧
    (∃ y : Shell p, y * y = 0) ∧ (∃ y : Shell p, y * y = 1) ∧ ¬ ∃ y : Shell p, y * y = g := by
  refine ⟨F.two_pi, F.half_period, ?_, F.quarter_turn_sq, ⟨0, mul_zero 0⟩, ⟨1, mul_one 1⟩, F.drive_nonsquare⟩
  have e : (ofNat (Frame.halfPeriod κ) : Shell p) * 2 = -1 := by
    rw [show (2 : Shell p) = ofNat 2 from rfl, Prime.ofNat_mul, Nat.mul_comm]; exact F.two_pi
  rw [← neg_mul, e, neg_neg]

/-! ## C3: the signature -/

/-- **C3 (p00150), the Euclidean–Lorentzian dichotomy.** On every frame the temporal coefficient `ν = g` is a
nonsquare; the norm form `x² − ν t²` has a zero with `t ≠ 0` iff `ν` is a square (split torus) and none otherwise
(non-split); `ν = 2⁻¹ · (2g)`, and the classes of `2⁻¹` and `2g` are fixed by the parity of `κ`. -/
theorem signature {κ : Nat} {g : Shell p} (F : Frame p κ g) :
    (¬ ∃ y : Shell p, y * y = g) ∧
    (∀ ν : Shell p, (∃ t x : Shell p, t ≠ 0 ∧ x * x = ν * (t * t)) ↔ ∃ w : Shell p, w * w = ν) ∧
    (∀ h : Shell p, 2 * h = 1 → h * (2 * g) = g ∧ ((∃ r : Shell p, r * r = h) ↔ κ % 2 = 0) ∧
      ((∃ r : Shell p, r * r = 2 * g) ↔ κ % 2 = 1)) := by
  have hp := frame_isPrime F
  refine ⟨F.drive_nonsquare, fun ν => ⟨fun ⟨t, x, ht, e⟩ => ?_, fun ⟨w, hw⟩ => ⟨1, w, F.one_ne_zero, by rw [mul_one, mul_one, hw]⟩⟩,
    fun h h2 => ?_⟩
  · obtain ⟨s, hs⟩ := F.exists_inv ht
    exact ⟨x * s, by rw [mul_mul_mul_comm, e, mul_assoc, ← mul_mul_mul_comm, hs, mul_one, mul_one]⟩
  · have hh0 : h ≠ 0 := fun e => by rw [e, mul_zero] at h2; exact F.one_ne_zero h2.symm
    have hh : h = ofNat (2 * κ + 1) :=
      Prime.mul_left_cancel hp F.two_ne_zero (h2.trans (Prime.two_mul_chart_half F.cap).symm)
    have hsq : (∃ r : Shell p, r * r = h) ↔ κ % 2 = 0 := by rw [hh]; exact Prime.half_square_iff hp F.cap
    refine ⟨by rw [← mul_assoc, mul_comm h 2, h2, one_mul], hsq, ?_⟩
    obtain ⟨a, _, ha⟩ := F.eq_pow_of_ne_zero hh0
    obtain ⟨b, _, hb⟩ := F.eq_pow_of_ne_zero F.two_ne_zero
    have hab : (a + b) % 2 = 0 := by
      have h1 : g ^ (a + b) = 1 := by rw [pow_add, ha, hb, mul_comm]; exact h2
      obtain ⟨q, hq⟩ := FRC.Nat.mod_spec (p - 1) F.n_pos (a + b)
      rw [F.mod_eq_zero_of_pow_eq_one h1, Nat.add_zero, F.n_eq, FRC.Nat.mul_assoc] at hq
      rw [hq, show 4 = 2 * 2 from rfl, FRC.Nat.mul_assoc]; exact Frame.two_mul_mod _
    have h2g : 2 * g = g ^ (b + 1) := by rw [pow_succ, hb]
    rw [h2g]
    refine (F.parity_iff (b + 1)).trans ((Frame.succ_mod_two_eq_zero_iff b).trans ?_)
    have hA : a % 2 = 0 ↔ κ % 2 = 0 := (F.parity_iff a).symm.trans (by rw [ha]; exact hsq)
    constructor
    · intro hb1
      match Frame.mod_two_cases κ with
      | .inr e => exact e
      | .inl e => rw [(even_add hab).1 (hA.2 e)] at hb1; exact absurd hb1 (by decide)
    · intro hk
      match Frame.mod_two_cases b with
      | .inr e => exact e
      | .inl e => rw [hA.1 ((even_add hab).2 e)] at hk; exact absurd hk (by decide)

/-! ## C8: the square class is chronon parity -/

/-- **C8 (p00028), the square class is chronon parity.** On every frame `g^m` is a square iff `m` is even: the
registered (two-way) transport `g²` is even, the one-way multiplier `g` and its inverse odd. -/
theorem square_class {κ : Nat} {g : Shell p} (F : Frame p κ g) :
    (∀ m : Nat, (∃ y : Shell p, y * y = g ^ m) ↔ m % 2 = 0) ∧ (¬ ∃ y : Shell p, y * y = g) ∧
    (∀ y : Shell p, g * y = 1 → ¬ ∃ r : Shell p, r * r = y) ∧ (∃ y : Shell p, y * y = g * g) :=
  ⟨F.parity_iff, F.drive_nonsquare, fun _ hy => F.inv_drive_nonsquare hy, ⟨g, rfl⟩⟩

/-- The Carrier's class `[c²] = [2⁻¹]` (C3, C8): on a prime `p = 4S + 1`, the half `h` (`2h = 1`) is a square iff `S`
is even; the half is `2S + 1` (`Prime.half_square_iff`). -/
theorem half_class (hp : FRC.Nat.isPrime p) {S : Nat} (hS : p = 4 * S + 1) :
    ∀ h : Shell p, 2 * h = 1 → ((∃ c : Shell p, c * c = h) ↔ S % 2 = 0) := fun h h2 => by
  have hh : h = ofNat (2 * S + 1) :=
    calc h = h * (2 * ofNat (2 * S + 1)) := by rw [Prime.two_mul_chart_half hS, mul_one]
      _ = 2 * h * ofNat (2 * S + 1) := by rw [← mul_assoc, mul_comm h 2]
      _ = ofNat (2 * S + 1) := by rw [h2, one_mul]
  rw [hh]; exact Prime.half_square_iff hp hS

/-! ## C20: the mass–energy channel -/

/-- **C20 (p00040), the mass–energy channel**, generator-free on a prime `p` with a quarter-turn `h² = −1`: inside
`𝔽_{p²}^×`, `C_{p−1} = 𝔽_p^×` meets the boost torus `C_{p+1} = {z^{p+1} = 1}` in the sign `±1` alone, and the spinor
cover `C_{2(p+1)}` in exactly `Q₄ = {±1, ±h}`; the quarter is spinorial, `N(h) = h^{p+1} = h² = −1`. -/
theorem channel (hp : FRC.Nat.isPrime p) {h : Shell p} (hh : h * h = -1) :
    (∀ x : Shell p, x ≠ 0 → (x ^ (p + 1) = 1 ↔ x = 1 ∨ x = -1)) ∧
    (∀ x : Shell p, x ≠ 0 → (x ^ (2 * (p + 1)) = 1 ↔ x = 1 ∨ x = -1 ∨ x = h ∨ x = -h)) ∧ h ^ (p + 1) = -1 := by
  have e : p + 1 = p - 1 + 2 := by
    match p, hp.1 with
    | k + 2, _ => rfl
  have hN : ∀ x : Shell p, x ≠ 0 → x ^ (p + 1) = x * x := fun x hx => by
    rw [e, pow_add, Prime.fermat hp hx, one_mul, pow_two]
  have h0 : h ≠ 0 := Prime.ne_zero_of_mul_self (Prime.neg_one_ne_zero hp) hh
  have hsq1 : ∀ x : Shell p, x * x = 1 ↔ x = 1 ∨ x = -1 := fun x =>
    ⟨Prime.sq_eq_one hp, fun hx => match hx with
      | .inl e => by rw [e, mul_one]
      | .inr e => by rw [e, neg_mul_neg, mul_one]⟩
  refine ⟨fun x hx => by rw [hN x hx]; exact hsq1 x, fun x hx => ?_, by rw [hN h h0, hh]⟩
  rw [show 2 * (p + 1) = (p + 1) * 2 from Nat.mul_comm 2 (p + 1), pow_mul, hN x hx, pow_two]
  refine (hsq1 (x * x)).trans ?_
  constructor
  · intro hx2
    match hx2 with
    | .inl e1 => exact match (hsq1 x).1 e1 with
      | .inl a => .inl a
      | .inr a => .inr (.inl a)
    | .inr e1 => exact match Prime.sq_eq_sq hp (e1.trans hh.symm) with
      | .inl a => .inr (.inr (.inl a))
      | .inr a => .inr (.inr (.inr a))
  · intro hx
    match hx with
    | .inl a => exact .inl ((hsq1 x).2 (.inl a))
    | .inr (.inl a) => exact .inl ((hsq1 x).2 (.inr a))
    | .inr (.inr (.inl a)) => exact .inr (by rw [a, hh])
    | .inr (.inr (.inr a)) => exact .inr (by rw [a, neg_mul_neg, hh])

/-- C20's Carrier instance (38:A4): on `Ω = 233`, `78^58 = 89 = ħ`, a root of `−1`. -/
theorem channel_233 : (78 : Shell 233) ^ 58 = 89 ∧ (89 : Shell 233) * 89 = -1 := by decide

/-! ## C13's part 10:G2: the exponent-window ladder on every capacity -/

/-- **10:G2 (p10038), the exponent-window ladder, on every capacity** (C13's first part; the key is paper 10's): coherence
`2√κ` lies below recovery `κ/2` iff `16κ < κ²` iff `κ ≥ 17`, so the threshold is exact and the toy `κ = 3` fails;
recovery `κ/2` below flag inaccessibility `κ`, and the flag below covariance `2κ`, both `κ < 2κ`; and the coherence
identity `(2√κ)² = 4κ = p − 1` on `p = 4κ + 1`. -/
theorem exponent_ladder :
    (∀ κ : Nat, 16 * κ < κ * κ ↔ 17 ≤ κ) ∧ (∀ κ : Nat, 0 < κ → κ < 2 * κ) ∧ (∀ κ : Nat, 2 * 2 * κ = 4 * κ + 1 - 1) := by
  refine ⟨fun κ => ⟨fun h => ?_, fun h => FRC.Nat.mul_lt_mul_of_lt_of_pos h (Nat.lt_of_lt_of_le (by decide) h)⟩,
    fun κ hκ => ?_, fun κ => rfl⟩
  · match Nat.lt_or_ge κ 17 with
    | .inr h' => exact h'
    | .inl h' => exact absurd (Nat.lt_of_lt_of_le h (Nat.mul_le_mul_right κ (Nat.le_of_lt_succ h'))) (Nat.lt_irrefl _)
  · have := FRC.Nat.mul_lt_mul_of_lt_of_pos (by decide : 1 < 2) hκ
    rwa [Nat.one_mul] at this

/-! ## C14: the quarter-turn is the odd member of the `±√−1` pair -/

theorem parity_ne {a b : Nat} (h : a % 2 = 0 ↔ ¬ b % 2 = 0) : a % 2 ≠ b % 2 := fun e =>
  match Frame.mod_two_cases a with
  | .inl ha => h.1 ha (e ▸ ha)
  | .inr ha => (show a % 2 ≠ 0 by rw [ha]; decide) (h.2 (by rw [← e, ha]; decide))

/-- **C14 (p00034), the quarter-turn is the odd member of the `±√−1` pair.** On every frame: the Euler identity
`e^{iπ} := (g^i)^{i·2κ} = (−1)^i` for every lift `i`; the two roots of `−1` have representatives of opposite parity,
so `e^{iπ} = −1` holds exactly on the odd one; the conjugate chart (the inverse drive) is a frame and toggles the
quarter-turn; and every frame is `g^u` with `u` odd, its quarter-turn the same as `g`'s when `u ≡ 1 (mod 4)` and the
negative when `u ≡ 3`, so the parity of the quarter-turn names the chirality class. -/
theorem quarter_turn_odd {κ : Nat} {g : Shell p} (F : Frame p κ g) :
    (∀ i : Nat, (g ^ i) ^ (i * (2 * κ)) = if i % 2 = 0 then 1 else -1) ∧
    (∀ h : Shell p, h * h = -1 → (h.val % 2 = 0 ↔ ¬ (-h).val % 2 = 0)) ∧
    (∀ h : Shell p, h * h = -1 → ((g ^ h.val) ^ (h.val * (2 * κ)) = -1 ↔ h.val % 2 = 1)) ∧
    (∀ y : Shell p, g * y = 1 → Frame p κ y ∧ Frame.quarterTurn y κ = -Frame.quarterTurn g κ) ∧
    (∀ g' : Shell p, Frame p κ g' → ∃ u : Nat, u < p - 1 ∧ g ^ u = g' ∧ (u % 4 = 1 ∨ u % 4 = 3) ∧
      (u % 4 = 1 → Frame.quarterTurn g' κ = Frame.quarterTurn g κ) ∧
      (u % 4 = 3 → Frame.quarterTurn g' κ = -Frame.quarterTurn g κ) ∧
      ((Frame.quarterTurn g' κ).val % 2 = (Frame.quarterTurn g κ).val % 2 ↔ u % 4 = 1)) := by
  have hp := frame_isPrime F
  have hroot : ∀ h : Shell p, h * h = -1 → h ≠ 0 := fun h hh => Prime.ne_zero_of_mul_self (Prime.neg_one_ne_zero hp) hh
  have hflip : ∀ x : Shell p, x ≠ 0 → (x.val % 2 = 0 ↔ ¬ (-x).val % 2 = 0) := fun x hx => Prime.parity_flips F.cap hx
  refine ⟨F.euler_identity, fun h hh => hflip h (hroot h hh), fun h _ => ?_, fun y hy => ?_, fun g' F' => ?_⟩
  · rw [F.euler_identity]
    match Frame.mod_two_cases h.val with
    | .inl e => rw [ite_eq_left e, e]
                exact ⟨fun e1 => absurd e1.symm (Prime.neg_one_ne_one F.two_lt_p), fun e1 => absurd e1 (by decide)⟩
    | .inr e => rw [ite_eq_right (by rw [e]; decide), e]; exact ⟨fun _ => rfl, fun _ => rfl⟩
  · have hpow : ∀ l, g ^ l * y ^ l = 1 := fun l => by rw [← mul_pow, hy, one_pow]
    have Fy : Frame p κ y := ⟨F.cap, F.cap_pos,
      ⟨by have := hpow (p - 1); rwa [F.pow_n, one_mul] at this,
       fun l hl hl0 e => F.prim.2 l hl hl0 (by have := hpow l; rwa [e, mul_one] at this)⟩⟩
    refine ⟨Fy, ?_⟩
    have e1 : g ^ κ * y ^ κ = g ^ κ * -(g ^ κ) := by
      rw [hpow κ, ← mul_neg, ← pow_add, ← Nat.two_mul, F.half_period, neg_neg]
    show -(y ^ κ) = -(-(g ^ κ))
    rw [Prime.mul_left_cancel hp (F.pow_ne_zero κ) e1]
  · obtain ⟨u, hu, hgu⟩ := F.eq_pow_of_ne_zero F'.g_ne_zero
    have hodd : u % 2 = 1 := match Frame.mod_two_cases u with
      | .inr e => e
      | .inl e => absurd (hgu ▸ (F.parity_iff u).2 e) F'.drive_nonsquare
    have h4 : u % 4 = 1 ∨ u % 4 = 3 := by
      obtain ⟨q, hq⟩ := FRC.Nat.mod_spec 4 (by decide) u
      have hm : (u % 4) % 2 = 1 := by rw [← Frame.mod_two_of_mod_four_mul (u % 4) q, ← hq]; exact hodd
      have hlt := Nat.mod_lt u (by decide : 0 < 4)
      generalize u % 4 = r at hm hlt ⊢
      match r, hm, hlt with
      | 1, _, _ => exact .inl rfl
      | 3, _, _ => exact .inr rfl
      | 0, hm, _ => exact absurd hm (by decide)
      | 2, hm, _ => exact absurd hm (by decide)
      | k + 4, _, hlt => exact absurd hlt (Nat.not_lt_of_le (Nat.le_add_left 4 k))
    have hq1 : u % 4 = 1 → Frame.quarterTurn g' κ = Frame.quarterTurn g κ := fun e => by
      rw [← hgu]; exact (F.orientation_class u).1 e
    have hq3 : u % 4 = 3 → Frame.quarterTurn g' κ = -Frame.quarterTurn g κ := fun e => by
      rw [← hgu]; exact (F.orientation_class u).2 e
    refine ⟨u, hu, hgu, h4, hq1, hq3, fun hpar => ?_, fun e => by rw [hq1 e]⟩
    match h4 with
    | .inl e => exact e
    | .inr e =>
      rw [hq3 e] at hpar
      exact absurd hpar.symm (parity_ne (hflip _ (hroot _ F.quarter_turn_sq)))

/-! ## C16: the spinor dichotomy -/

/-- `n = 4q + r`, `r < 4`, by counting: no division. -/
def qr4 : Nat → Nat × Nat
  | 0 => (0, 0)
  | n + 1 => if (qr4 n).2 = 3 then ((qr4 n).1 + 1, 0) else ((qr4 n).1, (qr4 n).2 + 1)

theorem qr4_spec : ∀ n, n = 4 * (qr4 n).1 + (qr4 n).2 ∧ (qr4 n).2 < 4
  | 0 => ⟨rfl, by decide⟩
  | n + 1 => by
    have ih := qr4_spec n
    show n + 1 = 4 * (if (qr4 n).2 = 3 then ((qr4 n).1 + 1, 0) else ((qr4 n).1, (qr4 n).2 + 1)).1 +
      (if (qr4 n).2 = 3 then ((qr4 n).1 + 1, 0) else ((qr4 n).1, (qr4 n).2 + 1)).2 ∧
      (if (qr4 n).2 = 3 then ((qr4 n).1 + 1, 0) else ((qr4 n).1, (qr4 n).2 + 1)).2 < 4
    generalize qr4 n = x at ih ⊢
    obtain ⟨q, r⟩ := x
    obtain ⟨e, hr⟩ := ih
    change n = 4 * q + r at e
    change r < 4 at hr
    show n + 1 = 4 * (if r = 3 then (q + 1, 0) else (q, r + 1)).1 + (if r = 3 then (q + 1, 0) else (q, r + 1)).2 ∧
      (if r = 3 then (q + 1, 0) else (q, r + 1)).2 < 4
    match Nat.decEq r 3 with
    | .isTrue h3 =>
      rw [ite_eq_left h3, e, h3]
      exact ⟨by show 4 * q + 3 + 1 = 4 * (q + 1) + 0; rw [Nat.left_distrib], by show 0 < 4; decide⟩
    | .isFalse h3 =>
      rw [ite_eq_right h3, e]
      exact ⟨Nat.add_assoc _ _ _, Nat.succ_lt_succ (Nat.lt_of_le_of_ne (Nat.le_of_lt_succ hr) h3)⟩

/-- The fold `iʳ (g⁴)ˢ = g^{3κr + 4s}` (`i = −g^κ = g^{3κ}`). -/
theorem fold_eq {κ : Nat} {g : Shell p} (F : Frame p κ g) (r s : Nat) :
    Frame.quarterTurn g κ ^ r * (g ^ 4) ^ s = g ^ (3 * κ * r + 4 * s) := by
  have hi : Frame.quarterTurn g κ = g ^ (3 * κ) := by
    show -(g ^ κ) = g ^ (3 * κ)
    rw [show 3 * κ = 2 * κ + κ by rw [Nat.succ_mul, Nat.add_comm], pow_add, F.half_period, neg_one_mul]
  rw [hi, ← pow_mul, ← pow_mul, ← pow_add]

theorem pow_ne_zero (hp : FRC.Nat.isPrime p) {x : Shell p} (hx : x ≠ 0) : ∀ k : Nat, x ^ k ≠ 0
  | 0 => Prime.one_ne_zero hp
  | k + 1 => Prime.mul_ne_zero hp (pow_ne_zero hp hx k) hx

/-- An element with `j² = −1` tells `0, 1, 2, 3` apart: `jʳ = jʳ'` with `r, r' < 4` gives `r = r'`. -/
theorem quarter_pow_inj (hp : FRC.Nat.isPrime p) (h2 : 2 < p) {j : Shell p} (hj : j * j = -1) :
    ∀ {r r' : Nat}, r < 4 → r' < 4 → j ^ r = j ^ r' → r = r' := by
  have hne : (-1 : Shell p) ≠ 1 := Prime.neg_one_ne_one h2
  have hj0 : j ≠ 0 := Prime.ne_zero_of_mul_self (Prime.neg_one_ne_zero hp) hj
  have one : ∀ d, d < 4 → j ^ d = 1 → d = 0 := fun d hd e => by
    match d, hd, e with
    | 0, _, _ => rfl
    | 1, _, e => rw [pow_one] at e; rw [e, mul_one] at hj; exact absurd hj.symm hne
    | 2, _, e => rw [pow_two, hj] at e; exact absurd e hne
    | 3, _, e =>
      rw [show (3 : Nat) = 2 + 1 from rfl, pow_succ, pow_two, hj, neg_one_mul] at e
      rw [← neg_neg j, e, neg_mul_neg, mul_one] at hj; exact absurd hj.symm hne
    | k + 4, hd, _ => exact absurd hd (Nat.not_lt_of_le (Nat.le_add_left 4 k))
  have key : ∀ {r r' : Nat}, r' ≤ r → r < 4 → j ^ r = j ^ r' → r = r' := fun {r r'} hle hr e => by
    have e1 : j ^ r' * j ^ (r - r') = j ^ r' * 1 := by rw [← pow_add, FRC.Nat.add_sub_of_le hle, mul_one, e]
    have h0 := one (r - r') (Nat.lt_of_le_of_lt (Nat.sub_le r r') hr)
      (Prime.mul_left_cancel hp (pow_ne_zero hp hj0 r') e1)
    rw [← FRC.Nat.add_sub_of_le hle, h0, Nat.add_zero]
  intro r r' hr hr' e
  match Nat.lt_or_ge r r' with
  | .inl hlt => exact (key (Nat.le_of_lt hlt) hr' e.symm).symm
  | .inr hge => exact key hge hr e

/-- **C16 (p00151), the spinor dichotomy**, on every frame (`p − 1 = 4κ`, `i = −g^κ`): `κ` is odd iff
`v₂(p − 1) = 2` (`8 ∤ p − 1`) iff the fold `(r, s) ↦ iʳ (g⁴)ˢ` is injective on `C₄ × C_κ`, and then onto `𝔽_p^×`, so
`C_{p−1} ≅ C₄ × C_κ`; and iff `3κr + 4s ≡ 1 (mod 4κ)` is solvable. -/
theorem spinor {κ : Nat} {g : Shell p} (F : Frame p κ g) :
    (κ % 2 = 1 ↔ (p - 1) % 8 ≠ 0) ∧
    (κ % 2 = 1 ↔ ∀ r s r' s' : Nat, r < 4 → s < κ → r' < 4 → s' < κ →
        Frame.quarterTurn g κ ^ r * (g ^ 4) ^ s = Frame.quarterTurn g κ ^ r' * (g ^ 4) ^ s' → r = r' ∧ s = s') ∧
    (κ % 2 = 1 → ∀ x : Shell p, x ≠ 0 → ∃ r s : Nat, r < 4 ∧ s < κ ∧ Frame.quarterTurn g κ ^ r * (g ^ 4) ^ s = x) ∧
    (κ % 2 = 1 ↔ ∃ r s : Nat, r < 4 ∧ s < κ ∧ (3 * κ * r + 4 * s) % (4 * κ) = 1) := by
  have hp := frame_isPrime F
  have h2 := F.two_lt_p
  have hn := F.n_eq
  have hq := F.quarter_turn_sq
  have hi0 : Frame.quarterTurn g κ ≠ 0 := Prime.ne_zero_of_mul_self (Prime.neg_one_ne_zero hp) hq
  have h4κ : 0 < 4 * κ := Nat.mul_pos (by decide) F.cap_pos
  -- injectivity on an odd capacity
  have inj : κ % 2 = 1 → ∀ r s r' s' : Nat, r < 4 → s < κ → r' < 4 → s' < κ →
      Frame.quarterTurn g κ ^ r * (g ^ 4) ^ s = Frame.quarterTurn g κ ^ r' * (g ^ 4) ^ s' → r = r' ∧ s = s' := by
    intro hk r s r' s' hr hs hr' hs' e
    have kill : ∀ t : Nat, ((g ^ 4) ^ t) ^ κ = 1 := fun t => by
      rw [← pow_mul, ← pow_mul, show 4 * (t * κ) = 4 * κ * t by rw [Nat.mul_comm t κ, FRC.Nat.mul_assoc],
        pow_mul, ← hn, F.pow_n, one_pow]
    have ej : (Frame.quarterTurn g κ ^ κ) ^ r = (Frame.quarterTurn g κ ^ κ) ^ r' := by
      have this : (Frame.quarterTurn g κ ^ r * (g ^ 4) ^ s) ^ κ = (Frame.quarterTurn g κ ^ r' * (g ^ 4) ^ s') ^ κ := by
        rw [e]
      rw [mul_pow, mul_pow, kill, kill, mul_one, mul_one, pow_mul_comm, pow_mul_comm (Frame.quarterTurn g κ) r'] at this
      exact this
    have hjj : Frame.quarterTurn g κ ^ κ * Frame.quarterTurn g κ ^ κ = -1 := by
      rw [← pow_add, ← Nat.two_mul, pow_mul, pow_two, hq, neg_one_pow, ite_eq_right (by rw [hk]; decide)]
    have hrr := quarter_pow_inj hp h2 hjj hr hr' ej
    subst hrr
    have e2 := Prime.mul_left_cancel hp (pow_ne_zero hp hi0 r) e
    rw [← pow_mul, ← pow_mul] at e2
    have h4s : ∀ t, t < κ → 4 * t < p - 1 := fun t ht => by
      rw [hn, Nat.mul_comm 4 t, Nat.mul_comm 4 κ]; exact FRC.Nat.mul_lt_mul_of_lt_of_pos ht (by decide : 0 < 4)
    exact ⟨rfl, Nat.eq_of_mul_eq_mul_left (by decide : 0 < 4) (F.pow_inj (h4s s hs) (h4s s' hs') e2)⟩
  have notinj : κ % 2 = 0 → ¬ ∀ r s r' s' : Nat, r < 4 → s < κ → r' < 4 → s' < κ →
      Frame.quarterTurn g κ ^ r * (g ^ 4) ^ s = Frame.quarterTurn g κ ^ r' * (g ^ 4) ^ s' → r = r' ∧ s = s' := by
    intro he hall
    obtain ⟨m, hm⟩ := FRC.Nat.mod_spec 2 (by decide) κ
    rw [he, Nat.add_zero] at hm
    have hm0 : 0 < m := by
      match m, hm with
      | 0, hm => have := F.cap_pos; rw [hm] at this; exact absurd this (Nat.lt_irrefl 0)
      | k + 1, _ => exact Nat.zero_lt_succ k
    have hmκ : m < κ := by rw [hm, Nat.two_mul]; exact Nat.lt_add_of_pos_right hm0
    have h4m : 4 * m = 2 * κ := by rw [hm, ← FRC.Nat.mul_assoc]
    have e : Frame.quarterTurn g κ ^ 2 * (g ^ 4) ^ 0 = Frame.quarterTurn g κ ^ 0 * (g ^ 4) ^ m := by
      rw [pow_two, hq, pow_zero, mul_one, pow_zero, one_mul, ← pow_mul, h4m, F.half_period]
    exact absurd (hall 2 0 0 m (by decide) F.cap_pos (by decide) hmκ e).1 (by decide)
  have hp' : p = p - 1 + 1 := (FRC.Nat.sub_add_cancel Pos.pos).symm
  have surj : κ % 2 = 1 → ∀ x : Shell p, x ≠ 0 →
      ∃ r s : Nat, r < 4 ∧ s < κ ∧ Frame.quarterTurn g κ ^ r * (g ^ 4) ^ s = x := by
    intro hk x hx
    have hy : ∀ n, Frame.quarterTurn g κ ^ (qr4 n).2 * (g ^ 4) ^ (qr4 n).1 ≠ 0 := fun n =>
      Prime.mul_ne_zero hp (pow_ne_zero hp hi0 _) (pow_ne_zero hp (pow_ne_zero hp F.g_ne_zero 4) _)
    have hq4 : ∀ n, n < p - 1 → (qr4 n).1 < κ := fun n hn' => by
      have h1 : 4 * (qr4 n).1 ≤ n :=
        calc 4 * (qr4 n).1 ≤ 4 * (qr4 n).1 + (qr4 n).2 := Nat.le_add_right _ _
          _ = n := (qr4_spec n).1.symm
      rw [hn] at hn'
      match Nat.lt_or_ge (qr4 n).1 κ with
      | .inl h => exact h
      | .inr h => exact absurd (Nat.lt_of_le_of_lt (Nat.le_trans (Nat.mul_le_mul_left 4 h) h1) hn') (Nat.lt_irrefl _)
    have hinj : ∀ i j, i < p - 1 → j < p - 1 →
        (fun n => (Frame.quarterTurn g κ ^ (qr4 n).2 * (g ^ 4) ^ (qr4 n).1).val) i =
        (fun n => (Frame.quarterTurn g κ ^ (qr4 n).2 * (g ^ 4) ^ (qr4 n).1).val) j → i = j := fun i j hi hj e => by
      obtain ⟨er, es⟩ := inj hk _ _ _ _ (qr4_spec i).2 (hq4 i hi) (qr4_spec j).2 (hq4 j hj) (ext e)
      calc i = 4 * (qr4 i).1 + (qr4 i).2 := (qr4_spec i).1
        _ = 4 * (qr4 j).1 + (qr4 j).2 := by rw [er, es]
        _ = j := (qr4_spec j).1.symm
    have hb : ∀ e, Pigeonhole.mem e (imageList (fun n => (Frame.quarterTurn g κ ^ (qr4 n).2 * (g ^ 4) ^ (qr4 n).1).val) (p - 1)) →
        1 ≤ e ∧ e ≤ p - 1 := fun e he =>
      match mem_imageList he with
      | ⟨n, _, hσ⟩ => ⟨by rw [← hσ]; exact Prime.val_pos (hy n),
          by rw [← hσ]; exact Nat.le_of_lt_succ (Nat.lt_of_lt_of_le (Shell.lt _) (Nat.le_of_eq hp'))⟩
    obtain ⟨n, hn', hσ⟩ := mem_imageList (Pigeonhole.mem_of_nodup_of_length (p - 1) _ (imageList_nodup hinj (Nat.le_refl _))
      hb (imageList_length _ _) x.val (Prime.val_pos hx) (Nat.le_of_lt_succ (Nat.lt_of_lt_of_le x.lt (Nat.le_of_eq hp'))))
    exact ⟨(qr4 n).2, (qr4 n).1, (qr4_spec n).2, hq4 n hn', ext hσ⟩
  have solv1 : κ % 2 = 1 → ∃ r s : Nat, r < 4 ∧ s < κ ∧ (3 * κ * r + 4 * s) % (4 * κ) = 1 := fun hk => by
    obtain ⟨r, s, hr, hs, e⟩ := surj hk g F.g_ne_zero
    rw [fold_eq F] at e
    refine ⟨r, s, hr, hs, ?_⟩
    have e2 : g ^ ((3 * κ * r + 4 * s) % (p - 1)) = g ^ 1 := by rw [← F.pow_mod, pow_one]; exact e
    have h1 : 1 < p - 1 := by
      rw [hn]; exact Nat.lt_of_lt_of_le (by decide : 1 < 4 * 1) (Nat.mul_le_mul_left 4 F.cap_pos)
    rw [← hn]; exact F.pow_inj (Nat.mod_lt _ F.n_pos) h1 e2
  have solv2 : (∃ r s : Nat, r < 4 ∧ s < κ ∧ (3 * κ * r + 4 * s) % (4 * κ) = 1) → κ % 2 = 1 := fun ⟨r, s, _, _, e⟩ => by
    match Frame.mod_two_cases κ with
    | .inr h => exact h
    | .inl h =>
      obtain ⟨m, hm⟩ := FRC.Nat.mod_spec 2 (by decide) κ
      rw [h, Nat.add_zero] at hm
      obtain ⟨t, ht⟩ := FRC.Nat.mod_spec (4 * κ) h4κ (3 * κ * r + 4 * s)
      rw [e] at ht
      have hl : 3 * κ * r + 4 * s = 2 * (3 * m * r + 2 * s) := by
        rw [hm, FRC.Nat.mul_left_comm 3 2 m, FRC.Nat.mul_assoc 2, show 4 * s = 2 * (2 * s) by rw [← FRC.Nat.mul_assoc],
          ← Nat.left_distrib]
      have hr' : 4 * κ * t + 1 = 2 * (2 * κ * t) + 1 := by rw [← FRC.Nat.mul_assoc, ← FRC.Nat.mul_assoc]
      have this : (2 * (3 * m * r + 2 * s)) % 2 = (2 * (2 * κ * t) + 1) % 2 := by rw [← hl, ht, hr']
      rw [Frame.two_mul_mod, FRC.Nat.add_mul_mod_self_left _ _ _ (by decide)] at this
      exact absurd this (by decide)
  have hv : κ % 2 = 1 ↔ (p - 1) % 8 ≠ 0 := by
    rw [hn]
    obtain ⟨q, hq'⟩ := FRC.Nat.mod_spec 2 (by decide) κ
    have e8 : 4 * κ = 8 * q + 4 * (κ % 2) :=
      calc 4 * κ = 4 * (2 * q + κ % 2) := by rw [← hq']
        _ = 8 * q + 4 * (κ % 2) := by rw [Nat.left_distrib, ← FRC.Nat.mul_assoc]
    rw [e8, FRC.Nat.add_mul_mod_self_left _ _ _ (by decide)]
    match Frame.mod_two_cases κ with
    | .inl h => rw [h]; exact ⟨fun e => absurd e (by decide), fun e => absurd rfl e⟩
    | .inr h => rw [h]; exact ⟨fun _ => by decide, fun _ => rfl⟩
  exact ⟨hv, ⟨inj, fun hall => match Frame.mod_two_cases κ with
    | .inr h => h
    | .inl h => absurd hall (notinj h)⟩, surj, ⟨solv1, solv2⟩⟩

/-- 00:C16, the converse — for `κ` even no isomorphism `C_{p−1} ≅ C₄ × C_κ` exists: a map `φ` from the nonzero residues
to the pairs `(r mod 4, s mod κ)` that turns products into sums is never injective, since `2κ` kills `C₄ × C_κ`
(`4 ∣ 2κ`) while `g^{2κ} = −1 ≠ 1`. -/
theorem no_iso {κ : Nat} {g : Shell p} (F : Frame p κ g) (hκ : κ % 2 = 0) (φ : Shell p → Nat × Nat)
    (hφ : ∀ x y : Shell p, x ≠ 0 → y ≠ 0 → φ (x * y) = (((φ x).1 + (φ y).1) % 4, ((φ x).2 + (φ y).2) % κ)) :
    ¬ ∀ x y : Shell p, x ≠ 0 → y ≠ 0 → φ x = φ y → x = y := fun hinj => by
  have hg0 : g ≠ 0 := by have := F.pow_ne_zero 1; rwa [pow_one] at this
  have hpow : ∀ n, φ (g ^ (n + 2)) = (((n + 2) * (φ g).1) % 4, ((n + 2) * (φ g).2) % κ) := fun n => by
    induction n with
    | zero => show φ (g ^ 1 * g) = (((0 + 2) * (φ g).1) % 4, ((0 + 2) * (φ g).2) % κ); rw [pow_one, hφ g g hg0 hg0, Nat.zero_add, Nat.two_mul, Nat.two_mul]
    | succ n ih =>
      show φ (g ^ (n + 2) * g) = (((n + 1 + 2) * (φ g).1) % 4, ((n + 1 + 2) * (φ g).2) % κ)
      rw [hφ _ g (F.pow_ne_zero _) hg0, ih, FRC.Nat.mod_add_mod _ _ _ (Nat.zero_lt_succ 3),
        FRC.Nat.mod_add_mod _ _ _ F.cap_pos, Nat.succ_mul (n + 2) (φ g).1, Nat.succ_mul (n + 2) (φ g).2]
  obtain ⟨t, ht⟩ := FRC.Nat.mod_spec 2 (Nat.zero_lt_succ 1) κ; rw [hκ, Nat.add_zero] at ht
  have c1 : ((2 * κ + 2) * (φ g).1) % 4 = ((0 + 2) * (φ g).1) % 4 := by
    rw [FRC.Nat.add_mul, ht, ← FRC.Nat.mul_assoc 2 2 t, FRC.Nat.mul_assoc (2 * 2) t, Nat.zero_add]
    exact FRC.Nat.add_mul_mod_self_left _ (t * (φ g).1) 4 (Nat.zero_lt_succ 3)
  have c2 : ((2 * κ + 2) * (φ g).2) % κ = ((0 + 2) * (φ g).2) % κ := by
    rw [FRC.Nat.add_mul, Nat.mul_comm 2 κ, FRC.Nat.mul_assoc κ 2, Nat.zero_add]
    exact FRC.Nat.add_mul_mod_self_left _ _ _ F.cap_pos
  have he : φ (g ^ (2 * κ + 2)) = φ (g ^ (0 + 2)) := by rw [hpow, hpow, c1, c2]
  have hg := hinj _ _ (F.pow_ne_zero _) (F.pow_ne_zero _) he; rw [pow_add, Nat.zero_add, F.half_period] at hg
  have hc : g ^ 2 * -1 = g ^ 2 * 1 := by rw [mul_comm, hg, mul_one]
  exact Prime.neg_one_ne_one F.two_lt_p (F.mul_left_cancel (F.pow_ne_zero 2) hc)

/-- `2^k ∣ 2^a u` with `u` odd forces `k ≤ a`. -/
theorem pow_dvd_odd {a k u : Nat} (hu : u % 2 = 1) : 2 ^ k ∣ 2 ^ a * u → k ≤ a
  | ⟨c, hc⟩ => by
    match Nat.lt_or_ge a k with
    | .inr h => exact h
    | .inl h =>
      obtain ⟨d, hd⟩ : ∃ d, k = a + 1 + d := ⟨k - (a + 1), (FRC.Nat.add_sub_of_le (Nat.succ_le_of_lt h)).symm⟩
      have e : 2 ^ a * u = 2 ^ a * (2 * (2 ^ d * c)) := by
        rw [hc, hd, FRC.Nat.pow_add, Nat.pow_succ, FRC.Nat.mul_assoc (2 ^ a) 2, FRC.Nat.mul_assoc (2 ^ a),
          FRC.Nat.mul_assoc 2]
      rw [Nat.eq_of_mul_eq_mul_left (FRC.Nat.pos_pow_of_pos a (by decide : 0 < 2)) e, Frame.two_mul_mod] at hu
      exact absurd hu (by decide)

/-- C16's 2-parts. With `p − 1 = 2^a u` and `Ω − 1 = 2^b w`, `u, w` odd, and `m = min(a, b)`: `2^m` divides both and
`2^{m+1}` not both (the shared 2-part `C_{2^m}`), and `2^m · 2^{b−m} = 2^b` (the shared order times the cover degree is
the Carrier's 2-part); for `Ω − 1 = 4S` the Carrier's 2-part is `8` iff `S ≡ 2 (mod 4)`. -/
theorem two_part :
    (∀ a b u w m : Nat, u % 2 = 1 → w % 2 = 1 → m ≤ a → m ≤ b → (m = a ∨ m = b) →
      2 ^ m ∣ 2 ^ a * u ∧ 2 ^ m ∣ 2 ^ b * w ∧ ¬ (2 ^ (m + 1) ∣ 2 ^ a * u ∧ 2 ^ (m + 1) ∣ 2 ^ b * w) ∧
      2 ^ m * 2 ^ (b - m) = 2 ^ b) ∧
    (∀ S b w : Nat, w % 2 = 1 → 4 * S = 2 ^ b * w → (2 ^ b = 8 ↔ S % 4 = 2)) := by
  have dv : ∀ m a u, m ≤ a → 2 ^ m ∣ 2 ^ a * u := fun m a u h =>
    ⟨2 ^ (a - m) * u, by rw [← FRC.Nat.mul_assoc, ← FRC.Nat.pow_add, FRC.Nat.add_sub_of_le h]⟩
  refine ⟨fun a b u w m hu hw ha hb hm => ⟨dv m a u ha, dv m b w hb, fun ⟨h1, h2⟩ => ?_,
    by rw [← FRC.Nat.pow_add, FRC.Nat.add_sub_of_le hb]⟩, fun S b w hw e => ⟨fun h8 => ?_, fun h2 => ?_⟩⟩
  · match hm with
    | .inl e => rw [e] at h1; exact Nat.not_succ_le_self a (pow_dvd_odd hu h1)
    | .inr e => rw [e] at h2; exact Nat.not_succ_le_self b (pow_dvd_odd hw h2)
  · rw [h8] at e
    have hS : S = 2 * w := Nat.eq_of_mul_eq_mul_left (by decide : 0 < 4) (by rw [e, ← FRC.Nat.mul_assoc])
    obtain ⟨t, ht⟩ := FRC.Nat.mod_spec 2 (by decide) w
    rw [hw] at ht
    rw [hS, ht, Nat.left_distrib, ← FRC.Nat.mul_assoc, FRC.Nat.add_mul_mod_self_left _ _ _ (by decide)]
  · obtain ⟨t, ht⟩ := FRC.Nat.mod_spec 4 (by decide) S
    rw [h2] at ht
    have e' : 2 ^ b * w = 2 ^ 3 * (2 * t + 1) := by
      rw [← e, ht]
      show 4 * (4 * t + 2) = 8 * (2 * t + 1)
      rw [Nat.left_distrib, Nat.left_distrib, ← FRC.Nat.mul_assoc, ← FRC.Nat.mul_assoc]
    have hodd : (2 * t + 1) % 2 = 1 := FRC.Nat.add_mul_mod_self_left 1 t 2 (by decide)
    have hb : b = 3 := Nat.le_antisymm (pow_dvd_odd hodd ⟨w, e'.symm⟩) (pow_dvd_odd hw ⟨2 * t + 1, e'⟩)
    rw [hb]

/-! ## C25: the horizon is the origin's antipode on the boost torus -/

section torus
variable {ν : Shell p}

/-- The boost carrying the origin `[0 : 1]` to the direction `[x : y]` (`q = x/y`): `u = yν + xw`. -/
def dir (ν : Shell p) (x y : Shell p) : Extension.Ext p ν := ⟨ν * y, x⟩

/-- The torsor map `u ↦ u/ū = u²/N(u)` onto the boost torus `C_{p+1} = {N = 1}`. -/
def ratio (u : Extension.Ext p ν) : Extension.Ext p ν := Extension.Ext.ofShell (inv u.norm) * (u * u)

theorem ext_mul4 (a b c d : Extension.Ext p ν) : a * b * (c * d) = a * c * (b * d) := by
  rw [Extension.Ext.mul_assoc, ← Extension.Ext.mul_assoc b, Extension.Ext.mul_comm b c, Extension.Ext.mul_assoc c,
    ← Extension.Ext.mul_assoc]

theorem ratio_ofShell (hp : FRC.Nat.isPrime p) {a : Shell p} (ha : a ≠ 0) :
    ratio (Extension.Ext.ofShell a : Extension.Ext p ν) = 1 := by
  rw [ratio, Extension.Ext.norm_ofShell, Extension.Ext.ofShell_mul, Extension.Ext.ofShell_mul, mul_comm,
    mul_inv hp (Prime.mul_ne_zero hp ha ha)]; rfl

theorem ratio_mul (u v : Extension.Ext p ν) : ratio (v * u) = ratio v * ratio u := by
  rw [ratio, ratio, ratio, Extension.Ext.norm_mul, inv, inv, inv, mul_pow, ← Extension.Ext.ofShell_mul,
    ext_mul4 v u v u, ext_mul4]

theorem ratio_scale (hp : FRC.Nat.isPrime p) {c : Shell p} (hc : c ≠ 0) (u : Extension.Ext p ν) :
    ratio (Extension.Ext.ofShell c * u) = ratio u := by
  rw [ratio_mul, ratio_ofShell hp hc, Extension.Ext.one_mul]

theorem norm_ratio (hp : FRC.Nat.isPrime p) {u : Extension.Ext p ν} (hu : u.norm ≠ 0) : (ratio u).norm = 1 := by
  rw [ratio, Extension.Ext.norm_scale, Extension.Ext.norm_mul, mul_mul_mul_comm, mul_comm (inv _), mul_inv hp hu, one_mul]

theorem nonsquare_ne_zero {ν : Shell p} (hν : ¬ ∃ y : Shell p, y * y = ν) : ν ≠ 0 :=
  fun e => hν ⟨0, by rw [e, mul_zero]⟩

/-- **C25 (p00139), the horizon is the origin's antipode on the boost torus.** On a prime `p = 4κ + 1` with `ν` a
nonsquare and `𝔽_{p²} = 𝔽_p[w]/(w² − ν)`: a direction `[x : y] ≠ 0` has the boost `u = yν + xw` of nonzero norm, and
`v = a + bw` moves it by `q ↦ (aq + νb)/(bq + a)`; the torsor map `u ↦ u/ū` lands on `C_{p+1}`, is constant on the
classes `𝔽_p^× u` and equivariant, and is a bijection from the directions onto `C_{p+1}`; it sends the origin `[0 : 1]`
to `1` and the horizon `[1 : 0]` to `−1`, the one element of order two, and `𝔽_p^× ∩ C_{p+1} = {±1}`; the one boost
of order two is the class of `w`, `q ↦ ν/q`, which swaps the origin and the horizon; and `2s = 0` forces `s = 0`, the
seam `2κ + (2κ + 1) = 0`: `2⁻¹ = 2κ + 1 = −2κ`. -/
theorem horizon_antipode (hp : FRC.Nat.isPrime p) {κ : Nat} (hκ : p = 4 * κ + 1) (hν : ¬ ∃ y : Shell p, y * y = ν) :
    (∀ x y : Shell p, (x ≠ 0 ∨ y ≠ 0) → (dir ν x y).norm ≠ 0) ∧
    (∀ (v : Extension.Ext p ν) (x y : Shell p), v * dir ν x y = dir ν (v.re * x + ν * (v.im * y)) (v.re * y + v.im * x)) ∧
    (∀ u : Extension.Ext p ν, u.norm ≠ 0 → (ratio u).norm = 1) ∧
    (∀ (c : Shell p) (u : Extension.Ext p ν), c ≠ 0 → ratio (Extension.Ext.ofShell c * u) = ratio u) ∧
    (∀ u v : Extension.Ext p ν, ratio (v * u) = ratio v * ratio u) ∧
    (∀ x y x' y' : Shell p, (x ≠ 0 ∨ y ≠ 0) → (x' ≠ 0 ∨ y' ≠ 0) →
      (ratio (dir ν x y) = ratio (dir ν x' y') ↔ x * y' = x' * y)) ∧
    (∀ z : Extension.Ext p ν, z.norm = 1 → ∃ x y : Shell p, (x ≠ 0 ∨ y ≠ 0) ∧ ratio (dir ν x y) = z) ∧
    ratio (dir ν 0 1) = 1 ∧ ratio (dir ν 1 0) = -1 ∧
    (∀ z : Extension.Ext p ν, z.norm = 1 → z * z = 1 → z = 1 ∨ z = -1) ∧
    (∀ z : Extension.Ext p ν, z.im = 0 → (z.norm = 1 ↔ z = 1 ∨ z = -1)) ∧
    (∀ v : Extension.Ext p ν, (v * v).im = 0 → v.im ≠ 0 → v.re = 0) ∧
    (∀ x y : Shell p, Extension.Ext.w * dir ν x y = dir ν (ν * y) x) ∧
    (∀ s : Shell p, 2 * s = 0 → s = 0) ∧ (2 : Shell p) * ofNat (2 * κ + 1) = 1 ∧
      ofNat (2 * κ) + ofNat (2 * κ + 1) = (0 : Shell p) := by
  have hν0 := nonsquare_ne_zero hν
  have h2 : (2 : Shell p) ≠ 0 := fun e => by
    have := Prime.two_mul_chart_half hκ; rw [e, zero_mul] at this; exact Prime.one_ne_zero hp this.symm
  have hsq1 : ∀ c : Shell p, c * c = 1 ↔ c = 1 ∨ c = -1 := fun c =>
    ⟨Prime.sq_eq_one hp, fun h => match h with
      | .inl e => by rw [e, mul_one]
      | .inr e => by rw [e, neg_mul_neg, mul_one]⟩
  -- the norm of a direction's boost, `ν (ν y² − x²)`
  have hnd : ∀ x y : Shell p, (dir ν x y).norm = ν * (ν * (y * y) + -(x * x)) := fun x y =>
    Shell.Frame.RE.sound (Shell.Frame.look [ν, x, y])
      (.add (.mul (.mul (.var 0) (.var 2)) (.mul (.var 0) (.var 2))) (.neg (.mul (.var 0) (.mul (.var 1) (.var 1)))))
      (.mul (.var 0) (.add (.mul (.var 0) (.mul (.var 2) (.var 2))) (.neg (.mul (.var 1) (.var 1))))) (by decide +kernel)
  have hne : ∀ x y : Shell p, (x ≠ 0 ∨ y ≠ 0) → (dir ν x y).norm ≠ 0 := fun x y hxy h0 => by
    rw [hnd] at h0
    have e := Prime.eq_of_sub_eq_zero ((Prime.mul_eq_zero hp h0).resolve_left hν0)
    match Shell.instDecidableEq y 0 with
    | .isFalse hy =>
      exact hν ⟨x * inv y, by rw [mul_mul_mul_comm, ← e, mul_assoc, ← mul_mul_mul_comm, mul_inv hp hy, mul_one, mul_one]⟩
    | .isTrue hy =>
      rw [hy, mul_zero, mul_zero] at e
      have hx : x = 0 := match Prime.mul_eq_zero hp e.symm with | .inl a => a | .inr a => a
      exact match hxy with | .inl a => a hx | .inr a => a hy
  have hact : ∀ (v : Extension.Ext p ν) (x y : Shell p),
      v * dir ν x y = dir ν (v.re * x + ν * (v.im * y)) (v.re * y + v.im * x) := fun v x y =>
    Extension.Ext.ext
      (Shell.Frame.RE.sound (Shell.Frame.look [ν, v.re, v.im, x, y])
        (.add (.mul (.var 1) (.mul (.var 0) (.var 4))) (.mul (.var 0) (.mul (.var 2) (.var 3))))
        (.mul (.var 0) (.add (.mul (.var 1) (.var 4)) (.mul (.var 2) (.var 3)))) (by decide +kernel))
      (Shell.Frame.RE.sound (Shell.Frame.look [ν, v.re, v.im, x, y])
        (.add (.mul (.var 1) (.var 3)) (.mul (.var 2) (.mul (.var 0) (.var 4))))
        (.add (.mul (.var 1) (.var 3)) (.mul (.var 0) (.mul (.var 2) (.var 4)))) (by decide +kernel))
  -- the horizon's boost is `w`, of norm `−ν`
  have hw : dir ν 1 0 = Extension.Ext.w := Extension.Ext.ext (mul_zero ν) rfl
  have hm1 : ratio (dir ν 1 0) = -1 := by
    rw [hw, ratio, Extension.Ext.w_sq, Extension.Ext.ofShell_mul]
    have hn : (Extension.Ext.w : Extension.Ext p ν).norm = -ν := by
      show 0 * 0 + -(ν * (1 * 1)) = -ν; rw [zero_mul, zero_add, mul_one, mul_one]
    rw [hn]
    have hn0 : -ν ≠ 0 := fun h => hν0 (by rw [← neg_neg ν, h, neg_zero])
    have e : inv (-ν) * ν = -1 :=
      calc inv (-ν) * ν = -(inv (-ν) * -ν) := by rw [← mul_neg, neg_neg]
        _ = -1 := by rw [mul_comm, mul_inv hp hn0]
    rw [e]; exact Extension.Ext.ext rfl (neg_zero).symm
  -- `a² + νb² = a² − νb²` forces `b = 0`
  have hb0 : ∀ a b : Shell p, a * a + ν * (b * b) = a * a + -(ν * (b * b)) → b = 0 := fun a b e => by
    have key : a * a + ν * (b * b) + -(a * a + -(ν * (b * b))) = (1 + 1) * (ν * (b * b)) :=
      Shell.Frame.RE.sound (Shell.Frame.look [ν, a, b])
        (.add (.add (.mul (.var 1) (.var 1)) (.mul (.var 0) (.mul (.var 2) (.var 2)))) (.neg (.add (.mul (.var 1) (.var 1)) (.neg (.mul (.var 0) (.mul (.var 2) (.var 2)))))))
        (.mul (.add .one .one) (.mul (.var 0) (.mul (.var 2) (.var 2)))) (by decide +kernel)
    rw [e, add_neg] at key
    have e3 := (Prime.mul_eq_zero hp key.symm).resolve_left (by rw [← Prime.two_eq]; exact h2)
    have e4 := (Prime.mul_eq_zero hp e3).resolve_left hν0
    exact match Prime.mul_eq_zero hp e4 with | .inl a => a | .inr a => a
  -- a norm-one element of order two is `±1`
  have hord2 : ∀ z : Extension.Ext p ν, z.norm = 1 → z * z = 1 → z = 1 ∨ z = -1 := fun z hz hzz => by
    have hre : z.re * z.re + ν * (z.im * z.im) = 1 := Extension.Ext.re_congr hzz
    have hb := hb0 z.re z.im (hre.trans hz.symm)
    have ha : z.re * z.re = 1 := by rw [hb, mul_zero, mul_zero, add_zero] at hre; exact hre
    exact match (hsq1 z.re).1 ha with
      | .inl a => .inl (Extension.Ext.ext a hb)
      | .inr a => .inr (Extension.Ext.ext a (by rw [hb]; exact (neg_zero).symm))
  -- the torsor map is injective on directions
  have hinj : ∀ x y x' y' : Shell p, (x ≠ 0 ∨ y ≠ 0) → (x' ≠ 0 ∨ y' ≠ 0) →
      (ratio (dir ν x y) = ratio (dir ν x' y') ↔ x * y' = x' * y) := fun x y x' y' hxy hxy' => by
    constructor
    · intro e
      have hu' := hne x' y' hxy'
      have hnc : (Extension.Ext.conj (dir ν x' y')).norm = (dir ν x' y').norm := by
        show (ν * y') * (ν * y') + -(ν * (-x' * -x')) = (ν * y') * (ν * y') + -(ν * (x' * x')); rw [neg_mul_neg]
      have hc : ratio (Extension.Ext.conj (dir ν x' y')) * ratio (dir ν x' y') = 1 := by
        rw [← ratio_mul, Extension.Ext.mul_comm, Extension.Ext.mul_conj]; exact ratio_ofShell hp hu'
      have ht : ratio (dir ν x y * Extension.Ext.conj (dir ν x' y')) = 1 := by
        rw [ratio_mul, e, Extension.Ext.mul_comm]; exact hc
      have hnt : (dir ν x y * Extension.Ext.conj (dir ν x' y')).norm ≠ 0 := by
        rw [Extension.Ext.norm_mul, hnc]; exact Prime.mul_ne_zero hp (hne x y hxy) hu'
      generalize hT : dir ν x y * Extension.Ext.conj (dir ν x' y') = T at ht hnt
      have h1 : inv T.norm * (T * T).re = 1 := by
        have := Extension.Ext.re_congr ht; rw [ratio, Extension.Ext.ofShell_mul_eq] at this; exact this
      have h2' : (T * T).re = T.norm := by
        rw [← one_mul (T * T).re, ← mul_inv hp hnt, mul_assoc, h1, mul_one]
      have hTi : T.im = 0 := hb0 T.re T.im h2'
      have hTi' : T.im = ν * (x * y' + -(x' * y)) := by
        rw [← hT]
        exact Shell.Frame.RE.sound (Shell.Frame.look [ν, x, y, x', y'])
          (.add (.mul (.mul (.var 0) (.var 2)) (.neg (.var 3))) (.mul (.var 1) (.mul (.var 0) (.var 4))))
          (.mul (.var 0) (.add (.mul (.var 1) (.var 4)) (.neg (.mul (.var 3) (.var 2))))) (by decide +kernel)
      rw [hTi'] at hTi
      exact Prime.eq_of_sub_eq_zero ((Prime.mul_eq_zero hp hTi).resolve_left hν0)
    · intro e
      match Shell.instDecidableEq y 0 with
      | .isFalse hy =>
        have hy' : y' ≠ 0 := fun h0 => by
          rw [h0, mul_zero] at e
          exact match hxy' with
            | .inl a => a ((Prime.mul_eq_zero hp e.symm).resolve_right hy)
            | .inr a => a h0
        have hd : dir ν x' y' = Extension.Ext.ofShell (y' * inv y) * dir ν x y := by
          rw [Extension.Ext.ofShell_mul_eq]
          refine Extension.Ext.ext ?_ ?_
          · show ν * y' = y' * inv y * (ν * y)
            rw [mul_assoc, mul_left_comm (inv y), mul_comm (inv y), mul_inv hp hy, mul_one, mul_comm]
          · show x' = y' * inv y * x
            calc x' = x' * (y * inv y) := by rw [mul_inv hp hy, mul_one]
              _ = x * y' * inv y := by rw [e, mul_assoc]
              _ = y' * inv y * x := by rw [mul_comm x y', mul_assoc, mul_comm x (inv y), ← mul_assoc]
        rw [hd, ratio_scale hp (Prime.mul_ne_zero hp hy' (inv_ne_zero hp hy))]
      | .isTrue hy =>
        subst hy
        have hx : x ≠ 0 := match hxy with | .inl a => a | .inr a => absurd rfl a
        have hy' : y' = 0 := by
          rw [mul_zero] at e; exact (Prime.mul_eq_zero hp e).resolve_left hx
        subst hy'
        have hx' : x' ≠ 0 := match hxy' with | .inl a => a | .inr a => absurd rfl a
        have hd : dir ν x' 0 = Extension.Ext.ofShell (x' * inv x) * dir ν x 0 := by
          rw [Extension.Ext.ofShell_mul_eq]
          refine Extension.Ext.ext ?_ ?_
          · show ν * 0 = x' * inv x * (ν * 0); rw [mul_zero, mul_zero]
          · show x' = x' * inv x * x; rw [mul_assoc, mul_comm (inv x), mul_inv hp hx, mul_one]
        rw [hd, ratio_scale hp (Prime.mul_ne_zero hp hx' (inv_ne_zero hp hx))]
  -- and onto `C_{p+1}` (Hilbert 90: `z = (1 + z)/(1 + z̄)` for `z ≠ −1`)
  have hsurj : ∀ z : Extension.Ext p ν, z.norm = 1 → ∃ x y : Shell p, (x ≠ 0 ∨ y ≠ 0) ∧ ratio (dir ν x y) = z :=
    fun z hz => by
    have hzn : z.re * z.re + -(ν * (z.im * z.im)) = 1 := hz
    match Shell.instDecidableEq (1 + z.re) 0 with
    | .isTrue h1 =>
      refine ⟨1, 0, .inl (Prime.one_ne_zero hp), ?_⟩
      have hre : z.re = -1 := (neg_eq_of_add_eq_zero h1).symm
      rw [hre, neg_mul_neg, mul_one] at hzn
      have h0 : -(ν * (z.im * z.im)) = 0 :=
        add_right_cancel (by rw [add_comm, hzn, zero_add] : -(ν * (z.im * z.im)) + 1 = 0 + 1)
      have hn0 : ν * (z.im * z.im) = 0 := by rw [← neg_neg (ν * (z.im * z.im)), h0, neg_zero]
      have him : z.im = 0 :=
        match Prime.mul_eq_zero hp ((Prime.mul_eq_zero hp hn0).resolve_left hν0) with | .inl a => a | .inr a => a
      rw [hm1]
      exact Extension.Ext.ext hre.symm (by show -(0 : Shell p) = z.im; rw [him, neg_zero])
    | .isFalse h1 =>
      refine ⟨ν * z.im, 1 + z.re, .inr h1, ?_⟩
      have hd : dir ν (ν * z.im) (1 + z.re) = Extension.Ext.ofShell ν * (⟨1 + z.re, z.im⟩ : Extension.Ext p ν) := by
        rw [Extension.Ext.ofShell_mul_eq]; rfl
      rw [hd, ratio_scale hp hν0]
      have hbb : ν * (z.im * z.im) = z.re * z.re + -1 := by
        have e : ν * (z.im * z.im) = z.re * z.re + -(z.re * z.re + -(ν * (z.im * z.im))) :=
          Shell.Frame.RE.sound (Shell.Frame.look [z.re, ν * (z.im * z.im)]) (.var 1)
            (.add (.mul (.var 0) (.var 0)) (.neg (.add (.mul (.var 0) (.var 0)) (.neg (.var 1))))) (by decide +kernel)
        rw [e, hzn]
      have hM : (⟨1 + z.re, z.im⟩ : Extension.Ext p ν).norm = (1 + 1) * (1 + z.re) := by
        show (1 + z.re) * (1 + z.re) + -(ν * (z.im * z.im)) = (1 + 1) * (1 + z.re)
        rw [hbb]
        exact Shell.Frame.RE.sound (Shell.Frame.look [z.re])
          (.add (.mul (.add .one (.var 0)) (.add .one (.var 0))) (.neg (.add (.mul (.var 0) (.var 0)) (.neg .one))))
          (.mul (.add .one .one) (.add .one (.var 0))) (by decide +kernel)
      have hsq : (⟨1 + z.re, z.im⟩ : Extension.Ext p ν) * ⟨1 + z.re, z.im⟩ =
          Extension.Ext.ofShell ((1 + 1) * (1 + z.re)) * z := by
        rw [Extension.Ext.ofShell_mul_eq]
        refine Extension.Ext.ext ?_ ?_
        · show (1 + z.re) * (1 + z.re) + ν * (z.im * z.im) = (1 + 1) * (1 + z.re) * z.re
          rw [hbb]
          exact Shell.Frame.RE.sound (Shell.Frame.look [z.re])
            (.add (.mul (.add .one (.var 0)) (.add .one (.var 0))) (.add (.mul (.var 0) (.var 0)) (.neg .one)))
            (.mul (.mul (.add .one .one) (.add .one (.var 0))) (.var 0)) (by decide +kernel)
        · exact Shell.Frame.RE.sound (Shell.Frame.look [z.re, z.im])
            (.add (.mul (.add .one (.var 0)) (.var 1)) (.mul (.var 1) (.add .one (.var 0))))
            (.mul (.mul (.add .one .one) (.add .one (.var 0))) (.var 1)) (by decide +kernel)
      have hM0 : (1 + 1) * (1 + z.re) ≠ 0 := Prime.mul_ne_zero hp (by rw [← Prime.two_eq]; exact h2) h1
      rw [ratio, hM, hsq, ← Extension.Ext.mul_assoc, Extension.Ext.ofShell_mul, mul_comm, mul_inv hp hM0]
      exact Extension.Ext.one_mul z
  have h01 : ratio (dir ν 0 1) = 1 := by
    have : dir ν 0 1 = Extension.Ext.ofShell (ν * 1) := rfl
    rw [this]; exact ratio_ofShell hp (by rw [mul_one]; exact hν0)
  have hinv : ∀ v : Extension.Ext p ν, (v * v).im = 0 → v.im ≠ 0 → v.re = 0 := fun v e hv => by
    have key : (v * v).im = (1 + 1) * (v.re * v.im) :=
      Shell.Frame.RE.sound (Shell.Frame.look [v.re, v.im])
        (.add (.mul (.var 0) (.var 1)) (.mul (.var 1) (.var 0))) (.mul (.add .one .one) (.mul (.var 0) (.var 1)))
        (by decide +kernel)
    rw [key] at e
    exact (Prime.mul_eq_zero hp ((Prime.mul_eq_zero hp e).resolve_left (by rw [← Prime.two_eq]; exact h2))).resolve_right hv
  have hwact : ∀ x y : Shell p, Extension.Ext.w * dir ν x y = dir ν (ν * y) x := fun x y => by
    rw [hact]
    show dir ν (0 * x + ν * (1 * y)) (0 * y + 1 * x) = dir ν (ν * y) x
    rw [zero_mul, zero_add, one_mul, zero_mul, zero_add, one_mul]
  have hrat : ∀ z : Extension.Ext p ν, z.im = 0 → (z.norm = 1 ↔ z = 1 ∨ z = -1) := fun z hz => by
    have hn : z.norm = z.re * z.re := by
      show z.re * z.re + -(ν * (z.im * z.im)) = z.re * z.re
      rw [hz, zero_mul, mul_zero, neg_zero, add_zero]
    rw [hn]
    constructor
    · intro h
      match (hsq1 z.re).1 h with
      | .inl e => exact .inl (Extension.Ext.ext e hz)
      | .inr e => exact .inr (Extension.Ext.ext e (by show z.im = -(0 : Shell p); rw [hz, neg_zero]))
    · intro h
      match h with
      | .inl e => rw [e]; exact mul_one (1 : Shell p)
      | .inr e => rw [e]; show (-1 : Shell p) * -1 = 1; rw [neg_mul_neg, mul_one]
  have hseam : (ofNat (2 * κ) : Shell p) + ofNat (2 * κ + 1) = 0 := by
    rw [show (ofNat (2 * κ) + ofNat (2 * κ + 1) : Shell p) = ofNat (2 * κ + (2 * κ + 1)) from
      ext (FRC.Nat.add_mod _ _ _ Pos.pos).symm, show 2 * κ + (2 * κ + 1) = p by
      rw [hκ, ← Nat.add_assoc, ← Nat.two_mul, ← FRC.Nat.mul_assoc]]
    exact Prime.ofNat_self
  exact ⟨hne, hact, fun u hu => norm_ratio hp hu, fun c u hc => ratio_scale hp hc u, fun u v => ratio_mul u v, hinj,
    hsurj, h01, hm1, hord2, hrat, hinv, hwact,
    fun s hs => (Prime.mul_eq_zero hp hs).resolve_left h2, Prime.two_mul_chart_half hκ, hseam⟩

/-- 00:C25 — the horizon is `ζ^{(p+1)/2}` for every generator `ζ` of the torus: a norm-one `ζ` of order exactly `p + 1`
has `ζ^{2κ+1} = −1`, the torus's one element of order two. -/
theorem horizon_generator (hp : FRC.Nat.isPrime p) {κ : Nat} (hκ : p = 4 * κ + 1) (hν : ¬ ∃ y : Shell p, y * y = ν)
    (ζ : Extension.Ext p ν) (hn : ζ.norm = 1) (hζ : ζ ^ (p + 1) = 1)
    (hmin : ∀ l, 0 < l → l < p + 1 → ζ ^ l ≠ 1) : ζ ^ (2 * κ + 1) = -1 := by
  have hh : (2 * κ + 1) + (2 * κ + 1) = p + 1 := by
    rw [hκ, show 4 * κ = 2 * κ + 2 * κ from FRC.Nat.add_mul 2 2 κ]; exact congrArg Nat.succ (Nat.succ_add _ _)
  have hsq : ζ ^ (2 * κ + 1) * ζ ^ (2 * κ + 1) = 1 := by rw [← Extension.Ext.pow_add, hh, hζ]
  have hnorm : (ζ ^ (2 * κ + 1)).norm = 1 := by rw [Extension.Ext.norm_pow, hn, one_pow]
  have hlt : 2 * κ + 1 < p + 1 := by rw [← hh]; exact Nat.lt_add_of_pos_right (Nat.zero_lt_succ _)
  match (horizon_antipode hp hκ hν).2.2.2.2.2.2.2.2.2.1 _ hnorm hsq with
  | .inl e => exact absurd e (hmin _ (Nat.zero_lt_succ _) hlt)
  | .inr e => exact e

/-- 00:C25 — `u_P` is the unique boost carrying the origin to `P`: a boost `v` with `v · dir(0, 1) = c · dir(x, y)` is
`(c/ν) · dir(x, y)`, so it is `dir(x, y)` up to a scalar, which acts trivially on `ℙ¹` and leaves the ratio unchanged. -/
theorem boost_unique (hp : FRC.Nat.isPrime p) (hν : ¬ ∃ y : Shell p, y * y = ν) (v : Extension.Ext p ν) (c x y : Shell p)
    (h : v * dir ν 0 1 = Extension.Ext.ofShell c * dir ν x y) :
    v = Extension.Ext.ofShell (c * inv ν) * dir ν x y := by
  have h0 : dir ν 0 1 = Extension.Ext.ofShell ν := Extension.Ext.ext (mul_one ν) rfl
  have hi : (Extension.Ext.ofShell (inv ν) : Extension.Ext p ν) * Extension.Ext.ofShell ν = 1 := by
    rw [Extension.Ext.ofShell_mul, mul_comm, mul_inv hp (nonsquare_ne_zero hν)]; rfl
  calc v = Extension.Ext.ofShell (inv ν) * Extension.Ext.ofShell ν * v := by rw [hi, Extension.Ext.one_mul]
    _ = Extension.Ext.ofShell (inv ν) * (v * dir ν 0 1) := by rw [h0, Extension.Ext.mul_assoc, Extension.Ext.mul_comm _ v]
    _ = Extension.Ext.ofShell (c * inv ν) * dir ν x y := by rw [h, ← Extension.Ext.mul_assoc, Extension.Ext.ofShell_mul, mul_comm (inv ν) c]

end torus

end FRC.Subject
