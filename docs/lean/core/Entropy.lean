import FrcCore.Frame
import FrcCore.Orbit
import FrcCore.Dimensions
import FrcCore.Instances

/-!
# 14-entropy — the import's congruences, the octant sector and the laboratory Carrier, no axioms

The finite content of *De Sitter Entropy Estimates over Finite Holographic Substrate* (tree
`14-entropy-20260722`) from first principles: the quarter identity `Ω = 4S + 1 ⇒ Ω ≡ 1 (mod 4)`,
`Ω − 1 = 4S` (A1); the triality centre `S ≡ 1 (mod 3) ⇒ 3 ∣ Ω + 1`, `3 ∤ Ω − 1` (A2); the octant sector
`8 ∣ 4S ⟺ 2 ∣ S`, with `S = 2m` the cycle `8m`, its quarter `2m` and its octant `m` (C6, X4, B2); the closure
budget `2x ≤ 2m ⟺ x ≤ m` (C5); on every frame `(τ; 0, 1, g)` of even capacity `κ = 2m` the octant character
`ζ = g^m` — `ζ⁴ = −1`, `ζ⁸ = 1`, its inverse `g^{7m}`, the Tsirelson square `(ζ + ζ⁻¹)² = 2`,
`(2(ζ + ζ⁻¹))² = 8`, hence `2` a square on every such shell; and the converses — an element with `ζ⁴ = −1`,
`ζ⁸ = 1` forces the capacity even, and a square root `r` of `2` gives one, `ζ = (r + i r)/2` with `ζ² = i` —
so that, on every frame at tier 0, the octant sector exists ⟺ the capacity is even ⟺ `2` is a square: the
octant and the c-square are one condition (C6, X4); the nesting bound `q² < p`, `p² < Ω ⇒ q⁴ < Ω` (B10);
primality by trial division up to the square root. Decided by the kernel: the octant on `𝔽₁₇` and its absence
on `𝔽₁₃` and `𝔽₂₉`, the characters `ζ₈` of the Carriers `233` and `2 408 561`; the laboratory Carrier —
`S = 602 140` even, `≡ 1 (mod 3)`, `4S + 1` prime (A2); the capacity axis `𝔽₅`, no shell at `κ = 2`, `𝔽₁₃` at
hydrogen, `12N + 1` prime at `N = 1, 3` and not at `N = 2` (C10, B10); the nesting `37 → 1373 → 2 408 561` and
the bound `N ≤ 3` on the laboratory Carrier (B10). The realisation premises of the octant lemma (A4, A5, B6,
B7) are outside this module: it decides the lemma's arithmetic. Every declaration is checked to depend on no
axiom (`check_core_axioms.py`).
-/

namespace FRC.Entropy

open FRC.Shell

/-! ## The import and its congruences (14:A1, A2) -/
section congruences

/-- 14:A1, 14:B9 — the quarter identity: `Ω = 4S + 1` has `Ω ≡ 1 (mod 4)` and `Ω − 1 = 4S`, so the import fixes the
cardinality exactly; the finite face of B9's area law `A = 4S`. -/
theorem quarter_identity (S : Nat) : (4 * S + 1) % 4 = 1 ∧ 4 * S + 1 - 1 = 4 * S :=
  ⟨FRC.Nat.add_mul_mod_self_left 1 S 4 (Nat.zero_lt_succ 3), FRC.Nat.add_sub_cancel (4 * S) 1⟩

/-- 14:A2 — the triality centre: `S ≡ 1 (mod 3)` gives `(Ω + 1) % 3 = 0` and `(Ω − 1) % 3 = 1`, so the centre
`3 ∣ Ω + 1` is carried and `3 ∤ 4S`. -/
theorem triality_residues (S : Nat) (h : S % 3 = 1) : (4 * S + 2) % 3 = 0 ∧ (4 * S) % 3 = 1 := by
  have h3 : 0 < 3 := Nat.zero_lt_succ 2
  have h4S : (4 * S) % 3 = 1 := by
    rw [FRC.Nat.mul_mod 4 S 3 h3, h]
  refine ⟨?_, h4S⟩
  rw [FRC.Nat.add_mod (4 * S) 2 3 h3, h4S]

/-- 14:C6, 14:X4 — the octant sector `C₈ ⊂ C_{4S}` exists (`8 ∣ 4S`) exactly when `S` is even. -/
theorem octant_divides (S : Nat) : (∃ k, 4 * S = 8 * k) ↔ (∃ m, S = 2 * m) := by
  constructor
  · rintro ⟨k, hk⟩
    refine ⟨k, Nat.eq_of_mul_eq_mul_left (Nat.zero_lt_succ 3) ?_⟩
    rw [hk, ← FRC.Nat.mul_assoc]
  · rintro ⟨m, hm⟩
    exact ⟨m, by rw [hm, ← FRC.Nat.mul_assoc]⟩

/-- 14:B2, 14:C5 — the dictionary on the count face: the full cycle is `4S` (`2π`); the half-cycle `2S` (`π`)
twice over is the cycle, and with `S = 2m` the octant `m = S/2` (`π/4`) eight times over is the cycle — an
integer count on every admissible Carrier. -/
theorem octant_count (S m : Nat) (h : S = 2 * m) : 2 * (2 * S) = 4 * S ∧ 8 * m = 4 * S :=
  ⟨by rw [← FRC.Nat.mul_assoc], by rw [h, ← FRC.Nat.mul_assoc]⟩

/-- 14:C5, 14:B6 — the closure count: given B6's accounting (a two-way registration of depth `x` costs `2x` of
the one-way budget `S = 2m`; the realisation, not formalised), the closable depths are exactly `x ≤ m`, and the
octant `x = m` closes the budget. -/
theorem closure_count (m x : Nat) : 2 * x ≤ 2 * m ↔ x ≤ m := by
  constructor
  · intro h
    match Nat.lt_or_ge m x with
    | .inr hle => exact hle
    | .inl hlt =>
      have : m * 2 < x * 2 := FRC.Nat.mul_lt_mul_of_lt_of_pos hlt (Nat.zero_lt_succ 1)
      rw [Nat.mul_comm m 2, Nat.mul_comm x 2] at this
      exact absurd (Nat.lt_of_lt_of_le this h) (Nat.lt_irrefl _)
  · intro h; exact Nat.mul_le_mul_left 2 h

end congruences

/-! ## The octant character on every framed shell of even capacity (14:C6, X4) -/
section octant

variable {p : Nat} [Pos p] {κ : Nat} {g : Shell p}

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

end octant

/-! ## The converse: `2` a square ⇒ even capacity, on every frame (14:X4) -/
section converse

variable {p : Nat} [Pos p] {κ : Nat} {g : Shell p}

/-- `a b (c d) = a c (b d)` on every shell. -/
theorem mul_mul_mul_comm (a b c d : Shell p) : a * b * (c * d) = a * c * (b * d) := by
  rw [Shell.mul_assoc, Shell.mul_left_comm b c d, ← Shell.mul_assoc]

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

end converse

/-! ## The nesting bound and trial division (14:B10) -/
section nesting

/-- 14:B10 — the nesting bound, the necessity direction: a shell `q` registered whole by a Subject `p` of the
Carrier `Ω` (`q² < p`, `p² < Ω`) has `q⁴ < Ω`; for `q = 12N + 1` this bounds the hydrogen count `N`; a Subject
between the two is exhibited on the laboratory Carrier (`lab_nesting`, `p = 1373`). -/
theorem nesting_bound (q p Ω : Nat) (hq : q * q < p) (hp : p * p < Ω) : q * q * (q * q) < Ω := by
  have hp0 : 0 < p := FRC.Nat.pos_of_lt hq
  have h1 : q * q * (q * q) < p * p := by
    match Nat.lt_or_ge 0 (q * q) with
    | .inl hpos =>
      have ha : q * q * (q * q) < p * (q * q) := FRC.Nat.mul_lt_mul_of_lt_of_pos hq hpos
      have hb : q * q * p < p * p := FRC.Nat.mul_lt_mul_of_lt_of_pos hq hp0
      rw [Nat.mul_comm (q * q) p] at hb
      exact Nat.lt_trans ha hb
    | .inr hz =>
      have h0 : q * q = 0 := Nat.le_antisymm hz (Nat.zero_le _)
      rw [h0]; exact Nat.mul_pos hp0 hp0
  exact Nat.lt_trans h1 hp

/-- Trial division up to `B` decides primality when `n < (B + 1)²`: a divisor `d ≥ 2` of `n` with
`d > B` has a cofactor `q = n/d` with `2 ≤ q ≤ B`, itself a divisor. -/
theorem isPrime_of_bounded (n B : Nat) (h2 : 2 ≤ n) (hB : n < (B + 1) * (B + 1))
    (hd : ∀ d, d < B + 1 → 2 ≤ d → n % d ≠ 0) : Dimensions.isPrime n := by
  refine ⟨h2, fun d hdn hd2 hmod => ?_⟩
  have hd0 : 0 < d := Nat.lt_of_lt_of_le (Nat.zero_lt_succ 1) hd2
  obtain ⟨q, hq⟩ := FRC.Nat.mod_spec d hd0 n
  rw [hmod, Nat.add_zero] at hq
  match Nat.lt_or_ge d (B + 1) with
  | .inl hlt => exact hd d hlt hd2 hmod
  | .inr hge =>
    -- the cofactor `q`: `n = d q`, `q ≥ 2` (else `n = 0` or `n = d`), and `q ≤ B` (else `d q ≥ (B+1)²`)
    have hq2 : 2 ≤ q := by
      match q with
      | 0 => rw [Nat.mul_zero] at hq; exact absurd (hq ▸ h2) (Nat.not_succ_le_zero 1)
      | 1 => rw [Nat.mul_one] at hq; exact absurd (hq ▸ hdn) (Nat.lt_irrefl d)
      | q + 2 => exact Nat.le_add_left 2 q
    have hqB : q < B + 1 := by
      match Nat.lt_or_ge q (B + 1) with
      | .inl h => exact h
      | .inr hqge =>
        have : (B + 1) * (B + 1) ≤ d * q := Nat.mul_le_mul hge hqge
        exact absurd (Nat.lt_of_lt_of_le hB this) (hq ▸ Nat.lt_irrefl n)
    have hq0 : 0 < q := Nat.lt_of_lt_of_le (Nat.zero_lt_succ 1) hq2
    have hmodq : n % q = 0 :=
      FRC.Nat.mod_unique hq0 (by rw [hq, Nat.mul_comm d q, Nat.add_zero])
    exact hd q hqB hq2 hmodq

end nesting

/-! ## The values decided by the kernel (14:A2, C6, C10, B10) -/
section values

/-- 14:C6, 14:X4 — the octant on `𝔽₁₇` (`κ = 4`, `g = 3`): `ζ = 3² = 9` has `9⁴ = −1`, `9⁸ = 1`,
`ζ⁻¹ = 2`, `(9 + 2)² = 2`, `(2 · 11)² = 8`; on `𝔽₁₃` (`κ = 3`) and `𝔽₂₉` (`κ = 7`) no residue has `x⁴ = −1`,
and `2` is not a square. -/
theorem octant17 :
    (9 : Shell 17) = 3 ^ 2 ∧ (9 : Shell 17) ^ 4 = -1 ∧ (9 : Shell 17) ^ 8 = 1 ∧ (9 : Shell 17) * 2 = 1 ∧
    ((9 : Shell 17) + 2) ^ 2 = 2 ∧ (2 * ((9 : Shell 17) + 2)) ^ 2 = 8 ∧
    (∀ x : Shell 13, x ^ 4 ≠ -1) ∧ (∀ x : Shell 13, x * x ≠ 2) ∧
    (∀ x : Shell 29, x ^ 4 ≠ -1) ∧ (∀ x : Shell 29, x * x ≠ 2) := by decide +kernel

/-- 14:C6 — an octant character of the Carrier `Ω = 233` (`S = 58` even), host-decided in the chart with drive
`3`: `ζ₈ = 3²⁹ = 221`, `ζ₈⁴ = −1`, `ζ₈⁸ = 1`, `ζ₈⁻¹ = 97`, `(ζ₈ + ζ₈⁻¹)² = 2`, `(2(ζ₈ + ζ₈⁻¹))² = 8`. -/
theorem octant233 :
    (221 : Shell 233) ^ 4 = -1 ∧ (221 : Shell 233) ^ 8 = 1 ∧ (221 : Shell 233) * 97 = 1 ∧
    ((221 : Shell 233) + 97) ^ 2 = 2 ∧ (2 * ((221 : Shell 233) + 97)) ^ 2 = 8 := by decide +kernel

/-- 14:A2, 14:C6 — the laboratory Carrier `Ω = 2 408 561`, host-decided values: `4S + 1 = Ω` with
`S = 602 140` even and `≡ 1 (mod 3)`, the octant sector realised — in the chart with drive `6`,
`ζ₈ = 6³⁰¹⁰⁷⁰ = 1 639 587`, `ζ₈⁴ = −1`, `ζ₈⁸ = 1`, `ζ₈⁻¹ = 1 111 186`, `(ζ₈ + ζ₈⁻¹)² = 2`,
`(2(ζ₈ + ζ₈⁻¹))² = 8`. -/
theorem lab_carrier :
    4 * 602140 + 1 = 2408561 ∧ 602140 % 2 = 0 ∧ 602140 % 3 = 1 ∧
    (1639587 : Shell 2408561) ^ 4 = -1 ∧ (1639587 : Shell 2408561) ^ 8 = 1 ∧
    (1639587 : Shell 2408561) * 1111186 = 1 ∧ ((1639587 : Shell 2408561) + 1111186) ^ 2 = 2 ∧
    (2 * ((1639587 : Shell 2408561) + 1111186)) ^ 2 = 8 := by decide +kernel

/-- 14:A2 — the laboratory Carrier is prime: `2 408 561 < 1553²`, and no `d ≤ 1552` divides it. -/
theorem carrierLab_prime : Dimensions.isPrime 2408561 :=
  isPrime_of_bounded 2408561 1552 (by decide) (by decide) (by decide +kernel)

/-- 14:C10, 14:B10 — the primality behind the capacity axis: `κ = 1` (the bare proton) is the shell `𝔽₅`, `κ = 2`
has no shell (`9` composite), `κ_H = 3` (hydrogen, `N = 1`) is `𝔽₁₃`; the `3N` shell at `N = 3` (`37`), none at
`N = 2` (`25`). -/
theorem capacity_axis :
    Dimensions.isPrime 5 ∧ ¬ Dimensions.isPrime 9 ∧ Dimensions.isPrime (12 * 1 + 1) ∧
    ¬ Dimensions.isPrime (12 * 2 + 1) ∧ Dimensions.isPrime (12 * 3 + 1) := by decide +kernel

/-- 14:B10 — the nesting on the laboratory Carrier: the capacity-`9` shell `q = 37` nests through the Subject
`p = 1373 = 4 · 343 + 1`, prime (`1373 < 38²`, no `d ≤ 37` divides it), `37² < 1373`, `1373² < Ω`; and the bound
`N ≤ 3`: `37⁴ < Ω < 49⁴`. -/
theorem lab_nesting :
    Dimensions.isPrime 1373 ∧ 1373 = 4 * 343 + 1 ∧ 37 * 37 < 1373 ∧ 1373 * 1373 < 2408561 ∧
    37 * 37 * (37 * 37) < 2408561 ∧ 2408561 < 49 * 49 * (49 * 49) :=
  ⟨isPrime_of_bounded 1373 37 (by decide) (by decide) (by decide +kernel), by decide, by decide,
    by decide, by decide, by decide⟩

end values

end FRC.Entropy
