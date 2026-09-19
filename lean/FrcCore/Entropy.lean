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
`(2(ζ + ζ⁻¹))² = 8`, hence `2` a square on every such shell — one direction of the octant's second face at
tier 0 (even capacity ⇒ `2` a square); the converse is `FrcLedger.Entropy.octant_second_face` on Mathlib, and
its instances on `𝔽₁₃`, `𝔽₂₉` are decided here (C6, X4); the nesting bound `q² < p`, `p² < Ω ⇒ q⁴ < Ω` (B10); primality by trial division up to the square
root. Decided by the kernel: the octant on `𝔽₁₇` and its absence on `𝔽₁₃` and `𝔽₂₉`, the characters `ζ₈` of
the Carriers `233` and `2 408 561`; the laboratory Carrier — `S = 602 140` even, `≡ 1 (mod 3)`, `4S + 1` prime
(A2); the capacity axis `𝔽₅`, no shell at `κ = 2`, `𝔽₁₃` at hydrogen, `12N + 1` prime at `N = 1, 3` and not at
`N = 2` (C10, B10); the nesting `37 → 1373 → 2 408 561` and the bound `N ≤ 3` on the laboratory Carrier (B10).
The realisation premises of the octant lemma (A4, A5, B6, B7) are outside this module: it decides the lemma's
arithmetic. Every declaration is checked to depend on no axiom (`check_core_axioms.py`).
-/

namespace FRC.Entropy

open FRC.Shell

/-! ## The import and its congruences (14:A1, A2) -/
section congruences

/-- 14:A1, 14:B9 — the quarter identity: `Ω = 4S + 1` has `Ω ≡ 1 (mod 4)` and `Ω − 1 = 4S`, so the import fixes the
quarter_identity exactly; the finite face of B9's area law `A = 4S`. -/
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
`FRC.Entropy.octant_second_face` on Mathlib). -/
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

/-- 14:X4 — one direction of the second face at tier 0: on every frame of even capacity `2` is a square,
`(ζ + ζ⁻¹)² = 2`; the converse (`2` a square ⇒ even capacity) is on Mathlib, its instances decided in
`octant17`. -/
theorem two_is_square (F : Frame p κ g) (m : Nat) (hm : κ = 2 * m) : ∃ r : Shell p, r * r = 2 :=
  ⟨g ^ m + g ^ (7 * m), by rw [← Shell.pow_two]; exact (tsirelson_square F m hm).2.1⟩

end octant

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
