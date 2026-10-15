import FrcCore.Frame
import FrcCore.Orbit
import FrcCore.Instances
import FrcCore.Keys.Frame
import FrcCore.Theme.Quantum

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
primality by trial division up to the square root; the additive window `|Σhᵢ| ≤ Σκᵢ`, attained, every total
occurring (B11), the lock of like units with recurrence `12` and its offset (B12), the shells of capacity `3N` and
the multiplicative fusion of coprime cycles (B13). Decided by the kernel: the octant on `𝔽₁₇` and its absence
on `𝔽₁₃` and `𝔽₂₉`, the characters `ζ₈` of the Carriers `233` and `2 408 561`; the laboratory Carrier —
`S = 602 140` even, `≡ 1 (mod 3)`, `4S + 1` prime (A2); the capacity axis `𝔽₅`, no shell at `κ = 2`, `𝔽₁₃` at
hydrogen, `12N + 1` prime at `N = 1, 3` and not at `N = 2` (C10, B10); the nesting `37 → 1373 → 2 408 561` and
the bound `N ≤ 3` on the laboratory Carrier (B10). The realisation premises of the octant lemma (A4, A5, B6,
B7) are outside this module: it decides the lemma's arithmetic. Every declaration is checked to depend on no
axiom (`check_core_axioms.py`).

Since the ledger migration (task LM17) the octant character and its converse live in the frame theme (`Orbit.lean`)
and `isPrime` in `Nat.lean`; since task LM22 `isPrime_of_bounded` lives in `Nat.lean` too. Every old name stays as
an alias.
-/

namespace FRC.Entropy

open FRC.Shell

section
open FRC.Shell.Frame (lit_mul add_one_add_one_neg even_capacity_powers octant_residue tsirelson_square two_is_square lit_add neg_one_ne_one neg_one_ne_zero octant_of_two_square even_of_order_eight even_capacity_of_octant octant_iff even_capacity_of_two_square two_is_square_iff)

/-! ## The import and its congruences (14:A1, A2) -/
section congruences

/-- 14:A1, 14:B9, 14:C2 — the quarter identity: `Ω = 4S + 1` has `Ω ≡ 1 (mod 4)` and `Ω − 1 = 4S`, so the import fixes the
cardinality exactly; the finite face of B9's area law `A = 4S`, and the integer face of C2's horizon-quarter closure
`(Ω − 1)/4 = S`. -/
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
`d > B` has a cofactor `q = n/d` with `2 ≤ q ≤ B`, itself a divisor. Since task LM22 the base theme's
`FRC.Nat.isPrime_of_bounded`, under its old name. -/
theorem isPrime_of_bounded (n B : Nat) (h2 : 2 ≤ n) (hB : n < (B + 1) * (B + 1))
    (hd : ∀ d, d < B + 1 → 2 ≤ d → n % d ≠ 0) : FRC.Nat.isPrime n :=
  FRC.Nat.isPrime_of_bounded n B h2 hB hd

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
theorem carrierLab_prime : FRC.Nat.isPrime 2408561 :=
  isPrime_of_bounded 2408561 1552 (by decide) (by decide) (by decide +kernel)

/-- 14:C10, 14:B10 — the primality behind the capacity axis: `κ = 1` (the bare proton) is the shell `𝔽₅`, `κ = 2`
has no shell (`9` composite), `κ_H = 3` (hydrogen, `N = 1`) is `𝔽₁₃`; the `3N` shell at `N = 3` (`37`), none at
`N = 2` (`25`). -/
theorem capacity_axis :
    FRC.Nat.isPrime 5 ∧ ¬ FRC.Nat.isPrime 9 ∧ FRC.Nat.isPrime (12 * 1 + 1) ∧
    ¬ FRC.Nat.isPrime (12 * 2 + 1) ∧ FRC.Nat.isPrime (12 * 3 + 1) := by decide +kernel

/-- 14:B10 — the nesting on the laboratory Carrier: the capacity-`9` shell `q = 37` nests through the Subject
`p = 1373 = 4 · 343 + 1`, prime (`1373 < 38²`, no `d ≤ 37` divides it), `37² < 1373`, `1373² < Ω`; and the bound
`N ≤ 3`: `37⁴ < Ω < 49⁴`. -/
theorem lab_nesting :
    FRC.Nat.isPrime 1373 ∧ 1373 = 4 * 343 + 1 ∧ 37 * 37 < 1373 ∧ 1373 * 1373 < 2408561 ∧
    37 * 37 * (37 * 37) < 2408561 ∧ 2408561 < 49 * 49 * (49 * 49) :=
  ⟨isPrime_of_bounded 1373 37 (by decide) (by decide) (by decide +kernel), by decide, by decide,
    by decide, by decide, by decide⟩

end values

/-! ## Old names (ledger migration, task LM17): the declarations moved to the themes, each under its old name -/
end

section aliases
variable {p : Nat} [Pos p] {κ : Nat} {g : Shell p}

/-- `a b (c d) = a c (b d)` on every shell. -/
theorem mul_mul_mul_comm (a b c d : Shell p) : a * b * (c * d) = a * c * (b * d) :=
  FRC.Shell.mul_mul_mul_comm a b c d

/-- Literals multiply as their values: `a · b = ab` on every shell. -/
theorem lit_mul (a b : Nat) : (OfNat.ofNat a : Shell p) * OfNat.ofNat b = (OfNat.ofNat (a * b) : Shell p) :=
  FRC.Shell.Frame.lit_mul a b

/-- `a + 1 + (1 − a) = 2` on every shell. -/
theorem add_one_add_one_neg (a : Shell p) : a + 1 + (1 + -a) = 2 :=
  FRC.Shell.Frame.add_one_add_one_neg a

/-- On a frame of capacity `κ = 2m`: `g^{4m} = −1` (the half-period) and `g^{8m} = 1`. -/
theorem even_capacity_powers (F : Frame p κ g) (m : Nat) (hm : κ = 2 * m) :
    g ^ (4 * m) = -1 ∧ g ^ (8 * m) = 1 :=
  FRC.Shell.Frame.even_capacity_powers F m hm

/-- 14:C6 — the octant character: on every frame `(τ; 0, 1, g)` of even capacity `κ = 2m`, `ζ = g^m` has
`ζ⁴ = −1` and `ζ⁸ = 1` — the sector `C₈ ⊂ C_{4κ}` is realised and `ζ` is its residue `ζ₈`. -/
theorem octant_residue (F : Frame p κ g) (m : Nat) (hm : κ = 2 * m) :
    (g ^ m) ^ 4 = -1 ∧ (g ^ m) ^ 8 = 1 :=
  FRC.Shell.Frame.octant_residue F m hm

/-- 14:C6, 14:X4 — the Tsirelson square: with `ζ = g^m` and `ζ' = g^{7m}` its inverse (`ζζ' = 1`),
`(ζ + ζ')² = 2` and `(2(ζ + ζ'))² = 8` on every frame of capacity `κ = 2m`; hence `2` is a square on every
such shell — the direction "octant ⇒ c-square" of X4's second face (the converse is
`even_capacity_of_two_square` below; the equivalence `two_is_square_iff`). -/
theorem tsirelson_square (F : Frame p κ g) (m : Nat) (hm : κ = 2 * m) :
    g ^ m * g ^ (7 * m) = 1 ∧ (g ^ m + g ^ (7 * m)) ^ 2 = 2 ∧
    (2 * (g ^ m + g ^ (7 * m))) ^ 2 = 8 :=
  FRC.Shell.Frame.tsirelson_square F m hm

/-- 14:X4 — the direction "even capacity ⇒ `2` a square" at tier 0: on every frame of even capacity `2` is a
square, `(ζ + ζ⁻¹)² = 2`; the converse is `even_capacity_of_two_square`, the equivalence `two_is_square_iff`. -/
theorem two_is_square (F : Frame p κ g) (m : Nat) (hm : κ = 2 * m) : ∃ r : Shell p, r * r = 2 :=
  FRC.Shell.Frame.two_is_square F m hm

/-- Literals add as their values: `a + b = (a + b)` on every shell. -/
theorem lit_add (a b : Nat) : (OfNat.ofNat a : Shell p) + OfNat.ofNat b = (OfNat.ofNat (a + b) : Shell p) :=
  FRC.Shell.Frame.lit_add a b

/-- `−1 ≠ 1` on every frame (`2 ≠ 0`). -/
theorem neg_one_ne_one (F : Frame p κ g) : (-1 : Shell p) ≠ 1 :=
  FRC.Shell.Frame.neg_one_ne_one F

/-- `−1 ≠ 0` on every frame. -/
theorem neg_one_ne_zero (F : Frame p κ g) : (-1 : Shell p) ≠ 0 :=
  FRC.Shell.Frame.neg_one_ne_zero F

/-- A square root of `2` gives a square root of the quarter-turn: with `i² = −1`, `2h = 1` and `r² = 2`,
`ζ = (r + i r) h` has `ζ² = i`, hence `ζ⁴ = −1` and `ζ⁸ = 1` — an element of order eight wherever `−1 ≠ 1`,
that is on every frame. -/
theorem octant_of_two_square {r i h : Shell p} (hr : r * r = 2) (hi : i * i = -1)
    (hh : 2 * h = 1) :
    ∃ ζ : Shell p, ζ * ζ = i ∧ ζ ^ 4 = -1 ∧ ζ ^ 8 = 1 :=
  FRC.Shell.Frame.octant_of_two_square hr hi hh

/-- The arithmetic of the order: `(k · 8) % 4κ = 0` and `(k · 4) % 4κ ≠ 0` force `κ` even (a divisor `4κ` of
`8k` that misses `4k` cannot be `4 · odd`; `0 < κ` is only what `mod_spec` needs). -/
theorem even_of_order_eight {κ k : Nat} (hκ : 0 < κ) (h8 : (k * 8) % (4 * κ) = 0)
    (h4 : (k * 4) % (4 * κ) ≠ 0) : ∃ m, κ = 2 * m :=
  FRC.Shell.Frame.even_of_order_eight hκ h8 h4

/-- 14:C6 — the octant forces even capacity: on every frame, an element `ζ` with `ζ⁴ = −1` and `ζ⁸ = 1` (an
element of order eight) gives `8 ∣ 4κ`, so the capacity is even. -/
theorem even_capacity_of_octant (F : Frame p κ g) {ζ : Shell p} (hz4 : ζ ^ 4 = -1) (hz8 : ζ ^ 8 = 1) :
    ∃ m, κ = 2 * m :=
  FRC.Shell.Frame.even_capacity_of_octant F hz4 hz8

/-- 14:C6 — the octant sector at tier 0, as an equivalence: on every frame, an element with `ζ⁴ = −1` and
`ζ⁸ = 1` exists exactly when the capacity is even. -/
theorem octant_iff (F : Frame p κ g) : (∃ ζ : Shell p, ζ ^ 4 = -1 ∧ ζ ^ 8 = 1) ↔ ∃ m, κ = 2 * m :=
  FRC.Shell.Frame.octant_iff F

/-- 14:X4 — the converse of the second face at tier 0: on every frame, a square root of `2` forces the
capacity even — `ζ = (r + i r)/2` has `ζ² = i`, so an element of order eight exists and `8 ∣ 4κ`. -/
theorem even_capacity_of_two_square (F : Frame p κ g) {r : Shell p} (hr : r * r = 2) :
    ∃ m, κ = 2 * m :=
  FRC.Shell.Frame.even_capacity_of_two_square F hr

/-- 14:X4 — the second face as an equivalence at tier 0: on every frame `(τ; 0, 1, g)`, `2` is a square
exactly when the capacity is even — the c-square congruence and the octant sector are one condition. -/
theorem two_is_square_iff (F : Frame p κ g) : (∃ r : Shell p, r * r = 2) ↔ ∃ m, κ = 2 * m :=
  FRC.Shell.Frame.two_is_square_iff F

end aliases

/-! ## 14:B11–B13 — the additive window, the lock of like units, the shells of capacity `3N` (master F7, returned
15 October 2026). Heights `hᵢ` with `|hᵢ| ≤ κᵢ` are read as `uᵢ = hᵢ + κᵢ ≤ 2κᵢ`, so that the window `|Σhᵢ| ≤ Σκᵢ` is
`Σuᵢ ≤ 2Σκᵢ` and "every total occurs" is "every `s ≤ 2Σκᵢ` is a sum": the statements stay in `Nat`, with no axiom. -/

section window

/-- The total of the modes `u 0, …, u (m − 1)` (as the quantum theme's `prodN`, for sums). -/
def sumN (u : Nat → Nat) : Nat → Nat
  | 0 => 0
  | m + 1 => sumN u m + u m

theorem sumN_congr (u v : Nat → Nat) : ∀ m, (∀ j, j < m → u j = v j) → sumN u m = sumN v m
  | 0, _ => rfl
  | m + 1, h => by
    show sumN u m + u m = sumN v m + v m
    rw [sumN_congr u v m (fun j hj => h j (Nat.lt_succ_of_lt hj)), h m (Nat.lt_succ_self m)]

theorem sumN_mul (c : Nat) (κ : Nat → Nat) : ∀ m, sumN (fun j => c * κ j) m = c * sumN κ m
  | 0 => (Nat.mul_zero c).symm
  | m + 1 => by
    show sumN (fun j => c * κ j) m + c * κ m = c * (sumN κ m + κ m)
    rw [sumN_mul c κ m, Nat.mul_add]

/-- 14:B11 — the additive window, the bound: `m` modes at heights `uᵢ ≤ 2κᵢ` total at most `2Σκᵢ`
(`|Σhᵢ| ≤ Σκᵢ` for `hᵢ = uᵢ − κᵢ`). -/
theorem additive_window_bound (u κ : Nat → Nat) : ∀ m, (∀ j, j < m → u j ≤ 2 * κ j) → sumN u m ≤ 2 * sumN κ m
  | 0, _ => Nat.le_refl 0
  | m + 1, h => by
    show sumN u m + u m ≤ 2 * (sumN κ m + κ m)
    rw [Nat.mul_add]
    exact Nat.add_le_add (additive_window_bound u κ m (fun j hj => h j (Nat.lt_succ_of_lt hj))) (h m (Nat.lt_succ_self m))

/-- 14:B11 — the window is attained: the heights `uᵢ = 2κᵢ` (`hᵢ = κᵢ`) total `2Σκᵢ`. -/
theorem additive_window_attained (κ : Nat → Nat) (m : Nat) : sumN (fun j => 2 * κ j) m = 2 * sumN κ m :=
  sumN_mul 2 κ m

/-- 14:B11 — every total occurs: for every `s ≤ 2Σκᵢ` there are heights `uᵢ ≤ 2κᵢ` with `Σuᵢ = s` — the last
height `s` itself when `s ≤ 2κ_m`, else `2κ_m` with the rest by induction. -/
theorem additive_window_every (κ : Nat → Nat) :
    ∀ m s, s ≤ 2 * sumN κ m → ∃ u : Nat → Nat, (∀ j, j < m → u j ≤ 2 * κ j) ∧ sumN u m = s
  | 0, s, hs => ⟨fun _ => 0, fun j hj => absurd hj (Nat.not_lt_zero j), (Nat.eq_zero_of_le_zero hs).symm⟩
  | m + 1, s, hs => by
    have hs' : s ≤ 2 * sumN κ m + 2 * κ m := by
      have e : 2 * sumN κ (m + 1) = 2 * sumN κ m + 2 * κ m := Nat.mul_add 2 (sumN κ m) (κ m)
      exact e ▸ hs
    match Nat.lt_or_ge (2 * κ m) s with
    | .inr hle =>
      obtain ⟨u', hu', hsum'⟩ := additive_window_every κ m 0 (Nat.zero_le _)
      refine ⟨fun j => if j = m then s else u' j, ?_, ?_⟩
      · intro j hj
        match Nat.decEq j m with
        | isTrue e => show (if j = m then s else u' j) ≤ 2 * κ j; rw [if_pos e, e]; exact hle
        | isFalse ne =>
          show (if j = m then s else u' j) ≤ 2 * κ j
          rw [if_neg ne]; exact hu' j (Nat.lt_of_le_of_ne (Nat.le_of_lt_succ hj) ne)
      · show sumN (fun j => if j = m then s else u' j) m + (if m = m then s else u' m) = s
        rw [if_pos rfl, sumN_congr (fun j => if j = m then s else u' j) u' m (fun j hj => if_neg (Nat.ne_of_lt hj)),
          hsum']
        exact Nat.zero_add s
    | .inl hlt =>
      obtain ⟨s', hs'eq⟩ := Nat.le.dest (Nat.le_of_lt hlt)
      have hs'le : s' ≤ 2 * sumN κ m := by
        apply FRC.Nat.le_of_add_le_add_left (a := 2 * κ m)
        rw [hs'eq]
        exact Nat.le_trans hs' (Nat.le_of_eq (Nat.add_comm _ _))
      obtain ⟨u', hu', hsum'⟩ := additive_window_every κ m s' hs'le
      refine ⟨fun j => if j = m then 2 * κ m else u' j, ?_, ?_⟩
      · intro j hj
        match Nat.decEq j m with
        | isTrue e => show (if j = m then 2 * κ m else u' j) ≤ 2 * κ j; rw [if_pos e, e]; exact Nat.le_refl _
        | isFalse ne =>
          show (if j = m then 2 * κ m else u' j) ≤ 2 * κ j
          rw [if_neg ne]; exact hu' j (Nat.lt_of_le_of_ne (Nat.le_of_lt_succ hj) ne)
      · show sumN (fun j => if j = m then 2 * κ m else u' j) m + (if m = m then 2 * κ m else u' m) = s
        rw [if_pos rfl, sumN_congr (fun j => if j = m then 2 * κ m else u' j) u' m (fun j hj => if_neg (Nat.ne_of_lt hj)),
          hsum', Nat.add_comm]
        exact hs'eq

/-- 14:B11 — the additive window as one statement: the bound, its attainment and every total in the range
(heights read as `uᵢ = hᵢ + κᵢ ≤ 2κᵢ`). -/
theorem additive_window :
    (∀ (u κ : Nat → Nat) (m : Nat), (∀ j, j < m → u j ≤ 2 * κ j) → sumN u m ≤ 2 * sumN κ m) ∧
    (∀ (κ : Nat → Nat) (m : Nat), sumN (fun j => 2 * κ j) m = 2 * sumN κ m) ∧
    (∀ (κ : Nat → Nat) (m s : Nat), s ≤ 2 * sumN κ m →
      ∃ u : Nat → Nat, (∀ j, j < m → u j ≤ 2 * κ j) ∧ sumN u m = s) :=
  ⟨additive_window_bound, additive_window_attained, additive_window_every⟩

/-- 14:B11 — hydrogen units: `N` modes of capacity `3` have the window `3N` (`2 · 3N` in the shifted reading);
on the hydrogen shell `𝔽₁₃` two heights `≤ 3` sum to at most `6 = 2κ` (38:A8), and three can exceed it,
`3 + 3 + 3 = 9 > 6` — the window grows with `N`. -/
theorem additive_window_hydrogen :
    (∀ N : Nat, sumN (fun _ => 2 * 3) N = 2 * (3 * N)) ∧
    (∀ u, u < 7 → ∀ v, v < 7 → u + v ≤ 12) ∧ 6 + 6 + 6 > 12 := by
  refine ⟨fun N => ?_, by decide, by decide⟩
  have e := sumN_mul 2 (fun _ => 3) N
  rw [e]
  have h3 : ∀ n, sumN (fun _ => 3) n = 3 * n := fun n => by
    induction n with
    | zero => rfl
    | succ k ih => show sumN (fun _ => 3) k + 3 = 3 * (k + 1); rw [ih, Nat.mul_succ]
  rw [h3]

end window

section lock

/-- 14:B12 — the lock of like units: `m ≥ 1` cycles of period `12` return jointly exactly at the multiples of
`12` (the quantum theme's `Joint`), so the joint recurrence is `12` for every `m` and no element has order `12m`
for `m ≥ 2`. -/
theorem lock_recurrence (m : Nat) (hm : 0 < m) (t : Nat) :
    FRC.Quantum.Joint (fun _ => 12) m t ↔ t % 12 = 0 :=
  ⟨fun h => h 0 hm, fun h _ _ => h⟩

/-- 14:B12 — the instances on the lock `C₁₂ × C₁₂`: the diagonal drive `(x, y) ↦ (x + 1, y + 1)` returns every
point after `12` steps, `x + 12 = x`, and not before, `x + k ≠ x` for `0 < k < 12`; it keeps the offset,
`(x + 1) − (y + 1) = x − y` (one superselected `C₁₂` offset per further unit); so the `144` points fall into `12`
orbits of length `12`, and the `1728` points of `C₁₂³` into `144`. -/
theorem lock_orbits :
    (∀ x : Shell 12, x + 12 = x) ∧
    (∀ x : Shell 12, ∀ k, k < 12 → 0 < k → x + FRC.Shell.ofNat k ≠ x) ∧
    (∀ x : Shell 12, ∀ y : Shell 12, (x + 1) + -(y + 1) = x + -y) ∧ 144 = 12 * 12 ∧ 1728 = 144 * 12 := by
  refine ⟨by decide +kernel, by decide +kernel, by decide +kernel, by decide, by decide⟩

end lock

section shells

/-- 14:B13 — the shell of capacity `3N` is `𝔽_{12N+1}`, `4 · 3N + 1 = 12N + 1`; below `N = 10` it exists exactly for
`N = 1, 3, 5, 6, 8, 9` (`12N + 1` prime), and not at `N = 2` (`25 = 5²`), `4`, `7`. -/
theorem shells_of_capacity :
    (∀ N : Nat, 4 * (3 * N) + 1 = 12 * N + 1) ∧
    (∀ N : Nat, N < 10 → (FRC.Nat.isPrime (12 * N + 1) ↔ N = 1 ∨ N = 3 ∨ N = 5 ∨ N = 6 ∨ N = 8 ∨ N = 9)) ∧
    25 = 5 * 5 := by
  refine ⟨fun N => ?_, ?_, by decide⟩
  · rw [← FRC.Nat.mul_assoc]
  · intro N hN
    match N, hN with
    | 0, _ => decide +kernel
    | 1, _ => decide +kernel
    | 2, _ => decide +kernel
    | 3, _ => decide +kernel
    | 4, _ => decide +kernel
    | 5, _ => decide +kernel
    | 6, _ => decide +kernel
    | 7, _ => decide +kernel
    | 8, _ => decide +kernel
    | 9, _ => decide +kernel
    | n + 10, h => exact absurd (Nat.lt_of_lt_of_le h (Nat.le_add_left 10 n)) (Nat.lt_irrefl _)

/-- 14:B13 — fusion of coprime cycles is multiplicative, the instances: hydrogen `(4, 3)` returns jointly exactly
at the multiples of `12 = 4 · 3` (searched below `24`), the diagonal drive on `C₄ × C₃` is one orbit of length `12`
(the twelve points `(k, k)`, `k < 12`, distinct), and the fused capacity is `4 · 3 / 4 = 3`; like cycles do not
fuse — `(12, 12)` returns at the multiples of `12`, `gcd (12, 12) = 12` — and the capacity-`3` shell `13` is not
the lock's register `12`. The general law, `lcm (n₁, n₂) = n₁ n₂` for coprime cycles, is the Mathlib declaration. -/
theorem fusion_capacity :
    (∀ t, t < 24 → (FRC.Quantum.Joint (fun j => if j = 0 then 4 else 3) 2 t ↔ t % 12 = 0)) ∧
    (∀ k, k < 12 → ∀ k', k' < 12 →
      (FRC.Shell.ofNat k : Shell 4) = FRC.Shell.ofNat k' → (FRC.Shell.ofNat k : Shell 3) = FRC.Shell.ofNat k' → k = k') ∧
    4 * 3 / 4 = 3 ∧ Nat.lcm 4 3 = 12 ∧
    (∀ t, t < 24 → (FRC.Quantum.Joint (fun _ => 12) 2 t ↔ t % 12 = 0)) ∧ Nat.gcd 12 12 = 12 ∧ (13 : Nat) ≠ 12 :=
  ⟨by decide +kernel, by decide +kernel, by decide, by decide, by decide +kernel, by decide, by decide⟩

end shells

/-! ## The concordance in integers (14:C4) -/
section concordance

/-- 14:C4 [approx] — the concordance as integer arithmetic: the five evidence readings of `r_H` (rows 1, 2a, 2b, 3,
4b of the instrument table) are `166, 127, 133, 119, 164` in units of `10²⁴ m`, the gauge reading 4a (`129`) displayed
and excluded; the count face `√S = √π · r_H/ℓ_P` is monotone in `r_H`, so rows 1 and 3 are the extremes. Clauses:
the five lie in `[119, 166]`; the half-range `(166 − 119)/(166 + 119)` lies in `(16 %, 17 %)`, the paper's `±17 %`;
the full-range factor on `S`, `(166/119)²`, lies in `(1.9, 2.0)`, the paper's `1.9`; with `ℓ_P = 1.616255 × 10⁻³⁵ m`
the two extremes of `r_H/ℓ_P` lie in `(7.36, 7.37) × 10⁶⁰` and `(10.27, 10.28) × 10⁶⁰`; with `√π ∈ (1.772, 1.773)`
(`1772² < 3 141 592 < 3 141 593 < 1773²`) the count face lies in `(1.30, 1.31) × 10⁶¹` and `(1.80, 1.83) × 10⁶¹`,
the paper's `√S = (1.3–1.8) × 10⁶¹`. The readings, `ℓ_P` and `π` are chart data (taken as given); the arithmetic is
decided. -/
theorem concordance :
    (119 ≤ 127 ∧ 127 ≤ 166 ∧ 119 ≤ 133 ∧ 133 ≤ 166 ∧ 119 ≤ 164 ∧ 164 ≤ 166) ∧
    (16 * (166 + 119) < 100 * (166 - 119) ∧ 100 * (166 - 119) < 17 * (166 + 119)) ∧
    (19 * (119 * 119) < 10 * (166 * 166) ∧ 10 * (166 * 166) < 20 * (119 * 119)) ∧
    (736 * 1616255 < 1190 * 1000000 ∧ 1190 * 1000000 < 737 * 1616255 ∧
      1027 * 1616255 < 1660 * 1000000 ∧ 1660 * 1000000 < 1028 * 1616255) ∧
    (1772 * 1772 < 3141592 ∧ 3141593 < 1773 * 1773) ∧
    (1300000 < 1772 * 736 ∧ 1773 * 737 < 1310000 ∧ 1800000 < 1772 * 1027 ∧ 1773 * 1028 < 1830000) := by
  decide

end concordance

-- Ledger predicates of 14-entropy (generated by make_predicates.py from docs/14-entropy/14-entropy-ledger.json; edit the ledger, not this section)
/-- 14:A1 (p14001) — The de Sitter entropy $\dS$, the single quantitative import, fixing the cardinality exactly, $\Om=4\dS+1$. -/
theorem p14001 : ∀ (S : Nat), ((4 : Nat) * S + (1 : Nat)) % (4 : Nat) = (1 : Nat) ∧ (4 : Nat) * S + (1 : Nat) - (1 : Nat) = (4 : Nat) * S :=
  @FRC.Entropy.quarter_identity
/-- 14:A2 (p14002) — The Carrier congruences, relations certified by the realisations (the $c$-square $\dS$ even, the triality centre $\dS\equiv1\pmod3$, completeness $4\dS+1$ prime); instantiated on the laboratory Carrier as host-decided values. -/
theorem p14002 : FRC.Nat.isPrime (2408561 : Nat) :=
  @FRC.Entropy.carrierLab_prime
/-- 14:B2 (p14010) — The angle--count dictionary: $2\pi$ the full cycle, $h=2\pi\hbar$; every angular numeral is the chart face of a count ($\pi/4\leftrightarrow\dS/2$ chronons). -/
theorem p14010 : ∀ (S m : Nat), S = (2 : Nat) * m → (2 : Nat) * ((2 : Nat) * S) = (4 : Nat) * S ∧ (8 : Nat) * m = (4 : Nat) * S :=
  @FRC.Entropy.octant_count
/-- 14:B9 (p14017) — The area law: the projected horizon area in Planck cells is the full phase cycle, $A=4\dS$ \apx{} at the horizon ($4\pi n_A=4\dS$, $n_A=(r_H/\lP)^{2}$ \apx); the Bekenstein--Hawking quarter $\dS=A/4$ is the quarter-turn $Q_4$, the generative four of $\Om=4\dS+1$ and $\p=4\kap+1$; area is a Subject-projection property, the Carrier carrying none. -/
theorem p14017 : ∀ (S : Nat), ((4 : Nat) * S + (1 : Nat)) % (4 : Nat) = (1 : Nat) ∧ (4 : Nat) * S + (1 : Nat) - (1 : Nat) = (4 : Nat) * S :=
  @FRC.Entropy.quarter_identity
/-- 14:B10 (p14044) — The capacity axis counts hydrogen units (one gram at $N_A$ to $0.003$ dex \apx): a definition, not a registered shell. The least register window resolving the total winding of $N$ units is $3N$, a theorem about the observing Subject (B11); a phase-locked composite of like units is an aggregate, never one shell (B12; a shell of capacity $3N$ exists only when $12N+1$ is prime, B13); the largest shell any Subject registers whole is the nesting bound $\mathsf{q}<\Om^{1/4}$ (00:B8), $N<(\Om^{1/4}-1)/12$ units, $8\times10^{2}$\,kg at $\dS=3.3\times10^{122}$ \apx{} ($\Om^{1/4}$ units overcounts by $12$); everything heavier an aggregate of locks; the proton's $1$ against $3$ compares a tower label with a chart count. -/
theorem p14044 : (∀ (q p Ω : Nat), q * q < p → p * p < Ω → q * q * (q * q) < Ω) ∧ FRC.Nat.isPrime (1373 : Nat) ∧ (1373 : Nat) = (4 : Nat) * (343 : Nat) + (1 : Nat) ∧ (37 : Nat) * (37 : Nat) < (1373 : Nat) ∧ (1373 : Nat) * (1373 : Nat) < (2408561 : Nat) ∧ (37 : Nat) * (37 : Nat) * ((37 : Nat) * (37 : Nat)) < (2408561 : Nat) ∧ (2408561 : Nat) < (49 : Nat) * (49 : Nat) * ((49 : Nat) * (49 : Nat)) :=
  And.intro @FRC.Entropy.nesting_bound (@FRC.Entropy.lab_nesting)
/-- 14:B11 (p14046) — The additive window: for $N$ modes at resolvable heights $|\hat h_i|\le\kap_i$ (38:A8) the total winding satisfies $|\sum_i\hat h_i|\le\sum_i\kap_i$, attained, every total in the range occurring; the least register window resolving the total exactly is the capacity sum $\sum_i\kap_i$, $3N$ for $N$ hydrogen units --- a capacity of the observing Subject, not a shell of the composite (B10). -/
theorem p14046 : ((∀ (u κ : Nat → Nat) (m : Nat), (∀ (j : Nat), j < m → u j ≤ (2 : Nat) * κ j) → FRC.Entropy.sumN u m ≤ (2 : Nat) * FRC.Entropy.sumN κ m) ∧ (∀ (κ : Nat → Nat) (m : Nat), FRC.Entropy.sumN (fun j => (2 : Nat) * κ j) m = (2 : Nat) * FRC.Entropy.sumN κ m) ∧ ∀ (κ : Nat → Nat) (m s : Nat), s ≤ (2 : Nat) * FRC.Entropy.sumN κ m → ∃ u, (∀ (j : Nat), j < m → u j ≤ (2 : Nat) * κ j) ∧ FRC.Entropy.sumN u m = s) ∧ (∀ (N : Nat), FRC.Entropy.sumN (fun x => (2 : Nat) * (3 : Nat)) N = (2 : Nat) * ((3 : Nat) * N)) ∧ (∀ (u : Nat), u < (7 : Nat) → ∀ (v : Nat), v < (7 : Nat) → u + v ≤ (12 : Nat)) ∧ (6 : Nat) + (6 : Nat) + (6 : Nat) > (12 : Nat) :=
  And.intro @FRC.Entropy.additive_window (@FRC.Entropy.additive_window_hydrogen)
/-- 14:B12 (p14047) — The lock of like units: $N$ like units never fuse (00:F6, $\gcd(12,12)=12$): their joint registration (00:F2) recurs on $C_{12}$ with period $12$ for every $N$, one superselected $C_{12}$ offset per further unit --- an aggregate, never one shell. Instances: the diagonal drive on $C_{12}^{2}$ has $12$ orbits of length $12$, on $C_{12}^{3}$ $144$. -/
theorem p14047 : (∀ (m : Nat), (0 : Nat) < m → ∀ (t : Nat), FRC.Quantum.Joint (fun x => (12 : Nat)) m t ↔ t % (12 : Nat) = (0 : Nat)) ∧ (∀ (x : FRC.Shell (12 : Nat)), x + (12 : FRC.Shell (12 : Nat)) = x) ∧ (∀ (x : FRC.Shell (12 : Nat)) (k : Nat), k < (12 : Nat) → (0 : Nat) < k → x + FRC.Shell.ofNat k ≠ x) ∧ (∀ (x y : FRC.Shell (12 : Nat)), x + (1 : FRC.Shell (12 : Nat)) + -(y + (1 : FRC.Shell (12 : Nat))) = x + -y) ∧ (144 : Nat) = (12 : Nat) * (12 : Nat) ∧ (1728 : Nat) = (144 : Nat) * (12 : Nat) :=
  And.intro @FRC.Entropy.lock_recurrence (@FRC.Entropy.lock_orbits)
set_option linter.defProp false in
/-- 14:B13 (p14048) — Shells of capacity $3N$ and fusion: the shell of capacity $3N$ is $\F_{12N+1}$ and exists iff $12N+1$ is prime ($N=1,3,5,6,8,9$ below $10$; none at $N=2$, $25=5^{2}$), never the lock's register (B12); fusion of coprime cycles is multiplicative, $\kap=n_{1}n_{2}/4$: hydrogen $(4,3)\to3$, one orbit of length $12$ (00:F6). -/
def p14048 := And.intro @FRC.Entropy.shells_of_capacity (@FRC.Entropy.fusion_capacity)
/-- 14:C2 (p14019) — The non-channels: the constants correspondence carries no dimensional readout, the horizon-quarter closure is an internal consistency loop, the registered entropy budget is a floor eighteen orders below $\dS$ \apx. -/
theorem p14019 : ∀ (S : Nat), ((4 : Nat) * S + (1 : Nat)) % (4 : Nat) = (1 : Nat) ∧ (4 : Nat) * S + (1 : Nat) - (1 : Nat) = (4 : Nat) * S :=
  @FRC.Entropy.quarter_identity
/-- 14:C4 (p14021) — The concordance: five evidence readings return $\sqrt{\dS}=(1.3\text{--}1.8)\times10^{61}$ \apx, $\pm17\%$ half-range on the count face, factor $1.9$ on $\dS$; the gauge reading 4a is displayed and excluded from every statistic. -/
theorem p14021 : ((119 : Nat) ≤ (127 : Nat) ∧ (127 : Nat) ≤ (166 : Nat) ∧ (119 : Nat) ≤ (133 : Nat) ∧ (133 : Nat) ≤ (166 : Nat) ∧ (119 : Nat) ≤ (164 : Nat) ∧ (164 : Nat) ≤ (166 : Nat)) ∧ ((16 : Nat) * ((166 : Nat) + (119 : Nat)) < (100 : Nat) * ((166 : Nat) - (119 : Nat)) ∧ (100 : Nat) * ((166 : Nat) - (119 : Nat)) < (17 : Nat) * ((166 : Nat) + (119 : Nat))) ∧ ((19 : Nat) * ((119 : Nat) * (119 : Nat)) < (10 : Nat) * ((166 : Nat) * (166 : Nat)) ∧ (10 : Nat) * ((166 : Nat) * (166 : Nat)) < (20 : Nat) * ((119 : Nat) * (119 : Nat))) ∧ ((736 : Nat) * (1616255 : Nat) < (1190 : Nat) * (1000000 : Nat) ∧ (1190 : Nat) * (1000000 : Nat) < (737 : Nat) * (1616255 : Nat) ∧ (1027 : Nat) * (1616255 : Nat) < (1660 : Nat) * (1000000 : Nat) ∧ (1660 : Nat) * (1000000 : Nat) < (1028 : Nat) * (1616255 : Nat)) ∧ ((1772 : Nat) * (1772 : Nat) < (3141592 : Nat) ∧ (3141593 : Nat) < (1773 : Nat) * (1773 : Nat)) ∧ (1300000 : Nat) < (1772 : Nat) * (736 : Nat) ∧ (1773 : Nat) * (737 : Nat) < (1310000 : Nat) ∧ (1800000 : Nat) < (1772 : Nat) * (1027 : Nat) ∧ (1773 : Nat) * (1028 : Nat) < (1830000 : Nat) :=
  @FRC.Entropy.concordance
/-- 14:C5 (p14022) — The octant lemma: the measured age is $\dS/2$ chronons, $(\pi/4)\,r_H/c$ in the chart \apx; the halving and the sector are exact through the enumerated realisation set $B_{\mathrm{oct}}=\{$A4, A5, B2, B3, B6, B7$\}$, the same class as the constants correspondence. -/
theorem p14022 : (∀ (m x : Nat), (2 : Nat) * x ≤ (2 : Nat) * m ↔ x ≤ m) ∧ ∀ (S m : Nat), S = (2 : Nat) * m → (2 : Nat) * ((2 : Nat) * S) = (4 : Nat) * S ∧ (8 : Nat) * m = (4 : Nat) * S :=
  And.intro @FRC.Entropy.closure_count (@FRC.Entropy.octant_count)
/-- 14:C6 (p14023) — The octant sector: $C_{8}\subset C_{4\dS}$ exists exactly when $\dS$ is even, its character $\zeta_8$ the residue the Tsirelson identity carries; the octant count $\dS/2$ is an integer on every admissible Carrier. -/
theorem p14023 : (∀ {p : Nat} [FRC.Pos p] {κ : Nat} {g : FRC.Shell p}, FRC.Shell.Frame p κ g → ∀ (m : Nat), κ = (2 : Nat) * m → g ^ m * g ^ ((7 : Nat) * m) = (1 : FRC.Shell p) ∧ (g ^ m + g ^ ((7 : Nat) * m)) ^ (2 : Nat) = (2 : FRC.Shell p) ∧ ((2 : FRC.Shell p) * (g ^ m + g ^ ((7 : Nat) * m))) ^ (2 : Nat) = (8 : FRC.Shell p)) ∧ (∀ {p : Nat} [FRC.Pos p] {κ : Nat} {g : FRC.Shell p}, FRC.Shell.Frame p κ g → ((∃ ζ, ζ ^ (4 : Nat) = (-1 : FRC.Shell p) ∧ ζ ^ (8 : Nat) = (1 : FRC.Shell p)) ↔ ∃ m, κ = (2 : Nat) * m)) ∧ (4 : Nat) * (602140 : Nat) + (1 : Nat) = (2408561 : Nat) ∧ (602140 : Nat) % (2 : Nat) = (0 : Nat) ∧ (602140 : Nat) % (3 : Nat) = (1 : Nat) ∧ (1639587 : FRC.Shell (2408561 : Nat)) ^ (4 : Nat) = (-1 : FRC.Shell (2408561 : Nat)) ∧ (1639587 : FRC.Shell (2408561 : Nat)) ^ (8 : Nat) = (1 : FRC.Shell (2408561 : Nat)) ∧ (1639587 : FRC.Shell (2408561 : Nat)) * (1111186 : FRC.Shell (2408561 : Nat)) = (1 : FRC.Shell (2408561 : Nat)) ∧ ((1639587 : FRC.Shell (2408561 : Nat)) + (1111186 : FRC.Shell (2408561 : Nat))) ^ (2 : Nat) = (2 : FRC.Shell (2408561 : Nat)) ∧ ((2 : FRC.Shell (2408561 : Nat)) * ((1639587 : FRC.Shell (2408561 : Nat)) + (1111186 : FRC.Shell (2408561 : Nat)))) ^ (2 : Nat) = (8 : FRC.Shell (2408561 : Nat)) :=
  And.intro @FRC.Entropy.tsirelson_square (And.intro @FRC.Entropy.octant_iff (@FRC.Entropy.lab_carrier))
/-- 14:C10 (p14027) — The capacity axis \apx: holographic ring capacity $\log_{10}\kap_{q}$, zero at hydrogen ($\kap_H=3$; $\kap_{q}=2$ has no shell), one dex per chart dex, terminating at the count face $\sqrt{\dS}$ --- the triangle's own sixty dex; the one-gram horizontal lands on $N_A$ to $0.0035$ dex (the $1.008$\,u offset), asserted before drawing. -/
theorem p14027 : FRC.Nat.isPrime (5 : Nat) ∧ ¬FRC.Nat.isPrime (9 : Nat) ∧ FRC.Nat.isPrime ((12 : Nat) * (1 : Nat) + (1 : Nat)) ∧ ¬FRC.Nat.isPrime ((12 : Nat) * (2 : Nat) + (1 : Nat)) ∧ FRC.Nat.isPrime ((12 : Nat) * (3 : Nat) + (1 : Nat)) :=
  @FRC.Entropy.capacity_axis
/-- 14:X4 (p14031) — \textbf{The congruence $\dS$ even} acquires a second physical face: it is the existence of the octant sector, hence the well-definedness of the measured age --- a structure of the Carrier's cycle lattice, certified by realisation and read as an observational condition, never an arithmetic property of the numeral. -/
theorem p14031 : ∀ {p : Nat} [FRC.Pos p] {κ : Nat} {g : FRC.Shell p}, FRC.Shell.Frame p κ g → ((∃ r, r * r = (2 : FRC.Shell p)) ↔ ∃ m, κ = (2 : Nat) * m) :=
  @FRC.Ledger.p14031
-- end ledger predicates

end FRC.Entropy
