import FrcCore.Theme.Lorentz

/-!
# FrcCore.Theme.Register — the register and the fixed points of the frame moves (7-spacetime)

The projective theme's fourth core file (2 November 2026; the record schema of 7-spacetime). 7:B6: a translation `[x : y] ↦
[x + by : y]` with `b ≠ 0` fixes `[x : y]` exactly when `y = 0`, the antipode (`translation_fixes_antipode`). 7:C10: on `ℙ¹(𝔽₁₃)`
every non-identity element of `PGL₂` fixes two, one or no direction as its discriminant is a nonzero square, zero or a nonsquare
(`fixed_points_13`, by the kernel over the `2183` classes), and the `1001`, `168`, `1014` elements with two, one and no fixed point
are `11 · 91`, `12 · 14` and `13 · 78`, the square axes, the null directions and the nonsquare axes of space
(`fixed_points_of_class`). 7:F5: the record of `n < m < Ω − 1` chronons is strictly increasing (`record_second_law`) and the
saturated record is four channel counts plus the origin, `(4κ + 1)² = 4κ(4κ + 2) + 1` (`record_quarter`, the three pairs in
`record_quarter_pairs`). 7:P2: `k_B c = ħ` gives `k_B (cH) = ħH`, the floor as the temperature (`floor_is_temperature`), and the
three Carriers' residues satisfy `k_B c ≡ ħ`, `ħ² ≡ −1`, `k_B² ≡ −2` (`kB_c_carriers`). No axioms.
-/

namespace FRC.Register

open FRC.Shell FRC.Lorentz

variable {p : Nat} [Pos p]

/-- 7:B6 — **a nontrivial translation fixes the antipode alone.** On the frame's line the translation `[x : y] ↦ [x + by : y]`
with `b ≠ 0` fixes `[x : y]` exactly when `y = 0`: `x + by = x` forces `by = 0`, and the frame's shell has no zero divisors
(`Frame.mul_eq_zero`, the frame theme; the hypothesis is the frame, which makes the shell prime). -/
theorem translation_fixes_antipode {κ : Nat} {g : Shell p} (F : Frame p κ g) (b x y : Shell p) (hb : b ≠ 0) :
    x + b * y = x ↔ y = 0 := by
  constructor
  · intro h
    have h1 : b * y + x = 0 + x := by rw [add_comm, h, zero_add]
    match F.mul_eq_zero (add_right_cancel h1) with
    | Or.inl e => exact absurd e hb
    | Or.inr e => exact e
  · intro h; rw [h, mul_zero, add_zero]

/-- Whether `[[a, b], [c, d]]` fixes the direction `(x, y)` on `𝔽₁₃`: the image `(ax + by, cx + dy)` is proportional to `(x, y)`,
that is `(ax + by) y = (cx + dy) x`. -/
def fixes13 (a b c d : Nat) (pt : Nat × Nat) : Bool := ((a * pt.1 + b * pt.2) * pt.2) % 13 = ((c * pt.1 + d * pt.2) * pt.1) % 13
/-- The number of the `14` directions that `[[a, b], [c, d]]` fixes. -/
def fixedCount13 (a b c d : Nat) : Nat := (classes13.filter (fixes13 a b c d)).length
/-- The fixed points a discriminant class predicts: two for a nonzero square, one for zero, none for a nonsquare. -/
def predicted13 (a b c d : Nat) : Nat := let Δ := disc13 a b c d; if Δ = 0 then 1 else if isSquare13 Δ then 2 else 0
/-- A representative of its class in `PGL₂(𝔽₁₃)`: the first nonzero entry of `[[a, b], [c, d]]` is `1`. -/
def isRep13 (a b c d : Nat) : Bool := (if a ≠ 0 then a else if b ≠ 0 then b else if c ≠ 0 then c else d) = 1
/-- Over the `2183` non-identity classes of `PGL₂(𝔽₁₃)`: how many fix the predicted number, and the tally of two, one and none. -/
def fixedTally13 : Nat × (Nat × Nat × Nat) :=
  (List.range 13).foldl (fun acc a => (List.range 13).foldl (fun acc b => (List.range 13).foldl (fun acc c =>
    (List.range 13).foldl (fun acc d =>
      if isInvertible13 a b c d ∧ isRep13 a b c d ∧ (a, b, c, d) ≠ (1, 0, 0, 1) then
        let f := fixedCount13 a b c d
        (if f = predicted13 a b c d then acc.1 + 1 else acc.1,
         if f = 2 then (acc.2.1 + 1, acc.2.2.1, acc.2.2.2) else if f = 1 then (acc.2.1, acc.2.2.1 + 1, acc.2.2.2) else (acc.2.1, acc.2.2.1, acc.2.2.2 + 1))
      else acc) acc) acc) acc) (0, (0, 0, 0))
/-- 7:C10 — **the fixed points by the discriminant class at `p = 13`.** Every non-identity element of `PGL₂(𝔽₁₃)` fixes the
predicted number of directions; the tally `1001`, `168`, `1014` of two, one and none is the class equation's three terms. -/
theorem fixed_points_13 : fixedTally13 = (2183, (1001, 168, 1014)) ∧ 1 + 1001 + 168 + 1014 = 12 * 13 * 14 := by decide +kernel

/-- The directions of space, the binary forms `(s₁₁, s₁₂, s₂₂)` up to scale on `𝔽₁₃`, by the class of `s₁₂² − s₁₁s₂₂`: null,
nonsquare axes (internal points), square axes (external points). -/
def directionCounts13 : Nat × Nat × Nat :=
  (List.range 13).foldl (fun acc s11 => (List.range 13).foldl (fun acc s12 => (List.range 13).foldl (fun acc s22 =>
    let lead := if s11 ≠ 0 then s11 else if s12 ≠ 0 then s12 else s22
    if lead = 1 then
      let Δ := (s12 * s12 + 169 - s11 * s22) % 13
      if Δ = 0 then (acc.1 + 1, acc.2.1, acc.2.2) else if isSquare13 Δ then (acc.1, acc.2.1, acc.2.2 + 1) else (acc.1, acc.2.1 + 1, acc.2.2)
    else acc) acc) acc) (0, 0, 0)
/-- 7:C10 — **the three kinds of cycle are the three kinds of direction at `p = 13`.** `14` null directions, `78` nonsquare and
`91` square axes; the tally of `fixed_points_13` is `78 · 13` elements with no fixed point (the non-split tori, `13` non-identity
elements each), `14 · 12` with one (the unipotent groups, `12` each) and `91 · 11` with two (the split tori, `11` each). -/
theorem fixed_points_of_class : directionCounts13 = (14, 78, 91) ∧ 1014 = 78 * 13 ∧ 168 = 14 * 12 ∧ 1001 = 91 * 11 ∧
    14 = 13 + 1 ∧ 78 = 13 * 12 / 2 ∧ 91 = 13 * 14 / 2 := by decide +kernel

/-- 7:F5 — **the record is strictly increasing below the cycle.** For `n < m < Ω − 1` the chart counts are `n` and `m`
themselves, so the record of `m` chronons holds the record of `n` and one entry more per chronon, the entries distinct. -/
theorem record_second_law (Om n m : Nat) (hm : m < Om - 1) (h : n < m) : n % (Om - 1) < m % (Om - 1) := by
  rw [FRC.Nat.mod_eq_of_lt (Nat.lt_trans h hm), FRC.Nat.mod_eq_of_lt hm]; exact h

/-- 7:F5 — **the saturated record is four channel counts plus the origin**: `(4κ + 1)² = 4 · κ(4κ + 2) + 1`, and `κ(4κ + 2)` is
the channel count `κ(p + 1)` of the first law (00:D15); the entropy of the first law is the record's quarter. -/
theorem record_quarter (k : Nat) : (4 * k + 1) * (4 * k + 1) = 4 * (k * (4 * k + 1 + 1)) + 1 := by
  have h1 : (4 * k + 1) * (4 * k + 1) = 4 * k * (4 * k) + 4 * k + (4 * k + 1) := by
    rw [FRC.Nat.add_mul, Nat.mul_add, Nat.mul_one, Nat.one_mul]
  have h2 : 4 * (k * (4 * k + 1 + 1)) = 4 * k * (4 * k) + 4 * k + 4 * k := by
    rw [Nat.mul_add, Nat.mul_add, Nat.mul_one, Nat.mul_add, Nat.mul_add, FRC.Nat.mul_assoc, Nat.mul_one]
  rw [h1, h2, Nat.add_assoc (4 * k * (4 * k) + 4 * k) (4 * k) 1]

/-- 7:F5 — **the three laboratory pairs**: `p² = 4κ(p + 1) + 1` at `p = 13, 173, 1549`, and `p² < Ω − 1` in the Carriers
`233, 30089, 2408561`, so the record saturates below the cycle. -/
theorem record_quarter_pairs : 13 * 13 = 4 * (3 * 14) + 1 ∧ 173 * 173 = 4 * (43 * 174) + 1 ∧ 1549 * 1549 = 4 * (387 * 1550) + 1 ∧
    13 * 13 < 233 - 1 ∧ 173 * 173 < 30089 - 1 ∧ 1549 * 1549 < 2408561 - 1 := by decide

/-- 7:P2 — **the floor is the Carrier's temperature.** With the chart's unit `k_B c = ħ` (00:B7), `k_B · (cH) = ħ · H`: the de
Sitter temperature `ħH/(2π k_B)` and the floor `cH/2π` are one number, `k_B T_dS = (ħ/c) a₀`. -/
theorem floor_is_temperature (kB c hbar H : Nat) (h : kB * c = hbar) : kB * (c * H) = hbar * H := by
  rw [← Nat.mul_assoc, h]

/-- 7:P2 — **`k_B c ≡ ħ`, `ħ² ≡ −1` and `k_B² ≡ −2` on the three Carriers**: the residues of the register at `Ω = 233`
(`c = 159`, `ħ = 144`, `k_B = 124`), `30089` (`27765`, `22003`, `2567`) and `2408561` (`2237455`, `18688`, `1880160`). -/
theorem kB_c_carriers : 124 * 159 % 233 = 144 ∧ 144 * 144 % 233 = 232 ∧ 124 * 124 % 233 = 231 ∧
    2567 * 27765 % 30089 = 22003 ∧ 22003 * 22003 % 30089 = 30088 ∧ 2567 * 2567 % 30089 = 30087 ∧
    1880160 * 2237455 % 2408561 = 18688 ∧ 18688 * 18688 % 2408561 = 2408560 ∧ 1880160 * 1880160 % 2408561 = 2408559 := by decide

end FRC.Register
