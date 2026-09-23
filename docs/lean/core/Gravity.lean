import FrcCore.Frame
import FrcCore.Entropy
import FrcCore.Instances

/-!
# 21-gravity — the Carrier register and the count face on every frame, no axioms

The finite content of *Gravitation as Phase Synchronisation over Finite Holographic Substrate* (tree
`21-gravity-20260623`) from first principles. On every frame `(τ; 0, 1, g)` of capacity `κ` (`p = 4κ + 1`):
the calibration congruence `4κ = −1`, `(4κ)² = 1` (C16); the register value of the Newton constant `G = 2κ`
— `2G = −1`, `(−2) G = 1` (the face convention `4π ↦ −2`), the Gauss count `(2 · 4κ) G = 1`, `c² = 2⁻¹ = 2κ + 1`
with `2c² = 1`, and `G = −c²` (C2, C5, C16); the action quantum as a member of the quarter-turn pair,
`ħ = g^κ = −i` (`Frame.quarterTurn g κ = −g^κ`) with `ħ² = −1`, and `ħ = 2r` for the square root `r = g^κ c²` of
the capacity, `r² = κ` (C5). In the count register: the count
face of the area law, `4S + 1 = p²` for `S = κ(4κ + 2)`, `Sp = κA` and `4Sp = A(p − 1)` for `A = p(p + 1)`
(C13); the two-face ratio `κ/S : κ/(2S) = 2` and the fibre product `(p − 1)(Ω − 1) = 4 · 4κS` (A9). Decided
by the kernel: the register on `𝔽₁₃` (`κ = 3`, drive `2`) and `𝔽₁₇` (`κ = 4`, drive `3`), the merger law's
instance `27 811 + 1 596 → 29 407` with `ΔA = 88 772 712` (C13), and the laboratory Carrier `Ω = 2 408 561`:
`4S = 2 408 560 = −1`, `(4S)² = 1`, `G = 1 204 280` with `2G = −1`, `(−2) G = 1`, the Gauss count, `ħ = 18 688`
with `ħ² = −1`, `ħ = 2 · 9 344` and `9 344² = S = 602 140` (C2, C5, C16; the residues `c = 171 106` and
`G = −c²` are `Dimensions.carrierLab`). Every declaration is checked to depend on no axiom
(`check_core_axioms.py`).
-/

namespace FRC.Gravity

open FRC.Shell

/-! ## The register on every frame (21:C2, C5, C16) -/
section register

variable {p : Nat} [Pos p] {κ : Nat} {g : Shell p}

/-- Literals multiply and add as their values, in the `ofNat` form. -/
theorem ofNat_mul (a b : Nat) : (ofNat a : Shell p) * ofNat b = ofNat (a * b) :=
  Shell.ext (by
    show (a % p * (b % p)) % p = (a * b) % p
    exact (FRC.Nat.mul_mod a b p Pos.pos).symm)

theorem ofNat_add (a b : Nat) : (ofNat a : Shell p) + ofNat b = ofNat (a + b) :=
  Shell.ext (by
    show (a % p + b % p) % p = (a + b) % p
    exact (FRC.Nat.add_mod a b p Pos.pos).symm)

/-- The residue of the cardinality itself is `0`. -/
theorem ofNat_p : (ofNat p : Shell p) = 0 :=
  Shell.ext (by show p % p = 0; exact FRC.Nat.mod_self p Pos.pos)

/-- 21:C16, 21:A1 — the calibration congruence on every frame: the full cycle `2π ↦ 4κ = p − 1` is `−1`,
and `(4κ)² = 1`. -/
theorem calibration (F : Frame p κ g) :
    (ofNat (4 * κ) : Shell p) = -1 ∧ (ofNat (4 * κ) : Shell p) * ofNat (4 * κ) = 1 := by
  have h : (ofNat (4 * κ) : Shell p) = -1 := by
    have h2 := F.two_pi
    have e : 2 * Frame.halfPeriod κ = 4 * κ := (FRC.Nat.mul_assoc 2 2 κ).symm
    rw [e] at h2
    exact h2
  exact ⟨h, by rw [h, Shell.neg_mul_neg, Shell.one_mul]⟩

/-- 21:C2, 21:C5, 21:C16 — the register value of the Newton constant on every frame, `G = 2κ`, the half-cycle:
`2G = −1`; `(−2) G = 1` (the face convention `4π ↦ −2`, `G = (−2)⁻¹`); the Gauss count `(2 · 4κ) G = 1`;
`c² = 2⁻¹ = 2κ + 1` with `2c² = 1`; and `G = −c²`. -/
theorem newton_residue (F : Frame p κ g) :
    (2 : Shell p) * ofNat (2 * κ) = -1 ∧ (-2 : Shell p) * ofNat (2 * κ) = 1 ∧
    (2 * ofNat (4 * κ) : Shell p) * ofNat (2 * κ) = 1 ∧
    (2 : Shell p) * ofNat (2 * κ + 1) = 1 ∧ (ofNat (2 * κ) : Shell p) = -ofNat (2 * κ + 1) := by
  obtain ⟨h4, _⟩ := calibration F
  have hG : (2 : Shell p) * ofNat (2 * κ) = -1 := by
    show ofNat 2 * ofNat (2 * κ) = -1
    rw [ofNat_mul, ← FRC.Nat.mul_assoc]
    exact h4
  have hG' : (-2 : Shell p) * ofNat (2 * κ) = 1 := by
    rw [← Shell.neg_mul, hG, Shell.neg_neg]
  have hc : (2 : Shell p) * ofNat (2 * κ + 1) = 1 := by
    show ofNat 2 * ofNat (2 * κ + 1) = 1
    rw [ofNat_mul, Nat.mul_add, ← FRC.Nat.mul_assoc, Nat.mul_one, ← ofNat_add, h4]
    show -1 + ofNat 2 = 1
    rw [show (ofNat 2 : Shell p) = 1 + 1 from Frame.two_eq_one_add_one, ← Shell.add_assoc, Shell.neg_add,
      Shell.zero_add]
  refine ⟨hG, hG', ?_, hc, ?_⟩
  · rw [h4, ← Shell.mul_neg, Shell.mul_one, hG']
  · apply Shell.eq_neg_of_add_eq_zero
    rw [ofNat_add, ← Nat.add_assoc, F.four_kappa, F.n_eq, ← F.cap]
    exact ofNat_p

/-- 21:C5 — the action quantum on every frame: `ħ = g^κ` is a member of the quarter-turn pair (`−i`, the
frame's `quarterTurn` being `−g^κ`), `ħ² = −1`; with `c² = 2κ + 1` the residue `r = ħ c²` is a square root of
the capacity, `r² = κ`, and `ħ = 2r` — the paper's `ħ = 2√S` read on the shell. -/
theorem hbar_root (F : Frame p κ g) :
    (g ^ κ) ^ 2 = -1 ∧ (g ^ κ * ofNat (2 * κ + 1)) * (g ^ κ * ofNat (2 * κ + 1)) = ofNat κ ∧
    (2 : Shell p) * (g ^ κ * ofNat (2 * κ + 1)) = g ^ κ := by
  obtain ⟨hq, _⟩ := F.quarter_turn_order
  obtain ⟨_, _, _, hc, _⟩ := newton_residue F
  obtain ⟨h4, _⟩ := calibration F
  have h2r : (2 : Shell p) * (g ^ κ * ofNat (2 * κ + 1)) = g ^ κ := by
    rw [Shell.mul_left_comm, hc, Shell.mul_one]
  refine ⟨hq, ?_, h2r⟩
  -- `4 (r² − κ) = (2r)² − 4κ = ħ² + 1 = 0`, and `4 ≠ 0` on the shell
  have h4ne : (4 : Shell p) ≠ 0 := by
    rw [show (4 : Shell p) = 2 * 2 from (ofNat_mul 2 2).symm]
    exact F.mul_ne_zero F.two_ne_zero F.two_ne_zero
  have h4κ : (4 : Shell p) * ofNat κ = -1 := by
    show ofNat 4 * ofNat κ = -1
    rw [ofNat_mul]; exact h4
  have h4r : (4 : Shell p) * ((g ^ κ * ofNat (2 * κ + 1)) * (g ^ κ * ofNat (2 * κ + 1))) = -1 := by
    rw [show (4 : Shell p) = 2 * 2 from (ofNat_mul 2 2).symm, FRC.Entropy.mul_mul_mul_comm, h2r,
      ← Shell.pow_two, hq]
  have key : (4 : Shell p) * ((g ^ κ * ofNat (2 * κ + 1)) * (g ^ κ * ofNat (2 * κ + 1)) + -ofNat κ) = 0 := by
    rw [Shell.left_distrib, h4r, ← Shell.mul_neg, h4κ, Shell.neg_neg]
    exact Shell.neg_add 1
  rcases F.mul_eq_zero key with h | h
  · exact absurd h h4ne
  · have := Shell.eq_neg_of_add_eq_zero h
    rw [Shell.neg_neg] at this
    exact this

end register

/-! ## The count face (21:A9, C13) -/
section count

/-- 21:C13 — the count face of the area law on `p = 4κ + 1`: `S = κ(4κ + 2)` has `4S + 1 = p²`
(`S = (p² − 1)/4`), and with the coordinate area `A = p(p + 1)`: `Sp = κA` (`S/A = κ/p`) and `4Sp = A(p − 1)`
(`S = (A/4)(1 − 1/p)`). -/
theorem count_identity (κ : Nat) :
    4 * (κ * (4 * κ + 2)) + 1 = (4 * κ + 1) * (4 * κ + 1) ∧
    κ * (4 * κ + 2) * (4 * κ + 1) = κ * ((4 * κ + 1) * (4 * κ + 2)) ∧
    4 * (κ * (4 * κ + 2)) * (4 * κ + 1) = ((4 * κ + 1) * (4 * κ + 2)) * (4 * κ) := by
  refine ⟨?_, ?_, ?_⟩
  · calc 4 * (κ * (4 * κ + 2)) + 1
        = 4 * (κ * (4 * κ) + κ * 2) + 1 := by rw [Nat.mul_add κ]
      _ = (4 * (κ * (4 * κ)) + 4 * (κ * 2)) + 1 := by rw [Nat.mul_add 4]
      _ = (4 * κ * (4 * κ) + 4 * κ * 2) + 1 := by rw [Nat.mul_assoc 4 κ (4 * κ), Nat.mul_assoc 4 κ 2]
      _ = (4 * κ * (4 * κ) + (4 * κ + 4 * κ)) + 1 := by rw [Nat.mul_two]
      _ = 4 * κ * (4 * κ) + 4 * κ + (4 * κ + 1) := by
          rw [Nat.add_assoc (4 * κ * (4 * κ)) (4 * κ + 4 * κ) 1, Nat.add_assoc (4 * κ) (4 * κ) 1,
            Nat.add_assoc (4 * κ * (4 * κ)) (4 * κ) (4 * κ + 1)]
      _ = (4 * κ + 1) * (4 * κ) + (4 * κ + 1) * 1 := by rw [Nat.add_mul, Nat.one_mul, Nat.mul_one]
      _ = (4 * κ + 1) * (4 * κ + 1) := by rw [← Nat.mul_add]
  · rw [Nat.mul_assoc, Nat.mul_comm (4 * κ + 2)]
  · calc 4 * (κ * (4 * κ + 2)) * (4 * κ + 1)
        = (4 * κ + 1) * (4 * (κ * (4 * κ + 2))) := Nat.mul_comm _ _
      _ = (4 * κ + 1) * ((4 * κ + 2) * (4 * κ)) := by
          rw [← Nat.mul_assoc 4 κ, Nat.mul_comm (4 * κ) (4 * κ + 2)]
      _ = (4 * κ + 1) * (4 * κ + 2) * (4 * κ) := (Nat.mul_assoc _ _ _).symm

/-- 21:A9 — the two-face count: the angular face `κ/S` against the temporal face `κ/(2S)` has ratio `2`
(`κ · 2S = 2 · κS`), and the registration fibre product has `(p − 1)(Ω − 1) = 4 · 4κS` for `p = 4κ + 1`,
`Ω = 4S + 1`. -/
theorem two_face_count (κ S : Nat) :
    κ * (2 * S) = 2 * (κ * S) ∧ (4 * κ) * (4 * S) = 4 * (4 * (κ * S)) := by
  refine ⟨Nat.mul_left_comm κ 2 S, ?_⟩
  rw [Nat.mul_assoc 4 κ, Nat.mul_left_comm κ 4]

end count

/-! ## The values decided by the kernel (21:C2, C5, C13, C16) -/
section values

/-- 21:C2, 21:C5, 21:C16 — the register on `𝔽₁₃` (`κ = 3`, drive `2`): `4κ = 12 = −1`, `G = 6` with
`2G = −1`, `c² = 7` with `2c² = 1`, `ħ = 2³ = 8 = −i` with `ħ² = −1` (the frame's `quarterTurn` is `5`), the root `r = 8 · 7 = 4` with `r² = 3 = κ` and
`2r = ħ`; and on `𝔽₁₇` (`κ = 4`, drive `3`): `4κ = 16 = −1`, `G = 8`, `c² = 9`, `ħ = 3⁴ = 13 = −i` (`quarterTurn`
`4`), `r = 15` with `r² = 4 = κ`, `2r = 13`. -/
theorem register13_17 :
    (12 : Shell 13) = -1 ∧ 2 * (6 : Shell 13) = -1 ∧ 2 * (7 : Shell 13) = 1 ∧ (6 : Shell 13) = -7 ∧
    (2 : Shell 13) ^ 3 = 8 ∧ (8 : Shell 13) * 8 = -1 ∧ (4 : Shell 13) * 4 = 3 ∧ 2 * (4 : Shell 13) = 8 ∧
    (16 : Shell 17) = -1 ∧ 2 * (8 : Shell 17) = -1 ∧ 2 * (9 : Shell 17) = 1 ∧ (8 : Shell 17) = -9 ∧
    (3 : Shell 17) ^ 4 = 13 ∧ (13 : Shell 17) * 13 = -1 ∧ (15 : Shell 17) * 15 = 4 ∧
    2 * (15 : Shell 17) = 13 := by decide +kernel

/-- 21:C13 — the merger law's instance on the count face `A = M(M + 1)`: `27 811 + 1 596 → 29 407` gives
`ΔA = 2 · 27 811 · 1 596 = 88 772 712`. -/
theorem merger_instance :
    29407 * (29407 + 1) = 27811 * (27811 + 1) + 1596 * (1596 + 1) + 88772712 ∧
    2 * (27811 * 1596) = 88772712 ∧ 27811 + 1596 = 29407 := by decide

/-- 21:C2, 21:C5, 21:C16 — the laboratory Carrier `Ω = 2 408 561` (`S = 602 140`), host-decided: `4S = 2 408 560 = −1`
and `(4S)² = 1` (the calibration congruence); `G = 1 204 280 = 2S` with `2G = −1`, `(−2) G = 1` and the Gauss
count `(2 · 4S) G = 1`; `ħ = 18 688` with `ħ² = −1`, `ħ = 2 · 9 344` and `9 344² = S`. -/
theorem lab_register :
    4 * 602140 = 2408560 ∧ (2408560 : Shell 2408561) = -1 ∧
    (2408560 : Shell 2408561) * 2408560 = 1 ∧
    2 * (1204280 : Shell 2408561) = -1 ∧ (-2 : Shell 2408561) * 1204280 = 1 ∧
    (2 * (2408560 : Shell 2408561)) * 1204280 = 1 ∧
    (18688 : Shell 2408561) * 18688 = -1 ∧ 2 * (9344 : Shell 2408561) = 18688 ∧
    (9344 : Shell 2408561) * 9344 = 602140 := by decide +kernel

end values

end FRC.Gravity
