import FrcCore.Frame

/-!
# FrcCore.Instances — concrete shells, decided by computation

Every statement here is closed by `decide`: the kernel evaluates the shell arithmetic (through its
accelerated `Nat` operations) and the proof term is `of_decide_eq_true rfl`. No axiom, no library.
-/

namespace FRC
namespace Shell

/-- 00:C1 on `𝔽₁₃`: the frame `(τ; 0, 1, 2)` of capacity `3` — `2` is a primitive generator. -/
theorem frame13 : Frame 13 3 (2 : Shell 13) := ⟨rfl, Nat.zero_lt_succ 2, by decide, by decide⟩

/-- 1:B3, 2:D3 [value] — on `𝔽₁₃(τ; 0, 1, 2)`: `i = −2³ = 5`, `i² = −1`, `−i = 8`, `π = 6`, `2^6 = −1`,
`e = 2^5 = 6`. -/
theorem s13_datum :
    Frame.quarterTurn (2 : Shell 13) 3 = 5 ∧ (5 : Shell 13) * 5 = -1 ∧ -(5 : Shell 13) = 8 ∧
    (2 : Shell 13) ^ 6 = -1 ∧ (2 : Shell 13) ^ 5 = 6 := by decide

/-- 2:D6 [value] — the Euler identity on `𝔽₁₃`: the representative `5` of `i` is odd, `e^{iπ} = −1`. -/
theorem s13_euler : ((2 : Shell 13) ^ 5) ^ (5 * 6) = -1 := by decide

/-- 00:C1 on `𝔽₁₇`: two frames, `g = 3` and `g = 6`. -/
theorem frame17a : Frame 17 4 (3 : Shell 17) := ⟨rfl, Nat.zero_lt_succ 3, by decide, by decide⟩
theorem frame17b : Frame 17 4 (6 : Shell 17) := ⟨rfl, Nat.zero_lt_succ 3, by decide, by decide⟩

set_option maxRecDepth 20000 in
/-- 2:D6 [value], 00:C14 — on `𝔽₁₇` the frame `g = 3` reads `i = 4` (even: `e^{iπ} = +1`) and the frame
`g = 6` reads `i = 13` (odd: `e^{iπ} = −1`); `6 = 3^{15}` with `15 ≡ 3 (mod 4)` flips the orientation. -/
theorem s17_orientation :
    Frame.quarterTurn (3 : Shell 17) 4 = 4 ∧ Frame.quarterTurn (6 : Shell 17) 4 = 13 ∧
    ((3 : Shell 17) ^ 4) ^ (4 * 8) = 1 ∧ ((6 : Shell 17) ^ 13) ^ (13 * 8) = -1 ∧
    (3 : Shell 17) ^ 15 = 6 := by decide

/-- 00:C1 on `𝔽₂₉`: the frame `(τ; 0, 1, 2)`, capacity `7`. -/
theorem frame29 : Frame 29 7 (2 : Shell 29) := ⟨rfl, Nat.zero_lt_succ 6, by decide, by decide⟩

/-- 1:B2 [value] — on `𝔽₁₃` the fourth roots of unity are `{1, 5, 12, 8}`, and every other nonzero
residue has four distinct companions `{x, −x, x⁻¹, −x⁻¹}`: the two Klein orbits `{2, 11, 7, 6}` and
`{3, 10, 9, 4}`. -/
theorem s13_klein :
    (∀ x : Fin 13, (x.val = 1 ∨ x.val = 5 ∨ x.val = 12 ∨ x.val = 8) ↔ (ofNat x.val : Shell 13) ^ 4 = 1) ∧
    (2 : Shell 13) * 7 = 1 ∧ (3 : Shell 13) * 9 = 1 := by decide

end Shell
end FRC
