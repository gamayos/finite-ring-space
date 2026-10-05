import FrcCore.Frame

/-!
# FrcCore.Theme.Projective — the affine group of the shell (the projective theme, ledger migration task LM17)

The affine maps `x ↦ a + b·x`, `b ≠ 0`: the Borel subgroup of `PGL₂` acting on the shell's affine line. They form a
group under composition and act simply transitively on the frames `(a, b)`; there are `p·(p − 1)` of them
(1:C2, 4:C5). Moved from 1-algebra with their names unchanged. No axioms.
-/

namespace FRC
namespace Shell
namespace Frame

variable {p : Nat} [Pos p] {κ : Nat} {g : Shell p}

/-- An affine map of the shell, `x ↦ a + b·x` with `b ≠ 0`. -/
structure Affine (p : Nat) [Pos p] where
  a : Shell p
  b : Shell p
  hb : b ≠ 0

namespace Affine

def apply (φ : Affine p) (x : Shell p) : Shell p := φ.a + φ.b * x

theorem ext' {φ ψ : Affine p} (ha : φ.a = ψ.a) (hb : φ.b = ψ.b) : φ = ψ := by
  cases φ; cases ψ; cases ha; cases hb; rfl

/-- The identity `x ↦ 0 + 1·x`. -/
def one (F : Frame p κ g) : Affine p := ⟨0, 1, F.one_ne_zero⟩

/-- Composition: `(a, b) ∘ (c, d) = (a + b·c, b·d)`. -/
def comp (F : Frame p κ g) (φ ψ : Affine p) : Affine p := ⟨φ.a + φ.b * ψ.a, φ.b * ψ.b, F.mul_ne_zero φ.hb ψ.hb⟩

theorem comp_apply (F : Frame p κ g) (φ ψ : Affine p) (x : Shell p) :
    (comp F φ ψ).apply x = φ.apply (ψ.apply x) := by
  unfold comp apply
  show φ.a + φ.b * ψ.a + φ.b * ψ.b * x = φ.a + φ.b * (ψ.a + ψ.b * x)
  rw [left_distrib, add_assoc, mul_assoc]

theorem one_apply (F : Frame p κ g) (x : Shell p) : (one F).apply x = x := by
  unfold one apply; show 0 + 1 * x = x; rw [one_mul, zero_add]

theorem comp_assoc (F : Frame p κ g) (φ ψ χ : Affine p) : comp F (comp F φ ψ) χ = comp F φ (comp F ψ χ) :=
  ext' (by show φ.a + φ.b * ψ.a + φ.b * ψ.b * χ.a = φ.a + φ.b * (ψ.a + ψ.b * χ.a); rw [left_distrib, add_assoc, mul_assoc])
    (by show φ.b * ψ.b * χ.b = φ.b * (ψ.b * χ.b); exact mul_assoc _ _ _)

/-- The inverse of `(a, b)`: `(−a·b⁻¹, b⁻¹)`, with `y` the inverse of `b`. -/
def inv (F : Frame p κ g) (φ : Affine p) (y : Shell p) (hy : φ.b * y = 1) : Affine p :=
  ⟨-(φ.a * y), y, fun h => F.one_ne_zero (by rw [← hy, h, mul_zero])⟩

theorem comp_inv (F : Frame p κ g) (φ : Affine p) (y : Shell p) (hy : φ.b * y = 1) :
    comp F φ (inv F φ y hy) = one F :=
  ext' (by
      show φ.a + φ.b * -(φ.a * y) = 0
      calc φ.a + φ.b * -(φ.a * y) = φ.a + -(φ.b * (φ.a * y)) := by rw [← mul_neg]
        _ = φ.a + -(φ.a * (φ.b * y)) := by rw [mul_left_comm]
        _ = φ.a + -φ.a := by rw [hy, mul_one]
        _ = 0 := add_neg _)
    (by show φ.b * y = 1; exact hy)

/-- 1:C2, 4:C5 (the frame group), simple transitivity — for frames `(a, b)` and `(c, d)` (`b, d ≠ 0`) there
is exactly one affine map carrying the first to the second: `φ (a, b) := (φ.apply a, φ.b · b)`. -/
theorem simply_transitive (F : Frame p κ g) (a b c d : Shell p) (hb : b ≠ 0) (hd : d ≠ 0) :
    (∃ φ : Affine p, φ.apply a = c ∧ φ.b * b = d) ∧
    (∀ φ ψ : Affine p, φ.apply a = c → φ.b * b = d → ψ.apply a = c → ψ.b * b = d → φ = ψ) := by
  match F.exists_inv hb with
  | ⟨y, hy⟩ =>
    constructor
    · refine ⟨⟨c + -(d * y * a), d * y, ?_⟩, ?_, ?_⟩
      · exact F.mul_ne_zero hd (fun h => F.one_ne_zero (by rw [← hy, h, mul_zero]))
      · show c + -(d * y * a) + d * y * a = c
        rw [add_assoc, neg_add, add_zero]
      · show d * y * b = d
        rw [mul_assoc, mul_comm y b, hy, mul_one]
    · intro φ ψ h1 h2 h3 h4
      have eb : φ.b = ψ.b := by
        calc φ.b = φ.b * (b * y) := by rw [hy, mul_one]
          _ = (φ.b * b) * y := (mul_assoc _ _ _).symm
          _ = (ψ.b * b) * y := by rw [h2, h4]
          _ = ψ.b := by rw [mul_assoc, hy, mul_one]
      have ea : φ.a = ψ.a := by
        have e1 : φ.a + φ.b * a = c := h1
        have e2 : ψ.a + ψ.b * a = c := h3
        rw [← eb] at e2
        exact add_right_cancel (e1.trans e2.symm)
      exact ext' ea eb

end Affine

/-- 1:C2, 4:C5, the order — the frames `(a, b)`, `b ≠ 0`, number `p·(p − 1)`: `p` choices of the origin, `p − 1`
of the unit. -/
theorem frame_count (_F : Frame p κ g) :
    natCount (fun _ => True) p * natCount (fun b => b ≠ 0) p = p * (p - 1) := by
  have h1 : ∀ n, natCount (fun _ => True) n = n := fun n => by
    induction n with
    | zero => rfl
    | succ n ih => show natCount (fun _ => True) n + (if True then 1 else 0) = n + 1; rw [ih, ite_eq_left trivial]
  have hp : p = (p - 1) + 1 := (FRC.Nat.sub_add_cancel Pos.pos).symm
  rw [h1]
  have h2 : natCount (fun b => b ≠ 0) p = p - 1 := by
    have := natCount_ne_zero (p - 1)
    rw [← hp] at this; exact this
  rw [h2]

end Frame
end Shell
end FRC
