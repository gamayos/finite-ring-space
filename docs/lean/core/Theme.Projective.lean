import FrcCore.Ring
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


/-! ## C19: the Hopf section of `PGL₂` (task LM25)

`PGL₂(𝔽_p)` by elements: a matrix `[[a, b], [c, d]]` acts on the projective line by `[x : y] ↦ [a x + b y : c x + d y]`
and is read up to a nonzero scalar. The non-split torus is the boosts `[[α, νβ], [β, α]]` (`ν` a nonsquare), the Borel
subgroup the upper-triangular matrices, the stabiliser of the horizon `[1 : 0]`: the cone chart `x ↦ a x + b`. -/

/-- A 2 × 2 matrix over the shell. -/
structure M2 (p : Nat) [Pos p] where
  a : Shell p
  b : Shell p
  c : Shell p
  d : Shell p

namespace M2

theorem ext' {M N : M2 p} (ha : M.a = N.a) (hb : M.b = N.b) (hc : M.c = N.c) (hd : M.d = N.d) : M = N := by
  cases M; cases N; cases ha; cases hb; cases hc; cases hd; rfl

/-- The product. -/
def mul (M N : M2 p) : M2 p :=
  ⟨M.a * N.a + M.b * N.c, M.a * N.b + M.b * N.d, M.c * N.a + M.d * N.c, M.c * N.b + M.d * N.d⟩

/-- A scalar multiple. -/
def smul (l : Shell p) (M : M2 p) : M2 p := ⟨l * M.a, l * M.b, l * M.c, l * M.d⟩

/-- The determinant. -/
def det (M : M2 p) : Shell p := M.a * M.d + -(M.b * M.c)

/-- The action on the projective line, `[x : y] ↦ [a x + b y : c x + d y]`. -/
def act (M : M2 p) (x y : Shell p) : Shell p × Shell p := (M.a * x + M.b * y, M.c * x + M.d * y)

end M2

/-- The boost `α + β w` as a matrix, `[[α, ν β], [β, α]]`: the non-split torus `C_{p+1}`. -/
def boost (ν α β : Shell p) : M2 p := ⟨α, ν * β, β, α⟩

/-- An upper-triangular matrix `[[a, b], [0, e]]`: the Borel subgroup, the cone chart `x ↦ (a x + b)/e`. -/
def borel (a b e : Shell p) : M2 p := ⟨a, b, 0, e⟩

/-- Two points `(x, y)`, `(x', y')` of the projective line are equal, `x y' = x' y`. -/
def PEq (u v : Shell p × Shell p) : Prop := u.1 * v.2 = v.1 * u.2

theorem eq_of_add_neg_eq_zero {x y : Shell p} (h : x + -y = 0) : x = y := by
  rw [← add_zero x, ← neg_add y, ← add_assoc, h, zero_add]

/-- On a frame, `x² − ν y² ≠ 0` for `(x, y) ≠ 0` when `ν` is a nonsquare. -/
theorem norm_ne_zero (F : Frame p κ g) {ν : Shell p} (hν : ¬ ∃ y : Shell p, y * y = ν) {x y : Shell p}
    (hxy : x ≠ 0 ∨ y ≠ 0) : x * x + -(ν * (y * y)) ≠ 0 := fun h => by
  have e := eq_of_add_neg_eq_zero h
  match Shell.instDecidableEq y 0 with
  | .isTrue hy =>
    rw [hy, mul_zero, mul_zero] at e
    exact hxy.elim (fun hx => hx (match F.mul_eq_zero e with | .inl h => h | .inr h => h)) (fun h => h hy)
  | .isFalse hy =>
    obtain ⟨s, hs⟩ := F.exists_inv hy
    exact hν ⟨x * s, by rw [mul_mul_mul_comm, e, mul_assoc, ← mul_mul_mul_comm, hs, mul_one, mul_one]⟩

/-- **C19 (p00039), the Hopf section.** In `PGL₂(𝔽_p)` on a frame, `ν` a nonsquare:
(1) a boost that is not scalar fixes no point of `ℙ¹`; (2) a boost in the Borel subgroup is scalar: `T ∩ B = 1`;
(3) every invertible matrix factors as (cone chart) × (boost) up to a scalar, (4) uniquely up to scalars — the cone
chart is a global section of `G → G/T`; (5) the boost classes are the points of `ℙ¹` (`p + 1` per fibre) and (6) the
cone charts number `p (p − 1)`; (7) on the spin cover `SL₂` the sign `−I` is both a boost and a chart, `B ∩ T = {±I}`
there, and `b t = (−b)(−t)`: the section obstructs at `−1`. -/
theorem hopf_section (F : Frame p κ g) {ν : Shell p} (hν : ¬ ∃ y : Shell p, y * y = ν) :
    (∀ α β x y : Shell p, β ≠ 0 → (x ≠ 0 ∨ y ≠ 0) → ¬ PEq ((boost ν α β).act x y) (x, y)) ∧
    (∀ α β a b e l : Shell p, boost ν α β = M2.smul l (borel a b e) → β = 0) ∧
    (∀ M : M2 p, M.det ≠ 0 → ∃ N a b e α β : Shell p, N ≠ 0 ∧ a * e ≠ 0 ∧ (α ≠ 0 ∨ β ≠ 0) ∧
      M2.smul N M = (borel a b e).mul (boost ν α β)) ∧
    (∀ l a1 b1 e1 α1 β1 a2 b2 e2 α2 β2 : Shell p, l ≠ 0 → e2 ≠ 0 → (α1 ≠ 0 ∨ β1 ≠ 0) →
      M2.smul l ((borel a1 b1 e1).mul (boost ν α1 β1)) = (borel a2 b2 e2).mul (boost ν α2 β2) →
      α1 * β2 = α2 * β1 ∧ e2 * a1 = e1 * a2 ∧ e2 * b1 = e1 * b2) ∧
    (∀ α β α' β' : Shell p, (α ≠ 0 ∨ β ≠ 0) → (α' ≠ 0 ∨ β' ≠ 0) →
      ((∃ μ : Shell p, μ ≠ 0 ∧ boost ν α' β' = M2.smul μ (boost ν α β)) ↔ α * β' = α' * β)) ∧
    natCount (fun _ => True) p * natCount (fun b => b ≠ 0) p = p * (p - 1) ∧
    (boost ν (-1) 0 = borel (-1) 0 (-1) ∧ (-1 : Shell p) * -1 + -(ν * (0 * 0)) = 1 ∧ (-1 : Shell p) * -1 = 1 ∧
      (∀ α β a b e : Shell p, boost ν α β = borel a b e → α * α + -(ν * (β * β)) = 1 → β = 0 ∧ (α = 1 ∨ α = -1)) ∧
      ∀ M N : M2 p, (M2.smul (-1) M).mul (M2.smul (-1) N) = M.mul N) := by
  have hN : ∀ {x y : Shell p}, (x ≠ 0 ∨ y ≠ 0) → x * x + -(ν * (y * y)) ≠ 0 := fun hxy => norm_ne_zero F hν hxy
  refine ⟨fun α β x y hβ hxy hP => ?_, fun α β a b e l h => ?_, fun M hM => ?_,
    fun l a1 b1 e1 α1 β1 a2 b2 e2 α2 β2 hl he2 hαβ h => ?_, fun α β α' β' h1 h2 => ?_, frame_count F, ?_⟩
  · -- (1) a fixed point forces `β (ν y² − x²) = 0`
    have e : (α * x + ν * β * y) * y + -(x * (β * x + α * y)) = β * (ν * (y * y) + -(x * x)) :=
      Shell.Frame.RE.sound (Shell.Frame.look [α, β, ν, x, y])
        (.add (.mul (.add (.mul (.var 0) (.var 3)) (.mul (.mul (.var 2) (.var 1)) (.var 4))) (.var 4)) (.neg (.mul (.var 3) (.add (.mul (.var 1) (.var 3)) (.mul (.var 0) (.var 4))))))
        (.mul (.var 1) (.add (.mul (.var 2) (.mul (.var 4) (.var 4))) (.neg (.mul (.var 3) (.var 3))))) (by decide +kernel)
    have hP' : (α * x + ν * β * y) * y = x * (β * x + α * y) := hP
    rw [hP', add_neg] at e
    match F.mul_eq_zero e.symm with
    | .inl h => exact hβ h
    | .inr h =>
      have h' : x * x + -(ν * (y * y)) = 0 := by
        rw [← neg_neg (x * x + -(ν * (y * y))), neg_add_rev, neg_neg, add_comm, h, neg_zero]
      exact hN hxy h'
  · -- (2) the `c`-entry
    have := congrArg M2.c h
    show β = 0
    exact this.trans (mul_zero l)
  · -- (3) `N M = [[det, b d − ν a c], [0, N]] · boost (d, c)`, `N = d² − ν c²`
    have hcd : M.d ≠ 0 ∨ M.c ≠ 0 := by
      match Shell.instDecidableEq M.d 0, Shell.instDecidableEq M.c 0 with
      | .isTrue hd, .isTrue hc =>
        exact absurd (show M.det = 0 by
          show M.a * M.d + -(M.b * M.c) = 0; rw [hd, hc, mul_zero, mul_zero, neg_zero, add_zero]) hM
      | .isFalse hd, _ => exact .inl hd
      | _, .isFalse hc => exact .inr hc
    refine ⟨M.d * M.d + -(ν * (M.c * M.c)), M.det, M.b * M.d + -(ν * (M.a * M.c)), M.d * M.d + -(ν * (M.c * M.c)),
      M.d, M.c, hN hcd, F.mul_ne_zero hM (hN hcd), hcd, M2.ext' ?_ ?_ ?_ ?_⟩
    · exact Shell.Frame.RE.sound (Shell.Frame.look [M.a, M.b, M.c, M.d, ν])
        (.mul (.add (.mul (.var 3) (.var 3)) (.neg (.mul (.var 4) (.mul (.var 2) (.var 2))))) (.var 0))
        (.add (.mul (.add (.mul (.var 0) (.var 3)) (.neg (.mul (.var 1) (.var 2)))) (.var 3)) (.mul (.add (.mul (.var 1) (.var 3)) (.neg (.mul (.var 4) (.mul (.var 0) (.var 2))))) (.var 2))) (by decide +kernel)
    · exact Shell.Frame.RE.sound (Shell.Frame.look [M.a, M.b, M.c, M.d, ν])
        (.mul (.add (.mul (.var 3) (.var 3)) (.neg (.mul (.var 4) (.mul (.var 2) (.var 2))))) (.var 1))
        (.add (.mul (.add (.mul (.var 0) (.var 3)) (.neg (.mul (.var 1) (.var 2)))) (.mul (.var 4) (.var 2))) (.mul (.add (.mul (.var 1) (.var 3)) (.neg (.mul (.var 4) (.mul (.var 0) (.var 2))))) (.var 3))) (by decide +kernel)
    · exact Shell.Frame.RE.sound (Shell.Frame.look [M.a, M.b, M.c, M.d, ν])
        (.mul (.add (.mul (.var 3) (.var 3)) (.neg (.mul (.var 4) (.mul (.var 2) (.var 2))))) (.var 2))
        (.add (.mul .zero (.var 3)) (.mul (.add (.mul (.var 3) (.var 3)) (.neg (.mul (.var 4) (.mul (.var 2) (.var 2))))) (.var 2))) (by decide +kernel)
    · exact Shell.Frame.RE.sound (Shell.Frame.look [M.a, M.b, M.c, M.d, ν])
        (.mul (.add (.mul (.var 3) (.var 3)) (.neg (.mul (.var 4) (.mul (.var 2) (.var 2))))) (.var 3))
        (.add (.mul .zero (.mul (.var 4) (.var 2))) (.mul (.add (.mul (.var 3) (.var 3)) (.neg (.mul (.var 4) (.mul (.var 2) (.var 2))))) (.var 3))) (by decide +kernel)
  · -- (4) uniqueness: the torus class from the bottom row, the chart from the 2 × 2 system of determinant `N(α, β)`
    have ha : l * (a1 * α1 + b1 * β1) = a2 * α2 + b2 * β2 := congrArg M2.a h
    have hb : l * (a1 * (ν * β1) + b1 * α1) = a2 * (ν * β2) + b2 * α2 := congrArg M2.b h
    have hc : l * (0 * α1 + e1 * β1) = 0 * α2 + e2 * β2 := congrArg M2.c h
    have hd : l * (0 * (ν * β1) + e1 * α1) = 0 * (ν * β2) + e2 * α2 := congrArg M2.d h
    rw [zero_mul, zero_mul, zero_add, zero_add] at hc hd
    have hc' : e2 * β2 = l * (e1 * β1) := hc.symm
    have hd' : e2 * α2 = l * (e1 * α1) := hd.symm
    -- the torus class
    have t1 : e2 * (α1 * β2 + -(α2 * β1)) = α1 * (e2 * β2) + -(β1 * (e2 * α2)) := Shell.Frame.RE.sound (Shell.Frame.look [l, a1, b1, e1, α1, β1, a2, b2, e2, α2, β2, ν])
        (.mul (.var 8) (.add (.mul (.var 4) (.var 10)) (.neg (.mul (.var 9) (.var 5)))))
        (.add (.mul (.var 4) (.mul (.var 8) (.var 10))) (.neg (.mul (.var 5) (.mul (.var 8) (.var 9))))) (by decide +kernel)
    rw [hc', hd'] at t1
    have t2 : α1 * (l * (e1 * β1)) + -(β1 * (l * (e1 * α1))) = 0 := Shell.Frame.RE.sound (Shell.Frame.look [l, a1, b1, e1, α1, β1, a2, b2, e2, α2, β2, ν])
        (.add (.mul (.var 4) (.mul (.var 0) (.mul (.var 3) (.var 5)))) (.neg (.mul (.var 5) (.mul (.var 0) (.mul (.var 3) (.var 4))))))
        .zero (by decide +kernel)
    rw [t2] at t1
    have hT : α1 * β2 = α2 * β1 := eq_of_add_neg_eq_zero ((F.mul_eq_zero t1).resolve_left he2)
    -- the chart: X = e2 a1 − e1 a2, Y = e2 b1 − e1 b2 solve the system with matrix boost(α1, β1)
    have s1 : e2 * (l * (a1 * α1 + b1 * β1)) = a2 * (l * (e1 * α1)) + b2 * (l * (e1 * β1)) := by
      rw [ha, ← hd', ← hc']; exact Shell.Frame.RE.sound (Shell.Frame.look [l, a1, b1, e1, α1, β1, a2, b2, e2, α2, β2, ν])
        (.mul (.var 8) (.add (.mul (.var 6) (.var 9)) (.mul (.var 7) (.var 10))))
        (.add (.mul (.var 6) (.mul (.var 8) (.var 9))) (.mul (.var 7) (.mul (.var 8) (.var 10)))) (by decide +kernel)
    have s2 : e2 * (l * (a1 * (ν * β1) + b1 * α1)) = a2 * (ν * (l * (e1 * β1))) + b2 * (l * (e1 * α1)) := by
      rw [hb, ← hd', ← hc']; exact Shell.Frame.RE.sound (Shell.Frame.look [l, a1, b1, e1, α1, β1, a2, b2, e2, α2, β2, ν])
        (.mul (.var 8) (.add (.mul (.var 6) (.mul (.var 11) (.var 10))) (.mul (.var 7) (.var 9))))
        (.add (.mul (.var 6) (.mul (.var 11) (.mul (.var 8) (.var 10)))) (.mul (.var 7) (.mul (.var 8) (.var 9)))) (by decide +kernel)
    have u1 : l * ((e2 * a1 + -(e1 * a2)) * α1 + (e2 * b1 + -(e1 * b2)) * β1) =
        e2 * (l * (a1 * α1 + b1 * β1)) + -(a2 * (l * (e1 * α1)) + b2 * (l * (e1 * β1))) := Shell.Frame.RE.sound (Shell.Frame.look [l, a1, b1, e1, α1, β1, a2, b2, e2, α2, β2, ν])
        (.mul (.var 0) (.add (.mul (.add (.mul (.var 8) (.var 1)) (.neg (.mul (.var 3) (.var 6)))) (.var 4)) (.mul (.add (.mul (.var 8) (.var 2)) (.neg (.mul (.var 3) (.var 7)))) (.var 5))))
        (.add (.mul (.var 8) (.mul (.var 0) (.add (.mul (.var 1) (.var 4)) (.mul (.var 2) (.var 5))))) (.neg (.add (.mul (.var 6) (.mul (.var 0) (.mul (.var 3) (.var 4)))) (.mul (.var 7) (.mul (.var 0) (.mul (.var 3) (.var 5))))))) (by decide +kernel)
    have u2 : l * ((e2 * a1 + -(e1 * a2)) * (ν * β1) + (e2 * b1 + -(e1 * b2)) * α1) =
        e2 * (l * (a1 * (ν * β1) + b1 * α1)) + -(a2 * (ν * (l * (e1 * β1))) + b2 * (l * (e1 * α1))) := Shell.Frame.RE.sound (Shell.Frame.look [l, a1, b1, e1, α1, β1, a2, b2, e2, α2, β2, ν])
        (.mul (.var 0) (.add (.mul (.add (.mul (.var 8) (.var 1)) (.neg (.mul (.var 3) (.var 6)))) (.mul (.var 11) (.var 5))) (.mul (.add (.mul (.var 8) (.var 2)) (.neg (.mul (.var 3) (.var 7)))) (.var 4))))
        (.add (.mul (.var 8) (.mul (.var 0) (.add (.mul (.var 1) (.mul (.var 11) (.var 5))) (.mul (.var 2) (.var 4))))) (.neg (.add (.mul (.var 6) (.mul (.var 11) (.mul (.var 0) (.mul (.var 3) (.var 5))))) (.mul (.var 7) (.mul (.var 0) (.mul (.var 3) (.var 4))))))) (by decide +kernel)
    rw [s1, add_neg] at u1
    rw [s2, add_neg] at u2
    have v1 := (F.mul_eq_zero u1).resolve_left hl
    have v2 := (F.mul_eq_zero u2).resolve_left hl
    have w1 : (e2 * a1 + -(e1 * a2)) * (α1 * α1 + -(ν * (β1 * β1))) =
        α1 * ((e2 * a1 + -(e1 * a2)) * α1 + (e2 * b1 + -(e1 * b2)) * β1) +
        -(β1 * ((e2 * a1 + -(e1 * a2)) * (ν * β1) + (e2 * b1 + -(e1 * b2)) * α1)) := Shell.Frame.RE.sound (Shell.Frame.look [l, a1, b1, e1, α1, β1, a2, b2, e2, α2, β2, ν])
        (.mul (.add (.mul (.var 8) (.var 1)) (.neg (.mul (.var 3) (.var 6)))) (.add (.mul (.var 4) (.var 4)) (.neg (.mul (.var 11) (.mul (.var 5) (.var 5))))))
        (.add (.mul (.var 4) (.add (.mul (.add (.mul (.var 8) (.var 1)) (.neg (.mul (.var 3) (.var 6)))) (.var 4)) (.mul (.add (.mul (.var 8) (.var 2)) (.neg (.mul (.var 3) (.var 7)))) (.var 5)))) (.neg (.mul (.var 5) (.add (.mul (.add (.mul (.var 8) (.var 1)) (.neg (.mul (.var 3) (.var 6)))) (.mul (.var 11) (.var 5))) (.mul (.add (.mul (.var 8) (.var 2)) (.neg (.mul (.var 3) (.var 7)))) (.var 4)))))) (by decide +kernel)
    have w2 : (e2 * b1 + -(e1 * b2)) * (α1 * α1 + -(ν * (β1 * β1))) =
        α1 * ((e2 * a1 + -(e1 * a2)) * (ν * β1) + (e2 * b1 + -(e1 * b2)) * α1) +
        -(ν * β1 * ((e2 * a1 + -(e1 * a2)) * α1 + (e2 * b1 + -(e1 * b2)) * β1)) := Shell.Frame.RE.sound (Shell.Frame.look [l, a1, b1, e1, α1, β1, a2, b2, e2, α2, β2, ν])
        (.mul (.add (.mul (.var 8) (.var 2)) (.neg (.mul (.var 3) (.var 7)))) (.add (.mul (.var 4) (.var 4)) (.neg (.mul (.var 11) (.mul (.var 5) (.var 5))))))
        (.add (.mul (.var 4) (.add (.mul (.add (.mul (.var 8) (.var 1)) (.neg (.mul (.var 3) (.var 6)))) (.mul (.var 11) (.var 5))) (.mul (.add (.mul (.var 8) (.var 2)) (.neg (.mul (.var 3) (.var 7)))) (.var 4)))) (.neg (.mul (.mul (.var 11) (.var 5)) (.add (.mul (.add (.mul (.var 8) (.var 1)) (.neg (.mul (.var 3) (.var 6)))) (.var 4)) (.mul (.add (.mul (.var 8) (.var 2)) (.neg (.mul (.var 3) (.var 7)))) (.var 5)))))) (by decide +kernel)
    rw [v1, v2, mul_zero, mul_zero, neg_zero, add_zero] at w1
    rw [v1, v2, mul_zero, mul_zero, neg_zero, add_zero] at w2
    exact ⟨hT, eq_of_add_neg_eq_zero ((F.mul_eq_zero w1).resolve_right (hN hαβ)),
      eq_of_add_neg_eq_zero ((F.mul_eq_zero w2).resolve_right (hN hαβ))⟩
  · -- (5) the boost classes are the points of `ℙ¹`
    constructor
    · intro ⟨μ, _, h⟩
      have hα : α' = μ * α := congrArg M2.a h
      have hβ : β' = μ * β := congrArg M2.c h
      rw [hα, hβ, mul_left_comm, mul_assoc]
    · intro e
      match Shell.instDecidableEq α 0 with
      | .isFalse hα =>
        obtain ⟨s, hs⟩ := F.exists_inv hα
        have hb' : β' = α' * s * β :=
          calc β' = β' * (α * s) := by rw [hs, mul_one]
            _ = (α * β') * s := by rw [mul_left_comm, ← mul_assoc]
            _ = (α' * β) * s := by rw [e]
            _ = α' * s * β := by rw [mul_assoc, mul_comm β s, ← mul_assoc]
        have hμ : α' * s ≠ 0 := fun h0 => by
          have hα' : α' = 0 := by rw [← mul_one α', ← hs, mul_left_comm, h0, mul_zero]
          have hβ' : β' = 0 := by rw [hb', h0, zero_mul]
          exact h2.elim (fun h => h hα') (fun h => h hβ')
        refine ⟨α' * s, hμ, M2.ext' ?_ ?_ ?_ ?_⟩
        · show α' = α' * s * α; rw [mul_assoc, mul_comm s, hs, mul_one]
        · show ν * β' = α' * s * (ν * β); rw [hb', mul_left_comm]
        · show β' = α' * s * β; exact hb'
        · show α' = α' * s * α; rw [mul_assoc, mul_comm s, hs, mul_one]
      | .isTrue hα =>
        have hβ : β ≠ 0 := h1.resolve_left (fun h => h hα)
        have hα' : α' = 0 := by
          have : α' * β = 0 := by rw [← e, hα, zero_mul]
          exact (F.mul_eq_zero this).resolve_right hβ
        have hβ' : β' ≠ 0 := h2.resolve_left (fun h => h hα')
        obtain ⟨s, hs⟩ := F.exists_inv hβ
        refine ⟨β' * s, F.mul_ne_zero hβ' (fun h0 => F.one_ne_zero (by rw [← hs, h0, mul_zero])), M2.ext' ?_ ?_ ?_ ?_⟩
        · show α' = β' * s * α; rw [hα, hα', mul_zero]
        · show ν * β' = β' * s * (ν * β); rw [mul_left_comm, mul_assoc, mul_comm s, hs, mul_one]
        · show β' = β' * s * β; rw [mul_assoc, mul_comm s, hs, mul_one]
        · show α' = β' * s * α; rw [hα, hα', mul_zero]
  · -- (7) the spin cover
    refine ⟨M2.ext' rfl (mul_zero ν) rfl rfl, by rw [mul_zero, mul_zero, neg_zero, add_zero, neg_mul_neg, one_mul],
      by rw [neg_mul_neg, one_mul], fun α β a b e h hn => ?_, fun M N => M2.ext' ?_ ?_ ?_ ?_⟩
    · have hβ : β = 0 := congrArg M2.c h
      refine ⟨hβ, F.sq_eq_one ?_⟩
      rw [hβ, mul_zero, mul_zero, neg_zero, add_zero] at hn; exact hn
    · exact Shell.Frame.RE.sound (Shell.Frame.look [M.a, M.b, M.c, M.d, N.a, N.b, N.c, N.d])
        (.add (.mul (.mul (.neg .one) (.var 0)) (.mul (.neg .one) (.var 4))) (.mul (.mul (.neg .one) (.var 1)) (.mul (.neg .one) (.var 6))))
        (.add (.mul (.var 0) (.var 4)) (.mul (.var 1) (.var 6))) (by decide +kernel)
    · exact Shell.Frame.RE.sound (Shell.Frame.look [M.a, M.b, M.c, M.d, N.a, N.b, N.c, N.d])
        (.add (.mul (.mul (.neg .one) (.var 0)) (.mul (.neg .one) (.var 5))) (.mul (.mul (.neg .one) (.var 1)) (.mul (.neg .one) (.var 7))))
        (.add (.mul (.var 0) (.var 5)) (.mul (.var 1) (.var 7))) (by decide +kernel)
    · exact Shell.Frame.RE.sound (Shell.Frame.look [M.a, M.b, M.c, M.d, N.a, N.b, N.c, N.d])
        (.add (.mul (.mul (.neg .one) (.var 2)) (.mul (.neg .one) (.var 4))) (.mul (.mul (.neg .one) (.var 3)) (.mul (.neg .one) (.var 6))))
        (.add (.mul (.var 2) (.var 4)) (.mul (.var 3) (.var 6))) (by decide +kernel)
    · exact Shell.Frame.RE.sound (Shell.Frame.look [M.a, M.b, M.c, M.d, N.a, N.b, N.c, N.d])
        (.add (.mul (.mul (.neg .one) (.var 2)) (.mul (.neg .one) (.var 5))) (.mul (.mul (.neg .one) (.var 3)) (.mul (.neg .one) (.var 7))))
        (.add (.mul (.var 2) (.var 5)) (.mul (.var 3) (.var 7))) (by decide +kernel)

end Frame
end Shell
end FRC
