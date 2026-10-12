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
theorem frame_count :
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
theorem ext'_a {M N : M2 p} (h : M = N) : M.a = N.a := by cases h; rfl
theorem ext'_b {M N : M2 p} (h : M = N) : M.b = N.b := by cases h; rfl
theorem ext'_c {M N : M2 p} (h : M = N) : M.c = N.c := by cases h; rfl
theorem ext'_d {M N : M2 p} (h : M = N) : M.d = N.d := by cases h; rfl

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

/-- The field laws of a shell, as the Hopf section and the frame triple use them; a frame gives them (`Frame.fld`), so
does primality (`Prime.fld`, `Theme/Hopf.lean`): the theorems below hold on every prime shell (38:A9). -/
structure Fld (p : Nat) [Pos p] : Prop where
  one_ne_zero : (1 : Shell p) ≠ 0
  exists_inv : ∀ {x : Shell p}, x ≠ 0 → ∃ y, x * y = 1
  mul_eq_zero : ∀ {a b : Shell p}, a * b = 0 → a = 0 ∨ b = 0
  mul_ne_zero : ∀ {a b : Shell p}, a ≠ 0 → b ≠ 0 → a * b ≠ 0
  mul_left_cancel : ∀ {a b c : Shell p}, a ≠ 0 → a * b = a * c → b = c
  sq_eq_one : ∀ {x : Shell p}, x * x = 1 → x = 1 ∨ x = -1

/-- A frame has the field laws. -/
theorem fld (F : Frame p κ g) : Fld p :=
  ⟨F.one_ne_zero, fun hx => F.exists_inv hx, fun h => F.mul_eq_zero h, fun ha hb => F.mul_ne_zero ha hb,
   fun ha h => F.mul_left_cancel ha h, fun h => F.sq_eq_one h⟩

/-- 38:A9, 00:C19 — on a field-law shell, `x² − ν y² ≠ 0` for `(x, y) ≠ 0` when `ν` is a nonsquare. -/
theorem Fld.norm_ne_zero (K : Fld p) {ν : Shell p} (hν : ¬ ∃ y : Shell p, y * y = ν) {x y : Shell p}
    (hxy : x ≠ 0 ∨ y ≠ 0) : x * x + -(ν * (y * y)) ≠ 0 := fun h => by
  have e := eq_of_add_neg_eq_zero h
  match Shell.instDecidableEq y 0 with
  | .isTrue hy =>
    rw [hy, mul_zero, mul_zero] at e
    exact hxy.elim (fun hx => hx (match K.mul_eq_zero e with | .inl h => h | .inr h => h)) (fun h => h hy)
  | .isFalse hy =>
    obtain ⟨s, hs⟩ := K.exists_inv hy
    exact hν ⟨x * s, by rw [mul_mul_mul_comm, e, mul_assoc, ← mul_mul_mul_comm, hs, mul_one, mul_one]⟩

/-- 38:A7, 38:A9 — **C19 (p00039), the Hopf section.** In `PGL₂(𝔽_p)` on a frame, `ν` a nonsquare:
(1) a boost that is not scalar fixes no point of `ℙ¹`; (2) a boost in the Borel subgroup is scalar: `T ∩ B = 1`;
(3) every invertible matrix factors as (cone chart) × (boost) up to a scalar, (4) uniquely up to scalars — the cone
chart is a global section of `G → G/T`; (5) the boost classes are the points of `ℙ¹` (`p + 1` per fibre) and (6) the
cone charts number `p (p − 1)`; (7) on the spin cover `SL₂` the sign `−I` is both a boost and a chart, `B ∩ T = {±I}`
there, and `b t = (−b)(−t)`: the section obstructs at `−1`. -/
theorem Fld.hopf_section (K : Fld p) {ν : Shell p} (hν : ¬ ∃ y : Shell p, y * y = ν) :
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
  have hN : ∀ {x y : Shell p}, (x ≠ 0 ∨ y ≠ 0) → x * x + -(ν * (y * y)) ≠ 0 := fun hxy => K.norm_ne_zero hν hxy
  refine ⟨fun α β x y hβ hxy hP => ?_, fun α β a b e l h => ?_, fun M hM => ?_,
    fun l a1 b1 e1 α1 β1 a2 b2 e2 α2 β2 hl he2 hαβ h => ?_, fun α β α' β' h1 h2 => ?_, frame_count, ?_⟩
  · -- (1) a fixed point forces `β (ν y² − x²) = 0`
    have e : (α * x + ν * β * y) * y + -(x * (β * x + α * y)) = β * (ν * (y * y) + -(x * x)) :=
      Shell.Frame.RE.sound (Shell.Frame.look [α, β, ν, x, y])
        (.add (.mul (.add (.mul (.var 0) (.var 3)) (.mul (.mul (.var 2) (.var 1)) (.var 4))) (.var 4)) (.neg (.mul (.var 3) (.add (.mul (.var 1) (.var 3)) (.mul (.var 0) (.var 4))))))
        (.mul (.var 1) (.add (.mul (.var 2) (.mul (.var 4) (.var 4))) (.neg (.mul (.var 3) (.var 3))))) (by decide +kernel)
    have hP' : (α * x + ν * β * y) * y = x * (β * x + α * y) := hP
    rw [hP', add_neg] at e
    match K.mul_eq_zero e.symm with
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
      M.d, M.c, hN hcd, K.mul_ne_zero hM (hN hcd), hcd, M2.ext' ?_ ?_ ?_ ?_⟩
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
    have hT : α1 * β2 = α2 * β1 := eq_of_add_neg_eq_zero ((K.mul_eq_zero t1).resolve_left he2)
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
    have v1 := (K.mul_eq_zero u1).resolve_left hl
    have v2 := (K.mul_eq_zero u2).resolve_left hl
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
    exact ⟨hT, eq_of_add_neg_eq_zero ((K.mul_eq_zero w1).resolve_right (hN hαβ)),
      eq_of_add_neg_eq_zero ((K.mul_eq_zero w2).resolve_right (hN hαβ))⟩
  · -- (5) the boost classes are the points of `ℙ¹`
    constructor
    · intro ⟨μ, _, h⟩
      have hα : α' = μ * α := congrArg M2.a h
      have hβ : β' = μ * β := congrArg M2.c h
      rw [hα, hβ, mul_left_comm, mul_assoc]
    · intro e
      match Shell.instDecidableEq α 0 with
      | .isFalse hα =>
        obtain ⟨s, hs⟩ := K.exists_inv hα
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
          exact (K.mul_eq_zero this).resolve_right hβ
        have hβ' : β' ≠ 0 := h2.resolve_left (fun h => h hα')
        obtain ⟨s, hs⟩ := K.exists_inv hβ
        refine ⟨β' * s, K.mul_ne_zero hβ' (fun h0 => K.one_ne_zero (by rw [← hs, h0, mul_zero])), M2.ext' ?_ ?_ ?_ ?_⟩
        · show α' = β' * s * α; rw [hα, hα', mul_zero]
        · show ν * β' = β' * s * (ν * β); rw [mul_left_comm, mul_assoc, mul_comm s, hs, mul_one]
        · show β' = β' * s * β; rw [mul_assoc, mul_comm s, hs, mul_one]
        · show α' = β' * s * α; rw [hα, hα', mul_zero]
  · -- (7) the spin cover
    refine ⟨M2.ext' rfl (mul_zero ν) rfl rfl, by rw [mul_zero, mul_zero, neg_zero, add_zero, neg_mul_neg, one_mul],
      by rw [neg_mul_neg, one_mul], fun α β a b e h hn => ?_, fun M N => M2.ext' ?_ ?_ ?_ ?_⟩
    · have hβ : β = 0 := congrArg M2.c h
      refine ⟨hβ, K.sq_eq_one ?_⟩
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

/-- 38:A7, 38:A9 — on a frame (`Frame.fld`): `Fld.hopf_section`. -/
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
      ∀ M N : M2 p, (M2.smul (-1) M).mul (M2.smul (-1) N) = M.mul N) :=
  F.fld.hopf_section hν

/-- 38:A7, 38:A9, 38:X4, 00:C19 — the fibration counted by representatives. Every Borel class (an upper-triangular `[[a, b], [0, e]]`,
`a e ≠ 0`, up to a nonzero scalar) has exactly one representative `[[i, j], [0, 1]]` with `i, j < p` and `i ≠ 0`, and
these number `p (p − 1)`. Every boost class has exactly one representative among `[[i, ν], [1, i]]` (`i < p`) and the
identity `[[1, 0], [0, 1]]`, and these number `p + 1`. With the factorisation (`hopf_section`), the frames are
`p (p − 1)` fibres of `p + 1`. -/
theorem Fld.hopf_counts (K : Fld p) (ν : Shell p) :
    (∀ a b e : Shell p, a * e ≠ 0 → ∃ i j : Nat, i < p ∧ j < p ∧ i ≠ 0 ∧
      ∃ l : Shell p, l ≠ 0 ∧ M2.smul l (borel a b e) = borel (ofNat i) (ofNat j) 1) ∧
    (∀ i j i' j' : Nat, i < p → j < p → i' < p → j' < p → ∀ l : Shell p,
      M2.smul l (borel (ofNat i) (ofNat j) 1) = borel (ofNat i') (ofNat j') 1 → i = i' ∧ j = j') ∧
    natCount (fun _ => True) p * natCount (fun b => b ≠ 0) p = p * (p - 1) ∧
    (∀ α β : Shell p, (α ≠ 0 ∨ β ≠ 0) →
      (∃ i : Nat, i < p ∧ ∃ μ : Shell p, μ ≠ 0 ∧ M2.smul μ (boost ν α β) = boost ν (ofNat i) 1) ∨
      (∃ μ : Shell p, μ ≠ 0 ∧ M2.smul μ (boost ν α β) = boost ν 1 0)) ∧
    (∀ i i' : Nat, i < p → i' < p → ∀ μ : Shell p, M2.smul μ (boost ν (ofNat i) 1) = boost ν (ofNat i') 1 → i = i') ∧
    (∀ i : Nat, ∀ μ : Shell p, μ ≠ 0 → M2.smul μ (boost ν (ofNat i) 1) ≠ boost ν 1 0) ∧
    (∀ i : Nat, ∀ μ : Shell p, M2.smul μ (boost ν 1 0) ≠ boost ν (ofNat i) 1) ∧
    natCount (fun _ => True) p + 1 = p + 1 := by
  have hT : ∀ n, natCount (fun _ => True) n = n := fun n => by
    induction n with
    | zero => rfl
    | succ n ih => show natCount (fun _ => True) n + (if True then 1 else 0) = n + 1; rw [ih, ite_eq_left trivial]
  have ofNat_inj : ∀ {i j : Nat}, i < p → j < p → (ofNat i : Shell p) = ofNat j → i = j := fun hi hj h => by
    have := val_injective h
    rw [val_ofNat, val_ofNat, FRC.Nat.mod_eq_of_lt hi, FRC.Nat.mod_eq_of_lt hj] at this
    exact this
  have hval : ∀ x : Shell p, x ≠ 0 → x.val ≠ 0 := fun x hx h0 => hx (by rw [← ofNat_val x, h0]; rfl)
  have hl1 : ∀ l : Shell p, l * 1 = 1 → l = 1 := fun l h => by rw [mul_one] at h; exact h
  -- the boost scaled: `μ · [[α, νβ], [β, α]] = [[μα, ν(μβ)], [μβ, μα]]`
  have hsb : ∀ μ α β : Shell p, M2.smul μ (boost ν α β) = boost ν (μ * α) (μ * β) := fun μ α β =>
    M2.ext' rfl (by show μ * (ν * β) = ν * (μ * β); rw [mul_left_comm]) rfl rfl
  refine ⟨fun a b e hae => ?_, fun i j i' j' hi hj hi' hj' l h => ?_, frame_count, fun α β hαβ => ?_,
    fun i i' hi hi' μ h => ?_, fun i μ hμ h => ?_, fun i μ h => ?_, by rw [hT]⟩
  · have he : e ≠ 0 := fun h0 => hae (by rw [h0, mul_zero])
    have ha : a ≠ 0 := fun h0 => hae (by rw [h0, zero_mul])
    obtain ⟨y, hy⟩ := K.exists_inv he
    have hy0 : y ≠ 0 := fun h0 => K.one_ne_zero (by rw [← hy, h0, mul_zero])
    refine ⟨(y * a).val, (y * b).val, (y * a).lt, (y * b).lt, hval _ (K.mul_ne_zero hy0 ha), y, hy0, ?_⟩
    rw [ofNat_val, ofNat_val]
    exact M2.ext' rfl rfl (mul_zero y) (by show y * e = 1; rw [mul_comm]; exact hy)
  · have hl : l = 1 := hl1 l (M2.ext'_d h)
    rw [hl] at h
    have ha : 1 * ofNat i = (ofNat i' : Shell p) := M2.ext'_a h
    have hb : 1 * ofNat j = (ofNat j' : Shell p) := M2.ext'_b h
    rw [one_mul] at ha hb
    exact ⟨ofNat_inj hi hi' ha, ofNat_inj hj hj' hb⟩
  · match Shell.instDecidableEq β 0 with
    | .isFalse hβ =>
      obtain ⟨y, hy⟩ := K.exists_inv hβ
      have hy0 : y ≠ 0 := fun h0 => K.one_ne_zero (by rw [← hy, h0, mul_zero])
      refine .inl ⟨(y * α).val, (y * α).lt, y, hy0, ?_⟩
      rw [hsb, ofNat_val, mul_comm y β, hy]
    | .isTrue hβ =>
      have hα : α ≠ 0 := match hαβ with | .inl h => h | .inr h => absurd hβ h
      obtain ⟨y, hy⟩ := K.exists_inv hα
      have hy0 : y ≠ 0 := fun h0 => K.one_ne_zero (by rw [← hy, h0, mul_zero])
      refine .inr ⟨y, hy0, ?_⟩
      rw [hsb, hβ, mul_zero, mul_comm y α, hy]
  · rw [hsb] at h
    have hμ : μ = 1 := hl1 μ (M2.ext'_c h)
    rw [hμ, one_mul] at h
    exact ofNat_inj hi hi' (M2.ext'_a h)
  · rw [hsb] at h
    exact hμ (by have := M2.ext'_c h; rwa [mul_one] at this)
  · rw [hsb, mul_zero] at h
    exact K.one_ne_zero (M2.ext'_c h).symm


/-- 38:A7, 38:A9, 38:X4, 00:C19 — on a frame (`Frame.fld`): `Fld.hopf_counts`. -/
theorem hopf_counts (F : Frame p κ g) (ν : Shell p) :
    (∀ a b e : Shell p, a * e ≠ 0 → ∃ i j : Nat, i < p ∧ j < p ∧ i ≠ 0 ∧
      ∃ l : Shell p, l ≠ 0 ∧ M2.smul l (borel a b e) = borel (ofNat i) (ofNat j) 1) ∧
    (∀ i j i' j' : Nat, i < p → j < p → i' < p → j' < p → ∀ l : Shell p,
      M2.smul l (borel (ofNat i) (ofNat j) 1) = borel (ofNat i') (ofNat j') 1 → i = i' ∧ j = j') ∧
    natCount (fun _ => True) p * natCount (fun b => b ≠ 0) p = p * (p - 1) ∧
    (∀ α β : Shell p, (α ≠ 0 ∨ β ≠ 0) →
      (∃ i : Nat, i < p ∧ ∃ μ : Shell p, μ ≠ 0 ∧ M2.smul μ (boost ν α β) = boost ν (ofNat i) 1) ∨
      (∃ μ : Shell p, μ ≠ 0 ∧ M2.smul μ (boost ν α β) = boost ν 1 0)) ∧
    (∀ i i' : Nat, i < p → i' < p → ∀ μ : Shell p, M2.smul μ (boost ν (ofNat i) 1) = boost ν (ofNat i') 1 → i = i') ∧
    (∀ i : Nat, ∀ μ : Shell p, μ ≠ 0 → M2.smul μ (boost ν (ofNat i) 1) ≠ boost ν 1 0) ∧
    (∀ i : Nat, ∀ μ : Shell p, M2.smul μ (boost ν 1 0) ≠ boost ν (ofNat i) 1) ∧
    natCount (fun _ => True) p + 1 = p + 1 :=
  F.fld.hopf_counts ν

/-! ## 38:A9, 38:X4, 38:B6: the frame triple and the split fibration (12 October 2026)

The adjugate `adj M = [[d, −b], [−c, a]]` with `M · adj M = adj M · M = det M · I`; the frame triple
`G ≅ ℙ¹ × B`: every invertible `M` factors as (boost carrying the horizon to its direction `M·[1 : 0]`) × (cone chart),
uniquely up to scalars (`frame_triple`); the split fibration by the unit `i = diag(r, −r)`, `r = g^κ`, `r² = −1`: the
centraliser of `i` is the diagonal torus inside the Borel, `i` is not scalar, the circle `x² + y² = 1` is the torus's
norm-one part, the conjugates of `i` fill the trace-zero quadric `a² + bc = −1` and every point of it is reached, and
the quadric is the unit sphere `x² + y² + z² = 1` under a linear change of chart (`unit_split`); the sphere's
`p(p + 1)` points are the gravity theme's `Grav.sphere_area_rung`, the circle's `p − 1` its `conic_count`. -/

namespace M2

/-- The adjugate `[[d, −b], [−c, a]]`. -/
def adj (M : M2 p) : M2 p := ⟨M.d, -M.b, -M.c, M.a⟩

/-- `M · adj M = det M · I`. -/
theorem mul_adj (M : M2 p) : M.mul M.adj = ⟨M.det, 0, 0, M.det⟩ :=
  ext' (Shell.Frame.RE.sound (Shell.Frame.look [M.a, M.b, M.c, M.d]) (.add (.mul (.var 0) (.var 3)) (.mul (.var 1) (.neg (.var 2)))) (.add (.mul (.var 0) (.var 3)) (.neg (.mul (.var 1) (.var 2)))) (by decide +kernel)) (Shell.Frame.RE.sound (Shell.Frame.look [M.a, M.b, M.c, M.d]) (.add (.mul (.var 0) (.neg (.var 1))) (.mul (.var 1) (.var 0))) .zero (by decide +kernel)) (Shell.Frame.RE.sound (Shell.Frame.look [M.a, M.b, M.c, M.d]) (.add (.mul (.var 2) (.var 3)) (.mul (.var 3) (.neg (.var 2)))) .zero (by decide +kernel)) (Shell.Frame.RE.sound (Shell.Frame.look [M.a, M.b, M.c, M.d]) (.add (.mul (.var 2) (.neg (.var 1))) (.mul (.var 3) (.var 0))) (.add (.mul (.var 0) (.var 3)) (.neg (.mul (.var 1) (.var 2)))) (by decide +kernel))

/-- `adj M · M = det M · I`. -/
theorem adj_mul (M : M2 p) : M.adj.mul M = ⟨M.det, 0, 0, M.det⟩ :=
  ext' (Shell.Frame.RE.sound (Shell.Frame.look [M.a, M.b, M.c, M.d]) (.add (.mul (.var 3) (.var 0)) (.mul (.neg (.var 1)) (.var 2))) (.add (.mul (.var 0) (.var 3)) (.neg (.mul (.var 1) (.var 2)))) (by decide +kernel)) (Shell.Frame.RE.sound (Shell.Frame.look [M.a, M.b, M.c, M.d]) (.add (.mul (.var 3) (.var 1)) (.mul (.neg (.var 1)) (.var 3))) .zero (by decide +kernel)) (Shell.Frame.RE.sound (Shell.Frame.look [M.a, M.b, M.c, M.d]) (.add (.mul (.neg (.var 2)) (.var 0)) (.mul (.var 0) (.var 2))) .zero (by decide +kernel)) (Shell.Frame.RE.sound (Shell.Frame.look [M.a, M.b, M.c, M.d]) (.add (.mul (.neg (.var 2)) (.var 1)) (.mul (.var 0) (.var 3))) (.add (.mul (.var 0) (.var 3)) (.neg (.mul (.var 1) (.var 2)))) (by decide +kernel))

theorem mul_assoc' (M N K : M2 p) : (M.mul N).mul K = M.mul (N.mul K) :=
  ext' (Shell.Frame.RE.sound (Shell.Frame.look [M.a, M.b, M.c, M.d, N.a, N.b, N.c, N.d, K.a, K.b, K.c, K.d]) (.add (.mul (.add (.mul (.var 0) (.var 4)) (.mul (.var 1) (.var 6))) (.var 8)) (.mul (.add (.mul (.var 0) (.var 5)) (.mul (.var 1) (.var 7))) (.var 10))) (.add (.mul (.var 0) (.add (.mul (.var 4) (.var 8)) (.mul (.var 5) (.var 10)))) (.mul (.var 1) (.add (.mul (.var 6) (.var 8)) (.mul (.var 7) (.var 10))))) (by decide +kernel)) (Shell.Frame.RE.sound (Shell.Frame.look [M.a, M.b, M.c, M.d, N.a, N.b, N.c, N.d, K.a, K.b, K.c, K.d]) (.add (.mul (.add (.mul (.var 0) (.var 4)) (.mul (.var 1) (.var 6))) (.var 9)) (.mul (.add (.mul (.var 0) (.var 5)) (.mul (.var 1) (.var 7))) (.var 11))) (.add (.mul (.var 0) (.add (.mul (.var 4) (.var 9)) (.mul (.var 5) (.var 11)))) (.mul (.var 1) (.add (.mul (.var 6) (.var 9)) (.mul (.var 7) (.var 11))))) (by decide +kernel)) (Shell.Frame.RE.sound (Shell.Frame.look [M.a, M.b, M.c, M.d, N.a, N.b, N.c, N.d, K.a, K.b, K.c, K.d]) (.add (.mul (.add (.mul (.var 2) (.var 4)) (.mul (.var 3) (.var 6))) (.var 8)) (.mul (.add (.mul (.var 2) (.var 5)) (.mul (.var 3) (.var 7))) (.var 10))) (.add (.mul (.var 2) (.add (.mul (.var 4) (.var 8)) (.mul (.var 5) (.var 10)))) (.mul (.var 3) (.add (.mul (.var 6) (.var 8)) (.mul (.var 7) (.var 10))))) (by decide +kernel)) (Shell.Frame.RE.sound (Shell.Frame.look [M.a, M.b, M.c, M.d, N.a, N.b, N.c, N.d, K.a, K.b, K.c, K.d]) (.add (.mul (.add (.mul (.var 2) (.var 4)) (.mul (.var 3) (.var 6))) (.var 9)) (.mul (.add (.mul (.var 2) (.var 5)) (.mul (.var 3) (.var 7))) (.var 11))) (.add (.mul (.var 2) (.add (.mul (.var 4) (.var 9)) (.mul (.var 5) (.var 11)))) (.mul (.var 3) (.add (.mul (.var 6) (.var 9)) (.mul (.var 7) (.var 11))))) (by decide +kernel))

theorem smul_mul (l : Shell p) (M N : M2 p) : (smul l M).mul N = smul l (M.mul N) :=
  ext' (Shell.Frame.RE.sound (Shell.Frame.look [l, M.a, M.b, M.c, M.d, N.a, N.b, N.c, N.d]) (.add (.mul (.mul (.var 0) (.var 1)) (.var 5)) (.mul (.mul (.var 0) (.var 2)) (.var 7))) (.mul (.var 0) (.add (.mul (.var 1) (.var 5)) (.mul (.var 2) (.var 7)))) (by decide +kernel)) (Shell.Frame.RE.sound (Shell.Frame.look [l, M.a, M.b, M.c, M.d, N.a, N.b, N.c, N.d]) (.add (.mul (.mul (.var 0) (.var 1)) (.var 6)) (.mul (.mul (.var 0) (.var 2)) (.var 8))) (.mul (.var 0) (.add (.mul (.var 1) (.var 6)) (.mul (.var 2) (.var 8)))) (by decide +kernel)) (Shell.Frame.RE.sound (Shell.Frame.look [l, M.a, M.b, M.c, M.d, N.a, N.b, N.c, N.d]) (.add (.mul (.mul (.var 0) (.var 3)) (.var 5)) (.mul (.mul (.var 0) (.var 4)) (.var 7))) (.mul (.var 0) (.add (.mul (.var 3) (.var 5)) (.mul (.var 4) (.var 7)))) (by decide +kernel)) (Shell.Frame.RE.sound (Shell.Frame.look [l, M.a, M.b, M.c, M.d, N.a, N.b, N.c, N.d]) (.add (.mul (.mul (.var 0) (.var 3)) (.var 6)) (.mul (.mul (.var 0) (.var 4)) (.var 8))) (.mul (.var 0) (.add (.mul (.var 3) (.var 6)) (.mul (.var 4) (.var 8)))) (by decide +kernel))

theorem mul_smul (l : Shell p) (M N : M2 p) : M.mul (smul l N) = smul l (M.mul N) :=
  ext' (Shell.Frame.RE.sound (Shell.Frame.look [l, M.a, M.b, M.c, M.d, N.a, N.b, N.c, N.d]) (.add (.mul (.var 1) (.mul (.var 0) (.var 5))) (.mul (.var 2) (.mul (.var 0) (.var 7)))) (.mul (.var 0) (.add (.mul (.var 1) (.var 5)) (.mul (.var 2) (.var 7)))) (by decide +kernel)) (Shell.Frame.RE.sound (Shell.Frame.look [l, M.a, M.b, M.c, M.d, N.a, N.b, N.c, N.d]) (.add (.mul (.var 1) (.mul (.var 0) (.var 6))) (.mul (.var 2) (.mul (.var 0) (.var 8)))) (.mul (.var 0) (.add (.mul (.var 1) (.var 6)) (.mul (.var 2) (.var 8)))) (by decide +kernel)) (Shell.Frame.RE.sound (Shell.Frame.look [l, M.a, M.b, M.c, M.d, N.a, N.b, N.c, N.d]) (.add (.mul (.var 3) (.mul (.var 0) (.var 5))) (.mul (.var 4) (.mul (.var 0) (.var 7)))) (.mul (.var 0) (.add (.mul (.var 3) (.var 5)) (.mul (.var 4) (.var 7)))) (by decide +kernel)) (Shell.Frame.RE.sound (Shell.Frame.look [l, M.a, M.b, M.c, M.d, N.a, N.b, N.c, N.d]) (.add (.mul (.var 3) (.mul (.var 0) (.var 6))) (.mul (.var 4) (.mul (.var 0) (.var 8)))) (.mul (.var 0) (.add (.mul (.var 3) (.var 6)) (.mul (.var 4) (.var 8)))) (by decide +kernel))

/-- A scalar matrix acts as the scalar. -/
theorem diag_mul (l : Shell p) (M : M2 p) : (⟨l, 0, 0, l⟩ : M2 p).mul M = smul l M :=
  ext' (Shell.Frame.RE.sound (Shell.Frame.look [l, M.a, M.b, M.c, M.d]) (.add (.mul (.var 0) (.var 1)) (.mul .zero (.var 3))) (.mul (.var 0) (.var 1)) (by decide +kernel)) (Shell.Frame.RE.sound (Shell.Frame.look [l, M.a, M.b, M.c, M.d]) (.add (.mul (.var 0) (.var 2)) (.mul .zero (.var 4))) (.mul (.var 0) (.var 2)) (by decide +kernel)) (Shell.Frame.RE.sound (Shell.Frame.look [l, M.a, M.b, M.c, M.d]) (.add (.mul .zero (.var 1)) (.mul (.var 0) (.var 3))) (.mul (.var 0) (.var 3)) (by decide +kernel)) (Shell.Frame.RE.sound (Shell.Frame.look [l, M.a, M.b, M.c, M.d]) (.add (.mul .zero (.var 2)) (.mul (.var 0) (.var 4))) (.mul (.var 0) (.var 4)) (by decide +kernel))


/-- A scalar matrix on the right acts as the scalar. -/
theorem mul_diag (l : Shell p) (M : M2 p) : M.mul ⟨l, 0, 0, l⟩ = smul l M :=
  ext' (Shell.Frame.RE.sound (Shell.Frame.look [l, M.a, M.b, M.c, M.d]) (.add (.mul (.var 1) (.var 0)) (.mul (.var 2) .zero)) (.mul (.var 0) (.var 1)) (by decide +kernel)) (Shell.Frame.RE.sound (Shell.Frame.look [l, M.a, M.b, M.c, M.d]) (.add (.mul (.var 1) .zero) (.mul (.var 2) (.var 0))) (.mul (.var 0) (.var 2)) (by decide +kernel)) (Shell.Frame.RE.sound (Shell.Frame.look [l, M.a, M.b, M.c, M.d]) (.add (.mul (.var 3) (.var 0)) (.mul (.var 4) .zero)) (.mul (.var 0) (.var 3)) (by decide +kernel)) (Shell.Frame.RE.sound (Shell.Frame.look [l, M.a, M.b, M.c, M.d]) (.add (.mul (.var 3) .zero) (.mul (.var 4) (.var 0))) (.mul (.var 0) (.var 4)) (by decide +kernel))

/-- A nonzero scalar cancels. -/
theorem smul_cancel (K : Fld p) {l : Shell p} (hl : l ≠ 0) {A B : M2 p} (h : smul l A = smul l B) : A = B :=
  ext' (K.mul_left_cancel hl (ext'_a h)) (K.mul_left_cancel hl (ext'_b h)) (K.mul_left_cancel hl (ext'_c h))
    (K.mul_left_cancel hl (ext'_d h))

end M2

/-- 38:A9, 38:X4 — **the frame triple** (Theorem *The two fibrations and the frame triple*, the master's C22). On a
frame with `ν` a nonsquare: (1) an invertible `M` has a nonzero first column, its direction `M·[1 : 0] = [a : c]` is the
boost `[[a, νc], [c, a]]`'s direction, that boost has nonzero norm `N = a² − νc²`, and `N·M = boost(a, c) · borel(N, ab − νcd, det M)`:
every frame is (boost carrying the horizon to its direction) × (cone chart); (2) the cone charts fix the horizon;
(3) the factorisation is unique up to scalars — two factorisations of proportional frames have the same boost class and
the same chart class. With `hopf_counts` (`p + 1` boost classes, `p(p − 1)` charts) the frames number
`(p + 1)·p·(p − 1)`: one direction, one shell cell, one drive phase. -/
theorem Fld.frame_triple (K : Fld p) {ν : Shell p} (hν : ¬ ∃ y : Shell p, y * y = ν) :
    (∀ M : M2 p, M.det ≠ 0 → (M.a ≠ 0 ∨ M.c ≠ 0) ∧ M.act 1 0 = (M.a, M.c) ∧ (boost ν M.a M.c).act 1 0 = (M.a, M.c) ∧
      M.a * M.a + -(ν * (M.c * M.c)) ≠ 0 ∧
      M2.smul (M.a * M.a + -(ν * (M.c * M.c))) M =
        (boost ν M.a M.c).mul (borel (M.a * M.a + -(ν * (M.c * M.c))) (M.a * M.b + -(ν * (M.c * M.d))) M.det)) ∧
    (∀ a b e : Shell p, (borel a b e).act 1 0 = (a, 0)) ∧
    (∀ l α1 β1 a1 b1 e1 α2 β2 a2 b2 e2 : Shell p, l ≠ 0 → a1 ≠ 0 → a2 ≠ 0 → (α1 ≠ 0 ∨ β1 ≠ 0) →
      M2.smul l ((boost ν α1 β1).mul (borel a1 b1 e1)) = (boost ν α2 β2).mul (borel a2 b2 e2) →
      α1 * β2 = α2 * β1 ∧ e2 * a1 = e1 * a2 ∧ e2 * b1 = e1 * b2) := by
  have hN : ∀ {x y : Shell p}, (x ≠ 0 ∨ y ≠ 0) → x * x + -(ν * (y * y)) ≠ 0 := fun hxy => K.norm_ne_zero hν hxy
  refine ⟨fun M hM => ?_, fun a b e => ?_, fun l α1 β1 a1 b1 e1 α2 β2 a2 b2 e2 hl ha1 ha2 hαβ h => ?_⟩
  · have hac : M.a ≠ 0 ∨ M.c ≠ 0 := by
      match Shell.instDecidableEq M.a 0, Shell.instDecidableEq M.c 0 with
      | .isTrue ha, .isTrue hc =>
        exact absurd (show M.det = 0 by
          show M.a * M.d + -(M.b * M.c) = 0; rw [ha, hc, zero_mul, mul_zero, neg_zero, add_zero]) hM
      | .isFalse ha, _ => exact .inl ha
      | _, .isFalse hc => exact .inr hc
    refine ⟨hac, ?_, ?_, hN hac, M2.ext' ?_ ?_ ?_ ?_⟩
    · show (M.a * 1 + M.b * 0, M.c * 1 + M.d * 0) = (M.a, M.c)
      rw [mul_one, mul_zero, add_zero, mul_one, mul_zero, add_zero]
    · show (M.a * 1 + ν * M.c * 0, M.c * 1 + M.a * 0) = (M.a, M.c)
      rw [mul_one, mul_zero, add_zero, mul_one, mul_zero, add_zero]
    · exact Shell.Frame.RE.sound (Shell.Frame.look [M.a, M.b, M.c, M.d, ν]) (.mul (.add (.mul (.var 0) (.var 0)) (.neg (.mul (.var 4) (.mul (.var 2) (.var 2))))) (.var 0)) (.add (.mul (.var 0) (.add (.mul (.var 0) (.var 0)) (.neg (.mul (.var 4) (.mul (.var 2) (.var 2)))))) (.mul (.mul (.var 4) (.var 2)) .zero)) (by decide +kernel)
    · exact Shell.Frame.RE.sound (Shell.Frame.look [M.a, M.b, M.c, M.d, ν]) (.mul (.add (.mul (.var 0) (.var 0)) (.neg (.mul (.var 4) (.mul (.var 2) (.var 2))))) (.var 1)) (.add (.mul (.var 0) (.add (.mul (.var 0) (.var 1)) (.neg (.mul (.var 4) (.mul (.var 2) (.var 3)))))) (.mul (.mul (.var 4) (.var 2)) (.add (.mul (.var 0) (.var 3)) (.neg (.mul (.var 1) (.var 2)))))) (by decide +kernel)
    · exact Shell.Frame.RE.sound (Shell.Frame.look [M.a, M.b, M.c, M.d, ν]) (.mul (.add (.mul (.var 0) (.var 0)) (.neg (.mul (.var 4) (.mul (.var 2) (.var 2))))) (.var 2)) (.add (.mul (.var 2) (.add (.mul (.var 0) (.var 0)) (.neg (.mul (.var 4) (.mul (.var 2) (.var 2)))))) (.mul (.var 0) .zero)) (by decide +kernel)
    · exact Shell.Frame.RE.sound (Shell.Frame.look [M.a, M.b, M.c, M.d, ν]) (.mul (.add (.mul (.var 0) (.var 0)) (.neg (.mul (.var 4) (.mul (.var 2) (.var 2))))) (.var 3)) (.add (.mul (.var 2) (.add (.mul (.var 0) (.var 1)) (.neg (.mul (.var 4) (.mul (.var 2) (.var 3)))))) (.mul (.var 0) (.add (.mul (.var 0) (.var 3)) (.neg (.mul (.var 1) (.var 2)))))) (by decide +kernel)
  · show (a * 1 + b * 0, 0 * 1 + e * 0) = (a, 0)
    rw [mul_one, mul_zero, add_zero, zero_mul, mul_zero, add_zero]
  · have ha : l * (α1 * a1 + ν * β1 * 0) = α2 * a2 + ν * β2 * 0 := congrArg M2.a h
    have hb : l * (α1 * b1 + ν * β1 * e1) = α2 * b2 + ν * β2 * e2 := congrArg M2.b h
    have hc : l * (β1 * a1 + α1 * 0) = β2 * a2 + α2 * 0 := congrArg M2.c h
    have hd : l * (β1 * b1 + α1 * e1) = β2 * b2 + α2 * e2 := congrArg M2.d h
    rw [mul_zero, add_zero, mul_zero, add_zero] at ha hc
    -- the boost class: `(l a1)(α1 β2 − α2 β1) = 0`
    have t1 : (l * a1) * (α1 * β2 + -(α2 * β1)) = (l * (α1 * a1)) * β2 + -(α2 * (l * (β1 * a1))) := Shell.Frame.RE.sound (Shell.Frame.look [l, α1, β1, a1, b1, e1, α2, β2, a2, b2, e2, ν]) (.mul (.mul (.var 0) (.var 3)) (.add (.mul (.var 1) (.var 7)) (.neg (.mul (.var 6) (.var 2))))) (.add (.mul (.mul (.var 0) (.mul (.var 1) (.var 3))) (.var 7)) (.neg (.mul (.var 6) (.mul (.var 0) (.mul (.var 2) (.var 3)))))) (by decide +kernel)
    rw [ha, hc] at t1
    have t2 : α2 * a2 * β2 + -(α2 * (β2 * a2)) = 0 := Shell.Frame.RE.sound (Shell.Frame.look [l, α1, β1, a1, b1, e1, α2, β2, a2, b2, e2, ν]) (.add (.mul (.mul (.var 6) (.var 8)) (.var 7)) (.neg (.mul (.var 6) (.mul (.var 7) (.var 8))))) .zero (by decide +kernel)
    rw [t2] at t1
    have hT : α1 * β2 = α2 * β1 := eq_of_add_neg_eq_zero ((K.mul_eq_zero t1).resolve_left (K.mul_ne_zero hl ha1))
    -- the chart class: scale the `b`, `d` rows by `a2` and read the boost classes equal
    have s1 : a2 * (α2 * b2 + ν * β2 * e2) = l * (a1 * (α1 * b2 + ν * β1 * e2)) := by
      have e : a2 * (α2 * b2 + ν * β2 * e2) = (α2 * a2) * b2 + ν * ((β2 * a2) * e2) := Shell.Frame.RE.sound (Shell.Frame.look [l, α1, β1, a1, b1, e1, α2, β2, a2, b2, e2, ν]) (.mul (.var 8) (.add (.mul (.var 6) (.var 9)) (.mul (.mul (.var 11) (.var 7)) (.var 10)))) (.add (.mul (.mul (.var 6) (.var 8)) (.var 9)) (.mul (.var 11) (.mul (.mul (.var 7) (.var 8)) (.var 10)))) (by decide +kernel)
      rw [e, ← ha, ← hc]; exact Shell.Frame.RE.sound (Shell.Frame.look [l, α1, β1, a1, b1, e1, α2, β2, a2, b2, e2, ν]) (.add (.mul (.mul (.var 0) (.mul (.var 1) (.var 3))) (.var 9)) (.mul (.var 11) (.mul (.mul (.var 0) (.mul (.var 2) (.var 3))) (.var 10)))) (.mul (.var 0) (.mul (.var 3) (.add (.mul (.var 1) (.var 9)) (.mul (.mul (.var 11) (.var 2)) (.var 10))))) (by decide +kernel)
    have s2 : a2 * (β2 * b2 + α2 * e2) = l * (a1 * (β1 * b2 + α1 * e2)) := by
      have e : a2 * (β2 * b2 + α2 * e2) = (β2 * a2) * b2 + (α2 * a2) * e2 := Shell.Frame.RE.sound (Shell.Frame.look [l, α1, β1, a1, b1, e1, α2, β2, a2, b2, e2, ν]) (.mul (.var 8) (.add (.mul (.var 7) (.var 9)) (.mul (.var 6) (.var 10)))) (.add (.mul (.mul (.var 7) (.var 8)) (.var 9)) (.mul (.mul (.var 6) (.var 8)) (.var 10))) (by decide +kernel)
      rw [e, ← ha, ← hc]; exact Shell.Frame.RE.sound (Shell.Frame.look [l, α1, β1, a1, b1, e1, α2, β2, a2, b2, e2, ν]) (.add (.mul (.mul (.var 0) (.mul (.var 2) (.var 3))) (.var 9)) (.mul (.mul (.var 0) (.mul (.var 1) (.var 3))) (.var 10))) (.mul (.var 0) (.mul (.var 3) (.add (.mul (.var 2) (.var 9)) (.mul (.var 1) (.var 10))))) (by decide +kernel)
    have X1 : a2*(α1*b1 + ν*β1*e1) = a1*(α1*b2 + ν*β1*e2) := by
      have e : l * (a2*(α1*b1 + ν*β1*e1)) = a2 * (l * (α1 * b1 + ν * β1 * e1)) := Shell.Frame.RE.sound (Shell.Frame.look [l, α1, β1, a1, b1, e1, α2, β2, a2, b2, e2, ν]) (.mul (.var 0) (.mul (.var 8) (.add (.mul (.var 1) (.var 4)) (.mul (.mul (.var 11) (.var 2)) (.var 5))))) (.mul (.var 8) (.mul (.var 0) (.add (.mul (.var 1) (.var 4)) (.mul (.mul (.var 11) (.var 2)) (.var 5))))) (by decide +kernel)
      rw [hb, s1] at e
      exact K.mul_left_cancel hl e
    have X2 : a2*(β1*b1 + α1*e1) = a1*(β1*b2 + α1*e2) := by
      have e : l * (a2*(β1*b1 + α1*e1)) = a2 * (l * (β1 * b1 + α1 * e1)) := Shell.Frame.RE.sound (Shell.Frame.look [l, α1, β1, a1, b1, e1, α2, β2, a2, b2, e2, ν]) (.mul (.var 0) (.mul (.var 8) (.add (.mul (.var 2) (.var 4)) (.mul (.var 1) (.var 5))))) (.mul (.var 8) (.mul (.var 0) (.add (.mul (.var 2) (.var 4)) (.mul (.var 1) (.var 5))))) (by decide +kernel)
      rw [hd, s2] at e
      exact K.mul_left_cancel hl e
    -- invert the boost: `N(α1, β1) ≠ 0`
    have w1 : (a2 * b1 + -(a1 * b2)) * (α1*α1 + -(ν*(β1*β1))) = α1 * (a2*(α1*b1 + ν*β1*e1) + -(a1*(α1*b2 + ν*β1*e2))) + -(ν * β1 * (a2*(β1*b1 + α1*e1) + -(a1*(β1*b2 + α1*e2)))) := Shell.Frame.RE.sound (Shell.Frame.look [l, α1, β1, a1, b1, e1, α2, β2, a2, b2, e2, ν]) (.mul (.add (.mul (.var 8) (.var 4)) (.neg (.mul (.var 3) (.var 9)))) (.add (.mul (.var 1) (.var 1)) (.neg (.mul (.var 11) (.mul (.var 2) (.var 2)))))) (.add (.mul (.var 1) (.add (.mul (.var 8) (.add (.mul (.var 1) (.var 4)) (.mul (.mul (.var 11) (.var 2)) (.var 5)))) (.neg (.mul (.var 3) (.add (.mul (.var 1) (.var 9)) (.mul (.mul (.var 11) (.var 2)) (.var 10))))))) (.neg (.mul (.mul (.var 11) (.var 2)) (.add (.mul (.var 8) (.add (.mul (.var 2) (.var 4)) (.mul (.var 1) (.var 5)))) (.neg (.mul (.var 3) (.add (.mul (.var 2) (.var 9)) (.mul (.var 1) (.var 10))))))))) (by decide +kernel)
    have w2 : (a2 * e1 + -(a1 * e2)) * (α1*α1 + -(ν*(β1*β1))) = α1 * (a2*(β1*b1 + α1*e1) + -(a1*(β1*b2 + α1*e2))) + -(β1 * (a2*(α1*b1 + ν*β1*e1) + -(a1*(α1*b2 + ν*β1*e2)))) := Shell.Frame.RE.sound (Shell.Frame.look [l, α1, β1, a1, b1, e1, α2, β2, a2, b2, e2, ν]) (.mul (.add (.mul (.var 8) (.var 5)) (.neg (.mul (.var 3) (.var 10)))) (.add (.mul (.var 1) (.var 1)) (.neg (.mul (.var 11) (.mul (.var 2) (.var 2)))))) (.add (.mul (.var 1) (.add (.mul (.var 8) (.add (.mul (.var 2) (.var 4)) (.mul (.var 1) (.var 5)))) (.neg (.mul (.var 3) (.add (.mul (.var 2) (.var 9)) (.mul (.var 1) (.var 10))))))) (.neg (.mul (.var 2) (.add (.mul (.var 8) (.add (.mul (.var 1) (.var 4)) (.mul (.mul (.var 11) (.var 2)) (.var 5)))) (.neg (.mul (.var 3) (.add (.mul (.var 1) (.var 9)) (.mul (.mul (.var 11) (.var 2)) (.var 10))))))))) (by decide +kernel)
    rw [X1, X2, add_neg, add_neg, mul_zero, mul_zero, neg_zero, add_zero] at w1 w2
    have hB : a2 * b1 = a1 * b2 := eq_of_add_neg_eq_zero ((K.mul_eq_zero w1).resolve_right (hN hαβ))
    have hE : a2 * e1 = a1 * e2 := eq_of_add_neg_eq_zero ((K.mul_eq_zero w2).resolve_right (hN hαβ))
    refine ⟨hT, by rw [mul_comm e2 a1, ← hE, mul_comm], ?_⟩
    apply K.mul_left_cancel ha2
    calc a2 * (e2 * b1) = e2 * (a2 * b1) := mul_left_comm a2 e2 b1
      _ = e2 * a1 * b2 := by rw [hB, mul_assoc]
      _ = a1 * e2 * b2 := by rw [mul_comm e2 a1]
      _ = a2 * e1 * b2 := by rw [hE]
      _ = a2 * (e1 * b2) := mul_assoc a2 e1 b2

/-- 38:A9, 38:X4 — on a frame (`Frame.fld`): `Fld.frame_triple`. -/
theorem frame_triple (F : Frame p κ g) {ν : Shell p} (hν : ¬ ∃ y : Shell p, y * y = ν) :
    (∀ M : M2 p, M.det ≠ 0 → (M.a ≠ 0 ∨ M.c ≠ 0) ∧ M.act 1 0 = (M.a, M.c) ∧ (boost ν M.a M.c).act 1 0 = (M.a, M.c) ∧
      M.a * M.a + -(ν * (M.c * M.c)) ≠ 0 ∧
      M2.smul (M.a * M.a + -(ν * (M.c * M.c))) M =
        (boost ν M.a M.c).mul (borel (M.a * M.a + -(ν * (M.c * M.c))) (M.a * M.b + -(ν * (M.c * M.d))) M.det)) ∧
    (∀ a b e : Shell p, (borel a b e).act 1 0 = (a, 0)) ∧
    (∀ l α1 β1 a1 b1 e1 α2 β2 a2 b2 e2 : Shell p, l ≠ 0 → a1 ≠ 0 → a2 ≠ 0 → (α1 ≠ 0 ∨ β1 ≠ 0) →
      M2.smul l ((boost ν α1 β1).mul (borel a1 b1 e1)) = (boost ν α2 β2).mul (borel a2 b2 e2) →
      α1 * β2 = α2 * β1 ∧ e2 * a1 = e1 * a2 ∧ e2 * b1 = e1 * b2) :=
  F.fld.frame_triple hν

/-- The split fibration (`unit_split` states it with the unit and the diagonal matrices named) by the unit `i = diag(r, −r)`, `r = g^κ`, `r² = −1`, on every frame
`p = 4κ + 1`: (1) a matrix commuting with `i` is diagonal — the centraliser is the diagonal torus, inside the Borel
(`diag(a, d) = borel a 0 d`); (2) every diagonal matrix commutes with `i`; (3) `i` is not scalar: the torus is split;
(4) the circle `x² + y² = 1` lands in the torus with determinant `1`, as `x + yi ↦ diag(x + ry, x − ry)`; (5) every
conjugate `M i adj(M)` is trace-zero with `a² + bc = −(det M)²`: the orbit lies in the quadric `a² + bc = −1` up to the
scalar; (6) every point of the quadric is reached: for `N` trace-zero with `a² + bc = −1` there is an invertible `M`
with `M i = N M`; (7) the quadric is the unit sphere `x² + y² + z² = 1` under `(x, y, z) ↦ (rx, y + rz, −(y − rz))`,
and back with `h = 2⁻¹`; (8) two frames over one point of the quadric differ by an element commuting with `i`: the
fibres of the conjugation map are the cosets of the centraliser, by (1). The sphere has `p(p + 1)` points
(`Grav.sphere_area_rung`) and the circle `p − 1` (`Grav.conic_count`). -/
theorem unit_split_let (F : Frame p κ g) :
    let r : Shell p := g ^ κ
    let I : M2 p := ⟨r, 0, 0, -r⟩
    (∀ M : M2 p, M.mul I = I.mul M → M.b = 0 ∧ M.c = 0) ∧
    (∀ a d : Shell p, (⟨a, 0, 0, d⟩ : M2 p).mul I = I.mul ⟨a, 0, 0, d⟩ ∧ (⟨a, 0, 0, d⟩ : M2 p) = borel a 0 d) ∧
    (∀ l : Shell p, I ≠ ⟨l, 0, 0, l⟩) ∧
    (∀ x y : Shell p, x * x + y * y = 1 → (⟨x + r * y, 0, 0, x + -(r * y)⟩ : M2 p).det = 1) ∧
    (∀ M : M2 p, ((M.mul I).mul M.adj).a + ((M.mul I).mul M.adj).d = 0 ∧
      ((M.mul I).mul M.adj).a * ((M.mul I).mul M.adj).a + ((M.mul I).mul M.adj).b * ((M.mul I).mul M.adj).c =
        -(M.det * M.det)) ∧
    (∀ N : M2 p, N.a + N.d = 0 → N.a * N.a + N.b * N.c = -1 → ∃ M : M2 p, M.det ≠ 0 ∧ M.mul I = N.mul M) ∧
    (∀ x y z : Shell p, x * x + y * y + z * z = 1 → (r * x) * (r * x) + (y + r * z) * (-(y + -(r * z))) = -1) ∧
    (∀ h : Shell p, (1 + 1) * h = 1 → ∀ a b c : Shell p, a * a + b * c = -1 →
      (-(r * a)) * (-(r * a)) + (h * (b + -c)) * (h * (b + -c)) + (-(h * (r * (b + c)))) * (-(h * (r * (b + c)))) = 1) ∧
    (∀ N M M' : M2 p, M'.det ≠ 0 → M.mul I = N.mul M → M'.mul I = N.mul M' →
      (M'.adj.mul M).mul I = I.mul (M'.adj.mul M)) := by
  intro r I
  have hr : r * r = -1 := by have e := (F.quarter_turn_order).1; rwa [pow_two] at e
  have hr0 : r ≠ 0 := F.pow_ne_zero κ
  have h2 : (1 : Shell p) + 1 ≠ 0 := by rw [← Frame.two_eq_one_add_one]; exact F.two_ne_zero
  have hm1 : (-1 : Shell p) ≠ 0 := fun e => F.one_ne_zero (by rw [← neg_neg (1 : Shell p), e, neg_zero])
  refine ⟨fun M hM => ?_, fun a d => ⟨M2.ext' ?_ ?_ ?_ ?_, rfl⟩, fun l hl => ?_, fun x y hxy => ?_, fun M => ⟨?_, ?_⟩,
    fun N ht hq => ?_, fun x y z hs => ?_, fun h hh a b c hq => ?_, fun N M M' hM' hM hM'' => ?_⟩
  · -- (1) the `b` and `c` entries of `M i − i M` are `−2 r b` and `2 r c`
    have eb : M.a * 0 + M.b * -r = r * M.b + 0 * M.d := congrArg M2.b hM
    have ec : M.c * r + M.d * 0 = 0 * M.a + -r * M.c := congrArg M2.c hM
    have ub : (1 + 1) * (r * M.b) = (r * M.b + 0 * M.d) + -(M.a * 0 + M.b * -r) := Shell.Frame.RE.sound (Shell.Frame.look [M.a, M.b, M.c, M.d, r]) (.mul (.add .one .one) (.mul (.var 4) (.var 1))) (.add (.add (.mul (.var 4) (.var 1)) (.mul .zero (.var 3))) (.neg (.add (.mul (.var 0) .zero) (.mul (.var 1) (.neg (.var 4)))))) (by decide +kernel)
    have uc : (1 + 1) * (r * M.c) = (M.c * r + M.d * 0) + -(0 * M.a + -r * M.c) := Shell.Frame.RE.sound (Shell.Frame.look [M.a, M.b, M.c, M.d, r]) (.mul (.add .one .one) (.mul (.var 4) (.var 2))) (.add (.add (.mul (.var 2) (.var 4)) (.mul (.var 3) .zero)) (.neg (.add (.mul .zero (.var 0)) (.mul (.neg (.var 4)) (.var 2))))) (by decide +kernel)
    rw [← eb, add_neg] at ub
    rw [ec, add_neg] at uc
    exact ⟨(F.mul_eq_zero ((F.mul_eq_zero ub).resolve_left h2)).resolve_left hr0,
      (F.mul_eq_zero ((F.mul_eq_zero uc).resolve_left h2)).resolve_left hr0⟩
  · exact Shell.Frame.RE.sound (Shell.Frame.look [a, d, r]) (.add (.mul (.var 0) (.var 2)) (.mul .zero .zero)) (.add (.mul (.var 2) (.var 0)) (.mul .zero .zero)) (by decide +kernel)
  · exact Shell.Frame.RE.sound (Shell.Frame.look [a, d, r]) (.add (.mul (.var 0) .zero) (.mul .zero (.neg (.var 2)))) (.add (.mul (.var 2) .zero) (.mul .zero (.var 1))) (by decide +kernel)
  · exact Shell.Frame.RE.sound (Shell.Frame.look [a, d, r]) (.add (.mul .zero (.var 2)) (.mul (.var 1) .zero)) (.add (.mul .zero (.var 0)) (.mul (.neg (.var 2)) .zero)) (by decide +kernel)
  · exact Shell.Frame.RE.sound (Shell.Frame.look [a, d, r]) (.add (.mul .zero .zero) (.mul (.var 1) (.neg (.var 2)))) (.add (.mul .zero .zero) (.mul (.neg (.var 2)) (.var 1))) (by decide +kernel)
  · -- (3) `r = l = −r` forces `r = 0`
    have e1 : r = l := congrArg M2.a hl
    have e2 : -r = l := congrArg M2.d hl
    exact hr0 (F.eq_zero_of_eq_neg (e1.trans e2.symm))
  · -- (4) `(x + ry)(x − ry) = x² − r²y²`
    show (x + r * y) * (x + -(r * y)) + -(0 * 0) = 1
    have e : (x + r * y) * (x + -(r * y)) + -(0 * 0) + (r * r + 1) * (y * y) = x * x + y * y := Shell.Frame.RE.sound (Shell.Frame.look [x, y, r]) (.add (.add (.mul (.add (.var 0) (.mul (.var 2) (.var 1))) (.add (.var 0) (.neg (.mul (.var 2) (.var 1))))) (.neg (.mul .zero .zero))) (.mul (.add (.mul (.var 2) (.var 2)) .one) (.mul (.var 1) (.var 1)))) (.add (.mul (.var 0) (.var 0)) (.mul (.var 1) (.var 1))) (by decide +kernel)
    rw [hr, neg_add, zero_mul (y * y), add_zero, hxy] at e
    exact e
  · exact Shell.Frame.RE.sound (Shell.Frame.look [M.a, M.b, M.c, M.d, r]) (.add (.add (.mul (.add (.mul (.var 0) (.var 4)) (.mul (.var 1) .zero)) (.var 3)) (.mul (.add (.mul (.var 0) .zero) (.mul (.var 1) (.neg (.var 4)))) (.neg (.var 2)))) (.add (.mul (.add (.mul (.var 2) (.var 4)) (.mul (.var 3) .zero)) (.neg (.var 1))) (.mul (.add (.mul (.var 2) .zero) (.mul (.var 3) (.neg (.var 4)))) (.var 0)))) .zero (by decide +kernel)
  · have e : ((M.mul I).mul M.adj).a * ((M.mul I).mul M.adj).a + ((M.mul I).mul M.adj).b * ((M.mul I).mul M.adj).c =
        (r * r + 1) * (M.det * M.det) + -(M.det * M.det) := Shell.Frame.RE.sound (Shell.Frame.look [M.a, M.b, M.c, M.d, r]) (.add (.mul (.add (.mul (.add (.mul (.var 0) (.var 4)) (.mul (.var 1) .zero)) (.var 3)) (.mul (.add (.mul (.var 0) .zero) (.mul (.var 1) (.neg (.var 4)))) (.neg (.var 2)))) (.add (.mul (.add (.mul (.var 0) (.var 4)) (.mul (.var 1) .zero)) (.var 3)) (.mul (.add (.mul (.var 0) .zero) (.mul (.var 1) (.neg (.var 4)))) (.neg (.var 2))))) (.mul (.add (.mul (.add (.mul (.var 0) (.var 4)) (.mul (.var 1) .zero)) (.neg (.var 1))) (.mul (.add (.mul (.var 0) .zero) (.mul (.var 1) (.neg (.var 4)))) (.var 0))) (.add (.mul (.add (.mul (.var 2) (.var 4)) (.mul (.var 3) .zero)) (.var 3)) (.mul (.add (.mul (.var 2) .zero) (.mul (.var 3) (.neg (.var 4)))) (.neg (.var 2)))))) (.add (.mul (.add (.mul (.var 4) (.var 4)) .one) (.mul (.add (.mul (.var 0) (.var 3)) (.neg (.mul (.var 1) (.var 2)))) (.add (.mul (.var 0) (.var 3)) (.neg (.mul (.var 1) (.var 2)))))) (.neg (.mul (.add (.mul (.var 0) (.var 3)) (.neg (.mul (.var 1) (.var 2)))) (.add (.mul (.var 0) (.var 3)) (.neg (.mul (.var 1) (.var 2))))))) (by decide +kernel)
    rw [e, hr, neg_add, zero_mul, zero_add]
  · -- (6) three cases: `b ≠ 0`; `b = 0` and `a = r`; `b = 0` and `a = −r`, with `w = (2r)⁻¹`
    have hd : N.d = -N.a := (neg_eq_of_add_eq_zero ht).symm
    obtain ⟨w, hw⟩ := F.exists_inv (F.mul_ne_zero h2 hr0)
    match Shell.instDecidableEq N.b 0 with
    | .isFalse hb =>
      refine ⟨⟨N.b, N.b, r + -N.a, -(r + N.a)⟩, ?_, M2.ext' ?_ ?_ ?_ ?_⟩
      · show N.b * -(r + N.a) + -(N.b * (r + -N.a)) ≠ 0
        have e : N.b * -(r + N.a) + -(N.b * (r + -N.a)) = -((1 + 1) * (N.b * r)) := Shell.Frame.RE.sound (Shell.Frame.look [N.a, N.b, N.c, N.d, r, w]) (.add (.mul (.var 1) (.neg (.add (.var 4) (.var 0)))) (.neg (.mul (.var 1) (.add (.var 4) (.neg (.var 0)))))) (.neg (.mul (.add .one .one) (.mul (.var 1) (.var 4)))) (by decide +kernel)
        rw [e]
        intro h0
        have h1 : (1 + 1) * (N.b * r) = 0 := by rw [← neg_neg ((1 + 1) * (N.b * r)), h0, neg_zero]
        exact hr0 ((F.mul_eq_zero ((F.mul_eq_zero h1).resolve_left h2)).resolve_left hb)
      · exact Shell.Frame.RE.sound (Shell.Frame.look [N.a, N.b, N.c, N.d, r, w]) (.add (.mul (.var 1) (.var 4)) (.mul (.var 1) .zero)) (.add (.mul (.var 0) (.var 1)) (.mul (.var 1) (.add (.var 4) (.neg (.var 0))))) (by decide +kernel)
      · exact Shell.Frame.RE.sound (Shell.Frame.look [N.a, N.b, N.c, N.d, r, w]) (.add (.mul (.var 1) .zero) (.mul (.var 1) (.neg (.var 4)))) (.add (.mul (.var 0) (.var 1)) (.mul (.var 1) (.neg (.add (.var 4) (.var 0))))) (by decide +kernel)
      · show (r + -N.a) * r + -(r + N.a) * 0 = N.c * N.b + N.d * (r + -N.a)
        rw [hd]
        have e : (r + -N.a) * r + -(r + N.a) * 0 = N.c * N.b + -N.a * (r + -N.a) + (r * r + 1) + -(N.a * N.a + N.b * N.c + 1) := Shell.Frame.RE.sound (Shell.Frame.look [N.a, N.b, N.c, N.d, r, w]) (.add (.mul (.add (.var 4) (.neg (.var 0))) (.var 4)) (.mul (.neg (.add (.var 4) (.var 0))) .zero)) (.add (.add (.add (.mul (.var 2) (.var 1)) (.mul (.neg (.var 0)) (.add (.var 4) (.neg (.var 0))))) (.add (.mul (.var 4) (.var 4)) .one)) (.neg (.add (.add (.mul (.var 0) (.var 0)) (.mul (.var 1) (.var 2))) .one))) (by decide +kernel)
        rw [e, hr, hq, neg_add, add_zero, neg_zero, add_zero]
      · show (r + -N.a) * 0 + -(r + N.a) * -r = N.c * N.b + N.d * -(r + N.a)
        rw [hd]
        have e : (r + -N.a) * 0 + -(r + N.a) * -r = N.c * N.b + -N.a * -(r + N.a) + (r * r + 1) + -(N.a * N.a + N.b * N.c + 1) := Shell.Frame.RE.sound (Shell.Frame.look [N.a, N.b, N.c, N.d, r, w]) (.add (.mul (.add (.var 4) (.neg (.var 0))) .zero) (.mul (.neg (.add (.var 4) (.var 0))) (.neg (.var 4)))) (.add (.add (.add (.mul (.var 2) (.var 1)) (.mul (.neg (.var 0)) (.neg (.add (.var 4) (.var 0))))) (.add (.mul (.var 4) (.var 4)) .one)) (.neg (.add (.add (.mul (.var 0) (.var 0)) (.mul (.var 1) (.var 2))) .one))) (by decide +kernel)
        rw [e, hr, hq, neg_add, add_zero, neg_zero, add_zero]
    | .isTrue hb =>
      have ha2 : N.a * N.a = r * r := by rw [hr, ← hq, hb, zero_mul, add_zero]
      have hsq : (N.a + -r) * (N.a + r) = 0 := by
        have e : (N.a + -r) * (N.a + r) = N.a * N.a + -(r * r) := Shell.Frame.RE.sound (Shell.Frame.look [N.a, N.b, N.c, N.d, r, w]) (.mul (.add (.var 0) (.neg (.var 4))) (.add (.var 0) (.var 4))) (.add (.mul (.var 0) (.var 0)) (.neg (.mul (.var 4) (.var 4)))) (by decide +kernel)
        rw [e, ha2, add_neg]
      match F.mul_eq_zero hsq with
      | .inl h1 =>
        have ha : N.a = r := eq_of_add_neg_eq_zero h1
        refine ⟨⟨1, 0, N.c * w, 1⟩, ?_, M2.ext' ?_ ?_ ?_ ?_⟩
        · show 1 * 1 + -(0 * (N.c * w)) ≠ 0
          rw [mul_one, zero_mul, neg_zero, add_zero]; exact F.one_ne_zero
        · show 1 * r + 0 * 0 = N.a * 1 + N.b * (N.c * w)
          rw [ha, hb]; exact Shell.Frame.RE.sound (Shell.Frame.look [N.a, N.b, N.c, N.d, r, w]) (.add (.mul .one (.var 4)) (.mul .zero .zero)) (.add (.mul (.var 4) .one) (.mul .zero (.mul (.var 2) (.var 5)))) (by decide +kernel)
        · show 1 * 0 + 0 * -r = N.a * 0 + N.b * 1
          rw [hb]; exact Shell.Frame.RE.sound (Shell.Frame.look [N.a, N.b, N.c, N.d, r, w]) (.add (.mul .one .zero) (.mul .zero (.neg (.var 4)))) (.add (.mul (.var 0) .zero) (.mul .zero .one)) (by decide +kernel)
        · show N.c * w * r + 1 * 0 = N.c * 1 + N.d * (N.c * w)
          rw [hd, ha]
          have e : N.c * w * r + 1 * 0 = N.c * 1 + -r * (N.c * w) + N.c * ((1 + 1) * r * w + -1) := Shell.Frame.RE.sound (Shell.Frame.look [N.a, N.b, N.c, N.d, r, w]) (.add (.mul (.mul (.var 2) (.var 5)) (.var 4)) (.mul .one .zero)) (.add (.add (.mul (.var 2) .one) (.mul (.neg (.var 4)) (.mul (.var 2) (.var 5)))) (.mul (.var 2) (.add (.mul (.mul (.add .one .one) (.var 4)) (.var 5)) (.neg .one)))) (by decide +kernel)
          rw [e, hw, add_neg, mul_zero, add_zero]
        · show N.c * w * 0 + 1 * -r = N.c * 0 + N.d * 1
          rw [hd, ha]; exact Shell.Frame.RE.sound (Shell.Frame.look [N.a, N.b, N.c, N.d, r, w]) (.add (.mul (.mul (.var 2) (.var 5)) .zero) (.mul .one (.neg (.var 4)))) (.add (.mul (.var 2) .zero) (.mul (.neg (.var 4)) .one)) (by decide +kernel)
      | .inr h1 =>
        have ha : N.a = -r := eq_neg_of_add_eq_zero h1
        refine ⟨⟨0, 1, 1, -(N.c * w)⟩, ?_, M2.ext' ?_ ?_ ?_ ?_⟩
        · show 0 * -(N.c * w) + -(1 * 1) ≠ 0
          rw [zero_mul, mul_one, zero_add]; exact hm1
        · show 0 * r + 1 * 0 = N.a * 0 + N.b * 1
          rw [ha, hb]; exact Shell.Frame.RE.sound (Shell.Frame.look [N.a, N.b, N.c, N.d, r, w]) (.add (.mul .zero (.var 4)) (.mul .one .zero)) (.add (.mul (.neg (.var 4)) .zero) (.mul .zero .one)) (by decide +kernel)
        · show 0 * 0 + 1 * -r = N.a * 1 + N.b * -(N.c * w)
          rw [ha, hb]; exact Shell.Frame.RE.sound (Shell.Frame.look [N.a, N.b, N.c, N.d, r, w]) (.add (.mul .zero .zero) (.mul .one (.neg (.var 4)))) (.add (.mul (.neg (.var 4)) .one) (.mul .zero (.neg (.mul (.var 2) (.var 5))))) (by decide +kernel)
        · show 1 * r + -(N.c * w) * 0 = N.c * 0 + N.d * 1
          rw [hd, ha]; exact Shell.Frame.RE.sound (Shell.Frame.look [N.a, N.b, N.c, N.d, r, w]) (.add (.mul .one (.var 4)) (.mul (.neg (.mul (.var 2) (.var 5))) .zero)) (.add (.mul (.var 2) .zero) (.mul (.neg (.neg (.var 4))) .one)) (by decide +kernel)
        · show 1 * 0 + -(N.c * w) * -r = N.c * 1 + N.d * -(N.c * w)
          rw [hd, ha]
          have e : 1 * 0 + -(N.c * w) * -r = N.c * 1 + - -r * -(N.c * w) + N.c * ((1 + 1) * r * w + -1) := Shell.Frame.RE.sound (Shell.Frame.look [N.a, N.b, N.c, N.d, r, w]) (.add (.mul .one .zero) (.mul (.neg (.mul (.var 2) (.var 5))) (.neg (.var 4)))) (.add (.add (.mul (.var 2) .one) (.mul (.neg (.neg (.var 4))) (.neg (.mul (.var 2) (.var 5))))) (.mul (.var 2) (.add (.mul (.mul (.add .one .one) (.var 4)) (.var 5)) (.neg .one)))) (by decide +kernel)
          rw [e, hw, add_neg, mul_zero, add_zero]
  · -- (7) forward
    have e : (r * x) * (r * x) + (y + r * z) * (-(y + -(r * z))) = (r * r + 1) * (x * x + z * z) + -(x * x + y * y + z * z) := Shell.Frame.RE.sound (Shell.Frame.look [x, y, z, r]) (.add (.mul (.mul (.var 3) (.var 0)) (.mul (.var 3) (.var 0))) (.mul (.add (.var 1) (.mul (.var 3) (.var 2))) (.neg (.add (.var 1) (.neg (.mul (.var 3) (.var 2))))))) (.add (.mul (.add (.mul (.var 3) (.var 3)) .one) (.add (.mul (.var 0) (.var 0)) (.mul (.var 2) (.var 2)))) (.neg (.add (.add (.mul (.var 0) (.var 0)) (.mul (.var 1) (.var 1))) (.mul (.var 2) (.var 2))))) (by decide +kernel)
    rw [e, hr, neg_add, zero_mul, zero_add, hs]
  · -- (7) back
    have e : (-(r * a)) * (-(r * a)) + (h * (b + -c)) * (h * (b + -c)) + (-(h * (r * (b + c)))) * (-(h * (r * (b + c)))) =
        (a * a + (h * (b + c)) * (h * (b + c))) * (r * r + 1) + -(a * a + b * c) + -(b * c * (((1 + 1) * h + -1) * ((1 + 1) * h + 1))) := Shell.Frame.RE.sound (Shell.Frame.look [a, b, c, r, h]) (.add (.add (.mul (.neg (.mul (.var 3) (.var 0))) (.neg (.mul (.var 3) (.var 0)))) (.mul (.mul (.var 4) (.add (.var 1) (.neg (.var 2)))) (.mul (.var 4) (.add (.var 1) (.neg (.var 2)))))) (.mul (.neg (.mul (.var 4) (.mul (.var 3) (.add (.var 1) (.var 2))))) (.neg (.mul (.var 4) (.mul (.var 3) (.add (.var 1) (.var 2))))))) (.add (.add (.mul (.add (.mul (.var 0) (.var 0)) (.mul (.mul (.var 4) (.add (.var 1) (.var 2))) (.mul (.var 4) (.add (.var 1) (.var 2))))) (.add (.mul (.var 3) (.var 3)) .one)) (.neg (.add (.mul (.var 0) (.var 0)) (.mul (.var 1) (.var 2))))) (.neg (.mul (.mul (.var 1) (.var 2)) (.mul (.add (.mul (.add .one .one) (.var 4)) (.neg .one)) (.add (.mul (.add .one .one) (.var 4)) .one))))) (by decide +kernel)
    rw [e, hr, hq, hh, neg_add, mul_zero, zero_add, neg_neg, add_neg, zero_mul, mul_zero, neg_zero, add_zero]
  · -- (8) two frames over one point of the quadric differ by an element commuting with `i`
    have k1 : M'.adj.mul (M'.mul I) = M'.adj.mul (N.mul M') := congrArg M'.adj.mul hM''
    rw [← M2.mul_assoc', M2.adj_mul, M2.diag_mul, ← M2.mul_assoc'] at k1
    have k2 : (M2.smul M'.det I).mul M'.adj = ((M'.adj.mul N).mul M').mul M'.adj := congrArg (fun X => X.mul M'.adj) k1
    rw [M2.smul_mul, M2.mul_assoc', M2.mul_adj, M2.mul_diag] at k2
    have k3 : I.mul M'.adj = M'.adj.mul N := M2.smul_cancel F.fld hM' k2
    calc (M'.adj.mul M).mul I = M'.adj.mul (M.mul I) := M2.mul_assoc' _ _ _
      _ = (M'.adj.mul N).mul M := by rw [hM, M2.mul_assoc']
      _ = (I.mul M'.adj).mul M := by rw [k3]
      _ = I.mul (M'.adj.mul M) := M2.mul_assoc' _ _ _

/-- The unit as a matrix, `diag(r, −r)` with `r = g^κ`: the corpus's unit is `i = −g^κ` (`quarterTurn`), so this is the
matrix of `−i`; projectively the same class as `diag(−r, r)`, with the same centraliser and the same quadric. -/
def unit (g : Shell p) (κ : Nat) : M2 p := ⟨g ^ κ, 0, 0, -(g ^ κ)⟩

/-- A diagonal matrix `diag(a, d)`. -/
def diag (a d : Shell p) : M2 p := ⟨a, 0, 0, d⟩

/-- 38:A9, 38:B6, 38:X4 — **the split fibration**, `unit_split_let`'s statement with the unit `unit g κ = diag(g^κ, −g^κ)` and the
diagonal matrices `diag a d` named (so that the key files re-elaborate it); the clauses are `unit_split_let`'s (1)–(8): the
centraliser of the unit is the diagonal torus inside the Borel, the unit is not scalar, the circle lands in the torus, the
conjugates fill the quadric `a² + bc = −1` and every point is reached, the quadric is the unit sphere, and two frames over
one point differ by an element of the centraliser. -/
theorem unit_split (F : Frame p κ g) :
    (∀ M : M2 p, M.mul (unit g κ) = (unit g κ).mul M → M.b = 0 ∧ M.c = 0) ∧
    (∀ a d : Shell p, (diag a d).mul (unit g κ) = (unit g κ).mul (diag a d) ∧ (diag a d) = borel a 0 d) ∧
    (∀ l : Shell p, (unit g κ) ≠ diag l l) ∧
    (∀ x y : Shell p, x * x + y * y = 1 → (diag (x + g ^ κ * y) (x + -(g ^ κ * y))).det = 1) ∧
    (∀ M : M2 p, ((M.mul (unit g κ)).mul M.adj).a + ((M.mul (unit g κ)).mul M.adj).d = 0 ∧
      ((M.mul (unit g κ)).mul M.adj).a * ((M.mul (unit g κ)).mul M.adj).a + ((M.mul (unit g κ)).mul M.adj).b * ((M.mul (unit g κ)).mul M.adj).c =
        -(M.det * M.det)) ∧
    (∀ N : M2 p, N.a + N.d = 0 → N.a * N.a + N.b * N.c = -1 → ∃ M : M2 p, M.det ≠ 0 ∧ M.mul (unit g κ) = N.mul M) ∧
    (∀ x y z : Shell p, x * x + y * y + z * z = 1 → (g ^ κ * x) * (g ^ κ * x) + (y + g ^ κ * z) * (-(y + -(g ^ κ * z))) = -1) ∧
    (∀ h : Shell p, (1 + 1) * h = 1 → ∀ a b c : Shell p, a * a + b * c = -1 →
      (-(g ^ κ * a)) * (-(g ^ κ * a)) + (h * (b + -c)) * (h * (b + -c)) + (-(h * (g ^ κ * (b + c)))) * (-(h * (g ^ κ * (b + c)))) = 1) ∧
    (∀ N M M' : M2 p, M'.det ≠ 0 → M.mul (unit g κ) = N.mul M → M'.mul (unit g κ) = N.mul M' →
      (M'.adj.mul M).mul (unit g κ) = (unit g κ).mul (M'.adj.mul M)) :=
  unit_split_let F

/-- 38:A9, 38:A7 — the frame counts: `(p + 1)·p·(p − 1) = 14·13·12 = 2184 = 156·14`, the Borel `156 = 13·12`, the spin cover
twice the rotation half `2·1092 = 2184`, and `PGL₂` carries `169 = 13²` involutions against `SL₂`'s one. -/
theorem frame_counts :
    (14 : Nat) * 13 * 12 = 2184 ∧ (2184 : Nat) = 156 * 14 ∧ (156 : Nat) = 13 * 12 ∧ (2 : Nat) * 1092 = 2184 ∧
    (13 : Nat) * 13 = 169 ∧ (182 : Nat) = 13 * 14 ∧ (2184 : Nat) = 12 * 182 := by decide +kernel

/-- The quaternion `x + y i + z j + w k` as a matrix, `[[x + r y, z + r w], [−z + r w, x − r y]]` with `r² = −1`. -/
def quat (r x y z w : Shell p) : M2 p := ⟨x + r * y, z + r * w, -z + r * w, x + -(r * y)⟩

/-- 38:A7 — the norm-one sphere is `SL₂`: with `r² = −1` the quaternion `x + y i + z j + w k` is the matrix `quat`
(`1, i, j, k ↦ I, diag(r, −r), [[0, 1], [−1, 0]], [[0, r], [r, 0]]`) and its norm is the determinant. -/
theorem sphere_det {r : Shell p} (hr : r * r = -1) (x y z w : Shell p) :
    M2.det (quat r x y z w) = x * x + y * y + z * z + w * w := by
  have e : M2.det (quat r x y z w) =
      x * x + -((r * r) * (y * y)) + (z * z + -((r * r) * (w * w))) :=
    Shell.Frame.RE.sound (Shell.Frame.look [x, y, z, w, r]) (.add (.mul (.add (.var 0) (.mul (.var 4) (.var 1))) (.add (.var 0) (.neg (.mul (.var 4) (.var 1))))) (.neg (.mul (.add (.var 2) (.mul (.var 4) (.var 3))) (.add (.neg (.var 2)) (.mul (.var 4) (.var 3)))))) (.add (.add (.mul (.var 0) (.var 0)) (.neg (.mul (.mul (.var 4) (.var 4)) (.mul (.var 1) (.var 1))))) (.add (.mul (.var 2) (.var 2)) (.neg (.mul (.mul (.var 4) (.var 4)) (.mul (.var 3) (.var 3)))))) (by decide +kernel)
  rw [e, hr, neg_one_mul, neg_one_mul, neg_neg, neg_neg, ← add_assoc]

end Frame
end Shell
end FRC
