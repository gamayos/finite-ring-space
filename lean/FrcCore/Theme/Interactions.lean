import FrcCore.Frame
import FrcCore.Ring

/-!
# FrcCore.Theme.Interactions — the interactions theme: one generation and the Koide form (ledger migration, task LM29)

The master's block G where its derivations are exact.

* **The reflection algebra of four directions (00:G12).** The basis `e_S`, `S ⊆ {0, 1, 2, 3}` (a subset is a bitmask
  `S < 16`), with `e_S e_T = ± e_{S∪T}` for disjoint `S`, `T` and `0` otherwise, the sign the parity of the pairs
  `s > t`: sixteen elements, an associative product, anticommuting directions (`reflection_algebra`). The quarter-turn
  as the fifth direction, `e_S ↦ e_S` (`|S|` even) and `e_S ↦ e_S e_4` (`|S|` odd), is a bijection onto the even subsets
  of five directions, the chiral spinor `16` (`fifth_direction`).
* **One generation (00:G11).** The `16` read `3 + 2` (colour `{0, 1, 2}`, weak `{3, 4}`), the hypercharge
  `Y(S) = −|S ∩ C|/3 + |S ∩ W|/2` (in sixths): the content `(1,1)₀ + (3̄,1)_{−2/3} + (3,2)_{1/6} + (1,1)₁ + (1,2)_{−1/2} +
  (3̄,1)_{1/3}`, the charges `Q = T₃ + Y`, the anomaly sums `Σ Y = Σ Y³ = 0`, `SU(3)²Y = SU(2)²Y = 0`, as many colour
  triplets as antitriplets, an even number of doublets, and the right-handed neutrino `(1,1)₀` (`one_generation`).
* **The Koide form (00:G16).** On the cube-root orbit, Parseval on `C₃`: `3 Σ a_j² = â₀² + 2 â₁ â₂` with
  `â_k = Σ_j a_j ω^{jk}`, `ω² + ω + 1 = 0` — that is `Q = 1/3 + (2/3)ρ²`, `ρ² = â₁â₂/â₀²` (`koide_parseval`); and
  `Q = 2/3 ⟺ ρ² = 1/2` (`koide_two_thirds`).

The finite statements are decided by the kernel; the Koide identities by the ring normaliser. No axioms.
-/

namespace FRC.Interactions

open FRC.Shell FRC.Shell.Frame

/-! ## Subsets of the directions -/

/-- Direction `i` belongs to the subset `S` (a bitmask). -/
def bit (S i : Nat) : Bool := (S / 2 ^ i) % 2 == 1

/-- The number of directions `lo ≤ i < hi` in `S`. -/
def cnt (S lo hi : Nat) : Nat := ((List.range (hi - lo)).filter (fun k => bit S (lo + k))).length

/-- `S` and `T` share no direction among the first five. -/
def disj (S T : Nat) : Bool := (List.range 5).all (fun i => !(bit S i && bit T i))

/-- The pairs `s ∈ S`, `t ∈ T` with `s > t`. -/
def inv (S T : Nat) : Nat :=
  ((List.range 5).flatMap (fun s => (List.range 5).map (fun t => (s, t)))).filter
    (fun st => bit S st.1 && bit T st.2 && decide (st.2 < st.1)) |>.length

/-- The product of basis elements: `e_S e_T = (−1)^{inv(S,T)} e_{S∪T}` for disjoint `S`, `T`, else `0`; as
(coefficient, index of the basis element). -/
def emul (S T : Nat) : Int × Nat := if disj S T then (if inv S T % 2 == 0 then 1 else -1, S + T) else (0, 0)

/-- `(e_S e_T) e_U` and `e_S (e_T e_U)` on the basis. -/
def assocL (S T U : Nat) : Int × Nat :=
  let a := emul S T; let b := emul a.2 U; (a.1 * b.1, if a.1 * b.1 == 0 then 0 else b.2)
def assocR (S T U : Nat) : Int × Nat :=
  let a := emul T U; let b := emul S a.2; (a.1 * b.1, if a.1 * b.1 == 0 then 0 else b.2)

/-- The even subsets of five directions: the chiral spinor `16`. -/
def gen16 : List Nat := (List.range 32).filter (fun S => cnt S 0 5 % 2 == 0)

/-- The quarter-turn as the fifth direction: `e_S ↦ e_S` for `|S|` even, `e_S ↦ e_S e_4` for `|S|` odd. -/
def fifth (S : Nat) : Nat := if cnt S 0 4 % 2 == 0 then S else S + 16

/-! ## The reflection algebra of four directions (00:G12) -/

/-- 00:G12 — the reflection algebra of four directions: `16` basis elements `e_S`; the product is associative on
the basis; distinct directions anticommute, `e_i e_j = −e_j e_i`, and each squares to zero. -/
theorem reflection_algebra :
    (List.range 16).length = 16 ∧
    (List.range 16).all (fun S => (List.range 16).all (fun T => (List.range 16).all (fun U =>
      assocL S T U == assocR S T U))) = true ∧
    (List.range 4).all (fun i => (List.range 4).all (fun j =>
      if i == j then emul (2 ^ i) (2 ^ j) == (0, 0)
      else emul (2 ^ i) (2 ^ j) == ((-(emul (2 ^ j) (2 ^ i)).1), (emul (2 ^ j) (2 ^ i)).2))) = true := by
  decide +kernel

/-- 00:G12 — the quarter-turn as the fifth direction maps the sixteen `e_S` of four directions one-to-one onto the
sixteen even subsets of five directions, the chiral spinor `16`; for `|S|` odd the image is the product `e_S e_4`
with sign `+1`. -/
theorem fifth_direction :
    gen16.length = 16 ∧
    (List.range 16).all (fun S => gen16.contains (fifth S)) = true ∧
    (List.range 16).all (fun S => (List.range 16).all (fun T => fifth S == fifth T → S == T)) = true ∧
    gen16.all (fun R => (List.range 16).any (fun S => fifth S == R)) = true ∧
    (List.range 16).all (fun S => cnt S 0 4 % 2 == 0 || emul S 16 == (1, fifth S)) = true := by
  decide +kernel

/-! ## One generation, read `3 + 2` (00:G11) -/

/-- Colour indices `{0, 1, 2}` and weak indices `{3, 4}` of a state. -/
def col (S : Nat) : Nat := cnt S 0 3
def wk (S : Nat) : Nat := cnt S 3 5

/-- The hypercharge in sixths: `6Y = −2 |S ∩ C| + 3 |S ∩ W|`. -/
def y6 (S : Nat) : Int := -2 * (col S : Int) + 3 * (wk S : Int)

/-- The weak isospin in halves: `+1` for `{3}`, `−1` for `{4}`, `0` for the singlets. -/
def t3h (S : Nat) : Int := if wk S == 1 then (if bit S 3 then 1 else -1) else 0

/-- The charge in sixths: `6Q = 6T₃ + 6Y`. -/
def q6 (S : Nat) : Int := 3 * t3h S + y6 S

/-- The sum of a list of integers. -/
def isum (l : List Int) : Int := l.foldl (· + ·) 0

/-- 00:G11 — one generation as the spinor `16` of the rank-five frame read `3 + 2`. The content by multiplet
(colour indices, weak indices, `6Y`): `(0,0,0)`, `(2,0,−4)` ×3, `(1,1,1)` ×6, `(0,2,6)`, `(3,1,−3)` ×2, `(2,2,2)` ×3,
that is `ν^c + u^c + Q + e^c + L + d^c`; the charges `6Q`; the anomaly sums `Σ Y = Σ Y³ = 0`, `SU(3)²Y = 0` (the colour
triplets and antitriplets), `SU(2)²Y = 0` (the doublets); as many triplets as antitriplets; an even number of doublets
(Witten); and the right-handed neutrino, the state `∅`, neutral and a singlet. -/
theorem one_generation :
    (gen16.filter (fun S => col S == 0 && wk S == 0 && y6 S == 0)).length = 1 ∧
    (gen16.filter (fun S => col S == 2 && wk S == 0 && y6 S == -4)).length = 3 ∧
    (gen16.filter (fun S => col S == 1 && wk S == 1 && y6 S == 1)).length = 6 ∧
    (gen16.filter (fun S => col S == 0 && wk S == 2 && y6 S == 6)).length = 1 ∧
    (gen16.filter (fun S => col S == 3 && wk S == 1 && y6 S == -3)).length = 2 ∧
    (gen16.filter (fun S => col S == 2 && wk S == 2 && y6 S == 2)).length = 3 ∧
    gen16.map q6 = [0, -4, -4, -4, 4, 4, 4, 0, -2, -2, -2, -6, 6, 2, 2, 2] ∧
    isum (gen16.map y6) = 0 ∧ isum (gen16.map (fun S => y6 S ^ 3)) = 0 ∧
    isum ((gen16.filter (fun S => col S == 1 || col S == 2)).map y6) = 0 ∧
    isum ((gen16.filter (fun S => wk S == 1)).map y6) = 0 ∧
    (gen16.filter (fun S => col S == 1)).length = (gen16.filter (fun S => col S == 2)).length ∧
    (gen16.filter (fun S => wk S == 1)).length % 4 = 0 ∧
    (gen16.contains 0 && y6 0 == 0 && q6 0 == 0 && col 0 == 0 && wk 0 == 0) = true := by
  decide +kernel

/-! ## The Koide form on the cube-root orbit (00:G16) -/

variable {p : Nat} [Pos p]

theorem three_eq : (3 : Shell p) = 1 + 1 + 1 := by
  show ofNat 3 = ofNat 1 + ofNat 1 + ofNat 1
  rw [ofNat_add, ofNat_add]

theorem two_eq : (2 : Shell p) = 1 + 1 := by
  show ofNat 2 = ofNat 1 + ofNat 1
  rw [ofNat_add]

/-- 00:G16 — Parseval on the cube-root orbit `C₃`: for amplitudes `a₀, a₁, a₂` and `ω` with `ω² + ω + 1 = 0`,
`3 Σ a_j² = â₀² + 2 â₁ â₂`, `â₀ = Σ a_j`, `â₁ = a₀ + a₁ω + a₂ω²`, `â₂ = a₀ + a₁ω² + a₂ω` — the Koide form
`Q = Σ a_j² / (Σ a_j)² = 1/3 + (2/3)ρ²` with `ρ² = â₁â₂/â₀²`, exact and assumption-free. -/
theorem koide_parseval (a₀ a₁ a₂ ω : Shell p) (hω : ω * ω + ω + 1 = 0) :
    3 * (a₀ * a₀ + a₁ * a₁ + a₂ * a₂) =
      (a₀ + a₁ + a₂) * (a₀ + a₁ + a₂) + 2 * ((a₀ + a₁ * ω + a₂ * (ω * ω)) * (a₀ + a₁ * (ω * ω) + a₂ * ω)) := by
  rw [three_eq, two_eq]
  have h : (1 + 1 + 1) * (a₀ * a₀ + a₁ * a₁ + a₂ * a₂) =
      (a₀ + a₁ + a₂) * (a₀ + a₁ + a₂) + (1 + 1) * ((a₀ + a₁ * ω + a₂ * (ω * ω)) * (a₀ + a₁ * (ω * ω) + a₂ * ω)) +
        (ω * ω + ω + 1) * (-((1 + 1) * a₀ * a₁) + -((1 + 1) * a₀ * a₂) + -((1 + 1) * a₁ * a₁ * ω) + (1 + 1) * a₁ * a₁ + -((1 + 1) * a₁ * a₂ * ω * ω) + (1 + 1) * a₁ * a₂ * ω + -((1 + 1) * a₁ * a₂) + -((1 + 1) * a₂ * a₂ * ω) + (1 + 1) * a₂ * a₂) :=
    Shell.Frame.RE.sound (Shell.Frame.look [a₀, a₁, a₂, ω]) (.mul (.add (.add .one .one) .one) (.add (.add (.mul (.var 0) (.var 0)) (.mul (.var 1) (.var 1))) (.mul (.var 2) (.var 2)))) (.add (.add (.mul (.add (.add (.var 0) (.var 1)) (.var 2)) (.add (.add (.var 0) (.var 1)) (.var 2))) (.mul (.add .one .one) (.mul (.add (.add (.var 0) (.mul (.var 1) (.var 3))) (.mul (.var 2) (.mul (.var 3) (.var 3)))) (.add (.add (.var 0) (.mul (.var 1) (.mul (.var 3) (.var 3)))) (.mul (.var 2) (.var 3)))))) (.mul (.add (.add (.mul (.var 3) (.var 3)) (.var 3)) .one) (.add (.add (.add (.add (.add (.add (.add (.add (.neg (.mul (.mul (.add .one .one) (.var 0)) (.var 1))) (.neg (.mul (.mul (.add .one .one) (.var 0)) (.var 2)))) (.neg (.mul (.mul (.mul (.add .one .one) (.var 1)) (.var 1)) (.var 3)))) (.mul (.mul (.add .one .one) (.var 1)) (.var 1))) (.neg (.mul (.mul (.mul (.mul (.add .one .one) (.var 1)) (.var 2)) (.var 3)) (.var 3)))) (.mul (.mul (.mul (.add .one .one) (.var 1)) (.var 2)) (.var 3))) (.neg (.mul (.mul (.add .one .one) (.var 1)) (.var 2)))) (.neg (.mul (.mul (.mul (.add .one .one) (.var 2)) (.var 2)) (.var 3)))) (.mul (.mul (.add .one .one) (.var 2)) (.var 2))))) (by decide +kernel)
  rw [h, hω, zero_mul, add_zero]

/-- 00:G16, 28:C2 — `Q = 2/3 ⟺ ρ² = 1/2`: `3 Σ a_j² = 2 â₀²` exactly when `2 â₁ â₂ = â₀²`. -/
theorem koide_two_thirds (a₀ a₁ a₂ ω : Shell p) (hω : ω * ω + ω + 1 = 0) :
    3 * (a₀ * a₀ + a₁ * a₁ + a₂ * a₂) = 2 * ((a₀ + a₁ + a₂) * (a₀ + a₁ + a₂)) ↔
      2 * ((a₀ + a₁ * ω + a₂ * (ω * ω)) * (a₀ + a₁ * (ω * ω) + a₂ * ω)) = (a₀ + a₁ + a₂) * (a₀ + a₁ + a₂) := by
  rw [koide_parseval a₀ a₁ a₂ ω hω, two_mul' ((a₀ + a₁ + a₂) * (a₀ + a₁ + a₂))]
  constructor
  · intro h
    apply add_right_cancel (c := (a₀ + a₁ + a₂) * (a₀ + a₁ + a₂))
    rw [add_comm, h]
  · intro h
    rw [h]

end FRC.Interactions
