import FrcCore.Frame
import FrcCore.Ring
import FrcCore.Theme.Quadratic
import FrcCore.Theme.Field

/-!
# FrcCore.Theme.Interactions — the interactions theme: one generation, the Koide form and 27-fields' exact content (task LM29; 16 October 2026)

The master's block G where its derivations are exact, and the exact content of 27-fields' ledger (16 October 2026).

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

* **27-fields (16 October 2026).** The electroweak counts (`weinberg_angle`, `unification_counts`, `five_eighths`), the
  residue and its instances (`residue_five`, `residue_instances`, by the twelve-periodic induction `twelve_periodic`), the
  rank tower (`rank_tower`), the neutral Hessian and the forced projector (`hessian_neutral`, `hessian_full` on `𝔽₁₃` and
  `𝔽₅`, `projector_forced`), the lattice identities (`holonomy_stokes`, `gauge_flux_invariant`), the V − A cancellation and
  the orientation relabelling (`va_cancel`, `projector_idempotent`, `orientation_flip`), the drive's adjoint on `𝔽₁₃`
  (`drive_adjoint`), and the colour–isospin reframings as automorphisms of the reflection algebra (`offblock_automorphism`).
  The kernel-decided certificates of the paper's data are `Theme/Fields.lean`'s.

The finite statements are decided by the kernel; the ring identities by the ring normaliser. No axioms.
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

/-- 00:G12 — the reflection algebra of four directions: the `16` basis elements `e_S`, `S ⊆ {0, 1, 2, 3}`, close under
the product; the product is associative on the basis; distinct directions anticommute, `e_i e_j = −e_j e_i`, and each
squares to zero. -/
theorem reflection_algebra :
    (List.range 16).all (fun S => (List.range 16).all (fun T => decide ((emul S T).2 < 16))) = true ∧
    (List.range 16).all (fun S => (List.range 16).all (fun T => (List.range 16).all (fun U =>
      assocL S T U == assocR S T U))) = true ∧
    (List.range 4).all (fun i => (List.range 4).all (fun j =>
      if i == j then emul (2 ^ i) (2 ^ j) == (0, 0)
      else emul (2 ^ i) (2 ^ j) == ((-(emul (2 ^ j) (2 ^ i)).1), (emul (2 ^ j) (2 ^ i)).2))) = true := by
  decide +kernel

/-- 00:G12, 27:C9 — the quarter-turn as the fifth direction maps the sixteen `e_S` of four directions one-to-one onto the
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

/-- 00:G11, 27:C6, 27:C8, 27:X2, 27:X8, 27:P2, 27:P6, 27:P7 — one generation as the spinor `16` of the rank-five frame read `3 + 2`. The content by multiplet
(colour indices, weak indices, `6Y`): `(0,0,0)`, `(2,0,−4)` ×3, `(1,1,1)` ×6, `(0,2,6)`, `(3,1,−3)` ×2, `(2,2,2)` ×3,
that is `ν^c + u^c + Q + e^c + L + d^c`; the charges `6Q`; the anomaly sums `Σ Y = Σ Y³ = 0`, `SU(3)²Y = 0` (the colour
triplets and antitriplets), `SU(2)²Y = 0` (the doublets); as many triplets as antitriplets; an even number of doublets
(Witten); and the right-handed neutrino, the state `∅`, neutral and a singlet; the charges `6Q` of the list give the proton's
`6Q(uud) = 4 + 4 − 2 = 6 = 6Q(e⁺)` (27:X2). -/
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

/-- 00:G16, 27:X10, 27:P8 — Parseval on the cube-root orbit `C₃`: for amplitudes `a₀, a₁, a₂` and `ω` with `ω² + ω + 1 = 0`,
`3 Σ a_j² = â₀² + 2 â₁ â₂`, `â₀ = Σ a_j`, `â₁ = a₀ + a₁ω + a₂ω²`, `â₂ = a₀ + a₁ω² + a₂ω` — the Koide form
`Q = Σ a_j² / (Σ a_j)² = 1/3 + (2/3)ρ²` with `ρ² = â₁â₂/â₀²`, exact on every shell carrying the root `ω`. -/
theorem koide_parseval (a₀ a₁ a₂ ω : Shell p) (hω : ω * ω + ω + 1 = 0) :
    3 * (a₀ * a₀ + a₁ * a₁ + a₂ * a₂) =
      (a₀ + a₁ + a₂) * (a₀ + a₁ + a₂) + 2 * ((a₀ + a₁ * ω + a₂ * (ω * ω)) * (a₀ + a₁ * (ω * ω) + a₂ * ω)) := by
  rw [three_eq, two_eq]
  have h : (1 + 1 + 1) * (a₀ * a₀ + a₁ * a₁ + a₂ * a₂) =
      (a₀ + a₁ + a₂) * (a₀ + a₁ + a₂) + (1 + 1) * ((a₀ + a₁ * ω + a₂ * (ω * ω)) * (a₀ + a₁ * (ω * ω) + a₂ * ω)) +
        (ω * ω + ω + 1) * (-((1 + 1) * a₀ * a₁) + -((1 + 1) * a₀ * a₂) + -((1 + 1) * a₁ * a₁ * ω) + (1 + 1) * a₁ * a₁ + -((1 + 1) * a₁ * a₂ * ω * ω) + (1 + 1) * a₁ * a₂ * ω + -((1 + 1) * a₁ * a₂) + -((1 + 1) * a₂ * a₂ * ω) + (1 + 1) * a₂ * a₂) :=
    Shell.Frame.RE.sound (Shell.Frame.look [a₀, a₁, a₂, ω]) (.mul (.add (.add .one .one) .one) (.add (.add (.mul (.var 0) (.var 0)) (.mul (.var 1) (.var 1))) (.mul (.var 2) (.var 2)))) (.add (.add (.mul (.add (.add (.var 0) (.var 1)) (.var 2)) (.add (.add (.var 0) (.var 1)) (.var 2))) (.mul (.add .one .one) (.mul (.add (.add (.var 0) (.mul (.var 1) (.var 3))) (.mul (.var 2) (.mul (.var 3) (.var 3)))) (.add (.add (.var 0) (.mul (.var 1) (.mul (.var 3) (.var 3)))) (.mul (.var 2) (.var 3)))))) (.mul (.add (.add (.mul (.var 3) (.var 3)) (.var 3)) .one) (.add (.add (.add (.add (.add (.add (.add (.add (.neg (.mul (.mul (.add .one .one) (.var 0)) (.var 1))) (.neg (.mul (.mul (.add .one .one) (.var 0)) (.var 2)))) (.neg (.mul (.mul (.mul (.add .one .one) (.var 1)) (.var 1)) (.var 3)))) (.mul (.mul (.add .one .one) (.var 1)) (.var 1))) (.neg (.mul (.mul (.mul (.mul (.add .one .one) (.var 1)) (.var 2)) (.var 3)) (.var 3)))) (.mul (.mul (.mul (.add .one .one) (.var 1)) (.var 2)) (.var 3))) (.neg (.mul (.mul (.add .one .one) (.var 1)) (.var 2)))) (.neg (.mul (.mul (.mul (.add .one .one) (.var 2)) (.var 2)) (.var 3)))) (.mul (.mul (.add .one .one) (.var 2)) (.var 2))))) (by decide +kernel)
  rw [h, hω, zero_mul, add_zero]

/-- 00:G16, 28:C2, 27:X10, 27:P8 — `Q = 2/3 ⟺ ρ² = 1/2`: `3 Σ a_j² = 2 â₀²` exactly when `2 â₁ â₂ = â₀²`. -/
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

/-! ## The Koide form on every shell, the Carrier included (00:G16)

The Carrier has no cube root of unity (`Ω ≡ 5 (mod 12)`, B5), so `koide_parseval` is vacuous there. The cube roots lie
in the extension `𝔽_p[w]/(w² − ν)` at `ν = −3`: `ω = −h + h w` with `h = 1/2`. Read there, Parseval on `C₃` holds on
every shell, and `â₁ â₂ = N(â₁)` is a residue of the shell. -/

/-- `ω = −1/2 + (1/2) w`, a cube root of unity of the extension at `ν = −3` (`h = 1/2`). -/
def omega3 (ν h : Shell p) : Extension.Ext p ν := ⟨-h, h⟩

/-- `â₁ = a₀ + a₁ ω + a₂ ω²` and `â₂ = a₀ + a₁ ω² + a₂ ω`. -/
def hat1 (ν h a₀ a₁ a₂ : Shell p) : Extension.Ext p ν :=
  Extension.Ext.ofShell a₀ + Extension.Ext.ofShell a₁ * omega3 ν h + Extension.Ext.ofShell a₂ * (omega3 ν h * omega3 ν h)
def hat2 (ν h a₀ a₁ a₂ : Shell p) : Extension.Ext p ν :=
  Extension.Ext.ofShell a₀ + Extension.Ext.ofShell a₁ * (omega3 ν h * omega3 ν h) + Extension.Ext.ofShell a₂ * omega3 ν h

theorem red2i {L R A B X Y : Shell p} (e : L = R + A * X + B * Y) (ha : A = 0) (hb : B = 0) : L = R := by
  rw [ha, hb, zero_mul, zero_mul, add_zero, add_zero] at e; exact e

/-- 00:G16, 27:X10, 27:P8, on every shell: with `h + h = 1` and `ν = −3`, `ω = −h + h w` has `ω² + ω + 1 = 0`; `â₂ = â̄₁`, so
`â₁ â₂ = N(â₁)`; Parseval `3 Σ a_j² = â₀² + 2 N(â₁)`; and `Q = 2/3 ⟺ 2 N(â₁) = â₀²` (`ρ² = 1/2`). -/
theorem koide_extension {ν h : Shell p} (hh : h + h = 1) (hν : ν + 1 + 1 + 1 = 0) (a₀ a₁ a₂ : Shell p) :
    omega3 ν h * omega3 ν h + omega3 ν h + 1 = 0 ∧ hat2 ν h a₀ a₁ a₂ = Extension.Ext.conj (hat1 ν h a₀ a₁ a₂) ∧
    hat1 ν h a₀ a₁ a₂ * hat2 ν h a₀ a₁ a₂ = Extension.Ext.ofShell (hat1 ν h a₀ a₁ a₂).norm ∧
    3 * (a₀ * a₀ + a₁ * a₁ + a₂ * a₂) = (a₀ + a₁ + a₂) * (a₀ + a₁ + a₂) + 2 * (hat1 ν h a₀ a₁ a₂).norm ∧
    (3 * (a₀ * a₀ + a₁ * a₁ + a₂ * a₂) = 2 * ((a₀ + a₁ + a₂) * (a₀ + a₁ + a₂)) ↔
      2 * (hat1 ν h a₀ a₁ a₂).norm = (a₀ + a₁ + a₂) * (a₀ + a₁ + a₂)) := by
  have hA : h + h + -1 = 0 := by rw [hh, add_neg]
  have hB := hν
  have hc : hat2 ν h a₀ a₁ a₂ = Extension.Ext.conj (hat1 ν h a₀ a₁ a₂) := Extension.Ext.ext
    ((red2i (Shell.Frame.RE.sound (Shell.Frame.look [ν, h, a₀, a₁, a₂]) (.add (.add (.var 2) (.add (.mul (.var 3) (.add (.mul (.neg (.var 1)) (.neg (.var 1))) (.mul (.var 0) (.mul (.var 1) (.var 1))))) (.mul (.var 0) (.mul .zero (.add (.mul (.neg (.var 1)) (.var 1)) (.mul (.var 1) (.neg (.var 1)))))))) (.add (.mul (.var 4) (.neg (.var 1))) (.mul (.var 0) (.mul .zero (.var 1))))) (.add (.add (.add (.add (.var 2) (.add (.mul (.var 3) (.neg (.var 1))) (.mul (.var 0) (.mul .zero (.var 1))))) (.add (.mul (.var 4) (.add (.mul (.neg (.var 1)) (.neg (.var 1))) (.mul (.var 0) (.mul (.var 1) (.var 1))))) (.mul (.var 0) (.mul .zero (.add (.mul (.neg (.var 1)) (.var 1)) (.mul (.var 1) (.neg (.var 1)))))))) (.mul (.add (.add (.var 1) (.var 1)) (.neg .one)) (.add (.mul (.var 1) (.var 4)) (.neg (.mul (.var 1) (.var 3)))))) (.mul (.add (.add (.add (.var 0) .one) .one) .one) (.add (.mul (.mul (.var 3) (.var 1)) (.var 1)) (.neg (.mul (.mul (.var 4) (.var 1)) (.var 1)))))) (by decide +kernel)) hA hB : (a₀ + ((a₁ * (((-h) * (-h)) + (ν * (h * h)))) + (ν * (0 * (((-h) * h) + (h * (-h))))))) + ((a₂ * (-h)) + (ν * (0 * h))) = (a₀ + ((a₁ * (-h)) + (ν * (0 * h)))) + ((a₂ * (((-h) * (-h)) + (ν * (h * h)))) + (ν * (0 * (((-h) * h) + (h * (-h))))))))
    ((red2i (Shell.Frame.RE.sound (Shell.Frame.look [ν, h, a₀, a₁, a₂]) (.add (.add .zero (.add (.mul (.var 3) (.add (.mul (.neg (.var 1)) (.var 1)) (.mul (.var 1) (.neg (.var 1))))) (.mul .zero (.add (.mul (.neg (.var 1)) (.neg (.var 1))) (.mul (.var 0) (.mul (.var 1) (.var 1))))))) (.add (.mul (.var 4) (.var 1)) (.mul .zero (.neg (.var 1))))) (.add (.add (.neg (.add (.add .zero (.add (.mul (.var 3) (.var 1)) (.mul .zero (.neg (.var 1))))) (.add (.mul (.var 4) (.add (.mul (.neg (.var 1)) (.var 1)) (.mul (.var 1) (.neg (.var 1))))) (.mul .zero (.add (.mul (.neg (.var 1)) (.neg (.var 1))) (.mul (.var 0) (.mul (.var 1) (.var 1)))))))) (.mul (.add (.add (.var 1) (.var 1)) (.neg .one)) (.add (.neg (.mul (.var 1) (.var 3))) (.neg (.mul (.var 1) (.var 4)))))) (.mul (.add (.add (.add (.var 0) .one) .one) .one) .zero)) (by decide +kernel)) hA hB : (0 + ((a₁ * (((-h) * h) + (h * (-h)))) + (0 * (((-h) * (-h)) + (ν * (h * h)))))) + ((a₂ * h) + (0 * (-h))) = -((0 + ((a₁ * h) + (0 * (-h)))) + ((a₂ * (((-h) * h) + (h * (-h)))) + (0 * (((-h) * (-h)) + (ν * (h * h))))))))
  have hp : 3 * (a₀ * a₀ + a₁ * a₁ + a₂ * a₂) = (a₀ + a₁ + a₂) * (a₀ + a₁ + a₂) + 2 * (hat1 ν h a₀ a₁ a₂).norm := by
    rw [three_eq, two_eq]
    exact (red2i (Shell.Frame.RE.sound (Shell.Frame.look [ν, h, a₀, a₁, a₂]) (.mul (.add (.add .one .one) .one) (.add (.add (.mul (.var 2) (.var 2)) (.mul (.var 3) (.var 3))) (.mul (.var 4) (.var 4)))) (.add (.add (.add (.mul (.add (.add (.var 2) (.var 3)) (.var 4)) (.add (.add (.var 2) (.var 3)) (.var 4))) (.mul (.add .one .one) (.add (.mul (.add (.add (.var 2) (.add (.mul (.var 3) (.neg (.var 1))) (.mul (.var 0) (.mul .zero (.var 1))))) (.add (.mul (.var 4) (.add (.mul (.neg (.var 1)) (.neg (.var 1))) (.mul (.var 0) (.mul (.var 1) (.var 1))))) (.mul (.var 0) (.mul .zero (.add (.mul (.neg (.var 1)) (.var 1)) (.mul (.var 1) (.neg (.var 1)))))))) (.add (.add (.var 2) (.add (.mul (.var 3) (.neg (.var 1))) (.mul (.var 0) (.mul .zero (.var 1))))) (.add (.mul (.var 4) (.add (.mul (.neg (.var 1)) (.neg (.var 1))) (.mul (.var 0) (.mul (.var 1) (.var 1))))) (.mul (.var 0) (.mul .zero (.add (.mul (.neg (.var 1)) (.var 1)) (.mul (.var 1) (.neg (.var 1))))))))) (.neg (.mul (.var 0) (.mul (.add (.add .zero (.add (.mul (.var 3) (.var 1)) (.mul .zero (.neg (.var 1))))) (.add (.mul (.var 4) (.add (.mul (.neg (.var 1)) (.var 1)) (.mul (.var 1) (.neg (.var 1))))) (.mul .zero (.add (.mul (.neg (.var 1)) (.neg (.var 1))) (.mul (.var 0) (.mul (.var 1) (.var 1))))))) (.add (.add .zero (.add (.mul (.var 3) (.var 1)) (.mul .zero (.neg (.var 1))))) (.add (.mul (.var 4) (.add (.mul (.neg (.var 1)) (.var 1)) (.mul (.var 1) (.neg (.var 1))))) (.mul .zero (.add (.mul (.neg (.var 1)) (.neg (.var 1))) (.mul (.var 0) (.mul (.var 1) (.var 1))))))))))))) (.mul (.add (.add (.var 1) (.var 1)) (.neg .one)) (.add (.add (.add (.add (.add (.add (.add (.add (.add (.add (.add (.neg (.mul (.add .one .one) (.mul (.var 3) (.var 3)))) (.neg (.mul (.add .one .one) (.mul (.var 4) (.var 4))))) (.neg (.mul (.add (.add (.add (.add (.add (.add (.add (.add (.add (.add (.add (.add (.add (.add (.add .one .one) .one) .one) .one) .one) .one) .one) .one) .one) .one) .one) .one) .one) .one) .one) (.mul (.mul (.mul (.mul (.var 1) (.var 1)) (.var 1)) (.var 4)) (.var 4))))) (.neg (.mul (.add (.add (.add (.add (.add (.add (.add .one .one) .one) .one) .one) .one) .one) .one) (.mul (.mul (.mul (.var 1) (.var 1)) (.var 4)) (.var 4))))) (.neg (.mul (.add (.add (.add .one .one) .one) .one) (.mul (.mul (.var 1) (.var 3)) (.var 3))))) (.neg (.mul (.add (.add (.add .one .one) .one) .one) (.mul (.mul (.var 1) (.var 4)) (.var 4))))) (.mul (.add .one .one) (.mul (.var 2) (.var 3)))) (.mul (.add .one .one) (.mul (.var 2) (.var 4)))) (.mul (.add .one .one) (.mul (.var 3) (.var 4)))) (.mul (.add (.add (.add .one .one) .one) .one) (.mul (.mul (.var 1) (.var 2)) (.var 4)))) (.mul (.add (.add (.add .one .one) .one) .one) (.mul (.mul (.var 1) (.var 3)) (.var 4)))) (.mul (.add (.add (.add (.add (.add (.add (.add .one .one) .one) .one) .one) .one) .one) .one) (.mul (.mul (.mul (.var 3) (.var 4)) (.var 1)) (.var 1)))))) (.mul (.add (.add (.add (.var 0) .one) .one) .one) (.add (.add (.add (.add (.mul (.add .one .one) (.mul (.mul (.mul (.var 1) (.var 1)) (.var 3)) (.var 3))) (.mul (.add (.add (.add (.add (.add (.add (.add (.add (.add .one .one) .one) .one) .one) .one) .one) .one) .one) .one) (.mul (.mul (.mul (.mul (.mul (.var 1) (.var 1)) (.var 1)) (.var 1)) (.var 4)) (.var 4)))) (.neg (.mul (.add (.add (.add .one .one) .one) .one) (.mul (.mul (.mul (.var 2) (.var 4)) (.var 1)) (.var 1))))) (.neg (.mul (.add (.add (.add .one .one) .one) .one) (.mul (.mul (.mul (.mul (.var 3) (.var 4)) (.var 1)) (.var 1)) (.var 1))))) (.neg (.mul (.add .one .one) (.mul (.mul (.mul (.mul (.mul (.mul (.var 0) (.var 1)) (.var 1)) (.var 1)) (.var 1)) (.var 4)) (.var 4))))))) (by decide +kernel)) hA hB : ((1 + 1) + 1) * (((a₀ * a₀) + (a₁ * a₁)) + (a₂ * a₂)) = (((a₀ + a₁) + a₂) * ((a₀ + a₁) + a₂)) + ((1 + 1) * ((((a₀ + ((a₁ * (-h)) + (ν * (0 * h)))) + ((a₂ * (((-h) * (-h)) + (ν * (h * h)))) + (ν * (0 * (((-h) * h) + (h * (-h))))))) * ((a₀ + ((a₁ * (-h)) + (ν * (0 * h)))) + ((a₂ * (((-h) * (-h)) + (ν * (h * h)))) + (ν * (0 * (((-h) * h) + (h * (-h)))))))) + (-(ν * (((0 + ((a₁ * h) + (0 * (-h)))) + ((a₂ * (((-h) * h) + (h * (-h)))) + (0 * (((-h) * (-h)) + (ν * (h * h)))))) * ((0 + ((a₁ * h) + (0 * (-h)))) + ((a₂ * (((-h) * h) + (h * (-h)))) + (0 * (((-h) * (-h)) + (ν * (h * h))))))))))))
  refine ⟨Extension.Ext.ext ((red2i (Shell.Frame.RE.sound (Shell.Frame.look [ν, h, a₀, a₁, a₂]) (.add (.add (.add (.mul (.neg (.var 1)) (.neg (.var 1))) (.mul (.var 0) (.mul (.var 1) (.var 1)))) (.neg (.var 1))) .one) (.add (.add .zero (.mul (.add (.add (.var 1) (.var 1)) (.neg .one)) (.add (.neg .one) (.neg (.var 1))))) (.mul (.add (.add (.add (.var 0) .one) .one) .one) (.mul (.var 1) (.var 1)))) (by decide +kernel)) hA hB : ((((-h) * (-h)) + (ν * (h * h))) + (-h)) + 1 = 0)) ((red2i (Shell.Frame.RE.sound (Shell.Frame.look [ν, h, a₀, a₁, a₂]) (.add (.add (.add (.mul (.neg (.var 1)) (.var 1)) (.mul (.var 1) (.neg (.var 1)))) (.var 1)) .zero) (.add (.add .zero (.mul (.add (.add (.var 1) (.var 1)) (.neg .one)) (.neg (.var 1)))) (.mul (.add (.add (.add (.var 0) .one) .one) .one) .zero)) (by decide +kernel)) hA hB : ((((-h) * h) + (h * (-h))) + h) + 0 = 0)), hc, by rw [hc]; exact Extension.Ext.mul_conj _, hp, ?_⟩
  rw [hp, two_mul' ((a₀ + a₁ + a₂) * (a₀ + a₁ + a₂))]
  constructor
  · intro e
    apply add_right_cancel (c := (a₀ + a₁ + a₂) * (a₀ + a₁ + a₂))
    rw [add_comm, e]
  · intro e
    rw [e]

/-- 00:G16, 27:X10, 27:P8 — the hypotheses of `koide_extension` hold on every frame `p = 4κ + 1`, the Carrier included:
`h = 2κ + 1` has `h + h = 1`, and `ν = −3` has `ν + 3 = 0`. -/
theorem koide_half {κ : Nat} (hκ : p = 4 * κ + 1) :
    (ofNat (2 * κ + 1) : Shell p) + ofNat (2 * κ + 1) = 1 ∧ (-3 : Shell p) + 1 + 1 + 1 = 0 := by
  refine ⟨Shell.ext ?_, ?_⟩
  · show ((2 * κ + 1) % p + (2 * κ + 1) % p) % p = 1 % p
    rw [← FRC.Nat.add_mod _ _ _ Pos.pos]
    have e : (2 * κ + 1) + (2 * κ + 1) = p * 1 + 1 := by
      rw [Nat.mul_one, hκ, show 4 * κ = 2 * κ + 2 * κ from FRC.Nat.add_mul 2 2 κ]
      show Nat.succ ((2 * κ + 1) + 2 * κ) = Nat.succ (2 * κ + 2 * κ + 1)
      rw [Nat.succ_add]
    rw [e]; exact FRC.Nat.add_mul_mod_self_left 1 1 p Pos.pos
  · rw [three_eq]
    exact Shell.Frame.RE.sound (Shell.Frame.look ([] : List (Shell p)))
      (.add (.add (.add (.neg (.add (.add .one .one) .one)) .one) .one) .one) .zero (by decide +kernel)


/-! ## The electroweak counts: the Weinberg angle, the unification counts, the residue (27-fields, 16 October 2026)

The counting content of 27-fields' ledger, decided by the kernel on the sixteen of `gen16` and on small integers. -/

/-- 27:C6, 27:X4 — the Weinberg angle from the charge spectrum of one generation: over the sixteen states of `gen16`,
`Σ (6T₃)² = 72` and `Σ (6Q)² = 192`, so `Tr T₃² = 2`, `Tr Q² = 16/3` and `sin²θ_W = Tr T₃²/Tr Q² = 72/192 = 3/8`
(`72 · 8 = 192 · 3`). -/
theorem weinberg_angle :
    isum (gen16.map (fun S => (3 * t3h S) * (3 * t3h S))) = 72 ∧
    isum (gen16.map (fun S => q6 S * q6 S)) = 192 ∧
    72 * 8 = 192 * 3 := by
  decide +kernel

/-- 27:C9 — the unification counts: `dim SU(5) − dim (SU(3) × SU(2) × U(1)) = 24 − (8 + 3 + 1) = 12 = 2 · (3 · 2)`, the
colour–isospin off-block; the spinor `16 = 1 + 5 + 10`; `dim SO(10) = 10 · 9 / 2 = 45`. -/
theorem unification_counts :
    24 - (8 + 3 + 1) = 12 ∧ 12 = 2 * (3 * 2) ∧ 1 + 5 + 10 = 16 ∧ 10 * 9 = 2 * 45 := by
  decide

/-- `(n + 12) % k = n % k` when `k` divides `12` (`12 % k = 0`), from the shell's own modular arithmetic. -/
theorem mod_add_twelve (n k : Nat) (hk : 0 < k) (h12 : 12 % k = 0) : (n + 12) % k = n % k := by
  rw [FRC.Nat.add_mod n 12 k hk, h12, Nat.add_zero, FRC.Nat.mod_mod n k hk]

/-- A property of the naturals that holds below `12` and is carried by `n ↦ n + 12` holds everywhere: strong induction
with the step `n = (n − 12) + 12`. -/
theorem twelve_periodic {P : Nat → Prop} (base : ∀ r, r < 12 → P r) (step : ∀ m, P m → P (m + 12)) (n : Nat) : P n :=
  Nat.strongRecOn n fun n ih => by
    rcases Nat.lt_or_ge n 12 with h | h
    · exact base n h
    · have e : n - 12 + 12 = n := (Nat.add_comm (n - 12) 12).trans (FRC.Nat.add_sub_of_le h)
      rw [← e]
      exact step (n - 12) (ih (n - 12) (Nat.sub_lt (Nat.lt_of_lt_of_le (by decide) h) (by decide)))

/-- 27:C11 — `Ω ≡ 5 (mod 12)` is the conjunction `Ω ≡ 1 (mod 4)` and `Ω ≡ 2 (mod 3)`, for every natural number: the
twelve residues decide it, and the three moduli are periodic in `12`. -/
theorem residue_five (n : Nat) : n % 12 = 5 ↔ n % 4 = 1 ∧ n % 3 = 2 :=
  twelve_periodic (P := fun n => n % 12 = 5 ↔ n % 4 = 1 ∧ n % 3 = 2)
    (fun r hr => (by decide : ∀ r, r < 12 → (r % 12 = 5 ↔ r % 4 = 1 ∧ r % 3 = 2)) r hr)
    (fun m hm => by
      show (m + 12) % 12 = 5 ↔ (m + 12) % 4 = 1 ∧ (m + 12) % 3 = 2
      rw [mod_add_twelve m 12 (by decide) rfl, mod_add_twelve m 4 (by decide) rfl, mod_add_twelve m 3 (by decide) rfl]
      exact hm) n

/-- 27:C11 — the instances: the first eight admissible shells `5, 17, 29, 41, 53, 89, 101, 113` and the laboratory
Carrier `Ω = 2 408 561` (37-sim) read `5 (mod 12)`; the Koide carriers `13, 61, 157, 421` read `1 (mod 12)` and fail the
criterion. -/
theorem residue_instances :
    [5, 17, 29, 41, 53, 89, 101, 113, 2408561].all (fun n => n % 12 == 5 && n % 4 == 1 && n % 3 == 2) = true ∧
    [13, 61, 157, 421].all (fun n => n % 12 == 1 && n % 4 == 1 && n % 3 == 1) = true := by
  decide

/-- 27:C7, 27:X7 — the rank tower: for `Ω ≡ 5 (mod 12)` the cycle `Ω + 1 ≡ 6 (mod 12)` carries the ranks `1, 2, 3`,
`2 ∣ Ω + 1` and `3 ∣ Ω + 1`, and stops there: `Ω + 1 ≡ 2 (mod 4)`, so `4 ∤ Ω + 1` and `gcd(4, Ω + 1) = 2`. The colour
rank is `3`, the isospin rank `2`. -/
theorem rank_tower (n : Nat) (h : n % 12 = 5) : (n + 1) % 2 = 0 ∧ (n + 1) % 3 = 0 ∧ (n + 1) % 4 = 2 :=
  twelve_periodic (P := fun n => n % 12 = 5 → (n + 1) % 2 = 0 ∧ (n + 1) % 3 = 0 ∧ (n + 1) % 4 = 2)
    (fun r hr => (by decide : ∀ r, r < 12 → r % 12 = 5 → (r + 1) % 2 = 0 ∧ (r + 1) % 3 = 0 ∧ (r + 1) % 4 = 2) r hr)
    (fun m hm h12 => by
      show (m + 12 + 1) % 2 = 0 ∧ (m + 12 + 1) % 3 = 0 ∧ (m + 12 + 1) % 4 = 2
      rw [mod_add_twelve m 12 (by decide) rfl] at h12
      rw [Nat.add_right_comm m 12 1, mod_add_twelve (m + 1) 2 (by decide) rfl, mod_add_twelve (m + 1) 3 (by decide) rfl,
        mod_add_twelve (m + 1) 4 (by decide) rfl]
      exact hm h12) n h

/-! ## The neutral Hessian and the photon (27:C2, C5, X3, X5)

The neutral `(W₃, B)` mass block of the gauged Higgs action at the broken vacuum is `¼ v² [[g², −g g′], [−g g′, g′²]]`.
Cleared of the `¼`, its entries are ring expressions in `g, g′, v` on every shell, and the normaliser decides the
identities: the determinant vanishes and `(g′, g)` spans the kernel (the massless photon, the unbroken `U(1)`), and
`(g, −g′)` is the eigenvector of the eigenvalue `(g² + g′²) v²`, that is `4 M_Z² = (g² + g′²) v²`. The custodial `ρ = 1` is the
separate identity `M_W² (g² + g′²) = M_Z² g²` of the doublet's full Hessian, the `W` block `g² v²/4` against the `Z`
eigenvalue: `hessian_full` decides it on `𝔽₁₃` and `𝔽₅` from the four generators, as the ledger file's check C6 does. -/

/-- 27:C5, 27:X3, 27:X5 — the neutral Hessian, cleared of `¼`: with `m₀₀ = g² v²`, `m₀₁ = −g g′ v²`, `m₁₁ = g′² v²`,
`m₀₀ m₁₁ − m₀₁² = 0` (the massless photon); `(m₀₀, m₀₁) · (g′, g) = 0` and `(m₀₁, m₁₁) · (g′, g) = 0`; the block applied to
`(g, −g′)` returns `(g² + g′²) v² · (g, −g′)`. -/
theorem hessian_neutral (g g' v : Shell p) :
    g * g * (v * v) * (g' * g' * (v * v)) + -(-(g * g' * (v * v)) * -(g * g' * (v * v))) = 0 ∧
    g * g * (v * v) * g' + -(g * g' * (v * v)) * g = 0 ∧
    -(g * g' * (v * v)) * g' + g' * g' * (v * v) * g = 0 ∧
    g * g * (v * v) * g + -(g * g' * (v * v)) * -g' = (g * g + g' * g') * (v * v) * g ∧
    -(g * g' * (v * v)) * g + g' * g' * (v * v) * -g' = (g * g + g' * g') * (v * v) * -g' := by
  have hdet : g * g * (v * v) * (g' * g' * (v * v)) + -(-(g * g' * (v * v)) * -(g * g' * (v * v))) = 0 :=
    Shell.Frame.RE.sound (Shell.Frame.look [g, g', v]) (.add (.mul (.mul (.mul (.var 0) (.var 0)) (.mul (.var 2) (.var 2))) (.mul (.mul (.var 1) (.var 1)) (.mul (.var 2) (.var 2)))) (.neg (.mul (.neg (.mul (.mul (.var 0) (.var 1)) (.mul (.var 2) (.var 2)))) (.neg (.mul (.mul (.var 0) (.var 1)) (.mul (.var 2) (.var 2))))))) .zero (by decide +kernel)
  have hk1 : g * g * (v * v) * g' + -(g * g' * (v * v)) * g = 0 :=
    Shell.Frame.RE.sound (Shell.Frame.look [g, g', v]) (.add (.mul (.mul (.mul (.var 0) (.var 0)) (.mul (.var 2) (.var 2))) (.var 1)) (.mul (.neg (.mul (.mul (.var 0) (.var 1)) (.mul (.var 2) (.var 2)))) (.var 0))) .zero (by decide +kernel)
  have hk2 : -(g * g' * (v * v)) * g' + g' * g' * (v * v) * g = 0 :=
    Shell.Frame.RE.sound (Shell.Frame.look [g, g', v]) (.add (.mul (.neg (.mul (.mul (.var 0) (.var 1)) (.mul (.var 2) (.var 2)))) (.var 1)) (.mul (.mul (.mul (.var 1) (.var 1)) (.mul (.var 2) (.var 2))) (.var 0))) .zero (by decide +kernel)
  have he1 : g * g * (v * v) * g + -(g * g' * (v * v)) * -g' = (g * g + g' * g') * (v * v) * g :=
    Shell.Frame.RE.sound (Shell.Frame.look [g, g', v]) (.add (.mul (.mul (.mul (.var 0) (.var 0)) (.mul (.var 2) (.var 2))) (.var 0)) (.mul (.neg (.mul (.mul (.var 0) (.var 1)) (.mul (.var 2) (.var 2)))) (.neg (.var 1)))) (.mul (.mul (.add (.mul (.var 0) (.var 0)) (.mul (.var 1) (.var 1))) (.mul (.var 2) (.var 2))) (.var 0)) (by decide +kernel)
  have he2 : -(g * g' * (v * v)) * g + g' * g' * (v * v) * -g' = (g * g + g' * g') * (v * v) * -g' :=
    Shell.Frame.RE.sound (Shell.Frame.look [g, g', v]) (.add (.mul (.neg (.mul (.mul (.var 0) (.var 1)) (.mul (.var 2) (.var 2)))) (.var 0)) (.mul (.mul (.mul (.var 1) (.var 1)) (.mul (.var 2) (.var 2))) (.neg (.var 1)))) (.mul (.mul (.add (.mul (.var 0) (.var 0)) (.mul (.var 1) (.var 1))) (.mul (.var 2) (.var 2))) (.neg (.var 1))) (by decide +kernel)
  exact ⟨hdet, hk1, hk2, he1, he2⟩

/-- The entry of a list of pairs, `(0, 0)` past its end. -/
def pget : List (Shell p × Shell p) → Nat → Shell p × Shell p
  | [], _ => (0, 0)
  | x :: _, 0 => x
  | _ :: l, n + 1 => pget l n

/-- The four generators `(g/2) σ₁, (g/2) σ₂, (g/2) σ₃, (g′/2) 1` applied to the vacuum `(0, v)`: `X_a φ₀ = (A_a[0][1] v, A_a[1][1] v)`,
with `i` the unit `i² = −1` of the shell and `h = 1/2`. -/
def xphi (i g g' v h : Shell p) : List (Shell p × Shell p) :=
  [(g * h * v, 0), (-(i * (g * h)) * v, 0), (0, -(g * h) * v), (0, g' * h * v)]

/-- The Hessian `M_ab = (X_a φ₀)^† (X_b φ₀)`, the conjugate row with `−i`. -/
def hess (i g g' v h : Shell p) (a b : Nat) : Shell p :=
  (pget (xphi (-i) g g' v h) a).1 * (pget (xphi i g g' v h) b).1 + (pget (xphi (-i) g g' v h) a).2 * (pget (xphi i g g' v h) b).2

/-- 27:C5, 27:X5 — the full `4 × 4` Hessian of the gauged doublet on `𝔽₁₃` (`i = 5`, `g = 1`, `g′ = 2`, `v = 2`, `h = 7`) and on
`𝔽₅` (`i = 2`, `g = g′ = 1`, `v = 2`, `h = 3`): `(0, 0, g′, g)` is the kernel (the photon), `det (W₃, B) = 0`, `W₁` and `W₂`
are degenerate, the `(W₃, B)` trace is `M_Z² = (g² + g′²) v² h²`, and the custodial identity `M_W² (g² + g′²) = M_Z² g²`
(`ρ = 1`) holds with `M_W² = M₁₁`; `i² = −1` and `2h = 1` on both shells. -/
theorem hessian_full :
    ((List.range 4).all (fun a => hess (5 : Shell 13) 1 2 2 7 a 2 * 2 + hess (5 : Shell 13) 1 2 2 7 a 3 * 1 == 0)) = true ∧
    hess (5 : Shell 13) 1 2 2 7 2 2 * hess (5 : Shell 13) 1 2 2 7 3 3 + -(hess (5 : Shell 13) 1 2 2 7 2 3 * hess (5 : Shell 13) 1 2 2 7 3 2) = 0 ∧
    hess (5 : Shell 13) 1 2 2 7 0 0 = hess (5 : Shell 13) 1 2 2 7 1 1 ∧
    hess (5 : Shell 13) 1 2 2 7 2 2 + hess (5 : Shell 13) 1 2 2 7 3 3 = (1 * 1 + 2 * 2) * (2 * 2) * (7 * 7) ∧
    hess (5 : Shell 13) 1 2 2 7 0 0 * (1 * 1 + 2 * 2) = (hess (5 : Shell 13) 1 2 2 7 2 2 + hess (5 : Shell 13) 1 2 2 7 3 3) * (1 * 1) ∧
    (5 : Shell 13) * 5 = -1 ∧ (7 : Shell 13) + 7 = 1 ∧
    ((List.range 4).all (fun a => hess (2 : Shell 5) 1 1 2 3 a 2 * 1 + hess (2 : Shell 5) 1 1 2 3 a 3 * 1 == 0)) = true ∧
    hess (2 : Shell 5) 1 1 2 3 2 2 * hess (2 : Shell 5) 1 1 2 3 3 3 + -(hess (2 : Shell 5) 1 1 2 3 2 3 * hess (2 : Shell 5) 1 1 2 3 3 2) = 0 ∧
    hess (2 : Shell 5) 1 1 2 3 0 0 = hess (2 : Shell 5) 1 1 2 3 1 1 ∧
    hess (2 : Shell 5) 1 1 2 3 2 2 + hess (2 : Shell 5) 1 1 2 3 3 3 = (1 * 1 + 1 * 1) * (2 * 2) * (3 * 3) ∧
    hess (2 : Shell 5) 1 1 2 3 0 0 * (1 * 1 + 1 * 1) = (hess (2 : Shell 5) 1 1 2 3 2 2 + hess (2 : Shell 5) 1 1 2 3 3 3) * (1 * 1) ∧
    (2 : Shell 5) * 2 = -1 ∧ (3 : Shell 5) + 3 = 1 := by
  decide +kernel

theorem five_eq : (5 : Shell p) = 1 + 1 + 1 + 1 + 1 := by
  show ofNat 5 = ofNat 1 + ofNat 1 + ofNat 1 + ofNat 1 + ofNat 1
  rw [ofNat_add, ofNat_add, ofNat_add, ofNat_add]

theorem eight_eq : (8 : Shell p) = 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 := by
  show ofNat 8 = ofNat 1 + ofNat 1 + ofNat 1 + ofNat 1 + ofNat 1 + ofNat 1 + ofNat 1 + ofNat 1
  rw [ofNat_add, ofNat_add, ofNat_add, ofNat_add, ofNat_add, ofNat_add, ofNat_add]

/-- 27:C5 — `M_W²/M_Z² = cos²θ_W = 5/8`: `M_W² = g² v²/4` and `M_Z² = (g² + g′²) v²/4`, so the ratio is
`g²/(g² + g′²)`; where `sin²θ_W = g′²/(g² + g′²) = 3/8`, that is `8 g′² = 3 (g² + g′²)`, the ratio reads
`8 g² = 5 (g² + g′²)`, on every shell. -/
theorem five_eighths (g g' : Shell p) (h : 8 * (g' * g') = 3 * (g * g + g' * g')) :
    8 * (g * g) = 5 * (g * g + g' * g') := by
  rw [eight_eq, three_eq] at h
  rw [eight_eq, five_eq]
  have e : (1 + 1 + 1 + 1 + 1 + 1 + 1 + 1) * (g * g) = (1 + 1 + 1 + 1 + 1) * (g * g + g' * g') + ((1 + 1 + 1) * (g * g + g' * g') + -((1 + 1 + 1 + 1 + 1 + 1 + 1 + 1) * (g' * g'))) :=
    Shell.Frame.RE.sound (Shell.Frame.look [g, g']) (.mul (.add (.add (.add (.add (.add (.add (.add .one .one) .one) .one) .one) .one) .one) .one) (.mul (.var 0) (.var 0))) (.add (.mul (.add (.add (.add (.add .one .one) .one) .one) .one) (.add (.mul (.var 0) (.var 0)) (.mul (.var 1) (.var 1)))) (.add (.mul (.add (.add .one .one) .one) (.add (.mul (.var 0) (.var 0)) (.mul (.var 1) (.var 1)))) (.neg (.mul (.add (.add (.add (.add (.add (.add (.add .one .one) .one) .one) .one) .one) .one) .one) (.mul (.var 1) (.var 1)))))) (by decide +kernel)
  rw [e, ← h, add_neg, add_zero]

/-- 27:C2, 27:X3 — the photon's operator forced. A rotation-invariant quadratic symbol with constant part is
`σ(k) = a k k + b |k|² δ + c δ`; gauge invariance, `σ(k) k = 0` for every `k`, reads `((a + b) |k|² + c) k = 0`, and
its two evaluations at `|k|² = 1` and `|k|² = 2` give `a + b = 0` and `c = 0`: the symbol is `b (|k|² δ − k k)`, the
transverse projector, massless (`c = 0`) and unique up to the one coefficient. -/
theorem projector_forced (a b c : Shell p) (h1 : (a + b) * 1 + c = 0) (h2 : (a + b) * (1 + 1) + c = 0) :
    a + b = 0 ∧ c = 0 := by
  have e1 : a + b = (a + b) * (1 + 1) + c + -((a + b) * 1 + c) :=
    Shell.Frame.RE.sound (Shell.Frame.look [a, b, c]) (.add (.var 0) (.var 1)) (.add (.add (.mul (.add (.var 0) (.var 1)) (.add .one .one)) (.var 2)) (.neg (.add (.mul (.add (.var 0) (.var 1)) .one) (.var 2)))) (by decide +kernel)
  have e2 : c = (a + b) * 1 + c + -(a + b) :=
    Shell.Frame.RE.sound (Shell.Frame.look [a, b, c]) (.var 2) (.add (.add (.mul (.add (.var 0) (.var 1)) .one) (.var 2)) (.neg (.add (.var 0) (.var 1)))) (by decide +kernel)
  rw [h1, h2, neg_zero, add_zero] at e1
  rw [h1, e1, neg_zero, add_zero] at e2
  exact ⟨e1, e2⟩

/-! ## The lattice identities: Stokes and gauge invariance on `ℤ/M` (27:C2, X2)

The link variables of a `U(1)` connection on the cubic lattice take values in the phase cycle `ℤ/M`, read here on the
shell `Shell M` (any positive modulus). The two identities of the discrete calculus are ring identities in the link
variables, decided by the normaliser. -/

/-- 27:X2, 27:C2 — discrete Stokes on a `2 × 1` rectangle: the holonomy of the boundary loop, `A₁ + A₂ + B₃ − A₄ − A₅ − B₀`
(two bottom links, the right link, two top links, the left link), equals the sum of the two enclosed plaquette fluxes
`F₁ = A₁ + B₁ − A₅ − B₀` and `F₂ = A₂ + B₃ − A₄ − B₁`, the shared link `B₁` cancelling; the holonomy is additive over
adjacent loops. -/
theorem holonomy_stokes (A₁ A₂ B₃ A₄ A₅ B₀ B₁ : Shell p) :
    A₁ + A₂ + B₃ + -A₄ + -A₅ + -B₀ = A₁ + B₁ + -A₅ + -B₀ + (A₂ + B₃ + -A₄ + -B₁) :=
  Shell.Frame.RE.sound (Shell.Frame.look [A₁, A₂, B₃, A₄, A₅, B₀, B₁]) (.add (.add (.add (.add (.add (.var 0) (.var 1)) (.var 2)) (.neg (.var 3))) (.neg (.var 4))) (.neg (.var 5))) (.add (.add (.add (.add (.var 0) (.var 6)) (.neg (.var 4))) (.neg (.var 5))) (.add (.add (.add (.var 1) (.var 2)) (.neg (.var 3))) (.neg (.var 6)))) (by decide +kernel)

/-- 27:C2, 27:X1 — gauge invariance of the plaquette flux: with the corner gauges `φ₀, φ₁, φ₂, φ₃` and the links
`A: 0 → 1`, `B: 1 → 2`, `C: 3 → 2`, `D: 0 → 3`, the transformed links `A + φ₁ − φ₀`, `B + φ₂ − φ₁`, `C + φ₂ − φ₃`,
`D + φ₃ − φ₀` carry the flux `A + B − C − D` of the original. -/
theorem gauge_flux_invariant (A B C D φ₀ φ₁ φ₂ φ₃ : Shell p) :
    A + φ₁ + -φ₀ + (B + φ₂ + -φ₁) + -(C + φ₂ + -φ₃) + -(D + φ₃ + -φ₀) = A + B + -C + -D :=
  Shell.Frame.RE.sound (Shell.Frame.look [A, B, C, D, φ₀, φ₁, φ₂, φ₃]) (.add (.add (.add (.add (.add (.var 0) (.var 5)) (.neg (.var 4))) (.add (.add (.var 1) (.var 6)) (.neg (.var 5)))) (.neg (.add (.add (.var 2) (.var 6)) (.neg (.var 7))))) (.neg (.add (.add (.var 3) (.var 7)) (.neg (.var 4))))) (.add (.add (.add (.var 0) (.var 1)) (.neg (.var 2))) (.neg (.var 3))) (by decide +kernel)

/-! ## The V − A current and the chiral projector (27:C4, C7, C9, C10, X6)

The boost cycle `C_{q+1}` is read on a prime shell as a root `u` of order `N`; the drive advances the phase by `2δ`
per chronon. Over one period the drive-aligned branch sums to `N` and the counter-aligned branch to `0` unless
`u^{2δ} = 1`: the geometric sum against `u^{2δ} − 1` telescopes to `u^{2δN} − 1 = 0`, and a prime shell has no zero
divisors. -/

/-- 27:C4, 27:X6 — the V − A cancellation: on a prime shell, for `u^N = 1` and `u^{2δ} ≠ 1`,
`Σ_{τ<N} u^{2δτ} = 0` (the counter-aligned branch) while `Σ_{τ<N} 1 = N` (the aligned branch). -/
theorem va_cancel (hp : FRC.Nat.isPrime p) {u : Shell p} {N : Nat} (hu : u ^ N = 1) {δ : Nat}
    (hδ : u ^ (2 * δ) ≠ 1) :
    sumRange (fun τ => u ^ (2 * δ * τ)) N = 0 ∧ sumRange (fun _ => (1 : Shell p)) N = ofNat N := by
  constructor
  · have e : sumRange (fun τ => u ^ (2 * δ * τ)) N = sumRange (fun τ => (u ^ (2 * δ)) ^ τ) N :=
      sum_congr N (fun τ _ => pow_mul u (2 * δ) τ)
    have hg := geom_sum_mul (u ^ (2 * δ)) N
    rw [pow_mul_comm, hu, one_pow, add_neg] at hg
    rw [e]
    rcases Prime.mul_eq_zero hp hg with h | h
    · exact h
    · exact absurd (by rw [eq_neg_of_add_eq_zero h, neg_neg]) hδ
  · clear hu hδ
    induction N with
    | zero => rfl
    | succ n ih => rw [sumRange_succ, ih]; exact ofNat_add n 1

/-- The chiral projector `P_L = diag(1, 0)` is idempotent and annihilates the right branch, `P_L (ψ_L, ψ_R) = (ψ_L, 0)`:
ring axioms, corroboration only — the projector's content, `(1/N) Σ_τ diag(1, u^{2δτ}) = diag(1, 0)`, is `va_cancel`'s. -/
theorem projector_idempotent (x y : Shell p) :
    (1 : Shell p) * 1 = 1 ∧ (0 : Shell p) * 0 = 0 ∧ 1 * x = x ∧ 0 * y = 0 :=
  ⟨mul_one 1, mul_zero 0, one_mul x, zero_mul y⟩

/-- 27:C4, 27:X6 — the orientation convention `ε ↦ −ε` relabels the branches and leaves the selection: the inverse exponent
`2(N − δ)` is as far from the identity as `2δ` (`u^{2δ} u^{2(N−δ)} = u^{2N} = 1`), so its branch sums to `0` too; the
two conventions disagree on the label (`1 ≠ −1`) and agree that the coupled branch is the drive-aligned one
(`ε · ε > 0` for both signs). -/
theorem orientation_flip (hp : FRC.Nat.isPrime p) {u : Shell p} {N : Nat} (hu : u ^ N = 1) {δ : Nat}
    (hδN : δ ≤ N) (hδ : u ^ (2 * δ) ≠ 1) :
    sumRange (fun τ => u ^ (2 * (N - δ) * τ)) N = 0 ∧
    ((1 : Int) ≠ -1 ∧ (1 : Int) * 1 > 0 ∧ (-1 : Int) * -1 > 0) := by
  refine ⟨?_, by decide⟩
  have h' : u ^ (2 * (N - δ)) ≠ 1 := fun e => hδ (by
    have h2 : u ^ (2 * δ) = u ^ (2 * δ) * u ^ (2 * (N - δ)) := by rw [e, mul_one]
    rw [h2, ← pow_add, ← _root_.Nat.mul_add, FRC.Nat.add_sub_of_le hδN, _root_.Nat.mul_comm, pow_mul, hu, one_pow])
  exact (va_cancel hp hu h').1

/-! ## The breaking over `𝔽₁₃`: the drive's adjoint action (27:C4)

`2 × 2` matrices over the shell as quadruples `(a, b, c, d)`; the drive `δ = diag(2, 7)` of `𝔽₁₃` (`2 · 7 = 14 ≡ 1`)
acts by conjugation on `𝔰𝔩₂`: it fixes `H = diag(1, −1)` and scales `E` by `g² = 4` and `F` by `g⁻² = 10`; its
centraliser in `SL₂(𝔽₁₃)` is the split torus of order `12 = p − 1`. -/

/-- The product of `2 × 2` matrices over the shell, as quadruples. -/
def m2 (X Y : Shell p × Shell p × Shell p × Shell p) : Shell p × Shell p × Shell p × Shell p :=
  (X.1 * Y.1 + X.2.1 * Y.2.2.1, X.1 * Y.2.1 + X.2.1 * Y.2.2.2,
   X.2.2.1 * Y.1 + X.2.2.2 * Y.2.2.1, X.2.2.1 * Y.2.1 + X.2.2.2 * Y.2.2.2)

/-- The quadruple of the residues `(a, b, c, d)` of a number `n < p⁴`. -/
def m2of (n : Nat) : Shell p × Shell p × Shell p × Shell p :=
  (ofNat (n % p), ofNat (n / p % p), ofNat (n / (p * p) % p), ofNat (n / (p * p * p)))

/-- 27:C4, 27:X1 — the drive `δ = diag(2, 7)` of `𝔽₁₃` (`δ⁻¹ = diag(7, 2)`): `Ad_δ H = H`, `Ad_δ E = 4 E`, `Ad_δ F = 10 F` with
`4 · 10 ≡ 1`; the centraliser of `δ` in `SL₂(𝔽₁₃)` has `12` elements (the split torus); the non-split torus element
`[[3, 4], [2, 3]]` (`a = 3, b = 2, ν = 2`, `a² − ν b² = 1`) does not commute with the drive. -/
theorem drive_adjoint :
    m2 (2, 0, 0, 7) (7, 0, 0, (2 : Shell 13)) = (1, 0, 0, 1) ∧
    m2 (m2 (2, 0, 0, 7) (1, 0, 0, 12)) (7, 0, 0, (2 : Shell 13)) = (1, 0, 0, 12) ∧
    m2 (m2 (2, 0, 0, 7) (0, 1, 0, 0)) (7, 0, 0, (2 : Shell 13)) = (0, 4, 0, 0) ∧
    m2 (m2 (2, 0, 0, 7) (0, 0, 1, 0)) (7, 0, 0, (2 : Shell 13)) = (0, 0, 10, 0) ∧
    (4 : Shell 13) * 10 = 1 ∧
    ((List.range (13 * 13 * 13 * 13)).filter (fun n =>
      let X := m2of (p := 13) n
      X.1 * X.2.2.2 + -(X.2.1 * X.2.2.1) == 1 && m2 X (2, 0, 0, 7) == m2 (2, 0, 0, 7) X)).length = 12 ∧
    m2 (3, 4, 2, 3) (2, 0, 0, 7) ≠ m2 (2, 0, 0, 7) (3, 4, 2, (3 : Shell 13)) := by
  decide +kernel

/-! ## The colour–isospin reframings as automorphisms (27:C9, X8, 00:Z5)

A reframing that exchanges a colour direction `c ∈ {0, 1, 2}` with a weak direction `w ∈ {3, 4}` is a relabelling of the
five directions; on the reflection algebra it acts on the basis `e_S ↦ e_{τS}`, and the product is covariant up to the
sign of the basis element: `e_{τS} e_{τT} = ± e_{τ(S∪T)}` exactly when `e_S e_T = ± e_{S∪T}`. The six off-block
transpositions are therefore automorphisms of the algebra up to sign, the `3 + 2` split invisible to the product. -/

/-- The transposition `(c w)` on the five directions. -/
def tr (c w i : Nat) : Nat := if i == c then w else if i == w then c else i

/-- The relabelled subset: `S ↦ Σ_{i ∈ S} 2^{τ i}`. -/
def act (c w S : Nat) : Nat := ((List.range 5).map (fun i => if bit S i then 2 ^ tr c w i else 0)).foldl (· + ·) 0

/-- The six colour–isospin transpositions `(c w)`, `c ∈ {0, 1, 2}`, `w ∈ {3, 4}`. -/
def offblock : List (Nat × Nat) := [(0, 3), (0, 4), (1, 3), (1, 4), (2, 3), (2, 4)]

/-- 27:C9, 27:X8, 00:Z5 — each colour–isospin transposition is an automorphism of the reflection algebra of five directions
up to the sign of the basis element: for all `S, T < 32`, `e_{τS} e_{τT}` vanishes exactly when `e_S e_T` does, and
otherwise is `± e_{τ(S∪T)}`; the relabelling is a bijection of the `32` subsets. -/
theorem offblock_automorphism :
    offblock.all (fun cw => (List.range 32).all (fun S => (List.range 32).all (fun T =>
      let a := emul S T
      let b := emul (act cw.1 cw.2 S) (act cw.1 cw.2 T)
      b.1 * b.1 == a.1 * a.1 && (a.1 == 0 || b.2 == act cw.1 cw.2 a.2)))) = true ∧
    offblock.all (fun cw => (List.range 32).all (fun S => (List.range 32).all (fun T =>
      act cw.1 cw.2 S == act cw.1 cw.2 T → S == T)) && (List.range 32).all (fun S => act cw.1 cw.2 S < 32)) = true := by
  decide +kernel

end FRC.Interactions
