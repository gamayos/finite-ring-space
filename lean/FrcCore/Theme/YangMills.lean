import FrcCore.Theme.Brackets
import FrcCore.Theme.Extension
import FrcCore.Theme.Hadrons

/-!
# FrcCore.Theme.YangMills — the yangmills theme (46-yangmills, 7–8 November 2026)

The exact content of *Yang–Mills and the Mass Gap over Finite Holographic Substrate* (tree `46-yangmills-20261107`) above
the extension, frame and hadrons themes and the window fractions of `Theme/Brackets.lean`, as `frc/yangmills.py`, `frc/chart_yangmills.py` and
`frc/ledgers/p46_yangmills.py` compute it. Each theorem over a frame is a schema, instantiated on a shell of the totality
(`p < √Ω`); the sweeps are bounded; every number is a natural number, an integer, a residue on the shell or a window fraction
(1:D8, a pair of an integer and a positive natural read as the residue `a·b⁻¹` on every shell whose window holds it),
and every comparison is a comparison of cross-products in the integers. Colour's triality is the Carrier's relation
`Ω ≡ 5 (mod 12)` (46:B5). The Subject reads colour in its unitary frame, `SU(3)` over the Subject's quadratic extension, whose
centre has order three where `3 ∣ p + 1`.

The registrations (46:C1–C3): a norm-one element `a + b√ν` of the shell's quadratic extension with `b ≠ 0` has no eigenvalue
in the shell (`no_shell_eigenvalue`, the norm-one cycle fixes no line, the gluon's residue is `0`), the split torus fixes
exactly the two coordinate lines (`split_fixed_lines`, the photon's residue `2`); the centre of `SU(3, 𝔽_q)` has order
`gcd(3, q + 1)`, `3` exactly where `3 ∣ q + 1` (`centre_sweep`, `lab_centres`, `full_centre_sweep` — the
arithmetic of the order formula, the formula itself 27-fields Proposition su3), and the three laboratory Carriers are
`5 (mod 12)` (`carrier_triality`); the residue series on the instance
by the singlet multiplicities (`glueball_singlet` on the hadrons theme's constant terms, `residue_series_pieri` on the Pieri
multiplicities, `mult_moment6` tying the two). The Casimir and one-loop rationals with denominators cleared (`casimirs`,
`b0_values`, `b0_pos`, `b0_seventeen`, `b0_neg`, 46:C4, C5) and the Casimirs from the frame's torus exponents on the three Subjects
(`casimir_exponents`, 46:C4, no lift); the drive exponent (`drive_exponent`, `drive_exponent_unique`,
`drive_exponent_add`, 46:C6). The tension's coefficient (46:C7): the singlet multiplicities of `𝟛^{⊗m} ⊗ 𝟛̄^{⊗n}` by the
Pieri rule on Dynkin labels (`mult`, `moments`), the plaquette coefficient `c₃` to `ϑ⁷` as window fractions
(`c3_fractions`) and as residues on the three laboratory Subjects and the `20` shells `13 ≤ p < 200` (`c3_readback`, every
division an inverse on the shell), the `SU(2)` series beside the instance `2T = SU(2, 𝔽₃)` from its `24` Hurwitz units
(`c2_lab`). The adjoint wrap's two plaquette layers (`adjoint_two_sheets`, 46:C9). The chains of the logarithm (the artanh
chain with its geometric majorant, `lnBr`) and the six-place bracket of `π` (`piBr`), both in `Theme/Brackets.lean`, read the chart's constants as
brackets of window fractions, and decide: the declared coupling against the Herbst value, `π² > 6 ln 2`
(`herbst_comparison`, 46:C10); the plaquette channel's ratio and spread at channel unity (`plaquette_cells`, 46:C11); the
one-loop run from `M_Z` to `m_τ` (`running_one_loop`, 46:P2). The family of the minimal wrap against the lattice in
thousandths (`wrap_family`, 46:C12) and the colour factors against LEP in hundredths (`colour_factors_within`, 46:P1, X4)
are integer comparisons. The adjoint without an invariant line (`adjoint_no_invariant`, 46:X1). The two rationals of the
one-loop coefficient (46:C13): the spin traces on the shell's modules (`spin_traces`), the Faulhaber third with its complete
cycle vanishing (`faulhaber_third`, `faulhaber_residues`, `complete_cycle_vanishes`) and the species sum of Hughes–Nielsen
with denominators cleared (`hughes_nielsen_sum`). The radial ratio of the operator form against the lattice, the Airy
ladder and the nucleon, in thousandths (`radial_ratio`, 46:P3). The frame's window, the spectral amplitude of a plaquette, the transfer tally and the tallies of the ring
(46:A9, C15 to C27) are in `Theme/Plaquette.lean`, the theme's third core file (13 November 2026). No axioms.
-/

namespace FRC.YangMills

open FRC.Shell FRC.Shell.Frame

variable {p : Nat} [Pos p] {κ : Nat} {g : Shell p}

/-! ## The norm-one cycle fixes no line (46:C1) -/

/-- 46:C1, 46:X1 — a norm-one element `a + b√ν` of the extension with `b ≠ 0`, `ν` a nonsquare, has no eigenvalue in the shell: a
root `r` of its characteristic polynomial `x² − 2a x + 1` would give `(r − a)² = a² − 1 = ν b²`, so `ν = ((r − a)/b)²`, a
square. Hence a non-scalar element of the norm-one cycle fixes no line of the shell plane, and the cycle fixes none: the
gluon, the residue `0` of the norm-one cycle, is never registered alone. -/
theorem no_shell_eigenvalue (F : Frame p κ g) {ν a b r : Shell p} (hν : ¬IsSquare ν)
    (h : a * a + -(ν * (b * b)) = 1) (hb : b ≠ 0) (hr : r * r + -((a + a) * r) + 1 = 0) : False := by
  -- (r − a)² = (r² − 2ar + 1) + (a² − νb² − 1) + νb²
  have e1 : (r + -a) * (r + -a) = (r * r + -((a + a) * r) + 1) + (a * a + -(ν * (b * b)) + -1) + ν * (b * b) :=
    RE.sound (look [r, a, ν, b])
      (.mul (.add (.var 0) (.neg (.var 1))) (.add (.var 0) (.neg (.var 1))))
      (.add (.add (.add (.add (.mul (.var 0) (.var 0)) (.neg (.mul (.add (.var 1) (.var 1)) (.var 0)))) .one)
                  (.add (.add (.mul (.var 1) (.var 1)) (.neg (.mul (.var 2) (.mul (.var 3) (.var 3))))) (.neg .one)))
            (.mul (.var 2) (.mul (.var 3) (.var 3))))
      (by decide +kernel)
  have e2 : (r + -a) * (r + -a) = ν * (b * b) := by
    rw [e1, hr, h, zero_add, add_neg, zero_add]
  match F.exists_inv hb with
  | ⟨s, hs⟩ =>
    exact hν ⟨(r + -a) * s, by
      calc (r + -a) * s * ((r + -a) * s) = ((r + -a) * (r + -a)) * (s * s) := sq_mul _ _
        _ = (ν * (b * b)) * (s * s) := by rw [e2]
        _ = ν * ((b * s) * (b * s)) := by rw [mul_assoc, sq_mul b s]
        _ = ν := by rw [hs, one_mul, mul_one]⟩

/-- 46:C1 — the two scalars `±1` are the only norm-one elements with `b = 0`: `a² = 1` forces `a = ±1`. -/
theorem scalar_of_im_zero (F : Frame p κ g) {ν a b : Shell p} (h : a * a + -(ν * (b * b)) = 1) (hb : b = 0) :
    a = 1 ∨ a = -1 := by
  rw [hb, mul_zero, mul_zero, neg_zero, add_zero] at h
  exact F.sq_eq_one h

/-- 46:C1 — the split torus `diag(g, g⁻¹)` fixes exactly the two coordinate lines of the projective line: a point `[x : y]` is
fixed iff `g x · y = x · g⁻¹ y`, i.e. `(g² − 1) x y = 0`, i.e. `x y = 0` since `g² ≠ 1` (the drive is primitive of order
`p − 1 > 2`). The photon's two helicities, residue `2`. -/
theorem split_fixed_lines (F : Frame p κ g) {x y s : Shell p} (hs : g * s = 1) :
    (g * x) * y = x * (s * y) ↔ x * y = 0 := by
  have hg2 : g * g ≠ 1 := fun e => by
    have h2 : (2 : Nat) < p - 1 := Nat.lt_of_le_of_lt (Nat.mul_le_mul_left 2 F.cap_pos) F.two_kappa_lt
    exact F.prim.2 2 h2 (by decide) (by rw [pow_succ, pow_one, e])
  constructor
  · intro e
    -- g x y = x s y, multiply by g: g² x y = x (g s) y = x y, so (g² − 1) x y = 0 with g² − 1 ≠ 0
    have e3 : (g * g) * (x * y) = x * y := by
      have i1 : (g * g) * (x * y) = g * ((g * x) * y) :=
        RE.sound (look [g, x, y]) (.mul (.mul (.var 0) (.var 0)) (.mul (.var 1) (.var 2)))
          (.mul (.var 0) (.mul (.mul (.var 0) (.var 1)) (.var 2))) (by decide +kernel)
      have i2 : g * (x * (s * y)) = (g * s) * (x * y) :=
        RE.sound (look [g, x, s, y]) (.mul (.var 0) (.mul (.var 1) (.mul (.var 2) (.var 3))))
          (.mul (.mul (.var 0) (.var 2)) (.mul (.var 1) (.var 3))) (by decide +kernel)
      rw [i1, e, i2, hs, one_mul]
    have e4 : (g * g + -1) * (x * y) = 0 := by
      rw [right_distrib, e3, neg_one_mul, add_neg]
    match F.mul_eq_zero e4 with
    | .inl e5 =>
      exact absurd (calc g * g = g * g + (-1 + 1) := by rw [neg_add, add_zero]
        _ = (g * g + -1) + 1 := (add_assoc _ _ _).symm
        _ = 1 := by rw [e5, zero_add]) hg2
    | .inr e5 => exact e5
  · intro e
    -- x y = 0 gives x = 0 or y = 0, and both sides vanish
    match F.mul_eq_zero e with
    | .inl hx => rw [hx, mul_zero, zero_mul, zero_mul]
    | .inr hy => rw [hy, mul_zero, mul_zero, mul_zero]

/-! ## The centre of the unitary frame and the Carrier's triality (46:C2) -/

/-- 46:C2 — the arithmetic of the centre's order formula. Given that the centre of `SU(3, 𝔽_q)` is the norm-one cube roots
of unity, `gcd(3, q + 1)` of them (27-fields Proposition su3, imported, not proved here), on every shell of the sweep below
`200`, `q ≡ 5 (mod 12)` gives `Z₃` and `q ≡ 1 (mod 12)` the trivial centre, and the residue `q ≡ 5 (mod 12)` is
exactly `q ≡ 1 (mod 4)` (a shell) with `q ≡ 2 (mod 3)` (the centre of order three). Kernel-decided over the range, so that no
library lemma on `gcd` or `%` (which carry `propext`) enters. -/
theorem centre_sweep :
    ∀ q, q < 200 → (q % 12 = 5 → Nat.gcd 3 (q + 1) = 3) ∧ (q % 12 = 1 → Nat.gcd 3 (q + 1) = 1) ∧
      (q % 12 = 5 ↔ q % 4 = 1 ∧ q % 3 = 2) := by
  decide +kernel

/-- 46:C2 — the laboratory Subjects: `173 ≡ 5 (mod 12)` has the centre `Z₃`; `13` and `1549`, both `≡ 1 (mod 12)`, have
the trivial centre. -/
theorem lab_centres :
    Nat.gcd 3 (13 + 1) = 1 ∧ Nat.gcd 3 (173 + 1) = 3 ∧ Nat.gcd 3 (1549 + 1) = 1 ∧
    13 % 12 = 1 ∧ 173 % 12 = 5 ∧ 1549 % 12 = 1 := by
  decide

/-- 46:C2 — of the `21` shells `p = 4κ + 1` below `200`, the `12` with `p ≡ 5 (mod 12)` carry the centre `Z₃` and the other
`9` do not. -/
theorem full_centre_sweep :
    ([5, 17, 29, 41, 53, 89, 101, 113, 137, 149, 173, 197].all fun q => q % 12 == 5 && Nat.gcd 3 (q + 1) == 3) = true ∧
    ([13, 37, 61, 73, 97, 109, 157, 181, 193].all fun q => q % 12 == 1 && Nat.gcd 3 (q + 1) == 1) = true ∧
    [5, 17, 29, 41, 53, 89, 101, 113, 137, 149, 173, 197].length + [13, 37, 61, 73, 97, 109, 157, 181, 193].length = 21 := by
  decide

/-- 46:C2, 46:B5 — colour's triality is the Carrier's relation: each of the three laboratory Carriers is `5 (mod 12)`, so `3`
divides `Ω + 1` and not `Ω − 1`. The cube roots of unity are the pairs `(0, 1)` and `(−1, −1)` of residues, `a + bω` with
`ω² = −ω − 1` and the norm `a² − ab + b²`: both have norm `1`, `(0, 1)² = (−1, −1)` and `(0, 1)·(−1, −1) = (1, 0)`. The product
of `(a, b)` and `(c, d)` is `(ac − bd, ad + bc − bd)`. -/
theorem carrier_triality :
    233 % 12 = 5 ∧ 30089 % 12 = 5 ∧ 2408561 % 12 = 5 ∧
    (233 + 1) % 3 = 0 ∧ (30089 + 1) % 3 = 0 ∧ (2408561 + 1) % 3 = 0 ∧
    (233 - 1) % 3 = 1 ∧ (30089 - 1) % 3 = 1 ∧ (2408561 - 1) % 3 = 1 ∧
    ((0 : Int) * 0 - 0 * 1 + 1 * 1 = 1 ∧ (-1 : Int) * (-1) - (-1) * (-1) + (-1) * (-1) = 1) ∧
    ((0 : Int) * 0 - 1 * 1 = -1 ∧ (0 : Int) * 1 + 1 * 0 - 1 * 1 = -1) ∧
    ((0 : Int) * (-1) - 1 * (-1) = 1 ∧ (0 : Int) * (-1) + 1 * (-1) - 1 * (-1) = 0) := by
  decide

/-! ## The residue series on the instance (46:C3) -/

/-- 46:C3, 46:X2 — by the singlet multiplicities of the tensor powers of the triplet (the hadrons theme's `moment6`, six
times the multiplicity, computed as the constant term of the Weyl character polynomial — exact integers): the adjoint
has no invariant (`E[χχ̄] − 1 = 0`, the gluon's residue `0`), `𝟛 ⊗ 𝟛 ⊗ 𝟛` has one singlet (`E[χ³] = 1`, the baryon),
`𝟛 ⊗ 𝟛̄` one (`E[χχ̄] = 1`, the meson), and `𝟠 ⊗ 𝟠` one (`E[(χχ̄ − 1)²] = E[χ²χ̄²] − 2E[χχ̄] + 1 = 2 − 2 + 1 = 1`, the glueball):
photon `2`, gluon `0`, baryon `1`, meson `1`, glueball `1`. -/
theorem glueball_singlet :
    FRC.Hadrons.moment6 1 1 - 6 = 0 ∧ FRC.Hadrons.moment6 3 0 = 6 * 1 ∧ FRC.Hadrons.moment6 1 1 = 6 * 1 ∧
    FRC.Hadrons.moment6 2 2 - 2 * FRC.Hadrons.moment6 1 1 + 6 = 6 * 1 := by
  decide +kernel

/-! ## The adjoint wrap (46:C9, Phase 2)

The plaquette coefficient of a representation `R` is computed to order `ϑ⁷` with coefficients that are rationals built from
the singlet multiplicities `E[χ^a χ̄^b]` of the tensor powers of the triplet (`frc/yangmills.py`). For the adjoint, `χ₈ = χχ̄ − 1`,
the `ϑ¹` coefficient is `E[χ₈ Re χ]`, which vanishes (the trivial representation occurs `0` times in `𝟠 ⊗ 𝟛` and in `𝟠 ⊗ 𝟛̄`), and
the `ϑ²` coefficient is `E[χ₈ (Re χ)²] = (E[χ³χ̄] + 2E[χ²χ̄²] + E[χχ̄³] − E[χ²] − 2E[χχ̄] − E[χ̄²])/4 = (0 + 4 + 0 − 0 − 2 − 0)/4 = 1/2`:
the adjoint coefficient is `ϑ²/8 + …`, the square of the fundamental's `ϑ/3` up to the factor `9/8` — the adjoint wrap
needs two fundamental plaquette layers. Both multiplicity identities below are decided by the kernel on the constant terms;
the same two numbers hold on the enumerable instance `SU(3, 𝔽₂)` over `𝔽₄` by enumeration (ledger check F1). -/

/-- 46:C9 — the two multiplicity identities of the adjoint wrap: the `ϑ¹` coefficient of the adjoint plaquette coefficient
vanishes (`E[χ²χ̄] + E[χχ̄²] − E[χ] − E[χ̄] = 0`, no singlet in `𝟠 ⊗ 𝟛` or `𝟠 ⊗ 𝟛̄`), and `4 E[(χχ̄ − 1)(Re χ)²] = 2`
(`E[χ³χ̄] + 2E[χ²χ̄²] + E[χχ̄³] − E[χ²] − 2E[χχ̄] − E[χ̄²] = 2`), so `c₈ = ϑ²/8 + …`, the square of `c₃`'s `ϑ/3` up to
the factor `9/8`: the adjoint wrap is two fundamental wraps. Stated on the sixfold multiplicities `moment6`. -/
theorem adjoint_two_sheets :
    FRC.Hadrons.moment6 2 1 + FRC.Hadrons.moment6 1 2 - FRC.Hadrons.moment6 1 0 - FRC.Hadrons.moment6 0 1 = 0 ∧
    FRC.Hadrons.moment6 3 1 + 2 * FRC.Hadrons.moment6 2 2 + FRC.Hadrons.moment6 1 3
      - FRC.Hadrons.moment6 2 0 - 2 * FRC.Hadrons.moment6 1 1 - FRC.Hadrons.moment6 0 2 = 6 * 2 := by
  decide +kernel

/-! ## The Casimirs and the window rational (46:C4, C5) -/

/-- 46:C4, 46:X4, 46:P1 — the Casimirs of the unitary frame with denominators cleared: `2N C_F = N² − 1` gives `6 C_F = 8` (`C_F = 4/3`),
`C_A = N = 3`, `2 T_F = 1`, and `C_A / C_F = 2N² / (N² − 1)` gives `8 (C_A/C_F) = 18` (`9/4`). -/
theorem casimirs :
    (3 * 3 - 1 : Int) = 8 ∧ 6 * 4 = 3 * 8 ∧ (2 * 3 * 3 : Int) = 18 ∧ 8 * 9 = 4 * 18 ∧ 2 * 1 = 2 := by
  decide

/-- 46:C4 — the Casimir rationals from the frame's torus exponents, with no lift (round 03, 9 November 2026). A torus element of the
unitary frame acts on the fundamental with the eigenvalue exponents `(a, b, −a−b)` and on the adjoint with their six differences and
two zeros; the second moment of the adjoint's exponents is six times the fundamental's, `2((a−b)² + (2a+b)² + (a+2b)²) =
6(a² + b² + (a+b)²)`, which is `T_A/T_F = 6` and hence `C_A/C_F = 9/4`. On the Subject `13` the split torus has the exponents
`(n, 12n, −13n)` modulo `168`: `2((11n)² + (14n)² + (25n)²) = 6(n² + (12n)² + (13n)²)` for every `n < 168` (`1884 n² = 6 · 314 n²`);
at `n = 1` likewise on `173` (`(1, 172, −173)`) and `1549` (`(1, 1548, −1549)`). The identity for every exponent pair is the
Mathlib cell `YangMillsML.casimir_exponents_all`. -/
theorem casimir_exponents :
    (List.range 168).all (fun n => 2 * ((11 * n) ^ 2 + (14 * n) ^ 2 + (25 * n) ^ 2) == 6 * (n ^ 2 + (12 * n) ^ 2 + (13 * n) ^ 2)) = true ∧
    2 * (171 ^ 2 + 174 ^ 2 + 345 ^ 2) = 6 * (1 + 172 ^ 2 + 173 ^ 2) ∧
    2 * (1547 ^ 2 + 1550 ^ 2 + 3097 ^ 2) = 6 * (1 + 1548 ^ 2 + 1549 ^ 2) := by
  decide

/-- The numerator of `3 b₀` for `n_f` flavours: `3 b₀ = 11 C_A − 4 T_F n_f = 33 − 2 n_f` at `N = 3`. -/
def threeB0 (nf : Nat) : Int := 33 - 2 * nf

/-- 46:C5, 46:P2 — the one-loop rational `b₀ = (11/3) C_A − (4/3) T_F n_f = 11 − 2n_f/3`: `9, 25/3, 23/3, 7` for `n_f = 3, 4, 5, 6`
(`3 b₀ = 27, 25, 23, 21`). -/
theorem b0_values : threeB0 3 = 27 ∧ threeB0 4 = 25 ∧ threeB0 5 = 23 ∧ threeB0 6 = 21 := by
  decide

/-- 46:C5 — `b₀ > 0` for every `n_f ≤ 16` (the sign the chart calls asymptotic freedom, for the matter content `n_f ≤ 16`). -/
theorem b0_pos : ∀ nf, nf < 17 → 0 < threeB0 nf := by
  decide

/-- 46:C5 — the sign flips at `n_f = 17`: `3 b₀ = −1`. -/
theorem b0_seventeen : threeB0 17 = -1 := by
  decide

/-- 46:C5 — `b₀ < 0` for every `n_f` from `17` to `200` (a bounded sweep, kernel-decided). -/
theorem b0_neg : ∀ nf, nf < 201 → 17 ≤ nf → threeB0 nf < 0 := by
  decide +kernel

/-! ## The drive exponent (46:C6) -/

/-- 46:C6 — every registered scale `w ≠ 0` is one power of the drive: `w = gⁿ` for some `n < p − 1` (the discrete logarithm of
26-pnp, `FrameCore.eq_pow_of_ne_zero`). -/
theorem drive_exponent (F : Frame p κ g) {w : Shell p} (hw : w ≠ 0) : ∃ n, n < p - 1 ∧ g ^ n = w :=
  F.eq_pow_of_ne_zero hw

/-- 46:C6 — the exponent is unique below `p − 1` (`FrameCore.pow_inj`). -/
theorem drive_exponent_unique (F : Frame p κ g) {m n : Nat} (hm : m < p - 1) (hn : n < p - 1) (h : g ^ m = g ^ n) :
    m = n :=
  F.pow_inj hm hn h

/-- 46:C6 — the exponent of a product is the sum of the exponents, read modulo `p − 1`. -/
theorem drive_exponent_add (F : Frame p κ g) (m n : Nat) :
    g ^ m * g ^ n = g ^ ((m + n) % (p - 1)) := by
  rw [← pow_add, F.pow_mod]

/-! ## The singlet multiplicities of the triplet, by the Pieri rule

An irreducible representation of `SU(3)` is a pair of Dynkin labels `(a, b)` (the triplet `(1, 0)`, its conjugate `(0, 1)`,
the adjoint `(1, 1)`). Tensoring with the triplet adds one box to the Young diagram: `(a, b) ↦ (a + 1, b)`, `(a − 1, b + 1)`
for `a ≥ 1`, `(a, b − 1)` for `b ≥ 1`. The multiplicity of the trivial representation in `𝟛^{⊗m} ⊗ 𝟛̄^{⊗n}` is
`Σ_λ mult_m(λ) · mult_n(λ)` (the invariants of `V ⊗ W*` are the homomorphisms `W → V`), every number a natural number. The
constant-term computation of the hadrons theme (`moment6`) gives six times the same multiplicities (`mult_moment6`). -/

/-- A weight list: Dynkin labels with multiplicities. -/
abbrev Mult := List ((Nat × Nat) × Nat)

/-- Add `m` copies of the label `k`. -/
def addW (k : Nat × Nat) (m : Nat) : Mult → Mult
  | [] => [(k, m)]
  | (l, n) :: rest => if l == k then (l, n + m) :: rest else (l, n) :: addW k m rest

/-- One tensor factor of the triplet (the Pieri rule). -/
def tensor3 (M : Mult) : Mult :=
  M.foldl (fun acc x =>
    let a := x.1.1; let b := x.1.2; let m := x.2
    let acc := addW (a + 1, b) m acc
    let acc := if 1 ≤ a then addW (a - 1, b + 1) m acc else acc
    if 1 ≤ b then addW (a, b - 1) m acc else acc) []

/-- The decomposition of `𝟛^{⊗m}`. -/
def powers3 : Nat → Mult
  | 0 => [((0, 0), 1)]
  | m + 1 => tensor3 (powers3 m)

/-- The multiplicity of the label `k` in a weight list. -/
def lookup (k : Nat × Nat) : Mult → Nat
  | [] => 0
  | (l, n) :: rest => if l == k then n else lookup k rest

/-- `E[χ^m χ̄^n]`: the number of invariants of `𝟛^{⊗m} ⊗ 𝟛̄^{⊗n}`, `Σ_λ mult_m(λ) mult_n(λ)`. -/
def mult (m n : Nat) : Nat := (powers3 m).foldl (fun s x => s + x.2 * lookup x.1 (powers3 n)) 0

/-- The hadrons theme's constant terms are six times the Pieri multiplicities, in every degree the paper uses through
the adjoint wrap (`m + n ≤ 4`). -/
theorem mult_moment6 :
    ((List.range 5).flatMap fun m => (List.range (5 - m)).map fun n => (m, n)).all
      (fun x => FRC.Hadrons.moment6 x.1 x.2 == 6 * (mult x.1 x.2 : Int)) = true := by
  decide +kernel

/-- The binomial coefficient by Pascal's rule. -/
def choose : Nat → Nat → Nat
  | _, 0 => 1
  | 0, _ + 1 => 0
  | n + 1, k + 1 => choose n k + choose n (k + 1)

/-- `2^k · E[(Re χ)^k] = Σ_j C(k, j) · E[χ^j χ̄^{k−j}]`. -/
def ex (k : Nat) : Nat := (List.range (k + 1)).foldl (fun s j => s + choose k j * mult j (k - j)) 0

/-- `2^k · E[χ (Re χ)^k] = Σ_j C(k, j) · E[χ^{j+1} χ̄^{k−j}]`. -/
def exc (k : Nat) : Nat := (List.range (k + 1)).foldl (fun s j => s + choose k j * mult (j + 1) (k - j)) 0

/-- 46:C7 — the moment lists `(ex k)` and `(exc k)` for `k < 8`, from the Pieri multiplicities. -/
theorem moments :
    (List.range 8).map ex = [1, 0, 2, 2, 12, 30, 130, 462] ∧
    (List.range 8).map exc = [0, 1, 1, 6, 15, 65, 231, 973] := by
  decide +kernel

/-! ## Framed rationals on the shell -/

/-- The residue of an integer on the shell. -/
def ofInt : Int → Shell p
  | .ofNat n => Shell.ofNat n
  | .negSucc n => -(Shell.ofNat (n + 1))

/-- The inverse on the shell by bounded search (`0` for a non-unit), as 13-epi's `FRC.Epi.inv`; a theme imports no paper module. -/
def invSearch (x : Shell p) : Nat → Shell p
  | 0 => 0
  | n + 1 => if x * Shell.ofNat n = 1 then Shell.ofNat n else invSearch x n

def invS (x : Shell p) : Shell p := invSearch x p

/-- The framed rational `a / d` on the shell: the residue `a · d⁻¹`. -/
def fr (a : Int) (d : Shell p) : Shell p := ofInt a * invS d

/-- The residue of `k!` on the shell. -/
def factS : Nat → Shell p
  | 0 => 1
  | k + 1 => factS k * Shell.ofNat (k + 1)

/-! ## Power series over the shell -/

/-- A power series over the shell, as its coefficient list. -/
abbrev SP (p : Nat) := List (Shell p)

def psCoeff (a : SP p) (k : Nat) : Shell p := nth 0 a k

/-- The product to order `n` (`n` coefficients). -/
def psMul (a b : SP p) (n : Nat) : SP p :=
  (List.range n).map fun k => (List.range (k + 1)).foldl (fun s i => s + psCoeff a i * psCoeff b (k - i)) 0

/-- The reciprocal to order `n`, given the inverse `a0inv` of the constant term: `r₀ = a0inv`,
`r_k = −a0inv · Σ_{i=1}^{k} a_i r_{k−i}`. -/
def psInv (a : SP p) (a0inv : Shell p) : Nat → SP p
  | 0 => []
  | n + 1 =>
    let r := psInv a a0inv n
    if n = 0 then [a0inv]
    else r ++ [-(a0inv * (List.range n).foldl (fun s i => s + psCoeff a (i + 1) * psCoeff r (n - 1 - i)) 0)]

/-- The fundamental plaquette coefficient of `SU(3)` in the stiffness `ϑ` of the connection (46:A16) on the shell, from the
moment lists `E = (ex k)` and `EC = (exc k)`: `c₃ = (1/3) Σ_k E[χ X^k] (2ϑ)^k/k! / Σ_k E[X^k] (2ϑ)^k/k!`, `X = Re χ`, with
`E[X^k] = ex k / 2^k` and `E[χ X^k] = exc k / 2^k`, so the denominator series has coefficients `ex k / k!` and the
numerator `exc k / (3 · k!)`; every division is an inverse on the shell. -/
def c3Series (E EC : List Nat) (n : Nat) : SP p :=
  let i3 : Shell p := invS 3
  let den : SP p := (List.range n).map fun k => Shell.ofNat (nth 0 E k) * invS (factS k)
  let num : SP p := (List.range n).map fun k => Shell.ofNat (nth 0 EC k) * i3 * invS (factS k)
  psMul num (psInv den (invS (psCoeff den 0)) n) n

/-- The eight framed rationals `0, 1/3, 1/6, 0, −5/72, −1/24, 7/720, 59/2160` on the shell, the denominators as products
of the small primes. -/
def c3Targets : SP p :=
  [0, fr 1 3, fr 1 (2 * 3), 0, fr (-5) (2 ^ 3 * 3 ^ 2), fr (-1) (2 ^ 3 * 3),
   fr 7 (2 ^ 4 * 3 ^ 2 * 5), fr 59 (2 ^ 4 * 3 ^ 3 * 5)]

/-- The decision on one shell `p = q + 1`. -/
def c3Check : Nat → Bool
  | 0 => false
  | q + 1 => decide (c3Series (p := q + 1) [1, 0, 2, 2, 12, 30, 130, 462] [0, 1, 1, 6, 15, 65, 231, 973] 8 = c3Targets)

theorem c3_lab : c3Check 13 = true ∧ c3Check 173 = true ∧ c3Check 1549 = true := by
  decide +kernel

theorem c3_sweep :
    [13, 17, 29, 37, 41, 53, 61, 73, 89, 97, 101, 109, 113, 137, 149, 157, 173, 181, 193, 197].all c3Check = true := by
  decide +kernel

/-- The five decisions of `series_window` on the shell `13`, as one Boolean (so that the theorem's statement re-elaborates). -/
def windowCheck : Bool :=
  decide ((c3Series (p := 13) [1, 0, 2, 2, 12, 30, 130, 462] [0, 1, 1, 6, 15, 65, 231, 974] 8).take 7
      = (c3Series (p := 13) [1, 0, 2, 2, 12, 30, 130, 462] [0, 1, 1, 6, 15, 65, 231, 973] 8).take 7) &&
  decide (psCoeff (c3Series (p := 13) [1, 0, 2, 2, 12, 30, 130, 462] [0, 1, 1, 6, 15, 65, 231, 974] 8) 7
      ≠ psCoeff (c3Series (p := 13) [1, 0, 2, 2, 12, 30, 130, 462] [0, 1, 1, 6, 15, 65, 231, 973] 8) 7) &&
  decide (psCoeff (c3Series (p := 13) [1, 0, 2, 2, 12] [0, 1, 1, 6, 20] 5) 4 = 0) &&
  decide (psCoeff (c3Series (p := 13) [1, 0, 2, 2, 12] [0, 1, 1, 6, 15] 5) 4 = psCoeff (c3Targets (p := 13)) 4) &&
  decide (psCoeff (c3Targets (p := 13)) 4 ≠ 0)

/-- 46:C14 — the series' window, the corollary of A9 (the push on T06, 9 November 2026). The `ϑ^k` coefficient of `c₃` is built from
the invariant counts of degree `≤ k + 1` (`exc k` has degree `k + 1`, `ex k` degree `k`), so on a Subject `p`, where the frame's counts
equal the compact ones through degree `p − 2` (A9), the frame's series equals the compact one through `ϑ^{p−3}`: `ϑ^{10}` on `13`,
`ϑ^{170}` on `173`, `ϑ^{1546}` on `1549`, all beyond the `ϑ^7` computed. Decided on the shell `13`: raising the degree-`8` count
`exc 7` by one leaves the coefficients of `ϑ^0`…`ϑ^6` unchanged and moves `ϑ^7`; and the instance's departure at degree `5`
(`M(4,1) = M(1,4) = 4` against `3`, so `exc 4 = 20` against `15`) puts the instance's `ϑ^4` coefficient at `0`, where the compact one is
`−5/72` (`c3Targets`), a nonzero residue on the shell; the five decisions are the Boolean `windowCheck`. -/
theorem series_window :
    (13 - 3 = 10 ∧ 7 ≤ 13 - 3 ∧ 7 ≤ 173 - 3 ∧ 7 ≤ 1549 - 3 ∧ 7 ≤ 13 - 4) ∧ windowCheck = true := by
  decide +kernel

/-! ## The instance `2T` against `SU(2)` (46:C7, second clause)

`SU(2)`: an irreducible representation is one Dynkin label `n` (spin `n/2`); tensoring with the doublet sends `n` to `n + 1`
and, for `n ≥ 1`, to `n − 1`, so the singlet multiplicity in `𝟚^{⊗k}` is the Catalan number at even `k` and `0` at odd `k`.
`2T = SU(2, 𝔽₃)` is the group of the `24` Hurwitz units `±1, ±i, ±j, ±k, (±1 ± i ± j ± k)/2`; the trace of a unit
quaternion `a + bi + cj + dk` in the doublet is `2a`, so the traces are `2, −2` once each, `0` six times, `1` and `−1`
eight times each, and the `k`-th moment of the trace is `Σ t^k / 24`. -/

/-- A weight list for `SU(2)`: Dynkin labels with multiplicities. -/
abbrev Mult2 := List (Nat × Nat)

def addW2 (k m : Nat) : Mult2 → Mult2
  | [] => [(k, m)]
  | (l, n) :: rest => if l == k then (l, n + m) :: rest else (l, n) :: addW2 k m rest

/-- One tensor factor of the doublet. -/
def tensor2 (M : Mult2) : Mult2 :=
  M.foldl (fun acc x => let acc := addW2 (x.1 + 1) x.2 acc; if 1 ≤ x.1 then addW2 (x.1 - 1) x.2 acc else acc) []

def powers2 : Nat → Mult2
  | 0 => [(0, 1)]
  | m + 1 => tensor2 (powers2 m)

def lookup2 (k : Nat) : Mult2 → Nat
  | [] => 0
  | (l, n) :: rest => if l == k then n else lookup2 k rest

/-- `E[χ^k]` over `SU(2)`: the singlet multiplicity in `𝟚^{⊗k}`. -/
def mult2 (k : Nat) : Nat := lookup2 0 (powers2 k)

theorem catalan_moments : (List.range 9).map mult2 = [1, 0, 1, 0, 2, 0, 5, 0, 14] := by decide

/-- The doubled coordinates `(2a, 2b, 2c, 2d)` of the `24` Hurwitz units. -/
def hurwitz : List (Int × Int × Int × Int) :=
  [(2, 0, 0, 0), (-2, 0, 0, 0), (0, 2, 0, 0), (0, -2, 0, 0), (0, 0, 2, 0), (0, 0, -2, 0), (0, 0, 0, 2), (0, 0, 0, -2)] ++
  ((([1, -1].flatMap fun a => [1, -1].flatMap fun b => [1, -1].flatMap fun c => [1, -1].map fun d => (a, b, c, d))) :
    List (Int × Int × Int × Int))

/-- `Σ_{q ∈ 2T} (tr q)^k`, the trace of a unit quaternion being its doubled real part. -/
def traceSum2T (k : Nat) : Int := hurwitz.foldl (fun s q => s + q.1 ^ k) 0

/-- The `24` traces: `2` and `−2` once, `0` six times, `1` and `−1` eight times each. -/
theorem traces_2T :
    hurwitz.length = 24 ∧ (hurwitz.filter fun q => q.1 == 2).length = 1 ∧ (hurwitz.filter fun q => q.1 == -2).length = 1 ∧
    (hurwitz.filter fun q => q.1 == 0).length = 6 ∧ (hurwitz.filter fun q => q.1 == 1).length = 8 ∧
    (hurwitz.filter fun q => q.1 == -1).length = 8 ∧
    (List.range 8).map traceSum2T = [24, 0, 24, 0, 48, 0, 144, 0] := by
  decide

/-- The fundamental plaquette coefficient of a group with doublet moments `m_k = M_k / D` (`D = 1` for `SU(2)`'s
multiplicities, `D = 24` for the trace sums of `2T`): `c = (1/2) Σ_k m_{k+1} (2ϑ)^k/k! / Σ_k m_k (2ϑ)^k/k!` in the stiffness, Wilson's coupling being `4ϑ`. -/
def c2Series (M : List Int) (D : Nat) (n : Nat) : SP p :=
  let i2 : Shell p := invS 2
  let iD : Shell p := invS (Shell.ofNat D)
  let den : SP p := (List.range n).map fun k => ofInt (nth 0 M k) * iD * 2 ^ k * invS (factS k)
  let num : SP p := (List.range n).map fun k => ofInt (nth 0 M (k + 1)) * iD * i2 * 2 ^ k * invS (factS k)
  psMul num (psInv den (invS (psCoeff den 0)) n) n

/-- `ϑ − 2ϑ³/3 + 2ϑ⁵/3` on the shell. -/
def c2Targets : SP p := [0, 1, 0, fr (-2) 3, 0, fr 2 3, 0]

/-- `ϑ − 2ϑ³/3 + 4ϑ⁵/5` on the shell. -/
def c2TTargets : SP p := [0, 1, 0, fr (-2) 3, 0, fr 4 5, 0]

/-- The decision on one shell: `SU(2)` from the Catalan multiplicities, `2T` from its trace sums over `24`. -/
def c2Check : Nat → Bool
  | 0 => false
  | q + 1 =>
    decide (c2Series (p := q + 1) [1, 0, 1, 0, 2, 0, 5, 0, 14] 1 7 = c2Targets) &&
    decide (c2Series (p := q + 1) [24, 0, 24, 0, 48, 0, 144, 0, 528] 24 7 = c2TTargets)

/-- 46:C7 — `SU(2)`'s `ϑ − 2ϑ³/3 + 2ϑ⁵/3` against `2T`'s `ϑ − 2ϑ³/3 + 4ϑ⁵/5` on the three laboratory Subjects: the
same coefficients through `ϑ³`, the first difference at `ϑ⁵`. -/
theorem c2_lab : c2Check 13 = true ∧ c2Check 173 = true ∧ c2Check 1549 = true := by decide +kernel

/-! ## The tension's coefficient as window fractions (46:C7) -/

/-- The series `c₃` of `c3Series`, computed in window fractions: the same division with the coefficients
`ex k / k!` and `exc k / (3 · k!)`. -/
def c3WF (E EC : List Nat) (n : Nat) : List WF :=
  let den := (List.range n).map fun k => WF.frac ((nth 0 E k : Nat) : Int) (fact k)
  let num := (List.range n).map fun k => WF.frac ((nth 0 EC k : Nat) : Int) (3 * fact k)
  wsMul num (wsInv den (WF.inv (wsCoeff den 0)) n) n

/-- 46:C7 — the eight fractions of `c₃` modulo `ϑ⁸`, from the multiplicities of `moments`. -/
theorem c3_fractions :
    c3WF [1, 0, 2, 2, 12, 30, 130, 462] [0, 1, 1, 6, 15, 65, 231, 973] 8 =
      [(0, 1), WF.frac 1 3, WF.frac 1 (2 * 3), (0, 1), WF.frac (-5) (2 ^ 3 * 3 ^ 2),
       WF.frac (-1) (2 ^ 3 * 3), WF.frac 7 (2 ^ 4 * 3 ^ 2 * 5), WF.frac 59 (2 ^ 4 * 3 ^ 3 * 5)] := by
  decide +kernel

/-- 46:C7 — the residue of every fraction of `c3_fractions` is the series' coefficient on the shell (`c3Check`): on the three
laboratory Subjects and on the `20` shells `13 ≤ p < 200`; the shell `5` is blind to the coefficients of `ϑ⁶` and `ϑ⁷`,
whose denominators it divides. -/
theorem c3_readback :
    c3Check 13 = true ∧ c3Check 173 = true ∧ c3Check 1549 = true ∧
    [13, 17, 29, 37, 41, 53, 61, 73, 89, 97, 101, 109, 113, 137, 149, 157, 173, 181, 193, 197].all c3Check = true ∧
    (2 ^ 4 * 3 ^ 2 * 5 : Shell 5) = 0 := by
  exact ⟨c3_lab.1, c3_lab.2.1, c3_lab.2.2, c3_sweep, by decide⟩

/-! ## The short-range route: the declared coupling against the Herbst bound (46:C10)

The chart's one-loop coupling at the one scale, `α_s(√σ) = 2π/(b₀ ln(√σ/Λ))` with `b₀ = 9` and `√σ/Λ = 2`, and the
two-adjoint colour factor `C = C_A α_s`. Herbst's criterion for the chart operator `a|p| − C/r`: bounded below iff
`C ≤ 2a/π`, so `2/π` for one body and `4/π` for two. Every quantity is a bracket of window fractions, `π` by the six-place
bracket and `ln 2` by the chain; the comparison `C > 4/π` is `π² > 6 ln 2`, decided on cross-products. -/

/-- `α_s(√σ) = 2π/(9 ln 2)` as a bracket. -/
def alphaDeclared : BR :=
  let l2 := lnBr (WF.ofNat 2) 12
  (WF.div (WF.mul (WF.ofNat 2) piBr.1) (WF.mul (WF.ofNat 9) l2.2),
   WF.div (WF.mul (WF.ofNat 2) piBr.2) (WF.mul (WF.ofNat 9) l2.1))

/-- `C = C_A α_s(√σ)` with `C_A = 3`. -/
def couplingC : BR := BR.smul 3 alphaDeclared

/-- The Herbst values `2/π` (one body) and `4/π` (two bodies) as brackets. -/
def herbstOne : BR := (WF.div (WF.ofNat 2) piBr.2, WF.div (WF.ofNat 2) piBr.1)
def herbstTwo : BR := (WF.div (WF.ofNat 4) piBr.2, WF.div (WF.ofNat 4) piBr.1)

/-- 46:C10 — `α_s(√σ) ∈ (1.0065, 1.0075)`, `C ∈ (3.015, 3.025)`, the Herbst values `2/π ∈ (0.636, 0.637)` and
`4/π ∈ (1.273, 1.274)`; `C` exceeds both, and in the form without division, `π² > 6 ln 2` on the brackets
(`L² > 6 (s + t)`). -/
theorem herbst_comparison :
    BR.within alphaDeclared (WF.frac 10065 10000) (WF.frac 10075 10000) = true ∧
    BR.within couplingC (WF.frac 3015 1000) (WF.frac 3025 1000) = true ∧
    BR.within herbstOne (WF.frac 636 1000) (WF.frac 637 1000) = true ∧
    BR.within herbstTwo (WF.frac 1273 1000) (WF.frac 1274 1000) = true ∧
    WF.lt herbstTwo.2 couplingC.1 = true ∧ WF.lt herbstOne.2 couplingC.1 = true ∧
    WF.lt (WF.mul (WF.ofNat 6) (lnBr (WF.ofNat 2) 12).2) (WF.mul piBr.1 piBr.1) = true := by
  decide +kernel

/-! ## The plaquette channel (46:C11)

The imported series `a m = −4 ln u + Σ_{k=1}^{7} M_k u^k` (A11) and the tension at leading order `a²σ = −ln u` (A7) give
`m/√σ = (4x + P_o(u))/√x` with `x = −ln u` and `P_o` the series to order `o`. With `P_o(u) < 0 < 4x + P_o(u)` the square
`(4x + P)²/x` increases with `x`, so the bracket of `x` (the chain) brackets the ratio; the relative spread of the orders
`3, 5, 7` is `(max P_o − min P_o)/(4x + P₇)`, decreasing in `x`. -/

/-- Münster's coefficients `M₁, …, M₇` of the `0⁺⁺` series (A11). -/
def munster : List WF :=
  [(0, 1), (-3, 1), (9, 1), WF.frac (-27) 2, (-7, 1), WF.frac (-297) 2, WF.frac 858827 10240, WF.frac 47641149 71680]

/-- `P_o(u) = Σ_{k=1}^{o} M_k u^k`. -/
def polyP (o : Nat) (u : WF) : WF :=
  (List.range o).foldl (fun s k => WF.add s (WF.mul (nth (0, 1) munster (k + 1)) (WF.pow u (k + 1)))) (0, 1)

/-- The bracket of `x = −ln u = ln(1/u)` by the chain at stage `n`. -/
def xBr (u : WF) (n : Nat) : BR := lnBr (WF.inv u) n

/-- `(4x + P)² / x`, the square of the ratio `m/√σ`. -/
def ratioSq (P x : WF) : WF :=
  let s := WF.add (WF.mul (WF.ofNat 4) x) P
  WF.div (WF.mul s s) x

/-- The ratio at order `o` lies in `(lo, hi)`, with the chain at stage `n`: `4 x_lo + P > 0`, `lo² < (4x_lo + P)²/x_lo` and
`(4x_hi + P)²/x_hi < hi²`. -/
def ratioWithin (n o : Nat) (u lo hi : WF) : Bool :=
  let P := polyP o u; let x := xBr u n
  WF.lt (0, 1) (WF.add (WF.mul (WF.ofNat 4) x.1) P) &&
  WF.lt (WF.mul lo lo) (ratioSq P x.1) && WF.lt (ratioSq P x.2) (WF.mul hi hi)

/-- An upper bound of the relative spread of the orders `3, 5, 7`, `(max P − min P)/(4 x_lo + P₇)`. -/
def spreadHi (n : Nat) (u : WF) : WF :=
  let a := polyP 3 u; let b := polyP 5 u; let c := polyP 7 u
  WF.div (WF.sub (WF.max a (WF.max b c)) (WF.min a (WF.min b c))) (WF.add (WF.mul (WF.ofNat 4) (xBr u n).1) c)

/-- A lower bound of the same spread, with `x_hi`. -/
def spreadLo (n : Nat) (u : WF) : WF :=
  let a := polyP 3 u; let b := polyP 5 u; let c := polyP 7 u
  WF.div (WF.sub (WF.max a (WF.max b c)) (WF.min a (WF.min b c))) (WF.add (WF.mul (WF.ofNat 4) (xBr u n).2) c)

/-- The sum of the computed terms of `c₃` through `ϑ⁷` at the stiffness `ϑ`: the fractions of `c3_fractions` against the
powers of `ϑ`. -/
def uAt (th : WF) : WF :=
  let c := c3WF [1, 0, 2, 2, 12, 30, 130, 462] [0, 1, 1, 6, 15, 65, 231, 973] 8
  (List.range 8).foldl (fun s k => WF.add s (WF.mul (wsCoeff c k) (WF.pow th k))) (0, 1)

/-- 46:C7 — the computed terms of `c₃` through `ϑ⁷` sum to `23/54` at the stiffness `ϑ = 1`. -/
theorem c3_sum_at_one : uAt (WF.ofNat 1) = WF.frac 23 54 := by
  decide +kernel

/-- 46:C11 — the plaquette channel at channel unity (46:B6), where the stiffness is `ϑ = 1/24` (46:A16). The computed terms of
`c₃` through `ϑ⁷` sum there to `u = 140458562483/9906778275840`, between `0.0141` and `0.0142`. At the abscissa `0.0142`, the
row's `u`, with the chain of the logarithm at stage `2`, the orders `3, 5, 7` of `m/√σ` lie in `(8.2, 8.3)`, above the lattice
bracket `(3.4, 3.7)`, and their relative spread is below `10⁻⁶`. The stage `2` keeps every integer that the comparisons form
below `10¹⁰⁷`. The ratio at the exact `u` over the reals, in `(8.23, 8.24)`, is a theorem on Mathlib
(`FRC.YangMillsML.plaquette_cells_values`) and the chart check of the ledger file. -/
theorem plaquette_cells :
    uAt (WF.frac 1 24) = WF.frac 140458562483 9906778275840 ∧
    (WF.lt (WF.frac 141 10000) (uAt (WF.frac 1 24)) && WF.lt (uAt (WF.frac 1 24)) (WF.frac 142 10000)) = true ∧
    ([3, 5, 7].all fun o => ratioWithin 2 o (WF.frac 142 10000) (WF.frac 82 10) (WF.frac 83 10)) = true ∧
    WF.lt (spreadHi 2 (WF.frac 142 10000)) (WF.frac 1 1000000) = true := by
  decide +kernel

/-! ## The family of the minimal wrap against the lattice (46:C12)

`E₀(a, ϰ) = √(aϰ) E₀(1, 1)` by the dilation `r ↦ r/μ`, `p ↦ μp` of the chart operator, and the chart's `E₀(1, 1) = 2.232`
(35-hadrons C17). In thousandths, `(2000 E₀)² = a · (4ϰ) · 2232²` with `4ϰ ∈ {4, 8, 9}`; the determinations (A1) are
`3700(60)`, `3630(100)`, `3405(21)`. -/

/-- `(2000 E₀)²` for the member `(a, 4ϰ)`. -/
def famSq (a k4 : Nat) : Nat := a * k4 * 2232 ^ 2

/-- The six members `(a, 4ϰ)`. -/
def family : List (Nat × Nat) := [(1, 4), (1, 8), (1, 9), (2, 4), (2, 8), (2, 9)]

/-- The three determinations `(value, error)` in thousandths. -/
def determinations : List (Nat × Nat) := [(3700, 60), (3630, 100), (3405, 21)]

/-- 46:C12 — the six values read `2.232, 3.157, 3.348, 3.157, 4.464, 4.735` (each within half a unit of its decimal);
none lies inside any determination's error; every member is at least `0.057` from every central value, the distance of
`(a, ϰ) = (1, 9/4)` from the direct value, which it falls below by `1.7 %` (`57/3405 ∈ (0.0165, 0.0175)`). -/
theorem wrap_family :
    (List.zip family [2232, 3157, 3348, 3157, 4464, 4735]).all
      (fun x => decide ((2 * x.2 - 1) ^ 2 < famSq x.1.1 x.1.2 ∧ famSq x.1.1 x.1.2 < (2 * x.2 + 1) ^ 2)) = true ∧
    family.all (fun m => determinations.all fun d =>
      decide (famSq m.1 m.2 < 4 * (d.1 - d.2) ^ 2 ∨ 4 * (d.1 + d.2) ^ 2 < famSq m.1 m.2)) = true ∧
    family.all (fun m => determinations.all fun d =>
      decide (famSq m.1 m.2 ≤ 4 * (d.1 - 57) ^ 2 ∨ 4 * (d.1 + 57) ^ 2 ≤ famSq m.1 m.2)) = true ∧
    famSq 1 9 = (2 * 3348) ^ 2 ∧ 3348 + 57 = 3405 ∧ 165 * 3405 < 57 * 10000 ∧ 57 * 10000 < 175 * 3405 := by
  decide

/-! ## The colour factors against LEP (46:P1, X4) -/

/-- 46:P1, 46:X4 — `C_A = 3 ∈ 2.89 ± 0.21`, `C_F = 4/3 ∈ 1.30 ± 0.09`, `C_A/C_F = 9/4 ∈ 2.22 ± 0.11`, each within one
standard deviation (in hundredths, the fractions cleared); the abelian alternative `C_A = 0`, `C_F = 1` lies outside
both brackets. -/
theorem colour_factors_within :
    268 ≤ 300 ∧ 300 ≤ 310 ∧ 3 * 121 ≤ 400 ∧ 400 ≤ 3 * 139 ∧ 4 * 211 ≤ 900 ∧ 900 ≤ 4 * 233 ∧
    0 < 268 ∧ 100 < 121 := by
  decide

/-! ## The one-loop run between the laboratory scales (46:P2)

`1/α_s(μ)` is linear in `ln μ` with slope `b₀/2π` between thresholds (the window rational `b₀ = 23/3` for five flavours,
`25/3` for four, C5): `1/α(m_τ) = 1/α(M_Z) − (23/3) ln(M_Z/m_b)/(2π) − (25/3) ln(m_b/m_τ)/(2π)` with `α(M_Z) = 0.1180`,
`M_Z = 91.1876`, `m_b = 4.18`, `m_τ = 1.77686` (A3). The logarithms are chains at stage `3`, which keeps every integer of the
comparisons below `10⁸⁰`; `π` is the six-place bracket. -/

/-- The subtracted term `T = ((23/3) ℓ₁ + (25/3) ℓ₂)/(2π)` as a bracket, `ℓ₁ = ln(M_Z/m_b)`, `ℓ₂ = ln(m_b/m_τ)`. -/
def runTerm : BR :=
  let l1 := lnBr (WF.frac 911876 41800) 3
  let l2 := lnBr (WF.frac 418000 177686) 3
  let s : BR := BR.add (BR.smul 23 l1) (BR.smul 25 l2)
  (WF.div s.1 (WF.mul (WF.ofNat 6) piBr.2), WF.div s.2 (WF.mul (WF.ofNat 6) piBr.1))

/-- `α_s(m_τ)` at one loop as a bracket: `1/(500/59 − T)`. -/
def alphaTau : BR :=
  (WF.inv (WF.sub (WF.frac 500 59) runTerm.1), WF.inv (WF.sub (WF.frac 500 59) runTerm.2))

/-- 46:P2 — the one-loop run gives `α_s(m_τ) ∈ (0.2785, 0.2795)`, against `0.312(15)`: the deficit `0.312 − α` is between
`2.15` and `2.25` standard deviations of `0.015`; the slopes are the window rationals of C5 (`3 b₀ = 23, 25`). -/
theorem running_one_loop :
    BR.within alphaTau (WF.frac 2785 10000) (WF.frac 2795 10000) = true ∧
    WF.lt (WF.frac 215 100) (WF.div (WF.sub (WF.frac 312 1000) alphaTau.2) (WF.frac 15 1000)) = true ∧
    WF.lt (WF.div (WF.sub (WF.frac 312 1000) alphaTau.1) (WF.frac 15 1000)) (WF.frac 225 100) = true ∧
    threeB0 5 = 23 ∧ threeB0 4 = 25 := by
  decide +kernel

/-! ## The explanations (46:X1, X2) and the states of residue 0 (46:P4) -/

/-- 46:X1 — the adjoint has no invariant: `𝟛 ⊗ 𝟛̄` has one singlet (the trace) and the adjoint `𝟠` is its complement,
`E[χχ̄] − 1 = 0`; with `no_shell_eigenvalue` (the torus fixes no line) no registration singles a gluon out. -/
theorem adjoint_no_invariant : mult 1 1 = 1 ∧ mult 1 1 - 1 = 0 ∧ lookup (1, 1) (powers3 2) = 0 ∧
    lookup (1, 1) (tensor3 [((0, 1), 1)]) = 1 := by
  decide

/-- 46:X2 — one invariant line each: baryon `E[χ³] = 1`, meson `E[χχ̄] = 1`, glueball `E[(χχ̄ − 1)²] = 2 − 2 + 1 = 1`, by
the Pieri multiplicities. -/
theorem residue_series_pieri : mult 3 0 = 1 ∧ mult 1 1 = 1 ∧ mult 2 2 - 2 * mult 1 1 + 1 = 1 := by
  decide

/-- 46:P4 — a quark and a gluon are states of residue `0`: the triplet and its dual have no singlet, `mult 1 0 = mult 0 1 = 0`,
and the adjoint has none, `mult 1 1 - 1 = 0`, by the Pieri multiplicities. -/
theorem residue_zero_states : mult 1 0 = 0 ∧ mult 0 1 = 0 ∧ mult 1 1 - 1 = 0 := by
  decide


/-! ## The two rationals of the one-loop coefficient (46:C13)

Hughes and Nielsen write the one-loop coefficient as a sum over the field species of a paramagnetic spin term and a
diamagnetic charge term, `b₀ = Σ (−1)^{2s} [(2s)² − 1/3] T(R)` (46:A12, imported). Both rationals are the frame's. The spin
term is `(2s)² = −2 Tr_V(J₁₂²)`, `J₁₂` the generator of the rotation of the `(1, 2)`-plane on the field's module: on the
vector `J₁₂ = e₁₂ − e₂₁`, on the Weyl spinor `(i/2) σ₃` with `i² = −1`, which the shell has (`p ≡ 1 (mod 4)`); the traces
are decided on the laboratory Subjects with the doubled spinor generator `i σ₃`. The charge term is the leading Faulhaber
coefficient of the scalar loop's midpoint sum, `3 Σ_{k<N} (N − 2k − 1)² = N (N² − 1)`: the chart's `∫₀¹ (1 − 2x)² dx = 1/3`
is the leading coefficient, `−1/(3N²)` the finite-size term the chart discards, and the complete cycle `N = p` vanishes on
the shell. With `C_A = 3`, `2 T_F = 1` the species sum gives `3 b₀ = 3(3·4 − 1) − n_f (3·1 − 1) = 33 − 2 n_f`, the window
rational of 46:C5. -/

/-- Square matrices over the shell as row lists. -/
abbrev Mat (p : Nat) := List (List (Shell p))

def mmul (A B : Mat p) : Mat p :=
  A.map fun row => (List.range B.length).map fun j =>
    (List.range row.length).foldl (fun s k => s + nth 0 row k * nth 0 (nth [] B k) j) 0

def tr (A : Mat p) : Shell p := (List.range A.length).foldl (fun s k => s + nth 0 (nth [] A k) k) 0

/-- The rotation generator of the `(1, 2)`-plane on the vector, `e₁₂ − e₂₁`. -/
def jVec : Mat p := [[0, 1, 0, 0], [-1, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0]]

/-- Twice the generator on the Weyl spinor, `i σ₃`. -/
def jWeyl (i : Shell p) : Mat p := [[i, 0], [0, -i]]

/-- 46:C13 — the spin term `(2s)² = −2 Tr(J₁₂²)`: `4` on the vector, `1` on the Weyl spinor (`−Tr((iσ₃)²) = 2`, the generator
doubled), `0` on the scalar, with `i = 5, 80, 88` the square roots of `−1` on `13`, `173`, `1549`. -/
theorem spin_traces :
    (-(2 * tr (mmul jVec jVec)) = (4 : Shell 13) ∧ (5 : Shell 13) * 5 = -1 ∧ -(tr (mmul (jWeyl 5) (jWeyl 5))) = (2 : Shell 13)) ∧
    (-(2 * tr (mmul jVec jVec)) = (4 : Shell 173) ∧ (80 : Shell 173) * 80 = -1 ∧ -(tr (mmul (jWeyl 80) (jWeyl 80))) = (2 : Shell 173)) ∧
    (-(2 * tr (mmul jVec jVec)) = (4 : Shell 1549) ∧ (88 : Shell 1549) * 88 = -1 ∧ -(tr (mmul (jWeyl 88) (jWeyl 88))) = (2 : Shell 1549)) ∧
    tr (mmul ([[0]] : Mat 13) [[0]]) = 0 := by
  decide +kernel

/-- `Σ_{k<N} (N − 2k − 1)²` in the integers. -/
def sq (N : Nat) : Int := (List.range N).foldl (fun (s : Int) (k : Nat) => s + ((N : Int) - 2 * (k : Int) - 1) ^ 2) (0 : Int)

/-- The same sum on the shell. -/
def sqS (N : Nat) : Shell p :=
  (List.range N).foldl (fun (s : Shell p) (k : Nat) => s + (Shell.ofNat N + -((2 : Shell p) * Shell.ofNat k) + -(1 : Shell p)) ^ 2) 0

/-- 46:C13 — the Faulhaber identity `3 Σ_{k<N} (N − 2k − 1)² = N (N² − 1)` for every `N < 400` in the integers: the leading
coefficient `1/3` is the chart's `∫₀¹ (1 − 2x)² dx`, the lower term `−1/(3N²)` is what the chart discards. -/
theorem faulhaber_third : ∀ N, N < 400 → 3 * sq N = (N : Int) * ((N : Int) ^ 2 - 1) := by
  decide +kernel

/-- 46:C13 — on the shell `173` the identity holds as residues for every `N < p`, `Σ = N(N² − 1) · 3⁻¹`. -/
theorem faulhaber_residues : ∀ N, N < 173 → sqS (p := 173) N = Shell.ofNat N * (Shell.ofNat N ^ 2 + -1) * invS 3 := by
  decide +kernel

/-- 46:C13 — the complete cycle `N = p` vanishes on `13`, `173`, `1549` (the power sums over the shell vanish), while `N = 10`
on `173` reads `330 = 10 · 99 / 3`: the third is never a complete residue sum, only the leading coefficient read in the
window. -/
theorem complete_cycle_vanishes :
    sqS (p := 13) 13 = 0 ∧ sqS (p := 173) 173 = 0 ∧ sqS (p := 1549) 1549 = 0 ∧ sqS (p := 173) 10 = 330 := by
  decide +kernel

/-- 46:C13 — the species sum with the denominators cleared: `3 b₀ = C_A (3·(2s_V)² − 1) − n_f · 2T_F · (3·(2s_W)² − 1)` with
`(2s_V)² = 4`, `(2s_W)² = 1`, `C_A = 3`, `2 T_F = 1` is `33 − 2 n_f`, the window rational `threeB0` of 46:C5, for every
`n_f ≤ 200`. -/
theorem hughes_nielsen_sum : ∀ nf, nf < 201 → threeB0 nf = 3 * (3 * 4 - 1) - (nf : Int) * 1 * (3 * 1 - 1) := by
  decide +kernel

/-! ## The radial ratio of the operator form (46:P3)

The ratios of the eigenvalues of the chart operator `a|p| + ϰr` are free of `a` and `ϰ` (the dilation symmetry). The chart's
first radial ratio `E₁/E₀ = 1.4915` (the Lanczos computation of the chart file) is compared in thousandths with the lattice
determinations `0⁺⁺*/0⁺⁺ = 1.544 ± 0.112` (1999) and `5.855(41)/3.405(21) = 1.720 ± 0.016` (2020, A1; the error takes the two
masses as uncorrelated, and the largest error any correlation allows, the two terms added, is `0.0227`), with the nonrelativistic
ladder's Airy ratio `a₂/a₁ ∈ (1.74, 1.76)` from the brackets `2.33 < a₁ < 2.34`, `4.08 < a₂ < 4.09` (the hadrons theme's
`airy_sturm`; the chart's quotient `1.748`), and with the nucleon's `1440/939`. -/

/-- 46:P3 — against the determination of 1999, `1491 ∈ [1432, 1656]`, less than half the error from the centre (`2·53 < 112`),
and the Airy ratio in `(1.74, 1.76)` above the bracket's upper end; against the continuum determination of 2020,
`1720 ± 16`, the ratio `1491` lies more than fourteen errors below (`229 > 14·16`), and more than ten of the largest error any
correlation of the two masses allows (`0.0227`, in ten-thousandths `227`: `10·227 < 17195 − 14915`), while the Airy ratio `1748`
(the chart's quotient of the zeros) lies within two of the quoted error (`28 < 32`); `1440/939` lies within `3 %` of `1.491`. -/
theorem radial_ratio :
    1432 ≤ 1491 ∧ 1491 ≤ 1656 ∧ 2 * (1544 - 1491) < 112 ∧
    174 * 234 < 408 * 100 ∧ 409 * 100 < 176 * 233 ∧ 1656 < 1740 ∧
    14 * 16 < 1720 - 1491 ∧ 10 * 227 < 17195 - 14915 ∧ 1748 - 1720 < 2 * 16 ∧
    1491 * 939 < 1440 * 1000 ∧ 1440 * 1000 * 100 < 1491 * 939 * 103 := by
  decide

/-- 46:C28 — the ground value of the wrap of two windings between the rational bounds `3.1415 < π < 3.1416` [chart]: for
`a = ϰ = 2` the square is `4π`, and `3.544² < 4 · 3.1415`, `4 · 3.1416 < 3.546²`; for `a = 2`, `ϰ = 9/4` it is `9π/2`, and
`3.759² < (9/2) · 3.1415`, `(9/2) · 3.1416 < 3.761²`. The two values, `3.545` and `3.760`, bracket `3.63` and `3.70`, and
`3.405` lies below `3.544`. In integers, over the common denominators. -/
theorem two_windings_ground :
    3544 * 3544 * 10000 < 4 * 31415 * 1000000 ∧ 4 * 31416 * 1000000 < 3546 * 3546 * 10000 ∧
    2 * (3759 * 3759) * 10000 < 9 * 31415 * 1000000 ∧ 9 * 31416 * 1000000 < 2 * (3761 * 3761) * 10000 ∧
    3546 < 3630 ∧ 3700 < 3759 ∧ 3405 < 3544 := by
  decide

/-- 46:P5 — the radial ratio of the wrap of two windings [chart]: the squares of the ratios are `(2 + 4k)/2`, that is `3` and
`5`; `√3` lies in the interval of the 2020 determination `1.720(16)`, as `1704² < 3 · 1000² < 1736²`; and `7/3`, the square
for three windings, lies below it, as `7 · 1000² < 3 · 1704²`. -/
theorem two_windings_radial :
    2 + 4 * 1 = 3 * (2 + 4 * 0) ∧ 2 + 4 * 2 = 5 * (2 + 4 * 0) ∧
    1704 * 1704 < 3 * (1000 * 1000) ∧ 3 * (1000 * 1000) < 1736 * 1736 ∧ 7 * (1000 * 1000) < 3 * (1704 * 1704) := by
  decide

end FRC.YangMills
