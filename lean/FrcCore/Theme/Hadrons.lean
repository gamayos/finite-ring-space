import FrcCore.Theme.Fields
import FrcCore.Ring

/-!
# FrcCore.Theme.Hadrons — the hadrons theme (35-hadrons, 19 October 2026)

The exact content of *Ground-State Light Hadron Spectroscopy over Finite Substrate* (tree `35-hadrons-20260629`) above the
interactions theme's colour sector over `𝔽₄` (`Theme/Fields.lean`), as `frc/hadrons.py` and `frc/ledgers/p35_hadrons.py`
compute it: the colour group `SU(3, 2)` built by orthonormal frames and its centre (`colour_group`, 35:C1), the colourless
content `(1, 0, 0, 1)` of the exterior algebra `Λ•(𝟛)` (`colourless_content`, 35:C15), the meson contraction
(`meson_invariant`, 35:C18), the Weyl constant terms of `SU(3)` — the representation content behind the character sums
(`adjoint_channel`, 35:C14) and the flavour cube `𝟛⊗𝟛⊗𝟛 = 𝟙𝟘 ⊕ 𝟠 ⊕ 𝟠 ⊕ 𝟙` (`flavour_cube`, 35:P5) — the Casimir, spin
and charge arithmetic with cleared denominators (`colour_factor`, `spin_pattern`, `sigma_lambda`, `charge_structure`,
35:C4, C5, C9, C13), the flavour and isospin relations as ring identities on the shell (`gmo`, `spacing`,
`third_difference`, `hyperfine_links`, `coleman_glashow`, `vector_spacing`, `lambda_n_gap`, `spin_split`), the admissible
shells (`admissible_shells`, 35:C20) and Sturm's count of the finite confinement operator (`airy_sturm`, 35:C16).
Kernel-decided throughout (`decide +kernel`); no axioms (`check_core_axioms.py`).
-/

namespace FRC.Hadrons

open FRC.Shell FRC.Shell.Frame FRC.Interactions FRC.Interactions.F4

/-! ## The colour group `SU(3, 2)` over `𝔽₄` by frames (35:C1, X2) -/

/-- The four elements of `𝔽₄`. -/
def f4 : List F4 := [z, o, w, w2]

/-- The `64` vectors of `𝔽₄³`, as lists of three entries. -/
def vecs : List (List F4) := f4.flatMap fun a => f4.flatMap fun b => f4.map fun c => [a, b, c]

/-- The Hermitian form `u†v = Σ ū_i v_i`. -/
def hv (u v : List F4) : F4 :=
  conj (fget u 0) * fget v 0 + conj (fget u 1) * fget v 1 + conj (fget u 2) * fget v 2

/-- The unit vectors `v†v = 1`: `q²(q³ + 1) = 36` of them at `q = 2`. -/
def unitv : List (List F4) := vecs.filter (fun v => hv v v == o)

/-- The matrix with the given columns. -/
def cols (c₁ c₂ c₃ : List F4) : M :=
  [fget c₁ 0, fget c₂ 0, fget c₃ 0, fget c₁ 1, fget c₂ 1, fget c₃ 1, fget c₁ 2, fget c₂ 2, fget c₃ 2]

/-- `U(3, 2)`: the orthonormal frames, column by column. -/
def u3 : List M := unitv.flatMap fun c₁ =>
  (unitv.filter (fun v => hv c₁ v == z)).flatMap fun c₂ =>
    (unitv.filter (fun v => hv c₁ v == z && hv c₂ v == z)).map fun c₃ => cols c₁ c₂ c₃

/-- `SU(3, 2)`: the frames of determinant one. -/
def su3 : List M := u3.filter (fun g => det g == o)

/-- The action on a vector. -/
def mv (A : M) (v : List F4) : List F4 :=
  [at' A 0 0 * fget v 0 + at' A 0 1 * fget v 1 + at' A 0 2 * fget v 2,
   at' A 1 0 * fget v 0 + at' A 1 1 * fget v 1 + at' A 1 2 * fget v 2,
   at' A 2 0 * fget v 0 + at' A 2 1 * fget v 1 + at' A 2 2 * fget v 2]

/-- The entrywise conjugate: the action on `Λ²(𝟛) ≅ 𝟛̄` (for `g†g = I`, `Λ²g = (g⁻¹)ᵀ det g = ḡ`). -/
def conjm (A : M) : M := A.map conj

def zero3 : List F4 := [z, z, z]

/-- The diagonal drive `diag(1, w, w²)` and the permutation `U1` of `Theme/Fields.lean`. -/
def D1 : M := [o, z, z, z, w, z, z, z, w2]
def U1 : M := [z, z, o, z, o, z, o, z, z]

/-- 35:C1, 35:X2 — the colour group built exactly: `36` unit vectors, `648` orthonormal frames (`U(3, 2)`), `216` of
determinant one (`SU(3, 2)`), every element unitary (`g†g = I`) with `det g = 1`; the triality centre: the elements
commuting with `D1` and `U1` are exactly the three scalars `I, wI, w²I`, and each scalar commutes with the whole group.
`su3_centre` of the interactions theme shows the scalars central; here the centre is no larger. -/
theorem colour_group :
    unitv.length = 36 ∧ u3.length = 648 ∧ su3.length = 216 ∧
    (su3.all (fun g => mm (dg g) g == one && det g == o)) = true ∧
    (su3.filter (fun g => mm g D1 == mm D1 g && mm g U1 == mm U1 g)).length = 3 ∧
    ((su3.filter (fun g => mm g D1 == mm D1 g && mm g U1 == mm U1 g)).all
      (fun g => g == one || g == scal w || g == scal w2)) = true ∧
    ([o, w, w2].all (fun x => su3.all (fun g => mm (scal x) g == mm g (scal x)))) = true := by
  decide +kernel

/-- The nonzero vectors fixed by every element, on `𝟛` and on `Λ²(𝟛) ≅ 𝟛̄`. -/
def fixed1 : List (List F4) := vecs.filter (fun v => !(v == zero3) && su3.all (fun g => mv g v == v))
def fixed2 : List (List F4) := vecs.filter (fun v => !(v == zero3) && su3.all (fun g => mv (conjm g) v == v))

/-- 35:C15, 35:X1, 35:X3, 35:X7, 35:P4 — the colourless content of `Λ•(𝟛)` is `(1, 0, 0, 1)`: the vacuum; no nonzero vector of `𝟛`
fixed by the group (a single quark has residue `0`); none of `Λ²(𝟛) ≅ 𝟛̄` (the diquark); `Λ³(𝟛) = det`, fixed by every
element (`det g = 1`), the one-dimensional invariant — the baryon at `k = N = 3`, residue `1`. The dimensions
`1, 3, 3, 1` sum to `8 = 2³`. -/
theorem colourless_content :
    fixed1.length = 0 ∧ fixed2.length = 0 ∧ (su3.all (fun g => det g == o)) = true ∧
    [1, fixed1.length, fixed2.length, 1] = [1, 0, 0, 1] ∧ 1 + 3 + 3 + 1 = 2 ^ 3 := by
  decide +kernel

/-- 35:C18, 35:X12 — the meson contraction: `g†g = I` for every element is the invariance of the Hermitian form on the basis pairs,
`⟨g e_i, g e_j⟩ = (g†g)_{ij} = δ_{ij}`, so the `q q̄` contraction `v^a w̄_a` is the one-dimensional invariant of
`𝟛 ⊗ 𝟛̄`; the triality of `q q̄` is `1 + 2 ≡ 0`, of `qqq` is `3 ≡ 0` (mod 3). -/
theorem meson_invariant :
    (su3.all (fun g => mm (dg g) g == one && det g == o)) = true ∧ (1 + 2) % 3 = 0 ∧ 3 % 3 = 0 ∧ 1 % 3 = 1 ∧ 2 % 3 = 2 :=
  ⟨colour_group.2.2.2.1, by decide⟩

/-! ## The Weyl constant terms of `SU(3)`: the representation content (35:C14, P5) -/

/-- Laurent polynomials in the torus variables `z1, z2` (with `z3 = 1/(z1z2)`): terms `(e₁, e₂, coefficient)`. -/
abbrev LP := List (Int × Int × Int)

def lpAdd1 (t : Int × Int × Int) : LP → LP
  | [] => if t.2.2 == 0 then [] else [t]
  | u :: l => if u.1 == t.1 && u.2.1 == t.2.1 then
      (if u.2.2 + t.2.2 == 0 then l else (u.1, u.2.1, u.2.2 + t.2.2) :: l) else u :: lpAdd1 t l

def lpAdd (p q : LP) : LP := q.foldl (fun acc t => lpAdd1 t acc) p
def lpMul (p q : LP) : LP :=
  p.foldl (fun acc t => q.foldl (fun acc₂ u => lpAdd1 (t.1 + u.1, t.2.1 + u.2.1, t.2.2 * u.2.2) acc₂) acc) []
def lpNeg (p : LP) : LP := p.map (fun t => (t.1, t.2.1, -t.2.2))
def lpPow (p : LP) : Nat → LP
  | 0 => [(0, 0, 1)]
  | n + 1 => lpMul (lpPow p n) p

/-- The constant term. -/
def ct (p : LP) : Int := (p.filter (fun t => t.1 == 0 && t.2.1 == 0)).foldl (fun s t => s + t.2.2) 0

def z1 : LP := [(1, 0, 1)]
def z2 : LP := [(0, 1, 1)]
def z3 : LP := [(-1, -1, 1)]
/-- The fundamental character `χ = z1 + z2 + z3` and its conjugate. -/
def chi : LP := lpAdd (lpAdd z1 z2) z3
def chib : LP := lpAdd (lpAdd [(-1, 0, 1)] [(0, -1, 1)]) [(1, 1, 1)]
/-- The Weyl denominator `|Δ|² = Π_{i<j} (z_i − z_j)(z̄_i − z̄_j)`. -/
def weyl : LP :=
  let d := lpMul (lpMul (lpAdd z1 (lpNeg z2)) (lpAdd z1 (lpNeg z3))) (lpAdd z2 (lpNeg z3))
  let db := lpMul (lpMul (lpAdd [(-1, 0, 1)] (lpNeg [(0, -1, 1)])) (lpAdd [(-1, 0, 1)] (lpNeg [(1, 1, 1)])))
    (lpAdd [(0, -1, 1)] (lpNeg [(1, 1, 1)]))
  lpMul d db

/-- `6 E[χ^a χ̄^b]`: the constant term of `|Δ|² χ^a χ̄^b` (the Weyl integration formula; the Haar moment is one sixth). -/
def moment6 (a b : Nat) : Int := ct (lpMul (lpMul weyl (lpPow chi a)) (lpPow chib b))

/-- 35:C14, 35:C6, 35:C23 — the representation content behind the character sums, as Haar moments by the Weyl constant term:
`E[χχ̄] = 1` (`𝟛 ⊗ 𝟛̄` has one singlet), `E[χ²] = 0` (`𝟛 ⊗ 𝟛` has none), `E[χ²χ̄²] − E[χχ̄] = 1` (the adjoint `𝟠 = χχ̄ − 1`
sits in `𝟛 ⊗ 𝟛̄` once), `E[χ³χ̄] − E[χ²] = 0` (`𝟠` is absent from `𝟛 ⊗ 𝟛`). The single-plaquette coefficients
`c₁ = β/(2N²) = β/18` and `c_adj = β²/(2N)² = β²/36` at `N = 3`. -/
theorem adjoint_channel :
    moment6 1 1 = 6 * 1 ∧ moment6 2 0 = 0 ∧ moment6 2 2 - moment6 1 1 = 6 * 1 ∧ moment6 3 1 - moment6 2 0 = 0 ∧
    2 * 3 ^ 2 = 18 ∧ (2 * 3) ^ 2 = 36 := by
  decide +kernel

/-- 35:P5 — the flavour cube `𝟛 ⊗ 𝟛 ⊗ 𝟛 = 𝟙𝟘 ⊕ 𝟠 ⊕ 𝟠 ⊕ 𝟙`: one singlet (`E[χ³] = 1`), the adjoint twice
(`E[χ⁴χ̄] − E[χ³] = 2`), the squared multiplicities summing to `E[χ³χ̄³] = 6 = 1 + 2² + 1`, the dimensions
`27 = 10 + 8 + 8 + 1`; the symmetric spin–flavour cube `Sym³(𝟞)` has `8·7·6/3! = 56 = 10 · 4 + 8 · 2` states:
no multiplet beyond the `𝟠` and the `𝟙𝟘` at leading order. -/
theorem flavour_cube :
    moment6 3 0 = 6 * 1 ∧ moment6 4 1 - moment6 3 0 = 6 * 2 ∧ moment6 3 3 = 6 * (1 + 2 ^ 2 + 1) ∧
    3 ^ 3 = 10 + 8 + 8 + 1 ∧ 8 * 7 * 6 / (3 * 2 * 1) = 56 ∧ 10 * 4 + 8 * 2 = 56 := by
  decide +kernel

/-! ## The Casimir, spin and charge arithmetic (35:C4, C5, C8, C9, C13, X6, X8, X9) -/

/-- 35:C4, 35:X6 — the colour factor of the singlet with denominators cleared: `2N C₂(𝟛) = N² − 1` gives `6 C₂ = 8`
(`C₂ = 4/3`); `2 Σ_{i<j} T_i·T_j = C₂(𝟙) − 3 C₂(𝟛)` gives `12 Σ T·T = −24` (`−2`); `λ = 2T` gives `Σ λ·λ = −8`,
`−8/3` per pair. -/
theorem colour_factor :
    (3 * 3 - 1 : Int) = 8 ∧ 2 * 3 * 4 = 3 * 8 ∧ (0 - 3 * 8 : Int) = -24 ∧ (-24 : Int) / 12 = -2 ∧ 4 * (-2 : Int) = -8 := by
  decide

/-- 35:C5, 35:X6, 35:P3 — the spin pattern with denominators cleared: for `S = n/2`, `8 g_spin = 8[½S(S+1) − 9/8] = n(n+2) − 9`:
the octet (`n = 1`) `−6/8 = −3/4`, the decuplet (`n = 3`) `6/8 = 3/4`, the separation `12/8 = 3/2`; the eigenvalues of
`Σ(λ·λ)(S·S)` on the singlet, `(−8/3) g`: `(−8)(−6) = 48 = 2 · 24` (`+2`) and `(−8)(6) = −48` (`−2`). -/
theorem spin_pattern :
    (1 * (1 + 2) - 9 : Int) = -6 ∧ (3 * (3 + 2) - 9 : Int) = 6 ∧ (6 - (-6) : Int) = 12 ∧
    (-8) * (-6 : Int) = 2 * 24 ∧ (-8) * (6 : Int) = -2 * 24 := by
  decide

/-- 35:C9, 35:X9 — the `Σ`–`Λ` fine structure: the light pair's `S_u·S_d` is `−3/4` at spin `0` and `+1/4` at spin `1`
(`4 S·S = 2S(S+1) − 3`: `−3`, `+1`); the strange quark's coupling to the pair, `2 S_s·(S_u + S_d) = S(S+1) − S_ud(S_ud+1) − 3/4`
at total spin `½` (`4S(S+1) = 3`): `0` for the spin-`0` pair, `−1` for the spin-`1` pair (`8 S_s·S_pair = 3 − 4S_ud(S_ud+1) − 3`: `0`, `−8`). So
`M_Σ − M_Λ = a_ll(1/4 + 3/4) + a_ls(−1 − 0) = a_ll − a_ls`. -/
theorem sigma_lambda :
    (2 * 0 * 1 - 3 : Int) = -3 ∧ (2 * 1 * 2 - 3 : Int) = 1 ∧ (1 - (-3) : Int) = 4 ∧
    (3 - 4 * (0 * 1) - 3 : Int) = 0 ∧ (3 - 4 * (1 * 2) - 3 : Int) = -8 := by
  decide

/-- 35:C8, 35:C13, 35:X8, 35:C21 — the charge structure with `9Q²` integral (`Q_u = 2/3`, `Q_d = −1/3`): one-body
`9 Σ Q² = 4 + 4 + 1 = 9` for the proton (`1`) and `4 + 1 + 1 = 6` for the neutron (`2/3`); two-body
`9 Σ_{i<j} Q_iQ_j = 4 − 2 − 2 = 0` for the proton and `−2 − 2 + 1 = −3` for the neutron (`−1/3`); both differences
`p − n` positive (`+3`, `+3`, that is `+1/3` each): the electromagnetic term makes the proton heavier. -/
theorem charge_structure :
    (4 + 4 + 1 : Int) = 9 ∧ (4 + 1 + 1 : Int) = 6 ∧ (2 * 2 + 2 * (-1) + 2 * (-1) : Int) = 0 ∧
    (2 * (-1) + 2 * (-1) + (-1) * (-1) : Int) = -3 ∧ (9 - 6 : Int) = 3 ∧ (0 - (-3) : Int) = 3 ∧ 0 < (3 : Int) := by
  decide

/-! ## The flavour and isospin relations as ring identities on the shell (35:C2, C3, C7, C11, C12, C16, C17, C18)

Every mass is a named expression in the shell's ring; a relation is `RE.sound`'s normalisation of both sides, so it holds on
every shell for every value of the parameters. Coefficients are written as repeated sums (`a + a + a` for `3a`), the dark
theme's convention, since a numeral on the shell is not definitionally a sum. -/

variable {p : Nat} [Pos p]

/-! ### The octet operator `M = M₀ + aY + 2c[I(I+1) − Y²/4]` (`b = 2c`, so the halves are integral) -/

/-- `N`: `Y = 1`, `I = 1/2`: `M₀ + a + b/2`. -/
def octN (m a c : Shell p) : Shell p := m + a + c

/-- `Λ`: `Y = 0`, `I = 0`: `M₀`. -/
def octL (m _a _c : Shell p) : Shell p := m

/-- `Σ`: `Y = 0`, `I = 1`: `M₀ + 2b`. -/
def octS (m _a c : Shell p) : Shell p := m + (c + c + c + c)

/-- `Ξ`: `Y = −1`, `I = 1/2`: `M₀ − a + b/2`. -/
def octX (m a c : Shell p) : Shell p := m + -a + c

/-- 35:C2, 35:X4, 35:P1 — Gell-Mann–Okubo as a ring identity: `2N + 2Ξ − 3Λ − Σ = 0` for every `M₀, a, c`; the scale and the breaking parameters cancel. -/
theorem gmo (m a c : Shell p) :
    octN m a c + octN m a c + (octX m a c + octX m a c) + -(octL m a c + octL m a c + octL m a c) + -octS m a c = 0 :=
  RE.sound (look [m, a, c]) (.add (.add (.add (.add (.add (.add (.var 0) (.var 1)) (.var 2)) (.add (.add (.var 0) (.var 1)) (.var 2))) (.add (.add (.add (.var 0) (.neg (.var 1))) (.var 2)) (.add (.add (.var 0) (.neg (.var 1))) (.var 2)))) (.neg (.add (.add (.var 0) (.var 0)) (.var 0)))) (.neg (.add (.var 0) (.add (.add (.add (.var 2) (.var 2)) (.var 2)) (.var 2))))) .zero (by decide +kernel)

/-! ### The decuplet at first order, `M = α + β n_s` -/

/-- `Δ`, `n_s = 0`. -/
def decD (m _b : Shell p) : Shell p := m

/-- `Σ*`, `n_s = 1`. -/
def decSs (m b : Shell p) : Shell p := m + b

/-- `Ξ*`, `n_s = 2`. -/
def decXs (m b : Shell p) : Shell p := m + b + b

/-- `Ω`, `n_s = 3`. -/
def decO (m b : Shell p) : Shell p := m + b + b + b

/-- 35:C3, 35:X5, 35:P2 — decuplet equal spacing as a ring identity: the two second differences `Δ − 2Σ* + Ξ*` and `Σ* − 2Ξ* + Ω` vanish for every `α, β`. -/
theorem spacing (m b : Shell p) :
    decD m b + -(decSs m b + decSs m b) + decXs m b = 0 ∧
    decSs m b + -(decXs m b + decXs m b) + decO m b = 0 :=
  ⟨RE.sound (look [m, b]) (.add (.add (.var 0) (.neg (.add (.add (.var 0) (.var 1)) (.add (.var 0) (.var 1))))) (.add (.add (.var 0) (.var 1)) (.var 1))) .zero (by decide +kernel),
   RE.sound (look [m, b]) (.add (.add (.add (.var 0) (.var 1)) (.neg (.add (.add (.add (.var 0) (.var 1)) (.var 1)) (.add (.add (.var 0) (.var 1)) (.var 1))))) (.add (.add (.add (.var 0) (.var 1)) (.var 1)) (.var 1))) .zero (by decide +kernel)⟩

/-! ### The linear-seed pairwise-hyperfine model, `A_ij = A (m/m_i)(m/m_j)`, `r = m/m_s`, with `A = 4a` so that the quarter
correlators `±1/4`, `−3/4` are integral: the decuplet pairs `+1/4`, the octet as in `Theme/Hadrons`'s `sigma_lambda` -/

/-- `Δ = M₀ + 3A/4`. -/
def hfD (m _d a _r : Shell p) : Shell p := m + (a + a + a)

/-- `Σ* = M₀ + d + (A/4)(1 + 2r)`. -/
def hfSs (m d a r : Shell p) : Shell p := m + d + a + (a * r + a * r)

/-- `Ξ* = M₀ + 2d + (A/4)(2r + r²)`. -/
def hfXs (m d a r : Shell p) : Shell p := m + d + d + (a * r + a * r) + a * r * r

/-- `Ω = M₀ + 3d + 3Ar²/4`. -/
def hfO (m d a r : Shell p) : Shell p := m + d + d + d + (a * r * r + a * r * r + a * r * r)

/-- `N = M₀ − 3A/4`. -/
def hfN (m _d a _r : Shell p) : Shell p := m + -(a + a + a)

/-- `Λ = M₀ + d − 3A/4` (the `ud` pair at spin `0`, the strange quark decoupled). -/
def hfL (m d a _r : Shell p) : Shell p := m + d + -(a + a + a)

/-- `Σ = M₀ + d + A(1/4 − r)`. -/
def hfS (m d a r : Shell p) : Shell p := m + d + a + -(a * r + a * r + a * r + a * r)

/-- `Ξ = M₀ + 2d + A(r²/4 − r)`. -/
def hfX (m d a r : Shell p) : Shell p := m + d + d + a * r * r + -(a * r + a * r + a * r + a * r)

/-- 35:C11, 35:P8 — the decuplet third difference vanishes identically in the model: `Δ − 3Σ* + 3Ξ* − Ω = 0` for every `M₀, d, A, r`. -/
theorem third_difference (m d a r : Shell p) :
    hfD m d a r + -(hfSs m d a r + hfSs m d a r + hfSs m d a r) + (hfXs m d a r + hfXs m d a r + hfXs m d a r) + -hfO m d a r = 0 :=
  RE.sound (look [m, d, a, r]) (.add (.add (.add (.add (.var 0) (.add (.add (.var 2) (.var 2)) (.var 2))) (.neg (.add (.add (.add (.add (.add (.var 0) (.var 1)) (.var 2)) (.add (.mul (.var 2) (.var 3)) (.mul (.var 2) (.var 3)))) (.add (.add (.add (.var 0) (.var 1)) (.var 2)) (.add (.mul (.var 2) (.var 3)) (.mul (.var 2) (.var 3))))) (.add (.add (.add (.var 0) (.var 1)) (.var 2)) (.add (.mul (.var 2) (.var 3)) (.mul (.var 2) (.var 3))))))) (.add (.add (.add (.add (.add (.add (.var 0) (.var 1)) (.var 1)) (.add (.mul (.var 2) (.var 3)) (.mul (.var 2) (.var 3)))) (.mul (.mul (.var 2) (.var 3)) (.var 3))) (.add (.add (.add (.add (.var 0) (.var 1)) (.var 1)) (.add (.mul (.var 2) (.var 3)) (.mul (.var 2) (.var 3)))) (.mul (.mul (.var 2) (.var 3)) (.var 3)))) (.add (.add (.add (.add (.var 0) (.var 1)) (.var 1)) (.add (.mul (.var 2) (.var 3)) (.mul (.var 2) (.var 3)))) (.mul (.mul (.var 2) (.var 3)) (.var 3))))) (.neg (.add (.add (.add (.add (.var 0) (.var 1)) (.var 1)) (.var 1)) (.add (.add (.mul (.mul (.var 2) (.var 3)) (.var 3)) (.mul (.mul (.var 2) (.var 3)) (.var 3))) (.mul (.mul (.var 2) (.var 3)) (.var 3)))))) .zero (by decide +kernel)

/-- 35:C12 — the two octet–decuplet hyperfine links, parameter-free: `3(Σ − Λ) = 2[(Δ − N) − (Σ* − Σ)]` and `(Σ* − Σ) − (Ξ* − Ξ) = 0`. -/
theorem hyperfine_links (m d a r : Shell p) :
    hfS m d a r + -hfL m d a r + (hfS m d a r + -hfL m d a r) + (hfS m d a r + -hfL m d a r) = hfD m d a r + -hfN m d a r + -(hfSs m d a r + -hfS m d a r) + (hfD m d a r + -hfN m d a r + -(hfSs m d a r + -hfS m d a r)) ∧
    hfSs m d a r + -hfS m d a r + -(hfXs m d a r + -hfX m d a r) = 0 :=
  ⟨RE.sound (look [m, d, a, r]) (.add (.add (.add (.add (.add (.add (.var 0) (.var 1)) (.var 2)) (.neg (.add (.add (.add (.mul (.var 2) (.var 3)) (.mul (.var 2) (.var 3))) (.mul (.var 2) (.var 3))) (.mul (.var 2) (.var 3))))) (.neg (.add (.add (.var 0) (.var 1)) (.neg (.add (.add (.var 2) (.var 2)) (.var 2)))))) (.add (.add (.add (.add (.var 0) (.var 1)) (.var 2)) (.neg (.add (.add (.add (.mul (.var 2) (.var 3)) (.mul (.var 2) (.var 3))) (.mul (.var 2) (.var 3))) (.mul (.var 2) (.var 3))))) (.neg (.add (.add (.var 0) (.var 1)) (.neg (.add (.add (.var 2) (.var 2)) (.var 2))))))) (.add (.add (.add (.add (.var 0) (.var 1)) (.var 2)) (.neg (.add (.add (.add (.mul (.var 2) (.var 3)) (.mul (.var 2) (.var 3))) (.mul (.var 2) (.var 3))) (.mul (.var 2) (.var 3))))) (.neg (.add (.add (.var 0) (.var 1)) (.neg (.add (.add (.var 2) (.var 2)) (.var 2))))))) (.add (.add (.add (.add (.var 0) (.add (.add (.var 2) (.var 2)) (.var 2))) (.neg (.add (.var 0) (.neg (.add (.add (.var 2) (.var 2)) (.var 2)))))) (.neg (.add (.add (.add (.add (.var 0) (.var 1)) (.var 2)) (.add (.mul (.var 2) (.var 3)) (.mul (.var 2) (.var 3)))) (.neg (.add (.add (.add (.var 0) (.var 1)) (.var 2)) (.neg (.add (.add (.add (.mul (.var 2) (.var 3)) (.mul (.var 2) (.var 3))) (.mul (.var 2) (.var 3))) (.mul (.var 2) (.var 3))))))))) (.add (.add (.add (.var 0) (.add (.add (.var 2) (.var 2)) (.var 2))) (.neg (.add (.var 0) (.neg (.add (.add (.var 2) (.var 2)) (.var 2)))))) (.neg (.add (.add (.add (.add (.var 0) (.var 1)) (.var 2)) (.add (.mul (.var 2) (.var 3)) (.mul (.var 2) (.var 3)))) (.neg (.add (.add (.add (.var 0) (.var 1)) (.var 2)) (.neg (.add (.add (.add (.mul (.var 2) (.var 3)) (.mul (.var 2) (.var 3))) (.mul (.var 2) (.var 3))) (.mul (.var 2) (.var 3)))))))))) (by decide +kernel),
   RE.sound (look [m, d, a, r]) (.add (.add (.add (.add (.add (.var 0) (.var 1)) (.var 2)) (.add (.mul (.var 2) (.var 3)) (.mul (.var 2) (.var 3)))) (.neg (.add (.add (.add (.var 0) (.var 1)) (.var 2)) (.neg (.add (.add (.add (.mul (.var 2) (.var 3)) (.mul (.var 2) (.var 3))) (.mul (.var 2) (.var 3))) (.mul (.var 2) (.var 3))))))) (.neg (.add (.add (.add (.add (.add (.var 0) (.var 1)) (.var 1)) (.add (.mul (.var 2) (.var 3)) (.mul (.var 2) (.var 3)))) (.mul (.mul (.var 2) (.var 3)) (.var 3))) (.neg (.add (.add (.add (.add (.var 0) (.var 1)) (.var 1)) (.mul (.mul (.var 2) (.var 3)) (.var 3))) (.neg (.add (.add (.add (.mul (.var 2) (.var 3)) (.mul (.var 2) (.var 3))) (.mul (.var 2) (.var 3))) (.mul (.var 2) (.var 3))))))))) .zero (by decide +kernel)⟩

/-! ### Isospin, the vector nonet, the gap and the split -/

/-- 35:C7, 35:X10, 35:P6 — Coleman–Glashow as a one-body identity: counting the `d − u` content, `n − p = δ`, `Ξ⁻ − Ξ⁰ = δ`, `Σ⁻ − Σ⁺ = 2δ`, so `(n − p) + (Ξ⁻ − Ξ⁰) − (Σ⁻ − Σ⁺) = 0` for every one-body unit `δ`. -/
theorem coleman_glashow (δ : Shell p) :
    δ + δ + -(δ + δ) = 0 :=
  RE.sound (look [δ]) (.add (.add (.var 0) (.var 0)) (.neg (.add (.var 0) (.var 0)))) .zero (by decide +kernel)

/-- `ρ`, `n_s = 0`: `M = a + b n_s`. -/
def vecRho (a _b : Shell p) : Shell p := a

/-- `K*`, `n_s = 1`. -/
def vecKs (a b : Shell p) : Shell p := a + b

/-- `φ`, `n_s = 2`. -/
def vecPhi (a b : Shell p) : Shell p := a + b + b

/-- 35:C18, 35:X12, 35:P9 — the vector-nonet equal spacing as a ring identity: `2K* − ρ − φ = 0` for every `a, b`. -/
theorem vector_spacing (a b : Shell p) :
    vecKs a b + vecKs a b + -vecRho a b + -vecPhi a b = 0 :=
  RE.sound (look [a, b]) (.add (.add (.add (.add (.var 0) (.var 1)) (.add (.var 0) (.var 1))) (.neg (.var 0))) (.neg (.add (.add (.var 0) (.var 1)) (.var 1)))) .zero (by decide +kernel)

/-- `M_Λ = 2m_l + m_s − 3u` with `v_ll = 4u` (the correlator sum `−3/4`). -/
def massL (l s u : Shell p) : Shell p := l + l + s + -(u + u + u)

/-- `M_N = 3m_l − 3u`, the same hyperfine. -/
def massN (l _s u : Shell p) : Shell p := l + l + l + -(u + u + u)

/-- 35:C16, 35:P11, 35:P10 — the Λ–N gap is the strange constituent excess: `M_Λ − M_N = m_s − m_l` for every `l, s, u`, the hyperfine cancelling. -/
theorem lambda_n_gap (l s u : Shell p) :
    massL l s u + -massN l s u = s + -l :=
  RE.sound (look [l, s, u]) (.add (.add (.add (.add (.var 0) (.var 0)) (.var 1)) (.neg (.add (.add (.var 2) (.var 2)) (.var 2)))) (.neg (.add (.add (.add (.var 0) (.var 0)) (.var 0)) (.neg (.add (.add (.var 2) (.var 2)) (.var 2)))))) (.add (.var 1) (.neg (.var 0))) (by decide +kernel)

/-- `M_N/√σ = 3λ_l − 3f` with `λ_hf = 4f`. -/
def splitN (l f : Shell p) : Shell p := l + l + l + -(f + f + f)

/-- `M_Δ/√σ = 3λ_l + 3f`. -/
def splitD (l f : Shell p) : Shell p := l + l + l + (f + f + f)

/-- 35:C17, 35:C19, 35:C16, 35:P10 — the exact spin split inverts: `M_N + M_Δ = 6λ_l` and `M_Δ − M_N = 6f = (3/2)λ_hf`, so `λ_l = (M_N + M_Δ)/6` and `λ_hf = (2/3)(M_Δ − M_N)`. -/
theorem spin_split (l f : Shell p) :
    splitN l f + splitD l f = l + l + l + l + l + l ∧
    splitD l f + -splitN l f = f + f + f + f + f + f :=
  ⟨RE.sound (look [l, f]) (.add (.add (.add (.add (.var 0) (.var 0)) (.var 0)) (.neg (.add (.add (.var 1) (.var 1)) (.var 1)))) (.add (.add (.add (.var 0) (.var 0)) (.var 0)) (.add (.add (.var 1) (.var 1)) (.var 1)))) (.add (.add (.add (.add (.add (.var 0) (.var 0)) (.var 0)) (.var 0)) (.var 0)) (.var 0)) (by decide +kernel),
   RE.sound (look [l, f]) (.add (.add (.add (.add (.var 0) (.var 0)) (.var 0)) (.add (.add (.var 1) (.var 1)) (.var 1))) (.neg (.add (.add (.add (.var 0) (.var 0)) (.var 0)) (.neg (.add (.add (.var 1) (.var 1)) (.var 1)))))) (.add (.add (.add (.add (.add (.var 1) (.var 1)) (.var 1)) (.var 1)) (.var 1)) (.var 1)) (by decide +kernel)⟩


/-! ## The admissible shells (35:C20, C23, X13, Z1) -/

/-- 35:C20, 35:C23, 35:X13, 35:Z1 — the colour rank is shell-independent: on every admissible shell `Ω ≡ 5 (mod 12)`,
`3 ∣ Ω + 1` (`12k + 6 = 3(4k + 2)`); the four laboratory shells `53, 173, 389, 1373` are admissible. -/
theorem admissible_shells :
    (∀ k : Nat, (12 * k + 5 + 1) % 3 = 0) ∧ [53, 173, 389, 1373].all (fun n => n % 12 == 5 && (n + 1) % 3 == 0) = true :=
  ⟨fun k => by
    have h : 12 * k + 5 + 1 = 3 * (4 * k + 2) + 0 := by rw [Nat.left_distrib, ← FRC.Nat.mul_assoc]
    rw [h]; exact FRC.Nat.add_mul_mod_self_left 0 (4 * k + 2) 3 (by decide), by decide⟩

/-! ## A Sturm count of the finite confinement operator (35:C16) -/

/-- The leading principal minors of the integer tridiagonal `M − μI`, `M = (N+1)³ T + L³ K` on `N` sites (`T` the
second-difference Laplacian, `K = diag(1, …, N)` the position; the grid `h = L/(N+1)` of `H = −u'' + x u` scaled by
`(N+1)³ h² = (N+1) L²`), by the recurrence `p_k = (M_kk − μ) p_{k−1} − c² p_{k−2}`, `c = (N+1)³`, with the running count of
sign changes along `p₀ = 1, p₁, …, p_k`: `(p_k, p_{k−1}, changes)`. -/
def sturmAux (N L : Nat) (μ : Int) : Nat → Int × Int × Nat
  | 0 => (1, 1, 0)
  | k + 1 =>
    let (pm, pmm, acc) := sturmAux N L μ k
    let c : Int := ((N + 1) ^ 3 : Nat)
    let d : Int := 2 * c + (L ^ 3 : Nat) * (k + 1 : Nat)
    let cur := (d - μ) * pm - (if k = 0 then 0 else c * c * pmm)
    (cur, pm, if (decide (cur < 0)) != (decide (pm < 0)) then acc + 1 else acc)

/-- Sturm's count of the eigenvalues of `M` below `μ`: the sign changes along the `N + 1` leading principal minors. An
eigenvalue `ε` of the grid operator corresponds to `μ = (N + 1) L² ε`. -/
def sturm (N L : Nat) (μ : Int) : Nat := (sturmAux N L μ N).2.2

/-- 35:C16 — the finite confinement operator `H^{(N)} = −u'' + x u` on `N = 200` sites of `[0, 16]`: Sturm's count of the
integer tridiagonal `201³ T + 16³ K` at `μ = 201 · 256 · ε` places exactly one eigenvalue in `(2.33, 2.34)`, one in
`(4.08, 4.09)`, one in `(5.51, 5.52)` and one in `(6.77, 6.79)`: the finite-stage spectrum sits at the decimals of the Airy
zeros to the grid's accuracy (the readout `2.338, 4.088, 5.521, 6.787` is the chart's). -/
theorem airy_sturm :
    sturm 200 16 (201 * 256 * 233 / 100) = 0 ∧ sturm 200 16 (201 * 256 * 234 / 100) = 1 ∧
    sturm 200 16 (201 * 256 * 408 / 100) = 1 ∧ sturm 200 16 (201 * 256 * 409 / 100) = 2 ∧
    sturm 200 16 (201 * 256 * 551 / 100) = 2 ∧ sturm 200 16 (201 * 256 * 552 / 100) = 3 ∧
    sturm 200 16 (201 * 256 * 677 / 100) = 3 ∧ sturm 200 16 (201 * 256 * 679 / 100) = 4 := by
  decide +kernel

end FRC.Hadrons
