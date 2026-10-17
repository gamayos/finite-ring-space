import FrcCore.Theme.Interactions
import FrcCore.Theme.Unitary

/-!
# FrcCore.Theme.Flavour — the flavour theme: 28-flavour's exact content (17 October 2026)

The flavour sector of *Fermion Flavour Sector over Finite Relational Substrate* (28-flavour), on the interactions theme's
Koide form (`koide_parseval`, `koide_two_thirds`, 00:G16) and the unitary file's `M3` and `Ext` normaliser. Every
statement is on a shell `Shell p` or its quadratic extension `Ext p ν`; every proof is the kernel's (`decide +kernel`
through the normalisers `RE.sound` and `xsound`, with explicit cofactors for the identities that hold modulo a
hypothesis), and no axiom enters.

* **The circulant (28:C1, C11).** `circ a b c` is the matrix with rows `(a b c)`, `(c a b)`, `(b c a)`. Products,
  transposes and adjugates of circulants are circulants (`circ_mul`, `circ_transpose`, `circ_adj`); the determinant is
  `a³ + b³ + c³ − 3abc` (`circ_det`), which at `c = b̄` is the cube invariant `a³ + 2 Re b³ − 3a N(b)`. On a cube root
  `ω² + ω + 1 = 0` the vectors `(1, ω^k, ω^{2k})` are eigenvectors with eigenvalues `λ_k = a + b ω^k + c ω^{2k}`
  (`circ_eigen`), `Σ λ_k = 3a` and `Σ λ_k² = 3a² + 6bc` (`eigen_sum`, `eigen_sumsq`): the Koide form.
* **The quarter-turn boundary (28:C3, X7).** With `i² = −1`, `2h = 1` and `b = −h(1 + i) a ω²`, `c = −h(1 − i) a ω`, the
  eigenvalue `λ₁` vanishes and `2bc = a²`: the massless generation sits at the quarter-turn diagonal
  (`quarter_turn_boundary`). The other two eigenvalues are `a h (3 ± s)` with `s = i(ω − ω²)`, `s² = 3`
  (`lo_eigen`), and `((3 − s)/(3 + s))² = 7 − 4s` (`lo_ratio_sq`): the leading-order ratio `m_μ/m_τ = 7 − 4√3`.
* **The amplitudes (28:C4, X2, X5, P2).** `N(1 − i) = 2` and `N(1 − ω) = 3` (`norm_one_sub_i`, `norm_one_sub_omega`);
  `Q = 5/6 ⟺ ρ² = 3/4` (`koide_five_sixths`), the up-quark value beside `koide_two_thirds`; the colour count 3
  against 1 on the sixteen (`colour_count`).
* **The texture (28:C6, C7, X3, X4, X6).** The role depths `(2, 1, 0)` give the exponents `(4, 2, 0)` and, doubled,
  `(8, 4, 0)` (`texture_exponents`); the two-by-two texture with a vanishing `(1,1)` entry has `tan²θ = −m₁/m₂`
  (`gst_relation`); the Cabibbo modulus `|s_d c_u − c_d s_u z|² = s_d² c_u² + c_d² s_u² − s_d c_u c_d s_u T(z)` on a
  unit `z` (`cabibbo_modulus`).
* **The mixing (28:C8, C10, X8, X10, P8).** `(A B)ᵀ = Bᵀ Aᵀ` and `(L D Rᵀ)ᵀ = R D Lᵀ` for a diagonal `D`
  (`transpose_mul`, `transpose_exchanges`); the shift fixes `(1, 1, 1)` and fixes no multiple of `(2, −1, −1)`
  (`protected_column`); `N(ω) = N(ω²) = 1` (`trimaximal`); `4(−ν h²) = 3`, that is `108 J² = 1` (`jarlskog_sq`);
  the trace relations `T(z²) = T(z)² − 2`, `T(z³) = T(z)³ − 3T(z)` of a unit (`trace_double`, `trace_triple`), the
  lock relations of 28:C5.
* **The seesaw (28:C11, X11).** `A · adj A = det A · 1` (`mul_adj`); `adj (c A) = c² adj A`; the seesaw of circulants is
  circulant (`seesaw_circulant`); with `M_R = c m_D` it collapses to `c² det(m_D) · m_Dᵀ` (`transpose_fixed_point`).
-/

namespace FRC.Flavour
open FRC.Shell FRC.Shell.Frame FRC.Extension FRC.Unitary FRC.Interactions

variable {p : Nat} [Pos p] {ν : Shell p}

/-! ## Reduction modulo hypotheses, in the extension -/

theorem xred1 {L R A X : Ext p ν} (e : L = R + A * X) (ha : A = 0) : L = R := by
  rw [ha, x_zero_mul, x_add_zero] at e; exact e

theorem xred2 {L R A B X Y : Ext p ν} (e : L = R + A * X + B * Y) (ha : A = 0) (hb : B = 0) : L = R := by
  rw [ha, hb, x_zero_mul, x_zero_mul, x_add_zero, x_add_zero] at e; exact e

theorem xred3 {L R A B C X Y Z : Ext p ν} (e : L = R + A * X + B * Y + C * Z) (ha : A = 0) (hb : B = 0) (hc : C = 0) :
    L = R := by
  rw [ha, hb, hc, x_zero_mul, x_zero_mul, x_zero_mul, x_add_zero, x_add_zero, x_add_zero] at e; exact e

theorem x_add_neg (a : Ext p ν) : a + -a = 0 := by rw [x_add_comm]; exact x_neg_add a

/-! ## The circulant (28:C1, 28:C11) -/

/-- The circulant with first row `(a, b, c)`: the rows `(a b c)`, `(c a b)`, `(b c a)`, that is `a·1 + b P + c P²` for
the cyclic shift `P`. -/
def circ (a b c : Ext p ν) : M3 p ν := ⟨a, b, c, c, a, b, b, c, a⟩

/-- The cyclic shift `P = circ 0 1 0`. -/
def shift : M3 p ν := circ 0 1 0

/-- The transpose. -/
def transpose (A : M3 p ν) : M3 p ν := ⟨A.a00, A.a10, A.a20, A.a01, A.a11, A.a21, A.a02, A.a12, A.a22⟩

/-- The diagonal matrix. -/
def diag (x y z : Ext p ν) : M3 p ν := ⟨x, 0, 0, 0, y, 0, 0, 0, z⟩

/-- 28:C11 — circulants are closed under the product: `circ a b c · circ a' b' c' = circ (aa' + bc' + cb') (ab' + ba' + cc')
(ac' + bb' + ca')`. -/
theorem circ_mul (a b c a' b' c' : Ext p ν) :
    mmul (circ a b c) (circ a' b' c') =
      circ (a * a' + b * c' + c * b') (a * b' + b * a' + c * c') (a * c' + b * b' + c * a') :=
  mext
    (xsound (xlook [a, b, c, a', b', c']) (.add (.add (.mul (.var 0) (.var 3)) (.mul (.var 1) (.var 5))) (.mul (.var 2) (.var 4))) (.add (.add (.mul (.var 0) (.var 3)) (.mul (.var 1) (.var 5))) (.mul (.var 2) (.var 4))) (by decide +kernel) : a * a' + b * c' + c * b' = a * a' + b * c' + c * b')
    (xsound (xlook [a, b, c, a', b', c']) (.add (.add (.mul (.var 0) (.var 4)) (.mul (.var 1) (.var 3))) (.mul (.var 2) (.var 5))) (.add (.add (.mul (.var 0) (.var 4)) (.mul (.var 1) (.var 3))) (.mul (.var 2) (.var 5))) (by decide +kernel) : a * b' + b * a' + c * c' = a * b' + b * a' + c * c')
    (xsound (xlook [a, b, c, a', b', c']) (.add (.add (.mul (.var 0) (.var 5)) (.mul (.var 1) (.var 4))) (.mul (.var 2) (.var 3))) (.add (.add (.mul (.var 0) (.var 5)) (.mul (.var 1) (.var 4))) (.mul (.var 2) (.var 3))) (by decide +kernel) : a * c' + b * b' + c * a' = a * c' + b * b' + c * a')
    (xsound (xlook [a, b, c, a', b', c']) (.add (.add (.mul (.var 2) (.var 3)) (.mul (.var 0) (.var 5))) (.mul (.var 1) (.var 4))) (.add (.add (.mul (.var 0) (.var 5)) (.mul (.var 1) (.var 4))) (.mul (.var 2) (.var 3))) (by decide +kernel) : c * a' + a * c' + b * b' = a * c' + b * b' + c * a')
    (xsound (xlook [a, b, c, a', b', c']) (.add (.add (.mul (.var 2) (.var 4)) (.mul (.var 0) (.var 3))) (.mul (.var 1) (.var 5))) (.add (.add (.mul (.var 0) (.var 3)) (.mul (.var 1) (.var 5))) (.mul (.var 2) (.var 4))) (by decide +kernel) : c * b' + a * a' + b * c' = a * a' + b * c' + c * b')
    (xsound (xlook [a, b, c, a', b', c']) (.add (.add (.mul (.var 2) (.var 5)) (.mul (.var 0) (.var 4))) (.mul (.var 1) (.var 3))) (.add (.add (.mul (.var 0) (.var 4)) (.mul (.var 1) (.var 3))) (.mul (.var 2) (.var 5))) (by decide +kernel) : c * c' + a * b' + b * a' = a * b' + b * a' + c * c')
    (xsound (xlook [a, b, c, a', b', c']) (.add (.add (.mul (.var 1) (.var 3)) (.mul (.var 2) (.var 5))) (.mul (.var 0) (.var 4))) (.add (.add (.mul (.var 0) (.var 4)) (.mul (.var 1) (.var 3))) (.mul (.var 2) (.var 5))) (by decide +kernel) : b * a' + c * c' + a * b' = a * b' + b * a' + c * c')
    (xsound (xlook [a, b, c, a', b', c']) (.add (.add (.mul (.var 1) (.var 4)) (.mul (.var 2) (.var 3))) (.mul (.var 0) (.var 5))) (.add (.add (.mul (.var 0) (.var 5)) (.mul (.var 1) (.var 4))) (.mul (.var 2) (.var 3))) (by decide +kernel) : b * b' + c * a' + a * c' = a * c' + b * b' + c * a')
    (xsound (xlook [a, b, c, a', b', c']) (.add (.add (.mul (.var 1) (.var 5)) (.mul (.var 2) (.var 4))) (.mul (.var 0) (.var 3))) (.add (.add (.mul (.var 0) (.var 3)) (.mul (.var 1) (.var 5))) (.mul (.var 2) (.var 4))) (by decide +kernel) : b * c' + c * b' + a * a' = a * a' + b * c' + c * b')

/-- 28:C11, 28:P5 — the transpose of a circulant is the circulant of the reversed row: `(circ a b c)ᵀ = circ a c b`. -/
theorem circ_transpose (a b c : Ext p ν) : transpose (circ a b c) = circ a c b := rfl

/-- 28:C11 — the adjugate of a circulant is a circulant: `adj (circ a b c) = circ (a² − bc) (c² − ab) (b² − ac)`. -/
theorem circ_adj (a b c : Ext p ν) :
    adj (circ a b c) = circ (a * a + -(b * c)) (c * c + -(a * b)) (b * b + -(a * c)) :=
  mext
    (xsound (xlook [a, b, c]) (.add (.mul (.var 0) (.var 0)) (.neg (.mul (.var 1) (.var 2)))) (.add (.mul (.var 0) (.var 0)) (.neg (.mul (.var 1) (.var 2)))) (by decide +kernel) : a * a + -(b * c) = a * a + -(b * c))
    (xsound (xlook [a, b, c]) (.add (.mul (.var 2) (.var 2)) (.neg (.mul (.var 1) (.var 0)))) (.add (.mul (.var 2) (.var 2)) (.neg (.mul (.var 0) (.var 1)))) (by decide +kernel) : c * c + -(b * a) = c * c + -(a * b))
    (xsound (xlook [a, b, c]) (.add (.mul (.var 1) (.var 1)) (.neg (.mul (.var 2) (.var 0)))) (.add (.mul (.var 1) (.var 1)) (.neg (.mul (.var 0) (.var 2)))) (by decide +kernel) : b * b + -(c * a) = b * b + -(a * c))
    (xsound (xlook [a, b, c]) (.add (.mul (.var 1) (.var 1)) (.neg (.mul (.var 2) (.var 0)))) (.add (.mul (.var 1) (.var 1)) (.neg (.mul (.var 0) (.var 2)))) (by decide +kernel) : b * b + -(c * a) = b * b + -(a * c))
    (xsound (xlook [a, b, c]) (.add (.mul (.var 0) (.var 0)) (.neg (.mul (.var 2) (.var 1)))) (.add (.mul (.var 0) (.var 0)) (.neg (.mul (.var 1) (.var 2)))) (by decide +kernel) : a * a + -(c * b) = a * a + -(b * c))
    (xsound (xlook [a, b, c]) (.add (.mul (.var 2) (.var 2)) (.neg (.mul (.var 0) (.var 1)))) (.add (.mul (.var 2) (.var 2)) (.neg (.mul (.var 0) (.var 1)))) (by decide +kernel) : c * c + -(a * b) = c * c + -(a * b))
    (xsound (xlook [a, b, c]) (.add (.mul (.var 2) (.var 2)) (.neg (.mul (.var 0) (.var 1)))) (.add (.mul (.var 2) (.var 2)) (.neg (.mul (.var 0) (.var 1)))) (by decide +kernel) : c * c + -(a * b) = c * c + -(a * b))
    (xsound (xlook [a, b, c]) (.add (.mul (.var 1) (.var 1)) (.neg (.mul (.var 0) (.var 2)))) (.add (.mul (.var 1) (.var 1)) (.neg (.mul (.var 0) (.var 2)))) (by decide +kernel) : b * b + -(a * c) = b * b + -(a * c))
    (xsound (xlook [a, b, c]) (.add (.mul (.var 0) (.var 0)) (.neg (.mul (.var 1) (.var 2)))) (.add (.mul (.var 0) (.var 0)) (.neg (.mul (.var 1) (.var 2)))) (by decide +kernel) : a * a + -(b * c) = a * a + -(b * c))

/-- 28:C1, 28:C5, 28:Z1 — the determinant of a circulant: `det (circ a b c) = a³ + b³ + c³ − 3abc`; at `c = b̄` this is the cube
invariant `∏ √m_k = a³ + 2 Re(b³) − 3a N(b)`, whose phase part `Re(b³)` carries the winding residue (28:Z1). -/
theorem circ_det (a b c : Ext p ν) :
    det (circ a b c) = a * a * a + b * b * b + c * c * c + -((1 + 1 + 1) * (a * b * c)) :=
  (xsound (xlook [a, b, c]) (.add (.add (.mul (.var 0) (.add (.mul (.var 0) (.var 0)) (.neg (.mul (.var 1) (.var 2))))) (.neg (.mul (.var 1) (.add (.mul (.var 2) (.var 0)) (.neg (.mul (.var 1) (.var 1))))))) (.mul (.var 2) (.add (.mul (.var 2) (.var 2)) (.neg (.mul (.var 0) (.var 1)))))) (.add (.add (.add (.mul (.mul (.var 0) (.var 0)) (.var 0)) (.mul (.mul (.var 1) (.var 1)) (.var 1))) (.mul (.mul (.var 2) (.var 2)) (.var 2))) (.neg (.mul (.add (.add .one .one) .one) (.mul (.mul (.var 0) (.var 1)) (.var 2))))) (by decide +kernel) : a * (a * a + -(b * c)) + -(b * (c * a + -(b * b))) + c * (c * c + -(a * b)) = a * a * a + b * b * b + c * c * c + -((1 + 1 + 1) * (a * b * c)))

/-- 28:C1, 28:X11 — on a cube root `ω² + ω + 1 = 0` the circulant has the eigenvectors `(1, ω, ω²)` and `(1, ω², ω)` with the
eigenvalues `λ₁ = a + bω + cω²` and `λ₂ = a + bω² + cω` (the first row gives `λ_k` itself; the second and third rows
give `ω^k λ_k` and `ω^{2k} λ_k`); the eigenvector `(1, 1, 1)` has `λ₀ = a + b + c`. Universality makes the amplitude
matrix a circulant, and this is its spectrum: the Koide functional form. -/
theorem circ_eigen (a b c ω : Ext p ν) (hω : ω * ω + ω + 1 = 0) :
    (c + a * ω + b * (ω * ω) = ω * (a + b * ω + c * (ω * ω))) ∧ (b + c * ω + a * (ω * ω) = (ω * ω) * (a + b * ω + c * (ω * ω))) ∧
    (c + a * (ω * ω) + b * ω = (ω * ω) * (a + b * (ω * ω) + c * ω)) ∧ (b + c * (ω * ω) + a * ω = ω * (a + b * (ω * ω) + c * ω)) :=
  ⟨(xred1 (xsound (xlook [a, b, c, ω]) (.add (.add (.var 2) (.mul (.var 0) (.var 3))) (.mul (.var 1) (.mul (.var 3) (.var 3)))) (.add (.mul (.var 3) (.add (.add (.var 0) (.mul (.var 1) (.var 3))) (.mul (.var 2) (.mul (.var 3) (.var 3))))) (.mul (.add (.add (.mul (.var 3) (.var 3)) (.var 3)) .one) (.add (.neg (.mul (.var 2) (.var 3))) (.var 2)))) (by decide +kernel) : c + a * ω + b * (ω * ω) = ω * (a + b * ω + c * (ω * ω)) + (ω * ω + ω + 1) * (-(c * ω) + c)) hω),
   (xred1 (xsound (xlook [a, b, c, ω]) (.add (.add (.var 1) (.mul (.var 2) (.var 3))) (.mul (.var 0) (.mul (.var 3) (.var 3)))) (.add (.mul (.mul (.var 3) (.var 3)) (.add (.add (.var 0) (.mul (.var 1) (.var 3))) (.mul (.var 2) (.mul (.var 3) (.var 3))))) (.mul (.add (.add (.mul (.var 3) (.var 3)) (.var 3)) .one) (.add (.add (.add (.neg (.mul (.var 1) (.var 3))) (.var 1)) (.neg (.mul (.mul (.var 2) (.var 3)) (.var 3)))) (.mul (.var 2) (.var 3))))) (by decide +kernel) : b + c * ω + a * (ω * ω) = ω * ω * (a + b * ω + c * (ω * ω)) + (ω * ω + ω + 1) * (-(b * ω) + b + -(c * ω * ω) + c * ω)) hω),
   (xred1 (xsound (xlook [a, b, c, ω]) (.add (.add (.var 2) (.mul (.var 0) (.mul (.var 3) (.var 3)))) (.mul (.var 1) (.var 3))) (.add (.mul (.mul (.var 3) (.var 3)) (.add (.add (.var 0) (.mul (.var 1) (.mul (.var 3) (.var 3)))) (.mul (.var 2) (.var 3)))) (.mul (.add (.add (.mul (.var 3) (.var 3)) (.var 3)) .one) (.add (.add (.add (.neg (.mul (.mul (.var 1) (.var 3)) (.var 3))) (.mul (.var 1) (.var 3))) (.neg (.mul (.var 2) (.var 3)))) (.var 2)))) (by decide +kernel) : c + a * (ω * ω) + b * ω = ω * ω * (a + b * (ω * ω) + c * ω) + (ω * ω + ω + 1) * (-(b * ω * ω) + b * ω + -(c * ω) + c)) hω),
   (xred1 (xsound (xlook [a, b, c, ω]) (.add (.add (.var 1) (.mul (.var 2) (.mul (.var 3) (.var 3)))) (.mul (.var 0) (.var 3))) (.add (.mul (.var 3) (.add (.add (.var 0) (.mul (.var 1) (.mul (.var 3) (.var 3)))) (.mul (.var 2) (.var 3)))) (.mul (.add (.add (.mul (.var 3) (.var 3)) (.var 3)) .one) (.add (.neg (.mul (.var 1) (.var 3))) (.var 1)))) (by decide +kernel) : b + c * (ω * ω) + a * ω = ω * (a + b * (ω * ω) + c * ω) + (ω * ω + ω + 1) * (-(b * ω) + b)) hω)⟩

/-- 28:C1 — the eigenvalues sum to `3a`: `λ₀ + λ₁ + λ₂ = 3a`. -/
theorem eigen_sum (a b c ω : Ext p ν) (hω : ω * ω + ω + 1 = 0) :
    a + b + c + (a + b * ω + c * (ω * ω)) + (a + b * (ω * ω) + c * ω) = (1 + 1 + 1) * a :=
  (xred1 (xsound (xlook [a, b, c, ω]) (.add (.add (.add (.add (.var 0) (.var 1)) (.var 2)) (.add (.add (.var 0) (.mul (.var 1) (.var 3))) (.mul (.var 2) (.mul (.var 3) (.var 3))))) (.add (.add (.var 0) (.mul (.var 1) (.mul (.var 3) (.var 3)))) (.mul (.var 2) (.var 3)))) (.add (.mul (.add (.add .one .one) .one) (.var 0)) (.mul (.add (.add (.mul (.var 3) (.var 3)) (.var 3)) .one) (.add (.var 1) (.var 2)))) (by decide +kernel) : a + b + c + (a + b * ω + c * (ω * ω)) + (a + b * (ω * ω) + c * ω) = (1 + 1 + 1) * a + (ω * ω + ω + 1) * (b + c)) hω)

/-- 28:C1, 28:C2, 28:C11b — the squares of the eigenvalues sum to `3a² + 6bc`: at `c = b̄` this is `3a² + 6 N(b)`, so
`Q = Σλ²/(Σλ)² = 1/3 + (2/3) N(b)/a²`, the Koide form with `ρ² = N(b)/a²` (`koide_parseval`). -/
theorem eigen_sumsq (a b c ω : Ext p ν) (hω : ω * ω + ω + 1 = 0) :
    (a + b + c) * (a + b + c) + (a + b * ω + c * (ω * ω)) * (a + b * ω + c * (ω * ω)) + (a + b * (ω * ω) + c * ω) * (a + b * (ω * ω) + c * ω) = (1 + 1 + 1) * (a * a) + (1 + 1 + 1 + 1 + 1 + 1) * (b * c) :=
  (xred1 (xsound (xlook [a, b, c, ω]) (.add (.add (.mul (.add (.add (.var 0) (.var 1)) (.var 2)) (.add (.add (.var 0) (.var 1)) (.var 2))) (.mul (.add (.add (.var 0) (.mul (.var 1) (.var 3))) (.mul (.var 2) (.mul (.var 3) (.var 3)))) (.add (.add (.var 0) (.mul (.var 1) (.var 3))) (.mul (.var 2) (.mul (.var 3) (.var 3)))))) (.mul (.add (.add (.var 0) (.mul (.var 1) (.mul (.var 3) (.var 3)))) (.mul (.var 2) (.var 3))) (.add (.add (.var 0) (.mul (.var 1) (.mul (.var 3) (.var 3)))) (.mul (.var 2) (.var 3))))) (.add (.add (.mul (.add (.add .one .one) .one) (.mul (.var 0) (.var 0))) (.mul (.add (.add (.add (.add (.add .one .one) .one) .one) .one) .one) (.mul (.var 1) (.var 2)))) (.mul (.add (.add (.mul (.var 3) (.var 3)) (.var 3)) .one) (.add (.add (.add (.add (.add (.add (.add (.add (.add (.mul (.add .one .one) (.mul (.var 0) (.var 1))) (.mul (.add .one .one) (.mul (.var 0) (.var 2)))) (.mul (.mul (.mul (.var 1) (.var 1)) (.var 3)) (.var 3))) (.neg (.mul (.mul (.var 1) (.var 1)) (.var 3)))) (.mul (.var 1) (.var 1))) (.mul (.add (.add (.add .one .one) .one) .one) (.mul (.mul (.var 1) (.var 2)) (.var 3)))) (.neg (.mul (.add (.add (.add .one .one) .one) .one) (.mul (.var 1) (.var 2))))) (.mul (.mul (.mul (.var 2) (.var 2)) (.var 3)) (.var 3))) (.neg (.mul (.mul (.var 2) (.var 2)) (.var 3)))) (.mul (.var 2) (.var 2))))) (by decide +kernel) : (a + b + c) * (a + b + c) + (a + b * ω + c * (ω * ω)) * (a + b * ω + c * (ω * ω)) + (a + b * (ω * ω) + c * ω) * (a + b * (ω * ω) + c * ω) = (1 + 1 + 1) * (a * a) + (1 + 1 + 1 + 1 + 1 + 1) * (b * c) + (ω * ω + ω + 1) * ((1 + 1) * (a * b) + (1 + 1) * (a * c) + b * b * ω * ω + -(b * b * ω) + b * b + (1 + 1 + 1 + 1) * (b * c * ω) + -((1 + 1 + 1 + 1) * (b * c)) + c * c * ω * ω + -(c * c * ω) + c * c)) hω)

/-! ## The quarter-turn boundary and the leading-order spectrum (28:C3, 28:X7) -/

/-- 28:C3, 28:X7 — the massless generation sits at the quarter-turn diagonal. With `i² = −1`, `ω² + ω + 1 = 0` and
`h + h = 1`, the circulant `(a, b, c)` with `b = −h(1 + i) a ω²` and `c = −h(1 − i) a ω` (so `c = b̄` when `a, h` are
real, `ī = −i`, `ω̄ = ω²`) has `λ₁ = a + bω + cω² = 0` and `2bc = a²`: the vanishing eigenvalue and the Koide value
`Q = 2/3` (`2N(b) = a²`) at once. -/
theorem quarter_turn_boundary (a i ω h : Ext p ν) (hi : i * i + 1 = 0) (hω : ω * ω + ω + 1 = 0) (hh : h + h = 1) :
    a + (-(h * (1 + i) * a)) * (ω * ω) * ω + (-(h * (1 + -i) * a)) * ω * (ω * ω) = 0 ∧ (1 + 1) * ((-(h * (1 + i) * a)) * (ω * ω) * ((-(h * (1 + -i) * a)) * ω)) = a * a := by
  have hA : h + h + -1 = 0 := by rw [hh, x_add_neg]
  exact ⟨(xred3 (xsound (xlook [a, i, ω, h]) (.add (.add (.var 0) (.mul (.mul (.neg (.mul (.mul (.var 3) (.add .one (.var 1))) (.var 0))) (.mul (.var 2) (.var 2))) (.var 2))) (.mul (.mul (.neg (.mul (.mul (.var 3) (.add .one (.neg (.var 1)))) (.var 0))) (.var 2)) (.mul (.var 2) (.var 2)))) (.add (.add (.add .zero (.mul (.add (.mul (.var 1) (.var 1)) .one) .zero)) (.mul (.add (.add (.mul (.var 2) (.var 2)) (.var 2)) .one) (.add (.neg (.mul (.add .one .one) (.mul (.mul (.var 0) (.var 2)) (.var 3)))) (.mul (.add .one .one) (.mul (.var 0) (.var 3)))))) (.mul (.add (.add (.var 3) (.var 3)) (.neg .one)) (.neg (.var 0)))) (by decide +kernel) : a + (-(h * (1 + i) * a)) * (ω * ω) * ω + (-(h * (1 + -i) * a)) * ω * (ω * ω) = 0 + (i * i + 1) * 0 + (ω * ω + ω + 1) * (-((1 + 1) * (a * ω * h)) + (1 + 1) * (a * h)) + (h + h + -1) * (-a)) hi hω hA),
    (xred3 (xsound (xlook [a, i, ω, h]) (.mul (.add .one .one) (.mul (.mul (.neg (.mul (.mul (.var 3) (.add .one (.var 1))) (.var 0))) (.mul (.var 2) (.var 2))) (.mul (.neg (.mul (.mul (.var 3) (.add .one (.neg (.var 1)))) (.var 0))) (.var 2)))) (.add (.add (.add (.mul (.var 0) (.var 0)) (.mul (.add (.mul (.var 1) (.var 1)) .one) (.neg (.mul (.add .one .one) (.mul (.mul (.mul (.mul (.mul (.mul (.var 0) (.var 0)) (.var 2)) (.var 2)) (.var 2)) (.var 3)) (.var 3)))))) (.mul (.add (.add (.mul (.var 2) (.var 2)) (.var 2)) .one) (.add (.mul (.add (.add (.add .one .one) .one) .one) (.mul (.mul (.mul (.mul (.var 0) (.var 0)) (.var 2)) (.var 3)) (.var 3))) (.neg (.mul (.add (.add (.add .one .one) .one) .one) (.mul (.mul (.mul (.var 0) (.var 0)) (.var 3)) (.var 3))))))) (.mul (.add (.add (.var 3) (.var 3)) (.neg .one)) (.add (.mul (.add .one .one) (.mul (.mul (.var 0) (.var 0)) (.var 3))) (.mul (.var 0) (.var 0))))) (by decide +kernel) : (1 + 1) * ((-(h * (1 + i) * a)) * (ω * ω) * ((-(h * (1 + -i) * a)) * ω)) = a * a + (i * i + 1) * (-((1 + 1) * (a * a * ω * ω * ω * h * h))) + (ω * ω + ω + 1) * ((1 + 1 + 1 + 1) * (a * a * ω * h * h) + -((1 + 1 + 1 + 1) * (a * a * h * h))) + (h + h + -1) * ((1 + 1) * (a * a * h) + a * a)) hi hω hA)⟩

/-- 28:C3, 28:X7 — the leading-order spectrum. At the boundary of `quarter_turn_boundary` the two remaining eigenvalues
are `λ₀ = a h (3 + s)` and `λ₂ = a h (3 − s)` with `s = i (ω − ω²)`, and `s² = 3`: the square-root masses
`(0, 3 − √3, 3 + √3)·ah`, the ratios `m_e : m_μ : m_τ = 0 : (2 − √3)² : 1`. -/
theorem lo_eigen (a i ω h : Ext p ν) (hi : i * i + 1 = 0) (hω : ω * ω + ω + 1 = 0) (hh : h + h = 1) :
    a + (-(h * (1 + i) * a)) * (ω * ω) + (-(h * (1 + -i) * a)) * ω = a * h * (1 + 1 + 1 + i * (ω + -(ω * ω))) ∧ a + (-(h * (1 + i) * a)) * (ω * ω) * (ω * ω) + (-(h * (1 + -i) * a)) * ω * ω = a * h * (1 + 1 + 1 + -(i * (ω + -(ω * ω)))) ∧ i * (ω + -(ω * ω)) * (i * (ω + -(ω * ω))) = 1 + 1 + 1 := by
  have hA : h + h + -1 = 0 := by rw [hh, x_add_neg]
  exact ⟨(xred3 (xsound (xlook [a, i, ω, h]) (.add (.add (.var 0) (.mul (.neg (.mul (.mul (.var 3) (.add .one (.var 1))) (.var 0))) (.mul (.var 2) (.var 2)))) (.mul (.neg (.mul (.mul (.var 3) (.add .one (.neg (.var 1)))) (.var 0))) (.var 2))) (.add (.add (.add (.mul (.mul (.var 0) (.var 3)) (.add (.add (.add .one .one) .one) (.mul (.var 1) (.add (.var 2) (.neg (.mul (.var 2) (.var 2))))))) (.mul (.add (.mul (.var 1) (.var 1)) .one) .zero)) (.mul (.add (.add (.mul (.var 2) (.var 2)) (.var 2)) .one) (.neg (.mul (.var 0) (.var 3))))) (.mul (.add (.add (.var 3) (.var 3)) (.neg .one)) (.neg (.var 0)))) (by decide +kernel) : a + (-(h * (1 + i) * a)) * (ω * ω) + (-(h * (1 + -i) * a)) * ω = a * h * (1 + 1 + 1 + i * (ω + -(ω * ω))) + (i * i + 1) * 0 + (ω * ω + ω + 1) * (-(a * h)) + (h + h + -1) * (-a)) hi hω hA),
    (xred3 (xsound (xlook [a, i, ω, h]) (.add (.add (.var 0) (.mul (.mul (.neg (.mul (.mul (.var 3) (.add .one (.var 1))) (.var 0))) (.mul (.var 2) (.var 2))) (.mul (.var 2) (.var 2)))) (.mul (.mul (.neg (.mul (.mul (.var 3) (.add .one (.neg (.var 1)))) (.var 0))) (.var 2)) (.var 2))) (.add (.add (.add (.mul (.mul (.var 0) (.var 3)) (.add (.add (.add .one .one) .one) (.neg (.mul (.var 1) (.add (.var 2) (.neg (.mul (.var 2) (.var 2)))))))) (.mul (.add (.mul (.var 1) (.var 1)) .one) .zero)) (.mul (.add (.add (.mul (.var 2) (.var 2)) (.var 2)) .one) (.add (.add (.add (.add (.neg (.mul (.mul (.mul (.mul (.var 0) (.var 1)) (.var 2)) (.var 2)) (.var 3))) (.mul (.mul (.mul (.var 0) (.var 1)) (.var 2)) (.var 3))) (.neg (.mul (.mul (.mul (.var 0) (.var 2)) (.var 2)) (.var 3)))) (.mul (.mul (.var 0) (.var 2)) (.var 3))) (.neg (.mul (.var 0) (.var 3)))))) (.mul (.add (.add (.var 3) (.var 3)) (.neg .one)) (.neg (.var 0)))) (by decide +kernel) : a + (-(h * (1 + i) * a)) * (ω * ω) * (ω * ω) + (-(h * (1 + -i) * a)) * ω * ω = a * h * (1 + 1 + 1 + -(i * (ω + -(ω * ω)))) + (i * i + 1) * 0 + (ω * ω + ω + 1) * (-(a * i * ω * ω * h) + a * i * ω * h + -(a * ω * ω * h) + a * ω * h + -(a * h)) + (h + h + -1) * (-a)) hi hω hA),
    (xred2 (xsound (xlook [a, i, ω, h]) (.mul (.mul (.var 1) (.add (.var 2) (.neg (.mul (.var 2) (.var 2))))) (.mul (.var 1) (.add (.var 2) (.neg (.mul (.var 2) (.var 2)))))) (.add (.add (.add (.add .one .one) .one) (.mul (.add (.mul (.var 1) (.var 1)) .one) (.add (.add (.mul (.mul (.mul (.var 2) (.var 2)) (.var 2)) (.var 2)) (.neg (.mul (.add .one .one) (.mul (.mul (.var 2) (.var 2)) (.var 2))))) (.mul (.var 2) (.var 2))))) (.mul (.add (.add (.mul (.var 2) (.var 2)) (.var 2)) .one) (.add (.add (.neg (.mul (.var 2) (.var 2))) (.mul (.add (.add .one .one) .one) (.var 2))) (.neg (.add (.add .one .one) .one))))) (by decide +kernel) : i * (ω + -(ω * ω)) * (i * (ω + -(ω * ω))) = 1 + 1 + 1 + (i * i + 1) * (ω * ω * ω * ω + -((1 + 1) * (ω * ω * ω)) + ω * ω) + (ω * ω + ω + 1) * (-(ω * ω) + (1 + 1 + 1) * ω + -(1 + 1 + 1))) hi hω)⟩

/-- 28:C3, 28:X7 — with `s² = 3`, `(3 − s)² = (7 − 4s)(3 + s)²`: the leading-order ratio `(λ₂/λ₀)² = m_μ/m_τ` is
`7 − 4√3 = (2 − √3)² ≈ 0.0718` (observed `0.0595`). -/
theorem lo_ratio_sq (s : Ext p ν) (hs : s * s + -(1 + 1 + 1) = 0) :
    (1 + 1 + 1 + -s) * (1 + 1 + 1 + -s) = (1 + 1 + 1 + 1 + 1 + 1 + 1 + -((1 + 1 + 1 + 1) * s)) * ((1 + 1 + 1 + s) * (1 + 1 + 1 + s)) :=
  (xred1 (xsound (xlook [s]) (.mul (.add (.add (.add .one .one) .one) (.neg (.var 0))) (.add (.add (.add .one .one) .one) (.neg (.var 0)))) (.add (.mul (.add (.add (.add (.add (.add (.add (.add .one .one) .one) .one) .one) .one) .one) (.neg (.mul (.add (.add (.add .one .one) .one) .one) (.var 0)))) (.mul (.add (.add (.add .one .one) .one) (.var 0)) (.add (.add (.add .one .one) .one) (.var 0)))) (.mul (.add (.mul (.var 0) (.var 0)) (.neg (.add (.add .one .one) .one))) (.add (.mul (.add (.add (.add .one .one) .one) .one) (.var 0)) (.add (.add (.add (.add (.add (.add (.add (.add (.add (.add (.add (.add (.add (.add (.add (.add (.add .one .one) .one) .one) .one) .one) .one) .one) .one) .one) .one) .one) .one) .one) .one) .one) .one) .one)))) (by decide +kernel) : (1 + 1 + 1 + -s) * (1 + 1 + 1 + -s) = (1 + 1 + 1 + 1 + 1 + 1 + 1 + -((1 + 1 + 1 + 1) * s)) * ((1 + 1 + 1 + s) * (1 + 1 + 1 + s)) + (s * s + -(1 + 1 + 1)) * ((1 + 1 + 1 + 1) * s + (1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1))) hs)

/-- 28:C3 — the leading phase as a cycle fraction: `δ_LO = 3/8 − 1/3 = 1/24`, that is `9 − 8 = 1` over the common
denominator `24 = 3 · 8`. -/
theorem delta_lo : (3 : Nat) * 3 = 8 + 1 ∧ 24 = 3 * 8 := by decide

/-! ## The amplitudes (28:C4, 28:X2, 28:X5, 28:P2) -/

/-- 28:C4, 28:X2, 28:P2, 00:G17 — the quarter-turn norm: `(1 − i)(1 + i) = 2` on every shell with `i² = −1`; the squared amplitude
of a colourless sector, `r² = N(1 − i) = 2`, so `Q = 1/3 + r²/6 = 2/3`. -/
theorem norm_one_sub_i {i : Shell p} (hi : i * i + 1 = 0) : (1 + -i) * (1 + i) = 2 := by
  rw [FRC.Interactions.two_eq]
  exact red1 (RE.sound (look [i])
    (.mul (.add .one (.neg (.var 0))) (.add .one (.var 0)))
    (.add (.add .one .one) (.mul (.add (.mul (.var 0) (.var 0)) .one) (.neg .one)))
    (by decide +kernel) :
    (1 + -i) * (1 + i) = (1 + 1) + (i * i + 1) * -1) hi

/-- 28:C4, 28:X2, 28:P2, 00:G17 — the colour norm: `N(1 − ω) = 3` for the cube root `ω = −h + h w` of the extension at `ν = −3`
(`h + h = 1`); the squared amplitude of a coloured sector, `r² = N(1 − ω) = 3`, so `Q = 1/3 + r²/6 = 5/6`. -/
theorem norm_one_sub_omega {h : Shell p} (hh : h + h = 1) (hν : ν + 1 + 1 + 1 = 0) :
    Ext.norm ((1 : Ext p ν) + -(omega3 ν h)) = 3 := by
  have hA : h + h + -1 = 0 := by rw [hh, add_neg]
  rw [FRC.Interactions.three_eq]
  exact red2 (RE.sound (look [ν, h])
    (.add (.mul (.add .one (.neg (.neg (.var 1)))) (.add .one (.neg (.neg (.var 1))))) (.neg (.mul (.var 0) (.mul (.add .zero (.neg (.var 1))) (.add .zero (.neg (.var 1)))))))
    (.add (.add (.add (.add .one .one) .one) (.mul (.add (.add (.var 1) (.var 1)) (.neg .one)) (.add (.add (.var 1) (.var 1)) (.add .one .one)))) (.mul (.add (.add (.add (.var 0) .one) .one) .one) (.neg (.mul (.var 1) (.var 1)))))
    (by decide +kernel) :
    (1 + - -h) * (1 + - -h) + -(ν * ((0 + -h) * (0 + -h))) = (1 + 1 + 1) + (h + h + -1) * (h + h + (1 + 1)) + (ν + 1 + 1 + 1) * -(h * h)) hA hν

/-- 28:C4, 28:X2, 28:P2 — the up-quark Koide value: `Q = 5/6 ⟺ ρ² = 3/4`, that is `6 Σ a_j² = 5 â₀²` exactly when
`4 â₁ â₂ = 3 â₀²` (beside `koide_two_thirds`, `Q = 2/3 ⟺ 2 â₁ â₂ = â₀²`); with `â₁ â₂ = N(b)` and `r² = 4N(b)/a²`
this is `r² = 3`, the colour norm. -/
theorem koide_five_sixths (a₀ a₁ a₂ ω : Shell p) (hω : ω * ω + ω + 1 = 0) :
    (1 + 1 + 1 + 1 + 1 + 1) * (a₀ * a₀ + a₁ * a₁ + a₂ * a₂) = (1 + 1 + 1 + 1 + 1) * ((a₀ + a₁ + a₂) * (a₀ + a₁ + a₂)) ↔
      (1 + 1 + 1 + 1) * ((a₀ + a₁ * ω + a₂ * (ω * ω)) * (a₀ + a₁ * (ω * ω) + a₂ * ω)) =
        (1 + 1 + 1) * ((a₀ + a₁ + a₂) * (a₀ + a₁ + a₂)) := by
  have hp := koide_parseval a₀ a₁ a₂ ω hω
  rw [FRC.Interactions.three_eq, FRC.Interactions.two_eq] at hp
  have e : (1 + 1 + 1 + 1 + 1 + 1) * (a₀ * a₀ + a₁ * a₁ + a₂ * a₂) = (1 + 1) * ((1 + 1 + 1) * (a₀ * a₀ + a₁ * a₁ + a₂ * a₂)) :=
    RE.sound (look [a₀, a₁, a₂]) (.mul (.add (.add (.add (.add (.add .one .one) .one) .one) .one) .one) (.add (.add (.mul (.var 0) (.var 0)) (.mul (.var 1) (.var 1))) (.mul (.var 2) (.var 2)))) (.mul (.add .one .one) (.mul (.add (.add .one .one) .one) (.add (.add (.mul (.var 0) (.var 0)) (.mul (.var 1) (.var 1))) (.mul (.var 2) (.var 2))))) (by decide +kernel)
  rw [e, hp]
  generalize (a₀ + a₁ + a₂) * (a₀ + a₁ + a₂) = S
  generalize (a₀ + a₁ * ω + a₂ * (ω * ω)) * (a₀ + a₁ * (ω * ω) + a₂ * ω) = P
  have e2 : (1 + 1) * (S + (1 + 1) * P) = (1 + 1 + 1 + 1) * P + (1 + 1) * S :=
    RE.sound (look [S, P]) (.mul (.add .one .one) (.add (.var 0) (.mul (.add .one .one) (.var 1)))) (.add (.mul (.add (.add (.add .one .one) .one) .one) (.var 1)) (.mul (.add .one .one) (.var 0))) (by decide +kernel)
  have e3 : (1 + 1 + 1 + 1 + 1) * S = (1 + 1 + 1) * S + (1 + 1) * S :=
    RE.sound (look [S]) (.mul (.add (.add (.add (.add .one .one) .one) .one) .one) (.var 0)) (.add (.mul (.add (.add .one .one) .one) (.var 0)) (.mul (.add .one .one) (.var 0))) (by decide +kernel)
  rw [e2, e3]
  constructor
  · intro h; exact add_right_cancel h
  · intro h; rw [h]

/-- 28:X5, 00:G17 — the Georgi–Jarlskog factor is the colour count: on the sixteen the down-type antiquarks `d^c` (colour indices
`2`, weak indices `2`, `6Y = 2`) are three states and the charged antilepton `e^c` (`0`, `2`, `6Y = 6`) one, the colour
triplet against the colour singlet, `N_c = 3`; the scale-robust double ratio is `N_c² = 9`. -/
theorem colour_count :
    (gen16.filter (fun S => col S == 2 && wk S == 2 && y6 S == 2)).length = 3 ∧
    (gen16.filter (fun S => col S == 0 && wk S == 2 && y6 S == 6)).length = 1 ∧ (3 : Nat) * 3 = 9 := by
  decide +kernel

/-! ## The texture (28:C6, 28:C7, 28:X3, 28:X4, 28:X6) -/

/-- The `i`-th entry of a list of charges (`0` past the end), by structural recursion. -/
def nth : List Nat → Nat → Nat
  | [], _ => 0
  | x :: _, 0 => x
  | _ :: l, n + 1 => nth l n

/-- The Froggatt–Nielsen exponent of the entry `(i, j)` for the charges `n`: `n_i + n_j`. -/
def expo (n : List Nat) (i j : Nat) : Nat := nth n i + nth n j

/-- 28:C7, 28:X3, 28:X6, 00:G17 — the role depths `(2, 1, 0)` as flavour charges: the down and lepton masses carry the exponents
`2n = (4, 2, 0)` (the charge-carrying `10` enters once), the up masses `4n = (8, 4, 0) = 2 · (4, 2, 0)` (the `10 · 10`
Yukawa enters it twice), and every exponent matrix `n_i + n_j` is symmetric. -/
theorem texture_exponents :
    [2, 1, 0].map (fun k => 2 * k) = [4, 2, 0] ∧ [2, 1, 0].map (fun k => 4 * k) = [8, 4, 0] ∧
    [4, 2, 0].map (fun k => 2 * k) = [8, 4, 0] ∧
    (List.range 3).all (fun i => (List.range 3).all (fun j => expo [2, 1, 0] i j == expo [2, 1, 0] j i)) = true ∧
    (List.range 3).all (fun i => (List.range 3).all (fun j => expo [4, 2, 0] i j == expo [4, 2, 0] j i)) = true := by
  decide +kernel

/-- 28:C6, 28:X4, 28:P3 — the Gatto–Sartori–Tonin relation. A symmetric two-by-two texture `R D Rᵀ` with `R` the rotation
`(c, −s; s, c)`, `c² + s² = 1`, and `D = diag(m₁, m₂)` has the `(1,1)` entry `m₁ c² + m₂ s²`; when that entry vanishes
(the texture zero), `m₂ s² = −m₁ c²`, that is `tan²θ = −m₁/m₂`: the Cabibbo angle from the two light masses. -/
theorem gst_relation (c s m₁ m₂ : Shell p) (_hc : c * c + s * s = 1) (h0 : m₁ * (c * c) + m₂ * (s * s) = 0) :
    m₂ * (s * s) = -(m₁ * (c * c)) := by
  have e : m₂ * (s * s) = -(m₁ * (c * c)) + (m₁ * (c * c) + m₂ * (s * s)) :=
    RE.sound (look [c, s, m₁, m₂]) (.mul (.var 3) (.mul (.var 1) (.var 1))) (.add (.neg (.mul (.var 2) (.mul (.var 0) (.var 0)))) (.add (.mul (.var 2) (.mul (.var 0) (.var 0))) (.mul (.var 3) (.mul (.var 1) (.var 1))))) (by decide +kernel)
  rw [e, h0, add_zero]

/-- 28:C6, 28:X4, 28:P3 — the full Cabibbo relation: for a unit `z` (`z z̄ = 1`, the relative winding phase `e^{iφ}`) the
modulus `|s_d c_u − c_d s_u z|² = s_d² c_u² + c_d² s_u² − s_d c_u c_d s_u T(z)` with `T(z) = z + z̄ = 2 cos φ`; with
`s_d = √(m_d/m_s)` and `s_u = √(m_u/m_c)` this is `V_us = |√(m_d/m_s) − e^{iφ} √(m_u/m_c)|`. -/
theorem cabibbo_modulus (sd cu cd su z : Ext p ν) (hz : z * Ext.conj z = 1) :
    (sd * cu + -(cd * su * z)) * (sd * cu + -(cd * su * Ext.conj z)) = sd * cu * (sd * cu) + cd * su * (cd * su) + -(sd * cu * (cd * su) * (z + Ext.conj z)) := by
  have hz' : z * Ext.conj z + -1 = 0 := by rw [hz, x_add_neg]
  exact (xred1 (xsound (xlook [sd, cu, cd, su, z, Ext.conj z]) (.mul (.add (.mul (.var 0) (.var 1)) (.neg (.mul (.mul (.var 2) (.var 3)) (.var 4)))) (.add (.mul (.var 0) (.var 1)) (.neg (.mul (.mul (.var 2) (.var 3)) (.var 5))))) (.add (.add (.add (.mul (.mul (.var 0) (.var 1)) (.mul (.var 0) (.var 1))) (.mul (.mul (.var 2) (.var 3)) (.mul (.var 2) (.var 3)))) (.neg (.mul (.mul (.mul (.var 0) (.var 1)) (.mul (.var 2) (.var 3))) (.add (.var 4) (.var 5))))) (.mul (.add (.mul (.var 4) (.var 5)) (.neg .one)) (.mul (.mul (.mul (.var 2) (.var 2)) (.var 3)) (.var 3)))) (by decide +kernel) : (sd * cu + -(cd * su * z)) * (sd * cu + -(cd * su * Ext.conj z)) = sd * cu * (sd * cu) + cd * su * (cd * su) + -(sd * cu * (cd * su) * (z + Ext.conj z)) + (z * Ext.conj z + -1) * (cd * cd * su * su)) hz')

/-! ## The mixing (28:C8, 28:C10, 28:X8, 28:X10, 28:P8) -/

theorem transpose_entry (a00 a01 a02 a10 a11 a12 a20 a21 a22 b00 b01 b02 b10 b11 b12 b20 b21 b22 : Ext p ν) :
    transpose (mmul ⟨a00, a01, a02, a10, a11, a12, a20, a21, a22⟩ ⟨b00, b01, b02, b10, b11, b12, b20, b21, b22⟩) =
      mmul (transpose ⟨b00, b01, b02, b10, b11, b12, b20, b21, b22⟩) (transpose ⟨a00, a01, a02, a10, a11, a12, a20, a21, a22⟩) :=
  mext
    (xsound (xlook [a00, a01, a02, a10, a11, a12, a20, a21, a22, b00, b01, b02, b10, b11, b12, b20, b21, b22]) (.add (.add (.mul (.var 0) (.var 9)) (.mul (.var 1) (.var 12))) (.mul (.var 2) (.var 15))) (.add (.add (.mul (.var 9) (.var 0)) (.mul (.var 12) (.var 1))) (.mul (.var 15) (.var 2))) (by decide +kernel) : a00 * b00 + a01 * b10 + a02 * b20 = b00 * a00 + b10 * a01 + b20 * a02)
    (xsound (xlook [a00, a01, a02, a10, a11, a12, a20, a21, a22, b00, b01, b02, b10, b11, b12, b20, b21, b22]) (.add (.add (.mul (.var 3) (.var 9)) (.mul (.var 4) (.var 12))) (.mul (.var 5) (.var 15))) (.add (.add (.mul (.var 9) (.var 3)) (.mul (.var 12) (.var 4))) (.mul (.var 15) (.var 5))) (by decide +kernel) : a10 * b00 + a11 * b10 + a12 * b20 = b00 * a10 + b10 * a11 + b20 * a12)
    (xsound (xlook [a00, a01, a02, a10, a11, a12, a20, a21, a22, b00, b01, b02, b10, b11, b12, b20, b21, b22]) (.add (.add (.mul (.var 6) (.var 9)) (.mul (.var 7) (.var 12))) (.mul (.var 8) (.var 15))) (.add (.add (.mul (.var 9) (.var 6)) (.mul (.var 12) (.var 7))) (.mul (.var 15) (.var 8))) (by decide +kernel) : a20 * b00 + a21 * b10 + a22 * b20 = b00 * a20 + b10 * a21 + b20 * a22)
    (xsound (xlook [a00, a01, a02, a10, a11, a12, a20, a21, a22, b00, b01, b02, b10, b11, b12, b20, b21, b22]) (.add (.add (.mul (.var 0) (.var 10)) (.mul (.var 1) (.var 13))) (.mul (.var 2) (.var 16))) (.add (.add (.mul (.var 10) (.var 0)) (.mul (.var 13) (.var 1))) (.mul (.var 16) (.var 2))) (by decide +kernel) : a00 * b01 + a01 * b11 + a02 * b21 = b01 * a00 + b11 * a01 + b21 * a02)
    (xsound (xlook [a00, a01, a02, a10, a11, a12, a20, a21, a22, b00, b01, b02, b10, b11, b12, b20, b21, b22]) (.add (.add (.mul (.var 3) (.var 10)) (.mul (.var 4) (.var 13))) (.mul (.var 5) (.var 16))) (.add (.add (.mul (.var 10) (.var 3)) (.mul (.var 13) (.var 4))) (.mul (.var 16) (.var 5))) (by decide +kernel) : a10 * b01 + a11 * b11 + a12 * b21 = b01 * a10 + b11 * a11 + b21 * a12)
    (xsound (xlook [a00, a01, a02, a10, a11, a12, a20, a21, a22, b00, b01, b02, b10, b11, b12, b20, b21, b22]) (.add (.add (.mul (.var 6) (.var 10)) (.mul (.var 7) (.var 13))) (.mul (.var 8) (.var 16))) (.add (.add (.mul (.var 10) (.var 6)) (.mul (.var 13) (.var 7))) (.mul (.var 16) (.var 8))) (by decide +kernel) : a20 * b01 + a21 * b11 + a22 * b21 = b01 * a20 + b11 * a21 + b21 * a22)
    (xsound (xlook [a00, a01, a02, a10, a11, a12, a20, a21, a22, b00, b01, b02, b10, b11, b12, b20, b21, b22]) (.add (.add (.mul (.var 0) (.var 11)) (.mul (.var 1) (.var 14))) (.mul (.var 2) (.var 17))) (.add (.add (.mul (.var 11) (.var 0)) (.mul (.var 14) (.var 1))) (.mul (.var 17) (.var 2))) (by decide +kernel) : a00 * b02 + a01 * b12 + a02 * b22 = b02 * a00 + b12 * a01 + b22 * a02)
    (xsound (xlook [a00, a01, a02, a10, a11, a12, a20, a21, a22, b00, b01, b02, b10, b11, b12, b20, b21, b22]) (.add (.add (.mul (.var 3) (.var 11)) (.mul (.var 4) (.var 14))) (.mul (.var 5) (.var 17))) (.add (.add (.mul (.var 11) (.var 3)) (.mul (.var 14) (.var 4))) (.mul (.var 17) (.var 5))) (by decide +kernel) : a10 * b02 + a11 * b12 + a12 * b22 = b02 * a10 + b12 * a11 + b22 * a12)
    (xsound (xlook [a00, a01, a02, a10, a11, a12, a20, a21, a22, b00, b01, b02, b10, b11, b12, b20, b21, b22]) (.add (.add (.mul (.var 6) (.var 11)) (.mul (.var 7) (.var 14))) (.mul (.var 8) (.var 17))) (.add (.add (.mul (.var 11) (.var 6)) (.mul (.var 14) (.var 7))) (.mul (.var 17) (.var 8))) (by decide +kernel) : a20 * b02 + a21 * b12 + a22 * b22 = b02 * a20 + b12 * a21 + b22 * a22)

/-- 28:C8, 28:X8 — `(A B)ᵀ = Bᵀ Aᵀ`. -/
theorem transpose_mul (A B : M3 p ν) : transpose (mmul A B) = mmul (transpose B) (transpose A) := by
  cases A; cases B; exact transpose_entry _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _

theorem transpose_transpose (A : M3 p ν) : transpose (transpose A) = A := by cases A; rfl

theorem transpose_diag (x y z : Ext p ν) : transpose (diag x y z) = diag x y z := rfl

/-- 28:C8, 28:X8 — the lopsided split: `(L D Rᵀ)ᵀ = R D Lᵀ` for a diagonal `D`. A mass matrix `M_d = L D Rᵀ` whose large
off-diagonal entry sits in the right-handed rotation `R` (invisible to the quark mixing, which sees `L`) has the transpose
`M_e = M_dᵀ = R D Lᵀ`, where the same rotation is the left-handed one the lepton mixing sees. -/
theorem transpose_exchanges (L R : M3 p ν) (x y z : Ext p ν) :
    transpose (mmul (mmul L (diag x y z)) (transpose R)) = mmul (mmul R (diag x y z)) (transpose L) := by
  rw [transpose_mul, transpose_mul, transpose_transpose, transpose_diag, mmul_assoc]

/-- The matrix applied to a column vector `(x, y, z)`. -/
def mulvec (A : M3 p ν) (x y z : Ext p ν) : Ext p ν × Ext p ν × Ext p ν :=
  (A.a00 * x + A.a01 * y + A.a02 * z, A.a10 * x + A.a11 * y + A.a12 * z, A.a20 * x + A.a21 * y + A.a22 * z)

/-- 28:C10, 28:P8 — the protected column. The shift `P` fixes the democratic vector `(1, 1, 1)`, the trivial `C₃`
character; it fixes no multiple of `(2, −1, −1)` (the reducible TM1 column): `P (2, −1, −1) = (−1, −1, 2)`, and
`(−1, −1, 2) = l · (2, −1, −1)` forces `−1 = 1 + 1`, that is `3 = 0`. So a `C₃` residual selects TM2. -/
theorem protected_column :
    mulvec (shift : M3 p ν) 1 1 1 = (1, 1, 1) ∧
    mulvec (shift : M3 p ν) (1 + 1) (-1) (-1) = (-1, -1, 1 + 1) ∧
    ∀ l : Ext p ν, l * (1 + 1) = -1 → l * -1 = -1 → l * -1 = 1 + 1 → (1 + 1 + 1 : Ext p ν) = 0 := by
  refine ⟨Prod.ext ?_ (Prod.ext ?_ ?_), Prod.ext ?_ (Prod.ext ?_ ?_), ?_⟩
  · exact (xsound (xlook []) (.add (.add (.mul .zero .one) (.mul .one .one)) (.mul .zero .one)) .one (by decide +kernel) : (0 * 1 + 1 * 1 + 0 * 1 : Ext p ν) = 1)
  · exact (xsound (xlook []) (.add (.add (.mul .zero .one) (.mul .zero .one)) (.mul .one .one)) .one (by decide +kernel) : (0 * 1 + 0 * 1 + 1 * 1 : Ext p ν) = 1)
  · exact (xsound (xlook []) (.add (.add (.mul .one .one) (.mul .zero .one)) (.mul .zero .one)) .one (by decide +kernel) : (1 * 1 + 0 * 1 + 0 * 1 : Ext p ν) = 1)
  · exact (xsound (xlook []) (.add (.add (.mul .zero (.add .one .one)) (.mul .one (.neg .one))) (.mul .zero (.neg .one))) (.neg .one) (by decide +kernel) : (0 * (1 + 1) + 1 * (-1) + 0 * (-1) : Ext p ν) = -1)
  · exact (xsound (xlook []) (.add (.add (.mul .zero (.add .one .one)) (.mul .zero (.neg .one))) (.mul .one (.neg .one))) (.neg .one) (by decide +kernel) : (0 * (1 + 1) + 0 * (-1) + 1 * (-1) : Ext p ν) = -1)
  · exact (xsound (xlook []) (.add (.add (.mul .one (.add .one .one)) (.mul .zero (.neg .one))) (.mul .zero (.neg .one))) (.add .one .one) (by decide +kernel) : (1 * (1 + 1) + 0 * (-1) + 0 * (-1) : Ext p ν) = 1 + 1)
  · intro l _ h2 h3
    have e : (-1 : Ext p ν) = 1 + 1 := h2.symm.trans h3
    rw [← e, x_neg_add]

/-- 28:C10, 28:X10, 28:P8, 00:G17 — the magic matrix is trimaximal: `N(ω) = 1` and `N(ω²) = 1` for the cube root `ω = −h + h w` at
`ν = −3`, so every entry `ω^{jk}/√3` of the Fourier matrix has squared modulus `1/3`. -/
theorem trimaximal {h : Shell p} (hh : h + h = 1) (hν : ν + 1 + 1 + 1 = 0) :
    Ext.norm (omega3 ν h) = 1 ∧ Ext.norm (omega3 ν h * omega3 ν h) = 1 := by
  have hA : h + h + -1 = 0 := by rw [hh, add_neg]
  have e : Ext.norm (omega3 ν h) = 1 :=
    (red2 (RE.sound (look [ν, h]) (.add (.mul (.neg (.var 1)) (.neg (.var 1))) (.neg (.mul (.var 0) (.mul (.var 1) (.var 1))))) (.add (.add .one (.mul (.add (.add (.var 1) (.var 1)) (.neg .one)) (.add (.mul (.add .one .one) (.var 1)) .one))) (.mul (.add (.add (.add (.var 0) .one) .one) .one) (.neg (.mul (.var 1) (.var 1))))) (by decide +kernel) : (-h) * (-h) + -(ν * (h * h)) = 1 + (h + h + -1) * ((1 + 1) * h + 1) + (ν + 1 + 1 + 1) * (-(h * h))) hA hν)
  exact ⟨e, by rw [Ext.norm_mul, e, Shell.one_mul]⟩

/-- 28:C10, 28:X10, 28:P8, 00:G17 — the maximal Jarlskog invariant as a framed rational. The magic matrix's rephasing invariant
is `F₀₀ F₁₁ F̄₀₁ F̄₁₀ = ω/9`, so `J = Im(ω)/9` and `J² = (Im ω)²/81` with `(Im ω)² = −ν h²` (the `w`-part `h` of
`ω = −h + h w`, `w² = ν = −3`). Then `108 J² = 1` reads `4(−ν h²) = 3`, exact on every shell with `h + h = 1`,
`ν + 3 = 0`: the continuum `J = 1/(6√3)`, `J² = 1/108`. -/
theorem jarlskog_sq {h : Shell p} (hh : h + h = 1) (hν : ν + 1 + 1 + 1 = 0) :
    (1 + 1 + 1 + 1) * (-(ν * (h * h))) = 1 + 1 + 1 := by
  have hA : h + h + -1 = 0 := by rw [hh, add_neg]
  exact (red2 (RE.sound (look [ν, h]) (.mul (.add (.add (.add .one .one) .one) .one) (.neg (.mul (.var 0) (.mul (.var 1) (.var 1))))) (.add (.add (.add (.add .one .one) .one) (.mul (.add (.add (.var 1) (.var 1)) (.neg .one)) (.add (.neg (.mul (.add .one .one) (.mul (.var 0) (.var 1)))) (.neg (.var 0))))) (.mul (.add (.add (.add (.var 0) .one) .one) .one) (.neg .one))) (by decide +kernel) : (1 + 1 + 1 + 1) * (-(ν * (h * h))) = 1 + 1 + 1 + (h + h + -1) * (-((1 + 1) * (ν * h)) + -ν) + (ν + 1 + 1 + 1) * (-1)) hA hν)

/-- 28:C5, 00:G17 — the trace of the square of a unit: for `z z̄ = 1`, `z² + z̄² = (z + z̄)² − 2`; with `z = e^{iθ}` this is
`2cos 2θ = (2cos θ)² − 2`. The lock `δ_d = δ₀/2` of 28:C5 is this relation between the cube invariants `c = cos 3δ`
of the lepton and down sectors: `c_ℓ = 2 c_d² − 1`. -/
theorem trace_double (z : Ext p ν) (hz : z * Ext.conj z = 1) :
    z * z + Ext.conj z * Ext.conj z = (z + Ext.conj z) * (z + Ext.conj z) + -(1 + 1) := by
  have hz' : z * Ext.conj z + -1 = 0 := by rw [hz, x_add_neg]
  exact (xred1 (xsound (xlook [z, Ext.conj z]) (.add (.mul (.var 0) (.var 0)) (.mul (.var 1) (.var 1))) (.add (.add (.mul (.add (.var 0) (.var 1)) (.add (.var 0) (.var 1))) (.neg (.add .one .one))) (.mul (.add (.mul (.var 0) (.var 1)) (.neg .one)) (.neg (.add .one .one)))) (by decide +kernel) : z * z + Ext.conj z * Ext.conj z = (z + Ext.conj z) * (z + Ext.conj z) + -(1 + 1) + (z * Ext.conj z + -1) * (-(1 + 1))) hz')

/-- 28:C5, 00:G17 — the trace of the cube of a unit: for `z z̄ = 1`, `z³ + z̄³ = (z + z̄)³ − 3(z + z̄)`; with `z = e^{iθ}`,
`2cos 3θ = (2cos θ)³ − 3(2cos θ)`. The lock `δ_u = δ₀/3` of 28:C5 is `c_ℓ = 4 c_u³ − 3 c_u` between the lepton and up
cube invariants. -/
theorem trace_triple (z : Ext p ν) (hz : z * Ext.conj z = 1) :
    z * z * z + Ext.conj z * Ext.conj z * Ext.conj z = (z + Ext.conj z) * ((z + Ext.conj z) * (z + Ext.conj z)) + -((1 + 1 + 1) * (z + Ext.conj z)) := by
  have hz' : z * Ext.conj z + -1 = 0 := by rw [hz, x_add_neg]
  exact (xred1 (xsound (xlook [z, Ext.conj z]) (.add (.mul (.mul (.var 0) (.var 0)) (.var 0)) (.mul (.mul (.var 1) (.var 1)) (.var 1))) (.add (.add (.mul (.add (.var 0) (.var 1)) (.mul (.add (.var 0) (.var 1)) (.add (.var 0) (.var 1)))) (.neg (.mul (.add (.add .one .one) .one) (.add (.var 0) (.var 1))))) (.mul (.add (.mul (.var 0) (.var 1)) (.neg .one)) (.add (.neg (.mul (.add (.add .one .one) .one) (.var 0))) (.neg (.mul (.add (.add .one .one) .one) (.var 1)))))) (by decide +kernel) : z * z * z + Ext.conj z * Ext.conj z * Ext.conj z = (z + Ext.conj z) * ((z + Ext.conj z) * (z + Ext.conj z)) + -((1 + 1 + 1) * (z + Ext.conj z)) + (z * Ext.conj z + -1) * (-((1 + 1 + 1) * z) + -((1 + 1 + 1) * Ext.conj z))) hz')

/-! ## The seesaw of circulants (28:C11, 28:X11) -/

theorem mul_adj_entry (a00 a01 a02 a10 a11 a12 a20 a21 a22 : Ext p ν) :
    mmul ⟨a00, a01, a02, a10, a11, a12, a20, a21, a22⟩ (adj ⟨a00, a01, a02, a10, a11, a12, a20, a21, a22⟩) =
      scal (det ⟨a00, a01, a02, a10, a11, a12, a20, a21, a22⟩) :=
  mext
    (xsound (xlook [a00, a01, a02, a10, a11, a12, a20, a21, a22]) (.add (.add (.mul (.var 0) (.add (.mul (.var 4) (.var 8)) (.neg (.mul (.var 5) (.var 7))))) (.mul (.var 1) (.add (.mul (.var 5) (.var 6)) (.neg (.mul (.var 3) (.var 8)))))) (.mul (.var 2) (.add (.mul (.var 3) (.var 7)) (.neg (.mul (.var 4) (.var 6)))))) (.add (.add (.mul (.var 0) (.add (.mul (.var 4) (.var 8)) (.neg (.mul (.var 5) (.var 7))))) (.neg (.mul (.var 1) (.add (.mul (.var 3) (.var 8)) (.neg (.mul (.var 5) (.var 6))))))) (.mul (.var 2) (.add (.mul (.var 3) (.var 7)) (.neg (.mul (.var 4) (.var 6)))))) (by decide +kernel) : a00 * (a11 * a22 + -(a12 * a21)) + a01 * (a12 * a20 + -(a10 * a22)) + a02 * (a10 * a21 + -(a11 * a20)) = a00 * (a11 * a22 + -(a12 * a21)) + -(a01 * (a10 * a22 + -(a12 * a20))) + a02 * (a10 * a21 + -(a11 * a20)))
    (xsound (xlook [a00, a01, a02, a10, a11, a12, a20, a21, a22]) (.add (.add (.mul (.var 0) (.add (.mul (.var 2) (.var 7)) (.neg (.mul (.var 1) (.var 8))))) (.mul (.var 1) (.add (.mul (.var 0) (.var 8)) (.neg (.mul (.var 2) (.var 6)))))) (.mul (.var 2) (.add (.mul (.var 1) (.var 6)) (.neg (.mul (.var 0) (.var 7)))))) .zero (by decide +kernel) : a00 * (a02 * a21 + -(a01 * a22)) + a01 * (a00 * a22 + -(a02 * a20)) + a02 * (a01 * a20 + -(a00 * a21)) = 0)
    (xsound (xlook [a00, a01, a02, a10, a11, a12, a20, a21, a22]) (.add (.add (.mul (.var 0) (.add (.mul (.var 1) (.var 5)) (.neg (.mul (.var 2) (.var 4))))) (.mul (.var 1) (.add (.mul (.var 2) (.var 3)) (.neg (.mul (.var 0) (.var 5)))))) (.mul (.var 2) (.add (.mul (.var 0) (.var 4)) (.neg (.mul (.var 1) (.var 3)))))) .zero (by decide +kernel) : a00 * (a01 * a12 + -(a02 * a11)) + a01 * (a02 * a10 + -(a00 * a12)) + a02 * (a00 * a11 + -(a01 * a10)) = 0)
    (xsound (xlook [a00, a01, a02, a10, a11, a12, a20, a21, a22]) (.add (.add (.mul (.var 3) (.add (.mul (.var 4) (.var 8)) (.neg (.mul (.var 5) (.var 7))))) (.mul (.var 4) (.add (.mul (.var 5) (.var 6)) (.neg (.mul (.var 3) (.var 8)))))) (.mul (.var 5) (.add (.mul (.var 3) (.var 7)) (.neg (.mul (.var 4) (.var 6)))))) .zero (by decide +kernel) : a10 * (a11 * a22 + -(a12 * a21)) + a11 * (a12 * a20 + -(a10 * a22)) + a12 * (a10 * a21 + -(a11 * a20)) = 0)
    (xsound (xlook [a00, a01, a02, a10, a11, a12, a20, a21, a22]) (.add (.add (.mul (.var 3) (.add (.mul (.var 2) (.var 7)) (.neg (.mul (.var 1) (.var 8))))) (.mul (.var 4) (.add (.mul (.var 0) (.var 8)) (.neg (.mul (.var 2) (.var 6)))))) (.mul (.var 5) (.add (.mul (.var 1) (.var 6)) (.neg (.mul (.var 0) (.var 7)))))) (.add (.add (.mul (.var 0) (.add (.mul (.var 4) (.var 8)) (.neg (.mul (.var 5) (.var 7))))) (.neg (.mul (.var 1) (.add (.mul (.var 3) (.var 8)) (.neg (.mul (.var 5) (.var 6))))))) (.mul (.var 2) (.add (.mul (.var 3) (.var 7)) (.neg (.mul (.var 4) (.var 6)))))) (by decide +kernel) : a10 * (a02 * a21 + -(a01 * a22)) + a11 * (a00 * a22 + -(a02 * a20)) + a12 * (a01 * a20 + -(a00 * a21)) = a00 * (a11 * a22 + -(a12 * a21)) + -(a01 * (a10 * a22 + -(a12 * a20))) + a02 * (a10 * a21 + -(a11 * a20)))
    (xsound (xlook [a00, a01, a02, a10, a11, a12, a20, a21, a22]) (.add (.add (.mul (.var 3) (.add (.mul (.var 1) (.var 5)) (.neg (.mul (.var 2) (.var 4))))) (.mul (.var 4) (.add (.mul (.var 2) (.var 3)) (.neg (.mul (.var 0) (.var 5)))))) (.mul (.var 5) (.add (.mul (.var 0) (.var 4)) (.neg (.mul (.var 1) (.var 3)))))) .zero (by decide +kernel) : a10 * (a01 * a12 + -(a02 * a11)) + a11 * (a02 * a10 + -(a00 * a12)) + a12 * (a00 * a11 + -(a01 * a10)) = 0)
    (xsound (xlook [a00, a01, a02, a10, a11, a12, a20, a21, a22]) (.add (.add (.mul (.var 6) (.add (.mul (.var 4) (.var 8)) (.neg (.mul (.var 5) (.var 7))))) (.mul (.var 7) (.add (.mul (.var 5) (.var 6)) (.neg (.mul (.var 3) (.var 8)))))) (.mul (.var 8) (.add (.mul (.var 3) (.var 7)) (.neg (.mul (.var 4) (.var 6)))))) .zero (by decide +kernel) : a20 * (a11 * a22 + -(a12 * a21)) + a21 * (a12 * a20 + -(a10 * a22)) + a22 * (a10 * a21 + -(a11 * a20)) = 0)
    (xsound (xlook [a00, a01, a02, a10, a11, a12, a20, a21, a22]) (.add (.add (.mul (.var 6) (.add (.mul (.var 2) (.var 7)) (.neg (.mul (.var 1) (.var 8))))) (.mul (.var 7) (.add (.mul (.var 0) (.var 8)) (.neg (.mul (.var 2) (.var 6)))))) (.mul (.var 8) (.add (.mul (.var 1) (.var 6)) (.neg (.mul (.var 0) (.var 7)))))) .zero (by decide +kernel) : a20 * (a02 * a21 + -(a01 * a22)) + a21 * (a00 * a22 + -(a02 * a20)) + a22 * (a01 * a20 + -(a00 * a21)) = 0)
    (xsound (xlook [a00, a01, a02, a10, a11, a12, a20, a21, a22]) (.add (.add (.mul (.var 6) (.add (.mul (.var 1) (.var 5)) (.neg (.mul (.var 2) (.var 4))))) (.mul (.var 7) (.add (.mul (.var 2) (.var 3)) (.neg (.mul (.var 0) (.var 5)))))) (.mul (.var 8) (.add (.mul (.var 0) (.var 4)) (.neg (.mul (.var 1) (.var 3)))))) (.add (.add (.mul (.var 0) (.add (.mul (.var 4) (.var 8)) (.neg (.mul (.var 5) (.var 7))))) (.neg (.mul (.var 1) (.add (.mul (.var 3) (.var 8)) (.neg (.mul (.var 5) (.var 6))))))) (.mul (.var 2) (.add (.mul (.var 3) (.var 7)) (.neg (.mul (.var 4) (.var 6)))))) (by decide +kernel) : a20 * (a01 * a12 + -(a02 * a11)) + a21 * (a02 * a10 + -(a00 * a12)) + a22 * (a00 * a11 + -(a01 * a10)) = a00 * (a11 * a22 + -(a12 * a21)) + -(a01 * (a10 * a22 + -(a12 * a20))) + a02 * (a10 * a21 + -(a11 * a20)))

/-- `A · adj A = det A · 1`. -/
theorem mul_adj (A : M3 p ν) : mmul A (adj A) = scal (det A) := by
  cases A; exact mul_adj_entry _ _ _ _ _ _ _ _ _

theorem adj_smul_entry (c a00 a01 a02 a10 a11 a12 a20 a21 a22 : Ext p ν) :
    adj (smul c ⟨a00, a01, a02, a10, a11, a12, a20, a21, a22⟩) = smul (c * c) (adj ⟨a00, a01, a02, a10, a11, a12, a20, a21, a22⟩) :=
  mext
    (xsound (xlook [c, a00, a01, a02, a10, a11, a12, a20, a21, a22]) (.add (.mul (.mul (.var 0) (.var 5)) (.mul (.var 0) (.var 9))) (.neg (.mul (.mul (.var 0) (.var 6)) (.mul (.var 0) (.var 8))))) (.mul (.mul (.var 0) (.var 0)) (.add (.mul (.var 5) (.var 9)) (.neg (.mul (.var 6) (.var 8))))) (by decide +kernel) : c * a11 * (c * a22) + -(c * a12 * (c * a21)) = c * c * (a11 * a22 + -(a12 * a21)))
    (xsound (xlook [c, a00, a01, a02, a10, a11, a12, a20, a21, a22]) (.add (.mul (.mul (.var 0) (.var 3)) (.mul (.var 0) (.var 8))) (.neg (.mul (.mul (.var 0) (.var 2)) (.mul (.var 0) (.var 9))))) (.mul (.mul (.var 0) (.var 0)) (.add (.mul (.var 3) (.var 8)) (.neg (.mul (.var 2) (.var 9))))) (by decide +kernel) : c * a02 * (c * a21) + -(c * a01 * (c * a22)) = c * c * (a02 * a21 + -(a01 * a22)))
    (xsound (xlook [c, a00, a01, a02, a10, a11, a12, a20, a21, a22]) (.add (.mul (.mul (.var 0) (.var 2)) (.mul (.var 0) (.var 6))) (.neg (.mul (.mul (.var 0) (.var 3)) (.mul (.var 0) (.var 5))))) (.mul (.mul (.var 0) (.var 0)) (.add (.mul (.var 2) (.var 6)) (.neg (.mul (.var 3) (.var 5))))) (by decide +kernel) : c * a01 * (c * a12) + -(c * a02 * (c * a11)) = c * c * (a01 * a12 + -(a02 * a11)))
    (xsound (xlook [c, a00, a01, a02, a10, a11, a12, a20, a21, a22]) (.add (.mul (.mul (.var 0) (.var 6)) (.mul (.var 0) (.var 7))) (.neg (.mul (.mul (.var 0) (.var 4)) (.mul (.var 0) (.var 9))))) (.mul (.mul (.var 0) (.var 0)) (.add (.mul (.var 6) (.var 7)) (.neg (.mul (.var 4) (.var 9))))) (by decide +kernel) : c * a12 * (c * a20) + -(c * a10 * (c * a22)) = c * c * (a12 * a20 + -(a10 * a22)))
    (xsound (xlook [c, a00, a01, a02, a10, a11, a12, a20, a21, a22]) (.add (.mul (.mul (.var 0) (.var 1)) (.mul (.var 0) (.var 9))) (.neg (.mul (.mul (.var 0) (.var 3)) (.mul (.var 0) (.var 7))))) (.mul (.mul (.var 0) (.var 0)) (.add (.mul (.var 1) (.var 9)) (.neg (.mul (.var 3) (.var 7))))) (by decide +kernel) : c * a00 * (c * a22) + -(c * a02 * (c * a20)) = c * c * (a00 * a22 + -(a02 * a20)))
    (xsound (xlook [c, a00, a01, a02, a10, a11, a12, a20, a21, a22]) (.add (.mul (.mul (.var 0) (.var 3)) (.mul (.var 0) (.var 4))) (.neg (.mul (.mul (.var 0) (.var 1)) (.mul (.var 0) (.var 6))))) (.mul (.mul (.var 0) (.var 0)) (.add (.mul (.var 3) (.var 4)) (.neg (.mul (.var 1) (.var 6))))) (by decide +kernel) : c * a02 * (c * a10) + -(c * a00 * (c * a12)) = c * c * (a02 * a10 + -(a00 * a12)))
    (xsound (xlook [c, a00, a01, a02, a10, a11, a12, a20, a21, a22]) (.add (.mul (.mul (.var 0) (.var 4)) (.mul (.var 0) (.var 8))) (.neg (.mul (.mul (.var 0) (.var 5)) (.mul (.var 0) (.var 7))))) (.mul (.mul (.var 0) (.var 0)) (.add (.mul (.var 4) (.var 8)) (.neg (.mul (.var 5) (.var 7))))) (by decide +kernel) : c * a10 * (c * a21) + -(c * a11 * (c * a20)) = c * c * (a10 * a21 + -(a11 * a20)))
    (xsound (xlook [c, a00, a01, a02, a10, a11, a12, a20, a21, a22]) (.add (.mul (.mul (.var 0) (.var 2)) (.mul (.var 0) (.var 7))) (.neg (.mul (.mul (.var 0) (.var 1)) (.mul (.var 0) (.var 8))))) (.mul (.mul (.var 0) (.var 0)) (.add (.mul (.var 2) (.var 7)) (.neg (.mul (.var 1) (.var 8))))) (by decide +kernel) : c * a01 * (c * a20) + -(c * a00 * (c * a21)) = c * c * (a01 * a20 + -(a00 * a21)))
    (xsound (xlook [c, a00, a01, a02, a10, a11, a12, a20, a21, a22]) (.add (.mul (.mul (.var 0) (.var 1)) (.mul (.var 0) (.var 5))) (.neg (.mul (.mul (.var 0) (.var 2)) (.mul (.var 0) (.var 4))))) (.mul (.mul (.var 0) (.var 0)) (.add (.mul (.var 1) (.var 5)) (.neg (.mul (.var 2) (.var 4))))) (by decide +kernel) : c * a00 * (c * a11) + -(c * a01 * (c * a10)) = c * c * (a00 * a11 + -(a01 * a10)))

/-- `adj (c A) = c² adj A`. -/
theorem adj_smul (c : Ext p ν) (A : M3 p ν) : adj (smul c A) = smul (c * c) (adj A) := by
  cases A; exact adj_smul_entry _ _ _ _ _ _ _ _ _ _

theorem mul_smul_entry (d a00 a01 a02 a10 a11 a12 a20 a21 a22 b00 b01 b02 b10 b11 b12 b20 b21 b22 : Ext p ν) :
    mmul ⟨a00, a01, a02, a10, a11, a12, a20, a21, a22⟩ (smul d ⟨b00, b01, b02, b10, b11, b12, b20, b21, b22⟩) =
      smul d (mmul ⟨a00, a01, a02, a10, a11, a12, a20, a21, a22⟩ ⟨b00, b01, b02, b10, b11, b12, b20, b21, b22⟩) :=
  mext
    (xsound (xlook [d, a00, a01, a02, a10, a11, a12, a20, a21, a22, b00, b01, b02, b10, b11, b12, b20, b21, b22]) (.add (.add (.mul (.var 1) (.mul (.var 0) (.var 10))) (.mul (.var 2) (.mul (.var 0) (.var 13)))) (.mul (.var 3) (.mul (.var 0) (.var 16)))) (.mul (.var 0) (.add (.add (.mul (.var 1) (.var 10)) (.mul (.var 2) (.var 13))) (.mul (.var 3) (.var 16)))) (by decide +kernel) : a00 * (d * b00) + a01 * (d * b10) + a02 * (d * b20) = d * (a00 * b00 + a01 * b10 + a02 * b20))
    (xsound (xlook [d, a00, a01, a02, a10, a11, a12, a20, a21, a22, b00, b01, b02, b10, b11, b12, b20, b21, b22]) (.add (.add (.mul (.var 1) (.mul (.var 0) (.var 11))) (.mul (.var 2) (.mul (.var 0) (.var 14)))) (.mul (.var 3) (.mul (.var 0) (.var 17)))) (.mul (.var 0) (.add (.add (.mul (.var 1) (.var 11)) (.mul (.var 2) (.var 14))) (.mul (.var 3) (.var 17)))) (by decide +kernel) : a00 * (d * b01) + a01 * (d * b11) + a02 * (d * b21) = d * (a00 * b01 + a01 * b11 + a02 * b21))
    (xsound (xlook [d, a00, a01, a02, a10, a11, a12, a20, a21, a22, b00, b01, b02, b10, b11, b12, b20, b21, b22]) (.add (.add (.mul (.var 1) (.mul (.var 0) (.var 12))) (.mul (.var 2) (.mul (.var 0) (.var 15)))) (.mul (.var 3) (.mul (.var 0) (.var 18)))) (.mul (.var 0) (.add (.add (.mul (.var 1) (.var 12)) (.mul (.var 2) (.var 15))) (.mul (.var 3) (.var 18)))) (by decide +kernel) : a00 * (d * b02) + a01 * (d * b12) + a02 * (d * b22) = d * (a00 * b02 + a01 * b12 + a02 * b22))
    (xsound (xlook [d, a00, a01, a02, a10, a11, a12, a20, a21, a22, b00, b01, b02, b10, b11, b12, b20, b21, b22]) (.add (.add (.mul (.var 4) (.mul (.var 0) (.var 10))) (.mul (.var 5) (.mul (.var 0) (.var 13)))) (.mul (.var 6) (.mul (.var 0) (.var 16)))) (.mul (.var 0) (.add (.add (.mul (.var 4) (.var 10)) (.mul (.var 5) (.var 13))) (.mul (.var 6) (.var 16)))) (by decide +kernel) : a10 * (d * b00) + a11 * (d * b10) + a12 * (d * b20) = d * (a10 * b00 + a11 * b10 + a12 * b20))
    (xsound (xlook [d, a00, a01, a02, a10, a11, a12, a20, a21, a22, b00, b01, b02, b10, b11, b12, b20, b21, b22]) (.add (.add (.mul (.var 4) (.mul (.var 0) (.var 11))) (.mul (.var 5) (.mul (.var 0) (.var 14)))) (.mul (.var 6) (.mul (.var 0) (.var 17)))) (.mul (.var 0) (.add (.add (.mul (.var 4) (.var 11)) (.mul (.var 5) (.var 14))) (.mul (.var 6) (.var 17)))) (by decide +kernel) : a10 * (d * b01) + a11 * (d * b11) + a12 * (d * b21) = d * (a10 * b01 + a11 * b11 + a12 * b21))
    (xsound (xlook [d, a00, a01, a02, a10, a11, a12, a20, a21, a22, b00, b01, b02, b10, b11, b12, b20, b21, b22]) (.add (.add (.mul (.var 4) (.mul (.var 0) (.var 12))) (.mul (.var 5) (.mul (.var 0) (.var 15)))) (.mul (.var 6) (.mul (.var 0) (.var 18)))) (.mul (.var 0) (.add (.add (.mul (.var 4) (.var 12)) (.mul (.var 5) (.var 15))) (.mul (.var 6) (.var 18)))) (by decide +kernel) : a10 * (d * b02) + a11 * (d * b12) + a12 * (d * b22) = d * (a10 * b02 + a11 * b12 + a12 * b22))
    (xsound (xlook [d, a00, a01, a02, a10, a11, a12, a20, a21, a22, b00, b01, b02, b10, b11, b12, b20, b21, b22]) (.add (.add (.mul (.var 7) (.mul (.var 0) (.var 10))) (.mul (.var 8) (.mul (.var 0) (.var 13)))) (.mul (.var 9) (.mul (.var 0) (.var 16)))) (.mul (.var 0) (.add (.add (.mul (.var 7) (.var 10)) (.mul (.var 8) (.var 13))) (.mul (.var 9) (.var 16)))) (by decide +kernel) : a20 * (d * b00) + a21 * (d * b10) + a22 * (d * b20) = d * (a20 * b00 + a21 * b10 + a22 * b20))
    (xsound (xlook [d, a00, a01, a02, a10, a11, a12, a20, a21, a22, b00, b01, b02, b10, b11, b12, b20, b21, b22]) (.add (.add (.mul (.var 7) (.mul (.var 0) (.var 11))) (.mul (.var 8) (.mul (.var 0) (.var 14)))) (.mul (.var 9) (.mul (.var 0) (.var 17)))) (.mul (.var 0) (.add (.add (.mul (.var 7) (.var 11)) (.mul (.var 8) (.var 14))) (.mul (.var 9) (.var 17)))) (by decide +kernel) : a20 * (d * b01) + a21 * (d * b11) + a22 * (d * b21) = d * (a20 * b01 + a21 * b11 + a22 * b21))
    (xsound (xlook [d, a00, a01, a02, a10, a11, a12, a20, a21, a22, b00, b01, b02, b10, b11, b12, b20, b21, b22]) (.add (.add (.mul (.var 7) (.mul (.var 0) (.var 12))) (.mul (.var 8) (.mul (.var 0) (.var 15)))) (.mul (.var 9) (.mul (.var 0) (.var 18)))) (.mul (.var 0) (.add (.add (.mul (.var 7) (.var 12)) (.mul (.var 8) (.var 15))) (.mul (.var 9) (.var 18)))) (by decide +kernel) : a20 * (d * b02) + a21 * (d * b12) + a22 * (d * b22) = d * (a20 * b02 + a21 * b12 + a22 * b22))

/-- `A (d B) = d (A B)`. -/
theorem mul_smul (d : Ext p ν) (A B : M3 p ν) : mmul A (smul d B) = smul d (mmul A B) := by
  cases A; cases B; exact mul_smul_entry _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _

/-- `c (d 1) = (c d) 1`. -/
theorem smul_scal (c d : Ext p ν) : smul c (scal d) = scal (c * d) :=
  mext
    (xsound (xlook [c, d]) (.mul (.var 0) (.var 1)) (.mul (.var 0) (.var 1)) (by decide +kernel) : c * d = c * d)
    (xsound (xlook [c, d]) (.mul (.var 0) .zero) .zero (by decide +kernel) : c * 0 = 0)
    (xsound (xlook [c, d]) (.mul (.var 0) .zero) .zero (by decide +kernel) : c * 0 = 0)
    (xsound (xlook [c, d]) (.mul (.var 0) .zero) .zero (by decide +kernel) : c * 0 = 0)
    (xsound (xlook [c, d]) (.mul (.var 0) (.var 1)) (.mul (.var 0) (.var 1)) (by decide +kernel) : c * d = c * d)
    (xsound (xlook [c, d]) (.mul (.var 0) .zero) .zero (by decide +kernel) : c * 0 = 0)
    (xsound (xlook [c, d]) (.mul (.var 0) .zero) .zero (by decide +kernel) : c * 0 = 0)
    (xsound (xlook [c, d]) (.mul (.var 0) .zero) .zero (by decide +kernel) : c * 0 = 0)
    (xsound (xlook [c, d]) (.mul (.var 0) (.var 1)) (.mul (.var 0) (.var 1)) (by decide +kernel) : c * d = c * d)

/-- 28:C11, 28:X11, 00:G15 — the seesaw of circulants is circulant: `m_D · adj(M_R) · m_Dᵀ` is a circulant whenever `m_D` and `M_R` are
(the inverse `M_R⁻¹ = adj(M_R)/det M_R` differs from the adjugate by the scalar), so the light neutrinos are Koide-form. -/
theorem seesaw_circulant (a b c a' b' c' : Ext p ν) :
    ∃ x y z, mmul (mmul (circ a b c) (adj (circ a' b' c'))) (transpose (circ a b c)) = circ x y z := by
  rw [circ_adj, circ_mul, circ_transpose, circ_mul]; exact ⟨_, _, _, rfl⟩

/-- 28:C11, 28:X11, 28:P5, 00:G15 — the transpose fixed point. With `M_R = c · m_D` (the `126` alignment, 28:Y1) the seesaw
collapses: `m_D · adj(c m_D) · m_Dᵀ = c² det(m_D) · m_Dᵀ`, a scalar multiple of the transpose, so the light neutrinos
carry the Dirac eigenvalues (`circ_transpose`, `circ_eigen`: the transpose circulant has the eigenvalues `λ_{-k}`), the
amplitude `r_ν = r_D` and the Koide value `Q_ν = Q_D = 2/3` of the colourless Dirac mass. -/
theorem transpose_fixed_point (c : Ext p ν) (M : M3 p ν) :
    mmul (mmul M (adj (smul c M))) (transpose M) = smul (c * c * det M) (transpose M) := by
  rw [adj_smul, mul_smul, mul_adj, smul_scal, scal_mul]

end FRC.Flavour
