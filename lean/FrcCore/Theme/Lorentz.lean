import FrcCore.Theme.Spin

/-!
# FrcCore.Theme.Lorentz — the register square and the finite Lorentz group (7-spacetime)

The projective theme's third core file (31 October 2026; the verification package of 7-spacetime). On a shell
`p = 4κ + 1` with its quadratic extension `K = 𝔽_p(η)`, `η² = ν` the drive's generator, a nonsquare, with
`conj η = −η`:

* **The register square** (7:C1). The Hermitian matrices `X(x) = [[x₀ + x₃, x₁ + ηx₂], [x₁ − ηx₂, x₀ − x₃]]` have
  `det X(x) = x₀² − x₁² − x₃² + ν x₂²` (`register_det`) and `X(x)† = X(x)` (`register_hermitian`); the time vector is
  `X(0, 0, 1, 0) = ηJ` (`time_vector`), the Hermitian form of `Theme/Spin.lean`.
* **The congruence** (7:C2). `X ↦ A X A†` carries Hermitian matrices to Hermitian matrices (`congruence_hermitian`)
  and multiplies the determinant by `N(det A)` (`congruence_det`, from `det_mul` and `det_dagger`); a matrix of
  determinant one fixing the four basis vectors is `±I` (`kernel_pm`): the kernel of the finite Lorentz group.
* **The cone** (7:C3, C4). `v v†` is the Hermitian matrix of explicit coordinates with `det = 0` (`cone_point`); a
  direction `[z : 1]` with `z ∉ 𝔽_p` carries a time component (`cone_time`).
* **The two classes** (7:C5). `det(u u† + v v†) = N(u₁v₂ − u₂v₁)` (`rank_two_det`): two null points span no
  isotropic plane unless proportional over `K`, since the norm is anisotropic (`register_elliptic`); the frame quadric
  `(M₂(𝔽_p), det)` carries the isotropic plane of the first row (`frame_hyperbolic`).
* **No inertia** (7:C6). With `a² + b² = ν` the explicit linear map multiplies the form by `ν` (`similitude`), and
  such `a, b` exist on every shell with a quarter-turn (`two_squares`).
* **The fibration** (7:C7, C8). The stabiliser of the ray `η` in `SL₂(𝔽_p)` is the norm-one torus `[[a, νc], [c, a]]`
  (`ray_stabiliser`); `−I` lies in the Borel lift and in the torus lift (`minus_one_in_both`); the axis of a ray `z`,
  the binary form with roots `z, z̄`, has discriminant `ν (2 Im z)²` (`axis_discriminant`).
* **Time** (7:D3, D4). The one-chronon move `diag(g, 1)` scales the time vector by `g` (`drive_time`), its unimodular
  lift `diag(η, η⁻¹)` has determinant one and negates it (`lift_det`, `lift_time`), the even transport fixes it and
  dilates the origin and the horizon (`even_transport`); `−I` acts trivially (`neg_one_trivial`) and `P diag(λ, λ̄) =
  (mult λ) P` conjugates `N¹` to the torus lift (`torus_conjugate`).
* **The horizon** (7:D6). `η` has order two modulo `𝔽_p^×` (`horizon_order_two`), the half step `(p + 1)/2 = 2κ + 1`
  is odd (`half_step_odd`), and no square of `K` lies on the line `𝔽_p^× η`: the unimodular torus, the even steps,
  never reaches the horizon (`even_never_horizon`).
* **The arrow** (7:F3, F4). No matrix of determinant one realises the time reversal `x₂ ↦ −x₂` (the Frobenius), the
  reflection `x₁ ↦ −x₁` or the total inversion `X ↦ −X` on the four basis vectors (`no_time_reversal`,
  `no_reflection`, `no_inversion`). The drift: on a hosted pair the joint period is `lcm(4κ, 4S)` (`joint_period`) and the
  chart count `4κn mod 4S` of the origin is injective for `n < S / gcd(κ, S)` (`drift_injective`, `drift_injective_gcd`);
  on the physical pair `p² < Ω − 1`, so the drift is one-directional (`drift_one_directional`, `nesting_depth`).

The identities are decided by the ring normaliser of `Ring.lean` lifted to the extension and to its two-by-two matrices
(`Theme/Spin.lean`'s `XR`, `MX`). No axioms.
-/

namespace FRC.Lorentz

open FRC.Shell FRC.Shell.Frame FRC.Extension FRC.Spin

variable {p : Nat} [Pos p] {ν : Shell p}

/-! ## The register square -/

/-- The register matrix `X(x) = [[x₀ + x₃, x₁ + ηx₂], [x₁ − ηx₂, x₀ − x₃]]`. -/
def X (x0 x1 x2 x3 : Shell p) : M2x p ν := ⟨⟨x0 + x3, 0⟩, ⟨x1, x2⟩, ⟨x1, -x2⟩, ⟨x0 + -x3, 0⟩⟩

/-- The determinant form `Q(x) = x₀² − x₁² − x₃² + ν x₂²`. -/
def Q (ν : Shell p) (x0 x1 x2 x3 : Shell p) : Shell p := x0 * x0 + -(x1 * x1) + -(x3 * x3) + ν * (x2 * x2)

/-- The congruence `A X A†`. -/
def cong (A M : M2x p ν) : M2x p ν := (A.mul M).mul A.dagger

/-- A diagonal matrix over the extension. -/
def diagx (a d : Ext p ν) : M2x p ν := ⟨a, 0, 0, d⟩

/-- The identity over the extension. -/
def Ix : M2x p ν := ⟨1, 0, 0, 1⟩

/-- A shell scalar as a symbolic element of the extension. -/
def sv (i : Nat) : XR := ⟨.var i, .zero⟩

/-- The symbolic register matrix of four ring expressions. -/
def MXX' (a b c d : RE) : MX := ⟨⟨.add a d, .zero⟩, ⟨b, c⟩, ⟨b, .neg c⟩, ⟨.add a (.neg d), .zero⟩⟩

/-- The symbolic register matrix on the variables `i, i + 1, i + 2, i + 3`. -/
def MXX (i : Nat) : MX := MXX' (.var i) (.var (i + 1)) (.var (i + 2)) (.var (i + 3))

/-- The symbolic time vector `X(0, 0, 1, 0)`. -/
def MXT : MX := MXX' .zero .zero .one .zero

/-- The symbolic form `Q` on the variables `i, …, i + 3`, `ν` the variable `0`. -/
def QX (i : Nat) : RE :=
  .add (.add (.add (.mul (.var i) (.var i)) (.neg (.mul (.var (i + 1)) (.var (i + 1))))) (.neg (.mul (.var (i + 3)) (.var (i + 3)))))
    (.mul (.var 0) (.mul (.var (i + 2)) (.var (i + 2))))

/-- The symbolic congruence. -/
def MXcong (A M : MX) : MX := MX.mul (MX.mul A M) (MX.tr (MX.conj A))

/-- The environment of a register vector after `ν`. -/
def envX (ν x0 x1 x2 x3 : Shell p) : Nat → Shell p := look [ν, x0, x1, x2, x3]

/-- The environment of a matrix `A` (variables `1 … 8`) and a register vector (`9 … 12`). -/
def envAX (A : M2x p ν) (x0 x1 x2 x3 : Shell p) : Nat → Shell p :=
  look [ν, A.a.re, A.a.im, A.b.re, A.b.im, A.c.re, A.c.im, A.d.re, A.d.im, x0, x1, x2, x3]

/-- The environment of two matrices (`1 … 8`, `9 … 16`). -/
def envAB (A B : M2x p ν) : Nat → Shell p :=
  look [ν, A.a.re, A.a.im, A.b.re, A.b.im, A.c.re, A.c.im, A.d.re, A.d.im,
        B.a.re, B.a.im, B.b.re, B.b.im, B.c.re, B.c.im, B.d.re, B.d.im]

/-- 7:C1 — `det X(x) = x₀² − x₁² − x₃² + ν x₂²`. -/
theorem register_det (x0 x1 x2 x3 : Shell p) : (X (ν := ν) x0 x1 x2 x3).det = Ext.ofShell (Q ν x0 x1 x2 x3) :=
  XR.sound (envX ν x0 x1 x2 x3) (MX.det (MXX 1)) ⟨QX 1, .zero⟩ (by decide +kernel)

/-- 7:C1 — `X(x)` is Hermitian: `X(x)† = X(x)`. -/
theorem register_hermitian (x0 x1 x2 x3 : Shell p) : (X (ν := ν) x0 x1 x2 x3).dagger = X x0 x1 x2 x3 :=
  MX.sound (envX ν x0 x1 x2 x3) (MX.tr (MX.conj (MXX 1))) (MXX 1) (by decide +kernel)

/-- 7:C1, 7:D1 — the time vector `X(0, 0, 1, 0)` is the Hermitian form `ηJ` of 00:C27 (`Theme/Spin.lean`). -/
theorem time_vector : (X (ν := ν) 0 0 1 0) = M2x.wJ Ext.w :=
  MX.sound (look [ν]) MXT ⟨XR.zero, ⟨.zero, .one⟩, XR.neg ⟨.zero, .one⟩, XR.zero⟩ (by decide +kernel)

/-! ## The congruence -/

theorem det_mul (A B : M2x p ν) : (A.mul B).det = A.det * B.det :=
  XR.sound (envAB A B) (MX.det (MX.mul (MX.v 1) (MX.v 9))) (XR.mul (MX.det (MX.v 1)) (MX.det (MX.v 9))) (by decide +kernel)

theorem det_dagger (A : M2x p ν) : A.dagger.det = Ext.conj A.det :=
  XR.sound (envAB A A) (MX.det (MX.tr (MX.conj (MX.v 1)))) (XR.conj (MX.det (MX.v 1))) (by decide +kernel)

theorem dagger_mul (A B : M2x p ν) : (A.mul B).dagger = B.dagger.mul A.dagger :=
  MX.sound (envAB A B) (MX.tr (MX.conj (MX.mul (MX.v 1) (MX.v 9)))) (MX.mul (MX.tr (MX.conj (MX.v 9))) (MX.tr (MX.conj (MX.v 1)))) (by decide +kernel)

theorem dagger_dagger (A : M2x p ν) : A.dagger.dagger = A :=
  MX.sound (envAB A A) (MX.tr (MX.conj (MX.tr (MX.conj (MX.v 1))))) (MX.v 1) (by decide +kernel)

theorem mul_assocx (A B C : M2x p ν) : (A.mul B).mul C = A.mul (B.mul C) :=
  MX.sound (look [ν, A.a.re, A.a.im, A.b.re, A.b.im, A.c.re, A.c.im, A.d.re, A.d.im,
                  B.a.re, B.a.im, B.b.re, B.b.im, B.c.re, B.c.im, B.d.re, B.d.im,
                  C.a.re, C.a.im, C.b.re, C.b.im, C.c.re, C.c.im, C.d.re, C.d.im])
    (MX.mul (MX.mul (MX.v 1) (MX.v 9)) (MX.v 17)) (MX.mul (MX.v 1) (MX.mul (MX.v 9) (MX.v 17))) (by decide +kernel)

/-- 7:C2 — the congruence multiplies the determinant by the norm of `det A`: `det(A X A†) = det A · conj(det A) · det X`. -/
theorem congruence_det (A : M2x p ν) (x0 x1 x2 x3 : Shell p) :
    (cong A (X x0 x1 x2 x3)).det = A.det * Ext.conj A.det * Ext.ofShell (Q ν x0 x1 x2 x3) := by
  unfold cong
  rw [det_mul, det_mul, det_dagger, register_det, Ext.mul_assoc, Ext.mul_comm (Ext.ofShell _), ← Ext.mul_assoc]

/-- 7:C2 — the congruence of a Hermitian matrix is Hermitian. -/
theorem congruence_hermitian (A : M2x p ν) (x0 x1 x2 x3 : Shell p) :
    (cong A (X x0 x1 x2 x3)).dagger = cong A (X x0 x1 x2 x3) := by
  unfold cong
  rw [dagger_mul, dagger_mul, dagger_dagger, register_hermitian, mul_assocx]

/-- 7:F3, 7:C2 — a congruence of determinant one preserves the form: `det(A X A†) = det X` when `det A = 1`. -/
theorem congruence_preserves (A : M2x p ν) (hA : A.det = 1) (x0 x1 x2 x3 : Shell p) :
    (cong A (X x0 x1 x2 x3)).det = Ext.ofShell (Q ν x0 x1 x2 x3) := by
  rw [congruence_det, hA]
  have c1 : Ext.conj (1 : Ext p ν) = 1 := Ext.ext rfl Shell.neg_zero
  rw [c1, Ext.one_mul, Ext.one_mul]

/-! ## The cone -/

/-- 7:C3 — the Hermitian matrix of `v = (v₁, v₂)`: `v v† = X(x)` with `x₀ = h(N v₁ + N v₂)`, `x₃ = h(N v₁ − N v₂)` (`2h = 1`),
`(x₁, x₂) = v₁ conj v₂`, and `Q(x) = 0`: a null point of the register square. -/
theorem cone_point (h : Shell p) (h2 : (1 + 1) * h = 1) (v1 v2 : Ext p ν) :
    (⟨v1 * Ext.conj v1, v1 * Ext.conj v2, v2 * Ext.conj v1, v2 * Ext.conj v2⟩ : M2x p ν) =
      X (h * (Ext.norm v1 + Ext.norm v2)) (v1 * Ext.conj v2).re (v1 * Ext.conj v2).im (h * (Ext.norm v1 + -Ext.norm v2)) ∧
    Q ν (h * (Ext.norm v1 + Ext.norm v2)) (v1 * Ext.conj v2).re (v1 * Ext.conj v2).im (h * (Ext.norm v1 + -Ext.norm v2)) = 0 := by
  have e := look (p := p) [ν, v1.re, v1.im, v2.re, v2.im, h]
  -- the entries: `x₀ + x₃ = (2h) N v₁`, `x₀ − x₃ = (2h) N v₂`
  have ea : h * (Ext.norm v1 + Ext.norm v2) + h * (Ext.norm v1 + -Ext.norm v2) = (1 + 1) * h * Ext.norm v1 :=
    RE.sound (look [h, Ext.norm v1, Ext.norm v2]) (.add (.mul (.var 0) (.add (.var 1) (.var 2))) (.mul (.var 0) (.add (.var 1) (.neg (.var 2)))))
      (.mul (.mul (.add .one .one) (.var 0)) (.var 1)) (by decide +kernel)
  have ed : h * (Ext.norm v1 + Ext.norm v2) + -(h * (Ext.norm v1 + -Ext.norm v2)) = (1 + 1) * h * Ext.norm v2 :=
    RE.sound (look [h, Ext.norm v1, Ext.norm v2]) (.add (.mul (.var 0) (.add (.var 1) (.var 2))) (.neg (.mul (.var 0) (.add (.var 1) (.neg (.var 2))))))
      (.mul (.mul (.add .one .one) (.var 0)) (.var 2)) (by decide +kernel)
  rw [h2, Shell.one_mul] at ea ed
  have ec : v2 * Ext.conj v1 = ⟨(v1 * Ext.conj v2).re, -(v1 * Ext.conj v2).im⟩ :=
    XR.sound (look [ν, v1.re, v1.im, v2.re, v2.im]) (XR.mul (XR.v 3) (XR.conj (XR.v 1))) (XR.conj (XR.mul (XR.v 1) (XR.conj (XR.v 3)))) (by decide +kernel)
  -- `Q(x) = (x₀ + x₃)(x₀ − x₃) − N(v₁ conj v₂) = N v₁ N v₂ − N v₁ N v₂`
  have eq : Q ν (h * (Ext.norm v1 + Ext.norm v2)) (v1 * Ext.conj v2).re (v1 * Ext.conj v2).im (h * (Ext.norm v1 + -Ext.norm v2)) =
      (h * (Ext.norm v1 + Ext.norm v2) + h * (Ext.norm v1 + -Ext.norm v2)) * (h * (Ext.norm v1 + Ext.norm v2) + -(h * (Ext.norm v1 + -Ext.norm v2))) +
        -(Ext.norm (v1 * Ext.conj v2)) :=
    RE.sound (look [ν, h, Ext.norm v1, Ext.norm v2, (v1 * Ext.conj v2).re, (v1 * Ext.conj v2).im])
      (.add (.add (.add (.mul (.mul (.var 1) (.add (.var 2) (.var 3))) (.mul (.var 1) (.add (.var 2) (.var 3)))) (.neg (.mul (.var 4) (.var 4))))
        (.neg (.mul (.mul (.var 1) (.add (.var 2) (.neg (.var 3)))) (.mul (.var 1) (.add (.var 2) (.neg (.var 3)))))))
        (.mul (.var 0) (.mul (.var 5) (.var 5))))
      (.add (.mul (.add (.mul (.var 1) (.add (.var 2) (.var 3))) (.mul (.var 1) (.add (.var 2) (.neg (.var 3)))))
        (.add (.mul (.var 1) (.add (.var 2) (.var 3))) (.neg (.mul (.var 1) (.add (.var 2) (.neg (.var 3)))))))
        (.neg (.add (.mul (.var 4) (.var 4)) (.neg (.mul (.var 0) (.mul (.var 5) (.var 5))))))) (by decide +kernel)
  have nc : Ext.norm (Ext.conj v2) = Ext.norm v2 :=
    RE.sound (look [ν, v2.re, v2.im]) (.add (.mul (.var 1) (.var 1)) (.neg (.mul (.var 0) (.mul (.neg (.var 2)) (.neg (.var 2))))))
      (.add (.mul (.var 1) (.var 1)) (.neg (.mul (.var 0) (.mul (.var 2) (.var 2))))) (by decide +kernel)
  refine ⟨?_, ?_⟩
  · refine M2x.ext' ?_ rfl ec ?_
    · show v1 * Ext.conj v1 = ⟨h * (Ext.norm v1 + Ext.norm v2) + h * (Ext.norm v1 + -Ext.norm v2), 0⟩
      rw [ea]; exact Ext.mul_conj v1
    · show v2 * Ext.conj v2 = ⟨h * (Ext.norm v1 + Ext.norm v2) + -(h * (Ext.norm v1 + -Ext.norm v2)), 0⟩
      rw [ed]; exact Ext.mul_conj v2
  · rw [eq, ea, ed, Ext.norm_mul, nc]; exact Shell.add_neg _

/-- 7:C4 — a direction `[z : 1]` with `z ∉ 𝔽_p` carries a time component: the `x₂` coordinate of `v v†`, `v = (z, 1)`, is `Im z`. -/
theorem cone_time (z : Ext p ν) : (z * Ext.conj (1 : Ext p ν)).im = z.im := by
  show z.re * -(0 : Shell p) + z.im * 1 = z.im
  rw [Shell.neg_zero, Shell.mul_zero, Shell.zero_add, Shell.mul_one]

/-! ## The two classes (7:C5) -/

/-- 7:C5 — the determinant of a sum of two rank-one Hermitian matrices is the norm of the two-by-two determinant of the
vectors: `det(u u† + v v†) = N(u₁ v₂ − u₂ v₁)`. -/
theorem rank_two_det (u1 u2 v1 v2 : Ext p ν) :
    (⟨u1 * Ext.conj u1 + v1 * Ext.conj v1, u1 * Ext.conj u2 + v1 * Ext.conj v2,
      u2 * Ext.conj u1 + v2 * Ext.conj v1, u2 * Ext.conj u2 + v2 * Ext.conj v2⟩ : M2x p ν).det =
      Ext.ofShell (Ext.norm (u1 * v2 + -(u2 * v1))) :=
  XR.sound (look [ν, u1.re, u1.im, u2.re, u2.im, v1.re, v1.im, v2.re, v2.im])
    (MX.det ⟨XR.add (XR.mul (XR.v 1) (XR.conj (XR.v 1))) (XR.mul (XR.v 5) (XR.conj (XR.v 5))),
             XR.add (XR.mul (XR.v 1) (XR.conj (XR.v 3))) (XR.mul (XR.v 5) (XR.conj (XR.v 7))),
             XR.add (XR.mul (XR.v 3) (XR.conj (XR.v 1))) (XR.mul (XR.v 7) (XR.conj (XR.v 5))),
             XR.add (XR.mul (XR.v 3) (XR.conj (XR.v 3))) (XR.mul (XR.v 7) (XR.conj (XR.v 7)))⟩)
    (let d := XR.add (XR.mul (XR.v 1) (XR.v 7)) (XR.neg (XR.mul (XR.v 3) (XR.v 5)))
     ⟨.add (.mul d.re d.re) (.neg (.mul (.var 0) (.mul d.im d.im))), .zero⟩) (by decide +kernel)

/-- 7:B4, 7:X1, 7:C5 — **the register square is elliptic**: on a field shell with `ν` a nonsquare, two null points `u u†`, `v v†` whose
sum is null have proportional vectors, `u₁ v₂ = u₂ v₁`: the null cone contains no totally isotropic plane. -/
theorem register_elliptic (K : Fld p) (hν : ¬ ∃ y : Shell p, y * y = ν) (u1 u2 v1 v2 : Ext p ν)
    (h : (⟨u1 * Ext.conj u1 + v1 * Ext.conj v1, u1 * Ext.conj u2 + v1 * Ext.conj v2,
           u2 * Ext.conj u1 + v2 * Ext.conj v1, u2 * Ext.conj u2 + v2 * Ext.conj v2⟩ : M2x p ν).det = 0) :
    u1 * v2 = u2 * v1 := by
  rw [rank_two_det] at h
  have hn : Ext.norm (u1 * v2 + -(u2 * v1)) = 0 := Ext.re_congr h
  have hz : u1 * v2 + -(u2 * v1) = 0 :=
    match Shell.instDecidableEq (u1 * v2 + -(u2 * v1)).re 0, Shell.instDecidableEq (u1 * v2 + -(u2 * v1)).im 0 with
    | isTrue h1, isTrue h2 => Ext.ext h1 h2
    | isTrue _, isFalse h2 => absurd hn (K.norm_ne_zero hν (Or.inr h2))
    | isFalse h1, _ => absurd hn (K.norm_ne_zero hν (Or.inl h1))
  exact ext_eq_of_add_neg_eq_zero hz

/-- 7:B4, 7:X1, 7:C5 — **the frame quadric is hyperbolic**: the matrices `[[a, b], [0, 0]]` form a totally isotropic plane of `det` on `M₂(𝔽_p)`. -/
theorem frame_hyperbolic (a b : Shell p) : (M2.det (⟨a, b, 0, 0⟩ : M2 p)) = 0 := by
  show a * 0 + -(b * 0) = 0
  rw [Shell.mul_zero, Shell.mul_zero, Shell.neg_zero, Shell.add_zero]

/-! ## No inertia (7:C6) -/

/-- 7:A9, 7:X5, 7:C6 — with `a² + b² = ν`, the map `(x₀, x₁, x₂, x₃) ↦ (ν x₂, a x₁ − b x₃, x₀, b x₁ + a x₃)` multiplies the form by `ν`:
`⟨1, 1, 1, ν⟩ ≅ ⟨1, ν, ν, ν⟩`, a similitude of multiplier `ν` exchanging the two non-null classes. -/
theorem similitude (a b : Shell p) (hab : a * a + b * b = ν) (x0 x1 x2 x3 : Shell p) :
    Q ν (ν * x2) (a * x1 + -(b * x3)) x0 (b * x1 + a * x3) = ν * Q ν x0 x1 x2 x3 := by
  have e : Q ν (ν * x2) (a * x1 + -(b * x3)) x0 (b * x1 + a * x3) =
      ν * (ν * (x2 * x2)) + -((a * a + b * b) * (x1 * x1 + x3 * x3)) + ν * (x0 * x0) :=
    RE.sound (look [ν, x0, x1, x2, x3, a, b])
      (.add (.add (.add (.mul (.mul (.var 0) (.var 3)) (.mul (.var 0) (.var 3)))
          (.neg (.mul (.add (.mul (.var 5) (.var 2)) (.neg (.mul (.var 6) (.var 4)))) (.add (.mul (.var 5) (.var 2)) (.neg (.mul (.var 6) (.var 4)))))))
          (.neg (.mul (.add (.mul (.var 6) (.var 2)) (.mul (.var 5) (.var 4))) (.add (.mul (.var 6) (.var 2)) (.mul (.var 5) (.var 4))))))
        (.mul (.var 0) (.mul (.var 1) (.var 1))))
      (.add (.add (.mul (.var 0) (.mul (.var 0) (.mul (.var 3) (.var 3))))
          (.neg (.mul (.add (.mul (.var 5) (.var 5)) (.mul (.var 6) (.var 6))) (.add (.mul (.var 2) (.var 2)) (.mul (.var 4) (.var 4))))))
        (.mul (.var 0) (.mul (.var 1) (.var 1)))) (by decide +kernel)
  have e2 : ν * (ν * (x2 * x2)) + -(ν * (x1 * x1 + x3 * x3)) + ν * (x0 * x0) = ν * Q ν x0 x1 x2 x3 :=
    RE.sound (look [ν, x0, x1, x2, x3])
      (.add (.add (.mul (.var 0) (.mul (.var 0) (.mul (.var 3) (.var 3)))) (.neg (.mul (.var 0) (.add (.mul (.var 2) (.var 2)) (.mul (.var 4) (.var 4))))))
        (.mul (.var 0) (.mul (.var 1) (.var 1))))
      (.mul (.var 0) (QX 1)) (by decide +kernel)
  rw [e, hab, e2]

/-- 7:C6 — on a shell with a quarter-turn `i² = −1` and `2h = 1`, every `ν` is a sum of two squares:
`ν = ((ν + 1)h)² + (i(ν − 1)h)²`. -/
theorem two_squares (i h : Shell p) (hi : i * i = -1) (h2 : (1 + 1) * h = 1) :
    (ν + 1) * h * ((ν + 1) * h) + i * ((ν + -1) * h) * (i * ((ν + -1) * h)) = ν := by
  have e : (ν + 1) * h * ((ν + 1) * h) + i * ((ν + -1) * h) * (i * ((ν + -1) * h)) =
      h * h * ((ν + 1) * (ν + 1) + i * i * ((ν + -1) * (ν + -1))) :=
    RE.sound (look [ν, i, h])
      (.add (.mul (.mul (.add (.var 0) .one) (.var 2)) (.mul (.add (.var 0) .one) (.var 2)))
            (.mul (.mul (.var 1) (.mul (.add (.var 0) (.neg .one)) (.var 2))) (.mul (.var 1) (.mul (.add (.var 0) (.neg .one)) (.var 2)))))
      (.mul (.mul (.var 2) (.var 2)) (.add (.mul (.add (.var 0) .one) (.add (.var 0) .one)) (.mul (.mul (.var 1) (.var 1)) (.mul (.add (.var 0) (.neg .one)) (.add (.var 0) (.neg .one))))))
      (by decide +kernel)
  have e2 : h * h * ((ν + 1) * (ν + 1) + -1 * ((ν + -1) * (ν + -1))) = (1 + 1) * h * ((1 + 1) * h) * ν :=
    RE.sound (look [ν, h])
      (.mul (.mul (.var 1) (.var 1)) (.add (.mul (.add (.var 0) .one) (.add (.var 0) .one)) (.mul (.neg .one) (.mul (.add (.var 0) (.neg .one)) (.add (.var 0) (.neg .one))))))
      (.mul (.mul (.mul (.add .one .one) (.var 1)) (.mul (.add .one .one) (.var 1))) (.var 0)) (by decide +kernel)
  rw [e, hi, e2, h2, Shell.one_mul, Shell.one_mul]

/-! ## The fibration (7:C7, C8) -/

/-- 7:C7 — the stabiliser of the ray `η` in the frame moves: `[[a, b], [c, d]]` fixes `η` under `z ↦ (az + b)/(cz + d)`,
i.e. `aη + b = (cη + d)η`, exactly when `a = d` and `b = νc`: the norm-one torus `[[a, νc], [c, a]]` of A10. -/
theorem ray_stabiliser (a b c d : Shell p) :
    (Ext.ofShell a * Ext.w + Ext.ofShell b : Ext p ν) = (Ext.ofShell c * Ext.w + Ext.ofShell d) * Ext.w ↔ a = d ∧ b = ν * c := by
  have l : (Ext.ofShell a * Ext.w + Ext.ofShell b : Ext p ν) = ⟨b, a⟩ :=
    XR.sound (look [ν, a, b]) (XR.add (XR.mul (sv 1) ⟨.zero, .one⟩) (sv 2)) ⟨.var 2, .var 1⟩ (by decide +kernel)
  have r : ((Ext.ofShell c * Ext.w + Ext.ofShell d) * Ext.w : Ext p ν) = ⟨ν * c, d⟩ :=
    XR.sound (look [ν, c, d]) (XR.mul (XR.add (XR.mul (sv 1) ⟨.zero, .one⟩) (sv 2)) ⟨.zero, .one⟩) ⟨.mul (.var 0) (.var 1), .var 2⟩ (by decide +kernel)
  rw [l, r]
  constructor
  · intro h; exact ⟨Ext.im_congr h, Ext.re_congr h⟩
  · intro h; exact Ext.ext h.2 h.1

/-- 7:B1, 7:C7 — on the spin cover `−I` is both upper triangular of determinant one and a norm-one diagonal matrix
`diag(λ, λ̄)`: the Borel lift and the torus lift meet in `±I`, the obstruction to a subgroup section. -/
theorem minus_one_in_both :
    (-1 : Shell p) * -1 + -((0 : Shell p) * 0) = 1 ∧ Ext.norm (-1 : Ext p ν) = 1 ∧ Ext.conj (-1 : Ext p ν) = -1 := by
  refine ⟨?_, ?_, ?_⟩
  · rw [Shell.neg_mul_neg, Shell.one_mul, Shell.mul_zero, Shell.neg_zero, Shell.add_zero]
  · show (-1 : Shell p) * -1 + -(ν * (-0 * -0)) = 1
    rw [Shell.neg_mul_neg, Shell.one_mul, Shell.neg_zero, Shell.mul_zero, Shell.mul_zero, Shell.neg_zero, Shell.add_zero]
  · exact Ext.ext rfl (by show -(-(0 : Shell p)) = -0; rw [Shell.neg_neg, Shell.neg_zero])

/-- 7:X2, 7:C8 — the axis of a ray `z`: the binary form `(t − z)(t − z̄) = t² − tr(z) t + N(z)` has discriminant
`tr(z)² − 4 N(z) = ν (2 Im z)²`, a nonsquare times a square. -/
theorem axis_discriminant (z : Ext p ν) :
    Ext.trace z * Ext.trace z + -((1 + 1) * (1 + 1) * Ext.norm z) = ν * (((1 + 1) * z.im) * ((1 + 1) * z.im)) :=
  RE.sound (look [ν, z.re, z.im])
    (.add (.mul (.add (.var 1) (.var 1)) (.add (.var 1) (.var 1)))
          (.neg (.mul (.mul (.add .one .one) (.add .one .one)) (.add (.mul (.var 1) (.var 1)) (.neg (.mul (.var 0) (.mul (.var 2) (.var 2))))))))
    (.mul (.var 0) (.mul (.mul (.add .one .one) (.var 2)) (.mul (.add .one .one) (.var 2)))) (by decide +kernel)

/-! ## Time (7:D3, D4) -/

/-- 7:D1, 7:D3, 7:A16 — the one-chronon move `diag(g, 1)` carries the time vector `ηJ = X(0, 0, 1, 0)` to `g·ηJ = X(0, 0, g, 0)`:
its square class flips with the chronon parity, and it carries the ray `(z, 1)` to `(gz, 1)`. -/
theorem drive_time (g : Shell p) :
    cong (diagx (Ext.ofShell g) 1) (X (ν := ν) 0 0 1 0) = X 0 0 g 0 ∧
    ∀ z : Ext p ν, (diagx (Ext.ofShell g) 1).mul ⟨z, 0, 1, 0⟩ = ⟨Ext.ofShell g * z, 0, 1, 0⟩ :=
  ⟨MX.sound (look [ν, g]) (MXcong ⟨sv 1, XR.zero, XR.zero, XR.one⟩ MXT) (MXX' .zero .zero (.var 1) .zero) (by decide +kernel),
   fun z => MX.sound (look [ν, g, z.re, z.im]) (MX.mul ⟨sv 1, XR.zero, XR.zero, XR.one⟩ ⟨XR.v 2, XR.zero, XR.one, XR.zero⟩)
     ⟨XR.mul (sv 1) (XR.v 2), XR.zero, XR.one, XR.zero⟩ (by decide +kernel)⟩

/-- 7:D3 — the unimodular lift `D = diag(η, uη)`, `νu = 1` (so `uη = η⁻¹`), has determinant one. -/
theorem lift_det (u : Shell p) (hu : ν * u = 1) : (diagx Ext.w (Ext.ofShell u * Ext.w) : M2x p ν).det = 1 := by
  have e : (diagx Ext.w (Ext.ofShell u * Ext.w) : M2x p ν).det = Ext.ofShell (ν * u) :=
    XR.sound (look [ν, u]) (MX.det ⟨⟨.zero, .one⟩, XR.zero, XR.zero, XR.mul (sv 1) ⟨.zero, .one⟩⟩) ⟨.mul (.var 0) (.var 1), .zero⟩ (by decide +kernel)
  rw [e, hu]; rfl

/-- 7:D3 — the lift negates the time vector: `D (ηJ) D† = −ηJ`, i.e. `X(0, 0, 1, 0) ↦ X(0, 0, −1, 0)`. -/
theorem lift_time (u : Shell p) (hu : ν * u = 1) :
    cong (diagx Ext.w (Ext.ofShell u * Ext.w)) (X (ν := ν) 0 0 1 0) = X 0 0 (-1) 0 := by
  have e : cong (diagx Ext.w (Ext.ofShell u * Ext.w)) (X (ν := ν) 0 0 1 0) = X 0 0 (-(ν * u)) 0 :=
    MX.sound (look [ν, u]) (MXcong ⟨⟨.zero, .one⟩, XR.zero, XR.zero, XR.mul (sv 1) ⟨.zero, .one⟩⟩ MXT)
      (MXX' .zero .zero (.neg (.mul (.var 0) (.var 1))) .zero) (by decide +kernel)
  rw [e, hu]

/-- 7:D3 — the even transport `diag(g, u)`, `gu = 1`, fixes the time vector and `σ_x` and dilates `E₂₂` by `u²` and `E₁₁` by `g²`. -/
theorem even_transport (g u : Shell p) (hu : g * u = 1) :
    cong (diagx (Ext.ofShell g) (Ext.ofShell u)) (X (ν := ν) 0 0 1 0) = X 0 0 1 0 ∧
    cong (diagx (Ext.ofShell g) (Ext.ofShell u)) (X (ν := ν) 0 1 0 0) = X 0 1 0 0 ∧
    cong (diagx (Ext.ofShell g) (Ext.ofShell u)) (⟨0, 0, 0, 1⟩ : M2x p ν) = ⟨0, 0, 0, Ext.ofShell (u * u)⟩ ∧
    cong (diagx (Ext.ofShell g) (Ext.ofShell u)) (⟨1, 0, 0, 0⟩ : M2x p ν) = ⟨Ext.ofShell (g * g), 0, 0, 0⟩ := by
  have e1 : cong (diagx (Ext.ofShell g) (Ext.ofShell u)) (X (ν := ν) 0 0 1 0) = X 0 0 (g * u) 0 :=
    MX.sound (look [ν, g, u]) (MXcong ⟨sv 1, XR.zero, XR.zero, sv 2⟩ MXT) (MXX' .zero .zero (.mul (.var 1) (.var 2)) .zero) (by decide +kernel)
  have e2 : cong (diagx (Ext.ofShell g) (Ext.ofShell u)) (X (ν := ν) 0 1 0 0) = X 0 (g * u) 0 0 :=
    MX.sound (look [ν, g, u]) (MXcong ⟨sv 1, XR.zero, XR.zero, sv 2⟩ (MXX' .zero .one .zero .zero)) (MXX' .zero (.mul (.var 1) (.var 2)) .zero .zero) (by decide +kernel)
  refine ⟨by rw [e1, hu], by rw [e2, hu], ?_, ?_⟩
  · exact MX.sound (look [ν, g, u]) (MXcong ⟨sv 1, XR.zero, XR.zero, sv 2⟩ ⟨XR.zero, XR.zero, XR.zero, XR.one⟩)
      ⟨XR.zero, XR.zero, XR.zero, ⟨.mul (.var 2) (.var 2), .zero⟩⟩ (by decide +kernel)
  · exact MX.sound (look [ν, g, u]) (MXcong ⟨sv 1, XR.zero, XR.zero, sv 2⟩ ⟨XR.one, XR.zero, XR.zero, XR.zero⟩)
      ⟨⟨.mul (.var 1) (.var 1), .zero⟩, XR.zero, XR.zero, XR.zero⟩ (by decide +kernel)

/-- 7:X4, 7:D4 — `−I` acts trivially on the register square: the spinor's two circuits are one on the square. -/
theorem neg_one_trivial (x0 x1 x2 x3 : Shell p) : cong (diagx (-1) (-1)) (X (ν := ν) x0 x1 x2 x3) = X x0 x1 x2 x3 :=
  MX.sound (envX ν x0 x1 x2 x3) (MXcong ⟨XR.neg XR.one, XR.zero, XR.zero, XR.neg XR.one⟩ (MXX 1)) (MXX 1) (by decide +kernel)

/-- 7:D4 — `P diag(λ, λ̄) = (mult λ) P` for `P = [[η, −η], [1, 1]]` and `mult λ = [[x, νy], [y, x]]`, `λ = x + yη`: the
norm-one diagonal group `N¹` and the torus lift are conjugate in `SL₂(K)` through `P`. -/
theorem torus_conjugate (l : Ext p ν) :
    (⟨Ext.w, -Ext.w, 1, 1⟩ : M2x p ν).mul (diagx l (Ext.conj l)) =
      (⟨Ext.ofShell l.re, Ext.ofShell (ν * l.im), Ext.ofShell l.im, Ext.ofShell l.re⟩ : M2x p ν).mul ⟨Ext.w, -Ext.w, 1, 1⟩ :=
  MX.sound (look [ν, l.re, l.im])
    (MX.mul ⟨⟨.zero, .one⟩, ⟨.neg .zero, .neg .one⟩, XR.one, XR.one⟩ ⟨XR.v 1, XR.zero, XR.zero, XR.conj (XR.v 1)⟩)
    (MX.mul ⟨sv 1, ⟨.mul (.var 0) (.var 2), .zero⟩, sv 2, sv 1⟩ ⟨⟨.zero, .one⟩, ⟨.neg .zero, .neg .one⟩, XR.one, XR.one⟩) (by decide +kernel)

/-! ## The kernel of the congruence (7:C2) and the three exclusions of the arrow (7:F3) -/

/-- The negative of a matrix over the extension. -/
def negx (M : M2x p ν) : M2x p ν := ⟨-M.a, -M.b, -M.c, -M.d⟩
/-- `σ_x = [[0, 1], [1, 0]] = X(0, 1, 0, 0)` and `σ_z = diag(1, −1) = X(0, 0, 0, 1)`. -/
def Sx : M2x p ν := ⟨0, 1, 1, 0⟩
def Dx : M2x p ν := ⟨1, 0, 0, -1⟩

theorem X_I : (X (ν := ν) 1 0 0 0) = Ix := MX.sound (look [ν]) (MXX' .one .zero .zero .zero) ⟨XR.one, XR.zero, XR.zero, XR.one⟩ (by decide +kernel)
theorem X_S : (X (ν := ν) 0 1 0 0) = Sx := MX.sound (look [ν]) (MXX' .zero .one .zero .zero) ⟨XR.zero, XR.one, XR.one, XR.zero⟩ (by decide +kernel)
theorem X_D : (X (ν := ν) 0 0 0 1) = Dx := MX.sound (look [ν]) (MXX' .zero .zero .zero .one) ⟨XR.one, XR.zero, XR.zero, XR.neg XR.one⟩ (by decide +kernel)
theorem X_negI : (X (ν := ν) (-1) 0 0 0) = negx Ix :=
  MX.sound (look [ν]) (MXX' (.neg .one) .zero .zero .zero) ⟨XR.neg XR.one, XR.neg XR.zero, XR.neg XR.zero, XR.neg XR.one⟩ (by decide +kernel)
theorem X_negS : (X (ν := ν) 0 (-1) 0 0) = negx Sx :=
  MX.sound (look [ν]) (MXX' .zero (.neg .one) .zero .zero) ⟨XR.neg XR.zero, XR.neg XR.one, XR.neg XR.one, XR.neg XR.zero⟩ (by decide +kernel)
theorem X_negD : (X (ν := ν) 0 0 0 (-1)) = negx Dx :=
  MX.sound (look [ν]) (MXX' .zero .zero .zero (.neg .one)) ⟨XR.neg XR.one, XR.neg XR.zero, XR.neg XR.zero, XR.neg (XR.neg XR.one)⟩ (by decide +kernel)
theorem X_negT : (X (ν := ν) 0 0 (-1) 0) = negx (X 0 0 1 0) :=
  MX.sound (look [ν]) (MXX' .zero .zero (.neg .one) .zero)
    ⟨XR.neg ⟨.add .zero .zero, .zero⟩, XR.neg ⟨.zero, .one⟩, XR.neg ⟨.zero, .neg .one⟩, XR.neg ⟨.add .zero (.neg .zero), .zero⟩⟩ (by decide +kernel)

theorem mul_Ix (A : M2x p ν) : A.mul Ix = A := MX.sound (envAB A A) (MX.mul (MX.v 1) ⟨XR.one, XR.zero, XR.zero, XR.one⟩) (MX.v 1) (by decide +kernel)
theorem Ix_mul (A : M2x p ν) : Ix.mul A = A := MX.sound (envAB A A) (MX.mul ⟨XR.one, XR.zero, XR.zero, XR.one⟩ (MX.v 1)) (MX.v 1) (by decide +kernel)
theorem adj_mulx (A : M2x p ν) : A.adj.mul A = diagx A.det A.det :=
  MX.sound (envAB A A) (MX.mul ⟨(MX.v 1).d, XR.neg (MX.v 1).b, XR.neg (MX.v 1).c, (MX.v 1).a⟩ (MX.v 1))
    ⟨MX.det (MX.v 1), XR.zero, XR.zero, MX.det (MX.v 1)⟩ (by decide +kernel)
theorem mul_negx (A B : M2x p ν) : A.mul (negx B) = negx (A.mul B) :=
  MX.sound (envAB A B) (MX.mul (MX.v 1) ⟨XR.neg (MX.v 9).a, XR.neg (MX.v 9).b, XR.neg (MX.v 9).c, XR.neg (MX.v 9).d⟩)
    (let P := MX.mul (MX.v 1) (MX.v 9); ⟨XR.neg P.a, XR.neg P.b, XR.neg P.c, XR.neg P.d⟩) (by decide +kernel)
theorem negx_inj {A B : M2x p ν} (h : negx A = negx B) : A = B := by
  have n : ∀ x y : Ext p ν, -x = -y → x = y := fun x y e =>
    Ext.ext (by have h : -x.re = -y.re := Ext.re_congr e; rw [← Shell.neg_neg x.re, h]; exact Shell.neg_neg y.re)
            (by have h : -x.im = -y.im := Ext.im_congr e; rw [← Shell.neg_neg x.im, h]; exact Shell.neg_neg y.im)
  exact M2x.ext' (n _ _ (M2x.ext'_a h)) (n _ _ (M2x.ext'_b h)) (n _ _ (M2x.ext'_c h)) (n _ _ (M2x.ext'_d h))

theorem diagx_one : (diagx (1 : Ext p ν) 1) = Ix := rfl

/-- A right inverse of a matrix of determinant one is its adjugate. -/
theorem right_inverse (A N : M2x p ν) (hdet : A.det = 1) (h : A.mul N = Ix) : N = A.adj := by
  have e : A.adj.mul (A.mul N) = A.adj.mul Ix := congrArg _ h
  rw [← mul_assocx, adj_mulx, hdet, diagx_one, Ix_mul, mul_Ix] at e
  exact e

/-- `cong A I = A A†`. -/
theorem cong_I (A : M2x p ν) : cong A Ix = A.mul A.dagger := by unfold cong; rw [mul_Ix]

/-- A unitary matrix of determinant one (`A A† = I`) fixing `M` under the congruence commutes with `M`. -/
theorem commute_of_cong (A M : M2x p ν) (hdet : A.det = 1) (hu : A.mul A.dagger = Ix) (h : cong A M = M) : A.mul M = M.mul A := by
  have hadj := right_inverse A A.dagger hdet hu
  unfold cong at h; rw [hadj] at h
  have e : ((A.mul M).mul A.adj).mul A = M.mul A := congrArg (fun Y => Y.mul A) h
  rw [mul_assocx, adj_mulx, hdet, diagx_one, mul_Ix] at e
  exact e

/-- The products with `σ_z` and `σ_x`, entrywise. -/
theorem mul_Dx (A : M2x p ν) : A.mul Dx = ⟨A.a, -A.b, A.c, -A.d⟩ ∧ Dx.mul A = ⟨A.a, A.b, -A.c, -A.d⟩ :=
  ⟨MX.sound (envAB A A) (MX.mul (MX.v 1) ⟨XR.one, XR.zero, XR.zero, XR.neg XR.one⟩) ⟨XR.v 1, XR.neg (XR.v 3), XR.v 5, XR.neg (XR.v 7)⟩ (by decide +kernel),
   MX.sound (envAB A A) (MX.mul ⟨XR.one, XR.zero, XR.zero, XR.neg XR.one⟩ (MX.v 1)) ⟨XR.v 1, XR.v 3, XR.neg (XR.v 5), XR.neg (XR.v 7)⟩ (by decide +kernel)⟩
theorem mul_Sx (A : M2x p ν) : A.mul Sx = ⟨A.b, A.a, A.d, A.c⟩ ∧ Sx.mul A = ⟨A.c, A.d, A.a, A.b⟩ :=
  ⟨MX.sound (envAB A A) (MX.mul (MX.v 1) ⟨XR.zero, XR.one, XR.one, XR.zero⟩) ⟨XR.v 3, XR.v 1, XR.v 7, XR.v 5⟩ (by decide +kernel),
   MX.sound (envAB A A) (MX.mul ⟨XR.zero, XR.one, XR.one, XR.zero⟩ (MX.v 1)) ⟨XR.v 5, XR.v 7, XR.v 1, XR.v 3⟩ (by decide +kernel)⟩

theorem two_ne_zero_ext (h2 : (1 + 1 : Shell p) ≠ 0) : (1 + 1 : Ext p ν) ≠ 0 := fun h => h2 (Ext.re_congr h)

/-- On a field shell of odd characteristic, `x + x = 0` forces `x = 0` in the extension. -/
theorem eq_zero_of_double (K : Fld p) (hν : ¬ ∃ y : Shell p, y * y = ν) (h2 : (1 + 1 : Shell p) ≠ 0) {x : Ext p ν} (h : x + x = 0) : x = 0 :=
  have e : (1 + 1 : Ext p ν) * x = x + x :=
    XR.sound (look [ν, x.re, x.im]) (XR.mul (XR.add XR.one XR.one) (XR.v 1)) (XR.add (XR.v 1) (XR.v 1)) (by decide +kernel)
  ext_eq_zero_of_mul K hν (two_ne_zero_ext h2) (by rw [e]; exact h)

/-- A matrix commuting with `σ_z` is diagonal. -/
theorem diagonal_of_commute_D (K : Fld p) (hν : ¬ ∃ y : Shell p, y * y = ν) (h2 : (1 + 1 : Shell p) ≠ 0) (A : M2x p ν)
    (hD : A.mul Dx = Dx.mul A) : A.b = 0 ∧ A.c = 0 := by
  rw [(mul_Dx A).1, (mul_Dx A).2] at hD
  have hb : -A.b = A.b := M2x.ext'_b hD
  have hc : A.c = -A.c := M2x.ext'_c hD
  refine ⟨eq_zero_of_double K hν h2 ?_, eq_zero_of_double K hν h2 ?_⟩
  · have : A.b + A.b = -A.b + A.b := by rw [hb]
    rw [this]; exact Ext.ext (Shell.neg_add _) (Shell.neg_add _)
  · have : A.c + A.c = A.c + -A.c := by rw [← hc]
    rw [this]; exact Ext.ext (Shell.add_neg _) (Shell.add_neg _)

/-- A matrix commuting with `σ_z` and `σ_x` is scalar. -/
theorem scalar_of_commute (K : Fld p) (hν : ¬ ∃ y : Shell p, y * y = ν) (h2 : (1 + 1 : Shell p) ≠ 0) (A : M2x p ν)
    (hD : A.mul Dx = Dx.mul A) (hS : A.mul Sx = Sx.mul A) : A = diagx A.a A.a := by
  obtain ⟨hb, hc⟩ := diagonal_of_commute_D K hν h2 A hD
  rw [(mul_Sx A).1, (mul_Sx A).2] at hS
  have had : A.a = A.d := M2x.ext'_b hS
  exact M2x.ext' rfl hb hc had.symm

/-- `diag(a, d) (ηJ) diag(a, d)† = (a conj d) ηJ`, `diag(a, d) σ_x diag(a, d)† = [[0, a conj d], [d conj a, 0]]`, and
`diag(a, d) diag(a, d)† = diag(N a, N d)`. -/
theorem cong_diag (a d : Ext p ν) :
    cong (diagx a d) (X 0 0 1 0) = ⟨0, (a * Ext.conj d) * Ext.w, -((d * Ext.conj a) * Ext.w), 0⟩ ∧
    cong (diagx a d) Sx = ⟨0, a * Ext.conj d, d * Ext.conj a, 0⟩ ∧
    (diagx a d).mul (diagx a d).dagger = diagx (Ext.ofShell (Ext.norm a)) (Ext.ofShell (Ext.norm d)) :=
  let e := look (p := p) [ν, a.re, a.im, d.re, d.im]
  ⟨MX.sound e (MXcong ⟨XR.v 1, XR.zero, XR.zero, XR.v 3⟩ MXT)
     ⟨XR.zero, XR.mul (XR.mul (XR.v 1) (XR.conj (XR.v 3))) ⟨.zero, .one⟩, XR.neg (XR.mul (XR.mul (XR.v 3) (XR.conj (XR.v 1))) ⟨.zero, .one⟩), XR.zero⟩ (by decide +kernel),
   MX.sound e (MXcong ⟨XR.v 1, XR.zero, XR.zero, XR.v 3⟩ ⟨XR.zero, XR.one, XR.one, XR.zero⟩)
     ⟨XR.zero, XR.mul (XR.v 1) (XR.conj (XR.v 3)), XR.mul (XR.v 3) (XR.conj (XR.v 1)), XR.zero⟩ (by decide +kernel),
   MX.sound e (MX.mul ⟨XR.v 1, XR.zero, XR.zero, XR.v 3⟩ (MX.tr (MX.conj ⟨XR.v 1, XR.zero, XR.zero, XR.v 3⟩)))
     ⟨⟨.add (.mul (.var 1) (.var 1)) (.neg (.mul (.var 0) (.mul (.var 2) (.var 2)))), .zero⟩, XR.zero, XR.zero,
      ⟨.add (.mul (.var 3) (.var 3)) (.neg (.mul (.var 0) (.mul (.var 4) (.var 4)))), .zero⟩⟩ (by decide +kernel)⟩

theorem one_ne_neg_one (h2 : (1 + 1 : Shell p) ≠ 0) : (1 : Shell p) ≠ -1 := fun h => h2 (by
  have e : (1 : Shell p) + 1 = 1 + -1 := by rw [← h]
  rw [e]; exact Shell.add_neg (1 : Shell p))

/-- On a field shell with `ν` a nonsquare, `a² = 1` in the extension forces `a = ±1`. -/
theorem sq_one (K : Fld p) (hν : ¬ ∃ y : Shell p, y * y = ν) (a : Ext p ν) (hsq : a * a = 1) : a = 1 ∨ a = -1 := by
  have fac : (a + -1) * (a + 1) = 0 := by
    have e : (a + -1) * (a + 1) = a * a + -1 :=
      XR.sound (look [ν, a.re, a.im]) (XR.mul (XR.add (XR.v 1) (XR.neg XR.one)) (XR.add (XR.v 1) XR.one)) (XR.add (XR.mul (XR.v 1) (XR.v 1)) (XR.neg XR.one)) (by decide +kernel)
    rw [e, hsq]; exact ext_add_neg_self 1
  match Ext.instDecidableEq (a + -1) 0 with
  | isTrue h => exact Or.inl (ext_eq_of_add_neg_eq_zero h)
  | isFalse h =>
    have h' : a + 1 = 0 := ext_eq_zero_of_mul K hν h fac
    have nn : -(-1 : Ext p ν) = 1 := Ext.ext (Shell.neg_neg 1) (by show -(-(0 : Shell p)) = 0; rw [Shell.neg_neg])
    exact Or.inr (ext_eq_of_add_neg_eq_zero (by rw [nn]; exact h'))

theorem norm_one' : Ext.norm (1 : Ext p ν) = 1 :=
  RE.sound (look [ν]) (.add (.mul .one .one) (.neg (.mul (.var 0) (.mul .zero .zero)))) .one (by decide +kernel)
theorem norm_neg_one : Ext.norm (-1 : Ext p ν) = 1 :=
  RE.sound (look [ν]) (.add (.mul (.neg .one) (.neg .one)) (.neg (.mul (.var 0) (.mul (.neg .zero) (.neg .zero))))) .one (by decide +kernel)
theorem negx_negx (M : M2x p ν) : negx (negx M) = M :=
  MX.sound (envAB M M) ⟨XR.neg (XR.neg (XR.v 1)), XR.neg (XR.neg (XR.v 3)), XR.neg (XR.neg (XR.v 5)), XR.neg (XR.neg (XR.v 7))⟩ (MX.v 1) (by decide +kernel)

/-- 7:X4, 7:C2 — **the kernel of the congruence is `±I`**: a matrix of determinant one fixing the four basis vectors of the
register square is `I` or `−I`. -/
theorem kernel_pm (K : Fld p) (hν : ¬ ∃ y : Shell p, y * y = ν) (h2 : (1 + 1 : Shell p) ≠ 0) (A : M2x p ν) (hdet : A.det = 1)
    (h0 : cong A (X 1 0 0 0) = X 1 0 0 0) (h1 : cong A (X 0 1 0 0) = X 0 1 0 0) (h3 : cong A (X 0 0 0 1) = X 0 0 0 1) :
    A = diagx 1 1 ∨ A = diagx (-1) (-1) := by
  rw [X_I] at h0; rw [X_S] at h1; rw [X_D] at h3
  have hu : A.mul A.dagger = Ix := by rw [← cong_I]; exact h0
  have hA := scalar_of_commute K hν h2 A (commute_of_cong A Dx hdet hu h3) (commute_of_cong A Sx hdet hu h1)
  have hsq : A.a * A.a = 1 := by
    have e : (diagx A.a A.a).det = A.a * A.a :=
      XR.sound (look [ν, A.a.re, A.a.im]) (MX.det ⟨XR.v 1, XR.zero, XR.zero, XR.v 1⟩) (XR.mul (XR.v 1) (XR.v 1)) (by decide +kernel)
    rw [← e, ← hA]; exact hdet
  rw [hA]
  match sq_one K hν A.a hsq with
  | Or.inl h => exact Or.inl (by rw [h])
  | Or.inr h => exact Or.inr (by rw [h])

/-- 7:X6, 7:F3 — **the time reversal is not a Lorentz move.** No matrix of determinant one carries the four basis vectors of the
register square as the Frobenius does, `x₂ ↦ −x₂` (which negates the time vector and fixes `I`, `σ_x`, `σ_z`). -/
theorem no_time_reversal (K : Fld p) (hν : ¬ ∃ y : Shell p, y * y = ν) (h2 : (1 + 1 : Shell p) ≠ 0) (A : M2x p ν) (hdet : A.det = 1)
    (h0 : cong A (X 1 0 0 0) = X 1 0 0 0) (h1 : cong A (X 0 1 0 0) = X 0 1 0 0) (h3 : cong A (X 0 0 0 1) = X 0 0 0 1)
    (hT : cong A (X 0 0 1 0) = X 0 0 (-1) 0) : False := by
  rw [X_I] at h0; rw [X_S] at h1; rw [X_D] at h3
  have hu : A.mul A.dagger = Ix := by rw [← cong_I]; exact h0
  have hA := scalar_of_commute K hν h2 A (commute_of_cong A Dx hdet hu h3) (commute_of_cong A Sx hdet hu h1)
  obtain ⟨cT, _, cU⟩ := cong_diag A.a A.a
  rw [hA] at hu hT; rw [cU] at hu; rw [cT] at hT
  -- `N a = 1` from `A A† = I`, and `N a = −1` from the time vector
  have n1 : Ext.norm A.a = 1 := Ext.re_congr (M2x.ext'_a hu)
  have hb := M2x.ext'_b hT
  have e : (A.a * Ext.conj A.a) * Ext.w = ⟨0, Ext.norm A.a⟩ := by
    rw [Ext.mul_conj]
    exact XR.sound (look [ν, Ext.norm A.a]) (XR.mul (sv 1) ⟨.zero, .one⟩) ⟨.zero, .var 1⟩ (by decide +kernel)
  rw [e] at hb
  have n2 : Ext.norm A.a = -1 := Ext.im_congr hb
  exact one_ne_neg_one h2 (n1.symm.trans n2)

/-- 7:X6, 7:F3 — **a spatial reflection is not a Lorentz move**: no matrix of determinant one carries the basis as `x₁ ↦ −x₁` (negating `σ_x`, fixing `I`, `σ_z`
and the time vector). -/
theorem no_reflection (K : Fld p) (hν : ¬ ∃ y : Shell p, y * y = ν) (h2 : (1 + 1 : Shell p) ≠ 0) (A : M2x p ν) (hdet : A.det = 1)
    (h0 : cong A (X 1 0 0 0) = X 1 0 0 0) (h1 : cong A (X 0 1 0 0) = X 0 (-1) 0 0) (h3 : cong A (X 0 0 0 1) = X 0 0 0 1)
    (hT : cong A (X 0 0 1 0) = X 0 0 1 0) : False := by
  rw [X_I] at h0; rw [X_S, X_negS] at h1; rw [X_D] at h3
  have hu : A.mul A.dagger = Ix := by rw [← cong_I]; exact h0
  obtain ⟨hb, hc⟩ := diagonal_of_commute_D K hν h2 A (commute_of_cong A Dx hdet hu h3)
  have hA : A = diagx A.a A.d := M2x.ext' rfl hb hc rfl
  obtain ⟨cT, cS, _⟩ := cong_diag A.a A.d
  rw [hA] at h1 hT; rw [cS] at h1; rw [cT] at hT
  -- `a conj d = −1` from `σ_x`, and `(a conj d) η = η` from the time vector
  have q1 : A.a * Ext.conj A.d = -1 := M2x.ext'_b h1
  have q2 : (A.a * Ext.conj A.d) * Ext.w = ⟨0, 1⟩ := M2x.ext'_b hT
  rw [q1] at q2
  have : (-1 : Ext p ν) * Ext.w = ⟨0, -1⟩ := XR.sound (look [ν]) (XR.mul (XR.neg XR.one) ⟨.zero, .one⟩) ⟨.zero, .neg .one⟩ (by decide +kernel)
  rw [this] at q2
  exact one_ne_neg_one h2 (Ext.im_congr q2).symm

/-- 7:X6, 7:F3 — **the total inversion is not a Lorentz move**: no matrix of determinant one carries the basis as `X ↦ −X`. -/
theorem no_inversion (K : Fld p) (hν : ¬ ∃ y : Shell p, y * y = ν) (h2 : (1 + 1 : Shell p) ≠ 0) (A : M2x p ν) (hdet : A.det = 1)
    (h0 : cong A (X 1 0 0 0) = X (-1) 0 0 0) (h1 : cong A (X 0 1 0 0) = X 0 (-1) 0 0) (h3 : cong A (X 0 0 0 1) = X 0 0 0 (-1)) : False := by
  rw [X_I, X_negI] at h0; rw [X_S, X_negS] at h1; rw [X_D, X_negD] at h3
  have hu : A.mul (negx A.dagger) = Ix := by
    rw [mul_negx, ← cong_I, h0]
    exact MX.sound (look [ν]) ⟨XR.neg (XR.neg XR.one), XR.neg (XR.neg XR.zero), XR.neg (XR.neg XR.zero), XR.neg (XR.neg XR.one)⟩ ⟨XR.one, XR.zero, XR.zero, XR.one⟩ (by decide +kernel)
  have hadj := right_inverse A _ hdet hu
  -- the congruences with `A† = −adj A` read `A M adj A = M`
  have comm : ∀ M : M2x p ν, cong A M = negx M → A.mul M = M.mul A := fun M h => by
    unfold cong at h
    have hd : A.dagger = negx A.adj := by
      have : negx (negx A.dagger) = negx A.adj := congrArg negx hadj
      have nn : negx (negx A.dagger) = A.dagger :=
        MX.sound (envAB A.dagger A.dagger) ⟨XR.neg (XR.neg (XR.v 1)), XR.neg (XR.neg (XR.v 3)), XR.neg (XR.neg (XR.v 5)), XR.neg (XR.neg (XR.v 7))⟩ (MX.v 1) (by decide +kernel)
      rw [← nn]; exact this
    rw [hd, mul_negx] at h
    have h' := negx_inj h
    have e : ((A.mul M).mul A.adj).mul A = M.mul A := congrArg (fun Y => Y.mul A) h'
    rw [mul_assocx, adj_mulx, hdet, diagx_one, mul_Ix] at e
    exact e
  have hA := scalar_of_commute K hν h2 A (comm Dx h3) (comm Sx h1)
  obtain ⟨_, _, cU⟩ := cong_diag A.a A.a
  -- `A A† = −I` gives `N a = −1`; `det A = a² = 1` gives `a = ±1` and `N a = 1`
  have hu' : A.mul A.dagger = negx Ix := by
    have e : negx (A.mul A.dagger) = Ix := by rw [← mul_negx]; exact hu
    rw [← negx_negx (A.mul A.dagger), e]
  rw [hA, cU] at hu'
  have nm : Ext.norm A.a = -1 := Ext.re_congr (M2x.ext'_a hu')
  have hsq : A.a * A.a = 1 := by
    have e : (diagx A.a A.a).det = A.a * A.a :=
      XR.sound (look [ν, A.a.re, A.a.im]) (MX.det ⟨XR.v 1, XR.zero, XR.zero, XR.v 1⟩) (XR.mul (XR.v 1) (XR.v 1)) (by decide +kernel)
    rw [← e, ← hA]; exact hdet
  have n1 : Ext.norm A.a = 1 := match sq_one K hν A.a hsq with
    | Or.inl h => by rw [h]; exact norm_one'
    | Or.inr h => by rw [h]; exact norm_neg_one
  exact one_ne_neg_one h2 (n1.symm.trans nm)

/-! ## The horizon (7:D6) -/

/-- 7:D6, 7:A15 — `η` has order two modulo `𝔽_p^×`: `η² = ν ∈ 𝔽_p` while `η ∉ 𝔽_p` (its imaginary part is `1`). -/
theorem horizon_order_two : (Ext.w : Ext p ν) * Ext.w = Ext.ofShell ν ∧ (Ext.w : Ext p ν).im = 1 := ⟨Ext.w_sq, rfl⟩

/-- 7:D6 — the half step of the cycle `C_{p+1}`, `p = 4κ + 1`: `p + 1 = 2(2κ + 1)`, and `2κ + 1` is odd. -/
theorem half_step_odd (κ : Nat) : 4 * κ + 1 + 1 = 2 * (2 * κ + 1) ∧ (2 * κ + 1) % 2 = 1 :=
  ⟨by rw [Nat.mul_add, ← FRC.Nat.mul_assoc], FRC.Nat.mod_unique (by decide) rfl⟩

/-- 7:D6 — **the even steps never reach the horizon.** On a field shell with a quarter-turn `i² = −1` and `ν` a nonsquare,
no square `y²` of the extension lies on the line `𝔽_p^× η` of the horizon: `y² = cη`, `c ≠ 0`, would make
`ν = (i · N(y) · c⁻¹)²` a square. The unimodular torus, the even powers of a generator, misses the horizon. -/
theorem even_never_horizon (K : Fld p) (hν : ¬ ∃ y : Shell p, y * y = ν) (i : Shell p) (hi : i * i = -1)
    (c : Shell p) (hc : c ≠ 0) (y : Ext p ν) : y * y ≠ Ext.ofShell c * Ext.w := fun h => by
  have hn : Ext.norm y * Ext.norm y = c * c * -ν := by
    have e : Ext.norm (Ext.ofShell c * Ext.w : Ext p ν) = c * c * -ν :=
      RE.sound (look [ν, c]) (.add (.mul (.add (.mul (.var 1) .zero) (.mul (.var 0) (.mul .zero .one))) (.add (.mul (.var 1) .zero) (.mul (.var 0) (.mul .zero .one))))
        (.neg (.mul (.var 0) (.mul (.add (.mul (.var 1) .one) (.mul .zero .zero)) (.add (.mul (.var 1) .one) (.mul .zero .zero))))))
        (.mul (.mul (.var 1) (.var 1)) (.neg (.var 0))) (by decide +kernel)
    rw [← e, ← h]; exact (Ext.norm_mul y y).symm
  obtain ⟨s, hs⟩ := K.exists_inv hc
  apply hν
  refine ⟨i * (Ext.norm y * s), ?_⟩
  have e1 : i * (Ext.norm y * s) * (i * (Ext.norm y * s)) = i * i * (Ext.norm y * Ext.norm y * (s * s)) :=
    RE.sound (look [i, Ext.norm y, s]) (.mul (.mul (.var 0) (.mul (.var 1) (.var 2))) (.mul (.var 0) (.mul (.var 1) (.var 2))))
      (.mul (.mul (.var 0) (.var 0)) (.mul (.mul (.var 1) (.var 1)) (.mul (.var 2) (.var 2)))) (by decide +kernel)
  have e2 : (-1 : Shell p) * (c * c * -ν * (s * s)) = ν * ((c * s) * (c * s)) :=
    RE.sound (look [ν, c, s]) (.mul (.neg .one) (.mul (.mul (.mul (.var 1) (.var 1)) (.neg (.var 0))) (.mul (.var 2) (.var 2))))
      (.mul (.var 0) (.mul (.mul (.var 1) (.var 2)) (.mul (.var 1) (.var 2)))) (by decide +kernel)
  rw [e1, hi, hn, e2, hs, Shell.one_mul, Shell.mul_one]

/-! ## The drift (7:F4, 7:A17) -/

/-- 7:F4, 7:A25 — the joint period of a coprime pair, with its Bezout certificate `aκ = bS + 1` (at the laboratory pair
`(13, 233)`: `3 · 39 = 2 · 58 + 1`): `4κS` is a common multiple of `4κ` and `4S`, and every common multiple `L = 4κx = 4Sy` is a
multiple of `4κS` — the joint period is `lcm(4κ, 4S) = 4κS`. -/
theorem joint_period (κ S a b : Nat) (hS : 0 < S) (hbz : a * κ = b * S + 1) :
    (∃ x, 4 * κ * S = 4 * κ * x) ∧ (∃ y, 4 * κ * S = 4 * S * y) ∧
    ∀ L x y, L = 4 * κ * x → L = 4 * S * y → ∃ z, L = 4 * κ * S * z := by
  refine ⟨⟨S, rfl⟩, ⟨κ, by rw [FRC.Nat.mul_assoc, Nat.mul_comm κ S, ← FRC.Nat.mul_assoc]⟩, fun L x y hx hy => ?_⟩
  have e : κ * x = S * y := Nat.eq_of_mul_eq_mul_left (by decide : 0 < 4) (by rw [← FRC.Nat.mul_assoc, ← FRC.Nat.mul_assoc, ← hx, ← hy])
  have e2 : S * (b * x) + x = S * (a * y) :=
    calc S * (b * x) + x = (b * S + 1) * x := by rw [FRC.Nat.add_mul, Nat.one_mul, FRC.Nat.mul_assoc b S x, FRC.Nat.mul_left_comm b S x]
      _ = a * κ * x := by rw [hbz]
      _ = a * (S * y) := by rw [FRC.Nat.mul_assoc, e]
      _ = S * (a * y) := FRC.Nat.mul_left_comm a S y
  have e3 : (S * (b * x) + x) % S = (S * (a * y)) % S := by rw [e2]
  have hz : (S * (a * y)) % S = 0 := by
    have h0 := FRC.Nat.add_mul_mod_self_left 0 (a * y) S hS
    rw [Nat.add_zero, FRC.Nat.zero_mod] at h0; exact h0
  rw [FRC.Nat.add_mul_mod_self_left x (b * x) S hS, hz] at e3
  obtain ⟨q, hq⟩ := FRC.Nat.mod_spec S hS x
  rw [e3, Nat.add_zero] at hq
  exact ⟨q, by rw [hx, hq, FRC.Nat.mul_assoc (4 * κ) S q]⟩

/-- 7:X6, 7:F4 — **the drift distinguishes the revolutions on a hosted pair.** For a coprime pair, with its Bezout certificate `aκ = bS + 1`, the
chart count `4κn mod 4S` of the shell's origin after `n` revolutions is injective on `n < S`: two revolutions below `S` at the
same chart count are the same revolution. -/
theorem drift_injective (κ S n m a b : Nat) (hS : 0 < S) (hbz : a * κ = b * S + 1) (hn : n < S) (hm : m < S)
    (h : (4 * κ * n) % (4 * S) = (4 * κ * m) % (4 * S)) : n = m := by
  have h4 : 0 < 4 * S := Nat.mul_pos (by decide) hS
  obtain ⟨q1, e1⟩ := FRC.Nat.mod_spec (4 * S) h4 (4 * κ * n)
  obtain ⟨q2, e2⟩ := FRC.Nat.mod_spec (4 * S) h4 (4 * κ * m)
  rw [h] at e1
  generalize hr : 4 * κ * m % (4 * S) = r at e1 e2
  have e3 : 4 * (κ * n + S * q2) = 4 * (κ * m + S * q1) :=
    calc 4 * (κ * n + S * q2) = 4 * κ * n + 4 * S * q2 := by rw [Nat.mul_add, ← FRC.Nat.mul_assoc, ← FRC.Nat.mul_assoc]
      _ = 4 * S * q1 + r + 4 * S * q2 := by rw [e1]
      _ = 4 * S * q2 + r + 4 * S * q1 := by rw [Nat.add_right_comm, Nat.add_comm (4 * S * q1), ← Nat.add_right_comm]
      _ = 4 * κ * m + 4 * S * q1 := by rw [e2]
      _ = 4 * (κ * m + S * q1) := by rw [Nat.mul_add, ← FRC.Nat.mul_assoc, ← FRC.Nat.mul_assoc]
  have e4 : κ * n + S * q2 = κ * m + S * q1 := Nat.eq_of_mul_eq_mul_left (by decide : 0 < 4) e3
  have key : ∀ x q : Nat, a * (κ * x + S * q) = S * (b * x + a * q) + x := fun x q =>
    calc a * (κ * x + S * q) = a * κ * x + a * (S * q) := by rw [Nat.mul_add, ← FRC.Nat.mul_assoc]
      _ = (b * S + 1) * x + S * (a * q) := by rw [hbz, FRC.Nat.mul_left_comm a S q]
      _ = b * S * x + x + S * (a * q) := by rw [FRC.Nat.add_mul, Nat.one_mul]
      _ = S * (b * x) + x + S * (a * q) := by rw [FRC.Nat.mul_assoc b S x, FRC.Nat.mul_left_comm b S x]
      _ = S * (b * x) + S * (a * q) + x := by rw [Nat.add_right_comm]
      _ = S * (b * x + a * q) + x := by rw [Nat.mul_add]
  have e5 : S * (b * n + a * q2) + n = S * (b * m + a * q1) + m := by rw [← key n q2, ← key m q1, e4]
  have e6 : (S * (b * n + a * q2) + n) % S = (S * (b * m + a * q1) + m) % S := by rw [e5]
  rw [FRC.Nat.add_mul_mod_self_left n (b * n + a * q2) S hS, FRC.Nat.add_mul_mod_self_left m (b * m + a * q1) S hS,
      FRC.Nat.mod_eq_of_lt hn, FRC.Nat.mod_eq_of_lt hm] at e6
  exact e6

/-- 7:F4 — the three laboratory pairs of the corpus, `(13, 233)`, `(173, 30089)` and `(1549, 2408561)`: their Bezout
certificates `aκ = bS + 1` — `39 · 3 = 2 · 58 + 1`, `5073 · 43 = 29 · 7522 + 1`, `395203 · 387 = 254 · 602140 + 1` — and the
joint periods `4κS`: `696`, `1293784`, `932112720`. -/
theorem drift_instance : (39 * 3 = 2 * 58 + 1 ∧ 4 * 3 * 58 = 696) ∧ (5073 * 43 = 29 * 7522 + 1 ∧ 4 * 43 * 7522 = 1293784) ∧
    (395203 * 387 = 254 * 602140 + 1 ∧ 4 * 387 * 602140 = 932112720) := by decide

/-! ## The counts on the Subjects `𝔽₁₃`, `𝔽₁₇₃` and `𝔽₁₅₄₉`, decided by the kernel (7:C4, C9, B1) -/

/-- 7:X2, 7:C9 — the class equation `1 + (p² − 1) + p(p + 1)(p − 2)/2 + p²(p − 1)/2 = (p − 1)p(p + 1)` at `p = 13`. -/
theorem class_equation_13 : 1 + (13 * 13 - 1) + 13 * 14 * 11 / 2 + 13 * 13 * 12 / 2 = 12 * 13 * 14 := by decide
/-- 7:C9, 7:X2 — the class equation at `p = 173`. -/
theorem class_equation_173 : 1 + (173 * 173 - 1) + 173 * 174 * 171 / 2 + 173 * 173 * 172 / 2 = 172 * 173 * 174 := by decide
/-- 7:C9, 7:X2 — the class equation at `p = 1549`. -/
theorem class_equation_1549 : 1 + (1549 * 1549 - 1) + 1549 * 1550 * 1547 / 2 + 1549 * 1549 * 1548 / 2 = 1548 * 1549 * 1550 := by decide

/-- 7:C4 — the cone's `p² + 1` directions are the `p + 1` of space and the `p(p − 1)` causal rays, at `p = 13`. -/
theorem cone_count_13 : 13 + 1 + 13 * 12 = 13 * 13 + 1 := by decide
/-- 7:C4 — the cone's count at `p = 173`. -/
theorem cone_count_173 : 173 + 1 + 173 * 172 = 173 * 173 + 1 := by decide
/-- 7:C4 — the cone's count at `p = 1549`. -/
theorem cone_count_1549 : 1549 + 1 + 1549 * 1548 = 1549 * 1549 + 1 := by decide

/-- 7:P1, 7:B1 — the three cycles have the consecutive orders `4κ`, `4κ + 1`, `4κ + 2` on the shell `p = 4κ + 1`. -/
theorem consecutive_orders (κ : Nat) : (4 * κ + 1) - 1 = 4 * κ ∧ (4 * κ + 1) + 1 = 4 * κ + 2 := ⟨FRC.Nat.add_sub_cancel (4 * κ) 1, rfl⟩

/-! ## The general pair, and the counts on `𝔽₁₃` by elements (7:F4, C9, C4, D6; the repair of 1 November 2026) -/

/-- `(d x) mod (d y) = d (x mod y)` for `0 < d` and `0 < y`, from the division identity. -/
theorem mul_mod_mul_left' (d x y : Nat) (hd : 0 < d) (hy : 0 < y) : (d * x) % (d * y) = d * (x % y) := by
  obtain ⟨q, hq⟩ := FRC.Nat.mod_spec y hy x
  have hr : x % y < y := FRC.Nat.mod_lt' x hy
  have hdr : d * (x % y) < d * y := by
    have h := FRC.Nat.mul_lt_mul_of_lt_of_pos hr hd
    rw [Nat.mul_comm (x % y) d, Nat.mul_comm y d] at h; exact h
  apply FRC.Nat.mod_unique hdr
  calc d * x = d * (y * q + x % y) := by rw [← hq]
    _ = d * (y * q) + d * (x % y) := Nat.mul_add d (y * q) (x % y)
    _ = d * y * q + d * (x % y) := by rw [FRC.Nat.mul_assoc]

/-- 7:F4 — **the drift distinguishes the revolutions, general hosted pair.** With `d = gcd(κ, S)`, `κ = d κ'`, `S = d S'` and a Bezout
certificate `a κ' = b S' + 1` for the coprime parts, the chart count `4κn mod 4S` is injective on `n < S' = S/d`. -/
theorem drift_injective_gcd (κ' S' d n m a b : Nat) (hd : 0 < d) (hS : 0 < S') (hbz : a * κ' = b * S' + 1)
    (hn : n < S') (hm : m < S')
    (h : (4 * (d * κ') * n) % (4 * (d * S')) = (4 * (d * κ') * m) % (4 * (d * S'))) : n = m := by
  have h4S : 0 < 4 * S' := Nat.mul_pos (by decide) hS
  have e : ∀ x : Nat, (4 * (d * κ') * x) % (4 * (d * S')) = d * ((4 * κ' * x) % (4 * S')) := by
    intro x
    rw [FRC.Nat.mul_left_comm 4 d κ', FRC.Nat.mul_assoc d (4 * κ') x, FRC.Nat.mul_left_comm 4 d S']
    exact mul_mod_mul_left' d (4 * κ' * x) (4 * S') hd h4S
  rw [e n, e m] at h
  exact drift_injective κ' S' n m a b hS hbz hn hm (Nat.eq_of_mul_eq_mul_left hd h)

/-- 7:F4 — an admissible pair with `gcd(κ, S) = 3`: `(13, 181)`, `κ = 3 · 1`, `S = 45 = 3 · 15`, the certificate `1 · 1 = 0 · 15 + 1`
for the coprime parts, and the joint period `lcm(12, 180) = 180 = 4κS/3`. -/
theorem drift_instance_gcd : 3 = 3 * 1 ∧ 45 = 3 * 15 ∧ 1 * 1 = 0 * 15 + 1 ∧ 4 * 3 * 45 / 3 = 180 ∧ 13 * 13 < 181 := by decide

/-! ## The drift is one-directional (7:F4, 7:A17; the physical pair, 1 November 2026) -/

/-- 7:X6, 7:F4, 7:A17 — **a count below the Carrier's cycle is its own residue**: the chart count of a duration `n < Ω − 1` is `n`. -/
theorem drift_one_directional (Om n : Nat) (h : n < Om - 1) : n % (Om - 1) = n := FRC.Nat.mod_eq_of_lt h

/-- 7:B5, 7:F4, 7:A17 — **the nesting bound keeps every registrable depth below the cycle.** For an odd `p` with `p² < Ω = 4S + 1`,
`p²` is odd and `4S` even, so `p² ≤ 4S − 1`, and a registered duration `n ≤ p²` has `n < Ω − 1`: the cycle never acts. -/
theorem nesting_depth (p S n : Nat) (hp : p % 2 = 1) (hn : p * p < 4 * S + 1) (hd : n ≤ p * p) : n < 4 * S + 1 - 1 := by
  have h1 : p * p ≤ 4 * S := Nat.le_of_lt_succ hn
  have h2 : p * p % 2 = 1 := by rw [FRC.Nat.mul_mod p p 2 (by decide), hp]
  have h3 : 4 * S % 2 = 0 := by rw [FRC.Nat.mul_mod 4 S 2 (by decide)]; show 0 * (S % 2) % 2 = 0; rw [Nat.zero_mul]
  have h4 : p * p ≠ 4 * S := fun e => by rw [e] at h2; rw [h3] at h2; exact Nat.zero_ne_one h2
  have h5 : p * p < 4 * S := Nat.lt_of_le_of_ne h1 h4
  rw [Nat.add_sub_cancel]
  exact Nat.lt_of_le_of_lt hd h5

/-- 7:F4, 7:A17 — the three laboratory pairs and `(13, 181)`: `p² < Ω − 1` on each, and the hosted joint periods all exceed `p²`. -/
theorem drift_instance_pairs : 13 * 13 < 232 ∧ 173 * 173 < 30088 ∧ 1549 * 1549 < 2408560 ∧ 13 * 13 < 180 ∧
    13 * 13 < 696 ∧ 173 * 173 < 1293784 ∧ 1549 * 1549 < 932112720 ∧ 13 * 13 < 180 := by decide

/-- The discriminant class on `𝔽₁₃` of `[[a, b], [c, d]]`: `Δ = tr² − 4 det = (a − d)² + 4bc`, in `Nat` with `a − d` as `a + 13 − d`. -/
def disc13 (a b c d : Nat) : Nat := ((a + 13 - d) * (a + 13 - d) + 4 * b * c) % 13
/-- The nonzero squares of `𝔽₁₃`. -/
def isSquare13 (x : Nat) : Bool := [1, 3, 4, 9, 10, 12].contains x
/-- `ad − bc ≠ 0` on `𝔽₁₃`, in `Nat`. -/
def isInvertible13 (a b c d : Nat) : Bool := (a * d + 169 - b * c) % 13 != 0
/-- The elements of `GL₂(𝔽₁₃)` by discriminant class: `Δ` a nonzero square, `Δ = 0`, `Δ` a nonsquare. -/
def classCounts13 : Nat × Nat × Nat :=
  (List.range 13).foldl (fun acc a => (List.range 13).foldl (fun acc b => (List.range 13).foldl (fun acc c =>
    (List.range 13).foldl (fun acc d =>
      if isInvertible13 a b c d then
        let Δ := disc13 a b c d
        if Δ = 0 then (acc.1, acc.2.1 + 1, acc.2.2)
        else if isSquare13 Δ then (acc.1 + 1, acc.2.1, acc.2.2)
        else (acc.1, acc.2.1, acc.2.2 + 1)
      else acc) acc) acc) acc) (0, 0, 0)
/-- 7:C9, 7:X2 — **the class equation by elements at `p = 13`.** The `26208` invertible matrices fall into the three discriminant
classes with `12012`, `2028` and `12168` elements; divided by the `12` scalars these are the `1001` split classes, the identity
with the `168` unipotent classes, and the `1014` non-split classes of `PGL₂(𝔽₁₃)`: the three terms of `class_equation_13`. -/
theorem class_partition_13 : classCounts13 = (12012, 2028, 12168) ∧ 12012 = 12 * (13 * 14 * 11 / 2) ∧
    2028 = 12 * (1 + (13 * 13 - 1)) ∧ 12168 = 12 * (13 * 13 * 12 / 2) ∧ 12012 + 2028 + 12168 = 12 * (12 * 13 * 14) := by
  decide +kernel

/-- The null vectors of the register square `Q_2 = x₀² − x₁² − x₃² + 2x₂²` on `𝔽₁₃⁴`, the zero vector included. -/
def nullCount13 : Nat :=
  (List.range 13).foldl (fun acc x0 => (List.range 13).foldl (fun acc x1 => (List.range 13).foldl (fun acc x2 =>
    (List.range 13).foldl (fun acc x3 =>
      if (x0 * x0 + 2 * x2 * x2 + 2 * 169 - x1 * x1 - x3 * x3) % 13 = 0 then acc + 1 else acc) acc) acc) acc) 0
/-- 7:C3, 7:C4 — **the cone by vectors at `p = 13`**: `2041 = p³ − p² + p` null vectors, hence `(2041 − 1)/12 = 170 = p² + 1` null
lines, the count of `cone_count_13`. -/
theorem null_count_13 : nullCount13 = 2041 ∧ 2041 = 13 * 13 * 13 - 13 * 13 + 13 ∧ (2041 - 1) / 12 = 13 * 13 + 1 := by
  decide +kernel

/-- `K = 𝔽₁₃(η)`, `η² = 2`: the product of `a + bη` and `c + dη`. -/
def kmul13 (u v : Nat × Nat) : Nat × Nat := ((u.1 * v.1 + 2 * u.2 * v.2) % 13, (u.1 * v.2 + u.2 * v.1) % 13)
/-- The inverse of `b` in `𝔽₁₃^×` (`0` for `b = 0`). -/
def inv13 (b : Nat) : Nat := (List.range 13).foldl (fun acc c => if (b * c) % 13 = 1 then c else acc) 0
/-- The class of `a + bη` modulo `𝔽₁₃^×`: `(a/b, 1)` for `b ≠ 0`, the horizon `(1, 0)` for `b = 0`. -/
def nrm13 (u : Nat × Nat) : Nat × Nat := if u.2 = 0 then (1, 0) else ((u.1 * inv13 u.2) % 13, 1)
/-- The least `k ∈ [1, 14]` with `w^k ≡ t` modulo `𝔽₁₃^×`, or `0` when none. -/
def firstHit13 (w t : Nat × Nat) : Nat :=
  ((List.range 14).foldl (fun (acc : Nat × (Nat × Nat)) k =>
      let pw := kmul13 acc.2 w
      (if acc.1 = 0 ∧ nrm13 pw = nrm13 t then k + 1 else acc.1, pw)) (0, (1, 0))).1
/-- The `14 = p + 1` classes of `K^×/𝔽₁₃^×`, the directions `ℙ¹(𝔽₁₃)`. -/
def classes13 : List (Nat × Nat) := (1, 0) :: (List.range 13).map (fun a => (a, 1))
/-- The generators of the cycle `K^×/𝔽₁₃^×`: the classes whose first return to the identity is at `k = 14`. -/
def generators13 : List (Nat × Nat) := classes13.filter (fun w => firstHit13 w (1, 0) = 14)
/-- 7:D6 — **the horizon at the odd half step, by every generator, at `p = 13`.** `K^×/𝔽₁₃^×` is a cycle of order `14` with
`6 = φ(14)` generators, and every generator first carries the origin `η = [0 : 1]` to the horizon `1 = [1 : 0]` at the step
`7 = (p + 1)/2 = 2κ + 1`, which is odd; `η` itself has order two. -/
theorem horizon_half_step_13 : classes13.length = 14 ∧ generators13.length = 6 ∧
    generators13.all (fun w => firstHit13 w (0, 1) = 7) = true ∧ firstHit13 (0, 1) (1, 0) = 2 ∧ 7 % 2 = 1 := by
  decide +kernel

end FRC.Lorentz
