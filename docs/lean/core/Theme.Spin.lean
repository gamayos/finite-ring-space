import FrcCore.Theme.Extension
import FrcCore.Theme.Projective

/-!
# FrcCore.Theme.Spin — the frame group has one form (00:C27) and the adjoint action of `PGL₂` (00:C22)

The projective theme's second core file (20 October 2026; the master's witnesses, group C). On a prime shell `p = 4κ + 1`
with its quadratic extension `𝔽_{p²} = 𝔽_p[w]`, `w² = ν` a nonsquare and `w^p = −w` (the Frobenius conjugate of `w` is
`−w`):

* **The unitary form is the frame group** (00:C27). For the Hermitian form `wJ`, `J = [[0, 1], [−1, 0]]`, a matrix of
  determinant one over `𝔽_{p²}` is unitary exactly when its entries are Frobenius-fixed, i.e. lie in `𝔽_p`:
  `SU₂(𝔽_{p²}/𝔽_p) = SL₂(𝔽_p)` on the nose (`su2_eq_sl2`); the form is Hermitian because `conj w = −w` and `Jᵀ = −J`
  (`hermitian_wJ`). The proof is the two-by-two identity `Mᵀ J M = det(M) J`: unitarity reads `adj(M̄) M = I`, which
  with `adj(M) M = I` forces `M̄ = M`. Every element of `SL₂(𝔽_p)` has finite order (`finite_order`): the powers of
  `M` take at most `p⁴` values, so two of them coincide, and the adjugate cancels. The quadric clause — the sphere
  `x² + y² + z² + w² = 1` and `ad − bc = 1` correspond point by point through the quarter-turn `r² = −1` — is
  `Theme/Projective.lean`'s `sphere_det` and `Theme/Hopf.lean`'s `quat_bijective` (38:A7).
* **The adjoint action** (00:C22). Conjugation `X ↦ M X adj(M)` preserves the determinant up to `det(M)²` and scales
  the trace by `det M` (`ad_preserves`): on `SL₂` it is an orthogonal map of the trace-zero matrices for the form
  `−det`, the map `PGL₂ → SO₃`. A matrix commuting with `J` and with `diag(1, −1)` is scalar on an odd shell
  (`ad_kernel`): the kernel of the adjoint action is the centre, the map is injective.

The identities over `𝔽_{p²}` are decided by the ring normaliser of `Ring.lean`, lifted to pairs (`XR`: a symbolic
element of the extension, the variable `0` standing for `ν`) and to two-by-two matrices of pairs (`MX`), as
`Theme/Extension.lean` lifts it to quaternions. No axioms.
-/

namespace FRC.Spin

open FRC.Shell FRC.Shell.Frame FRC.Extension

variable {p : Nat} [Pos p] {ν : Shell p}

/-! ## The ring normaliser on the quadratic extension -/

/-- A symbolic element of `𝔽_{p²}`: its two parts as ring expressions; the variable `0` is `ν`. -/
structure XR where
  re : RE
  im : RE

namespace XR

/-- The value, the parts evaluated. -/
def eval (env : Nat → Shell p) (z : XR) : Ext p ν := ⟨z.re.eval env, z.im.eval env⟩

def add (z w : XR) : XR := ⟨.add z.re w.re, .add z.im w.im⟩
def neg (z : XR) : XR := ⟨.neg z.re, .neg z.im⟩
/-- `(a + b w)(c + d w) = (ac + ν bd) + (ad + bc) w`, `ν` the variable `0`. -/
def mul (z w : XR) : XR :=
  ⟨.add (.mul z.re w.re) (.mul (.var 0) (.mul z.im w.im)), .add (.mul z.re w.im) (.mul z.im w.re)⟩
/-- The Frobenius conjugate `w ↦ −w`. -/
def conj (z : XR) : XR := ⟨z.re, .neg z.im⟩
/-- The element of the variables `i, i + 1`. -/
def v (i : Nat) : XR := ⟨.var i, .var (i + 1)⟩
def zero : XR := ⟨.zero, .zero⟩
def one : XR := ⟨.one, .zero⟩

def check (l r : XR) : Bool := RE.check l.re r.re && RE.check l.im r.im

theorem sound (env : Nat → Shell p) (l r : XR) (h : check l r = true) : l.eval (ν := ν) env = r.eval env :=
  Ext.ext (RE.sound env _ _ (and_true_left h)) (RE.sound env _ _ (and_true_right h))

end XR

/-- A two-by-two matrix over `𝔽_{p²}`. -/
structure M2x (p : Nat) [Pos p] (ν : Shell p) where
  a : Ext p ν
  b : Ext p ν
  c : Ext p ν
  d : Ext p ν

namespace M2x

theorem ext' {M N : M2x p ν} (ha : M.a = N.a) (hb : M.b = N.b) (hc : M.c = N.c) (hd : M.d = N.d) : M = N := by
  cases M; cases N; cases ha; cases hb; cases hc; cases hd; rfl

theorem ext'_a {M N : M2x p ν} (h : M = N) : M.a = N.a := by cases h; rfl
theorem ext'_b {M N : M2x p ν} (h : M = N) : M.b = N.b := by cases h; rfl
theorem ext'_c {M N : M2x p ν} (h : M = N) : M.c = N.c := by cases h; rfl
theorem ext'_d {M N : M2x p ν} (h : M = N) : M.d = N.d := by cases h; rfl

def mul (M N : M2x p ν) : M2x p ν :=
  ⟨M.a * N.a + M.b * N.c, M.a * N.b + M.b * N.d, M.c * N.a + M.d * N.c, M.c * N.b + M.d * N.d⟩
/-- The transpose. -/
def tr (M : M2x p ν) : M2x p ν := ⟨M.a, M.c, M.b, M.d⟩
/-- The entrywise Frobenius conjugate. -/
def conj (M : M2x p ν) : M2x p ν := ⟨Ext.conj M.a, Ext.conj M.b, Ext.conj M.c, Ext.conj M.d⟩
/-- The adjoint `M† = M̄ᵀ`. -/
def dagger (M : M2x p ν) : M2x p ν := M.conj.tr
def det (M : M2x p ν) : Ext p ν := M.a * M.d + -(M.b * M.c)
def adj (M : M2x p ν) : M2x p ν := ⟨M.d, -M.b, -M.c, M.a⟩
/-- The Hermitian form `wJ = [[0, w], [−w, 0]]`. -/
def wJ (w : Ext p ν) : M2x p ν := ⟨0, w, -w, 0⟩
/-- `M` is unitary for the form `H`: `M† H M = H`. -/
def unitary (H M : M2x p ν) : Prop := (M.dagger.mul H).mul M = H

end M2x

/-- A symbolic two-by-two matrix over the extension. -/
structure MX where
  a : XR
  b : XR
  c : XR
  d : XR

namespace MX

def eval (env : Nat → Shell p) (M : MX) : M2x p ν := ⟨M.a.eval env, M.b.eval env, M.c.eval env, M.d.eval env⟩
def mul (M N : MX) : MX :=
  ⟨XR.add (XR.mul M.a N.a) (XR.mul M.b N.c), XR.add (XR.mul M.a N.b) (XR.mul M.b N.d),
   XR.add (XR.mul M.c N.a) (XR.mul M.d N.c), XR.add (XR.mul M.c N.b) (XR.mul M.d N.d)⟩
def tr (M : MX) : MX := ⟨M.a, M.c, M.b, M.d⟩
def conj (M : MX) : MX := ⟨M.a.conj, M.b.conj, M.c.conj, M.d.conj⟩
def det (M : MX) : XR := XR.add (XR.mul M.a M.d) (XR.neg (XR.mul M.b M.c))
/-- The matrix of the variables `i, …, i + 7`. -/
def v (i : Nat) : MX := ⟨XR.v i, XR.v (i + 2), XR.v (i + 4), XR.v (i + 6)⟩
def wJ (w : XR) : MX := ⟨XR.zero, w, XR.neg w, XR.zero⟩

def check (L R : MX) : Bool := XR.check L.a R.a && XR.check L.b R.b && (XR.check L.c R.c && XR.check L.d R.d)

theorem sound (env : Nat → Shell p) (L R : MX) (h : check L R = true) : L.eval (ν := ν) env = R.eval env :=
  M2x.ext' (XR.sound env _ _ (and_true_left (and_true_left h))) (XR.sound env _ _ (and_true_right (and_true_left h)))
    (XR.sound env _ _ (and_true_left (and_true_right h))) (XR.sound env _ _ (and_true_right (and_true_right h)))

end MX

/-- The environment of a matrix `M` (variables `1 … 8`), a second matrix `N` (`9 … 16`) and an element `w` (`17, 18`)
after `ν` (`0`). -/
def env (M N : M2x p ν) (w : Ext p ν) : Nat → Shell p :=
  look [ν, M.a.re, M.a.im, M.b.re, M.b.im, M.c.re, M.c.im, M.d.re, M.d.im,
        N.a.re, N.a.im, N.b.re, N.b.im, N.c.re, N.c.im, N.d.re, N.d.im, w.re, w.im]

/-! ## The frame group has one form (00:C27) -/

/-- `Mᵀ (wJ) M = det(M) · wJ`: the symplectic identity of two-by-two matrices, over the extension. -/
theorem tr_wJ_mul (M : M2x p ν) (w : Ext p ν) :
    (M.tr.mul (M2x.wJ w)).mul M = ⟨0, w * M.det, -(w * M.det), 0⟩ :=
  MX.sound (env M M w) (MX.mul (MX.mul (MX.tr (MX.v 1)) (MX.wJ (XR.v 17))) (MX.v 1))
    ⟨XR.zero, XR.mul (XR.v 17) (MX.det (MX.v 1)), XR.neg (XR.mul (XR.v 17) (MX.det (MX.v 1))), XR.zero⟩ (by decide +kernel)

/-- `Nᵀ (wJ) M` entrywise, for two matrices `N = [[a', b'], [c', d']]` and `M = [[a, b], [c, d]]`. -/
theorem tr_wJ_mul' (M N : M2x p ν) (w : Ext p ν) :
    (N.tr.mul (M2x.wJ w)).mul M =
      ⟨w * (N.a * M.c + -(N.c * M.a)), w * (N.a * M.d + -(N.c * M.b)),
       w * (N.b * M.c + -(N.d * M.a)), w * (N.b * M.d + -(N.d * M.b))⟩ :=
  MX.sound (env M N w) (MX.mul (MX.mul (MX.tr (MX.v 9)) (MX.wJ (XR.v 17))) (MX.v 1))
    ⟨XR.mul (XR.v 17) (XR.add (XR.mul (XR.v 9) (XR.v 5)) (XR.neg (XR.mul (XR.v 13) (XR.v 1)))),
     XR.mul (XR.v 17) (XR.add (XR.mul (XR.v 9) (XR.v 7)) (XR.neg (XR.mul (XR.v 13) (XR.v 3)))),
     XR.mul (XR.v 17) (XR.add (XR.mul (XR.v 11) (XR.v 5)) (XR.neg (XR.mul (XR.v 15) (XR.v 1)))),
     XR.mul (XR.v 17) (XR.add (XR.mul (XR.v 11) (XR.v 7)) (XR.neg (XR.mul (XR.v 15) (XR.v 3))))⟩ (by decide +kernel)

/-- The four recovery identities: with `E₁ = a'c − c'a`, `E₂ = a'd − c'b − 1`, `E₃ = d'a − b'c − 1`, `E₄ = b'd − d'b`,
each `x' − x` is a combination of `1 − det M` and the `Eᵢ`. -/
theorem recover (M N : M2x p ν) :
    N.a + -M.a = N.a * (1 + -M.det) + (M.a * (N.a * M.d + -(N.c * M.b) + -1) + -(M.b * (N.a * M.c + -(N.c * M.a)))) ∧
    N.c + -M.c = N.c * (1 + -M.det) + (M.c * (N.a * M.d + -(N.c * M.b) + -1) + -(M.d * (N.a * M.c + -(N.c * M.a)))) ∧
    N.b + -M.b = N.b * (1 + -M.det) + (M.a * (N.b * M.d + -(N.d * M.b)) + M.b * (N.d * M.a + -(N.b * M.c) + -1)) ∧
    N.d + -M.d = N.d * (1 + -M.det) + (M.d * (N.d * M.a + -(N.b * M.c) + -1) + M.c * (N.b * M.d + -(N.d * M.b))) :=
  let e : Nat → Shell p := env M N 0
  let a := XR.v 1; let b := XR.v 3; let c := XR.v 5; let d := XR.v 7
  let a' := XR.v 9; let b' := XR.v 11; let c' := XR.v 13; let d' := XR.v 15
  let dt := MX.det (MX.v 1)
  let E1 := XR.add (XR.mul a' c) (XR.neg (XR.mul c' a))
  let E2 := XR.add (XR.add (XR.mul a' d) (XR.neg (XR.mul c' b))) (XR.neg XR.one)
  let E3 := XR.add (XR.add (XR.mul d' a) (XR.neg (XR.mul b' c))) (XR.neg XR.one)
  let E4 := XR.add (XR.mul b' d) (XR.neg (XR.mul d' b))
  let one_det := XR.add XR.one (XR.neg dt)
  ⟨XR.sound e (XR.add a' (XR.neg a)) (XR.add (XR.mul a' one_det) (XR.add (XR.mul a E2) (XR.neg (XR.mul b E1)))) (by decide +kernel),
   XR.sound e (XR.add c' (XR.neg c)) (XR.add (XR.mul c' one_det) (XR.add (XR.mul c E2) (XR.neg (XR.mul d E1)))) (by decide +kernel),
   XR.sound e (XR.add b' (XR.neg b)) (XR.add (XR.mul b' one_det) (XR.add (XR.mul a E4) (XR.mul b E3))) (by decide +kernel),
   XR.sound e (XR.add d' (XR.neg d)) (XR.add (XR.mul d' one_det) (XR.add (XR.mul d E3) (XR.mul c E4))) (by decide +kernel)⟩

theorem ext_mul_zero (a : Ext p ν) : a * 0 = 0 :=
  XR.sound (look [ν, a.re, a.im]) (XR.mul (XR.v 1) XR.zero) XR.zero (by decide +kernel)

theorem ext_add_zero (a : Ext p ν) : a + 0 = a := Ext.ext (Shell.add_zero _) (Shell.add_zero _)

theorem ext_neg_zero : (-0 : Ext p ν) = 0 := Ext.ext Shell.neg_zero Shell.neg_zero

theorem ext_mul_neg (a b : Ext p ν) : a * -b = -(a * b) :=
  XR.sound (look [ν, a.re, a.im, b.re, b.im]) (XR.mul (XR.v 1) (XR.neg (XR.v 3))) (XR.neg (XR.mul (XR.v 1) (XR.v 3))) (by decide +kernel)

theorem ext_eq_of_add_neg_eq_zero {x y : Ext p ν} (h : x + -y = 0) : x = y :=
  Ext.ext (eq_of_add_neg_eq_zero (congrArg Ext.re h)) (eq_of_add_neg_eq_zero (congrArg Ext.im h))

theorem ext_add_neg_self (x : Ext p ν) : x + -x = 0 := Ext.ext (Shell.add_neg x.re) (Shell.add_neg x.im)

theorem ext_norm_zero : Ext.norm (0 : Ext p ν) = 0 := by
  show (0 : Shell p) * 0 + -(ν * (0 * 0)) = 0
  rw [mul_zero, mul_zero, neg_zero, add_zero]

/-- On a field shell with `ν` a nonsquare, the extension has no zero divisors: `w x = 0` and `w ≠ 0` give `x = 0`. -/
theorem ext_eq_zero_of_mul (K : Fld p) (hν : ¬ ∃ y : Shell p, y * y = ν) {w x : Ext p ν} (hw : w ≠ 0)
    (h : w * x = 0) : x = 0 := by
  have hn : Ext.norm w * Ext.norm x = 0 := by rw [← Ext.norm_mul, h, ext_norm_zero]
  have nz : ∀ z : Ext p ν, Ext.norm z = 0 → z = 0 := fun z hz =>
    match Shell.instDecidableEq z.re 0, Shell.instDecidableEq z.im 0 with
    | isTrue h1, isTrue h2 => Ext.ext h1 h2
    | isTrue h1, isFalse h2 => absurd hz (K.norm_ne_zero hν (Or.inr h2))
    | isFalse h1, _ => absurd hz (K.norm_ne_zero hν (Or.inl h1))
  exact match K.mul_eq_zero hn with
    | Or.inl e => absurd (nz w e) hw
    | Or.inr e => nz x e

/-- 00:C27 — the form `wJ` is Hermitian: `(wJ)† = wJ`, because `conj w = −w` (`w^p = −w`) and `Jᵀ = −J`. -/
theorem hermitian_wJ {w : Ext p ν} (hw : Ext.conj w = -w) : (M2x.wJ w).dagger = M2x.wJ w := by
  have c0 : Ext.conj (0 : Ext p ν) = 0 := Ext.ext rfl Shell.neg_zero
  have cn : Ext.conj (-w) = w := by
    have e : Ext.conj (-w) = -(Ext.conj w) := rfl
    rw [e, hw]; exact Ext.ext (Shell.neg_neg w.re) (Shell.neg_neg w.im)
  exact M2x.ext' c0 cn (by show Ext.conj w = -w; exact hw) c0

/-- 00:C27 — **the frame group has one form.** On a field shell, `ν` a nonsquare and `w ≠ 0` (the form `wJ` is Hermitian
for `conj w = −w`, `hermitian_wJ`): a matrix over `𝔽_{p²}` of determinant one is unitary for `wJ` exactly when its
entries are fixed by the Frobenius conjugation, i.e. lie in `𝔽_p` — `SU₂(𝔽_{p²}/𝔽_p) = SL₂(𝔽_p)`. -/
theorem su2_eq_sl2 (K : Fld p) (hν : ¬ ∃ y : Shell p, y * y = ν) {w : Ext p ν} (hw0 : w ≠ 0)
    (M : M2x p ν) (hdet : M.det = 1) : M2x.unitary (M2x.wJ w) M ↔ M.conj = M := by
  constructor
  · intro hu
    have h := hu
    unfold M2x.unitary M2x.dagger at h
    rw [tr_wJ_mul' M M.conj w] at h
    have ha := M2x.ext'_a h; have hb := M2x.ext'_b h; have hc := M2x.ext'_c h; have hd := M2x.ext'_d h
    simp only [M2x.conj, M2x.wJ] at ha hb hc hd
    -- the four equations after cancelling `w`
    have E1 : Ext.conj M.a * M.c + -(Ext.conj M.c * M.a) = 0 := ext_eq_zero_of_mul K hν hw0 ha
    have E2 : Ext.conj M.a * M.d + -(Ext.conj M.c * M.b) + -1 = 0 := by
      have : w * (Ext.conj M.a * M.d + -(Ext.conj M.c * M.b) + -1) = 0 := by
        rw [ext_mul_add, hb, ext_mul_neg, Ext.mul_one]; exact ext_add_neg_self w
      exact ext_eq_zero_of_mul K hν hw0 this
    have E3 : Ext.conj M.d * M.a + -(Ext.conj M.b * M.c) + -1 = 0 := by
      have : w * (Ext.conj M.d * M.a + -(Ext.conj M.b * M.c) + -1) = 0 := by
        have e : w * (Ext.conj M.d * M.a + -(Ext.conj M.b * M.c) + -1) =
            -(w * (Ext.conj M.b * M.c + -(Ext.conj M.d * M.a))) + -w :=
          XR.sound (env M M.conj w)
            (XR.mul (XR.v 17) (XR.add (XR.add (XR.mul (XR.v 15) (XR.v 1)) (XR.neg (XR.mul (XR.v 11) (XR.v 5)))) (XR.neg XR.one)))
            (XR.add (XR.neg (XR.mul (XR.v 17) (XR.add (XR.mul (XR.v 11) (XR.v 5)) (XR.neg (XR.mul (XR.v 15) (XR.v 1)))))) (XR.neg (XR.v 17)))
            (by decide +kernel)
        rw [e, hc]
        exact Ext.ext (Shell.neg_add _ ) (Shell.neg_add _)
      exact ext_eq_zero_of_mul K hν hw0 this
    have E4 : Ext.conj M.b * M.d + -(Ext.conj M.d * M.b) = 0 := ext_eq_zero_of_mul K hν hw0 hd
    obtain ⟨ra, rc, rb, rd⟩ := recover M M.conj
    have hz : (1 : Ext p ν) + -M.det = 0 := by rw [hdet]; exact ext_add_neg_self 1
    simp only [M2x.conj] at ra rc rb rd
    rw [hz, E1, E2, ext_mul_zero, ext_mul_zero, ext_mul_zero, ext_neg_zero, ext_add_zero, ext_add_zero] at ra rc
    rw [hz, E3, E4, ext_mul_zero, ext_mul_zero, ext_mul_zero, ext_add_zero, ext_add_zero] at rb rd
    exact M2x.ext' (ext_eq_of_add_neg_eq_zero ra) (ext_eq_of_add_neg_eq_zero rb)
      (ext_eq_of_add_neg_eq_zero rc) (ext_eq_of_add_neg_eq_zero rd)
  · intro hM
    show (M.conj.tr.mul (M2x.wJ w)).mul M = M2x.wJ w
    rw [hM, tr_wJ_mul, hdet, Ext.mul_one]
    rfl

/-! ## The sphere is `SL₂`, point by point (00:C27, 00:C22) -/

/-- 00:C27, 00:C22 — the quaternion map is a bijection of `𝔽_p⁴` onto `M₂` on a field shell with `r² = −1` and `2h = 1`, the
inverse `M ↦ ((a + d) h, (a − d)(−r) h, (b − c) h, (b + c)(−r) h)`: with `sphere_det`, the norm-one sphere is the whole of
`SL₂`, point by point through the quarter-turn. The projective theme's statement of `Theme/Hopf.lean`'s `quat_bijective`
(38:A7, the subject theme), so that the master's keys of C22 and C27 ride on the projective theme (20 October 2026). -/
theorem sphere_bijective (K : Fld p) {r h : Shell p} (hr : r * r = -1) (h2 : (1 + 1) * h = 1) :
    (∀ M : M2 p, quat r ((M.a + M.d) * h) ((M.a + -M.d) * (-r * h)) ((M.b + -M.c) * h) ((M.b + M.c) * (-r * h)) = M) ∧
    (∀ x y z w x' y' z' w' : Shell p, quat r x y z w = quat r x' y' z' w' → x = x' ∧ y = y' ∧ z = z' ∧ w = w') := by
  have ca : ∀ a d : Shell p, (a + d) * h + r * ((a + -d) * (-r * h)) = a := fun a d => by
    have e1 : (a + d) * h + r * ((a + -d) * (-r * h)) = (a + d) * h + -(r * r) * ((a + -d) * h) := Shell.Frame.RE.sound (Shell.Frame.look [a, d, h, r]) (.add (.mul (.add (.var 0) (.var 1)) (.var 2)) (.mul (.var 3) (.mul (.add (.var 0) (.neg (.var 1))) (.mul (.neg (.var 3)) (.var 2))))) (.add (.mul (.add (.var 0) (.var 1)) (.var 2)) (.mul (.neg (.mul (.var 3) (.var 3))) (.mul (.add (.var 0) (.neg (.var 1))) (.var 2)))) (by decide +kernel)
    have e2 : (a + d) * h + (a + -d) * h = a * ((1 + 1) * h) := Shell.Frame.RE.sound (Shell.Frame.look [a, d, h]) (.add (.mul (.add (.var 0) (.var 1)) (.var 2)) (.mul (.add (.var 0) (.neg (.var 1))) (.var 2))) (.mul (.var 0) (.mul (.add .one .one) (.var 2))) (by decide +kernel)
    rw [e1, hr, neg_neg, one_mul, e2, h2, mul_one]
  have cd : ∀ a d : Shell p, (a + d) * h + -(r * ((a + -d) * (-r * h))) = d := fun a d => by
    have e1 : (a + d) * h + -(r * ((a + -d) * (-r * h))) = (a + d) * h + -(-(r * r) * ((a + -d) * h)) := Shell.Frame.RE.sound (Shell.Frame.look [a, d, h, r]) (.add (.mul (.add (.var 0) (.var 1)) (.var 2)) (.neg (.mul (.var 3) (.mul (.add (.var 0) (.neg (.var 1))) (.mul (.neg (.var 3)) (.var 2)))))) (.add (.mul (.add (.var 0) (.var 1)) (.var 2)) (.neg (.mul (.neg (.mul (.var 3) (.var 3))) (.mul (.add (.var 0) (.neg (.var 1))) (.var 2))))) (by decide +kernel)
    have e2 : (a + d) * h + -((a + -d) * h) = d * ((1 + 1) * h) := Shell.Frame.RE.sound (Shell.Frame.look [a, d, h]) (.add (.mul (.add (.var 0) (.var 1)) (.var 2)) (.neg (.mul (.add (.var 0) (.neg (.var 1))) (.var 2)))) (.mul (.var 1) (.mul (.add .one .one) (.var 2))) (by decide +kernel)
    rw [e1, hr, neg_neg, one_mul, e2, h2, mul_one]
  have cb : ∀ b c : Shell p, (b + -c) * h + r * ((b + c) * (-r * h)) = b := fun b c => by
    have e1 : (b + -c) * h + r * ((b + c) * (-r * h)) = (b + -c) * h + -(r * r) * ((b + c) * h) := Shell.Frame.RE.sound (Shell.Frame.look [b, c, h, r]) (.add (.mul (.add (.var 0) (.neg (.var 1))) (.var 2)) (.mul (.var 3) (.mul (.add (.var 0) (.var 1)) (.mul (.neg (.var 3)) (.var 2))))) (.add (.mul (.add (.var 0) (.neg (.var 1))) (.var 2)) (.mul (.neg (.mul (.var 3) (.var 3))) (.mul (.add (.var 0) (.var 1)) (.var 2)))) (by decide +kernel)
    have e2 : (b + -c) * h + (b + c) * h = b * ((1 + 1) * h) := Shell.Frame.RE.sound (Shell.Frame.look [b, c, h]) (.add (.mul (.add (.var 0) (.neg (.var 1))) (.var 2)) (.mul (.add (.var 0) (.var 1)) (.var 2))) (.mul (.var 0) (.mul (.add .one .one) (.var 2))) (by decide +kernel)
    rw [e1, hr, neg_neg, one_mul, e2, h2, mul_one]
  have cc : ∀ b c : Shell p, -((b + -c) * h) + r * ((b + c) * (-r * h)) = c := fun b c => by
    have e1 : -((b + -c) * h) + r * ((b + c) * (-r * h)) = -((b + -c) * h) + -(r * r) * ((b + c) * h) := Shell.Frame.RE.sound (Shell.Frame.look [b, c, h, r]) (.add (.neg (.mul (.add (.var 0) (.neg (.var 1))) (.var 2))) (.mul (.var 3) (.mul (.add (.var 0) (.var 1)) (.mul (.neg (.var 3)) (.var 2))))) (.add (.neg (.mul (.add (.var 0) (.neg (.var 1))) (.var 2))) (.mul (.neg (.mul (.var 3) (.var 3))) (.mul (.add (.var 0) (.var 1)) (.var 2)))) (by decide +kernel)
    have e2 : -((b + -c) * h) + (b + c) * h = c * ((1 + 1) * h) := Shell.Frame.RE.sound (Shell.Frame.look [b, c, h]) (.add (.neg (.mul (.add (.var 0) (.neg (.var 1))) (.var 2))) (.mul (.add (.var 0) (.var 1)) (.var 2))) (.mul (.var 1) (.mul (.add .one .one) (.var 2))) (by decide +kernel)
    rw [e1, hr, neg_neg, one_mul, e2, h2, mul_one]
  have h2ne : (1 + 1 : Shell p) ≠ 0 := fun h0 => K.one_ne_zero (by rw [← h2, h0, zero_mul])
  have hrne : r ≠ 0 := fun h0 => K.one_ne_zero (by
    have := hr; rw [h0, zero_mul] at this; rw [← neg_neg (1 : Shell p), ← this, neg_zero])
  have ex : ∀ x y : Shell p, (1 + 1) * x = (x + r * y) + (x + -(r * y)) := fun x y => Shell.Frame.RE.sound (Shell.Frame.look [x, y, r]) (.mul (.add .one .one) (.var 0)) (.add (.add (.var 0) (.mul (.var 2) (.var 1))) (.add (.var 0) (.neg (.mul (.var 2) (.var 1))))) (by decide +kernel)
  have ey : ∀ x y : Shell p, (1 + 1) * (r * y) = (x + r * y) + -(x + -(r * y)) := fun x y => Shell.Frame.RE.sound (Shell.Frame.look [x, y, r]) (.mul (.add .one .one) (.mul (.var 2) (.var 1))) (.add (.add (.var 0) (.mul (.var 2) (.var 1))) (.neg (.add (.var 0) (.neg (.mul (.var 2) (.var 1)))))) (by decide +kernel)
  have ew : ∀ z w : Shell p, (1 + 1) * (r * w) = (z + r * w) + (-z + r * w) := fun z w => Shell.Frame.RE.sound (Shell.Frame.look [z, w, r]) (.mul (.add .one .one) (.mul (.var 2) (.var 1))) (.add (.add (.var 0) (.mul (.var 2) (.var 1))) (.add (.neg (.var 0)) (.mul (.var 2) (.var 1)))) (by decide +kernel)
  have ez : ∀ z w : Shell p, (1 + 1) * z = (z + r * w) + -(-z + r * w) := fun z w => Shell.Frame.RE.sound (Shell.Frame.look [z, w, r]) (.mul (.add .one .one) (.var 0)) (.add (.add (.var 0) (.mul (.var 2) (.var 1))) (.neg (.add (.neg (.var 0)) (.mul (.var 2) (.var 1))))) (by decide +kernel)
  refine ⟨fun M => M2.ext' (ca M.a M.d) (cb M.b M.c) (cc M.b M.c) (cd M.a M.d), fun x y z w x' y' z' w' e => ?_⟩
  have ha : x + r * y = x' + r * y' := M2.ext'_a e
  have hb : z + r * w = z' + r * w' := M2.ext'_b e
  have hc : -z + r * w = -z' + r * w' := M2.ext'_c e
  have hd : x + -(r * y) = x' + -(r * y') := M2.ext'_d e
  refine ⟨K.mul_left_cancel h2ne (by rw [ex x y, ex x' y', ha, hd]),
    K.mul_left_cancel hrne (K.mul_left_cancel h2ne (by rw [ey x y, ey x' y', ha, hd])),
    K.mul_left_cancel h2ne (by rw [ez z w, ez z' w', hb, hc]),
    K.mul_left_cancel hrne (K.mul_left_cancel h2ne (by rw [ew z w, ew z' w', hb, hc]))⟩

/-! ## Every element of the frame group has finite order (00:C27) -/

/-- The identity matrix. -/
def I : M2 p := ⟨1, 0, 0, 1⟩

/-- Powers of a matrix, `M⁰ = I`, `M^{n+1} = Mⁿ · M`. -/
def mpow (M : M2 p) : Nat → M2 p
  | 0 => I
  | n + 1 => (mpow M n).mul M

theorem smul_one' (M : M2 p) : M2.smul 1 M = M :=
  M2.ext' (one_mul _) (one_mul _) (one_mul _) (one_mul _)

theorem I_mul (M : M2 p) : I.mul M = M := by rw [I, M2.diag_mul, smul_one']

theorem mul_I (M : M2 p) : M.mul I = M := by rw [I, M2.mul_diag, smul_one']

theorem mpow_succ_left (M : M2 p) : ∀ n, mpow M (n + 1) = M.mul (mpow M n)
  | 0 => by show I.mul M = M.mul I; rw [I_mul, mul_I]
  | n + 1 => by show (mpow M (n + 1)).mul M = M.mul ((mpow M n).mul M); rw [mpow_succ_left M n, M2.mul_assoc']

theorem mpow_add (M : M2 p) (m : Nat) : ∀ n, mpow M (m + n) = (mpow M m).mul (mpow M n)
  | 0 => by show mpow M m = (mpow M m).mul I; rw [mul_I]
  | n + 1 => by
    show (mpow M (m + n)).mul M = (mpow M m).mul ((mpow M n).mul M)
    rw [mpow_add M m n, M2.mul_assoc']

/-- With `det M = 1`, `adj(M)ⁱ Mⁱ = I` for every `i`. -/
theorem adj_mpow_mul (M : M2 p) (hdet : M.det = 1) : ∀ i, (mpow M.adj i).mul (mpow M i) = I
  | 0 => by show I.mul I = I; exact I_mul I
  | i + 1 => by
    rw [mpow_succ_left M i]
    show ((mpow M.adj i).mul M.adj).mul (M.mul (mpow M i)) = I
    rw [M2.mul_assoc', ← M2.mul_assoc' M.adj, M2.adj_mul, hdet]
    show (mpow M.adj i).mul (I.mul (mpow M i)) = I
    rw [I_mul]; exact adj_mpow_mul M hdet i

/-- The mixed-radix code of a matrix, below `p⁴`. -/
def code (M : M2 p) : Nat := M.a.val + p * (M.b.val + p * (M.c.val + p * M.d.val))

omit [Pos p] in
theorem digit_lt {x X q : Nat} (hx : x < p) (hX : X < q) : x + p * X < p * q := by
  have h1 : x + p * X < p + p * X := Nat.add_lt_add_right hx _
  have h2 : p + p * X = p * (X + 1) := by rw [Nat.mul_succ, Nat.add_comm]
  rw [h2] at h1
  exact Nat.lt_of_lt_of_le h1 (Nat.mul_le_mul_left p (Nat.succ_le_of_lt hX))

theorem code_lt (M : M2 p) : code M < p * (p * (p * p)) :=
  digit_lt M.a.lt (digit_lt M.b.lt (digit_lt M.c.lt M.d.lt))

omit [Pos p] in
theorem digit_inj {x x' X X' : Nat} (hx : x < p) (hx' : x' < p) (h : x + p * X = x' + p * X') : x = x' ∧ X = X' := by
  have h' : p * X + x = p * X' + x' := by rw [Nat.add_comm, h, Nat.add_comm]
  have hX : X = X' := FRC.Nat.quot_unique hx hx' h'
  refine ⟨?_, hX⟩
  rw [hX] at h
  exact Nat.add_right_cancel h

theorem code_inj {M N : M2 p} (h : code M = code N) : M = N := by
  have ⟨ha, h1⟩ := digit_inj M.a.lt N.a.lt h
  have ⟨hb, h2⟩ := digit_inj M.b.lt N.b.lt h1
  have ⟨hc, hd⟩ := digit_inj M.c.lt N.c.lt h2
  exact M2.ext' (Shell.ext ha) (Shell.ext hb) (Shell.ext hc) (Shell.ext hd)

/-- A bounded search: some `i < n` has `f i = true`. -/
def anyLt (f : Nat → Bool) : Nat → Bool
  | 0 => false
  | n + 1 => anyLt f n || f n

theorem anyLt_true {f : Nat → Bool} : ∀ {n}, anyLt f n = true → ∃ i, i < n ∧ f i = true
  | 0, h => nomatch h
  | n + 1, h =>
    match hn : anyLt f n, hf : f n with
    | true, _ => match anyLt_true hn with | ⟨i, hi, e⟩ => ⟨i, Nat.lt_succ_of_lt hi, e⟩
    | false, true => ⟨n, Nat.lt_succ_self n, hf⟩
    | false, false => by
      have h' : (anyLt f n || f n) = true := h
      rw [hn, hf] at h'
      exact nomatch h'

theorem anyLt_false {f : Nat → Bool} : ∀ {n}, anyLt f n = false → ∀ i, i < n → f i = false
  | 0, _, i, hi => absurd hi (Nat.not_lt_zero i)
  | n + 1, h, i, hi =>
    have h' : (anyLt f n || f n) = false := h
    have hn : anyLt f n = false := by
      match e : anyLt f n with
      | false => rfl
      | true => rw [e] at h'; exact nomatch h'
    have hf : f n = false := by rw [hn] at h'; exact h'
    match Nat.lt_or_ge i n with
    | Or.inl hlt => anyLt_false hn i hlt
    | Or.inr hge => (Nat.le_antisymm (Nat.le_of_lt_succ hi) hge) ▸ hf

/-- The pigeonhole on a sequence: `N + 1` values below `N` collide. -/
theorem collide (σ : Nat → Nat) (N : Nat) (hb : ∀ k, k ≤ N → σ k < N) : ∃ i j, i < j ∧ j ≤ N ∧ σ i = σ j := by
  match hs : anyLt (fun j => anyLt (fun i => decide (σ i = σ j)) j) (N + 1) with
  | true =>
    match anyLt_true hs with
    | ⟨j, hj, hj'⟩ => match anyLt_true hj' with
      | ⟨i, hi, e⟩ => exact ⟨i, j, hi, Nat.le_of_lt_succ hj, of_decide_eq_true e⟩
  | false =>
    have inj : ∀ i j, i < N + 1 → j < N + 1 → σ i = σ j → i = j := fun i j hi hj e =>
      match Nat.lt_or_ge i j with
      | Or.inl hlt => absurd (decide_eq_true e) (by rw [anyLt_false (anyLt_false hs j hj) i hlt]; decide)
      | Or.inr hge => match Nat.lt_or_ge j i with
        | Or.inl hlt => absurd (decide_eq_true e.symm) (by rw [anyLt_false (anyLt_false hs i hi) j hlt]; decide)
        | Or.inr hge' => Nat.le_antisymm hge' hge
    have nd := imageList_nodup inj (Nat.le_refl (N + 1))
    have hlt : ∀ e, Pigeonhole.mem e (imageList σ (N + 1)) → e < N := fun e he =>
      match mem_imageList he with
      | ⟨j, hj, ej⟩ => by rw [← ej]; exact hb j (Nat.le_of_lt_succ hj)
    have := Pigeonhole.length_le_of_nodup_lt N _ nd hlt
    rw [imageList_length] at this
    exact absurd this (Nat.not_succ_le_self N)

/-- 00:C27 — every element of `SL₂` has finite order: with `det M = 1` some positive `n ≤ p⁴` has `Mⁿ = I` — the `p⁴ + 1`
powers `M⁰, …, M^{p⁴}` cannot be distinct, and the adjugate cancels the common factor. -/
theorem finite_order (M : M2 p) (hdet : M.det = 1) : ∃ n, 0 < n ∧ n ≤ p * (p * (p * p)) ∧ mpow M n = I := by
  match collide (fun k => code (mpow M k)) (p * (p * (p * p))) (fun k _ => code_lt (mpow M k)) with
  | ⟨i, j, hij, hjN, e⟩ =>
    have hpow : mpow M i = mpow M j := code_inj e
    have hj : j = i + (j - i) := (FRC.Nat.add_sub_of_le (Nat.le_of_lt hij)).symm
    have hpos : 0 < j - i := by                             -- without `Nat.sub_pos_of_lt`, which carries propext
      match e : j - i with
      | 0 =>
        have hji : j = i := by rw [e, Nat.add_zero] at hj; exact hj
        exact absurd (hji ▸ hij) (Nat.lt_irrefl i)
      | k + 1 => exact Nat.zero_lt_succ k
    refine ⟨j - i, hpos, Nat.le_trans (Nat.sub_le j i) hjN, ?_⟩
    have h1 : (mpow M i).mul (mpow M (j - i)) = (mpow M i).mul I := by
      rw [← mpow_add, ← hj, ← hpow, mul_I]
    have h2 := congrArg (fun X => (mpow M.adj i).mul X) h1
    rw [← M2.mul_assoc', ← M2.mul_assoc', adj_mpow_mul M hdet i, I_mul, I_mul] at h2
    exact h2

/-! ## The adjoint action of `PGL₂` (00:C22) -/

/-- 00:C22 — conjugation `X ↦ M X adj(M)` multiplies the determinant by `det(M)²` and the trace by `det M`: on `SL₂`
it preserves `−det` on the trace-zero matrices — the map `PGL₂(𝔽_p) → SO₃(𝔽_p)` of the row. -/
theorem ad_preserves (M X : M2 p) :
    ((M.mul X).mul M.adj).det = M.det * M.det * X.det ∧
    ((M.mul X).mul M.adj).a + ((M.mul X).mul M.adj).d = M.det * (X.a + X.d) :=
  ⟨RE.sound (look [M.a, M.b, M.c, M.d, X.a, X.b, X.c, X.d]) (.add (.mul (.add (.mul (.add (.mul (.var 0) (.var 4)) (.mul (.var 1) (.var 6))) (.var 3)) (.mul (.add (.mul (.var 0) (.var 5)) (.mul (.var 1) (.var 7))) (.neg (.var 2)))) (.add (.mul (.add (.mul (.var 2) (.var 4)) (.mul (.var 3) (.var 6))) (.neg (.var 1))) (.mul (.add (.mul (.var 2) (.var 5)) (.mul (.var 3) (.var 7))) (.var 0)))) (.neg (.mul (.add (.mul (.add (.mul (.var 0) (.var 4)) (.mul (.var 1) (.var 6))) (.neg (.var 1))) (.mul (.add (.mul (.var 0) (.var 5)) (.mul (.var 1) (.var 7))) (.var 0))) (.add (.mul (.add (.mul (.var 2) (.var 4)) (.mul (.var 3) (.var 6))) (.var 3)) (.mul (.add (.mul (.var 2) (.var 5)) (.mul (.var 3) (.var 7))) (.neg (.var 2))))))) (.mul (.mul (.add (.mul (.var 0) (.var 3)) (.neg (.mul (.var 1) (.var 2)))) (.add (.mul (.var 0) (.var 3)) (.neg (.mul (.var 1) (.var 2))))) (.add (.mul (.var 4) (.var 7)) (.neg (.mul (.var 5) (.var 6))))) (by decide +kernel),
   RE.sound (look [M.a, M.b, M.c, M.d, X.a, X.b, X.c, X.d]) (.add (.add (.mul (.add (.mul (.var 0) (.var 4)) (.mul (.var 1) (.var 6))) (.var 3)) (.mul (.add (.mul (.var 0) (.var 5)) (.mul (.var 1) (.var 7))) (.neg (.var 2)))) (.add (.mul (.add (.mul (.var 2) (.var 4)) (.mul (.var 3) (.var 6))) (.neg (.var 1))) (.mul (.add (.mul (.var 2) (.var 5)) (.mul (.var 3) (.var 7))) (.var 0)))) (.mul (.add (.mul (.var 0) (.var 3)) (.neg (.mul (.var 1) (.var 2)))) (.add (.var 4) (.var 7))) (by decide +kernel)⟩

/-- The quarter-turn matrix `J = [[0, 1], [−1, 0]]` and the reflection `D = diag(1, −1)`. -/
def J : M2 p := ⟨0, 1, -1, 0⟩
def D : M2 p := ⟨1, 0, 0, -1⟩

/-- 00:C22 — the kernel of the adjoint action is the centre: on a frame (an odd shell) a matrix commuting with `J` and
with `D` is scalar, `b = c = 0` and `a = d`; so `PGL₂ → SO₃` is injective. -/
theorem ad_kernel {κ : Nat} {g : Shell p} (F : Frame p κ g) (M : M2 p) (hJ : M.mul J = J.mul M) (hD : M.mul D = D.mul M) :
    M.b = 0 ∧ M.c = 0 ∧ M.a = M.d := by
  have ja : -M.b = M.c := by
    have e : M.a * 0 + M.b * -1 = 0 * M.a + 1 * M.c := M2.ext'_a hJ
    rw [mul_zero, zero_add, ← mul_neg, mul_one, zero_mul, zero_add, one_mul] at e
    exact e
  have jb : M.a = M.d := by
    have e : M.a * 1 + M.b * 0 = 0 * M.b + 1 * M.d := M2.ext'_b hJ
    rw [mul_one, mul_zero, add_zero, zero_mul, zero_add, one_mul] at e
    exact e
  have db : -M.b = M.b := by
    have e : M.a * 0 + M.b * -1 = 1 * M.b + 0 * M.d := M2.ext'_b hD
    rw [mul_zero, zero_add, ← mul_neg, mul_one, one_mul, zero_mul, add_zero] at e
    exact e
  have hb : M.b = 0 := by
    have h2 : (1 + 1) * M.b = 0 := by
      rw [right_distrib, one_mul]
      have e : M.b + M.b = -M.b + M.b := congrArg (fun x => x + M.b) db.symm
      rw [e]; exact Shell.neg_add M.b
    exact match F.mul_eq_zero h2 with
      | Or.inl h => absurd (by rw [two_eq_one_add_one]; exact h) F.two_ne_zero
      | Or.inr h => h
  exact ⟨hb, by rw [← ja, hb, neg_zero], jb⟩

end FRC.Spin
