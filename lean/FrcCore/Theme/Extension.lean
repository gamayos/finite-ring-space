import FrcCore.Ring
import FrcCore.Frame
import FrcCore.Theme.Quadratic

/-!
# FrcCore.Theme.Extension — the quaternion norm and the Lorentzian plane (the extension theme, task LM17)

The quadratic extension `FRC.Extension.Ext p ν` itself is `Theme/Quadratic.lean`, frame-free, and the normaliser that
decides ring identities on the shell is the base's `Ring.lean` (both split off by task LM24, every name unchanged).
This file keeps what needs the frame or the quaternions: conjugation fixes exactly the prime meridian (`fixed_conj`);
the quaternions over the shell, the Hamilton product, conjugation and the norm, and the multiplicativity of the norm
`N(qr) = N(q) N(r)` (1-algebra's Quaternion.lean, names unchanged); and the Lorentzian plane of the shell: the square
classes, the diagonal form `Q_ν = −ν t² + x² + y² + z²`, the boosts `Λ(γ, b)` with `γ² − νb² = 1` (the norm-one elements
of `𝔽_p(√ν)`), their velocities and the counts of the null cone and of the boosts (3-causality's Causality.lean, task
LM20, names unchanged); and the two strata of probability (00:C10, 8 October 2026): the tally line, the conjugate-pair
trace tally and the dial-ensemble Parseval tally in the extension, the engineered-core weights and the framed readout.
No axioms.
-/

namespace FRC.Extension

open FRC.Shell

namespace Ext
variable {p : Nat} [Pos p] {ν : Shell p}

section frame
variable {κ : Nat} {g : Shell p}

/-- 20:B9 — the fixed locus of conjugation is the prime meridian: `z̄ = z ⟺ b = 0`. -/
theorem fixed_conj (F : Frame p κ g) (z : Ext p ν) : conj z = z ↔ z.im = 0 := by
  constructor
  · intro h
    exact F.eq_zero_of_eq_neg (im_congr h).symm
  · intro h
    exact ext rfl (show -z.im = z.im by rw [h, Shell.neg_zero])

end frame

end Ext

end FRC.Extension


namespace FRC
namespace Shell
namespace Frame

variable {p : Nat} [Pos p]

/-- A quaternion over the shell. -/
structure Quat (p : Nat) [Pos p] where
  a : Shell p
  b : Shell p
  c : Shell p
  d : Shell p

/-- The Hamilton product on the shell. -/
def Quat.mul (q r : Quat p) : Quat p :=
  ⟨(q.a * r.a + -(q.b * r.b)) + (-(q.c * r.c) + -(q.d * r.d)),
   (q.a * r.b + q.b * r.a) + (q.c * r.d + -(q.d * r.c)),
   (q.a * r.c + -(q.b * r.d)) + (q.c * r.a + q.d * r.b),
   (q.a * r.d + q.b * r.c) + (-(q.c * r.b) + q.d * r.a)⟩



/-! ## Quaternions over the shell: conjugation, norm, cross and dot products, and their expression twins -/

def Quat.conj (q : Quat p) : Quat p := ⟨q.a, -q.b, -q.c, -q.d⟩
def Quat.nrm (q : Quat p) : Shell p := q.a * q.a + q.b * q.b + (q.c * q.c + q.d * q.d)
def Quat.vec (q : Quat p) : Quat p := ⟨0, q.b, q.c, q.d⟩
def Quat.sc (s : Shell p) : Quat p := ⟨s, 0, 0, 0⟩
def Quat.smul (s : Shell p) (q : Quat p) : Quat p := ⟨s * q.a, s * q.b, s * q.c, s * q.d⟩
def Quat.add (q r : Quat p) : Quat p := ⟨q.a + r.a, q.b + r.b, q.c + r.c, q.d + r.d⟩
def Quat.neg (q : Quat p) : Quat p := ⟨-q.a, -q.b, -q.c, -q.d⟩
def Quat.cross (v x : Quat p) : Quat p := ⟨0, v.c * x.d + -(v.d * x.c), v.d * x.b + -(v.b * x.d), v.b * x.c + -(v.c * x.b)⟩
def Quat.dot (v x : Quat p) : Shell p := v.b * x.b + v.c * x.c + v.d * x.d
/-- Conjugation by `q`, not yet divided by the norm: `x ↦ q x q̄`. -/
def Quat.conjBy (q x : Quat p) : Quat p := Quat.mul (Quat.mul q x) (Quat.conj q)

theorem Quat.ext4 {q r : Quat p} (ha : q.a = r.a) (hb : q.b = r.b) (hc : q.c = r.c) (hd : q.d = r.d) : q = r :=
  match q, r, ha, hb, hc, hd with
  | ⟨_, _, _, _⟩, ⟨_, _, _, _⟩, rfl, rfl, rfl, rfl => rfl

theorem Quat.pure_eq {x : Quat p} (hx : x.a = 0) : x = ⟨0, x.b, x.c, x.d⟩ :=
  match x, hx with
  | ⟨_, _, _, _⟩, rfl => rfl

structure QR where
  a : RE
  b : RE
  c : RE
  d : RE

def QR.eval (env : Nat → Shell p) (q : QR) : Quat p := ⟨q.a.eval env, q.b.eval env, q.c.eval env, q.d.eval env⟩
def QR.mul (q r : QR) : QR :=
  ⟨.add (.add (.mul q.a r.a) (.neg (.mul q.b r.b))) (.add (.neg (.mul q.c r.c)) (.neg (.mul q.d r.d))),
   .add (.add (.mul q.a r.b) (.mul q.b r.a)) (.add (.mul q.c r.d) (.neg (.mul q.d r.c))),
   .add (.add (.mul q.a r.c) (.neg (.mul q.b r.d))) (.add (.mul q.c r.a) (.mul q.d r.b)),
   .add (.add (.mul q.a r.d) (.mul q.b r.c)) (.add (.neg (.mul q.c r.b)) (.mul q.d r.a))⟩
def QR.conj (q : QR) : QR := ⟨q.a, .neg q.b, .neg q.c, .neg q.d⟩
def QR.nrm (q : QR) : RE := .add (.add (.mul q.a q.a) (.mul q.b q.b)) (.add (.mul q.c q.c) (.mul q.d q.d))
def QR.vec (q : QR) : QR := ⟨.zero, q.b, q.c, q.d⟩
def QR.sc (s : RE) : QR := ⟨s, .zero, .zero, .zero⟩
def QR.smul (s : RE) (q : QR) : QR := ⟨.mul s q.a, .mul s q.b, .mul s q.c, .mul s q.d⟩
def QR.add (q r : QR) : QR := ⟨.add q.a r.a, .add q.b r.b, .add q.c r.c, .add q.d r.d⟩
def QR.neg (q : QR) : QR := ⟨.neg q.a, .neg q.b, .neg q.c, .neg q.d⟩
def QR.cross (v x : QR) : QR :=
  ⟨.zero, .add (.mul v.c x.d) (.neg (.mul v.d x.c)), .add (.mul v.d x.b) (.neg (.mul v.b x.d)), .add (.mul v.b x.c) (.neg (.mul v.c x.b))⟩
def QR.dot (v x : QR) : RE := .add (.add (.mul v.b x.b) (.mul v.c x.c)) (.mul v.d x.d)
def QR.conjBy (q x : QR) : QR := QR.mul (QR.mul q x) (QR.conj q)
/-- A quaternion of variables `i, i+1, i+2, i+3`; a pure one of variables `i, i+1, i+2`. -/
def QR.v (i : Nat) : QR := ⟨.var i, .var (i + 1), .var (i + 2), .var (i + 3)⟩
def QR.pv (i : Nat) : QR := ⟨.zero, .var i, .var (i + 1), .var (i + 2)⟩

def QR.check (l r : QR) : Bool := RE.check l.a r.a && RE.check l.b r.b && (RE.check l.c r.c && RE.check l.d r.d)

theorem QR.sound (env : Nat → Shell p) (l r : QR) (h : QR.check l r = true) : l.eval env = r.eval env :=
  Quat.ext4 (RE.sound env _ _ (and_true_left (and_true_left h))) (RE.sound env _ _ (and_true_right (and_true_left h)))
    (RE.sound env _ _ (and_true_left (and_true_right h))) (RE.sound env _ _ (and_true_right (and_true_right h)))


/-- 1:E8, the norm is multiplicative: `N(qr) = N(q) N(r)`. -/
theorem nrm_mul (q r : Quat p) : Quat.nrm (Quat.mul q r) = Quat.nrm q * Quat.nrm r :=
  RE.sound (look [q.a, q.b, q.c, q.d, r.a, r.b, r.c, r.d]) (QR.nrm (QR.mul (QR.v 0) (QR.v 4))) (.mul (QR.nrm (QR.v 0)) (QR.nrm (QR.v 4))) (by decide +kernel)

end Frame
end Shell
end FRC

/-! ## The Lorentzian plane of the shell: the square classes, the diagonal form and the boosts (3-causality's
`Causality.lean`, moved by the ledger migration, task LM20, names unchanged) -/

namespace FRC
namespace Shell
namespace Frame

variable {p : Nat} [Pos p] {κ : Nat} {g : Shell p}

/-- `x` is a square: `x = y·y` for some residue `y`. -/
def IsSquare (x : Shell p) : Prop := ∃ y : Shell p, y * y = x

/-- 3:B2 (Thm. nonexistence, first clause) — `c² = ν` makes `ν` a square, so a nonsquare `ν` has no root `c`. -/
theorem no_causal_root {ν : Shell p} (h : ¬IsSquare ν) (c : Shell p) : c * c ≠ ν := fun e => h ⟨c, e⟩

theorem sq_mul (a b : Shell p) : (a * b) * (a * b) = (a * a) * (b * b) := mul_mul_mul_comm a b a b

/-- 3:B2 (Thm. nonexistence, the consequence) — `−c²` is a square on every shell: `−c² = (i·c)²` with `i² = −1`;
so with `c ≠ 0` every coefficient of `−c² t² + x² + y² + z²` is a square and the form is Euclidean. -/
theorem neg_sq_is_square (F : Frame p κ g) (c : Shell p) : IsSquare (-(c * c)) :=
  ⟨quarterTurn g κ * c, by rw [sq_mul, F.quarter_turn_sq, neg_one_mul]⟩

/-- 3:B2 — `−1` itself is a square (`i²`): the paper's hypothesis `p ≡ 1 (mod 4)` in the shell's own terms. -/
theorem neg_one_is_square (F : Frame p κ g) : IsSquare (-1 : Shell p) := ⟨quarterTurn g κ, F.quarter_turn_sq⟩

/-- 3:B3 (Lemma absorption) — if `a_i = w_i² a_0` for `i = 1, 2, 3` then
`a_0 x_0² + a_1 x_1² + a_2 x_2² + a_3 x_3² = a_0 (x_0² + (w_1 x_1)² + (w_2 x_2)² + (w_3 x_3)²)`: a common square
class is absorbed by the rescaling `x_i ↦ w_i x_i`, with no square root of `a_0` itself required. -/
theorem absorb (a0 a1 a2 a3 w1 w2 w3 x0 x1 x2 x3 : Shell p) (h1 : w1 * w1 * a0 = a1) (h2 : w2 * w2 * a0 = a2)
    (h3 : w3 * w3 * a0 = a3) :
    a0 * (x0 * x0) + a1 * (x1 * x1) + a2 * (x2 * x2) + a3 * (x3 * x3) =
    a0 * (x0 * x0 + (w1 * x1) * (w1 * x1) + (w2 * x2) * (w2 * x2) + (w3 * x3) * (w3 * x3)) := by
  rw [← h1, ← h2, ← h3, sq_mul w1 x1, sq_mul w2 x2, sq_mul w3 x3, left_distrib, left_distrib, left_distrib,
    mul_left_comm a0 (w1 * w1), mul_left_comm a0 (w2 * w2), mul_left_comm a0 (w3 * w3),
    mul_assoc (w1 * w1), mul_assoc (w2 * w2), mul_assoc (w3 * w3)]

/-! ### The binary form `x² − ν t²`, the norm of `K = F_p(√ν)` -/

/-- The `(t, x)`-plane form `Q₂(t, x) = x² − ν t²`, the norm `N(x + t√ν)`. -/
def Q2 (ν t x : Shell p) : Shell p := x * x + -(ν * (t * t))

/-- 3:B5 — the plane `x² − ν t²` is anisotropic when `ν` is a nonsquare: `x² = ν t²` forces `t = x = 0`
(else `ν = (x/t)²`).  This is the Witt kernel of the Lorentzian form, its index one. -/
theorem aniso_tx (F : Frame p κ g) {ν : Shell p} (h : ¬IsSquare ν) {t x : Shell p} (e : x * x = ν * (t * t)) :
    t = 0 ∧ x = 0 := by
  match Shell.instDecidableEq t 0 with
  | .isTrue ht =>
    refine ⟨ht, ?_⟩
    rw [ht, mul_zero, mul_zero] at e
    match F.mul_eq_zero e with
    | .inl hx => exact hx
    | .inr hx => exact hx
  | .isFalse ht =>
    match F.exists_inv ht with
    | ⟨s, hs⟩ =>
      exact absurd ⟨x * s, by
        calc (x * s) * (x * s) = (x * x) * (s * s) := sq_mul x s
          _ = ν * ((t * t) * (s * s)) := by rw [e, mul_assoc]
          _ = ν * ((t * s) * (t * s)) := by rw [sq_mul t s]
          _ = ν := by rw [hs, one_mul, mul_one]⟩ h

/-- 3:B5 — the `(y, z)`-plane `y² + z²` is hyperbolic on every shell: `(1, i)` is null. -/
theorem null_yz (F : Frame p κ g) : (1 : Shell p) * 1 + quarterTurn g κ * quarterTurn g κ = 0 := by
  rw [F.quarter_turn_sq, one_mul, add_neg]

/-- 3:B5 — for a square `ν = w²` the `(t, x)`-plane is hyperbolic too: `(1, w)` is null; the form is then
`H ⊥ H`, Witt index two — the Euclidean type. -/
theorem null_tx_of_square (w : Shell p) : Q2 (w * w) 1 w = 0 := by
  unfold Q2; rw [mul_one, mul_one, add_neg]

/-! ### The boosts -/

theorem sq_add (u v : Shell p) : (u + v) * (u + v) = u * u + (u * v + u * v) + v * v := by
  rw [right_distrib, left_distrib, left_distrib, mul_comm v u, ← add_assoc, add_assoc (u * u)]

theorem regroup (P R S T X : Shell p) : P + (X + X) + R + (S + -(X + X) + T) = P + S + T + R := by
  rw [add_add_add_comm, add_assoc P, add_left_comm (X + X), add_neg, add_zero, add_comm R T, ← add_assoc]

/-- The norm is multiplicative: `N((a + b√ν)(c + d√ν)) = N(a + b√ν) N(c + d√ν)`, i.e.
`(ac + νbd)² − ν(ad + bc)² = (a² − νb²)(c² − νd²)` — the identity behind every boost. -/
theorem norm_mul (ν a b c d : Shell p) :
    Q2 ν (a * d + b * c) (a * c + ν * (b * d)) = (a * a + -(ν * (b * b))) * (c * c + -(ν * (d * d))) := by
  unfold Q2
  have cross : (a * c) * (b * d) = (a * d) * (b * c) := by
    rw [mul_assoc, mul_left_comm c, ← mul_assoc, mul_assoc a d, mul_left_comm d, ← mul_assoc a b (d * c), mul_comm d c]
  have e1 : (a * c + ν * (b * d)) * (a * c + ν * (b * d)) =
      (a * c) * (a * c) + (ν * ((a * c) * (b * d)) + ν * ((a * c) * (b * d))) + (ν * ν) * ((b * d) * (b * d)) := by
    rw [sq_add, mul_left_comm (a * c) ν (b * d), sq_mul ν (b * d)]
  have e2 : -(ν * ((a * d + b * c) * (a * d + b * c))) =
      -(ν * ((a * d) * (a * d))) + -(ν * ((a * d) * (b * c)) + ν * ((a * d) * (b * c))) + -(ν * ((b * c) * (b * c))) := by
    rw [sq_add, left_distrib, left_distrib, left_distrib, neg_add_rev, neg_add_rev]
  rw [e1, e2, cross, regroup]
  rw [right_distrib, left_distrib, left_distrib, ← mul_neg, ← neg_mul, neg_mul_neg, ← add_assoc,
    ← sq_mul a c, mul_left_comm (a * a) ν (d * d), ← sq_mul a d, mul_assoc ν (b * b) (c * c), ← sq_mul b c,
    mul_assoc ν (b * b) (ν * (d * d)), mul_left_comm (b * b) ν (d * d), ← mul_assoc ν ν, ← sq_mul b d]

/-- The boost `Λ(γ, b)` of `(t, x)`: `t ↦ γ t + b x`, `x ↦ γ x + ν b t` (multiplication by `γ + b√ν` in `K`). -/
def boostT (_ν γ b t x : Shell p) : Shell p := γ * t + b * x
def boostX (ν γ b t x : Shell p) : Shell p := γ * x + ν * (b * t)

/-- 3:C2 (the finite Lorentz boost) — with `γ² − νb² = 1`, `Λ(γ, b)` preserves `x² − ν t²` exactly, on every shell. -/
theorem boost_preserves {ν γ b : Shell p} (h : γ * γ + -(ν * (b * b)) = 1) (t x : Shell p) :
    Q2 ν (boostT ν γ b t x) (boostX ν γ b t x) = Q2 ν t x := by
  unfold boostT boostX
  have := norm_mul ν γ b x t
  unfold Q2 at this ⊢
  rw [this, h, one_mul]

/-- 3:C2 — boosts compose as their parameters multiply in `K`:
`Λ(γ₁, b₁) Λ(γ₂, b₂) = Λ(γ₁γ₂ + νb₁b₂, γ₁b₂ + b₁γ₂)`, the `t`-row. -/
theorem boost_comp_t (ν γ1 b1 γ2 b2 t x : Shell p) :
    boostT ν γ1 b1 (boostT ν γ2 b2 t x) (boostX ν γ2 b2 t x) =
    boostT ν (γ1 * γ2 + ν * (b1 * b2)) (γ1 * b2 + b1 * γ2) t x := by
  unfold boostT boostX
  rw [left_distrib, left_distrib, right_distrib, right_distrib, ← mul_assoc γ1 γ2 t, ← mul_assoc γ1 b2 x,
    ← mul_assoc b1 γ2 x, mul_left_comm b1 ν (b2 * t), ← mul_assoc b1 b2 t, ← mul_assoc ν (b1 * b2) t,
    add_comm (b1 * γ2 * x) (ν * (b1 * b2) * t), add_add_add_comm]

/-- 3:C2 — the composition, the `x`-row. -/
theorem boost_comp_x (ν γ1 b1 γ2 b2 t x : Shell p) :
    boostX ν γ1 b1 (boostT ν γ2 b2 t x) (boostX ν γ2 b2 t x) =
    boostX ν (γ1 * γ2 + ν * (b1 * b2)) (γ1 * b2 + b1 * γ2) t x := by
  unfold boostT boostX
  rw [left_distrib, left_distrib, left_distrib, right_distrib, right_distrib, left_distrib,
    ← mul_assoc γ1 γ2 x, mul_left_comm γ1 ν (b2 * t), ← mul_assoc γ1 b2 t, ← mul_assoc b1 γ2 t,
    ← mul_assoc b1 b2 x, ← mul_assoc ν (b1 * b2) x,
    add_comm (ν * (b1 * γ2 * t)) (ν * (b1 * b2) * x), add_add_add_comm]

/-- 3:C2 — the norm-one elements form a group: `N(z₁z₂) = N(z₁)N(z₂) = 1`. -/
theorem norm_one_mul {ν γ1 b1 γ2 b2 : Shell p} (h1 : γ1 * γ1 + -(ν * (b1 * b1)) = 1)
    (h2 : γ2 * γ2 + -(ν * (b2 * b2)) = 1) :
    (γ1 * γ2 + ν * (b1 * b2)) * (γ1 * γ2 + ν * (b1 * b2)) +
      -(ν * ((γ1 * b2 + b1 * γ2) * (γ1 * b2 + b1 * γ2))) = 1 := by
  have := norm_mul ν γ1 b1 γ2 b2
  unfold Q2 at this
  rw [this, h1, h2, one_mul]

/-- 3:C3 — `γ ≠ 0` on every boost of the Lorentzian plane: `γ = 0` would give `ν b² = −1`, i.e.
`ν = (i/b)²`, a square. -/
theorem gamma_ne_zero (F : Frame p κ g) {ν γ b : Shell p} (hν : ¬IsSquare ν) (h : γ * γ + -(ν * (b * b)) = 1) :
    γ ≠ 0 := fun hγ => by
  rw [hγ, mul_zero, zero_add] at h
  have hb : b ≠ 0 := fun hb => by
    rw [hb, mul_zero, mul_zero, neg_zero] at h
    exact F.one_ne_zero h.symm
  have hνb : ν * (b * b) = -1 := by rw [← neg_neg (ν * (b * b)), h]
  match F.exists_inv hb with
  | ⟨s, hs⟩ =>
    exact hν ⟨quarterTurn g κ * s, by
      calc quarterTurn g κ * s * (quarterTurn g κ * s) = (quarterTurn g κ * quarterTurn g κ) * (s * s) := sq_mul _ _
        _ = -1 * (s * s) := by rw [F.quarter_turn_sq]
        _ = (ν * (b * b)) * (s * s) := by rw [hνb]
        _ = ν * ((b * s) * (b * s)) := by rw [mul_assoc, sq_mul b s]
        _ = ν := by rw [hs, one_mul, mul_one]⟩

/-- 3:C3 — the velocity of the boost, `v = −νb/γ` (`vγ = −νb`), satisfies `γ² (ν − v²) = ν`: the finite form of
`γ = 1/√(1 − β²)` with `β² = v²/ν`. -/
theorem gamma_velocity {ν γ b v : Shell p} (hz : γ * γ + -(ν * (b * b)) = 1) (hv : v * γ = -(ν * b)) :
    γ * γ * (ν + -(v * v)) = ν := by
  calc γ * γ * (ν + -(v * v)) = γ * γ * ν + -((v * γ) * (v * γ)) := by
        rw [left_distrib, ← mul_neg, sq_mul v γ, mul_comm (v * v)]
    _ = ν * (γ * γ) + -(ν * (ν * (b * b))) := by
        rw [hv, neg_mul_neg, sq_mul ν b, mul_assoc ν ν (b * b), mul_comm (γ * γ) ν]
    _ = ν * (γ * γ + -(ν * (b * b))) := by rw [left_distrib, ← mul_neg]
    _ = ν := by rw [hz, mul_one]

/-- 3:C3 (the velocity addition law) — for boosts with velocities `v₁, v₂` (`v_i γ_i = −ν b_i`) and the composed
boost's velocity `v₁₂`, `v₁₂ (ν + v₁v₂) = ν (v₁ + v₂)`: Einstein's law `v₁₂ = (v₁ + v₂)/(1 + v₁v₂/ν)`, exact. -/
theorem velocity_addition (F : Frame p κ g) {ν γ1 b1 γ2 b2 v1 v2 v12 : Shell p} (hν : ¬IsSquare ν)
    (hz1 : γ1 * γ1 + -(ν * (b1 * b1)) = 1) (hz2 : γ2 * γ2 + -(ν * (b2 * b2)) = 1)
    (hv1 : v1 * γ1 = -(ν * b1)) (hv2 : v2 * γ2 = -(ν * b2))
    (hv12 : v12 * (γ1 * γ2 + ν * (b1 * b2)) = -(ν * (γ1 * b2 + b1 * γ2))) :
    v12 * (ν + v1 * v2) = ν * (v1 + v2) := by
  have hγ : γ1 * γ2 ≠ 0 := F.mul_ne_zero (gamma_ne_zero F hν hz1) (gamma_ne_zero F hν hz2)
  apply F.mul_left_cancel hγ
  calc γ1 * γ2 * (v12 * (ν + v1 * v2)) = v12 * (γ1 * γ2 * ν + (v1 * γ1) * (v2 * γ2)) := by
        rw [mul_left_comm (γ1 * γ2) v12, left_distrib, mul_mul_mul_comm γ1 γ2 v1 v2, mul_comm γ1 v1, mul_comm γ2 v2]
    _ = v12 * (ν * (γ1 * γ2 + ν * (b1 * b2))) := by
        rw [hv1, hv2, neg_mul_neg, mul_mul_mul_comm ν b1 ν b2, mul_assoc ν ν (b1 * b2), mul_comm (γ1 * γ2) ν,
          ← left_distrib]
    _ = ν * (v12 * (γ1 * γ2 + ν * (b1 * b2))) := mul_left_comm _ _ _
    _ = -(ν * (ν * (γ1 * b2 + b1 * γ2))) := by rw [hv12, ← mul_neg]
    _ = ν * (-(γ2 * (ν * b1)) + -(γ1 * (ν * b2))) := by
        rw [mul_left_comm γ2 ν b1, mul_left_comm γ1 ν b2, ← neg_add_rev, ← left_distrib, mul_comm γ2 b1, ← mul_neg,
          add_comm (b1 * γ2) (γ1 * b2)]
    _ = ν * (γ2 * (v1 * γ1) + γ1 * (v2 * γ2)) := by rw [hv1, hv2, ← mul_neg, ← mul_neg]
    _ = γ1 * γ2 * (ν * (v1 + v2)) := by
        rw [mul_left_comm (γ1 * γ2) ν]
        refine congrArg (ν * ·) ?_
        rw [left_distrib, mul_comm v1 γ1, mul_comm v2 γ2, ← mul_assoc γ2 γ1 v1, mul_comm γ2 γ1, ← mul_assoc γ1 γ2 v2]

/-! ### The counts, decided by the kernel -/

/-- `Σ_{i<n} f i` on naturals. -/
def sumTo (f : Nat → Nat) : Nat → Nat
  | 0 => 0
  | n + 1 => sumTo f n + f n

/-- The number of `(t, x, y, z) ∈ [0, p)⁴` with `−ν t² + x² + y² + z² ≡ 0 (mod p)`. -/
def nullCount (p ν : Nat) : Nat :=
  sumTo (fun t => sumTo (fun x => sumTo (fun y => sumTo (fun z =>
    if (x * x + y * y + z * z + (p - ν) * (t * t)) % p = 0 then 1 else 0) p) p) p) p

/-- The number of `(γ, b) ∈ [0, p)²` with `γ² − ν b² ≡ 1 (mod p)`: the boosts. -/
def normOneCount (p ν : Nat) : Nat :=
  sumTo (fun γ => sumTo (fun b => if (γ * γ + (p - ν) * (b * b)) % p = 1 then 1 else 0) p) p

/-- 3:B4, 3:D1 [value] — the null cone of `Q_2` on `𝔽₁₃` has `2041 = 13³ − 13² + 13` points: the elliptic type. -/
theorem null13 : nullCount 13 2 = 2041 := by decide +kernel
/-- 3:B4 [value] — the Euclidean form (`ν = 1`) on `𝔽₁₃` has `2353 = 13³ + 13² − 13` zeros: the hyperbolic type. -/
theorem euclid13 : nullCount 13 1 = 2353 := by decide +kernel
/-- 3:B4 [value] — `𝔽₅`, `ν = 2`: `105 = 5³ − 5² + 5` null points; `ν = 1`: `145`. -/
theorem null5 : nullCount 5 2 = 105 ∧ nullCount 5 1 = 145 := by decide +kernel
/-- 3:B4 [value] — `𝔽₁₇`, `ν = 3`: `4641 = 17³ − 17² + 17` null points. -/
theorem null17 : nullCount 17 3 = 4641 := by decide +kernel
/-- 3:C2, 3:D1 [value] — the boosts number `p + 1`: `6`, `14`, `18`, `30` on `𝔽₅`, `𝔽₁₃`, `𝔽₁₇`, `𝔽₂₉`. -/
theorem normOne_values : normOneCount 5 2 = 6 ∧ normOneCount 13 2 = 14 ∧ normOneCount 17 3 = 18 ∧
    normOneCount 29 2 = 30 := by decide +kernel

end Frame
end Shell
end FRC

/-! ## The two strata of probability (00:C10; the push of 8 October 2026)

A structural weight is an element of the quadratic extension `𝔽_p[w]/(w² − ν)` (`Ext`); a registered value lies on the
tally line, the elements `a + 0 w`, the part fixed by the extension's conjugation. The paper's two-way subring is the
part of the cyclotomic ring fixed by `ζ ↦ ζ⁻¹`: for `ℤ[i]` it is the tally line (`ν = −1`), and for `ν = 2` it holds
`w = √2 = ζ₈ + ζ₈⁻¹` itself (`root_two_two_way`), so the engineered-core weights `2 ± w` are two-way, and `w ↦ −w` is
the conjugate-pair involution `W₊ ↔ W₋`. The two reductions that join the strata on the stationary core-valued sector
(22-quantum, Rem. strata; the witness `22:stratum.py`, S9 and S10): the conjugate-pair trace tally,
`z^k z̄^(k+m) + z̄^k z^(k+m) = N(z)^k · tr(z^m)`, core-valued for every weight `z`, with the trace sequence's
recurrence `t_{m+2} + N(z) t_m = tr(z) t_{m+1}` and the dial-shift conjugation `w₊(M − θ) = w₋(θ)`; and the
dial-ensemble Parseval tally, `Σ_θ w±(θ) = Σ_θ w₊ w₋ = 2N` over a dial of `N` settings closed under `ζ`, the cross
terms cancelling by the character sums. The engineered-core weights `W± = 2 ± w`, `w² = 2`, have `W₊ + W₋ = 4` and
`W₊ W₋ = 2`, on `Ω = 641` as residues (S2, S4); the framed readout's instances are decided by the kernel (S5–S7): a
readout computation over the naturals of the laboratory host in which the paper's Carrier `Ω = 641` is observed, as
decision Q20 allows, not a count of the totality. The frame supplies the odd prime where one is needed. -/

namespace FRC.Extension

open FRC.Shell

section strata
variable {p : Nat} [Pos p] {ν : Shell p} {κ : Nat} {g : Shell p}

theorem lit_add (a b : Nat) : (ofNat a : Shell p) + ofNat b = ofNat (a + b) :=
  Shell.ext (show (a % p + b % p) % p = (a + b) % p from (FRC.Nat.add_mod a b p Pos.pos).symm)

theorem two_eq : (2 : Shell p) = 1 + 1 := (lit_add 1 1).symm

theorem ext_add_comm (z z' : Ext p ν) : z + z' = z' + z :=
  Ext.ext (Shell.add_comm z.re z'.re) (Shell.add_comm z.im z'.im)

theorem ext_mul_add (u a b : Ext p ν) : u * (a + b) = u * a + u * b :=
  Ext.ext (Shell.Frame.RE.sound (Shell.Frame.look [ν, u.re, u.im, a.re, a.im, b.re, b.im])
      (.add (.mul (.var 1) (.add (.var 3) (.var 5))) (.mul (.var 0) (.mul (.var 2) (.add (.var 4) (.var 6)))))
      (.add (.add (.mul (.var 1) (.var 3)) (.mul (.var 0) (.mul (.var 2) (.var 4)))) (.add (.mul (.var 1) (.var 5)) (.mul (.var 0) (.mul (.var 2) (.var 6)))))
      (by decide +kernel))
    (Shell.Frame.RE.sound (Shell.Frame.look [ν, u.re, u.im, a.re, a.im, b.re, b.im])
      (.add (.mul (.var 1) (.add (.var 4) (.var 6))) (.mul (.var 2) (.add (.var 3) (.var 5))))
      (.add (.add (.mul (.var 1) (.var 4)) (.mul (.var 2) (.var 3))) (.add (.mul (.var 1) (.var 6)) (.mul (.var 2) (.var 5))))
      (by decide +kernel))

theorem ext_conj_one : Ext.conj (1 : Ext p ν) = 1 := Ext.ext rfl Shell.neg_zero

/-- The symmetrised weight is core-valued: `z + z̄ = tr(z)` on the tally line. -/
theorem ext_tally_line (u : Ext p ν) : u + Ext.conj u = Ext.ofShell (Ext.trace u) := Ext.ext rfl (Shell.add_neg u.im)

theorem ext_conj_pow (z : Ext p ν) : ∀ n : Nat, Ext.conj (z ^ n) = Ext.conj z ^ n
  | 0 => ext_conj_one
  | n + 1 => by show Ext.conj (z ^ n * z) = Ext.conj z ^ n * Ext.conj z; rw [Ext.conj_mul, ext_conj_pow z n]

theorem ext_mul_pow (z z' : Ext p ν) : ∀ n : Nat, (z * z') ^ n = z ^ n * z' ^ n
  | 0 => (Ext.mul_one 1).symm
  | n + 1 => by
    show (z * z') ^ n * (z * z') = z ^ n * z * (z' ^ n * z')
    rw [ext_mul_pow z z' n, Ext.mul_assoc, ← Ext.mul_assoc (z' ^ n), Ext.mul_comm (z' ^ n) z, Ext.mul_assoc (z ^ n),
      Ext.mul_assoc z]

theorem ext_ofShell_pow (c : Shell p) : ∀ n : Nat, (Ext.ofShell c : Ext p ν) ^ n = Ext.ofShell (c ^ n)
  | 0 => rfl
  | n + 1 => by
    show (Ext.ofShell c : Ext p ν) ^ n * Ext.ofShell c = Ext.ofShell (c ^ n * c)
    rw [ext_ofShell_pow c n, Ext.ofShell_mul]

theorem ext_trace_add (u v : Ext p ν) : Ext.trace (u + v) = Ext.trace u + Ext.trace v :=
  Shell.add_add_add_comm u.re v.re u.re v.re

theorem ext_trace_smul (c : Shell p) (u : Ext p ν) : Ext.trace (Ext.ofShell c * u) = c * Ext.trace u :=
  Shell.Frame.RE.sound (Shell.Frame.look [ν, c, u.re, u.im])
    (.add (.add (.mul (.var 1) (.var 2)) (.mul (.var 0) (.mul .zero (.var 3)))) (.add (.mul (.var 1) (.var 2)) (.mul (.var 0) (.mul .zero (.var 3)))))
    (.mul (.var 1) (.add (.var 2) (.var 2)))
    (by decide +kernel)

/-- Cayley–Hamilton in the extension: `z² + N(z) = tr(z) z`. -/
theorem ext_cayley_hamilton (z : Ext p ν) : z * z + Ext.ofShell (Ext.norm z) = Ext.ofShell (Ext.trace z) * z :=
  Ext.ext (Shell.Frame.RE.sound (Shell.Frame.look [ν, z.re, z.im])
      (.add (.add (.mul (.var 1) (.var 1)) (.mul (.var 0) (.mul (.var 2) (.var 2)))) (.add (.mul (.var 1) (.var 1)) (.neg (.mul (.var 0) (.mul (.var 2) (.var 2))))))
      (.add (.mul (.add (.var 1) (.var 1)) (.var 1)) (.mul (.var 0) (.mul .zero (.var 2))))
      (by decide +kernel))
    (Shell.Frame.RE.sound (Shell.Frame.look [ν, z.re, z.im])
      (.add (.add (.mul (.var 1) (.var 2)) (.mul (.var 2) (.var 1))) .zero)
      (.add (.mul (.add (.var 1) (.var 1)) (.var 2)) (.mul .zero (.var 1)))
      (by decide +kernel))

/-- 00:C10 (S1) — the part of the extension fixed by its conjugation is the tally line: a weight `z` is its own
conjugate exactly when its `w`-component vanishes (the frame's odd prime), and the symmetrised weight `z + z̄` is the
tally-line element `tr(z)`. For `ℤ[i]`, `ν = −1`, this is the paper's two-way subring. -/
theorem two_way_tally (F : Frame p κ g) (z : Ext p ν) :
    (Ext.conj z = z ↔ z.im = 0) ∧ z + Ext.conj z = Ext.ofShell (Ext.trace z) :=
  ⟨⟨fun h => F.eq_zero_of_eq_neg (Ext.im_congr h).symm, fun h => Ext.ext rfl (by show -z.im = z.im; rw [h, Shell.neg_zero])⟩,
    ext_tally_line z⟩

/-- The engineered-core weight `W₊ = 2 + w` in `𝔽_p[w]/(w² − 2)`; `W₋ = W̄₊ = 2 − w`. -/
def Wp : Ext p 2 := ⟨2, 1⟩

/-- 00:C10 (S2, S4) — the engineered-core weights reduce to the core: `W₊ + W₋ = 4` and `W₊ W₋ = 2` in every
`𝔽_p[w]/(w² − 2)`, and on `Ω = 641` (`641 ≡ 1 (mod 8)`) as residues, `r = 67`, `r² = 2`, `W± = 2 ± r`, with `r` a
grid point of the Subject chart of generator `3`, `r = 3⁵⁵⁵` (S4). -/
theorem core_weights :
    ((Wp : Ext p 2) + Ext.conj Wp = Ext.ofShell 4 ∧ (Wp : Ext p 2) * Ext.conj Wp = Ext.ofShell 2 ∧
      Ext.trace (Wp : Ext p 2) = 4 ∧ Ext.norm (Wp : Ext p 2) = 2) ∧
    (641 % 8 = 1 ∧ (67 : Shell 641) * 67 = 2 ∧ (2 + 67 : Shell 641) + (2 + -67) = 4 ∧
      (2 + 67 : Shell 641) * (2 + -67) = 2 ∧ (3 : Shell 641) ^ 555 = 67) := by
  have hn : Ext.norm (Wp : Ext p 2) = 2 := by
    show (2 : Shell p) * 2 + -(2 * (1 * 1)) = 2
    have h4 : (2 : Shell p) * 2 = 2 + 2 := by rw [two_eq, Shell.right_distrib, Shell.one_mul]
    rw [Shell.one_mul, Shell.mul_one, h4, Shell.add_assoc, Shell.add_neg, Shell.add_zero]
  refine ⟨⟨Ext.ext (lit_add 2 2) (Shell.add_neg 1), by rw [Ext.mul_conj, hn], lit_add 2 2, hn⟩, by decide,
    by decide +kernel, by decide +kernel, by decide +kernel, by decide +kernel⟩

/-- 00:C10 (S2) — the two-way root of two: on a frame, for `ζ` of order `8` (`ζ⁸ = 1`, `ζ⁴ ≠ 1`) and `η = ζ⁻¹`,
`(ζ + η)² = 2`. So `w = ζ₈ + ζ₈⁻¹` lies in the paper's two-way subring, the part of the cyclotomic ring fixed by
`ζ ↦ ζ⁻¹`, and the engineered-core weights `2 ± w` are two-way (on `641`: `ζ₈ = 318`, `ζ₈ + ζ₈⁻¹ = 574 = −67`). -/
theorem root_two_two_way (F : Frame p κ g) {ζ η : Shell p} (h8 : ζ ^ 8 = 1) (h4 : ζ ^ 4 ≠ 1) (hζη : ζ * η = 1) :
    (ζ + η) * (ζ + η) = 2 := by
  have hsq : ζ ^ 4 * ζ ^ 4 = 1 := by rw [← pow_add]; exact h8
  have hm1 : ζ ^ 4 = -1 := match F.sq_eq_one hsq with
    | .inl h => absurd h h4
    | .inr h => h
  have h22 : ζ ^ 2 * ζ ^ 2 = -1 := by rw [← pow_add]; exact hm1
  have hη2 : ζ ^ 2 * η ^ 2 = 1 := by rw [← mul_pow, hζη, one_pow]
  have hzero : ζ ^ 2 + η ^ 2 = 0 := by
    calc ζ ^ 2 + η ^ 2 = η ^ 2 * (ζ ^ 2 * ζ ^ 2) + η ^ 2 := by
          rw [← mul_assoc, mul_comm (η ^ 2) (ζ ^ 2), hη2, one_mul]
      _ = η ^ 2 * -1 + η ^ 2 := by rw [h22]
      _ = 0 := by rw [← mul_neg, mul_one, neg_add]
  rw [right_distrib, left_distrib, left_distrib, hζη, mul_comm η ζ, hζη, add_comm 1 (η * η), add_add_add_comm,
    ← pow_two ζ, ← pow_two η, hzero, zero_add]
  exact two_eq.symm

/-- 00:C10 (S9) — the conjugate-pair trace tally: a flip-summed pair of conjugate string weights is core-valued,
`z^k z̄^(k+m) + z̄^k z^(k+m) = N(z)^k · tr(z^m)` on the tally line, for every weight `z` of every quadratic extension. -/
theorem conjugate_pair_tally (z : Ext p ν) (k m : Nat) :
    z ^ k * Ext.conj z ^ (k + m) + Ext.conj z ^ k * z ^ (k + m) = Ext.ofShell (Ext.norm z ^ k * Ext.trace (z ^ m)) := by
  rw [Ext.pow_add, Ext.pow_add, ← Ext.mul_assoc, ← Ext.mul_assoc, ← ext_mul_pow, ← ext_mul_pow, Ext.mul_conj,
    Ext.mul_comm (Ext.conj z) z, Ext.mul_conj, ext_ofShell_pow, ← ext_mul_add, ← ext_conj_pow, ext_add_comm,
    ext_tally_line (z ^ m), Ext.ofShell_mul]

/-- 00:C10 (S9) — the trace sequence `t_m = tr(z^m)` obeys `t_{m+2} + N(z) t_m = tr(z) t_{m+1}`; for `W₊` (`tr = 4`,
`N = 2`): `t_0 = 2`, `t_1 = 4`, `t_{m+2} = 4 t_{m+1} − 2 t_m`, so `t_2 = 12`, `t_3 = 40` (on `Ω = 641`). -/
theorem trace_recurrence :
    (∀ (z : Ext p ν) (m : Nat), Ext.trace (z ^ (m + 2)) + Ext.norm z * Ext.trace (z ^ m) = Ext.trace z * Ext.trace (z ^ (m + 1))) ∧
    (Ext.trace ((Wp : Ext p 2) ^ 0) = 2 ∧ Ext.trace ((Wp : Ext p 2) ^ 1) = 4) ∧
    (Ext.trace ((Wp : Ext 641 2) ^ 2) = 12 ∧ Ext.trace ((Wp : Ext 641 2) ^ 3) = 40) := by
  refine ⟨fun z m => ?_, ⟨lit_add 1 1, by show Ext.trace (1 * Wp) = 4; rw [Ext.one_mul]; exact lit_add 2 2⟩,
    by decide +kernel, by decide +kernel⟩
  have h : z ^ (m + 2) + Ext.ofShell (Ext.norm z) * z ^ m = Ext.ofShell (Ext.trace z) * z ^ (m + 1) := by
    calc z ^ (m + 2) + Ext.ofShell (Ext.norm z) * z ^ m
        = z ^ m * (z * z) + z ^ m * Ext.ofShell (Ext.norm z) := by
          rw [Ext.mul_comm (Ext.ofShell _)]; show z ^ m * z * z + _ = _; rw [Ext.mul_assoc]
      _ = z ^ m * (z * z + Ext.ofShell (Ext.norm z)) := (ext_mul_add _ _ _).symm
      _ = z ^ m * (Ext.ofShell (Ext.trace z) * z) := by rw [ext_cayley_hamilton]
      _ = Ext.ofShell (Ext.trace z) * z ^ (m + 1) := by
          show z ^ m * (Ext.ofShell (Ext.trace z) * z) = Ext.ofShell (Ext.trace z) * (z ^ m * z)
          rw [← Ext.mul_assoc, Ext.mul_comm (z ^ m), Ext.mul_assoc]
  have := congrArg Ext.trace h
  rw [ext_trace_add, ext_trace_smul, ext_trace_smul] at this
  exact this

theorem geom_sum_zero (F : Frame p κ g) {x : Shell p} (n : Nat) (hn : x ^ n = 1) (hx : x ≠ 1) :
    sumRange (fun l => x ^ l) n = 0 := by
  have hg := geom_sum_mul x n
  rw [hn, add_neg] at hg
  match F.mul_eq_zero hg with
  | .inl h => exact h
  | .inr h => exact absurd (by
      calc x = x + 0 := (add_zero x).symm
        _ = x + (-1 + 1) := by rw [neg_add]
        _ = (x + -1) + 1 := (add_assoc _ _ _).symm
        _ = 1 := by rw [h, zero_add]) hx

/-- 00:C10 (S9) — the dial-shift conjugation: on a dial of `2M` settings (`ζ^(2M) = 1`, `ζ^M ≠ 1`, `η = ζ⁻¹`), the
weight at the shifted setting is the conjugate weight, `w₊(M − θ) = w₋(θ)` for `θ ≤ M` (the witness: `M = 40` in
`ℤ[x]/(x⁴⁰ + 1)`, `w₊(40 − D) = w₋(D)`). -/
theorem dial_shift (F : Frame p κ g) {ζ η : Shell p} (M : Nat) (h2M : ζ ^ (2 * M) = 1) (hM : ζ ^ M ≠ 1)
    (hζη : ζ * η = 1) (θ : Nat) (hθ : θ ≤ M) :
    2 + (ζ ^ (M - θ) + η ^ (M - θ)) = 2 + -(ζ ^ θ + η ^ θ) := by
  have hsq : ζ ^ M * ζ ^ M = 1 := by rw [← pow_add, ← Nat.two_mul]; exact h2M
  have hζM : ζ ^ M = -1 := match F.sq_eq_one hsq with
    | .inl h => absurd h hM
    | .inr h => h
  have hηM : η ^ M = -1 := by
    have h1 : ζ ^ M * η ^ M = 1 := by rw [← mul_pow, hζη, one_pow]
    rw [hζM] at h1
    calc η ^ M = -(-1 * η ^ M) := by rw [neg_mul, neg_neg, one_mul]
      _ = -1 := by rw [h1]
  have hθη : ζ ^ θ * η ^ θ = 1 := by rw [← mul_pow, hζη, one_pow]
  have e1 : ζ ^ (M - θ) = -(η ^ θ) := by
    calc ζ ^ (M - θ) = ζ ^ (M - θ) * (ζ ^ θ * η ^ θ) := by rw [hθη, mul_one]
      _ = ζ ^ M * η ^ θ := by rw [← mul_assoc, ← pow_add, FRC.Nat.sub_add_cancel hθ]
      _ = -(η ^ θ) := by rw [hζM, neg_one_mul]
  have e2 : η ^ (M - θ) = -(ζ ^ θ) := by
    calc η ^ (M - θ) = η ^ (M - θ) * (η ^ θ * ζ ^ θ) := by rw [mul_comm (η ^ θ), hθη, mul_one]
      _ = η ^ M * ζ ^ θ := by rw [← mul_assoc, ← pow_add, FRC.Nat.sub_add_cancel hθ]
      _ = -(ζ ^ θ) := by rw [hηM, neg_one_mul]
  rw [e1, e2, neg_add_rev, add_comm (-(ζ ^ θ))]

/-- 00:C10 (S10) — the dial-ensemble Parseval tally: over a dial of `N` settings closed under `ζ` (`ζ^N = 1`,
`ζ² ≠ 1`, `η = ζ⁻¹`) on a frame, the weights `w±(θ) = 2 ± (ζ^θ + η^θ)` sum to `2N`, and so do the products
`w₊(θ) w₋(θ)`: the cross terms cancel by the character sums (the frame: no zero divisors). -/
theorem dial_tally (F : Frame p κ g) {ζ η : Shell p} (N : Nat) (hN : ζ ^ N = 1) (hζη : ζ * η = 1) (h2 : ζ * ζ ≠ 1) :
    sumRange (fun θ => 2 + (ζ ^ θ + η ^ θ)) N = ofNat N * 2 ∧
    sumRange (fun θ => 2 + -(ζ ^ θ + η ^ θ)) N = ofNat N * 2 ∧
    sumRange (fun θ => (2 + (ζ ^ θ + η ^ θ)) * (2 + -(ζ ^ θ + η ^ θ))) N = ofNat N * 2 := by
  have hζ1 : ζ ≠ 1 := fun h => h2 (by rw [h, Shell.one_mul])
  have hηN : η ^ N = 1 := by
    have : (ζ * η) ^ N = 1 := by rw [hζη, one_pow]
    rw [mul_pow, hN, Shell.one_mul] at this; exact this
  have hη1 : η ≠ 1 := fun h => hζ1 (calc ζ = ζ * 1 := (Shell.mul_one ζ).symm
    _ = ζ * η := by rw [h]
    _ = 1 := hζη)
  have hζ2N : (ζ * ζ) ^ N = 1 := by rw [mul_pow, hN, Shell.one_mul]
  have hη2N : (η * η) ^ N = 1 := by rw [mul_pow, hηN, Shell.one_mul]
  have hη2 : η * η ≠ 1 := fun h => h2 (by
    calc ζ * ζ = ζ * ζ * (η * η) := by rw [h, Shell.mul_one]
      _ = (ζ * η) * (ζ * η) := Shell.Frame.RE.sound (Shell.Frame.look [ζ, η])
            (.mul (.mul (.var 0) (.var 0)) (.mul (.var 1) (.var 1))) (.mul (.mul (.var 0) (.var 1)) (.mul (.var 0) (.var 1)))
            (by decide +kernel)
      _ = 1 := by rw [hζη, Shell.mul_one])
  have gζ := geom_sum_zero F N hN hζ1
  have gη := geom_sum_zero F N hηN hη1
  have gζ2 := geom_sum_zero F N hζ2N h2
  have gη2 := geom_sum_zero F N hη2N hη2
  have term : ∀ θ, θ < N → (2 + (ζ ^ θ + η ^ θ)) * (2 + -(ζ ^ θ + η ^ θ)) = 2 + -((ζ * ζ) ^ θ + (η * η) ^ θ) := by
    intro θ _
    have hab : ζ ^ θ * η ^ θ = 1 := by rw [← mul_pow, hζη, one_pow]
    rw [mul_pow, mul_pow, two_eq]
    calc (1 + 1 + (ζ ^ θ + η ^ θ)) * (1 + 1 + -(ζ ^ θ + η ^ θ))
        = (1 + 1 + -(ζ ^ θ * ζ ^ θ + η ^ θ * η ^ θ)) + (1 + 1 + -(ζ ^ θ * η ^ θ + ζ ^ θ * η ^ θ)) :=
          Shell.Frame.RE.sound (Shell.Frame.look [ζ ^ θ, η ^ θ])
            (.mul (.add (.add .one .one) (.add (.var 0) (.var 1))) (.add (.add .one .one) (.neg (.add (.var 0) (.var 1)))))
            (.add (.add (.add .one .one) (.neg (.add (.mul (.var 0) (.var 0)) (.mul (.var 1) (.var 1)))))
              (.add (.add .one .one) (.neg (.add (.mul (.var 0) (.var 1)) (.mul (.var 0) (.var 1))))))
            (by decide +kernel)
      _ = 1 + 1 + -(ζ ^ θ * ζ ^ θ + η ^ θ * η ^ θ) := by rw [hab, add_neg, add_zero]
  refine ⟨?_, ?_, ?_⟩
  · rw [sum_add (fun _ => (2 : Shell p)) (fun θ => ζ ^ θ + η ^ θ) N, sum_const, sum_add (fun θ => ζ ^ θ) (fun θ => η ^ θ) N,
      gζ, gη, add_zero, add_zero]
  · rw [sum_add (fun _ => (2 : Shell p)) (fun θ => -(ζ ^ θ + η ^ θ)) N, sum_const, sum_neg (fun θ => ζ ^ θ + η ^ θ) N,
      sum_add (fun θ => ζ ^ θ) (fun θ => η ^ θ) N, gζ, gη, add_zero, neg_zero, add_zero]
  · rw [sum_congr N term, sum_add (fun _ => (2 : Shell p)) (fun θ => -((ζ * ζ) ^ θ + (η * η) ^ θ)) N, sum_const,
      sum_neg (fun θ => (ζ * ζ) ^ θ + (η * η) ^ θ) N, sum_add (fun θ => (ζ * ζ) ^ θ) (fun θ => (η * η) ^ θ) N,
      gζ2, gη2, add_zero, neg_zero, add_zero]

/-- The framed grid points `s_n = ⌊√(2 · 9ⁿ)⌋`, `n ≤ 8`, of the Subject chart with generator `g = 3`. -/
def gridPoint : Nat → Nat
  | 0 => 1 | 1 => 4 | 2 => 12 | 3 => 38 | 4 => 114 | 5 => 343 | 6 => 1030 | 7 => 3092 | 8 => 9278 | _ => 0

/-- The `i`-th entry of a list of naturals, `0` past its end (the core's `getD` carries `propext`). -/
def nth : List Nat → Nat → Nat
  | [], _ => 0
  | x :: _, 0 => x
  | _ :: xs, i + 1 => nth xs i

/-- The rank of the `i`-th remainder among `rems`: the number of remainders that precede it, the larger first and, at a
tie, the earlier index. -/
def remainderRank (rems : List Nat) (i : Nat) : Nat := go 0 rems
where
  go : Nat → List Nat → Nat
    | _, [] => 0
    | j, r :: rs => (if r > nth rems i ∨ (r = nth rems i ∧ j < i) then 1 else 0) + go (j + 1) rs

/-- The largest-remainder allocation of `B` counts to the probabilities `nums / den`: each takes its floor, and the
seats left go one each to the largest remainders, ties by index. -/
def largestRemainder (B den : Nat) (nums : List Nat) : List Nat :=
  let floors := nums.map (fun n => B * n / den)
  let rems := nums.map (fun n => B * n % den)
  let seats := B - floors.foldl (· + ·) 0
  (List.range nums.length).map (fun i => nth floors i + if remainderRank rems i < seats then 1 else 0)

/-- 00:C10 (S5–S7) — a registered probability is a framed rational, decided by the kernel: the grid bound
`s_n² ≤ 2 · 9ⁿ < (s_n + 1)²` at every scale `n ≤ 8` and the readouts nest, `3 s_n ≤ s_{n+1} ≤ 3 s_n + 2`; the readout
`R_4((2 + √2)/8) = (2 · 3⁴ + 114)/(8 · 3⁴) = 23/54`; the `√3` instance `s_3 = 46`; the largest-remainder allocation at
`B = 81` of `(23/54, 23/54, 4/54, 4/54)` is `35 + 34 + 6 + 6` (the floors `34 + 34 + 6 + 6`, the one seat left to the
first of the two remainders `27/54`). A readout computation over the naturals of the laboratory host (decision Q20). -/
theorem framed_readout :
    (∀ n, n < 9 → gridPoint n * gridPoint n ≤ 2 * 9 ^ n ∧ 2 * 9 ^ n < (gridPoint n + 1) * (gridPoint n + 1)) ∧
    (∀ n, n < 8 → 3 * gridPoint n ≤ gridPoint (n + 1) ∧ gridPoint (n + 1) ≤ 3 * gridPoint n + 2) ∧
    (2 * 3 ^ 4 + gridPoint 4) * 54 = 23 * (8 * 3 ^ 4) ∧ (46 * 46 ≤ 3 * 3 ^ 6 ∧ 3 * 3 ^ 6 < 47 * 47) ∧
    (23 + 23 + 4 + 4 = 54 ∧ largestRemainder 81 54 [23, 23, 4, 4] = [35, 34, 6, 6]) := by
  refine ⟨by decide, by decide, by decide, by decide, by decide⟩

end strata

end FRC.Extension
