import FrcCore.Orbit

/-!
# FrcCore.Causality — the Euclidean–Lorentzian dichotomy on the shell (3-causality)

The square classes of the shell, the diagonal form `Q_ν = −ν t² + x² + y² + z²`, and the boosts of its `(t, x)`
plane, from first principles.  3:B2: a nonsquare `ν` has no root, and with `c ≠ 0` the coefficient `−c²` is a square
(`−1 = i²`).  3:B3: the absorption of a common square class by rescaling.  3:B5: `x² − ν t²` is anisotropic for a
nonsquare `ν` (the Witt kernel of the Lorentzian form), while `y² + z²` and `x² − w² t²` are hyperbolic planes.
3:C2, C3: the boost `Λ(γ, b) = [[γ, b], [νb, γ]]` with `γ² − νb² = 1` preserves `x² − ν t²` (the norm of `K = F_p(√ν)`
is multiplicative), boosts compose as norm-one elements multiply, `γ` is never zero, and the velocities
`v = −νb/γ` obey the Einstein addition law exactly.  The counts — the null cone `p³ − p² + p` on the Lorentzian form,
`p³ + p² − p` on the Euclidean one, `p + 1` boosts — are decided by the kernel on `𝔽₅`, `𝔽₁₃`, `𝔽₁₇`.  No axioms.
-/

namespace FRC
namespace Shell
namespace Frame

variable {p : Nat} [Pos p] {κ : Nat} {g : Shell p}

/-- `x` is a square: `x = y·y` for some residue `y`. -/
def IsSquare (x : Shell p) : Prop := ∃ y : Shell p, y * y = x

/-- 3:B2 (Thm. nonexistence, first clause) — `c² = ν` makes `ν` a square, so a nonsquare `ν` has no root `c`. -/
theorem no_causal_root {ν : Shell p} (h : ¬IsSquare ν) (c : Shell p) : c * c ≠ ν := fun e => h ⟨c, e⟩

theorem mul_mul_mul_comm (a b c d : Shell p) : (a * b) * (c * d) = (a * c) * (b * d) := by
  rw [mul_assoc, mul_left_comm b, ← mul_assoc]

theorem sq_mul (a b : Shell p) : (a * b) * (a * b) = (a * a) * (b * b) := mul_mul_mul_comm a b a b

/-- 3:B2 (Thm. nonexistence, the consequence) — `−c²` is a square on every shell: `−c² = (i·c)²` with `i² = −1`;
so with `c ≠ 0` every coefficient of `−c² t² + x² + y² + z²` is a square and the form is Euclidean. -/
theorem neg_sq_is_square (F : Frame p κ g) (c : Shell p) : IsSquare (-(c * c)) :=
  ⟨quarterTurn g κ * c, by rw [sq_mul, F.quarter_turn_sq, neg_one_mul]⟩

/-- 3:B2 — `−1` itself is a square (`i²`): the paper's hypothesis `p ≡ 1 (mod 4)` in the shell's own terms. -/
theorem neg_one_is_square (F : Frame p κ g) : IsSquare (-1 : Shell p) := ⟨quarterTurn g κ, F.quarter_turn_sq⟩

/-- 3:B3 (Lemma absorption, repaired) — if `a_i = w_i² a_0` for `i = 1, 2, 3` then
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
def boostT (ν γ b t x : Shell p) : Shell p := γ * t + b * x
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
