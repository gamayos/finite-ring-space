import FrcCore.Theme.Framed
import FrcCore.Theme.Extension

/-!
# FrcCore.Theme.Quaternion — rotations in the window (the algebra theme)

1-algebra's framed quaternions and their rotations (6 November 2026), moved here from the paper module
`FrcCore/Quaternion.lean`, every name unchanged, and completed in the core. The revision of 1-algebra of the same day
moved the rotations out of that paper's ledger; they wait for a paper of their own:

* the framed quaternions compose exactly: with coordinates in the window `H` and a shell `p > 8H²` the product
  lies in the window `4H²` and the shell reading determines it (`quaternion_window`, `read_mul`);
* one axis: the rotation `x ↦ q x q̄ / N(q)` is the Cayley step of `S_v` (`rot_cayley`, `cayley_inj`), the
  half-turn at `a = 0` (`half_turn`), with kernel the scalars (`rot_trivial`) and `ρ_{−q} = ρ_q` (`rot_neg`); a quaternion
  `a + tv` with `a ≠ 0` is the scalar `a` times `1 + sv`, `s = t/a` (`axis_param`, `rot_smul`), distinct parameters
  give distinct rotations (`axis_inj`) and none of them is the half-turn (`axis_half`), and the parameter `s` fails exactly where `s² = −N(v)⁻¹`
  (`axis_exceptional`), at two values `±x` when `N(v)` is a square and at none otherwise (`neg_inv_square_iff`,
  `root_pair`); the window pairs `±(a, t)`, `|a|, |t| ≤ H`, number `2H² + 2H` (`box_count`);
* two axes: `(1 + u)(1 + w) = (1 − u·w) + (u + w + u × w)` (`one_add_mul`), the composition law (`compose`), the
  half-turn case (`one_add_mul_half`), the bracket (`bracket`), and the multiplicative norm (`nrm_mul`, `rot_mul`).

No axioms.
-/

namespace FRC
namespace Shell
namespace Frame

variable {p : Nat} [Pos p]


/-- A framed quaternion with signed window coordinates. -/
structure IQuat where
  a : SInt
  b : SInt
  c : SInt
  d : SInt

/-- The Hamilton product on the window pairs, the same formula. -/
def IQuat.mul (q r : IQuat) : IQuat :=
  ⟨sadd (sadd (smul q.a r.a) (sneg (smul q.b r.b))) (sadd (sneg (smul q.c r.c)) (sneg (smul q.d r.d))),
   sadd (sadd (smul q.a r.b) (smul q.b r.a)) (sadd (smul q.c r.d) (sneg (smul q.d r.c))),
   sadd (sadd (smul q.a r.c) (sneg (smul q.b r.d))) (sadd (smul q.c r.a) (smul q.d r.b)),
   sadd (sadd (smul q.a r.d) (smul q.b r.c)) (sadd (sneg (smul q.c r.b)) (smul q.d r.a))⟩

def IQuat.read (q : IQuat) : Quat p := ⟨sread q.a, sread q.b, sread q.c, sread q.d⟩
def IQuat.norm (q : IQuat) : IQuat := ⟨snorm q.a, snorm q.b, snorm q.c, snorm q.d⟩
def QBound (H : Nat) (q : IQuat) : Prop := SBound H q.a ∧ SBound H q.b ∧ SBound H q.c ∧ SBound H q.d

theorem IQuat.ext' {q r : IQuat} (ha : q.a = r.a) (hb : q.b = r.b) (hc : q.c = r.c) (hd : q.d = r.d) : q = r := by
  cases q; cases r; cases ha; cases hb; cases hc; cases hd; rfl

/-- Exact composition — the reading of the integer product is the product of the readings. -/
theorem read_mul (q r : IQuat) : ((IQuat.mul q r).read : Quat p) = Quat.mul q.read r.read := by
  unfold IQuat.mul IQuat.read Quat.mul
  rw [sread_add, sread_add, sread_add, sread_add, sread_add, sread_add, sread_add, sread_add, sread_add,
    sread_add, sread_add, sread_add, sread_neg, sread_neg, sread_neg, sread_neg, sread_neg, sread_neg,
    sread_mul, sread_mul, sread_mul, sread_mul, sread_mul, sread_mul, sread_mul, sread_mul, sread_mul,
    sread_mul, sread_mul, sread_mul, sread_mul, sread_mul, sread_mul, sread_mul]

theorem read_norm (q : IQuat) : (q.norm.read : Quat p) = q.read := by
  unfold IQuat.norm IQuat.read
  rw [sread_norm, sread_norm, sread_norm, sread_norm]

theorem norm_bound {H : Nat} {q r : IQuat} (hq : QBound H q) (hr : QBound H r) :
    QBound (4 * (H * H)) (IQuat.mul q r).norm := by
  have m := fun {x y : SInt} (hx : SBound H x) (hy : SBound H y) => smul_bound hx hy
  refine ⟨?_, ?_, ?_, ?_⟩
  · have := sum4_bound (m hq.1 hr.1) (sneg_bound (m hq.2.1 hr.2.1)) (sneg_bound (m hq.2.2.1 hr.2.2.1))
      (sneg_bound (m hq.2.2.2 hr.2.2.2))
    exact snorm_bound this.1 this.2
  · have := sum4_bound (m hq.1 hr.2.1) (m hq.2.1 hr.1) (m hq.2.2.1 hr.2.2.2) (sneg_bound (m hq.2.2.2 hr.2.2.1))
    exact snorm_bound this.1 this.2
  · have := sum4_bound (m hq.1 hr.2.2.1) (sneg_bound (m hq.2.1 hr.2.2.2)) (m hq.2.2.1 hr.1) (m hq.2.2.2 hr.2.1)
    exact snorm_bound this.1 this.2
  · have := sum4_bound (m hq.1 hr.2.2.2) (m hq.2.1 hr.2.2.1) (sneg_bound (m hq.2.2.1 hr.2.1)) (m hq.2.2.2 hr.1)
    exact snorm_bound this.1 this.2

/-- The finitary clause — framed quaternions with window coordinates `≤ H`, read in a shell `p > 8H²`,
compose exactly: the product of the readings is the reading of the integer product; that product's
coordinates lie in the window `4H²`; and the reading determines it among the window's quaternions. -/
theorem quaternion_window {H : Nat} (hH : 8 * (H * H) < p) {q r : IQuat} (hq : QBound H q) (hr : QBound H r) :
    ((IQuat.mul q r).read : Quat p) = Quat.mul q.read r.read ∧
    QBound (4 * (H * H)) (IQuat.mul q r).norm ∧
    ∀ s : IQuat, QBound (4 * (H * H)) s → (s.read : Quat p) = (IQuat.mul q r).read → s = (IQuat.mul q r).norm := by
  refine ⟨read_mul q r, norm_bound hq hr, ?_⟩
  intro s hs he
  have hn := norm_bound hq hr
  have hM : 2 * (4 * (H * H)) < p := by rw [← Nat.mul_assoc]; exact hH
  rw [← read_norm (IQuat.mul q r)] at he
  unfold IQuat.read at he
  exact IQuat.ext' (sread_inj hM hs.1 hn.1 (congrArg Quat.a he)) (sread_inj hM hs.2.1 hn.2.1 (congrArg Quat.b he))
    (sread_inj hM hs.2.2.1 hn.2.2.1 (congrArg Quat.c he)) (sread_inj hM hs.2.2.2 hn.2.2.2 (congrArg Quat.d he))

/-! ## The Lie-algebra layer, one axis -/

/-- Conjugation keeps a pure quaternion pure: the scalar part of `q x q̄` vanishes. -/
theorem rot_pure (q x : Quat p) (hx : x.a = 0) : (Quat.conjBy q x).a = 0 := by
  rw [Quat.pure_eq hx]
  exact RE.sound (look [q.a, q.b, q.c, q.d, x.b, x.c, x.d]) (QR.conjBy (QR.v 0) (QR.pv 4)).a .zero (by decide +kernel)

/-- The Cayley form cleared of the norm: for `q = a + v` and a pure `x`, the conjugate `y = q x q̄` satisfies
`(aI − S_v) y = N(q) (aI + S_v) x`, where `S_v x = v × x`. -/
theorem rot_cayley (q x : Quat p) (hx : x.a = 0) :
    Quat.add (Quat.smul q.a (Quat.conjBy q x)) (Quat.neg (Quat.cross (Quat.vec q) (Quat.conjBy q x))) =
      Quat.smul (Quat.nrm q) (Quat.add (Quat.smul q.a x) (Quat.cross (Quat.vec q) x)) := by
  rw [Quat.pure_eq hx]
  exact QR.sound (look [q.a, q.b, q.c, q.d, x.b, x.c, x.d])
    (QR.add (QR.smul (.var 0) (QR.conjBy (QR.v 0) (QR.pv 4))) (QR.neg (QR.cross (QR.vec (QR.v 0)) (QR.conjBy (QR.v 0) (QR.pv 4)))))
    (QR.smul (QR.nrm (QR.v 0)) (QR.add (QR.smul (.var 0) (QR.pv 4)) (QR.cross (QR.vec (QR.v 0)) (QR.pv 4)))) (by decide +kernel)

/-- The half-turn: for pure `v` and `x`, `v x v̄ = N(v) x + 2 v × (v × x)`, so `ρ_v = I + 2N(v)⁻¹ S_v²`. -/
theorem half_turn (v x : Quat p) (hv : v.a = 0) (hx : x.a = 0) :
    Quat.conjBy v x = Quat.add (Quat.smul (Quat.nrm v) x) (Quat.add (Quat.cross v (Quat.cross v x)) (Quat.cross v (Quat.cross v x))) := by
  rw [Quat.pure_eq hv, Quat.pure_eq hx]
  exact QR.sound (look [v.b, v.c, v.d, x.b, x.c, x.d])
    (QR.conjBy (QR.pv 0) (QR.pv 3))
    (QR.add (QR.smul (QR.nrm (QR.pv 0)) (QR.pv 3)) (QR.add (QR.cross (QR.pv 0) (QR.cross (QR.pv 0) (QR.pv 3))) (QR.cross (QR.pv 0) (QR.cross (QR.pv 0) (QR.pv 3))))) (by decide +kernel)

/-- The key identity of uniqueness: with `w = a z − v × z`, `a (a² + N(v)) z = a² w + a (v × w) + (v · w) v`. -/
theorem cayley_key (a : Shell p) (v z : Quat p) (hv : v.a = 0) (hz : z.a = 0) :
    Quat.smul (a * (a * a + Quat.dot v v)) z =
      Quat.add (Quat.add (Quat.smul (a * a) (Quat.add (Quat.smul a z) (Quat.neg (Quat.cross v z))))
        (Quat.smul a (Quat.cross v (Quat.add (Quat.smul a z) (Quat.neg (Quat.cross v z))))))
        (Quat.smul (Quat.dot v (Quat.add (Quat.smul a z) (Quat.neg (Quat.cross v z)))) v) := by
  rw [Quat.pure_eq hv, Quat.pure_eq hz]
  exact QR.sound (look [a, v.b, v.c, v.d, z.b, z.c, z.d])
    (QR.smul (.mul (.var 0) (.add (.mul (.var 0) (.var 0)) (QR.dot (QR.pv 1) (QR.pv 1)))) (QR.pv 4))
    (QR.add (QR.add (QR.smul (.mul (.var 0) (.var 0)) (QR.add (QR.smul (.var 0) (QR.pv 4)) (QR.neg (QR.cross (QR.pv 1) (QR.pv 4)))))
        (QR.smul (.var 0) (QR.cross (QR.pv 1) (QR.add (QR.smul (.var 0) (QR.pv 4)) (QR.neg (QR.cross (QR.pv 1) (QR.pv 4)))))))
      (QR.smul (QR.dot (QR.pv 1) (QR.add (QR.smul (.var 0) (QR.pv 4)) (QR.neg (QR.cross (QR.pv 1) (QR.pv 4))))) (QR.pv 1))) (by decide +kernel)

theorem add_neg_q (q : Quat p) : Quat.add q (Quat.neg q) = ⟨0, 0, 0, 0⟩ :=
  QR.sound (look [q.a, q.b, q.c, q.d]) (QR.add (QR.v 0) (QR.neg (QR.v 0))) ⟨.zero, .zero, .zero, .zero⟩ (by decide +kernel)

theorem key_zero (a : Shell p) (v : Quat p) :
    Quat.add (Quat.add (Quat.smul (a * a) ⟨0, 0, 0, 0⟩) (Quat.smul a (Quat.cross v ⟨0, 0, 0, 0⟩)))
      (Quat.smul (Quat.dot v ⟨0, 0, 0, 0⟩) v) = ⟨0, 0, 0, 0⟩ :=
  QR.sound (look [a, v.a, v.b, v.c, v.d])
    (QR.add (QR.add (QR.smul (.mul (.var 0) (.var 0)) ⟨.zero, .zero, .zero, .zero⟩) (QR.smul (.var 0) (QR.cross (QR.v 1) ⟨.zero, .zero, .zero, .zero⟩)))
      (QR.smul (QR.dot (QR.v 1) ⟨.zero, .zero, .zero, .zero⟩) (QR.v 1))) ⟨.zero, .zero, .zero, .zero⟩ (by decide +kernel)

/-- `aI − S_v` is injective on pure quaternions when `a ≠ 0` and `a² + N(v) ≠ 0` (a field shell). -/
theorem cayley_inj {κ : Nat} {g : Shell p} (F : Frame p κ g) {a : Shell p} {v z : Quat p} (hv : v.a = 0) (hz : z.a = 0)
    (ha : a ≠ 0) (hn : a * a + Quat.dot v v ≠ 0) (h : Quat.smul a z = Quat.cross v z) : z = ⟨0, 0, 0, 0⟩ := by
  have hw : Quat.add (Quat.smul a z) (Quat.neg (Quat.cross v z)) = ⟨0, 0, 0, 0⟩ := by rw [h]; exact add_neg_q _
  have key := cayley_key a v z hv hz
  rw [hw, key_zero] at key
  have hc : a * (a * a + Quat.dot v v) ≠ 0 := fun e =>
    match F.mul_eq_zero e with
    | .inl e1 => ha e1
    | .inr e2 => hn e2
  have comp : ∀ t : Shell p, a * (a * a + Quat.dot v v) * t = 0 → t = 0 := fun t e =>
    match F.mul_eq_zero e with
    | .inl e1 => absurd e1 hc
    | .inr e2 => e2
  exact Quat.ext4 hz (comp _ (congrArg Quat.b key)) (comp _ (congrArg Quat.c key)) (comp _ (congrArg Quat.d key))

/-! ## The Lie-algebra layer, two axes and range -/

/-- The product of two Gibbs quaternions: `(1 + u)(1 + w) = (1 − u·w) + (u + w + u × w)` for pure `u`, `w`. -/
theorem one_add_mul (u w : Quat p) (hu : u.a = 0) (hw : w.a = 0) :
    Quat.mul (Quat.add (Quat.sc 1) u) (Quat.add (Quat.sc 1) w) =
      Quat.add (Quat.sc (1 + -(Quat.dot u w))) (Quat.add (Quat.add u w) (Quat.cross u w)) := by
  rw [Quat.pure_eq hu, Quat.pure_eq hw]
  exact QR.sound (look [u.b, u.c, u.d, w.b, w.c, w.d])
    (QR.mul (QR.add (QR.sc .one) (QR.pv 0)) (QR.add (QR.sc .one) (QR.pv 3)))
    (QR.add (QR.sc (.add .one (.neg (QR.dot (QR.pv 0) (QR.pv 3))))) (QR.add (QR.add (QR.pv 0) (QR.pv 3)) (QR.cross (QR.pv 0) (QR.pv 3)))) (by decide +kernel)

/-- The bracket: `uw − wu = 2 u × w` for pure `u`, `w`. -/
theorem bracket (u w : Quat p) (hu : u.a = 0) (hw : w.a = 0) :
    Quat.add (Quat.mul u w) (Quat.neg (Quat.mul w u)) = Quat.add (Quat.cross u w) (Quat.cross u w) := by
  rw [Quat.pure_eq hu, Quat.pure_eq hw]
  exact QR.sound (look [u.b, u.c, u.d, w.b, w.c, w.d])
    (QR.add (QR.mul (QR.pv 0) (QR.pv 3)) (QR.neg (QR.mul (QR.pv 3) (QR.pv 0)))) (QR.add (QR.cross (QR.pv 0) (QR.pv 3)) (QR.cross (QR.pv 0) (QR.pv 3))) (by decide +kernel)

/-- Conjugation is multiplicative: `(qr) x (qr)‾ = q (r x r̄) q̄`. -/
theorem rot_mul (q r x : Quat p) : Quat.conjBy (Quat.mul q r) x = Quat.conjBy q (Quat.conjBy r x) :=
  QR.sound (look [q.a, q.b, q.c, q.d, r.a, r.b, r.c, r.d, x.a, x.b, x.c, x.d]) (QR.conjBy (QR.mul (QR.v 0) (QR.v 4)) (QR.v 8))
    (QR.conjBy (QR.v 0) (QR.conjBy (QR.v 4) (QR.v 8))) (by decide +kernel)

/-- Scaling: `(sq) x (sq)‾ = s² q x q̄` and `N(sq) = s² N(q)`, so the rotation of `q` depends on `q` up to a scalar. -/
theorem rot_smul (s : Shell p) (q x : Quat p) :
    Quat.conjBy (Quat.smul s q) x = Quat.smul (s * s) (Quat.conjBy q x) ∧ Quat.nrm (Quat.smul s q) = s * s * Quat.nrm q :=
  ⟨QR.sound (look [s, q.a, q.b, q.c, q.d, x.a, x.b, x.c, x.d]) (QR.conjBy (QR.smul (.var 0) (QR.v 1)) (QR.v 5))
      (QR.smul (.mul (.var 0) (.var 0)) (QR.conjBy (QR.v 1) (QR.v 5))) (by decide +kernel),
   RE.sound (look [s, q.a, q.b, q.c, q.d]) (QR.nrm (QR.smul (.var 0) (QR.v 1))) (.mul (.mul (.var 0) (.var 0)) (QR.nrm (QR.v 1))) (by decide +kernel)⟩

/-- The half-turn case: at `u · w = 1` the product `(1 + u)(1 + w)` is the pure quaternion `u + w + u × w`. -/
theorem one_add_mul_half (u w : Quat p) (hu : u.a = 0) (hw : w.a = 0) (h1 : Quat.dot u w = 1) :
    Quat.mul (Quat.add (Quat.sc 1) u) (Quat.add (Quat.sc 1) w) = Quat.add (Quat.sc 0) (Quat.add (Quat.add u w) (Quat.cross u w)) := by
  rw [one_add_mul u w hu hw, h1, add_neg]

/-- The sign: `ρ_{−q} = ρ_q` (`(−q) x (−q)‾ = q x q̄`, `N(−q) = N(q)`); the window rotations of an axis come in
pairs `±(a, t)`, which bounds them by `2H² + 2H` (`FRC.Algebra.card_image_le_of_neg`). -/
theorem rot_neg (q x : Quat p) : Quat.conjBy (Quat.neg q) x = Quat.conjBy q x ∧ Quat.nrm (Quat.neg q) = Quat.nrm q :=
  ⟨QR.sound (look [q.a, q.b, q.c, q.d, x.a, x.b, x.c, x.d]) (QR.conjBy (QR.neg (QR.v 0)) (QR.v 4)) (QR.conjBy (QR.v 0) (QR.v 4)) (by decide +kernel),
   RE.sound (look [q.a, q.b, q.c, q.d]) (QR.nrm (QR.neg (QR.v 0))) (QR.nrm (QR.v 0)) (by decide +kernel)⟩

theorem smul_sc_add (s s' : Shell p) (m : Quat p) :
    Quat.smul s (Quat.add (Quat.sc 1) (Quat.smul s' m)) = Quat.add (Quat.sc s) (Quat.smul (s * s') m) :=
  QR.sound (look [s, s', m.a, m.b, m.c, m.d]) (QR.smul (.var 0) (QR.add (QR.sc .one) (QR.smul (.var 1) (QR.v 2))))
    (QR.add (QR.sc (.var 0)) (QR.smul (.mul (.var 0) (.var 1)) (QR.v 2))) (by decide +kernel)

theorem smul_one_q (m : Quat p) : Quat.smul 1 m = m :=
  QR.sound (look [m.a, m.b, m.c, m.d]) (QR.smul .one (QR.v 0)) (QR.v 0) (by decide +kernel)

theorem smul_smul_q (s t : Shell p) (m : Quat p) : Quat.smul s (Quat.smul t m) = Quat.smul (s * t) m :=
  QR.sound (look [s, t, m.a, m.b, m.c, m.d]) (QR.smul (.var 0) (QR.smul (.var 1) (QR.v 2))) (QR.smul (.mul (.var 0) (.var 1)) (QR.v 2)) (by decide +kernel)

theorem conjBy_smul (q y : Quat p) (t : Shell p) : Quat.conjBy q (Quat.smul t y) = Quat.smul t (Quat.conjBy q y) :=
  QR.sound (look [q.a, q.b, q.c, q.d, t, y.a, y.b, y.c, y.d]) (QR.conjBy (QR.v 0) (QR.smul (.var 4) (QR.v 5)))
    (QR.smul (.var 4) (QR.conjBy (QR.v 0) (QR.v 5))) (by decide +kernel)

theorem inv_chain (nu nw s nc Nu Nw Nc : Shell p) (hu : Nu * nu = 1) (hw : Nw * nw = 1) (hc : Nc * nc = 1)
    (hN : Nu * Nw = s * s * Nc) : nu * nw * (s * s) = nc := by
  have e1 : nu * nw * (s * s) = nc * (nu * nw * (s * s * Nc)) := by
    calc nu * nw * (s * s) = nu * nw * (s * s) * (Nc * nc) := by rw [hc, mul_one]
      _ = nc * (nu * nw * (s * s * Nc)) :=
        RE.sound (look [nu, nw, s, nc, Nc])
          (.mul (.mul (.mul (.var 0) (.var 1)) (.mul (.var 2) (.var 2))) (.mul (.var 4) (.var 3)))
          (.mul (.var 3) (.mul (.mul (.var 0) (.var 1)) (.mul (.mul (.var 2) (.var 2)) (.var 4)))) (by decide +kernel)
  have e2 : nu * nw * (Nu * Nw) = (Nu * nu) * (Nw * nw) :=
    RE.sound (look [nu, nw, Nu, Nw]) (.mul (.mul (.var 0) (.var 1)) (.mul (.var 2) (.var 3)))
      (.mul (.mul (.var 2) (.var 0)) (.mul (.var 3) (.var 1))) (by decide +kernel)
  rw [e1, ← hN, e2, hu, hw, mul_one, mul_one]

/-- The composition law: for pure `u`, `w` with `1 + N(u)`, `1 + N(w)`, `1 − u·w` and `1 + N(u∘w)` invertible
(inverses `nu`, `nw`, `s'`, `nc`), `ρ_{1+u} ρ_{1+w} = ρ_{1+u∘w}` with `u∘w = (u + w + u × w)/(1 − u·w)`; here
`ρ_q x = N(q)⁻¹ q x q̄`. -/
theorem compose (u w x : Quat p) (hu : u.a = 0) (hw : w.a = 0) (s' nu nw nc : Shell p)
    (hs : (1 + -(Quat.dot u w)) * s' = 1)
    (hnu : Quat.nrm (Quat.add (Quat.sc 1) u) * nu = 1) (hnw : Quat.nrm (Quat.add (Quat.sc 1) w) * nw = 1)
    (hnc : Quat.nrm (Quat.add (Quat.sc 1) (Quat.smul s' (Quat.add (Quat.add u w) (Quat.cross u w)))) * nc = 1) :
    Quat.smul nu (Quat.conjBy (Quat.add (Quat.sc 1) u) (Quat.smul nw (Quat.conjBy (Quat.add (Quat.sc 1) w) x))) =
      Quat.smul nc (Quat.conjBy (Quat.add (Quat.sc 1) (Quat.smul s' (Quat.add (Quat.add u w) (Quat.cross u w)))) x) := by
  have hP : Quat.mul (Quat.add (Quat.sc 1) u) (Quat.add (Quat.sc 1) w) =
      Quat.smul (1 + -(Quat.dot u w)) (Quat.add (Quat.sc 1) (Quat.smul s' (Quat.add (Quat.add u w) (Quat.cross u w)))) := by
    rw [smul_sc_add, hs, smul_one_q, one_add_mul u w hu hw]
  have hN : Quat.nrm (Quat.add (Quat.sc 1) u) * Quat.nrm (Quat.add (Quat.sc 1) w) =
      (1 + -(Quat.dot u w)) * (1 + -(Quat.dot u w)) *
        Quat.nrm (Quat.add (Quat.sc 1) (Quat.smul s' (Quat.add (Quat.add u w) (Quat.cross u w)))) := by
    rw [← nrm_mul, hP, (rot_smul _ _ x).2]
  rw [conjBy_smul, smul_smul_q, ← rot_mul, hP, (rot_smul _ _ x).1, smul_smul_q, inv_chain nu nw _ nc _ _ _ hnu hnw hnc hN]

theorem add_cancel_q {r m : Quat p} (h : Quat.add r m = r) : m = ⟨0, 0, 0, 0⟩ := by
  have c : ∀ x y : Shell p, x + y = x → y = 0 := fun x y e => add_right_cancel (c := x) (by rw [add_comm, e, zero_add])
  exact Quat.ext4 (c _ _ (congrArg Quat.a h)) (c _ _ (congrArg Quat.b h)) (c _ _ (congrArg Quat.c h)) (c _ _ (congrArg Quat.d h))

theorem cayley_trivial_id (q x : Quat p) (hx : x.a = 0) :
    Quat.add (Quat.add (Quat.smul q.a (Quat.smul (Quat.nrm q) x)) (Quat.neg (Quat.cross (Quat.vec q) (Quat.smul (Quat.nrm q) x))))
      (Quat.smul (1 + 1) (Quat.smul (Quat.nrm q) (Quat.cross (Quat.vec q) x))) =
      Quat.smul (Quat.nrm q) (Quat.add (Quat.smul q.a x) (Quat.cross (Quat.vec q) x)) := by
  rw [Quat.pure_eq hx]
  exact QR.sound (look [q.a, q.b, q.c, q.d, x.b, x.c, x.d])
    (QR.add (QR.add (QR.smul (.var 0) (QR.smul (QR.nrm (QR.v 0)) (QR.pv 4))) (QR.neg (QR.cross (QR.vec (QR.v 0)) (QR.smul (QR.nrm (QR.v 0)) (QR.pv 4)))))
      (QR.smul (.add .one .one) (QR.smul (QR.nrm (QR.v 0)) (QR.cross (QR.vec (QR.v 0)) (QR.pv 4)))))
    (QR.smul (QR.nrm (QR.v 0)) (QR.add (QR.smul (.var 0) (QR.pv 4)) (QR.cross (QR.vec (QR.v 0)) (QR.pv 4)))) (by decide +kernel)

/-- The kernel: on a field shell, a rotation `ρ_q` (`N(q) ≠ 0`) that fixes every pure quaternion has `q` a
scalar — so `a + t v ↦ ρ_{a+tv}` is injective on the pairs modulo the scalars, and the axis group of
`FRC.Algebra.axis_group` is the rotation group of the axis. -/
theorem rot_trivial {κ : Nat} {g : Shell p} (F : Frame p κ g) (q : Quat p) (hN : Quat.nrm q ≠ 0)
    (h : ∀ x : Quat p, x.a = 0 → Quat.conjBy q x = Quat.smul (Quat.nrm q) x) : q.b = 0 ∧ q.c = 0 ∧ q.d = 0 := by
  have key : ∀ x : Quat p, x.a = 0 → Quat.smul (1 + 1) (Quat.smul (Quat.nrm q) (Quat.cross (Quat.vec q) x)) = ⟨0, 0, 0, 0⟩ := by
    intro x hx
    have E := rot_cayley q x hx
    rw [h x hx] at E
    have I := cayley_trivial_id q x hx
    rw [← E] at I
    exact add_cancel_q I
  have h2 : (1 + 1 : Shell p) ≠ 0 := by rw [← two_eq_one_add_one]; exact F.two_ne_zero
  have z : ∀ t : Shell p, (1 + 1) * (Quat.nrm q * t) = 0 → t = 0 := fun t e =>
    match F.mul_eq_zero e with
    | .inl e1 => absurd e1 h2
    | .inr e2 => match F.mul_eq_zero e2 with
      | .inl e3 => absurd e3 hN
      | .inr e4 => e4
  have kb := key ⟨0, 1, 0, 0⟩ rfl
  have kc := key ⟨0, 0, 1, 0⟩ rfl
  have hd : q.d = 0 := z _ (by
    have := congrArg Quat.c kb
    simp only [Quat.smul, Quat.cross, Quat.vec] at this
    rw [mul_one, mul_zero, neg_zero, add_zero] at this; exact this)
  have hcneg : -q.c = 0 := z _ (by
    have := congrArg Quat.d kb
    simp only [Quat.smul, Quat.cross, Quat.vec] at this
    rw [mul_zero, mul_one] at this
    rw [zero_add] at this; exact this)
  have hb : q.b = 0 := z _ (by
    have := congrArg Quat.d kc
    simp only [Quat.smul, Quat.cross, Quat.vec] at this
    rw [mul_one, mul_zero, neg_zero, add_zero] at this; exact this)
  refine ⟨hb, ?_, hd⟩
  rw [← neg_neg q.c, hcneg, neg_zero]



/-! ## The axis: parameters, injectivity, exceptional values, the window count -/

/-- On the axis of `v`, `a + t v` (`a y = 1`) is the scalar `a` times `1 + s v` with `s = t y`. -/
theorem axis_param {a t y : Shell p} (hay : a * y = 1) (v : Quat p) :
    Quat.add (Quat.sc a) (Quat.smul t v) = Quat.smul a (Quat.add (Quat.sc 1) (Quat.smul (t * y) v)) := by
  have key : ∀ w : Shell p, t * w = a * (t * y * w) := fun w => by
    calc t * w = (a * y) * (t * w) := by rw [hay, one_mul]
      _ = a * (t * y * w) := RE.sound (look [a, y, t, w]) (.mul (.mul (.var 0) (.var 1)) (.mul (.var 2) (.var 3)))
            (.mul (.var 0) (.mul (.mul (.var 2) (.var 1)) (.var 3))) (by decide +kernel)
  apply Quat.ext4
  · show a + t * v.a = a * (1 + t * y * v.a)
    rw [left_distrib, mul_one, ← key]
  · show 0 + t * v.b = a * (0 + t * y * v.b)
    rw [zero_add, zero_add, ← key]
  · show 0 + t * v.c = a * (0 + t * y * v.c)
    rw [zero_add, zero_add, ← key]
  · show 0 + t * v.d = a * (0 + t * y * v.d)
    rw [zero_add, zero_add, ← key]

/-- `q̄ (q x q̄) q = N(q)² x`. -/
theorem conj_conjBy (q x : Quat p) : Quat.conjBy (Quat.conj q) (Quat.conjBy q x) = Quat.smul (Quat.nrm q * Quat.nrm q) x :=
  QR.sound (look [q.a, q.b, q.c, q.d, x.a, x.b, x.c, x.d]) (QR.conjBy (QR.conj (QR.v 0)) (QR.conjBy (QR.v 0) (QR.v 4)))
    (QR.smul (.mul (QR.nrm (QR.v 0)) (QR.nrm (QR.v 0))) (QR.v 4)) (by decide +kernel)

theorem nrm_conj (q : Quat p) : Quat.nrm (Quat.conj q) = Quat.nrm q :=
  RE.sound (look [q.a, q.b, q.c, q.d]) (QR.nrm (QR.conj (QR.v 0))) (QR.nrm (QR.v 0)) (by decide +kernel)

/-- `(1 − s v)(1 + t v) = (1 + st N(v)) + (t − s) v` for a pure `v = (0, b, c, d)`. -/
theorem axis_quotient (s t b c d : Shell p) :
    Quat.mul (Quat.conj (Quat.add (Quat.sc 1) (Quat.smul s ⟨0, b, c, d⟩))) (Quat.add (Quat.sc 1) (Quat.smul t ⟨0, b, c, d⟩)) =
    Quat.add (Quat.sc (1 + s * t * (b * b + c * c + d * d))) (Quat.smul (t + -s) ⟨0, b, c, d⟩) :=
  QR.sound (look [s, t, b, c, d])
    (QR.mul (QR.conj (QR.add (QR.sc .one) (QR.smul (.var 0) ⟨.zero, .var 2, .var 3, .var 4⟩)))
      (QR.add (QR.sc .one) (QR.smul (.var 1) ⟨.zero, .var 2, .var 3, .var 4⟩)))
    (QR.add (QR.sc (.add .one (.mul (.mul (.var 0) (.var 1)) (.add (.add (.mul (.var 2) (.var 2)) (.mul (.var 3) (.var 3))) (.mul (.var 4) (.var 4))))))
      (QR.smul (.add (.var 1) (.neg (.var 0))) ⟨.zero, .var 2, .var 3, .var 4⟩)) (by decide +kernel)

/-- Distinct parameters give distinct rotations: if `1 + s v` and `1 + t v` (`v` pure and nonzero, both norms
nonzero) rotate every pure quaternion alike, `N(r) ρ_q = N(q) ρ_r`, then `s = t`. -/
theorem axis_inj {κ : Nat} {g : Shell p} (F : Frame p κ g) {b c d s t : Shell p} (hv0 : b ≠ 0 ∨ c ≠ 0 ∨ d ≠ 0)
    (hq : Quat.nrm (Quat.add (Quat.sc 1) (Quat.smul s ⟨0, b, c, d⟩)) ≠ 0)
    (hr : Quat.nrm (Quat.add (Quat.sc 1) (Quat.smul t ⟨0, b, c, d⟩)) ≠ 0)
    (h : ∀ x : Quat p, x.a = 0 →
      Quat.smul (Quat.nrm (Quat.add (Quat.sc 1) (Quat.smul t ⟨0, b, c, d⟩))) (Quat.conjBy (Quat.add (Quat.sc 1) (Quat.smul s ⟨0, b, c, d⟩)) x) =
      Quat.smul (Quat.nrm (Quat.add (Quat.sc 1) (Quat.smul s ⟨0, b, c, d⟩))) (Quat.conjBy (Quat.add (Quat.sc 1) (Quat.smul t ⟨0, b, c, d⟩)) x)) :
    s = t := by
  generalize hQ : Quat.add (Quat.sc 1) (Quat.smul s ⟨0, b, c, d⟩) = q at hq h
  generalize hR : Quat.add (Quat.sc 1) (Quat.smul t ⟨0, b, c, d⟩) = r at hr h
  have hw : Quat.mul (Quat.conj q) r = Quat.add (Quat.sc (1 + s * t * (b * b + c * c + d * d))) (Quat.smul (t + -s) ⟨0, b, c, d⟩) := by
    rw [← hQ, ← hR]; exact axis_quotient s t b c d
  have hNw : Quat.nrm (Quat.mul (Quat.conj q) r) = Quat.nrm q * Quat.nrm r := by rw [nrm_mul, nrm_conj]
  have hNw0 : Quat.nrm (Quat.mul (Quat.conj q) r) ≠ 0 := by rw [hNw]; exact F.mul_ne_zero hq hr
  have triv : ∀ x : Quat p, x.a = 0 → Quat.conjBy (Quat.mul (Quat.conj q) r) x = Quat.smul (Quat.nrm (Quat.mul (Quat.conj q) r)) x := by
    intro x hx
    have e1 : Quat.smul (Quat.nrm q) (Quat.conjBy (Quat.mul (Quat.conj q) r) x) =
        Quat.smul (Quat.nrm q) (Quat.smul (Quat.nrm (Quat.mul (Quat.conj q) r)) x) := by
      rw [rot_mul, ← conjBy_smul, ← h x hx, conjBy_smul, conj_conjBy, smul_smul_q, smul_smul_q, hNw]
      congr 1
      exact RE.sound (look [Quat.nrm q, Quat.nrm r]) (.mul (.var 1) (.mul (.var 0) (.var 0))) (.mul (.var 0) (.mul (.var 0) (.var 1))) (by decide +kernel)
    have cancel : ∀ u w : Shell p, Quat.nrm q * u = Quat.nrm q * w → u = w := fun u w e => F.mul_left_cancel hq e
    exact Quat.ext4 (cancel _ _ (congrArg Quat.a e1)) (cancel _ _ (congrArg Quat.b e1)) (cancel _ _ (congrArg Quat.c e1)) (cancel _ _ (congrArg Quat.d e1))
  obtain ⟨hb, hc, hd⟩ := rot_trivial F _ hNw0 triv
  rw [hw] at hb hc hd
  have hb' : (t + -s) * b = 0 := by have := hb; simp only [Quat.add, Quat.sc, Quat.smul] at this; rw [zero_add] at this; exact this
  have hc' : (t + -s) * c = 0 := by have := hc; simp only [Quat.add, Quat.sc, Quat.smul] at this; rw [zero_add] at this; exact this
  have hd' : (t + -s) * d = 0 := by have := hd; simp only [Quat.add, Quat.sc, Quat.smul] at this; rw [zero_add] at this; exact this
  have hts : t + -s = 0 := by
    match hv0 with
    | Or.inl hb0 => exact (F.mul_eq_zero hb').resolve_right hb0
    | Or.inr (Or.inl hc0) => exact (F.mul_eq_zero hc').resolve_right hc0
    | Or.inr (Or.inr hd0) => exact (F.mul_eq_zero hd').resolve_right hd0
  exact (Prime.eq_of_sub_eq_zero hts).symm

/-- `(1 − s v) v = s N(v) + v` for a pure `v = (0, b, c, d)`. -/
theorem axis_half_quotient (s b c d : Shell p) :
    Quat.mul (Quat.conj (Quat.add (Quat.sc 1) (Quat.smul s ⟨0, b, c, d⟩))) ⟨0, b, c, d⟩ =
    Quat.add (Quat.sc (s * (b * b + c * c + d * d))) ⟨0, b, c, d⟩ :=
  QR.sound (look [s, b, c, d])
    (QR.mul (QR.conj (QR.add (QR.sc .one) (QR.smul (.var 0) ⟨.zero, .var 1, .var 2, .var 3⟩))) ⟨.zero, .var 1, .var 2, .var 3⟩)
    (QR.add (QR.sc (.mul (.var 0) (.add (.add (.mul (.var 1) (.var 1)) (.mul (.var 2) (.var 2))) (.mul (.var 3) (.var 3)))))
      ⟨.zero, .var 1, .var 2, .var 3⟩) (by decide +kernel)

/-- The half-turn is not among the parameters: `ρ_{1+sv} ≠ ρ_v` for a pure nonzero `v` (the quotient
`(1 − s v) v = sN(v) + v` is never a scalar). -/
theorem axis_half {κ : Nat} {g : Shell p} (F : Frame p κ g) {b c d s : Shell p} (hv0 : b ≠ 0 ∨ c ≠ 0 ∨ d ≠ 0)
    (hq : Quat.nrm (Quat.add (Quat.sc 1) (Quat.smul s ⟨0, b, c, d⟩)) ≠ 0)
    (hr : Quat.nrm (⟨0, b, c, d⟩ : Quat p) ≠ 0)
    (h : ∀ x : Quat p, x.a = 0 →
      Quat.smul (Quat.nrm (⟨0, b, c, d⟩ : Quat p)) (Quat.conjBy (Quat.add (Quat.sc 1) (Quat.smul s ⟨0, b, c, d⟩)) x) =
      Quat.smul (Quat.nrm (Quat.add (Quat.sc 1) (Quat.smul s ⟨0, b, c, d⟩))) (Quat.conjBy ⟨0, b, c, d⟩ x)) : False := by
  generalize hQ : Quat.add (Quat.sc 1) (Quat.smul s ⟨0, b, c, d⟩) = q at hq h
  generalize hR : (⟨0, b, c, d⟩ : Quat p) = r at hr h
  have hw : Quat.mul (Quat.conj q) r = Quat.add (Quat.sc (s * (b * b + c * c + d * d))) ⟨0, b, c, d⟩ := by
    rw [← hQ, ← hR]; exact axis_half_quotient s b c d
  have hNw : Quat.nrm (Quat.mul (Quat.conj q) r) = Quat.nrm q * Quat.nrm r := by rw [nrm_mul, nrm_conj]
  have hNw0 : Quat.nrm (Quat.mul (Quat.conj q) r) ≠ 0 := by rw [hNw]; exact F.mul_ne_zero hq hr
  have triv : ∀ x : Quat p, x.a = 0 → Quat.conjBy (Quat.mul (Quat.conj q) r) x = Quat.smul (Quat.nrm (Quat.mul (Quat.conj q) r)) x := by
    intro x hx
    have e1 : Quat.smul (Quat.nrm q) (Quat.conjBy (Quat.mul (Quat.conj q) r) x) =
        Quat.smul (Quat.nrm q) (Quat.smul (Quat.nrm (Quat.mul (Quat.conj q) r)) x) := by
      rw [rot_mul, ← conjBy_smul, ← h x hx, conjBy_smul, conj_conjBy, smul_smul_q, smul_smul_q, hNw]
      congr 1
      exact RE.sound (look [Quat.nrm q, Quat.nrm r]) (.mul (.var 1) (.mul (.var 0) (.var 0))) (.mul (.var 0) (.mul (.var 0) (.var 1))) (by decide +kernel)
    have cancel : ∀ u w : Shell p, Quat.nrm q * u = Quat.nrm q * w → u = w := fun u w e => F.mul_left_cancel hq e
    exact Quat.ext4 (cancel _ _ (congrArg Quat.a e1)) (cancel _ _ (congrArg Quat.b e1)) (cancel _ _ (congrArg Quat.c e1)) (cancel _ _ (congrArg Quat.d e1))
  obtain ⟨hb, hc, hd⟩ := rot_trivial F _ hNw0 triv
  rw [hw] at hb hc hd
  have hb' : b = 0 := by have := hb; simp only [Quat.add, Quat.sc] at this; rw [zero_add] at this; exact this
  have hc' : c = 0 := by have := hc; simp only [Quat.add, Quat.sc] at this; rw [zero_add] at this; exact this
  have hd' : d = 0 := by have := hd; simp only [Quat.add, Quat.sc] at this; rw [zero_add] at this; exact this
  match hv0 with
  | Or.inl h0 => exact h0 hb'
  | Or.inr (Or.inl h0) => exact h0 hc'
  | Or.inr (Or.inr h0) => exact h0 hd'

/-- The parameter `s` fails exactly at the roots of `1 + N s² = 0`, that is `s² = −N⁻¹` (`N m = 1`). -/
theorem axis_exceptional {N m : Shell p} (hm : N * m = 1) (s : Shell p) : (1 : Shell p) + N * (s * s) = 0 ↔ s * s = -m := by
  constructor
  · intro h
    have h1 : N * (s * s) = -1 := (eq_neg_of_add_eq_zero (by rw [add_comm]; exact h))
    calc s * s = (m * N) * (s * s) := by rw [mul_comm m N, hm, one_mul]
      _ = m * (N * (s * s)) := mul_assoc _ _ _
      _ = -m := by rw [h1, ← mul_neg, mul_one]
  · intro h
    rw [h, ← mul_neg, hm]
    exact add_neg 1

/-- On a framed shell `−N⁻¹` is a square exactly when `N` is (the quarter-turn turns one into the other), so the
exceptional parameters are two (`root_pair`) when `N` is a square and none otherwise. -/
theorem neg_inv_square_iff {κ : Nat} {g : Shell p} (F : Frame p κ g) {N m : Shell p} (hm : N * m = 1) :
    (∃ x : Shell p, x * x = -m) ↔ (∃ y : Shell p, y * y = N) := by
  have hm0 : m ≠ 0 := fun e => F.one_ne_zero (by rw [← hm, e, mul_zero])
  have hN0 : N ≠ 0 := fun e => F.one_ne_zero (by rw [← hm, e, zero_mul])
  have hi := F.quarter_turn_sq
  constructor
  · intro ⟨x, hx⟩
    have hx0 : x ≠ 0 := fun e => hm0 (by
      have : -m = 0 := by rw [← hx, e, mul_zero]
      rw [← neg_neg m, this, neg_zero])
    obtain ⟨xi, hxi⟩ := F.exists_inv hx0
    refine ⟨quarterTurn g κ * xi, ?_⟩
    -- (i xi)² = −xi², and −xi² · m = (xi x)² = 1, so −xi² = N
    apply inv_unique (y := m)
    · calc quarterTurn g κ * xi * (quarterTurn g κ * xi) * m = (quarterTurn g κ * quarterTurn g κ) * (xi * xi) * m :=
            RE.sound (look [quarterTurn g κ, xi, m]) (.mul (.mul (.mul (.var 0) (.var 1)) (.mul (.var 0) (.var 1))) (.var 2))
              (.mul (.mul (.mul (.var 0) (.var 0)) (.mul (.var 1) (.var 1))) (.var 2)) (by decide +kernel)
        _ = (xi * xi) * (x * x) := by
            rw [hi, hx]
            exact RE.sound (look [xi, m]) (.mul (.mul (.neg .one) (.mul (.var 0) (.var 0))) (.var 1))
              (.mul (.mul (.var 0) (.var 0)) (.neg (.var 1))) (by decide +kernel)
        _ = (x * xi) * (x * xi) := RE.sound (look [x, xi]) (.mul (.mul (.var 1) (.var 1)) (.mul (.var 0) (.var 0)))
              (.mul (.mul (.var 0) (.var 1)) (.mul (.var 0) (.var 1))) (by decide +kernel)
        _ = 1 := by rw [hxi, one_mul]
    · exact hm
  · intro ⟨y, hy⟩
    have hy0 : y ≠ 0 := fun e => hN0 (by rw [← hy, e, mul_zero])
    obtain ⟨yi, hyi⟩ := F.exists_inv hy0
    refine ⟨quarterTurn g κ * yi, ?_⟩
    have hyim : yi * yi = m := by
      apply inv_unique (y := N)
      · calc yi * yi * N = (y * yi) * (y * yi) := by
              rw [← hy]
              exact RE.sound (look [y, yi]) (.mul (.mul (.var 1) (.var 1)) (.mul (.var 0) (.var 0)))
                (.mul (.mul (.var 0) (.var 1)) (.mul (.var 0) (.var 1))) (by decide +kernel)
          _ = 1 := by rw [hyi, one_mul]
      · rw [mul_comm]; exact hm
    calc quarterTurn g κ * yi * (quarterTurn g κ * yi) = (quarterTurn g κ * quarterTurn g κ) * (yi * yi) :=
          RE.sound (look [quarterTurn g κ, yi]) (.mul (.mul (.var 0) (.var 1)) (.mul (.var 0) (.var 1)))
            (.mul (.mul (.var 0) (.var 0)) (.mul (.var 1) (.var 1))) (by decide +kernel)
      _ = -m := by rw [hi, hyim, neg_one_mul]

/-- The window box: the `(2H + 1)²` pairs `(a, t)`, `|a|, |t| ≤ H`, are the origin and `2(2H² + 2H)` others,
which the sign `(a, t) ↦ (−a, −t)` (`window_signed`, `rot_neg`) pairs into `2H² + 2H` classes. -/
theorem box_count (H : Nat) : (2 * H + 1) * (2 * H + 1) = 2 * (2 * H * H + 2 * H) + 1 := by
  have hA : 2 * (2 * H * H) = 2 * H * (2 * H) := by
    rw [Nat.mul_comm 2 (2 * H * H), FRC.Nat.mul_assoc (2 * H) H 2, Nat.mul_comm H 2]
  calc (2 * H + 1) * (2 * H + 1) = (2 * H + 1) * (2 * H) + (2 * H + 1) := Nat.mul_succ _ _
    _ = 2 * H * (2 * H) + 1 * (2 * H) + (2 * H + 1) := by rw [FRC.Nat.add_mul]
    _ = 2 * H * (2 * H) + (2 * H + 2 * H) + 1 := by rw [Nat.one_mul, Nat.add_assoc, Nat.add_assoc, Nat.add_assoc]
    _ = 2 * (2 * H * H) + 2 * (2 * H) + 1 := by rw [hA, ← Nat.two_mul]
    _ = 2 * (2 * H * H + 2 * H) + 1 := by rw [Nat.left_distrib]

end Frame
end Shell
end FRC
