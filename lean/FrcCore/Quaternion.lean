import FrcCore.Algebra

/-!
# FrcCore.Quaternion — the framed quaternions and the window (1:E6, the finitary clause); the Lie-algebra layer (1:E7, 1:E8)

A signed window integer is a pair of naturals `(u, v)` read as `u − v` in the shell (no `Int`: the core's
integers are the shell's own readings).  A framed quaternion is four such pairs; the Hamilton product is
computed on the pairs, and `read_mul` says the product of the readings is the reading of the product — the
composition is exact.  `quaternion_window` adds the bounds: with coordinates in the window `H` and a shell
`p > 8H²`, the product's coordinates lie in the window `4H²`, and the shell reading determines the integer
product among the window's quaternions.  No axioms.

The Lie-algebra layer works on quaternions over the shell (`Quat`, with `conj`, `nrm`, `cross`, `dot`).  Its identities are
decided by a normaliser: `RE.sound` expands both sides of an identity into sorted lists of monomials and compares them by a
kernel computation, so an identity is one `decide +kernel`.  1:E7: the rotation `x ↦ q x q̄ / N(q)` is the Cayley
transform `(aI − S_v)⁻¹(aI + S_v)` (`rot_cayley`, `cayley_inj`), the half-turn at `a = 0` (`half_turn`), with kernel the
scalars (`rot_trivial`) and `ρ_{−q} = ρ_q` (`rot_neg`).  1:E8: `(1+u)(1+w) = (1 − u·w) + (u + w + u × w)` (`one_add_mul`),
the composition law (`compose`), the bracket (`bracket`).  No axioms.
-/

namespace FRC
namespace Shell
namespace Frame

variable {p : Nat} [Pos p]

/-- A signed window integer: `(u, v)` stands for `u − v`. -/
abbrev SInt := Nat × Nat

def sread (x : SInt) : Shell p := ofNat x.1 + -(ofNat x.2)
def sadd (x y : SInt) : SInt := (x.1 + y.1, x.2 + y.2)
def sneg (x : SInt) : SInt := (x.2, x.1)
def smul (x y : SInt) : SInt := (x.1 * y.1 + x.2 * y.2, x.1 * y.2 + x.2 * y.1)
/-- The canonical pair of the same value: one component zero. -/
def snorm (x : SInt) : SInt := (x.1 - x.2, x.2 - x.1)

theorem prod_ext {x y : SInt} (h1 : x.1 = y.1) (h2 : x.2 = y.2) : x = y :=
  match x, y, h1, h2 with
  | (_, _), (_, _), h1, h2 => by cases h1; cases h2; rfl

theorem sread_add (x y : SInt) : (sread (sadd x y) : Shell p) = sread x + sread y := by
  unfold sread sadd
  show ofNat (x.1 + y.1) + -(ofNat (x.2 + y.2)) = ofNat x.1 + -(ofNat x.2) + (ofNat y.1 + -(ofNat y.2))
  rw [← ofNat_add, ← ofNat_add, neg_add_rev, add_assoc, add_assoc, ← add_assoc (-(ofNat x.2)),
    add_comm (-(ofNat x.2)) (ofNat y.1), add_assoc]

theorem sread_neg (x : SInt) : (sread (sneg x) : Shell p) = -(sread x) := by
  unfold sread sneg
  show ofNat x.2 + -(ofNat x.1) = -(ofNat x.1 + -(ofNat x.2))
  rw [neg_add_rev, neg_neg, add_comm]

theorem sread_mul (x y : SInt) : (sread (smul x y) : Shell p) = sread x * sread y := by
  unfold sread smul
  show ofNat (x.1 * y.1 + x.2 * y.2) + -(ofNat (x.1 * y.2 + x.2 * y.1)) =
    (ofNat x.1 + -(ofNat x.2)) * (ofNat y.1 + -(ofNat y.2))
  rw [right_distrib, left_distrib, left_distrib, ← mul_neg, ← neg_mul, neg_mul_neg, ← ofNat_add, ← ofNat_add,
    ← ofNat_mul, ← ofNat_mul, ← ofNat_mul, ← ofNat_mul, neg_add_rev]
  -- a + d + (-b + -c) = a + -b + (-c + d)
  rw [add_assoc, add_assoc]
  refine congrArg (ofNat x.1 * ofNat y.1 + ·) ?_
  rw [← add_assoc, add_comm (ofNat x.2 * ofNat y.2), add_assoc, add_comm (ofNat x.2 * ofNat y.2)]

theorem sread_norm (x : SInt) : (sread (snorm x) : Shell p) = sread x := by
  unfold sread snorm
  match Nat.decLe x.2 x.1 with
  | .isTrue h =>
    have e : x.2 - x.1 = 0 := FRC.Nat.sub_eq_zero_of_le h
    show ofNat (x.1 - x.2) + -(ofNat (x.2 - x.1)) = ofNat x.1 + -(ofNat x.2)
    rw [e]
    have e0 : (ofNat 0 : Shell p) = 0 := rfl
    rw [e0, neg_zero, add_zero]
    have e1 : x.1 = (x.1 - x.2) + x.2 := (FRC.Nat.sub_add_cancel h).symm
    calc ofNat (x.1 - x.2) = ofNat (x.1 - x.2) + 0 := (add_zero _).symm
      _ = ofNat (x.1 - x.2) + (ofNat x.2 + -(ofNat x.2)) := by rw [add_neg]
      _ = ofNat (x.1 - x.2 + x.2) + -(ofNat x.2) := by rw [← add_assoc, ofNat_add]
      _ = ofNat x.1 + -(ofNat x.2) := by rw [← e1]
  | .isFalse h =>
    have h' : x.1 ≤ x.2 := Nat.le_of_lt (Nat.lt_of_not_le h)
    have e : x.1 - x.2 = 0 := FRC.Nat.sub_eq_zero_of_le h'
    show ofNat (x.1 - x.2) + -(ofNat (x.2 - x.1)) = ofNat x.1 + -(ofNat x.2)
    rw [e]
    have e0 : (ofNat 0 : Shell p) = 0 := rfl
    rw [e0, zero_add]
    have e1 : x.2 = (x.2 - x.1) + x.1 := (FRC.Nat.sub_add_cancel h').symm
    calc (-(ofNat (x.2 - x.1)) : Shell p) = (0 : Shell p) + -(ofNat (x.2 - x.1)) := (zero_add _).symm
      _ = (ofNat x.1 + -(ofNat x.1)) + -(ofNat (x.2 - x.1)) := by rw [add_neg]
      _ = ofNat x.1 + -((ofNat (x.2 - x.1) : Shell p) + ofNat x.1) := by
          rw [add_assoc, neg_add_rev, add_comm (-(ofNat x.1))]
      _ = ofNat x.1 + -(ofNat x.2) := by rw [ofNat_add, ← e1]

/-- The window bound: both components at most `H`, one of them zero. -/
def SBound (H : Nat) (x : SInt) : Prop := x.1 ≤ H ∧ x.2 ≤ H ∧ (x.1 = 0 ∨ x.2 = 0)

theorem sneg_bound {H : Nat} {x : SInt} (h : SBound H x) : SBound H (sneg x) :=
  ⟨h.2.1, h.1, match h.2.2 with | Or.inl e => Or.inr e | Or.inr e => Or.inl e⟩

theorem smul_bound {H : Nat} {x y : SInt} (hx : SBound H x) (hy : SBound H y) : SBound (H * H) (smul x y) := by
  unfold smul
  have b11 := Nat.mul_le_mul hx.1 hy.1
  have b22 := Nat.mul_le_mul hx.2.1 hy.2.1
  have b12 := Nat.mul_le_mul hx.1 hy.2.1
  have b21 := Nat.mul_le_mul hx.2.1 hy.1
  match hx.2.2, hy.2.2 with
  | Or.inl e, Or.inl f =>
    refine ⟨?_, ?_, Or.inr ?_⟩
    · show x.1 * y.1 + x.2 * y.2 ≤ H * H
      rw [e, Nat.zero_mul, Nat.zero_add]; exact b22
    · show x.1 * y.2 + x.2 * y.1 ≤ H * H
      rw [e, f, Nat.zero_mul, Nat.mul_zero]; exact Nat.zero_le _
    · show x.1 * y.2 + x.2 * y.1 = 0
      rw [e, f, Nat.zero_mul, Nat.mul_zero]
  | Or.inl e, Or.inr f =>
    refine ⟨?_, ?_, Or.inl ?_⟩
    · show x.1 * y.1 + x.2 * y.2 ≤ H * H
      rw [e, f, Nat.zero_mul, Nat.mul_zero]; exact Nat.zero_le _
    · show x.1 * y.2 + x.2 * y.1 ≤ H * H
      rw [e, Nat.zero_mul, Nat.zero_add]; exact b21
    · show x.1 * y.1 + x.2 * y.2 = 0
      rw [e, f, Nat.zero_mul, Nat.mul_zero]
  | Or.inr e, Or.inl f =>
    refine ⟨?_, ?_, Or.inl ?_⟩
    · show x.1 * y.1 + x.2 * y.2 ≤ H * H
      rw [e, f, Nat.mul_zero, Nat.zero_mul]; exact Nat.zero_le _
    · show x.1 * y.2 + x.2 * y.1 ≤ H * H
      rw [e, Nat.zero_mul, Nat.add_zero]; exact b12
    · show x.1 * y.1 + x.2 * y.2 = 0
      rw [e, f, Nat.mul_zero, Nat.zero_mul]
  | Or.inr e, Or.inr f =>
    refine ⟨?_, ?_, Or.inr ?_⟩
    · show x.1 * y.1 + x.2 * y.2 ≤ H * H
      rw [e, Nat.zero_mul, Nat.add_zero]; exact b11
    · show x.1 * y.2 + x.2 * y.1 ≤ H * H
      rw [e, f, Nat.mul_zero, Nat.zero_mul]; exact Nat.zero_le _
    · show x.1 * y.2 + x.2 * y.1 = 0
      rw [e, f, Nat.mul_zero, Nat.zero_mul]

/-- Four window terms of size `M` add to a pair with both components at most `4M`. -/
theorem sum4_bound {M : Nat} {t1 t2 t3 t4 : SInt} (h1 : SBound M t1) (h2 : SBound M t2) (h3 : SBound M t3)
    (h4 : SBound M t4) :
    (sadd (sadd t1 t2) (sadd t3 t4)).1 ≤ 4 * M ∧ (sadd (sadd t1 t2) (sadd t3 t4)).2 ≤ 4 * M := by
  unfold sadd
  rw [four_mul_eq, Nat.add_assoc (M + M) M M]
  exact ⟨Nat.add_le_add (Nat.add_le_add h1.1 h2.1) (Nat.add_le_add h3.1 h4.1),
    Nat.add_le_add (Nat.add_le_add h1.2.1 h2.2.1) (Nat.add_le_add h3.2.1 h4.2.1)⟩

theorem snorm_bound {M : Nat} {x : SInt} (h1 : x.1 ≤ M) (h2 : x.2 ≤ M) : SBound M (snorm x) := by
  unfold snorm
  refine ⟨Nat.le_trans (Nat.sub_le _ _) h1, Nat.le_trans (Nat.sub_le _ _) h2, ?_⟩
  match Nat.decLe x.2 x.1 with
  | .isTrue h => exact Or.inr (FRC.Nat.sub_eq_zero_of_le h)
  | .isFalse h => exact Or.inl (FRC.Nat.sub_eq_zero_of_le (Nat.le_of_lt (Nat.lt_of_not_le h)))

/-- The signed window law: two canonical pairs of size `M`, `2M < p`, with the same reading are equal. -/
theorem sread_inj {M : Nat} (hM : 2 * M < p) {x y : SInt} (hx : SBound M x) (hy : SBound M y)
    (h : (sread x : Shell p) = sread y) : x = y := by
  unfold sread at h
  have h' : (ofNat (x.1 + y.2) : Shell p) = ofNat (y.1 + x.2) := by
    rw [← ofNat_add, ← ofNat_add]
    calc ofNat x.1 + ofNat y.2 = ofNat x.1 + -(ofNat x.2) + (ofNat x.2 + ofNat y.2) := by
          rw [add_assoc, ← add_assoc (-(ofNat x.2)), neg_add, zero_add]
      _ = ofNat y.1 + -(ofNat y.2) + (ofNat x.2 + ofNat y.2) := by rw [h]
      _ = ofNat y.1 + ofNat x.2 := by
          rw [add_assoc, add_comm (ofNat x.2), ← add_assoc (-(ofNat y.2)), neg_add, zero_add]
  have hv := val_injective h'
  rw [val_ofNat, val_ofNat] at hv
  have l1 : x.1 + y.2 < p := Nat.lt_of_le_of_lt (Nat.add_le_add hx.1 hy.2.1) (Nat.two_mul M ▸ hM)
  have l2 : y.1 + x.2 < p := Nat.lt_of_le_of_lt (Nat.add_le_add hy.1 hx.2.1) (Nat.two_mul M ▸ hM)
  rw [FRC.Nat.mod_eq_of_lt l1, FRC.Nat.mod_eq_of_lt l2] at hv
  -- hv : x.1 + y.2 = y.1 + x.2
  match hx.2.2, hy.2.2 with
  | Or.inl e, Or.inl f =>
    rw [e, f, Nat.zero_add, Nat.zero_add] at hv
    exact prod_ext (e.trans f.symm) hv.symm
  | Or.inl e, Or.inr f =>
    rw [e, f, Nat.zero_add] at hv
    -- hv : 0 = y.1 + x.2
    have hy1 : y.1 = 0 := Nat.eq_zero_of_add_eq_zero_right hv.symm
    have hx2 : x.2 = 0 := Nat.eq_zero_of_add_eq_zero_left hv.symm
    exact prod_ext (e.trans hy1.symm) (hx2.trans f.symm)
  | Or.inr e, Or.inl f =>
    rw [e, f, Nat.zero_add] at hv
    -- hv : x.1 + y.2 = 0
    have hx1 : x.1 = 0 := Nat.eq_zero_of_add_eq_zero_right hv
    have hy2 : y.2 = 0 := Nat.eq_zero_of_add_eq_zero_left hv
    exact prod_ext (hx1.trans f.symm) (e.trans hy2.symm)
  | Or.inr e, Or.inr f =>
    rw [e, f, Nat.add_zero, Nat.add_zero] at hv
    exact prod_ext hv (e.trans f.symm)

/-- A framed quaternion with signed window coordinates. -/
structure IQuat where
  a : SInt
  b : SInt
  c : SInt
  d : SInt

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

/-- 1:E6, exact composition — the reading of the integer product is the product of the readings. -/
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

/-- 1:E6, the finitary clause — framed quaternions with window coordinates `≤ H`, read in a shell `p > 8H²`,
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

/-! ## A normaliser for ring identities on the shell (no axioms)

An identity between two polynomial expressions is decided by expanding each side into a positive and a negative
list of monomials, sorting, and comparing `P_l ++ N_r` with `P_r ++ N_l`; `RE.sound` turns a successful comparison
(a kernel computation, `decide`) into the equation on the shell. -/

inductive RE where
  | var : Nat → RE
  | zero : RE
  | one : RE
  | add : RE → RE → RE
  | mul : RE → RE → RE
  | neg : RE → RE

def RE.eval (env : Nat → Shell p) : RE → Shell p
  | .var i => env i
  | .zero => 0
  | .one => 1
  | .add a b => a.eval env + b.eval env
  | .mul a b => a.eval env * b.eval env
  | .neg a => -(a.eval env)

/-- The assignment of shell values to the variables `0, 1, 2, …` of an expression. -/
def look : List (Shell p) → Nat → Shell p
  | [], _ => 0
  | x :: _, 0 => x
  | _ :: l, n + 1 => look l n

def mEval (env : Nat → Shell p) : List Nat → Shell p
  | [] => 1
  | i :: m => env i * mEval env m

def pEval (env : Nat → Shell p) : List (List Nat) → Shell p
  | [] => 0
  | m :: P => mEval env m + pEval env P

def pRow (m : List Nat) : List (List Nat) → List (List Nat)
  | [] => []
  | n :: Q => (m ++ n) :: pRow m Q

def pMul : List (List Nat) → List (List Nat) → List (List Nat)
  | [], _ => []
  | m :: P, Q => pRow m Q ++ pMul P Q

def RE.toP : RE → List (List Nat) × List (List Nat)
  | .var i => ([[i]], [])
  | .zero => ([], [])
  | .one => ([[]], [])
  | .add a b => (a.toP.1 ++ b.toP.1, a.toP.2 ++ b.toP.2)
  | .mul a b => (pMul a.toP.1 b.toP.1 ++ pMul a.toP.2 b.toP.2, pMul a.toP.1 b.toP.2 ++ pMul a.toP.2 b.toP.1)
  | .neg a => (a.toP.2, a.toP.1)

def insM (i : Nat) : List Nat → List Nat
  | [] => [i]
  | j :: m => if Nat.ble i j then i :: j :: m else j :: insM i m

def sortM : List Nat → List Nat
  | [] => []
  | i :: m => insM i (sortM m)

def lexLe : List Nat → List Nat → Bool
  | [], _ => true
  | _ :: _, [] => false
  | i :: m, j :: n => if i = j then lexLe m n else Nat.ble i j

def insP (m : List Nat) : List (List Nat) → List (List Nat)
  | [] => [m]
  | n :: P => if lexLe m n then m :: n :: P else n :: insP m P

def sortP : List (List Nat) → List (List Nat)
  | [] => []
  | m :: P => insP m (sortP P)

def nfP : List (List Nat) → List (List Nat)
  | [] => []
  | m :: P => insP (sortM m) (nfP P)

theorem mEval_append (env : Nat → Shell p) (m n : List Nat) : mEval env (m ++ n) = mEval env m * mEval env n := by
  induction m with
  | nil => exact (one_mul _).symm
  | cons i m ih => show env i * mEval env (m ++ n) = env i * mEval env m * mEval env n; rw [ih, mul_assoc]

theorem pEval_append (env : Nat → Shell p) (P Q : List (List Nat)) : pEval env (P ++ Q) = pEval env P + pEval env Q := by
  induction P with
  | nil => exact (zero_add _).symm
  | cons m P ih => show mEval env m + pEval env (P ++ Q) = mEval env m + pEval env P + pEval env Q; rw [ih, add_assoc]

theorem pEval_row (env : Nat → Shell p) (m : List Nat) (Q : List (List Nat)) : pEval env (pRow m Q) = mEval env m * pEval env Q := by
  induction Q with
  | nil => exact (mul_zero _).symm
  | cons n Q ih =>
    show mEval env (m ++ n) + pEval env (pRow m Q) = mEval env m * (mEval env n + pEval env Q)
    rw [ih, mEval_append, left_distrib]

theorem pEval_mul (env : Nat → Shell p) (P Q : List (List Nat)) : pEval env (pMul P Q) = pEval env P * pEval env Q := by
  induction P with
  | nil => exact (zero_mul _).symm
  | cons m P ih =>
    show pEval env (pRow m Q ++ pMul P Q) = (mEval env m + pEval env P) * pEval env Q
    rw [pEval_append, pEval_row, ih, right_distrib]

theorem ring_add (A B C D : Shell p) : A + -B + (C + -D) = A + C + -(B + D) := by
  rw [neg_add_rev, add_assoc, add_assoc, add_left_comm (-B) C (-D)]

theorem ring_mul (A B C D : Shell p) : (A + -B) * (C + -D) = A * C + B * D + -(A * D + B * C) := by
  rw [right_distrib, left_distrib, left_distrib, ← mul_neg, ← neg_mul, neg_mul_neg, neg_add_rev, add_assoc, add_assoc]
  refine congrArg (A * C + ·) ?_
  rw [add_comm (-(B * C)) (B * D), add_left_comm]

theorem ring_neg (A B : Shell p) : -(A + -B) = B + -A := by rw [neg_add_rev, neg_neg, add_comm]

theorem RE.toP_eval (env : Nat → Shell p) (e : RE) : e.eval env = pEval env e.toP.1 + -(pEval env e.toP.2) := by
  induction e with
  | var i =>
    show env i = (env i * 1 + 0) + -(0 : Shell p)
    rw [mul_one, add_zero, neg_zero, add_zero]
  | zero => show (0 : Shell p) = 0 + -0; rw [neg_zero, add_zero]
  | one => show (1 : Shell p) = (1 + 0) + -(0 : Shell p); rw [add_zero, neg_zero, add_zero]
  | add a b iha ihb =>
    show a.eval env + b.eval env = pEval env (a.toP.1 ++ b.toP.1) + -(pEval env (a.toP.2 ++ b.toP.2))
    rw [iha, ihb, pEval_append, pEval_append, ring_add]
  | mul a b iha ihb =>
    show a.eval env * b.eval env = pEval env (pMul a.toP.1 b.toP.1 ++ pMul a.toP.2 b.toP.2) +
      -(pEval env (pMul a.toP.1 b.toP.2 ++ pMul a.toP.2 b.toP.1))
    rw [iha, ihb, pEval_append, pEval_append, pEval_mul, pEval_mul, pEval_mul, pEval_mul, ring_mul]
  | neg a iha =>
    show -(a.eval env) = pEval env a.toP.2 + -(pEval env a.toP.1)
    rw [iha, ring_neg]

theorem mEval_insM (env : Nat → Shell p) (i : Nat) (m : List Nat) : mEval env (insM i m) = env i * mEval env m := by
  induction m with
  | nil => rfl
  | cons j m ih =>
    show mEval env (if Nat.ble i j then i :: j :: m else j :: insM i m) = env i * (env j * mEval env m)
    cases Nat.ble i j with
    | true => rfl
    | false => show env j * mEval env (insM i m) = _; rw [ih, mul_left_comm]

theorem mEval_sortM (env : Nat → Shell p) (m : List Nat) : mEval env (sortM m) = mEval env m := by
  induction m with
  | nil => rfl
  | cons i m ih => show mEval env (insM i (sortM m)) = env i * mEval env m; rw [mEval_insM, ih]

theorem pEval_insP (env : Nat → Shell p) (m : List Nat) (P : List (List Nat)) : pEval env (insP m P) = mEval env m + pEval env P := by
  induction P with
  | nil => rfl
  | cons n P ih =>
    show pEval env (if lexLe m n then m :: n :: P else n :: insP m P) = mEval env m + (mEval env n + pEval env P)
    cases lexLe m n with
    | true => rfl
    | false => show mEval env n + pEval env (insP m P) = _; rw [ih, add_left_comm]

theorem pEval_nfP (env : Nat → Shell p) (P : List (List Nat)) : pEval env (nfP P) = pEval env P := by
  induction P with
  | nil => rfl
  | cons m P ih => show pEval env (insP (sortM m) (nfP P)) = mEval env m + pEval env P; rw [pEval_insP, ih, mEval_sortM]

def nbeq : List Nat → List Nat → Bool
  | [], [] => true
  | [], _ :: _ => false
  | _ :: _, [] => false
  | i :: m, j :: n => Nat.beq i j && nbeq m n

def pbeq : List (List Nat) → List (List Nat) → Bool
  | [], [] => true
  | [], _ :: _ => false
  | _ :: _, [] => false
  | m :: P, n :: Q => nbeq m n && pbeq P Q

theorem and_true_left {a b : Bool} (h : (a && b) = true) : a = true := by
  cases a with
  | false => exact absurd h (fun h' => Bool.noConfusion h')
  | true => rfl

theorem and_true_right {a b : Bool} (h : (a && b) = true) : b = true := by
  cases a with
  | false => exact absurd h (fun h' => Bool.noConfusion h')
  | true => exact h

theorem nbeq_eq : ∀ {m n : List Nat}, nbeq m n = true → m = n
  | [], [], _ => rfl
  | i :: m, j :: n, h => by
    have e1 : i = j := Nat.eq_of_beq_eq_true (and_true_left h)
    have e2 : m = n := nbeq_eq (and_true_right h)
    rw [e1, e2]
  | [], _ :: _, h => Bool.noConfusion h
  | _ :: _, [], h => Bool.noConfusion h

theorem pbeq_eq : ∀ {P Q : List (List Nat)}, pbeq P Q = true → P = Q
  | [], [], _ => rfl
  | m :: P, n :: Q, h => by
    have e1 : m = n := nbeq_eq (and_true_left h)
    have e2 : P = Q := pbeq_eq (and_true_right h)
    rw [e1, e2]
  | [], _ :: _, h => Bool.noConfusion h
  | _ :: _, [], h => Bool.noConfusion h

/-- The normaliser's soundness: if the two cross lists agree after normalisation, the two sides are equal on
every assignment of shell values to the variables. -/
theorem RE.sound (env : Nat → Shell p) (l r : RE) (hb : pbeq (nfP (l.toP.1 ++ r.toP.2)) (nfP (r.toP.1 ++ l.toP.2)) = true) :
    l.eval env = r.eval env := by
  have h := pbeq_eq hb
  have h1 : pEval env l.toP.1 + pEval env r.toP.2 = pEval env r.toP.1 + pEval env l.toP.2 := by
    rw [← pEval_append, ← pEval_append, ← pEval_nfP env (l.toP.1 ++ r.toP.2), ← pEval_nfP env (r.toP.1 ++ l.toP.2), h]
  rw [RE.toP_eval env l, RE.toP_eval env r]
  apply add_right_cancel (c := pEval env l.toP.2 + pEval env r.toP.2)
  rw [← add_assoc, add_assoc (pEval env l.toP.1), neg_add, add_zero,
      ← add_assoc, add_comm (pEval env r.toP.1 + -(pEval env r.toP.2)) (pEval env l.toP.2), ← add_assoc,
      add_comm (pEval env l.toP.2) (pEval env r.toP.1), add_assoc, neg_add, add_zero, h1]

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

def RE.check (l r : RE) : Bool := pbeq (nfP (l.toP.1 ++ r.toP.2)) (nfP (r.toP.1 ++ l.toP.2))
def QR.check (l r : QR) : Bool := RE.check l.a r.a && RE.check l.b r.b && (RE.check l.c r.c && RE.check l.d r.d)

theorem QR.sound (env : Nat → Shell p) (l r : QR) (h : QR.check l r = true) : l.eval env = r.eval env :=
  Quat.ext4 (RE.sound env _ _ (and_true_left (and_true_left h))) (RE.sound env _ _ (and_true_right (and_true_left h)))
    (RE.sound env _ _ (and_true_left (and_true_right h))) (RE.sound env _ _ (and_true_right (and_true_right h)))

/-! ## 1:E7 — the Lie-algebra layer, one axis -/

/-- 1:E7, conjugation keeps a pure quaternion pure: the scalar part of `q x q̄` vanishes. -/
theorem rot_pure (q x : Quat p) (hx : x.a = 0) : (Quat.conjBy q x).a = 0 := by
  rw [Quat.pure_eq hx]
  exact RE.sound (look [q.a, q.b, q.c, q.d, x.b, x.c, x.d]) (QR.conjBy (QR.v 0) (QR.pv 4)).a .zero (by decide +kernel)

/-- 1:E7, the Cayley form cleared of the norm: for `q = a + v` and a pure `x`, the conjugate `y = q x q̄` satisfies
`(aI − S_v) y = N(q) (aI + S_v) x`, where `S_v x = v × x`. -/
theorem rot_cayley (q x : Quat p) (hx : x.a = 0) :
    Quat.add (Quat.smul q.a (Quat.conjBy q x)) (Quat.neg (Quat.cross (Quat.vec q) (Quat.conjBy q x))) =
      Quat.smul (Quat.nrm q) (Quat.add (Quat.smul q.a x) (Quat.cross (Quat.vec q) x)) := by
  rw [Quat.pure_eq hx]
  exact QR.sound (look [q.a, q.b, q.c, q.d, x.b, x.c, x.d])
    (QR.add (QR.smul (.var 0) (QR.conjBy (QR.v 0) (QR.pv 4))) (QR.neg (QR.cross (QR.vec (QR.v 0)) (QR.conjBy (QR.v 0) (QR.pv 4)))))
    (QR.smul (QR.nrm (QR.v 0)) (QR.add (QR.smul (.var 0) (QR.pv 4)) (QR.cross (QR.vec (QR.v 0)) (QR.pv 4)))) (by decide +kernel)

/-- 1:E7, the half-turn: for pure `v` and `x`, `v x v̄ = N(v) x + 2 v × (v × x)`, so `ρ_v = I + 2N(v)⁻¹ S_v²`. -/
theorem half_turn (v x : Quat p) (hv : v.a = 0) (hx : x.a = 0) :
    Quat.conjBy v x = Quat.add (Quat.smul (Quat.nrm v) x) (Quat.add (Quat.cross v (Quat.cross v x)) (Quat.cross v (Quat.cross v x))) := by
  rw [Quat.pure_eq hv, Quat.pure_eq hx]
  exact QR.sound (look [v.b, v.c, v.d, x.b, x.c, x.d])
    (QR.conjBy (QR.pv 0) (QR.pv 3))
    (QR.add (QR.smul (QR.nrm (QR.pv 0)) (QR.pv 3)) (QR.add (QR.cross (QR.pv 0) (QR.cross (QR.pv 0) (QR.pv 3))) (QR.cross (QR.pv 0) (QR.cross (QR.pv 0) (QR.pv 3))))) (by decide +kernel)

/-- 1:E7, the key identity of uniqueness: with `w = a z − v × z`, `a (a² + N(v)) z = a² w + a (v × w) + (v · w) v`. -/
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

/-- 1:E7, `aI − S_v` is injective on pure quaternions when `a ≠ 0` and `a² + N(v) ≠ 0` (a field shell). -/
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

/-! ## 1:E8 — the Lie-algebra layer, two axes and range -/

/-- 1:E8, the product of two Gibbs quaternions: `(1 + u)(1 + w) = (1 − u·w) + (u + w + u × w)` for pure `u`, `w`. -/
theorem one_add_mul (u w : Quat p) (hu : u.a = 0) (hw : w.a = 0) :
    Quat.mul (Quat.add (Quat.sc 1) u) (Quat.add (Quat.sc 1) w) =
      Quat.add (Quat.sc (1 + -(Quat.dot u w))) (Quat.add (Quat.add u w) (Quat.cross u w)) := by
  rw [Quat.pure_eq hu, Quat.pure_eq hw]
  exact QR.sound (look [u.b, u.c, u.d, w.b, w.c, w.d])
    (QR.mul (QR.add (QR.sc .one) (QR.pv 0)) (QR.add (QR.sc .one) (QR.pv 3)))
    (QR.add (QR.sc (.add .one (.neg (QR.dot (QR.pv 0) (QR.pv 3))))) (QR.add (QR.add (QR.pv 0) (QR.pv 3)) (QR.cross (QR.pv 0) (QR.pv 3)))) (by decide +kernel)

/-- 1:E8, the bracket: `uw − wu = 2 u × w` for pure `u`, `w`. -/
theorem bracket (u w : Quat p) (hu : u.a = 0) (hw : w.a = 0) :
    Quat.add (Quat.mul u w) (Quat.neg (Quat.mul w u)) = Quat.add (Quat.cross u w) (Quat.cross u w) := by
  rw [Quat.pure_eq hu, Quat.pure_eq hw]
  exact QR.sound (look [u.b, u.c, u.d, w.b, w.c, w.d])
    (QR.add (QR.mul (QR.pv 0) (QR.pv 3)) (QR.neg (QR.mul (QR.pv 3) (QR.pv 0)))) (QR.add (QR.cross (QR.pv 0) (QR.pv 3)) (QR.cross (QR.pv 0) (QR.pv 3))) (by decide +kernel)

/-- 1:E8, conjugation is multiplicative: `(qr) x (qr)‾ = q (r x r̄) q̄`. -/
theorem rot_mul (q r x : Quat p) : Quat.conjBy (Quat.mul q r) x = Quat.conjBy q (Quat.conjBy r x) :=
  QR.sound (look [q.a, q.b, q.c, q.d, r.a, r.b, r.c, r.d, x.a, x.b, x.c, x.d]) (QR.conjBy (QR.mul (QR.v 0) (QR.v 4)) (QR.v 8))
    (QR.conjBy (QR.v 0) (QR.conjBy (QR.v 4) (QR.v 8))) (by decide +kernel)

/-- 1:E8, the norm is multiplicative: `N(qr) = N(q) N(r)`. -/
theorem nrm_mul (q r : Quat p) : Quat.nrm (Quat.mul q r) = Quat.nrm q * Quat.nrm r :=
  RE.sound (look [q.a, q.b, q.c, q.d, r.a, r.b, r.c, r.d]) (QR.nrm (QR.mul (QR.v 0) (QR.v 4))) (.mul (QR.nrm (QR.v 0)) (QR.nrm (QR.v 4))) (by decide +kernel)

/-- 1:E8, scaling: `(sq) x (sq)‾ = s² q x q̄` and `N(sq) = s² N(q)`, so the rotation of `q` depends on `q` up to a scalar. -/
theorem rot_smul (s : Shell p) (q x : Quat p) :
    Quat.conjBy (Quat.smul s q) x = Quat.smul (s * s) (Quat.conjBy q x) ∧ Quat.nrm (Quat.smul s q) = s * s * Quat.nrm q :=
  ⟨QR.sound (look [s, q.a, q.b, q.c, q.d, x.a, x.b, x.c, x.d]) (QR.conjBy (QR.smul (.var 0) (QR.v 1)) (QR.v 5))
      (QR.smul (.mul (.var 0) (.var 0)) (QR.conjBy (QR.v 1) (QR.v 5))) (by decide +kernel),
   RE.sound (look [s, q.a, q.b, q.c, q.d]) (QR.nrm (QR.smul (.var 0) (QR.v 1))) (.mul (.mul (.var 0) (.var 0)) (QR.nrm (QR.v 1))) (by decide +kernel)⟩

/-- 1:E8, the half-turn case: at `u · w = 1` the product `(1 + u)(1 + w)` is the pure quaternion `u + w + u × w`. -/
theorem one_add_mul_half (u w : Quat p) (hu : u.a = 0) (hw : w.a = 0) (h1 : Quat.dot u w = 1) :
    Quat.mul (Quat.add (Quat.sc 1) u) (Quat.add (Quat.sc 1) w) = Quat.add (Quat.sc 0) (Quat.add (Quat.add u w) (Quat.cross u w)) := by
  rw [one_add_mul u w hu hw, h1, add_neg]

/-- 1:E7, the sign: `ρ_{−q} = ρ_q` (`(−q) x (−q)‾ = q x q̄`, `N(−q) = N(q)`); the window rotations of an axis come in
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

/-- 1:E8, the composition law: for pure `u`, `w` with `1 + N(u)`, `1 + N(w)`, `1 − u·w` and `1 + N(u∘w)` invertible
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

/-- 1:E7, the kernel: on a field shell, a rotation `ρ_q` (`N(q) ≠ 0`) that fixes every pure quaternion has `q` a
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

end Frame
end Shell
end FRC

namespace FRC.Algebra
-- Ledger predicates of 1-algebra (generated by make_predicates.py from docs/1-algebra/1-algebra-ledger.json; edit the ledger, not this section)
set_option linter.defProp false in
/-- 1:E6 (p01030) — Continuous symmetry, the non-abelian case resolved by the window: the framed quaternions $W_H^{4}$, read in a shell $\p>8H^{2}$, compose exactly (products land in $W_{4H^{2}}$); normalised, they are an $\varepsilon$-net of $SO(3)$ with $\varepsilon\le2\arcsin(1/H)$ (round $Hs$ to the lattice). At $H=3$, $\p=73$: $38.9^\circ<\varepsilon_0$, finer than any finite subgroup; measured $30.0^\circ$. -/
def p01030 := And.intro @FRC.Shell.Frame.quaternion_window (@FRC.Shell.Frame.read_mul)
/-- 1:E7 (p01032) — The Lie-algebra layer, one axis: on a shell $\p>8H^{2}$, for $q=a+v\in W_H^{4}$ with $v\ne0$, the rotation $\rho_q\colon x\mapsto qxq^{-1}$ is the Cayley step (8:C3) of the self-adjoint $\eta S_v$ (E2's $\eta$, $S_vx=v\times x$, $N(v)=v\cdot v$) at $\alpha=\eta/(\nu a)$, and the half-turn $U_\infty=I+2N(v)^{-1}S_v^{2}$ at $a=0$. With $U_\infty$ these steps form a cyclic group of order $\p-\bigl(\tfrac{N(v)}{\p}\bigr)$ containing every iterate; at most $2H^{2}+2H$ of its elements are window rotations. -/
theorem p01032 : (∀ {p : Nat} [FRC.Pos p] (q x : FRC.Shell.Frame.Quat p), x.a = (0 : FRC.Shell p) → (FRC.Shell.Frame.Quat.smul q.a (q.conjBy x)).add (q.vec.cross (q.conjBy x)).neg = FRC.Shell.Frame.Quat.smul q.nrm ((FRC.Shell.Frame.Quat.smul q.a x).add (q.vec.cross x))) ∧ (∀ {p : Nat} [FRC.Pos p] {κ : Nat} {g : FRC.Shell p}, FRC.Shell.Frame p κ g → ∀ {a : FRC.Shell p} {v z : FRC.Shell.Frame.Quat p}, v.a = (0 : FRC.Shell p) → z.a = (0 : FRC.Shell p) → a ≠ (0 : FRC.Shell p) → a * a + v.dot v ≠ (0 : FRC.Shell p) → FRC.Shell.Frame.Quat.smul a z = v.cross z → z = { a := (0 : FRC.Shell p), b := (0 : FRC.Shell p), c := (0 : FRC.Shell p), d := (0 : FRC.Shell p) }) ∧ (∀ {p : Nat} [FRC.Pos p] (v x : FRC.Shell.Frame.Quat p), v.a = (0 : FRC.Shell p) → x.a = (0 : FRC.Shell p) → v.conjBy x = (FRC.Shell.Frame.Quat.smul v.nrm x).add ((v.cross (v.cross x)).add (v.cross (v.cross x)))) ∧ (∀ {p : Nat} [FRC.Pos p] {κ : Nat} {g : FRC.Shell p}, FRC.Shell.Frame p κ g → ∀ (q : FRC.Shell.Frame.Quat p), q.nrm ≠ (0 : FRC.Shell p) → (∀ (x : FRC.Shell.Frame.Quat p), x.a = (0 : FRC.Shell p) → q.conjBy x = FRC.Shell.Frame.Quat.smul q.nrm x) → q.b = (0 : FRC.Shell p) ∧ q.c = (0 : FRC.Shell p) ∧ q.d = (0 : FRC.Shell p)) ∧ ∀ {p : Nat} [FRC.Pos p] (q x : FRC.Shell.Frame.Quat p), q.neg.conjBy x = q.conjBy x ∧ q.neg.nrm = q.nrm :=
  And.intro @FRC.Shell.Frame.rot_cayley (And.intro @FRC.Shell.Frame.cayley_inj (And.intro @FRC.Shell.Frame.half_turn (And.intro @FRC.Shell.Frame.rot_trivial (@FRC.Shell.Frame.rot_neg))))
/-- 1:E8 (p01033) — The Lie-algebra layer, two axes and range: for pure quaternions $u,w$ with $1+N(u)$, $1+N(w)$ and $1-u\cdot w$ nonzero, $\rho_{1+u}\rho_{1+w}=\rho_{1+u\circ w}$ with $u\circ w=(u+w+u\times w)/(1-u\cdot w)$, the bracket being $[u,w]=2u\times w$; at $u\cdot w=1$ the product is the half-turn about $u+w+u\times w$. The entries of $q^{m}$, $q\in W_H^{4}$, are at most $(2H)^{m}$, and $q^{m}$ reads back from the shell iff $2\|q^{m}\|_\infty<\p$ (D2). -/
theorem p01033 : (∀ {p : Nat} [FRC.Pos p] (u w x : FRC.Shell.Frame.Quat p), u.a = (0 : FRC.Shell p) → w.a = (0 : FRC.Shell p) → ∀ (s' nu nw nc : FRC.Shell p), ((1 : FRC.Shell p) + -u.dot w) * s' = (1 : FRC.Shell p) → ((FRC.Shell.Frame.Quat.sc (1 : FRC.Shell p)).add u).nrm * nu = (1 : FRC.Shell p) → ((FRC.Shell.Frame.Quat.sc (1 : FRC.Shell p)).add w).nrm * nw = (1 : FRC.Shell p) → ((FRC.Shell.Frame.Quat.sc (1 : FRC.Shell p)).add (FRC.Shell.Frame.Quat.smul s' ((u.add w).add (u.cross w)))).nrm * nc = (1 : FRC.Shell p) → FRC.Shell.Frame.Quat.smul nu (((FRC.Shell.Frame.Quat.sc (1 : FRC.Shell p)).add u).conjBy (FRC.Shell.Frame.Quat.smul nw (((FRC.Shell.Frame.Quat.sc (1 : FRC.Shell p)).add w).conjBy x))) = FRC.Shell.Frame.Quat.smul nc (((FRC.Shell.Frame.Quat.sc (1 : FRC.Shell p)).add (FRC.Shell.Frame.Quat.smul s' ((u.add w).add (u.cross w)))).conjBy x)) ∧ (∀ {p : Nat} [FRC.Pos p] (u w : FRC.Shell.Frame.Quat p), u.a = (0 : FRC.Shell p) → w.a = (0 : FRC.Shell p) → ((FRC.Shell.Frame.Quat.sc (1 : FRC.Shell p)).add u).mul ((FRC.Shell.Frame.Quat.sc (1 : FRC.Shell p)).add w) = (FRC.Shell.Frame.Quat.sc ((1 : FRC.Shell p) + -u.dot w)).add ((u.add w).add (u.cross w))) ∧ (∀ {p : Nat} [FRC.Pos p] (u w : FRC.Shell.Frame.Quat p), u.a = (0 : FRC.Shell p) → w.a = (0 : FRC.Shell p) → u.dot w = (1 : FRC.Shell p) → ((FRC.Shell.Frame.Quat.sc (1 : FRC.Shell p)).add u).mul ((FRC.Shell.Frame.Quat.sc (1 : FRC.Shell p)).add w) = (FRC.Shell.Frame.Quat.sc (0 : FRC.Shell p)).add ((u.add w).add (u.cross w))) ∧ (∀ {p : Nat} [FRC.Pos p] (u w : FRC.Shell.Frame.Quat p), u.a = (0 : FRC.Shell p) → w.a = (0 : FRC.Shell p) → (u.mul w).add (w.mul u).neg = (u.cross w).add (u.cross w)) ∧ (∀ {p : Nat} [FRC.Pos p] (q r x : FRC.Shell.Frame.Quat p), (q.mul r).conjBy x = q.conjBy (r.conjBy x)) ∧ ∀ {p : Nat} [FRC.Pos p] (q r : FRC.Shell.Frame.Quat p), (q.mul r).nrm = q.nrm * r.nrm :=
  And.intro @FRC.Shell.Frame.compose (And.intro @FRC.Shell.Frame.one_add_mul (And.intro @FRC.Shell.Frame.one_add_mul_half (And.intro @FRC.Shell.Frame.bracket (And.intro @FRC.Shell.Frame.rot_mul (@FRC.Shell.Frame.nrm_mul)))))
-- end ledger predicates
end FRC.Algebra
