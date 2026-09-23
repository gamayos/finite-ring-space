import FrcCore.Algebra

/-!
# FrcCore.Quaternion — the framed quaternions and the window (1:G5, the finitary clause)

A signed window integer is a pair of naturals `(u, v)` read as `u − v` in the shell (no `Int`: the core's
integers are the shell's own readings).  A framed quaternion is four such pairs; the Hamilton product is
computed on the pairs, and `read_mul` says the product of the readings is the reading of the product — the
composition is exact.  `quaternion_window` adds the bounds: with coordinates in the window `H` and a shell
`p > 8H²`, the product's coordinates lie in the window `4H²`, and the shell reading determines the integer
product among the window's quaternions.  No axioms.
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

/-- 1:G5, exact composition — the reading of the integer product is the product of the readings. -/
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

/-- 1:G5, the finitary clause — framed quaternions with window coordinates `≤ H`, read in a shell `p > 8H²`,
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

end Frame
end Shell
end FRC

namespace FRC.Algebra
-- Ledger predicates of 1-algebra (generated by make_predicates.py from docs/1-algebra/1-algebra-ledger.json; edit the ledger, not this section)
set_option linter.defProp false in
/-- 1:G5 (p01030) — Continuous symmetry, the non-abelian case resolved by the window: the framed quaternions $W_H^{4}$, read in a shell $\p>8H^{2}$, compose exactly (products land in $W_{4H^{2}}$); normalised, they are an $\varepsilon$-net of $SO(3)$ with $\varepsilon\le2\arcsin(1/H)$ (round $Hs$ to the lattice). At $H=3$, $\p=73$: $38.9^\circ<\varepsilon_0$, finer than any finite subgroup; measured $30.0^\circ$. -/
def p01030 := And.intro @FRC.Shell.Frame.quaternion_window (@FRC.Shell.Frame.read_mul)
-- end ledger predicates
end FRC.Algebra
