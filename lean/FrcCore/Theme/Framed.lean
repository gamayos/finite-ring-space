import FrcCore.Frame
import FrcCore.Orbit
import FrcCore.Ring
import FrcCore.Theme.Field
import FrcCore.Theme.Foundation

/-!
# FrcCore.Theme.Framed — framed integers and framed rationals on the window (the algebra theme)

The algebra theme holds 1-algebra's exact content above the frame and the foundation (6 November 2026). This file:

* the signed window integers `SInt` (a pair `(u, v)` read as `u − v`; no `Int`), their reading `sread`, the window
  bound `SBound`, and the signed window law `sread_inj` — moved here from the paper module `FrcCore/Quaternion.lean`,
  every name unchanged;
* the window law for framed rationals (1:D8): fractions `a/b` with `|a| ≤ N`, `1 ≤ b ≤ D` and `2ND < p` that read as
  the same residue are the same fraction (`frac_window`, `frac_window_inv`), so the products and the sums of window
  fractions read back on the windows `(H², H²)` and `(2H², H²)` (`frac_mul_readback`, `frac_add_readback`);
* the scale grid covers the shell (1:D9): every residue is `t · B⁻¹` for exactly one `t` with `|t| ≤ 2κ`
  (`signed_rep`, `signed_rep_unique`, `grid_cover`, `grid_unique`), and the nonzero residues form `2κ` sign pairs
  (`sign_pair`; 1:C4 with `vertex_count`);
* the complex chart is a field exactly off the shells (1:E2): on a prime `p ≡ 3 (mod 4)` every nonzero pair of
  `F_p[X]/(X² + 1)` is invertible (`complex_chart_field`);
* scale-periodicity made exact (1:D4): the grid `x · g^{−n}` returns to a nonzero point exactly when the scales
  agree modulo `p − 1`, the zoom has order exactly `p − 1`, and every grid lists the whole shell once;
* the circle in counts (1:E4): the rounding of a framed turn `u/v` to the cycle of `N` steps is within half a step,
  and the rounding's group-law defect is `−1`, `0` or `1` (`round_bounds`, `round_defect`).

No axioms.
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


/-! ## Framed rationals: the window law (1:D8) -/

/-- A natural number as a signed window integer reads as itself. -/
theorem sread_nat (b : Nat) : (sread (b, 0) : Shell p) = ofNat b := by
  unfold sread
  show ofNat b + -(ofNat 0 : Shell p) = ofNat b
  have e0 : (ofNat 0 : Shell p) = 0 := rfl
  rw [e0, neg_zero, add_zero]

theorem nat_bound {D b : Nat} (hb : b ≤ D) : SBound D (b, 0) := ⟨hb, Nat.zero_le D, Or.inr rfl⟩

/-- The product of window integers of sizes `N` and `D` is a window integer of size `N·D`. -/
theorem smul_bound2 {N D : Nat} {x y : SInt} (hx : SBound N x) (hy : SBound D y) : SBound (N * D) (smul x y) := by
  unfold smul
  have b11 := Nat.mul_le_mul hx.1 hy.1
  have b22 := Nat.mul_le_mul hx.2.1 hy.2.1
  have b12 := Nat.mul_le_mul hx.1 hy.2.1
  have b21 := Nat.mul_le_mul hx.2.1 hy.1
  match hx.2.2, hy.2.2 with
  | Or.inl e, Or.inl f =>
    refine ⟨?_, ?_, Or.inr ?_⟩
    · show x.1 * y.1 + x.2 * y.2 ≤ N * D
      rw [e, Nat.zero_mul, Nat.zero_add]; exact b22
    · show x.1 * y.2 + x.2 * y.1 ≤ N * D
      rw [e, f, Nat.zero_mul, Nat.mul_zero]; exact Nat.zero_le _
    · show x.1 * y.2 + x.2 * y.1 = 0
      rw [e, f, Nat.zero_mul, Nat.mul_zero]
  | Or.inl e, Or.inr f =>
    refine ⟨?_, ?_, Or.inl ?_⟩
    · show x.1 * y.1 + x.2 * y.2 ≤ N * D
      rw [e, f, Nat.zero_mul, Nat.mul_zero]; exact Nat.zero_le _
    · show x.1 * y.2 + x.2 * y.1 ≤ N * D
      rw [e, Nat.zero_mul, Nat.zero_add]; exact b21
    · show x.1 * y.1 + x.2 * y.2 = 0
      rw [e, f, Nat.zero_mul, Nat.mul_zero]
  | Or.inr e, Or.inl f =>
    refine ⟨?_, ?_, Or.inl ?_⟩
    · show x.1 * y.1 + x.2 * y.2 ≤ N * D
      rw [e, f, Nat.mul_zero, Nat.zero_mul]; exact Nat.zero_le _
    · show x.1 * y.2 + x.2 * y.1 ≤ N * D
      rw [e, Nat.zero_mul, Nat.add_zero]; exact b12
    · show x.1 * y.1 + x.2 * y.2 = 0
      rw [e, f, Nat.mul_zero, Nat.zero_mul]
  | Or.inr e, Or.inr f =>
    refine ⟨?_, ?_, Or.inr ?_⟩
    · show x.1 * y.1 + x.2 * y.2 ≤ N * D
      rw [e, Nat.zero_mul, Nat.add_zero]; exact b11
    · show x.1 * y.2 + x.2 * y.1 ≤ N * D
      rw [e, f, Nat.mul_zero, Nat.zero_mul]; exact Nat.zero_le _
    · show x.1 * y.2 + x.2 * y.1 = 0
      rw [e, f, Nat.mul_zero, Nat.zero_mul]

/-- 1:D8, the window law for framed rationals — two fractions `a₁/b₁`, `a₂/b₂` with `|aᵢ| ≤ N`, `bᵢ ≤ D` and
`2ND < p` whose cross-products agree on the shell, `a₁ b₂ ≡ a₂ b₁`, are the same fraction: `a₁ b₂ = a₂ b₁` as
integers. -/
theorem frac_window {N D : Nat} (hND : 2 * (N * D) < p) {a₁ a₂ : SInt} {b₁ b₂ : Nat}
    (ha₁ : SBound N a₁) (ha₂ : SBound N a₂) (hb₁ : b₁ ≤ D) (hb₂ : b₂ ≤ D)
    (h : (sread a₁ : Shell p) * ofNat b₂ = sread a₂ * ofNat b₁) :
    smul a₁ (b₂, 0) = smul a₂ (b₁, 0) := by
  apply sread_inj hND (smul_bound2 ha₁ (nat_bound hb₂)) (smul_bound2 ha₂ (nat_bound hb₁))
  rw [sread_mul, sread_mul, sread_nat, sread_nat]; exact h

/-- 1:D8, in the residues of the fractions — `a₁ · b₁⁻¹ = a₂ · b₂⁻¹` on the shell, with the window bounds and
`2ND < p`, forces `a₁ b₂ = a₂ b₁`: distinct window fractions take distinct residues. -/
theorem frac_window_inv {N D : Nat} (hND : 2 * (N * D) < p) {a₁ a₂ : SInt} {b₁ b₂ : Nat} {y₁ y₂ : Shell p}
    (ha₁ : SBound N a₁) (ha₂ : SBound N a₂) (hb₁ : b₁ ≤ D) (hb₂ : b₂ ≤ D)
    (hy₁ : (ofNat b₁ : Shell p) * y₁ = 1) (hy₂ : (ofNat b₂ : Shell p) * y₂ = 1)
    (h : (sread a₁ : Shell p) * y₁ = sread a₂ * y₂) :
    smul a₁ (b₂, 0) = smul a₂ (b₁, 0) := by
  apply frac_window hND ha₁ ha₂ hb₁ hb₂
  calc (sread a₁ : Shell p) * ofNat b₂ = sread a₁ * (ofNat b₁ * y₁) * ofNat b₂ := by rw [hy₁, mul_one]
    _ = (sread a₁ * y₁) * (ofNat b₁ * ofNat b₂) :=
        RE.sound (look [sread a₁, ofNat b₁, y₁, ofNat b₂]) (.mul (.mul (.var 0) (.mul (.var 1) (.var 2))) (.var 3))
          (.mul (.mul (.var 0) (.var 2)) (.mul (.var 1) (.var 3))) (by decide +kernel)
    _ = (sread a₂ * y₂) * (ofNat b₁ * ofNat b₂) := by rw [h]
    _ = (sread a₂ * ofNat b₁) * (ofNat b₂ * y₂) :=
        RE.sound (look [sread a₂, y₂, ofNat b₁, ofNat b₂]) (.mul (.mul (.var 0) (.var 1)) (.mul (.var 2) (.var 3)))
          (.mul (.mul (.var 0) (.var 2)) (.mul (.var 3) (.var 1))) (by decide +kernel)
    _ = sread a₂ * ofNat b₁ := by rw [hy₂, mul_one]

/-- 1:D8, products read back — for window fractions `a/b`, `c/d` (`|a|, |c|, b, d ≤ H`) the product `ac/bd` lies
in the window `(H², H²)`; when `2H⁴ < p` the residue of the product determines it among that window's fractions
`e/f`. -/
theorem frac_mul_readback {H : Nat} (hH : 2 * ((H * H) * (H * H)) < p) {a c e : SInt} {b d f : Nat}
    {yb yd yf : Shell p} (ha : SBound H a) (hc : SBound H c) (hb : b ≤ H) (hd : d ≤ H)
    (he : SBound (H * H) e) (hf : f ≤ H * H)
    (hyb : (ofNat b : Shell p) * yb = 1) (hyd : (ofNat d : Shell p) * yd = 1) (hyf : (ofNat f : Shell p) * yf = 1)
    (h : (sread a * yb) * (sread c * yd) = (sread e : Shell p) * yf) :
    smul (smul a c) (f, 0) = smul e (b * d, 0) := by
  have hbd : (ofNat (b * d) : Shell p) * (yb * yd) = 1 := by
    rw [← ofNat_mul]
    calc (ofNat b : Shell p) * ofNat d * (yb * yd) = (ofNat b * yb) * (ofNat d * yd) :=
          RE.sound (look [ofNat b, ofNat d, yb, yd]) (.mul (.mul (.var 0) (.var 1)) (.mul (.var 2) (.var 3)))
            (.mul (.mul (.var 0) (.var 2)) (.mul (.var 1) (.var 3))) (by decide +kernel)
      _ = 1 := by rw [hyb, hyd, mul_one]
  apply frac_window_inv hH (smul_bound ha hc) he (Nat.mul_le_mul hb hd) hf hbd hyf
  rw [sread_mul]
  rw [← h]
  exact RE.sound (look [sread a, sread c, yb, yd]) (.mul (.mul (.var 0) (.var 1)) (.mul (.var 2) (.var 3)))
    (.mul (.mul (.var 0) (.var 2)) (.mul (.var 1) (.var 3))) (by decide +kernel)

/-- 1:D8, sums read back — for window fractions `a/b`, `c/d` the sum `(ad + cb)/bd` lies in the window
`(2H², H²)`; when `4H⁴ < p` its residue determines it among that window's fractions `e/f`. -/
theorem frac_add_readback {H : Nat} (hH : 2 * ((H * H + H * H) * (H * H)) < p) {a c e : SInt} {b d f : Nat}
    {yb yd yf : Shell p} (ha : SBound H a) (hc : SBound H c) (hb : b ≤ H) (hd : d ≤ H)
    (he : SBound (H * H + H * H) e) (hf : f ≤ H * H)
    (hyb : (ofNat b : Shell p) * yb = 1) (hyd : (ofNat d : Shell p) * yd = 1) (hyf : (ofNat f : Shell p) * yf = 1)
    (h : sread a * yb + sread c * yd = (sread e : Shell p) * yf) :
    smul (snorm (sadd (smul a (d, 0)) (smul c (b, 0)))) (f, 0) = smul e (b * d, 0) := by
  have hbd : (ofNat (b * d) : Shell p) * (yb * yd) = 1 := by
    rw [← ofNat_mul]
    calc (ofNat b : Shell p) * ofNat d * (yb * yd) = (ofNat b * yb) * (ofNat d * yd) :=
          RE.sound (look [ofNat b, ofNat d, yb, yd]) (.mul (.mul (.var 0) (.var 1)) (.mul (.var 2) (.var 3)))
            (.mul (.mul (.var 0) (.var 2)) (.mul (.var 1) (.var 3))) (by decide +kernel)
      _ = 1 := by rw [hyb, hyd, mul_one]
  have h1 := smul_bound2 ha (nat_bound hd)
  have h2 := smul_bound2 hc (nat_bound hb)
  have hs : SBound (H * H + H * H) (snorm (sadd (smul a (d, 0)) (smul c (b, 0)))) :=
    snorm_bound (Nat.add_le_add h1.1 h2.1) (Nat.add_le_add h1.2.1 h2.2.1)
  apply frac_window_inv hH hs he (Nat.mul_le_mul hb hd) hf hbd hyf
  rw [sread_norm, sread_add, sread_mul, sread_mul, sread_nat, sread_nat, ← h]
  -- (a d + c b) · (yb yd) = a yb (d yd) + c yd (b yb)
  calc (sread a * ofNat d + sread c * ofNat b) * (yb * yd)
        = sread a * yb * (ofNat d * yd) + sread c * yd * (ofNat b * yb) :=
          RE.sound (look [sread a, ofNat d, sread c, ofNat b, yb, yd])
            (.mul (.add (.mul (.var 0) (.var 1)) (.mul (.var 2) (.var 3))) (.mul (.var 4) (.var 5)))
            (.add (.mul (.mul (.var 0) (.var 4)) (.mul (.var 1) (.var 5))) (.mul (.mul (.var 2) (.var 5)) (.mul (.var 3) (.var 4))))
            (by decide +kernel)
    _ = sread a * yb + sread c * yd := by rw [hyd, hyb, mul_one, mul_one]

/-! ## The scale grid covers the shell (1:D9) and the sign pairs (1:C4) -/

theorem four_eq_two_two (κ : Nat) : 4 * κ = 2 * κ + 2 * κ := by
  rw [four_mul_eq, Nat.two_mul, Nat.add_assoc (κ + κ) κ κ]

omit [Pos p] in
theorem two_two_lt {κ : Nat} (hcap : p = 4 * κ + 1) : 2 * (2 * κ) < p := by
  rw [hcap, Nat.two_mul (2 * κ), ← four_eq_two_two]; exact Nat.lt_succ_self _

/-- 1:D9 — every residue of the shell `p = 4κ + 1` is the reading of exactly one signed window integer of size `2κ`
(existence here, uniqueness `signed_rep_unique`). -/
theorem signed_rep {κ : Nat} (hcap : p = 4 * κ + 1) (x : Shell p) : ∃ t : SInt, SBound (2 * κ) t ∧ (sread t : Shell p) = x := by
  match Nat.decLe x.val (2 * κ) with
  | .isTrue h => exact ⟨(x.val, 0), nat_bound h, by rw [sread_nat, ofNat_val]⟩
  | .isFalse h =>
    have hlt : 2 * κ < x.val := Nat.lt_of_not_le h
    have hxp : x.val ≤ p := Nat.le_of_lt x.lt
    refine ⟨(0, p - x.val), ⟨Nat.zero_le _, ?_, Or.inl rfl⟩, ?_⟩
    · apply FRC.Nat.sub_le_of_le_add
      -- p ≤ 2κ + x.val
      have e : p = 2 * κ + (2 * κ + 1) := by rw [hcap, four_eq_two_two, Nat.add_assoc]
      calc p = 2 * κ + (2 * κ + 1) := e
        _ ≤ 2 * κ + x.val := Nat.add_le_add_left (Nat.succ_le_of_lt hlt) (2 * κ)
    · unfold sread
      show ofNat 0 + -(ofNat (p - x.val)) = x
      have e0 : (ofNat 0 : Shell p) = 0 := rfl
      rw [e0, zero_add]
      have hs : (ofNat (p - x.val) : Shell p) + ofNat x.val = 0 := by
        rw [ofNat_add, FRC.Nat.sub_add_cancel hxp, ofNat_self]
      rw [neg_eq_of_add_eq_zero hs, ofNat_val]

/-- 1:D9, uniqueness — two signed window integers of size `2κ` with the same reading are equal. -/
theorem signed_rep_unique {κ : Nat} (hcap : p = 4 * κ + 1) {t t' : SInt} (ht : SBound (2 * κ) t) (ht' : SBound (2 * κ) t')
    (h : (sread t : Shell p) = sread t') : t = t' :=
  sread_inj (two_two_lt hcap) ht ht' h

/-- 1:D9 — for every unit `B` (`B · y = 1`) the scale grid `t · B⁻¹`, `|t| ≤ 2κ`, covers the shell. -/
theorem grid_cover {κ : Nat} (hcap : p = 4 * κ + 1) {B y : Shell p} (hBy : B * y = 1) (x : Shell p) :
    ∃ t : SInt, SBound (2 * κ) t ∧ (sread t : Shell p) * y = x := by
  obtain ⟨t, ht, hr⟩ := signed_rep hcap (x * B)
  exact ⟨t, ht, by rw [hr, mul_assoc, hBy, mul_one]⟩

/-- 1:D9 — and each residue sits on the grid once: `t · B⁻¹ = t' · B⁻¹` with `|t|, |t'| ≤ 2κ` forces `t = t'`. -/
theorem grid_unique {κ : Nat} (hcap : p = 4 * κ + 1) {B y : Shell p} (hBy : B * y = 1) {t t' : SInt}
    (ht : SBound (2 * κ) t) (ht' : SBound (2 * κ) t') (h : (sread t : Shell p) * y = sread t' * y) : t = t' := by
  apply signed_rep_unique hcap ht ht'
  calc (sread t : Shell p) = sread t * (B * y) := by rw [hBy, mul_one]
    _ = sread t * y * B := by rw [mul_comm B y, mul_assoc]
    _ = sread t' * y * B := by rw [h]
    _ = sread t' := by rw [mul_assoc, mul_comm y B, hBy, mul_one]

/-- 1:C4 — the nonzero residues form `2κ` sign pairs: every `x ≠ 0` is `a` or `−a` for some `1 ≤ a ≤ 2κ`
(the pair is unique by `window_injective` and `window_signed` at `H = 2κ`). -/
theorem sign_pair {κ : Nat} (hcap : p = 4 * κ + 1) {x : Shell p} (hx : x ≠ 0) :
    ∃ a, 0 < a ∧ a ≤ 2 * κ ∧ (x = ofNat a ∨ x = -(ofNat a)) := by
  obtain ⟨t, ht, hr⟩ := signed_rep hcap x
  have e0 : (ofNat 0 : Shell p) = 0 := rfl
  match ht.2.2 with
  | Or.inr e =>
    have hx' : x = ofNat t.1 := by
      rw [← hr]; unfold sread; rw [e, e0, neg_zero, add_zero]
    refine ⟨t.1, Nat.pos_of_ne_zero (fun h0 => hx (by rw [hx', h0]; rfl)), ht.1, Or.inl hx'⟩
  | Or.inl e =>
    have hx' : x = -(ofNat t.2) := by
      rw [← hr]; unfold sread; rw [e, e0, zero_add]
    refine ⟨t.2, Nat.pos_of_ne_zero (fun h0 => hx (by rw [hx', h0, e0, neg_zero])), ht.2.1, Or.inr hx'⟩

/-- 1:C4 — the one-sided vertex count: `(p − 1)² = 2 · (2κ · (p − 1))`, with `p − 1 = 4κ`; the orbital complex has
`2κ(p − 1) + 1` vertices, half its double cover plus the origin. -/
theorem vertex_count (κ : Nat) : (4 * κ) * (4 * κ) = 2 * ((2 * κ) * (4 * κ)) := by
  rw [← FRC.Nat.mul_assoc 2 (2 * κ) (4 * κ), ← FRC.Nat.mul_assoc 2 2 κ]

/-! ## The complex chart off the shells (1:E2) -/

/-- Inverses on a prime shell (Fermat; as `Theme/Hopf.lean`'s `exists_inv`, restated in the algebra theme). -/
theorem inv_of_prime (hp : FRC.Nat.isPrime p) {x : Shell p} (hx : x ≠ 0) : ∃ y, x * y = 1 := by
  refine ⟨x ^ (p - 2), ?_⟩
  have e : p - 1 = (p - 2) + 1 := by
    have h2 : 2 ≤ p := Prime.two_le hp
    have : p = (p - 2) + 2 := (FRC.Nat.sub_add_cancel h2).symm
    rw [this, FRC.Nat.add_sub_cancel]; rfl
  rw [mul_comm, ← pow_succ, ← e]; exact Prime.fermat hp hx

/-- 1:E2, the converse — on a prime `p ≡ 3 (mod 4)` the chart `F_p[X]/(X² + 1)` is a field: every nonzero pair
`(a, b)` has the inverse `(a, −b)/(a² + b²)`, since `a² + b² = 0` with `b ≠ 0` would make `a/b` a square root of `−1`. -/
theorem complex_chart_field (hp : FRC.Nat.isPrime p) (h3 : p % 4 = 3) {x : Shell p × Shell p} (hx : x ≠ (0, 0)) :
    ∃ y, cmul x y = (1, 0) := by
  have h2 : 2 < p := by
    match Nat.lt_or_ge 2 p with
    | Or.inl h => exact h
    | Or.inr h =>
      have hp2 : p = 2 := Nat.le_antisymm h (Prime.two_le hp)
      rw [hp2] at h3; exact absurd h3 (by decide)
  have hn : x.1 * x.1 + x.2 * x.2 ≠ 0 := by
    intro hn
    match decEq x.2 0 with
    | isTrue hb =>
      rw [hb, mul_zero, add_zero] at hn
      have ha : x.1 = 0 := match Prime.mul_eq_zero hp hn with | Or.inl h => h | Or.inr h => h
      exact hx (Prod.ext ha hb)
    | isFalse hb =>
      obtain ⟨yb, hyb⟩ := inv_of_prime hp hb
      have hsq : (x.1 * yb) * (x.1 * yb) = -1 := by
        have ha : x.1 * x.1 = -(x.2 * x.2) := eq_neg_of_add_eq_zero hn
        calc (x.1 * yb) * (x.1 * yb) = (x.1 * x.1) * (yb * yb) :=
              RE.sound (look [x.1, yb]) (.mul (.mul (.var 0) (.var 1)) (.mul (.var 0) (.var 1)))
                (.mul (.mul (.var 0) (.var 0)) (.mul (.var 1) (.var 1))) (by decide +kernel)
          _ = -((x.2 * yb) * (x.2 * yb)) := by
              rw [ha]
              exact RE.sound (look [x.2, yb]) (.mul (.neg (.mul (.var 0) (.var 0))) (.mul (.var 1) (.var 1)))
                (.neg (.mul (.mul (.var 0) (.var 1)) (.mul (.var 0) (.var 1)))) (by decide +kernel)
          _ = -1 := by rw [hyb, mul_one]
      have h1 : p % 4 = 1 := (FRC.Shell.Prime.quarter_turn_iff hp h2).1 ⟨_, hsq⟩
      rw [h1] at h3; exact absurd h3 (by decide)
  obtain ⟨m, hm⟩ := inv_of_prime hp hn
  refine ⟨(x.1 * m, -(x.2 * m)), ?_⟩
  unfold cmul
  show (x.1 * (x.1 * m) + -(x.2 * -(x.2 * m)), x.1 * -(x.2 * m) + x.2 * (x.1 * m)) = (1, 0)
  have e1 : x.1 * (x.1 * m) + -(x.2 * -(x.2 * m)) = (x.1 * x.1 + x.2 * x.2) * m :=
    RE.sound (look [x.1, x.2, m]) (.add (.mul (.var 0) (.mul (.var 0) (.var 2))) (.neg (.mul (.var 1) (.neg (.mul (.var 1) (.var 2))))))
      (.mul (.add (.mul (.var 0) (.var 0)) (.mul (.var 1) (.var 1))) (.var 2)) (by decide +kernel)
  have e2 : x.1 * -(x.2 * m) + x.2 * (x.1 * m) = 0 :=
    RE.sound (look [x.1, x.2, m]) (.add (.mul (.var 0) (.neg (.mul (.var 1) (.var 2)))) (.mul (.var 1) (.mul (.var 0) (.var 2))))
      .zero (by decide +kernel)
  rw [e1, e2, hm]

/-! ## Scale-periodicity, exact (1:D4)

The grid at scale `n` is `G_n = (x · g^{−n})_x`, written with the inverse `y` of the drive (`g · y = 1`), so that
`x · y^n = x g^{−n}`. The frame theme's `scale_periodic` gives the period `p − 1`; the theorems below make it exact:
two scales give the same grid point of a nonzero `x` exactly when they agree modulo `p − 1`, the zoom `y` has order
exactly `p − 1`, and every grid is the whole shell, each residue once. -/

/-- The inverse drive's powers invert the drive's: `g^k · y^k = 1` when `g · y = 1`. -/
theorem inv_pow {g y : Shell p} (hy : g * y = 1) (k : Nat) : g ^ k * y ^ k = 1 := by
  rw [← mul_pow, hy, one_pow]

/-- Cancellation by a nonzero residue on a framed shell: `x · a = x · b` with `x ≠ 0` forces `a = b`. -/
theorem mul_cancel {κ : Nat} {g : Shell p} (F : Frame p κ g) {x a b : Shell p} (hx : x ≠ 0) (h : x * a = x * b) :
    a = b := by
  obtain ⟨z, hz⟩ := F.exists_inv hx
  calc a = z * x * a := by rw [mul_comm z x, hz, one_mul]
    _ = z * (x * b) := by rw [mul_assoc, h]
    _ = b := by rw [← mul_assoc, mul_comm z x, hz, one_mul]

/-- 1:D4 — the grid of scale `n` is periodic in `n` with period `p − 1`: `x · y^{n+(p−1)} = x · y^n`. -/
theorem scale_inv_periodic {κ : Nat} {g y : Shell p} (F : Frame p κ g) (hy : g * y = 1) (x : Shell p) (n : Nat) :
    x * y ^ (n + (p - 1)) = x * y ^ n := by
  have h1 : y ^ (p - 1) = 1 := by
    calc y ^ (p - 1) = g ^ (p - 1) * y ^ (p - 1) := by rw [F.pow_n, one_mul]
      _ = 1 := inv_pow hy _
  rw [pow_add, h1, mul_one]

/-- The drive's powers agree exactly when their exponents agree modulo `p − 1`. -/
theorem pow_eq_iff {κ : Nat} {g : Shell p} (F : Frame p κ g) (m n : Nat) :
    g ^ m = g ^ n ↔ m % (p - 1) = n % (p - 1) := by
  constructor
  · intro h
    rw [F.pow_mod m, F.pow_mod n] at h
    exact F.pow_inj (Nat.mod_lt m F.n_pos) (Nat.mod_lt n F.n_pos) h
  · intro h; rw [F.pow_mod m, F.pow_mod n, h]

/-- 1:D4, the period is exact — for a nonzero `x` the grid points `x · y^m` and `x · y^n` coincide exactly when
`m ≡ n (mod p − 1)`: no smaller shift of scale returns a nonzero point to its place. -/
theorem scale_exact {κ : Nat} {g y : Shell p} (F : Frame p κ g) (hy : g * y = 1) {x : Shell p} (hx : x ≠ 0)
    (m n : Nat) : x * y ^ m = x * y ^ n ↔ m % (p - 1) = n % (p - 1) := by
  constructor
  · intro h
    have e : y ^ m = y ^ n := mul_cancel F hx h
    have hg : g ^ m = g ^ n := by
      calc g ^ m = g ^ m * (g ^ n * y ^ n) := by rw [inv_pow hy n, mul_one]
        _ = g ^ n * (g ^ m * y ^ n) := mul_left_comm _ _ _
        _ = g ^ n * (g ^ m * y ^ m) := by rw [e]
        _ = g ^ n := by rw [inv_pow hy m, mul_one]
    exact (pow_eq_iff F m n).1 hg
  · intro h
    have e : g ^ m = g ^ n := (pow_eq_iff F m n).2 h
    have ey : y ^ m = y ^ n := by
      calc y ^ m = y ^ m * (g ^ n * y ^ n) := by rw [inv_pow hy n, mul_one]
        _ = y ^ m * (g ^ m * y ^ n) := by rw [e]
        _ = (g ^ m * y ^ m) * y ^ n := by rw [← mul_assoc, mul_comm (y ^ m) (g ^ m)]
        _ = y ^ n := by rw [inv_pow hy m, one_mul]
    rw [ey]

/-- 1:D4, the zoom has order `p − 1` — the zoom by `k` steps fixes every grid point, `x · y^k = x` for all `x`,
exactly when `(p − 1) ∣ k`. -/
theorem zoom_order {κ : Nat} {g y : Shell p} (F : Frame p κ g) (hy : g * y = 1) (k : Nat) :
    (∀ x : Shell p, x * y ^ k = x) ↔ k % (p - 1) = 0 := by
  have h0 : k % (p - 1) = 0 % (p - 1) ↔ k % (p - 1) = 0 := by
    rw [FRC.Nat.mod_eq_of_lt F.n_pos]
  constructor
  · intro h
    have e := h 1
    rw [one_mul] at e
    have e' : (1 : Shell p) * y ^ k = 1 * y ^ 0 := by rw [one_mul, e, pow_zero, one_mul]
    exact h0.1 ((scale_exact F hy F.one_ne_zero k 0).1 e')
  · intro h x
    have e := (scale_exact F hy F.one_ne_zero k 0).2 (h0.2 h)
    rw [one_mul, one_mul, pow_zero] at e
    rw [e, mul_one]

/-- 1:D4, every grid is the whole shell — the scale map `x ↦ x · y^n` is onto (`z = (z g^n) y^n`) and one-to-one,
so each grid `G_n` lists every residue once, and `G_m`, `G_n` are equal as ordered lists exactly when
`m ≡ n (mod p − 1)` (`scale_exact` at `x = 1`, `scale_inv_periodic`). -/
theorem scale_bijective {κ : Nat} {g y : Shell p} (F : Frame p κ g) (hy : g * y = 1) (n : Nat) :
    (∀ z : Shell p, (z * g ^ n) * y ^ n = z) ∧ (∀ x x' : Shell p, x * y ^ n = x' * y ^ n → x = x') := by
  refine ⟨fun z => by rw [mul_assoc, inv_pow hy n, mul_one], fun x x' h => ?_⟩
  have hyn : y ^ n ≠ 0 := fun h0 => F.one_ne_zero (by rw [← inv_pow hy n, h0, mul_zero])
  rw [mul_comm x, mul_comm x'] at h
  exact mul_cancel F hyn h

/-! ## The circle in counts (1:E4) -/

/-- `k` rounds the framed turn `u/v` to the cycle of `N` steps: `2vk ≤ 2Nu + v < 2vk + 2v`, that is
`k = ⌊Nu/v + 1/2⌋` and `|k/N − u/v| ≤ 1/(2N)`. -/
def IsRound (N u v k : Nat) : Prop := 2 * v * k ≤ 2 * N * u + v ∧ 2 * N * u + v < 2 * v * k + 2 * v

theorem two_v_pos {v : Nat} (hv : 0 < v) : 0 < 2 * v := Nat.mul_pos (Nat.zero_lt_succ 1) hv

/-- 1:E4 — every framed turn has its rounding (the division with remainder by `2v`). -/
theorem round_exists (N u v : Nat) (hv : 0 < v) : ∃ k, IsRound N u v k := by
  obtain ⟨q, hq⟩ := FRC.Nat.mod_spec (2 * v) (two_v_pos hv) (2 * N * u + v)
  have hr := Nat.mod_lt (2 * N * u + v) (two_v_pos hv)
  refine ⟨q, ?_, ?_⟩
  · calc 2 * v * q ≤ 2 * v * q + (2 * N * u + v) % (2 * v) := Nat.le_add_right _ _
      _ = 2 * N * u + v := hq.symm
  · calc 2 * N * u + v = 2 * v * q + (2 * N * u + v) % (2 * v) := hq
      _ < 2 * v * q + 2 * v := Nat.add_lt_add_left hr _

theorem lt_of_mul_lt {c a b : Nat} (h : c * a < c * b) : a < b :=
  match Nat.lt_or_ge a b with
  | Or.inl hab => hab
  | Or.inr hba => absurd (Nat.lt_of_lt_of_le h (Nat.mul_le_mul_left c hba)) (Nat.lt_irrefl _)

theorem shuffle (A B v : Nat) : (A + v) + (B + v) = (A + B + v) + v := by
  rw [Nat.add_assoc A v, Nat.add_comm v (B + v), Nat.add_assoc B v v, ← Nat.add_assoc A B (v + v), Nat.add_assoc (A + B) v v]

theorem round_step (v k : Nat) : 2 * v * k + 2 * v = 2 * v * (k + 1) := (Nat.mul_succ (2 * v) k).symm

/-- 1:E4 — the rounding's group-law defect is `−1`, `0` or `1`: `k(u) + k(u′)` and `k(u + u′)` differ by at most one
step of the cycle. -/
theorem round_defect {N u u' v k₁ k₂ k₃ : Nat} (hv : 0 < v) (h₁ : IsRound N u v k₁) (h₂ : IsRound N u' v k₂)
    (h₃ : IsRound N (u + u') v k₃) : k₁ + k₂ ≤ k₃ + 1 ∧ k₃ ≤ k₁ + k₂ + 1 := by
  have hX : 2 * N * (u + u') = 2 * N * u + 2 * N * u' := Nat.left_distrib _ _ _
  have hvv : v < 2 * v := by
    rw [Nat.two_mul]; exact Nat.lt_add_of_pos_right hv
  refine ⟨Nat.le_of_lt_succ (lt_of_mul_lt (c := 2 * v) ?_), Nat.le_of_lt_succ (lt_of_mul_lt (c := 2 * v) ?_)⟩
  · -- 2v(k₁ + k₂) ≤ (2Nu + v) + (2Nu′ + v) = 2N(u + u′) + v + v < 2v k₃ + 2v + v < 2v(k₃ + 2)
    calc 2 * v * (k₁ + k₂) = 2 * v * k₁ + 2 * v * k₂ := Nat.left_distrib _ _ _
      _ ≤ (2 * N * u + v) + (2 * N * u' + v) := Nat.add_le_add h₁.1 h₂.1
      _ = (2 * N * (u + u') + v) + v := by rw [hX]; exact shuffle _ _ _
      _ < (2 * v * k₃ + 2 * v) + v := Nat.add_lt_add_right h₃.2 v
      _ < (2 * v * k₃ + 2 * v) + 2 * v := Nat.add_lt_add_left hvv _
      _ = 2 * v * (k₃ + 1 + 1) := by rw [round_step, round_step]
  · -- 2v k₃ ≤ 2N(u + u′) + v < (2Nu + v) + (2Nu′ + v) < (2v k₁ + 2v) + (2v k₂ + 2v) = 2v(k₁ + k₂ + 2)
    calc 2 * v * k₃ ≤ 2 * N * (u + u') + v := h₃.1
      _ < (2 * N * (u + u') + v) + v := Nat.lt_add_of_pos_right hv
      _ = (2 * N * u + v) + (2 * N * u' + v) := by rw [hX]; exact (shuffle _ _ _).symm
      _ < (2 * v * k₁ + 2 * v) + (2 * v * k₂ + 2 * v) := Nat.add_lt_add h₁.2 h₂.2
      _ = 2 * v * (k₁ + k₂ + 1 + 1) := by
          rw [round_step, round_step, ← Nat.left_distrib, Nat.add_assoc k₁ 1 (k₂ + 1), Nat.add_comm 1 (k₂ + 1),
            ← Nat.add_assoc, ← Nat.add_assoc]

end Frame
end Shell
end FRC
