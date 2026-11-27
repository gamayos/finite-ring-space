import FrcCore.Theme.Charge

/-!
# FrcCore.Theme.Rank — commutation, the drive and the rank of the internal frame (27:C18–27:C21)

`Theme/Charge.lean` states the cycles of the charges in the frame of rank five. This file states what commutation
and the drive fix of the internal frame, and the exact constraints on its rank.

* **Commutation (27:C18).** A matrix of rank two over the extension that commutes with the two unipotent frame moves
  of the frame plane is a scalar (`plane_commutant`).
* **The drive (27:C19).** An entry of a matrix that commutes with a diagonal matrix lies between two directions of
  equal value, or it is zero (`offblock_zero`).
* **The rank (27:C20, 27:C21).** The triality scalar has determinant one on a frame of rank `m` exactly when `3 ∣ m`
  (`triality_rank`). The parity of the complementary exterior power (`conj_parity`); on the ranks `2` to
  `408` the integers of the one-loop form, `11 m − 3·2^(m−1)` and `11 m − 2^(m−1)`, are positive for `m ≤ 5` and for
  `m ≤ 7` (`light_three`, `light_one`) and not positive beyond (`bound_three`, `bound_one`); a multiple of three with
  the first positive is three (`colour_rank_three`, `colour_rank_three_chiral`). No integer above `3·2^407` is formed; the two exact constraints hold together at the ranks congruent to `3` modulo `6`
  (`exact_ranks`), and the index sum of a generation is `2^(m−2)` (`index_sum`). No axioms.
-/

namespace FRC.Unitary

open FRC.Shell FRC.Shell.Frame FRC.Extension

variable {p : Nat} [Pos p] {ν : Shell p}

/-- The upper unipotent frame move of the frame plane. -/
def uup : M2 p ν := ⟨1, 1, 0, 1⟩
/-- The lower unipotent frame move of the frame plane. -/
def ulow : M2 p ν := ⟨1, 0, 1, 1⟩

/-- 27:C18 — a matrix of rank two over the extension that commutes with the two unipotent frame moves of the frame
plane is a scalar. -/
theorem plane_commutant {A : M2 p ν} (hU : mmul2 A uup = mmul2 uup A) (hL : mmul2 A ulow = mmul2 ulow A) :
    A.a01 = 0 ∧ A.a10 = 0 ∧ A.a00 = A.a11 := by
  cases A with
  | mk a b c d =>
    have h00 : a * 1 + b * 0 = 1 * a + 1 * c := congrArg M2.a00 hU
    have h01 : a * 1 + b * 1 = 1 * b + 1 * d := congrArg M2.a01 hU
    have g00 : a * 1 + b * 1 = 1 * a + 0 * c := congrArg M2.a00 hL
    have ec : c = (1 * a + 1 * c) + -(a * 1 + b * 0) :=
      xsound (xlook [a, b, c, d]) (.var 2)
        (.add (.add (.mul .one (.var 0)) (.mul .one (.var 2))) (.neg (.add (.mul (.var 0) .one) (.mul (.var 1) .zero))))
        (by decide +kernel)
    have zc : (1 * a + 1 * c) + -(1 * a + 1 * c) = 0 :=
      xsound (xlook [a, b, c, d])
        (.add (.add (.mul .one (.var 0)) (.mul .one (.var 2))) (.neg (.add (.mul .one (.var 0)) (.mul .one (.var 2))))) .zero
        (by decide +kernel)
    have eb : b = (a * 1 + b * 1) + -(1 * a + 0 * c) :=
      xsound (xlook [a, b, c, d]) (.var 1)
        (.add (.add (.mul (.var 0) .one) (.mul (.var 1) .one)) (.neg (.add (.mul .one (.var 0)) (.mul .zero (.var 2)))))
        (by decide +kernel)
    have zb : (1 * a + 0 * c) + -(1 * a + 0 * c) = 0 :=
      xsound (xlook [a, b, c, d])
        (.add (.add (.mul .one (.var 0)) (.mul .zero (.var 2))) (.neg (.add (.mul .one (.var 0)) (.mul .zero (.var 2))))) .zero
        (by decide +kernel)
    have hc : c = 0 := by rw [h00] at ec; exact ec.trans zc
    have hb : b = 0 := by rw [g00] at eb; exact eb.trans zb
    have ead : a = (a * 1 + b * 1) + -(1 * b + 1 * d) + d :=
      xsound (xlook [a, b, c, d]) (.var 0)
        (.add (.add (.add (.mul (.var 0) .one) (.mul (.var 1) .one)) (.neg (.add (.mul .one (.var 1)) (.mul .one (.var 3))))) (.var 3))
        (by decide +kernel)
    have zad : (1 * b + 1 * d) + -(1 * b + 1 * d) + d = d :=
      xsound (xlook [a, b, c, d])
        (.add (.add (.add (.mul .one (.var 1)) (.mul .one (.var 3))) (.neg (.add (.mul .one (.var 1)) (.mul .one (.var 3))))) (.var 3)) (.var 3)
        (by decide +kernel)
    have had : a = d := by rw [h01] at ead; exact ead.trans zad
    exact ⟨hb, hc, had⟩

/-- The image of the upper unipotent frame move on the symmetric square of the frame plane, in the basis `x², xy, y²`. -/
def sup : M3 p ν := ⟨1, 1, 1, 0, 1, 1 + 1, 0, 0, 1⟩
/-- The image of the lower unipotent frame move on the symmetric square of the frame plane. -/
def slow : M3 p ν := ⟨1, 0, 0, 1 + 1, 1, 0, 1, 1, 1⟩

/-- 27:C18 — a matrix of rank three over the extension that commutes with the images of the two unipotent frame moves
on the symmetric square of the frame plane is a scalar, on a shell where `1 + 1` has an inverse `k`. -/
theorem space_commutant {A : M3 p ν} {k : Ext p ν} (h2 : (1 + 1) * k = 1)
    (hU : mmul A sup = mmul sup A) (hL : mmul A slow = mmul slow A) :
    A.a01 = 0 ∧ A.a02 = 0 ∧ A.a10 = 0 ∧ A.a12 = 0 ∧ A.a20 = 0 ∧ A.a21 = 0 ∧ A.a00 = A.a11 ∧ A.a11 = A.a22 := by
  cases A with
  | mk a00 a01 a02 a10 a11 a12 a20 a21 a22 =>
    have hL00 : (((a00 * 1) + (a01 * (1 + 1))) + (a02 * 1)) = (((1 * a00) + (0 * a10)) + (0 * a20)) := congrArg M3.a00 hL
    have dL00 : ((((a00 * 1) + (a01 * (1 + 1))) + (a02 * 1)) + -(((1 * a00) + (0 * a10)) + (0 * a20))) = 0 := by
      rw [hL00]
      exact xsound (xlook [a00, a01, a02, a10, a11, a12, a20, a21, a22, k]) (.add (.add (.add (.mul .one (.var 0)) (.mul .zero (.var 3))) (.mul .zero (.var 6))) (.neg (.add (.add (.mul .one (.var 0)) (.mul .zero (.var 3))) (.mul .zero (.var 6))))) .zero (by decide +kernel)
    have hL01 : (((a00 * 0) + (a01 * 1)) + (a02 * 1)) = (((1 * a01) + (0 * a11)) + (0 * a21)) := congrArg M3.a01 hL
    have dL01 : ((((a00 * 0) + (a01 * 1)) + (a02 * 1)) + -(((1 * a01) + (0 * a11)) + (0 * a21))) = 0 := by
      rw [hL01]
      exact xsound (xlook [a00, a01, a02, a10, a11, a12, a20, a21, a22, k]) (.add (.add (.add (.mul .one (.var 1)) (.mul .zero (.var 4))) (.mul .zero (.var 7))) (.neg (.add (.add (.mul .one (.var 1)) (.mul .zero (.var 4))) (.mul .zero (.var 7))))) .zero (by decide +kernel)
    have hU00 : (((a00 * 1) + (a01 * 0)) + (a02 * 0)) = (((1 * a00) + (1 * a10)) + (1 * a20)) := congrArg M3.a00 hU
    have dU00 : ((((a00 * 1) + (a01 * 0)) + (a02 * 0)) + -(((1 * a00) + (1 * a10)) + (1 * a20))) = 0 := by
      rw [hU00]
      exact xsound (xlook [a00, a01, a02, a10, a11, a12, a20, a21, a22, k]) (.add (.add (.add (.mul .one (.var 0)) (.mul .one (.var 3))) (.mul .one (.var 6))) (.neg (.add (.add (.mul .one (.var 0)) (.mul .one (.var 3))) (.mul .one (.var 6))))) .zero (by decide +kernel)
    have hU01 : (((a00 * 1) + (a01 * 1)) + (a02 * 0)) = (((1 * a01) + (1 * a11)) + (1 * a21)) := congrArg M3.a01 hU
    have dU01 : ((((a00 * 1) + (a01 * 1)) + (a02 * 0)) + -(((1 * a01) + (1 * a11)) + (1 * a21))) = 0 := by
      rw [hU01]
      exact xsound (xlook [a00, a01, a02, a10, a11, a12, a20, a21, a22, k]) (.add (.add (.add (.mul .one (.var 1)) (.mul .one (.var 4))) (.mul .one (.var 7))) (.neg (.add (.add (.mul .one (.var 1)) (.mul .one (.var 4))) (.mul .one (.var 7))))) .zero (by decide +kernel)
    have hU02 : (((a00 * 1) + (a01 * (1 + 1))) + (a02 * 1)) = (((1 * a02) + (1 * a12)) + (1 * a22)) := congrArg M3.a02 hU
    have dU02 : ((((a00 * 1) + (a01 * (1 + 1))) + (a02 * 1)) + -(((1 * a02) + (1 * a12)) + (1 * a22))) = 0 := by
      rw [hU02]
      exact xsound (xlook [a00, a01, a02, a10, a11, a12, a20, a21, a22, k]) (.add (.add (.add (.mul .one (.var 2)) (.mul .one (.var 5))) (.mul .one (.var 8))) (.neg (.add (.add (.mul .one (.var 2)) (.mul .one (.var 5))) (.mul .one (.var 8))))) .zero (by decide +kernel)
    have hU10 : (((a10 * 1) + (a11 * 0)) + (a12 * 0)) = (((0 * a00) + (1 * a10)) + ((1 + 1) * a20)) := congrArg M3.a10 hU
    have dU10 : ((((a10 * 1) + (a11 * 0)) + (a12 * 0)) + -(((0 * a00) + (1 * a10)) + ((1 + 1) * a20))) = 0 := by
      rw [hU10]
      exact xsound (xlook [a00, a01, a02, a10, a11, a12, a20, a21, a22, k]) (.add (.add (.add (.mul .zero (.var 0)) (.mul .one (.var 3))) (.mul (.add .one .one) (.var 6))) (.neg (.add (.add (.mul .zero (.var 0)) (.mul .one (.var 3))) (.mul (.add .one .one) (.var 6))))) .zero (by decide +kernel)
    have hU11 : (((a10 * 1) + (a11 * 1)) + (a12 * 0)) = (((0 * a01) + (1 * a11)) + ((1 + 1) * a21)) := congrArg M3.a11 hU
    have dU11 : ((((a10 * 1) + (a11 * 1)) + (a12 * 0)) + -(((0 * a01) + (1 * a11)) + ((1 + 1) * a21))) = 0 := by
      rw [hU11]
      exact xsound (xlook [a00, a01, a02, a10, a11, a12, a20, a21, a22, k]) (.add (.add (.add (.mul .zero (.var 1)) (.mul .one (.var 4))) (.mul (.add .one .one) (.var 7))) (.neg (.add (.add (.mul .zero (.var 1)) (.mul .one (.var 4))) (.mul (.add .one .one) (.var 7))))) .zero (by decide +kernel)
    have hU12 : (((a10 * 1) + (a11 * (1 + 1))) + (a12 * 1)) = (((0 * a02) + (1 * a12)) + ((1 + 1) * a22)) := congrArg M3.a12 hU
    have dU12 : ((((a10 * 1) + (a11 * (1 + 1))) + (a12 * 1)) + -(((0 * a02) + (1 * a12)) + ((1 + 1) * a22))) = 0 := by
      rw [hU12]
      exact xsound (xlook [a00, a01, a02, a10, a11, a12, a20, a21, a22, k]) (.add (.add (.add (.mul .zero (.var 2)) (.mul .one (.var 5))) (.mul (.add .one .one) (.var 8))) (.neg (.add (.add (.mul .zero (.var 2)) (.mul .one (.var 5))) (.mul (.add .one .one) (.var 8))))) .zero (by decide +kernel)
    have e_a20 : (a20 * ((1 + 1) * k)) = ((-((((a10 * 1) + (a11 * 0)) + (a12 * 0)) + -(((0 * a00) + (1 * a10)) + ((1 + 1) * a20)))) * k) :=
      xsound (xlook [a00, a01, a02, a10, a11, a12, a20, a21, a22, k]) (.mul (.var 6) (.mul (.add .one .one) (.var 9))) (.mul (.neg (.add (.add (.add (.mul (.var 3) .one) (.mul (.var 4) .zero)) (.mul (.var 5) .zero)) (.neg (.add (.add (.mul .zero (.var 0)) (.mul .one (.var 3))) (.mul (.add .one .one) (.var 6)))))) (.var 9)) (by decide +kernel)
    have z_a20 : (((-0) * k) : Ext p ν) = 0 :=
      xsound (xlook [a00, a01, a02, a10, a11, a12, a20, a21, a22, k]) (.mul (.neg .zero) (.var 9)) .zero (by decide +kernel)
    have o_a20 : (a20 * 1) = a20 :=
      xsound (xlook [a00, a01, a02, a10, a11, a12, a20, a21, a22, k]) (.mul (.var 6) .one) (.var 6) (by decide +kernel)
    rw [h2, dU10] at e_a20
    have f_a20 : a20 = 0 := o_a20.symm.trans (e_a20.trans z_a20)
    have e_a10 : (a10 * ((1 + 1) * k)) = ((((-((((a00 * 1) + (a01 * 0)) + (a02 * 0)) + -(((1 * a00) + (1 * a10)) + (1 * a20)))) + (-((((a00 * 1) + (a01 * 0)) + (a02 * 0)) + -(((1 * a00) + (1 * a10)) + (1 * a20))))) + ((((a10 * 1) + (a11 * 0)) + (a12 * 0)) + -(((0 * a00) + (1 * a10)) + ((1 + 1) * a20)))) * k) :=
      xsound (xlook [a00, a01, a02, a10, a11, a12, a20, a21, a22, k]) (.mul (.var 3) (.mul (.add .one .one) (.var 9))) (.mul (.add (.add (.neg (.add (.add (.add (.mul (.var 0) .one) (.mul (.var 1) .zero)) (.mul (.var 2) .zero)) (.neg (.add (.add (.mul .one (.var 0)) (.mul .one (.var 3))) (.mul .one (.var 6)))))) (.neg (.add (.add (.add (.mul (.var 0) .one) (.mul (.var 1) .zero)) (.mul (.var 2) .zero)) (.neg (.add (.add (.mul .one (.var 0)) (.mul .one (.var 3))) (.mul .one (.var 6))))))) (.add (.add (.add (.mul (.var 3) .one) (.mul (.var 4) .zero)) (.mul (.var 5) .zero)) (.neg (.add (.add (.mul .zero (.var 0)) (.mul .one (.var 3))) (.mul (.add .one .one) (.var 6)))))) (.var 9)) (by decide +kernel)
    have z_a10 : (((((-0) + (-0)) + 0) * k) : Ext p ν) = 0 :=
      xsound (xlook [a00, a01, a02, a10, a11, a12, a20, a21, a22, k]) (.mul (.add (.add (.neg .zero) (.neg .zero)) .zero) (.var 9)) .zero (by decide +kernel)
    have o_a10 : (a10 * 1) = a10 :=
      xsound (xlook [a00, a01, a02, a10, a11, a12, a20, a21, a22, k]) (.mul (.var 3) .one) (.var 3) (by decide +kernel)
    rw [h2, dU00, dU10] at e_a10
    have f_a10 : a10 = 0 := o_a10.symm.trans (e_a10.trans z_a10)
    have e_a21 : ((a21 * ((1 + 1) * k)) * ((1 + 1) * k)) = (((((((-((((a00 * 1) + (a01 * 0)) + (a02 * 0)) + -(((1 * a00) + (1 * a10)) + (1 * a20)))) + (-((((a00 * 1) + (a01 * 0)) + (a02 * 0)) + -(((1 * a00) + (1 * a10)) + (1 * a20))))) + ((((a10 * 1) + (a11 * 0)) + (a12 * 0)) + -(((0 * a00) + (1 * a10)) + ((1 + 1) * a20)))) + (-((((a10 * 1) + (a11 * 1)) + (a12 * 0)) + -(((0 * a01) + (1 * a11)) + ((1 + 1) * a21))))) + (-((((a10 * 1) + (a11 * 1)) + (a12 * 0)) + -(((0 * a01) + (1 * a11)) + ((1 + 1) * a21))))) * k) * k) :=
      xsound (xlook [a00, a01, a02, a10, a11, a12, a20, a21, a22, k]) (.mul (.mul (.var 7) (.mul (.add .one .one) (.var 9))) (.mul (.add .one .one) (.var 9))) (.mul (.mul (.add (.add (.add (.add (.neg (.add (.add (.add (.mul (.var 0) .one) (.mul (.var 1) .zero)) (.mul (.var 2) .zero)) (.neg (.add (.add (.mul .one (.var 0)) (.mul .one (.var 3))) (.mul .one (.var 6)))))) (.neg (.add (.add (.add (.mul (.var 0) .one) (.mul (.var 1) .zero)) (.mul (.var 2) .zero)) (.neg (.add (.add (.mul .one (.var 0)) (.mul .one (.var 3))) (.mul .one (.var 6))))))) (.add (.add (.add (.mul (.var 3) .one) (.mul (.var 4) .zero)) (.mul (.var 5) .zero)) (.neg (.add (.add (.mul .zero (.var 0)) (.mul .one (.var 3))) (.mul (.add .one .one) (.var 6)))))) (.neg (.add (.add (.add (.mul (.var 3) .one) (.mul (.var 4) .one)) (.mul (.var 5) .zero)) (.neg (.add (.add (.mul .zero (.var 1)) (.mul .one (.var 4))) (.mul (.add .one .one) (.var 7))))))) (.neg (.add (.add (.add (.mul (.var 3) .one) (.mul (.var 4) .one)) (.mul (.var 5) .zero)) (.neg (.add (.add (.mul .zero (.var 1)) (.mul .one (.var 4))) (.mul (.add .one .one) (.var 7))))))) (.var 9)) (.var 9)) (by decide +kernel)
    have z_a21 : ((((((((-0) + (-0)) + 0) + (-0)) + (-0)) * k) * k) : Ext p ν) = 0 :=
      xsound (xlook [a00, a01, a02, a10, a11, a12, a20, a21, a22, k]) (.mul (.mul (.add (.add (.add (.add (.neg .zero) (.neg .zero)) .zero) (.neg .zero)) (.neg .zero)) (.var 9)) (.var 9)) .zero (by decide +kernel)
    have o_a21 : ((a21 * 1) * 1) = a21 :=
      xsound (xlook [a00, a01, a02, a10, a11, a12, a20, a21, a22, k]) (.mul (.mul (.var 7) .one) .one) (.var 7) (by decide +kernel)
    rw [h2, dU00, dU10, dU11] at e_a21
    have f_a21 : a21 = 0 := o_a21.symm.trans (e_a21.trans z_a21)
    have e_a02 : a02 = ((((a00 * 0) + (a01 * 1)) + (a02 * 1)) + -(((1 * a01) + (0 * a11)) + (0 * a21))) :=
      xsound (xlook [a00, a01, a02, a10, a11, a12, a20, a21, a22, k]) (.var 2) (.add (.add (.add (.mul (.var 0) .zero) (.mul (.var 1) .one)) (.mul (.var 2) .one)) (.neg (.add (.add (.mul .one (.var 1)) (.mul .zero (.var 4))) (.mul .zero (.var 7))))) (by decide +kernel)
    have z_a02 : (0 : Ext p ν) = 0 :=
      xsound (xlook [a00, a01, a02, a10, a11, a12, a20, a21, a22, k]) .zero .zero (by decide +kernel)
    have o_a02 : a02 = a02 :=
      xsound (xlook [a00, a01, a02, a10, a11, a12, a20, a21, a22, k]) (.var 2) (.var 2) (by decide +kernel)
    rw [dL01] at e_a02
    have f_a02 : a02 = 0 := o_a02.symm.trans (e_a02.trans z_a02)
    have e_a01 : (a01 * ((1 + 1) * k)) = ((((((a00 * 1) + (a01 * (1 + 1))) + (a02 * 1)) + -(((1 * a00) + (0 * a10)) + (0 * a20))) + (-((((a00 * 0) + (a01 * 1)) + (a02 * 1)) + -(((1 * a01) + (0 * a11)) + (0 * a21))))) * k) :=
      xsound (xlook [a00, a01, a02, a10, a11, a12, a20, a21, a22, k]) (.mul (.var 1) (.mul (.add .one .one) (.var 9))) (.mul (.add (.add (.add (.add (.mul (.var 0) .one) (.mul (.var 1) (.add .one .one))) (.mul (.var 2) .one)) (.neg (.add (.add (.mul .one (.var 0)) (.mul .zero (.var 3))) (.mul .zero (.var 6))))) (.neg (.add (.add (.add (.mul (.var 0) .zero) (.mul (.var 1) .one)) (.mul (.var 2) .one)) (.neg (.add (.add (.mul .one (.var 1)) (.mul .zero (.var 4))) (.mul .zero (.var 7))))))) (.var 9)) (by decide +kernel)
    have z_a01 : (((0 + (-0)) * k) : Ext p ν) = 0 :=
      xsound (xlook [a00, a01, a02, a10, a11, a12, a20, a21, a22, k]) (.mul (.add .zero (.neg .zero)) (.var 9)) .zero (by decide +kernel)
    have o_a01 : (a01 * 1) = a01 :=
      xsound (xlook [a00, a01, a02, a10, a11, a12, a20, a21, a22, k]) (.mul (.var 1) .one) (.var 1) (by decide +kernel)
    rw [h2, dL00, dL01] at e_a01
    have f_a01 : a01 = 0 := o_a01.symm.trans (e_a01.trans z_a01)
    have e_a12 : (a12 * ((1 + 1) * k)) = ((((((((((((((a00 * 1) + (a01 * 1)) + (a02 * 0)) + -(((1 * a01) + (1 * a11)) + (1 * a21))) + ((((a00 * 1) + (a01 * 1)) + (a02 * 0)) + -(((1 * a01) + (1 * a11)) + (1 * a21)))) + (-((((a00 * 1) + (a01 * (1 + 1))) + (a02 * 1)) + -(((1 * a02) + (1 * a12)) + (1 * a22))))) + (-((((a00 * 1) + (a01 * (1 + 1))) + (a02 * 1)) + -(((1 * a02) + (1 * a12)) + (1 * a22))))) + (-((((a10 * 1) + (a11 * 1)) + (a12 * 0)) + -(((0 * a01) + (1 * a11)) + ((1 + 1) * a21))))) + ((((a10 * 1) + (a11 * (1 + 1))) + (a12 * 1)) + -(((0 * a02) + (1 * a12)) + ((1 + 1) * a22)))) + ((((a00 * 1) + (a01 * (1 + 1))) + (a02 * 1)) + -(((1 * a00) + (0 * a10)) + (0 * a20)))) + ((((a00 * 1) + (a01 * (1 + 1))) + (a02 * 1)) + -(((1 * a00) + (0 * a10)) + (0 * a20)))) + (-((((a00 * 0) + (a01 * 1)) + (a02 * 1)) + -(((1 * a01) + (0 * a11)) + (0 * a21))))) + (-((((a00 * 0) + (a01 * 1)) + (a02 * 1)) + -(((1 * a01) + (0 * a11)) + (0 * a21))))) * k) :=
      xsound (xlook [a00, a01, a02, a10, a11, a12, a20, a21, a22, k]) (.mul (.var 5) (.mul (.add .one .one) (.var 9))) (.mul (.add (.add (.add (.add (.add (.add (.add (.add (.add (.add (.add (.add (.mul (.var 0) .one) (.mul (.var 1) .one)) (.mul (.var 2) .zero)) (.neg (.add (.add (.mul .one (.var 1)) (.mul .one (.var 4))) (.mul .one (.var 7))))) (.add (.add (.add (.mul (.var 0) .one) (.mul (.var 1) .one)) (.mul (.var 2) .zero)) (.neg (.add (.add (.mul .one (.var 1)) (.mul .one (.var 4))) (.mul .one (.var 7)))))) (.neg (.add (.add (.add (.mul (.var 0) .one) (.mul (.var 1) (.add .one .one))) (.mul (.var 2) .one)) (.neg (.add (.add (.mul .one (.var 2)) (.mul .one (.var 5))) (.mul .one (.var 8))))))) (.neg (.add (.add (.add (.mul (.var 0) .one) (.mul (.var 1) (.add .one .one))) (.mul (.var 2) .one)) (.neg (.add (.add (.mul .one (.var 2)) (.mul .one (.var 5))) (.mul .one (.var 8))))))) (.neg (.add (.add (.add (.mul (.var 3) .one) (.mul (.var 4) .one)) (.mul (.var 5) .zero)) (.neg (.add (.add (.mul .zero (.var 1)) (.mul .one (.var 4))) (.mul (.add .one .one) (.var 7))))))) (.add (.add (.add (.mul (.var 3) .one) (.mul (.var 4) (.add .one .one))) (.mul (.var 5) .one)) (.neg (.add (.add (.mul .zero (.var 2)) (.mul .one (.var 5))) (.mul (.add .one .one) (.var 8)))))) (.add (.add (.add (.mul (.var 0) .one) (.mul (.var 1) (.add .one .one))) (.mul (.var 2) .one)) (.neg (.add (.add (.mul .one (.var 0)) (.mul .zero (.var 3))) (.mul .zero (.var 6)))))) (.add (.add (.add (.mul (.var 0) .one) (.mul (.var 1) (.add .one .one))) (.mul (.var 2) .one)) (.neg (.add (.add (.mul .one (.var 0)) (.mul .zero (.var 3))) (.mul .zero (.var 6)))))) (.neg (.add (.add (.add (.mul (.var 0) .zero) (.mul (.var 1) .one)) (.mul (.var 2) .one)) (.neg (.add (.add (.mul .one (.var 1)) (.mul .zero (.var 4))) (.mul .zero (.var 7))))))) (.neg (.add (.add (.add (.mul (.var 0) .zero) (.mul (.var 1) .one)) (.mul (.var 2) .one)) (.neg (.add (.add (.mul .one (.var 1)) (.mul .zero (.var 4))) (.mul .zero (.var 7))))))) (.var 9)) (by decide +kernel)
    have z_a12 : (((((((((((0 + 0) + (-0)) + (-0)) + (-0)) + 0) + 0) + 0) + (-0)) + (-0)) * k) : Ext p ν) = 0 :=
      xsound (xlook [a00, a01, a02, a10, a11, a12, a20, a21, a22, k]) (.mul (.add (.add (.add (.add (.add (.add (.add (.add (.add .zero .zero) (.neg .zero)) (.neg .zero)) (.neg .zero)) .zero) .zero) .zero) (.neg .zero)) (.neg .zero)) (.var 9)) .zero (by decide +kernel)
    have o_a12 : (a12 * 1) = a12 :=
      xsound (xlook [a00, a01, a02, a10, a11, a12, a20, a21, a22, k]) (.mul (.var 5) .one) (.var 5) (by decide +kernel)
    rw [h2, dU01, dU02, dU11, dU12, dL00, dL01] at e_a12
    have f_a12 : a12 = 0 := o_a12.symm.trans (e_a12.trans z_a12)
    have e_d01 : (((a00 + -a11) * ((1 + 1) * k)) * ((1 + 1) * k)) = (((((((((((-((((a00 * 1) + (a01 * 0)) + (a02 * 0)) + -(((1 * a00) + (1 * a10)) + (1 * a20)))) + (-((((a00 * 1) + (a01 * 0)) + (a02 * 0)) + -(((1 * a00) + (1 * a10)) + (1 * a20))))) + ((((a00 * 1) + (a01 * 1)) + (a02 * 0)) + -(((1 * a01) + (1 * a11)) + (1 * a21)))) + ((((a00 * 1) + (a01 * 1)) + (a02 * 0)) + -(((1 * a01) + (1 * a11)) + (1 * a21)))) + ((((a00 * 1) + (a01 * 1)) + (a02 * 0)) + -(((1 * a01) + (1 * a11)) + (1 * a21)))) + ((((a00 * 1) + (a01 * 1)) + (a02 * 0)) + -(((1 * a01) + (1 * a11)) + (1 * a21)))) + ((((a10 * 1) + (a11 * 0)) + (a12 * 0)) + -(((0 * a00) + (1 * a10)) + ((1 + 1) * a20)))) + (-((((a10 * 1) + (a11 * 1)) + (a12 * 0)) + -(((0 * a01) + (1 * a11)) + ((1 + 1) * a21))))) + (-((((a10 * 1) + (a11 * 1)) + (a12 * 0)) + -(((0 * a01) + (1 * a11)) + ((1 + 1) * a21))))) * k) * k) :=
      xsound (xlook [a00, a01, a02, a10, a11, a12, a20, a21, a22, k]) (.mul (.mul (.add (.var 0) (.neg (.var 4))) (.mul (.add .one .one) (.var 9))) (.mul (.add .one .one) (.var 9))) (.mul (.mul (.add (.add (.add (.add (.add (.add (.add (.add (.neg (.add (.add (.add (.mul (.var 0) .one) (.mul (.var 1) .zero)) (.mul (.var 2) .zero)) (.neg (.add (.add (.mul .one (.var 0)) (.mul .one (.var 3))) (.mul .one (.var 6)))))) (.neg (.add (.add (.add (.mul (.var 0) .one) (.mul (.var 1) .zero)) (.mul (.var 2) .zero)) (.neg (.add (.add (.mul .one (.var 0)) (.mul .one (.var 3))) (.mul .one (.var 6))))))) (.add (.add (.add (.mul (.var 0) .one) (.mul (.var 1) .one)) (.mul (.var 2) .zero)) (.neg (.add (.add (.mul .one (.var 1)) (.mul .one (.var 4))) (.mul .one (.var 7)))))) (.add (.add (.add (.mul (.var 0) .one) (.mul (.var 1) .one)) (.mul (.var 2) .zero)) (.neg (.add (.add (.mul .one (.var 1)) (.mul .one (.var 4))) (.mul .one (.var 7)))))) (.add (.add (.add (.mul (.var 0) .one) (.mul (.var 1) .one)) (.mul (.var 2) .zero)) (.neg (.add (.add (.mul .one (.var 1)) (.mul .one (.var 4))) (.mul .one (.var 7)))))) (.add (.add (.add (.mul (.var 0) .one) (.mul (.var 1) .one)) (.mul (.var 2) .zero)) (.neg (.add (.add (.mul .one (.var 1)) (.mul .one (.var 4))) (.mul .one (.var 7)))))) (.add (.add (.add (.mul (.var 3) .one) (.mul (.var 4) .zero)) (.mul (.var 5) .zero)) (.neg (.add (.add (.mul .zero (.var 0)) (.mul .one (.var 3))) (.mul (.add .one .one) (.var 6)))))) (.neg (.add (.add (.add (.mul (.var 3) .one) (.mul (.var 4) .one)) (.mul (.var 5) .zero)) (.neg (.add (.add (.mul .zero (.var 1)) (.mul .one (.var 4))) (.mul (.add .one .one) (.var 7))))))) (.neg (.add (.add (.add (.mul (.var 3) .one) (.mul (.var 4) .one)) (.mul (.var 5) .zero)) (.neg (.add (.add (.mul .zero (.var 1)) (.mul .one (.var 4))) (.mul (.add .one .one) (.var 7))))))) (.var 9)) (.var 9)) (by decide +kernel)
    have z_d01 : ((((((((((((-0) + (-0)) + 0) + 0) + 0) + 0) + 0) + (-0)) + (-0)) * k) * k) : Ext p ν) = 0 :=
      xsound (xlook [a00, a01, a02, a10, a11, a12, a20, a21, a22, k]) (.mul (.mul (.add (.add (.add (.add (.add (.add (.add (.add (.neg .zero) (.neg .zero)) .zero) .zero) .zero) .zero) .zero) (.neg .zero)) (.neg .zero)) (.var 9)) (.var 9)) .zero (by decide +kernel)
    have o_d01 : (((a00 + -a11) * 1) * 1) = (a00 + -a11) :=
      xsound (xlook [a00, a01, a02, a10, a11, a12, a20, a21, a22, k]) (.mul (.mul (.add (.var 0) (.neg (.var 4))) .one) .one) (.add (.var 0) (.neg (.var 4))) (by decide +kernel)
    rw [h2, dU00, dU01, dU10, dU11] at e_d01
    have f_d01 : (a00 + -a11) = 0 := o_d01.symm.trans (e_d01.trans z_d01)
    have e_d12 : (((a11 + -a22) * ((1 + 1) * k)) * ((1 + 1) * k)) = ((((((((((a00 * 1) + (a01 * 0)) + (a02 * 0)) + -(((1 * a00) + (1 * a10)) + (1 * a20))) + ((((a00 * 1) + (a01 * 0)) + (a02 * 0)) + -(((1 * a00) + (1 * a10)) + (1 * a20)))) + (-((((a10 * 1) + (a11 * 0)) + (a12 * 0)) + -(((0 * a00) + (1 * a10)) + ((1 + 1) * a20))))) + ((((a10 * 1) + (a11 * (1 + 1))) + (a12 * 1)) + -(((0 * a02) + (1 * a12)) + ((1 + 1) * a22)))) + ((((a10 * 1) + (a11 * (1 + 1))) + (a12 * 1)) + -(((0 * a02) + (1 * a12)) + ((1 + 1) * a22)))) * k) * k) :=
      xsound (xlook [a00, a01, a02, a10, a11, a12, a20, a21, a22, k]) (.mul (.mul (.add (.var 4) (.neg (.var 8))) (.mul (.add .one .one) (.var 9))) (.mul (.add .one .one) (.var 9))) (.mul (.mul (.add (.add (.add (.add (.add (.add (.add (.mul (.var 0) .one) (.mul (.var 1) .zero)) (.mul (.var 2) .zero)) (.neg (.add (.add (.mul .one (.var 0)) (.mul .one (.var 3))) (.mul .one (.var 6))))) (.add (.add (.add (.mul (.var 0) .one) (.mul (.var 1) .zero)) (.mul (.var 2) .zero)) (.neg (.add (.add (.mul .one (.var 0)) (.mul .one (.var 3))) (.mul .one (.var 6)))))) (.neg (.add (.add (.add (.mul (.var 3) .one) (.mul (.var 4) .zero)) (.mul (.var 5) .zero)) (.neg (.add (.add (.mul .zero (.var 0)) (.mul .one (.var 3))) (.mul (.add .one .one) (.var 6))))))) (.add (.add (.add (.mul (.var 3) .one) (.mul (.var 4) (.add .one .one))) (.mul (.var 5) .one)) (.neg (.add (.add (.mul .zero (.var 2)) (.mul .one (.var 5))) (.mul (.add .one .one) (.var 8)))))) (.add (.add (.add (.mul (.var 3) .one) (.mul (.var 4) (.add .one .one))) (.mul (.var 5) .one)) (.neg (.add (.add (.mul .zero (.var 2)) (.mul .one (.var 5))) (.mul (.add .one .one) (.var 8)))))) (.var 9)) (.var 9)) (by decide +kernel)
    have z_d12 : (((((((0 + 0) + (-0)) + 0) + 0) * k) * k) : Ext p ν) = 0 :=
      xsound (xlook [a00, a01, a02, a10, a11, a12, a20, a21, a22, k]) (.mul (.mul (.add (.add (.add (.add .zero .zero) (.neg .zero)) .zero) .zero) (.var 9)) (.var 9)) .zero (by decide +kernel)
    have o_d12 : (((a11 + -a22) * 1) * 1) = (a11 + -a22) :=
      xsound (xlook [a00, a01, a02, a10, a11, a12, a20, a21, a22, k]) (.mul (.mul (.add (.var 4) (.neg (.var 8))) .one) .one) (.add (.var 4) (.neg (.var 8))) (by decide +kernel)
    rw [h2, dU00, dU10, dU12] at e_d12
    have f_d12 : (a11 + -a22) = 0 := o_d12.symm.trans (e_d12.trans z_d12)
    have g_d01 : a00 = a11 := by
      have e : a00 = ((a00 + -a11) + a11) := xsound (xlook [a00, a01, a02, a10, a11, a12, a20, a21, a22, k]) (.var 0) (.add (.add (.var 0) (.neg (.var 4))) (.var 4)) (by decide +kernel)
      have z : ((0 : Ext p ν) + a11) = a11 := xsound (xlook [a00, a01, a02, a10, a11, a12, a20, a21, a22, k]) (.add .zero (.var 4)) (.var 4) (by decide +kernel)
      rw [f_d01] at e
      exact e.trans z
    have g_d12 : a11 = a22 := by
      have e : a11 = ((a11 + -a22) + a22) := xsound (xlook [a00, a01, a02, a10, a11, a12, a20, a21, a22, k]) (.var 4) (.add (.add (.var 4) (.neg (.var 8))) (.var 8)) (by decide +kernel)
      have z : ((0 : Ext p ν) + a22) = a22 := xsound (xlook [a00, a01, a02, a10, a11, a12, a20, a21, a22, k]) (.add .zero (.var 8)) (.var 8) (by decide +kernel)
      rw [f_d12] at e
      exact e.trans z
    exact ⟨f_a01, f_a02, f_a10, f_a12, f_a20, f_a21, g_d01, g_d12⟩


/-- 27:C19 — an entry `x` of a matrix that commutes with a diagonal matrix, between a direction of value `a` (its row)
and a direction of value `b` (its column), is zero when `a − b` is invertible. On the internal frame the drive has the
values `1`, `η` and `η⁻¹`, so a commuting matrix has the blocks of the colour part and of the two lines of the doublet. -/
theorem offblock_zero {x a b k : Ext p ν} (hk : (a + -b) * k = 1) (hx : x * b = a * x) : x = 0 := by
  have e : x * ((a + -b) * k) = (a * x + -(x * b)) * k :=
    xsound (xlook [x, a, b, k]) (.mul (.var 0) (.mul (.add (.var 1) (.neg (.var 2))) (.var 3)))
      (.mul (.add (.mul (.var 1) (.var 0)) (.neg (.mul (.var 0) (.var 2)))) (.var 3)) (by decide +kernel)
  have z : (a * x + -(a * x)) * k = 0 :=
    xsound (xlook [x, a, b, k]) (.mul (.add (.mul (.var 1) (.var 0)) (.neg (.mul (.var 1) (.var 0)))) (.var 3)) .zero
      (by decide +kernel)
  have o : x * 1 = x := xsound (xlook [x, a, b, k]) (.mul (.var 0) .one) (.var 0) (by decide +kernel)
  rw [hk, hx] at e
  exact o.symm.trans (e.trans z)

/-- 27:C20 — the triality scalar on a colour frame of rank `m`. On a shell without zero divisors whose base has no
root of `x² + x + 1`, a root `ω` of it in the extension has `ω̄ ω = 1`, so the scalar `ω I_m` is unitary. Its
determinant `ω^m` is one exactly when `3 ∣ m` (`triality_scalar`). -/
theorem triality_rank (hdom : ∀ a b : Shell p, a * b = 0 → a = 0 ∨ b = 0)
    (hno : ¬ ∃ a : Shell p, a * a + a + 1 = 0) {ω : Ext p ν} (hω : ω * ω + ω + 1 = 0) :
    Ext.conj ω * ω = 1 ∧ ∀ m : Nat, ω ^ m = 1 ↔ m % 3 = 0 :=
  have h := triality_scalar hdom hno hω
  ⟨h.2.2.2.1, h.2.2.2.2.2.2.2⟩

end FRC.Unitary

namespace FRC.Interactions

/-- 27:C20 — the complement of an exterior power of even degree has the parity of the rank: the conjugate of the even
exterior algebra is the even one for an even rank and the odd one for an odd rank. -/
theorem conj_parity (n k : Nat) (hk : k ≤ n) (he : k % 2 = 0) : (n - k) % 2 = n % 2 := by
  have e : n = n - k + k := (FRC.Nat.sub_add_cancel hk).symm
  have h : n % 2 = ((n - k) % 2 + k % 2) % 2 := by
    rw [← FRC.Nat.add_mod (n - k) k 2 (by decide), ← e]
  rw [he, Nat.add_zero, FRC.Nat.mod_mod (n - k) 2 (by decide)] at h
  exact h.symm

/-- 27:C21 — from the rank six to the rank `408` the matter of three generations outweighs the gluons:
`11 (k+6) ≤ 3·2^(k+5)` for `k ≤ 402`. The largest integer formed is `3·2^407`, below `Ω`. -/
theorem heavy_three : ∀ k : Nat, k ≤ 402 → 11 * (k + 6) ≤ 3 * 2 ^ (k + 5)
  | 0, _ => by decide
  | k + 1, hk => by
    have ih := heavy_three k (Nat.le_of_succ_le hk)
    have h11 : 11 ≤ 11 * (k + 6) := Nat.le_trans (by decide : 11 ≤ 11 * 6) (Nat.mul_le_mul_left 11 (Nat.le_add_left 6 k))
    have h1 : 11 * (k + 6) + 11 ≤ 3 * 2 ^ (k + 5) + 3 * 2 ^ (k + 5) := Nat.add_le_add ih (Nat.le_trans h11 ih)
    have e1 : 11 * (k + 1 + 6) = 11 * (k + 6) + 11 := rfl
    have e2 : 3 * 2 ^ (k + 1 + 5) = 3 * 2 ^ (k + 5) + 3 * 2 ^ (k + 5) := by
      show 3 * (2 ^ (k + 5) * 2) = _
      rw [← FRC.Nat.mul_assoc, Nat.mul_two]
    rw [e1, e2]; exact h1

/-- 27:C21 — from the rank eight to the rank `408` the matter of one generation outweighs the gluons:
`11 (k+8) ≤ 2^(k+7)` for `k ≤ 400`. -/
theorem heavy_one : ∀ k : Nat, k ≤ 400 → 11 * (k + 8) ≤ 2 ^ (k + 7)
  | 0, _ => by decide
  | k + 1, hk => by
    have ih := heavy_one k (Nat.le_of_succ_le hk)
    have h11 : 11 ≤ 11 * (k + 8) := Nat.le_trans (by decide : 11 ≤ 11 * 8) (Nat.mul_le_mul_left 11 (Nat.le_add_left 8 k))
    have h1 : 11 * (k + 8) + 11 ≤ 2 ^ (k + 7) + 2 ^ (k + 7) := Nat.add_le_add ih (Nat.le_trans h11 ih)
    have e1 : 11 * (k + 1 + 8) = 11 * (k + 8) + 11 := rfl
    have e2 : 2 ^ (k + 1 + 7) = 2 ^ (k + 7) + 2 ^ (k + 7) := by
      show 2 ^ (k + 7) * 2 = _
      rw [Nat.mul_two]
    rw [e1, e2]; exact h1

/-- 27:C21 — the integers of the one-loop form for three generations, `11 m − 3·2^(m−1)`: positive for the ranks
`2, 3, 4, 5` (the values `16, 21, 20, 7`). -/
theorem light_three : 3 * 2 ^ (2 - 1) < 11 * 2 ∧ 3 * 2 ^ (3 - 1) < 11 * 3 ∧ 3 * 2 ^ (4 - 1) < 11 * 4 ∧ 3 * 2 ^ (5 - 1) < 11 * 5 := by
  decide

/-- 27:C21 — the integers of the one-loop form for one generation, `11 m − 2^(m−1)`: positive for the ranks `2` to `7`. -/
theorem light_one : 2 ^ (2 - 1) < 11 * 2 ∧ 2 ^ (3 - 1) < 11 * 3 ∧ 2 ^ (4 - 1) < 11 * 4 ∧ 2 ^ (5 - 1) < 11 * 5 ∧
    2 ^ (6 - 1) < 11 * 6 ∧ 2 ^ (7 - 1) < 11 * 7 := by
  decide

/-- 27:C21 — for three generations the integer is not positive at any rank from six to `408`. -/
theorem bound_three (m : Nat) (h : 6 ≤ m) (hm : m ≤ 408) : ¬ 3 * 2 ^ (m - 1) < 11 * m := by
  intro hb
  have e : m = m - 6 + 6 := (FRC.Nat.sub_add_cancel h).symm
  have h' := heavy_three (m - 6) (FRC.Nat.sub_le_of_le_add hm)
  rw [e] at hb
  exact Nat.lt_irrefl _ (Nat.lt_of_lt_of_le hb h')

/-- 27:C21 — for one generation the integer is not positive at any rank from eight to `408`. -/
theorem bound_one (m : Nat) (h : 8 ≤ m) (hm : m ≤ 408) : ¬ 2 ^ (m - 1) < 11 * m := by
  intro hb
  have e : m = m - 8 + 8 := (FRC.Nat.sub_add_cancel h).symm
  have h' := heavy_one (m - 8) (FRC.Nat.sub_le_of_le_add hm)
  rw [e] at hb
  exact Nat.lt_irrefl _ (Nat.lt_of_lt_of_le hb h')

/-- 27:C21 — on the ranks up to `408`, a multiple of three at which the integer of three generations is
positive is three. -/
theorem colour_rank_three : ∀ m : Nat, 0 < m → m ≤ 408 → m % 3 = 0 → 3 * 2 ^ (m - 1) < 11 * m → m = 3
  | 0, h0, _, _, _ => absurd h0 (by decide)
  | 1, _, _, h3, _ => absurd h3 (by decide)
  | 2, _, _, h3, _ => absurd h3 (by decide)
  | 3, _, _, _, _ => rfl
  | 4, _, _, h3, _ => absurd h3 (by decide)
  | 5, _, _, h3, _ => absurd h3 (by decide)
  | k + 6, _, hm, _, hb => absurd hb (bound_three (k + 6) (Nat.le_add_left 6 k) hm)

/-- 27:C21 — on the ranks up to `408`, an odd multiple of three at which the integer of one generation is
positive is three. -/
theorem colour_rank_three_chiral : ∀ m : Nat, 0 < m → m ≤ 408 → m % 3 = 0 → m % 2 = 1 → 2 ^ (m - 1) < 11 * m → m = 3
  | 0, h0, _, _, _, _ => absurd h0 (by decide)
  | 1, _, _, h3, _, _ => absurd h3 (by decide)
  | 2, _, _, h3, _, _ => absurd h3 (by decide)
  | 3, _, _, _, _, _ => rfl
  | 4, _, _, h3, _, _ => absurd h3 (by decide)
  | 5, _, _, h3, _, _ => absurd h3 (by decide)
  | 6, _, _, _, ho, _ => absurd ho (by decide)
  | 7, _, _, h3, _, _ => absurd h3 (by decide)
  | k + 8, _, hm, _, _, hb => absurd hb (bound_one (k + 8) (Nat.le_add_left 8 k) hm)

/-- 27:C20 — the two exact constraints, the triality and the odd rank, hold together exactly at the ranks congruent to
`3` modulo `6`. -/
theorem exact_ranks (m : Nat) : (m % 3 = 0 ∧ m % 2 = 1) ↔ m % 6 = 3 := by
  obtain ⟨q, hq⟩ := FRC.Nat.mod_spec 6 (by decide) m
  have hr : m % 6 < 6 := Nat.mod_lt m (by decide)
  have h3 : m % 3 = (m % 6) % 3 := by
    have e : m = 3 * (2 * q) + m % 6 := by rw [← FRC.Nat.mul_assoc]; exact hq
    have h := FRC.Nat.add_mul_mod_self_left (m % 6) (2 * q) 3 (by decide)
    rw [← e] at h; exact h
  have h2 : m % 2 = (m % 6) % 2 := by
    have e : m = 2 * (3 * q) + m % 6 := by rw [← FRC.Nat.mul_assoc]; exact hq
    have h := FRC.Nat.add_mul_mod_self_left (m % 6) (3 * q) 2 (by decide)
    rw [← e] at h; exact h
  rw [h3, h2]
  generalize m % 6 = r at hr
  match r, hr with
  | 0, _ => exact ⟨fun h => absurd h.2 (by decide), fun h => absurd h (by decide)⟩
  | 1, _ => exact ⟨fun h => absurd h.1 (by decide), fun h => absurd h (by decide)⟩
  | 2, _ => exact ⟨fun h => absurd h.1 (by decide), fun h => absurd h (by decide)⟩
  | 3, _ => exact ⟨fun _ => rfl, fun _ => ⟨rfl, rfl⟩⟩
  | 4, _ => exact ⟨fun h => absurd h.1 (by decide), fun h => absurd h (by decide)⟩
  | 5, _ => exact ⟨fun h => absurd h.1 (by decide), fun h => absurd h (by decide)⟩
  | k + 6, h => exact absurd h (Nat.not_lt.mpr (Nat.le_add_left 6 k))

/-- The binomial coefficient by Pascal's rule. -/
def binom : Nat → Nat → Nat
  | _, 0 => 1
  | 0, _ + 1 => 0
  | n + 1, k + 1 => binom n k + binom n (k + 1)

/-- The sum of the row `n` of Pascal's triangle up to the entry `k`. -/
def rowSum (n : Nat) : Nat → Nat
  | 0 => binom n 0
  | k + 1 => rowSum n k + binom n (k + 1)

theorem binom_zero_right (n : Nat) : binom n 0 = 1 := by cases n <;> rfl

/-- Above the diagonal Pascal's triangle is zero. -/
theorem binom_above : ∀ n k : Nat, n < k → binom n k = 0
  | 0, 0, h => absurd h (Nat.lt_irrefl 0)
  | 0, _ + 1, _ => rfl
  | _ + 1, 0, h => absurd h (Nat.not_lt_zero _)
  | n + 1, k + 1, h => by
    have h1 : n < k := Nat.lt_of_succ_lt_succ h
    show binom n k + binom n (k + 1) = 0
    rw [binom_above n k h1, binom_above n (k + 1) (Nat.lt_succ_of_lt h1)]

/-- Pascal's rule on the partial sums of a row. -/
theorem rowSum_succ (n : Nat) : ∀ k : Nat, rowSum (n + 1) (k + 1) = rowSum n k + rowSum n (k + 1)
  | 0 => by
    show binom (n + 1) 0 + (binom n 0 + binom n 1) = binom n 0 + (binom n 0 + binom n 1)
    rw [binom_zero_right, binom_zero_right]
  | k + 1 => by
    have ih := rowSum_succ n k
    show rowSum (n + 1) (k + 1) + (binom n (k + 1) + binom n (k + 2)) = rowSum n k + binom n (k + 1) + (rowSum n (k + 1) + binom n (k + 2))
    rw [ih, Nat.add_assoc, Nat.add_assoc, Nat.add_left_comm (rowSum n (k + 1))]

/-- 27:C20 — the index sum of one generation: twice the index of the `k`-th exterior power of the colour frame of rank
`m` is `binom (m − 2) (k − 1)`, and each power occurs twice, so the indices sum to the row sum of `m − 2`, which is
`2^(m−2)`. For the rows up to `406`, the ranks up to `408`. -/
theorem index_sum : ∀ n : Nat, n ≤ 406 → rowSum n n = 2 ^ n
  | 0, _ => rfl
  | n + 1, h => by
    have ih := index_sum n (Nat.le_of_succ_le h)
    have top : rowSum n (n + 1) = rowSum n n := by
      show rowSum n n + binom n (n + 1) = rowSum n n
      rw [binom_above n (n + 1) (Nat.lt_succ_self n), Nat.add_zero]
    rw [rowSum_succ n n, top, ih]
    show 2 ^ n + 2 ^ n = 2 ^ n * 2
    rw [Nat.mul_two]

end FRC.Interactions
