import FrcCore.Theme.Unitary
import FrcCore.Theme.Interactions
import FrcCore.Theme.Field
import FrcCore.Theme.Drive

/-!
# FrcCore.Theme.Torus — the two cycles of the diagonal torus: their points and their periods (27:C15)

The diagonal torus over the extension `K = 𝔽_p[η]`, `η² = ν`, has its split cycles over the shell and its unitary
cycles (`Theme/Unitary.lean`, `torus_cycles`). This file states their orders by elements, on a prime shell with `ν` a
nonsquare and `2 ≠ 0`, and never by a count of a group.

* **The split cycle, `p − 1` points.** The nonzero residues are those of `1, …, p − 1`
  (`Interactions.nonzero_residues`). Each has `a^(p−1) = 1` (`Prime.fermat`), and for `0 < m < p − 1` some nonzero
  residue has `a^m ≠ 1` (`Prime.exists_pow_ne_one`). One of them has order `p − 1` (`Prime.exists_primitive`).
* **The unitary cycle, `p + 1` points.** The unitary points, `σ(w) w = 1`, are `−1` and the `p` points
  `cay ν s = (1 + s η)² / N(1 + s η)`, one for each residue `s`: every `cay ν s` is unitary and is not `−1`
  (`cay_unitary`, `cay_recover`), `s` is read back from `cay ν s` (`cay_inj`), every unitary point other than `−1` is
  `cay ν s` at `s = w.im / (w.re + 1)` (`cay_surj`), and a unitary point with `w.re + 1 = 0` is `−1` (`cay_exc`).
* **Its period.** Multiplication by a unitary point permutes these `p + 1` points, so the product of the points is
  fixed and `w^(p+1) = 1` (`unitary_period`). The products over the extension and their invariance under a permutation
  of the indices are those of `Series.lean`, on the extension.
* **No smaller period.** For `0 < d < p` some unitary point has `w^d ≠ 1` (`unitary_escape`): the second component of
  `(1 + s η)^d` is a polynomial in `s` of degree at most `d` whose coefficient of `s` is `d`, and the root bound of the
  shell applies. At `d = p` the point `−1` escapes (`unitary_escape_top`).
* **A generator.** Some unitary point has order exactly `p + 1` (`unitary_generator`): the argument of
  `Theme/Drive.lean` for the nonzero residues, on the unitary points. A prime power `qᵉ ∣ p + 1` is an order by the
  clause above, and orders `m` and `qᵉ` with `q ∤ m` multiply.

For the drive `ν = g` of a frame the number of the unitary points, `p + 1`, is also counted as the solutions of
`x² − g t² = 1` in `Theme/Causal.lean` (`Causal.plane_nonzero`).

`cycle_orders` conjoins the clauses for the row. No axioms.
-/

namespace FRC.Unitary

open FRC.Shell FRC.Shell.Frame FRC.Extension

variable {p : Nat} [Pos p] {ν : Shell p}

/-! ## Inverses on a prime shell -/

/-- Fermat's inverse on a prime shell: `a · a^(p−2) = 1` for `a ≠ 0`. -/
theorem mul_pow_pred (hp : FRC.Nat.isPrime p) {a : Shell p} (ha : a ≠ 0) : a * a ^ (p - 2) = 1 := by
  have h2 : p - 1 = (p - 2) + 1 := by
    have h := hp.1
    match p, h with
    | k + 2, _ => rfl
  rw [Shell.mul_comm, ← Shell.pow_succ, ← h2]
  exact Prime.fermat hp ha

/-- For a nonsquare `ν` the norm `1 − ν s²` of `1 + s η` is not zero. -/
theorem cnorm_ne_zero (hp : FRC.Nat.isPrime p) (hν : ¬ ∃ y : Shell p, y * y = ν) (s : Shell p) :
    1 + -(ν * (s * s)) ≠ 0 := fun h => by
  have h1 : ν * (s * s) = 1 := by
    have e : ∀ r : Shell p, ((ν * (s * s)) + (1 + -(ν * (s * s)))) = 1 := fun r => Shell.Frame.RE.sound (Shell.Frame.look [ν, s, r]) (.add (.mul (.var 0) (.mul (.var 1) (.var 1))) (.add .one (.neg (.mul (.var 0) (.mul (.var 1) (.var 1)))))) .one (by decide +kernel)
    have e' := e 0
    rw [h, Shell.add_zero] at e'
    exact e'
  have hs : s ≠ 0 := fun e => Prime.one_ne_zero hp (by rw [← h1, e, Shell.mul_zero, Shell.mul_zero])
  have hr := mul_pow_pred hp hs
  exact hν ⟨s ^ (p - 2), by
    have e : ∀ r : Shell p, ((ν * (s * s)) * (r * r)) = (ν * ((s * r) * (s * r))) := fun r => Shell.Frame.RE.sound (Shell.Frame.look [ν, s, r]) (.mul (.mul (.var 0) (.mul (.var 1) (.var 1))) (.mul (.var 2) (.var 2))) (.mul (.var 0) (.mul (.mul (.var 1) (.var 2)) (.mul (.var 1) (.var 2)))) (by decide +kernel)
    have e' := e (s ^ (p - 2))
    rw [h1, hr, Shell.one_mul, Shell.mul_one, Shell.mul_one] at e'
    exact e'⟩

/-! ## The Cayley points of the unitary cycle -/

/-- The algebra of a Cayley point, with `i` the inverse of the norm `1 − ν s²`. -/
theorem cay_alg {s i : Shell p} (hi : (1 + -(ν * (s * s))) * i = 1) :
    ((((1 + (ν * (s * s))) * i) * ((1 + (ν * (s * s))) * i)) + (ν * (-((s + s) * i) * ((s + s) * i)))) = 1 ∧ ((((1 + (ν * (s * s))) * i) * ((s + s) * i)) + (-((s + s) * i) * ((1 + (ν * (s * s))) * i))) = 0 ∧ (((1 + (ν * (s * s))) * i) + 1) = ((1 + 1) * i) ∧ ((s + s) * i) = (s * ((1 + 1) * i)) := by
  refine ⟨?_, Shell.Frame.RE.sound (Shell.Frame.look [ν, s, i]) (.add (.mul (.mul (.add .one (.mul (.var 0) (.mul (.var 1) (.var 1)))) (.var 2)) (.mul (.add (.var 1) (.var 1)) (.var 2))) (.mul (.neg (.mul (.add (.var 1) (.var 1)) (.var 2))) (.mul (.add .one (.mul (.var 0) (.mul (.var 1) (.var 1)))) (.var 2)))) .zero (by decide +kernel), ?_, Shell.Frame.RE.sound (Shell.Frame.look [ν, s, i]) (.mul (.add (.var 1) (.var 1)) (.var 2)) (.mul (.var 1) (.mul (.add .one .one) (.var 2))) (by decide +kernel)⟩
  · have e : ((((1 + (ν * (s * s))) * i) * ((1 + (ν * (s * s))) * i)) + (ν * (-((s + s) * i) * ((s + s) * i)))) = (((1 + -(ν * (s * s))) * i) * ((1 + -(ν * (s * s))) * i)) := Shell.Frame.RE.sound (Shell.Frame.look [ν, s, i]) (.add (.mul (.mul (.add .one (.mul (.var 0) (.mul (.var 1) (.var 1)))) (.var 2)) (.mul (.add .one (.mul (.var 0) (.mul (.var 1) (.var 1)))) (.var 2))) (.mul (.var 0) (.mul (.neg (.mul (.add (.var 1) (.var 1)) (.var 2))) (.mul (.add (.var 1) (.var 1)) (.var 2))))) (.mul (.mul (.add .one (.neg (.mul (.var 0) (.mul (.var 1) (.var 1))))) (.var 2)) (.mul (.add .one (.neg (.mul (.var 0) (.mul (.var 1) (.var 1))))) (.var 2))) (by decide +kernel)
    rw [e, hi, Shell.mul_one]
  · have e : (((1 + (ν * (s * s))) * i) + ((1 + -(ν * (s * s))) * i)) = ((1 + 1) * i) := Shell.Frame.RE.sound (Shell.Frame.look [ν, s, i]) (.add (.mul (.add .one (.mul (.var 0) (.mul (.var 1) (.var 1)))) (.var 2)) (.mul (.add .one (.neg (.mul (.var 0) (.mul (.var 1) (.var 1))))) (.var 2))) (.mul (.add .one .one) (.var 2)) (by decide +kernel)
    rw [hi] at e
    exact e

/-- The algebra of `cay ν s · σ(1 + s η) = 1 + s η`. -/
theorem cay_conj_alg {s i : Shell p} (hi : (1 + -(ν * (s * s))) * i = 1) : ((((1 + (ν * (s * s))) * i) * 1) + (ν * (((s + s) * i) * -s))) = 1 ∧ ((((1 + (ν * (s * s))) * i) * -s) + (((s + s) * i) * 1)) = s := by
  refine ⟨?_, ?_⟩
  · have e : ((((1 + (ν * (s * s))) * i) * 1) + (ν * (((s + s) * i) * -s))) = ((1 + -(ν * (s * s))) * i) := Shell.Frame.RE.sound (Shell.Frame.look [ν, s, i]) (.add (.mul (.mul (.add .one (.mul (.var 0) (.mul (.var 1) (.var 1)))) (.var 2)) .one) (.mul (.var 0) (.mul (.mul (.add (.var 1) (.var 1)) (.var 2)) (.neg (.var 1))))) (.mul (.add .one (.neg (.mul (.var 0) (.mul (.var 1) (.var 1))))) (.var 2)) (by decide +kernel)
    rw [hi] at e
    exact e
  · have e : ((((1 + (ν * (s * s))) * i) * -s) + (((s + s) * i) * 1)) = (s * ((1 + -(ν * (s * s))) * i)) := Shell.Frame.RE.sound (Shell.Frame.look [ν, s, i]) (.add (.mul (.mul (.add .one (.mul (.var 0) (.mul (.var 1) (.var 1)))) (.var 2)) (.neg (.var 1))) (.mul (.mul (.add (.var 1) (.var 1)) (.var 2)) .one)) (.mul (.var 1) (.mul (.add .one (.neg (.mul (.var 0) (.mul (.var 1) (.var 1))))) (.var 2))) (by decide +kernel)
    rw [hi] at e
    exact e.trans (Shell.mul_one s)

/-- The algebra of the inverse map: a unitary `x + t η` with `x + 1` invertible is the Cayley point of `s = t / (x + 1)`. -/
theorem cay_inv_alg {x t j i : Shell p} (hu : x * x + ν * (-t * t) = 1) (hj : (x + 1) * j = 1)
    (hi : (1 + -(ν * ((t * j) * (t * j)))) * i = 1) : ((1 + (ν * ((t * j) * (t * j)))) * i) = x ∧ (((t * j) + (t * j)) * i) = t := by
  have H1 : ((1 + -(ν * ((t * j) * (t * j)))) * ((x + 1) * (x + 1))) = ((1 + 1) * (x + 1)) := by
    have e1 : ((1 + -(ν * ((t * j) * (t * j)))) * ((x + 1) * (x + 1))) = (((x + 1) * (x + 1)) + -(ν * ((t * t) * (((x + 1) * j) * ((x + 1) * j))))) := Shell.Frame.RE.sound (Shell.Frame.look [ν, x, t, j, i]) (.mul (.add .one (.neg (.mul (.var 0) (.mul (.mul (.var 2) (.var 3)) (.mul (.var 2) (.var 3)))))) (.mul (.add (.var 1) .one) (.add (.var 1) .one))) (.add (.mul (.add (.var 1) .one) (.add (.var 1) .one)) (.neg (.mul (.var 0) (.mul (.mul (.var 2) (.var 2)) (.mul (.mul (.add (.var 1) .one) (.var 3)) (.mul (.add (.var 1) .one) (.var 3))))))) (by decide +kernel)
    have e2 : (((x + 1) * (x + 1)) + -(ν * ((t * t) * (1 * 1)))) = (((x * x) + (ν * (-t * t))) + ((x + x) + 1)) := Shell.Frame.RE.sound (Shell.Frame.look [ν, x, t, j, i]) (.add (.mul (.add (.var 1) .one) (.add (.var 1) .one)) (.neg (.mul (.var 0) (.mul (.mul (.var 2) (.var 2)) (.mul .one .one))))) (.add (.add (.mul (.var 1) (.var 1)) (.mul (.var 0) (.mul (.neg (.var 2)) (.var 2)))) (.add (.add (.var 1) (.var 1)) .one)) (by decide +kernel)
    have e3 : (1 + ((x + x) + 1)) = ((1 + 1) * (x + 1)) := Shell.Frame.RE.sound (Shell.Frame.look [ν, x, t, j, i]) (.add .one (.add (.add (.var 1) (.var 1)) .one)) (.mul (.add .one .one) (.add (.var 1) .one)) (by decide +kernel)
    rw [e1, hj, e2, hu, e3]
  have H2 : (1 + -(ν * ((t * j) * (t * j)))) = ((1 + 1) * j) := by
    have e1 : (1 + -(ν * ((t * j) * (t * j)))) = ((((1 + -(ν * ((t * j) * (t * j)))) * ((x + 1) * (x + 1))) * (j * j)) + ((1 + -(ν * ((t * j) * (t * j)))) * (1 + -(((x + 1) * j) * ((x + 1) * j))))) := Shell.Frame.RE.sound (Shell.Frame.look [ν, x, t, j, i]) (.add .one (.neg (.mul (.var 0) (.mul (.mul (.var 2) (.var 3)) (.mul (.var 2) (.var 3)))))) (.add (.mul (.mul (.add .one (.neg (.mul (.var 0) (.mul (.mul (.var 2) (.var 3)) (.mul (.var 2) (.var 3)))))) (.mul (.add (.var 1) .one) (.add (.var 1) .one))) (.mul (.var 3) (.var 3))) (.mul (.add .one (.neg (.mul (.var 0) (.mul (.mul (.var 2) (.var 3)) (.mul (.var 2) (.var 3)))))) (.add .one (.neg (.mul (.mul (.add (.var 1) .one) (.var 3)) (.mul (.add (.var 1) .one) (.var 3))))))) (by decide +kernel)
    have e2 : ((((1 + 1) * (x + 1)) * (j * j)) + ((1 + -(ν * ((t * j) * (t * j)))) * (1 + -(1 * 1)))) = (((1 + 1) * j) * ((x + 1) * j)) := Shell.Frame.RE.sound (Shell.Frame.look [ν, x, t, j, i]) (.add (.mul (.mul (.add .one .one) (.add (.var 1) .one)) (.mul (.var 3) (.var 3))) (.mul (.add .one (.neg (.mul (.var 0) (.mul (.mul (.var 2) (.var 3)) (.mul (.var 2) (.var 3)))))) (.add .one (.neg (.mul .one .one))))) (.mul (.mul (.add .one .one) (.var 3)) (.mul (.add (.var 1) .one) (.var 3))) (by decide +kernel)
    rw [e1, H1, hj, e2, hj, Shell.mul_one]
  have H3 : (((1 + 1) * j) * i) = 1 := by
    rw [← H2]
    exact hi
  refine ⟨?_, ?_⟩
  · have e1 : ((1 + (ν * ((t * j) * (t * j)))) * i) = (((1 + 1) * i) + -((1 + -(ν * ((t * j) * (t * j)))) * i)) := Shell.Frame.RE.sound (Shell.Frame.look [ν, x, t, j, i]) (.mul (.add .one (.mul (.var 0) (.mul (.mul (.var 2) (.var 3)) (.mul (.var 2) (.var 3))))) (.var 4)) (.add (.mul (.add .one .one) (.var 4)) (.neg (.mul (.add .one (.neg (.mul (.var 0) (.mul (.mul (.var 2) (.var 3)) (.mul (.var 2) (.var 3)))))) (.var 4)))) (by decide +kernel)
    have e2 : ((1 + 1) * i) = (((x + 1) * (((1 + 1) * j) * i)) + (((1 + 1) * i) * (1 + -((x + 1) * j)))) := Shell.Frame.RE.sound (Shell.Frame.look [ν, x, t, j, i]) (.mul (.add .one .one) (.var 4)) (.add (.mul (.add (.var 1) .one) (.mul (.mul (.add .one .one) (.var 3)) (.var 4))) (.mul (.mul (.add .one .one) (.var 4)) (.add .one (.neg (.mul (.add (.var 1) .one) (.var 3)))))) (by decide +kernel)
    have e3 : ((((x + 1) * 1) + (((1 + 1) * i) * (1 + -1))) + -1) = x := Shell.Frame.RE.sound (Shell.Frame.look [ν, x, t, j, i]) (.add (.add (.mul (.add (.var 1) .one) .one) (.mul (.mul (.add .one .one) (.var 4)) (.add .one (.neg .one)))) (.neg .one)) (.var 1) (by decide +kernel)
    rw [e1, hi, e2, H3, hj, e3]
  · have e1 : (((t * j) + (t * j)) * i) = (t * (((1 + 1) * j) * i)) := Shell.Frame.RE.sound (Shell.Frame.look [ν, x, t, j, i]) (.mul (.add (.mul (.var 2) (.var 3)) (.mul (.var 2) (.var 3))) (.var 4)) (.mul (.var 2) (.mul (.mul (.add .one .one) (.var 3)) (.var 4))) (by decide +kernel)
    rw [e1, H3, Shell.mul_one]

/-- The algebra of the exceptional point: a unitary `x + t η` with `x + 1 = 0` is `−1`. -/
theorem cay_exc_alg (hp : FRC.Nat.isPrime p) (hν : ¬ ∃ y : Shell p, y * y = ν) {x t : Shell p}
    (hu : x * x + ν * (-t * t) = 1) (hx : x + 1 = 0) : x = -1 ∧ t = 0 := by
  have ex : x = -1 := by
    have e : x = ((x + 1) + -1) := Shell.Frame.RE.sound (Shell.Frame.look [ν, x, t]) (.var 1) (.add (.add (.var 1) .one) (.neg .one)) (by decide +kernel)
    rw [hx, Shell.zero_add] at e
    exact e
  have et : ν * (t * t) = 0 := by
    have e : (ν * (t * t)) = (((x + 1) * (x + -1)) + (1 + -((x * x) + (ν * (-t * t))))) := Shell.Frame.RE.sound (Shell.Frame.look [ν, x, t]) (.mul (.var 0) (.mul (.var 2) (.var 2))) (.add (.mul (.add (.var 1) .one) (.add (.var 1) (.neg .one))) (.add .one (.neg (.add (.mul (.var 1) (.var 1)) (.mul (.var 0) (.mul (.neg (.var 2)) (.var 2))))))) (by decide +kernel)
    rw [hu, hx, Shell.zero_mul, Shell.add_neg, Shell.add_zero] at e
    exact e
  refine ⟨ex, ?_⟩
  match Prime.mul_eq_zero hp et with
  | .inl h0 => exact absurd ⟨0, (Shell.zero_mul 0).trans h0.symm⟩ hν
  | .inr htt =>
    match Prime.mul_eq_zero hp htt with
    | .inl h => exact h
    | .inr h => exact h

/-- The Cayley point of the residue `s`: `(1 + s η)² / N(1 + s η)`, with `N(1 + s η) = 1 − ν s²` inverted by Fermat. -/
def cay (ν s : Shell p) : Ext p ν :=
  ⟨(1 + ν * (s * s)) * (1 + -(ν * (s * s))) ^ (p - 2), (s + s) * (1 + -(ν * (s * s))) ^ (p - 2)⟩

/-- 27:C15 — a Cayley point is a unitary point. -/
theorem cay_unitary (hp : FRC.Nat.isPrime p) (hν : ¬ ∃ y : Shell p, y * y = ν) (s : Shell p) :
    Ext.conj (cay ν s) * cay ν s = 1 :=
  have h := cay_alg (ν := ν) (mul_pow_pred hp (cnorm_ne_zero hp hν s))
  Ext.ext h.1 h.2.1

/-- 27:C15 — a Cayley point is not `−1`, and its residue is read back: `s = im / (re + 1)`. -/
theorem cay_recover (hp : FRC.Nat.isPrime p) (hν : ¬ ∃ y : Shell p, y * y = ν) (h2 : (1 : Shell p) + 1 ≠ 0)
    (s : Shell p) : (cay ν s).re + 1 ≠ 0 ∧ (cay ν s).im * ((cay ν s).re + 1) ^ (p - 2) = s := by
  have hi := mul_pow_pred hp (cnorm_ne_zero hp hν s)
  have h := cay_alg (ν := ν) hi
  have hi0 : (1 + -(ν * (s * s))) ^ (p - 2) ≠ 0 := fun e => Prime.one_ne_zero hp (by rw [← hi, e, Shell.mul_zero])
  have hq : (cay ν s).re + 1 = (1 + 1) * (1 + -(ν * (s * s))) ^ (p - 2) := h.2.2.1
  have hq0 : (cay ν s).re + 1 ≠ 0 := by rw [hq]; exact Prime.mul_ne_zero hp h2 hi0
  refine ⟨hq0, ?_⟩
  have hj := mul_pow_pred hp hq0
  have him : (cay ν s).im = s * ((cay ν s).re + 1) := by rw [hq]; exact h.2.2.2
  rw [him, Shell.mul_assoc, hj, Shell.mul_one]

/-- 27:C15 — the Cayley points of two residues are equal only for one residue. -/
theorem cay_inj (hp : FRC.Nat.isPrime p) (hν : ¬ ∃ y : Shell p, y * y = ν) (h2 : (1 : Shell p) + 1 ≠ 0)
    {s s' : Shell p} (h : cay ν s = cay ν s') : s = s' := by
  have a := (cay_recover hp hν h2 s).2
  rw [h] at a
  exact a.symm.trans (cay_recover hp hν h2 s').2

/-- 27:C15 — a unitary point other than `−1` is the Cayley point of `s = w.im / (w.re + 1)`. -/
theorem cay_surj (hp : FRC.Nat.isPrime p) (hν : ¬ ∃ y : Shell p, y * y = ν) {w : Ext p ν}
    (hw : Ext.conj w * w = 1) (h1 : w.re + 1 ≠ 0) : cay ν (w.im * (w.re + 1) ^ (p - 2)) = w := by
  have hu : w.re * w.re + ν * (-w.im * w.im) = 1 := Ext.re_congr hw
  have h := cay_inv_alg hu (mul_pow_pred hp h1)
    (mul_pow_pred hp (cnorm_ne_zero hp hν (w.im * (w.re + 1) ^ (p - 2))))
  exact Ext.ext h.1 h.2

/-- 27:C15 — a unitary point with `w.re + 1 = 0` is `−1`. -/
theorem cay_exc (hp : FRC.Nat.isPrime p) (hν : ¬ ∃ y : Shell p, y * y = ν) {w : Ext p ν}
    (hw : Ext.conj w * w = 1) (h1 : w.re + 1 = 0) : w = -1 := by
  have h := cay_exc_alg hp hν (Ext.re_congr hw) h1
  exact Ext.ext h.1 (h.2.trans Shell.neg_zero.symm)

/-- `−1` is a unitary point. -/
theorem neg_one_unitary : Ext.conj (-1 : Ext p ν) * -1 = 1 :=
  Ext.ext
    (Shell.Frame.RE.sound (Shell.Frame.look [ν]) (.add (.mul (.neg .one) (.neg .one)) (.mul (.var 0) (.mul (.neg (.neg .zero)) (.neg .zero)))) .one (by decide +kernel))
    (Shell.Frame.RE.sound (Shell.Frame.look [ν]) (.add (.mul (.neg .one) (.neg .zero)) (.mul (.neg (.neg .zero)) (.neg .one))) .zero (by decide +kernel))

/-- `1` is a unitary point. -/
theorem one_unitary : Ext.conj (1 : Ext p ν) * 1 = 1 :=
  Ext.ext
    (Shell.Frame.RE.sound (Shell.Frame.look [ν]) (.add (.mul .one .one) (.mul (.var 0) (.mul (.neg .zero) .zero))) .one (by decide +kernel))
    (Shell.Frame.RE.sound (Shell.Frame.look [ν]) (.add (.mul .one .zero) (.mul (.neg .zero) .one)) .zero (by decide +kernel))

/-- The product of two unitary points is a unitary point. -/
theorem unitary_mul {a b : Ext p ν} (ha : Ext.conj a * a = 1) (hb : Ext.conj b * b = 1) :
    Ext.conj (a * b) * (a * b) = 1 := by
  have e : ((Ext.conj a * Ext.conj b) * (a * b)) = ((Ext.conj a * a) * (Ext.conj b * b)) := xsound (xlook [Ext.conj a, Ext.conj b, a, b]) (.mul (.mul (.var 0) (.var 1)) (.mul (.var 2) (.var 3))) (.mul (.mul (.var 0) (.var 2)) (.mul (.var 1) (.var 3))) (by decide +kernel)
  rw [Ext.conj_mul, e, ha, hb]
  exact Ext.one_mul 1

/-! ## Products over the extension, invariant under a permutation of the indices -/

/-- `Π_{j<n} f j` on the extension. -/
def eprod (f : Nat → Ext p ν) : Nat → Ext p ν
  | 0 => 1
  | n + 1 => eprod f n * f n

theorem eprod_congr {f h : Nat → Ext p ν} : ∀ n, (∀ j, j < n → f j = h j) → eprod f n = eprod h n
  | 0, _ => rfl
  | n + 1, e => by
    show eprod f n * f n = eprod h n * h n
    rw [eprod_congr n (fun j hj => e j (Nat.lt_succ_of_lt hj)), e n (Nat.lt_succ_self n)]

/-- A common factor leaves the product as its power. -/
theorem eprod_mul_left (a : Ext p ν) (G : Nat → Ext p ν) : ∀ n, eprod (fun j => a * G j) n = a ^ n * eprod G n
  | 0 => (Ext.one_mul 1).symm
  | n + 1 => by
    show eprod (fun j => a * G j) n * (a * G n) = (a ^ n * a) * (eprod G n * G n)
    rw [eprod_mul_left a G n]
    exact xsound (xlook [a ^ n, eprod G n, a, G n]) (.mul (.mul (.var 0) (.var 1)) (.mul (.var 2) (.var 3))) (.mul (.mul (.var 0) (.var 2)) (.mul (.var 1) (.var 3))) (by decide +kernel)

/-- The product of unitary points is a unitary point. -/
theorem unitary_eprod {f : Nat → Ext p ν} : ∀ n, (∀ j, j < n → Ext.conj (f j) * f j = 1) →
    Ext.conj (eprod f n) * eprod f n = 1
  | 0, _ => one_unitary
  | n + 1, h => unitary_mul (unitary_eprod n (fun j hj => h j (Nat.lt_succ_of_lt hj))) (h n (Nat.lt_succ_self n))

/-- The product of `F` over a list of indices. -/
def elist (F : Nat → Ext p ν) : List Nat → Ext p ν
  | [] => 1
  | a :: l => F a * elist F l

theorem elist_imageList (F : Nat → Ext p ν) (σ : Nat → Nat) (n : Nat) :
    elist F (imageList σ n) = eprod (fun j => F (σ j)) n := by
  induction n with
  | zero => rfl
  | succ n ih =>
    show F (σ n) * elist F (imageList σ n) = eprod (fun j => F (σ j)) n * F (σ n); rw [ih, Ext.mul_comm]

theorem elist_erase (F : Nat → Ext p ν) {v : Nat} : ∀ {l : List Nat}, Pigeonhole.mem v l →
    elist F l = F v * elist F (Pigeonhole.erase v l)
  | [], h => absurd h id
  | a :: l, h => by
    exact match Nat.decEq a v with
      | isTrue e => by rw [show Pigeonhole.erase v (a :: l) = l from ite_eq_left e, e]; rfl
      | isFalse e => by
          rw [show Pigeonhole.erase v (a :: l) = a :: Pigeonhole.erase v l from ite_eq_right e]
          have hm : Pigeonhole.mem v l := match h with
            | Or.inl h' => absurd h'.symm e
            | Or.inr h' => h'
          show F a * elist F l = F v * (F a * elist F (Pigeonhole.erase v l))
          rw [elist_erase F hm]
          exact xsound (xlook [F a, F v, elist F (Pigeonhole.erase v l)]) (.mul (.var 0) (.mul (.var 1) (.var 2))) (.mul (.var 1) (.mul (.var 0) (.var 2))) (by decide +kernel)

/-- A product over any list of `n` distinct indices below `n` is the product over `0, …, n − 1`. -/
theorem elist_eq_eprod (F : Nat → Ext p ν) : ∀ (n : Nat) (l : List Nat), Pigeonhole.NoDup l →
    (∀ e, Pigeonhole.mem e l → e < n) → l.length = n → elist F l = eprod F n
  | 0, [], _, _, _ => rfl
  | 0, a :: l, _, hb, _ => absurd (hb a (Or.inl rfl)) (Nat.not_lt_zero a)
  | n + 1, l, hnd, hb, hlen => by
    have hm : Pigeonhole.mem n l := Pigeonhole.mem_of_nodup_of_length_lt (n + 1) l hnd hb hlen n (Nat.lt_succ_self n)
    rw [elist_erase F hm]
    show F n * elist F (Pigeonhole.erase n l) = eprod F n * F n
    rw [Ext.mul_comm]
    have hb' : ∀ e, Pigeonhole.mem e (Pigeonhole.erase n l) → e < n := fun e he =>
      match Nat.lt_or_ge e n with
      | Or.inl hlt => hlt
      | Or.inr hge =>
        have : e = n := Nat.le_antisymm (Nat.le_of_lt_succ (hb e (Pigeonhole.mem_of_mem_erase he))) hge
        absurd (this ▸ he) (Pigeonhole.not_mem_erase_self n hnd)
    have hlen' : (Pigeonhole.erase n l).length = n := by
      have := Pigeonhole.length_erase_of_mem hm; rw [hlen] at this; exact Nat.succ.inj this
    rw [elist_eq_eprod F n (Pigeonhole.erase n l) (Pigeonhole.nodup_erase n hnd) hb' hlen']

/-- Permutation invariance on the extension: for `σ` injective on `[0, n)` with values below `n`,
`Π_{j<n} F (σ j) = Π_{l<n} F l`. -/
theorem eprod_perm (F : Nat → Ext p ν) (σ : Nat → Nat) (n : Nat) (hlt : ∀ j, j < n → σ j < n)
    (hinj : ∀ i j, i < n → j < n → σ i = σ j → i = j) :
    eprod (fun j => F (σ j)) n = eprod F n := by
  rw [← elist_imageList]
  exact elist_eq_eprod F n (imageList σ n) (imageList_nodup hinj (Nat.le_refl n))
    (fun e he => match mem_imageList he with | ⟨j, hj, e'⟩ => e' ▸ hlt j hj) (imageList_length σ n)

/-! ## The `p + 1` unitary points, indexed, and the period -/

/-- The unitary points indexed by `0, …, p`: the Cayley point of the residue `j` for `j < p`, and `−1` at `p`. -/
def upt (ν : Shell p) (j : Nat) : Ext p ν := if j < p then cay ν (ofNat j) else -1

/-- The index of a unitary point. -/
def uidx (w : Ext p ν) : Nat := if w.re + 1 = 0 then p else (w.im * (w.re + 1) ^ (p - 2)).val

theorem upt_unitary (hp : FRC.Nat.isPrime p) (hν : ¬ ∃ y : Shell p, y * y = ν) (j : Nat) :
    Ext.conj (upt ν j) * upt ν j = 1 :=
  match Nat.decLt j p with
  | isTrue h => by
    rw [show upt ν j = cay ν (ofNat j) from ite_eq_left h]
    exact cay_unitary hp hν _
  | isFalse h => by
    rw [show upt ν j = -1 from ite_eq_right h]
    exact neg_one_unitary

/-- Every unitary point is the point of its index, and the index is below `p + 1`. -/
theorem upt_uidx (hp : FRC.Nat.isPrime p) (hν : ¬ ∃ y : Shell p, y * y = ν) {w : Ext p ν}
    (hw : Ext.conj w * w = 1) : upt ν (uidx w) = w ∧ uidx w < p + 1 :=
  match decEq (w.re + 1) 0 with
  | isTrue h => by
    have e : uidx w = p := ite_eq_left h
    rw [e]
    exact ⟨(show upt ν p = -1 from ite_eq_right (Nat.lt_irrefl p)).trans (cay_exc hp hν hw h).symm, Nat.lt_succ_self p⟩
  | isFalse h => by
    have e : uidx w = (w.im * (w.re + 1) ^ (p - 2)).val := ite_eq_right h
    rw [e]
    have hl := (w.im * (w.re + 1) ^ (p - 2)).lt
    refine ⟨?_, Nat.lt_succ_of_lt hl⟩
    rw [show upt ν (w.im * (w.re + 1) ^ (p - 2)).val = cay ν (ofNat (w.im * (w.re + 1) ^ (p - 2)).val) from ite_eq_left hl,
      Shell.ofNat_val]
    exact cay_surj hp hν hw h

/-- The index of the `j`-th point is `j`, for `j ≤ p`. -/
theorem uidx_upt (hp : FRC.Nat.isPrime p) (hν : ¬ ∃ y : Shell p, y * y = ν) (h2 : (1 : Shell p) + 1 ≠ 0)
    {j : Nat} (hj : j < p + 1) : uidx (upt ν j) = j :=
  match Nat.decLt j p with
  | isTrue h => by
    have r := cay_recover hp hν h2 (ofNat j)
    rw [show upt ν j = cay ν (ofNat j) from ite_eq_left h]
    have e : uidx (cay ν (ofNat j)) = ((cay ν (ofNat j)).im * ((cay ν (ofNat j)).re + 1) ^ (p - 2)).val := ite_eq_right r.1
    rw [e, r.2, Shell.val_ofNat]
    exact FRC.Nat.mod_eq_of_lt h
  | isFalse h => by
    have ej : j = p := Nat.le_antisymm (Nat.le_of_lt_succ hj) (Nat.ge_of_not_lt h)
    rw [show upt ν j = -1 from ite_eq_right h, ej]
    exact ite_eq_left (Shell.neg_add 1)

/-- 27:C15 — the period of the unitary cycle: a unitary point has `w^(p+1) = 1`. Multiplication by `w` permutes the
`p + 1` unitary points, so `w^(p+1) · Π u = Π u`, and the product, a unitary point, cancels. -/
theorem unitary_period (hp : FRC.Nat.isPrime p) (hν : ¬ ∃ y : Shell p, y * y = ν) (h2 : (1 : Shell p) + 1 ≠ 0)
    {w : Ext p ν} (hw : Ext.conj w * w = 1) : w ^ (p + 1) = 1 := by
  have hU : ∀ j, Ext.conj (upt ν j) * upt ν j = 1 := upt_unitary hp hν
  have hwU : ∀ j, Ext.conj (w * upt ν j) * (w * upt ν j) = 1 := fun j => unitary_mul hw (hU j)
  have hF : ∀ j, j < p + 1 → upt ν (uidx (w * upt ν j)) = w * upt ν j := fun j _ => (upt_uidx hp hν (hwU j)).1
  have hlt : ∀ j, j < p + 1 → uidx (w * upt ν j) < p + 1 := fun j _ => (upt_uidx hp hν (hwU j)).2
  have hc : ∀ u : Ext p ν, Ext.conj w * (w * u) = u := fun u => by rw [← Ext.mul_assoc, hw, Ext.one_mul]
  have hinj : ∀ i j, i < p + 1 → j < p + 1 → uidx (w * upt ν i) = uidx (w * upt ν j) → i = j := fun i j hi hj e => by
    have e1 : w * upt ν i = w * upt ν j := (hF i hi).symm.trans ((congrArg (upt ν) e).trans (hF j hj))
    have e2 : upt ν i = upt ν j := (hc (upt ν i)).symm.trans ((congrArg (fun u => Ext.conj w * u) e1).trans (hc (upt ν j)))
    exact (uidx_upt hp hν h2 hi).symm.trans ((congrArg uidx e2).trans (uidx_upt hp hν h2 hj))
  have hperm := eprod_perm (upt ν) (fun j => uidx (w * upt ν j)) (p + 1) hlt hinj
  rw [eprod_congr (f := fun j => upt ν (uidx (w * upt ν j))) (h := fun j => w * upt ν j) (p + 1) hF,
    eprod_mul_left w (upt ν) (p + 1)] at hperm
  have hP := unitary_eprod (f := upt ν) (p + 1) (fun j _ => hU j)
  calc w ^ (p + 1) = (w ^ (p + 1) * eprod (upt ν) (p + 1)) * Ext.conj (eprod (upt ν) (p + 1)) := by
        rw [Ext.mul_assoc, Ext.mul_comm (eprod (upt ν) (p + 1)), hP, Ext.mul_one]
    _ = 1 := by rw [hperm, Ext.mul_comm, hP]

/-! ## No smaller period on the unitary cycle

The components of `(1 + s η)^n` are polynomials in `s` of degree at most `n`, and the coefficient of `s` in the second
is `n`. If every unitary point had `w^d = 1`, the second component of `(1 + s η)^d` would vanish at every residue `s`,
and for `d < p` the root bound of the shell would make its coefficient `d` zero. -/

/-- `X · f` on coefficient functions. -/
def pshift (f : Nat → Shell p) : Nat → Shell p
  | 0 => 0
  | k + 1 => f k

theorem eval_add (f h : Nat → Shell p) (n : Nat) (a : Shell p) :
    Poly.eval (fun i => f i + h i) n a = Poly.eval f n a + Poly.eval h n a := by
  show sumRange (fun i => (f i + h i) * a ^ i) (n + 1)
    = sumRange (fun i => f i * a ^ i) (n + 1) + sumRange (fun i => h i * a ^ i) (n + 1)
  rw [← sum_add]
  exact sum_congr (n + 1) (fun i _ => Shell.right_distrib (f i) (h i) (a ^ i))

theorem eval_smul (c : Shell p) (f : Nat → Shell p) (n : Nat) (a : Shell p) :
    Poly.eval (fun i => c * f i) n a = c * Poly.eval f n a := by
  show sumRange (fun i => c * f i * a ^ i) (n + 1) = c * sumRange (fun i => f i * a ^ i) (n + 1)
  rw [← sum_mul_left]
  exact sum_congr (n + 1) (fun i _ => Shell.mul_assoc c (f i) (a ^ i))

theorem eval_shift (f : Nat → Shell p) (n : Nat) (a : Shell p) :
    Poly.eval (pshift f) (n + 1) a = a * Poly.eval f n a := by
  show sumRange (fun i => pshift f i * a ^ i) (n + 1 + 1) = a * sumRange (fun i => f i * a ^ i) (n + 1)
  rw [sumRange_succ', ← sum_mul_left]
  show (0 : Shell p) * a ^ 0 + sumRange (fun l => f l * (a ^ l * a)) (n + 1) = sumRange (fun l => a * (f l * a ^ l)) (n + 1)
  rw [Shell.zero_mul, Shell.zero_add]
  exact sum_congr (n + 1) (fun i _ => Shell.Frame.RE.sound (Shell.Frame.look [f i, a ^ i, a]) (.mul (.var 0) (.mul (.var 1) (.var 2))) (.mul (.var 2) (.mul (.var 0) (.var 1))) (by decide +kernel))

/-- The components of `(1 + s η)^n` as coefficient functions in `s`. -/
def cpoly (ν : Shell p) : Nat → (Nat → Shell p) × (Nat → Shell p)
  | 0 => (fun i => if i = 0 then 1 else 0, fun _ => 0)
  | n + 1 => (fun i => (cpoly ν n).1 i + ν * pshift (cpoly ν n).2 i, fun i => (cpoly ν n).2 i + pshift (cpoly ν n).1 i)

theorem cpoly_bound (ν : Shell p) : ∀ n, Poly.Bound (cpoly ν n).1 n ∧ Poly.Bound (cpoly ν n).2 n
  | 0 => ⟨fun _ hi => ite_eq_right (Nat.ne_of_gt hi), fun _ _ => rfl⟩
  | n + 1 => by
    have ih := cpoly_bound ν n
    refine ⟨fun i hi => ?_, fun i hi => ?_⟩
    · match i, hi with
      | 0, hi => exact absurd hi (Nat.not_lt_zero _)
      | k + 1, hi =>
        have hk : n < k := Nat.lt_of_succ_lt_succ hi
        show (cpoly ν n).1 (k + 1) + ν * (cpoly ν n).2 k = 0
        rw [ih.1 (k + 1) (Nat.lt_succ_of_lt hk), ih.2 k hk, Shell.mul_zero, Shell.add_zero]
    · match i, hi with
      | 0, hi => exact absurd hi (Nat.not_lt_zero _)
      | k + 1, hi =>
        have hk : n < k := Nat.lt_of_succ_lt_succ hi
        show (cpoly ν n).2 (k + 1) + (cpoly ν n).1 k = 0
        rw [ih.2 (k + 1) (Nat.lt_succ_of_lt hk), ih.1 k hk, Shell.add_zero]

/-- The constant coefficient of the first component is `1`, and the coefficient of `s` in the second is `n`. -/
theorem cpoly_coeff (ν : Shell p) : ∀ n, (cpoly ν n).1 0 = 1 ∧ (cpoly ν n).2 1 = sumRange (fun _ => 1) n
  | 0 => ⟨show (if (0 : Nat) = 0 then (1 : Shell p) else 0) = 1 from ite_eq_left rfl, rfl⟩
  | n + 1 => by
    have ih := cpoly_coeff ν n
    refine ⟨?_, ?_⟩
    · show (cpoly ν n).1 0 + ν * (0 : Shell p) = 1
      rw [ih.1, Shell.mul_zero, Shell.add_zero]
    · show (cpoly ν n).2 1 + (cpoly ν n).1 0 = sumRange (fun _ => 1) n + 1
      rw [ih.1, ih.2]

/-- The components of `(1 + s η)^n` are the values of the two polynomials at `s`. -/
theorem cpoly_pow (ν s : Shell p) : ∀ n, ((⟨1, s⟩ : Ext p ν) ^ n).re = Poly.eval (cpoly ν n).1 n s ∧
    ((⟨1, s⟩ : Ext p ν) ^ n).im = Poly.eval (cpoly ν n).2 n s
  | 0 => by
    refine ⟨?_, ?_⟩
    · show (1 : Shell p) = 0 + (if (0 : Nat) = 0 then 1 else 0) * s ^ 0
      rw [ite_eq_left rfl, Shell.pow_zero, Shell.mul_one, Shell.zero_add]
    · show (0 : Shell p) = 0 + 0 * s ^ 0
      rw [Shell.zero_mul, Shell.add_zero]
  | n + 1 => by
    have ih := cpoly_pow ν s n
    have hb := cpoly_bound ν n
    have eA : Poly.eval (cpoly ν (n + 1)).1 (n + 1) s
        = Poly.eval (cpoly ν n).1 n s + ν * (s * Poly.eval (cpoly ν n).2 n s) := by
      show Poly.eval (fun i => (cpoly ν n).1 i + ν * pshift (cpoly ν n).2 i) (n + 1) s = _
      rw [eval_add, eval_smul, eval_shift, Poly.eval_bound hb.1 (Nat.le_succ n)]
    have eB : Poly.eval (cpoly ν (n + 1)).2 (n + 1) s
        = Poly.eval (cpoly ν n).2 n s + s * Poly.eval (cpoly ν n).1 n s := by
      show Poly.eval (fun i => (cpoly ν n).2 i + pshift (cpoly ν n).1 i) (n + 1) s = _
      rw [eval_add, eval_shift, Poly.eval_bound hb.2 (Nat.le_succ n)]
    refine ⟨?_, ?_⟩
    · show ((⟨1, s⟩ : Ext p ν) ^ n).re * 1 + ν * (((⟨1, s⟩ : Ext p ν) ^ n).im * s) = Poly.eval (cpoly ν (n + 1)).1 (n + 1) s
      rw [eA, ih.1, ih.2, Shell.mul_one, Shell.mul_comm (Poly.eval (cpoly ν n).2 n s) s]
    · show ((⟨1, s⟩ : Ext p ν) ^ n).re * s + ((⟨1, s⟩ : Ext p ν) ^ n).im * 1 = Poly.eval (cpoly ν (n + 1)).2 (n + 1) s
      rw [eB, ih.1, ih.2, Shell.mul_one, Shell.add_comm, Shell.mul_comm s]

theorem ext_mul_pow (a b : Ext p ν) : ∀ n : Nat, (a * b) ^ n = a ^ n * b ^ n
  | 0 => (Ext.one_mul 1).symm
  | n + 1 => by
    show (a * b) ^ n * (a * b) = (a ^ n * a) * (b ^ n * b)
    rw [ext_mul_pow a b n]
    exact xsound (xlook [a ^ n, b ^ n, a, b]) (.mul (.mul (.var 0) (.var 1)) (.mul (.var 2) (.var 3))) (.mul (.mul (.var 0) (.var 2)) (.mul (.var 1) (.var 3))) (by decide +kernel)

theorem conj_pow (z : Ext p ν) : ∀ n : Nat, Ext.conj (z ^ n) = Ext.conj z ^ n
  | 0 => Ext.ext rfl Shell.neg_zero
  | n + 1 => by
    show Ext.conj (z ^ n * z) = Ext.conj z ^ n * Ext.conj z
    rw [Ext.conj_mul, conj_pow z n]

/-- 27:C15 — no `0 < d < p` is a period of the unitary cycle: some unitary point has `w^d ≠ 1`. -/
theorem unitary_escape (hp : FRC.Nat.isPrime p) (hν : ¬ ∃ y : Shell p, y * y = ν) (h2 : (1 : Shell p) + 1 ≠ 0)
    {d : Nat} (hd : 0 < d) (hlt : d < p) : ¬∀ w : Ext p ν, Ext.conj w * w = 1 → w ^ d = 1 := fun hall => by
  have hz : ∀ s : Shell p, Poly.eval (cpoly ν d).2 d s = 0 := fun s => by
    have ha := cay_conj_alg (ν := ν) (mul_pow_pred hp (cnorm_ne_zero hp hν s))
    have hwz : cay ν s * Ext.conj (⟨1, s⟩ : Ext p ν) = ⟨1, s⟩ := Ext.ext ha.1 ha.2
    have h1 : (cay ν s * Ext.conj (⟨1, s⟩ : Ext p ν)) ^ d = Ext.conj ((⟨1, s⟩ : Ext p ν) ^ d) := by
      rw [ext_mul_pow, hall _ (cay_unitary hp hν s), Ext.one_mul, conj_pow]
    rw [hwz] at h1
    have him : ((⟨1, s⟩ : Ext p ν) ^ d).im = -((⟨1, s⟩ : Ext p ν) ^ d).im := Ext.im_congr h1
    rw [← (cpoly_pow ν s d).2]
    have hb : (1 + 1) * ((⟨1, s⟩ : Ext p ν) ^ d).im = 0 := by
      have e2 : ∀ b : Shell p, (1 + 1) * b = b + -(-b) := fun b =>
        Shell.Frame.RE.sound (Shell.Frame.look [b]) (.mul (.add .one .one) (.var 0)) (.add (.var 0) (.neg (.neg (.var 0)))) (by decide +kernel)
      rw [e2, ← him, Shell.add_neg]
    match Prime.mul_eq_zero hp hb with
    | .inl h => exact absurd h h2
    | .inr h => exact h
  have hroot := Poly.root_bound_of (fun h => Prime.mul_eq_zero hp h) d (cpoly ν d).2 (cpoly_bound ν d).2 (fun i => ofNat i)
    (fun i j hi hj e => Poly.Frame.ofNat_inj_lt (Nat.lt_of_le_of_lt hi hlt) (Nat.lt_of_le_of_lt hj hlt) e)
    (fun i _ => hz (ofNat i)) 1
  rw [(cpoly_coeff ν d).2, sum_const, Shell.mul_one] at hroot
  exact Prime.ofNat_ne_zero hd hlt hroot

/-- 27:C15 — no `0 < d < p + 1` is a period of the unitary cycle. At `d = p` the point `−1` has `(−1)^p = −1`. -/
theorem unitary_escape_top (hp : FRC.Nat.isPrime p) (hν : ¬ ∃ y : Shell p, y * y = ν) (h2 : (1 : Shell p) + 1 ≠ 0)
    {d : Nat} (hd : 0 < d) (hlt : d < p + 1) : ¬∀ w : Ext p ν, Ext.conj w * w = 1 → w ^ d = 1 :=
  match Nat.lt_or_ge d p with
  | .inl h => unitary_escape hp hν h2 hd h
  | .inr h => fun hall => by
    have ed : d = p := Nat.le_antisymm (Nat.le_of_lt_succ hlt) h
    have h1 := hall (-1) neg_one_unitary
    have h3 : (-1 : Ext p ν) ^ p * -1 = 1 := unitary_period hp hν h2 neg_one_unitary
    rw [ed] at h1
    rw [h1, Ext.one_mul] at h3
    have e : (-1 : Shell p) = 1 := Ext.re_congr h3
    exact h2 ((show (1 : Shell p) + 1 = 1 + -1 by rw [e]).trans (Shell.add_neg 1))

/-! ## The unitary cycle has a generator

The argument of `Theme/Drive.lean`, on the unitary points: the order of a unitary point divides every exponent that
kills it, a prime power `qᵉ ∣ p + 1` is an order, and orders `m` and `qᵉ` with `q ∤ m` multiply. -/

theorem ext_one_pow : ∀ n : Nat, (1 : Ext p ν) ^ n = 1
  | 0 => rfl
  | n + 1 => by
    show (1 : Ext p ν) ^ n * 1 = 1
    rw [ext_one_pow n]; exact Ext.one_mul 1

theorem ext_pow_mul (z : Ext p ν) (m : Nat) : ∀ n : Nat, z ^ (m * n) = (z ^ m) ^ n
  | 0 => rfl
  | n + 1 => by
    show z ^ (m * n + m) = (z ^ m) ^ n * z ^ m
    rw [Ext.pow_add, ext_pow_mul z m n]

theorem ext_pow_mul_comm (z : Ext p ν) (m n : Nat) : (z ^ m) ^ n = (z ^ n) ^ m := by
  rw [← ext_pow_mul, Nat.mul_comm, ext_pow_mul]

theorem ext_pow_one (z : Ext p ν) : z ^ 1 = z := Ext.one_mul z

/-- A power of a unitary point is a unitary point. -/
theorem unitary_pow {w : Ext p ν} (hw : Ext.conj w * w = 1) : ∀ k : Nat, Ext.conj (w ^ k) * w ^ k = 1
  | 0 => one_unitary
  | k + 1 => unitary_mul (unitary_pow hw k) hw

/-- `x` has order `n`: `0 < n`, `xⁿ = 1`, and no positive power below `n` is `1`. -/
def UOrder (x : Ext p ν) (n : Nat) : Prop := 0 < n ∧ x ^ n = 1 ∧ ∀ l, l < n → 0 < l → x ^ l ≠ 1

/-- Every unitary point has an order, the least positive exponent with `xⁿ = 1`; the period `p + 1` bounds it. -/
theorem uorder_exists (hp : FRC.Nat.isPrime p) (hν : ¬ ∃ y : Shell p, y * y = ν) (h2 : (1 : Shell p) + 1 ≠ 0)
    {x : Ext p ν} (hx : Ext.conj x * x = 1) : ∃ n, UOrder x n := by
  obtain ⟨n, _, ⟨hn0, hxn⟩, hmin⟩ := FRC.Nat.exists_least (fun l => 0 < l ∧ x ^ l = 1) (p + 2)
    ⟨p + 1, Nat.lt_succ_self _, Nat.zero_lt_succ p, unitary_period hp hν h2 hx⟩
  exact ⟨n, hn0, hxn, fun l hl hl0 hxl => hmin l hl ⟨hl0, hxl⟩⟩

theorem uorder_pow_of_dvd {x : Ext p ν} {n k : Nat} (h : UOrder x n) : n ∣ k → x ^ k = 1
  | ⟨c, hc⟩ => by rw [hc, ext_pow_mul, h.2.1, ext_one_pow]

theorem uorder_dvd {x : Ext p ν} {n k : Nat} (h : UOrder x n) (hk : x ^ k = 1) : n ∣ k := by
  obtain ⟨c, hc⟩ := FRC.Nat.mod_spec n h.1 k
  rw [hc, Ext.pow_add, ext_pow_mul, h.2.1, ext_one_pow, Ext.one_mul] at hk
  match Nat.decEq (k % n) 0 with
  | .isTrue h0 => exact ⟨c, by rw [h0, Nat.add_zero] at hc; exact hc⟩
  | .isFalse h0 => exact absurd hk (h.2.2 _ (Nat.mod_lt k h.1) (Nat.pos_of_ne_zero h0))

/-- A unitary `w` with `w^{qᵉ} = 1` and `w^m = 1`, `q` prime and `q ∤ m`, is `1`. -/
theorem uorder_one_of_pows (hp : FRC.Nat.isPrime p) (hν : ¬ ∃ y : Shell p, y * y = ν) (h2 : (1 : Shell p) + 1 ≠ 0)
    {q e m : Nat} (hq : FRC.Nat.isPrime q) {w : Ext p ν} (hw : Ext.conj w * w = 1)
    (he : w ^ (q ^ e) = 1) (hm : w ^ m = 1) (hmq : m % q ≠ 0) : w = 1 := by
  obtain ⟨n, hn⟩ := uorder_exists hp hν h2 hw
  obtain ⟨j, _, hj⟩ := FRC.Nat.dvd_prime_pow hq e n (uorder_dvd hn he)
  have hnm := uorder_dvd hn hm
  match j, hj with
  | 0, hj => rw [hj, Nat.pow_zero] at hn; have := hn.2.1; rwa [ext_pow_one] at this
  | j + 1, hj =>
    have hq0 : 0 < q := Nat.lt_of_lt_of_le (Nat.zero_lt_succ 1) hq.1
    have hqn : q ∣ n := ⟨q ^ j, by rw [hj, Nat.pow_succ, Nat.mul_comm]⟩
    exact absurd ((FRC.Nat.dvd_iff_mod hq0).1 (FRC.Nat.dvd_trans' hqn hnm)) hmq

/-- Orders `m` and `qᵉ` with `q ∤ m` multiply: `y z` has order `m qᵉ`. -/
theorem uorder_mul (hp : FRC.Nat.isPrime p) (hν : ¬ ∃ y : Shell p, y * y = ν) (h2 : (1 : Shell p) + 1 ≠ 0)
    {q e m : Nat} (hq : FRC.Nat.isPrime q) {y z : Ext p ν} (hy0 : Ext.conj y * y = 1) (hz0 : Ext.conj z * z = 1)
    (hy : UOrder y m) (hz : UOrder z (q ^ e)) (hmq : m % q ≠ 0) : UOrder (y * z) (m * q ^ e) := by
  refine ⟨Nat.mul_pos hy.1 hz.1, ?_, fun l hl hl0 hyz => ?_⟩
  · rw [ext_mul_pow, ext_pow_mul, hy.2.1, ext_one_pow, Ext.one_mul, Nat.mul_comm, ext_pow_mul, hz.2.1, ext_one_pow]
  · rw [ext_mul_pow] at hyz
    have hzl : z ^ l = 1 := by
      refine uorder_one_of_pows hp hν h2 hq (unitary_pow hz0 l) (by rw [ext_pow_mul_comm, hz.2.1, ext_one_pow]) ?_ hmq
      have h1 : (y ^ l * z ^ l) ^ m = 1 := by rw [hyz, ext_one_pow]
      rwa [ext_mul_pow, ext_pow_mul_comm, hy.2.1, ext_one_pow, Ext.one_mul] at h1
    have hyl : y ^ l = 1 := by rw [hzl, Ext.mul_one] at hyz; exact hyz
    obtain ⟨l', hl'⟩ := uorder_dvd hz hzl
    have hyl' : y ^ l' = 1 := by
      refine uorder_one_of_pows hp hν h2 (e := e) hq (unitary_pow hy0 l') ?_ (by rw [ext_pow_mul_comm, hy.2.1, ext_one_pow]) hmq
      rw [← ext_pow_mul, Nat.mul_comm, ← hl']; exact hyl
    obtain ⟨c, hc⟩ := uorder_dvd hy hyl'
    have hle : m * q ^ e ≤ l := FRC.Nat.le_of_dvd' hl0
      ⟨c, by rw [hl', hc, Nat.mul_comm m (q ^ e), FRC.Nat.mul_assoc]⟩
    exact absurd hl (Nat.not_lt_of_le hle)

/-- A unitary point that escapes the exponent `d`, found among the `p + 1` points. -/
theorem uescape_exists (hp : FRC.Nat.isPrime p) (hν : ¬ ∃ y : Shell p, y * y = ν) (h2 : (1 : Shell p) + 1 ≠ 0)
    {d : Nat} (hd : 0 < d) (hlt : d < p + 1) : ∃ a : Ext p ν, Ext.conj a * a = 1 ∧ a ^ d ≠ 1 :=
  match decExistsLT (fun j => (upt ν j) ^ d ≠ 1) (p + 1) with
  | .isTrue ⟨j, _, h⟩ => ⟨upt ν j, upt_unitary hp hν j, h⟩
  | .isFalse hno => (unitary_escape_top hp hν h2 hd hlt (fun w hw => by
      have hu := upt_uidx hp hν hw
      match decEq ((upt ν (uidx w)) ^ d) 1 with
      | .isTrue e => rw [hu.1] at e; exact e
      | .isFalse ne => exact absurd ⟨uidx w, hu.2, ne⟩ hno)).elim

/-- A prime power `qᵉ ∣ p + 1`, `e ≥ 1`, is an order: with `p + 1 = qᵉ t` and `a^{(p+1)/q} ≠ 1`, `aᵗ` has order `qᵉ`. -/
theorem uorder_prime_pow (hp : FRC.Nat.isPrime p) (hν : ¬ ∃ y : Shell p, y * y = ν) (h2 : (1 : Shell p) + 1 ≠ 0)
    {q e : Nat} (hq : FRC.Nat.isPrime q) (he : 0 < e) (hdvd : q ^ e ∣ p + 1) :
    ∃ z : Ext p ν, Ext.conj z * z = 1 ∧ UOrder z (q ^ e) := by
  obtain ⟨t, ht⟩ := hdvd
  match e, he with
  | e + 1, _ =>
    have hq2 : 2 ≤ q := hq.1
    have hpd : p + 1 = q * (q ^ e * t) := by rw [ht, Nat.pow_succ, Nat.mul_comm (q ^ e) q, FRC.Nat.mul_assoc]
    have hd0 : 0 < q ^ e * t := Nat.pos_of_ne_zero (fun h => by
      rw [h, Nat.mul_zero] at hpd; exact Nat.succ_ne_zero p hpd)
    have hdlt : q ^ e * t < p + 1 := by
      rw [hpd]
      calc q ^ e * t = 1 * (q ^ e * t) := (Nat.one_mul _).symm
        _ < q * (q ^ e * t) := FRC.Nat.mul_lt_mul_of_lt_of_pos (Nat.lt_of_lt_of_le (Nat.lt_succ_self 1) hq2) hd0
    obtain ⟨a, ha0, had⟩ := uescape_exists hp hν h2 hd0 hdlt
    have hz0 := unitary_pow ha0 t
    have hzq : (a ^ t) ^ (q ^ (e + 1)) = 1 := by
      rw [← ext_pow_mul, Nat.mul_comm, ← ht, unitary_period hp hν h2 ha0]
    obtain ⟨n, hn⟩ := uorder_exists hp hν h2 hz0
    obtain ⟨j, hj, hjn⟩ := FRC.Nat.dvd_prime_pow hq (e + 1) n (uorder_dvd hn hzq)
    match Nat.lt_or_ge j (e + 1) with
    | .inl hlt =>
      have hje : q ^ j ∣ q ^ e := ⟨q ^ (e - j), by rw [← FRC.Nat.pow_add, FRC.Nat.add_sub_of_le (Nat.le_of_lt_succ hlt)]⟩
      have h1 : (a ^ t) ^ (q ^ e) = 1 := uorder_pow_of_dvd hn (by rw [hjn]; exact hje)
      rw [← ext_pow_mul, Nat.mul_comm] at h1
      exact absurd h1 had
    | .inr hge =>
      have : j = e + 1 := Nat.le_antisymm hj hge
      rw [this] at hjn
      exact ⟨a ^ t, hz0, hjn ▸ hn⟩

/-- Every divisor `n` of `p + 1` is an order of a unitary point. -/
theorem uorder_of_dvd (hp : FRC.Nat.isPrime p) (hν : ¬ ∃ y : Shell p, y * y = ν) (h2 : (1 : Shell p) + 1 ≠ 0) :
    ∀ B n, n ≤ B → 0 < n → n ∣ p + 1 → ∃ y : Ext p ν, Ext.conj y * y = 1 ∧ UOrder y n
  | 0, n, hB, hn, _ => absurd (Nat.lt_of_lt_of_le hn hB) (Nat.lt_irrefl 0)
  | B + 1, n, hB, hn, hdvd => by
    match n, hn with
    | 1, _ => exact ⟨1, one_unitary, Nat.zero_lt_succ 0, ext_one_pow 1,
        fun l hl hl0 => absurd (Nat.lt_of_lt_of_le hl0 (Nat.le_of_lt_succ hl)) (Nat.lt_irrefl 0)⟩
    | k + 2, _ =>
      obtain ⟨q, hq, hqn⟩ := FRC.Nat.exists_prime_dvd (Nat.le_add_left 2 k)
      have hq2 : 2 ≤ q := hq.1
      have hq0 : 0 < q := Nat.lt_of_lt_of_le (Nat.zero_lt_succ 1) hq2
      obtain ⟨e, m, hem, hmq⟩ := FRC.Nat.exists_pow_mul hq2 (k + 2) (k + 2) (Nat.le_refl _) (Nat.zero_lt_succ _)
      have hm0 : 0 < m := Nat.pos_of_ne_zero (fun h => by rw [h, Nat.mul_zero] at hem; exact Nat.noConfusion hem)
      have he0 : 0 < e := by
        match e, hem with
        | 0, hem =>
          rw [Nat.pow_zero, Nat.one_mul] at hem
          rw [hem] at hqn
          exact absurd ((FRC.Nat.dvd_iff_mod hq0).1 hqn) hmq
        | e + 1, _ => exact Nat.zero_lt_succ e
      have hqe : 2 ≤ q ^ e := by
        match e, he0 with
        | e + 1, _ =>
          rw [Nat.pow_succ]
          calc 2 ≤ q := hq2
            _ = 1 * q := (Nat.one_mul q).symm
            _ ≤ q ^ e * q := Nat.mul_le_mul_right q (Nat.pos_pow_of_pos e hq0)
      have hmn : m < k + 2 := by
        rw [hem]
        calc m = 1 * m := (Nat.one_mul m).symm
          _ < q ^ e * m := FRC.Nat.mul_lt_mul_of_lt_of_pos (Nat.lt_of_lt_of_le (Nat.lt_succ_self 1) hqe) hm0
      obtain ⟨y, hy0, hy⟩ := uorder_of_dvd hp hν h2 B m (Nat.le_of_lt_succ (Nat.lt_of_lt_of_le hmn hB)) hm0
        (FRC.Nat.dvd_trans' ⟨q ^ e, by rw [hem, Nat.mul_comm]⟩ hdvd)
      obtain ⟨z, hz0, hz⟩ := uorder_prime_pow hp hν h2 hq he0 (FRC.Nat.dvd_trans' ⟨m, hem⟩ hdvd)
      have h := uorder_mul hp hν h2 hq hy0 hz0 hy hz hmq
      rw [Nat.mul_comm, ← hem] at h
      exact ⟨y * z, unitary_mul hy0 hz0, h⟩

/-- 27:C15 — the unitary cycle has a generator: a unitary point with `w^(p+1) = 1` and no positive power below `p + 1`
equal to `1`. -/
theorem unitary_generator (hp : FRC.Nat.isPrime p) (hν : ¬ ∃ y : Shell p, y * y = ν) (h2 : (1 : Shell p) + 1 ≠ 0) :
    ∃ w : Ext p ν, Ext.conj w * w = 1 ∧ w ^ (p + 1) = 1 ∧ ∀ l, l < p + 1 → 0 < l → w ^ l ≠ 1 := by
  obtain ⟨w, hw0, hw⟩ := uorder_of_dvd hp hν h2 (p + 1) (p + 1) (Nat.le_refl _) (Nat.zero_lt_succ p)
    ⟨1, (Nat.mul_one _).symm⟩
  exact ⟨w, hw0, hw.2.1, hw.2.2⟩

/-! ## The orders of the two cycles -/

/-- 27:C15 — the orders of the two cycles of the diagonal torus, on a prime shell with `ν` a nonsquare and `2 ≠ 0`.
The split cycle: the nonzero residues are those of `1, …, p − 1`, each has `a^(p−1) = 1`, no `0 < m < p − 1` is a
period of all of them, and one of them has order `p − 1`. The unitary cycle: its points are `−1` and the Cayley points of the `p` residues, pairwise
distinct, each has `w^(p+1) = 1`, no `0 < d < p + 1` is a period of all of them, and one of them has order `p + 1`. -/
theorem cycle_orders (hp : FRC.Nat.isPrime p) (hν : ¬ ∃ y : Shell p, y * y = ν) (h2 : (1 : Shell p) + 1 ≠ 0) :
    ((∀ a : Shell p, a ≠ 0 ↔ 0 < a.val) ∧ (∀ a : Shell p, a.val < p) ∧
      (∀ a b : Shell p, a.val = b.val → a = b) ∧ (∀ k : Nat, k < p → ¬∀ a : Shell p, a.val ≠ k)) ∧
    (∀ a : Shell p, a ≠ 0 → a ^ (p - 1) = 1) ∧
    (∀ m : Nat, 0 < m → m < p - 1 → ¬∀ a : Shell p, a ≠ 0 → a ^ m = 1) ∧
    (¬∀ a : Shell p, a ≠ 0 → ¬∀ l : Nat, l < p - 1 → 0 < l → a ^ l ≠ 1) ∧
    (∀ s : Shell p, Ext.conj (cay ν s) * cay ν s = 1 ∧ (cay ν s).re + 1 ≠ 0) ∧
    (∀ s s' : Shell p, cay ν s = cay ν s' → s = s') ∧
    (∀ w : Ext p ν, Ext.conj w * w = 1 → w.re + 1 ≠ 0 → cay ν (w.im * (w.re + 1) ^ (p - 2)) = w) ∧
    (∀ w : Ext p ν, Ext.conj w * w = 1 → w.re + 1 = 0 → w = -1) ∧
    (∀ w : Ext p ν, Ext.conj w * w = 1 → w ^ (p + 1) = 1) ∧
    (∀ d : Nat, 0 < d → d < p + 1 → ¬∀ w : Ext p ν, Ext.conj w * w = 1 → w ^ d = 1) ∧
    (¬∀ w : Ext p ν, Ext.conj w * w = 1 → ¬∀ l : Nat, l < p + 1 → 0 < l → w ^ l ≠ 1) :=
  ⟨FRC.Interactions.nonzero_residues, fun _ ha => Prime.fermat hp ha,
   fun _ hm hlt h => match Prime.exists_pow_ne_one hp hm hlt with | ⟨a, ha, hne⟩ => hne (h a ha),
   fun h => match Prime.exists_primitive hp with | ⟨g, hg, _, hl⟩ => h g hg hl,
   fun s => ⟨cay_unitary hp hν s, (cay_recover hp hν h2 s).1⟩, fun _ _ h => cay_inj hp hν h2 h,
   fun _ hw h1 => cay_surj hp hν hw h1, fun _ hw h1 => cay_exc hp hν hw h1, fun _ hw => unitary_period hp hν h2 hw,
   fun _ hd hlt => unitary_escape_top hp hν h2 hd hlt,
   fun h => match unitary_generator hp hν h2 with | ⟨w, hw, _, hl⟩ => h w hw hl⟩

end FRC.Unitary
