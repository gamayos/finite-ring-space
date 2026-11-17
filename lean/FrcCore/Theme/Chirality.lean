import FrcCore.Theme.Quadratic
import FrcCore.Theme.OpRing

/-!
# FrcCore.Theme.Chirality — chirality as the root of the drive, and the two branches along the drive (27-fields, 16 November 2026)

The exact content of 27-fields' rows C13 and C14, on every shell.

* **Chirality is the root of the drive (27:C13).** In an operator ring, four pairwise anticommuting elements have
  `(γ⁰γ¹γ²γ³)² ≈ (γ⁰)²(γ¹)²(γ²)²(γ³)²` (`chirality_square`): no sign is left over. With the Clifford relations of
  `diag(−ν, 1, 1, 1)` the product `Γ` has `Γ² ≈ −ν` (`chirality_clifford`), and for a central `u` with `u² ≈ −1` the
  element `uΓ` has `(uΓ)² ≈ ν` (`chirality_root`). On a shell with `i² = −1` and `ν` a nonsquare, `−ν` is a nonsquare
  (`neg_nonsquare`), so `Γ` has no eigenvalue on the shell. In the extension `(i w)² = −ν` (`root_sq`), and the
  Frobenius conjugation sends `i w` to `−i w` (`root_conj`): the two eigenvalues, exchanged.
* **The two branches along the drive (27:C14).** The extension is graded by the Frobenius: it fixes the shell's part
  (`conj_shell`) and negates the multiples of `w` (`conj_root`). The grading is multiplicative (`shell_mul_shell`,
  `root_mul_shell`, `shell_mul_root`, `root_mul_root`) and additive (`shell_add_shell`, `root_add_root`). A matrix over
  the shell is therefore fixed, and its product with the drive's lift `diag(w, w/ν)` is negated, entry by entry
  (`drive_lift_frobenius`), while the lift's square is over the shell (`drive_lift_square`). The sign cancels in a
  sesquilinear tally (`tally_sign`).
* **The mass form of the doublet (27:C5, 27:X5).** With the Frobenius as the conjugation, the pairings of the four vectors
  that the generators make of the unit vacuum lie on the shell (`mass_form`), and so does the invariant form
  (`invariant_form`). Against that form the charged pair has one value, `(a′, a)` is the kernel and `(a, −a′)` has the value
  `a² + a′²` (`mass_spectrum`). The two neutral eigenvectors are independent where `a² + a′² ≠ 0` (`mass_independent`),
  and the neutral block has the square `(a² + a′²)` times itself (`mass_block_square`).
* **The idempotents of `𝔽_p[Γ]` (27:C13, 27:X6).** An idempotent `a + bΓ` with `b` invertible makes `ν` a square
  (`idempotent_square`), so a shell where `ν` is no square holds none (`no_idempotent`).
-/

namespace FRC.Chirality

open FRC FRC.Shell FRC.Extension FRC.Dirac.Operator
open OpRing (add_congr mul_congr neg_congr add_comm add_assoc zero_add add_neg mul_assoc one_mul mul_one left_distrib right_distrib)

section clifford
variable {R : Type} [Add R] [Mul R] [Neg R] [OfNat R 0] [OfNat R 1] [OpRing R]

/-- `B A ≈ −(A B)` for anticommuting `A`, `B`. -/
theorem anti_swap {A B : R} (h : Anticomm A B) : B * A ≈ -(A * B) :=
  eq_symm (neg_eq_of_add_eq_zero h)

/-- A product of two elements that anticommute with `x` commutes with `x`. -/
theorem anti_mul2 {a b x : R} (ha : Anticomm a x) (hb : Anticomm b x) : Comm (a * b) x :=
  calc (a * b) * x ≈ a * (b * x) := mul_assoc a b x
    _ ≈ a * -(x * b) := mul_congr_right a (anti_swap (Anticomm.symm hb))
    _ ≈ -(a * (x * b)) := eq_symm (mul_neg a (x * b))
    _ ≈ -((a * x) * b) := neg_congr (eq_symm (mul_assoc a x b))
    _ ≈ -(-(x * a) * b) := neg_congr (mul_congr_left b (anti_swap (Anticomm.symm ha)))
    _ ≈ -(-((x * a) * b)) := neg_congr (eq_symm (neg_mul (x * a) b))
    _ ≈ (x * a) * b := neg_neg _
    _ ≈ x * (a * b) := mul_assoc x a b

/-- `(A B)² ≈ A² B²` for commuting `A`, `B`. -/
theorem sq_mul_of_comm {A B : R} (h : Comm A B) : (A * B) * (A * B) ≈ (A * A) * (B * B) :=
  calc (A * B) * (A * B) ≈ A * (B * (A * B)) := mul_assoc A B (A * B)
    _ ≈ A * ((B * A) * B) := mul_congr_right A (eq_symm (mul_assoc B A B))
    _ ≈ A * ((A * B) * B) := mul_congr_right A (mul_congr_left B (Comm.symm h))
    _ ≈ A * (A * (B * B)) := mul_congr_right A (mul_assoc A B B)
    _ ≈ (A * A) * (B * B) := eq_symm (mul_assoc A A (B * B))

/-- `(a b)² ≈ −(a² b²)` for anticommuting `a`, `b`. -/
theorem sq_mul_of_anticomm {a b : R} (h : Anticomm a b) : (a * b) * (a * b) ≈ -((a * a) * (b * b)) :=
  calc (a * b) * (a * b) ≈ a * (b * (a * b)) := mul_assoc a b (a * b)
    _ ≈ a * ((b * a) * b) := mul_congr_right a (eq_symm (mul_assoc b a b))
    _ ≈ a * (-(a * b) * b) := mul_congr_right a (mul_congr_left b (anti_swap h))
    _ ≈ a * -((a * b) * b) := mul_congr_right a (eq_symm (neg_mul (a * b) b))
    _ ≈ -(a * ((a * b) * b)) := eq_symm (mul_neg a ((a * b) * b))
    _ ≈ -(a * (a * (b * b))) := neg_congr (mul_congr_right a (mul_assoc a b b))
    _ ≈ -((a * a) * (b * b)) := neg_congr (eq_symm (mul_assoc a a (b * b)))

/-- 27:C13 — the square of the product of four pairwise anticommuting elements is the product of their squares, with
no sign left over. -/
theorem chirality_square {g0 g1 g2 g3 : R} (h01 : Anticomm g0 g1) (h02 : Anticomm g0 g2) (h03 : Anticomm g0 g3)
    (h12 : Anticomm g1 g2) (h13 : Anticomm g1 g3) (h23 : Anticomm g2 g3) :
    (g0 * g1 * g2 * g3) * (g0 * g1 * g2 * g3) ≈ ((g0 * g0) * (g1 * g1)) * ((g2 * g2) * (g3 * g3)) :=
  have hc : Comm (g0 * g1) (g2 * g3) := Comm.mul_right (anti_mul2 h02 h12) (anti_mul2 h03 h13)
  have hG : g0 * g1 * g2 * g3 ≈ (g0 * g1) * (g2 * g3) := mul_assoc (g0 * g1) g2 g3
  calc (g0 * g1 * g2 * g3) * (g0 * g1 * g2 * g3) ≈ ((g0 * g1) * (g2 * g3)) * ((g0 * g1) * (g2 * g3)) := mul_congr hG hG
    _ ≈ ((g0 * g1) * (g0 * g1)) * ((g2 * g3) * (g2 * g3)) := sq_mul_of_comm hc
    _ ≈ -((g0 * g0) * (g1 * g1)) * -((g2 * g2) * (g3 * g3)) := mul_congr (sq_mul_of_anticomm h01) (sq_mul_of_anticomm h23)
    _ ≈ ((g0 * g0) * (g1 * g1)) * ((g2 * g2) * (g3 * g3)) := neg_mul_neg _ _

/-- 27:C13 — with the Clifford relations of `diag(−c, 1, 1, 1)`, the product `Γ = γ⁰γ¹γ²γ³` has `Γ² ≈ −c`. -/
theorem chirality_clifford {g0 g1 g2 g3 c : R} (h01 : Anticomm g0 g1) (h02 : Anticomm g0 g2) (h03 : Anticomm g0 g3)
    (h12 : Anticomm g1 g2) (h13 : Anticomm g1 g3) (h23 : Anticomm g2 g3)
    (h0 : g0 * g0 ≈ -c) (h1 : g1 * g1 ≈ 1) (h2 : g2 * g2 ≈ 1) (h3 : g3 * g3 ≈ 1) :
    (g0 * g1 * g2 * g3) * (g0 * g1 * g2 * g3) ≈ -c :=
  calc (g0 * g1 * g2 * g3) * (g0 * g1 * g2 * g3) ≈ ((g0 * g0) * (g1 * g1)) * ((g2 * g2) * (g3 * g3)) :=
        chirality_square h01 h02 h03 h12 h13 h23
    _ ≈ (-c * 1) * (1 * 1) := mul_congr (mul_congr h0 h1) (mul_congr h2 h3)
    _ ≈ -c * 1 := mul_congr (mul_one (-c)) (mul_one 1)
    _ ≈ -c := mul_one (-c)

/-- 27:C13 — for a central `u` with `u² ≈ −1` and `Γ² ≈ −c`, the element `uΓ` is a square root of `c`. -/
theorem chirality_root {u G c : R} (hu : Central u) (huu : u * u ≈ -1) (hG : G * G ≈ -c) : (u * G) * (u * G) ≈ c :=
  calc (u * G) * (u * G) ≈ (u * u) * (G * G) := sq_mul_of_comm (hu G)
    _ ≈ -1 * -c := mul_congr huu hG
    _ ≈ 1 * c := neg_mul_neg 1 c
    _ ≈ c := one_mul c

end clifford

section shell
variable {p : Nat} [Pos p]

/-- 27:C13, 27:X6 — on a shell with `i² = −1`, if `ν` is a nonsquare then `−ν` is a nonsquare: `x² + ν` has no root, so an
element with square `−ν` has no eigenvalue on the shell. -/
theorem neg_nonsquare {i ν : Shell p} (hi : i * i = -1) (hν : ¬ ∃ r : Shell p, r * r = ν) : ¬ ∃ r : Shell p, r * r = -ν :=
  fun ⟨r, hr⟩ => hν ⟨i * r, by rw [Shell.mul_mul_mul_comm, hi, hr, Shell.neg_mul_neg, Shell.one_mul]⟩

variable {ν : Shell p}

/-- The shell's part of the extension: `a ↦ a + 0 w`. -/
def shellPart (ν : Shell p) (a : Shell p) : Ext p ν := ⟨a, 0⟩
/-- The multiples of `w`: `b ↦ 0 + b w`. -/
def rootPart (ν : Shell p) (b : Shell p) : Ext p ν := ⟨0, b⟩

/-- 27:C13 — `(i w)² = −ν` in the extension: `i w` and `−i w` are the roots of `x² + ν`. -/
theorem root_sq {i : Shell p} (hi : i * i = -1) : rootPart ν i * rootPart ν i = shellPart ν (-ν) := by
  show (⟨0 * 0 + ν * (i * i), 0 * i + i * 0⟩ : Ext p ν) = ⟨-ν, 0⟩
  rw [hi, Shell.zero_mul, Shell.zero_add, Shell.zero_mul, Shell.mul_zero, Shell.add_zero, ← Shell.mul_neg, Shell.mul_one]

/-- 27:C13, 27:C14 — the Frobenius conjugation negates a multiple of `w`: it exchanges `i w` and `−i w`. -/
theorem conj_root (b : Shell p) : Ext.conj (rootPart ν b) = -rootPart ν b := by
  show (⟨0, -b⟩ : Ext p ν) = ⟨-0, -b⟩
  rw [Shell.neg_zero]

/-- 27:C13, 27:X6 — the Frobenius conjugation exchanges the two roots `i w` and `−i w`. -/
theorem root_conj (i : Shell p) : Ext.conj (rootPart ν i) = -rootPart ν i := conj_root i

/-- 27:C14 — the Frobenius conjugation fixes the shell's part of the extension. -/
theorem conj_shell (a : Shell p) : Ext.conj (shellPart ν a) = shellPart ν a := by
  show (⟨a, -0⟩ : Ext p ν) = ⟨a, 0⟩
  rw [Shell.neg_zero]

/-- 27:C14 — the grading is multiplicative: shell times shell is on the shell. -/
theorem shell_mul_shell (a c : Shell p) : shellPart ν a * shellPart ν c = shellPart ν (a * c) := by
  show (⟨a * c + ν * (0 * 0), a * 0 + 0 * c⟩ : Ext p ν) = ⟨a * c, 0⟩
  rw [Shell.mul_zero a, Shell.zero_mul c, Shell.zero_mul, Shell.mul_zero ν, Shell.add_zero, Shell.add_zero]

/-- 27:C14 — a multiple of `w` times a shell element is a multiple of `w`. -/
theorem root_mul_shell (b c : Shell p) : rootPart ν b * shellPart ν c = rootPart ν (b * c) := by
  show (⟨0 * c + ν * (b * 0), 0 * 0 + b * c⟩ : Ext p ν) = ⟨0, b * c⟩
  rw [Shell.zero_mul c, Shell.mul_zero b, Shell.mul_zero ν, Shell.add_zero, Shell.zero_mul, Shell.zero_add]

/-- 27:C14 — a shell element times a multiple of `w` is a multiple of `w`. -/
theorem shell_mul_root (a d : Shell p) : shellPart ν a * rootPart ν d = rootPart ν (a * d) := by
  show (⟨a * 0 + ν * (0 * d), a * d + 0 * 0⟩ : Ext p ν) = ⟨0, a * d⟩
  rw [Shell.mul_zero a, Shell.zero_mul d, Shell.mul_zero ν, Shell.add_zero, Shell.zero_mul, Shell.add_zero]

/-- 27:C14 — two multiples of `w` multiply to a shell element. -/
theorem root_mul_root (b d : Shell p) : rootPart ν b * rootPart ν d = shellPart ν (ν * (b * d)) := by
  show (⟨0 * 0 + ν * (b * d), 0 * d + b * 0⟩ : Ext p ν) = ⟨ν * (b * d), 0⟩
  rw [Shell.zero_mul, Shell.zero_add, Shell.zero_mul, Shell.mul_zero, Shell.add_zero]

/-- 27:C14 — the grading is additive on the shell's part. -/
theorem shell_add_shell (a c : Shell p) : shellPart ν a + shellPart ν c = shellPart ν (a + c) := by
  show (⟨a + c, 0 + 0⟩ : Ext p ν) = ⟨a + c, 0⟩
  rw [Shell.add_zero]

/-- 27:C14 — the grading is additive on the multiples of `w`. -/
theorem root_add_root (b d : Shell p) : rootPart ν b + rootPart ν d = rootPart ν (b + d) := by
  show (⟨0 + 0, b + d⟩ : Ext p ν) = ⟨0, b + d⟩
  rw [Shell.add_zero]

/-- 27:C14 — an entry of the drive's lift times a shell element is negated by the Frobenius conjugation: on the coset
of the lift, `σ(A) = −A` entry by entry. -/
theorem drive_lift_frobenius (d a : Shell p) :
    Ext.conj (rootPart ν d * shellPart ν a) = -(rootPart ν d * shellPart ν a) := by
  rw [root_mul_shell, conj_root]

/-- 27:C14 — the square of the lift's entry `w` is the shell element `ν`: the lift's square is over the shell. -/
theorem drive_lift_square : rootPart ν 1 * rootPart ν 1 = shellPart ν ν := by
  rw [root_mul_root, Shell.mul_one, Shell.mul_one]

/-- 27:C14 — the sign cancels in a sesquilinear tally: `σ(−x)(−y) = σ(x) y`. -/
theorem tally_sign (x y : Ext p ν) : Ext.conj (-x) * (-y) = Ext.conj x * y := by
  apply Ext.ext
  · show -x.re * -y.re + ν * (- -x.im * -y.im) = x.re * y.re + ν * (-x.im * y.im)
    rw [Shell.neg_mul_neg, Shell.neg_mul_neg]
  · show -x.re * -y.im + - -x.im * -y.re = x.re * y.im + -x.im * y.re
    rw [Shell.neg_mul_neg, Shell.neg_mul_neg]

/-! ## The mass form of the doublet on the extension (27:C5), and the idempotents of `𝔽_p[Γ]` (27:C13) -/

/-- `−(b w) = (−b) w`. -/
theorem neg_root (b : Shell p) : -rootPart ν b = rootPart ν (-b) := by
  show (⟨-0, -b⟩ : Ext p ν) = ⟨0, -b⟩
  rw [Shell.neg_zero]

/-- 27:C5 — the Frobenius-Hermitian pairing of two multiples of `w` lies on the shell: `σ(b w) (d w) = −ν b d`. -/
theorem herm_root_root (b d : Shell p) : Ext.conj (rootPart ν b) * rootPart ν d = shellPart ν (-(ν * (b * d))) := by
  rw [conj_root, neg_root, root_mul_root, ← Shell.neg_mul, ← Shell.mul_neg]

/-- 27:C5 — a shell entry paired with a multiple of `w` is a multiple of `w`: `σ(a) (d w) = (a d) w`. -/
theorem herm_shell_root (a d : Shell p) : Ext.conj (shellPart ν a) * rootPart ν d = rootPart ν (a * d) := by
  rw [conj_shell, shell_mul_root]

/-- 27:C5 — `σ(b w) c = −(b c) w`. -/
theorem herm_root_shell (b c : Shell p) : Ext.conj (rootPart ν b) * shellPart ν c = rootPart ν (-(b * c)) := by
  rw [conj_root, neg_root, root_mul_shell, ← Shell.neg_mul]

/-- 27:C5, 27:X5 — the mass form of the doublet in the basis of the four generators. With `w² = ν`, the unit vacuum `(0, 1)`
and `a = g / 2`, `a′ = g′ / 2`, the generators send the vacuum to `(a, 0)`, `(a w, 0)`, `(0, −a w)` and `(0, a′ w)`. Their
Frobenius-Hermitian pairings lie on the shell: `a²` and `−ν a²` for the charged pair, whose mixed pairing cancels; `−ν a²`,
`−ν a′²` and the mixed sum `2 ν a a′` for the neutral pair. -/
theorem mass_form (a a' : Shell p) :
    Ext.conj (shellPart ν a) * shellPart ν a = shellPart ν (a * a) ∧
    Ext.conj (rootPart ν a) * rootPart ν a = shellPart ν (-(ν * (a * a))) ∧
    Ext.conj (shellPart ν a) * rootPart ν a + Ext.conj (rootPart ν a) * shellPart ν a = rootPart ν 0 ∧
    Ext.conj (rootPart ν (-a)) * rootPart ν (-a) = shellPart ν (-(ν * (a * a))) ∧
    Ext.conj (rootPart ν a') * rootPart ν a' = shellPart ν (-(ν * (a' * a'))) ∧
    Ext.conj (rootPart ν (-a)) * rootPart ν a' + Ext.conj (rootPart ν a') * rootPart ν (-a) =
      shellPart ν ((ν * (a * a')) + (ν * (a * a'))) := by
  have e : (-(ν * (-a * a')) + -(ν * (a' * -a))) = ((ν * (a * a')) + (ν * (a * a'))) :=
    Shell.Frame.RE.sound (Shell.Frame.look [ν, a, a']) (.add (.neg (.mul (.var 0) (.mul (.neg (.var 1)) (.var 2)))) (.neg (.mul (.var 0) (.mul (.var 2) (.neg (.var 1)))))) (.add (.mul (.var 0) (.mul (.var 1) (.var 2))) (.mul (.var 0) (.mul (.var 1) (.var 2)))) (by decide +kernel)
  refine ⟨?_, herm_root_root a a, ?_, ?_, herm_root_root a' a', ?_⟩
  · rw [conj_shell, shell_mul_shell]
  · rw [herm_shell_root, herm_root_shell, root_add_root, Shell.add_neg]
  · rw [herm_root_root, Shell.neg_mul_neg]
  · rw [herm_root_root, herm_root_root, shell_add_shell, e]

/-- 27:C5, 27:X5 — the spectrum of the mass form against the invariant form `diag(1, −ν, −ν, −ν)`: the second charged
generator has the value `a²` of the first; `(a′, a)` is the kernel of the neutral block (the photon); and `(a, −a′)` has the
value `a² + a′²`. -/
theorem mass_spectrum (ν a a' : Shell p) :
    -(ν * (a * a)) = ((a * a) * -ν) ∧
    ((-(ν * (a * a)) * a') + ((ν * (a * a')) * a)) = 0 ∧
    (((ν * (a * a')) * a') + (-(ν * (a' * a')) * a)) = 0 ∧
    ((-(ν * (a * a)) * a) + ((ν * (a * a')) * -a')) = (((a * a) + (a' * a')) * (-ν * a)) ∧
    (((ν * (a * a')) * a) + (-(ν * (a' * a')) * -a')) = (((a * a) + (a' * a')) * (-ν * -a')) :=
  ⟨Shell.Frame.RE.sound (Shell.Frame.look [ν, a, a']) (.neg (.mul (.var 0) (.mul (.var 1) (.var 1)))) (.mul (.mul (.var 1) (.var 1)) (.neg (.var 0))) (by decide +kernel),
   Shell.Frame.RE.sound (Shell.Frame.look [ν, a, a']) (.add (.mul (.neg (.mul (.var 0) (.mul (.var 1) (.var 1)))) (.var 2)) (.mul (.mul (.var 0) (.mul (.var 1) (.var 2))) (.var 1))) .zero (by decide +kernel),
   Shell.Frame.RE.sound (Shell.Frame.look [ν, a, a']) (.add (.mul (.mul (.var 0) (.mul (.var 1) (.var 2))) (.var 2)) (.mul (.neg (.mul (.var 0) (.mul (.var 2) (.var 2)))) (.var 1))) .zero (by decide +kernel),
   Shell.Frame.RE.sound (Shell.Frame.look [ν, a, a']) (.add (.mul (.neg (.mul (.var 0) (.mul (.var 1) (.var 1)))) (.var 1)) (.mul (.mul (.var 0) (.mul (.var 1) (.var 2))) (.neg (.var 2)))) (.mul (.add (.mul (.var 1) (.var 1)) (.mul (.var 2) (.var 2))) (.mul (.neg (.var 0)) (.var 1))) (by decide +kernel),
   Shell.Frame.RE.sound (Shell.Frame.look [ν, a, a']) (.add (.mul (.mul (.var 0) (.mul (.var 1) (.var 2))) (.var 1)) (.mul (.neg (.mul (.var 0) (.mul (.var 2) (.var 2)))) (.neg (.var 2)))) (.mul (.add (.mul (.var 1) (.var 1)) (.mul (.var 2) (.var 2))) (.mul (.neg (.var 0)) (.neg (.var 2)))) (by decide +kernel)⟩

/-- 27:C5, 27:X5 — the two neutral eigenvectors `(a′, a)` and `(a, −a′)` are independent when `a² + a′² ≠ 0`: a combination
`x (a′, a) + y (a, −a′) = 0` has `(a² + a′²) x = 0` and `(a² + a′²) y = 0`. -/
theorem mass_independent {a a' x y : Shell p} (h1 : x * a' + y * a = 0) (h2 : x * a + y * -a' = 0) :
    (a * a + a' * a') * x = 0 ∧ (a * a + a' * a') * y = 0 := by
  have e1 : (((a * a) + (a' * a')) * x) = ((((x * a') + (y * a)) * a') + (((x * a) + (y * -a')) * a)) :=
    Shell.Frame.RE.sound (Shell.Frame.look [a, a', x, y]) (.mul (.add (.mul (.var 0) (.var 0)) (.mul (.var 1) (.var 1))) (.var 2)) (.add (.mul (.add (.mul (.var 2) (.var 1)) (.mul (.var 3) (.var 0))) (.var 1)) (.mul (.add (.mul (.var 2) (.var 0)) (.mul (.var 3) (.neg (.var 1)))) (.var 0))) (by decide +kernel)
  have e2 : (((a * a) + (a' * a')) * y) = ((((x * a') + (y * a)) * a) + -(((x * a) + (y * -a')) * a')) :=
    Shell.Frame.RE.sound (Shell.Frame.look [a, a', x, y]) (.mul (.add (.mul (.var 0) (.var 0)) (.mul (.var 1) (.var 1))) (.var 3)) (.add (.mul (.add (.mul (.var 2) (.var 1)) (.mul (.var 3) (.var 0))) (.var 0)) (.neg (.mul (.add (.mul (.var 2) (.var 0)) (.mul (.var 3) (.neg (.var 1)))) (.var 1)))) (by decide +kernel)
  have z1 : (((0 : Shell p) * a') + (0 * a)) = 0 :=
    Shell.Frame.RE.sound (Shell.Frame.look [a, a']) (.add (.mul .zero (.var 1)) (.mul .zero (.var 0))) .zero (by decide +kernel)
  have z2 : (((0 : Shell p) * a) + -(0 * a')) = 0 :=
    Shell.Frame.RE.sound (Shell.Frame.look [a, a']) (.add (.mul .zero (.var 0)) (.neg (.mul .zero (.var 1)))) .zero (by decide +kernel)
  rw [h1, h2] at e1 e2
  exact ⟨e1.trans z1, e2.trans z2⟩

/-- 27:C5 — the neutral block `N = [[a², −a a′], [−a a′, a′²]]` has `N² = (a² + a′²) N`, entry by entry. Where
`a² + a′² = 0` it squares to zero: the excluded case of the mass form. -/
theorem mass_block_square (a a' : Shell p) :
    (((a * a) * (a * a)) + (-(a * a') * -(a * a'))) = (((a * a) + (a' * a')) * (a * a)) ∧
    (((a * a) * -(a * a')) + (-(a * a') * (a' * a'))) = (((a * a) + (a' * a')) * -(a * a')) ∧
    ((-(a * a') * (a * a)) + ((a' * a') * -(a * a'))) = (((a * a) + (a' * a')) * -(a * a')) ∧
    ((-(a * a') * -(a * a')) + ((a' * a') * (a' * a'))) = (((a * a) + (a' * a')) * (a' * a')) :=
  ⟨Shell.Frame.RE.sound (Shell.Frame.look [a, a']) (.add (.mul (.mul (.var 0) (.var 0)) (.mul (.var 0) (.var 0))) (.mul (.neg (.mul (.var 0) (.var 1))) (.neg (.mul (.var 0) (.var 1))))) (.mul (.add (.mul (.var 0) (.var 0)) (.mul (.var 1) (.var 1))) (.mul (.var 0) (.var 0))) (by decide +kernel),
   Shell.Frame.RE.sound (Shell.Frame.look [a, a']) (.add (.mul (.mul (.var 0) (.var 0)) (.neg (.mul (.var 0) (.var 1)))) (.mul (.neg (.mul (.var 0) (.var 1))) (.mul (.var 1) (.var 1)))) (.mul (.add (.mul (.var 0) (.var 0)) (.mul (.var 1) (.var 1))) (.neg (.mul (.var 0) (.var 1)))) (by decide +kernel),
   Shell.Frame.RE.sound (Shell.Frame.look [a, a']) (.add (.mul (.neg (.mul (.var 0) (.var 1))) (.mul (.var 0) (.var 0))) (.mul (.mul (.var 1) (.var 1)) (.neg (.mul (.var 0) (.var 1))))) (.mul (.add (.mul (.var 0) (.var 0)) (.mul (.var 1) (.var 1))) (.neg (.mul (.var 0) (.var 1)))) (by decide +kernel),
   Shell.Frame.RE.sound (Shell.Frame.look [a, a']) (.add (.mul (.neg (.mul (.var 0) (.var 1))) (.neg (.mul (.var 0) (.var 1)))) (.mul (.mul (.var 1) (.var 1)) (.mul (.var 1) (.var 1)))) (.mul (.add (.mul (.var 0) (.var 0)) (.mul (.var 1) (.var 1))) (.mul (.var 1) (.var 1))) (by decide +kernel)⟩

/-- 27:C5 — the invariant form `−2 tr(T²)` on the generators with `h = 1/2`: `4h² = 1` for the first, `−4 ν h² = −ν` for the
three that carry `w`. -/
theorem invariant_form {h : Shell p} (hh : h + h = 1) (ν : Shell p) :
    (((h * h) + (h * h)) + ((h * h) + (h * h))) = 1 ∧
    -(((ν * (h * h)) + (ν * (h * h))) + ((ν * (h * h)) + (ν * (h * h)))) = -ν := by
  have e1 : (((h * h) + (h * h)) + ((h * h) + (h * h))) = ((h + h) * (h + h)) :=
    Shell.Frame.RE.sound (Shell.Frame.look [h]) (.add (.add (.mul (.var 0) (.var 0)) (.mul (.var 0) (.var 0))) (.add (.mul (.var 0) (.var 0)) (.mul (.var 0) (.var 0)))) (.mul (.add (.var 0) (.var 0)) (.add (.var 0) (.var 0))) (by decide +kernel)
  have e2 : -(((ν * (h * h)) + (ν * (h * h))) + ((ν * (h * h)) + (ν * (h * h)))) = -(ν * ((h + h) * (h + h))) :=
    Shell.Frame.RE.sound (Shell.Frame.look [ν, h]) (.neg (.add (.add (.mul (.var 0) (.mul (.var 1) (.var 1))) (.mul (.var 0) (.mul (.var 1) (.var 1)))) (.add (.mul (.var 0) (.mul (.var 1) (.var 1))) (.mul (.var 0) (.mul (.var 1) (.var 1)))))) (.neg (.mul (.var 0) (.mul (.add (.var 1) (.var 1)) (.add (.var 1) (.var 1))))) (by decide +kernel)
  exact ⟨by rw [e1, hh, Shell.mul_one], by rw [e2, hh, Shell.mul_one, Shell.mul_one]⟩

/-- 27:C13 — the idempotents of `𝔽_p[Γ]`, `Γ² = −ν`: if `(a + bΓ)² = a + bΓ` with `b` invertible, then `ν` is a square,
the square of `i / (2b)`. -/
theorem idempotent_square {i h ν a b c : Shell p} (hi : i * i = -1) (hh : h + h = 1) (hc : b * c = 1)
    (h1 : a * a + -(ν * (b * b)) = a) (h2 : (a + a) * b = b) : (i * (h * c)) * (i * (h * c)) = ν := by
  have ha : a + a = 1 := by
    calc a + a = (a + a) * 1 := (Shell.mul_one _).symm
      _ = (a + a) * (b * c) := by rw [hc]
      _ = (a + a) * b * c := (Shell.mul_assoc _ _ _).symm
      _ = b * c := by rw [h2]
      _ = 1 := hc
  have n1 : (((a + a) * (a + a)) + -(((ν * (b * b)) + (ν * (b * b))) + ((ν * (b * b)) + (ν * (b * b))))) = ((((a * a) + -(ν * (b * b))) + ((a * a) + -(ν * (b * b)))) + (((a * a) + -(ν * (b * b))) + ((a * a) + -(ν * (b * b))))) :=
    Shell.Frame.RE.sound (Shell.Frame.look [ν, a, b]) (.add (.mul (.add (.var 1) (.var 1)) (.add (.var 1) (.var 1))) (.neg (.add (.add (.mul (.var 0) (.mul (.var 2) (.var 2))) (.mul (.var 0) (.mul (.var 2) (.var 2)))) (.add (.mul (.var 0) (.mul (.var 2) (.var 2))) (.mul (.var 0) (.mul (.var 2) (.var 2))))))) (.add (.add (.add (.mul (.var 1) (.var 1)) (.neg (.mul (.var 0) (.mul (.var 2) (.var 2))))) (.add (.mul (.var 1) (.var 1)) (.neg (.mul (.var 0) (.mul (.var 2) (.var 2)))))) (.add (.add (.mul (.var 1) (.var 1)) (.neg (.mul (.var 0) (.mul (.var 2) (.var 2))))) (.add (.mul (.var 1) (.var 1)) (.neg (.mul (.var 0) (.mul (.var 2) (.var 2))))))) (by decide +kernel)
  rw [h1, ha] at n1
  have n2 : (((ν * (b * b)) + (ν * (b * b))) + ((ν * (b * b)) + (ν * (b * b)))) = ((1 * 1) + -((1 * 1) + -(((ν * (b * b)) + (ν * (b * b))) + ((ν * (b * b)) + (ν * (b * b)))))) :=
    Shell.Frame.RE.sound (Shell.Frame.look [(((ν * (b * b)) + (ν * (b * b))) + ((ν * (b * b)) + (ν * (b * b))))]) (.var 0) (.add (.mul .one .one) (.neg (.add (.mul .one .one) (.neg (.var 0))))) (by decide +kernel)
  have n3 : ((1 * 1) + -(1 + 1) : Shell p) = -1 :=
    Shell.Frame.RE.sound (Shell.Frame.look []) (.add (.mul .one .one) (.neg (.add .one .one))) (.neg .one) (by decide +kernel)
  have hX : (((ν * (b * b)) + (ν * (b * b))) + ((ν * (b * b)) + (ν * (b * b)))) = -1 := by rw [n2, n1, n3]
  have n4 : ((i * (h * c)) * (i * (h * c))) = ((i * i) * ((h * c) * (h * c))) :=
    Shell.Frame.RE.sound (Shell.Frame.look [i, h, c]) (.mul (.mul (.var 0) (.mul (.var 1) (.var 2))) (.mul (.var 0) (.mul (.var 1) (.var 2)))) (.mul (.mul (.var 0) (.var 0)) (.mul (.mul (.var 1) (.var 2)) (.mul (.var 1) (.var 2)))) (by decide +kernel)
  have n5 : ((ν * ((h + h) * (h + h))) * ((b * c) * (b * c))) = ((((ν * (b * b)) + (ν * (b * b))) + ((ν * (b * b)) + (ν * (b * b)))) * ((h * c) * (h * c))) :=
    Shell.Frame.RE.sound (Shell.Frame.look [ν, h, b, c]) (.mul (.mul (.var 0) (.mul (.add (.var 1) (.var 1)) (.add (.var 1) (.var 1)))) (.mul (.mul (.var 2) (.var 3)) (.mul (.var 2) (.var 3)))) (.mul (.add (.add (.mul (.var 0) (.mul (.var 2) (.var 2))) (.mul (.var 0) (.mul (.var 2) (.var 2)))) (.add (.mul (.var 0) (.mul (.var 2) (.var 2))) (.mul (.var 0) (.mul (.var 2) (.var 2))))) (.mul (.mul (.var 1) (.var 3)) (.mul (.var 1) (.var 3)))) (by decide +kernel)
  rw [hh, hc, Shell.mul_one, Shell.mul_one, Shell.mul_one, hX] at n5
  rw [n4, hi, n5]

/-- 27:C13, 27:X6 — `𝔽_p[Γ]` holds no idempotent `a + bΓ` with `b` invertible: on a shell where `ν` is no square,
`(a + bΓ)² = a + bΓ` and `b c = 1` are contradictory. An idempotent therefore has `b = 0` and is an idempotent of the shell. -/
theorem no_idempotent {i h ν a b c : Shell p} (hi : i * i = -1) (hh : h + h = 1) (hν : ¬∃ r : Shell p, r * r = ν)
    (hc : b * c = 1) (h1 : a * a + -(ν * (b * b)) = a) (h2 : (a + a) * b = b) : False :=
  hν ⟨_, idempotent_square hi hh hc h1 h2⟩

end shell

end FRC.Chirality
