import FrcCore.Ring

/-!
# FrcCore.Theme.Quadratic — the quadratic extension of the shell, frame-free (the extension theme)

`FRC.Extension.Ext p ν`: the elements `a + b w` of `𝔽_p[w]/(w² − ν)` on components, with addition, the product
`(a + bw)(c + dw) = (ac + νbd) + (ad + bc)w`, powers, Frobenius conjugation, the trace and the norm `N = a² − νb²`;
`z z̄ = N(z)`, conjugation is a ring map and an involution, the norm scales by squares, and on the circle `N = 1` the
conjugate is the inverse. One structure for 8-dirac's coefficient field and 20-rh's extension, which keep their old names
as aliases. Split from `Theme/Extension.lean` by the ledger migration (task LM24), every name unchanged, with the ring
laws of `Ext` and the multiplicativity of the norm, decided by the normaliser (`Ring.lean`); the frame-dependent
`fixed_conj`, the quaternions and the Lorentzian plane stay in `Theme/Extension.lean`. No axioms.
-/

namespace FRC.Extension

open FRC.Shell

variable {p : Nat} [Pos p]


/-- 8:B1 — an element `a + b w` of the coefficient field, on components. -/
structure Ext (p : Nat) [Pos p] (ν : Shell p) where
  re : Shell p
  im : Shell p

namespace Ext
variable {ν : Shell p}

theorem ext {z z' : Ext p ν} (h1 : z.re = z'.re) (h2 : z.im = z'.im) : z = z' := by
  cases z; cases z'; cases h1; cases h2; rfl

theorem re_congr {a b : Ext p ν} (h : a = b) : a.re = b.re := by cases h; rfl
theorem im_congr {a b : Ext p ν} (h : a = b) : a.im = b.im := by cases h; rfl

instance : DecidableEq (Ext p ν) := fun a b =>
  if h1 : a.re = b.re then
    if h2 : a.im = b.im then isTrue (ext h1 h2) else isFalse (fun e => h2 (by cases e; rfl))
  else isFalse (fun e => h1 (by cases e; rfl))

/-- The base field inside `K`. -/
def ofShell (a : Shell p) : Ext p ν := ⟨a, 0⟩
/-- The adjoined root `w`, `w² = ν`. -/
def w : Ext p ν := ⟨0, 1⟩
instance (n : Nat) : OfNat (Ext p ν) n := ⟨ofShell (OfNat.ofNat n)⟩
instance : Add (Ext p ν) := ⟨fun z z' => ⟨z.re + z'.re, z.im + z'.im⟩⟩
instance : Neg (Ext p ν) := ⟨fun z => ⟨-z.re, -z.im⟩⟩
instance : Mul (Ext p ν) := ⟨fun z z' => ⟨z.re * z'.re + ν * (z.im * z'.im), z.re * z'.im + z.im * z'.re⟩⟩
/-- Frobenius conjugation `a + b w ↦ a − b w`. -/
def conj (z : Ext p ν) : Ext p ν := ⟨z.re, -z.im⟩
/-- The trace `Tr(a + b w) = 2a`. -/
def trace (z : Ext p ν) : Shell p := z.re + z.re
/-- The norm `N(z) = z z̄ = a² − ν b²`. -/
def norm (z : Ext p ν) : Shell p := z.re * z.re + -(ν * (z.im * z.im))
/-- Powers by structural recursion. -/
def pow (z : Ext p ν) : Nat → Ext p ν
  | 0 => 1
  | n + 1 => pow z n * z
instance : Pow (Ext p ν) Nat := ⟨pow⟩

theorem mul_re (z z' : Ext p ν) : (z * z').re = z.re * z'.re + ν * (z.im * z'.im) := rfl
theorem mul_im (z z' : Ext p ν) : (z * z').im = z.re * z'.im + z.im * z'.re := rfl
theorem ofShell_re (a : Shell p) : (ofShell a : Ext p ν).re = a := rfl
theorem ofShell_im (a : Shell p) : (ofShell a : Ext p ν).im = 0 := rfl
theorem conj_re (z : Ext p ν) : (conj z).re = z.re := rfl
theorem conj_im (z : Ext p ν) : (conj z).im = -z.im := rfl

/-- 8:A2 — `w² = ν`. -/
theorem w_sq : (w : Ext p ν) * w = ofShell ν :=
  ext (by show 0 * 0 + ν * (1 * 1) = ν; rw [Shell.zero_mul, Shell.one_mul, Shell.mul_one, Shell.zero_add])
      (by show 0 * 1 + 1 * 0 = 0; rw [Shell.zero_mul, Shell.mul_zero, Shell.zero_add])

/-- 8:A2 — the norm is the product with the conjugate: `z z̄ = N(z)`, a base-field element. -/
theorem mul_conj (z : Ext p ν) : z * conj z = ofShell (norm z) :=
  ext (by show z.re * z.re + ν * (z.im * -z.im) = z.re * z.re + -(ν * (z.im * z.im))
          rw [← Shell.mul_neg, ← Shell.mul_neg])
      (by show z.re * -z.im + z.im * z.re = 0
          rw [← Shell.mul_neg, Shell.mul_comm z.im z.re, Shell.neg_add])

/-- 8:A2 — conjugation is multiplicative (the Frobenius involution is a ring map). -/
theorem conj_mul (z z' : Ext p ν) : conj (z * z') = conj z * conj z' :=
  ext (by show z.re * z'.re + ν * (z.im * z'.im) = z.re * z'.re + ν * (-z.im * -z'.im)
          rw [Shell.neg_mul_neg])
      (by show -(z.re * z'.im + z.im * z'.re) = z.re * -z'.im + -z.im * z'.re
          rw [Shell.neg_add_rev, ← Shell.mul_neg, ← Shell.neg_mul])

/-- 8:B6 — norm growth: `N(c z) = c² N(z)` for every base residue `c`; one chronon of drive multiplies every
norm by `g²`, a square. -/
theorem norm_scale (c : Shell p) (z : Ext p ν) : norm (ofShell c * z) = c * c * norm z := by
  unfold norm
  rw [mul_re, mul_im, ofShell_re, ofShell_im, Shell.zero_mul, Shell.mul_zero, Shell.add_zero,
    Shell.zero_mul, Shell.add_zero, FRC.Shell.mul_mul_mul_comm, FRC.Shell.mul_mul_mul_comm c z.im c z.im,
    Shell.mul_left_comm ν (c * c), Shell.left_distrib, ← Shell.mul_neg]

/-- 20:B9 — conjugation is an involution. -/
theorem conj_conj (z : Ext p ν) : conj (conj z) = z := ext rfl (Shell.neg_neg z.im)

/-- 20:B6 — on the circle `N(z) = 1` the conjugate is the inverse: `z z̄ = 1`. -/
theorem conj_inv_of_norm_one (z : Ext p ν) (hz : norm z = 1) : z * conj z = 1 := by
  rw [mul_conj, hz]; rfl



/-! ## Ring laws and the norm's multiplicativity (task LM24; the identities decided by `Ring.lean`'s normaliser) -/

theorem ofShell_mul_eq (c : Shell p) (z : Ext p ν) : ofShell c * z = ⟨c * z.re, c * z.im⟩ :=
  ext (by show c * z.re + ν * (0 * z.im) = c * z.re; rw [Shell.zero_mul, Shell.mul_zero, Shell.add_zero])
      (by show c * z.im + 0 * z.re = c * z.im; rw [Shell.zero_mul, Shell.add_zero])

theorem ofShell_mul (a b : Shell p) : (ofShell a : Ext p ν) * ofShell b = ofShell (a * b) := by
  rw [ofShell_mul_eq]; exact ext rfl (Shell.mul_zero a)

theorem one_mul (z : Ext p ν) : (1 : Ext p ν) * z = z := by
  show ofShell 1 * z = z
  rw [ofShell_mul_eq, Shell.one_mul, Shell.one_mul]

theorem mul_comm (z z' : Ext p ν) : z * z' = z' * z :=
  ext (by show z.re * z'.re + ν * (z.im * z'.im) = z'.re * z.re + ν * (z'.im * z.im)
          rw [Shell.mul_comm z.re, Shell.mul_comm z.im])
      (by show z.re * z'.im + z.im * z'.re = z'.re * z.im + z'.im * z.re
          rw [Shell.add_comm, Shell.mul_comm z.im, Shell.mul_comm z.re])

theorem mul_assoc (z z' z'' : Ext p ν) : z * z' * z'' = z * (z' * z'') :=
  ext (Shell.Frame.RE.sound (Shell.Frame.look [ν, z.re, z.im, z'.re, z'.im, z''.re, z''.im])
        (.add (.mul (.add (.mul (.var 1) (.var 3)) (.mul (.var 0) (.mul (.var 2) (.var 4)))) (.var 5)) (.mul (.var 0) (.mul (.add (.mul (.var 1) (.var 4)) (.mul (.var 2) (.var 3))) (.var 6))))
        (.add (.mul (.var 1) (.add (.mul (.var 3) (.var 5)) (.mul (.var 0) (.mul (.var 4) (.var 6))))) (.mul (.var 0) (.mul (.var 2) (.add (.mul (.var 3) (.var 6)) (.mul (.var 4) (.var 5))))))
        (by decide +kernel))
      (Shell.Frame.RE.sound (Shell.Frame.look [ν, z.re, z.im, z'.re, z'.im, z''.re, z''.im])
        (.add (.mul (.add (.mul (.var 1) (.var 3)) (.mul (.var 0) (.mul (.var 2) (.var 4)))) (.var 6)) (.mul (.add (.mul (.var 1) (.var 4)) (.mul (.var 2) (.var 3))) (.var 5)))
        (.add (.mul (.var 1) (.add (.mul (.var 3) (.var 6)) (.mul (.var 4) (.var 5)))) (.mul (.var 2) (.add (.mul (.var 3) (.var 5)) (.mul (.var 0) (.mul (.var 4) (.var 6))))))
        (by decide +kernel))

/-- The norm is multiplicative: `N(z z') = N(z) N(z')`. -/
theorem norm_mul (z z' : Ext p ν) : norm (z * z') = norm z * norm z' :=
  Shell.Frame.RE.sound (Shell.Frame.look [ν, z.re, z.im, z'.re, z'.im])
    (.add (.mul (.add (.mul (.var 1) (.var 3)) (.mul (.var 0) (.mul (.var 2) (.var 4)))) (.add (.mul (.var 1) (.var 3)) (.mul (.var 0) (.mul (.var 2) (.var 4))))) (.neg (.mul (.var 0) (.mul (.add (.mul (.var 1) (.var 4)) (.mul (.var 2) (.var 3))) (.add (.mul (.var 1) (.var 4)) (.mul (.var 2) (.var 3)))))))
    (.mul (.add (.mul (.var 1) (.var 1)) (.neg (.mul (.var 0) (.mul (.var 2) (.var 2))))) (.add (.mul (.var 3) (.var 3)) (.neg (.mul (.var 0) (.mul (.var 4) (.var 4))))))
    (by decide +kernel)

theorem norm_ofShell (c : Shell p) : norm (ofShell c : Ext p ν) = c * c := by
  show c * c + -(ν * (0 * 0)) = c * c
  rw [Shell.zero_mul, Shell.mul_zero, Shell.neg_zero, Shell.add_zero]

end Ext

end FRC.Extension
