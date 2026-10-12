import FrcCore.Cycle

/-!
# FrcCore.Theme.Shift — the cycle, its shifts and the finite Fourier shift theorem (the gravity theme's first file; 21-gravity, 10 October 2026, moved from the fourier theme on 11 October; the cycle lemmas to the base on 12 October)

The cycle of `n` sites (`FRC.Cycle.cyc`, a function `Nat → Shell p` read at `i mod n`), its return after `n` steps and the
invariance of a sum over the cycle under the shift of its index (`sum_shift`) live in the base theme's `Cycle.lean` since
12 October 2026 (38-s13, task T02; here from 10 to 12 October), so that every theme may read the cycle. The finite Fourier transform
on the cycle against a character `ζ` with `ζⁿ = 1` is `F f (k) = Σ_x f(x) ζ^{xk}` (`dft`); the exponent is read modulo `n`
(`pow_mod`). The shift theorem in both forms (21:C20, the kick of the two-shift law): the kick — multiplication by the
character `ζ^{ax}` in position — is the shift `k ↦ k + a` of the transform (`dft_kick`), and the shift of the position by
`a` is multiplication of the transform by `ζ^{ak}` (`dft_shift`). No axioms.
-/

namespace FRC.Cycle

open FRC.Shell

variable {p : Nat} [Pos p]

/-! ## A character of the cycle: the exponent reads modulo `n` -/

/-- With `ζⁿ = 1` the power `ζ^m` depends on `m` modulo `n`. -/
theorem pow_mod (n : Nat) (hn : 0 < n) {ζ : Shell p} (hζ : ζ ^ n = 1) (m : Nat) : ζ ^ m = ζ ^ (m % n) := by
  obtain ⟨q, hq⟩ := FRC.Nat.mod_spec n hn m
  calc ζ ^ m = ζ ^ (n * q + m % n) := by rw [← hq]
    _ = (ζ ^ n) ^ q * ζ ^ (m % n) := by rw [pow_add, pow_mul]
    _ = ζ ^ (m % n) := by rw [hζ, one_pow, one_mul]

/-! ## The finite Fourier transform on the cycle and the shift theorem (21:C20) -/

/-- The transform of `f` on the cycle of `n` sites against the character `ζ`: `F f (k) = Σ_{x<n} f(x) ζ^{xk}`. -/
def dft (n : Nat) (ζ : Shell p) (f : Nat → Shell p) (k : Nat) : Shell p :=
  sumRange (fun x => cyc n f x * ζ ^ (x * k)) n

/-- 21:C20 — the kick: multiplying `f` by the character `ζ^{ax}` in position shifts the transform,
`F(ζ^{a·} f)(k) = F f (k + a)`, on every character with `ζⁿ = 1`. -/
theorem dft_kick (n : Nat) (hn : 0 < n) {ζ : Shell p} (hζ : ζ ^ n = 1) (f : Nat → Shell p) (a k : Nat) :
    dft n ζ (fun x => ζ ^ (a * x) * f x) k = dft n ζ f (k + a) := by
  apply sum_congr; intro x _
  show ζ ^ (a * (x % n)) * f (x % n) * ζ ^ (x * k) = f (x % n) * ζ ^ (x * (k + a))
  have e1 : ζ ^ (a * (x % n)) = ζ ^ (x * a) := by
    rw [pow_mod n hn hζ (a * (x % n)), FRC.Nat.mul_mod_mod a x n hn, Nat.mul_comm a x, ← pow_mod n hn hζ]
  rw [e1, Nat.mul_add, pow_add, mul_comm (ζ ^ (x * a)) (f (x % n)), mul_assoc, mul_comm (ζ ^ (x * a))]

/-- 21:C20 — the shift: moving the position by `a` (`f(x − a)`, read on the cycle) multiplies the transform by the
character `ζ^{ak}`: `F(f(· − a))(k) = ζ^{ak} F f (k)`, for `a ≤ n` and `ζⁿ = 1`. -/
theorem dft_shift (n : Nat) (hn : 0 < n) {ζ : Shell p} (hζ : ζ ^ n = 1) (f : Nat → Shell p) (a k : Nat) (ha : a ≤ n) :
    dft n ζ (fun x => cyc n f (x + (n - a))) k = ζ ^ (a * k) * dft n ζ f k := by
  show sumRange (fun x => cyc n (fun x => cyc n f (x + (n - a))) x * ζ ^ (x * k)) n = ζ ^ (a * k) * dft n ζ f k
  -- read the shifted function on the cycle: `cyc n (cyc n f (· + (n − a))) x = cyc n f (x + (n − a))`
  have e0 : ∀ x, cyc n (fun x => cyc n f (x + (n - a))) x = cyc n f (x + (n - a)) := fun x => by
    show cyc n f (x % n + (n - a)) = cyc n f (x + (n - a)); exact cyc_add_mod n hn f x (n - a)
  rw [sum_congr n (fun x _ => by rw [e0 x])]
  -- reindex `x = (y + a) mod n`
  rw [← sum_shift n hn (fun x => cyc n f (x + (n - a)) * ζ ^ (x * k)) a]
  rw [dft, ← sum_mul_left]
  apply sum_congr; intro y _
  show cyc n f ((y + a) % n + (n - a)) * ζ ^ ((y + a) % n * k) = ζ ^ (a * k) * (cyc n f y * ζ ^ (y * k))
  have e1 : cyc n f ((y + a) % n + (n - a)) = cyc n f y := by
    rw [cyc_add_mod n hn, Nat.add_assoc, Nat.add_comm a (n - a), FRC.Nat.sub_add_cancel ha, cyc_add_n n hn]
  have e2 : ζ ^ ((y + a) % n * k) = ζ ^ (y * k) * ζ ^ (a * k) := by
    rw [pow_mod n hn hζ ((y + a) % n * k), FRC.Nat.mod_mul_mod (y + a) k n hn, ← pow_mod n hn hζ, Nat.add_mul, pow_add]
  rw [e1, e2, ← mul_assoc, mul_comm (cyc n f y * ζ ^ (y * k)) (ζ ^ (a * k))]

end FRC.Cycle
