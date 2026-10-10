import FrcCore.Series

/-!
# FrcCore.Theme.Shift — the cycle, its shifts and the finite Fourier shift theorem (the fourier theme; 21-gravity, 10 October 2026)

A function on the cycle of `n` sites is a function `Nat → Shell p` read at `i mod n` (`cyc`). A sum over the cycle is
invariant under the shift of its index (`sum_shift`), because `j ↦ (j + s) mod n` permutes `[0, n)` (`shift_inj`, proved
on the core's own division algorithm `FRC.Nat.mod_spec`, without the prelude's `omega`). The finite Fourier transform
on the cycle against a character `ζ` with `ζⁿ = 1` is `F f (k) = Σ_x f(x) ζ^{xk}` (`dft`); the exponent is read modulo `n`
(`pow_mod`). The shift theorem in both forms (21:C20, the kick of the two-shift law): the kick — multiplication by the
character `ζ^{ax}` in position — is the shift `k ↦ k + a` of the transform (`dft_kick`), and the shift of the position by
`a` is multiplication of the transform by `ζ^{ak}` (`dft_shift`). No axioms.
-/

namespace FRC.Cycle

open FRC.Shell

variable {p : Nat} [Pos p]

/-- A function on the cycle, read at `i mod n`. -/
def cyc (n : Nat) (f : Nat → Shell p) (i : Nat) : Shell p := f (i % n)

theorem cyc_mod (n : Nat) (hn : 0 < n) (f : Nat → Shell p) (i : Nat) : cyc n f (i % n) = cyc n f i := by
  show f (i % n % n) = f (i % n); rw [FRC.Nat.mod_mod i n hn]

theorem cyc_add_mod (n : Nat) (hn : 0 < n) (f : Nat → Shell p) (i s : Nat) :
    cyc n f (i % n + s) = cyc n f (i + s) := by
  show f ((i % n + s) % n) = f ((i + s) % n); rw [FRC.Nat.mod_add_mod i s n hn]

theorem cyc_add_n (n : Nat) (hn : 0 < n) (f : Nat → Shell p) (i : Nat) : cyc n f (i + n) = cyc n f i := by
  show f ((i + n) % n) = f (i % n)
  rw [FRC.Nat.add_mod i n n hn, FRC.Nat.mod_self n hn, Nat.add_zero, FRC.Nat.mod_mod i n hn]

/-! ## The shift permutes the cycle -/

theorem shift_lt (n : Nat) (hn : 0 < n) (s j : Nat) (_ : j < n) : (j + s) % n < n := FRC.Nat.mod_lt' _ hn

/-- If `i + s` and `j + s` share a residue mod `n` with quotients `q₁ < q₂`, then `j ≥ i + n`, impossible for `j < n`. -/
theorem no_lower_quot {n i j s q₁ q₂ r : Nat} (hj : j < n) (h1 : i + s = n * q₁ + r) (h2 : j + s = n * q₂ + r)
    (hq : q₁ < q₂) : False := by
  have h3 : n * (q₁ + 1) ≤ n * q₂ := Nat.mul_le_mul_left n (Nat.succ_le_of_lt hq)
  rw [Nat.mul_succ] at h3
  have h4 : i + s + n ≤ j + s := by
    rw [h2, h1]
    calc n * q₁ + r + n = n * q₁ + n + r := by rw [Nat.add_assoc, Nat.add_comm r n, ← Nat.add_assoc]
      _ ≤ n * q₂ + r := Nat.add_le_add_right h3 r
  have h5 : i + n ≤ j := by
    have : (i + n) + s ≤ j + s := by
      rw [Nat.add_right_comm]; exact h4
    exact Nat.le_of_add_le_add_right this
  exact Nat.lt_irrefl n (Nat.lt_of_le_of_lt (Nat.le_trans (Nat.le_add_left n i) h5) hj)

/-- The shift `j ↦ (j + s) mod n` is injective on `[0, n)`. -/
theorem shift_inj (n : Nat) (hn : 0 < n) (s i j : Nat) (hi : i < n) (hj : j < n)
    (h : (i + s) % n = (j + s) % n) : i = j := by
  obtain ⟨q₁, h1⟩ := FRC.Nat.mod_spec n hn (i + s)
  obtain ⟨q₂, h2⟩ := FRC.Nat.mod_spec n hn (j + s)
  rw [h] at h1
  rcases Nat.lt_or_ge q₁ q₂ with hq | hq
  · exact (no_lower_quot hj h1 h2 hq).elim
  · rcases Nat.lt_or_ge q₂ q₁ with hq' | hq'
    · exact (no_lower_quot hi h2 h1 hq').elim
    · have e : q₁ = q₂ := Nat.le_antisymm hq' hq
      rw [e] at h1
      exact Nat.add_right_cancel (h1.trans h2.symm)

/-- A sum over the cycle is invariant under the shift of its index by `s`. -/
theorem sum_shift (n : Nat) (hn : 0 < n) (F : Nat → Shell p) (s : Nat) :
    sumRange (fun j => F ((j + s) % n)) n = sumRange F n :=
  sum_perm F (fun j => (j + s) % n) n (shift_lt n hn s) (shift_inj n hn s)

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
