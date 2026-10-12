import FrcCore.Series

/-!
# FrcCore.Cycle — the cycle of `n` sites and the shift of its index (the base theme; 38-s13, 12 October 2026)

A function on the cycle of `n` sites is a function `Nat → Shell p` read at `i mod n` (`cyc`); it returns after `n` steps
(`cyc_add_n`). A sum over the cycle is invariant under the shift of its index (`sum_shift`), because `j ↦ (j + s) mod n`
permutes `[0, n)` (`shift_inj`, proved on the core's own division algorithm `FRC.Nat.mod_spec`, without the prelude's
`omega`). Moved here from the gravity theme's `Theme/Shift.lean` (21-gravity, 10 October 2026) on 12 October (38-s13,
task T02; the author's decision D4), so that every theme may read the cycle; every name is unchanged (`FRC.Cycle`), and
the shift theorem stays in `Theme/Shift.lean`. No axioms.
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

/-- 21:X3, 00:E5, 00:E10, 38:B4 — the drive returns after `n` steps: a function on the cycle read `n` sites on is itself, so a permutation of
the cycle has finite order and what it moves comes back. -/
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

end FRC.Cycle
