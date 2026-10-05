import Mathlib

/-!
# FrcLedger.Theme.Frame — the frame's square classes (the frame theme, ledger migration task LM17)

On `ZMod p` with a primitive root `g`, `g^k` is a square exactly when `k` is even, and `g` and `g⁻¹` are nonsquares
(8:B5, 8:B3); over a field with `2 ≠ 0` the roots of `y² = x²` are exactly `±x` (10:E4). Moved from 8-dirac's and
10-dimensions' modules, which keep the old names as aliases. Classical, on Mathlib's hierarchy.
-/

namespace FRC.Frame

section parity
variable {p : ℕ} [hp : Fact (Nat.Prime p)]

/-- 8:B5 — the square class is chronon parity: for a primitive root `g` (`orderOf g = p − 1`), `g^k` is a
square exactly when `k` is even (Theorem `parity`). -/
theorem parity_iff {g : ZMod p} (hg : orderOf g = p - 1) (hodd : p % 2 = 1) (k : ℕ) :
    IsSquare (g ^ k) ↔ Even k := by
  have hg0 : g ≠ 0 := by
    rintro rfl
    have := hp.out.two_le
    have h : orderOf (0 : ZMod p) = 0 := by
      rw [orderOf_eq_zero_iff']
      intro n hn h0
      rw [zero_pow hn.ne'] at h0
      exact zero_ne_one h0
    omega
  have hgk : g ^ k ≠ 0 := pow_ne_zero k hg0
  rw [ZMod.euler_criterion p hgk, ← pow_mul, ← orderOf_dvd_iff_pow_eq_one, hg]
  have hp2 : p - 1 = 2 * (p / 2) := by have := hp.out.two_le; omega
  rw [hp2]
  constructor
  · rintro ⟨c, hc⟩
    have hpos : 0 < p / 2 := by have := hp.out.two_le; omega
    have : k = 2 * c := Nat.eq_of_mul_eq_mul_right hpos (by rw [hc]; ring)
    exact ⟨c, by omega⟩
  · rintro ⟨c, rfl⟩
    exact ⟨c, by ring⟩

/-- 8:B3 — the drive is a nonsquare (`g^{(p−1)/2} = −1`), and so is its inverse `g^{p−2}`: `[g⁻¹] = [g]`. -/
theorem drive_nonsquare {g : ZMod p} (hg : orderOf g = p - 1) (hodd : p % 2 = 1) :
    ¬ IsSquare g ∧ ¬ IsSquare g⁻¹ := by
  have h1 := parity_iff hg hodd 1
  have h2 := parity_iff hg hodd (p - 2)
  rw [pow_one] at h1
  have hinv : g⁻¹ = g ^ (p - 2) := by
    have hg0 : g ≠ 0 := by
      rintro rfl
      have := hp.out.two_le
      have h : orderOf (0 : ZMod p) = 0 := by
        rw [orderOf_eq_zero_iff']
        intro n hn h0
        rw [zero_pow hn.ne'] at h0
        exact zero_ne_one h0
      omega
    have : g ^ (p - 1) = 1 := by rw [← hg]; exact pow_orderOf_eq_one g
    have hp3 : p - 1 = (p - 2) + 1 := by have := hp.out.two_le; omega
    rw [hp3, pow_succ] at this
    exact (eq_inv_of_mul_eq_one_left this).symm
  refine ⟨fun h => ?_, fun h => ?_⟩
  · exact Nat.not_even_one (h1.1 h)
  · rw [hinv] at h
    obtain ⟨c, hc⟩ := h2.1 h
    have := hp.out.two_le
    omega

end parity

section field
variable {K : Type*} [Field K]

/-- 10:E4 — each quadratic defining congruence has exactly two roots, the pair `{x, −x}`: if `x² = a` with
`x ≠ 0` (`2 ≠ 0`), then `y² = a` iff `y = x` or `y = −x`, and `−x ≠ x`. -/
theorem root_pair (a x : K) (hx : x ^ 2 = a) (hx0 : x ≠ 0) (h2 : (2 : K) ≠ 0) :
    (∀ y : K, y ^ 2 = a ↔ y = x ∨ y = -x) ∧ -x ≠ x := by
  refine ⟨fun y => by rw [← hx]; exact sq_eq_sq_iff_eq_or_eq_neg, fun h => hx0 ?_⟩
  apply mul_left_cancel₀ h2
  linear_combination -h

end field

end FRC.Frame
