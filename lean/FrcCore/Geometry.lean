import FrcCore.Frame

/-!
# FrcCore.Geometry — 2-geometry rows on the core

2:C2 (the cell counts of the orbital shell and its completion, as identities of natural numbers) and
2:E3 (the fixed-shell refutation at `(13, 2)`: no grid point `x/2^n`, `x ≤ 6`, lies in `(3/4, 1)`, as
the integer statement `¬(3·2^n < 4x ∧ x < 2^n)`). No axioms.
-/

namespace FRC
namespace Geometry

/-- 2:C2 (Remark 3.4) — the counts: with `π = m + 1` phases-deep and `n = p − 1` phases,
`|V| − |E| + |F| = 1` for the shell and `2` for its completion, written without subtraction:
`(πn + 1) + πn = 2πn + 1` and `((π−1)n + 2) + πn = (2π−1)n + 2`. -/
theorem euler_characteristic (m n : Nat) :
    ((m + 1) * n + 1) + (m + 1) * n = 2 * ((m + 1) * n) + 1 ∧
    (m * n + 2) + (m + 1) * n = (2 * m + 1) * n + 2 := by
  constructor
  · rw [Nat.two_mul, Nat.add_right_comm]
  · rw [FRC.Nat.add_mul, FRC.Nat.add_mul, Nat.one_mul, FRC.Nat.mul_assoc, Nat.two_mul,
      FRC.Nat.add_add_add_comm, Nat.add_comm 2 n, ← Nat.add_assoc]

/-- 2:E3 — the fixed-shell refutation at `p = 13`, `g = 2` (window `x ≤ 6`): no grid point `x / 2^n`
lies strictly between `3/4` and `1` at any depth `n` — the covering radius of the fixed-shell
refinement in `[0, 1]` is at least `1/8` for every depth. -/
theorem fixed_shell_gap (n x : Nat) (hx : x ≤ 6) : ¬ (3 * 2 ^ n < 4 * x ∧ x < 2 ^ n) := by
  intro h
  match Nat.lt_or_ge n 3 with
  | .inl hn =>
    exact (by decide : ∀ n, n < 3 → ∀ x, x ≤ 6 → ¬ (3 * 2 ^ n < 4 * x ∧ x < 2 ^ n)) n hn x hx h
  | .inr hn =>
    have h8 : 2 ^ 3 ≤ 2 ^ n := Nat.pow_le_pow_right (Nat.zero_lt_succ 1) hn
    have h24 : 4 * x ≤ 4 * 6 := Nat.mul_le_mul_left 4 hx
    have h24' : 3 * 2 ^ 3 ≤ 3 * 2 ^ n := Nat.mul_le_mul_left 3 h8
    exact Nat.lt_irrefl _ (Nat.lt_of_lt_of_le (Nat.lt_of_le_of_lt h24' h.1) h24)

/-- 2:E3 (the fixed-shell bound, every shell) — for `g ≥ 2`, any cut `m`, depth `n` and `x ≤ 2κ` with
`x < g^n` (the grid point `x/g^n` below `1`): either `x/g^n ≤ 1 − g^{−m}`, i.e. `x·g^m + g^n ≤ g^m·g^n`,
or `x/g^n ≤ 2κ·g^{−(m+1)}`, i.e. `x·g^{m+1} ≤ 2κ·g^n`. With `2κ + 1 < g^{m+1}` both bounds are below `1`, so the
covering radius of the fixed-shell refinement in `[0, 1]` is bounded below at every depth. -/
theorem fixed_shell_bound (g κ m n x : Nat) (hg : 2 ≤ g) (hx : x ≤ 2 * κ) (hlt : x < g ^ n) :
    x * g ^ m + g ^ n ≤ g ^ m * g ^ n ∨ x * g ^ (m + 1) ≤ 2 * κ * g ^ n := by
  have hg1 : 1 ≤ g := Nat.le_trans (Nat.le_succ 1) hg
  match Nat.lt_or_ge n (m + 1) with
  | .inl hnm =>
    -- n ≤ m: x + 1 ≤ g^n, so x·g^m + g^m ≤ g^n·g^m, and g^n ≤ g^m
    refine .inl ?_
    have hn : n ≤ m := Nat.le_of_lt_succ hnm
    have h1 : (x + 1) * g ^ m ≤ g ^ n * g ^ m := Nat.mul_le_mul_right _ hlt
    have h2 : g ^ n ≤ g ^ m := Nat.pow_le_pow_right (Nat.lt_of_lt_of_le (Nat.zero_lt_succ 0) hg1) hn
    rw [FRC.Nat.add_mul, Nat.one_mul] at h1
    calc x * g ^ m + g ^ n ≤ x * g ^ m + g ^ m := Nat.add_le_add_left h2 _
      _ ≤ g ^ n * g ^ m := h1
      _ = g ^ m * g ^ n := Nat.mul_comm _ _
  | .inr hnm =>
    refine .inr ?_
    have h1 : g ^ (m + 1) ≤ g ^ n := Nat.pow_le_pow_right (Nat.lt_of_lt_of_le (Nat.zero_lt_succ 0) hg1) hnm
    exact Nat.mul_le_mul hx h1

/-- The cut `m = ⌊log_g(2κ+1)⌋`, i.e. `2κ + 1 < g^{m+1}`, puts the second bound below `1`
(`2κ·g^n < g^{m+1}·g^n`); the first is below `1` for every `m` (`g^m·g^n − g^n < g^m·g^n`). -/
theorem fixed_shell_bound_lt_one (g κ m n : Nat) (hg : 2 ≤ g) (hm : 2 * κ + 1 < g ^ (m + 1)) :
    2 * κ * g ^ n < g ^ (m + 1) * g ^ n ∧ 0 < g ^ n := by
  have hg1 : 1 ≤ g := Nat.le_trans (Nat.le_succ 1) hg
  have hpos : 0 < g ^ n := Nat.pow_pos (Nat.lt_of_lt_of_le (Nat.zero_lt_succ 0) hg1)
  exact ⟨FRC.Nat.mul_lt_mul_of_lt_of_pos (Nat.lt_of_le_of_lt (Nat.le_succ _) hm) hpos, hpos⟩

end Geometry
end FRC
