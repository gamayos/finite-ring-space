import FrcCore.Orbit
import FrcCore.Sum
import FrcCore.Instances
import FrcCore.Poly

/-!
# FrcCore.Theme.Orbital — the orbital shell's arithmetic (the geometry theme)

The geometry theme holds 2-geometry's exact content above the frame (6 November 2026, the minimal revision of the
paper; moved here from the paper module `FrcCore/Geometry.lean`, every name unchanged): the cell counts of the orbital
shell and its completion (2:C2); the fixed-shell bound of the scale grids, its floor `1/(p+1)` and the `(13, 2)` gap
(2:E3); which reindexings of the phase cycle preserve its adjacency (2:B4); the frame moves the labels of one complex
(2:C4); the Lipschitz budget of a bounded experiment (2:E4); the exponents of the external transport (2:F6). No axioms.
-/

namespace FRC
namespace Geometry

/-- 2:C2, 2:C3, 2:C6 (Remark 3.4) — the counts: with `π = m + 1` phases-deep and `n = p − 1` phases,
`|V| − |E| + |F| = 1` for the shell and `2` for its completion, written without subtraction:
`(πn + 1) + πn = 2πn + 1` and `((π−1)n + 2) + πn = (2π−1)n + 2`. -/
theorem euler_characteristic (m n : Nat) :
    ((m + 1) * n + 1) + (m + 1) * n = 2 * ((m + 1) * n) + 1 ∧
    (m * n + 2) + (m + 1) * n = (2 * m + 1) * n + 2 := by
  constructor
  · rw [Nat.two_mul, Nat.add_right_comm]
  · rw [FRC.Nat.add_mul, FRC.Nat.add_mul, Nat.one_mul, FRC.Nat.mul_assoc, Nat.two_mul,
      FRC.Nat.add_add_add_comm, Nat.add_comm 2 n, ← Nat.add_assoc]

/-- 2:E3 — the fixed-shell gap at `p = 13`, `g = 2` (window `x ≤ 6`): no grid point `x / 2^n`
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

/-! ### 2:B4 — which reindexings of the phase cycle are cellular -/

/-- `m` and `m'` are adjacent on the phase cycle of length `n`. -/
def Adj (n m m' : Nat) : Prop := (m + 1) % n = m' ∨ (m' + 1) % n = m

/-- The reindexing `ρ_u : m ↦ u·m mod n`. -/
def rho (n u m : Nat) : Nat := (u * m) % n

/-- 2:B4, 2:C4 (Prop. 2.8) — `ρ_u` preserves the adjacency of the phase cycle (`n ≥ 3`) exactly when
`u ≡ 1` or `u ≡ −1 (mod n)`. -/
theorem rho_adj_iff (n u : Nat) (hn : 3 ≤ n) :
    (∀ m, m < n → Adj n (rho n u m) (rho n u ((m + 1) % n))) ↔ (u % n = 1 ∨ u % n = n - 1) := by
  have hn0 : 0 < n := Nat.lt_of_lt_of_le (Nat.zero_lt_succ 2) hn
  have h1n : 1 < n := Nat.lt_of_lt_of_le (Nat.lt_succ_self 1) (Nat.le_trans (Nat.le_succ 2) hn)
  constructor
  · intro h
    have h0 := h 0 hn0
    unfold rho at h0
    rw [Nat.mul_zero, FRC.Nat.zero_mod, Nat.zero_add, FRC.Nat.mod_eq_of_lt h1n, Nat.mul_one] at h0
    -- Adj n 0 (u % n): (0 + 1) % n = u % n, or (u % n + 1) % n = 0
    match h0 with
    | Or.inl e => exact Or.inl (by rw [Nat.zero_add, FRC.Nat.mod_eq_of_lt h1n] at e; exact e.symm)
    | Or.inr e =>
      refine Or.inr ?_
      have hu := Nat.mod_lt u hn0
      exact match Nat.lt_or_ge (u % n + 1) n with
        | Or.inl hlt => by
            rw [FRC.Nat.mod_eq_of_lt hlt] at e
            exact absurd e (Nat.succ_ne_zero _)
        | Or.inr hge =>
            have : u % n + 1 = n := Nat.le_antisymm hu hge
            calc u % n = (u % n + 1) - 1 := (FRC.Nat.add_sub_cancel _ _).symm
              _ = n - 1 := by rw [this]
  · intro h m hm
    unfold rho Adj
    match h with
    | Or.inl e =>
      -- u ≡ 1: ρ is the identity on residues
      have e1 : ∀ x, x < n → (u * x) % n = x := fun x hx => by
        rw [← FRC.Nat.mod_mul_mod _ _ _ hn0, e, Nat.one_mul, FRC.Nat.mod_eq_of_lt hx]
      rw [e1 m hm, e1 _ (Nat.mod_lt _ hn0)]
      exact Or.inl rfl
    | Or.inr e =>
      -- u ≡ −1: ρ is the reflection m ↦ (n − m) % n, and rev (m+1) + 1 ≡ rev m
      have e1 : ∀ x, x < n → (u * x) % n = Shell.Frame.rev n x := fun x hx => by
        unfold Shell.Frame.rev
        rw [← FRC.Nat.mod_mul_mod _ _ _ hn0, e]
        exact match Nat.decEq x 0 with
          | isTrue hx0 => by rw [hx0, Nat.mul_zero, Nat.sub_zero, FRC.Nat.zero_mod, FRC.Nat.mod_self n hn0]
          | isFalse hx0 => by
              have hx0' := Nat.pos_of_ne_zero hx0
              -- (n − 1)·x = n·(x − 1) + (n − x)
              have : (n - 1) * x = n * (x - 1) + (n - x) := by
                have h1 : (n - 1) * x + x = n * x := by
                  rw [← Nat.succ_mul, Nat.succ_eq_add_one, FRC.Nat.sub_add_cancel (Nat.le_of_lt h1n)]
                have h2 : n * (x - 1) + n = n * x := by
                  rw [← Nat.mul_succ, Nat.succ_eq_add_one, FRC.Nat.sub_add_cancel hx0']
                have h3 : n * (x - 1) + (n - x) + x = n * x := by
                  rw [Nat.add_assoc, FRC.Nat.sub_add_cancel (Nat.le_of_lt hx), h2]
                exact FRC.Nat.add_right_cancel (h1.trans h3.symm)
              rw [this, FRC.Nat.add_mul_mod_self_left _ _ _ hn0]
      rw [e1 m hm, e1 _ (Nat.mod_lt _ hn0)]
      -- rev (m+1 mod n) + 1 ≡ rev m: both ≡ −m
      refine Or.inr ?_
      exact match Nat.lt_or_ge (m + 1) n with
        | Or.inl hlt => by
            rw [FRC.Nat.mod_eq_of_lt hlt]
            exact match Nat.decEq m 0 with
              | isTrue e0 => by
                  rw [e0] at hlt ⊢
                  rw [Shell.Frame.rev_zero _ hn0, Shell.Frame.rev_of_pos hlt (Nat.zero_lt_succ 0), Nat.zero_add,
                    FRC.Nat.sub_add_cancel (Nat.le_of_lt h1n)]
                  exact FRC.Nat.mod_self n hn0
              | isFalse e0 => by
                  have hm0 := Nat.pos_of_ne_zero e0
                  rw [Shell.Frame.rev_of_pos hlt (Nat.zero_lt_succ m), Shell.Frame.rev_of_pos hm hm0]
                  -- (n − (m+1)) + 1 = n − m, below n
                  have : n - (m + 1) + 1 = n - m := by
                    have h1 : n - (m + 1) + (m + 1) = n := FRC.Nat.sub_add_cancel (Nat.le_of_lt hlt)
                    have h2 : n - m + m = n := FRC.Nat.sub_add_cancel (Nat.le_of_lt hm)
                    apply FRC.Nat.add_right_cancel (c := m)
                    rw [h2, Nat.add_assoc, Nat.add_comm 1 m, h1]
                  rw [this]
                  exact FRC.Nat.mod_eq_of_lt (Nat.sub_lt hn0 hm0)
        | Or.inr hge => by
            -- m + 1 = n: m = n − 1, rev 0 + 1 = 1, rev (n−1) = 1
            have hmn : m + 1 = n := Nat.le_antisymm hm hge
            rw [hmn, FRC.Nat.mod_self _ hn0, Shell.Frame.rev_zero _ hn0, Nat.zero_add, FRC.Nat.mod_eq_of_lt h1n]
            have hm0 : 0 < m := by
              refine Nat.lt_of_add_lt_add_right (n := 1) ?_
              rw [Nat.zero_add, hmn]; exact h1n
            rw [Shell.Frame.rev_of_pos hm hm0, ← hmn, FRC.Nat.add_sub_cancel_left]

/-- 2:B4 — the rotations `m ↦ m + c` preserve adjacency (with `ρ_{±1}` they generate the dihedral maps of B4). -/
theorem rotation_adj (n c m : Nat) (hn : 0 < n) : Adj n ((m + c) % n) (((m + 1) % n + c) % n) := by
  unfold Adj
  refine Or.inl ?_
  rw [FRC.Nat.mod_add_mod _ _ _ hn, FRC.Nat.mod_add_mod _ _ _ hn, Nat.add_right_comm]

/-! ### 2:C4 — the frame moves the labels of one complex -/

variable {p : Nat} [Pos p]

/-- The action reading of the vertex `(a, m)` in the frame with drive `g`: `a · g^m`. -/
def label (g : Shell p) (a : Shell p) (m : Nat) : Shell p := a * g ^ m

/-- 2:C4 (Prop. 3.5) — the complex is one for every generator; the frame `g' = g^u` moves the
labels by the reindexing `ρ_u`: `label g' (a, m) = label g (a, u·m mod n)`. -/
theorem label_covariance {κ : Nat} {g : Shell p} (F : Shell.Frame p κ g) (u : Nat) (a : Shell p) (m : Nat) :
    label (g ^ u) a m = label g a (rho (p - 1) u m) := by
  unfold label rho
  rw [← Shell.pow_mul, F.pow_mod (u * m)]


/-! ### 2:E3 — the floor of the fixed-shell bound -/

/-- 2:E3 — the floor: with `2κ + 1 < g^{m+1}` the second bound `2κ·g^{−(m+1)}` leaves a gap below `1` longer than
`1/(2κ+1)`, i.e. `g^{m+1} < (g^{m+1} − 2κ)·(2κ + 1)`; with `g^m ≤ 2κ + 1` the first gap `g^{−m}` is at least `1/(2κ+1)`
by hypothesis, so the covering radius is at least `1/(4κ+2) = 1/(p+1)`. -/
theorem fixed_shell_floor (g κ m : Nat) (hκ : 0 < κ) (hm : 2 * κ + 1 < g ^ (m + 1)) :
    g ^ (m + 1) < (g ^ (m + 1) - 2 * κ) * (2 * κ + 1) := by
  have hle : 2 * κ ≤ g ^ (m + 1) := Nat.le_of_lt (Nat.lt_of_le_of_lt (Nat.le_succ _) hm)
  have h2k : 0 < 2 * κ := Nat.mul_pos (Nat.zero_lt_succ 1) hκ
  have hG : g ^ (m + 1) = (g ^ (m + 1) - 2 * κ) + 2 * κ := (FRC.Nat.sub_add_cancel hle).symm
  generalize hT : g ^ (m + 1) - 2 * κ = t at hG ⊢
  have ht : 1 < t := by
    have h' : 1 + 2 * κ < t + 2 * κ := by rw [Nat.add_comm 1, ← hG]; exact hm
    exact Nat.lt_of_add_lt_add_right h'
  rw [hG, Nat.mul_add, Nat.mul_one, Nat.add_comm (t * (2 * κ)) t]
  refine Nat.add_lt_add_left ?_ t
  calc 2 * κ = 1 * (2 * κ) := (Nat.one_mul _).symm
    _ < t * (2 * κ) := Nat.mul_lt_mul_of_pos_right ht h2k

/-! ### 2:E4 — the Lipschitz budget of a bounded experiment -/

/-- 2:E4 — the budget: `r ≤ L` marked points, each within `d` of its vertex, move an `L`-Lipschitz observable by at
most `L·(r·d) ≤ L·(L·d)`, the bound `L²·δ_p` of the operational theorem in counts. -/
theorem lipschitz_budget (L r d : Nat) (h : r ≤ L) : L * (r * d) ≤ L * (L * d) :=
  Nat.mul_le_mul_left L (Nat.mul_le_mul_right d h)

/-! ### 2:F6 — the exponents of the external transport -/

section transport
variable {p : Nat} [Pos p]

/-- 2:F6 — the external transport in its exponents: the half-period shifts by `−1`, `g^{m+2κ} = −g^m`; the oriented
quarter-turn shifts by three quarters, `i·g^m = g^{m+3κ}` (with `i = −g^κ`, so `χ(i·g^m) = i·χ(g^m)` in the chart);
and the kernel, `(g^j)^r = g^{jr}`. -/
theorem transport_exponents {κ : Nat} {g : Shell p} (F : Shell.Frame p κ g) (m j r : Nat) :
    g ^ (m + 2 * κ) = -(g ^ m) ∧ Shell.Frame.quarterTurn g κ * g ^ m = g ^ (m + 3 * κ) ∧ (g ^ j) ^ r = g ^ (j * r) := by
  have hh : g ^ (m + 2 * κ) = -(g ^ m) := by
    rw [Shell.pow_add, F.half_period, ← Shell.mul_neg, Shell.mul_one]
  refine ⟨hh, ?_, (Shell.pow_mul g j r).symm⟩
  unfold Shell.Frame.quarterTurn
  have h3 : m + 3 * κ = (m + 2 * κ) + κ := by
    rw [Nat.add_assoc, show 3 * κ = 2 * κ + κ from Nat.succ_mul 2 κ]
  rw [h3, Shell.pow_add, hh, ← Shell.neg_mul, ← Shell.neg_mul, Shell.mul_comm]

end transport
/-! ### 2:D6 — the two orientation classes on the laboratory shell -/

set_option maxRecDepth 20000 in
/-- 2:D6 [value] — on `𝔽₁₃` the frame `g = 2` reads `i = 5` (odd: `e^{iπ} = −1`) and the frame `g = 7` reads `i = 8`
(even: `e^{iπ} = +1`); `7 = 2^{11}` with `11 ≡ 3 (mod 4)` flips the orientation. -/
theorem s13_orientation :
    Shell.Frame.quarterTurn (2 : Shell 13) 3 = 5 ∧ Shell.Frame.quarterTurn (7 : Shell 13) 3 = 8 ∧
    ((2 : Shell 13) ^ 5) ^ (5 * 6) = -1 ∧ ((7 : Shell 13) ^ 8) ^ (8 * 6) = 1 ∧
    (2 : Shell 13) ^ 11 = 7 := by decide

end Geometry
end FRC
