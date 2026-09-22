import FrcCore.Orbit
import FrcCore.Sum
import FrcCore.Algebra
import FrcCore.Instances

/-!
# FrcCore.Geometry — 2-geometry rows on the core

2:C2 (the cell counts of the orbital shell and its completion, as identities of natural numbers), 2:E3 (the
fixed-shell bound, every shell, and the `(13, 2)` gap), 2:B4 (the reindexing `m ↦ u·m` preserves the phase
cycle's adjacency exactly when `u ≡ ±1`; the dihedral maps do), 2:C4 (the frame moves the labels of one complex),
and 2:C3 with the automorphism census of B4 decided on the coded complex for `p = 5, 13, 17` (the completion is a
closed surface: every edge in two faces, every vertex link one cycle). No axioms.
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

/-- 2:B4 (Prop. 2.8) — `ρ_u` preserves the adjacency of the phase cycle (`n ≥ 3`) exactly when
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

/-- The rotations `m ↦ m + c` preserve adjacency (with `ρ_{±1}` they generate the dihedral maps of B4). -/
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

end Geometry
end FRC

namespace FRC.Geometry
-- Ledger rows of 2-geometry (generated by make_rows.py from docs/2-geometry/2-geometry-ledger.json; edit the ledger, not this section)
/-- 2:B3 — Primitive generators form one orbit: every generator is $\gen^{u}$ with $u\in\Z_{\p-1}^{\times}$, a torsor for $\operatorname{Aut}(C_{\p-1})$ (Props.~\ref{prop:primitive-orbit}, \ref{prop:no-canonical-e}). -/
theorem row_B3 : (∀ {p : Nat} [FRC.Pos p] {κ : Nat} {g : FRC.Shell p}, FRC.Shell.Frame p κ g → ∀ (h : FRC.Shell p), h.IsPrimitive (p - (1 : Nat)) ↔ ∃ u, u < p - (1 : Nat) ∧ FRC.Shell.Coprime u (p - (1 : Nat)) ∧ h = g ^ u) ∧ FRC.Shell.Coprime (5 : Nat) (12 : Nat) ∧ FRC.Shell.Coprime (7 : Nat) (12 : Nat) ∧ FRC.Shell.Coprime (11 : Nat) (12 : Nat) ∧ ¬FRC.Shell.Coprime (2 : Nat) (12 : Nat) ∧ FRC.Shell.IsPrimitive (6 : FRC.Shell (13 : Nat)) (12 : Nat) ∧ ¬FRC.Shell.IsPrimitive (4 : FRC.Shell (13 : Nat)) (12 : Nat) ∧ (2 : FRC.Shell (13 : Nat)) ^ (5 : Nat) = (6 : FRC.Shell (13 : Nat)) :=
  And.intro @FRC.Shell.Frame.generator_orbit (@FRC.Shell.s13_orbit)
/-- 2:D1 — The half-period: $\gen^{\pi}=-1$ for every primitive $\gen$, $\pi=2\kap$ (Prop.~\ref{prop:half-period}); $2\pi\equiv-1$ (00:C1). -/
theorem row_D1 : ∀ {p : Nat} [FRC.Pos p] {κ : Nat} {g : FRC.Shell p}, FRC.Shell.Frame p κ g → g ^ ((2 : Nat) * κ) = (-1 : FRC.Shell p) :=
  @FRC.Shell.Frame.half_period
/-- 2:D2 — The quarter-turn subgroup $\Qp=\{x:x^{4}=1\}$ is the unique subgroup of order four; $\gen^{\kap}$ has order four with $(\gen^{\kap})^{2}=-1$; $\Qp=\{\pm1,\pm\It\}$ (Def.~\ref{def:quarter-turn-subgroup}, Prop.~\ref{prop:quarter-turn}; 1:B2). -/
theorem row_D2 : ∀ {p : Nat} [FRC.Pos p] {κ : Nat} {g : FRC.Shell p}, FRC.Shell.Frame p κ g → (g ^ κ) ^ (2 : Nat) = (-1 : FRC.Shell p) ∧ (g ^ κ) ^ (4 : Nat) = (1 : FRC.Shell p) :=
  @FRC.Shell.Frame.quarter_turn_order
/-- 2:D3 — The oriented quarter-turn $\It=-\gen^{\kap}=\gen^{-\kap}$, $\It^{2}=-1$, orientation by A2 (Rem.~\ref{rem:observer-canonical-e}); on $\F_{13}(\chron;0,1,2)$: $\It=5$, $-\It=8$, $\pi=6$ [value] (Fig.~\ref{fig:f13-constant-datum}). -/
theorem row_D3 : FRC.Shell.Frame.quarterTurn (2 : FRC.Shell (13 : Nat)) (3 : Nat) = (5 : FRC.Shell (13 : Nat)) ∧ (5 : FRC.Shell (13 : Nat)) * (5 : FRC.Shell (13 : Nat)) = (-1 : FRC.Shell (13 : Nat)) ∧ (-5 : FRC.Shell (13 : Nat)) = (8 : FRC.Shell (13 : Nat)) ∧ (2 : FRC.Shell (13 : Nat)) ^ (6 : Nat) = (-1 : FRC.Shell (13 : Nat)) ∧ (2 : FRC.Shell (13 : Nat)) ^ (5 : Nat) = (6 : FRC.Shell (13 : Nat)) :=
  @FRC.Shell.s13_datum
/-- 2:D5 — Orientation classes: for $\gen'=\gen^{u}$, $\It'=-\gen'^{\kap}$ equals $\It$ when $u\equiv1\pmod4$ and $-\It$ when $u\equiv3\pmod4$; the oriented quarter-turn is frame-covariant within one class of generators, not under every generator change. -/
theorem row_D5 : ∀ {p : Nat} [FRC.Pos p] {κ : Nat} {g : FRC.Shell p}, FRC.Shell.Frame p κ g → ∀ (u : Nat), (u % (4 : Nat) = (1 : Nat) → -(g ^ u) ^ κ = -g ^ κ) ∧ (u % (4 : Nat) = (3 : Nat) → -(g ^ u) ^ κ = - -g ^ κ) :=
  @FRC.Shell.Frame.orientation_class
/-- 2:D6 — The Euler identity on the shell: $\eu^{\It\pi}=\gen^{2\kap\It^{2}}=(-1)^{\It}$, equal to $-1$ exactly when the representative of $\It$ is odd (00:C14); the oriented frames of a shell are those with $-\gen^{\kap}$ odd --- on $\F_{13}$, $\gen=2$ ($\It=5$) is one, on $\F_{17}$, $\gen=3$ ($\It=4$) is not. -/
theorem row_D6 : (∀ {p : Nat} [FRC.Pos p] {κ : Nat} {g : FRC.Shell p}, FRC.Shell.Frame p κ g → ∀ (i : Nat), (g ^ i) ^ (i * ((2 : Nat) * κ)) = if i % (2 : Nat) = (0 : Nat) then (1 : FRC.Shell p) else (-1 : FRC.Shell p)) ∧ FRC.Shell.Frame.quarterTurn (3 : FRC.Shell (17 : Nat)) (4 : Nat) = (4 : FRC.Shell (17 : Nat)) ∧ FRC.Shell.Frame.quarterTurn (6 : FRC.Shell (17 : Nat)) (4 : Nat) = (13 : FRC.Shell (17 : Nat)) ∧ ((3 : FRC.Shell (17 : Nat)) ^ (4 : Nat)) ^ ((4 : Nat) * (8 : Nat)) = (1 : FRC.Shell (17 : Nat)) ∧ ((6 : FRC.Shell (17 : Nat)) ^ (13 : Nat)) ^ ((13 : Nat) * (8 : Nat)) = (-1 : FRC.Shell (17 : Nat)) ∧ (3 : FRC.Shell (17 : Nat)) ^ (15 : Nat) = (6 : FRC.Shell (17 : Nat)) :=
  And.intro @FRC.Shell.Frame.euler_identity (@FRC.Shell.s17_orientation)
/-- 2:D7 — Negation $R(x)=-x$ and inversion $I(x)=x^{-1}$ are commuting involutions; off $\Qp$ the $\langle R,I\rangle$-orbit $\{x,-x,x^{-1},-x^{-1}\}$ has four elements, and $\Fpx\setminus\Qp$ splits into $\kap-1$ such orbits (Props.~\ref{prop:shell-negation}, \ref{prop:k4-shell}; 1:B2). -/
theorem row_D7 : (∀ {p : Nat} [FRC.Pos p] {κ : Nat} {g : FRC.Shell p}, FRC.Shell.Frame p κ g → ∀ {x y : FRC.Shell p}, x * y = (1 : FRC.Shell p) → x ^ (4 : Nat) ≠ (1 : FRC.Shell p) → x ≠ -x ∧ x ≠ y ∧ x ≠ -y ∧ -x ≠ y ∧ -x ≠ -y ∧ y ≠ -y) ∧ (∀ {p : Nat} [FRC.Pos p] {κ : Nat} {g : FRC.Shell p}, FRC.Shell.Frame p κ g → ∀ {x : FRC.Shell p}, x ≠ (0 : FRC.Shell p) → x ^ (4 : Nat) ≠ (1 : FRC.Shell p) → ∃ r, (1 : Nat) ≤ r ∧ r < κ ∧ FRC.Shell.Frame.InOrbit (g ^ r) x) ∧ ∀ {p : Nat} [FRC.Pos p] {κ : Nat} {g : FRC.Shell p}, FRC.Shell.Frame p κ g → ∀ {r r' : Nat}, (1 : Nat) ≤ r → r < κ → (1 : Nat) ≤ r' → r' < κ → ∀ {x : FRC.Shell p}, FRC.Shell.Frame.InOrbit (g ^ r) x → FRC.Shell.Frame.InOrbit (g ^ r') x → r = r' :=
  And.intro @FRC.Shell.Frame.klein_orbit_four (And.intro @FRC.Shell.Frame.orbit_rep (@FRC.Shell.Frame.orbit_rep_unique))
/-- 2:E3 — Fixed-shell refinement is bounded: with $m=\lfloor\log_{\gen}(2\kap+1)\rfloor$ no point $x/\gen^{n}$, $|x|\le2\kap$, lies in $(\max(1-\gen^{-m},2\kap\gen^{-m-1}),1)$ at any depth, so the covering radius of the scale grid in $[0,1]$ is $\ge\tfrac12\min(\gen^{-m},1-2\kap\gen^{-m-1})$ for every $N$: $1/8$ at $(13,2)$, $5/22$ at $(13,11)$. -/
theorem row_E3 : (∀ (g κ m n x : Nat), (2 : Nat) ≤ g → x ≤ (2 : Nat) * κ → x < g ^ n → x * g ^ m + g ^ n ≤ g ^ m * g ^ n ∨ x * g ^ (m + (1 : Nat)) ≤ (2 : Nat) * κ * g ^ n) ∧ ∀ (n x : Nat), x ≤ (6 : Nat) → ¬((3 : Nat) * (2 : Nat) ^ n < (4 : Nat) * x ∧ x < (2 : Nat) ^ n) :=
  And.intro @FRC.Geometry.fixed_shell_bound (@FRC.Geometry.fixed_shell_gap)
/-- 2:F1 — $\gen$ is a principal $n$-th root of unity, $n=\p-1$: $\gen^{n}=1$, $\sum_{j<n}\gen^{jk}=0$ for $0<k<n$, and $n^{-1}=-1$ in $\Fp$ (Prop.~\ref{prop:principal-root}; $2\pi\equiv-1$). -/
theorem row_F1 : ∀ {p : Nat} [FRC.Pos p] {κ : Nat} {g : FRC.Shell p}, FRC.Shell.Frame p κ g → ∀ (k : Nat), (0 : Nat) < k → k < p - (1 : Nat) → g ^ (p - (1 : Nat)) = (1 : FRC.Shell p) ∧ FRC.Shell.sumRange (fun j => (g ^ k) ^ j) (p - (1 : Nat)) = (0 : FRC.Shell p) ∧ FRC.Shell.ofNat (p - (1 : Nat)) = (-1 : FRC.Shell p) :=
  @FRC.Shell.Frame.principal_root
/-- 2:F3 — Inversion: $v_{j}=-\sum_{k<n}\mathcal F_{\gen}(v)_{k}\gen^{-jk}$, i.e.\ $W_{\gen}^{-1}=-(\gen^{-jk})_{jk}=-W_{\gen}J$ (Prop.~\ref{prop:ring-dft-inverse}; 6:B5), exact on every shell. -/
theorem row_F3 : ∀ {p : Nat} [FRC.Pos p] {κ : Nat} {g : FRC.Shell p}, FRC.Shell.Frame p κ g → ∀ {k j : Nat}, k < p - (1 : Nat) → j < p - (1 : Nat) → FRC.Shell.sumRange (fun l => g ^ (l * k) * -g ^ ((p - (1 : Nat) - j) * l)) (p - (1 : Nat)) = if k = j then (1 : FRC.Shell p) else (0 : FRC.Shell p) :=
  @FRC.Shell.Frame.dft_inverse
/-- 2:F4 — Polynomial reading: $\mathcal F_{\gen}(v)_{k}=P_{v}(\gen^{k})$ with $P_{v}=\sum_{j}v_{j}X^{j}$; the transform exchanges coefficients with values on the phase cycle (Prop.~\ref{prop:polynomial-form}). -/
theorem row_F4 : ∀ {p : Nat} [FRC.Pos p] (g : FRC.Shell p) (n : Nat) (v : Nat → FRC.Shell p) (k : Nat), FRC.Shell.Frame.dft g n v k = FRC.Shell.Frame.polyEval n v (g ^ k) :=
  @FRC.Shell.Frame.dft_eq_polyEval
/-- 2:F5 — Covariance under generator change: for $\gen'=\gen^{u}$, $v^{(\gen')}_{j}=v^{(\gen)}_{uj}$ and $\mathcal F_{\gen'}(v^{(\gen')})=\mathcal F_{\gen}(v^{(\gen)})$ (Prop.~\ref{prop:ring-dft-covariance}). -/
theorem row_F5 : ∀ {p : Nat} [FRC.Pos p] {κ : Nat} {g : FRC.Shell p}, FRC.Shell.Frame p κ g → ∀ {u : Nat}, FRC.Shell.Coprime u (p - (1 : Nat)) → ∀ (v : Nat → FRC.Shell p) (k : Nat), FRC.Shell.Frame.dft (g ^ u) (p - (1 : Nat)) (fun j => v (u * j % (p - (1 : Nat)))) k = FRC.Shell.Frame.dft g (p - (1 : Nat)) v k :=
  @FRC.Shell.Frame.dft_covariance
-- end ledger rows
end FRC.Geometry
