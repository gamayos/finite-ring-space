import Mathlib
import FrcMathlib.Theme.Geometry
import FrcMathlib.Keys.Geometry

/-!
# FrcMathlib.Geometry — 2-geometry on Mathlib (the paper module)

The declarations moved to the geometry theme's `Theme/Geometry.lean` (namespace `FRC.GeometryML`) on 6 November 2026.
This module keeps the names the ledgers cite, `FRC.Geometry.<name>`, as aliases with their statements, and the
predicates of 2-geometry. Every docstring opens with the ledger rows the declaration decides.
-/

namespace FRC.Geometry

universe u_1 u_2 u_3

/-! ## Old names (moved to the geometry theme's `Theme/Geometry.lean`, 6 November 2026) -/

/-- 2:B3 (Props. 2.7, 4.5, the primitive generators form one orbit): the primitive roots of unity of order `n = card F − 1` are exactly the `g^u` with `u < n` coprime to `n`. -/
theorem generator_orbit : ∀ {F : Type u_1} [Field F] [Fintype F] (g : F), IsPrimitiveRoot g (Fintype.card F - (1 : ℕ)) → ∀ (h : F), IsPrimitiveRoot h (Fintype.card F - (1 : ℕ)) ↔ ∃ u < Fintype.card F - (1 : ℕ), u.Coprime (Fintype.card F - (1 : ℕ)) ∧ h = g ^ u :=
  @FRC.GeometryML.generator_orbit
/-- 2:C2 (Remark 3.4, the counts): for the orbital shell, `χ = V − E + F = 1`; for its completion, `χ = 2` (`π = 2κ`, `n = p − 1`), as integer identities. -/
theorem euler_characteristic : ∀ (π n : ℤ), π * n + (1 : ℤ) - (2 : ℤ) * π * n + π * n = (1 : ℤ) ∧ (π - (1 : ℤ)) * n + (2 : ℤ) - ((2 : ℤ) * π - (1 : ℤ)) * n + π * n = (2 : ℤ) :=
  @FRC.GeometryML.euler_characteristic
/-- 2:D1 (Prop. 4.1, the shell half-period): `g^π = −1` for `π = 2κ` and every primitive root `g`. -/
theorem half_period : ∀ {F : Type u_1} [Field F] [Fintype F] (κ : ℕ), Fintype.card F = (4 : ℕ) * κ + (1 : ℕ) → ∀ (g : F), IsPrimitiveRoot g (Fintype.card F - (1 : ℕ)) → g ^ ((2 : ℕ) * κ) = (-1 : F) :=
  @FRC.GeometryML.half_period
/-- 2:D2 (Prop. 4.3, the quarter-turn structure): `i = −g^κ` squares to `−1`, so `g^κ` has order four. -/
theorem quarter_turn_order : ∀ {F : Type u_1} [Field F] [Fintype F] (κ : ℕ), Fintype.card F = (4 : ℕ) * κ + (1 : ℕ) → ∀ (g : F), IsPrimitiveRoot g (Fintype.card F - (1 : ℕ)) → (g ^ κ) ^ (2 : ℕ) = (-1 : F) ∧ (g ^ κ) ^ (4 : ℕ) = (1 : F) :=
  @FRC.GeometryML.quarter_turn_order
/-- 2:D5 (Remark 4.11 — the orientation classes): under `g' = g^u` the oriented quarter-turn `i' = −g'^κ` equals `i = −g^κ` when `u ≡ 1 (mod 4)` and `−i` when `u ≡ 3 (mod 4)`. -/
theorem orientation_class : ∀ {F : Type u_1} [Field F] [Fintype F] (κ : ℕ), Fintype.card F = (4 : ℕ) * κ + (1 : ℕ) → ∀ (g : F), IsPrimitiveRoot g (Fintype.card F - (1 : ℕ)) → ∀ (u : ℕ), (u % (4 : ℕ) = (1 : ℕ) → -(g ^ u) ^ κ = -g ^ κ) ∧ (u % (4 : ℕ) = (3 : ℕ) → -(g ^ u) ^ κ = - -g ^ κ) :=
  @FRC.GeometryML.orientation_class
/-- 2:D6 (the Euler identity on the shell, master C14): with `e = g^i` and `π = 2κ`, `e^(iπ) = (−1)^i` for any integer reading `i` of the quarter-turn — `−1` exactly when that reading is odd. -/
theorem euler_identity : ∀ {F : Type u_1} [Field F] [Fintype F] (κ : ℕ), Fintype.card F = (4 : ℕ) * κ + (1 : ℕ) → ∀ (g : F), IsPrimitiveRoot g (Fintype.card F - (1 : ℕ)) → ∀ (i : ℕ), (g ^ i) ^ (i * ((2 : ℕ) * κ)) = (-1 : F) ^ i :=
  @FRC.GeometryML.euler_identity
/-- 2:E3 (the fixed-shell bound, every shell): for any depth cut `m`, every grid point `x / g^n` with `x ≤ 2κ` that lies below `1` is at most `max (1 − g^{−m}) (2κ · g^{−(m+1)})`; with `m = ⌊log_g(2κ+1)⌋` that bound is below `1` (`fixed_shell_bound_lt_one`), so the interval above it is free at every depth and the covering radius of the fixed-shell refinement in `[0, 1]` is bounded below independently of `N`. -/
theorem fixed_shell_bound : ∀ (g κ m n x : ℕ), (2 : ℕ) ≤ g → x ≤ (2 : ℕ) * κ → ↑x / ↑g ^ n < (1 : ℚ) → ↑x / ↑g ^ n ≤ max ((1 : ℚ) - (1 : ℚ) / ↑g ^ m) ((2 : ℚ) * ↑κ / ↑g ^ (m + (1 : ℕ))) :=
  @FRC.GeometryML.fixed_shell_bound
/-- 2:F1 (Prop. 6.1, root-of-unity facts): `Σ_j g^{jk} = 0` for `0 < k < n`, and `n = card F − 1` reads as `−1` in `F`. -/
theorem principal_root : ∀ {F : Type u_1} [Field F] [Fintype F] (g : F), IsPrimitiveRoot g (Fintype.card F - (1 : ℕ)) → ∀ (k : ℕ), (0 : ℕ) < k → k < Fintype.card F - (1 : ℕ) → ∑ j ∈ Finset.range (Fintype.card F - (1 : ℕ)), (g ^ k) ^ j = (0 : F) ∧ ↑(Fintype.card F - (1 : ℕ)) = (-1 : F) :=
  @FRC.GeometryML.principal_root
/-- 2:F3 (Prop. 6.3, inversion): on every shell the inverse of the Fourier matrix `W_g` (`W k j = g^{jk}`) is `−W_g J`, whose entry at `(k, j)` is `−g^{−jk}`: `W_g · (−W_g J) = 1`. -/
theorem dft_inverse : ∀ {F : Type u_1} [Field F] [Fintype F] (κ : ℕ), Fintype.card F = 4 * κ + 1 → ∀ (g : F), IsPrimitiveRoot g (Fintype.card F - 1) → haveI : NeZero (Fintype.card F - 1) := ⟨by have := Fintype.one_lt_card (α := F); omega⟩; (FRC.DFT.W g : Matrix (Fin (Fintype.card F - 1)) (Fin (Fintype.card F - 1)) F) * (-(FRC.DFT.W g * FRC.DFT.J)) = 1 ∧ ∀ k j : Fin (Fintype.card F - 1), (-(FRC.DFT.W g * FRC.DFT.J) : Matrix (Fin (Fintype.card F - 1)) (Fin (Fintype.card F - 1)) F) k j = -(g ^ ((j : ℕ) * (k : ℕ)))⁻¹ :=
  @FRC.GeometryML.dft_inverse

-- Ledger predicates of 2-geometry (generated by make_predicates.py from docs/2-geometry/2-geometry-ledger.json; edit the ledger, not this section)
/-- 2:B3 (p02007) — Primitive generators form one orbit: every generator is $\gen^{u}$ with $u\in\Zp^{\times}$, a torsor for $\operatorname{Aut}(C_{\p-1})$. -/
theorem primitive_generators_one_orbit : ∀ {F : Type u_1} [Field F] [Fintype F] (g : F), IsPrimitiveRoot g (Fintype.card F - (1 : ℕ)) → ∀ (h : F), IsPrimitiveRoot h (Fintype.card F - (1 : ℕ)) ↔ ∃ u < Fintype.card F - (1 : ℕ), u.Coprime (Fintype.card F - (1 : ℕ)) ∧ h = g ^ u :=
  @FRC.LedgerML.p02007
/-- 2:C2 (p02010) — Counts: $|V|=\pi(\p-1)+1$, $|E|=2\pi(\p-1)$, $|F|=\pi(\p-1)$, $\chi(\Sp)=1$; the completion has $(\pi-1)(\p-1)+2$ vertices, $(2\pi-1)(\p-1)$ edges, $\pi(\p-1)$ faces, $\chi=2$. -/
theorem cell_counts : ∀ (π n : ℤ), π * n + (1 : ℤ) - (2 : ℤ) * π * n + π * n = (1 : ℤ) ∧ (π - (1 : ℤ)) * n + (2 : ℤ) - ((2 : ℤ) * π - (1 : ℤ)) * n + π * n = (2 : ℤ) :=
  @FRC.LedgerML.p02010
/-- 2:D1 (p02013) — The half-period: $\gen^{\pi}=-1$ for every primitive $\gen$, $\pi=2\kap$; $2\pi\equiv-1$ (00:C1). -/
theorem half_period_is_minus_one : ∀ {F : Type u_1} [Field F] [Fintype F] (κ : ℕ), Fintype.card F = (4 : ℕ) * κ + (1 : ℕ) → ∀ (g : F), IsPrimitiveRoot g (Fintype.card F - (1 : ℕ)) → g ^ ((2 : ℕ) * κ) = (-1 : F) :=
  @FRC.LedgerML.p02013
/-- 2:D2 (p02014) — The quarter-turn subgroup $\Qp=\{x:x^{4}=1\}$ is the unique subgroup of order four; $\gen^{\kap}$ has order four with $(\gen^{\kap})^{2}=-1$; $\Qp=\{\pm1,\pm\im\}$ (1:B2). -/
theorem quarter_turn_subgroup_unique : ∀ {F : Type u_1} [Field F] [Fintype F] (κ : ℕ), Fintype.card F = (4 : ℕ) * κ + (1 : ℕ) → ∀ (g : F), IsPrimitiveRoot g (Fintype.card F - (1 : ℕ)) → (g ^ κ) ^ (2 : ℕ) = (-1 : F) ∧ (g ^ κ) ^ (4 : ℕ) = (1 : F) :=
  @FRC.LedgerML.p02014
/-- 2:D5 (p02017) — Orientation classes: for $\gen'=\gen^{u}$, $\im'=-\gen'^{\kap}$ equals $\im$ when $u\equiv1\pmod4$ and $-\im$ when $u\equiv3\pmod4$; the oriented quarter-turn is frame-covariant within one class of generators, not under every generator change. -/
theorem orientation_classes : ∀ {F : Type u_1} [Field F] [Fintype F] (κ : ℕ), Fintype.card F = (4 : ℕ) * κ + (1 : ℕ) → ∀ (g : F), IsPrimitiveRoot g (Fintype.card F - (1 : ℕ)) → ∀ (u : ℕ), (u % (4 : ℕ) = (1 : ℕ) → -(g ^ u) ^ κ = -g ^ κ) ∧ (u % (4 : ℕ) = (3 : ℕ) → -(g ^ u) ^ κ = - -g ^ κ) :=
  @FRC.LedgerML.p02017
/-- 2:D6 (p02018) — The Euler identity on the shell: $\eu^{\im\pi}=\gen^{2\kap\im^{2}}=(-1)^{\im}$, equal to $-1$ exactly when the representative of $\im$ is odd (00:C14); the oriented frames of a shell are those with $-\gen^{\kap}$ odd --- on $\F_{13}$, $\gen=2$ ($\im=5$) is one and $\gen=7$ ($\im=8$) is not. -/
theorem euler_identity_shell : ∀ {F : Type u_1} [Field F] [Fintype F] (κ : ℕ), Fintype.card F = (4 : ℕ) * κ + (1 : ℕ) → ∀ (g : F), IsPrimitiveRoot g (Fintype.card F - (1 : ℕ)) → ∀ (i : ℕ), (g ^ i) ^ (i * ((2 : ℕ) * κ)) = (-1 : F) ^ i :=
  @FRC.LedgerML.p02018
/-- 2:E3 (p02023) — Fixed-shell refinement is bounded: with $\gen^{m}\le2\kap+1<\gen^{m+1}$ no point $x/\gen^{n}$, $0\le x\le2\kap$, lies in $(\max(1-\gen^{-m},2\kap\gen^{-m-1}),1)$ at any depth, so the covering radius of the scale grids in $[0,1]$ is $\ge\tfrac12\min(\gen^{-m},1-2\kap\gen^{-m-1})\ge1/(\p+1)$: $1/8$ at $(13,2)$, $5/22$ at $(13,11)$. -/
theorem fixed_shell_refinement_bounded : ∀ (g κ m n x : ℕ), (2 : ℕ) ≤ g → x ≤ (2 : ℕ) * κ → ↑x / ↑g ^ n < (1 : ℚ) → ↑x / ↑g ^ n ≤ max ((1 : ℚ) - (1 : ℚ) / ↑g ^ m) ((2 : ℚ) * ↑κ / ↑g ^ (m + (1 : ℕ))) :=
  @FRC.LedgerML.p02023
/-- 2:F1 (p02025) — $\gen$ is a principal $n$-th root of unity, $n=\p-1$: $\gen^{n}=1$, $\sum_{j<n}\gen^{jk}=0$ for $0<k<n$, and $n^{-1}=-1$ in $\Fp$ ($2\pi\equiv-1$). -/
theorem principal_root_of_unity : ∀ {F : Type u_1} [Field F] [Fintype F] (g : F), IsPrimitiveRoot g (Fintype.card F - (1 : ℕ)) → ∀ (k : ℕ), (0 : ℕ) < k → k < Fintype.card F - (1 : ℕ) → ∑ j ∈ Finset.range (Fintype.card F - (1 : ℕ)), (g ^ k) ^ j = (0 : F) ∧ ↑(Fintype.card F - (1 : ℕ)) = (-1 : F) :=
  @FRC.LedgerML.p02025
set_option linter.defProp false in
/-- 2:F3 (p02027) — Inversion: $v_{j}=-\sum_{k<n}\mathcal F_{\gen}(v)_{k}\gen^{-jk}$, i.e.\ $W_{\gen}^{-1}=-(\gen^{-jk})_{jk}=-W_{\gen}J$ (6:B5), exact on every shell. -/
def dft_inversion := @FRC.LedgerML.p02027
-- end ledger predicates

end FRC.Geometry
