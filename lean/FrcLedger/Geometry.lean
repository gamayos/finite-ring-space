import Mathlib
import FrcLedger.Fourier
import FrcLedger.Algebra

/-!
# 2-geometry — the ledger rows in Lean (2026-09-17)

Rows of the predicate ledger of *Geometry and Constants in Finite Ring Continuum* (Symmetry 2026, 18, 751;
tree `2-geometry-20260706`). Compiled 17 Sep 2026, standard axioms only (`axioms.log`). Every universal statement is over an
arbitrary finite field `F` with `Fintype.card F = 4κ + 1` (the shell) and a primitive root `g`; the cell counts
are integer identities; the fixed-shell bound is decided over `ℚ` (the `(13, 2)` instance over `ℕ`); the
Fourier inversion is the matrix identity `W · (−W J) = 1` on `Fin (p − 1)`, from the relations of `FrcLedger.Fourier`.
-/

namespace FRC.Geometry

open Finset

section shell

variable {F : Type*} [Field F] [Fintype F]

/-- 2:D1 (Prop. 4.1, the shell half-period): `g^π = −1` for `π = 2κ` and every primitive root `g`. -/
theorem half_period (κ : ℕ) (hκ : Fintype.card F = 4 * κ + 1) (g : F)
    (hg : IsPrimitiveRoot g (Fintype.card F - 1)) : g ^ (2 * κ) = -1 := by
  have h := FRC.Fourier.quarter_turn_sq κ hκ g hg
  have : (-(g ^ κ)) ^ 2 = g ^ (2 * κ) := by ring
  rwa [this] at h

/-- 2:D2 (Prop. 4.3, the quarter-turn structure): `i = −g^κ` squares to `−1`, so `g^κ` has order four. -/
theorem quarter_turn_order (κ : ℕ) (hκ : Fintype.card F = 4 * κ + 1) (g : F)
    (hg : IsPrimitiveRoot g (Fintype.card F - 1)) :
    (g ^ κ) ^ 2 = -1 ∧ (g ^ κ) ^ 4 = 1 := by
  have h := FRC.Fourier.quarter_turn_sq κ hκ g hg
  have h2 : (g ^ κ) ^ 2 = -1 := by rw [← h]; ring
  refine ⟨h2, ?_⟩
  rw [show (4 : ℕ) = 2 * 2 by norm_num, pow_mul, h2]; ring

/-- 2:D5 (Remark 4.11 — the orientation classes): under `g' = g^u` the oriented quarter-turn
`i' = −g'^κ` equals `i = −g^κ` when `u ≡ 1 (mod 4)` and `−i` when `u ≡ 3 (mod 4)`. -/
theorem orientation_class (κ : ℕ) (hκ : Fintype.card F = 4 * κ + 1) (g : F)
    (hg : IsPrimitiveRoot g (Fintype.card F - 1)) (u : ℕ) :
    (u % 4 = 1 → -((g ^ u) ^ κ) = -(g ^ κ)) ∧ (u % 4 = 3 → -((g ^ u) ^ κ) = -(-(g ^ κ))) := by
  have h4 : (g ^ κ) ^ 4 = 1 := (quarter_turn_order κ hκ g hg).2
  have h2 : (g ^ κ) ^ 2 = -1 := (quarter_turn_order κ hκ g hg).1
  have key : (g ^ u) ^ κ = (g ^ κ) ^ u := by rw [← pow_mul, ← pow_mul, mul_comm]
  have hu : (g ^ κ) ^ u = (g ^ κ) ^ (u % 4) := by
    conv_lhs => rw [← Nat.mod_add_div u 4, pow_add, pow_mul, h4, one_pow, mul_one]
  constructor
  · intro h1; rw [key, hu, h1, pow_one]
  · intro h3; rw [key, hu, h3, show (3 : ℕ) = 2 + 1 by norm_num, pow_add, h2, pow_one]; ring

/-- 2:D6 (the Euler identity on the shell, master C14): with `e = g^i` and `π = 2κ`, `e^(iπ) = (−1)^i`
for any integer reading `i` of the quarter-turn — `−1` exactly when that reading is odd. -/
theorem euler_identity (κ : ℕ) (hκ : Fintype.card F = 4 * κ + 1) (g : F)
    (hg : IsPrimitiveRoot g (Fintype.card F - 1)) (i : ℕ) :
    (g ^ i) ^ (i * (2 * κ)) = (-1 : F) ^ i := by
  have hπ := half_period κ hκ g hg
  rw [← pow_mul, show i * (i * (2 * κ)) = (2 * κ) * (i * i) by ring, pow_mul, hπ]
  rcases Nat.even_or_odd i with he | ho
  · rw [he.neg_one_pow, (he.mul_right i).neg_one_pow]
  · rw [ho.neg_one_pow, (ho.mul ho).neg_one_pow]

/-- 2:B3 (Props. 2.7, 4.5, the primitive generators form one orbit): the primitive roots of unity of order
`n = card F − 1` are exactly the `g^u` with `u < n` coprime to `n`. -/
theorem generator_orbit (g : F) (hg : IsPrimitiveRoot g (Fintype.card F - 1)) (h : F) :
    IsPrimitiveRoot h (Fintype.card F - 1) ↔
      ∃ u, u < Fintype.card F - 1 ∧ Nat.Coprime u (Fintype.card F - 1) ∧ h = g ^ u := by
  have hn : 0 < Fintype.card F - 1 := by have := Fintype.one_lt_card (α := F); omega
  have : NeZero (Fintype.card F - 1) := ⟨by omega⟩
  constructor
  · intro hh
    obtain ⟨u, hu, rfl⟩ := hg.eq_pow_of_pow_eq_one hh.pow_eq_one
    exact ⟨u, hu, (hg.pow_iff_coprime hn u).mp hh, rfl⟩
  · rintro ⟨u, -, hcop, rfl⟩
    exact (hg.pow_iff_coprime hn u).mpr hcop

/-- 2:F1 (Prop. 6.1, root-of-unity facts): `Σ_j g^{jk} = 0` for `0 < k < n`, and `n = card F − 1` reads as
`−1` in `F`. -/
theorem principal_root (g : F) (hg : IsPrimitiveRoot g (Fintype.card F - 1)) (k : ℕ) (hk0 : 0 < k)
    (hk : k < Fintype.card F - 1) :
    (∑ j ∈ range (Fintype.card F - 1), (g ^ k) ^ j = 0) ∧ ((Fintype.card F - 1 : ℕ) : F) = -1 := by
  refine ⟨?_, FRC.Fourier.natCast_card_pred_eq_neg_one⟩
  have hne : g ^ k ≠ 1 := fun h => by
    have := hg.pow_eq_one_iff_dvd k |>.mp h
    exact absurd (Nat.le_of_dvd hk0 this) (not_le.mpr hk)
  have hpow : (g ^ k) ^ (Fintype.card F - 1) = 1 := by
    rw [← pow_mul, mul_comm, pow_mul, hg.pow_eq_one, one_pow]
  have h := geom_sum_mul (g ^ k) (Fintype.card F - 1)
  rw [hpow, sub_self] at h
  exact (mul_eq_zero.1 h).resolve_right (sub_ne_zero.2 hne)

/-- 2:F3 (Prop. 6.3, inversion): on every shell the inverse of the Fourier matrix `W_g` (`W k j = g^{jk}`) is
`−W_g J`, whose entry at `(k, j)` is `−g^{−jk}`: `W_g · (−W_g J) = 1`. -/
theorem dft_inverse (κ : ℕ) (hκ : Fintype.card F = 4 * κ + 1) (g : F)
    (hg : IsPrimitiveRoot g (Fintype.card F - 1)) :
    haveI : NeZero (Fintype.card F - 1) := ⟨by have := Fintype.one_lt_card (α := F); omega⟩
    (FRC.Fourier.W g : Matrix (Fin (Fintype.card F - 1)) (Fin (Fintype.card F - 1)) F) *
        (-(FRC.Fourier.W g * FRC.Fourier.J)) = 1 ∧
    ∀ k j : Fin (Fintype.card F - 1),
      (-(FRC.Fourier.W g * FRC.Fourier.J) :
        Matrix (Fin (Fintype.card F - 1)) (Fin (Fintype.card F - 1)) F) k j
        = -(g ^ ((j : ℕ) * (k : ℕ)))⁻¹ := by
  have : NeZero (Fintype.card F - 1) := ⟨by have := Fintype.one_lt_card (α := F); omega⟩
  obtain ⟨hW, -, -, -⟩ := FRC.Fourier.shell_relations κ hκ g hg
  constructor
  · rw [mul_neg, ← mul_assoc, ← sq, hW, neg_mul, neg_neg, ← sq, FRC.Fourier.J_sq]
  · intro k j
    rw [Matrix.neg_apply, Matrix.mul_apply]
    simp only [FRC.Fourier.W_apply, FRC.Fourier.J_apply, mul_ite, mul_one, mul_zero]
    rw [Finset.sum_eq_single (-j)]
    · rw [ite_eq_left (by rw [neg_neg]), pow_mul, FRC.Fourier.pow_neg_val hg.pow_eq_one j, inv_pow,
        ← pow_mul]
    · intro x _ hx
      rw [ite_eq_right (fun h => hx (by rw [h, neg_neg]))]
    · intro h; exact absurd (Finset.mem_univ _) h

end shell

/-- 2:C2 (Remark 3.4, the counts): for the orbital shell, `χ = V − E + F = 1`; for its completion, `χ = 2`
(`π = 2κ`, `n = p − 1`), as integer identities. -/
theorem euler_characteristic (π n : ℤ) :
    (π * n + 1) - 2 * π * n + π * n = 1 ∧ ((π - 1) * n + 2) - (2 * π - 1) * n + π * n = 2 := by
  constructor <;> ring

/-- 2:E3 (the fixed-shell gap of Prop. 5.5 at `p = 13`, `g = 2`, `H = 6`): no grid point `x / 2^n`
with `0 ≤ x ≤ 6` lies strictly between `3/4` and `1`, at any depth `n` — the covering radius of the
fixed-shell refinement in `[0, 1]` is at least `1/8` for every `N`. -/
theorem fixed_shell_gap (n x : ℕ) (hx : x ≤ 6) : ¬ (3 * 2 ^ n < 4 * x ∧ x < 2 ^ n) := by
  rintro ⟨h1, h2⟩
  have hn : n < 3 := by
    by_contra hn; push Not at hn
    have := Nat.pow_le_pow_right (by norm_num : 0 < 2) hn
    omega
  interval_cases n <;> omega

/-- The same, read in `ℚ`: no `x / 2^n` with `x ≤ 6` lies in the open interval `(3/4, 1)`. -/
theorem fixed_shell_gap_rat (n x : ℕ) (hx : x ≤ 6) :
    ¬ ((3 / 4 : ℚ) < x / 2 ^ n ∧ (x : ℚ) / 2 ^ n < 1) := by
  rintro ⟨h1, h2⟩
  have h2n : (0 : ℚ) < 2 ^ n := by positivity
  rw [lt_div_iff₀ h2n] at h1
  rw [div_lt_iff₀ h2n] at h2
  apply fixed_shell_gap n x hx
  constructor
  · have : (3 * 2 ^ n : ℚ) < 4 * x := by linarith
    exact_mod_cast this
  · have : (x : ℚ) < 2 ^ n := by linarith
    exact_mod_cast this

/-- 2:E3 (the fixed-shell bound, every shell): for any depth cut `m`, every grid point `x / g^n` with
`x ≤ 2κ` that lies below `1` is at most `max (1 − g^{−m}) (2κ · g^{−(m+1)})`; with `m = ⌊log_g(2κ+1)⌋`
that bound is below `1` (`fixed_shell_bound_lt_one`), so the interval above it is free at every depth
and the covering radius of the fixed-shell refinement in `[0, 1]` is bounded below independently of `N`. -/
theorem fixed_shell_bound (g κ m n x : ℕ) (hg : 2 ≤ g) (hx : x ≤ 2 * κ)
    (hlt : (x : ℚ) / (g : ℚ) ^ n < 1) :
    (x : ℚ) / (g : ℚ) ^ n ≤ max (1 - 1 / (g : ℚ) ^ m) (2 * (κ : ℚ) / (g : ℚ) ^ (m + 1)) := by
  have hg0 : (0 : ℚ) < g := by exact_mod_cast (by omega : 0 < g)
  have hg1 : (1 : ℚ) ≤ g := by exact_mod_cast (by omega : 1 ≤ g)
  have hgn : (0 : ℚ) < (g : ℚ) ^ n := pow_pos hg0 n
  rcases le_or_gt n m with hnm | hnm
  · refine le_max_of_le_left ?_
    have hxn : x < g ^ n := by
      have h := (div_lt_one hgn).mp hlt
      exact_mod_cast h
    have hx1 : (x : ℚ) ≤ (g : ℚ) ^ n - 1 := by
      have h : ((x + 1 : ℕ) : ℚ) ≤ ((g ^ n : ℕ) : ℚ) := by exact_mod_cast hxn
      push_cast at h; linarith
    have hgm : (0 : ℚ) < (g : ℚ) ^ m := pow_pos hg0 m
    have hnm' : (g : ℚ) ^ n ≤ (g : ℚ) ^ m := pow_le_pow_right₀ hg1 hnm
    have hq : (g : ℚ) ^ n / (g : ℚ) ^ m ≤ 1 := (div_le_one hgm).mpr hnm'
    rw [div_le_iff₀ hgn]
    calc (x : ℚ) ≤ (g : ℚ) ^ n - 1 := hx1
      _ ≤ (g : ℚ) ^ n - (g : ℚ) ^ n / (g : ℚ) ^ m := by linarith
      _ = (1 - 1 / (g : ℚ) ^ m) * (g : ℚ) ^ n := by ring
  · refine le_max_of_le_right ?_
    have hgm1 : (0 : ℚ) < (g : ℚ) ^ (m + 1) := pow_pos hg0 _
    have hpow : (g : ℚ) ^ (m + 1) ≤ (g : ℚ) ^ n := pow_le_pow_right₀ hg1 hnm
    have hx' : (x : ℚ) ≤ 2 * (κ : ℚ) := by exact_mod_cast hx
    calc (x : ℚ) / (g : ℚ) ^ n ≤ (2 * (κ : ℚ)) / (g : ℚ) ^ n :=
          div_le_div_of_nonneg_right hx' hgn.le
      _ ≤ (2 * (κ : ℚ)) / (g : ℚ) ^ (m + 1) :=
          div_le_div_of_nonneg_left (by positivity) hgm1 hpow

/-- The cut `m = ⌊log_g(2κ+1)⌋` (`2κ + 1 < g^(m+1)`) puts the bound of `fixed_shell_bound` strictly below `1`. -/
theorem fixed_shell_bound_lt_one (g κ m : ℕ) (hg : 2 ≤ g) (hm : 2 * κ + 1 < g ^ (m + 1)) :
    max (1 - 1 / (g : ℚ) ^ m) (2 * (κ : ℚ) / (g : ℚ) ^ (m + 1)) < 1 := by
  have hg0 : (0 : ℚ) < g := by exact_mod_cast (by omega : 0 < g)
  have hgm1 : (0 : ℚ) < (g : ℚ) ^ (m + 1) := pow_pos hg0 _
  refine max_lt ?_ ?_
  · have : (0 : ℚ) < 1 / (g : ℚ) ^ m := by positivity
    linarith
  · rw [div_lt_one hgm1]
    have h : ((2 * κ : ℕ) : ℚ) < ((g ^ (m + 1) : ℕ) : ℚ) := by exact_mod_cast (by omega : 2 * κ < g ^ (m + 1))
    push_cast at h; exact h

-- Ledger rows of 2-geometry (generated by make_rows.py from docs/2-geometry/2-geometry-ledger.json; edit the ledger, not this section)
/-- 2:B3 — Primitive generators form one orbit: every generator is $\gen^{u}$ with $u\in\Z_{\p-1}^{\times}$, a torsor for $\operatorname{Aut}(C_{\p-1})$ (Props.~\ref{prop:primitive-orbit}, \ref{prop:no-canonical-e}). -/
theorem row_B3 : ∀ {F : Type u_1} [Field F] [Fintype F] (g : F), IsPrimitiveRoot g (Fintype.card F - (1 : ℕ)) → ∀ (h : F), IsPrimitiveRoot h (Fintype.card F - (1 : ℕ)) ↔ ∃ u < Fintype.card F - (1 : ℕ), u.Coprime (Fintype.card F - (1 : ℕ)) ∧ h = g ^ u :=
  @FRC.Geometry.generator_orbit
/-- 2:C2 — Counts: $|V|=\pi(\p-1)+1$, $|E|=2\pi(\p-1)$, $|F|=\pi(\p-1)$, $\chi(\Sp)=1$; the completion has $(\pi-1)(\p-1)+2$ vertices, $(2\pi-1)(\p-1)$ edges, $\pi(\p-1)$ faces, $\chi=2$ (Rem.~\ref{rem:cell-counts}). -/
theorem row_C2 : ∀ (π n : ℤ), π * n + (1 : ℤ) - (2 : ℤ) * π * n + π * n = (1 : ℤ) ∧ (π - (1 : ℤ)) * n + (2 : ℤ) - ((2 : ℤ) * π - (1 : ℤ)) * n + π * n = (2 : ℤ) :=
  @FRC.Geometry.euler_characteristic
/-- 2:D1 — The half-period: $\gen^{\pi}=-1$ for every primitive $\gen$, $\pi=2\kap$ (Prop.~\ref{prop:half-period}); $2\pi\equiv-1$ (00:C1). -/
theorem row_D1 : ∀ {F : Type u_1} [Field F] [Fintype F] (κ : ℕ), Fintype.card F = (4 : ℕ) * κ + (1 : ℕ) → ∀ (g : F), IsPrimitiveRoot g (Fintype.card F - (1 : ℕ)) → g ^ ((2 : ℕ) * κ) = (-1 : F) :=
  @FRC.Geometry.half_period
/-- 2:D2 — The quarter-turn subgroup $\Qp=\{x:x^{4}=1\}$ is the unique subgroup of order four; $\gen^{\kap}$ has order four with $(\gen^{\kap})^{2}=-1$; $\Qp=\{\pm1,\pm\It\}$ (Def.~\ref{def:quarter-turn-subgroup}, Prop.~\ref{prop:quarter-turn}; 1:B2). -/
theorem row_D2 : ∀ {F : Type u_1} [Field F] [Fintype F] (κ : ℕ), Fintype.card F = (4 : ℕ) * κ + (1 : ℕ) → ∀ (g : F), IsPrimitiveRoot g (Fintype.card F - (1 : ℕ)) → (g ^ κ) ^ (2 : ℕ) = (-1 : F) ∧ (g ^ κ) ^ (4 : ℕ) = (1 : F) :=
  @FRC.Geometry.quarter_turn_order
/-- 2:D5 — Orientation classes: for $\gen'=\gen^{u}$, $\It'=-\gen'^{\kap}$ equals $\It$ when $u\equiv1\pmod4$ and $-\It$ when $u\equiv3\pmod4$; the oriented quarter-turn is frame-covariant within one class of generators, not under every generator change. -/
theorem row_D5 : ∀ {F : Type u_1} [Field F] [Fintype F] (κ : ℕ), Fintype.card F = (4 : ℕ) * κ + (1 : ℕ) → ∀ (g : F), IsPrimitiveRoot g (Fintype.card F - (1 : ℕ)) → ∀ (u : ℕ), (u % (4 : ℕ) = (1 : ℕ) → -(g ^ u) ^ κ = -g ^ κ) ∧ (u % (4 : ℕ) = (3 : ℕ) → -(g ^ u) ^ κ = - -g ^ κ) :=
  @FRC.Geometry.orientation_class
/-- 2:D6 — The Euler identity on the shell: $\eu^{\It\pi}=\gen^{2\kap\It^{2}}=(-1)^{\It}$, equal to $-1$ exactly when the representative of $\It$ is odd (00:C14); the oriented frames of a shell are those with $-\gen^{\kap}$ odd --- on $\F_{13}$, $\gen=2$ ($\It=5$) is one, on $\F_{17}$, $\gen=3$ ($\It=4$) is not. -/
theorem row_D6 : ∀ {F : Type u_1} [Field F] [Fintype F] (κ : ℕ), Fintype.card F = (4 : ℕ) * κ + (1 : ℕ) → ∀ (g : F), IsPrimitiveRoot g (Fintype.card F - (1 : ℕ)) → ∀ (i : ℕ), (g ^ i) ^ (i * ((2 : ℕ) * κ)) = (-1 : F) ^ i :=
  @FRC.Geometry.euler_identity
/-- 2:E3 — Fixed-shell refinement is bounded: with $m=\lfloor\log_{\gen}(2\kap+1)\rfloor$ no point $x/\gen^{n}$, $|x|\le2\kap$, lies in $(\max(1-\gen^{-m},2\kap\gen^{-m-1}),1)$ at any depth, so the covering radius of the scale grid in $[0,1]$ is $\ge\tfrac12\min(\gen^{-m},1-2\kap\gen^{-m-1})$ for every $N$: $1/8$ at $(13,2)$, $5/22$ at $(13,11)$. -/
theorem row_E3 : ∀ (g κ m n x : ℕ), (2 : ℕ) ≤ g → x ≤ (2 : ℕ) * κ → ↑x / ↑g ^ n < (1 : ℚ) → ↑x / ↑g ^ n ≤ max ((1 : ℚ) - (1 : ℚ) / ↑g ^ m) ((2 : ℚ) * ↑κ / ↑g ^ (m + (1 : ℕ))) :=
  @FRC.Geometry.fixed_shell_bound
/-- 2:F1 — $\gen$ is a principal $n$-th root of unity, $n=\p-1$: $\gen^{n}=1$, $\sum_{j<n}\gen^{jk}=0$ for $0<k<n$, and $n^{-1}=-1$ in $\Fp$ (Prop.~\ref{prop:principal-root}; $2\pi\equiv-1$). -/
theorem row_F1 : ∀ {F : Type u_1} [Field F] [Fintype F] (g : F), IsPrimitiveRoot g (Fintype.card F - (1 : ℕ)) → ∀ (k : ℕ), (0 : ℕ) < k → k < Fintype.card F - (1 : ℕ) → ∑ j ∈ Finset.range (Fintype.card F - (1 : ℕ)), (g ^ k) ^ j = (0 : F) ∧ ↑(Fintype.card F - (1 : ℕ)) = (-1 : F) :=
  @FRC.Geometry.principal_root
set_option linter.defProp false in
/-- 2:F3 — Inversion: $v_{j}=-\sum_{k<n}\mathcal F_{\gen}(v)_{k}\gen^{-jk}$, i.e.\ $W_{\gen}^{-1}=-(\gen^{-jk})_{jk}=-W_{\gen}J$ (Prop.~\ref{prop:ring-dft-inverse}; 6:B5), exact on every shell. -/
def row_F3 := @FRC.Geometry.dft_inverse
-- end ledger rows

end FRC.Geometry
