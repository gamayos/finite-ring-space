import Mathlib
import FrcMathlib.Theme.Algebra
import FrcMathlib.Theme.Circle
import FrcMathlib.Keys.Algebra
import FrcMathlib.Keys.Chart

/-!
# FrcMathlib.Algebra — 1-algebra on Mathlib (the paper module)

The declarations moved to the algebra theme's `Theme/Algebra.lean` (namespace `FRC.AlgebraML`) on 6 November 2026.
This module keeps the names the ledgers cite, `FRC.Algebra.<name>`, as aliases with their statements, and the
predicates of 1-algebra. Every docstring opens with the ledger rows the declaration decides.
-/

namespace FRC.Algebra

universe u_1 u_2 u_3

/-! ## Old names (moved to the algebra theme's `Theme/Algebra.lean`, 6 November 2026) -/

/-- 1:B2 (Theorem 1, existence clause): on the shell `card F = 4κ+1` a quarter-turn `u` with `u² = −1` exists. Mathlib: `FiniteField.isSquare_neg_one_iff`. -/
theorem quarter_turn_exists : ∀ {F : Type u_1} [Field F] [Fintype F] (κ : ℕ), Fintype.card F = (4 : ℕ) * κ + (1 : ℕ) → ∃ u, u ^ (2 : ℕ) = (-1 : F) :=
  @FRC.AlgebraML.quarter_turn_exists
/-- 1:B2 (Theorem 1, orbit clause), 2:D7: for a unit `x` with `x² ≠ 1` and `x² ≠ −1` the four elements `x, −x, x⁻¹, −x⁻¹` of the Klein-four orbit are pairwise distinct (any field of characteristic `≠ 2`); the structural set `{1, i, −1, −i}` is exactly the complement. -/
theorem klein_orbit_four : ∀ {F : Type u_1} [Field F], (2 : F) ≠ (0 : F) → ∀ (x : F), x ≠ (0 : F) → x ^ (2 : ℕ) ≠ (1 : F) → x ^ (2 : ℕ) ≠ (-1 : F) → x ≠ -x ∧ x ≠ x⁻¹ ∧ x ≠ -x⁻¹ ∧ -x ≠ x⁻¹ ∧ -x ≠ -x⁻¹ ∧ x⁻¹ ≠ -x⁻¹ :=
  @FRC.AlgebraML.klein_orbit_four
/-- 1:B2 (Theorem 1, the structural set): the fourth roots of unity number exactly `4` on the shell. Mathlib: `IsPrimitiveRoot.card_rootsOfUnity`. -/
theorem card_fourth_roots : ∀ {F : Type u_1} [Field F] [Fintype F] (κ : ℕ), Fintype.card F = (4 : ℕ) * κ + (1 : ℕ) → Nat.card ↥(rootsOfUnity (4 : ℕ) F) = (4 : ℕ) :=
  @FRC.AlgebraML.card_fourth_roots
/-- 1:B3 (convention 4, the oriented quarter-turn): `i := −g^κ` satisfies `i² = −1`; and `g^(2κ) = −1`, the involution behind Definition 5. From `FrcMathlib.Fourier`. -/
theorem quarter_turn : ∀ {F : Type u_1} [Field F] [Fintype F] (κ : ℕ), Fintype.card F = (4 : ℕ) * κ + (1 : ℕ) → ∀ (g : F), IsPrimitiveRoot g (Fintype.card F - (1 : ℕ)) → (-g ^ κ) ^ (2 : ℕ) = (-1 : F) ∧ g ^ ((2 : ℕ) * κ) = (-1 : F) :=
  @FRC.AlgebraML.quarter_turn
/-- 1:B3 on `𝔽₁₃`: `g = 2`, `i = −2³ = 5`, `5² = −1`. -/
theorem s13_quarter_turn : -(2 : ZMod (13 : ℕ)) ^ (3 : ℕ) = (5 : ZMod (13 : ℕ)) ∧ (5 : ZMod (13 : ℕ)) ^ (2 : ℕ) = (-1 : ZMod (13 : ℕ)) :=
  @FRC.AlgebraML.s13_quarter_turn
/-- 1:B4 (Definition 2, Lemma 1): in the affine frame `(a, b)`, `φ x = a + b x` carries `+` and `·` to `⊕` and `⊗`, is a bijection, and the multiplicative unit of the relabelled field is `a + b`; `b` is the unit only when `a = 0`. -/
theorem affine_frame : ∀ {F : Type u_1} [Field F] (a b : F), b ≠ (0 : F) → have φ := fun x => a + b * x; have oplus := fun x y => a + b * ((x - a) / b + (y - a) / b); have otimes := fun x y => a + b * ((x - a) / b * ((y - a) / b)); (∀ (x y : F), φ (x + y) = oplus (φ x) (φ y)) ∧ (∀ (x y : F), φ (x * y) = otimes (φ x) (φ y)) ∧ Function.Bijective φ ∧ (∀ (y : F), otimes (a + b) y = y) ∧ (a ≠ (0 : F) → otimes b (a + b) ≠ a + b) :=
  @FRC.AlgebraML.affine_frame
/-- 1:C4 (Definition 5 (a)): the meridian involution `(−a)·g^(n + 2κ) = a·g^n`. -/
theorem meridian_involution : ∀ {F : Type u_1} [Field F] [Fintype F] (κ : ℕ), Fintype.card F = (4 : ℕ) * κ + (1 : ℕ) → ∀ (g : F), IsPrimitiveRoot g (Fintype.card F - (1 : ℕ)) → ∀ (a : F) (n : ℕ), -a * g ^ (n + (2 : ℕ) * κ) = a * g ^ n :=
  @FRC.AlgebraML.meridian_involution
/-- 1:D2 (Definition 6 made precise): the framed-integer window. Integers of absolute value `≤ H` with `2H < card F` have distinct residues: the cast `ℤ → ZMod p` is injective on the window. Stated on `ZMod p`. -/
theorem framed_integer_window : ∀ (p : Nat) [@NeZero Nat (@MulZeroClass.toZero Nat Nat.instMulZeroClass) p] (H : Nat), @LT.lt Nat instLTNat (@HMul.hMul Nat Nat Nat (@instHMul Nat instMulNat) (@OfNat.ofNat Nat (nat_lit 2) (instOfNatNat (nat_lit 2))) H) p → ∀ (x y : Int), @LE.le Int Int.instLEInt (@abs Int instLatticeInt Int.instAddGroup x) (@Nat.cast Int instNatCastInt H) → @LE.le Int Int.instLEInt (@abs Int instLatticeInt Int.instAddGroup y) (@Nat.cast Int instNatCastInt H) → @Eq (ZMod p) (@Int.cast (ZMod p) (@AddGroupWithOne.toIntCast (ZMod p) (@Ring.toAddGroupWithOne (ZMod p) (@CommRing.toRing (ZMod p) (ZMod.commRing p)))) x) (@Int.cast (ZMod p) (@AddGroupWithOne.toIntCast (ZMod p) (@Ring.toAddGroupWithOne (ZMod p) (@CommRing.toRing (ZMod p) (ZMod.commRing p)))) y) → @Eq Int x y :=
  @FRC.AlgebraML.framed_integer_window
/-- 1:D4 (Lemma 2 restated in the field — scale-periodicity): the scale map `S n x = x · g^(−n)` on the shell is `(card F − 1)`-periodic in `n`: the residue grids `G_n = S_n(0..p−1)` coincide as ordered lists. -/
theorem scale_periodic : ∀ {F : Type u_1} [Field F] [Fintype F] (g : F), IsPrimitiveRoot g (Fintype.card F - (1 : ℕ)) → ∀ (n : ℕ) (x : F), x * (g ^ (n + (Fintype.card F - (1 : ℕ))))⁻¹ = x * (g ^ n)⁻¹ :=
  @FRC.AlgebraML.scale_periodic
/-- 1:E2 (Proposition 5 reversed): adjoining a root of `X² + 1` to a field that already contains one gives zero divisors — `F[X]/(X²+1)` is not a field on the shell. With `u² = −1`, `(X + u)(X − u) = 0` in the quotient while both factors are nonzero. -/
theorem complex_chart_zero_divisor : ∀ {F : Type u_1} [Field F] (u : F), u ^ (2 : ℕ) = (-1 : F) → let R := AdjoinRoot (Polynomial.X ^ (2 : ℕ) + (1 : Polynomial F)); ∃ α β, α ≠ (0 : R) ∧ β ≠ (0 : R) ∧ α * β = (0 : R) :=
  @FRC.AlgebraML.complex_chart_zero_divisor
/-- 1:E3 (the conjecture's first clause, solving): `f ∈ F_p[X]` has a root in `F_p` iff `f` and `X^p − X = ∏_a (X − a)` are not coprime — the root test is a gcd, exact in the substrate. -/
theorem root_iff_not_coprime : ∀ (p : ℕ) [hp : Fact (Nat.Prime p)] (f : Polynomial (ZMod p)), (∃ a, Polynomial.eval a f = (0 : ZMod p)) ↔ ¬IsCoprime f (Polynomial.X ^ p - Polynomial.X) :=
  @FRC.AlgebraML.root_iff_not_coprime
/-- 1:E4 (third clause, the abelian case): the rounding `k(θ) = round(Nθ/2π)` puts `2πk/N` within `π/N` of `θ` — `C_N ≅ F_p^×` (`N = p − 1`) is a `π/N`-net of `U(1)`. -/
theorem circle_net : ∀ (N : ℕ), (0 : ℕ) < N → ∀ (θ : ℝ), |θ - (2 : ℝ) * Real.pi * ↑(round (↑N * θ / ((2 : ℝ) * Real.pi))) / ↑N| ≤ Real.pi / ↑N :=
  @FRC.AlgebraML.circle_net
/-- 1:E4 (third clause): the group-law defect of the rounding is at most one step. -/
theorem group_law_defect : ∀ (N : ℕ) (θ₁ θ₂ : ℝ), |round (↑N * θ₁ / ((2 : ℝ) * Real.pi)) + round (↑N * θ₂ / ((2 : ℝ) * Real.pi)) - round (↑N * (θ₁ + θ₂) / ((2 : ℝ) * Real.pi))| ≤ (1 : ℤ) :=
  @FRC.AlgebraML.group_law_defect
/-- 1:Z1 (Theorem 3): `2s = 0 ⇒ s = 0` in a field of characteristic `≠ 2`: the additive cycle has no element of order two; the antipode of the origin is not a residue. -/
theorem no_south_pole : ∀ {F : Type u_1} [Field F], (2 : F) ≠ (0 : F) → ∀ (s : F), (2 : F) * s = (0 : F) → s = (0 : F) :=
  @FRC.AlgebraML.no_south_pole
/-- 1:Z3 (Theorem thm:no-equator): `4s = 0 ⇒ s = 0` in a field of characteristic `≠ 2`: the additive cycle has no element of order four; the quarter positions of the cycle are no residues. -/
theorem no_equator : ∀ {F : Type u_1} [Field F], (2 : F) ≠ (0 : F) → ∀ (s : F), (4 : F) * s = (0 : F) → s = (0 : F) :=
  @FRC.AlgebraML.no_equator
/-- 1:Z3 — a framed rational `a/b` at a quarter position of the additive cycle, `a/b = p(4n+j)/4` with `j ∈ {1, 2, 3}`, satisfies `4a = p·b·(4n+j)` as integers; on the shell this forces `a ≡ 0`, so its value `a b⁻¹` is `0`. Stated for every integer `m` in place of `4n + j`. -/
theorem quarter_position : ∀ (p : ℕ) [Fact (Nat.Prime p)], (2 : ZMod p) ≠ (0 : ZMod p) → ∀ (a b m : ℤ), (4 : ℤ) * a = ↑p * b * m → ↑a * (↑b)⁻¹ = (0 : ZMod p) :=
  @FRC.AlgebraML.quarter_position
/-- 1:Z3 — no framed rational of a window `W_H`, `2H < p`, sits at a quarter position: `4a = p·b·m` with `b, m ≠ 0` and `|a| ≤ H` is impossible, since `p ∣ a` and `|a| < p` force `a = 0`. -/
theorem quarter_position_window : ∀ (p : ℕ) [Fact (Nat.Prime p)] (a b m : ℤ) (H : ℕ), (2 : ℕ) * H < p → |a| ≤ ↑H → b ≠ (0 : ℤ) → m ≠ (0 : ℤ) → (4 : ℤ) * a = ↑p * b * m → False :=
  @FRC.AlgebraML.quarter_position_window
/-- 1:Z3 — the equator lies strictly between the latitudes `L_κ` and `L_{κ+1}`: `4κ < p < 4(κ + 1)` on `p = 4κ + 1`. -/
theorem equator_between : ∀ (p κ : ℕ), p = (4 : ℕ) * κ + (1 : ℕ) → (4 : ℕ) * κ < p ∧ p < (4 : ℕ) * (κ + (1 : ℕ)) :=
  @FRC.AlgebraML.equator_between

-- Ledger predicates of 1-algebra (generated by make_predicates.py from docs/1-algebra/1-algebra-ledger.json; edit the ledger, not this section)
/-- 1:B2 (p01004) — Symmetry completeness: the fourth roots of unity form the unique order-four subgroup $Q_4=\{1,\im,-1,-\im\}$; under the Klein four-group $\langle x\mapsto-x,\,x\mapsto x^{-1}\rangle$, $Q_4$ is the union of the two size-two orbits $\{\pm1\}$, $\{\pm\im\}$, and $\Fpx\setminus Q_4$ splits into exactly $\kap-1$ orbits of size four. For $\p\equiv3\pmod4$ no $\im$ exists. -/
theorem symmetry_completeness : (∀ {F : Type u_1} [Field F] [Fintype F] (κ : ℕ), Fintype.card F = (4 : ℕ) * κ + (1 : ℕ) → ∃ u, u ^ (2 : ℕ) = (-1 : F)) ∧ (∀ {F : Type u_2} [Field F], (2 : F) ≠ (0 : F) → ∀ (x : F), x ≠ (0 : F) → x ^ (2 : ℕ) ≠ (1 : F) → x ^ (2 : ℕ) ≠ (-1 : F) → x ≠ -x ∧ x ≠ x⁻¹ ∧ x ≠ -x⁻¹ ∧ -x ≠ x⁻¹ ∧ -x ≠ -x⁻¹ ∧ x⁻¹ ≠ -x⁻¹) ∧ ∀ {F : Type u_3} [Field F] [Fintype F] (κ : ℕ), Fintype.card F = (4 : ℕ) * κ + (1 : ℕ) → Nat.card ↥(rootsOfUnity (4 : ℕ) F) = (4 : ℕ) :=
  @FRC.LedgerML.p01004
/-- 1:B3 (p01005) — The oriented quarter-turn: $\im=-\gen^{\kap}$ satisfies $\im^{2}=-1$ for every primitive root $\gen$; the two square roots of $-1$ are $\{-\gen^{\kap},\gen^{\kap}\}$, so the drive fixes which is $\im$. On $\F_{13}$, $\gen=2$: $\im=5$. -/
theorem oriented_quarter_turn : (∀ {F : Type u_1} [Field F] [Fintype F] (κ : ℕ), Fintype.card F = (4 : ℕ) * κ + (1 : ℕ) → ∀ (g : F), IsPrimitiveRoot g (Fintype.card F - (1 : ℕ)) → (-g ^ κ) ^ (2 : ℕ) = (-1 : F) ∧ g ^ ((2 : ℕ) * κ) = (-1 : F)) ∧ -(2 : ZMod (13 : ℕ)) ^ (3 : ℕ) = (5 : ZMod (13 : ℕ)) ∧ (5 : ZMod (13 : ℕ)) ^ (2 : ℕ) = (-1 : ZMod (13 : ℕ)) :=
  @FRC.LedgerML.p01005
/-- 1:B4 (p01006) — Affine reframing: $\varphi_{a,b}(x)=a+bx$, $b\neq0$, is a ring isomorphism $(\Fp,+,\cdot)\to(\Fp,\oplus,\otimes)$ with origin $a$ and unit $a+b$; every polynomial identity is frame-covariant. -/
theorem affine_reframing : ∀ {F : Type u_1} [Field F] (a b : F), b ≠ (0 : F) → have φ := fun x => a + b * x; have oplus := fun x y => a + b * ((x - a) / b + (y - a) / b); have otimes := fun x y => a + b * ((x - a) / b * ((y - a) / b)); (∀ (x y : F), φ (x + y) = oplus (φ x) (φ y)) ∧ (∀ (x y : F), φ (x * y) = otimes (φ x) (φ y)) ∧ Function.Bijective φ ∧ (∀ (y : F), otimes (a + b) y = y) ∧ (a ≠ (0 : F) → otimes b (a + b) ≠ a + b) :=
  @FRC.LedgerML.p01006
/-- 1:C4 (p01011) — Involutions and counts: $M_n(a)=M_{n+2\kap}(-a)$ and $L_a(m)=L_{-a}(m+2\kap)$ since $\gen^{2\kap}=-1$; $\p-1$ distinct meridian lists in $2\kap$ great circles; $2\kap$ latitude pairs; one-sided vertex count $(\p-1)^{2}/2+1$, the double cover $(\p-1)^{2}$. -/
theorem involutions_and_counts : ∀ {F : Type u_1} [Field F] [Fintype F] (κ : ℕ), Fintype.card F = (4 : ℕ) * κ + (1 : ℕ) → ∀ (g : F), IsPrimitiveRoot g (Fintype.card F - (1 : ℕ)) → ∀ (a : F) (n : ℕ), -a * g ^ (n + (2 : ℕ) * κ) = a * g ^ n :=
  @FRC.LedgerML.p01011
set_option linter.defProp false in
/-- 1:D2 (p01013) — The window law: $z\mapsto z\bmod\p$ is injective on $W_H$ when $2H<\p$; for $x,y\in W_H$ the residue of $x\pm y$ reads back the integer when $4H<\p$, and that of $xy$ when $2H^{2}<\p$ (the same injectivity on the windows $2H$ and $H^{2}$). -/
def window_law := @FRC.LedgerML.p01013
set_option linter.defProp false in
/-- 1:D4 (p01015) — Scale-periodicity, in the field: $S_n(x)=x\gen^{-n}$ satisfies $S_{n+(\p-1)}=S_n$, and the period is exact: for $x\neq0$, $x\gen^{-m}=x\gen^{-n}$ iff $m\equiv n\pmod{\p-1}$; each grid $G_n$ lists every residue once; the zoom has order $\p-1$. As lists of rationals $x/\gen^{n}$ the grids are not periodic. -/
def scale_periodicity_field := @FRC.LedgerML.p01015
/-- 1:E2 (p01019) — The extension by $X^{2}+1$ is trivial: on the shell $\Fp[X]/(X^{2}+1)$ has zero divisors, $(X+\im)(X-\im)=0$, so it is not a field; $\Fp[X]/(X^{2}+1)$ is a field exactly when $\p\equiv3\pmod4$, every nonzero pair $(a,b)$ having the inverse $(a,-b)/(a^{2}+b^{2})$. -/
theorem quadratic_extension_trivial : ∀ {F : Type u_1} [Field F] (u : F), u ^ (2 : ℕ) = (-1 : F) → let R := AdjoinRoot (Polynomial.X ^ (2 : ℕ) + (1 : Polynomial F)); ∃ α β, α ≠ (0 : R) ∧ β ≠ (0 : R) ∧ α * β = (0 : R) :=
  @FRC.LedgerML.p01019
/-- 1:E3 (p01026) — Solving in the substrate: $f\in\Fp[X]$ has a root in $\Fp$ iff $f$ and $X^{\p}-X=\prod_{a}(X-a)$ are not coprime; a nonzero $f$ of degree $d$ has at most $d$ roots. An equation without a root in $\Fp$ is recognised, not extended (E2). -/
theorem solving_substrate : ∀ (p : ℕ) [hp : Fact (Nat.Prime p)] (f : Polynomial (ZMod p)), (∃ a, Polynomial.eval a f = (0 : ZMod p)) ↔ ¬IsCoprime f (Polynomial.X ^ p - Polynomial.X) :=
  @FRC.LedgerML.p01026
/-- 1:E4 (p01028) — Continuous symmetry, the abelian case: $\Fpx\simeq C_{\p-1}$ is a $\pi/(\p-1)$-net of $U(1)$ under $k\mapsto e^{2\pi\im k/(\p-1)}$; the rounding of a framed turn $u/v$ to $C_{\p-1}$ lies within half a step, and its group-law defect is at most one step. -/
theorem continuous_symmetry_abelian : (∀ (N : ℕ), (0 : ℕ) < N → ∀ (θ : ℝ), |θ - (2 : ℝ) * Real.pi * ↑(round (↑N * θ / ((2 : ℝ) * Real.pi))) / ↑N| ≤ Real.pi / ↑N) ∧ ∀ (N : ℕ) (θ₁ θ₂ : ℝ), |round (↑N * θ₁ / ((2 : ℝ) * Real.pi)) + round (↑N * θ₂ / ((2 : ℝ) * Real.pi)) - round (↑N * (θ₁ + θ₂) / ((2 : ℝ) * Real.pi))| ≤ (1 : ℤ) :=
  @FRC.LedgerML.p01028
/-- 1:Z1 (p01020) — No element of additive order two: $2s=0$ forces $s=0$; the antipode of the origin on the additive cycle is not a residue; it sits between $2\kap=(\p-1)/2$ and $2\kap+1=(\p+1)/2=2^{-1}$. -/
theorem no_additive_order_two : ∀ {F : Type u_1} [Field F], (2 : F) ≠ (0 : F) → ∀ (s : F), (2 : F) * s = (0 : F) → s = (0 : F) :=
  @FRC.LedgerML.p01020
/-- 1:Z3 (p01034) — No latitude on the equator: $4s=0$ forces $s=0$; a framed rational at a quarter position of the additive cycle ($\p/4$, $\p/2$, $3\p/4$) has value $0$, and none of the window sits there; the equator, depth $\kap+\tfrac14$, lies strictly between $L_\kap$ and $L_{\kap+1}$. -/
theorem no_latitude_equator : (∀ {F : Type u_1} [Field F], (2 : F) ≠ (0 : F) → ∀ (s : F), (4 : F) * s = (0 : F) → s = (0 : F)) ∧ (∀ (p : ℕ) [Fact (Nat.Prime p)], (2 : ZMod p) ≠ (0 : ZMod p) → ∀ (a b m : ℤ), (4 : ℤ) * a = ↑p * b * m → ↑a * (↑b)⁻¹ = (0 : ZMod p)) ∧ (∀ (p : ℕ) [Fact (Nat.Prime p)] (a b m : ℤ) (H : ℕ), (2 : ℕ) * H < p → |a| ≤ ↑H → b ≠ (0 : ℤ) → m ≠ (0 : ℤ) → (4 : ℤ) * a = ↑p * b * m → False) ∧ ∀ (p κ : ℕ), p = (4 : ℕ) * κ + (1 : ℕ) → (4 : ℕ) * κ < p ∧ p < (4 : ℕ) * (κ + (1 : ℕ)) :=
  @FRC.LedgerML.p01034
-- end ledger predicates

end FRC.Algebra
