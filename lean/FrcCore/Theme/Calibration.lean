import FrcCore.Nat
import FrcCore.Theme.Field

/-!
# FrcCore.Theme.Calibration — the calibration of the coherent fraction (22:C30, 22:C31)
(the quantum theme; 22-quantum, the calibration construction of 30 October 2026)

Two sources of `m₁`, `m₂` cells, `c₁`, `c₂` of them on their synchronised orbits. Under the eighth realisation's clause
(a locked pair carries one step phase per coupling step in every branch, at any relative phase offset; a pair with a
spread cell carries, in place of the step phase, the cell's winding offset times it) the systematic conditional phase of a
pair run counts the locked–locked pairs, `c₁ c₂` step phases per coupling step against the `m₁ m₂` of the full-mass rate. The normalised rate is the framed rational `ρ = c₁ c₂ / (m₁ m₂)`, written
here as the pair `(c₁ c₂, m₁ m₂)` with equality by cross-multiplication (`feq`). The file decides, on counts alone:

* `reference_rate`: against a spread-free reference (`c = m`) the normalised rate is the source's own fraction;
* `recover_sq`: for three sources the product of two normalised rates over the third returns the square of a fraction,
  `ρ_ij ρ_ik / ρ_jk = (c_i / m_i)²`;
* `quad_consistency`: `ρ_ij ρ_kl = ρ_ik ρ_jl` for four sources, the rank-one structure of the rate table;
* `unit_table`: spread-free sources give the unit entry, the standard-theory case.

For the pairwise spread characteristic (22:C31), the ensemble average of a product of factors drawn independently is the
product of the averages: `dsum_eq` is that identity for finite weighted tables, `Σᵢ Σⱼ (pᵢ qⱼ)(gᵢ hⱼ) = (Σᵢ pᵢ gᵢ)(Σⱼ qⱼ hⱼ)`,
the product rule whose cyclotomic instance the ledger file evaluates in `ℤ[ζ_n]`. No axioms.
-/

namespace FRC.Calibration

/-- A framed rational as a pair (numerator, denominator); two pairs are equal as fractions when they cross-multiply. -/
def feq (a b : Nat × Nat) : Prop := a.1 * b.2 = b.1 * a.2

/-- 22:C30 — the normalised systematic rate of the pair run of sources `(c_i, m_i)` and `(c_j, m_j)`: the locked–locked
pairs over all pairs, `c_i c_j / (m_i m_j)`, the product of the two coherent fractions. -/
def rho (ci mi cj mj : Nat) : Nat × Nat := (ci * cj, mi * mj)

/-- The product of two fractions. -/
def fmul (a b : Nat × Nat) : Nat × Nat := (a.1 * b.1, a.2 * b.2)

/-- `(a b)(c d) = (a c)(b d)`: the one rearrangement every identity below uses. -/
theorem mul4 (a b c d : Nat) : (a * b) * (c * d) = (a * c) * (b * d) := by
  rw [FRC.Nat.mul_assoc, FRC.Nat.mul_left_comm b c d, ← FRC.Nat.mul_assoc]

/-- 22:C30 — the rate law: the normalised rate is the product of the fractions, by definition of the count. -/
theorem rho_eq (ci mi cj mj : Nat) : rho ci mi cj mj = fmul (ci, mi) (cj, mj) := rfl

/-- 22:C30 — against a spread-free reference (`c = m`) the normalised rate of the pair run is the source's own
fraction: `(c_i m) / (m_i m) = c_i / m_i`. -/
theorem reference_rate (ci mi m : Nat) : feq (rho ci mi m m) (ci, mi) := by
  show (ci * m) * mi = ci * (mi * m)
  rw [FRC.Nat.mul_assoc, Nat.mul_comm m mi]

/-- 22:C30 — recovery from three pair runs: `ρ_ij ρ_ik = ρ_jk (c_i/m_i)²` as fractions, so the square of each fraction
is the product of its two rates over the third. -/
theorem recover_sq (ci mi cj mj ck mk : Nat) :
    feq (fmul (rho ci mi cj mj) (rho ci mi ck mk)) (fmul (rho cj mj ck mk) (ci * ci, mi * mi)) := by
  show ((ci * cj) * (ci * ck)) * ((mj * mk) * (mi * mi)) = ((cj * ck) * (ci * ci)) * ((mi * mj) * (mi * mk))
  rw [mul4 ci cj ci ck, mul4 mj mk mi mi, Nat.mul_comm mj mi, Nat.mul_comm mk mi, Nat.mul_comm (cj * ck) (ci * ci)]

/-- 22:C30 — the rank-one table: `ρ_ij ρ_kl = ρ_ik ρ_jl` for four sources, every quadruple a consistency test of the law. -/
theorem quad_consistency (ci mi cj mj ck mk cl ml : Nat) :
    feq (fmul (rho ci mi cj mj) (rho ck mk cl ml)) (fmul (rho ci mi ck mk) (rho cj mj cl ml)) := by
  show ((ci * cj) * (ck * cl)) * ((mi * mk) * (mj * ml)) = ((ci * ck) * (cj * cl)) * ((mi * mj) * (mk * ml))
  rw [mul4 ci cj ck cl, mul4 mi mk mj ml]

/-- 22:C30 — two spread-free sources give the unit entry: the standard theory is the table of ones. -/
theorem unit_table (m m' : Nat) : feq (rho m m m' m') (1, 1) := by
  show (m * m') * 1 = 1 * (m * m')
  rw [Nat.mul_one, Nat.one_mul]

/-- The weighted sum `Σᵢ pᵢ gᵢ` of two tables (the ensemble average of `g` under the weights `p`, up to the total weight). -/
def wsum : List Nat → List Nat → Nat
  | [], _ => 0
  | _ :: _, [] => 0
  | p :: ps, g :: gs => p * g + wsum ps gs

/-- One row of the double sum: `Σⱼ (p qⱼ)(g hⱼ)`. -/
def rowsum (p g : Nat) : List Nat → List Nat → Nat
  | [], _ => 0
  | _ :: _, [] => 0
  | q :: qs, h :: hs => (p * q) * (g * h) + rowsum p g qs hs

/-- The double sum `Σᵢ Σⱼ (pᵢ qⱼ)(gᵢ hⱼ)`: the average of the product of two independent factors over the product ensemble. -/
def dsum : List Nat → List Nat → List Nat → List Nat → Nat
  | [], _, _, _ => 0
  | _ :: _, [], _, _ => 0
  | p :: ps, g :: gs, q, h => rowsum p g q h + dsum ps gs q h

theorem rowsum_eq (p g : Nat) : ∀ (q h : List Nat), rowsum p g q h = (p * g) * wsum q h
  | [], h => by
    show 0 = (p * g) * 0
    rw [Nat.mul_zero]
  | _ :: _, [] => by
    show 0 = (p * g) * 0
    rw [Nat.mul_zero]
  | q :: qs, h :: hs => by
    show (p * q) * (g * h) + rowsum p g qs hs = (p * g) * (q * h + wsum qs hs)
    rw [rowsum_eq p g qs hs, Nat.left_distrib, mul4 p q g h]

/-- 22:C31 — the product rule for independent ensembles: the double sum of the products of two weighted tables is the
product of their sums, `Σᵢ Σⱼ (pᵢ qⱼ)(gᵢ hⱼ) = (Σᵢ pᵢ gᵢ)(Σⱼ qⱼ hⱼ)`; the pairwise spread characteristic of two
independently prepared sources is the product of their own characteristics. -/
theorem dsum_eq : ∀ (p g q h : List Nat), dsum p g q h = wsum p g * wsum q h
  | [], _, q, h => by
    show 0 = 0 * wsum q h
    rw [Nat.zero_mul]
  | _ :: _, [], q, h => by
    show 0 = 0 * wsum q h
    rw [Nat.zero_mul]
  | p :: ps, g :: gs, q, h => by
    show rowsum p g q h + dsum ps gs q h = (p * g + wsum ps gs) * wsum q h
    rw [rowsum_eq, dsum_eq ps gs q h, FRC.Nat.add_mul]

/-! ## Spread laws: the domain of the normalised rate and entanglement under spread (22:C33, 22:C34) -/

section spread
open FRC.Shell
variable {q : Nat} [Pos q]

/-- 22:C33 (ii) — a completely spread cell at a nontrivial character: on a prime shell the complete sum of a character of
order dividing `n` vanishes, `Σ_{ξ<n} w^ξ = 0` for `w^n = 1`, `w ≠ 1` (the telescoping geometric sum, then no zero divisors).
With `w = ζ^{mΔ}` this is the vanishing of the uniform law's characteristic at every nontrivial argument. -/
theorem complete_spread_zero (hq : FRC.Nat.isPrime q) (w : Shell q) (n : Nat) (hn : w ^ n = 1) (hw : w ≠ 1) :
    sumRange (fun ξ => w ^ ξ) n = 0 := by
  have hg := geom_sum_mul w n
  rw [hn, add_neg] at hg
  match Prime.mul_eq_zero hq hg with
  | .inl h => exact h
  | .inr h => exact absurd (Prime.eq_of_sub_eq_zero h) hw

/-- 22:C33 (iv) — the two-point law `(δ₀ + δ₅)/2` on the cycle of order 12 vanishes at the argument 6: for `ζ` of order 12
on a prime shell, `ζ^6` squares to one and is not one, so it is `−1`, and `1 + ζ^{30} = 1 + ζ^6 = 0`. -/
theorem two_point_zero (hq : FRC.Nat.isPrime q) (ζ : Shell q) (h12 : ζ ^ 12 = 1) (h6 : ζ ^ 6 ≠ 1) : 1 + ζ ^ 30 = 0 := by
  have e30 : ζ ^ 30 = ζ ^ 6 := by
    rw [show (30 : Nat) = 12 * 2 + 6 from rfl, pow_add, pow_mul, h12, one_pow, one_mul]
  have hsq : ζ ^ 6 * ζ ^ 6 = 1 := by rw [← pow_add]; exact h12
  have hprod : (ζ ^ 6 + -1) * (ζ ^ 6 + 1) = 0 := by
    rw [right_distrib, left_distrib, left_distrib, hsq, mul_one, neg_one_mul, neg_one_mul, add_assoc,
      ← add_assoc (ζ ^ 6), add_neg, zero_add, add_neg]
  rw [e30]
  match Prime.mul_eq_zero hq hprod with
  | .inl h => exact absurd (Prime.eq_of_sub_eq_zero h) h6
  | .inr h => rw [add_comm]; exact h

end spread

/-! ### The complete-spread states of the four separation classes (22:C34), decided on their integer forms -/

/-- The `i`-th element of a list, or the default past its end (structural, without the library's `getD`). -/
def nth {α : Type} (d : α) : List α → Nat → α
  | [], _ => d
  | x :: _, 0 => x
  | _ :: xs, i + 1 => nth d xs i

/-- The entry `(i, j)` of an integer matrix given as rows. -/
def ent (M : List (List Int)) (i j : Nat) : Int := nth 0 (nth [] M i) j

/-- The principal 2-minor on rows and columns `i, j`. -/
def pmin2 (M : List (List Int)) (i j : Nat) : Int := ent M i i * ent M j j - ent M i j * ent M j i

/-- The principal 3-minor on `i, j, k` (the rule of Sarrus). -/
def pmin3 (M : List (List Int)) (i j k : Nat) : Int :=
  ent M i i * (ent M j j * ent M k k - ent M j k * ent M k j)
  - ent M i j * (ent M j i * ent M k k - ent M j k * ent M k i)
  + ent M i k * (ent M j i * ent M k j - ent M j j * ent M k i)

/-- The determinant of a 4 × 4 matrix, by Laplace expansion along the first row. -/
def det4 (M : List (List Int)) : Int :=
  ent M 0 0 * pmin3 M 1 2 3 - ent M 0 1 * cof M 1 2 3 1 + ent M 0 2 * cof M 1 2 3 2 - ent M 0 3 * cof M 1 2 3 3
where
  /-- The 3 × 3 minor on rows `a b c` with the column `d` removed from `0 1 2 3`. -/
  cof (M : List (List Int)) (a b c d : Nat) : Int :=
    let cols := [0, 1, 2, 3].filter (· ≠ d)
    let sub := [a, b, c].map (fun r => cols.map (fun col => ent M r col))
    pmin3 sub 0 1 2

/-- Nonnegativity of an integer, by its constructor. -/
def nonneg : Int → Bool
  | Int.ofNat _ => true
  | Int.negSucc _ => false

/-- Positive semidefiniteness of a symmetric 4 × 4 integer matrix: every principal minor is nonnegative. -/
def psd4 (M : List (List Int)) : Bool :=
  [0, 1, 2, 3].all (fun i => nonneg (ent M i i)) &&
  [(0, 1), (0, 2), (0, 3), (1, 2), (1, 3), (2, 3)].all (fun p => nonneg (pmin2 M p.1 p.2)) &&
  [(0, 1, 2), (0, 1, 3), (0, 2, 3), (1, 2, 3)].all (fun t => nonneg (pmin3 M t.1 t.2.1 t.2.2)) &&
  nonneg (det4 M)

/-- Four times the partial transpose of the complete-spread state: four distinct separations. -/
def ptDistinct : List (List Int) := [[1, 0, 0, 0], [0, 1, 0, 0], [0, 0, 1, 0], [0, 0, 0, 1]]
/-- One pair of separations equal (`r_LL = r_RR`, the linear layouts). -/
def ptOnePair : List (List Int) := [[1, 0, 0, 0], [0, 1, 1, 0], [0, 1, 1, 0], [0, 0, 0, 1]]
/-- Two pairs equal (`r_LL = r_RR` and `r_LR = r_RL`). -/
def ptTwoPairs : List (List Int) := [[1, 0, 0, 1], [0, 1, 1, 0], [0, 1, 1, 0], [1, 0, 0, 1]]
/-- Three separations equal (`r_LL = r_LR = r_RL`). -/
def ptThreeEqual : List (List Int) := [[1, 1, 1, 1], [1, 1, 0, 0], [1, 0, 1, 0], [1, 0, 0, 1]]

/-- 22:C34 (i) — the three nondegenerate classes are positive under partial transposition, hence separable (Peres–Horodecki
for two qubits): every principal minor of the three integer forms is nonnegative. -/
theorem pt_psd_classes : psd4 ptDistinct = true ∧ psd4 ptOnePair = true ∧ psd4 ptTwoPairs = true := ⟨rfl, rfl, rfl⟩

/-- 22:C34 (ii) — three equal separations: the partial transpose has a negative determinant, `−2` on the integer form,
so an eigenvalue is negative and the complete-spread state is entangled. -/
theorem three_equal_npt : det4 ptThreeEqual = -2 := rfl

/-- The position of `x` in a list, if present. -/
def posOf (x : Nat) : List Nat → Nat → Option Nat
  | [], _ => none
  | y :: ys, i => if y = x then some i else posOf x ys (i + 1)

/-- The relabelling of a list of separation labels by first occurrence. -/
def canon : List Nat → List Nat → List Nat
  | [], _ => []
  | x :: xs, seen =>
    match posOf x seen 0 with
    | some i => i :: canon xs seen
    | none => seen.length :: canon xs (seen ++ [x])

/-- Insertion into a decreasing list. -/
def insertDesc (x : Nat) : List Nat → List Nat
  | [] => [x]
  | y :: ys => if y ≤ x then x :: y :: ys else y :: insertDesc x ys

/-- Insertion sort, decreasing. -/
def sortDesc : List Nat → List Nat
  | [] => []
  | x :: xs => insertDesc x (sortDesc xs)

/-- The block sizes of a canonical labelling, in decreasing order. -/
def blockSizes (l : List Nat) : List Nat :=
  sortDesc ((List.range l.length).filterMap (fun v => let c := l.count v; if c = 0 then none else some c))

/-- The labellings of the four branches by separation, relabelled by first occurrence (every map from four branches to
four labels), and the nondegenerate ones among them: no three separations equal. -/
def labellings : List (List Nat) :=
  (List.range 4).flatMap fun a => (List.range 4).flatMap fun b => (List.range 4).flatMap fun c => (List.range 4).map fun d =>
    canon [a, b, c, d] []

def nondegenerate : List (List Nat) := labellings.filter (fun l => l.all (fun v => l.count v < 3))

/-- 22:C34 (i) — the nondegenerate geometries fall into exactly three classes by block sizes, four distinct, one pair
equal and two pairs equal: every nondegenerate labelling has one of the three block-size patterns, and each pattern occurs. -/
theorem nondegenerate_classes :
    (nondegenerate.all (fun l => [[1, 1, 1, 1], [2, 1, 1], [2, 2]].contains (blockSizes l)) &&
     [[1, 1, 1, 1], [2, 1, 1], [2, 2]].all (fun s => (nondegenerate.map blockSizes).contains s)) = true := by decide

end FRC.Calibration
