import FrcCore.Theme.YangMills

/-!
# FrcCore.Theme.Plaquette — the frame's window, the spectral amplitude of a plaquette and the tallies of the ring (the yangmills theme's third file, 13 November 2026)

Split from `Theme/YangMills.lean` on 13 November 2026 with every declaration as it stood, in the namespace `FRC.YangMills`, as
`frc/plaquette.py`, `frc/yangmills.py` and `frc/ledgers/p46_yangmills.py` compute it. The frame's window and its first
departure on the shell `13` (`frame_window`, 46:C15). The spectral amplitude of a plaquette (`spectral_amplitude`,
`frame_cycle_trace`, 46:C16), the frame's root elements (`frame_root_elements`, 46:A9), the instance's distribution and its
transfer tally (`instance_amplitude`, 46:C17; `instance_transfer`, 46:C18). The transfer tally on the three Subjects (46:C19):
the orders of their frames, the three degrees whose inverses are the eigenvalues of the step with the frame's mean, and the
bookkeeping of its spectrum (`subject_spectrum`), and the identity `Σ a χ(1) = 3` swept over `q ≤ 2000` (`degree_identity`);
the gap `1/(q + 1)` of the transfer tally (`ring_gap`); the reduced tally of the ring in the quadratic extension, its
conjugate and its norm (`ring_tally_plane`), and the example at a boundary class with eigenvalues outside the shell on the
three Subjects (`ring_tally_outside_shell`); the tally with a norm-one link at every step, in the plane, on the three Subjects
(`norm_one_link_tally`, 46:C27). The spectrum in `2π` (`spectrum_in_pi`, 46:C21), the product channels
(`product_channel_counts`, 46:C22), the tally with the same boundary link at every step (`uniform_boundary_tally`, 46:C23),
what a reading keeps of the window (`window_readings`, 46:C24), three rings on common links (`three_rings_reading`, 46:C25)
and the series on the shell (`shell_series_readings`, 46:C26). No axioms.
-/

namespace FRC.YangMills

open FRC.Shell FRC.Shell.Frame

variable {p : Nat} [Pos p] {κ : Nat} {g : Shell p}

/-! ## The frame's window and its first departure (46:C15)

For `p > 3` the frame's invariant counts in `3^{⊗a} ⊗ 3̄^{⊗b}` are the compact ones through degree `2p − 1`, and the Frobenius
tensor `v_p` at `(4p − 4, 1)` lies beyond them (46-yangmills, Theorem thm:window), so the first departure `d_*` lies in
`[2p, 4p − 3]`. The finite ingredients decided here on the shell `13`: the binomial table of the row-operation identity, `C(m + r, r)`
modulo `13` for `m = 11, 12` with `r ≤ 25` and for `m = 24, 25` with `r ≤ 12`, nonzero exactly at the stated `r`; the weights
`(25, 11, 11)` of the words of `v_13`, unequal and congruent modulo `p + 1 = 14`; the bounds on the three Subjects; the orders of the
series' window; and the small fields' first degrees `5 = 4·2 − 3`, `9 = 4·3 − 3`. -/

/-- `C(m + r, r)` by the recurrence `C(m + r, r) = C(m + r − 1, r − 1) (m + r) / r`, the division exact. -/
def binomShift (m : Nat) : Nat → Nat
  | 0 => 1
  | r + 1 => binomShift m r * (m + r + 1) / (r + 1)

/-- The residues `C(m + r, r) mod p` for `r ≤ R`. -/
def binomRow (p m R : Nat) : List Nat := (List.range (R + 1)).map (fun r => binomShift m r % p)

/-- The pattern of the proof of 46:C15 for `q = p`: for `m = p − 2` the residues are `1, p − 1` at `r = 0, 1` and again at `r = p, p + 1`;
for `m = p − 1` they are `1` at `r = 0, p`; for `m = 2p − 2` (`r ≤ p − 1`) `1, p − 1` at `r = 0, 1`; for `m = 2p − 1` only `1` at `r = 0`. -/
def expectedRow (p m R : Nat) : List Nat :=
  (List.range (R + 1)).map (fun r =>
    if m = p - 2 then (if r = 0 ∨ r = p then 1 else if r = 1 ∨ r = p + 1 then p - 1 else 0)
    else if m = p - 1 then (if r = 0 ∨ r = p then 1 else 0)
    else if m = 2 * p - 2 then (if r = 0 then 1 else if r = 1 then p - 1 else 0)
    else (if r = 0 then 1 else 0))

/-- 46:C15 — on the shell `13`: the four rows of the binomial table are the proof's pattern; the weights `(25, 11, 11)` of `v_13`'s
words are unequal, with `25 − 11 = 14 = p + 1`; the first departure lies in `[26, 49]` on `13`, `[346, 689]` on `173`,
`[3098, 6193]` on `1549`; the series' window is `ϑ^{24}, ϑ^{23}` on `13`, beyond the `ϑ^{7}` computed; and `4q − 3` is `5`, `9` at
`q = 2, 3`. -/
theorem frame_window :
    binomRow 13 11 25 = expectedRow 13 11 25 ∧ binomRow 13 12 25 = expectedRow 13 12 25 ∧
    binomRow 13 24 12 = expectedRow 13 24 12 ∧ binomRow 13 25 12 = expectedRow 13 25 12 ∧
    (2 * 13 - 1 ≠ 13 - 2 ∧ (2 * 13 - 1) - (13 - 2) = 13 + 1) ∧
    (2 * 13 = 26 ∧ 4 * 13 - 3 = 49 ∧ 2 * 173 = 346 ∧ 4 * 173 - 3 = 689 ∧ 2 * 1549 = 3098 ∧ 4 * 1549 - 3 = 6193) ∧
    (2 * 13 - 2 = 24 ∧ 2 * 13 - 3 = 23 ∧ 7 < 2 * 13 - 3) ∧ (4 * 2 - 3 = 5 ∧ 4 * 3 - 3 = 9) := by
  decide

/-! ## The spectral amplitude of a plaquette (46:B4, C16, C17, C18) and the frame's root elements (46:A9)

The amplitude `w(U)` of 46-yangmills, Definition def:amplitude, the sum of the three phases of the class of `U_s`, takes its values in the
cyclotomic ring of two formal roots of unity, of the orders `q² − 1` and `q² − q + 1`; on the enumerable instance `q = 2` the ring is `Z[ζ₃]`, written here as integer pairs `a + b z` with
`z² = −1 − z`. Decided here: the plane's cycles `p² − 1` and their gcds with the Carriers' cycles on the three Subjects, the orders
`p² − p + 1` of the second cycle prime to those cycles, the second cycle in the arithmetic of the plane (`frame_cycle_trace`), the centre of order `3` on `173` only (Proposition prop:amplitude(iv)); the identity `2η + η⁻² = 3η` for
`η³ = 1` and the arithmetic `z ≠ 1`, `1 + z + z² = 0` behind the vanishing of a sum fixed by multiplication by `z` (the trivial channel annihilated); the instance's distribution
`64 · (3 + 3z + 3z²) = 0` with its moments `8, 24, 72` (Theorem thm:amplitude); and the bookkeeping of the transfer tally's
spectrum `144, 36, 0, −72` with multiplicities `9, 36, 144, 27` (Theorem thm:transfer). The enumeration over `F_4` is the python
check's. -/

/-- `Z[ζ₃]` as pairs `a + b z`, `z² = −1 − z`: the product. -/
def z3Mul (x y : Int × Int) : Int × Int := (x.1 * y.1 - x.2 * y.2, x.1 * y.2 + x.2 * y.1 - x.2 * y.2)

/-- The inverse-phase conjugation `z ↦ z² = −1 − z`. -/
def z3Conj (x : Int × Int) : Int × Int := (x.1 - x.2, -x.2)

/-- The norm `w · w̄` of a pair, an integer. -/
def z3Norm (x : Int × Int) : Int := (z3Mul x (z3Conj x)).1

/-- 46:C16 — the plane's cycles `p² − 1` on the Subjects, their gcds with the Carriers' cycles `Ω − 1`, the orders
`p² − p + 1` of the second cycle prime to the cycles (`157` against `232` on the Subject `13`), the centre of order `3` on `173` only; and in `Z[ζ₃]`
the singular identity `2η + η⁻² = 3η` for `η = z, z²`, the conjugation `z ↦ z²`, `z³ = 1`, `z ≠ 1` and `1 + z + z² = 0`. -/
theorem spectral_amplitude :
    (13 * 13 - 1 = 168 ∧ 173 * 173 - 1 = 29928 ∧ 1549 * 1549 - 1 = 2399400) ∧
    (Nat.gcd 168 232 = 8 ∧ Nat.gcd 29928 30088 = 8 ∧ Nat.gcd 2399400 2408560 = 40) ∧
    (13 * 13 - 13 + 1 = 157 ∧ Nat.gcd 157 232 = 1 ∧ Nat.gcd (173 * 173 - 173 + 1) 30088 = 1 ∧ Nat.gcd (1549 * 1549 - 1549 + 1) 2408560 = 1) ∧
    ((13 + 1) % 3 ≠ 0 ∧ (173 + 1) % 3 = 0 ∧ (1549 + 1) % 3 ≠ 0 ∧ (2 + 1) % 3 = 0) ∧
    (z3Mul (0, 1) (0, 1) = (-1, -1) ∧ z3Mul (z3Mul (0, 1) (0, 1)) (0, 1) = (1, 0) ∧ z3Conj (0, 1) = (-1, -1)) ∧
    (((0 : Int), (1 : Int)) ≠ (1, 0) ∧ (1 : Int) + 0 + -1 = 0 ∧ (0 : Int) + 1 + -1 = 0) ∧      -- z ≠ 1 and 1 + z + z² = 0: a sum fixed by z vanishes
    (z3Mul (2, 0) (0, 1) = (0, 2) ∧ z3Mul (0, 2) (0, 1) = (-2, -2) ∧
     (0, 2).1 + (0, 1).1 = (0, 3).1 ∧ (0, 2).2 + (0, 1).2 = (0, 3).2 ∧            -- 2z + z⁻² = 2z + z = 3z
     (-2, -2).1 + (-1, -1).1 = (-3, -3).1 ∧ (-2, -2).2 + (-1, -1).2 = (-3, -3).2) := by   -- 2z² + z⁻⁴ = 2z² + z² = 3z²
  decide

section FrameCycle
open FRC.Extension

/-- A 3×3 matrix over the plane `F_p(√2)`: the list of its nine entries, by rows. -/
abbrev PMat (p : Nat) [Pos p] := List (Ext p 2)

/-- The entry of a matrix at a position `0, …, 8`. -/
def pmGet {p : Nat} [Pos p] : PMat p → Nat → Ext p 2
  | [], _ => 0
  | a :: _, 0 => a
  | _ :: l, n + 1 => pmGet l n

/-- The product of two 3×3 matrices over the plane. -/
def pmMul {p : Nat} [Pos p] (A B : PMat p) : PMat p :=
  (List.range 9).map fun n =>
    pmGet A (3 * (n / 3)) * pmGet B (n % 3) + pmGet A (3 * (n / 3) + 1) * pmGet B (3 + n % 3)
      + pmGet A (3 * (n / 3) + 2) * pmGet B (6 + n % 3)

/-- The sum of two matrices, and the scalar matrix of a point of the plane. -/
def pmAdd {p : Nat} [Pos p] (A B : PMat p) : PMat p := List.zipWith (· + ·) A B
def pmScal {p : Nat} [Pos p] (c : Ext p 2) : PMat p := [c, 0, 0, 0, c, 0, 0, 0, c]

/-- `A ^ n` by squaring. The first argument is an encoding: it bounds the number of binary digits of `n`, and `64` covers every
exponent of this file. -/
def pmPow {p : Nat} [Pos p] : Nat → PMat p → Nat → PMat p
  | 0, _, _ => pmScal 1
  | f + 1, A, n => if n = 0 then pmScal 1 else
      if n % 2 = 1 then pmMul A (pmPow f (pmMul A A) (n / 2)) else pmPow f (pmMul A A) (n / 2)

/-- The trace and the determinant. -/
def pmTrace {p : Nat} [Pos p] (A : PMat p) : Ext p 2 := pmGet A 0 + pmGet A 4 + pmGet A 8
def pmDet {p : Nat} [Pos p] (A : PMat p) : Ext p 2 :=
  pmGet A 0 * (pmGet A 4 * pmGet A 8 + -(pmGet A 5 * pmGet A 7))
    + -(pmGet A 1 * (pmGet A 3 * pmGet A 8 + -(pmGet A 5 * pmGet A 6)))
    + pmGet A 2 * (pmGet A 3 * pmGet A 7 + -(pmGet A 4 * pmGet A 6))

/-- The element `a + b√2` of `F_p(√2)`. -/
def planePoint (p : Nat) [Pos p] (a b : Shell p) : Ext p 2 := ⟨a, b⟩

/-- The companion matrix of `x³ − t x² + t̄ x − 1`, for a point `t = (a, b)` of the plane. -/
def cycleMat (p : Nat) [Pos p] (a b : Shell p) : PMat p := [0, 0, 1, 1, 0, planePoint p (-a) b, 0, 1, planePoint p a b]

/-- The facts of one Subject, for `C = cycleMat p a b`, `m = p² − p + 1`, `D = C^(p²)` and `E = C^(m − p)`, the inverse of
`C^p`: `C^m = 1`; `D − C` is invertible, so `C` has no eigenvalue on the plane; and `C`, `D`, `E` have the sum `t·1`, the sum
of pairwise products `t̄·1` and the product `1`. The three are then the roots of `x³ − t x² + t̄ x − 1`, and
`C^k + D^k + E^k = (Tr C^k)·1` for every power. -/
def cycleFacts (p : Nat) [Pos p] (a b : Shell p) (m : Nat) : Bool :=
  let C := cycleMat p a b
  let D := pmPow 64 C (p * p)
  let E := pmPow 64 C (m - p)
  let t : Ext p 2 := planePoint p a b
  decide (pmPow 64 C m = pmScal 1) && decide (pmDet (pmAdd D (pmMul (pmScal (-1)) C)) ≠ 0)
    && decide (pmAdd (pmAdd C D) E = pmScal t)
    && decide (pmAdd (pmAdd (pmMul C D) (pmMul D E)) (pmMul E C) = pmScal (Ext.conj t))
    && decide (pmMul (pmMul C D) E = pmScal 1)

/-- 46:C16 — the second cycle on the three Subjects, in the arithmetic of the plane `F_p(√2)` alone, for a matrix with the
characteristic polynomial of a generator of that cycle: the companion matrix `C` of `x³ − t x² + t̄ x − 1`, `t = (9, 4)`,
`(166, 160)`, `(1275, 523)`. A frame element with this characteristic polynomial is conjugate to `C` over the plane, and the
statements do not change under conjugation. `C` has the order `p² − p + 1 = 157`, `29757`, `2397853` (a power `C^(m/r)` is not
`1` for the prime divisors `r` of `m`) and no eigenvalue on the plane. `C`, `C^(p²)` and `C^(−p)` are the three roots of the
polynomial: their sum is `t·1`, the sum of their pairwise products `t̄·1` and their product `1`, so
`C^k + C^(kp²) + C^(−kp) = (Tr C^k)·1` for every power. On `173` the power `C^(m/3)` is the central point `(86, 155)` of
order `3`. -/
theorem frame_cycle_trace :
    (cycleFacts 13 9 4 157 = true ∧ cycleMat 13 9 4 ≠ pmScal 1) ∧
    (cycleFacts 173 166 160 29757 = true ∧
      pmPow 64 (cycleMat 173 166 160) 9919 = pmScal (planePoint 173 86 155) ∧ planePoint 173 86 155 ≠ 1 ∧
      planePoint 173 86 155 * planePoint 173 86 155 * planePoint 173 86 155 = 1 ∧
      pmPow 64 (cycleMat 173 166 160) 4251 ≠ pmScal 1 ∧ pmPow 64 (cycleMat 173 166 160) 2289 ≠ pmScal 1 ∧
      pmPow 64 (cycleMat 173 166 160) 273 ≠ pmScal 1) ∧
    (cycleFacts 1549 1275 523 2397853 = true ∧ cycleMat 1549 1275 523 ≠ pmScal 1) := by
  decide +kernel

/-! ### The frame's root elements (46:A9)

Proposition prop:mult(iii) of 46-yangmills uses the elements `x(λ, μ) = 1 + λE₀₁ − λ̄E₁₂ + μE₀₂`, `μ + μ̄ + λλ̄ = 0`, of the frame of the
Hermitian form `ξ₀η̄₂ + ξ₁η̄₁ + ξ₂η̄₀`, and their transposes. Decided here on the three Subjects, over the plane `F_p(√2)`: the two
elements at `(λ, μ) = (1, −1/2 + √2)` and `(√2, 1 + √2)`, with `−1/2` the residue `(p − 1)/2`, have determinant `1` and preserve the
form, as do their transposes; `6` is invertible on the shell; the plane has more than `a + b + min(a, b)` elements for every degree
`a + b ≤ 2p − 1`; and the degree `9` of the python check satisfies `9 + 2 ≤ 13`, the smallest Subject. The counts of the fixed vectors are the python check's. -/

/-- The transpose of a `3 × 3` matrix over the plane. -/
def pmTr {p : Nat} [Pos p] (A : PMat p) : PMat p := (List.range 9).map fun n => pmGet A (3 * (n % 3) + n / 3)

/-- The entrywise conjugate, the Frobenius of the plane over the shell. -/
def pmConj {p : Nat} [Pos p] (A : PMat p) : PMat p := A.map Ext.conj

/-- The matrix of the Hermitian form `ξ₀η̄₂ + ξ₁η̄₁ + ξ₂η̄₀`. -/
def antiDiag (p : Nat) [Pos p] : PMat p := [0, 0, 1, 0, 1, 0, 1, 0, 0]

/-- The root element `x(λ, μ) = 1 + λE₀₁ − λ̄E₁₂ + μE₀₂`. -/
def rootMat {p : Nat} [Pos p] (l m : Ext p 2) : PMat p := [1, l, m, 0, 1, -(Ext.conj l), 0, 0, 1]

/-- The facts of one root element `x = x(λ, μ)`: `μ + μ̄ + λλ̄ = 0`; `det x = 1`; `xᵀ J x̄ = J`; the transpose satisfies the same
equation; `x ≠ 1`. -/
def rootFacts {p : Nat} [Pos p] (l m : Ext p 2) : Bool :=
  let x := rootMat l m
  decide (m + Ext.conj m + l * Ext.conj l = 0)
    && decide (pmDet x = 1)
    && decide (pmMul (pmMul (pmTr x) (antiDiag p)) (pmConj x) = antiDiag p)
    && decide (pmMul (pmMul x (antiDiag p)) (pmConj (pmTr x)) = antiDiag p)
    && decide (x ≠ pmScal 1)

/-- 46:A9 — the frame's root elements on the three Subjects, where `−1/2` is the residue `6`, `86`, `774`: `x(1, −1/2 + √2)` and
`x(√2, 1 + √2)` have determinant `1` and preserve the Hermitian form of the antidiagonal, as do their transposes; `6` is invertible
on the shell, with the inverses `11`, `29`, `1291`; `(2p − 1) + (p − 1) < p²`, so the plane has more than `a + b + min(a, b)` elements
through the degree `2p − 1`; and `9 + 2 ≤ 13`. -/
theorem frame_root_elements :
    (rootFacts (planePoint 13 1 0) (planePoint 13 6 1) = true ∧ rootFacts (planePoint 13 0 1) (planePoint 13 1 1) = true) ∧
    (rootFacts (planePoint 173 1 0) (planePoint 173 86 1) = true ∧ rootFacts (planePoint 173 0 1) (planePoint 173 1 1) = true) ∧
    (rootFacts (planePoint 1549 1 0) (planePoint 1549 774 1) = true ∧
      rootFacts (planePoint 1549 0 1) (planePoint 1549 1 1) = true) ∧
    ((6 : Shell 13) * 11 = 1 ∧ (6 : Shell 173) * 29 = 1 ∧ (6 : Shell 1549) * 1291 = 1) ∧
    (25 + 12 < 13 * 13 ∧ 345 + 172 < 173 * 173 ∧ 3097 + 1548 < 1549 * 1549) ∧
    9 + 2 ≤ 13 := by
  decide +kernel

end FrameCycle

/-- 46:C17 — the instance's distribution: the values `3, 3z, 3z²` on `64` elements each and `0` on `24` sum to zero,
`64 · (3 + 3z + 3z²) = 0`; every nonzero value has norm `9`, so the moments are `192 · 9 / 216 = 8`, `192 · 27 / 216 = 24` (the cubes of
`3, 3z, 3z²` are all `27`) and `192 · 81 / 216 = 72`; the invariant counts the moments are set against are `1, 1, 2`. -/
theorem instance_amplitude :
    (64 * ((3 : Int) + 0 + -3) = 0 ∧ 64 * ((0 : Int) + 3 + -3) = 0) ∧
    (z3Norm (3, 0) = 9 ∧ z3Norm (0, 3) = 9 ∧ z3Norm (-3, -3) = 9 ∧ z3Norm (0, 0) = 0) ∧
    (z3Mul (z3Mul (0, 3) (0, 3)) (0, 3) = (27, 0) ∧ z3Mul (z3Mul (-3, -3) (-3, -3)) (-3, -3) = (27, 0)) ∧
    (192 * 9 = 8 * 216 ∧ 192 * 27 = 24 * 216 ∧ 192 * 81 = 72 * 216 ∧ 64 + 64 + 64 + 24 = 216) ∧
    (8 ≠ 1 ∧ 24 ≠ 1 ∧ 72 ≠ 2) := by
  decide

/-- 46:C18 — the transfer tally on the instance, the step of one plaquette with the frame's mean: the multiplicities `9, 36, 144, 27`
of the eigenvalues `2/3, 1/6, 0, −1/3` sum to `216`; the eigenvalues are the integers `144, 36, 0, −72` of the matrix `216 K` over
`216`; with the denominators cleared by `6` the trace is `tr K = 3`, and by `36` it is `tr K² = 8`, which is the sum `192 · 9` of
the norms of the `216` amplitudes over `216`; `(3x + 1)(6x − 1)(3x − 2) = 54x³ − 27x² − 9x + 2`, so the annihilating polynomial
has distinct roots; and `−1/3 < 0`. -/
theorem instance_transfer :
    (9 + 36 + 144 + 27 = 216) ∧
    (2 * 216 = 3 * 144 ∧ 1 * 216 = 6 * 36 ∧ (-1 : Int) * 216 = 3 * (-72)) ∧
    (4 * 9 + 1 * 36 + 0 * 144 + (-2 : Int) * 27 = 6 * 3) ∧
    (4 * 4 * 9 + 1 * 1 * 36 + 0 + (2 : Int) * 2 * 27 = 36 * 8 ∧ 8 * 216 = 192 * 9) ∧
    (3 * 6 * 3 = (54 : Int) ∧ 3 * 6 * (-2) + 3 * (-1) * 3 + 1 * 6 * 3 = (-27 : Int) ∧
     3 * (-1) * (-2) + 1 * 6 * (-2) + 1 * (-1) * 3 = (-9 : Int) ∧ 1 * (-1) * (-2) = (2 : Int)) ∧
    ((-2 : Int) < 0 ∧ (-2 : Int) < 1 ∧ (1 : Int) < 4) := by
  decide

/-! ### The transfer tally on the Subjects (46:C19, 10 November 2026)

The amplitude expands as `w = χ₁ + χ₂ − χ₃` in the first members of the three families of degrees `q² − q + 1`, `q³ + 1`,
`(q + 1)² (q − 1)` of the generic character table of `SU(3, q)` (the python side's exact character sums; the paper's Theorem thm:subjects).
The transfer tally is the step of one plaquette with the frame's mean, and its nonzero eigenvalues are `a_χ / χ(1)`: `1/d₁`, `1/d₂`,
`−1/d₃`. Decided here: the orders of the three Subjects' frames, the three degrees, and the bookkeeping of the spectrum — the
degrees divide the order, `tr K = d₁ + d₂ − d₃ = 3`, `tr K² = Σ a² = 3`, a zero eigenvalue of positive multiplicity, the degrees
positive and increasing (`subject_spectrum`); and the polynomial identity `Σ a χ(1) = 3`, that is
`(q² − q + 1) + (q³ + 1) = (q + 1)² (q − 1) + 3`, swept over `1 ≤ q ≤ 2000` (`degree_identity`). The coefficients themselves are the
python computation's. -/

/-- The order of `SU(3, 𝔽_q)`: `q³ (q + 1)² (q − 1) (q² − q + 1)`. This and `degs`, `spectrumOK`, `gapOK` are instantiated on the
laboratory frames only, where the order is below the totality's count. -/
def su3Order (q : Nat) : Int := (q ^ 3 * (q + 1) ^ 2 * (q - 1) * (q * q - q + 1) : Nat)

/-- The three degrees of the expansion `w = χ₁ + χ₂ − χ₃`: `q² − q + 1`, `q³ + 1`, `(q + 1)² (q − 1)`. -/
def degs (q : Nat) : Int × Int × Int := ((q * q - q + 1 : Nat), (q ^ 3 + 1 : Nat), ((q + 1) ^ 2 * (q - 1) : Nat))

/-- The bookkeeping of the spectrum of the step on one frame, whose nonzero eigenvalues are `1/d₁, 1/d₂, −1/d₃`: the degrees divide
the order, `tr K = Σ a d = d₁ + d₂ − d₃ = 3`, `tr K² = Σ a² = 3`, a zero eigenvalue of positive multiplicity
(`d₁² + d₂² + d₃² < |G|`), and `0 < d₁ < d₂ < d₃`, so the three eigenvalues are distinct and the third is negative. -/
def spectrumOK (q : Nat) : Bool :=
  let G := su3Order q; let (d1, d2, d3) := degs q
  G % d1 == 0 && G % d2 == 0 && G % d3 == 0 && d1 + d2 - d3 == 3 && (1 : Int) * 1 + 1 * 1 + (-1) * (-1) == 3 &&
  d1 * d1 + d2 * d2 + d3 * d3 < G && 0 < d1 && d1 < d2 && d2 < d3

/-- 46:C19 — the transfer tally on the Subjects: the orders `811 273 008`, `802 332 524 681 473 968`, `33 144 476 289 365 359 469 790 000`
of the frames on `13`, `173`, `1549`; the degrees `157, 2198, 2352`; `29 757, 5 177 718, 5 207 472`;
`2 397 853, 3 716 672 150, 3 719 070 000`, whose inverses with the signs `+, +, −` are the eigenvalues of the step with the frame's
mean; and the bookkeeping of the spectrum on each. -/
theorem subject_spectrum :
    (su3Order 13 = 811273008 ∧ su3Order 173 = 802332524681473968 ∧ su3Order 1549 = 33144476289365359469790000) ∧
    (degs 13 = (157, 2198, 2352) ∧ degs 173 = (29757, 5177718, 5207472) ∧ degs 1549 = (2397853, 3716672150, 3719070000)) ∧
    (spectrumOK 13 = true ∧ spectrumOK 173 = true ∧ spectrumOK 1549 = true) := by
  decide

/-- The identity `Σ a χ(1) = 3` of the expansion, `(q² − q + 1) + (q³ + 1) = (q + 1)² (q − 1) + 3`, on `q = k + 1` for `k < n`. -/
def degreeSweep (n : Nat) : Bool :=
  (List.range n).all (fun k => let q := k + 1; (q * q - q + 1) + (q ^ 3 + 1) == (q + 1) ^ 2 * (q - 1) + 3)

/-- 46:C19 — the identity `Σ a χ(1) = 3 = w(1)` swept over `1 ≤ q ≤ 2000`. -/
theorem degree_identity : degreeSweep 2000 = true := by
  decide +kernel

/-- The gap of the transfer tally on one frame, on the degrees: `d₂ = (q + 1) d₁`, `d₃ = (q + 1)(q² − 1)` and `0 < d₁ < d₂ < d₃`,
so the eigenvalues `1/d₁ > 1/d₂ > 1/d₃` of the step have the gap `d₁/d₂ = 1/(q + 1)`; and the degrees are `1, 1, −1` modulo `q`,
so the three multipliers `1/d₁, 1/d₂, −1/d₃` of one plaquette reduce to `1`. -/
def gapOK (q : Nat) : Bool :=
  let (d1, d2, d3) := degs q; let c : Int := (q : Nat)
  d2 == ((q + 1 : Nat) : Int) * d1 && d3 == ((q + 1 : Nat) : Int) * ((q * q - 1 : Nat) : Int) &&
  0 < d1 && d1 < d2 && d2 < d3 && d1 % c == 1 && d2 % c == 1 && (d3 + 1) % c == 0

/-- 46:C20 — the gap of the transfer tally is `1/(q + 1)` on the seven frames of 46:C19: `1/14`, `1/174`, `1/1550` on the Subjects. -/
theorem ring_gap :
    (gapOK 3 = true ∧ gapOK 4 = true ∧ gapOK 5 = true ∧ gapOK 7 = true ∧ gapOK 13 = true ∧ gapOK 173 = true ∧ gapOK 1549 = true) ∧
    ((degs 13).2.1 = 14 * (degs 13).1 ∧ (degs 173).2.1 = 174 * (degs 173).1 ∧ (degs 1549).2.1 = 1550 * (degs 1549).1) := by
  decide

section Plane
open FRC.Extension

variable {ν : Shell p}

/-- The conjugation of the quadratic extension is additive. -/
theorem planeConj_add (z z' : Ext p ν) : Ext.conj (z + z') = Ext.conj z + Ext.conj z' :=
  Ext.ext rfl (Shell.neg_add_rev _ _)

/-- The reduced tally of the ring in the quadratic extension `K` of a Subject, at boundary classes with the reduced character
values `a₁, a₂, a₃` at `h₁` and `b₁, b₂, b₃` at `h₂`: `Σ aᵢ · conj bᵢ`. Every coefficient reads `1`, and a character takes at
`h⁻¹` the conjugate of its value at `h`. -/
def planeTally (a1 a2 a3 b1 b2 b3 : Ext p ν) : Ext p ν :=
  a1 * Ext.conj b1 + a2 * Ext.conj b2 + a3 * Ext.conj b3

/-- 46:C20 — the reduced tally of the ring on pairs `a + b√ν`, for every modulus `p` and every `ν`; for a nonsquare `ν` of a
Subject the pairs are its quadratic extension `K`. The six arguments are reduced character values that take at `h⁻¹` the
conjugate of their value at `h`; that they do is the table's identity, checked class by class in the ledger file. (1) The
conjugate of the reduced tally is the tally formed at the conjugate values. (2) The product of the two is the norm of the
reduced tally, an element of the shell. -/
theorem ring_tally_plane (a1 a2 a3 b1 b2 b3 : Ext p ν) :
    Ext.conj (planeTally a1 a2 a3 b1 b2 b3)
      = planeTally (Ext.conj a1) (Ext.conj a2) (Ext.conj a3) (Ext.conj b1) (Ext.conj b2) (Ext.conj b3) ∧
    planeTally a1 a2 a3 b1 b2 b3
        * planeTally (Ext.conj a1) (Ext.conj a2) (Ext.conj a3) (Ext.conj b1) (Ext.conj b2) (Ext.conj b3)
      = Ext.ofShell (Ext.norm (planeTally a1 a2 a3 b1 b2 b3)) := by
  have h : Ext.conj (planeTally a1 a2 a3 b1 b2 b3)
      = planeTally (Ext.conj a1) (Ext.conj a2) (Ext.conj a3) (Ext.conj b1) (Ext.conj b2) (Ext.conj b3) := by
    unfold planeTally
    rw [planeConj_add, planeConj_add, Ext.conj_mul, Ext.conj_mul, Ext.conj_mul]
  exact ⟨h, by rw [← h]; exact Ext.mul_conj _⟩

end Plane

/-- The reduced tally at `h₁ = s₁`, with the reduced characters `1`, `2 + 2⁻¹`, `0`, and at `h₂` of the eigenvalues `√2`,
`−√2/2`, `−1`, with the reduced characters `−1`, `√2/2`, `0`, on a Subject `p` where `2` is a nonsquare; `h` is the residue of
`2⁻¹`. -/
def planeExample (p : Nat) [Pos p] (h : Shell p) : FRC.Extension.Ext p 2 :=
  planeTally 1 (FRC.Extension.Ext.ofShell (2 + h)) 0 (FRC.Extension.Ext.ofShell (-1)) ⟨0, h⟩ 0

/-- 46:C20 — the tally of the ring at a boundary class with eigenvalues outside the shell, on the three Subjects, in
`K = F_p(√2)` on pairs `(a, b) = a + b√2`. (1) `2` is a nonsquare, by Euler's criterion, and the residues of `2⁻¹`. (2) The
eigenvalues `√2`, `−√2/2`, `−1` of `h₂`: their product is `1`, the second is the inverse of the conjugate of the first, the third
times the first is its conjugate, and the first plus the second is `√2/2`. (3) The reduced tally is `−1 − (5/4)√2`: `(12, 2)`,
`(172, 42)`, `(1548, 386)`, outside the shell, with the second coordinate the residue of `−5/4`. (4) Its norm, the reduced
paired weight, is `6`, `106`, `966`, the residue of `−17/8`. Every power is taken by repeated multiplication of residues. -/
theorem ring_tally_outside_shell :
    ((2 : Shell 13) ^ 6 + 1 = 0 ∧ (2 : Shell 173) ^ 86 + 1 = 0 ∧ (2 : Shell 1549) ^ 774 + 1 = 0) ∧
    ((2 : Shell 13) * 7 = 1 ∧ (2 : Shell 173) * 87 = 1 ∧ (2 : Shell 1549) * 775 = 1) ∧
    ((planePoint 13 0 1 * planePoint 13 0 (-7) * planePoint 13 (-1) 0 = 1 ∧ FRC.Extension.Ext.conj (planePoint 13 0 1) * planePoint 13 0 (-7) = 1 ∧
        planePoint 13 (-1) 0 * planePoint 13 0 1 = FRC.Extension.Ext.conj (planePoint 13 0 1) ∧ planePoint 13 0 1 + planePoint 13 0 (-7) = planePoint 13 0 7) ∧
      (planePoint 173 0 1 * planePoint 173 0 (-87) * planePoint 173 (-1) 0 = 1 ∧ FRC.Extension.Ext.conj (planePoint 173 0 1) * planePoint 173 0 (-87) = 1 ∧
        planePoint 173 (-1) 0 * planePoint 173 0 1 = FRC.Extension.Ext.conj (planePoint 173 0 1) ∧ planePoint 173 0 1 + planePoint 173 0 (-87) = planePoint 173 0 87) ∧
      (planePoint 1549 0 1 * planePoint 1549 0 (-775) * planePoint 1549 (-1) 0 = 1 ∧ FRC.Extension.Ext.conj (planePoint 1549 0 1) * planePoint 1549 0 (-775) = 1 ∧
        planePoint 1549 (-1) 0 * planePoint 1549 0 1 = FRC.Extension.Ext.conj (planePoint 1549 0 1) ∧ planePoint 1549 0 1 + planePoint 1549 0 (-775) = planePoint 1549 0 775)) ∧
    (planeExample 13 7 = planePoint 13 12 2 ∧ planeExample 173 87 = planePoint 173 172 42 ∧ planeExample 1549 775 = planePoint 1549 1548 386) ∧
    ((planeExample 13 7).im ≠ 0 ∧ (planeExample 173 87).im ≠ 0 ∧ (planeExample 1549 775).im ≠ 0) ∧
    ((4 : Shell 13) * 2 + 5 = 0 ∧ (4 : Shell 173) * 42 + 5 = 0 ∧ (4 : Shell 1549) * 386 + 5 = 0) ∧
    (FRC.Extension.Ext.norm (planeExample 13 7) = 6 ∧ FRC.Extension.Ext.norm (planeExample 173 87) = 106 ∧
      FRC.Extension.Ext.norm (planeExample 1549 775) = 966) ∧
    ((8 : Shell 13) * 6 + 17 = 0 ∧ (8 : Shell 173) * 106 + 17 = 0 ∧ (8 : Shell 1549) * 966 + 17 = 0) := by
  decide +kernel

/-- 46:C21 — the spectrum in `2π = p − 1` on the three Subjects, `π = 6, 86, 774`: `d₁ = 4π² + 2π + 1`, `d₂ = (2π + 2) d₁` and
`d₃ = 8π(π + 1)²`, so the gap of the transfer tally is `1/(2π + 2)`; and `2π + 2` has the residue `1` on the shell. -/
theorem spectrum_in_pi :
    (13 = 2 * 6 + 1 ∧ 173 = 2 * 86 + 1 ∧ 1549 = 2 * 774 + 1) ∧
    ((degs 13).1 = 4 * 6 * 6 + 2 * 6 + 1 ∧ (degs 173).1 = 4 * 86 * 86 + 2 * 86 + 1 ∧
      (degs 1549).1 = 4 * 774 * 774 + 2 * 774 + 1) ∧
    ((degs 13).2.1 = (2 * 6 + 2) * (degs 13).1 ∧ (degs 173).2.1 = (2 * 86 + 2) * (degs 173).1 ∧
      (degs 1549).2.1 = (2 * 774 + 2) * (degs 1549).1) ∧
    ((degs 13).2.2 = 8 * 6 * (6 + 1) * (6 + 1) ∧ (degs 173).2.2 = 8 * 86 * (86 + 1) * (86 + 1) ∧
      (degs 1549).2.2 = 8 * 774 * (774 + 1) * (774 + 1)) ∧
    ((2 * 6 + 2) % 13 = 1 ∧ (2 * 86 + 2) % 173 = 1 ∧ (2 * 774 + 2) % 1549 = 1) := by
  decide

/-- 46:C22 — the product channels, the arithmetic of the counts. The binomial inversion of the compact counts `1, 1, 2, 6, 23`
gives the fixed dimensions `0, 1, 2, 8` of `8^{⊗n}` on a Subject, and of the instance's counts `1, 1, 2, 11, 92` gives `7` and `57`.
A fixed subspace of dimension `2` has `p² + 1` invariant lines, `170`, `29930`, `2399402` on the Subjects; on the instance
`(4^d − 1)/3` gives `5`, `5461`, `21845` for `d = 2, 7, 8`; and the degree `8` lies in the window `2p − 1` of the Subject `13`. -/
theorem product_channel_counts :
    ((1 : Int) - 1 = 0 ∧ (2 : Int) - 2 * 1 + 1 = 1 ∧ (6 : Int) - 3 * 2 + 3 * 1 - 1 = 2 ∧ (23 : Int) - 4 * 6 + 6 * 2 - 4 * 1 + 1 = 8) ∧
    ((11 : Int) - 3 * 2 + 3 * 1 - 1 = 7 ∧ (92 : Int) - 4 * 11 + 6 * 2 - 4 * 1 + 1 = 57) ∧
    (13 * 13 + 1 = 170 ∧ 173 * 173 + 1 = 29930 ∧ 1549 * 1549 + 1 = 2399402) ∧
    ((13 * 13 - 1) * 170 = 13 * 13 * 13 * 13 - 1 ∧ 13 * 13 * 13 * 13 + 13 * 13 + 1 = 28731) ∧
    ((4 ^ 2 - 1) / 3 = 5 ∧ (4 ^ 7 - 1) / 3 = 5461 ∧ (4 ^ 8 - 1) / 3 = 21845) ∧
    (8 ≤ 2 * 13 - 1) := by
  decide

/-- The residues of `χ₁, χ₂, χ₃` on a frame element with the eigenvalues `μ, 1, μ⁻¹` of a Subject `p`, from the table's
entries: the degrees at `μ = 1`; `(1 − q)a + a⁻²`, `(q + 1)a` and `0` at `a = −1`, the eigenvalues `−1, −1, 1`; and `1`,
`μ + μ⁻¹`, `0` elsewhere. Here `q = p` and `mui` is `μ⁻¹`. -/
def ubChars (p mu mui : Nat) : Nat × Nat × Nat :=
  if mu == 1 then ((p * p - p + 1) % p, (p * p * p + 1) % p, ((p + 1) * (p + 1) * (p - 1)) % p)
  else if mu == p - 1 then (((p - 1) + 1) % p, (p * p - (p + 1)) % p, 0)
  else (1, (mu + mui) % p, 0)

/-- The tally's residue at the boundary classes of `x` and `y`; the three multipliers of a step are `1` on the shell. -/
def ubTally (p x xi y yi : Nat) : Nat :=
  let (a1, a2, a3) := ubChars p x xi
  let (b1, b2, b3) := ubChars p y yi
  (a1 * b1 + a2 * b2 + a3 * b3) % p

/-- The five powers `1 + xy + (xy)⁻¹ + x y⁻¹ + x⁻¹ y`. -/
def ubFive (p x xi y yi : Nat) : Nat := (1 + (x * y) % p + (xi * yi) % p + (x * yi) % p + (xi * y) % p) % p

/-- A length is regular when neither boundary class is that of `1` or of `−1`. -/
def ubRegular (p x y : Nat) : Bool := x != 1 && x != p - 1 && y != 1 && y != p - 1

/-- On every regular length among the next `fuel` steps the tally is the five powers. -/
def ubSweep (p gj gji gk gki : Nat) : Nat → Nat → Nat → Nat → Nat → Bool
  | 0, _, _, _, _ => true
  | fuel + 1, x, xi, y, yi =>
    let x' := (x * gj) % p; let xi' := (xi * gji) % p; let y' := (y * gk) % p; let yi' := (yi * gki) % p
    (!(ubRegular p x' y') || ubTally p x' xi' y' yi' == ubFive p x' xi' y' yi') && ubSweep p gj gji gk gki fuel x' xi' y' yi'

/-- The tally at the next `fuel` lengths. -/
def ubValues (p gj gji gk gki : Nat) : Nat → Nat → Nat → Nat → Nat → List Nat
  | 0, _, _, _, _ => []
  | fuel + 1, x, xi, y, yi =>
    let x' := (x * gj) % p; let xi' := (xi * gji) % p; let y' := (y * gk) % p; let yi' := (yi * gki) % p
    ubTally p x' xi' y' yi' :: ubValues p gj gji gk gki fuel x' xi' y' yi'

/-- The lengths among the next `fuel` that are not regular; `n` counts the steps taken. -/
def ubOthers (p gj gk : Nat) : Nat → Nat → Nat → Nat → List Nat
  | 0, _, _, _ => []
  | fuel + 1, n, x, y =>
    let x' := (x * gj) % p; let y' := (y * gk) % p
    if ubRegular p x' y' then ubOthers p gj gk fuel (n + 1) x' y' else (n + 1) :: ubOthers p gj gk fuel (n + 1) x' y'

/-- 46:C23 — the tally of the ring with the same boundary links at every step, of the eigenvalues `g^{±j}, 1` and `g^{±k}, 1` with
`g = 2` and `(j, k) = (1, 2)`; after `n` steps the boundary classes are those of `x = 2^n` and `y = 4^n`. (1) The inverses of `2`
and `4` on the three Subjects. (2) On `13` the tally at the lengths `1` to `12`. (3) On the Subjects `13`, `173`, `1549` the tally
is the five powers at every regular length of the drive's cycle. (4) The other lengths: four on each Subject, the multiples of `3`,
`43` and `387`. (5) At the length of the cycle the boundary links are units and the tally is `3`. Every product is reduced at once;
the largest numeral formed is the degree `(p + 1)²(p − 1)`. -/
theorem uniform_boundary_tally :
    ((2 * 7) % 13 = 1 ∧ (4 * 10) % 13 = 1 ∧ (2 * 87) % 173 = 1 ∧ (4 * 130) % 173 = 1 ∧
      (2 * 775) % 1549 = 1 ∧ (4 * 1162) % 1549 = 1) ∧
    ubValues 13 2 7 4 10 12 1 1 1 1 = [10, 0, 0, 2, 5, 12, 5, 2, 0, 0, 10, 3] ∧
    (ubSweep 13 2 7 4 10 12 1 1 1 1 = true ∧ ubSweep 173 2 87 4 130 172 1 1 1 1 = true ∧
      ubSweep 1549 2 775 4 1162 1548 1 1 1 1 = true) ∧
    (ubOthers 13 2 4 12 0 1 1 = [3, 6, 9, 12] ∧ ubOthers 173 2 4 172 0 1 1 = [43, 86, 129, 172] ∧
      ubOthers 1549 2 4 1548 0 1 1 = [387, 774, 1161, 1548]) ∧
    (ubTally 13 1 1 1 1 = 3 ∧ ubTally 173 1 1 1 1 = 3 ∧ ubTally 1549 1 1 1 1 = 3) := by
  decide +kernel

/-- The residue of `k!` modulo `p`, every product reduced at once. -/
def wrFact (p : Nat) : Nat → Nat
  | 0 => 1
  | k + 1 => (wrFact p k * (k + 1)) % p

/-- 46:C24 — what a reading keeps of the window. (1) The pair `(1, 13)` has `13!/(840 · 120 · 24) = 2574 = 13 · 198` invariants (the
hook formula on `(5, 4, 4)`), so the count reads `0` on the Subject `13`. (2) On the Subjects `13`, `173`, `1549` the factorial
`(p − 1)!` reads `p − 1`, and `2` and `3` have inverses: the factors `2`, `3` and `1, …, p − 1` of the denominators of the series'
coefficients below `ϑ^p` are units of the shell, and these coefficients are computed in its arithmetic. (3) `p!` reads `0`: from
`ϑ^p` on no reading is stated. -/
theorem window_readings : (6227020800 = 2574 * (840 * 120 * 24) ∧ 2574 = 13 * 198) ∧
    (wrFact 13 12 = 12 ∧ wrFact 173 172 = 172 ∧ wrFact 1549 1548 = 1548) ∧
    ((2 * 7) % 13 = 1 ∧ (3 * 9) % 13 = 1 ∧ (2 * 87) % 173 = 1 ∧ (3 * 58) % 173 = 1 ∧
      (2 * 775) % 1549 = 1 ∧ (3 * 1033) % 1549 = 1) ∧
    (wrFact 13 13 = 0 ∧ wrFact 173 173 = 0 ∧ wrFact 1549 1549 = 0) := by decide +kernel

/-- The residue of the tally of three rings on common links at three classes of the split torus, of the eigenvalues `x, 1, x⁻¹`,
`y, 1, y⁻¹` and `z, 1, z⁻¹`: the three characters read `1`, `x + x⁻¹` and `0`, and the triples of the first two characters have
`1`, `0`, `n122` and `n222` invariants. -/
def trTally (p n122 n222 x xi y yi z zi : Nat) : Nat :=
  let cx := (x + xi) % p; let cy := (y + yi) % p; let cz := (z + zi) % p
  (1 + n122 * ((cx * cy) % p + (cx * cz) % p + (cy * cz) % p) + (n222 % p) * (((cx * cy) % p * cz) % p)) % p

/-- The expression `1 + n122 (c_x c_y + c_x c_z + c_y c_z)` with `c_m = m + m⁻¹`. -/
def trReading (p n122 x xi y yi z zi : Nat) : Nat :=
  let cx := (x + xi) % p; let cy := (y + yi) % p; let cz := (z + zi) % p
  (1 + n122 * ((cx * cy) % p + (cx * cz) % p + (cy * cz) % p)) % p

/-- The three classes are regular when none is that of `1` or of `−1`. -/
def trRegular (p x y z : Nat) : Bool := x != 1 && x != p - 1 && y != 1 && y != p - 1 && z != 1 && z != p - 1

/-- At every one of the next `fuel` lengths whose three classes are regular the tally is the expression. -/
def trSweep (p n122 n222 gj gji gk gki gl gli : Nat) : Nat → Nat → Nat → Nat → Nat → Nat → Nat → Bool
  | 0, _, _, _, _, _, _ => true
  | fuel + 1, x, xi, y, yi, z, zi =>
    let x' := (x * gj) % p; let xi' := (xi * gji) % p; let y' := (y * gk) % p; let yi' := (yi * gki) % p
    let z' := (z * gl) % p; let zi' := (zi * gli) % p
    (!(trRegular p x' y' z') || trTally p n122 n222 x' xi' y' yi' z' zi' == trReading p n122 x' xi' y' yi' z' zi') &&
      trSweep p n122 n222 gj gji gk gki gl gli fuel x' xi' y' yi' z' zi'

/-- The lengths among the next `fuel` whose three classes are regular, each with its residue; `n` counts the steps taken. -/
def trValues (p n122 gj gji gk gki gl gli : Nat) : Nat → Nat → Nat → Nat → Nat → Nat → Nat → Nat → List (Nat × Nat)
  | 0, _, _, _, _, _, _, _ => []
  | fuel + 1, n, x, xi, y, yi, z, zi =>
    let x' := (x * gj) % p; let xi' := (xi * gji) % p; let y' := (y * gk) % p; let yi' := (yi * gki) % p
    let z' := (z * gl) % p; let zi' := (zi * gli) % p
    if trRegular p x' y' z' then
      (n + 1, trReading p n122 x' xi' y' yi' z' zi') :: trValues p n122 gj gji gk gki gl gli fuel (n + 1) x' xi' y' yi' z' zi'
    else trValues p n122 gj gji gk gki gl gli fuel (n + 1) x' xi' y' yi' z' zi'

/-- 46:C25 — three rings on common links, each with the same boundary link at every step, of the eigenvalues `g^{±j}, 1` with `g = 2` and
`j = 1, 2, 3`; after `n` steps the boundary classes are those of `2^n`, `4^n` and `8^n`. (1) The inverses of `8` on the three Subjects.
(2) The count of invariants of the second character alone, `p` on `13` and `1549` and `3p` on `173`, has the residue `0`. (3) On
`13` the regular lengths and their residues. (4) On the Subjects `13`, `173`, `1549` the tally is the expression at every regular
length of the drive's cycle. (5) The first length reads `6`, `25` and `616`. Every product is reduced at once. -/
theorem three_rings_reading :
    ((8 * 5) % 13 = 1 ∧ (8 * 65) % 173 = 1 ∧ (8 * 581) % 1549 = 1) ∧
    (13 % 13 = 0 ∧ (3 * 173) % 173 = 0 ∧ 1549 % 1549 = 0) ∧
    trValues 13 2 2 7 4 10 8 5 12 0 1 1 1 1 1 1 = [(1, 6), (5, 9), (7, 9), (11, 6)] ∧
    (trSweep 13 2 13 2 7 4 10 8 5 12 1 1 1 1 1 1 = true ∧ trSweep 173 4 519 2 87 4 130 8 65 172 1 1 1 1 1 1 = true ∧
      trSweep 1549 2 1549 2 775 4 1162 8 581 1548 1 1 1 1 1 1 = true) ∧
    (trReading 13 2 2 7 4 10 8 5 = 6 ∧ trReading 173 4 2 87 4 130 8 65 = 25 ∧
      trReading 1549 2 2 775 4 1162 8 581 = 616) := by decide +kernel

/-! ## The series on the shell (46:C26) -/

/-- The integers `h_k` of `d_R c_R = Σ h_k ϑ^k/k!`, `k < m`, from the counts `n_k` and `d_k`:
`h_k = n_k − Σ_{j=1}^{k} C(k, j) d_j h_{k−j}`, a recursion with no division. -/
def hurwitzH (n d : List Int) : Nat → List Int
  | 0 => []
  | k + 1 =>
    let h := hurwitzH n d k
    h ++ [nth 0 n k - (List.range k).foldl (fun s j => s + ((choose k (j + 1) : Nat) : Int) * nth 0 d (j + 1) * nth 0 h (k - (j + 1))) 0]

/-- The two truncated sums of `c₃` at channel unity on the shell: `Σ_{k<m} n_k/(3 k!)` and `Σ_{k<m} d_k/k!`. -/
def truncSums (E EC : List Nat) (m : Nat) : Shell p × Shell p :=
  ((List.range m).foldl (fun (s : Shell p) (k : Nat) => s + Shell.ofNat (nth 0 EC k) * invS 3 * invS (factS k)) 0,
   (List.range m).foldl (fun (s : Shell p) (k : Nat) => s + Shell.ofNat (nth 0 E k) * invS (factS k)) 0)

/-- 46:C26 — the series on the shell. (1) The integers `h_k` of `3c₃` and of `8c₈` for `k < 8`, from the counts. (2) `p!` reads `0`
on the three laboratory Subjects, so the `p`-th power of the stiffness reads `0` in the divided-power algebra of the series. (3) On the Subject `13`
at channel unity the sum of the coefficients of `c₃` below `ϑ¹³` reads `6`, and the quotient of the two truncated sums reads `4`. -/
theorem shell_series_readings :
    (hurwitzH [0, 1, 1, 6, 15, 65, 231, 973] [1, 0, 2, 2, 12, 30, 130, 462] 8 = [0, 1, 1, 0, -5, -15, 21, 413] ∧
     hurwitzH [0, 0, 2, 4, 24, 80, 372, 1512] [1, 0, 2, 2, 12, 30, 130, 462] 8 = [0, 0, 2, 4, 0, -40, -148, 252]) ∧
    (wrFact 13 13 = 0 ∧ wrFact 173 173 = 0 ∧ wrFact 1549 1549 = 0) ∧
    ((c3Series (p := 13) [1, 0, 2, 2, 12, 30, 130, 462, 1946, 7980, 34776, 153120, 694056]
        [0, 1, 1, 6, 15, 65, 231, 973, 3990, 17388, 76560, 347028, 1597167] 13).foldl (fun (s x : Shell 13) => s + x) 0 = 6 ∧
     (truncSums (p := 13) [1, 0, 2, 2, 12, 30, 130, 462, 1946, 7980, 34776, 153120, 694056]
        [0, 1, 1, 6, 15, 65, 231, 973, 3990, 17388, 76560, 347028, 1597167] 13).1 *
       invS (truncSums (p := 13) [1, 0, 2, 2, 12, 30, 130, 462, 1946, 7980, 34776, 153120, 694056]
        [0, 1, 1, 6, 15, 65, 231, 973, 3990, 17388, 76560, 347028, 1597167] 13).2 = 4) := by
  decide +kernel

/-- The product of two points of the plane `F_p(√2)`, pairs `(a, b) = a + b√2`, every product reduced at once. -/
def noMul (p : Nat) (z w : Nat × Nat) : Nat × Nat :=
  ((z.1 * w.1 + 2 * (z.2 * w.2)) % p, (z.1 * w.2 + z.2 * w.1) % p)

/-- The sum of two points of the plane. -/
def noAdd (p : Nat) (z w : Nat × Nat) : Nat × Nat := ((z.1 + w.1) % p, (z.2 + w.2) % p)

/-- The conjugate of a point; on the norm-one cycle it is the inverse. -/
def noConj (p : Nat) (z : Nat × Nat) : Nat × Nat := (z.1, (p - z.2) % p)

/-- The norm of a point, a residue of the shell. -/
def noNorm (p : Nat) (z : Nat × Nat) : Nat := (z.1 * z.1 + (p - (2 * (z.2 * z.2)) % p)) % p

/-- The power `z^n` by repeated multiplication. -/
def noPow (p : Nat) (z : Nat × Nat) : Nat → Nat × Nat
  | 0 => (1, 0)
  | n + 1 => noMul p (noPow p z n) z

/-- A point of the norm-one cycle is central in the frame when its cube is `1`. -/
def noCentral (p : Nat) (x : Nat × Nat) : Bool := noMul p (noMul p x x) x == (1, 0)

/-- The reductions of the three characters at the class of the eigenvalues `x, x, x⁻²`, `x` of norm one: `x + x⁻²`, `x`, `0` off
the centre, and `x`, `x`, `−x` on it, where the degrees read `1`, `1`, `−1`. -/
def noChars (p : Nat) (x : Nat × Nat) : (Nat × Nat) × (Nat × Nat) × (Nat × Nat) :=
  let xi := noConj p x
  if noCentral p x then (x, x, ((p - x.1) % p, (p - x.2) % p)) else (noAdd p x (noMul p xi xi), x, (0, 0))

/-- The reduced tally of the ring at the boundary classes of `x` and `y`: the characters at `x` times those at `y⁻¹`; every
coefficient reads `1`. -/
def noTally (p : Nat) (x y : Nat × Nat) : Nat × Nat :=
  let (a1, a2, a3) := noChars p x
  let (b1, b2, b3) := noChars p (noConj p y)
  noAdd p (noAdd p (noMul p a1 b1) (noMul p a2 b2)) (noMul p a3 b3)

/-- The four powers `2 x y⁻¹ + x y² + x⁻² y⁻¹ + x⁻² y²`. -/
def noFour (p : Nat) (x y : Nat × Nat) : Nat × Nat :=
  let xi := noConj p x; let yi := noConj p y
  let xy := noMul p x yi
  noAdd p (noAdd p (noAdd p xy xy) (noMul p x (noMul p y y)))
    (noAdd p (noMul p (noMul p xi xi) yi) (noMul p (noMul p xi xi) (noMul p y y)))

/-- A length is regular when neither boundary class is central. -/
def noRegular (p : Nat) (x y : Nat × Nat) : Bool := !(noCentral p x) && !(noCentral p y)

/-- On every regular length among the next `fuel` steps the reduced tally is the four powers. -/
def noSweep (p : Nat) (uj uk : Nat × Nat) : Nat → Nat × Nat → Nat × Nat → Bool
  | 0, _, _ => true
  | fuel + 1, x, y =>
    let x' := noMul p x uj; let y' := noMul p y uk
    (!(noRegular p x' y') || noTally p x' y' == noFour p x' y') && noSweep p uj uk fuel x' y'

/-- The reduced tally at the next `fuel` lengths. -/
def noValues (p : Nat) (uj uk : Nat × Nat) : Nat → Nat × Nat → Nat × Nat → List (Nat × Nat)
  | 0, _, _ => []
  | fuel + 1, x, y =>
    let x' := noMul p x uj; let y' := noMul p y uk
    noTally p x' y' :: noValues p uj uk fuel x' y'

/-- The lengths among the next `fuel` that are not regular; `n` counts the steps taken. -/
def noOthers (p : Nat) (uj uk : Nat × Nat) : Nat → Nat → Nat × Nat → Nat × Nat → List Nat
  | 0, _, _, _ => []
  | fuel + 1, n, x, y =>
    let x' := noMul p x uj; let y' := noMul p y uk
    if noRegular p x' y' then noOthers p uj uk fuel (n + 1) x' y' else (n + 1) :: noOthers p uj uk fuel (n + 1) x' y'

/-- The reductions of the three characters at the class of the eigenvalues `x, 1, x⁻¹` of the split torus, `x` a residue of the
shell with the inverse `xi`: `1`, `x + x⁻¹`, `0`; the degrees `1`, `1`, `−1` at `x = 1`; and `0`, `−1`, `0` at `x = −1`. -/
def mxChars (p x xi : Nat) : Nat × Nat × Nat :=
  if x == 1 then (1, 1, p - 1) else if x == p - 1 then (0, p - 1, 0) else (1, (x + xi) % p, 0)

/-- The reduced tally with one link on each torus: the characters at the class of `x` on the split torus times those at `y⁻¹`
on the norm-one cycle. -/
def mxTally (p x xi : Nat) (y : Nat × Nat) : Nat × Nat :=
  let (a1, a2, a3) := mxChars p x xi
  let (b1, b2, b3) := noChars p (noConj p y)
  noAdd p (noAdd p (noMul p (a1, 0) b1) (noMul p (a2, 0) b2)) (noMul p (a3, 0) b3)

/-- The expression `y² + (1 + x + x⁻¹) y⁻¹`. -/
def mxReading (p x xi : Nat) (y : Nat × Nat) : Nat × Nat :=
  noAdd p (noMul p y y) (noMul p ((1 + x + xi) % p, 0) (noConj p y))

/-- A length is regular when `x` is neither `1` nor `−1` and `y` is not central. -/
def mxRegular (p x : Nat) (y : Nat × Nat) : Bool := x != 1 && x != p - 1 && !(noCentral p y)

/-- On every regular length among the next `fuel` steps the reduced tally is the expression. -/
def mxSweep (p gj gji : Nat) (uk : Nat × Nat) : Nat → Nat → Nat → Nat × Nat → Bool
  | 0, _, _, _ => true
  | fuel + 1, x, xi, y =>
    let x' := (x * gj) % p; let xi' := (xi * gji) % p; let y' := noMul p y uk
    (!(mxRegular p x' y') || mxTally p x' xi' y' == mxReading p x' xi' y') && mxSweep p gj gji uk fuel x' xi' y'

/-- The reduced tally with one link on each torus at the next `fuel` lengths. -/
def mxValues (p gj gji : Nat) (uk : Nat × Nat) : Nat → Nat → Nat → Nat × Nat → List (Nat × Nat)
  | 0, _, _, _ => []
  | fuel + 1, x, xi, y =>
    let x' := (x * gj) % p; let xi' := (xi * gji) % p; let y' := noMul p y uk
    mxTally p x' xi' y' :: mxValues p gj gji uk fuel x' xi' y'

/-- The power `z^n` by squaring, on `fuel` binary digits of `n`. -/
def noPowB (p : Nat) : Nat → Nat × Nat → Nat → Nat × Nat
  | 0, _, _ => (1, 0)
  | fuel + 1, z, n =>
    if n == 0 then (1, 0)
    else
      let h := noPowB p fuel (noMul p z z) (n / 2)
      if n % 2 == 1 then noMul p h z else h

/-- The reduced tally with one link on each torus at the length `n`: `x = g^n` with the inverse `gi^n`, and `y = u^n`. -/
def mxAt (p g gi : Nat) (u : Nat × Nat) (n : Nat) : Nat × Nat :=
  mxTally p (g ^ n % p) (gi ^ n % p) (noPowB p 24 u n)

/-- The length `L` reads `3` and none of the listed lengths does. With the lengths `L/r`, `r` the prime divisors of a period
`L`, this makes `L` the least period: a proper divisor of `L` that is a period divides some `L/r`, which would then read `3`. -/
def mxLeast (p g gi : Nat) (u : Nat × Nat) (L : Nat) (ds : List Nat) : Bool :=
  mxAt p g gi u L == (3, 0) && ds.all (fun d => mxAt p g gi u d != (3, 0))

/-- 46:C27 — the tally of the ring with a norm-one link at every step, of the eigenvalues `u^j, u^j, u^{−2j}` and
`u^k, u^k, u^{−2k}` with `(j, k) = (1, 2)`, in the plane `F_p(√2)` on pairs `(a, b) = a + b√2`; after `n` steps the boundary
classes are those of `x = u^n` and `y = u^{2n}`. (1) `u = 3 + 2√2` on `13` and `173` and `u = 1459 + 1276√2` on `1549` have the
norm `1` and the order `p + 1`. (2) On `13` the reduced tally at the lengths `1` to `14`, and its norms, the reduced paired
weight. (3) On the Subjects `13`, `173`, `1549` the reduced tally is the four powers at every regular length of the norm-one
cycle. (4) The other lengths: the multiples of `7`, `29` and `775`. (5) With unit links the tally is `3`. (6) One link on each
torus, of the eigenvalues `2, 1, 2⁻¹` and `u, u, u⁻²`: on `13` the first six lengths, the expression `y² + (1 + x + x⁻¹) y⁻¹` at
every regular length of the whole period `84`, and the value `3` at the length `84`; on `173` and `1549` the expression at
every regular length among the first `1740` and `3100`. (7) The period `L = 84`, `14964`, `1199700` of (6) is the least one on
the three Subjects: the length `L` reads `3`, and no length `L/r`, `r` a prime divisor of `L`, reads `3`. Every product is
reduced at once. -/
theorem norm_one_link_tally :
    ((noNorm 13 (3, 2) = 1 ∧ noPow 13 (3, 2) 14 = (1, 0) ∧ noPow 13 (3, 2) 7 ≠ (1, 0) ∧ noPow 13 (3, 2) 2 ≠ (1, 0)) ∧
      (noNorm 173 (3, 2) = 1 ∧ noPow 173 (3, 2) 174 = (1, 0) ∧ noPow 173 (3, 2) 87 ≠ (1, 0) ∧ noPow 173 (3, 2) 58 ≠ (1, 0) ∧
        noPow 173 (3, 2) 6 ≠ (1, 0)) ∧
      (noNorm 1549 (1459, 1276) = 1 ∧ noPow 1549 (1459, 1276) 1550 = (1, 0) ∧ noPow 1549 (1459, 1276) 775 ≠ (1, 0) ∧
        noPow 1549 (1459, 1276) 310 ≠ (1, 0) ∧ noPow 1549 (1459, 1276) 50 ≠ (1, 0))) ∧
    noValues 13 (3, 2) (noMul 13 (3, 2) (3, 2)) 14 (1, 0) (1, 0)
      = [(11, 2), (2, 4), (7, 6), (8, 4), (2, 3), (7, 1), (12, 0), (7, 12), (2, 10), (8, 9), (7, 7), (2, 9), (11, 11), (3, 0)] ∧
    (noValues 13 (3, 2) (noMul 13 (3, 2) (3, 2)) 14 (1, 0) (1, 0)).map (noNorm 13)
      = [9, 11, 3, 6, 12, 8, 1, 8, 12, 6, 3, 11, 9, 9] ∧
    (noSweep 13 (3, 2) (noMul 13 (3, 2) (3, 2)) 14 (1, 0) (1, 0) = true ∧
      noSweep 173 (3, 2) (noMul 173 (3, 2) (3, 2)) 174 (1, 0) (1, 0) = true ∧
      noSweep 1549 (1459, 1276) (noMul 1549 (1459, 1276) (1459, 1276)) 1550 (1, 0) (1, 0) = true) ∧
    (noOthers 13 (3, 2) (noMul 13 (3, 2) (3, 2)) 14 0 (1, 0) (1, 0) = [7, 14] ∧
      noOthers 173 (3, 2) (noMul 173 (3, 2) (3, 2)) 174 0 (1, 0) (1, 0) = [29, 58, 87, 116, 145, 174] ∧
      noOthers 1549 (1459, 1276) (noMul 1549 (1459, 1276) (1459, 1276)) 1550 0 (1, 0) (1, 0) = [775, 1550]) ∧
    (noTally 13 (1, 0) (1, 0) = (3, 0) ∧ noTally 173 (1, 0) (1, 0) = (3, 0) ∧ noTally 1549 (1, 0) (1, 0) = (3, 0)) ∧
    (mxValues 13 2 7 (3, 2) 6 1 1 (1, 0) = [(8, 5), (0, 7), (5, 10), (10, 11), (11, 0), (3, 2)] ∧
      mxSweep 13 2 7 (3, 2) 84 1 1 (1, 0) = true ∧ mxSweep 173 2 87 (3, 2) 1740 1 1 (1, 0) = true ∧
      mxSweep 1549 2 775 (1459, 1276) 3100 1 1 (1, 0) = true ∧
      (mxValues 13 2 7 (3, 2) 84 1 1 (1, 0)).getLast? = some (3, 0)) ∧
    (mxLeast 13 2 7 (3, 2) 84 [42, 28, 12] = true ∧ mxLeast 173 2 87 (3, 2) 14964 [7482, 4988, 516, 348] = true ∧
      mxLeast 1549 2 775 (1459, 1276) 1199700 [599850, 399900, 239940, 38700, 27900] = true) := by
  decide +kernel


end FRC.YangMills
