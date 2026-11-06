import FrcCore.Frame
import FrcCore.Orbit
import FrcCore.Sum
import FrcCore.Instances
import FrcCore.Theme.Extension

/-!
# The Dirac theme — the square-class arithmetic, the coefficient field and the worked shells, no axioms

The finite content of *Schrödinger and Dirac Dynamics over Finite Substrate* (8-dirac, tree `8-dirac-20260709`;
the paper module `FrcCore/Dirac.lean` since the migration of 1 November 2026) from first principles, on every frame
`(τ; 0, 1, g)` of capacity `κ`, `p = 4κ + 1`: the square class is chronon parity — a residue `g^m` is a square
exactly when `m` is even (B5); the drive `g` and its inverse `g^{p−2}` are nonsquares, the quarter-turn
`i = −g^κ = g^{3κ}` is a square exactly when `κ` is even, and `2`, `2⁻¹`, `−2` are squares exactly when `κ` is
even — so on every κ-even shell the drive is the only nonsquare among the frame's named residues (B3); the
factorisation `ν = g = 2⁻¹·(2g)` on every shell, the cofactor `2g` a square exactly when `κ` is odd, the product
odd always (B4); the coefficient field `K = 𝔽_p[w]/(w² − ν)` on components with its conjugation and norm,
`z z̄ = N(z)`, `N(gz) = g² N(z)` (B6); the latitude identities `4κ ≡ −1`, `κ = −4⁻¹`, `1 + κ = 3·4⁻¹`, `2κ = −2⁻¹`,
`g^κ = −i` and the ladder `κ < κ + 1 ≤ 2κ` (F2); the drive's spectrum on the characters — the eigenvalue
`g^{(p−2)k}` inverse to `g^k`, the isotropy `Σ_j g^{2jk} = 0` unless `(p − 1) ∣ 2k`, and the two exceptional
lines `k = 0, 2κ` with eigenvalues `±1` (F3, F6); the sector separation — `g^{p−2}` primitive of order `p − 1`,
and `u² = 1 ⇒ u = ±1`, the meeting of the drive cycle and the norm-one cycle (F4, F6, X1). Decided by the kernel
on the laboratory Subjects `𝔽₁₃`, `𝔽₁₇₃` and `𝔽₁₅₄₉` (all with the drive `2`; the standard set of 5 November 2026, the
shell `𝔽₅` dropped): the Clifford relations, the spin conjugation with `A = 10`, `B = 2` on `𝔽₁₃`, `A = 170`, `B = 2` on
`𝔽₁₇₃` and `A = 1546`, `B = 2` on `𝔽₁₅₄₉`, the transported gammas (D2, D6, D7, D12); the spinor twist `X = γ⁰γ¹γ³` with `X² = ν`, its commutations, `(γ^μ)† X = −X γ^μ` and the failure of
the `γ⁰`-twist (D9, X4); the norm-one cycle `|N¹| = 14` on `𝔽₁₃` and `174` on `𝔽₁₇₃`, an order-three element on
`𝔽₁₇₃` and none on `𝔽₁₃` (D5, D12); the Cayley step of `H = −Δ` on `𝔽₁₃`, `U¹³ = I ≠ U` at `α = w` and `α = 6w`
(C6, E4); the potential propagators of order `14` on `𝔽₁₃` and `174` on `𝔽₁₇₃`, the least common multiple of the
phase orders (E4); the power-map image counts on `𝔽₁₃` (E2); the zero counts `2353`, `2041` on `𝔽₁₃` (B7); the unit-norm circle of `p − 1` points (F2); the named residues of the two Subjects (B3,
D12); the laboratory Carrier's `c = 171 106` with `c² = 2⁻¹` and `2⁻¹·12 = 6` (B4). Every declaration is checked
to depend on no axiom (`check_core_axioms.py`).

Since the ledger migration (task LM17) the coefficient field is the extension theme's `FRC.Extension.Ext p ν`
(`Theme/Extension.lean`) and chronon parity is the frame theme's (`Orbit.lean`); every old name stays as an alias.
-/

namespace FRC.Dirac

open FRC.Shell

section
open FRC.Extension
open FRC.Shell.Frame (two_mul_mod mod_two_of_mod_four_mul mod_n_mod_two parity_iff drive_nonsquare mod_two_cases succ_mod_two_eq_zero_iff inv_drive_odd inv_drive_nonsquare)

/-! ## The square class is chronon parity (8:B5, B3, B4) -/
section parity
variable {p : Nat} [Pos p] {κ : Nat} {g : Shell p}

/-- 8:B3 — the quarter-turn is `g^{3κ}` (`i = −g^κ`, `−1 = g^{2κ}`). -/
theorem quarterTurn_eq_pow (F : Frame p κ g) : Frame.quarterTurn g κ = g ^ (3 * κ) := by
  unfold Frame.quarterTurn
  rw [← Shell.neg_one_mul, ← F.half_period, ← Shell.pow_add]
  show g ^ (2 * κ + κ) = g ^ (3 * κ)
  rw [show 2 * κ + κ = 3 * κ from (Nat.succ_mul 2 κ).symm]

/-- 8:B3 — `i` is a square exactly when the capacity is even (the eighth root of unity exists iff
`8 ∣ p − 1`). -/
theorem quarter_class (F : Frame p κ g) :
    (∃ y : Shell p, y * y = Frame.quarterTurn g κ) ↔ κ % 2 = 0 := by
  rw [quarterTurn_eq_pow F]
  refine (parity_iff F (3 * κ)).trans ?_
  have : 3 * κ = 2 * κ + κ := (Nat.succ_mul 2 κ)
  rw [this, FRC.Nat.add_mul_mod_self_left κ κ 2 (Nat.zero_lt_succ 1)]

/-- 8:B3 — `2`, `2⁻¹` and `−2` are squares exactly when the capacity is even (the second supplementary
law at tier 0, 14-entropy's `two_is_square_iff`, and `−1 = (g^κ)²`). -/
theorem two_class (F : Frame p κ g) {h : Shell p} (hh : 2 * h = 1) :
    ((∃ r : Shell p, r * r = 2) ↔ κ % 2 = 0) ∧ ((∃ r : Shell p, r * r = h) ↔ κ % 2 = 0) ∧
    ((∃ r : Shell p, r * r = -2) ↔ κ % 2 = 0) := by
  have key : (∃ r : Shell p, r * r = 2) ↔ κ % 2 = 0 := by
    refine (FRC.Shell.Frame.two_is_square_iff F).trans ?_
    constructor
    · rintro ⟨m, hm⟩; rw [hm]; exact two_mul_mod m
    · intro h0
      match FRC.Nat.mod_spec 2 (Nat.zero_lt_succ 1) κ with
      | ⟨q, hq⟩ => exact ⟨q, by rw [h0, Nat.add_zero] at hq; exact hq⟩
  have hsq : (g ^ κ) * (g ^ κ) = -1 := by rw [← Shell.pow_two]; exact (F.quarter_turn_order).1
  refine ⟨key, ?_, ?_⟩
  · refine Iff.trans ?_ key
    constructor
    · rintro ⟨r, hr⟩
      refine ⟨2 * r, ?_⟩
      rw [FRC.Shell.mul_mul_mul_comm, hr, Shell.mul_assoc, hh, Shell.mul_one]
    · rintro ⟨r, hr⟩
      refine ⟨r * h, ?_⟩
      rw [FRC.Shell.mul_mul_mul_comm, hr]
      calc (2 : Shell p) * (h * h) = 2 * h * h := (Shell.mul_assoc _ _ _).symm
        _ = h := by rw [hh, Shell.one_mul]
  · refine Iff.trans ?_ key
    constructor
    · rintro ⟨r, hr⟩
      refine ⟨g ^ κ * r, ?_⟩
      rw [FRC.Shell.mul_mul_mul_comm, hsq, hr, Shell.neg_mul_neg, Shell.one_mul]
    · rintro ⟨r, hr⟩
      refine ⟨g ^ κ * r, ?_⟩
      rw [FRC.Shell.mul_mul_mul_comm, hsq, hr, Shell.neg_one_mul]

/-- 8:B4, 8:X2 — the factorisation of the temporal coefficient: `ν = g = 2⁻¹·(2g)` exactly on every shell
(`h = 2⁻¹`), and the cofactor `2g` is a square exactly when `κ` is odd — the product `g` odd always (Corollary
`coefficient-factors`); the one-way coefficient is the odd step `g`, the two-way constant the Carrier's. -/
theorem nu_factorisation (F : Frame p κ g) {h : Shell p} (hh : 2 * h = 1) :
    h * (2 * g) = g ∧ ((∃ y : Shell p, y * y = 2 * g) ↔ κ % 2 = 1) := by
  refine ⟨by rw [← Shell.mul_assoc, Shell.mul_comm h 2, hh, Shell.one_mul], ?_⟩
  obtain ⟨m, _, hm⟩ := F.eq_pow_of_ne_zero F.two_ne_zero
  have h2g : (2 : Shell p) * g = g ^ (m + 1) := by rw [Shell.pow_succ, hm]
  rw [h2g]
  refine (parity_iff F (m + 1)).trans ((succ_mod_two_eq_zero_iff m).trans ?_)
  have hm2 : (∃ r : Shell p, r * r = 2) ↔ m % 2 = 0 := by rw [← hm]; exact parity_iff F m
  replace hm2 : κ % 2 = 0 ↔ m % 2 = 0 := (two_class F hh).1.symm.trans hm2
  constructor
  · intro h1
    rcases mod_two_cases κ with hk | hk
    · exact absurd (hm2.1 hk) (by rw [h1]; exact fun e => Nat.noConfusion e)
    · exact hk
  · intro h1
    rcases mod_two_cases m with hm' | hm'
    · exact absurd (hm2.2 hm') (by rw [h1]; exact fun e => Nat.noConfusion e)
    · exact hm'

end parity

/-! ## The latitude identities (8:F2) -/
section latitude
variable {p : Nat} [Pos p] {κ : Nat} {g : Shell p}

/-- 8:F2 — the ladder `1, …, 2κ`: `κ + 1`, the first rung past the midpoint `κ`, is still a rung. -/
theorem ladder (F : Frame p κ g) : κ + 1 ≤ 2 * κ := by
  rw [Nat.two_mul]; exact Nat.add_le_add_left F.cap_pos κ

/-- 8:F2 — `4κ ≡ −1` on the shell (`4κ = p − 1`), so `κ = −4⁻¹` and the energy radius `1 + κ = 3·4⁻¹`. -/
theorem four_kappa (F : Frame p κ g) {q : Shell p} (hq : 4 * q = 1) :
    (4 : Shell p) * ofNat κ = -1 ∧ (ofNat κ : Shell p) = -q ∧ (1 : Shell p) + ofNat κ = 3 * q := by
  have h4 : (4 : Shell p) * ofNat κ = -1 := by
    have := F.two_pi
    unfold Frame.halfPeriod at this
    rw [← FRC.Nat.mul_assoc, ← Frame.ofNat_mul] at this
    exact this
  have hk : (ofNat κ : Shell p) = -q := by
    calc (ofNat κ : Shell p) = 1 * ofNat κ := (Shell.one_mul _).symm
      _ = 4 * q * ofNat κ := by rw [hq]
      _ = q * (4 * ofNat κ) := by rw [Shell.mul_comm 4 q, Shell.mul_assoc]
      _ = -q := by rw [h4, ← Shell.mul_neg, Shell.mul_one]
  refine ⟨h4, hk, ?_⟩
  have h3 : (4 : Shell p) = 3 + 1 :=
    Shell.ext (by rw [Shell.val_add, Shell.val_lit, Shell.val_lit, Shell.val_one,
      FRC.Nat.mod_add_mod _ _ _ Shell.hp, FRC.Nat.add_mod_mod _ _ _ Shell.hp])
  rw [hk, ← hq, h3, Shell.right_distrib, Shell.one_mul, Shell.add_assoc, Shell.add_neg, Shell.add_zero]

/-- 8:F2 — the terminal latitude: `π = 2κ = −2⁻¹`; the quarter-cycle shift `m ↦ m + κ` on the
ladder is multiplication by `g^κ = −i` (`quarterTurn_eq_pow`, `i = −g^κ` by definition). -/
theorem terminal_latitude (F : Frame p κ g) {h : Shell p} (hh : 2 * h = 1) :
    (ofNat (2 * κ) : Shell p) = -h := by
  have h2 : (2 : Shell p) * ofNat (2 * κ) = -1 := by
    have := F.two_pi
    unfold Frame.halfPeriod at this
    rw [← Frame.ofNat_mul] at this
    exact this
  calc (ofNat (2 * κ) : Shell p) = 1 * ofNat (2 * κ) := (Shell.one_mul _).symm
    _ = 2 * h * ofNat (2 * κ) := by rw [hh]
    _ = h * (2 * ofNat (2 * κ)) := by rw [Shell.mul_comm 2 h, Shell.mul_assoc]
    _ = -h := by rw [h2, ← Shell.mul_neg, Shell.mul_one]

end latitude

/-! ## The free evolution is the drive (8:F3) and the two sectors (8:F4) -/
section drive
variable {p : Nat} [Pos p] {κ : Nat} {g : Shell p}

/-- 8:F3, 8:F6 — the drive pullback on the characters: with `y = g⁻¹`, `χ_k(g^{j}) = y^k · χ_k(g^{j+1})` for every
`j, k` — the winding-`k` mode acquires the phase `g^{−k}` per chronon, so the drive is semisimple with the whole
drive cycle as its spectrum (Theorem `zonal` (2), Proposition `two-spectra`). -/
theorem drive_eigen {y : Shell p} (hy : g * y = 1) (j k : Nat) :
    y ^ k * g ^ ((j + 1) * k) = g ^ (j * k) := by
  rw [Nat.add_mul, Nat.one_mul, Shell.pow_add, Shell.mul_comm (g ^ (j * k)), ← Shell.mul_assoc,
    ← Shell.mul_pow, Shell.mul_comm y g, hy, Shell.one_pow, Shell.one_mul]

/-- 8:F3 — the exceptional eigenvalue: `k = 2κ` gives `g^{−2κ} = −1` (and `k = 0` gives `1`) — the
intersection `N¹ ∩ μ_{p−1} = {±1}` of the norm-one torus with the phase cycle. -/
theorem exceptional_eigen (F : Frame p κ g) {y : Shell p} (hy : g * y = 1) : y ^ (2 * κ) = -1 := by
  have h1 : y ^ (2 * κ) * g ^ (2 * κ) = 1 := by
    rw [← Shell.mul_pow, Shell.mul_comm y g, hy, Shell.one_pow]
  rw [F.half_period] at h1
  calc y ^ (2 * κ) = y ^ (2 * κ) * (-1 * -1) := by rw [Shell.neg_mul_neg, Shell.one_mul, Shell.mul_one]
    _ = y ^ (2 * κ) * -1 * -1 := (Shell.mul_assoc _ _ _).symm
    _ = -1 := by rw [h1, Shell.one_mul]

/-- 8:F3 — isotropy: the character line `χ_k` is isotropic, `Σ_j χ_k(g^j)² = Σ_j g^{2jk} = 0`, unless
`(p − 1) ∣ 2k`; on the two exceptional lines the sum is `p − 1 = −1 ≠ 0` (Theorem `zonal` (3)). -/
theorem isotropy (F : Frame p κ g) (k : Nat) :
    ((2 * k) % (p - 1) ≠ 0 → sumRange (fun j => g ^ (j * k) * g ^ (j * k)) (p - 1) = 0) ∧
    ((2 * k) % (p - 1) = 0 → sumRange (fun j => g ^ (j * k) * g ^ (j * k)) (p - 1) = -1) := by
  have e : ∀ j, g ^ (j * k) * g ^ (j * k) = (g ^ (2 * k)) ^ j := fun j => by
    rw [← Shell.pow_add, ← Shell.pow_mul]
    show g ^ (j * k + j * k) = g ^ (2 * k * j)
    rw [← Nat.two_mul, Nat.mul_assoc 2 k j, Nat.mul_comm k j]
  rw [sum_congr (p - 1) (fun j _ => e j)]
  constructor
  · intro hk
    have hx : g ^ (2 * k) ≠ 1 := fun h1 => hk (F.mod_eq_zero_of_pow_eq_one h1)
    have hn : (g ^ (2 * k)) ^ (p - 1) = 1 := by rw [Shell.pow_mul_comm, F.pow_n, Shell.one_pow]
    exact Frame.geom_sum_eq_zero F (p - 1) hn hx
  · intro hk
    rw [sum_congr (p - 1) (fun j _ => by rw [F.pow_eq_one_of_mod hk, Shell.one_pow]),
      sum_const, Shell.mul_one]
    exact Frame.ofNat_n F

/-- 8:F4, 8:F6, 8:X1, 8:E8 — sector separation: the inverse of the drive is primitive of order `p − 1` (`ord(g⁻¹) = p − 1`,
so the free evolution is no Cayley step, whose scalar phases have order dividing `p + 1`), and the norm-one
cycle meets the base field in `{±1}` alone (`u² = 1 ⇒ u = ±1`): the two spectra meet in the two signs. -/
theorem sector_separation (F : Frame p κ g) {y : Shell p} (hy : g * y = 1) :
    IsPrimitive y (p - 1) ∧ ∀ u : Shell p, u * u = 1 → u = 1 ∨ u = -1 := by
  refine ⟨⟨?_, fun l hl hl0 h1 => ?_⟩, fun u hu => F.sq_eq_one hu⟩
  · rw [← Shell.one_pow (p - 1), ← hy, Shell.mul_pow, F.pow_n, Shell.one_mul]
  · have h2 : g ^ l = 1 := by
      calc g ^ l = g ^ l * 1 := (Shell.mul_one _).symm
        _ = g ^ l * y ^ l := by rw [h1]
        _ = 1 := by rw [← Shell.mul_pow, hy, Shell.one_pow]
    exact F.prim.2 l hl hl0 h2

end drive

/-! ## The worked shells, decided by the kernel -/
section decided
variable {p : Nat} [Pos p]

/-- `Σ_{a<p} Σ_{b<p} [f a b]`, the count of pairs of residues satisfying `f`. -/
def count2 (p : Nat) (f : Nat → Nat → Bool) : Nat :=
  (List.range p).foldl (fun acc a => (List.range p).foldl (fun acc b => if f a b then acc + 1 else acc) acc) 0

/-- The count of quadruples of residues satisfying `f`. -/
def count4 (p : Nat) (f : Nat → Nat → Nat → Nat → Bool) : Nat :=
  (List.range p).foldl (fun acc a => (List.range p).foldl (fun acc b => (List.range p).foldl (fun acc c =>
    (List.range p).foldl (fun acc d => if f a b c d then acc + 1 else acc) acc) acc) acc) 0

/-- 8:D5 — the number of points of the norm-one torus `N¹ = {a² − ν b² = 1}` on the shell. -/
def normOneCount (p : Nat) [Pos p] (ν : Shell p) : Nat :=
  count2 p fun a b => decide (Ext.norm (⟨ofNat a, ofNat b⟩ : Ext p ν) = 1)

/-- 8:F2 — the number of points of the unit-norm circle `a² + b² = 1` of the framed-complex chart. -/
def unitCircleCount (p : Nat) [Pos p] : Nat :=
  count2 p fun a b => decide ((ofNat a : Shell p) * ofNat a + ofNat b * ofNat b = 1)

/-- 8:B7 — the zero count of the Euclidean form `t² + x² + y² + z²`. -/
def euclidZeros (p : Nat) [Pos p] : Nat :=
  count4 p fun t x y z => decide ((ofNat t : Shell p) * ofNat t + ofNat x * ofNat x + ofNat y * ofNat y +
    ofNat z * ofNat z = 0)

/-- 8:B7 — the zero count of the Lorentzian form `−ν t² + x² + y² + z²`. -/
def lorentzZeros (p : Nat) [Pos p] (ν : Shell p) : Nat :=
  count4 p fun t x y z => decide (-(ν * ((ofNat t : Shell p) * ofNat t)) + ofNat x * ofNat x +
    ofNat y * ofNat y + ofNat z * ofNat z = 0)

/-- 8:B7 [value] — on `𝔽₁₃` the Euclidean form has `13³ + 13² − 13 = 2353` zeros and the Lorentzian form (`ν = g = 2`)
has `13³ − 13² + 13 = 2041`: the hyperbolic and the elliptic form part on the base shell. -/
theorem zeros13 : euclidZeros 13 = 2353 ∧ lorentzZeros 13 2 = 2041 := by decide +kernel

/-- 8:D5, 8:D12, 8:D19, 8:C5, 8:F2, 8:F6 [value] — the norm-one cycle: `|N¹| = 14 = p + 1` on `𝔽₁₃` and `174` on `𝔽₁₇₃`
(both `ν = g = 2`); the unit-norm circle of the chart has `p − 1` points: `12` and `172` (8:F2). -/
theorem torus_counts :
    normOneCount 13 2 = 14 ∧ normOneCount 173 2 = 174 ∧ unitCircleCount 13 = 12 ∧ unitCircleCount 173 = 172 := by
  decide +kernel

end decided

/-! ## Matrices over the coefficient field, the gammas and the Cayley step, decided by the kernel -/
section matrices
variable {p : Nat} [Pos p] {ν : Shell p}

/-- A matrix over `K` as a list of rows. -/
abbrev Mat (p : Nat) [Pos p] (ν : Shell p) := List (List (Ext p ν))

namespace Mat

/-- The `j`-th element of a list, `d` beyond its end (structural; Lean's `List.getD` carries `propext`). -/
def nth {α : Type} (d : α) : List α → Nat → α
  | [], _ => d
  | a :: _, 0 => a
  | _ :: l, n + 1 => nth d l n
def dot (r c : List (Ext p ν)) : Ext p ν := (List.zipWith (· * ·) r c).foldl (· + ·) 0
def col (A : Mat p ν) (j : Nat) : List (Ext p ν) := A.map fun r => nth 0 r j
def transpose (A : Mat p ν) : Mat p ν := (List.range (A.headD []).length).map (col A)
def mul (A B : Mat p ν) : Mat p ν :=
  let Bt := transpose B
  A.map fun r => Bt.map fun c => dot r c
def add (A B : Mat p ν) : Mat p ν := List.zipWith (fun r s => List.zipWith (· + ·) r s) A B
def neg (A : Mat p ν) : Mat p ν := A.map fun r => r.map (- ·)
def smul (c : Ext p ν) (A : Mat p ν) : Mat p ν := A.map fun r => r.map (c * ·)
def ident (n : Nat) : Mat p ν := (List.range n).map fun i => (List.range n).map fun j => if i = j then 1 else 0
/-- Powers by squaring. -/
def pow (A : Mat p ν) (n : Nat) : Nat → Mat p ν
  | 0 => ident n
  | e + 1 => mul (pow A n e) A
/-- The conjugate transpose (Frobenius on the entries). -/
def dagger (A : Mat p ν) : Mat p ν := (transpose A).map fun r => r.map Ext.conj

instance : Mul (Mat p ν) := ⟨mul⟩
instance : Add (Mat p ν) := ⟨add⟩
instance : Neg (Mat p ν) := ⟨neg⟩

end Mat

open Mat

/-- The gamma matrices of `(eq:gamma-definition)` over `K`, given the quarter-turn `i` of the shell:
`γ⁰ = i w β`, `γ^k = i ρ^k` (with `i² = −1`, so `γ²`'s entries are `∓i² = ±1`). -/
def gamma0 (i : Shell p) : Mat p ν :=
  let iw : Ext p ν := ⟨0, i⟩
  [[0, 0, iw, 0], [0, 0, 0, iw], [iw, 0, 0, 0], [0, iw, 0, 0]]
def gamma1 (i : Shell p) : Mat p ν :=
  let ii : Ext p ν := ⟨i, 0⟩
  [[0, 0, 0, ii], [0, 0, ii, 0], [0, -ii, 0, 0], [-ii, 0, 0, 0]]
def gamma2 (i : Shell p) : Mat p ν :=
  let ii : Ext p ν := ⟨i, 0⟩
  [[0, 0, 0, -(ii * ii)], [0, 0, ii * ii, 0], [0, ii * ii, 0, 0], [-(ii * ii), 0, 0, 0]]
def gamma3 (i : Shell p) : Mat p ν :=
  let ii : Ext p ν := ⟨i, 0⟩
  [[0, 0, ii, 0], [0, 0, 0, -ii], [-ii, 0, 0, 0], [0, ii, 0, 0]]
def gamma (i : Shell p) : Nat → Mat p ν
  | 0 => gamma0 i
  | 1 => gamma1 i
  | 2 => gamma2 i
  | _ => gamma3 i
/-- `η = diag(−ν, 1, 1, 1)`. -/
def eta (ν : Shell p) : Nat → Nat → Ext p ν
  | 0, 0 => -(⟨ν, 0⟩ : Ext p ν)
  | 1, 1 => 1
  | 2, 2 => 1
  | 3, 3 => 1
  | _, _ => 0

/-- 8:D2 — the Clifford relations `γ^μ γ^ν + γ^ν γ^μ = 2 η_{μν} I₄`, all sixteen. -/
def clifford (ν : Shell p) (i : Shell p) : Bool :=
  (List.range 4).all fun μ => (List.range 4).all fun μ' =>
    decide (gamma i μ * gamma i μ' + gamma i μ' * gamma i μ = smul (2 * eta ν μ μ') (ident 4 : Mat p ν))

/-- 8:D2, 8:D17 [value] — the Clifford relations hold on `𝔽₁₃` (`ν = 2`, `i = 5`), `𝔽₁₇₃` (`ν = 2`, `i = 93`) and
`𝔽₁₅₄₉` (`ν = 2`, `i = 1461`). -/
theorem clifford_values : clifford (2 : Shell 13) 5 = true ∧ clifford (2 : Shell 173) 93 = true ∧
    clifford (2 : Shell 1549) 1461 = true := by decide +kernel

/-- The spin lift `S(x, y) = x I₄ + y γ⁰γ¹` and its inverse `δ⁻¹(x I₄ − y γ⁰γ¹)`, `δ = x² − ν y²`, with the
inverse of `δ` supplied. -/
def spinLift (i x y : Shell p) : Mat p ν :=
  smul ⟨x, 0⟩ (ident 4) + smul ⟨y, 0⟩ (gamma0 i * gamma1 i)
def spinLiftInv (i x y dinv : Shell p) : Mat p ν :=
  smul ⟨dinv, 0⟩ (smul ⟨x, 0⟩ (ident 4) + smul ⟨-y, 0⟩ (gamma0 i * gamma1 i))

/-- 8:D6, 8:D16, 8:D12 — the spin conjugation `S⁻¹γ⁰S = Aγ⁰ + νBγ¹`, `S⁻¹γ¹S = Bγ⁰ + Aγ¹`, `γ², γ³` fixed, and
the transported gammas `Sγ⁰S⁻¹ = Aγ⁰ − νBγ¹`, `Sγ¹S⁻¹ = −Bγ⁰ + Aγ¹`, at the lift `(x, y)` with the entries
`A`, `B` given. -/
def spinConj (ν i x y dinv A B : Shell p) : Bool :=
  let S : Mat p ν := spinLift i x y
  let Si : Mat p ν := spinLiftInv i x y dinv
  let a : Ext p ν := ⟨A, 0⟩
  let b : Ext p ν := ⟨B, 0⟩
  let n : Ext p ν := ⟨ν, 0⟩
  decide (Si * S = ident 4) &&
  decide (Si * gamma0 i * S = smul a (gamma0 i) + smul (n * b) (gamma1 i)) &&
  decide (Si * gamma1 i * S = smul b (gamma0 i) + smul a (gamma1 i)) &&
  decide (Si * gamma2 i * S = gamma2 i) && decide (Si * gamma3 i * S = gamma3 i) &&
  decide (S * gamma0 i * Si = smul a (gamma0 i) + smul (-(n * b)) (gamma1 i)) &&
  decide (S * gamma1 i * Si = smul (-b) (gamma0 i) + smul a (gamma1 i))

/-- 8:D6, 8:D16, 8:D12 [value] — on `𝔽₁₃` (`ν = g = 2`, `x = y = 1`, `δ = −1`): `A = 10`, `B = 2`,
`γ̂⁰ = 10γ⁰ − 4γ¹`, `γ̂¹ = −2γ⁰ + 10γ¹`; on `𝔽₁₇₃` (`ν = g = 2`, `i = 93`, `δ = −1`): `A = 170`, `B = 2`,
`γ̂⁰ = 170γ⁰ − 4γ¹`, `γ̂¹ = −2γ⁰ + 170γ¹`; on `𝔽₁₅₄₉` (`i = 1461`, `δ = −1`): `A = 1546`, `B = 2`. -/
theorem spin_conjugation_values :
    spinConj (2 : Shell 13) 5 1 1 12 10 2 = true ∧ spinConj (2 : Shell 173) 93 1 1 172 170 2 = true ∧
    spinConj (2 : Shell 1549) 1461 1 1 1548 1546 2 = true := by
  decide +kernel

/-- 8:D9 — the spinor twist `X = γ⁰γ¹γ³`: Hermitian for the conjugate transpose, `X² = ν I₄`, commuting with
`γ⁰, γ¹, γ³`, anticommuting with `γ²`, and `(γ^μ)† X = −X γ^μ` for every `μ` (so `X⁻¹(γ^μ)†X = −γ^μ`); the
component signs `(γ⁰)† = −γ⁰`, `(γ¹)† = −γ¹`, `(γ²)† = +γ²` (the obstruction), `(γ³)† = −γ³`; and the failure
of the `γ⁰`-twist: `(γ¹)† γ⁰ ≠ −γ⁰ γ¹`. -/
def spinorForm (ν i : Shell p) : Bool :=
  let X : Mat p ν := gamma0 i * gamma1 i * gamma3 i
  let n : Ext p ν := ⟨ν, 0⟩
  decide (dagger X = X) && decide (X * X = smul n (ident 4)) &&
  decide (X * gamma0 i = gamma0 i * X) && decide (X * gamma1 i = gamma1 i * X) &&
  decide (X * gamma3 i = gamma3 i * X) && decide (X * gamma2 i = -(gamma2 i * X)) &&
  (List.range 4).all (fun μ => decide (dagger (gamma i μ) * X = -(X * gamma i μ))) &&
  decide ((dagger (gamma0 i) : Mat p ν) = -(gamma0 i)) && decide ((dagger (gamma1 i) : Mat p ν) = -(gamma1 i)) &&
  decide ((dagger (gamma2 i) : Mat p ν) = gamma2 i) && decide ((dagger (gamma3 i) : Mat p ν) = -(gamma3 i)) &&
  decide ((dagger (gamma1 i) : Mat p ν) * gamma0 i ≠ -(gamma0 i * gamma1 i))

/-- 8:D9, 8:X4 [value] — the spinor form on `𝔽₁₃`, `𝔽₁₇₃` and `𝔽₁₅₄₉`: the `γ⁰`-twist fails and `X = γ⁰γ¹γ³` is the
form the arithmetic forces. -/
theorem spinor_form_values :
    spinorForm (2 : Shell 13) 5 = true ∧ spinorForm (2 : Shell 173) 93 = true ∧ spinorForm (2 : Shell 1549) 1461 = true := by
  decide +kernel

/-- The inverse of a residue by bounded search (`0` when none). -/
def invS (a : Shell p) : Shell p :=
  match (List.range p).find? (fun b => decide (a * ofNat b = 1)) with
  | some b => ofNat b
  | none => 0

/-- A circulant `p × p` matrix over `K` by its first row; the product of two circulants is the cyclic
convolution of their first rows. -/
def cyc (n : Nat) (a b : List (Ext p ν)) : List (Ext p ν) :=
  (List.range n).map fun k =>
    ((List.range n).map fun j => nth 0 a j * nth 0 b ((k + n - j) % n)).foldl (· + ·) 0
def cycId (n : Nat) : List (Ext p ν) := (List.range n).map fun k => if k = 0 then 1 else 0
def cycAdd (a b : List (Ext p ν)) : List (Ext p ν) := List.zipWith (· + ·) a b
def cycSmul (c : Ext p ν) (a : List (Ext p ν)) : List (Ext p ν) := a.map (c * ·)
def cycPow (n : Nat) (a : List (Ext p ν)) : Nat → List (Ext p ν)
  | 0 => cycId n
  | e + 1 => cyc n (cycPow n a e) a

/-- `H = −Δ = 2I − T − T⁻¹` on `𝔽_p`, the kinetic Hamiltonian at unit stiffness, a circulant with first row
`(2, −1, 0, …, 0, −1)`. -/
def kineticRow (p : Nat) [Pos p] (ν : Shell p) : List (Ext p ν) :=
  (List.range p).map fun j => if j = 0 then 2 else if j = 1 ∨ j + 1 = p then -1 else 0

/-- The Cayley step `U = (I − αH)⁻¹(I + αH)` of a nilpotent circulant `H`, the inverse as the series
`Σ_{j≤n} (αH)^j` (exact once `(αH)^n = 0`, which `cayley13` checks). -/
def cayleyRow (α : Ext p ν) (H : List (Ext p ν)) : List (Ext p ν) :=
  let N := cycSmul α H
  let inv := (List.range p).foldl (fun acc _ => cycAdd (cycId p) (cyc p N acc)) (cycId p)
  cyc p inv (cycAdd (cycId p) N)

/-- 8:C6, 8:E4 — on `𝔽₁₃` with `ν = g = 2`: for `α = w` and `α = c = 6w` (`c² = 2⁻¹ = 7`, `(6w)² = 36·2 = 7`),
`(αH)^{13} = 0` (so the series inverse is exact), `U^{13} = I` and `U ≠ I`: the order is exactly `13`, the
translation torus `C_p` (Example `cayley-13`, Theorem `period-dichotomy` (1)). -/
def cayley13 (α : Ext 13 2) : Bool :=
  let H := kineticRow 13 2
  let U := cayleyRow α H
  decide (cycPow 13 (cycSmul α H) 13 = (List.range 13).map fun _ => (0 : Ext 13 2)) &&
  decide (cycPow 13 U 13 = cycId 13) && decide (U ≠ cycId 13)

/-- 8:C6, 8:C15, 8:E4, 8:E7, 8:E8 [value] — the Cayley step of `H = −Δ` on `𝔽₁₃` has order exactly `13` at `α = w` and at
`α = c = 6w` (`c² = 7 = 2⁻¹`): every Cayley orbit on the shell is periodic, here with the period `13` (C15). -/
theorem cayley13_values : cayley13 ⟨0, 1⟩ = true ∧ cayley13 ⟨0, 6⟩ = true ∧
    ((⟨0, 6⟩ : Ext 13 2) * ⟨0, 6⟩ = 7 ∧ (2 : Shell 13) * 7 = 1) := by decide +kernel

/-- The scalar Cayley map `φ(λ) = (1 + wλ)/(1 − wλ)` (`α = w`) on `K`, by the conjugate and the searched
inverse of the norm. -/
def phi (ν : Shell p) (lam : Shell p) : Ext p ν :=
  let num : Ext p ν := ⟨1, lam⟩
  let den : Ext p ν := ⟨1, -lam⟩
  num * Ext.conj den * Ext.ofShell (invS (Ext.norm den))

/-- The order of `u` in the torus, by the running product up to `p + 1` steps (`0` if none). -/
def orderIn (u : Ext p ν) : Nat :=
  go u 1 (p + 1)
where
  go (x : Ext p ν) (e : Nat) : Nat → Nat
    | 0 => 0
    | fuel + 1 => if x = 1 then e else go (x * u) (e + 1) fuel

/-- 8:E4 (2), 8:C5 — the potential propagator `U = diag(φ(V(x)))` for `V = id`: every phase `φ(λ)` has norm
one and `φ(λ)^{p+1} = 1`, and the order of the diagonal is the least common multiple of the phase orders —
`14 = p + 1` on `𝔽₁₃` and `174 = p + 1` on `𝔽₁₇₃`: the bound `p + 1` is attained. -/
def potentialOrder (p : Nat) [Pos p] (ν : Shell p) : Nat :=
  (List.range p).foldl (fun acc l => Nat.lcm acc (orderIn (phi ν (ofNat l)))) 1

def potentialNormOne (p : Nat) [Pos p] (ν : Shell p) : Bool :=
  (List.range p).all fun l => decide (Ext.norm (phi ν (ofNat l)) = 1) && decide ((phi ν (ofNat l)) ^ (p + 1) = 1)

/-- 8:E4, 8:E8 [value] — the potential propagator of `V = id` has order `14 = p + 1` on `𝔽₁₃` and `174` on `𝔽₁₇₃`, the
least common multiple of the phase orders, every phase of norm one. -/
theorem potential_orders : potentialNormOne 13 2 = true ∧ potentialOrder 13 2 = 14 ∧
    potentialNormOne 173 2 = true ∧ potentialOrder 173 2 = 174 := by decide +kernel

/-- 8:D5 [value] — the triality clause: the norm-one cycle of `𝔽₁₇₃` (`174 = 3·58`) carries an element of order
three, and that of `𝔽₁₃` (`14`, `3 ∤ 14`) carries none: `u³ = 1`, `u ≠ 1` with `N(u) = 1`. -/
def hasOrderThree (p : Nat) [Pos p] (ν : Shell p) : Bool :=
  (List.range p).any fun a => (List.range p).any fun b =>
    let u : Ext p ν := ⟨ofNat a, ofNat b⟩
    decide (Ext.norm u = 1) && decide (u ^ 3 = 1) && decide (u ≠ 1)

/-- 8:D5, 8:D12, 8:D19 [value] — an element of order three on the norm-one cycle of `𝔽₁₇₃`, none on that of `𝔽₁₃`. -/
theorem triality_values : hasOrderThree 173 2 = true ∧ hasOrderThree 13 2 = false := by decide +kernel

/-- 8:E5 — the image count of the power map `x ↦ x^ε` on the nonzero residues. -/
def powerImage (p : Nat) [Pos p] (ε : Nat) : Nat :=
  ((List.range p).drop 1).foldl (fun acc y =>
    if ((List.range p).drop 1).any (fun x => decide ((ofNat x : Shell p) ^ ε = ofNat y)) then acc + 1 else acc) 0

/-- 8:E5 [value] — on `𝔽₁₃`: the images of `x ↦ x^ε` have `(p − 1)/gcd(ε, 12)` elements — `12, 6, 4, 3, 2, 1`
for `ε = 1, 2, 3, 4, 6, 12` (loss factors `1, 2, 3, 4, 6, 12`). -/
theorem power_map13 : powerImage 13 1 = 12 ∧ powerImage 13 2 = 6 ∧ powerImage 13 3 = 4 ∧ powerImage 13 4 = 3 ∧
    powerImage 13 6 = 2 ∧ powerImage 13 12 = 1 := by decide +kernel

/-- 8:D12, 8:D19, 8:B3 [value] — the worked shells: on `𝔽₁₃` (`g = 2`, `κ = 3`) the quarter-turn is `i = 5`, `2⁻¹ = 7`,
`e = g^i = 6` and `π = 2κ = 6`, and `2`, `7`, `5`, `6` are nonsquares; on `𝔽₁₇₃` (`g = 2`, `κ = 43`) `i = 93` with
`i² = −1`, `2⁻¹ = 87`, `e = 2^{93} = 45`, `π = 86`, and `2`, `87`, `93`, `45`, `86` are nonsquares; the lift at
`x = y = 1` has `δ = −1` on both, `A = (1 + ν)/δ = 10` and `170`, `B = −2/δ = 2`. -/
theorem shell173_values :
    ((2 : Shell 13) * 7 = 1 ∧ (5 : Shell 13) * 5 = -1 ∧ (2 : Shell 13) ^ 5 = 6 ∧
      ∀ r : Shell 13, r * r ≠ 2 ∧ r * r ≠ 7 ∧ r * r ≠ 5 ∧ r * r ≠ 6) ∧
    ((2 : Shell 173) * 87 = 1 ∧ (93 : Shell 173) * 93 = -1 ∧ (2 : Shell 173) ^ 93 = 45 ∧ (86 : Shell 173) = 2 * 43 ∧
      ∀ r : Shell 173, r * r ≠ 2 ∧ r * r ≠ 87 ∧ r * r ≠ 93 ∧ r * r ≠ 45 ∧ r * r ≠ 86) ∧
    ((-(1 : Shell 13)) * 10 = 1 + 2 ∧ (-(1 : Shell 13)) * 2 = -2 ∧ (-(1 : Shell 173)) * 170 = 1 + 2 ∧
      (-(1 : Shell 173)) * 2 = -2) := by decide +kernel

/-- 8:B4 [value] — the laboratory Carrier `Ω = 2 408 561`: the two-way constant `c = 171 106` is a Carrier residue
with `c² = 2⁻¹ = 1 204 281`, and the two factors compose, `2⁻¹ · (2g) = 1 204 281 · 12 = 6 = g`. -/
theorem carrier_constants :
    (171106 : Shell 2408561) * 171106 = 1204281 ∧ (2 : Shell 2408561) * 1204281 = 1 ∧
    (1204281 : Shell 2408561) * 12 = 6 := by decide +kernel

end matrices

/-! ## Old names (ledger migration, task LM17): the declarations moved to the themes, each under its old name -/
end

section aliases
variable {p : Nat} [Pos p] {κ : Nat} {g : Shell p}

theorem two_mul_mod (l : Nat) : (2 * l) % 2 = 0 :=
  FRC.Shell.Frame.two_mul_mod l

theorem mod_two_of_mod_four_mul (m q : Nat) : (4 * q + m) % 2 = m % 2 :=
  FRC.Shell.Frame.mod_two_of_mod_four_mul m q

theorem mod_n_mod_two (F : Frame p κ g) (m : Nat) : (m % (p - 1)) % 2 = m % 2 :=
  FRC.Shell.Frame.mod_n_mod_two F m

/-- 8:B5, 8:X2 — the square class is chronon parity: on every frame, `g^m` is a square exactly when the drive-step
count `m` is even (Theorem `parity`); registered transport `g²` is even, the one-way step `g` odd. -/
theorem parity_iff (F : Frame p κ g) (m : Nat) : (∃ y : Shell p, y * y = g ^ m) ↔ m % 2 = 0 :=
  FRC.Shell.Frame.parity_iff F m

/-- 8:B3 — the drive is a nonsquare on every frame (`m = 1`). -/
theorem drive_nonsquare (F : Frame p κ g) : ¬ ∃ y : Shell p, y * y = g :=
  FRC.Shell.Frame.drive_nonsquare F

theorem mod_two_cases (m : Nat) : m % 2 = 0 ∨ m % 2 = 1 :=
  FRC.Shell.Frame.mod_two_cases m

theorem succ_mod_two_eq_zero_iff (m : Nat) : (m + 1) % 2 = 0 ↔ m % 2 = 1 :=
  FRC.Shell.Frame.succ_mod_two_eq_zero_iff m

/-- The inverse of the drive is `g^{p−2}`: every `y` with `g y = 1` is an odd power of `g`. -/
theorem inv_drive_odd (F : Frame p κ g) {y : Shell p} (hy : g * y = 1) :
    ∃ l, l < p - 1 ∧ g ^ l = y ∧ l % 2 = 1 :=
  FRC.Shell.Frame.inv_drive_odd F hy

/-- 8:B3, 8:B6 — the reframing flip preserves the class: the inverse of the drive is a nonsquare (an odd
power of `g`), so `[g⁻¹] = [g]`. -/
theorem inv_drive_nonsquare (F : Frame p κ g) {y : Shell p} (hy : g * y = 1) :
    ¬ ∃ r : Shell p, r * r = y :=
  FRC.Shell.Frame.inv_drive_nonsquare F hy

/-- 8:B1 — an element `a + b w` of the coefficient field, on components. -/
@[reducible] def Ext := @FRC.Extension.Ext

namespace Ext
variable {ν : Shell p}

theorem ext' {z z' : Ext p ν} (h1 : z.re = z'.re) (h2 : z.im = z'.im) : z = z' :=
  FRC.Extension.Ext.ext h1 h2

/-- The base field inside `K`. -/
@[reducible] def ofShell (a : Shell p) : Ext p ν :=
  FRC.Extension.Ext.ofShell a

/-- The adjoined root `w`, `w² = ν`. -/
@[reducible] def w : Ext p ν :=
  FRC.Extension.Ext.w

/-- Frobenius conjugation `a + b w ↦ a − b w`. -/
@[reducible] def conj (z : Ext p ν) : Ext p ν :=
  FRC.Extension.Ext.conj z

/-- The norm `N(z) = z z̄ = a² − ν b²`. -/
@[reducible] def norm (z : Ext p ν) : Shell p :=
  FRC.Extension.Ext.norm z

/-- Powers by structural recursion. -/
@[reducible] def pow (z : Ext p ν) : Nat → Ext p ν :=
  FRC.Extension.Ext.pow z

theorem mul_re (z z' : Ext p ν) : (z * z').re = z.re * z'.re + ν * (z.im * z'.im) :=
  FRC.Extension.Ext.mul_re z z'

theorem mul_im (z z' : Ext p ν) : (z * z').im = z.re * z'.im + z.im * z'.re :=
  FRC.Extension.Ext.mul_im z z'

theorem ofShell_re (a : Shell p) : (ofShell a : Ext p ν).re = a :=
  FRC.Extension.Ext.ofShell_re a

theorem ofShell_im (a : Shell p) : (ofShell a : Ext p ν).im = 0 :=
  FRC.Extension.Ext.ofShell_im a

theorem conj_re (z : Ext p ν) : (conj z).re = z.re :=
  FRC.Extension.Ext.conj_re z

theorem conj_im (z : Ext p ν) : (conj z).im = -z.im :=
  FRC.Extension.Ext.conj_im z

/-- `w² = ν`. -/
theorem w_sq : (w : Ext p ν) * w = ofShell ν :=
  FRC.Extension.Ext.w_sq

/-- 8:B6 — the norm is the product with the conjugate: `z z̄ = N(z)`, a base-field element. -/
theorem mul_conj (z : Ext p ν) : z * conj z = ofShell (norm z) :=
  FRC.Extension.Ext.mul_conj z

/-- Conjugation is multiplicative (the Frobenius involution is a ring map). -/
theorem conj_mul (z z' : Ext p ν) : conj (z * z') = conj z * conj z' :=
  FRC.Extension.Ext.conj_mul z z'

/-- 8:B6 — norm growth: `N(c z) = c² N(z)` for every base residue `c`; one chronon of drive multiplies every
norm by `g²`, a square. -/
theorem norm_scale (c : Shell p) (z : Ext p ν) : norm (ofShell c * z) = c * c * norm z :=
  FRC.Extension.Ext.norm_scale c z

end Ext

end aliases


end FRC.Dirac
