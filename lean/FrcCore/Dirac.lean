import FrcCore.Frame
import FrcCore.Sum
import FrcCore.Algebra
import FrcCore.Dimensions
import FrcCore.Entropy
import FrcCore.Instances

/-!
# 8-dirac — the square-class arithmetic, the coefficient field and the worked shells, no axioms

The finite content of *Schrödinger and Dirac Dynamics over Finite Substrate* (tree `8-dirac-20260709`) from
first principles, on every frame `(τ; 0, 1, g)` of capacity `κ`, `p = 4κ + 1`: the square class is chronon
parity — a residue `g^m` is a square exactly when `m` is even (B5); the drive `g` and its inverse `g^{p−2}`
are nonsquares, the quarter-turn `i = −g^κ = g^{3κ}` is a square exactly when `κ` is even, and `2`, `2⁻¹`,
`−2` are squares exactly when `κ` is even — so on every admissibility-class shell the drive is the only
nonsquare among the frame's named residues (B3); the factorisation `ν = g = c²·(2g)` with `c² = 2⁻¹`, the
cofactor `2g` a square exactly when `κ` is odd, the product odd always (B4); the coefficient field
`K = 𝔽_p[w]/(w² − ν)` on components with its conjugation and norm, `z z̄ = N(z)`, `N(gz) = g² N(z)` (B6, A2);
the latitude identities `4κ ≡ −1`, `κ = −4⁻¹`, `1 + κ = 3·4⁻¹`, `2κ = −2⁻¹`, `g^κ = −i` and the ladder
`κ < κ + 1 ≤ 2κ` (F2); the drive's spectrum on the characters — the eigenvalue `g^{(p−2)k}` inverse to `g^k`,
the isotropy `Σ_j g^{2jk} = 0` unless `(p − 1) ∣ 2k`, and the two exceptional lines `k = 0, 2κ` with
eigenvalues `±1` (F3); the sector separation — `g^{p−2}` primitive of order `p − 1`, and `u² = 1 ⇒ u = ±1`
(F4). Decided by the kernel on the worked shells: the Clifford relations, the spin conjugation with `A = 10`,
`B = 2` on `𝔽₁₃` and `A = 15`, `B = 1` on `𝔽₁₇`, the transported gammas (D2, D6, D7, D12); the spinor twist
`X = γ⁰γ¹γ³` with `X² = ν`, its commutations, `(γ^μ)† X = −X γ^μ` and the failure of the `γ⁰`-twist (D9); the
boost torus `|N¹| = 14` on `𝔽₁₃`, `18` on `𝔽₁₇`, an order-three element on `𝔽₁₇` and none on `𝔽₁₃` (D5, D12);
the Cayley step of `H = −Δ` on `𝔽₁₃`, `U¹³ = I ≠ U` at `α = w` and `α = c = 6w` (C6, E4); the potential
propagators of order `14` on `𝔽₁₃` and `18` on `𝔽₁₇`, the least common multiple of the phase orders (E4); the power-map image counts on `𝔽₁₃` (E2); the zero
counts `145`, `105` on `𝔽₅` and `2353`, `2041` on `𝔽₁₃` (B7); the unit-norm circle of `p − 1` points (F2); the
minimal admissible shell `𝔽₁₇` (D12); the laboratory Carrier's `c = 171 106`, `c² = 2⁻¹`, `2⁻¹·12 = 6` (B4).
Every declaration is checked to depend on no axiom (`check_core_axioms.py`).
-/

namespace FRC.Dirac

open FRC.Shell

/-! ## The coefficient field `K = 𝔽_p[w]/(w² − ν)` on components (8:A2, B1) -/
section ext
variable {p : Nat} [Pos p]

/-- 8:B1 — an element `a + b w` of the coefficient field, on components. -/
structure Ext (p : Nat) [Pos p] (ν : Shell p) where
  re : Shell p
  im : Shell p

namespace Ext
variable {ν : Shell p}

theorem ext' {z z' : Ext p ν} (h1 : z.re = z'.re) (h2 : z.im = z'.im) : z = z' := by
  cases z; cases z'; cases h1; cases h2; rfl

instance : DecidableEq (Ext p ν) := fun a b =>
  if h1 : a.re = b.re then
    if h2 : a.im = b.im then isTrue (ext' h1 h2) else isFalse (fun e => h2 (by cases e; rfl))
  else isFalse (fun e => h1 (by cases e; rfl))

/-- The base field inside `K`. -/
def ofShell (a : Shell p) : Ext p ν := ⟨a, 0⟩
/-- The adjoined root `w`, `w² = ν`. -/
def w : Ext p ν := ⟨0, 1⟩
instance (n : Nat) : OfNat (Ext p ν) n := ⟨ofShell (OfNat.ofNat n)⟩
instance : Add (Ext p ν) := ⟨fun z z' => ⟨z.re + z'.re, z.im + z'.im⟩⟩
instance : Neg (Ext p ν) := ⟨fun z => ⟨-z.re, -z.im⟩⟩
instance : Mul (Ext p ν) := ⟨fun z z' => ⟨z.re * z'.re + ν * (z.im * z'.im), z.re * z'.im + z.im * z'.re⟩⟩
/-- Frobenius conjugation `a + b w ↦ a − b w`. -/
def conj (z : Ext p ν) : Ext p ν := ⟨z.re, -z.im⟩
/-- The norm `N(z) = z z̄ = a² − ν b²`. -/
def norm (z : Ext p ν) : Shell p := z.re * z.re + -(ν * (z.im * z.im))
/-- Powers by structural recursion. -/
def pow (z : Ext p ν) : Nat → Ext p ν
  | 0 => 1
  | n + 1 => pow z n * z
instance : Pow (Ext p ν) Nat := ⟨pow⟩

theorem mul_re (z z' : Ext p ν) : (z * z').re = z.re * z'.re + ν * (z.im * z'.im) := rfl
theorem mul_im (z z' : Ext p ν) : (z * z').im = z.re * z'.im + z.im * z'.re := rfl
theorem ofShell_re (a : Shell p) : (ofShell a : Ext p ν).re = a := rfl
theorem ofShell_im (a : Shell p) : (ofShell a : Ext p ν).im = 0 := rfl
theorem conj_re (z : Ext p ν) : (conj z).re = z.re := rfl
theorem conj_im (z : Ext p ν) : (conj z).im = -z.im := rfl

/-- 8:A2 — `w² = ν`. -/
theorem w_sq : (w : Ext p ν) * w = ofShell ν :=
  ext' (by show 0 * 0 + ν * (1 * 1) = ν; rw [Shell.zero_mul, Shell.one_mul, Shell.mul_one, Shell.zero_add])
       (by show 0 * 1 + 1 * 0 = 0; rw [Shell.zero_mul, Shell.mul_zero, Shell.zero_add])

/-- 8:A2 — the norm is the product with the conjugate: `z z̄ = N(z)`, a base-field element. -/
theorem mul_conj (z : Ext p ν) : z * conj z = ofShell (norm z) :=
  ext' (by show z.re * z.re + ν * (z.im * -z.im) = z.re * z.re + -(ν * (z.im * z.im))
           rw [← Shell.mul_neg, ← Shell.mul_neg])
       (by show z.re * -z.im + z.im * z.re = 0
           rw [← Shell.mul_neg, Shell.mul_comm z.im z.re, Shell.neg_add])

/-- 8:A2 — conjugation is multiplicative (the Frobenius involution is a ring map). -/
theorem conj_mul (z z' : Ext p ν) : conj (z * z') = conj z * conj z' :=
  ext' (by show z.re * z'.re + ν * (z.im * z'.im) = z.re * z'.re + ν * (-z.im * -z'.im)
           rw [Shell.neg_mul_neg])
       (by show -(z.re * z'.im + z.im * z'.re) = z.re * -z'.im + -z.im * z'.re
           rw [Shell.neg_add_rev, ← Shell.mul_neg, ← Shell.neg_mul])

/-- 8:B6 — norm growth: `N(c z) = c² N(z)` for every base residue `c`; one chronon of drive multiplies every
norm by `g²`, a square. -/
theorem norm_scale (c : Shell p) (z : Ext p ν) : norm (ofShell c * z) = c * c * norm z := by
  unfold norm
  rw [mul_re, mul_im, ofShell_re, ofShell_im, Shell.zero_mul, Shell.mul_zero, Shell.add_zero,
    Shell.zero_mul, Shell.add_zero, FRC.Entropy.mul_mul_mul_comm, FRC.Entropy.mul_mul_mul_comm c z.im c z.im,
    Shell.mul_left_comm ν (c * c), Shell.left_distrib, ← Shell.mul_neg]

end Ext
end ext

/-! ## The square class is chronon parity (8:B5, B3, B4) -/
section parity
variable {p : Nat} [Pos p] {κ : Nat} {g : Shell p}

theorem two_mul_mod (l : Nat) : (2 * l) % 2 = 0 := by
  rw [← Nat.add_zero (2 * l)]; exact FRC.Nat.add_mul_mod_self_left 0 l 2 (Nat.zero_lt_succ 1)

theorem mod_two_of_mod_four_mul (m q : Nat) : (4 * q + m) % 2 = m % 2 := by
  have : 4 * q + m = 2 * (2 * q) + m := by rw [← FRC.Nat.mul_assoc]
  rw [this, FRC.Nat.add_mul_mod_self_left m (2 * q) 2 (Nat.zero_lt_succ 1)]

theorem mod_n_mod_two (F : Frame p κ g) (m : Nat) : (m % (p - 1)) % 2 = m % 2 := by
  match FRC.Nat.mod_spec (p - 1) F.n_pos m with
  | ⟨q, hq⟩ =>
    have e : m = 4 * (κ * q) + m % (p - 1) := by
      rw [← FRC.Nat.mul_assoc, ← F.n_eq]; exact hq
    calc (m % (p - 1)) % 2 = (4 * (κ * q) + m % (p - 1)) % 2 := (mod_two_of_mod_four_mul _ _).symm
      _ = m % 2 := by rw [← e]

/-- 8:B5 — the square class is chronon parity: on every frame, `g^m` is a square exactly when the drive-step
count `m` is even (Theorem `parity`). -/
theorem parity_iff (F : Frame p κ g) (m : Nat) : (∃ y : Shell p, y * y = g ^ m) ↔ m % 2 = 0 := by
  constructor
  · rintro ⟨y, hy⟩
    have hy0 : y ≠ 0 := fun h0 => F.pow_ne_zero m (by rw [← hy, h0, Shell.mul_zero])
    obtain ⟨l, hl, hgl⟩ := F.eq_pow_of_ne_zero hy0
    have h2 : g ^ (2 * l) = g ^ m := by
      rw [Nat.mul_comm, Shell.pow_mul, Shell.pow_two, hgl]; exact hy
    rw [F.pow_mod, F.pow_mod m] at h2
    have h3 := F.pow_inj (Nat.mod_lt _ F.n_pos) (Nat.mod_lt _ F.n_pos) h2
    rw [← mod_n_mod_two F m, ← h3, mod_n_mod_two F]
    exact two_mul_mod l
  · intro h
    match FRC.Nat.mod_spec 2 (Nat.zero_lt_succ 1) m with
    | ⟨q, hq⟩ =>
      rw [h, Nat.add_zero] at hq
      exact ⟨g ^ q, by rw [hq, Nat.mul_comm, Shell.pow_mul, Shell.pow_two]⟩

/-- 8:B3 — the drive is a nonsquare on every frame (`m = 1`). -/
theorem drive_nonsquare (F : Frame p κ g) : ¬ ∃ y : Shell p, y * y = g := fun ⟨y, hy⟩ =>
  Nat.noConfusion ((parity_iff F 1).1 ⟨y, by rw [Shell.pow_one]; exact hy⟩)

theorem mod_two_cases (m : Nat) : m % 2 = 0 ∨ m % 2 = 1 := by
  have := Nat.mod_lt m (Nat.zero_lt_succ 1)
  match m % 2, this with
  | 0, _ => exact .inl rfl
  | 1, _ => exact .inr rfl
  | k + 2, hk => exact absurd hk (Nat.not_lt_of_le (Nat.le_add_left 2 k))

theorem succ_mod_two_eq_zero_iff (m : Nat) : (m + 1) % 2 = 0 ↔ m % 2 = 1 := by
  rw [FRC.Nat.add_mod m 1 2 (Nat.zero_lt_succ 1)]
  rcases mod_two_cases m with h | h <;> rw [h]
  · exact ⟨fun e => Nat.noConfusion e, fun e => Nat.noConfusion e⟩
  · exact ⟨fun _ => rfl, fun _ => rfl⟩

/-- The inverse of the drive is `g^{p−2}`: every `y` with `g y = 1` is an odd power of `g`. -/
theorem inv_drive_odd (F : Frame p κ g) {y : Shell p} (hy : g * y = 1) :
    ∃ l, l < p - 1 ∧ g ^ l = y ∧ l % 2 = 1 := by
  have hy0 : y ≠ 0 := fun h0 => F.one_ne_zero (by rw [← hy, h0, Shell.mul_zero])
  obtain ⟨l, hl, hgl⟩ := F.eq_pow_of_ne_zero hy0
  refine ⟨l, hl, hgl, ?_⟩
  have h1 : g ^ (l + 1) = 1 := by rw [Shell.pow_succ, hgl, Shell.mul_comm]; exact hy
  have h2 := F.mod_eq_zero_of_pow_eq_one h1
  have h3 : l + 1 = p - 1 := by
    match Nat.lt_or_ge (l + 1) (p - 1) with
    | .inl hlt => exact absurd (by rw [FRC.Nat.mod_eq_of_lt hlt] at h2; exact h2) (Nat.succ_ne_zero l)
    | .inr hge => exact Nat.le_antisymm (Nat.succ_le_of_lt hl) hge
  have h4 : (l + 1) % 2 = 0 := by
    rw [h3, F.n_eq, ← Nat.add_zero (4 * κ), mod_two_of_mod_four_mul]
  exact (succ_mod_two_eq_zero_iff l).1 h4

/-- 8:B3, 8:B6 — the reframing flip preserves the class: the inverse of the drive is a nonsquare (an odd
power of `g`), so `[g⁻¹] = [g]`. -/
theorem inv_drive_nonsquare (F : Frame p κ g) {y : Shell p} (hy : g * y = 1) :
    ¬ ∃ r : Shell p, r * r = y := fun h => by
  obtain ⟨l, _, hgl, hodd⟩ := inv_drive_odd F hy
  rw [← hgl] at h
  have h2 := (parity_iff F l).1 h
  rw [hodd] at h2
  exact Nat.noConfusion h2

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
    refine (FRC.Entropy.two_is_square_iff F).trans ?_
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
      rw [FRC.Entropy.mul_mul_mul_comm, hr, Shell.mul_assoc, hh, Shell.mul_one]
    · rintro ⟨r, hr⟩
      refine ⟨r * h, ?_⟩
      rw [FRC.Entropy.mul_mul_mul_comm, hr]
      calc (2 : Shell p) * (h * h) = 2 * h * h := (Shell.mul_assoc _ _ _).symm
        _ = h := by rw [hh, Shell.one_mul]
  · refine Iff.trans ?_ key
    constructor
    · rintro ⟨r, hr⟩
      refine ⟨g ^ κ * r, ?_⟩
      rw [FRC.Entropy.mul_mul_mul_comm, hsq, hr, Shell.neg_mul_neg, Shell.one_mul]
    · rintro ⟨r, hr⟩
      refine ⟨g ^ κ * r, ?_⟩
      rw [FRC.Entropy.mul_mul_mul_comm, hsq, hr, Shell.neg_one_mul]

/-- 8:B4 — the factorisation of the coefficient: with `c² = 2⁻¹`, `ν = g = c²·(2g)` exactly on every shell,
and the cofactor `2g` is a square exactly when `κ` is odd — the product `g` odd always (Corollary
`two-seats`). -/
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

/-- 8:F2 — the terminal latitude: `π = 2κ = −2⁻¹` (`= −c²`); the quarter-cycle shift `m ↦ m + κ` on the
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

/-- 8:F3 — the drive pullback on the characters: with `y = g⁻¹`, `χ_k(g^{j}) = y^k · χ_k(g^{j+1})` for every
`j, k` — the winding-`k` mode acquires the phase `g^{−k}` per chronon (Theorem `zonal` (2)). -/
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

/-- 8:F4 — sector separation: the inverse of the drive is primitive of order `p − 1` (`ord(g⁻¹) = p − 1`,
so the free evolution is no Cayley step, whose scalar phases have order dividing `p + 1`), and the norm-one
torus meets the base field in `{±1}` alone (`u² = 1 ⇒ u = ±1`). -/
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

/-- 8:B7 [value] — on `𝔽₅` the Euclidean form has `5³ + 5² − 5 = 145` zeros and the Lorentzian form
(`ν = g = 2`) has `5³ − 5² + 5 = 105`: the hyperbolic and the elliptic form part on the base shell. -/
theorem zeros5 : euclidZeros 5 = 145 ∧ lorentzZeros 5 2 = 105 := by decide +kernel

/-- 8:B7 [value] — on `𝔽₁₃`: `2353` and `2041` zeros (`13³ ± 13² ∓ 13`), `ν = g = 2`. -/
theorem zeros13 : euclidZeros 13 = 2353 ∧ lorentzZeros 13 2 = 2041 := by decide +kernel

/-- 8:D5, 8:D12, 8:C5, 8:F2 [value] — the boost torus: `|N¹| = 14 = p + 1` on `𝔽₁₃` (`ν = 2`) and `18` on `𝔽₁₇`
(`ν = 3`); the unit-norm circle of the chart has `p − 1` points: `12` and `16` (8:F2). -/
theorem torus_counts :
    normOneCount 13 2 = 14 ∧ normOneCount 17 3 = 18 ∧ unitCircleCount 13 = 12 ∧ unitCircleCount 17 = 16 := by
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

/-- 8:D2 [value] — the Clifford relations hold on `𝔽₁₃` (`ν = 2`, `i = 5`), `𝔽₁₇` (`ν = 3`, `i = 4`) and
`𝔽₅` (`ν = 2`, `i = 2`). -/
theorem clifford_values : clifford (2 : Shell 13) 5 = true ∧ clifford (3 : Shell 17) 4 = true ∧
    clifford (2 : Shell 5) 2 = true := by decide +kernel

/-- The spin lift `S(x, y) = x I₄ + y γ⁰γ¹` and its inverse `δ⁻¹(x I₄ − y γ⁰γ¹)`, `δ = x² − ν y²`, with the
inverse of `δ` supplied. -/
def spinLift (i x y : Shell p) : Mat p ν :=
  smul ⟨x, 0⟩ (ident 4) + smul ⟨y, 0⟩ (gamma0 i * gamma1 i)
def spinLiftInv (i x y dinv : Shell p) : Mat p ν :=
  smul ⟨dinv, 0⟩ (smul ⟨x, 0⟩ (ident 4) + smul ⟨-y, 0⟩ (gamma0 i * gamma1 i))

/-- 8:D6, 8:D7, 8:D12 — the spin conjugation `S⁻¹γ⁰S = Aγ⁰ + νBγ¹`, `S⁻¹γ¹S = Bγ⁰ + Aγ¹`, `γ², γ³` fixed, and
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

/-- 8:D6, 8:D7, 8:D12 [value] — on `𝔽₁₃` (`ν = g = 2`, `x = y = 1`, `δ = −1`): `A = 10`, `B = 2`,
`γ̂⁰ = 10γ⁰ − 4γ¹`, `γ̂¹ = −2γ⁰ + 10γ¹`; on `𝔽₁₇` (`ν = g = 3`, `δ = −2`, `δ⁻¹ = 8`): `A = 15`, `B = 1`,
`γ̂⁰ = 15γ⁰ − 3γ¹`, `γ̂¹ = −γ⁰ + 15γ¹`. -/
theorem spin_conjugation_values :
    spinConj (2 : Shell 13) 5 1 1 12 10 2 = true ∧ spinConj (3 : Shell 17) 4 1 1 8 15 1 = true := by
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

/-- 8:D9 [value] — the spinor form on `𝔽₅`, `𝔽₁₃` and `𝔽₁₇`. -/
theorem spinor_form_values :
    spinorForm (2 : Shell 5) 2 = true ∧ spinorForm (2 : Shell 13) 5 = true ∧ spinorForm (3 : Shell 17) 4 = true := by
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

/-- 8:C6, 8:E4 [value] — the Cayley step of `H = −Δ` on `𝔽₁₃` has order exactly `13` at `α = w` and at `α = c = 6w`
(`c² = 7 = 2⁻¹`). -/
theorem cayley13_values : cayley13 ⟨0, 1⟩ = true ∧ cayley13 ⟨0, 6⟩ = true ∧
    ((⟨0, 6⟩ : Ext 13 2) * ⟨0, 6⟩ = 7 ∧ (2 : Shell 13) * 7 = 1) := by decide +kernel

/-- The scalar Cayley map `φ(λ) = (1 + wλ)/(1 − wλ)` (`α = w`) on `K`, by the conjugate and the searched
inverse of the norm. -/
def phi (ν : Shell p) (lam : Shell p) : Ext p ν :=
  let num : Ext p ν := ⟨1, lam⟩
  let den : Ext p ν := ⟨1, -lam⟩
  num * Ext.conj den * Ext.ofShell (invS (Ext.norm den))

/-- The order of `u` in the torus, by search up to `p + 1` (`0` if none). -/
def orderIn (u : Ext p ν) : Nat :=
  match (List.range (p + 2)).find? (fun e => decide (0 < e ∧ u ^ e = 1)) with
  | some e => e
  | none => 0

/-- 8:E4 (2), 8:C5 — the potential propagator `U = diag(φ(V(x)))` for `V = id`: every phase `φ(λ)` has norm
one and `φ(λ)^{p+1} = 1`, and the order of the diagonal is the least common multiple of the phase orders —
`14 = p + 1` on `𝔽₁₃` and `18 = p + 1` on `𝔽₁₇`: the bound `p + 1` is attained. -/
def potentialOrder (p : Nat) [Pos p] (ν : Shell p) : Nat :=
  (List.range p).foldl (fun acc l => Nat.lcm acc (orderIn (phi ν (ofNat l)))) 1

def potentialNormOne (p : Nat) [Pos p] (ν : Shell p) : Bool :=
  (List.range p).all fun l => decide (Ext.norm (phi ν (ofNat l)) = 1) && decide ((phi ν (ofNat l)) ^ (p + 1) = 1)

/-- 8:E4 [value] — the potential propagator of `V = id` has order `14 = p + 1` on `𝔽₁₃` and `18` on `𝔽₁₇`, the
least common multiple of the phase orders, every phase of norm one. -/
theorem potential_orders : potentialNormOne 13 2 = true ∧ potentialOrder 13 2 = 14 ∧
    potentialNormOne 17 3 = true ∧ potentialOrder 17 3 = 18 := by decide +kernel

/-- 8:D5 [value] — the triality clause: the torus of `𝔽₁₇` (`18 = 3·6`) carries an element of order three,
and the torus of `𝔽₁₃` (`14`, `3 ∤ 14`) carries none: `u³ = 1`, `u ≠ 1` with `N(u) = 1`. -/
def hasOrderThree (p : Nat) [Pos p] (ν : Shell p) : Bool :=
  (List.range p).any fun a => (List.range p).any fun b =>
    let u : Ext p ν := ⟨ofNat a, ofNat b⟩
    decide (Ext.norm u = 1) && decide (u ^ 3 = 1) && decide (u ≠ 1)

/-- 8:D5 [value] — an element of order three on the torus of `𝔽₁₇`, none on the torus of `𝔽₁₃`. -/
theorem triality_values : hasOrderThree 17 3 = true ∧ hasOrderThree 13 2 = false := by decide +kernel

/-- 8:E2 — the image count of the power map `x ↦ x^ε` on the nonzero residues. -/
def powerImage (p : Nat) [Pos p] (ε : Nat) : Nat :=
  ((List.range p).drop 1).foldl (fun acc y =>
    if ((List.range p).drop 1).any (fun x => decide ((ofNat x : Shell p) ^ ε = ofNat y)) then acc + 1 else acc) 0

/-- 8:E2 [value] — on `𝔽₁₃`: the images of `x ↦ x^ε` have `(p − 1)/gcd(ε, 12)` elements — `12, 6, 4, 3, 2, 1`
for `ε = 1, 2, 3, 4, 6, 12` (loss factors `1, 2, 3, 4, 6, 12`). -/
theorem power_map13 : powerImage 13 1 = 12 ∧ powerImage 13 2 = 6 ∧ powerImage 13 3 = 4 ∧ powerImage 13 4 = 3 ∧
    powerImage 13 6 = 2 ∧ powerImage 13 12 = 1 := by decide +kernel

/-- 8:B4, 8:B3, 8:D12 [value] — the anchors: on `𝔽₁₃` (`g = 2`, `i = 5`) `2⁻¹ = 7` is a nonsquare and
`e = g^i = 6` is a nonsquare; on `𝔽₁₇` (`g = 3`, `i = 4`) `2 = 6²`, `i = 2²` and `e = 3⁴ = 13 = 8²` are
squares, and `ν = g = 3` is the only nonsquare among the named residues — so the class of `e` is not
stable across shells (B3). -/
theorem anchors :
    ((2 : Shell 13) * 7 = 1 ∧ ∀ r : Shell 13, r * r ≠ 7) ∧ ((2 : Shell 13) ^ 5 = 6 ∧ ∀ r : Shell 13, r * r ≠ 6) ∧
    ((6 : Shell 17) * 6 = 2 ∧ (2 : Shell 17) * 2 = 4 ∧ (3 : Shell 17) ^ 4 = 13 ∧ (8 : Shell 17) * 8 = 13 ∧
      ∀ r : Shell 17, r * r ≠ 3) := by decide +kernel

/-- 8:D12 — the shell admissibility congruences of the programme: `κ` even, `κ ≡ 1 (mod 3)`, `4κ + 1` prime. -/
def shellAdmissible (κ : Nat) : Prop := κ % 2 = 0 ∧ κ % 3 = 1 ∧ FRC.Dimensions.isPrime (4 * κ + 1)
instance (κ : Nat) : Decidable (shellAdmissible κ) := by unfold shellAdmissible; exact inferInstance

/-- 8:D12, 8:A5 [value] — `𝔽₁₇` (`κ = 4`) is the minimal admissible shell: `17 ≡ 5 (mod 12)`, and no capacity below
`4` is admissible (`κ = 1, 3` odd, `κ = 2` gives `9`). -/
theorem minimal_admissible : shellAdmissible 4 ∧ (∀ κ, κ < 4 → ¬ shellAdmissible κ) ∧ 17 % 12 = 5 := by
  decide +kernel

/-- 8:B4, 8:A5 [value] — the laboratory Carrier `Ω = 2 408 561`: `c = 171 106` is base-rational with
`c² = 2⁻¹ = 1 204 281`, and the two factors compose, `2⁻¹ · (2g) = 1 204 281 · 12 = 6 = g`. -/
theorem carrier_constants :
    (171106 : Shell 2408561) * 171106 = 1204281 ∧ (2 : Shell 2408561) * 1204281 = 1 ∧
    (1204281 : Shell 2408561) * 12 = 6 := by decide +kernel

end matrices

end FRC.Dirac
