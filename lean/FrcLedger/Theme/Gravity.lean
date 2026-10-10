import Mathlib

/-!
# FrcLedger.Theme.Gravity — the gravity theme on Mathlib: the exact faces of 21-gravity (10 October 2026)

The exact Mathlib variants of 21-gravity's rows, moved from the paper module `FrcLedger/Gravity.lean` (which keeps
every old name as an alias): the Carrier register on a field with `4S + 1 = 0` — the calibration congruence, the
register value `G = 2S`, the action quantum as the quarter-turn pair (21:A1, C2, C5, C16); the count face of the area
law and the merger law on `ℤ` (21:C13); the cover forcing and the PPN triangle over `ℚ` (21:A9, C7, C8, C25); the
mass–energy channel as a gcd (21:A9); the central difference's anti-self-adjointness and the finite Fourier
shift theorem on `ZMod N` (21:C9, C20). No reals here (gate G09): the chart readings are `Theme/Strong.lean`'s. The core
proves the same faces with no axioms (`FrcCore/Theme/Gravity.lean`, `Theme/Drift.lean`, `Theme/Lattice.lean`,
`Theme/Shift.lean`); these are their Mathlib counterparts on the classical hierarchy.
-/

namespace FRC.GravML

/-! ## The Carrier register (21:A1, C2, C5, C16) -/
section register

variable {K : Type*} [Field K]

/-- 21:C16, 21:A1 — the calibration congruence: on the Carrier chart `4S + 1 = 0` the full cycle `2π ↦ 4S` is
`−1` and `(4S)² = 1`, one residue relation. -/
theorem calibration_congruence (S : ℕ) (hΩ : ((4 * S + 1 : ℕ) : K) = 0) :
    ((4 * S : ℕ) : K) = -1 ∧ ((4 * S : ℕ) : K) ^ 2 = 1 := by
  push_cast at hΩ ⊢
  exact ⟨by linear_combination hΩ, by linear_combination (4 * (S : K) - 1) * hΩ⟩

/-- 21:C2, 21:C5, 21:C16 — the register value of the Newton constant, `G = 2S`, on the Carrier chart
`4S + 1 = 0`: `2G = −1` (the half-cycle); `(−2) G = 1`, the face convention `4π ↦ −2` with `G = (−2)⁻¹`; the
Gauss count `(2 · 4S) G = 1`; `c² = 2⁻¹ = 2S + 1` and `G = −c²` (the chart ratio `4π/2π = 2` is read as
`(−2)/(−1)`). The uniqueness of the linear solution is `Dimensions.G_unique`. -/
theorem newton_register (S : ℕ) (hΩ : ((4 * S + 1 : ℕ) : K) = 0) :
    2 * ((2 * S : ℕ) : K) = -1 ∧ (-2) * ((2 * S : ℕ) : K) = 1 ∧
    (2 * ((4 * S : ℕ) : K)) * ((2 * S : ℕ) : K) = 1 ∧
    2 * ((2 * S + 1 : ℕ) : K) = 1 ∧ ((2 * S + 1 : ℕ) : K) = 2⁻¹ ∧
    ((2 * S : ℕ) : K) = -((2 * S + 1 : ℕ) : K) := by
  push_cast at hΩ ⊢
  refine ⟨by linear_combination hΩ, by linear_combination -hΩ,
    by linear_combination (4 * (S : K) - 1) * hΩ, by linear_combination hΩ, ?_,
    by linear_combination hΩ⟩
  exact eq_inv_of_mul_eq_one_left (by linear_combination hΩ)

/-- On the Carrier `𝔽_Ω`, `Ω = 4S + 1` prime, `2 ≠ 0` (`Ω` is odd). -/
theorem carrier_two_ne_zero (S : ℕ) [hp : Fact (Nat.Prime (4 * S + 1))] :
    (2 : ZMod (4 * S + 1)) ≠ 0 := by
  rw [show (2 : ZMod (4 * S + 1)) = ((2 : ℕ) : ZMod (4 * S + 1)) by norm_cast, Ne,
    ZMod.natCast_eq_zero_iff]
  intro hd
  have h1 : 4 * S + 1 ≤ 2 := Nat.le_of_dvd (by norm_num) hd
  have h2 : 2 ≤ 4 * S + 1 := hp.out.two_le
  omega

/-- In any field with `4S + 1 = 0` and `2 ≠ 0`, a quarter-turn `i² = −1` gives a square root of `S`,
`r = i/2`, with `(2r)² = −1`. -/
theorem hbar_of_quarter_turn {K : Type*} [Field K] (S : ℕ) (hΩ : ((4 * S + 1 : ℕ) : K) = 0)
    (h2 : (2 : K) ≠ 0) (i : K) (hi : i ^ 2 = -1) :
    ∃ r : K, r ^ 2 = (S : K) ∧ (2 * r) ^ 2 = -1 := by
  push_cast at hΩ
  have h4 : (2⁻¹ : K) ^ 2 * 4 = 1 := by field_simp; norm_num
  refine ⟨i * 2⁻¹, ?_, ?_⟩
  · calc (i * 2⁻¹) ^ 2 = i ^ 2 * (2⁻¹) ^ 2 := by ring
      _ = -1 * (2⁻¹) ^ 2 := by rw [hi]
      _ = (S : K) := by linear_combination (-(2⁻¹ : K) ^ 2) * hΩ + (S : K) * h4
  · have : 2 * (i * 2⁻¹) = i := by field_simp
    rw [this, hi]

/-- 21:C5, 21:C16, 21:A1 — the action quantum as the quarter-turn pair: on every Carrier `Ω = 4S + 1` prime, `S`
is a square (`S = (i/2)²` with `i² = −1`, since `4S = −1`), so `ħ = 2√S` has `ħ² = 4S = −1` — `ħ` is one of the
quarter-turn pair `±i`. -/
theorem hbar_register (S : ℕ) [Fact (Nat.Prime (4 * S + 1))] :
    ∃ r : ZMod (4 * S + 1), r ^ 2 = (S : ZMod (4 * S + 1)) ∧ (2 * r) ^ 2 = -1 := by
  obtain ⟨i, hi⟩ : IsSquare (-1 : ZMod (4 * S + 1)) := ZMod.exists_sq_eq_neg_one_iff.mpr (by omega)
  exact hbar_of_quarter_turn S (ZMod.natCast_self _) (carrier_two_ne_zero S) i (by rw [sq]; exact hi.symm)

end register

/-! ## The count face and the cover forcing (21:A9, C7, C8, C13, C25) -/
section count

/-- 21:C13 — the count face of the area law on a symmetry-complete shell `p = 4κ + 1`: with `S = (p² − 1)/4`,
i.e. `4S + 1 = p²` for `S = κ(4κ + 2)`, and the coordinate area `A = p(p + 1)`, the ratio `S/A = κ/p` holds
exactly (`Sp = κA`) and `S = (A/4)(1 − 1/p)` (`4Sp = A(p − 1)`) — the Bekenstein quarter as the `Q₄` quotient. -/
theorem count_face (κ : ℕ) :
    4 * (κ * (4 * κ + 2)) + 1 = (4 * κ + 1) ^ 2 ∧
    (κ * (4 * κ + 2)) * (4 * κ + 1) = κ * ((4 * κ + 1) * (4 * κ + 2)) ∧
    4 * (κ * (4 * κ + 2)) * (4 * κ + 1) = ((4 * κ + 1) * (4 * κ + 2)) * (4 * κ) :=
  ⟨by ring, by ring, by ring⟩

/-- 21:C13 — the merger area law on the count face, `A = M(M + 1)`: `ΔA = 2M₁M₂` exactly under additive mass,
the paper's instance `27 811 + 1 596 → 29 407` giving `ΔA = 88 772 712`; with a radiated `δ` the count gives
`ΔA = 2M₁M₂ − (2(M₁ + M₂) + 1)δ + δ²`, at most the additive value for `0 ≤ δ ≤ 2(M₁ + M₂) + 1` — the area
statement an inequality (the coefficient `−2(M₁ + M₂)δ` is the `A = M²` form; on the count face the linear
term carries the extra `−δ`). -/
theorem merger_area_law (M₁ M₂ δ : ℤ) :
    (M₁ + M₂) * (M₁ + M₂ + 1) - M₁ * (M₁ + 1) - M₂ * (M₂ + 1) = 2 * M₁ * M₂ ∧
    (M₁ + M₂ - δ) * (M₁ + M₂ - δ + 1) - M₁ * (M₁ + 1) - M₂ * (M₂ + 1)
      = 2 * M₁ * M₂ - (2 * (M₁ + M₂) + 1) * δ + δ ^ 2 ∧
    (0 ≤ δ → δ ≤ 2 * (M₁ + M₂) + 1 →
      (M₁ + M₂ - δ) * (M₁ + M₂ - δ + 1) - M₁ * (M₁ + 1) - M₂ * (M₂ + 1) ≤ 2 * M₁ * M₂) ∧
    (27811 + 1596) * (27811 + 1596 + 1) - 27811 * (27811 + 1) - 1596 * (1596 + 1) = (88772712 : ℤ) := by
  refine ⟨by ring, by ring, ?_, by norm_num⟩
  intro h0 h1
  nlinarith [mul_nonneg h0 (sub_nonneg.mpr h1)]

/-- 21:A9, 21:C25, 21:C7, 21:C8 — the cover forcing: the apsidal coefficient `2 − β + 2γ` against the
PPN-free deficit `3/2` equals the two-face ratio `2` exactly when `2γ − β = 1`, with deviation
`(2/3)(2γ − β − 1)`; channel unity `γ = 1` together with the forcing gives `β = 1`, and the perihelion factor
`(2 + 2γ − β)/3` is then `1` (the deflection factor `(1 + γ)/2` is `1` at `γ = 1`). -/
theorem cover_forcing (β γ : ℚ) :
    ((2 - β + 2 * γ) / (3 / 2) = 2 ↔ 2 * γ - β = 1) ∧
    (2 - β + 2 * γ) / (3 / 2) - 2 = 2 / 3 * (2 * γ - β - 1) ∧
    (γ = 1 → 2 * γ - β = 1 → β = 1 ∧ (2 + 2 * γ - β) / 3 = 1) := by
  refine ⟨?_, by ring, ?_⟩
  · constructor <;> intro h <;> linarith
  · rintro rfl h
    exact ⟨by linarith, by linarith⟩

/-- 21:A9 — the mass–energy channel `C_{p−1} ∩ C_{2(p+1)} = Q₄`: on every shell `p ≡ 1 (mod 4)`,
`gcd(p − 1, 2(p + 1)) = 4`; the subgroup reading — in the cyclic unit group of `𝔽_{p²}` (order `(p − 1)(p + 1)`)
the subgroups of orders `p − 1` and `2(p + 1)` meet in the subgroup of order `gcd` — is not formalised here. -/
theorem channel_q4 (p : ℕ) (hp : p % 4 = 1) : Nat.gcd (p - 1) (2 * (p + 1)) = 4 := by
  obtain ⟨κ, rfl⟩ : ∃ κ, p = 4 * κ + 1 := ⟨p / 4, by omega⟩
  have h1 : 4 * κ + 1 - 1 = 4 * κ := by omega
  have h2 : 2 * (4 * κ + 1 + 1) = 4 * (1 + 2 * κ) := by ring
  rw [h1, h2, Nat.gcd_mul_left, Nat.gcd_add_mul_right_right, Nat.gcd_one_right]

end count

/-! ## The lattice on `ZMod N` (21:C9, C20) -/
section lattice

variable {N : ℕ} [NeZero N] {R : Type*} [CommRing R]

/-- 21:C9 — anti-self-adjointness of the central difference on the cycle `ℤ/N`: with
`(Δf)(x) = f(x + 1) − f(x − 1)`, `Σ_x f(x)(Δg)(x) = −Σ_x (Δf)(x) g(x)` — `Δᵀ = −Δ`, the identity that carries
the discrete Fierz–Pauli gauge invariance (the package proves the four-term functional's invariance as an exact
integer identity; the paper's `½` in `D_μ = (T_μ − T_μ⁻¹)/2` scales both sides alike). The one-sided
difference `(δf)(x) = f(x + 1) − f(x)` has adjoint the negative *backward* difference,
`Σ_x f(x)(δg)(x) = −Σ_x (f(x) − f(x − 1)) g(x)` — the package's failing control is that this is not `−δ`. -/
theorem central_difference_adjoint (f g : ZMod N → R) :
    ∑ x, f x * (g (x + 1) - g (x - 1)) = -∑ x, (f (x + 1) - f (x - 1)) * g x ∧
    ∑ x, f x * (g (x + 1) - g x) = -∑ x, (f x - f (x - 1)) * g x := by
  have h1 : ∑ x, f x * g (x + 1) = ∑ x, f (x - 1) * g x := by
    rw [← Equiv.sum_comp (Equiv.addRight (1 : ZMod N)) (fun x => f (x - 1) * g x)]
    simp
  have h2 : ∑ x, f x * g (x - 1) = ∑ x, f (x + 1) * g x := by
    rw [← Equiv.sum_comp (Equiv.subRight (1 : ZMod N)) (fun x => f (x + 1) * g x)]
    simp
  constructor
  · simp only [mul_sub, sub_mul, Finset.sum_sub_distrib, h1, h2]; ring
  · simp only [mul_sub, sub_mul, Finset.sum_sub_distrib, h1]; ring

/-- The finite Fourier transform on the cycle, against a character `ζ` with `ζ^N = 1`:
`(F f)(k) = Σ_x f(x) ζ^{xk}`. -/
def dft (ζ : R) (f : ZMod N → R) (k : ZMod N) : R := ∑ x, f x * ζ ^ (x.val * k.val)

omit [NeZero N] in
/-- A root of unity is insensitive to the reduction of its exponent modulo `N`. -/
theorem pow_val_mod (ζ : R) (hζ : ζ ^ N = 1) (m k : ℕ) : ζ ^ ((m % N) * k) = ζ ^ (m * k) := by
  conv_rhs => rw [← Nat.mod_add_div m N]
  rw [add_mul, pow_add, mul_assoc, pow_mul, pow_mul, hζ, one_pow, mul_one]

omit [NeZero N] in
/-- A root of unity is insensitive to the reduction of a factor of its exponent modulo `N`. -/
theorem pow_mul_val_mod (ζ : R) (hζ : ζ ^ N = 1) (k m : ℕ) : ζ ^ (k * (m % N)) = ζ ^ (k * m) := by
  rw [mul_comm, pow_val_mod ζ hζ, mul_comm]

/-- 21:C20 — the finite Fourier shift theorem in both forms, the kick of the two-shift law: the kick, a
character `ζ^{ax}` multiplying `f` in position, shifts the transform, `F(ζ^{a·} f)(k) = (F f)(k + a)`; dually,
shifting `f` by `a` multiplies its transform by the character, `F(f(· − a))(k) = ζ^{ak} (F f)(k)`. -/
theorem shift_theorem (ζ : R) (hζ : ζ ^ N = 1) (f : ZMod N → R) (a k : ZMod N) :
    dft ζ (fun x => ζ ^ (a.val * x.val) * f x) k = dft ζ f (k + a) ∧
    dft ζ (fun x => f (x - a)) k = ζ ^ (a.val * k.val) * dft ζ f k := by
  constructor
  · unfold dft
    apply Finset.sum_congr rfl
    intro x _
    dsimp only
    rw [ZMod.val_add, pow_mul_val_mod ζ hζ, mul_add, pow_add, mul_comm a.val x.val]
    ring
  · unfold dft
    rw [Finset.mul_sum, ← Equiv.sum_comp (Equiv.addRight a)]
    apply Finset.sum_congr rfl
    intro x _
    simp only [Equiv.coe_addRight, add_sub_cancel_right]
    rw [ZMod.val_add, pow_val_mod ζ hζ, add_mul, pow_add]
    ring

end lattice

end FRC.GravML
