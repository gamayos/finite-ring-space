import Mathlib
import FrcLedger.Theme.Chart
import FrcLedger.Theme.Strong
import FrcLedger.Theme.Gravity
import FrcLedger.Keys.Chart
import FrcLedger.Keys.Gravity

/-!
# 21-gravity — the paper module on Mathlib: every row's declaration under the paper's name (10 October 2026)

Rows of the predicate ledger of *Gravitation as Phase Synchronisation over Finite Holographic Substrate* (tree
`21-gravity-20260623`). Since 10 October 2026 (the paper's migration to the framework, `reports/blueprint-20261010.md`)
the theorems live in the themes and every name here is an alias: the exact faces in `FrcLedger/Theme/Gravity.lean`
(`FRC.GravML`: the Carrier register, the count face and the merger law, the cover forcing over `ℚ`, the channel, the
central difference and the shift theorem on `ZMod N`), the chart readings in `FrcLedger/Theme/Strong.lean`
(`FRC.Strong`: the operational cut, the photon sphere, the shadow and the ringdown, the ISCO and its efficiency, the
capacity ratio and the preferred-frame scale re-anchored to the scale import `ln Ω = 283.5`, `Ω = 1.3 × 10¹²³`, the
redshift, the registration root and the crossover, the discriminant, the fixed point, the dispersion symbol, the
locked sum, the exponential reading, the post-Newtonian brackets, dilution), and the floor and the tilt in
`FrcLedger/Theme/Chart.lean` (`FRC.Chart.floor_value`, `FRC.Chart.tilt_ledger`; the tilt was bracketed at `281` here
before 10 October 2026). Classical (tier 2) on Mathlib's hierarchy; the finite content — the register on every frame,
the channel, the defect's recurrence, the pair tally, the Gauss law, the post-Newtonian coefficients, the central
difference and the shift theorem — is proved with no axioms in the core (`FrcCore/Theme/Gravity.lean`,
`Theme/Drift.lean`, `Theme/Lattice.lean`, `Theme/Shift.lean`; the aliases `FrcCore/Gravity.lean`). `make_predicates.py`
writes the typed predicates `FRC.Gravity.p21NNN` below this module's declarations.
-/

namespace FRC.Gravity

open Real

/-! ## Old names (10 October 2026): every declaration of this module is an alias of a theme's, under the paper's name —
`FRC.GravML` (`Theme/Gravity.lean`), `FRC.Strong` (`Theme/Strong.lean`), `FRC.Chart` (`Theme/Chart.lean`) -/

section register
variable {K : Type*} [Field K]

/-- 21:C16, 21:A1 — the calibration congruence: on the Carrier chart `4S + 1 = 0` the full cycle `2π ↦ 4S` is
`−1` and `(4S)² = 1`, one residue relation. (`FRC.GravML.calibration_congruence`, `Theme/Gravity.lean`). -/
theorem calibration_congruence (S : ℕ) (hΩ : ((4 * S + 1 : ℕ) : K) = 0) :
    ((4 * S : ℕ) : K) = -1 ∧ ((4 * S : ℕ) : K) ^ 2 = 1 :=
  FRC.GravML.calibration_congruence S hΩ

/-- 21:C2, 21:C5, 21:C16 — the register value of the Newton constant, `G = 2S`, on the Carrier chart
`4S + 1 = 0`: `2G = −1` (the half-cycle); `(−2) G = 1`, the face convention `4π ↦ −2` with `G = (−2)⁻¹`; the
Gauss count `(2 · 4S) G = 1`; `c² = 2⁻¹ = 2S + 1` and `G = −c²` (the chart ratio `4π/2π = 2` is read as
`(−2)/(−1)`). The uniqueness of the linear solution is `Dimensions.G_unique`. (`FRC.GravML.newton_register`, `Theme/Gravity.lean`). -/
theorem newton_register (S : ℕ) (hΩ : ((4 * S + 1 : ℕ) : K) = 0) :
    2 * ((2 * S : ℕ) : K) = -1 ∧ (-2) * ((2 * S : ℕ) : K) = 1 ∧
    (2 * ((4 * S : ℕ) : K)) * ((2 * S : ℕ) : K) = 1 ∧
    2 * ((2 * S + 1 : ℕ) : K) = 1 ∧ ((2 * S + 1 : ℕ) : K) = 2⁻¹ ∧
    ((2 * S : ℕ) : K) = -((2 * S + 1 : ℕ) : K) :=
  FRC.GravML.newton_register S hΩ

/-- 21:C5, 21:C16, 21:A1 — the action quantum as the quarter-turn pair: on every Carrier `Ω = 4S + 1` prime, `S`
is a square (`S = (i/2)²` with `i² = −1`, since `4S = −1`), so `ħ = 2√S` has `ħ² = 4S = −1` — `ħ` is one of the
quarter-turn pair `±i`. (`FRC.GravML.hbar_register`, `Theme/Gravity.lean`). -/
theorem hbar_register (S : ℕ) [Fact (Nat.Prime (4 * S + 1))] :
    ∃ r : ZMod (4 * S + 1), r ^ 2 = (S : ZMod (4 * S + 1)) ∧ (2 * r) ^ 2 = -1 :=
  FRC.GravML.hbar_register S

/-- 21:X8, 21:C5 — the weakness of gravity as cardinality dilution: with the Planck mass the
locality horizon, `m_P = √Ω`, the dimensionless coupling of two masses `m` is `(m/m_P)² = m²/Ω`, small because
`Ω` is large. C5's frame covariance is not formal content. (`FRC.Strong.dilution`, `Theme/Strong.lean`). -/
theorem dilution (m Ω : ℝ) (hΩ : 0 < Ω) : (m / √Ω) ^ 2 = m ^ 2 / Ω :=
  FRC.Strong.dilution m Ω hΩ

end register

/-- 21:C13 — the count face of the area law on a symmetry-complete shell `p = 4κ + 1`: with `S = (p² − 1)/4`,
i.e. `4S + 1 = p²` for `S = κ(4κ + 2)`, and the coordinate area `A = p(p + 1)`, the ratio `S/A = κ/p` holds
exactly (`Sp = κA`) and `S = (A/4)(1 − 1/p)` (`4Sp = A(p − 1)`) — the Bekenstein quarter as the `Q₄` quotient. (`FRC.GravML.count_face`, `Theme/Gravity.lean`). -/
theorem count_face (κ : ℕ) :
    4 * (κ * (4 * κ + 2)) + 1 = (4 * κ + 1) ^ 2 ∧
    (κ * (4 * κ + 2)) * (4 * κ + 1) = κ * ((4 * κ + 1) * (4 * κ + 2)) ∧
    4 * (κ * (4 * κ + 2)) * (4 * κ + 1) = ((4 * κ + 1) * (4 * κ + 2)) * (4 * κ) :=
  FRC.GravML.count_face κ

/-- 21:C13 — the merger area law on the count face, `A = M(M + 1)`: `ΔA = 2M₁M₂` exactly under additive mass,
the paper's instance `27 811 + 1 596 → 29 407` giving `ΔA = 88 772 712`; with a radiated `δ` the count gives
`ΔA = 2M₁M₂ − (2(M₁ + M₂) + 1)δ + δ²`, at most the additive value for `0 ≤ δ ≤ 2(M₁ + M₂) + 1` — the area
statement an inequality (the coefficient `−2(M₁ + M₂)δ` is the `A = M²` form; on the count face the linear
term carries the extra `−δ`). (`FRC.GravML.merger_area_law`, `Theme/Gravity.lean`). -/
theorem merger_area_law (M₁ M₂ δ : ℤ) :
    (M₁ + M₂) * (M₁ + M₂ + 1) - M₁ * (M₁ + 1) - M₂ * (M₂ + 1) = 2 * M₁ * M₂ ∧
    (M₁ + M₂ - δ) * (M₁ + M₂ - δ + 1) - M₁ * (M₁ + 1) - M₂ * (M₂ + 1)
      = 2 * M₁ * M₂ - (2 * (M₁ + M₂) + 1) * δ + δ ^ 2 ∧
    (0 ≤ δ → δ ≤ 2 * (M₁ + M₂) + 1 →
      (M₁ + M₂ - δ) * (M₁ + M₂ - δ + 1) - M₁ * (M₁ + 1) - M₂ * (M₂ + 1) ≤ 2 * M₁ * M₂) ∧
    (27811 + 1596) * (27811 + 1596 + 1) - 27811 * (27811 + 1) - 1596 * (1596 + 1) = (88772712 : ℤ) :=
  FRC.GravML.merger_area_law M₁ M₂ δ

/-- 21:A9, 21:C25, 21:C7, 21:C8 — the cover forcing: the apsidal coefficient `2 − β + 2γ` against the
PPN-free deficit `3/2` equals the two-face ratio `2` exactly when `2γ − β = 1`, with deviation
`(2/3)(2γ − β − 1)`; channel unity `γ = 1` together with the forcing gives `β = 1`, and the perihelion factor
`(2 + 2γ − β)/3` is then `1` (the deflection factor `(1 + γ)/2` is `1` at `γ = 1`). (`FRC.GravML.cover_forcing`, `Theme/Gravity.lean`). -/
theorem cover_forcing (β γ : ℚ) :
    ((2 - β + 2 * γ) / (3 / 2) = 2 ↔ 2 * γ - β = 1) ∧
    (2 - β + 2 * γ) / (3 / 2) - 2 = 2 / 3 * (2 * γ - β - 1) ∧
    (γ = 1 → 2 * γ - β = 1 → β = 1 ∧ (2 + 2 * γ - β) / 3 = 1) :=
  FRC.GravML.cover_forcing β γ

/-- 21:A9 — the mass–energy channel `C_{p−1} ∩ C_{2(p+1)} = Q₄`: on every shell `p ≡ 1 (mod 4)`,
`gcd(p − 1, 2(p + 1)) = 4`; the subgroup reading — in the cyclic unit group of `𝔽_{p²}` (order `(p − 1)(p + 1)`)
the subgroups of orders `p − 1` and `2(p + 1)` meet in the subgroup of order `gcd` — is not formalised here. (`FRC.GravML.channel_q4`, `Theme/Gravity.lean`). -/
theorem channel_q4 (p : ℕ) (hp : p % 4 = 1) : Nat.gcd (p - 1) (2 * (p + 1)) = 4 :=
  FRC.GravML.channel_q4 p hp

/-- 21:C12, 21:P7 — the operational cut and the slip core in the substrate coordinate (`G = 1`, `M` in Planck
masses, `L = ln Ω`): `r_f = 2M/L` carries `e^{2M/r_f} = Ω` (the round-trip delay's factor); `r_* = √M < r_f`
exactly when `M > (L/2)²`, and `r_f < M` exactly when `L > 2` (master E10). (`FRC.Strong.operational_cut`, `Theme/Strong.lean`). -/
theorem operational_cut (M L Ω : ℝ) (hM : 0 < M) (hL : 0 < L) (hΩ : L = log Ω) (hΩ0 : 0 < Ω) :
    exp (2 * M / (2 * M / L)) = Ω ∧
    (√M < 2 * M / L ↔ (L / 2) ^ 2 < M) ∧ (2 * M / L < M ↔ 2 < L) :=
  FRC.Strong.operational_cut M L Ω hM hL hΩ hΩ0

/-- 21:P1 — the photon sphere (`prop:shadow`, `rem:exponential`): the impact parameter `b(r) = r e^{2Gm/r}` of the exponential metric
satisfies `b(r) ≥ 2e·Gm` for every `r > 0`, with equality exactly at `r = 2Gm` (from `x + 1 ≤ eˣ`, strict off
`x = 0`): the photon sphere is at `r_ph = 2Gm`, the critical impact parameter `b_c = 2e·Gm`. (`FRC.Strong.photon_sphere`, `Theme/Strong.lean`). -/
theorem photon_sphere (Gm r : ℝ) (hG : 0 < Gm) (hr : 0 < r) :
    2 * exp 1 * Gm ≤ r * exp (2 * Gm / r) ∧ (r * exp (2 * Gm / r) = 2 * exp 1 * Gm ↔ r = 2 * Gm) :=
  FRC.Strong.photon_sphere Gm r hG hr

/-- 21:P1 — the shadow and the ringdown against general relativity, bracketed from `e` (nine places) and `√3`:
the critical impact parameters `b_c = 2e·Gm` (this work) and `3√3·Gm` (Schwarzschild) have ratio
`2e/(3√3)` between `1.0462` and `1.0463` (the shadow `+4.6 %`), and the eikonal ringdown frequency, `∝ 1/b_c`,
ratio `3√3/(2e)` between `0.9557` and `0.9558` (`−4.4 %`); the Sgr A* excess `(4e − 6√3) θ_g` at the
GRAVITY `θ_g = 5.12 µas` [data, A8] lies between `2.46` and `2.47 µas` (the `2.5 µas` of the text). (`FRC.Strong.shadow_bracket`, `Theme/Strong.lean`). -/
theorem shadow_bracket :
    (1.0462 : ℝ) < 2 * exp 1 / (3 * √3) ∧ 2 * exp 1 / (3 * √3) < 1.0463 ∧
    (0.9557 : ℝ) < 3 * √3 / (2 * exp 1) ∧ 3 * √3 / (2 * exp 1) < 0.9558 ∧
    (2.46 : ℝ) < (4 * exp 1 - 6 * √3) * 5.12 ∧ (4 * exp 1 - 6 * √3) * 5.12 < 2.47 :=
  FRC.Strong.shadow_bracket

/-- 21:P1 — the innermost stable circular orbit of the exponential metric (`G = m = 1`, isotropic radius),
with the circular-orbit relations of the paper's `prop:isco` taken as given and not formalised
(`L² = e^{2/r} r²/(r − 2)` and `E² = e^{−2/r}(r − 1)/(r − 2)` for a circular orbit at `r > 2`): what is
proved is that `log L²` has derivative `(r² − 6r + 4)/(r²(r − 2))`, that `r_ISCO = 3 + √5` is the root of
`r² − 6r + 4` above `2`, and that `(r − 1)/(r − 2) = r/4` there, so `E² = e^{−2/r} r/4` at the orbit. (`FRC.Strong.isco`, `Theme/Strong.lean`). -/
theorem isco (r : ℝ) (hr : 2 < r) :
    HasDerivAt (fun r : ℝ => 2 / r + 2 * log r - log (r - 2))
      ((r ^ 2 - 6 * r + 4) / (r ^ 2 * (r - 2))) r ∧
    (3 + √5) ^ 2 - 6 * (3 + √5) + 4 = 0 ∧ 2 < 3 + √5 ∧
    (3 + √5 - 1) / (3 + √5 - 2) = (3 + √5) / 4 :=
  FRC.Strong.isco r hr

/-- 21:P1 — the accretion efficiency bracketed: at `r_ISCO = 3 + √5` the orbital energy `E = √(e^{−2/r} r/4)`
lies between `0.9452` and `0.9453`, so `1 − E` is between `5.47 %` and `5.48 %` (the text's `5.48 %`),
against Schwarzschild's `1 − √(8/9)` between `5.71 %` and `5.72 %`. (`FRC.Strong.isco_efficiency`, `Theme/Strong.lean`). -/
theorem isco_efficiency :
    (0.0547 : ℝ) < 1 - √(exp (-(2 / (3 + √5))) * (3 + √5) / 4) ∧
    1 - √(exp (-(2 / (3 + √5))) * (3 + √5) / 4) < 0.0548 ∧
    (0.0571 : ℝ) < 1 - √(8 / 9) ∧ 1 - √(8 / 9) < (0.0572 : ℝ) :=
  FRC.Strong.isco_efficiency

/-- The arithmetic behind 21:C13's capacity ratio: for `r_f = r_s/L` the square of `r_f/r_s` is `1/L²`, and at
`L = ln Ω = 283.5` (the scale import) the ratio lies between `1.24 × 10⁻⁵` and `1.25 × 10⁻⁵` (the text's `1.24 × 10⁻⁵`); that the
externally resolvable capacity scales as `(r_f/r_s)²` is the paper's count, not formal content. (`FRC.Strong.capacity_ratio`, `Theme/Strong.lean`). -/
theorem capacity_ratio (rs L : ℝ) (hrs : rs ≠ 0) (hL : L ≠ 0) : (rs / L / rs) ^ 2 = 1 / L ^ 2 :=
  FRC.Strong.capacity_ratio rs L hrs hL

/-- `FRC.Strong.capacity_ratio_numeral` (`Theme/Strong.lean`). -/
theorem capacity_ratio_numeral : (1.24e-5 : ℝ) < 1 / 283.5 ^ 2 ∧ (1 / 283.5 ^ 2 : ℝ) < 1.25e-5 :=
  FRC.Strong.capacity_ratio_numeral

/-- 21:C4 — the redshift as clock rate: the bias field `e^{−u}` with `u = Gm/rc²` gives
`Δf/f = 1 − e^{−u} = u + O(u²)`, `|1 − e^{−u} − u| ≤ u²` on `0 ≤ u ≤ 1`. (`FRC.Strong.redshift_linear`, `Theme/Strong.lean`). -/
theorem redshift_linear (u : ℝ) (h0 : 0 ≤ u) (h1 : u ≤ 1) : |1 - exp (-u) - u| ≤ u ^ 2 :=
  FRC.Strong.redshift_linear u h0 h1

/-- 21:C19, 21:P4 — the registration root: for `0 < w < 1` the quadratic `wη² − 2η + w = 0` (rational in the
paper's `w`, here over `ℝ`) has
exactly the roots `(1 ∓ √(1 − w²))/w`; the smaller, `η = (1 − √(1 − w²))/w`, lies in `(0, 1)` and the larger
exceeds `1`, so the in-`(0, 1)` root that fixes the resolved fraction `f = 1 − η^a` is unique. (`FRC.Strong.registration_root`, `Theme/Strong.lean`). -/
theorem registration_root (w : ℝ) (hw0 : 0 < w) (hw1 : w < 1) :
    w * ((1 - √(1 - w ^ 2)) / w) ^ 2 - 2 * ((1 - √(1 - w ^ 2)) / w) + w = 0 ∧
    0 < (1 - √(1 - w ^ 2)) / w ∧ (1 - √(1 - w ^ 2)) / w < 1 ∧
    1 < (1 + √(1 - w ^ 2)) / w ∧
    (∀ x : ℝ, w * x ^ 2 - 2 * x + w = 0 →
      x = (1 - √(1 - w ^ 2)) / w ∨ x = (1 + √(1 - w ^ 2)) / w) :=
  FRC.Strong.registration_root w hw0 hw1

/-- 21:C19, 21:P4 — the crossover `g_obs = g_N/(1 − e^{−√x})`, `x = g_N/a₀`, squeezed: with `t = √x > 0`,
`1 ≤ t/(1 − e^{−t})`, and `t/(1 − e^{−t}) ≤ 1/(1 − 3t/4)` for `t ≤ 1`; and the Tully–Fisher algebra is
exact: `v² = g_obs r` with `g_obs = √(g_N a₀)`, `g_N = GM/r²`, gives `v⁴ = GMa₀`. (`FRC.Strong.crossover_limits`, `Theme/Strong.lean`). -/
theorem crossover_limits (t : ℝ) (ht : 0 < t) :
    0 < 1 - exp (-t) ∧ 1 ≤ t / (1 - exp (-t)) ∧
    (t ≤ 1 → t / (1 - exp (-t)) ≤ 1 / (1 - 3 * t / 4)) ∧
    (∀ G M r a₀ v : ℝ, 0 < r → 0 ≤ G * M → 0 ≤ a₀ →
      v ^ 2 = √(G * M / r ^ 2 * a₀) * r → v ^ 4 = G * M * a₀) :=
  FRC.Strong.crossover_limits t ht

/-- 21:C19, 21:P4, 21:X2 — the deep limit: `t/(1 − e^{−t}) → 1` as `t → 0⁺`, so `g_obs/√(g_N a₀) → 1` — the
deep regime `g_obs = √(g_N a₀)`, the floor read as noise with no dark sector. (`FRC.Strong.crossover_deep_limit`, `Theme/Strong.lean`). -/
theorem crossover_deep_limit :
    Filter.Tendsto (fun t : ℝ => t / (1 - exp (-t))) (nhdsWithin 0 (Set.Ioi 0)) (nhds 1) :=
  FRC.Strong.crossover_deep_limit

/-- 21:C19, 21:P4 — the Newtonian limit: `1 − e^{−t} → 1` as `t → ∞`, so `g_obs/g_N → 1` for `x → ∞`. (`FRC.Strong.crossover_newton_limit`, `Theme/Strong.lean`). -/
theorem crossover_newton_limit :
    Filter.Tendsto (fun t : ℝ => 1 - exp (-t)) Filter.atTop (nhds 1) :=
  FRC.Strong.crossover_newton_limit

/-- 21:P4 — the discriminant against the simple interpolant at `g_N = 5a₀`: the crossover
`ν(5) = 1/(1 − e^{−√5})` lies between `1.11966` and `1.11967`, the simple interpolant
`ν_s(5) = 1/2 + √(1/4 + 1/5)` between `1.17082` and `1.17083`, so they part by between `0.0511` and `0.0512` in
`g_obs/g_N` (the text's `0.05`). (`FRC.Strong.interpolant_discriminant`, `Theme/Strong.lean`). -/
theorem interpolant_discriminant :
    (1.11966 : ℝ) < 1 / (1 - exp (-√5)) ∧ 1 / (1 - exp (-√5)) < 1.11967 ∧
    (1.17082 : ℝ) < 1 / 2 + √(1 / 4 + 1 / 5) ∧ 1 / 2 + √(1 / 4 + 1 / 5) < 1.17083 ∧
    (0.0511 : ℝ) < (1 / 2 + √(1 / 4 + 1 / 5)) - 1 / (1 - exp (-√5)) ∧
    (1 / 2 + √(1 / 4 + 1 / 5)) - 1 / (1 - exp (-√5)) < 0.0512 :=
  FRC.Strong.interpolant_discriminant

/-- 21:C18 — the fixed point: for a power law `P(k) = k^n` the dimensionless `k³P(k)` is the
same at every scale `k > 0` exactly when `n = −3`, i.e. `n_s − 1 = n + 3 = 0`, the Harrison–Zel'dovich
`n_s = 1`, uniquely; that the drive's jitter spectrum is this fixed point is the paper's argument. (`FRC.Strong.scale_invariance_iff`, `Theme/Strong.lean`). -/
theorem scale_invariance_iff (n : ℝ) :
    (∀ k : ℝ, 0 < k → k ^ 3 * k ^ n = 1) ↔ n = -3 :=
  FRC.Strong.scale_invariance_iff n

/-- 21:C15 — the dispersion symbol: the central second difference acts on the plane wave
`e^{ikx}` by `−(2 − 2 cos k) = −4 sin²(k/2)`; the wave equation, its two polarisations and the speed `c` are
the package's. (`FRC.Strong.dispersion_symbol`, `Theme/Strong.lean`). -/
theorem dispersion_symbol (k : ℝ) : 2 - 2 * cos k = 4 * sin (k / 2) ^ 2 :=
  FRC.Strong.dispersion_symbol k

/-- 21:C1 — the coherent coefficient: a locked cluster of `m` cells with one phase sums with
coefficient exactly `m`, `‖Σ_{j<m} z‖ = m ‖z‖`; the incoherent `O(√m)` and the gradient flow are not formal
content. (`FRC.Strong.locked_sum`, `Theme/Strong.lean`). -/
theorem locked_sum (m : ℕ) (z : ℂ) : ‖∑ _j : Fin m, z‖ = m * ‖z‖ :=
  FRC.Strong.locked_sum m z

/-- 21:C11 — the exponential reading is the multiplicative one, `e^{−(a+b)} = e^{−a} e^{−b}`; the isotropic
Schwarzschild factor `R(U) = (1 − U/2)/(1 + U/2)` is `e^{−2 artanh(U/2)}`, the exponential reading of the
self-sourced `ψ = 2 artanh(U/2)`, and it violates the composition law: `R(1) = 1/3 ≠ 9/25 = R(1/2)²`. (`FRC.Strong.exponential_reading`, `Theme/Strong.lean`). -/
theorem exponential_reading (a b : ℝ) :
    exp (-(a + b)) = exp (-a) * exp (-b) ∧
    (∀ U : ℝ, -2 < U → U < 2 → exp (-(2 * artanh (U / 2))) = (1 - U / 2) / (1 + U / 2)) ∧
    (1 - (1 : ℝ) / 2) / (1 + 1 / 2) ≠ ((1 - (1 / 2 : ℝ) / 2) / (1 + (1 / 2) / 2)) ^ 2 :=
  FRC.Strong.exponential_reading a b

/-- 21:C8, 21:P6 — the post-Newtonian inputs as Taylor brackets on `|U| ≤ 1/2`: the exponential metric's
`A = e^{−2U}`, `B = e^{2U}` against the isotropic Schwarzschild `A_S = ((1 − U/2)/(1 + U/2))²`,
`B_S = (1 + U/2)⁴` satisfy `|A − A_S − U³/6| ≤ 3U⁴` and `|B − B_S − U²/2| ≤ 3|U|³`: the single-potential
inputs consumed by C23 coincide through first post-Newtonian order (`A` to `O(U²)`, `B` to `O(U)`) and part at
2PN with `δA = U³/6`, `δB = U²/2`; the two-body superposition of C23 is the package's. (`FRC.Strong.pn_series`, `Theme/Strong.lean`). -/
theorem pn_series (U : ℝ) (hU : |U| ≤ 1 / 2) :
    |exp (-(2 * U)) - ((1 - U / 2) / (1 + U / 2)) ^ 2 - U ^ 3 / 6| ≤ 3 * U ^ 4 ∧
    |exp (2 * U) - (1 + U / 2) ^ 4 - U ^ 2 / 2| ≤ 3 * |U| ^ 3 :=
  FRC.Strong.pn_series U hU

/-- 21:P2, 21:C10 — the numeral behind the preferred-frame scale: the drive's signature is `O(1/√Ω)` (the paper's
`α₁, α₂`), and at the scale import's `Ω = 1.3 × 10¹²³` (00:A7) this lies between `2.7` and `2.8 × 10⁻⁶²` (the row's
`3 × 10⁻⁶²`). (`FRC.Strong.preferred_frame_scale`, `Theme/Strong.lean`). -/
theorem preferred_frame_scale : (2.7e-62 : ℝ) < 1 / √(1.3e123) ∧ 1 / √(1.3e123) < 2.8e-62 :=
  FRC.Strong.preferred_frame_scale

section lattice
variable {N : ℕ} [NeZero N] {R : Type*} [CommRing R]

/-- The transform on the cycle, `FRC.GravML.dft`. -/
abbrev dft (ζ : R) (f : ZMod N → R) (k : ZMod N) : R := FRC.GravML.dft ζ f k

/-- 21:C9 — anti-self-adjointness of the central difference on the cycle `ℤ/N`: with
`(Δf)(x) = f(x + 1) − f(x − 1)`, `Σ_x f(x)(Δg)(x) = −Σ_x (Δf)(x) g(x)` — `Δᵀ = −Δ`, the identity that carries
the discrete Fierz–Pauli gauge invariance (the package proves the four-term functional's invariance as an exact
integer identity; the paper's `½` in `D_μ = (T_μ − T_μ⁻¹)/2` scales both sides alike). The one-sided
difference `(δf)(x) = f(x + 1) − f(x)` has adjoint the negative *backward* difference,
`Σ_x f(x)(δg)(x) = −Σ_x (f(x) − f(x − 1)) g(x)` — the package's failing control is that this is not `−δ`. (`FRC.GravML.central_difference_adjoint`, `Theme/Gravity.lean`). -/
theorem central_difference_adjoint (f g : ZMod N → R) :
    ∑ x, f x * (g (x + 1) - g (x - 1)) = -∑ x, (f (x + 1) - f (x - 1)) * g x ∧
    ∑ x, f x * (g (x + 1) - g x) = -∑ x, (f x - f (x - 1)) * g x :=
  FRC.GravML.central_difference_adjoint f g

/-- 21:C20 — the finite Fourier shift theorem in both forms, the kick of the two-shift law: the kick, a
character `ζ^{ax}` multiplying `f` in position, shifts the transform, `F(ζ^{a·} f)(k) = (F f)(k + a)`; dually,
shifting `f` by `a` multiplies its transform by the character, `F(f(· − a))(k) = ζ^{ak} (F f)(k)`. (`FRC.GravML.shift_theorem`, `Theme/Gravity.lean`). -/
theorem shift_theorem (ζ : R) (hζ : ζ ^ N = 1) (f : ZMod N → R) (a k : ZMod N) :
    dft ζ (fun x => ζ ^ (a.val * x.val) * f x) k = dft ζ f (k + a) ∧
    dft ζ (fun x => f (x - a)) k = ζ ^ (a.val * k.val) * dft ζ f k :=
  FRC.GravML.shift_theorem ζ hζ f a k

end lattice

/-- 21:C18, 21:P8 — the tilt's numerals at the ledger's `ln Ω = 283.5` (`FRC.Chart.tilt_ledger`, the scale import 00:A7;
before 10 October 2026 this name bracketed the tilt at `281`): `−π²/283.5` between `−0.03482` and `−0.03481` (the row's
`−0.0348`), `+0.07σ` from Planck 2018's `−0.0351 ± 0.0042` [data], and `½ ln Ω` excluded at `8.2σ`. -/
theorem tilt_bracket :
    (0.03481 : ℝ) < π ^ 2 / 283.5 ∧ π ^ 2 / 283.5 < 0.03482 ∧
    (0.068 * 0.0042 : ℝ) < 0.0351 - π ^ 2 / 283.5 ∧ 0.0351 - π ^ 2 / 283.5 < 0.069 * 0.0042 ∧
    (8.2 * 0.0042 : ℝ) < π ^ 2 / (283.5 / 2) - 0.0351 ∧ π ^ 2 / (283.5 / 2) - 0.0351 < 8.25 * 0.0042 :=
  FRC.Chart.tilt_ledger

/-- 21:P3 — the floor `a₀ = cH₀/2π` at the entailed `H₀ = 67.4`: between `1.04` and `1.05 × 10⁻¹⁰ m s⁻²`, `13 %`
low and `0.7σ` against the fitted `1.20 ± 0.24 × 10⁻¹⁰`. -/
theorem floor_value (c H0 : ℝ) (hc : c = 299792458) (hH : H0 = 67.4e3 / 3.0856775814913673e22) :
    (1.04e-10 : ℝ) < c * H0 / (2 * π) ∧ c * H0 / (2 * π) < 1.05e-10 ∧
    (0.868 : ℝ) < c * H0 / (2 * π) / 1.2e-10 ∧ c * H0 / (2 * π) / 1.2e-10 < 0.870 ∧
    (0.65 : ℝ) < (1.2e-10 - c * H0 / (2 * π)) / 0.24e-10 ∧
    (1.2e-10 - c * H0 / (2 * π)) / 0.24e-10 < 0.67 :=
  FRC.Chart.floor_value c H0 hc hH

-- Ledger predicates of 21-gravity (generated by make_predicates.py from docs/21-gravity/21-gravity-ledger.json; edit the ledger, not this section)
/-- 21:A1 (p21001) — The finite substrate: the torsor Carrier, coordinatized by a frame as $\F_\Omega$, its cardinality the Carrier identity $\Omega=4S+1$ with the measured $S\sim10^{122}$ (Planck units) locating the coherence horizon, with the phase cycle $C_{\Omega-1}$, the quarter-turn core $Q_4$, the drive (time is scale-dilation, each Subject's own), the coherence horizon $\sqrt\Omega$, and the resolution floor $1/\sqrt\Omega$. -/
theorem p21001 : (∀ {K : Type u_1} [Field K] (S : ℕ), ↑((4 : ℕ) * S + (1 : ℕ)) = (0 : K) → ↑((4 : ℕ) * S) = (-1 : K) ∧ ↑((4 : ℕ) * S) ^ (2 : ℕ) = (1 : K)) ∧ ∀ (S : ℕ) [Fact (Nat.Prime ((4 : ℕ) * S + (1 : ℕ)))], ∃ r, r ^ (2 : ℕ) = ↑S ∧ ((2 : ZMod ((4 : ℕ) * S + (1 : ℕ))) * r) ^ (2 : ℕ) = (-1 : ZMod ((4 : ℕ) * S + (1 : ℕ))) :=
  @FRC.LedgerML.p21001
/-- 21:A9 (p21009) — The minimal-instance results consumed: the two-face count of the drift (angular $\kap/S$, temporal $\kap/(2S)$, ratio $2$ the double cover), the registration dictionary $p_{\mathrm{sl}}=3(S/\kap)\,r_g$ with the forcing $2\gamma-\beta=1$, and the mass--energy channel $C_{\p-1}\cap C_{2(\p+1)}=Q_4$. -/
theorem p21009 : (∀ (β γ : ℚ), (((2 : ℚ) - β + (2 : ℚ) * γ) / (3 / 2 : ℚ) = (2 : ℚ) ↔ (2 : ℚ) * γ - β = (1 : ℚ)) ∧ ((2 : ℚ) - β + (2 : ℚ) * γ) / (3 / 2 : ℚ) - (2 : ℚ) = (2 / 3 : ℚ) * ((2 : ℚ) * γ - β - (1 : ℚ)) ∧ (γ = (1 : ℚ) → (2 : ℚ) * γ - β = (1 : ℚ) → β = (1 : ℚ) ∧ ((2 : ℚ) + (2 : ℚ) * γ - β) / (3 : ℚ) = (1 : ℚ))) ∧ ∀ (p : ℕ), p % (4 : ℕ) = (1 : ℕ) → (p - (1 : ℕ)).gcd ((2 : ℕ) * (p + (1 : ℕ))) = (4 : ℕ) :=
  @FRC.LedgerML.p21009
set_option linter.defProp false in
/-- 21:C1 (p21016) — The linearised dynamics is the gradient flow of a coherence free energy --- its current derived from the pair tally conditional on channel unity (Lemma~\ref{lem:pairtally}) --- and a locked cluster of cardinality $m$ couples with coefficient exactly $m$. -/
def p21016 := @FRC.LedgerML.p21016
set_option linter.defProp false in
/-- 21:C2 (p21017) — Newton's law $F=-Gm_1m_2/r^2$ with $G=1/4\pi\varkappa$ [chart] (register value $G=2S$): the $r^{-2}$ from harmonicity in the three frame freedoms, the product $m_1m_2$ from coherent additivity. -/
def p21017 := @FRC.LedgerML.p21017
/-- 21:C4 (p21019) — The equivalence principle as an identity; the bias field is clock rate, giving the redshift $\Delta f/f=Gm/rc^2$; the turnaround radius against the Hubble drive. -/
theorem p21019 : ∀ (u : ℝ), (0 : ℝ) ≤ u → u ≤ (1 : ℝ) → |(1 : ℝ) - Real.exp (-u) - u| ≤ u ^ (2 : ℕ) :=
  @FRC.LedgerML.p21019
/-- 21:C5 (p21020) — The magnitude $G=\hbar c/m_P^2$, frame-covariant (a relativity principle for scale); gravity's weakness is cardinality dilution. -/
theorem p21020 : (∀ (S : ℕ) [Fact (Nat.Prime ((4 : ℕ) * S + (1 : ℕ)))], ∃ r, r ^ (2 : ℕ) = ↑S ∧ ((2 : ZMod ((4 : ℕ) * S + (1 : ℕ))) * r) ^ (2 : ℕ) = (-1 : ZMod ((4 : ℕ) * S + (1 : ℕ)))) ∧ ∀ (m Ω : ℝ), (0 : ℝ) < Ω → (m / √Ω) ^ (2 : ℕ) = m ^ (2 : ℕ) / Ω :=
  @FRC.LedgerML.p21020
/-- 21:C7 (p21022) — Channel unity forces the spatial bias to equal the temporal one, $\gamma=1$, restoring the full light deflection $4Gm/c^2b$. -/
theorem p21022 : ∀ (β γ : ℚ), (((2 : ℚ) - β + (2 : ℚ) * γ) / (3 / 2 : ℚ) = (2 : ℚ) ↔ (2 : ℚ) * γ - β = (1 : ℚ)) ∧ ((2 : ℚ) - β + (2 : ℚ) * γ) / (3 / 2 : ℚ) - (2 : ℚ) = (2 / 3 : ℚ) * ((2 : ℚ) * γ - β - (1 : ℚ)) ∧ (γ = (1 : ℚ) → (2 : ℚ) * γ - β = (1 : ℚ) → β = (1 : ℚ) ∧ ((2 : ℚ) + (2 : ℚ) * γ - β) / (3 : ℚ) = (1 : ℚ)) :=
  @FRC.LedgerML.p21022
/-- 21:C8 (p21023) — The exponential isotropic metric by multiplicative composition, with $\beta=\gamma=1$: deflection, Shapiro delay, and perihelion at their observed values. -/
theorem p21023 : (∀ (β γ : ℚ), (((2 : ℚ) - β + (2 : ℚ) * γ) / (3 / 2 : ℚ) = (2 : ℚ) ↔ (2 : ℚ) * γ - β = (1 : ℚ)) ∧ ((2 : ℚ) - β + (2 : ℚ) * γ) / (3 / 2 : ℚ) - (2 : ℚ) = (2 / 3 : ℚ) * ((2 : ℚ) * γ - β - (1 : ℚ)) ∧ (γ = (1 : ℚ) → (2 : ℚ) * γ - β = (1 : ℚ) → β = (1 : ℚ) ∧ ((2 : ℚ) + (2 : ℚ) * γ - β) / (3 : ℚ) = (1 : ℚ))) ∧ ∀ (U : ℝ), |U| ≤ (1 / 2 : ℝ) → |Real.exp (-((2 : ℝ) * U)) - (((1 : ℝ) - U / (2 : ℝ)) / ((1 : ℝ) + U / (2 : ℝ))) ^ (2 : ℕ) - U ^ (3 : ℕ) / (6 : ℝ)| ≤ (3 : ℝ) * U ^ (4 : ℕ) ∧ |Real.exp ((2 : ℝ) * U) - ((1 : ℝ) + U / (2 : ℝ)) ^ (4 : ℕ) - U ^ (2 : ℕ) / (2 : ℝ)| ≤ (3 : ℝ) * |U| ^ (3 : ℕ) :=
  @FRC.LedgerML.p21023
/-- 21:C9 (p21024) — The discrete Fierz--Pauli functional, exactly gauge-invariant and the unique adjacency-local stiffness on the shell (the spin-one case is unique-Maxwell). -/
theorem p21024 : ∀ {N : ℕ} [NeZero N] {R : Type u_1} [CommRing R] (f g : ZMod N → R), ∑ x, f x * (g (x + (1 : ZMod N)) - g (x - (1 : ZMod N))) = -∑ x, (f (x + (1 : ZMod N)) - f (x - (1 : ZMod N))) * g x ∧ ∑ x, f x * (g (x + (1 : ZMod N)) - g x) = -∑ x, (f x - f (x - (1 : ZMod N))) * g x :=
  @FRC.LedgerML.p21024
/-- 21:C11 (p21026) — The nonlinear completion forced: the exact cut-flux law (transfer antisymmetry) plus the winding grading forbid independent static self-sourcing, the clock-comparison cocycle makes the exponential reading unique (exactly the character $\gen^{-\Delta n}$, $e^{-u}$ its observer lift), and Deser's bootstrap does not apply because what gravitates is winding rate. -/
theorem p21026 : ∀ (a b : ℝ), Real.exp (-(a + b)) = Real.exp (-a) * Real.exp (-b) ∧ (∀ (U : ℝ), (-2 : ℝ) < U → U < (2 : ℝ) → Real.exp (-((2 : ℝ) * Real.artanh (U / (2 : ℝ)))) = ((1 : ℝ) - U / (2 : ℝ)) / ((1 : ℝ) + U / (2 : ℝ))) ∧ ((1 : ℝ) - (1 / 2 : ℝ)) / ((1 : ℝ) + (1 / 2 : ℝ)) ≠ (((1 : ℝ) - (1 / 2 : ℝ) / (2 : ℝ)) / ((1 : ℝ) + (1 / 2 : ℝ) / (2 : ℝ))) ^ (2 : ℕ) :=
  @FRC.LedgerML.p21026
/-- 21:C12 (p21027) — The exact saturating static profile and its slip core at $r_*=\sqrt{Gm}$: horizonless, operationally black at $r_f=r_s/\ln\Omega$ --- the exact statement the cut form, $4\pi r^{2}$ its [chart] reading; the $r_f$-anchored claims stated in the substrate coordinate, $r_*<r_f<M$ for $M>(\ln\Omega/2)^{2}$ Planck masses (master E10). -/
theorem p21027 : ∀ (M L Ω : ℝ), (0 : ℝ) < M → (0 : ℝ) < L → L = Real.log Ω → (0 : ℝ) < Ω → Real.exp ((2 : ℝ) * M / ((2 : ℝ) * M / L)) = Ω ∧ (√M < (2 : ℝ) * M / L ↔ (L / (2 : ℝ)) ^ (2 : ℕ) < M) ∧ ((2 : ℝ) * M / L < M ↔ (2 : ℝ) < L) :=
  @FRC.LedgerML.p21027
/-- 21:C13 (p21062) — Area-law entropy $S=c_S'A_f/\ell_P^2$: the $\tfrac14$ the $Q_4$ gauge quotient counted on the shell ($S/A=\kap/\p $ exactly), the Carrier identity $S=(\Omega-1)/4$ at the coherence-horizon shell the same quarter (a consistency, not a closure); the count read as the coordinate area at the operational cut (B7); the identification of the entropy with the channel count (master D15); an exact merger area law $\Delta A=2M_1M_2$ on the count face of the mass; a phase-slip (Hawking-scaling) emission suppressed below one quantum per Hubble time. -/
theorem p21062 : (∀ (κ : ℕ), (4 : ℕ) * (κ * ((4 : ℕ) * κ + (2 : ℕ))) + (1 : ℕ) = ((4 : ℕ) * κ + (1 : ℕ)) ^ (2 : ℕ) ∧ κ * ((4 : ℕ) * κ + (2 : ℕ)) * ((4 : ℕ) * κ + (1 : ℕ)) = κ * (((4 : ℕ) * κ + (1 : ℕ)) * ((4 : ℕ) * κ + (2 : ℕ))) ∧ (4 : ℕ) * (κ * ((4 : ℕ) * κ + (2 : ℕ))) * ((4 : ℕ) * κ + (1 : ℕ)) = ((4 : ℕ) * κ + (1 : ℕ)) * ((4 : ℕ) * κ + (2 : ℕ)) * ((4 : ℕ) * κ)) ∧ (∀ (M₁ M₂ δ : ℤ), (M₁ + M₂) * (M₁ + M₂ + (1 : ℤ)) - M₁ * (M₁ + (1 : ℤ)) - M₂ * (M₂ + (1 : ℤ)) = (2 : ℤ) * M₁ * M₂ ∧ (M₁ + M₂ - δ) * (M₁ + M₂ - δ + (1 : ℤ)) - M₁ * (M₁ + (1 : ℤ)) - M₂ * (M₂ + (1 : ℤ)) = (2 : ℤ) * M₁ * M₂ - ((2 : ℤ) * (M₁ + M₂) + (1 : ℤ)) * δ + δ ^ (2 : ℕ) ∧ ((0 : ℤ) ≤ δ → δ ≤ (2 : ℤ) * (M₁ + M₂) + (1 : ℤ) → (M₁ + M₂ - δ) * (M₁ + M₂ - δ + (1 : ℤ)) - M₁ * (M₁ + (1 : ℤ)) - M₂ * (M₂ + (1 : ℤ)) ≤ (2 : ℤ) * M₁ * M₂) ∧ ((27811 : ℤ) + (1596 : ℤ)) * ((27811 : ℤ) + (1596 : ℤ) + (1 : ℤ)) - (27811 : ℤ) * ((27811 : ℤ) + (1 : ℤ)) - (1596 : ℤ) * ((1596 : ℤ) + (1 : ℤ)) = (88772712 : ℤ)) ∧ ∀ (rs L : ℝ), rs ≠ (0 : ℝ) → L ≠ (0 : ℝ) → (rs / L / rs) ^ (2 : ℕ) = (1 : ℝ) / L ^ (2 : ℕ) :=
  @FRC.LedgerML.p21062
/-- 21:C15 (p21030) — The radiative sector: the quarter-turn conjugate momentum makes the dynamics a wave equation: two helicity-$\pm2$ gravitons at speed $c$, quadrupole radiation; gauge leaves two polarisations. -/
theorem p21030 : ∀ (k : ℝ), (2 : ℝ) - (2 : ℝ) * Real.cos k = (4 : ℝ) * Real.sin (k / (2 : ℝ)) ^ (2 : ℕ) :=
  @FRC.LedgerML.p21030
set_option linter.defProp false in
/-- 21:C16 (p21031) — The order-one constants are determined: $c_S'=\tfrac14$ (the $Q_4$ gauge quotient, counted on an instantiated shell and carried by the Carrier identity), the floor's $2\pi$ the full cycle of the angle--count dictionary (14:B2), its threshold the realisation 32:B3, the recurring constant the solid angle $4\pi$, reducing in the Carrier register to the calibration congruence $(4S)^{2}\equiv1$ (one residue relation). -/
def p21031 := @FRC.LedgerML.p21031
/-- 21:C18 (p21033) — The primordial spectrum: $n_s=1$ the scale-dilation fixed point; the tilt's committed form $-\pi^{2}/\ln\Omega$, $\ln\Omega$ the e-fold count of the frame's scale range, the realisation of master L8, with the measured tilt its falsifier ($\tfrac12\ln\Omega$ excluded at $8.2\sigma$; the linearity condition undefined on a shell); the wrapped chart fixing the low large-angle power. -/
theorem p21033 : (∀ (n : ℝ), (∀ (k : ℝ), (0 : ℝ) < k → k ^ (3 : ℕ) * k ^ n = (1 : ℝ)) ↔ n = (-3 : ℝ)) ∧ 3481e-5 < Real.pi ^ (2 : ℕ) / 283.5 ∧ Real.pi ^ (2 : ℕ) / 283.5 < 3482e-5 ∧ 68e-3 * 42e-4 < 351e-4 - Real.pi ^ (2 : ℕ) / 283.5 ∧ 351e-4 - Real.pi ^ (2 : ℕ) / 283.5 < 69e-3 * 42e-4 ∧ 8.2 * 42e-4 < Real.pi ^ (2 : ℕ) / (283.5 / (2 : ℝ)) - 351e-4 ∧ Real.pi ^ (2 : ℕ) / (283.5 / (2 : ℝ)) - 351e-4 < 8.25 * 42e-4 :=
  @FRC.LedgerML.p21033
/-- 21:C19 (p21064) — The registration crossover made exact: the killed walk is the noise sector, first passage the masking event, the window attribution the framed-rational tally ratio $g_N/f$, and the orbital response now derived (Theorem~\ref{thm:twoshift} with the registered-inertia identity); it rests on the masking barrier (B9) and the corpus's unified sampling clause (master D10), shared with \citep{quantum}. -/
theorem p21064 : (∀ (w : ℝ), (0 : ℝ) < w → w < (1 : ℝ) → w * (((1 : ℝ) - √((1 : ℝ) - w ^ (2 : ℕ))) / w) ^ (2 : ℕ) - (2 : ℝ) * (((1 : ℝ) - √((1 : ℝ) - w ^ (2 : ℕ))) / w) + w = (0 : ℝ) ∧ (0 : ℝ) < ((1 : ℝ) - √((1 : ℝ) - w ^ (2 : ℕ))) / w ∧ ((1 : ℝ) - √((1 : ℝ) - w ^ (2 : ℕ))) / w < (1 : ℝ) ∧ (1 : ℝ) < ((1 : ℝ) + √((1 : ℝ) - w ^ (2 : ℕ))) / w ∧ ∀ (x : ℝ), w * x ^ (2 : ℕ) - (2 : ℝ) * x + w = (0 : ℝ) → x = ((1 : ℝ) - √((1 : ℝ) - w ^ (2 : ℕ))) / w ∨ x = ((1 : ℝ) + √((1 : ℝ) - w ^ (2 : ℕ))) / w) ∧ (∀ (t : ℝ), (0 : ℝ) < t → (0 : ℝ) < (1 : ℝ) - Real.exp (-t) ∧ (1 : ℝ) ≤ t / ((1 : ℝ) - Real.exp (-t)) ∧ (t ≤ (1 : ℝ) → t / ((1 : ℝ) - Real.exp (-t)) ≤ (1 : ℝ) / ((1 : ℝ) - (3 : ℝ) * t / (4 : ℝ))) ∧ ∀ (G M r a₀ v : ℝ), (0 : ℝ) < r → (0 : ℝ) ≤ G * M → (0 : ℝ) ≤ a₀ → v ^ (2 : ℕ) = √(G * M / r ^ (2 : ℕ) * a₀) * r → v ^ (4 : ℕ) = G * M * a₀) ∧ Filter.Tendsto (fun t => t / ((1 : ℝ) - Real.exp (-t))) (nhdsWithin (0 : ℝ) (Set.Ioi (0 : ℝ))) (nhds (1 : ℝ)) :=
  @FRC.LedgerML.p21064
/-- 21:C20 (p21035) — The two-shift update law: kick (finite Fourier shift by the source character) composed with metaplectic transport gives $\Delta^{2}_{\tau}q=-\nabla u$ with $m$ cancelling --- registered inertia and the equivalence principle inside one derived law. -/
theorem p21035 : ∀ {N : ℕ} [NeZero N] {R : Type u_1} [CommRing R] (ζ : R), ζ ^ N = (1 : R) → ∀ (f : ZMod N → R) (a k : ZMod N), FRC.GravML.dft ζ (fun x => ζ ^ (a.val * x.val) * f x) k = FRC.GravML.dft ζ f (k + a) ∧ FRC.GravML.dft ζ (fun x => f (x - a)) k = ζ ^ (a.val * k.val) * FRC.GravML.dft ζ f k :=
  @FRC.LedgerML.p21035
/-- 21:C25 (p21040) — The PPN triangle closed by two routes: channel unity gives $\gamma=1$ (C7), the instance cover forces $2\gamma-\beta=1$ (A9), jointly $\beta=1$ --- Proposition~\ref{prop:ppn} reached independently, the deviation $\tfrac23(2\gamma-\beta-1)$ its falsifier. -/
theorem p21040 : ∀ (β γ : ℚ), (((2 : ℚ) - β + (2 : ℚ) * γ) / (3 / 2 : ℚ) = (2 : ℚ) ↔ (2 : ℚ) * γ - β = (1 : ℚ)) ∧ ((2 : ℚ) - β + (2 : ℚ) * γ) / (3 / 2 : ℚ) - (2 : ℚ) = (2 / 3 : ℚ) * ((2 : ℚ) * γ - β - (1 : ℚ)) ∧ (γ = (1 : ℚ) → (2 : ℚ) * γ - β = (1 : ℚ) → β = (1 : ℚ) ∧ ((2 : ℚ) + (2 : ℚ) * γ - β) / (3 : ℚ) = (1 : ℚ)) :=
  @FRC.LedgerML.p21040
/-- 21:X2 (p21042) — \textbf{No dark-matter particle.} The radial acceleration relation is a registration crossover of the resolution floor, not evidence for undetected mass: galactic dynamics require no dark sector beyond the floor already fixed by $\Omega$. -/
theorem p21042 : Filter.Tendsto (fun t => t / ((1 : ℝ) - Real.exp (-t))) (nhdsWithin (0 : ℝ) (Set.Ioi (0 : ℝ))) (nhds (1 : ℝ)) :=
  @FRC.LedgerML.p21042
/-- 21:X8 (p21048) — \textbf{The weakness of gravity} is cardinality dilution, not a hierarchy to be tuned. -/
theorem p21048 : ∀ (m Ω : ℝ), (0 : ℝ) < Ω → (m / √Ω) ^ (2 : ℕ) = m ^ (2 : ℕ) / Ω :=
  @FRC.LedgerML.p21048
/-- 21:P1 (p21049) — Strong-field signatures at or outside the photon sphere: shadow $+4.6\%$, ringdown $-4.4\%$, ISCO frequency $-6.9\%$ with accretion efficiency $5.48\%$ (against $5.72\%$): one origin, jointly falsifiable, conditional on Theorem~\ref{thm:branch}'s inputs alone. -/
theorem p21049 : (∀ (Gm r : ℝ), (0 : ℝ) < Gm → (0 : ℝ) < r → (2 : ℝ) * Real.exp (1 : ℝ) * Gm ≤ r * Real.exp ((2 : ℝ) * Gm / r) ∧ (r * Real.exp ((2 : ℝ) * Gm / r) = (2 : ℝ) * Real.exp (1 : ℝ) * Gm ↔ r = (2 : ℝ) * Gm)) ∧ (1.0462 < (2 : ℝ) * Real.exp (1 : ℝ) / ((3 : ℝ) * √(3 : ℝ)) ∧ (2 : ℝ) * Real.exp (1 : ℝ) / ((3 : ℝ) * √(3 : ℝ)) < 1.0463 ∧ 0.9557 < (3 : ℝ) * √(3 : ℝ) / ((2 : ℝ) * Real.exp (1 : ℝ)) ∧ (3 : ℝ) * √(3 : ℝ) / ((2 : ℝ) * Real.exp (1 : ℝ)) < 0.9558 ∧ 2.46 < ((4 : ℝ) * Real.exp (1 : ℝ) - (6 : ℝ) * √(3 : ℝ)) * 5.12 ∧ ((4 : ℝ) * Real.exp (1 : ℝ) - (6 : ℝ) * √(3 : ℝ)) * 5.12 < 2.47) ∧ (∀ (r : ℝ), (2 : ℝ) < r → HasDerivAt (fun r => (2 : ℝ) / r + (2 : ℝ) * Real.log r - Real.log (r - (2 : ℝ))) ((r ^ (2 : ℕ) - (6 : ℝ) * r + (4 : ℝ)) / (r ^ (2 : ℕ) * (r - (2 : ℝ)))) r ∧ ((3 : ℝ) + √(5 : ℝ)) ^ (2 : ℕ) - (6 : ℝ) * ((3 : ℝ) + √(5 : ℝ)) + (4 : ℝ) = (0 : ℝ) ∧ (2 : ℝ) < (3 : ℝ) + √(5 : ℝ) ∧ ((3 : ℝ) + √(5 : ℝ) - (1 : ℝ)) / ((3 : ℝ) + √(5 : ℝ) - (2 : ℝ)) = ((3 : ℝ) + √(5 : ℝ)) / (4 : ℝ)) ∧ 547e-4 < (1 : ℝ) - √(Real.exp (-((2 : ℝ) / ((3 : ℝ) + √(5 : ℝ)))) * ((3 : ℝ) + √(5 : ℝ)) / (4 : ℝ)) ∧ (1 : ℝ) - √(Real.exp (-((2 : ℝ) / ((3 : ℝ) + √(5 : ℝ)))) * ((3 : ℝ) + √(5 : ℝ)) / (4 : ℝ)) < 548e-4 ∧ 571e-4 < (1 : ℝ) - √(8 / 9 : ℝ) ∧ (1 : ℝ) - √(8 / 9 : ℝ) < 572e-4 :=
  @FRC.LedgerML.p21049
/-- 21:P7 (p21050) — Floor-surface signatures: no prompt echoes (the exact profile horizonless with no reflecting surface, C12; the round-trip delay to $r_f$ carrying $e^{2u(r_f)}=\Omega$) and no evaporation bursts; a reported echo detection at the stated precision falsifies the construction. -/
theorem p21050 : ∀ (M L Ω : ℝ), (0 : ℝ) < M → (0 : ℝ) < L → L = Real.log Ω → (0 : ℝ) < Ω → Real.exp ((2 : ℝ) * M / ((2 : ℝ) * M / L)) = Ω ∧ (√M < (2 : ℝ) * M / L ↔ (L / (2 : ℝ)) ^ (2 : ℕ) < M) ∧ ((2 : ℝ) * M / L < M ↔ (2 : ℝ) < L) :=
  @FRC.LedgerML.p21050
/-- 21:P8 (p21060) — The primordial tilt $n_s-1=-\pi^{2}/\ln\Omega=-0.0348$ [approx] at $\ln\Omega=283.5$ (the master's scale import), against Planck 2018 $-0.0351\pm0.0042$ ($+0.07\sigma$); $0.25\%$ per factor two in $S$; the neighbouring count $\tfrac12\ln\Omega$ excluded at $8.2\sigma$. -/
theorem p21060 : 3481e-5 < Real.pi ^ (2 : ℕ) / 283.5 ∧ Real.pi ^ (2 : ℕ) / 283.5 < 3482e-5 ∧ 68e-3 * 42e-4 < 351e-4 - Real.pi ^ (2 : ℕ) / 283.5 ∧ 351e-4 - Real.pi ^ (2 : ℕ) / 283.5 < 69e-3 * 42e-4 ∧ 8.2 * 42e-4 < Real.pi ^ (2 : ℕ) / (283.5 / (2 : ℝ)) - 351e-4 ∧ Real.pi ^ (2 : ℕ) / (283.5 / (2 : ℝ)) - 351e-4 < 8.25 * 42e-4 :=
  @FRC.LedgerML.p21060
/-- 21:P2 (p21051) — Preferred-frame effects at $O(1/\sqrt\Omega)=O(10^{-62})$ ($3\times10^{-62}$ at $\Omega=1.3\times10^{123}$): the drive's in-principle signature, far below current $10^{-5}$ bounds. -/
theorem p21051 : 27e-63 < (1 : ℝ) / √13e122 ∧ (1 : ℝ) / √13e122 < 28e-63 :=
  @FRC.LedgerML.p21051
/-- 21:P3 (p21052) — The weak-acceleration floor $a_0=cH_0/2\pi=1.04\times10^{-10}\,\mathrm{m\,s^{-2}}$ at the entailed $H_0=67.4$ \cite{entropy}, against the fitted $1.20\pm0.24\times10^{-10}$: $13\%$ low, $0.7\sigma$ of the systematic-dominated error, no free parameter; the $2\pi$ the dictionary's full cycle (14:B2), the one-cycle-per-period threshold the realisation 32:B3 with its discrete falsifier. -/
theorem p21052 : ∀ (c H0 : ℝ), c = (299792458 : ℝ) → H0 = 674e2 / 30856775814913673e6 → 104e-12 < c * H0 / ((2 : ℝ) * Real.pi) ∧ c * H0 / ((2 : ℝ) * Real.pi) < 105e-12 ∧ 0.868 < c * H0 / ((2 : ℝ) * Real.pi) / 12e-11 ∧ c * H0 / ((2 : ℝ) * Real.pi) / 12e-11 < 0.870 ∧ 0.65 < (12e-11 - c * H0 / ((2 : ℝ) * Real.pi)) / 24e-12 ∧ (12e-11 - c * H0 / ((2 : ℝ) * Real.pi)) / 24e-12 < 0.67 :=
  @FRC.LedgerML.p21052
/-- 21:P4 (p21053) — The radial acceleration relation, $g_{\mathrm{obs}}=g_N/(1-e^{-\sqrt{g_N/a_0}})$, no fitted function beyond the barrier identification (B9), the form the data selected across the four observed acceleration decades, its approach to Newton the discriminant ($0.05$ at $g_N\approx5a_0$ against the simple rational interpolant); the deep limit gives the baryonic Tully--Fisher relation $v^4=GMa_0$. -/
theorem p21053 : (∀ (t : ℝ), (0 : ℝ) < t → (0 : ℝ) < (1 : ℝ) - Real.exp (-t) ∧ (1 : ℝ) ≤ t / ((1 : ℝ) - Real.exp (-t)) ∧ (t ≤ (1 : ℝ) → t / ((1 : ℝ) - Real.exp (-t)) ≤ (1 : ℝ) / ((1 : ℝ) - (3 : ℝ) * t / (4 : ℝ))) ∧ ∀ (G M r a₀ v : ℝ), (0 : ℝ) < r → (0 : ℝ) ≤ G * M → (0 : ℝ) ≤ a₀ → v ^ (2 : ℕ) = √(G * M / r ^ (2 : ℕ) * a₀) * r → v ^ (4 : ℕ) = G * M * a₀) ∧ (∀ (w : ℝ), (0 : ℝ) < w → w < (1 : ℝ) → w * (((1 : ℝ) - √((1 : ℝ) - w ^ (2 : ℕ))) / w) ^ (2 : ℕ) - (2 : ℝ) * (((1 : ℝ) - √((1 : ℝ) - w ^ (2 : ℕ))) / w) + w = (0 : ℝ) ∧ (0 : ℝ) < ((1 : ℝ) - √((1 : ℝ) - w ^ (2 : ℕ))) / w ∧ ((1 : ℝ) - √((1 : ℝ) - w ^ (2 : ℕ))) / w < (1 : ℝ) ∧ (1 : ℝ) < ((1 : ℝ) + √((1 : ℝ) - w ^ (2 : ℕ))) / w ∧ ∀ (x : ℝ), w * x ^ (2 : ℕ) - (2 : ℝ) * x + w = (0 : ℝ) → x = ((1 : ℝ) - √((1 : ℝ) - w ^ (2 : ℕ))) / w ∨ x = ((1 : ℝ) + √((1 : ℝ) - w ^ (2 : ℕ))) / w) ∧ 1.11966 < (1 : ℝ) / ((1 : ℝ) - Real.exp (-√(5 : ℝ))) ∧ (1 : ℝ) / ((1 : ℝ) - Real.exp (-√(5 : ℝ))) < 1.11967 ∧ 1.17082 < (1 / 2 : ℝ) + √((1 / 4 : ℝ) + (1 / 5 : ℝ)) ∧ (1 / 2 : ℝ) + √((1 / 4 : ℝ) + (1 / 5 : ℝ)) < 1.17083 ∧ 511e-4 < (1 / 2 : ℝ) + √((1 / 4 : ℝ) + (1 / 5 : ℝ)) - (1 : ℝ) / ((1 : ℝ) - Real.exp (-√(5 : ℝ))) ∧ (1 / 2 : ℝ) + √((1 / 4 : ℝ) + (1 / 5 : ℝ)) - (1 : ℝ) / ((1 : ℝ) - Real.exp (-√(5 : ℝ))) < 512e-4 :=
  @FRC.LedgerML.p21053
/-- 21:P6 (p21055) — The 2PN periastron excess $\delta\dot\omega/\dot\omega\approx1.5\times10^{-6}$ for PSR~J0737$-$3039, today degenerate with the mass refit; decisive either way once an independent observable fixes $M_{\mathrm{tot}}$ at $10^{-6}$. Independent of the coherent-fraction falsifier of \citep{quantum}; the ledger carries both. -/
theorem p21055 : ∀ (U : ℝ), |U| ≤ (1 / 2 : ℝ) → |Real.exp (-((2 : ℝ) * U)) - (((1 : ℝ) - U / (2 : ℝ)) / ((1 : ℝ) + U / (2 : ℝ))) ^ (2 : ℕ) - U ^ (3 : ℕ) / (6 : ℝ)| ≤ (3 : ℝ) * U ^ (4 : ℕ) ∧ |Real.exp ((2 : ℝ) * U) - ((1 : ℝ) + U / (2 : ℝ)) ^ (4 : ℕ) - U ^ (2 : ℕ) / (2 : ℝ)| ≤ (3 : ℝ) * |U| ^ (3 : ℕ) :=
  @FRC.LedgerML.p21055
-- end ledger predicates

end FRC.Gravity
