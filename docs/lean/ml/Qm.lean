import Mathlib
import FrcMathlib.Theme.Quantum
import FrcMathlib.Theme.Chart
import FrcMathlib.Keys.Chart
import FrcMathlib.Keys.Quantum

/-!
# 22-quantum — the paper module on Mathlib: the ledger's identities and the chart rows under the paper's name (15 October 2026)

Rows of the predicate ledger of *Quantum Observation over Finite Holographic Substrate* (tree `22-quantum-20260625`)
whose content is read on the ledger itself or against the continuum: the Sorkin hierarchy on every commutative ring
(C8, X8, P2), the weight of a Gaussian-integer amplitude as a nonnegative integer (C7, X1) and the Hadamard layers
with the minimal denominator on the Gaussian integers (C14, P5) in
`FrcMathlib/Theme/Quantum.lean` (`FRC.QuantumML`, exact); the Tsirelson value `2√2` (C17, X7, P3, C25), the singlet law
(C17), the channel's chart (C19, P1), the granularity ceiling and the Ω ledger's floors at the scale import's anchor
(A5, C14, P5, Z2) in `FrcMathlib/Theme/Chart.lean` (`FRC.Chart`, the chart theme, where the reals live). Every name
here is an alias; the exact content of the paper is the core's (`FrcCore/Qm.lean` and the themes it cites).
-/

namespace FRC.Qm

open Real

/-! ## Old names (15 October 2026): every declaration of this module is an alias of a theme's (`FRC.QuantumML`,
`FRC.Chart`), under the paper's name -/

/-- 22:C8, 22:X8, 22:P2 — the Sorkin hierarchy on every commutative ring with an additive conjugation
(`FRC.QuantumML.sorkin_hierarchy`, `Theme/Quantum.lean`). -/
theorem sorkin_hierarchy {R : Type*} [CommRing R] {c : R → R} (hc : ∀ x y, c (x + y) = c x + c y) (a : ℕ → R) :
    ∀ k x, FRC.QuantumML.mixedDiff a (fun x => x * c x) (k + 3) x = 0 :=
  FRC.QuantumML.sorkin_hierarchy hc a

/-- 22:C14 — the Hadamard layers on `ℤ[i]` and the minimal denominator (`FRC.QuantumML.gaussian_layers`,
`gaussian_minimal`, `Theme/Quantum.lean`). -/
theorem gaussian_layers (m : ℕ) :
    FRC.QuantumML.onePlusI ^ (2 * m) = 2 ^ m * FRC.QuantumML.gi ^ m ∧
    FRC.QuantumML.onePlusI ^ (2 * m + 1) = 2 ^ m * FRC.QuantumML.gi ^ m * FRC.QuantumML.onePlusI :=
  FRC.QuantumML.gaussian_layers m

/-- 22:C17, 22:X7, 22:C25, 22:P3 [chart] — the Tsirelson value `2√2` (`FRC.Chart.tsirelson_real`, `Theme/Chart.lean`). -/
theorem tsirelson_real :
    FRC.Chart.zeta8 + FRC.Chart.zeta8⁻¹ = (Real.sqrt 2 : ℂ) ∧
    2 * (FRC.Chart.zeta8 + FRC.Chart.zeta8⁻¹) = (2 * Real.sqrt 2 : ℝ) ∧
    (2 * (FRC.Chart.zeta8 + FRC.Chart.zeta8⁻¹)) ^ 2 = 8 :=
  FRC.Chart.tsirelson_real

/-- 22:C14, 22:P5 [chart] — the ceiling at the anchor (`FRC.Chart.ceiling_bracket`, `Theme/Chart.lean`). -/
theorem ceiling_bracket (Λ ℓP r S Ω : ℝ) (hΛ : Λ = 1.088e-52) (hℓ : ℓP = 1.616255e-35)
    (hr2 : r ^ 2 = 3 / Λ) (hS : S = π * (r / ℓP) ^ 2) (hΩ : Ω = 4 * S + 1) :
    (2 : ℝ) ^ 408 < Ω ∧ Ω / 4 < (2 : ℝ) ^ 408 ∧ (2 : ℝ) ^ 204 < √Ω ∧ √Ω / 4 < (2 : ℝ) ^ 204 :=
  FRC.Chart.ceiling_bracket Λ ℓP r S Ω hΛ hℓ hr2 hS hΩ

/-- 22:C7, 22:X1 — the ledger weight `z z̄ = N(z)` is a nonnegative integer, the coincidence count
(`FRC.QuantumML.pair_count_tally`, `Theme/Quantum.lean`). -/
theorem pair_count_tally (z : GaussianInt) : z * star z = (Zsqrtd.norm z : GaussianInt) ∧ 0 ≤ Zsqrtd.norm z :=
  FRC.QuantumML.pair_count_tally z

/-- 22:C8 — `I₂` is generically nonzero on the ledger: on `ℤ[i]` with the conjugation and the paths `a = b = 1`,
`I₂ = 2` (`FRC.QuantumML.sorkin_second_witness`, `Theme/Quantum.lean`). -/
theorem sorkin_second_witness :
    FRC.QuantumML.mixedDiff (fun _ => (1 : GaussianInt)) (fun x => x * star x) 2 0 = 2 :=
  FRC.QuantumML.sorkin_second_witness

/-- 22:C14 — the minimal tally norm is the square of the minimal denominator, `T(k) = (2^{⌈k/2⌉})²`
(`FRC.QuantumML.tally_norm_eq`, `Theme/Quantum.lean`). -/
theorem tally_norm_eq (k : ℕ) : 2 ^ (k + k % 2) = (2 ^ ((k + 1) / 2)) ^ 2 :=
  FRC.QuantumML.tally_norm_eq k

/-- 22:C19 [chart] — the channel entangles off the trivial phase: `sin(φ/2) ≠ 0` for `0 < φ < 2π`
(`FRC.Chart.channel_entangles`, `Theme/Chart.lean`). -/
theorem channel_entangles (φ : ℝ) (h0 : 0 < φ) (h1 : φ < 2 * Real.pi) : Real.sin (φ / 2) ≠ 0 :=
  FRC.Chart.channel_entangles φ h0 h1

/-- 22:C14, 22:P5 — `2` does not divide `i^m (1 + i)`: the minimal denominator (`FRC.QuantumML.gaussian_minimal`,
`Theme/Quantum.lean`). -/
theorem gaussian_minimal (m : ℕ) : ¬ (2 : GaussianInt) ∣ FRC.QuantumML.gi ^ m * FRC.QuantumML.onePlusI :=
  FRC.QuantumML.gaussian_minimal m

/-- 22:C14 — the norm of `k` layers is `2^k` (`FRC.QuantumML.gaussian_norm`, `Theme/Quantum.lean`). -/
theorem gaussian_norm (k : ℕ) : Zsqrtd.norm (FRC.QuantumML.onePlusI ^ k) = 2 ^ k :=
  FRC.QuantumML.gaussian_norm k

/-- 22:C17 [chart] — the singlet law `E(Δ) = cos(πΔ/40)` (`FRC.Chart.singlet_law`, `Theme/Chart.lean`). -/
theorem singlet_law (Δ : ℕ) :
    (Complex.exp ((2 * π * Δ / 80 : ℝ) * Complex.I)).re = Real.cos (π * Δ / 40) :=
  FRC.Chart.singlet_law Δ

/-- 22:C19, 22:P1 [chart] — the channel's chart: `V = cos(φ/2)`, `C = sin(φ/2)`, `V² + C² = 1` (`FRC.Chart.channel_chart`,
`Theme/Chart.lean`). -/
theorem channel_chart (φ : ℝ) :
    (Complex.exp ((φ / 2 : ℝ) * Complex.I) + Complex.exp (-((φ / 2 : ℝ) * Complex.I))) / 2 =
      (Real.cos (φ / 2) : ℂ) ∧
    (Complex.exp ((φ / 2 : ℝ) * Complex.I) - Complex.exp (-((φ / 2 : ℝ) * Complex.I))) / (2 * Complex.I) =
      (Real.sin (φ / 2) : ℂ) ∧
    Real.cos (φ / 2) ^ 2 + Real.sin (φ / 2) ^ 2 = 1 ∧ Real.sin (0 / 2) = 0 :=
  FRC.Chart.channel_chart φ

/-- 22:A5, 22:Z2 [chart] — the Ω ledger's floors below the anchor (`FRC.Chart.omega_floors`, `Theme/Chart.lean`). -/
theorem omega_floors (Λ ℓP r S Ω : ℝ) (hΛ : Λ = 1.088e-52) (hℓ : ℓP = 1.616255e-35)
    (hr2 : r ^ 2 = 3 / Λ) (hS : S = π * (r / ℓP) ^ 2) (hΩ : Ω = 4 * S + 1) :
    (3e12 : ℝ) ^ 4 = 8.1e49 ∧ (3e12 : ℝ) ^ 4 < Ω ∧ (1e22 : ℝ) < Ω ∧ (2 : ℝ) ^ 60 < Ω :=
  FRC.Chart.omega_floors Λ ℓP r S Ω hΛ hℓ hr2 hS hΩ

-- Ledger predicates of 22-quantum (generated by make_predicates.py from docs/22-quantum/22-quantum-ledger.json; edit the ledger, not this section)
set_option linter.defProp false in
/-- 22:A5 (p22005) — The window discipline, committed: the coherence horizon $\sqrt\Omega$, the decidability horizon $\Omega^{1/4}$, and the committed cardinality $\Omega\sim1.3\times10^{123}$ [chart] (the corpus's scale import, master A7) --- declared inputs of the programme, their cost recorded in the $\Omega$ ledger. -/
def p22005 := @FRC.LedgerML.p22005
/-- 22:C7 (p22023) — Squared amplitudes are coincidence counts (the pair-count identity), realized tallies on $\Z[\im]$ for stationary core-valued states of definite drive eigenvalue; a distinct-eigenvalue superposition registers the integral drive-frequency count; for a pure winding the weights are $d^2[r\equiv k]$. -/
theorem p22023 : ∀ (z : GaussianInt), z * star z = ↑(Zsqrtd.norm z) ∧ (0 : ℤ) ≤ Zsqrtd.norm z :=
  @FRC.LedgerML.p22023
/-- 22:C8 (p22024) — Sorkin nullity: $I_k=0$ for every $k\ge3$, exactly, on every channel and outcome, with $I_2$ generically nonzero. -/
theorem p22024 : (∀ {R : Type u_1} [CommRing R] {c : R → R}, (∀ (x y : R), c (x + y) = c x + c y) → ∀ (a : ℕ → R) (k : ℕ) (x : R), FRC.QuantumML.mixedDiff a (fun x => x * c x) (k + (3 : ℕ)) x = (0 : R)) ∧ FRC.QuantumML.mixedDiff (fun x => (1 : GaussianInt)) (fun x => x * star x) (2 : ℕ) (0 : GaussianInt) = (2 : GaussianInt) :=
  @FRC.LedgerML.p22024
/-- 22:C14 (p22030) — The granularity ceiling: the representable coherent-splitting depth is the largest $k$ with $d\,T(k)<\Omega$, $T(k)=2^{k+[k\text{ odd}]}$ the minimal tally norm, and resolution finer than $1/\Omega$ lies outside the derived Born regime. -/
theorem p22030 : (∀ (m : ℕ), FRC.QuantumML.onePlusI ^ ((2 : ℕ) * m) = (2 : GaussianInt) ^ m * FRC.QuantumML.gi ^ m ∧ FRC.QuantumML.onePlusI ^ ((2 : ℕ) * m + (1 : ℕ)) = (2 : GaussianInt) ^ m * FRC.QuantumML.gi ^ m * FRC.QuantumML.onePlusI) ∧ (∀ (m : ℕ), ¬(2 : GaussianInt) ∣ FRC.QuantumML.gi ^ m * FRC.QuantumML.onePlusI) ∧ (∀ (k : ℕ), Zsqrtd.norm (FRC.QuantumML.onePlusI ^ k) = (2 : ℤ) ^ k) ∧ ∀ (k : ℕ), (2 : ℕ) ^ (k + k % (2 : ℕ)) = ((2 : ℕ) ^ ((k + (1 : ℕ)) / (2 : ℕ))) ^ (2 : ℕ) :=
  @FRC.LedgerML.p22030
/-- 22:C17 (p22033) — Exact Tsirelson saturation: the singlet law $E(\Delta)=\cos(\pi\Delta/40)$ [chart], $S=2(\zeta_8+\zeta_8^{-1})$, $S^2=8$, the exhaustive $80^3$ sweep never exceeding it [chart]; no-signalling and the composite reduction commute. -/
theorem p22033 : (FRC.Chart.zeta8 + FRC.Chart.zeta8⁻¹ = ↑√(2 : ℝ) ∧ (2 : ℂ) * (FRC.Chart.zeta8 + FRC.Chart.zeta8⁻¹) = ↑((2 : ℝ) * √(2 : ℝ)) ∧ ((2 : ℂ) * (FRC.Chart.zeta8 + FRC.Chart.zeta8⁻¹)) ^ (2 : ℕ) = (8 : ℂ)) ∧ ∀ (Δ : ℕ), (Complex.exp (↑((2 : ℝ) * Real.pi * ↑Δ / (80 : ℝ)) * Complex.I)).re = Real.cos (Real.pi * ↑Δ / (40 : ℝ)) :=
  @FRC.LedgerML.p22033
/-- 22:C19 (p22035) — The gravitational channel entangles exactly, $C^2=\sin^2(\varphi/2)$ [chart], with the pure-channel complementarity $V^2+C^2=1$. -/
theorem p22035 : (∀ (φ : ℝ), (Complex.exp (↑(φ / (2 : ℝ)) * Complex.I) + Complex.exp (-(↑(φ / (2 : ℝ)) * Complex.I))) / (2 : ℂ) = ↑(Real.cos (φ / (2 : ℝ))) ∧ (Complex.exp (↑(φ / (2 : ℝ)) * Complex.I) - Complex.exp (-(↑(φ / (2 : ℝ)) * Complex.I))) / ((2 : ℂ) * Complex.I) = ↑(Real.sin (φ / (2 : ℝ))) ∧ Real.cos (φ / (2 : ℝ)) ^ (2 : ℕ) + Real.sin (φ / (2 : ℝ)) ^ (2 : ℕ) = (1 : ℝ) ∧ Real.sin (0 / 2 : ℝ) = (0 : ℝ)) ∧ ∀ (φ : ℝ), (0 : ℝ) < φ → φ < (2 : ℝ) * Real.pi → Real.sin (φ / (2 : ℝ)) ≠ (0 : ℝ) :=
  @FRC.LedgerML.p22035
/-- 22:C25 (p22041) — The measurement problem dissolved: Kochen--Specker poses no separate threat because values exist only as Subject-relative quotient phases, carried together with the Tsirelson strength $2\sqrt2$ [chart]. -/
theorem p22041 : FRC.Chart.zeta8 + FRC.Chart.zeta8⁻¹ = ↑√(2 : ℝ) ∧ (2 : ℂ) * (FRC.Chart.zeta8 + FRC.Chart.zeta8⁻¹) = ↑((2 : ℝ) * √(2 : ℝ)) ∧ ((2 : ℂ) * (FRC.Chart.zeta8 + FRC.Chart.zeta8⁻¹)) ^ (2 : ℕ) = (8 : ℂ) :=
  @FRC.LedgerML.p22041
/-- 22:X1 (p22044) — \textbf{The Born rule} is a coincidence count, the unique window lift of its carrier shadow, not a postulated quadratic functional --- on its stationary domain, where the weights are uniform over the fibres; non-uniform statistics are read through the engineered-core readout (C11). -/
theorem p22044 : ∀ (z : GaussianInt), z * star z = ↑(Zsqrtd.norm z) ∧ (0 : ℤ) ≤ Zsqrtd.norm z :=
  @FRC.LedgerML.p22044
/-- 22:X7 (p22050) — \textbf{The Tsirelson boundary} is attained as a ring identity, $S=2(\zeta_8+\zeta_8^{-1})=2\sqrt2$ [chart], so a relational finite substrate carries full quantum correlation strength, not merely quantum vocabulary. -/
theorem p22050 : FRC.Chart.zeta8 + FRC.Chart.zeta8⁻¹ = ↑√(2 : ℝ) ∧ (2 : ℂ) * (FRC.Chart.zeta8 + FRC.Chart.zeta8⁻¹) = ↑((2 : ℝ) * √(2 : ℝ)) ∧ ((2 : ℂ) * (FRC.Chart.zeta8 + FRC.Chart.zeta8⁻¹)) ^ (2 : ℕ) = (8 : ℂ) :=
  @FRC.LedgerML.p22050
/-- 22:X8 (p22051) — \textbf{Higher-order interference} is forbidden exactly: the Sorkin hierarchy is zero with a forbidden neighbourhood, not a small number to be measured down. -/
theorem p22051 : ∀ {R : Type u_1} [CommRing R] {c : R → R}, (∀ (x y : R), c (x + y) = c x + c y) → ∀ (a : ℕ → R) (k : ℕ) (x : R), FRC.QuantumML.mixedDiff a (fun x => x * c x) (k + (3 : ℕ)) x = (0 : R) :=
  @FRC.LedgerML.p22051
/-- 22:P1 (p22052) — Gravitationally induced entanglement at exactly the Newtonian rate [chart], $V^2+C^2=1$ on the pure channel: equal force but unequal entanglement --- a source gravitates by its full mass while the systematic conditional phase, the calibrated discriminator, is carried by the coherent sectors alone, the fully incoherent channel separable at generic (nondegenerate) geometry. The one dated forward prediction. -/
theorem p22052 : ∀ (φ : ℝ), (Complex.exp (↑(φ / (2 : ℝ)) * Complex.I) + Complex.exp (-(↑(φ / (2 : ℝ)) * Complex.I))) / (2 : ℂ) = ↑(Real.cos (φ / (2 : ℝ))) ∧ (Complex.exp (↑(φ / (2 : ℝ)) * Complex.I) - Complex.exp (-(↑(φ / (2 : ℝ)) * Complex.I))) / ((2 : ℂ) * Complex.I) = ↑(Real.sin (φ / (2 : ℝ))) ∧ Real.cos (φ / (2 : ℝ)) ^ (2 : ℕ) + Real.sin (φ / (2 : ℝ)) ^ (2 : ℕ) = (1 : ℝ) ∧ Real.sin (0 / 2 : ℝ) = (0 : ℝ) :=
  @FRC.LedgerML.p22052
/-- 22:P2 (p22053) — Third-order interference exactly zero at every accessible scale, any wrap quantised to a multiple of $\Omega$: a single confirmed small $I_3\neq0$ falsifies outright. -/
theorem p22053 : ∀ {R : Type u_1} [CommRing R] {c : R → R}, (∀ (x y : R), c (x + y) = c x + c y) → ∀ (a : ℕ → R) (k : ℕ) (x : R), FRC.QuantumML.mixedDiff a (fun x => x * c x) (k + (3 : ℕ)) x = (0 : R) :=
  @FRC.LedgerML.p22053
/-- 22:P3 (p22054) — The Tsirelson value $S=2\sqrt2$ exact [chart] and the network behaviour of complex (not real) quantum theory: vacuum dispersion, $S\neq2\sqrt2$, or non-quantum network behaviour each falsify. -/
theorem p22054 : FRC.Chart.zeta8 + FRC.Chart.zeta8⁻¹ = ↑√(2 : ℝ) ∧ (2 : ℂ) * (FRC.Chart.zeta8 + FRC.Chart.zeta8⁻¹) = ↑((2 : ℝ) * √(2 : ℝ)) ∧ ((2 : ℂ) * (FRC.Chart.zeta8 + FRC.Chart.zeta8⁻¹)) ^ (2 : ℕ) = (8 : ℂ) :=
  @FRC.LedgerML.p22054
/-- 22:P5 (p22056) — Quantum computation succeeds as standard quantum mechanics prescribes at every accessible depth; the first deviation, if any, is quantised at the unit-core ceiling $k^*=408$ ($204$ for $\sqrt\Omega$) [chart], not gradual. -/
theorem p22056 : (∀ (Λ ℓP r S Ω : ℝ), Λ = 1088e-55 → ℓP = 1616255e-41 → r ^ (2 : ℕ) = (3 : ℝ) / Λ → S = Real.pi * (r / ℓP) ^ (2 : ℕ) → Ω = (4 : ℝ) * S + (1 : ℝ) → (2 : ℝ) ^ (408 : ℕ) < Ω ∧ Ω / (4 : ℝ) < (2 : ℝ) ^ (408 : ℕ) ∧ (2 : ℝ) ^ (204 : ℕ) < √Ω ∧ √Ω / (4 : ℝ) < (2 : ℝ) ^ (204 : ℕ)) ∧ ∀ (m : ℕ), ¬(2 : GaussianInt) ∣ FRC.QuantumML.gi ^ m * FRC.QuantumML.onePlusI :=
  @FRC.LedgerML.p22056
set_option linter.defProp false in
/-- 22:Z2 (p22061) — The committed $\Omega$ anchor and the binding floor: the carrier scale is fixed by the verified Riemann height through $\Omega^{1/4}$ [chart], and a single off-line zero below $\Omega^{1/4}$ falsifies from a desk. -/
def p22061 := @FRC.LedgerML.p22061
-- end ledger predicates

end FRC.Qm
