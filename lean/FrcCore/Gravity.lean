import FrcCore.Frame
import FrcCore.Orbit
import FrcCore.Instances
import FrcCore.Theme.Gravity
import FrcCore.Keys.Fourier
import FrcCore.Keys.Gravity

/-!
# 21-gravity — the Carrier register and the count face on every frame, no axioms

The finite content of *Gravitation as Phase Synchronisation over Finite Holographic Substrate* (tree
`21-gravity-20260623`) from first principles. On every frame `(τ; 0, 1, g)` of capacity `κ` (`p = 4κ + 1`):
the calibration congruence `4κ = −1`, `(4κ)² = 1` (C16); the register value of the Newton constant `G = 2κ`
— `2G = −1`, `(−2) G = 1` (the face convention `4π ↦ −2`), the Gauss count `(2 · 4κ) G = 1`, `c² = 2⁻¹ = 2κ + 1`
with `2c² = 1`, and `G = −c²` (C2, C5, C16); the action quantum as a member of the quarter-turn pair,
`ħ = g^κ = −i` (`Frame.quarterTurn g κ = −g^κ`) with `ħ² = −1`, and `ħ = 2r` for the square root `r = g^κ c²` of
the capacity, `r² = κ` (C5). In the count register: the count
face of the area law, `4S + 1 = p²` for `S = κ(4κ + 2)`, `Sp = κA` and `4Sp = A(p − 1)` for `A = p(p + 1)`
(C13); the two-face ratio `κ/S : κ/(2S) = 2` and the fibre product `(p − 1)(Ω − 1) = 4 · 4κS` (A9). Decided
by the kernel: the register on `𝔽₁₃` (`κ = 3`, drive `2`) and `𝔽₁₇` (`κ = 4`, drive `3`), the merger law's
instance `27 811 + 1 596 → 29 407` with `ΔA = 88 772 712` (C13), and the laboratory Carrier `Ω = 2 408 561`:
`4S = 2 408 560 = −1`, `(4S)² = 1`, `G = 1 204 280` with `2G = −1`, `(−2) G = 1`, the Gauss count, `ħ = 18 688`
with `ħ² = −1`, `ħ = 2 · 9 344` and `9 344² = S = 602 140` (C2, C5, C16; the residues `c = 171 106` and
`G = −c²` are `Dimensions.carrierLab`). Since task LM27 the count face's identities are the gravity theme's
`FRC.Grav.count_identity` (`Theme/Gravity.lean`), and since 10 October 2026 the register on every frame (`calibration`,
`newton_residue`, `hbar_root`, `two_face_count`) and the kernel-decided values (`register13_17`, `merger_instance`,
`lab_register`) are the theme's too; every name here is an alias. Every declaration is checked
to depend on no axiom (`check_core_axioms.py`).
-/

namespace FRC.Gravity

open FRC.Shell

/-! ## Old names (10 October 2026): every declaration of this module is an alias of the gravity theme's (`FRC.Grav`,
`Theme/Gravity.lean`), under the paper's name -/

/-! ### The register on every frame (21:A1, A9, C2, C5, C16) -/
section register

variable {p : Nat} [Pos p] {κ : Nat} {g : Shell p}

/-- 21:C16, 21:A1 — the calibration congruence on every frame (`FRC.Grav.calibration`, `Theme/Gravity.lean`). -/
theorem calibration (F : Frame p κ g) :
    (ofNat (4 * κ) : Shell p) = -1 ∧ (ofNat (4 * κ) : Shell p) * ofNat (4 * κ) = 1 :=
  FRC.Grav.calibration F

/-- 21:C2, 21:C5, 21:C16 — the register value of the Newton constant on every frame (`FRC.Grav.newton_residue`). -/
theorem newton_residue (F : Frame p κ g) :
    (2 : Shell p) * ofNat (2 * κ) = -1 ∧ (-2 : Shell p) * ofNat (2 * κ) = 1 ∧
    (2 * ofNat (4 * κ) : Shell p) * ofNat (2 * κ) = 1 ∧
    (2 : Shell p) * ofNat (2 * κ + 1) = 1 ∧ (ofNat (2 * κ) : Shell p) = -ofNat (2 * κ + 1) :=
  FRC.Grav.newton_residue F

/-- 21:C5 — the action quantum on every frame as the quarter-turn pair and the root of the capacity
(`FRC.Grav.hbar_root`). -/
theorem hbar_root (F : Frame p κ g) :
    (g ^ κ) ^ 2 = -1 ∧ (g ^ κ * ofNat (2 * κ + 1)) * (g ^ κ * ofNat (2 * κ + 1)) = ofNat κ ∧
    (2 : Shell p) * (g ^ κ * ofNat (2 * κ + 1)) = g ^ κ :=
  FRC.Grav.hbar_root F

end register

/-- 21:A9 — the two-face count and the fibre product (`FRC.Grav.two_face_count`). -/
theorem two_face_count (κ S : Nat) :
    κ * (2 * S) = 2 * (κ * S) ∧ (4 * κ) * (4 * S) = 4 * (4 * (κ * S)) :=
  FRC.Grav.two_face_count κ S

/-! ### The values decided by the kernel (21:C2, C5, C13, C16) -/
section values

/-- 21:C2, 21:C5, 21:C16 — the register on `𝔽₁₃` and `𝔽₁₇` (`FRC.Grav.register13_17`). -/
theorem register13_17 :
    (12 : Shell 13) = -1 ∧ 2 * (6 : Shell 13) = -1 ∧ 2 * (7 : Shell 13) = 1 ∧ (6 : Shell 13) = -7 ∧
    (2 : Shell 13) ^ 3 = 8 ∧ (8 : Shell 13) * 8 = -1 ∧ (4 : Shell 13) * 4 = 3 ∧ 2 * (4 : Shell 13) = 8 ∧
    (16 : Shell 17) = -1 ∧ 2 * (8 : Shell 17) = -1 ∧ 2 * (9 : Shell 17) = 1 ∧ (8 : Shell 17) = -9 ∧
    (3 : Shell 17) ^ 4 = 13 ∧ (13 : Shell 17) * 13 = -1 ∧ (15 : Shell 17) * 15 = 4 ∧
    2 * (15 : Shell 17) = 13 := FRC.Grav.register13_17

/-- 21:C13 — the merger law's instance on the count face (`FRC.Grav.merger_instance`). -/
theorem merger_instance :
    29407 * (29407 + 1) = 27811 * (27811 + 1) + 1596 * (1596 + 1) + 88772712 ∧
    2 * (27811 * 1596) = 88772712 ∧ 27811 + 1596 = 29407 := FRC.Grav.merger_instance

/-- 21:C2, 21:C5, 21:C16 — the laboratory Carrier `Ω = 2 408 561`, host-decided (`FRC.Grav.lab_register`). -/
theorem lab_register :
    4 * 602140 = 2408560 ∧ (2408560 : Shell 2408561) = -1 ∧
    (2408560 : Shell 2408561) * 2408560 = 1 ∧
    2 * (1204280 : Shell 2408561) = -1 ∧ (-2 : Shell 2408561) * 1204280 = 1 ∧
    (2 * (2408560 : Shell 2408561)) * 1204280 = 1 ∧
    (18688 : Shell 2408561) * 18688 = -1 ∧ 2 * (9344 : Shell 2408561) = 18688 ∧
    (9344 : Shell 2408561) * 9344 = 602140 := FRC.Grav.lab_register

end values

/-! ### The count face (ledger migration, task LM27) -/

/-- 21:C13 — the count face of the area law on `p = 4κ + 1` (21-gravity's name; the theorem is
`FRC.Grav.count_identity` in `Theme/Gravity.lean`, task LM27): `4S + 1 = p²`, `Sp = κA`, `4Sp = A(p − 1)`. -/
theorem count_identity (κ : Nat) :
    4 * (κ * (4 * κ + 2)) + 1 = (4 * κ + 1) * (4 * κ + 1) ∧
    κ * (4 * κ + 2) * (4 * κ + 1) = κ * ((4 * κ + 1) * (4 * κ + 2)) ∧
    4 * (κ * (4 * κ + 2)) * (4 * κ + 1) = ((4 * κ + 1) * (4 * κ + 2)) * (4 * κ) :=
  FRC.Grav.count_identity κ

-- Ledger predicates of 21-gravity (generated by make_predicates.py from docs/21-gravity/21-gravity-ledger.json; edit the ledger, not this section)
/-- 21:A1 (p21001) — The finite substrate: the torsor Carrier, coordinatized by a frame as $\F_\Omega$, its cardinality the Carrier identity $\Omega=4S+1$ with the measured $S\sim10^{122}$ (Planck units) locating the coherence horizon, with the phase cycle $C_{\Omega-1}$, the quarter-turn core $Q_4$, the drive (time is scale-dilation, each Subject's own), the coherence horizon $\sqrt\Omega$, and the resolution floor $1/\sqrt\Omega$. -/
theorem p21001 : ∀ {p : Nat} [FRC.Pos p] {κ : Nat} {g : FRC.Shell p}, FRC.Shell.Frame p κ g → FRC.Shell.ofNat ((4 : Nat) * κ) = (-1 : FRC.Shell p) ∧ FRC.Shell.ofNat ((4 : Nat) * κ) * FRC.Shell.ofNat ((4 : Nat) * κ) = (1 : FRC.Shell p) :=
  @FRC.Ledger.p21001
/-- 21:A9 (p21009) — The minimal-instance results consumed: the two-face count of the drift (angular $\kap/S$, temporal $\kap/(2S)$, ratio $2$ the double cover), the registration dictionary $p_{\mathrm{sl}}=3(S/\kap)\,r_g$ with the forcing $2\gamma-\beta=1$, and the mass--energy channel $C_{\p-1}\cap C_{2(\p+1)}=Q_4$. -/
theorem p21009 : (∀ (κ S : Nat), κ * ((2 : Nat) * S) = (2 : Nat) * (κ * S) ∧ (4 : Nat) * κ * ((4 : Nat) * S) = (4 : Nat) * ((4 : Nat) * (κ * S))) ∧ ∀ {p : Nat} [FRC.Pos p] (κ : Nat) (x : FRC.Shell p), x ^ ((4 : Nat) * κ) = (1 : FRC.Shell p) ∧ x ^ ((2 : Nat) * ((4 : Nat) * κ + (2 : Nat))) = (1 : FRC.Shell p) ↔ x ^ (4 : Nat) = (1 : FRC.Shell p) :=
  @FRC.Ledger.p21009
/-- 21:C1 (p21016) — The linearised dynamics is the gradient flow of a coherence free energy --- its current derived from the pair tally conditional on channel unity (Lemma~\ref{lem:pairtally}) --- and a locked cluster of cardinality $m$ couples with coefficient exactly $m$. -/
theorem p21016 : (∀ {p : Nat} [FRC.Pos p] (z : FRC.Shell p) (m : Nat), FRC.Shell.sumRange (fun x => z) m = FRC.Shell.ofNat m * z) ∧ ∀ {p : Nat} [FRC.Pos p] (z w : FRC.Shell p), z * w = (1 : FRC.Shell p) → (z + -w) * (z + -w) = -(((1 : FRC.Shell p) + (1 : FRC.Shell p) + -z + -w) * ((1 : FRC.Shell p) + (1 : FRC.Shell p) + z + w)) :=
  @FRC.Ledger.p21016
set_option linter.defProp false in
/-- 21:C2 (p21017) — Newton's law $F=-Gm_1m_2/r^2$ with $G=1/4\pi\varkappa$ [chart] (register value $G=2S$): the $r^{-2}$ from harmonicity in the three frame freedoms, the product $m_1m_2$ from coherent additivity. -/
def p21017 := @FRC.Ledger.p21017
/-- 21:C5 (p21020) — The magnitude $G=\hbar c/m_P^2$, frame-covariant (a relativity principle for scale); gravity's weakness is cardinality dilution. -/
theorem p21020 : ∀ {p : Nat} [FRC.Pos p] {κ : Nat} {g : FRC.Shell p}, FRC.Shell.Frame p κ g → (g ^ κ) ^ (2 : Nat) = (-1 : FRC.Shell p) ∧ g ^ κ * FRC.Shell.ofNat ((2 : Nat) * κ + (1 : Nat)) * (g ^ κ * FRC.Shell.ofNat ((2 : Nat) * κ + (1 : Nat))) = FRC.Shell.ofNat κ ∧ (2 : FRC.Shell p) * (g ^ κ * FRC.Shell.ofNat ((2 : Nat) * κ + (1 : Nat))) = g ^ κ :=
  @FRC.Ledger.p21020
/-- 21:C6 (p21021) — The conserved dust-tensor source as the Frobenius-symmetric square on the mass shell (cardinality conservation and torsor equivariance). -/
theorem p21021 : ∀ {p : Nat} [FRC.Pos p] (m a b ν : FRC.Shell p), m * (a * a) + -(ν * (m * (b * b))) = m * (a * a + -(ν * (b * b))) :=
  @FRC.Ledger.p21021
/-- 21:C7 (p21022) — Channel unity forces the spatial bias to equal the temporal one, $\gamma=1$, restoring the full light deflection $4Gm/c^2b$. -/
theorem p21022 : ∀ {p : Nat} [FRC.Pos p] {β γ : FRC.Shell p}, ((1 : FRC.Shell p) + (1 : FRC.Shell p)) * γ + -β = (1 : FRC.Shell p) → γ = (1 : FRC.Shell p) → β = (1 : FRC.Shell p) :=
  @FRC.Ledger.p21022
/-- 21:C8 (p21023) — The exponential isotropic metric by multiplicative composition, with $\beta=\gamma=1$: deflection, Shapiro delay, and perihelion at their observed values. -/
theorem p21023 : (∀ {p : Nat} [FRC.Pos p] {β γ : FRC.Shell p}, ((1 : FRC.Shell p) + (1 : FRC.Shell p)) * γ + -β = (1 : FRC.Shell p) → γ = (1 : FRC.Shell p) → β = (1 : FRC.Shell p)) ∧ (6 : Int) * (-4 : Int) / (3 : Int) - (6 : Int) * (-3 : Int) / (2 : Int) = (1 : Int) ∧ (2 : Int) * (2 : Int) - (3 : Int) = (1 : Int) ∧ (3 : Int) + (4 : Int) + (1 : Int) = (8 : Int) ∧ (-4 : Int) - (6 : Int) - (2 : Int) = (-12 : Int) ∧ (8 / 4 : Int) = (2 : Int) ∧ (-12 : Int) * (2 : Int) / (8 : Int) = (-3 : Int) :=
  @FRC.Ledger.p21023
/-- 21:C9 (p21024) — The discrete Fierz--Pauli functional, exactly gauge-invariant and the unique adjacency-local stiffness on the shell (the spin-one case is unique-Maxwell). -/
theorem p21024 : (∀ {p : Nat} [FRC.Pos p] (n : Nat), (0 : Nat) < n → ∀ (f g : Nat → FRC.Shell p), FRC.Shell.sumRange (fun i => FRC.Lattice.cdiff n f i * FRC.Cycle.cyc n g i) n = -FRC.Shell.sumRange (fun i => FRC.Cycle.cyc n f i * FRC.Lattice.cdiff n g i) n) ∧ (∀ {p : Nat} [FRC.Pos p] (n : Nat), (0 : Nat) < n → ∀ (f g : Nat → FRC.Shell p), FRC.Shell.sumRange (fun i => FRC.Lattice.fdiff n f i * FRC.Cycle.cyc n g i) n = -FRC.Shell.sumRange (fun i => FRC.Cycle.cyc n f i * FRC.Lattice.bdiff n g i) n) ∧ ∀ {p : Nat} [FRC.Pos p] (η : Nat → FRC.Shell p) {n : Nat} {w₀ w₁ t : FRC.Shell p}, (1 : Nat) < n → η (0 : Nat) * w₀ = (1 : FRC.Shell p) → η (1 : Nat) * w₁ = (1 : FRC.Shell p) → ((1 : FRC.Shell p) + (1 : FRC.Shell p)) * t = (1 : FRC.Shell p) → ∀ (a₁ a₂ a₃ a₄ : FRC.Shell p), (∀ (k ξ : Nat → FRC.Shell p) (h : Nat → Nat → FRC.Shell p), (∀ (μ ν : Nat), h μ ν = h ν μ) → FRC.Symbol.tensForm η n a₁ a₂ a₃ a₄ k (FRC.Symbol.gauge h k ξ) = FRC.Symbol.tensForm η n a₁ a₂ a₃ a₄ k h) ↔ ∃ c, a₁ = -c ∧ a₂ = ((1 : FRC.Shell p) + (1 : FRC.Shell p)) * c ∧ a₃ = -(((1 : FRC.Shell p) + (1 : FRC.Shell p)) * c) ∧ a₄ = c :=
  @FRC.Ledger.p21024
/-- 21:C11 (p21026) — The nonlinear completion forced: the exact cut-flux law (transfer antisymmetry) plus the winding grading forbid independent static self-sourcing, the clock-comparison cocycle makes the exponential reading unique (exactly the character $\gen^{-\Delta n}$, $e^{-u}$ its observer lift), and Deser's bootstrap does not apply because what gravitates is winding rate. -/
theorem p21026 : (∀ {p : Nat} [FRC.Pos p] {κ : Nat} {g : FRC.Shell p}, FRC.Shell.Frame p κ g → ∀ (n : Nat) (J : Nat → Nat → FRC.Shell p), (∀ (x y : Nat), J x y = -J y x) → ∀ (R : Nat → Bool), FRC.Shell.sumRange (fun x => FRC.Drift.ind R x * FRC.Shell.sumRange (fun y => J x y) n) n = FRC.Shell.sumRange (fun x => FRC.Drift.ind R x * FRC.Shell.sumRange (fun y => ((1 : FRC.Shell p) + -FRC.Drift.ind R y) * J x y) n) n) ∧ ∀ {p : Nat} [FRC.Pos p] (g : FRC.Shell p) (a b : Nat), g ^ (a + b) = g ^ a * g ^ b :=
  @FRC.Ledger.p21026
/-- 21:C13 (p21062) — Area-law entropy $S=c_S'A_f/\ell_P^2$: the $\tfrac14$ the $Q_4$ gauge quotient counted on the shell ($S/A=\kap/\p $ exactly), the Carrier identity $S=(\Omega-1)/4$ at the coherence-horizon shell the same quarter (a consistency, not a closure); the count read as the coordinate area at the operational cut (B7); the identification of the entropy with the channel count (master D15); an exact merger area law $\Delta A=2M_1M_2$ on the count face of the mass; a phase-slip (Hawking-scaling) emission suppressed below one quantum per Hubble time. -/
theorem p21062 : (∀ (κ : Nat), (4 : Nat) * (κ * ((4 : Nat) * κ + (2 : Nat))) + (1 : Nat) = ((4 : Nat) * κ + (1 : Nat)) * ((4 : Nat) * κ + (1 : Nat)) ∧ κ * ((4 : Nat) * κ + (2 : Nat)) * ((4 : Nat) * κ + (1 : Nat)) = κ * (((4 : Nat) * κ + (1 : Nat)) * ((4 : Nat) * κ + (2 : Nat))) ∧ (4 : Nat) * (κ * ((4 : Nat) * κ + (2 : Nat))) * ((4 : Nat) * κ + (1 : Nat)) = ((4 : Nat) * κ + (1 : Nat)) * ((4 : Nat) * κ + (2 : Nat)) * ((4 : Nat) * κ)) ∧ (29407 : Nat) * ((29407 : Nat) + (1 : Nat)) = (27811 : Nat) * ((27811 : Nat) + (1 : Nat)) + (1596 : Nat) * ((1596 : Nat) + (1 : Nat)) + (88772712 : Nat) ∧ (2 : Nat) * ((27811 : Nat) * (1596 : Nat)) = (88772712 : Nat) ∧ (27811 : Nat) + (1596 : Nat) = (29407 : Nat) :=
  @FRC.Ledger.p21062
/-- 21:C15 (p21030) — The radiative sector: the quarter-turn conjugate momentum makes the dynamics a wave equation: two helicity-$\pm2$ gravitons at speed $c$, quadrupole radiation; gauge leaves two polarisations. -/
theorem p21030 : ∀ {p : Nat} [FRC.Pos p] (n : Nat), (0 : Nat) < n → ∀ {g : FRC.Shell p}, g ^ n = (1 : FRC.Shell p) → ∀ (k i : Nat), FRC.Lattice.lap n (FRC.Lattice.chi n g k) i = (g ^ k + g ^ (k * (n - (1 : Nat))) + -((1 : FRC.Shell p) + (1 : FRC.Shell p))) * FRC.Lattice.chi n g k i :=
  @FRC.Ledger.p21030
/-- 21:C16 (p21031) — The order-one constants are determined: $c_S'=\tfrac14$ (the $Q_4$ gauge quotient, counted on an instantiated shell and carried by the Carrier identity), the floor's $2\pi$ the full cycle of the angle--count dictionary (14:B2), its threshold the realisation 32:B3, the recurring constant the solid angle $4\pi$, reducing in the Carrier register to the calibration congruence $(4S)^{2}\equiv1$ (one residue relation). -/
theorem p21031 : (∀ {p : Nat} [FRC.Pos p] {κ : Nat} {g : FRC.Shell p}, FRC.Shell.Frame p κ g → FRC.Shell.ofNat ((4 : Nat) * κ) = (-1 : FRC.Shell p) ∧ FRC.Shell.ofNat ((4 : Nat) * κ) * FRC.Shell.ofNat ((4 : Nat) * κ) = (1 : FRC.Shell p)) ∧ (4 : Nat) * (602140 : Nat) = (2408560 : Nat) ∧ (2408560 : FRC.Shell (2408561 : Nat)) = (-1 : FRC.Shell (2408561 : Nat)) ∧ (2408560 : FRC.Shell (2408561 : Nat)) * (2408560 : FRC.Shell (2408561 : Nat)) = (1 : FRC.Shell (2408561 : Nat)) ∧ (2 : FRC.Shell (2408561 : Nat)) * (1204280 : FRC.Shell (2408561 : Nat)) = (-1 : FRC.Shell (2408561 : Nat)) ∧ (-2 : FRC.Shell (2408561 : Nat)) * (1204280 : FRC.Shell (2408561 : Nat)) = (1 : FRC.Shell (2408561 : Nat)) ∧ (2 : FRC.Shell (2408561 : Nat)) * (2408560 : FRC.Shell (2408561 : Nat)) * (1204280 : FRC.Shell (2408561 : Nat)) = (1 : FRC.Shell (2408561 : Nat)) ∧ (18688 : FRC.Shell (2408561 : Nat)) * (18688 : FRC.Shell (2408561 : Nat)) = (-1 : FRC.Shell (2408561 : Nat)) ∧ (2 : FRC.Shell (2408561 : Nat)) * (9344 : FRC.Shell (2408561 : Nat)) = (18688 : FRC.Shell (2408561 : Nat)) ∧ (9344 : FRC.Shell (2408561 : Nat)) * (9344 : FRC.Shell (2408561 : Nat)) = (602140 : FRC.Shell (2408561 : Nat)) :=
  @FRC.Ledger.p21031
/-- 21:C19 (p21064) — The registration crossover made exact: the killed walk is the noise sector, first passage the masking event, the window attribution the framed-rational tally ratio $g_N/f$, and the orbital response now derived (Theorem~\ref{thm:twoshift} with the registered-inertia identity); it rests on the masking barrier (B9) and the corpus's unified sampling clause (master D10), shared with \citep{quantum}. -/
theorem p21064 : ∀ {p : Nat} [FRC.Pos p] {κ : Nat} {g : FRC.Shell p}, FRC.Shell.Frame p κ g → ∀ {w s η : FRC.Shell p}, s * s = (1 : FRC.Shell p) + -(w * w) → w ≠ (0 : FRC.Shell p) → w * η = (1 : FRC.Shell p) + -s → w * (η * η) + -(((1 : FRC.Shell p) + (1 : FRC.Shell p)) * η) + w = (0 : FRC.Shell p) :=
  @FRC.Ledger.p21064
/-- 21:C20 (p21035) — The two-shift update law: kick (finite Fourier shift by the source character) composed with metaplectic transport gives $\Delta^{2}_{\tau}q=-\nabla u$ with $m$ cancelling --- registered inertia and the equivalence principle inside one derived law. -/
theorem p21035 : (∀ {p : Nat} [FRC.Pos p] (n : Nat), (0 : Nat) < n → ∀ {ζ : FRC.Shell p}, ζ ^ n = (1 : FRC.Shell p) → ∀ (f : Nat → FRC.Shell p) (a k : Nat), FRC.Cycle.dft n ζ (fun x => ζ ^ (a * x) * f x) k = FRC.Cycle.dft n ζ f (k + a)) ∧ ∀ {p : Nat} [FRC.Pos p] (n : Nat), (0 : Nat) < n → ∀ {ζ : FRC.Shell p}, ζ ^ n = (1 : FRC.Shell p) → ∀ (f : Nat → FRC.Shell p) (a k : Nat), a ≤ n → FRC.Cycle.dft n ζ (fun x => FRC.Cycle.cyc n f (x + (n - a))) k = ζ ^ (a * k) * FRC.Cycle.dft n ζ f k :=
  @FRC.Ledger.p21035
/-- 21:C21 (p21036) — The defect chain: relative-cycle defect with exact recurrence; the compression identity (relaxation $=$ unresolved leakage, recurrence retained); the pair-tally current (sine derived, conditional on channel unity); binding bookkeeping decided --- substrate winding sources the field, the defect registered-side, $\eta_{\mathrm{Nordtvedt}}=0$. -/
theorem p21036 : (∀ (L a t : Nat), (0 : Nat) < L → (t * a % L = (0 : Nat) ↔ FRC.Drift.firstReturn L a ∣ t)) ∧ ((420 / 28 : Nat) = (15 : Nat) ∧ (420 / 60 : Nat) = (7 : Nat) ∧ (420 : Nat) % (28 : Nat) = (0 : Nat) ∧ (420 : Nat) % (60 : Nat) = (0 : Nat) ∧ (60 : Nat) % (4 : Nat) = (0 : Nat) ∧ (28 : Nat) % (4 : Nat) = (0 : Nat) ∧ ((15 : Nat) - (7 : Nat)) % (420 : Nat) = (8 : Nat) ∧ FRC.Drift.firstReturn (105 : Nat) (8 : Nat) = (105 : Nat) ∧ FRC.Drift.firstReturn (420 : Nat) (8 : Nat) = (105 : Nat)) ∧ ∀ {p : Nat} [FRC.Pos p] (z w : FRC.Shell p), z * w = (1 : FRC.Shell p) → (z + -w) * (z + -w) = -(((1 : FRC.Shell p) + (1 : FRC.Shell p) + -z + -w) * ((1 : FRC.Shell p) + (1 : FRC.Shell p) + z + w)) :=
  @FRC.Ledger.p21036
/-- 21:C25 (p21040) — The PPN triangle closed by two routes: channel unity gives $\gamma=1$ (C7), the instance cover forces $2\gamma-\beta=1$ (A9), jointly $\beta=1$ --- Proposition~\ref{prop:ppn} reached independently, the deviation $\tfrac23(2\gamma-\beta-1)$ its falsifier. -/
theorem p21040 : (∀ {p : Nat} [FRC.Pos p] {β γ : FRC.Shell p}, ((1 : FRC.Shell p) + (1 : FRC.Shell p)) * γ + -β = (1 : FRC.Shell p) → γ = (1 : FRC.Shell p) → β = (1 : FRC.Shell p)) ∧ ∀ {p : Nat} [FRC.Pos p] {β γ : FRC.Shell p}, ((1 : FRC.Shell p) + (1 : FRC.Shell p)) * γ + -β = (1 : FRC.Shell p) → ((1 : FRC.Shell p) + (1 : FRC.Shell p)) * γ + -β + (-1 : FRC.Shell p) = (0 : FRC.Shell p) :=
  @FRC.Ledger.p21040
/-- 21:P6 (p21055) — The 2PN periastron excess $\delta\dot\omega/\dot\omega\approx1.5\times10^{-6}$ for PSR~J0737$-$3039, today degenerate with the mass refit; decisive either way once an independent observable fixes $M_{\mathrm{tot}}$ at $10^{-6}$. Independent of the coherent-fraction falsifier of \citep{quantum}; the ledger carries both. -/
theorem p21055 : (6 : Int) * (-4 : Int) / (3 : Int) - (6 : Int) * (-3 : Int) / (2 : Int) = (1 : Int) ∧ (2 : Int) * (2 : Int) - (3 : Int) = (1 : Int) ∧ (3 : Int) + (4 : Int) + (1 : Int) = (8 : Int) ∧ (-4 : Int) - (6 : Int) - (2 : Int) = (-12 : Int) ∧ (8 / 4 : Int) = (2 : Int) ∧ (-12 : Int) * (2 : Int) / (8 : Int) = (-3 : Int) :=
  @FRC.Ledger.p21055
-- end ledger predicates

end FRC.Gravity
