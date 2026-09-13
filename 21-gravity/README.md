# Numeric validation suite — *Gravitation as Phase Synchronisation over Finite Relational Substrate*

Repository: <https://github.com/gamayos/frc-numerics/tree/main/21-gravity>

Independent numerical verification of every quantitative claim of the manuscript
(`../main.tex`). Each script is self-contained, prints the computed values against
the manuscript's targets, and ends with a single `PASS`/`FAIL` line. The checks are
framed-rational where it counts: the exact objects are rational or quadratic-extension
algebraic, and any continuum reading (a transcendental limit, a comparison to measured
data) is tagged `[approx]` or `[data]` and carries no exact claim.

## Requirements

Python 3.10+, `numpy`, `sympy` (which provides `mpmath`). The figure scripts also need
`matplotlib`. No other dependencies.

## Usage

```
python3 run_all.py          # full suite (12 checks) with PASS/FAIL summary
python3 validate_<x>.py      # any single check
python3 make_all_figures.py  # regenerate every publication figure
```

Total runtime ≈ 1–2 minutes; `validate_fluxnoise.py` (a stochastic simulation)
dominates. The twelve checks run in the order listed below.

## Checks and the claims they validate

| Script | Manuscript claim | What is checked |
|---|---|---|
| `validate_newton.py` | Lemma (stationary bias field); Theorem (Newtonian limit); Lemma (coherent additivity) | Exact lattice Green's function of Z³ via the Montroll–Bessel representation: 4πr·G(r) → 1 with the stated O(r⁻²) correction; potential power law r⁻¹ (hence force r⁻²); locked ensemble couples as m, unlocked as √m. |
| `validate_ppn.py` | Prop. (full light deflection); Prop. (classical tests); Prop. (exact static profile, series) | Symbolic: Fermat deflection 4Gm/c²b in the index n = 1+2u; PPN β = γ = 1 from the exponential metric expansion; perihelion factor (2+2γ−β)/3 = 1; static-profile series Gm/r·(1+(Gm/r²)²/30). |
| `validate_strongfield.py` | Prop. (exact static profile); Prop. (horizonless, operationally black); Prop. (photon sphere and shadow); Prop. (innermost stable orbit and accretion efficiency); area law; echo suppression | Slip-core boundary r\* = √(Gm); exact potential at the photon sphere; numerical extremum of b(r) = r·e^{2u}: r_ph = 2Gm, b_c = 2e·Gm; shadow deviation +4.6 %, ringdown −4.4 %; ISCO at the isotropic radius r_ISCO = (3+√5)·Gm (marginal stability W′ = W″ = 0), accretion efficiency 1−E = 5.48 % vs Schwarzschild 5.72 %, ISCO orbital frequency Gm·Ω/c³ = 0.0633 (0.931× the Schwarzschild 1/6√6); r_f = r_s/ln Ω, S/S_BH = ln⁻²Ω; echo delay factor Ω/ln²Ω (no observable echoes); Sgr A\*/M87\* angular diameters (53.3 → 55.7 µas; 39.7 → 41.5 µas). |
| `validate_fp_gauge.py` | Eq. (discrete Fierz–Pauli functional); exact discrete gauge invariance; Prop. (the (3+1) tensor) | The four-term FP form on a periodic **(3+1)** lattice with integer random fields: gauge invariance under h → h + Δξ (symmetrised) holds as an **exact integer identity** for **central** differences and **fails** for one-sided differences, confirming that the anti-self-adjointness Δᵀ = −Δ carries the proof. By Schwartz–Zippel an exact zero on random integer fields certifies the algebraic identity. Same four-frame signature as the uniqueness script. |
| `validate_branch.py` | Theorem (nonlinear completion); Remark (where GR sits) | The Ward identity in the full nonlinear sine model: flux through every closed surface equals the enclosed demand to solver precision, for one and two sources at strong gradients, and the nonlinear deviation of the potential scales as m³ (no m² self-sourcing term). Symbolic: isotropic Schwarzschild is the exponential reading of the self-sourced ψ = 2 artanh(U/2) (exact identity), ψ is non-harmonic, and the Schwarzschild reading violates the composition law R(a+b)=R(a)R(b) that the exponential uniquely satisfies. |
| `validate_fluxnoise.py` | Lemma (flux conservation under noise) | A driven, pinned Kuramoto chain in the statistically stationary regime: the time-averaged transport through every link equals the source demand, with and without drive noise. (The lemma's stationarity hypothesis is essential: overdriving the chain produces a running state, visible by raising `b` or the noise.) |
| `validate_rar.py` | Prop. (floor acceleration); Cor. (turnaround) | a₀ = cH₀/2π for H₀ ∈ {67.4, 70, 73} against the SPARC fit 1.20 ± 0.24 × 10⁻¹⁰ m s⁻² (all within one systematic sigma); Local-Group turnaround radius (Gm/H²)^{1/3} ≈ 1.6 Mpc against the observed ~1 Mpc zero-velocity surface. |
| `validate_deepregime.py` | Prop. (registration crossover, D4) | The deep-MOND crossover g_obs = g_b / f as first-passage registration. The floor a₀ = cH₀/2π is the link-decorrelation rate; a sub-floor gradient gives x = g_b/a₀ < 1 cycles per Hubble time and Born amplitude √x; registration is the first passage of the killed meridian walk to that barrier, with resolved fraction f = 1 − η^a and η the in-(0,1) root of the **rational** quadratic w·η² − 2η + w = 0. Checks the deep-MOND limit (g_obs → √(g_b·a₀), BTFR), the Newtonian limit (f → 1), and the η root exactly; the e^{−√x} reading is tagged `[approx]`. |
| `validate_radiative.py` | Prop. (wave equation); Prop. (graviton); Rem. (radiative Noether) — sector D5 | Reversibility of the drive forces a conjugate momentum (the quarter-turn dual of u), making the dynamics Hamiltonian: χü = κΔu, the wave equation. Channel unity (κ and χ are one capacity) gives c_g² = κ/χ = c²; the Fierz–Pauli field yields the spin-2 theory with two transverse-traceless polarisations, helicity ±2. Checks the dispersion relation, the long-wave speed = c, the TT rank = 2, the helicity, and the absence of mode doubling (Nyquist). |
| `validate_orderone.py` | Prop. (area law c_S′ = 1/4); Prop. (floor 2π); radiation constant — sector D6 | The order-one normalisations are determined, not free: c_S′ = 1/4 (Bekenstein–Hawking) from the de Sitter closure — the same area law on the cosmological horizon (radius √Ω) reproduces the de Sitter entropy that defines the cardinality; the 2π of a₀ = cH₀/2π as the angular period of one phase turn (the same 2π as the Hawking temperature); the radiation constant as the spin-2 quadrupole factor fixed by D5; the recurring geometric constant 4π. Exact rational arithmetic (`fractions`); a₀ vs data tagged `[approx]`. |
| `validate_rotating.py` | Prop. (frame-dragging); Rem. (no event horizon) — sector D7 | The rotating solution as the quarter-turn dual of the static field. The momentum flux (the off-diagonal of the dust tensor) sources a gravitomagnetic potential — the same Q₄ that gives the conjugate momentum (D5) and the registration (D4). Checks the Lense–Thirring frame-dragging ω = 2GJ/c²r³, the gravitomagnetic dipole, horizonless-ness (only the redshift floor), and the O(a) shadow spin shift (structure only; the exact coefficient and the ergosphere are the rapid-rotation residue). |
| `validate_primordial.py` | Prop. (primordial spectrum, D8) | The spectrum is structural. Time is scale-dilation, so the fluctuation spectrum is the dilation invariant: the unique scale-free Harrison–Zel'dovich spectrum, n_s = 1, no inflaton. Checks that P ∝ k^n is scale-invariant **iff** n = −3 (n_s = 1) uniquely; that the observed red tilt n_s − 1 = −0.035 (the chart misalignment, the same object as the a₀(z) running, D9) has the predicted sign; and the wrapped-chart truncation of correlations beyond ~60° (low quadrupole, small S_{1/2}). The fixed point is exact; observed numbers are tagged `[data]`/`[approx]`. |

## Figures

The publication figures are regenerated from the same suite (`matplotlib` required):

| Script | Figure |
|---|---|
| `make_all_figures.py` | Regenerates every figure below. |
| `make_fig_phase_a.py` | Phase emergence and subject-relative observation (worked F₁₅₇ example). |
| `make_fig_rar.py` | The radial acceleration relation and the a₀ registration crossover. |
| `make_fig_anatomy.py` | The radial anatomy of the static object: zones, slip core, operational horizon, redshift. |
| `make_fig_shadow.py` | Shadow and ringdown against general relativity, with the EHT measurements. |
| `make_fig_sync.py` | The synchronisation mechanism: forced frame drift and its relaxation. |
| `make_fig_sync_variants.py` | Alternative synchronisation-figure variants (not imported into the manuscript). |

## Supplementary symbolic check

`fierz_pauli_uniqueness.py` proves, by the symbol/transversality method, that the
discrete Fierz–Pauli functional is the **unique** adjacency-local gauge functional on
the shell — the symmetric rank-2 analogue of the Maxwell uniqueness theorem. It runs in
the same full (3+1) signature as `validate_fp_gauge.py`, so the gauge-invariance and
uniqueness checks are dimensionally aligned with the displayed theory (the 2×2 mass shell
to (3+1) tensor map, Prop. spacetime). It is a longer symbolic run and is kept outside
`run_all.py`; run it directly.

## What is *not* validated here

The suite validates derived numbers, not inputs. The ledger surface is two definitions
(mass as winding rate, distance as decoherence), one frame normalisation (unit
capacity), one counting lemma (channel unity), and a single physical premise (composite
matter is internally phase-locked), all on top of the imported FRC framework; these are
imported or bridged, not checked here.

Every constructive item is derived and checked: the nonlinear completion (the Gauss-law
Ward identity and the composition-law characterisation, `validate_branch.py`), the
deep-regime crossover (D4), the radiative sector (D5), the order-one constants (D6), the
rotating solution (D7), and the primordial spectrum (D8). Two bounded residues sit inside
derived sectors and are not load-bearing: the fully nonlinear graviton self-interaction
(controlled by the no-self-sourcing Ward identity) and the exact rapid-rotation metric.
The single residue no bounded observer can close is the cross-scale running of a₀ (D9):
Ω-hard through the factorisation of Ω−1, decided by the totality. Its absence from the
suite is by construction, not a gap.

## Control note

`validate_fp_gauge.py` retains a deliberately failing configuration as a control. With
one-sided differences the lattice adjoint is not the negative of the difference operator
and exact invariance fails; with central differences — the functional the manuscript
exhibits — the anti-self-adjointness Δᵀ = −Δ holds and invariance is exact to machine
precision. The contrast is what pins anti-self-adjointness as the property that carries
the continuum proof.
