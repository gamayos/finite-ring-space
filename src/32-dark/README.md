# Validation suite — *The Dark Sector over Finite Substrate*

**Repository:** <https://github.com/gamayos/frc-numerics/tree/main/32-dark>

This folder holds the computational verification for the paper *The Dark Sector over a Finite
Substrate* (`../main.tex`). Every quantitative and algebraic claim in the paper is checked by one of
the scripts below, in **exact arithmetic** wherever the claim is exact (integer, finite-field,
cyclotomic, or high-precision), and against the lattice Green's function or standard astrophysical
constants where the claim is a continuum reading. The scripts are standalone, deterministic, and print
a human-readable verdict; none takes input, and only `make_figures.py` writes files (the two figure
PDFs).

The map below is the executable form of the paper's reproducibility appendix (Appendix A,
`\ref{app:methods}`).

## What is exact and what is a continuum confrontation

The construction's discipline (Appendix A, and the scale-periodicity audit in
`../reports/scale-periodicity/`) is that **every exact claim lives in finite-field, integer, or
cyclotomic arithmetic**, and any continuum reading is a *labelled, profinitely controlled*
approximation. The suite is split accordingly:

- **Exact cores** — the discrete Gauss law (`flux_exact`), the amplitude identity (`born_exact`), the
  meridian first-passage discriminant and its finite-cycle transform (`meridian_walk`,
  `firstpassage_finite`). No floating point where an identity is claimed.
- **Labelled continuum confrontations** — the deep-regime law, the radial acceleration relation, the
  rotation curve, the scatter, and the predictions (`deep_mond`, `interpolation`, `predictions`).
  These compare the substrate readings to data or to the McGaugh fit, and are reported as such.

The single residue the construction leaves to the totality (the cross-scale running of `a0`) is
**Ω-hard** and is *not* computed here; its framed-rational certificate is in
`../reports/omega-hard-certificate/`.

## Requirements

- Python 3.10+
- `numpy`, `scipy`, `matplotlib`, `mpmath` (only some scripts need each — see the table)
- `fractions` is from the standard library; no other dependencies, no network, no data files

```bash
pip install numpy scipy matplotlib mpmath
```

## Running

Each script is run directly and prints its result:

```bash
python3 firstpassage_finite.py
```

To run the whole suite:

```bash
for f in *.py; do echo "=== $f ==="; python3 "$f"; done
```

All scripts exit 0 and complete in a few seconds, except `meridian_walk.py` and `cluster_coherent.py`
(a few seconds of random-walk simulation) and `firstpassage_finite.py` (60-digit `mpmath`).

## Script → claim map

The "paper result" column refers to the labelled propositions, theorems, equations, and figures in
`../main.tex`.

| script | paper result | what it verifies | arithmetic | deps |
|---|---|---|---|---|
| `flux_exact.py` | **Prop. 1** (Newtonian limit) | the discrete Gauss law of the synchronisation flux on a `5³` box with Dirichlet boundary: a unit point source gives unit flux through every enclosing surface, a source-free field gives zero, and their superposition gives unit flux — Newton's law as the high-acceleration reading | exact rationals | `fractions` |
| `deep_regime.py` | **§2**, Construction 1 (illustrative) | the noisy-Kuramoto (Adler) link `dφ=(T−sinφ)dt+√(2D)dW`: the mean dynamics is Newtonian-shaped; the framed-rational reading is a killed random walk on the phase cycle `C_{p−1}` | stochastic, labelled | `numpy`, `matplotlib` |
| `born_exact.py` | **Prop. 2** (amplitude = √count) | in the quarter-turn core `ℤ[i]`: a coherent stack of `n` aligned phasors has amplitude `n`; an incoherent ensemble has RMS amplitude `√n` by cross-term cancellation `𝔼\|Σe^{iθ}\|²=n` | exact `ℤ[i]` | `fractions` |
| `meridian_walk.py` | **Prop. 3** (first-passage) | the meridian phase performs a killed walk; non-registration is first passage across the Born-amplitude barrier; the single-step factor carries `√(1−z²)`, the `a`-level escape is `f(z)^a → e^{−a√(2s)}`, collapsing onto `e^{−√x}` | exact roots + simulation | `numpy`, `matplotlib`, `fractions` |
| `firstpassage_finite.py` | **Prop. 3** (finite cycle), **eq. norm** | the exact single-step identity `f(e^{−s})=e^{−arccosh(eˢ)}`; the controlled reduction `arccosh(eˢ)=√(2s)(1+s/6+s²/120+…)` with **series error `O(s)`** and **lattice (integer-barrier) error `O(√s)`**; the finite-cycle wrap correction `O(e^{−(Ω−1−a)arccosh(eˢ)})` | exact, `mpmath` 60 dp | `mpmath` |
| `interpolation.py` | **Thm. 1**, **eq. interp**, **§4** | the RAR shape assembled from the FrFT angle, the Born amplitude `√x`, the horizon detection `f=1−e^{−A}`, and flux conservation, equal to the McGaugh fit to machine precision; deep slope `→½`, Newtonian `→1`; the chart angle `α(x)` with `sin²α=e^{−√x}` | float, labelled | `numpy`, `matplotlib` |
| `deep_mond.py` | **§3** (geometric mean, RAR, BTFR) | the two-chart Gauss law: position chart `g_eff=g_bar` (Newtonian), spectral chart `g_eff=√(g_bar a0)` (deep); the RAR, the baryonic Tully–Fisher slope `0.25`, and the exponential-disk rotation curve | float, labelled | `numpy`, `scipy` |
| `cluster_coherent.py` | **§6.2**, **eq. cohsum/neff**, ledger **D5** | the coherence-matrix amplitude law `g_amp²/a0=Σg_i+2Σ√(g_ig_j)Re C_ij`; `N_eff=(Σ√g_i)²/Σg_i`; the Bullet selection (`C→0`) and the core addition (`C→1`) in one law; the factor-two core closure as a **falsifiable conjecture**, not a theorem | exact + illustrative | `numpy` |
| `predictions.py` | **§7** (P1–P4) | the further falsifiable predictions: the `a0(z)=cH(z)/2π` knee and BTFR evolution `v_flat∝E(z)^{1/4}`; the two-variable scatter law `σ(x,σ_v/v)`; the wide-binary deep-regime enhancement with the vector Galactic EFE; the pressure-supported coherence offset `√w` | float, labelled | `numpy` |
| `make_figures.py` | **Figs. 1–2** | regenerates `../figures/fig_rar.pdf` (RAR with the rational-alternative knee + exponential-disk rotation curve) and `../figures/fig_mechanism.pdf` (the meridian first-passage collapse + the chart angle) | float (plots) | `numpy`, `scipy`, `matplotlib` |

## Representative expected output

- `flux_exact.py` → "unit source: flux = 1 through every surface; source-free: 0; superposition: 1" (exact).
- `born_exact.py` → coherent amplitude `n`, incoherent RMS amplitude `√n` (cross terms cancel).
- `firstpassage_finite.py` → `f(e^{−s}) = e^{−arccosh(eˢ)}` to `60` digits; `rel.err/s → 1/6`; substrate `s∼Ω^{−1/2}` ⇒ reduction exact to `~10^{−62}`; wrap correction `~e^{−(N−a)arccosh}`.
- `interpolation.py` → "derived interpolation == McGaugh RAR fit: True"; deep slope `→0.5`, Newtonian `→1.0`.
- `deep_mond.py` → BTFR slope `0.25`; disk baryonic peak vs flat registered speed.
- `cluster_coherent.py` → `N_eff=(Σ√g)²/Σg` (equal components `→N`, dominant BCG `→` suppressed); the residual a *falsifiable conjecture*, not a theorem.
- `predictions.py` → `v_flat(z)/v_0 = E(z)^{1/4}` (`+15%` at `z=1`); deep-regime scatter `~0.27` dex; wide-binary `ν` with EFE `~1.1–1.3`.

## Conventions and notes

- **Exact where exact.** Claims marked *exact* in the paper are computed in integer, finite-field
  (`𝔽_p`), cyclotomic (`ℚ(ζ_M)`, `ℤ[i]`), or arbitrary-precision (`mpmath`) arithmetic and verified as
  identities, never by sampling.
- **Labelled continuum readings.** The RAR, the BTFR, the rotation curve, the scatter, and the
  predictions are degenerate-idealisation readings; these use standard constants
  (`a0=cH0/2π`, `H0=70`) and are reported as confrontations, not exact claims.
- **Determinism.** The two simulations (`meridian_walk`, `cluster_coherent`) use fixed seeds; results
  are reproducible. No exact claim depends on a random step.
- **Reduce-and-resolve, or reduce-and-prove-Ω-hard.** Every residue is either resolved by a finite
  identity here (e.g. the cluster residual via the coherence matrix, `cluster_coherent.py`) or proved
  Ω-hard in `../reports/omega-hard-certificate/` (the single cross-scale running). There is no third
  category; "too small" or "missing mass" readings are continuum imports and are not used.
- **Companion reports.** The scatter and external-field figures, the Bullet-cluster convergence map,
  and the scale-periodicity audit live under `../reports/` (`scatter-efe/`, `cluster-lensing/`,
  `scale-periodicity/`, `omega-hard-certificate/`).
