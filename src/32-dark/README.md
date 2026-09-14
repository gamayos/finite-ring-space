# 32-dark validation package

Validation package of *The Dark Sector over Finite Relational Substrate* (Akhtman, Geifman & Voether, 2026), `32-dark`
of the FRC corpus. The paper's twelve validation scripts and its figure script as written, run through one registry
(`darkcommon.py`): a family check is one script (`dark.<stem>`), its micro-checks the script's own verdict lines (four of
the thirteen print one — `flux_exact`, `born_exact`, `deep_regime_fp`, `rar_scatter`; `rar_shape` prints one per check)
together with the registry's predicates, which decide the stated values explicitly where a script prints without
asserting: the exact Gauss law and the amplitude identity recomputed, the first-passage reduction with rel.err/s → 1/6,
the slopes 1.03/1.11 and the exact slope 1, the 0.051 discriminant at x = 5.2 and the two pinning checks of B8, the RAR
and BTFR slopes with the 162 km/s flat speed, the SPARC scatter 0.038 dex and the bound δα ≲ 3.5°, the cluster law's
N_eff, the prediction numerals. An exception, a nonzero exit or a failed predicate fails the family. `rar_shape.py`, the
named test of row B8 that the paper's Appendix A owed "once the binned data file is on the tree", is delivered here
(`data/RAR.mrt`). Driven by `32-dark-main.ipynb` (Google Colab, *Runtime → Run all*, ≈ 30 s) or by `run_all.py`.
Python 3.10+, numpy, mpmath, matplotlib; scipy for the exponential-disk curve. The scripts write their figures and
`deep.json` into `out/`, the paper's two figures into `figures/` (both ignored by git); the registry gives every saved
figure a PNG sibling and the notebook shows the PNGs inline below each family's output (six figures).

Every family names the row(s) of the paper's predicate ledger it witnesses (the paper's Appendix "Predicate ledger",
49 rows in blocks A, B, C, X, P, V, Z, O, cited as `32:XN`; public copy `docs/32-dark/32-dark-ledger.html`); the ledger's
source column cites the family ids in return. Master-ledger rows of the corpus sourced from this paper: `00:L1` (the
floor a₀ = cH₀/2π and the RAR's barrier identification), `00:L7` (the running floor), `00:Z7` (the running's
normalisation), `00:D3` (distance is decoherence), `00:N1` (the exclusion predictions), `00:N2` (parameter-freeness).

Three kinds, recorded per family in `results.json`: **EXACT** — exact rationals, Z[i] or 60-digit identities, no
tolerance in the verdict; **SIM** — a seeded stochastic simulation (the noisy link, the killed walk), verdict by stated
tolerance; **CHART** — a continuum reading or a comparison with data (the interpolation, the RAR/BTFR, the SPARC scatter,
the predictions, the cluster illustration), tagged [approx] in the paper, verdict by stated tolerance.

[![Open In Colab](https://colab.research.google.com/assets/colab-badge.svg)](https://colab.research.google.com/github/gamayos/finite-ring-space/blob/main/src/32-dark/32-dark-main.ipynb)

## In-tree

| family | script | kind | claims backed (ledger rows) |
|---|---|---|---|
| `dark.flux_exact` | `flux_exact.py` | EXACT | the discrete Gauss law of the synchronisation flux in exact rationals on the 5³ box: unit source → unit flux through both enclosing surfaces, a source-free noise field → zero, the superposition → one — Newton as the high-acceleration reading (32:C1, X1) |
| `dark.born_exact` | `born_exact.py` | EXACT | amplitude = √count in Z[i]: \|Σ\|² = n² coherent, ⟨\|Σ\|²⟩ = n over all sign patterns, n ≤ 10 — the cross-term cancellation forcing the deep-regime square root (32:C3, C7) |
| `dark.firstpassage_finite` | `firstpassage_finite.py` | EXACT | the finite-cycle first-passage law at 60 digits: f(e^(−s)) = e^(−arccosh e^s); arccosh(e^s) = √(2s)(1 + s/6 + …), rel.err/s → 1/6; the wrap correction of the killed walk on Z_N (32:B8, C7) |
| `dark.meridian_walk` | `meridian_walk.py` | SIM | the meridian killed walk: the exact first-passage quadratic; the seeded escape probability against e^(−a√(2s)); the resolved fraction 1 − e^(−√x) with deep slope 1/2 (32:B8, C6, C7) |
| `dark.deep_regime` | `deep_regime.py` | SIM | the noisy Kuramoto (Adler) link simulated: deep slopes 1.03 (D = 0.3) and 1.11 (D = 0.6), the boost constant to rising — registration, not force modification (32:C4) |
| `dark.deep_regime_fp` | `deep_regime_fp.py` | CHART | the stationary Fokker–Planck solution of the same link: the small-tilt log-slope exactly 1 at both D (within 2 × 10⁻³) (32:C4) |
| `dark.interpolation` | `interpolation.py` | CHART | the interpolation from the rotation angle: deep slope 1/2, Newtonian slope 1; the 0.051 discriminant against the simple rational form at x = 5.2; the two pinning checks of B8; the chart angle (32:B8, C6, X4) |
| `dark.rar_shape` | `rar_shape.py` | CHART | the named test of B8 against the binned SPARC relation: the exponential form's free a₀ within 10 % of the RAR fit and below the rational form in χ²; the band 2 < x < 10 within the bin scatter; the floor 13 % below the fit [approx] (32:B8, C2, C6) |
| `dark.deep_mond` | `deep_mond.py` | CHART | the two-chart Gauss law: a₀ = cH₀/2π = 1.042 × 10⁻¹⁰; RAR slope 0.514, BTFR slope 0.250, v_flat(5 × 10¹⁰ M⊙) = 162 km/s; the exponential-disk curve flattening [approx] (32:C2, C4, C5, X2, X3) |
| `dark.rar_scatter` | `rar_scatter.py` | CHART | the SPARC residual test at fixed a₀: intrinsic 0.038 dex, 0.04 at the knee rising to 0.13 at x ≈ 0.02; δα ≲ 3.5°; ρ = −0.01 over 116 disks; the 0.14-dex amplitude-sum boost; ν(0.1) = 3.7 [approx, data] (32:C8, P2, X5, O1, O2) |
| `dark.cluster_coherent` | `cluster_coherent.py` | CHART | the coherence-matrix amplitude law N_eff = (Σ√g)²/Σg: N for equal components, 2.67 for 4:1:1; the core boost √6 decaying to 1 by ~Mpc [illustrative] (32:C10, X7, X8, O1) |
| `dark.predictions` | `predictions.py` | CHART | the predictions computed: v_flat ∝ E(z)^(1/4) (+7, +15, +31 % at z = 0.5, 1, 2); the scatter law 0.27 dex at x = 0.01, σ_v/v = 0.1; the wide-binary velocity enhancement 12–16 % at 10–40 kAU with g_ext = 1.8a₀; the coherence offset −0.05 to −0.15 dex [approx] (32:P1–P4) |
| `dark.make_figures` | `make_figures.py` | CHART | the paper's two figures regenerated into `figures/` (32:V2) |
| — | `darkcommon.py` | — | the registry: the script runner, `PRED` (the predicates per family), `LEDGER` (family → rows), `LABELS`, `KIND`, `results.json` |

Run: `python3 run_all.py`. Any script also runs alone as before (`python3 flux_exact.py`), printing its own report.
Rebuild the notebook: `python3 make_notebook.py`.

## Provenance

The scripts are the paper's `validation/` suite (June–September 2026), unchanged; `rar_shape.py` (September 2026) is
new to both. The public copy had carried June versions of `cluster_coherent.py`, `deep_mond.py`, `interpolation.py`,
`make_figures.py`, `predictions.py` and lacked `deep_regime_fp.py`, `rar_scatter.py` and `data/`; its README and the
five old scripts are in `_to_delete/32-dark-superseded/` with the stale figure and json outputs. Registry-side findings
recorded here, not repaired: `rar_scatter`'s check "knee bins (0.1 < x < 3) intrinsic within 0.03–0.05 dex" tests
0.02–0.06 and the bin 0.1 < x < 0.3 gives 0.028 (the registry pins the paper's 0.04 to the bins 0.3 < x < 3, which give
0.043 and 0.046); `cluster_coherent` rebinds its `Neff` function to a float in its second part (the registry recomputes
the law); the wide-binary prediction is stated in the paper as a velocity enhancement of 10–30 % while the script
prints the acceleration ratio ν = 1.24–1.35 (the registry checks √ν − 1 = 12–16 %).

## Predicate ledger

Rows A1–A7 imports; B1–B8 realisations; C1–C11 derived (C4, C6, C11 composite T|R; C10 composite D|T); X1–X11 the
explanation register; P1–P6 the predictions (P1, P2, P3, P4, P6 formerly D1, D4, D7, D8, D3; P5, the coherence-state
cluster gas, from the body's list); V1–V3 the verification; Z1 the Ω-hard residue, formerly D6; O1–O2 the conjectures,
formerly Y1–Y2. Family → rows: `darkcommon.LEDGER`.
