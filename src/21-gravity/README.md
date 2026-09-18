# 21-gravity validation package

Validation package of *Gravitation as Phase Synchronisation over Finite Holographic Substrate* (Akhtman & Voether,
2026), `21-grav` of the FRC corpus. The paper's twenty-one validation scripts as written, run through one registry
(`gravcommon.py`): a family check is one script's verdict (`grav.<stem>`), its micro-checks the script's labelled
checks and every PASS/FAIL line it prints; an exception or a nonzero exit fails the family. Driven by
`21-gravity-main.ipynb` (Google Colab, *Runtime → Run all*, ≈ 1–2 min) or by `run_all.py`. Python 3.10+, numpy,
sympy (mpmath); matplotlib for the figure scripts.

Every family names the row(s) of the paper's predicate ledger it witnesses (the paper's Section "Status", subsection
"Predicate ledger", 59 rows in blocks A, B, C, X, P, V, Z, cited as `21:XN`; public copy
`docs/21-gravity/21-gravity-ledger.html`); the ledger's source column cites the family ids in return. Master-ledger
rows of the corpus reached through the paper rows: `00:A9`, `00:D1`, `00:D3`, `00:D5`, `00:B7`, `00:E1`, `00:D15`, `00:E3`–`00:E7`,
`00:E10`, `00:L1`, `00:L7`, `00:L8`, `00:T1`, `00:T4`, `00:T5`, `00:Z7`.

Three kinds, recorded per family in `results.json`: **EXACT** — decidable identities over finite fields, cyclotomic
extensions, exact rationals, or symbolic identities, no tolerance in the verdict; **CHART** — a continuum reading (a
limit, a series coefficient, a numerical extremum) or a comparison with measured data, tagged [approx]/[data] in the
script, verdict by stated tolerance; **SIM** — a seeded stochastic simulation (the Kuramoto chain), verdict by stated
tolerance on time averages.

[![Open In Colab](https://colab.research.google.com/assets/colab-badge.svg)](https://colab.research.google.com/github/gamayos/finite-ring-space/blob/main/src/21-gravity/21-gravity-main.ipynb)

## In-tree

| family | script | kind | claims backed (ledger rows) |
|---|---|---|---|
| `grav.newton` | `validate_newton.py` | CHART | the lattice Green's function 4πr·G → 1 with the O(r⁻²) correction, the r⁻¹ potential, locked m vs incoherent √m; spanning-tree admissibility det L_red = τ(C_n) = n (21:C1, C2) |
| `grav.ppn` | `validate_ppn.py` | EXACT | Fermat deflection 4Gm/c²b, β = γ = 1, the perihelion factor, the static-profile series (21:C7, C8, C12) |
| `grav.strongfield` | `validate_strongfield.py` | CHART | slip core r* = √(Gm), photon sphere and shadow (+4.6 %, ringdown −4.4 %), ISCO (3+√5)Gm with efficiency 5.48 % and Gm·Ω/c³ = 0.0633, r_f = r_s/ln Ω, S/S_BH = ln⁻²Ω, echo delay Ω/ln²Ω, Sgr A*/M87* diameters (21:C12, C13, P1, P7) |
| `grav.fp_gauge` | `validate_fp_gauge.py` | EXACT | discrete Fierz–Pauli gauge invariance as an exact integer identity for central differences, failing for one-sided (the control) (21:C9) |
| `grav.fierz_pauli` | `fierz_pauli_uniqueness.py` | EXACT | uniqueness of the adjacency-local gauge functional on the shell, (3+1) signature (21:C9) |
| `grav.branch` | `validate_branch.py` | CHART | the cut-flux law of the full sine model, the m³ scaling (no self-sourcing); Schwarzschild as the exponential reading of ψ = 2 artanh(U/2), ψ non-harmonic, the composition law (21:C11) |
| `grav.fluxnoise` | `validate_fluxnoise.py` | SIM | flux conservation under drive noise on a driven, pinned Kuramoto chain (21:C19) |
| `grav.rar` | `validate_rar.py` | CHART | a₀ = cH₀/2π against SPARC for three H₀; the Local-Group turnaround radius (21:C4, P3) |
| `grav.deepregime` | `validate_deepregime.py` | EXACT | the registration crossover: the η root of wη² − 2η + w = 0 exact, f = 1 − η^a, the deep-MOND and Newtonian limits (21:C19, P4) |
| `grav.deepregime_orbit` | `validate_deepregime_orbit.py` | EXACT | the Chebyshev two-boundary weight, the registered-inertia identity, the event-based killed-registration orbit (21:C19, C20) |
| `grav.radiative` | `validate_radiative.py` | EXACT | the wave equation, c_g = c, TT rank 2, helicity ±2, no mode doubling; the even symbol on the continuum form and on C₁₃ (21:C15) |
| `grav.orderone` | `validate_orderone.py` | EXACT | c_S′ = 1/4 from the de Sitter closure, the 2π of a₀, the radiation constant, the 4π; the Carrier-register residues on Ω = 2 408 561 (21:C5, C13, C16) |
| `grav.rotating` | `validate_rotating.py` | CHART | Lense–Thirring frame-dragging, the gravitomagnetic dipole, horizonless-ness, the O(a) shadow shift (21:C10, C17) |
| `grav.primordial` | `validate_primordial.py` | EXACT | scale invariance iff n_s = 1, the sign of the red tilt, the wrapped-chart truncation, the O2 probe K²λ₁ → π² (21:C18, X6, P8) |
| `grav.inertia` | `validate_inertia.py` | EXACT | the two-shift law: the finite Fourier shift theorem, the Ehrenfest parabola, the equivalence principle bitwise (21:C20) |
| `grav.defect` | `validate_defect.py` | EXACT | the projection defect on dev shells: cycle-quotient closure, the wrap count, K_S contractive vs U_C recurrent, the sine mode as the unique minimal odd harmonic (21:C21, C22) |
| `grav.counting` | `validate_counting.py` | EXACT | the Christoffel registration pattern, the censored geometric identity, the Ω = 641 readout instance, the Kesten control, the per-stratum split in Z[√2] and mod 641 (21:C7, C21) |
| `grav.binding` | `validate_binding.py` | EXACT | binding bookkeeping on Z_N³: superposition exact, far-field flux m₁ + m₂ exactly, bilinear interaction energy, the registered-clock defect m(1 − u), η_Nordtvedt = 0 (21:C21, C23) |
| `grav.1pn_eih` | `validate_1pn_eih.py` | EXACT | the 1PN equivalence lemma: A to O(U²), B to O(U) identical to GR-isotropic on the superposed potential (21:C23) |
| `grav.2pn` | `validate_2pn.py` | EXACT | δA = U³/6, δB = U²/2 term by term; the test-particle periastron excess π(GM/c²p)²(2 + e²/2) and its J0737−3039 reading ≈ 1.5 × 10⁻⁶ [chart] (21:C8, P6) |
| `grav.fold_echo` | `validate_fold_echo.py` | EXACT | the fold-return average at dev scale over F₁₇: the period-averaged exterior return is the uniform floor operator N⁻¹J_E, fold-independent (21:C12, P7) |
| — | `make_fig_*.py`, `make_all_figures.py` | — | the publication figures (matplotlib), outside the run |
| — | `gravcommon.py` | — | the registry: the script runner, `LEDGER` (family → rows), `LABELS`, `KIND`, `results.json` |

Run: `python3 run_all.py`. Any script also runs alone as before (`python3 validate_strongfield.py`), printing its own
PASS/FAIL line. Rebuild the notebook: `python3 make_notebook.py`.

## Provenance

The scripts are the paper's `validation/` suite: the twelve of the original suite (June 2026) and the nine of the
round-01/02 revisions (July–August 2026: `validate_2pn`, `validate_1pn_eih`, `validate_binding`, `validate_counting`,
`validate_defect`, `validate_inertia`, `validate_deepregime_orbit`, `validate_fold_echo`, and `validate_strongfield`'s
ISCO block), unchanged; the registry runs each script's source in its own namespace, routing the script's `chk` (where
it defines one) and its printed verdicts to the record. The public copy had carried the original twelve and the figure
scripts only (June–July 2026); its README is in `_to_delete/21-gravity-superseded/`. Not shipped, per the corpus
discipline stated in `validate_1pn_eih.py`: the failed first reduction of the comparable-mass 2PN ν-sector
(`validate_2body_2pn.py` in the corpus tree, which also fails under sympy 1.14 at its final evaluation); the sector is
open (master row T4).

## Predicate ledger

Rows A1–A9 imports; B1–B6 realisations; C1–C25 derived (C13–C19 composite T|R); X1–X8 the explanation register;
P1–P7 the predictions (P7 the former P1′); V1–V3 the verification; Z1 the Ω-hard running of a₀. Family → rows:
`gravcommon.LEDGER`.
