# 22-quantum validation package

Validation package of *Quantum Observation over Finite Holographic Substrate* (Akhtman & Voether, 2026), `22-qm`
of the FRC corpus. The paper's seventeen validation suites as written — 187 labelled checks in exact arithmetic
(modular integers, Gaussian integers, cyclotomic rings, exact rationals), one `PASS` line per check, a `FAIL` raising
an assertion — run through one registry (`qmcommon.py`): a family check is one suite's verdict (`qm.<suite>`), its
micro-checks the suite's PASS/FAIL lines; an assertion, an exception or a nonzero exit fails the family. Driven by
`22-quantum-main.ipynb` (Google Colab, *Runtime → Run all*, ≈ 1–2 min) or by `run_all.py`. Python ≥ 3.10, numpy, sympy.

Every family names the row(s) of the paper's predicate ledger it witnesses (the paper's Section "Status", subsection
"Predicate ledger", 61 rows in blocks A, B, C, X, P, V, Z, cited as `22:XN`; public copy
`docs/22-quantum/22-quantum-ledger.html`); the ledger's source column cites the family ids in return, and the paper's
Appendix B carries the check-level map (suite: checks → claim). Master-ledger rows of the corpus reached through the
paper rows: `00:D4`, `00:F1`, `00:C10`, `00:C11`, `00:F2`, `00:F3`, `00:D1`, `00:D3`, `00:D10`, `00:B8`, `00:Y5`.

Kinds, recorded per family in `results.json`: **EXACT** (sixteen families) — exact arithmetic throughout, exhaustive
where the domain is finite, deterministic (fixed test states; the one random draw, the sampled √m illustration of
`equivalence.py`, decides nothing); **NUM** (`emulation`) — floating point as the numeric image of exact references,
agreement to 10⁻¹².

[![Open In Colab](https://colab.research.google.com/assets/colab-badge.svg)](https://colab.research.google.com/github/gamayos/finite-ring-space/blob/main/src/22-quantum/22-quantum-main.ipynb)

## In-tree

| family | suite | checks | arithmetic | claims backed (ledger rows) |
|---|---|---|---|---|
| `qm.validate` | `validate.py` | 19 | F₁₅₇, F₄₂₁, Z[i], Z[ζ₁₂] | the single-system formalism: cores, fibres, the selection rule over all channel pairs, drive eigenstates, forced-basis orthogonality/Parseval/Lüders, ledger selection, reduction commutation, the two-regime dichotomy (22:C1–C5, C7, C9, C24) |
| `qm.sorkin` | `sorkin.py` | 8 | Z[i], shadows mod 157 | Sorkin nullity I₃ = I₄ = 0, I₂ ≠ 0 on F₁₅₇, F₄₂₁; sub-horizon shadow exactness; wrap quantisation in pZ (22:C8, P2, X8) |
| `qm.dispersion` | `dispersion.py` | 9 | F₁₃, F₁₆₉ | exact boost transport, all 168 boosts, full-cycle covariance, Dirac→KG factorisation, the finite spinor double cover S^((p+1)/2) = −I (22:A2, P4) |
| `qm.composite` | `composite.py` | 18 | F₆₄₁, Z[ζ₈₀], Z[ζ₈]; F₄₂₁ | the composite gate: conserved offset, σₓ readout, the singlet law, no-signalling, the 80³ CHSH sweep, Tsirelson S² = 8; the unequal-cycle gate U1–U6 (22:C15–C17, C26, P3, X7) |
| `qm.synchronisation` | `synchronisation.py` | 26 | F₆₄₁, F₁₃, Z[ζ₁₆], Z[ζ₄] | the m-body conserved offset, orbit lengths and bijective labelling, m² coherent vs m incoherent, exhaustive for m ≤ 6 (22:C15) |
| `qm.renou` | `renou.py` | 10 | Q(ζ₈) | the real-vs-complex network: Bell basis, swapping, the full conditional table, the witness 6√2, source independence (22:C18, P3) |
| `qm.bmv` | `bmv.py` | 6 | Q(ζ₈₀) | the gravitational channel: C² = sin²(φ/2), the Horodecki bound, drive commutation, no-signalling, V² + C² = 1 (22:C19, P1) |
| `qm.decoherence` | `decoherence.py` | 7 | Q(ζ₄₀), Z[ζ₇] | forbidden collapse, dilation dephasing, the exact revival; the integral registered count P = 1/7 (22:C7, C20) |
| `qm.equivalence` | `equivalence.py` | 5 | exact rational lattice Poisson | the two scaling laws, η = 0, E|Σ|² = m (22:C22) |
| `qm.granularity` | `granularity.py` | 7 | Q(ζ₈), Q(i) | the depth ceiling: denominator and tally-norm laws, k* = 8/6 in F₆₄₁ and 404/202 at the corpus windows, the conductor-4 splitting law (22:C14, P5) |
| `qm.stratum` | `stratum.py` | 12 | Z[i], Z[ζ₁₂], F₆₄₁ | the two probability strata, the engineered-core residues on Ω = 641, the readout map, the trace and Parseval tallies (22:C10, C11) |
| `qm.gravfraction` | `gravfraction.py` | 12 | Z[ζ₁₆] | the coherent-fraction channel: branch phases, envelope separation, the assembled channel, the 15-partition classification, the local-additivity theorem (22:C21) |
| `qm.gleason` | `gleason.py` | 9 | Z[i], exhaustive Q₄ | uniqueness of the pair tally: the admissible kernels, channel fixing, the fibre-norm counterexample, the pure-winding fixing, the spanning transfer (22:C12) |
| `qm.emulation` | `emulation.py` | 7 | numeric (10⁻¹² vs exact) | the 12- and 16-level compilations of the forced bases, the laws on them, the gate decomposition, the two experiment cards (22:V3) |
| `qm.omega` | `omega.py` | 4 | scale arithmetic | the Ω ledger: floors below the anchor, the joint window, scale coherence, the binding floor (22:A5, Z2) |
| `qm.intersubject` | `intersubject.py` | 22 | F₄₂₁, Z[ζₙ] | inter-Subject consistency with equal and embedded cores; the incomparable-core control (22:C23, X4) |
| `qm.transport` | `transport.py` | 6 | F₁₅₇, F₄₂₁, F₆₄₁ | the quarter-turn transport trichotomy: faithful, conjugate, broken (22:C27) |
| — | `qmcommon.py` | — | — | the registry: the suite runner, `LEDGER` (family → rows), `LABELS`, `KIND`, `results.json` |

Run: `python3 run_all.py`. Any suite also runs alone as before (`python3 composite.py`). Rebuild the notebook:
`python3 make_notebook.py`. The six technical-note PDFs (`reports/`) are the per-target write-ups of the suites.

## Provenance

The suites are the paper's `validation/` directory as it stands in the corpus tree (June–July 2026 with the
round-05 repair of `gleason.py`, whose wording is "channel fixing" as in the paper's Appendix B — the public copy
had carried the earlier "pinning" wording), unchanged; the registry runs each suite's source in its own namespace and
records its printed verdicts. The public README of July 2026 is in `_to_delete/22-quantum-superseded/`.

## Worked configurations

| carrier | generator | Subject(s) | Object(s) | core | quotient |
|---|---|---|---|---|---|
| F₁₅₇ | g = 5 | S₅₃ (C₅₂) | O₁₃ (C₁₂) | Q₄ | C₃ |
| F₄₂₁ | g = 2 | S₆₁ (C₆₀) | O₂₉ (C₂₈); O₁₃ (C₁₂) | Q₄; C₁₂ | C₇; C₁ |
| F₆₄₁ | g = 3 | S₄₁×2 (C₄₀) | O₁₇×2 (C₁₆) | C₈ | C₂ |

## Predicate ledger

Rows A1–A8 imports (A5 Ω-hard); B1–B8 realisations with their falsifiers; C1–C27 derived (C11, C21, C25 composite
T|R); X1–X8 the explanation register; P1–P5 the predictions; V1–V3 the verification; Z1–Z2 the Ω-hard residues.
Family → rows: `qmcommon.LEDGER`.
