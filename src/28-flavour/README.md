# 28-flavour validation package

Validation package of *Fermion Flavour Sector over Finite Relational Substrate* (Akhtman & Voether, 2026), `28-flav`
of the FRC corpus. The paper's sixteen validation scripts as written, run through one registry (`flvcommon.py`): a
family check is one script (`flv.<stem>`), its micro-checks the script's own verdict lines (twelve of the sixteen print
`[PASS]`/`[OK]`/`[EXACT]` lines and a pass count) together with the registry's predicates, which decide the stated values
explicitly where a script prints without asserting (`framed_koide`, `theta13`, `scale_a`, `coupling_anchor`) and pin the
headline numerals elsewhere (the pass counts, Q_ℓ − 2/3, Σm_ν on both orderings, the Cabibbo relation, the TM2 band).
An exception, a nonzero exit or a failed predicate fails the family. Driven by `28-flavour-main.ipynb` (Google Colab,
*Runtime → Run all*, ≈ 1 min) or by `run_all.py`. Python 3.10+, numpy, sympy; scipy for `tm2_jointfit`.

Every family names the row(s) of the paper's predicate ledger it witnesses (the paper's Appendix "Predicate ledger",
49 rows in blocks A, B, C, X, P, V, Z, cited as `28:XN`; public copy `docs/28-flavour/28-flavour-ledger.html`); the
ledger's source column cites the family ids in return. Master-ledger rows of the corpus reached through the paper rows:
`00:K2`, `00:K3`, `00:K4`, `00:J2`, `00:J4`, `00:D2`, `00:D8`, `00:Z6`, `00:Z8`, `00:C7`, `00:B5`.

Three kinds — the suite's own classes (EXACT 2, MIXED 7, APPROX 7), recorded per family in `results.json`: **EXACT** —
integer, F_p, F_{p²} or cyclotomic arithmetic throughout, no float in any asserted claim; **MIXED** — the script carries
its own exact check for at least one claim, the continuum confined to labelled [approx] comparisons; **APPROX** —
continuum/numerical by construction: a numerical reconfirmation of an identity proven exactly in `exact_core`, a
comparison with measured data, or an Ω-hard reading.

[![Open In Colab](https://colab.research.google.com/assets/colab-badge.svg)](https://colab.research.google.com/github/gamayos/finite-ring-space/blob/main/src/28-flavour/28-flavour-main.ipynb)

## In-tree

| family | script | kind | claims backed (ledger rows) |
|---|---|---|---|
| `flv.exact_core` | `exact_core.py` | EXACT | the float-free core, 25 verifications: the circulant Koide identities in Q(ω, √2), the π/12 boundary, the cubic Gauss sums as integer group-ring identities, the magic matrix's maximal Jarlskog, Koide over framed rationals and N(1 − ζ_n) = 2, 3 in F_p (28:C1, C2, C3, C4, C10, Z1) |
| `flv.framed_koide` | `framed_koide.py` | EXACT | Q = 2/3 natively over framed rationals in F_{p²}/F_p on p = 17, 53, 89; the √2 amplitude the rational N(b)/a² = 1/2 (28:C2, X1) |
| `flv.tier_b` | `tier_b.py` | MIXED | the Tier-A/B figures: Q_ℓ against 2/3, the symbolic Koide identities, ρ = 1/√2, the λ-texture and Gatto, the Georgi–Jarlskog double ratio, the lopsided split with its seesaw control (28:C2, C6, C8, X3, X5, P1) |
| `flv.m10` | `m10.py` | MIXED | the winding kernel: the circulant √M and its eigenvalues, Q = 1/3 + r²/6, δ_LO = π/12 with the electron massless, the per-sector extraction (28:C1, C2, C3, X7) |
| `flv.delta` | `delta.py` | MIXED | the phase lock 1 : 1/2 : 1/3 and its robustness, the Gauss-sum reality and π/3 quantisation on small shells (28:C3, C5, Z1, Z2) |
| `flv.revision_checks` | `revision_checks.py` | MIXED | J = 1/(6√3), δ_LO = 1/24 cycle, the signed Koide, the cube invariant; 3δ₀ = Q, the branch preference, the Q_u schemes (28:C3, C10, C11b, P2, Z1) |
| `flv.quark_amp` | `quark_amp.py` | MIXED | the colour dressing of the quark amplitudes: Q_d from GJ, r_u ≈ √3, N(1 − ζ_n) = 2, 3 in F_p, the Q_u scheme band (28:B4, C4, X2, P2) |
| `flv.up_doubling` | `up_doubling.py` | MIXED | the up-sector doubling (8, 4) = 2 × (4, 2) from 10·10 against 10·5̄ (28:B3, C7, X6) |
| `flv.spurion` | `spurion.py` | APPROX | the Cabibbo spurion: Gatto, λ from the down circulant, λ ≈ δ₀ ≈ 2/9 (28:C6, X4, Z1) |
| `flv.theta13` | `theta13.py` | APPROX | θ₁₃ = θ_C/√2 as a leading-order estimate (7 %), quark–lepton complementarity, the fold onto δ₀/√2 (28:C9, X9) |
| `flv.neutrino` | `neutrino.py` | MIXED | the seesaw of circulants; Q_ν = 2/3 on both orderings, the boundary branch, Σm_ν = 59.1 meV, the 58.8 meV floor (28:C11, C11b, P5, P6, X11) |
| `flv.pmns_cp` | `pmns_cp.py` | APPROX | the magic matrix and maximal Jarlskog; θ₂₃ = 45° ⇔ \|δ_CP\| = 90° over TM2; δ_CP at the observed angles (28:C10, P8, X10) |
| `flv.tm2_jointfit` | `tm2_jointfit.py` | APPROX | the TM2 status: the protected column, the solar accommodation, θ₁₃ ≈ 9.15°, the joint-fit parameter count, the cos δ_CP–θ₂₃ relation and its band (28:C9, C10, P8) |
| `flv.scale_a` | `scale_a.py` | APPROX | the overall scale as transmutation: y_t ≈ 1, the quartic's descent, v/M_P = e^(−38.4), a² ≈ y_τ v (28:Z3) |
| `flv.coupling_anchor` | `coupling_anchor.py` | APPROX | the bare 1/4π against the unified continuum coupling: the matching offset, the near-miss (28:Z4) |
| `flv.alpha_probe` | `alpha_probe.py` | APPROX | the α ledger: the 4π anchor, the electroweak decomposition, 3/8 at unification, the one-loop fermion sum (≈ 100, not 137), the 10³⁶ hierarchy (28:A2, Z4) |
| — | `flvcommon.py` | — | the registry: the script runner, `PRED` (the predicates per family), `LEDGER` (family → rows), `LABELS`, `KIND`, `results.json` |

Run: `python3 run_all.py`. Any script also runs alone as before (`python3 exact_core.py`), printing its own report.
Rebuild the notebook: `python3 make_notebook.py`.

## Provenance

The scripts are the paper's `validation/` suite (June–August 2026), unchanged. The public copy had carried the July
versions of `alpha_probe.py`, `delta.py`, `neutrino.py`, `quark_amp.py`, `tm2_jointfit.py` (before the T23 scheme-band
and both-orderings revisions); its README is in `_to_delete/28-flavour-superseded/` with the five old scripts.
Registry-side findings recorded here, not repaired: five of the scripts' own checks are vacuous (`check(…, True)`:
`delta` 1.reduce and 4.count, `neutrino` 1.koide_form and 3.robust, `alpha_probe` C.nearmiss — statements, not
decisions; the registry's predicates decide their content where a number is stated); `tm2_jointfit`'s joint fit draws
unseeded random starts (its χ² ≈ 0 verdict is insensitive to them); `tier_b`'s Georgi–Jarlskog check passes within
20 % (the paper carries the 15 % excess as open, and the registry pins it to 10–20 %). One paper numeral corrected
against its cited script: row AL5 of the paper's Appendix B said the one-loop fermion sum from 4π "gives ≈ 90"; the
script adds ≈ 87 to 4π, giving ≈ 100 (the registry pins both).

## Predicate ledger

Rows A1–A6 imports; B1–B5 realisations; C1–C12 (with C11b) derived (C2, C4, C11, C11b composite T|R); X1–X11 the
explanation register; P1–P8 (no P4) the predictions, formerly D1–D8; V1–V3 the verification; Z1–Z4 the Ω-hard
residues, formerly D10–D13. Family → rows: `flvcommon.LEDGER`.
