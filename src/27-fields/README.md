# 27-fields validation package

Validation package of *Standard-Model Interactions over Finite Relational Substrate* (Akhtman & Voether, 2026),
`27-fld` of the FRC corpus. The paper's twenty-eight validation scripts as written, run through one registry
(`fldcommon.py`): a family check is one script (`fld.<stem>`), its micro-checks the script's own PASS/FAIL lines
together with the registry's predicates, which read the script's namespace and printed output and decide the
manuscript's stated values explicitly — most of the scripts print their booleans and numbers without asserting them
(they exit 0 whatever they compute), so the decision is made in `fldcommon.py`, in the open, one labelled predicate per
stated value. An exception, a nonzero exit or a failed predicate fails the family. Driven by `27-fields-main.ipynb`
(Google Colab, *Runtime → Run all*, ≈ 1.5 min) or by `run_all.py`. Python 3.10+, numpy, sympy.

Every family names the row(s) of the paper's predicate ledger it witnesses (the paper's Section "Status", subsection
"Predicate ledger", 48 rows in blocks A, B, C, X, P, V, Z, O, cited as `27:XN`; public copy
`docs/27-fields/27-fields-ledger.html`); the ledger's source column cites the family ids in return; the paper's
Appendix "Reproducibility map" is the per-script map. Master-ledger rows of the corpus reached through the paper rows:
`00:B5`, `00:D2`, `00:D6`, `00:E1`, `00:E3`, `00:G1`, `00:H1`–`00:H3`, `00:I1`–`00:I4`, `00:J1`, `00:J4`, `00:K2`, `00:N1`,
`00:Z5`, `00:Z8`.

Three kinds — the paper's own classes (Appendix "Reproducibility map": exact 15, mixed 11, approx 2), recorded per
family in `results.json`: **EXACT** — integer, F_p, F_{p²} or cyclotomic arithmetic throughout, a pass a proof on the
tested instances; **MIXED** — an exact core with a labelled continuum-comparison layer ([approx] against published
constants, or a continuum reading), the exact claim never resting on the float part; **APPROX** — a
continuum-comparison or dimensional-transmutation reading by construction.

[![Open In Colab](https://colab.research.google.com/assets/colab-badge.svg)](https://colab.research.google.com/github/gamayos/finite-ring-space/blob/main/src/27-fields/27-fields-main.ipynb)

## In-tree

| family | script | kind | claims backed (ledger rows) |
|---|---|---|---|
| `fld.em1_prototype` | `em1_prototype.py` | MIXED | the finite U(1) prototype on Z/M (M = 12, 52, 156, 420): gauge invariance of flux, action, covariant difference; discrete Stokes; the Coulomb coefficient against 1/4π; like charges repel, gravity attracts (27:C2, C3, X2) |
| `fld.enumerate_maxwell` | `enumerate_maxwell.py` | MIXED | uniqueness of the Maxwell operator: exact F_p corank 2 on L = 4, 5, 6, one relevant operator = the transverse projector, one irrelevant O(k⁴) artefact (27:C2, X3) |
| `fld.audit_finitism` | `audit_finitism.py` | EXACT | the electromagnetic and admissible-space claims with no float: F(dλ) = 0 exhaustive, the L = 4 Green's function 257/7680, nullity 2 by integer rank, the Wilson action cyclotomic (27:C2, C3) |
| `fld.o2_numbers` | `o2_numbers.py` | MIXED | 1/α_bare = 4π; the 10³⁶ hierarchy; the open gap 4π → 137 (27:C2) |
| `fld.p2` | `p2.py` | MIXED | the order-one coefficient 1; the saturation profile's Coulomb coefficient, core r* and finite self-energy (27:C2) |
| `fld.correspondence` | `correspondence.py` | APPROX | the finite gauge correspondence, blocks A–H (27:C1, C7) |
| `fld.p3` | `p3.py` | EXACT | the SU(2,F₃) weak connection: order 24, exhaustive Wilson invariance, the doublet covariant, the drive breaking SU(2) (27:C4) |
| `fld.ew1` | `ew1.py` | EXACT | breaking as drive–torus misalignment over F₁₃; ρ = 1; sin²θ_W = 3/8 for a complete generation (27:C4, C5, C6, X4, X5) |
| `fld.weak_spectrum` | `weak_spectrum.py` | EXACT | the W, Z spectrum as the Hessian of S_ρ: photon kernel, ρ = 1 as det ≡ 0, cos²θ_W = 5/8; over Q, F₁₃, F₅ (27:C5, X3, X5) |
| `fld.weak_current` | `weak_current.py` | MIXED | the V−A current (N against 0, q = 3, 5, 7, 13), the chiral projector, G_F = 1/(√2 v²) (27:C4, C6, X6) |
| `fld.p4` | `p4.py` | EXACT | maximal parity violation from the Frobenius branch, exact in Z/(q+1) (27:C4, X6) |
| `fld.p10` | `p10.py` | EXACT | chirality selection relative to the drive, convention-invariant (27:C10) |
| `fld.v_scale` | `v_scale.py` | APPROX | the electroweak scale against the transmutation forms; the Y1 numeral 2^(3/2) m_P e^(−(2π)²) = 247.2 GeV (27:Y1, Z1) |
| `fld.qcd` | `qcd.py` | MIXED | SU(3,2) enumerated over F₄ (216, centre Z₃); the strong-coupling string tension (27:C7, X7) |
| `fld.p5` | `p5.py` | EXACT | the SU(3,F₄) gluon connection: exhaustive Wilson invariance, the self-coupling commutator, the triplet covariant (27:C7) |
| `fld.string_tension` | `string_tension.py` | MIXED | c₁ as an exact character sum: S₃, 2T closed form, the SU(3) series β/18 + β²/216; σ > 0 (27:C7, X7) |
| `fld.p6` | `p6.py` | MIXED | b₀ = 11 − (2/3)n_f exact; Λ_QCD by transmutation; (m_p/m_P)² = e^(−88) (27:X7, Z1) |
| `fld.missing_rank` | `missing_rank.py` | EXACT | the rank tower; \|SU(3,5)\| = 378 000; dim Λ^even(C⁵) = 16 (27:C7, C8) |
| `fld.generation` | `generation.py` | EXACT | the 16 = 1 ⊕ 5̄ ⊕ 10: charges, ΣY = ΣY³ = 0, 3/8 (27:C6, C8, X8) |
| `fld.p8` | `p8.py` | EXACT | the spinorial unification argument; τ_p ∝ M_X⁴, 10⁴⁸ yr at the Planck scale (27:C9, P4, X8) |
| `fld.p8b` | `p8b.py` | EXACT | the X, Y as the colour–isospin off-block: 24 − 12 = 12 (27:C9, X8) |
| `fld.p9` | `p9.py` | EXACT | Frobenius orbit sizes 2, 3, 6 on F_{q^n} for q = 2, 3, 5 (27:C10) |
| `fld.p9b` | `p9b.py` | EXACT | the 1 + 3 role split; the generation mass ordering (27:C10, X9, P1) |
| `fld.p11` | `p11.py` | EXACT | Ω ≡ 5 (mod 12) as the CRT conjunction; Dirichlet density 1/4 (27:C11) |
| `fld.p1` | `p1.py` | MIXED | one-loop running: 3/8 at α₁ = α₂ (≈ 10¹³ GeV); the α₃ near-miss (27:C6, P3) |
| `fld.p7` | `p7.py` | MIXED | the seesaw scale, b–τ unification, the winding-overlap hierarchy (27:P5, Z1) |
| `fld.koide` | `koide.py` | MIXED | the framed-rational Koide identity over five shells p ≡ 5 (mod 12); the measured Q against 2/3 (27:X10, P8) |
| `fld.strongcp` | `strongcp.py` | EXACT | Hermitian mass matrices over F_{p²}/F_p have det ∈ F_p; [M_u, M_d] ≠ 0 — 20 checks (27:X11, P9) |
| — | `fldcommon.py` | — | the registry: the script runner, `PRED` (the predicates per family), `LEDGER` (family → rows), `LABELS`, `KIND`, `results.json` |
| — | `reports/` | — | the two derivation memos (`correspondence.pdf`, `string-tension.pdf`) |

Run: `python3 run_all.py`. Any script also runs alone as before (`python3 ew1.py`), printing its own report. Rebuild the
notebook: `python3 make_notebook.py`.

## Provenance

The scripts are the paper's `validation/` suite (June–August 2026), unchanged except one instance: `weak_spectrum.py`'s
second finite-field example ran at (q, g, g′, v) = (5, 1, 2, 2), where g² + g′² = 5 ≡ 0 (mod 5) makes the Z massless
too, against the script's own printed claim; it now runs at (5, 1, 1, 2). The public copy had carried the June–July
versions of `o2_numbers.py`, `p7.py`, `v_scale.py`, `weak_spectrum.py`; its README is in
`_to_delete/27-fields-superseded/`. Registry-side findings recorded here, not repaired: `correspondence.py` block G's
last check is vacuous (`check(..., True)`), and its block A draws unseeded random pairs (the homomorphism identity holds
for every pair, so the verdict is unaffected); `p6.py`'s one-loop Λ_QCD from the M_Z anchor is 87 MeV against its
printed "observed ~200–300 MeV" (the registry decides the decade); `p8.py`'s printed band "1e44–1e47 yr" sits below its
own Planck-scale value 1.0 × 10⁴⁸ yr (the registry decides the M_X⁴ scaling and row P4's bound 10⁴⁵ yr); the F_q mass
matrices of `weak_spectrum.py` keep the imaginary cross term in the W₁W₂ block (the real part is taken over Q), which
none of the checked statements touch.

## Predicate ledger

Rows A1–A6 imports; B1–B6 realisations; C1–C11 derived (C3, C5, C6, C8–C10 composite T|R); X1–X11 the explanation
register; P1–P9 the predictions; V1–V3 the verification; Z1 the Ω-hard running and scales; Y1 the electroweak-scale
conjecture (formerly Y1; block O holds the open rows, as in the corpus). Family → rows: `fldcommon.LEDGER`.
