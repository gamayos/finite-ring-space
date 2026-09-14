# 35-hadrons validation package

Validation package of *Ground-State Light Hadron Spectroscopy over Finite Substrate* (Akhtman & Voether, 2026),
`35-hadr` of the FRC corpus. The paper's fifteen validation scripts and its figure script as written, run through
one registry (`hadcommon.py`): a family check is one script (`had.<stem>`), its micro-checks the script's own
verdict lines (fourteen assert their identities and print a report; `forward_eigenvalues` prints one `[PASS]` line
per check) together with the registry's predicates, which decide the stated values explicitly: the group order 216
and the centre Z_3, the colourless content (1, 0, 0, 1), the five scale-cancelling identities (Gell-Mann–Okubo, the
decuplet spacing, the third difference, Coleman–Glashow, the vector spacing) with their PDG residuals 0.57 %, 9.2 %,
0.36 %, 0.79 %, 0.42 %, the colour factor −8 and the spin pattern ∓3/4, the charge structure and the coefficients
β/18 and β²/36, the absolute spectrum within 1.1 %, the Λ–N gap 176.8 MeV, the Airy tower, the baryon eigenvalue
E₀ = 2.232 (M_N to 4.6 %), the forward landings 0.855/0.442. An exception, a failed assert, a nonzero exit or a
failed predicate fails the family. Driven by `35-hadrons-main.ipynb` (Google Colab, *Runtime → Run all*, ≈ 20 s) or
by `run_all.py`. Python 3.10+, numpy and sympy (the finite-grid eigenvalues and the symbolic identities); the
EXACT and MIXED cores need the standard library only; matplotlib for the figure script, which writes the paper's
two figures into `figures/` (ignored by git), each with a PNG sibling the notebook shows inline.

Every family names the row(s) of the paper's predicate ledger it witnesses (the paper's Appendix "Predicate
ledger", 65 rows in blocks A, B, C, X, P, V, Z, cited as `35:XN`; public copy `docs/35-hadrons/35-hadrons-ledger.html`);
the ledger's source column cites the family ids in return. Master-ledger rows of the corpus sourced from this
paper: `00:I5` (the hadron spectrum: the colour singlet, the SU(3)_F relations, the hyperfine invariant), `00:I6`
(the residue series and the stability selector), `00:I7` (the baryon scale E₀ and the forward eigenvalues).

Four kinds, recorded per family in `results.json`: **EXACT** — finite-field (F_4), integer or exact-rational
identities only, no float in the script; **MIXED** — an exact core (the asserted identity) with a labelled [approx]
decimal display of the PDG confrontation, verdict on the core and on the stated residual by tolerance;
**PROFINITE** — additionally a labelled [profinite approx] finite-grid eigenvalue (numpy linear algebra over a finite
matrix), verdict by stated tolerance; **CHART** — the figure script.

[![Open In Colab](https://colab.research.google.com/assets/colab-badge.svg)](https://colab.research.google.com/github/gamayos/finite-ring-space/blob/main/src/35-hadrons/35-hadrons-main.ipynb)

## In-tree

| family | script | kind | claims backed (ledger rows) |
|---|---|---|---|
| `had.su3_singlet` | `su3_singlet.py` | EXACT | colour SU(3,F_2) built over F_4: order 216, centre {I, ωI, ω²I} ≅ Z_3; the singlet rule is triality 0; det ≡ 1 so ε_abc is the invariant (35:B1, C1, X2) |
| `had.carrier_residue` | `carrier_residue.py` | EXACT | no colour vector fixed by the group (a quark has residue 0); Λ³ = det the invariant, residue 1; colourless content (1, 0, 0, 1); the residue series and the stability selector (35:B5, C15, X1, X3, X7) |
| `had.su3f_relations` | `su3f_relations.py` | MIXED | Gell-Mann–Okubo and the decuplet second differences vanish identically; PDG 0.57 %, spread 9.2 %, β = 146.8 MeV (35:C2, C3, P1, P2, X4, X5) |
| `had.su3f_second_order` | `su3f_second_order.py` | MIXED | the third difference and the two octet–decuplet hyperfine links vanish identically (sympy); PDG +6.0 MeV, 0.36 % (35:C11, C12, P8) |
| `had.hyperfine_charsum` | `hyperfine_charsum.py` | MIXED | the colour factor −8 (−8/3 per pair), g_spin ∓3/4 with separation 3/2, the eigenvalues ±2; A_light = 195.4 MeV (35:C4, C5, C6, P3, X6) |
| `had.isospin_cottingham` | `isospin_cottingham.py` | MIXED | Coleman–Glashow exact at one body (0.79 %); M_n > M_p from the d−u seed against ΣQ²; M_Σ > M_Λ from the ud pair spin (35:C7, C8, C9, P6, X8, X9, X10) |
| `had.heavy_flavour` | `heavy_flavour.py` | MIXED | M(Λ_b) − M(Λ_c) = M(B) − M(D) to −2.4 %; the 1/m_Q hyperfine ratio 0.339 ≈ m_s/m_c (35:C10, P7, X11) |
| `had.em_heavy_cmag` | `em_heavy_cmag.py` | MIXED | the charge structure (1, 0; 2/3, −1/3), the magnitude α√σ; the heavy masses m_Q + O(√σ); c_adj = β²/36 against c₁ = β/18 (35:C13, C14, C21, C22) |
| `had.absolute_masses` | `absolute_masses.py` | MIXED | the octet and decuplet from one scale and two ratios anchored to N, Λ, Δ: five predictions within 1.1 % [approx] (35:P10) |
| `had.vector_nonet` | `vector_nonet.py` | MIXED | the meson as residue 1 (B = 0); 2M_K* = M_ρ + M_φ exact; PDG −0.42 %, K* and ω under 1 % (35:C18, P9, X12) |
| `had.subhorizon_resolution` | `subhorizon_resolution.py` | MIXED | N = 3 on every admissible shell, the coefficients 1/18, 1/36 Ω-free; the residuals O(ε_s²): 0.017, 0.041 (35:C20, C23, X13) |
| `had.confinement_completion` | `confinement_completion.py` | PROFINITE | λ_l = 0.822, m_s/m_l = 1.489, λ_hf = 0.444; M_Λ − M_N = m_s − m_l = 176.8 MeV exactly; the Airy tower on the finite grid (35:C16, P11) |
| `had.final_resolution` | `final_resolution.py` | PROFINITE | the two kinds of sub-horizon residue, the Ω-free bound-state inputs, ε₁/ε₀ = 1.7484; the tally: six T rows, two Ω-hard, nothing open (35:C16, C20, X13) |
| `had.confinement_closure` | `confinement_closure.py` | PROFINITE | E₀ = 2.2322 converged across the tower, E₁/E₀ = 1.4917; M_N = E₀√σ = 982 MeV (4.6 %); λ_l, λ_hf from {M_N, M_Δ} (35:C17) |
| `had.forward_eigenvalues` | `forward_eigenvalues.py` | PROFINITE | [EXACT] the colour-spin algebra and the coefficients; [profinite approx] \|u'(0)\|² = 1, E₀ = 2.2323, F_rel = 3.52; [approx] α_s(√σ) ≈ 1, the landings within 7 % — ten checks (35:C17, C19) |
| `had.make_figures` | `make_figures.py` | CHART | the paper's two figures regenerated into `figures/` (35:V2) |
| — | `hadcommon.py` | — | the registry: the script runner, `PRED` (the predicates per family), `LEDGER` (family → rows), `LABELS`, `KIND`, `results.json` |

Run: `python3 run_all.py`. Any script also runs alone as before (`python3 su3_singlet.py`), printing its own report.
Rebuild the notebook: `python3 make_notebook.py`.

## Provenance

The scripts are the paper's `validation/` suite (June 2026, the continuum-free audit of 30 June), unchanged, and
`make_figures.py` its figure script; no public copy existed before this package. `forward_eigenvalues.py` guards its
own imports (`assert "random" not in sys.modules`); under the registry the process may already hold that module
through matplotlib or IPython, so the runner sets it aside for the script's run and restores it after — the script's
own imports are unchanged. The paper's README class "MIXED +[profinite approx]" is recorded here as the kind
PROFINITE. The forward landing λ_hf = 0.442 is taken at the hyperfine-required coupling α_s = 0.93 (the script's own
check), the transmutation value 1.00 giving 0.475.

## Predicate ledger

Rows A1–A9 imports; B1–B5 realisations; C1–C23 derived (C6, C10, C13, C17 composite T|Ω; C20–C23 the residue
resolutions, formerly E1–E4); X1–X13 the explanation register; P1–P11 the predictions (P1–P9 the body's list,
formerly D1–D7, D10 and the third difference; P10–P11 the absolute spectrum and the Λ–N gap, formerly D8, D9);
V1–V3 the verification; Z1 the Ω-hard residue, formerly E5. Family → rows: `hadcommon.LEDGER`.
