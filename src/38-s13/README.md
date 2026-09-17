# 38-s13 validation package

*Exact Quantum Dynamics on the Minimal (13,233) Holographic Substrate* (Akhtman & Voether, 2026; preprint
pp202608.0390). Discipline: every exact claim in the paper is integer-pinned; floating point appears only in
declared chart residuals, never behind a T-tagged claim. Twelve families through one registry (`s13common.py`);
the notebook `38-s13-main.ipynb` (Colab badge inside) runs them all; `results.json` carries one record per family
with the paper's ledger rows it witnesses. Rows are cited as `38:XN`; the public ledger is
`docs/38-s13/38-s13-ledger.html`, the laboratory `https://www.finitering.space/38-s13/`.

Run: `python3 run_all.py` (node ≥ 18 and python ≥ 3.10 with `sympy` for `o1_gr_chart`; ≈ 20 s, the rendering suite
dominating). Each script also runs on its own and exits nonzero on any failure.

## In-tree audits (here)

| family | script | kind | checks | claims backed |
|---|---|---|---|---|
| `s13.check_s13` | `check_s13.js` | EXACT | 58 | blocks A–D of the ledger: the pair constants (A1), the tower identity and its general form (A2), the channel gcds and N(i) = −1 (A3), the Carrier quarter roots ħ = 144, h = 89 (A4), the algebra half (A6), the frame counts (A7), the resolvable window (A8), the dilation instance 3/58 and the (53,13) kill test (C6), the per-chronon leak rate (κ/S)/(p−1) = 1/(Ω−1) at (13,233) and (5,233) (C10), the step law (D2), the stations, the covering 144 = 36 + 108, the ramification, the fusion (D6–D9), the registration fibre product |R| = 696 |
| `s13.check_o1` | `check_o1.js` | EXACT | 10 | the two faces of the leak, ratio 2 = the double cover (C7); the face-ratio identity 2 ⟺ 2γ − β = 1 over the PPN lattice (C8); the dictionary p_sl = 3(S/κ) r_g and the capacity reading (C12); the p = 53 regression |
| `s13.o1_gr_chart` | `o1_gr_chart.py` | SYMBOLIC [approx: continuum chart] | 10 | the parametrised isotropic metric's apsidal coefficient 2 − β + 2γ and clock-deficit coefficient 3/2, the ratio deviation (2/3)(2γ − β − 1), the dictionary match (C8, C12); Brans–Dicke's −2/(2+ω) with its GR limit (the combination is measured to 10⁻⁴; the identity discriminates nothing the data have not) |
| `s13.check_o2` | `check_o2.js` | EXACT | 11 | the covering parity theorem (D12): the reflection identity at p = 5, 13, 17, 29, μ ∈ {1, 3}, the 72/72 balance, the decider Ω-blind at p = 5, 17, 29 |
| `s13.check_o3` | `check_o3.js` | EXACT | 7 | the winding family (D13): the winding-1/5 identity, the 144-slot containment, the covering multiset, the axis passages 13j/m (m ≥ 4), the ramification 13/(2m) |
| `s13.check_phi` | `check_phi.py` | EXACT | 10 | the golden-ratio audit of the quarter roots (A4): h = 13/8 ≡ 89, ħ = 8/13 ≡ 144 on F₂₃₃ (the Fibonacci convergents), φ present iff 5 is a square, the Pisano closure, the Y6 lock constraint |

## The laboratory's suites (`docs/38-s13`, one source)

The six suites the laboratory ships (`node run-all.js` there runs them; 192 checks) are run by the registry from
`../../docs/38-s13`, not copied. The notebook's sparse checkout takes both directories.

| family | suite | checks | claims backed |
|---|---|---|---|
| `s13.verify-233` | `verify-233.js` | 84 | pair dynamics, events, octant bridge, the precession 3/58 with the joint cycle 696 and the half event, the mass–energy channel (B5) |
| `s13.verify-sky` | `verify-sky.js` | 28 | the node field, the radial ladder, the mounting, the central product isomorphism (B1–B3) |
| `s13.verify-space` | `verify-space.js` | 25 | the register, cone arithmetic, the winding spectrum, the curl algebra δ₅₈ = h (D11) |
| `s13.verify-f13` | `verify-f13.js` | 25 | the shell operator core H⁷ = 0, ord(U) = 13, U exactly unitary (D11) |
| `s13.verify-hopf` | `verify-hopf.js` | 10 | the finite Hopf fibration, the frame counts 2184 = 156 × 14, Ω-blind at p = 5 (A7) |
| `s13.verify-render` | `verify-render.js` | 20 | the production rendering itself: the sky chronon, the Hopf representation, the frame leak, the flow law, the stations, the rays, the quadrature pair (B4, B6, B7, C1–C5, D1, D3–D5, D10, V2) |

`results.json` records for every family: `id`, `rows` (the `38:` rows witnessed), `script`, `file` (the path in this
repository), `kind`, `label`, `ok`, `detail`. Verification history: the 1-phase laboratory suites (frozen phase-5
build 189 checks; 192 at phase 6), the in-tree audits of 1–15 August 2026, `check_s13` at 58 checks since the T30
push of 14 September 2026 (the per-chronon rate C10).
