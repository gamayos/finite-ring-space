# 8-dirac validation package

Validation package of *Schrödinger and Dirac Dynamics over Finite Substrate* (Akhtman, Preprints 2025,
doi 10.20944/preprints202510.1486.v2), `8-dirac` of the FRC corpus, added with the paper's predicate ledger
(13 September 2026; one script since 24 September 2026). One script, `dirac.py`, eight blocks, 52 family checks over
3 848 exact micro-checks, standard library only — exact integer arithmetic over F_p and K = F_p[w]/(w² − ν), no floats,
no random sampling — driven by `frc-8-dirac.ipynb` (Google Colab: one cell per ledger predicate, any cell on its own, or
*Runtime → Run all*, ≈ 1 min) or run whole.

Every family check is the labelled claim of a block (`fin.S1`, `o2.C3i`, `o8.X7`, …) and names the predicate(s) of the
paper's predicate ledger it witnesses (Appendix A "Predicate ledger and machine verification", 43 predicates in blocks
A–F, T, cited as `8:XN`; public copy `docs/8-dirac/index.html`), and the ledger's source column links, for each
machine-verified predicate, the script at the check that decides it (`dirac.py#<key>`) and the Lean module at the
predicate's declaration (`lean/FrcCore/Dirac.lean` with no axioms, or `lean/FrcLedger/Dirac.lean` on Mathlib); the check
here is the instance the reader can run; the two witnesses decide the same statements at different generality.
Master-ledger predicates of the corpus reached through the paper predicates: `00:C3` (8:B4), `00:C8` (8:B5, 8:B6),
`00:B10` (8:B5).

Run: `python3 dirac.py` (python ≥ 3.9, no third-party packages; ≈ 1 min; `results.json` written), or the named blocks:
`python3 dirac.py o8 lat`; installed, `python3 -m frc_8_dirac`.

| block | claims backed |
|---|---|
| `fin` | the F_13 worked examples (the paper's p = 13 computations, `finite_checks.py` until 24 September 2026): power-map counts (Prop `power-map-count`, 8:E2); the Cayley step of H = −Δ, U¹³ = I, every trace-zero parameter admissible with order 13, unitarity (Ex `cayley-13`, Thm `cayley-preservation`, 8:C4, C6, E3); the Dirac example — Clifford, boost formulas, transported gammas with A = 10, B = 2, covariance on a sample field (Ex `dirac-13`, Props `clifford`, `spin-conjugation`, `transported-dirac-form`, Cor `boost-covariance`, 8:D2, D6–D8, D12) |
| `shell` | Thm `zonal` exhaustively over windings and cycle points (8:F3), the sector separation (8:F4), the F_17 numbers (8:D5, D12) |
| `o2` | Lemmas `class-datum`, `canonical-nu`: the square classes of every named residue on all symmetry-complete shells p < 2000, the anchors F_13, F_17 and the lab Carrier (8:B2–B4, D5, D12) |
| `o7` | Thms `parity`, `even-transport`, Cor `two-seats`: the parity grading exhaustive over every primitive root of the worked shells, ν = c²·(2g), the chart-grading clause (8:B4–B6) |
| `o134` | Lemma `boost-torus` by exhaustive enumeration with Hilbert 90 per element, Thm `cayley-transform`, Thm `period-dichotomy` with attained orders, the quintic datum, the minimality of F_17 (8:C5, C6, D5, D12, E4) |
| `o8` | Lemma `spinor-form` at p = 5, 13, 17 with the γ⁰-twist failure, Thm `dirac-evolution` in 1+1 at p = 5, the commuting composite of Cor `sectors`, the spin-lift transport of Prop `two-diracs`, the dispersion relation (8:D9–D11, F4) |
| `lat` | the latitude indices of the shell reading on F_13, F_17 and the lab Carrier (8:F2) |
| `o9` | Remark `signature-record`: zero counts of the Euclidean and Q_ν forms on p < 60, 2353/2041 at p = 13, the collapse over K (8:B7) |

| id | block | kind | claim | ledger predicate |
|---|---|---|---|---|
| `fin.S1` | fin | EXACT | power maps on F_13^×: image counts (p−1)/gcd(ε, p−1) and loss factors gcd(ε, p−1) for ε = 1, 2, 3, 4, 6, 12 | `8:E2` |
| `fin.S2` | fin | EXACT | Cayley step of H = −Δ on F_13 at α = c: U^13 = I; every trace-zero α = kc admissible with exact order 13 (k ≠ 0) | `8:C4`, `8:C6`, `8:E3` |
| `fin.S3` | fin | EXACT | F_13 Dirac example: Clifford relations for η = diag(−2,1,1,1); S⁻¹γ^μS boost formulas; transported γ̂⁰ = 10γ⁰ − 4γ¹, γ̂¹ = −2γ⁰ + 10γ¹; A = 10, B = 2; covariance on a sample field | `8:D2`, `8:D6`, `8:D7`, `8:D8`, `8:D12` |
| `shell.Z1` | shell | EXACT | the drive pullback is a permutation operator with D χ_k = g^{−k} χ_k on every character and cycle point (p = 13, 17) | `8:F3` |
| `shell.Z2` | shell | EXACT | isotropy: ⟨χ_k, χ_k⟩ = 0 except k = 0, (p−1)/2 with eigenvalues ±1 | `8:F3` |
| `shell.Z3` | shell | EXACT | sector separation: ord(g⁻¹) = p − 1 > 2, the free evolution is no Cayley step of a Frobenius-fixed Hamiltonian | `8:F4` |
| `shell.Z4` | shell | EXACT | F_17 example: i = 3^{−4} = 4, 2, i, e squares, g nonsquare; ν = 3, A = 15, B = 1, A² − νB² = 1; \|G_3\| = 18, \|G_2\| = 14; an order-3 boost at 17, none at 13 | `8:D5`, `8:D12` |
| `o2.C1` | o2 | EXACT | every primitive g is a nonsquare on every symmetry-complete shell p < 2000 | `8:B3` |
| `o2.C2` | o2 | EXACT | the nonsquare class is unique: the product of two nonsquares is a square | `8:B2` |
| `o2.C3i` | o2 | EXACT | i = g^{−κ} is a square iff κ is even (8 \| p − 1), on every symmetry-complete shell p < 2000 | `8:B3` |
| `o2.C3a` | o2 | EXACT | 2, 2⁻¹, −2 are squares iff κ is even: on κ-even shells g is the only named nonsquare | `8:B3` |
| `o2.C4` | o2 | EXACT | e = g^i has no stable square class (counterexamples both ways) | `8:B3` |
| `o2.C5` | o2 | EXACT | flip stability: [g⁻¹] = [g] | `8:B3` |
| `o2.C6` | o2 | EXACT | \|G_ν\| = p + 1 with ν = g, by exhaustive enumeration on small shells | `8:D5` |
| `o2.C7` | o2 | EXACT | F_13 anchor: g = 2 = ν, i = 5, 2⁻¹ = 7 nonsquare (κ odd, non-admissible) | `8:B4` |
| `o2.C8` | o2 | EXACT | F_17 anchor: 2, i = 4, e squares, only g = 3 nonsquare, \|G_3\| = 18 | `8:B4`, `8:D12` |
| `o2.C9` | o2 | EXACT | lab Carrier Ω = 2,408,561: g = 6 nonsquare; 2, 2⁻¹, −2, i = ħ = 18,688 squares; c = √(2⁻¹) = 171,106 base-rational | `8:B4` |
| `o7.P1` | o7 | EXACT | squares = ⟨g²⟩: the square class is the drive-step parity, exhaustive on every primitive g of F_13, F_17, Euler form on p < 2000 | `8:B5` |
| `o7.P2` | o7 | EXACT | ν = c² · (2g) exactly (2c² = 1); lab-Carrier instance 1,204,281 · 12 = 6 = g | `8:B4` |
| `o7.P3` | o7 | EXACT | [c²] even iff κ even, [2g] odd iff κ even, the product odd on every shell | `8:B4` |
| `o7.P4` | o7 | EXACT | on κ-even shells every element of Q₄ = {1, i, −1, −i} is a square: the chart grading carries no signature | `8:B5` |
| `o7.P5` | o7 | EXACT | N(gx) = g² N(x), g² a square (registered transport even), g odd, x² = g unsolvable in F_p | `8:B6` |
| `o7.P6` | o7 | EXACT | gauge stability: dlog_g(g⁻¹) = −1 odd — the flip preserves the parity class | `8:B6` |
| `o134.O1a` | o134 | EXACT | kernel of (x, y) ↦ Λ(x, y) is the scalar line: p − 1 preimages per boost, \|G_ν\| = p + 1 | `8:D5` |
| `o134.O1b` | o134 | EXACT | Hilbert 90: A − Bw = z/z̄, z F_p^× ↦ z/z̄ a bijection onto N¹ | `8:D5` |
| `o134.O1c` | o134 | EXACT | G_ν is cyclic: an element of order p + 1 exists | `8:D5` |
| `o134.O1d` | o134 | EXACT | an order-3 boost exists iff 3 \| p + 1 (17 yes, 13 no) | `8:D5` |
| `o134.O1e` | o134 | EXACT | F_17 is the minimal admissible shell: κ = 4 even, κ ≡ 1 (mod 3), p ≡ 5 (mod 12), no smaller symmetry-complete p | `8:D12` |
| `o134.O3a` | o134 | EXACT | the Cayley map φ(λ) = (1+aλ)/(1−aλ), a ∈ K⁻ nonzero, bijects P¹(F_p) onto N¹ with φ(∞) = −1 | `8:C5` |
| `o134.O3b` | o134 | EXACT | the unitary group of one channel is N¹ = C_{p+1} | `8:C5` |
| `o134.O4a` | o134 | EXACT | kinetic case: H = −Δ nilpotent, U unipotent, ord(U) = p | `8:C6`, `8:E4` |
| `o134.O4b` | o134 | EXACT | potential case: H = M_V diagonal, eigenphases in N¹, ord(U) = p + 1 (13 → 14, 17 → 18) | `8:E4` |
| `o134.O4c` | o134 | EXACT | mixed case: ord(U) = 1563 for H = −Δ + M_id at p = 5 | `8:E4` |
| `o134.O4d` | o134 | EXACT | composite: the order of a block-diagonal pair is the lcm (13, 14 → 182) | `8:E4` |
| `o8.X1` | o8 | EXACT | plain adjoints: (γ⁰)† = −γ⁰, (γ¹)† = −γ¹, (γ²)† = +γ², (γ³)† = −γ³ (p = 5, 13, 17) | `8:D9` |
| `o8.X2` | o8 | EXACT | the spinor twist X = γ⁰γ¹γ³: Hermitian, X² = ν, commutes with γ⁰, γ¹, γ³, anticommutes with γ²; X⁻¹(γ^μ)†X = −γ^μ for all μ | `8:D9` |
| `o8.X3` | o8 | EXACT | the γ⁰-twist fails: signs remain mixed | `8:D9` |
| `o8.X4` | o8 | EXACT | T − T⁻¹ nilpotent and anti-self-adjoint; D^s X-self-adjoint and nilpotent | `8:D9` |
| `o8.X5` | o8 | EXACT | 1+1 at p = 5: H = D^s X-self-adjoint, the Cayley step X-unitary, unipotent with ord(U) = 25 = p² | `8:D10` |
| `o8.X6` | o8 | EXACT | massive: H = D^s − mI, ord(U) = lcm(p-power, ord_{N¹} φ(−m)) for m = 1, 2 at p = 5 | `8:D10` |
| `o8.X7` | o8 | EXACT | the cycle Laplacian Δ_Φ is self-adjoint, its Cayley steps commute with D, the composite is unitary (p = 13) | `8:F4` |
| `o8.X8` | o8 | EXACT | spin lift vs the spinor form: S(x,y)# = S(x,−y) = δS⁻¹; the transport scales the X-form by N(z), norm-one lifts preserve it | `8:D11` |
| `o8.X9` | o8 | EXACT | the dispersion relation on the cycle: −Δ_Φ χ_k = (2 − g^k − g^{−k}) χ_k for every k (F_13); D^s − m invertible for m ≠ 0 | `8:F4` |
| `lat.L1` | lat | EXACT | ladder bounds: the energy index κ + 1 is the first rung past the midpoint of the ladder 1 … 2κ | `8:F2` |
| `lat.L2` | lat | EXACT | one shift, two ladders: m ↦ m + κ is multiplication by g^κ = ±i; a ↦ a + κ sends 1 ↦ κ + 1 | `8:F2` |
| `lat.L3` | lat | EXACT | κ = −4⁻¹, so the energy radius is 1 + κ = 3·4⁻¹ | `8:F2` |
| `lat.L4` | lat | EXACT | terminal latitude: π = 2κ = −2⁻¹ = −c²; on the Carrier π_Ω = 2S | `8:F2` |
| `lat.L5` | lat | EXACT | chart consistency: the unit-norm circle has p − 1 points; the energy circle carries norm 9/16 | `8:F2` |
| `o9.S1` | o9 | EXACT | the Euclidean form t² + x² + y² + z² has p³ + p² − p zeros on every symmetry-complete shell p < 60 | `8:B7` |
| `o9.S2` | o9 | EXACT | the form −νt² + x² + y² + z², ν = g, has p³ − p² + p zeros | `8:B7` |
| `o9.S3` | o9 | EXACT | p = 13: the counts are 2353 and 2041 | `8:B7` |
| `o9.S4` | o9 | EXACT | over F_{p²} every element of F_p is a square: the extension erases the dichotomy | `8:B7` |

`results.json` carries one record per family check (id, rows, block, script, kind, claim, PASS/FAIL, detail); the site
generator reads it to colour the witnesses on the public ledger page.

## One cell per predicate

`frc-8-dirac.ipynb` (built by `make_notebook.py`, executed) carries one cell per witnessed ledger predicate, addressable by
its stable id (the predicate's accession key, e.g. `p08029` for `8:D9`; the ledger page opens the notebook at the cell). Every cell is self-contained: it installs the
package from the site (`pip install frc-8-dirac --find-links https://finitering.space/pkg/` — a named requirement,
so pip reports it already satisfied once installed; the sdist `frc-8-dirac-<version>.tar.gz` that `src/make_pkg.py`
writes under `docs/pkg/` at each site build; import name `frc_8_dirac`, `__init__.py` exporting `predicate` and `verify_all`),
states the predicate and runs `predicate("8:D9")`: the blocks of the families that cite the predicate run once per session (the
deciding family is `dirac.PREDICATES`, the block the prefix of its id), the deciding check is printed from the script's own source — the line under its
`# 8:D9 (<key>)` marker — and every record citing the predicate is listed with its verdict. The markers in `dirac.py`
are the lines the ledger page's source glyph opens (`docs/src/8-dirac/#<key>`). The predicates'
Lean counterparts are the declarations named by their keys (`p08029`) at the end of `lean/FrcCore/Dirac.lean` and
`lean/FrcLedger/Dirac.lean` (`lean/make_predicates.py`), one per predicate, with the module as one executable file for the
web editor (`lean/web/core/Dirac.lean`, `lean/web/Dirac.lean`).

## Provenance

The scripts of the paper's `supplement/` were kept as written (wrapped in a `run()` reporting to a shared registry,
13 September 2026) and merged into the one script on 24 September 2026: the registry is the head of `dirac.py`, the
p = 13 library the section after it, each former script a block function under a banner carrying its docstring; the
micro-check labels and the family records are unchanged (`results.json` compared record by record), except that the
massless datum of `o8.X5` reads `ord(U) = 25 = p²`, the paper's own number (Theorem `dirac-evolution`), where the label
had said 5. Pre-merge files in `src/_to_delete/`.
