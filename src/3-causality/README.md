# 3-causality validation package

Validation package of *Euclidean–Lorentzian Dichotomy and Algebraic Causality in Finite Ring Continuum* (Akhtman,
Entropy 2025, 27, 1098), `3-causality` of the FRC corpus, added with the paper's predicate ledger (Appendix A,
17 September 2026; one script since 24 September 2026). One script, `causality.py`, four blocks, sixteen exact checks, standard library only, driven by
`frc-3-causality.ipynb` (Google Colab: one cell per ledger predicate, any cell on its own, or *Runtime → Run all*, ≈ 20 s) or run whole.

Every check names the predicate(s) of the paper's predicate ledger it witnesses (Appendix A "Predicate ledger and machine verification", 20 predicates in blocks A–E, Y,
cited as `3:XN`; public copy `docs/3-causality/index.html`), and the ledger's source column links, for each
machine-verified predicate, the script at the check that decides it (`causality.py#<key>`) and the Lean module at the predicate's declaration
(`lean/FrcCore/Causality.lean` with no axioms, or `lean/FrcLedger/Causality.lean` on Mathlib). Where a predicate is proved in Lean (`lean/FrcCore/Causality.lean` with no axioms, or
`lean/FrcLedger/Causality.lean` on Mathlib), the check here is the instance the reader can run.

The package decides the dichotomy by counting: on the shell the form `Q_ν = −νt² + x² + y² + z²` has `p³ − p² + p`
zeros for a nonsquare `ν` (the elliptic, Witt-index-one class, the Lorentzian one) and `p³ + p² − p` for a square `ν`
(hyperbolic, Witt index two), with the isometry groups `O₄⁻(p)` and `O₄⁺(p)` of the orders the classification
predicts, by frame counting; over `K = F_{p²}` every element of `F_p` is a square and the form is hyperbolic — the
extension is where the dichotomy collapses. The boosts of the shell are the norm-one cycle of order `p + 1`; the
family `u = g^{Δm}` is the split torus over `K`.

Run: `python3 causality.py` (python ≥ 3.8, no third-party packages; ≈ 5 s; `results.json` written), or one block: `python3 causality.py C`; installed, `python3 -m frc_3_causality`.

| id | block | kind | claim | ledger predicate |
|---|---|---|---|---|
| `A1` | A | EXACT | two square classes of (p−1)/2; −1, c², −c² squares (c ≠ 0); no c with c² a nonsquare — p ∈ {5, 13, 17, 29, 37, 41} | `3:B2` |
| `A2` | A | EXACT | one square class ⇒ Q ≅ a₀·(sum of squares) by w_i² = a_i/a₀, all one-class coefficient tuples at 5, 13, 17; no root of a₀ exists for a₀ a nonsquare | `3:B3` |
| `A3` | A | EXACT | every primitive root is a nonsquare (ν = g canonical); Q_ν depends on ν only through its class | `3:B1` |
| `A4` | A | EXACT | −c²t² + x² + y² + z² (c ≠ 0) has p³ + p² − p zeros (hyperbolic); c = 0 is degenerate | `3:B2` |
| `B1` | B | EXACT | Q_ν has p³ − p² + p zeros (ν nonsquare) and p³ + p² − p (ν square), every ν, p ≤ 41 | `3:B4` |
| `B2` | B | EXACT | over F_{p²}: ν = c², every element of F_p a square, Q_ν hyperbolic — q³ + q² − q zeros (16 225 at q = 25), \|O\| = 2q²(q²−1)² | `3:B5` |
| `B3` | B | EXACT | \|O(Q_ν, F_p)\| = 2p²(p⁴−1) and \|O(Euclidean)\| = 2p²(p²−1)² by frame counting, p = 5, 13, 17 | `3:B6` |
| `B4` | B | EXACT | the null cone and the two non-null classes partition F_p⁴ with sizes p³−p²+p, (p−1)(p³+p)/2 each; invariant under reflections and rescaling | `3:B7` |
| `B5` | B | EXACT | x² − νt² anisotropic (ν nonsquare); y² + z² and x² − w²t² hyperbolic planes | `3:B5` |
| `C1` | C | EXACT | the boosts Λ(γ, b), γ² − νb² = 1, form the norm-one cycle of order p + 1, cyclic; each preserves Q_ν; Λ(z₁)Λ(z₂) = Λ(z₁z₂) | `3:C2` |
| `C2` | C | EXACT | SO(Q_ν, F_p) in 1+1 dimensions has p + 1 elements (ν nonsquare), p − 1 (ν square), all of the boost shape — exhaustive over the 2×2 matrices | `3:C2` |
| `C3` | C | EXACT | γ ≠ 0; v = −νb/γ; γ²(ν − v²) = ν; v₁₂ = (v₁ + v₂)/(1 + v₁v₂/ν) exactly, denominator never zero | `3:C3` |
| `C4` | C | EXACT | the family Λ(u), u = g^{Δm} ∈ F_p^×: a ∈ c·F_p, not in F_p for u ≠ ±1; preserves Q_ν over K; p − 1 matrices, the split torus | `3:C5` |
| `C5` | C | EXACT | at p = 5 the x-boosts and O(3, F_p) (order 240) generate O(Q_ν, F_5) = O₄⁻(5) of order 31 200 | `3:C4` |
| `D1` | D | EXACT | F₁₃: the classes, ν = 2 = g, X² − 2 irreducible, c = √2 ∉ F₁₃, 2041 null points, 14 boosts, 7 velocities | `3:D1` |
| `D2` | D | EXACT | the null cone of Q₂ on F₁₃ counted vector by vector: 2041 = 13³ − 13² + 13 | `3:D1` |

`results.json` carries one record per check (id, rows, block, script, kind, claim, PASS/FAIL, detail); the site generator
reads it to colour the witnesses on the public ledger page.

## One cell per predicate

`frc-3-causality.ipynb` (built by `make_notebook.py`, executed) carries one cell per witnessed ledger predicate, addressable by
its stable id (the predicate's accession key, e.g. `p03006` for `3:B2`; the ledger page opens the notebook at the cell). Every cell is self-contained: it installs the
package from the site (`pip install frc-3-causality --find-links https://finitering.space/pkg/` — a named requirement,
so pip reports it already satisfied once installed; the sdist `frc-3-causality-<version>.tar.gz` that `src/make_pkg.py`
writes under `docs/pkg/` at each site build; import name `frc_3_causality`, `__init__.py` exporting `predicate` and `verify_all`),
states the predicate and runs `predicate("3:B2")`: the block of the check that decides the predicate runs once per session (the
deciding check is `causality.PREDICATES`, the block the letter of its id), that check is printed from the script's own source — the line under its
`# 3:B2 (p03006)` marker — and every record citing the predicate is listed with its verdict (A4 corroborates B2, B5 corroborates B5, C2 corroborates C2, D2 corroborates D1). The markers in `causality.py`
are the lines the ledger page's source glyph opens (`docs/src/3-causality/#<key>`). The predicates'
Lean counterparts are the declarations named by their keys (`p03006`) at the end of `lean/FrcCore/Causality.lean` and `lean/FrcLedger/Causality.lean`
(`lean/make_predicates.py`), one per predicate, with the module as one executable file for the web editor (`lean/web/core/Causality.lean`, `lean/web/Causality.lean`).
