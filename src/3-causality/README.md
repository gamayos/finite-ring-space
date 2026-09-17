# 3-causality validation package

Validation package of *Euclidean–Lorentzian Dichotomy and Algebraic Causality in Finite Ring Continuum* (Akhtman,
Entropy 2025, 27, 1098), `3-causality` of the FRC corpus, added with the paper's predicate ledger (Appendix A,
17 September 2026). Four block scripts, sixteen exact checks, standard library only, driven by
`3-causality-main.ipynb` (Google Colab, *Runtime → Run all*, ≈ 30 s) or by `run_all.py`.

Every check names the row(s) of the paper's predicate ledger it witnesses (Appendix A, 22 rows in blocks A–E, V, O,
cited as `3:XN`; public copy `docs/3-causality/3-causality-ledger.html`), and the ledger's source column cites the
check ids in return. Where a row is proved in Lean (`lean/FrcCore/Causality.lean` with no axioms, or
`lean/FrcLedger/Causality.lean` on Mathlib), the check here is the instance the reader can run.

The package decides the dichotomy by counting: on the shell the form `Q_ν = −νt² + x² + y² + z²` has `p³ − p² + p`
zeros for a nonsquare `ν` (the elliptic, Witt-index-one class, the Lorentzian one) and `p³ + p² − p` for a square `ν`
(hyperbolic, Witt index two), with the isometry groups `O₄⁻(p)` and `O₄⁺(p)` of the orders the classification
predicts, by frame counting; over `K = F_{p²}` every element of `F_p` is a square and the form is hyperbolic — the
extension is where the dichotomy collapses. The boosts of the shell are the norm-one cycle of order `p + 1`; the
printed parametrisation `u = g^{Δm}` lives over `K`.

Run: `python3 run_all.py` (python ≥ 3.8, no third-party packages; ≈ 5 s). Each block also runs on its own.

| id | script | kind | claim | ledger row |
|---|---|---|---|---|
| `A1` | `a_classes.py` | EXACT | two square classes of (p−1)/2; −1, c², −c² squares (c ≠ 0); no c with c² a nonsquare — p ∈ {5, 13, 17, 29, 37, 41} | `3:B2` |
| `A2` | `a_classes.py` | EXACT | one square class ⇒ Q ≅ a₀·(sum of squares) by w_i² = a_i/a₀, all one-class coefficient tuples at 5, 13, 17; the printed √a₀ step fails on nonsquares | `3:B3` |
| `A3` | `a_classes.py` | EXACT | every primitive root is a nonsquare (ν = g canonical); Q_ν depends on ν only through its class | `3:B1` |
| `A4` | `a_classes.py` | EXACT | −c²t² + x² + y² + z² (c ≠ 0) has p³ + p² − p zeros (hyperbolic); c = 0 is degenerate | `3:B2` |
| `B1` | `b_signature.py` | EXACT | Q_ν has p³ − p² + p zeros (ν nonsquare) and p³ + p² − p (ν square), every ν, p ≤ 41 | `3:B4` |
| `B2` | `b_signature.py` | EXACT | over F_{p²}: ν = c², every element of F_p a square, Q_ν hyperbolic — q³ + q² − q zeros (16 225 at q = 25), \|O\| = 2q²(q²−1)² | `3:B5` |
| `B3` | `b_signature.py` | EXACT | \|O(Q_ν, F_p)\| = 2p²(p⁴−1) and \|O(Euclidean)\| = 2p²(p²−1)² by frame counting, p = 5, 13, 17 | `3:B6` |
| `B4` | `b_signature.py` | EXACT | the null cone and the two non-null classes partition F_p⁴ with sizes p³−p²+p, (p−1)(p³+p)/2 each; invariant under reflections and rescaling | `3:B7` |
| `B5` | `b_signature.py` | EXACT | x² − νt² anisotropic (ν nonsquare); y² + z² and x² − w²t² hyperbolic planes | `3:B5` |
| `C1` | `c_boost.py` | EXACT | the boosts Λ(γ, b), γ² − νb² = 1, form the norm-one cycle of order p + 1, cyclic; each preserves Q_ν; Λ(z₁)Λ(z₂) = Λ(z₁z₂) | `3:C2` |
| `C2` | `c_boost.py` | EXACT | SO(Q_ν, F_p) in 1+1 dimensions has p + 1 elements (ν nonsquare), p − 1 (ν square), all of the boost shape — exhaustive over the 2×2 matrices | `3:C2` |
| `C3` | `c_boost.py` | EXACT | γ ≠ 0; v = −νb/γ; γ²(ν − v²) = ν; v₁₂ = (v₁ + v₂)/(1 + v₁v₂/ν) exactly, denominator never zero | `3:C3` |
| `C4` | `c_boost.py` | EXACT | the printed Λ(u), u = g^{Δm}: a ∈ c·F_p, not in F_p for u ≠ ±1; preserves Q_ν over K; p − 1 matrices, the split torus | `3:C5` |
| `C5` | `c_boost.py` | EXACT | at p = 5 the x-boosts and O(3, F_p) (order 240) generate O(Q_ν, F_5) = O₄⁻(5) of order 31 200 | `3:C4` |
| `D1` | `d_example.py` | EXACT | F₁₃: the classes, ν = 2 = g, X² − 2 irreducible, c = √2 ∉ F₁₃, 2041 null points, 14 boosts, 7 velocities | `3:D1` |
| `D2` | `d_example.py` | EXACT | the null cone of Q₂ on F₁₃ counted vector by vector: 2041 = 13³ − 13² + 13 | `3:D1` |

`results.json` carries one record per check (id, rows, script, kind, claim, PASS/FAIL, detail); the site generator
reads it to colour the witnesses on the public ledger page.
