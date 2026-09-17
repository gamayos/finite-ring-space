# 2-geometry validation package

Validation package of *Geometry and Constants in Finite Ring Continuum* (Akhtman, Symmetry 2026, 18, 751),
`2-geometry` of the FRC corpus, added with the paper's predicate ledger (Appendix A, 17 September 2026) from the
corpus script `validation/verify_geometry.py`. Four block scripts, eighteen checks, standard library only, driven
by `2-geometry-main.ipynb` (Google Colab, *Runtime → Run all*, ≈ 30 s) or by `run_all.py`.

Every check names the row(s) of the paper's predicate ledger it witnesses (Appendix A, 34 rows in blocks A–F, V, O,
cited as `2:XN`; public copy `docs/2-geometry/2-geometry-ledger.html`), and the ledger's source column cites the
check ids in return. Where a row is proved in Lean (`lean/FrcLedger/Geometry.lean` on Mathlib, or `lean/FrcCore`
with no axioms, in this repository), the check here is the instance the reader can run; the witnesses decide the
same statements at different generality.

Run: `python3 run_all.py` (python ≥ 3.8, no third-party packages; ≈ 3 s). Each block also runs on its own.

| id | script | kind | claim | ledger row |
|---|---|---|---|---|
| `A1` | `a_datum.py` | EXACT | g^π = −1, π = 2κ; i = −g^κ of order 4 with i² = −1; Q_p = {±1, ±i}; 2π = −1; e = g^i — every primitive g on p ∈ {5, 13, 17, 29, 37, 41} | `2:D1`–`2:D4` |
| `A2` | `a_datum.py` | EXACT | the primitive generators are the g^u, u a unit mod p−1: one torsor | `2:B3` |
| `A3` | `a_datum.py` | EXACT | orientation classes: i' = i iff u ≡ 1 (mod 4), i' = −i iff u ≡ 3 (mod 4) | `2:D5` |
| `A4` | `a_datum.py` | EXACT | the Euler identity e^{iπ} = g^{2κ i²} = (−1)^i, −1 iff the residue i is odd; F₁₃ g = 2 (i = 5) oriented, F₁₇ g = 3 (i = 4) not | `2:D6` |
| `A5` | `a_datum.py` | EXACT | negation and inversion commute; off Q_p their orbits have four elements, κ − 1 of them | `2:D7` |
| `A6` | `a_datum.py` | EXACT | Euclidean conjugation is an involution of the coordinate pairs, not of the field (the pair map is p-to-one) | `2:D8` |
| `B1` | `b_shell.py` | EXACT | cell counts of S_p (χ = 1) and of its completion (χ = 2), p ∈ {5, 13, 17, 29} | `2:C2` |
| `B2` | `b_shell.py` | EXACT | the completion is a closed surface (every edge in two faces, every vertex link one cycle), S_p is not, p ≤ 29 | `2:C3` |
| `B3` | `b_shell.py` | EXACT | ρ_u : m ↦ um is cellular iff u = ±1; the dihedral maps are; meridian reversal is a map of the completion only | `2:B4`, `2:C4` |
| `C1` | `c_charts.py` | CHART | base-grid covering radius 0.360 at p = 13 within the bound √2 π/(p−1) = 0.370 | `2:E2` |
| `C2` | `c_charts.py` | EXACT | the fixed-shell scale grid's covering radius in [0, 1] is ≥ ½ min(g^−m, 1 − 2κ g^−(m+1)) at every depth (exact rationals; six frames) | `2:E3` |
| `C2b` | `c_charts.py` | EXACT | fixed-shell density at ε = 1/20: the covering radius exceeds 1/20 on every tested shell | `2:E3` |
| `C3` | `c_charts.py` | CHART | the tower p = 13 … 4093 (g = 2) resolves every target within 1/2048; the single shell (13, 2) does not | `2:E4` |
| `D1` | `d_fourier.py` | EXACT | g is a principal n-th root of unity, n^−1 = −1 | `2:F1` |
| `D2` | `d_fourier.py` | EXACT | W^−1 = −(g^−jk) on (13, 2), (13, 11), (17, 3), (29, 2) | `2:F3` |
| `D3` | `d_fourier.py` | EXACT | the polynomial reading F(v)_k = P_v(g^k) | `2:F4` |
| `D4` | `d_fourier.py` | EXACT | covariance under g → g^u with v'_j = v_{uj} | `2:F5` |
| `D5` | `d_fourier.py` | CHART | the external transport χ(g^m) = e^{−2πim/n}: injective; step, half-period and quarter-turn identities | `2:F6` |

`results.json` carries one record per check (id, rows, script, kind, claim, PASS/FAIL, detail); the site generator
reads it to colour the witnesses on the public ledger page.
