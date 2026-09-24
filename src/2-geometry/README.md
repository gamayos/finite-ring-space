# 2-geometry validation package

Validation package of *Geometry and Constants in Finite Ring Continuum* (Akhtman, Symmetry 2026, 18, 751),
`2-geometry` of the FRC corpus, added with the paper's predicate ledger (Appendix A, 17 September 2026) from the
corpus script `validation/verify_geometry.py`; one script since 24 September 2026. One script, `geometry.py`, four blocks, eighteen checks, standard library only, driven
by `frc-2-geometry.ipynb` (Google Colab: one cell per ledger predicate, any cell on its own, or *Runtime → Run all*, ≈ 10 s)
or run whole.

Every check names the predicate(s) of the paper's ledger it witnesses (Appendix A "Predicate ledger and machine
verification", 32 predicates in blocks A–F, T, cited as `2:XN`; public copy `docs/2-geometry/2-geometry-ledger.html`), and
the ledger's source column links, for each machine-verified predicate, the script at the check that decides it (`geometry.py#<key>`) and the Lean
module at the predicate's declaration (`lean/FrcCore/Geometry.lean` with no axioms — B4, C2–C4's in `lean/FrcCore/Complex.lean`,
which imports Geometry — or `lean/FrcLedger/Geometry.lean` on Mathlib); the check here is the instance the reader can
run; the two witnesses decide the same statements at different generality.

Run: `python3 geometry.py` (python ≥ 3.8, no third-party packages; ≈ 3 s; `results.json` written), or one block: `python3 geometry.py C`; installed, `python3 -m frc_2_geometry`.

| id | block | kind | claim | ledger predicate |
|---|---|---|---|---|
| `A1` | A | EXACT | g^π = −1, π = 2κ; i = −g^κ of order 4 with i² = −1; Q_p = {±1, ±i}; 2π = −1; e = g^i — every primitive g on p ∈ {5, 13, 17, 29, 37, 41} | `2:D1`–`2:D4` |
| `A2` | A | EXACT | the primitive generators are the g^u, u a unit mod p−1: one torsor | `2:B3` |
| `A3` | A | EXACT | orientation classes: i' = i iff u ≡ 1 (mod 4), i' = −i iff u ≡ 3 (mod 4) | `2:D5` |
| `A4` | A | EXACT | the Euler identity e^{iπ} = g^{2κ i²} = (−1)^i, −1 iff the residue i is odd; F₁₃ g = 2 (i = 5) oriented, F₁₇ g = 3 (i = 4) not | `2:D6` |
| `A5` | A | EXACT | negation and inversion commute; off Q_p their orbits have four elements, κ − 1 of them | `2:D7` |
| `A6` | A | EXACT | Euclidean conjugation is an involution of the coordinate pairs, not of the field (the pair map is p-to-one) | `2:D8` |
| `B1` | B | EXACT | cell counts of S_p (χ = 1) and of its completion (χ = 2), p ∈ {5, 13, 17, 29} | `2:C2` |
| `B2` | B | EXACT | the completion is a closed surface (every edge in two faces, every vertex link one cycle), S_p is not, p ≤ 29 | `2:C3` |
| `B3` | B | EXACT | ρ_u : m ↦ um is cellular iff u = ±1; the dihedral maps are; meridian reversal is a map of the completion only | `2:B4`, `2:C4` |
| `C1` | C | CHART | base-grid covering radius 0.360 at p = 13 within the bound √2 π/(p−1) = 0.370 | `2:E2` |
| `C2` | C | EXACT | the fixed-shell scale grid's covering radius in [0, 1] is ≥ ½ min(g^−m, 1 − 2κ g^−(m+1)) at every depth (exact rationals; six frames) | `2:E3` |
| `C2b` | C | EXACT | fixed-shell density at ε = 1/20: the covering radius exceeds 1/20 on every tested shell | `2:E3` |
| `C3` | C | CHART | the tower p = 13 … 4093 (g = 2) resolves every target within 1/2048; the single shell (13, 2) does not | `2:E4` |
| `D1` | D | EXACT | g is a principal n-th root of unity, n^−1 = −1 | `2:F1` |
| `D2` | D | EXACT | W^−1 = −(g^−jk) on (13, 2), (13, 11), (17, 3), (29, 2) | `2:F3` |
| `D3` | D | EXACT | the polynomial reading F(v)_k = P_v(g^k) | `2:F4` |
| `D4` | D | EXACT | covariance under g → g^u with v'_j = v_{uj} | `2:F5` |
| `D5` | D | CHART | the external transport χ(g^m) = e^{−2πim/n}: injective; step, half-period and quarter-turn identities | `2:F6` |

`results.json` carries one record per check (id, rows, block, script, kind, claim, PASS/FAIL, detail); the site generator
reads it to colour the witnesses on the public ledger page.

## One cell per predicate

`frc-2-geometry.ipynb` (built by `make_notebook.py`, executed) carries one cell per witnessed ledger predicate, addressable by
its stable id (the predicate's accession key, e.g. `p02013` for `2:D1`; the ledger page opens the notebook at the cell). Every cell is self-contained: it installs the
package from the site (`pip install frc-2-geometry --find-links https://finitering.space/pkg/` — a named requirement,
so pip reports it already satisfied once installed; the sdist `frc-2-geometry-<version>.tar.gz` that `src/make_pkg.py`
writes under `docs/pkg/` at each site build; import name `frc_2_geometry`, `__init__.py` exporting `predicate` and `verify_all`),
states the predicate and runs `predicate("2:D1")`: the block of the check that decides the predicate runs once per session (the
deciding check is `geometry.PREDICATES`, the block the letter of its id; a check deciding several predicates — A1 for D1–D4, B3 for B4 and C4 — carries them all
on one marker), that check is printed from the script's own source — the line under its `# 2:D1 (<key>)` marker — and every
record citing the predicate is listed with its verdict (C2b corroborates E3). The markers in `geometry.py` are the
lines the ledger page's source glyph opens (`docs/src/2-geometry/geometry.html#<key>`). The predicates' Lean
counterparts are the declarations named by their keys (`p02013`) at the end of `lean/FrcCore/Geometry.lean` (B4, C2, C3, C4's in
`lean/FrcCore/Complex.lean`, which imports Geometry) and `lean/FrcLedger/Geometry.lean` (`lean/make_predicates.py`), one per
predicate, with the modules as executable files for the web editor (`lean/web/core/Geometry.lean`, `lean/web/core/Complex.lean`,
`lean/web/Geometry.lean`).
