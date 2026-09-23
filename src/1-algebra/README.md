# 1-algebra validation package

Validation package of *Relativistic Algebra over Finite Ring Continuum* (Akhtman, Axioms 2025, 14, 636,
doi 10.3390/axioms14080636), `1-algebra` of the FRC corpus, added with the paper's predicate ledger
(Appendix A, 16 September 2026). Three block scripts, sixteen checks, standard library only, driven by
`frc-1-algebra.ipynb` (Google Colab: one cell per ledger predicate, any cell on its own, or *Runtime → Run all*, ≈ 45 s) or by `run_all.py`.

Every check names the predicate of the paper's predicate ledger it witnesses (Appendix A "Predicate ledger and machine verification", 27 predicates in blocks A–G, Y,
cited as `1:XN`; public copy `docs/1-algebra/1-algebra-ledger.html`), and the ledger's source column links, for each
machine-verified predicate, the script at the check that decides it and the Lean module at the predicate's declaration
(`lean/FrcCore/Algebra.lean` with no axioms — G5's in `lean/FrcCore/Quaternion.lean` — or `lean/FrcLedger/Algebra.lean` on Mathlib);
the check here is the instance the reader can run; the two witnesses decide the same statements at different generality.

Run: `python3 run_all.py` (python ≥ 3.8, no third-party packages; ≈ 45 s). Each block also runs on its own.

| id | script | kind | claim | ledger predicate |
|---|---|---|---|---|
| `A1` | `a_shell.py` | EXACT | Q₄ = {1, i, −1, −i} the unique order-4 subgroup; under the Klein four-group, two orbits of size 2 and κ−1 orbits of size 4; no i for p ≡ 3 (mod 4) — p ∈ {5, 13, 17, 29, 37, 41, 173}, controls {7, 11, 19, 23} | `1:B2` |
| `A2` | `a_shell.py` | EXACT | i = −g^κ, i² = −1 for every primitive root; {−g^κ, g^κ} the two square roots of −1; g^{2κ} = −1; F₁₃, g = 2: i = 5 | `1:B3` |
| `A3` | `a_shell.py` | EXACT | φ_{a,b} = a + bx a ring isomorphism onto (F_p, ⊕, ⊗) on all 428 frames of F₁₃, F₁₇; unit a + b; b the unit iff a = 0 | `1:B4` |
| `A4` | `a_shell.py` | EXACT | ⟨T_a, S_m⟩ = Aff(F_p) of order p(p−1), simply transitive on the frames (every pair of frames, one carrier) | `1:C2` |
| `A5` | `a_shell.py` | EXACT | M_n(a) = M_{n+2κ}(−a), L_a(m) = L_{−a}(m+2κ); p−1 meridian lists in 2κ great circles; 2κ latitude pairs; \|V\| = (p−1)²/2 + 1 | `1:C4` |
| `B1` | `b_numbers.py` | EXACT | the window law: injective iff 2H < p; sums read back iff 4H < p; products whenever 2H² < p — every H on p ∈ {13, 17, 29} | `1:D2` |
| `B2` | `b_numbers.py` | EXACT | G_n = (x g^{−n})_x is (p−1)-periodic in the field with exact period p−1; the rational grids x/gⁿ are not periodic | `1:D4` |
| `B3` | `b_numbers.py` | CHART | \|r\| ≤ H g^{−n} ⇒ some x/gⁿ, x ∈ W_H, within 1/(2gⁿ) (exact rationals); at (13, 2) no point of step ≤ 1/8 within 1/16 of r = 33/10: range and resolution trade off at fixed window | `1:D6` |
| `B4` | `b_numbers.py` | EXACT | F_p[X]/(X²+1) has zero divisors on the shell; a field exactly when p ≡ 3 (mod 4) (exhaustive at 7, 11, 19, 23) | `1:E2` |
| `B5` | `b_numbers.py` | EXACT | 2s = 0 ⇒ s = 0 for every odd prime < 200; 2⁻¹ = 2κ + 1 on the shell | `1:F1` |
| `B6` | `b_numbers.py` | EXACT | the Euclidean step count against ⌊log₂ p⌋+1: (55, 34) needs 7 > 6 at p = 59, (987, 610) needs 13 > 10 at p = 1009; F₄ = 3 < 4 | — (a check of the package, no ledger predicate) |
| `C1` | `c_conjecture.py` | EXACT | f ∈ F_p[X] has a root iff gcd(f, X^p − X) ≠ 1, and deg gcd = the number of distinct roots — every monic polynomial of degree ≤ 3 over F₁₃ and F₁₇ | `1:G1` |
| `C2` | `c_conjecture.py` | CHART | for r ∈ {π, e, √2, 33/10, 1/3} and ε = 10⁻²..10⁻⁸ a shell p = 4κ+1 carries x/2ⁿ, \|x\| ≤ 2κ, within ε of r (exact rationals) | `1:G2` |
| `C3` | `c_conjecture.py` | CHART | k(θ) = ⌊Nθ/2π + ½⌋, N = p−1: angle and chord error ≤ π/N, group-law defect ≤ 1, on every shell | `1:G3` |
| `C4` | `c_conjecture.py` | CHART | covering radii in SO(3): tetrahedral π/2, octahedral arccos((2√2−1)/4) ≈ 62.8°, icosahedral ε₀ = arccos((3√5−1)/8) ≈ 44.48°, cyclic/dihedral ≥ π/2 — no finite subgroup is an ε-net for ε < ε₀ | `1:G4` |
| `C5` | `c_conjecture.py` | CHART | the normalised window quaternions W_H⁴ are a 2·arcsin(1/H)-net of SO(3) (H = 1, 2, 3; measured 60.8°, 41.0°, 30.0°), 38.9° < ε₀ at H = 3; their products read back exactly from F₇₃ (8H² < p) | `1:G5` |

`results.json` carries one record per check (id, rows, script, kind, claim, PASS/FAIL, detail); the site generator
reads it to colour the witnesses on the public ledger page.

## One cell per predicate

`frc-1-algebra.ipynb` (built by `make_notebook.py`, executed) carries one cell per witnessed ledger predicate, addressable by
its stable id (the predicate's accession key, e.g. `p01004` for `1:B2`; the ledger page opens the notebook at the cell). Every cell is self-contained: it installs the
package from the site (`pip install frc-1-algebra --find-links https://finitering.space/pkg/` — a named requirement,
so pip reports it already satisfied once installed; the sdist `frc-1-algebra-<version>.tar.gz` that `src/make_pkg.py`
writes under `docs/pkg/` at each site build; import name `frc_1_algebra`, `__init__.py` exporting `predicate` and `verify_all`),
states the predicate and runs `predicate("1:B2")`: the block script of the check that decides the predicate runs once per session (the
deciding check is `algcommon.PREDICATES`), that check is printed from the script's own source — the line under its
`# predicate 1:B2` marker — and every record citing the predicate is listed with its verdict. The markers in the three block
scripts are the lines the ledger page's source glyph opens (`docs/src/1-algebra/<script>.html#<key>`). The predicates'
Lean counterparts are the declarations named by their keys (`p01004`) at the end of `lean/FrcCore/Algebra.lean` (G5's in
`lean/FrcCore/Quaternion.lean`, which imports Algebra) and `lean/FrcLedger/Algebra.lean` (`lean/make_predicates.py`), one per
predicate, with the module as one executable file for the web editor (`lean/web/core/Algebra.lean`, `lean/web/Algebra.lean`).
