# 1-algebra validation package

Validation package of *Relativistic Algebra over Finite Ring Continuum* (Akhtman, Axioms 2025, 14, 636,
doi 10.3390/axioms14080636), `1-algebra` of the FRC corpus, added with the paper's predicate ledger
(Appendix A, 16 September 2026). Two block scripts, eleven checks, standard library only, driven by
`1-algebra-main.ipynb` (Google Colab, *Runtime → Run all*, ≈ 10 s) or by `run_all.py`.

Every check names the row of the paper's predicate ledger it witnesses (Appendix A, 24 rows in blocks A–F, V, O,
cited as `1:XN`; public copy `docs/1-algebra/1-algebra-ledger.html`), and the ledger's source column cites the check
ids in return. Where a row is proved in Lean for every shell (`reports/lean/Algebra.lean` in the corpus tree), the
check here is the instance the reader can run; the two witnesses decide the same statements at different generality.

Run: `python3 run_all.py` (python ≥ 3.8, no third-party packages; ≈ 5 s). Each block also runs on its own.

| id | script | kind | claim | ledger row |
|---|---|---|---|---|
| `A1` | `a_shell.py` | EXACT | Q₄ = {1, i, −1, −i} the unique order-4 subgroup; under the Klein four-group, two orbits of size 2 and κ−1 orbits of size 4; no i for p ≡ 3 (mod 4) — p ∈ {5, 13, 17, 29, 37, 41, 173}, controls {7, 11, 19, 23} | `1:B2` |
| `A2` | `a_shell.py` | EXACT | i = −g^κ, i² = −1 for every primitive root; {−g^κ, g^κ} the two square roots of −1; g^{2κ} = −1; F₁₃, g = 2: i = 5 | `1:B3` |
| `A3` | `a_shell.py` | EXACT | φ_{a,b} = a + bx a ring isomorphism onto (F_p, ⊕, ⊗) on all 428 frames of F₁₃, F₁₇; unit a + b; b the unit iff a = 0 | `1:B4` |
| `A4` | `a_shell.py` | EXACT | ⟨T_a, S_m⟩ = Aff(F_p) of order p(p−1), simply transitive on the frames (every pair of frames, one carrier) | `1:C2` |
| `A5` | `a_shell.py` | EXACT | M_n(a) = M_{n+2κ}(−a), L_a(m) = L_{−a}(m+2κ); p−1 meridian lists in 2κ great circles; 2κ latitude pairs; \|V\| = (p−1)²/2 + 1 | `1:C4` |
| `B1` | `b_numbers.py` | EXACT | the window law: injective iff 2H < p; sums read back iff 4H < p; products whenever 2H² < p — every H on p ∈ {13, 17, 29} | `1:D2` |
| `B2` | `b_numbers.py` | EXACT | G_n = (x g^{−n})_x is (p−1)-periodic in the field with exact period p−1; the rational grids x/gⁿ are not periodic | `1:D4` |
| `B3` | `b_numbers.py` | CHART | \|r\| ≤ H g^{−n} ⇒ some x/gⁿ, x ∈ W_H, within 1/(2gⁿ) (exact rationals); the published Theorem 2 fails at (13, 2), r = 33/10, k = 3 | `1:D5` |
| `B4` | `b_numbers.py` | EXACT | F_p[X]/(X²+1) has zero divisors on the shell; a field exactly when p ≡ 3 (mod 4) (exhaustive at 7, 11, 19, 23) | `1:E2` |
| `B5` | `b_numbers.py` | EXACT | 2s = 0 ⇒ s = 0 for every odd prime < 200; 2⁻¹ = 2κ + 1 on the shell | `1:F1` |
| `B6` | `b_numbers.py` | EXACT | the published Lemma 3 refuted: (55, 34) needs 7 > 6 at p = 59, (987, 610) needs 13 > 10 at p = 1009; F₄ = 3 < 4 | `1:V1` |

`results.json` carries one record per check (id, rows, script, kind, claim, PASS/FAIL, detail); the site generator
reads it to colour the witnesses on the public ledger page.
