# 6-fourier validation package

Validation package of *Scale-Shift and Fractional Fourier Transform as Rotations over Finite Holographic
Substrate* (Akhtman, 2026; doi 10.20944/preprints202606.0127.v1), `6-fourier` of the FRC corpus, added with the paper's
predicate ledger (13 September 2026; one script since 24 September 2026; the entropy block retired with the revision of 9 October
2026, kept in `_to_delete/fourier-pre-rewrite-20261009.py` and described in the paper's `reports/entropy-20261008.md`). One script,
`fourier.py`, four blocks, thirty-one checks, numpy, driven by `frc-6-fourier.ipynb` (Google Colab: one cell per ledger predicate,
any cell on its own, or *Runtime → Run all*, ≈ 10 s) or run whole.

Every check names the predicate(s) of the paper's predicate ledger it witnesses (Appendix A "Predicate ledger and machine
verification", 39 predicates in blocks A–E, cited as `6:XN`; public copy `docs/6-fourier/index.html`), and the ledger's
source column links, for each machine-verified predicate, the script at the check that decides it (`fourier.py#<key>`) and the
Lean module at the predicate's declaration (`lean/FrcCore/Fourier.lean` with no axioms, or `lean/FrcLedger/Fourier.lean` on
Mathlib); the check here is the instance the reader can run; the two witnesses decide the same statements at different
generality. Three master-ledger predicates of the corpus are reached through the paper's (`00:C2`, `00:C14`, `00:C7`).

Run: `python3 fourier.py` (python ≥ 3.9, numpy; ≈ 5 s; `results.json` written), or one block: `python3 fourier.py D`;
installed, `python3 -m frc_6_fourier`.

## The blocks

| block | class | checks | claims backed |
|---|---|---|---|
| A | EXACT | 6/6 | the frame datum p = 4κ+1, i = −g^κ, π = 2κ, e = g^i and Table `tab:checks` (A1); the Euler identity e^{iπ} ≡ −1 exactly on the odd quarter-turn, toggled by the conjugate reframing, on every primitive frame (Remark `euler`, **00:C14**, A2); the u-relabelling of Remark `gt-covariance` with the p = 13, u = 5 instance (A3); W² = −J, (iW)² = J, (iW)⁴ = I (Lemma `W-square`, Proposition `F-cycle`, **00:C2**, A4); ±i the unitary normalisations (Remark `unitary-norm`, A5); the J-decomposition dimensions 2κ±1 (Lemma `JF-decomp`, A6) |
| B | EXACT | 10/10 | the projector idempotents (Lemma `projectors`, B1); additivity on all 4096 pairs and the cardinal values (Theorem `FRC-FrFT`, **00:C2**, B2–B3); faithfulness (Theorem `faithful`, B4); the multiplicity sums (Lemma `multiplicity`, B5); multiplicities as chart data, (3,3,4,2) vs (4,2,3,3) at p = 13 and the permutation conjugacy F(g) ~ F(g^{u²}) (Remark `multiplicities`, B6); the dichotomy G = ε(1+i) with both patterns, the conjugate and Jacobi laws and the even split on all 38 primitive frames of p ∈ {5,13,17,29,37} plus the 16 of p = 41 (Theorem `multiplicity`, B7) and the proof's identities G G* = −2, G² = 2i, the traces (B8); the exponent lifts and the non-commuting charts u² ≢ 1 (mod 4κ) of the six shells, p = 29, u = 5 first (Remark `classification`, B9); the conjugate frame: relations, cardinal values, faithfulness kept, the tuple flipped, F' = −F⁻¹, Π'_ℓ = Π_{ℓ+2} (Remark `gt-covariance`, **00:C7** on the transform layer, B10) |
| C | EXACT | 6/6 | invertibility (Definition `domain`, C1); the 4κ distinct framed bases (Theorem `faithful`, C2); exactly 2κ unordered bases by parity, no further coincidence (Remark `ordered-bases`, C3); S_r(M_m) = M_{m+r} on all pairs (Proposition `meridian-scale`, **00:C2**, C4); the effective step and the (p−1)-periodicity (Corollary `effective-step`, C5); the p = 13 ladder and the no-wrap window (Section 7, Definition `scale-chart`, C6) |
| D | EXACT | 9/9 | R_s ∈ SO(2, F_p) (Proposition `rotation-isom`, D1); the isomorphism Z_{4κ} ≅ SO(2, F_p) (Proposition `rotation-isom`, D2); the cardinal values R_0, R_κ, R_{2κ}, R_{3κ} and z_κ = i (Theorem `Weil-equivalence`, D3); the spectral obstruction (Proposition `nogo`, D4); the common character sector (Proposition `charsector`, D5); the cardinal Heisenberg covariance and the expansion of F^[s] in the powers of F (Proposition `heisenberg`, D6); monomiality exactly at the cardinal indices on the six shells, the 112 intermediate indices of the sweep (Theorem `monomial`, D7); cardinal exclusivity on every shell below 200 by the row-0 argument (Theorem `monomial`, D8); the plane as its origin and n+2 free orbits of the rotation group, dim V = n (Corollary `boundary`, D9) |
| `make_f13_C_figure.py` | figure | — | the framed complex-plane rendering of F_13 (`f13-C-check.png`), a drawing cross-checked against the manuscript figure; not a computation, kept from the paper's `code/` |

Blocks A–D are exact modular arithmetic on the six shells of Table `tab:checks` (p = 5, 13, 17, 29, 37, 41; D8 on every shell p ≡ 1 (mod 4) below 200),
over every primitive frame where a statement ranges over frames.

## The checks

| id | block | kind | claim | ledger predicate |
|---|---|---|---|---|
| `A1` | A | EXACT | p = 4κ+1, g the smallest primitive root, i = −g^κ = g^{−κ}, i² ≡ −1, π = 2κ, 2π ≡ −1, g^π ≡ −1, −π ≡ 2⁻¹, e = g^i; Table tab:checks (κ, g, i) | `6:B1` |
| `A2` | A | EXACT | e^{iπ} = g^{2κ(i mod 2)} ≡ −1 exactly on the odd quarter-turn; the conjugate reframing toggles it, one member of each pair carries it | `6:B2` |
| `A3` | A | EXACT | g' = g^u: the quarter-turn flips only on u ≡ 3 (mod 4); e' = g^{ui} ≠ e iff i(u−1) ≢ 0 (mod 4κ); at p = 13, u = 5: e' = 2 ≠ 6 | `6:B3` |
| `A4` | A | EXACT | W² = −J, (iW)² = J, (iW)⁴ = I on the six shells of Table tab:checks | `6:B5` |
| `A5` | A | EXACT | the square roots of 1/n ≡ −1 in F_p are exactly ±i, the two unitary normalisations of W: (cW)² = J iff c = ±i | `6:B6` |
| `A6` | A | EXACT | WJ = JW, FJ = JF; dim V⁺ = 2κ+1, dim V⁻ = 2κ−1 | `6:B7` |
| `B1` | B | EXACT | Π_ℓ² = Π_ℓ, Π_ℓ Π_m = 0, Σ Π_ℓ = I, F Π_ℓ = i^ℓ Π_ℓ | `6:C2` |
| `B2` | B | EXACT | F^[s+r] = F^[s] F^[r] on every pair (s, r) of Z_{4κ} | `6:C3` |
| `B3` | B | EXACT | F^[0] = I, F^[κ] = F, F^[2κ] = J, F^[3κ] = F⁻¹, F^[4κ] = I; (F^[1])^κ = F | `6:C3` |
| `B4` | B | EXACT | s ↦ F^[s] is injective on Z_{4κ}: the 4κ members are pairwise distinct (p = 5 included) | `6:C4` |
| `B5` | B | EXACT | Π_0+Π_2 = ½(I+J), Π_1+Π_3 = ½(I−J); (Π_0)_{00}, (Π_2)_{00} ≠ 0; κ ≥ 2: (Π_1)_{21} = ¼(g²−g⁻²) = −(Π_3)_{21} ≠ 0; m_ℓ = rank Π_ℓ = dim ker(F − i^ℓ I), m_0+m_2 = 2κ+1, m_1+m_3 = 2κ−1; p = 5: one odd projector vanishes | `6:C5` |
| `B6` | B | EXACT | p = 13: g = 2 gives (3,3,4,2), Tr F = 4; g = 6 gives (4,2,3,3), Tr F = 9; m ↦ um carries F(g) to F(g^{u²}) by a permutation | `6:C6` |
| `B7` | B | EXACT | G = ε(1+i), the two patterns, ε(g⁻¹) = −ε(g); 38 frames of p ∈ {5,…,37} and 16 of p = 41; the table frames with κ ≥ 2 in class ε = +1; p = 5: (2,0,1,1) at g = 2, (1,1,2,0) at g = 3 | `6:C7` |
| `B8` | B | EXACT | G G* = −2, G² = 2i, Tr F = iG, Tr F² = 2, Tr F³ = iG*, m_ℓ ≡ ¼ Σ_r i^{−ℓr} Tr F^r (mod p) | `6:C7` |
| `B9` | B | EXACT | exponent lifts a_ℓ ≡ ℓ (mod 4) are additive with the cardinal skeleton (p = 13); the chart g^5 at p = 29 (u² ≢ 1 mod 28) does not commute with F, nor does any chart with u² ≢ 1 (mod 4κ) on the six shells | `6:C8`, `6:C11` |
| `B10` | B | EXACT | the conjugate frame (g⁻¹, −i) keeps the operator relations, cardinal values, additivity and faithfulness; its multiplicity tuple is the other pattern; F' = −F⁻¹, Π'_ℓ = Π_{ℓ+2} | `6:C9` |
| `C1` | C | EXACT | every F^[s] has full rank 4κ over F_p; the eigenvalues g^{−ℓs} are nonzero | `6:D1` |
| `C2` | C | EXACT | the 4κ framed bases B_s = F^[s] B_0 are pairwise distinct | `6:D2` |
| `C3` | C | EXACT | F^[s+2κ] = F^[s] J, so B_{s+2κ} = B_s as unordered bases, and B_{s+t} ≠ B_s for t ∉ {0,2κ}: every off-site entry of row 0 of F^[t] is (i/2)(1 − g^{−2t}) ≠ 0, F^[t] not monomial — 4κ framed domains, exactly 2κ measurement bases | `6:D2`, `6:D7` |
| `C4` | C | EXACT | S_r(M_m) = M_{m+r} on every (m, r), as ordered lists | `6:D4` |
| `C5` | C | EXACT | consecutive entries of M_m differ by the effective step g^m; S_{r+(p−1)} = S_r | `6:D4` |
| `C6` | C | EXACT | p = 13, g = 2: M_0…M_3 = the printed ladder at steps 1, 2, 4, 8; the no-wrap window w·g^r < p with w = π = 6 holds for r ≤ 1 and the listing wraps from M_2 | `6:D4` |
| `D1` | D | EXACT | c_s² + d_s² = 1, det R_s = 1: R_s ∈ SO(2, F_p) for every s | `6:E2` |
| `D2` | D | EXACT | R_{s+r} = R_s R_r, s ↦ R_s injective, \|SO(2, F_p)\| = p−1 = 4κ: an isomorphism | `6:E2` |
| `D3` | D | EXACT | R_0 = I, R_κ = [[0,−1],[1,0]] (Table tab:checks), R_{2κ} = −I, R_{3κ} = w⁻¹; z_κ = g^{−κ} = i | `6:E3` |
| `D4` | D | EXACT | σ has the 4κ simple eigenvalues F_p^×; F^[1] has at most four; for κ ≥ 2 ⟨σ⟩ and ⟨F^[1]⟩ are not conjugate | `6:E5`, `6:E9` |
| `D5` | D | EXACT | E_1 ≠ 0 for κ ≥ 2; F^[s] = g^{−s} on E_1; F^[s] T_v = T_v S_{−s} on every x and s; R_s (1,−i)ᵀ = g^{−s} (1,−i)ᵀ | `6:E6` |
| `D6` | D | EXACT | F σ F⁻¹ = D_1, F D_1 F⁻¹ = σ⁻¹; F^r σ = σ_r F^r with (σ, D_1, σ⁻¹, D_1⁻¹); F^[s] = Σ_r c_r(s) F^r, c_r(s) = ¼ Σ_ℓ (g^{rκ−s})^ℓ | `6:E7` |
| `D7` | D | EXACT | on the six shells F^[s] σ F^[s]⁻¹ is monomial exactly at the four cardinal indices: the 112 intermediate indices of p ∈ {13,17,29,37,41} all non-monomial (E8 on Table tab:checks) | `6:E8` |
| `D8` | D | EXACT | cardinal exclusivity (thm:monomial): row 0 of F^[s] σ F^[s]⁻¹ is x⁻¹ times a quadratic in x = g^j off j ∈ {−1,0,1}, leading coefficient i(c₀+c₂)c₃(−s) ≠ 0, at least 4κ−5 nonzero entries for every non-cardinal s, every shell p ≡ 1 (mod 4) below 200 | `6:E8` |
| `D9` | D | EXACT | the plane as orbits of the cycle (cor:boundary): \|SO(2,F_p)\| = n = p−1 and it is {R_s}; F_p² = the origin + (n+2) free orbits (n circles of nonzero norm, two isotropic lines y = ±ix), p² = 1+(n+2)n; (u,v) ↦ (z_s u, z_s⁻¹ v); dim V = n | `6:E10` |

`results.json` carries one record per check (id, rows, block, script, kind, claim, PASS/FAIL, detail); the site generator
reads it to colour the witnesses on the public ledger page.

## One cell per predicate

`frc-6-fourier.ipynb` (built by `make_notebook.py`, executed) carries one cell per witnessed ledger predicate, addressable by
its stable id (the predicate's accession key, e.g. `p06017` for `6:C3`; the ledger page opens the notebook at the cell). Every cell is self-contained: it installs the
package from the site (`pip install frc-6-fourier --find-links https://finitering.space/pkg/` — a named requirement,
so pip reports it already satisfied once installed; the sdist `frc-6-fourier-<version>.tar.gz` that `src/make_pkg.py`
writes under `docs/pkg/` at each site build, declaring numpy; import name `frc_6_fourier`, `__init__.py` exporting `predicate` and `verify_all`),
states the predicate and runs `predicate("6:C3")`: the block of the check that decides the predicate runs once per session (the
deciding check is `fourier.PREDICATES`, the block the letter of its id), that check is printed from the script's own source — the line under its
`# 6:C3 (<key>)` marker — and every record citing the predicate is listed with its verdict. The markers in `fourier.py`
are the lines the ledger page's source glyph opens (`docs/src/6-fourier/#<key>`). The predicates'
Lean counterparts are the declarations named by their keys (`p06017`) at the end of `lean/FrcCore/Fourier.lean` (twenty-six, no axioms:
the twenty-five theorem rows and D1, conjunctions of theorems of the frame and fourier themes) and `lean/FrcLedger/Fourier.lean` (fifteen, Mathlib),
one per predicate (`lean/make_predicates.py`), with the module as one executable file for Lean Live (`lean/web/core/Fourier.lean`, `lean/web/ml/Fourier.lean`).
