# 5-reductio validation package

Validation package of *Paradoxes of Infinity as Reductio ad Absurdum* (Akhtman, preprint 2026), `5-red` of the FRC
corpus, added with the paper's predicate ledger (Appendix B, 17 September 2026; one script since 24 September 2026). One script, `reductio.py`, four blocks, seventeen
checks (all exact), standard library only, driven by `frc-5-reductio.ipynb` (Google Colab: one cell per ledger predicate, any cell on its own, or *Runtime → Run all*,
≈ 1 min) or run whole.

Every check names the predicate(s) of the paper's predicate ledger it witnesses (Appendix B "Predicate ledger and machine verification", 38 predicates in blocks A–F, T, cited as
`5:XN`; public copy `docs/5-reductio/index.html`), and the ledger's source column links, for each
machine-verified predicate, the script at the check that decides it (`reductio.py#<key>`) and the Lean module at the predicate's declaration
(`lean/FrcCore/Reductio.lean` with no axioms, or `lean/FrcLedger/Reductio.lean` on Mathlib). Where a predicate is proved in Lean (`lean/FrcCore/Reductio.lean` with no axioms, or `lean/FrcLedger/Reductio.lean`
on Mathlib), the check here is the instance the reader can run.

The package decides the paper's logic on the bounded universe it is about. The arithmetic frames `W_N` of
Section 2 are built as finite structures and their theories decided by evaluation: every sentence of a sample is
decided in every frame, the categorical sentence `σ_N` has exactly the `N!` copies of `W_N` as models, no finite
structure carries a successor map that is injective and misses `0` (so no `Th(W_N)` interprets `Q`), and the
bounded-stability schema is run on the Δ₀ language of the core module with its computed bound `t(φ)` — the worked
Goldbach instance below 20 has the proved bound 400 and the empirical threshold 21, and below the bound frames
disagree (82 of 300 random sentences). The migration of Section 3 is counted (`Σ_{i≤K} s^i < s^{K+1}`, no injection
of `N` elements into fewer records, the certified fraction falling as `s^{K+1}/⌊c^L/2⌋`) and the horizon separation
is run on deterministic systems (halt within `C` steps or revisit a configuration and never halt). The normal forms
of Section 4 are decided on hereditarily finite sets coded by Ackermann's bijection (`V₄`, 65 536 sets: every Russell
class a set not in its parent, no universal set, `x ∉ x` throughout), on listings and power sets (the external
diagonal missing, the internal diagonal of a complete registry one of its entries), on counting measure and
ultrafilters, and on the second-order theory of `W₃` by exhaustion over all subsets, relations and functions. The
choice results of Section 5 are decided on `F₁₃`, on random equality-periodic families, on random `G`-families for
`G = ℤ/2, ℤ/3, S₃` (the equivariant criterion, both sides exhaustive), on all 64 subspaces of `F₅³`, on all digraphs
with `|D| ≤ 3`, and on random periodic graphs of bounded range (the transfer digraph, a periodic colouring produced
and verified). The Ω-hard row B7 is witnessed only as the paper states it: the bounded Goldbach sentence receives a
verdict from each of the 397 frames `W_N`, `4 ≤ N ≤ 400`, and no frame states the closure.

Run: `python3 reductio.py` (python ≥ 3.8, no third-party packages; ≈ 50 s, of which the Goldbach instance in 40
frames is most; `results.json` written), or one block: `python3 reductio.py C`; installed, `python3 -m frc_5_reductio`.

| id | block | kind | claim | ledger predicate |
|---|---|---|---|---|
| `A1` | A | EXACT | `Th(W_N)` complete and decidable: ten sentences decided by evaluation in `N = 2..8`; `σ_N` categorical — its models on `[0, N)` are the `N!` copies of `W_N` (`N ≤ 5`) | `5:B5` |
| `A2` | A | EXACT | no finite model of `Q`: among all `N^N` maps on `N ≤ 7` elements none is injective and misses `0` | `5:B3` |
| `A3` | A | EXACT | bounded stability: the Goldbach sentence below 20 takes its standard value in 40 frames above `t(φ) = 400` (proved bound; empirical threshold 21); 300 random Δ₀ sentences, 82 disagree below their bound | `5:B6` |
| `A4` | A | EXACT | records: `Σ_{i≤K} s^i < s^{K+1}` (`s = 2, 3, 10`, `K ≤ 20`); no injection of `N` elements into `R < N` records; the certified fraction `s^{K+1}/⌊c^L/2⌋` is `3.9·10⁻³, 3.7·10⁻⁹, 3.4·10⁻²¹` at `L = 20, 40, 80` | `5:C2`, `5:C3` |
| `A5` | A | EXACT | horizon separation: a deterministic run on `C` configurations halts within `C` steps or revisits a configuration and never halts — `C ≤ 5` exhaustive, `C = 1000` on 200 random systems | `5:C5` |
| `B1` | B | EXACT | on `V₄` (65 536 sets) the Russell class of every `u` is a set not in `u`; no set of `V₄` contains every set of `V₄`; `x ∉ x` throughout | `5:D2` |
| `B2` | B | EXACT | the external diagonal is missing from every listing (`n ≤ 3` exhaustive, `n = 60` random); no map `[n] → P([n])` is onto (`n ≤ 3`); `2ⁿ > n`; the diagonal of a complete finite registry is one of its entries | `5:D3` |
| `B3` | B | EXACT | counting measure on a 6-set invariant under all 720 permutations × 64 subsets; no injection `X ⊔ X → X` (`\|X\| ≤ 4`); the 7 filters on a 3-set have 3 ultrafilters, all principal | `5:D4`, `5:E8` |
| `B4` | B | EXACT | the iterated singletons `∅, {∅}, {{∅}}, …` (seven, the last of 65 537 bits) pairwise distinct with ranks `0..6` | `5:D9` |
| `C1` | C | EXACT | `ch(A) = min A` is a member and the least element of every nonempty subset of `F₁₃` (8191 subsets); finite products of nonempty sets are nonempty | `5:E1` |
| `C2` | C | EXACT | an equality-periodic family `A_{i+N} = A_i` has the choice `f(i) = min A_i` of the same period (50 random families, periods 1..7) | `5:E2` |
| `C3` | C | EXACT | a `G`-equivariant section exists iff every stabiliser action on its fibre has a fixed point: 139 random `G`-families, `G = ℤ/2, ℤ/3, S₃`, both sides exhaustive, 136 with a section | `5:E3` |
| `C4` | C | EXACT | every subspace of `F₅³` (64) has the greedy minimal basis, independent and spanning; `v ↦ −v` on the line fixes no basis over `F_p` for odd `p ≤ 13` and one over `F₂` | `5:E4` |
| `C5` | C | EXACT | periodic König: in every finite digraph with out-degree `≥ 1` the greedy walk repeats within `\|D\| + 1` steps with period `≤ \|D\|` — 353 digraphs with `\|D\| ≤ 3` exhaustive, random `\|D\| = 10, 20, 30` | `5:E5` |
| `C6` | C | EXACT | periodic de Bruijn–Erdős in dimension one: the transfer digraph decides `c`-colourability of all finite subgraphs of 40 random periodic graphs; 32 colourable with a definable periodic colouring produced and verified, 8 with a finite obstruction | `5:E6` |
| `D1` | D | EXACT | the full second-order theory of `W₃` decided by exhaustion (8 subsets, 512 relations, 27 functions): well-ordering, Dedekind-finiteness and the existence of a linear order true, a false sentence false | `5:D8` |
| `D2` | D | EXACT | the Π₁ Goldbach sentence receives a verdict from each frame about its own domain — true in `W_N` for every `4 ≤ N ≤ 400` — and no frame states the closure over all frames | `5:B7` |

`results.json` carries one record per check (id, rows, block, script, kind, claim, PASS/FAIL, detail); the site generator
reads it to colour the witnesses on the public ledger page.

## One cell per predicate

`frc-5-reductio.ipynb` (built by `make_notebook.py`, executed) carries one cell per witnessed ledger predicate, addressable by
its stable id (the predicate's accession key, e.g. `p05027` for `5:E1`; the ledger page opens the notebook at the cell). Every cell is self-contained: it installs the
package from the site (`pip install frc-5-reductio --find-links https://finitering.space/pkg/` — a named requirement,
so pip reports it already satisfied once installed; the sdist `frc-5-reductio-<version>.tar.gz` that `src/make_pkg.py`
writes under `docs/pkg/` at each site build; import name `frc_5_reductio`, `__init__.py` exporting `predicate` and `verify_all`),
states the predicate and runs `predicate("5:E1")`: the block of the check that decides the predicate runs once per session (the
deciding check is `reductio.PREDICATES`, the block the letter of its id; A4 decides C2 and C3, B3 decides D4 and E8, each on one marker), that check is printed from the script's own source — the line under its
`# 5:E1 (p05027)` marker — and every record citing the predicate is listed with its verdict. The markers in `reductio.py`
are the lines the ledger page's source glyph opens (`docs/src/5-reductio/reductio.html#<key>`). The predicates'
Lean counterparts are the declarations named by their keys (`p05027`) at the end of `lean/FrcCore/Reductio.lean` and `lean/FrcLedger/Reductio.lean`
(`lean/make_predicates.py`), one per predicate, with the module as one executable file for the web editor (`lean/web/core/Reductio.lean`, `lean/web/Reductio.lean`).
