# 25-godel validation package

Validation package of *Incompleteness Without Infinity* (Akhtman, preprint 2026), `25-göd` of the FRC
corpus, added with the paper's predicate ledger (Appendix A, 3 October 2026). One script, `godel.py`, six blocks, twenty-one
checks (all exact), standard library only, driven by `frc-25-godel.ipynb` (Google Colab: one cell per ledger predicate, any cell on its own, or *Runtime → Run all*,
≈ 50 s) or run whole.

Every check names the predicate(s) of the paper's predicate ledger it witnesses (Appendix A "Predicate ledger, machine verification and formalisation", 46 predicates in blocks A–H, J, T, cited as
`25:XN`; public copy `docs/25-godel/index.html`), and the ledger's source column links, for each
machine-verified predicate, the script at the check that decides it (`godel.py#<key>`) and the Lean module at the predicate's declaration
(`lean/FrcCore/Godel.lean` with no axioms, `lean/FrcLedger/Godel.lean` on Mathlib). Where a predicate is proved in Lean, the check here is the instance the reader can run.

The package checks the paper's statements on the finite structures they are about.

- **Gödel's hypotheses over a finite structure (Section 3).** Among all `N^N` maps on `N ≤ 7` elements every injective
  one is onto, so none is a successor of `Q`. A sample of sentences of `Th(M_p)` is decided by exhaustive evaluation,
  with an evaluation object of exactly `m^q` leaves at quantifier depth `q`. The characterising sentence `σ_M` has,
  among all 177 147 structures on three elements, exactly the `3!` copies of the structure as its models. Each of its
  clauses has a control.
- **The part and the whole (Section 4).** The part–whole bound is run on every reading of small structures. The wrap
  lemma is run on certificates built for the purpose. A record of table lookups is accepted, by the same steps and with
  a true end sentence, in the small structure on its cited elements. For a certificate over `Z_5` this holds under
  every completion of the uncited entries, for two larger ones under a fixed sample. An axiom asserted on syntactic
  recognition is accepted there and true in few.
- **The counting facts (Section 5).** The closed terms with `ℓ` leaves are the Catalan-many full binary trees, all of
  value `ℓ mod p`. The records of length at most `B` number fewer than `a^(B+1)`. The certified fraction of the
  equation cohort falls below every tested `1/N`.
- **No compression (Section 5.2).** Every formula of length at most 9 over `M_2` is written out and read back by an
  independent reader. The mention-cost lemma is decided on all of them. The diagonal formula is written out from every
  formula that defines a diagonal relation and measured against the scale `N`. For a dense coding the symbols of the
  diagonal formula are counted in integers. Let `m` have `d` digits in base `a`. An injective coding of length-`n`
  strings by `k`-tuples has `n < dk`. With `k` coordinates in `v` and `k1` in `u`, the formula names each coordinate
  of `v` three times and each of `u` once. It costs at least `2c(k) + c(k+k1)` symbols and its instance `λ` at least
  `3c(k) + k1`, `c(j)` the total length of the `j` shortest names. Both must fit their codes: `2c(k) + c(k+k1) < d·k1`
  and `3c(k) + k1 < dk`. This holds for no `k` beyond `k*(M) < 6a^(⌊d/3⌋+1)`, of cube-root order in `m`. At one
  scale (`k1 = k`) the bound is `6a^(⌊d/4⌋+1)`, of fourth-root order. No instance codes `λ` at a length
  `n ≥ t(M) = d·k*(M)`, and `t(M) < m` in every structure. The comment of block D in `godel.py` carries the proofs.
- **The Tarski reversal (Section 5.3).** The prefix simulation is evaluated as a written sentence against every matrix
  over `M_2` and `M_3`. The guessed labels are checked on every code of length at most 8. Their composition with the
  pairing prefix over `M_3`, the variable indices coded as data, is checked on every string of length at most 6.
- **Section 6, on its finite side.** Second-order sentences are decided over all 512 binary relations on three
  elements. The finite parts of the theory that occupies the trichotomy's middle cell are decided over 248 structures.

Run: `python3 godel.py` (python ≥ 3.9, no third-party packages; ≈ 50 s; `results.json` written), or one block:
`python3 godel.py D`; installed, `python3 -m frc_25_godel`. The summary fails if a check reports FAIL or if a check of the
registry does not report at all.

| id | block | kind | claim | ledger predicate |
|---|---|---|---|---|
| `A1` | A | EXACT | no finite model of `Q`: on `N` elements every injective map is onto (all 873 612 maps, `N ≤ 7`); the `N + 1` numerals `0, S0, …, S^N 0` repeat under every `S` (all 50 069 maps, `N ≤ 6`) | `25:C1` |
| `A2` | A | EXACT | `Th(M_p)` decided by exhaustive evaluation: a sample of eight sentences over `p = 5, 7, 13` take the values number theory gives them, with evaluation objects of `m^q` leaves; `σ_M`, evaluated as a sentence in all 177 147 structures on three elements, holds exactly in the `3!` structures isomorphic to `M` (two choices of `M`); its distinctness clause excludes the structures of one and two elements, its closure clause the 16 384 one-element extensions (each clause with its control) | `25:C2` |
| `A3` | A | EXACT | the `m + 1` sentences `F, ~F, …, ~^m F` admit no injective numbering into a structure of `m` elements (all 16 738 maps, `m = 2..5`); their truth is a finite external table, computed from the written sentences | `25:C5` |
| `B1` | B | EXACT | with `a^K < m` every assignment of storage states to the `m` elements identifies two of them (all 37 218 maps on six instances); at `a^K = m = 4` the injective readings are the 24 bijections | `25:D1` |
| `B2` | B | EXACT | every reading of `m` elements by `R < m` states has a fibre of at least `⌈m/R⌉ ≥ 2` elements, and some reading attains the bound (all 8455 maps on eight instances); every element outside a maximal faithfully represented range is read as one inside it (all 31 203 maximal ranges on six instances) | `25:D3` |
| `B3` | B | EXACT | the wrap: a certificate checked by table lookups is accepted, by the same steps and with a true end sentence, in the structure on its cited elements — under every completion for a certificate over `Z_5` (729 worlds), under fixed samples of 42 and 12 completions for certificates over `M_13` and `M_p`, `p = 10^18 + 9`; a record with a wrong product or a false end sentence is rejected; an axiom asserted on syntactic recognition is accepted in all 2187 small worlds and true in 81 | `25:D4` (corroborates `25:J2`) |
| `C1` | C | EXACT | the closed terms over `{1, +}` with `ℓ` leaves are the Catalan(`ℓ − 1`) full binary trees, all of value `ℓ mod p` (6918 trees, `ℓ ≤ 10`); `C_{ℓ−1} ≥ 2^{ℓ−2}` and the cohort `C(C_{ℓ−1}, 2) ≥ 2^ℓ` for `6 ≤ ℓ ≤ 500`, so the truths of length `≤ L` number at least `2^{L/9}` (`43 ≤ L ≤ 4000`) | `25:E1` |
| `C2` | C | EXACT | the records of length `≤ B` over `a` letters number `(a^{B+1} − 1)/(a − 1) < a^{B+1}`; at `a = 2`, `B = 20` the certified fraction of the cohort is below 1 at `ℓ = 12`, below `10^-6` at `ℓ = 24`, below each tested `1/N` at the 60 values of `ℓ` from a first one on | `25:E2` |
| `C3` | C | EXACT | in the bare evaluation calculus the universal rule for `∀x x+0=x` applies to the full set of its `m` premises alone (all 8224 premise sets for `m = 5, 13`), so the derivation has length `m + 1 > H` for every `H < m`; a richer system with an axiom rule for the clause derives it in one line | `25:E4` |
| `C4` | C | EXACT | for `B = 20, 100, 1000` a true equation between two comb terms, built and written out, is longer than `B`: no record of length `≤ B` contains it | `25:G1` |
| `C5` | C | EXACT | `D_tt` accepts exactly the sentences number theory makes true (a sample of eight sentences and their negations over `M_5`, `M_7`), each true one derived in one line; its step-check performs `m^q` evaluations | `25:G2` |
| `C6` | C | EXACT | bounded consistency by exhaustive search: of 1026 candidate records over `M_5` (754 with an end step, 272 cut at a wrong value) every accepted one has a true end sentence and the 34 ending in `0 = 1` are rejected; the brute certificate lists `(a^{H+1} − 1)/(a − 1) > H` candidates; the reflexivity instances that fit a budget grow over every 8 symbols, not with every symbol | `25:G7` |
| `D1` | D | EXACT | mention cost: a coordinate on which the truth depends is a variable occurring free — 53 925 formulas over `M_3`, and all 17 820 formulas of length `≤ 9` over `M_2` in four variables, each written out and read back by an independent reader | `25:F1` |
| `D2` | D | EXACT | no compression on built instances: the graph of every injective map on M_2^N depends on all 2N coordinates (N = 1, 2; a fixed sample of 1090 maps at N = 3; a constant map as control); every formula of length <= 9 that defines such a graph (N = 1, 2) mentions all 2N variables; each of the 2432 diagonal formulas Ev (Diag & theta), written out from them with each non-degenerate theta of length <= 5 and read back by the independent reader, computes theta at the diagonal image, names each coordinate of v at least three times and each of u at least once (both counts attained), and has at least 3N + \|theta\| > N symbols, so its code is no N-tuple; with the scales split (u of scale 1, v of scale 2; 448 formulas) it is longer than theta, which is at least as long as the scale of v | `25:F2` |
| `D3` | D | EXACT | density: an injective coding of the a^n strings into k-tuples needs m^k >= a^n — below it every coding collides (all 718394 maps, five cases), at equality injective codings exist — so n < dk, d the digit count of m in base a: the largest n with a^n <= m^k lies between (d-1)k and dk - 1 (425112 pairs (m, k): every k up to 12a^(floor(d/3)+1) in the 1990 structures a <= m <= 500 (a = 2), 400 (a = 3, 4), 700 (a = 5)); the diagonal formula with k coordinates in v and k1 in u names each coordinate of v three times and each of u once: over all 52824 orderings of k + k1 names chosen among the k + k1 + 2 shortest, the first k of an ordering given to v (a = 2, 3; nine pairs (k, k1) with k, k1 <= 3), the least cost in delta is 2c(k) + c(k+k1), the least in lambda, with a one-symbol term in each place of u, is 3c(k) + k1, and one ordering attains both, c the cost of the shortest names | `25:F4` |
| `D4` | D | EXACT | quotation exceeds mention: over all 65 600 formulas of length `≤ 9` over `M_2` in six variables, the truth depends on fewer coordinates than the formula has symbols; the shortest formula reading 2, 3, 4 coordinates has 3, 7, 9 symbols | `25:F3` |
| `D5` | D | EXACT | the threshold lies inside the count: an instance with k coordinates in v and k1 in u needs 2c(k) + c(k+k1) < d k1 and 3c(k) + k1 < dk, d the digit count of m in base a; k*(M) is the largest k for which some k1 satisfies both, and t(M) = d k*(M) — by digit count, k*(M) depending on a and d alone, at every alphabet a <= 40 and every d >= 1 with a^d <= 2^400 (4347 cases): where d <= 12 and 6a^(floor(d/3)+1) <= 10000 (243 cases) a scan of every k below twice that bound (1070649 values) and every k1 the second inequality allows (1209527 pairs) finds the k that pass to be the k <= k*(M), with k*(M) < 6a^(floor(d/3)+1), d k*(M) < a^(d-1) <= m (at most 21/32 of a^(d-1), at a = 2, d = 7), k*(M) = 0 exactly for d <= 4, and the one-scale threshold, the largest k with 2c(k) + c(2k) < dk, found by the scan and by bisection, at most k*(M); from d = 13 on k*(M) < 6a^(floor(d/3)+1) alone gives d k*(M) < a^(d-1) (3879 cases), for d = 5..12 it leaves fifteen pairs (a, d), all scanned, and every case is decided by the scan or the bound; at one scale k < 6a^(floor(d/4)+1) in every case, and (2c(k) + c(2k))/k does not decrease (80000 steps: k <= 20000, a = 2..5); in the 1990 structures of D3, in exact integers, each of the 39624 instances the names leave open (a^n <= m^k, a^n1 <= m^k1; every k up to 12a^(floor(d/3)+1), the 425112 pairs (m, k) of D3, and every k1 within lambda's reach, 102969 pairs (k, k1)) passes in digit form and has n < t(M) (some instance reaches n = t(M) - 1), so no instance codes lambda at a length n >= t(M) under any injective codings; there t(M) < m, k*(M) = 0 exactly when m < a^4, t(M)/m is at most 21/32 (at a = 2, m = 64), and at one scale every k <= floor(a^floor((d-1)/4) / 2) is left open (1492 pairs (m, k)) | `25:F6` |
| `E1` | E | EXACT | the prefix simulation: the sentence with the uniform prefix and the copy clauses, evaluated as written, agrees with the coded prefix on every pattern and every matrix over `M_2` (depth `≤ 3`) and `M_3` (depth `≤ 2`), 4184 instances, and on a family of 768 over `M_5`; without the copy clauses the two differ | `25:G4` |
| `E2` | E | EXACT | fragment truth by guessed labels on small coded languages: the propositional layer (340 codes over every labelling, 87 380 by the right-to-left pass); with variable indices coded as data — parse labels, value labels, linkage clauses, pairing prefix — against a separate direct evaluator over `M_3`: all 66 429 strings of length `≤ 5` and all 531 441 of length 6 over every labelling, 1540 well-formed codes, 108 048 edits and extensions | `25:G5` |
| `F1` | F | EXACT | a second-order quantifier over `k`-ary relations ranges over `2^(m^k)` relations; four second-order sentences decided over all 512 binary relations on three elements | `25:H2` |
| `F2` | F | EXACT | the finite parts of "at least `n` elements, for every `n`" with a free predicate `P`, decided over all 248 structures of at most 5 elements, have models with `∃x P(x)` true and false; `∀x ¬P(x)` settles it; the theory of a finite model gives each sentence of a sample its value | `25:H5` |

`results.json` carries one record per check (`id`, `rows`, `block`, `script`, `label`, `ok`, `detail`, `kind`); the site generator
reads it to colour the witnesses on the public ledger page.

## One cell per predicate

`frc-25-godel.ipynb` (built by `make_notebook.py`, executed) carries one cell per witnessed ledger predicate, addressable by
its stable id (the predicate's accession key, e.g. `p25023` for `25:F1`; the ledger page opens the notebook at the cell). Every cell is self-contained: it installs the
package from the site (`pip install frc-25-godel --find-links https://finitering.space/pkg/` — a named requirement,
so pip reports it already satisfied once installed; the sdist `frc-25-godel-<version>.tar.gz` that `src/make_pkg.py`
writes under `docs/pkg/` at each site build; import name `frc_25_godel`, `__init__.py` exporting `predicate` and `verify_all`),
states the predicate and runs `predicate("25:F1")`: the block of the check that decides the predicate runs once per session (the
deciding check is `godel.PREDICATES`, the block the letter of its id), that check is printed from the script's own source — the line under its
`# 25:F1 (p25023)` marker — and every record citing the predicate is listed with its verdict. The markers in `godel.py`
are the lines the ledger page's source glyph opens (`docs/src/25-godel/#<key>`). The predicates'
Lean counterparts are the declarations named by their keys (`p25023`) at the end of `lean/FrcCore/Godel.lean` and `lean/FrcLedger/Godel.lean`
(`lean/make_predicates.py`), one per predicate, with the module as one executable file for the web editor (`lean/web/core/Godel.lean`, `lean/web/Godel.lean`).
