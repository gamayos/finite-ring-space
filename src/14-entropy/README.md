# 14-entropy validation package

Validation package of *De Sitter Entropy Estimates over Finite Holographic Substrate* (Akhtman & Voether, 2026),
`14-entr` of the FRC corpus. One script, `entropy.py` (since 24 September 2026; the registry and the three blocks
merged), three blocks, 19 family checks over 92 micro-checks, driven by `frc-14-entropy.ipynb` (Google Colab: one cell
per ledger predicate, any cell on its own, or *Runtime → Run all*, ≈ 5 s) or run whole. Python with matplotlib (the two
triangle blocks draw the paper's figures into `out/`).

Two kinds of check are kept apart. **EXACT**: integer counts on the instantiated laboratory Carrier Ω = 2 408 561
(the admissibility congruences, the quarter identity, the octant count) — a pass is a proof on that instance.
**CHART**: a one-line computation on published [approx] or [ΛCDM] data (the instrument table, the concordances, the
audit identities, the locus, the confrontations, the triangle's regression), reproduced to the precision the paper
quotes — a pass says the paper's numeral follows from its named inputs; it is not a measurement of the framework.
No fitted framework parameter and no random sampling enters anywhere.

Every family check is one labelled claim of a block (`est.C1`, `tri.D`, `cap.K`, …) and names the predicate(s) of the
paper's ledger it witnesses (the paper's Section 5.3, "Predicate ledger", 41 predicates in blocks A, B, C, X, P, Z, cited
as `14:<label>`; public copy `docs/14-entropy/14-entropy-ledger.html`); the ledger's source column links the script at
the deciding family's marker, `entropy.py#<key>` (the family checks are listed on the public page from `results.json`).
Where a predicate is proved in Lean (`lean/FrcCore/Entropy.lean` with no axioms, or `lean/FrcLedger/Entropy.lean` on
Mathlib — the congruences and the laboratory Carrier, the octant sector and its character, the rival chart's age
identity verified against its own Friedmann equation with its numerals bracketed, the locus), the check here is the
instance the reader can run. Master-ledger predicates of the corpus reached through the paper predicates: `00:A9`,
`00:L1`–`00:L7`, `00:F7`.

[![Open In Colab](https://colab.research.google.com/assets/colab-badge.svg)](https://colab.research.google.com/github/gamayos/finite-ring-space/blob/main/src/14-entropy/frc-14-entropy.ipynb)

## In-tree

| block | families | micro-checks | claims backed |
|---|---|---|---|
| `est` | est.F1, B9, T1, C1, C2, A1, C3, P3, C4, L1, P2, P1 | 56 | the paper's `estimate_S.py` as written: the exact faces (EXACT; 14:A2, C6) and the area law (EXACT counts and a CHART face; 14:B9) on the laboratory Carrier; the instrument table from the four public data (14:C1, C4); the two-face concordance ±17 %/factor 1.9 and the conventional ±14 %/1.7 (14:C4); the chart identity behind the two clusters (14:C8); the circularity audit and the octant inversion, 0.19σ (14:C3, C7, X3, X6); the channel-1 consistency 67.4 (14:C8); the age–rate locus 0.950 read on the stellar age, H₀ = 68.2 ± 1.7 with its three confrontations (14:P3); the one-face concordance ±7 %/±4 % and the r_H^Λ column (14:C4, C7); the floor landing 5.46 ± 1.1 (14:X2); the octant bound 13.79 Gyr against the stellar ages (14:C5, P2); the running floor against the intermediate-redshift measurement — the endpoint and the global linear rate against the ∝ H(z) chord, and the four bins: a constant floor excluded by Δχ² = 23, the running form at A = 1.39 ± 0.03 with χ² = 5.4/3, the binned rate 0.98 ± 0.19 on the chord, the amplitude 0.12 dex above cH₀/2π (14:P1) |
| `tri` | tri.A, D, W, F | 19 | `make-wedge-2.py` of the paper: the audit identities before drawing (14:C5, C8, C9); the thirteen-object regression k = 3.032, the constrained cubic coefficient c̃ = m/R³ = 0.97 × 10³ kg/m³, the fifteen-object sensitivity, the over-closure exit 1.8 × 10⁸ M☉ within its band (14:C9, X5); the wall residents, the slope decomposition, the Compton entry (14:C9); the triangle and wall-channels figures written (no predicate) |
| `cap` | cap.A, K, F | 17 | `make-wedge-3.py` of the paper: the same identities re-asserted (14:C9); the pinned mass axis and the Avogadro landing to 0.0035 dex (14:C10); the capacity-axis figure written (no predicate) |

The registry (micro-check collector, family aggregation, `LEDGER` check → predicates, `LABELS`, kinds, `PREDICATES`,
`results.json`) is the head of the script; matplotlib is imported on a block's first use, so importing the package is
instantaneous.

Run: `python3 entropy.py` (`results.json` written; exit 1 if a family check fails), or one block: `python3 entropy.py
tri`; installed, `python3 -m frc_14_entropy`. Rebuild the notebook: `python3 make_notebook.py`. The figures land in
`out/` beside the script (gitignored): `registrable-wedge{,-plain,-capacity}.{png,pdf}`, `wall-channels.{png,pdf}`; the
paper's `figures/` carries the dated copies.

## One cell per predicate

`frc-14-entropy.ipynb` (built by `make_notebook.py`, executed) carries one cell per witnessed ledger predicate,
addressable by its stable id (the predicate's accession key, e.g. `p14022` for `14:C5`; the ledger page opens the
notebook at the cell). Every cell is self-contained: it installs the package from the site (`pip install frc-14-entropy
--find-links https://finitering.space/pkg/` — a named requirement, so pip reports it already satisfied once installed;
the sdist `frc-14-entropy-<version>.tar.gz` `src/make_pkg.py` writes under `docs/pkg/` at each site build, matplotlib
its one dependency (`REQUIRES` in `__init__.py`); import name `frc_14_entropy`, `__init__.py` exporting `predicate`),
states the predicate and runs `predicate("14:C5")`: the blocks of the families that cite the predicate run once per
session (the deciding family is `entropy.PREDICATES`), the check that decides the predicate is printed from the
script's own source — the line under its `# 14:C5 (<key>)` marker — and every family record citing the predicate is
listed with its verdict, the deciding one marked. The markers in `entropy.py` are the lines the ledger page's source
glyph opens (`docs/src/14-entropy/#<key>`). The predicates' Lean counterparts are the declarations named by
their keys (`p14022`) at the end of `lean/FrcCore/Entropy.lean` and `lean/FrcLedger/Entropy.lean`
(`lean/make_predicates.py`), one per predicate, with the paper's module as one executable file for the web editor.

## Provenance

Block `est` is the paper's script `estimate_S.py` as written (round-01/02 amendments of July 2026; the T19 revision of
2026-09-13 replacing the "entailed rate" block by the channel-1 consistency, the age–rate locus and the one-face
concordance), its asserts and [PASS] lines reporting to the registry; the instrument table, the r_H^Λ column, the audit
numerals and the confrontations are additionally asserted at the paper's quoted precision. Blocks `tri` and `cap` are
`make-wedge-2.py` and `make-wedge-3.py` of the paper (the capacity-ruler variant of 2026-08-15/26), their asserts routed
to the registry and their figures written to `out/`; the wall-channels annotation reads "channel-1 rate 67.4" (the T19
wording) where the July figure read "entailed rate H₀ = 67.4 ± 0.7". Until 24 September 2026 the package was four
files (`entcommon.py`, `estimate_S.py`, `triangle.py`, `capacity.py`, driven by `run_all.py` and the narrative notebook
`14-entropy-main.ipynb`); the records of `results.json` are unchanged by the merge (the two figure families no longer
cite a ledger predicate, block V having left the ledger), and `est.P1` gained the four-bin confrontation the predicate
states (the bins digitised in the corpus paper 43-muse; 88 → 92 micro-checks). Not part of the run: the concordance figure (no in-tree
generator) and the exploratory simplex/shell scripts of August 2026 in the corpus tree (`check_simplex`,
`check_shell`, `check_particles`, `make-simplex`, `make-shell`), which back the structural note of the paper's
Section 4 and are not cited by it.

## Predicate ledger

Predicates A1–A8 imports; B1, B3, B4, B6–B8 realisations, B2, B5 definitions, B9 composite; C1–C10 derived; X1–X8 the
explicability dividends; P1–P4 the predictions with their falsifiers; Z1 the Ω-hard numeral; B10 the capacity axis as
a definition (the former lock conjecture O1, closed 17 Sep 2026 as `00:F7`). Block V retired on 24 September 2026: its
rows described the package and the libraries, not the paper; the machine verification is carried by the witness links
of the rows. Check → predicate: `entropy.LEDGER`.
