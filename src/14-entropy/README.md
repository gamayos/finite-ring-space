# 14-entropy validation package

Validation package of *De Sitter Entropy Estimates over Finite Holographic Substrate* (Akhtman & Voether, 2026),
`14-entr` of the FRC corpus. Three blocks, 19 family checks over 88 micro-checks, driven by `14-entropy-main.ipynb`
(Google Colab, *Runtime → Run all*, ≈ 15 s) or by `run_all.py`. Python with matplotlib (the two triangle blocks draw
the paper's figures into `out/`).

Two kinds of check are kept apart. **EXACT**: integer counts on the instantiated laboratory Carrier Ω = 2 408 561
(the admissibility congruences, the quarter identity, the octant count) — a pass is a proof on that instance.
**CHART**: a one-line computation on published [approx] or [ΛCDM] data (the instrument table, the concordances, the
audit identities, the locus, the confrontations, the triangle's regression), reproduced to the precision the paper
quotes — a pass says the paper's numeral follows from its named inputs; it is not a measurement of the framework.
No fitted framework parameter and no random sampling enters anywhere.

Every family check is one labelled claim of a script and names the row(s) of the paper's predicate ledger it
witnesses (the paper's Section "Claim status", subsection "Predicate ledger", 44 rows in blocks A, B, C, X, P, V, Z,
O, cited as `14:XN`; public copy `docs/14-entropy/14-entropy-ledger.html`); the ledger's source column cites the
check ids in return. Master-ledger rows of the corpus reached through the paper rows: `00:A9`, `00:L1`–`00:L7`,
`00:F7` (formerly Y6).

[![Open In Colab](https://colab.research.google.com/assets/colab-badge.svg)](https://colab.research.google.com/github/gamayos/finite-ring-space/blob/main/src/14-entropy/14-entropy-main.ipynb)

## In-tree

| script | families | micro-checks | claims backed |
|---|---|---|---|
| `estimate_S.py` | est.F1, B9, T1, C1, C2, A1, C3, P3, C4, L1, P2, P1 | 52 | the exact faces and the area law on the laboratory Carrier (EXACT; 14:A2, C6, B9); the instrument table from the four public data (14:C1, C4); the two-face concordance ±17 %/factor 1.9 and the conventional ±14 %/1.7 (14:C4); the chart identity behind the two clusters (14:C8); the circularity audit and the octant inversion, 0.19σ (14:C3, C7, X3, X6); the channel-1 consistency 67.4 (14:C8); the age–rate locus 0.950 read on the stellar age, H₀ = 68.2 ± 1.7 with its three confrontations (14:P3); the one-face concordance ±7 %/±4 % and the r_H^Λ column (14:C4, C7); the floor landing 5.46 ± 1.1 (14:X2); the octant bound 13.79 Gyr against the stellar ages (14:C5, P2); the running floor against the intermediate-redshift measurement (14:P1) |
| `triangle.py` | tri.A, D, W, F | 19 | `make-wedge-2.py` of the paper: the audit identities before drawing (14:C5, C8, C9); the thirteen-object regression k = 3.032, the constrained cubic coefficient c̃ = m/R³ = 0.97 × 10³ kg/m³, the fifteen-object sensitivity, the over-closure exit 1.8 × 10⁸ M☉ within its band (14:C9, X5); the wall residents, the slope decomposition, the Compton entry (14:C9); the triangle and wall-channels figures written (14:V2) |
| `capacity.py` | cap.A, K, F | 17 | `make-wedge-3.py` of the paper: the same identities re-asserted (14:C9); the pinned mass axis and the Avogadro landing to 0.0035 dex (14:C10); the capacity-axis figure written (14:V2) |
| `entcommon.py` | — | — | the registry: micro-check collector, family aggregation, `LEDGER` (check → rows), `LABELS`, kinds, `results.json` |

Run: `python3 run_all.py`. Each block also runs alone (`python3 triangle.py`). Rebuild the notebook: `python3
make_notebook.py`. The figures land in `out/` (gitignored): `registrable-wedge{,-plain,-capacity}.{png,pdf}`,
`wall-channels.{png,pdf}`; the paper's `figures/` carries the dated copies.

## Provenance

`estimate_S.py` is the paper's script as written (round-01/02 amendments of July 2026; the T19 revision of
2026-09-13 replacing the "entailed rate" block by the channel-1 consistency, the age–rate locus and the one-face
concordance), wrapped in a `run()` whose asserts and [PASS] lines report to the registry; the instrument table, the
r_H^Λ column, the audit numerals and the confrontations are additionally asserted at the paper's quoted precision.
`triangle.py` and `capacity.py` are `make-wedge-2.py` and `make-wedge-3.py` of the paper (the capacity-ruler variant
of 2026-08-15/26), renamed for import, their asserts routed to the registry and their figures written to `out/`; the
wall-channels annotation reads "channel-1 rate 67.4" (the T19 wording) where the July figure read "entailed rate
H₀ = 67.4 ± 0.7". The public copy had carried the pre-T19 `estimate_S.py` and `make-wedge-2.py` only; both are in
`_to_delete/14-entropy-superseded/`. Not part of the run: the concordance figure (no in-tree generator) and the
exploratory simplex/shell scripts of August 2026 in the corpus tree (`check_simplex`, `check_shell`,
`check_particles`, `make-simplex`, `make-shell`), which back the structural note of the paper's Section 4 and are
not cited by it.

## Predicate ledger

Rows A1–A8 imports; B1, B3, B4, B6–B8 realisations, B2, B5 definitions, B9 composite; C1–C10 derived; X1–X8 the
explicability dividends; P1–P4 the predictions with their falsifiers; V1–V3 the verification; Z1 the Ω-hard
numeral; B10 the capacity axis as a definition (the former lock conjecture O1, closed 17 Sep 2026 as 00:F7). Check → row: `entcommon.LEDGER`.
