# frc — the framework of the Finite Ring Continuum

One python package and two Lean libraries, shared by every ledger of the corpus: the papers' ledgers and the master's
blocks. Begun with the ledger migration's Phase 3 (5 October 2026). The validation packages under `src/` stay as
released, pinned in their dated archives, until their papers migrate.

**Layers.** Each imports only the layer below it.

1. The themes: `frc/<theme>.py`, mirrored in Lean by `lean/FrcCore` (no Mathlib, no axioms) and `lean/FrcLedger` (Mathlib).
2. The ledger files: `frc/ledgers/` and `Ledgers/`, one per paper and one per master block. A ledger file binds each
   predicate to the check and the theorem that decide it.
3. The presentation: one notebook per ledger, and the ledger pages of finitering.space.

**Rules.** A file imports only files of lower rank, or the files listed before it in its own theme. The base, structure
and programme tiers are exact: integers and fractions, the standard library only. Floats and the reals appear in the
chart tier alone. `ci/gates.py` enforces the map (gates G09, G10 and G19), checks the migrated ledgers' coverage (gate G12)
and executes their notebooks (gate G13), and keeps the bridge inventory complete (gate G14; `ci/bridges.py` runs the bridged
pairs' python witnesses), and checks that every published paper pins a served release (gate G15; `ci/release.py`
cuts a release at a paper milestone and serves its archive, web copies and pinned sdists under `docs/releases/`); the workflow `framework` runs it with the tests on every push.

**Run.** `python3 -m unittest discover -s frc/tests -t .` and `python3 ci/gates.py`, from the repository root.

**Ledger files.** `frc/ledgers/p<NN>_<topic>.py` binds one paper's ledger to the themes: the table of its keys, its
shells and its checks, each check marked by the predicates it decides. `ci/make_ledgers.py` generates the table from the
ledger, the notebook beside the file (one cell per predicate, its id the key) and the Lean certificates
(`lean/FrcCore/Ledgers/`, `lean/FrcLedger/Ledgers/`). Migrated so far: 3-causality, `p03_causality.py` (task LM20); 22-quantum, `p22_quantum.py`, and 27-fields,
`p27_fields.py` (task LM35), whose readings against the continuum sit in the chart tier's `chart_quantum.py` and `chart_fields.py`.
One ledger runs with `python3 -m frc.ledgers.p03_causality`.

**Master blocks.** `frc/ledgers/master/<theme>.py` binds one block of the master ledger the same way. Its table is
generated from `docs/00-ledger.json` (the block's rows); the Lean theorems each row's key conjoins are written in the
file (`PROOFS`), since the master has no Lean cells; `lean/make_keys.py` writes the keys from them, and
`ci/make_ledgers.py` the notebook and the certificate `lean/FrcCore/Ledgers/Master/<Theme>.lean`. The first is the
Carrier's, block B, `master/carrier.py` (task LM22): `python3 -m frc.ledgers.master.carrier`. The second is the
Foundation's, block A, `master/foundation.py` (task LM23): `python3 -m frc.ledgers.master.foundation`. The third is the
Subject's, block C, `master/subject.py` (task LM24): `python3 -m frc.ledgers.master.subject`. A block is bound by one
file per theme whose key file proves its rows (task LM25): block C also by `master/fourier.py` (C2, C7),
`master/projective.py` (C19) and `master/extension.py` (C10, the two strata of probability, on `frc/extension.py`'s
quadratic ring; the push of 8 October 2026). Block Z is bound by `master/horizon.py` (Z10, the shell theorem) and `master/logic.py`
(Z1, Gödel vacuous over a finite structure) (task LM26), on the themes' python `frc/horizon.py` and `frc/logic.py`.
Block E is bound by `master/gravity.py` (E6, E7, the horizon's count) (task LM27), on `frc/gravity.py`, and block F by
`master/quantum.py` (F2, the unequal-cycle composite) (task LM28), on `frc/quantum.py`, and block G by
`master/interactions.py` (G11, G12, G16, one generation and the Koide form) (task LM29), on `frc/interactions.py`.
The chart theme's `master/chart.py` (task LM30) binds the chart clauses of L1, L3, L8 and P1, rows of blocks L and P
(`BLOCK = "LP"`), in `CHART`, on `frc/chart.py`: each row decided by a certified bracket in rational arithmetic and
corroborated in floating point.

## The theme map

Generated from `frc/themes.py` (`python3 -m frc.themes`).

| theme | tier | rank | exact | python | Lean core | Lean Mathlib | content |
|---|---|---|---|---|---|---|---|
| base | base | 0 | yes | `registry.py`, `arith.py` | `Nat.lean`, `Pigeonhole.lean`, `Shell.lean`, `Series.lean`, `Ring.lean` | — | the registry of checks; exact integer arithmetic; the naturals, the pigeonhole and the shell's residues; bounded search, finite sums and products; the normaliser of ring identities |
| frame | structure | 10 | yes | `shell.py` | `FrameCore.lean`, `Frame.lean`, `Parity.lean`, `Transform.lean`, `Orbit.lean`, `Instances.lean`, `Sum.lean`, `Meridian.lean` | `Theme/Frame.lean` | the frame (τ; 0, 1, g), the drive and its orbit, the quarter-turn, the lift; finite sums; concrete shells |
| extension | structure | 11 | yes | `extension.py` | `Theme/Quadratic.lean`, `Theme/Extension.lean` | `Theme/Extension.lean` | the quadratic extension F_{p²}, its norm and conjugation, the norm-one torus and the boost; the quaternion norm; the two strata of probability (00:C10) |
| projective | structure | 12 | yes | `projective.py` | `Theme/Projective.lean` | `Theme/Projective.lean` | PGL₂ and SL₂ by elements, the Borel subgroup, the split and non-split tori |
| fourier | structure | 13 | yes | `fourier.py` | `Theme/Fourier.lean` | `Theme/Fourier.lean`, `Theme/Fractional.lean` | the shell DFT and its inversion, the fractional family, the meridians and the scale-shift |
| numbers | structure | 14 | yes | `numbers.py` | `Poly.lean`, `Theme/Numbers.lean` | `Theme/Numbers.lean` | polynomials over the shell and the root criterion; the walls of π and e; the comb |
| logic | structure | 15 | yes | `logic.py` | `Theme/Logic.lean` | `Theme/Logic.lean` | the bounded (Δ₀) language over a finite structure, evaluation, finite Gödel; the counting core of 5-reductio and 25-godel |
| foundation | programme | 20 | yes | `foundation.py` | `Theme/Field.lean`, `Theme/Foundation.lean`, `Theme/Drive.lean` | — | master block A: the ground, the pillars' formal shadows, the trusted base; completeness is primality; every prime carries a frame |
| carrier | programme | 21 | yes | `carrier.py` | `Theme/Carrier.lean` | — | master block B: the Carrier and its constants; the window ladder; the octant |
| subject | programme | 22 | yes | `subject.py` | `Theme/Subject.lean` | — | master block C: the Subject, the frame group, the registration |
| gravity | programme | 23 | yes | `gravity.py` | `Theme/Symbol.lean`, `Theme/Gravity.lean` | — | master block E: gravity on the lattice; the count face |
| quantum | programme | 24 | yes | `quantum.py` | `Theme/Quantum.lean` | — | master block F: the quantum rows |
| interactions | programme | 25 | yes | `interactions.py` | `Theme/Unitary.lean`, `Theme/Interactions.lean` | — | master block G: electromagnetism, the weak and strong forces, matter, flavour |
| horizon | programme | 26 | yes | `horizon.py` | `Theme/Horizon.lean` | `Theme/Horizon.lean` | master block Z: the horizon; the shell theorem; finite Gödel at the totality |
| chart | chart | 30 | no | `chart.py`, `chart_quantum.py`, `chart_fields.py`, `chart_rh.py`, `chart_fourier.py` | — | `Theme/Chart.lean` | readings against the continuum: the cosmology section, the constants' charts; floats and ℝ allowed here only |
| keys | keys | 40 | yes | — | `Keys/<Theme>.lean` | `Keys/<Theme>.lean` | one declaration per key: `FRC.Ledger.p{key}` and `FRC.LedgerML.p{key}` (generated) |
| ledgers | ledgers | 50 | yes | `ledgers/p<NN>_<topic>.py`, `ledgers/master/<theme>.py` | `Ledgers/<ledger>.lean` | `Ledgers/<ledger>.lean` | one file per paper and per master block: predicates bound to themes |

The Lean files that exist today keep their paths: `Frame`, `Orbit`, `Instances` and `Sum` form the frame theme, `Meridian`
belongs to the Fourier theme and `Poly` to the numbers theme. Since task LM22 `Series` (bounded search, sums and
products) is in the base, `Poly` stands on it without the frame, and the frame's root criterion is `Theme/Numbers`.
Since task LM24 (the author's decision of 5 October: split the frame and extension themes, keep the budget) the frame
theme opens with `FrameCore` (the frame) and `Parity` (the square class), the extension theme with `Theme/Quadratic`
(the quadratic extension without a frame), the base holds `Ring` (the normaliser of ring identities), and the foundation
theme opens with `Theme/Field` (the prime field), so that a programme theme takes what it needs under the budget (G10).
Since task LM25 the frame theme's `Transform` holds the transform on the cycle (`W`, `J`, `F`), split from `Sum`.
Since task LM26 the horizon theme's `Theme/Horizon` holds the shell theorem (from 20-rh's `Rh`, which keeps every old
name), and `Theme/Logic` the first-order theory of a finite structure. Since task LM27 the gravity theme's
`Theme/Gravity` holds the horizon's count, with 21-gravity's `count_identity`, and since task LM28 the quantum theme's
`Theme/Quantum` the unequal-cycle composite, and since task LM29 the interactions theme's `Theme/Interactions` one
generation and the Koide form. Since task LM30 the chart theme's Mathlib file `FrcLedger/Theme/Chart.lean` holds the
octant's readings (from 14-entropy) and the floor's (from 21-gravity), with the tilt and the running floor. New theme files go under `Theme/`, since `FrcCore/Fourier.lean`
and `FrcCore/Gravity.lean` hold the papers 6-fourier and 21-gravity. Since task LM18 the paper modules of today import
themes only (and their own paper's modules), and gate G09 fails a cross-paper import.
