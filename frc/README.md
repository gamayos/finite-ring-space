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
and executes their notebooks (gate G13); the workflow `framework` runs it with the tests on every push.

**Run.** `python3 -m unittest discover -s frc/tests -t .` and `python3 ci/gates.py`, from the repository root.

**Ledger files.** `frc/ledgers/p<NN>_<topic>.py` binds one paper's ledger to the themes: the table of its keys, its
shells and its checks, each check marked by the predicates it decides. `ci/make_ledgers.py` generates the table from the
ledger, the notebook beside the file (one cell per predicate, its id the key) and the Lean certificates
(`lean/FrcCore/Ledgers/`, `lean/FrcLedger/Ledgers/`). Migrated so far: 3-causality, `p03_causality.py` (task LM20).
One ledger runs with `python3 -m frc.ledgers.p03_causality`.

## The theme map

Generated from `frc/themes.py` (`python3 -m frc.themes`).

| theme | tier | rank | exact | python | Lean core | Lean Mathlib | content |
|---|---|---|---|---|---|---|---|
| base | base | 0 | yes | `registry.py`, `arith.py` | `Nat.lean`, `Pigeonhole.lean`, `Shell.lean` | — | the registry of checks; exact integer arithmetic; the naturals, the pigeonhole and the shell's residues |
| frame | structure | 10 | yes | `shell.py` | `Frame.lean`, `Orbit.lean`, `Instances.lean`, `Sum.lean` | `Theme/Frame.lean` | the frame (τ; 0, 1, g), the drive and its orbit, the quarter-turn, the lift; finite sums; concrete shells |
| extension | structure | 11 | yes | `extension.py` | `Theme/Extension.lean` | `Theme/Extension.lean` | the quadratic extension F_{p²}, its norm and conjugation, the norm-one torus and the boost; the quaternion norm |
| projective | structure | 12 | yes | `projective.py` | `Theme/Projective.lean` | `Theme/Projective.lean` | PGL₂ and SL₂ by elements, the Borel subgroup, the split and non-split tori |
| fourier | structure | 13 | yes | `fourier.py` | `Meridian.lean`, `Theme/Fourier.lean` | `Theme/Fourier.lean` | the shell DFT and its inversion, the fractional family, the meridians and the scale-shift |
| numbers | structure | 14 | yes | `numbers.py` | `Poly.lean`, `Theme/Numbers.lean` | `Theme/Numbers.lean` | polynomials over the shell and the root criterion; the walls of π and e; the comb |
| logic | structure | 15 | yes | `logic.py` | `Theme/Logic.lean` | `Theme/Logic.lean` | the bounded (Δ₀) language over a finite structure, evaluation, finite Gödel; the counting core of 5-reductio and 25-godel |
| foundation | programme | 20 | yes | `foundation.py` | `Theme/Foundation.lean` | — | master block A: the ground, the pillars' formal shadows, the trusted base; completeness is primality |
| carrier | programme | 21 | yes | `carrier.py` | `Theme/Carrier.lean` | — | master block B: the Carrier and its constants; the window ladder; the octant |
| subject | programme | 22 | yes | `subject.py` | `Theme/Subject.lean` | — | master block C: the Subject, the frame group, the registration |
| gravity | programme | 23 | yes | `gravity.py` | `Theme/Gravity.lean` | — | master block E: gravity on the lattice; the count face |
| quantum | programme | 24 | yes | `quantum.py` | `Theme/Quantum.lean` | — | master block F: the quantum rows |
| interactions | programme | 25 | yes | `interactions.py` | `Theme/Interactions.lean` | — | master block G: electromagnetism, the weak and strong forces, matter, flavour |
| horizon | programme | 26 | yes | `horizon.py` | `Theme/Horizon.lean` | — | master block Z: the horizon; the shell theorem; finite Gödel at the totality |
| chart | chart | 30 | no | `chart.py` | — | `Theme/Chart.lean` | readings against the continuum: the cosmology section, the constants' charts; floats and ℝ allowed here only |
| keys | keys | 40 | yes | — | `Keys/<Theme>.lean` | `Keys/<Theme>.lean` | one declaration per key: `FRC.Ledger.p{key}` and `FRC.LedgerML.p{key}` (generated) |
| ledgers | ledgers | 50 | yes | `ledgers/p<NN>_<topic>.py`, `ledgers/master/<theme>.py` | `Ledgers/<ledger>.lean` | `Ledgers/<ledger>.lean` | one file per paper and per master block: predicates bound to themes |

The Lean files that exist today keep their paths: `Frame`, `Orbit`, `Instances` and `Sum` form the frame theme, `Meridian`
belongs to the Fourier theme and `Poly` to the numbers theme. New theme files go under `Theme/`, since `FrcCore/Fourier.lean`
and `FrcCore/Gravity.lean` hold the papers 6-fourier and 21-gravity. Since task LM18 the paper modules of today import
themes only (and their own paper's modules), and gate G09 fails a cross-paper import.
