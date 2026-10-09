"""The theme map of the FRC framework: tiers, files and allowed imports (ledger migration, task LM14, 5 October 2026).

The map is Part I §4 of the migration plan (`00-ledger-20260816/reports/ledger-migration-20261003.md`, decisions DF1,
Q05), frozen as data. `ci/gates.py` enforces it (gates G09, G10 and G19), and `frc/README.md` prints it.

The framework has three layers, and each imports only the layer below it:
  the themes (python `frc/<theme>.py`; Lean `FrcCore` and `FrcLedger`), shared by every ledger;
  the ledger files (`frc/ledgers/`, `Ledgers/`), one per paper and one per master block, which bind predicates to themes;
  the presentation (one notebook per ledger, the ledger pages).

Every theme has a rank. A file imports only files of lower rank, or the files listed before it in its own theme. The
base, structure and programme tiers are exact: no float and no third-party import. The chart tier holds the readings
against the continuum, the only place where floats and the reals appear.

The Lean files that exist today keep their paths. `Frame`, `Orbit`, `Instances`, `Sum`, `Meridian` and `Poly` are
assigned to their themes in place. Since task LM22 the base holds `Series` (bounded search, sums and products, from
`Frame` and `Sum`), and the numbers theme's `Theme/Numbers` holds the frame's root criterion (from `Poly`), so that the
programme themes stand on the prime shell without the frame. Since task LM24 (the author's decision of 5 October: split
the frame and extension themes, keep the budget) the frame theme opens with `FrameCore` (the frame itself) and `Parity`
(the square class), the extension theme with `Theme/Quadratic` (the quadratic extension, frame-free), and the base holds
`Ring` (the normaliser of ring identities, from `Theme/Extension`), so that a theme takes the frame without its
arithmetic and the extension without the frame; the foundation theme opens with `Theme/Field` (the prime field, split
from `Theme/Foundation` the same day), so that the Subject takes the field without the foundation's rows. Since task LM25
the frame theme's `Transform` holds the transform on the cycle (split from `Sum`), so that the fourier theme takes it
without the orbits; and a master block may be bound by several block files, one per theme whose key file proves its rows. Since task LM26
the horizon theme's `Theme/Horizon` holds the shell theorem (from 20-rh's `Rh`, the home of 00:Z10), and the logic
theme's `Theme/Logic` the first-order theory of a finite structure (00:Z1). Since task LM27 the gravity theme's
`Theme/Gravity` holds the horizon's count (the registration sphere, the record, the merger law; 00:E6, E7), and
21-gravity's `count_identity` moved there. Since task LM28 the quantum theme's `Theme/Quantum` holds the unequal-cycle
composite (the joint recurrence, the gcd offset, the dephasing; 00:F2), and since task LM29 the interactions theme's
`Theme/Interactions` one generation and the Koide form (00:G11, G12, G16). Since task LM30 the chart theme's `Theme/Chart`
(Mathlib) and `chart.py` hold the readings against the continuum that the master's L1, L3, L8 and P1 stake: the
octant's chart theorems moved there from 14-entropy and the floor's from 21-gravity, under their old names as aliases. Since
task LM36 the horizon theme's Mathlib `Theme/Horizon` holds 20-rh's shell arithmetic on Mathlib, the core `Theme/Horizon`
the rest of 20-rh's core arithmetic, and the chart theme's `Theme/Chart` and `chart_rh.py` its readings with the reals and
in floating point; `Rh` keeps every old name as an alias. The same day the fourier theme's Mathlib `Theme/Fractional` took 6-fourier's
fractional family from its `Fourier` module, old names kept as aliases, and `chart_fourier.py` its observer readout in
floating point. `Meridian` (the meridians and the scale map, on the frame alone) joined the frame theme, so
that 6-fourier's certificate takes its keys from one key file within the budget of gate G10. New theme files go under `Theme/`, since `FrcCore/Fourier.lean` and
`FrcCore/Gravity.lean` are paper modules (6-fourier and 21-gravity). Since task LM18 (5 October 2026) the paper modules
(`LEGACY`) import themes only, and gate G09 fails a cross-paper import.
"""

TIERS = ("base", "structure", "programme", "chart", "keys", "ledgers")

# theme: tier, rank, exact, python files, Lean core files, Lean Mathlib files, content.
# Paths are relative to the repository root. A Mathlib theme file is created where a theme needs Mathlib.
THEMES = {
    "base": dict(tier="base", rank=0, exact=True,
                 py=["frc/registry.py", "frc/arith.py"],
                 core=["lean/FrcCore/Nat.lean", "lean/FrcCore/Pigeonhole.lean", "lean/FrcCore/Shell.lean", "lean/FrcCore/Series.lean", "lean/FrcCore/Ring.lean"], ml=[],
                 content="the registry of checks; exact integer arithmetic; the naturals, the pigeonhole and the shell's residues; bounded search, finite sums and products; the normaliser of ring identities"),
    "frame": dict(tier="structure", rank=10, exact=True,
                  py=["frc/shell.py"],
                  core=["lean/FrcCore/FrameCore.lean", "lean/FrcCore/Frame.lean", "lean/FrcCore/Parity.lean", "lean/FrcCore/Transform.lean", "lean/FrcCore/Orbit.lean", "lean/FrcCore/Instances.lean", "lean/FrcCore/Sum.lean", "lean/FrcCore/Meridian.lean", "lean/FrcCore/Theme/Domain.lean"],
                  ml=["lean/FrcLedger/Theme/Frame.lean"],
                  content="the frame (τ; 0, 1, g), the drive and its orbit, the quarter-turn, the lift; finite sums; concrete shells; the unit-domain lattice on the frame's two charts (00:C12)"),
    "extension": dict(tier="structure", rank=11, exact=True,
                      py=["frc/extension.py"], core=["lean/FrcCore/Theme/Quadratic.lean", "lean/FrcCore/Theme/Extension.lean", "lean/FrcCore/Theme/Tally.lean"], ml=["lean/FrcLedger/Theme/Extension.lean"],
                      content="the quadratic extension F_{p²}, its norm and conjugation, the norm-one torus and the boost; the quaternion norm; the two strata of probability (00:C10); the pair tally on the Q₄ core (00:C11)"),
    "projective": dict(tier="structure", rank=12, exact=True,
                       py=["frc/projective.py"], core=["lean/FrcCore/Theme/Projective.lean"], ml=["lean/FrcLedger/Theme/Projective.lean"],
                       content="PGL₂ and SL₂ by elements, the Borel subgroup, the split and non-split tori"),
    "fourier": dict(tier="structure", rank=13, exact=True,
                    py=["frc/fourier.py"], core=["lean/FrcCore/Theme/Fourier.lean", "lean/FrcCore/Theme/Fractional.lean", "lean/FrcCore/Theme/Lifts.lean", "lean/FrcCore/Theme/Dichotomy.lean", "lean/FrcCore/Theme/Rotations.lean", "lean/FrcCore/Theme/Heisenberg.lean", "lean/FrcCore/Theme/Spectra.lean"],
                    ml=["lean/FrcLedger/Theme/Fourier.lean", "lean/FrcLedger/Theme/Fractional.lean"],
                    content="the shell DFT and its inversion, the fractional family, the meridians and the scale-shift"),
    "numbers": dict(tier="structure", rank=14, exact=True,
                    py=["frc/numbers.py"], core=["lean/FrcCore/Poly.lean", "lean/FrcCore/Theme/Numbers.lean"],
                    ml=["lean/FrcLedger/Theme/Numbers.lean"],
                    content="polynomials over the shell and the root criterion; the walls of π and e; the comb"),
    "logic": dict(tier="structure", rank=15, exact=True,
                  py=["frc/logic.py"], core=["lean/FrcCore/Theme/Logic.lean"], ml=["lean/FrcLedger/Theme/Logic.lean"],
                  content="the bounded (Δ₀) language over a finite structure, evaluation, finite Gödel; the counting core of 5-reductio and 25-godel"),
    "foundation": dict(tier="programme", rank=20, exact=True,
                       py=["frc/foundation.py"], core=["lean/FrcCore/Theme/Field.lean", "lean/FrcCore/Theme/Foundation.lean", "lean/FrcCore/Theme/Drive.lean"], ml=[],
                       content="master block A: the ground, the pillars' formal shadows, the trusted base; completeness is primality; every prime carries a frame"),
    "carrier": dict(tier="programme", rank=21, exact=True,
                    py=["frc/carrier.py"], core=["lean/FrcCore/Theme/Carrier.lean"], ml=[],
                    content="master block B: the Carrier and its constants; the window ladder; the octant"),
    "subject": dict(tier="programme", rank=22, exact=True,
                    py=["frc/subject.py"], core=["lean/FrcCore/Theme/Subject.lean"], ml=[],
                    content="master block C: the Subject, the frame group, the registration"),
    "gravity": dict(tier="programme", rank=23, exact=True,
                    py=["frc/gravity.py"], core=["lean/FrcCore/Theme/Symbol.lean", "lean/FrcCore/Theme/Gravity.lean"], ml=[],
                    content="master block E: gravity on the lattice; the count face"),
    "quantum": dict(tier="programme", rank=24, exact=True,
                    py=["frc/quantum.py"], core=["lean/FrcCore/Theme/Quantum.lean"], ml=[],
                    content="master block F: the quantum rows"),
    "interactions": dict(tier="programme", rank=25, exact=True,
                         py=["frc/interactions.py"], core=["lean/FrcCore/Theme/Unitary.lean", "lean/FrcCore/Theme/Interactions.lean"], ml=[],
                         content="master block G: electromagnetism, the weak and strong forces, matter, flavour"),
    "horizon": dict(tier="programme", rank=26, exact=True,
                    py=["frc/horizon.py"], core=["lean/FrcCore/Theme/Horizon.lean"], ml=["lean/FrcLedger/Theme/Horizon.lean"],
                    content="master block Z: the horizon; the shell theorem; finite Gödel at the totality"),
    "chart": dict(tier="chart", rank=30, exact=False,
                  py=["frc/chart.py", "frc/chart_quantum.py", "frc/chart_fields.py", "frc/chart_rh.py", "frc/chart_fourier.py"], core=[], ml=["lean/FrcLedger/Theme/Chart.lean"],
                  content="readings against the continuum: the cosmology section, the constants' charts; floats and ℝ allowed here only"),
}

# The generated and the binding files (tasks LM19 and LM20): their patterns, ranks above every theme. The key files are
# written by lean/make_keys.py (LM19): a key whose cited theorems all live in themes, in the file of its highest theme.
KEYS = dict(tier="keys", rank=40, core="lean/FrcCore/Keys/{theme}.lean", ml="lean/FrcLedger/Keys/{theme}.lean",
            names=("FRC.Ledger.p{key}", "FRC.LedgerML.p{key}"))
LEDGERS = dict(tier="ledgers", rank=50, py_paper="frc/ledgers/p{nn}_{topic}.py", py_master="frc/ledgers/master/{theme}.py",
               core="lean/FrcCore/Ledgers/{ledger}.lean", ml="lean/FrcLedger/Ledgers/{ledger}.lean")

# The paper modules of today and where their generic content went (tasks LM17, LM18). They become ledger files when
# their paper migrates (LM35, LM36). A paper module imports themes, key files and its own paper's modules only.
LEGACY = {
    "lean/FrcCore/Algebra.lean": ("1-algebra", ["frame", "numbers"]),
    "lean/FrcCore/Quaternion.lean": ("1-algebra", ["extension"]),
    "lean/FrcCore/Geometry.lean": ("2-geometry", ["frame"]),
    "lean/FrcCore/Complex.lean": ("2-geometry", []),
    "lean/FrcCore/Causality.lean": ("3-causality", ["extension"]),
    "lean/FrcCore/Representation.lean": ("4-representation", []),
    "lean/FrcCore/Reductio.lean": ("5-reductio", ["logic"]),
    "lean/FrcCore/Fourier.lean": ("6-fourier", ["fourier"]),
    "lean/FrcCore/Dirac.lean": ("8-dirac", ["extension", "frame"]),
    "lean/FrcCore/Dimensions.lean": ("10-dimensions", ["frame"]),
    "lean/FrcCore/Epi.lean": ("13-epi", ["numbers"]),
    "lean/FrcCore/Entropy.lean": ("14-entropy", []),
    "lean/FrcCore/Rh.lean": ("20-rh", ["extension", "horizon"]),
    "lean/FrcCore/Gravity.lean": ("21-gravity", ["gravity"]),
    "lean/FrcCore/Godel.lean": ("25-godel", ["logic"]),
    "lean/FrcLedger/Algebra.lean": ("1-algebra", []),
    "lean/FrcLedger/Geometry.lean": ("2-geometry", []),
    "lean/FrcLedger/Causality.lean": ("3-causality", []),
    "lean/FrcLedger/Representation.lean": ("4-representation", []),
    "lean/FrcLedger/Reductio.lean": ("5-reductio", ["logic"]),
    "lean/FrcLedger/Fourier.lean": ("6-fourier", ["fourier"]),
    "lean/FrcLedger/Dirac.lean": ("8-dirac", ["extension"]),
    "lean/FrcLedger/Dimensions.lean": ("10-dimensions", []),
    "lean/FrcLedger/Epi.lean": ("13-epi", ["numbers"]),
    "lean/FrcLedger/Entropy.lean": ("14-entropy", ["chart"]),
    "lean/FrcLedger/Rh.lean": ("20-rh", ["extension"]),
    "lean/FrcLedger/Gravity.lean": ("21-gravity", ["chart"]),
    "lean/FrcLedger/Godel.lean": ("25-godel", ["logic"]),
}
LEGACY_IMPORTS_ENFORCED = True          # set by LM18 (5 October 2026): the paper modules import themes only

# Gate G10 (decision Q03): size budgets, on framework files and migrated ledgers only.
BUDGETS = dict(python_file=1800, core_file=800, mathlib_file=1800, executable=3500)
# A theme may carry a larger executable budget (the import closure of a file that includes one of its files): the fourier
# theme at 5,000 lines, the author's decision of 8 October 2026 for 6-fourier's core proofs (6-fourier-20260716/reports/
# blueprint-20261008.md). A file takes the largest budget among the themes in its closure; the file limits are unchanged.
EXECUTABLE_BUDGETS = {"fourier": 5000}

# Gate G09: what an exact python file may import, and the exact functions of `math`.
EXACT_STDLIB = {"fractions", "itertools", "functools", "collections", "math", "json", "os", "re", "sys", "dataclasses",
                "typing", "time", "random", "hashlib", "pathlib", "argparse", "io", "contextlib", "runpy", "__future__"}
MATH_EXACT = {"isqrt", "gcd", "lcm", "comb", "perm", "factorial", "prod"}


def files(kind):
    """kind 'py', 'core' or 'ml': [(path, theme, rank, index in the theme)] over every theme, in rank order."""
    out = []
    for name, t in sorted(THEMES.items(), key=lambda kv: kv[1]["rank"]):
        for i, f in enumerate(t[kind]):
            out.append((f, name, t["rank"], i))
    return out


def markdown():
    """The map as the table of `frc/README.md`."""
    rows = ["| theme | tier | rank | exact | python | Lean core | Lean Mathlib | content |", "|---|---|---|---|---|---|---|---|"]
    short = lambda fs, pre: ", ".join(f"`{f[len(pre):] if f.startswith(pre) else f}`" for f in fs) or "—"
    for name, t in sorted(THEMES.items(), key=lambda kv: kv[1]["rank"]):
        rows.append(f"| {name} | {t['tier']} | {t['rank']} | {'yes' if t['exact'] else 'no'} | {short(t['py'], 'frc/')} | "
                    f"{short(t['core'], 'lean/FrcCore/')} | {short(t['ml'], 'lean/FrcLedger/')} | {t['content']} |")
    rows.append(f"| keys | keys | {KEYS['rank']} | yes | — | `Keys/<Theme>.lean` | `Keys/<Theme>.lean` | one declaration per key: "
                f"`{KEYS['names'][0]}` and `{KEYS['names'][1]}` (generated) |")
    rows.append(f"| ledgers | ledgers | {LEDGERS['rank']} | yes | `ledgers/p<NN>_<topic>.py`, `ledgers/master/<theme>.py` | "
                f"`Ledgers/<ledger>.lean` | `Ledgers/<ledger>.lean` | one file per paper and per master block: predicates bound to themes |")
    return "\n".join(rows)


if __name__ == "__main__":
    print(markdown())
