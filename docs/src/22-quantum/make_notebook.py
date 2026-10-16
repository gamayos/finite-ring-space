"""Builds 22-quantum-main.ipynb (the Colab driver of the 22-quantum validation package). Run: python3 make_notebook.py"""
import json
import qmcommon as gc

NB = "22-quantum-main.ipynb"
PKG = "22-quantum"
COLAB = f"https://colab.research.google.com/github/gamayos/finite-ring-space/blob/main/src/{PKG}/{NB}"
cells = []
def md(s): cells.append({"cell_type": "markdown", "metadata": {}, "source": s})
def code(s): cells.append({"cell_type": "code", "metadata": {}, "execution_count": None, "outputs": [], "source": s})

GROUPS = [
    ("The single-system formalism and its arithmetic", ["validate", "sorkin", "dispersion", "transport", "stratum", "gleason", "granularity"],
     "The forced basis, the selection rule, the Lüders update, the ledger and its reduction on both worked carriers; the Sorkin nullity and wrap quantisation; exact boost transport and the finite double cover; the quarter-turn transport trichotomy; the two probability strata and the readout map; the uniqueness of the pair tally; the depth ceiling."),
    ("Composites and the quantum boundary", ["composite", "synchronisation", "renou", "intersubject"],
     "The composite gate on equal and unequal cycles with exact Tsirelson saturation; the m-body locked cluster; the real-vs-complex network table; the consistency of distinct Subjects."),
    ("The gravitational channel and the floors", ["bmv", "gravfraction", "decoherence", "equivalence", "omega"],
     "Gravitationally induced entanglement at the Newtonian rate; the coherent-fraction channel; forbidden collapse, the dilation floor and its exact revival; the two scaling laws and the equivalence-principle null; the Ω ledger."),
    ("The hardware compilations", ["emulation"],
     "The 12- and 16-level compilations of the forced bases against exact references, and the two experiment cards (numeric, 10⁻¹²)."),
]

md(f"""[![Open In Colab](https://colab.research.google.com/assets/colab-badge.svg)]({COLAB})

## Quantum Observation over Finite Relational Substrate (Akhtman, 2026)

**Validation Package.** `finite-ring-space/src/{PKG}` — the paper's seventeen validation suites as written (187 checks), run through one registry: a
family check is one suite's verdict (`qm.<suite>`), its micro-checks the suite's PASS/FAIL lines; each family names the row(s) of the
paper's predicate ledger it witnesses (the paper's Section "Status", subsection "Predicate ledger", rows cited as `22:XN`; public copy at
`docs/22-quantum/22-quantum-ledger.html`), and the ledger's source column cites the family ids in return; the paper's Appendix B carries
the check-level map. Master-ledger rows of the corpus reached through the paper rows: `00:D4`, `00:F1`, `00:C10`, `00:C11`, `00:F2`,
`00:F3`, `00:D1`, `00:D3`, `00:B8`, `00:Y5`.

**Kinds.** `EXACT`: modular integers, Gaussian integers, cyclotomic rings and exact rationals throughout, exhaustive where the domain is
finite, deterministic. `NUM`: floating point as the numeric image of exact references (the hardware compilations, 10⁻¹²).

**Run.** Cell by cell, or *Runtime → Run all*; ≈ 1–2 minutes on Colab. The last cell writes `results.json` and fails loudly if any family fails.""")

code(f"""# --- environment: clone the package if this notebook is not already running inside it (Colab). numpy and sympy are present on Colab.
import os
if not os.path.exists("qmcommon.py"):
    if not os.path.exists("finite-ring-space"):
        !git clone --filter=blob:none --sparse https://github.com/gamayos/finite-ring-space.git
        os.chdir("finite-ring-space")
        !git sparse-checkout set src/{PKG}
        os.chdir("src/{PKG}")
    else:
        os.chdir("finite-ring-space/src/{PKG}")
print("working directory:", os.path.join(*os.getcwd().split(os.sep)[-3:]))""")

code("""import importlib, qmcommon as gc
importlib.reload(gc)         # a fresh registry if the notebook is re-run
print("families registered:", len(gc.LABELS))""")

def rowkey(r):
    lab = r.split(":")[1]
    return (lab[0], int(re.sub(r"[^0-9]", "", lab) or 0), lab)
import re
for title, stems, desc in GROUPS:
    ids = ["qm." + s for s in stems]
    rows = sorted({r.strip() for i in ids for r in gc.LEDGER[i].split(",")}, key=rowkey)
    table = "| id | script | kind | claim | ledger rows |\n|---|---|---|---|---|\n" + "\n".join(f"| `{i}` | `{gc.script_of(i)}.py` | {gc.KIND[i]} | {gc.LABELS[i]} | {gc.LEDGER[i]} |" for i in ids)
    md(f"## {title}\n{desc}\n\n{table}\n\nLedger rows witnessed: {', '.join(rows)}.")
    code("for fam in " + json.dumps(ids) + ":\n    print(f\"\\n— {gc.script_of(fam)}.py\"); gc.run_block(fam)")

md("""## Summary
Writes `results.json` (one record per family: id, the ledger row(s) witnessed, script, kind, claim, PASS/FAIL, the micro-check count) and raises if any family failed.""")
code("""ok = gc.summary(write=True)
failed = [r["id"] for r in gc.RESULTS if not r["ok"]]
assert ok, f"FAILED families: {failed}"
print(f"all {len(gc.RESULTS)} families pass ({len(gc.MICRO)} micro-checks); records in results.json")""")

for k, c in enumerate(cells):
    c["id"] = f"cell-{k}"
nb = {"cells": cells, "nbformat": 4, "nbformat_minor": 5,
      "metadata": {"kernelspec": {"display_name": "Python 3", "language": "python", "name": "python3"},
                   "language_info": {"name": "python"}, "colab": {"provenance": [], "toc_visible": True}}}
try:
    import nbformat
    nbf = nbformat.from_dict(nb); nbformat.validate(nbf); nbformat.write(nbf, NB)
except ImportError:
    with open(NB, "w") as f:
        json.dump(nb, f, indent=1, ensure_ascii=False)
print(f"wrote {NB} with {len(cells)} cells")
