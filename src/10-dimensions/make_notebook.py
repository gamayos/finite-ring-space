"""Builds 8-dirac-main.ipynb (the Colab driver of the 8-dirac validation package). Run: python3 make_notebook.py"""
import json
import dimcommon as dcommon

NB = "10-dimensions-main.ipynb"
PKG = "10-dimensions"
COLAB = f"https://colab.research.google.com/github/gamayos/finite-ring-space/blob/main/src/{PKG}/{NB}"
cells = []
def md(s): cells.append({"cell_type": "markdown", "metadata": {}, "source": s})
def code(s): cells.append({"cell_type": "code", "metadata": {}, "execution_count": None, "outputs": [], "source": s})

BLOCKS = [
    ("verify_domains", "dom", "The exact suite, layers A–H", "The shell datum and domain algebra on F_13 (A), the quartet at the unit face in exact rationals (B), the defining congruences on the lab Carrier (C), both Carriers with faces, minimality and temperature (D), covariance witnesses (E), the window bound and twisted action (F), realized action, the window ladder and meridian transport (G), the pair layer and representative inertness (H)."),
    ("check_lift", "lift", "The lift", "Proposition `lift`: the flag records the fractional-Fourier quarter the chart duality forgets — the operator four-cycle, the chart shadow, the record map, the Carrier face of order four, and the invariance classification, on the shells (13, 2) and (173, 3) and the Carriers 233 and 2 408 561."),
]

md(f"""[![Open In Colab](https://colab.research.google.com/assets/colab-badge.svg)]({COLAB})

## Dimensional Analysis over Finite Holographic Substrate (Akhtman, 2026)

**Validation Package.** `finite-ring-space/src/{PKG}` — two exact suites driven by this notebook, {len(dcommon.LABELS)} family checks aggregating
210 exact micro-checks (integers, residues, exact rationals; no floats, no random sampling). A family check is a layer of
`verify_domains.py` (A–H) or a claim of `check_lift.py` (L1–L5), identified as `<script>.<family>`; each names the row(s) of the paper's
predicate ledger it witnesses (the paper's Section "Machine verification and predicate ledger", rows cited as `10:XN`; public copy at
`docs/10-dimensions/10-dimensions-ledger.html`), and the ledger's source column cites the check ids in return. Master-ledger rows of the
corpus reached through the paper rows: `00:D7` (a unit is a reciprocal cross-frame relation), `00:C12` (temperature and the arity),
`00:C13` (the window ladder and the minimal pair), `00:C8` (the c-square congruence), `00:B10` (the pair-inert sign sector).
The manuscript's 105 source gates (`check_gates.py`) read the paper's LaTeX and run in the corpus tree, not here.

**Kinds.** Every check is `EXACT`: a pass is a proof on the tested instances (the toy shell F_13, the shells p = 29 and 229, the
laboratory-scale shell 173, and both instantiated Carriers Ω = 233 and Ω = 2 408 561).

**Run.** Cell by cell, or *Runtime → Run all*; ≈ 10 s on Colab. The last cell writes `results.json` and fails loudly if any check fails.""")

code(f"""# --- environment: clone the package if this notebook is not already running inside it (Colab). Pure Python; nothing to install.
import os
if not os.path.exists("dimcommon.py"):
    if not os.path.exists("finite-ring-space"):
        !git clone --filter=blob:none --sparse https://github.com/gamayos/finite-ring-space.git
        os.chdir("finite-ring-space")
        !git sparse-checkout set src/{PKG}
        os.chdir("src/{PKG}")
    else:
        os.chdir("finite-ring-space/src/{PKG}")
print("working directory:", os.path.join(*os.getcwd().split(os.sep)[-3:]))""")

code("""import importlib, dimcommon as dcommon
importlib.reload(dcommon)         # a fresh registry if the notebook is re-run
print("families registered:", len(dcommon.LABELS))""")

for script, tag, title, desc in BLOCKS:
    ids = [i for i in dcommon.LABELS if i.startswith(tag + ".")]
    rows = sorted({r.strip() for i in ids for r in dcommon.LEDGER[i].split(",")}, key=lambda r: (r.split(':')[1][0], int(r.split(':')[1][1:])))
    table = "| id | claim | ledger rows |\n|---|---|---|\n" + "\n".join(f"| `{i}` | {dcommon.LABELS[i]} | {dcommon.LEDGER[i]} |" for i in ids)
    md(f"## {title}  (`{script}.py`, EXACT)\n{desc}\n\n{table}\n\nLedger rows witnessed: {', '.join(rows)}.")
    code(f"import {script}; {script}.run()")

md("""## Summary
Writes `results.json` (one record per family check: id, the ledger row(s) witnessed, claim, PASS/FAIL, the micro-check count) and raises if any check failed.""")
code("""ok = dcommon.summary(write=True)
failed = [r["id"] for r in dcommon.RESULTS if not r["ok"]]
assert ok, f"FAILED checks: {failed}"
print(f"all {len(dcommon.RESULTS)} family checks pass ({len(dcommon.MICRO)} exact micro-checks); records in results.json")""")

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
