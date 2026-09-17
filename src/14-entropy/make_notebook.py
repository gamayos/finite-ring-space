"""Builds 14-entropy-main.ipynb (the Colab driver of the 14-entropy validation package). Run: python3 make_notebook.py"""
import json
import entcommon as ecommon

NB = "14-entropy-main.ipynb"
PKG = "14-entropy"
COLAB = f"https://colab.research.google.com/github/gamayos/finite-ring-space/blob/main/src/{PKG}/{NB}"
cells = []
def md(s): cells.append({"cell_type": "markdown", "metadata": {}, "source": s})
def code(s): cells.append({"cell_type": "code", "metadata": {}, "execution_count": None, "outputs": [], "source": s})

BLOCKS = [
    ("estimate_S", "est", "The estimate", "The exact faces on the laboratory Carrier Ω = 2 408 561 and the area law (EXACT); then every chart numeral of the paper: the instrument table from the four public data, the two-face and one-face concordances, the chart identity behind the two clusters, the circularity audit and the octant inversion, the channel-1 consistency, the age–rate locus read on the stellar age, the floor landing, the octant bound against the stellar ages, and the running floor against the intermediate-redshift measurement (CHART)."),
    ("triangle", "tri", "The registrable triangle", "`make-wedge-2.py` of the paper: the audit identities asserted before drawing, the ordinary least-squares regression over the thirteen mid-triangle objects with its constrained and fifteen-object variants, the wall intersections and the over-closure band, the wall residents and the slope decomposition; writes the triangle and the wall-channels figure to `out/`."),
    ("capacity", "cap", "The capacity axis", "`make-wedge-3.py` of the paper: the same identities re-asserted, the pinned mass axis and the Avogadro landing of the holographic-ring-capacity axis; writes the capacity-axis triangle (the paper's Figure 4) to `out/`."),
]

md(f"""[![Open In Colab](https://colab.research.google.com/assets/colab-badge.svg)]({COLAB})

## De Sitter Entropy Estimates over Finite Holographic Substrate (Akhtman & Voether, 2026)

**Validation Package.** `finite-ring-space/src/{PKG}` — three blocks driven by this notebook, {len(ecommon.LABELS)} family checks aggregating
88 micro-checks. A family check is one labelled claim of a script, identified as `<script>.<family>`; each names the row(s) of the
paper's predicate ledger it witnesses (the paper's Section "Claim status", subsection "Predicate ledger", rows cited as `14:XN`;
public copy at `docs/14-entropy/14-entropy-ledger.html`), and the ledger's source column cites the check ids in return.
Master-ledger rows of the corpus reached through the paper rows: `00:A9` (scale, the sole import), `00:L1`–`00:L7` (cosmology,
the metrology, the octant lemma, the triangle, the area law, the interior completions, the running floor), `00:F7` (the additive
window, formerly Y6).

**Kinds.** `EXACT`: integer counts on the instantiated Carrier (the congruences, the quarter identity, the octant count) — a pass is a
proof on that instance. `CHART`: a one-line computation on published [approx] or [ΛCDM] data, reproduced to the precision the paper
quotes — a pass says the paper's numeral follows from its named inputs; it is not a measurement of the framework. No fitted framework
parameter and no random sampling enters anywhere.

**Run.** Cell by cell, or *Runtime → Run all*; ≈ 15 s on Colab. The last cells write `results.json` and show the figures.""")

code(f"""# --- environment: clone the package if this notebook is not already running inside it (Colab). Python + matplotlib; nothing to install on Colab.
import os
if not os.path.exists("entcommon.py"):
    if not os.path.exists("finite-ring-space"):
        !git clone --filter=blob:none --sparse https://github.com/gamayos/finite-ring-space.git
        os.chdir("finite-ring-space")
        !git sparse-checkout set src/{PKG}
        os.chdir("src/{PKG}")
    else:
        os.chdir("finite-ring-space/src/{PKG}")
print("working directory:", os.path.join(*os.getcwd().split(os.sep)[-3:]))""")

code("""import importlib, entcommon as ecommon
importlib.reload(ecommon)         # a fresh registry if the notebook is re-run
print("families registered:", len(ecommon.LABELS))""")

def rowkey(r):
    lab = r.split(":")[1]
    return (lab[0], int(lab[1:]))

for script, tag, title, desc in BLOCKS:
    ids = [i for i in ecommon.LABELS if i.startswith(tag + ".")]
    rows = sorted({r.strip() for i in ids for r in ecommon.LEDGER[i].split(",")}, key=rowkey)
    table = "| id | claim | ledger rows |\n|---|---|---|\n" + "\n".join(f"| `{i}` | {ecommon.LABELS[i]} | {ecommon.LEDGER[i]} |" for i in ids)
    md(f"## {title}  (`{script}.py`)\n{desc}\n\n{table}\n\nLedger rows witnessed: {', '.join(rows)}.")
    code(f"import {script}; {script}.run()")

md("""## Summary
Writes `results.json` (one record per family check: id, the ledger row(s) witnessed, claim, kind, PASS/FAIL, the micro-check count) and raises if any check failed.""")
code("""ok = ecommon.summary(write=True)
failed = [r["id"] for r in ecommon.RESULTS if not r["ok"]]
assert ok, f"FAILED checks: {failed}"
print(f"all {len(ecommon.RESULTS)} family checks pass ({len(ecommon.MICRO)} micro-checks); records in results.json")""")

md("""## The figures
The registrable triangle with the capacity axis (the paper's Figure 4) and the wall-channels figure (Figure 3), as just drawn.""")
code("""from IPython.display import Image, display
display(Image("out/registrable-wedge-capacity.png", width=560))
display(Image("out/wall-channels.png", width=560))""")

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
