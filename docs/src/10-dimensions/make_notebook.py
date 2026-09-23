#!/usr/bin/env python3
"""Builds 10-dimensions-main.ipynb, the package's Colab notebook: one cell per witnessed predicate of the paper's ledger, each cell addressable
from the ledger page by the predicate's accession key as its stable id (`p10015`: Colab opens the notebook at that cell with `#scrollTo=p10015`).
A predicate cell states the predicate (its text, from the site's ledger JSON) and runs `predicate("10:C5")`: the script of the
predicate's deciding family runs once per session, the deciding check's source is printed from its `# predicate` marker, and every
family record citing the predicate is listed with its verdict. Run: python3 make_notebook.py  (then execute the notebook)."""
import json, re, os
import dimcommon as dcommon

PKG = "10-dimensions"; NB = f"{PKG}-main.ipynb"; PAPER = "10"
COLAB = f"https://colab.research.google.com/github/gamayos/finite-ring-space/blob/main/src/{PKG}/{NB}"
LEDGER = os.path.join(os.path.dirname(os.path.abspath(__file__)), "..", "..", "docs", PKG, f"{PKG}-ledger.json")
cells = []
def md(s, cid): cells.append({"cell_type": "markdown", "metadata": {"id": cid}, "source": s})
def code(s, cid): cells.append({"cell_type": "code", "metadata": {"id": cid}, "execution_count": None, "outputs": [], "source": s})

def plain(tex):
    """The predicate\'s text for a code comment: TeX kept, whitespace collapsed, wrapped at 110 columns."""
    words = " ".join(tex.split()).split(" "); lines, cur = [], "#"
    for w in words:
        if len(cur) + 1 + len(w) > 110: lines.append(cur); cur = "#"
        cur += " " + w
    lines.append(cur); return "\n".join(lines)

data = json.load(open(LEDGER, encoding="utf-8"))
rows = [r for b in data["blocks"] for r in b["rows"]]
witnessed = [r for r in rows if f"{PAPER}:{r['label']}" in dcommon.PREDICATES]

md(f"""[![Open in Colab](https://colab.research.google.com/assets/colab-badge.svg)]({COLAB})

## Dimensional Analysis over Finite Holographic Substrate (Akhtman, 2026) — the predicate ledger, one cell per predicate

**One cell per predicate.** Each cell below verifies one predicate of the paper's ledger (Appendix B; the public copy
`docs/{PKG}/{PKG}-ledger.html`): it installs the package (`pip install` from the site, a no-op after the first), states
the predicate, runs the scripts of the families that cite it (`verify_domains.py`, `check_lift.py` — each once per session),
prints the check that decides the predicate from the script's own source, and lists every family record that cites it
with its verdict. Any cell can be run first. The ledger page links each predicate here, at its cell.

**Run.** Any cell on its own, or *Runtime → Run all*; ≈ 10 s on Colab.""", "header")

# the package from the site as a named requirement through the site's find-links page (docs/pkg/index.html): pip checks the
# installed set first, so a second call in the session is "Requirement already satisfied" (a URL archive would be rebuilt every time)
INSTALL = "!pip install -q frc-10-dimensions --find-links https://finitering.space/pkg/"
md("""Every cell is self-contained: its first line installs the package from the site (pip reports it already satisfied once it is there), its last runs the predicate.""", "note")

for r in witnessed:
    lab = f"{PAPER}:{r['label']}"
    code(f"{INSTALL}\n# {lab} [{r['tag']}] — the deciding family {dcommon.PREDICATES[lab]}\n{plain(r['predicate'])}\nfrom frc_10_dimensions import predicate; predicate(\"{lab}\")", r['key'])

md("""## Summary

The cells above are the paper's python-witnessed predicates; the whole package, family by family, is `run_all.py`
(13 family checks, 217 exact micro-checks, `results.json`).""", "summary")
code(f"""{INSTALL}
from frc_10_dimensions import verify_all
assert verify_all(), "a family check failed"
print("all family checks pass")""", "run-all")

nb = {"cells": cells, "metadata": {"colab": {"provenance": [], "toc_visible": True}, "kernelspec": {"display_name": "Python 3", "language": "python", "name": "python3"},
      "language_info": {"name": "python"}}, "nbformat": 4, "nbformat_minor": 5}
for c in nb["cells"]: c["id"] = c["metadata"]["id"]          # nbformat 4.5: the cell id at top level too, the same stable value
with open(NB, "w", encoding="utf-8") as f: json.dump(nb, f, indent=1, ensure_ascii=False); f.write("\n")
print(f"wrote {NB}: {len(cells)} cells, {len(witnessed)} predicate cells")
