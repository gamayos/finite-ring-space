#!/usr/bin/env python3
"""Builds frc-8-dirac.ipynb, the package's Colab notebook: one cell per witnessed predicate of the paper's ledger, each cell addressable
from the ledger page by the predicate's accession key as its stable id (`p08029`: Colab opens the notebook at that cell with `#scrollTo=p08029`).
A predicate cell states the predicate (its text, from the site's ledger JSON) and runs `predicate("8:D9")`: the block of the
predicate's deciding family runs once per session, the deciding check's source is printed from its `# 8:D9 (p08029)` marker, and every
family record citing the predicate is listed with its verdict. Run: python3 make_notebook.py  (then execute the notebook)."""
import json, re, os
import dirac as dcommon

PKG = "8-dirac"; NB = f"frc-{PKG}.ipynb"; PAPER = "8"
LEDGER_URL = f"https://finitering.space/{PKG}/"; APPENDIX = "A"          # the paper's ledger page and the appendix that carries the ledger
CITE = "Akhtman, Preprints 2025"; DOI = "https://doi.org/10.20944/preprints202510.1486.v2"                     # the heading's citation, linked to the article
SCRIPT = "dirac.py"; SCRIPTS = f"[`{SCRIPT}`](https://finitering.space/src/{PKG}/)"; RUNTIME = "≈ 1 min"      # the one script, linked to its source page
LEDGER = os.path.join(os.path.dirname(os.path.abspath(__file__)), "..", "..", "docs", PKG, f"{PKG}-ledger.json")
cells = []
def md(s, cid): cells.append({"cell_type": "markdown", "metadata": {"id": cid}, "source": s})
def code(s, cid): cells.append({"cell_type": "code", "metadata": {"id": cid}, "execution_count": None, "outputs": [], "source": s})

def plain(tex):
    """The predicate's text for a code comment: TeX kept, whitespace collapsed, wrapped at 110 columns."""
    words = " ".join(tex.split()).split(" "); lines, cur = [], "#"
    for w in words:
        if len(cur) + 1 + len(w) > 110: lines.append(cur); cur = "#"
        cur += " " + w
    lines.append(cur); return "\n".join(lines)

data = json.load(open(LEDGER, encoding="utf-8"))
rows = [r for b in data["blocks"] for r in b["rows"]]
witnessed = [r for r in rows if f"{PAPER}:{r['label']}" in dcommon.PREDICATES]

md(f"""## Schrödinger and Dirac Dynamics over Finite Substrate, [{CITE}]({DOI})

Each cell below verifies one predicate of the paper's predicate ledger (Appendix {APPENDIX}; [{LEDGER_URL[8:]}]({LEDGER_URL})): it runs the
blocks of {SCRIPTS} whose family checks cite the predicate, prints the deciding check and lists every record that cites it with its verdict. Any cell can be run first, or *Runtime → Run all* ({RUNTIME}).""", "header")

# the package from the site as a named requirement through the site's find-links page (docs/pkg/index.html): pip checks the
# installed set first, so a second call in the session is "Requirement already satisfied" (a URL archive would be rebuilt every time)
INSTALL = "!pip install -q frc-8-dirac --find-links https://finitering.space/pkg/"
md("""Every cell is self-contained: its first line installs the package from the site (pip reports it already satisfied once it is there), its last runs the predicate.""", "note")

for r in witnessed:
    lab = f"{PAPER}:{r['label']}"
    code(f"{INSTALL}\n# {lab} ({r['key']}) [{r['tag']}] — the deciding check {dcommon.PREDICATES[lab]}\n{plain(r['predicate'])}\nfrom frc_8_dirac import predicate; predicate(\"{lab}\")", r['key'])

md("""## Summary

The cells above are the paper's python-witnessed predicates; the whole script, block by block, is `python3 dirac.py`
(52 family checks over 3 848 exact micro-checks, `results.json`), `python3 -m frc_8_dirac` once installed.""", "summary")
code(f"""{INSTALL}
from frc_8_dirac import verify_all
assert verify_all(), "a check failed"
print("all checks pass")""", "run-all")

nb = {"cells": cells, "metadata": {"colab": {"provenance": [], "toc_visible": True}, "kernelspec": {"display_name": "Python 3", "language": "python", "name": "python3"},
      "language_info": {"name": "python"}}, "nbformat": 4, "nbformat_minor": 5}
for c in nb["cells"]: c["id"] = c["metadata"]["id"]          # nbformat 4.5: the cell id at top level too, the same stable value
with open(NB, "w", encoding="utf-8") as f: json.dump(nb, f, indent=1, ensure_ascii=False); f.write("\n")
print(f"wrote {NB}: {len(cells)} cells, {len(witnessed)} predicate cells")
