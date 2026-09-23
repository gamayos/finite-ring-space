#!/usr/bin/env python3
"""Builds 1-algebra-main.ipynb, the package's Colab notebook: one cell per witnessed row of the paper's predicate ledger, each cell addressable
from the ledger page by its stable id (`row-1-B2`: Colab opens the notebook at that cell with `#scrollTo=row-1-B2`).
A row cell states the row (its text, from the site's ledger JSON) and runs `algcommon.row("1:B2")`: the block script of the
row's deciding check runs once per session, the deciding check's source is printed from its `# row` marker, and every
record citing the row is listed with its verdict. Run: python3 make_notebook.py  (then execute the notebook)."""
import json, re, os
import algcommon as dcommon

PKG = "1-algebra"; NB = f"{PKG}-main.ipynb"; PAPER = "1"
COLAB = f"https://colab.research.google.com/github/gamayos/finite-ring-space/blob/main/src/{PKG}/{NB}"
LEDGER = os.path.join(os.path.dirname(os.path.abspath(__file__)), "..", "..", "docs", PKG, f"{PKG}-ledger.json")
cells = []
def md(s, cid): cells.append({"cell_type": "markdown", "metadata": {"id": cid}, "source": s})
def code(s, cid): cells.append({"cell_type": "code", "metadata": {"id": cid}, "execution_count": None, "outputs": [], "source": s})

def plain(tex):
    """The row's text for a code comment: TeX kept, whitespace collapsed, wrapped at 110 columns."""
    words = " ".join(tex.split()).split(" "); lines, cur = [], "#"
    for w in words:
        if len(cur) + 1 + len(w) > 110: lines.append(cur); cur = "#"
        cur += " " + w
    lines.append(cur); return "\n".join(lines)

data = json.load(open(LEDGER, encoding="utf-8"))
rows = [r for b in data["blocks"] for r in b["rows"]]
witnessed = [r for r in rows if f"{PAPER}:{r['label']}" in dcommon.ROWS]

md(f"""[![Open in Colab](https://colab.research.google.com/assets/colab-badge.svg)]({COLAB})

## Relativistic Algebra over Finite Ring Continuum (Akhtman, Axioms 2025) — the predicate ledger, one cell per row

**One cell per row.** Each cell below verifies one row of the paper's predicate ledger (Appendix B; the public copy
`docs/{PKG}/{PKG}-ledger.html`): it installs the package (`pip install` from the site, a no-op after the first), states
the row, runs the block script of the check that decides it (`a_shell.py`, `b_numbers.py`, `c_conjecture.py` — each once per session),
prints that check from the script's own source, and lists every record that cites the row
with its verdict. Any cell can be run first. The ledger page links each row here, at its cell.

**Run.** Any cell on its own, or *Runtime → Run all*; ≈ 30 s on Colab (the block C charts are the slow part).""", "rows-header")

# the package from the site as a named requirement through the site's find-links page (docs/pkg/index.html): pip checks the
# installed set first, so a second call in the session is "Requirement already satisfied" (a URL archive would be rebuilt every time)
INSTALL = "!pip install -q frc-1-algebra --find-links https://finitering.space/pkg/"
md("""Every cell is self-contained: its first line installs the package from the site (pip reports it already satisfied once it is there), its last runs the row.""", "rows-note")

for r in witnessed:
    lab = f"{PAPER}:{r['label']}"
    code(f"{INSTALL}\n# {lab} [{r['tag']}] — the deciding check {dcommon.ROWS[lab]}\n{plain(r['predicate'])}\nfrom frc_1_algebra import row; row(\"{lab}\")", f"row-{PAPER}-{r['label']}")

md("""## Summary

The rows above are the paper's python-witnessed predicates; the whole package, check by check, is `run_all.py`
(16 checks, `results.json`).""", "rows-summary")
code(f"""{INSTALL}
from frc_1_algebra import verify_all
assert verify_all(), "a check failed"
print("all checks pass")""", "rows-run-all")

nb = {"cells": cells, "metadata": {"colab": {"provenance": [], "toc_visible": True}, "kernelspec": {"display_name": "Python 3", "language": "python", "name": "python3"},
      "language_info": {"name": "python"}}, "nbformat": 4, "nbformat_minor": 5}
for c in nb["cells"]: c["id"] = c["metadata"]["id"]          # nbformat 4.5: the cell id at top level too, the same stable value
with open(NB, "w", encoding="utf-8") as f: json.dump(nb, f, indent=1, ensure_ascii=False); f.write("\n")
print(f"wrote {NB}: {len(cells)} cells, {len(witnessed)} row cells")
