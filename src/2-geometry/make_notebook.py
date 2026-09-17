"""Builds 2-geometry-main.ipynb (the Colab driver of the 2-geometry validation package). Run: python3 make_notebook.py"""
import json

NB = "2-geometry-main.ipynb"
PKG = "2-geometry"
COLAB = f"https://colab.research.google.com/github/gamayos/finite-ring-space/blob/main/src/{PKG}/{NB}"
cells = []
def md(s): cells.append({"cell_type": "markdown", "metadata": {}, "source": s})
def code(s): cells.append({"cell_type": "code", "metadata": {}, "execution_count": None, "outputs": [], "source": s})

md(f"""[![Open In Colab](https://colab.research.google.com/assets/colab-badge.svg)]({COLAB})

## Geometry and Constants in Finite Ring Continuum (Akhtman, Symmetry 2026, 18, 751)

**Validation Package.** `finite-ring-space/src/{PKG}` — four block scripts, eighteen checks, standard library only,
added with the paper's predicate ledger (Appendix A, 17 September 2026). Each check names the row(s) of the paper's
ledger it witnesses (rows cited as `2:XN`; public copy at `docs/{PKG}/{PKG}-ledger.html`), and the ledger's source
column cites the check ids in return. Block A decides the Euclidean datum: the half-period, the quarter-turn of order
four and the exponential unit (`2:D1`–`D4`), the generator orbit (`2:B3`), the orientation classes (`2:D5`), the Euler
identity on the shell (`2:D6`), the negation–inversion orbits (`2:D7`) and the conjugation of pairs (`2:D8`). Block B
decides the orbital shell: the cell counts (`2:C2`), the closedness of the spherical completion by exhaustive incidence
(`2:C3`), and the cellular automorphisms — the reindexing `ρ_u` only for `u = ±1`, the dihedral maps, the meridian
reversal on the completion only (`2:B4`, `2:C4`). Block C decides the external comparison: the base-grid bound
(`2:E2`), the bounded refinement of a fixed shell (`2:E3`), and the tower
(`2:E4`). Block D decides the Fourier duality: the principal root (`2:F1`), the inversion (`2:F3`), the polynomial
reading (`2:F4`), the covariance (`2:F5`) and the external transport (`2:F6`).

**Kinds** — `EXACT`: integer arithmetic in `F_p` or exact rationals, no float behind any claim; `CHART`: a [chart]
row — the reading of the shell against the sphere or the circle — in floats with the closed forms checked (C1, C3, D5).

**Run.** Cell by cell, or *Runtime → Run all*; ≈ 30 s. The last cell writes `results.json` and fails loudly if any
check fails.""")

code(f"""# --- environment: clone the package if this notebook is not already running inside it (Colab).
import os
if not os.path.exists("geocommon.py"):
    if not os.path.exists("finite-ring-space"):
        !git clone --filter=blob:none --sparse https://github.com/gamayos/finite-ring-space.git
        os.chdir("finite-ring-space")
        !git sparse-checkout set src/{PKG}
        os.chdir("src/{PKG}")
    else:
        os.chdir("finite-ring-space/src/{PKG}")
print("working directory:", os.path.join(*os.getcwd().split(os.sep)[-3:]))""")

code("""import importlib, geocommon as gc
importlib.reload(gc)         # a fresh registry if the notebook is re-run
gc.RESULTS.clear()""")

md("""## Block A — the Euclidean datum and the involutions
Every primitive generator of `p ∈ {5, 13, 17, 29, 37, 41}`: the half-period, the quarter-turn `i = −g^κ`, the structural set
`Q_p`, the exponential unit; the generator orbit; the orientation classes under `g → g^u`; the Euler identity; the four-orbits;
the conjugation of pairs.""")
code("""import a_datum; importlib.reload(a_datum); a_datum.run()""")

md("""## Block B — the orbital shell and its completion
The complex of Definition 3.1 coded on `p ∈ {5, 13, 17, 29}`: the counts, the closedness of the completion (every edge in two faces,
every vertex link one cycle), and the census of the cellular maps.""")
code("""import b_shell; importlib.reload(b_shell); b_shell.run()""")

md("""## Block C — the external spherical comparison
The base-grid covering radius at `p = 13` (chart); the bounded refinement of a fixed shell in exact rationals, with the
covering radius above `ε = 1/20`; the tower of shells (chart).""")
code("""import c_charts; importlib.reload(c_charts); c_charts.run()""")

md("""## Block D — Fourier duality on the phase cycle
On `(13, 2)`, `(13, 11)`, `(17, 3)`, `(29, 2)`: the principal root, the inversion, the polynomial reading, the covariance, and the
external transport (chart).""")
code("""import d_fourier; importlib.reload(d_fourier); d_fourier.run()""")

md("""## Summary
`results.json` — one record per check (id, ledger rows, script, kind, claim, PASS/FAIL, detail). The site generator reads it to
colour the witnesses on the public ledger page.""")
code("""ok = gc.summary(write=True)
assert ok, "some checks failed — see the FAIL lines above"
print("all checks passed; results.json written")""")

nb = {"cells": cells, "metadata": {"kernelspec": {"display_name": "Python 3", "language": "python", "name": "python3"},
      "language_info": {"name": "python"}, "colab": {"provenance": []}}, "nbformat": 4, "nbformat_minor": 5}
with open(NB, "w") as f:
    json.dump(nb, f, indent=1)
print(f"{NB}: {len(cells)} cells")
