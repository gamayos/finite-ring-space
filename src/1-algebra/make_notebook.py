"""Builds 1-algebra-main.ipynb (the Colab driver of the 1-algebra validation package). Run: python3 make_notebook.py"""
import json
import algcommon as gc

NB = "1-algebra-main.ipynb"
PKG = "1-algebra"
COLAB = f"https://colab.research.google.com/github/gamayos/finite-ring-space/blob/main/src/{PKG}/{NB}"
cells = []
def md(s): cells.append({"cell_type": "markdown", "metadata": {}, "source": s})
def code(s): cells.append({"cell_type": "code", "metadata": {}, "execution_count": None, "outputs": [], "source": s})

md(f"""[![Open In Colab](https://colab.research.google.com/assets/colab-badge.svg)]({COLAB})

## Relativistic Algebra over Finite Ring Continuum (Akhtman, Axioms 2025, 14, 636)

**Validation Package.** `finite-ring-space/src/{PKG}` — two block scripts, eleven checks, standard library only,
added with the paper's predicate ledger (Appendix A, 16 September 2026). Each check names the row of the paper's
ledger it witnesses (rows cited as `1:XN`; public copy at `docs/{PKG}/{PKG}-ledger.html`), and the ledger's source
column cites the check ids in return. Block A decides the shell and its frame: symmetry completeness (the Klein
orbits and the structural set, `1:B2`), the oriented quarter-turn `i = −g^κ` (`1:B3`), the affine frame with its
unit `a + b` (`1:B4`), the frame group `Aff(F_p)` of order `p(p−1)` (`1:C2`) and the involutions and counts of the
orbital complex (`1:C4`). Block B decides the framed numbers: the window law (`1:D2`), scale-periodicity in the field
and its failure in `Q` (`1:D4`), the chart of the grid and the obstruction to the published Theorem 2 (`1:D5`), the
zero divisors of `F_p[X]/(X²+1)` (`1:E2`), the absence of an element of additive order two (`1:F1`), and the
refutation of the published Lemma 3 (`1:V1`).

**Kinds** — `EXACT`: integer arithmetic in `F_p` or exact rationals, no float behind any claim; `CHART`: a [chart]
row decided in exact rationals (B3).

**Run.** Cell by cell, or *Runtime → Run all*; ≈ 10 s. The last cell writes `results.json` and fails loudly if any
check fails.""")

code(f"""# --- environment: clone the package if this notebook is not already running inside it (Colab).
import os
if not os.path.exists("algcommon.py"):
    if not os.path.exists("finite-ring-space"):
        !git clone --filter=blob:none --sparse https://github.com/gamayos/finite-ring-space.git
        os.chdir("finite-ring-space")
        !git sparse-checkout set src/{PKG}
        os.chdir("src/{PKG}")
    else:
        os.chdir("finite-ring-space/src/{PKG}")
print("working directory:", os.path.join(*os.getcwd().split(os.sep)[-3:]))""")

code("""import importlib, algcommon as gc
importlib.reload(gc)         # a fresh registry if the notebook is re-run
gc.RESULTS.clear()""")

md("""## Block A — the shell, its frame and the orbital complex
Symmetry completeness on `p ∈ {5, 13, 17, 29, 37, 41, 173}` with the `p ≡ 3 (mod 4)` controls; the oriented quarter-turn on every
primitive root; the affine frame on all 428 frames of `F_13` and `F_17`; the frame group's simple transitivity; the meridian and
latitude involutions and the counts `p−1`, `2κ`, `2κ`, `(p−1)²/2 + 1`.""")
code("""import a_shell; importlib.reload(a_shell); a_shell.run()""")

md("""## Block B — the framed numbers, the charts and the horizon
The window law swept over every `H` on `p ∈ {13, 17, 29}`; scale-periodicity in the field against the rational grids; the
range–resolution trade-off of the chart and the obstruction to the published Theorem 2 at `(13, 2)`, `r = 33/10`; zero divisors
of `F_p[X]/(X²+1)` on the shell against the fields at `p ≡ 3 (mod 4)`; `2s = 0 ⇒ s = 0`; the Euclidean counterexamples.""")
code("""import b_numbers; importlib.reload(b_numbers); b_numbers.run()""")

md("""## Summary
Writes `results.json` (one record per check: id, the ledger row witnessed, script, kind, claim, PASS/FAIL, detail) and raises if any check failed.""")
code("""ok = gc.summary(write=True)
failed = [r["id"] for r in gc.RESULTS if not r["ok"]]
assert ok, f"FAILED checks: {failed}"
print(f"all {len(gc.RESULTS)} checks pass; records in results.json")""")

for k, c in enumerate(cells):
    c["id"] = f"cell-{k}"
nb = {"cells": cells, "metadata": {"kernelspec": {"display_name": "Python 3", "language": "python", "name": "python3"},
      "language_info": {"name": "python"}, "colab": {"provenance": []}}, "nbformat": 4, "nbformat_minor": 5}
with open(NB, "w") as f:
    json.dump(nb, f, indent=1, ensure_ascii=False)
print("wrote", NB, len(cells), "cells")
