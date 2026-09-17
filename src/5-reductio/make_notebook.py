"""Builds 5-reductio-main.ipynb (the Colab driver of the 5-reductio validation package). Run: python3 make_notebook.py"""
import json

NB = "5-reductio-main.ipynb"
PKG = "5-reductio"
COLAB = f"https://colab.research.google.com/github/gamayos/finite-ring-space/blob/main/src/{PKG}/{NB}"
cells = []
def md(s): cells.append({"cell_type": "markdown", "metadata": {}, "source": s})
def code(s): cells.append({"cell_type": "code", "metadata": {}, "execution_count": None, "outputs": [], "source": s})

md(f"""[![Open In Colab](https://colab.research.google.com/assets/colab-badge.svg)]({COLAB})

## Paradoxes of Infinity as Reductio ad Absurdum (Akhtman, preprint 2026)

**Validation Package.** `finite-ring-space/src/{PKG}` — four block scripts, seventeen exact checks, standard library only,
added with the paper's predicate ledger (Appendix B, 17 September 2026). Each check names the row(s) of the paper's
ledger it witnesses (rows cited as `5:XN`; public copy at `docs/{PKG}/{PKG}-ledger.html`), and the ledger's source
column cites the check ids in return. Block A decides the frames: `Th(W_N)` complete and decidable with `σ_N` categorical
(`5:B5`), no finite model of `Q` (`5:B3`), bounded stability with the paper's worked instance and a random sample of
`Δ₀` sentences (`5:B6`), the migration counts (`5:C2`, `5:C3`) and the horizon separation of bounded halting (`5:C5`).
Block B decides the normal forms on a finite universe: Russell on `V₄` (`5:D2`), the external diagonal (`5:D3`), the
choice paradoxes vanishing (`5:D4`, `5:E8`), the iterated singletons (`5:D9`). Block C decides choice recovered: the
least-element choice (`5:E1`), periodic choice (`5:E2`), the equivariant criterion by exhaustion (`5:E3`), the greedy basis
and the `𝔽₅` obstruction (`5:E4`), periodic König (`5:E5`) and periodic de Bruijn–Erdős in dimension one (`5:E6`). Block D
decides determinacy on `W₃` by exhaustive second-order evaluation (`5:D8`) and reports the `Π₁` verdicts frame by frame
(`5:B7`).

**Kinds** — every check is `EXACT`: exhaustive enumeration or integer arithmetic, no float behind any claim.

**Run.** Cell by cell, or *Runtime → Run all*; ≈ 60 s. The last cell writes `results.json` and fails loudly if any
check fails.""")

code(f"""# --- environment: clone the package if this notebook is not already running inside it (Colab).
import os
if not os.path.exists("redcommon.py"):
    if not os.path.exists("finite-ring-space"):
        !git clone --filter=blob:none --sparse https://github.com/gamayos/finite-ring-space.git
        os.chdir("finite-ring-space")
        !git sparse-checkout set src/{PKG}
        os.chdir("src/{PKG}")
    else:
        os.chdir("finite-ring-space/src/{PKG}")
print("working directory:", os.path.join(*os.getcwd().split(os.sep)[-3:]))""")

code("""import importlib, redcommon as rc
importlib.reload(rc)         # a fresh registry if the notebook is re-run
rc.RESULTS.clear()""")

md("""## Block A — the arithmetic frames, their theories, the stability schema, the migration
The frame `W_N` and its first-order evaluator; categoricity of `σ_N`; no finite successor structure of `Q`; the worked Goldbach
instance with its proved bound and its empirical threshold; random `Δ₀` sentences above and below their bounds; record counts,
the mirror and the certified fraction; deterministic runs on `C` configurations.""")
code("""import a_frames; importlib.reload(a_frames); a_frames.run()""")

md("""## Block B — the normal forms on a finite universe
Hereditarily finite sets as Ackermann codes: Russell's class on `V₄`; the diagonal as a theorem and as an entry of a complete finite
registry; counting measure, no doubling, principal ultrafilters; the iterated singletons.""")
code("""import b_paradox; importlib.reload(b_paradox); b_paradox.run()""")

md("""## Block C — choice recovered on finite and periodic structures
The least element as the choice; periodic families; the equivariant criterion on random `G`-families; the greedy basis on `𝔽₅³`
and the obstruction; periodic König; the transfer digraph and the periodic colouring.""")
code("""import c_choice; importlib.reload(c_choice); c_choice.run()""")

md("""## Block D — determinacy on the finite totality
Second-order sentences over `W₃` decided by exhaustion; the `Π₁` sentence frame by frame.""")
code("""import d_determinacy; importlib.reload(d_determinacy); d_determinacy.run()""")

md("""## Summary
`results.json` — one record per check (id, ledger rows, script, kind, claim, PASS/FAIL, detail). The site generator reads it to
colour the witnesses on the public ledger page.""")
code("""ok = rc.summary(write=True)
assert ok, "some checks failed — see the FAIL lines above"
print("all checks passed; results.json written")""")

nb = {"cells": cells, "metadata": {"kernelspec": {"display_name": "Python 3", "language": "python", "name": "python3"},
      "language_info": {"name": "python"}, "colab": {"provenance": []}}, "nbformat": 4, "nbformat_minor": 5}
with open(NB, "w") as f:
    json.dump(nb, f, indent=1)
print(f"{NB}: {len(cells)} cells")
