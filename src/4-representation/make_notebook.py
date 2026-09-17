"""Builds 4-representation-main.ipynb (the Colab driver of the 4-representation validation package). Run: python3 make_notebook.py"""
import json

NB = "4-representation-main.ipynb"
PKG = "4-representation"
COLAB = f"https://colab.research.google.com/github/gamayos/finite-ring-space/blob/main/src/{PKG}/{NB}"
cells = []
def md(s): cells.append({"cell_type": "markdown", "metadata": {}, "source": s})
def code(s): cells.append({"cell_type": "code", "metadata": {}, "execution_count": None, "outputs": [], "source": s})

md(f"""[![Open In Colab](https://colab.research.google.com/assets/colab-badge.svg)]({COLAB})

## Universal Latent Representation in Finite Ring Continuum (Akhtman, Entropy 2026, 28, 40)

**Validation Package.** `finite-ring-space/src/{PKG}` — three block scripts, thirteen checks (eleven exact, two chart),
standard library only, added with the paper's predicate ledger (Section 8, 17 September 2026). Each check names the
row(s) of the paper's ledger it witnesses (rows cited as `4:XN`; public copy at `docs/{PKG}/{PKG}-ledger.html`), and
the ledger's source column cites the check ids in return. Block A decides the paper's set theory by exhaustion on every
finite model with `|Z| ≤ 3`, `|X| ≤ 4`, `|W| = |Z|`: adequacy forces the observation map injective (`4:B4`), two adequate
representations of one observation map are related by the unique bijection `ψ = φ₂ ∘ φ₁⁻¹` (`4:B5`), the charts are
injective with bijective transitions and the canonical choice makes every chart the inclusion (`4:C1`, `4:C2`), and the
lifts invert the observation maps (`4:C3`, `4:C4`). Block B decides what the shell supplies: the host bound `|W_m| = |Z| ≤ p`
(`4:B6`), the affine frames as the charts of the shell itself (`4:C5`), and the `F₁₃` instance end to end. Block C decides
the geometry of Section 6: the character chart on one sphere, exactly (`4:E1`), the quantisation count with exponent
`d − 1` (`4:E2`), and the Gödel code with its reduction modulo a prime above its maximum (`4:E3`).

**Kinds** — `EXACT`: exhaustive enumeration or integer arithmetic, no float behind any claim; `CHART`: a [chart] row — the
reading of the shell against `R^d` — in floats with the closed forms checked (C1, C3).

**Run.** Cell by cell, or *Runtime → Run all*; ≈ 30 s. The last cell writes `results.json` and fails loudly if any
check fails.""")

code(f"""# --- environment: clone the package if this notebook is not already running inside it (Colab).
import os
if not os.path.exists("repcommon.py"):
    if not os.path.exists("finite-ring-space"):
        !git clone --filter=blob:none --sparse https://github.com/gamayos/finite-ring-space.git
        os.chdir("finite-ring-space")
        !git sparse-checkout set src/{PKG}
        os.chdir("src/{PKG}")
    else:
        os.chdir("finite-ring-space/src/{PKG}")
print("working directory:", os.path.join(*os.getcwd().split(os.sep)[-3:]))""")

code("""import importlib, repcommon as rc
importlib.reload(rc)         # a fresh registry if the notebook is re-run
rc.RESULTS.clear()""")

md("""## Block A — adequacy and the Universal Subspace Theorem on every finite model
Every observation map and every representation on the small models; adequacy and the count of adequate representations; the
transition `ψ` and its uniqueness, with the clause off `g(Z)`; Theorem 1 (i)–(iii) over every embedding into `F₅`; the lifts.""")
code("""import a_adequacy; importlib.reload(a_adequacy); a_adequacy.run()""")

md("""## Block B — the shell as host, the frames as charts, the `F₁₃` instance
The host bound and the least hosting shell; the affine frames as the arithmetic charts, simply transitive; three modalities on
`Z ⊂ F₁₃` with quantised codes, their transitions and lifts.""")
code("""import b_shell; importlib.reload(b_shell); b_shell.run()""")

md("""## Block C — the finite ring geometry of embeddings
The character chart on the sphere of radius `√(p−1)`, in floats and in `F_p`; the quantisation count; the Gödel code and its
reduction.""")
code("""import c_geometry; importlib.reload(c_geometry); c_geometry.run()""")

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
