"""Builds 8-dirac-main.ipynb (the Colab driver of the 8-dirac validation package). Run: python3 make_notebook.py"""
import json
import dcommon

NB = "8-dirac-main.ipynb"
PKG = "8-dirac"
COLAB = f"https://colab.research.google.com/github/gamayos/finite-ring-space/blob/main/src/{PKG}/{NB}"
cells = []
def md(s): cells.append({"cell_type": "markdown", "metadata": {}, "source": s})
def code(s): cells.append({"cell_type": "code", "metadata": {}, "execution_count": None, "outputs": [], "source": s})

BLOCKS = [
    ("worked_checks", "fin", "The F_13 worked examples", "Examples `cayley-13` and `dirac-13`, Proposition `power-map-count`, Theorem `cayley-preservation`, Propositions `clifford`, `spin-conjugation`, `transported-dirac-form`, Corollary `boost-covariance` — `finite_checks.py` is the paper's library, its printed booleans made predicates."),
    ("shell_checks", "shell", "The free evolution is the drive", "Theorem `zonal` exhaustively over all windings and cycle points, Corollary `sectors` (the sector separation), the F_17 numbers of Example `dirac-17`."),
    ("o2_checks", "o2", "The canonical Lorentzian coefficient", "Lemmas `class-datum` and `canonical-nu`: the square classes of every named residue on all symmetry-complete shells p < 2000, the admissibility anchors of Remark `nu-not-c`, the lab Carrier."),
    ("o7_checks", "o7", "The parity grading and the two speed-of-light seats", "Theorems `parity` and `even-transport`, Corollary `two-seats`; the drive-step parity exhaustive over every primitive root of the worked shells."),
    ("o134_checks", "o134", "Boost torus, Cayley transform, orbit periods", "Lemma `boost-torus` by exhaustive torus enumeration with the Hilbert-90 identity per element, Theorem `cayley-transform`, Theorem `period-dichotomy` with attained orders, the quintic datum of Remark `three-tori`, the minimality of F_17."),
    ("o8_checks", "o8", "Symmetric Dirac dynamics", "Lemma `spinor-form` at p = 5, 13, 17 including the failure of the γ⁰-twist, Theorem `dirac-evolution` with the 1+1 operator computation at p = 5, the commuting free–interacting composite of Corollary `sectors`, the spin-lift transport of Proposition `two-diracs`."),
    ("latitude_checks", "lat", "The latitude indices of the shell reading", "Section `shell-reading`: time L_1, energy L_{κ+1}, both dualities one capacity shift, the terminal-latitude identities, on F_13, F_17 and the lab Carrier."),
    ("o9_signature_counts", "o9", "Signature as a square-class dichotomy", "Remark `signature-record`: the zero counts of the Euclidean and the Q_ν forms on every symmetry-complete shell p < 60, the collapse of the class over K."),
]

md(f"""[![Open In Colab](https://colab.research.google.com/assets/colab-badge.svg)]({COLAB})

## Schrödinger and Dirac Dynamics over Finite Substrate (Akhtman, 2026)

**Validation Package.** `finite-ring-space/src/{PKG}` — eight block scripts driven by this notebook, {len(dcommon.LABELS)} family checks aggregating
3 848 exact micro-checks. Every script is exact integer arithmetic over F_p and K = F_p[w]/(w² − ν): no floats, no random sampling.
A family check is the labelled claim of a script's docstring (Z1, C3, P5, O1a, X7, L2, …), identified as `<script>.<family>`; each names
the row(s) of the paper's predicate ledger it witnesses (the paper's Section "Machine verification and predicate ledger", rows cited as
`8:XN`; public copy at `docs/8-dirac/8-dirac-ledger.html`), and the ledger's source column cites the check ids in return. Where a row is proved in Lean (`lean/FrcCore/Dirac.lean` with no axioms, or `lean/FrcLedger/Dirac.lean` on Mathlib —
the chronon parity and the named residues, the Hermitian layer and the Cayley step, the kinetic period, the torus with
Hilbert 90, the Clifford relations and the spinor twist, the characters and the counts), the check here is the instance
the reader can run. The
master-ledger rows of the corpus reached through the paper rows: `00:C3` (the Euclidean–Lorentzian dichotomy, 8:B4), `00:C8` (the square
class is chronon parity, 8:B5–B6), `00:B10` (the chart grading carries no signature, 8:B5).

**Kinds.** Every check is `EXACT`: a pass is a proof on the tested instances (the worked shells F_5, F_13, F_17; every symmetry-complete
shell p < 2000 for the square-class scans, p < 60 for the zero counts; the lab Carrier Ω = 2 408 561 for the Carrier-register instances).

**Run.** Cell by cell, or *Runtime → Run all*; ≈ 1 min on Colab. The last cell writes `results.json` and fails loudly if any check fails.""")

code(f"""# --- environment: clone the package if this notebook is not already running inside it (Colab). Pure Python; nothing to install.
import os
if not os.path.exists("dcommon.py"):
    if not os.path.exists("finite-ring-space"):
        !git clone --filter=blob:none --sparse https://github.com/gamayos/finite-ring-space.git
        os.chdir("finite-ring-space")
        !git sparse-checkout set src/{PKG}
        os.chdir("src/{PKG}")
    else:
        os.chdir("finite-ring-space/src/{PKG}")
print("working directory:", os.path.join(*os.getcwd().split(os.sep)[-3:]))""")

code("""import importlib, dcommon
importlib.reload(dcommon)         # a fresh registry if the notebook is re-run
print("families registered:", len(dcommon.LABELS))""")

for script, tag, title, desc in BLOCKS:
    ids = [i for i in dcommon.LABELS if i.startswith(tag + ".")]
    rows = sorted({r.strip() for i in ids for r in dcommon.LEDGER[i].split(",")}, key=lambda r: (r[2], int(r[3:])))
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
