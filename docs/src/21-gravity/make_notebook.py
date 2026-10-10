"""Builds 21-gravity-main.ipynb (the Colab driver of the 21-gravity validation package). Run: python3 make_notebook.py"""
import json
import gravcommon as gc

NB = "21-gravity-main.ipynb"
PKG = "21-gravity"
COLAB = f"https://colab.research.google.com/github/gamayos/finite-ring-space/blob/main/src/{PKG}/{NB}"
cells = []
def md(s): cells.append({"cell_type": "markdown", "metadata": {}, "source": s})
def code(s): cells.append({"cell_type": "code", "metadata": {}, "execution_count": None, "outputs": [], "source": s})

GROUPS = [
    ("The Newtonian and relativistic layers", ["newton", "ppn", "branch", "fp_gauge", "fierz_pauli", "radiative", "orderone"],
     "The lattice Green's function and the inverse-square law; the PPN and classical-test factors; the nonlinear completion (cut-flux law, the exponential reading unique); the discrete Fierz–Pauli gauge invariance and its uniqueness; the radiative sector; the order-one constants and the Carrier-register residues."),
    ("The strong field and the rotating solution", ["strongfield", "rotating", "fold_echo"],
     "The static profile with its photon sphere, shadow, ISCO and accretion efficiency; frame dragging as the quarter-turn dual; the fold-return criterion at dev scale (no prompt echo)."),
    ("The floor, the crossover and registration", ["rar", "deepregime", "deepregime_orbit", "inertia", "defect", "counting", "fluxnoise"],
     "The acceleration floor against SPARC; the registration crossover and its orbital response; the two-shift update law; the projection defect; the unified counting checks; flux conservation under drive noise."),
    ("The two-body sector and the primordial spectrum", ["2pn", "1pn_eih", "binding", "primordial"],
     "The 2PN inputs and the J0737−3039 excess; the 1PN equivalence lemma; the binding bookkeeping; the scale-invariant spectrum."),
]

md(f"""[![Open In Colab](https://colab.research.google.com/assets/colab-badge.svg)]({COLAB})

## Gravitation as Phase Synchronisation over Finite Holographic Substrate (Akhtman & Voether, 2026)

**Validation Package.** `finite-ring-space/src/{PKG}` — the paper's twenty-one validation scripts as written, run through one registry: a
family check is one script's verdict (`grav.<stem>`), its micro-checks the script's labelled checks and every PASS/FAIL line it
prints; each family names the row(s) of the paper's predicate ledger it witnesses (the paper's Section "Status", subsection
"Predicate ledger", rows cited as `21:XN`; public copy at `docs/21-gravity/21-gravity-ledger.html`), and the ledger's source column
cites the family ids in return. Where a row is proved in Lean (`lean/FrcCore/Gravity.lean` with no axioms, or
`lean/FrcLedger/Gravity.lean` on Mathlib — the Carrier register, the count face and the merger law, the cover forcing, the operational
cut and the photon sphere, the registration root and the crossover's limits, the shift theorem, with the shadow, ringdown, efficiency,
floor, tilt and interpolant numerals bracketed), the check here is the instance the reader can run. Master-ledger rows of the corpus
reached through the paper rows: `00:A9`, `00:D1`, `00:D3`, `00:D5`, `00:B7`, `00:E1`, `00:D15`, `00:E3`–`00:E7`, `00:E10`, `00:L1`,
`00:L7`, `00:L8`, `00:T1`, `00:T4`, `00:T5`, `00:Z7`.

**Kinds.** `EXACT`: decidable identities over finite fields, exact rationals or symbolic identities, no tolerance in the verdict.
`CHART`: a continuum reading or a comparison with measured data, tagged [approx]/[data] in the script, verdict by stated tolerance.
`SIM`: a seeded stochastic simulation, verdict by stated tolerance on time averages.

**Run.** Cell by cell, or *Runtime → Run all*; ≈ 1–2 minutes on Colab. The last cell writes `results.json` and fails loudly if any family fails.""")

code(f"""# --- environment: clone the package if this notebook is not already running inside it (Colab). numpy and sympy are present on Colab.
import os
if not os.path.exists("gravcommon.py"):
    if not os.path.exists("finite-ring-space"):
        !git clone --filter=blob:none --sparse https://github.com/gamayos/finite-ring-space.git
        os.chdir("finite-ring-space")
        !git sparse-checkout set src/{PKG}
        os.chdir("src/{PKG}")
    else:
        os.chdir("finite-ring-space/src/{PKG}")
print("working directory:", os.path.join(*os.getcwd().split(os.sep)[-3:]))""")

code("""import importlib, gravcommon as gc
importlib.reload(gc)         # a fresh registry if the notebook is re-run
print("families registered:", len(gc.LABELS))""")

def rowkey(r):
    lab = r.split(":")[1]
    return (lab[0], int(re.sub(r"[^0-9]", "", lab) or 0), lab)
import re
for title, stems, desc in GROUPS:
    ids = ["grav." + s for s in stems]
    rows = sorted({r.strip() for i in ids for r in gc.LEDGER[i].split(",")}, key=rowkey)
    table = "| id | script | kind | claim | ledger rows |\n|---|---|---|---|---|\n" + "\n".join(f"| `{i}` | `{gc.script_of(i)}.py` | {gc.KIND[i]} | {gc.LABELS[i]} | {gc.LEDGER[i]} |" for i in ids)
    md(f"## {title}\n{desc}\n\n{table}\n\nLedger rows witnessed: {', '.join(rows)}.")
    code("for fam in " + json.dumps(ids) + ":\n    print(f\"\\n— {gc.script_of(fam)}.py\"); gc.run_block(fam)")

md("""## Summary
Writes `results.json` (one record per family: id, the ledger row(s) witnessed, script, kind, claim, PASS/FAIL, the micro-check count) and raises if any family failed.""")
code("""ok = gc.summary(write=True)
failed = [r["id"] for r in gc.RESULTS if not r["ok"]]
assert ok, f"FAILED families: {failed}"
print(f"all {len(gc.RESULTS)} families pass ({len(gc.MICRO)} micro-checks); records in results.json")""")

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
