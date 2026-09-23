#!/usr/bin/env python3
"""make_notebook.py — writes frc-lean-main.ipynb, the Colab notebook that checks the ledger's Lean modules.

Colab has no Lean kernel; the notebook runs Lean in shell cells: elan (the toolchain manager), a sparse
clone of lean/, Mathlib's compiled cache (the one slow step: ≈7 GB unpacked), then `lake env lean` on
each module and the axioms gate.  The web editor (README) is the fast door; this is the Colab door.
"""
import json
from pathlib import Path

ROOT = Path(__file__).resolve().parent
REPO = "https://github.com/gamayos/finite-ring-space"
NB = "frc-lean-main.ipynb"
COLAB = f"https://colab.research.google.com/github/gamayos/finite-ring-space/blob/main/lean/{NB}"
modules = sorted(p.stem for p in (ROOT / "FrcLedger").glob("*.lean"))

def md(s): return {"cell_type": "markdown", "metadata": {}, "source": s.strip("\n").splitlines(keepends=True)}
def code(s): return {"cell_type": "code", "metadata": {}, "execution_count": None, "outputs": [], "source": s.strip("\n").splitlines(keepends=True)}

cells = [
md(f"""
[![Open In Colab](https://colab.research.google.com/assets/colab-badge.svg)]({COLAB})

# FRC predicate ledgers — the Lean witnesses

Each module under `lean/FrcLedger/` proves ledger predicates of one paper as Lean 4 theorems over Mathlib
({', '.join(f'`{m}`' for m in modules)}). This notebook installs the pinned toolchain, fetches Mathlib's
compiled cache and re-checks every module, then prints the axioms each theorem depends on and applies the
strict gate (only `propext`, `Classical.choice`, `Quot.sound`; `sorryAx` and `native_decide` fail).

Budget: 10–15 minutes on a fresh Colab runtime, almost all of it the cache download. To read a proof with
live goal states instead, open the module in the Lean web editor — links in `lean/README.md`.
"""),
code(f"""
# --- toolchain: elan installs the Lean version pinned in lean-toolchain on first use
import os
if not os.path.exists(os.path.expanduser("~/.elan/bin/lake")):
    !curl -sSf https://raw.githubusercontent.com/leanprover/elan/master/elan-init.sh | sh -s -- -y --default-toolchain none
os.environ["PATH"] = os.path.expanduser("~/.elan/bin") + ":" + os.environ["PATH"]
!lake --version || true
"""),
code(f"""
# --- the package: a sparse clone of lean/ (Colab) or the checkout this notebook lives in
if not os.path.exists("lakefile.toml"):
    if not os.path.exists("finite-ring-space"):
        !git clone --depth 1 --filter=blob:none --sparse {REPO}
        !cd finite-ring-space && git sparse-checkout set lean
    %cd finite-ring-space/lean
!cat lean-toolchain && grep -A2 'name = "mathlib"' lake-manifest.json | head -3
"""),
code("""
# --- Mathlib's compiled cache (≈7 GB unpacked; minutes), then the build of the modules themselves
!lake exe cache get
!lake build
"""),
] + [
code(f"""
# --- {m}: re-check the module (0 errors expected; linter notes are not errors)
!lake env lean FrcLedger/{m}.lean
""") for m in modules
] + [
code("""
# --- the axioms of every theorem, and the strict gate
!python3 check_axioms.py
print(open("axioms.log").read())
"""),
code("""
# --- the web copies (one self-contained file per module, for live.lean-lang.org) still compile
!python3 make_web.py --check
for m in __import__("glob").glob("web/*.lean"):
    print("==", m); !lake env lean {m}
"""),
]

nb = {"cells": cells, "metadata": {"kernelspec": {"display_name": "Python 3", "language": "python", "name": "python3"},
                                    "language_info": {"name": "python"}, "colab": {"name": NB}},
      "nbformat": 4, "nbformat_minor": 5}
(ROOT / NB).write_text(json.dumps(nb, indent=1, ensure_ascii=False) + "\n", encoding="utf-8")
print(f"{NB}: {len(cells)} cells, modules {modules}")
