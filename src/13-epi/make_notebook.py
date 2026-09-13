"""Builds 13-epi-main.ipynb (the Colab driver of the 13-epi validation package). Run: python3 make_notebook.py"""
import json
import epicommon as ecommon

NB = "13-epi-main.ipynb"
PKG = "13-epi"
COLAB = f"https://colab.research.google.com/github/gamayos/finite-ring-space/blob/main/src/{PKG}/{NB}"
cells = []
def md(s): cells.append({"cell_type": "markdown", "metadata": {}, "source": s})
def code(s): cells.append({"cell_type": "code", "metadata": {}, "execution_count": None, "outputs": [], "source": s})

BLOCKS = [
    ("validate_e", "e", "The emergence of e", "The derangement chain ε_n = n!/!n: the superexponential enclosure, the binary64 readout ε_18 and the 100-digit determination at n = 70, the feasibility counts; the wall of e — Wilson reflection, the wall identity !(p−1) ≡ K(p) and the terminal residue −K(p)⁻¹, antiperiodicity, the series duals and the broken group law, the p = 13 residue line; the blind-scale counts over 501 primes; the radian-calibration scan over p < 10⁶ (decided in exact rational arithmetic, π as a Machin bracket); the null experiment."),
    ("validate_pi", "pi", "The emergence of π", "The Wallis pair and its enclosure, the p = 13 residue line, the Machin chain with the binary64 readout M_10 and the 100-digit determination at N = 71, the arcsin tail bound; the legibility window and the −2 terminus, the wall residue for p ≡ 3 (mod 4); Morley, the second-order formula and the π-Wieferich set {5, 45827} below 10⁶; the Lucas revivals; the first-order arcsin vanishing on 428 primes."),
    ("validate_pi2", "pi2", "The quarter wall and the arcsin hierarchy", "Gauss's congruence and the two-squares invariant on the 211 primes p ≡ 1 (mod 4) below 3000; Sun's supercongruence σ_p ≡ 0 (mod p²) and the third-order Bernoulli law on the sixty primes 5 ≤ p < 300; the proof ingredients of the first-order vanishing (binomial transfer, Lerch, the Wallis evaluation, the key identity A + B = 2L); the blind-range Euler congruence; the first revival to second order."),
    ("validate_towers", "tow", "The towers, the frame and the heights", "The fixed-shell towers of e and π on p = 13 and 29 (exact shell projection, bracketed external convergence); the Cayley composition law exhaustively on F_13 and F_29; orientation transport over the units; the height run over all 500 shells p ≡ 1 (mod 4), p ≤ 8009 (the calibration pin, the horizon band, the 68 small-height shells, the height-2 set); the wrap-free window, the pinning relation, the half-turn tautology and the quarter-turn pin."),
    ("kurepa_wall", "kur", "The Kurepa wall to 2.5·10⁵", "`kurepa_wall.c`, compiled here: one O(p) pass per prime in 128-bit modular arithmetic checking !(p−1) ≡ K(p) (mod p) and K(p) ≢ 0 (mod p) for all 22 043 odd primes p < 2.5·10⁵ (≈ 30 s)."),
]

md(f"""# 13-epi — validation package
[![Open In Colab](https://colab.research.google.com/assets/colab-badge.svg)]({COLAB})

**Paper.** *Finite Field Realisation of the Classical Constants π and e* (Akhtman, 2026), `13-epi` of the FRC corpus.
**Package.** `finite-ring-space/src/{PKG}` — five blocks driven by this notebook, {len(ecommon.LABELS)} family checks aggregating
≈ 780 exact micro-checks (integers, residues, exact rationals; the external targets e and π enter only as certified rational
brackets of the paper's own chains, the binary64 constants only as the objects of study of the readout theorems). A family
check is one labelled claim of a script, identified as `<script>.<family>`; each names the row(s) of the paper's predicate
ledger it witnesses (the paper's Section "Machine verification and predicate ledger", rows cited as `13:XN`; public copy at
`docs/13-epi/13-epi-ledger.html`), and the ledger's source column cites the check ids in return. Master-ledger rows of the
corpus reached through the paper rows: `00:B8` (the two-level horizon law), `00:B9` (certification as the orthogonal axis),
`00:C13` (the horizon band), `00:C14` (the quarter-turn and its chirality), `00:B1` (framed rationals), and the open rows
`00:T7`, `00:T8`, `00:T9` (the constants-sector walls).

**Kinds.** Every check is `EXACT`: a pass is a proof on the tested instances. The few floating-point figures printed (a
Pearson correlation, a median, the Gauss sums, the Fermat-quotient moments) are the paper's [approx] diagnostics and decide nothing.

**Run.** Cell by cell, or *Runtime → Run all*; ≈ 45 s on Colab (30 s of it the C pass). The last cell writes `results.json` and fails loudly if any check fails.""")

code(f"""# --- environment: clone the package if this notebook is not already running inside it (Colab). Pure Python plus a C compiler
# for kurepa_wall.c (present on Colab); nothing to install.
import os
if not os.path.exists("epicommon.py"):
    if not os.path.exists("finite-ring-space"):
        !git clone --filter=blob:none --sparse https://github.com/gamayos/finite-ring-space.git
        os.chdir("finite-ring-space")
        !git sparse-checkout set src/{PKG}
        os.chdir("src/{PKG}")
    else:
        os.chdir("finite-ring-space/src/{PKG}")
print("working directory:", os.path.join(*os.getcwd().split(os.sep)[-3:]))""")

code("""import importlib, epicommon as ecommon
importlib.reload(ecommon)         # a fresh registry if the notebook is re-run
print("families registered:", len(ecommon.LABELS))""")

def rowkey(r):
    lab = r.split(":")[1]
    return (lab[0], int(lab[1:]))

for script, tag, title, desc in BLOCKS:
    ids = [i for i in ecommon.LABELS if i.startswith(tag + ".")]
    rows = sorted({r.strip() for i in ids for r in ecommon.LEDGER[i].split(",")}, key=rowkey)
    table = "| id | claim | ledger rows |\n|---|---|---|\n" + "\n".join(f"| `{i}` | {ecommon.LABELS[i]} | {ecommon.LEDGER[i]} |" for i in ids)
    md(f"## {title}  (`{script}.py`, EXACT)\n{desc}\n\n{table}\n\nLedger rows witnessed: {', '.join(rows)}.")
    code(f"import {script}; {script}.run()")

md("""## Summary
Writes `results.json` (one record per family check: id, the ledger row(s) witnessed, claim, PASS/FAIL, the micro-check count) and raises if any check failed.""")
code("""ok = ecommon.summary(write=True)
failed = [r["id"] for r in ecommon.RESULTS if not r["ok"]]
assert ok, f"FAILED checks: {failed}"
print(f"all {len(ecommon.RESULTS)} family checks pass ({len(ecommon.MICRO)} exact micro-checks); records in results.json")""")

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
