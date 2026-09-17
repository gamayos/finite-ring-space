"""Builds 38-s13-main.ipynb (the Colab driver of the 38-s13 validation package). Run: python3 make_notebook.py"""
import json, re
import s13common as gc

NB = "38-s13-main.ipynb"
PKG = "38-s13"
COLAB = f"https://colab.research.google.com/github/gamayos/finite-ring-space/blob/main/src/{PKG}/{NB}"
cells = []
def md(s): cells.append({"cell_type": "markdown", "metadata": {}, "source": s})
def code(s): cells.append({"cell_type": "code", "metadata": {}, "execution_count": None, "outputs": [], "source": s})

GROUPS = [
    ("The in-tree audit: the pair, the tower, the quarter roots, the flow, the covering", ["check_s13", "check_phi"],
     "Integer arithmetic on F₁₃ and F₂₃₃: the pair constants and the tower identity C₁₂ = C₄ × C₃ (with its general form 4a − κb ≡ 1 mod 4κ), the channel gcds, the Carrier quarter roots 78⁵⁸ = 89 = h and ħ = 144 (ħh = 1, ħ + h = Ω), the dilation instance 3/58 = (p−1)/(Ω−1) and the per-chronon leak rate (κ/S)/(p−1) = 1/(Ω−1), κ-free at both (13,233) and (5,233) (C10), the (53,13) kill test, the meridian stations, the covering 144 = 36 + 108, the ramification and fusion congruences, the registration fibre product |R| = 696; the golden-ratio audit of the quarter roots (h = 13/8, ħ = 8/13 on F₂₃₃, the Fibonacci convergents)."),
    ("The gravitational face: the two faces of the leak and the comparison chart", ["check_o1", "o1_gr_chart"],
     "The two faces of the leak, angular κ/S and temporal κ/(2S), ratio exactly 2 (the double cover, C7); the face-ratio identity 2 ⟺ 2γ − β = 1 over the PPN lattice (C8); the dictionary p_sl = 3(S/κ) r_g and its capacity reading — the dictionary C12, a definition — in exact rationals; the continuum comparison chart in sympy [approx: continuum chart]: the parametrised isotropic metric's apsidal and clock-deficit coefficients, the ratio deviation (2/3)(2γ − β − 1), Brans–Dicke's −2/(2+ω) with its GR limit."),
    ("The two fibrations of the frame variety", ["check_fibrations"],
     "The frame variety of order p(p²−1) carries two torus fibrations with one count (A9, master C22): the split fibration by the drive torus C_{p−1} over the unit 2-sphere, p(p+1) points, and the non-split fibration by the boost torus C_{p+1} over the nonsquare-radius 2-sphere, p(p−1) points — the frame triple G ≅ P¹ × F_p × C_{p−1} and the boundary clause, exact at p = 5, 13, 17 (the laboratory's `verify-hopf` carries the same content at p = 13 and p = 5)."),
    ("The covering parity and the winding family", ["check_o2", "check_o3"],
     "The covering parity theorem (D12): the reflection identity at p = 5, 13, 17, 29, the multiplicities μ ∈ {1, 3} by the row-parity decider, the 72/72 direct/echo balance, Ω-blind at p = 5, 17, 29; the winding family (D13): the winding-1/5 identity, the 144-slot containment, the covering multiset, the axis passages 13j/m (drawn iff m ≥ 4), the ramification 13/(2m)."),
    ("The laboratory's six suites", ["verify-233", "verify-sky", "verify-space", "verify-f13", "verify-hopf", "verify-render"],
     "The suites the laboratory at `finitering.space/38-s13/` ships, run from `docs/38-s13` (one source): the pair dynamics, events, octant bridge, precession and the mass–energy channel (84); the sky map, fibered covers, radial ladder and the central product isomorphism (28); the register, cone arithmetic, the winding spectrum and the curl algebra (25); the shell operator core H⁷ = 0, ord(U) = 13, U unitary (25); the two fibrations of the frame variety, Ω-blind at p = 5 (26); the production rendering itself (20) — 208 checks."),
]

md(f"""[![Open In Colab](https://colab.research.google.com/assets/colab-badge.svg)]({COLAB})

## Exact Quantum Dynamics on the Minimal (13,233) Holographic Substrate (Akhtman & Voether, 2026)

**Validation Package.** `finite-ring-space/src/{PKG}` — the paper's seven in-tree audits (four node scripts, integer-exact;
`o1_gr_chart.py`, sympy over the declared continuum chart; `check_phi.py`, the golden-ratio audit; `check_fibrations.py`, the two fibrations) and the laboratory's
six node suites (`docs/{PKG}/verify-*.js`, run from where the laboratory serves them), through one registry: a family
check is one script (`s13.<stem>`) run as its own process, its micro-checks the script's own PASS/FAIL lines together
with the registry's predicates, which pin the stated totals (58, 10, 10, 11, 7, 10, 30; 84, 28, 25, 25, 26, 20 — the
laboratory's 208) and the lines the paper's rows rest on: the quarter roots ħ = 144, h = 89; the apsidal fraction
3/58 = (p−1)/(Ω−1); the per-chronon rate 1/(Ω−1) at (13,233) and (5,233); the face ratio 2 ⟺ 2γ − β = 1; the covering
parity; the winding family. Each family names the row(s) of the paper's predicate ledger it witnesses (the paper's
subsection "Predicate ledger", rows cited as `38:XN`; public copy at `docs/{PKG}/{PKG}-ledger.html`), and the ledger's
source column cites the family ids in return. Master-ledger rows of the corpus sourced from this paper: `00:C16`–`00:C19`,
`00:C22`, `00:C25`, `00:D13`, `00:D14`, `00:E8`, `00:E9`, `00:Y6`.

**Kinds** — two, recorded per family. `EXACT`: integer arithmetic (node, python int), no float behind any claim.
`SYMBOLIC`: exact rationals in sympy over a declared continuum comparison chart ([approx]).

**Run.** Cell by cell, or *Runtime → Run all*; ≈ 30 s on Colab (node and sympy are present there). The last cell writes
`results.json` and fails loudly if any family fails.""")

code(f"""# --- environment: clone the package and the laboratory if this notebook is not already running inside the package (Colab).
import os
if not os.path.exists("s13common.py"):
    if not os.path.exists("finite-ring-space"):
        !git clone --filter=blob:none --sparse https://github.com/gamayos/finite-ring-space.git
        os.chdir("finite-ring-space")
        !git sparse-checkout set src/{PKG} docs/{PKG}
        os.chdir("src/{PKG}")
    else:
        os.chdir("finite-ring-space/src/{PKG}")
print("working directory:", os.path.join(*os.getcwd().split(os.sep)[-3:]))
!node --version""")

code("""import importlib, s13common as gc
importlib.reload(gc)         # a fresh registry if the notebook is re-run
print("families registered:", len(gc.LABELS))""")

def rowkey(r):
    lab = r.split(":")[1]
    return (lab[0], int(re.sub(r"[^0-9]", "", lab) or 0), lab)
for title, stems, desc in GROUPS:
    ids = ["s13." + s for s in stems]
    rows = sorted({r.strip() for i in ids for r in gc.LEDGER[i].split(",")}, key=rowkey)
    table = "| id | script | kind | claim | ledger rows |\n|---|---|---|---|---|\n" + "\n".join(f"| `{i}` | `{gc.FILE[i]}` | {gc.KIND[i]} | {gc.LABELS[i]} | {gc.LEDGER[i]} |" for i in ids)
    md(f"## {title}\n{desc}\n\n{table}\n\nLedger rows witnessed: {', '.join(rows)}.")
    code("for fam in " + json.dumps(ids) + ":\n    print(f\"\\n— {gc.FILE[fam]}\"); gc.run_block(fam)")

md("""## Summary
Writes `results.json` (one record per family: id, the ledger row(s) witnessed, script and path, kind, claim, PASS/FAIL, the check counts) and raises if any family failed.""")
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
