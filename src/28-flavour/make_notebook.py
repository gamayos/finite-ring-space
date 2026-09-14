"""Builds 28-flavour-main.ipynb (the Colab driver of the 28-flavour validation package). Run: python3 make_notebook.py"""
import json, re
import flvcommon as gc

NB = "28-flavour-main.ipynb"
PKG = "28-flavour"
COLAB = f"https://colab.research.google.com/github/gamayos/finite-ring-space/blob/main/src/{PKG}/{NB}"
cells = []
def md(s): cells.append({"cell_type": "markdown", "metadata": {}, "source": s})
def code(s): cells.append({"cell_type": "code", "metadata": {}, "execution_count": None, "outputs": [], "source": s})

GROUPS = [
    ("The float-free core", ["exact_core", "framed_koide"],
     "The Koide and circulant identities in Q(ω, √2) and over framed rationals in F_{p²}/F_p; the π/12 boundary; the cubic Gauss sums as integer group-ring identities; the trimaximal magic matrix with maximal Jarlskog; the amplitude diagonal N(1 − ζ_n) = 2, 3 as integers in F_p."),
    ("The charged sectors: Koide, the winding kernel, the phase lock", ["tier_b", "m10", "delta", "revision_checks"],
     "The Tier-A/B figures against data; the circulant winding kernel with δ_LO = π/12 and the per-sector extraction; the cross-sector phase lock 1 : 1/2 : 1/3 and the small-shell quantisation; the revision identities (J, δ_LO = 1/24, the signed Koide, the cube invariant) with their labelled confrontations."),
    ("The quark sector: amplitudes, doubling, the spurion, the reactor angle", ["quark_amp", "up_doubling", "spurion", "theta13"],
     "The colour dressing of the quark amplitudes (r_u ≈ √3, Q_u = 5/6 in framed arithmetic); the up-sector doubling from 10·10; the Cabibbo spurion folded onto the winding kernel; θ₁₃ = θ_C/√2 as a leading-order estimate."),
    ("The neutrino sector and leptonic CP", ["neutrino", "pmns_cp", "tm2_jointfit"],
     "The seesaw of circulants; Q_ν = 2/3 solved on both orderings with the boundary branch selecting normal, Σm_ν = 59.1 meV; the magic matrix and maximal Jarlskog; the TM2 relation locking δ_CP to θ₂₃, its band and the joint-fit status."),
    ("The scales: transmutation, the coupling anchor, the fine-structure ledger", ["scale_a", "coupling_anchor", "alpha_probe"],
     "The overall scale as a transmutation exponent with y_t ≈ 1; the bare 1/4π against the unified continuum coupling; the α ledger — the 4π anchor, the electroweak decomposition, 3/8 at unification, the one-loop fermion sum, the 10³⁶ hierarchy."),
]

md(f"""[![Open In Colab](https://colab.research.google.com/assets/colab-badge.svg)]({COLAB})

## Fermion Flavour Sector over Finite Relational Substrate (Akhtman & Voether, 2026)

**Validation Package.** `finite-ring-space/src/{PKG}` — the paper's sixteen validation scripts as written, run through one registry: a
family check is one script (`flv.<stem>`), its micro-checks the script's own verdict lines (twelve of the sixteen print one per check)
together with the registry's predicates, which decide the stated values explicitly where a script prints without asserting
(`framed_koide`, `theta13`, `scale_a`, `coupling_anchor`) and pin the headline numerals elsewhere; each family names the row(s) of the
paper's predicate ledger it witnesses (the paper's Appendix "Predicate ledger", rows cited as `28:XN`; public copy at
`docs/28-flavour/28-flavour-ledger.html`), and the ledger's source column cites the family ids in return. Master-ledger rows of the
corpus reached through the paper rows: `00:K2`, `00:K3`, `00:K4`, `00:J2`, `00:J4`, `00:D2`, `00:D8`, `00:Z6`, `00:Z8`, `00:C7`, `00:B5`.

**Kinds** — the suite's own three classes, recorded per family. `EXACT`: integer, F_p, F_{{p²}} or cyclotomic arithmetic throughout, no
float in any asserted claim. `MIXED`: the script carries its own exact check for at least one claim, the continuum confined to
labelled [approx] comparisons. `APPROX`: continuum/numerical by construction — a numerical reconfirmation of an identity proven
exactly in `exact_core`, a comparison with measured data, or an Ω-hard reading.

**Run.** Cell by cell, or *Runtime → Run all*; ≈ 1 minute on Colab (`pmns_cp` is the long one; `tm2_jointfit` needs scipy). The last
cell writes `results.json` and fails loudly if any family fails.""")

code(f"""# --- environment: clone the package if this notebook is not already running inside it (Colab). numpy, sympy and scipy are present on Colab.
import os
if not os.path.exists("flvcommon.py"):
    if not os.path.exists("finite-ring-space"):
        !git clone --filter=blob:none --sparse https://github.com/gamayos/finite-ring-space.git
        os.chdir("finite-ring-space")
        !git sparse-checkout set src/{PKG}
        os.chdir("src/{PKG}")
    else:
        os.chdir("finite-ring-space/src/{PKG}")
print("working directory:", os.path.join(*os.getcwd().split(os.sep)[-3:]))""")

code("""import importlib, flvcommon as gc
importlib.reload(gc)         # a fresh registry if the notebook is re-run
print("families registered:", len(gc.LABELS))""")

def rowkey(r):
    lab = r.split(":")[1]
    return (lab[0], int(re.sub(r"[^0-9]", "", lab) or 0), lab)
for title, stems, desc in GROUPS:
    ids = ["flv." + s for s in stems]
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
