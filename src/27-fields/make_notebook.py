"""Builds 27-fields-main.ipynb (the Colab driver of the 27-fields validation package). Run: python3 make_notebook.py"""
import json, re
import fldcommon as gc

NB = "27-fields-main.ipynb"
PKG = "27-fields"
COLAB = f"https://colab.research.google.com/github/gamayos/finite-ring-space/blob/main/src/{PKG}/{NB}"
cells = []
def md(s): cells.append({"cell_type": "markdown", "metadata": {}, "source": s})
def code(s): cells.append({"cell_type": "code", "metadata": {}, "execution_count": None, "outputs": [], "source": s})

GROUPS = [
    ("Electromagnetism: gauging the phase frame", ["em1_prototype", "enumerate_maxwell", "audit_finitism", "o2_numbers", "p2"],
     "The finite U(1) prototype (gauge invariance, discrete Stokes, the Coulomb coefficient, the sign dichotomy); the uniqueness of the Maxwell operator by exact corank; the finitism cross-check with no float; the bare coupling 1/4π as phase-channel capacity and its order-one coefficient."),
    ("The finite gauge correspondence", ["correspondence"],
     "The abelian inclusion, the exact q = 3 embedding SU(2,F₃) = 2T, the low-curvature Yang–Mills term, exact gauge invariance, the window residue, the area law from positivity, the character lift and the finite quadrature — the continuum-comparison layer by construction."),
    ("The weak interaction: gauging the spinor frame", ["p3", "ew1", "weak_spectrum", "weak_current", "p4", "p10", "v_scale"],
     "The cell-local SU(2,F₃) connection; breaking as drive–torus misalignment over F₁₃ with ρ = 1 and sin²θ_W = 3/8; the propagating W, Z spectrum as the Hessian of S_ρ; the V−A current, the chiral projector and G_F; maximal parity violation from the Frobenius branch; chirality selection; the electroweak scale against the transmutation forms (conjecture O1)."),
    ("The strong interaction: confinement and the colour rank", ["qcd", "p5", "string_tension", "p6", "missing_rank"],
     "SU(3,2) enumerated over F₄ with its Z₃ centre; the gluon connection and its self-coupling; the string tension in finite units (2T closed form, the SU(3) series); asymptotic freedom and the QCD scale; the rank tower and SU(3,5) on the smallest admissible shell."),
    ("The generation, unification, and the flavour results", ["generation", "p8", "p8b", "p9", "p9b", "p11", "p1", "p7", "koide", "strongcp"],
     "One generation as the spinor 16 with anomaly freedom and 3/8; the spinorial unification argument and the X, Y off-block; generations as Galois conjugates and the 1 + 3 role split; the substrate residue Ω ≡ 5 (mod 12); the one-loop running; the mass mechanism; the framed-rational Koide identity; the vanishing strong-CP angle."),
]

md(f"""[![Open In Colab](https://colab.research.google.com/assets/colab-badge.svg)]({COLAB})

## Standard-Model Interactions over Finite Relational Substrate (Akhtman & Voether, 2026)

**Validation Package.** `finite-ring-space/src/{PKG}` — the paper's twenty-eight validation scripts as written, run through one registry:
a family check is one script (`fld.<stem>`), its micro-checks the script's own PASS/FAIL lines together with the registry's predicates,
which read the script's namespace and output and decide the manuscript's stated values explicitly (most of the scripts print their
booleans and numbers without asserting them, so the decision is made in `fldcommon.py`, in the open); each family names the row(s) of
the paper's predicate ledger it witnesses (the paper's Section "Status", subsection "Predicate ledger", rows cited as `27:XN`; public
copy at `docs/27-fields/27-fields-ledger.html`), and the ledger's source column cites the family ids in return; the paper's Appendix
"Reproducibility map" is the per-script map. Master-ledger rows of the corpus reached through the paper rows: `00:B5`, `00:H1`, `00:H2`,
`00:H3`, `00:I1`, `00:I2`, `00:I4`, `00:J1`, `00:J4`, `00:K2`, `00:G1`, `00:E1`, `00:E3`, `00:D6`, `00:N1`, `00:Z5`, `00:Z8`.

**Kinds** — the paper's own three classes, recorded per family. `EXACT`: integer, F_p, F_{{p²}} or cyclotomic arithmetic throughout, a
pass a proof on the tested instances. `MIXED`: an exact core with a labelled continuum-comparison layer ([approx] against published
constants or a continuum reading), the exact claim never resting on the float part. `APPROX`: a continuum-comparison or
dimensional-transmutation reading by construction (the finite-window correspondence, the electroweak scale).

**Run.** Cell by cell, or *Runtime → Run all*; ≈ 1.5 minutes on Colab (`enumerate_maxwell` is the long one). The last cell writes
`results.json` and fails loudly if any family fails.""")

code(f"""# --- environment: clone the package if this notebook is not already running inside it (Colab). numpy and sympy are present on Colab.
import os
if not os.path.exists("fldcommon.py"):
    if not os.path.exists("finite-ring-space"):
        !git clone --filter=blob:none --sparse https://github.com/gamayos/finite-ring-space.git
        os.chdir("finite-ring-space")
        !git sparse-checkout set src/{PKG}
        os.chdir("src/{PKG}")
    else:
        os.chdir("finite-ring-space/src/{PKG}")
print("working directory:", os.path.join(*os.getcwd().split(os.sep)[-3:]))""")

code("""import importlib, fldcommon as gc
importlib.reload(gc)         # a fresh registry if the notebook is re-run
print("families registered:", len(gc.LABELS))""")

def rowkey(r):
    lab = r.split(":")[1]
    return (lab[0], int(re.sub(r"[^0-9]", "", lab) or 0), lab)
for title, stems, desc in GROUPS:
    ids = ["fld." + s for s in stems]
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
