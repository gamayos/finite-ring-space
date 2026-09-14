"""Builds 32-dark-main.ipynb (the Colab driver of the 32-dark validation package). Run: python3 make_notebook.py"""
import json, re
import darkcommon as gc

NB = "32-dark-main.ipynb"
PKG = "32-dark"
COLAB = f"https://colab.research.google.com/github/gamayos/finite-ring-space/blob/main/src/{PKG}/{NB}"
cells = []
def md(s): cells.append({"cell_type": "markdown", "metadata": {}, "source": s})
def code(s): cells.append({"cell_type": "code", "metadata": {}, "execution_count": None, "outputs": [], "source": s})

GROUPS = [
    ("The exact core: Gauss law, amplitude = √count, first passage", ["flux_exact", "born_exact", "firstpassage_finite", "meridian_walk"],
     "The discrete Gauss law of the synchronisation flux in exact rationals (Newton as the high-acceleration reading); the amplitude identity |Σ|² = n² coherent, ⟨|Σ|²⟩ = n incoherent, exact in Z[i] — the cross-term cancellation behind the deep-regime square root; the finite-cycle first-passage law at 60 digits (f(e^(−s)) = e^(−arccosh e^s), the √(2s) reduction with rel.err/s → 1/6, the wrap correction of the killed walk on Z_N); the seeded meridian walk collapsing onto e^(−a√(2s)) and the assembled resolved fraction 1 − e^(−√x)."),
    ("The noisy link: registration, not force modification", ["deep_regime", "deep_regime_fp"],
     "The noisy Kuramoto (Adler) link simulated and solved: the mean response is Newtonian at every noise level (deep slopes 1.03 and 1.11 by simulation, exactly 1 by the stationary Fokker–Planck solution), the boost constant to rising — the √ law is a property of registration, not of the mean force."),
    ("The interpolation against the radial acceleration relation", ["interpolation", "rar_shape", "deep_mond"],
     "The interpolation g_obs = g_b/(1 − e^(−√x)) from the rotation angle: deep slope 1/2, Newtonian slope 1, the 0.051 discriminant against the simple rational form at x = 5.2, the two pinning checks of B8; the named test of B8 against the binned SPARC relation (data/RAR.mrt): the exponential form's free a₀ within 10 % of the RAR fit, the departures in the band 2 < x < 10 within the bin scatter; the two-chart Gauss law with a₀ = cH₀/2π, the RAR and BTFR slopes and the exponential-disk rotation curve."),
    ("The scatter, the clusters, the predictions", ["rar_scatter", "cluster_coherent", "predictions"],
     "The SPARC residual test at fixed a₀ = cH₀/2π: intrinsic scatter 0.038 dex, 0.04 at the knee rising to 0.13 in the deep regime, the bound δα ≲ 3.5°, no within-galaxy correlation with 1/V_flat over 116 disks, the 0.14-dex amplitude-sum boost; the coherence-matrix amplitude law N_eff for clusters (the Bullet selection and the core addition in one law, the factor-two closure a conjecture); the falsifiable predictions computed — a₀(z) ∝ H(z), the two-variable scatter law, the wide-binary enhancement with the Galactic external field, the pressure-supported offset."),
    ("The figures", ["make_figures"],
     "The paper's two figures regenerated into figures/: fig_rar.pdf (the RAR with the rational alternative and the exponential-disk rotation curve) and fig_mechanism.pdf (the first-passage collapse and the chart angle)."),
]

md(f"""[![Open In Colab](https://colab.research.google.com/assets/colab-badge.svg)]({COLAB})

## The Dark Sector over Finite Relational Substrate (Akhtman, Geifman & Voether, 2026)

**Validation Package.** `finite-ring-space/src/{PKG}` — the paper's twelve validation scripts and its figure script as written,
run through one registry: a family check is one script (`dark.<stem>`), its micro-checks the script's own verdict lines (four of the
thirteen print one) together with the registry's predicates, which decide the stated values explicitly where a script prints
without asserting — the exact Gauss law and the amplitude identity recomputed, the slopes 1.03/1.11 and the exact slope 1, the
0.051 discriminant and the two pinning checks of B8, the first-passage reduction, the SPARC scatter 0.038 dex and the bound
δα ≲ 3.5°, the prediction numerals; `rar_shape.py`, the named test of row B8 owed by the paper's Appendix A, is delivered here.
Each family names the row(s) of the paper's predicate ledger it witnesses (the paper's Appendix "Predicate ledger", rows cited as
`32:XN`; public copy at `docs/32-dark/32-dark-ledger.html`), and the ledger's source column cites the family ids in return.
Master-ledger rows of the corpus sourced from this paper: `00:L1`, `00:L7`, `00:Z7`, `00:D3`, `00:N1`, `00:N2`.

**Kinds** — three, recorded per family. `EXACT`: exact rationals, Z[i] or 60-digit identities, no tolerance in the verdict.
`SIM`: a seeded stochastic simulation (the noisy link, the killed walk), verdict by stated tolerance. `CHART`: a continuum reading
or a comparison with data (the interpolation, the RAR/BTFR, the SPARC scatter, the predictions, the cluster illustration), tagged
[approx] in the paper, verdict by stated tolerance.

**Run.** Cell by cell, or *Runtime → Run all*; ≈ 30 s on Colab (numpy, mpmath, matplotlib, scipy are present there). The scripts
write their figures and `deep.json` into `out/`, the paper's two figures into `figures/`; every figure a script saves gets a PNG
sibling, shown inline below its family's output. The last cell writes `results.json` and fails loudly if any family fails.""")

code(f"""# --- environment: clone the package if this notebook is not already running inside it (Colab). numpy, mpmath, matplotlib and scipy are present on Colab.
import os
if not os.path.exists("darkcommon.py"):
    if not os.path.exists("finite-ring-space"):
        !git clone --filter=blob:none --sparse https://github.com/gamayos/finite-ring-space.git
        os.chdir("finite-ring-space")
        !git sparse-checkout set src/{PKG}
        os.chdir("src/{PKG}")
    else:
        os.chdir("finite-ring-space/src/{PKG}")
print("working directory:", os.path.join(*os.getcwd().split(os.sep)[-3:]))""")

code("""import importlib, darkcommon as gc
importlib.reload(gc)         # a fresh registry if the notebook is re-run
print("families registered:", len(gc.LABELS))""")

def rowkey(r):
    lab = r.split(":")[1]
    return (lab[0], int(re.sub(r"[^0-9]", "", lab) or 0), lab)
for title, stems, desc in GROUPS:
    ids = ["dark." + s for s in stems]
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
