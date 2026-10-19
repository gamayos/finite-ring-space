"""Builds 35-hadrons-main.ipynb (the Colab driver of the 35-hadrons validation package). Run: python3 make_notebook.py"""
import json, re
import hadcommon as gc

NB = "35-hadrons-main.ipynb"
PKG = "35-hadrons"
COLAB = f"https://colab.research.google.com/github/gamayos/finite-ring-space/blob/main/src/{PKG}/{NB}"
cells = []
def md(s): cells.append({"cell_type": "markdown", "metadata": {}, "source": s})
def code(s): cells.append({"cell_type": "code", "metadata": {}, "execution_count": None, "outputs": [], "source": s})

GROUPS = [
    ("The colour frame and the baryon residue", ["su3_singlet", "carrier_residue"],
     "Colour SU(3,F_2) built exhaustively over F_4 (order 216, centre Z_3): the colour-singlet rule is centre neutrality (triality 0), the baryon the ε_abc invariant; the fundamental carries no invariant line and Λ³ = det is the one-dimensional invariant, so the baryon is the Carrier residue 1 forced by the gluon residue 0, the colourless content of Λ^k(3) being (1, 0, 0, 1) — the residue series photon 2, gluon 0, baryon 1. Finite-field arithmetic only."),
    ("The SU(3)_F relations, the hyperfine pattern, isospin and heavy flavour", ["su3f_relations", "su3f_second_order", "hyperfine_charsum", "isospin_cottingham", "heavy_flavour"],
     "The scale-cancelling identities in exact rationals and sympy: Gell-Mann–Okubo and the decuplet equal spacing (PDG 0.57 %, 9.2 %), the third-difference relation and the octet–decuplet hyperfine links (6 MeV, 0.36 %), the colour factor −8 with the spin structure ∓3/4 and separation 3/2 (A_light = 195 MeV), Coleman–Glashow with the orderings M_n > M_p and M_Σ > M_Λ (0.79 %), heavy-quark symmetry and the 1/m_Q ratio (2.4 %, 0.339)."),
    ("The absolute scales, the spectrum, the vector nonet, the discriminator", ["em_heavy_cmag", "absolute_masses", "vector_nonet", "subhorizon_resolution"],
     "The electromagnetic charge structure and the adjoint coefficient β²/36 against the tension β/18 (no new residue); the absolute octet and decuplet from one scale and two ratios, five predictions within 1.1 %; the meson as residue 1 and the vector equal spacing 2M_K* = M_ρ + M_φ (0.42 %); the Ω-stability discriminator — N = 3 on every admissible shell, the residuals O(ε_s²)."),
    ("The confinement completion: the finite-grid eigenvalue towers", ["confinement_completion", "final_resolution", "confinement_closure", "forward_eigenvalues"],
     "The single-scale reduction with the exact Λ–N gap 176.8 MeV; the linear-potential tower on the finite grid reproducing the Airy zeros [profinite approx]; the terminal classification (two kinds of sub-horizon residue, nothing open); the baryon scale as the converged eigenvalue E₀ = 2.232 of H_G = T_G^{1/2} + R_G (M_N to 4.6 %); the forward evaluation of λ_l, λ_hf from {N = 3, β} with no measured baryon mass — the script's ten checks."),
    ("The figures", ["make_figures"],
     "The paper's two figures regenerated into figures/ from the exact values: fig_spectrum.pdf (FRC against PDG for the octet, the decuplet and the vector nonet) and fig_strangeness.pdf (mass against strangeness, the two equal spacings), shown inline."),
]

md(f"""[![Open In Colab](https://colab.research.google.com/assets/colab-badge.svg)]({COLAB})

## Ground-State Light Hadron Spectroscopy over Finite Substrate (Akhtman & Voether, 2026)

**Validation Package.** `finite-ring-space/src/{PKG}` — the paper's fifteen validation scripts and its figure script as
written, run through one registry: a family check is one script (`had.<stem>`), its micro-checks the script's own
verdict lines (fourteen assert their identities and print a report; `forward_eigenvalues` prints one `[PASS]` line per
check) together with the registry's predicates, which decide the stated values explicitly — the group order 216 and
the centre Z_3, the colourless content (1, 0, 0, 1), the five identities and their PDG residuals, the colour factor −8
and the spin pattern ∓3/4, the coefficients 1/18 and 1/36, the spectrum within 1.1 %, the Λ–N gap, the Airy tower, the
baryon eigenvalue E₀ = 2.232 and the forward landings. Each family names the row(s) of the paper's predicate ledger it
witnesses (the paper's Appendix "Predicate ledger", rows cited as `35:XN`; public copy at
`docs/35-hadrons/35-hadrons-ledger.html`), and the ledger's source column cites the family ids in return.
Master-ledger rows of the corpus sourced from this paper: `00:I5`, `00:I6`, `00:I7`.

**Kinds** — four, recorded per family. `EXACT`: finite-field (F_4), integer or exact-rational identities only, no
float in the script. `MIXED`: an exact core (the asserted identity) with a labelled [approx] decimal display of the
PDG confrontation, verdict on the core and on the stated residual by tolerance. `PROFINITE`: additionally a labelled
[profinite approx] finite-grid eigenvalue (numpy linear algebra over a finite matrix), verdict by stated tolerance.
`CHART`: the figure script.

**Run.** Cell by cell, or *Runtime → Run all*; ≈ 20 s on Colab (numpy, sympy and matplotlib are present there). The
figure script writes the paper's two figures into `figures/`, each with a PNG sibling shown inline below its output.
The last cell writes `results.json` and fails loudly if any family fails.""")

code(f"""# --- environment: clone the package if this notebook is not already running inside it (Colab). numpy, sympy and matplotlib are present on Colab.
import os
if not os.path.exists("hadcommon.py"):
    if not os.path.exists("finite-ring-space"):
        !git clone --filter=blob:none --sparse https://github.com/gamayos/finite-ring-space.git
        os.chdir("finite-ring-space")
        !git sparse-checkout set src/{PKG}
        os.chdir("src/{PKG}")
    else:
        os.chdir("finite-ring-space/src/{PKG}")
print("working directory:", os.path.join(*os.getcwd().split(os.sep)[-3:]))""")

code("""import importlib, hadcommon as gc
importlib.reload(gc)         # a fresh registry if the notebook is re-run
print("families registered:", len(gc.LABELS))""")

def rowkey(r):
    lab = r.split(":")[1]
    return (lab[0], int(re.sub(r"[^0-9]", "", lab) or 0), lab)
for title, stems, desc in GROUPS:
    ids = ["had." + s for s in stems]
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
