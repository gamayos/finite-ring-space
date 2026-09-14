"""
run_all.py — the 35-hadrons validation package, end to end
==========================================================
Runs the sixteen scripts through the registry (hadcommon), writes results.json — one record per family, carrying
the paper's ledger row(s) it witnesses — and exits nonzero if any family fails. Python ≥ 3.10 with numpy and sympy
(matplotlib for the figure script); ≈ 40 s, the finite-grid eigenvalue towers dominating. The figure script writes
the paper's two figures into figures/.

    python3 run_all.py

Families (one per script, in the README's order):
    su3_singlet carrier_residue | su3f_relations su3f_second_order hyperfine_charsum isospin_cottingham heavy_flavour
    | em_heavy_cmag absolute_masses vector_nonet subhorizon_resolution | confinement_completion final_resolution
    confinement_closure forward_eigenvalues | make_figures
"""
import sys, time
import hadcommon

FAMILIES = ["had." + s for s in [
    "su3_singlet", "carrier_residue",
    "su3f_relations", "su3f_second_order", "hyperfine_charsum", "isospin_cottingham", "heavy_flavour",
    "em_heavy_cmag", "absolute_masses", "vector_nonet", "subhorizon_resolution",
    "confinement_completion", "final_resolution", "confinement_closure", "forward_eigenvalues",
    "make_figures"]]

def main():
    t0 = time.time()
    for fam in FAMILIES:
        print(f"\n— {hadcommon.script_of(fam)}.py")
        hadcommon.run_block(fam)
    ok = hadcommon.summary(write=True)
    print(f"{len(hadcommon.RESULTS)} families, {len(hadcommon.MICRO)} micro-checks, {time.time() - t0:.0f} s; results.json written")
    sys.exit(0 if ok else 1)

if __name__ == "__main__":
    main()
