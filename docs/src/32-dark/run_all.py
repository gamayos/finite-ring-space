"""
run_all.py — the 32-dark validation package, end to end
=======================================================
Runs the thirteen scripts through the registry (darkcommon), writes results.json — one record per family, carrying
the paper's ledger row(s) it witnesses — and exits nonzero if any family fails. Python ≥ 3.10 with numpy, mpmath and
matplotlib (scipy for the exponential-disk curve of deep_mond); ≈ 30 s. The scripts write their figures and
deep.json into out/, the paper's two figures into figures/.

    python3 run_all.py

Families (one per script, in the README's order):
    flux_exact born_exact firstpassage_finite meridian_walk | deep_regime deep_regime_fp | interpolation rar_shape deep_mond
    | rar_scatter cluster_coherent predictions | make_figures
"""
import sys, time
import darkcommon

FAMILIES = ["dark." + s for s in [
    "flux_exact", "born_exact", "firstpassage_finite", "meridian_walk",
    "deep_regime", "deep_regime_fp",
    "interpolation", "rar_shape", "deep_mond",
    "rar_scatter", "cluster_coherent", "predictions",
    "make_figures"]]

def main():
    t0 = time.time()
    for fam in FAMILIES:
        print(f"\n— {darkcommon.script_of(fam)}.py")
        darkcommon.run_block(fam)
    ok = darkcommon.summary(write=True)
    print(f"{len(darkcommon.RESULTS)} families, {len(darkcommon.MICRO)} micro-checks, {time.time() - t0:.0f} s; results.json written")
    sys.exit(0 if ok else 1)

if __name__ == "__main__":
    main()
