"""
run_all.py — the 27-fields validation package, end to end
==========================================================
Runs the twenty-eight scripts through the registry (fldcommon), writes results.json — one record per family, carrying
the paper's ledger row(s) it witnesses — and exits nonzero if any family fails. Python ≥ 3.10 with numpy and sympy;
≈ 1.5 minutes (enumerate_maxwell dominates).

    python3 run_all.py

Families (one per script, in the README's order):
    em1_prototype enumerate_maxwell audit_finitism o2_numbers p2 | correspondence | p3 ew1 weak_spectrum weak_current
    p4 p10 v_scale | qcd p5 string_tension p6 missing_rank | generation p8 p8b p9 p9b p11 p1 p7 koide strongcp
"""
import sys, time
import fldcommon

FAMILIES = ["fld." + s for s in [
    "em1_prototype", "enumerate_maxwell", "audit_finitism", "o2_numbers", "p2",
    "correspondence",
    "p3", "ew1", "weak_spectrum", "weak_current", "p4", "p10", "v_scale",
    "qcd", "p5", "string_tension", "p6", "missing_rank",
    "generation", "p8", "p8b", "p9", "p9b", "p11", "p1", "p7", "koide", "strongcp"]]

def main():
    t0 = time.time()
    for fam in FAMILIES:
        print(f"\n— {fldcommon.script_of(fam)}.py")
        fldcommon.run_block(fam)
    ok = fldcommon.summary(write=True)
    print(f"{len(fldcommon.RESULTS)} families, {len(fldcommon.MICRO)} micro-checks, {time.time() - t0:.0f} s; results.json written")
    sys.exit(0 if ok else 1)

if __name__ == "__main__":
    main()
