"""
run_all.py — the 28-flavour validation package, end to end
==========================================================
Runs the sixteen scripts through the registry (flvcommon), writes results.json — one record per family, carrying
the paper's ledger row(s) it witnesses — and exits nonzero if any family fails. Python ≥ 3.10 with numpy, sympy and scipy (tm2_jointfit);
≈ 1 minute (pmns_cp dominates).

    python3 run_all.py

Families (one per script, in the README's order):
    exact_core framed_koide | tier_b m10 delta revision_checks | quark_amp up_doubling spurion theta13 | neutrino pmns_cp
    tm2_jointfit | scale_a coupling_anchor alpha_probe
"""
import sys, time
import flvcommon

FAMILIES = ["flv." + s for s in [
    "exact_core", "framed_koide",
    "tier_b", "m10", "delta", "revision_checks",
    "quark_amp", "up_doubling", "spurion", "theta13",
    "neutrino", "pmns_cp", "tm2_jointfit",
    "scale_a", "coupling_anchor", "alpha_probe"]]

def main():
    t0 = time.time()
    for fam in FAMILIES:
        print(f"\n— {flvcommon.script_of(fam)}.py")
        flvcommon.run_block(fam)
    ok = flvcommon.summary(write=True)
    print(f"{len(flvcommon.RESULTS)} families, {len(flvcommon.MICRO)} micro-checks, {time.time() - t0:.0f} s; results.json written")
    sys.exit(0 if ok else 1)

if __name__ == "__main__":
    main()
