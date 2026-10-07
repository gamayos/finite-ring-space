"""
run_all.py — the 22-quantum validation package, end to end
===========================================================
Runs the seventeen suites through the registry (qmcommon), writes results.json — one record per family, carrying the
paper's ledger row(s) it witnesses — and exits nonzero if any family fails. Python ≥ 3.10 with numpy and sympy;
≈ 1 minute (intersubject and decoherence dominate).

    python3 run_all.py

Families (one per suite, in the README's order):
    validate sorkin dispersion composite synchronisation renou bmv decoherence equivalence granularity stratum
    gravfraction gleason emulation omega intersubject transport
"""
import sys, time
import qmcommon

FAMILIES = ["qm." + s for s in [
    "validate", "sorkin", "dispersion", "composite", "synchronisation", "renou", "bmv", "decoherence", "equivalence",
    "granularity", "stratum", "gravfraction", "gleason", "emulation", "omega", "intersubject", "transport"]]

def main():
    t0 = time.time()
    for fam in FAMILIES:
        print(f"\n— {qmcommon.script_of(fam)}.py")
        qmcommon.run_block(fam)
    ok = qmcommon.summary(write=True)
    print(f"{len(qmcommon.RESULTS)} families, {len(qmcommon.MICRO)} micro-checks, {time.time() - t0:.0f} s; results.json written")
    sys.exit(0 if ok else 1)

if __name__ == "__main__":
    main()
