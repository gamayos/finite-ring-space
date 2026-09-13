"""
run_all.py — the 10-dimensions validation package, end to end
=============================================================
Runs the two exact suites, writes results.json — one record per family check, carrying the paper's ledger
row(s) it witnesses — and exits nonzero if any check fails.  Pure Python, ≈ 5 s.

    python3 run_all.py

Blocks:  verify_domains   layers A–H, 200 exact micro-checks (F_13, p = 29, 229; Carriers 233 and 2 408 561)   dom.A–H
         check_lift       Proposition `lift`, L1–L5 on the shells (13, 2), (173, 3) and both Carriers           lift.L1–L5
check_gates.py (105 source gates on the manuscript text) runs in the corpus tree only.
"""
import sys, time
import dimcommon

BLOCKS = ["verify_domains", "check_lift"]

def main():
    t0 = time.time()
    for name in BLOCKS:
        mod = __import__(name)
        t = time.time(); print(f"— {name}")
        mod.run()
        print(f"    [{name}: {time.time() - t:.1f} s]")
    ok = dimcommon.summary(write=True)
    print(f"{len(dimcommon.RESULTS)} family checks, {len(dimcommon.MICRO)} exact micro-checks, {time.time() - t0:.0f} s; results.json written")
    sys.exit(0 if ok else 1)

if __name__ == "__main__":
    main()
