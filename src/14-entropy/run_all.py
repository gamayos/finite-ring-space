"""
run_all.py — the 14-entropy validation package, end to end
===========================================================
Runs the three blocks, writes results.json — one record per family check, carrying the paper's ledger row(s) it
witnesses — and exits nonzero if any check fails. Python with matplotlib (the two triangle blocks draw the paper's
figures into out/); ≈ 10 s.

    python3 run_all.py

Blocks:  estimate_S   the exact faces and the area law on the laboratory Carrier; the instrument table, the two
                      concordances, the chart identity, the circularity audit, the channel-1 consistency, the
                      age–rate locus, the floor landing, the octant bound and the running floor       est.F1 … est.P1
         triangle     make-wedge-2: the audit identities, the diagonal regression with its wall intersections,
                      the wall residents; the triangle and wall-channels figures                          tri.A–F
         capacity     make-wedge-3: the same identities re-asserted, the capacity axis and the Avogadro landing;
                      the capacity-axis figure                                                            cap.A–F
"""
import sys, time
import entcommon

BLOCKS = ["estimate_S", "triangle", "capacity"]

def main():
    t0 = time.time()
    for name in BLOCKS:
        mod = __import__(name)
        t = time.time(); print(f"— {name}")
        mod.run()
        print(f"    [{name}: {time.time() - t:.1f} s]")
    ok = entcommon.summary(write=True)
    print(f"{len(entcommon.RESULTS)} family checks, {len(entcommon.MICRO)} micro-checks, {time.time() - t0:.0f} s; results.json written")
    sys.exit(0 if ok else 1)

if __name__ == "__main__":
    main()
