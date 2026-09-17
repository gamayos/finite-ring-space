"""
run_all.py — the 4-representation validation package, end to end
=================================================================
Runs the three blocks in order, writes results.json (each record carrying the paper's ledger row(s) it decides),
and exits nonzero if any check fails.

    python3 run_all.py            # ≈ 20 s on a laptop; python ≥ 3.8, standard library only

Blocks:  A  a_adequacy.py   adequacy and the Universal Subspace Theorem on every finite model   EXACT  (4:B4–B5, C1–C4)
         B  b_shell.py      the shell as host, the frames as charts, the F_13 instance          EXACT  (4:B6, C1, C3, C5)
         C  c_geometry.py   the hypersphere, the quantisation count, the Gödel code             EXACT/CHART (4:E1–E3)
"""
import sys, time
import repcommon

BLOCKS = ["a_adequacy", "b_shell", "c_geometry"]

def main():
    t0 = time.time()
    for name in BLOCKS:
        mod = __import__(name)
        t = time.time()
        mod.run()
        print(f"    [{name}: {time.time() - t:.1f} s]")
    ok = repcommon.summary(write=True)
    kinds = {}
    for r in repcommon.RESULTS:
        kinds[r["kind"]] = kinds.get(r["kind"], 0) + 1
    print("by kind: " + ", ".join(f"{k} {v}" for k, v in sorted(kinds.items())) + f"; {len(repcommon.RESULTS)} checks in {time.time() - t0:.1f} s; results.json written")
    sys.exit(0 if ok else 1)

if __name__ == "__main__":
    main()
