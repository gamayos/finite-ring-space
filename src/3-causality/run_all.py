"""
run_all.py — the 3-causality validation package, end to end
===========================================================
Runs the four blocks in order, writes results.json (each record carrying the paper's ledger row(s) it decides),
and exits nonzero if any check fails.

    python3 run_all.py            # ≈ 10 s on a laptop; python ≥ 3.8, standard library only

Blocks:  A  a_classes.py    the square classes and the nonexistence theorem     EXACT  (3:B1–B3)
         B  b_signature.py  the signature on the shell and in the extension     EXACT  (3:B4–B7)
         C  c_boost.py      the finite Lorentz boosts                           EXACT  (3:C2–C5)
         D  d_example.py    the worked shell F_13                               EXACT  (3:D1)
"""
import sys, time
import lcommon

BLOCKS = ["a_classes", "b_signature", "c_boost", "d_example"]

def main():
    t0 = time.time()
    for name in BLOCKS:
        mod = __import__(name)
        t = time.time()
        mod.run()
        print(f"    [{name}: {time.time() - t:.1f} s]")
    ok = lcommon.summary(write=True)
    kinds = {}
    for r in lcommon.RESULTS:
        kinds[r["kind"]] = kinds.get(r["kind"], 0) + 1
    print("by kind: " + ", ".join(f"{k} {v}" for k, v in sorted(kinds.items())) + f"; {len(lcommon.RESULTS)} checks in {time.time() - t0:.1f} s; results.json written")
    sys.exit(0 if ok else 1)

if __name__ == "__main__":
    main()
