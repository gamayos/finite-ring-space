"""
run_all.py — the 5-reductio validation package, end to end
==========================================================
Runs the four blocks in order, writes results.json (each record carrying the paper's ledger row(s) it decides),
and exits nonzero if any check fails.

    python3 run_all.py            # ≈ 60 s on a laptop; python ≥ 3.8, standard library only

Blocks:  A  a_frames.py       the frames, their theories, stability, the migration, the horizon   EXACT  (5:B3, B5, B6, C2, C3, C5)
         B  b_paradox.py      the normal forms on a finite universe                              EXACT  (5:D2, D3, D4, D9, E8)
         C  c_choice.py       choice recovered on finite and periodic structures                 EXACT  (5:E1–E6)
         D  d_determinacy.py  determinacy on the finite totality; the Π₁ verdicts frame by frame  EXACT  (5:D8, B7)
"""
import sys, time
import redcommon

BLOCKS = ["a_frames", "b_paradox", "c_choice", "d_determinacy"]

def main():
    t0 = time.time()
    for name in BLOCKS:
        mod = __import__(name)
        t = time.time()
        mod.run()
        print(f"    [{name}: {time.time() - t:.1f} s]")
    ok = redcommon.summary(write=True)
    kinds = {}
    for r in redcommon.RESULTS:
        kinds[r["kind"]] = kinds.get(r["kind"], 0) + 1
    print("by kind: " + ", ".join(f"{k} {v}" for k, v in sorted(kinds.items())) + f"; {len(redcommon.RESULTS)} checks in {time.time() - t0:.1f} s; results.json written")
    sys.exit(0 if ok else 1)

if __name__ == "__main__":
    main()
