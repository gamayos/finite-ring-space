"""
run_all.py — the 6-fourier validation package, end to end
=========================================================
Runs the five blocks in order, regenerates the paper's one numerical figure into figures/, writes
results.json (each record carrying the paper statement it decides and the master-ledger row it
witnesses), and exits nonzero if any check fails.

    python3 run_all.py            # ≈ 5 s on a laptop; numpy only (matplotlib for the figure)

Blocks:  A  a_shell.py        the frame datum and the shell Fourier operator     EXACT   (00:C2, 00:C14)
         B  b_fractional.py   the fractional family F^[s]                        EXACT   (00:C2, 00:C7)
         C  c_domains.py      representation domains and the coordinate zoom     EXACT   (00:C2)
         D  d_weil.py         the Weil dictionary, the operator-level comparison EXACT
         E  e_entropy.py      the cyclotomic observer readout, the entropy cycle EXACT / [approx]
"""
import sys, time
import fcommon

BLOCKS = ["a_shell", "b_fractional", "c_domains", "d_weil", "e_entropy"]

def main():
    t0 = time.time()
    for name in BLOCKS:
        mod = __import__(name)
        t = time.time()
        mod.run()
        print(f"    [{name}: {time.time() - t:.1f} s]")
    ok = fcommon.summary(write=True)
    n = len(fcommon.RESULTS)
    kinds = {}
    for r in fcommon.RESULTS:
        kinds[r["kind"]] = kinds.get(r["kind"], 0) + 1
    print("by kind: " + ", ".join(f"{k} {v}" for k, v in sorted(kinds.items())) + f"; {n} checks in {time.time() - t0:.1f} s; results.json written")
    sys.exit(0 if ok else 1)

if __name__ == "__main__":
    main()
