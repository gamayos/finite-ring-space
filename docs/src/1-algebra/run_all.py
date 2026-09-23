"""
run_all.py — the 1-algebra validation package, end to end
=========================================================
Runs the three blocks in order, writes results.json (each record carrying the paper's ledger predicate it decides),
and exits nonzero if any check fails.

    python3 run_all.py            # ≈ 10 s on a laptop; python ≥ 3.8, standard library only

Blocks:  A  a_shell.py     the shell, its frame and the orbital complex        EXACT   (1:B2–B4, C2, C4)
         B  b_numbers.py   the framed numbers, the charts and the horizon       EXACT / CHART (1:D2, D4, D5, E2, F1, V1)
         C  c_conjecture.py the conjecture of the conclusion, clause by clause    EXACT / CHART (1:G1–G5)
"""
import sys, time
import algcommon

BLOCKS = ["a_shell", "b_numbers", "c_conjecture"]

def main():
    t0 = time.time()
    for name in BLOCKS:
        mod = __import__(name)
        t = time.time()
        mod.run()
        print(f"    [{name}: {time.time() - t:.1f} s]")
    ok = algcommon.summary(write=True)
    kinds = {}
    for r in algcommon.RESULTS:
        kinds[r["kind"]] = kinds.get(r["kind"], 0) + 1
    print("by kind: " + ", ".join(f"{k} {v}" for k, v in sorted(kinds.items())) + f"; {len(algcommon.RESULTS)} checks in {time.time() - t0:.1f} s; results.json written")
    sys.exit(0 if ok else 1)

if __name__ == "__main__":
    main()
