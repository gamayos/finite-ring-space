"""
run_all.py — the 2-geometry validation package, end to end
==========================================================
Runs the four blocks in order, writes results.json (each record carrying the paper's ledger row(s) it decides),
and exits nonzero if any check fails.

    python3 run_all.py            # ≈ 20 s on a laptop; python ≥ 3.8, standard library only

Blocks:  A  a_datum.py    the Euclidean datum and the involutions         EXACT         (2:B3, D1–D8)
         B  b_shell.py    the orbital shell and its completion            EXACT         (2:B4, C2–C4)
         C  c_charts.py   the external spherical comparison               CHART / EXACT (2:E2–E4)
         D  d_fourier.py  Fourier duality on the phase cycle              EXACT / CHART (2:F1, F3–F6)
"""
import sys, time
import geocommon

BLOCKS = ["a_datum", "b_shell", "c_charts", "d_fourier"]

def main():
    t0 = time.time()
    for name in BLOCKS:
        mod = __import__(name)
        t = time.time()
        mod.run()
        print(f"    [{name}: {time.time() - t:.1f} s]")
    ok = geocommon.summary(write=True)
    kinds = {}
    for r in geocommon.RESULTS:
        kinds[r["kind"]] = kinds.get(r["kind"], 0) + 1
    print("by kind: " + ", ".join(f"{k} {v}" for k, v in sorted(kinds.items())) + f"; {len(geocommon.RESULTS)} checks in {time.time() - t0:.1f} s; results.json written")
    sys.exit(0 if ok else 1)

if __name__ == "__main__":
    main()
