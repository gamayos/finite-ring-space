"""
run_all.py — the 20-rh validation package, end to end
=====================================================
Runs the five blocks in order, regenerates every numerical figure of the paper into figures/,
writes results.json (each record carrying the paper's ledger row it witnesses), and exits nonzero if any
check fails.

    python3 run_all.py            # full depths (≈ 6–8 min on a laptop; 8×10⁷ comb in block D)
    RH_FAST=1 python3 run_all.py  # reduced depths (≈ 3 min)

Blocks:  A  a_shell.py          the shell theorem, exact shell arithmetic        (00:D11)
         B  b_deframe.py        the de-framing dictionary                        [chart]/[approx]
         C  c_primeside.py      the spectrum from the prime side, ζ never evaluated
            c_gue.py            GUE statistics of the target spectrum
            c_chi.py            the χ-twisted comb (generalized hypothesis)
         D  d_classification.py Turing's count, the phantom, the DH controls     (00:D12)
         E  e_resonance.py      resonance, antipode, horizon, √p-flatness
"""
import sys, time
import rhcommon

BLOCKS = ["a_shell", "b_deframe", "c_primeside", "c_gue", "c_chi", "d_classification", "e_resonance"]

def main():
    t0 = time.time()
    for name in BLOCKS:
        mod = __import__(name)
        t = time.time()
        mod.run()
        print(f"    [{name}: {time.time() - t:.0f} s]")
    ok = rhcommon.summary(write=True)
    n = len(rhcommon.RESULTS)
    kinds = {}
    for r in rhcommon.RESULTS:
        kinds[r["kind"]] = kinds.get(r["kind"], 0) + 1
    print("by kind: " + ", ".join(f"{k} {v}" for k, v in sorted(kinds.items())) + f"; {n} checks in {time.time() - t0:.0f} s; results.json written")
    sys.exit(0 if ok else 1)

if __name__ == "__main__":
    main()
