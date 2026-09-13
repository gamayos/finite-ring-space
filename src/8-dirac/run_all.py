"""
run_all.py — the 8-dirac validation package, end to end
=======================================================
Runs the eight blocks in order (exact integer arithmetic throughout; ≈ 1 min on a laptop, the p = 5 spinor
matrices of o8 and the p < 2000 shell scans of o2/o7 the longest), writes results.json — one record per
family check, carrying the paper's ledger row(s) it witnesses — and exits nonzero if any check fails.

    python3 run_all.py

Blocks:  worked_checks        the F_13 worked examples (finite_checks.py as the library)      fin.S1–S3
         shell_checks         the free evolution is the drive; the F_17 numbers               shell.Z1–Z4
         o2_checks            the canonical Lorentzian coefficient ν = g                     o2.C1–C9
         o7_checks            the parity grading and the two speed-of-light seats             o7.P1–P6
         o134_checks          boost torus, Cayley transform, orbit periods                    o134.O1a–O4d
         o8_checks            symmetric Dirac dynamics and the spinor form                    o8.X1–X8
         latitude_checks      the latitude indices of the shell reading                       lat.L1–L5
         o9_signature_counts  signature as a square-class dichotomy                           o9.S1–S4
"""
import sys, time
import dcommon

BLOCKS = ["worked_checks", "shell_checks", "o2_checks", "o7_checks", "o134_checks", "o8_checks", "latitude_checks", "o9_signature_counts"]

def main():
    t0 = time.time()
    for name in BLOCKS:
        mod = __import__(name)
        t = time.time()
        print(f"— {name}")
        mod.run()
        print(f"    [{name}: {time.time() - t:.1f} s]")
    ok = dcommon.summary(write=True)
    print(f"{len(dcommon.RESULTS)} family checks, {len(dcommon.MICRO)} exact micro-checks, {time.time() - t0:.0f} s; results.json written")
    sys.exit(0 if ok else 1)

if __name__ == "__main__":
    main()
