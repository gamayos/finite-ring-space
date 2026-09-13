"""
run_all.py — the 13-epi validation package, end to end
=======================================================
Runs the five blocks, writes results.json — one record per family check, carrying the paper's ledger row(s) it
witnesses — and exits nonzero if any check fails. Pure Python except kurepa_wall.c (compiled on the fly; a pure-Python
fallback to a smaller bound runs without a compiler). ≈ 40 s, of which ≈ 30 s is the C pass over 22 043 primes.

    python3 run_all.py

Blocks:  validate_e        the derangement chain: enclosure, readouts, feasibility, the Kurepa wall, antiperiodicity,
                           duals, the p = 13 line, blind statistics, radian calibration, the null experiment   e.R1–N1
         validate_pi       the Wallis, Machin and arcsin chains, the legibility window and the −2 terminus, Morley
                           and the π-Wieferich search, Lucas revivals, the first-order arcsin vanishing     pi.R1–V1
         validate_pi2      the two-squares quarter invariant, Sun's supercongruence and the Bernoulli law,
                           the proof ingredients, the blind-range Euler congruence, the revival to p²      pi2.A1–D2
         validate_towers   the fixed-shell towers, the Cayley map, orientation transport, the height run,
                           the wrap-free window and the pins                                                 tow.E–W
         kurepa_wall       !(p−1) ≡ K(p) and K(p) ≢ 0 for all 22 043 odd primes p < 2.5·10⁵ (C)                kur.K1
"""
import sys, time
import epicommon

BLOCKS = ["validate_e", "validate_pi", "validate_pi2", "validate_towers", "kurepa_wall"]

def main():
    t0 = time.time()
    for name in BLOCKS:
        mod = __import__(name)
        t = time.time(); print(f"— {name}")
        mod.run()
        print(f"    [{name}: {time.time() - t:.1f} s]")
    ok = epicommon.summary(write=True)
    print(f"{len(epicommon.RESULTS)} family checks, {len(epicommon.MICRO)} exact micro-checks, {time.time() - t0:.0f} s; results.json written")
    sys.exit(0 if ok else 1)

if __name__ == "__main__":
    main()
