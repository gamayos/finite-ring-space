"""
run_all.py — the 38-s13 validation package, end to end
======================================================
Runs the thirteen families through the registry (s13common): the six in-tree audits here (four node, three python) and
the laboratory's six node suites at ../../docs/38-s13, writes results.json — one record per family, carrying the
paper's ledger row(s) it witnesses and the script's path — and exits nonzero if any family fails. Needs node (any
LTS) and python ≥ 3.10 with sympy (o1_gr_chart); ≈ 5 s.

    python3 run_all.py
"""
import sys, time
import s13common

FAMILIES = ["s13." + s for s in ["check_s13", "check_o1", "o1_gr_chart", "check_o2", "check_o3", "check_phi",
                                 "check_fibrations",
                                 "verify-233", "verify-sky", "verify-space", "verify-f13", "verify-hopf", "verify-render"]]

def main():
    t0 = time.time()
    for fam in FAMILIES:
        print(f"\n— {s13common.FILE[fam]}")
        s13common.run_block(fam)
    ok = s13common.summary(write=True)
    print(f"{len(s13common.RESULTS)} families, {len(s13common.MICRO)} micro-checks, {time.time() - t0:.0f} s; results.json written")
    sys.exit(0 if ok else 1)

if __name__ == "__main__":
    main()
