"""
geocommon.py — shared primitives for the 2-geometry validation package
======================================================================
"Geometry and Constants in Finite Ring Continuum" (Akhtman, Symmetry 2026, 18, 751), validation package of the
FRC corpus (finite-ring-space/src/2-geometry), added with the paper's predicate ledger (Appendix A,
17 September 2026), from the corpus script validation/verify_geometry.py.

Each check names the row(s) of the paper's predicate ledger it witnesses (LEDGER below; rows cited as 2:XN),
and the ledger's source column cites the check ids in return.  Where a row is proved in Lean
(lean/FrcLedger/Geometry.lean on Mathlib, or lean/FrcCore with no axioms), the check here is the instance the
reader can run; the witnesses decide the same statements at different generality.

Everything the block scripts share:
  * the shell datum: p = 4κ+1 prime, the primitive generators of F_p, the oriented quarter-turn i = −g^κ,
    the half-period π = 2κ, the phase cycle of length n = p − 1;
  * exact arithmetic in F_p (python int, reduced mod p) and in Q (fractions.Fraction);
  * the PASS/FAIL registry every block reports into (results.json).

Kinds: EXACT checks are integer-pinned computations in F_p or exact rationals (a pass is a proof on the tested
instances); CHART checks decide a [chart] row — the reading of the shell against R or C — in floats with the
closed forms checked.
"""
import os, json, sys, math

# The shells (p, κ): p = 4κ+1 prime.
SHELLS = [(5, 1), (13, 3), (17, 4), (29, 7), (37, 9), (41, 10)]

# ----------------------------------------------------------------------------- registry
RESULTS = []

# The paper's predicate ledger (Appendix A, rows cited as 2:XN): the row(s) each check witnesses.
LEDGER = {
    "A1": "2:D1, 2:D2, 2:D3, 2:D4", "A2": "2:B3", "A3": "2:D5", "A4": "2:D6", "A5": "2:D7", "A6": "2:D8",
    "B1": "2:C2", "B2": "2:C3", "B3": "2:B4, 2:C4",
    "C1": "2:E2", "C2": "2:E3", "C2b": "2:E3", "C3": "2:E4",
    "D1": "2:F1", "D2": "2:F3", "D3": "2:F4", "D4": "2:F5", "D5": "2:F6",
}

def check(pid, label, ok, detail="", kind="EXACT"):
    """Record one predicate check. pid = package check id; LEDGER[pid] = the paper statement(s) decided."""
    ok = bool(ok)
    rows = LEDGER.get(pid, "")
    script = sys._getframe(1).f_globals.get("__name__", "")
    if script == "__main__":
        script = os.path.splitext(os.path.basename(sys.argv[0]))[0]
    RESULTS.append({"id": pid, "rows": rows, "script": script, "label": label, "ok": ok, "detail": detail, "kind": kind})
    print(f"  [{'PASS' if ok else 'FAIL'}] {pid:4s} {kind:6s} [{rows}] {label}" + (f"  --  {detail}" if detail else ""))
    return ok

def summary(write=True):
    n_ok = sum(r["ok"] for r in RESULTS)
    print(f"\nSUMMARY: {n_ok}/{len(RESULTS)} checks passed" + ("" if n_ok == len(RESULTS) else "  <-- FAILURES"))
    if write:
        with open("results.json", "w") as f:
            json.dump(RESULTS, f, indent=1)
    return n_ok == len(RESULTS)

# ----------------------------------------------------------------------------- the shell datum
def is_prime(n):
    return n > 1 and all(n % q for q in range(2, int(n ** .5) + 1))

def order(x, p):
    """The multiplicative order of x in F_p^x."""
    k, y = 1, x % p
    while y != 1:
        y = y * x % p; k += 1
    return k

def generators(p):
    """The primitive generators of F_p^x, in increasing order."""
    return [g for g in range(2, p) if order(g, p) == p - 1]

def units(n):
    """The units of Z_n: u in [1, n) coprime to n."""
    return [u for u in range(1, n) if math.gcd(u, n) == 1]

def kappa(p):
    assert is_prime(p) and p % 4 == 1, p
    return (p - 1) // 4

def quarter_turn(p, g):
    """The oriented quarter-turn i = −g^κ (00:C7, 2:A2)."""
    return (-pow(g, kappa(p), p)) % p

for _p, _k in SHELLS:
    assert is_prime(_p) and _p == 4 * _k + 1, (_p, _k)
