"""
algcommon.py — shared primitives for the 1-algebra validation package
=====================================================================
"Relativistic Algebra over Finite Ring Continuum" (Akhtman, Axioms 2025, 14, 636;
doi 10.3390/axioms14080636), validation package of the FRC corpus (finite-ring-space/src/1-algebra),
added with the paper's predicate ledger (Appendix A, 16 September 2026).

Each check names the row(s) of the paper's predicate ledger it witnesses (LEDGER below; rows cited as
1:XN), and the ledger's source column cites the check ids in return. The paper \\label(s) a check decides
are in the block docstrings. Seven master-ledger rows of the corpus cite this paper (00:A8, B1, B8, B11,
C9, C10, Y3); the rows of the paper ledger that the master carries are listed in the site generator.

Everything the block scripts share:
  * the shell datum: p = 4κ+1 prime, the primitive roots of F_p, the oriented quarter-turn i = −g^κ;
  * exact arithmetic in F_p (python int, reduced mod p) and in Q (fractions.Fraction);
  * the PASS/FAIL registry every block reports into (results.json).

Kinds: EXACT checks are integer-pinned computations in F_p or exact rationals (a pass is a proof on the
tested instances); CHART checks decide a [chart] row — a statement about the reading of the shell against
Q or R — in exact rationals.
"""
import os, json, sys

# The shells: p = 4κ+1 prime; the controls: p ≡ 3 (mod 4).
SHELLS = [5, 13, 17, 29, 37, 41, 173]
CONTROLS = [7, 11, 19, 23]

# ----------------------------------------------------------------------------- registry
RESULTS = []

# The paper's predicate ledger (Appendix A, rows cited as 1:XN): the row(s) each check witnesses.
LEDGER = {
    "A1": "1:B2", "A2": "1:B3", "A3": "1:B4", "A4": "1:C2", "A5": "1:C4",
    "B1": "1:D2", "B2": "1:D4", "B3": "1:D6", "B4": "1:E2", "B5": "1:F1", "B6": "1:V1",
    "C1": "1:G1", "C2": "1:G2", "C3": "1:G3", "C4": "1:G4", "C5": "1:G5",
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
    if n < 2: return False
    d = 2
    while d * d <= n:
        if n % d == 0: return False
        d += 1
    return True

def prime_factors(n):
    f, d = set(), 2
    while d * d <= n:
        while n % d == 0:
            f.add(d); n //= d
        d += 1
    if n > 1: f.add(n)
    return f

def primitive_roots(p):
    n = p - 1
    fac = prime_factors(n)
    return [g for g in range(2, p) if all(pow(g, n // q, p) != 1 for q in fac)]

def kappa(p):
    assert p % 4 == 1 and is_prime(p), p
    return (p - 1) // 4

def quarter_turn(p, g):
    """i = −g^κ, the oriented quarter-turn of the frame (τ; 0, 1, g)."""
    return (-pow(g, kappa(p), p)) % p

def sqrt_neg_one(p):
    return sorted(x for x in range(1, p) if (x * x) % p == p - 1)
