"""
lcommon.py — shared primitives for the 3-causality validation package
=====================================================================
"Euclidean–Lorentzian Dichotomy and Algebraic Causality in Finite Ring Continuum" (Akhtman, Entropy 2025, 27, 1098),
validation package of the FRC corpus (finite-ring-space/src/3-causality), added with the paper's predicate ledger
(Appendix A, 17 September 2026).

Each check names the row(s) of the paper's predicate ledger it witnesses (LEDGER below; rows cited as 3:XN), and
the ledger's source column cites the check ids in return.  Where a row is proved in Lean (lean/FrcCore, no axioms;
lean/FrcLedger/Causality.lean on Mathlib), the check here is the instance the reader can run.

Everything the block scripts share:
  * the shell datum: p = 4κ+1 prime, the square classes S = (F_p^×)² and N = F_p^× \ S, the primitive generators;
  * the quadratic extension K = F_p(√ν) = F_{p²} as pairs (a, b) = a + b√ν, with its Frobenius conjugation and norm;
  * the diagonal form Q_ν(t, x, y, z) = −ν t² + x² + y² + z² and the value distributions that count its zeros;
  * the PASS/FAIL registry every block reports into (results.json).

Kinds: EXACT checks are integer-pinned computations in F_p, F_{p²} or exact rationals (a pass is a proof on the
tested instances); CHART checks decide a [chart] row.
"""
import os, json, sys, math

# The shells (p, κ): p = 4κ+1 prime.
SHELLS = [(5, 1), (13, 3), (17, 4), (29, 7), (37, 9), (41, 10)]

# ----------------------------------------------------------------------------- registry
RESULTS = []

# The paper's predicate ledger (Appendix A, rows cited as 3:XN): the row(s) each check witnesses.
LEDGER = {
    "A1": "3:B2", "A2": "3:B3", "A3": "3:B1", "A4": "3:B2",
    "B1": "3:B4", "B2": "3:B5", "B3": "3:B6", "B4": "3:B7", "B5": "3:B5",
    "C1": "3:C2", "C2": "3:C2", "C3": "3:C3", "C4": "3:C5", "C5": "3:C4",
    "D1": "3:D1", "D2": "3:D1",
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
    k, y = 1, x % p
    while y != 1:
        y = y * x % p; k += 1
    return k

def generators(p):
    """The primitive generators of F_p^x, in increasing order."""
    return [g for g in range(2, p) if order(g, p) == p - 1]

def squares(p):
    """The nonzero squares S = (F_p^x)^2."""
    return sorted({x * x % p for x in range(1, p)})

def nonsquares(p):
    S = set(squares(p))
    return [x for x in range(1, p) if x not in S]

def is_square(x, p):
    return x % p != 0 and pow(x % p, (p - 1) // 2, p) == 1

def kappa(p):
    assert is_prime(p) and p % 4 == 1, p
    return (p - 1) // 4

# ----------------------------------------------------------------------------- the quadratic extension K = F_p(√ν)
class Ext:
    """F_{p²} = F_p[X]/(X² − ν) for a nonsquare ν: elements are pairs (a, b) = a + b√ν."""
    def __init__(self, p, nu):
        assert not is_square(nu, p), (p, nu)
        self.p, self.nu = p, nu % p
    def add(self, x, y): return ((x[0] + y[0]) % self.p, (x[1] + y[1]) % self.p)
    def sub(self, x, y): return ((x[0] - y[0]) % self.p, (x[1] - y[1]) % self.p)
    def neg(self, x): return ((-x[0]) % self.p, (-x[1]) % self.p)
    def mul(self, x, y):
        p, nu = self.p, self.nu
        return ((x[0] * y[0] + nu * x[1] * y[1]) % p, (x[0] * y[1] + x[1] * y[0]) % p)
    def conj(self, x): return (x[0], (-x[1]) % self.p)          # the Frobenius x ↦ x^p
    def norm(self, x): return (x[0] * x[0] - self.nu * x[1] * x[1]) % self.p
    def inv(self, x):
        n = self.norm(x); assert n != 0
        ni = pow(n, -1, self.p); c = self.conj(x)
        return (c[0] * ni % self.p, c[1] * ni % self.p)
    def pow(self, x, k):
        r = (1, 0)
        while k:
            if k & 1: r = self.mul(r, x)
            x = self.mul(x, x); k >>= 1
        return r
    def elements(self): return [(a, b) for a in range(self.p) for b in range(self.p)]
    def is_square_ext(self, x):
        """x is a square in K iff x^((p²−1)/2) = 1 (x ≠ 0)."""
        return x != (0, 0) and self.pow(x, (self.p * self.p - 1) // 2) == (1, 0)
    def scalar(self, a): return (a % self.p, 0)
    def norm_one(self):
        """The norm-one group N¹ = {z : z z̄ = 1}."""
        return [z for z in self.elements() if self.norm(z) == 1]

# ----------------------------------------------------------------------------- the form and its value distributions
def Q(coeffs, v, p):
    return sum(a * x * x for a, x in zip(coeffs, v)) % p

def value_counts(coeffs, p):
    """counts[w] = #{v in F_p^n : Q(v) = w}, by convolving the one-variable distributions (O(n p²))."""
    dist = [1] + [0] * (p - 1)                      # the empty form: Q = 0 once
    for a in coeffs:
        one = [0] * p
        for x in range(p): one[a * x * x % p] += 1
        new = [0] * p
        for u in range(p):
            if dist[u]:
                for w in range(p):
                    if one[w]: new[(u + w) % p] += dist[u] * one[w]
        dist = new
    return dist

def isotropic_count(coeffs, p):
    """#{v : Q(v) = 0}, the zero vector included."""
    return value_counts(coeffs, p)[0]

def orthogonal_order(coeffs, p):
    """|O(Q)| for a diagonal form by frame counting: the number of ordered orthogonal frames (v_0, …, v_n) with
    Q(v_i) = a_i, i.e. ∏_i #{v in <e_i, …, e_n> : Q(v) = a_i} (Witt: the count in the complement depends only on the
    isometry class of the restricted form)."""
    n = 1
    for i, a in enumerate(coeffs):
        n *= value_counts(coeffs[i:], p)[a % p]
    return n

def o_plus_4(q): return 2 * q * q * (q * q - 1) ** 2          # |O_4^+(q)|, Witt index 2
def o_minus_4(q): return 2 * q * q * (q ** 4 - 1)            # |O_4^-(q)|, Witt index 1

for _p, _k in SHELLS:
    assert is_prime(_p) and _p == 4 * _k + 1, (_p, _k)
