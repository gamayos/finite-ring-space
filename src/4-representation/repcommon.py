"""
repcommon.py — shared primitives for the 4-representation validation package
============================================================================
"Universal Latent Representation in Finite Ring Continuum" (Akhtman, Entropy 2026, 28, 40), validation package of
the FRC corpus (finite-ring-space/src/4-representation), added with the paper's predicate ledger (Appendix A,
17 September 2026).

Each check names the row(s) of the paper's predicate ledger it witnesses (LEDGER below; rows cited as 4:XN), and
the ledger's source column cites the check ids in return.  Where a row is proved in Lean (lean/FrcCore, no axioms;
lean/FrcLedger/Representation.lean on Mathlib), the check here is the instance the reader can run.

Everything the block scripts share:
  * finite models: the latent domain Z, the observations X_m, the representation spaces W_m as small sets, and the
    enumeration of every map between them (the theorem's clauses are decided on every configuration);
  * the shell datum: p = 4κ+1 prime, its primitive generators and its affine frames x ↦ a + b x;
  * the PASS/FAIL registry every block reports into (results.json).

Kinds: EXACT checks are exhaustive or integer-pinned computations (a pass is a proof on the tested instances);
CHART checks decide a [chart] row in floating point with the closed forms checked.
"""
import os, json, sys, itertools

# The shells (p, κ): p = 4κ+1 prime.
SHELLS = [(5, 1), (13, 3), (17, 4), (29, 7), (37, 9), (41, 10)]

# ----------------------------------------------------------------------------- registry
RESULTS = []

# The paper's predicate ledger (Appendix A, rows cited as 4:XN): the row(s) each check witnesses.
LEDGER = {
    "A1": "4:B4", "A2": "4:B5", "A3": "4:B5", "A4": "4:C1, 4:C2", "A5": "4:C3, 4:C4",
    "B1": "4:B6", "B2": "4:C5", "B3": "4:C1, 4:C3",
    "C1": "4:E1", "C2": "4:E1", "C3": "4:E2", "C4": "4:E3", "C5": "4:E3",
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

# ----------------------------------------------------------------------------- finite models
def maps(dom, cod):
    """Every map dom -> cod, as a dict."""
    for vals in itertools.product(cod, repeat=len(dom)):
        yield dict(zip(dom, vals))

def injective(f, dom):
    return len({f[x] for x in dom}) == len(dom)

def compose(f, g, dom):
    """x ↦ f(g(x)) on dom."""
    return {x: f[g[x]] for x in dom}

def adequate(g, E, Z, W):
    """Definition 2: E ∘ g is a bijection Z -> W (W the codomain of E)."""
    phi = {z: E[g[z]] for z in Z}
    return len({phi[z] for z in Z}) == len(Z) == len(W)

def inverse(phi, Z):
    """The inverse of a bijection given by its dict on Z."""
    return {phi[z]: z for z in Z}

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

def frames(p):
    """The affine frames x ↦ a + b x of F_p (1:C2): p(p−1) of them."""
    return [(a, b) for a in range(p) for b in range(1, p)]

def frame_map(frame, p):
    a, b = frame
    return {x: (a + b * x) % p for x in range(p)}

for _p, _k in SHELLS:
    assert is_prime(_p) and _p == 4 * _k + 1, (_p, _k)
