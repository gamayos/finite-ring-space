"""
redcommon.py — shared primitives for the 5-reductio validation package
======================================================================
"Paradoxes of Infinity as Reductio ad Absurdum" (Akhtman, preprint 2026), validation package of the FRC corpus
(finite-ring-space/src/5-reductio), added with the paper's predicate ledger (Appendix B, 17 September 2026).

Each check names the row(s) of the paper's predicate ledger it witnesses (LEDGER below; rows cited as 5:XN), and
the ledger's source column cites the check ids in return.  Where a row is proved in Lean (lean/FrcCore, no axioms;
lean/FrcLedger/Reductio.lean on Mathlib), the check here is the instance the reader can run.

Everything the block scripts share:
  * the arithmetic frame W_N of Definition frame — domain [0, N), the graphs of successor, addition and
    multiplication with overflow, and a first-order evaluator over it (sentences in prenex or nested form, as
    Python closures over the frame);
  * the Δ₀ evaluator over ℕ and its frame transcription φ*, with the bound t(φ) of Theorem stability;
  * hereditarily finite sets of small rank as bit masks (the antinomy normal form on a finite universe);
  * the PASS/FAIL registry every block reports into (results.json).

Kinds: EXACT checks are exhaustive or integer-pinned computations (a pass is a proof on the tested instances);
CHART checks decide a [chart] row in floating point with the closed forms checked.
"""
import os, json, sys, itertools, random

# ----------------------------------------------------------------------------- registry
RESULTS = []

# The paper's predicate ledger (rows cited as 5:XN): the row(s) each check witnesses.
LEDGER = {
    "A1": "5:B5", "A2": "5:B3", "A3": "5:B6", "A4": "5:C2, 5:C3", "A5": "5:C5",
    "B1": "5:D2", "B2": "5:D3", "B3": "5:D4, 5:E8", "B4": "5:D9",
    "C1": "5:E1", "C2": "5:E2", "C3": "5:E3", "C4": "5:E4", "C5": "5:E5", "C6": "5:E6",
    "D1": "5:D8", "D2": "5:B7",
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

# ----------------------------------------------------------------------------- the arithmetic frame W_N
class Frame:
    """W_N: domain [0, N), constant 0, order <, and the graphs S, A, M of successor, sum and product restricted to
    the domain (Definition frame).  An atomic relation with an argument outside the domain is false."""
    def __init__(self, N):
        self.N = N; self.dom = range(N)
    def S(self, x, y): return 0 <= x < self.N and y == x + 1 and y < self.N
    def A(self, x, y, z): return all(0 <= v < self.N for v in (x, y, z)) and z == x + y
    def M(self, x, y, z): return all(0 <= v < self.N for v in (x, y, z)) and z == x * y
    def lt(self, x, y): return 0 <= x < self.N and 0 <= y < self.N and x < y

def is_prime(n):
    return n > 1 and all(n % q for q in range(2, int(n ** .5) + 1))

# ----------------------------------------------------------------------------- the Δ₀ language of the core module
# Terms: ('var', i) | ('zero',) | ('one',) | ('add', s, t) | ('mul', s, t);  formulas: ('eq', s, t) | ('lt', s, t) |
# ('neg', φ) | ('conj', φ, ψ) | ('ball', t, φ)  (∀ x ≤ t, φ; x is var 0 in φ, de Bruijn, t read outside).
def num(n):
    t = ('zero',)
    for _ in range(n): t = ('add', t, ('one',))
    return t

def bex(t, phi): return ('neg', ('ball', t, ('neg', phi)))
def disj(a, b): return ('neg', ('conj', ('neg', a), ('neg', b)))
def impl(a, b): return ('neg', ('conj', a, ('neg', b)))

def evalT(env, t):
    k = t[0]
    if k == 'var': return env[t[1]]
    if k == 'zero': return 0
    if k == 'one': return 1
    a, b = evalT(env, t[1]), evalT(env, t[2])
    return a + b if k == 'add' else a * b

def evalF(env, f):
    """The standard value over ℕ (env: list, index 0 innermost)."""
    k = f[0]
    if k == 'eq': return evalT(env, f[1]) == evalT(env, f[2])
    if k == 'lt': return evalT(env, f[1]) < evalT(env, f[2])
    if k == 'neg': return not evalF(env, f[1])
    if k == 'conj': return evalF(env, f[1]) and evalF(env, f[2])
    b = evalT(env, f[1])
    return all(evalF([x] + env, f[2]) for x in range(b + 1))

def evalT_frame(N, env, t):
    """The term in W_N: None when an intermediate value overflows."""
    k = t[0]
    if k == 'var': return env[t[1]] if env[t[1]] < N else None
    if k == 'zero': return 0 if 0 < N else None
    if k == 'one': return 1 if 1 < N else None
    a, b = evalT_frame(N, env, t[1]), evalT_frame(N, env, t[2])
    if a is None or b is None: return None
    v = a + b if k == 'add' else a * b
    return v if v < N else None

def evalF_frame(N, env, f):
    """The transcription φ* in W_N: an atom with an undefined term is false; a bounded quantifier is guarded."""
    k = f[0]
    if k in ('eq', 'lt'):
        a, b = evalT_frame(N, env, f[1]), evalT_frame(N, env, f[2])
        if a is None or b is None: return False
        return a == b if k == 'eq' else a < b
    if k == 'neg': return not evalF_frame(N, env, f[1])
    if k == 'conj': return evalF_frame(N, env, f[1]) and evalF_frame(N, env, f[2])
    b = evalT_frame(N, env, f[1])
    if b is None: return False
    return all(evalF_frame(N, [x] + env, f[2]) for x in range(b + 1))

def boundT(env, t):
    k = t[0]
    if k == 'var': return env[t[1]]
    if k in ('zero',): return 0
    if k == 'one': return 1
    return max(boundT(env, t[1]), boundT(env, t[2]), evalT(env, t))

def boundF(env, f):
    """t(φ): the largest integer the evaluation over ℕ references (the bound of Theorem stability)."""
    k = f[0]
    if k in ('eq', 'lt'): return max(boundT(env, f[1]), boundT(env, f[2]))
    if k == 'neg': return boundF(env, f[1])
    if k == 'conj': return max(boundF(env, f[1]), boundF(env, f[2]))
    b = evalT(env, f[1])
    return max([boundT(env, f[1])] + [boundF([x] + env, f[2]) for x in range(b + 1)])

def prime_form(i):
    """'variable i is prime': 1 < x ∧ ∀ d ≤ x ∀ e ≤ x ¬(d·e = x ∧ d ≠ 1 ∧ d ≠ x)."""
    v = lambda j: ('var', j)
    return ('conj', ('lt', ('one',), v(i)),
            ('ball', v(i), ('ball', v(i + 1), ('neg', ('conj', ('eq', ('mul', v(1), v(0)), v(i + 2)),
                                                          ('conj', ('neg', ('eq', v(1), ('one',))), ('neg', ('eq', v(1), v(i + 2)))))))))

def goldbach_form(M):
    """Every even m ≤ M with 4 ≤ m is a sum of two primes x, y ≤ m (the worked instance of the paper, M = 20)."""
    v = lambda j: ('var', j)
    even0 = bex(v(0), ('eq', ('add', v(0), v(0)), v(1)))
    body = bex(v(0), bex(v(1), ('conj', prime_form(1), ('conj', prime_form(0), ('eq', ('add', v(1), v(0)), v(2))))))
    return ('ball', num(M), impl(('conj', even0, ('neg', ('lt', v(0), num(4)))), body))

def random_form(rng, depth, nvars, maxnum=6):
    """A random Δ₀ formula with the given quantifier depth."""
    def term(d):
        r = rng.random()
        if d == 0 or r < 0.4:
            return ('var', rng.randrange(nvars)) if nvars and rng.random() < 0.6 else num(rng.randrange(maxnum))
        return (rng.choice(['add', 'mul']), term(d - 1), term(d - 1))
    def form(d, nv):
        r = rng.random()
        if d == 0 or r < 0.3:
            return (rng.choice(['eq', 'lt']), term(1), term(1)) if nv else (rng.choice(['eq', 'lt']), num(rng.randrange(maxnum)), num(rng.randrange(maxnum)))
        if r < 0.45: return ('neg', form(d - 1, nv))
        if r < 0.6: return ('conj', form(d - 1, nv), form(d - 1, nv))
        return ('ball', num(rng.randrange(1, maxnum)) if not nv else (('var', rng.randrange(nv)) if rng.random() < 0.5 else num(rng.randrange(1, maxnum))), form(d - 1, nv + 1))
    nvars = 0
    return form(depth, nvars)

# ----------------------------------------------------------------------------- hereditarily finite sets as bit masks
def hf_levels(k):
    """V_0 ⊂ V_1 ⊂ … ⊂ V_k as lists; a set of rank ≤ j is a bit mask over the elements of V_{j−1} (in the
    enumeration of level j−1).  Returns the list of levels, each a list of frozensets of indices into the previous."""
    levels = [[]]                                   # V_0 = ∅ has no elements
    for j in range(1, k + 1):
        prev = levels[-1]
        # elements of V_j are subsets of V_{j-1}; represent as frozenset of indices into V_{j-1}
        levels.append([frozenset(c) for r in range(len(prev) + 1) for c in itertools.combinations(range(len(prev)), r)])
    return levels
