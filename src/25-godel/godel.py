"""
godel.py — the validation package of "Incompleteness Without Infinity" (Akhtman, preprint 2026; Preprints
doi 10.20944/preprints202607.0850.v1), the paper 25-godel of the FRC corpus (finite-ring-space/src/25-godel), added with
the paper's predicate ledger (Appendix A, 3 October 2026).
========================================================================================================================

One script, six blocks, twenty-one checks, standard library only. Each check names the predicate(s) of the paper's ledger
it witnesses (LEDGER below; predicates cited as 25:XN) under a `# 25:XN (<key>)` marker, the key the predicate's accession
key, and the ledger's source column links the marker of the check that decides each predicate (PREDICATES below;
finitering.space/src/25-godel/#<key>). Where a predicate is proved in Lean (lean/FrcCore/Godel.lean, no axioms;
lean/FrcLedger/Godel.lean on Mathlib), the check here is the instance the reader can run.

    python3 godel.py              every block, results.json written; exit 1 if a check fails (≈ 50 s)
    python3 godel.py D            one block (A–F); no results.json
    from frc_25_godel import predicate; predicate("25:F1")    one predicate: its block runs once per session

Blocks:  A  Gödel's hypotheses over a finite structure (Section 3)                      EXACT  (25:C1, C2, C5)
         B  the part and the whole: collisions, aliasing, the wrap (Section 4)           EXACT  (25:D1, D3, D4; corroborates J2)
         C  the reach bound and the horizon's counting facts (Sections 5.1, 5.3, 5.4)    EXACT  (25:E1, E2, E4, G1, G2, G7)
         D  the diagonal does not migrate: mention cost, the template, density (5.2)     EXACT  (25:F1–F4, F6)
         E  fragment truth: the pairing prefix and the guessed labels (Section 5.3)      EXACT  (25:G4, G5)
         F  second-order decidability and the trichotomy's middle cell (Section 6)       EXACT  (25:H2, H5)

Everything the blocks share:
  * the running example M_p = ({0,…,p−1}; 0, 1, +, ×), arithmetic modulo a prime, with its tables read on demand;
  * a prenex evaluator that builds the whole evaluation object (no short-circuit) and counts its matrix evaluations;
  * the certificate format of the wrap lemma: a record of term steps, each checked by one table lookup, and its verifier;
  * every formula over M_2 up to a given length, written out, with its truth table and free variables (the complete enumerations
    of block D), and an independent reader of the written formula, against which the tables are checked;
  * the PASS/FAIL registry every block reports into (results.json).

Kinds: every check is EXACT — an exhaustive or integer-pinned computation, no floating point; a pass is a proof on the
tested instances. The counts a label states are asserted by the check. Where a check works on a sample, its label says so and
the sample is fixed: the sentences of A2, C5 and F2 (a list of eight), the completions of two certificates in B3 (seeded), the
maps at N = 3 in D2 (every 37th), the matrix family over M_5 in E1. D3 and D5 decide ranges of structures and the base
cases of t(M) < m; the comment of block D carries the proofs for every structure.
"""
import os, json, sys, itertools, math, random
from fractions import Fraction

SCRIPT = os.path.splitext(os.path.basename(__file__))[0]        # "godel": the one script, the name results.json and the site pages carry

# ----------------------------------------------------------------------------- registry
RESULTS = []

# The paper's predicate ledger (Appendix A, predicates cited as 25:XN): the predicate(s) each check witnesses.
LEDGER = {
    "A1": "25:C1", "A2": "25:C2", "A3": "25:C5",
    "B1": "25:D1", "B2": "25:D3", "B3": "25:D4, 25:J2",
    "C1": "25:E1", "C2": "25:E2", "C3": "25:E4", "C4": "25:G1", "C5": "25:G2", "C6": "25:G7",
    "D1": "25:F1", "D2": "25:F2", "D3": "25:F4", "D4": "25:F3", "D5": "25:F6",
    "E1": "25:G4", "E2": "25:G5",
    "F1": "25:H2", "F2": "25:H5",
}

BLOCK = {"A": "Gödel's hypotheses over a finite structure",          # check-id prefix -> the block (the function block_<letter> below)
         "B": "the part and the whole: collisions, aliasing, the wrap",
         "C": "the reach bound and the horizon's counting facts",
         "D": "the diagonal does not migrate: mention cost, the template, density",
         "E": "fragment truth: the pairing prefix and the guessed labels",
         "F": "second-order decidability and the trichotomy's middle cell"}

# the deciding check of each witnessed predicate: the one whose verdict decides the predicate's statement (the other checks that
# touch it are corroboration, listed by predicate() from the records)
PREDICATES = {
    "25:C1": "A1", "25:C2": "A2", "25:C5": "A3",
    "25:D1": "B1", "25:D3": "B2", "25:D4": "B3",
    "25:E1": "C1", "25:E2": "C2", "25:E4": "C3", "25:G1": "C4", "25:G2": "C5", "25:G7": "C6",
    "25:F1": "D1", "25:F2": "D2", "25:F4": "D3", "25:F3": "D4", "25:F6": "D5",
    "25:G4": "E1", "25:G5": "E2",
    "25:H2": "F1", "25:H5": "F2",
}
_RAN = set()                                            # blocks already run in this session (predicate() runs each once)
T_EXACT = {}                                            # (a, m) -> (d, fit_table), computed in D3 and read in D5 (block D)

def check(pid, label, ok, detail="", kind="EXACT"):
    """Record one predicate check. pid = package check id; LEDGER[pid] = the paper statement(s) decided."""
    ok = bool(ok)
    rows = LEDGER.get(pid, "")
    RESULTS.append({"id": pid, "rows": rows, "block": pid[0], "script": SCRIPT, "label": label, "ok": ok, "detail": detail, "kind": kind})
    print(f"  [{'PASS' if ok else 'FAIL'}] {pid:4s} {kind:6s} [{rows}] {label}" + (f"  --  {detail}" if detail else ""))
    return ok

def summary(write=True, expect=None):
    """Print the verdict and (write=True) store results.json.  `expect` lists the check ids that must have run: a check that
    never reported fails the summary, as a check that reported FAIL does."""
    n_ok = sum(r["ok"] for r in RESULTS)
    ran = sorted(r["id"] for r in RESULTS)
    census = expect is None or ran == sorted(expect)
    print(f"\nSUMMARY: {n_ok}/{len(RESULTS)} checks passed" + ("" if n_ok == len(RESULTS) else "  <-- FAILURES"))
    if not census: print(f"  <-- CENSUS: expected {sorted(expect)}, ran {ran}")
    if write:
        with open("results.json", "w") as f:
            json.dump(RESULTS, f, indent=1)
    return n_ok == len(RESULTS) and census

def markers():
    """predicate label -> (script file, line) of its marker `# <paper>:<label> (<key>)`: the line of the check that decides it."""
    import re
    out = {}
    for i, line in enumerate(open(os.path.abspath(__file__), encoding="utf-8"), 1):
        m = re.match(r"\s*# ((?:\d+:[A-Z]+\d+[a-z]?(?: \(p\d{5}\))?)(?:, \d+:[A-Z]+\d+[a-z]?(?: \(p\d{5}\))?)*)\s*$", line)
        if m:
            for lab in re.findall(r"\d+:[A-Z]+\d+[a-z]?", m.group(1)): out.setdefault(lab, (SCRIPT + ".py", i))
    return out

def _run_block(letter):
    if letter not in _RAN:
        globals()[f"block_{letter}"](); _RAN.add(letter)

def predicate(label, lines=14):
    """Verify one ledger predicate: run the block of the check that decides it (once per session), print that check's source
    (from its marker) and every record that cites the predicate, and return True iff all pass."""
    pid = PREDICATES.get(label)
    if pid is None:
        print(f"{label}: no python witness (see the predicate's Lean witness or its source)"); return None
    citing = {i[0] for i, rows in LEDGER.items() if label in [t.strip() for t in rows.split(",")]}
    for b in sorted({pid[0]} | citing): _run_block(b)          # the deciding block and every block whose checks cite the predicate
    mk = markers().get(label)
    if mk:
        src = open(os.path.abspath(__file__), encoding="utf-8").read().split("\n")
        print(f"— {mk[0]}:{mk[1]} (the check that decides {label}: {pid})")
        for j in range(mk[1] - 1, min(mk[1] - 1 + lines, len(src))):
            if not src[j].strip(): break                                # the check ends at the first blank line
            print(f"{j + 1:5d}  {src[j]}")
    recs = [r for r in RESULTS if label in [t.strip() for t in r["rows"].split(",")]]
    ok = all(r["ok"] for r in recs) and any(r["id"] == pid for r in recs)     # every citing record passes, and the deciding check reported
    for r in recs:
        role = "(deciding)" if r["id"] == pid else "(corroborating)"
        print(f"  [{'PASS' if r['ok'] else 'FAIL'}] {r['id']:4s} {role:16s} {r['detail'][:150]}")
    print(f"{label}: {'VERIFIED' if ok else 'FAILED'} — {len(recs)} record(s)")
    return ok

def verify_all():
    """Run every block (those already run in this session are not re-run) and print the summary; True iff every check passed."""
    for b in sorted(BLOCK): _run_block(b)
    return summary(write=False, expect=list(LEDGER))

# ----------------------------------------------------------------------------- shared primitives
def is_prime(n):
    """Deterministic Miller–Rabin on the first twelve prime bases (exact below 3.3e24)."""
    if n < 2: return False
    small = (2, 3, 5, 7, 11, 13, 17, 19, 23, 29, 31, 37)
    for q in small:
        if n % q == 0: return n == q
    d, s = n - 1, 0
    while d % 2 == 0: d //= 2; s += 1
    for a in small:
        x = pow(a, d, n)
        if x in (1, n - 1): continue
        for _ in range(s - 1):
            x = x * x % n
            if x == n - 1: break
        else: return False
    return True

def next_prime_1mod4(n):
    """The least prime p >= n with p = 1 (mod 4)."""
    n += (1 - n) % 4
    while not is_prime(n): n += 4
    return n

P_SMALL, P_MID, P_BIG = 13, next_prime_1mod4(10 ** 6), next_prime_1mod4(10 ** 18)     # 13, 1000033, 1000000000000000009
assert (P_MID, P_BIG) == (1000033, 10 ** 18 + 9)

def iroot(n, k):
    """floor(n^(1/k)) by integer bisection."""
    lo, hi = 0, 1
    while hi ** k <= n: hi *= 2
    while lo < hi:
        mid = (lo + hi + 1) // 2
        if mid ** k <= n: lo = mid
        else: hi = mid - 1
    return lo

def catalan(k):
    """The Catalan number C_k by the exact integer recurrence C_{i+1} = C_i · 2(2i+1)/(i+2)."""
    c = 1
    for i in range(k): c = c * 2 * (2 * i + 1) // (i + 2)
    return c

def trees(leaves, memo={}):
    """Every full binary tree with the given number of leaves: a leaf is 1, an inner node a pair (left, right)."""
    if leaves not in memo:
        memo[leaves] = [1] if leaves == 1 else [(l, r) for k in range(1, leaves) for l in trees(k) for r in trees(leaves - k)]
    return memo[leaves]

def tree_value(t, p):
    """The value in M_p of the closed term the tree stands for (1 at the leaves, + at the inner nodes)."""
    return 1 % p if t == 1 else (tree_value(t[0], p) + tree_value(t[1], p)) % p

def tree_text(t):
    """The term written out: 1 at a leaf, (s+t) at an inner node."""
    return "1" if t == 1 else "(" + tree_text(t[0]) + "+" + tree_text(t[1]) + ")"

def decide(m, pattern, matrix, counter=None):
    """The exhaustive evaluation of the prenex sentence Q1 x1 … Qq xq matrix(x) over a domain of m elements: the whole tree of
    quantifier instantiations is built (no short-circuit), and counter[0] counts the matrix evaluations — m^q of them."""
    def rec(i, vals):
        if i == len(pattern):
            if counter is not None: counter[0] += 1
            return bool(matrix(vals))
        res = [rec(i + 1, vals + (t,)) for t in range(m)]
        return all(res) if pattern[i] == "A" else any(res)
    return rec(0, ())

def sentences(p):
    """A sample of prenex sentences over M_p, p prime: (text, pattern, matrix, the value number theory gives it). The expected
    values are stated here, not computed: the checks compare the evaluator against them."""
    return [
        ("AxEy x+y=0", "AE", lambda v: (v[0] + v[1]) % p == 0, True),
        ("AxAy x+y=y+x", "AA", lambda v: (v[0] + v[1]) % p == (v[1] + v[0]) % p, True),
        ("AxEy (x=0 or x*y=1)", "AE", lambda v: v[0] == 0 or (v[0] * v[1]) % p == 1, True),
        ("Ex x*x+1=0", "E", lambda v: (v[0] * v[0] + 1) % p == 0, p == 2 or p % 4 == 1),     # -1 is a square exactly for p = 2 and p = 1 (mod 4)
        ("ExAy x*y=y", "EA", lambda v: (v[0] * v[1]) % p == v[1], True),
        ("AxEy y*y=x", "AE", lambda v: (v[1] * v[1]) % p == v[0], p == 2),                   # every element a square only in characteristic 2
        ("ExEyEz (x*x+y*y+z*z=0 and not x=y=z=0)", "EEE", lambda v: (v[0] * v[0] + v[1] * v[1] + v[2] * v[2]) % p == 0 and v != (0, 0, 0), True),
        ("AxAyAz (x+y)+z=x+(y+z)", "AAA", lambda v: ((v[0] + v[1]) + v[2]) % p == (v[0] + (v[1] + v[2])) % p, True),
    ]

VARS = "abcdef"                                          # the variable names v_0 .. v_5 of the written formulas

def formulas_M2(V, maxlen):
    """EVERY formula of length <= maxlen over M_2 = ({0, 1}; 0, 1, +, x) in the variables v_0 .. v_{V-1}, written out.  Terms: a
    variable, 0, 1 (one symbol), (s+t), (s*t) (three symbols more than their parts); formulas: s=t (one more), ~phi (one more),
    (phi&psi) (three more), Ev phi (two more).  Returns ({length: [(truth table, free variables, text)]}, swap): the table is a
    bit mask over the 2^V assignments (bit a: the truth value under the assignment whose coordinate i is bit i of a), the free
    variables a bit mask, the text the formula as a string, and swap(table, i) is the table with coordinate i reassigned (0 <-> 1)."""
    n_as = 1 << V; full = (1 << n_as) - 1
    lo = [sum(1 << a for a in range(n_as) if not (a >> i) & 1) for i in range(V)]      # the assignments whose coordinate i is 0
    def swap(tab, i): return ((tab & lo[i]) << (1 << i)) | ((tab >> (1 << i)) & lo[i])
    terms = {1: [(full ^ lo[i], 1 << i, VARS[i]) for i in range(V)] + [(0, 0, "0"), (full, 0, "1")]}   # value tables: v_i, the constants
    for L in range(2, maxlen + 1):
        out = []
        for a in range(1, L - 3):
            b = L - 3 - a
            for s_tab, s_fv, s_tx in terms.get(a, []):
                for t_tab, t_fv, t_tx in terms.get(b, []):
                    out.append((s_tab ^ t_tab, s_fv | t_fv, "(" + s_tx + "+" + t_tx + ")"))      # (s+t) modulo 2
                    out.append((s_tab & t_tab, s_fv | t_fv, "(" + s_tx + "*" + t_tx + ")"))      # (s*t) modulo 2
        if out: terms[L] = out
    forms = {}
    for L in range(3, maxlen + 1):
        out = []
        for a in range(1, L - 1):                                                       # s=t
            for s_tab, s_fv, s_tx in terms.get(a, []):
                for t_tab, t_fv, t_tx in terms.get(L - 1 - a, []): out.append((full ^ s_tab ^ t_tab, s_fv | t_fv, s_tx + "=" + t_tx))
        out += [(full ^ tab, fv, "~" + tx) for tab, fv, tx in forms.get(L - 1, [])]     # ~phi
        out += [(tab | swap(tab, i), fv & ~(1 << i), "E" + VARS[i] + tx) for tab, fv, tx in forms.get(L - 2, []) for i in range(V)]   # Ev_i phi
        for a in range(3, L - 5):                                                       # (phi&psi)
            for t1, f1, x1 in forms.get(a, []):
                for t2, f2, x2 in forms.get(L - 3 - a, []): out.append((t1 & t2, f1 | f2, "(" + x1 + "&" + x2 + ")"))
        if out: forms[L] = out
    return forms, swap

def read_term(s, i, env):
    """The written term at s[i:], read by recursive descent: (value in M_2 under env, next position, variables occurring), or None."""
    if i >= len(s): return None
    c = s[i]
    if c in "01": return int(c), i + 1, frozenset()
    if c in VARS: return env.get(c, 0), i + 1, frozenset(c)
    if c == "(":
        l = read_term(s, i + 1, env)
        if l is None or l[1] >= len(s) or s[l[1]] not in "+*": return None
        r = read_term(s, l[1] + 1, env)
        if r is None or r[1] >= len(s) or s[r[1]] != ")": return None
        return ((l[0] + r[0]) % 2 if s[l[1]] == "+" else l[0] * r[0]), r[1] + 1, l[2] | r[2]
    return None

def read_formula(s, i, env):
    """The written formula at s[i:], read by recursive descent and evaluated in M_2 under env (variables absent from env read 0):
    (truth value, next position, free variables), or None if no formula stands there.  It shares no code with formulas_M2: the
    truth tables and the free-variable masks of the enumeration are checked against it."""
    if i >= len(s): return None
    c = s[i]
    if c == "~":
        r = read_formula(s, i + 1, env); return None if r is None else (not r[0], r[1], r[2])
    if c == "E" and i + 1 < len(s) and s[i + 1] in VARS:
        x = s[i + 1]; rs = [read_formula(s, i + 2, {**env, x: b}) for b in (0, 1)]
        return None if rs[0] is None else (rs[0][0] or rs[1][0], rs[0][1], rs[0][2] - {x})
    if c == "(":                                                     # a conjunction, or an equation whose left term opens a bracket
        l = read_formula(s, i + 1, env)
        if l is not None and l[1] < len(s) and s[l[1]] == "&":
            r = read_formula(s, l[1] + 1, env)
            if r is not None and r[1] < len(s) and s[r[1]] == ")": return l[0] and r[0], r[1] + 1, l[2] | r[2]
    l = read_term(s, i, env)
    if l is None or l[1] >= len(s) or s[l[1]] != "=": return None
    r = read_term(s, l[1] + 1, env)
    return None if r is None else (l[0] == r[0], r[1], l[2] | r[2])

def name_cost(k, a):
    """The total length of the k shortest distinct names over an alphabet of a letters: a names of one letter, a^2 of two, …"""
    cost, L = 0, 1
    while k > 0:
        take = min(k, a ** L); cost += take * L; k -= take; L += 1
    return cost

def delta_names(k, k1, a):
    """The least total length of the variable names in the diagonal formula delta(u) = Ev (Diag(u, v) & theta(v)) with k
    coordinates in v and k1 in u: k + k1 distinct variables, each coordinate of v named three times (the block, Diag, theta)
    and each of u once (Diag).  Of k + k1 distinct names the k + k1 shortest cost least, and the weight 3 goes to the k
    shortest of them."""
    return 2 * name_cost(k, a) + name_cost(k + k1, a)

def lambda_names(k, k1, a):
    """The least number of symbols the coordinates cost in lambda = delta(code of delta): each coordinate of v named three
    times, and a closed term of at least one symbol in each of the k1 places of u."""
    return 3 * name_cost(k, a) + k1

def admits(k, k1, d, a):
    """The name count leaves an instance open, in digit form: lambda's symbols fit a code of k coordinates and delta's a
    code of k1, a code of j coordinates over a structure of d digits holding fewer than d*j letters."""
    return lambda_names(k, k1, a) < d * k and delta_names(k, k1, a) < d * k1

def fit_table(m, a, d, upto):
    """[n_0, n_1, …, n_upto], n_j the largest n with a^n <= m^j: the longest strings an injective coding by j-tuples can
    reach.  For a^(d-1) <= m < a^d each step adds d - 1 or d."""
    out, P, Q, n = [0], 1, 1, 0
    for _ in range(upto):
        P *= m; Q *= a ** (d - 1); n += d - 1
        if Q * a <= P: Q *= a; n += 1
        assert Q <= P < Q * a
        out.append(n)
    return out

def last_k(w, a, strict=False):
    """The largest k with delta_names(k, k, a) <= w*k (< w*k if strict), 0 if none: the template at one scale.
    delta_names(k, k)/k does not decrease with k (proved in the comment of block D; D5 checks it for a = 2..5, k <= 20000),
    so the k that pass form an initial segment and bisection finds its end.  The doubling stops because the quotient is
    unbounded (bound (i) there)."""
    good = (lambda k: delta_names(k, k, a) < w * k) if strict else (lambda k: delta_names(k, k, a) <= w * k)
    if not good(1): return 0
    lo, hi = 1, 2
    while good(hi): hi *= 2
    while lo < hi - 1:
        mid = (lo + hi) // 2
        if good(mid): lo = mid
        else: hi = mid
    return lo

# ----------------------------------------------------------------------------- the certificate format of the wrap lemma
# A structure is a dict {"U": universe (list), "c": {0: element, 1: element}, "+": table, "*": table}; a table is a function
# (x, y) -> element (M_p: arithmetic on demand) or a dict (a small structure M').  A record is a list of steps:
#   ("c", k)            the constant k (0 or 1): a term step, checked by reading the constant (one element)
#   ("o", op, i, j, v)  the term op(step i, step j) has the value v: checked by ONE table lookup, touching at most r+1 = 3 elements
#   ("=", i, j)         the end sentence: term i = term j, checked by comparing the two recorded values
#   ("ax", name)        an axiom asserted on syntactic recognition alone: its check consults nothing
def Mp(p, ops="+*"):
    S = {"U": None, "p": p, "c": {0: 0, 1: 1 % p}}
    if "+" in ops: S["+"] = lambda x, y: (x + y) % p
    if "*" in ops: S["*"] = lambda x, y: (x * y) % p
    return S

def lookup(S, op, x, y):
    t = S[op]
    return t(x, y) if callable(t) else t[(x, y)]

def verify(record, S, axioms=()):
    """Step-check a record against the tables of S, in the system whose axiom rules assert the sentences listed in `axioms` on
    syntactic recognition.  Returns (accepted, values, cited entries {(op, x, y): v}, cited elements, number of lookups).  Only the
    entries the steps name are consulted."""
    vals, cited, elems, n_look = [], {}, set(), 0
    for st in record:
        if st[0] == "c":
            v = S["c"][st[1]]; vals.append(v); elems.add(v); n_look += 1
        elif st[0] == "o":
            _, op, i, j, v = st
            if not (i < len(vals) and j < len(vals)) or vals[i] is None or vals[j] is None: return False, vals, cited, elems, n_look
            got = lookup(S, op, vals[i], vals[j]); n_look += 1
            cited[(op, vals[i], vals[j])] = got; elems.update((vals[i], vals[j], got))
            if got != v: return False, vals, cited, elems, n_look
            vals.append(v)
        elif st[0] == "=":
            _, i, j = st
            if vals[i] != vals[j]: return False, vals, cited, elems, n_look
            vals.append(None)
        elif st[0] == "ax":
            if st[1] not in axioms: return False, vals, cited, elems, n_look     # not an axiom of the system
            vals.append(None)                                  # recognised by its shape; no table entry is consulted
        else: return False, vals, cited, elems, n_look
    return True, vals, cited, elems, n_look

def term_of(record, i):
    """The term a term step stands for, as a nested tuple."""
    st = record[i]
    return ("c", st[1]) if st[0] == "c" else (st[1], term_of(record, st[2]), term_of(record, st[3]))

def eval_term(S, t):
    """The value of a term in S, computed from the tables directly (not from a record)."""
    return S["c"][t[1]] if t[0] == "c" else lookup(S, t[0], eval_term(S, t[1]), eval_term(S, t[2]))

def eval_step(S, record, i, memo=None):
    """The value in S of the term that step i stands for, computed from the tables of S alone — the values the record states are
    not read; shared subterms are evaluated once (a record is a term graph, not a tree)."""
    memo = {} if memo is None else memo
    if i not in memo:
        st = record[i]
        memo[i] = S["c"][st[1]] if st[0] == "c" else lookup(S, st[1], eval_step(S, record, st[2], memo), eval_step(S, record, st[3], memo))
    return memo[i]

def small_world(cited, elems, ops, fill):
    """The structure M' of the wrap lemma: universe = the cited elements, the tables agreeing with M on every cited entry and
    completed inside the universe by `fill(op, x, y)` elsewhere."""
    U = sorted(elems) or [0]
    S = {"U": U, "c": {k: (k if k in elems else U[0]) for k in (0, 1)}}
    for op in ops:
        S[op] = {(x, y): cited.get((op, x, y), None) for x in U for y in U}
        for (x, y), v in list(S[op].items()):
            if v is None: S[op][(x, y)] = fill(op, x, y, U)
    return S

def commutative(S, op="+"):
    return all(lookup(S, op, x, y) == lookup(S, op, y, x) for x in S["U"] for y in S["U"])

# ------------------------------------------------------------------------------------------------------------
# block A: Gödel's hypotheses over a finite structure (25:C1, C2, C5) — Section 3 of the paper.
# A1: no finite structure carries a successor that is injective and omits an element (exhaustive over all N^N maps,
# N ≤ 7), so no finite structure is a model of Q, and none interprets it.  A2: the theory of M_p is decided by exhaustive
# evaluation — every sentence of a sample takes the value number theory gives it, the evaluation object has m^q leaves at
# quantifier depth q, exactly one of a sentence and its negation is true; and the characterising sentence σ_M, evaluated
# as a sentence in every structure on 3 elements, holds exactly in the structures isomorphic to M, and in none of 1 or 2
# elements or among the one-element extensions of M, each clause of σ_M with its control.  A3: the sentences outnumber the elements — m+1 sentences of length
# at most m+1 admit no injective numbering into M — while truth is given externally by a finite table.
def block_A():
    """Block A — Gödel's hypotheses over a finite structure (EXACT): A1–A3."""
    # A1 no finite model of Q: injective maps on a finite set are onto; the chain 0, S0, SS0, … repeats
    ok = True; det = []; n_maps = n_chain = 0
    for N in range(1, 8):
        n_inj = n_miss = 0
        for S in itertools.product(range(N), repeat=N):
            n_maps += 1
            if len(set(S)) == N:
                n_inj += 1
                ok &= set(S) == set(range(N))                     # injective => surjective
                if 0 not in S: n_miss += 1                        # a successor of Q: injective with 0 outside its range
        ok &= n_inj == math.factorial(N) and n_miss == 0
        det.append(f"N={N}: {N**N} maps, {n_inj} injective, all onto")
    for N in range(1, 7):                                          # the numerals 0, S0, …, S^N 0 are not pairwise distinct, whatever S
        for S in itertools.product(range(N), repeat=N):
            n_chain += 1
            x, seen = 0, [0]
            for _ in range(N): x = S[x]; seen.append(x)
            ok &= len(set(seen)) < len(seen)
    ok &= n_maps == 873612 and n_chain == 50069                    # 1 + 4 + 27 + … + 7^7 maps; 1 + 4 + … + 6^6 chains
    # 25:C1 (p25010)
    check("A1", "no finite model of Q: on N elements every injective map is onto, so no successor is injective and misses 0 (all 873612 maps, N <= 7); the N+1 numerals 0, S0, ..., S^N 0 repeat under every S (all 50069 maps, N <= 6)", ok,
          "; ".join(det[3:]))

    # A2 completeness and decidability of Th(M_p); the evaluation object has m^q leaves; sigma_M is categorical
    ok = True; det = []; n_sent = 0
    for p in (5, 7, 13):
        for text, pat, mat, want in sentences(p):
            cnt = [0]; v = decide(p, pat, mat, cnt); n_sent += 1
            ok &= v == want and cnt[0] == p ** len(pat)                              # decided, with the evaluation object of size m^q
            dual = "".join("E" if c == "A" else "A" for c in pat)
            ok &= decide(p, dual, lambda vals, mat=mat: not mat(vals)) == (not v)   # exactly one of the sentence and its negation is true
        det.append(f"p={p}: 8 sentences decided, depth-3 objects of {p**3} leaves")
    ok &= n_sent == 24
    # the characterising sentence sigma_M, evaluated as a sentence in a structure (c0, c1, o) on n elements: there are pairwise distinct
    # x_0, x_1, x_2 with c0 = x_0, c1 = x_1, x_a o x_b = x_{a o b} for every table entry of M, and every element is one of them.
    # `distinct` and `closure` switch its first and last clause off, for the controls.
    def sigma(M_tab, n, c0, c1, tab, distinct=True, closure=True):
        for xs in (itertools.permutations(range(n), 3) if distinct else itertools.product(range(n), repeat=3)):
            if xs[0] == c0 and xs[1] == c1 and all(tab[n * xs[a] + xs[b]] == xs[M_tab[a][b]] for a in range(3) for b in range(3)) \
               and (not closure or all(y in xs for y in range(n))): return True
        return False
    def iso_forced(M_tab, c0, c1, tab):
        """Isomorphism to M tested a second way: M is generated by its constants (2 = 1 o 1), so an isomorphism is forced to be
        0 -> c0, 1 -> c1, 2 -> c1 o c1; it is one iff that map is a bijection carrying every table entry."""
        f = (c0, c1, tab[3 * c1 + c1])
        return len(set(f)) == 3 and all(tab[3 * f[a] + f[b]] == f[M_tab[a][b]] for a in range(3) for b in range(3))
    Z3 = [[(a + b) % 3 for b in range(3)] for a in range(3)]
    NC = [[0, 1, 2], [2, 2, 0], [1, 0, 0]]                             # a second structure: a non-commutative table with 1 o 1 = 2
    ok &= NC[0][1] != NC[1][0] and all(Z3[a][b] == Z3[b][a] for a in range(3) for b in range(3))
    models = {}
    for name, M_tab in (("Z_3", Z3), ("NC", NC)):
        n_mod = total = 0
        for c0 in range(3):
            for c1 in range(3):
                for tab in itertools.product(range(3), repeat=9):      # every structure (c0, c1, o) on 3 elements
                    total += 1; sg = sigma(M_tab, 3, c0, c1, tab)
                    ok &= sg == iso_forced(M_tab, c0, c1, tab)         # the models of sigma_M are exactly the structures isomorphic to M
                    n_mod += sg
        ok &= total == 3 * 3 * 3 ** 9 == 177147 and n_mod == math.factorial(3)
        ok &= sigma(M_tab, 3, 0, 1, tuple(M_tab[a][b] for a in range(3) for b in range(3)))     # M itself is a model
        # smaller structures: the distinctness clause excludes them.  Without it sigma_M holds in the one-element structure
        # (every table equation collapses to the point); with it, in no structure of one or two elements.
        n1 = sigma(M_tab, 1, 0, 0, (0,)); n1_open = sigma(M_tab, 1, 0, 0, (0,), distinct=False)
        n2 = n2_scanned = 0
        for c0 in range(2):
            for c1 in range(2):
                for tab in itertools.product(range(2), repeat=4): n2_scanned += 1; n2 += sigma(M_tab, 2, c0, c1, tab)
        ok &= (n1, n1_open, n2, n2_scanned) == (False, True, 0, 64)
        # larger structures: the closure clause excludes them.  Every one-element extension of M (4^7 completions of the new row
        # and column) satisfies sigma_M without its closure clause, and none satisfies sigma_M.
        ext = ext_open = ext_scanned = 0
        for new in itertools.product(range(4), repeat=7):
            tab = [0] * 16
            for a in range(3):
                for b in range(3): tab[4 * a + b] = M_tab[a][b]
            for k, (a, b) in enumerate([(0, 3), (1, 3), (2, 3), (3, 0), (3, 1), (3, 2), (3, 3)]): tab[4 * a + b] = new[k]
            ext_scanned += 1; ext += sigma(M_tab, 4, 0, 1, tab); ext_open += sigma(M_tab, 4, 0, 1, tab, closure=False)
        ok &= (ext, ext_open, ext_scanned) == (0, 16384, 16384)
        models[name] = n_mod
    # 25:C2 (p25011)
    check("A2", "Th(M_p) is decided by exhaustive evaluation: a sample of 8 sentences over p = 5, 7, 13 take the values number theory gives them, the evaluation object has m^q leaves, and exactly one of a sentence and its negation is true; sigma_M, evaluated as a sentence in all 177147 structures (c0, c1, o) on 3 elements, holds exactly in the 3! structures isomorphic to M (for M = (Z_3; 0, 1, +) and for a non-commutative M); its distinctness clause excludes the structures of 1 and 2 elements (without it the one-element structure is a model), its closure clause the 16384 one-element extensions of M (without it all are models)", ok,
          "; ".join(det) + f"; models of sigma among 177147 structures: {models}; 64 structures of 2 elements and 16384 extensions to 4 elements: none")

    # A3 the sentences outnumber the elements; truth is an external table
    ok = True; n_maps = 0
    def value(sent):
        """The truth value of ~…~F, by recursion on the written sentence (F is the false constant)."""
        return False if sent == "F" else not value(sent[1:])
    for m in range(2, 6):
        sents = ["~" * k + "F" for k in range(m + 1)]                # F, ~F, ~~F, …: m+1 sentences of length <= m+1
        ok &= len(set(sents)) == m + 1 and max(map(len, sents)) == m + 1
        for f in itertools.product(range(m), repeat=m + 1):          # every numbering of them into M
            n_maps += 1
            ok &= len(set(f)) < m + 1                                # is not injective
        table = {sent: value(sent) for sent in sents}                # the external truth table: m+1 entries, computed from the sentences
        ok &= len(table) == m + 1 and [table[sent] for sent in sents] == [k % 2 == 1 for k in range(m + 1)]   # F false, ~F true, alternating
    ok &= n_maps == 2 ** 3 + 3 ** 4 + 4 ** 5 + 5 ** 6 == 16738
    # 25:C5 (p25014)
    check("A3", "Tarski scoped: the m+1 sentences F, ~F, ..., ~^m F of length at most m+1 admit no injective numbering into a structure of m elements (all 16738 maps, m = 2..5), and their truth is a finite external table, computed from the written sentences", ok,
          f"{n_maps} numberings scanned, none injective")

# ------------------------------------------------------------------------------------------------------------
# block B: the part and the whole (25:D1, D3, D4; corroborates J2) — Section 4.
# B1: an agent with a^K storage states in a structure of m > a^K elements has no injective encoding (every map on six
# instances; at a^K = m the injective readings are the bijections).  B2: every total reading has a fibre of at least
# ⌈m/a^K⌉ ≥ 2 elements, some reading attains the bound, and every element outside a maximal faithfully represented range
# is an alias of one inside it.  B3: the wrap — for a certificate checked by table lookups, the
# structure M' on the cited elements (the tables agreeing with M on the cited entries, completed arbitrarily) accepts the
# same record by the same steps and makes its end sentence true: under EVERY completion for a certificate over Z_5, under
# a fixed sample of completions for two larger ones; an axiom asserted on syntactic recognition is accepted there too,
# and its truth does not transport.
def block_B():
    """Block B — the part and the whole: collisions, aliasing, the wrap (EXACT): B1–B3."""
    # B1 the relational diagonal: a^K < m leaves no injective encoding
    ok = True; det = []; n_all = 0
    for a, K, m in ((2, 1, 3), (2, 2, 5), (3, 1, 4), (2, 2, 6), (5, 1, 6), (2, 2, 7)):
        states = a ** K; n = 0
        assert states < m
        for rho in itertools.product(range(states), repeat=m):        # every assignment of storage states to the m elements
            n += 1
            ok &= any(rho[x] == rho[y] for x in range(m) for y in range(x))    # identifies two of them
        det.append(f"a^K={states}<m={m}: {n} readings"); n_all += n
    ok &= n_all == 2 ** 3 + 4 ** 5 + 3 ** 4 + 4 ** 6 + 5 ** 6 + 4 ** 7 == 37218
    n_inj = sum(1 for rho in itertools.product(range(4), repeat=4) if len(set(rho)) == 4)
    ok &= n_inj == 24                                                  # the control: with as many states as elements, 4! readings are injective
    # 25:D1 (p25015)
    check("B1", "the part cannot hold the whole: with a^K < m every assignment of storage states to the m elements identifies two of them (all 37218 maps on six instances); with a^K = m = 4 the injective readings are the 24 bijections", ok,
          "; ".join(det[:4]))

    # B2 aliasing with multiplicity
    ok = True; det = []; n_all = 0
    for m, R in ((4, 2), (5, 2), (5, 3), (6, 3), (7, 2), (7, 3), (6, 4), (5, 4)):
        need = -(-m // R); least = m                                   # ceil(m / R)
        for rho in itertools.product(range(R), repeat=m):
            n_all += 1
            big = max(sum(1 for x in range(m) if rho[x] == y) for y in range(R))
            ok &= big >= need; least = min(least, big)                  # some reading stands for at least ceil(m/R) elements
        ok &= least == need >= 2                                       # the bound is attained, and it is at least 2
        det.append(f"m={m}, R={R}: largest fibre >= {need}, attained")
    ok &= n_all == 2 ** 4 + 2 ** 5 + 3 ** 5 + 3 ** 6 + 2 ** 7 + 3 ** 7 + 4 ** 6 + 4 ** 5 == 8455
    # a maximal faithfully represented range: a set S of elements on which the reading is injective and which no larger set with
    # that property contains.  Every element outside it is read as an element inside it (an alias).
    n_max = 0
    for m, R in ((4, 2), (5, 2), (5, 3), (6, 3), (5, 4), (6, 4)):
        for rho in itertools.product(range(R), repeat=m):
            faithful = [mask for mask in range(1, 2 ** m) if len({rho[x] for x in range(m) if (mask >> x) & 1}) == bin(mask).count("1")]
            for mask in faithful:
                if any(t != mask and t & mask == mask for t in faithful): continue               # a larger faithful set contains S: not maximal
                S = [x for x in range(m) if (mask >> x) & 1]; out = [x for x in range(m) if not (mask >> x) & 1]
                n_max += 1
                ok &= len(out) >= 1 and all(any(rho[s0] == rho[x] for s0 in S) for x in out)    # some element lies outside, and each is an alias
    ok &= n_max == 31203
    # 25:D3 (p25017)
    check("B2", "aliasing: every total reading of m elements by R < m storage states has a fibre of at least ceil(m/R) >= 2 elements, and some reading attains the bound (all 8455 maps on eight instances, m = 5, R = 4 among them, where m/R < 2); every element outside a maximal faithfully represented range is read as one inside it (all 31203 maximal ranges of all readings on six instances)", ok,
          "; ".join(det))

    # B3 the wrap: the same certificate, with its warrant, in a small world
    ok = True; det = []
    r = 2                                                              # the largest operation arity
    # (i) a certificate over M_13: ((1+1)+1)*(1+1) = (1+1)*((1+1)+1)
    rec = [("c", 1), ("o", "+", 0, 0, 2), ("o", "+", 1, 0, 3), ("o", "*", 2, 1, 6), ("o", "*", 1, 2, 6), ("=", 3, 4)]
    M = Mp(13); acc, vals, cited, elems, n_look = verify(rec, M)
    ok &= acc and len(elems) <= n_look <= len(rec)                      # an operand is an earlier step, so each lookup cites at most one new
                                                                        # element: within the lemma's bound of r+1 elements per lookup
    rng = random.Random(25); n_fill = 0
    fills = [lambda op, x, y, U: U[0], lambda op, x, y, U: U[(U.index(x) + 2 * U.index(y) + 1) % len(U)]] + [None] * 40
    for f in fills:
        fill = f or (lambda op, x, y, U: rng.choice(U))
        W = small_world(cited, elems, "+*", fill); n_fill += 1
        acc2, vals2, cited2, elems2, n2 = verify(rec, W)
        ok &= acc2 and vals2 == vals and cited2 == cited                # accepted by the same steps, the same lookups, the same results
        ok &= eval_term(W, term_of(rec, 3)) == eval_term(W, term_of(rec, 4))   # the end sentence is true in M'
    ok &= n_fill == 42
    bad_val = rec[:3] + [("o", "*", 2, 1, 7)]                           # the controls: a record cut at a wrong product, and a false end sentence (3 = 6),
    bad_end = rec[:-1] + [("=", 2, 3)]                                  # are rejected in M and in the last small world
    ok &= not verify(bad_val, M)[0] and not verify(bad_end, M)[0] and not verify(bad_val, W)[0] and not verify(bad_end, W)[0]
    det.append(f"M_13: {len(rec)} steps, {n_look} lookups, |M'| = {len(elems)} <= {n_look} <= {(r + 1) * n_look}, {n_fill} completions (2 fixed, 40 seeded)")
    # (ii) a certificate over the carrier 10^18+9 whose term values are reduced modulo p: t = 2^(2^7), a term of 256 leaves, and t*(t+1) = (t+1)*t
    p = P_BIG; M = Mp(p); rec = [("c", 1), ("o", "+", 0, 0, 2)]; v = 2; size = [1, 5]     # size[i]: the written length of the term of step i
    for _ in range(7):
        rec.append(("o", "*", len(rec) - 1, len(rec) - 1, v * v % p)); v = v * v % p; size.append(2 * size[-1] + 3)
    i_t = len(rec) - 1
    rec.append(("o", "+", i_t, 0, (v + 1) % p)); i_s = len(rec) - 1; size.append(size[i_t] + 1 + 3)
    rec.append(("o", "*", i_t, i_s, v * (v + 1) % p)); rec.append(("o", "*", i_s, i_t, v * (v + 1) % p)); rec.append(("=", len(rec) - 2, len(rec) - 1))
    end_len = 2 * (size[i_t] + size[i_s] + 3) + 1                         # the end sentence written out: a few thousand symbols
    acc, vals, cited, elems, n_look = verify(rec, M)
    ok &= acc and len(elems) <= n_look and len(elems) < 2 ** 8 < p and end_len == 4099   # M' has fewer than 256 elements, M has p
    ok &= pow(2, 2 ** 7, p) == v != 2 ** (2 ** 7) and 2 ** (2 ** 7) > p    # the term's integer value 2^128 exceeds p: its value in M_p is the residue
    n_fill2 = 0
    for f in fills[:12]:
        fill = f or (lambda op, x, y, U: rng.choice(U))
        W = small_world(cited, elems, "+*", fill); n_fill2 += 1
        acc2, vals2, cited2, _, _ = verify(rec, W)
        ok &= acc2 and vals2 == vals and cited2 == cited
        ok &= eval_step(W, rec, len(rec) - 3) == eval_step(W, rec, len(rec) - 2)     # the end sentence is true in M', evaluated from its own tables
    ok &= n_fill2 == 12
    det.append(f"M_p, p = 10^18+9: {len(rec)} steps, end sentence of {end_len} symbols, values reduced mod p, |M'| = {len(elems)}, {n_fill2} completions")
    # (iii) every completion, exhaustively: 1+(1+1) = (1+1)+1 over (Z_5; 0, 1, +)
    rec = [("c", 1), ("o", "+", 0, 0, 2), ("o", "+", 0, 1, 3), ("o", "+", 1, 0, 3), ("=", 2, 3)]
    M = Mp(5, "+"); acc, vals, cited, elems, n_look = verify(rec, M); U = sorted(elems)
    free = [(x, y) for x in U for y in U if ("+", x, y) not in cited]
    n_all = n_true = 0
    for choice in itertools.product(U, repeat=len(free)):
        tab = dict(zip(free, choice))
        W = small_world(cited, elems, "+", lambda op, x, y, U: tab[(x, y)])
        acc2, vals2, _, _, _ = verify(rec, W); n_all += 1
        n_true += acc2 and eval_term(W, term_of(rec, 2)) == eval_term(W, term_of(rec, 3))
    ok &= acc and n_all == len(U) ** len(free) == 729 and n_true == n_all   # a locally sound certificate keeps its truth under every completion
    # (iv) an axiom asserted on syntactic recognition: the system D with the one axiom rule "AxAy x+y=y+x" (true in M: D is sound)
    COMM = "AxAy x+y=y+x"; D_AX = (COMM,)
    rec_ax = [("c", 1), ("o", "+", 0, 0, 2), ("o", "+", 1, 0, 3), ("ax", COMM)]
    acc, vals, cited, elems, _ = verify(rec_ax, M, D_AX); U = sorted(elems)
    free = [(x, y) for x in U for y in U if ("+", x, y) not in cited]
    n_acc = n_comm = n_w = 0
    for choice in itertools.product(U, repeat=len(free)):
        tab = dict(zip(free, choice))
        W = small_world(cited, elems, "+", lambda op, x, y, U: tab[(x, y)]); n_w += 1
        n_acc += verify(rec_ax, W, D_AX)[0]; n_comm += commutative(W)
    ok &= acc and commutative({"U": list(range(5)), "+": M["+"]}) and n_acc == n_w == 2187 and n_comm == 81   # accepted everywhere; its end sentence true in 81 of the 2187 small worlds
    ok &= not verify([("ax", "0=1")], M, D_AX)[0] and not verify(rec_ax, M)[0]      # a sentence the system does not list is not accepted
    # (v) the display case of the neutrality theorem: a description T whose axiom rules assert the successor axioms of Q.  Its record is
    # accepted by the same syntactic check over M_13, where the axioms are false (0 = S(12))
    T_Q = ("S injective", "0 not in the range of S")
    succ = lambda x: (x + 1) % 13
    q_inj = len({succ(x) for x in range(13)}) == 13; q_zero = all(succ(x) != 0 for x in range(13))
    ok &= verify([("ax", T_Q[0]), ("ax", T_Q[1])], Mp(13), T_Q)[0] and q_inj and not q_zero
    # 25:D4 (p25018)
    check("B3", "the wrap: a certificate checked by table lookups is accepted, by the same steps and with a true end sentence, in the structure M' on its cited elements (|M'| <= lookups, within the lemma's (r+1) x lookups) — under every completion of the uncited entries for a certificate over Z_5 (729 worlds), under a fixed sample of 42 and of 12 completions for certificates over M_13 and over M_p, p = 10^18+9, whose term values are reduced modulo p; a record with a wrong product or a false end sentence is rejected in both worlds; an axiom asserted on syntactic recognition is accepted in all 2187 small worlds of its record and true in 81 of them", ok,
          "; ".join(det) + f"; Z_5: all {n_all} completions keep the end sentence true; the commutativity axiom accepted in {n_acc} of {n_w} worlds, true in {n_comm}; Q's successor axioms accepted as a record over M_13, where 0 = S(12)")

# ------------------------------------------------------------------------------------------------------------
# block C: the reach bound and the horizon's counting facts (25:E1, E2, E4, G1, G2, G7) — Sections 5.1, 5.3, 5.4.
# C1: the closed terms over {1, +} with l leaves are the C_{l-1} full binary trees, all of value l mod p, giving
# C(C_{l-1}, 2) >= 2^l true equations of length 8l-5 for l >= 6.  C2: the records of length <= B over a letters number
# (a^{B+1}-1)/(a-1) < a^{B+1}, and the certified fraction of the cohort falls below every 1/N.  C3: in the bare evaluation
# calculus the universal rule applies to the full set of its m premises alone, so a global clause has a derivation of
# length m+1 > H for every budget H < m.  C4: truths longer than a budget B, built and written out — no record of length
# <= B contains one.  C5: the one-rule system D_tt accepts exactly the true sentences, each in one line, and step-checks
# by m^q evaluations.  C6: the two counting cells of the decomposition table that are not predicates of their own — bounded
# consistency by exhaustive search, with the candidate count of its brute certificate, and reach against the budget.
def block_C():
    """Block C — the reach bound and the horizon's counting facts (EXACT): C1–C6."""
    # C1 abundance of truths
    ok = True; det = []; n_trees = 0
    for l in range(1, 11):
        ts = trees(l); n_trees += len(ts)
        ok &= len(ts) == len(set(ts)) == catalan(l - 1)                  # the terms with l leaves are the full binary trees: Catalan C_{l-1}
        for p in (2, 3, 5, 13):
            ok &= {tree_value(t, p) for t in ts} == {l % p}              # all of one value, l mod p
        ok &= all(len(tree_text(t)) == 4 * l - 3 for t in ts)            # written out: 4l-3 symbols, an equation t = t' 8l-5
    ok &= n_trees == 6918
    det.append(f"l <= 10: {n_trees} trees enumerated, each of value l mod p for p = 2, 3, 5, 13")
    ok &= all(catalan(l - 1) >= 2 ** (l - 2) for l in range(2, 501))     # C_{l-1} >= 2^{l-2}
    pair = lambda l: catalan(l - 1) * (catalan(l - 1) - 1) // 2
    ok &= all(pair(l) >= 2 ** l for l in range(6, 501)) and [l for l in range(2, 6) if pair(l) < 2 ** l] == [2, 3, 4]   # the cohort C(C_{l-1}, 2) >= 2^l from l = 6 (and at l = 5; it fails at l = 2, 3, 4)
    for L in range(43, 4001):                                            # the truths of length <= L: the cohort at l = floor((L+5)/8) leaves
        l = (L + 5) // 8
        ok &= 6 <= l <= 500 and 8 * l - 5 <= L and 9 * l >= L             # its equations fit in L symbols and number at least 2^l >= 2^{L/9}
    # 25:E1 (p25019)
    check("C1", "abundance: the closed terms over {1, +} with l leaves are the Catalan(l-1) full binary trees, all of value l mod p (6918 trees enumerated, l <= 10, p = 2, 3, 5, 13); C_{l-1} >= 2^{l-2} and the cohort of true equations C(C_{l-1}, 2) >= 2^l for 6 <= l <= 500, each of 8l-5 symbols, so the truths of length <= L number at least 2^{L/9} (43 <= L <= 4000)", ok,
          "; ".join(det) + f"; cohort at l = 6: {pair(6)} >= 64, at l = 4: {pair(4)} < 16")

    # C2 vanishing reach
    ok = True; det = []
    for a, Bmax in ((2, 12), (3, 7), (5, 5)):
        for B in range(Bmax + 1):
            n = sum(1 for k in range(B + 1) for _ in itertools.product(range(a), repeat=k))   # the strings of length <= B, enumerated
            ok &= n == (a ** (B + 1) - 1) // (a - 1) < a ** (B + 1)
    a, B = 2, 20; certs = a ** (B + 1)
    f12, f24, f48 = (Fraction(certs, pair(l)) for l in (12, 24, 48))
    ok &= f12 < 1 and f24 < Fraction(1, 10 ** 6) and f48 < f24 < f12
    for N in (10 ** 3, 10 ** 6, 10 ** 12, 10 ** 100):
        l0 = next(l for l in range(6, 2000) if certs * N < pair(l))
        ok &= all(certs * N < pair(l) for l in range(l0, l0 + 60))       # below 1/N from l0 on
        det.append(f"< 1/{'10^' + str(len(str(N)) - 1)} from l = {l0}")
    # 25:E2 (p25020)
    check("C2", "vanishing reach: the records of length <= B over a letters number (a^{B+1}-1)/(a-1) < a^{B+1} (enumerated for a = 2, 3, 5), and at a = 2, B = 20 the certified fraction a^{B+1}/C(C_{l-1}, 2) of the equation cohort is below 1 at l = 12, below 10^-6 at l = 24, and below each tested 1/N (N = 10^3, 10^6, 10^12, 10^100) at the 60 values of l from a first one on", ok,
          f"fraction at l = 12: {f12.numerator}/{f12.denominator}; " + "; ".join(det))

    # C3 a global clause in the bare evaluation calculus
    ok = True; det = []
    def bare_accepts(deriv, p, phi=lambda x, p: (x + 0) % p == x):
        """The bare evaluation calculus on the clause Ax x+0=x: a premise ("inst", c) is checked by one lookup; the universal rule
        ("all",) is accepted only when a premise for every element of the structure stands before it."""
        have = set()
        for st in deriv:
            if st[0] == "inst":
                if not phi(st[1], p): return False
                have.add(st[1])
            elif st[0] == "all":
                if have != set(range(p)): return False
            else: return False
        return bool(deriv) and deriv[-1] == ("all",)
    for p in (5, 13, 101, 1009):
        deriv = [("inst", c) for c in range(p)] + [("all",)]              # the m premises phi(c), one per element, then the universal rule
        ok &= bare_accepts(deriv, p) and len(deriv) == p + 1 and all(len(deriv) > H for H in range(p))
        ok &= not any(bare_accepts(deriv[:c] + deriv[c + 1:], p) for c in range(p))   # with any one premise missing the rule does not apply
        det.append(f"m={p}: length {len(deriv)}")
    n_sub = 0
    for p in (5, 13):                                                    # every subset of the premises: the rule applies to the full set alone
        for mask in range(2 ** p):
            n_sub += 1
            ok &= bare_accepts([("inst", c) for c in range(p) if (mask >> c) & 1] + [("all",)], p) == (mask == 2 ** p - 1)
    ok &= n_sub == 2 ** 5 + 2 ** 13 == 8224
    ok &= not bare_accepts([("inst", c) for c in range(5)] + [("all",)], 5, lambda x, p: (x * x) % p == x)   # the controls: a false premise (2*2 = 2) is rejected,
    ok &= not bare_accepts([("inst", c) for c in range(5)], 5)                                              # and premises without the universal step derive no global clause
    def rich_accepts(deriv, p):
        """A richer system: the bare calculus with one more rule, which asserts the clause as an axiom on syntactic recognition."""
        return deriv == [("ax", "Ax x+0=x")] or bare_accepts(deriv, p)
    ok &= all(rich_accepts([("ax", "Ax x+0=x")], p) and not bare_accepts([("ax", "Ax x+0=x")], p) for p in (5, 13, 101, 1009))   # there the clause has a one-line derivation
    # 25:E4 (p25022)
    check("C3", "a global clause in the bare evaluation calculus: the universal rule for Ax x+0=x applies to the full set of its m premises alone (all 8224 premise sets for m = 5, 13; every single omission for m = 101, 1009), so the derivation has length m+1, beyond every budget H < m; a false premise is rejected, premises without the universal step derive nothing, and a richer system with an axiom rule for the clause derives it in one line", ok,
          "; ".join(det) + f"; {n_sub} premise sets")

    # C4 the length horizon: truths longer than the budget, built and measured
    ok = True; det = []
    def comb(l, left):
        """The left comb ((1+1)+1)+… or the right comb 1+(1+(…)) with l leaves, as a tree."""
        t = 1
        for _ in range(l - 1): t = (t, 1) if left else (1, t)
        return t
    for B in (20, 100, 1000):
        l = (B + 5) // 8 + 1
        L, R = comb(l, True), comb(l, False)
        eq = tree_text(L) + "=" + tree_text(R)                            # the equation, written out
        ok &= L != R and len(eq) > B                                      # longer than every record of length <= B, which would have to contain it
        ok &= all(tree_value(L, p) == tree_value(R, p) for p in (P_SMALL, P_MID))   # and true in M_p
        ok &= len(eq) - 8 <= B                                            # the comb pair one leaf shorter fits: the horizon sits at this length
        det.append(f"B={B}: a true equation of {len(eq)} symbols")
    # 25:G1 (p25028)
    check("C4", "the length horizon on instances: for B = 20, 100, 1000 the equation between the left comb and the right comb of floor((B+5)/8)+1 leaves, built and written out, is true in M_13 and M_1000033 and longer than B, so no record of length <= B contains it", ok,
          "; ".join(det))

    # C5 the evaluation ceiling: the one-rule system D_tt
    ok = True; det = []
    for p in (5, 7):
        pool = {}; expect = {}                                            # the sample and its negations: text -> (pattern, matrix); the value number theory gives each
        for text, pat, mat, want in sentences(p):
            pool[text] = (pat, mat); expect[text] = want
            pool["not " + text] = ("".join("E" if c == "A" else "A" for c in pat), lambda v, mat=mat: not mat(v)); expect["not " + text] = not want
        cost = [0]
        def dtt_accepts(deriv):
            """D_tt: every line is a sentence asserted outright, its side condition truth under exhaustive evaluation."""
            return all(decide(p, *pool[line], cost) for line in deriv)
        ok &= all(dtt_accepts([t]) == expect[t] for t in pool)            # D_tt derives exactly the true sentences: sound, and complete on the sample
        truths = [t for t in pool if expect[t]]
        ok &= len(pool) == 16 and len(truths) == 8
        for t in truths:
            cost[0] = 0; ok &= dtt_accepts([t]) and cost[0] == p ** len(pool[t][0])   # the one-line derivation [t]; its step-check: m^q evaluations at depth q
        ok &= not any(dtt_accepts([t, f]) or dtt_accepts([f, t]) for t in truths[:2] for f in pool if not expect[f])   # a false line anywhere spoils a derivation
        det.append(f"p={p}: 8 truths each derived in one line, 8 falsehoods rejected, step-check {p}^q evaluations (q = 3: {p**3})")
    # 25:G2 (p25029)
    check("C5", "the evaluation ceiling: the one-rule system D_tt accepts exactly the sentences number theory makes true (a sample of 8 sentences and their negations over M_5, M_7), each true one derived in one line, the line being the sentence itself, while the step-check of the one rule performs m^q evaluations at depth q", ok, "; ".join(det))

    # C6 the decomposition's counting cells: bounded consistency by exhaustive search; its brute certificate; reach against the budget
    ok = True
    M = Mp(5); n_rec = n_acc = n_false = n_absurd = n_absurd_acc = n_cut = 0
    def ext(rec, depth):
        """Every record of at most `depth` further term steps followed by an end step."""
        nonlocal n_rec, n_acc, n_false, n_absurd, n_absurd_acc, n_cut, ok
        k = len(rec)
        for i in range(k):
            for j in range(k):
                full = rec + [("=", i, j)]; n_rec += 1
                acc, vals, _, _, _ = verify(full, M)
                absurd = term_of(full, i) == ("c", 0) and term_of(full, j) == ("c", 1)      # the record ends in the absurdity 0 = 1
                n_absurd += absurd
                if acc:
                    n_acc += 1; n_absurd_acc += absurd
                    n_false += eval_term(M, term_of(full, i)) != eval_term(M, term_of(full, j))   # the end sentence, evaluated from the tables
        if depth == 0: return
        for st in [("c", 0), ("c", 1)] + [("o", op, i, j, v) for op in "+*" for i in range(k) for j in range(k) for v in range(5)]:
            if st[0] == "o" and lookup(M, st[1], verify(rec, M)[1][st[2]], verify(rec, M)[1][st[3]]) != st[4]:
                n_rec += 1; n_cut += 1; ok &= not verify(rec + [st], M)[0]   # a step with a wrong value is rejected
                continue
            ext(rec + [st], depth - 1)
    ext([], 3)
    ok &= (n_rec, n_cut, n_acc) == (1026, 272, 562) and n_false == 0      # 754 records with an end step, 272 cut at a wrong value; soundness on every accepted record
    ok &= n_absurd == 34 and n_absurd_acc == 0                           # Con: 34 candidates end in 0 = 1, and none is accepted
    n_strings = 0
    for a in (2, 3):                                                     # the brute certificate of Con_H lists every candidate record of length <= H:
        for H in range(1, 11):                                           # their number, counted by enumeration, exceeds the budget H
            n = sum(1 for k in range(H + 1) for _ in itertools.product(range(a), repeat=k)); n_strings += n
            ok &= n == (a ** (H + 1) - 1) // (a - 1) > H
    ok &= n_strings == 136935
    eqs = sorted(len(tree_text(t)) * 2 + 1 for l in range(1, 11) for t in trees(l))    # the reflexivity instances t = t, written out: their lengths
    reach = lambda B: sum(1 for L in eqs if L <= B)                       # those that fit in a budget of B symbols
    ok &= eqs[0] == 3 and all(reach(B) < reach(B + 8) for B in range(3, 68))   # the reach grows over every 8 symbols of budget …
    ok &= all(reach(B) == reach(B + 1) for B in range(3, 10))             # … and not with every symbol: 3 <= B <= 10 holds the one instance 1 = 1
    # 25:G7 (p25034)
    check("C6", "the decomposition's counting cells: bounded consistency decided by exhaustive search — of the 1026 candidate records of at most three term steps over M_5 (754 with an end step, 272 cut at a step with a wrong value), every accepted one has a true end sentence, and the 34 ending in 0 = 1 are all rejected; the brute certificate of Con_H lists (a^(H+1)-1)/(a-1) > H candidate records (enumerated, a = 2, 3, H <= 10); the reflexivity instances t = t that fit a budget B grow in number over every 8 symbols (enumerated, 3 <= B < 68), not with every symbol", ok,
          f"{n_rec} records scanned, {n_acc} accepted, {n_false} with a false end sentence, {n_absurd} ending in 0 = 1 ({n_absurd_acc} accepted); {n_strings} candidate strings enumerated; reach at B = 3, 11, 19, 27: {reach(3)}, {reach(11)}, {reach(19)}, {reach(27)}")

# ------------------------------------------------------------------------------------------------------------
# block D: the diagonal does not migrate (25:F1, F2, F3, F4, F6) — Section 5.2.
# D1: mention cost — a coordinate on which the truth of a formula depends is a variable that occurs free in it: on a family of
# formulas over M_3 and on EVERY formula of length <= 9 over M_2 in four variables, each written out and read back by the
# independent reader.  D2: the no-compression theorem on built instances — the graph of every injective map on M_2^N depends
# on all 2N coordinates; every formula that defines such a graph mentions all 2N variables; the diagonal formula written out
# from each of them computes theta at the diagonal image, names each coordinate of v at least three times and each of u at
# least once, and is longer than N, so its code is no N-tuple; with the scales split it is longer than the scale of v.
# D3: density — an injective coding of the a^n strings into k-tuples needs m^k >= a^n (below it every coding collides), so
# n < dk, d the digit count of m in base a; the diagonal formula with k coordinates in v and k1 in u costs at least
# 2c(k) + c(k+k1) symbols, and its instance lambda at least 3c(k) + k1.  D4: quotation exceeds mention — over EVERY formula
# of length <= 9 in six variables, the truth depends on fewer coordinates than the formula has symbols.  D5: the threshold
# lies inside the count — the two costs fit their codes for no k beyond k*(M), no instance codes lambda at a length
# n >= t(M) = d k*(M), and t(M) < m in every structure.
#
# The statements of D3 and D5 hold for every alphabet a >= 2 and every structure; the checks decide ranges and the base
# cases.  Notation: d is the digit count of m, a^(d-1) <= m < a^d; c(j) is the total length of the j shortest names; k >= 1
# and k1 >= 1 are the coordinates of v and of u in delta(u) = Ev (Diag(u, v) & theta(v)), and lambda = delta(code of delta).
#   The codes.  The code of delta is the k1-tuple that fills u; it codes a string of some length n1 >= |delta|.  The code of
# lambda is a k-tuple, the argument of theta; it codes a string of length n >= |lambda|.  An injective coding of the strings
# of length n by k-tuples has a^n <= m^k < a^(dk), so n < dk; likewise n1 < d k1.  At one scale k1 = k and n1 = n.
#   The count.  In delta the block binds the k coordinates of v, Diag has k1 + k argument places and theta has k: each
# coordinate of v is named three times and each of u once, by k + k1 distinct names.  Of k + k1 distinct names the k + k1
# shortest cost least, and the weight 3 goes to the k shortest: |delta| >= 2c(k) + c(k+k1).  In lambda the places of u hold
# k1 closed terms of at least one symbol: |lambda| >= 3c(k) + k1.  So an instance needs
#       2c(k) + c(k+k1) < d k1     and     3c(k) + k1 < dk,
# and k*(M) is the largest k for which some k1 satisfies both (0 if none).  At one scale the first reads N(k) < dk,
# N(k) = 2c(k) + c(2k), and implies the second.
#   (i) Bounds.  c(k) is the sum over j >= 0 of the number of the k shortest names longer than j.  The names of at most j
# letters number A_j <= 2a^j - 2, so c(k) > kJ - 2a^J for every J >= 1.  With J = floor(d/3) + 1, 3J >= d + 1, and
# 3c(k) < dk gives k <= k(3J - d) < 6a^J: k*(M) < 6a^(floor(d/3)+1).  At one scale the same sum with the weights gives
# N(k) > 4kJ - 6a^J; with J = floor(d/4) + 1, 4J >= d + 1, and N(k) < dk gives k < 6a^(floor(d/4)+1).  N(k)/k =
# 2 c(k)/k + 2 c(2k)/(2k), and each term is twice the mean length of an initial run of the names in order of length, so
# N(k)/k does not decrease: at one scale the k that pass form an initial segment.
#   (ii) No instance at n >= t(M) = d k*(M).  An instance has k <= k*(M) by definition and n < dk, whatever the two
# injective codings.
#   (iii) t(M) < m.  For d <= 4 there is no instance: c(j) >= j, so the second inequality gives 3k + k1 < 4k, k1 < k, and
# the first gives 3k + k1 < 4 k1, k1 > k.  For d >= 5, d k*(M) < 6d a^J, J = floor(d/3) + 1.  For d >= 13,
# 6d a^J <= a^(d-1): it holds at d = 13, 14, 15 for a = 2 (2496 <= 4096, 2688 <= 8192, 5760 <= 16384), hence for every a
# (J < d - 1), and the step d -> d+3 multiplies the left side by a(d+3)/d < a^3.  For d = 5, …, 12 it fails at fifteen
# pairs (a, d), all with a <= 5, which D5 decides directly, and holds at every larger a (J < d - 1 again).  So
# t(M) < a^(d-1) <= m.
#   Below, at one scale.  For k <= floor(a^floor((d-1)/4) / 2) the 2k names have at most floor((d-1)/4) letters, so
# N(k) <= (d-1)k, which is at most the largest n with a^n <= m^k: the count leaves these k open.
# The cut 2^400 of the ranges is a test parameter.
def block_D():
    """Block D — the diagonal does not migrate: mention cost, the template, density (EXACT): D1–D5."""
    # D1 mention cost: a family over M_3, then every short formula over M_2
    m, V = 3, 3
    assigns = list(itertools.product(range(m), repeat=V)); idx = {a: i for i, a in enumerate(assigns)}
    leaf = [(("v", i), tuple(a[i] for a in assigns), 1, frozenset([i])) for i in range(V)] + [(("k", c), tuple(c for _ in assigns), 1, frozenset()) for c in (0, 1)]
    terms = list(leaf)
    for op, f in (("+", lambda x, y: (x + y) % m), ("*", lambda x, y: (x * y) % m)):
        for s in leaf:
            for t in leaf:
                terms.append(((op, s[0], t[0]), tuple(f(x, y) for x, y in zip(s[1], t[1])), s[2] + t[2] + 3, s[3] | t[3]))
    # a formula is (truth table over the 27 assignments, length in symbols, free variables)
    atoms = [(tuple(x == y for x, y in zip(s[1], t[1])), s[2] + t[2] + 1, s[3] | t[3]) for s in terms for t in terms]
    def neg(f): return (tuple(not b for b in f[0]), f[1] + 1, f[2])
    def ex(i, f):                                                       # Ev_i phi: 2 more symbols; v_i is bound
        tab = tuple(any(f[0][idx[a[:i] + (c,) + a[i + 1:]]] for c in range(m)) for a in assigns)
        return (tab, f[1] + 2, f[2] - {i})
    def conj(f, g): return (tuple(x and y for x, y in zip(f[0], g[0])), f[1] + g[1] + 3, f[2] | g[2])
    leaf_atoms = [(tuple(x == y for x, y in zip(s[1], t[1])), s[2] + t[2] + 1, s[3] | t[3]) for s in leaf for t in leaf]
    family = list(atoms) + [neg(f) for f in atoms] + [ex(i, f) for i in range(V) for f in atoms]
    family += [ex(i, ex(j, f)) for i in range(V) for j in range(V) for f in atoms] + [neg(ex(i, f)) for i in range(V) for f in atoms]
    family += [conj(f, g) for f in leaf_atoms for g in leaf_atoms] + [ex(i, conj(f, g)) for i in range(V) for f in leaf_atoms for g in leaf_atoms]
    def depends(tab, i):
        return any(tab[idx[a]] != tab[idx[a[:i] + (c,) + a[i + 1:]]] for a in assigns for c in range(m))
    ok = True; n_dep = [0] * (V + 1); n_idle = 0
    for tab, length, free in family:
        dep = {i for i in range(V) if depends(tab, i)}
        ok &= dep <= free                                               # truth depends on coordinate i  =>  v_i occurs (free)
        n_dep[len(dep)] += 1; n_idle += dep != free                     # the converse fails: a variable can occur idly (v0 = v0)
    ok &= len(family) == 53925 and n_dep == [31839, 13872, 7566, 648] and n_idle == 21903
    # every formula of length <= 9 over M_2 in four variables, written out.  The enumeration's truth table and free variables are
    # first checked against the independent reader of the written formula, under every assignment; then the lemma.
    forms, swap = formulas_M2(4, 9); n2 = n2_dep = 0; by_free = [0] * 5
    for L, fs in forms.items():
        for tab, fv, tx in fs:
            n2 += 1
            reads = [read_formula(tx, 0, {VARS[i]: (a >> i) & 1 for i in range(4)}) for a in range(16)]
            ok &= len(tx) == L and all(r is not None and r[1] == L and r[0] == bool((tab >> a) & 1) for a, r in enumerate(reads))
            free = reads[0][2]
            ok &= free == frozenset(VARS[i] for i in range(4) if (fv >> i) & 1)        # the free variables, read off the written formula
            dep = [i for i in range(4) if swap(tab, i) != tab]
            ok &= all(VARS[i] in free for i in dep)                     # a coordinate read is a variable occurring free
            n2_dep += bool(dep); by_free[len(free)] += 1
    ok &= n2 == 17820 and n2_dep == 8820 and by_free == [4604, 8344, 4128, 720, 24]
    # 25:F1 (p25023)
    check("D1", "mention cost: a coordinate on which the truth of a formula depends is a variable occurring free in it — on a family of 53925 formulas over M_3 (equations between terms with at most one operation, negations, conjunctions, one or two quantifiers) and on all 17820 formulas of length <= 9 over M_2 in four variables, each written out and read back by an independent reader; the converse fails (a variable can occur idly)", ok,
          f"{len(family)} formulas over M_3, depending on 0/1/2/3 coordinates: {n_dep[0]}/{n_dep[1]}/{n_dep[2]}/{n_dep[3]}, {n_idle} with an idle variable; {n2} formulas over M_2, {n2_dep} with a dependence, by number of free variables 0..4: {by_free}")

    # D2 the no-compression theorem on built instances
    ok = True; n_maps = 0
    def graph_depends(d, N):
        """The coordinates (of u, then of v) on which the relation v = d(u) on M_2^N x M_2^N depends, by reassigning each one."""
        rel = lambda u, v: v == d[u]
        dep_u = [any(rel(u, v) != rel(u ^ (1 << i), v) for u in range(1 << N) for v in range(1 << N)) for i in range(N)]
        dep_v = [any(rel(u, v) != rel(u, v ^ (1 << i)) for u in range(1 << N) for v in range(1 << N)) for i in range(N)]
        return dep_u + dep_v
    for N in (1, 2, 3):
        for k, d in enumerate(itertools.permutations(range(1 << N))):   # the injective maps on M_2^N (N = 3: every 37th of the 40320)
            if N == 3 and k % 37: continue
            n_maps += 1; ok &= all(graph_depends(d, N))                 # the diagonal relation depends on every one of its 2N coordinates
        ok &= graph_depends((0,) * (1 << N), N) == [False] * N + [True] * N   # the control: the graph of a constant map reads no coordinate of u
    ok &= n_maps == 2 + 24 + 1090
    # the template itself, on written formulas.  u = v_0..v_{N-1} carries a code of scale N, v = v_N..v_{N+N2-1} a code of scale N2
    # (N2 = N: the theorem's template; N2 > N: the scales split).  Diag ranges over EVERY formula of length <= 9 whose relation is the
    # graph of an injective map u -> v, theta over EVERY formula of length <= 5 in v alone that reads each coordinate of v.
    built = []; n_delta = 0; census = {}; least_occ = (99, 99)
    for N, N2 in ((1, 1), (2, 2), (1, 2)):
        V = N + N2; forms, swap = formulas_M2(V, 9); u_side, v_side = 1 << N, 1 << N2
        u_names, v_names = VARS[:N], VARS[N:V]
        def as_map(tab):
            """The injective map d: M_2^N -> M_2^N2 whose graph the table is, or None."""
            d = []
            for u in range(u_side):
                vs = [v for v in range(v_side) if (tab >> (u + u_side * v)) & 1]
                if len(vs) != 1: return None
                d.append(vs[0])
            return tuple(d) if len(set(d)) == u_side else None
        diags = [(L, tx, as_map(tab)) for L, fs in forms.items() for tab, fv, tx in fs if as_map(tab) is not None]
        thetas = [(L, tx) for L, fs in forms.items() if L <= 5 for tab, fv, tx in fs
                  if fv >> N << N == fv and all(swap(tab, i) != tab for i in range(N, V))]      # theta(v): reads every coordinate of v, no other variable
        ok &= len(diags) > 0 and len(thetas) > 0
        for Ld, dtx, d in diags:
            ok &= {c for c in dtx if c in VARS} == set(VARS[:V]) and Ld >= V   # the written Diag mentions every one of its N + N2 variables
        for Lt, ttx in thetas:
            ok &= set(v_names) <= {c for c in ttx if c in VARS} and Lt >= N2   # the written theta mentions every coordinate of v
        for Ld, dtx, d in diags:
            for Lt, ttx in thetas:
                delta = "".join("E" + x for x in v_names) + "(" + dtx + "&" + ttx + ")"   # delta(u) = Ev (Diag(u, v) & theta(v)), written out
                n_delta += 1
                for u in range(u_side):
                    got = read_formula(delta, 0, {u_names[i]: (u >> i) & 1 for i in range(N)})
                    want = read_formula(ttx, 0, {v_names[i]: (d[u] >> i) & 1 for i in range(N2)})
                    ok &= got is not None and got[1] == len(delta) and got[2] <= set(u_names) and got[0] == want[0]   # delta(u) is theta at the diagonal image of u
                occ_v = min(delta.count(x) for x in v_names); occ_u = min(delta.count(x) for x in u_names)
                ok &= occ_v >= 3 and occ_u >= 1                         # each coordinate of v is named three times (block, Diag, theta), each of u once
                least_occ = (min(least_occ[0], occ_v), min(least_occ[1], occ_u))
                ok &= len(delta) == 2 * N2 + 3 + Ld + Lt                # the written length: the block, the conjunction, Diag, theta
                ok &= len(delta) >= 3 * N + Lt > N and len(delta) > Lt >= N2   # longer than N and than N2: its code is no N-tuple, and no N2-tuple
        census[(N, N2)] = (len(diags), min(L for L, _, _ in diags), len(thetas))
        built.append(f"(N, N2) = ({N}, {N2}): {len(diags)} formulas define a diagonal relation (shortest {census[(N, N2)][1]} symbols), {len(thetas)} formulas theta")
    ok &= census == {(1, 1): (142, 3, 16), (2, 2): (16, 9, 10), (1, 2): (56, 9, 8)} and n_delta == 142 * 16 + 16 * 10 + 56 * 8 == 2880
    ok &= least_occ == (3, 1)                                           # the counts 3 and 1 are attained
    # 25:F2 (p25024)
    check("D2", "no compression on built instances: the graph of every injective map on M_2^N depends on all 2N coordinates (N = 1, 2; a fixed sample of 1090 maps at N = 3; a constant map as control); every formula of length <= 9 that defines such a graph (N = 1, 2) mentions all 2N variables; each of the 2432 diagonal formulas Ev (Diag & theta), written out from them with each non-degenerate theta of length <= 5 and read back by the independent reader, computes theta at the diagonal image, names each coordinate of v at least three times and each of u at least once (both counts attained), and has at least 3N + |theta| > N symbols, so its code is no N-tuple; with the scales split (u of scale 1, v of scale 2; 448 formulas) it is longer than theta, which is at least as long as the scale of v", ok,
          f"{n_maps} injective maps; " + "; ".join(built) + f"; {n_delta} diagonal formulas written out")

    # D3 density and the name count of the template
    ok = True
    n_cases = n_codings = 0
    for a, m, n, k in ((2, 3, 2, 1), (3, 2, 1, 1), (2, 2, 3, 2), (3, 4, 2, 1), (2, 5, 3, 1)):   # below m^k >= a^n every coding collides: every map, five cases
        src = list(itertools.product(range(a), repeat=n)); n_states = m ** k
        assert n_states < len(src) and n_states ** len(src) <= 400000
        n_cases += 1
        for f in itertools.product(range(n_states), repeat=len(src)):
            n_codings += 1; ok &= len(set(f)) < len(src)
    ok &= n_cases == 5 and n_codings == 3 ** 4 + 2 ** 3 + 4 ** 8 + 4 ** 9 + 5 ** 8 == 718394
    n_inj = sum(1 for f in itertools.product(range(4), repeat=4) if len(set(f)) == 4)
    ok &= n_inj == 24                                                    # the control: at m^k = a^n = 4 injective codings exist
    # the digit bound.  d is the digit count of m in base a: a^(d-1) <= m < a^d.  The longest strings an injective coding
    # by k-tuples reaches have the largest n with a^n <= m^k letters, and (d-1)k <= n < dk.
    T_EXACT.clear(); n_pairs = 0
    for a, top in ((2, 500), (3, 400), (4, 400), (5, 700)):              # every structure in a range, in exact integers
        for m in range(a, top + 1):
            d = 1
            while a ** d <= m: d += 1
            upto = 2 * 6 * a ** (d // 3 + 1)                             # every k up to twice the bound (i) of D5
            fit = fit_table(m, a, d, upto)
            for k in range(1, upto + 1):
                n_pairs += 1; n = fit[k]
                ok &= a ** n <= m ** k < a ** (n + 1) and (d - 1) * k <= n < d * k
            T_EXACT[(a, m)] = (d, fit)
    ok &= len(T_EXACT) == 499 + 398 + 397 + 696 == 1990 and n_pairs == 425112
    # the name count of the template, in integers.  With k coordinates in v and k1 in u the diagonal formula names k + k1
    # distinct variables, each coordinate of v three times and each of u once (D2).  Every ordering of k + k1 names chosen
    # among the k + k1 + 2 shortest, the first k of an ordering given to v: the least cost in delta is delta_names, the
    # least in lambda (a one-symbol term in each place of u) is lambda_names, and one ordering attains both.
    n_ord = 0; least = []; pairs = ((1, 1), (2, 2), (3, 3), (1, 2), (2, 1), (1, 3), (3, 1), (2, 3), (3, 2))
    for a in (2, 3):
        for k, k1 in pairs:
            pool = [L for L in range(1, 6) for _ in range(a ** L)][:k + k1 + 2]
            costs = set()
            for c in itertools.combinations(range(len(pool)), k + k1):
                for p in itertools.permutations([pool[x] for x in c]):
                    n_ord += 1; costs.add((3 * sum(p[:k]) + sum(p[k:]), 3 * sum(p[:k]) + k1))
            ok &= min(x for x, y in costs) == delta_names(k, k1, a) and min(y for x, y in costs) == lambda_names(k, k1, a)
            ok &= (delta_names(k, k1, a), lambda_names(k, k1, a)) in costs
            least.append((min(x for x, y in costs), min(y for x, y in costs)))
    ok &= n_ord == 52824
    ok &= least == [(4, 4), (10, 8), (18, 15), (6, 5), (8, 7), (8, 6), (14, 13), (12, 9), (16, 14), (4, 4), (9, 8), (15, 12), (5, 5), (7, 7), (7, 6), (11, 10), (11, 9), (13, 11)]
    # 25:F4 (p25048)
    check("D3", "density: an injective coding of the a^n strings into k-tuples needs m^k >= a^n — below it every coding collides (all 718394 maps, five cases), at equality injective codings exist — so n < dk, d the digit count of m in base a: the largest n with a^n <= m^k lies between (d-1)k and dk - 1 (425112 pairs (m, k): every k up to 12a^(floor(d/3)+1) in the 1990 structures a <= m <= 500 (a = 2), 400 (a = 3, 4), 700 (a = 5)); the diagonal formula with k coordinates in v and k1 in u names each coordinate of v three times and each of u once: over all 52824 orderings of k + k1 names chosen among the k + k1 + 2 shortest, the first k of an ordering given to v (a = 2, 3; nine pairs (k, k1) with k, k1 <= 3), the least cost in delta is 2c(k) + c(k+k1), the least in lambda, with a one-symbol term in each place of u, is 3c(k) + k1, and one ordering attains both, c the cost of the shortest names", ok,
          f"{n_codings} codings below the bound, all colliding; {n_pairs} pairs (m, k); (delta, lambda) costs at a = 2, (k, k1) = (1, 1), (2, 2), (3, 3), (2, 3): " + ", ".join(str((delta_names(k, k1, 2), lambda_names(k, k1, 2))) for k, k1 in ((1, 1), (2, 2), (3, 3), (2, 3))))

    # D4 quotation exceeds mention: every formula of length <= 9 in six variables
    ok = True
    forms, swap = formulas_M2(6, 9); n6 = 0; least = {}; most = {}; hist = [0] * 7
    for L, fs in forms.items():
        for tab, fv, tx in fs:
            n6 += 1
            r = read_formula(tx, 0, {})
            ok &= len(tx) == L and r is not None and r[1] == L and r[2] == frozenset(VARS[i] for i in range(6) if (fv >> i) & 1) and r[0] == bool(tab & 1)
            fl = [i for i in range(6) if (fv >> i) & 1]
            for bits in range(1, 1 << len(fl)):                          # every assignment to the free variables (the others 0)
                a = sum(1 << i for j, i in enumerate(fl) if (bits >> j) & 1)
                ok &= read_formula(tx, 0, {VARS[i]: 1 for i in fl if (a >> i) & 1})[0] == bool((tab >> a) & 1)
            ok &= all(swap(tab, i) == tab for i in range(6) if i not in fl)   # and the table does not move along a variable that is not free
            k = sum(1 for i in range(6) if swap(tab, i) != tab)          # the number of coordinates the truth depends on
            hist[k] += 1
            ok &= k < L                                                  # fewer than the formula has symbols
            least[k] = min(least.get(k, L), L); most[L] = max(most.get(L, 0), k)
    ok &= n6 == 65600 and least == {0: 3, 1: 3, 2: 3, 3: 7, 4: 9}        # the shortest formula reading k coordinates
    ok &= hist == [28430, 16320, 16170, 4320, 360, 0, 0]                 # the formulas by the number of coordinates read
    ok &= most == {3: 2, 4: 2, 5: 2, 6: 2, 7: 3, 8: 3, 9: 4}             # six variables are on offer; no formula of 9 symbols reads more than four
    # 25:F3 (p25025)
    check("D4", "quotation exceeds mention: over all 65600 formulas of length <= 9 over M_2 in six variables, written out, the truth depends on fewer coordinates than the formula has symbols — the shortest formula reading 2, 3, 4 coordinates has 3, 7, 9 symbols, and none of at most 9 symbols reads five of the six", ok,
          f"{n6} formulas; least length by coordinates read: {least}; most coordinates read by length: {most}")

    # D5 the threshold lies inside the count.  An instance with k coordinates in v and k1 in u needs lambda_names < dk and
    # delta_names < d k1 (admits).  k*(M) is the largest k for which some k1 admits; it depends on a and d alone.
    ok = True
    n_mono = 0; ends = []
    for a in (2, 3, 4, 5):                                               # one scale: N(k)/k does not decrease, N(k) = delta_names(k, k)
        for k in range(1, 20001):
            n_mono += 1; ok &= delta_names(k + 1, k + 1, a) * k >= delta_names(k, k, a) * (k + 1)
        ends.append(delta_names(20001, 20001, a))
    ok &= n_mono == 80000 and ends == [1029078, 686271, 556370, 486813]
    kstar = {}; n_direct = n_bound = n_scan = n_scan_k = n_scan_k1 = 0; left = []; inside = []
    for a in range(2, 41):                                               # by digit count: every alphabet a <= 40, every d >= 1 with a^d <= 2^400
        d = 1
        while a ** d <= 2 ** 400:
            n_direct += 1
            b3, b4 = 6 * a ** (d // 3 + 1), 6 * a ** (d // 4 + 1)        # the bounds (i)
            k_one = last_k(d, a, strict=True)                            # one scale: the largest k with N(k) < dk
            ok &= k_one < b4
            ok &= 3 * name_cost(b3, a) >= d * b3 and delta_names(b4, b4, a) >= d * b4    # at the bounds the counts fail; the quotients do not decrease, so they fail from there on
            by_bound = d * b3 <= a ** (d - 1)
            scanned = d <= 12 and b3 <= 10000
            if scanned:                                                  # k*(M) by a scan of every k below twice the bound
                scan = range(1, 2 * b3); n_scan += 1; n_scan_k += len(scan); good = []; one = 0
                for k in scan:
                    reach = d * k - 1 - 3 * name_cost(k, a)              # lambda's inequality allows the k1 <= reach
                    ok &= not admits(k, max(reach, 0) + 1, d, a)         # and no further k1
                    for k1 in range(1, reach + 1):                       # every such k1
                        n_scan_k1 += 1
                        if admits(k, k1, d, a):
                            if not good or good[-1] != k: good.append(k)
                            if k1 == k: one = k
                K = max(good, default=0); kstar[(a, d)] = K
                ok &= good == list(range(1, K + 1)) and K < b3           # an initial segment, ending below the bound
                ok &= d * K < a ** (d - 1)                               # directly: t(M) = d k*(M) < a^(d-1) <= m
                inside.append((Fraction(d * K, a ** (d - 1)), a, d))
                ok &= (K == 0) == (d <= 4) and one == k_one <= K         # the one-scale threshold found both ways, at most k*(M)
            if d >= 13: n_bound += 1; ok &= by_bound
            elif d >= 5 and not by_bound: left.append((a, d))
            ok &= scanned or (d >= 5 and by_bound)                       # every case is decided by the scan or by the bound
            d += 1
    ok &= (n_direct, n_bound, n_scan, n_scan_k, n_scan_k1) == (4347, 3879, 243, 1070649, 1209527) and max(inside) == (Fraction(21, 32), 2, 7)
    ok &= left == [(2, 5), (2, 6), (2, 7), (2, 8), (2, 9), (2, 10), (2, 11), (2, 12), (3, 5), (3, 6), (3, 7), (4, 5), (4, 6), (5, 5), (5, 6)]
    ok &= all(x in kstar for x in left) and [d * kstar[(a, d)] for a, d in left] == [10, 18, 42, 72, 126, 180, 275, 396, 15, 36, 84, 20, 54, 30, 66]
    ok &= [last_k(d, 2, strict=True) for d in (5, 9, 17, 33, 65)] == [1, 7, 43, 806, 209693] and [kstar[(2, d)] for d in (5, 9, 12)] == [2, 14, 33]
    # the structures of D3, in exact integers: every instance the names leave open, a^n <= m^k and a^n1 <= m^k1 exactly
    n_inst = n_one = n_try = n_k = 0; share = []; slack = None
    for (a, m), (d, fit) in T_EXACT.items():
        K = kstar[(a, d)]; t = d * K
        ok &= t < m and (K == 0) == (m < a ** 4)
        one = 0
        for k in range(1, len(fit)):                                     # every k up to twice the bound
            n_k += 1
            reach = fit[k] - 3 * name_cost(k, a)                         # every k1 with lambda's symbols within the reach of k-tuples: k1 <= reach
            ok &= reach <= len(fit) - 1                                  # the table covers them all
            for k1 in range(1, reach + 1):
                n_try += 1
                if delta_names(k, k1, a) <= fit[k1]:                     # an instance left open: delta's symbols within the reach of k1-tuples
                    n_inst += 1; one += k1 == k
                    ok &= admits(k, k1, d, a) and k <= K and fit[k] < t  # it is admitted in digit form, and lambda's length is below t(M)
                    slack = t - fit[k] if slack is None else min(slack, t - fit[k])
        n_one += one
        ok &= all(lambda_names(k, k, a) <= delta_names(k, k, a) <= fit[k] for k in range(1, a ** ((d - 1) // 4) // 2 + 1))   # below, at one scale: each of these k is left open
        share.append((Fraction(t, m), a, m))
    ok &= (n_k, n_try, n_inst, n_one, slack) == (425112, 102969, 39624, 3615, 1) and max(share) == (Fraction(21, 32), 2, 64)
    # 25:F6 (p25047)
    check("D5", "the threshold lies inside the count: an instance with k coordinates in v and k1 in u needs 2c(k) + c(k+k1) < d k1 and 3c(k) + k1 < dk, d the digit count of m in base a; k*(M) is the largest k for which some k1 satisfies both, and t(M) = d k*(M) — by digit count, k*(M) depending on a and d alone, at every alphabet a <= 40 and every d >= 1 with a^d <= 2^400 (4347 cases): where d <= 12 and 6a^(floor(d/3)+1) <= 10000 (243 cases) a scan of every k below twice that bound (1070649 values) and every k1 the second inequality allows (1209527 pairs) finds the k that pass to be the k <= k*(M), with k*(M) < 6a^(floor(d/3)+1), d k*(M) < a^(d-1) <= m (at most 21/32 of a^(d-1), at a = 2, d = 7), k*(M) = 0 exactly for d <= 4, and the one-scale threshold, the largest k with 2c(k) + c(2k) < dk, found by the scan and by bisection, at most k*(M); from d = 13 on k*(M) < 6a^(floor(d/3)+1) alone gives d k*(M) < a^(d-1) (3879 cases), for d = 5..12 it leaves fifteen pairs (a, d), all scanned, and every case is decided by the scan or the bound; at one scale k < 6a^(floor(d/4)+1) in every case, and (2c(k) + c(2k))/k does not decrease (80000 steps: k <= 20000, a = 2..5); in the 1990 structures of D3, in exact integers, each of the 39624 instances the names leave open (a^n <= m^k, a^n1 <= m^k1; every k up to 12a^(floor(d/3)+1), the 425112 pairs (m, k) of D3, and every k1 within lambda's reach, 102969 pairs (k, k1)) passes in digit form and has n < t(M) (some instance reaches n = t(M) - 1), so no instance codes lambda at a length n >= t(M) under any injective codings; there t(M) < m, k*(M) = 0 exactly when m < a^4, t(M)/m is at most 21/32 (at a = 2, m = 64), and at one scale every k <= floor(a^floor((d-1)/4) / 2) is left open", ok,
          f"{n_direct} pairs (a, d); k* at a = 2, d = 5, 9, 12: {[kstar[(2, d)] for d in (5, 9, 12)]}; one scale at d = 5, 9, 17, 33, 65: {[last_k(d, 2, strict=True) for d in (5, 9, 17, 33, 65)]}; the fifteen pairs: " + "; ".join(f"({a}, {d}): {d * kstar[(a, d)]} < {a ** (d - 1)}" for a, d in left) + f"; {n_inst} exact instances, {n_one} at one scale")

# ------------------------------------------------------------------------------------------------------------
# block E: fragment truth (25:G4, G5) — Section 5.3.
# E1: the prefix simulation — the sentence with the uniform prefix Ay1 Ex1 … Ayd Exd and the clause x_i = y_i at the
# universal positions, evaluated as written, decides what the coded prefix Q1 … Qd decides: every pattern against EVERY
# matrix over M_2 (depth <= 3) and M_3 (depth <= 2), and against a matrix family over M_5.  E2: the guessed labels — a
# labelling consistent with the position-local clauses and rooted true exists exactly for the well-formed true codes, and
# it is unique; and the composition of the label layers with the pairing prefix agrees with direct truth on every string
# of length <= 6 of a small language, conjunctions included.
def block_E():
    """Block E — fragment truth: the pairing prefix and the guessed labels (EXACT): E1–E2."""
    def paired(m, pattern, matrix):
        """The sentence of the lemma's right-hand side, evaluated by the shared evaluator: the uniform prefix Ay1 Ex1 … Ayd Exd over
        the matrix [ AND_{i: Q_i = A} x_i = y_i  &  psi(x) ], the copy clauses standing in the matrix."""
        d = len(pattern)
        def mat(v):                                                      # v = (y1, x1, …, yd, xd)
            ys, xs = v[0::2], v[1::2]
            return all(xs[i] == ys[i] for i in range(d) if pattern[i] == "A") and matrix(tuple(xs))
        return decide(m, "AE" * d, mat)
    ok = True; n = 0; det = []
    for m, dmax in ((2, 3), (3, 2)):
        for d in range(1, dmax + 1):
            pts = list(itertools.product(range(m), repeat=d))
            for bits in range(2 ** len(pts)):                            # every matrix: every subset of M^d
                S = {pt for k, pt in enumerate(pts) if (bits >> k) & 1}
                for pat in itertools.product("AE", repeat=d):
                    n += 1
                    ok &= decide(m, "".join(pat), lambda v: v in S) == paired(m, pat, lambda v: v in S)
        det.append(f"M_{m}: every matrix to depth {dmax}")
    n5 = 0
    for pat in itertools.product("AE", repeat=2):                        # over M_5, depth 2: the matrices c1 x1 + c2 x2 in S, six coefficient pairs, every S
        for cs in ((1, 2), (3, 1), (1, 1), (2, 3), (4, 1), (0, 1)):
            for smask in range(32):
                S = {t for t in range(5) if (smask >> t) & 1}
                mat = lambda v, cs=cs, S=S: sum(c * x for c, x in zip(cs, v)) % 5 in S
                n5 += 1; ok &= decide(5, "".join(pat), mat) == paired(5, pat, mat)
    ok &= n == 4184 and n5 == 768
    wrong = sum(decide(2, "".join(pat), lambda v: v in S) != decide(2, "AE" * 2, lambda v: (v[1], v[3]) in S)     # the control: without the copy clauses
                for S in ({(0, 0)}, {(0, 1), (1, 0)}) for pat in itertools.product("AE", repeat=2))              # the uniform prefix decides something else
    ok &= wrong > 0
    # 25:G4 (p25031)
    check("E1", "the prefix simulation: the sentence Ay1 Ex1 ... Ayd Exd [x_i = y_i at the coded universal positions & psi(x)], evaluated as written by the shared evaluator, agrees with Q1 z1 ... Qd zd psi(z) on every pattern and every matrix over M_2 (depth <= 3) and M_3 (depth <= 2), 4184 instances, and on a family of 768 pattern-matrix instances over M_5 at depth 2; without the copy clauses the two differ", ok,
          f"{n} exhaustive instances ({'; '.join(det)}) + {n5} over M_5")

    # E2 the guessed labels: propositional layer, then the composition with the prefix and the environments
    def parse(s, i=0):
        """Polish notation over T, F, N (negation), C (conjunction): (value, next position) or None."""
        if i >= len(s): return None
        c = s[i]
        if c in "TF": return (c == "T", i + 1)
        if c == "N":
            r = parse(s, i + 1); return None if r is None else (not r[0], r[1])
        if c == "C":
            r1 = parse(s, i + 1)
            if r1 is None: return None
            r2 = parse(s, r1[1]); return None if r2 is None else (r1[0] and r2[0], r2[1])
        return None
    def direct(s):
        r = parse(s); return None if r is None or r[1] != len(s) else r[0]
    def consistent(s, ends, vals):
        """The position-local clauses: ends[i] = the end of the subformula opening at i, vals[i] = its value."""
        n = len(s)
        for i, c in enumerate(s):
            if c in "TF":
                if not (ends[i] == i + 1 and vals[i] == (c == "T")): return False
            elif c == "N":
                if i + 1 >= n or not (ends[i] == ends[i + 1] and vals[i] == (not vals[i + 1])): return False
            elif c == "C":
                if i + 1 >= n: return False
                j = ends[i + 1]
                if j >= n or not (ends[i] == ends[j] and vals[i] == (vals[i + 1] and vals[j])): return False
        return True
    def labellings(s, root=None):
        n = len(s); out = 0
        for ends in itertools.product(range(1, n + 1), repeat=n):
            if ends[0] != n: continue
            for vals in itertools.product((False, True), repeat=n):
                if root is not None and vals[0] != root: continue
                out += consistent(s, ends, vals)
        return out
    ok = True; n_codes = n_wf = 0
    for L in range(1, 5):
        for tup in itertools.product("TFNC", repeat=L):
            s = "".join(tup); n_codes += 1; d = direct(s)
            if d is None: ok &= labellings(s) == 0                        # an ill-formed code admits no labelling
            else:
                n_wf += 1
                ok &= labellings(s) == 1 and labellings(s, True) == (1 if d else 0)   # exactly the labelling of its parse tree; rooted true iff true
    ok &= (n_codes, n_wf) == (340, 24)
    def backward(s):
        """The one candidate labelling, computed right to left from the clauses; None if a clause cannot be met."""
        n = len(s); ends = [0] * n; vals = [False] * n
        for i in range(n - 1, -1, -1):
            c = s[i]
            if c in "TF": ends[i], vals[i] = i + 1, c == "T"
            elif c == "N":
                if i + 1 >= n: return None
                ends[i], vals[i] = ends[i + 1], not vals[i + 1]
            else:
                if i + 1 >= n or ends[i + 1] >= n: return None
                j = ends[i + 1]; ends[i], vals[i] = ends[j], vals[i + 1] and vals[j]
        return (vals[0] if ends[0] == n else None)
    n_long = 0
    for L in range(1, 9):
        for tup in itertools.product("TFNC", repeat=L):
            s = "".join(tup); n_long += 1
            b = backward(s); d = direct(s)
            ok &= (b is None) == (d is None) and b == d                   # the pass labels exactly the well-formed codes, with their values
    ok &= n_long == 87380
    # the composition over M_3, with the variable indices as data.  A code is a string over A E N C z t e 0 1: a prefix of d
    # quantifiers (d = 1, 2), then a matrix in Polish notation whose atoms are `z i` (x_i = 0), `t i` (x_i + x_i = 1) and `e i j`
    # (x_i = x_j), the indices written as the tokens 0, 1.  Truth is computed twice, by two separate routines.
    ARITY = {"z": 1, "t": 1, "e": 2}
    def d_matrix(code, i, env, d):
        """Direct: parse the matrix from position i and evaluate it; (value, next position), or None if ill-formed."""
        if i >= len(code): return None
        c = code[i]
        if c in ARITY:
            ix = code[i + 1:i + 1 + ARITY[c]]
            if len(ix) < ARITY[c] or any(ch not in "01" or int(ch) >= d for ch in ix): return None
            x = [env[int(ch)] for ch in ix]
            return ((x[0] == 0) if c == "z" else ((2 * x[0]) % 3 == 1) if c == "t" else (x[0] == x[1]), i + 1 + ARITY[c])
        if c == "N":
            r = d_matrix(code, i + 1, env, d); return None if r is None else (not r[0], r[1])
        if c == "C":
            r1 = d_matrix(code, i + 1, env, d)
            if r1 is None: return None
            r2 = d_matrix(code, r1[1], env, d); return None if r2 is None else (r1[0] and r2[0], r2[1])
        return None
    def d_truth(code):
        d = 0
        while d < len(code) and code[d] in "AE": d += 1
        if d not in (1, 2): return None
        wf = d_matrix(code, d, (0, 0), d)
        if wf is None or wf[1] != len(code): return None
        return decide(3, code[:d], lambda v: d_matrix(code, d, tuple(v) + (0,) * (2 - d), d)[0])
    def clause(code, d, q, ends):
        """The position-local clause on the parse label of matrix position d + q (ends[q]: the end of the subformula opening there).
        It refers to labels at positions to its right only."""
        n = len(code); i = d + q; c = code[i]; e = ends[q]
        if q == 0 and e != n: return False                               # the root: the matrix ends where the code ends
        if c in "zt": return i + 1 < n and code[i + 1] in "01" and e == i + 2
        if c == "e": return i + 2 < n and code[i + 1] in "01" and code[i + 2] in "01" and e == i + 3
        if c == "N": return i + 1 < n and code[i + 1] in "NCzte" and e == ends[q + 1]
        if c == "C":
            if not (i + 1 < n and code[i + 1] in "NCzte"): return False
            j = ends[q + 1]
            return j < n and code[j] in "NCzte" and e == ends[j - d]
        if c in "01":                                                    # an index token: owned by the atom before it, its own labels inert
            own = (i - 1 >= d and code[i - 1] in "zte") or (i - 2 >= d and code[i - 2] == "e" and code[i - 1] in "01")
            return own and e == i + 1
        return False                                                     # a quantifier token inside the matrix
    def structural(code, d, ends):
        """The clauses on the ends (the parse labels), at every matrix position."""
        return ends[0] == len(code) and all(clause(code, d, q, ends) for q in range(len(code) - d))
    def valued(code, d, ends, vals, x):
        """The clauses on the values, under the quantified values x: an atom's clause resolves its coded index against x by a case over
        the d candidates (the linkage clause)."""
        for q in range(len(code) - d):
            i = d + q; c = code[i]; v = vals[q]
            if c == "z":
                if not any(code[i + 1] == str(j) and v == (x[j] == 0) for j in range(d)): return False
            elif c == "t":
                if not any(code[i + 1] == str(j) and v == ((x[j] + x[j]) % 3 == 1) for j in range(d)): return False
            elif c == "e":
                if not any(code[i + 1] == str(j1) and code[i + 2] == str(j2) and v == (x[j1] == x[j2]) for j1 in range(d) for j2 in range(d)): return False
            elif c == "N":
                if v != (not vals[q + 1]): return False
            elif c == "C":
                if v != (vals[q + 1] and vals[ends[q + 1] - d]): return False
            elif v: return False                                         # an index token carries the inert value
        return True
    def parses(code, d, search):
        """The labellings of the ends that satisfy the structural clauses: by search over all of them, or the one candidate of the
        right-to-left pass, checked against the clauses."""
        n = len(code); k = n - d
        if search: return [e for e in itertools.product(range(d + 1, n + 1), repeat=k) if structural(code, d, e)]
        ends = [0] * k
        for q in range(k - 1, -1, -1):
            i = d + q; c = code[i]
            if c in "zt": ends[q] = i + 2
            elif c == "e": ends[q] = i + 3
            elif c in "01": ends[q] = i + 1
            elif c == "N": ends[q] = ends[q + 1] if q + 1 < k else 0
            elif c == "C":
                j = ends[q + 1] if q + 1 < k else 0
                ends[q] = ends[j - d] if d <= j < n else 0
        return [tuple(ends)] if all(d < e <= n for e in ends) and structural(code, d, tuple(ends)) else []
    def parses_bt(code, d):
        """EVERY labelling of the ends that satisfies the structural clauses, by backtracking from the right: the clause at a position
        refers only to labels on its right, so a partial labelling is extended by every value that meets the clause there."""
        n = len(code); k = n - d; out = []
        def rec(q, ends):
            if q < 0: out.append(tuple(ends[x] for x in range(k))); return
            for e in range(d + 1, n + 1):
                ends[q] = e
                if clause(code, d, q, ends): rec(q - 1, ends)
            ends.pop(q, None)
        if k > 0: rec(k - 1, {})
        return out
    def values(code, d, ends, x, search):
        """The labellings of the values consistent with the clauses under x."""
        k = len(code) - d
        if search: return [v for v in itertools.product((False, True), repeat=k) if valued(code, d, ends, v, x)]
        vals = [False] * k
        for q in range(k - 1, -1, -1):
            i = d + q; c = code[i]
            if c == "z": vals[q] = x[int(code[i + 1])] == 0 if int(code[i + 1]) < d else False
            elif c == "t": vals[q] = (2 * x[int(code[i + 1])]) % 3 == 1 if int(code[i + 1]) < d else False
            elif c == "e": vals[q] = x[int(code[i + 1])] == x[int(code[i + 2])] if max(int(code[i + 1]), int(code[i + 2])) < d else False
            elif c == "N": vals[q] = not vals[q + 1]
            elif c == "C": vals[q] = vals[q + 1] and vals[ends[q + 1] - d]
        return [tuple(vals)] if valued(code, d, ends, tuple(vals), x) else []
    def l_truth(code, mode):
        """Truth by guessed labels: a prefix length d, checked against the token classes; the parse labels; and, under the uniform
        pairing prefix whose copy clauses are read off the coded prefix, value labels rooted true.  mode "all": every labelling of
        ends and values is tried (the ends over the full product); "search": the same, the ends by backtracking; "pass": the one
        candidate of the right-to-left pass, checked against the clauses."""
        n = len(code)
        for d in (1, 2):
            if not (d < n and all(code[k] in "AE" for k in range(d)) and code[d] not in "AE"): continue
            ps = parses(code, d, True) if mode == "all" else parses_bt(code, d) if mode == "search" else parses(code, d, False)
            rooted = {}                                                  # the matrix of the paired sentence at x: some labelling is rooted true
            def matrix(x):                                               # (it reads x alone, so each x is labelled once)
                if x not in rooted: rooted[x] = any(v[0] for e in ps for v in values(code, d, e, x + (0,) * (2 - d), mode != "pass"))
                return rooted[x]
            if paired(3, code[:d], matrix): return True
        return False
    n_comp = n_comp_wf = n_true = n_pairs = 0
    for L in range(1, 6):                                                # every string of length <= 5: the labellings over the full product
        for tup in itertools.product("AENCzte01", repeat=L):
            code = "".join(tup); n_comp += 1
            want = d_truth(code); got = l_truth(code, "all")
            ok &= got == (want is True) == l_truth(code, "pass")          # the labelled truth holds exactly for the well-formed true codes
            n_comp_wf += want is not None; n_true += want is True
            for d in (1, 2):                                             # and the backtracking search finds exactly the labellings of the full product
                if d < L: n_pairs += 1; ok &= sorted(parses_bt(code, d)) == sorted(parses(code, d, True))
    ok &= (n_comp, n_comp_wf, n_true, n_pairs) == (66429, 64, 36, 132759)
    n6 = n6_wf = n6_true = 0
    for tup in itertools.product("AENCzte01", repeat=6):                 # every string of length 6, the labellings by the complete search:
        code = "".join(tup); n6 += 1                                     # the shortest codes with a conjunction are among them
        want = d_truth(code); ok &= l_truth(code, "search") == (want is True)
        n6_wf += want is not None; n6_true += want is True
    ok &= n6 == 531441 and 0 < n6_true < n6_wf
    ok &= d_truth("ECCz0z0t0") is False and not l_truth("ECCz0z0t0", "search")     # a false conjunction is not labelled true,
    ok &= d_truth("ECz0z0z0") is None and not l_truth("ECz0z0z0", "search")        # nor a conjunction followed by a stray atom
    def matrices(size, d, memo={}):
        """Every well-formed matrix of exactly `size` tokens over d variables."""
        if (size, d) not in memo:
            out = [c + str(i) for c in "zt" for i in range(d)] if size == 2 else [("e" + str(i) + str(j)) for i in range(d) for j in range(d)] if size == 3 else []
            if size > 2: out += ["N" + m for m in matrices(size - 1, d)]
            for a in range(2, size - 2): out += ["C" + m1 + m2 for m1 in matrices(a, d) for m2 in matrices(size - 1 - a, d)]
            memo[(size, d)] = out
        return memo[(size, d)]
    n_big = n_big_true = n_edit = n_edit_wf = 0
    for d in (1, 2):                                                     # every well-formed code with a matrix of at most 7 tokens,
        for pref in itertools.product("AE", repeat=d):                   # by the complete search and by the pass
            for size in range(2, 8):
                for mat in matrices(size, d):
                    code = "".join(pref) + mat; n_big += 1
                    want = d_truth(code); ok &= want is not None and l_truth(code, "search") == want == l_truth(code, "pass"); n_big_true += want
                    eds = [code[:pos] + tok + code[pos + 1:] for pos in range(len(code)) for tok in "AENCzte01" if tok != code[pos]]
                    eds += [code + tail for tail in ("z0", "t0", "0", "N")]     # every one-token edit, and four extensions: an ill-formed code is rejected
                    for ed in eds:
                        n_edit += 1; w2 = d_truth(ed); ok &= l_truth(ed, "search") == (w2 is True); n_edit_wf += w2 is not None
    ok &= (n_big, n_big_true) == (1540, 654) and n_edit == 108048 and 0 < n_edit_wf < n_edit
    # 25:G5 (p25032)
    check("E2", "fragment truth by guessed labels, on small languages: on the propositional layer a consistent labelling exists exactly for the well-formed codes, is unique, and is rooted true exactly for the true ones (all 340 codes of length <= 4 over every labelling; all 87380 codes of length <= 8 by the right-to-left pass); with the variable indices coded as data, the labelled truth — parse labels, value labels, linkage clauses by cases, the pairing prefix — holds exactly for the well-formed true codes, against a separate direct evaluator over M_3: on all 66429 strings of length <= 5 over nine tokens (every labelling), on all 531441 strings of length 6 (every labelling, the ends by a complete backtracking search), on the 1540 well-formed codes with a matrix of at most 7 tokens, and on 108048 one-token edits and extensions of them", ok,
          f"{n_codes} codes ({n_wf} well-formed) over every labelling; {n_long} by the pass; composition: {n_comp} strings ({n_comp_wf} well-formed, {n_true} true), {n6} strings of length 6 ({n6_wf} well-formed, {n6_true} true), {n_big} well-formed codes ({n_big_true} true), {n_edit} edits and extensions ({n_edit_wf} well-formed)")

# ------------------------------------------------------------------------------------------------------------
# block F: second-order decidability and the trichotomy's middle cell (25:H2, H5) — Section 6.
# F1: over a finite domain a second-order quantifier over k-ary relations ranges over the 2^(m^k) subsets of M^k, so
# second-order sentences are decided by enumeration: the counts for five (m, k), and four sentences decided on |X| = 3.
# F2: the theory "at least n elements, for every n" with a free unary predicate P — each finite part of it has models
# with P empty and with P non-empty, so it decides neither Ex P(x) nor its negation, and Ax not P(x) completes it; the
# theory of a finite model decides every sentence of the sample.
def block_F():
    """Block F — second-order decidability and the trichotomy's middle cell (EXACT): F1–F2."""
    ok = True; det = []
    for m, k in ((2, 1), (2, 2), (3, 1), (3, 2), (2, 3)):
        pts = list(itertools.product(range(m), repeat=k))
        rels = sum(1 for _ in itertools.product((0, 1), repeat=len(pts)))        # every k-ary relation, enumerated
        ok &= rels == 2 ** (m ** k); det.append(f"(m,k)=({m},{k}): {rels}")
    X = range(3); pairs = [(i, j) for i in X for j in X]
    found = {"order": False, "inj_not_onto": False, "all_have_min": True, "equiv_classes": set()}
    n = n_fun = n_injf = n_onto = n_bij = 0
    for bits in itertools.product((0, 1), repeat=9):
        R = {pq for pq, b in zip(pairs, bits) if b}; n += 1
        functional = all(sum((i, j) in R for j in X) == 1 for i in X)
        if functional:
            n_fun += 1
            injective = not any((i, j) in R and (i2, j) in R for j in X for i in X for i2 in X if i != i2)   # no value is taken twice
            onto = all(any((i, j) in R for i in X) for j in X)                                              # every element is a value
            n_injf += injective; n_onto += onto; n_bij += injective and onto
            if injective and not onto: found["inj_not_onto"] = True       # an injective function that is not onto: the scan finds none
        irr = all((i, i) not in R for i in X)
        tra = all((i, k2) in R for (i, j) in R for (j2, k2) in R if j == j2)
        tot = all((i, j) in R or (j, i) in R for i in X for j in X if i != j)
        if irr and tra and tot:
            found["order"] = True
            for sub in itertools.product((0, 1), repeat=3):                          # second-order over subsets: every non-empty subset has a least element
                S = [x for x in X if sub[x]]
                if S: found["all_have_min"] &= any(all(x == y or (x, y) in R for y in S) for x in S)
        refl = all((i, i) in R for i in X); sym = all((j, i) in R for (i, j) in R)
        if refl and sym and tra: found["equiv_classes"].add(frozenset(frozenset(j for j in X if (i, j) in R) for i in X))
    ok &= n == 512 and found["order"] and not found["inj_not_onto"] and found["all_have_min"] and len(found["equiv_classes"]) == 5
    ok &= (n_fun, n_injf, n_onto, n_bij) == (27, 6, 6, 6)                # 27 graphs of functions among the relations: 6 injective, 6 onto, the same 6
    # 25:H2 (p25036)
    check("F1", "second-order decidability on a finite domain: a quantifier over k-ary relations ranges over 2^(m^k) relations (enumerated for five (m, k)); on 3 elements, over all 512 binary relations: a strict total order exists, every one well-orders the non-empty subsets, among the 27 functions the 6 injective ones are the 6 onto ones, and the equivalence relations are the 5 partitions", ok,
          "; ".join(det))

    ok = True; det = []
    at_least = lambda s, n: decide(s, "E" * n, lambda v: len(set(v)) == n)   # the axiom "there are at least n elements", decided over a domain of s elements
    n_struct = 0
    for N in range(1, 5):                                               # the first N axioms, over every structure (domain of s <= 5 elements, a unary predicate P)
        seen = {}
        for s in range(1, 6):
            sat = all(at_least(s, n) for n in range(1, N + 1))
            ok &= sat == (s >= N)                                       # the models of the first N axioms: the structures of at least N elements
            for P in itertools.product((0, 1), repeat=s):
                n_struct += 1
                if sat: seen.setdefault(s, set()).add(decide(s, "E", lambda v: P[v[0]] == 1))   # the value of Ex P(x) in the model
        ok &= all(vals == {False, True} for vals in seen.values())      # in every model size both values occur: the N axioms decide neither Ex P(x) nor its negation
        ok &= not all(at_least(N, n) for n in range(1, N + 2))          # no structure of N elements satisfies the next axiom
        for s in seen:                                                  # the completing axiom Ax not P(x) leaves one value
            ok &= {decide(s, "E", lambda v: P[v[0]] == 1) for P in itertools.product((0, 1), repeat=s) if decide(s, "A", lambda v: P[v[0]] == 0)} == {False}
    det.append(f"N <= 4: {n_struct} structures decided; both values of Ex P(x) among the models of the first N axioms; none of N elements satisfies N+1 axioms")
    ok &= n_struct == 4 * (2 + 4 + 8 + 16 + 32) == 248
    for p in (2, 3, 5):                                                 # cell (iii): the theory of a finite model decides every sentence of the sample
        ok &= all(decide(p, pat, mat) == want for _, pat, mat, want in sentences(p))
    # 25:H5 (p25039)
    check("F2", "the trichotomy's middle cell on its finite parts: the first N axioms 'at least n elements' (n <= N <= 4), decided over all 248 structures of at most 5 elements with a unary predicate P, have models with Ex P(x) true and with it false, so they decide neither it nor its negation, and Ax not P(x) settles it; no structure of N elements satisfies N+1 of the axioms; the theory of a finite model (M_2, M_3, M_5) gives every sentence of a sample of 8 its value", ok,
          "; ".join(det))

if __name__ == "__main__":
    import time
    want = [a.upper() for a in sys.argv[1:]] or sorted(BLOCK)
    bad = [b for b in want if b not in BLOCK]
    if bad: sys.exit(f"no block {', '.join(bad)}: the blocks are {', '.join(sorted(BLOCK))}")
    t0 = time.time()
    for b in want:
        t = time.time(); _run_block(b); print(f"    [block {b}: {time.time() - t:.1f} s]")
    ok = summary(write=(want == sorted(BLOCK)), expect=[i for i in LEDGER if i[0] in want])
    kinds = {}
    for r in RESULTS: kinds[r["kind"]] = kinds.get(r["kind"], 0) + 1
    print("by kind: " + ", ".join(f"{k} {v}" for k, v in sorted(kinds.items())) + f"; {len(RESULTS)} checks in {time.time() - t0:.1f} s" + ("; results.json written" if want == sorted(BLOCK) else ""))
    sys.exit(0 if ok else 1)
