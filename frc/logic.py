"""frc.logic — the first-order theory of a finite structure (the logic theme; ledger migration, task LM26, 6 October 2026).

The python side of the first-order part of `lean/FrcCore/Theme/Logic.lean`: a finite relational structure on the elements
0, …, m − 1, formulas with de Bruijn variables (the atoms R_r(x_i, …) and x_i = x_j, negation, conjunction and ∀ over
the elements), their exhaustive evaluation, and a second evaluator by satisfying tables. Exact, the standard library only
(gate G09). The first ledger to use it is the master's block file frc/ledgers/master/logic.py.

    A formula is a tuple: ("rel", r, (i, …)), ("eq", i, j), ("neg", φ), ("conj", φ, ψ), ("all", φ).
    A structure is (m, rel), rel(r, args) -> bool.

    fval(M, env, phi)            exhaustive evaluation, env a tuple (variable 0 first): the Lean definition fval
    table(M, phi, k)             the satisfying assignments of the variables 0..k−1, built bottom-up (a second method)
    free_vars(phi)               the number of de Bruijn variables phi reads (one more than the largest free index)
    random_formula(rng, d, k)    a random formula of depth ≤ d over k free variables and relations of arity ≤ 2
    random_structure(rng, m)     a random structure on m elements with two binary relations and one unary relation
    successor_counterexample(n)  an injective map of [0, n) into itself that misses an element, by search: None for every n
"""
from itertools import product


def fval(M, env, phi):
    """Exhaustive evaluation (the Lean definition `fval`): env[i] is variable i."""
    m, rel = M
    t = phi[0]
    if t == "rel": return rel(phi[1], tuple(env[i] for i in phi[2]))
    if t == "eq": return env[phi[1]] == env[phi[2]]
    if t == "neg": return not fval(M, env, phi[1])
    if t == "conj": return fval(M, env, phi[1]) and fval(M, env, phi[2])
    if t == "all": return all(fval(M, (x,) + tuple(env), phi[1]) for x in range(m))
    raise ValueError(t)


def free_vars(phi):
    """One more than the largest free de Bruijn index of phi (0 for a sentence)."""
    t = phi[0]
    if t == "rel": return max(phi[2]) + 1 if phi[2] else 0
    if t == "eq": return max(phi[1], phi[2]) + 1
    if t == "neg": return free_vars(phi[1])
    if t == "conj": return max(free_vars(phi[1]), free_vars(phi[2]))
    if t == "all": return max(free_vars(phi[1]) - 1, 0)
    raise ValueError(t)


def table(M, phi, k):
    """The set of assignments (x_0, …, x_{k−1}) ∈ [0, m)^k satisfying phi, k ≥ free_vars(phi), computed bottom-up by
    tables: complement for ¬, intersection for ∧, and for ∀ the assignments all of whose extensions lie in the body's table."""
    m, rel = M
    t = phi[0]
    full = set(product(range(m), repeat=k))
    if t == "rel": return {a for a in full if rel(phi[1], tuple(a[i] for i in phi[2]))}
    if t == "eq": return {a for a in full if a[phi[1]] == a[phi[2]]}
    if t == "neg": return full - table(M, phi[1], k)
    if t == "conj": return table(M, phi[1], k) & table(M, phi[2], k)
    if t == "all":
        body = table(M, phi[1], k + 1)
        return {a for a in full if all((x,) + a in body for x in range(m))}
    raise ValueError(t)


def random_formula(rng, d, k):
    """A random formula of depth at most d whose free variables are among 0..k−1 (k ≥ 1)."""
    if d == 0 or rng.randrange(5) == 0:
        c = rng.randrange(3)
        if c == 0: return ("eq", rng.randrange(k), rng.randrange(k))
        if c == 1: return ("rel", 0, (rng.randrange(k), rng.randrange(k)))
        return ("rel", rng.choice([1, 2]), (rng.randrange(k),) if rng.randrange(2) == 0 else (rng.randrange(k), rng.randrange(k)))
    c = rng.randrange(3)
    if c == 0: return ("neg", random_formula(rng, d - 1, k))
    if c == 1: return ("conj", random_formula(rng, d - 1, k), random_formula(rng, d - 1, k))
    return ("all", random_formula(rng, d - 1, k + 1))


def random_structure(rng, m):
    """m elements; relation 0 binary, 1 unary, 2 binary (a function's graph: y = f(x)); arities beyond read as false."""
    R0 = {(x, y) for x in range(m) for y in range(m) if rng.randrange(2) == 0}
    R1 = {x for x in range(m) if rng.randrange(2) == 0}
    f = [rng.randrange(m) for _ in range(m)]

    def rel(r, args):
        if r == 0: return len(args) == 2 and args in R0
        if r == 1: return len(args) == 1 and args[0] in R1
        if r == 2: return len(args) == 2 and f[args[0]] == args[1]
        return False
    return m, rel


def successor_counterexample(n):
    """An injective S: [0, n) → [0, n) with an element outside its range, by search over all n^n maps; None if there is none."""
    for S in product(range(n), repeat=n):
        if len(set(S)) == n and set(S) != set(range(n)): return S
    return None


# ======================================================================================================================
# 25-godel's primitives (moved from the package src/25-godel/godel.py at the migration of 20 October 2026): the running
# example M_p, the prenex evaluator with its matrix count, every formula over M_2 up to a length with its truth table and
# free variables, the independent reader of the written formula, the closed terms over {1, +} as trees, and the
# certificate format of the wrap lemma with its verifier. The ledger file frc/ledgers/p25_godel.py calls them.
# ======================================================================================================================
from frc.arith import is_prime

def next_prime_1mod4(n):
    """The least prime p >= n with p = 1 (mod 4)."""
    n += (1 - n) % 4
    while not is_prime(n): n += 4
    return n

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

    return out


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


# ======================================================================================================================
# 5-reductio's arithmetic frame and Δ₀ constructors (moved from the package src/5-reductio/reductio.py at the migration of
# 21 October 2026). The Δ₀ language is the core's (Theme/Logic.lean: Term, Form) in the encoding frc/formation.py evaluates
# (d0_term, d0_eval, d0_term_frame, d0_eval_frame, d0_bound); here its constructors, the worked instance of 5:B6 (Goldbach
# below M) and a random sentence, and the frame W_N as a relational structure for the first-order sample of 5:B5.
# ======================================================================================================================
class Frame:
    """W_N: domain [0, N), constant 0, order <, and the graphs S, A, M of successor, sum and product restricted to
    the domain (Definition frame).  An atomic relation with an argument outside the domain is false."""
    def __init__(self, N):
        self.N = N; self.dom = range(N)
    def S(self, x, y): return 0 <= x < self.N and y == x + 1 and y < self.N
    def A(self, x, y, z): return all(0 <= v < self.N for v in (x, y, z)) and z == x + y
    def M(self, x, y, z): return all(0 <= v < self.N for v in (x, y, z)) and z == x * y
    def lt(self, x, y): return 0 <= x < self.N and 0 <= y < self.N and x < y


def num(n):
    t = ('zero',)
    for _ in range(n): t = ('add', t, ('one',))
    return t

def bex(t, phi): return ('neg', ('ball', t, ('neg', phi)))
def disj(a, b): return ('neg', ('conj', ('neg', a), ('neg', b)))
def impl(a, b): return ('neg', ('conj', a, ('neg', b)))

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
        r = rng.randrange(20)
        if d == 0 or r < 8:
            return ('var', rng.randrange(nvars)) if nvars and rng.randrange(5) < 3 else num(rng.randrange(maxnum))
        return (rng.choice(['add', 'mul']), term(d - 1), term(d - 1))
    def form(d, nv):
        r = rng.randrange(20)
        if d == 0 or r < 6:
            return (rng.choice(['eq', 'lt']), term(1), term(1)) if nv else (rng.choice(['eq', 'lt']), num(rng.randrange(maxnum)), num(rng.randrange(maxnum)))
        if r < 9: return ('neg', form(d - 1, nv))
        if r < 12: return ('conj', form(d - 1, nv), form(d - 1, nv))
        return ('ball', num(rng.randrange(1, maxnum)) if not nv else (('var', rng.randrange(nv)) if rng.randrange(2) == 0 else num(rng.randrange(1, maxnum))), form(d - 1, nv + 1))
    nvars = 0
    return form(depth, nvars)
