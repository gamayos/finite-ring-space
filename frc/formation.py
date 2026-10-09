"""frc.formation — formation universes, traces and bounded certificates (the logic theme; 29-finitism, 9 October 2026).

The python side of `lean/FrcCore/Theme/Formation.lean` and `Theme/SecondOrder.lean`: a universe of formations is a finite
set of objects 0, …, size − 1 with a formation image of each (None where the act fails); a trace is what a completed check
reads, t mentioned objects and the formation atoms it asserts among them; a check passes in a universe under a reading of
its objects. The constructions of 29-finitism: the minimal realization (Theorem idleness), padding (Corollary symmetry),
the disjoint double and its swap (Lemma boundary), the buffer frame (Proposition illusion), induction from the least
element (Lemma innocence), the record count of a bounded agent (Definition agent), and the full second-order theory of a
finite structure decided by exhaustive evaluation (Corollary determinacy). Exact, the standard library only (gate G09).

    A universe is (size, form), form a list of length size with entries in range(size) or None.
    A trace is (t, atom), atom a t × t table of booleans: atom[i][j] reads "the formation image of i is j".

    passes(T, U, e)              the check of trace T passes in U under the reading e (a list of t objects): Lean `Passes`
    minimal(T)                   the minimal realization, exactly the trace's objects: Lean `minimal`
    pad(U, k)                    k fresh objects appended, formation failing at each: Lean `pad`
    double(U), swap(U, x)        the disjoint double and the swap of its copies: Lean `double`, `swap`
    count_invariant(U, D)        the number of satisfiers of a condition D (a list over the double) : Lean `count`
    buffer(sigma, D), chain(sigma, D, s, k)   the buffer frame and the chain from seed s: Lean `buffer`, `chain`
    least_below(P, n), finite_induction_holds(P)   the least element and the induction schema on [0, n)
    records(s, K)                Σ_{i≤K} s^i, the strings of length at most K: Lean `records`
    record(T)                    the atom table as a list of t² booleans: Lean `record`
    random_universe(rng, n), random_passed_trace(rng, U)   test data
    sval2(M, env, senv, renv, phi)   second-order exhaustive evaluation over a finite structure: Lean `sval2`
    sval2_table(M, phi)          the same sentence decided a second way, by tables of satisfying assignments
"""
from itertools import product

from frc.logic import fval


# ---- universes and traces ------------------------------------------------------------------------------------------------

def closed(U):
    """Every formation image is an object of the universe (Lean `Universe.Closed`)."""
    size, form = U
    return len(form) == size and all(f is None or 0 <= f < size for f in form)


def passes(T, U, e):
    """The three clauses of Lean `Passes`: e reads the t objects into U, injectively, and every asserted atom holds."""
    t, atom = T
    size, form = U
    return (all(0 <= e[i] < size for i in range(t)) and len(set(e[:t])) == t
            and all(form[e[i]] == e[j] for i in range(t) for j in range(t) if atom[i][j]))


def minimal(T):
    """The minimal realization: the trace's objects, each formed to the least object the trace asserts for it."""
    t, atom = T
    return t, [next((j for j in range(t) if atom[i][j]), None) for i in range(t)]


def pad(U, k):
    """U with k fresh objects, formation failing at each."""
    size, form = U
    return size + k, list(form) + [None] * k


def double(U):
    """The disjoint double U ⊔ U: objects x < size the first copy, size + x the second, each formed inside its copy."""
    size, form = U
    return 2 * size, list(form) + [None if f is None else size + f for f in form]


def swap(U, x):
    """The swap of the two copies of the double."""
    size = U[0]
    return size + x if x < size else x - size


def is_automorphism(U, sigma):
    """sigma (a list over the objects of U) commutes with formation and is a bijection."""
    size, form = U
    if sorted(sigma) != list(range(size)): return False
    return all((form[sigma[x]] is None and form[x] is None) or
               (form[x] is not None and form[sigma[x]] == sigma[form[x]]) for x in range(size))


def count_invariant(U, D):
    """The number of satisfiers of the condition D (a list of booleans over the objects of U)."""
    return sum(1 for x in range(U[0]) if D[x])


def swap_invariant(U, D):
    """D is invariant under the swap of the double U."""
    return all(D[swap((U[0] // 2, None), x)] == D[x] for x in range(U[0]))


# ---- the buffer frame ------------------------------------------------------------------------------------------------------

def buffer(sigma, D):
    """sigma seeds, each the root of a chain of D formations; object s (D + 1) + k is seed s at level k ≤ D."""
    M = sigma * (D + 1)
    return M, [x + 1 if x % (D + 1) < D else None for x in range(M)]


def chain(sigma, D, s, k):
    """k acts of formation from seed s in the buffer frame: the object reached, or None past the top."""
    _, form = buffer(sigma, D)
    x = s * (D + 1)
    for _ in range(k):
        if x is None: return None
        x = form[x]
    return x


def reachable(U, seeds, r):
    """The objects reachable from the seeds by at most r formation acts."""
    _, form = U
    reach = set(seeds)
    for _ in range(r):
        reach |= {form[x] for x in reach if form[x] is not None}
    return reach


# ---- the least element and induction ---------------------------------------------------------------------------------------

def least_below(P, n):
    """The least x < n with P[x], or None (Lean `leastBelow`)."""
    return next((x for x in range(n) if P[x]), None)


def finite_induction_holds(P):
    """The induction schema on [0, n) for the property P (a list of n booleans): P[0] and closure under successor below n
    give P everywhere; checked by the least counterexample (Lean `finite_induction`)."""
    n = len(P)
    hyp = n == 0 or (P[0] and all((not P[x]) or P[x + 1] for x in range(n - 1)))
    if not hyp: return True                                   # the schema asserts nothing
    bad = least_below([not p for p in P], n)
    return bad is None


# ---- records -------------------------------------------------------------------------------------------------------------------

def records(s, K):
    """The strings of length at most K over s letters: Σ_{i≤K} s^i (Lean `records`)."""
    return sum(s ** i for i in range(K + 1))


def record(T):
    """The atom table of a trace, row by row: a record of t² symbols (Lean `record`)."""
    t, atom = T
    return [bool(atom[i][j]) for i in range(t) for j in range(t)]


# ---- test data -----------------------------------------------------------------------------------------------------------------

def random_universe(rng, n):
    """n objects with a random formation image each, or none."""
    return n, [rng.choice([None] + list(range(n))) for _ in range(n)]


def random_passed_trace(rng, U):
    """A trace and a reading under which it passes in U: t distinct objects and some of the formations among them."""
    size, form = U
    t = rng.randrange(1, size + 1)
    e = rng.sample(range(size), t)
    atom = [[(form[e[i]] == e[j]) and rng.randrange(2) == 0 for j in range(t)] for i in range(t)]
    return (t, atom), e


# ---- the full second-order theory of a finite structure -----------------------------------------------------------------------

def mem_bit(n, x):
    """Bit x of the code n: whether element x belongs to the subset coded by n (Lean `memBit`)."""
    return n // 2 ** x % 2 == 1


def tuple_index(m, xs):
    """The code of a tuple in base m: x0 + m x1 + m² x2 + … (Lean `tupleIndex`)."""
    idx = 0
    for x in reversed(xs): idx = x + m * idx
    return idx


def sval2(M, env, senv, renv, phi):
    """Exhaustive second-order evaluation (Lean `sval2`): env, senv, renv are tuples (variable 0 first) of element values,
    subset codes and relation codes. Formulas: ("rel", r, (i, …)), ("eq", i, j), ("setmem", k, i), ("relapp", k, (i, …)),
    ("neg", φ), ("conj", φ, ψ), ("all", φ), ("allset", φ), ("allrel", a, φ)."""
    m, rel = M
    t = phi[0]
    if t == "rel": return rel(phi[1], tuple(env[i] for i in phi[2]))
    if t == "eq": return env[phi[1]] == env[phi[2]]
    if t == "setmem": return mem_bit(senv[phi[1]], env[phi[2]])
    if t == "relapp": return mem_bit(renv[phi[1]], tuple_index(m, [env[i] for i in phi[2]]))
    if t == "neg": return not sval2(M, env, senv, renv, phi[1])
    if t == "conj": return sval2(M, env, senv, renv, phi[1]) and sval2(M, env, senv, renv, phi[2])
    if t == "all": return all(sval2(M, (x,) + tuple(env), senv, renv, phi[1]) for x in range(m))
    if t == "allset": return all(sval2(M, env, (S,) + tuple(senv), renv, phi[1]) for S in range(2 ** m))
    if t == "allrel": return all(sval2(M, env, senv, (R,) + tuple(renv), phi[2]) for R in range(2 ** (m ** phi[1])))
    raise ValueError(t)


def so_arities(phi):
    """The (element, set, relation) variable counts a formula reads: one more than the largest free index of each sort."""
    t = phi[0]
    if t == "rel": return (max(phi[2]) + 1 if phi[2] else 0, 0, 0)
    if t == "eq": return (max(phi[1], phi[2]) + 1, 0, 0)
    if t == "setmem": return (phi[2] + 1, phi[1] + 1, 0)
    if t == "relapp": return (max(phi[2]) + 1 if phi[2] else 0, 0, phi[1] + 1)
    if t == "neg": return so_arities(phi[1])
    if t == "conj":
        a, b = so_arities(phi[1]), so_arities(phi[2]); return tuple(max(x, y) for x, y in zip(a, b))
    if t == "all":
        e, s, r = so_arities(phi[1]); return (max(e - 1, 0), s, r)
    if t == "allset":
        e, s, r = so_arities(phi[1]); return (e, max(s - 1, 0), r)
    if t == "allrel":
        e, s, r = so_arities(phi[2]); return (e, s, max(r - 1, 0))
    raise ValueError(t)


def sval2_table(M, phi, ke, ks, kr, amax):
    """A second way: the set of assignments (elements^ke, subsets^ks, relations^kr) satisfying phi, built bottom-up by tables
    (complement for ¬, intersection for ∧, and for a quantifier the assignments all of whose extensions lie in the body's
    table). Relation variables range over the codes of relations of arity at most amax, since a relation quantifier's
    arity is fixed by the formula; amax bounds the codes tried."""
    m, rel = M
    E = range(m); S = range(2 ** m); R = range(2 ** (m ** amax))
    full = set(product(product(E, repeat=ke), product(S, repeat=ks), product(R, repeat=kr)))
    t = phi[0]
    if t in ("rel", "eq", "setmem", "relapp"):
        return {a for a in full if sval2(M, a[0], a[1], a[2], phi)}
    if t == "neg": return full - sval2_table(M, phi[1], ke, ks, kr, amax)
    if t == "conj": return sval2_table(M, phi[1], ke, ks, kr, amax) & sval2_table(M, phi[2], ke, ks, kr, amax)
    if t == "all":
        body = sval2_table(M, phi[1], ke + 1, ks, kr, amax)
        return {a for a in full if all(((x,) + a[0], a[1], a[2]) in body for x in E)}
    if t == "allset":
        body = sval2_table(M, phi[1], ke, ks + 1, kr, amax)
        return {a for a in full if all((a[0], (s,) + a[1], a[2]) in body for s in S)}
    if t == "allrel":
        body = sval2_table(M, phi[2], ke, ks, kr + 1, amax)
        return {a for a in full if all((a[0], a[1], (r,) + a[2]) in body for r in range(2 ** (m ** phi[1])))}
    raise ValueError(t)


def random_sformula(rng, d, ke, ks, kr):
    """A random second-order formula of depth at most d over ke element, ks set and kr relation variables (arity 1 or 2)."""
    if d == 0 or rng.randrange(4) == 0:
        c = rng.randrange(4)
        if c == 0 and ke: return ("eq", rng.randrange(ke), rng.randrange(ke))
        if c == 1 and ke and ks: return ("setmem", rng.randrange(ks), rng.randrange(ke))
        if c == 2 and ke and kr: return ("relapp", rng.randrange(kr), (rng.randrange(ke),) if rng.randrange(2) else (rng.randrange(ke), rng.randrange(ke)))
        if ke: return ("rel", rng.choice([0, 1]), (rng.randrange(ke),) if rng.randrange(2) else (rng.randrange(ke), rng.randrange(ke)))
        return ("all", ("eq", 0, 0))
    c = rng.randrange(5)
    if c == 0: return ("neg", random_sformula(rng, d - 1, ke, ks, kr))
    if c == 1: return ("conj", random_sformula(rng, d - 1, ke, ks, kr), random_sformula(rng, d - 1, ke, ks, kr))
    if c == 2: return ("all", random_sformula(rng, d - 1, ke + 1, ks, kr))
    if c == 3: return ("allset", random_sformula(rng, d - 1, ke, ks + 1, kr))
    return ("allrel", rng.choice([1, 2]), random_sformula(rng, d - 1, ke, ks, kr + 1))


# ---- the bounded (Δ₀) language and its frames (5-reductio B6, the python counterpart of Lean `stable`) ----------------------

def d0_term(env, t):
    """Terms over ℕ: ("var", i), ("zero",), ("one",), ("add", s, t), ("mul", s, t) (Lean `evalT`)."""
    k = t[0]
    if k == "var": return env[t[1]]
    if k == "zero": return 0
    if k == "one": return 1
    if k == "add": return d0_term(env, t[1]) + d0_term(env, t[2])
    if k == "mul": return d0_term(env, t[1]) * d0_term(env, t[2])
    raise ValueError(k)


def d0_term_frame(N, env, t):
    """The same term in the frame W_N: defined only while every intermediate value stays below N (Lean `evalT?`)."""
    k = t[0]
    if k == "var": return env[t[1]] if env[t[1]] < N else None
    if k == "zero": return 0 if 0 < N else None
    if k == "one": return 1 if 1 < N else None
    a, b = d0_term_frame(N, env, t[1]), d0_term_frame(N, env, t[2])
    if a is None or b is None: return None
    v = a + b if k == "add" else a * b
    return v if v < N else None


def d0_eval(env, phi):
    """Δ₀ formulas over ℕ: ("eq", s, t), ("lt", s, t), ("neg", φ), ("conj", φ, ψ), ("ball", t, φ) — ∀ x ≤ t, φ, x variable 0
    (Lean `evalF`)."""
    k = phi[0]
    if k == "eq": return d0_term(env, phi[1]) == d0_term(env, phi[2])
    if k == "lt": return d0_term(env, phi[1]) < d0_term(env, phi[2])
    if k == "neg": return not d0_eval(env, phi[1])
    if k == "conj": return d0_eval(env, phi[1]) and d0_eval(env, phi[2])
    if k == "ball": return all(d0_eval((x,) + tuple(env), phi[2]) for x in range(d0_term(env, phi[1]) + 1))
    raise ValueError(k)


def d0_eval_frame(N, env, phi):
    """The same formula in W_N: an atom with an undefined term is false, a bounded quantifier is guarded (Lean `evalF?`)."""
    k = phi[0]
    if k in ("eq", "lt"):
        a, b = d0_term_frame(N, env, phi[1]), d0_term_frame(N, env, phi[2])
        if a is None or b is None: return False
        return a == b if k == "eq" else a < b
    if k == "neg": return not d0_eval_frame(N, env, phi[1])
    if k == "conj": return d0_eval_frame(N, env, phi[1]) and d0_eval_frame(N, env, phi[2])
    if k == "ball":
        b = d0_term_frame(N, env, phi[1])
        if b is None: return False
        return all(d0_eval_frame(N, (x,) + tuple(env), phi[2]) for x in range(b + 1))
    raise ValueError(k)


def d0_bound(env, phi):
    """t(φ): the largest integer the standard evaluation of φ touches (Lean `boundF`)."""
    def bt(env, t):
        k = t[0]
        if k == "var": return env[t[1]]
        if k in ("zero", "one"): return d0_term(env, t)
        return max(bt(env, t[1]), bt(env, t[2]), d0_term(env, t))
    k = phi[0]
    if k in ("eq", "lt"): return max(bt(env, phi[1]), bt(env, phi[2]))
    if k == "neg": return d0_bound(env, phi[1])
    if k == "conj": return max(d0_bound(env, phi[1]), d0_bound(env, phi[2]))
    if k == "ball":
        b = d0_term(env, phi[1])
        return max([bt(env, phi[1])] + [d0_bound((x,) + tuple(env), phi[2]) for x in range(b + 1)])
    raise ValueError(k)


def random_d0(rng, d, k):
    """A random Δ₀ formula of depth at most d over k free variables, with small terms."""
    def term(d, k):
        if d == 0 or rng.randrange(3) == 0:
            c = rng.randrange(3)
            if c == 0 and k: return ("var", rng.randrange(k))
            return ("one",) if c == 1 else ("zero",)
        return (rng.choice(["add", "mul"]), term(d - 1, k), term(d - 1, k))
    if d == 0 or rng.randrange(4) == 0:
        return (rng.choice(["eq", "lt"]), term(2, k), term(2, k))
    c = rng.randrange(3)
    if c == 0: return ("neg", random_d0(rng, d - 1, k))
    if c == 1: return ("conj", random_d0(rng, d - 1, k), random_d0(rng, d - 1, k))
    return ("ball", term(1, k), random_d0(rng, d - 1, k + 1))
