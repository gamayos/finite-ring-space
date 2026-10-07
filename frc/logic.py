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
