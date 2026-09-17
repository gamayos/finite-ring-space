"""
c_choice.py — block C: choice recovered on finite and periodic structures (5:E1–E6)
===================================================================================
Section 5 of the paper.  C1: global choice on a finite universe — ch(A) = min A is a member of every nonempty
subset of F₁₃ (all 8191), and finite products are nonempty by induction.  C2: periodic choice — an equality-periodic
family receives a choice function of the same period.  C3: equivariant choice — over random finite G-families
(G = ℤ/2, ℤ/3, S₃ as permutation groups on the index set, stabilisers acting on the fibres) an equivariant section
exists exactly when every stabiliser action has a fixed point, decided by exhaustive search on both sides.
C4: the definable basis — the greedy minimal basis of every subspace of F₅³ (all 64) is independent and spanning;
the obstruction: ℤ/2 acting by v ↦ −v on the line over F_p fixes no basis for odd p ≤ 13 and fixes one over F₂.
C5: periodic König — in every finite digraph with out-degree ≥ 1 the greedy walk repeats a vertex within |D| + 1
steps and is eventually periodic with period ≤ |D| (exhaustive for |D| ≤ 3, random up to 30).  C6: periodic
de Bruijn–Erdős in dimension one — for random periodic graphs with bounded range, the transfer digraph decides
c-colorability of all finite subgraphs, and when they are colorable a definable σ^m-periodic coloring is produced
and verified; the count of periodic graphs where finite colorability fails is reported.
"""
import itertools, random
import redcommon as rc

def perm_group(name):
    if name == "Z2": return [(0, 1), (1, 0)]
    if name == "Z3": return [(0, 1, 2), (1, 2, 0), (2, 0, 1)]
    return list(itertools.permutations(range(3)))                      # S_3

def compose(p, q): return tuple(p[q[i]] for i in range(len(p)))

def run():
    # C1 global choice by the least element
    U = list(range(13)); ok = True
    for mask in range(1, 1 << 13):
        A = [x for x in U if mask >> x & 1]
        ok &= min(A) in A and all(min(A) <= a for a in A)
    ok &= all(len(list(itertools.product(*[range(1, k + 1) for k in ks]))) > 0 for ks in [(1,), (2, 3), (2, 2, 2), (3, 1, 4, 2)])
    rc.check("C1", "ch(A) = min A is a member and the least element of every nonempty subset of F_13 (8191 subsets); finite products of nonempty sets are nonempty", ok, "")

    # C2 periodic choice
    rng = random.Random(11); ok = True
    for _ in range(50):
        N = rng.randrange(1, 8); period = [rng.sample(U, rng.randrange(1, 6)) for _ in range(N)]
        A = lambda i: period[i % N]                                       # A_{i+N} = A_i
        f = lambda i: min(A(i))
        ok &= all(A(i + N) == A(i) and f(i + N) == f(i) and f(i) in A(i) for i in range(-20, 20))
    rc.check("C2", "an equality-periodic family A_{i+N} = A_i on F_13 has the choice f(i) = min A_i of the same period (50 random families, periods 1..7)", ok, "")

    # C3 equivariant choice iff stabiliser fixed points
    ok = True; n_cases = 0; n_exist = 0
    for gname in ("Z2", "Z3", "S3"):
        G = perm_group(gname); nI = len(G[0])
        for _ in range(60):
            # the index set I = orbit of G on {0..nI-1} (one orbit, transitive by construction? use the natural action)
            # a G-family: fibers A_i of size m with an action of G on the total space compatible with the projection.
            # Build it as an induced family: A = I x F with g.(i, a) = (g.i, rho_i(g).a) for a cocycle rho; take
            # the simplest compatible actions: g.(i, a) = (g.i, sigma_g(a)) for a homomorphism sigma: G -> Sym(F).
            m = rng.randrange(1, 4); F = list(range(m))
            perms = list(itertools.permutations(F))
            # random homomorphism G -> Sym(F): choose images of generators and check compatibility by brute force
            hom = None
            for _ in range(20):
                cand = {g: rng.choice(perms) for g in G}
                if all(cand[compose(g, h)] == compose(cand[g], cand[h]) for g in G for h in G):
                    hom = cand; break
            if hom is None: continue
            n_cases += 1
            I = list(range(nI)); A = [(i, a) for i in I for a in F]
            act = lambda g, x: (g[x[0]], hom[g][x[1]])
            # equivariant section by brute force: s : I -> F with s(g.i) = g.s(i)
            exists = any(all(act(g, (i, s[i]))[1] == s[g[i]] for g in G for i in I) for s in itertools.product(F, repeat=nI))
            # the criterion: for each orbit representative i, the stabiliser G_i has a fixed point in the fibre
            orbits = {}
            for i in I: orbits.setdefault(frozenset(g[i] for g in G), i)
            crit = all(any(all(hom[g][a] == a for g in G if g[i] == i) for a in F) for i in orbits.values())
            ok &= exists == crit
            n_exist += exists
    rc.check("C3", "a G-equivariant section exists iff every stabiliser action on its fibre has a fixed point: exhaustive on both sides for random G-families, G = Z/2, Z/3, S_3, fibres of size 1..3", ok,
             f"{n_cases} families, {n_exist} with a section; the criterion agrees in every case")

    # C4 the definable basis and the equivariant obstruction
    p = 5; ok = True
    vecs = list(itertools.product(range(p), repeat=3))
    def span(B):
        S = {(0, 0, 0)}
        for b in B:
            S = {tuple((s[k] + c * b[k]) % p for k in range(3)) for s in S for c in range(p)}
        return S
    subspaces = set()
    for k in range(4):
        for B in itertools.combinations(vecs[1:], k):
            S = frozenset(span(B))
            if len(S) == p ** k: subspaces.add(S)
    ok &= len(subspaces) == 1 + 31 + 31 + 1
    for V in subspaces:
        B = []; rest = sorted(V - {(0, 0, 0)})
        while rest:
            b = min(rest); B.append(b); Sp = span(B); rest = sorted(V - Sp)
        ok &= span(B) == V and len(B) == {1: 0, 5: 1, 25: 2, 125: 3}[len(V)]
    obstruction = {q: all((-v) % q != v for v in range(1, q)) for q in (3, 5, 7, 11, 13)}
    ok &= all(obstruction.values()) and (-1) % 2 == 1
    rc.check("C4", "every subspace of F_5^3 (64 of them) has the greedy minimal basis, independent and spanning; the involution v -> -v on the line fixes no basis over F_p for odd p <= 13 and fixes 1 over F_2", ok,
             "obstruction over F_3, F_5, F_7, F_11, F_13; none over F_2")

    # C5 periodic Koenig
    ok = True; n_graphs = 0
    for n in (1, 2, 3):
        for out in itertools.product(*[list(itertools.chain.from_iterable(itertools.combinations(range(n), r) for r in range(1, n + 1))) for _ in range(n)]):
            n_graphs += 1
            for r in range(n):
                walk = [r]
                while len(walk) <= n:
                    walk.append(min(out[walk[-1]]))
                seen = {}; period = None
                for k, v in enumerate(walk):
                    if v in seen: period = k - seen[v]; break
                    seen[v] = k
                ok &= period is not None and 1 <= period <= n
    for n in (10, 20, 30):
        for _ in range(30):
            out = [sorted(rng.sample(range(n), rng.randrange(1, 4))) for _ in range(n)]
            walk = [0]
            while len(walk) <= n: walk.append(out[walk[-1]][0])
            first = next(k for k in range(len(walk)) if walk[k] in walk[k + 1:])
            k2 = walk.index(walk[first], first + 1); period = k2 - first
            ok &= period <= n and all(walk[first + j] == walk[first + j + period] for j in range(len(walk) - first - period))
    rc.check("C5", "periodic Koenig: in every finite digraph with out-degree >= 1 the greedy walk repeats within |D|+1 steps and is eventually periodic with period <= |D| (exhaustive |D| <= 3, random |D| = 10, 20, 30)", ok,
             f"{n_graphs} digraphs exhaustive")

    # C6 periodic de Bruijn-Erdos in dimension one
    ok = True; n_col = 0; n_uncol = 0
    for _ in range(40):
        b = rng.randrange(1, 4); c = rng.choice((2, 3))
        intra = [(u, v) for u in range(b) for v in range(u + 1, b) if rng.random() < 0.6]     # edges inside a block
        inter = [(u, v) for u in range(b) for v in range(b) if rng.random() < 0.4]            # block k -> block k+1
        cols = [col for col in itertools.product(range(c), repeat=b) if all(col[u] != col[v] for u, v in intra)]
        edges = {(x, y) for x in cols for y in cols if all(x[u] != y[v] for u, v in inter)}    # the transfer digraph D_c
        # finite subgraphs colorable for all n  <=>  walks of every length  <=>  D'_c (vertices beginning walks of every length) nonempty
        alive = set(cols)
        while True:
            nxt = {x for x in alive if any((x, y) in edges for y in alive)}
            if nxt == alive: break
            alive = nxt
        if not alive:
            n_uncol += 1
            # some finite subgraph is not c-colorable: the longest walk is bounded — verify by search up to |cols| + 1 blocks
            ok &= not any(True for _ in [0] if len(cols) and longest_walk(cols, edges) > len(cols))
            continue
        n_col += 1
        # a definable periodic coloring: greedy walk in D'_c from the least vertex
        walk = [min(alive)]
        while len(walk) <= len(alive):
            walk.append(min(y for y in alive if (walk[-1], y) in edges))
        first = next(k for k in range(len(walk)) if walk[k] in walk[k + 1:]); k2 = walk.index(walk[first], first + 1)
        cycle = walk[first:k2]; m = len(cycle)
        ok &= 1 <= m <= len(alive)
        # verify the periodic coloring on 6 periods
        seq = (cycle * 6)
        ok &= all((seq[k], seq[k + 1]) in edges for k in range(len(seq) - 1))
    rc.check("C6", "periodic de Bruijn-Erdos (dimension one): the transfer digraph decides c-colorability of all finite subgraphs of a random periodic graph; when they are colorable, a definable sigma^m-periodic coloring with m <= |D'_c| is produced and verified", ok,
             f"40 random periodic graphs (block <= 3, range 1, c = 2, 3): {n_col} colorable with a periodic coloring found, {n_uncol} with a finite obstruction")

def longest_walk(cols, edges):
    best = 0
    for x in cols:
        frontier = {x}; L = 0
        while frontier and L <= len(cols):
            frontier = {y for f in frontier for y in cols if (f, y) in edges}; L += 1 if frontier else 0
        best = max(best, L)
    return best

if __name__ == "__main__":
    run(); rc.summary(write=False)
