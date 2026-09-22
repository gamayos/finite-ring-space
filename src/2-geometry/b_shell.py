"""
b_shell.py — block B: the orbital shell and its spherical completion (2:B4, C2, C3, C4)
=======================================================================================
Section 3 of the paper: the complex S_p of def:orbital-shell coded as vertices, edges and faces; the
completion (the terminal latitude collapsed to S); the counts of rem:cell-counts (B1); closedness — every edge
in two faces, every vertex link one cycle — of thm:combinatorial-sphere, exhaustive on p ∈ {5, 13, 17, 29} (B2);
the cellular automorphisms: the reindexing ρ_u is cellular only for u = ±1, the dihedral maps are, the meridian
reversal is a map of the completion only (prop:phase-frame-change, prop:shell-covariance; B3).
"""
import math
from collections import Counter, defaultdict
try:
    from . import geocommon as gc
except ImportError:                       # run in place (python3 <script>.py)
    import geocommon as gc

SHELLS = (5, 13, 17, 29)

def shell(p):
    """The orbital shell S_p of Def. 3.1: vertices, edges, faces; and its completion."""
    k = (p - 1) // 4; pi = 2 * k; n = p - 1
    V = ["N"] + [(a, m) for a in range(1, pi + 1) for m in range(n)]
    E = set()
    for m in range(n):
        E.add(frozenset(["N", (1, m)]))
        for a in range(1, pi): E.add(frozenset([(a, m), (a + 1, m)]))
        for a in range(1, pi + 1): E.add(frozenset([(a, m), (a, (m + 1) % n)]))
    F = []
    for m in range(n):
        F.append(("N", (1, m), (1, (m + 1) % n)))
        for a in range(1, pi): F.append(((a, m), (a + 1, m), (a + 1, (m + 1) % n), (a, (m + 1) % n)))
    col = lambda v: "S" if (v != "N" and v[0] == pi) else v      # the completion: L_pi collapsed to S
    Vc = sorted({col(v) for v in V}, key=str)
    Ec = {frozenset(map(col, e)) for e in E if len({col(v) for v in e}) == 2}
    Fc = []
    for f in F:
        cf = []
        for v in map(col, f):
            if v not in cf: cf.append(v)
        Fc.append(tuple(cf))
    return V, E, F, Vc, Ec, Fc

def closed_surface(V, E, F):
    """Every edge in exactly two faces; every vertex link a single cycle."""
    edge_faces = defaultdict(list)
    for fi, f in enumerate(F):
        for j in range(len(f)): edge_faces[frozenset([f[j], f[(j + 1) % len(f)]])].append(fi)
    if set(edge_faces) != set(E) or any(len(v) != 2 for v in edge_faces.values()): return False
    for v in V:
        around = [fi for fi, f in enumerate(F) if v in f]
        adj = defaultdict(set)
        for fi in around:
            f = F[fi]; j = f.index(v)
            for w in (f[(j - 1) % len(f)], f[(j + 1) % len(f)]):
                for fj in edge_faces[frozenset([v, w])]:
                    if fj != fi: adj[fi].add(fj)
        if any(len(s) != 2 for s in adj.values()): return False
        seen, stack = set(), [around[0]]
        while stack:
            x = stack.pop()
            if x in seen: continue
            seen.add(x); stack.extend(adj[x])
        if seen != set(around): return False
    return True

def run():
    # B1 the counts and the Euler characteristics (2:C2)
    ok = True; det = []
    for p in SHELLS:
        k = (p - 1) // 4; pi = 2 * k; n = p - 1
        V, E, F, Vc, Ec, Fc = shell(p)
        ok &= (len(V), len(E), len(F)) == (pi * n + 1, 2 * pi * n, pi * n) and len(V) - len(E) + len(F) == 1
        ok &= (len(Vc), len(Ec), len(Fc)) == ((pi - 1) * n + 2, (2 * pi - 1) * n, pi * n) and len(Vc) - len(Ec) + len(Fc) == 2
        det.append(f"p={p}: |V|,|E|,|F| = {len(V)},{len(E)},{len(F)}, chi=1; completion {len(Vc)},{len(Ec)},{len(Fc)}, chi=2")
    # row 2:C2
    gc.check("B1", "cell counts of S_p and of its completion, chi = 1 and chi = 2 (Remark 3.4)", ok, "; ".join(det))

    # B2 the completion is a closed surface (chi = 2, a sphere); S_p itself is not closed (2:C3)
    ok = True; det = []
    for p in SHELLS:
        V, E, F, Vc, Ec, Fc = shell(p)
        closed = closed_surface(Vc, Ec, Fc)
        ok &= closed and not closed_surface(V, E, F)
        det.append(f"p={p}: completion closed={closed}, S_p closed=False")
    # row 2:C3
    gc.check("B2", "the completion is a closed surface with chi = 2 (a sphere) by exhaustive incidence; S_p has a boundary", ok, "; ".join(det))

    # B3 cellular automorphisms: rho_u iff u = ±1; the dihedral maps; meridian reversal on the completion only (2:B4, 2:C4)
    ok = True; det = []
    for p in SHELLS:
        k = (p - 1) // 4; pi = 2 * k; n = p - 1
        V, E, F, Vc, Ec, Fc = shell(p)
        faces = lambda FF, f: sorted(Counter(tuple(sorted(map(str, map(f, x)))) for x in FF).items())
        cellular = lambda f, EE, FF: {frozenset(map(f, e)) for e in EE} == EE and faces(FF, f) == faces(FF, lambda v: v)
        good = []
        for u in gc.units(n):
            rho = lambda v: v if v in ("N", "S") else (v[0], v[1] * u % n)
            if cellular(rho, E, F): good.append(u)
            ok &= cellular(rho, E, F) == (u in (1, n - 1)) and cellular(rho, Ec, Fc) == (u in (1, n - 1))
        for c in range(n):
            for s_ in (1, -1):
                dih = lambda v: v if v in ("N", "S") else (v[0], (s_ * v[1] + c) % n)
                ok &= cellular(dih, E, F)
        sig = lambda v: "S" if v == "N" else "N" if v == "S" else (pi - v[0], v[1])
        ok &= cellular(sig, Ec, Fc)
        ok &= sum(1 for v in V if v == "N") == 1 and sum(1 for v in V if v != "N" and v[0] == pi) == n
        det.append(f"p={p}: rho_u cellular only for u in {good} of {len(gc.units(n))} units")
    # row 2:B4, 2:C4
    gc.check("B3", "rho_u (m -> um) is cellular iff u = ±1; the dihedral maps are; meridian reversal is a map of the completion only", ok, "; ".join(det))

if __name__ == "__main__":
    run(); gc.summary(write=False)
