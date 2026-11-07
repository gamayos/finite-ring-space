"""frc.geometry — 2-geometry's exact content above the frame (the geometry theme, 6 November 2026).

The python side of `lean/FrcCore/Theme/Orbital.lean` and `lean/FrcCore/Theme/Cells.lean`: the orbital shell S_p of
2-geometry and its spherical completion as a finite cell complex, the closed-surface test (every edge in two faces,
every vertex link one cycle), which reindexings of the phase cycle are cellular, and the scale grids of a fixed frame
with their covering radius in [0, 1]. Exact integers and fractions only, the standard library only (gate G09).

    shell(p)                        (V, E, F, Vc, Ec, Fc): the shell of Def. 3.1 and its completion (L_π collapsed to S)
    closed_surface(V, E, F)         every edge in exactly two faces and every vertex link a single cycle
    cellular(f, E, F)               the vertex map f carries edges to edges and faces to faces
    rho_cellular(p, u)              m ↦ u·m is cellular on the shell (and on the completion)
    scale_grid(p, g, depth, H)      {x/g^n : 0 ≤ x ≤ H, n ≤ depth} ∩ [0, 1] as fractions
    covering_radius(points)         the covering radius of a finite set of fractions in [0, 1]
    fixed_shell_cut(p, g)           (m, the bound ½·min(g^−m, 1 − 2κ·g^−(m+1))) with g^m ≤ 2κ + 1 < g^(m+1)
"""
from collections import defaultdict
from fractions import Fraction
from math import gcd


def kappa(p):
    if p % 4 != 1: raise ValueError(f"kappa: {p} is not 4κ + 1")
    return (p - 1) // 4


def units(n):
    """The units of Z_n."""
    return [u for u in range(1, n) if gcd(u, n) == 1]


def shell(p):
    """The orbital shell S_p of Def. 3.1 (vertices N and (a, m), 1 ≤ a ≤ π, m < n) and its completion."""
    k = kappa(p); pi = 2 * k; n = p - 1
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
    col = lambda v: "S" if (v != "N" and v[0] == pi) else v
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
    """Every edge lies in exactly two faces, and every vertex link is a single cycle."""
    edge_faces = defaultdict(list)
    for fi, f in enumerate(F):
        for j in range(len(f)): edge_faces[frozenset([f[j], f[(j + 1) % len(f)]])].append(fi)
    if set(edge_faces) != set(E) or any(len(v) != 2 for v in edge_faces.values()): return False
    at = defaultdict(list)
    for fi, f in enumerate(F):
        for w in f: at[w].append(fi)
    for v in V:
        around = at[v]
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


def _face_multiset(F, f):
    out = defaultdict(int)
    for x in F: out[tuple(sorted(map(str, map(f, x))))] += 1
    return dict(out)


def cellular(f, E, F):
    """The vertex map f carries the edges onto the edges and the faces onto the faces."""
    return {frozenset(map(f, e)) for e in E} == set(E) and _face_multiset(F, f) == _face_multiset(F, lambda v: v)


def rho_cellular(p, u):
    """(on the shell, on the completion): whether m ↦ u·m is a cellular automorphism."""
    n = p - 1
    V, E, F, Vc, Ec, Fc = shell(p)
    rho = lambda v: v if v in ("N", "S") else (v[0], v[1] * u % n)
    return cellular(rho, E, F), cellular(rho, Ec, Fc)


def scale_grid(p, g, depth, H=None):
    """The scale grids {x/g^n : 0 ≤ x ≤ H, n ≤ depth} of the frame (p, g) inside [0, 1]; H = 2κ by default."""
    H = 2 * kappa(p) if H is None else H
    return sorted({Fraction(x, g ** n) for n in range(depth + 1) for x in range(H + 1) if x <= g ** n})


def covering_radius(points):
    """The covering radius in [0, 1] of a finite sorted set of fractions in [0, 1]."""
    gaps = [points[0] - 0, Fraction(1) - points[-1]] + [Fraction(b - a, 2) for a, b in zip(points, points[1:])]
    return max(gaps)


def fixed_shell_cut(p, g, H=None):
    """(m, ½·min(g^−m, 1 − H·g^−(m+1))) with g^m ≤ H + 1 < g^(m+1): the bound of 2:E3 (H = 2κ by default)."""
    H = 2 * kappa(p) if H is None else H
    m = 0
    while g ** (m + 1) <= H + 1: m += 1
    return m, min(Fraction(1, g ** m), 1 - Fraction(H, g ** (m + 1))) / 2
