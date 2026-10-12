"""frc.projective — PGL₂ by elements: the boosts, the Borel subgroup and the Hopf section (the projective theme; ledger
migration, task LM25, 5 October 2026).

The python side of `lean/FrcCore/Theme/Projective.lean`: 2 × 2 matrices over F_p as tuples (a, b, c, d), read up to a
nonzero scalar, acting on the projective line [x : y] ↦ [a x + b y : c x + d y]. Exact integers mod p only, the standard
library only (gate G09). The first ledger to use it is the master's block file frc/ledgers/master/projective.py.

    mul(M, N, p), det(M, p), act(M, P, p)     the product, the determinant, the action on a point P = (x, y)
    normal(P, p)                              a point of ℙ¹ in normal form: (x, 1) or (1, 0)
    pclass(M, p)                              a matrix's projective class: M scaled to its first nonzero entry 1
    line(p)                                   the p + 1 points of ℙ¹
    boost(nu, a, b, p), borel(a, b, e, p)     [[α, νβ], [β, α]] and [[a, b], [0, e]]
    pgl2(p)                                   every class of PGL₂(F_p), by search (p(p² − 1) of them)
    factor(M, nu, p)                          (N, (a, b, e), (α, β)) with N M = borel · boost (the Lean proof's formula)

The two fibrations and the frame triple of 38-s13 (12 October 2026; `Projective.lean`'s `frame_triple`, `unit_split`):

    adj(M, p), conj(M, N, p)                  the adjugate [[d, −b], [−c, a]]; the conjugate M N M⁻¹
    triple(M, nu, p)                          (direction, (α, β), (a, b, e)) with N M = boost(α, β) · borel(a, b, e), N = α² − νβ²
    frame_triple(p, nu)                       every class of PGL₂ is one direction × one Borel class, (p + 1)·p·(p − 1) exactly
    sl2(p)                                    the norm-one sphere SL₂(F_p) by elements, p(p² − 1) of them
    involutions(p)                            the involutions of SL₂ (one) and of PGL₂ (p²): the two groups are not isomorphic
    circle(p)                                 the points of x² + y² = 1: p − 1 of them at p = 4κ + 1
    unit(p)                                   i = diag(r, −r) with r² = −1, the unit's matrix on a frame p = 4κ + 1
    centraliser(p)                            the classes commuting with i: the diagonal torus, p − 1 classes, inside the Borel
    split_fibration(p)                        the orbit of i under conjugation = the quadric a² + bc = −1, p(p + 1) points, fibres the cosets
    nonsplit_fibration(p, nu)                 the orbit of u (u² = ν) = the quadric a² + bc = ν, p(p − 1) points; the Borel a section
    sphere(p, c)                              the points of x² + y² + z² = c: p(p + 1) for c a nonzero square (38:A9, B6)
"""


def mul(M, N, p):
    a, b, c, d = M; e, f, g, h = N
    return ((a * e + b * g) % p, (a * f + b * h) % p, (c * e + d * g) % p, (c * f + d * h) % p)


def det(M, p):
    a, b, c, d = M
    return (a * d - b * c) % p


def act(M, P, p):
    a, b, c, d = M; x, y = P
    return ((a * x + b * y) % p, (c * x + d * y) % p)


def normal(P, p):
    x, y = P[0] % p, P[1] % p
    if y: return (x * pow(y, -1, p) % p, 1)
    if x: return (1, 0)
    raise ValueError("the zero vector is no point")


def pclass(M, p):
    lead = next(v for v in M if v % p)
    s = pow(lead, -1, p)
    return tuple(v * s % p for v in M)


def line(p):
    return [(x, 1) for x in range(p)] + [(1, 0)]


def boost(nu, a, b, p):
    return (a % p, nu * b % p, b % p, a % p)


def borel(a, b, e, p):
    return (a % p, b % p, 0, e % p)


def pgl2(p):
    """Every class of PGL₂(F_p): the invertible matrices scaled to a leading 1, by search."""
    out = []
    for a in range(p):
        for b in range(p):
            for c in range(p):
                for d in range(p):
                    M = (a, b, c, d)
                    if det(M, p) and pclass(M, p) == M: out.append(M)
    return out


def factor(M, nu, p):
    """N M = borel(det M, b d − ν a c, N) · boost(d, c), N = d² − ν c² (Projective.lean, `hopf_section` (3))."""
    a, b, c, d = M
    N = (d * d - nu * c * c) % p
    return N, (det(M, p), (b * d - nu * a * c) % p, N), (d % p, c % p)


# ---- the frame triple and the two fibrations (38:A9, X4, B6) --------------------------------------------------------
def adj(M, p):
    a, b, c, d = M
    return (d % p, (-b) % p, (-c) % p, a % p)


def conj(M, N, p):
    """The conjugate M N M⁻¹ as a matrix (scalars cancel: well defined on the class of M), M⁻¹ = adj M / det M."""
    di = pow(det(M, p), -1, p)
    return tuple(x * di % p for x in mul(mul(M, N, p), adj(M, p), p))


def triple(M, nu, p):
    """The T·B factorisation of an invertible M (Projective.lean, `frame_triple` (1)): the direction M·[1 : 0] = [a : c],
    the boost (α, β) = (a, c) carrying the horizon to it with norm N = a² − νc², and the chart (N, ab − νcd, det M), with
    N M = boost(α, β) · borel(N, ab − νcd, det M)."""
    a, b, c, d = M
    N = (a * a - nu * c * c) % p
    direction = normal((a, c), p)
    chart = (N, (a * b - nu * c * d) % p, det(M, p))
    assert tuple(N * x % p for x in M) == mul(boost(nu, a, c, p), borel(*chart, p), p)
    return direction, (a % p, c % p), chart


def frame_triple(p, nu):
    """Every class of PGL₂(F_p) is one point of ℙ¹ (its direction) and one Borel class (the chart), uniquely: the map
    class ↦ (direction, Borel class) is a bijection onto ℙ¹ × (the p(p − 1) Borel classes); returns
    (the number of classes, p + 1, p(p − 1), bijective)."""
    G = pgl2(p)
    seen = set()
    for M in G:
        direction, _, chart = triple(M, nu, p)
        seen.add((direction, pclass(borel(*chart, p), p)))
    return len(G), p + 1, p * (p - 1), len(seen) == len(G) == (p + 1) * p * (p - 1)


def sl2(p):
    """The norm-one sphere SL₂(F_p) by elements: the matrices of determinant 1, p(p² − 1) of them."""
    return [(a, b, c, d) for a in range(p) for b in range(p) for c in range(p) for d in range(p) if (a * d - b * c) % p == 1]


def involutions(p):
    """(the involutions of SL₂, of PGL₂): one (−I) against p²; the two groups of order p(p² − 1) are not isomorphic
    (38:A7)."""
    I = (1, 0, 0, 1)
    s = sum(1 for M in sl2(p) if M != I and mul(M, M, p) == I)
    g = sum(1 for M in pgl2(p) if M != I and pclass(mul(M, M, p), p) == I)
    return s, g


def circle(p):
    """The points (x, y) of x² + y² = 1 over F_p: p − 1 of them when p ≡ 1 (mod 4), p + 1 when p ≡ 3 (38:B6)."""
    return [(x, y) for x in range(p) for y in range(p) if (x * x + y * y) % p == 1]


def unit(p):
    """The unit i = diag(r, −r) with r² = −1 on p = 4κ + 1 (r the least such residue)."""
    r = next(x for x in range(1, p) if x * x % p == p - 1)
    return (r, 0, 0, (-r) % p)


def centraliser(p):
    """The classes of PGL₂ whose matrices commute with the unit i (M i = i M as matrices, independent of the scalar):
    the diagonal torus, p − 1 classes, every one inside the Borel; returns (the classes, p − 1, all diagonal)."""
    i = unit(p)
    cen = [M for M in pgl2(p) if mul(M, i, p) == mul(i, M, p)]
    return cen, p - 1, all(M[1] == 0 and M[2] == 0 for M in cen)


def split_fibration(p):
    """The split fibration of PGL₂ by the unit i (38:A9): the conjugates M i M⁻¹ are exactly the points of the
    trace-zero quadric a² + bc = −1 (p(p + 1) points, none scalar), every fibre is a coset of the centraliser
    (p − 1 classes), and the Borel meets a fibre in the whole fibre or not at all (no section). Returns the dict."""
    i = unit(p)
    G = pgl2(p)
    fib = {}
    for M in G:
        N = conj(M, i, p)
        fib.setdefault(N, []).append(M)
    quadric = {(a, b, c, (-a) % p) for a in range(p) for b in range(p) for c in range(p) if (a * a + b * c) % p == p - 1}
    cen, _, _ = centraliser(p)
    B = {pclass(borel(a, b, e, p), p) for a in range(1, p) for b in range(p) for e in range(1, p)}
    return {"base": len(fib), "quadric": len(quadric), "orbit_is_quadric": set(fib) == quadric,
            "count": p * (p + 1), "fibre": p - 1, "fibres_are_cosets": all(len(v) == len(cen) for v in fib.values()),
            "borel_whole_or_none": all(len(set(v) & B) in (0, len(cen)) for v in fib.values())}


def nonsplit_fibration(p, nu):
    """The non-split fibration by u = [[0, ν], [1, 0]] (u² = ν a nonsquare; 00:C19, 38:A9): the conjugates fill the
    quadric a² + bc = ν (p(p − 1) points), the fibres are the cosets of the boost torus (p + 1 classes), and the Borel
    meets every fibre exactly once (the section)."""
    u = (0, nu % p, 1, 0)
    G = pgl2(p)
    fib = {}
    for M in G:
        N = conj(M, u, p)
        fib.setdefault(N, []).append(M)
    quadric = {(a, b, c, (-a) % p) for a in range(p) for b in range(p) for c in range(p) if (a * a + b * c) % p == nu % p}
    B = {pclass(borel(a, b, e, p), p) for a in range(1, p) for b in range(p) for e in range(1, p)}
    return {"base": len(fib), "quadric": len(quadric), "orbit_is_quadric": set(fib) == quadric, "count": p * (p - 1),
            "fibre": p + 1, "fibres": all(len(v) == p + 1 for v in fib.values()),
            "section": all(len(set(v) & B) == 1 for v in fib.values())}


def sphere(p, c):
    """The number of (x, y, z) with x² + y² + z² = c over F_p: p(p + 1) for c a nonzero square on p = 4κ + 1 (the unit
    sphere; Grav.sphere_area_rung), p(p − 1) for a nonsquare (38:A9)."""
    return sum(1 for x in range(p) for y in range(p) for z in range(p) if (x * x + y * y + z * z) % p == c % p)
