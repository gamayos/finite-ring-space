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
