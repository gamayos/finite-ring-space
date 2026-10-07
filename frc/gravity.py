"""frc.gravity — the horizon's count (the gravity theme; ledger migration, task LM27, 6 October 2026).

The python side of `lean/FrcCore/Theme/Gravity.lean`: on a shell p = 4κ + 1 the points of the plane conic x² + y² = c
and of the sphere x² + y² + z² = a in 𝔽_p³, the record S = κ(p + 1), the area A = p(p + 1), the rate-face mass
M = (p + 1)/2, the registration rate T = A/p³ and the response T_resp = 1/p, and the merger law on the count face
A = M(M + 1). Exact integers and fractions only, the standard library only (gate G09). The first ledger to use it is the
master's block file frc/ledgers/master/gravity.py.

    squares(p)              the number of square roots of each residue: r[v] = #{x : x² = v}
    conic_points(p, c)      #{(x, y) : x² + y² = c}, by the square counts
    sphere_points(p, a)     #{(x, y, z) : x² + y² + z² = a}, by the square counts
    sphere_brute(p, a)      the same by enumerating 𝔽_p³ (a second method, p small)
    record(p), area(p)      S = κ(p + 1) and A = p(p + 1)
    rate_mass(p)            M = (p + 1)/2
    temperature(p)          T = A/p³, a Fraction
    response(p)             T_resp = (dS/dM)⁻¹ = 1/p, a Fraction
    merger_area(m1, m2)     A(m1 + m2) − A(m1) − A(m2) on the count face A = M(M + 1)
"""
from fractions import Fraction


def squares(p):
    """r[v] = the number of x in 𝔽_p with x² = v."""
    r = [0] * p
    for x in range(p): r[x * x % p] += 1
    return r


def conic_points(p, c):
    """The points of x² + y² = c in 𝔽_p²."""
    r = squares(p)
    return sum(r[(c - x * x) % p] for x in range(p))


def sphere_points(p, a):
    """The points of x² + y² + z² = a in 𝔽_p³: Σ_z (points of the conic at a − z²)."""
    r = squares(p)
    conic = [sum(r[(c - x * x) % p] for x in range(p)) for c in range(p)]
    return sum(conic[(a - z * z) % p] for z in range(p))


def sphere_brute(p, a):
    """The same count by enumerating 𝔽_p³."""
    return sum(1 for x in range(p) for y in range(p) for z in range(p) if (x * x + y * y + z * z - a) % p == 0)


def record(p):
    return (p - 1) // 4 * (p + 1)


def area(p):
    return p * (p + 1)


def rate_mass(p):
    return (p + 1) // 2


def temperature(p):
    return Fraction(area(p), p ** 3)


def response(p):
    return Fraction(1, p)


def merger_area(m1, m2):
    A = lambda m: m * (m + 1)
    return A(m1 + m2) - A(m1) - A(m2)
