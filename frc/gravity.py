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
    merger_area_loss(m1, m2, dm)   A(m1 + m2 − dm) − A(m1) − A(m2) = 2m1m2 − (2m1 + 2m2 + 1)dm + dm², a coalescence radiating dm
    merger_loss_bound(m1, m2)      the largest dm ≤ m1 + m2 with merger_area_loss ≥ 0: ⌊(b − √(b² − 8m1m2))/2⌋, b = 2m1 + 2m2 + 1
    registered_ticks(P, h)         the framed readout of a clock: ⌊P h⌋ ticks per far window of h ticks
    operational_cut_count(Om, M)   the operational cut on a Carrier Om as a count (21-gravity, D5 of 21 November 2026): the
                                   outermost cut r whose composed rate ∏_{s=r}^{h−1} (1 − M/(s(s+1))) from the horizon
                                   h = ⌊√Om⌋ registers no tick, P < 1/h; returns (r_f, P(r_f), P(r_f + 1)), exact Fractions
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


def merger_area_loss(m1, m2, dm):
    """The count-face area change of a coalescence that radiates the cardinality dm: A(m1 + m2 − dm) − A(m1) − A(m2)."""
    A = lambda m: m * (m + 1)
    return A(m1 + m2 - dm) - A(m1) - A(m2)


def merger_loss_bound(m1, m2):
    """The largest radiated cardinality dm ≤ m1 + m2 that keeps the area change non-negative: the smaller root of
    dm² − (2m1 + 2m2 + 1) dm + 2m1m2, floored, ⌊(b − √(b² − 8 m1 m2))/2⌋ with b = 2m1 + 2m2 + 1 (b² − 8m1m2 =
    4m1² + 4m2² + 4m1 + 4m2 + 1 > 0). Integer arithmetic: ⌊b − √D⌋ = b − ⌈√D⌉."""
    from math import isqrt
    b = 2 * m1 + 2 * m2 + 1
    D = b * b - 8 * m1 * m2
    s = isqrt(D)
    ceil_sqrt = s if s * s == D else s + 1
    return (b - ceil_sqrt) // 2


def registered_ticks(P, h):
    """The far window's readout of a clock: a window of h far ticks registers ⌊P h⌋ completed ticks of a clock whose rate
    against the far cut's is the exact rational P — the unit-pulse sequence s_k = ⌊kP⌋ of 21-gravity's Lemma 6.2 (the pulse
    law, C27) read at k = h, a tick counted whole; the window count of Lemma 3.3(i) rounds a weight (relaxation.count) and
    is a different rule (Lean: FRC.Relaxation.clockTicks, no_tick_iff, one_tick_outside)."""
    return (P * h).numerator // (P * h).denominator


def operational_cut_count(Om, M):
    """The operational cut as a count on the Carrier Om (21-gravity, Proposition 8.2 after D5, 21 November 2026). The far
    cut is the no-wrap horizon h = ⌊√Om⌋; across the cell between the decoherence counts s and s + 1 the offset increment is
    u(s) − u(s + 1) = M/(s(s + 1)), u = M/s, and the composed rate from h inward to r is P(r) = ∏_{s=r}^{h−1} (1 − M/(s(s+1))),
    an exact rational (the increments telescope to M/r − M/h). The far window of h ticks registers ⌊P h⌋ ticks
    (registered_ticks). The cut is the outermost r > ⌊√M⌋ whose clock registers no tick in a window of h far ticks, P(r) < 1/h
    (D3 of 21 November 2026: the strict crossing). Returns (r_f, P(r_f), P(r_f + 1)), or None when the rate stays at or
    above the floor down to the slip core."""
    from math import isqrt
    h = isqrt(Om)
    floor_rate = Fraction(1, h)
    P, prev = Fraction(1), Fraction(1)
    r = h
    while r > isqrt(M):
        if P < floor_rate:
            return r, P, prev
        r -= 1
        prev, P = P, P * (1 - Fraction(M, r * (r + 1)))
    return None
