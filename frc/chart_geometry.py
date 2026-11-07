"""frc.chart_geometry — 2-geometry's readings against the continuum (the chart theme, 6 November 2026).

The comparison map Ξ_{p,g} of 2-geometry (Def. 5.1) in floating point: the covering radius of the base grid on the unit
sphere against the bound δ_p = √2·π/(p − 1) (2:E2), the operational precision at the shell's resolution (2:E4) on
Lipschitz observables, and the external transport χ(g^m) = exp(−2πi·m/n) with its step, half-period and quarter-turn
identities (2:F6). Floats and the reals appear only here (gate G09).

    base_radius(p, samples)         the sampled covering radius of Ξ_{p,g}(V(S_p)) and the bound δ_p
    precision(p, L, configs)        the largest observable change over L-Lipschitz test observables, and L²·δ_p
    tolerance_shell(L, num, den)    the least prime p ≡ 1 (mod 4) with x < p ≤ 2x, x = max(7, √2·π·L²/ε + 1), ε = num/den
    transport(p, g, i)              True iff χ is injective and carries the step, π and i to the classical roles
"""
import math
import random


def _xi(p, a, m):
    pi = (p - 1) // 2; th = math.pi * a / pi; ph = 2 * math.pi * m / (p - 1)
    return (math.sin(th) * math.cos(ph), math.sin(th) * math.sin(ph), math.cos(th))


def _geod(u, v):
    return math.acos(max(-1.0, min(1.0, u[0] * v[0] + u[1] * v[1] + u[2] * v[2])))


def _fib(N):
    ga = math.pi * (3 - math.sqrt(5)); out = []
    for j in range(N):
        z = 1 - 2 * (j + 0.5) / N; r = math.sqrt(1 - z * z); t = ga * j
        out.append((r * math.cos(t), r * math.sin(t), z))
    return out


def vertices(p):
    pi = (p - 1) // 2
    return [(0.0, 0.0, 1.0)] + [_xi(p, a, m) for a in range(1, pi + 1) for m in range(p - 1)]


def base_radius(p, samples=60000):
    """(the sampled covering radius of the vertex images, the bound √2·π/(p − 1))."""
    grid = vertices(p)
    return max(min(_geod(x, y) for y in grid) for x in _fib(samples)), math.sqrt(2) * math.pi / (p - 1)


def precision(p, L, configs=40, seed=7):
    """(the largest change of the L-Lipschitz test observables O(X) = L·Σ_k d(x_k, c_k) over random configurations of
    r = L points moved to their nearest vertex images, the bound L²·δ_p)."""
    rnd = random.Random(seed); grid = vertices(p); pts = _fib(400)
    worst = 0.0
    for _ in range(configs):
        X = [rnd.choice(pts) for _ in range(L)]; C = [rnd.choice(pts) for _ in range(L)]
        Y = [min(grid, key=lambda y: _geod(x, y)) for x in X]
        O = lambda Z: L * sum(_geod(z, c) for z, c in zip(Z, C))
        worst = max(worst, abs(O(X) - O(Y)))
    return worst, L * L * math.sqrt(2) * math.pi / (p - 1)


def transport(p, g, i):
    """χ(g^m) = exp(−2πi·m/n): injective, χ(g^{m+1}) = χ(g)χ(g^m), χ(g^{m+π}) = −χ(g^m), χ(i·g^m) = i·χ(g^m)."""
    n = p - 1; k = n // 4
    log = {pow(g, m, p): m for m in range(n)}
    chi = lambda x: complex(math.cos(-2 * math.pi * log[x] / n), math.sin(-2 * math.pi * log[x] / n))
    ok = len({(round(chi(pow(g, m, p)).real, 9), round(chi(pow(g, m, p)).imag, 9)) for m in range(n)}) == n
    for m in range(n):
        x = pow(g, m, p)
        ok &= abs(chi(x * g % p) - chi(g) * chi(x)) < 1e-12 and abs(chi(pow(g, m + 2 * k, p)) + chi(x)) < 1e-12
        ok &= abs(chi(i * x % p) - 1j * chi(x)) < 1e-12
    return ok


def tolerance_shell(L, num, den):
    """The least prime p ≡ 1 (mod 4) in Breusch's interval (x, 2x], x = max(7, √2·π·L²/ε + 1), ε = num/den, provided it
    meets the tolerance (p − 1 > √2·π·L²/ε); None otherwise."""
    T = math.sqrt(2) * math.pi * L * L * den / num
    x = max(7, T + 1)
    for q in range(math.floor(x) + 1, math.floor(2 * x) + 1):
        if q % 4 == 1 and all(q % d for d in range(2, math.isqrt(q) + 1)):
            return q if q - 1 > T else None
    return None
