"""
c_charts.py — block C: the external spherical comparison (2:E2, E3, E4)
=======================================================================
Section 5 of the paper.  C1 (CHART): the base-grid covering radius of the comparison map Xi_{13,g} against the
bound sqrt2·pi/(p−1) of prop:grid-density.  C2 (EXACT, rationals): the fixed-shell scale grid {x/g^n : |x| ≤ 2κ}
has a covering radius in [0, 1] bounded below by ½ min(g^−m, 1 − 2κ g^−(m+1)) at every depth — the bounded
precision of a fixed shell, prop:fixed-shell-density and thm:operational-precision (C2b: the covering radius
exceeds ε = 1/20 on every tested shell).  C3 (CHART): across the tower of shells the grids resolve every target (1:G2).
"""
import math
from fractions import Fraction
import geocommon as gc

def fib_sphere(N):
    pts = []
    ga = math.pi * (3 - math.sqrt(5))
    for j in range(N):
        z = 1 - 2 * (j + .5) / N; r = math.sqrt(1 - z * z); t = ga * j
        pts.append((r * math.cos(t), r * math.sin(t), z))
    return pts

def geod(u, v): return math.acos(max(-1., min(1., u[0] * v[0] + u[1] * v[1] + u[2] * v[2])))

def fixed_shell_radius(p, g, N, H=None):
    """Covering radius in [0,1] of {x/g^n : 0 <= x <= H, n <= N}; H = 2κ (the balanced window) by default."""
    k = (p - 1) // 4; H = 2 * k if H is None else H
    pts = sorted({Fraction(x, g ** n) for n in range(N + 1) for x in range(0, H + 1) if x <= g ** n})
    return max(b - a for a, b in zip(pts, pts[1:])) / 2

def lower_bound(p, g, H=None):
    """½ min(g^−m, 1 − H g^−(m+1)) with m = floor(log_g(H+1)): the cut of lean fixed_shell_bound."""
    k = (p - 1) // 4; H = 2 * k if H is None else H; m = 0
    while g ** (m + 1) <= H + 1: m += 1
    return min(Fraction(1, g ** m), 1 - Fraction(H, g ** (m + 1))) / 2

def tower_best(t, shells, N=12):
    best = 1.
    for p, g in shells:
        k = (p - 1) // 4
        for n in range(N + 1):
            for x in range(0, 2 * k + 1):
                best = min(best, abs(t - x / g ** n))
    return best

def run():
    # C1 the base-grid covering radius at p = 13 within sqrt2·pi/(p−1) (2:E2) — chart
    p = 13; pi = 6; n = 12
    grid = [(0., 0., 1.), (0., 0., -1.)]
    for a in range(1, pi + 1):
        th = math.pi * a / pi
        for m in range(n):
            ph = 2 * math.pi * m / n
            grid.append((math.sin(th) * math.cos(ph), math.sin(th) * math.sin(ph), math.cos(th)))
    cov = max(min(geod(x, y) for y in grid) for x in fib_sphere(60000))
    bound = math.sqrt(2) * math.pi / (p - 1)
    gc.check("C1", "base-grid covering radius at p = 13 within the bound sqrt2 pi/(p-1)", cov <= bound,
             f"measured {cov:.4f} rad, bound {bound:.4f} rad", kind="CHART")

    # C2 the fixed-shell refinement is bounded (2:E3) — exact rationals
    ok = True; det = []
    for p, g in [(13, 2), (13, 11), (13, 6), (17, 3), (29, 2), (173, 2)]:
        radii = [fixed_shell_radius(p, g, N) for N in (3, 6, 12, 24)]
        lb = lower_bound(p, g)
        radii_p = [fixed_shell_radius(p, g, N, p - 1) for N in (12, 24)]; lb_p = lower_bound(p, g, p - 1)
        ok &= all(r >= lb for r in radii) and radii[-1] == radii[-2] and all(r >= lb_p for r in radii_p) and radii_p[0] == radii_p[1]
        det.append(f"({p},{g}): radius {radii[-1]} >= {lb}")
    gc.check("C2", "fixed-shell covering radius stabilises at >= 1/2 min(g^-m, 1 - H g^-(m+1)) for every depth (H = 2k and H = p-1)", ok, "; ".join(det[:4]))
    eps = Fraction(1, 20)
    viol = [(p, g) for p, g in [(13, 2), (13, 11), (17, 3), (29, 2)] if fixed_shell_radius(p, g, 40) > eps]
    gc.check("C2b", "fixed-shell density at eps = 1/20: the covering radius exceeds 1/20 on every tested shell", viol == [(13, 2), (13, 11), (17, 3), (29, 2)],
             f"shells with covering radius > 1/20 at N = 40: {viol}")

    # C3 the tower of shells resolves every target (2:E4, 1:G2) — chart
    targets = [0.9, 1 / 3, math.pi / 4, math.sqrt(2) - 1]
    tower = [(p, 2) for p in (13, 29, 173, 1013, 4093)]
    errs = [tower_best(t, tower) for t in targets]
    single = [tower_best(t, [(13, 2)]) for t in targets]
    gc.check("C3", "the tower of shells (p = 13..4093, g = 2) brings every target within 1/2048; the single shell (13, 2) does not",
             all(e <= 1 / 2048 for e in errs) and max(single) > 1 / 16,
             "tower errors " + ", ".join(f"{e:.2e}" for e in errs) + "; single shell " + ", ".join(f"{e:.3f}" for e in single), kind="CHART")

if __name__ == "__main__":
    run(); gc.summary(write=False)
