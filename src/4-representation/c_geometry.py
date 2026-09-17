"""
c_geometry.py — block C: the finite ring geometry of embeddings (4:E1, E2, E3)
==============================================================================
Section 6 of the paper.  C1 (CHART): the character chart of the shell, z ↦ (cos 2πkz/p, sin 2πkz/p)_{k<p−1}, is
equivariant — a translation z ↦ z + a rotates plane k by 2πka/p — and has ‖Emb(z)‖² = p − 1 for every z: the whole
chart lies on one sphere; a chart that is not equivariant (random) does not.  C2 (EXACT): the same in the shell's
own arithmetic — the conjugate norm Σ_k g^{kz} g^{k(n−z)} equals n = p − 1 for every z and every generator g, and
translation multiplies coordinate k by g^{ka}.  C3 (CHART): the quantisation count — the grid points Δ·Z^d within
Δ/2 of a sphere of radius R grow like (R/Δ)^{d−1} (fitted exponents at d = 2, 3).  C4, C5 (EXACT): the Gödel
code G(x) = ∏ p_i^{x_i} is injective on the box {0..4}³ over the primes 2, 3, 5 (125 distinct codes, maximum
810 000); reduced modulo the least prime above the maximum, q = 810 013, it stays injective, while smaller moduli
collide; the two-prime code 2^a 3^b is injective on a, b ≤ 20 (the core instance), and signed coordinates are
coded after a shift.
"""
import math, random
import repcommon as rc

def emb(p, z):
    return [f(2 * math.pi * k * z / p) for k in range(1, p) for f in (math.cos, math.sin)]

def run():
    # C1 the character chart on the sphere (chart)
    ok = True; det = []
    for p, k in rc.SHELLS[:4]:
        norms = [sum(c * c for c in emb(p, z)) for z in range(p)]
        ok &= all(abs(n - (p - 1)) < 1e-9 for n in norms)
        # equivariance: Emb(z + a) = R(a) Emb(z), R(a) the block rotation by 2 pi k a / p in plane k
        for a in range(1, p):
            for z in range(p):
                e, ez = emb(p, z + a), emb(p, z)
                for kk in range(1, p):
                    c, s = math.cos(2 * math.pi * kk * a / p), math.sin(2 * math.pi * kk * a / p)
                    x, y = ez[2 * (kk - 1)], ez[2 * (kk - 1) + 1]
                    ok &= abs(c * x - s * y - e[2 * (kk - 1)]) < 1e-9 and abs(s * x + c * y - e[2 * (kk - 1) + 1]) < 1e-9
        det.append(f"p={p}: |Emb|^2 = {p-1}")
    random.seed(1)
    rnd = [[random.gauss(0, 1) for _ in range(8)] for _ in range(13)]
    spread = max(sum(c * c for c in v) for v in rnd) - min(sum(c * c for c in v) for v in rnd)
    ok &= spread > 1                                                                       # a non-equivariant chart is not on a sphere
    rc.check("C1", "the character chart z -> (cos 2 pi k z/p, sin 2 pi k z/p)_k has |Emb(z)|^2 = p-1 for every z and is translation-equivariant (block rotations); a random chart is not on a sphere", ok,
             "; ".join(det) + f"; random control: norm spread {spread:.1f}", kind="CHART")

    # C2 the conjugate norm in the shell's arithmetic, exact
    ok = True; det = []
    for p, k in rc.SHELLS:
        n = p - 1
        for g in rc.generators(p):
            for z in range(n + 1):
                ok &= sum(pow(g, kk * z, p) * pow(g, kk * (n - z), p) for kk in range(n)) % p == n % p
            for z in range(n):
                for a in range(1, 4):
                    ok &= all(pow(g, kk * (z + a), p) == pow(g, kk * a, p) * pow(g, kk * z, p) % p for kk in range(n))
        det.append(f"p={p}: {len(rc.generators(p))} generators")
    rc.check("C2", "sum_k g^(kz) g^(k(n-z)) = n = p-1 in F_p for every z <= n and every generator; translation multiplies coordinate k by g^(ka)", ok, "; ".join(det[:4]))

    # C3 the quantisation count on the sphere (chart): exponent d-1
    def count(d, r):
        """grid points of Z^d within 1/2 of the sphere of radius r (Delta = 1)."""
        rng = range(-int(r) - 1, int(r) + 2)
        if d == 2:
            return sum(1 for x in rng for y in rng if abs(math.hypot(x, y) - r) <= 0.5)
        return sum(1 for x in rng for y in rng for z in rng if abs(math.sqrt(x * x + y * y + z * z) - r) <= 0.5)
    ok = True; det = []
    for d in (2, 3):
        radii = list(range(10, 101, 10)) if d == 2 else list(range(5, 41, 5))
        cs = [count(d, r) for r in radii]
        xs = [math.log(r) for r in radii]; ys = [math.log(c) for c in cs]
        mx, my = sum(xs) / len(xs), sum(ys) / len(ys)
        slope = sum((x - mx) * (y - my) for x, y in zip(xs, ys)) / sum((x - mx) ** 2 for x in xs)   # least squares
        ok &= abs(slope - (d - 1)) < 0.15
        det.append(f"d={d}: R = {radii[0]}..{radii[-1]}, counts {cs[0]}..{cs[-1]}, slope {slope:.2f}")
    rc.check("C3", "grid points within Delta/2 of the sphere of radius R number ~ (R/Delta)^(d-1): least-squares exponents within 0.15 of d-1 at d = 2, 3", ok, "; ".join(det), kind="CHART")

    # C4 the Goedel code on the box {0..4}^3 over 2, 3, 5; reduction mod q
    box = [(a, b, c) for a in range(5) for b in range(5) for c in range(5)]
    G = {x: 2 ** x[0] * 3 ** x[1] * 5 ** x[2] for x in box}
    ok = len(set(G.values())) == len(box) == 125
    mx = max(G.values()); ok &= mx == 810000
    q = mx + 1
    while not rc.is_prime(q): q += 1
    ok &= q == 810013 and len({v % q for v in G.values()}) == 125
    coll = {m: 125 - len({v % m for v in G.values()}) for m in (101, 1009, 10007, 100003)}
    ok &= coll[101] > 0                                                                    # below the maximum the guarantee lapses
    rc.check("C4", "G(x) = 2^a 3^b 5^c is injective on {0..4}^3 (125 codes, max 810000); mod q = 810013 (the least prime above the maximum) injective by the bound; below it the bound gives nothing: mod 101 there are collisions", ok,
             f"collisions below the maximum: {coll} (none at 1009, 10007, 100003 is the accident of these residues, not the bound)")

    # C5 the two-prime core instance and signed coordinates
    codes = {(a, b): 2 ** a * 3 ** b for a in range(21) for b in range(21)}
    ok = len(set(codes.values())) == 441
    signed = [(a, b, c) for a in range(-2, 3) for b in range(-2, 3) for c in range(-2, 3)]
    Gs = {x: 2 ** (x[0] + 2) * 3 ** (x[1] + 2) * 5 ** (x[2] + 2) for x in signed}
    ok &= len(set(Gs.values())) == 125 and max(Gs.values()) == 810000
    rc.check("C5", "2^a 3^b injective on a, b <= 20 (441 codes); signed coordinates in {-2..2}^3 coded after the shift +2: 125 distinct codes, the same maximum", ok, "")

if __name__ == "__main__":
    run(); rc.summary(write=False)
