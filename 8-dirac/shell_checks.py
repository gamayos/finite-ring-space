#!/usr/bin/env python3
"""Shell-reading checks: the free evolution is the drive (EXACT).

Verifies Theorem (zonal evolution) and its corollaries on F_13 and F_17,
plus the F_17 Dirac example numbers quoted in the manuscript.

  Z1  The drive pullback (D psi)(x) = psi(g^{-1} x) is a permutation
      operator (unitary); on the character chi_k(g^j) = g^{jk} it acts
      with eigenvalue g^{-k}: the winding-k mode gains phase g^{-k} per
      chronon, exhaustively over all k and all cycle points.
  Z2  Isotropy: <chi_k, chi_k> = 0 except k = 0 and k = (p-1)/2, whose
      eigenvalues are +-1 = N^1 intersect the phase cycle.
  Z3  Sector separation: the eigenvalue g^{-1} has order p-1 > 2, hence
      lies outside N^1: the free evolution is not a Cayley step of any
      Hamiltonian with Frobenius-fixed spectrum.
  Z4  F_17 example: frame (t;0,1,3), derived i = 3^{-4} = 4, i^2 = -1;
      2, i, e = g^i all squares (only g nonsquare); with nu = g = 3 and
      x = y = 1: A = 15, B = 1, A^2 - nu B^2 = 1; |G_3| = 18 = p + 1;
      an order-3 boost exists (triality), none exists at p = 13.
Class: EXACT.
"""
import sys

checks = 0
def chk(label, ok):
    global checks
    checks += 1
    if not ok:
        print(f"FAIL: {label}"); sys.exit(1)

def is_sq(a, p):
    return pow(a % p, (p - 1) // 2, p) == 1

for p, g in ((13, 2), (17, 3)):
    n = p - 1
    # Z1: eigen-relation of the pullback on every character, every point
    for k in range(n):
        lam = pow(g, (-k) % n, p)
        chk(f"Z1 p={p} k={k}",
            all(pow(g, ((j - 1) * k) % n, p) == lam * pow(g, (j * k) % n, p) % p
                for j in range(n)))
    # Z2: isotropy pattern
    for k in range(n):
        s = sum(pow(g, (2 * j * k) % n, p) for j in range(n)) % p
        chk(f"Z2 p={p} k={k}", (s == 0) == (k not in (0, n // 2)))
    chk(f"Z2 p={p} real eigenvalues",
        pow(g, 0, p) == 1 and pow(g, (-(n // 2)) % n, p) == p - 1)
    # Z3: sector separation
    o, v = 1, pow(g, n - 1, p)          # g^{-1}
    u = v
    while u != 1:
        u = u * v % p; o += 1
    chk(f"Z3 p={p} ord(g^-1) = p-1", o == n)

# Z4: the F_17 anchor
p, g = 17, 3
i = pow(pow(g, p - 2, p), 4, p)
chk("Z4 i = 4, i^2 = -1", i == 4 and i * i % p == p - 1)
chk("Z4 2, i, e squares; g nonsquare",
    is_sq(2, p) and is_sq(i, p) and is_sq(pow(g, i, p), p) and not is_sq(g, p))
nu = g
d = (1 - nu) % p
di = pow(d, p - 2, p)
A, B = (1 + nu) * di % p, (-2) * di % p
chk("Z4 A = 15, B = 1", A == 15 and B == 1)
chk("Z4 A^2 - nu B^2 = 1", (A * A - nu * B * B) % p == 1)
def boost_count(p, nu):
    seen = set()
    for x in range(p):
        for y in range(p):
            dd = (x * x - nu * y * y) % p
            if dd == 0:
                continue
            ddi = pow(dd, p - 2, p)
            seen.add(((x * x + nu * y * y) * ddi % p, (-2 * x * y) * ddi % p))
    return seen
G17 = boost_count(17, 3)
G13 = boost_count(13, 2)
chk("Z4 |G_3| = 18", len(G17) == 18)
chk("Z4 |G_2| = 14", len(G13) == 14)
def kord(a, b, p, nu):
    x, y, o = a, b, 1
    while (x, y) != (1, 0):
        x, y = (x * a + nu * y * b) % p, (x * b + y * a) % p, ; o += 1
    return o
# order-3 element in N^1: exists iff 3 | p+1 (via A - B w norm-one coords)
def n1_orders(p, nu):
    out = set()
    for x in range(p):
        for y in range(p):
            if (x * x - nu * y * y) % p == 1:
                out.add(kord(x, y, p, nu))
    return out
chk("Z4 triality at p=17", 3 in n1_orders(17, 3))
chk("Z4 no triality at p=13", 3 not in n1_orders(13, 2))

print(f"{checks}/{checks} exact checks pass")
