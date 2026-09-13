#!/usr/bin/env python3
"""O7 exact checks: the two speed-of-light seats; parity resolution (EXACT).

Blueprint item O7; findings in reports/o7-flag-parity.md. All arithmetic
exact; square classes by the Euler criterion; discrete logs by exhaustive
exponent scan on small shells (dev shells only).

Claims checked:
  P1  Parity form of the square class: for primitive g the squares are
      exactly <g^2>, so the class of x is the parity of dlog_g(x) --
      the drive-step (chronon) parity.  Exhaustive on F_13, F_17 for
      every primitive g; Euler-criterion form on all symmetry-complete
      shells p < 2000.
  P2  The exact factorization nu = c^2 * (2g): shell-generic since
      2*c^2 = 1; lab-Carrier instance (mod Om = 2,408,561):
      c^2 = 1,204,281, 2g = 12, product = 6 = g.
  P3  Parity split: [c^2] is even (square) iff kappa is even (the
      admissibility class: the two-way constant is registered exactly
      where c exists); [2g] is odd iff kappa is even; the product is
      odd on every shell -- the cofactor carries the entire signature
      bit in both parities.
  P4  Chart-grading insufficiency: on kappa-even shells every element
      of Q4 = {1, i, -1, -i} is a square -- the order-four chart
      family carries no signature on the admissibility class; the
      signature lives in the parity grading, invisible to torsion-free
      (and Q4D) bookkeeping.
  P5  Registered transport is even: N(g x) = g^2 N(x) identically
      (framed-complex norm), and g^2 is a square -- per-chronon
      two-way/comparison readings are even-parity; the one-way
      multiplier g is odd; no x in F_p has x^2 = g (the cone slope is
      the unregistrable half-step).
  P6  Gauge stability: dlog_g(g^{-1}) = -1 is odd -- the B19 flip
      g -> g^{-1} preserves the parity class while reversing the
      one-way direction (finite Reichenbach freedom).
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

def primitive_roots(p):
    n = p - 1
    fac, m, d = set(), n, 2
    while d * d <= m:
        while m % d == 0:
            fac.add(d); m //= d
        d += 1
    if m > 1:
        fac.add(m)
    return [g for g in range(2, p) if all(pow(g, n // q, p) != 1 for q in fac)]

def shells(limit):
    for p in range(5, limit):
        if p % 4 == 1 and all(p % d for d in range(2, int(p**0.5) + 1)):
            yield p

# P1 exhaustive on dev shells: class of g^j = parity of j, every primitive g
for p in (13, 17):
    for g in primitive_roots(p):
        for j in range(p - 1):
            chk(f"P1 p={p} g={g} j={j}", is_sq(pow(g, j, p), p) == (j % 2 == 0))
# P1 Euler form on the scan: <g^2> = squares
for p in shells(2000):
    g = primitive_roots(p)[0]
    chk(f"P1 p={p} g odd", not is_sq(g, p))
    chk(f"P1 p={p} g^2 even", is_sq(g * g % p, p))

# P2 factorization
for p in shells(2000):
    g = primitive_roots(p)[0]
    c2 = (p + 1) // 2                       # 2^{-1}
    chk(f"P2 p={p} nu = c^2*2g", (c2 * 2 * g) % p == g % p)
Om, S, gO = 2408561, 602140, 6
c2O = (Om + 1) // 2
chk("P2 lab Carrier c^2 = 2S+1", c2O == 2 * S + 1 == 1204281)
chk("P2 lab Carrier c^2*(2g) = g", (c2O * 12) % Om == 6)

# P3 parity split; P4 chart-grading insufficiency
for p in shells(2000):
    kap = (p - 1) // 4
    g = primitive_roots(p)[0]
    c2 = (p + 1) // 2
    chk(f"P3 p={p} [c^2] even iff kappa even", is_sq(c2, p) == (kap % 2 == 0))
    chk(f"P3 p={p} [2g] odd iff kappa even", (not is_sq(2 * g % p, p)) == (kap % 2 == 0))
    chk(f"P3 p={p} product odd", not is_sq(c2 * 2 * g % p, p))
    if kap % 2 == 0:
        i = pow(g, kap, p)
        chk(f"P4 p={p} Q4 all squares", all(is_sq(x, p) for x in (1, i, p - 1, p - i)))

# P5 registered transport even; cone slope unregistrable
for p, g in ((13, 2), (17, 3)):
    for a in range(p):
        for b in range(p):
            if (a, b) == (0, 0):
                continue
            n1 = (a * a + b * b) % p
            ga, gb = (g * a) % p, (g * b) % p
            chk(f"P5 p={p} N(gx)=g^2N(x) ({a},{b})",
                (ga * ga + gb * gb) % p == (g * g * n1) % p)
    chk(f"P5 p={p} g^2 square", is_sq(g * g % p, p))
    chk(f"P5 p={p} x^2=g insoluble", all(pow(x, 2, p) != g for x in range(p)))

# P6 flip parity
for p in shells(2000):
    g = primitive_roots(p)[0]
    chk(f"P6 p={p} g^-1 odd", not is_sq(pow(g, p - 2, p), p))

print(f"{checks}/{checks} exact checks pass")
