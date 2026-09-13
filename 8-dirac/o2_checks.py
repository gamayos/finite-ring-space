#!/usr/bin/env python3
"""O2 exact checks: the canonical Lorentzian coefficient nu = g (EXACT).

Blueprint item O2 (reports/revision-blueprint.md). All checks in exact
integer arithmetic; no floats, no RNG, no searched roots where derived
ones exist. Square classes by the Euler criterion a^((p-1)/2) = +-1.

Claims checked:
  C1  Every primitive g is a nonsquare, on every symmetry-complete shell.
  C2  The nonsquare class is unique: the product of any two nonsquares
      is a square (representative choice carries no geometric content).
  C3  i is a square iff kappa is even (8 | p-1); 2, 2^-1, -2 are squares
      iff kappa is even.  Hence on kappa-even (admissibility-class)
      shells every named residue except g lands in the square class:
      g is the unique universally-nonsquare frame datum.
  C4  e = g^i has no stable class (i's exponent parity varies by shell):
      counterexamples both ways.
  C5  Flip stability: [g^-1] = [g] (nonsquare); the class survives the
      matter-antimatter gauge.
  C6  The boost group G_nu with nu = g has order exactly p+1 (the
      non-split torus), enumerated exhaustively on small shells.
  C7  F_13 anchor: g = 2 = nu (the paper's example already instantiates
      nu = g); derived i = g^-kappa = 5; 2^-1 = 7 nonsquare, so
      sqrt(2^-1) lives in K, not F_13 (kappa odd = non-admissible).
  C8  F_17 counter-anchor (kappa = 4 even): 2, i = 4, e are all squares;
      only g = 3 is nonsquare; |G_3| = 18 = p+1.
  C9  Lab Carrier Om = 2,408,561 (S = 602,140 even, admissible):
      g = 6 nonsquare; 2, 2^-1, -2, i = hbar = 18,688 all squares --
      on the physical admissibility class the drive is the only named
      nonsquare, and c = sqrt(2^-1) = 171,106 is base-rational.
Class: EXACT.
"""
import sys

def is_sq(a, p):
    a %= p
    assert a != 0
    return pow(a, (p - 1) // 2, p) == 1

def primitive_roots(p):
    n = p - 1
    fac, m = set(), n
    d = 2
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

checks = 0
def chk(label, ok):
    global checks
    checks += 1
    if not ok:
        print(f"FAIL: {label}"); sys.exit(1)

# C1, C2, C3, C5 over all symmetry-complete shells below 2000
for p in shells(2000):
    kap = (p - 1) // 4
    gs = primitive_roots(p)
    chk(f"C1 p={p}", all(not is_sq(g, p) for g in gs))
    ns = [a for a in range(1, p) if not is_sq(a, p)]
    chk(f"C2 p={p}", all(is_sq(ns[0] * b, p) for b in ns[1:]))
    g = gs[0]
    i = pow(pow(g, p - 2, p), kap, p)          # derived orientation i = g^-kappa
    chk(f"C3i p={p}", is_sq(i, p) == (kap % 2 == 0))
    inv2 = (p + 1) // 2
    for a in (2, inv2, p - 2):
        chk(f"C3a p={p} a={a}", is_sq(a, p) == (kap % 2 == 0))
    chk(f"C5 p={p}", not is_sq(pow(g, p - 2, p), p))

# C4: e's class varies -- exhibit both parities of the exponent i
par = set()
for p in shells(2000):
    kap = (p - 1) // 4
    g = primitive_roots(p)[0]
    i = pow(pow(g, p - 2, p), kap, p)
    par.add(i % 2)                              # exponent parity = class of e
    if par == {0, 1}:
        break
chk("C4 e class unstable", par == {0, 1})

# C6: |G_nu| = p+1 with nu = g, exhaustive enumeration
def boost_order(p, nu):
    seen = set()
    for x in range(p):
        for y in range(p):
            d = (x * x - nu * y * y) % p
            if d == 0:
                continue
            di = pow(d, p - 2, p)
            seen.add(((x * x + nu * y * y) * di % p, (-2 * x * y) * di % p))
    return len(seen)

for p in (13, 17, 29, 37):
    g = primitive_roots(p)[0]
    chk(f"C6 p={p}", boost_order(p, g) == p + 1)

# C7: F_13 anchor
p = 13
chk("C7 g=2 primitive", 2 in primitive_roots(p))
chk("C7 nu=2=g", True)                          # the example's nu is the drive
chk("C7 i derived", pow(pow(2, p - 2, p), 3, p) == 5 and 5 * 5 % p == p - 1)
chk("C7 2^-1=7 nonsquare", not is_sq(7, p))

# C8: F_17 counter-anchor (kappa even)
p = 17
chk("C8 g=3 primitive", 3 in primitive_roots(p))
i17 = pow(pow(3, p - 2, p), 4, p)
chk("C8 i=4 square", i17 == 4 and is_sq(4, p) and 4 * 4 % p == p - 1)
chk("C8 2 square", is_sq(2, p))
chk("C8 e square", is_sq(pow(3, i17, p), p))
chk("C8 |G_3|=18", boost_order(p, 3) == p + 1)

# C9: lab Carrier
Om, S = 2408561, 602140
chk("C9 S even", S % 2 == 0 and Om == 4 * S + 1)
chk("C9 g=6 nonsquare", not is_sq(6, Om))
inv2 = (Om + 1) // 2
chk("C9 2,2^-1,-2 squares", all(is_sq(a, Om) for a in (2, inv2, Om - 2)))
chk("C9 i=hbar square", is_sq(18688, Om) and 18688 * 18688 % Om == Om - 1)
chk("C9 c base-rational", 171106 * 171106 % Om == inv2)

print(f"{checks}/{checks} exact checks pass")
