#!/usr/bin/env python3
"""O9 exact checks: signature is a square-class dichotomy on F_p (EXACT).

Remark rem:signature-record (Section 2); ledger row 8:B7. All arithmetic exact; no floats.

Claims checked, on every symmetry-complete shell p = 4k+1 < 60:
  S1  The Euclidean form t^2+x^2+y^2+z^2 has p^3+p^2-p zeros in F_p^4
      (square discriminant: hyperbolic, Witt index 2).
  S2  The form -nu t^2+x^2+y^2+z^2 with nu the canonical nonsquare g has
      p^3-p^2+p zeros (nonsquare discriminant: elliptic, Witt index 1).
  S3  At p = 13 the counts are 2353 and 2041.
  S4  Over F_{p^2} every element of F_p is a square: nu = w^2 for some
      w in F_{p^2}, so the extension erases the dichotomy.
"""
from dcommon import check

def is_prime(n):
    if n < 2: return False
    i = 2
    while i * i <= n:
        if n % i == 0: return False
        i += 1
    return True

def primitive_root(p):
    order = p - 1
    fac = []; m = order; d = 2
    while d * d <= m:
        if m % d == 0:
            fac.append(d)
            while m % d == 0: m //= d
        d += 1
    if m > 1: fac.append(m)
    for g in range(2, p):
        if all(pow(g, order // q, p) != 1 for q in fac): return g
    raise RuntimeError

def zero_count(p, a_t):
    # number of (t,x,y,z) with a_t*t^2 + x^2 + y^2 + z^2 = 0 in F_p
    sq = [0] * p
    for v in range(p): sq[v * v % p] += 1
    # distribution of x^2+y^2+z^2
    conv2 = [0] * p
    for u in range(p):
        for v in range(p):
            conv2[(u + v) % p] += sq[u] * sq[v]
    conv3 = [0] * p
    for u in range(p):
        for v in range(p):
            conv3[(u + v) % p] += conv2[u] * sq[v]
    total = 0
    for t in range(p):
        need = (-a_t * t * t) % p
        total += conv3[need]
    return total

def run():
    ok1 = ok2 = ok4 = True; c13 = None
    for p in range(5, 60):
        if not is_prime(p) or p % 4 != 1: continue
        g = primitive_root(p)
        e = zero_count(p, 1)
        q = zero_count(p, (-g) % p)   # the form -g t^2 + x^2 + y^2 + z^2
        ok1 &= e == p**3 + p**2 - p
        ok2 &= q == p**3 - p**2 + p
        ok4 &= (p * p - 1) // 2 % (p - 1) == 0      # F_p^x has order p-1 | (p^2-1)/2: every a in F_p^x is a square in F_{p^2}
        if p == 13: c13 = (e, q)
    check("o9.S1", ok1, "p = 5 … 53, p ≡ 1 (mod 4)")
    check("o9.S2", ok2, "ν = g the smallest primitive root")
    check("o9.S3", c13 == (2353, 2041), f"p = 13: {c13}")
    check("o9.S4", ok4, "(p² − 1)/2 ≡ 0 (mod p − 1)")

if __name__ == "__main__":
    import dcommon
    run(); dcommon.summary(write=False)
