#!/usr/bin/env python3
"""38-s13 check_fibrations.py (from the Y4 push of 2026-09-17, master row C22): the two torus fibrations of the order-p(p^2-1) frame varieties, exact.

On the norm-one quaternion sphere S3(F_p) = SL_2(F_p) and on the observable variety
PGL_2(F_p) = SO_3(F_p) there are two coset fibrations with the same count factorisation
p(p^2-1) = (p-1) * p(p+1) = (p+1) * p(p-1):

  SPLIT      fibre S^1 = {x + y i : x^2 + y^2 = 1}, the drive torus C_{p-1} (p = 4k+1),
             base the unit 2-sphere {x^2+y^2+z^2 = 1}, p(p+1) points   (40-hyper thm:hopf, row B2;
             the drawn leaves of 38-s13 sky B6: left multiplication by the unit i)
  NON-SPLIT  fibre the boost torus T = C_{p+1}, base the nonsquare-radius 2-sphere, p(p-1) points
             = Terras's finite upper half-plane                        (38-s13 th:hopf = master C19)

The Borel section of C19 exists for the non-split fibration on PGL_2 only: the split fibre lies
inside the Borel (B ∩ S^1 = S^1), so the split fibration has no transversal in B at all.
Run: python3 y4_two_fibrations.py   (exit 0 iff every check passes)
"""
import sys
from itertools import product

FAILS = 0
def check(name, cond, *nums):
    global FAILS
    if not cond: FAILS += 1
    print(("PASS " if cond else "FAIL ") + name + ("  [" + ", ".join(map(str, nums)) + "]" if nums else ""))

def eta(a, p):
    a %= p
    return 0 if a == 0 else (1 if pow(a, (p-1)//2, p) == 1 else -1)

def mul(m, n, p):
    a, b, c, d = m; e, f, g, h = n
    return ((a*e+b*g) % p, (a*f+b*h) % p, (c*e+d*g) % p, (c*f+d*h) % p)
def det(m, p): return (m[0]*m[3] - m[1]*m[2]) % p
def inv2(m, p):
    a, b, c, d = m; di = pow(det(m, p), p-2, p)
    return ((d*di) % p, (-b*di) % p, (-c*di) % p, (a*di) % p)
def canon(m, p):
    for x in m:
        if x % p:
            f = pow(x, p-2, p); return tuple((v*f) % p for v in m)

def run(p):
    nu = next(a for a in range(2, p) if eta(a, p) == -1)
    r = next(a for a in range(1, p) if (a*a) % p == p-1) if eta(-1, p) == 1 else None
    print(f"\n=== p = {p}, nu = {nu}, eta(-1) = {eta(-1, p)} ===")
    circle = [(x, y) for x in range(p) for y in range(p) if (x*x + y*y) % p == 1]
    check(f"p={p}: |S^1| = #{{x^2+y^2=1}} = p - eta(-1) (p-1 at p=4k+1: the drive torus; p+1 at p=4k+3)",
          len(circle) == p - eta(-1, p), len(circle), p+1)
    SL = {m for m in product(range(p), repeat=4) if det(m, p) == 1}
    G = {canon(m, p) for m in product(range(p), repeat=4) if det(m, p)}
    B_SL = {(a, b, 0, pow(a, p-2, p)) for a in range(1, p) for b in range(p)}
    B = {canon((a, b, 0, 1), p) for a in range(1, p) for b in range(p)}   # the Borel of PGL_2, order p(p-1)
    if r is not None:
        # the circle subgroup in SL_2: x + y i -> diag(x + r y, x - r y): the diagonal (split) torus
        S1 = {((x + r*y) % p, 0, 0, (x - r*y) % p) for x, y in circle}
        check(f"p={p}: the circle subgroup is the diagonal torus of SL_2, order p-1, inside the Borel",
              len(S1) == p-1 and S1 <= B_SL, len(S1), len(S1 & B_SL))
        cos1 = {frozenset(mul(g, s, p) for s in S1) for g in SL}
        ui = (r, 0, 0, (-r) % p)
        fib1 = {}
        for g in SL: fib1.setdefault(mul(mul(g, ui, p), inv2(g, p), p), set()).add(g)
        base1 = set(fib1)
        unit = {(a, b, c) for a, b, c in product(range(p), repeat=3) if (a*a + b*c) % p == 1}
        # the orbit of i = diag(r,-r) is the quadric {a^2+bc = -det i = r^2 = -1}; at p = 4k+1 it is the unit quadric scaled by r
        unit_i = {(a, b, c) for a, b, c in product(range(p), repeat=3) if (a*a + b*c) % p == p-1}
        check(f"p={p}: SPLIT fibration of S3=SL_2: q -> q i q^-1, fibres = the p(p+1) cosets of S^1, base = the unit 2-sphere {{a^2+bc=1}} (p(p+1) points)",
              {frozenset(v) for v in fib1.values()} == cos1 and len(cos1) == p*(p+1)
              and {(m[0], m[1], m[2]) for m in base1} == unit_i and len(unit_i) == len(unit) == p*(p+1), len(cos1), len(unit))
        check(f"p={p}: SPLIT: the Borel meets every fibre in the whole fibre or not at all: no section in B (B_SL ∩ S^1 = S^1)",
              all(len(c & B_SL) in (0, p-1) for c in cos1) and len(S1 & B_SL) == p-1)
        # 40-hyper's Hopf identity, the count face of the split fibration
        check(f"p={p}: 40-hyper B2: |S3| = |S^1| |S^2| = (p-1) p(p+1)", len(SL) == len(circle)*len(unit), len(SL), len(circle)*len(unit))
    # the non-split fibration on PGL_2 (C19) and on SL_2 (no section)
    T = {canon((x, (nu*y) % p, y, x), p) for x in range(p) for y in range(p) if (x or y) and (x*x - nu*y*y) % p}
    un = (0, nu, 1, 0)
    cosT = {frozenset(canon(mul(g, t, p), p) for t in T) for g in G}
    fibT = {}
    for g in G: fibT.setdefault(mul(mul(g, un, p), inv2(g, p), p), set()).add(g)
    nsq = {(a, b, c) for a, b, c in product(range(p), repeat=3) if (a*a + b*c) % p == nu}
    check(f"p={p}: NON-SPLIT fibration of PGL_2: g -> g u_n g^-1 (u_n^2 = nu, nonsquare), fibres = the p(p-1) cosets of T = C_(p+1), base the nonsquare sphere {{a^2+bc=nu}} (p(p-1) points)",
          {frozenset(v) for v in fibT.values()} == cosT and len(cosT) == p*(p-1) and len(set(fibT)) == len(nsq) == p*(p-1), len(cosT), len(nsq))
    check(f"p={p}: NON-SPLIT: the Borel meets every fibre exactly once (C19's section); B ∩ T = 1",
          all(len(c & B) == 1 for c in cosT) and len(B & T) == 1)
    T_SL = {(x, (nu*y) % p, y, x) for x in range(p) for y in range(p) if (x*x - nu*y*y) % p == 1}
    cosT_SL = {frozenset(mul(g, t, p) for t in T_SL) for g in SL}
    hits = sorted({len(c & B_SL) for c in cosT_SL})
    check(f"p={p}: NON-SPLIT on S3=SL_2: p(p-1) cosets of C_(p+1); the Borel meets a coset in 0 or 2 elements (the sign): no section",
          len(cosT_SL) == p*(p-1) and hits == [0, 2], len(cosT_SL), hits)
    # involution counts: SL_2 has one (-I), PGL_2 has p^2: the two order-p(p^2-1) groups are not isomorphic
    I2 = (1, 0, 0, 1)
    invSL = sum(1 for g in SL if g != I2 and mul(g, g, p) == I2)
    invG = sum(1 for g in G if g != canon(I2, p) and canon(mul(g, g, p), p) == canon(I2, p))
    check(f"p={p}: involutions: SL_2 has 1, PGL_2 has p^2 -- same order, non-isomorphic groups", invSL == 1 and invG == p*p, invSL, invG)
    # the frame count as boundary data: PGL_2 = P1 x F_p x C_(p-1) exactly, (p+1) p (p-1)
    check(f"p={p}: frame count = (direction) x (shell cell) x (drive phase) = (p+1) p (p-1) = |PGL_2|, B = F_p x C_(p-1) as a set",
          (p+1)*p*(p-1) == len(G) and len(B) == p*(p-1), (p+1)*p*(p-1))

for p in (5, 13, 17):
    run(p)
print(f"\nTOTAL FAILS: {FAILS}")
sys.exit(1 if FAILS else 0)
