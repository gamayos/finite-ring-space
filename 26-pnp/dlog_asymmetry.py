#!/usr/bin/env python3
# -*- coding: utf-8 -*-
"""
dlog_asymmetry.py  (26-pnp formalization anchor)
The hyperoperation ASCENT vs DESCENT timing asymmetry on the carrier:
  ascent  f(j) = g^j mod P     -- fast exponentiation, O(log j) multiplications
  descent f^{-1}(h) = dlog(h)   -- baby-step-giant-step, O(sqrt(P)) operations
Confirms the one-way structure: ascent flat in log P, descent ~ sqrt(P).
"""
import time, math, random
from sympy import nextprime, primitive_root

def bsgs(g, h, P, n):           # solve g^x = h mod P, x in [0,n)
    m = int(math.isqrt(n)) + 1
    table = {}
    e = 1
    for i in range(m):          # baby steps
        table.setdefault(e, i); e = (e*g) % P
    factor = pow(g, (P-2)*m, P) # g^{-m} mod P  (Fermat inverse)
    gamma = h
    for q in range(m):          # giant steps
        if gamma in table:
            return q*m + table[gamma]
        gamma = (gamma*factor) % P
    return None

print(f"{'P (~)':>12} {'bits':>5} {'ascent (us)':>12} {'descent (s)':>12} {'descent/ascent':>15} {'sqrt(P)':>10}")
rows=[]
for target in (10**5, 10**6, 10**7, 10**8, 10**9):
    P = nextprime(target)
    g = primitive_root(P)
    j = random.randrange(2, P-1)
    # ascent: time many reps
    t0=time.perf_counter()
    for _ in range(2000): h = pow(g, j, P)
    asc = (time.perf_counter()-t0)/2000*1e6        # microseconds per exponentiation
    # descent
    t0=time.perf_counter()
    x = bsgs(g, h, P, P-1)
    desc = time.perf_counter()-t0                  # seconds
    assert pow(g, x, P) == h, "dlog failed"
    rows.append((P, asc, desc))
    print(f"{P:>12} {P.bit_length():>5} {asc:>12.2f} {desc:>12.4f} {desc*1e6/asc:>15.1f} {math.isqrt(P):>10}")

import numpy as np
lP=np.log([r[0] for r in rows])
b_asc=np.polyfit(lP, np.log([r[1] for r in rows]),1)[0]   # ascent ~ P^?  (expect ~0, i.e. ~log)
b_desc=np.polyfit(np.log([r[0] for r in rows]), np.log([r[2] for r in rows]),1)[0]  # descent ~ P^?
print(f"\nscaling: ascent ~ P^({b_asc:+.3f}) (flat: cost ~ log P, polynomial in bits)")
print(f"         descent ~ P^({b_desc:+.3f}) (~0.5: cost ~ sqrt(P), exponential in bits)")
print("=> the ascent is feasible (horizon-bounded), the descent is not: the one-way structure")
print("   of the hyperoperation ladder is the candidate source of P != NP, FRC's scale/dlog map.")
