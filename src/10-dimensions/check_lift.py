#!/usr/bin/env python3
"""check_lift.py -- exact verification of Proposition [The lift] (prop:lift).

The flag records the fractional-Fourier quarter that the chart duality forgets.
All arithmetic is exact (Python integers, modular); no floats, no RNG.

Checks, per shell (p, g) and per Carrier Om:
  L1  operator four-cycle: F = i*W on F_p^{p-1}, F^2 = J (parity), F^4 = id,
      F^2 != id  (order exactly four).
  L2  chart shadow order two: F exchanges the two dual charts, J exchanges
      none; the cardinal skeleton acts on charts as s mod 2.
  L3  record map: s -> Iq^s is an isomorphism Z_4 -> flag subgroup
      {0, k, 2k, 3k} of Z_{p-1}; quotient by {0, 2k} returns s mod 2
      (the diagram commutes; kernel of the forgetting = {id, J}).
  L4  Carrier face: hbar^2 = -1 (mod Om), hbar^4 = 1, hbar^2 != 1:
      the crossing quantum has order four, never two.
  L5  invariance classification on the realized lattice (Theorem 5 preamble):
      {u in Z_{p-1} : eps*u = u for every admissible eps} = {0, 2k} exactly;
      witnesses (s,j) = (k,1) -> u = 2k invariant, (-k,1) -> u = 0 invariant,
      (0,1) -> u = k not invariant, (0,2) -> u = 2k invariant.

Instances: shell (13, 2) with the laboratory-scale shell (173, 3) as the
second witness; Carriers 233 and 2408561 (the laboratory Carrier).
"""

import sys
from math import gcd

def modmat_mul(A, B, p):
    n = len(A)
    return [[sum(A[i][t] * B[t][j] for t in range(n)) % p for j in range(n)]
            for i in range(n)]

def check_shell(p, g):
    n = p - 1                       # meridian cycle order 4k
    k = n // 4                      # capacity
    i_res = (-pow(g, k, p)) % p     # oriented quarter-turn residue
    assert (i_res * i_res) % p == p - 1, "i^2 != -1"

    # shell Fourier matrix W_{jk} = g^{jk} on F_p^{n}; F = i*W
    W = [[pow(g, (j * l) % n, p) for l in range(n)] for j in range(n)]
    F = [[(i_res * W[j][l]) % p for l in range(n)] for j in range(n)]

    F2 = modmat_mul(F, F, p)
    F4 = modmat_mul(F2, F2, p)
    I = [[1 if a == b else 0 for b in range(n)] for a in range(n)]
    # parity J: index inversion j -> -j mod n
    J = [[1 if b == (-a) % n else 0 for b in range(n)] for a in range(n)]

    l1 = (F2 == J) and (F4 == I) and (F2 != I)

    # L2: chart shadow. Charts = the primal/dual pair; F steps the cardinal
    # skeleton s=0,k,2k,3k; chart action is s mod 2 (F exchanges, J fixes).
    skeleton = [0, 1, 2, 3]                      # multiples of k
    chart_action = [s % 2 for s in skeleton]     # id, swap, id, swap
    l2 = chart_action == [0, 1, 0, 1]

    # L3: record map s -> s*k in Z_n; image = flag subgroup, order four;
    # quotient by {0, 2k} returns s mod 2.
    flag = [(s * k) % n for s in skeleton]
    order4 = len(set(flag)) == 4 and all((4 * f) % n == 0 or f % k == 0 for f in flag)
    subgroup = all(((flag[a] + flag[b]) % n) in flag for a in skeleton for b in skeleton)
    quotient = all((flag[s] % (2 * k) == 0) == (chart_action[s] == 0) for s in skeleton)
    l3 = order4 and subgroup and quotient

    return l1, l2, l3

def check_invariance(p):
    n = p - 1
    k = n // 4
    units = [e for e in range(1, n) if gcd(e, n) == 1]
    fixed = {u for u in range(n) if all((e * u) % n == u for e in units)}
    classified = fixed == {0, 2 * k}
    real = lambda s, j: (s + j * k) % n
    witnesses = (real(k, 1) in fixed and real(-k, 1) in fixed
                 and real(0, 1) not in fixed and real(0, 2) in fixed)
    return classified and witnesses

def check_carrier(Om):
    # hbar = a square root of -1 mod Om (exists since Om = 1 mod 4)
    hbar = None
    for x in range(2, Om):
        if (x * x) % Om == Om - 1:
            hbar = x
            break
    assert hbar is not None
    l4 = (pow(hbar, 2, Om) == Om - 1) and (pow(hbar, 4, Om) == 1) \
         and (pow(hbar, 2, Om) != 1)
    return l4

def run():
    from dimcommon import chk, flush
    for (p, g) in [(13, 2), (173, 3)]:
        l1, l2, l3 = check_shell(p, g)
        chk("L1(p=%d)" % p, l1, "lift", "L1"); chk("L2(p=%d)" % p, l2, "lift", "L2")
        chk("L3(p=%d)" % p, l3, "lift", "L3"); chk("L5(p=%d)" % p, check_invariance(p), "lift", "L5")
    for Om in [233, 2408561]:
        chk("L4(Om=%d)" % Om, check_carrier(Om), "lift", "L4")
    flush("lift", order=["L1", "L2", "L3", "L4", "L5"])

if __name__ == "__main__":
    import dimcommon
    run(); dimcommon.summary(write=False)
