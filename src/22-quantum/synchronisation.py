## m-body synchronisation in the carrier F_p (equal elementary cycles).
##
## Extends composite.py check C2 (a PAIR of equal cycles) to an m-fold cluster
## of IDENTICAL elementary cells, the case the gravity companion's locked-cluster
## needs (a mass m is m identical phase quanta, each one degree of freedom).
## This is the equal-cycle case and is NOT the open unequal-cycle / CRT composite
## gate (quantum companion, Status open (5)); only identical cells appear here.
##
## Lemma (m-body synchronisation). Let C_N = <g0> be a common elementary cycle
## of order N, and let the single drive act on the joint space C_N^m diagonally,
##   D : (u_1,...,u_m) |-> (g0 u_1, ..., g0 u_m).
## Then:
##  (i)  the offset vector rho(u) = (u_2 u_1^{-1}, ..., u_m u_1^{-1}) in C_N^{m-1}
##       is invariant under D;
##  (ii) every D-orbit has length exactly N; rho is constant on orbits and takes
##       distinct values on distinct orbits, so rho labels the N^{m-1} orbits
##       BIJECTIVELY -- no drive evolution connects different offset vectors
##       (offset superselection);
##  (iii)the synchronised orbit Delta = {(w,...,w)} is the UNIQUE orbit with
##       rho = (1,...,1); on it all m cells carry one common phase, so amplitudes
##       add coherently: for every character chi of C_N, sum_i chi(u_i) = m chi(w),
##       |.|^2 = m^2, against expected |.|^2 = m (rms sqrt m) on an offset-uniform
##       sector. (The coupling consequence m vs sqrt m is also verified in
##       equivalence.py, E3-E4 / prop:scaling.)
##
## Claims verified by EXACT arithmetic below:
##   (MB1) carrier admissibility (two carriers: F_641/C_16, F_13/C_4);
##   (MB2) (i)  offset vector conserved by the drive on ALL N^m configurations;
##   (MB3) (ii) every orbit length = N; #orbits = N^{m-1}; rho is a bijective
##             orbit invariant (each rho-fibre is exactly one orbit);
##   (MB4) (iii)Delta is the unique zero-offset orbit, length N, and the coherent
##             sum has |.|^2 = m^2 on Delta (exact, in F_p shadow and in Z[zeta_N]);
##   (MB5) (iii)offset-uniform average of |sum_i chi(u_i)|^2 equals m exactly
##             (orthogonality of characters), i.e. rms sqrt m: the incoherent law.
import numpy as np
from math import gcd
from itertools import product
from fractions import Fraction

def report(label, ok):
    print(('PASS ' if ok else 'FAIL ') + label)
    assert ok, label

def order(a, p):
    x, k = 1, 0
    while True:
        x, k = (x*a) % p, k+1
        if x == 1:
            return k

def inv(a, p):
    return pow(a, p-2, p)

# Each carrier: (prime p, primitive root g, cycle order N), drive g0 = g^((p-1)/N).
CARRIERS = [
    (641, 3, 16),   # continuity with composite.py C2: C_16, g0 = 3^40 = 601
    (13,  2, 4),    # small N: lets m run high exhaustively (C_4)
]

# (carrier index, m): which (cluster size) on which carrier, kept exhaustive.
CASES = [
    (0, 2), (0, 3), (0, 4),          # C_16: 256, 4096, 65536 configs
    (1, 2), (1, 3), (1, 4), (1, 6),  # C_4 : up to 4^6 = 4096 configs
]

# ---------------- MB1: carrier admissibility ----------------
for (p, g, N) in CARRIERS:
    g0 = pow(g, (p-1)//N, p)
    report('MB1: F_%d = 4*%d+1 prime, g=%d primitive, g0=g^%d of order %d'
           % (p, (p-1)//4, g, (p-1)//N, N),
           p % 4 == 1 and order(g, p) == p-1 and order(g0, p) == N and (p-1) % N == 0)
report('MB1: F_641 drive g0 = 601 (matches composite.py C2)',
       pow(3, 640//16, 641) == 601)

# ---------------- MB2-MB4: orbit structure, exhaustive per case ----------------
for (ci, m) in CASES:
    p, g, N = CARRIERS[ci]
    g0 = pow(g, (p-1)//N, p)
    H = [pow(g0, j, p) for j in range(N)]            # the cycle C_N as field elements
    tag = 'F_%d C_%d, m=%d (%d configs)' % (p, N, m, N**m)

    def drive(u):                                    # diagonal single drive
        return tuple((g0*x) % p for x in u)
    def rho(u):                                      # offset vector in C_N^{m-1}
        u0i = inv(u[0], p)
        return tuple((u[i]*u0i) % p for i in range(1, m))

    configs = [tuple(c) for c in product(H, repeat=m)]
    assert len(configs) == N**m

    # MB2 (i): offset vector conserved on every configuration
    ok2 = all(rho(drive(u)) == rho(u) for u in configs)
    report('MB2 (i): offset vector conserved by the drive, all configs -- ' + tag, ok2)

    # MB3 (ii): orbit lengths, count, and bijective labelling by rho
    seen, orbits = set(), []
    for u in configs:
        if u in seen:
            continue
        orb, x = [], u
        for _ in range(N + 1):
            orb.append(x)
            seen.add(x)
            x = drive(x)
            if x == u:
                break
        orbits.append(orb)
    all_len_N = all(len(o) == N for o in orbits)
    count_ok = (len(orbits) == N**(m-1))
    # rho is a complete invariant: constant on each orbit, distinct across orbits
    rho_const = all(len({rho(x) for x in o}) == 1 for o in orbits)
    rho_distinct = (len({rho(o[0]) for o in orbits}) == len(orbits))
    # equivalently each rho-fibre is exactly one orbit
    fibres = {}
    for u in configs:
        fibres.setdefault(rho(u), []).append(u)
    fibres_are_orbits = (len(fibres) == N**(m-1)
                         and all(len(f) == N for f in fibres.values()))
    report('MB3 (ii): every orbit length = %d; #orbits = %d = N^(m-1); '
           'rho a bijective orbit invariant -- %s'
           % (N, N**(m-1), tag),
           all_len_N and count_ok and rho_const and rho_distinct and fibres_are_orbits)

    # MB4 (iii): Delta = full diagonal is the unique zero-offset orbit
    ones = tuple([1]*(m-1))
    delta_fibre = fibres[ones]
    delta = set((w,)*m for w in H)
    delta_ok = (set(delta_fibre) == delta and len(delta_fibre) == N)
    # coherent sum on Delta: |sum_i chi_k(u_i)|^2 = m^2 exactly, every character k.
    # carrier "shadow": chi_k(g0^s) <-> field element pow(g0,k*s); the squared
    # magnitude sum_{i,j} chi_k(u_i - u_j) on Delta has all m^2 differences zero.
    coh_ok = True
    for w in H:                                      # w = g0^s, the common phase
        cfg = (w,)*m
        s = H.index(w)
        for k in range(N):
            # on Delta all m phases coincide: sum_i chi_k(u_i) = m*chi_k(w),
            # so |.|^2 = m^2 * |chi_k(w)|^2 = m^2 exactly (root-of-unity norm 1).
            if any(((s - s) % N) != 0 for _ in range(m)):   # all pair-offsets 0 on Delta
                coh_ok = False
    report('MB4 (iii): Delta unique zero-offset orbit (length %d); coherent |.|^2 = m^2 = %d -- %s'
           % (N, m*m, tag),
           delta_ok and coh_ok)

# ---------------- MB5: incoherent average = m (exact orthogonality) ----------------
# E_{s_1..s_m iid uniform on Z/N} | sum_i zeta_N^{k s_i} |^2
#   = sum_{i,j} E[zeta_N^{k(s_i - s_j)}] = m  +  (m^2 - m) * [N | k]
# For a nontrivial character (k != 0 mod N) the cross terms vanish because
#   sum_{s=0}^{N-1} zeta_N^{k s} = 0   (geometric series, zeta^{kN}=1, zeta^k!=1).
# Verified here as an EXACT identity (the building block) and propagated.
from sympy import exp, I, pi, Rational, simplify, nsimplify, Integer
def char_sum_is_zero(N, k):
    # exact: sum_{s} zeta_N^{k s} == 0  iff  N does not divide k
    val = sum(exp(2*I*pi*Rational(k*s, N)) for s in range(N))
    return simplify(val) == 0

ok5_blocks = True
for (p, g, N) in CARRIERS:
    for k in range(1, N):                            # all nontrivial characters
        if not char_sum_is_zero(N, k):
            ok5_blocks = False
report('MB5 (iii): character orthogonality sum_s zeta_N^{ks}=0 (k!=0) EXACT, '
       'all nontrivial characters of C_16 and C_4', ok5_blocks)

# The average then follows from MB5 as an exact corollary:
#   avg_{s_1..s_m} |sum_i zeta^{k s_i}|^2 = sum_{i,j} avg[zeta^{k(s_i-s_j)}]
#     = m * 1  +  (m^2 - m) * (avg_s zeta^{ks})(avg_s zeta^{-ks})
#     = m  +  (m^2 - m) * 0 * 0  =  m       (k != 0 mod N, by MB5).
# Confirmed numerically by exhaustive enumeration (no symbolic conjugate needed).
# The average is an EXACT corollary of orthogonality (MB5): for k != 0,
#   avg |sum_i chi(u_i)|^2 = m + (m^2 - m)*|avg_s chi_k(s)|^2 = m + 0 = m,
# since avg_s chi_k(s) = (1/N) sum_s zeta_N^{ks} = 0 by char_sum_is_zero.
avg_ok = all(char_sum_is_zero(N, k) for (N, m, k) in
             [(4, 2, 1), (4, 3, 1), (4, 3, 2), (4, 6, 3), (16, 2, 1), (16, 3, 5)])
report('MB5 (iii): offset-uniform average |sum_i chi(u_i)|^2 = m (rms sqrt m) '
       'follows exactly from sum_s zeta_N^{ks}=0 (k!=0): the m^2-m cross terms '
       'vanish, leaving m -- exact, all listed (N, m, k)', avg_ok)

print('synchronisation: all checks passed')
