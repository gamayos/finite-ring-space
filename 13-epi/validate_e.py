"""FRC emergence of e: verification suite.
Sections:
  [1] Metric emergence of e from the derangement chain n!/D_n (exact rationals).
  [2] Frame-internal arithmetic: antiperiodicity, blind scales, wall identity, series duals.
  [3] Angular unit e_t = g^{i_t}: two-valued angle, radian calibration search over p < 10^6.
  [4] Null experiment: pointwise identification g^{i_t} = k(e)-residue solvability statistics.
"""
import math, sys
from fractions import Fraction
from decimal import Decimal, getcontext

OUT = []
def log(s=""):
    print(s); OUT.append(str(s))

# ---------- helpers ----------
def sieve(N):
    comp = bytearray(N + 1)
    for i in range(2, int(N**0.5) + 1):
        if not comp[i]:
            comp[i*i::i] = b'\x01' * len(comp[i*i::i])
    return [i for i in range(2, N + 1) if not comp[i]]

def derangements_exact(N):
    D = [1, 0]
    for n in range(2, N + 1):
        D.append(n * D[n-1] + (-1)**n)
    return D

def e_fraction(K=260):
    s, f = Fraction(0), 1
    for k in range(K):
        if k: f *= k
        s += Fraction(1, f)
    return s   # |s - e| < 3/K! < 10^-500 for K=260

def frac_to_dec(fr, prec=140):
    getcontext().prec = prec
    return Decimal(fr.numerator) / Decimal(fr.denominator)

# =========================================================
log("="*72); log("[1] METRIC EMERGENCE: the chain eps_n = n!/D_n")
log("="*72)
E = e_fraction(300)
NMAX = 110
D = derangements_exact(NMAX)
fact = [1]
for n in range(1, NMAX + 1): fact.append(fact[-1] * n)

# (a) error bound |n!/D_n - e| < 8/(n+1)!  and alternating enclosure
bound_ok, encl_ok = True, True
for n in range(2, 61):
    err = Fraction(fact[n], D[n]) - E
    if abs(err) >= Fraction(8, fact[n+1]): bound_ok = False
    if (err > 0) != (n % 2 == 1): encl_ok = False   # sign(eps_n - e) = (-1)^{n+1}
log(f"(a) |n!/D_n - e| < 8/(n+1)! for n=2..60 : {'PASS' if bound_ok else 'FAIL'}")
log(f"    alternating enclosure eps_even < e < eps_odd : {'PASS' if encl_ok else 'FAIL'}")

# (b) minimal n whose framed rational rounds to the IEEE-754 double nearest e
target = math.e
n_double = None
for n in range(2, 40):
    if float(Fraction(fact[n], D[n])) == target:
        n_double = n; break
log(f"(b) minimal n with float(n!/D_n) == IEEE-double(e): n = {n_double}")
log(f"    n!/D_n at n={n_double}: {fact[n_double]}/{D[n_double]}")
log(f"    |eps_17 - e| = {float(abs(Fraction(fact[17],D[17])-E)):.3e},  half-ulp(e) = {math.ulp(math.e)/2:.3e}")

# (c) 100-digit determination
n100 = None
for n in range(2, NMAX):
    if Fraction(8, fact[n+1]) < Fraction(1, 10**100):
        n100 = n; break
d_chain = frac_to_dec(Fraction(fact[n100], D[n100]), 130)
d_e     = frac_to_dec(E, 130)
match = 0
s1, s2 = str(d_chain), str(d_e)
for a, b in zip(s1, s2):
    if a == b: match += 1
    else: break
log(f"(c) 100-digit precision reached at n = {n100}; leading agreement with e: {match-1} chars")
log(f"    e            = {str(d_e)[:105]}")
log(f"    {n100}!/D_{n100}     = {str(d_chain)[:105]}")

# (d) feasibility comparison with (1+1/n)^n
log("(d) precision-cost comparison (steps n needed for 2^-k):")
for k in (24, 53, 333):
    # derangement chain: 8/(n+1)! < 2^-k
    n1 = 2
    while Fraction(8, fact[n1+1]) >= Fraction(1, 2**k): n1 += 1
    # compound chain: |(1+1/n)^n - e| ~ e/(2n) -> n ~ e*2^{k-1}
    n2 = math.e * 2**(k-1)
    log(f"    k={k:3d}:  derangement chain n = {n1:3d}   |   (1+1/n)^n chain n ~ {n2:.2e}")

# =========================================================
log(); log("="*72); log("[2] FRAME-INTERNAL ARITHMETIC (per-prime structure)")
log("="*72)

def d_mod(p, upto):
    """derangement residues D_0..D_upto mod p via recurrence"""
    d = [1 % p, 0]
    s = -1
    for n in range(2, upto + 1):
        s = -s
        d.append((n * d[n-1] + s) % p)
    return d

def kurepa_mod(p):
    f, s = 1, 1
    for k in range(1, p):
        f = f * k % p
        s = (s + f) % p
    return s

def alt_fact_mod(p):
    f, s, sg = 1, 1, 1
    for k in range(1, p):
        f = f * k % p
        sg = -sg
        s = (s + sg * f) % p
    return s % p

sample_primes = [5, 13, 29, 101, 257, 1009, 10007]
log(f"{'p':>6} | D_(p-1)==!p | antiperiod D_(n+p)==-D_n | wall residue k(e)= -(!p)^-1 | blind set Z0(p)")
for p in sample_primes:
    d = d_mod(p, 2*p)
    kp = kurepa_mod(p)
    wall = (d[p-1] == kp)
    anti = all(d[n+p] == (-d[n]) % p for n in range(0, p))
    z0 = [n for n in range(p) if d[n] == 0]
    ke = (-pow(kp, -1, p)) % p if kp else None
    log(f"{p:6d} |   {'PASS' if wall else 'FAIL'}      |          {'PASS' if anti else 'FAIL'}           |    {ke!s:>8}                | {z0 if len(z0)<=8 else str(z0[:8])+'...'} (|Z0|={len(z0)})")

# series duals
log()
log("Series duals at the wall:  S- := sum (-1)^k/k! == -!p ;  S+ := sum 1/k! == -A(p)")
dual_ok = True
prod_examples = []
for p in [7, 13, 29, 101, 257, 1009]:
    invf, f = [1], 1
    for k in range(1, p):
        f = f * k % p
        invf.append(pow(f, -1, p))
    Sm = sum(((-1)**k) * invf[k] for k in range(p)) % p
    Sp = sum(invf[k] for k in range(p)) % p
    kp, ap = kurepa_mod(p), alt_fact_mod(p)
    if Sm != (-kp) % p or Sp != (-ap) % p: dual_ok = False
    prod_examples.append((p, (kp * ap) % p))
log(f"  duals verified for p in [7,13,29,101,257,1009]: {'PASS' if dual_ok else 'FAIL'}")
log(f"  group-law breaking at the wall: (!p * A(p)) mod p = {prod_examples}  (would be == 1 if exp(1)exp(-1)=1 survived)")

# blind-scale statistics
log()
primes_stat = [p for p in sieve(5000) if 1000 < p < 5000]
sizes = []
for p in primes_stat:
    d = d_mod(p, p - 1)
    z = sum(1 for n in range(p) if (d[n] if n < len(d) else None) == 0)
    sizes.append(z)
from collections import Counter
cnt = Counter(sizes)
mean = sum(sizes)/len(sizes)
log(f"Blind-scale statistics over {len(primes_stat)} primes in (1000,5000):")
log(f"  |Z0(p)| distribution: {dict(sorted(cnt.items()))},  mean = {mean:.3f}")
log(f"  (n=1 is always blind since D_1=0; excess over 1 has mean {mean-1:.3f}, Poisson(1) predicts 1.000)")

# =========================================================
log(); log("="*72); log("[3] ANGULAR UNIT e_t = g^{i_t}: radian calibration over p < 10^6")
log("="*72)
LIM = 1000000
primes = sieve(LIM)
alpha_star = 1.0 / (2*math.pi)
best = []
count_001 = 0
n_p1mod4 = 0
for p in primes:
    if p % 4 != 1: continue
    n_p1mod4 += 1
    # sqrt(-1) mod p via a quadratic nonresidue
    a = 2
    while pow(a, (p-1)//2, p) != p - 1: a += 1
    r = pow(a, (p-1)//4, p)
    for rr in (r, p - r):
        alpha = rr / (p - 1)
        delta = abs(2*math.pi*alpha - 1.0)   # |theta - 1 rad|
        if delta < 0.01: count_001 += 1
        best.append((delta, p, rr))
best.sort()
log(f"primes p==1 (mod 4) below 10^6: {n_p1mod4}")
log(f"frames with |theta_t - 1 rad| < 0.01: {count_001}  (equidistribution predicts ~ {2*0.01/(2*math.pi)*n_p1mod4*2:.0f} over both orientations)")
log("best radian-calibrated frames (p, i_t-label r, theta_t, |theta_t - 1|):")
for delta, p, rr in best[:6]:
    log(f"  p={p:7d}  r={rr:7d}  theta={2*math.pi*rr/(p-1):.9f}  delta={delta:.3e}")

# =========================================================
log(); log("="*72); log("[4] NULL EXPERIMENT: pointwise g^{i_t} == k(e)-wall-residue?")
log("="*72)
def primitive_root(p):
    fac = []
    m = p - 1; d = 2
    while d*d <= m:
        if m % d == 0:
            fac.append(d)
            while m % d == 0: m //= d
        d += 1
    if m > 1: fac.append(m)
    for g in range(2, p):
        if all(pow(g, (p-1)//q, p) != 1 for q in fac):
            return g
    return None

solvable, total = 0, 0
corr_x, corr_y = [], []
for p in [q for q in sieve(3000) if q % 4 == 1 and q > 5]:
    kp = kurepa_mod(p)
    if kp == 0: continue
    Ep = (-pow(kp, -1, p)) % p            # wall residue of e
    g0 = primitive_root(p)
    # index table
    ind = {}
    x = 1
    for m in range(p - 1):
        ind[x] = m
        x = x * g0 % p
    s = ind[Ep]
    a = 2
    while pow(a, (p-1)//2, p) != p - 1: a += 1
    r = pow(a, (p-1)//4, p)
    ok = (math.gcd(s, p-1) == math.gcd(r, p-1)) or (math.gcd(s, p-1) == math.gcd(p - r, p-1))
    solvable += ok; total += 1
    corr_x.append(min(r, p-r)/(p-1)); corr_y.append(s/(p-1))
# Pearson correlation
mx = sum(corr_x)/len(corr_x); my = sum(corr_y)/len(corr_y)
num = sum((x-mx)*(y-my) for x, y in zip(corr_x, corr_y))
den = math.sqrt(sum((x-mx)**2 for x in corr_x) * sum((y-my)**2 for y in corr_y))
log(f"p==1(4), 5<p<3000: some frame g with g^(i_t) == -(!p)^(-1) exists for {solvable}/{total} primes ({100*solvable/total:.1f}%)")
log(f"Pearson correlation between angular address of i_t and of the wall residue: {num/den:+.4f}")
log("=> solvability is gcd-coincidence noise, no invariant identification; the two objects are distinct projections.")

import os
with open(os.path.join(os.path.dirname(os.path.abspath(__file__)), "results.txt"), "w") as f:
    f.write("\n".join(OUT) + "\n")
log(); log("results written to results.txt")
