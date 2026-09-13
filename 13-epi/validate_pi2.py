"""Follow-up: quarter-wall two-squares invariant, arcsin supercongruence, proof sanity checks."""
import math
from fractions import Fraction
from math import comb

OUT = []
def log(s=""):
    print(s); OUT.append(str(s))

def sieve(N):
    c = bytearray(N + 1)
    for i in range(2, int(N**0.5) + 1):
        if not c[i]: c[i*i::i] = b'\x01' * len(c[i*i::i])
    return [i for i in range(3, N + 1) if not c[i]]

def two_squares(p):
    for a in range(1, int(p**0.5) + 1):
        b = int((p - a*a)**0.5)
        if a*a + b*b == p:
            return (a, b) if a % 2 == 1 else (b, a)
    return None

# ---- [A] Quarter-wall: Gauss congruence C(2t,t) == 2a (mod p), a odd, a == 1 (mod 4);
#          and k(w_t) == -(a^2)^{-1} == (b^2)^{-1} (mod p)
log("[A] QUARTER-WALL TWO-SQUARES INVARIANT, all p == 1 (mod 4), p < 3000")
ok_g, ok_w, cnt = True, True, 0
for p in [q for q in sieve(3000) if q % 4 == 1]:
    t = (p - 1)//4
    a, b = two_squares(p)
    astar = a if a % 4 == 1 else -a           # Gauss normalization
    C = 1
    for n in range(t): C = C * 2*(2*n+1) % p * pow(n+1, -1, p) % p   # C(2t,t) mod p
    if C != (2*astar) % p: ok_g = False; log(f"  Gauss fails at p={p}")
    kw = pow(16, t, p) * pow(t % p, -1, p) % p * pow(C*C % p, -1, p) % p
    if kw != (-pow(a*a % p, -1, p)) % p or kw != pow(b*b % p, -1, p) % p:
        ok_w = False; log(f"  wall formula fails at p={p}")
    cnt += 1
log(f"  Gauss congruence C(2t,t) == 2a* (mod p): {'PASS' if ok_g else 'FAIL'} ({cnt} primes)")
log(f"  k(w_t) == -(a^2)^(-1) == (b^2)^(-1) (mod p): {'PASS' if ok_w else 'FAIL'}")
p = 13; a, b = two_squares(13)
log(f"  example p=13 = {a}^2+{b}^2: k(w_3) = {pow(16,3,13)*pow(3,-1,13)*pow(pow(comb(6,3),2,13),-1,13)%13} = -(9)^(-1) = 10")

# ---- [B] arcsin supercongruence: sigma == 0 (mod p^2) and third-order invariant
log(); log("[B] ARCSIN CHAIN sigma_p := sum_(k=0)^((p-3)/2) C(2k,k)/((2k+1)16^k)")
ok2 = True
rows = []
def euler_mod(p, upto):
    E = [0]*(upto+1); E[0] = 1 % p
    for n in range(1, upto//2 + 1):
        s = sum(comb(2*n, 2*j) * E[2*j] for j in range(n))
        E[2*n] = (-s) % p
    return E
def bernoulli_upto(N):
    """Exact Bernoulli numbers B_0..B_N via sum C(n+1,k) B_k = 0."""
    B = [Fraction(0)] * (N + 1); B[0] = Fraction(1)
    for n in range(1, N + 1):
        B[n] = -sum(Fraction(comb(n+1, k)) * B[k] for k in range(n)) / (n + 1)
    return B
BERN = bernoulli_upto(297)
for p in [q for q in sieve(300) if q >= 5]:
    m = (p-1)//2
    sig = sum(Fraction(comb(2*k, k), (2*k+1)*16**k) for k in range(m))
    num, den = sig.numerator, sig.denominator
    if num % (p*p) != 0: ok2 = False; log(f"  p^2 fails at p={p}")
    T3 = (num//(p*p)) % p * pow(den % p, -1, p) % p
    E = euler_mod(p, p-3)[p-3]
    r = T3 * pow(E, -1, p) % p if E % p else None
    Bpm3 = BERN[p-3]
    bmod = Bpm3.numerator % p * pow(Bpm3.denominator % p, -1, p) % p
    law = (-1)**((p+1)//2) * bmod % p * pow(36, -1, p) % p
    rows.append((p, T3, E, r, law))
log(f"  sigma == 0 (mod p^2) for all 5 <= p < 300: {'PASS' if ok2 else 'FAIL'}")
okB3 = all(T3 == law for _, T3, _, _, law in rows)
log(f"  third-order Bernoulli law sigma/p^2 == (-1)^((p+1)/2) B_(p-3)/36 (mod p), 5<=p<300: "
    f"{'PASS' if okB3 else 'FAIL'} ({len(rows)} primes)  [mod-p^3 reading of Sun Conj. 5.1 + Wolstenholme refinement]")
log("  third-order invariant T3 := sigma/p^2 mod p vs Euler number E_(p-3):")
log("  p, T3, E_(p-3), T3/E: " + str([(p, t, e, r) for p, t, e, r, _ in rows[:10]]))
from collections import Counter
c1 = Counter(); c3 = Counter()
for p, T3, E, r, _ in rows:
    if r is None: continue
    found = None
    for uu in range(-8, 9):
        for vv in range(1, 9):
            if vv % p == 0: continue
            if uu % vv == 0 and vv > 1: continue
            if (uu * pow(vv, -1, p)) % p == r:
                found = f"{uu}/{vv}"; break
        if found: break
    (c1 if p % 4 == 1 else c3)[found] += 1
log(f"  T3/E as small rational, p==1(4): {dict(c1)}")
log(f"  T3/E as small rational, p==3(4): {dict(c3)}")

# ---- [C] proof sanity checks
log(); log("[C] PROOF INGREDIENTS")
okc = True
for p in [11, 13, 29, 37]:
    m = (p-1)//2
    for k in range(m):
        if comb(2*k, k) % p != pow(-4, k, p) * comb(m, k) % p: okc = False
log(f"  C(2k,k) == (-4)^k binom(m,k) (mod p), k < m: {'PASS' if okc else 'FAIL'}")
okl = True
for p in [q for q in sieve(500) if q >= 5]:
    m = (p-1)//2
    H = sum(pow(j, -1, p) for j in range(1, m+1)) % p
    q2 = (pow(2, p-1, p*p) - 1)//p % p
    if H != (-2*q2) % p: okl = False
log(f"  Lerch: H_((p-1)/2) == -2 q_p(2) (mod p): {'PASS' if okl else 'FAIL'}")
okI = True
for m in range(1, 61):
    L = sum(Fraction(comb(m, j)*(-1)**j, 2*j+1) for j in range(m+1))
    if L != Fraction(4**m * math.factorial(m)**2, math.factorial(2*m+1)):
        okI = False
log(f"  L_m = sum binom(m,j)(-1)^j/(2j+1) = 4^m (m!)^2/(2m+1)!, m<=60: {'PASS' if okI else 'FAIL'}")
okB = True
for m in range(1, 61):
    y = Fraction(-1, 4)
    B = sum(comb(m, k)*y**k/(k+m+1) for k in range(m+1))
    A = sum(comb(m, k)*y**k/(2*k+1) for k in range(m+1))
    L = sum(Fraction(comb(m, j)*(-1)**j, 2*j+1) for j in range(m+1))
    def F(s):
        return sum(Fraction(comb(m, j)*(-1)**j) * s**(2*j+1) / (2*j+1) for j in range(m+1))
    if A + B != 2*L: okB = False
    if A != 2*(F(Fraction(1, 2)) - F(Fraction(0))): okB = False
    if B != 2*(F(Fraction(1)) - F(Fraction(1, 2))): okB = False
    if L != F(Fraction(1)) - F(Fraction(0)): okB = False
log(f"  key identity A_m + B_m = 2 L_m over Q, via formal-antiderivative bookkeeping, m<=60: {'PASS' if okB else 'FAIL'}")

log(); log("[D] BLIND-RANGE AND REVIVAL REFINEMENTS")
okU = True
for p in [q for q in sieve(80) if q >= 5]:
    m = (p-1)//2
    Us = sum(Fraction(comb(2*k, k), (2*k+1)*16**k) for k in range(m+1, p))
    E = euler_mod(p, p-3)[p-3]
    lhs = Us.numerator * pow(Us.denominator, -1, p*p) % (p*p)
    rhs = p*E % (p*p) * pow(3, -1, p*p) % (p*p)
    if lhs != rhs: okU = False
log(f"  blind-range sum == p*E_(p-3)/3 (mod p^2), 5<=p<80: {'PASS' if okU else 'FAIL'}  [known: van Hamme-Sun family]")
okR = True
for p in [5, 7, 11, 13, 29, 37]:
    v = Fraction(2*16**p, (2*p+1)*comb(2*p, p)**2)
    lhs = v.numerator * pow(v.denominator, -1, p*p) % (p*p)
    q2 = (pow(2, p-1, p*p) - 1)//p % p
    if lhs != (8 + 16*p*(2*q2 - 1)) % (p*p): okR = False
log(f"  first revival v_p == 8 + 16p(2q_p(2)-1) (mod p^2): {'PASS' if okR else 'FAIL'}  [via Wolstenholme]")

import os
with open(os.path.join(os.path.dirname(os.path.abspath(__file__)), "results_pi2.txt"), "w") as f:
    f.write("\n".join(OUT) + "\n")
