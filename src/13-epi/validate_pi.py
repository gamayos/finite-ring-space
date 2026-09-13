"""FRC emergence of pi: verification suite.
Sections:
  [1] Radial chains: Wallis central-binomial pair (v_n, w_n) enclosure; Machin readout.
  [2] Wall arithmetic: legibility window [1,2t], empty blind set, hard wall, residue -2.
  [3] Second order: Morley congruence, W mod p^2 = Fermat-quotient formula, pi-Wieferich search.
  [4] Lucas revivals and digitwise self-similarity.
  [5] arcsin(1/2) chain: wall vanishing T(p) == 0 test and second-order pattern hunt.
  [6] Angular exactness and Gauss-sum saturation.
"""
import math
from fractions import Fraction
from math import comb, gcd

OUT = []
def log(s=""):
    print(s); OUT.append(str(s))

def sieve(N):
    c = bytearray(N + 1)
    for i in range(2, int(N**0.5) + 1):
        if not c[i]: c[i*i::i] = b'\x01' * len(c[i*i::i])
    return [i for i in range(3, N + 1) if not c[i]]

# reference pi to ~420 digits via exact Machin
def pi_fraction(N=320):
    def arctan_inv(x, N):
        s = Fraction(0)
        for k in range(N + 1):
            s += Fraction((-1)**k, (2*k + 1) * x**(2*k + 1))
        return s
    return 16*arctan_inv(5, N) - 4*arctan_inv(239, N)
PI = pi_fraction(320)

# =========================================================
log("="*72); log("[1] RADIAL CHAINS")
log("="*72)
# Wallis pair
def vw(n):
    C = comb(2*n, n)
    w = Fraction(16**n, n * C * C)
    v = Fraction(2 * 16**n, (2*n + 1) * C * C)
    return v, w
encl = True; ident = True; mono = True
prev_v, prev_w = vw(1)
for n in range(1, 301):
    v, w = vw(n)
    if not (v < PI < w): encl = False
    if w - v != w / (2*n + 1): ident = False
    if n > 1 and not (v > prev_v and w < prev_w): mono = False
    if n > 1: prev_v, prev_w = v, w
log(f"(a) Wallis pair: v_n < pi < w_n for n=1..300: {'PASS' if encl else 'FAIL'}; "
    f"exact width identity w-v=w/(2n+1): {'PASS' if ident else 'FAIL'}; strict monotonicity: {'PASS' if mono else 'FAIL'}")
v50, w50 = vw(50)
log(f"    example n=50: width = {float(w50-v50):.4e} ~ pi/101 = {math.pi/101:.4e}  (O(1/n) rate)")
# p=13 showcase residue line (round-01: anchors the manuscript's displayed line)
p13_line = [pow(16, n, 13) * pow(n * pow(math.comb(2*n, n), 2, 13) % 13, -1, 13) % 13 for n in range(1, 7)]
log(f"    p=13 residue line [w_n]_13, n=1..6: {p13_line} " + ("PASS" if p13_line == [4, 5, 10, 9, 6, 11] else "FAIL"))

# Machin chain: M_N with both arctans truncated at N
def machin(N):
    def S(x, N): return sum(Fraction((-1)**k, (2*k+1)*x**(2*k+1)) for k in range(N+1))
    return 16*S(5, N) - 4*S(239, N)
n_double = None
for N in range(2, 25):
    if float(machin(N)) == math.pi:
        n_double = N; break
log(f"(b) Machin chain: minimal N with float(M_N) == IEEE-double(pi): N = {n_double}")
err_bound_ok = all(abs(machin(N) - PI) < Fraction(17, (2*N+3)*5**(2*N+3)) for N in range(2, 40))
log(f"    error bound |M_N - pi| < 17/((2N+3) 5^(2N+3)) for N=2..39: {'PASS' if err_bound_ok else 'FAIL'}")
N100 = None
for N in range(60, 90):
    if abs(machin(N) - PI) < Fraction(1, 10**101): N100 = N; break
log(f"    100-decimal-digit determination at N = {N100}")
# enclosure via alternating pairing
def S_pair(x, N):  # (lower, upper) alternating bounds for arctan(1/x)
    s = Fraction(0); terms = [Fraction((-1)**k, (2*k+1)*x**(2*k+1)) for k in range(N+2)]
    partial = []
    run = Fraction(0)
    for t in terms:
        run += t; partial.append(run)
    lo = min(partial[N], partial[N+1]); hi = max(partial[N], partial[N+1])
    return lo, hi
l5, u5 = S_pair(5, 12); l239, u239 = S_pair(239, 4)
lo, hi = 16*l5 - 4*u239, 16*u5 - 4*l239
log(f"    fQ-native certified enclosure at (12,4) terms: pi in ({float(lo):.16f}, {float(hi):.16f}): {'PASS' if lo < PI < hi else 'FAIL'}")

# feasibility table
log("(c) precision-cost (terms n for 2^-k):")
for k in (24, 53, 333):
    nL = 2**k            # Leibniz/Wallis ~ error 1/n
    nM = math.ceil((k*math.log(2)/math.log(5) - 3)/2)   # Machin ~ 5^{-2N}
    nA = math.ceil(k/2)  # arcsin(1/2) ~ 4^{-n}
    log(f"    k={k:3d}: Wallis/Leibniz ~ {nL:.1e}   Machin ~ {nM}   arcsin(1/2) ~ {nA}   (e-chain reference: {[11,18,70][(24,53,333).index(k)]})")

# =========================================================
log(); log("="*72); log("[2] WALL ARITHMETIC (mod p)")
log("="*72)
def Cmod_track(p, nmax):
    """return list over n=1..nmax of (vp, unit) for C(2n,n): p-adic valuation and unit part mod p"""
    res = []
    e, u = 0, 1  # C(2,1)=2 handled in loop start from n=0: C(0,0)=1
    # iterate C(2(n+1),n+1) = C(2n,n)*2*(2n+1)/(n+1)
    cur_e, cur_u = 0, 1
    for n in range(0, nmax):
        num = 2*(2*n + 1); den = n + 1
        while num % p == 0: num //= p; cur_e += 1
        while den % p == 0: den //= p; cur_e -= 1
        cur_u = cur_u * (num % p) % p
        cur_u = cur_u * pow(den % p, -1, p) % p
        res.append((cur_e, cur_u))  # this is C(2(n+1), n+1)
    return res

samples = [5, 13, 29, 101, 257, 1009, 10007]
log(f"{'p':>6} | window [1,2t] all legible | (2t,p) all blind | k(w_wall) | v blind at wall (den=p)")
for p in samples:
    t2 = (p - 1)//2
    trk = Cmod_track(p, p - 1)
    legible = all(trk[n-1][0] == 0 for n in range(1, t2 + 1))
    blind   = all(trk[n-1][0] >= 1 for n in range(t2 + 1, p))
    e_, u_ = trk[t2 - 1]  # C(2*2t choose 2t) = C(p-1, (p-1)/2)
    wall = pow(16, t2, p) * pow(t2 % p, -1, p) * pow(u_*u_ % p, -1, p) % p if e_ == 0 else None
    log(f"{p:6d} |          {'PASS' if legible else 'FAIL'}          |      {'PASS' if blind else 'FAIL'}      |   {(wall - p) if wall and wall > p//2 else wall}      |  2*2t+1 = {2*t2+1} = p: {'YES' if 2*t2+1==p else 'NO'}")

# also p == 3 mod 4
p3ok = True
for p in [7, 23, 1031]:
    m = (p-1)//2
    C = 1
    for n in range(m): C = C * 2*(2*n+1) % p * pow(n+1, -1, p) % p
    wall = pow(16, m, p) * pow(m, -1, p) * pow(C*C % p, -1, p) % p
    if wall != p - 2: p3ok = False
log(f"universal wall residue -2 also for p == 3 (mod 4) [7, 23, 1031]: {'PASS' if p3ok else 'FAIL'}")

# =========================================================
log(); log("="*72); log("[3] SECOND ORDER: Morley, Fermat quotient, pi-Wieferich")
log("="*72)
morley_ok = True; formula_ok = True
rows = []
for p in [13, 29, 37, 41, 53, 101]:
    m = (p-1)//2
    C = comb(p-1, m)
    # Morley mod p^3
    if ((-1)**m * C - pow(4, p-1, p**3)) % p**3 != 0: morley_ok = False
    W = Fraction(16**m, m * C * C)
    k2 = W.numerator * pow(W.denominator, -1, p*p) % (p*p)
    q4 = (pow(4, p-1, p*p) - 1)//p % p
    pred = (-2 + 2*p*(q4 - 1)) % (p*p)
    if k2 != pred: formula_ok = False
    rows.append((p, (k2 - p*p) , q4))
log(f"Morley: (-1)^m C(p-1,m) == 4^(p-1) (mod p^3) for p in [13..101]: {'PASS' if morley_ok else 'FAIL'}")
log(f"Second-order wall formula W == -2 + 2p(q_p(4)-1) (mod p^2): {'PASS' if formula_ok else 'FAIL'}")
log(f"  (p, W mod p^2 as negative lift, q_p(4) mod p): {rows[:4]}")

# pi-Wieferich search: 4^(p-1) == 1 + p (mod p^2)
hits = []
LIM = 1000000
for p in sieve(LIM):
    if pow(4, p-1, p*p) == (1 + p) % (p*p):
        hits.append(p)
log(f"pi-Wieferich primes (W == -2 mod p^2), p < 10^6: {hits if hits else 'none'}  "
    f"(heuristic expectation ~ sum 1/p ~ {sum(1/q for q in sieve(LIM)):.2f} ... over the range)")

# distribution of q_p(4) mod p (uniformity check via normalized mean/var on p<20000)
vals = []
for p in sieve(20000):
    q4 = (pow(4, p-1, p*p) - 1)//p % p
    vals.append(q4/p)
mean = sum(vals)/len(vals); var = sum((x-mean)**2 for x in vals)/len(vals)
log(f"q_p(4)/p over p<20000: mean {mean:.4f} (uniform: 0.5), variance {var:.4f} (uniform: 0.0833)")

# =========================================================
log(); log("="*72); log("[4] LUCAS REVIVALS AND SELF-SIMILARITY")
log("="*72)
p = 13
Cv = comb(26, 13) % p
vres = 2 * pow(16, 13, p) * pow((27 % p) * Cv * Cv % p, -1, p) % p
log(f"p=13: C(26,13) mod 13 = {Cv} = C(2,1)*C(0,0); k(v_13) = {vres} (predicted universal 8: {'PASS' if vres==8 else 'FAIL'})")
C28 = comb(28, 14) % 13
log(f"p=13, n=14=(1,1)_13: C(28,14) mod 13 = {C28} = C(2,1)^2 = 4 digitwise (Lucas): {'PASS' if C28==4 else 'FAIL'}")
# density of legible n in [p, p^2): digits all <= (p-1)/2 and n not = 0 mod p etc.
p = 13; cnt = 0
for n in range(p, p*p):
    a, b = divmod(n, p)
    if a <= 6 and b <= 6 and n % p != 0 and comb(2*n, n) % p != 0: cnt += 1
log(f"p=13: legible w-scales in [13,169): {cnt}/156 = {cnt/156:.3f} (prediction ((2t+1)/p)^2-ish = {(7/13)**2:.3f}, minus n==0 mod p column)")

# =========================================================
log(); log("="*72); log("[5] ARCSIN(1/2) CHAIN WALL: T(p) and second order")
log("="*72)
def T_mod(p):
    m = (p-1)//2
    s = 0; C = 1  # C(0,0)
    inv16 = pow(16, -1, p)
    pw = 1
    for k in range(m):
        if k > 0:
            C = C * 2*(2*k-1) % p * pow(k, -1, p) % p
            pw = pw * inv16 % p
        s = (s + C * pw % p * pow(2*k+1, -1, p)) % p
    return s
zero_all = True; tested = 0
for p in sieve(3000):
    if p == 3:
        if T_mod(p) == 0: zero_all = False; log("  T(3) == 0 (expected nonzero: sole exception)!")
        continue
    if T_mod(p) != 0: zero_all = False; log(f"  T({p}) != 0 !")
    tested += 1
log(f"T(p) := sum_(k=0)^(m-1) C(2k,k)/((2k+1)16^k) == 0 (mod p) for all odd primes 5<=p<3000 (p=3 is the sole exception, T(3)={T_mod(3)}): {'PASS' if zero_all else 'FAIL'} ({tested} primes)")

# second order: sigma/p mod p, pattern hunt
def euler_numbers_mod(p, upto):
    E = [0]*(upto+1); E[0] = 1
    for n in range(1, upto//2 + 1):
        s = 0
        for j in range(n):
            s += comb(2*n, 2*j) * E[2*j]
        E[2*n] = (-s) % p
    return E
def two_squares(p):
    # p = a^2 + b^2, p == 1 mod 4; a odd normalized a == 1 mod 4? return (a,b) a odd
    for a in range(1, int(p**0.5)+1):
        b2 = p - a*a
        b = int(b2**0.5)
        if b*b == b2: 
            if a % 2 == 1: return a, b
            return b, a
    return None
log("second-order invariant T2(p) := (sigma/p) mod p, sigma the exact rational partial sum:")
log(f"{'p':>4} | T2 | E_(p-3) | q_p(2) | a (p=a^2+b^2) | T2/E | T2/q2")
pat = []
for p in [q for q in sieve(200) if q > 3]:
    m = (p-1)//2
    sigma = sum(Fraction(comb(2*k,k), (2*k+1)*16**k) for k in range(m))
    num, den = sigma.numerator, sigma.denominator
    assert num % p == 0 and den % p != 0
    T2 = (num//p) * pow(den, -1, p) % p
    E = euler_numbers_mod(p, p-3)[p-3]
    q2 = (pow(2, p-1, p*p) - 1)//p % p
    ts = two_squares(p) if p % 4 == 1 else None
    rE = T2 * pow(E, -1, p) % p if E else None
    rq = T2 * pow(q2, -1, p) % p if q2 else None
    pat.append((p, T2, E, q2, ts, rE, rq))
    log(f"{p:4d} | {T2:3d} | {E:5d} | {q2:4d} | {str(ts):>10} | {str(rE):>4} | {str(rq):>4}")

# also Leibniz wall U(p) and ratio to E_(p-3)
log()
log("Leibniz wall U(p) := sum_(k=0)^(m-1) (-1)^k/(2k+1) mod p, ratio to E_(p-3):")
for p in [q for q in sieve(120) if q > 3]:
    m = (p-1)//2
    U = sum((-1)**k * pow(2*k+1, -1, p) for k in range(m)) % p
    E = euler_numbers_mod(p, p-3)[p-3]
    r = U * pow(E, -1, p) % p if E else None
    log(f"  p={p:3d}: U={U:3d}  E_(p-3)={E:4d}  U/E={r}")

# =========================================================
log(); log("="*72); log("[6] ANGULAR EXACTNESS AND GAUSS SUM")
log("="*72)
for p in [13, 101, 1009, 10007]:
    re = sum(math.cos(2*math.pi*(x*x % p)/p) for x in range(p))
    im = sum(math.sin(2*math.pi*(x*x % p)/p) for x in range(p))
    log(f"  p={p:6d}: Gauss sum = {re:.6f} + {im:.2e} i;  sqrt(p) = {math.sqrt(p):.6f}  (class: +sqrt(p) if p==1 mod 4, +i*sqrt(p) if p==3 mod 4)")
log("angle of -1 on the multiplicative circle: 2pi * (2t)/(4t) = pi exactly, every frame, both chiralities.")

import os
with open(os.path.join(os.path.dirname(os.path.abspath(__file__)), "results_pi.txt"), "w") as f:
    f.write("\n".join(OUT) + "\n")
log(); log("results written to results_pi.txt")
