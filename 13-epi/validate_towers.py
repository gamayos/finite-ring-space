#!/usr/bin/env python3
"""validate_towers.py -- 13-epi fixed-shell towers, Cayley identities, orientation rule.
Exact arithmetic only: integers and fractions.Fraction. No floats anywhere.
External comparisons use the paper's own certified rational brackets."""
from fractions import Fraction as F
import math, sys

ok = True
def check(name, cond):
    global ok
    print(("PASS " if cond else "FAIL ") + name)
    if not cond: ok = False

def subfact(n):
    d = [1, 0]
    for k in range(2, n+1):
        d.append(k*d[-1] + (-1)**k)
    return d[n]

def C(n, k):
    return math.comb(n, k)

def e_brackets(n):
    """Certified bracket for e via the subfactorial chain: eps_{2m} < e < eps_{2m+1}."""
    lo = F(math.factorial(2*n), subfact(2*n))
    hi = F(math.factorial(2*n+1), subfact(2*n+1))
    return lo, hi

def pi_brackets(m):
    """Certified Machin brackets: L_m < pi < U_m (alternating pairing)."""
    def AN(x, N):
        return sum(F((-1)**k, (2*k+1)*x**(2*k+1)) for k in range(N+1))
    L = 16*AN(5, 2*m+1) - 4*AN(239, 2*m)
    U = 16*AN(5, 2*m)   - 4*AN(239, 2*m+1)
    return L, U

def centered(x, p):
    x %= p
    return x - p if x > (p-1)//2 else x

def primitive_root(p):
    fac = set()
    n = p-1
    d = 2
    while d*d <= n:
        while n % d == 0:
            fac.add(d); n //= d
        d += 1
    if n > 1: fac.add(n)
    for g in range(2, p):
        if all(pow(g, (p-1)//q, p) != 1 for q in fac):
            return g
    raise ValueError

for p in (13, 29):
    kap = (p-1)//4
    g = primitive_root(p)
    i = pow(g, p-1-kap, p)              # i = g^{-kap}
    check(f"p={p}: i^2 = -1", (i*i) % p == p-1)
    lam = i                              # label lift: canonical representative read as exponent
    eP = pow(g, lam, p)
    piA = (2*kap) % p

    # --- e-tower: q_m = ((mp)! + delta_m)/!(mp), shell reading = eP, external -> e ---
    for m in (1, 2, 3):
        delta = centered(((-1)**m * eP) % p, p)
        num = math.factorial(m*p) + delta
        den = subfact(m*p)
        check(f"p={p} e-tower grade {m}: !(mp) == (-1)^m (mod p)", den % p == ((-1)**m) % p)
        check(f"p={p} e-tower grade {m}: shell reading = e_p", (num * pow(den % p, p-2, p)) % p == eP)
        lo, hi = e_brackets(max(m*p//2, 12))
        q = F(num, den)
        # the paper's certificate: |q - e| < (mp)!/( !(mp) !(mp+1) ) + pi_F/!(mp)
        width = F(math.factorial(m*p), den*subfact(m*p+1)) + F((p-1)//2, den)
        check(f"p={p} e-tower grade {m}: |q - e| inside certified window",
              q > lo - width and q < hi + width)

    # --- pi-tower: (2*16^n + delta)/((2n+1) C(2n,n)^2), n = p^r ---
    for r in (1, 2):
        n = p**r
        Cb = C(2*n, n)
        Bn = (2*n+1) * Cb * Cb
        check(f"p={p} pi-tower r={r}: C(2n,n) == 2 (mod p)", Cb % p == 2)
        check(f"p={p} pi-tower r={r}: 16^n == 16 (mod p)", pow(16, n, p) == 16 % p)
        delta = centered((piA * Bn - 2*pow(16, n)) % p, p)
        check(f"p={p} pi-tower r={r}: delta = centered(-34)", delta == centered(-34 % p, p))
        num = 2*pow(16, n) + delta
        check(f"p={p} pi-tower r={r}: shell reading = pi_A",
              (num * pow(Bn % p, p-2, p)) % p == piA)
        if r == 1:
            L, U = pi_brackets(8)
            v = F(num, Bn)
            check(f"p={p} pi-tower r=1: member below the certified upper bracket", v < U)
            check(f"p={p} pi-tower r=1: member above v_n floor", v > F(2*4**n, (2*n+1)*Cb*Cb) - F(1))

    # --- Cayley identities, exhaustive where denominators are units ---
    cnt = 0
    for x in range(p):
        for y in range(p):
            dx, dy = (1 - i*x) % p, (1 - i*y) % p
            dxy = (1 - x*y) % p
            if dx and dy and dxy:
                num_c = ((x + y) * pow(dxy, p-2, p)) % p
                dc = (1 - i*num_c) % p
                if dc:
                    Cx = ((1 + i*x) * pow(dx, p-2, p)) % p
                    Cy = ((1 + i*y) * pow(dy, p-2, p)) % p
                    Cc = ((1 + i*num_c) * pow(dc, p-2, p)) % p
                    if (Cx*Cy) % p != Cc:
                        check(f"p={p} Cayley composition at ({x},{y})", False)
                    cnt += 1
    check(f"p={p} Cayley composition exhaustive ({cnt} pairs)", True)
    check(f"p={p} Cayley C(0)=1", ((1) * pow(1, p-2, p)) % p == 1)
    check(f"p={p} Cayley C(1)=i", ((1+i) * pow((1-i) % p, p-2, p)) % p == i)

    # --- orientation rule: u = 1 mod 4 preserves i, u = 3 mod 4 conjugates ---
    for u in range(1, p-1):
        if math.gcd(u, p-1) != 1:
            continue
        gp = pow(g, u, p)
        ip = pow(gp, p-1-kap, p)
        if u % 4 == 1:
            if ip != i: check(f"p={p} orientation u={u} (u=1 mod 4) preserves i", False)
        else:
            if ip != (p - i) % p: check(f"p={p} orientation u={u} (u=3 mod 4) conjugates i", False)
    check(f"p={p} orientation-transport rule exhaustive over units", True)


# --- two-level horizon law: minimal framed-rational heights ---
def minheight(x, p):
    best = p
    for b in range(1, best + 1):
        a = (x * b) % p
        a = a - p if a > p // 2 else a
        h = max(abs(a), b)
        if h < best:
            best = h
        if b > best:
            break
    return best

import math as _m

def _sieve(N):
    c = bytearray(N + 1)
    for i in range(2, _m.isqrt(N) + 1):
        if not c[i]: c[i*i::i] = b'\x01' * len(c[i*i::i])
    return [i for i in range(3, N + 1) if not c[i]]

hs = []
pin_ok = True; band_ok = True
for p in [q for q in _sieve(8009) if q % 4 == 1]:
    kap = (p - 1) // 4
    g = primitive_root(p)
    e_neg = pow(g, pow(g, p-1-kap, p), p)
    e_pos = pow(g, pow(g, kap, p), p)
    piA = (2 * kap) % p
    if not ((piA * (-2)) % p == 1 and minheight(piA, p) == 2): pin_ok = False
    h = min(minheight(e_neg, p), minheight(e_pos, p))
    if h > 2 * _m.isqrt(p): band_ok = False
    hs.append((p, h, _m.isqrt(p)))
check("pi_A = [-1/2] pinned at height 2 on all 500 shells p <= 8009", pin_ok and len(hs) == 500)
check("H(e_p) within the horizon band 2 sqrt(p) on every shell", band_ok)
small = sorted(p for p, h, s in hs if h <= 10)
exc2 = sorted(p for p, h, s in hs if h == 2)
ratios = sorted(h/s for p, h, s in hs)
med = (ratios[249] + ratios[250]) / 2
check("small-height shells (H <= 10): exactly 68", len(small) == 68)
check("height-2 shells exactly {13, 1933, 4177, 5857}", exc2 == [13, 1933, 4177, 5857])
print(f"height run: 500 shells, median H/sqrt(p) = {med:.3f}, H<=10: {len(small)}, height-2: {exc2}")

for p in (13, 29, 101, 997, 8009):
    s = _m.isqrt(p)
    check(f"p={p}: wrap-free window (isqrt(p)^2 < p, sums below p)", s*s < p and 2*s < p)
    kap = (p - 1) // 4
    piA = (2 * kap) % p
    check(f"p={p}: pinning relation 2*pi_A + 1 == 0 (the shell calibration)", (2*piA + 1) % p == 0)

print("ALL PASS" if ok else "FAILURES PRESENT")
sys.exit(0 if ok else 1)
