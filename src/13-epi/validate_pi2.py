"""Follow-up: quarter-wall two-squares invariant, arcsin supercongruence, proof sanity checks.

Package form (2026-09): the script as written, its PASS/FAIL lines turned into registry predicates
(families pi2.A1-A2, pi2.B1-B2, pi2.C1-C4, pi2.D1-D2). Exact arithmetic only: integers and fractions.Fraction.
"""
import math
from fractions import Fraction
from math import comb
from epicommon import chk, family, flush

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

def run():
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
        chk(f"p={p}: C(2t,t) == 2a* (mod p)", C == (2*astar) % p, "pi2", "A1")
        kw = pow(16, t, p) * pow(t % p, -1, p) % p * pow(C*C % p, -1, p) % p
        if kw != (-pow(a*a % p, -1, p)) % p or kw != pow(b*b % p, -1, p) % p:
            ok_w = False; log(f"  wall formula fails at p={p}")
        chk(f"p={p}: [w_t] == -(a^2)^-1 == (b^2)^-1 (mod p)", kw == (-pow(a*a % p, -1, p)) % p == pow(b*b % p, -1, p) % p, "pi2", "A2")
        cnt += 1
    log(f"  Gauss congruence C(2t,t) == 2a* (mod p): {'PASS' if ok_g else 'FAIL'} ({cnt} primes)")
    log(f"  k(w_t) == -(a^2)^(-1) == (b^2)^(-1) (mod p): {'PASS' if ok_w else 'FAIL'}")
    p = 13; a, b = two_squares(13)
    log(f"  example p=13 = {a}^2+{b}^2: k(w_3) = {pow(16,3,13)*pow(3,-1,13)*pow(pow(comb(6,3),2,13),-1,13)%13} = -(9)^(-1) = 10")
    chk("211 primes p == 1 (mod 4) below 3000", cnt == 211, "pi2", "A1")
    chk("p=13 = 3^2 + 2^2: [w_3] = 10 = -(9)^-1", (a, b) == (3, 2) and pow(16,3,13)*pow(3,-1,13)*pow(pow(comb(6,3),2,13),-1,13) % 13 == 10 == (-pow(9, -1, 13)) % 13, "pi2", "A2")

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
        chk(f"p={p}: sigma_p == 0 (mod p^2)", num % (p*p) == 0 and den % p != 0, "pi2", "B1")
        T3 = (num//(p*p)) % p * pow(den % p, -1, p) % p
        Bpm3 = BERN[p-3]
        bmod = Bpm3.numerator % p * pow(Bpm3.denominator % p, -1, p) % p
        law = (-1)**((p+1)//2) * bmod % p * pow(36, -1, p) % p
        rows.append((p, T3, law))
        chk(f"p={p}: sigma_p/p^2 == (-1)^((p+1)/2) B_(p-3)/36 (mod p)", T3 == law, "pi2", "B2")
    log(f"  sigma == 0 (mod p^2) for all 5 <= p < 300: {'PASS' if ok2 else 'FAIL'}")
    okB3 = all(T3 == law for _, T3, law in rows)
    log(f"  third-order Bernoulli law sigma/p^2 == (-1)^((p+1)/2) B_(p-3)/36 (mod p), 5<=p<300: "
        f"{'PASS' if okB3 else 'FAIL'} ({len(rows)} primes)  [mod-p^3 reading of Sun Conj. 5.1 + Wolstenholme refinement]")
    log("  p, sigma/p^2 mod p, law: " + str([(p, t, l) for p, t, l in rows[:8]]))
    chk("sixty primes 5 <= p < 300", len(rows) == 60, "pi2", "B2")

    # ---- [C] proof sanity checks
    log(); log("[C] PROOF INGREDIENTS")
    okc = True
    for p in [11, 13, 29, 37]:
        m = (p-1)//2
        for k in range(m):
            if comb(2*k, k) % p != pow(-4, k, p) * comb(m, k) % p: okc = False
    log(f"  C(2k,k) == (-4)^k binom(m,k) (mod p), k < m: {'PASS' if okc else 'FAIL'}")
    chk("C(2k,k) == (-4)^k C(m,k) (mod p) for k < m, p in {11, 13, 29, 37}", okc, "pi2", "C1")
    okl = True
    for p in [q for q in sieve(500) if q >= 5]:
        m = (p-1)//2
        H = sum(pow(j, -1, p) for j in range(1, m+1)) % p
        q2 = (pow(2, p-1, p*p) - 1)//p % p
        if H != (-2*q2) % p: okl = False
    log(f"  Lerch: H_((p-1)/2) == -2 q_p(2) (mod p): {'PASS' if okl else 'FAIL'}")
    chk("Lerch H_((p-1)/2) == -2 q_p(2) (mod p) for 5 <= p < 500", okl, "pi2", "C2")
    okI = True
    for m in range(1, 61):
        L = sum(Fraction(comb(m, j)*(-1)**j, 2*j+1) for j in range(m+1))
        if L != Fraction(4**m * math.factorial(m)**2, math.factorial(2*m+1)): okI = False
    log(f"  L_m = sum binom(m,j)(-1)^j/(2j+1) = 4^m (m!)^2/(2m+1)!, m<=60: {'PASS' if okI else 'FAIL'}")
    chk("L_m = 4^m (m!)^2/(2m+1)! over Q for m <= 60", okI, "pi2", "C3")
    okB = True
    for m in range(1, 61):
        y = Fraction(-1, 4)
        B = sum(comb(m, k)*y**k/(k+m+1) for k in range(m+1))
        A = sum(comb(m, k)*y**k/(2*k+1) for k in range(m+1))
        L = sum(Fraction(comb(m, j)*(-1)**j, 2*j+1) for j in range(m+1))
        # finite proof route (round-01): F = formal antiderivative of expanded (1-s^2)^m;
        # A = 2(F(1/2)-F(0)), B = 2(F(1)-F(1/2)), 2L = 2(F(1)-F(0)) -- coefficient bookkeeping only
        def F(s):
            return sum(Fraction(comb(m, j)*(-1)**j) * s**(2*j+1) / (2*j+1) for j in range(m+1))
        if A + B != 2*L: okB = False
        if A != 2*(F(Fraction(1, 2)) - F(Fraction(0))): okB = False
        if B != 2*(F(Fraction(1)) - F(Fraction(1, 2))): okB = False
        if L != F(Fraction(1)) - F(Fraction(0)): okB = False
    log(f"  key identity A_m + B_m = 2 L_m over Q, via formal-antiderivative bookkeeping, m<=60: {'PASS' if okB else 'FAIL'}")
    chk("A_m + B_m = 2 L_m with A = 2(F(1/2)-F(0)), B = 2(F(1)-F(1/2)), L = F(1)-F(0) for m <= 60", okB, "pi2", "C4")

    # ---- [D] blind-range Euler congruence and refined revival residue
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
    chk("blind-range sum == p E_(p-3)/3 (mod p^2) for 5 <= p < 80", okU, "pi2", "D1")
    okR = True
    for p in [5, 7, 11, 13, 29, 37]:
        v = Fraction(2*16**p, (2*p+1)*comb(2*p, p)**2)
        lhs = v.numerator * pow(v.denominator, -1, p*p) % (p*p)
        q2 = (pow(2, p-1, p*p) - 1)//p % p
        if lhs != (8 + 16*p*(2*q2 - 1)) % (p*p): okR = False
    log(f"  first revival v_p == 8 + 16p(2q_p(2)-1) (mod p^2): {'PASS' if okR else 'FAIL'}  [via Wolstenholme]")
    chk("v_p == 8 + 16p(2 q_p(2) - 1) (mod p^2) for p in {5, 7, 11, 13, 29, 37}", okR, "pi2", "D2")


    flush("pi2", order=["A1", "A2", "B1", "B2", "C1", "C2", "C3", "C4", "D1", "D2"])

if __name__ == "__main__":
    import epicommon
    run(); epicommon.summary(write=False)
