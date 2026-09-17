#!/usr/bin/env python3
"""The golden ratio against the (13,233) constant web.

Grades the four clauses of the public statement -- h and hbar are 89 and 144 (the paper's A4: hbar = 144, h = 89; labels corrected 2026-09-14, T30),
Om = 233 = 13^2 + 8^2, 144 + 89 = 233, and 13/89/144/233 are Fibonacci -- into
what is forced by admissibility and what is a property of the minimal instance.
Then tests whether phi has any load-bearing role, and whether phi-registrability
is a useful filter for lab scale targets.

Exact integers throughout: deterministic Miller-Rabin, Tonelli-Shanks, exact
two-square search. No floats in any asserted quantity; the two density
comparisons are labelled [comparison] and assert nothing.
"""

_W = (2, 3, 5, 7, 11, 13, 17, 19, 23, 29, 31, 37)


def is_prime(n):
    if n < 2:
        return False
    for q in _W:
        if n % q == 0:
            return n == q
    d, r = n - 1, 0
    while d % 2 == 0:
        d //= 2
        r += 1
    for a in _W:
        x = pow(a, d, n)
        if x in (1, n - 1):
            continue
        for _ in range(r - 1):
            x = x * x % n
            if x == n - 1:
                break
        else:
            return False
    return True


def prime_factors(n):
    f, d = [], 2
    while d * d <= n:
        if n % d == 0:
            f.append(d)
            while n % d == 0:
                n //= d
        d += 1 if d == 2 else 2
    if n > 1:
        f.append(n)
    return f


def two_squares(n):
    """Exact Fermat decomposition n = a^2 + b^2 with a >= b, for prime n == 1 (mod 4)."""
    a = 1
    while a * a <= n:
        m, lo, hi = n - a * a, 0, n
        while lo <= hi:                      # exact integer square root, no floats
            mid = (lo + hi) // 2
            if mid * mid == m:
                if mid <= a:
                    return (a, mid)
                break
            if mid * mid < m:
                lo = mid + 1
            else:
                hi = mid - 1
        a += 1
    return None


def sqrt_mod(a, p):
    a %= p
    if a == 0:
        return 0
    if pow(a, (p - 1) // 2, p) != 1:
        return None
    if p % 4 == 3:
        return pow(a, (p + 1) // 4, p)
    q, s = p - 1, 0
    while q % 2 == 0:
        q //= 2
        s += 1
    z = 2
    while pow(z, (p - 1) // 2, p) != p - 1:
        z += 1
    m, c, t, r = s, pow(z, q, p), pow(a, q, p), pow(a, (q + 1) // 2, p)
    while t != 1:
        i, t2 = 0, t
        while t2 != 1:
            t2 = t2 * t2 % p
            i += 1
        b = pow(c, 1 << (m - i - 1), p)
        m, c = i, b * b % p
        t, r = t * c % p, r * b % p
    return r


def golden(N):
    """The phi-pair of F_N, or None when 5 is a non-residue."""
    r = sqrt_mod(5, N)
    if r is None:
        return None
    inv2 = pow(2, -1, N)
    return ((1 + r) * inv2 % N, (1 - r) * inv2 % N)


def carrier_admissible(Om):
    if (Om - 1) % 4:
        return False
    S = (Om - 1) // 4
    return S % 4 == 2 and S % 3 == 1 and is_prime(Om)


def pisano(p):
    a, b, n = 0, 1, 0
    while True:
        a, b = b, (a + b) % p
        n += 1
        if (a, b) == (0, 1):
            return n


INSTANCES = ((13, 233), (29, 857), (173, 30089))
LAB = 2408561

# =====================================================================
# P1  hbar + h = Om is forced: the roots of -1 are x and Om-x.
# =====================================================================
for _, Om in INSTANCES + ((None, LAB),):
    r = sqrt_mod(Om - 1, Om)
    assert (r * r) % Om == Om - 1 and ((Om - r) ** 2) % Om == Om - 1
    assert r + (Om - r) == Om
assert (89 * 89) % 233 == 232 and (144 * 144) % 233 == 232 and 89 + 144 == 233
print("P1 FORCED: the two roots of -1 are x and Om-x, so hbar + h = Om at every "
      "admissible Carrier. 144+89=233 is a definition, not a Fibonacci fact.")

# =====================================================================
# P2  Om = a^2 + b^2 is forced: Fermat, since admissibility gives Om == 1 (mod 4).
# =====================================================================
legs = {}
for _, Om in INSTANCES + ((None, LAB),):
    assert Om % 4 == 1
    a, b = two_squares(Om)
    assert a * a + b * b == Om
    legs[Om] = (a, b)
assert legs[233] == (13, 8)
print("P2 FORCED: admissibility requires Om == 1 (mod 4), so every Carrier has a "
      f"unique two-square form. 233 = 13^2+8^2, 857 = {legs[857][0]}^2+{legs[857][1]}^2, "
      f"30089 = {legs[30089][0]}^2+{legs[30089][1]}^2.")

# =====================================================================
# P3  THE THEOREM INSIDE: hbar and h are the Gaussian leg ratios.
# =====================================================================
for Om, (a, b) in legs.items():
    ab, ba = a * pow(b, -1, Om) % Om, b * pow(a, -1, Om) % Om
    assert (ab * ab) % Om == Om - 1, "a/b is a square root of -1"
    assert (ba * ba) % Om == Om - 1
    assert ab + ba == Om and (ab * ba) % Om == 1
assert 13 * pow(8, -1, 233) % 233 == 89
assert 8 * pow(13, -1, 233) % 233 == 144
print("P3 THEOREM: for Om = a^2+b^2, (a/b)^2 == -1. So {hbar,h} ARE the two Gaussian "
      "leg ratios. At (13,233): h = 13/8 = 89, hbar = 8/13 = 144 (the paper's A4). Holds at all four.")

# P3a  the Subject as the larger leg: a two-instance regularity, not a law.
same = [(p, Om, legs[Om][0] == p) for p, Om in INSTANCES]
assert [s[2] for s in same] == [True, True, False]
print("P3a REGULARITY, NOT LAW: p is the larger leg at (13,233) and (29,857) "
      "(Om - p^2 a perfect square: 64, 16) and NOT at (173,30089) "
      f"(30089 - 173^2 = 160, no square). Record with O5's caution.")

# =====================================================================
# P4  The Fibonacci layer: an instance property that cannot recur.
# =====================================================================
F = [0, 1]
while len(F) < 90:
    F.append(F[-1] + F[-2])
assert F[13] == 233 and F[7] == 13 and F[6] == 8
assert F[6] ** 2 + F[7] ** 2 == F[13], "F_(2n+1) = F_n^2 + F_(n+1)^2"
fib_adm = [(i, F[i]) for i in range(3, 90)
           if F[i] > 5 and is_prime(F[i]) and F[i] % 48 == 41]
assert fib_adm == [(11, 89), (13, 233), (83, 99194853094755497)], fib_adm
# F_83's legs are consecutive Fibonacci by the same identity, so h there is
# again a phi convergent -- but the larger leg F_42 is even, so no Subject sits on it.
a83, b83 = F[42], F[41]
assert a83 * a83 + b83 * b83 == F[83]
assert not is_prime(a83) and a83 % 2 == 0
print("P4 RECURS ONCE, OUT OF REACH: 233 = F_13, and F_(2n+1) = F_n^2+F_(n+1)^2 forces "
      "consecutive-Fibonacci legs, hence h = F_7/F_6 = 13/8, a phi convergent (hbar = 8/13). "
      "Among ALL Fibonacci primes through F_89 exactly three satisfy Om == 41 (mod 48): "
      "F_11=89 (too small -- p^2 < 89 leaves only the degenerate p=5), F_13=233, and "
      f"F_83={F[83]} (~9.9e16, legs F_42/F_41, larger leg even so no Subject sits on it). "
      "233 is the only Fibonacci-prime Carrier within reach that hosts a Subject.")

# =====================================================================
# P5  Is phi registrable? Only when Om == +-1 (mod 5).
# =====================================================================
reg = {}
for Om in (233, 857, 30089, LAB):
    g = golden(Om)
    reg[Om] = g is not None
    if g:
        a, b = g
        assert (a * a - a - 1) % Om == 0 and (b * b - b - 1) % Om == 0
        assert (a + b) % Om == 1 and (a * b) % Om == Om - 1
assert reg == {233: False, 857: False, 30089: True, LAB: True}
print("P5 phi is NOT registrable at 233 (Om==3 mod 5) or 857 (Om==2 mod 5); it IS at "
      "30089 (==4) and at the lab Om=2,408,561 (==1). The instance that generated the "
      "Fibonacci observation is one where phi itself is not a residue.")

# =====================================================================
# P6  The native role: phi is the additive/multiplicative exchange point.
# =====================================================================
for Om in (30089, LAB):
    phi, phip = golden(Om)
    assert (phi * phi) % Om == (phi + 1) % Om, "one multiplicative step = one additive step"
print("P6 ROLE: phi is the unique pair with x*x = x+1 -- one multiplicative step equals "
      "one additive step. i-pair {i,-i}: sum 0, product 1, anchored on the origin. "
      "phi-pair: sum 1, product -1, anchored on the unit.")

# =====================================================================
# P7  phi is not canonically the drive: primitive-root rate is unremarkable.
# =====================================================================
adm, Om = [], 41
while len(adm) < 200:
    if carrier_admissible(Om):
        adm.append(Om)
    Om += 48
phi_reg = [O for O in adm if O % 5 in (1, 4)]
prim = 0
for O in phi_reg:
    phi = golden(O)[0]
    if phi in (0, 1):
        continue
    if all(pow(phi, (O - 1) // q, O) != 1 for q in prime_factors(O - 1)):
        prim += 1
print(f"P7 NOT THE DRIVE: phi is a primitive root in {prim} of {len(phi_reg)} "
      "phi-registrable admissible Carriers, indistinguishable from the rate for an "
      "arbitrary residue [comparison]. No forcing selects phi as the frame generator.")

# =====================================================================
# P8  phi-registrability is independent of admissibility (CRT).
# =====================================================================
assert len(phi_reg) * 2 >= len(adm) - 20 and len(phi_reg) * 2 <= len(adm) + 20
print(f"P8 INDEPENDENT: admissibility fixes Om mod 48, phi needs Om mod 5 in {{1,4}}; "
      f"gcd(48,5)=1, so by CRT they are independent. Measured {len(phi_reg)}/{len(adm)} "
      "against the CRT half. phi-registrability carries no information about the lane.")

# =====================================================================
# P9  What it does buy: where the Fibonacci recursion closes.
# =====================================================================
for Om, inreg in ((233, False), (857, False), (30089, True)):
    per = pisano(Om)
    if inreg:
        assert (Om - 1) % per == 0
    else:
        assert (2 * (Om + 1)) % per == 0 and (Om - 1) % per != 0
print("P9 THE ONE PAYOFF: phi present -> the Fibonacci recursion closes in-register "
      "(Pisano period divides Om-1: 30088 at 30089). phi absent -> it closes only in "
      "the quadratic extension (52 | 468 at 233; 1716 = 2(Om+1) at 857).")

# =====================================================================
# P10  F7 constraint (the additive window, formerly Y6): a phase-locked N-hydrogen lock needs 12N+1 prime.
# =====================================================================
hosts = [N for N in range(1, 13) if is_prime(12 * N + 1)]
blocked = [N for N in range(1, 13) if not is_prime(12 * N + 1)]
assert 2 in blocked and (12 * 2 + 1) == 25 == 5 * 5
print(f"P10 F7 CONSTRAINT (formerly Y6): kap_O = 3N gives q = 12N+1, which must be prime to carry a "
      f"shell. Registrable N in 1..12: {hosts}. Blocked: {blocked} "
      f"(N=2 gives q=25=5^2, so a two-hydrogen lock has NO shell). "
      "The additivity law lands on a shell only at those N.")

print()
print("check_phi: all checks passed.")
