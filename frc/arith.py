"""frc.arith — exact integer arithmetic for every ledger (base tier; ledger migration, task LM15, 5 October 2026).

Integers only: no float, no third-party import (gate G09). Each function states its range. Inside it the answer is
exact; outside it the function raises ValueError instead of guessing.

    isqrt, is_square              integer square roots (every n ≥ 0)
    is_prime                      trial division by the primes below 100, then deterministic Miller–Rabin on the first
                                  13 primes: exact for every n with a prime factor below 100 and for every n < PRIME_RANGE
    factorize, prime_factors      trial division, then Pollard–Brent rho with fixed seeds; every factor proved prime, so
                                  every prime factor must lie below PRIME_RANGE
    phi, carmichael, order        Euler's φ, Carmichael's λ, multiplicative orders, from the factorisation
    primitive_root(s)             the least primitive root, and all of them, of n = 2, 4, p^k or 2p^k
    legendre, jacobi              the Legendre symbol by Euler's criterion; the Jacobi symbol by reciprocity
    nonresidue, sqrt_mod          the least quadratic non-residue; square roots mod p by Tonelli–Shanks
    inverse, crt, valuation       modular inverses, the Chinese remainder theorem, p-adic valuations

PRIME_RANGE is 3,317,044,064,679,887,385,961,981: the first 13 primes as bases decide primality below it (Sorenson and
Webster, Math. Comp. 86 (2017) 985–1003). Every number a check of the corpus tests lies below it, the laboratory Carrier
2,408,561 included. The physical Carrier is not tested, and no function here counts towards it.
"""
from math import gcd, isqrt

PRIME_RANGE = 3317044064679887385961981
_MR_BASES = (2, 3, 5, 7, 11, 13, 17, 19, 23, 29, 31, 37, 41)
_SMALL = (2, 3, 5, 7, 11, 13, 17, 19, 23, 29, 31, 37, 41, 43, 47, 53, 59, 61, 67, 71, 73, 79, 83, 89, 97)
_TRIAL_LIMIT = 10_000                    # factorize: trial division to here, then rho


def is_square(n):
    """True iff n is a perfect square (n ≥ 0)."""
    if n < 0: return False
    r = isqrt(n)
    return r * r == n


def is_prime(n):
    """Primality: exact for n < PRIME_RANGE and for any n with a prime factor below 100; ValueError otherwise."""
    if n < 2: return False
    for q in _SMALL:
        if n % q == 0: return n == q
    if n < 97 * 97: return True
    if n >= PRIME_RANGE: raise ValueError(f"is_prime: {n} is outside the stated range (below {PRIME_RANGE})")
    d, s = n - 1, 0
    while d % 2 == 0: d //= 2; s += 1
    for a in _MR_BASES:
        x = pow(a, d, n)
        if x == 1 or x == n - 1: continue
        for _ in range(s - 1):
            x = x * x % n
            if x == n - 1: break
        else:
            return False
    return True


def _rho(n, c, limit=None):
    """A non-trivial factor of the composite n by Brent's cycle, or n on failure (then another c is tried). With a limit,
    n is also returned once the cycle search passes that many steps."""
    y, m, g, r, q = 2, 128, 1, 1, 1
    f = lambda v: (v * v + c) % n
    x = ys = y
    while g == 1:
        if limit is not None and r > limit: return n
        x = y
        for _ in range(r): y = f(y)
        k = 0
        while k < r and g == 1:
            ys = y
            for _ in range(min(m, r - k)):
                y = f(y); q = q * abs(x - y) % n
            g = gcd(q, n); k += m
        r *= 2
    if g == n:
        g = 1
        while g == 1:
            ys = f(ys); g = gcd(abs(x - ys), n)
    return g


def factorize(n):
    """{prime: exponent} for n ≥ 1, each prime proved by is_prime; ValueError if a prime factor lies at or above
    PRIME_RANGE, where no primality proof is stated."""
    if n < 1: raise ValueError("factorize: n must be positive")
    out, m = {}, n
    for q in range(2, _TRIAL_LIMIT):
        if q * q > m: break
        while m % q == 0: out[q] = out.get(q, 0) + 1; m //= q
    stack = [m] if m > 1 else []
    while stack:
        x = stack.pop()
        if x == 1: continue
        if x < PRIME_RANGE and is_prime(x): out[x] = out.get(x, 0) + 1; continue
        if is_square(x): r = isqrt(x); stack += [r, r]; continue
        c, d = 1, x
        big = x >= PRIME_RANGE                                                 # no primality proof: a bounded search
        while d == x and (not big or c <= 4): d = _rho(x, c, 1 << 20 if big else None); c += 1
        if d == x: raise ValueError(f"factorize: {x} lies outside the stated range and was not split")
        stack += [d, x // d]
    return dict(sorted(out.items()))


def prime_factors(n):
    """The distinct primes dividing n, ascending."""
    return list(factorize(n))


def phi(n):
    """Euler's totient."""
    r = n
    for p in factorize(n): r = r // p * (p - 1)
    return r


def carmichael(n):
    """Carmichael's λ(n): the exponent of the unit group mod n."""
    out = 1
    for p, e in factorize(n).items():
        lam = (p - 1) * p ** (e - 1)
        if p == 2 and e >= 3: lam //= 2
        out = out * lam // gcd(out, lam)
    return out


def order(a, n):
    """The multiplicative order of a mod n (gcd(a, n) = 1 required)."""
    if n < 1 or gcd(a, n) != 1: raise ValueError(f"order: {a} is not a unit mod {n}")
    if n == 1: return 1
    k = carmichael(n)
    for p in factorize(k):
        while k % p == 0 and pow(a, k // p, n) == 1: k //= p
    return k


def is_primitive_root(g, n):
    """True iff g generates the unit group mod n."""
    return gcd(g, n) == 1 and order(g % n, n) == phi(n)


def _has_primitive_root(n):
    if n in (1, 2, 4): return True
    m = n // 2 if n % 2 == 0 else n
    if m % 2 == 0: return False
    f = factorize(m)
    return len(f) == 1


def primitive_root(n):
    """The least primitive root of n = 1, 2, 4, p^k or 2p^k (p an odd prime); ValueError otherwise."""
    if not _has_primitive_root(n): raise ValueError(f"primitive_root: {n} has none")
    if n <= 2: return n - 1 if n == 2 else 0
    ph = phi(n); ps = prime_factors(ph)
    for g in range(2, n):
        if gcd(g, n) == 1 and all(pow(g, ph // q, n) != 1 for q in ps): return g
    raise AssertionError("unreachable: the unit group is cyclic")


def primitive_roots(n):
    """Every primitive root of n, ascending: g0^u for the least g0 and u coprime to φ(n)."""
    g0, ph = primitive_root(n), phi(n)
    if n <= 2: return [g0]
    return sorted(pow(g0, u, n) for u in range(1, ph) if gcd(u, ph) == 1)


def legendre(a, p):
    """The Legendre symbol (a | p) ∈ {−1, 0, 1} for an odd prime p, by Euler's criterion."""
    t = pow(a % p, (p - 1) // 2, p)
    return -1 if t == p - 1 else t


def jacobi(a, n):
    """The Jacobi symbol (a | n) for odd n > 0, by quadratic reciprocity (no factorisation)."""
    if n <= 0 or n % 2 == 0: raise ValueError("jacobi: n must be odd and positive")
    a, s = a % n, 1
    while a:
        while a % 2 == 0:
            a //= 2
            if n % 8 in (3, 5): s = -s
        a, n = n, a
        if a % 4 == 3 and n % 4 == 3: s = -s
        a %= n
    return s if n == 1 else 0


def nonresidue(p):
    """The least quadratic non-residue mod the odd prime p."""
    for a in range(2, p):
        if legendre(a, p) == -1: return a
    raise ValueError(f"nonresidue: {p} is not an odd prime")


def sqrt_mod(a, p):
    """A square root of a mod the odd prime p (the smaller of the two), by Tonelli–Shanks; ValueError if a is a non-residue."""
    a %= p
    if a == 0: return 0
    if legendre(a, p) != 1: raise ValueError(f"sqrt_mod: {a} is not a square mod {p}")
    q, s = p - 1, 0
    while q % 2 == 0: q //= 2; s += 1
    z = nonresidue(p)
    m, c, t, r = s, pow(z, q, p), pow(a, q, p), pow(a, (q + 1) // 2, p)
    while t != 1:
        i, t2 = 0, t
        while t2 != 1: t2 = t2 * t2 % p; i += 1
        b = pow(c, 1 << (m - i - 1), p)
        m, c, t, r = i, b * b % p, t * b * b % p, r * b % p
    return min(r, p - r)


def inverse(a, n):
    """The inverse of a mod n (ValueError if a is not a unit)."""
    try: return pow(a, -1, n)
    except ValueError: raise ValueError(f"inverse: {a} is not a unit mod {n}") from None


def crt(residues, moduli):
    """The x mod lcm(moduli) with x ≡ r_i (mod m_i) for every i; ValueError if the congruences are incompatible."""
    x, m = 0, 1
    for r, n in zip(residues, moduli):
        g = gcd(m, n)
        if (r - x) % g: raise ValueError("crt: incompatible congruences")
        k = ((r - x) // g) * inverse(m // g, n // g) % (n // g)
        x, m = x + m * k, m // g * n
        x %= m
    return x


def valuation(n, p):
    """The exponent of the prime p in n ≠ 0."""
    if n == 0: raise ValueError("valuation: n must be nonzero")
    k = 0
    while n % p == 0: n //= p; k += 1
    return k
