"""frc.horizon — the shell theorem in the 𝔽_p reading (the horizon theme; ledger migration, task LM26, 6 October 2026).

The python side of `lean/FrcCore/Theme/Horizon.lean`: on a frame (p = 4κ + 1, g a drive, n = p − 1) the finite zeta
Z(k) = Σ_{x≠0} x^k, the coefficients of a vector in the power modes x ↦ x^k, the scale-shift x ↦ g^r x and its fixed
points, and the readout z(θ) = 2⁻¹ + θη on the self-dual line Tr z = 1. Exact integers mod p only, the standard library
only (gate G09). The first ledger to use it is the master's block file frc/ledgers/master/horizon.py.

    zeta(p, k)                   Z(k) = Σ_{x=1}^{p−1} x^k mod p
    mode_coeffs(p, g, v)         c_k = −Σ_{l<n} v_l g^((n−l)k), k < n: the Lean proof's coefficients
    expand(p, g, c, j)           Σ_{k<n} c_k (g^j)^k, the vector at the point x = g^j
    shift(p, g, r, x)            g^r x
    fixed_points(p, g, r)        the nonzero residues x with g^r x = x
    readout(p, theta)            (2⁻¹, θ): the point 2⁻¹ + θη as (real part, η-part), 2⁻¹ = 2κ + 1
    trace(p, z)                  Tr z = 2 Re z

20-rh's ledger file (frc/ledgers/p20_rh.py, task LM36) adds the arithmetic of its units-chart resonance:

    prime_power_base(n)          ℓ when n = ℓ^k (k ≥ 1), else None: the support of Λ, Λ(n) = log ℓ
    mobius_phi(M)                the lists μ(n) and φ(n) for n ≤ M (a linear sieve)
    divisors(n)                  the divisors of n, ascending
    ramanujan_c(q, n, mu)        Kluyver's c_q(n) = Σ_{d | gcd(q, n)} d μ(q/d), an integer
    resonance(L, N, mu, phi)     R_l(n) = Σ_{q≤l} μ(q)/φ(q) c_q(n) for l ≤ L, n ≤ N, in rationals
    log_free_mangoldt(n, mu)     Π_{d|n} d^{−μ(d)}: ℓ on the prime powers ℓ^k and 1 elsewhere, Λ = μ ∗ log exponentiated
"""
from fractions import Fraction


def zeta(p, k):
    """The finite zeta Z(k) = Σ_{x≠0} x^k on the shell p."""
    return sum(pow(x, k, p) for x in range(1, p)) % p


def mode_coeffs(p, g, v):
    """The coefficients of the vector v (indexed by the cycle, v[j] at x = g^j) in the power modes: c_k = −Σ_l v_l g^((n−l)k)."""
    n = p - 1
    return [(-sum(v[l] * pow(g, (n - l) * k, p) for l in range(n))) % p for k in range(n)]


def expand(p, g, c, j):
    """The expansion Σ_k c_k (g^j)^k at the point x = g^j."""
    x = pow(g, j, p)
    return sum(ck * pow(x, k, p) for k, ck in enumerate(c)) % p


def shift(p, g, r, x):
    """The scale-shift x ↦ g^r x."""
    return pow(g, r, p) * x % p


def fixed_points(p, g, r):
    """The nonzero residues the scale-shift x ↦ g^r x fixes."""
    return [x for x in range(1, p) if shift(p, g, r, x) == x]


def readout(p, theta):
    """The readout z(θ) = 2⁻¹ + θη as the pair (2κ + 1, θ)."""
    return ((p - 1) // 2 + 1) % p, theta % p


def trace(p, z):
    """The trace Tr(a + bη) = 2a."""
    return 2 * z[0] % p


def prime_power_base(n):
    """The prime ℓ when n = ℓ^k with k ≥ 1, else None (the support of the von Mangoldt weight)."""
    if n < 2: return None
    d = 2
    while d * d <= n and n % d: d += 1
    if n % d: d = n
    while n % d == 0: n //= d
    return d if n == 1 else None


def mobius_phi(M):
    """μ(n) and φ(n) for 0 ≤ n ≤ M, by a linear sieve (μ(0) = 0)."""
    mu, phi, comp, primes = [1] * (M + 1), list(range(M + 1)), [False] * (M + 1), []
    mu[0] = 0
    for i in range(2, M + 1):
        if not comp[i]: primes.append(i); mu[i] = -1; phi[i] = i - 1
        for q in primes:
            if i * q > M: break
            comp[i * q] = True
            if i % q == 0: mu[i * q] = 0; phi[i * q] = phi[i] * q; break
            mu[i * q] = -mu[i]; phi[i * q] = phi[i] * (q - 1)
    return mu, phi


def divisors(n):
    """The divisors of n, ascending."""
    return [d for d in range(1, n + 1) if n % d == 0]


def ramanujan_c(q, n, mu):
    """Kluyver's formula: c_q(n) = Σ_{d | gcd(q, n)} d μ(q/d)."""
    from math import gcd
    return sum(d * mu[q // d] for d in divisors(gcd(q, n)))


def resonance(L, N, mu, phi):
    """cum[l][n] = R_l(n) = Σ_{q≤l} μ(q)/φ(q) c_q(n) for 0 ≤ l ≤ L, 0 ≤ n ≤ N, exact rationals (n = 0 unused)."""
    cum = [[Fraction(0)] * (N + 1)]
    for q in range(1, L + 1):
        w = Fraction(mu[q], phi[q]); prev = cum[-1]
        cum.append([prev[n] + (w * ramanujan_c(q, n, mu) if n and w else 0) for n in range(N + 1)])
    return cum


def log_free_mangoldt(n, mu):
    """Π_{d | n, d > 1} d^{−μ(d)} as a rational: ℓ when n = ℓ^k and 1 elsewhere, the exponentiated form of
    −Σ_{d|n} μ(d) log d = Λ(n) (unique factorisation turns the identity of logarithms into one of rationals)."""
    out = Fraction(1)
    for d in divisors(n):
        if d > 1 and mu[d]: out *= Fraction(1, d) if mu[d] == 1 else d
    return out

