"""frc.quantum — the unequal-cycle composite (the quantum theme; ledger migration, task LM28, 6 October 2026).

The python side of `lean/FrcCore/Theme/Quantum.lean`: a composite of parts with registration periods n_j, driven jointly
one step per chronon. The joint period, the orbits of the joint drive and their offsets, and the characters of the
composite in a prime shell with their sums along the drive. Exact integers only, the standard library only (gate G09).
The first ledger to use it is the master's block file frc/ledgers/master/quantum.py.

    joint_period(ns)            the least t > 0 at which every part returns, by search
    orbits(a, b)                the orbits of (x, y) ↦ (x + 1, y + 1) on ℤ/a × ℤ/b, by enumeration
    offset(x, y, g)             the conserved offset (x − y) mod g
    reach(x, y, x2, y2, a, b)   a chronon t carrying (x, y) to (x2, y2), by search, or None
    root_of_unity(q, N)         an element of order N in 𝔽_q (N | q − 1)
    character_sums(q, a, b, T)  for every character (ζ_a, ζ_b) of ℤ/a × ℤ/b in 𝔽_q: Σ_{t<T} (ζ_a ζ_b)^t, with χ(v) ≠ 1 or not
    components(m)               the primary components ℓᵃ of m (the graded registration law, 00:F5)
    depth(n, p)                 d = ord_n(p), the depth at which a component of order n registers in the Subject 𝔽_p
    home(n, p)                  where it registers: "absorbed" (n | p − 1), "torus" (n | p + 1), "quadratic" (n | p² − 1
                                only) or "beyond"

The ledger of observation (task LM35, 7 October 2026), first used by 22-quantum's ledger file:
    cyclotomic_poly(n)          Φ_n as an integer coefficient list
    Cyclotomic(n)               the ring ℤ[ζ_n] ⊂ ℚ(ζ_n) = ℚ[x]/(Φ_n): elements are tuples of φ(n) coefficients
    partial_transpose(rho)      the partial transpose on the second factor of a 2 ⊗ 2 matrix
    charpoly(M)                 the characteristic polynomial det(xI − M) of a square matrix, exactly
    nonneg_spectrum(M)          every eigenvalue of a real symmetric matrix is ≥ 0, from the signs of its charpoly
"""
from fractions import Fraction
from math import gcd, lcm

from frc import arith


def joint_period(ns):
    t = 1
    while any(t % n for n in ns): t += 1
    return t


def orbits(a, b):
    seen, out = set(), []
    for x in range(a):
        for y in range(b):
            if (x, y) in seen: continue
            orb, s = [], (x, y)
            while s not in seen:
                seen.add(s); orb.append(s); s = ((s[0] + 1) % a, (s[1] + 1) % b)
            out.append(orb)
    return out


def offset(x, y, g):
    return (x - y) % g


def reach(x, y, x2, y2, a, b):
    for t in range(a * b):
        if (x + t) % a == x2 and (y + t) % b == y2: return t
    return None


def root_of_unity(q, N):
    """An element of order exactly N in 𝔽_q^× (N | q − 1)."""
    g = arith.primitive_root(q)
    return pow(g, (q - 1) // N, q)


def character_sums(q, a, b, T):
    """[(moved, Σ_{t<T} (ζ_a ζ_b)^t mod q)] over the a·b characters ζ_a = ω_a^j, ζ_b = ω_b^k of ℤ/a × ℤ/b."""
    wa, wb = root_of_unity(q, a), root_of_unity(q, b)
    out = []
    for j in range(a):
        for k in range(b):
            z = pow(wa, j, q) * pow(wb, k, q) % q
            out.append((z != 1, sum(pow(z, t, q) for t in range(T)) % q))
    return out


def components(m):
    """The primary components ℓᵃ of m ≥ 1, as a sorted list of (ℓ, a, ℓᵃ)."""
    return sorted((l, a, l ** a) for l, a in arith.factorize(m).items()) if m > 1 else []


def depth(n, p):
    """d = ord_n(p): the least d ≥ 1 with pᵈ ≡ 1 (mod n), p prime to n; the component of order n registers in 𝔽_{pᵈ}."""
    return arith.order(p % n, n) if n > 1 else 1


def home(n, p):
    """Where a component of order n registers in the Subject 𝔽_p (00:F5)."""
    if (p - 1) % n == 0: return "absorbed"
    if (p + 1) % n == 0: return "torus"
    if (p * p - 1) % n == 0: return "quadratic"
    return "beyond"


def _poly_divexact(a, b):
    """The exact quotient a / b of integer polynomials, as coefficient lists from the lowest degree, b monic."""
    a, db = list(a), len(b) - 1
    q = [0] * (len(a) - db)
    for i in range(len(a) - 1, db - 1, -1):
        c = a[i]
        if c:
            q[i - db] = c
            for j, bc in enumerate(b): a[i - db + j] -= c * bc
    assert not any(a[:db]), "not an exact division"
    return q


def cyclotomic_poly(n, _memo={}):
    """Φ_n as an integer coefficient list, lowest degree first: x^n − 1 divided by Φ_d for every proper divisor d."""
    if n not in _memo:
        num = [-1] + [0] * (n - 1) + [1]
        for d in range(1, n):
            if n % d == 0: num = _poly_divexact(num, cyclotomic_poly(d))
        _memo[n] = num
    return _memo[n]


class Cyclotomic:
    """The cyclotomic ring ℤ[ζ_n] inside ℚ(ζ_n) = ℚ[x]/(Φ_n). An element is a tuple of deg Φ_n coefficients (int or
    Fraction) on 1, ζ, …, ζ^{φ−1}, the canonical form: two elements are equal iff their tuples are. Arithmetic is exact."""

    def __init__(self, n):
        self.n, phi = n, cyclotomic_poly(n)
        self.d = d = len(phi) - 1
        red = []                                     # x^k mod Φ_n, k < max(n, 2d − 1), as sparse [(i, c)]
        cur = [1] + [0] * (d - 1)
        for k in range(max(n, 2 * d - 1)):
            red.append([(i, c) for i, c in enumerate(cur) if c])
            top = cur[-1]; cur = [0] + cur[:-1]      # multiply by x, then reduce x^d = −Σ φ_i x^i
            if top: cur = [c - top * phi[i] for i, c in enumerate(cur)]
        self._red = red
        self.zero, self.one = (0,) * d, (1,) + (0,) * (d - 1)

    def fold(self, c):
        """The element Σ c[k] x^k for a coefficient list of length below max(n, 2d − 1)."""
        out = [0] * self.d
        for k, ck in enumerate(c):
            if ck:
                for i, r in self._red[k]: out[i] += ck * r
        return tuple(out)

    def zeta(self, e, c=1):
        """c ζ^e."""
        out = [0] * self.d
        for i, r in self._red[e % self.n]: out[i] += c * r
        return tuple(out)

    def from_exponents(self, terms):
        """Σ c ζ^e over the pairs (e, c) of an iterable or the items of a dict."""
        out = [0] * self.d
        for e, c in (terms.items() if isinstance(terms, dict) else terms):
            if c:
                for i, r in self._red[e % self.n]: out[i] += c * r
        return tuple(out)

    def const(self, c): return (c,) + (0,) * (self.d - 1)
    def add(self, a, b): return tuple(x + y for x, y in zip(a, b))
    def sub(self, a, b): return tuple(x - y for x, y in zip(a, b))
    def neg(self, a): return tuple(-x for x in a)
    def scale(self, c, a): return tuple(c * x for x in a)
    def sum(self, xs):
        out = self.zero
        for x in xs: out = self.add(out, x)
        return out

    def mul(self, a, b):
        c = [0] * (2 * self.d - 1)
        for i, x in enumerate(a):
            if x:
                for j, y in enumerate(b):
                    if y: c[i + j] += x * y
        return self.fold(c)

    def conj(self, a):
        """The complex conjugate ζ ↦ ζ^{−1}."""
        return self.from_exponents((-i, c) for i, c in enumerate(a))

    def norm2(self, a): return self.mul(a, self.conj(a))
    def is_rational(self, a): return not any(a[1:])

    def shadow(self, a, p, v):
        """The reduction ζ ↦ v into 𝔽_p, for v of order dividing n in 𝔽_p^× and coefficients whose denominators are prime to p."""
        s = 0
        for i, c in enumerate(a):
            if c:
                c = Fraction(c)
                s += c.numerator * pow(c.denominator, -1, p) * pow(v, i, p)
        return s % p


def partial_transpose(rho):
    """The partial transpose on the second factor of a 4 × 4 matrix on 2 ⊗ 2 (row index 2a + b)."""
    return [[rho[(a // 2) * 2 + b % 2][(b // 2) * 2 + a % 2] for b in range(4)] for a in range(4)]


def charpoly(M):
    """det(xI − M) of a square matrix of ints or Fractions, by Faddeev–LeVerrier: the coefficient list from x^n down."""
    n = len(M)
    c, A = [Fraction(1)], [[Fraction(0)] * n for _ in range(n)]
    for k in range(1, n + 1):
        A = [[sum(M[i][l] * A[l][j] for l in range(n)) + (c[-1] if i == j else 0) for j in range(n)] for i in range(n)]
        MA = [[sum(M[i][l] * A[l][j] for l in range(n)) for j in range(n)] for i in range(n)]
        c.append(-sum(MA[i][i] for i in range(n)) / k)
    return c


def nonneg_spectrum(M):
    """True iff every eigenvalue of the real symmetric matrix M is ≥ 0. Its charpoly has real roots only, so they are all
    ≥ 0 exactly when the coefficients alternate in sign (Descartes' rule, exact for real-rooted polynomials)."""
    return all((-1) ** k * c >= 0 for k, c in enumerate(charpoly(M)))
