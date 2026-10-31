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

The division fold and the binding lift (00:F4, 00:F6; 17 October 2026):
    cycle(q, g)                 the cycle ⟨g⟩ in 𝔽_q^×, by iteration: [1, g, g², …] up to the return to 1
    division_fold(q, g)         00:F4 — {(r, s): iʳ gˢ} for r < 4, s < κ on the cycle ⟨g⟩ of order 4κ, i = g^{3κ}
    core_cosets(q, g)           the κ fibres gˢ·Q₄ of the quotient of ⟨g⟩ by its core Q₄ = {1, i, −1, −i}, s < κ
    fusion(a, b)                00:F6 — the joint drive with unit windings on ℤ/a × ℤ/b has one orbit

The ledger of observation (task LM35, 7 October 2026), first used by 22-quantum's ledger file:
    cyclotomic_poly(n)          Φ_n as an integer coefficient list
    Cyclotomic(n)               the ring ℤ[ζ_n] ⊂ ℚ(ζ_n) = ℚ[x]/(Φ_n): elements are tuples of φ(n) coefficients
    partial_transpose(rho)      the partial transpose on the second factor of a 2 ⊗ 2 matrix
    charpoly(M)                 the characteristic polynomial det(xI − M) of a square matrix, exactly
    nonneg_spectrum(M)          every eigenvalue of a real symmetric matrix is ≥ 0, from the signs of its charpoly

Exact real-root isolation of integer polynomials (the framed readout on the sweep, 22:C29; moved here from the ledger
file on 30 October 2026): coefficient lists low to high, rational arithmetic throughout.
    peval(poly, x)              the value at a rational x (Horner)
    padd(a, b)                  the sum of two coefficient lists
    sturm(poly)                 the Sturm sequence
    isolate(poly)               isolating intervals of every real root in (−2, 2), sorted decreasing
    refine(poly, lo, hi, width) bisection of an isolating bracket to the width
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


def cycle(q, g):
    """The cycle ⟨g⟩ in 𝔽_q^× by iteration: [1, g, g², …] up to the return to 1 (g a unit)."""
    out, x = [], 1
    while True:
        out.append(x); x = x * g % q
        if x == 1: return out


def division_fold(q, g):
    """00:F4 — the division fold of the cycle ⟨g⟩ of order n = 4κ in 𝔽_q: the dict {(r, s): iʳ gˢ} over the class r < 4
    and the rung s < κ, with i = g^{3κ} (= −g^κ, the quarter-turn of a frame)."""
    n = len(cycle(q, g))
    if n % 4: raise ValueError(f"division_fold: the order {n} of {g} in F_{q} is not a multiple of 4")
    k = n // 4
    i = pow(g, 3 * k, q)
    return {(r, s): pow(i, r, q) * pow(g, s, q) % q for r in range(4) for s in range(k)}


def core_cosets(q, g):
    """The fibres of the Q₄ quotient of the cycle ⟨g⟩ of order 4κ: the κ cosets gˢ·{1, i, −1, −i}, s < κ, as frozensets."""
    n = len(cycle(q, g))
    if n % 4: raise ValueError(f"core_cosets: the order {n} of {g} in F_{q} is not a multiple of 4")
    k = n // 4
    i = pow(g, 3 * k, q)
    core = [pow(i, r, q) for r in range(4)]
    return [frozenset(pow(g, s, q) * w % q for w in core) for s in range(k)]


def fusion(a, b):
    """00:F6 — the pair of cycles ℤ/a, ℤ/b fuses under the joint drive with unit windings: one orbit, by enumeration."""
    return len(orbits(a, b)) == 1


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


def padd(a, b):
    """The sum of two coefficient lists (low to high)."""
    n = max(len(a), len(b)); a = a + [0] * (n - len(a)); b = b + [0] * (n - len(b))
    return [x + y for x, y in zip(a, b)]

def peval(poly, x):
    """The value of the polynomial at x, by Horner's rule (exact for rational x)."""
    r = Fraction(0)
    for cc in reversed(poly): r = r * x + cc
    return r

def ptrim(poly):
    """The coefficient list without trailing zeros (the zero polynomial is [0])."""
    while len(poly) > 1 and poly[-1] == 0: poly = poly[:-1]
    return poly

def pdivmod(a, b):
    """The remainder of a modulo b over the rationals."""
    a = [Fraction(x) for x in ptrim(a)]; b = [Fraction(x) for x in ptrim(b)]
    while len(a) >= len(b) and any(a):
        k = len(a) - len(b); cc = a[-1] / b[-1]
        a = ptrim([a[i] - (cc * b[i - k] if i >= k else 0) for i in range(len(a))])
        if len(a) < len(b): break
    return a

def sturm(poly):
    """The Sturm sequence of poly: poly, its derivative, then the negated remainders."""
    seq = [ptrim(poly), ptrim([i * cc for i, cc in enumerate(poly)][1:])]
    while True:
        r = ptrim([-x for x in pdivmod(seq[-2], seq[-1])])
        if r == [0] or r == []: break
        seq.append(r)
    return seq

def nroots(seq, a, b):
    """The number of distinct real roots in (a, b] from the Sturm sequence seq, by sign changes."""
    def changes(x):
        v = [val for val in (peval(p, x) for p in seq) if val != 0]
        return sum(1 for u, w in zip(v, v[1:]) if (u > 0) != (w > 0))
    return changes(a) - changes(b)

def isolate(poly):
    """Isolating intervals (lo, hi) of every real root of poly in (−2, 2), sorted decreasing, by Sturm counts and bisection."""
    seq = sturm(poly); boxes, out = [(Fraction(-2), Fraction(2))], []
    while boxes:
        lo, hi = boxes.pop(); k = nroots(seq, lo, hi)
        if k == 0: continue
        if k == 1 and peval(poly, lo) * peval(poly, hi) < 0: out.append((lo, hi)); continue
        mid = (lo + hi) / 2
        if peval(poly, mid) == 0:
            eps = Fraction(1, 10 ** 6); out.append((mid - eps, mid + eps)); boxes += [(lo, mid - eps), (mid + eps, hi)]; continue
        boxes += [(lo, mid), (mid, hi)]
    return sorted(out, key=lambda t: -t[0])

def refine(poly, lo, hi, width):
    """Bisect the isolating bracket (lo, hi) of a simple root until its width is at most width; an exact hit returns (x, x)."""
    flo = peval(poly, lo)
    while hi - lo > width:
        mid = (lo + hi) / 2; fm = peval(poly, mid)
        if fm == 0: return mid, mid
        if (fm > 0) == (flo > 0): lo, flo = mid, fm
        else: hi = mid
    return lo, hi


# ---- the real subfield of ℚ(ζ_12) and Hermitian spectra over it (22:C33, C34) -------------------------------------------
def real_q3(Z, x):
    """A real element x of ℚ(ζ_12) as the pair (a, b) with x = a + b√3, where √3 = ζ_12 + ζ_12^{-1}; asserts reality."""
    assert Z.n == 12, "the real subfield ℚ(√3) is that of ℚ(ζ_12)"
    s3 = Z.add(Z.zeta(1), Z.zeta(-1))
    k = next(i for i, c in enumerate(s3) if c and i)
    b = Fraction(x[k]) / Fraction(s3[k]); a = Fraction(x[0]) - b * Fraction(s3[0])
    assert Z.add(Z.scale(a, Z.one), Z.scale(b, s3)) == tuple(Fraction(c) for c in x), "not a real element"
    return a, b

def sign_q3(a, b):
    """The sign of a + b√3, decided exactly on the rationals (a² against 3b² when the signs differ)."""
    if a == 0 and b == 0: return 0
    if a >= 0 and b >= 0: return 1
    if a <= 0 and b <= 0: return -1
    return (1 if a * a > 3 * b * b else -1) if a > 0 else (1 if 3 * b * b > a * a else -1)

def herm_charpoly(Z, M):
    """det(xI − M) for a Hermitian matrix over the cyclotomic ring Z, by Faddeev–LeVerrier: coefficients from x^n down."""
    n = len(M); c, A = [Z.one], [[Z.zero] * n for _ in range(n)]
    for k in range(1, n + 1):
        A = [[Z.add(Z.sum(Z.mul(M[i][l], A[l][j]) for l in range(n)), c[-1] if i == j else Z.zero) for j in range(n)] for i in range(n)]
        MA = [[Z.sum(Z.mul(M[i][l], A[l][j]) for l in range(n)) for j in range(n)] for i in range(n)]
        c.append(Z.scale(Fraction(-1, k), Z.sum(MA[i][i] for i in range(n))))
    return c

def herm_nonneg_spectrum(Z, M):
    """True iff every eigenvalue of the Hermitian matrix M over ℚ(ζ_12) is ≥ 0: its characteristic polynomial is real-rooted,
    so (Descartes) the roots are all ≥ 0 exactly when its real coefficients alternate in sign, decided in ℚ(√3)."""
    return all(sign_q3(*real_q3(Z, Z.scale((-1) ** k, cc))) >= 0 for k, cc in enumerate(herm_charpoly(Z, M)))


# ---- the registered state of a pair run under spread laws (22:C33, C34) -------------------------------------------------------
def spread_char(Z, q, s):
    """The characteristic Σ_ξ q_ξ ζ^{ξ s} of a spread law q (a dict offset → weight) at argument s."""
    return Z.from_exponents((e * s, w) for e, w in q.items())

def pair_coherence(Z, q1, q2, m1, m2, c1, c2, N):
    """The registered state ρ_{b,b'} = Γ_{b,b'}/4 of a pair run: sources of m1, m2 cells with c1, c2 locked and the spread laws
    q1, q2 of their spread cells; Γ_{b,b'} = ζ^{c1 c2 Δ} Π_a χ_a(m2 Δ) Π_b χ_b(m1 Δ) at the step counts N of the four branches."""
    def coh(D):
        g = Z.zeta(c1 * c2 * D)
        for q in q1: g = Z.mul(g, spread_char(Z, q, m2 * D))
        for q in q2: g = Z.mul(g, spread_char(Z, q, m1 * D))
        return Z.scale(Fraction(1, 4), g)
    return [[coh(N[i] - N[j]) for j in range(4)] for i in range(4)]

def canonical_partition(lab):
    """The partition of the four branches by equal label, as the first-occurrence relabelling."""
    seen = {}
    return tuple(seen.setdefault(x, len(seen)) for x in lab)

def partition_state(lab):
    """The complete-spread state: 1/4 on the pairs of branches with equal separation label, 0 elsewhere."""
    return [[Fraction(1, 4) if lab[a] == lab[b] else Fraction(0) for b in range(4)] for a in range(4)]
