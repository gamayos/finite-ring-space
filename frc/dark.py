"""frc.dark — the dark theme (programme tier, rank 28; 32-dark's migration, 18 October 2026).

The exact content of *The Dark Sector over Finite Relational Substrate* (32-dark), above the gravity theme's Gauss law
(frc/drift.py) and the extension theme's F_{p²} (frc/extension.py: Ext, Quad). Everything here is integer, finite-field
or rational arithmetic; the readings of the continuum and of the SPARC tables live in the chart theme
(frc/chart_dark.py). The Lean side is lean/FrcCore/Theme/Dark.lean, whose theorems these functions mirror: the discrete
Gauss law on a finite box (the enclosed flux, the source-free field, the superposition), the amplitude identity (the
coherent stack n², the mean over all sign patterns n), the first-passage quadratic and its two roots (Vieta), the
killed walk on the cycle Z_N against the two-image closed form, the passage factor, the coherence sum at C = 1 and
C = 0 and N_eff, the Tully–Fisher identity, and the divisor lattice of Ω − 1 on the laboratory carrier.

    GaussBox(n)                     the n³ box with Dirichlet boundary: field(source, boundary), flux(U, R) in Fractions
    gauss_law(seed)                 (flux R=0, flux R=1, source-free flux, superposed flux) of a unit source and a noise field
    coherent_count(K, u, n)         norm(n·u) = n² norm(u): the aligned stack
    sign_pattern_total(K, us)       Σ over all sign patterns of norm(Σ ε_k u_k) = 2^n Σ norm(u_k): the incoherent mean n
    incoherent_mean(n)              the mean of (Σ ε_k)² over all sign patterns of n units, exactly n
    passage_roots(z)                the two roots of (z/2)f² − f + z/2 = 0 for rational z with 1 − z² a square; product 1
    passage_factor(u)               f = u − √(u² − 1) for rational u with u² − 1 a square; f(1/u) by the quadratic
    cycle_escape(N, a, z)           the killed walk on Z_N (absorbing at a, start at 0) solved exactly in Fractions
    cycle_closed(N, a, f)           the two-image form (f^a + f^{N−a})/(1 + f^N)
    n_eff(gs)                       (Σ√g)²/Σg on rational squares
    coherence_sum(gs, C)            Σg + 2 Σ_{i<j} √(g_i g_j) C_ij: (Σ√g)² at C = 1, Σg at C = 0
    tully_fisher(G, M, a0)          s² = GMa₀, v² = s ⟹ v⁴ = GMa₀ on rational fourth powers
    divisor_lattice(n)              the divisors of n and the ratios n/d, exact
"""
import itertools
import random
from fractions import Fraction as Q
from math import isqrt

from frc.arith import factorize
from frc.extension import Ext, Quad

CARRIER = 2408561                                   # the laboratory Carrier of 37-sim; Ω − 1 = 2 408 560 = 2⁴·5·7·11·17·23


def _sqrt_q(q):
    """The rational square root of a rational square, or None."""
    q = Q(q)
    if q < 0: return None
    a, b = isqrt(q.numerator), isqrt(q.denominator)
    return Q(a, b) if a * a == q.numerator and b * b == q.denominator else None


# ---- the discrete Gauss law on a finite box ---------------------------------------------------------------------------------
class GaussBox:
    """The n³ box of sites, the Laplacian with Dirichlet boundary (the boundary sites fixed), solved in Fractions: the
    linear synchronisation statics L u = source. flux(U, R) is the net flux through the surface of the cube of radius R
    about the centre, Σ (U(p) − U(q)) over the edges leaving it (32:C1, 32:X1)."""

    def __init__(self, n=5):
        self.n = n
        self.pts = list(itertools.product(range(n), repeat=3))
        self.interior = [p for p in self.pts if all(0 < c < n - 1 for c in p)]
        self.boundary = [p for p in self.pts if not all(0 < c < n - 1 for c in p)]
        self.pos = {p: i for i, p in enumerate(self.interior)}
        self.centre = (n // 2,) * 3

    @staticmethod
    def nbrs(p):
        x, y, z = p
        for d in ((1, 0, 0), (-1, 0, 0), (0, 1, 0), (0, -1, 0), (0, 0, 1), (0, 0, -1)):
            yield (x + d[0], y + d[1], z + d[2])

    @staticmethod
    def solve(A, b):
        """Gauss–Jordan elimination in Fractions."""
        n = len(b); A = [r[:] for r in A]; b = b[:]
        for c in range(n):
            piv = next(r for r in range(c, n) if A[r][c] != 0)
            A[c], A[piv] = A[piv], A[c]; b[c], b[piv] = b[piv], b[c]
            inv = Q(1) / A[c][c]; A[c] = [v * inv for v in A[c]]; b[c] *= inv
            for r in range(n):
                if r != c and A[r][c] != 0:
                    f = A[r][c]; A[r] = [x - f * y for x, y in zip(A[r], A[c])]; b[r] -= f * b[c]
        return b

    def field(self, source, boundary):
        """The field U with 6U(p) − Σ_q U(q) = source(p) on the interior and U = boundary on the boundary sites."""
        M = len(self.interior)
        A = [[Q(0)] * M for _ in range(M)]; b = [Q(0)] * M
        for p in self.interior:
            i = self.pos[p]; A[i][i] = Q(6)
            for q in self.nbrs(p):
                if q in self.pos: A[i][self.pos[q]] -= 1
                else: b[i] += boundary.get(q, Q(0))
            b[i] += source.get(p, Q(0))
        x = self.solve(A, b)
        U = dict(boundary)
        for p in self.interior: U[p] = x[self.pos[p]]
        return U

    def flux(self, U, R):
        c = self.centre
        def inside(p): return max(abs(p[k] - c[k]) for k in range(3)) <= R
        tot = Q(0)
        for p in self.pts:
            if not inside(p): continue
            for q in self.nbrs(p):
                if not inside(q): tot += U.get(p, Q(0)) - U.get(q, Q(0))
        return tot


def gauss_law(seed=1, n=5):
    """On the n³ box: the unit source at the centre with zero boundary (its flux through R = 0 and R = 1), a source-free
    field with random rational boundary values (its flux through R = 1), and the superposition (its flux through R = 1).
    The Gauss law: (1, 1, 0, 1)."""
    box = GaussBox(n)
    zero = {p: Q(0) for p in box.boundary}
    Us = box.field({box.centre: Q(1)}, zero)
    rng = random.Random(seed)
    noise = {p: Q(rng.randint(-9, 9), 4) for p in box.boundary}
    Un = box.field({}, noise)
    Usn = box.field({box.centre: Q(1)}, noise)
    return box.flux(Us, 0), box.flux(Us, 1), box.flux(Un, 1), box.flux(Usn, 1)


def superposition(U1, U2):
    return {p: U1.get(p, Q(0)) + U2.get(p, Q(0)) for p in set(U1) | set(U2)}


# ---- the amplitude identity: coherent n², incoherent mean n -----------------------------------------------------------
GI = Quad(-1)                                        # Z[i]


def scale(K, u, n):
    """n·u in the ring K (repeated addition)."""
    s = K.el(0, 0) if isinstance(K, Quad) else (0, 0)
    for _ in range(n): s = K.add(s, u)
    return s


def coherent_count(K, u, n):
    """(norm(n·u), n² norm(u)): the aligned stack of n copies has norm n² times the unit's (32:C3)."""
    p = getattr(K, "p", None)
    rhs = n * n * K.norm(u)
    return K.norm(scale(K, u, n)), (rhs % p if p else rhs)


def sign_pattern_total(K, us):
    """(Σ_ε norm(Σ_k ε_k u_k), 2^n Σ_k norm(u_k)) over all 2^n sign patterns: the cross terms cancel (32:C3)."""
    n = len(us)
    zero = K.el(0, 0) if isinstance(K, Quad) else (0, 0)
    tot = 0
    for eps in itertools.product((1, -1), repeat=n):
        s = zero
        for e, u in zip(eps, us): s = K.add(s, u if e == 1 else K.neg(u))
        tot += K.norm(s)
    rhs = 2 ** n * sum(K.norm(u) for u in us)
    p = getattr(K, "p", None)
    return (tot % p, rhs % p) if p else (tot, rhs)


def incoherent_mean(n):
    """The mean of (Σ ε_k)² over all sign patterns of n real units, a Fraction: exactly n (32:C3)."""
    tot = sum(sum(eps) ** 2 for eps in itertools.product((1, -1), repeat=n))
    return Q(tot, 2 ** n)


def shell_ext(p):
    """F_{p²} = F_p(√ν) for the shell p, ν its least nonresidue."""
    from frc.arith import nonresidue
    return Ext(p, nonresidue(p))


# ---- the first-passage quadratic ---------------------------------------------------------------------------------------
def passage_roots(z):
    """The two roots f, f' of (z/2)f² − f + z/2 = 0 for rational z with 1 − z² a rational square: f = (1 − r)/z,
    f' = (1 + r)/z with r = √(1 − z²); ff' = 1 and f + f' = 2/z (Vieta). None if 1 − z² is not a square (32:C6, 32:C7)."""
    z = Q(z)
    r = _sqrt_q(1 - z * z)
    if r is None: return None
    return (1 - r) / z, (1 + r) / z


def passage_residual(z, f):
    """(z/2)f² − f + z/2."""
    z, f = Q(z), Q(f)
    return z / 2 * f * f - f + z / 2


def passage_factor(u):
    """f = u − √(u² − 1) for rational u ≥ 1 with u² − 1 a rational square, and its reciprocal u + √(u² − 1); f is the
    smaller root of the quadratic at z = 1/u (32:C7)."""
    u = Q(u)
    r = _sqrt_q(u * u - 1)
    if r is None: return None
    return u - r, u + r


def cycle_escape(N, a, z):
    """The killed walk on Z_N with per-step survival z, absorbing at site a, started at 0: h_a = 1 and
    h_i = (z/2)(h_{i−1} + h_{i+1}) for i ≠ a, solved exactly in Fractions; returns h_0 (32:C7)."""
    z = Q(z)
    A = [[Q(0)] * N for _ in range(N)]; b = [Q(0)] * N
    for i in range(N):
        A[i][i] = Q(1)
        if i == a: b[i] = Q(1)
        else:
            A[i][(i - 1) % N] -= z / 2
            A[i][(i + 1) % N] -= z / 2
    return GaussBox.solve(A, b)[0]


def cycle_closed(N, a, f):
    """The two-image closed form of the cycle's escape value, (f^a + f^{N−a})/(1 + f^N), for the line's factor f."""
    f = Q(f)
    return (f ** a + f ** (N - a)) / (1 + f ** N)


def line_escape(a, f):
    return Q(f) ** a


# ---- the coherence sum and N_eff --------------------------------------------------------------------------------------------
def coherence_sum(gs, C):
    """g_amp² = Σ g_i + 2 Σ_{i<j} √(g_i g_j) C_ij on rational squares g_i, with a constant C (32:C10, 32:P5, 32:X8)."""
    gs = [Q(g) for g in gs]
    roots = [_sqrt_q(g) for g in gs]
    if any(r is None for r in roots): return None
    tot = sum(gs)
    for i in range(len(gs)):
        for j in range(i + 1, len(gs)):
            tot += 2 * roots[i] * roots[j] * Q(C)
    return tot


def n_eff(gs):
    """N_eff = (Σ√g)²/Σg on rational squares (32:X8)."""
    gs = [Q(g) for g in gs]
    roots = [_sqrt_q(g) for g in gs]
    if any(r is None for r in roots): return None
    return sum(roots) ** 2 / sum(gs)


def phasor_cycle_sum(K, zeta, n):
    """Σ_{l<n} ζ^l in K for ζ of order n: zero (the full cycle's bulk-coherence weight 0, 32:C10); the aligned sum of n
    units is n (weight 1)."""
    s = K.scalar(0) if isinstance(K, Ext) else K.el(0, 0)
    z = K.scalar(1) if isinstance(K, Ext) else K.el(1, 0)
    for _ in range(n):
        s = K.add(s, z); z = K.mul(z, zeta)
    return s


# ---- the Tully–Fisher identity ------------------------------------------------------------------------------------------------
def tully_fisher(G, M, a0):
    """s = √(GMa₀) and v = √s on rationals where both exist: (v⁴, GMa₀, v², s); v⁴ = GMa₀ (32:C5, 32:X3)."""
    G, M, a0 = Q(G), Q(M), Q(a0)
    s = _sqrt_q(G * M * a0)
    if s is None: return None
    v = _sqrt_q(s)
    if v is None: return None
    return v ** 4, G * M * a0, v * v, s


# ---- the divisor lattice of Ω − 1 ----------------------------------------------------------------------------------------------
def divisor_lattice(n):
    """The divisors of n in increasing order and the exact ratios n/d (the running a₀(d)/a₀(carrier) = (Ω − 1)/d of
    32:Z1), from the factorisation."""
    fac = factorize(n)
    divs = [1]
    for p, e in sorted(fac.items()):
        divs = [d * p ** k for d in divs for k in range(e + 1)]
    divs.sort()
    return fac, divs, [n // d for d in divs]
