"""frc.drift — the exact faces of frame drift (the gravity theme; 21-gravity, 10 October 2026).

The python side of `lean/FrcCore/Theme/Drift.lean` and of the register section of `lean/FrcCore/Theme/Gravity.lean`,
with the exact checks of 21-gravity's drift rows: the register on a frame, the mass–energy channel, the cover triangle,
the relative-cycle defect and its recurrence, the pair tally, the locked sum against the incoherent ensemble, the Gauss
law from transfer antisymmetry, the compression identity, the post-Newtonian coefficients as exact rational series, the
dust tensor's trace, the registration root, the Chebyshev two-boundary weight, the registered-inertia ledger identity,
the Christoffel registration words and the readout's largest-remainder allocation, the binding bookkeeping on a torus
(exact linear algebra over a prime field), the fold-return toy over 𝔽₁₇. Exact integers, fractions and residues; the
standard library only (gate G09). The ledger file that uses it: frc/ledgers/p21_gravity.py.

    calibration(p)                   (4κ mod p, (4κ)² mod p) on p = 4κ + 1: (p − 1, 1)
    newton_register(p)               G = 2κ, c² = 2κ + 1: the five register relations of 21:C2 as booleans
    hbar_root(p, g)                  ħ = g^κ, r = ħ c²: ħ² = −1, r² = κ, 2r = ħ
    channel_q4(p)                    the residues in both cycles are exactly the quarter-turn core {x : x⁴ = 1}
    cover_triangle(gamma, beta)      the PPN triangle: 2γ − β = 1 and γ = 1 give β = 1
    defect(nA, nB, wA, wB)           L, q, a, T_def of the relative-cycle defect
    first_return(L, a)               the least t ≥ 1 with t·a ≡ 0 (mod L)
    pair_tally_identity(p, z)        (z − w)² = −(2 − z − w)(2 + z + w) on z ∈ 𝔽_p^×, w = z⁻¹
    antisymmetric_dimension(d)       the antisymmetric Laurent polynomials of degree ≤ d form a d-dimensional space
    locked_sum(n, m)                 |Σ_m z|² = m² on the locked word; the exact mean of |Σ|² over all n^m phase words is m
    gauss_law(J, region)             the divergence summed over a region equals the boundary flux (antisymmetric J)
    compression_identity(n, sector)  P − KᵀK = CᵀC on the cyclic shift with a sector projector (exact rationals)
    offset_return(n, sector)         the sector's weight splits into the kept and the leaked parts exactly; Uⁿ = I returns the leak
    Series                           truncated power series over the rationals (exp, product, quotient, power)
    pn_coefficients()                e^{−2U} against ((1 − U/2)/(1 + U/2))², e^{2U} against (1 + U/2)⁴, to U³
    two_body_1pn()                   the two-body coefficients through 1PN agree, the cross term 4 U₁U₂ included
    pn_orbit_inputs()                the 2PN orbit-equation inputs: δc₂'s leading term and δc₃ = 5/6, the apsidal sum
    static_profile_coefficients()    u(r) = Gm/r (1 + (Gm/r²)²/30 + (Gm/r²)⁴/120 + …): the exact series of the profile
    scale_invariant_exponent(lo, hi) the n with (λk)^{n+3}/k^{n+3} = 1 at every dilation λ and drive k: −3 alone (n_s = 1)
    dilution(m, s)                   (m/√Ω)² = m²/Ω on Ω = s²: the coupling of two masses m is their count over Ω
    frobenius_trace(p, nu, m, a, b)  the Frobenius pairing of m (w ⊗ w) equals m N(w)
    single_arrow(p, nu)              the Frobenius is the conjugation; on the circle the conjugate branch is the orbit reversed
    pair_energy_sign(n)              the exact Dirichlet Green's function is positive: like-signed sources attract
    registration_root(w, s)          wη² − 2η + w = 0 for η = (1 − s)/w with s² = 1 − w², over the rationals
    chebyshev_weight(L, d, w)        q_{L,d} = (U_{d−1} + U_{L−d−1})/U_{L−1} at 1/w against the tridiagonal solve
    christoffel(a, b)                the registration word at rate a/b: a marks per recurrence, two-valued gaps
    largest_remainder(weights, B)    the allocation of B events to the weights, discrepancy ≤ 1
    event_orbit(a, b, gN)            the a registered events at g_N/f sum to the window total b·g_N
    kesten_control(Om, g, th)        raw-orbit prefix counts break unit discrepancy: the theorem is over complete recurrences
    stratum_split(B)                 the per-stratum tallies on Ω = 641 are 8 × the Galois-symmetric coefficients
    binding(N, m1, m2)               superposition, cut flux = m₁ + m₂, bilinear energy, the registered clock
    fold_return(p)                   the period-averaged exterior return through the fold is the uniform floor
"""
import random
from fractions import Fraction
from itertools import product
from math import gcd

from frc.extension import Ext


# ---- the register on a frame (21:A1, C2, C5, C16, X1) ------------------------------------------------------------
def calibration(p):
    """The calibration congruence on p = 4κ + 1: 4κ ≡ −1 and (4κ)² ≡ 1."""
    k = (p - 1) // 4
    return (4 * k) % p == p - 1 and (4 * k) ** 2 % p == 1


def newton_register(p):
    """The register value G = 2κ on p = 4κ + 1: 2G ≡ −1, (−2)G ≡ 1, (2·4κ)G ≡ 1, 2c² ≡ 1 with c² = 2κ + 1, G ≡ −c²."""
    k = (p - 1) // 4
    G, c2 = 2 * k, 2 * k + 1
    return (2 * G % p == p - 1, (-2 * G) % p == 1, (2 * 4 * k * G) % p == 1, (2 * c2) % p == 1, (G + c2) % p == 0)


def hbar_root(p, g):
    """ħ = g^κ: ħ² ≡ −1; r = ħ c² has r² ≡ κ and 2r ≡ ħ."""
    k = (p - 1) // 4
    h = pow(g, k, p)
    r = h * (2 * k + 1) % p
    return (h * h % p == p - 1, r * r % p == k % p, 2 * r % p == h)


def channel_q4(p):
    """The residues of 𝔽_p^× in both C_{p−1} and C_{2(p+1)} (x^{p−1} = 1 and x^{2(p+1)} = 1) are exactly those with x⁴ = 1."""
    both = {x for x in range(1, p) if pow(x, p - 1, p) == 1 and pow(x, 2 * (p + 1), p) == 1}
    q4 = {x for x in range(1, p) if pow(x, 4, p) == 1}
    return both == q4 and len(q4) == 4


def closed_chart(p, g):
    """The closed chart on the frame of 𝔽_p (p = 4κ + 1, g a generator of the multiplicative cycle): every nonzero residue
    returns after the full cycle p − 1 = 4κ chronons, the generator after no shorter run, the half cycle is −1; and the
    cycle's register is the calibration 4κ ≡ −1, (4κ)² ≡ 1 (21:X1)."""
    k = (p - 1) // 4
    full = all(pow(x, 4 * k, p) == 1 for x in range(1, p))
    order = pow(g, 4 * k, p) == 1 and all(pow(g, j, p) != 1 for j in range(1, 4 * k))
    half = pow(g, 2 * k, p) == p - 1
    register = (4 * k) % p == p - 1 and (4 * k) ** 2 % p == 1
    return full and order and half and register


def curvature_datum(S):
    """The two readings of the totality datum Ω = 4S + 1 on the chart, exact over ℚ with π a formal symbol (a quantity is a
    rational coefficient and a power of π): the de Sitter entropy S = π r_H² (Planck units) gives r_H² = (S/π); the
    curvature Λ = 3/r_H² = (3/S)π, so Λ(Ω − 1) = 12π and ΛS = 3π; the chronon τ = 2π r_H/(4S c) has τ² = (π/4S) t_P² (the
    paper's (√π/2) t_P/√S) and the horizon is r_H/(cτ) = 2S/π chronons (21:X1). Returns (ok, Λ/π, τ²/(π t_P²))."""
    S = Fraction(S); omega = 4 * S + 1
    rh2 = (S, -1)                                               # r_H² = S π⁻¹
    lam = (3 / rh2[0], -rh2[1])                                 # Λ = 3/r_H²
    product = (lam[0] * (omega - 1), lam[1])                    # Λ (Ω − 1)
    lam_s = (lam[0] * S, lam[1])                                # Λ S
    tau2 = (Fraction(4) * rh2[0] / (16 * S * S), 2 + rh2[1])    # τ² = (2π)² r_H² / (4S)²
    ratio2 = (rh2[0] / tau2[0], rh2[1] - tau2[1])               # (r_H/τ)²
    ok = product == (12, 1) and lam_s == (3, 1) and tau2 == (1 / (4 * S), 1) and ratio2 == (4 * S * S, -2)
    return ok, lam[0], tau2[0]


# ---- the cover triangle (21:C25, C7, C8) ---------------------------------------------------------------------------
def cover_triangle(gamma, beta):
    """The triangle: with 2γ − β = 1 and γ = 1, β = 1; the deviation ⅔(2γ − β − 1) vanishes."""
    forced = 2 * gamma - beta == 1
    return forced and gamma == 1 and beta == 1 and Fraction(2, 3) * (2 * gamma - beta - 1) == 0


# ---- the relative-cycle defect (21:C21) ----------------------------------------------------------------------------
def defect(nA, nB, wA, wB):
    """Two cycles of orders nA, nB with winding rates wA, wB: L = lcm, q = gcd, the defect a = wB L/nB − wA L/nA (mod L),
    and the recurrence period T_def = (L/q)/gcd(L/q, a)."""
    L = nA * nB // gcd(nA, nB)
    q = gcd(nA, nB)
    a = (wB * L // nB - wA * L // nA) % L
    T = (L // q) // gcd(L // q, a)
    return L, q, a, T


def first_return(L, a):
    """The least t ≥ 1 with t·a ≡ 0 (mod L): the period of the shift by a on the cycle of order L."""
    t = 1
    while (t * a) % L:
        t += 1
    return t


# ---- the pair tally (21:C21, C1) -----------------------------------------------------------------------------------
def antisymmetric_dimension(d):
    """The antisymmetric Laurent polynomials J(z) = Σ_{|k|≤d} c_k z^k with J(z⁻¹) = −J(z): the constraints c_{−k} = −c_k
    and c₀ = 0 as a matrix over ℚ on the 2d + 1 coefficients, its nullity by exact elimination. The space has dimension
    d (basis z^k − z^{−k}): at d = 1 the sine mode (z − z⁻¹)/2i is the unique antisymmetric current up to scale, the
    minimal degree of the pair-tally current (21:C21); higher odd harmonics exist for d ≥ 2."""
    cols = 2 * d + 1                                               # c_{−d}, …, c_d
    rows = [[Fraction(0)] * cols for _ in range(d + 1)]
    rows[0][d] = Fraction(1)                                       # c₀ = 0
    for k in range(1, d + 1):
        rows[k][d + k] = Fraction(1); rows[k][d - k] = Fraction(1)   # c_k + c_{−k} = 0
    rank, lead = 0, 0
    M = [r[:] for r in rows]
    for col in range(cols):
        piv = next((i for i in range(rank, len(M)) if M[i][col] != 0), None)
        if piv is None: continue
        M[rank], M[piv] = M[piv], M[rank]
        M[rank] = [x / M[rank][col] for x in M[rank]]
        for i in range(len(M)):
            if i != rank and M[i][col] != 0:
                M[i] = [a - M[i][col] * b for a, b in zip(M[i], M[rank])]
        rank += 1
    return cols - rank


def pair_tally_identity(p, z):
    """On z ∈ 𝔽_p^× with mate w = z⁻¹: E = 2 − z − w, W = 2 + z + w, E + W = 4 and (z − w)² = −E·W."""
    w = pow(z, p - 2, p)
    E, W = (2 - z - w) % p, (2 + z + w) % p
    return (E + W) % p == 4 % p and (z - w) ** 2 % p == (-E * W) % p


# ---- the locked sum against the incoherent ensemble (21:C1) --------------------------------------------------------
def locked_sum(n, m):
    """m cells of one phase on the n-cycle sum to m·z, |Σ|² = m²; over all n^m phase words the exact mean of |Σ ζ^k|²
    is m (the incoherent √m), computed in the cyclotomic ring ℤ[ζ_n] as an integer identity: Σ_words |Σ_j ζ^{k_j}|² = m·n^m."""
    # |Σ_j ζ^{k_j}|² = Σ_{j,l} ζ^{k_j − k_l}, an element of ℤ[ζ_n] recorded as the multiset of residues k_j − k_l; when
    # the nonzero residues appear equally often it equals counts[0] − counts[1], since Σ_{r≠0} ζ^r = −1
    def residues(words):
        counts = [0] * n
        for word in words:
            for j in range(m):
                for l in range(m):
                    counts[(word[j] - word[l]) % n] += 1
        return counts if len(set(counts[1:])) == 1 else None
    one = residues([(0,) * m])                                     # the locked word: every residue 0, |Σ|² = m²
    locked = one[0] - one[1] if one else None
    counts = residues(product(range(n), repeat=m))                 # all n^m words: Σ_words |Σ|² = counts[0] − counts[1]
    mean = Fraction(counts[0] - counts[1], n ** m) if counts else None
    return locked, mean


# ---- the Gauss law from transfer antisymmetry (21:C11) --------------------------------------------------------------
def gauss_law(J, region):
    """J[x][y] = −J[y][x] the link currents on n sites. The divergence Σ_y J[x][y] summed over the region equals the
    flux through its boundary, Σ_{x ∈ R} Σ_{y ∉ R} J[x][y]: the interior links cancel in pairs."""
    n = len(J)
    assert all(J[x][y] == -J[y][x] for x in range(n) for y in range(n))
    div = sum(J[x][y] for x in region for y in range(n))
    flux = sum(J[x][y] for x in region for y in range(n) if y not in region)
    return div == flux


# ---- the compression identity (21:C21, C22) --------------------------------------------------------------------------
def _matmul(A, B):
    n = len(A)
    return [[sum(A[i][k] * B[k][j] for k in range(n)) for j in range(n)] for i in range(n)]


def compression_identity(n, sector):
    """On the cyclic shift U of ℤ_n with the sector projector P: K = P U P, C = (I − P) U P, and P − KᵀK = CᵀC exactly."""
    U = [[Fraction(int(j == (i - 1) % n)) for j in range(n)] for i in range(n)]
    P = [[Fraction(int(i == j and i in sector)) for j in range(n)] for i in range(n)]
    I = [[Fraction(int(i == j)) for j in range(n)] for i in range(n)]
    IP = [[I[i][j] - P[i][j] for j in range(n)] for i in range(n)]
    K = _matmul(P, _matmul(U, P))
    C = _matmul(IP, _matmul(U, P))
    T = lambda A: [[A[j][i] for j in range(n)] for i in range(n)]
    KK, CC = _matmul(T(K), K), _matmul(T(C), C)
    lhs = [[P[i][j] - KK[i][j] for j in range(n)] for i in range(n)]
    return lhs == CC


def offset_return(n, sector, seed=43):
    """The drive on the cycle ℤ_n (the cyclic shift U) with the sector projector P, over ℚ: for random rational vectors
    ψ the sector's weight splits exactly into what the step keeps in the sector and what it moves to the offset sector,
    ‖Pψ‖² = ‖PUPψ‖² + ‖(1 − P)UPψ‖² (the compression identity as a quadratic form); the step conserves the whole
    weight, ‖Uψ‖² = ‖ψ‖²; and U is a permutation of finite order, Uⁿ = I, so what left the sector returns: the offset
    sector confines the leaked data exactly (21:X3, C21). Returns (ok, the order of U)."""
    rng = random.Random(seed)
    U = [[Fraction(int(j == (i - 1) % n)) for j in range(n)] for i in range(n)]
    apply = lambda A, v: [sum(A[i][j] * v[j] for j in range(n)) for i in range(n)]
    proj = lambda v: [v[i] if i in sector else Fraction(0) for i in range(n)]
    comp = lambda v: [Fraction(0) if i in sector else v[i] for i in range(n)]
    w = lambda v: sum(x * x for x in v)
    ok = True
    for _ in range(5):
        psi = [Fraction(rng.randint(-9, 9), rng.randint(1, 5)) for _ in range(n)]
        up = apply(U, proj(psi))
        ok &= w(proj(psi)) == w(proj(up)) + w(comp(up)) and w(apply(U, psi)) == w(psi)
    power = [row[:] for row in U]; order = 1
    while power != [[Fraction(int(i == j)) for j in range(n)] for i in range(n)]:
        power = _matmul(U, power); order += 1
    e = [Fraction(int(i == min(sector))) for i in range(n)]
    v = e
    for _ in range(order): v = apply(U, v)
    ok &= order == n and v == e
    return ok, order


# ---- exact rational power series (21:C7, C8, C23, P6) ---------------------------------------------------------------
class Series:
    """A truncated power series Σ_{k<n} c_k U^k over the rationals, n the order kept."""

    def __init__(self, coeffs, n):
        self.n = n
        self.c = [Fraction(x) for x in coeffs][:n] + [Fraction(0)] * max(0, n - len(coeffs))

    @classmethod
    def var(cls, n, scale=1):
        return cls([0, scale], n)

    @classmethod
    def const(cls, a, n):
        return cls([a], n)

    def __add__(self, o):
        o = o if isinstance(o, Series) else Series.const(o, self.n)
        return Series([a + b for a, b in zip(self.c, o.c)], self.n)

    def __sub__(self, o):
        o = o if isinstance(o, Series) else Series.const(o, self.n)
        return Series([a - b for a, b in zip(self.c, o.c)], self.n)

    def __mul__(self, o):
        if not isinstance(o, Series):
            return Series([a * Fraction(o) for a in self.c], self.n)
        out = [Fraction(0)] * self.n
        for i, a in enumerate(self.c):
            if a == 0: continue
            for j, b in enumerate(o.c):
                if i + j < self.n: out[i + j] += a * b
        return Series(out, self.n)

    __rmul__ = __mul__
    __radd__ = __add__

    def __rsub__(self, o):
        return Series.const(o, self.n) - self

    def __neg__(self):
        return Series([-a for a in self.c], self.n)

    def inverse(self):
        """1/self, needing a nonzero constant term."""
        a0 = self.c[0]
        assert a0 != 0
        out = [Fraction(0)] * self.n
        out[0] = 1 / a0
        for k in range(1, self.n):
            out[k] = -sum(self.c[j] * out[k - j] for j in range(1, k + 1)) / a0
        return Series(out, self.n)

    def __truediv__(self, o):
        return self * o.inverse()

    def pow(self, k):
        out = Series.const(1, self.n)
        for _ in range(k): out = out * self
        return out

    @classmethod
    def exp(cls, s):
        """exp of a series with zero constant term."""
        assert s.c[0] == 0
        out, term = cls.const(1, s.n), cls.const(1, s.n)
        for k in range(1, s.n):
            term = term * s * Fraction(1, k)
            out = out + term
        return out

    def __eq__(self, o):
        return isinstance(o, Series) and self.n == o.n and self.c == o.c


def pn_coefficients(n=5):
    """The exponential metric against the isotropic Schwarzschild form, exact to U^{n−1}: A = e^{−2U} and
    A_S = ((1 − U/2)/(1 + U/2))² agree through U² and differ by U³/6; B = e^{2U} and B_S = (1 + U/2)⁴ agree through U
    and differ by U²/2 — the PPN parameters β = γ = 1 read off A and B (21:C8, P6, C7)."""
    U = Series.var(n)
    A = Series.exp(-2 * U)
    AS = ((1 - U * Fraction(1, 2)) / (1 + U * Fraction(1, 2))).pow(2)
    B = Series.exp(2 * U)
    BS = (1 + U * Fraction(1, 2)).pow(4)
    dA, dB = (A - AS).c, (B - BS).c
    beta = A.c[2] / 2                                          # g00 = −(1 − 2U + 2βU²): β = A.c[2]/2
    gamma = B.c[1] / 2                                         # g_ij = 1 + 2γU
    return {"dA": dA, "dB": dB, "beta": beta, "gamma": gamma,
            "ok": dA[:3] == [0, 0, 0] and dA[3] == Fraction(1, 6) and dB[:2] == [0, 0] and dB[2] == Fraction(1, 2)
                  and beta == 1 and gamma == 1}


def two_body_1pn(n=3):
    """Through 1PN the two-body coefficients on the superposed potential U = t(U₁ + U₂) coincide with the isotropic
    Schwarzschild form: A agrees through t², the cross term 4U₁U₂ included; B through t (21:C23)."""
    # expand in t with U₁ = 1, U₂ = u a second parameter: coefficients polynomial in u are tracked by two evaluations
    ok = True
    for u in (Fraction(1), Fraction(3, 7), Fraction(-2, 5)):
        T = Series.var(n + 1, scale=1 + u)                     # U = t (U₁ + U₂), U₁ = 1, U₂ = u
        A = Series.exp(-2 * T); AS = ((1 - T * Fraction(1, 2)) / (1 + T * Fraction(1, 2))).pow(2)
        B = Series.exp(2 * T); BS = (1 + T * Fraction(1, 2)).pow(4)
        ok &= A.c[:3] == AS.c[:3] and B.c[:2] == BS.c[:2] and A.c[2] == 2 * (1 + u) ** 2
    return ok


def pn_orbit_inputs(n=4):
    """The orbit equation's 2PN inputs, exact in x = Mw: B/A = e^{4x} against the Schwarzschild reading
    e^{4x − x²/2 + x³/3}, and B = e^{2x} against e^{2x − x²/2 + x³/6}; the differences are x²/2 + 5x³/3 and
    x²/2 + 5x³/6, so δc₂ = (E² − 1)/2 · M²/L² has leading term ε M²/L² at E = 1 + ε and δc₃ = (5/3 − 5/6) M³/L² = 5/6 M³/L²;
    the apsidal sum 5/2 − (1 − e²)/2 = 2 + e²/2 as a polynomial identity (21:P6, C8)."""
    x = Series.var(n)
    half, third, sixth = Fraction(1, 2), Fraction(1, 3), Fraction(1, 6)
    dBA = Series.exp(4 * x) - Series.exp(4 * x - x.pow(2) * half + x.pow(3) * third)
    dB = Series.exp(2 * x) - Series.exp(2 * x - x.pow(2) * half + x.pow(3) * sixth)
    c2 = dBA.c[2] - dB.c[2]                                     # the ε⁰ term of δc₂ at E = 1: must vanish
    c2_eps = 2 * dBA.c[2]                                       # E² − 1 = 2ε + ε²: the ε coefficient
    c3 = dBA.c[3] - dB.c[3]
    apsidal = all(Fraction(5, 2) - (1 - e * e) / 2 == 2 + e * e / 2 for e in (Fraction(0), Fraction(1, 7), Fraction(878, 10000)))
    return {"dBA": dBA.c[:4], "dB": dB.c[:4], "c2_const": c2, "c2_eps": c2_eps, "c3": c3,
            "ok": c2 == 0 and c2_eps == 1 and c3 == Fraction(5, 6) and apsidal and dBA.c[:2] == [0, 0] and dB.c[:2] == [0, 0]}


def static_profile_coefficients(k=3):
    """u(r) = ∫_r^∞ arcsin(Gm/s²) ds with arcsin x = Σ_j a_j x^{2j+1}, a_j = (2j)!/(4^j (j!)² (2j+1)): the term
    a_j Gm^{2j+1} ∫_r^∞ s^{−2(2j+1)} ds = a_j Gm^{2j+1}/((4j+1) r^{4j+1}), so u = Gm/r (1 + (Gm/r²)²/30 + (Gm/r²)⁴/120 + …)."""
    from math import factorial
    out = []
    for j in range(k):
        a = Fraction(factorial(2 * j), 4 ** j * factorial(j) ** 2 * (2 * j + 1))
        out.append(a / (4 * j + 1))
    return out


def scale_invariant_exponent(lo=-6, hi=3, dilations=(Fraction(2), Fraction(3, 2), Fraction(1, 3)), drives=(1, 2, 5)):
    """Δ²(k) = k³ P(k) ∝ k^{n+3} for P ∝ kⁿ: the dilation k ↦ λk multiplies Δ² by (λk)^{n+3}/k^{n+3}, evaluated exactly
    over ℚ for every integer n ∈ [lo, hi), λ ∈ {2, 3/2, 1/3} and k ∈ {1, 2, 5}; returns the n whose ratio is 1 at every
    (λ, k) — the dilation fixed points, n = −3 alone, n_s = n + 4 = 1 (21:C18) — and the ratios, λ^{n+3}."""
    ratios = {n: {(lam, k): (lam * k) ** (n + 3) / Fraction(k) ** (n + 3) for lam in dilations for k in drives} for n in range(lo, hi)}
    fixed = [n for n in range(lo, hi) if all(r == 1 for r in ratios[n].values())]
    return fixed, ratios


def dilution(m, s):
    """With Ω = s² and the Planck mass √Ω = s the coupling of two masses m, (m/√Ω)², equals m²/Ω exactly (21:X8, C5)."""
    m, s = Fraction(m), Fraction(s)
    return (m / s) ** 2 == m * m / (s * s)


# ---- the single arrow (21:C3, 00:E3) ----------------------------------------------------------------------------------
def single_arrow(p, nu):
    """On 𝔽_{p²} = 𝔽_p(√ν): the Frobenius z ↦ z^p is the conjugation a + b√ν ↦ a − b√ν on every element (exhaustive); on the
    norm-one circle (order p + 1) the conjugate is the inverse, the conjugate orbit of a generator g is its orbit run
    backwards (conj(g)^k = g^{−k}), and the conjugation is no translation of the circle: it fixes ±1 alone, while z ↦ hz
    fixes nothing (h ≠ 1) or everything. The time-reversed clock is the Frobenius branch, not a step of the drive (21:C3).
    Returns (ok, the circle's order, the fixed points of the conjugation)."""
    K = Ext(p, nu)
    frob = all(K.pow(z, p) == K.conj(z) for z in K.elements())
    circle = K.norm_one()
    one = (1, 0)
    inverse = all(K.mul(z, K.conj(z)) == one for z in circle)
    order = lambda z: next(k for k in range(1, p + 2) if K.pow(z, k) == one)
    g = next(z for z in circle if order(z) == p + 1)
    orbit = [K.pow(g, k) for k in range(p + 1)]
    reversed_ = all(K.pow(K.conj(g), k) == orbit[(-k) % (p + 1)] for k in range(p + 1))
    fixed = [z for z in circle if K.conj(z) == z]
    translation = any(all(K.conj(z) == K.mul(h, z) for z in circle) for h in circle)
    ok = frob and len(circle) == p + 1 and inverse and reversed_ and sorted(fixed) == sorted([one, (p - 1, 0)]) and not translation
    return ok, len(circle), fixed


def pair_energy_sign(n):
    """The sign of the pair energy on the Dirichlet grid {1..n}³ (the interior of a box, the field zero on its faces):
    the lattice Laplacian L = 6 − adjacency inverted exactly over ℚ gives the Green's function G = L⁻¹, entrywise positive;
    the energy minimum of sources m₁, m₂ at sites a, b is −½ (m₁² G_aa + 2 m₁ m₂ G_ab + m₂² G_bb), whose cross term
    −m₁ m₂ G_ab lowers the energy exactly when the signs agree. Like-signed sources attract (21:C3, 00:E3); the field
    equation's stiffness is the Laplacian's, the Fierz–Pauli functional's scalar sector. Returns (ok, G_ab, G_aa)."""
    sites = [(x, y, z) for x in range(n) for y in range(n) for z in range(n)]
    idx = {s: i for i, s in enumerate(sites)}
    N = len(sites)
    L = [[Fraction(0)] * N for _ in range(N)]
    for (x, y, z), i in idx.items():
        L[i][i] = Fraction(6)
        for d in ((1, 0, 0), (-1, 0, 0), (0, 1, 0), (0, -1, 0), (0, 0, 1), (0, 0, -1)):
            j = idx.get((x + d[0], y + d[1], z + d[2]))
            if j is not None: L[i][j] = Fraction(-1)
    # G = L⁻¹ by Gauss–Jordan elimination over ℚ
    M = [row[:] + [Fraction(int(i == j)) for j in range(N)] for i, row in enumerate(L)]
    for col in range(N):
        piv = next(r for r in range(col, N) if M[r][col] != 0)
        M[col], M[piv] = M[piv], M[col]
        inv = 1 / M[col][col]
        M[col] = [v * inv for v in M[col]]
        for r in range(N):
            if r != col and M[r][col] != 0:
                f = M[r][col]; M[r] = [a - f * b for a, b in zip(M[r], M[col])]
    G = [row[N:] for row in M]
    positive = all(G[i][j] > 0 for i in range(N) for j in range(N))
    symmetric = all(G[i][j] == G[j][i] for i in range(N) for j in range(i))
    identity = all(sum(L[i][k] * G[k][j] for k in range(N)) == (1 if i == j else 0) for i in range(N) for j in range(N))
    a, b = idx[(0, 0, 0)], idx[(n - 1, n - 1, n - 1)]
    energy = lambda m1, m2: -Fraction(1, 2) * (m1 * m1 * G[a][a] + 2 * m1 * m2 * G[a][b] + m2 * m2 * G[b][b])
    cross = lambda m1, m2: energy(m1, m2) - energy(m1, 0) - energy(0, m2)
    like = all(cross(m1, m2) < 0 for m1, m2 in ((1, 1), (2, 3), (-1, -1), (-3, -2)))
    unlike = all(cross(m1, m2) > 0 for m1, m2 in ((1, -1), (2, -3), (-1, 1)))
    ok = positive and symmetric and identity and like and unlike and cross(1, 1) == -G[a][b]
    return ok, G[a][b], G[a][a]


# ---- the master's block E: the completion, the floor's faces and the fold (00:E4, E5, E10) ------------------------------
def exponential_reading(p):
    """The exponential reading is the character, and the unique one: on 𝔽_p every nonzero c composes, c^(a+b) = c^a c^b for
    all a, b below the full cycle (exhaustive), and a function of the drive's steps with the composition law and f(0) = 1
    is c^a with c = f(1), rebuilt step by step from f(1) alone (00:E4, 21:C11)."""
    n = p - 1
    composes = all(pow(c, a + b, p) == pow(c, a, p) * pow(c, b, p) % p for c in range(1, p) for a in range(n) for b in range(n))
    unique = True
    for c in range(1, p):
        f = [1]
        for a in range(2 * n): f.append(f[-1] * c % p)          # the law f(a + 1) = f(a) f(1) rebuilds f from f(1)
        unique &= all(f[a] == pow(c, a, p) for a in range(2 * n + 1))
    return composes and unique


def cut_ordering(L, M):
    """The operational cut between the slip core and the mass, exact over ℚ: with r_* = √M and r_f = 2M/L (L = ln Ω),
    r_*² < r_f² reads L² M < (2M)² and holds iff L² < 4M, and r_f < M reads 2M < L M, true once L > 2 (00:E5, E10).
    Returns (ordered, the threshold (L/2)²)."""
    L, M = Fraction(L), Fraction(M)
    ordered = L * L * M < (2 * M) * (2 * M) and 2 * M < L * M
    assert ordered == (L * L < 4 * M and L > 2)
    return ordered, (L / 2) ** 2


def fold_collision(p, g):
    """The two chart branches are two Carrier data (00:E10): on 𝔽_p with the generator g, for every ordered pair of
    distinct nonzero positions r₁ ≠ r₂ the residue products r₁ g^Δ and r₂ coincide at exactly one lift Δ below the full
    cycle, while the pairs (r, g^{−Δ}) never coincide for distinct r. Exhaustive. Returns (ok, the number of pairs)."""
    n = p - 1
    pairs = 0; ok = True
    powers = [pow(g, d, p) for d in range(n)]
    for r1 in range(1, p):
        for r2 in range(1, p):
            if r1 == r2: continue
            pairs += 1
            ok &= sum(1 for d in range(n) if r1 * powers[d] % p == r2) == 1
    inv = [pow(g, (-d) % n, p) for d in range(n)]
    ok &= len({(r, inv[d]) for r in range(1, p) for d in range(n)}) == (p - 1) * n
    return ok, pairs


def fold_return_general(p, N, NI, seed=5):
    """The fold-return identity for an arbitrary interior chart (00:E10): on the chain C_N over 𝔽_p with the interior block
    I = {0..NI−1} and the exterior E, a random invertible block F_I (identity on E) gives P_E F U^n F⁻¹ P_E = P_E U^n P_E for
    every n < N, term by term; the period sum Σ_n P_E U^n P_E is the all-ones block J_E on E (the uniform floor N⁻¹ J_E);
    and U^N = I. Returns ok."""
    rng = random.Random(seed)
    I = [[int(i == j) for j in range(N)] for i in range(N)]
    U = [[int(j == (i - 1) % N) for j in range(N)] for i in range(N)]
    mm = lambda A, B: [[sum(A[i][k] * B[k][j] for k in range(N)) % p for j in range(N)] for i in range(N)]
    def inverse(A):
        M = [[A[i][j] % p for j in range(N)] + [int(i == j) for j in range(N)] for i in range(N)]
        for c in range(N):
            piv = next((r for r in range(c, N) if M[r][c]), None)
            if piv is None: return None
            M[c], M[piv] = M[piv], M[c]
            iv = pow(M[c][c], p - 2, p); M[c] = [v * iv % p for v in M[c]]
            for r in range(N):
                if r != c and M[r][c]:
                    f = M[r][c]; M[r] = [(a - f * b) % p for a, b in zip(M[r], M[c])]
        return [row[N:] for row in M]
    while True:
        F = [[0] * N for _ in range(N)]
        for j in range(NI):
            for k in range(NI): F[j][k] = rng.randrange(p)
        for j in range(NI, N): F[j][j] = 1
        Fi = inverse(F)
        if Fi is not None: break
    PE = [[int(i == j and i >= NI) for j in range(N)] for i in range(N)]
    Un = I; acc = [[0] * N for _ in range(N)]; ok = True
    for n in range(N):
        folded = mm(PE, mm(F, mm(Un, mm(Fi, PE))))
        bare = mm(PE, mm(Un, PE))
        ok &= folded == bare
        acc = [[(acc[i][j] + bare[i][j]) % p for j in range(N)] for i in range(N)]
        Un = mm(U, Un)
    ok &= Un == I
    ok &= all(acc[i][j] == (1 if i >= NI and j >= NI else 0) for i in range(N) for j in range(N))
    return ok


# ---- the dust tensor's trace (21:C6) ----------------------------------------------------------------------------------
def frobenius_trace(p, nu, m, a, b):
    """w = a + bη in 𝔽_p[η]/(η² − ν): the Frobenius pairing of m(w ⊗ w), m a² − ν m b², equals m N(w)."""
    K = Ext(p, nu)
    N = K.norm((a, b))
    return (m * a * a - nu * m * b * b) % p == (m * N) % p


# ---- the registration root (21:C19) -----------------------------------------------------------------------------------
def registration_root(w, s):
    """With s² = 1 − w² and w ≠ 0 (rationals), η = (1 − s)/w solves wη² − 2η + w = 0 exactly."""
    w, s = Fraction(w), Fraction(s)
    assert s * s == 1 - w * w and w != 0
    eta = (1 - s) / w
    return w * eta * eta - 2 * eta + w == 0, eta


# ---- the Chebyshev two-boundary weight (21:C19) ---------------------------------------------------------------------
def _cheb_u(n, x):
    a, b = Fraction(1), 2 * x
    if n == 0: return a
    if n == 1: return b
    for _ in range(n - 1): a, b = b, 2 * x * b - a
    return b


def _tridiagonal(L, w):
    """q_0 = q_L = 1, q_j = (w/2)(q_{j−1} + q_{j+1}): the killed walk's masking weights, solved exactly."""
    n = L + 1
    M = [[Fraction(0)] * (n + 1) for _ in range(n)]
    M[0][0] = Fraction(1); M[0][n] = Fraction(1); M[L][L] = Fraction(1); M[L][n] = Fraction(1)
    for j in range(1, L):
        M[j][j] = Fraction(1); M[j][j - 1] = -w / 2; M[j][j + 1] = -w / 2
    for c in range(n):
        piv = next(r for r in range(c, n) if M[r][c] != 0)
        M[c], M[piv] = M[piv], M[c]
        M[c] = [v / M[c][c] for v in M[c]]
        for r in range(n):
            if r != c and M[r][c] != 0:
                f = M[r][c]; M[r] = [vr - f * vc for vr, vc in zip(M[r], M[c])]
    return [M[j][n] for j in range(n)]


def chebyshev_weight(L, d, w):
    """q_{L,d} = (U_{d−1}(1/w) + U_{L−d−1}(1/w))/U_{L−1}(1/w) against the tridiagonal solve."""
    w = Fraction(w)
    x = 1 / w
    return _tridiagonal(L, w)[d] == (_cheb_u(d - 1, x) + _cheb_u(L - d - 1, x)) / _cheb_u(L - 1, x)


# ---- the registration words and the readout (21:C7, C19, C21) ---------------------------------------------------------
def christoffel(a, b):
    """The registration word at rate a/b: exactly a marks per recurrence b, the gaps two-valued ⌊b/a⌋, ⌈b/a⌉ with mean b/a."""
    marks = [((k + 1) * a) // b - (k * a) // b for k in range(b)]
    idx = [k for k in range(b) if marks[k] == 1]
    gaps = [((idx[(i + 1) % len(idx)] - idx[i]) % b) or b for i in range(len(idx))]
    return sum(marks) == a and set(gaps) <= {b // a, -(-b // a)} and Fraction(sum(gaps), len(gaps)) == Fraction(b, a)


def largest_remainder(weights, B):
    """The largest-remainder allocation of B events to the weights: integer provisions with discrepancy ≤ 1."""
    weights = [Fraction(w) for w in weights]
    prov = [int(B * w) for w in weights]
    resid = B - sum(prov)
    order = sorted(range(len(weights)), key=lambda j: (B * weights[j]) - prov[j], reverse=True)
    for j in order[:resid]: prov[j] += 1
    return prov, all(abs(prov[j] - B * weights[j]) <= 1 for j in range(len(weights)))


def ledger_identity(m, g, N, T):
    """The registered-inertia identity over ℚ: with f = N/T the impulse m g T equals (f m)(g/f) T."""
    f = Fraction(N, T)
    return (f * m) * (Fraction(g) / f) * T == m * Fraction(g) * T


def event_orbit(a, b, gN):
    """The event-based orbit on the registration word at rate f = a/b: each of the a registered events of the window
    carries the impulse g_N/f, and their sum over the word is the window total b·g_N exactly (21:C19's registered
    balance over ℚ); returns (the identity, the registered count)."""
    f, gN = Fraction(a, b), Fraction(gN)
    marks = [((k + 1) * a) // b - (k * a) // b for k in range(b)]
    registered = sum(gN / f for e in marks if e)
    return registered == gN * b, sum(marks)


def kesten_control(Om=641, g=3, th=Fraction(23, 54), B_max=200):
    """The negative control of the counting theorem: along the raw drive orbit g^k mod Ω the prefix count of values
    below the threshold th·Ω is not discrepancy-bounded (Kesten: bounded discrepancy only for thresholds in the orbit's
    own lattice); returns the first prefix length B at which |count − B·th| ≥ 2, or None if none below B_max — the
    theorem is therefore stated over complete recurrences, where the counts are forced (21:C19)."""
    x, count = 1, 0
    for B in range(1, B_max):
        if x < th * Om: count += 1
        x = x * g % Om
        if abs(count - B * th) >= 2: return B
    return None


def stratum_split(B, Om=641, g=3):
    """The per-stratum split of the readout's worked instance (Ω = 641, g = 3): on the dial of the eight primitive
    eighth roots the values r_j = ζ⁸^{2j+1} + ζ⁸^{−(2j+1)} are ±√2 and sum to zero; over the 2^B strings the tallies
    Σ_j Π_i (2 ± r_j) computed in ℤ[√2] are 8 × the Galois-symmetric coefficient (the √2 part cancels), total 4^B·8, and
    the residues mod 641 agree (21:C19, C21)."""
    r = next(x for x in range(1, Om) if x * x % Om == 2)
    z8 = pow(g, (Om - 1) // 8, Om)
    dial = [(pow(z8, 2 * j + 1, Om) + pow(z8, -(2 * j + 1), Om)) % Om for j in range(8)]
    dial_ok = set(dial) == {r, Om - r} and sum(dial) % Om == 0
    mul = lambda x, y: (x[0] * y[0] + 2 * x[1] * y[1], x[0] * y[1] + x[1] * y[0])      # ℤ[√2] as (rational, √2) parts
    signs = [1 if d == r else -1 for d in dial]
    ok, total = True, 0
    for string in product((0, 1), repeat=B):
        acc = (0, 0)
        for s in signs:
            t = (1, 0)
            for bit in string: t = mul(t, (2, s) if bit == 0 else (2, -s))
            acc = (acc[0] + t[0], acc[1] + t[1])
        sym = (1, 0)
        for bit in string: sym = mul(sym, (2, 1) if bit == 0 else (2, -1))
        res = 0
        for d in dial:
            t = 1
            for bit in string: t = t * ((2 + d) if bit == 0 else (2 - d)) % Om
            res = (res + t) % Om
        ok &= acc[1] == 0 and acc[0] == 8 * sym[0] and res == (8 * sym[0]) % Om
        total += acc[0]
    return dial_ok and ok and total == 4 ** B * 8, total


# ---- the binding bookkeeping on the torus ℤ_N³ (21:C21, C23) ---------------------------------------------------------
def binding(N=5, m1=3, m2=5, P=(1 << 61) - 1):
    """Neutralised channel statics on ℤ_N³ with κ = 1: Δu = −s, s = m₁δ_a + m₂δ_b − (m₁ + m₂)δ_h, solved exactly over the
    prime field 𝔽_P (a Mersenne prime as the exact witness field, bounded heights). Returns the four verdicts:
    superposition, the cut flux m₁ + m₂, the bilinear energy cross term, the registered clock m₁(1 − u₂(a))."""
    idx = lambda x, y, z: (x % N) * N * N + (y % N) * N + z % N
    V = N ** 3

    def nbrs(i):
        x, y, z = i // (N * N), (i // N) % N, i % N
        return [idx(x + 1, y, z), idx(x - 1, y, z), idx(x, y + 1, z), idx(x, y - 1, z), idx(x, y, z + 1), idx(x, y, z - 1)]

    a, b, h = idx(1, 1, 1), idx(3, 1, 1), idx(2, 3, 3)

    def solve(src):
        n = V - 1
        A = [[0] * (n + 1) for _ in range(n)]
        for i in range(1, V):
            r = A[i - 1]
            r[i - 1] = (r[i - 1] + 6) % P
            for j in nbrs(i):
                if j != 0: r[j - 1] = (r[j - 1] - 1) % P
            r[n] = src.get(i, 0) % P
        for c in range(n):
            piv = next(r for r in range(c, n) if A[r][c])
            A[c], A[piv] = A[piv], A[c]
            inv = pow(A[c][c], P - 2, P)
            A[c] = [v * inv % P for v in A[c]]
            Ac = A[c]
            for r in range(n):
                if r != c and A[r][c]:
                    f = A[r][c]; Ar = A[r]
                    for k in range(c, n + 1): Ar[k] = (Ar[k] - f * Ac[k]) % P
        u = [0] * V
        for i in range(1, V): u[i] = A[i - 1][n]
        return u

    s1, s2, s12 = {a: m1, h: -m1}, {b: m2, h: -m2}, {a: m1, b: m2, h: -(m1 + m2)}
    u1, u2, u12 = solve(s1), solve(s2), solve(s12)
    superpose = all(u12[i] == (u1[i] + u2[i]) % P for i in range(V))
    region = {idx(x, y, z) for x in range(0, N) for y in range(0, 3) for z in range(0, 3)}
    assert a in region and b in region and h not in region
    flux = sum((u12[i] - u12[j]) for i in region for j in nbrs(i) if j not in region) % P
    cut = flux == (m1 + m2) % P

    def energy(u, src):
        quad = sum((u[i] - u[j]) ** 2 for i in range(V) for j in nbrs(i)) % P
        quad = quad * pow(4, P - 2, P) % P
        lin = sum(v * u[k] for k, v in src.items()) % P
        return (quad - lin) % P

    cross = (energy(u12, s12) - energy(u1, s1) - energy(u2, s2)) % P
    inner = (-sum(v * u2[k] for k, v in s1.items())) % P
    clock = (m1 * (1 - u2[a])) % P == (m1 - m1 * u2[a]) % P
    return superpose, cut, cross == inner, clock


# ---- the fold-return toy over 𝔽₁₇ (21:C12, P7) ----------------------------------------------------------------------
def fold_return(p=17, N=8, NI=4):
    """The chain C_N with an interior block of NI sites beyond the fold, converted by the exact DFT (i = 4 in 𝔽₁₇):
    the period-averaged exterior return P_E F U^n F⁻¹ P_E is the uniform floor operator (all nonzero entries equal)."""
    i4 = next(x for x in range(1, p) if x * x % p == p - 1)
    invN = pow(NI, p - 2, p)
    I = [[int(i == j) for j in range(N)] for i in range(N)]
    U = [[int(j == (i - 1) % N) for j in range(N)] for i in range(N)]
    F = [[0] * N for _ in range(N)]; Fi = [[0] * N for _ in range(N)]
    for j in range(NI):
        for k in range(NI):
            F[j][k] = pow(i4, j * k, p); Fi[j][k] = pow(i4, (-j * k) % (p - 1), p) * invN % p
    for j in range(NI, N): F[j][j] = Fi[j][j] = 1
    mm = lambda A, B: [[sum(A[i][k] * B[k][j] for k in range(N)) % p for j in range(N)] for i in range(N)]
    assert mm(F, Fi) == I
    PE = [[int(i == j and i >= NI) for j in range(N)] for i in range(N)]
    acc = [[0] * N for _ in range(N)]; Un = I
    for _ in range(N):
        M = mm(PE, mm(F, mm(Un, mm(Fi, PE))))
        acc = [[(acc[i][j] + M[i][j]) % p for j in range(N)] for i in range(N)]
        Un = mm(U, Un)
    invT = pow(N, p - 2, p)
    ext = [[acc[i][j] * invT % p for j in range(NI, N)] for i in range(NI, N)]
    nonzero = {v for row in ext for v in row if v}
    return len(nonzero) <= 1
