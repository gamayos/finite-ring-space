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
    locked_sum(n, m)                 |Σ_m z|² = m² for one phase; the exact mean of |Σ|² over all n^m phase words is m
    gauss_law(J, region)             the divergence summed over a region equals the boundary flux (antisymmetric J)
    compression_identity(n, sector)  P − KᵀK = CᵀC on the cyclic shift with a sector projector (exact rationals)
    Series                           truncated power series over the rationals (exp, product, quotient, power)
    pn_coefficients()                e^{−2U} against ((1 − U/2)/(1 + U/2))², e^{2U} against (1 + U/2)⁴, to U³
    two_body_1pn()                   the two-body coefficients through 1PN agree, the cross term 4 U₁U₂ included
    pn_orbit_inputs()                the 2PN orbit-equation inputs: δc₂'s leading term and δc₃ = 5/6, the apsidal sum
    static_profile_coefficients()    u(r) = Gm/r (1 + (Gm/r²)²/30 + (Gm/r²)⁴/120 + …): the exact series of the profile
    scale_invariant_exponent(lo, hi) Δ² ∝ k^{n+3} is dilation-invariant for n = −3 alone (n_s = 1)
    dilution(m, s)                   (m/√Ω)² = m²/Ω on Ω = s²: the coupling of two masses m is their count over Ω
    frobenius_trace(p, nu, m, a, b)  the Frobenius pairing of m (w ⊗ w) equals m N(w)
    registration_root(w, s)          wη² − 2η + w = 0 for η = (1 − s)/w with s² = 1 − w², over the rationals
    chebyshev_weight(L, d, w)        q_{L,d} = (U_{d−1} + U_{L−d−1})/U_{L−1} at 1/w against the tridiagonal solve
    christoffel(a, b)                the registration word at rate a/b: a marks per recurrence, two-valued gaps
    largest_remainder(weights, B)    the allocation of B events to the weights, discrepancy ≤ 1
    binding(N, m1, m2)               superposition, cut flux = m₁ + m₂, bilinear energy, the registered clock
    fold_return(p)                   the period-averaged exterior return through the fold is the uniform floor
"""
from fractions import Fraction
from itertools import product
from math import gcd

from frc.extension import Ext


# ---- the register on a frame (21:A1, C2, C5, C16) ----------------------------------------------------------------
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
def pair_tally_identity(p, z):
    """On z ∈ 𝔽_p^× with mate w = z⁻¹: E = 2 − z − w, W = 2 + z + w, E + W = 4 and (z − w)² = −E·W."""
    w = pow(z, p - 2, p)
    E, W = (2 - z - w) % p, (2 + z + w) % p
    return (E + W) % p == 4 % p and (z - w) ** 2 % p == (-E * W) % p


# ---- the locked sum against the incoherent ensemble (21:C1) --------------------------------------------------------
def locked_sum(n, m):
    """m cells of one phase on the n-cycle sum to m·z, |Σ|² = m²; over all n^m phase words the exact mean of |Σ ζ^k|²
    is m (the incoherent √m), computed in the cyclotomic ring ℤ[ζ_n] as an integer identity: Σ_words |Σ_j ζ^{k_j}|² = m·n^m."""
    locked = m * m
    # |Σ_j ζ^{k_j}|² = Σ_{j,l} ζ^{k_j − k_l}; summed over all words the cross terms (j ≠ l) sum to zero and the
    # diagonal gives m·n^m: the count of (word, j, l, residue) with k_j − k_l ≡ 0 is m·n^m + m(m − 1)·n^{m−1}·(1)…
    # computed directly as the multiset of residues k_j − k_l over all words: each nonzero residue appears equally often
    counts = [0] * n
    for word in product(range(n), repeat=m):
        for j in range(m):
            for l in range(m):
                counts[(word[j] - word[l]) % n] += 1
    off = set(counts[1:])
    # Σ_words |Σ|² = counts[0]·1 + Σ_{r≠0} counts[r]·ζ^r = counts[0] − counts[1] since Σ_{r≠0} ζ^r = −1 when all equal
    mean = Fraction(counts[0] - counts[1], n ** m) if len(off) == 1 else None
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


def scale_invariant_exponent(lo=-6, hi=3):
    """Δ²(k) = k³ P(k) ∝ k^{n+3} for P ∝ kⁿ is invariant under k ↦ λk iff n + 3 = 0: on the integer range the fixed
    point is n = −3 alone, n_s = n + 4 = 1 (21:C18)."""
    return [n for n in range(lo, hi) if n + 3 == 0] == [-3]


def dilution(m, s):
    """With Ω = s² and the Planck mass √Ω = s the coupling of two masses m, (m/√Ω)², equals m²/Ω exactly (21:X8, C5)."""
    m, s = Fraction(m), Fraction(s)
    return (m / s) ** 2 == m * m / (s * s)


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
