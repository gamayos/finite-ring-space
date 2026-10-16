"""frc.ladder — the ladder of the four roles, the ascent and the descent on a prime shell (the horizon theme; 26-pnp,
16 October 2026).

The computational face of the horizon clause (master Z2–Z4, B6), exact and float-free. On a prime shell 𝔽_P with the
drive g of order n = P − 1, the index cycle C_n is carried to the units by the ascent m ↦ g^m and read back by the
descent. The functions mirror the core's Theme/Ladder.lean declaration for declaration:

    sqmul(b, e, p)              square-and-multiply, right to left: (b^e mod p, the multiplication count ≤ 2·bits(e))
    sqmul_ltr(b, e, p)          the same, left to right, the paper's scan of the bits
    bsgs(g, h, p, m)            baby-step–giant-step: (i, j, giant multiplications) with g^(j + m·i) = h, or None
    descends(g, h, p, m)        the kernel's verdict (Ladder.descendsB): the pair returned reconstructs h
    phase_index(g, m, k, r, p)  P_k^r(g^m) by iteration, against the closed form g^(k^r·m mod n)
    tower(g, j, p)              g^(g^j) read with the exponent reduced modulo n
    power_image(k, p)           the image of x ↦ x^k on the units
    bezout(k, n)                (d, a, b) with d = gcd(k, n) and a·k = b·n + d in the naturals (power_image's witness)
    recentre(n, m, j)           the translation of the index cycle carrying m to 1 (Ladder.recentre)
    index_table(g, p)           unit ↦ its index (the counting distance from 1 along the orbit)
    mul_perm(c, p)              multiplication by c permutes the units
    ramanujan(p, c)             Σ_{t≠0} ψ(tc) in ℤ[ζ_p], the telescoping of the Gauss sum (−1 or p − 1)
    gauss_norm(p, g, nu)        g(χ_ν)·conj g(χ_ν) in ℤ[ζ_{p(p−1)}], the modulus squared, exactly
    ntt(a, w, q) / intt         the radix-2 number-theoretic transform over 𝔽_q and its inverse, with butterfly counts
    convolve_direct / convolve_ntt   cyclic convolution in the position chart and through the transform, with counts
    affine_f2(rows, n)          Gaussian elimination over 𝔽₂: a particular solution and a basis of the solution space

No float, no random number; every count is a deterministic integer. The chart row of 26-pnp (the family's bit length
against the certified Ω bracket) is decided by the ledger file on frc.chart.omega_bracket, not here.
"""
from math import isqrt

from frc import arith
from frc.quantum import Cyclotomic


# ---- the bit length and square-and-multiply (26:F2, G4) --------------------------------------------------------------

def bits(e):
    """The bit length of e (0 for e = 0), as Ladder.bits."""
    return int(e).bit_length()


def sqmul(b, e, p):
    """Square-and-multiply, right to left, as Ladder.sqmul: returns (b^e mod p, the number of modular multiplications).
    Each round costs one squaring and, when the bit is set, one multiplication: at most 2·bits(e). The last squaring,
    which the Lean count includes, is skipped here (the validation suite's count, 17, 26, 38 at the three carriers)."""
    r, ops = 1, 0
    b %= p
    while e > 0:
        if e % 2 == 1:
            r = r * b % p; ops += 1
        e //= 2
        if e > 0:
            b = b * b % p; ops += 1
    return r, ops


def sqmul_ltr(b, e, p):
    """Square-and-multiply, left to right (the paper's scan of the bits): (b^e mod p, the multiplication count)."""
    r, ops = 1, 0
    b %= p
    for bit in bin(e)[2:] if e > 0 else "":
        r = r * r % p; ops += 1
        if bit == "1":
            r = r * b % p; ops += 1
    return r, ops


# ---- the descent: baby-step–giant-step (26:F3, G4) --------------------------------------------------------------------

def bsgs(g, h, p, m=None):
    """Baby-step–giant-step on 𝔽_P, as Ladder.bsgs: m baby steps 1, g, …, g^(m−1) (one multiplication each, m − 1 in
    all), then giant steps γ_i = h·u^i with u = g^(n−m), one multiplication each, until γ_i is a baby step g^j; then
    h = g^(j + m·i). Returns (i, j, the giant multiplications) or None. m defaults to ⌊√(P − 1)⌋ + 1, so m² ≥ n."""
    n = p - 1
    if m is None: m = isqrt(n) + 1
    table, x = {}, 1
    for j in range(m):
        table.setdefault(x, j)
        x = x * g % p
    u = pow(g, n - m, p)
    gamma, ops = h % p, 0
    for i in range(m):
        if gamma in table:
            return i, table[gamma], ops
        gamma = gamma * u % p; ops += 1
    return None


def descends(g, h, p, m):
    """Ladder.descendsB: the pair returned by bsgs reconstructs h."""
    res = bsgs(g, h, p, m)
    if res is None: return False
    i, j, _ = res
    return j < m and pow(g, j + m * i, p) == h % p


def dlog(g, h, p):
    """The index of h with respect to g (the descent), by baby-step–giant-step; raises if h is not a power of g."""
    res = bsgs(g, h, p)
    if res is None: raise ValueError(f"dlog: {h} is not a power of {g} mod {p}")
    i, j, _ = res
    m = isqrt(p - 1) + 1
    return (j + m * i) % (p - 1)


# ---- the index dynamics of the power map (26:G2, G3, G5) ---------------------------------------------------------------

def phase_index(g, m, k, r, p):
    """P_k^r(g^m) by r iterations of x ↦ x^k, and the closed form g^(k^r·m mod n); returns (iterated, closed form)."""
    n = p - 1
    x = pow(g, m, p)
    for _ in range(r): x = pow(x, k, p)
    return x, pow(g, pow(k, r, n) * m % n, p)


def tower(g, j, p):
    """The tower g^(g^j): the exponent g^j is a residue below P, read as an index modulo n = P − 1; returns
    (g^(g^j), g^((g^j) mod n))."""
    e = pow(g, j, p)
    return pow(g, e, p), pow(g, e % (p - 1), p)


def power_image(k, p):
    """The image of x ↦ x^k on the units of 𝔽_P, as a sorted list."""
    return sorted({pow(x, k, p) for x in range(1, p)})


def bezout(k, n):
    """(d, a, b) with d = gcd(k, n) and a·k = b·n + d in the naturals: the witness Ladder.power_image takes."""
    old_r, r = k, n
    old_s, s = 1, 0
    old_t, t = 0, 1
    while r:
        q = old_r // r
        old_r, r = r, old_r - q * r
        old_s, s = s, old_s - q * s
        old_t, t = t, old_t - q * t
    d, x, y = old_r, old_s, old_t              # x·k + y·n = d
    if d == 0: raise ValueError("bezout: gcd(0, 0)")
    while x <= 0: x += n // d; y -= k // d
    assert x * k + y * n == d and y <= 0
    return d, x, -y


# ---- the recentring chart and the index table (26:E8, E10, F10) -------------------------------------------------------

def recentre(n, m, j):
    """The translation of the index cycle carrying the index m to 1 (Ladder.recentre)."""
    return (j + (n - m) + 1) % n


def index_table(g, p):
    """unit ↦ its index along the orbit of g (the counting distance from 1): {g^m: m} for m < P − 1."""
    out, x = {}, 1
    for m in range(p - 1):
        out.setdefault(x, m)
        x = x * g % p
    return out


# ---- the Gauss sum's telescoping and its modulus (26:B5) -------------------------------------------------------------

def mul_perm(c, p):
    """Multiplication by the unit c permutes the units: {t·c mod P : 0 < t < P} is {1, …, P − 1}."""
    return sorted(t * c % p for t in range(1, p)) == list(range(1, p))


def ramanujan(p, c, C=None):
    """Σ_{0<t<P} ψ(tc) with ψ(x) = ζ_P^x, computed in ℤ[ζ_P]: p − 1 when c ≡ 0, else −1 (the permutation and the
    vanishing of the full sum of the P-th roots of unity). Returns the element of the ring; compare with C.const."""
    C = C or Cyclotomic(p)
    return C.sum(C.zeta(t * c % p) for t in range(1, p))


def gauss_norm(p, g, nu, C=None):
    """g(χ_ν)·conj g(χ_ν) in ℤ[ζ_{P(P−1)}] for the multiplicative character χ_ν(g^t) = ζ_{P−1}^{νt} and the additive
    character ψ(x) = ζ_P^x: both roots live in ζ_N with N = P(P − 1) (ζ_{P−1} = ζ_N^P, ζ_P = ζ_N^{P−1}). Returns the
    ring element; the row asserts it equals C.const(P)."""
    n = p - 1
    N = p * n
    C = C or Cyclotomic(N)
    terms = []
    x = 1
    for t in range(n):                      # x = g^t runs over the units
        terms.append(((p * nu * t + n * x) % N, 1))
        x = x * g % p
    G = C.from_exponents(terms)
    return C.norm2(G)


# ---- the additive transform on the shell and the convolution counts (26:H3) ------------------------------------------

def ntt(a, w, q):
    """The radix-2 number-theoretic transform of a (length n = 2^k) over 𝔽_q with w a primitive n-th root of unity:
    returns (the transform, the butterfly count = (n/2)·log₂ n)."""
    a = [x % q for x in a]
    n = len(a)
    assert n & (n - 1) == 0, "the length must be a power of two"
    # bit reversal
    j = 0
    for i in range(1, n):
        bit = n >> 1
        while j & bit:
            j ^= bit; bit >>= 1
        j |= bit
        if i < j: a[i], a[j] = a[j], a[i]
    length, ops = 2, 0
    while length <= n:
        wlen = pow(w, n // length, q)
        for i in range(0, n, length):
            wk = 1
            for k in range(length // 2):
                u, v = a[i + k], a[i + k + length // 2] * wk % q
                a[i + k], a[i + k + length // 2] = (u + v) % q, (u - v) % q
                wk = wk * wlen % q
                ops += 1
        length <<= 1
    return a, ops


def intt(A, w, q):
    """The inverse transform: the transform with w⁻¹, scaled by n⁻¹; returns (the vector, the butterfly count)."""
    n = len(A)
    a, ops = ntt(A, pow(w, q - 2, q), q)
    ninv = pow(n, q - 2, q)
    return [x * ninv % q for x in a], ops


def convolve_direct(a, b, q):
    """Cyclic convolution in the position chart: (the vector, the multiplication count n²)."""
    n = len(a)
    out = [0] * n
    ops = 0
    for i in range(n):
        for j in range(n):
            out[(i + j) % n] = (out[(i + j) % n] + a[i] * b[j]) % q; ops += 1
    return out, ops


def convolve_ntt(a, b, w, q):
    """Cyclic convolution through the transform: three transforms and n pointwise products; (the vector, the count)."""
    A, o1 = ntt(a, w, q)
    B, o2 = ntt(b, w, q)
    n = len(a)
    C = [x * y % q for x, y in zip(A, B)]
    c, o3 = intt(C, w, q)
    return c, o1 + o2 + o3 + n


# ---- affine systems over 𝔽₂ (26:H4) ------------------------------------------------------------------------------------

def affine_f2(rows, ncols):
    """Gaussian elimination over 𝔽₂ on the augmented rows [a_1, …, a_n, b]: returns (w0, basis) with w0 a particular
    solution and basis a list of vectors spanning the homogeneous solutions, or None when the system is inconsistent."""
    M = [list(r) for r in rows]
    pivots = []
    row = 0
    for col in range(ncols):
        piv = next((r for r in range(row, len(M)) if M[r][col]), None)
        if piv is None: continue
        M[row], M[piv] = M[piv], M[row]
        for r in range(len(M)):
            if r != row and M[r][col]:
                M[r] = [(x ^ y) for x, y in zip(M[r], M[row])]
        pivots.append(col); row += 1
    for r in range(row, len(M)):
        if M[r][ncols]: return None                    # 0 = 1
    w0 = [0] * ncols
    for r, col in enumerate(pivots): w0[col] = M[r][ncols]
    free = [c for c in range(ncols) if c not in pivots]
    basis = []
    for f in free:
        v = [0] * ncols; v[f] = 1
        for r, col in enumerate(pivots): v[col] = M[r][f]
        basis.append(v)
    return w0, basis


def f2_solutions(rows, ncols):
    """Every solution of the augmented system by exhaustion, for the check against affine_f2."""
    sols = []
    for w in range(1 << ncols):
        vec = [(w >> i) & 1 for i in range(ncols)]
        if all(sum(r[i] * vec[i] for i in range(ncols)) % 2 == r[ncols] for r in rows): sols.append(vec)
    return sols
