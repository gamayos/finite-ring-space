"""frc.yangmills — the yangmills theme: the exact content of 46-yangmills above the hadrons and interactions themes
(7–8 November 2026; 46-yangmills-20261107/reports/study.md, Phases 1–2 and the repair of 8 November).

The registrations of the colour frame and their Carrier residues (the non-split torus without a fixed line, the split
torus with two, the centre Z_3 on Ω ≡ 5 (mod 12)), the residue series closed by the glueball (over F_4 by fixed vectors and
by the singlet multiplicities), the Casimirs and the one-loop rational b₀, the drive exponent (every winding rate is one
power of the drive), the single-plaquette coefficients c₁(β) and c₈(β) as formal power series with rational coefficients
(the multiplicities of the singlet in the tensor powers of the colour triplet, computed as constant terms of the Weyl
character polynomials, 27-fields Lemma charlift carrying them to the finite frame), the finite frame's own moments over
F_4, and the exact finite instance 2T = SU(2, F_3) — the arithmetic that frc/ledgers/p46_yangmills.py decides with, every
function integer, finite-field or rational (no float). The chart readings (the LEP colour factors, the one-loop run of
the coupling, the lattice anchors, the tensions as logarithms, the wrap operator) live in frc/chart_yangmills.py. The Lean
side is lean/FrcCore/Theme/YangMills.lean.

    LAB_PAIRS, shells_below(n)             the laboratory pairs (p, Ω) of 7 November 2026 and the sweep of shells p = 4κ+1 < n
    centre_order(q), admissible(q)         |Z(SU(3, F_q))| = gcd(3, q + 1); Z_3 exactly on q ≡ 5 (mod 12)
    nonsplit_torus(p, ν)                   the norm-one elements a + b√ν of F_p[√ν]: (a, b) pairs, p + 1 of them
    fixed_lines_nonsplit(p, ν)             how many of them have an eigenvector in F_p² (the two scalars ±1 only)
    fixed_lines_split(p, g)                the lines of P¹(F_p) fixed by the split torus diag(g, g⁻¹): the two coordinate lines
    adjoint_fixed(F, G), commutant_dim(F, G, action)
                                           the vectors of sl_3(F_4) fixed by SU(3, F_2) (none) and the dimension of the
                                           commutant of a matrix representation (1: the scalars), by linear algebra over F_4
    residue_series(F, G)                   photon 2, gluon 0, baryon 1, meson 1, glueball 1 over F_4
    weyl_residues()                        the same counts by the singlet multiplicities: E[|χ|²] − 1 = 0, E[χ³] = 1,
                                           E[|χ|²] = 1, E[(|χ|² − 1)²] = 1
    generators(F, G), frame_moments_f4(F, G, degree)
                                           a generating pair of SU(3, F_2) and the finite frame's own moments — the fixed
                                           vectors of 3^{⊗a} ⊗ 3̄^{⊗b} over F_4 — beside their compact readings, a + b ≤ degree
    casimirs(N), b0(nf, N)                 C_F, C_A, T_F, C_A/C_F; b₀ = (11/3) C_A − (4/3) T_F n_f
    drive_exponent(p, g), drive_exponents_unique(p)
                                           the discrete logarithm of every nonzero residue to a generator, and its uniqueness
    c1_series(N, n), c1_series_2T(n)       c₁(β), the fundamental plaquette coefficient, as a formal power series in β (Fractions)
                                           from the singlet multiplicities of SU(N) (N = 2, 3) and for 2T from its 24 unit quaternions
    c_adj_series(n)                        c₈(β), the adjoint plaquette coefficient: β²/288 + β³/2592 − β⁵/186624 − …
    adjoint_over_fundamental_squared(n)    c₈ / c₃² = (9/8)(1 − β/18 + β²/432 + β³/2592 + …): the adjoint wrap is two fundamental
                                           wraps up to the rational factor 9/8, the ratio to order β⁴ (no logarithm)
    adjoint_wrap_excess(n)                 the formal series 2L(e) − L(d), L(u) = Σ (−1)^{k+1} u^k/k, whose chart reading is
                                           σ₈ − 2σ₃ + ln(9/8)
"""
from fractions import Fraction as Q
from itertools import product
from math import comb, gcd

from frc import arith as A
from frc import interactions as I
from frc import hadrons as H

LAB_PAIRS = ((13, 233), (173, 30089), (1549, 2408561))        # the Subjects 13, 173, 1549 in their Carriers (the ruling of 7 November 2026)


def shells_below(n):
    """The shells p = 4κ + 1 below n, ascending (the sweep)."""
    return [p for p in range(5, n) if p % 4 == 1 and A.is_prime(p)]


# ---- the centre of the colour frame ----------------------------------------------------------------------------------------
def centre_order(q):
    """|Z(SU(3, F_q))| = gcd(3, q + 1): the norm-one cube roots of unity of the non-split torus (27-fields Proposition su3)."""
    return gcd(3, q + 1)


def admissible(q):
    """q ≡ 5 (mod 12): the shell residue 1 (mod 4) together with the triality centre, 3 | q + 1."""
    return q % 12 == 5


# ---- the tori of SL₂(F_p) and their fixed lines ----------------------------------------------------------------------------
def nonsplit_torus(p, nu):
    """The norm-one elements a + b√ν of F_p[√ν], ν a nonsquare: the pairs (a, b) with a² − ν b² ≡ 1; there are p + 1."""
    out = []
    for a in range(p):
        r = (a * a - 1) * pow(nu, p - 2, p) % p              # b² = (a² − 1)/ν
        if r == 0: out.append((a, 0)); continue
        if A.legendre(r, p) == 1:
            b = _sqrt_mod(r, p); out.append((a, b)); out.append((a, (-b) % p))
    return out


def _sqrt_mod(r, p):
    """A square root of the square r modulo p (p ≡ 1 mod 4: Tonelli–Shanks; small p by search is also exact)."""
    if p % 4 == 3: return pow(r, (p + 1) // 4, p)
    q, s = p - 1, 0
    while q % 2 == 0: q //= 2; s += 1
    z = next(x for x in range(2, p) if A.legendre(x, p) == -1)
    m, c, t, R = s, pow(z, q, p), pow(r, q, p), pow(r, (q + 1) // 2, p)
    while t != 1:
        i, tt = 0, t
        while tt != 1: tt = tt * tt % p; i += 1
        b = pow(c, 1 << (m - i - 1), p); m, c, t, R = i, b * b % p, t * b * b % p, R * b % p
    return R


def has_eigenvalue(p, a, b, nu):
    """Whether a + b√ν, acting on F_p² = F_p[√ν] by multiplication, has an eigenvalue in F_p: its characteristic polynomial is
    x² − 2a x + 1, whose discriminant 4(a² − 1) = 4ν b² is a square iff b = 0 (ν a nonsquare). The identity of the two forms of
    the discriminant is checked on every call."""
    disc = (4 * (a * a - 1)) % p
    assert disc == (4 * nu * b * b) % p, (p, a, b, nu)
    return disc == 0 or A.legendre(disc, p) == 1


def fixed_lines_nonsplit(p, nu):
    """(the number of norm-one elements, the number among them with an eigenvector in F_p²): (p + 1, 2), the two being the
    scalars ±1, so no line of F_p² is fixed by the torus and no non-scalar element fixes any line."""
    T = nonsplit_torus(p, nu)
    withev = [(a, b) for a, b in T if has_eigenvalue(p, a, b, nu)]
    return len(T), len(withev), withev


def fixed_lines_split(p, g):
    """The points [x : y] of P¹(F_p) fixed by diag(g, g⁻¹), g a generator: (g x : g⁻¹ y) = (x : y) iff xy = 0 (g² ≠ 1),
    the two coordinate lines — the photon's two helicities (residue 2)."""
    ginv = pow(g, p - 2, p)
    pts = [(1, y) for y in range(p)] + [(0, 1)]
    def same(u, v):            # [u] = [v] in P¹
        return (u[0] * v[1] - u[1] * v[0]) % p == 0
    return [pt for pt in pts if same((g * pt[0] % p, ginv * pt[1] % p), pt)]


# ---- the residue series over F_4 ---------------------------------------------------------------------------------------------
def _f4_solve_nullspace(F, rows, ncols):
    """The dimension of the nullspace of a matrix over F_4 given as a list of rows (lists of F elements): Gaussian elimination."""
    M = [list(r) for r in rows]; rank, col = 0, 0
    nrows = len(M)
    while rank < nrows and col < ncols:
        piv = next((i for i in range(rank, nrows) if M[i][col] != F.zero), None)
        if piv is None: col += 1; continue
        M[rank], M[piv] = M[piv], M[rank]
        inv = F.inv(M[rank][col]); M[rank] = [F.mul(inv, x) for x in M[rank]]
        for i in range(nrows):
            if i != rank and M[i][col] != F.zero:
                f = M[i][col]; M[i] = [F.sub(x, F.mul(f, y)) for x, y in zip(M[i], M[rank])]
        rank += 1; col += 1
    return ncols - rank


def _basis_matrices(F, n):
    out = []
    for i in range(n):
        for j in range(n):
            out.append(tuple(tuple(F.one if (r, c) == (i, j) else F.zero for c in range(n)) for r in range(n)))
    return out


def _flat(M): return [x for row in M for x in row]


def adjoint_fixed(F, G):
    """The dimension of {M ∈ gl_3(F_4) : g M g⁻¹ = M for all g} ∩ sl_3: the fixed vectors of the adjoint action on the traceless
    matrices. Returns (dim of the full commutant of the fundamental, dim of its traceless part)."""
    n = 3; E = _basis_matrices(F, n); rows = []
    for g in G:
        ginv = I.dagger(F, g)                                 # unitary: g⁻¹ = g†
        cols = [_flat(I.mat_mul(F, I.mat_mul(F, g, e), ginv)) for e in E]     # the images of the basis matrices
        for k in range(n * n):                                 # the equation (g e g⁻¹ − e)_k = 0 over the 9 coefficients
            rows.append([F.sub(cols[j][k], _flat(E[j])[k]) for j in range(n * n)])
    full = _f4_solve_nullspace(F, rows, n * n)
    # the traceless part: add the trace equation Σ c_ii = 0
    tr = [F.one if (j // n) == (j % n) else F.zero for j in range(n * n)]
    traceless = _f4_solve_nullspace(F, rows + [tr], n * n)
    return full, traceless


def commutant_dim(F, G, action, dim):
    """The dimension of the commutant of a matrix representation `action(g)` of G of dimension `dim` over F_4: the number of
    independent M with action(g) M = M action(g) for every g — 1 for an absolutely irreducible representation (Schur)."""
    E = _basis_matrices(F, dim); rows = []
    mats = [action(g) for g in G]
    for a in mats:
        left = [_flat(I.mat_mul(F, a, e)) for e in E]; right = [_flat(I.mat_mul(F, e, a)) for e in E]
        for k in range(dim * dim):
            rows.append([F.sub(left[j][k], right[j][k]) for j in range(dim * dim)])
    return _f4_solve_nullspace(F, rows, dim * dim)


def adjoint_rep(F, g):
    """The 8 × 8 matrix of Ad(g) on sl_3(F_4) in the basis e_ij (i ≠ j) and e_11 − e_22, e_22 − e_33 (traceless; char 2: the
    identity has trace 1 ≠ 0, so sl_3 is 8-dimensional and does not contain it)."""
    n = 3; basis = []
    for i in range(n):
        for j in range(n):
            if i != j: basis.append(tuple(tuple(F.one if (r, c) == (i, j) else F.zero for c in range(n)) for r in range(n)))
    basis.append(tuple(tuple(F.one if (r, c) in ((0, 0), (1, 1)) else F.zero for c in range(n)) for r in range(n)))   # e11 − e22 = e11 + e22 (char 2)
    basis.append(tuple(tuple(F.one if (r, c) in ((1, 1), (2, 2)) else F.zero for c in range(n)) for r in range(n)))
    ginv = I.dagger(F, g)
    cols = []
    for e in basis:
        m = I.mat_mul(F, I.mat_mul(F, g, e), ginv)
        cols.append(_coords(F, m, basis))
    return tuple(tuple(cols[j][i] for j in range(8)) for i in range(8))


def _coords(F, m, basis):
    """The coordinates of a traceless m in the basis above: the off-diagonal entries, then (m11, m11 + m22) for the two
    diagonal basis elements (m11 = x, m22 = x + y, m33 = y with the trace x + x + y + y = 0 automatic in char 2)."""
    c = []
    for i in range(3):
        for j in range(3):
            if i != j: c.append(m[i][j])
    x = m[0][0]; y = m[2][2]
    assert F.add(F.add(m[0][0], m[1][1]), m[2][2]) == F.zero and m[1][1] == F.add(x, y)
    c.append(x); c.append(y)
    return c


def residue_series(F=None, G=None):
    """The Carrier residues over F_4: photon 2 (the split torus's two fixed lines, stated on the shells), gluon 0 (no
    nonzero vector of sl_3 fixed by the adjoint action), baryon 1 (det), meson 1 (the commutant of the fundamental),
    glueball 1 (the commutant of the adjoint). Returns the dict and the content (1, 0, 0, 1) of Λ•(3)."""
    F, G = (F, G) if F else H.colour_group()
    content = H.colourless_content(F, G)
    full, traceless = adjoint_fixed(F, G)
    meson = commutant_dim(F, G, lambda g: g, 3)
    glue = commutant_dim(F, G, lambda g: adjoint_rep(F, g), 8)
    return dict(gluon=traceless, baryon=content[3], meson=meson, glueball=glue, fundamental_commutant=full), content


def generators(F, G, k=3):
    """A generating set of the finite colour group G: at most k elements, taken from twelve elements spread through the list,
    whose closure under multiplication is all of G (breadth-first closure); falls back to G itself."""
    import itertools
    step = max(1, len(G) // 12)                            # twelve elements spread through the list
    for size in range(1, k + 1):
        for gens in itertools.combinations(range(0, len(G), step), size):
            S = [G[i] for i in gens]; seen = {H.identity(F)}; frontier = [H.identity(F)]
            while frontier:
                nxt = []
                for x in frontier:
                    for g in S:
                        y = I.mat_mul(F, x, g)
                        if y not in seen: seen.add(y); nxt.append(y)
                frontier = nxt
            if len(seen) == len(G): return S
    return list(G)


def _kron(F, A, B):
    """The Kronecker product of two matrices over F (tuples of rows)."""
    n, m = len(A), len(B)
    return tuple(tuple(F.mul(A[i // m][j // m], B[i % m][j % m]) for j in range(n * m)) for i in range(n * m))


def frame_moment_f4(F, G, a, b, gens=None):
    """The finite frame's own moment: the dimension of the space of vectors of 3^{⊗a} ⊗ 3̄^{⊗b} fixed by every element of
    SU(3, F_2) over F_4 — the finite-field count whose compact reading is the multiplicity E[χ^a χ̄^b] (interactions.su3_moment).
    The dual action of a unitary g is its entrywise conjugate (g⁻¹ = g†). Computed on a generating set of G."""
    gens = gens or generators(F, G)
    dim = 3 ** (a + b); one = ((F.one,),)
    rows = []
    for g in gens:
        M = one
        for _ in range(a): M = _kron(F, M, g)
        gc = tuple(tuple(F.conj(x) for x in r) for r in g)
        for _ in range(b): M = _kron(F, M, gc)
        for i in range(dim):                                # (M − I) v = 0
            rows.append([F.sub(M[i][j], F.one if i == j else F.zero) for j in range(dim)])
    return _f4_solve_nullspace(F, rows, dim)


def frame_moments_f4(F=None, G=None, degree=4):
    """Every finite-frame moment of total degree a + b ≤ degree beside its compact reading: {(a, b): (finite, compact)}."""
    F, G = (F, G) if F else H.colour_group()
    gens = generators(F, G)
    out = {}
    for a in range(degree + 1):
        for b in range(degree + 1 - a):
            if a + b == 0: continue
            out[(a, b)] = (frame_moment_f4(F, G, a, b, gens), I.su3_moment(a, b))
    return out


def weyl_residues():
    """The same counts by the Weyl constant terms of SU(3): adjoint invariants E[|χ|²] − 1, the baryon singlet E[χ³], the meson
    singlet E[|χ|²], the glueball singlet E[(|χ|² − 1)²] = E[|χ|⁴] − 2E[|χ|²] + 1."""
    E = {(a, b): I.su3_moment(a, b) for (a, b) in [(1, 1), (3, 0), (2, 2)]}
    return dict(gluon=E[(1, 1)] - 1, baryon=E[(3, 0)], meson=E[(1, 1)], glueball=E[(2, 2)] - 2 * E[(1, 1)] + 1), E


# ---- the Casimirs and the window rational ----------------------------------------------------------------------------------
def casimirs(N=3):
    """C_F = (N² − 1)/2N, C_A = N, T_F = 1/2 and the ratio C_A/C_F (9/4 at N = 3)."""
    CF, CA, TF = Q(N * N - 1, 2 * N), Q(N), Q(1, 2)
    return dict(C_F=CF, C_A=CA, T_F=TF, ratio=CA / CF)


def b0(nf, N=3):
    """The one-loop coefficient b₀ = (11/3) C_A − (4/3) T_F n_f (= 11 − 2n_f/3 at N = 3), an exact rational of the Casimirs."""
    c = casimirs(N)
    return Q(11, 3) * c["C_A"] - Q(4, 3) * c["T_F"] * nf


# ---- the drive exponent ----------------------------------------------------------------------------------------------------
def drive_exponent(p, g, w):
    """The exponent n < p − 1 with gⁿ ≡ w (the discrete logarithm of the winding rate w to the drive g), by the forward power
    map; None if w ≡ 0."""
    if w % p == 0: return None
    x = 1
    for n in range(p - 1):
        if x == w % p: return n
        x = x * g % p
    raise AssertionError("g is not a generator")


def drive_exponents_unique(p, g=None):
    """Every nonzero residue has exactly one exponent below p − 1: the powers g⁰, …, g^{p−2} are a permutation of 1..p−1."""
    g = g or A.primitive_root(p)
    pows = [pow(g, n, p) for n in range(p - 1)]
    return sorted(pows) == list(range(1, p)), g


# ---- the single-plaquette coefficient as an exact series ------------------------------------------------------------------
def _series_from_moments(mX, mchiX, d, n):
    """c₁ = (1/d) Σ_k E[χ X^k] (β/d)^k/k! / Σ_k E[X^k] (β/d)^k/k!, X = Re χ, to order n (coefficient lists in β)."""
    num = [Q(mchiX[k], d) / Q(d) ** k / _fact(k) for k in range(n)]
    den = [Q(mX[k]) / Q(d) ** k / _fact(k) for k in range(n)]
    return I.ps_div(num, den, n)


def _fact(k):
    r = 1
    for j in range(2, k + 1): r *= j
    return r


def _su2_moment(k):
    """E[χ^k] for SU(2), the number of singlets in 2^{⊗k}: the Catalan numbers at even k, 0 at odd k."""
    if k % 2: return 0
    m = k // 2
    return comb(2 * m, m) // (m + 1)


def c1_series(N, n=7):
    """The fundamental plaquette coefficient with the real Wilson action (Re χ_f), N = 2 or 3, as a polynomial in β to order n
    (the series modulo β^{n+1}), every coefficient a rational built from the singlet multiplicities E[χ^a χ̄^b] of the tensor powers of the
    fundamental (interactions.su3_moment, the constant terms of the Weyl character polynomials; the Catalan numbers for SU(2)).
    SU(2): β/4 − β³/96 + β⁵/1536 − …(the chart reads the series as I₂(β)/I₁(β)); SU(3): β/18 + β²/216 − 5β⁴/93312 − …"""
    if N == 2:
        mX = [_su2_moment(k) for k in range(n + 1)]
        return _series_from_moments(mX, mX[1:] + [_su2_moment(n + 1)], 2, n)
    if N == 3:
        def E(a, b): return I.su3_moment(a, b)
        mX = [sum(comb(k, j) * E(j, k - j) for j in range(k + 1)) / Q(2 ** k) for k in range(n + 1)]
        mchiX = [sum(comb(k, j) * E(j + 1, k - j) for j in range(k + 1)) / Q(2 ** k) for k in range(n + 1)]
        return _series_from_moments(mX, mchiX, 3, n)
    raise ValueError("c1_series: N = 2 or 3")


def c_adj_series(n=8):
    """The adjoint plaquette coefficient with the real Wilson action, χ₈ = χχ̄ − 1, to order n in β with rational coefficients
    from the singlet multiplicities: β²/288 + β³/2592 + 0·β⁴ − β⁵/186624 − …. The β¹ coefficient vanishes (no singlet
    in 8 ⊗ 3 or 8 ⊗ 3̄) and the β² coefficient is E[(χχ̄ − 1)(Re χ)²]/18 with E[(χχ̄ − 1)(Re χ)²] = 1/2: the adjoint wrap needs two
    fundamental plaquette layers (46:C9). The enumerable instance's own moments (frame_moments_f4) give the same two numbers over F_4."""
    E = I.su3_moment
    mX = [sum(comb(k, j) * E(j, k - j) for j in range(k + 1)) / Q(2 ** k) for k in range(n + 1)]
    madj = [sum(comb(k, j) * (E(j + 1, k - j + 1) - E(j, k - j)) for j in range(k + 1)) / Q(2 ** k) for k in range(n + 1)]
    return [c * Q(3, 8) for c in _series_from_moments(mX, madj, 3, n)]       # _series_from_moments normalises by 1/3; the adjoint by 1/8


def _ps_log1p(u, n):
    """ln(1 + u) for a power series u with u₀ = 0, to order n (exact rationals)."""
    out = [Q(0)] * n; pw = [Q(1)] + [Q(0)] * (n - 1)
    for k in range(1, n):
        pw = I.ps_mul(pw, u, n)
        for i in range(n): out[i] += Q((-1) ** (k + 1), k) * pw[i]
    return out


def adjoint_over_fundamental_squared(n=6):
    """The ratio c₈ / c₃² to order n in β: 9/8 − β/16 + β²/384 + β³/2304 + … = (9/8)(1 − β/18 + β²/432 + β³/2592 + 7β⁴/933120
    − …). The adjoint wrap is two fundamental wraps at leading order, up to the rational factor 9/8 — the log-free form of 46:C9.
    Returns the coefficient list of the ratio."""
    c3 = c1_series(3, n + 3); c8 = c_adj_series(n + 3)
    return I.ps_div(c8[2:], I.ps_mul(c3[1:], c3[1:], n + 1), n)


def adjoint_wrap_excess(n=5):
    """The series s(β) = 2 L(e) − L(d) to order n, L(u) = Σ_{k≥1} (−1)^{k+1} u^k/k, with c₃ = (β/18)(1 + e(β)) and c₈ = (β²/288)(1 + d(β)):
    s = β/18 − β²/1296 − β³/2187 − 521β⁴/16796160 − …, exact rationals. Its chart reading (chart_yangmills.adjoint_ratio) is
    σ₈ − 2σ₃ + ln(9/8) for the tensions σ_R = −ln c_R; the exact tier states the ratio adjoint_over_fundamental_squared instead."""
    c3 = c1_series(3, n + 3); c8 = c_adj_series(n + 3)
    e = ([Q(0)] + [18 * c for c in c3[2:]])[:n + 1]
    d = ([Q(0)] + [288 * c for c in c8[3:]])[:n + 1]
    L3 = _ps_log1p(e, n + 1); L8 = _ps_log1p(d, n + 1)
    return [2 * L3[i] - L8[i] for i in range(n + 1)]


def c1_series_2T(n=7):
    """c₁(β) for the binary tetrahedral group 2T = SU(2, F_3) from the traces of its 24 unit quaternions (interactions.
    binary_tetrahedral): the multiset {2: 1, −2: 1, 0: 6, 1: 8, −1: 8}; β/4 − β³/96 + β⁵/1280 + …"""
    tr = {}
    for q in I.binary_tetrahedral():
        t = int(2 * q[0]); tr[t] = tr.get(t, 0) + 1
    tot = sum(tr.values())
    mX = [Q(sum(c * t ** k for t, c in tr.items()), tot) for k in range(n + 2)]
    return _series_from_moments(mX, mX[1:], 2, n), tr
