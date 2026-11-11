"""frc.yangmills — the yangmills theme: the exact content of 46-yangmills above the hadrons and interactions themes
(7–8 November 2026; 46-yangmills-20261107/reports/study.md, Phases 1–2 and the repair of 8 November).

The registrations of the unitary frame (the norm-one cycle without a fixed line, the split torus with two, the centre of
order gcd(3, p + 1)), colour's triality as the Carrier's relation Ω ≡ 5 (mod 12) (46:B5), the residue series on the instance (over F_4 by fixed vectors and
by the singlet multiplicities), the Casimirs and the one-loop rational b₀, the drive exponent (every winding rate is one
power of the drive), the single-plaquette coefficients c₁(β) and c₈(β) as formal power series with rational coefficients
(the multiplicities of the singlet in the tensor powers of the triplet, computed as constant terms of the Weyl
character polynomials, 27-fields Lemma charlift carrying them to the finite frame), the finite frame's own moments over
F_4, and the exact finite instance 2T = SU(2, F_3) — the arithmetic that frc/ledgers/p46_yangmills.py decides with, every
function integer, finite-field or rational (no float). The chart readings (the LEP colour factors, the one-loop run of
the coupling, the lattice anchors, the tensions as logarithms, the wrap operator) live in frc/chart_yangmills.py. The Lean
side is lean/FrcCore/Theme/YangMills.lean.

    LAB_PAIRS, shells_below(n)             the laboratory pairs (p, Ω) of 7 November 2026 and the sweep of shells p = 4κ+1 < n
    centre_order(q), full_centre(q)        |Z(SU(3, F_q))| = gcd(3, q + 1); of order three exactly where 3 | q + 1
    carrier_triality(Ω)                    colour's triality on a Carrier: Ω ≡ 5 (mod 12), x² + x + 1 without a root (46:B5, C2)
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
    small_frame(q), frobenius_tensor(q), row_identity(q), binomial_table(q, p), frame_counts_small_field(q, degree),
    first_departure_bounds(p), frame_window_orders(p)
                                           the frame's window and its first departure (46:C15): SU(3, F_q) for q = 2, 3 by frames,
                                           the Frobenius tensor v_q at (4q − 4, 1), the row-operation identity and the binomial table
                                           behind its invariance, the finite counts M(a, b) at q = 2, 3 (numpy, exact), and the
                                           bounds 2p ≤ d_* ≤ 4p − 3 with the series' orders 2p − 2, 2p − 3
    conductor(q), subject_phase_table(), nonsplit_amplitude_exponents(q), semisimple_part(F, U, p), eigenvalues_in_f_q2(F, S),
    spectral_amplitude_instance(), transfer_tally_instance(), z3_mul, z3_conj, z3_pow
                                           the spectral amplitude of a plaquette (46:B4, C16, C17, C18): the conductor M = lcm(q² − 1,
                                           q² − q + 1) and the phase table of the Subjects, the Jordan parts by powers, the amplitude
                                           w(U) = Σ ι(λ_j(U_s)) in Z[ζ₃] on the 216 elements with its distribution and moments, and the
                                           transfer tally K, the step of one plaquette with the frame's mean, with its exact spectrum 2/3, 1/6, 0, −1/3
    su3_order(q), amplitude_coefficients(q), amplitude_coefficients_direct(q), transfer_spectrum_subject(q)
                                           the transfer tally on the Subjects (46:C19): the amplitude's character expansion
                                           w = χ₁ + χ₂ − χ₃ from the generic character table of SU(3, q) by exact character sums over
                                           the class types (and from the explicit class list, traced down from Z[ζ_N]), the eigenvalues
                                           1/(q²−q+1), 1/(q³+1), −1/((q+1)²(q−1)) of the mean with multiplicities the squared degrees
"""
from fractions import Fraction as Q
from itertools import product
from math import comb, gcd, isqrt

from frc import arith as A
from frc import interactions as I
from frc import hadrons as H

LAB_PAIRS = ((13, 233), (173, 30089), (1549, 2408561))        # the Subjects 13, 173, 1549 in their Carriers (the ruling of 7 November 2026)


def shells_below(n):
    """The shells p = 4κ + 1 below n, ascending (the sweep)."""
    return [p for p in range(5, n) if p % 4 == 1 and A.is_prime(p)]


# ---- the centre of the unitary frame and the Carrier's triality ------------------------------------------------------------
def centre_order(q):
    """|Z(SU(3, F_q))| = gcd(3, q + 1): the norm-one cube roots of unity of the non-split torus (27-fields Proposition su3)."""
    return gcd(3, q + 1)


def full_centre(q):
    """3 | q + 1: the unitary frame SU(3, F_q) has the centre of order three. No condition on a Subject's prime follows (46:B5)."""
    return (q + 1) % 3 == 0


def carrier_triality(Om):
    """Colour's triality on a Carrier Ω (46:B5, 46:C2): Ω ≡ 5 (mod 12), so 3 | Ω + 1 and 3 ∤ Ω − 1. Then 1 is the one residue
    with cube 1, and x² + x + 1 has no root modulo Ω: its discriminant −3 is a nonsquare, and so is 3. The cube roots of unity
    are the pairs (0, 1) and (−1, −1) of residues, a + bω with ω² = −ω − 1, of norm a² − ab + b² = 1; with (1, 0) they form a
    group of order three, and no extension of the Carrier is formed. The roots are searched exhaustively below 10⁵; Euler's
    criterion decides on every Carrier. Returns the checks with their conjunction under "ok"."""
    mul = lambda u, v: ((u[0] * v[0] - u[1] * v[1]) % Om, (u[0] * v[1] + u[1] * v[0] - u[1] * v[1]) % Om)
    norm = lambda u: (u[0] * u[0] - u[0] * u[1] + u[1] * u[1]) % Om
    one, w, w2 = (1, 0), (0, 1), (Om - 1, Om - 1)
    checks = {"5 mod 12": Om % 12 == 5, "3 | Ω+1": (Om + 1) % 3 == 0, "3 ∤ Ω−1": gcd(3, Om - 1) == 1,
              "−3 nonsquare": pow(Om - 3, (Om - 1) // 2, Om) == Om - 1, "3 nonsquare": pow(3, (Om - 1) // 2, Om) == Om - 1,
              "no root": Om >= 10 ** 5 or not any((x * x + x + 1) % Om == 0 for x in range(Om)),
              "norm-one pairs": norm(w) == 1 and norm(w2) == 1 and norm(one) == 1,
              "group of order three": mul(w, w) == w2 and mul(w, w2) == one and mul(w2, w2) == w}
    return dict(checks, ok=all(checks.values()))


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
    """A generating set of the finite unitary frame G: at most k elements, taken from twelve elements spread through the list,
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


def casimirs_from_exponents():
    """The Casimir rationals from the frame's torus exponents, with no lift (round 03, 9 November 2026; 46:C4): a torus element acts
    on the fundamental with the eigenvalue exponents (a, b, −a−b) and on the adjoint with their six differences and two zeros; the
    second moments of the exponents are quadratic forms in (a, b), both multiples of the Weyl-invariant form a² + ab + b² — 2 and
    12 times it — so T_A/T_F = 6, and with the chart's normalisation T_F = 1/2: T_A = 3, C_F = 8 T_F/3 = 4/3, C_A = 8 T_A/8 = 3,
    C_A/C_F = 9/4; the three-quark singlet Σ_{i<j} λ_i·λ_j = −8 from (Σ λ)² = 0 with λ·λ = 4 C_F per quark. The forms are returned
    as the coefficient triples (aa, ab, bb)."""
    fund = [(1, 0), (0, 1), (-1, -1)]
    adj = [(u[0] - v[0], u[1] - v[1]) for u in fund for v in fund if u != v] + [(0, 0), (0, 0)]
    def form(ws):
        return (sum(a * a for a, _ in ws), sum(2 * a * b for a, b in ws), sum(b * b for _, b in ws))
    fF, fA = form(fund), form(adj)
    ratio_T = Q(fA[0], fF[0])
    TF = Q(1, 2); TA = TF * ratio_T
    CF, CA = 8 * TF / 3, 8 * TA / 8
    return dict(form_F=fF, form_A=fA, ratio_T=ratio_T, T_A=TA, C_F=CF, C_A=CA, ratio=CA / CF, singlet=(0 - 3 * 4 * CF) / 2)


def split_torus_exponents(p, n=1):
    """The split torus of SU(3, F_p) over F_{p²}: diag(λ, λ^{p−1}, λ^{−p}) with λ of exponent n on the doubled cycle of order p² − 1,
    so the fundamental's exponents are (n, (p−1)n, −pn) mod p² − 1 (their sum 0) and the adjoint's their differences; the second
    moments along this line of the exponent plane, n² + (p−1)²n² + p²n² and six times it, read the ratio 6 of
    casimirs_from_exponents on the Subject."""
    M = p * p - 1
    e = [n % M, (p - 1) * n % M, (-p * n) % M]
    assert sum(e) % M == 0
    a, b = n, (p - 1) * n                                                      # the window representatives (a, b, −a−b) = (n, (p−1)n, −pn)
    sF = a * a + b * b + (a + b) * (a + b)
    sA = 2 * ((a - b) ** 2 + (2 * a + b) ** 2 + (a + 2 * b) ** 2)
    return dict(exponents=e, second_moment_F=sF, second_moment_A=sA, ratio=Q(sA, sF))


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


def _c3_from(E, n):
    """c₃ to order n from an invariant-count function E(a, b) (the compact su3_moment, or the frame's own counts)."""
    mX = [sum(comb(k, j) * E(j, k - j) for j in range(k + 1)) / Q(2 ** k) for k in range(n + 1)]
    mchiX = [sum(comb(k, j) * E(j + 1, k - j) for j in range(k + 1)) / Q(2 ** k) for k in range(n + 1)]
    return _series_from_moments(mX, mchiX, 3, n)


def _c8_from(E, n):
    """c₈ to order n from an invariant-count function E(a, b), χ₈ = χχ̄ − 1."""
    mX = [sum(comb(k, j) * E(j, k - j) for j in range(k + 1)) / Q(2 ** k) for k in range(n + 1)]
    madj = [sum(comb(k, j) * (E(j + 1, k - j + 1) - E(j, k - j)) for j in range(k + 1)) / Q(2 ** k) for k in range(n + 1)]
    return [c * Q(3, 8) for c in _series_from_moments(mX, madj, 3, n)]


def series_window(n=8):
    """46:C14 — the series' window, the corollary of A9 (the push on T06, 9 November 2026). The β^k coefficient of c₃ is built from
    the invariant counts E(a, b) of degree a + b ≤ k + 1 (the numerator's E[χ X^k] has degree k + 1, the denominator's E[X^k] degree k)
    and that of c₈ from degree ≤ k + 2, so where the frame's counts equal the compact ones through degree p − 2 (A9) the frame's
    series equal the compact ones through β^{p−3} and β^{p−4}. Witnessed by perturbation: raising every count of degree d by one
    leaves c₃'s coefficients below β^{d−1} and c₈'s below β^{d−2} unchanged and moves the next; the windows of the Subjects."""
    E = I.su3_moment
    base3, base8 = _c3_from(E, n), _c8_from(E, n)
    first = {}
    for d in range(2, n + 2):
        Ed = (lambda a, b, d=d: E(a, b) + (1 if a + b == d else 0))
        p3, p8 = _c3_from(Ed, n), _c8_from(Ed, n)
        f3 = next((k for k in range(n) if p3[k] != base3[k]), None)
        f8 = next((k for k in range(n) if p8[k] != base8[k]), None)
        first[d] = (f3, f8)
    window = {p: (p - 3, p - 4) for p, _ in LAB_PAIRS}
    return dict(first_changed=first, window=window, c3=base3, c8=base8)


def instance_series_departure(F=None, G=None):
    """46:C14 — the instance's departure: on SU(3, F_2), where A9 is silent (p − 2 = 0), the frame's invariant counts agree with the
    compact ones through degree 4 (frame_moments_f4) and depart at degree 5, M(4, 1) = M(1, 4) = 4 against 3 (the other degree-5
    pairs vanish on both sides, the centre Z_3 acting by a nontrivial scalar); the instance's own series therefore depart at β⁴ (c₃)
    and β³ (c₈): c₃'s β⁴ coefficient is 0 against −5/93312 and c₈'s β³ is 1/1728 against 1/2592."""
    F, G = (F, G) if F else H.colour_group()
    gens = generators(F, G)
    m41, m14 = frame_moment_f4(F, G, 4, 1, gens), frame_moment_f4(F, G, 1, 4, gens)
    def Ef(a, b):
        if (a, b) == (4, 1): return m41
        if (a, b) == (1, 4): return m14
        return I.su3_moment(a, b)                            # degree ≤ 4 agree (frame_moments_f4); the other degree-5 pairs are 0 by the centre
    return dict(M41=m41, M14=m14, compact41=I.su3_moment(4, 1), c3_instance=_c3_from(Ef, 5), c3_compact=_c3_from(I.su3_moment, 5),
                c8_instance=_c8_from(Ef, 4), c8_compact=_c8_from(I.su3_moment, 4))


# ---- the frame's window and its first departure (46:C15; the T07 pushes of 9 November 2026) ---------------------------------
def small_frame(q):
    """SU(3, F_q) over F_{q²} for the identity hermitian form, by orthonormal frames (interactions.unitary_frames), with a generating
    pair verified by closure: q = 2 (216 elements over F_4 = F_2[t]/(t² + t + 1)) or q = 3 (6048 elements over F_9 = F_3[t]/(t² + 1))."""
    if q == 2: F = I.Fq2(2, 1, 1)
    elif q == 3: F = I.Fq2(3, 0, 2)
    else: raise ValueError("small_frame: q is 2 or 3")
    G = I.unitary_frames(F, 3)
    return F, G, generators(F, G, 2)


def word_contents(q):
    """The nine contents c(i, j)_l = q − 1 + q·[l = i] − [l = j] of the word sums S_{c(i,j)} of 3^{⊗(4q−4)} (46:C15)."""
    return {(i, j): tuple(q - 1 + q * (l == i) - (l == j) for l in range(3)) for i in range(3) for j in range(3)}


def words_of_content(c):
    """Every word with c[0] letters e₀, c[1] letters e₁ and c[2] letters e₂, as index tuples, each once."""
    from itertools import combinations
    n = sum(c); out = []
    for P0 in combinations(range(n), c[0]):
        rest = [f for f in range(n) if f not in P0]
        for P1 in combinations(rest, c[1]):
            w = [2] * n
            for f in P0: w[f] = 0
            for f in P1: w[f] = 1
            out.append(tuple(w))
    return out


def frobenius_tensor(q):
    """v_q = Σ_{(i,j,k)} sgn(i,j,k) S(i^{2q−1} j^{q−2} k^{q−1}) ⊗ e_k^* (46:C15, eq. frobenius): the dict word → ±1 over the integers,
    the words of 3^{⊗(4q−4)} ⊗ 3̄ written as index tuples with the dual index last. 24 terms at q = 2, 1008 at q = 3."""
    from itertools import permutations
    v = {}
    for (i, j, k) in permutations(range(3)):
        sgn = 1 if (i, j, k) in [(0, 1, 2), (1, 2, 0), (2, 0, 1)] else -1
        c = [0, 0, 0]; c[i] = 2 * q - 1; c[j] = q - 2; c[k] = q - 1
        for w in words_of_content(c): v[w + (k,)] = sgn
    return v


def frobenius_weights(q):
    """The weights (letters e_l less letters e_l^*) of the words of v_q: the permutations of (2q − 1, q − 2, q − 2), none of the form
    (k, k, k), all congruent modulo q + 1 — so v_q is no combination of pairing-and-determinant tensors."""
    wts = set()
    for w in frobenius_tensor(q):
        x = [0, 0, 0]
        for s in w[:-1]: x[s] += 1
        x[w[-1]] -= 1
        wts.add(tuple(x))
    return sorted(wts)


def binomial_table(q, p):
    """The coefficients binom(m + r, r) mod p that enter the row-operation identity of 46:C15, m ∈ {q−2, q−1} for r ≤ 2q − 1 and
    m ∈ {2q−2, 2q−1} for r ≤ q − 1, by Lucas's theorem on the base-p digits (no large integer is formed): the dict m → {r: value}
    of the nonzero ones. For q a power of p they are {0: 1, 1: p−1, q: 1, q+1: p−1}, {0: 1, q: 1}, {0: 1, 1: p−1}, {0: 1}."""
    def lucas(n, k):
        out = 1
        while n or k:
            a, b = n % p, k % p
            if b > a: return 0
            out = out * comb(a, b) % p; n //= p; k //= p
        return out
    table = {}
    for m, R in ((q - 2, 2 * q - 1), (q - 1, 2 * q - 1), (2 * q - 2, q - 1), (2 * q - 1, q - 1)):
        table[m] = {r: lucas(m + r, r) for r in range(R + 1) if lucas(m + r, r)}
    return table


def binomial_table_expected(q, p):
    """The pattern the proof of 46:C15 states, for comparison with binomial_table."""
    return {q - 2: {0: 1, 1: p - 1, q: 1, q + 1: p - 1}, q - 1: {0: 1, q: 1}, 2 * q - 2: {0: 1, 1: p - 1}, 2 * q - 1: {0: 1}}


def row_identity(q, F=None):
    """The identity (1 + zE_ab) S_{c(i,j)} = S_{c(i,j)} + [i=b] z^q S_{c(a,j)} − [j=a] z S_{c(i,b)} − [i=b][j=a] z^{q+1} S_{c(a,b)} on the word
    sums of 3^{⊗(4q−4)}, checked word by word for every root (a, b), every content (i, j) and every nonzero z of F_{q²}; returns
    (cases, failures). With the diagonal multipliers it makes e_i ⊗ e_j^* ↦ S_{c(i,j)} a map of GL₃(F_{q²})-modules from
    det^{q−1} ⊗ 3^{(q)} ⊗ 3̄ (the first factor twisted by the Frobenius of the entries), the heart of 46:C15 (ii)."""
    from itertools import combinations
    F = F or small_frame(q)[0]
    C = word_contents(q); n = 4 * q - 4
    S = {ij: words_of_content(c) for ij, c in C.items()}
    def scaled(ws, s): return {w: s for w in ws}
    def addto(acc, vec):
        for w, cf in vec.items():
            acc[w] = F.add(acc.get(w, F.zero), cf)
    cases = failures = 0
    for a in range(3):
        for b in range(3):
            if a == b: continue
            for (i, j), ws in S.items():
                for z in F.elements():
                    if z == F.zero: continue
                    img = {}
                    for w in ws:                                 # (1 + zE_ab) on every slot: e_b ↦ e_b + z e_a
                        slots = [s for s in range(n) if w[s] == b]
                        for r in range(len(slots) + 1):
                            zr = F.pow(z, r)
                            for Ssub in combinations(slots, r):
                                w2 = list(w)
                                for s in Ssub: w2[s] = a
                                w2 = tuple(w2); img[w2] = F.add(img.get(w2, F.zero), zr)
                    rhs = {w: F.one for w in ws}
                    if i == b: addto(rhs, scaled(S[(a, j)], F.pow(z, q)))
                    if j == a: addto(rhs, scaled(S[(i, b)], F.neg(z)))
                    if i == b and j == a: addto(rhs, scaled(S[(a, b)], F.neg(F.pow(z, q + 1))))
                    img = {w: cf for w, cf in img.items() if cf != F.zero}; rhs = {w: cf for w, cf in rhs.items() if cf != F.zero}
                    cases += 1; failures += (img != rhs)
    return cases, failures


def diagonal_multipliers(q, F=None):
    """A diagonal matrix with entries x₀, x₁, x₂ multiplies S_{c(i,j)} by Π x_l^{c(i,j)_l} = (x₀x₁x₂)^{q−1} x_i^q x_j^{−1}: the exponent
    identity c(i,j) = (q−1)(1,1,1) + q e_i − e_j for the nine contents, as integers; returns True."""
    return all(tuple(c) == tuple(q - 1 + q * (l == i) - (l == j) for l in range(3)) for (i, j), c in word_contents(q).items())


def frobenius_identification(q):
    """On the frame g^{(q)} (entries raised to the power q) equals the conjugate ḡ and the inverse transpose g^{−T}, checked on the
    generators of small_frame(q); and the alternating form ε* is fixed (det g = 1). Returns (checked, ok)."""
    F, G, gens = small_frame(q)
    ok = True
    for g in gens:
        gq = tuple(tuple(F.pow(x, q) for x in row) for row in g)
        gc = tuple(tuple(F.conj(x) for x in row) for row in g)
        gt = tuple(tuple(g[j][i] for j in range(3)) for i in range(3))
        prod = I.mat_mul(F, gt, gc)                             # g^T ḡ = 1 ⟺ ḡ = g^{−T}
        ok &= gq == gc and prod == H.identity(F) and I.det(F, g) == F.one
    return len(gens), ok


def frobenius_tensor_fixed(q):
    """v_q is fixed by the generators of SU(3, F_q) acting by g^{⊗(4q−4)} ⊗ ḡ on the words (ḡ = g^{−T}): a direct check of (ii) at
    q = 2 (24 terms in 3⁵ coordinates), by the images of the words; returns True. (At q = 3 the direct check is the row identity's
    business: 1008 terms in 3⁹ coordinates.)"""
    F, G, gens = small_frame(q)
    v = frobenius_tensor(q); n = 4 * q - 3
    vF = {w: (F.one if cf == 1 else F.neg(F.one)) for w, cf in v.items()}
    for g in gens:
        gc = tuple(tuple(F.conj(x) for x in row) for row in g)
        img = {}
        for w, cf in vF.items():
            # the image of the word: the tensor product of the columns g[:, w_s] (ḡ for the dual slot)
            vec = {(): cf}
            for s in range(n):
                mat = g if s < n - 1 else gc
                new = {}
                for pref, c0 in vec.items():
                    for r in range(3):
                        x = mat[r][w[s]]
                        if x == F.zero: continue
                        new[pref + (r,)] = F.add(new.get(pref + (r,), F.zero), F.mul(c0, x))
                vec = new
            for w2, c2 in vec.items(): img[w2] = F.add(img.get(w2, F.zero), c2)
        img = {w: cf for w, cf in img.items() if cf != F.zero}
        if img != vF: return False
    return True


def frame_counts_small_field(q, degree, pairs=None):
    """M(a, b), the number of invariants of SU(3, F_q) in 3^{⊗a} ⊗ 3̄^{⊗b} over F_{q²}, for the pairs with a + b ≤ degree, a ≥ b
    (M(a, b) = M(b, a)): the exact solver on the words fixed by the frame's diagonal torus (the weights congruent modulo q + 1), the
    equations (g − 1)v = 0 of a generating pair, the field written as pairs over F_p with integer arithmetic modulo p (numpy, exact),
    the candidate space cut block by block and the result verified against every equation. Returns the dict (a, b) → M.
    q = 3 through degree 9 takes about a minute; beside it the compact counts interactions.su3_moment (46:C15)."""
    import numpy as np
    F, G, gens = small_frame(q); p = F.q; s, nn = F.s, F.n
    def pmul(a, b):                                             # (a₀ + a₁t)(b₀ + b₁t) with t² = s t + n, componentwise on arrays
        return ((a[0] * b[0] + nn * a[1] * b[1]) % p, (a[0] * b[1] + a[1] * b[0] + s * a[1] * b[1]) % p)
    def padd(a, b): return ((a[0] + b[0]) % p, (a[1] + b[1]) % p)
    def matmul(A, B):                                           # pair matrices (A0, A1) @ (B0, B1) mod p
        return ((A[0] @ B[0] + nn * (A[1] @ B[1])) % p, (A[0] @ B[1] + A[1] @ B[0] + s * (A[1] @ B[1])) % p)
    def nullspace_pairs(E):
        """the nullspace over F_{q²} of the pair matrix E (R × Z): the regular representation over F_p, elimination mod p."""
        E0, E1 = E; R, Z = E0.shape
        # x = x0 + x1 t: E x = (E0 x0 + n E1 x1) + (E0 x1 + E1 x0 + s E1 x1) t
        M = np.zeros((2 * R, 2 * Z), dtype=np.int64)
        M[:R, :Z] = E0; M[:R, Z:] = (nn * E1) % p; M[R:, :Z] = E1; M[R:, Z:] = (E0 + s * E1) % p
        nr, nc = M.shape; piv = []; r = 0
        for c in range(nc):
            if r >= nr: break
            nz = np.flatnonzero(M[r:, c])
            if not len(nz): continue
            k = r + nz[0]
            if k != r: M[[r, k]] = M[[k, r]]
            inv = pow(int(M[r, c]), -1, p); M[r] = (M[r] * inv) % p
            others = np.flatnonzero(M[:, c]); others = others[others != r]
            if len(others): M[others] = (M[others] - np.outer(M[others, c], M[r])) % p
            piv.append(c); r += 1
        free = [c for c in range(nc) if c not in piv]
        N = np.zeros((nc, len(free)), dtype=np.int64)
        for t, f in enumerate(free):
            N[f, t] = 1
            for ri, pc in enumerate(piv): N[pc, t] = (-M[ri, f]) % p
        # the F_p-solution space of dimension 2w is an F_{q²}-space of dimension w; its F_p-basis as pair columns (x0 above, x1 below)
        return (N[:Z], N[Z:])
    def rank_pairs(W):
        """the rank over F_{q²} of the pair matrix W: half the rank over F_p of its regular representation."""
        W0, W1 = W; Z, m = W0.shape
        M = np.zeros((2 * Z, 2 * m), dtype=np.int64)
        M[:Z, :m] = W0; M[:Z, m:] = (nn * W1) % p; M[Z:, :m] = W1; M[Z:, m:] = (W0 + s * W1) % p
        nr, nc = M.shape; r = 0
        for c in range(nc):
            if r >= nr: break
            nz = np.flatnonzero(M[r:, c])
            if not len(nz): continue
            k = r + nz[0]
            if k != r: M[[r, k]] = M[[k, r]]
            inv = pow(int(M[r, c]), -1, p); M[r] = (M[r] * inv) % p
            others = np.flatnonzero(M[:, c]); others = others[others != r]
            if len(others): M[others] = (M[others] - np.outer(M[others, c], M[r])) % p
            r += 1
        assert r % 2 == 0
        return r // 2
    out = {}
    for a in range(degree + 1):
        for b in range(degree + 1 - a):
            if a < b or (pairs is not None and (a, b) not in pairs): continue
            n = a + b
            if n == 0: out[(a, b)] = 1; continue
            # the columns: the signed orbit sums, under the letter permutations, of the words fixed by the frame's diagonal torus
            # (weights congruent modulo q + 1) — the fixed space of the monomial subgroup of the frame (the torus and the signed
            # permutation matrices of determinant 1), which contains every invariant; a word whose orbit sum vanishes is dropped
            from itertools import permutations
            dim = 3 ** n
            def index(w):
                idx = 0
                for l in w: idx = idx * 3 + l
                return idx
            seen = set(); columns = []
            for w in product(range(3), repeat=n):
                x = [0, 0, 0]
                for t_, l in enumerate(w): x[l] += 1 if t_ < a else -1
                if (x[0] - x[2]) % (q + 1) or (x[1] - x[2]) % (q + 1) or w in seen: continue
                signs = {}
                for sigma in permutations(range(3)):
                    # the signed permutation matrix: e_l ↦ ε e_{σ(l)}, ε = −1 for the letter at the negated coordinate of an odd σ
                    odd = sum(1 for i in range(3) for j in range(i + 1, 3) if sigma[i] > sigma[j]) % 2 == 1
                    neg = next(l for l in range(3) if sigma[l] == l) if odd else -1   # an odd permutation of 3 letters fixes one letter
                    sign = (-1) ** sum(1 for l in w if l == neg) if odd else 1
                    w2 = tuple(sigma[l] for l in w); seen.add(w2)
                    signs.setdefault(w2, set()).add(sign % p)
                # the orbit sum with each word once; a word reached with both signs (odd p) kills the whole orbit
                if any(len(v) > 1 for v in signs.values()): continue
                columns.append({w2: next(iter(v)) for w2, v in signs.items()})
            Z = len(columns)
            if Z == 0: out[(a, b)] = 0; continue
            # the equations: for each generator the images of the columns minus the columns themselves
            blocks = []
            for g in gens:
                g0 = np.array([[x[0] for x in row] for row in g]); g1 = np.array([[x[1] for x in row] for row in g])
                gc = tuple(tuple(F.conj(x) for x in row) for row in g)
                c0 = np.array([[x[0] for x in row] for row in gc]); c1 = np.array([[x[1] for x in row] for row in gc])
                E0 = np.zeros((dim, Z), dtype=np.int64); E1 = np.zeros((dim, Z), dtype=np.int64)
                for col, vec in enumerate(columns):
                    for w, cf in vec.items():
                        v = (np.array([cf]), np.array([0]))
                        for t_, l in enumerate(w):
                            m0, m1 = (g0, g1) if t_ < a else (c0, c1)
                            v = pmul((v[0][:, None], v[1][:, None]), (m0[:, l][None, :], m1[:, l][None, :]))
                            v = (v[0].reshape(-1), v[1].reshape(-1))
                        E0[:, col] = (E0[:, col] + v[0]) % p; E1[:, col] = (E1[:, col] + v[1]) % p
                        E0[index(w), col] = (E0[index(w), col] - cf) % p
                blocks.append((E0, E1))
            E0 = np.vstack([bk[0] for bk in blocks]); E1 = np.vstack([bk[1] for bk in blocks])
            # cut the candidate space with a first block of rows, then verify against all rows and refine
            W = (np.eye(Z, dtype=np.int64), np.zeros((Z, Z), dtype=np.int64))
            rows_first = min(E0.shape[0], Z + 16)
            N = nullspace_pairs((E0[:rows_first], E1[:rows_first])); W = matmul(W, N)
            for _ in range(8):
                if W[0].shape[1] == 0: break
                EW = matmul((E0, E1), W)
                bad = np.flatnonzero(EW[0].any(axis=1) | EW[1].any(axis=1))
                if not len(bad): break
                N = nullspace_pairs((EW[0][bad], EW[1][bad])); W = matmul(W, N)
            out[(a, b)] = rank_pairs(W) if W[0].shape[1] else 0
    return out


def first_departure_bounds(p):
    """46:C15: 2p ≤ d_* ≤ 4p − 3 on a Subject p > 3 — (26, 49), (346, 689), (3098, 6193) on the laboratory Subjects — the lower
    bound from the window through degree 2p − 1, the upper from the Frobenius tensor v_p at (4p − 4, 1)."""
    return (2 * p, 4 * p - 3)


def frame_window_orders(p):
    """The orders through which the frame's series equal the compact ones by 46:C15: the counts through degree 2p − 1, c₃ through
    β^{2p−2}, c₈ through β^{2p−3} — (25, 24, 23) on the Subject 13."""
    return (2 * p - 1, 2 * p - 2, 2 * p - 3)


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


# ---- the spectral amplitude of a plaquette and the transfer tally on the instance (46:B4, C16, C17, C18; 9 November 2026) ----
# The tally ring Z[ζ_3] (the ring of the instance q = 2, where M = lcm(3, 3) = 3) as integer pairs (a, b) = a + b z with
# z² = −1 − z; the inverse-phase conjugation sends z to z². Every function below is integer or finite-field arithmetic.

def z3_mul(x, y):
    """(a + b z)(c + d z) in Z[z], z² + z + 1 = 0."""
    a, b = x; c, d = y; bd = b * d
    return (a * c - bd, a * d + b * c - bd)


def z3_conj(x):
    """The inverse-phase conjugation z ↦ z² = −1 − z: a + b z ↦ (a − b) − b z."""
    a, b = x
    return (a - b, -b)


def z3_pow(x, k):
    r = (1, 0)
    for _ in range(k): r = z3_mul(r, x)
    return r


def conductor(q):
    """M = lcm(q² − 1, q² − q + 1): every eigenvalue of an element of SU(3, F_q) has order dividing M (Prop. prop:amplitude(i))."""
    a, b = q * q - 1, q * q - q + 1
    return a * b // gcd(a, b)


def subject_phase_table(pairs=None):
    """For the laboratory pairs (p, Ω): the conductor M(p), gcd(M, Ω − 1), whether 3 | p + 1 (a central element of order 3, Prop.
    prop:amplitude(iv)) and the order q² − q + 1 of the non-split torus against the Carrier's cycle Ω − 1 (gcd)."""
    pairs = pairs or LAB_PAIRS
    out = []
    for p, Om in pairs:
        M = conductor(p); ns = p * p - p + 1
        out.append({"p": p, "Omega": Om, "M": M, "gcd_M_cycle": gcd(M, Om - 1), "centre3": (p + 1) % 3 == 0,
                    "nonsplit": ns, "gcd_nonsplit_cycle": gcd(ns, Om - 1)})
    return out


def nonsplit_amplitude_exponents(q):
    """A generator of the non-split torus of SU(3, F_q) has the eigenvalues λ, λ^{q²}, λ^{q⁴} with λ of order n = q² − q + 1 in
    F_{q⁶} (the F_{q²}-conjugates; λ^{−q} = λ^{q⁴} since −q ≡ q⁴ (mod n)); its amplitude is ζ + ζ^{q²} + ζ^{q⁴} for ζ = ι(λ) of order n.
    Returns (n, the three exponents mod n, the exponent multiset of the paired weight w·w̄): on the Subject 13, n = 157,
    (1, 12, 144) and {0: 3, 11, 14, 25, 132, 143, 146: 1 each} — six distinct nontrivial phases, so the paired weight is not rational."""
    n = q * q - q + 1
    E = [1 % n, (q * q) % n, (q ** 4) % n]
    assert (-q) % n == E[2], "λ^{−q} is the third conjugate"
    pw = {}
    for a in E:
        for b in E:
            k = (a - b) % n; pw[k] = pw.get(k, 0) + 1
    return n, E, pw


def _mat_mul(F, X, Y):
    return tuple(tuple(F.add(F.add(F.mul(X[i][0], Y[0][j]), F.mul(X[i][1], Y[1][j])), F.mul(X[i][2], Y[2][j])) for j in range(3)) for i in range(3))


def _mat_id(F):
    return tuple(tuple(F.one if i == j else F.zero for j in range(3)) for i in range(3))


def _mat_pow(F, X, k):
    R = _mat_id(F); B = X
    while k:
        if k & 1: R = _mat_mul(F, R, B)
        B = _mat_mul(F, B, B); k >>= 1
    return R


def element_order(F, U, bound=10 ** 6):
    I3 = _mat_id(F); k, B = 1, U
    while B != I3:
        B = _mat_mul(F, B, U); k += 1
        if k > bound: raise ValueError("element_order: bound exceeded")
    return k


def semisimple_part(F, U, p):
    """U = U_s U_n by powers: the order of U is p^a m with p ∤ m; e ≡ 0 (mod p^a), e ≡ 1 (mod m); U_s = U^e, U_n = U_s^{−1} U.
    Returns (U_s, U_n, e, p^a, m). U_s is the unique element of ⟨U⟩ of order dividing m with U U_s^{−1} of p-power order."""
    n = element_order(F, U); a = 0
    while n % p == 0: n //= p; a += 1
    m, pa = n, p ** a
    e = next(e for e in range(1, pa * m + 1) if e % pa == 0 and e % m == 1) if m > 1 else pa
    Us = _mat_pow(F, U, e)
    Un = _mat_mul(F, _mat_pow(F, Us, m * pa - 1), U)      # U_s^{−1} = U_s^{ord − 1} with ord | m·p^a
    return Us, Un, e, pa, m


def _rank(F, M):
    M = [list(r) for r in M]; rk = 0; rows = len(M); cols = len(M[0]) if rows else 0
    for c in range(cols):
        piv = next((r for r in range(rk, rows) if M[r][c] != F.zero), None)
        if piv is None: continue
        M[rk], M[piv] = M[piv], M[rk]
        iv = F.inv(M[rk][c]); M[rk] = [F.mul(iv, x) for x in M[rk]]
        for r in range(rows):
            if r != rk and M[r][c] != F.zero:
                f = M[r][c]; M[r] = [F.sub(x, F.mul(f, y)) for x, y in zip(M[r], M[rk])]
        rk += 1
    return rk


def eigenvalues_in_f_q2(F, S):
    """The eigenvalue multiset {λ: multiplicity} of a semisimple S whose eigenvalues lie in F_{q²} (multiplicity 3 − rank(S − λ))."""
    out = {}
    for lam in F.elements():
        D = tuple(tuple(F.sub(S[i][j], lam) if i == j else S[i][j] for j in range(3)) for i in range(3))
        m = 3 - _rank(F, D)
        if m: out[lam] = m
    assert sum(out.values()) == 3, "eigenvalues outside F_{q²}"
    return out


def spectral_amplitude_instance(F=None, G=None):
    """The spectral amplitude w(U) = Σ ι(λ_j(U_s)) on the 216 elements of SU(3, F_2) over F_4 = F_2[t]/(t² + t + 1), ι(t) = z
    (46:B4). Every eigenvalue of a semisimple element lies in F_4 (its order divides 3). Returns a dict with the amplitudes
    (W: element → (a, b)), the distribution, the counts of elements of even order per value, the element orders, the class
    count, the moments μ_{a,b} = (1/216) Σ w^a w̄^b at (1,1), (3,0), (2,2), the full sum, the involutions U, V of
    Thm. thm:amplitude with their product, and the checks of Prop. prop:amplitude(ii)–(iii) on every element."""
    if F is None: F, G, _ = small_frame(2)
    q = 2; I3 = _mat_id(F); t = (0, 1); tt = F.mul(t, t)
    assert F.mul(tt, t) == F.one and t != F.one
    iota = {F.one: (1, 0), t: (0, 1), tt: (-1, -1)}
    W, dist, even, orders = {}, {}, {}, {}
    inv = {}
    for U in G:
        Us, Un, e, pa, m = semisimple_part(F, U, q)
        o = pa * m
        assert _mat_mul(F, Us, Un) == U and _mat_pow(F, Us, m) == I3 and _mat_pow(F, Un, pa) == I3
        assert _mat_pow(F, U, 4) == Us, "the exponent 4 gives the semisimple part of every element"
        em = eigenvalues_in_f_q2(F, Us)
        w = (0, 0)
        for lam, mult in em.items():
            w = (w[0] + mult * iota[lam][0], w[1] + mult * iota[lam][1])
        # the trace reduces: Σ λ_j = Tr U_s = Tr U
        tr = F.add(F.add(U[0][0], U[1][1]), U[2][2]); trs = F.zero
        for lam, mult in em.items():
            for _ in range(mult): trs = F.add(trs, lam)
        assert trs == tr
        if o % q == 0:   # Prop. (iii): eigenvalues (λ, λ, λ⁻²), λ^{q+1} = 1
            lam = max(em, key=em.get); assert em[lam] >= 2 and F.pow(lam, q + 1) == F.one
            if em[lam] == 2: assert list(k for k in em if k != lam) == [F.inv(F.mul(lam, lam))]
            even[w] = even.get(w, 0) + 1
        W[U] = w; dist[w] = dist.get(w, 0) + 1; orders[o] = orders.get(o, 0) + 1
        inv[U] = _mat_pow(F, U, o - 1)
    for U in G: assert W[inv[U]] == z3_conj(W[U])          # Prop. (ii): w(U⁻¹) = conj
    seen, classes = set(), 0
    for U in G:
        if U in seen: continue
        cl = {_mat_mul(F, _mat_mul(F, h, U), inv[h]) for h in G}; seen |= cl; classes += 1
        assert len({W[x] for x in cl}) == 1                   # a class function
    def moment(a, b):
        s = (0, 0)
        for U in G:
            x = z3_mul(z3_pow(W[U], a), z3_pow(z3_conj(W[U]), b)); s = (s[0] + x[0], s[1] + x[1])
        assert s[0] % len(G) == 0 and s[1] % len(G) == 0
        return (s[0] // len(G), s[1] // len(G))
    total = (sum(w[0] for w in W.values()), sum(w[1] for w in W.values()))
    Umat = tuple(tuple(F.one if (i, j) in ((0, 2), (1, 1), (2, 0)) else F.zero for j in range(3)) for i in range(3))
    Vmat = ((F.zero, F.zero, t), (F.zero, F.one, F.zero), (tt, F.zero, F.zero))
    assert Umat in W and Vmat in W
    return {"F": F, "G": G, "W": W, "inv": inv, "distribution": dist, "even_order": even, "orders": orders, "classes": classes,
            "moments": {ab: moment(*ab) for ab in ((1, 1), (3, 0), (2, 2))}, "sum": total,
            "involutions": (Umat, Vmat, W[Umat], W[Vmat], W[_mat_mul(F, Umat, Vmat)], element_order(F, _mat_mul(F, Umat, Vmat)))}


def transfer_tally_instance(amp=None):
    """The transfer tally on SU(3, F_2) (46:C18): the step of one plaquette, (Kf)(x) = ⟨w(x⁻¹y) f(y)⟩_y with the frame's mean
    (46:B3). Its matrix has the entries w(x⁻¹y)/216; the matrix A = 216 K of the entries w(x⁻¹y) is held as two integer matrices
    (A + B z), with numpy (exact int64): tr A, tr A², the annihilating polynomial A(A + 72)(A − 36)(A − 144) = 0, the nullities of
    A − λI for λ = 144, 36, 0, −72 (Gaussian elimination modulo a prime P ≡ 1 (mod 3) with z a cube root of unity: each nullity is at
    least the nullity over Q(z), and the four sum to 216 as the exact ones do, so they are exact), A·1 = 0 and the negative quadratic
    value at (1, −1, −1) on (I, U, V). The statements on K are these divided by the order 216, as Fractions: the eigenvalues
    2/3, 1/6, 0, −1/3 with the same multiplicities, tr K = 3, tr K² = 8, the quadratic value −1/72. Returns a dict."""
    import numpy as np
    if amp is None: amp = spectral_amplitude_instance()
    F, G, W, inv = amp["F"], amp["G"], amp["W"], amp["inv"]
    n = len(G); idx = {g: i for i, g in enumerate(G)}
    KA = np.zeros((n, n), dtype=np.int64); KB = np.zeros((n, n), dtype=np.int64)
    for x in G:
        xi = inv[x]
        for y in G:
            w = W[_mat_mul(F, xi, y)]; KA[idx[x], idx[y]] = w[0]; KB[idx[x], idx[y]] = w[1]
    def mul(X, Y):
        A, B = X; C, D = Y; BD = B @ D
        return (A @ C - BD, A @ D + B @ C - BD)
    def shift(X, c):
        A, B = X; return (A + c * np.eye(n, dtype=np.int64), B)
    K = (KA, KB); K2 = mul(K, K)
    roots = [144, 36, 0, -72]
    P = mul(mul(mul(K, shift(K, 72)), shift(K, -36)), shift(K, -144))
    annihilated = not P[0].any() and not P[1].any()
    one = np.ones(n, dtype=np.int64)
    K_one = (KA @ one, KB @ one)
    Pm = 1000000009                                   # ≡ 1 (mod 3)
    zr = next(pow(g, (Pm - 1) // 3, Pm) for g in range(2, 1000) if pow(g, (Pm - 1) // 3, Pm) != 1)
    assert (zr * zr + zr + 1) % Pm == 0
    def rank_mod(M):
        M = [[int(v) % Pm for v in row] for row in M]; rk = 0; rows = len(M); cols = len(M[0])
        for c in range(cols):
            piv = next((r for r in range(rk, rows) if M[r][c]), None)
            if piv is None: continue
            M[rk], M[piv] = M[piv], M[rk]
            iv = pow(M[rk][c], Pm - 2, Pm); M[rk] = [v * iv % Pm for v in M[rk]]
            for r in range(rows):
                if r != rk and M[r][c]:
                    f = M[r][c]; M[r] = [(v - f * u) % Pm for v, u in zip(M[r], M[rk])]
            rk += 1
        return rk
    mults = {}
    for lam in roots:
        Mz = ((KA - lam * np.eye(n, dtype=np.int64)) + zr * KB) % Pm
        mults[lam] = n - rank_mod(Mz.tolist())
    Umat, Vmat = amp["involutions"][0], amp["involutions"][1]
    I3 = _mat_id(F)
    sub = [[W[_mat_mul(F, inv[a], b)] for b in (I3, Umat, Vmat)] for a in (I3, Umat, Vmat)]
    v = (1, -1, -1)
    quad = (sum(v[i] * v[j] * sub[i][j][0] for i in range(3) for j in range(3)), sum(v[i] * v[j] * sub[i][j][1] for i in range(3) for j in range(3)))
    trace = (int(np.trace(KA)), int(np.trace(KB))); trace2 = (int(np.trace(K2[0])), int(np.trace(K2[1])))
    mean = {"eigenvalues": {Q(lam, n): m for lam, m in mults.items()},                 # the eigenvalues of K = A/216 with their multiplicities
            "trace": (Q(trace[0], n), Q(trace[1], n)), "trace2": (Q(trace2[0], n * n), Q(trace2[1], n * n)),
            "quadratic": (Q(quad[0], n), Q(quad[1], n))}
    return {"trace": trace, "trace2": trace2,
            "annihilated": annihilated, "multiplicities": mults, "K_one_zero": not K_one[0].any() and not K_one[1].any(),
            "submatrix": sub, "quadratic": quad, "n": n, "mean": mean}


def transfer_annihilator_coefficients():
    """x(x + 72)(x − 36)(x − 144) = x⁴ − 108x³ − 7776x² + 373248x, ascending: [0, 373248, −7776, −108, 1]."""
    poly = [1]
    for r in (0, -72, 36, 144):
        poly = [0] + poly
        poly = [poly[i] - (r * poly[i + 1] if i + 1 < len(poly) else 0) for i in range(len(poly))]
    return poly


def transfer_annihilator_mean():
    """The annihilating polynomial of the step K = A/216 (46:C18): x(3x + 1)(6x − 1)(3x − 2) = 54x⁴ − 27x³ − 9x² + 2x, ascending
    [0, 2, −9, −27, 54]; it is the polynomial of A at X = 216x divided by 216 · 72 · 36 · 72 (asserted)."""
    poly = [1]
    for num, den in ((0, 1), (-1, 3), (1, 6), (2, 3)):                    # the factors (den · x − num)
        poly = [0] + poly
        poly = [den * poly[i] - (num * poly[i + 1] if i + 1 < len(poly) else 0) for i in range(len(poly))]
    A = transfer_annihilator_coefficients(); c = 216 * 72 * 36 * 72
    assert all(A[k] * 216 ** k == c * poly[k] for k in range(5)), "the polynomial of A at X = 216x"
    return poly


# ---- the transfer tally on the Subjects (46:C19, 10 November 2026): the amplitude's character expansion from the generic
#      character table of SU(3, q) (Simpson–Frame 1973; the CHEVIE table), by exact character sums — no floating point.
#      Class types (parameter l), with |C| = |G| / |C_G| and the amplitude of a representative:
#        1 central zI, z = Z(q²)^{l(q²−1)/d}, d = gcd(q+1, 3):  w = 3 ζ_d^l                                   |C_G| = |G|
#        2 z · transvection:                                    w = 3 ζ_d^l                                   |C_G| = q³(q+1)
#        3 z · regular unipotent, l = (l1, l2):                 w = 3 ζ_d^{l1}                                |C_G| = q² d
#        4 diag(a, a, a⁻²), a of order dividing q+1, l·d ≢ 0:   w = 2 ζ_{q+1}^l + ζ_{q+1}^{−2l}               |C_G| = q(q+1)²(q−1)
#        5 the same with a unipotent part:                      w = 2 ζ_{q+1}^l + ζ_{q+1}^{−2l}               |C_G| = q(q+1)
#        6 diag(a1, a2, a3), l1 + l2 + l3 ≡ 0 (q+1), distinct:  w = Σ ζ_{q+1}^{li}                            |C_G| = (q+1)²
#        7 the (q²−1)-torus, x ≢ 0 (q−1), orbit {x, −qx}:       w = ζ_{q²−1}^{x(q−1)} + ζ_{q²−1}^x + ζ_{q²−1}^{−qx}   |C_G| = q²−1
#        8 the Coxeter torus, x·d ≢ 0 (m), orbit {x, −qx, q²x}: w = ζ_m^x + ζ_m^{−qx} + ζ_m^{q²x}, m = q²−q+1   |C_G| = m
#      The three candidate characters (the first members, k = 1, of the families of degrees q² − q + 1, q³ + 1, (q+1)²(q−1)) on the
#      types, from the table (0 where a type is not listed):
#        χ₁ (q²−q+1):  1: (q²−q+1) ζ_d^l   2: (1−q) ζ_d^l   3: ζ_d^{l1}   4: (1−q) ζ_{q+1}^l + ζ_{q+1}^{−2l}   5: ζ_{q+1}^l + ζ_{q+1}^{−2l}
#                      6: Σ ζ_{q+1}^{li}   7: ζ_{q+1}^x
#        χ₂ (q³+1):    1: (q³+1) ζ_d^l     2: ζ_d^l         3: ζ_d^{l1}   4: (q+1) ζ_{q+1}^l                    5: ζ_{q+1}^l
#                      7: ζ_{q²−1}^x + ζ_{q²−1}^{−qx}
#        χ₃ ((q+1)²(q−1)): 1: (q+1)²(q−1) ζ_d^l   2: −(q+1) ζ_d^l   3: −ζ_d^{l1}   8: −(ζ_m^x + ζ_m^{−qx} + ζ_m^{q²x})
#      |G| a_χ = Σ_C |C| w(C) conj(χ(C)) is a rational integer (Green's theorem, 46:A14); each product is a sum of terms c ζ_n^{L(l)}
#      with L linear in the parameters, and Σ_{l ∈ Z/n} ζ_n^{cl} = n [n | c], the non-regular parameters removed by inclusion–exclusion
#      (amplitude_coefficients). The same five sums from the explicit class list, as exponent tables in Z[ζ_N], N = lcm(q²−1, m),
#      traced to Z through the Ramanujan sums c_N(e) = Σ_{t | gcd(e,N)} t μ(N/t), Tr(S) = φ(N) S for rational S
#      (amplitude_coefficients_direct, the cross-check for enumerable class lists).

def su3_order(q):
    """|SU(3, F_q)| = q³ (q+1)² (q−1) (q² − q + 1)."""
    return q ** 3 * (q + 1) ** 2 * (q - 1) * (q * q - q + 1)


def _geom(n, c):
    """Σ_{l ∈ Z/n} ζ_n^{c l} = n if n | c else 0."""
    return n if c % n == 0 else 0


def amplitude_coefficients(q):
    """The exact character sums on SU(3, F_q), q ≥ 3: {"a1": a on χ₁, "a2": a on χ₂, "a3": a on χ₃, "moment": Σ_χ a_χ² = (1/|G|) Σ_G |w|²,
    "trivial": a on the trivial character = (1/|G|) Σ_G w}, by Σ_{l ∈ Z/n} ζ_n^{cl} = n [n | c] over the class types with the non-regular
    parameters removed by inclusion–exclusion. Every intermediate value is a rational number; the results are asserted integers."""
    assert q >= 3, "the three candidates are irreducible characters for q >= 3 only (q = 2 is the exceptional instance, 46:C18)"
    d = gcd(q + 1, 3); m = q * q - q + 1; n1 = q + 1; n2 = q * q - 1; G = su3_order(q)
    targets = ("a1", "a2", "a3", "moment", "trivial")
    S = {t: Q(0) for t in targets}

    def prod(Aterms, Bterms):            # (Σ a ζ^{La}) · conj(Σ b ζ^{Lb}): terms (coefficient, modulus, linear form)
        out = []
        for ca, na, La in Aterms:
            for cb, nb, Lb in Bterms:
                assert na == nb
                out.append((ca * cb, na, tuple(x - y for x, y in zip(La, Lb))))
        return out

    # types 1, 2, 3 (parameter l ∈ Z/d; type 3 has a second parameter on which nothing depends: the factor d)
    for size, mult, chis in ((1, 1, {"a1": (m, 1), "a2": (q ** 3 + 1, 1), "a3": (n1 ** 2 * (q - 1), 1)}),
                             (G // (q ** 3 * n1), 1, {"a1": (1 - q, 1), "a2": (1, 1), "a3": (-n1, 1)}),
                             (G // (q * q * d), d, {"a1": (1, 1), "a2": (1, 1), "a3": (-1, 1)})):
        w = [(3, d, (1,))]
        f = {t: [(c, d, (e,))] for t, (c, e) in chis.items()}; f["moment"] = w; f["trivial"] = [(1, d, (0,))]
        for t in targets:
            S[t] += Q(size * mult) * sum(c * _geom(d, L[0]) for c, n, L in prod(w, f[t]))
    # types 4, 5 (l ∈ Z/(q+1), l·d ≢ 0: the full sum less the d values l = j(q+1)/d, Σ_j ζ_{q+1}^{c j (q+1)/d} = Σ_j ζ_d^{c j})
    w45 = [(2, n1, (1,)), (1, n1, (-2,))]
    for size, c1, c2 in ((G // (q * n1 ** 2 * (q - 1)), [(1 - q, n1, (1,)), (1, n1, (-2,))], [(n1, n1, (1,))]),
                         (G // (q * n1), [(1, n1, (1,)), (1, n1, (-2,))], [(1, n1, (1,))])):
        f = {"a1": c1, "a2": c2, "a3": [], "moment": w45, "trivial": [(1, n1, (0,))]}
        for t in targets:
            if f[t]: S[t] += Q(size) * sum(c * (_geom(n1, L[0]) - _geom(d, L[0])) for c, n, L in prod(w45, f[t]))
    # type 6 (unordered distinct triples with l1 + l2 + l3 ≡ 0, parameters (l1, l2), l3 = −l1 − l2):
    # Σ_unordered = (1/6) Σ_ordered-distinct, ordered-distinct = all − {l1 = l2} − {l1 = l3} − {l2 = l3} + 2 {all equal}
    w6 = [(1, n1, (1, 0)), (1, n1, (0, 1)), (1, n1, (-1, -1))]
    size6 = G // n1 ** 2
    for t, chi in (("a1", w6), ("moment", w6), ("trivial", [(1, n1, (0, 0))])):
        tot = Q(0)
        for c, n, (c1, c2) in prod(w6, chi):
            tot += c * (_geom(n1, c1) * _geom(n1, c2) - _geom(n1, c1 + c2) - _geom(n1, c1 - 2 * c2) - _geom(n1, c2 - 2 * c1) + 2 * _geom(d, c1 + c2))
        S[t] += Q(size6) * tot / 6
    # type 7 (x ∈ Z/(q²−1), x ≢ 0 (q−1); one representative per orbit {x, −qx}, of size 2 exactly on the regular x):
    # Σ_reps = (1/2)(Σ_all − Σ_{x = j(q−1)}), Σ_j ζ_{q²−1}^{c j (q−1)} = Σ_j ζ_{q+1}^{c j}
    w7 = [(1, n2, (q - 1,)), (1, n2, (1,)), (1, n2, (-q,))]
    size7 = G // n2
    for t, chi in (("a1", [(1, n2, (q - 1,))]), ("a2", [(1, n2, (1,)), (1, n2, (-q,))]), ("moment", w7), ("trivial", [(1, n2, (0,))])):
        S[t] += Q(size7) * sum(c * (_geom(n2, L[0]) - _geom(n1, L[0])) for c, n, L in prod(w7, chi)) / 2
    # type 8 (x ∈ Z/m, x·d ≢ 0 (m); one representative per orbit {x, −qx, q²x}, of size 3 exactly on the regular x):
    # Σ_reps = (1/3)(Σ_all − Σ_{x = j m/d}), Σ_j ζ_m^{c j m/d} = Σ_j ζ_d^{c j}
    w8 = [(1, m, (1,)), (1, m, (-q,)), (1, m, (q * q,))]
    size8 = G // m
    for t, chi in (("a3", [(-1, m, (1,)), (-1, m, (-q,)), (-1, m, (q * q,))]), ("moment", w8), ("trivial", [(1, m, (0,))])):
        S[t] += Q(size8) * sum(c * (_geom(m, L[0]) - _geom(d, L[0])) for c, n, L in prod(w8, chi)) / 3
    out = {}
    for t in targets:
        v = S[t] / G; assert v.denominator == 1, (t, S[t], G); out[t] = int(v)
    return out


def _factor(n):
    f = {}; p = 2
    while p * p <= n:
        while n % p == 0: f[p] = f.get(p, 0) + 1; n //= p
        p += 1 if p == 2 else 2
    if n > 1: f[n] = f.get(n, 0) + 1
    return f


def _divisors(f):
    out = [1]
    for p, e in f.items(): out = [x * p ** k for x in out for k in range(e + 1)]
    return out


def amplitude_coefficients_direct(q):
    """The same five sums from the explicit class list (every class with its size and its values as exponent tables over ζ_N,
    N = lcm(q² − 1, q² − q + 1)), each weighted sum S collected as an exponent table in Z[ζ_N] and traced to Z: Tr(ζ_N^e) = c_N(e) =
    Σ_{t | gcd(e, N)} t μ(N/t), S = Tr(S)/φ(N) for rational S (the division asserted exact). For enumerable class lists (q ≤ 13)."""
    assert 3 <= q <= 16
    d = gcd(q + 1, 3); m = q * q - q + 1; n1 = q + 1; n2 = q * q - 1; N = n2 * m // gcd(n2, m); G = su3_order(q)
    u1, u2, u3, u4 = N // d, N // n1, N // n2, N // m
    classes = []       # (size, w, chi1, chi2, chi3) with each value a list of (coefficient, exponent mod N)
    for l in range(d):
        classes.append((1, [(3, u1 * l)], [(m, u1 * l)], [(q ** 3 + 1, u1 * l)], [(n1 ** 2 * (q - 1), u1 * l)]))
        classes.append((G // (q ** 3 * n1), [(3, u1 * l)], [(1 - q, u1 * l)], [(1, u1 * l)], [(-n1, u1 * l)]))
        for l2 in range(d): classes.append((G // (q * q * d), [(3, u1 * l)], [(1, u1 * l)], [(1, u1 * l)], [(-1, u1 * l)]))
    for l in range(n1):
        if (l * d) % n1 == 0: continue
        w = [(2, u2 * l), (1, u2 * ((-2 * l) % n1))]
        classes.append((G // (q * n1 ** 2 * (q - 1)), w, [(1 - q, u2 * l), (1, u2 * ((-2 * l) % n1))], [(n1, u2 * l)], []))
        classes.append((G // (q * n1), w, [(1, u2 * l), (1, u2 * ((-2 * l) % n1))], [(1, u2 * l)], []))
    for l1 in range(n1):
        for l2 in range(l1 + 1, n1):
            l3 = (-l1 - l2) % n1
            if l2 < l3:
                w = [(1, u2 * l1), (1, u2 * l2), (1, u2 * l3)]; classes.append((G // n1 ** 2, w, w, [], []))
    for x in range(n2):
        if x % (q - 1) != 0 and x <= (-q * x) % n2:
            classes.append((G // n2, [(1, u3 * ((x * (q - 1)) % n2)), (1, u3 * x), (1, u3 * ((-q * x) % n2))], [(1, u2 * (x % n1))],
                            [(1, u3 * x), (1, u3 * ((-q * x) % n2))], []))
    for x in range(1, m):
        if (x * d) % m != 0 and x <= (-q * x) % m and x <= (q * q * x) % m:
            w = [(1, u4 * x), (1, u4 * ((-q * x) % m)), (1, u4 * ((q * q * x) % m))]
            classes.append((G // m, w, [], [], [(-c, e) for c, e in w]))
    assert sum(c[0] for c in classes) == G
    fN = _factor(N); phiN = 1
    for p, e in fN.items(): phiN *= (p - 1) * p ** (e - 1)
    divs = _divisors(fN)
    def mu(n):
        f = _factor(n)
        return 0 if any(e > 1 for e in f.values()) else (-1) ** len(f)
    ram = {}
    def c_N(e):
        g = gcd(e, N)
        if g not in ram: ram[g] = sum(t * mu(N // t) for t in divs if g % t == 0)
        return ram[g]
    out = {}
    for name, idx in (("a1", 2), ("a2", 3), ("a3", 4), ("moment", 1), ("trivial", None)):
        table = {}
        for cl in classes:
            size, w = cl[0], cl[1]; f = cl[idx] if idx is not None else [(1, 0)]
            for cw, ew in w:
                for cf, ef in f:
                    e = (ew - ef) % N; table[e] = table.get(e, 0) + size * cw * cf
        tr = sum(c * c_N(e) for e, c in table.items())
        assert tr % phiN == 0, (name, tr, phiN); S = tr // phiN
        assert S % G == 0, (name, S, G); out[name] = S // G
    out["classes"] = len(classes); out["N"] = N
    return out


def transfer_spectrum_subject(q):
    """The transfer tally's spectrum on SU(3, F_q) from the expansion w = χ₁ + χ₂ − χ₃ (q ≥ 3), for a laboratory frame (46:C19): the
    degrees d, the eigenvalues a_χ/χ(1) = 1/(q²−q+1), 1/(q³+1), −1/((q+1)²(q−1)) of the step with the frame's mean (Fractions), their
    multiplicities χ(1)², the zero eigenvalue's multiplicity, and the checks Σ d²e = Σ a d = 3 (tr K), Σ d²e² = Σ a² = 3 (tr K²),
    Σ d² < |G|, e₃ < 0. The "levels" |G| a_χ/χ(1) = q³(q+1)²(q−1), q³(q²−1), −q³(q²−q+1) are the eigenvalues times the order of the
    frame, counts of frame moves (46:B3): the laboratory frames keep them, and a Subject reads the order of its frame as 0."""
    assert q < 10 ** 4, "a laboratory frame: the order of the frame is formed"
    G = su3_order(q); m = q * q - q + 1
    degrees = (m, q ** 3 + 1, (q + 1) ** 2 * (q - 1))
    coefficients = (1, 1, -1)
    levels = tuple(G * a // dg for a, dg in zip(coefficients, degrees))
    assert all((G * a) % dg == 0 for a, dg in zip(coefficients, degrees))
    closed = (q ** 3 * (q + 1) ** 2 * (q - 1), q ** 3 * (q * q - 1), -q ** 3 * m)
    mult = {lev: dg * dg for lev, dg in zip(levels, degrees)}
    zero = G - sum(mult.values())
    eigenvalues = tuple(Q(a, dg) for a, dg in zip(coefficients, degrees))
    checks = {"levels_closed": levels == closed,
              "eigenvalues_are_levels_over_order": all(e * G == l for e, l in zip(eigenvalues, levels)),
              "mean_trace": sum(dg * dg * e for dg, e in zip(degrees, eigenvalues)) == 3,
              "mean_trace2": sum(dg * dg * e * e for dg, e in zip(degrees, eigenvalues)) == 3,
              "degree_identity": sum(a * dg for a, dg in zip(coefficients, degrees)) == 3,
              "trace": sum(l * mm for l, mm in mult.items()) == 3 * G,
              "trace2": sum(l * l * mm for l, mm in mult.items()) == 3 * G * G,
              "zero_positive": zero > 0, "negative_level": levels[2] < 0, "distinct": len(set(levels)) == 3}
    return {"q": q, "order": G, "degrees": degrees, "coefficients": coefficients, "eigenvalues": eigenvalues, "levels": levels,
            "multiplicities": mult, "zero": zero, "checks": checks, "ok": all(checks.values())}


# ---- the tally of the ring and the gap of the transfer tally (46:B3, C20; 10 November 2026) --------------------------------
# The finite theory is declared on a ring of n plaquettes, one per step of the drive (46:B3): plaquette i has the boundary links
# t_i, b_i and the rungs r_i, r_{i+1} (indices modulo n), its element U_i = t_i r_{i+1} b_i⁻¹ r_i⁻¹, and the tally is the frame's
# mean over the rungs, Z_n = ⟨Π_i w(U_i)⟩. By the orthogonality relations in their mean form the term of χ in Z_n is the product
# of n factors a_χ/χ(1) times χ(h₁) conj χ(h₂), h₁ = t₁⋯t_n, h₂ = b₁⋯b_n: one further plaquette multiplies it by a_χ/χ(1), and no
# order of the frame enters. The order |G| and the number of rung configurations are counts of frame moves; above the totality's
# count Ω ∼ 10¹²³ such a count is the chart's (46:B3), and nothing below forms one. On the frames of 46:C19 three characters
# survive (ring_step, ring_gap, split_torus_characters). The gluing identity is checked on the instance with no character table
# (ring_gluing_instance).


def ring_step(q):
    """The step of one plaquette on SU(3, F_q), q ≥ 3 (46:C20): the three multipliers a_i/d_i = 1/d₁, 1/d₂, −1/d₃ of the terms of
    χ₁, χ₂, χ₃ in the ring's tally, d₁ = q² − q + 1, d₂ = q³ + 1, d₃ = (q+1)²(q−1), as Fractions. They are the nonzero eigenvalues of
    the transfer tally (46:C19) and involve no order of the frame. On a Subject the degrees are counts, read modulo p as 1, 1
    and −1 (ring_residue)."""
    assert q >= 3
    m = q * q - q + 1
    degrees = (m, q ** 3 + 1, (q + 1) ** 2 * (q - 1))
    return {"q": q, "degrees": degrees, "multipliers": (Q(1, degrees[0]), Q(1, degrees[1]), Q(-1, degrees[2]))}


def ring_gap(q):
    """The gap of the transfer tally on SU(3, F_q), q ≥ 3 (46:C20), on the degrees: d₂ = (q+1) d₁, d₃ = (q+1)(q² − 1),
    d₃ − d₂ = (q+1)(q−2) > 0, so the eigenvalues have 1/d₁ > 1/d₂ > 1/d₃ > 0; the degrees reduce to 1, 1, −1 modulo q, so the three
    multipliers reduce to 1. Returns the gap d₁/d₂ = 1/(q+1) and the third ratio d₁/d₃ = (1/(q+1)) · (q²−q+1)/(q²−1) as Fractions,
    with the checks."""
    assert q >= 3
    st = ring_step(q); d1, d2, d3 = st["degrees"]; e1, e2, e3 = st["multipliers"]
    checks = {"second_degree_is_q_plus_one_times_first": d2 == (q + 1) * d1,
              "third_degree": d3 == (q + 1) * (q * q - 1),
              "ordered": e1 > e2 > -e3 > 0, "third_minus_second": d3 - d2 == (q + 1) * (q - 2),
              "degrees_modulo_q": (d1 % q, d2 % q, d3 % q) == (1, 1, q - 1),
              "multipliers_are_the_eigenvalues": (e1, e2, e3) == transfer_spectrum_subject(q)["eigenvalues"] if q < 10 ** 4 else True}
    gap, third = e2 / e1, -e3 / e1
    return {"q": q, "gap": gap, "third": third, "checks": checks,
            "ok": all(checks.values()) and gap == Q(1, q + 1) and third == Q(1, q + 1) * Q(q * q - q + 1, q * q - 1)}


def spectrum_in_pi(p):
    """The spectrum of the transfer tally in 2π = p − 1, the phase cycle of the Subject's shell (46:C21), p = 4κ + 1: with π = 2κ,
    d₁ = 4π² + 2π + 1, d₂ = (2π + 2) d₁, d₃ = 8π(π + 1)², the gap 1/(2π + 2) and the third ratio (4π² + 2π + 1)/(8π(π + 1)²), pure
    numbers of the Subject and one expression on every Subject; 2π ≡ −1 and 2π + 2 ≡ 1 modulo p, the residue 1 of 46:C20.
    [chart] With the classical π enclosed in (3.1415926, 3.1415927) the gap lies in (0.12072, 0.12073) and reads 0.1207; the
    enclosure is rational, and no float decides anything."""
    assert p % 4 == 1 and p >= 13
    pi = (p - 1) // 2; g = ring_gap(p); d1, d2, d3 = ring_step(p)["degrees"]
    lo, hi = Q(31415926, 10 ** 7), Q(31415927, 10 ** 7)
    chart = (1 / (2 * hi + 2), 1 / (2 * lo + 2))
    checks = {"p_is_two_pi_plus_one": p == 2 * pi + 1, "pi_is_twice_the_capacity": pi == 2 * ((p - 1) // 4),
              "first_degree": d1 == 4 * pi * pi + 2 * pi + 1, "second_degree": d2 == (2 * pi + 2) * d1,
              "third_degree": d3 == 8 * pi * (pi + 1) ** 2,
              "gap": g["gap"] == Q(1, 2 * pi + 2), "third_ratio": g["third"] == Q(4 * pi * pi + 2 * pi + 1, 8 * pi * (pi + 1) ** 2),
              "two_pi_is_minus_one": (2 * pi + 1) % p == 0, "two_pi_plus_two_is_one": (2 * pi + 2) % p == 1,
              "chart_numeral": Q(12072, 10 ** 5) < chart[0] < chart[1] < Q(12073, 10 ** 5)}
    return {"p": p, "pi": pi, "degrees": (d1, d2, d3), "gap": g["gap"], "third": g["third"], "chart": chart, "checks": checks,
            "ok": g["ok"] and all(checks.values())}


def instance_adjoint_fixed(nmax=4):
    """The vectors of 8^{⊗n}, n = 1, …, nmax, fixed on the instance SU(3, F_2) over F_4 (46:C22), in three exact steps: the basis
    tensors fixed by the diagonal torus T (order 9), among them the vectors fixed by the cyclic permutation c (with T the normal
    subgroup of order 27), and among those the vectors fixed by two further generators. F_4 is coded 0, 1, 2, 3 for x₀ + x₁ω,
    ω² = ω + 1, with XOR as addition; the group is enumerated as the matrices g with g ḡᵀ = 1 and det g = 1; the adjoint acts on the
    traceless matrices in the basis e_ij (i ≠ j), diag(1, 1, 0), diag(0, 1, 1). Returns the order and the three lists of dimensions."""
    import numpy as np
    MUL = np.zeros((4, 4), dtype=np.uint8)
    for a in range(4):
        for b in range(4):
            a0, a1, b0, b1 = a & 1, a >> 1, b & 1, b >> 1
            MUL[a, b] = ((a0 & b0) ^ (a1 & b1)) | (((a0 & b1) ^ (a1 & b0) ^ (a1 & b1)) << 1)
    INV = np.array([0, 1, 3, 2], dtype=np.uint8); SQ = INV                                  # x⁻¹ = x² = x̄ on the nonzero elements

    def matmul(A, B):
        A0, A1, B0, B1 = (A & 1).astype(np.int64), (A >> 1).astype(np.int64), (B & 1).astype(np.int64), (B >> 1).astype(np.int64)
        return (((A0 @ B0 + A1 @ B1) % 2) | (((A0 @ B1 + A1 @ B0 + A1 @ B1) % 2) << 1)).astype(np.uint8)

    def nullspace(A):
        A = A.copy(); m, n = A.shape; piv = []; r = 0
        for col in range(n):
            if r == m: break
            nz = np.nonzero(A[r:, col])[0]
            if nz.size == 0: continue
            k = r + nz[0]
            if k != r: A[[r, k]] = A[[k, r]]
            A[r] = MUL[INV[A[r, col]], A[r]]
            f = A[:, col].copy(); f[r] = 0; idx = np.nonzero(f)[0]
            if idx.size: A[idx] ^= MUL[f[idx][:, None], A[r][None, :]]
            piv.append(col); r += 1
        free = [col for col in range(n) if col not in set(piv)]
        N = np.zeros((len(free), n), dtype=np.uint8)
        for i, fc in enumerate(free):
            N[i, fc] = 1; N[i, piv] = A[:r, fc]
        return N

    def det3(g):
        m = lambda x, y: MUL[x, y]
        return (m(g[0][0], m(g[1][1], g[2][2]) ^ m(g[1][2], g[2][1])) ^ m(g[0][1], m(g[1][0], g[2][2]) ^ m(g[1][2], g[2][0]))
                ^ m(g[0][2], m(g[1][0], g[2][1]) ^ m(g[1][1], g[2][0])))
    I3 = np.eye(3, dtype=np.uint8)
    G = []
    for e in product(range(4), repeat=9):
        g = np.array(e, dtype=np.uint8).reshape(3, 3)
        if det3(g) == 1 and np.array_equal(matmul(g, SQ[g].T), I3): G.append(g)
    key = lambda g: bytes(g.flatten())

    def closure(gens):
        S = {key(I3)}; frontier = [I3]
        while frontier:
            new = []
            for x in frontier:
                for g in gens:
                    y = matmul(x, g)
                    if key(y) not in S: S.add(key(y)); new.append(y)
            frontier = new
        return S
    T = [g for g in G if all(g[i, j] == 0 for i in range(3) for j in range(3) if i != j)]
    c = np.array([[0, 0, 1], [1, 0, 0], [0, 1, 0]], dtype=np.uint8)
    P = closure(T + [c]); rest = [g for g in G if key(g) not in P]
    u, v = next((x, y) for x in rest[::7] for y in rest[::5] if len(closure(T + [c, x, y])) == len(G))
    offs = [(i, j) for i in range(3) for j in range(3) if i != j]
    basis = []
    for (i, j) in offs:
        E = np.zeros((3, 3), dtype=np.uint8); E[i, j] = 1; basis.append(E)
    basis += [np.diag(np.array([1, 1, 0], dtype=np.uint8)), np.diag(np.array([0, 1, 1], dtype=np.uint8))]
    coords = lambda Y: np.array([Y[i, j] for (i, j) in offs] + [Y[0, 0], Y[2, 2]], dtype=np.uint8)
    Ad = lambda g: np.stack([coords(matmul(matmul(g, X), SQ[g].T)) for X in basis], axis=1)
    TC = np.array([[MUL[t[i, i], INV[t[j, j]]] for (i, j) in offs] + [1, 1] for t in T], dtype=np.uint8)

    def zero_weight(n):
        Z = []
        for idx in product(range(8), repeat=n):
            for row in TC:
                p = 1
                for k in idx: p = MUL[p, row[k]]
                if p != 1: break
            else: Z.append(idx)
        return np.array(Z, dtype=np.int64)

    def block(A, Z):                                            # the block [Z, Z] of the n-fold Kronecker power of A
        M = np.ones((len(Z), len(Z)), dtype=np.uint8)
        for k in range(Z.shape[1]): M = MUL[M, A[Z[:, k]][:, Z[:, k]]]
        return M
    out = {"order": len(G), "normal": len(P), "torus_fixed": [], "normal_fixed": [], "fixed": []}
    for n in range(1, nmax + 1):
        Z = zero_weight(n); Iz = np.eye(len(Z), dtype=np.uint8)
        B = nullspace(block(Ad(c), Z) ^ Iz)
        N = nullspace(np.vstack([matmul(block(Ad(g), Z) ^ Iz, B.T) for g in (u, v)])) if len(B) else B
        V = matmul(N, B) if len(B) else B
        assert all(not matmul(block(Ad(g), Z) ^ Iz, V.T).any() for g in (c, u, v)) if len(V) else True
        out["torus_fixed"].append(len(Z)); out["normal_fixed"].append(len(B)); out["fixed"].append(len(N))
    return out


def product_channels():
    """46:C22 — the product channels. Where 3 is invertible, 3 ⊗ 3̄ = 1 ⊕ 8, so M(n, n) = Σ_k C(n, k) A_k and
    A_n = Σ_k (−1)^{n−k} C(n, k) M(k, k), with M(k, k) the fixed dimension of (3 ⊗ 3̄)^{⊗k} and A_n that of 8^{⊗n}. On a Subject the
    M(k, k) are the compact counts 1, 1, 2, 6, 23 (46:C15, the degrees at most 8 ≤ 2p − 1), so A = 0, 1, 2, 8: two mesons and three
    gluons have d = 2, a meson and a glueball d = 3, two glueballs d = 8; a fixed subspace of dimension d has (q^{2d} − 1)/(q² − 1)
    invariant lines. On the instance the direct count (instance_adjoint_fixed) gives A = 0, 1, 7, 57, hence M = 1, 1, 2, 11, 92."""
    inv = lambda M: [sum((-1) ** (n - k) * comb(n, k) * M[k] for k in range(n + 1)) for n in range(len(M))]
    comp = [I.su3_moment(k, k) for k in range(5)]; A = inv(comp)
    inst = instance_adjoint_fixed(4); Ai = [1] + inst["fixed"]
    Mi = [sum(comb(n, k) * Ai[k] for k in range(n + 1)) for n in range(5)]
    lines = lambda q, d: (q ** (2 * d) - 1) // (q * q - 1)
    channels = {"two mesons": (comp[2], Mi[2]), "three gluons": (A[3], Ai[3]),
                "a meson and a glueball": (A[2] + A[3], Ai[2] + Ai[3]), "two glueballs": (A[4], Ai[4])}
    checks = {"compact_counts": comp == [1, 1, 2, 6, 23], "subject_dimensions": A == [1, 0, 1, 2, 8],
              "window": all(8 <= 2 * p - 1 for p in (13, 173, 1549)),
              "instance_group": (inst["order"], inst["normal"]) == (216, 27),
              "instance_steps": (inst["torus_fixed"], inst["normal_fixed"], inst["fixed"]) == ([2, 22, 170, 1366], [0, 8, 56, 456], [0, 1, 7, 57]),
              "instance_counts": Mi == [1, 1, 2, 11, 92],
              "channels": channels == {"two mesons": (2, 2), "three gluons": (2, 7), "a meson and a glueball": (3, 8), "two glueballs": (8, 57)},
              "subject_lines": [lines(p, 2) for p in (13, 173, 1549)] == [170, 29930, 2399402] and lines(13, 3) == 28731 and lines(13, 8) == 3960813149899880,
              "instance_lines": (lines(2, 2), lines(2, 7), lines(2, 8)) == (5, 5461, 21845)}
    return {"compact": comp, "A": A, "instance": inst, "instance_counts": Mi, "channels": channels, "checks": checks, "ok": all(checks.values())}


def table_type7(q, x):
    """The entry of the generic character table (46:A15) on the class of type 7 with the parameter x ∈ Z/(q²−1), x ≢ 0 (mod q−1):
    the eigenvalue exponents (x, −qx, (q−1)x) and the values of χ₁, χ₂, χ₃ of 46:C19 as lists of (coefficient, exponent) of
    ζ_{q²−1} — χ₁ = ζ^{(q−1)x}, χ₂ = ζ^{x} + ζ^{−qx}, χ₃ = 0. A second transcription of the entry: amplitude_coefficients and
    amplitude_coefficients_direct carry the same formulas inside their own sums and do not call this function."""
    n2 = q * q - 1
    assert x % (q - 1) != 0, "a regular parameter of the type"
    return {"eigenvalues": (x % n2, (-q * x) % n2, ((q - 1) * x) % n2),
            "chi1": [(1, ((q - 1) * x) % n2)], "chi2": [(1, x % n2), (1, (-q * x) % n2)], "chi3": []}


def split_torus_characters(q, k):
    """The values of χ₁, χ₂, χ₃ of 46:C19 on the frame elements with the eigenvalues g^k, 1, g^{−k}, g a generator of F_q^×,
    g^{2k} ≠ 1, read from the table's entry of type 7 (table_type7) at the parameter x = (q+1)k, where ζ_{q²−1}^{q+1} = ζ_{q−1}.
    Returns the exponents of ζ_{q−1}: {"chi1": (0,), "chi2": (k, −k) mod q−1 sorted, "chi3": ()} as the table gives them, or None
    when g^{2k} = 1 (no such class)."""
    assert q >= 3
    n2 = q * q - 1
    if (2 * k) % (q - 1) == 0: return None
    t = table_type7(q, (q + 1) * k)
    assert sorted(t["eigenvalues"]) == sorted((((q + 1) * k) % n2, (-(q + 1) * k) % n2, 0)), "the eigenvalues g^k, g^{-k}, 1"
    out = {}
    for name in ("chi1", "chi2", "chi3"):
        assert all(c == 1 and e % (q + 1) == 0 for c, e in t[name]), "the values lie in Z[ζ_{q−1}]"
        out[name] = tuple(sorted((e // (q + 1)) % (q - 1) for c, e in t[name]))
    return out


def ring_step_split(q, j, k):
    """The tally of one plaquette on SU(3, F_q) with the boundary classes s_j, s_k of split_torus_characters (46:C20):
    Z₁ = 1/d₁ + (1/d₂)(ζ^j + ζ^{−j})(ζ^k + ζ^{−k}) in Q(ζ_{q−1}), as an exponent table {e mod (q−1): Fraction}. Each further
    plaquette multiplies the first term by 1/d₁ and the second by 1/d₂ (ring_step); the term of χ₃ vanishes on these classes."""
    e1, e2, _ = ring_step(q)["multipliers"]
    cj, ck = split_torus_characters(q, j), split_torus_characters(q, k)
    assert cj is not None and ck is not None
    assert cj["chi3"] == () and ck["chi3"] == ()
    table = {0: e1}
    for a in cj["chi2"]:
        for b in ck["chi2"]:
            e = (a - b) % (q - 1); table[e] = table.get(e, 0) + e2            # χ₂(s_j) · conj χ₂(s_k)
    return table


def ring_residue(p, j, k, g=2):
    """The tally of the ring in the framed rational arithmetic of a Subject p, modulo p (46:C20, part (iv) of the theorem): the
    degrees are 1, 1, −1 modulo p, so each multiplier a_i/d_i is a framed rational with the residue 1, and so is the coefficient
    after any number of plaquettes (the product of the residues; powers are taken modulo p, and no numeral above the totality's
    count is formed). The reduction ζ ↦ g then gives the same tally for every length of the ring: on the classes s_j, s_k of
    split_torus_characters it is 1 + (g^j + g^{−j})(g^k + g^{−k}) in F_p, the paired weight its square, and 3 with unit boundary
    links. g must generate F_p^×. The value is checked against the exact tally of one plaquette (ring_step_split), reduced with
    ζ ↦ g. Returns a dict."""
    q = p
    assert p >= 5 and all(p % r for r in range(2, isqrt(p) + 1)), "a prime"
    primes = [r for r in range(2, p) if (p - 1) % r == 0 and all(r % s for s in range(2, isqrt(r) + 1))]
    assert all(pow(g, (p - 1) // r, p) != 1 for r in primes), "g generates the units"
    st = ring_step(q); d = st["degrees"]; a = (1, 1, -1)
    res = lambda x: (x.numerator * pow(x.denominator, -1, p)) % p            # the residue of a framed rational
    checks = {"degrees_modulo_p": tuple(x % p for x in d) == (1, 1, p - 1),
              "multipliers_have_residue_one": tuple(res(e) for e in st["multipliers"]) == (1, 1, 1),
              "coefficients_have_residue_one": all((pow(ai, n, p) * pow(di, -n, p)) % p == 1
                                                    for n in (1, 2, 3, p - 1, 10 ** 6) for ai, di in zip(a, d))}
    c = lambda t: (pow(g, t, p) + pow(g, -t, p)) % p
    tally = (1 + c(j) * c(k)) % p
    exact = ring_step_split(q, j, k)                                         # the tally of one plaquette, {exponent of ζ: Fraction}
    checks["one_plaquette_reduces_to_it"] = sum(res(v) * pow(g, e, p) for e, v in exact.items()) % p == tally
    checks["unit_boundary_is_three"] = all(sum(pow(ai, n, p) * pow(di, 2 - n, p) for ai, di in zip(a, d)) % p == 3 for n in (1, 2, 3, p - 1))
    return {"p": p, "g": g, "tally": tally, "paired": tally * tally % p, "unit": 3, "checks": checks, "ok": all(checks.values())}


def table_type4(q, l):
    """The entry of the generic character table (46:A15) on the class of type 4 with the parameter l ∈ Z/(q+1), 3l ≢ 0 (mod q+1):
    the diagonalisable elements with the eigenvalues a, a, a^{−2}, a = ζ_{q+1}^l in F_{q²}. The values of χ₁, χ₂, χ₃ of 46:C19 as
    lists of (coefficient, exponent) of ζ_{q+1} — χ₁ = (1 − q) ζ^l + ζ^{−2l}, χ₂ = (q + 1) ζ^l, χ₃ = 0. A second transcription of the
    entry: amplitude_coefficients carries the same formulas inside its own sums and does not call this function."""
    n1 = q + 1
    assert (3 * l) % n1 != 0, "a parameter of the type"
    return {"eigenvalues": (l % n1, l % n1, (-2 * l) % n1),
            "chi1": [(1 - q, l % n1), (1, (-2 * l) % n1)], "chi2": [(q + 1, l % n1)], "chi3": []}


def uniform_boundary_tally(p, j, k, g=2):
    """The tally of the ring with the same boundary links at every step (46:C23): t and b lie in the classes s_j, s_k of
    split_torus_characters, so after n steps the boundary classes are those of t^n and b^n, with the eigenvalues x, 1, x^{−1} and
    y, 1, y^{−1}, x = g^{jn}, y = g^{kn}. The residues of χ₁, χ₂, χ₃ on such a class are read from the table: the degrees at the
    unit (ring_step), the entry of type 4 at a = −1 for the eigenvalues −1, −1, 1 (table_type4 at the parameter (p+1)/2), and the
    entry of type 7 elsewhere (split_torus_characters). The three multipliers have the residue 1 at every length (ring_residue), so
    the tally's residue is W(n) = Σ_i χ̄_i(t^n) χ̄_i(b^{−n}). Returns W(1), …, W(p−1), the lengths that are not regular and the
    checks: at every regular length W(n) = 1 + g^{(j+k)n} + g^{−(j+k)n} + g^{(j−k)n} + g^{−(j−k)n}; the other lengths are those
    with 2jn ≡ 0 or 2kn ≡ 0 (mod p−1), gcd(2j, p−1) + gcd(2k, p−1) − gcd(2j, 2k, p−1) of them, with the values 1 + c(y), −c(y),
    3, 1, −1 of the proposition, c(m) = m + m^{−1}; W(p−1) = 3; W(1) is the tally of ring_residue. Every power is taken modulo p."""
    q = p; N = p - 1; h = (q + 1) // 2
    assert (2 * j) % N and (2 * k) % N, "the links lie in classes s_j, s_k"
    rr = ring_residue(p, j, k, g); assert rr["ok"]                      # g generates the units; the multipliers have the residue 1
    deg = tuple(d % p for d in ring_step(q)["degrees"])
    t4 = table_type4(q, h)                                               # a = −1 = ζ_{q+1}^{(q+1)/2}
    assert sorted(t4["eigenvalues"]) == [0, h, h], "the eigenvalues −1, −1, 1"

    def at_minus_one(terms):
        assert all(e in (0, h) for c, e in terms)
        return sum(-c if e else c for c, e in terms)
    exact = tuple(at_minus_one(t4[name]) for name in ("chi1", "chi2", "chi3"))
    minus = tuple(v % p for v in exact)

    def chars(e):                                                        # the class of the eigenvalues g^e, 1, g^{−e}
        x = pow(g, e % N, p)
        if x == 1: return deg
        if x == p - 1: return minus
        st = split_torus_characters(q, e % N)
        return tuple(sum(pow(g, m, p) for m in st[name]) % p for name in ("chi1", "chi2", "chi3"))

    c = lambda m: (m + pow(m, -1, p)) % p
    xs = [pow(g, (j * n) % N, p) for n in range(1, N + 1)]; ys = [pow(g, (k * n) % N, p) for n in range(1, N + 1)]
    W = [sum(a * b for a, b in zip(chars(j * n), chars(-k * n))) % p for n in range(1, N + 1)]
    five = lambda n: (1 + sum(pow(g, (e * n) % N, p) for e in (j + k, -(j + k), j - k, k - j))) % p
    regular = [x not in (1, p - 1) and y not in (1, p - 1) for x, y in zip(xs, ys)]
    others = tuple(n for n in range(1, N + 1) if not regular[n - 1])

    def listed(x, y):
        ex, ey = x in (1, p - 1), y in (1, p - 1)
        if ex and ey: return 3 if x == y == 1 else (1 if x == y else p - 1)
        if ex: return (1 + c(y)) % p if x == 1 else (-c(y)) % p
        return (1 + c(x)) % p if y == 1 else (-c(x)) % p
    checks = {"table_at_the_unit_and_at_minus_one": deg == (1, 1, p - 1) and exact == (q, -(q + 1), 0) and minus == (0, p - 1, 0),
              "regular_lengths_are_five_powers": all(W[n - 1] == five(n) for n in range(1, N + 1) if regular[n - 1]),
              "other_lengths": others == tuple(n for n in range(1, N + 1) if (2 * j * n) % N == 0 or (2 * k * n) % N == 0)
                               and len(others) == gcd(2 * j, N) + gcd(2 * k, N) - gcd(gcd(2 * j, 2 * k), N),
              "other_values": all(W[n - 1] == listed(xs[n - 1], ys[n - 1]) for n in others),
              "cycle_is_three": W[N - 1] == 3,
              "first_length_is_the_ring_residue": W[0] == rr["tally"]}
    return {"p": p, "g": g, "j": j, "k": k, "values": tuple(W), "paired": tuple(w * w % p for w in W), "others": others,
            "checks": checks, "ok": all(checks.values())}


def ring_gluing_instance(amp=None, words=None):
    """The gluing identity of the ring on the instance SU(3, F_2), n = 2, in Q(ζ₃), with no character table: for boundary links
    (t₁, t₂, b₁, b₂) the mean over the two rungs of w(t₁ r₂ b₁⁻¹ r₁⁻¹) w(t₂ r₁ b₂⁻¹ r₂⁻¹) equals the mean over g of
    (w⋆w)(h₁ g h₂⁻¹ g⁻¹) with h₁ = t₁t₂, h₂ = b₁b₂ and (w⋆w)(u) = ⟨w(v) w(v⁻¹u)⟩_v; two words with the same boundary products give
    the same tally, and the unit boundary gives tr K² = 8 (46:C18). The two sides are compared as sums over the 216² pairs, in
    integers, and reported as means, the sums divided by 216² ("mean", pairs of Fractions a + b ζ₃). The six default words use the
    involutions U, V of 46:C17 and a central element z. Returns {"values": [...], "ok": bool}."""
    if amp is None: amp = spectral_amplitude_instance()
    F, G, W, inv = amp["F"], amp["G"], amp["W"], amp["inv"]
    n = len(G); idx = {g: i for i, g in enumerate(G)}
    mul = [[idx[_mat_mul(F, x, y)] for y in G] for x in G]
    iv = [idx[inv[g]] for g in G]
    w = [W[g] for g in G]
    def add(x, y): return (x[0] + y[0], x[1] + y[1])
    conv = []                                        # (w∗w)(u) = Σ_v w(v) w(v⁻¹u)
    for u in range(n):
        s = (0, 0)
        for v in range(n): s = add(s, z3_mul(w[v], w[mul[iv[v]][u]]))
        conv.append(s)
    e = idx[_mat_id(F)]
    U, V = idx[amp["involutions"][0]], idx[amp["involutions"][1]]
    UV = mul[U][V]
    z = next(g for g in range(n) if g != e and all(mul[g][h] == mul[h][g] for h in range(n)))     # a central element of order 3
    if words is None:
        words = [(e, e, e, e), (z, e, e, e), (U, mul[U][z], e, e), (U, e, V, UV), (U, e, U, e), (z, U, V, e)]
    values = []
    for t1, t2, b1, b2 in words:
        brute = (0, 0)
        for r1 in range(n):
            a1 = mul[iv[b1]][iv[r1]]                                     # b₁⁻¹ r₁⁻¹
            c2 = mul[t2][r1]                                             # t₂ r₁
            for r2 in range(n):
                u1 = mul[mul[t1][r2]][a1]                                # t₁ r₂ b₁⁻¹ r₁⁻¹
                u2 = mul[mul[c2][iv[b2]]][iv[r2]]                        # t₂ r₁ b₂⁻¹ r₂⁻¹
                brute = add(brute, z3_mul(w[u1], w[u2]))
        h1, h2i = mul[t1][t2], iv[mul[b1][b2]]
        glued = (0, 0)
        for g in range(n): glued = add(glued, conv[mul[mul[mul[h1][g]][h2i]][iv[g]]])
        values.append({"h1": h1, "h2": mul[b1][b2], "brute": brute, "glued": glued, "mean": (Q(brute[0], n * n), Q(brute[1], n * n))})
    ok = all(v["brute"] == v["glued"] for v in values)
    ok &= values[0]["mean"] == (8, 0)                                   # the unit boundary: tr K² = 8
    ok &= values[1]["brute"] == values[2]["brute"] and values[1]["h1"] == values[2]["h1"] == z     # two words with the boundary products (z, 1)
    ok &= sum(1 for v in values if v["brute"] != (0, 0)) >= 5
    return {"values": values, "ok": ok}
