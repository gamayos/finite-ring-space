"""frc.dirac — the Dirac theme: Hermitian spaces, Cayley dynamics, the gamma matrices and the boost over the shell's
quadratic extension (8-dirac's migration, 1 November 2026; the structure tier, exact).

The coefficient field is K = F_p[w]/(w² − ν) of frc.extension (pairs (a, b) = a + b w, ν the drive g, a nonsquare), and
every object below is a finite matrix or a finite map over it: no floats, no random sampling (gate G09).

    Matrices over K (lists of rows of pairs)
        mmul, madd, msub, msc, ident, meq, iszero, kron, minv, mord, nilindex, dagger, mvec; cyc_mul, cyc_pow, cyc_order (K[C_n])
    The frame data
        is_sq(a, p), primitive_roots(p), shells(limit), frame(p, g) -> (κ, i, named residues)
    The square classes and the counts (blocks B, E)
        class_of_form(p, nu), zero_count(p, a_t), power_image(p, eps)
    The torus and the Cayley transform (blocks C, D, E)
        norm_one(K), kord(K, z), boost_pair(p, nu, x, y), boost_group(p, nu), phi(K, lam, alpha), cayley(K, H, alpha)
        kinetic_H(K, n), potential_H(K, p), cycle_laplacian(K, g), drive_matrix(K, g), characters(p, g)
        hermitian_form(K, u, v), translate(K, n, s)
    The Dirac layer (block D)
        gammas(K, i), clifford(K, G, nu), spin_lift(K, G, x, y), spinor_twist(K, G), form_adjoint(K, X, A)
        symmetric_dirac(K, G, p, d), forward_dirac(K, G, p, d), field tools diff_apply, dirac_apply, transport_apply
    Translation-invariant operators as kernels (blocks D, F, X; 5 November 2026, the standard shells 13 and 173 in place of 𝔽₅)
        a kernel is {offset: 4×4 matrix}, (Aψ)(x) = Σ_s A[s] ψ(x + s): kadd, kneg, ksc, kconv, kid, kiszero, keq, kpow, kadjoint,
        knilindex, kseries_inv, sym_dirac_kernel, fwd_dirac_kernel, kg_kernel, kcayley; the quadratic algebra over the scalar
        kernels a + b·D with D² = Q central (sconv, qmul, qpow, qexpand; qeq compares expansions) for the powers of a Dirac Cayley step;
        order_certified(pow_, eq_, one, U, N, primes) decides ord(U) = N from U^N = 1 and U^(N/q) ≠ 1 for the primes q of N
    The latitude identities (block F)
        latitude_data(p, g)

The Lean side is lean/FrcCore/Theme/Dirac.lean (no axioms) and lean/FrcMathlib/Theme/Dirac.lean.
"""
from math import gcd, isqrt, lcm

from frc.extension import Ext

ZERO, ONE = (0, 0), (1, 0)


# ---- matrices over K -------------------------------------------------------------------------------------------------
def mmul(K, A, B):
    n, m = len(A), len(B[0])
    C = [[ZERO] * m for _ in range(n)]
    for i in range(n):
        Ai, Ci = A[i], C[i]
        for t, a in enumerate(Ai):
            if a == ZERO: continue
            Bt = B[t]
            for j in range(m):
                b = Bt[j]
                if b != ZERO: Ci[j] = K.add(Ci[j], K.mul(a, b))
    return C


def madd(K, A, B): return [[K.add(a, b) for a, b in zip(r, s)] for r, s in zip(A, B)]
def msub(K, A, B): return [[K.sub(a, b) for a, b in zip(r, s)] for r, s in zip(A, B)]
def msc(K, c, A): return [[K.mul(c, a) for a in r] for r in A]
def ident(n): return [[ONE if i == j else ZERO for j in range(n)] for i in range(n)]
def meq(A, B): return all(a == b for r, s in zip(A, B) for a, b in zip(r, s))
def iszero(A): return all(a == ZERO for r in A for a in r)
def dagger(K, A): return [[K.conj(A[j][i]) for j in range(len(A))] for i in range(len(A[0]))]
def mvec(K, A, v):
    out = []
    for row in A:
        s = ZERO
        for a, x in zip(row, v):
            if a != ZERO and x != ZERO: s = K.add(s, K.mul(a, x))
        out.append(s)
    return out


def kron(K, A, B):
    n, m = len(A), len(B)
    return [[K.mul(A[i // m][j // m], B[i % m][j % m]) for j in range(n * m)] for i in range(n * m)]


def minv(K, A):
    n = len(A); M = [row[:] + [ONE if i == j else ZERO for j in range(n)] for i, row in enumerate(A)]
    for c in range(n):
        piv = next((r for r in range(c, n) if M[r][c] != ZERO), None)
        if piv is None: raise ZeroDivisionError("minv: singular")
        M[c], M[piv] = M[piv], M[c]
        iv = K.inv(M[c][c]); M[c] = [K.mul(iv, x) for x in M[c]]
        for r in range(n):
            if r != c and M[r][c] != ZERO:
                f = M[r][c]; M[r] = [K.sub(x, K.mul(f, y)) for x, y in zip(M[r], M[c])]
    return [row[n:] for row in M]


def mord(K, U, cap):
    """The order of U, or None past cap."""
    I = ident(len(U)); X, k = U, 1
    while not meq(X, I):
        X = mmul(K, X, U); k += 1
        if k > cap: return None
    return k


def nilindex(K, A, cap):
    """The least k with A^k = 0, or None past cap."""
    X, k = A, 1
    while not iszero(X):
        X = mmul(K, X, A); k += 1
        if k > cap: return None
    return k


# ---- the frame data ----------------------------------------------------------------------------------------------------
def is_sq(a, p):
    a %= p
    return a != 0 and pow(a, (p - 1) // 2, p) == 1


def primitive_roots(p):
    n, fac, m, d = p - 1, set(), p - 1, 2
    while d * d <= m:
        while m % d == 0: fac.add(d); m //= d
        d += 1
    if m > 1: fac.add(m)
    return [g for g in range(2, p) if all(pow(g, n // q, p) != 1 for q in fac)]


def shells(limit):
    """The symmetry-complete shells p = 4κ + 1 below limit."""
    for p in range(5, limit):
        if p % 4 == 1 and all(p % d for d in range(2, isqrt(p) + 1)): yield p


def frame(p, g):
    """κ, the derived quarter-turn i = g^{−κ} and the named residues 2, 2⁻¹, −2, i, e = g^i, π = 2κ of the frame (τ; 0, 1, g)."""
    kap = (p - 1) // 4
    i = pow(pow(g, p - 2, p), kap, p)
    return kap, i, {"2": 2 % p, "2^-1": pow(2, -1, p), "-2": (-2) % p, "i": i, "e": pow(g, i, p), "pi": (2 * kap) % p}


# ---- square classes and counts ----------------------------------------------------------------------------------------
def zero_count(p, a_t):
    """#{(t, x, y, z) : a_t t² + x² + y² + z² = 0} over F_p, by convolution of the square distribution."""
    sq = [0] * p
    for v in range(p): sq[v * v % p] += 1
    conv2 = [0] * p
    for u in range(p):
        for v in range(p): conv2[(u + v) % p] += sq[u] * sq[v]
    conv3 = [0] * p
    for u in range(p):
        for v in range(p): conv3[(u + v) % p] += conv2[u] * sq[v]
    return sum(conv3[(-a_t * t * t) % p] for t in range(p))


def power_image(p, eps):
    """The image of x ↦ x^ε on F_p^× and the sizes of its fibres."""
    img = {}
    for x in range(1, p): img.setdefault(pow(x, eps, p), 0); img[pow(x, eps, p)] += 1
    return img


# ---- the torus and the Cayley transform ----------------------------------------------------------------------------------
def norm_one(K): return K.norm_one()


def kord(K, z):
    x, k = z, 1
    while x != ONE: x = K.mul(x, z); k += 1
    return k


def boost_pair(p, nu, x, y):
    """The boost Λ(x, y) of the pair (x, y), x² − νy² ≠ 0: its entries (A, B) with A = (x² + νy²)/δ, B = −2xy/δ."""
    d = (x * x - nu * y * y) % p
    di = pow(d, -1, p)
    return ((x * x + nu * y * y) * di % p, (-2 * x * y) * di % p)


def boost_group(p, nu):
    """boost (A, B) -> its preimages (x, y) in K^×."""
    pre = {}
    for x in range(p):
        for y in range(p):
            if (x * x - nu * y * y) % p: pre.setdefault(boost_pair(p, nu, x, y), []).append((x, y))
    return pre


def phi(K, lam, alpha=(0, 1)):
    """The scalar Cayley map φ(λ) = (1 + αλ)/(1 − αλ), λ in K (a shell residue as (λ, 0))."""
    return K.mul(K.add(ONE, K.mul(alpha, lam)), K.inv(K.sub(ONE, K.mul(alpha, lam))))


def cayley(K, H, alpha=(0, 1)):
    """The Cayley step U = (I − αH)⁻¹(I + αH); ZeroDivisionError when α is not admissible."""
    n = len(H); I = ident(n); aH = msc(K, alpha, H)
    return mmul(K, minv(K, msub(K, I, aH)), madd(K, I, aH))


def translate(K, n, s):
    """The translation (Tψ)(x) = ψ(x + s) on the cycle of n sites."""
    return [[ONE if (j - i) % n == s % n else ZERO for j in range(n)] for i in range(n)]


def kinetic_H(K, n):
    """H = −Δ = −(T + T⁻¹ − 2I) on the cycle of n sites."""
    return msc(K, K.neg(ONE), msub(K, madd(K, translate(K, n, 1), translate(K, n, -1)), msc(K, K.scalar(2), ident(n))))


def potential_H(K, p):
    """H = M_V with V = id on F_p."""
    return [[K.scalar(x) if x == y else ZERO for y in range(p)] for x in range(p)]


def hermitian_form(K, u, v):
    s = ZERO
    for a, b in zip(u, v): s = K.add(s, K.mul(K.conj(a), b))
    return s


def characters(p, g):
    """The points g^j of the phase cycle and χ_k(g^j) = g^{jk}."""
    n = p - 1
    pts = [pow(g, j, p) for j in range(n)]
    return pts, [[(pow(g, (j * k) % n, p), 0) for j in range(n)] for k in range(n)]


def drive_matrix(K, g):
    """The drive pullback (Dψ)(x) = ψ(g⁻¹x) on the phase cycle, in the basis of the points g^j."""
    p = K.p; n = p - 1
    pts = [pow(g, j, p) for j in range(n)]; gi = pow(g, -1, p)
    return [[ONE if pts[b] == gi * pts[a] % p else ZERO for b in range(n)] for a in range(n)]


def cycle_laplacian(K, g):
    """Δ_Φ = D + D⁻¹ − 2I on the phase cycle."""
    D = drive_matrix(K, g); n = len(D)
    return msub(K, madd(K, D, minv(K, D)), msc(K, K.scalar(2), ident(n)))


def cyc_mul(K, a, b):
    """The product in the group algebra K[C_n]: cyclic convolution of the first rows of two circulants."""
    n = len(a); c = [ZERO] * n
    for i, x in enumerate(a):
        if x == ZERO: continue
        for j, y in enumerate(b):
            if y != ZERO: c[(i + j) % n] = K.add(c[(i + j) % n], K.mul(x, y))
    return c


def cyc_pow(K, a, k):
    r = [ONE] + [ZERO] * (len(a) - 1)
    while k:
        if k & 1: r = cyc_mul(K, r, a)
        a = cyc_mul(K, a, a); k >>= 1
    return r


def cyc_order(K, a, cap):
    """The order of a circulant given by its first row, or None past cap."""
    e = [ONE] + [ZERO] * (len(a) - 1); x, k = a, 1
    while x != e:
        x = cyc_mul(K, x, a); k += 1
        if k > cap: return None
    return k


# ---- the Dirac layer ---------------------------------------------------------------------------------------------------
def gammas(K, i):
    """The gamma matrices for η = diag(−ν, 1, 1, 1): γ⁰ = i w β, γ^k = i ρ(σ_k), with β = [[0, I], [I, 0]], ρ(σ) = [[0, σ], [−σ, 0]]."""
    ii, z, o = K.scalar(i), ZERO, ONE
    s1 = [[z, o], [o, z]]; s2 = [[z, K.neg(ii)], [ii, z]]; s3 = [[o, z], [z, K.neg(o)]]
    I2 = [[o, z], [z, o]]; Z2 = [[z, z], [z, z]]
    blk = lambda A, B, C, D: [A[0] + B[0], A[1] + B[1], C[0] + D[0], C[1] + D[1]]
    beta = blk(Z2, I2, I2, Z2)
    rho = lambda s: blk(Z2, s, [[K.neg(x) for x in r] for r in s], Z2)
    return [msc(K, K.mul(ii, (0, 1)), beta)] + [msc(K, ii, rho(s)) for s in (s1, s2, s3)]


def clifford(K, G, nu):
    """γ^μ γ^ν + γ^ν γ^μ = 2 η_{μν} I₄, all sixteen."""
    eta = [(-nu) % K.p, 1, 1, 1]
    for mu in range(4):
        for nv in range(4):
            lhs = madd(K, mmul(K, G[mu], G[nv]), mmul(K, G[nv], G[mu]))
            rhs = msc(K, K.scalar(2 * eta[mu] if mu == nv else 0), ident(4))
            if not meq(lhs, rhs): return False
    return True


def spin_lift(K, G, x, y):
    """S(x, y) = xI + yγ⁰γ¹, its inverse (x I − y γ⁰γ¹)/δ with δ = x² − νy², and the boost entries A = (x² + νy²)/δ, B = −2xy/δ."""
    p = K.p; nu = K.nu
    M = mmul(K, G[0], G[1]); d = (x * x - nu * y * y) % p
    S = madd(K, msc(K, K.scalar(x), ident(4)), msc(K, K.scalar(y), M))
    Sinv = msc(K, K.scalar(pow(d, -1, p)), msub(K, msc(K, K.scalar(x), ident(4)), msc(K, K.scalar(y), M)))
    A, B = boost_pair(p, nu, x, y)
    return S, Sinv, A, B, d


def spinor_twist(K, G):
    """X = γ⁰γ¹γ³."""
    return mmul(K, mmul(K, G[0], G[1]), G[3])


def form_adjoint(K, X, A, blocks):
    """A^# = X⁻¹ A† X for X acting on the spinor index of a spinor-field matrix indexed (point, spinor) with `blocks` points:
    the entry layout is row = point*4 + spinor."""
    Xi = msc(K, K.inv(mmul(K, X, X)[0][0]), X)
    Ad = dagger(K, A); n = len(A); out = [[ZERO] * n for _ in range(n)]
    for P in range(blocks):
        for Q in range(blocks):
            blk = [[Ad[4 * P + a][4 * Q + b] for b in range(4)] for a in range(4)]
            if iszero(blk): continue
            t = mmul(K, mmul(K, Xi, blk), X)
            for a in range(4):
                for b in range(4): out[4 * P + a][4 * Q + b] = t[a][b]
    return out


def _shift(K, p, d, mu, s):
    """The translation by s in coordinate mu on F_p^d, as a matrix on the p^d points (row-major index Σ c_k p^k)."""
    N = p ** d; M = [[ZERO] * N for _ in range(N)]
    for r in range(N):
        c = [(r // p ** k) % p for k in range(d)]; c[mu] = (c[mu] + s) % p
        M[r][sum(v * p ** k for k, v in enumerate(c))] = ONE
    return M


def symmetric_dirac(K, G, p, d):
    """D^s = Σ_μ ∇^s_μ ⊗ γ^μ on spinor fields over F_p^d, ∇^s_μ = (T_μ − T_μ⁻¹)/2: a 4p^d × 4p^d matrix, row = point*4 + spinor."""
    inv2 = K.scalar(pow(2, -1, p))
    D = None
    for mu in range(d):
        nab = msc(K, inv2, msub(K, _shift(K, p, d, mu, 1), _shift(K, p, d, mu, -1)))
        term = kron(K, nab, G[mu])
        D = term if D is None else madd(K, D, term)
    return D


def forward_dirac(K, G, p, d, m=0):
    """The standard Dirac operator Σ_μ ∇_μ ⊗ γ^μ − m with the forward differences ∇_μ = T_μ − I, on F_p^d."""
    N = p ** d; D = msc(K, K.neg(K.scalar(m)), ident(4 * N))
    for mu in range(d):
        nab = msub(K, _shift(K, p, d, mu, 1), ident(N))
        D = madd(K, D, kron(K, nab, G[mu]))
    return D


def klein_gordon(K, p, d, nu, m=0):
    """The spinorial Klein–Gordon operator Σ_{μν} η_{μν} ∇_μ∇_ν ⊗ I₄ − m² with the forward differences."""
    N = p ** d; eta = [(-nu) % p, 1, 1, 1]
    KG = msc(K, K.neg(K.scalar(m * m)), ident(4 * N))
    for mu in range(d):
        nab = msub(K, _shift(K, p, d, mu, 1), ident(N))
        KG = madd(K, KG, kron(K, msc(K, K.scalar(eta[mu]), mmul(K, nab, nab)), ident(4)))
    return KG


# ---- spinor fields on F_p^4 as sparse dictionaries (the worked covariance sample) ------------------------------------------
def _padd(p, x, y): return tuple((a + b) % p for a, b in zip(x, y))
def _psub(p, x, y): return tuple((a - b) % p for a, b in zip(x, y))


def _canon(field): return {pt: v for pt, v in field.items() if any(x != ZERO for x in v)}


def field_add(K, a, b):
    out = {pt: v[:] for pt, v in a.items()}
    for pt, v in b.items(): out[pt] = [K.add(x, y) for x, y in zip(out.get(pt, [ZERO] * 4), v)]
    return _canon(out)


def diff_apply(K, field, shift):
    """(∇_s ψ)(x) = ψ(x + s) − ψ(x) on a sparse field over F_p^4."""
    p = K.p; pts = set(field) | {_psub(p, pt, shift) for pt in field}
    return _canon({pt: [K.sub(x, y) for x, y in zip(field.get(_padd(p, pt, shift), [ZERO] * 4), field.get(pt, [ZERO] * 4))] for pt in pts})


def dirac_apply(K, field, G, frame_shifts):
    out = {}
    for gamma, s in zip(G, frame_shifts):
        out = field_add(K, out, {pt: mvec(K, gamma, v) for pt, v in diff_apply(K, field, s).items()})
    return _canon(out)


def transport_apply(K, field, lam, S):
    """(Λ_* ψ)(Λx) = S ψ(x) for an integer matrix Λ on F_p^4 and the spin lift S."""
    p = K.p
    return _canon({tuple(sum(c * v for c, v in zip(row, pt)) % p for row in lam): mvec(K, S, val) for pt, val in field.items()})


# ---- translation-invariant operators as kernels (5 November 2026) --------------------------------------------------------
# A kernel is a sparse map {offset: 4×4 matrix over K} on F_p^d: (Aψ)(x) = Σ_s A[s] ψ(x + s). Composition is the convolution
# (A∘B)[t] = Σ_s A[s]·B[t − s]; the identity is {0: I₄}; the X-adjoint is (A^#)[s] = X⁻¹ A[−s]† X. A translation-invariant operator
# on the 4p^d-dimensional spinor space is determined by its kernel, so an identity of kernels is the identity of the operators,
# and the orders and nilpotency indices of the Dirac Cayley steps are decided on kernels where the dense matrices (4·13² = 676
# in 1+1 at p = 13, 4·173 = 692 in 0+1 at p = 173) are out of reach.
def _koff(p, s, t): return tuple((a + b) % p for a, b in zip(s, t))
def _kneg_off(p, s): return tuple((-a) % p for a in s)
def kadd(K, A, B):
    out = {s: [r[:] for r in M] for s, M in A.items()}
    for s, M in B.items(): out[s] = madd(K, out[s], M) if s in out else M
    return {s: M for s, M in out.items() if not iszero(M)}
def kneg(K, A): return {s: msc(K, K.neg(ONE), M) for s, M in A.items()}
def ksc(K, c, A): return {s: msc(K, c, M) for s, M in A.items()} if c != ZERO else {}
def kconv(K, p, A, B):
    out = {}
    for s, M in A.items():
        for t, N in B.items():
            u = _koff(p, s, t); P = mmul(K, M, N)
            out[u] = madd(K, out[u], P) if u in out else P
    return {s: M for s, M in out.items() if not iszero(M)}
def kid(d): return {(0,) * d: ident(4)}
def kiszero(A): return all(iszero(M) for M in A.values())
def keq(K, A, B): return kiszero(kadd(K, A, kneg(K, B)))
def kpow(K, p, A, e, d):
    """A^e by square-and-multiply."""
    R, X = kid(d), A
    while e:
        if e & 1: R = kconv(K, p, R, X)
        e >>= 1
        if e: X = kconv(K, p, X, X)
    return R
def kadjoint(K, p, X, A):
    """A^# = X⁻¹ A† X on kernels, X the spinor twist (X² a scalar)."""
    Xi = msc(K, K.inv(mmul(K, X, X)[0][0]), X)
    return {_kneg_off(p, s): mmul(K, mmul(K, Xi, dagger(K, M)), X) for s, M in A.items()}
def knilindex(K, p, A, cap):
    """The least k with A^k = 0, or None past cap."""
    X, k = A, 1
    while not kiszero(X):
        X = kconv(K, p, X, A); k += 1
        if k > cap: return None
    return k
def kseries_inv(K, p, N, d, idx):
    """(1 − N)⁻¹ = Σ_{k<idx} N^k for a kernel N nilpotent of index idx."""
    R, X = kid(d), kid(d)
    for _ in range(idx - 1):
        X = kconv(K, p, X, N); R = kadd(K, R, X)
    return R
def _unit(d, mu, s):
    v = [0] * d; v[mu] = s; return tuple(v)
def sym_dirac_kernel(K, p, d, G, shifts=None):
    """D^s = Σ_μ ∇^s_μ ⊗ γ^μ with ∇^s_μ = (T_{e_μ} − T_{−e_μ})/2, the frame vectors e_μ the standard ones unless `shifts` names them."""
    inv2 = K.scalar(pow(2, -1, p)); A = {}
    for mu in range(d):
        e = shifts[mu] if shifts else _unit(d, mu, 1)
        A = kadd(K, A, {tuple(x % p for x in e): msc(K, inv2, G[mu])})
        A = kadd(K, A, {_kneg_off(p, e): msc(K, K.neg(inv2), G[mu])})
    return A
def fwd_dirac_kernel(K, p, d, G, m=0):
    """The standard Dirac operator Σ_μ ∇_μ ⊗ γ^μ − m, ∇_μ = T_{e_μ} − 1."""
    A = {(0,) * d: msc(K, K.neg(K.scalar(m)), ident(4))}
    for mu in range(d):
        A = kadd(K, A, {_unit(d, mu, 1): G[mu]}); A = kadd(K, A, {(0,) * d: msc(K, K.neg(ONE), G[mu])})
    return A
def kg_kernel(K, p, d, nu, m=0):
    """The spinorial Klein–Gordon operator Σ_μ η_μμ ∇_μ² ⊗ I₄ − m² with the forward differences."""
    eta = [(-nu) % p, 1, 1, 1]; A = {(0,) * d: msc(K, K.neg(K.scalar(m * m)), ident(4))}
    for mu in range(d):
        nab = kadd(K, {_unit(d, mu, 1): ident(4)}, {(0,) * d: msc(K, K.neg(ONE), ident(4))})
        A = kadd(K, A, ksc(K, K.scalar(eta[mu]), kconv(K, p, nab, nab)))
    return A
def kcayley(K, p, d, H, alpha, nil_part, idx, scalar=ONE):
    """The Cayley step U = (1 − αH)⁻¹(1 + αH) for H = scalar·1 + nil_part with nil_part nilpotent of index idx (the inverse
    through the series of (1 + α·scalar)⁻¹ α nil_part)."""
    c = K.add(ONE, K.mul(alpha, scalar)); ci = K.inv(c)
    inv = ksc(K, ci, kseries_inv(K, p, ksc(K, K.mul(ci, alpha), nil_part), d, idx))
    return kconv(K, p, inv, kadd(K, kid(d), ksc(K, alpha, H)))

# The quadratic algebra over the scalar kernels: an element a + b·D with a, b scalar kernels {offset: K} and D² = Q a central
# scalar kernel (for D = D^s the Clifford relations give Q = Σ_μ η_μμ (∇^s_μ)² ⊗ I₄, which the package checks on the kernel itself).
def sconv(K, p, a, b):
    out = {}
    for s, x in a.items():
        for t, y in b.items():
            u = _koff(p, s, t); z = K.mul(x, y)
            out[u] = K.add(out[u], z) if u in out else z
    return {s: x for s, x in out.items() if x != ZERO}
def sadd(K, a, b):
    out = dict(a)
    for s, x in b.items(): out[s] = K.add(out[s], x) if s in out else x
    return {s: x for s, x in out.items() if x != ZERO}
def ssc(K, c, a): return {s: K.mul(c, x) for s, x in a.items()} if c != ZERO else {}
def qmul(K, p, Q, x, y):
    (a, b), (c, e) = x, y
    return (sadd(K, sconv(K, p, a, c), sconv(K, p, sconv(K, p, b, e), Q)), sadd(K, sconv(K, p, a, e), sconv(K, p, b, c)))
def qid(d): return ({(0,) * d: ONE}, {})
def qeq(K, p, D, x, y):
    """Equality of two elements as operators: the formal pairs are compared after expansion, since a nonzero b gives the zero
    operator b·D when D is nilpotent (the algebra is not faithful on the pairs)."""
    return keq(K, qexpand(K, p, D, x), qexpand(K, p, D, y))
def qpow(K, p, Q, x, e, d):
    R, X = qid(d), x
    while e:
        if e & 1: R = qmul(K, p, Q, R, X)
        e >>= 1
        if e: X = qmul(K, p, Q, X, X)
    return R
def qexpand(K, p, D, x):
    """The 4×4 kernel of a + b·D."""
    a, b = x
    return kadd(K, {s: msc(K, c, ident(4)) for s, c in a.items()}, kconv(K, p, {s: msc(K, c, ident(4)) for s, c in b.items()}, D))
def scalar_kernel(K, A):
    """A kernel that is scalar (every 4×4 block a multiple of I₄) as a scalar kernel, else None."""
    out = {}
    for s, M in A.items():
        c = M[0][0]
        if not meq(M, msc(K, c, ident(4))): return None
        out[s] = c
    return out

def order_certified(pow_, eq_, one, U, N, primes):
    """ord(U) = N exactly: U^N = 1, and U^(N/q) ≠ 1 for every prime q of N (`primes` must multiply to N with its multiplicities)."""
    prod = 1
    for q, e in primes.items(): prod *= q ** e
    if prod != N or not eq_(pow_(U, N), one): return False
    return all(not eq_(pow_(U, N // q), one) for q in primes)


# ---- the latitude identities -------------------------------------------------------------------------------------------
def latitude_data(p, g):
    """κ, π = 2κ, g^κ, 4⁻¹, 2⁻¹ and the unit-circle count of the framed-complex chart."""
    kap = (p - 1) // 4
    return {"kappa": kap, "pi": 2 * kap, "g_kappa": pow(g, kap, p), "inv4": pow(4, -1, p), "inv2": pow(2, -1, p),
            "unit_circle": sum(1 for a in range(p) for b in range(p) if (a * a + b * b) % p == 1) if p < 1000 else None}
