"""frc.interactions — one generation and the Koide form (the interactions theme; ledger migration, task LM29, 6 October
2026).

The python side of `lean/FrcCore/Theme/Interactions.lean`: the reflection algebra of four directions on subsets
(bitmasks), the fifth direction, the spinor 16 read 3 + 2 with its hypercharges and charges, and the Koide form of an
amplitude vector on the cube-root orbit. Exact integers and fractions only, the standard library only (gate G09). The
first ledger to use it is the master's block file frc/ledgers/master/interactions.py.

    bit(S, i), cnt(S, lo, hi)     direction i in S; the directions lo ≤ i < hi in S
    emul(S, T)                     e_S e_T = (sign, S ∪ T) for disjoint S, T, else (0, 0)
    fifth(S)                       e_S (|S| even) or e_S e_4 (|S| odd)
    gen16()                        the even subsets of five directions
    col(S), wk(S), y6(S), q6(S)    colour and weak indices, 6Y = −2|S∩C| + 3|S∩W|, 6Q = 6T₃ + 6Y
    koide_q(a)                     Q = Σ a² / (Σ a)², a Fraction
    koide_rho2(a, p, w)            ρ² = â₁â₂/â₀² in 𝔽_p with ω = w, ω² + ω + 1 = 0

Since task LM35 (7 October 2026) the theme also holds the exact algebra of 27-fields' ledger file
frc/ledgers/p27_fields.py: polynomials and power series over Q, cyclotomic arithmetic, the Z/M gauge field and the
uniqueness of Maxwell's action on the periodic cube, the quadratic extension with its unitary groups, the binary
tetrahedral group and the single-plaquette coefficient c₁. Their index stands at the head of that section below.
"""
from fractions import Fraction
from itertools import permutations, product


def bit(S, i):
    return (S >> i) & 1 == 1


def cnt(S, lo, hi):
    return sum(1 for i in range(lo, hi) if bit(S, i))


def emul(S, T):
    if S & T & 31: return (0, 0)
    inv = sum(1 for s in range(5) for t in range(5) if bit(S, s) and bit(T, t) and t < s)
    return (1 if inv % 2 == 0 else -1, S | T)


def fifth(S):
    return S if cnt(S, 0, 4) % 2 == 0 else S | 16


def gen16():
    return [S for S in range(32) if cnt(S, 0, 5) % 2 == 0]


def col(S): return cnt(S, 0, 3)
def wk(S): return cnt(S, 3, 5)
def y6(S): return -2 * col(S) + 3 * wk(S)
def q6(S): return 3 * ((1 if bit(S, 3) else -1) if wk(S) == 1 else 0) + y6(S)


def koide_q(a):
    return Fraction(sum(x * x for x in a), sum(a) ** 2)


def koide_rho2(a, p, w):
    """(â₀, â₁, â₂, 3Σa², â₀² + 2â₁â₂) in 𝔽_p, â_k = Σ_j a_j ω^{jk}."""
    hat = [sum(a[j] * pow(w, j * k, p) for j in range(3)) % p for k in range(3)]
    return hat, 3 * sum(x * x for x in a) % p, (hat[0] ** 2 + 2 * hat[1] * hat[2]) % p


# ======================================================================================================================
# The exact algebra of the interactions (task LM35, 7 October 2026): the objects 27-fields' ledger computes with, kept
# general. The first ledger to use them is frc/ledgers/p27_fields.py.
#
#   Poly                                  polynomials over Q in named variables, the variable "i" with i² = −1
#   ps_mul, ps_inv, ps_div                power series in one variable to a fixed order, rational coefficients
#   cyclotomic(n), cyclo_zero(c, n)       Φ_n, and whether Σ c_j ζ_n^j = 0 (reduction modulo Φ_n)
#   cos_rational(m, L)                    cos(2πm/L) for L ∈ {1, 2, 3, 4, 6}, where it is rational
#   lattice_sites, plaquette, gauge_transform, gradient, holonomy   the Z/M gauge field on the periodic cube (EM)
#   green_exact(L, x)                     the periodic lattice Green's function, exact for L ∈ {1, 2, 3, 4, 6}
#   maxwell_constraints, maxwell_admissible, symbol_taylor   the range-1 quadratic actions: gauge and cubic constraints,
#                                         the admissible space, the cosine symbol's constant and quadratic parts
#   rank_mod(rows, n, p), nullspace(rows, n)                 exact linear algebra over F_p and over Q
#   Fq2                                   F_{q²} = F_q[t]/(t² − st − n): arithmetic, Frobenius, norm
#   mat_mul, dagger, det, trace, unitary_frames, unit_vectors   matrices over Fq2, and U(n, q), SU(n, q) by frames
#   binary_tetrahedral, qmul, qconj       2T = SU(2, F_3) as the 24 unit quaternions with half-integer coordinates
#   c1_from_traces, c1_series             the single-plaquette coefficient c₁ of a finite group: closed form in x = e^{β/d}
#   su3_moment, bessel_ratio_series       Haar moments of SU(3) by the Weyl constant term, and I_{v+1}/I_v as a series
# ======================================================================================================================


class Poly:
    """A polynomial over Q in the variables `names`. If "i" is among them, i² = −1. Terms: exponent tuple -> Fraction."""
    def __init__(self, names, terms=None):
        self.names = tuple(names)
        self.terms = {}
        for e, c in (terms or {}).items():
            self._acc(self.terms, tuple(e), Fraction(c))

    def _acc(self, d, e, c):
        if "i" in self.names:
            k = self.names.index("i")
            if e[k] >= 2:
                q, r = divmod(e[k], 2)
                e = e[:k] + (r,) + e[k + 1:]
                c = c * (-1) ** q
        d[e] = d.get(e, 0) + c
        if d[e] == 0: del d[e]

    @classmethod
    def var(cls, names, name):
        return cls(names, {tuple(int(n == name) for n in names): 1})

    @classmethod
    def const(cls, names, c):
        return cls(names, {(0,) * len(names): c} if c else {})

    def _lift(self, o):
        return o if isinstance(o, Poly) else Poly.const(self.names, o)

    def __add__(self, o):
        o, d = self._lift(o), dict(self.terms)
        for e, c in o.terms.items(): self._acc(d, e, c)
        return Poly(self.names, d)
    __radd__ = __add__

    def __neg__(self):
        return Poly(self.names, {e: -c for e, c in self.terms.items()})

    def __sub__(self, o): return self + (-self._lift(o))
    def __rsub__(self, o): return self._lift(o) - self

    def __mul__(self, o):
        o, d = self._lift(o), {}
        for e1, c1 in self.terms.items():
            for e2, c2 in o.terms.items():
                self._acc(d, tuple(a + b for a, b in zip(e1, e2)), c1 * c2)
        return Poly(self.names, d)
    __rmul__ = __mul__

    def __pow__(self, k):
        r = Poly.const(self.names, 1)
        for _ in range(k): r = r * self
        return r

    def __eq__(self, o):
        return self.terms == self._lift(o).terms

    def __hash__(self):
        return hash(frozenset(self.terms.items()))

    def is_zero(self): return not self.terms

    def conj(self):
        """Complex conjugation: i -> −i (the other variables real)."""
        if "i" not in self.names: return self
        k = self.names.index("i")
        return Poly(self.names, {e: (-c if e[k] else c) for e, c in self.terms.items()})

    def real(self):
        """The real part: the terms free of i."""
        if "i" not in self.names: return self
        k = self.names.index("i")
        return Poly(self.names, {e: c for e, c in self.terms.items() if not e[k]})

    def __repr__(self):
        if not self.terms: return "0"
        out = []
        for e, c in sorted(self.terms.items(), reverse=True):
            m = "*".join(f"{n}^{k}" if k > 1 else n for n, k in zip(self.names, e) if k)
            out.append(f"{c}" + (f"*{m}" if m else ""))
        return " + ".join(out)


def ps_mul(a, b, n):
    """The product of two power series (coefficient lists) to order n (n coefficients)."""
    return [sum((a[i] * b[k - i] for i in range(k + 1) if i < len(a) and k - i < len(b)), Fraction(0)) for k in range(n)]


def ps_inv(a, n):
    """1/a to order n, for a[0] ≠ 0."""
    out = [Fraction(1) / a[0]]
    for k in range(1, n):
        out.append(-sum((a[i] * out[k - i] for i in range(1, k + 1) if i < len(a)), Fraction(0)) / a[0])
    return out


def ps_div(a, b, n):
    return ps_mul(a, ps_inv(b, n), n)


def _pdivmod(num, den):
    """Integer polynomial division (coefficient lists, low degree first) by a monic divisor."""
    num = list(num); q = [0] * max(1, len(num) - len(den) + 1)
    for k in range(len(num) - len(den), -1, -1):
        c = num[k + len(den) - 1]
        q[k] = c
        for j, d in enumerate(den): num[k + j] -= c * d
    return q, num[:len(den) - 1]


_CYC = {}


def cyclotomic(n):
    """Φ_n as an integer coefficient list, low degree first, by dividing x^n − 1 by Φ_d for the proper divisors d."""
    if n in _CYC: return list(_CYC[n])
    f = [-1] + [0] * (n - 1) + [1]
    for d in range(1, n):
        if n % d == 0:
            f, r = _pdivmod(f, cyclotomic(d))
            assert not any(r)
    while len(f) > 1 and f[-1] == 0: f.pop()
    _CYC[n] = list(f)
    return f


def cyclo_zero(c, n):
    """Whether Σ_j c_j ζ_n^j = 0 in Q(ζ_n), for an integer vector c indexed by j mod n: the remainder modulo Φ_n vanishes."""
    _, r = _pdivmod(list(c) + [0], cyclotomic(n))
    return not any(r)


def char_sum(N, k):
    """The coefficient vector of Σ_{τ<N} ζ_N^{kτ}: the number of τ with kτ ≡ j (mod N), for each j."""
    c = [0] * N
    for t in range(N): c[k * t % N] += 1
    return c


_COS = {1: [1], 2: [1, -1], 3: [1, Fraction(-1, 2), Fraction(-1, 2)], 4: [1, 0, -1, 0],
        6: [1, Fraction(1, 2), Fraction(-1, 2), -1, Fraction(-1, 2), Fraction(1, 2)]}


def cos_rational(m, L):
    """cos(2πm/L) for L ∈ {1, 2, 3, 4, 6}, the periods with a rational cosine (the crystallographic restriction)."""
    return Fraction(_COS[L][m % L])


# ---- the Z/M gauge field on the periodic cube L^3 (electromagnetism) ---------------------------------------------------
def _site(x, L): return (x[0] % L) * L * L + (x[1] % L) * L + (x[2] % L)


def _unit(mu): return tuple(int(k == mu) for k in range(3))


def _shift(x, z): return tuple(a + b for a, b in zip(x, z))


def lattice_sites(L):
    return list(product(range(L), repeat=3))


_NBR = {}


def _neighbours(L):
    """For each site index, the indices of x + e_0, x + e_1, x + e_2 on the periodic L³ (cached)."""
    if L not in _NBR:
        _NBR[L] = [[_site(_shift(x, _unit(m)), L) for m in range(3)] for x in lattice_sites(L)]
    return _NBR[L]


def plaquette(A, i, j, M, L):
    """F_ij(x) = A_i(x) + A_j(x + e_i) − A_i(x + e_j) − A_j(x), over the sites in index order (A: [3][L³] lists of
    integers), reduced mod M, or left as integers when M is None."""
    nb, Ai, Aj = _neighbours(L), A[i], A[j]
    F = [Ai[s] + Aj[nb[s][i]] - Ai[nb[s][j]] - Aj[s] for s in range(L ** 3)]
    return F if M is None else [f % M for f in F]


def gauge_transform(A, lam, M, L):
    """A_i(x) -> A_i(x) + λ(x + e_i) − λ(x), mod M (or over the integers when M is None)."""
    nb = _neighbours(L)
    out = [[A[i][s] + lam[nb[s][i]] - lam[s] for s in range(L ** 3)] for i in range(3)]
    return out if M is None else [[a % M for a in row] for row in out]


def gradient(lam, L):
    """(dλ)_i(x) = λ(x + e_i) − λ(x), over the integers."""
    nb = _neighbours(L)
    return [[lam[nb[s][i]] - lam[s] for s in range(L ** 3)] for i in range(3)]


def holonomy(Ax, Ay, x0, y0, a, b, L, M):
    """The holonomy of the rectangle [x0, x0 + a) × [y0, y0 + b) in a periodic plane, counterclockwise, from the link
    fields Ax, Ay (dicts (x, y) -> value), mod M."""
    X = lambda x, y: Ax[(x % L, y % L)]
    Y = lambda x, y: Ay[(x % L, y % L)]
    h = sum(X(x0 + x, y0) for x in range(a)) + sum(Y(x0 + a, y0 + y) for y in range(b))
    h -= sum(X(x0 + x, y0 + b) for x in range(a)) + sum(Y(x0, y0 + y) for y in range(b))
    return h % M


def green_exact(L, x):
    """The periodic lattice Green's function of −Δ with the zero mode removed, (1/L³) Σ_{k≠0} cos(2πk·x/L)/λ_k,
    λ_k = Σ 2(1 − cos 2πk_i/L): exact for L ∈ {1, 2, 3, 4, 6}."""
    tot = Fraction(0)
    for k in product(range(L), repeat=3):
        if not any(k): continue
        lam = sum(2 * (1 - cos_rational(ki, L)) for ki in k)
        tot += cos_rational(sum(a * b for a, b in zip(k, x)), L) / lam
    return tot / L ** 3


# ---- the range-1 quadratic actions of a U(1) lattice field: uniqueness of Maxwell --------------------------------------
def hypercubic_group():
    """The 48 signed permutation matrices of the cube, as tuples of rows (R[i][j]), in the package's order."""
    out = []
    for pi in permutations(range(3)):
        for eps in product((1, -1), repeat=3):
            R = [[0] * 3 for _ in range(3)]
            for a in range(3): R[pi[a]][a] = eps[pi[a]]
            out.append(tuple(tuple(r) for r in R))
    return out


def action_basis(R=1):
    """The parameters of a translation-invariant range-R quadratic form Q: one per class of (μ, ν, z) under
    (μ, ν, z) ~ (ν, μ, −z). Q_a = (E + Eᵀ)/2 with E = Σ_x E_{(x,μ),(x+z,ν)}."""
    disp = [z for z in product(range(-R, R + 1), repeat=3)]
    seen, out = set(), []
    for mu in range(3):
        for nu in range(3):
            for z in disp:
                if (mu, nu, z) in seen: continue
                seen.add((mu, nu, z)); seen.add((nu, mu, tuple(-c for c in z)))
                out.append((mu, nu, z))
    return out


def _origin_rows(par, L):
    """2Q_a restricted to the three origin rows (0, μ), as {(μ, (column site, ν)): integer}. By translation invariance
    these rows determine Q_a."""
    mu, nu, z = par; row = {}
    def put(m, col, v):
        key = (m, col); row[key] = row.get(key, 0) + v
        if row[key] == 0: del row[key]
    put(mu, (tuple(c % L for c in z), nu), 1)                          # E
    put(nu, (tuple((-c) % L for c in z), mu), 1)                       # Eᵀ
    return row


def _link_image(R, x, mu, L):
    """The signed permutation of links by the point-group element R: link (x, μ) -> (sign, (base, μ'))."""
    col = [R[i][mu] for i in range(3)]
    mup = next(i for i in range(3) if col[i]); sgn = col[mup]
    Rx = tuple(sum(R[i][j] * x[j] for j in range(3)) % L for i in range(3))
    if sgn == 1: return 1, (Rx, mup)
    return -1, (tuple((Rx[i] - (1 if i == mup else 0)) % L for i in range(3)), mup)


def maxwell_constraints(L, R=1):
    """The linear constraints on the coefficients c of Q = Σ c_a Q_a, as integer rows over the parameters
    (2Q_a integral): gauge invariance Q B = 0 (B the lattice gradient) and invariance under the 48 elements of the
    hypercubic group, each on the origin rows (the other rows are their translates). Returns (parameters, rows)."""
    pars = action_basis(R); n = len(pars)
    rows0 = [_origin_rows(p, L) for p in pars]
    eqs = {}
    def add(key, a, v):
        if v: eqs.setdefault(key, {}); eqs[key][a] = eqs[key].get(a, 0) + v
    # gauge: (Q B)[(0, μ), s] = Σ_links Q[(0,μ), (y,ν)] (δ_{s, y+e_ν} − δ_{s, y})
    for a, row in enumerate(rows0):
        for (m, (y, nu)), v in row.items():
            add(("G", m, _site(_shift(y, _unit(nu)), L)), a, v)
            add(("G", m, _site(y, L)), a, -v)
    # cubic: Q'[i, j] = s(t_i) s(t_j) Q[t_i, t_j] with t = σ⁻¹, on the origin rows i = (0, μ)
    for gi, Rm in enumerate(hypercubic_group()):
        img = {}
        for x in lattice_sites(L):
            for mu in range(3):
                img[(x, mu)] = _link_image(Rm, x, mu, L)
        pre = {lk: (s, src) for src, (s, lk) in img.items()}       # i -> (s at t_i, t_i): sigma[t_i] = i
        for a, row in enumerate(rows0):
            out = {}
            for m in range(3):
                si, (tx, tmu) = pre[((0, 0, 0), m)]
                # row t_i of Q_a is the origin row tmu translated by tx
                for (m2, (y, nu)), v in row.items():
                    if m2 != tmu: continue
                    c = (tuple((yy + xx) % L for yy, xx in zip(y, tx)), nu)
                    sc, j = img[c]
                    out[(m, j)] = out.get((m, j), 0) + si * sc * v
            for (m, (y, nu)), v in row.items(): out[(m, (y, nu))] = out.get((m, (y, nu)), 0) - v
            for key, v in out.items(): add(("C", gi) + key, a, v)
    rows = [r for r in eqs.values() if any(r.values())]
    return pars, rows


def rank_mod(rows, n, p):
    """The rank over F_p of the integer rows (dicts column -> value) on n columns."""
    piv = {}
    for r in rows:
        v = {k: x % p for k, x in r.items() if x % p}
        while v:
            c = min(v)
            if c not in piv:
                inv = pow(v[c], p - 2, p)
                piv[c] = {k: x * inv % p for k, x in v.items()}
                break
            f, pr = v[c], piv[c]
            for k, x in pr.items():
                y = (v.get(k, 0) - f * x) % p
                if y: v[k] = y
                else: v.pop(k, None)
    return len(piv)


def nullspace(rows, n):
    """A basis of the rational nullspace of the rows (dicts column -> Fraction) on n columns (reduced echelon form)."""
    piv = {}
    for r in rows:
        v = {k: Fraction(x) for k, x in r.items() if x}
        for c in sorted(piv):
            if c in v:
                f = v[c]
                for k, x in piv[c].items():
                    y = v.get(k, 0) - f * x
                    if y: v[k] = y
                    else: v.pop(k, None)
        if not v: continue
        c = min(v); inv = 1 / v[c]
        v = {k: x * inv for k, x in v.items()}
        for c2 in list(piv):
            if c in piv[c2]:
                f = piv[c2][c]
                w = dict(piv[c2])
                for k, x in v.items():
                    y = w.get(k, 0) - f * x
                    if y: w[k] = y
                    else: w.pop(k, None)
                piv[c2] = w
        piv[c] = v
    free = [c for c in range(n) if c not in piv]
    basis = []
    for fc in free:
        vec = [Fraction(0)] * n; vec[fc] = Fraction(1)
        for c, r in piv.items(): vec[c] = -r.get(fc, 0)
        basis.append(vec)
    return basis


def maxwell_admissible(L, R=1):
    """The admissible quadratic actions on L³ (translation invariant, range R, gauge and hypercubic invariant):
    (number of parameters, rational basis of the admissible coefficient vectors)."""
    pars, rows = maxwell_constraints(L, R)
    return pars, nullspace(rows, len(pars))


def maxwell_form(L):
    """The coefficients of the Maxwell plaquette action Σ_x Σ_{μ<ν} F_μν(x)²/2 in the basis action_basis(1), from its
    origin rows (Q_M[(0,μ), (y,ν)])."""
    pars = action_basis(1); idx = {p: a for a, p in enumerate(pars)}
    Q = {}
    for x in lattice_sites(3):
        x = tuple(c - 1 for c in x)                                   # the plaquettes touching the origin links
        for mu in range(3):
            for nu in range(mu + 1, 3):
                terms = [(1, x, mu), (1, _shift(x, _unit(mu)), nu), (-1, _shift(x, _unit(nu)), mu), (-1, x, nu)]
                for s1, y1, m1 in terms:
                    if y1 != (0, 0, 0): continue
                    for s2, y2, m2 in terms:
                        Q[(m1, y2, m2)] = Q.get((m1, y2, m2), 0) + Fraction(s1 * s2, 2)
    # Q[(μ, z, ν)] is the kernel M_μν(z). Q_a has kernel 1/2 at (μ, z, ν) and at (ν, −z, μ), so 1 when they coincide.
    c = [Fraction(0)] * len(pars)
    for (mu, z, nu), v in Q.items():
        key = (mu, nu, z) if (mu, nu, z) in idx else (nu, mu, tuple(-a for a in z))
        a = idx[key]
        c[a] += v                                                     # both entries of an off-diagonal class
    return c


def kernel_of(c, R=1):
    """The kernel M_μν(z) of Q = Σ c_a Q_a: {(μ, ν, z): Fraction}."""
    K = {}
    for a, (mu, nu, z) in enumerate(action_basis(R)):
        if not c[a]: continue
        K[(mu, nu, z)] = K.get((mu, nu, z), 0) + c[a] / 2
        mz = tuple(-x for x in z)
        K[(nu, mu, mz)] = K.get((nu, mu, mz), 0) + c[a] / 2
    return {k: v for k, v in K.items() if v}


def symbol_taylor(K):
    """The real (cosine) symbol Re S_μν(k) = Σ_z M_μν(z) cos(k·z) to second order: the constant S0[μ][ν] = Σ_z M and
    the quadratic form S2[μ][ν][a][b] = −½ Σ_z M_μν(z) z_a z_b, exact."""
    S0 = [[Fraction(0)] * 3 for _ in range(3)]
    S2 = [[[[Fraction(0)] * 3 for _ in range(3)] for _ in range(3)] for _ in range(3)]
    for (mu, nu, z), v in K.items():
        S0[mu][nu] += v
        for a in range(3):
            for b in range(3): S2[mu][nu][a][b] -= v * z[a] * z[b] / 2
    return S0, S2


def transverse_projector():
    """P_μν(k) = |k|² δ_μν − k_μ k_ν as the quadratic form P[μ][ν][a][b] (symmetric in a, b)."""
    return [[[[Fraction(int(mu == nu) * int(a == b)) - Fraction(int(mu == a) * int(nu == b) + int(mu == b) * int(nu == a), 2)
               for b in range(3)] for a in range(3)] for nu in range(3)] for mu in range(3)]


# ---- the quadratic extension and the unitary groups over it -------------------------------------------------------------
class Fq2:
    """F_{q²} = F_q[t]/(t² − s t − n) for a prime q and an irreducible t² − s t − n: elements (a, b) = a + b t. The
    Frobenius x ↦ x^q sends t to s − t, and the norm x·x^q lies in F_q."""
    def __init__(self, q, s, n):
        if any((x * x - s * x - n) % q == 0 for x in range(q)): raise ValueError(f"Fq2: t² − {s}t − {n} is reducible mod {q}")
        self.q, self.s, self.n = q, s % q, n % q
        self.zero, self.one = (0, 0), (1, 0)
    def add(self, x, y): return ((x[0] + y[0]) % self.q, (x[1] + y[1]) % self.q)
    def sub(self, x, y): return ((x[0] - y[0]) % self.q, (x[1] - y[1]) % self.q)
    def neg(self, x): return ((-x[0]) % self.q, (-x[1]) % self.q)
    def mul(self, x, y):
        q, s, n = self.q, self.s, self.n
        bb = x[1] * y[1]
        return ((x[0] * y[0] + n * bb) % q, (x[0] * y[1] + x[1] * y[0] + s * bb) % q)
    def conj(self, x): return ((x[0] + self.s * x[1]) % self.q, (-x[1]) % self.q)
    def norm(self, x):
        v = self.mul(x, self.conj(x)); assert v[1] == 0
        return v[0]
    def inv(self, x):
        ni = pow(self.norm(x), self.q - 2, self.q); c = self.conj(x)
        return (c[0] * ni % self.q, c[1] * ni % self.q)
    def pow(self, x, k):
        r = self.one
        for _ in range(k): r = self.mul(r, x)
        return r
    def scalar(self, a): return (a % self.q, 0)
    def elements(self): return [(a, b) for a in range(self.q) for b in range(self.q)]


def mat_mul(F, A, B):
    n = len(A)
    out = []
    for i in range(n):
        row = []
        for j in range(n):
            s = F.zero
            for k in range(n): s = F.add(s, F.mul(A[i][k], B[k][j]))
            row.append(s)
        out.append(tuple(row))
    return tuple(out)


def dagger(F, M):
    n = len(M)
    return tuple(tuple(F.conj(M[j][i]) for j in range(n)) for i in range(n))


def det(F, M):
    """The determinant by the Leibniz expansion (n ≤ 4)."""
    n = len(M); tot = F.zero
    for perm in permutations(range(n)):
        inv = sum(1 for a in range(n) for b in range(a + 1, n) if perm[a] > perm[b])
        t = F.one
        for i in range(n): t = F.mul(t, M[i][perm[i]])
        tot = F.add(tot, t) if inv % 2 == 0 else F.sub(tot, t)
    return tot


def trace(F, M):
    s = F.zero
    for i in range(len(M)): s = F.add(s, M[i][i])
    return s


def matvec(F, M, v):
    out = []
    for row in M:
        s = F.zero
        for a, b in zip(row, v): s = F.add(s, F.mul(a, b))
        out.append(s)
    return tuple(out)


def herm(F, u, v):
    """⟨u, v⟩ = Σ conj(u_i) v_i."""
    s = F.zero
    for a, b in zip(u, v): s = F.add(s, F.mul(F.conj(a), b))
    return s


def unitary_frames(F, n, det_one=True):
    """Every n × n matrix over F with orthonormal rows (M M† = I, hence M† M = I), with determinant 1 if asked: the
    unitary group U(n, q) or SU(n, q) by elements, enumerated row by row."""
    vecs = [v for v in product(F.elements(), repeat=n) if herm(F, v, v) == F.one]
    out = []
    def extend(rows):
        if len(rows) == n:
            M = tuple(rows)
            if not det_one or det(F, M) == F.one: out.append(M)
            return
        for v in vecs:
            if all(herm(F, r, v) == F.zero for r in rows): extend(rows + [v])
    extend([])
    return out


def unit_vectors(F, m):
    """The number of v ∈ F^m with ⟨v, v⟩ = 1, by the norms of the coordinates."""
    nrm = {}
    for x in F.elements(): nrm[F.norm(x)] = nrm.get(F.norm(x), 0) + 1
    counts = {0: 1}
    for _ in range(m):
        new = {}
        for s, c in counts.items():
            for t, d in nrm.items():
                k = (s + t) % F.q; new[k] = new.get(k, 0) + c * d
        counts = new
    return counts.get(1, 0)


# ---- the binary tetrahedral group 2T = SU(2, F_3) inside SU(2, C) --------------------------------------------------------
def binary_tetrahedral():
    """The 24 unit quaternions (a, b, c, d) = a + bi + cj + dk of 2T: ±1, ±i, ±j, ±k and (±1 ± i ± j ± k)/2, in the
    package's order."""
    out = []
    for s in ((1, 0, 0, 0), (0, 1, 0, 0), (0, 0, 1, 0), (0, 0, 0, 1)):
        for sg in (1, -1): out.append(tuple(Fraction(sg * x) for x in s))
    for signs in product((Fraction(1, 2), Fraction(-1, 2)), repeat=4): out.append(signs)
    return out


def qmul(x, y):
    a1, b1, c1, d1 = x; a2, b2, c2, d2 = y
    return (a1 * a2 - b1 * b2 - c1 * c2 - d1 * d2, a1 * b2 + b1 * a2 + c1 * d2 - d1 * c2,
            a1 * c2 - b1 * d2 + c1 * a2 + d1 * b2, a1 * d2 + b1 * c2 - c1 * b2 + d1 * a2)


def qconj(x): return (x[0], -x[1], -x[2], -x[3])


def su2_matrix(x):
    """[[a + bi, c + di], [−c + di, a − bi]] as Gaussian rationals (re, im). The trace is 2a, the determinant |x|²."""
    a, b, c, d = x
    return (((a, b), (c, d)), ((-c, d), (a, -b)))


# ---- the single-plaquette coefficient c₁ of a gauge group --------------------------------------------------------------
def c1_from_traces(traces, d):
    """For a finite group whose characters χ in dimension d take integer values (a multiset {trace: count}), the
    coefficient c₁(β) = ⟨(χ/d) e^{βχ/d}⟩ / ⟨e^{βχ/d}⟩ is N(x)/D(x) in x = e^{β/d}: returns the numerator and the
    denominator as coefficient lists in x (low degree first), both multiplied by x^{max|t|}."""
    m = max(abs(t) for t in traces)
    N = [Fraction(0)] * (2 * m + 1); D = [Fraction(0)] * (2 * m + 1)
    for t, c in traces.items():
        N[t + m] += Fraction(c * t, d); D[t + m] += c
    return N, D


def moment_c1_series(moments, d, n):
    """c₁(β) = (1/d) E[X e^{βX/d}] / E[e^{βX/d}] as a power series in β to order n, from the moments E[X^k], k ≤ n."""
    num = [Fraction(moments[k + 1], d) / Fraction(d) ** k / _fact(k) for k in range(n)]
    den = [Fraction(moments[k]) / Fraction(d) ** k / _fact(k) for k in range(n)]
    return ps_div(num, den, n)


def _fact(k):
    r = 1
    for j in range(2, k + 1): r *= j
    return r


def bessel_series(v, n):
    """I_v(β) = Σ_j (β/2)^{2j+v}/(j!(j+v)!) as a coefficient list to order n."""
    out = [Fraction(0)] * n
    j = 0
    while 2 * j + v < n:
        out[2 * j + v] = Fraction(1, 2 ** (2 * j + v) * _fact(j) * _fact(j + v)); j += 1
    return out


def bessel_ratio_series(v, n):
    """I_{v+1}(β)/I_v(β) to order n: (β · (I_{v+1}/β^{v+1})) / (I_v/β^v)."""
    a = bessel_series(v + 1, n + v + 1)[v + 1:]; b = bessel_series(v, n + v)[v:]
    r = ps_div(a, b, n)
    return [Fraction(0)] + r[:n - 1]


def _lmul(a, b):
    out = {}
    for e1, c1 in a.items():
        for e2, c2 in b.items():
            e = (e1[0] + e2[0], e1[1] + e2[1]); out[e] = out.get(e, 0) + c1 * c2
    return {e: c for e, c in out.items() if c}


def su3_moment(a, b):
    """E[χ^a χ̄^b] over SU(3) with Haar measure, χ the fundamental character: by the Weyl integration formula, one sixth
    of the constant term of χ^a χ̄^b |Δ|² on the maximal torus (z₁, z₂, z₃ = 1/(z₁z₂)); exact integers."""
    z1, z2, z3 = {(1, 0): 1}, {(0, 1): 1}, {(-1, -1): 1}
    w1, w2, w3 = {(-1, 0): 1}, {(0, -1): 1}, {(1, 1): 1}
    def sub(p, q):
        out = dict(p)
        for e, c in q.items(): out[e] = out.get(e, 0) - c
        return {e: c for e, c in out.items() if c}
    def add3(p, q, r):
        out = {}
        for s in (p, q, r):
            for e, c in s.items(): out[e] = out.get(e, 0) + c
        return out
    D = _lmul(_lmul(sub(z1, z2), sub(z1, z3)), sub(z2, z3))
    Db = _lmul(_lmul(sub(w1, w2), sub(w1, w3)), sub(w2, w3))
    f = _lmul(D, Db)
    chi, chib = add3(z1, z2, z3), add3(w1, w2, w3)
    for _ in range(a): f = _lmul(f, chi)
    for _ in range(b): f = _lmul(f, chib)
    ct = f.get((0, 0), 0)
    assert ct % 6 == 0
    return ct // 6
