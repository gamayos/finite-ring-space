"""frc.flavour — the flavour theme (programme tier, rank 27; 28-flavour's migration, 17 October 2026).

The exact content of *Fermion Flavour Sector over Finite Relational Substrate* (28-flavour), above the interactions
theme's Koide form (frc/interactions.py: koide_q, koide_rho2, the sixteen) and the extension theme's F_{p²}
(frc/extension.py: Ext). Everything here is integer, finite-field, rational or cyclotomic arithmetic; the readings of
measured data live in the chart theme (frc/chart_flavour.py). The Lean side is lean/FrcCore/Theme/Flavour.lean, whose
theorems these functions mirror: the circulant and its spectrum, the quarter-turn boundary and the leading-order
spectrum, the amplitudes N(1 − i) = 2 and N(1 − ω) = 3, the role-depth texture, the Gatto–Sartori–Tonin relation and
the Cabibbo modulus, the transpose identity of the lopsided split, the protected column, the trimaximal magic matrix
and its Jarlskog invariant, the trace relations of a unit, and the seesaw of circulants.

Two arenas. QOmega: the cyclotomic field Q(ω), elements x + yω with ω² = −1 − ω, exact Fractions (the paper's
"one rung up"). F_{p²} through Ext(p, −3) on the shells p ≡ 5 (mod 12), where −3 is a nonresidue, the cube root
ω = −h + h√−3 with h = 1/2, and the quarter-turn i = √−1 in F_p (the paper's native arena, exact_core sections E, F).
"""
from fractions import Fraction as Q
from itertools import product

from frc.arith import is_prime, sqrt_mod
from frc.extension import Ext
from frc.interactions import gen16, col, wk, y6, fifth

SHELLS_5MOD12 = (17, 29, 41, 53, 89, 101, 113, 137, 149, 173)


# ---- Q(ω): x + yω with ω² + ω + 1 = 0 ---------------------------------------------------------------------------------
class QOmega:
    """An element x + yω of Q(ω), ω a primitive cube root of unity; exact Fractions."""
    __slots__ = ("x", "y")

    def __init__(self, x, y=0):
        self.x, self.y = Q(x), Q(y)

    @staticmethod
    def lift(o):
        return o if isinstance(o, QOmega) else QOmega(o)

    def __add__(self, o): o = QOmega.lift(o); return QOmega(self.x + o.x, self.y + o.y)
    def __radd__(self, o): return self + o
    def __neg__(self): return QOmega(-self.x, -self.y)
    def __sub__(self, o): return self + (-QOmega.lift(o))
    def __rsub__(self, o): return QOmega.lift(o) - self
    def __mul__(self, o):
        o = QOmega.lift(o)                                     # (x + yω)(u + vω) = xu − yv + (xv + yu − yv)ω
        return QOmega(self.x * o.x - self.y * o.y, self.x * o.y + self.y * o.x - self.y * o.y)
    def __rmul__(self, o): return self * o
    def __pow__(self, n):
        r = QOmega(1)
        for _ in range(n): r = r * self
        return r
    def __eq__(self, o): o = QOmega.lift(o); return self.x == o.x and self.y == o.y
    def __hash__(self): return hash((self.x, self.y))
    def __repr__(self): return f"({self.x} + {self.y}ω)"
    def conj(self): return QOmega(self.x - self.y, -self.y)      # ω̄ = ω² = −1 − ω
    def norm(self): return self.x * self.x - self.x * self.y + self.y * self.y
    def re2(self): return 2 * self.x - self.y                    # 2 Re z = z + z̄
    def im2sq(self): return 3 * self.y * self.y                  # (2 Im z)² = (z − z̄)(z̄ − z) = 3y²


OMEGA = QOmega(0, 1)


# ---- the circulant ----------------------------------------------------------------------------------------------------
def circ(a, b, c):
    """The 3×3 circulant with rows (a b c), (c a b), (b c a): a·1 + bP + cP² for the cyclic shift P."""
    return [[a, b, c], [c, a, b], [b, c, a]]


def is_circ(M):
    return M[1] == [M[0][2], M[0][0], M[0][1]] and M[2] == [M[0][1], M[0][2], M[0][0]]


def mmul(A, B):
    return [[sum(A[i][k] * B[k][j] for k in range(3)) for j in range(3)] for i in range(3)]


def transpose(A):
    return [[A[j][i] for j in range(3)] for i in range(3)]


def det3(A):
    return (A[0][0] * (A[1][1] * A[2][2] - A[1][2] * A[2][1]) - A[0][1] * (A[1][0] * A[2][2] - A[1][2] * A[2][0])
            + A[0][2] * (A[1][0] * A[2][1] - A[1][1] * A[2][0]))


def adj3(A):
    """The adjugate (the transpose of the cofactors): A · adj A = det A · 1."""
    a = A
    return [[a[1][1] * a[2][2] - a[1][2] * a[2][1], a[0][2] * a[2][1] - a[0][1] * a[2][2], a[0][1] * a[1][2] - a[0][2] * a[1][1]],
            [a[1][2] * a[2][0] - a[1][0] * a[2][2], a[0][0] * a[2][2] - a[0][2] * a[2][0], a[0][2] * a[1][0] - a[0][0] * a[1][2]],
            [a[1][0] * a[2][1] - a[1][1] * a[2][0], a[0][1] * a[2][0] - a[0][0] * a[2][1], a[0][0] * a[1][1] - a[0][1] * a[1][0]]]


def smul(c, A):
    return [[c * x for x in row] for row in A]


def mulvec(A, v):
    return [sum(A[i][k] * v[k] for k in range(3)) for i in range(3)]


def eigenvalues(a, b, c, w=OMEGA):
    """λ_k = a + b ω^k + c ω^{2k}, k = 0, 1, 2, for the circulant (a, b, c) on a cube root ω."""
    return [a + b * w ** k + c * w ** (2 * k) for k in range(3)]


def eigen_identities(a, b, c, w=OMEGA):
    """circ_eigen: M (1, ω^k, ω^{2k}) = λ_k (1, ω^k, ω^{2k}) for k = 0, 1, 2; eigen_sum: Σλ = 3a; eigen_sumsq: Σλ² = 3a² + 6bc;
    circ_det: det = a³ + b³ + c³ − 3abc = λ₀λ₁λ₂. Returns True when all hold."""
    M = circ(a, b, c); lam = eigenvalues(a, b, c, w)
    ok = True
    for k in range(3):
        v = [w ** 0, w ** k, w ** (2 * k)]
        ok &= mulvec(M, v) == [lam[k] * x for x in v]
    ok &= sum(lam, QOmega(0) if isinstance(a, QOmega) else 0) == 3 * a
    ok &= sum((l * l for l in lam), QOmega(0) if isinstance(a, QOmega) else 0) == 3 * a * a + 6 * b * c
    d = det3(M)
    ok &= d == a * a * a + b * b * b + c * c * c - 3 * a * b * c and d == lam[0] * lam[1] * lam[2]
    return ok


def koide_functional(lams):
    """Q = Σλ²/(Σλ)² (the signed amplitudes enter with their signs), exact."""
    s = sum(lams)
    return Q(sum(l * l for l in lams)) / Q(s * s)


# ---- F_{p²} on a shell p ≡ 5 (mod 12): the native arena ----------------------------------------------------------------
class Shell:
    """The shell F_p with p ≡ 5 (mod 12) and its extension F_{p²} = F_p[w]/(w² + 3): the quarter-turn i ∈ F_p, the half
    h = 1/2, the cube root ω = −h + hw, and √3 = i w."""
    def __init__(self, p):
        if not (is_prime(p) and p % 12 == 5): raise ValueError(f"Shell: {p} is not a prime ≡ 5 (mod 12)")
        self.p = p
        self.K = Ext(p, (-3) % p)
        self.i = sqrt_mod(p - 1, p)
        self.h = (p + 1) // 2
        self.omega = ((-self.h) % p, self.h)
        self.s3 = (0, self.i)                                  # √3 = i w: (iw)² = i² w² = (−1)(−3) = 3

    def sc(self, a): return (a % self.p, 0)
    def inFp(self, z): return z[1] == 0

    def unit_of_norm(self, target, avoid_zero=True):
        """Some b ∈ F_{p²} with N(b) = target (every residue is a norm)."""
        for u in range(self.p):
            for v in range(self.p):
                if (u, v) != (0, 0) and self.K.norm((u, v)) == target % self.p: return (u, v)
        return None

    def koide_point(self, a, two_norm_over_a2):
        """A circulant (a, b, b̄) with N(b)/a² = two_norm_over_a2/2 … precisely N(b) = a²·num/den for the Fraction given;
        returns (λ₀, λ₁, λ₂) in F_p (they are framed rationals) and Q = Σλ²/(Σλ)² in F_p."""
        p, K = self.p, self.K
        f = Q(two_norm_over_a2)
        tgt = a * a * f.numerator * pow(f.denominator, -1, p) % p
        b = self.unit_of_norm(tgt); bb = K.conj(b)
        w = self.omega
        lam = []
        for k in range(3):
            wk = K.pow(w, k); w2k = K.pow(w, 2 * k)
            l = K.add(K.add(self.sc(a), K.mul(b, wk)), K.mul(bb, w2k))
            lam.append(l)
        assert all(self.inFp(l) for l in lam)
        ls = [l[0] for l in lam]
        s = sum(ls) % p
        Qv = sum(x * x for x in ls) * pow(s * s, -1, p) % p
        return ls, Qv, b

    def frac(self, f):
        f = Q(f); return f.numerator * pow(f.denominator, -1, self.p) % self.p


def norms_two_three(p):
    """N(1 − i) = 2 in F_p and N(1 − ω) = 3 in F_{p²}, for p ≡ 5 (mod 12)."""
    S = Shell(p); K = S.K
    n_i = ((1 - S.i) * (1 + S.i)) % p
    one_minus_w = K.sub((1, 0), S.omega)
    return n_i == 2 % p and K.norm(one_minus_w) == 3 % p


def boundary(p, a=1):
    """quarter_turn_boundary and lo_eigen on F_{p²}: with b = −h(1 + i) a ω², c = −h(1 − i) a ω the eigenvalue λ₁ vanishes,
    2bc = a², λ₀ = a h (3 + s), λ₂ = a h (3 − s) with s = i(ω − ω²), s² = 3; and (3 − s)² = (7 − 4s)(3 + s)².
    Returns (ok, (λ₀, λ₁, λ₂))."""
    S = Shell(p); K = S.K; h, i, w = S.h, S.i, S.omega
    one_plus_i, one_minus_i = ((1 + i) % p, 0), ((1 - i) % p, 0)
    b = K.mul(K.mul(K.neg(K.mul((h, 0), one_plus_i)), (a % p, 0)), K.pow(w, 2))
    c = K.mul(K.mul(K.neg(K.mul((h, 0), one_minus_i)), (a % p, 0)), w)
    lam = [K.add(K.add((a % p, 0), K.mul(b, K.pow(w, k))), K.mul(c, K.pow(w, 2 * k))) for k in range(3)]
    s = K.mul((i, 0), K.sub(w, K.pow(w, 2)))
    three = (3 % p, 0)
    ok = lam[1] == (0, 0)
    ok &= K.mul((2, 0), K.mul(b, c)) == ((a * a) % p, 0)
    ok &= lam[0] == K.mul(K.mul((a % p, 0), (h, 0)), K.add(three, s))
    ok &= lam[2] == K.mul(K.mul((a % p, 0), (h, 0)), K.sub(three, s))
    ok &= K.mul(s, s) == three and s == S.s3
    L = K.sub(three, s); R = K.add(three, s)
    ok &= K.mul(L, L) == K.mul(K.sub((7 % p, 0), K.mul((4, 0), s)), K.mul(R, R))
    return ok, lam


# ---- the amplitudes ---------------------------------------------------------------------------------------------------
def koide_of_norm(r2):
    """Q = 1/3 + r²/6 for the squared amplitude r² = N(1 − ζ_n): 2 → 2/3, 3 → 5/6."""
    return Q(1, 3) + Q(r2, 6)


def colour_count():
    """(the d^c states of the sixteen, the e^c states, N_c²): (3, 1, 9)."""
    G = gen16()
    dc = [S for S in G if col(S) == 2 and wk(S) == 2 and y6(S) == 2]
    ec = [S for S in G if col(S) == 0 and wk(S) == 2 and y6(S) == 6]
    return len(dc), len(ec), 3 * 3


# ---- the texture ------------------------------------------------------------------------------------------------------
DEPTHS = (2, 1, 0)                                     # the role depths, the heaviest generation at depth 0


def texture_exponents(depths=DEPTHS):
    """(down/lepton exponents 2n, up exponents 4n, the symmetric exponent matrices n_i + n_j for both)."""
    down = tuple(2 * k for k in depths); up = tuple(4 * k for k in depths)
    E_d = [[down[i] + down[j] for j in range(3)] for i in range(3)]
    E_u = [[up[i] + up[j] for j in range(3)] for i in range(3)]
    return down, up, E_d, E_u


def gst_relation(c, s, m1, m2):
    """The texture R D Rᵀ with R = (c, −s; s, c), D = diag(m₁, m₂): its (1,1) entry m₁c² + m₂s² and (1,2) entry
    (m₁ − m₂)cs; when the (1,1) entry vanishes, m₂s² = −m₁c² (tan²θ = −m₁/m₂). Exact in Fractions."""
    c, s, m1, m2 = Q(c), Q(s), Q(m1), Q(m2)
    R = [[c, -s], [s, c]]; D = [[m1, 0], [0, m2]]
    RD = [[sum(R[i][k] * D[k][j] for k in range(2)) for j in range(2)] for i in range(2)]
    M = [[sum(RD[i][k] * R[j][k] for k in range(2)) for j in range(2)] for i in range(2)]
    return M, M[0][0] == m1 * c * c + m2 * s * s, M[0][1] == (m1 - m2) * c * s


def cabibbo_modulus(p, sd, cu, cd, su):
    """|s_d c_u − c_d s_u z|² = s_d²c_u² + c_d²s_u² − s_d c_u c_d s_u T(z) on every unit z of F_{p²} (z z̄ = 1), exhaustively."""
    S = Shell(p); K = S.K
    sd, cu, cd, su = (x % p for x in (sd, cu, cd, su))
    A = (sd * cu) % p; B = (cd * su) % p
    ok = True
    for z in K.norm_one():
        lhs = K.mul(K.sub((A, 0), K.mul((B, 0), z)), K.sub((A, 0), K.mul((B, 0), K.conj(z))))
        T = K.add(z, K.conj(z))
        rhs = K.sub(((A * A + B * B) % p, 0), K.mul(((A * B) % p, 0), T))
        ok &= lhs == rhs
    return ok


# ---- the mixing -------------------------------------------------------------------------------------------------------
def shift():
    return circ(0, 1, 0)


def protected_column():
    """P(1,1,1) = (1,1,1); P(2,−1,−1) = (−1,−1,2), no multiple of (2,−1,−1)."""
    P = shift()
    v = mulvec(P, [1, 1, 1]); u = mulvec(P, [2, -1, -1])
    prop = any(u == [l * x for x in (2, -1, -1)] for l in (Q(k, 2) for k in range(-8, 9)))
    return v == [1, 1, 1], u == [-1, -1, 2], not prop


def magic_matrix():
    """F_jk = ω^{jk} (unnormalised by 1/√3): N(F_jk) = 1 for every entry, so |F_jk/√3|² = 1/3; the rephasing invariant
    F₀₀F₁₁F̄₀₁F̄₁₀ = ω, and (2 Im ω)² = 3, so J² = (Im ω)²/81 = (3/4)/81 = 1/108."""
    F = [[OMEGA ** (j * k) for k in range(3)] for j in range(3)]
    tri = all(F[j][k].norm() == 1 for j in range(3) for k in range(3))
    q = F[0][0] * F[1][1] * F[0][1].conj() * F[1][0].conj()
    J2 = Q(q.im2sq(), 4) / 81
    return tri, q == OMEGA, J2


def jarlskog_framed(p):
    """4(−ν h²) = 3 in F_p at ν = −3, h = 1/2: the framed form of 108 J² = 1."""
    S = Shell(p); nu = (-3) % p
    return (4 * (-nu * S.h * S.h)) % p == 3 % p


def trace_relations(p):
    """For every unit z of F_{p²} (z z̄ = 1): T(z²) = T(z)² − 2 and T(z³) = T(z)³ − 3T(z), T the trace z + z̄."""
    S = Shell(p); K = S.K
    ok = True
    for z in K.norm_one():
        T = K.add(z, K.conj(z)); z2 = K.mul(z, z); z3 = K.mul(z2, z)
        ok &= K.add(z2, K.conj(z2)) == K.sub(K.mul(T, T), (2, 0))
        ok &= K.add(z3, K.conj(z3)) == K.sub(K.mul(K.mul(T, T), T), K.mul((3, 0), T))
    return ok


def chebyshev_lock(c_l, c_d, c_u):
    """The lock relations between cube invariants c = cos 3δ: δ_d = δ₀/2 gives c_ℓ = 2c_d² − 1, δ_u = δ₀/3 gives
    c_ℓ = 4c_u³ − 3c_u (exact arithmetic on the values given)."""
    return 2 * c_d * c_d - 1, 4 * c_u ** 3 - 3 * c_u


# ---- the seesaw -------------------------------------------------------------------------------------------------------
def seesaw_closure(mD, MR):
    """(m_D · adj M_R · m_Dᵀ is circulant, products/transposes/adjugates of the two circulants are circulant,
    M · adj M = det M · 1 for both)."""
    prod = mmul(mmul(mD, adj3(MR)), transpose(mD))
    ok = is_circ(prod) and is_circ(mmul(mD, MR)) and is_circ(transpose(mD)) and is_circ(adj3(MR))
    for M in (mD, MR):
        d = det3(M)
        ok &= mmul(M, adj3(M)) == [[d if i == j else 0 * d for j in range(3)] for i in range(3)]
    return ok, prod


def transpose_fixed_point(c, mD):
    """With M_R = c m_D: m_D · adj(c m_D) · m_Dᵀ = c² det(m_D) · m_Dᵀ."""
    lhs = mmul(mmul(mD, adj3(smul(c, mD))), transpose(mD))
    rhs = smul(c * c * det3(mD), transpose(mD))
    return lhs == rhs


def transpose_eigen(a, b, c, w=OMEGA):
    """The transpose circulant (a, c, b) has the eigenvalues λ_{−k}: (λ₀, λ₂, λ₁)."""
    return eigenvalues(a, c, b, w) == [eigenvalues(a, b, c, w)[k] for k in (0, 2, 1)]


def random_circ(rng, lo=-9, hi=9):
    a, b, c = (Q(rng.randint(lo, hi), rng.randint(1, 5)) for _ in range(3))
    return circ(a, b, c)


def random_matrix(rng, lo=-9, hi=9):
    return [[Q(rng.randint(lo, hi), rng.randint(1, 5)) for _ in range(3)] for _ in range(3)]


def lopsided_transpose(L, D, R):
    """(L D Rᵀ)ᵀ = R D Lᵀ for a diagonal D, and (AB)ᵀ = BᵀAᵀ."""
    Dm = [[D[i] if i == j else 0 * D[i] for j in range(3)] for i in range(3)]
    lhs = transpose(mmul(mmul(L, Dm), transpose(R))); rhs = mmul(mmul(R, Dm), transpose(L))
    return lhs == rhs and transpose(mmul(L, R)) == mmul(transpose(R), transpose(L))


# ---- the sixteen (28:C12) ---------------------------------------------------------------------------------------------
def sixteen():
    """(|gen16| = 16, the fifth direction is a bijection onto the even subsets of five, the split 1 + 10 + 5 by
    (colour, weak) content: the singlet, the ten (u^c, Q, e^c), the five (L, d^c))."""
    G = gen16()
    images = sorted(fifth(S) for S in range(16))
    even = sorted(S for S in range(32) if bin(S).count("1") % 2 == 0)
    ten = [S for S in G if (col(S), wk(S)) in ((2, 0), (1, 1), (0, 2))]
    five = [S for S in G if (col(S), wk(S)) in ((3, 1), (2, 2))]
    one = [S for S in G if (col(S), wk(S)) == (0, 0)]
    return len(G) == 16, images == even, (len(one), len(ten), len(five))
