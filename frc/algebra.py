"""frc.algebra — 1-algebra's exact content above the frame and the foundation (the algebra theme, 6 November 2026).

The python side of `lean/FrcCore/Theme/Framed.lean` and `lean/FrcCore/Theme/Quaternion.lean`: the Klein orbits of the
shell, the signed window, framed rationals and their window law, the scale grid, the rounding of a framed turn, the
complex chart, polynomials over the shell, and the framed quaternions with their rotations. Exact integers and
fractions only, the standard library only (gate G09).

    klein_orbits(p)                 the orbits {x, −x, x⁻¹, −x⁻¹} of the Klein four-group on F_p^×
    sqrt_neg_one(p)                 the roots of x² = −1, by search
    quarter_turn(p, g)              i = −g^κ, the oriented quarter-turn of the frame (p, g)
    signed(x, p)                    the signed window reading of a residue, in [−(p−1)/2, (p−1)/2]
    frac(a, b, p)                   the residue a · b⁻¹ of the framed rational a/b
    window_fractions(N, D)          the fractions a/b with |a| ≤ N, 1 ≤ b ≤ D, in lowest terms
    window_law(p, N, D)             True iff the window fractions take pairwise distinct residues
    grid(B, p)                      the scale grid t · B⁻¹, |t| ≤ (p−1)/2, as a map residue → t
    round_turn(N, u, v)             k = ⌊(2Nu + v)/(2v)⌋, the rounding of u/v to the cycle of N steps
    cmul(x, y, p)                   the complex chart's product on pairs, (a, b)(c, d) = (ac − bd, ad + bc)
    p_eval, p_gcd, p_mod            polynomials over F_p as coefficient lists, low degree first
    qmul, qconj, qnrm, cross, dot   quaternions as 4-tuples; the cross and dot products on 3-tuples
    rho(q, p)                       the rotation x ↦ q x q̄ / N(q) as a 3×3 matrix over F_p
    smat, cayley, halfturn          S_v x = v × x; the Cayley step (aI − S_v)⁻¹(aI + S_v); I + 2N(v)⁻¹S_v²
"""
from fractions import Fraction
from math import gcd

from frc import arith


def kappa(p):
    if not (arith.is_prime(p) and p % 4 == 1): raise ValueError(f"kappa: {p} is not a prime 4κ + 1")
    return (p - 1) // 4


def klein_orbits(p):
    """The orbits of ⟨x ↦ −x, x ↦ x⁻¹⟩ on the nonzero residues, in order of their least element."""
    seen, orbits = set(), []
    for x in range(1, p):
        if x in seen: continue
        inv = pow(x, -1, p)
        orb = {x, (-x) % p, inv, (-inv) % p}
        seen |= orb; orbits.append(orb)
    return orbits


def sqrt_neg_one(p):
    return [x for x in range(1, p) if x * x % p == p - 1]


def quarter_turn(p, g):
    return (-pow(g, kappa(p), p)) % p


def signed(x, p):
    x %= p
    return x - p if x > (p - 1) // 2 else x


def frac(a, b, p):
    return a * pow(b, -1, p) % p


def window_fractions(N, D):
    return sorted({Fraction(a, b) for b in range(1, D + 1) for a in range(-N, N + 1)})


def window_law(p, N, D):
    """True iff the window fractions of (N, D) take pairwise distinct residues."""
    seen = {}
    for q in window_fractions(N, D):
        r = frac(q.numerator, q.denominator, p)
        if r in seen: return False
        seen[r] = q
    return True


def grid(B, p):
    """residue → t for the scale grid t · B⁻¹, |t| ≤ (p − 1)/2; None if two t share a residue."""
    out, h, Bi = {}, (p - 1) // 2, pow(B, -1, p)
    for t in range(-h, h + 1):
        r = t * Bi % p
        if r in out: return None
        out[r] = t
    return out


def round_turn(N, u, v):
    return (2 * N * u + v) // (2 * v)


def cmul(x, y, p):
    return ((x[0] * y[0] - x[1] * y[1]) % p, (x[0] * y[1] + x[1] * y[0]) % p)


def p_trim(a):
    while a and a[-1] == 0: a.pop()
    return a


def p_mod(a, b, p):
    a = a[:]; db = len(b) - 1; inv = pow(b[-1], -1, p)
    while len(a) - 1 >= db and a:
        c = (a[-1] * inv) % p; s = len(a) - 1 - db
        for i, bi in enumerate(b): a[s + i] = (a[s + i] - c * bi) % p
        p_trim(a)
    return a


def p_gcd(a, b, p):
    a, b = p_trim(a[:]), p_trim(b[:])
    while b: a, b = b, p_mod(a, b, p)
    if a:
        inv = pow(a[-1], -1, p); a = [(c * inv) % p for c in a]
    return a


def p_eval(a, x, p):
    r = 0
    for c in reversed(a): r = (r * x + c) % p
    return r


def qmul(x, y):
    a1, b1, c1, d1 = x; a2, b2, c2, d2 = y
    return (a1 * a2 - b1 * b2 - c1 * c2 - d1 * d2, a1 * b2 + b1 * a2 + c1 * d2 - d1 * c2,
            a1 * c2 - b1 * d2 + c1 * a2 + d1 * b2, a1 * d2 + b1 * c2 - c1 * b2 + d1 * a2)


def qconj(q):
    return (q[0], -q[1], -q[2], -q[3])


def qnrm(q):
    return sum(c * c for c in q)


def cross(u, w):
    return (u[1] * w[2] - u[2] * w[1], u[2] * w[0] - u[0] * w[2], u[0] * w[1] - u[1] * w[0])


def dot(u, w):
    return sum(x * y for x, y in zip(u, w))


I3 = ((1, 0, 0), (0, 1, 0), (0, 0, 1))


def mm(A, B, p):
    return tuple(tuple(sum(A[i][k] * B[k][j] for k in range(3)) % p for j in range(3)) for i in range(3))


def minv(A, p):
    (a, b, c), (d, e, f), (g, h, i) = A
    det = (a * (e * i - f * h) - b * (d * i - f * g) + c * (d * h - e * g)) % p
    if det == 0: return None
    di = pow(det, -1, p)
    adj = ((e * i - f * h, c * h - b * i, b * f - c * e), (f * g - d * i, a * i - c * g, c * d - a * f), (d * h - e * g, b * g - a * h, a * e - b * d))
    return tuple(tuple((x * di) % p for x in r) for r in adj)


def rho(q, p):
    n = qnrm(q) % p; ni = pow(n, -1, p); cols = []
    for e in ((0, 1, 0, 0), (0, 0, 1, 0), (0, 0, 0, 1)):
        r = qmul(qmul(q, e), qconj(q)); cols.append([(c * ni) % p for c in r[1:]])
    return tuple(tuple(cols[j][i] for j in range(3)) for i in range(3))


def smat(v, p):
    x, y, z = v
    return tuple(tuple(c % p for c in r) for r in ((0, -z, y), (z, 0, -x), (-y, x, 0)))


def cayley(a, v, p):
    S = smat(v, p)
    M = minv(tuple(tuple((a * I3[i][j] - S[i][j]) % p for j in range(3)) for i in range(3)), p)
    return None if M is None else mm(M, tuple(tuple((a * I3[i][j] + S[i][j]) % p for j in range(3)) for i in range(3)), p)


def halfturn(v, p):
    S = smat(v, p); S2 = mm(S, S, p); ni = pow(sum(c * c for c in v) % p, -1, p)
    return tuple(tuple((I3[i][j] + 2 * ni * S2[i][j]) % p for j in range(3)) for i in range(3))


def primitive(v):
    """The primitive integer vector along v, its first nonzero coordinate positive."""
    g = 0
    for c in v: g = gcd(g, abs(c))
    v = tuple(c // g for c in v)
    for c in v:
        if c: return v if c > 0 else tuple(-x for x in v)
