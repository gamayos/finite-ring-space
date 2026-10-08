"""frc.subject — the Subject: the frame, the signature, the square class, the chirality (the subject theme; ledger
migration, task LM24, 5 October 2026).

The python side of `lean/FrcCore/Theme/Subject.lean`: the frame data of a shell p = 4κ + 1, the Euler identity and the
chirality of the quarter-turn, the spinor fold and the 2-parts, the mass–energy channel, and the torsor map of the boost
torus. Exact integers only, the standard library only (gate G09). The first ledger to use it is the Subject's block file
(frc/ledgers/master/subject.py).

    frame(p)                 (κ, g, π, i): the drive g the Lean proof builds (frc.foundation.drive), π = 2κ, i = −g^κ
    frames(p)                every drive of p, by iteration (the elements of order p − 1)
    euler(g, j, p)           e^{jπ} := (g^j)^{j·2κ} mod p, for the lift j of a residue (C14)
    chirality(g, g2, p)      the exponent u < p − 1 with g^u = g2, by iteration (C14)
    fold_image(p, g)         the residues iʳ (g⁴)ˢ, r < 4, s < κ, with multiplicity (C16)
    fold_solutions(kappa)    the pairs r < 4, s < κ with 3κr + 4s ≡ 1 (mod 4κ), by search (C16)
    two_parts(p, Om)         (a, b, m, cover, carrier): v₂(p−1), v₂(Ω−1), m = min(a, b), 2^{b−m}, 2^b (C16)
    channel(p, h)            the nonzero x with x^{p+1} = 1, and with x^{2(p+1)} = 1, by search (C20)
    projective_line(p)       the p + 1 points of P¹(F_p): (x, 1) for x < p, then (1, 0)
    direction(P, nu, p)      u_P = ν y + x w, the boost carrying the origin [0:1] to P = [x:y] (C25)
    torsor(P, nu, p)         u_P / ū_P = u_P² / N(u_P), the torsor map P¹ → C_{p+1} (C25)
    boost_act(v, P, nu, p)   the boost v = a + b w on P = [x:y]: [a x + ν b y : b x + a y], normalised (C25)
"""
from frc import arith
from frc.extension import Ext
from frc.foundation import drive, element_order


def frame(p):
    """(κ, g, π, i) on the prime p = 4κ + 1: g the generator-free drive of Drive.lean (`exists_drive`), π = 2κ the
    half-period, i = −g^κ the quarter-turn (C1)."""
    if not (arith.is_prime(p) and p % 4 == 1): raise ValueError(f"frame: {p} is not a prime 4κ + 1")
    k = (p - 1) // 4
    g = drive(p)
    return k, g, 2 * k, (-pow(g, k, p)) % p


def frames(p):
    """Every drive of the prime p: the residues of order p − 1, found by iteration (no factorisation)."""
    return [x for x in range(1, p) if element_order(x, p) == p - 1]


def euler(g, j, p):
    """e^{jπ} := (g^j)^{j·2κ} mod p on p = 4κ + 1, for a lift j ≥ 0 (C14: it is (−1)^j on every frame)."""
    k = (p - 1) // 4
    return pow(pow(g, j, p), j * 2 * k, p)


def chirality(g, g2, p):
    """The exponent u < p − 1 with g^u ≡ g2 (mod p), by iteration; None when g2 is not a power of g."""
    y = 1
    for u in range(p - 1):
        if y == g2 % p: return u
        y = y * g % p
    return None


def fold_image(p, g):
    """The residues iʳ (g⁴)ˢ for r < 4 and s < κ, i = −g^κ, as a list with multiplicity (C16's fold)."""
    k = (p - 1) // 4
    i = (-pow(g, k, p)) % p
    g4 = pow(g, 4, p)
    return [pow(i, r, p) * pow(g4, s, p) % p for r in range(4) for s in range(k)]


def fold_solutions(kappa):
    """Every pair (r, s), r < 4, s < κ, with 3κr + 4s ≡ 1 (mod 4κ), by search (C16)."""
    return [(r, s) for r in range(4) for s in range(kappa) if (3 * kappa * r + 4 * s) % (4 * kappa) == 1]


def two_parts(p, Om):
    """(a, b, m, cover, carrier) for the Subject p and the Carrier Ω: a = v₂(p − 1), b = v₂(Ω − 1), m = min(a, b) the
    shared 2-part's exponent, cover = 2^{b−m} the degree of the shell's cover, carrier = 2^b the Carrier's 2-part."""
    a, b = arith.valuation(p - 1, 2), arith.valuation(Om - 1, 2)
    m = min(a, b)
    return a, b, m, 2 ** (b - m), 2 ** b


def channel(p, h):
    """(sign, q4): the nonzero residues x with x^{p+1} = 1, and those with x^{2(p+1)} = 1, by search (C20: the sign
    ±1 and Q₄ = {±1, ±h} for h² = −1)."""
    sign = [x for x in range(1, p) if pow(x, p + 1, p) == 1]
    q4 = [x for x in range(1, p) if pow(x, 2 * (p + 1), p) == 1]
    return sign, q4


def projective_line(p):
    """The p + 1 points of P¹(F_p) in normal form: (x, 1) for x in [0, p), the origin (0, 1) first, then the horizon
    (1, 0)."""
    return [(x, 1) for x in range(p)] + [(1, 0)]


def _normal(x, y, p):
    x, y = x % p, y % p
    if y: return (x * pow(y, -1, p) % p, 1)
    if x: return (1, 0)
    raise ValueError("projective point (0, 0)")


def direction(P, nu, p):
    """u_P = ν y + x w for P = [x:y] (Subject.lean's `dir ν x y = ⟨ν y, x⟩`): the boost a + b w with
    (a·0 + ν b)/(b·0 + a) = x/y, carrying the origin [0:1] to P."""
    x, y = P
    return (nu * y % p, x % p)


def torsor(P, nu, p):
    """The torsor map P ↦ u_P / ū_P = u_P² / N(u_P) into the norm-one torus C_{p+1} (Subject.lean's `ratio`)."""
    K = Ext(p, nu)
    u = direction(P, nu, p)
    return K.mul(K.scalar(pow(K.norm(u), -1, p)), K.mul(u, u))


def boost_act(v, P, nu, p):
    """The boost v = a + b w on P = [x:y]: [a x + ν b y : b x + a y] in normal form (Subject.lean's action
    `v · dir ν x y = dir ν (a x + ν b y) (a y + b x)`)."""
    a, b = v
    x, y = P
    return _normal(a * x + nu * b * y, b * x + a * y, p)
