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

The pair (p, Ω) of 38-s13 (12 October 2026; the python side of `lean/FrcCore/Theme/Pair.lean` and of the A-block of
`lean/FrcCore/S13.lean`):

    admissible(p, Om)        the pair's admissibility: p, Ω prime, p = 4κ + 1, Ω = 4S + 1, κ odd, S ≡ 2 (4), S ≡ 1 (3), p² < Ω
    pair(p, Om, g)           (κ, S, i, g⁴, g⁹) on the drive g: i = −g^κ = g^{3κ}, the tower g = g⁴ · i at κ = 3 (38:A1, A2)
    tower_solution(kappa)    the (a, b) with 4a = κb + 1 for odd κ: ((3κ + 1)/4, 3) or ((κ + 1)/4, 1) (38:A2; Pair.tower_solvable)
    carrier_roots(Om, g)     (q, ħ, octant): q = g^S the quarter, q² = −1, ħ = −q = q⁻¹, ζ₈ = g^{S/2} with ζ₈² = q (38:A4)
    two_squares(Om)          the (a, b), a ≥ b, with Ω = a² + b², and the Gaussian leg ratios a/b, b/a on 𝔽_Ω (38:A4)
    fibonacci(n)             F_0 … F_n
    pisano(p)                the period of the Fibonacci recurrence mod p
    window(p)                the resolvable window: the heights k with 4k < p, i.e. k ≤ κ (38:A8, B2; Pair.window)
    pairwise_conservation(p) every pair of window heights sums within one period (38:A8; Pair.window_sum)
    leak_rate(p, Om)         (κ/S, (κ/S)/(p − 1), 1/(Ω − 1), 1/(2(Ω − 1))): the two faces per chronon (38:C10, C7; Pair.leak_rate)
    joint_cycle(p, Om)       (L, L/2, L/2 mod p − 1, L/2 mod Ω − 1): lcm(p − 1, Ω − 1) and the half event (38:C14, B5; Pair.joint_cycle)
    least_return(p, Om)      the least t ≥ 1 with t ≡ 0 mod p − 1 and mod Ω − 1, by search
    apsidal_bound(p, Om)     the root-free bound (p − 1)²Ω < (Ω − p)² and its equivalence with p² < Ω (38:C13; Drift.nesting_bound)
    kill_test(p, kO, Om)     the (p, q) regression in the auxiliary modulus Ω: the residues the paper reads (38:C6)
"""
from fractions import Fraction
from math import gcd, isqrt

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


# ---- the pair (p, Ω) of 38-s13 ----------------------------------------------------------------------------------------
def admissible(p, Om):
    """The pair's admissibility (38-s13, §2): p = 4κ + 1 and Ω = 4S + 1 prime, κ odd, S ≡ 2 (mod 4), S ≡ 1 (mod 3),
    and the nesting p² < Ω. Returns the dict of clauses."""
    k, S = (p - 1) // 4, (Om - 1) // 4
    return {"p_prime": arith.is_prime(p), "Om_prime": arith.is_prime(Om), "p_form": p == 4 * k + 1,
            "Om_form": Om == 4 * S + 1, "kappa_odd": k % 2 == 1, "S_mod4": S % 4 == 2, "S_mod3": S % 3 == 1,
            "nesting": p * p < Om}


def pair(p, Om, g):
    """(κ, S, i, g⁴, g⁹) on the Subject's drive g: the quarter i = −g^κ (= g^{3κ}), the rung g⁴, and g^{3κ}; at
    (13, 233) with g = 2: (3, 58, 5, 3, 5), the tower identity g = g⁴ · i (3 · 5 = 2 on 𝔽₁₃)."""
    k, S = (p - 1) // 4, (Om - 1) // 4
    return k, S, (-pow(g, k, p)) % p, pow(g, 4, p), pow(g, 3 * k, p)


def tower_solution(kappa):
    """The pair (a, b) with 4a = κb + 1 for odd κ, as Pair.tower_solvable builds it: ((3κ + 1)/4, 3) when κ ≡ 1 (mod 4),
    ((κ + 1)/4, 1) when κ ≡ 3 (mod 4): (1, 1) at κ = 3, (4, 3) at κ = 5, (2, 1) at κ = 7."""
    if kappa % 2 == 0: raise ValueError("tower_solution: κ must be odd")
    a, b = ((3 * kappa + 1) // 4, 3) if kappa % 4 == 1 else ((kappa + 1) // 4, 1)
    assert 4 * a == kappa * b + 1
    return a, b


def carrier_roots(Om, g):
    """(q, ħ, ζ₈) on the Carrier Ω = 4S + 1 with the drive g: the quarter q = g^S (q² = −1), ħ = −q = q⁻¹ (ħq = 1,
    ħ + q = Ω), and the octant ζ₈ = g^{S/2} when S is even (ζ₈² = q); at (233, 78): (89, 144, 97)."""
    S = (Om - 1) // 4
    q = pow(g, S, Om)
    hb = (-q) % Om
    assert q * q % Om == Om - 1 and hb * q % Om == 1 and hb + q == Om
    z8 = pow(g, S // 2, Om) if S % 2 == 0 else None
    if z8 is not None: assert z8 * z8 % Om == q
    return q, hb, z8


def two_squares(Om):
    """The decomposition Ω = a² + b² (a ≥ b) of a prime Ω ≡ 1 (mod 4) by search, and the leg ratios (a/b, b/a) on 𝔽_Ω:
    both are square roots of −1 (38:A4: at 233 = 13² + 8², 13/8 = 89 = h and 8/13 = 144 = ħ)."""
    for a in range(isqrt(Om), 0, -1):
        r = Om - a * a
        b = isqrt(r)
        if b * b == r and b <= a:
            ab, ba = a * pow(b, -1, Om) % Om, b * pow(a, -1, Om) % Om
            assert ab * ab % Om == Om - 1 and ba * ba % Om == Om - 1 and (ab + ba) % Om == 0
            return (a, b), (ab, ba)
    raise ValueError(f"two_squares: {Om} is no sum of two squares")


def fibonacci(n):
    """F_0, …, F_n."""
    F = [0, 1]
    while len(F) <= n: F.append(F[-1] + F[-2])
    return F[:n + 1]


def pisano(p):
    """The period of the Fibonacci recurrence modulo p."""
    a, b, n = 0, 1, 0
    while True:
        a, b, n = b, (a + b) % p, n + 1
        if (a, b) == (0, 1): return n


def window(p):
    """The resolvable window on p = 4κ + 1: the heights k ≥ 0 with 4k < p, which are exactly k ≤ κ; returns
    (κ, [0..κ], the symmetric heights of C_{p−1}: −(2κ − 1)..2κ)."""
    k = (p - 1) // 4
    heights = [h for h in range(p) if 4 * h < p]
    assert heights == list(range(k + 1))
    return k, heights, list(range(-(2 * k - 1), 2 * k + 1))


def pairwise_conservation(p):
    """Every pair of window magnitudes k₁, k₂ ≤ κ sums to at most 2κ < 4κ = p − 1: exact integer conservation inside one
    period (38:A8); returns (ok, the maximal sum 2κ, the period p − 1)."""
    k = (p - 1) // 4
    ok = all(a + b <= 2 * k and 2 * k < 4 * k for a in range(k + 1) for b in range(k + 1))
    return ok, 2 * k, p - 1


def leak_rate(p, Om):
    """The leak faces per revolution and per chronon as exact fractions: (κ/S, (κ/S)/(p − 1), 1/(Ω − 1), 1/(2(Ω − 1))),
    with (κ/S)/(p − 1) = 1/(4S) = 1/(Ω − 1), κ-free (38:C10, C7, X1, X3)."""
    k, S = (p - 1) // 4, (Om - 1) // 4
    ang = Fraction(k, S)
    assert ang == Fraction(p - 1, Om - 1)
    per = ang / (p - 1)
    assert per == Fraction(1, 4 * S) == Fraction(1, Om - 1)
    return ang, per, Fraction(1, Om - 1), Fraction(1, 2 * (Om - 1))


def joint_cycle(p, Om):
    """(L, L/2, L/2 mod (p − 1), L/2 mod (Ω − 1)) with L = lcm(p − 1, Ω − 1): the joint cycle closes at (home, home) and,
    for a κ-odd pair with S ≡ 2 (mod 4), the half event reads (home, (Ω − 1)/2): the Carrier at −1 (38:C14, B5)."""
    a, b = p - 1, Om - 1
    L = a * b // gcd(a, b)
    return L, L // 2, (L // 2) % a, (L // 2) % b


def least_return(p, Om):
    """The least t ≥ 1 with t ≡ 0 modulo both p − 1 and Ω − 1, by search: lcm(p − 1, Ω − 1)."""
    a, b = p - 1, Om - 1
    t = a
    while t % b: t += a
    return t


def apsidal_bound(p, Om):
    """The apsidal bound κ/S < 1/(√Ω + 1) in root-free form, (p − 1)²Ω < (Ω − p)², and its equivalence with the nesting
    p² < Ω (38:C13; Drift.nesting_bound); returns (bound holds, p² < Ω)."""
    lhs, rhs = (p - 1) ** 2 * Om, (Om - p) ** 2 if Om >= p else 0
    return lhs < rhs, p * p < Om


def kill_test(p=53, kO=3, Om=157):
    """The (p, q) regression of 38:C6 read in the auxiliary modulus Ω = 4S + 1 (S = 39 at Ω = 157, not admissible):
    v_O = 5^13, 3 ∤ 13, 22⁹ = 28 = 5^{−39}, 22⁴ of order 3, the idempotent 117·13 ≡ 117 (mod 156), 5^39 = 129,
    12/52 = 3/13 = κ_O/κ_S, lcm(12, 52) = 156 with the half event 78. Returns the dict of readings."""
    kS = (p - 1) // 4
    S = (Om - 1) // 4
    vO = pow(5, 13, Om)
    x = pow(vO, 4, Om)
    return {"Om_form": Om == 4 * S + 1, "S": S, "v_O": vO, "three_divides_13": 13 % 3 == 0, "core_quarter": pow(vO, 9, Om),
            "inverse": pow(5, 39, Om) * pow(vO, 9, Om) % Om, "order3": pow(x, 3, Om) == 1 and x != 1,
            "idempotent": (117 * 13) % 156, "subject_face": pow(5, 39, Om),
            "ratio": Fraction(4 * kO, 4 * kS) == Fraction(kO, kS), "lcm": 12 * 52 // gcd(12, 52), "half": 12 * 52 // gcd(12, 52) // 2}
