"""frc.projective — PGL₂ by elements: the boosts, the Borel subgroup and the Hopf section (the projective theme; ledger
migration, task LM25, 5 October 2026).

The python side of `lean/FrcCore/Theme/Projective.lean`: 2 × 2 matrices over F_p as tuples (a, b, c, d), read up to a
nonzero scalar, acting on the projective line [x : y] ↦ [a x + b y : c x + d y]. Exact integers mod p only, the standard
library only (gate G09). The first ledger to use it is the master's block file frc/ledgers/master/projective.py.

    mul(M, N, p), det(M, p), act(M, P, p)     the product, the determinant, the action on a point P = (x, y)
    normal(P, p)                              a point of ℙ¹ in normal form: (x, 1) or (1, 0)
    pclass(M, p)                              a matrix's projective class: M scaled to its first nonzero entry 1
    line(p)                                   the p + 1 points of ℙ¹
    boost(nu, a, b, p), borel(a, b, e, p)     [[α, νβ], [β, α]] and [[a, b], [0, e]]
    pgl2(p)                                   every class of PGL₂(F_p), by search (p(p² − 1) of them)
    factor(M, nu, p)                          (N, (a, b, e), (α, β)) with N M = borel · boost (the Lean proof's formula)

The two fibrations and the frame triple of 38-s13 (12 October 2026; `Projective.lean`'s `frame_triple`, `unit_split`):

    adj(M, p), conj(M, N, p)                  the adjugate [[d, −b], [−c, a]]; the conjugate M N M⁻¹
    triple(M, nu, p)                          (direction, (α, β), (a, b, e)) with N M = boost(α, β) · borel(a, b, e), N = α² − νβ²
    frame_triple(p, nu)                       every class of PGL₂ is one direction × one Borel class, (p + 1)·p·(p − 1) exactly
    sl2(p)                                    the norm-one sphere SL₂(F_p) by elements, p(p² − 1) of them
    involutions(p)                            the involutions of SL₂ (one) and of PGL₂ (p²): the two groups are not isomorphic
    circle(p)                                 the points of x² + y² = 1: p − 1 of them at p = 4κ + 1
    unit(p)                                   i = diag(r, −r) with r² = −1, the unit's matrix on a frame p = 4κ + 1
    centraliser(p)                            the classes commuting with i: the diagonal torus, p − 1 classes, inside the Borel
    split_fibration(p)                        the orbit of i under conjugation = the quadric a² + bc = −1, p(p + 1) points, fibres the cosets
    nonsplit_fibration(p, nu)                 the orbit of u (u² = ν) = the quadric a² + bc = ν, p(p − 1) points; the Borel a section
    sphere(p, c)                              the points of x² + y² + z² = c: p(p + 1) for c a nonzero square (38:A9, B6)

The frame group has one form and the adjoint action (00:C27, 00:C22; `Theme/Spin.lean`, 20 October 2026): 𝔽_{p²} through
frc.extension.Ext, 2 × 2 matrices over it as tuples of pairs.

    xmul(K, A, B), xdagger(K, A), xdet(K, A)  the product, the adjoint A† = conj(A)ᵀ and the determinant over 𝔽_{p²}
    unitary(K, H, A)                          A† H A = H
    hermitian_wJ(p, nu)                       the form wJ, w = √ν, and (wJ)† = wJ
    su2_is_sl2(p, nu, full)                   every element of SL₂(𝔽_p) is wJ-unitary; the converse by enumeration of SL₂(𝔽_{p²}) (full) or on random non-rational elements
    su2_identity_count(p, nu)                 |SU₂(I)| = #{N(a) + N(b) = 1} = p³ − p; hermitian_congruence(p, nu): a Q with Qᵀ conj(Q) = wJ, Q SL₂ Q⁻¹ = SU₂(I)
    element_census(p)                         the six classes of SL₂(𝔽_p) by trace and discriminant, their counts, orders and the one involution
    quadric_counts(p, nu)                     S³, dS₃, H³, AdS₃ and ad − bc = 1 over 𝔽_p, the circle and the hyperbola
    psl2_image(p, r)                          the sphere's image in PGL₂ is PSL₂, index 2
    so3(p)                                    the adjoint action: PGL₂ → O(𝔰𝔩₂, −det) injective, det 1, image SO₃ of order p(p² − 1) (|O₃| by frames)
    no_section_split(p)                       the Sylow count: p + 1 Sylow p-subgroups, |N(U)| = p(p − 1), the unipotents generate PSL₂ > p(p + 1)
"""
from frc.extension import Ext as Ext2
from frc.shell import is_square


def mul(M, N, p):
    a, b, c, d = M; e, f, g, h = N
    return ((a * e + b * g) % p, (a * f + b * h) % p, (c * e + d * g) % p, (c * f + d * h) % p)


def det(M, p):
    a, b, c, d = M
    return (a * d - b * c) % p


def act(M, P, p):
    a, b, c, d = M; x, y = P
    return ((a * x + b * y) % p, (c * x + d * y) % p)


def normal(P, p):
    x, y = P[0] % p, P[1] % p
    if y: return (x * pow(y, -1, p) % p, 1)
    if x: return (1, 0)
    raise ValueError("the zero vector is no point")


def pclass(M, p):
    lead = next(v for v in M if v % p)
    s = pow(lead, -1, p)
    return tuple(v * s % p for v in M)


def line(p):
    return [(x, 1) for x in range(p)] + [(1, 0)]


def boost(nu, a, b, p):
    return (a % p, nu * b % p, b % p, a % p)


def borel(a, b, e, p):
    return (a % p, b % p, 0, e % p)


def pgl2(p):
    """Every class of PGL₂(F_p): the invertible matrices scaled to a leading 1, by search."""
    out = []
    for a in range(p):
        for b in range(p):
            for c in range(p):
                for d in range(p):
                    M = (a, b, c, d)
                    if det(M, p) and pclass(M, p) == M: out.append(M)
    return out


def factor(M, nu, p):
    """N M = borel(det M, b d − ν a c, N) · boost(d, c), N = d² − ν c² (Projective.lean, `hopf_section` (3))."""
    a, b, c, d = M
    N = (d * d - nu * c * c) % p
    return N, (det(M, p), (b * d - nu * a * c) % p, N), (d % p, c % p)


# ---- the frame triple and the two fibrations (38:A9, X4, B6) --------------------------------------------------------
def adj(M, p):
    a, b, c, d = M
    return (d % p, (-b) % p, (-c) % p, a % p)


def conj(M, N, p):
    """The conjugate M N M⁻¹ as a matrix (scalars cancel: well defined on the class of M), M⁻¹ = adj M / det M."""
    di = pow(det(M, p), -1, p)
    return tuple(x * di % p for x in mul(mul(M, N, p), adj(M, p), p))


def triple(M, nu, p):
    """The T·B factorisation of an invertible M (Projective.lean, `frame_triple` (1)): the direction M·[1 : 0] = [a : c],
    the boost (α, β) = (a, c) carrying the horizon to it with norm N = a² − νc², and the chart (N, ab − νcd, det M), with
    N M = boost(α, β) · borel(N, ab − νcd, det M)."""
    a, b, c, d = M
    N = (a * a - nu * c * c) % p
    direction = normal((a, c), p)
    chart = (N, (a * b - nu * c * d) % p, det(M, p))
    assert tuple(N * x % p for x in M) == mul(boost(nu, a, c, p), borel(*chart, p), p)
    return direction, (a % p, c % p), chart


def quaternion_matrix(x, y, z, w, r, p):
    """The quaternion x + y i + z j + w k as the matrix [[x + r y, z + r w], [−z + r w, x − r y]], r² = −1
    (Projective.lean, `sphere_det`): its determinant is x² + y² + z² + w², so the norm-one sphere is SL₂."""
    return ((x + r * y) % p, (z + r * w) % p, (-z + r * w) % p, (x - r * y) % p)


def sphere_is_sl2(p, r):
    """38:A7 — the quaternion matrices of the norm-one sphere x² + y² + z² + w² = 1 are exactly the matrices of
    determinant one of the quaternion form, and their number is p(p² − 1) = |SL₂|; returns
    (the norm equals the determinant on every quaternion, the sphere's size, |SL₂|, the two sets equal)."""
    assert r * r % p == p - 1
    quats = [(x, y, z, w) for x in range(p) for y in range(p) for z in range(p) for w in range(p)]
    norm_is_det = all((x * x + y * y + z * z + w * w) % p == det(quaternion_matrix(x, y, z, w, r, p), p) for x, y, z, w in quats)
    sphere = {quaternion_matrix(x, y, z, w, r, p) for x, y, z, w in quats if (x * x + y * y + z * z + w * w) % p == 1}
    return norm_is_det, len(sphere), len(sl2(p)), sphere == set(sl2(p))


def frame_triple(p, nu):
    """Every class of PGL₂(F_p) is one point of ℙ¹ (its direction) and one Borel class (the chart), uniquely: the map
    class ↦ (direction, Borel class) is a bijection onto ℙ¹ × (the p(p − 1) Borel classes); returns
    (the number of classes, p + 1, p(p − 1), bijective)."""
    G = pgl2(p)
    seen = set()
    for M in G:
        direction, _, chart = triple(M, nu, p)
        seen.add((direction, pclass(borel(*chart, p), p)))
    return len(G), p + 1, p * (p - 1), len(seen) == len(G) == (p + 1) * p * (p - 1)


def sl2(p):
    """The norm-one sphere SL₂(F_p) by elements: the matrices of determinant 1, p(p² − 1) of them."""
    return [(a, b, c, d) for a in range(p) for b in range(p) for c in range(p) for d in range(p) if (a * d - b * c) % p == 1]


def involutions(p):
    """(the involutions of SL₂, of PGL₂): one (−I) against p²; the two groups of order p(p² − 1) are not isomorphic
    (38:A7)."""
    I = (1, 0, 0, 1)
    s = sum(1 for M in sl2(p) if M != I and mul(M, M, p) == I)
    g = sum(1 for M in pgl2(p) if M != I and pclass(mul(M, M, p), p) == I)
    return s, g


def circle(p):
    """The points (x, y) of x² + y² = 1 over F_p: p − 1 of them when p ≡ 1 (mod 4), p + 1 when p ≡ 3 (38:B6)."""
    return [(x, y) for x in range(p) for y in range(p) if (x * x + y * y) % p == 1]


def unit(p):
    """The unit i = diag(r, −r) with r² = −1 on p = 4κ + 1 (r the least such residue)."""
    r = next(x for x in range(1, p) if x * x % p == p - 1)
    return (r, 0, 0, (-r) % p)


def centraliser(p):
    """The classes of PGL₂ whose matrices commute with the unit i (M i = i M as matrices, independent of the scalar):
    the diagonal torus, p − 1 classes, every one inside the Borel; returns (the classes, their number, all diagonal)."""
    i = unit(p)
    cen = [M for M in pgl2(p) if mul(M, i, p) == mul(i, M, p)]
    return cen, len(cen), all(M[1] == 0 and M[2] == 0 for M in cen)


def split_fibration(p):
    """The split fibration of PGL₂ by the unit i (38:A9): the conjugates M i M⁻¹ are exactly the points of the
    trace-zero quadric a² + bc = −1 (p(p + 1) points, none scalar), every fibre is a coset of the centraliser
    (p − 1 classes), and the Borel meets a fibre in the whole fibre or not at all (no section). Returns the dict."""
    i = unit(p)
    G = pgl2(p)
    fib = {}
    for M in G:
        N = conj(M, i, p)
        fib.setdefault(N, []).append(M)
    quadric = {(a, b, c, (-a) % p) for a in range(p) for b in range(p) for c in range(p) if (a * a + b * c) % p == p - 1}
    cen, _, _ = centraliser(p)
    B = {pclass(borel(a, b, e, p), p) for a in range(1, p) for b in range(p) for e in range(1, p)}
    return {"base": len(fib), "quadric": len(quadric), "orbit_is_quadric": set(fib) == quadric,
            "count": p * (p + 1), "fibre": p - 1, "fibres_are_cosets": all(len(v) == len(cen) for v in fib.values()),
            "borel_whole_or_none": all(len(set(v) & B) in (0, len(cen)) for v in fib.values())}


def nonsplit_fibration(p, nu):
    """The non-split fibration by u = [[0, ν], [1, 0]] (u² = ν a nonsquare; 00:C19, 38:A9): the conjugates fill the
    quadric a² + bc = ν (p(p − 1) points), the fibres are the cosets of the boost torus (p + 1 classes), and the Borel
    meets every fibre exactly once (the section)."""
    u = (0, nu % p, 1, 0)
    G = pgl2(p)
    fib = {}
    for M in G:
        N = conj(M, u, p)
        fib.setdefault(N, []).append(M)
    quadric = {(a, b, c, (-a) % p) for a in range(p) for b in range(p) for c in range(p) if (a * a + b * c) % p == nu % p}
    B = {pclass(borel(a, b, e, p), p) for a in range(1, p) for b in range(p) for e in range(1, p)}
    return {"base": len(fib), "quadric": len(quadric), "orbit_is_quadric": set(fib) == quadric, "count": p * (p - 1),
            "fibre": p + 1, "fibres": all(len(v) == p + 1 for v in fib.values()),
            "section": all(len(set(v) & B) == 1 for v in fib.values())}


def sphere(p, c):
    """The number of (x, y, z) with x² + y² + z² = c over F_p: p(p + 1) for c a nonzero square on p = 4κ + 1 (the unit
    sphere; Grav.sphere_area_rung), p(p − 1) for a nonsquare (38:A9)."""
    return sum(1 for x in range(p) for y in range(p) for z in range(p) if (x * x + y * y + z * z) % p == c % p)


# ---- the frame group has one form (00:C27) and the adjoint action (00:C22); Theme/Spin.lean, 20 October 2026 ------------
def xmul(K, A, B):
    """The product of two 2 × 2 matrices (a, b, c, d) over K = 𝔽_{p²}."""
    (a, b, c, d), (e, f, g, h) = A, B
    return (K.add(K.mul(a, e), K.mul(b, g)), K.add(K.mul(a, f), K.mul(b, h)),
            K.add(K.mul(c, e), K.mul(d, g)), K.add(K.mul(c, f), K.mul(d, h)))


def xdagger(K, A):
    """A† = conj(A)ᵀ."""
    a, b, c, d = A
    return (K.conj(a), K.conj(c), K.conj(b), K.conj(d))


def xdet(K, A):
    a, b, c, d = A
    return K.sub(K.mul(a, d), K.mul(b, c))


def unitary(K, H, A):
    """A is unitary for the form H: A† H A = H."""
    return xmul(K, xmul(K, xdagger(K, A), H), A) == H


def embed(K, M):
    """A matrix over 𝔽_p as a matrix over 𝔽_{p²}."""
    return tuple(K.scalar(x) for x in M)


def hermitian_wJ(p, nu):
    """The form H = wJ = [[0, w], [−w, 0]] with w = √ν (w^p = −w): returns (H, H† = H)."""
    K = Ext2(p, nu)
    w = (0, 1)
    H = (K.scalar(0), w, K.neg(w), K.scalar(0))
    return H, xdagger(K, H) == H


def su2_is_sl2(p, nu, full=False, samples=400, seed=27):
    """00:C27 — SU₂(𝔽_{p²}/𝔽_p) = SL₂(𝔽_p) for the form wJ: every element of SL₂(𝔽_p) is unitary; conversely, with full, by
    enumeration of SL₂(𝔽_{p²}) (|SL₂(𝔽_{p²})| = p⁶ − p², the unitary ones exactly the p³ − p rational ones), else on random
    elements of SL₂(𝔽_{p²}) with a non-rational entry, none unitary. Returns (all rational unitary, |SL₂(𝔽_p)|, |SL₂(𝔽_{p²})| or
    the sample size, the unitary count among them)."""
    K = Ext2(p, nu)
    H, _ = hermitian_wJ(p, nu)
    SL = sl2(p)
    rational = all(unitary(K, H, embed(K, M)) for M in SL)
    one = K.scalar(1)
    if full:
        els = K.elements(); n2 = cnt = 0
        for a in els:
            for b in els:
                for c in els:
                    bc = K.mul(b, c)
                    for d in els:
                        if K.sub(K.mul(a, d), bc) != one: continue
                        n2 += 1
                        if unitary(K, H, (a, b, c, d)): cnt += 1
        return rational, len(SL), n2, cnt
    import random
    rng = random.Random(seed); n2 = cnt = 0
    while n2 < samples:
        a, b, c = ((rng.randrange(p), rng.randrange(p)) for _ in range(3))
        if K.norm(a) == 0: continue
        d = K.mul(K.add(one, K.mul(b, c)), K.inv(a))                       # ad − bc = 1
        if all(x[1] == 0 for x in (a, b, c, d)): continue                 # a rational element: skip
        n2 += 1; cnt += unitary(K, H, (a, b, c, d))
    return rational, len(SL), n2, cnt


def su2_identity_count(p, nu):
    """|SU₂(I)| = #{(a, b) ∈ 𝔽_{p²}² : N(a) + N(b) = 1}, the quaternion shape [[a, b], [−b̄, ā]]: p³ − p = |SL₂(𝔽_p)|."""
    K = Ext2(p, nu)
    els = K.elements(); norms = [K.norm(x) for x in els]
    return sum(1 for na in norms for nb in norms if (na + nb) % p == 1)


def hermitian_congruence(p, nu):
    """An invertible Q over 𝔽_{p²} with Qᵀ conj(Q) = wJ (the identity form and wJ are congruent), and Q SL₂(𝔽_p) Q⁻¹ lands in
    SU₂(I) — the quaternion shape with N(a) + N(b) = 1 — injectively onto p³ − p elements. Returns (Q, shape, |image|)."""
    K = Ext2(p, nu); H, _ = hermitian_wJ(p, nu); Z, W = K.scalar(0), (0, 1)
    els = K.elements()
    Q = None
    for q1 in els:
        for q3 in els:
            if q3 == Z or (K.norm(q1) + K.norm(q3)) % p: continue
            for q2 in els:
                q4 = K.conj(K.mul(K.sub(W, K.mul(q1, K.conj(q2))), K.inv(q3)))
                if (K.norm(q2) + K.norm(q4)) % p: continue
                if xdet(K, (q1, q2, q3, q4)) == Z: continue
                Q = (q1, q2, q3, q4); break
            if Q: break
        if Q: break
    if Q is None: return None, False, 0
    a, b, c, d = Q
    assert xmul(K, (a, c, b, d), tuple(K.conj(x) for x in Q)) == H
    di = K.inv(xdet(K, Q))
    Qi = (K.mul(d, di), K.mul(K.neg(b), di), K.mul(K.neg(c), di), K.mul(a, di))
    img, shape = set(), True
    for M in sl2(p):
        B = xmul(K, xmul(K, Q, embed(K, M)), Qi)
        a, b, c, d = B
        shape &= c == K.neg(K.conj(b)) and d == K.conj(a) and (K.norm(a) + K.norm(b)) % p == 1
        img.add(B)
    return Q, shape, len(img)


def element_census(p):
    """The six classes of SL₂(𝔽_p): I, −I, the unipotents of trace 2 and −2, the split (t² − 4 a nonzero square) and the
    non-split (a nonsquare); their counts 1, 1, p² − 1, p² − 1, (p − 3)p(p + 1)/2, (p − 1)²p/2; the orders of a sample of
    each (unipotent p, negative unipotent 2p, split dividing p − 1, non-split dividing p + 1); the involutions (one, −I).
    Returns (counts, expected, orders by class, involutions)."""
    I = (1, 0, 0, 1); mI = (p - 1, 0, 0, p - 1)
    counts = {"I": 0, "-I": 0, "unip+": 0, "unip-": 0, "split": 0, "nonsplit": 0}
    orders = {k: set() for k in counts}
    def order(A):
        M, k = A, 1
        while M != I: M = mul(M, A, p); k += 1
        return k
    for A in sl2(p):
        t = (A[0] + A[3]) % p
        typ = "I" if A == I else "-I" if A == mI else "unip+" if t == 2 else "unip-" if t == p - 2 else \
              ("split" if is_square((t * t - 4) % p, p) else "nonsplit")
        counts[typ] += 1
        if counts[typ] <= 40 or counts[typ] % 97 == 0: orders[typ].add(order(A))
    expected = {"I": 1, "-I": 1, "unip+": p * p - 1, "unip-": p * p - 1, "split": (p - 3) * p * (p + 1) // 2, "nonsplit": (p - 1) * p * (p - 1) // 2}
    inv = sum(1 for A in sl2(p) if A != I and mul(A, A, p) == I)
    return counts, expected, orders, inv


def quadric_counts(p, nu):
    """The points of the five quadrics over 𝔽_p: S³ (x² + y² + z² + w² = 1), dS₃ (x² + y² + z² − w² = 1), H³ (= −1), AdS₃
    (x² + y² − z² − w² = 1) and the frame quadric ad − bc = 1 — all p³ − p at p = 4κ + 1; the circle x² + y² = 1 (p − 1
    points) and the hyperbola x² − νy² = 1 (p + 1). Returns (s4, s31, h3, s22, frame, circle, hyperbola)."""
    sq = [(x * x) % p for x in range(p)]
    def count(form, value=1):
        return sum(1 for x in range(p) for y in range(p) for z in range(p) for w in range(p) if form(sq[x], sq[y], sq[z], sq[w], x, y, z, w) % p == value % p)
    s4 = count(lambda X, Y, Z, W, x, y, z, w: X + Y + Z + W)
    s31 = count(lambda X, Y, Z, W, x, y, z, w: X + Y + Z - W)
    h3 = count(lambda X, Y, Z, W, x, y, z, w: X + Y + Z - W, -1)
    s22 = count(lambda X, Y, Z, W, x, y, z, w: X + Y - Z - W)
    fr = count(lambda X, Y, Z, W, x, y, z, w: x * w - y * z)
    circle_ = sum(1 for x in range(p) for y in range(p) if (sq[x] + sq[y]) % p == 1)
    hyper = sum(1 for x in range(p) for y in range(p) if (sq[x] - nu * sq[y]) % p == 1)
    return s4, s31, h3, s22, fr, circle_, hyper


def psl2_image(p, r):
    """The sphere's image in PGL₂ is PSL₂, of index 2: returns (|image classes|, |PGL₂|)."""
    assert r * r % p == p - 1
    img = {pclass(quaternion_matrix(x, y, z, w, r, p), p) for x in range(p) for y in range(p) for z in range(p) for w in range(p)
           if (x * x + y * y + z * z + w * w) % p == 1}
    return len(img), len(pgl2(p))


def so3(p):
    """00:C22 — the adjoint action Ad(M): X ↦ M X M⁻¹ on the trace-zero matrices X = a h + b e + f c (h = diag(1, −1)): over
    the classes of PGL₂ the images are p(p² − 1) distinct 3 × 3 matrices (Ad injective), each of determinant 1 and orthogonal
    for Q(a, b, c) = a² + bc = −det X on every vector; |O(Q)| = 2p(p² − 1) by counting orthonormal frames, so the image is
    SO₃. Returns (|image|, |PGL₂|, the determinants, orthogonal, |O₃|)."""
    G = pgl2(p)
    basis = [(1, 0, 0, p - 1), (0, 1, 0, 0), (0, 0, 1, 0)]
    def Ad(M):
        di = pow(det(M, p), -1, p); Mi = tuple(x * di % p for x in adj(M, p))             # M⁻¹ = adj(M)/det M
        return tuple(tuple(mul(mul(M, X, p), Mi, p)[:3]) for X in basis)                # the columns (a, b, c) of the images
    def det3(c):
        (a, d, g), (b, e, h), (cc, f, i) = c
        return (a * (e * i - f * h) - b * (d * i - f * g) + cc * (d * h - e * g)) % p
    def apply(c, v): return tuple((c[0][k] * v[0] + c[1][k] * v[1] + c[2][k] * v[2]) % p for k in range(3))
    Qf = lambda v: (v[0] * v[0] + v[1] * v[2]) % p
    imgs = {Ad(M) for M in G}
    dets = {det3(c) for c in imgs}
    vecs = [(x, y, z) for x in range(p) for y in range(p) for z in range(p)]
    orth = all(Qf(apply(c, v)) == Qf(v) for c in imgs for v in vecs[::max(1, len(vecs) // 60)])
    Bf = lambda u, v: (2 * u[0] * v[0] + u[1] * v[2] + u[2] * v[1]) % p
    e1s = [v for v in vecs if Qf(v) == 1]
    e1 = (1, 0, 0)
    e2s = [v for v in e1s if Bf(v, e1) == 0]
    e2 = e2s[0]
    e3s = [v for v in e1s if Bf(v, e1) == 0 and Bf(v, e2) == 0]
    O3 = len(e1s) * len(e2s) * len(e3s)
    return len(imgs), len(G), dets, orth, O3


def no_section_split(p):
    """00:C22 — the split fibration has no section at p = 4κ + 1: a subgroup of order p(p + 1) would hold a Sylow
    p-subgroup U; normal in it, the subgroup lies in N(U) of order p(p − 1) < p(p + 1); not normal, it holds all p + 1
    Sylow p-subgroups, which generate PSL₂ of order p(p² − 1)/2 > p(p + 1) for p > 3. Returns (the Sylow count, |N(U)|,
    the order generated by the unipotents, the split torus inside the Borel)."""
    G = pgl2(p); I = (1, 0, 0, 1)
    def close(gens):
        H, fr = {I}, [I]
        while fr:
            nx = []
            for x in fr:
                for g in gens:
                    y = pclass(mul(x, g, p), p)
                    if y not in H: H.add(y); nx.append(y)
            fr = nx
        return H
    U = close([(1, 1, 0, 1)])
    sylows = {frozenset(pclass(conj(M, u, p), p) for u in U) for M in G}
    NU = [M for M in G if frozenset(pclass(conj(M, u, p), p) for u in U) == frozenset(U)]
    gen = close(sorted(set().union(*sylows)))
    Ts = {pclass((a, 0, 0, 1), p) for a in range(1, p)}
    B = {pclass(borel(a, b, 1, p), p) for a in range(1, p) for b in range(p)}
    return len(sylows), len(NU), len(gen), Ts <= B
