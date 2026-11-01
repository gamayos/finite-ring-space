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

The register square and the finite Lorentz group (7-spacetime; `Theme/Lorentz.lean`, 31 October 2026): the Hermitian
matrices over 𝔽_{p²} as the register square Herm₂(K) = Sym²(V) ⊕ 𝔽_p ηJ with det X = x₀² − x₁² − x₃² + ν x₂².

    herm(K, x), herm_coords(K, X), lorentz_form(x, nu, p)    X(x), its inverse, and Q_ν(x) = det X(x)
    register_square(p, nu)                    det X(x) = Q_ν(x) on all of 𝔽_p⁴; the null counts p³ − p² + p and p² + 1 (7:C1)
    cone_bijection(p, nu)                     [v] ↦ [v v†] bijective ℙ¹(K) → null lines; ℙ¹(𝔽_p) symmetric, the rest with a time component (7:C3, C4)
    sl2_ext(K), congruence(K, A, X)           SL₂(K) once, and A X A†
    congruence_image(p, nu)                   the kernel ±I, the image p²(p⁴ − 1)/2 of index four in O₄⁻, the stabiliser SL₂(𝔽_p), T/P/−I outside (7:C2, D1, F3)
    class_equation(p)                         orders divide p − 1, p, p + 1; the maximal cyclic subgroups partition G ∖ {1} (7:C9, B1)
    direction_classes(p, nu)                  the p + 1 null, p(p − 1)/2 internal and p(p + 1)/2 external directions of space (7:C8, C9)
    hopf_fibration(p, nu)                     SL₂(𝔽_p) transitive on the p(p − 1) causal rays with stabiliser C_{p+1}; the Borel section; the axes (7:C7, C8)
    drive_on_square(p, nu, g)                 diag(g, 1): [z] ↦ [gz], ηJ ↦ g ηJ; the lift diag(η, η⁻¹): ηJ ↦ −ηJ; the even transport (7:D3)
    two_circuits(p, nu)                       N¹ of order p + 1 with −I, image of order (p + 1)/2, conjugate to the torus lift (7:D4)
    no_definite_space(p, nu)                  every three-dimensional subspace carries a null vector (7:D5)
    horizon_half_step(p, nu)                  K^×/𝔽_p^× regular on ℙ¹(𝔽_p); the horizon at the half step 2κ + 1 by every generator (7:D6)
    similitude(p, nu, g)                      the similitude of multiplier g exchanging the two non-null classes (7:C6)
    elliptic_hyperbolic(p, nu)                the frame quadric hyperbolic, the register square elliptic (7:C5)
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


# ---- the register square and the finite Lorentz group (7-spacetime; Theme/Lorentz.lean, 31 October 2026) -----------------
# The Hermitian 2 × 2 matrices over K = 𝔽_{p²} = 𝔽_p(η), η² = ν a nonsquare, as the register square Herm₂(K) = Sym²(V) ⊕ 𝔽_p ηJ
# with coordinates x = (x₀, x₁, x₂, x₃): X(x) = [[x₀ + x₃, x₁ + η x₂], [x₁ − η x₂, x₀ − x₃]], det X = x₀² − x₁² − x₃² + ν x₂²
# (7:C1); SL₂(K) acts by the congruence X ↦ A X A† (7:C2); the cone ℙ¹(K) → null lines, [v] ↦ [v v†] (7:C3, C4); the
# three cycles and the class equation of PGL₂ (7:C9); the fibration (7:C7, C8); the drive, the lift and the horizon
# (7:D3, D4, D6); the three exclusions of the arrow (7:F3). Exact integers only.

def herm(K, x):
    """X(x), the Hermitian matrix of the coordinates x = (x₀, x₁, x₂, x₃) ∈ 𝔽_p⁴."""
    p = K.p; x0, x1, x2, x3 = (v % p for v in x)
    return (((x0 + x3) % p, 0), (x1, x2), (x1, (-x2) % p), ((x0 - x3) % p, 0))


def herm_coords(K, X):
    """The coordinates of a Hermitian matrix (None if X is not Hermitian): x₀ = (a + d)/2, x₃ = (a − d)/2, (x₁, x₂) = b."""
    p = K.p; a, b, c, d = X
    if a[1] or d[1] or c != K.conj(b): return None
    h = pow(2, -1, p)
    return ((a[0] + d[0]) * h % p, b[0], b[1], (a[0] - d[0]) * h % p)


def lorentz_form(x, nu, p):
    """Q_ν(x) = x₀² − x₁² − x₃² + ν x₂², the determinant of X(x) (7:C1)."""
    x0, x1, x2, x3 = x
    return (x0 * x0 - x1 * x1 - x3 * x3 + nu * x2 * x2) % p


def register_square(p, nu):
    """7:C1 — on every x ∈ 𝔽_p⁴, X(x) is Hermitian with det X(x) = Q_ν(x) and herm_coords inverts herm; the null vectors
    number p³ − p² + p with the zero vector (the elliptic count, 3:B4), the null lines p² + 1. Returns (identity on all p⁴, null vectors, null lines)."""
    K = Ext2(p, nu); ok, nulls = True, 0
    for x in ((a, b, c, d) for a in range(p) for b in range(p) for c in range(p) for d in range(p)):
        X = herm(K, x)
        ok &= xdagger(K, X) == X and xdet(K, X) == (lorentz_form(x, nu, p), 0) and herm_coords(K, X) == x
        nulls += lorentz_form(x, nu, p) == 0
    return ok, nulls, (nulls - 1) // (p - 1)


def null_count_by_fibres(p, nu):
    """7:C1 on a large Subject — the null vectors of Q_ν(x) = x₀² − x₁² − x₃² + ν x₂² counted through the two binary forms
    without visiting 𝔽_p⁴: r(v) = #{(x₁, x₂) : x₁² − ν x₂² = v} and s(w) = #{(x₀, x₃) : x₀² − x₃² = w} are each O(p²), and
    the null count is Σ_v r(v) s(v). Returns (null vectors, null lines); equals register_square's count where both run."""
    r, s_ = [0] * p, [0] * p
    for x1 in range(p):
        for x2 in range(p): r[(x1 * x1 - nu * x2 * x2) % p] += 1
    for x0 in range(p):
        for x3 in range(p): s_[(x0 * x0 - x3 * x3) % p] += 1
    nulls = sum(r[v] * s_[v] for v in range(p))
    return nulls, (nulls - 1) // (p - 1)


def proj_line_ext(K):
    """ℙ¹(K): the p² + 1 points (z, 1) and (1, 0), z ∈ K."""
    return [(z, (1, 0)) for z in K.elements()] + [((1, 0), (0, 0))]


def herm_class(K, X):
    """A nonzero Hermitian matrix scaled to leading coefficient one (the null line it spans)."""
    p = K.p; x = herm_coords(K, X)
    lead = next(v for v in x if v)
    s = pow(lead, -1, p)
    return tuple(v * s % p for v in x)


def cone_bijection(p, nu):
    """7:C3, 7:C4 — [v] ↦ [v v†] is a bijection of ℙ¹(K) onto the null lines of the register square: p² + 1 directions; the
    p + 1 points of ℙ¹(𝔽_p) give the symmetric matrices (x₂ = 0), the p(p − 1) others carry a time component (x₂ ≠ 0).
    Returns (bijective, |ℙ¹(K)|, null lines, symmetric images, time-carrying images)."""
    K = Ext2(p, nu)
    nulls = {tuple(x) for x in ((a, b, c, d) for a in range(p) for b in range(p) for c in range(p) for d in range(p))
             if any(x) and lorentz_form(x, nu, p) == 0 and x[next(k for k, v in enumerate(x) if v)] == 1}
    img, sym, tim = {}, 0, 0
    for v1, v2 in proj_line_ext(K):
        X = (K.mul(v1, K.conj(v1)), K.mul(v1, K.conj(v2)), K.mul(v2, K.conj(v1)), K.mul(v2, K.conj(v2)))
        x = herm_coords(K, X)
        assert x is not None and lorentz_form(x, nu, p) == 0
        img[(v1, v2)] = herm_class(K, X)
        if x[2] == 0: sym += 1
        else: tim += 1
    bij = len(set(img.values())) == len(img) == len(nulls) and set(img.values()) == nulls
    return bij, len(img), len(nulls), sym, tim


def sl2_ext(K):
    """SL₂(K) exactly once: (a, b, c, d) with d = (1 + bc)/a for a ≠ 0, and the sheet a = 0, c = −1/b."""
    els = K.elements(); one = (1, 0); zero = (0, 0)
    for a in els:
        if a == zero: continue
        ai = K.inv(a)
        for b in els:
            for c in els:
                bc = K.mul(b, c)
                yield (a, b, c, K.mul(K.add(one, bc), ai))
    for b in els:
        if b == zero: continue
        c = K.neg(K.inv(b))
        for d in els:
            yield (zero, b, c, d)


def congruence(K, A, X):
    """A X A†."""
    return xmul(K, xmul(K, A, X), xdagger(K, A))


def congruence_image(p, nu):
    """7:C2, 7:D1, 7:F3 — over SL₂(K), enumerated once: the kernel of A ↦ (X ↦ A X A†) on the four basis vectors is ±I,
    so the image has order |SL₂(K)|/2 = p²(p⁴ − 1)/2 = |O₄⁻(p)|/4 (index four); the stabiliser of the time vector ηJ is
    exactly SL₂(𝔽_p) (p³ − p elements, all Frobenius-fixed); and no A carries X to σ(X) (the time reversal, x₂ ↦ −x₂), to
    the reflection x₁ ↦ −x₁, or to −X. Returns a dict of the counts."""
    K = Ext2(p, nu); zero, one = (0, 0), (1, 0); mone = ((-1) % p, 0)
    eta = (0, 1); etaJ = herm(K, (0, 0, 1, 0))
    basis = [herm(K, e) for e in ((1, 0, 0, 0), (0, 1, 0, 0), (0, 0, 1, 0), (0, 0, 0, 1))]
    T = [herm(K, e) for e in ((1, 0, 0, 0), (0, 1, 0, 0), (0, 0, p - 1, 0), (0, 0, 0, 1))]      # the Frobenius σ: x₂ ↦ −x₂
    P = [herm(K, e) for e in ((1, 0, 0, 0), (0, p - 1, 0, 0), (0, 0, 1, 0), (0, 0, 0, 1))]      # x₁ ↦ −x₁
    PT = [herm(K, e) for e in ((p - 1, 0, 0, 0), (0, p - 1, 0, 0), (0, 0, p - 1, 0), (0, 0, 0, p - 1))]   # X ↦ −X
    n = kernel = stab = stab_rational = hitT = hitP = hitPT = 0
    for A in sl2_ext(K):
        n += 1
        a, b, c, d = A
        # A A† = X(e₀) ↦ ? : the images of I decide quickly whether the four tests can hold (I ↦ I for the kernel, T, P; I ↦ −I for PT)
        aa = xmul(K, A, xdagger(K, A))
        if congruence(K, A, etaJ) == etaJ:
            stab += 1
            if all(v[1] == 0 for v in A): stab_rational += 1
        if aa == (one, zero, zero, one):
            imgs = [congruence(K, A, X) for X in basis]
            if imgs == basis: kernel += 1
            if imgs == T: hitT += 1
            if imgs == P: hitP += 1
        elif aa == (mone, zero, zero, mone):
            if [congruence(K, A, X) for X in basis] == PT: hitPT += 1
    from frc.shell import o_minus_4
    return dict(sl2K=n, sl2K_formula=p * p * (p ** 4 - 1), kernel=kernel, image=n // kernel, image_formula=p * p * (p ** 4 - 1) // 2,
                o_minus_4=o_minus_4(p), index=o_minus_4(p) // (n // kernel), stabiliser=stab, stabiliser_rational=stab_rational,
                sl2p=p * (p * p - 1), T_hits=hitT, P_hits=hitP, PT_hits=hitPT)


def class_equation(p):
    """7:C9, 7:B1 — the order of every element of PGL₂(𝔽_p) divides p − 1, p or p + 1; the maximal cyclic subgroups are the
    split tori (order p − 1), the unipotent groups (p) and the non-split tori (p + 1), p(p + 1)/2, p + 1 and p(p − 1)/2 of
    them, and they partition G ∖ {1}: 1 + (p² − 1) + p(p + 1)(p − 2)/2 + p²(p − 1)/2 = (p − 1)p(p + 1). Returns (orders divide,
    the counts of maximal cyclic subgroups by order, partition, the class equation)."""
    G = pgl2(p); I = (1, 0, 0, 1)
    def cyc(M):
        H, X = [I], M
        while X != I: H.append(X); X = pclass(mul(X, M, p), p)
        return frozenset(H)
    cycs = {cyc(M) for M in G if M != I}
    divides = all((p - 1) % len(H) == 0 or p % len(H) == 0 or (p + 1) % len(H) == 0 for H in cycs)
    maximal = [H for H in cycs if not any(H < H2 for H2 in cycs)]
    counts = {len(H): sum(1 for H2 in maximal if len(H2) == len(H)) for H in maximal}
    covered = [x for H in maximal for x in H if x != I]
    partition = len(covered) == len(set(covered)) == len(G) - 1
    eq = 1 + (p * p - 1) + p * (p + 1) * (p - 2) // 2 + p * p * (p - 1) // 2 == (p - 1) * p * (p + 1) == len(G)
    return divides, counts, partition, eq


def direction_classes(p, nu):
    """7:C8, 7:C9 — the p² + p + 1 directions of space Sym²(V) ≅ binary forms by the square class of the discriminant
    s₁₂² − s₁₁s₂₂ = −det: the null directions (p + 1, the conic and [1:0]), the internal points (p(p − 1)/2, the nonsquare
    axes, the Hopf base) and the external points (p(p + 1)/2). Returns (null, internal, external)."""
    pts = [(a, b, c) for a in range(p) for b in range(p) for c in range(p) if any((a, b, c)) and (a, b, c)[next(k for k, v in enumerate((a, b, c)) if v)] == 1]
    null = internal = external = 0
    for s11, s12, s22 in pts:
        d = (s12 * s12 - s11 * s22) % p
        if d == 0: null += 1
        elif is_square(d, p): external += 1
        else: internal += 1
    return null, internal, external


def hopf_fibration(p, nu):
    """7:C7, 7:C8 — SL₂(𝔽_p) acts on the causal rays H_p = ℙ¹(K) ∖ ℙ¹(𝔽_p) (p(p − 1) of them) by Möbius maps: transitively,
    with stabiliser of η the norm-one torus {[[α, νβ], [β, α]] : α² − νβ² = 1} of order p + 1 (the fibration with fibre
    C_{p+1}); the Borel B = {[[a, b], [0, 1]]} of G is simply transitive on H_p (a section in G); the Borel lift of SL₂,
    {[[a, b], [0, a⁻¹]]}, has two orbits of p(p − 1)/2 and meets the torus in ±I. The axis of a ray z: the binary form
    (t − z)(t − z̄) = t² − tr(z) t + N(z) has discriminant tr² − 4N = 4ν(Im z)², a nonsquare. Returns a dict."""
    K = Ext2(p, nu)
    rays = [z for z in K.elements() if z[1] != 0]
    def mob(M, z):                       # (a z + b)/(c z + d) on K, M over 𝔽_p; None at the pole
        a, b, c, d = M
        num = K.add(K.mul(K.scalar(a), z), K.scalar(b)); den = K.add(K.mul(K.scalar(c), z), K.scalar(d))
        return K.mul(num, K.inv(den)) if den != (0, 0) else None
    SL = sl2(p); eta = (0, 1)
    orbit = {mob(M, eta) for M in SL}
    stab = [M for M in SL if mob(M, eta) == eta]
    torus = {(a % p, nu * b % p, b % p, a % p) for a in range(p) for b in range(p) if (a * a - nu * b * b) % p == 1}
    B = [(a, b, 0, 1) for a in range(1, p) for b in range(p)]
    reach = {mob(M, eta) for M in B}
    free = len(reach) == len(B)
    Bl = [(a, b, 0, pow(a, -1, p)) for a in range(1, p) for b in range(p)]
    orbs = []
    seen = set()
    for z in rays:
        if z in seen: continue
        o = {mob(M, z) for M in Bl}; orbs.append(len(o)); seen |= o
    mI = (p - 1, 0, 0, p - 1)
    nonsq_axes = all(not is_square((4 * nu * z[1] * z[1]) % p, p) and ((2 * z[0]) ** 2 - 4 * K.norm(z)) % p == (4 * nu * z[1] * z[1]) % p for z in rays)
    return dict(rays=len(rays), transitive=orbit == set(rays), stabiliser=len(stab), torus=set(stab) == torus, torus_order=len(torus),
                borel_section=free and reach == set(rays), borel_lift_orbits=sorted(orbs), lift_meets_torus_in_pm_I=set(Bl) & torus == {(1, 0, 0, 1), mI},
                axes_nonsquare=nonsq_axes, count=len(SL) == len(rays) * len(torus))


def drive_on_square(p, nu, g):
    """7:D3, 7:A16 — the one-chronon move diag(g, 1) carries [z : 1] to [g z : 1] and ηJ to g·ηJ (the class flips, two
    chronons restore it); the unimodular lift D = diag(η, η⁻¹) has det 1, D† = −D and D(ηJ)D† = −ηJ; the even transport
    diag(g, g⁻¹) fixes ηJ and σ_x and dilates E₂₂ by g⁻² and E₁₁ by g². Returns a dict of booleans."""
    K = Ext2(p, nu); zero, one = (0, 0), (1, 0); eta = (0, 1)
    etaJ = herm(K, (0, 0, 1, 0)); sx = herm(K, (0, 1, 0, 0)); E11 = (one, zero, zero, zero); E22 = (zero, zero, zero, one)
    G1 = (K.scalar(g), zero, zero, one)
    scal = lambda s, X: tuple(K.mul(K.scalar(s), v) for v in X)
    rays_ok = all(herm_class(K, congruence(K, G1, (K.mul(z, K.conj(z)), z, K.conj(z), one))) ==
                  herm_class(K, (K.mul(K.mul(K.scalar(g), z), K.conj(K.mul(K.scalar(g), z))), K.mul(K.scalar(g), z), K.conj(K.mul(K.scalar(g), z)), one))
                  for z in K.elements())
    time_g = congruence(K, G1, etaJ) == scal(g, etaJ)
    twice = congruence(K, G1, congruence(K, G1, etaJ)) == scal(g * g % p, etaJ)
    D = (eta, zero, zero, K.inv(eta))
    lift = xdet(K, D) == one and xdagger(K, D) == tuple(K.neg(v) for v in D) and congruence(K, D, etaJ) == tuple(K.neg(v) for v in etaJ)
    E = (K.scalar(g), zero, zero, K.scalar(pow(g, -1, p)))
    gi2 = pow(g, -2, p)
    even = (xdet(K, E) == one and congruence(K, E, etaJ) == etaJ and congruence(K, E, sx) == sx and
            congruence(K, E, E22) == scal(gi2, E22) and congruence(K, E, E11) == scal(g * g % p, E11))
    return dict(rays=rays_ok, time_scaled_by_g=time_g, two_chronons_square=twice, g_nonsquare=not is_square(g, p), lift=lift, even_transport=even)


def two_circuits(p, nu):
    """7:D4 — N¹ = {diag(λ, λ̄) : N(λ) = 1} has order p + 1, contains −I, and its image on the register square has order
    (p + 1)/2 (−I acts trivially: the spinor closes in two circuits); N¹ and the torus lift are conjugate in SL₂(K) through
    P = [[η, −η], [1, 1]]: P diag(λ, λ̄) P⁻¹ is the matrix of multiplication by λ in the basis (1, η). Returns a dict."""
    K = Ext2(p, nu); zero, one = (0, 0), (1, 0); eta = (0, 1)
    N1 = [(l, zero, zero, K.conj(l)) for l in K.elements() if K.norm(l) == 1]
    basis = [herm(K, e) for e in ((1, 0, 0, 0), (0, 1, 0, 0), (0, 0, 1, 0), (0, 0, 0, 1))]
    imgs = {tuple(congruence(K, A, X) for X in basis) for A in N1}
    mI = (K.scalar(p - 1), zero, zero, K.scalar(p - 1))
    P = (eta, K.neg(eta), one, one); Pi_den = K.inv(xdet(K, P)); a, b, c, d = P
    Pi = (K.mul(d, Pi_den), K.mul(K.neg(b), Pi_den), K.mul(K.neg(c), Pi_den), K.mul(a, Pi_den))
    conj_ok = True
    for A in N1:
        l = A[0]
        M = xmul(K, xmul(K, P, A), Pi)                     # multiplication by λ = x + yη on (1, η): [[x, νy], [y, x]]
        x, y = l
        conj_ok &= M == (K.scalar(x), K.scalar(nu * y % p), K.scalar(y), K.scalar(x))
    return dict(order=len(N1), order_formula=p + 1, contains_minus_I=mI in N1, image_order=len(imgs), half=(p + 1) // 2, conjugate_to_torus=conj_ok)


def no_definite_space(p, nu):
    """7:D5 — every three-dimensional subspace of the register square (the kernel of a nonzero linear form ℓ) contains a
    nonzero null vector of Q_ν; by search over the p³ + p² + p + 1 forms. Returns (all hyperplanes isotropic, their number)."""
    forms = [(a, b, c, d) for a in range(p) for b in range(p) for c in range(p) for d in range(p) if any((a, b, c, d)) and (a, b, c, d)[next(k for k, v in enumerate((a, b, c, d)) if v)] == 1]
    nulls = [x for x in ((a, b, c, d) for a in range(p) for b in range(p) for c in range(p) for d in range(p)) if any(x) and lorentz_form(x, nu, p) == 0]
    ok = all(any((l[0] * x[0] + l[1] * x[1] + l[2] * x[2] + l[3] * x[3]) % p == 0 for x in nulls) for l in forms)
    return ok, len(forms)


def horizon_half_step(p, nu):
    """7:D6 — K^×/𝔽_p^× (cyclic of order p + 1) acts regularly on ℙ¹(𝔽_p) under [x : y] ↔ x + yη; η is its unique element of
    order two, the horizon [1 : 0] ↔ 1 is reached from the origin [0 : 1] ↔ η by every generator first at the half step
    (p + 1)/2 = 2κ + 1, which is odd; the unimodular torus (the even steps) never reaches it. Returns a dict."""
    K = Ext2(p, nu); one, eta = (1, 0), (0, 1)
    def cls(z):                                   # the class of z = x + yη in K^×/𝔽_p^× as the point [y : x] of ℙ¹(𝔽_p): 1 ↦ [0 : 1] the origin, η ↦ [1 : 0] the horizon
        return normal((z[1], z[0]), p)
    origin, horizon = cls(one), cls(eta)
    pts = {cls(z) for z in K.elements() if z != (0, 0)}
    regular = len(pts) == p + 1 and (origin, horizon) == ((0, 1), (1, 0))
    order2 = [z for z in K.elements() if z != (0, 0) and cls(z) != origin and cls(K.mul(z, z)) == origin]
    gens = [w for w in K.elements() if w != (0, 0) and len({cls(K.pow(w, k)) for k in range(p + 1)}) == p + 1]
    half = (p + 1) // 2
    first = {}
    for w in gens:
        k, z = 0, one
        while cls(z) != horizon: z = K.mul(w, z); k += 1
        first[w] = k
    even_never = all(cls(K.pow(w, 2 * k)) != horizon for w in gens[:12] for k in range(p + 1))
    return dict(regular=regular, order_two_classes={cls(z) for z in order2}, generators=len(gens), first_step=set(first.values()),
                half=half, half_odd=half % 2 == 1, even_never=even_never)


def similitude(p, nu, g):
    """7:C6 — no inertia: with a² + b² = g (solvable: the sums of two squares cover 𝔽_p) and c² = −1 the map
    (t, x, y, z) ↦ (c z, a x − b y, b x + a y, c g t) multiplies Q_g = −g t² + x² + y² + z² by g and so exchanges the two
    non-null classes, which are equal in size (3:B7); ⟨1,1,1,g⟩ ≅ ⟨1,g,g,g⟩. Returns a dict."""
    c = next(x for x in range(1, p) if x * x % p == p - 1)
    a, b = next((a, b) for a in range(p) for b in range(p) if (a * a + b * b) % p == g % p)
    Qg = lambda v: (-g * v[0] * v[0] + v[1] * v[1] + v[2] * v[2] + v[3] * v[3]) % p
    S = lambda v: ((c * v[3]) % p, (a * v[1] - b * v[2]) % p, (b * v[1] + a * v[2]) % p, (c * g * v[0]) % p)
    vecs = [(t, x, y, z) for t in range(p) for x in range(p) for y in range(p) for z in range(p)]
    mult = all(Qg(S(v)) == g * Qg(v) % p for v in vecs)
    sq = {v for v in vecs if Qg(v) and is_square(Qg(v), p)}; nsq = {v for v in vecs if Qg(v) and not is_square(Qg(v), p)}
    exchange = {S(v) for v in sq} == nsq and {S(v) for v in nsq} == sq
    inj = len({S(v) for v in vecs}) == len(vecs)
    return dict(c=c, ab=(a, b), multiplies=mult, exchanges=exchange, equal_classes=len(sq) == len(nsq), bijective=inj)


def elliptic_hyperbolic(p, nu):
    """7:C5 — the frame quadric (M₂(𝔽_p), det) has (p + 1)² null lines and a totally isotropic plane (hyperbolic, Witt index
    two); the register square has p² + 1 null lines and no totally isotropic plane (elliptic, Witt index one); and
    ⟨1,1,1,1⟩ ≅ ⟨1,1,1,−1⟩ have the same null count (the sign pattern is not the invariant). Returns a dict."""
    def null_lines(Q):
        return [x for x in ((a, b, c, d) for a in range(p) for b in range(p) for c in range(p) for d in range(p)) if any(x) and Q(x) == 0 and x[next(k for k, v in enumerate(x) if v)] == 1]
    def has_plane(Q, nulls):
        B = lambda u, v: (Q(tuple((a + b) % p for a, b in zip(u, v))) - Q(u) - Q(v)) % p
        return any(B(u, v) == 0 for i, u in enumerate(nulls) for v in nulls[i + 1:])
    frame = lambda x: (x[0] * x[3] - x[1] * x[2]) % p
    reg = lambda x: lorentz_form(x, nu, p)
    s4 = lambda x: (x[0] ** 2 + x[1] ** 2 + x[2] ** 2 + x[3] ** 2) % p
    s31 = lambda x: (x[0] ** 2 + x[1] ** 2 + x[2] ** 2 - x[3] ** 2) % p
    nf, nr, n4, n31 = null_lines(frame), null_lines(reg), null_lines(s4), null_lines(s31)
    return dict(frame_null=len(nf), frame_formula=(p + 1) ** 2, frame_plane=has_plane(frame, nf), register_null=len(nr),
                register_formula=p * p + 1, register_plane=has_plane(reg, nr), s4_null=len(n4), s31_null=len(n31))
