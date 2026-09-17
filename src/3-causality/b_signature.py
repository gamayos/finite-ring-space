"""
b_signature.py — block B: the signature on the shell and its collapse in the extension (3:B4, B5, B6, B7)
=========================================================================================================
The dichotomy is decided by counting.  On F_p the form Q_ν = −ν t² + x² + y² + z² has p³ − p² + p zeros when ν is a
nonsquare (the elliptic, minus type: Witt index 1, the Lorentzian class) and p³ + p² − p when ν is a square (the
hyperbolic, plus type: Witt index 2, the Euclidean class); the isometry groups are O_4^−(p) of order 2p²(p⁴−1) and
O_4^+(p) of order 2p²(p²−1)², counted by orthogonal frames (B1, B3).  Over K = F_{p²} every element of F_p is a
square, Q_ν has q³ + q² − q zeros with q = p² and |O(Q_ν, K)| = 2q²(q²−1)²: the plus type — the extension is where
the dichotomy collapses, not where it arises (B2).  The causal classes — the null cone and the two classes of
non-null vectors by the square class of Q_ν(v) — are invariant under every isometry and under rescaling (B4).
"""
import random
import lcommon as lc

def ext_value_counts(K, coeffs):
    """counts[w] = #{v in K^n : Q(v) = w} for K = F_{p²} (elements as pairs), by convolution."""
    els = K.elements(); idx = {z: i for i, z in enumerate(els)}
    dist = {(0, 0): 1}
    for a in coeffs:
        one = {}
        for x in els:
            w = K.mul(K.scalar(a) if isinstance(a, int) else a, K.mul(x, x)); one[w] = one.get(w, 0) + 1
        new = {}
        for u, cu in dist.items():
            for w, cw in one.items():
                s = K.add(u, w); new[s] = new.get(s, 0) + cu * cw
        dist = new
    return dist

def ext_orthogonal_order(K, coeffs):
    n = 1
    for i, a in enumerate(coeffs):
        n *= ext_value_counts(K, coeffs[i:]).get(K.scalar(a), 0)
    return n

def run():
    # B1 the zero counts on the shell decide the type (3:B4); agrees with 8:B7 (2353, 2041 at p = 13)
    ok = True; det = []
    for p, k in lc.SHELLS:
        S, N = lc.squares(p), lc.nonsquares(p)
        for nu in N:
            ok &= lc.isotropic_count(((-nu) % p, 1, 1, 1), p) == p ** 3 - p * p + p
        for nu in S:
            ok &= lc.isotropic_count(((-nu) % p, 1, 1, 1), p) == p ** 3 + p * p - p
        ok &= all(not lc.is_square((-nu) % p, p) for nu in N)     # the discriminant -nu is a nonsquare for nu in N
        det.append(f"p={p}: {p**3 - p*p + p} zeros (nu in N), {p**3 + p*p - p} (nu in S)")
    lc.check("B1", "Q_nu has p^3 - p^2 + p zeros for nu nonsquare (elliptic, Witt index 1) and p^3 + p^2 - p for nu square (hyperbolic, Witt index 2), every nu", ok, "; ".join(det[:4]))

    # B2 over K = F_{p^2} the dichotomy collapses: nu = c^2, Q_nu of the plus type, q^3 + q^2 - q zeros, |O| = 2q^2(q^2-1)^2 (3:B5)
    ok = True; det = []
    for p in (5, 13):
        nu = lc.nonsquares(p)[0]; K = lc.Ext(p, nu); q = p * p
        c = (0, 1)
        ok &= K.mul(c, c) == (nu, 0)                                              # c^2 = nu in K
        ok &= all(K.is_square_ext((a, 0)) for a in range(1, p))                    # every element of F_p is a square in K
        z = ext_value_counts(K, [(-nu) % p, 1, 1, 1])[(0, 0)]
        ok &= z == q ** 3 + q * q - q
        det.append(f"p={p}: q={q}, {z} zeros of Q_nu over K = q^3+q^2-q")
        if p == 5:
            o = ext_orthogonal_order(K, [(-nu) % p, 1, 1, 1])
            ok &= o == lc.o_plus_4(q)
            det.append(f"|O(Q_nu, F_25)| = {o} = 2q^2(q^2-1)^2 (plus type; the minus type would be {lc.o_minus_4(q)})")
    lc.check("B2", "over K = F_{p^2}: nu = c^2, every element of F_p a square, Q_nu of the plus type (Witt index 2)", ok, "; ".join(det))

    # B3 the isometry groups on the shell by frame counting (3:B6)
    ok = True; det = []
    for p in (5, 13, 17):
        nu = lc.nonsquares(p)[0]; s = lc.squares(p)[1] if p > 5 else lc.squares(p)[0]
        om = lc.orthogonal_order(((-nu) % p, 1, 1, 1), p); op = lc.orthogonal_order(((-s) % p, 1, 1, 1), p)
        ok &= om == lc.o_minus_4(p) and op == lc.o_plus_4(p)
        det.append(f"p={p}: |O(Q_nu)|={om} = 2p^2(p^4-1); Euclidean {op} = 2p^2(p^2-1)^2")
    lc.check("B3", "|O(Q_nu, F_p)| = 2p^2(p^4-1) (O_4^-) and |O(Euclidean)| = 2p^2(p^2-1)^2 (O_4^+) by frame counting", ok, "; ".join(det))

    # B4 the causal classes: null cone, square class, nonsquare class; sizes; invariance under isometries and rescaling (3:B7)
    ok = True; det = []
    rnd = random.Random(3)
    for p in (5, 13):
        nu = lc.nonsquares(p)[0]; coeffs = ((-nu) % p, 1, 1, 1)
        cls = {}
        for t in range(p):
            for x in range(p):
                for y in range(p):
                    for z in range(p):
                        w = lc.Q(coeffs, (t, x, y, z), p)
                        cls[(t, x, y, z)] = 0 if w == 0 else (1 if lc.is_square(w, p) else 2)
        sizes = [sum(1 for v in cls.values() if v == i) for i in range(3)]
        ok &= sizes == [p ** 3 - p * p + p, (p - 1) * (p ** 3 + p) // 2, (p - 1) * (p ** 3 + p) // 2]
        # the reflection along a non-isotropic w: v -> v - 2 B(v,w)/Q(w) w, an isometry; rescaling v -> lambda v
        B = lambda u, w: sum(a * ui * wi for a, ui, wi in zip(coeffs, u, w)) % p
        ws = [w for w in cls if cls[w] != 0]; rnd.shuffle(ws)
        for w in ws[:60]:
            qw_inv = pow(lc.Q(coeffs, w, p), -1, p)
            for v in rnd.sample(list(cls), 200):
                f = 2 * B(v, w) * qw_inv % p
                v2 = tuple((vi - f * wi) % p for vi, wi in zip(v, w))
                ok &= lc.Q(coeffs, v2, p) == lc.Q(coeffs, v, p) and cls[v2] == cls[v]
        for lam in range(1, p):
            ok &= all(cls[tuple(lam * vi % p for vi in v)] == cls[v] for v in rnd.sample(list(cls), 300))
        det.append(f"p={p}: null {sizes[0]}, square class {sizes[1]}, nonsquare class {sizes[2]}")
    lc.check("B4", "the null cone and the two non-null classes (square class of Q_nu(v)) partition F_p^4 with sizes p^3-p^2+p, (p-1)(p^3+p)/2 each; invariant under reflections and rescaling", ok, "; ".join(det))

    # B5 the anisotropic kernel and the isotropic planes (3:B5): x^2 - nu t^2 = 0 only trivially; (y, z) = (1, i) null;
    #    for nu = w^2 the (t, x) plane is hyperbolic too
    ok = True
    for p, k in lc.SHELLS:
        nu = lc.nonsquares(p)[0]; i = next(x for x in range(p) if x * x % p == p - 1)
        ok &= all((x * x - nu * t * t) % p != 0 for t in range(1, p) for x in range(p))
        ok &= (1 + i * i) % p == 0
        w = 2; s = w * w % p
        ok &= (w * w - s * 1) % p == 0 and lc.isotropic_count(((-s) % p, 1), p) == 2 * p - 1 and lc.isotropic_count(((-nu) % p, 1), p) == 1
    lc.check("B5", "x^2 - nu t^2 is anisotropic (nu nonsquare); y^2 + z^2 and x^2 - w^2 t^2 are hyperbolic planes: Witt index 1 vs 2 from the decomposition", ok)

if __name__ == "__main__":
    run(); lc.summary(write=False)
