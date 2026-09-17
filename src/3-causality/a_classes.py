"""
a_classes.py — block A: the square classes and the nonexistence theorem (3:B1, B2, B3)
======================================================================================
Section 2 of the paper: the two square classes of F_p^x with −1 a square (p ≡ 1 mod 4); no c ∈ F_p has c² = ν for a
nonsquare ν, and for c ≠ 0 every coefficient of −c²t² + x² + y² + z² is a square (thm:nonexistence, with c ≠ 0
made explicit — c = 0 gives a degenerate form); the absorption lemma by rescaling, no root of a_0 needed
(lem:square-class-absorption); the class of ν as the datum, canonically ν = g (8:B2, B3).
"""
import lcommon as lc

def run():
    # A1 the square classes, −1 a square, c² and −c² squares, no causal square root (3:B2)
    ok = True; det = []
    for p, k in lc.SHELLS:
        S, N = lc.squares(p), lc.nonsquares(p)
        ok &= len(S) == len(N) == (p - 1) // 2 and (p - 1) in S
        ok &= all(c * c % p in S and (-c * c) % p in S for c in range(1, p))
        ok &= all(c * c % p != nu for c in range(p) for nu in N)
        det.append(f"p={p}: |S|=|N|={len(S)}, -1={p-1} in S")
    lc.check("A1", "F_p^x splits into two classes of (p-1)/2; -1, c^2 and -c^2 are squares (c != 0); no c with c^2 in N", ok, "; ".join(det[:3]))

    # A2 the absorption lemma: coefficients in one class => Q = a_0 sum (w_i X_i)^2 with w_i^2 = a_i/a_0;
    #    no root of a_0 is used: a_0 in N has none, and -a_i stays in N (3:B3)
    ok = True; det = []
    for p, k in lc.SHELLS[:3]:
        S, N = lc.squares(p), lc.nonsquares(p)
        sq = {}
        for w in range(1, p): sq.setdefault(w * w % p, w)          # a square root of each square
        for cls in (S, N):
            for a0 in cls:
                for a1 in cls:
                    for a2 in cls:
                        for a3 in cls:
                            a = (a0, a1, a2, a3); inv0 = pow(a0, -1, p)
                            ws = [sq.get(ai * inv0 % p) for ai in a]
                            ok &= all(w is not None for w in ws) and all((a0 * w * w) % p == ai for w, ai in zip(ws, a))
        # u_0 with u_0^2 = a_0 exists only for a_0 in S; -a_i for a_i in N is in N again
        ok &= all(nu not in sq for nu in N) and all((-nu) % p in N for nu in N)
        det.append(f"p={p}: {len(S)**4 + len(N)**4} one-class coefficient tuples absorbed")
    lc.check("A2", "one square class => Q equivalent to a_0 (sum of squares) by w_i^2 = a_i/a_0; no root of a_0 exists for a_0 in N, and -a_i stays in N", ok, "; ".join(det))

    # A3 the class is the datum: g is a nonsquare for every primitive root; Q_nu depends on nu only through its class,
    #    Q_{nu w^2}(t, x, y, z) = Q_nu(w t, x, y, z) (3:B1)
    ok = True
    for p, k in lc.SHELLS:
        ok &= all(not lc.is_square(g, p) for g in lc.generators(p))
        nu = lc.nonsquares(p)[0]
        for w in range(1, p):
            nu2 = nu * w * w % p
            ok &= all(lc.Q((-nu2, 1, 1, 1), (t, x, y, z), p) == lc.Q((-nu, 1, 1, 1), (w * t, x, y, z), p)
                      for t in range(p) for x in range(0, p, 3) for y in (0, 1) for z in (0, 2))
    lc.check("A3", "every primitive root g is a nonsquare (nu = g canonical); Q_nu depends on nu only through its class", ok)

    # A4 c in F_p^x gives a Euclidean form; c = 0 a degenerate one (3:B2)
    ok = True
    for p, k in lc.SHELLS[:4]:
        for c in range(1, p):
            coeffs = ((-c * c) % p, 1, 1, 1)
            ok &= all(lc.is_square(a, p) for a in coeffs)
            ok &= lc.isotropic_count(coeffs, p) == p ** 3 + p * p - p        # hyperbolic count: the Euclidean type
        ok &= lc.isotropic_count((0, 1, 1, 1), p) != p ** 3 + p * p - p        # c = 0: degenerate, not of either type
    lc.check("A4", "-c^2 t^2 + x^2 + y^2 + z^2 (c != 0) has p^3 + p^2 - p zeros: the Euclidean (hyperbolic) type; c = 0 degenerate", ok)

if __name__ == "__main__":
    run(); lc.summary(write=False)
