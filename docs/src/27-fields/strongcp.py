# framed-rational status: EXACT -- integer / modular-F_p / cyclotomic arithmetic throughout (F_{p^2} determinants); no float, no continuum primitives.
"""Vanishing strong-CP angle on the substrate (27-fields, prop:strongcp).

Physical angle: theta-bar = theta + arg det(M_q).

(i) theta = 0: the colour action is the unique adjacency-local gauge-invariant
    quadratic functional; the topological term is not such a functional and is
    not generated (and colour is drive-invariant, so it carries no drive-selected
    orientation). Structural; not checked numerically here.

(ii) arg det(M_q) = 0: the quark mass matrices are Hermitian over the quadratic
     extension F_{p^2}/F_p (mass is the modulus-square of a Hermitian-circulant
     amplitude, generation universality). A Hermitian matrix has determinant in
     the fixed field F_p (real): det(M^dagger) = Frob(det M), and M^dagger = M
     gives det M = Frob(det M), so det M in F_p, arg det M = 0. The CKM phase
     lives in the up-down misalignment, not in det.

All arithmetic is framed-rational: integer/modular F_p and F_{p^2}, no floats,
no continuum primitives.
"""

_pass = 0
_fail = 0


def check(name, cond):
    global _pass, _fail
    cond = bool(cond)
    print(("PASS" if cond else "FAIL") + " : " + name)
    if cond:
        _pass += 1
    else:
        _fail += 1


def legendre(a, p):
    return pow(a % p, (p - 1) // 2, p)


# ---- F_{p^2} = F_p[theta], theta^2 = -3 (a non-residue for p = 2 mod 3) ----
# element = (u, v) meaning u + v*theta ; Frobenius conjugation: (u, v) -> (u, -v)
def fadd(A, B, p):
    return ((A[0] + B[0]) % p, (A[1] + B[1]) % p)


def fmul(A, B, p, d):
    a0, a1 = A
    b0, b1 = B
    return ((a0 * b0 + a1 * b1 * d) % p, (a0 * b1 + a1 * b0) % p)


def frob(A, p):
    return (A[0] % p, (-A[1]) % p)


def fconst(c, p):
    return (c % p, 0)


def det3(M, p, d):
    # Leibniz for 3x3 over F_{p^2}
    def term(i, j, k, s):
        t = fmul(M[0][i], fmul(M[1][j], M[2][k], p, d), p, d)
        return t if s > 0 else (((-t[0]) % p), ((-t[1]) % p))
    r = (0, 0)
    for (i, j, k, s) in [(0, 1, 2, 1), (1, 2, 0, 1), (2, 0, 1, 1),
                         (0, 2, 1, -1), (2, 1, 0, -1), (1, 0, 2, -1)]:
        r = fadd(r, term(i, j, k, s), p)
    return r


def hermitian(diag, upper, p):
    # build 3x3 Hermitian over F_{p^2}: diag in F_p, upper = [M01,M02,M12] in F_{p^2}
    M = [[fconst(diag[0], p), upper[0], upper[1]],
         [frob(upper[0], p), fconst(diag[1], p), upper[2]],
         [frob(upper[1], p), frob(upper[2], p), fconst(diag[2], p)]]
    return M


def commutes(A, B, p, d):
    # [A,B] = AB - BA over F_{p^2}, 3x3
    def matmul(X, Y):
        return [[
            (lambda s: s)(
                ( (lambda acc: acc)(
                    (fadd(fadd(fmul(X[i][0], Y[0][j], p, d),
                               fmul(X[i][1], Y[1][j], p, d), p),
                          fmul(X[i][2], Y[2][j], p, d), p)) )))
            for j in range(3)] for i in range(3)]
    AB = matmul(A, B)
    BA = matmul(B, A)
    return all(AB[i][j] == BA[i][j] for i in range(3) for j in range(3))


for p in (17, 53, 173, 389, 1373):
    d = (-3) % p
    assert legendre(d, p) == p - 1
    # (a) Hermitian circulant: diag equal, upper entries (b, b, b) with b in F_{p^2}
    b = (2, 1)
    Hc = hermitian([5, 5, 5], [b, frob(b, p), b], p)
    detc = det3(Hc, p, d)
    check("F_%d: Hermitian circulant det in F_p (arg det = 0)" % p, detc[1] == 0)
    # (b) Hermitian textured (non-circulant): unequal diag and distinct upper entries
    Hu = hermitian([3, 7, 11], [(1, 1), (2, 3), (4, 1)], p)
    Hd = hermitian([2, 5, 13], [(3, 2), (1, 4), (5, 2)], p)
    du = det3(Hu, p, d)
    dd = det3(Hd, p, d)
    check("F_%d: textured up/down Hermitian dets in F_p (arg det M_q = 0)" % p,
          du[1] == 0 and dd[1] == 0)
    # (c) product of the two mass matrices still has real det (theta-bar = 0)
    # det(M_u M_d) = det(M_u) det(M_d), real * real = real
    prod = fmul(du, dd, p, d)
    check("F_%d: det(M_u M_d) in F_p" % p, prod[1] == 0)
    # (d) the two textured Hermitian matrices do not commute -> CKM mixing (delta_CP) is free
    check("F_%d: [M_u, M_d] != 0 (non-trivial CKM misalignment, dets still real)" % p,
          not commutes(Hu, Hd, p, d))

print("\n%d framed-rational checks, %d passed, %d failed" % (_pass + _fail, _pass, _fail))
raise SystemExit(1 if _fail else 0)
