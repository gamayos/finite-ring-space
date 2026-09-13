from math import gcd


def primitive_root(p):
    factors = []
    n = p - 1
    m = n
    d = 2
    while d * d <= m:
        if m % d == 0:
            factors.append(d)
            while m % d == 0:
                m //= d
        d += 1
    if m > 1:
        factors.append(m)
    for g in range(2, p):
        if all(pow(g, n // q, p) != 1 for q in factors):
            return g
    raise ValueError("no primitive root found")


def matmul(A, B, p):
    n = len(A)
    m = len(B[0])
    k = len(B)
    return [[sum(A[i][r] * B[r][j] for r in range(k)) % p for j in range(m)] for i in range(n)]


def mat_add(A, B, p):
    n, m = len(A), len(A[0])
    return [[(A[i][j] + B[i][j]) % p for j in range(m)] for i in range(n)]


def scalar_mat(A, c, p):
    n, m = len(A), len(A[0])
    return [[(A[i][j] * c) % p for j in range(m)] for i in range(n)]


def eye(n, p):
    return [[1 if i == j else 0 for j in range(n)] for i in range(n)]


def J(n, p, sign=1):
    M = [[0 for _ in range(n)] for _ in range(n)]
    for k in range(n):
        M[k][(-k) % n] = sign % p
    return M


def rank_mod_p(M, p):
    A = [row[:] for row in M]
    n, m = len(A), len(A[0])
    r, col = 0, 0
    while r < n and col < m:
        pivot = None
        for i in range(r, n):
            if A[i][col] % p != 0:
                pivot = i
                break
        if pivot is None:
            col += 1
            continue
        A[r], A[pivot] = A[pivot], A[r]
        inv = pow(A[r][col], p - 2, p)
        A[r] = [(x * inv) % p for x in A[r]]
        for i in range(n):
            if i != r and A[i][col] % p != 0:
                f = A[i][col]
                A[i] = [(A[i][j] - f * A[r][j]) % p for j in range(m)]
        r += 1
        col += 1
    return r


for p in [5, 13, 17, 29, 37, 41]:
    if p % 4 != 1:
        raise ValueError("p must satisfy p = 1 mod 4")
    t = (p - 1) // 4
    n = p - 1
    g_t = primitive_root(p)
    # Oriented quarter-turn: imaginary axis up from the unit, clockwise phase
    # rotation g_t^m, hence i_t = -g_t^t = g_t^{-t} (= g_t^{3t}).
    i_t = (-pow(g_t, t, p)) % p
    e_t = pow(g_t, i_t, p)  # exponential unit e_t = g_t^{i_t}
    W = [[pow(g_t, (j * k) % n, p) for j in range(n)] for k in range(n)]
    W2 = matmul(W, W, p)
    F = [[i_t * x % p for x in row] for row in W]
    F2 = matmul(F, F, p)
    F4 = matmul(F2, F2, p)
    # Weil parameter on the inverse generator: z_s = g_t^{-s}; z_t = i_t.
    z = pow(g_t, n - t, p)
    inv_z = pow(z, p - 2, p)
    inv_2 = pow(2, p - 2, p)
    inv_i = pow(i_t, p - 2, p)
    c = ((z + inv_z) * inv_2) % p
    d = ((z - inv_z) * inv_2 * inv_i) % p
    R_t = [[c, (-d) % p], [d, c]]

    # Multiplicity check (Lemma 4): m_l = rank Pi_l = dim ker(F - i_t^l I).
    # Pi_l = (1/4) sum_r i_t^{-l r} F^r.
    Fs = [eye(n, p), F, F2, matmul(F2, F, p)]
    inv4 = pow(4, p - 2, p)
    mults = []
    for ell in range(4):
        P = [[0] * n for _ in range(n)]
        for r in range(4):
            coef = (pow(i_t, (-ell * r) % (p - 1), p) * inv4) % p
            P = mat_add(P, scalar_mat(Fs[r], coef, p), p)
        mults.append(rank_mod_p(P, p))
    all_nonzero = all(m > 0 for m in mults)
    sum_check = mults[0] + mults[2] == 2 * t + 1 and mults[1] + mults[3] == 2 * t - 1
    # injectivity on Z_{4t}: a surviving odd projector carries a faithful
    # character (m_1 > 0 or m_3 > 0); holds for every kappa >= 1, including
    # p = 5 where exactly one odd projector survives.
    faithful = mults[1] > 0 or mults[3] > 0

    # FrFT family on the inverse generator: F^{[s]} = sum_l g_t^{-l s} Pi_l.
    Pis = []
    for ell in range(4):
        P = [[0] * n for _ in range(n)]
        for r in range(4):
            coef = (pow(i_t, (-ell * r) % (p - 1), p) * inv4) % p
            P = mat_add(P, scalar_mat(Fs[r], coef, p), p)
        Pis.append(P)

    def frft(s):
        M = [[0] * n for _ in range(n)]
        for ell in range(4):
            M = mat_add(M, scalar_mat(Pis[ell], pow(g_t, (-ell * s) % n, p), p), p)
        return M

    F3 = matmul(F2, F, p)
    cardinal_ok = (
        frft(0) == eye(n, p)
        and frft(t) == F
        and frft(2 * t) == J(n, p, 1)
        and frft(3 * t) == F3
        and frft(4 * t) == eye(n, p)
    )
    additive_ok = matmul(frft(1), frft(t - 1), p) == F

    # Meridian-scale covariance (Proposition: S_r(M_m) = M_{m+r}).
    # M_m = {a * g_t^m mod p : a in I_p}, I_p = {0, 1, ..., pi_t}.
    pi_t = (p - 1) // 2
    I_p = list(range(pi_t + 1))

    def meridian(m):
        em = pow(g_t, m % n, p)
        return frozenset((a * em) % p for a in I_p)

    # Check S_r(M_m) = M_{m+r} for several (m, r) on Z_{4t}.
    zoom_ok = all(
        frozenset((pow(g_t, r % n, p) * x) % p for x in meridian(m)) == meridian(m + r)
        for m in range(n)
        for r in range(n)
    )

    print(
        f"p={p}, t={t}, g_t={g_t}, i_t={i_t}, e_t={e_t}, "
        f"W^2=-J:{W2 == J(n, p, -1)}, "
        f"(i_t W)^2=J:{F2 == J(n, p, 1)}, "
        f"(i_t W)^4=I:{F4 == eye(n, p)}, R_t={R_t}, "
        f"cardinal:{cardinal_ok}, additive:{additive_ok}, "
        f"mults={tuple(mults)}, sym/antisym={sum_check}, faithful={faithful}, "
        f"S_r(M_m)=M_{{m+r}}:{zoom_ok}"
    )


# --- chart-sensitivity check (rem "Multiplicities are chart data") ---------
# At p=13 the frames g=2 and g=6 (same shell, same orientation class) give
# genuinely non-conjugate operators F(g) = i W(g): multiplicity tuples
# (3,3,4,2) vs (4,2,3,3), traces 4 vs 9. Registered structure (cardinal
# values, faithfulness, entropy under the frame's own readout) is invariant.
def _mult_tuple(pp, gg):
    nn = pp - 1
    tt = nn // 4
    ii = (-pow(gg, tt, pp)) % pp
    W = [[pow(gg, (j * kk) % nn, pp) for j in range(nn)] for kk in range(nn)]
    F = [[ii * x % pp for x in row] for row in W]
    def _mm(A, B):
        return [[sum(A[r][t2] * B[t2][c] for t2 in range(nn)) % pp
                 for c in range(nn)] for r in range(nn)]
    Fs = [[[1 if r == c else 0 for c in range(nn)] for r in range(nn)]]
    for _ in range(3):
        Fs.append(_mm(Fs[-1], F))
    inv4 = pow(4, pp - 2, pp)
    def _rank(M):
        A = [row[:] for row in M]
        r = 0
        for c in range(nn):
            piv = next((rr for rr in range(r, nn) if A[rr][c] % pp), None)
            if piv is None:
                continue
            A[r], A[piv] = A[piv], A[r]
            iv = pow(A[r][c], pp - 2, pp)
            A[r] = [x * iv % pp for x in A[r]]
            for rr in range(nn):
                if rr != r and A[rr][c] % pp:
                    f = A[rr][c]
                    A[rr] = [(x - f * y) % pp for x, y in zip(A[rr], A[r])]
            r += 1
        return r
    ms = []
    for l in range(4):
        P = [[0] * nn for _ in range(nn)]
        for r in range(4):
            co = (pow(ii, (4 - (l * r) % 4) % 4, pp) * inv4) % pp
            P = [[(P[a][b] + co * Fs[r][a][b]) % pp for b in range(nn)]
                 for a in range(nn)]
        ms.append(_rank(P))
    return tuple(ms)

assert _mult_tuple(13, 2) == (3, 3, 4, 2)
assert _mult_tuple(13, 6) == (4, 2, 3, 3)
print("chart-sensitivity check: F(2) mults (3,3,4,2) vs F(6) mults (4,2,3,3) at p=13 -- EXACT")


# --- multiplicity dichotomy check (thm "Multiplicity dichotomy") ------------
# G = sum g^{k^2} = eps(1+i); pattern A=(k,k,k+1,k-1) iff eps=+1,
# B=(k+1,k-1,k,k) iff eps=-1; conjugate frames carry opposite eps.
def _order(a, pp):
    o, x = 1, a % pp
    while x != 1:
        x = x * a % pp
        o += 1
    return o

def _dichotomy_check():
    for pp in (5, 13, 17, 29, 37):
        nn = pp - 1
        tt = nn // 4
        prims = [gg for gg in range(2, pp) if _order(gg, pp) == nn]
        eps = {}
        for gg in prims:
            ii = (-pow(gg, tt, pp)) % pp
            G = sum(pow(gg, (kk * kk) % nn, pp) for kk in range(nn)) % pp
            onepi = (1 + ii) % pp
            if G == onepi:
                e = 1
            elif G == (pp - onepi) % pp:
                e = -1
            else:
                raise AssertionError((pp, gg, G))
            eps[gg] = e
            want = (tt, tt, tt + 1, tt - 1) if e == 1 else (tt + 1, tt - 1, tt, tt)
            assert _mult_tuple(pp, gg) == want, (pp, gg, e)
        for gg in prims:
            assert eps[pow(gg, pp - 2, pp)] == -eps[gg], (pp, gg)
        assert sum(1 for gg in prims if eps[gg] == 1) * 2 == len(prims), pp
    print("multiplicity dichotomy: G = eps(1+i), patterns, conjugate law, even split -- "
          "EXACT on all primitive frames of p in {5,13,17,29,37}")

_dichotomy_check()
