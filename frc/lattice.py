"""frc.lattice — difference operators, the finite Fourier shift and the Fierz–Pauli functional on the lattice
(the gravity theme; 21-gravity, 10 October 2026).

The python side of `lean/FrcCore/Theme/Lattice.lean` and of the fourier theme's `Theme/Shift.lean`, with the exact
lattice checks of 21-gravity: the central difference on the cycle and its anti-self-adjointness, the finite Fourier
shift theorem on a cycle in 𝔽_p, the discrete Fierz–Pauli functional on the periodic chart ℤ_N^d with integer fields and
its exact gauge invariance, the symbol lines of the gauge-invariant quadratic forms (spin 1: Maxwell; spin 2: Fierz–Pauli)
by exact linear algebra over the rationals, the transverse-traceless projector's rank over the rationals, the cycle
Laplacian's symbol, the spanning-tree determinant of the cycle, and the two-shift update law on an integer grid.
Exact integers, fractions and residues; the standard library only (gate G09).

    cdiff(f, n)                       the central difference (f(i+1) − f(i−1)) on the cycle of n sites
    adjoint_identity(f, g, n)         Σ (Δf) g = −Σ f (Δg)
    dft(v, zeta, p)                   the transform on the cycle against a root of unity of 𝔽_p
    shift_theorem(p, n, g, v, a)      the kick ζ^{−ax} v shifts the transform by a; the shift of v by a multiplies it by ζ^{ak}
    fp_energy(h, N, d, kind)          the integer Fierz–Pauli functional on ℤ_N^d (central or forward differences)
    gauge_shift(xi, N, d, kind)       h ↦ h + D_μ ξ_ν + D_ν ξ_μ
    symbol_nullspace(spin, samples)   the gauge-invariant coefficient lines at a symbol, exact over ℚ
    tt_rank(k)                        the rank of the transverse-traceless projector at a rational direction
    laplacian_symbol_even(p, g)       the symbol 2 − g^k − g^{−k} is even in k on the cycle of 𝔽_p^×
    tree_count(n)                     det of the reduced Laplacian of the cycle C_n (= n)
    two_shift_run(m, gradu, T)        the registered trajectory under kick and transport: Δ²q = −∇u, m cancels
"""
from fractions import Fraction
from itertools import product
import random


# ---- the cycle: the central difference and its adjoint (21:C9) ------------------------------------------------------
def cdiff(f, n):
    return [f[(i + 1) % n] - f[(i - 1) % n] for i in range(n)]


def adjoint_identity(f, g, n):
    """Σ_i (Δf)(i) g(i) = −Σ_i f(i) (Δg)(i): the central difference is anti-self-adjoint on the cycle."""
    Df, Dg = cdiff(f, n), cdiff(g, n)
    return sum(Df[i] * g[i] for i in range(n)) == -sum(f[i] * Dg[i] for i in range(n))


def forward_adjoint_identity(f, g, n):
    """Σ_i (∂f)(i) g(i) = −Σ_i f(i) (∂̄g)(i): the forward difference's adjoint is the negative backward difference."""
    Ff = [f[(i + 1) % n] - f[i] for i in range(n)]
    Bg = [g[i] - g[(i - 1) % n] for i in range(n)]
    return sum(Ff[i] * g[i] for i in range(n)) == -sum(f[i] * Bg[i] for i in range(n))


# ---- the finite Fourier shift theorem (21:C20) ------------------------------------------------------------------------
def root_of_unity(p, n, g):
    """A primitive n-th root of unity in 𝔽_p from a primitive root g, n | p − 1."""
    assert (p - 1) % n == 0
    z = pow(g, (p - 1) // n, p)
    assert pow(z, n, p) == 1 and all(pow(z, n // q, p) != 1 for q in range(2, n + 1) if n % q == 0)
    return z


def dft(v, zeta, p):
    n = len(v)
    return [sum(v[x] * pow(zeta, (x * k) % n, p) for x in range(n)) % p for k in range(n)]


def shift_theorem(p, n, g, v, a):
    """On the cycle of n sites with ζ a primitive n-th root of 𝔽_p: the kick ζ^{ax} v has transform F v (k + a); the
    shift x ↦ x − a has transform ζ^{ak} F v (k)."""
    zeta = root_of_unity(p, n, g)
    V = dft(v, zeta, p)
    kicked = [pow(zeta, (a * x) % n, p) * v[x] % p for x in range(n)]
    shifted = [v[(x - a) % n] for x in range(n)]
    K, S = dft(kicked, zeta, p), dft(shifted, zeta, p)
    return all(K[k] == V[(k + a) % n] for k in range(n)) and all(S[k] == pow(zeta, (a * k) % n, p) * V[k] % p for k in range(n))


# ---- the discrete Fierz–Pauli functional on ℤ_N^d with integer fields (21:C9) -----------------------------------------
def _sites(N, d):
    return list(product(range(N), repeat=d))


def _roll(f, mu, s, N):
    """f shifted by s along axis mu on the periodic chart: (roll f)(x) = f(x − s e_mu)."""
    out = {}
    for x, v in f.items():
        y = list(x); y[mu] = (y[mu] + s) % N
        out[tuple(y)] = v
    return out


def _diff(f, mu, N, kind):
    if kind == "central":
        a, b = _roll(f, mu, -1, N), _roll(f, mu, 1, N)
        return {x: a[x] - b[x] for x in f}
    a = _roll(f, mu, -1, N)
    return {x: a[x] - f[x] for x in f}


def fp_energy(h, N, d, kind="central", eta=None):
    """The integer Fierz–Pauli functional with the coefficients cleared to (1, −1, −2, 2):
    E = Σ_λ η_λλ [Σ D_λ h_μν D_λ h^μν − Σ D_λ h D_λ h] − 2 Σ D_μ h^μν D^λ h_λν + 2 Σ D_μ h^μν D_ν h,
    on the periodic chart ℤ_N^d with the diagonal metric η (default Minkowski (−1, 1, …))."""
    eta = eta or ([-1] + [1] * (d - 1))
    sites = _sites(N, d)
    hu = {(m, n): {x: eta[m] * eta[n] * h[(m, n)][x] for x in sites} for m in range(d) for n in range(d)}
    tr = {x: sum(eta[m] * h[(m, m)][x] for m in range(d)) for x in sites}
    E = 0
    for lam in range(d):
        for m in range(d):
            for n in range(d):
                dh, dhu = _diff(h[(m, n)], lam, N, kind), _diff(hu[(m, n)], lam, N, kind)
                E += eta[lam] * sum(dh[x] * dhu[x] for x in sites)
        dtr = _diff(tr, lam, N, kind)
        E -= eta[lam] * sum(dtr[x] * dtr[x] for x in sites)
    divu = {}
    for n in range(d):
        acc = {x: 0 for x in sites}
        for m in range(d):
            dm = _diff(hu[(m, n)], m, N, kind)
            for x in sites: acc[x] += dm[x]
        divu[n] = acc
    for n in range(d):
        divd = {x: eta[n] * divu[n][x] for x in sites}
        E -= 2 * sum(divu[n][x] * divd[x] for x in sites)
        dtrn = _diff(tr, n, N, kind)
        E += 2 * sum(divu[n][x] * dtrn[x] for x in sites)
    return E


def gauge_shift(xi, N, d, kind="central"):
    """The gauge orbit h_μν ↦ h_μν + D_μ ξ_ν + D_ν ξ_μ as the symmetric field of the shift."""
    out = {}
    for m in range(d):
        for n in range(d):
            a, b = _diff(xi[n], m, N, kind), _diff(xi[m], n, N, kind)
            out[(m, n)] = {x: a[x] + b[x] for x in a}
    return out


def random_fields(N, d, seed=7, lo=-3, hi=3):
    rng = random.Random(seed)
    sites = _sites(N, d)
    h = {}
    for m in range(d):
        for n in range(m, d):
            f = {x: rng.randint(lo, hi) for x in sites}
            h[(m, n)] = f; h[(n, m)] = f
    xi = {n: {x: rng.randint(lo, hi) for x in sites} for n in range(d)}
    return h, xi


def fp_gauge_invariant(N=4, d=4, seed=7, kind="central"):
    """E[h + gauge shift] == E[h] as an exact integer identity on random integer fields (Schwartz–Zippel)."""
    h, xi = random_fields(N, d, seed)
    g = gauge_shift(xi, N, d, kind)
    h2 = {k: {x: h[k][x] + g[k][x] for x in h[k]} for k in h}
    return fp_energy(h, N, d, kind) == fp_energy(h2, N, d, kind)


# ---- the symbol lines (21:C9; 00:E1) ------------------------------------------------------------------------------------
def _dot(eta, u, v):
    return sum(eta[i] * u[i] * v[i] for i in range(len(u)))


def _nullspace(rows):
    """The nullspace of a rational matrix (list of rows), by Gaussian elimination; a list of basis vectors."""
    rows = [[Fraction(x) for x in r] for r in rows]
    m = len(rows[0])
    piv_cols, r = [], 0
    for c in range(m):
        piv = next((i for i in range(r, len(rows)) if rows[i][c] != 0), None)
        if piv is None: continue
        rows[r], rows[piv] = rows[piv], rows[r]
        rows[r] = [v / rows[r][c] for v in rows[r]]
        for i in range(len(rows)):
            if i != r and rows[i][c] != 0:
                f = rows[i][c]; rows[i] = [a - f * b for a, b in zip(rows[i], rows[r])]
        piv_cols.append(c); r += 1
    free = [c for c in range(m) if c not in piv_cols]
    basis = []
    for fc in free:
        v = [Fraction(0)] * m; v[fc] = Fraction(1)
        for i, pc in enumerate(piv_cols): v[pc] = -rows[i][fc]
        basis.append(v)
    return basis


def symbol_nullspace(spin, samples=12, d=4, seed=5):
    """At a symbol k the gauge-invariant quadratic forms: spin 1, a₁ k² A·A + a₂ (k·A)² under A ↦ A + z k; spin 2, the four
    scalars k²⟨h,h⟩, (k·h)·(k·h), (k·h·k) tr h, k² (tr h)² under h ↦ h + kξ + ξk. The variation at random rational
    points is linear in the coefficients; its nullspace over ℚ is the invariant line (Maxwell a₁ + a₂ = 0; the
    Fierz–Pauli line (−1, 2, −2, 1))."""
    rng = random.Random(seed)
    eta = [-1] + [1] * (d - 1)
    rows = []
    for _ in range(samples):
        k = [Fraction(rng.randint(-4, 4)) for _ in range(d)]
        if spin == 1:
            A = [Fraction(rng.randint(-4, 4)) for _ in range(d)]
            z = Fraction(rng.randint(-4, 4))
            A2 = [A[i] + z * k[i] for i in range(d)]
            f = lambda V: [_dot(eta, k, k) * _dot(eta, V, V), _dot(eta, k, V) ** 2]
            rows.append([a - b for a, b in zip(f(A2), f(A))])
        else:
            h = [[Fraction(0)] * d for _ in range(d)]
            for i in range(d):
                for j in range(i, d):
                    h[i][j] = h[j][i] = Fraction(rng.randint(-4, 4))
            xi = [Fraction(rng.randint(-4, 4)) for _ in range(d)]
            h2 = [[h[i][j] + k[i] * xi[j] + k[j] * xi[i] for j in range(d)] for i in range(d)]

            def scal(H):
                k2 = _dot(eta, k, k)
                hh = sum(eta[i] * eta[j] * H[i][j] * H[i][j] for i in range(d) for j in range(d))
                kh = [sum(eta[i] * k[i] * H[i][j] for i in range(d)) for j in range(d)]
                khkh = _dot(eta, kh, kh)
                khk = sum(eta[j] * kh[j] * k[j] for j in range(d))
                tr = sum(eta[i] * H[i][i] for i in range(d))
                return [k2 * hh, khkh, khk * tr, k2 * tr * tr]
            rows.append([a - b for a, b in zip(scal(h2), scal(h))])
    return _nullspace(rows)


def fierz_pauli_line(samples=12):
    """The spin-2 nullspace is one line, the Fierz–Pauli line (−1, 2, −2, 1) up to scale; spin 1 the Maxwell line."""
    ns2 = symbol_nullspace(2, samples)
    ns1 = symbol_nullspace(1, samples)
    fp = [Fraction(-1), Fraction(2), Fraction(-2), Fraction(1)]
    ok2 = len(ns2) == 1 and any(ns2[0][i] != 0 for i in range(4)) and all(
        ns2[0][i] * fp[0] == ns2[0][0] * fp[i] for i in range(4))
    ok1 = len(ns1) == 1 and ns1[0][0] + ns1[0][1] == 0
    return ok1, ok2, ns1, ns2


# ---- the transverse-traceless projector (21:C15) ----------------------------------------------------------------------
def tt_rank(k):
    """The rank over ℚ of the TT projector Λ_ij,kl = ½(P_ik P_jl + P_il P_jk) − ½ P_ij P_kl on symmetric 3-tensors,
    P = 1 − k kᵀ/|k|² at the rational direction k: two polarisations."""
    k = [Fraction(x) for x in k]
    k2 = sum(x * x for x in k)
    P = [[Fraction(int(i == j)) - k[i] * k[j] / k2 for j in range(3)] for i in range(3)]
    idx = [(0, 0), (1, 1), (2, 2), (0, 1), (0, 2), (1, 2)]
    L = [[Fraction(1, 2) * (P[i][kk] * P[j][l] + P[i][l] * P[j][kk]) - Fraction(1, 2) * P[i][j] * P[kk][l]
          for (kk, l) in idx] for (i, j) in idx]
    return 6 - len(_nullspace(L))


# ---- the cycle Laplacian's symbol (21:C15) --------------------------------------------------------------------------------
def laplacian_symbol_even(p, g):
    """On the cycle 𝔽_p^× = ⟨g⟩ the symbol 2 − g^k − g^{−k} of the cycle Laplacian is even in k, so no O(k) cross term
    exists; and it vanishes only at k ≡ 0 when g is primitive."""
    sym = lambda k: (2 - pow(g, k % (p - 1), p) - pow(g, (-k) % (p - 1), p)) % p
    even = all(sym(k) == sym(-k) for k in range(p - 1))
    zeros = [k for k in range(p - 1) if sym(k) == 0]
    return even, zeros


# ---- the spanning-tree determinant of the cycle (21:C2's admissibility) -------------------------------------------------
def tree_count(n):
    """det of the reduced Laplacian of C_n over ℚ: τ(C_n) = n (Matrix–Tree)."""
    L = [[Fraction(0)] * n for _ in range(n)]
    for i in range(n):
        L[i][i] = Fraction(2); L[i][(i + 1) % n] -= 1; L[i][(i - 1) % n] -= 1
    M = [row[1:] for row in L[1:]]
    det = Fraction(1)
    m = n - 1
    for c in range(m):
        piv = next((r for r in range(c, m) if M[r][c] != 0), None)
        if piv is None: return Fraction(0)
        if piv != c: M[c], M[piv] = M[piv], M[c]; det = -det
        det *= M[c][c]
        M[c] = [v / M[c][c] for v in M[c]]
        for r in range(c + 1, m):
            if M[r][c] != 0:
                f = M[r][c]; M[r] = [vr - f * vc for vr, vc in zip(M[r], M[c])]
    return det


# ---- the two-shift update law on an integer grid (21:C20) ------------------------------------------------------------
def two_shift_run(m, gradu, T=40):
    """The registered trajectory under the kick k ↦ k − m∇u and the transport q ↦ q + k/m per chronon."""
    q, k, traj = 0, 0, [0]
    for _ in range(T):
        k -= m * gradu
        q += k // m
        traj.append(q)
    return traj


def two_shift_law(m=4, gradu=2, T=40):
    """Δ²q = −∇u at every interior chronon, and the trajectory is independent of m (the equivalence principle, bitwise)."""
    t = two_shift_run(m, gradu, T)
    sec = [t[i + 1] - 2 * t[i] + t[i - 1] for i in range(1, len(t) - 1)]
    return all(s == -gradu for s in sec) and two_shift_run(m, gradu, T) == two_shift_run(3 * m, gradu, T)
