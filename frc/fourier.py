"""frc.fourier — the shell transform on the cycle and its fractional family (the fourier theme; ledger migration, task
LM25, 5 October 2026).

The python side of `lean/FrcCore/Theme/Fourier.lean` and `lean/FrcCore/Transform.lean`: on a frame (p = 4κ + 1, g a
drive) the matrices of the cycle of n = p − 1 indices, the spectral projectors of the transform F = i W, the fractional
family F^[s] = Σ_ℓ z^(ℓs) Π_ℓ (z = g⁻¹), and the meridians. Exact integers mod p only, the standard library only (gate
G09). The first ledger to use it is the master's block file frc/ledgers/master/fourier.py.

    transform(p, g)          (W, J, F): W k j = g^(jk), J k j = [k + j ≡ 0 (mod n)], F = i W with i = −g^κ
    identity(n)              the identity matrix
    matmul(A, B, p)          the product mod p
    matpow(A, m, p)          the m-th power mod p
    projectors(p, g)         Π_ℓ = 4⁻¹ Σ_m (i⁻¹)^(ℓm) F^m, ℓ = 0..3, the powers F^m computed by multiplication
    frft(p, g, s)            F^[s] = Σ_ℓ z^(ℓs) Π_ℓ, z = g⁻¹
    meridian(p, g, kappa, m) the meridian (a g^m) for a = 0..2κ, as a list
"""


def transform(p, g):
    """The cycle's matrices for the frame (p, g): W[k][j] = g^(jk), J the reversal, F = i W with i = −g^κ."""
    n, k4 = p - 1, (p - 1) // 4
    i = (-pow(g, k4, p)) % p
    W = [[pow(g, j * k, p) for j in range(n)] for k in range(n)]
    J = [[1 if (k + j) % n == 0 else 0 for j in range(n)] for k in range(n)]
    F = [[i * W[k][j] % p for j in range(n)] for k in range(n)]
    return W, J, F


def identity(n):
    return [[1 if k == j else 0 for j in range(n)] for k in range(n)]


def matmul(A, B, p):
    n, m = len(A), len(B[0])
    Bt = list(zip(*B))
    return [[sum(a * b for a, b in zip(A[k], Bt[j])) % p for j in range(m)] for k in range(n)]


def matpow(A, m, p):
    R = identity(len(A))
    for _ in range(m): R = matmul(R, A, p)
    return R


def projectors(p, g):
    """Π_ℓ = 4⁻¹ Σ_{m<4} j^(ℓm) F^m with j = i⁻¹, the powers of F by multiplication (no closed form)."""
    n, k4 = p - 1, (p - 1) // 4
    i = (-pow(g, k4, p)) % p
    j, q = pow(i, -1, p), pow(4, -1, p)
    _, _, F = transform(p, g)
    Fm = [identity(n)]
    for _ in range(3): Fm.append(matmul(Fm[-1], F, p))
    out = []
    for l in range(4):
        out.append([[q * sum(pow(j, l * m, p) * Fm[m][k][c] for m in range(4)) % p for c in range(n)] for k in range(n)])
    return out


def frft(p, g, s, P=None):
    """F^[s] = Σ_ℓ z^(ℓs) Π_ℓ, z = g⁻¹ the refinement base."""
    n = p - 1
    z = pow(g, -1, p)
    P = P or projectors(p, g)
    return [[sum(pow(z, l * s, p) * P[l][k][c] for l in range(4)) % p for c in range(n)] for k in range(n)]


def meridian(p, g, kappa, m):
    """M_m = (a g^m mod p) for a = 0..2κ."""
    return [a * pow(g, m, p) % p for a in range(2 * kappa + 1)]


# ---- 6-fourier's ledger file (frc/ledgers/p06_fourier.py, task LM36): ranks, the shift, monomial matrices ---------------
def rank_mod(M, p):
    """The rank of the matrix M over F_p, by Gauss–Jordan elimination."""
    A = [[x % p for x in row] for row in M]
    n, m = len(A), len(A[0]) if A else 0
    r = 0
    for col in range(m):
        piv = next((i for i in range(r, n) if A[i][col]), None)
        if piv is None: continue
        A[r], A[piv] = A[piv], A[r]
        inv = pow(A[r][col], -1, p)
        A[r] = [x * inv % p for x in A[r]]
        for i in range(n):
            if i != r and A[i][col]:
                c = A[i][col]
                A[i] = [(x - c * y) % p for x, y in zip(A[i], A[r])]
        r += 1
        if r == n: break
    return r


def shift_matrix(n):
    """The exponent shift σ: (σ v)_k = v_{k−1}, as a permutation matrix."""
    return [[1 if j == (k - 1) % n else 0 for j in range(n)] for k in range(n)]


def is_monomial(M):
    """Exactly one nonzero entry in every row and every column."""
    return all(sum(1 for x in row if x) == 1 for row in M) and all(sum(1 for x in col if x) == 1 for col in zip(*M))
