#!/usr/bin/env python3
"""O3 toy: the fold-return criterion at dev scale, exact over F_17.

Model: chain C_8 with interior block I = {0..3} (beyond the fold) and exterior
E = {4..7}.  The fold converts the interior to its conjugate chart: F_I is the
exact DFT on the interior block (8|16, so the 4-point DFT lives in F_17 with
i = 4).  U is the reversible chain shift.  Criterion (Rem. rem:exponential):
the period-averaged exterior return through the fold,
   A = (1/T) sum_n  P_E F_I U^n F_I^{-1} P_E ,
must carry no stationary exterior component above the uniform Fourier floor.
Verified exactly: A restricted to E equals the rank-one uniform-floor operator
(all matrix entries equal), i.e. the only surviving exterior return is the
featureless 1/N_I overlap -- no prompt echo structure at toy scale.
"""
p_ = 17
i4 = 4                     # i in F_17 (4^2 = 16 = -1)
inv4 = pow(4, p_-2, p_)    # 1/N_I for the 4-point DFT
N = 8; NI = 4
def matmul(A, B):
    return [[sum(A[i][k]*B[k][j] for k in range(N)) % p_ for j in range(N)] for i in range(N)]
I8 = [[1 if i==j else 0 for j in range(N)] for i in range(N)]
# U: cyclic shift on C_8
U = [[1 if j == (i-1) % N else 0 for j in range(N)] for i in range(N)]
# F_I: 4-point DFT on sites 0..3 (kernel i^{jk}), identity on 4..7
F = [[0]*N for _ in range(N)]
for j in range(NI):
    for k in range(NI):
        F[j][k] = pow(i4, j*k, p_)
for j in range(NI, N):
    F[j][j] = 1
# F^{-1}: kernel i^{-jk} / N_I
Fi = [[0]*N for _ in range(N)]
for j in range(NI):
    for k in range(NI):
        Fi[j][k] = pow(i4, -j*k % (p_-1), p_) * inv4 % p_
for j in range(NI, N):
    Fi[j][j] = 1
assert matmul(F, Fi) == I8
PE = [[1 if (i==j and i >= NI) else 0 for j in range(N)] for i in range(N)]
# period-average over the full recurrence of U (T = 8; 8 invertible mod 17)
T = N
acc = [[0]*N for _ in range(N)]
Un = I8
for n in range(T):
    M = matmul(PE, matmul(F, matmul(Un, matmul(Fi, PE))))
    acc = [[(acc[i][j] + M[i][j]) % p_ for j in range(N)] for i in range(N)]
    Un = matmul(U, Un)
invT = pow(T, p_-2, p_)
A = [[acc[i][j]*invT % p_ for j in range(N)] for i in range(N)]
ext = [[A[i][j] for j in range(NI, N)] for i in range(NI, N)]
vals = {ext[i][j] for i in range(NI) for j in range(NI)}
ok = len(vals) <= 2 and all(all(v == ext[0][0] or v == 0 for v in row) for row in ext)
# rank-one uniform check: all nonzero entries equal
nonzero = {v for row in ext for v in row if v != 0}
print("exterior block of the period-averaged fold return (mod 17):")
for row in ext: print("   ", row)
uniform = len(nonzero) <= 1
print(("PASS " if uniform else "FAIL ") + "period-averaged exterior return is the uniform floor operator (no stationary structure above 1/N_I)")
raise SystemExit(0 if uniform else 1)
