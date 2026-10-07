# framed-rational status: EXACT -- integer / modular-F_p / cyclotomic arithmetic; no float in any asserted check (float, if present, only formats an exact rational for display).
"""
missing_rank.py -- develops the open residue of sec:strong / sec:matter:
the *forcing* of the rank-three colour frame ("the missing rank") and the rank tower
U(1)/SU(2)/SU(3) on ranks 1/2/3, lifted off the degenerate q=2 case (prop:su3) onto the
smallest admissible substrate residue Omega = 5, where PSU(3,5) is simple.

FRC register: every check is an exact identity in finite-field / integer arithmetic.
No RNG, no floats, no logs/trigs/integrals; framed-rational throughout (1-algebra).

Claims verified
  A. Centre tower. Z(SU(n,Omega)) = Z_{gcd(n,Omega+1)}.  With the forced residue
     Omega = 5 (mod 12), Omega+1 = 6 (mod 12), so 2|Omega+1 and 3|Omega+1.  The minimal
     Hermitian rank over K = F_{Omega^2} carrying each torsion as the full SU centre is
        n=1 -> Z_1 (phase, U(1)),  n=2 -> Z_2 (spinor/isospin),  n=3 -> Z_3 (colour).
     => rank 3 is the MINIMAL rank realising the substrate-forced Z_3 triality centre,
        which is exactly the cubic of prop:residue read inside the structure group.
  B. SU(3,5) over F_25 (the smallest admissible non-degenerate case): |SU(3,5)| = 378000
     by the orthonormal-frame counting argument (no brute force of the group); the
     3-element triality centre (norm-one cube roots of unity); exact Wilson gauge
     invariance of Tr(U_plaq) under conjugation; non-abelian self-coupling [U1,U2] != I.
  C. dim Lambda^even(C^5) = 16 = the SO(10) chiral spinor (thm:gen).
"""
from math import gcd, comb

# ----------------------------------------------------------------------
# F_25 = F_5[t]/(t^2 - 2).  Element = (a,b) ~ a + b t,  a,b in F_5.
# Frobenius conjugation x -> x^5 sends t -> -t.  Norm N(x) = x*conj(x) in F_5.
# ----------------------------------------------------------------------
P = 5
def fadd(x, y): return ((x[0]+y[0]) % P, (x[1]+y[1]) % P)
def fsub(x, y): return ((x[0]-y[0]) % P, (x[1]-y[1]) % P)
def fmul(x, y):
    a, b = x; c, d = y
    return ((a*c + 2*b*d) % P, (a*d + b*c) % P)        # t^2 = 2
def conj(x): return (x[0] % P, (-x[1]) % P)            # x -> x^5
def norm(x): return fmul(x, conj(x))[0]
ZERO, ONE = (0, 0), (1, 0)
F25 = [(a, b) for a in range(P) for b in range(P)]
def finv(x):
    ninv = pow(norm(x), P-2, P)
    c = conj(x)
    return ((c[0]*ninv) % P, (c[1]*ninv) % P)

# ---- A. centre tower / minimality of rank 3 ------------------------------------------
def centre_order(n, Omega): return gcd(n, Omega + 1)
admissible = [q for q in range(5, 200)
              if q % 12 == 5 and all(q % d for d in range(2, q) if d*d <= q)]
A_ok = all([centre_order(n, Om) for n in (1, 2, 3)] == [1, 2, 3] for Om in admissible[:8])
rank_for_3 = min(n for n in range(1, 13) if centre_order(n, 5) % 3 == 0)
rank_for_2 = min(n for n in range(1, 13) if centre_order(n, 5) % 2 == 0)
print("A. centre tower [n=1,2,3]=[1,2,3] over admissible Omega:", A_ok, " (", admissible[:8], ")")
print("   minimal rank with 3 | centre =", rank_for_3, "(colour = minimal triality carrier)")
print("   minimal rank with 2 | centre =", rank_for_2, "(isospin = minimal spinor carrier)")

# ---- B. SU(3,5) over F_25 -------------------------------------------------------------
def herm_ip(u, v):
    s = ZERO
    for ui, vi in zip(u, v):
        s = fadd(s, fmul(conj(ui), vi))
    return s
nrm = [norm(x) for x in F25]
def unit_count(m):
    if m == 1:
        return sum(1 for x in F25 if norm(x) == 1)
    if m == 2:
        return sum(1 for i in range(25) for j in range(25) if (nrm[i]+nrm[j]) % P == 1)
    if m == 3:
        c = 0
        for i in range(25):
            for j in range(25):
                target = (1 - nrm[i] - nrm[j]) % P
                c += sum(1 for k in range(25) if nrm[k] == target)
        return c
N1, N2, N3 = unit_count(1), unit_count(2), unit_count(3)
U3 = N3 * N2 * N1
SU3 = U3 // (P + 1)
print("B1. (N1,N2,N3) =", (N1, N2, N3), "-> |U(3,5)| =", U3, " |SU(3,5)| =", SU3,
      " == 378000:", SU3 == 378000)

cube_roots = [x for x in F25 if fmul(fmul(x, x), x) == ONE]
centre_unitary = [x for x in cube_roots if norm(x) == 1]
print("B2. norm-one cube roots of 1 (triality centre):", len(centre_unitary), " == 3:",
      len(centre_unitary) == 3)

def mat_dagger(M): return [[conj(M[j][i]) for j in range(3)] for i in range(3)]
def mat_mul(A, B):
    C = [[ZERO]*3 for _ in range(3)]
    for i in range(3):
        for j in range(3):
            s = ZERO
            for k in range(3):
                s = fadd(s, fmul(A[i][k], B[k][j]))
            C[i][j] = s
    return C
def is_identity(M):
    return all(M[i][j] == (ONE if i == j else ZERO) for i in range(3) for j in range(3))
def det3(M):
    a,b,c = M[0]; d,e,f = M[1]; g,h,i = M[2]
    t1 = fmul(a, fsub(fmul(e,i), fmul(f,h)))
    t2 = fmul(b, fsub(fmul(d,i), fmul(f,g)))
    t3 = fmul(c, fsub(fmul(d,h), fmul(e,g)))
    return fadd(fsub(t1, t2), t3)
def trace(M): return fadd(fadd(M[0][0], M[1][1]), M[2][2])
def scale_col(M, j, lam):
    return [[fmul(M[r][j], lam) if cc == j else M[r][cc] for cc in range(3)] for r in range(3)]
def orthonormal_basis(reverse):
    vecs3 = [(x, y, z) for x in F25 for y in F25 for z in F25]
    order = list(reversed(vecs3)) if reverse else vecs3
    cols = []
    for v in order:
        if (nrm[F25.index(v[0])] + nrm[F25.index(v[1])] + nrm[F25.index(v[2])]) % P != 1:
            continue
        if all(herm_ip(c, v) == ZERO for c in cols):
            cols.append(v)
            if len(cols) == 3:
                break
    M = [[cols[j][i] for j in range(3)] for i in range(3)]
    return scale_col(M, 2, finv(det3(M)))           # force det = 1 (norm-one scaling stays unitary)

U1, U2 = orthonormal_basis(False), orthonormal_basis(True)
unit_ok = is_identity(mat_mul(mat_dagger(U1), U1)) and is_identity(mat_mul(mat_dagger(U2), U2))
det_ok = det3(U1) == ONE and det3(U2) == ONE
Uplaq = mat_mul(mat_mul(U1, U2), mat_mul(mat_dagger(U1), mat_dagger(U2)))   # U1 U2 U1^-1 U2^-1
gi_ok = trace(mat_mul(mat_mul(U2, Uplaq), mat_dagger(U2))) == trace(Uplaq)
self_ok = not is_identity(Uplaq)
print("B3. SU(3,5) matrices unitary:", unit_ok, " det=1:", det_ok,
      " Wilson Tr gauge-invariant:", gi_ok, " non-abelian [U1,U2]!=I:", self_ok)

# ---- C. generation count -------------------------------------------------------------
dim_even = comb(5, 0) + comb(5, 2) + comb(5, 4)
print("C. dim Lambda^even(C^5) =", dim_even, " == 16:", dim_even == 16)

print("\nALL PASS:", all([A_ok, rank_for_3 == 3, rank_for_2 == 2, SU3 == 378000,
                          len(centre_unitary) == 3, unit_ok, det_ok, gi_ok, self_ok,
                          dim_even == 16]))
