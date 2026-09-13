# framed-rational status: EXACT -- integer / modular-F_p / cyclotomic arithmetic; no float in any asserted check (float, if present, only formats an exact rational for display).
"""
P3: the cell-local non-abelian SU(2) weak connection, exact over a finite field.

Gauge group  SU(2, F_q) = { M in M_2(K) : M^dagger M = I, det M = 1 },  K = F_{q^2},
the special unitary group of a Hermitian form on the spinor doublet K^2 (the same
quadratic extension that carries the weak spinor and the SU(3) colour frame).
We take q=3, K = F_9 = F_3[i] (i^2 = -1), Frobenius conjugation x -> x^3 (a+bi -> a-bi).

Verified exactly:
  A. |SU(2,3)| = 24 = q(q^2-1); the group is non-abelian; Tr M in F_3.
  B. Non-abelian gauge invariance: the plaquette holonomy transforms by conjugation
     U_box -> g U_box g^{-1} under a gauge transformation, so Tr U_box (hence the
     Wilson action) is invariant -- an EXACT finite-field identity, checked
     exhaustively over the group and on an explicit plaquette.
  C. The doublet (spinor) matter field couples covariantly.
  D. The split-torus drive breaks SU(2) by conjugation (the EW-1 mechanism).
"""
from itertools import product

# ---------------- F_9 = F_3[i], i^2 = -1 ----------------
def add(x, y): return ((x[0]+y[0]) % 3, (x[1]+y[1]) % 3)
def neg(x):    return ((-x[0]) % 3, (-x[1]) % 3)
def mul(x, y): return ((x[0]*y[0]-x[1]*y[1]) % 3, (x[0]*y[1]+x[1]*y[0]) % 3)
def conj(x):   return (x[0], (-x[1]) % 3)
ZERO, ONE = (0, 0), (1, 0)
F9 = [(a, b) for a in range(3) for b in range(3)]

# ---------------- 2x2 matrices over F_9 ----------------
def mat(a, b, c, d): return (a, b, c, d)          # [[a,b],[c,d]]
EYE = mat(ONE, ZERO, ZERO, ONE)
def mm(M, N):
    a, b, c, d = M; e, f, g, h = N
    return mat(add(mul(a, e), mul(b, g)), add(mul(a, f), mul(b, h)),
               add(mul(c, e), mul(d, g)), add(mul(c, f), mul(d, h)))
def dagger(M):
    a, b, c, d = M
    return mat(conj(a), conj(c), conj(b), conj(d))   # conjugate transpose
def det(M):
    a, b, c, d = M
    return add(mul(a, d), neg(mul(b, c)))
def tr(M):
    a, b, c, d = M
    return add(a, d)
def matvec(M, v):
    a, b, c, d = M
    return (add(mul(a, v[0]), mul(b, v[1])), add(mul(c, v[0]), mul(d, v[1])))

# ---------------- A. build SU(2,3) ----------------
SU2 = []
for a, b, c, d in product(F9, repeat=4):
    M = mat(a, b, c, d)
    if mm(dagger(M), M) == EYE and det(M) == ONE:
        SU2.append(M)
order = len(SU2)
# inverse of a unitary is its dagger
def inv(M): return dagger(M)
nonabelian = any(mm(M, N) != mm(N, M) for M in SU2 for N in SU2)
tr_in_F3 = all(tr(M)[1] == 0 for M in SU2)            # imaginary part zero
print("=" * 66)
print("P3  the finite non-abelian SU(2) weak connection   (q=3, K=F_9)")
print("=" * 66)
print(f"\n[A] |SU(2,3)| = {order}   = q(q^2-1) = {3*(9-1)}   match: {order==24}")
print(f"    non-abelian: {nonabelian}    Tr(M) in F_3 for all M: {tr_in_F3}")

# ---------------- B. non-abelian gauge invariance ----------------
# (i) trace is conjugation-invariant -- exhaustive over the group (576 pairs)
conj_inv = all(tr(mm(mm(g, M), inv(g))) == tr(M) for g in SU2 for M in SU2)
print("\n[B] non-abelian Wilson gauge invariance")
print(f"    Tr(g M g^-1) = Tr(M) for all (g,M) in SU(2,3)^2  (exhaustive): {conj_inv}")

# (ii) explicit plaquette: corners a,b,c,d ; links U_ab,U_bc,U_cd,U_da
U_ab, U_bc, U_cd, U_da = SU2[5], SU2[11], SU2[17], SU2[23]
P = mm(mm(U_ab, U_bc), mm(U_cd, U_da))               # holonomy a->b->c->d->a
ga, gb, gc, gd = SU2[3], SU2[8], SU2[14], SU2[20]    # a gauge transformation
U_ab2 = mm(mm(ga, U_ab), inv(gb))
U_bc2 = mm(mm(gb, U_bc), inv(gc))
U_cd2 = mm(mm(gc, U_cd), inv(gd))
U_da2 = mm(mm(gd, U_da), inv(ga))
P2 = mm(mm(U_ab2, U_bc2), mm(U_cd2, U_da2))
print(f"    plaquette under gauge: P' = g_a P g_a^-1 ? {P2 == mm(mm(ga, P), inv(ga))}")
print(f"    Tr P invariant: {tr(P2) == tr(P)}   (Tr P = {tr(P)} in F_9)")
print(f"    Wilson density 1 - (1/2)Tr unchanged (since Tr unchanged): {tr(P2)==tr(P)}")

# ---------------- C. doublet matter couples covariantly ----------------
# doublet psi in K^2 at each site; covariant difference (D psi)_xy = psi_y - U_xy psi_x
psi_a = (SU2[1][0], SU2[1][2]); psi_b = (SU2[2][0], SU2[2][2])
def vsub(u, w): return (add(u[0], neg(w[0])), add(u[1], neg(w[1])))
# covariant difference  (D psi)_ab = psi_a - U_ab psi_b , transforms as -> g_a (D psi)
D = vsub(psi_a, matvec(U_ab, psi_b))
psi_a2 = matvec(ga, psi_a); psi_b2 = matvec(gb, psi_b)
D2 = vsub(psi_a2, matvec(U_ab2, psi_b2))
print("\n[C] doublet (spinor) matter field")
print(f"    covariant difference transforms as D -> g_a D : {D2 == matvec(ga, D)}")

# ---------------- D. the drive breaks SU(2) by conjugation (EW-1) ----------------
# a split-torus (diagonal) drive element delta = diag(t, t^-1) in SU(2,3):
# t must satisfy norm(t)=1 (unitary) and t * t^-1 =1 (det). Pick t = i (order 4).
t = (0, 1)                                            # i in F_9, |i|^2 = i*conj(i)=i*(-i)=1
delta = mat(t, ZERO, ZERO, conj(t))                   # diag(t, t^q)=diag(i,-i), unitary, det=1
assert mm(dagger(delta), delta) == EYE and det(delta) == ONE
# does the drive commute with all of SU(2)? (no -> it breaks SU(2))
commutes_with_all = all(mm(delta, M) == mm(M, delta) for M in SU2)
centralizer = sum(1 for M in SU2 if mm(delta, M) == mm(M, delta))
print("\n[D] electroweak breaking (EW-1) inside SU(2,3)")
print(f"    drive delta = diag(i,-i) in SU(2,3); commutes with all SU(2): {commutes_with_all}")
print(f"    centraliser of the drive = {centralizer}  (< 24 => SU(2) broken to a U(1))")
print("=" * 66)
print("The non-abelian weak connection is an exact finite-group lattice gauge")
print("field; its Wilson invariance is the exact conjugation-invariance of the")
print("trace, the same construction as the SU(3) colour frame (rank 2 vs 3).")
print("=" * 66)
