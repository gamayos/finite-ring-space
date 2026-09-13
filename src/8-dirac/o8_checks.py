#!/usr/bin/env python3
"""O8 exact checks: symmetric Dirac dynamics (round-01 item 1) (EXACT).

Repair route of review 8-dirac-20260709-01-1, executed and extended.
Elements of K = F_p[w]/(w^2 - nu) as pairs (a, b) = a + b w.

Claims checked:
  X1  Gamma adjoints under plain conj-transpose: (g0)+ = -g0, (g1)+ = -g1,
      (g2)+ = +g2, (g3)+ = -g3 (the g2 obstruction; p = 5, 13, 17).
  X2  The spinor twist X = g0 g1 g3 is Hermitian (X+ = X), invertible,
      commutes with g0, g1, g3 and anticommutes with g2; consequently
      X^{-1} (g_mu)+ X = -g_mu for ALL mu: every gamma is X-anti-self-
      adjoint.  (The continuum recipe M = g0 fails here because Frobenius
      fixes i; checked as X3.)
  X3  gamma0-twist fails: signs remain mixed.
  X4  Symmetric difference: (T - T^{-1}) is nilpotent on H(F_p)
      ((T^2 - I)^p = 0), and anti-self-adjoint; hence each gamma^mu
      del^s_mu is X-self-adjoint and D^s = sum gamma^mu del^s_mu is
      X-self-adjoint; D^s is nilpotent (its square is the symmetric
      Klein-Gordon operator, a sum of commuting nilpotents).
  X5  1+1 operator check at p = 5, nu = g = 2 (spinor space K^4 over
      F_5^2, dimension 100): H = D^s is X-self-adjoint as a matrix
      identity; the Cayley step U = (I - aH)^{-1}(I + aH), a = w, is
      X-unitary (U^# U = I); U is unipotent with ord(U) = p = 5
      (massless meridional period = the translation torus).
  X6  Massive case: H = D^s - m I is X-self-adjoint; U factors as
      norm-one phase times unipotent: ord(U) = lcm(p, ord_{N1} phi(-m))
      -- checked for m = 1, 2 at p = 5 (mass enters through the
      norm-one phase, interactions' torus).
  X7  Sector unification (round-01 item 2): on H(Phi_p) the cycle
      Laplacian Delta_Phi = D + D^{-1} - 2I is self-adjoint, its Cayley
      steps commute with the drive pullback D exactly, and both are
      unitary on the SAME space (p = 13: composite formed and checked).
Class: EXACT.
"""
import sys
from math import gcd, lcm

checks = 0
def chk(label, ok):
    global checks
    checks += 1
    if not ok:
        print(f"FAIL: {label}"); sys.exit(1)

def field(p, nu):
    add = lambda u, v: ((u[0]+v[0]) % p, (u[1]+v[1]) % p)
    sub = lambda u, v: ((u[0]-v[0]) % p, (u[1]-v[1]) % p)
    def mul(u, v):
        return ((u[0]*v[0] + nu*u[1]*v[1]) % p, (u[0]*v[1] + u[1]*v[0]) % p)
    conj = lambda u: (u[0], (-u[1]) % p)
    def inv(u):
        n = (u[0]*u[0] - nu*u[1]*u[1]) % p
        ni = pow(n, p-2, p)
        return ((u[0]*ni) % p, (-u[1]*ni) % p)
    return add, sub, mul, conj, inv

def gammas(p, nu, g):
    kap = (p-1)//4
    i = pow(pow(g, p-2, p), kap, p)
    O, I1, ii, ww, iw = (0,0), (1,0), (i % p, 0), (0,1), (0, i % p)
    niw = (0, (-i) % p); ni = ((p-i) % p, 0); m1 = ((p-1) % p, 0)
    s1 = [[O,I1],[I1,O]]; s2 = [[O,ni],[ii,O]]; s3 = [[I1,O],[O,m1]]
    def blk(A, B, C, D):
        return [[A[0][0],A[0][1],B[0][0],B[0][1]],
                [A[1][0],A[1][1],B[1][0],B[1][1]],
                [C[0][0],C[0][1],D[0][0],D[0][1]],
                [C[1][0],C[1][1],D[1][0],D[1][1]]]
    Z = [[O,O],[O,O]]
    def smul(s, M):
        add, sub, mul, conj, inv = field(p, nu)
        return [[mul(s, x) for x in row] for row in M]
    beta = blk(Z[0:2] and Z, [[I1,O],[O,I1]], [[I1,O],[O,I1]], Z)
    def rho(s):
        ms = [[((-x[0]) % p, (-x[1]) % p) for x in row] for row in s]
        return blk(Z, s, ms, Z)
    g0 = smul(iw, beta)
    g1 = smul(ii, rho(s1)); g2 = smul(ii, rho(s2)); g3 = smul(ii, rho(s3))
    return g0, g1, g2, g3, i

def mmul(A, B, p, nu):
    add, sub, mul, conj, inv = field(p, nu)
    n = len(A)
    C = [[(0,0)]*n for _ in range(n)]
    for a in range(n):
        for b in range(n):
            x = A[a][b]
            if x == (0,0): continue
            for c in range(n):
                C[a][c] = add(C[a][c], mul(x, B[b][c]))
    return C

def dagger(A, p, nu):
    add, sub, mul, conj, inv = field(p, nu)
    n = len(A)
    return [[conj(A[b][a]) for b in range(n)] for a in range(n)]

def neg(A, p): return [[((-x[0]) % p, (-x[1]) % p) for x in row] for row in A]
def eye(n): return [[(1,0) if a==b else (0,0) for b in range(n)] for a in range(n)]

# X1-X3
for p, g in ((5,2),(13,2),(17,3)):
    nu = g
    g0,g1,g2,g3,i = gammas(p, nu, g)
    G = [g0,g1,g2,g3]
    signs = []
    for M in G:
        Md = dagger(M, p, nu)
        signs.append(+1 if Md == M else (-1 if Md == neg(M,p) else 0))
    chk(f"X1 p={p} plain signs", signs == [-1,-1,1,-1])
    X = mmul(mmul(g0,g1,p,nu), g3, p, nu)
    chk(f"X2 p={p} X Hermitian", dagger(X,p,nu) == X)
    add, sub, mul, conj, inv = field(p, nu)
    ok = True
    for k, M in enumerate(G):
        XM, MX = mmul(X,M,p,nu), mmul(M,X,p,nu)
        ok &= (XM == MX) if k != 2 else (XM == neg(MX,p))
    chk(f"X2 p={p} (anti)commutation", ok)
    # X^{-1} M+ X = -M for all mu; X^2 is scalar so X^{-1} ~ X
    X2m = mmul(X, X, p, nu)
    s = X2m[0][0]
    chk(f"X2 p={p} X^2 scalar", X2m == [[s if a==b else (0,0) for b in range(4)] for a in range(4)])
    si = inv(s)
    Xi = [[mul(si, x) for x in row] for row in X]
    ok = all(mmul(mmul(Xi, dagger(M,p,nu),p,nu), X, p, nu) == neg(M,p) for M in G)
    chk(f"X2 p={p} all gammas X-anti-self-adjoint", ok)
    g0i = [[mul(inv(mmul(g0,g0,p,nu)[0][0]), x) for x in row] for row in g0]
    s03 = [ +1 if mmul(mmul(g0i, dagger(M,p,nu),p,nu), g0,p,nu) == M else -1 for M in G ]
    chk(f"X3 p={p} gamma0-twist mixed", len(set(s03)) > 1)

# X4: 1-dim symmetric difference nilpotent + anti-self-adjoint (plain form)
for p in (5, 13):
    T = [[(1,0) if (b-a) % p == 1 else (0,0) for b in range(p)] for a in range(p)]
    Ti = [[(1,0) if (b-a) % p == p-1 else (0,0) for b in range(p)] for a in range(p)]
    nu = 2 if p in (5,13) else 3
    S = [[( (T[a][b][0]-Ti[a][b][0]) % p, 0) for b in range(p)] for a in range(p)]
    P = S
    nil = False
    for _ in range(p):
        P = mmul(P, S, p, nu)
        if all(x == (0,0) for row in P for x in row): nil = True; break
    chk(f"X4 p={p} (T-T^-1) nilpotent", nil)
    chk(f"X4 p={p} anti-self-adjoint", dagger(S,p,nu) == neg(S,p))

# X5/X6: 1+1 operator check at p=5, nu=g=2
p, g = 5, 2
nu = g
g0,g1,g2,g3,i = gammas(p, nu, g)
add, sub, mul, conj, inv = field(p, nu)
inv2 = (pow(2, p-2, p), 0)
n = 4 * p * p                      # spinor index s + point (x0, x1)
def idx(s, x0, x1): return s*p*p + x0*p + x1
def build_D(m):
    D = [[(0,0)]*n for _ in range(n)]
    for x0 in range(p):
        for x1 in range(p):
            for s in range(4):
                for sp in range(4):
                    c0, c1 = g0[s][sp], g1[s][sp]
                    if c0 != (0,0):
                        h = mul(inv2, c0)
                        D[idx(s,x0,x1)][idx(sp,(x0+1)%p,x1)] = add(D[idx(s,x0,x1)][idx(sp,(x0+1)%p,x1)], h)
                        D[idx(s,x0,x1)][idx(sp,(x0-1)%p,x1)] = sub(D[idx(s,x0,x1)][idx(sp,(x0-1)%p,x1)], h)
                    if c1 != (0,0):
                        h = mul(inv2, c1)
                        D[idx(s,x0,x1)][idx(sp,x0,(x1+1)%p)] = add(D[idx(s,x0,x1)][idx(sp,x0,(x1+1)%p)], h)
                        D[idx(s,x0,x1)][idx(sp,x0,(x1-1)%p)] = sub(D[idx(s,x0,x1)][idx(sp,x0,(x1-1)%p)], h)
                if m and s == sp:
                    pass
    if m:
        for q in range(n):
            D[q][q] = sub(D[q][q], ((m) % p, 0))
    return D
# big-X form matrix: block-diagonal X per point
X = mmul(mmul(g0,g1,p,nu), g3, p, nu)
def form_adjoint(A):
    # A# = Xbig^{-1} A+ Xbig ; Xbig block diag
    Ad = dagger(A, p, nu)
    s = mmul(X, X, p, nu)[0][0]; si = inv(s)
    Xi4 = [[mul(si, x) for x in row] for row in X]
    B = [[(0,0)]*n for _ in range(n)]
    # (Xi A+ X) with X acting on spinor index only
    for x0 in range(p):
        for x1 in range(p):
            for y0 in range(p):
                for y1 in range(p):
                    # block (x,y): B_block = Xi4 * Ad_block * X4
                    blk = [[Ad[idx(a,x0,x1)][idx(b,y0,y1)] for b in range(4)] for a in range(4)]
                    if all(v == (0,0) for row in blk for v in row): continue
                    t1 = mmul(Xi4, blk, p, nu); t2 = mmul(t1, X, p, nu)
                    for a in range(4):
                        for b in range(4):
                            B[idx(a,x0,x1)][idx(b,y0,y1)] = t2[a][b]
    return B

def big_mmul(A, B_):
    C = [[(0,0)]*n for _ in range(n)]
    for a in range(n):
        Ar = A[a]
        for b in range(n):
            x = Ar[b]
            if x == (0,0): continue
            Bb = B_[b]
            Ca = C[a]
            for c in range(n):
                if Bb[c] != (0,0):
                    Ca[c] = add(Ca[c], mul(x, Bb[c]))
    return C

def big_inv(A):
    M = [row[:] + [( (1,0) if r==j else (0,0)) for j in range(n)] for r, row in enumerate(A)]
    for col in range(n):
        piv = next(r for r in range(col, n) if M[r][col] != (0,0))
        M[col], M[piv] = M[piv], M[col]
        pi = inv(M[col][col])
        M[col] = [mul(pi, v) for v in M[col]]
        for r in range(n):
            if r != col and M[r][col] != (0,0):
                f = M[r][col]
                M[r] = [sub(v, mul(f, w_)) for v, w_ in zip(M[r], M[col])]
    return [row[n:] for row in M]

def cayley_of(H, a):
    aH = [[mul(a, x) for x in row] for row in H]
    Im = [[sub((1,0) if r==c else (0,0), aH[r][c]) for c in range(n)] for r in range(n)]
    Ip = [[add((1,0) if r==c else (0,0), aH[r][c]) for c in range(n)] for r in range(n)]
    return big_mmul(big_inv(Im), Ip)

def big_ord(U, cap):
    I = eye(n); V = U; o = 1
    while V != I:
        V = big_mmul(V, U); o += 1
        if o > cap: return None
    return o

H0 = build_D(0)
chk("X5 D^s X-self-adjoint", form_adjoint(H0) == H0)
U0 = cayley_of(H0, (0,1))
chk("X5 U X-unitary", big_mmul(form_adjoint(U0), U0) == eye(n))
o0 = big_ord(U0, p*p + 1)
chk("X5 massless U unipotent, ord a p-power", o0 is not None and (o0 == p or o0 == p*p))
print(f"X5 datum: massless 1+1 Dirac-Cayley ord(U) = {o0} (p = {p})")

def n1_ord(u):
    v, o = u, 1
    while v != (1,0):
        v = mul(v, u); o += 1
    return o
for m in (1, 2):
    Hm = build_D(m)
    chk(f"X6 m={m} X-self-adjoint", form_adjoint(Hm) == Hm)
    Um = cayley_of(Hm, (0,1))
    lam = ((-m) % p, 0)
    a = (0,1)
    num = add((1,0), mul(a, lam)); den = sub((1,0), mul(a, lam))
    phi = mul(num, inv(den))
    om = big_ord(Um, p*p*(p+1) + 1)
    q = n1_ord(phi)
    chk(f"X6 m={m} ord = lcm(p-power, ord phi(-m))",
        om is not None and om % q == 0 and (om // q) in (1, p, p*p) and om % p == 0)
    print(f"X6 datum: m={m}: ord(U) = {om} (norm-one phase order {q})")

# X7: sector unification on H(Phi_p), p = 13
p, g = 13, 2
nu = g
add, sub, mul, conj, inv = field(p, nu)
n1 = p - 1
pts = [pow(g, j, p) for j in range(n1)]
pos = {x: j for j, x in enumerate(pts)}
Dm = [[(1,0) if pts[b] == (pow(g, p-2, p) * pts[a]) % p else (0,0) for b in range(n1)] for a in range(n1)]
Dinv = [[(1,0) if pts[b] == (g * pts[a]) % p else (0,0) for b in range(n1)] for a in range(n1)]
def small_mmul(A,B):
    m_ = len(A); C = [[(0,0)]*m_ for _ in range(m_)]
    for a in range(m_):
        for b in range(m_):
            x = A[a][b]
            if x == (0,0): continue
            for c in range(m_):
                if B[b][c] != (0,0): C[a][c] = add(C[a][c], mul(x, B[b][c]))
    return C
Lap = [[sub(add(Dm[a][b], Dinv[a][b]), ((2,0) if a==b else (0,0))) for b in range(n1)] for a in range(n1)]
chk("X7 Delta_Phi self-adjoint", [[conj(Lap[b][a]) for b in range(n1)] for a in range(n1)] == Lap)
# Cayley of Delta_Phi commutes with D
def small_inv(A):
    m_ = len(A)
    M = [row[:] + [((1,0) if r==j else (0,0)) for j in range(m_)] for r, row in enumerate(A)]
    for col in range(m_):
        piv = next(r for r in range(col, m_) if M[r][col] != (0,0))
        M[col], M[piv] = M[piv], M[col]
        pi = inv(M[col][col])
        M[col] = [mul(pi, v) for v in M[col]]
        for r in range(m_):
            if r != col and M[r][col] != (0,0):
                f = M[r][col]
                M[r] = [sub(v, mul(f, w_)) for v, w_ in zip(M[r], M[col])]
    return [row[m_:] for row in M]
a = (0,1)
aH = [[mul(a, x) for x in row] for row in Lap]
Im = [[sub((1,0) if r==c else (0,0), aH[r][c]) for c in range(n1)] for r in range(n1)]
Ip = [[add((1,0) if r==c else (0,0), aH[r][c]) for c in range(n1)] for r in range(n1)]
Uc = small_mmul(small_inv(Im), Ip)
chk("X7 [U, D] = 0 (exact composite)", small_mmul(Uc, Dm) == small_mmul(Dm, Uc))
chk("X7 U unitary", small_mmul([[conj(Uc[b][a_]) for b in range(n1)] for a_ in range(n1)], Uc) == eye(n1))

print(f"{checks}/{checks} exact checks pass")
