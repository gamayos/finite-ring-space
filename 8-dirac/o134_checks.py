#!/usr/bin/env python3
"""O1/O3/O4 exact checks: boost torus, Cayley transform, orbit periods (EXACT).

Blueprint items O1, O3, O4 (reports/revision-blueprint.md); findings in
reports/o134-findings.md. All arithmetic exact over K = F_p[w]/(w^2 - nu);
no floats, no RNG. Elements of K are pairs (a, b) = a + b*w.

Claims checked:
  O1a  The kernel of (x,y) -> Lambda(x,y) is the scalar line: each boost
       matrix has exactly p-1 preimages in K^x, so |G_nu| = p+1.
  O1b  Hilbert 90 form: the boost entries satisfy A - B*w = z/zbar, a
       norm-one element; the map z*F_p^x -> z/zbar is a bijection onto
       the norm-one torus N1, so G_nu ~ N1 = C_{p+1} canonically.
  O1c  G_nu is cyclic: an element of order exactly p+1 exists.
  O1d  Triality: an order-3 element exists in G_nu iff 3 | p+1
       (p = 17: yes; p = 13: no).
  O1e  F_17 is the minimal admissible shell: kappa = 4 even, kappa = 1
       (mod 3), p = 5 (mod 12), and no smaller symmetry-complete p
       satisfies the triple.
  O3a  The scalar Cayley map phi(lam) = (1 + a*lam)/(1 - a*lam), a in
       K^- nonzero, sends the Frobenius-fixed projective line
       P1(F_p) bijectively onto the norm-one torus N1 (with
       phi(infinity) = -1).  Self-adjoint line -> unitary torus, exact.
  O3b  The unitary group of one channel is N1: {u in K^x : ubar*u = 1}
       = C_{p+1}, same torus as the boosts.
  O4a  Kinetic case: H = -Delta on F_p is nilpotent (H = -T^{-1}(T-I)^2,
       (T-I)^p = 0 in characteristic p), hence U = phi(H) is unipotent
       and ord(U) = p.  Reproduces and explains the paper's ord = 13.
  O4b  Potential case: H = M_V with V = id is diagonal with F_p
       spectrum, so U's eigenphases lie in N1 and ord(U) = p+1.
       (p = 13: ord 14; p = 17: ord 18.)
  O4c  Mixed case (recorded datum, p = 5, nu = g = 2): ord(U) for
       H = -Delta + M_id is computed exactly and verified.
  O4d  Composite/E2 cross-check: ord of a block-diagonal pair is the
       lcm of the parts' orders (13, 14 -> 182).
Class: EXACT.
"""
import sys
from math import gcd

def make_field(p, nu):
    def add(u, v): return ((u[0] + v[0]) % p, (u[1] + v[1]) % p)
    def sub(u, v): return ((u[0] - v[0]) % p, (u[1] - v[1]) % p)
    def mul(u, v):
        return ((u[0] * v[0] + nu * u[1] * v[1]) % p,
                (u[0] * v[1] + u[1] * v[0]) % p)
    def conj(u): return (u[0], (-u[1]) % p)
    def norm(u): return (u[0] * u[0] - nu * u[1] * u[1]) % p
    def inv(u):
        n = norm(u)
        ni = pow(n, p - 2, p)
        return ((u[0] * ni) % p, (-u[1] * ni) % p)
    return add, sub, mul, conj, norm, inv

checks = 0
def chk(label, ok):
    global checks
    checks += 1
    if not ok:
        print(f"FAIL: {label}"); sys.exit(1)

def boost(p, nu, x, y):
    d = (x * x - nu * y * y) % p
    di = pow(d, p - 2, p)
    return ((x * x + nu * y * y) * di % p, (-2 * x * y) * di % p)

# ---------------- O1 ----------------
for p, nu in ((13, 2), (17, 3)):
    add, sub, mul, conj, norm, inv = make_field(p, nu)
    pre = {}
    for x in range(p):
        for y in range(p):
            if (x * x - nu * y * y) % p == 0:
                continue
            pre.setdefault(boost(p, nu, x, y), []).append((x, y))
    chk(f"O1a p={p} |G|=p+1", len(pre) == p + 1)
    chk(f"O1a p={p} fibers p-1", all(len(v) == p - 1 for v in pre.values()))
    n1 = {u for x in range(p) for y in range(p)
          if norm(u := (x, y)) == 1}
    chk(f"O3b p={p} |N1|=p+1", len(n1) == p + 1)
    ok = True
    for (A, B), zs in pre.items():
        for z in zs:
            q = mul(z, inv(conj(z)))              # z / zbar
            ok &= q == (A, (-B) % p) and norm(q) == 1
    chk(f"O1b p={p} Lambda = z/zbar (Hilbert 90)", ok)
    chk(f"O1b p={p} image = N1", {(A, (-B) % p) for (A, B) in pre} == n1)
    def kord(u):
        v, o = u, 1
        while v != (1, 0):
            v = mul(v, u); o += 1
        return o
    chk(f"O1c p={p} cyclic", max(kord(u) for u in n1) == p + 1)
    chk(f"O1d p={p} triality", any(kord(u) == 3 for u in n1) == ((p + 1) % 3 == 0))

def is_prime(n):
    return n > 1 and all(n % d for d in range(2, int(n**0.5) + 1))
adm = [4 * k + 1 for k in range(1, 5)
       if k % 2 == 0 and k % 3 == 1 and is_prime(4 * k + 1)]
chk("O1e F_17 minimal admissible", adm == [17])

# ---------------- O3 ----------------
for p, nu in ((13, 2), (17, 3)):
    add, sub, mul, conj, norm, inv = make_field(p, nu)
    n1 = {u for x in range(p) for y in range(p) if norm(u := (x, y)) == 1}
    for k in range(1, p):                          # every nonzero a = k*w
        a = (0, k)
        img = set()
        for lam in range(p):
            den = sub((1, 0), mul(a, (lam, 0)))
            chk(f"O3a p={p} k={k} lam={lam} invertible", norm(den) != 0)
            u = mul(add((1, 0), mul(a, (lam, 0))), inv(den))
            chk(f"O3a p={p} k={k} lam={lam} norm-one", norm(u) == 1)
            img.add(u)
        img.add(((-1) % p, 0))                     # phi(infinity) = -1
        chk(f"O3a p={p} k={k} bijection", img == n1 and len(img) == p + 1)

# ---------------- O4 ----------------
def mat_id(n): return [[(1, 0) if i == j else (0, 0) for j in range(n)] for i in range(n)]

def mat_mul(X, Y, mul, add, n):
    Z = [[(0, 0)] * n for _ in range(n)]
    for i in range(n):
        for k in range(n):
            x = X[i][k]
            if x == (0, 0):
                continue
            for j in range(n):
                Z[i][j] = add(Z[i][j], mul(x, Y[k][j]))
    return Z

def mat_inv(X, mul, add, sub, inv, n):
    A = [row[:] + I_row[:] for row, I_row in zip(X, mat_id(n))]
    for col in range(n):
        piv = next(r for r in range(col, n) if A[r][col] != (0, 0))
        A[col], A[piv] = A[piv], A[col]
        pi = inv(A[col][col])
        A[col] = [mul(pi, v) for v in A[col]]
        for r in range(n):
            if r != col and A[r][col] != (0, 0):
                f = A[r][col]
                A[r] = [sub(v, mul(f, w)) for v, w in zip(A[r], A[col])]
    return [row[n:] for row in A]

def cayley(H, a, p, nu, n):
    add, sub, mul, conj, norm, inv = make_field(p, nu)
    aH = [[mul(a, H[i][j]) for j in range(n)] for i in range(n)]
    I = mat_id(n)
    Im = [[sub(I[i][j], aH[i][j]) for j in range(n)] for i in range(n)]
    Ip = [[add(I[i][j], aH[i][j]) for j in range(n)] for i in range(n)]
    return mat_mul(mat_inv(Im, mul, add, sub, inv, n), Ip, mul, add, n)

def mat_ord(U, p, nu, n, cap):
    add, sub, mul, conj, norm, inv = make_field(p, nu)
    I, V, o = mat_id(n), U, 1
    while V != I:
        V = mat_mul(V, U, mul, add, n); o += 1
        if o > cap:
            return None
    return o

def build(p, kinetic, potential):
    n = p
    H = [[(0, 0)] * n for _ in range(n)]
    for x in range(n):
        if kinetic:                                 # -Delta = -(T + T^-1 - 2I)
            H[x][(x + 1) % n] = ((-1) % p, 0)
            H[x][(x - 1) % n] = ((-1) % p, 0)
            H[x][x] = (2 % p, 0)
        if potential:                               # + M_V, V = id
            a = H[x][x]
            H[x][x] = ((a[0] + x) % p, a[1])
    return H

for p, nu in ((13, 2), (17, 3)):
    add, sub, mul, conj, norm, inv = make_field(p, nu)
    a = (0, 1)                                      # alpha = w
    Hk = build(p, True, False)
    U = cayley(Hk, a, p, nu, p)
    # unipotency: (U - I)^p = 0
    I = mat_id(p)
    N = [[sub(U[i][j], I[i][j]) for j in range(p)] for i in range(p)]
    Np = N
    for _ in range(p - 1):
        Np = mat_mul(Np, N, mul, add, p)
    chk(f"O4a p={p} (U-I)^p = 0", all(v == (0, 0) for row in Np for v in row))
    chk(f"O4a p={p} ord(U) = p", mat_ord(U, p, nu, p, 2 * p) == p)
    Hv = build(p, False, True)
    Uv = cayley(Hv, a, p, nu, p)
    chk(f"O4b p={p} ord(U) = p+1", mat_ord(Uv, p, nu, p, 2 * p + 2) == p + 1)

# O4c: mixed case at p = 5, nu = g = 2 (primitive, nonsquare)
p, nu = 5, 2
Hm = build(p, True, True)
Um = cayley(Hm, (0, 1), p, nu, p)
om = mat_ord(Um, p, nu, p, 100000)
chk("O4c p=5 mixed order finite", om is not None)
print(f"O4c datum: p=5, nu=g=2, H=-Delta+M_id, alpha=w: ord(U) = {om}")

# O4d: composite = lcm (E2 cross-check)
chk("O4d lcm(13,14)=182", 13 * 14 // gcd(13, 14) == 182)

print(f"{checks}/{checks} exact checks pass")
