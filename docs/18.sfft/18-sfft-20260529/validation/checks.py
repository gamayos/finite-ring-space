"""
Exact checks for "Streaming Evaluation of Fractional Fourier Orbits over Prime Fields".
Integer arithmetic only; no floating point anywhere. Python >= 3.8.

Conventions (as in the paper): p = 4k+1 prime, n = p-1, g a primitive root,
i = g^{-k} (so i^2 = -1), W_{k,j} = g^{jk}, F = iW, Pi_l = (1/4) sum_r i^{-lr} F^r,
F^{[s]} = sum_l g^{-ls} Pi_l.

Sections:
  A  operator identities (W^2=-J, F^2=J, F^4=I, projectors, cardinal values)
  B  orbit identity and the one-transform setup lemma
  C  Algorithms A and B reproduce the direct orbit (B with halving, g = 2)
  D  Theorem C: kappa odd; Fermat separation; the primitive-root criterion;
     the prime-capacity family; the +-2^{+-1} equivalence and the one-directional
     Lemma 4.6 for k = +-1, +-3, +-5; Prop 4.7 enumeration; density
  E  halving primitive; worked example at p = 13; operation counts
"""
import random, sys

def is_prime(m):
    if m < 2: return False
    if m % 2 == 0: return m == 2
    d = 3
    while d * d <= m:
        if m % d == 0: return False
        d += 2
    return True

def factor(m):
    f = {}; d = 2
    while d * d <= m:
        while m % d == 0: f[d] = f.get(d, 0) + 1; m //= d
        d += 1
    if m > 1: f[m] = f.get(m, 0) + 1
    return f

def order(a, p):
    n = p - 1; o = n
    for q in factor(n):
        while o % q == 0 and pow(a, o // q, p) == 1: o //= q
    return o

def primitive_roots(p):
    return [g for g in range(2, p) if order(g, p) == p - 1]

def least_primitive_root(p):
    return primitive_roots(p)[0]

def primes(lo, hi):
    return [q for q in range(lo, hi) if is_prime(q)]

def matmul(A, B, p):
    n = len(A); Bt = list(zip(*B))
    return [[sum(a * b for a, b in zip(row, col)) % p for col in Bt] for row in A]

def matvec(A, v, p):
    return [sum(a * b for a, b in zip(row, v)) % p for row in A]

def setup(p, g):
    n = p - 1; k = n // 4
    i = pow(g, -k, p)
    W = [[pow(g, (j * kk) % n, p) for j in range(n)] for kk in range(n)]
    F = [[(i * x) % p for x in row] for row in W]
    return n, k, i, W, F

def J(v):
    n = len(v); return [v[(-kk) % n] for kk in range(n)]

def projections_direct(p, g, v):
    """u_l = Pi_l v computed from F^r v, r = 0..3, by repeated matvec."""
    n, k, i, W, F = setup(p, g)
    Fr = [v]
    for r in range(1, 4): Fr.append(matvec(F, Fr[-1], p))
    inv4 = pow(4, -1, p); ii = pow(i, -1, p)
    return [[(inv4 * sum(pow(ii, l * r, p) * Fr[r][j] for r in range(4))) % p for j in range(n)] for l in range(4)]

def projections_one_transform(p, g, v):
    """Lemma (setup): one product Wv, two reversals, 5n multiplications, 8n additions."""
    n, k, i, W, F = setup(p, g)
    Wv = matvec(W, v, p); Jv = J(v); JWv = J(Wv)
    inv4 = pow(4, -1, p)
    a = [(x + y) % p for x, y in zip(v, Jv)]
    b = [(x - y) % p for x, y in zip(v, Jv)]
    c = [(x + y) % p for x, y in zip(Wv, JWv)]
    d = [(x - y) % p for x, y in zip(Wv, JWv)]
    ic = [(i * x) % p for x in c]
    u0 = [(inv4 * (x + y)) % p for x, y in zip(a, ic)]
    u2 = [(inv4 * (x - y)) % p for x, y in zip(a, ic)]
    u1 = [(inv4 * (x + y)) % p for x, y in zip(b, d)]
    u3 = [(inv4 * (x - y)) % p for x, y in zip(b, d)]
    return [u0, u1, u2, u3]

def orbit_direct(p, g, v):
    n, k, i, W, F = setup(p, g)
    u = projections_direct(p, g, v)
    return [[(u[0][j] + pow(g, (-s) % n, p) * u[1][j] + pow(g, (-2 * s) % n, p) * u[2][j]
              + pow(g, (-3 * s) % n, p) * u[3][j]) % p for j in range(n)] for s in range(n)]

def algorithm_A(p, g, u, count=None):
    n = p - 1
    c = [1, 1, 1]; mu = [pow(g, -l, p) for l in (1, 2, 3)]
    out = []
    for s in range(n):
        out.append([(u[0][j] + c[0] * u[1][j] + c[1] * u[2][j] + c[2] * u[3][j]) % p for j in range(n)])
        if count is not None: count['M'] += 3 * n; count['A'] += 3 * n
        c = [(c[l] * mu[l]) % p for l in range(3)]
        if count is not None: count['M'] += 3
    return out

def half(a, p):
    """a * 2^{-1} mod p by one parity test, one conditional add of p, one right shift."""
    return (a + p) >> 1 if a & 1 else a >> 1

def algorithm_B(p, u, count=None):
    """g = 2: contribution arrays updated by halvings; no multiplication in the loop."""
    n = p - 1
    a1, a2, a3 = list(u[1]), list(u[2]), list(u[3])
    out = []
    for s in range(n):
        out.append([(u[0][j] + a1[j] + a2[j] + a3[j]) % p for j in range(n)])
        a1 = [half(x, p) for x in a1]
        a2 = [half(half(x, p), p) for x in a2]
        a3 = [half(half(half(x, p), p), p) for x in a3]
        if count is not None: count['A'] += 3 * n; count['S'] += 6 * n
    return out

def rand_vec(p, n, seed):
    r = random.Random(seed); return [r.randrange(p) for _ in range(n)]

fails = 0
def check(name, ok):
    global fails
    print(("PASS " if ok else "FAIL ") + name)
    if not ok: fails += 1

# ---------------- A. operator identities ----------------
for p in (5, 13, 29, 37, 41, 61):
    for g in primitive_roots(p):
        n, k, i, W, F = setup(p, g)
        I = [[int(a == b) for b in range(n)] for a in range(n)]
        Jm = [[int(b == (-a) % n) for b in range(n)] for a in range(n)]
        negJ = [[(-x) % p for x in row] for row in Jm]
        W2 = matmul(W, W, p); F2 = matmul(F, F, p); F4 = matmul(F2, F2, p)
        ok = (i * i) % p == p - 1 and W2 == negJ and F2 == Jm and F4 == I and i == (-pow(g, k, p)) % p
        inv4 = pow(4, -1, p); ii = pow(i, -1, p)
        Fr = [I, F, F2, matmul(F2, F, p)]
        Pi = [[[(inv4 * sum(pow(ii, l * r, p) * Fr[r][a][b] for r in range(4))) % p for b in range(n)] for a in range(n)] for l in range(4)]
        for l in range(4):
            for m in range(4):
                ok &= matmul(Pi[l], Pi[m], p) == (Pi[l] if l == m else [[0] * n for _ in range(n)])
            ok &= matmul(F, Pi[l], p) == [[(pow(i, l, p) * x) % p for x in row] for row in Pi[l]]
        S = [[sum(Pi[l][a][b] for l in range(4)) % p for b in range(n)] for a in range(n)]
        ok &= S == I
        def Fs(s): return [[sum(pow(g, (-l * s) % n, p) * Pi[l][a][b] for l in range(4)) % p for b in range(n)] for a in range(n)]
        ok &= Fs(0) == I and Fs(k) == F and Fs(2 * k) == Jm and Fs(3 * k) == Fr[3] and Fs(4 * k) == I
        ok &= matmul(Fs(1), Fs(2), p) == Fs(3)
        check(f"A: identities p={p} g={g} (i={i})", ok)

# ---------------- B. orbit identity and one-transform setup ----------------
for p, g in ((5, 2), (5, 3), (13, 2), (13, 6), (29, 2), (37, 2), (41, 6), (61, 2), (101, 2), (157, 5), (197, 2)):
    n = p - 1
    v = rand_vec(p, n, p)
    u_dir = projections_direct(p, g, v); u_one = projections_one_transform(p, g, v)
    check(f"B: one-transform setup equals projector route p={p} g={g}", u_dir == u_one)
    if p <= 61:
        n, k, i, W, F = setup(p, g)
        orb = orbit_direct(p, g, v)
        # cardinal checks of the orbit against powers of F applied to v
        Fv = matvec(F, v, p)
        ok = orb[0] == v and orb[k] == Fv and orb[2 * k] == J(v) and orb[3 * k] == J(Fv)
        check(f"B: orbit cardinal values p={p} g={g}", ok)

# ---------------- C. algorithms ----------------
dsc = [p for p in primes(5, 200) if p % 4 == 1 and order(2, p) == p - 1]
print("primes p<200, p=1 mod 4, 2 primitive:", dsc)
for p in dsc:
    n = p - 1; v = rand_vec(p, n, 100 + p)
    u = projections_one_transform(p, 2, v)
    orb = orbit_direct(p, 2, v)
    check(f"C: Algorithm A == direct orbit p={p} g=2", algorithm_A(p, 2, u) == orb)
    check(f"C: Algorithm B (halving) == direct orbit p={p}", algorithm_B(p, u) == orb)
for p, g in ((41, 6), (157, 5)):
    n = p - 1; v = rand_vec(p, n, 200 + p)
    u = projections_one_transform(p, g, v)
    check(f"C: Algorithm A == direct orbit p={p} g={g} (2 not primitive; ord(2)={order(2,p)})", algorithm_A(p, g, u) == orbit_direct(p, g, v))

# ---------------- D. arithmetic of the class ----------------
P1 = [p for p in primes(5, 100000) if p % 4 == 1]
cls = [p for p in P1 if order(2, p) == p - 1]
check("D: Thm C(i): every p=1 mod 4 with 2 primitive has kappa odd (p=5 mod 8), p<1e5", all(((p - 1) // 4) % 2 == 1 for p in cls))
check("D: Thm C(iii): ord(2) at Fermat primes = 2,4,8,16,32", [order(2, q) for q in (3, 5, 17, 257, 65537)] == [2, 4, 8, 16, 32])
def criterion(p):
    k = (p - 1) // 4
    return k % 2 == 1 and all(pow(2, 4 * k // l, p) != 1 for l in factor(k))
check("D: criterion (kappa odd and 2^{4k/l} != 1 for all primes l|k) <=> 2 primitive, p=1 mod 4, p<1e5",
      all(criterion(p) == (p in set(cls)) for p in P1))
fam = [p for p in P1 if is_prime((p - 1) // 4) and (p - 1) // 4 > 2]
check(f"D: kappa an odd prime => 2 primitive ({len(fam)} cases below 1e5; first {fam[:8]})", all(order(2, p) == p - 1 for p in fam))
check("D: for p=1 mod 4, p<3000: (-2 primitive) <=> (2^{-1} primitive) <=> (2 primitive)",
      all((order(p - 2, p) == p - 1) == (order(2, p) == p - 1) == (order(pow(2, -1, p), p) == p - 1) for p in P1 if p < 3000))
# Lemma 4.6 is one-directional for a general power: (eps * 2^k primitive) => (2 primitive), for k = +-1, +-3, +-5, eps = +-1.
check("D: Lemma 4.6, p=1 mod 4, p<3000, k in {+-1,+-3,+-5}: (eps*2^k primitive) => (2 primitive)",
      all(order(2, p) == p - 1 for p in P1 if p < 3000
          for k in (1, -1, 3, -3, 5, -5) for eps in (1, p - 1) if order((eps * pow(2, k, p)) % p, p) == p - 1))
print("   converse fails for k=3: p=13, ord(2)=", order(2, 13), " ord(2^3=8)=", order(8, 13))
c5 = [p for p in primes(5, 1001) if p % 8 == 5]; d5 = [p for p in c5 if order(2, p) == p - 1]
print("   p<=1000, p=5 mod 8:", len(c5), " with 2 primitive:", len(d5))
print("   members:", d5)
print("   exceptions (5 mod 8, 2 not primitive):", [p for p in c5 if p not in d5])
check("D: Prop 4.7 counts 43 / 36 and first thirty", len(c5) == 43 and len(d5) == 36 and d5[:30] ==
      [5, 13, 29, 37, 53, 61, 101, 149, 173, 181, 197, 269, 293, 317, 349, 373, 389, 421, 461, 509, 541, 557, 613, 653, 661, 677, 701, 709, 757, 773])
c5L = [p for p in primes(5, 100000) if p % 8 == 5]
print(f"   density below 1e5: {len(cls)} of {len(c5L)} primes p=5 mod 8 -> {10000*len(cls)//len(c5L)} / 10000;  Artin constant x2 = 7479/10000 [import]")

# ---------------- E. primitives, worked example, counts ----------------
check("E: halving primitive a -> a/2 mod p, all residues, p in {13,197,65537}",
      all(half(a, p) == (a * pow(2, -1, p)) % p for p in (13, 197, 65537) for a in range(p)))
p, g = 13, 2; n, k, i, W, F = setup(p, g)
e0 = [1] + [0] * (n - 1)
u = projections_one_transform(p, g, e0)
one = [1] * n
print(f"   worked example p=13 g=2: i={i}, 1/4={pow(4,-1,p)}; u0={u[0]}; u1={u[1]}; u2={u[2]}; u3={u[3]}")
orb = orbit_direct(p, g, e0)
print(f"   F^[1]e0={orb[1]}  F^[3]e0={orb[3]}  F^[6]e0={orb[6]}")
check("E: worked example values", i == 5 and u[0] == [3] + [9] * 11 and u[2] == [11] + [4] * 11 and u[1] == [0] * n and u[3] == [0] * n
      and orb[1] == [9] + [10] * 11 and orb[3] == [5] * n and orb[6] == e0 and orb[1] == orb[7])
p = 61; n = p - 1; v = rand_vec(p, n, 7); u = projections_one_transform(p, 2, v)
cA = {'M': 0, 'A': 0, 'S': 0}; cB = {'M': 0, 'A': 0, 'S': 0}
algorithm_A(p, 2, u, cA); algorithm_B(p, u, cB)
print(f"   operation counts over the full orbit, p=61 (n=60): A={cA}  B={cB};  3n^2={3*n*n}, 6n^2={6*n*n}, 3n={3*n}")
check("E: counts (Theorem 3.1, Table 2): A = 3n^2 M + 3n M + 3n^2 A; B = 0 M + 3n^2 A + 6n^2 S",
      cA == {'M': 3 * n * n + 3 * n, 'A': 3 * n * n, 'S': 0} and cB == {'M': 0, 'A': 3 * n * n, 'S': 6 * n * n})

print("\nFAILURES:", fails)
sys.exit(1 if fails else 0)
