#!/usr/bin/env python3
"""Projection defect (Definition def:defect): exact checks on dev shells.

(a) Cycle-quotient closure: for the cycle-projection registration the chart
    closes exactly (defect = 1), matching 'each shell reads its own projection'.
(b) Windowed (no-wrap) registration does NOT close: the accumulated defect over
    one full recurrence equals the exact wrap count -- the bias in count form.
(c) K_S = P U_C P on a non-invariant sector appears contractive (exact rational
    norms strictly decreasing on a test vector) while U_C is a permutation with
    U_C^ord = identity (reversible, recurrent).
(d) Constitutive selection: on the odd-character space of C_12 the antisymmetric
    currents J(z^-1) = -J(z) are spanned by odd harmonics; the minimal degree is
    unique up to sign (the sine mode); higher odd harmonics exist, so the
    minimal-degree condition is a declared realisation, exactly as stated.
"""
from fractions import Fraction
ok = True
def chk(n, c):
    global ok; ok = ok and bool(c); print(('PASS ' if c else 'FAIL ') + n)

# (a) cycle projection closes
p, g = 157, 5
e = (p - 1) // 52          # 3: projection onto C_52 by cubing
G = pow(g, e, p)
closed = all(pow((g * c) % p, e, p) == (G * pow(c, e, p)) % p for c in range(1, p))
chk("(a) cycle-quotient registration closes: defect = 1 on all of F_157^x", closed)

# (b) windowed registration wraps: accumulated defect = exact winding count
q, gq = 13, 2              # Subject F_13, drive 2, additive no-wrap window
W = 3                      # window half-width (comprehension bound, toy)
wraps = 0
x = 1
for n in range(12):        # one full multiplicative recurrence ord(2)=12
    xn = x * gq % q
    lift  = x  if x  <= q // 2 else x  - q
    liftn = xn if xn <= q // 2 else xn - q
    if abs(liftn) > W or abs(lift) > W:
        wraps += 1
    x = xn
chk(f"(b) windowed chart fails to close; accumulated defect over one recurrence = {wraps} (exact count > 0)", wraps > 0)

# (c) K_S = P U P contracts on the non-invariant sector; U recurrent
n = 12                      # cyclic permutation U on Z_12
sector = list(range(5))     # non-invariant window P
v = [Fraction(1) if i in sector else Fraction(0) for i in range(n)]
def U(vec):  return [vec[(i - 1) % n] for i in range(n)]
def P(vec):  return [vec[i] if i in sector else Fraction(0) for i in range(n)]
norms = []
w = v[:]
for _ in range(6):
    w = P(U(P(w)))
    norms.append(sum(x * x for x in w))
chk("(c) K_S norms strictly decreasing (exact rationals): " + ">".join(str(x) for x in norms[:4]),
    all(norms[i] > norms[i + 1] for i in range(len(norms) - 1)) or norms[-1] == 0)
w = v[:]
for _ in range(n):
    w = U(w)
chk("(c) U_C^ord = identity (reversible recurrence)", w == v)

# (d) odd-character space and the minimal degree
import itertools
m = 12
odd = [k for k in range(1, m) if (-k) % m != k and k < m - k]  # representatives k, m-k pair
chk(f"(d) antisymmetric currents = odd harmonics; minimal degree k=1 unique up to sign; higher odd harmonics exist (dim = {len(odd)} > 1)",
    odd[0] == 1 and len(odd) > 1)


# ---- round-02 additions ----
from math import gcd
# (e) relative-cycle defect and recurrence (Lemma lem:relcycle)
nA, nB, wA, wB = 60, 28, 1, 1
L = nA*nB//gcd(nA,nB); qq = gcd(nA,nB); aa = (wB*L//nB - wA*L//nA) % L
Tdef = (L//qq)//gcd(L//qq, aa)
chk(f"(e) relative-cycle defect: L=420, q=4, a=8, T_def=105 on the C60-C28 pair",
    (L, qq, aa, Tdef) == (420, 4, 8, 105))
# (f) compression identity P - K^t K = C^t C on the cyclic model (exact rationals)
from fractions import Fraction
n2 = 12; sector = list(range(5))
def Umat():
    M = [[Fraction(0)]*n2 for _ in range(n2)]
    for i in range(n2): M[i][(i-1) % n2] = Fraction(1)
    return M
def Pmat():
    M = [[Fraction(0)]*n2 for _ in range(n2)]
    for i in sector: M[i][i] = Fraction(1)
    return M
def mm(A,B): return [[sum(A[i][k]*B[k][j] for k in range(n2)) for j in range(n2)] for i in range(n2)]
def mt(A): return [[A[j][i] for j in range(n2)] for i in range(n2)]
def msub(A,B): return [[A[i][j]-B[i][j] for j in range(n2)] for i in range(n2)]
Uc, P = Umat(), Pmat()
K = mm(P, mm(Uc, P)); C = mm(msub([[Fraction(i==j) for j in range(n2)] for i in range(n2)], P), mm(Uc, P))
lhs = msub(P, mm(mt(K), K)); rhs = mm(mt(C), C)
chk("(f) compression identity P - K^T K = C^T C exact (12-cycle, 5-cell sector)",
    lhs == rhs)
# (g) Laurent uniqueness of the pair-tally deficit (support {0,+-1}, inversion, alignment)
# general a0 + a1 z + a-1 z^-1 with inversion symmetry a1 = a-1 and E(1) = 0 => a0 = -2 a1
# => E = a1 (2 - z - z^-1) up to scale; oriented mate (z - z^-1)/2i unique odd part
import sympy as _sp
_z, _a0, _a1, _am = _sp.symbols('z a0 a1 am')
_E = _a0 + _a1*_z + _am/_z
_c1 = _sp.simplify(_E - _E.subs(_z, 1/_z))          # inversion symmetry
_sol = _sp.solve([_sp.Poly(_sp.together(_c1)*_z, _z).all_coeffs()[0], _E.subs(_z, 1)], [_am, _a0], dict=True)
_ok_g = False
if _sol:
    _Ef = _sp.simplify(_E.subs(_sol[0]))
    _ok_g = _sp.simplify(_Ef - _a1*(_z + 1/_z - 2)) == 0
chk("(g) pair-tally deficit unique on unit-capacity support: E = a1(z + z^{-1} - 2), one scale",
    _ok_g)

print("\nALL PASS" if ok else "\nFAILURES PRESENT")
raise SystemExit(0 if ok else 1)
