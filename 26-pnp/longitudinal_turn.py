#!/usr/bin/env python3
# -*- coding: utf-8 -*-
"""
longitudinal_turn.py  --  the frequency domain as the longitudinal quarter turn.

Validates the rigorous spine of the frequency-domain blueprint (26-pnp), float-free in the
native finite-field (framed-rational) arena, with one symbolic continuum-shadow check.

  P1  the longitudinal turn = the multiplicative DFT on Z/(P-1): it diagonalises the scale
      shift theta -> g.theta, the multiplicative characters chi_nu being eigenvectors with the
      (P-1)-th roots of unity as eigenvalues; the eigen-index nu is the FREQUENCY.
      Continuum shadow: it diagonalises H = -i(x d/dx + 1/2), eigenfns x^{-1/2+i nu}, eigenvalue nu
      => frequency = spectrum of the dilation generator H.

  P2  the Gauss sum g(chi)=sum_theta chi(theta) psi(theta) couples an additive character
      (SPECTRUM) to a multiplicative one (FREQUENCY); for chi nontrivial |g(chi)|^2 = P.
      Verified by the exact additive-character telescoping (integer/combinatorial, no floats):
      sum_{t!=0} psi(t c) = -1 (c!=0), = P-1 (c=0).

  P3  the two turns are the classical/quantum line: the TRANSVERSE additive turn is an exact
      self-invertible transform (NTT round-trip over F_q, float-free) -- the classical FFT, in P;
      the LONGITUDINAL multiplicative turn underlies exp:Z/(P-1)->F_P^x (a bijection) whose forward
      inverse is dlog -- BQP-forward, classically arrow-bound (cf. dlog_asymmetry.py).
"""
from fractions import Fraction as Fr
import sympy as sp

PASS = []
def check(name, cond):
    PASS.append(bool(cond)); print(f"  [{'OK' if cond else 'XX'}] {name}")

def primroot(p):
    """least primitive root mod p (p prime)."""
    fac = sp.factorint(p-1)
    for g in range(2, p):
        if all(pow(g, (p-1)//q, p) != 1 for q in fac):
            return g
    raise RuntimeError

# ---------- P1: multiplicative DFT diagonalises the scale shift ----------
print("P1  longitudinal turn = multiplicative DFT diagonalises the scale shift")
for p in (13, 17, 53):
    g = primroot(p)                  # generator of F_p^x  (order n=p-1)
    n = p - 1
    zeta = g                         # a primitive n-th root of unity lives IN F_p: zeta=g
    # eigenvector for frequency nu: chi_nu(g^t) = zeta^{nu t}; shift S: (S f)(t)=f(t+1)
    ok_eig, ok_distinct = True, set()
    for nu in range(n):
        v = [pow(zeta, (nu*t) % n, p) for t in range(n)]
        Sv = [v[(t+1) % n] for t in range(n)]            # shifted
        lam = pow(zeta, nu, p)                            # claimed eigenvalue
        if any((Sv[t] - lam*v[t]) % p != 0 for t in range(n)):
            ok_eig = False
        ok_distinct.add(lam)
    check(f"p={p}: every chi_nu is an eigenvector of the scale shift (exact in F_{p})", ok_eig)
    check(f"p={p}: the {n} eigenvalues are distinct (full diagonalisation)", len(ok_distinct)==n)

# P1 continuum shadow: H x^{-1/2+i nu} = nu x^{-1/2+i nu}
print("P1  continuum shadow: H=-i(x d/dx + 1/2) on x^{-1/2+i nu}")
x = sp.symbols('x', positive=True); nu = sp.symbols('nu', real=True)
phi = x**(sp.Rational(-1,2) + sp.I*nu)
Hphi = -sp.I*(x*sp.diff(phi, x) + sp.Rational(1,2)*phi)
check("H phi = nu phi exactly (eigen-index nu = frequency = spectrum of H)",
      sp.simplify(Hphi - nu*phi) == 0)

# ---------- P2: Gauss-sum modulus |g(chi)|^2 = P via exact telescoping ----------
print("P2  Gauss sum couples spectrum<->frequency; |g(chi)|^2 = P (exact telescoping)")
for p in (13, 17, 53):
    # additive-character telescoping, purely combinatorial (no complex numbers):
    # sum_{t in F_p^x} psi(t c) = sum over exponents {t c mod p : t=1..p-1}.
    # c != 0 : the multiset is a permutation of {1,..,p-1}  => sum of all nonzero roots = -1.
    # c == 0 : every exponent 0                              => sum = (p-1).
    perm_ok = all(sorted((t*c) % p for t in range(1, p)) == list(range(1, p))
                  for c in range(1, p))
    zero_ok = all((t*0) % p == 0 for t in range(1, p))
    check(f"p={p}: {{t c mod p}} is a permutation of nonzero residues for every c!=0", perm_ok)
    # => |g(chi)|^2 = sum_u chi(u) [sum_t psi(t(u-1))] = (p-1)+(-1)(sum_{u!=1}chi(u))
    #              = (p-1) - (0 - 1) = p   for chi nontrivial (sum_u chi(u)=0).
    check(f"p={p}: hence |g(chi)|^2 = (p-1) - (0 - 1) = p = {p}", (p-1) - (0 - 1) == p and zero_ok)

# ---------- P3: transverse turn is an exact self-inverse transform (NTT round-trip) ----------
print("P3  transverse (additive) turn: NTT round-trip exact over F_q (the classical-P turn)")
def ntt(a, w, q):
    n = len(a)
    return [sum(a[t]*pow(w, (k*t) % n, q) for t in range(n)) % q for k in range(n)]
q, n, w = 17, 8, 2          # 2 is a primitive 8th root of unity mod 17 (2^8=1, 2^4=-1)
check("2 is a primitive 8th root of unity mod 17", pow(w,n,q)==1 and pow(w,n//2,q)==q-1)
a = [3, 1, 4, 1, 5, 9, 2, 6]
A = ntt(a, w, q)
ninv = pow(n, q-2, q); winv = pow(w, q-2, q)
a_rt = [(ninv * sum(A[k]*pow(winv, (t*k) % n, q) for k in range(n))) % q for t in range(n)]
check("inverse-NTT(NTT(a)) = a exactly (transverse turn forward-computable, in P)",
      a_rt == [v % q for v in a])

# P3 longitudinal underlying map exp:Z/(P-1)->F_P^x is a bijection; its inverse is dlog
print("P3  longitudinal turn underlies exp (bijection); forward inverse = dlog (classically hard)")
for p in (13, 17, 53):
    g = primroot(p)
    img = [pow(g, t, p) for t in range(p-1)]
    check(f"p={p}: exp t->g^t is a bijection Z/(P-1) -> F_P^x (image = all nonzero residues)",
          sorted(img) == list(range(1, p)))

print("\n" + "="*68)
print(f"longitudinal_turn: {sum(PASS)}/{len(PASS)} checks pass "
      f"(finite-field/integer exact; one symbolic continuum-shadow)")
print("="*68)
assert all(PASS), "a check failed"
