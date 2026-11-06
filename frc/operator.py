"""The operator theme (6 November 2026): translation-invariant operators as kernels, over the dirac theme's matrices.

A kernel is a sparse map {offset: 4×4 matrix over K} on F_p^d: (Aψ)(x) = Σ_s A[s] ψ(x + s). Composition is the convolution
(A∘B)[t] = Σ_s A[s]·B[t − s]; the identity is {0: I₄}; the X-adjoint is (A^#)[s] = X⁻¹ A[−s]† X. A translation-invariant
operator on the 4p^d-dimensional spinor space is determined by its kernel, so an identity of kernels is the identity of the
operators, and the orders and nilpotency indices of the Dirac Cayley steps are decided on kernels where the dense matrices
(4·13² = 676 in 1+1 at p = 13, 4·173 = 692 in 0+1 at p = 173) are out of reach. The section moved here from `frc/dirac.py`
(where it stood since 5 November 2026) when the operator layer became a theme of its own; the Lean side is the core's
`Theme/Packed`, `Theme/Plane`, `Theme/Hermitian`, `Theme/Operator`, `Theme/Unipotent`, `Theme/Spinor` and `Theme/Loss`.
Pure python, no third-party import (gate G09).
"""
from frc.dirac import ONE, ZERO, ident, iszero, msc, madd, mmul, meq, dagger

def _koff(p, s, t): return tuple((a + b) % p for a, b in zip(s, t))
def _kneg_off(p, s): return tuple((-a) % p for a in s)
def kadd(K, A, B):
    out = {s: [r[:] for r in M] for s, M in A.items()}
    for s, M in B.items(): out[s] = madd(K, out[s], M) if s in out else M
    return {s: M for s, M in out.items() if not iszero(M)}
def kneg(K, A): return {s: msc(K, K.neg(ONE), M) for s, M in A.items()}
def ksc(K, c, A): return {s: msc(K, c, M) for s, M in A.items()} if c != ZERO else {}
def kconv(K, p, A, B):
    out = {}
    for s, M in A.items():
        for t, N in B.items():
            u = _koff(p, s, t); P = mmul(K, M, N)
            out[u] = madd(K, out[u], P) if u in out else P
    return {s: M for s, M in out.items() if not iszero(M)}
def kid(d): return {(0,) * d: ident(4)}
def kiszero(A): return all(iszero(M) for M in A.values())
def keq(K, A, B): return kiszero(kadd(K, A, kneg(K, B)))
def kpow(K, p, A, e, d):
    """A^e by square-and-multiply."""
    R, X = kid(d), A
    while e:
        if e & 1: R = kconv(K, p, R, X)
        e >>= 1
        if e: X = kconv(K, p, X, X)
    return R
def kadjoint(K, p, X, A):
    """A^# = X⁻¹ A† X on kernels, X the spinor twist (X² a scalar)."""
    Xi = msc(K, K.inv(mmul(K, X, X)[0][0]), X)
    return {_kneg_off(p, s): mmul(K, mmul(K, Xi, dagger(K, M)), X) for s, M in A.items()}
def knilindex(K, p, A, cap):
    """The least k with A^k = 0, or None past cap."""
    X, k = A, 1
    while not kiszero(X):
        X = kconv(K, p, X, A); k += 1
        if k > cap: return None
    return k
def kseries_inv(K, p, N, d, idx):
    """(1 − N)⁻¹ = Σ_{k<idx} N^k for a kernel N nilpotent of index idx."""
    R, X = kid(d), kid(d)
    for _ in range(idx - 1):
        X = kconv(K, p, X, N); R = kadd(K, R, X)
    return R
def _unit(d, mu, s):
    v = [0] * d; v[mu] = s; return tuple(v)
def sym_dirac_kernel(K, p, d, G, shifts=None):
    """D^s = Σ_μ ∇^s_μ ⊗ γ^μ with ∇^s_μ = (T_{e_μ} − T_{−e_μ})/2, the frame vectors e_μ the standard ones unless `shifts` names them."""
    inv2 = K.scalar(pow(2, -1, p)); A = {}
    for mu in range(d):
        e = shifts[mu] if shifts else _unit(d, mu, 1)
        A = kadd(K, A, {tuple(x % p for x in e): msc(K, inv2, G[mu])})
        A = kadd(K, A, {_kneg_off(p, e): msc(K, K.neg(inv2), G[mu])})
    return A
def fwd_dirac_kernel(K, p, d, G, m=0):
    """The standard Dirac operator Σ_μ ∇_μ ⊗ γ^μ − m, ∇_μ = T_{e_μ} − 1."""
    A = {(0,) * d: msc(K, K.neg(K.scalar(m)), ident(4))}
    for mu in range(d):
        A = kadd(K, A, {_unit(d, mu, 1): G[mu]}); A = kadd(K, A, {(0,) * d: msc(K, K.neg(ONE), G[mu])})
    return A
def kg_kernel(K, p, d, nu, m=0):
    """The spinorial Klein–Gordon operator Σ_μ η_μμ ∇_μ² ⊗ I₄ − m² with the forward differences."""
    eta = [(-nu) % p, 1, 1, 1]; A = {(0,) * d: msc(K, K.neg(K.scalar(m * m)), ident(4))}
    for mu in range(d):
        nab = kadd(K, {_unit(d, mu, 1): ident(4)}, {(0,) * d: msc(K, K.neg(ONE), ident(4))})
        A = kadd(K, A, ksc(K, K.scalar(eta[mu]), kconv(K, p, nab, nab)))
    return A
def kcayley(K, p, d, H, alpha, nil_part, idx, scalar=ONE):
    """The Cayley step U = (1 − αH)⁻¹(1 + αH) for H = scalar·1 + nil_part with nil_part nilpotent of index idx (the inverse
    through the series of (1 + α·scalar)⁻¹ α nil_part)."""
    c = K.add(ONE, K.mul(alpha, scalar)); ci = K.inv(c)
    inv = ksc(K, ci, kseries_inv(K, p, ksc(K, K.mul(ci, alpha), nil_part), d, idx))
    return kconv(K, p, inv, kadd(K, kid(d), ksc(K, alpha, H)))

# The quadratic algebra over the scalar kernels: an element a + b·D with a, b scalar kernels {offset: K} and D² = Q a central
# scalar kernel (for D = D^s the Clifford relations give Q = Σ_μ η_μμ (∇^s_μ)² ⊗ I₄, which the package checks on the kernel itself).
def sconv(K, p, a, b):
    out = {}
    for s, x in a.items():
        for t, y in b.items():
            u = _koff(p, s, t); z = K.mul(x, y)
            out[u] = K.add(out[u], z) if u in out else z
    return {s: x for s, x in out.items() if x != ZERO}
def sadd(K, a, b):
    out = dict(a)
    for s, x in b.items(): out[s] = K.add(out[s], x) if s in out else x
    return {s: x for s, x in out.items() if x != ZERO}
def ssc(K, c, a): return {s: K.mul(c, x) for s, x in a.items()} if c != ZERO else {}
def qmul(K, p, Q, x, y):
    (a, b), (c, e) = x, y
    return (sadd(K, sconv(K, p, a, c), sconv(K, p, sconv(K, p, b, e), Q)), sadd(K, sconv(K, p, a, e), sconv(K, p, b, c)))
def qid(d): return ({(0,) * d: ONE}, {})
def qeq(K, p, D, x, y):
    """Equality of two elements as operators: the formal pairs are compared after expansion, since a nonzero b gives the zero
    operator b·D when D is nilpotent (the algebra is not faithful on the pairs)."""
    return keq(K, qexpand(K, p, D, x), qexpand(K, p, D, y))
def qpow(K, p, Q, x, e, d):
    R, X = qid(d), x
    while e:
        if e & 1: R = qmul(K, p, Q, R, X)
        e >>= 1
        if e: X = qmul(K, p, Q, X, X)
    return R
def qexpand(K, p, D, x):
    """The 4×4 kernel of a + b·D."""
    a, b = x
    return kadd(K, {s: msc(K, c, ident(4)) for s, c in a.items()}, kconv(K, p, {s: msc(K, c, ident(4)) for s, c in b.items()}, D))
def scalar_kernel(K, A):
    """A kernel that is scalar (every 4×4 block a multiple of I₄) as a scalar kernel, else None."""
    out = {}
    for s, M in A.items():
        c = M[0][0]
        if not meq(M, msc(K, c, ident(4))): return None
        out[s] = c
    return out

def order_certified(pow_, eq_, one, U, N, primes):
    """ord(U) = N exactly: U^N = 1, and U^(N/q) ≠ 1 for every prime q of N (`primes` must multiply to N with its multiplicities)."""
    prod = 1
    for q, e in primes.items(): prod *= q ** e
    if prod != N or not eq_(pow_(U, N), one): return False
    return all(not eq_(pow_(U, N // q), one) for q in primes)
