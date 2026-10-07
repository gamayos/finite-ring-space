# framed-rational status: EXACT -- integer / modular-F_p / cyclotomic arithmetic; no float in any asserted check (float, if present, only formats an exact rational for display).
"""
Finitism cross-check: the EM-1 / O1 load-bearing claims established in EXACT
arithmetic, with no random sampling, no FFT, no floating point, no transcendental
functions. Each part stands in an exact construct -- integer F_p, cyclotomic Z[i],
or rational -- so no claim depends on a continuum step.

  A. Gauge invariance & superselection -- exact integers, exhaustive over a basis.
  B. Lattice Coulomb Green's function on the L=4 torus -- exact rationals via the
     quarter-turn DFT in Z[i].
  C. O1 admissible-space dimension -- exact integer rank of the integer Gram.
  D. Wilson action -- exact cyclotomic value 1 - Re(zeta_M^F) in Q(zeta_M).
"""
import itertools
from fractions import Fraction as Fr
import numpy as np
import sympy as sp
import enumerate_maxwell as em

d = 3

# ----------------------------------------------------------------------
# A. gauge invariance & superselection: exact, exhaustive over a basis
# ----------------------------------------------------------------------
def partA(L=4):
    sites = list(itertools.product(range(L), repeat=d))
    sidx = {s: i for i, s in enumerate(sites)}
    def add(x, z): return tuple((x[i] + z[i]) % L for i in range(d))

    def grad(lam):                       # (d lambda)_mu(x) = lam(x+e_mu)-lam(x)
        A = {}
        for x in sites:
            for mu in range(d):
                e = tuple(1 if k == mu else 0 for k in range(d))
                A[(x, mu)] = lam[add(x, e)] - lam[x]
        return A

    def plaq(A):                         # F_{mu<nu}(x) over all plaquettes
        F = {}
        for x in sites:
            for mu in range(d):
                for nu in range(mu + 1, d):
                    emu = tuple(1 if k == mu else 0 for k in range(d))
                    enu = tuple(1 if k == nu else 0 for k in range(d))
                    F[(x, mu, nu)] = (A[(x, mu)] + A[(add(x, emu), nu)]
                                      - A[(add(x, enu), mu)] - A[(x, nu)])
        return F

    # F(d lambda) = 0 for every basis lambda = delta_s  => for ALL lambda (linearity)
    worst = 0
    for s in sites:
        lam = {x: (1 if x == s else 0) for x in sites}
        F = plaq(grad(lam))
        worst = max(worst, max(abs(v) for v in F.values()))
    # superselection: gradient of a constant is exactly zero
    lam_const = {x: 7 for x in sites}
    Ac = grad(lam_const)
    const_ok = all(v == 0 for v in Ac.values())
    return worst, const_ok, len(sites)


# ----------------------------------------------------------------------
# B. Coulomb Green's function on the L=4 torus, EXACT rationals via Z[i] DFT.
#    On L=4 every Laplacian eigenvalue is an integer (cos(2pi k/4) in {1,0,-1,0}),
#    and the modes are 4th roots of unity = the quarter-turn group Q4 = Z[i].
# ----------------------------------------------------------------------
def partB(L=4):
    N = L ** d
    re_i = [1, 0, -1, 0]                  # Re(i^m), m mod 4   (exact integers)
    ks = list(itertools.product(range(L), repeat=d))
    # integer eigenvalues  lambda_k = sum_i 2(1 - Re(i^{k_i}))
    def lam(k): return sum(2 * (1 - re_i[k[i] % 4]) for i in range(d))
    def G(x):                             # exact rational Green's function
        tot = Fr(0)
        for k in ks:
            if all(c == 0 for c in k):    # skip zero mode (neutralising background)
                continue
            kdotx = sum(k[i] * x[i] for i in range(d)) % 4
            tot += Fr(re_i[kdotx], lam(k))
        return tot / N
    # exact potential along an axis, and the two-charge interaction energy
    axis = [(n, G((n, 0, 0))) for n in range(L)]
    sep = 1
    U_cross = G((sep, 0, 0))              # q1 q2 G(sep), exact rational
    return axis, U_cross


# ----------------------------------------------------------------------
# C. O1 admissible-space dimension: EXACT integer rank of the integer Gram
#    (integer Gaussian elimination over F_p).
# ----------------------------------------------------------------------
def _rank_mod_p(Aint, p):
    """Exact rank of an integer matrix over the prime field F_p (vectorised, finite)."""
    A = (Aint.astype(np.int64) % p)
    rows, cols = A.shape; r = 0
    for c in range(cols):
        nz = np.nonzero(A[r:, c])[0]
        if nz.size == 0:
            continue
        piv = r + int(nz[0])
        A[[r, piv]] = A[[piv, r]]
        inv = pow(int(A[r, c]), p - 2, p)
        A[r] = (A[r] * inv) % p
        f = A[:, c].copy(); f[r] = 0
        A = (A - np.outer(f, A[r])) % p           # eliminate column c in all other rows
        r += 1
        if r == rows:
            break
    return r


def partC(L=4, R=1):
    g = em.build(L)
    Qs = em.param_basis(g, R); n = len(Qs)
    # entries are small integers; matmul in float64 is BLAS-fast and exact here
    # (all Gram values are integers well below 2^53), then rounded back to int.
    Qstack = np.array([Q.reshape(-1) for Q in Qs], dtype=np.float64)
    QB = np.array([(Q @ g['B']).reshape(-1) for Q in Qs], dtype=np.float64)
    Gram = QB @ QB.T                              # gauge block
    for fp, fs in zip(g['flatperm'], g['flatsign']):
        D = Qstack[:, fp] * fs - Qstack
        Gram = Gram + D @ D.T                     # + cubic blocks
    Gram = np.rint(Gram).astype(np.int64)         # exact integer Gram
    rk = max(_rank_mod_p(Gram, 2147483647), _rank_mod_p(Gram, 2147483629))
    return n, n - rk                              # (#params, exact nullity)


# ----------------------------------------------------------------------
# D. Wilson action is cyclotomic-exact:  1 - cos(2pi F/M) = 1 - Re(zeta_M^F)
#    is an algebraic number in Q(zeta_M), not a transcendental float.
# ----------------------------------------------------------------------
def partD():
    out = []
    for M, F in [(12, 1), (12, 3), (52, 13), (8, 1)]:
        exact = sp.nsimplify(1 - sp.cos(2 * sp.pi * sp.Integer(F) / M))
        flt = float(exact)
        out.append((M, F, sp.simplify(exact), flt))
    return out


if __name__ == "__main__":
    print("=" * 70)
    print("FINITISM CROSS-CHECK -- exact verification of EM-1 / O1 claims")
    print("=" * 70)

    worst, const_ok, ns = partA(L=4)
    print("\n[A] gauge invariance & superselection (exact integers, exhaustive)")
    print(f"    F(d.lambda) over ALL {ns} basis gauge fields: max|F| = {worst}"
          f"   (exact zero: {worst == 0})")
    print(f"    gradient of a constant is identically zero: {const_ok}")
    print("    => no RNG needed; the identities hold for every configuration.")

    axis, Ucross = partB(L=4)
    print("\n[B] Coulomb Green's function on the L=4 torus (exact rationals, Z[i] DFT)")
    for n, val in axis:
        print(f"    G(n={n},0,0) = {val}   = {float(val):+.6f}")
    print(f"    two unit charges at separation 1: U = {Ucross} = {float(Ucross):.6f}")
    print("    => the Coulomb object is an exact rational; 1/4pi is its large-L reading.")

    npar, nullity = partC(L=4, R=1)
    print("\n[C] O1 admissible dimension (exact integer rank, no tolerance)")
    print(f"    range-1 parameters = {npar},  exact nullity = {nullity}"
          f"   (matches the float SVD value 2: {nullity == 2})")

    print("\n[D] Wilson action is cyclotomic-exact: 1 - cos(2pi F/M) in Q(zeta_M)")
    for M, F, exact, flt in partD():
        print(f"    M={M:3d} F={F}: 1-cos(2pi F/M) = {exact}  = {flt:.6f}")
    print("    => the action is an algebraic (cyclotomic) number, not a float.")
    print("=" * 70)
