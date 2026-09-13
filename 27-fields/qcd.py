# framed-rational status: MIXED -- exact framed-rational core; continuum constructs are confined to clearly-labelled [approx] / degenerate-idealisation comparisons (Tier 2/3/5 or measured-data), never to an exact claim.
"""
Strong sector: QCD-1 (confinement) and QCD-2 (the SU(3) rank-three frame).

QCD-1.  Confinement is the area law of the Wilson loop in the strong-coupling
        (saturated) regime of the COMPACT finite gauge group.  We compute the
        strong-coupling string tension sigma(beta) for compact U(1) and for Z_N
        and exhibit the linear potential V(r)=sigma*r, with the crossover to the
        weak-coupling Coulomb phase.  The finite gauge group is compact, so the
        confined phase exists; non-abelian asymptotic freedom puts the IR there.

QCD-2.  SU(3) is the special unitary group of a Hermitian 3-form over the
        quadratic extension K=F_{q^2} (the spinor channel) with Frobenius
        conjugation.  Built exactly for q=2 (F_4): order 216, centre Z_3
        (colour triality), controlled by the cube-root structure 3 | q+1.
"""
import numpy as np
import itertools
from fractions import Fraction as Fr
import math

# =====================================================================
# QCD-1 : strong-coupling string tension and the linear potential
# =====================================================================
def besselratio(beta, kmax=60):
    """I1(beta)/I0(beta) by series -- the U(1) single-plaquette character coeff."""
    I0 = sum((beta/2)**(2*k) / (math.factorial(k)**2) for k in range(kmax))
    I1 = sum((beta/2)**(2*k+1) / (math.factorial(k)*math.factorial(k+1))
             for k in range(kmax))
    return I1 / I0

def sigma_U1(beta):       # string tension, strong-coupling leading order
    return -math.log(besselratio(beta))

def sigma_ZN(beta, N):
    """Z_N gauge: single-plaquette character coeff c1 = <cos th e^{b cos th}>/<...>."""
    ths = [2*math.pi*k/N for k in range(N)]
    Z = sum(math.exp(beta*math.cos(t)) for t in ths)
    c1 = sum(math.cos(t)*math.exp(beta*math.cos(t)) for t in ths) / Z
    return -math.log(c1)

def qcd1():
    print("QCD-1  confinement = area law in the saturated (strong-coupling) regime")
    print("  string tension sigma(beta) = -ln(plaquette character coeff):")
    print("    beta   sigma_U(1)   sigma_Z2    sigma_Z3   phase")
    for beta in (0.2, 0.5, 1.0, 2.0, 4.0):
        sU = sigma_U1(beta); s2 = sigma_ZN(beta, 2); s3 = sigma_ZN(beta, 3)
        phase = "confined (linear V)" if sU > 0.3 else "-> Coulomb (deconfined)"
        print(f"    {beta:4.1f}   {sU:8.4f}   {s2:8.4f}   {s3:8.4f}   {phase}")
    # linear potential: V(r) = -lim_T (1/T) ln <W(r,T)> = sigma * r  (area law)
    beta = 0.5; s = sigma_U1(beta)
    print(f"\n  linear potential at beta={beta} (sigma={s:.4f}):  V(r) from area law")
    print("    r :   " + "  ".join(f"{r}" for r in range(1, 7)))
    print("    V(r): " + "  ".join(f"{s*r:.3f}" for r in range(1, 7))
          + "   (V/r constant => linear => confining)")
    print("  capacity link: small beta = low channel capacity = saturated;")
    print("  sigma ~ ln(1/beta) is the string tension; sqrt(sigma) sets Lambda_QCD.\n")


# =====================================================================
# QCD-2 : SU(3, F_q) as the special unitary group of a Hermitian 3-form
#          over K = F_{q^2}.  Exact construction for q=2 (K=F_4).
# =====================================================================
# F_4 = {0,1,2=w,3=w^2}, char 2.  Frobenius conjugation x -> x^2.
ADD = np.array([[0,1,2,3],[1,0,3,2],[2,3,0,1],[3,2,1,0]])
MUL = np.array([[0,0,0,0],[0,1,2,3],[0,2,3,1],[0,3,1,2]])
CONJ = np.array([0,1,3,2])          # x -> x^q = x^2 (Frobenius over F_2)

def f4_matmul(A, B):
    """batched 3x3 matmul over F_4.  A,B: (...,3,3) int arrays."""
    C = np.zeros(A.shape[:-2] + (3, 3), dtype=np.int64)
    for i in range(3):
        for j in range(3):
            acc = np.zeros(A.shape[:-2], dtype=np.int64)
            for k in range(3):
                acc = ADD[acc, MUL[A[..., i, k], B[..., k, j]]]
            C[..., i, j] = acc
    return C

def f4_det(M):
    a,b,c = M[...,0,0],M[...,0,1],M[...,0,2]
    d,e,f = M[...,1,0],M[...,1,1],M[...,1,2]
    g,h,i = M[...,2,0],M[...,2,1],M[...,2,2]
    def m(x,y): return MUL[x,y]
    t1 = m(a, ADD[m(e,i), m(f,h)])
    t2 = m(b, ADD[m(d,i), m(f,g)])
    t3 = m(c, ADD[m(d,h), m(e,g)])
    return ADD[ADD[t1, t2], t3]

def qcd2():
    print("QCD-2  SU(3,2): special unitary group of a Hermitian 3-form over F_4")
    # all 3x3 matrices over F_4
    N = 4**9
    digits = np.array(np.unravel_index(np.arange(N), (4,)*9)).T  # (N,9)
    M = digits.reshape(N, 3, 3)
    # conjugate-transpose  M^dagger = conj(M)^T
    Mdag = CONJ[M].transpose(0, 2, 1)
    # Hermitian form H = identity:  unitary  <=>  M^dag M = I
    prod = f4_matmul(Mdag, M)
    I3 = np.eye(3, dtype=np.int64)
    unitary = np.all(prod == I3, axis=(1, 2))
    det1 = (f4_det(M) == 1)
    su3 = unitary & det1
    order = int(su3.sum())
    formula = 2**3 * (2**2 - 1) * (2**3 + 1)        # q^3 (q^2-1)(q^3+1)
    print(f"    |SU(3,2)| enumerated = {order}    formula q^3(q^2-1)(q^3+1) = {formula}"
          f"    match: {order == formula}")
    # centre: scalar matrices xI with x^3=1 and norm(x)=1
    centre = []
    for x in range(4):
        S = (x * I3)               # not F_4 scalar mult; build xI by hand
        S = np.zeros((3,3), dtype=np.int64)
        for j in range(3): S[j,j] = x
        Sd = CONJ[S].T
        if np.all(f4_matmul(Sd[None], S[None])[0] == I3) and f4_det(S[None])[0] == 1:
            centre.append(x)
    print(f"    centre = scalar cube-roots of unity {{x I : x in {centre}}}  ->  Z_{len(centre)}"
          f"   (colour triality)")
    print(f"    cube roots of unity in F_4^x = C_3 present (3 | q^2-1); centre Z_3 since 3 | q+1.")
    print(f"    the defining 3-module over K is the colour triplet.\n")
    return order, formula, len(centre)


if __name__ == "__main__":
    print("=" * 70)
    print("STRONG SECTOR  (QCD-1 confinement, QCD-2 the SU(3) rank-three frame)")
    print("=" * 70 + "\n")
    qcd1()
    qcd2()
    print("=" * 70)
