# framed-rational status: EXACT -- integer / modular-F_p / cyclotomic arithmetic; no float in any asserted check (float, if present, only formats an exact rational for display).
"""
EW-1: electroweak symmetry breaking as drive / torus misalignment.

  A. The breaking mechanism, exact over F_p:
     the drive (a split-torus element) acts by conjugation on the gauge Lie
     algebra sl2(F_p); it fixes its own Cartan (eigenvalue 1 = unbroken U(1)_EM,
     drive-invariant, hence massless) and rotates the off-diagonal generators
     (eigenvalues t^{+-2} != 1 = the charged, gapped W^pm).  Its centraliser is
     the split torus = U(1), order p-1.  The non-split torus (weak SU(2)) is NOT
     centralised by the drive -> the source of the breaking.
  B. Neutral mixing: the (W3,B) mass matrix -> massless photon + massive Z,
     tan(theta_W)=g'/g, and a doublet Higgs gives rho = M_W^2/(M_Z^2 cos^2)=1.
  C. The Weinberg angle reduces to the charge spectrum:
     sin^2(theta_W) = Tr(T3^2)/Tr(Q^2) = 3/8 for a complete generation (exact),
     1/2 for a lone lepton doublet -> the number is set by the fermion content.

Finitism: part A is exact arithmetic in F_p; part C is exact rationals; part B
is exact symbolic algebra.  No RNG, FFT, or floating point in the derivations.
"""
from fractions import Fraction as Fr
import sympy as sp
import itertools

# ======================================================================
# A. breaking mechanism, exact in F_p   (p = 13, symmetry-complete 4t+1)
# ======================================================================
def partA(p=13, g=2):
    # matrices over F_p as tuples (a,b,c,d) for [[a,b],[c,d]]
    def mul(X, Y):
        a, b, c, d = X; e, f, h, k = Y
        return ((a*e + b*h) % p, (a*f + b*k) % p,
                (c*e + d*h) % p, (c*f + d*k) % p)
    def inv_scalar(t): return pow(t, p - 2, p)

    t = g; ti = inv_scalar(t)                     # drive = diag(t, t^-1)
    drive = (t, 0, 0, ti)
    drive_inv = (ti, 0, 0, t)

    # Ad_drive on the sl2 basis H=[[1,0],[0,-1]], E=[[0,1],[0,0]], F=[[0,0],[1,0]]
    H = (1, 0, 0, p - 1); E = (0, 1, 0, 0); Fm = (0, 0, 1, 0)
    eig = {}
    for name, Xb in [('H', H), ('E', E), ('F', Fm)]:
        Y = mul(mul(drive, Xb), drive_inv)
        # Y should be lambda * Xb; read lambda off the nonzero component
        comp = next(i for i in range(4) if Xb[i] % p)
        lam = (Y[comp] * inv_scalar(Xb[comp] if Xb[comp] != p-1 else p-1)) % p
        # simpler: lambda = Y[comp]/Xb[comp]
        lam = (Y[comp] * inv_scalar(Xb[comp] % p)) % p
        eig[name] = lam

    # centraliser of the drive in SL2(F_p): brute force
    cent = 0
    for a in range(p):
        for b in range(p):
            for c in range(p):
                for d in range(p):
                    if (a*d - b*c) % p != 1:
                        continue
                    M = (a, b, c, d)
                    if mul(M, drive) == mul(drive, M):
                        cent += 1

    # non-split torus: norm-1 elements of F_p[sqrt(nu)], nu a nonsquare.
    squares = {(x*x) % p for x in range(p)}
    nu = next(x for x in range(2, p) if x not in squares)
    # element [[a, nu*b],[b, a]] has determinant a^2 - nu b^2 (the norm)
    nonsplit_gen = None
    for a in range(p):
        for b in range(p):
            if (a*a - nu*b*b) % p == 1 and not (b == 0 and a == 1):
                nonsplit_gen = (a, (nu*b) % p, b, a); break
        if nonsplit_gen: break
    commutes = mul(nonsplit_gen, drive) == mul(drive, nonsplit_gen)
    return eig, cent, p - 1, nu, commutes


# ======================================================================
# B. neutral mixing, photon/Z, rho = 1   (exact symbolic)
# ======================================================================
def partB():
    g, gp, v = sp.symbols('g g_prime v', positive=True)
    # neutral gauge mass^2 matrix in (W3, B) basis from a doublet Higgs vev v
    M2 = sp.Rational(1, 4) * v**2 * sp.Matrix([[g**2, -g*gp], [-g*gp, gp**2]])
    eigs = sp.simplify(sp.Matrix(M2).eigenvals())     # {0: photon, (g^2+g'^2)v^2/4: Z}
    MW2 = sp.Rational(1, 4) * g**2 * v**2             # charged W mass^2
    MZ2 = sp.Rational(1, 4) * (g**2 + gp**2) * v**2
    cos2 = g**2 / (g**2 + gp**2)                      # cos^2(theta_W)
    rho = sp.simplify(MW2 / (MZ2 * cos2))             # custodial rho parameter
    tan = gp / g                                      # tan(theta_W)
    return eigs, sp.simplify(rho), tan


# ======================================================================
# C. Weinberg angle from the charge spectrum  (exact rationals)
#    sin^2(theta_W) = Tr(T3^2) / Tr(Q^2)
# ======================================================================
def sin2_from_content(fermions):
    """fermions: list of (T3, Q, multiplicity)."""
    trT3 = sum(Fr(T3)**2 * m for T3, Q, m in fermions)
    trQ = sum(Fr(Q)**2 * m for T3, Q, m in fermions)
    return trT3 / trQ, trT3, trQ

def partC():
    # lone left-handed lepton doublet (nu, e)
    lepton = [(Fr(1, 2), 0, 1), (Fr(-1, 2), -1, 1)]
    # complete SM generation: 15 left-handed Weyl fermions
    #   (T3 nonzero only for LH SU(2) doublets; Q for all)
    gen = [
        (Fr(1, 2),  0,    1),   (Fr(-1, 2), -1,   1),    # lepton doublet
        (0,         1,    1),                            # e^c (positron)
        (Fr(1, 2),  Fr(2, 3), 3), (Fr(-1, 2), Fr(-1, 3), 3),  # quark doublet x3 colour
        (0,         Fr(-2, 3), 3),                       # u^c x3
        (0,         Fr(1, 3),  3),                       # d^c x3
    ]
    s_lep, *_ = sin2_from_content(lepton)
    s_gen, trT3, trQ = sin2_from_content(gen)
    return s_lep, s_gen, trT3, trQ


if __name__ == "__main__":
    print("=" * 68)
    print("EW-1  electroweak breaking as drive / torus misalignment")
    print("=" * 68)

    eig, cent, torus, nu, commutes = partA(13, 2)
    print("\n[A] breaking mechanism, exact in F_13 (drive = diag(2, 2^-1))")
    print(f"    Ad_drive eigenvalues on sl2:  H -> {eig['H']},  E -> {eig['E']},"
          f"  F -> {eig['F']}   (mod 13)")
    print(f"    H is drive-invariant (eigenvalue 1)  => unbroken U(1)_EM, MASSLESS photon")
    print(f"    E,F have eigenvalues != 1            => charged W^pm, GAPPED (massive)")
    print(f"    centraliser of the drive in SL2(F_13) = {cent}  = p-1 = {torus}"
          f"  (the split torus = U(1))")
    print(f"    non-split torus (weak SU(2), nu={nu}) commutes with drive: {commutes}"
          f"   => drive misaligns SU(2): the source of breaking")

    eigs, rho, tan = partB()
    print("\n[B] neutral mixing (exact symbolic)")
    print(f"    (W3,B) mass^2 eigenvalues: {dict(eigs)}")
    print(f"      -> one ZERO eigenvalue (photon) + one massive (Z)")
    print(f"    tan(theta_W) = g'/g ;  custodial rho = M_W^2/(M_Z^2 cos^2 theta_W) = {rho}"
          f"   (doublet Higgs => rho = 1 exactly)")

    s_lep, s_gen, trT3, trQ = partC()
    print("\n[C] Weinberg angle from the charge spectrum (exact rationals)")
    print(f"    sin^2(theta_W) = Tr(T3^2)/Tr(Q^2)")
    print(f"      lone lepton doublet        : {s_lep}  = {float(s_lep):.4f}")
    print(f"      complete SM generation     : Tr(T3^2)={trT3}, Tr(Q^2)={trQ}"
          f"  ->  sin^2 = {s_gen} = {float(s_gen):.4f}")
    print(f"    => the ANGLE reduces to the fermion content; a complete generation")
    print(f"       gives the standard unification value 3/8 (runs to ~0.231 at M_Z).")
    print("=" * 68)
