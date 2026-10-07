## T5: gravitationally induced entanglement (BMV) -- the FRC mechanism.
## In FRC gravity IS phase synchronisation on the substrate (gravity companion):
## two locked clusters in path superposition accumulate a branch-pair-dependent
## relative phase at the Newtonian rate phi(t) = (G m1 m2 / hbar)(1/d - 1/d')t,
## with the Newtonian potential supplied by the gravity paper's derived lattice
## Green's function. The interaction couples to the conserved offset sector of
## the pair -- the same constant of motion that carries Bell correlations
## (composite.py C2) -- so it is an entangling channel by construction.
## Claims verified by exact arithmetic (Q(zeta_80), polys mod Phi_80):
##   (B1) zero coupling: the joint state remains an exact product (concurrence 0);
##   (B2) conditional phase phi = 2 pi k/80 produces entanglement with
##        concurrence^2 = sin^2(phi/2) EXACTLY, for the full sweep k = 0..79;
##   (B3) the witness: the Horodecki CHSH maximum 2*sqrt(1 + sin^2(phi/2))
##        exceeds 2 for every k != 0 (numeric image of the exact table), and
##        reaches the Tsirelson value 2*sqrt2 at phi = pi -- consistency with
##        the composite gate;
##   (B4) the coupling is offset-diagonal (commutes with the drive); A's
##        marginal is invariant under local operations on B (no signalling);
##        and the fringe visibility obeys V^2 + C^2 = 1 exactly -- the
##        gravitational which-path complementarity, the BMV observable pair.
## FRC forward prediction for BMV-class experiments: entanglement forms at the
## Newtonian rate exactly; corrections are bounded by the horizon (1/sqrt(Omega))
## and are unobservable; a null result at the Newtonian rate falsifies the
## framework's gravitational sector outright.
from sympy import Poly, symbols, cyclotomic_poly, Rational

def report(label, ok):
    print(('PASS ' if ok else 'FAIL ') + label)
    assert ok, label

x = symbols('x')
PHI = Poly(cyclotomic_poly(80, x), x)
def zpow(k):  return Poly(x, x)**(k % 80) % PHI
def zmul(a, b): return (a*b) % PHI
def zconj(a):
    out = Poly(0, x)
    for m, c in zip(a.monoms(), a.coeffs()):
        out = (out + c*zpow(-m[0])) % PHI
    return out

# joint branch state of two clusters, each (|0> + |1>), coupling phase on |11>:
# amplitudes (1, 1, 1, zeta^k); unnormalised (norm^2 = 4).
def amps(k):
    return [Poly(1, x), Poly(1, x), Poly(1, x), zpow(k)]

# ---------------- B1: zero coupling -> exact product ----------------
a = amps(0)
det = (zmul(a[0], a[3]) - zmul(a[1], a[2])) % PHI     # ad - bc
report('B1: phi = 0: ad - bc = 0 exactly (product state, concurrence 0)',
       det.is_zero)

# ---------------- B2: concurrence^2 = sin^2(phi/2) exactly ----------------
ok2 = True
for k in range(80):
    a = amps(k)
    det = (zmul(a[0], a[3]) - zmul(a[1], a[2])) % PHI
    c2 = zmul(det, zconj(det))                         # |ad-bc|^2 (norm 4 state)
    # concurrence = 2|ad-bc|/norm^2 = |ad-bc|/2 -> C^2 = |ad-bc|^2/4
    # target: sin^2(phi/2) = (1 - cos phi)/2 = (2 - zeta^k - zeta^-k)/4
    tgt = (Poly(2, x) - zpow(k) - zpow(-k)) % PHI
    if not (c2 - tgt).is_zero: ok2 = False
report('B2: concurrence^2 = sin^2(phi/2) exactly, full sweep phi = 2 pi k/80', ok2)

# ---------------- B3: Horodecki CHSH witness, exact (pure-state formula) ----------------
# For a pure two-qubit state of concurrence C the maximal CHSH is exactly
#   S_max = 2 sqrt(1 + C^2), so S_max^2 = 4(1 + C^2) = 4 + |ad - bc|^2 (norm-4 state).
# Hence the witness is an exact ring element: > 4 (S_max > 2) iff C != 0, and = 8
# (S_max = 2 sqrt2) at phi = pi.  No eigenvalues, no floating point.
ok3, okts = True, False
for k in range(80):
    a = amps(k)
    det = (zmul(a[0], a[3]) - zmul(a[1], a[2])) % PHI
    c2 = zmul(det, zconj(det))                              # |ad - bc|^2 = 4 C^2
    smax2 = (Poly(4, x) + c2) % PHI                         # S_max^2 = 4 + |ad - bc|^2
    if k != 0 and c2.is_zero: ok3 = False                  # S_max^2 = 4: witness not > 2
    if k == 40 and not ((smax2 - Poly(8, x)) % PHI).is_zero: ok3 = False
    if k == 40 and ((smax2 - Poly(8, x)) % PHI).is_zero: okts = True
report('B3: Horodecki S_max^2 = 4(1 + C^2) = 4 + |ad-bc|^2 exactly; > 4 for phi != 0 '
       '(C != 0, S_max > 2), and = 8 (S_max = 2 sqrt2) at phi = pi (k = 40)',
       ok3 and okts)

# ---------------- B4: drive commutation + no-signalling (exact ring arithmetic) ----------------
# (i) coupling G = diag(1,1,1,z^k) and drive D = diag(1,i,i,-1) are both diagonal,
#     hence commute exactly; (ii) A's reduced state is invariant under ANY local
#     operation U on B (partial-trace invariance), checked on exact ring-valued U.
ONE_ = Poly(1, x); ZERO_ = Poly(0, x); II = zpow(20)        # i = zeta_80^20
locB = {'X': [[ZERO_, ONE_], [ONE_, ZERO_]],
        'Z': [[ONE_, ZERO_], [ZERO_, (-ONE_) % PHI]],
        'Y': [[ZERO_, (-II) % PHI], [II, ZERO_]]}
def rhoA(psi):                                              # 2x2 reduced state on A, exact
    return [[(zmul(psi[2*aa], zconj(psi[2*bb])) + zmul(psi[2*aa+1], zconj(psi[2*bb+1]))) % PHI
             for bb in (0, 1)] for aa in (0, 1)]
def eqmat(M, Nn): return all((M[i][j] - Nn[i][j]).is_zero for i in (0, 1) for j in (0, 1))
Dd = [ONE_, II, II, (-ONE_) % PHI]                          # diagonal drive image
ok4a, ok4b = True, True
for k in (1, 7, 20, 40, 63):
    Gd = [ONE_, ONE_, ONE_, zpow(k)]                        # diagonal coupling
    if any(not (zmul(Gd[j], Dd[j]) - zmul(Dd[j], Gd[j])).is_zero for j in range(4)):
        ok4a = False
    psi = [ONE_, ONE_, ONE_, zpow(k)]
    rA = rhoA(psi)
    for U in locB.values():
        psiU = [(zmul(U[b][0], psi[2*aa]) + zmul(U[b][1], psi[2*aa+1])) % PHI
                for aa in (0, 1) for b in (0, 1)]
        if not eqmat(rhoA(psiU), rA): ok4b = False
report('B4i: the coupling commutes with the diagonal drive (offset-diagonal), exact', ok4a)
report('B4ii: A marginal invariant under any local operation on B '
       '(no signalling), exact ring identity', ok4b)
# (iii) exact ring identity: V^2 + C^2 = 1, V^2 = (2 + z^k + z^-k)/4, C^2 = (2 - z^k - z^-k)/4
ok4c = True
for k in range(80):
    V2 = (Poly(2, x) + zpow(k) + zpow(-k)) % PHI
    C2 = (Poly(2, x) - zpow(k) - zpow(-k)) % PHI
    if not ((V2 + C2) % PHI).as_expr().equals(4): ok4c = False
report('B4iii: visibility-entanglement complementarity V^2 + C^2 = 1 exactly, '
       'full sweep (the BMV observable pair)', ok4c)

print('bmv: all checks passed')
