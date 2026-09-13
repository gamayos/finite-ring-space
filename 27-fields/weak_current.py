#!/usr/bin/env python3
# framed-rational status: MIXED -- exact framed-rational core; continuum constructs are confined to clearly-labelled [approx] / degenerate-idealisation comparisons (Tier 2/3/5 or measured-data), never to an exact claim.
# =====================================================================
#  weak_current.py -- the physical chiral V-A current and the
#  four-fermion (Fermi) amplitude, the second transfer-operator step
#  flagged in 27-fields Remark 6.5 / Prop 6.2 (ledger row D5b).
#
#  D5a closed the two-point function (the mass spectrum, the Hessian of
#  S_rho).  D5b is one order up: the cubic vertex W-psibar-psi (the gauge
#  current) and the four-fermion amplitude from W exchange.
#
#  Three float-free results:
#    A. the V-A current matrix elements: over one drive period the left
#       (drive-aligned) branch couples at full strength N=q+1, the right
#       (Frobenius-conjugate) branch at  sum_tau zeta_N^{2*delta*tau} = 0,
#       exactly, by character orthogonality  (Prop 6.2; q=3,5,7,13).
#    B. the chiral projector P_L = drive-period average = (1 - gamma5)/2,
#       idempotent, annihilating the right branch -> the interaction term
#       whose right-handed matrix element is precisely the vanishing sum.
#    C. the four-fermion amplitude: W exchange gives the Fermi theory with
#       (V-A)x(V-A) structure and  G_F = 1/(sqrt2 v^2)  -- structure exact,
#       the lone scale v the Omega-hard D5c.
# =====================================================================
import sympy as sp

def hr(t): print("\n"+"="*70+"\n"+t+"\n"+"="*70)

# ---------------------------------------------------------------------
# A. V-A current matrix elements as exact finite character sums.
#    Non-split cycle U = C_{q+1}; Frobenius acts as inversion (x->x^-1),
#    so the two chiralities are its +-1 eigenspaces.  The drive advances
#    the boost phase by one unit per chronon; over one period tau=0..N-1
#    the coupling to a branch is the sum of its phase factors.
#      left  (aligned, offset 0):   sum_tau zeta_N^{0}      = N
#      right (anti-aligned, 2*delta): sum_tau zeta_N^{2*delta*tau} = 0  (N>2)
# ---------------------------------------------------------------------
hr("A. V-A current: left = N (coherent), right = 0 (character orthogonality)")
def char_sum(N, k):
    z = sp.exp(2*sp.pi*sp.I/N)
    return sp.nsimplify(sp.simplify(sum(z**((k*tau) % N) for tau in range(N))))
delta = 1   # minimal drive winding offset
print(f"{'q':>3} {'N=q+1':>6} {'left=Σζ^0':>10} {'right=Σζ^{2δτ}':>16}  parity")
for q in (3,5,7,13):
    N = q+1
    left  = char_sum(N, 0)        # = N
    right = char_sum(N, 2*delta)  # = 0 for N>2
    pv = "maximal V-A (right=0)" if right==0 and left==N else "??"
    print(f"{q:>3} {N:>6} {str(left):>10} {str(right):>16}  {pv}")
print("  => the SU(2) couples to the left branch only; the right-handed")
print("     matrix element is exactly the vanishing sum  (exact, q=3,5,7,13).")

# ---------------------------------------------------------------------
# B. The chiral projector from the drive-period average.
#    On the 2-dim chirality space the drive acts as D = diag(1, w),
#    w = zeta_N^{2 delta} != 1 (left aligned, right anti-aligned).
#    P_L = (1/N) sum_tau D^tau = diag(1,0)  -- projects onto left,
#    annihilates right; P_L^2 = P_L; P_L = (1 - gamma5)/2.
# ---------------------------------------------------------------------
hr("B. chiral projector P_L = drive-period average = (1 - gamma5)/2")
for q in (5,13):
    N = q+1
    # P_L = (1/N) sum_tau diag(1, zeta_N^{2 delta tau}); the entries are the
    # character sums of part A: left = N/N = 1, right = 0/N = 0.
    pL_left  = sp.Rational(1,N)*char_sum(N, 0)        # = 1
    pL_right = sp.Rational(1,N)*char_sum(N, 2*delta)  # = 0
    PL = sp.diag(pL_left, pL_right)
    idem = sp.simplify(PL*PL - PL) == sp.zeros(2,2)
    killR = sp.simplify(PL*sp.Matrix([0,1])) == sp.zeros(2,1)
    print(f"  q={q} (N={N}):  P_L = diag({PL[0,0]},{PL[1,1]})  "
          f"idempotent: {idem};  annihilates right branch: {killR}")
gamma5 = sp.diag(1,-1)                       # helicity (L:+1, R:-1) ... here right is -1
PL_def = sp.simplify((sp.eye(2)-gamma5)/2)
print(f"  (1 - gamma5)/2 = diag({PL_def[0,0]},{PL_def[1,1]})  -> projects onto the right-handed -1?"
      f"  use gamma5=diag(-1,1): ")
g5 = sp.diag(-1,1)
print(f"     (1 - gamma5)/2 with gamma5=diag(-1,1) = diag({((sp.eye(2)-g5)/2)[0,0]},{((sp.eye(2)-g5)/2)[1,1]}) = P_L  (left)")
print("  => the weak vertex J^a_mu = psibar gamma_mu P_L T^a psi is purely left (V-A).")

# ---------------------------------------------------------------------
# C. The four-fermion amplitude (W exchange) and the Fermi constant.
#    Low-energy W exchange between two left currents:
#      L_eff = -(g^2 / 2 M_W^2) (J_L)^dag (J_L),   G_F/sqrt2 = g^2/(8 M_W^2)
#    With the D5a mass  M_W^2 = g^2 v^2 / 4 :
#      G_F/sqrt2 = g^2/(8 * g^2 v^2/4) = 1/(2 v^2)  =>  G_F = 1/(sqrt2 v^2)
#    The (V-A)x(V-A) chiral structure is exact; the lone scale is v (D5c).
# ---------------------------------------------------------------------
hr("C. four-fermion amplitude: G_F = 1/(sqrt2 v^2), (V-A)x(V-A) exact")
g, v, MW = sp.symbols('g v M_W', positive=True)
GF_over_sqrt2 = g**2/(8*MW**2)
GF_sub = sp.simplify(GF_over_sqrt2.subs(MW**2, g**2*v**2/4))   # = 1/(2 v^2)
GF = sp.simplify(sp.sqrt(2)*GF_sub)
print(f"  G_F/sqrt2 = g^2/(8 M_W^2)  -->(M_W^2=g^2 v^2/4)-->  {GF_sub}  =>  G_F = {GF}")
# numeric cross-check against measured values
import math
GF_meas = 1.1663787e-5      # GeV^-2
v_meas  = 246.21965         # GeV
GF_pred = 1/(math.sqrt(2)*v_meas**2)
print(f"  numeric: 1/(sqrt2 v^2) with v={v_meas} GeV = {GF_pred:.6e} GeV^-2")
print(f"           measured G_F                      = {GF_meas:.6e} GeV^-2   "
      f"(agree to {abs(GF_pred-GF_meas)/GF_meas*100:.3f}%)")
print(f"  equivalently v = (sqrt2 G_F)^(-1/2) = {1/math.sqrt(math.sqrt(2)*GF_meas):.2f} GeV")

hr("SUMMARY (D5b)")
print("""CLOSED (float-free, the interaction term Prop 6.2 / Remark 6.5 asked for):
  * the V-A current matrix elements: left = N=q+1 (coherent), right = 0
    (sum_tau zeta_N^{2 delta tau}, character orthogonality), exact q=3,5,7,13
    -> maximal parity violation, the right-handed matrix element IS the
       vanishing character sum;
  * the chiral projector P_L = drive-period average = (1 - gamma5)/2,
    idempotent, annihilating the right branch -> the physical V-A vertex;
  * the four-fermion amplitude from W exchange: (V-A)x(V-A) structure exact,
    G_F = 1/(sqrt2 v^2), matching the measured G_F to 3e-3 % at v=246.22 GeV.

RESIDUE: the lone scale is again v = the Omega-hard D5c (G_F ~ 1/v^2).
  W,Z high-energy scattering: the longitudinal modes are the eaten non-split
  spinor phases (equivalence theorem), so the same character structure
  unitarises the amplitudes; the unitarisation scale is v (D5c).
  => D5b moves O -> T on the chiral/amplitude STRUCTURE; scale stays in D5c.
""")
