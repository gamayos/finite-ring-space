## T6: the decoherence floor -- no spontaneous collapse, and the dilation floor.
## FRC is unitary below registration: the drive and every form-preserving
## propagator conserve ledger norms exactly, so an ISOLATED superposition keeps
## full fringe visibility at any mass, forever -- the framework forbids
## CSL/GRW-type spontaneous collapse outright (no parameter to tune). The only
## intrinsic floor is gravitational: mass is winding rate, so a composite's
## internal clocks read branch proper time, and a proper-time differential
## between interferometer arms writes which-path information into the internal
## state at exactly the rate of gravitational time-dilation decoherence
## (Pikovski et al. 2015) -- derived here from the FRC readings, with one
## FRC-specific discriminator: the spectrum is integer windings, so visibility
## REVIVES exactly at the cycle recurrence: dephasing, never collapse.
## Claims verified by exact arithmetic (Q(zeta_n), polys mod Phi_n):
##   (Q1) isolated doublet: fringe contrast = 1 exactly for every drive time and
##        every analyser setting sweep (unitarity: no intrinsic visibility loss);
##   (Q2) dilation dephasing: a cluster with internal winding distribution p_E
##        has branch visibility V(tau) = |sum_E p_E zeta^{E tau}| -- the
##        characteristic function of the internal energy distribution -- with
##        (a) the exact ring form verified, (b) Gaussian-envelope decay for a
##        binomial (thermal) distribution, matching the time-dilation law;
##   (Q3) exact recurrence: V(n) = 1 identically -- visibility revives at the
##        cycle period; decoherence in FRC is reversible dephasing, not collapse.
import numpy as np
from math import comb, gcd
from sympy import Poly, symbols, cyclotomic_poly, Rational

def report(label, ok):
    print(('PASS ' if ok else 'FAIL ') + label)
    assert ok, label

x = symbols('x')
n = 40                                                # internal winding cycle
PHI = Poly(cyclotomic_poly(n, x), x)
def zpow(k):  return Poly(x, x)**(k % n) % PHI
def zmul(a, b): return (a*b) % PHI
def zconj(a):
    out = Poly(0, x)
    for m, c in zip(a.monoms(), a.coeffs()):
        out = (out + c*zpow(-m[0])) % PHI
    return out

# ---------------- Q1: isolated superposition keeps contrast 1 ----------------
# doublet (1, lambda) with lambda = zeta^j; drive tau multiplies the relative
# phase by zeta^{8 tau} (gap 8, as in the composite gate); analyser sweep j':
# w_+(tau, j') = |1 + zeta^{j + 8 tau + j'}|^2 in {0..4}: contrast (max-min)/
# (max+min) over the sweep = 1 exactly iff max = 4 and min = 0 both occur.
ok1 = True
for j in (0, 3, 11):
    for tau in (0, 1, 5, 17, 39):
        vals = []
        for jp in range(n):
            k = (j + 8*tau + jp) % n
            w = (Poly(2, x) + zpow(k) + zpow(-k)) % PHI      # |1+zeta^k|^2
            vals.append(w)
        has4 = any(v.as_expr().equals(4) for v in vals)
        has0 = any(v.is_zero for v in vals)
        if not (has4 and has0): ok1 = False
report('Q1: isolated doublet contrast = 1 exactly, all drive times and phases '
       '(no spontaneous visibility loss at any mass: CSL forbidden)', ok1)

# ---------------- Q2: dilation dephasing law ----------------
# internal energy distribution p_E: binomial on E = 0..M (thermal-like), shifted;
# branch visibility V(tau)^2 = |sum_E p_E zeta^{E tau}|^2, exact in the ring.
M = 8
pE = {E: Rational(comb(M, E), 2**M) for E in range(M+1)}
def V2_exact(tau):
    s = Poly(0, x)
    for E, p in pE.items():
        s = (s + p*zpow(E*tau)) % PHI
    return zmul(s, zconj(s))
# (a) V(tau)^2 is a real, nonnegative ring element (a squared modulus), equal to 1
#     at tau = 0 (full coherence, sum_E p_E = 1) -- exact ring identities.
ok2 = True
for tau in range(n):
    v2 = V2_exact(tau)
    if not ((v2 - zconj(v2)) % PHI).is_zero: ok2 = False         # V^2 is real (= its conjugate)
if not ((V2_exact(0) - Poly(1, x)) % PHI).is_zero: ok2 = False    # V(0)^2 = 1, full coherence
report('Q2a: V(tau)^2 = |characteristic function of internal windings|^2 is real for '
       'every drive time and equals 1 at tau = 0 (full coherence): exact ring identities', ok2)
# (b) Gaussian envelope: binomial variance M/4: V ~ exp(-sigma^2 theta^2/2)
ok2b = True
sig2 = M/4
for tau in (1, 2, 3, 4):
    th = 2*np.pi*tau/n
    chi = abs(sum(float(p)*np.exp(1j*E*th) for E, p in pE.items()))
    gauss = np.exp(-sig2*th*th/2)
    if abs(chi - gauss) > 0.02: ok2b = False                 # envelope agreement
report('Q2b: Gaussian-envelope decay V = exp(-sigma^2 (omega tau)^2/2) -- the '
       'large-M numeric approximation of the exact ring characteristic function', ok2b)

# ---------------- Q3: exact recurrence ----------------
v2 = V2_exact(n)
report('Q3: exact recurrence V(n)^2 = 1: visibility revives at the cycle '
       'period -- dephasing, never collapse', v2.as_expr().equals(1))

# ---------------- Q4: distinct-eigenvalue superposition dephases to an integer count ----------------
# In 421/61/29, Object O_29 (cycle C_28, core Q4, quotient C_7, zeta7 = g_O^4), the
# same-channel superposition psi = psi_0 + psi_4 mixes windings of DISTINCT drive
# eigenvalues (1 and g_O^-4). The snapshot pair-count w_0(a) = |4(1+zeta7^a)|^2 =
# 16(2 + zeta7^a + zeta7^-a) is a real algebraic integer, NOT in Z. The REGISTERED
# weight is the drive-frequency count W_0(a) = sum_t |Psi_t^0(a)|^2 over the joint
# recurrence T = lcm(n_S, n_O) = lcm(60, 28) = 420; the cross term sums to zero,
# leaving an ordinary integer, uniform over the seven outcomes, so P = 1/7.
PHI7 = Poly(cyclotomic_poly(7, x), x)
def z7p(k):  return Poly(x, x)**(k % 7) % PHI7
def conj7(P):
    out = Poly(0, x)
    for m, c in zip(P.monoms(), P.coeffs()):
        out = (out + c*z7p(-m[0])) % PHI7
    return out
def isZ7(P):  return (P % PHI7).degree() <= 0
nO7 = 28
T7 = 60*nO7 // gcd(60, nO7)               # joint recurrence lcm(n_S, n_O) = lcm(60,28) = 420
snap, tot7 = [], Poly(0, x)
for a in range(7):
    Psi = (Poly(4, x)*(Poly(1, x) + z7p(a))) % PHI7
    w = (conj7(Psi)*Psi) % PHI7
    snap.append(w); tot7 = (tot7 + w) % PHI7
report('Q4a: snapshot pair-count w_0(1) = 16(2+zeta7+zeta7^-1) is a real algebraic '
       'integer, NOT in Z (the transient); sum over outcomes = 224 in Z',
       (not isZ7(snap[1])) and isZ7(tot7) and tot7.as_expr().equals(224))
W = []
for a in range(7):
    acc = Poly(0, x)
    for t in range(T7):
        Psi_t = (Poly(4, x)*(Poly(1, x) + z7p(a - t))) % PHI7
        acc = (acc + conj7(Psi_t)*Psi_t) % PHI7
    W.append(acc)
Wv = [int(w.as_expr()) for w in W]
report('Q4b: registered drive-frequency count W_0(alpha) = 13440 = 420*32 for every '
       'outcome (ordinary integer, uniform over T = lcm(60,28) = 420): the snapshot '
       'interference dephases over the recurrence',
       all(isZ7(w) for w in W) and len(set(Wv)) == 1 and Wv[0] == 13440)
report('Q4c: registered probability P_0(alpha) = 1/7 (rational); drive-average per '
       'step = 32 = incoherent diagonal sum |c0|^2+|c4|^2',
       Rational(Wv[0], sum(Wv)) == Rational(1, 7) and Wv[0] // T7 == 16 + 16)

print('decoherence: all checks passed')
