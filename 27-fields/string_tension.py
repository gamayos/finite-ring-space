# framed-rational status: MIXED -- exact framed-rational core; continuum constructs are confined to clearly-labelled [approx] / degenerate-idealisation comparisons (Tier 2/3/5 or measured-data), never to an exact claim.
"""
D6b -- the colour string tension from the finite strong-coupling expansion.
================================================================================
Closes the one *open* (closeable, not Omega-hard) residue of the strong sector:
the string tension sigma = -ln c_1(beta) had been computed only for the abelian
gauge groups U(1) and Z_N (qcd.py).  Here we give the NON-ABELIAN tension.

The area law itself (sigma>0) is a corollary of the positivity of S_rho
(Prop. corrarea, correspondence.py block F).  What was "still to be done" is the
*value* of the single-plaquette coefficient c_1(beta) for the colour group, in
finite units.  We supply it in three exact pieces and one resolved-window piece:

  T1  finite-group area law: for ANY finite gauge group, the rectangular Wilson
      loop tiles to c_1^Area with c_1 = <(1/N) chi_f>_w an EXACT finite sum
      (finite-group character orthogonality; no Haar measure, no Omega->infty).
  T2  SU(2,F_3)=2T (the corpus's exact non-abelian instance, 2T < SU(2,C)):
      c_1(beta) in closed form; leading sigma = ln(4/beta), reproducing the
      continuum SU(2) tension EXACTLY through order beta^3.
  T3  colour SU(3): resolved-window single-link expansion
      c_1 = beta/18 + beta^2/216 + ... = (beta/18)(1 + beta/12 + ...),
      positive and confining; the finite SU(3,F_q) reproduces it (Thm corr).
  S   structural float-free checks on SU(3,F_2): |G|=216, centre Z_3.

Everything exact is done over Q / closed form; the continuum Haar integrals are
the resolved-window (Omega->large) reference the finite group converges to.

Conventions match correspondence.py block F:
  action  S_rho(U) = 1 - (1/N) Re chi_f(U)  (positive class function),
  weight  w(U) = e^{-beta S_rho} ~ e^{beta (1/N) Re chi_f(U)}  (const cancels),
  coeff   c_1(beta) = < (1/N) chi_f >_w ,   sigma = -ln c_1 .
"""
import numpy as np
import math, itertools
from fractions import Fraction as Fr
import sympy as sp

PASS = []
def check(name, ok):
    PASS.append(bool(ok))
    print(f"  [{'PASS' if ok else 'FAIL'}] {name}")

# =====================================================================
print("="*72)
print("CHECK 0  normalisation matches the corpus (U(1): sigma(0.5)=1.4168)")
# =====================================================================
def Iv(v, beta, k=35):
    return sum((beta/2)**(2*j+v)/(math.factorial(j)*math.factorial(j+v))
               for j in range(k))
c1_U1 = lambda beta: Iv(1, beta)/Iv(0, beta)           # I1/I0
check("U(1) c_1=I1/I0, sigma(0.5)=1.4168",
      abs(-math.log(c1_U1(0.5)) - 1.4168) < 1e-3)

# =====================================================================
print("="*72)
print("CHECK T1  finite-group area law: orthogonality gives c_1 as an EXACT sum")
# =====================================================================
# The two identities the tiling uses, on a finite group G (uniform average
# (1/|G|) sum), verified on the symmetric group S_3 as a generic finite group:
#   (i)  <chi_r, chi_0> = (1/|G|) sum_g chi_r(g) = 0  for any nontrivial irrep r
#   (ii) (1/|G|) sum_g chi_r(a g) chi_s(g^{-1} b) = delta_{rs} chi_r(ab)/d_r
# (i) is exactly what makes the fundamental link integrate to zero (no tadpole),
# so the loop tiles its minimal surface; both are finite identities, no measure.
# Character table of S_3: classes e,(12),(123) sizes 1,3,2; irreps triv,sgn,std(2).
classes = [('e',1),('t',3),('c',2)]                    # name, size
chars = {'triv':{'e':1,'t':1,'c':1},
         'sgn' :{'e':1,'t':-1,'c':1},
         'std' :{'e':2,'t':0,'c':-1}}
order = 6
for r in ('sgn','std'):
    s = sum(sz*chars[r][nm] for nm,sz in classes)
    check(f"S_3: sum_g chi_{r} = 0  (fundamental has no singlet -> tiling closes)",
          s == 0)
# orthonormality (ii) at a=b=e: (1/|G|) sum |chi_r|^2 = 1
for r in chars:
    s = sum(sz*chars[r][nm]**2 for nm,sz in classes)
    check(f"S_3: <chi_{r},chi_{r}> = 1", Fr(s,order) == 1)

# =====================================================================
print("="*72)
print("CHECK T2  SU(2,F_3) = 2T < SU(2,C): exact closed-form string tension")
# =====================================================================
def quat_to_su2(q):
    a,b,c,d = q
    return np.array([[a+1j*b, c+1j*d], [-c+1j*d, a-1j*b]])
G2T = []
for s in ([1,0,0,0],[0,1,0,0],[0,0,1,0],[0,0,0,1]):
    for sg in (1,-1):
        G2T.append([sg*x for x in s])
for signs in itertools.product([0.5,-0.5], repeat=4):
    G2T.append(list(signs))
mats = [quat_to_su2(q) for q in G2T]
check("|2T| = 24 unit quaternions", len(mats) == 24)
check("2T < SU(2,C): all det=1, unitary",
      all(abs(np.linalg.det(M)-1) < 1e-9 and
          np.allclose(M.conj().T @ M, np.eye(2)) for M in mats))
from collections import Counter
trace_mult = Counter(int(round(np.trace(M).real)) for M in mats)
check("trace multiset {2:1,-2:1,0:6,1:8,-1:8}",
      dict(trace_mult) == {2:1,-2:1,0:6,1:8,-1:8})
# sum of the (nontrivial) fundamental character vanishes -> T1 hypothesis holds
check("sum_{g in 2T} chi_f(g) = 0 (orthogonality with trivial)",
      abs(sum(np.trace(M) for M in mats)) < 1e-9)

# exact closed form via the trace multiset, c_1 = <(1/2)chi>_w
b = sp.symbols('beta', positive=True)
mult = {2:1, -2:1, 0:6, 1:8, -1:8}
Zsum = sum(m*sp.exp(b*sp.Rational(t,2)) for t,m in mult.items())
Nsum = sum(m*sp.Rational(t,2)*sp.exp(b*sp.Rational(t,2)) for t,m in mult.items())
c1_2T = sp.nsimplify(sp.simplify(Nsum/Zsum))
print("    c_1^{2T}(beta) =", sp.simplify(c1_2T))
ser = sp.series(c1_2T, b, 0, 6).removeO()
print("    series         =", ser)
# leading term beta/4
lead = sp.limit(c1_2T/b, b, 0)
check("leading c_1^{2T} = beta/4  (=> sigma = ln(4/beta))", lead == sp.Rational(1,4))
# continuum SU(2) single-link c_1 = I2/I1; compare series
c1_SU2_series = sp.series(
    (sum((b/2)**(2*j+2)/(sp.factorial(j)*sp.factorial(j+2)) for j in range(6))) /
    (sum((b/2)**(2*j+1)/(sp.factorial(j)*sp.factorial(j+1)) for j in range(6))),
    b, 0, 6).removeO()
# agreement through beta^3: difference starts at beta^5
diff = sp.simplify(ser - c1_SU2_series)
low = sp.series(diff, b, 0, 5).removeO()
check("2T reproduces continuum SU(2) tension through O(beta^3) (diff starts beta^5)",
      sp.simplify(low) == 0)
f2T = sp.lambdify(b, c1_2T, 'math')
def c1_SU2(beta): return Iv(2,beta)/Iv(1,beta)
print("    beta   c_1^2T      c_1^SU2(Haar)   sigma^2T    reldiff")
for beta in (0.2,0.5,1.0,2.0):
    a, c = f2T(beta), c1_SU2(beta)
    print(f"    {beta:4.1f}  {a:.6f}   {c:.6f}     {-math.log(a):7.4f}   {abs(a-c)/c:.2e}")
check("sigma^{2T}(beta) > 0 for all tested beta (confining)",
      all(-math.log(f2T(x)) > 0 for x in (0.2,0.5,1.0,2.0,4.0)))

# =====================================================================
print("="*72)
print("CHECK T3  colour SU(3): resolved-window single-link expansion")
# =====================================================================
def c1_SU3(beta, n=600):
    p = np.linspace(0, 2*math.pi, n, endpoint=False)
    P1, P2 = np.meshgrid(p, p); P3 = -(P1+P2)
    z1, z2, z3 = np.exp(1j*P1), np.exp(1j*P2), np.exp(1j*P3)
    vdm = np.abs((z1-z2)*(z1-z3)*(z2-z3))**2            # SU(3) Weyl measure
    chi = z1+z2+z3
    w = np.exp(beta*chi.real/3.0)                        # w = e^{beta (1/3) Re chi}
    return float(np.sum((chi.real/3.0)*w*vdm)/np.sum(w*vdm))
bs = np.array([0.02,0.04,0.06,0.08,0.10,0.12])
vals = np.array([c1_SU3(x) for x in bs])
coef,*_ = np.linalg.lstsq(np.vstack([bs,bs**2,bs**3]).T, vals, rcond=None)
print(f"    fit: c_1^SU(3) = {coef[0]:.6f} b + {coef[1]:.6f} b^2 + ...")
check("SU(3) leading c_1 = beta/18 = 1/(2N^2)", abs(coef[0]-1/18) < 1e-4)
check("SU(3) next coeff = beta^2/216  (= (beta/18)(1+beta/12))", abs(coef[1]-1/216) < 1e-4)
print("    beta   c_1^SU(3)   sigma=-ln c_1")
for beta in (0.2,0.5,1.0,2.0,4.0):
    c = c1_SU3(beta); print(f"    {beta:4.1f}  {c:.6f}    {-math.log(c):7.4f}")
check("sigma^{SU(3)}(beta) > 0 for all tested beta (confining), ->0 as beta->inf",
      all(-math.log(c1_SU3(x)) > 0 for x in (0.2,0.5,1.0,2.0,4.0,8.0)))

# =====================================================================
print("="*72)
print("CHECK S  structural float-free checks on SU(3,F_2) over F_4")
# =====================================================================
ADD = np.array([[0,1,2,3],[1,0,3,2],[2,3,0,1],[3,2,1,0]])
MUL = np.array([[0,0,0,0],[0,1,2,3],[0,2,3,1],[0,3,1,2]])
CONJ = np.array([0,1,3,2])                               # Frobenius x->x^2
def herm(u,v):
    s = 0
    for i in range(3): s = ADD[s, MUL[CONJ[u[i]], v[i]]]
    return s
def det3(c0,c1,c2):
    M = [[c0[0],c1[0],c2[0]],[c0[1],c1[1],c2[1]],[c0[2],c1[2],c2[2]]]
    a,b_,c = M[0]; d,e,f = M[1]; g,h,i = M[2]
    pos = ADD[ADD[MUL[a,MUL[e,i]],MUL[b_,MUL[f,g]]],MUL[c,MUL[d,h]]]
    neg = ADD[ADD[MUL[c,MUL[e,g]],MUL[a,MUL[f,h]]],MUL[b_,MUL[d,i]]]
    return ADD[pos,neg]                                  # char 2: +/- identical
vecs = list(itertools.product(range(4), repeat=3))
norm1 = [v for v in vecs if herm(v,v) == 1]
cnt = 0; centre = set()
for c0 in norm1:
    for c1 in norm1:
        if herm(c0,c1) != 0: continue
        for c2 in norm1:
            if herm(c0,c2) != 0 or herm(c1,c2) != 0: continue
            if det3(c0,c1,c2) != 1: continue
            cnt += 1
            if (c0[1]==0 and c0[2]==0 and c1[0]==0 and c1[2]==0
                and c2[0]==0 and c2[1]==0 and c0[0]==c1[1]==c2[2]):
                centre.add(c0[0])
check("|SU(3,2)| = 216 = q^3(q^2-1)(q^3+1) at q=2",
      cnt == 216 == 2**3*(2**2-1)*(2**3+1))
check("centre = Z_3 (norm-one cube roots of unity; 3 | q+1)",
      len(centre) == 3 and (2+1) % 3 == 0)

# =====================================================================
print("="*72)
print(f"RESULT: {sum(PASS)}/{len(PASS)} checks pass")
print("D6b: the string tension sigma(beta) is computed in finite units --")
print("exact for U(1),Z_N (qcd.py) and 2T (closed form here), resolved-window")
print("series for SU(3).  The remaining strong-sector residue is the PHYSICAL")
print("value of beta (= the cross-scale running fixing Lambda_QCD = sqrt(sigma)),")
print("which is D6c, Omega-hard.  Clean cut: the function sigma(beta) is T; the")
print("point beta_phys on it is Omega.")
assert all(PASS), "some checks failed"
