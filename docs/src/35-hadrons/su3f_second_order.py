#!/usr/bin/env python3
# E1 push - second-order SU(3)_F breaking: the decuplet curvature and the octet-decuplet links.
#
# Framed-rational / 1-algebra: all relations are exact identities of the constituent hyperfine
# model (linear strange-seed mass + pairwise hyperfine), verified symbolically. No RNG, no logs,
# no fit. PDG enters once as the labelled [approx] readout.
#
# Model. Constituent mass: light m, strange m_s; strange excess d = m_s - m per strange seed.
# Pairwise hyperfine A_ij = A * (m/m_i)(m/m_j): A_ll = A, A_ls = A r, A_ss = A r^2, r = m/m_s.
# Spin correlator <S_i.S_j> = +1/4 (aligned), and the decuplet has all spins aligned (S=3/2).

import sympy as sp

M0, d, A, r = sp.symbols('M0 d A r', real=True)

print("== E1a: decuplet masses in the constituent hyperfine model ==")
# decuplet (S=3/2, every pair +1/4); strange-seed count n_s = 0,1,2,3
MD  = M0 +     0*d + A*sp.Rational(3,4)                          # Delta  uuu
MSs = M0 +     1*d + A*sp.Rational(1,4)*(1 + 2*r)                # Sigma* uus
MXs = M0 +     2*d + A*sp.Rational(1,4)*(2*r + r**2)             # Xi*    uss
MO  = M0 +     3*d + A*sp.Rational(3,4)*r**2                     # Omega  sss
for nm, e in [("Delta", MD), ("Sigma*", MSs), ("Xi*", MXs), ("Omega", MO)]:
    print(f"  M_{nm:6s} = {e}")

print("\n== E1b: the decuplet THIRD-difference relation (exact, parameter-free) ==")
third = sp.simplify(MD - 3*MSs + 3*MXs - MO)
print(f"  M_Delta - 3 M_Sigma* + 3 M_Xi* - M_Omega = {third}")
print(f"  -> vanishes identically in (M0, d, A, r): {third == 0}")
assert third == 0
print("  first order (linear n_s) gives equal spacing (2nd difference = 0, the 9.2% residual);")
print("  second order (pairwise strange wrap) gives the 3rd difference = 0, a parameter-free relation.")

print("\n== E1c: octet masses and the octet-decuplet hyperfine links ==")
# octet: Lambda (ud spin-0), Sigma (ud spin-1), Xi (ss spin-1), N (all light, S=1/2)
MN = M0 +     0*d + A*sp.Rational(-3,4)                          # N   (uud) Sig_<S.S> = -3/4
ML = M0 +     1*d + A*sp.Rational(-3,4)                          # Lam (uds) ud spin-0
MS = M0 +     1*d + A*(sp.Rational(1,4) - r)                     # Sig (uds) ud spin-1
MX = M0 +     2*d + A*(r**2*sp.Rational(1,4) - r)                # Xi  (uss) ss spin-1
# parameter-free links:
rel1 = sp.simplify((MS - ML) - sp.Rational(2,3)*((MD - MN) - (MSs - MS)))
rel2 = sp.simplify((MSs - MS) - (MXs - MX))
print(f"  M_Sigma - M_Lambda  -  (2/3)[(M_Delta-M_N) - (M_Sigma*-M_Sigma)]  = {rel1}  -> {rel1==0}")
print(f"  (M_Sigma* - M_Sigma) - (M_Xi* - M_Xi)                            = {rel2}  -> {rel2==0}")
assert rel1 == 0 and rel2 == 0
print("  both are exact, parameter-free predictions of the model (the strange-wrap hyperfine).")

# ---------------------------------------------------------------------------------------------
print("\n== [approx] PDG 2024 confrontation (isospin-averaged, MeV) ==")
F = sp.Rational
def avg(*x): return sum(sp.nsimplify(str(v)) for v in x)/len(x)
mN = avg(938.272, 939.565); mL = sp.nsimplify("1115.683")
mS = avg(1189.37,1192.642,1197.449); mX = avg(1314.86,1321.71)
mD = sp.nsimplify("1232.0"); mSs = avg(1382.8,1383.7,1387.2)
mXs = avg(1531.80,1535.0); mO = sp.nsimplify("1672.45")

third_pdg = mD - 3*mSs + 3*mXs - mO
print(f"  decuplet 3rd difference  M_D - 3 M_S* + 3 M_X* - M_O = {float(third_pdg):+.1f} MeV "
      f"({float(third_pdg/mO)*100:+.2f}% of the scale)   [approx]")
print(f"     (cf. the 1st-order equal-spacing spread ~13.5 MeV / 9.2%: the 2nd-order relation halves it)")
lhs1 = mS - mL; rhs1 = F(2,3)*((mD - mN) - (mSs - mS))
print(f"  M_Sigma - M_Lambda = {float(lhs1):.1f}  vs  (2/3)[(D-N)-(S*-S)] = {float(rhs1):.1f} MeV "
      f"  ({float((lhs1-rhs1)/lhs1)*100:+.0f}%)   [approx]")
lhs2 = mSs - mS; rhs2 = mXs - mX
print(f"  M_Sigma* - M_Sigma = {float(lhs2):.1f}  vs  M_Xi* - M_Xi = {float(rhs2):.1f} MeV "
      f"  ({float((lhs2-rhs2)/lhs2)*100:+.0f}%)   [approx]")

print("\nE1 PUSH: the decuplet 3rd-difference relation is exact and parameter-free, holding to")
print("6 MeV (0.4% of the scale), tightening the 1st-order 9.2% equal-spacing spread; the")
print("octet-decuplet hyperfine links hold to ~12%, the residual the wavefunction wrap correction.")
print("E1 reduces to: the decuplet 3rd-order residual (6 MeV) and the octet 27-plet GMO term (0.57%).")
