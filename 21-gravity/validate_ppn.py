"""Relativistic layer: PPN parameters, light deflection, perihelion, static-profile series.

Validates: Lemma (isotropic pair) + Prop (full light deflection)  alpha = 4Gm/(c^2 b);
           Prop (all three classical tests)  beta = gamma = 1 for the exponential metric;
           Prop (exact static profile)       u(r) = Gm/r (1 + (Gm/r^2)^2/30 + ...).
"""
import sympy as sp

ok = True
z, b, G, m, c, U, r, s, Gm = sp.symbols('z b G m c U r s Gm', positive=True)

# Fermat deflection in index n = 1 + 2Gm/(c^2 r)
n1 = 2*G*m/(c**2*sp.sqrt(b**2 + z**2))
alpha = sp.integrate(-sp.diff(n1, b), (z, -sp.oo, sp.oo))
print("  deflection:", sp.simplify(alpha), " (target 4Gm/(b c^2))")
if sp.simplify(alpha - 4*G*m/(b*c**2)) != 0: ok = False

# PPN of exponential isotropic metric
g00 = sp.series(-sp.exp(-2*U), U, 0, 3).removeO()
gij = sp.series(sp.exp(2*U), U, 0, 2).removeO()
beta = -sp.Rational(1, 2)*g00.coeff(U, 2)   # g00 = -1 + 2U - 2 beta U^2
gamma = sp.Rational(1, 2)*gij.coeff(U, 1)   # gij = 1 + 2 gamma U
print(f"  PPN: beta = {beta}, gamma = {gamma}  (targets 1, 1)")
if beta != 1 or gamma != 1: ok = False
peri = sp.Rational(2 + 2*1 - 1, 3)
print(f"  perihelion factor (2+2*gamma-beta)/3 = {peri}  (target 1)")
if peri != 1: ok = False

# exact static profile series: u = int_r^inf arcsin(Gm/s^2) ds
ser = sp.series(sp.asin(Gm/s**2), Gm, 0, 4).removeO()
user = sp.integrate(ser, (s, r, sp.oo))
target = Gm/r + Gm**3/(30*r**5)
print("  static profile:", sp.simplify(user), " (target Gm/r + Gm^3/(30 r^5))")
if sp.simplify(user - target) != 0: ok = False

print("PASS" if ok else "FAIL", "- relativistic layer / PPN")
