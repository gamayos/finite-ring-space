#!/usr/bin/env python3
"""2PN inputs and the J0737-3039 confrontation (sub:2pn).

Exact (sympy, rational series): the isotropic-gauge deviations of the
exponential metric from Schwarzschild -- delta A = U^3/6 in -g_00,
delta B = U^2/2 in g_ij -- certified term by term.
[chart] arithmetic: the periastron excess per orbit
   delta(Domega) = pi (GM/c^2 p)^2 (2 + e^2/2)
evaluated for PSR J0737-3039 (M = 2.5871 Msun, Pb = 8834.53 s, e = 0.0878),
giving the fractional excess ~1.5e-6 relative to the 1PN advance: at current
timing precision, presently degenerate with the omega-dot -> M_tot inference.
"""
import sympy as sp
ok = True
def chk(n, c):
    global ok; ok = ok and bool(c); print(('PASS ' if c else 'FAIL ') + n)

U = sp.symbols('U', positive=True)
exp_g00  = sp.series(sp.exp(-2*U), U, 0, 4).removeO()
schw_g00 = sp.series(((1 - U/2)/(1 + U/2))**2, U, 0, 4).removeO()
dA = sp.expand(exp_g00 - schw_g00)
chk("delta A = U^3/6 exactly (temporal, first difference at 3PN order in g_00)",
    sp.simplify(dA - U**3/6) == 0)
exp_gij  = sp.series(sp.exp(2*U), U, 0, 3).removeO()
schw_gij = sp.series((1 + U/2)**4, U, 0, 3).removeO()
dB = sp.expand(exp_gij - schw_gij)
chk("delta B = U^2/2 exactly (spatial, first difference at 2PN order in g_ij)",
    sp.simplify(dB - U**2/2) == 0)
chk("1PN agreement exact: g_00 and g_ij coincide through O(U^2) and O(U) resp.",
    sp.series(exp_g00 - schw_g00, U, 0, 3).removeO() == 0 and
    sp.series(exp_gij - schw_gij, U, 0, 2).removeO() == 0)

# ---- [chart] evaluation for J0737-3039 ----
G = 6.674e-11; c = 2.998e8; Msun = 1.989e30
M = 2.5871 * Msun; Pb = 8834.535; ecc = 0.0878
import math
a = (G * M * Pb**2 / (4 * math.pi**2)) ** (1.0/3.0)
p_slr = a * (1 - ecc**2)
Up = G * M / (c**2 * p_slr)
excess_frac = Up * (2 + ecc**2/2) / 6.0     # delta(Domega)/Domega_1PN
print(f"    [chart] U_p = {Up:.3e}; fractional 2PN excess = {excess_frac:.2e}")
chk("fractional excess ~1.5e-6 (within [1.0e-6, 2.0e-6])", 1.0e-6 < excess_frac < 2.0e-6)
print("    verdict: at current 1e-6 omega-dot precision, degenerate with the mass refit;")
print("    decisive once M_tot is fixed independently at 1e-6 (prediction P6).")



# ---- round-02: orbit-equation extraction (the analytic derivation's inputs) ----
w, E, L, M = sp.symbols('w E L M', positive=True)
BA_exp  = sp.series(sp.exp(4*M*w), M, 0, 4).removeO()
B_exp   = sp.series(sp.exp(2*M*w), M, 0, 4).removeO()
lnA_s   = -2*M*w - (M*w)**3/6
lnB_s   =  2*M*w - (M*w)**2/2 + (M*w)**3/6
BA_s    = sp.series(sp.exp(lnB_s - lnA_s), M, 0, 4).removeO()
B_s     = sp.series(sp.exp(lnB_s), M, 0, 4).removeO()
diff_eq = sp.expand((E**2*(BA_exp - BA_s) - (B_exp - B_s))/L**2)
c2 = diff_eq.coeff(w, 2).subs(E, 1 + sp.symbols('eps'))
c2 = sp.series(c2, sp.symbols('eps'), 0, 2).removeO()
c3 = diff_eq.coeff(w, 3).subs(E, 1)
chk("delta c2 leading term = eps M^2/L^2 exactly",
    sp.expand(c2).coeff(sp.symbols('eps'), 1) == M**2/L**2 and sp.expand(c2).coeff(sp.symbols('eps'), 0) == 0)
chk("delta c3 = (5/6) M^3/L^2 exactly", sp.simplify(c3 - sp.Rational(5,6)*M**3/L**2) == 0)
chk("apsidal sum identity: 5/2 - (1-e^2)/2 = 2 + e^2/2", True if sp.simplify(sp.Rational(5,2)-(1-sp.symbols('e')**2)/2-(2+sp.symbols('e')**2/2))==0 else False)

print("\nALL PASS" if ok else "\nFAILURES PRESENT")
raise SystemExit(0 if ok else 1)
