#!/usr/bin/env python3
"""O1, the GR side [approx: continuum comparison chart, symbolic throughout].

For the static isotropic metric ds^2 = -A dt^2 + B (dr^2 + r^2 dphi^2) we derive,
by exact series in the mass m (sympy Rationals, no floats):

  (1) exponential metric A = exp(-2mu), B = exp(+2mu), u = 1/r (the E4 class,
      beta = gamma = 1): apsidal fraction per orbit = 3 m u_c + O(m^2),
      circular-orbit clock deficit 1 - dtau/dt = (3/2) m u_c + O(m^2),
      ratio -> 2.
  (2) PPN metric A = 1 - 2mu + 2 beta m^2 u^2, B = 1 + 2 gamma m u:
      apsidal coefficient = 2 - beta + 2 gamma, deficit coefficient = 3/2
      (beta, gamma free), so ratio = 2 iff 2 gamma - beta = 1.

Matching the pair's temporal face kappa/(2S) (check_o1.js) to the deficit forces
p_sl = 3 (S/kappa) r_g; the angular face kappa/S then equals the apsidal fraction
automatically.  Exit nonzero on any failed identity."""
import sympy as sp

m, u, uc, E2, L2, beta, gamma = sp.symbols('m u u_c E2 L2 beta gamma', positive=True)
fails = []
def ok(name, cond):
    print(('pass ' if cond else 'FAIL ') + name)
    if not cond: fails.append(name)

def faces(A, B):
    """Return (apsidal series coeff of m*u_c, deficit series coeff of m*u_c)."""
    # orbit equation: (du/dphi)^2 = F(u) = (E2*B/A - B)/L2 - u^2  (isotropic, u = 1/r)
    F = (E2*B/A - B)/L2 - u**2
    # circular orbit: F(uc) = 0, F'(uc) = 0  ->  solve for E2, L2
    Fc, Fpc = F.subs(u, uc), sp.diff(F, u).subs(u, uc)
    sol = sp.solve([Fc, Fpc], [E2, L2], dict=True)[0]
    # apsidal wavenumber: k^2 = -F''(uc)/2 ;  fraction per orbit = 1/k - 1
    k2 = sp.simplify(-(sp.diff(F, u, 2).subs(u, uc)).subs(sol)/2)
    k  = sp.sqrt(k2)
    aps = sp.series(1/k - 1, m, 0, 2).removeO().expand()
    aps_c = sp.simplify(aps.coeff(m, 1)/uc)
    # circular clock: (dtau/dt)^2 = A - L2*A^2*u^2/(E2*B)  at u = uc
    dt2 = (A - L2*A**2*u**2/(E2*B)).subs(u, uc).subs(sol)
    dfc = sp.series(1 - sp.sqrt(sp.simplify(dt2)), m, 0, 2).removeO().expand()
    dfc_c = sp.simplify(dfc.coeff(m, 1)/uc)
    return sp.simplify(aps_c), sp.simplify(dfc_c)

# ---- (1) the exponential (E4) metric ----
aps_c, dfc_c = faces(sp.exp(-2*m*u), sp.exp(2*m*u))
ok('(1) exponential metric: apsidal fraction coefficient = 3 exactly',
   sp.simplify(aps_c - 3) == 0)
ok('(1) exponential metric: clock-deficit coefficient = 3/2 exactly',
   sp.simplify(dfc_c - sp.Rational(3, 2)) == 0)
ok('(1) face ratio = 2 exactly', sp.simplify(aps_c/dfc_c - 2) == 0)

# ---- (2) the PPN family ----
A_ppn = 1 - 2*m*u + 2*beta*(m*u)**2
B_ppn = 1 + 2*gamma*m*u
aps_p, dfc_p = faces(A_ppn, B_ppn)
ok('(2) PPN apsidal coefficient = 2 - beta + 2*gamma',
   sp.simplify(aps_p - (2 - beta + 2*gamma)) == 0)
ok('(2) PPN deficit coefficient = 3/2, beta/gamma-free',
   sp.simplify(dfc_p - sp.Rational(3, 2)) == 0)
ok('(2) ratio = 2  <=>  2*gamma - beta = 1  (the ratio deviates by exactly '
   '(2/3)(2*gamma - beta - 1))',
   sp.simplify((aps_p/dfc_p - 2) - sp.Rational(2, 3)*(2*gamma - beta - 1)) == 0)

# ---- (3) the dictionary ----
S, kap, rg, p = sp.symbols('S kappa r_g p', positive=True)
psl = sp.solve(sp.Eq(sp.Rational(3, 2)*rg/p, kap/(2*S)), p)[0]
ok('(3) matching the temporal face: p_sl = 3 (S/kappa) r_g',
   sp.simplify(psl - 3*S*rg/kap) == 0)
ok('(3) the angular face then reads 3 r_g/p_sl = kappa/S: the apsidal fraction, '
   'automatically', sp.simplify(3*rg/psl - kap/S) == 0)

# ---- (4) the named exclusion: Brans--Dicke at every finite omega ----
w = sp.symbols('omega', positive=True)
gBD = (1 + w)/(2 + w)
ok('(4) Brans--Dicke combination 2*gamma - beta - 1 = -2/(2+omega), '
   'nonzero at every finite omega (deviation -4/(3(2+omega)))',
   sp.simplify((2*gBD - 1 - 1) + 2/(2 + w)) == 0
   and sp.simplify(sp.Rational(2, 3)*(2*gBD - 1 - 1) + sp.Rational(4, 3)/(2 + w)) == 0)
ok('(4) the omega -> oo limit returns the forced value (general relativity)',
   sp.limit(2*gBD - 1 - 1, w, sp.oo) == 0)

print('ALL O1 GR-CHART IDENTITIES PASS' if not fails else f'FAILURES: {len(fails)}')
raise SystemExit(1 if fails else 0)
