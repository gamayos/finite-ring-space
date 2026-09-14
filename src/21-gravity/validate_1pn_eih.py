#!/usr/bin/env python3
"""O4 partial: the 1PN equivalence lemma (proved) and the nu-sector status.

PROVED here: through 1PN the FRC two-body metric coefficients are identical to
GR-isotropic with the superposed potential U = U1 + U2 -- both carry the same
(U1+U2)^2 cross term -- so the EIH Lagrangian, beta = gamma = 1, and all 1PN
two-body dynamics are shared exactly.  With the binding bookkeeping decided
(validate_binding.py: substrate winding sources, superposition exact), the
would-be Phi_2 ambiguity of the 1PN sector is absent.

STATUS of the 2PN nu-sector: a first delta-Lagrangian reduction was attempted
and FAILED its internal gate (the nu->0 limit did not reproduce the certified
test-particle coefficient 2 + e^2/2); the route requires the matched-invariant
(E, L) treatment.  Per the corpus discipline the failing derivation is not
shipped; the nu-sector remains OPEN (ledger row O4), with the test-particle
sector derived (validate_2pn.py) and the 1PN sector closed here.
"""
import sympy as sp
ok = True
def chk(n, c):
    global ok; ok = ok and bool(c); print(('PASS ' if c else 'FAIL ') + n)

U1, U2, t = sp.symbols('U1 U2 t', positive=True)
U = t*(U1 + U2)
A_frc = sp.series(sp.exp(-2*U), t, 0, 3).removeO()
A_gr  = sp.series(((1-U/2)/(1+U/2))**2, t, 0, 3).removeO()
chk("1PN: -g00 identical through (U1+U2)^2 incl. the cross term 4 U1 U2",
    sp.simplify(sp.expand(A_frc - A_gr)) == 0 and sp.expand(A_frc).coeff(t, 2).coeff(U1*U2) == 4)
B_frc = sp.series(sp.exp(2*U), t, 0, 2).removeO()
B_gr  = sp.series((1+U/2)**4, t, 0, 2).removeO()
chk("1PN: g_ij identical through (U1+U2)^1", sp.simplify(sp.expand(B_frc - B_gr)) == 0)
print("    => EIH two-body sector shared exactly at 1PN; nu-sector at 2PN remains OPEN (O4).")
print("\nALL PASS" if ok else "\nFAILURES PRESENT")
raise SystemExit(0 if ok else 1)
