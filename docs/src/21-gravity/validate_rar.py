"""Weak-acceleration floor: a0 = c H0 / (2 pi) against the radial acceleration relation.

Validates: Prop (floor acceleration) -- the derived scale against the SPARC fit
a0 = 1.20 +/- 0.02 (stat) +/- 0.24 (syst) x 10^-10 m/s^2 (McGaugh-Lelli-Schombert 2016);
and the turnaround radius corollary for the Local Group.
"""
import math

ok = True
c = 2.998e8
a0_fit, syst = 1.20e-10, 0.24e-10
print("  a0 = c H0 / (2 pi):")
for H0 in (67.4, 70.0, 73.0):
    H = H0*1000/3.0857e22
    a0 = c*H/(2*math.pi)
    dev = (a0 - a0_fit)/syst
    print(f"    H0={H0:5.1f}: a0 = {a0:.3e} m/s^2   ({dev:+.2f} syst-sigma from fit)")
    if abs(a0 - a0_fit) > 1.5*syst: ok = False

# turnaround radius for the Local Group (m ~ 5e12 Msun): r_ta = (Gm/H^2)^(1/3) ~ 1 Mpc scale
G, Msun, Mpc = 6.674e-11, 1.989e30, 3.0857e22
H = 70*1000/Mpc
r_ta = (G*5e12*Msun/H**2)**(1/3)/Mpc
print(f"  Local Group turnaround (Gm/H^2)^(1/3) = {r_ta:.2f} Mpc  (observed zero-velocity ~ 1 Mpc)")
if not 0.5 < r_ta < 3: ok = False
print("PASS" if ok else "FAIL", "- weak-acceleration floor")
