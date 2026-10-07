# framed-rational status: MIXED -- exact framed-rational core; continuum constructs are confined to clearly-labelled [approx] / degenerate-idealisation comparisons (Tier 2/3/5 or measured-data), never to an exact claim.
"""
P2: the order-one coefficient of the bare electromagnetic coupling.

Claim: the coefficient is exactly 1, alpha_bare = 1/(4pi), with NO open order-one
factor, because (i) channel unity makes the EM connection stiffness beta equal to
the one per-cell capacity kappa, (ii) that unit capacity is the action quantum
hbar, and (iii) charge = winding index = one phase quantum (EM-1), so in natural
units the elementary charge is 1 and alpha_bare = e^2/4pi = 1/4pi.

We back this with the saturation-regime computation (the EM analogue of gravity's
exact static profile): the capacity-bounded Gauss law 4 pi r^2 kappa sin(E) = q
gives the weak-field Coulomb coefficient 1/(4 pi kappa), an EM saturation core
r* = sqrt(q/4 pi kappa), and a FINITE charge self-energy -- the classical
self-energy divergence cut off by the same capacity bound that gives gravity its
slip core.  The 4pi is the 3-D Gauss solid angle (continuum-comparison reading).
"""
import math

print("=" * 68)
print("P2  the bare electromagnetic coupling coefficient")
print("=" * 68)

# ---- (1) the coefficient from channel unity -------------------------------
print("\n(1) coefficient from channel unity + charge=action=phase quantum")
print("    gravity:  G_shell      = 1/(4 pi kappa),  kappa = 1   (unit capacity)")
print("    EM:       Coulomb coef = 1/(4 pi beta),   beta  = kappa = 1  (channel unity)")
print("    charge quantum = action quantum = one phase quantum => e = 1 (natural units)")
alpha_bare = 1/(4*math.pi)
print(f"    => alpha_bare = e^2/(4 pi) = 1/(4 pi) = {alpha_bare:.6f}   (coefficient = 1)")

# ---- (2) saturation-regime profile: weak-field coefficient ----------------
# capacity-bounded Gauss law:  4 pi r^2 kappa sin(E(r)) = q   (kappa=1, q=1)
# weak field:  E(r) ~ q/(4 pi r^2),  potential A0(r) = integral_r^inf E dr'
def E_field(r, q=1.0, kappa=1.0):
    x = q/(4*math.pi*kappa*r**2)
    return math.asin(x) if x <= 1.0 else None          # undefined inside the core
def A0(r, q=1.0, kappa=1.0, R=1e4, n=200000):
    # potential = integral_r^R of E dr'  (R large)
    h = (R-r)/n; s = 0.0
    for i in range(n):
        rr = r + (i+0.5)*h; e = E_field(rr, q, kappa)
        s += e*h
    return s
print("\n(2) saturation profile  4 pi r^2 sin(E)=q  -> weak-field Coulomb coefficient")
for r in (5.0, 10.0, 20.0):
    a0 = A0(r); coef = a0*r
    print(f"    r={r:5.1f}:  r*A0(r) = {coef:.5f}   (-> 1/4pi = {alpha_bare:.5f})")

# ---- (3) the EM saturation core and a finite self-energy ------------------
q = kappa = 1.0
rstar = math.sqrt(q/(4*math.pi*kappa))                 # where sin(E)=1
print(f"\n(3) EM saturation core  r* = sqrt(q/4 pi kappa) = {rstar:.5f}  (shell units)")
# self-energy with the capacity bound: U = int_{r*}^inf (1/2) E^2 4 pi r^2 dr (finite),
# vs continuum int_0^inf which diverges at r->0.
def self_energy(rmin, R=1e4, n=400000):
    h=(R-rmin)/n; s=0.0
    for i in range(n):
        rr=rmin+(i+0.5)*h; e=E_field(rr,q,kappa)
        if e is None: continue
        s += 0.5*e*e*4*math.pi*rr*rr*h
    return s
U_cut = self_energy(rstar)
# continuum (no cutoff, no saturation): (1/2)(q/4pi r^2)^2 4pi r^2 = q^2/(8 pi r^2)
# integral_{eps}^inf = q^2/(8 pi eps)  -> diverges as eps->0
print(f"    finite self-energy U(>r*) = {U_cut:.5f}   (continuum int_0 DIVERGES)")
print(f"    continuum q^2/(8 pi r*)   = {q*q/(8*math.pi*rstar):.5f}  (same order, finite)")
print("    => the capacity bound cuts off the classical self-energy divergence,")
print("       the EM analogue of gravity's horizonless slip core.")

# ---- (4) honest separation from the running ------------------------------
print("\n(4) the residual to the measured value is NOT a bare-coefficient ambiguity")
print(f"    1/alpha_bare = 4 pi = {4*math.pi:.4f}      (coefficient fixed = 1)")
print(f"    1/alpha(0)   = 137.036                  (running P1 + EW mixing)")
print("    P2 closes the bare coefficient; the gap is P1 (running) + the Weinberg")
print("    mixing, both separate problems.  EM's bare coupling is MORE constrained")
print("    than gravity's open order-one constants (a0's 2pi, the entropy c_S'),")
print("    because channel unity locks it to hbar.")
print("=" * 68)
