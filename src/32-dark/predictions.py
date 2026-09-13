#!/usr/bin/env python3
# =====================================================================
#  predictions.py -- quantify the additional falsifiable predictions of
#  the finite-substrate dark sector (beyond the RAR/BTFR/EFE already in
#  the paper).  Each is DERIVED from the construction, not fitted.
# =====================================================================
import numpy as np
c=2.998e8; G=6.674e-11; Msun=1.989e30; AU=1.496e11; Mpc=3.086e22
H0=70*1000/Mpc; a0=c*H0/(2*np.pi)
nu=lambda y:1.0/(1-np.exp(-np.sqrt(y)))
Ez=lambda z,Om=0.3,OL=0.7:np.sqrt(Om*(1+z)**3+OL)
def hr(t): print("\n"+"="*70+"\n"+t+"\n"+"="*70)
print(f"a0 = c H0/2pi = {a0:.3e} m/s^2")

# ---------------------------------------------------------------------
# A. Cosmic evolution: a0(z)=cH(z)/2pi  =>  BTFR zero-point and RAR knee
#    shift with redshift.  At fixed baryonic mass, v_flat ~ a0^{1/4}, so
#    v_flat(z)/v_flat(0) = E(z)^{1/4}; the knee sits at cH(z)/2pi.
# ---------------------------------------------------------------------
hr("A. a0(z)=cH(z)/2pi: BTFR zero-point and knee evolution (parameter-free)")
print(f"  {'z':>4} {'E(z)':>7} {'a0(z)/a0':>9} {'v_flat(z)/v0 = E^1/4':>22}")
for z in (0.0,0.5,1.0,1.5,2.0):
    print(f"  {z:>4.1f} {Ez(z):>7.3f} {Ez(z):>9.3f} {Ez(z)**0.25:>22.3f}")
print("  => at fixed M_bar, high-z disks rotate faster by E(z)^1/4: +7% (z=.5), +15% (z=1), +31% (z=2);")
print("     the RAR transition shifts to a0(z)=cH(z)/2pi.  MOND (constant a0) predicts no shift.")

# ---------------------------------------------------------------------
# B. Two-variable RAR scatter:  sigma_log g = (2 tan a /ln10) arctan(sv/v)
#    tan a(x) = sqrt(e^{-sqrt x}/(1-e^{-sqrt x})).  -> 0 for cold and for x->inf;
#    rises as x^{-1/4} deep.  A definite surface over (x, sv/v).
# ---------------------------------------------------------------------
hr("B. two-variable RAR scatter sigma(x, sv/v) [dex]")
tana=lambda x:np.sqrt(np.exp(-np.sqrt(x))/(1-np.exp(-np.sqrt(x))))
sig=lambda x,r:(2*tana(x)/np.log(10))*np.arctan(r)
print(f"  {'x=g/a0':>8} | sv/v=0.05  0.10  0.20   (dex)")
for x in (100,10,1,0.1,0.01):
    row=" ".join(f"{sig(x,r):6.3f}" for r in (0.05,0.10,0.20))
    print(f"  {x:>8.2f} |  {row}")
print("  => tightest locus = cold (sv/v->0), high-acceleration (x->inf) disks (sigma->0);")
print("     deep regime scatter rises to ~0.27 dex (x~0.01, sv/v=0.1): a SHARP test deep,")
print("     where the intro's 0.11 dex is only the knee value.")

# ---------------------------------------------------------------------
# C. Wide binaries in the deep regime, WITH the Galactic external field.
#    Solar-neighbourhood g_ext ~ 1.8 a0; the vector total field sets nu.
# ---------------------------------------------------------------------
hr("C. wide binaries: g_obs/g_b with a0=cH0/2pi and the Galactic EFE")
gext=1.8*a0                          # Milky-Way field at the Sun, ~1.8 a0
print(f"  {'s[kAU]':>7} {'g_b/a0':>8} {'nu (isolated)':>14} {'nu (with EFE)':>14}")
for skAU in (3,5,10,20,40):
    s=skAU*1000*AU; gb=G*(1.5*Msun)/s**2   # ~1.5 Msun total
    y_iso=gb/a0; y_efe=(gb+gext)/a0
    print(f"  {skAU:>7d} {y_iso:>8.3f} {nu(y_iso):>14.3f} {nu(y_efe):>14.3f}")
print("  => isolated binaries would show ~2x enhancement deep; the real Galactic EFE (g_ext~1.8a0)")
print("     suppresses it to ~10-30% at s>~10 kAU -- the FRC-specific Gaia wide-binary prediction,")
print("     exponential knee distinct from Newtonian (1.0) and from rational-MOND.")

# ---------------------------------------------------------------------
# D. Pressure-supported coherence offset: hot systems (large sv/v) have a
#    lower bulk-coherence fraction w = cos^2(arctan(sv/v)) = 1/(1+(sv/v)^2),
#    so a reduced amplitude -> they sit at/below the cold-disk RAR.
# ---------------------------------------------------------------------
hr("D. pressure-supported coherence offset: w=1/(1+(sv/v)^2)")
print(f"  {'sv/v':>6} {'coherence w':>12} {'amp factor sqrt(w)':>18} {'offset [dex]':>14}")
for r in (0.05,0.1,0.2,0.5,1.0):
    w=1/(1+r**2); print(f"  {r:>6.2f} {w:>12.3f} {np.sqrt(w):>18.3f} {np.log10(np.sqrt(w)):>14.3f}")
print("  => cold disks (sv/v~0.1) lose <1%; hot dSph/UDG cores (sv/v~0.5-1) sit 0.05-0.15 dex BELOW")
print("     the cold-disk RAR, correlating with sv/v.  MOND predicts the same RAR for all states.")

hr("SUMMARY: falsifiers")
print("""  A  high-z RAR knee != cH(z)/2pi, or BTFR zero-point not ~E(z)^1/4  -> fails
  B  RAR scatter not rising as x^-1/4 deep, or not tracking sv/v        -> fails
  C  wide-binary motion Newtonian (no deep enhancement) or wrong knee   -> fails
  D  pressure-supported systems on the same RAR as cold disks           -> fails""")
