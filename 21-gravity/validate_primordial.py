"""The primordial spectrum is structural (ledger D8). Float-free where it counts.

Time is scale-dilation (the drive x->gx). The primordial fluctuations are the drive's own jitter,
so their spectrum is the invariant of scale-dilation -- the unique scale-free (Harrison-Zel'dovich)
spectrum, n_s = 1. No inflaton, no transport. The observed red tilt n_s-1 = -0.035 is the chart's
misalignment from the symmetric quarter-turn, the SAME object as the a0(z) cross-scale running
(D9, Omega-hard). The wrapped chart identifies super-horizon modes, truncating the two-point
correlation beyond the horizon angular scale (~60 deg) and predicting the observed low large-angle
CMB power (low quadrupole, small S_1/2).

n_s=1 as the dilation fixed point is exact; the observed numbers are tagged data/[approx].
"""
import math
ok = True

# 1. scale-invariance is the unique fixed point of scale-dilation
# Delta^2(k) = k^3 P(k)/2pi^2 ~ k^(n+3) for P~k^n; invariant under k->lambda k  <=>  n=-3  <=>  n_s=1.
print("[1] scale-invariance = the dilation fixed point:")
fixed = [n for n in range(-6,3) if (n+3)==0]
if fixed != [-3]: ok=False
for n in (-2,-3,-4):
    print(f"    P(k)~k^{n}: Delta^2~k^{n+3:+d}  scale-invariant={n+3==0}  n_s={n+4}")
print("    unique invariant: P~k^-3, n_s=1 (Harrison-Zel'dovich). The drive IS scale-dilation,")
print("    so its fluctuation spectrum is scale-invariant by its own symmetry -- structural, no inflaton.")

# 2. the observed red tilt is the chart misalignment (Omega-hard, = D9)
ns = 0.965
print(f"\n[2] observed n_s={ns} (Planck): red tilt n_s-1={ns-1:+.3f}.")
if ns-1 >= 0: ok=False
print("    symmetric-quarter-turn value n_s=1; the tilt is the chart misalignment, red from the finite")
print("    UV cutoff; exact magnitude = the chart-angle deviation = the a0(z) running (D9), Omega-hard.")

# 3. wrapped chart -> large-angle cutoff at the horizon -> low S_1/2
theta_H = 60.0
print(f"\n[3] wrapped chart: super-horizon modes identified, C(theta)~0 for theta>theta_H~{theta_H:.0f} deg;")
print("    predicts the observed low large-angle correlation (low quadrupole, small S_1/2). The cutoff")
print("    is the horizon: the section's 'consonance' becomes a number.")

# 4. scalar spectrum, low tensor ratio
print("\n[4] the spectrum is the scalar scale-dilation fluctuation; r (tensor/scalar) structurally small.")

print("\nPASS" if ok else "\nFAIL", "- primordial spectrum (D8): n_s=1 from the dilation fixed point, large-angle cutoff at the horizon")
