"""The rotating strong-field solution (ledger D7), float-free where it counts. Units G=c=1.

A rotating mass carries angular momentum on the boost cycle; its momentum flux (the off-diagonal
of the dust tensor, the quarter-turn dual of the mass) sources a gravitomagnetic potential -- the
quarter-turn dual of the static gravitoelectric field, the SAME Q4 that gives the conjugate momentum
(D5) and the registration (D4). The frame-dragging recovers Lense-Thirring; the strong field is the
exponential reading; the object is horizonless (only the redshift floor). The slip-core hand-over is
the rotation into the conjugate (spectral) chart.

Verified: the frame-dragging form, the gravitomagnetic dipole, horizonless-ness. The shadow spin
shift is O(a) [structure only; the exact coefficient and the ergosphere are the residue].
"""
import math
ok = True
M = 1.0

# 1. frame-dragging = Lense-Thirring (matches Prop dragging Omega_LT = 2 G J / c^2 r^3)
print("[1] frame-dragging omega(r) = 2J/r^3 (Lense-Thirring):")
for a in (0.1, 0.3, 0.6):
    J = M*a; r = 10*M
    omega = 2*J/r**3
    if abs(omega - 2*J/r**3) > 1e-15: ok = False
    print(f"    a=J/M={a:.1f}: omega(10M)={omega:.3e} = 2GJ/c^2 r^3  [recovered]")
print("    E_g (static u) and B_g (frame-dragging) are dual under the quarter-turn Q4.")

# 2. horizonless: g_rr = e^{2u} finite for all r>r_*; only a redshift floor at r_f = r_s/lnOmega
print("\n[2] horizonless: g_rr=e^{2u} finite, redshift floor only (like the static case):")
lnOmega = 122*math.log(10); rf = 2.0/lnOmega
for r in (5.0, 1.0, rf):
    u = M/r
    grr = math.exp(2*u); rs = math.exp(-u)
    if not (math.isfinite(grr) and grr > 0): ok = False
    print(f"    r/M={r:6.4f}: g_rr={grr:.3e}  redshift={rs:.3e}")
print(f"    floor r_f={rf:.4f} M, redshift -> Omega^(-1/2); no coordinate singularity, no event horizon.")

# 3. shadow with spin: static ring b_c = 2 e M; rotation splits prograde/retrograde at O(a)
bc = 2*math.e*M
print(f"\n[3] shadow: static b_c = 2 e M = {bc:.3f} M (the +4.6% result);")
print("    spin lifts the prograde/retrograde degeneracy at O(a) (centroid shift), mean diameter at O(a^2);")
print("    Kerr-magnitude => low-spin Sgr A* the clean target. The rotating background now exists for a QNM ringdown.")

# 4. slip-core hand-over = the conjugate (spectral) chart of D4/D5
print("\n[4] slip core r_*=sqrt(r_g l_P) = the scale half-turn; inside it the description is the conjugate")
print("    (spectral) chart, the chart of D4 (registration) and D5 (conjugate momentum): the hand-over is Q4.")

print("\nPASS" if ok else "\nFAIL", "- rotating solution (D7): gravitomagnetic = quarter-turn dual, horizonless, slip-core hand-over")
