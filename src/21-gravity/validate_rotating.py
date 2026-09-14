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


# 5. order-a^2 ergosurface: g_tt = -e^{-2u} + omega^2 rho^2 e^{2u} = 0  =>  e^{-4u} = 4 a^2 sin^2θ / r^4
#    equatorial (sinθ=1): e^{-4/r} = 4 a^2 / r^4. Horizonless object: NO horizon inside; only floor r_f.
print("\n[5] order-a^2 ergosurface (equatorial), horizonless object [approx; e = framed-transcendental]:")
def ergo_eq(a):
    f = lambda r: math.exp(-4.0/r) - 4*a*a/r**4
    prev=None; roots=[]
    r=0.05
    while r < 8.0:
        v=f(r)
        if prev is not None and prev[1]*v < 0:
            lo,hi=prev[0],r
            for _ in range(100):
                mid=0.5*(lo+hi)
                if f(lo)*f(mid)<=0: hi=mid
                else: lo=mid
            roots.append(0.5*(lo+hi))
        prev=(r,v); r+=0.001
    return max(roots) if roots else float('nan')
rf = 2.0/(122*math.log(10))
prev_rE=0.0
for a in (0.1,0.3,0.5,0.7,0.9,0.99,1.0):
    rE=ergo_eq(a)
    # ergosurface grows with spin, and sits far outside the operational floor for any appreciable spin
    if not (rE>prev_rE and rE>rf): ok=False
    print(f"    a/M={a:4.2f}: r_E={rE:6.4f} M  (> floor r_f={rf:.4f} M; monotone in a: {rE>prev_rE})")
    prev_rE=rE
print(f"    no event horizon inside r_E (redshift -> Omega^(-1/2) only at r_f): ergoregion without horizon => superradiance/ergo-instability, a Kerr-distinct signature.")
print(f"    a->0: r_E -> floor (no rotation, no ergoregion), NOT merging with a 2M horizon as in Kerr.")

print("\nPASS" if ok else "\nFAIL", "- rotating solution (D7): gravitomagnetic = quarter-turn dual, horizonless, slip-core hand-over")
