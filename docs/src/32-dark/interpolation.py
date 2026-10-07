# Construction 3: the interpolation shape from the Fourier rotation angle and the first-passage registration.
# Inputs:  (a) two charts space<->spectrum, FrFT angle a = (pi/2)(s/chi), s in Z_{4chi}  [6-fourier]
#          (b) spectral reading = Born amplitude, SNR = sqrt(x), x=g_bar/a0               [Constr.2, Z[i]]
#          (c) registration = first passage of the killed meridian walk to the AMPLITUDE barrier
#              (row B8, the one declared identification): f = 1 - e^{-sqrt(x)}             [Prop. passage]
#          (d) Gauss flux conservation: registered force = g_bar / f                       [Constr.1]
# Output:  g_obs = g_bar / (1 - e^{-sqrt(x)}); the fitting function of McGaugh-Lelli-Schombert 2016 is
#          this form with the fitted g_dagger in place of the derived a0 (a statement about which function
#          the data selected, not a check: the earlier "identity check" compared the form with itself and
#          was removed, 2026-09-12).  What is computed here instead:
#            1. the discriminant against the simple rational interpolant nu = (1+sqrt(1+4/x))/2
#               (same limits, different approach to Newton): where it is and how large;
#            2. the two pinning checks of row B8: for a barrier kappa*x^beta the deep slope is 1-beta
#               (so beta=1/2 is the Tully-Fisher fourth power), and kappa != 1 is a knee at a0/kappa^2.
import numpy as np
def nu_frc(x):    return 1.0/(1-np.exp(-np.sqrt(x)))          # derived given B8
def nu_simple(x): return 0.5*(1+np.sqrt(1+4.0/x))            # 'simple' mu alternative, same limits
def nu_gen(x,kappa=1.0,beta=0.5): return 1.0/(1-np.exp(-kappa*x**beta))

x=np.logspace(-3,3,4000)
# limits / slopes
deep=x<1e-2; newt=x>1e2
gobs=x*nu_frc(x)   # in units of a0
sl_deep=np.polyfit(np.log(x[deep]),np.log(gobs[deep]),1)[0]
sl_newt=np.polyfit(np.log(x[newt]),np.log(gobs[newt]),1)[0]
print(f"deep slope {sl_deep:.3f} (->1/2), Newtonian slope {sl_newt:.3f} (->1)")

# 1. discriminant against the simple interpolant
d=nu_simple(x)-nu_frc(x); i=int(np.argmax(d))
print(f"discriminant nu_simple - nu_frc: max {d[i]:.4f} in g_obs/g_b ({np.log10(nu_simple(x[i])/nu_frc(x[i])):.4f} dex) at x = {x[i]:.2f}")
print("   x      nu_frc  nu_simple   diff    dex")
for xx in (0.1,0.3,1,2,3,5,8,10,20,100):
    a,b=nu_frc(xx),nu_simple(xx); print(f"{xx:7.2f} {a:8.3f} {b:9.3f} {b-a:8.4f} {np.log10(b/a):7.4f}")
band=(x>2)&(x<10); print(f"over 2 < x < 10: {d[band].min():.3f} .. {d[band].max():.3f};  below x = 0.3: < {d[x<0.3].max():.3f}")

# 2. pinning checks (row B8)
xd=np.logspace(-4,-2,60)
for beta in (0.4,0.5,0.6):
    g=xd*nu_gen(xd,1.0,beta); print(f"barrier x^{beta}: deep slope {np.polyfit(np.log(xd),np.log(g),1)[0]:.3f} = 1 - beta")
target=nu_frc(1.0)
for kappa in (1.0,0.93,1.1):
    xs=np.logspace(-1,1,20001); k=int(np.argmin(np.abs(nu_gen(xs,kappa)-target)))
    print(f"barrier {kappa}*sqrt(x): knee (nu = nu_frc(1)) at x = {xs[k]:.3f}  vs 1/kappa^2 = {1/kappa**2:.3f}")

# rotation angle and discrete meridian index s for a sample shell
def alpha(x): return np.arcsin(np.sqrt(np.exp(-np.sqrt(x))))  # sin^2 a = e^{-sqrt x}
for chi in (3, 30, 1000):                 # p=4chi+1 shells; s in {0..chi} over space->spectrum
    print(f"  chi={chi:4d}: x=10  -> a={np.degrees(alpha(10.)):5.1f} deg, s={chi*2/np.pi*alpha(10.):7.2f};"
          f"  x=0.1 -> a={np.degrees(alpha(0.1)):5.1f} deg, s={chi*2/np.pi*alpha(0.1):7.2f}")
for xx in (0.01,0.1,1,10,100):
    m=np.sqrt(xx); print(f"   x={xx:6.2f}: SNR=sqrt(x)={m:6.3f}  P_resolve=1-e^-SNR={1-np.exp(-m):.3f}  nu={nu_frc(xx):.3f}")

import matplotlib; matplotlib.use('Agg'); import matplotlib.pyplot as plt
fig,ax=plt.subplots(1,2,figsize=(9,3.7))
ax[0].loglog(x, x*nu_frc(x),'b',label='derived (given B8) $g_{bar}/(1-e^{-\\sqrt{x}})$')
ax[0].loglog(x, x*nu_simple(x),'m--',lw=0.8,label="'simple' $\\mu$ (alt. shape)")
ax[0].loglog(x,x,'k:',lw=0.7,label='Newtonian'); ax[0].loglog(x,np.sqrt(x),'g:',lw=0.7,label='deep $\\sqrt{x}$')
ax[0].axvline(1,color='gray',ls=':',lw=0.6); ax[0].set_xlabel('$x=g_{bar}/a_0$'); ax[0].set_ylabel('$g_{obs}/a_0$')
ax[0].set_title('Interpolation from the rotation angle'); ax[0].legend(fontsize=6.5)
ax[1].semilogx(x, np.degrees(alpha(x)),'r'); ax[1].axhline(45,color='gray',ls=':',lw=0.6)
ax[1].set_xlabel('$x=g_{bar}/a_0$'); ax[1].set_ylabel('FrFT angle $\\alpha$ [deg]')
ax[1].set_title('Chart angle: $\\sin^2\\alpha=e^{-\\sqrt{x}}$ (0=space, 90=spectrum)')
fig.tight_layout(); fig.savefig('cons3_interpolation.pdf'); print("figure saved")
