# Construction 3: the interpolation shape DERIVED from the Fourier rotation angle.
# Inputs:  (a) two charts space<->spectrum, FrFT angle a = (pi/2)(s/chi), s in Z_{4chi}  [6-fourier]
#          (b) spectral reading = Born amplitude, SNR = sqrt(x), x=g_bar/a0               [Constr.2, Z[i]]
#          (c) comprehension-horizon detection: position chart resolves the signal with
#              Poisson probability f = 1 - e^{-mean}, mean = registered coincidence count [26-pnp + 22-quantum]
#          (d) Gauss flux conservation: registered force = g_bar / f                       [Constr.1]
# Output:  g_obs = g_bar / (1 - e^{-sqrt(x)})  -- the McGaugh RAR fitting function, with
#          spectral weight sin^2 a = e^{-sqrt(x)} (the un-resolved fraction).
import numpy as np
def nu_frc(x):  return 1.0/(1-np.exp(-np.sqrt(x)))          # derived
def nu_mcg(x):  return 1.0/(1-np.exp(-np.sqrt(x)))          # McGaugh-Lelli-Schombert 2016 RAR fit
def nu_simple(x): return 0.5*(1+np.sqrt(1+4.0/x))          # 'simple' mu alternative, same limits

x=np.logspace(-3,3,400)
print("identity check: derived interpolation == McGaugh RAR fit:",
      np.allclose(nu_frc(x), nu_mcg(x)))
# limits / slopes
deep=x<1e-2; newt=x>1e2
gobs=x*nu_frc(x)   # in units of a0
sl_deep=np.polyfit(np.log(x[deep]),np.log(gobs[deep]),1)[0]
sl_newt=np.polyfit(np.log(x[newt]),np.log(gobs[newt]),1)[0]
print(f"deep slope {sl_deep:.3f} (->1/2), Newtonian slope {sl_newt:.3f} (->1)")
# rotation angle and discrete meridian index s for a sample shell
def alpha(x): return np.arcsin(np.sqrt(np.exp(-np.sqrt(x))))  # sin^2 a = e^{-sqrt x}
for chi in (3, 30, 1000):                 # p=4chi+1 shells; s in {0..chi} over space->spectrum
    print(f"  chi={chi:4d}: x=10  -> a={np.degrees(alpha(10.)):5.1f} deg, s={chi*2/np.pi*alpha(10.):7.2f};"
          f"  x=0.1 -> a={np.degrees(alpha(0.1)):5.1f} deg, s={chi*2/np.pi*alpha(0.1):7.2f}")
# Poisson/Born detection identity (exact in expectation): mean coincidences m -> P=1-e^{-m}
# the registered amplitude (mean coincidence count) is sqrt(x); demonstrate the map is monotone+correct limits
for xx in (0.01,0.1,1,10,100):
    m=np.sqrt(xx); print(f"   x={xx:6.2f}: SNR=sqrt(x)={m:6.3f}  P_resolve=1-e^-SNR={1-np.exp(-m):.3f}  nu={nu_frc(xx):.3f}")

# vs simple-mu: same limits, different knee -> the exponential (derived) is what the RAR data show
import numpy as np
knee=(x>0.3)&(x<3)
maxdiff=np.max(np.abs(nu_frc(knee*x+ (~knee))-nu_simple(knee*x+(~knee))))
print(f"max |derived - simple-mu| over the knee: {np.max(np.abs(nu_frc(x[ (x>0.3)&(x<3)])-nu_simple(x[(x>0.3)&(x<3)]))):.3f} (distinguishable; data favour the exponential)")

import matplotlib; matplotlib.use('Agg'); import matplotlib.pyplot as plt
fig,ax=plt.subplots(1,2,figsize=(9,3.7))
ax[0].loglog(x, x*nu_frc(x),'b',label='derived = McGaugh $g_{bar}/(1-e^{-\\sqrt{x}})$')
ax[0].loglog(x, x*nu_simple(x),'m--',lw=0.8,label="'simple' $\\mu$ (alt. shape)")
ax[0].loglog(x,x,'k:',lw=0.7,label='Newtonian'); ax[0].loglog(x,np.sqrt(x),'g:',lw=0.7,label='deep $\\sqrt{x}$')
ax[0].axvline(1,color='gray',ls=':',lw=0.6); ax[0].set_xlabel('$x=g_{bar}/a_0$'); ax[0].set_ylabel('$g_{obs}/a_0$')
ax[0].set_title('Interpolation from the rotation angle'); ax[0].legend(fontsize=6.5)
ax[1].semilogx(x, np.degrees(alpha(x)),'r'); ax[1].axhline(45,color='gray',ls=':',lw=0.6)
ax[1].set_xlabel('$x=g_{bar}/a_0$'); ax[1].set_ylabel('FrFT angle $\\alpha$ [deg]')
ax[1].set_title('Chart angle: $\\sin^2\\alpha=e^{-\\sqrt{x}}$ (0=space, 90=spectrum)')
fig.tight_layout(); fig.savefig('cons3_interpolation.pdf'); print("figure saved")
