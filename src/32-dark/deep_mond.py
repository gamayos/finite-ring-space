# Construction 2 (LABELLED continuum confrontation): the two-chart Gauss law.
# Conserved flux per shell = enclosed baryonic source (Gauss, exact, both charts).
#   position chart: registered force = flux            -> g_eff = g_bar      (Newtonian)
#   spectral chart: registered force = Born amplitude  -> g_eff = sqrt(g_bar*a0) (deep)
# crossover at the floor a0 = c H0 / 2pi (the outward scale horizon). The standard
# rotation-angle weighting gives the interpolation g_eff = g_bar/(1-exp(-sqrt(g_bar/a0))).
import numpy as np
c=2.998e8; G=6.674e-11; Msun=1.989e30; Mpc=3.0857e22; kpc=Mpc/1000
H0=70*1000/Mpc; a0=c*H0/(2*np.pi)
print(f"a0 = c H0/2pi = {a0:.3e} m/s^2  (RAR fit 1.20e-10)")

def g_eff(g_bar):                      # interpolation (deep slope 1/2, Newtonian limit)
    return g_bar/(1-np.exp(-np.sqrt(g_bar/a0)))

# RAR deep slope
gb=np.logspace(-13,-8,200); go=g_eff(gb)
deep=gb<1e-12
slope=np.polyfit(np.log(gb[deep]),np.log(go[deep]),1)[0]
print(f"RAR deep-regime slope d ln g_obs/d ln g_bar = {slope:.3f}  (target 0.5)")

# BTFR: flat-velocity vs mass, point-mass deep limit v^4 = G M a0
M=np.logspace(8,12,40)*Msun
vflat=(G*M*a0)**0.25
bt=np.polyfit(np.log(M),np.log(vflat),1)[0]
print(f"BTFR slope d ln v_flat/d ln M = {bt:.3f}  (target 0.25 -> v^4 ~ M)")
print(f"  M=5e10 Msun -> v_flat = {(G*5e10*Msun*a0)**0.25/1000:.0f} km/s")

# Rotation curve for an exponential disk, Sigma0 with scale length Rd
def disk_curve(Mdisk, Rd):
    r=np.linspace(0.1,30,300)*kpc
    x=r/(2*Rd)
    from scipy.special import i0,i1,k0,k1
    # exact exponential-disk Newtonian v_bar^2
    vb2=(G*Mdisk/Rd)*x**2*(i0(x)*k0(x)-i1(x)*k1(x))*2
    gbar=vb2/r
    gobs=g_eff(gbar)
    vobs=np.sqrt(gobs*r)
    return r/kpc, np.sqrt(vb2)/1000, vobs/1000
try:
    import scipy
    r,vb,vo=disk_curve(6e10*Msun,3*kpc)
    print(f"disk: baryonic v peaks {vb.max():.0f} km/s -> observed flattens at {vo[-50:].mean():.0f} km/s")
    have_disk=True
except Exception as e:
    have_disk=False; print("scipy unavailable, skipping disk curve panel")

import matplotlib; matplotlib.use('Agg'); import matplotlib.pyplot as plt
n=3 if have_disk else 2
fig,ax=plt.subplots(1,n,figsize=(4.2*n,3.6))
ax[0].loglog(gb,go,'b',label='two-chart interpolation')
ax[0].loglog(gb,gb,'k--',lw=0.8,label='Newtonian (slope 1)')
ax[0].loglog(gb,np.sqrt(gb*a0),'g-',lw=1,label='deep $\\sqrt{g_{bar}a_0}$ (slope 1/2)')
ax[0].axvline(a0,color='gray',ls=':',lw=0.8); ax[0].set_xlabel('$g_{bar}$'); ax[0].set_ylabel('$g_{obs}$')
ax[0].set_title('Radial acceleration relation'); ax[0].legend(fontsize=6)
ax[1].loglog(M/Msun,vflat/1000,'r'); ax[1].set_xlabel('$M_{bar}/M_\\odot$'); ax[1].set_ylabel('$v_{flat}$ [km/s]')
ax[1].set_title(f'Baryonic Tully-Fisher (slope {bt:.2f})')
if have_disk:
    ax[2].plot(r,vb,'k--',label='baryonic'); ax[2].plot(r,vo,'b',label='observed (two-chart)')
    ax[2].set_xlabel('r [kpc]'); ax[2].set_ylabel('v [km/s]'); ax[2].set_title('Rotation curve (exp. disk)'); ax[2].legend(fontsize=7)
fig.tight_layout(); fig.savefig('cons2_rar_btfr.pdf'); print("figure saved")
