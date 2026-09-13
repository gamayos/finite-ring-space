#!/usr/bin/env python3
# =====================================================================
#  make_figures.py -- dark-sector figures.
#
#  The figure set:
#
#   fig_rar.pdf        (phenomenology):  RAR (with the rational-alt knee
#                       and both asymptotes)  |  exponential-disk rotation curve
#   fig_mechanism.pdf  (first principles): meridian first-passage collapse
#                       (walk -> e^{-a sqrt(2s)})  |  chart angle alpha(x)
#
#  The BTFR (v^4=GM a0) is a one-line corollary and stays in the text.
# =====================================================================
import numpy as np
import matplotlib; matplotlib.use('Agg'); import matplotlib.pyplot as plt

plt.rcParams.update({'font.size':10,'axes.titlesize':10,'axes.labelsize':10,
                     'legend.fontsize':8,'xtick.labelsize':8.5,'ytick.labelsize':8.5})

c=2.998e8; G=6.674e-11; Msun=1.989e30; kpc=3.086e19; Mpc=1000*kpc
a0=c*(70*1000/Mpc)/(2*np.pi)
nu     =lambda x:1.0/(1-np.exp(-np.sqrt(x)))          # derived = McGaugh RAR fit
nu_rat =lambda x:0.5*(1+np.sqrt(1+4.0/x))             # 'simple' rational alt (same limits)
alpha  =lambda x:np.arcsin(np.sqrt(np.exp(-np.sqrt(x))))

# ---------------------------------------------------------------------
# FIGURE 1 -- galactic phenomenology: RAR | rotation curve
# ---------------------------------------------------------------------
fig,ax=plt.subplots(1,2,figsize=(9.6,4.0))

gb=np.logspace(-13,-8,400)               # baryonic acceleration, m/s^2
x=gb/a0
ax[0].loglog(gb, gb*nu(x), 'b', lw=1.8, label=r'two-chart $g_{\rm obs}=g_{\rm bar}/(1-e^{-\sqrt{x}})$')
ax[0].loglog(gb, gb, 'k--', lw=0.9, label='Newtonian (slope 1)')
ax[0].loglog(gb, np.sqrt(gb*a0), 'g-.', lw=1.0, label=r'deep $\sqrt{g_{\rm bar}a_0}$ (slope $\frac{1}{2}$)')
ax[0].loglog(gb, gb*nu_rat(x), color='m', ls=':', lw=1.3, label=r'rational $\mu$ (alt. knee)')
ax[0].axvline(a0,color='gray',ls=':',lw=0.8); ax[0].text(a0*1.15,1.5e-13,r'$a_0$',color='gray',fontsize=9)
ax[0].set_xlabel(r'$g_{\rm bar}\ \mathrm{[m\,s^{-2}]}$'); ax[0].set_ylabel(r'$g_{\rm obs}\ \mathrm{[m\,s^{-2}]}$')
ax[0].set_title('Radial acceleration relation'); ax[0].legend(loc='upper left'); ax[0].set_xlim(1e-13,1e-8)

from scipy.special import i0,i1,k0,k1
Mdisk,Rd=5e10*Msun,3*kpc
r=np.linspace(0.1,30,300)*kpc; xd=r/(2*Rd)
vb2=(G*Mdisk/Rd)*xd**2*(i0(xd)*k0(xd)-i1(xd)*k1(xd))*2
gbar=vb2/r; vobs=np.sqrt(r*gbar*nu(gbar/a0))
ax[1].plot(r/kpc, np.sqrt(vb2)/1000, 'k--', lw=1.1, label='baryonic')
ax[1].plot(r/kpc, vobs/1000, 'b', lw=1.8, label='registered (two-chart)')
ax[1].set_xlabel('$r$ [kpc]'); ax[1].set_ylabel('$v$ [km s$^{-1}$]')
ax[1].set_title(r'Rotation curve (exponential disk, $5\times10^{10}M_\odot$)')
ax[1].legend(loc='lower right'); ax[1].set_ylim(0,None)
fig.tight_layout(); fig.savefig('../figures/fig_rar.pdf'); print("fig_rar.pdf saved")

# ---------------------------------------------------------------------
# FIGURE 2 -- the interpolation from first principles:
#             first-passage collapse | chart angle
# ---------------------------------------------------------------------
fig,ax=plt.subplots(1,2,figsize=(9.6,4.0))

def escape_prob(a,q,trials=20000,seed=0):
    rng=np.random.default_rng(seed); esc=0
    for _ in range(trials):
        pos=0
        while True:
            if rng.random()<q: break
            pos+=1 if rng.random()<0.5 else -1
            if pos>=a: esc+=1; break
    return esc/trials
pts=[]
for a in (3,5,8,10):
    for q in (0.01,0.02,0.04):
        pts.append((a*np.sqrt(2*q), escape_prob(a,q,seed=a*100+int(q*1000))))
pts=np.array(pts); u=np.linspace(0,3,100)
ax[0].plot(pts[:,0],pts[:,1],'o',ms=5,color='steelblue',label='killed-walk simulation')
ax[0].plot(u,np.exp(-u),'r-',lw=1.6,label=r'$e^{-A}$, $A=a\,\sqrt{2s}=\sqrt{x}$')
ax[0].set_xlabel(r'$A=a\,\sqrt{2s}$'); ax[0].set_ylabel('escape (non-registration) prob.')
ax[0].set_title('Meridian first-passage law (Prop. 3)'); ax[0].legend(loc='upper right')

xx=np.logspace(-3,3,400)
ax[1].semilogx(xx, np.degrees(alpha(xx)), 'r', lw=1.8)
ax[1].axhline(45,color='gray',ls=':',lw=0.7); ax[1].axhline(37,color='gray',ls=':',lw=0.5)
ax[1].axvline(1,color='gray',ls=':',lw=0.7); ax[1].text(1.3,5,r'$a_0$',color='gray',fontsize=9)
ax[1].text(1e-3*1.4,40,r'spectral',fontsize=8,color='dimgray'); ax[1].text(1e2,6,r'coordinate',fontsize=8,color='dimgray')
ax[1].set_xlabel(r'$x=g_{\rm bar}/a_0$'); ax[1].set_ylabel(r'chart angle $\alpha$ [deg]')
ax[1].set_title(r'Chart angle: $\sin^2\alpha=e^{-\sqrt{x}}$ ($0^\circ$ space, $90^\circ$ spectrum)')
ax[1].set_ylim(0,92)
fig.tight_layout(); fig.savefig('../figures/fig_mechanism.pdf'); print("fig_mechanism.pdf saved")
