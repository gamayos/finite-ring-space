# Construction 1 deep-regime experiment (LABELLED stochastic/continuum approximation;
# the framed-rational reading is a random walk on the finite phase cycle C_{p-1}).
# Noisy Kuramoto link (Adler eq):  dphi = (T - sin phi) dt + sqrt(2D) dW, kappa=1.
# T = mean phase gradient (the force), <sin phi> = transmitted flux. By the exact Gauss law
# the flux through a shell is the source demand g_N; so the force to carry g_N is the tilt T
# with <sin phi>(T)=g_N. We map (g_N=<sinphi>, g_eff=T) and read the deep-regime slope.
import numpy as np, json
def flux_of_tilt(T,D,K=3000,steps=5000,dt=0.02,seed=1):
    r=np.random.default_rng(seed); nb=steps//3
    phi=np.full(K,np.arcsin(min(T,0.999))); sq=np.sqrt(2*D*dt); a=0.0;c=0
    for i in range(steps):
        phi+=(T-np.sin(phi))*dt+sq*r.standard_normal(K)
        if i>=nb: a+=np.sin(phi).mean(); c+=1
    return a/c
out={}
for D in [0.3,0.6]:
    tilts=np.array([0.01,0.02,0.04,0.08,0.16,0.32])
    flux=np.array([flux_of_tilt(t,D,seed=11) for t in tilts])
    gN=flux; geff=tilts
    slope=np.polyfit(np.log(gN[:3]),np.log(geff[:3]),1)[0]
    boost=geff/gN
    out[D]={'gN':gN.tolist(),'geff':geff.tolist(),'slope':float(slope),'boost':boost.tolist()}
    print(f"D={D}: deep slope d ln g_eff/d ln g_N = {slope:.3f}  (Newtonian 1.0, MOND 0.5)")
    print("   boost g_eff/g_N =", np.round(boost,3), " ~ constant => Newtonian-shaped")
json.dump(out,open('deep.json','w'))

import matplotlib; matplotlib.use('Agg'); import matplotlib.pyplot as plt
fig,ax=plt.subplots(figsize=(5.4,4.2))
g=np.logspace(-2.4,-0.4,100)
for D,c in zip([0.3,0.6],['#1f77b4','#d62728']):
    d=out[D]; gN=np.array(d['gN']); geff=np.array(d['geff'])
    ax.loglog(gN,geff,'o',color=c,label=f'simulation, floor D={D} (slope {d["slope"]:.2f})')
a0=0.03
ax.loglog(g,g,'k--',lw=1,label='Newtonian  $g_{\\rm eff}=g_N$ (slope 1)')
ax.loglog(g,np.sqrt(g*a0),'g-',lw=1.4,label='deep-MOND  $g_{\\rm eff}=\\sqrt{g_N a_0}$ (slope 1/2)')
ax.set_xlabel('$g_N$  (capacity units)'); ax.set_ylabel('$g_{\\rm eff}$ (force / phase gradient)')
ax.set_title('Construction 1: mean noisy-Kuramoto dynamics is Newtonian-shaped')
ax.legend(fontsize=7,loc='upper left'); ax.grid(True,which='both',alpha=0.25)
fig.tight_layout(); fig.savefig('cons1_deepregime.pdf'); print("figure saved")
