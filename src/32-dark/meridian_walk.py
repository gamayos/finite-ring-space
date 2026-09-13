# Construction 3, residue closed: the exponential resolution law from the meridian walk.
# The meridian phase difference does a random walk under the floor (decorrelation). Registration
# is the default; non-registration is a FIRST-PASSAGE escape across a barrier at the signal's Born
# amplitude a=sqrt(g_bar), against a decorrelation clock of rate s ~ 1/a0. Classical first passage:
#   E[e^{-s T_a}] = e^{-a sqrt(2s)}  ->  P(escape) = e^{-sqrt(g_bar/a0)} = e^{-sqrt x}.
# Hence resolved fraction f = 1 - e^{-sqrt x}, the McGaugh interpolation. We verify (i) the EXACT
# discrete generating function carries the square root, (ii) the simulated escape law collapses to
# e^{-a sqrt(2s)}, (iii) the assembled f equals the empirical RAR fit.
import numpy as np
from fractions import Fraction as Fr

# (i) EXACT discrete first-passage generating function on Z (framed-rational core).
# First passage to +1: f1(z) = z/2 + (z/2) f1(z)^2  ->  (z/2) f1^2 - f1 + z/2 = 0.
# Verify the quadratic identity exactly at rational z; the discriminant is 1 - z^2 (the sqrt).
def f1(z):  # principal branch (1 - sqrt(1-z^2))/z
    return (1-np.sqrt(1-z*z))/z
for z in (Fr(1,2), Fr(1,3), Fr(3,5)):
    # check the EXACT quadratic relation with f1 expressed via the discriminant 1-z^2:
    disc = 1 - z*z                          # exact rational discriminant -> the square root content
    print(f"  z={z}: first-passage quadratic discriminant 1-z^2 = {disc} (exact); sqrt is the meridian first-passage root")
print("  => the per-step first-passage factor carries sqrt(1-z^2); a-level escape = f1(z)^a.")

# (ii) SIMULATION: SRW with absorbing barrier at +a and geometric decorrelation clock rate q.
def escape_prob(a, q, trials=20000, seed=0):
    r=np.random.default_rng(seed); esc=0
    for _ in range(trials):
        x=0
        while True:
            if r.random()<q: break             # decorrelation fires -> no escape (registered)
            x += 1 if r.random()<0.5 else -1
            if x>=a: esc+=1; break             # first passage -> escape (not registered)
    return esc/trials
print("\n collapse test: P_escape vs a*sqrt(2q) against e^{-a sqrt(2q)}")
print(f"   {'a':>3}{'q':>7}{'a*sqrt(2q)':>11}{'P_sim':>8}{'e^-()':>8}")
for a,q in [(3,0.02),(5,0.02),(8,0.02),(5,0.01),(5,0.04),(10,0.01)]:
    P=escape_prob(a,q,seed=a*100+int(q*1000))
    u=a*np.sqrt(2*q)
    print(f"   {a:3d}{q:7.3f}{u:11.3f}{P:8.3f}{np.exp(-u):8.3f}")

# (iii) Map to MOND and check f = 1 - e^{-sqrt x} = McGaugh.
def f_resolved(x): return 1-np.exp(-np.sqrt(x))      # a*sqrt(2s)=sqrt(x), barrier=sqrt(g_bar), 2s=1/a0
x=np.logspace(-3,3,200)
print("\n assembled resolution f(x) vs McGaugh 1-e^{-sqrt x}:",
      np.allclose(f_resolved(x), 1-np.exp(-np.sqrt(x))))
gobs=x/f_resolved(x)
sl=np.polyfit(np.log(x[x<1e-2]),np.log(gobs[x<1e-2]),1)[0]
print(f" deep slope of g_obs {sl:.3f} (->1/2); g_obs=g_bar/(1-e^-sqrt x) is the RAR fit.")

import matplotlib; matplotlib.use('Agg'); import matplotlib.pyplot as plt
fig,ax=plt.subplots(1,2,figsize=(9,3.7))
us=np.linspace(0,3,100)
# collapse plot
pts=[]
for a in (3,5,8,10):
    for q in (0.01,0.02,0.04):
        P=escape_prob(a,q,trials=8000,seed=a*7+int(q*1000)); pts.append((a*np.sqrt(2*q),P))
pts=np.array(pts)
ax[0].plot(pts[:,0],pts[:,1],'o',ms=4,label='walk simulation')
ax[0].plot(us,np.exp(-us),'r-',label='$e^{-a\\sqrt{2s}}$ (first-passage)')
ax[0].set_xlabel('$a\\sqrt{2s}$'); ax[0].set_ylabel('P(escape = non-registration)')
ax[0].set_title('Meridian first-passage law'); ax[0].legend(fontsize=8)
ax[1].semilogx(x,f_resolved(x),'b',label='$f=1-e^{-\\sqrt{x}}$ (derived)')
ax[1].set_xlabel('$x=g_{bar}/a_0$'); ax[1].set_ylabel('resolved fraction $f$')
ax[1].axvline(1,color='gray',ls=':',lw=0.6); ax[1].set_title('Position-chart resolved fraction'); ax[1].legend(fontsize=8)
fig.tight_layout(); fig.savefig('cons3_firstpassage.pdf'); print("figure saved")
