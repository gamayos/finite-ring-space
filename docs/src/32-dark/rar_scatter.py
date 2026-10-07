#!/usr/bin/env python3
# framed-rational status: [APPROX] -- a data confrontation (SPARC, Lelli et al. 2016, 2017);
# continuum statistics on measured accelerations; no exact claim rests on it.
# =====================================================================
#  rar_scatter.py -- the SPARC residual test of the radial acceleration
#  relation with a0 = c H0 / 2pi held FIXED (H0 = 67.4 km/s/Mpc), the
#  paper's interpolation nu(y) = 1/(1 - exp(-sqrt y)).  (32-dark, T25.)
#
#  Data (public, validation/data/):
#    RAR.mrt              Lelli, McGaugh, Schombert, Pawlowski 2017, Fig. 2 (2692 points)
#    Rotmod_LTG.zip       SPARC mass models, 175 galaxies (Lelli, McGaugh, Schombert 2016)
#    SPARC_Lelli2016c.mrt SPARC galaxy sample table
#
#  What is established:
#    1. total rms, the rms expected from the quoted errors, the intrinsic remainder;
#    2. the intrinsic scatter binned in x = g_b/a0 (the deep-regime rise);
#    3. the paper's scatter law sigma = (2 tan alpha(x)/ln10) d_alpha at d_alpha =
#       6-11 deg (the disk dynamical temperature identification) against the
#       intrinsic scatter, and the d_alpha the knee value bounds;
#    4. per galaxy: within-galaxy intrinsic scatter and its (absence of)
#       correlation with 1/Vflat, the dynamical-temperature proxy of gas disks;
#    5. the coherent-addition law applied to gas + disk + bulge: the sqrt(N_eff)
#       boost the RAR would show if a galaxy's components added as amplitudes;
#    6. nu at the cluster-core accelerations.
# =====================================================================
import numpy as np, zipfile, io, os

HERE = os.path.dirname(os.path.abspath(__file__))
DATA = os.path.join(HERE, "data")
c = 2.99792458e8; H0 = 67.4e3/3.0857e22; a0 = c*H0/(2*np.pi); kpc = 3.0857e19
def nu(y): return 1/(1-np.exp(-np.sqrt(y)))
fails = 0
def check(name, ok):
    global fails
    print(("  PASS  " if ok else "  FAIL  ") + name)
    if not ok: fails += 1

print(f"a0 = cH0/2pi = {a0:.4e} m/s^2 (H0 = 67.4)")

# ---- 1. all points ---------------------------------------------------
d = np.loadtxt(os.path.join(DATA, "RAR.mrt"), skiprows=14)
lgb, egb, lgo, ego = d.T
gb, go = 10**lgb, 10**lgo
x = gb/a0
r = np.log10(go) - np.log10(gb*nu(x))
s = np.sqrt(x); slope = 1 - 0.5*s*np.exp(-s)/(1-np.exp(-s))        # d log(g_b nu)/d log g_b
exp_err = np.sqrt(ego**2 + (slope*egb)**2)
intr = np.sqrt(max(r.var() - np.mean(exp_err**2), 0.0))
print(f"\n== 1. {len(r)} SPARC points, a0 fixed: mean {r.mean():+.4f} dex, rms {r.std():.4f}, expected {np.sqrt(np.mean(exp_err**2)):.4f}, intrinsic {intr:.4f} dex")
check("intrinsic scatter at fixed a0 below 0.05 dex", intr < 0.05)
check("total rms within 0.01 dex of the error-expected rms (error-dominated)", abs(r.std()-np.sqrt(np.mean(exp_err**2))) < 0.01)

# ---- 2. binned in x --------------------------------------------------
print("\n== 2. intrinsic scatter binned in log10 x")
edges = [-2, -1.5, -1, -0.5, 0, 0.5, 1, 1.5]
lx = np.log10(x); binned = {}
for lo, hi in zip(edges[:-1], edges[1:]):
    m = (lx >= lo) & (lx < hi)
    rr, ee = r[m], exp_err[m]
    it = np.sqrt(max(rr.var() - np.mean(ee**2), 0.0)); binned[(lo, hi)] = it
    print(f"   [{lo:5.1f},{hi:5.1f}) N={m.sum():4d}  mean {rr.mean():+.3f}  rms {rr.std():.3f}  expected {np.sqrt(np.mean(ee**2)):.3f}  intrinsic {it:.3f}")
check("knee bins (0.1 < x < 3) intrinsic within 0.03-0.05 dex", all(0.02 < binned[b] < 0.06 for b in [(-1,-0.5),(-0.5,0),(0,0.5)]))
check("deep-regime rise: intrinsic at x < 0.03 exceeds the knee value", binned[(-2,-1.5)] > 2*binned[(-1,-0.5)])

# ---- 3. the paper's law ----------------------------------------------
print("\n== 3. the scatter law sigma = (2 tan alpha / ln10) d_alpha against the intrinsic scatter")
def tana(x): return np.sqrt(np.exp(-np.sqrt(x))/(1-np.exp(-np.sqrt(x))))
def sig(x, da_deg): return 2*tana(x)*np.radians(da_deg)/np.log(10)
for xx in (0.01, 0.1, 1.0):
    print(f"   x={xx:5.2f}: law at d_alpha = 6 / 11 deg: {sig(xx,6):.3f} / {sig(xx,11):.3f} dex")
da_knee = np.degrees(0.04*np.log(10)/(2*tana(1.0)))
print(f"   d_alpha bounded by 0.04 dex at x = 1: {da_knee:.1f} deg  (sigma_v/v = tan = {np.tan(np.radians(da_knee)):.3f})")
check("d_alpha = 6-11 deg (sigma_v/v = 0.1-0.2) excluded at the knee: law > 1.5 x intrinsic", sig(1.0,6) > 1.5*binned[(-0.5,0)])
check("the bound d_alpha <~ 3.5 deg", da_knee < 4.0)

# ---- 4. per galaxy ---------------------------------------------------
print("\n== 4. per galaxy: within-galaxy intrinsic scatter vs 1/Vflat")
rows = {}
for l in open(os.path.join(DATA, "SPARC_Lelli2016c.mrt")).readlines()[98:]:
    p = l.split()
    if len(p) < 19: continue
    try: rows[p[0]] = dict(inc=float(p[5]), vflat=float(p[15]), Q=int(p[17]))
    except Exception: pass
z = zipfile.ZipFile(os.path.join(DATA, "Rotmod_LTG.zip"))
res = []
for fn in sorted(z.namelist()):
    if not fn.endswith("_rotmod.dat"): continue
    name = os.path.basename(fn).replace("_rotmod.dat", "")
    if name not in rows: continue
    g = rows[name]
    if g["Q"] == 3 or g["inc"] < 30 or g["vflat"] <= 0: continue
    dd = np.loadtxt(io.StringIO(z.read(fn).decode()))
    R, Vobs, eV, Vgas, Vdisk, Vbul = dd[:,0], dd[:,1], dd[:,2], dd[:,3], dd[:,4], dd[:,5]
    vb2 = Vgas*np.abs(Vgas) + 0.5*Vdisk**2 + 0.7*Vbul**2           # M/L 0.5 disk, 0.7 bulge (Lelli 2017)
    m = (vb2 > 0) & (Vobs > 0) & (eV/Vobs < 0.10)
    if m.sum() < 5: continue
    gbg = vb2[m]*1e6/(R[m]*kpc); gog = Vobs[m]**2*1e6/(R[m]*kpc)
    rg = np.log10(gog) - np.log10(gbg*nu(gbg/a0)); eg = 2*eV[m]/Vobs[m]/np.log(10)
    res.append((g["vflat"], rg.mean(), rg.std(), np.sqrt(np.mean(eg**2))))
res = np.array(res); vf, mean, rms, err = res.T
intr_g = np.sqrt(np.clip(rms**2 - err**2, 0, None))
def spearman(a, b):
    ra = np.argsort(np.argsort(a)); rb = np.argsort(np.argsort(b))
    return np.corrcoef(ra, rb)[0,1]
rho = spearman(intr_g, 1/vf)
print(f"   {len(res)} galaxies (Q<=2, i>30, dV/V<10%); median within-galaxy intrinsic {np.median(intr_g):.3f} dex; std of per-galaxy offsets {mean.std():.3f}")
for lo, hi in ((0,60),(60,100),(100,150),(150,200),(200,400)):
    m = (vf >= lo) & (vf < hi)
    if m.sum() >= 3: print(f"   Vflat [{lo:3d},{hi:3d}): {m.sum():3d} gal, median intrinsic {np.median(intr_g[m]):.3f}, proxy 8 km/s / Vflat = {8/vf[m].mean():.3f}")
print(f"   Spearman rho(intrinsic, 1/Vflat) = {rho:+.3f}  (n = {len(res)}; |rho| < 0.17 is p > 0.05)")
check("no correlation of within-galaxy intrinsic scatter with 1/Vflat (|rho| < 0.17)", abs(rho) < 0.17)

# ---- 5. coherent addition within a galaxy -----------------------------
print("\n== 5. the coherent-addition law applied to gas + disk + bulge")
boost = []
for fn in z.namelist():
    if not fn.endswith("_rotmod.dat"): continue
    dd = np.loadtxt(io.StringIO(z.read(fn).decode()))
    comps = [np.clip(dd[:,3]*np.abs(dd[:,3]), 0, None), 0.5*dd[:,4]**2, 0.7*dd[:,5]**2]
    for i in range(len(dd)):
        gi = [cc[i] for cc in comps if cc[i] > 0]
        if sum(gi) <= 0: continue
        neff = (np.sum(np.sqrt(gi)))**2/np.sum(gi); boost.append(0.5*np.log10(neff))
boost = np.array(boost)
print(f"   sqrt(N_eff) boost over {len(boost)} points: median {np.median(boost):.3f} dex, 16-84 %: {np.percentile(boost,16):.3f}-{np.percentile(boost,84):.3f}, max {boost.max():.3f}")
check("amplitude addition of a galaxy's components would boost the RAR by > 0.1 dex (excluded by the 0.04 dex intrinsic scatter)", np.median(boost) > 0.1)
for gi in ([1,1],[1,1,1,1],[0.8,0.05,0.05,0.05,0.05],[1]*20):
    gi = np.array(gi, float); ne = np.sum(np.sqrt(gi))**2/gi.sum()
    print(f"   components {np.round(gi[:5],2)}{'...' if len(gi)>5 else ''}: N_eff = {ne:.2f}, boost {np.sqrt(ne):.2f}")

# ---- 6. nu at the core ------------------------------------------------
print(f"\n== 6. nu(0.1) = {nu(0.1):.2f}, nu(0.2) = {nu(0.2):.2f}, nu(0.25) = {nu(0.25):.2f}")
check("nu(0.1) = 3.7, not 3", abs(nu(0.1)-3.69) < 0.02)

print("\nrar_scatter.py:", "PASS" if fails == 0 else f"FAIL ({fails})")
raise SystemExit(1 if fails else 0)
