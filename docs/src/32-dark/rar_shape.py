#!/usr/bin/env python3
"""
rar_shape.py -- the named test of row B8: the approach to Newton against the binned radial acceleration relation.

The paper's interpolation is g_obs = g_b / (1 - e^{-sqrt(x)}), x = g_b/a0 (the first-passage registration with the
amplitude barrier, row B8); the alternative with the same two limits is the 'simple' rational form
g_obs = g_b * (1 + sqrt(1 + 4/x))/2.  The two differ by up to 0.05 in g_obs/g_b near g_b ~ 5 a0 (interpolation.py).
This script bins the 2693 SPARC points of Lelli et al. (2017, data/RAR.mrt) in log g_b (0.2 dex), takes the mean
log g_obs per bin with the bin's scatter (the standard deviation, the error bars of the binned relation) as its
uncertainty, and confronts both forms with the binned relation: (i) at the fixed
floor a0 = cH0/2pi (H0 = 67.4), (ii) with a0 free for each form (a grid search on the binned chi^2).  A labelled
[approx] data comparison; the exact statements of the paper are elsewhere (firstpassage_finite.py, born_exact.py).
"""
import numpy as np, os
HERE = os.path.dirname(os.path.abspath(__file__))
c = 2.99792458e8; H0 = 67.4e3/3.0857e22; a0_floor = c*H0/(2*np.pi)
fails = 0
def check(name, ok):
    global fails
    print(("  PASS  " if ok else "  FAIL  ") + name)
    if not ok: fails += 1
def nu_exp(x):    return 1/(1-np.exp(-np.sqrt(x)))
def nu_simple(x): return 0.5*(1+np.sqrt(1+4/x))

d = np.loadtxt(os.path.join(HERE, "data", "RAR.mrt"), skiprows=14)
lgb, egb, lgo, ego = d.T
print(f"{len(lgb)} SPARC points; a0 = cH0/2pi = {a0_floor:.4e} m/s^2 (H0 = 67.4); the RAR fit g_dagger = 1.20e-10")

# --- the binned relation: mean log g_obs in 0.2-dex bins of log g_b, the bin's scatter as its uncertainty
edges = np.arange(-12.0, -8.4, 0.2)
bins = []
for lo, hi in zip(edges[:-1], edges[1:]):
    m = (lgb >= lo) & (lgb < hi)
    if m.sum() < 10: continue
    mean = lgo[m].mean(); sd = lgo[m].std()                          # the bin's mean and scatter (the binned relation's error bar)
    bins.append((0.5*(lo+hi), m.sum(), mean, sd))
bins = np.array(bins); cb, nb, mb, eb = bins.T
print(f"{len(bins)} bins of 0.2 dex in log g_b with >= 10 points; the uncertainty of a bin is its scatter (0.03-0.13 dex)")

def chi2(form, a0, sel=None):
    pred = np.log10(10**cb * form(10**cb/a0))
    r = (mb - pred)/eb
    return np.sum(r[sel]**2) if sel is not None else np.sum(r**2), pred

print("\n== 1. both forms at the fixed floor a0 = cH0/2pi")
print(f"   {'log g_b':>8} {'N':>4} {'<log g_obs>':>12} {'sd':>6} {'exp':>8} {'simple':>8} {'res exp':>8} {'res smp':>8}")
c_e0, p_e0 = chi2(nu_exp, a0_floor); c_s0, p_s0 = chi2(nu_simple, a0_floor)
for i in range(len(cb)):
    print(f"   {cb[i]:8.1f} {int(nb[i]):4d} {mb[i]:12.3f} {eb[i]:6.3f} {p_e0[i]:8.3f} {p_s0[i]:8.3f} {mb[i]-p_e0[i]:+8.3f} {mb[i]-p_s0[i]:+8.3f}")
print(f"   chi^2 over {len(cb)} bins: exponential {c_e0:.1f}, simple {c_s0:.1f}")

print("\n== 2. a0 free for each form (grid 0.8-1.6e-10)")
grid = np.linspace(0.8e-10, 1.6e-10, 801)
best = {}
for name, form in (("exponential", nu_exp), ("simple", nu_simple)):
    cs = np.array([chi2(form, a)[0] for a in grid]); k = int(np.argmin(cs))
    best[name] = (grid[k], cs[k]); print(f"   {name:12s}: best a0 = {grid[k]:.3e}, chi^2 = {cs[k]:.1f}")
a_e, c_e = best["exponential"]; a_s, c_s = best["simple"]
check("the exponential form's best-fit a0 lies within 10 % of the RAR fit g_dagger = 1.20e-10", abs(a_e/1.20e-10 - 1) < 0.10)
check("with a0 free, the exponential form fits the binned relation better than the simple form (lower chi^2)", c_e < c_s)

print("\n== 3. the discriminating band 2 < x < 10 (g_b ~ 5 a0), each form at its own best a0")
knee_e = (10**cb/a_e > 2) & (10**cb/a_e < 10); knee_s = (10**cb/a_s > 2) & (10**cb/a_s < 10)
ce_k, pe = chi2(nu_exp, a_e, knee_e); cs_k, ps = chi2(nu_simple, a_s, knee_s)
print(f"   {'log g_b':>8} {'<log g_obs>':>12} {'sd':>6} {'exp':>8} {'simple':>8} {'res exp':>8} {'res smp':>8}")
for i in np.where(knee_e | knee_s)[0]:
    print(f"   {cb[i]:8.1f} {mb[i]:12.3f} {eb[i]:6.3f} {pe[i]:8.3f} {ps[i]:8.3f} {mb[i]-pe[i]:+8.3f} {mb[i]-ps[i]:+8.3f}")
print(f"   chi^2 in the band: exponential {ce_k:.1f} ({knee_e.sum()} bins), simple {cs_k:.1f} ({knee_s.sum()} bins)")
print(f"   the forms differ by up to {np.max(np.abs(np.log10(nu_simple(10**cb/a_e)/nu_exp(10**cb/a_e)))):.3f} dex over the bins")
check("in the band 2 < x < 10 the binned relation departs from the exponential form by less than the bin scatter in every bin (the B8 falsifier not triggered)",
      np.all(np.abs((mb - pe)[knee_e]) < eb[knee_e]))
off = (mb - pe)[knee_e]
print(f"   note: the binned relation sits {-off.mean():.3f} dex below the exponential form on average in the band, within the scatter")
print(f"   power: the two forms differ by <= {np.max(np.abs(np.log10(nu_simple(10**cb/a_e)/nu_exp(10**cb/a_e)))):.3f} dex per bin against a bin scatter of {eb[knee_e].mean():.3f} dex: the binned relation prefers the exponential form by chi^2 but does not exclude the rational form")
check("the simple rational form is disfavoured in the band (its chi^2 exceeds the exponential form's)", cs_k > ce_k)

print("\n== 4. the fixed floor a0 = cH0/2pi against the free fit")
print(f"   floor/fit = {a0_floor/a_e:.3f} (the paper: 13 % below the fitted value); Delta chi^2 (fixed - free) = {c_e0 - c_e:.1f}")
check("the free-fit a0 of the exponential form exceeds the floor cH0/2pi by 5-25 % (the paper's 13 %)", 1.05 < a_e/a0_floor < 1.25)
print("\nrar_shape.py:", "PASS" if fails == 0 else f"FAIL ({fails})")
raise SystemExit(1 if fails else 0)
