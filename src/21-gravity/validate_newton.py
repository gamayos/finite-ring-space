"""Newtonian layer: lattice Green's function, inverse-square law, coherent additivity.

Validates: Lemma (stationary bias field)  u = m/(4 pi kappa r) on Z^3, via the exact
           Montroll representation G(x) = int_0^inf e^{-6t} I_x(2t) I_0(2t)^2 dt;
           Theorem (Newtonian limit)      U(r) ~ -G m1 m2 / r  =>  F ~ 1/r^2;
           Lemma (coherent additivity)    locked ensemble couples as m, unlocked as sqrt(m).
"""
import numpy as np
import mpmath as mp

ok = True
mp.mp.dps = 20

def G(r):
    f = lambda t: mp.exp(-6*t)*mp.besseli(r, 2*t)*mp.besseli(0, 2*t)**2
    return mp.quad(f, [0, mp.inf])

print("  exact lattice Green vs 1/(4 pi r):")
rs = [3, 5, 8, 12]
Gv = [float(G(r)) for r in rs]
for r, g in zip(rs, Gv):
    ratio = 4*np.pi*r*g
    print(f"    r={r:2d}: 4*pi*r*G(r) = {ratio:.5f}")
    if abs(ratio - 1) > 1.5/r**2 + 0.005: ok = False   # manuscript claims 1 + O(r^-2)

slope = np.polyfit(np.log(rs[1:]), np.log(Gv[1:]), 1)[0]   # r >= 5, beyond O(r^-2) zone
print(f"  potential power law: U ~ r^{slope:.4f}  (target -1)")
if abs(slope + 1) > 0.02: ok = False

rng = np.random.default_rng(1)
m = 10**4
locked = abs(np.sum(np.exp(1j*np.zeros(m))))
rand = np.mean([abs(np.sum(np.exp(1j*rng.uniform(0, 2*np.pi, m)))) for _ in range(200)])
print(f"  coupling: locked = {locked:.0f} (=m), unlocked ~ {rand:.0f} (target ~ sqrt(pi m)/2 = {np.sqrt(np.pi*m)/2:.0f})")
if not (abs(locked - m) < 1e-9 and 0.5*np.sqrt(m) < rand < 2*np.sqrt(m)): ok = False

print("PASS" if ok else "FAIL", "- Newtonian layer")
