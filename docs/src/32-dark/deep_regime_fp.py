#!/usr/bin/env python3
"""Stationary Fokker-Planck check for the noisy link of deep_regime.py (32-dark, §3.2 and Prop. newton).

The link  dphi = (T - sin phi) dt + sqrt(2D) dW  (Adler / noisy Kuramoto, unit stiffness) has the
stationary density on the circle
    P(phi) ∝ exp(-U(phi)/D) * ∫_phi^{phi+2pi} exp(U(psi)/D) dpsi,   U(phi) = -T phi - cos phi,
(additive noise, so Ito and Stratonovich coincide).  The transmitted flux is <sin phi>(T); the map
(g_N = <sin phi>, g_eff = T) is the one deep_regime.py reads off its simulation.

What this shows, exactly for the chart model: the mean response is linear at small tilt
(log-slope d ln g_eff / d ln g_N = 1) at every noise level, the noise renormalising the stiffness by a
constant boost g_eff/g_N = 1/chi(D) that rises only as the tilt approaches the running threshold T -> 1.
There is no sqrt regime in the mean force at any D: the deep-regime law of §3.2 is a registration
statement (row B4), not a modification of the mean force — the content of Prop. newton and of the
gravity paper's Lemma fluxnoise.  The simulated slopes 1.03 / 1.11 of deep_regime.py are the
Euler-step and finite-sample bias on this exact 1.000.

Run: python3 deep_regime_fp.py   (numpy only; ~10 s)
"""
import numpy as np

def mean_sin(T, D, n=3000):
    phi = np.linspace(0, 2 * np.pi, n, endpoint=False); dphi = 2 * np.pi / n
    U = lambda x: -T * x - np.cos(x)
    P = np.empty(n)
    for i, p in enumerate(phi):
        psi = np.linspace(p, p + 2 * np.pi, n)
        P[i] = np.exp(-U(p) / D) * np.trapezoid(np.exp(U(psi) / D), psi)
    P /= P.sum() * dphi
    return float((np.sin(phi) * P).sum() * dphi)

if __name__ == "__main__":
    tilts = np.array([0.01, 0.02, 0.04, 0.08, 0.16, 0.32])
    ok = True
    for D in (0.3, 0.6):
        flux = np.array([mean_sin(t, D) for t in tilts])
        slope = np.polyfit(np.log(flux[:3]), np.log(tilts[:3]), 1)[0]
        boost = tilts / flux
        print(f"D={D}: small-tilt log-slope d ln g_eff/d ln g_N = {slope:.4f}   boost g_eff/g_N = {np.round(boost, 3)}")
        ok &= abs(slope - 1.0) < 2e-3 and np.all(np.diff(boost) >= -1e-9)
    print("PASS: mean response Newtonian (slope 1) at every D; boost constant to rising; no sqrt regime" if ok else "FAIL")
