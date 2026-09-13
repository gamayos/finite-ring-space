"""Flux conservation under noise (Lemma: the mean static force law is noise-invariant).

A 1D chain of Kuramoto phases: site 0 driven by constant torque b (the source's
winding demand), site M pinned (the absorber). In the statistically stationary
state the time-averaged transport through EVERY link must equal b, with or without
drive noise -- slips redistribute the transfer in time, not in mean. This is the
content of the manuscript's flux-conservation lemma: the deep-MOND enhancement
cannot arise as a modification of the mean static force.
"""
import numpy as np

rng = np.random.default_rng(3)
M, dt, T = 20, 0.05, 300_000
burn = 100_000
b = 0.3                                    # demand well inside capacity, so a stationary state exists
ok = True
for noise in (0.0, 0.3):                   # noise amplitude (drive-noise floor)
    th = np.zeros(M + 1)
    J = np.zeros(M)                        # accumulated transport per link (smooth + slips)
    for step in range(T):
        dphi = np.diff(th)                 # th[i+1]-th[i]
        flux = np.sin(-dphi)               # transport i -> i+1
        dth = np.zeros(M + 1)
        dth[:-1] -= flux
        dth[1:] += flux
        dth[0] += b
        eta = np.zeros(M + 1)
        if noise:
            eta[1:-1] = rng.normal(0, noise, M - 1)/np.sqrt(dt)   # ambient drive noise
        th[:-1] += dt*(dth[:-1] + eta[:-1])
        th[-1] = 0.0                       # absorber pinned to the drive
        if step >= burn:
            J += flux*dt
    Jbar = J/((T - burn)*dt)
    spread = np.max(np.abs(Jbar - b))
    print(f"  noise={noise:.1f}: mean flux per link = {Jbar.mean():.4f} (demand b={b}), "
          f"max deviation {spread:.4f}")
    if abs(Jbar.mean() - b) > 0.02 or spread > 0.05: ok = False
print("PASS" if ok else "FAIL", "- flux conservation under noise")
