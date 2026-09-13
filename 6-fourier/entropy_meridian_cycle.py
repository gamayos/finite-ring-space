#!/usr/bin/env python3
# -*- coding: utf-8 -*-
"""
Entropy on the meridian cycle  (companion to the "Entropy on the meridian cycle"
subsection of the finite-field FrFT paper).

Computes the spatial-readout Shannon entropy H(s) of the FRC-native fractional
Fourier family along the full meridian cycle, for the symmetry-complete shell
F_13(3;0,1,2): p=13, t=3, n=p-1=12.

The readout is the degenerate-idealisation (complex) reading the FRC quantum
companion supplies: the finite-field eigenvalue refinement g^{-l s} maps to the
n-th root of unity e^{-2pi i l s / n}, so the fractional family is realised on C^n
by the *canonical* DFT eigenprojectors (the same projectors Pi_l used in the
paper, here over C). For a spatially-localised input (delta on M_0),
    p_j(s) = |(F^{[s]} delta_0)_j|^2,   H(s) = -sum_j p_j log p_j.
F^{[s]} is unitary, so the dynamics conserves entropy; H is a property of the
readout. Cardinal values are exact: H(0)=H(2t)=0, H(t)=H(3t)=log n.
"""
import numpy as np

def entropy_cycle(p=13, t=3):
    n = p - 1
    w = np.exp(2j*np.pi/n)
    F = np.array([[w**(j*k) for k in range(n)] for j in range(n)]) / np.sqrt(n)  # unitary DFT, F^4=I
    # canonical eigenprojectors onto the four Fourier eigenspaces, eigenvalue (-i)^l
    P = [sum(((-1j)**l)**(-r) * np.linalg.matrix_power(F, r) for r in range(4)) / 4
         for l in range(4)]
    assert np.allclose(sum(P), np.eye(n))
    assert all(np.allclose(Pl @ Pl, Pl) for Pl in P)
    e0 = np.zeros(n); e0[0] = 1.0
    H, Hmax = [], np.log(n)
    for s in range(n):
        Ms = sum(np.exp(-2j*np.pi*l*s/n) * P[l] for l in range(4))   # F^{[s]} on C^n
        psi = Ms @ e0
        q = np.abs(psi)**2; q = q / q.sum(); q = q[q > 1e-15]
        H.append(float(-(q*np.log(q)).sum()))
    return n, Hmax, H

if __name__ == "__main__":
    n, Hmax, H = entropy_cycle()
    # closed form of prop:closedform, and rem:input-dep check
    t = 3
    for s_ in range(n):
        ts = np.sin(np.pi * s_ / (2 * t)) ** 2
        if ts < 1e-15:
            Hcf = 0.0
        else:
            p0 = 1 - (n - 1) * ts / n
            Hcf = float(-(p0 * np.log(p0) + (n - 1) * (ts / n) * np.log(ts / n)))
        assert abs(Hcf - H[s_]) < 1e-10, (s_, Hcf, H[s_])
    print("closed-form check (prop:closedform): exact match at all 12 meridians")
    labels = {0: "M0 spatial", 3: "M3 spectral", 6: "M6 parity", 9: "M9 inverse-spectral"}
    print(f"F_13(3;0,1,2):  n={n}, Hmax = log {n} = {Hmax:.4f} nats\n")
    print(" s   meridian              H (nats)   H / log n")
    for s in range(n):
        print(f"{s:2d}   {labels.get(s,''):20s}  {H[s]:7.4f}    {H[s]/Hmax:6.4f}")

    # ---- figure ----
    import matplotlib
    matplotlib.use("Agg")
    import matplotlib.pyplot as plt
    plt.rcParams.update({"font.family": "serif", "font.size": 11,
                         "mathtext.fontset": "cm", "axes.linewidth": 0.8})
    s = np.arange(n)
    Hn = np.array(H)/Hmax
    fig, ax = plt.subplots(figsize=(6.2, 3.5))
    ax.axhline(1.0, ls="--", lw=0.8, color="0.5")
    ax.text(n-0.1, 1.005, r"$\log n$", ha="right", va="bottom", color="0.4", fontsize=10)
    ax.plot(s, Hn, "-", color="0.25", lw=1.3, zorder=1)
    ax.plot(s, Hn, "o", color="0.25", ms=4, zorder=2)
    # highlight cardinal meridians
    card = {0: ("$M_0$ spatial", "tab:blue"), 3: ("$M_\\kappa$ spectral", "tab:red"),
            6: ("$M_{2\\kappa}$ parity", "tab:green"), 9: ("$M_{3\\kappa}$ inv-spectral", "tab:orange")}
    for k, (lab, col) in card.items():
        ax.plot(k, Hn[k], "o", color=col, ms=8, zorder=3)
    ax.annotate("$M_0$", (0, 0), textcoords="offset points", xytext=(2, 8), color="tab:blue")
    ax.annotate("$M_{2\\kappa}$ (parity)", (6, 0), textcoords="offset points", xytext=(-6, 8),
                ha="center", color="tab:green")
    ax.annotate("$M_\\kappa$ (Fourier)", (3, 1), textcoords="offset points", xytext=(0, -16),
                ha="center", color="tab:red")
    ax.annotate("$M_{3\\kappa}$", (9, 1), textcoords="offset points", xytext=(0, -16),
                ha="center", color="tab:orange")
    ax.set_xlabel(r"meridian index $s\in\mathbb{Z}_{4\kappa}$")
    ax.set_ylabel(r"normalised entropy $H(s)/\log n$")
    ax.set_xticks(range(n)); ax.set_ylim(-0.05, 1.12); ax.set_xlim(-0.4, n-0.6)
    ax.spines[["top", "right"]].set_visible(False)
    fig.tight_layout()
    out = "figures/entropy-cycle-f13.pdf"
    fig.savefig(out, bbox_inches="tight")
    print(f"\nwrote {out}")
