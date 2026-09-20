"""
b_deframe.py — block B: the de-framing dictionary and its consequences ([chart], [approx])
=========================================================================================
The dictionary of Definition deframe: a shell of cardinality p reads ζ on the line to height
T = 2πp with the Riemann–Siegel main sum of length √p = √(T/2π); a height is the scale
coordinate of the shell that reads it (T/2π = p). Paper-local predicates:

  B1  Prop. density   [chart]  smooth zero density at T = 2πp equals the shell scale-depth (1/2π) log p:
                                0.6226, 0.9891, 1.3556, 1.7220 at p = 50, 500, 5·10³, 5·10⁴ (a substitution
                                into the Riemann–von Mangoldt formula; a consistency of the dictionary)
  B2  Obs. residue    [approx] the finite-horizon reconstruction error |Z_horizon − Z| scales as p^{-1/4}
                                (unconditional: truncation of the main sum), fitted slope ≈ −1/4
  B3  Prop. critical  [chart]  the de-framing limit of the critical real part: 2⁻¹/p = (2κ+1)/p → ½
  B4  Def. deframe    [approx] the horizon-length main sum (length ⌊√(t/2π)⌋, weight n^{-1/2}) tracks Z(t)
                                through the first ten zeros: sign changes of the main sum on [10, 55]
                                bracket every one of γ_1..γ_10 (the on-line reading of Proposition turing)

The Hardy Z function Z(t) enters here as the classical side of the correspondence (the paper's
"ζ never evaluated" discipline binds the prime-side realisation of block C, not this dictionary
check). Figure: fig_deframing.pdf.
"""
import math
import numpy as np
import mpmath as mp
import matplotlib
matplotlib.use("Agg")
import matplotlib.pyplot as plt
from rhcommon import check, HEIGHTS, FIGDIR, FAST, Timer

mp.mp.dps = 18

def Z_true(t):
    return float(mp.siegelz(t))

def Z_horizon(t):
    """Riemann–Siegel main sum of length ⌊√(t/2π)⌋ = the shell horizon √p at T = 2πp; no remainder."""
    N = int(mp.floor(mp.sqrt(t / (2 * mp.pi))))
    th = mp.siegeltheta(t)
    return float(2 * mp.fsum(mp.cos(th - t * mp.log(n)) / mp.sqrt(n) for n in range(1, N + 1)))

def run():
    print("\n== block B: the de-framing dictionary (Def. deframe) ==")
    # B1 density
    stated = {50: 0.6226, 500: 0.9891, 5000: 1.3556, 50000: 1.7220}
    got = {p: math.log(p) / (2 * math.pi) for p in stated}
    ok = all(abs(got[p] - stated[p]) < 6e-5 for p in stated)
    check("B1", "smooth zero density at T = 2πp is (1/2π) log p", ok,
          "  ".join(f"p={p}: {got[p]:.4f}" for p in stated), kind="[chart]")
    # B3 de-framing limit
    vals = [(p, (2 * ((p - 1) // 4) + 1) / p) for p in [13, 53, 101, 409, 1009, 10009]]
    ok = all(v > 0.5 for _, v in vals) and all(vals[i][1] > vals[i + 1][1] for i in range(len(vals) - 1)) and abs(vals[-1][1] - 0.5) < 1e-3
    check("B3", "de-framing limit (2κ+1)/p → ½ from above", ok, "  ".join(f"{p}: {v:.5f}" for p, v in vals), kind="[chart]")
    # B4 main sum brackets the first ten zeros
    with Timer("horizon sums on [10,55]"):
        ts = np.linspace(10, 55, 700 if not FAST else 350)
        zt = np.array([Z_true(t) for t in ts]); zh = np.array([Z_horizon(t) for t in ts])
    sc = ts[:-1][zh[:-1] * zh[1:] < 0]
    inwin = HEIGHTS[(HEIGHTS > 10) & (HEIGHTS < 55)]              # γ_1..γ_11
    dev = [float(np.min(np.abs(sc - g))) for g in inwin]
    ok = len(sc) == len(inwin) and max(dev) < 0.5
    check("B4", "the bare horizon-length main sum has one sign change per zero on [10,55], each within 0.5 of γ_n", ok,
          f"{len(sc)} sign changes for {len(inwin)} zeros; max deviation {max(dev):.2f} (1–2 terms only at these heights)", kind="[approx]")
    # B2 residue scaling
    with Timer("residue scan"):
        T0 = np.array([40, 80, 160, 320, 640, 1280, 2560, 5120] if not FAST else [40, 80, 160, 320, 640, 1280])
        err = []
        for t0 in T0:
            e = [abs(Z_horizon(float(t0) + 0.123 * i) - Z_true(float(t0) + 0.123 * i)) for i in range(1, 16)]
            err.append(float(np.median(e)))
    slope = np.polyfit(np.log(T0), np.log(err), 1)[0]
    check("B2", "reconstruction residue ∝ p^{-1/4}: fitted log-log slope in [−0.40, −0.10]", -0.40 < slope < -0.10,
          f"slope = {slope:.3f}", kind="[approx]")
    # figure
    fig, ax = plt.subplots(1, 3, figsize=(15, 4.3))
    ax[0].axhline(0, color="#ccc", lw=0.8)
    for g in HEIGHTS[:10]: ax[0].axvline(g, color="#ccc", lw=0.8, ls=":")
    ax[0].plot(ts, zt, color="#1a1a1a", lw=1.5, label=r"$Z(t)$")
    ax[0].plot(ts, zh, color="#c0392b", lw=1.3, ls="--", label=r"horizon sum, $N=\lfloor\sqrt{t/2\pi}\rfloor$")
    ax[0].plot(HEIGHTS[:10], [0] * 10, "o", color="#1f5fbf", ms=5, zorder=5, label=r"zeros $\gamma_n$")
    ax[0].set_xlabel(r"height $t$ ($=2\pi p$ at shell scale $p$)"); ax[0].set_ylabel(r"$Z(t)$"); ax[0].set_ylim(-6, 6)
    ax[0].set_title("B4: de-framing = finite Riemann–Siegel"); ax[0].legend(fontsize=8)
    ps = np.logspace(1.3, 5, 30)
    ax[1].plot(ps, np.log(ps) / (2 * np.pi), color="#1a1a1a", lw=1.8, label=r"$\frac{1}{2\pi}\log\frac{T}{2\pi}$, $T=2\pi p$")
    ax[1].plot(list(stated), [got[p] for p in stated], "o", color="#c0392b", label=r"shell scale-depth $\frac{1}{2\pi}\log p$")
    ax[1].set_xscale("log"); ax[1].set_xlabel("shell cardinality $p$"); ax[1].set_ylabel("zeros per unit height")
    ax[1].set_title("B1: zero density = shell scale-depth [chart]"); ax[1].legend(fontsize=8)
    ax[2].loglog(T0, err, "o-", color="#c0392b", lw=1.4, label=r"median $|Z_{\rm horizon}-Z|$")
    ax[2].loglog(T0, T0 ** -0.25, color="#1a1a1a", ls="--", label=r"$t^{-1/4}=p^{-1/4}$")
    ax[2].set_xlabel(r"height $t$ ($=2\pi p$)"); ax[2].set_ylabel("reconstruction error")
    ax[2].set_title(f"B2: residue $\\propto p^{{-1/4}}$ (slope {slope:.2f})"); ax[2].legend(fontsize=8)
    plt.tight_layout(); plt.savefig(f"{FIGDIR}/fig_deframing.pdf", bbox_inches="tight"); plt.savefig(f"{FIGDIR}/fig_deframing.png", dpi=110, bbox_inches="tight"); plt.close()
    print(f"    wrote {FIGDIR}/fig_deframing.pdf")

if __name__ == "__main__":
    from rhcommon import summary
    run(); summary(write=False)
