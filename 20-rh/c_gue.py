"""
c_gue.py — block C, continued: random-matrix statistics of the target spectrum ([approx])
=========================================================================================
The zero heights read as the target spectrum of the scale-evolution operator (Definition
specmap: ρ ↦ −i(ρ − ½)). The heights here are computed independently with mpmath's zetazero
and serve as the validation markers of Numerical Observation gue; no construction of the
package takes them as input. Paper-local predicates:

  C6  Obs. gue   [approx]  unfolded spacings of the first 240 zeros show GUE level repulsion, not
                           Poisson: P(s < ½) = 0.05 (GUE ≈ 0.12, Poisson ≈ 0.39), variance 0.13
                           (GUE ≈ 0.18, Poisson 1)
  C6b Fig. hp    [chart]   the eigenvalue count N(T) lies on the Berry–Keating semiclassical
                           (T/2π)(log(T/2π) − 1) + 7/8: density (1/2π) log p at T = 2πp, the shell
                           scale-depth (Proposition density, block B)

Figure: fig_hilbert_polya.pdf.
"""
import math
import numpy as np
import matplotlib
matplotlib.use("Agg")
import matplotlib.pyplot as plt
from rhcommon import check, riemann_zeros, FIGDIR, FAST, Timer

def unfold(g):
    """Smooth counting function N̄(γ) = (γ/2π) log(γ/2πe) + 7/8: unfolded ordinates with unit mean spacing."""
    return g / (2 * math.pi) * np.log(g / (2 * math.pi * math.e)) + 7.0 / 8.0

def gue_wigner(s):
    return 32 / math.pi ** 2 * s ** 2 * np.exp(-4 * s ** 2 / math.pi)

def run():
    print("\n== block C (continued): GUE level repulsion of the target spectrum (Obs. gue) ==")
    n = 240 if not FAST else 120
    with Timer(f"first {n} zeros (mpmath zetazero)"):
        g = riemann_zeros(n)
    u = unfold(g)
    s = np.diff(u); s = s / s.mean()
    p_half = float(np.mean(s < 0.5)); var = float(np.var(s))
    # reference values of the two ensembles (Wigner surmise for GUE; exponential for Poisson)
    from scipy.integrate import quad
    gue_half = quad(gue_wigner, 0, 0.5)[0]; gue_var = 3 * math.pi / 8 - 1
    poi_half = 1 - math.exp(-0.5); poi_var = 1.0
    tol = 0.02 if not FAST else 0.04
    ok = abs(p_half - 0.05) < tol and abs(var - 0.13) < 0.03 and p_half < 0.5 * poi_half and var < 0.5 * poi_var
    check("C6", "unfolded spacings of the first 240 zeros: P(s<½) ≈ 0.05, variance ≈ 0.13 (repulsion; far from Poisson)", ok,
          f"P(s<½) = {p_half:.3f} (GUE {gue_half:.3f}, Poisson {poi_half:.3f}); var = {var:.3f} (GUE {gue_var:.3f}, Poisson 1)", kind="[approx]")
    # C6b: the count against Berry–Keating
    Ts = np.linspace(10, g[-1], 200)
    Ncount = np.searchsorted(g, Ts)
    Nsemi = Ts / (2 * math.pi) * (np.log(Ts / (2 * math.pi)) - 1) + 7.0 / 8.0
    dev = np.abs(Ncount - Nsemi)
    check("C6b", "eigenvalue count N(T) within 1.5 of the Berry–Keating smooth count on [10, γ_240]", dev.max() < 1.5,
          f"max |N − N̄| = {dev.max():.2f}; mean = {dev.mean():.2f}", kind="[chart]")
    # figure
    fig, ax = plt.subplots(1, 2, figsize=(13, 4.4))
    A = ax[0]
    A.hist(s, bins=np.linspace(0, 3, 16), density=True, color="#1f5fbf", alpha=0.55, edgecolor="white", label=f"ζ zeros (first {n})")
    xx = np.linspace(0, 3, 400)
    A.plot(xx, gue_wigner(xx), color="#16a085", lw=2.2, label="GUE (Wigner surmise)")
    A.plot(xx, np.exp(-xx), color="#1a1a1a", lw=1.4, ls="--", label="Poisson")
    A.set_xlabel("normalised spacing $s$"); A.set_ylabel("$P(s)$"); A.set_xlim(0, 3)
    A.set_title(f"C6: level repulsion — $P(s<\\frac{{1}}{{2}})={p_half:.2f}$, var $={var:.2f}$", fontsize=10); A.legend(fontsize=8.5)
    B = ax[1]
    B.step(np.concatenate([[10], g]), np.arange(n + 1), where="post", color="#1f5fbf", lw=1.4, label=r"$N(T)=\#\{\gamma_k\leq T\}$")
    B.plot(Ts, Nsemi, color="#c0392b", lw=2.0, ls="--", label=r"Berry–Keating $\frac{T}{2\pi}(\log\frac{T}{2\pi}-1)+\frac{7}{8}$")
    B.set_xlabel(r"$T$ ($=2\pi p$ at shell scale $p$)"); B.set_ylabel("$N(T)$"); B.set_xlim(10, g[-1])
    B.set_title(r"C6b: density $\frac{1}{2\pi}\log\frac{T}{2\pi}=\frac{1}{2\pi}\log p$, the shell scale-depth", fontsize=10)
    B.legend(fontsize=8.5, loc="upper left")
    plt.tight_layout(); plt.savefig(f"{FIGDIR}/fig_hilbert_polya.pdf", bbox_inches="tight"); plt.savefig(f"{FIGDIR}/fig_hilbert_polya.png", dpi=110, bbox_inches="tight"); plt.close()
    print(f"    wrote {FIGDIR}/fig_hilbert_polya.pdf")

if __name__ == "__main__":
    from rhcommon import summary
    run(); summary(write=False)
