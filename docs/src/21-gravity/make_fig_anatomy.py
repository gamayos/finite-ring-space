"""Figure: anatomy of the static solution (Fig.~\\ref{fig:anatomy}).

Clock rate f/f_inf = e^{-u}, u = r_g/r, on a log-r axis: post-Newtonian and exponential
zones, the operational horizon r_f = r_s/lnOmega ~ r_s/281 where the redshift reaches the
resolution floor Omega^{-1/2}, and the cloaked microscopic slip core r_* = sqrt(r_g l_P).
Horizonless: no divergence at the GR horizon r_s = 2 r_g. [approx] continuum reading.
"""
import pathlib, math, numpy as np, matplotlib
matplotlib.use("Agg")
import matplotlib.pyplot as plt
FIG = pathlib.Path(__file__).resolve().parent.parent / "figures"
plt.rcParams.update({"font.family":"serif","mathtext.fontset":"cm","font.size":11,
                     "axes.linewidth":0.8,"figure.dpi":150})

lnOmega = 122*math.log(10)      # ln(10^122) ~ 280.9
rf = 2.0/lnOmega               # r_f / r_g = (r_s/lnOmega)/r_g, r_s = 2 r_g
floor = 10**-61                # Omega^{-1/2}
x = np.logspace(-2.45, 2, 1000); y = np.exp(-1.0/x)

fig, ax = plt.subplots(figsize=(6.8,4.4))
ax.axvspan(1, 1e2, color="#eef4fb", zorder=0)
ax.axvspan(rf, 1, color="#dce8f5", zorder=0)
ax.axvspan(1e-3, rf, color="#c9b8c9", alpha=0.45, zorder=0)
ax.plot(x, y, lw=2.3, color="#1f4e79", zorder=5,
        label=r"redshift $f/f_\infty=e^{-u}$,  $u=r_g/r$")
ax.axhline(floor, ls="--", lw=1.0, color="0.45")
ax.text(0.6, 3e-61, r"resolution floor $\Omega^{-1/2}$", fontsize=8.5, color="0.35", ha="center", va="bottom")
ax.axvline(rf, ls=":", lw=1.2, color="#b00020")
ax.axvline(2.0, ls="-.", lw=1.0, color="0.4")
ax.axvline(1.0, ls=":", lw=0.7, color="0.6")
ax.plot([rf],[floor], "o", ms=5, color="#b00020", zorder=6)
ax.text(13, 1e-30, "post-Newtonian\n"+r"$\beta=\gamma=1$", ha="center", fontsize=8.8, color="#26527a")
ax.text(0.13, 1e-33, "exponential\nzone", ha="center", fontsize=8.8, color="#26527a")
ax.text(rf*0.43, 1e-30, "operationally\nblack", ha="center", fontsize=8.6, color="#6a3d63")
ax.text(2.5, 1e-22, "photon sphere $r_s=2r_g$  (GR horizon - none here)",
        rotation=90, va="center", ha="left", fontsize=7.9, color="0.3")
ax.annotate(r"operational horizon  $r_f=r_s/\ln\Omega\approx r_s/281$", xy=(rf, floor),
            xytext=(rf*1.7, 6e-52), fontsize=8.7, color="#b00020",
            arrowprops=dict(arrowstyle="->", color="#b00020", lw=0.8))
ax.annotate(r"slip core $r_*=\sqrt{r_g\,\ell_P}\sim10^{-19}r_g$ (cloaked)",
            xy=(1.05e-3, 1e-58), xytext=(2.4e-3, 1e-58), fontsize=8.3, color="#6a3d63",
            arrowprops=dict(arrowstyle="->", color="#6a3d63", lw=0.8))
ax.set_xscale("log"); ax.set_yscale("log")
ax.set_xlim(1e-3, 1e2); ax.set_ylim(1e-65, 5)
ax.set_xlabel(r"$r/r_g$   ($r_g=Gm/c^2$)")
ax.set_ylabel(r"clock rate / redshift  $f/f_\infty$")
ax.set_yticks([1e0,1e-10,1e-20,1e-30,1e-40,1e-50,1e-60])
leg = ax.legend(loc="upper left", bbox_to_anchor=(0.012,0.99), fontsize=8.6,
                frameon=True, fancybox=False, edgecolor="0.8")
leg.get_frame().set_facecolor("white"); leg.get_frame().set_alpha(0.95)
fig.tight_layout()
fig.savefig(str(FIG/"fig_anatomy.pdf"), bbox_inches="tight")
fig.savefig(str(FIG/"fig_anatomy.png"), bbox_inches="tight", dpi=150)
print("wrote", FIG/"fig_anatomy.pdf", " (r_f/r_g=%.4f, e^{-1/r_f}=%.1e)"%(rf, math.exp(-1/rf)))
