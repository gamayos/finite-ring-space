"""Figure: strong-field signatures vs current data (Fig.~\\ref{fig:shadow}).

Left: the Sgr A* shadow, FRC (b_c = 2e Gm/c^2) a parameter-free +4.6% wider than GR
(b_c = 3 sqrt3 Gm/c^2), 55.7 vs 53.3 uas. Right: fractional deviation from GR; the shadow
prediction +4.6% sits ~1 sigma above the EHT Keck/VLTI constraints; ringdown -4.4% (GW);
echoes absent. [approx] empirical comparison.
"""
import pathlib, math, matplotlib
matplotlib.use("Agg")
import matplotlib.pyplot as plt
from matplotlib.patches import Circle
FIG = pathlib.Path(__file__).resolve().parent.parent / "figures"
plt.rcParams.update({"font.family":"serif","mathtext.fontset":"cm","font.size":11,
                     "axes.linewidth":0.8,"figure.dpi":150})

d_gr, d_frc = 53.3, 55.7
r_gr, r_frc = d_gr/2, d_frc/2
dshadow = 2*math.e/(3*math.sqrt(3))-1     # +0.0463
dring   = 3*math.sqrt(3)/(2*math.e)-1     # -0.0442

fig, (axA, axB) = plt.subplots(1, 2, figsize=(7.6,3.7), gridspec_kw=dict(width_ratios=[1,1.32]))
# (a) shadow rings
axA.set_aspect("equal")
axA.add_patch(Circle((0,0), r_frc+3.0, facecolor="#fdf3da", edgecolor="none", zorder=0))
axA.add_patch(Circle((0,0), r_frc, facecolor="none", edgecolor="#1f4e79", lw=2.4, zorder=4))
axA.add_patch(Circle((0,0), r_gr,  facecolor="#3a3a3a", edgecolor="0.2", lw=1.0, zorder=3))
axA.annotate("GR  "+r"$b_c=3\sqrt{3}\,Gm/c^2$"+"\n"+r"$53.3\,\mu$as",
             xy=(0,-r_gr*0.18), ha="center", va="center", color="white", fontsize=8.0, zorder=5)
axA.annotate("FRC  "+r"$b_c=2e\,Gm/c^2$"+",  +4.6%"+"\n"+r"$55.7\,\mu$as",
             xy=(0, r_frc+4.6), ha="center", va="bottom", color="#1f4e79", fontsize=8.3)
axA.set_xlim(-r_frc-7, r_frc+7); axA.set_ylim(-r_frc-7, r_frc+11); axA.axis("off")
axA.set_title(r"Sgr A$^*$ shadow", fontsize=9.5)
# (b) deviation forest vs EHT
for i,(lab,c,lo,hi) in enumerate([("EHT Keck",-4.0,10.0,9.0),("EHT VLTI",-8.0,9.0,9.0)]):
    yy=3-i
    axB.errorbar(c, yy, xerr=[[lo],[hi]], fmt="o", color="0.30", ecolor="0.30", capsize=3, ms=5, lw=1.3)
    axB.text(c, yy+0.24, lab, ha="center", fontsize=8.0, color="0.25")
axB.plot(dshadow*100, 1.0, "s", color="#1f4e79", ms=7)
axB.text(dshadow*100, 1.0+0.24, "FRC shadow +4.6%", ha="center", fontsize=8.2, color="#1f4e79")
axB.plot(dring*100, 0.0, "D", color="#7a3030", ms=6)
axB.text(dring*100, 0.0+0.24, "FRC ringdown -4.4% (GW)", ha="center", fontsize=8.2, color="#7a3030")
axB.axvline(0, ls="--", lw=1.0, color="0.55")
axB.text(0, 3.75, "GR", ha="center", fontsize=8.5, color="0.4")
axB.set_ylim(-0.6, 4.05); axB.set_xlim(-21, 13)
axB.set_yticks([]); axB.set_xlabel(r"fractional deviation from GR,  $\delta$ (%)")
axB.set_title("Shadow size & ringdown vs current data", fontsize=9.5)
for s in ["left","right","top"]: axB.spines[s].set_visible(False)
axB.text(0.99,0.02,r"echoes: absent ($\Delta t\sim\Omega$)", transform=axB.transAxes,
         ha="right", va="bottom", fontsize=7.6, color="0.45")
fig.tight_layout()
fig.savefig(str(FIG/"fig_shadow.pdf"), bbox_inches="tight")
fig.savefig(str(FIG/"fig_shadow.png"), bbox_inches="tight", dpi=150)
print("wrote", FIG/"fig_shadow.pdf", " (+%.2f%% / %.2f%%)"%(dshadow*100,dring*100))
