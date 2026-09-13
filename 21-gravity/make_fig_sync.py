"""Figure: gravity as the relaxation of forced frame drift (schematic, Fig.~\\ref{fig:sync}).

Two massive objects are non-ideal embedded shells: a field has no proper ideals, so neither
frame can close, and each reads its own clock (different angles = the drift). There is no
universal clock they share. The mutual drift relaxes, lowering the coherence free energy E[u];
since distance is decoherence, reducing the drift is identically approach, so -grad E[u] is
the force.
"""
import pathlib, math, numpy as np, matplotlib
matplotlib.use("Agg")
import matplotlib.pyplot as plt
from matplotlib.patches import Circle, FancyArrowPatch, FancyBboxPatch
FIG = pathlib.Path(__file__).resolve().parent.parent / "figures"
plt.rcParams.update({"font.family":"serif","mathtext.fontset":"cm","font.size":11,
                     "axes.linewidth":0.8,"figure.dpi":150})

BLUE, ORANGE, RED, TEAL = "#1f4e79", "#b5651d", "#b00020", "#2f8f8f"
fig, ax = plt.subplots(figsize=(7.4,4.0))
ax.set_xlim(-6,6); ax.set_ylim(-3.2,3.0); ax.set_aspect("equal"); ax.axis("off")

def clock(cx, cy, r, hand_deg, col, label):
    ax.add_patch(Circle((cx,cy), r, fc="white", ec="0.45", lw=1.4, zorder=2))
    for k in range(12):                              # hour ticks
        a=math.radians(90-k*30)
        ax.plot([cx+(r-0.10)*math.cos(a), cx+r*math.cos(a)],
                [cy+(r-0.10)*math.sin(a), cy+r*math.sin(a)], color="0.6", lw=1.0, zorder=3)
    a=math.radians(hand_deg)
    ax.add_patch(FancyArrowPatch((cx,cy),(cx+0.74*r*math.cos(a), cy+0.74*r*math.sin(a)),
                 arrowstyle="-|>", mutation_scale=13, lw=2.6, color=col, zorder=4))
    ax.add_patch(Circle((cx,cy),0.055, fc="0.2", ec="none", zorder=5))
    ax.text(cx, cy-r-0.34, label, ha="center", fontsize=8.8, color="0.2")

# two non-ideal shells as clocks reading different times (the drift): 1 o'clock vs 11 o'clock
clock(-2.55, 0.45, 1.05, 60,  BLUE,   r"non-ideal shell  $m_1$")
clock( 2.55, 0.45, 1.05, 120, ORANGE, r"non-ideal shell  $m_2$")

# centre: the drift relaxes -> force
ax.text(0, 1.18, r"drift $\Delta\theta$", ha="center", fontsize=9.2, color="0.3")
ax.add_patch(FancyArrowPatch((-0.42,0.92),(0.42,0.92),connectionstyle="arc3,rad=-0.45",
             arrowstyle="<|-|>", mutation_scale=9, lw=1.3, color=TEAL, zorder=4))
ax.text(0, 0.55, "relaxes", ha="center", fontsize=8.2, color=TEAL)
ax.add_patch(FancyArrowPatch((-1.18,-0.05),(-0.55,-0.05),arrowstyle="-|>",mutation_scale=15,lw=2.2,color=RED,zorder=4))
ax.add_patch(FancyArrowPatch(( 1.18,-0.05),( 0.55,-0.05),arrowstyle="-|>",mutation_scale=15,lw=2.2,color=RED,zorder=4))
ax.text(0,-0.05, r"force $=-\nabla E[u]$", ha="center", va="center", fontsize=8.8, color=RED, zorder=6,
        bbox=dict(boxstyle="round,pad=0.26", fc="white", ec="none"))

# titles (top) and the two explanatory lines (full width, bottom)
ax.text(0, 2.62, "Gravity as the relaxation of forced frame drift", ha="center", fontsize=10.6, color="0.1")
ax.text(0, 2.04, r"two massive objects are non-ideal embedded shells (a field has no proper ideals), so their frames drift",
        ha="center", fontsize=8.6, color="0.3")
ax.text(0,-1.62, r"reducing the mutual drift $\equiv$ approach, since $r$ is decoherence",
        ha="center", fontsize=8.8, color="0.25")
ax.add_patch(FancyBboxPatch((-5.5,-2.78),11.0,0.52,boxstyle="round,pad=0.02",fc="#f4f4f6",ec="0.82",lw=0.9,zorder=0))
ax.text(0,-2.52, r"no universal clock: each shell reads its own projection of the one Carrier $\mathbb{F}_\Omega$ (a field, no proper ideals)",
        ha="center", fontsize=8.2, color="0.4")

fig.savefig(str(FIG/"fig_sync.pdf"), bbox_inches="tight")
fig.savefig(str(FIG/"fig_sync.png"), bbox_inches="tight", dpi=150)
print("wrote", FIG/"fig_sync.pdf")
