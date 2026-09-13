"""Three alternate designs for the frame-drift schematic (NOT used in the paper).

Each restores the composite-cluster multiplicity (many locked clocks per shell) while keeping
the drift framing of fig_sync. Same shared frame (title, drift->force, explanatory lines);
the three differ only in how each shell is drawn:

  altA  tinted disc with a bundle of aligned arrows (two bundles at different angles = drift)
  altB  clock face with a fan of hands (two clocks reading different times)
  altC  phase dial with a dashed nominal-universal reference, the arrow bundle deviating from it

Writes figures/fig_sync_altA.{pdf,png}, ...altB..., ...altC...  Pick one and, if desired,
copy it over fig_sync.* (or point the \\includegraphics at it).
"""
import pathlib, math, matplotlib
matplotlib.use("Agg")
import matplotlib.pyplot as plt
from matplotlib.patches import Circle, FancyArrowPatch, FancyBboxPatch
FIG = pathlib.Path(__file__).resolve().parent.parent / "figures"
plt.rcParams.update({"font.family":"serif","mathtext.fontset":"cm","font.size":11,
                     "axes.linewidth":0.8,"figure.dpi":150})
BLUE, ORANGE, RED, TEAL = "#1f4e79", "#b5651d", "#b00020", "#2f8f8f"
LX, RX, CY, R = -2.55, 2.55, 0.45, 1.05

def frame(ax):
    ax.set_xlim(-6,6); ax.set_ylim(-3.2,3.0); ax.set_aspect("equal"); ax.axis("off")
    ax.text(0, 2.62, "Gravity as the relaxation of forced frame drift", ha="center", fontsize=10.6, color="0.1")
    ax.text(0, 2.04, r"two massive objects are non-ideal embedded shells (a field has no proper ideals), so their frames drift",
            ha="center", fontsize=8.6, color="0.3")
    ax.text(0, 1.18, r"drift $\Delta\theta$", ha="center", fontsize=9.2, color="0.3")
    ax.add_patch(FancyArrowPatch((-0.42,0.92),(0.42,0.92),connectionstyle="arc3,rad=-0.45",
                 arrowstyle="<|-|>", mutation_scale=9, lw=1.3, color=TEAL, zorder=4))
    ax.text(0, 0.55, "relaxes", ha="center", fontsize=8.2, color=TEAL)
    ax.add_patch(FancyArrowPatch((-1.18,-0.05),(-0.55,-0.05),arrowstyle="-|>",mutation_scale=15,lw=2.2,color=RED,zorder=4))
    ax.add_patch(FancyArrowPatch(( 1.18,-0.05),( 0.55,-0.05),arrowstyle="-|>",mutation_scale=15,lw=2.2,color=RED,zorder=4))
    ax.text(0,-0.05, r"force $=-\nabla E[u]$", ha="center", va="center", fontsize=8.8, color=RED, zorder=6,
            bbox=dict(boxstyle="round,pad=0.26", fc="white", ec="none"))
    ax.text(0,-1.62, r"reducing the mutual drift $\equiv$ approach, since $r$ is decoherence",
            ha="center", fontsize=8.8, color="0.25")
    ax.add_patch(FancyBboxPatch((-5.5,-2.78),11.0,0.52,boxstyle="round,pad=0.02",fc="#f4f4f6",ec="0.82",lw=0.9,zorder=0))
    ax.text(0,-2.52, r"no universal clock: each shell reads its own projection of the one Carrier $\mathbb{F}_\Omega$ (a field, no proper ideals)",
            ha="center", fontsize=8.2, color="0.4")

BUNDLE = [(-0.42,-0.30),(0.08,-0.46),(0.5,-0.08),(-0.5,0.22),(0.0,0.16),(0.42,0.42),(-0.08,0.55)]

def shell_bundle(ax, cx, ang, fill, label):     # altA
    ax.add_patch(Circle((cx,CY), R, fc=fill, ec="0.4", lw=1.2, alpha=0.9, zorder=2))
    a=math.radians(ang); L=0.5
    for dx,dy in BUNDLE:
        ax.add_patch(FancyArrowPatch((cx+dx,CY+dy),(cx+dx+L*math.cos(a),CY+dy+L*math.sin(a)),
                     arrowstyle="-|>",mutation_scale=8,lw=1.5,color="0.15",zorder=3))
    ax.text(cx,CY-R-0.34,label,ha="center",fontsize=8.8,color="0.2")

def shell_clockfan(ax, cx, ang, col, label):    # altB
    ax.add_patch(Circle((cx,CY), R, fc="white", ec="0.45", lw=1.4, zorder=2))
    for k in range(12):
        a=math.radians(90-k*30)
        ax.plot([cx+(R-0.10)*math.cos(a),cx+R*math.cos(a)],[CY+(R-0.10)*math.sin(a),CY+R*math.sin(a)],color="0.6",lw=1.0,zorder=3)
    for d,Lf in [(-18,0.58),(-9,0.70),(0,0.78),(9,0.70),(18,0.58)]:
        a=math.radians(ang+d)
        ax.add_patch(FancyArrowPatch((cx,CY),(cx+Lf*R*math.cos(a),CY+Lf*R*math.sin(a)),
                     arrowstyle="-|>",mutation_scale=9,lw=1.7,color=col,zorder=4))
    ax.add_patch(Circle((cx,CY),0.055,fc="0.2",ec="none",zorder=5))
    ax.text(cx,CY-R-0.34,label,ha="center",fontsize=8.8,color="0.2")

def shell_refdial(ax, cx, ang, col, label):     # altC
    ax.add_patch(Circle((cx,CY), R, fc="white", ec="0.5", lw=1.3, zorder=2))
    for k in range(24):
        a=math.radians(90-k*15)
        ax.plot([cx+(R-0.06)*math.cos(a),cx+R*math.cos(a)],[CY+(R-0.06)*math.sin(a),CY+R*math.sin(a)],color="0.72",lw=0.7,zorder=3)
    ax.plot([cx,cx],[CY,CY+0.84*R],ls=(0,(4,3)),lw=1.2,color="0.55",zorder=3)   # nominal universal direction
    ax.text(cx,CY+0.84*R+0.12,"ref.",ha="center",fontsize=6.8,color="0.55")
    for d in (-11,-4,4,11):
        a=math.radians(ang+d)
        ax.add_patch(FancyArrowPatch((cx,CY),(cx+0.74*R*math.cos(a),CY+0.74*R*math.sin(a)),
                     arrowstyle="-|>",mutation_scale=9,lw=1.7,color=col,zorder=4))
    ax.add_patch(Circle((cx,CY),0.05,fc="0.2",ec="none",zorder=5))
    ax.text(cx,CY-R-0.34,label,ha="center",fontsize=8.8,color="0.2")

def build(shell_fn, langle, rangle, lc, rc, name):
    fig, ax = plt.subplots(figsize=(7.4,4.0)); frame(ax)
    shell_fn(ax, LX, langle, lc, r"non-ideal shell  $m_1$")
    shell_fn(ax, RX, rangle, rc, r"non-ideal shell  $m_2$")
    fig.savefig(str(FIG/f"{name}.pdf"), bbox_inches="tight")
    fig.savefig(str(FIG/f"{name}.png"), bbox_inches="tight", dpi=150)
    plt.close(fig); print("wrote", FIG/f"{name}.pdf")

build(shell_bundle,   72, 48,  "#cfe0f2", "#f7e0c8", "fig_sync_altA")
build(shell_clockfan, 60, 120, BLUE,      ORANGE,    "fig_sync_altB")
build(shell_refdial,  66, 114, BLUE,      ORANGE,    "fig_sync_altC")
