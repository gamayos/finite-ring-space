"""Figure 2, panel (a): the Carrier phase cycle (Fig.~\\ref{fig:phase}).

Phi^C ~ C_156 = F_157^x with primitive generator g = 5 (order 156, verified in the quantum
companion's validate.py); the four cardinal residues 1, i, -1, -i form the quarter-turn core
Q_4; the drive advances every cell one generator step (one chronon) per step, clockwise.
Panels (b) and (c) of Figure 2 are unchanged.
"""
import pathlib, math, matplotlib
matplotlib.use("Agg")
import matplotlib.pyplot as plt
from matplotlib.patches import Circle, FancyArrowPatch
FIG = pathlib.Path(__file__).resolve().parent.parent / "figures"
plt.rcParams.update({"font.family":"serif","mathtext.fontset":"cm","figure.dpi":150})

# sanity: 5 is a primitive root mod 157 (order 156)
def order(a,m):
    o,x=1,a%m
    while x!=1: x=(x*a)%m; o+=1
    return o
assert order(5,157)==156, "5 must be a primitive root mod 157"

fig, ax = plt.subplots(figsize=(3.4,3.4))
ax.set_aspect("equal"); ax.axis("off"); ax.set_xlim(-1.34,1.34); ax.set_ylim(-1.34,1.34)
N=156
ax.add_patch(Circle((0,0),1.0, fill=False, ec="0.72", lw=1.6, zorder=2))
for k in range(N):
    a=math.radians(90 - k*360/N)
    ax.plot([math.cos(a)*1.0, math.cos(a)*0.955],[math.sin(a)*1.0, math.sin(a)*0.955],
            color="0.6", lw=0.6, zorder=1)
cards=[(0,"$1$",(0,0.16)),(39,"$i$",(0.16,0)),(78,r"$-1$",(0,-0.18)),(117,r"$-i$",(-0.18,0))]
for k,lab,off in cards:
    a=math.radians(90 - k*360/N); x,y=math.cos(a),math.sin(a)
    ax.plot([x],[y],"o",ms=9,color="black",zorder=4)
    ax.text(x*1.18+off[0], y*1.18+off[1], lab, ha="center", va="center", fontsize=21)
ax.text(0, 0.12, r"$\Phi^{\mathrm{C}}\simeq C_{156}$", ha="center", va="center", fontsize=16)
ax.text(0,-0.13, r"$g=5$", ha="center", va="center", fontsize=16)
a1=math.radians(74); a2=math.radians(47); R=1.13
ax.add_patch(FancyArrowPatch((math.cos(a1)*R,math.sin(a1)*R),(math.cos(a2)*R,math.sin(a2)*R),
             connectionstyle="arc3,rad=-0.32", arrowstyle="-|>", mutation_scale=16,
             lw=2.4, color="#cc1133", zorder=5))
fig.savefig(str(FIG/"fig_phase_a.pdf"), bbox_inches="tight")
fig.savefig(str(FIG/"fig_phase_a.png"), bbox_inches="tight", dpi=150)
print("wrote", FIG/"fig_phase_a.pdf", " (order of 5 mod 157 = 156)")
