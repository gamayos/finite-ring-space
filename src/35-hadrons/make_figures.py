#!/usr/bin/env python3
# Generates the two data figures (labelled [approx] visualisations of the exact FRC values and PDG):
#   fig_spectrum.pdf     -- FRC vs PDG light-hadron spectrum (octet, decuplet, vector nonet)
#   fig_strangeness.pdf  -- mass vs strangeness: decuplet + vector equal spacing
# The plotted FRC numbers are the exact-rational outputs of absolute_masses.py / vector_nonet.py;
# matplotlib is used only for the rendering. Run: python3 make_figures.py
import matplotlib
matplotlib.use("Agg")
import matplotlib.pyplot as plt

plt.rcParams.update({"font.size": 9, "font.family": "serif", "axes.linewidth": 0.7,
                     "xtick.major.width": 0.7, "ytick.major.width": 0.7})

# ---- data (MeV): (label, FRC, PDG, is_anchor) ----
octet = [("$N$",938.9,938.9,1),("$\\Lambda$",1115.7,1115.7,1),("$\\Sigma$",1179.8,1193.2,0),("$\\Xi$",1329.8,1318.3,0)]
decup = [("$\\Delta$",1232.0,1232.0,1),("$\\Sigma^*$",1376.7,1384.6,0),("$\\Xi^*$",1526.7,1533.4,0),("$\\Omega$",1681.9,1672.5,0)]
vect  = [("$\\rho$",775.3,775.3,1),("$\\omega$",775.3,782.7,0),("$K^*$",897.4,893.6,0),("$\\phi$",1019.5,1019.5,1)]

# ===== Figure 2: spectrum FRC vs PDG =====
fig, ax = plt.subplots(figsize=(6.4, 3.4))
groups = [("octet $\\mathbf{8}$", octet, 0), ("decuplet $\\mathbf{10}$", decup, 5.2), ("vector nonet", vect, 10.4)]
xticks, xlabels = [], []
for gname, states, x0 in groups:
    xs = [x0 + i for i in range(len(states))]
    for x,(lab,frc,pdg,anc) in zip(xs, states):
        ax.hlines(pdg, x-0.32, x+0.32, color="0.45", lw=3, zorder=1)            # PDG band
        ax.plot(x, frc, marker=("*" if anc else "D"), ms=(11 if anc else 6),
                color=("#1a7d3c" if anc else "#c0392b"), zorder=3, mec="k", mew=0.4)
        if not anc:
            ax.annotate(f"{(frc-pdg)/pdg*100:+.1f}%", (x, frc), textcoords="offset points",
                        xytext=(7,-1), fontsize=6.5, color="#c0392b")
        xticks.append(x); xlabels.append(lab)
    ax.text(x0+(len(states)-1)/2, 1735, gname, ha="center", fontsize=9)
ax.set_xticks(xticks); ax.set_xticklabels(xlabels)
ax.set_ylabel("mass  [MeV]"); ax.set_ylim(700, 1760); ax.set_xlim(-0.8, 14.0)
from matplotlib.lines import Line2D
ax.legend(handles=[Line2D([0],[0],color="0.45",lw=3,label="PDG 2024"),
                   Line2D([0],[0],marker="D",ls="",color="#c0392b",mec="k",mew=0.4,label="FRC (prediction)"),
                   Line2D([0],[0],marker="*",ls="",color="#1a7d3c",ms=11,mec="k",mew=0.4,label="FRC (anchor)")],
          loc="upper left", bbox_to_anchor=(0.005, 0.80), fontsize=7.5, frameon=False)
ax.grid(axis="y", color="0.9", lw=0.5)
fig.tight_layout(); fig.savefig("fig_spectrum.pdf"); plt.close(fig)

# ===== Figure 3: mass vs strangeness (equal spacing) =====
fig, ax = plt.subplots(figsize=(5.0, 3.4))
# decuplet n_s = 0,1,2,3 (PDG)
ns_d = [0,1,2,3]; m_d = [1232.0,1384.6,1533.4,1672.45]
a_d = m_d[0]; b_d = (m_d[-1]-m_d[0])/3
ax.plot([0,3],[a_d, a_d+3*b_d], "-", color="#c0392b", lw=1, zorder=1)
ax.plot(ns_d, m_d, "D", color="#c0392b", ms=6, mec="k", mew=0.4, label=f"decuplet ($\\beta\\simeq{b_d:.0f}$ MeV)")
for x,y,l in zip(ns_d,m_d,["$\\Delta$","$\\Sigma^*$","$\\Xi^*$","$\\Omega$"]):
    ax.annotate(l,(x,y),textcoords="offset points",xytext=(0,7),ha="center",fontsize=8)
# vector nonet n_s = 0,1,2 (PDG)
ns_v = [0,1,2]; m_v = [775.3,893.6,1019.5]
a_v = m_v[0]; b_v = (m_v[-1]-m_v[0])/2
ax.plot([0,2],[a_v, a_v+2*b_v], "-", color="#1a4fc0", lw=1, zorder=1)
ax.plot(ns_v, m_v, "o", color="#1a4fc0", ms=6, mec="k", mew=0.4, label=f"vector nonet ($b\\simeq{b_v:.0f}$ MeV)")
for x,y,l in zip(ns_v,m_v,["$\\rho$","$K^*$","$\\phi$"]):
    ax.annotate(l,(x,y),textcoords="offset points",xytext=(0,7),ha="center",fontsize=8)
ax.set_xlabel("strangeness count  $n_s$"); ax.set_ylabel("mass  [MeV]")
ax.set_xticks([0,1,2,3]); ax.set_xlim(-0.3,3.5); ax.set_ylim(700,1760)
ax.legend(loc="upper left", fontsize=7.5, frameon=False)
ax.grid(color="0.9", lw=0.5)
fig.tight_layout(); fig.savefig("fig_strangeness.pdf"); plt.close(fig)
print("wrote fig_spectrum.pdf, fig_strangeness.pdf")
