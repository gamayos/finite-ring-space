"""Figure: the registration crossover / radial acceleration relation (ledger D4, Fig.~\\ref{fig:rar}).

g_obs = g_N / (1 - e^{-sqrt(g_N/a0)}); deep slope 1/2 (deep-MOND sqrt(g_N a0)),
Newtonian slope 1, knee at the floor a0 = c H0 / 2pi. The continuum curve is the
[approx] reading of the exact registration fraction f = 1 - eta^a (validate_deepregime.py).
"""
import pathlib, numpy as np, matplotlib
matplotlib.use("Agg")
import matplotlib.pyplot as plt
FIG = pathlib.Path(__file__).resolve().parent.parent / "figures"
plt.rcParams.update({"font.family":"serif","mathtext.fontset":"cm","font.size":11,
                     "axes.linewidth":0.8,"figure.dpi":150})

x = np.logspace(-3,3,800)
y = x/(1.0-np.exp(-np.sqrt(x)))
fig,ax=plt.subplots(figsize=(5.4,4.2))
ax.plot(x,x,ls="--",lw=1.0,color="0.55",label=r"Newtonian  $g_{\mathrm{obs}}=g_N$  (slope 1)")
ax.plot(x,np.sqrt(x),ls="-.",lw=1.0,color="0.55",label=r"deep-MOND  $\sqrt{g_N a_0}$  (slope $\frac{1}{2}$)")
ax.plot(x,y,lw=2.2,color="#1f4e79",label=r"$g_{\mathrm{obs}}=g_N/(1-e^{-\sqrt{g_N/a_0}})$")
ax.axvline(1.0,ls=":",lw=0.9,color="#b00020")
ax.annotate(r"knee at $g_N=a_0=cH_0/2\pi$",xy=(1.0,1.6),xytext=(2.2,0.18),
            textcoords="data",fontsize=9,color="#b00020",
            arrowprops=dict(arrowstyle="->",color="#b00020",lw=0.8))
ax.annotate("slope 1",xy=(220,220),fontsize=9,color="0.35",rotation=33)
ax.annotate("slope 1/2",xy=(2e-3,0.10),fontsize=9,color="0.35",rotation=20)
ax.set_xscale("log");ax.set_yscale("log")
ax.set_xlim(1e-3,1e3);ax.set_ylim(3e-2,1e3)
ax.set_xlabel(r"$g_N/a_0$  (baryonic acceleration)")
ax.set_ylabel(r"$g_{\mathrm{obs}}/a_0$  (registered acceleration)")
ax.legend(loc="upper left",fontsize=8.3,frameon=False,handlelength=2.4)
ax.grid(True,which="major",ls="-",lw=0.4,color="0.9")
ax.grid(True,which="minor",ls="-",lw=0.25,color="0.95")
ax.text(0.98,0.03,"[approx] continuum reading of the exact\nregistration fraction $f=1-\\eta^{a}$",
        transform=ax.transAxes,ha="right",va="bottom",fontsize=7.2,color="0.4")
fig.tight_layout()
fig.savefig(str(FIG/"fig_rar.pdf"),bbox_inches="tight")
fig.savefig(str(FIG/"fig_rar.png"),bbox_inches="tight",dpi=150)
print("wrote", FIG/"fig_rar.pdf")
