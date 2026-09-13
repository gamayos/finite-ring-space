#!/usr/bin/env python3
"""The registrable triangle -- companion figure for the s-estimation note.

Exact layer: the audit identities are asserted before drawing (algebraic
identities; float tolerance documents CODATA rounding).  Display layer
[approx]: log10 chart of the bounded-window mass--radius plane.  FRC
reading: the two walls are the two lattice generators (Compton = the
crossing hbar; Schwarzschild = the normalisation G); the apex is the Planck
anchor; the right wall is the totality on its own horizon; the record-depth
ruler saturates at the octant (pi/4) r_H/c, the same at every observational
frame chronon, while the rival chart's cosmic time runs on -- the paper's
saturation falsifier drawn.
"""
import matplotlib
matplotlib.use("Agg")
import matplotlib.pyplot as plt
from math import log10, pi, sqrt

plt.rcParams.update({
    "font.family": "serif", "mathtext.fontset": "cm",
    "font.size": 9, "axes.linewidth": 0.6,
})
INK, MID, SOFT, FILL = "0.15", "0.35", "0.52", "0.945"

# ---- imports [approx]: laboratory constants and the note's table ----
c, G, hbar = 2.99792458e8, 6.67430e-11, 1.054571817e-34
lP, mP = 1.616255e-35, 2.176434e-8
tP = lP / c                            # identity anchor; CODATA agrees to 1e-7
rH_L = 1.659e26                        # Lambda face (channel 1)
rows = [  # (label, r_H [m], cluster) from the note, Sec. 3; 4a gauge (excluded)
    ("1", 1.659e26, "L"), ("2a", 1.27e26, "R"), ("2b", 1.33e26, "R"),
    ("3", 1.19e26, "R"), ("4a", 1.29e26, "G"), ("4b", 1.64e26, "L"),
]
S_L = pi * (rH_L / lP) ** 2

# ---- audit asserts ----
t_oct = pi / 4 * rH_L / c
assert abs(t_oct - sqrt(pi) / 4 * sqrt(S_L) * tP) / t_oct < 1e-12
mean_R = sum(r for _, r, k in rows if k == "R") / 3    # evidence rows only
mean_L = sum(r for _, r, k in rows if k == "L") / 2
assert abs((mean_L / mean_R) ** 2 - 1.71) < 0.02      # two-cluster ratio on S (Valcin IV rows)
assert abs(1 / sqrt(0.685) - 1.208) < 0.002           # chart-identity r_H split
# entailed rate from the octant + measured Lambda (round-02 F1)
from math import tanh
_HL = sqrt(1.088e-52 * c ** 2 / 3) * 3.0857e22 / 1e3
assert abs(_HL / tanh(3 * pi / 8) - 67.4) < 0.15      # H0 = 67.4 km/s/Mpc
# wedge width is the count face with the solid angle stripped: sqrt(S/pi)
assert abs(log10(rH_L / lP) - log10(sqrt(S_L / pi))) < 1e-12

# ---- chart ----
xg, yg = log10, log10
comp = lambda x: log10(hbar / c) - x        # Compton:  m R = hbar/c
schw = lambda x: x - log10(2 * G / c**2)    # Schwarzschild: m = R c^2/2G
x_apex = (log10(hbar / c) + log10(2 * G / c**2)) / 2
xW = xg(rH_L)
x_oct = xg(pi / 4 * rH_L)

fig, ax = plt.subplots(figsize=(6.4, 8.9))
ax.set_aspect("equal", adjustable="box")

ax.fill([x_apex, xW, xW], [comp(x_apex), schw(xW), comp(xW)],
        color=FILL, zorder=0, lw=0)
ax.plot([x_apex, xW], [schw(x_apex), schw(xW)], color=INK, lw=1.1, zorder=3)
ax.plot([x_apex, xW], [comp(x_apex), comp(xW)], color=INK, lw=1.1, zorder=3)
ax.plot([xW, xW], [comp(xW) - 2.5, schw(xW) + 3.2], color=MID, lw=1.0,
        ls=(0, (5, 3)), zorder=3)

ax.text(-20, schw(-20) + 2.0, r"Schwarzschild $\;R=2Gm/c^{2}$ — the normalisation $G$",
        rotation=45, ha="center", va="center", fontsize=9.5, color=INK)
ax.text(-14, comp(-14) - 2.0, r"Compton $\;mRc=\hbar$ — the crossing $\hbar$",
        rotation=-45, ha="center", va="center", fontsize=9.5, color=INK)
ax.text(xW - 1.1, -26, r"$r_H$ — the totality wall", rotation=90,
        ha="center", va="center", fontsize=9.5, color=MID)
ax.text(3, 39, "over-closed (horizon)", fontsize=8.5, color=SOFT,
        ha="center", style="italic", rotation=0)
ax.text(-19, -42, "delocalised (no registration)", fontsize=8.5, color=SOFT,
        ha="center", style="italic")
ax.text(13.5, -9, "the registrable triangle", fontsize=11.5, color="0.45",
        ha="center")

# Planck apex and the totality point
ax.scatter([xg(lP)], [yg(mP)], s=22, color=INK, zorder=5)
ax.annotate(r"Planck apex $(\ell_P,\,m_P)$", (xg(lP), yg(mP)),
            textcoords="offset points", xytext=(0, -14), ha="left",
            fontsize=8.5, color=INK)
ax.scatter([xW], [schw(xW)], s=26, color=INK, zorder=5)
ax.annotate(r"$\Omega$ — the totality on its own horizon",
            (xW, schw(xW)), textcoords="offset points", xytext=(-10, -11),
            ha="right", fontsize=9, color=INK)

# reference marks [approx]
objs = [  # reference marks along the typical-object diagonal [approx]
    ("electron", 3.86e-13, 9.109e-31, (7, -3), "left"),
    ("proton", 8.4e-16, 1.673e-27, (5, 4), "left"),
    ("H atom", 5.29e-11, 1.674e-27, (6, -8), "left"),
    ("protein", 5.0e-9, 1e-22, (5, -3), "left"),
    ("virus", 1.0e-7, 1e-18, (5, -3), "left"),
    ("bacterium", 1.0e-6, 1e-15, (5, -3), "left"),
    ("human cell", 1.0e-5, 1e-12, (5, -3), "left"),
    ("ant", 4.0e-3, 3e-6, (-5, -2), "right"),
    ("observer", 1.0, 7e1, (5, -9), "left"),
    ("blue whale", 2.5e1, 1.5e5, (5, -2), "left"),
    ("comet", 5.0e3, 1e13, (5, -3), "left"),
    ("asteroid", 2.6e5, 2.6e20, (-6, -2), "right"),
    ("Moon", 1.74e6, 7.35e22, (4, -11), "left"),
    ("Earth", 6.37e6, 5.97e24, (5, -9), "left"),
    ("Sun", 6.96e8, 1.99e30, (5, -9), "left"),
    ("white dwarf", 7.0e6, 1.2e30, (0, -13), "center"),
    ("solar system", 6.0e12, 2e30, (5, -3), "left"),
    ("neutron star", 1.2e4, 2.8e30, (-6, -6), "right"),
    (r"$10M_\odot$ hole", 2.95e4, 1.99e31, (-6, 4), "right"),
    ("Sgr A*", 1.2e10, 8.2e36, (7, -3), "left"),
    ("globular cluster", 2.5e17, 1e36, (5, -8), "left"),
    ("galaxy", 4.7e20, 2e42, (2, -10), "left"),
    ("galaxy cluster", 5.0e22, 2e45, (0, -12), "right"),
    ("supercluster", 4.0e24, 5e47, (-9, -12), "center"),
]
# the object diagonal: ordinary least-squares regression over the ON-DIAGONAL
# scale-typical single observable objects, MID-WEDGE ONLY.  Wall residents
# are excluded by the same rule as every other exclusion: the electron sits
# on the Compton wall by construction (its R is its reduced Compton
# wavelength) and Sgr A* on the Schwarzschild wall (its R is its horizon
# radius), so both are wall-displaced, drawn hollow, and become
# out-of-sample checks of the diagonal's wall tangencies.  Also hollow:
# the proton (the H atom stripped to its Compton-scale core), the compact
# remnants (white dwarf, neutron star, stellar hole: collapsed ends hugging
# the Schwarzschild wall), the solar system (the Sun's mass gravitationally
# diluted), and the bound aggregates (globular cluster through supercluster:
# collections, not single typical objects, bending toward the totality point).
FIT = ["H atom", "protein", "virus", "bacterium",
       "human cell", "ant", "observer", "blue whale", "comet", "asteroid",
       "Moon", "Earth", "Sun"]
FIT_FULL = FIT + ["electron", "Sgr A*"]      # sensitivity population
pos = {n: (xg(R), yg(m)) for n, R, m, _, _ in objs}


def ols(names):
    n = len(names)
    sx = sum(pos[m][0] for m in names); sy = sum(pos[m][1] for m in names)
    sxx = sum(pos[m][0] ** 2 for m in names)
    sxy = sum(pos[m][0] * pos[m][1] for m in names)
    k = (n * sxy - sx * sy) / (n * sxx - sx * sx)
    return k, (sy - k * sx) / n


def ols_k3(names):                       # constrained k = 3 fit
    n = len(names)
    b = sum(pos[m][1] - 3 * pos[m][0] for m in names) / n
    return 3.0, b


k_fit, b_fit = ols(FIT)
k_full, b_full = ols(FIT_FULL)
k_c13, b_c13 = ols_k3(FIT)
k_c15, b_c15 = ols_k3(FIT_FULL)
x_lo = (log10(hbar / c) - b_fit) / (1 + k_fit)              # Compton-wall entry
x_hi = min((-log10(2 * G / c**2) - b_fit) / (k_fit - 1), xW)  # exit: wall or r_H
M_exit = 10 ** (x_hi - log10(2 * G / c**2)) / 1.989e30        # exit mass [Msun]

# ---- diagonal asserts + pass lines [approx] ----
assert abs(k_fit - 3.032) < 0.005, k_fit          # slope 3 within 1.1%
assert abs(10 ** b_fit / 1.00e3 - 1) < 0.05       # coefficient 1.00e3 kg/m^3
assert abs(k_full - 3.007) < 0.005, k_full        # sensitivity: walls included
assert abs(M_exit / 1.8e8 - 1) < 0.05             # over-closure bound [Msun]
assert abs(10 ** b_c13 / 0.97e3 - 1) < 0.05       # constrained k=3 coefficient


def exit_of(k, b):                                # exit mass of a fit variant
    xh = (-log10(2 * G / c**2) - b) / (k - 1)
    return 10 ** (xh - log10(2 * G / c**2)) / 1.989e30


band = sorted(exit_of(k, b) for k, b in
              ((k_fit, b_fit), (k_full, b_full), (k_c13, b_c13), (k_c15, b_c15)))
assert band[0] > 1.3e8 and band[-1] < 2.9e8       # over-closure band (1.4-2.8)e8
print(f"[PASS] constrained k=3: rho~ = {10 ** b_c13:.2e} kg/m^3; over-closure band"
      f" ({band[0]:.2e} .. {band[-1]:.2e}) Msun across the four fit variants")
assert abs(pos["electron"][1] - (log10(hbar / c) - pos["electron"][0])) < 0.01
assert abs(pos["Sgr A*"][1] - (pos["Sgr A*"][0] - log10(2 * G / c**2))) < 0.01
print(f"[PASS] diagonal: k = {k_fit:.4f} (13 mid-wedge), intercept "
      f"{10 ** b_fit:.2e} at the metre pivot (density units only at k = 3); "
      f"sensitivity k = {k_full:.4f} (15 incl. walls)")
print(f"[PASS] boundaries: Compton entry R = {10 ** x_lo:.2e} m; "
      f"over-closure exit M = {M_exit:.2e} Msun")
print(f"[PASS] wall residents on-wall to <0.01 dex: electron (Compton, "
      f"{x_lo - pos['electron'][0]:+.1f} dex beyond entry), "
      f"Sgr A* (Schwarzschild, {x_hi - pos['Sgr A*'][0]:+.1f} dex before exit)")

ax.plot([x_lo, x_hi], [b_fit + k_fit * x_lo, b_fit + k_fit * x_hi],
        color="0.62", lw=0.9, ls=(0, (1, 2.6)), zorder=2)
ax.text(-1.6, 12.5, r"typical objects: $m=\tilde\rho R^{3}$,"
        r"  $\tilde\rho\approx10^{3}\,$kg$\,$m$^{-3}$",
        rotation=71.6, ha="center", va="center", fontsize=7.5, color="0.5")

for name, R, m, off, ha in objs:
    if name in FIT:
        ax.scatter([xg(R)], [yg(m)], s=11, color="0.4", zorder=4)
    else:
        ax.scatter([xg(R)], [yg(m)], s=11, facecolors="white",
                   edgecolors="0.45", linewidths=0.9, zorder=4)
    ax.annotate(name, (xg(R), yg(m)), textcoords="offset points", xytext=off,
                fontsize=7.5, color="0.4", ha=ha)

# record-depth ruler (top interior): solid to the octant, dashed on, arrow
yr = 58.0
ax.plot([xg(c * tP), x_oct], [yr, yr], color=INK, lw=1.2, zorder=4)
ax.plot([x_oct, xW + 2.8], [yr, yr], color=SOFT, lw=0.9, ls=(0, (3, 3)), zorder=4)
ax.annotate("", (xW + 3.6, yr), (xW + 2.8, yr),
            arrowprops=dict(arrowstyle="->", color=SOFT, lw=0.9))
for tval, lab in ((tP, r"$t_P$"), (1.0, r"$1\,$s"), (3.15576e7, r"$1\,$yr"),
                  (3.15576e16, r"$1\,$Gyr")):
    xt = xg(c * tval)
    ax.plot([xt, xt], [yr - 0.8, yr + 0.8], color=INK, lw=0.8)
    ax.annotate(lab, (xt, yr - 2.0), ha="center", va="top", fontsize=8, color=INK)
ax.plot([x_oct, x_oct], [yr - 1.3, yr + 1.3], color=INK, lw=1.8)
ax.annotate("record depth saturates:  " + r"$(\pi/4)\,r_H/c = 13.8\;$Gyr",
            (x_oct - 0.8, yr + 2.0), ha="right", va="bottom", fontsize=8.5, color=INK)
ax.annotate("chart time\n(unbounded)", (xW + 1.3, yr - 1.4), ha="left", va="top",
            fontsize=7.2, color=SOFT)
ax.annotate(r"registrable depth $\;t = R/c$", (xg(c * tP) + 5.0, yr - 2.0),
            ha="left", va="top", fontsize=8.5, color=INK)

# axes cosmetics
ax.set_xlim(-37, 33.5)
ax.set_ylim(-45, 62)
ax.set_xlabel(r"$\log_{10} R\;$ [m]$\;$ [approx]", fontsize=9.5)
ax.set_ylabel(r"$\log_{10} m\;$ [kg]$\;$ [approx]", fontsize=9.5)
ax.set_xticks(range(-30, 31, 10))
ax.set_yticks(range(-60, 61, 20))
ax.tick_params(labelsize=8, color=MID, labelcolor=MID, length=3, width=0.6)
for s in ax.spines.values():
    s.set_color(MID)

# ---- inset: the wall, measured ----
axi = ax.inset_axes([-35.5, 31.5, 27.0, 20.0], transform=ax.transData)
axi.set_title("the wall, measured — six channels [approx]",
              fontsize=8, color=INK, pad=4)
for a, b in ((1.17, 1.35), (1.59, 1.68)):
    axi.axvspan(a, b, color=FILL)
order = {"3": 0, "2a": 1, "4a": 2, "2b": 3, "4b": 4, "1": 5}
for lab, r, k in rows:
    y = 0.16 + 0.105 * order[lab]
    axi.scatter([r / 1e26], [y], s=17, color=INK if k == "R" else "0.5", zorder=4)
    axi.annotate(lab, (r / 1e26, y), textcoords="offset points",
                 xytext=(4, -2.5), fontsize=7, color="0.3")
axi.axvline(pi / 4 * rH_L / 1e26, color=INK, lw=1.1, ls=(0, (4, 2)))
axi.annotate(r"$(\pi/4)\,r_H^{\Lambda}$", (pi / 4 * rH_L / 1e26, 0.80),
             ha="center", va="top", fontsize=7.5, color=INK)
axi.annotate("registered rate", (1.26, 0.035), ha="center", va="bottom",
             fontsize=7.5, color=MID)
axi.annotate(r"$\Lambda$ face", (1.635, 0.035), ha="center", va="bottom",
             fontsize=7.5, color=MID)
axi.annotate(r"split: the ladder--CMB (Hubble-tension) split; entailed $H_0=67.4$",
             (1.425, 0.875), ha="center", fontsize=7.2, color=INK)
axi.set_xlim(1.1, 1.75)
axi.set_ylim(0, 0.95)
axi.set_yticks([])
axi.set_xticks([1.2, 1.4, 1.6])
axi.set_xlabel(r"$r_H\;$ [$10^{26}\,$m]", fontsize=7.5, labelpad=2)
axi.tick_params(labelsize=7, color=MID, labelcolor=MID, length=2.5, width=0.5)
for s in axi.spines.values():
    s.set_color(MID); s.set_linewidth(0.5)

fig.subplots_adjust(left=0.11, right=0.97, top=0.985, bottom=0.05)
ax.set_xlim(-37, 33.5)
ax.set_ylim(-45, 62)   # re-assert: pinned after all children
fig.savefig("registrable-wedge-20260722.png", dpi=200)
fig.savefig("registrable-wedge-20260722.pdf")

# ---- plain version: no inlay (the channel strip ships as its own figure) ----
axi.remove()
fig.savefig("registrable-wedge-plain-20260722.png", dpi=200)
fig.savefig("registrable-wedge-plain-20260722.pdf")

# ---- standalone channels figure (the former inlay, proportioned for print) ----
fig2, ax2 = plt.subplots(figsize=(5.2, 2.3))
for a, b in ((1.17, 1.35), (1.59, 1.68)):
    ax2.axvspan(a, b, color=FILL)
for lab, r, k in rows:
    y = 0.14 + 0.135 * order[lab]
    ax2.scatter([r / 1e26], [y], s=26, color=INK if k == "R" else "0.5", zorder=4)
    ax2.annotate(lab, (r / 1e26, y), textcoords="offset points", xytext=(5, -3),
                 fontsize=8.5, color="0.3")
ax2.axvline(pi / 4 * rH_L / 1e26, color=INK, lw=1.2, ls=(0, (4, 2)))
ax2.annotate(r"$(\pi/4)\,r_H^{\Lambda}$" + "  (depth face)",
             (pi / 4 * rH_L / 1e26 + 0.012, 0.97), ha="left", va="top",
             fontsize=8.5, color=INK)
ax2.annotate("registered-rate cluster", (1.26, 0.035), ha="center", va="bottom",
             fontsize=8.5, color=MID)
ax2.annotate(r"$\Lambda$-face cluster", (1.635, 0.035), ha="center", va="bottom",
             fontsize=8.5, color=MID)
ax2.annotate(r"cluster split on $r_H$: the ladder--CMB split (Hubble tension); entailed rate $H_0=67.4\pm0.7$",
             (1.425, 1.05), ha="center", fontsize=8.5, color=INK,
             annotation_clip=False)
ax2.set_xlim(1.1, 1.75)
ax2.set_ylim(0, 0.97)
ax2.set_yticks([])
ax2.set_xticks([1.2, 1.3, 1.4, 1.5, 1.6, 1.7])
ax2.set_xlabel(r"$r_H\;$ [$10^{26}\,$m]   [approx]", fontsize=9)
ax2.tick_params(labelsize=8, color=MID, labelcolor=MID, length=3, width=0.6)
for sp in ax2.spines.values():
    sp.set_color(MID); sp.set_linewidth(0.6)
fig2.subplots_adjust(left=0.03, right=0.985, top=0.86, bottom=0.19)
fig2.savefig("wall-channels-20260722.png", dpi=200)
fig2.savefig("wall-channels-20260722.pdf")
print("ok")