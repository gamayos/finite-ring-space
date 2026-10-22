"""Framed complex plane figure for F_13(3;0,1,2) — verification rendering.

Canonical frame datum (FRC formalism, cf. the RH paper):
    frame (t;0,1,g_t),  i_t := -g_t^t = g_t^{-t},  e_t := g_t^{i_t}.
Orientation convention: imaginary axis up from the unit 1, phase rotation
g_t^m advancing clockwise.
At p=13, g_t=2:  i_t = -8 = 5,  e_t = 2^5 = 6,  pi_t = 6.

Axis labels: horizontal (f-reals) a <-> a mod p; vertical k*i <-> k*i_t mod p.
Output: f13-C-check.png (cross-check against the manuscript figure
f13-C-20260530.png, which is the canonical rendering).
"""

import math
import matplotlib

matplotlib.use("Agg")
import matplotlib.pyplot as plt

P = 13
G = 2
T = (P - 1) // 4
I_T = (-pow(G, T, P)) % P  # oriented quarter-turn -g^t: 5
assert (I_T * I_T) % P == P - 1

LIM = 5.85
R_MAX = 6.6

BLUE = "#1f77b4"
RED = "#d62728"
PURPLE = "#9467bd"
GREEN = "#2ca02c"
GRAY = "#888888"

fig, ax = plt.subplots(figsize=(7.1, 7.1), dpi=100)
ax.set_aspect("equal")
ax.axis("off")
ax.set_xlim(-LIM, LIM)
ax.set_ylim(-LIM, LIM)

# --- concentric circles through the lattice radii ---
radii = sorted({a * a + b * b for a in range(0, 7) for b in range(0, 7)
                if 0 < a * a + b * b <= R_MAX * R_MAX})
green_r2 = {2: 0.9, 5: 0.55, 8: 0.35}  # diagonal/near norm circles, graded
for r2 in radii:
    r = math.sqrt(r2)
    if r2 in green_r2:
        c = plt.Circle((0, 0), r, fill=False, color=GREEN,
                       alpha=green_r2[r2], lw=0.9, zorder=1)
    else:
        c = plt.Circle((0, 0), r, fill=False, color=GRAY,
                       alpha=0.18, lw=0.8, zorder=1)
    ax.add_patch(c)

# --- lattice points off the axes ---
for a in range(-6, 7):
    for b in range(-6, 7):
        if a == 0 or b == 0:
            continue
        if a * a + b * b <= R_MAX * R_MAX:
            ax.plot(a, b, ".", color=GRAY, ms=4.5, alpha=0.75, zorder=2)

# --- axes ---
ax.plot([-LIM, LIM], [0, 0], color=BLUE, lw=1.4, zorder=3)
ax.plot([0, 0], [-LIM, LIM], color=RED, lw=1.4, zorder=3)

# --- horizontal labels: black integers above, purple residues below ---
for a in range(-5, 6):
    if a == 0:
        continue
    ax.annotate(f"{a}", (a, 0), xytext=(0, 7), textcoords="offset points",
                ha="center", va="bottom", fontsize=13, color="black", zorder=4)
    ax.annotate(f"{a % P}", (a, 0), xytext=(0, -7), textcoords="offset points",
                ha="center", va="top", fontsize=12, color=PURPLE, zorder=4)
    ax.plot(a, 0, ".", color=BLUE, ms=4.5, zorder=4)

# --- vertical labels: red k*i left, purple residues right ---
for b in range(-5, 6):
    if b == 0:
        continue
    ax.annotate(f"{b}i", (0, b), xytext=(-7, 0), textcoords="offset points",
                ha="right", va="center", fontsize=13, color=RED, zorder=4)
    ax.annotate(f"{(b * I_T) % P}", (0, b), xytext=(7, 0),
                textcoords="offset points",
                ha="left", va="center", fontsize=12, color=PURPLE, zorder=4)
    ax.plot(0, b, ".", color=RED, ms=4.5, zorder=4)

# --- origin ---
ax.annotate("0", (0, 0), xytext=(-6, 6), textcoords="offset points",
            ha="right", va="bottom", fontsize=13, color=BLUE, zorder=5)
ax.plot(0, 0, "o", color=BLUE, ms=5.5, zorder=5)

fig.savefig("f13-C-check.png", bbox_inches="tight", facecolor="white")
print(f"i_t = {I_T}; labels:",
      {f"{b}i": (b * I_T) % P for b in range(-5, 6) if b})
