#!/usr/bin/env python3
"""make_figures.py — the figures of "Riemann Hypothesis over Finite Holographic Substrate" (20-rh), drawn from this package.

    python3 make_figures.py [OUT_DIR]          writes fig_circle.pdf, fig_primespec.pdf and fig_primecount.pdf (default OUT_DIR: figures/paper)

fig_circle.pdf     the critical circle of the Subject F_13, drawn in the chart: (a) the shell with the circle of C and,
                   on the other side of the momentum meridian, the circle of its half-turn C_{-1}; (b) the section through
                   the prime meridian; (c) the two circles, each seen from its own side of the momentum meridian, with the
                   zeros on C and the counts on C_{-1} (Theorem "The critical circle", rows 20:G13 and 20:G14).
fig_primespec.pdf  the spectrum of a window [chart] (Numerical Observation, rows 20:D13 to D15): (a) the windows of the
                   Subjects F_173 and F_1549, (b) the window of depth 10^6 with the von Mangoldt weight.
fig_primecount.pdf  the count of the primes on the window of the Subject F_1549 [chart] (Numerical Observation, row 20:D16):
                   (a) Riemann's formula with the zeros below the heights 35, 78 and 202, (b) the count from the window's
                   own dual below the same heights. Drawn at the paper's text width, 6.27 in.

The exact data come from rh.py: the drive and the quarter-turn of the frame, the squares of the shell, the spectrum of a
window and the classical heights. The drawing of the sphere is a chart: positions are angles of 2π/p a step.
Needs matplotlib. The same numbers give the same files: no date is written into them.
"""
import math, os, sys
import matplotlib
matplotlib.use("Agg")
import matplotlib.pyplot as plt
import rh

BLUE, RED, PURPLE, TEAL, GREY, INK = "#2f5fa8", "#b0586a", "#6a4c93", "#007f7f", "#9a9a9a", "#111111"
META = {"CreationDate": None, "Producer": None, "Creator": "make_figures.py"}
TAU = 2 * math.pi


def circle_data(p=13):
    """The exact data of the circle on the frame (p, g): for each phase m of a point of the sphere on the circle, the
    position a = (g^m + g^{-m})^{-1}, the zero a g^m of the point of C, and the residue of the point (-a, -m) of C_{-1},
    the count of that zero. counts[m] is also the residue of the half-turn of the point of C at the phase m.
    Phases run over -kappa < m < kappa (the phases m and m + 2 kappa name one point)."""
    kap = (p - 1) // 4; g = rh.generators(p)[0]; gi = pow(g, p - 2, p)
    zeros, counts = {}, {}
    for m in range(-kap + 1, kap):
        a = pow((pow(g, m % (p - 1), p) + pow(gi, m % (p - 1), p)) % p, p - 2, p)
        zeros[m] = a * pow(g, m % (p - 1), p) % p                         # the zero at the phase m
        counts[-m] = (-a) * pow(gi, m % (p - 1), p) % p                     # the point (-a, -m): the count of that zero
    assert all((zeros[m] + zeros[-m]) % p == 1 and (counts[m] + counts[-m]) % p == p - 1 for m in zeros)
    assert all(counts[-m] == (zeros[m] - 1) % p for m in zeros) and zeros[0] == 2 * kap + 1 and counts[0] == 2 * kap
    assert all(counts[m] == (-zeros[m]) % p for m in zeros)                 # the half-turn of the drive negates the residue
    return kap, g, zeros, counts


def fig_circle(out, p=13):
    kap, g, zeros, counts = circle_data(p)
    s, c = math.sin(math.pi / p), math.cos(math.pi / p)             # the planes and the radius of the two circles [chart]
    th_e = TAU * (kap + 1) / p                                      # the colatitude of the energy latitude L_{κ+1}
    fig = plt.figure(figsize=(6.6, 6.75))
    gs = fig.add_gridspec(2, 2, height_ratios=(2.92, 2.86), hspace=0.03, wspace=0.03)
    a1, a2, a3 = fig.add_subplot(gs[0, 0]), fig.add_subplot(gs[0, 1]), fig.add_subplot(gs[1, :])
    for ax in (a1, a2):
        ax.set_aspect("equal"); ax.axis("off"); ax.set_xlim(-1.42, 1.42); ax.set_ylim(-1.42, 1.5)
    a3.set_aspect("equal"); a3.axis("off"); a3.set_xlim(-2.84, 2.84); a3.set_ylim(-1.42, 1.44)
    ring = [k * TAU / 360 for k in range(361)]

    # (a) the shell: an orthographic view from above the prime meridian's side, the circle of C at X = +s, of C_{-1} at X = -s
    az, el = math.radians(-62), math.radians(17)
    R = (-math.sin(az), math.cos(az), 0.0)
    U = (-math.sin(el) * math.cos(az), -math.sin(el) * math.sin(az), math.cos(el))
    D = (math.cos(el) * math.cos(az), math.cos(el) * math.sin(az), math.sin(el))
    dot = lambda P, Q: P[0] * Q[0] + P[1] * Q[1] + P[2] * Q[2]
    scr = lambda P: (dot(P, R), dot(P, U))

    def curve(pts, color, lw, back=0.38, z=2):
        run, side = [], None
        for P in pts + [None]:
            vis = None if P is None else dot(P, D) >= 0
            if P is None or (side is not None and vis != side):
                if len(run) > 1:
                    xs, ys = [dot(Q, R) for Q in run], [dot(Q, U) for Q in run]
                    a1.plot(xs, ys, color=color, lw=lw if side else lw * 0.8, ls="-" if side else (0, (3, 2.5)), alpha=1 if side else back, zorder=z if side else 1,
                            solid_capstyle="round")
                run = [run[-1]] if run and P is not None else []
            if P is not None:
                run.append(P); side = vis
    a1.fill([math.cos(t) for t in ring], [math.sin(t) for t in ring], color="#f5f7fa", zorder=0)
    a1.plot([math.cos(t) for t in ring], [math.sin(t) for t in ring], color="#c9ced6", lw=0.9, zorder=1)
    for a in range(1, 2 * kap + 1):                                  # the latitudes L_a, faint
        th = TAU * a / p
        curve([(math.sin(th) * math.cos(t), math.sin(th) * math.sin(t), math.cos(th)) for t in ring], "#d5d9e0", 0.6, back=0.5, z=1)
    curve([(math.sin(t), 0.0, math.cos(t)) for t in ring], BLUE, 1.2)                                   # the prime meridian
    curve([(0.0, math.sin(t), math.cos(t)) for t in ring], RED, 1.5)                                    # the momentum meridian
    curve([(math.sin(th_e) * math.cos(t), math.sin(th_e) * math.sin(t), math.cos(th_e)) for t in ring], PURPLE, 1.8)
    for x in (s, -s):                                                                                   # the two circles
        curve([(x, c * math.sin(t), c * math.cos(t)) for t in ring], TEAL, 2.4, z=3)
    top, top1, pole = scr((s, 0.0, c)), scr((-s, 0.0, c)), scr((0.0, 0.0, 1.0))
    a1.plot(*top, "o", ms=5.5, color=TEAL, zorder=5)
    a1.plot(*top1, "o", ms=5.5, mfc="white", mec=TEAL, mew=1.3, zorder=5)
    a1.plot(*pole, "o", ms=4, color=INK, zorder=5)
    a1.annotate("$0$", pole, xytext=(-3, 9), textcoords="offset points", fontsize=9, color=INK)
    a1.annotate(r"$2^{-1}$", top, xytext=(16, 13), textcoords="offset points", fontsize=9.5, color=TEAL,
                arrowprops={"arrowstyle": "-", "color": TEAL, "lw": 0.6})
    a1.annotate(r"$\pi$", top1, xytext=(-20, 13), textcoords="offset points", fontsize=9.5, color=TEAL,
                arrowprops={"arrowstyle": "-", "color": TEAL, "lw": 0.6})
    tq = math.radians(-60); pad = {"boxstyle": "round,pad=0.12", "fc": "#f5f7fa", "ec": "none"}
    (xl, yl), (xr, yr) = scr((-s, c * math.sin(tq), c * math.cos(tq))), scr((s, c * math.sin(tq), c * math.cos(tq)))
    a1.text(xl - 0.07, yl, r"$\mathcal{C}_{-1}$", fontsize=10, color=TEAL, ha="right", va="center", bbox=pad, zorder=6)
    a1.text(xr + 0.07, yr, r"$\mathcal{C}$", fontsize=10, color=TEAL, ha="left", va="center", bbox=pad, zorder=6)
    a1.text(-1.36, 1.02, "momentum\nmeridian", fontsize=8.5, color=RED, ha="left", va="center")
    a1.text(1.38, -1.12, "prime\nmeridian", fontsize=8.5, color=BLUE, ha="right", va="center")
    a1.text(-1.38, -1.12, "energy latitude\n" + r"$L_{\kappa+1}$", fontsize=8.5, color=PURPLE, ha="left", va="center")
    a1.set_title("(a)", fontsize=10, loc="left", pad=2)

    # (b) the section through the prime meridian, Y = 0: the two chords, mirror images in the momentum meridian
    a2.plot([math.cos(t) for t in ring], [math.sin(t) for t in ring], color=BLUE, lw=1.2, zorder=1, solid_capstyle="round")
    a2.plot([0, 0], [-1.12, 1.12], color=RED, lw=1.5, zorder=2)
    for x in (s, -s):
        a2.plot([x, x], [-c, c], color=TEAL, lw=2.4, zorder=3, solid_capstyle="round")
    ze = math.cos(th_e); xe = math.sin(th_e)
    a2.plot([-xe, xe], [ze, ze], color=PURPLE, lw=1.8, zorder=2)
    zq = -s                                                         # the latitude of the centre, at the position κ + 3/4
    a2.plot([-c, c], [zq, zq], color=TEAL, lw=0.9, ls=(0, (1.5, 2.5)), zorder=2)
    k = 0.085; a2.plot([s, s + k, s + k], [zq + k, zq + k, zq], color=INK, lw=0.7, zorder=4)        # the right angle
    one = (math.sin(TAU / p), math.cos(TAU / p))
    for (x, y) in ((0, 1), one):
        a2.plot(x, y, "o", ms=4.5, color=INK, zorder=5)
    a2.plot(s, c, "o", ms=5, color=TEAL, zorder=5)
    a2.plot(-s, c, "o", ms=5, mfc="white", mec=TEAL, mew=1.3, zorder=5)
    for x in (s, -s):                                               # where the planes meet the prime meridian again
        a2.plot(x, -c, "o", ms=3.2, color=GREY, zorder=5)
    a2.annotate("$0$", (0, 1), xytext=(-3, 8), textcoords="offset points", fontsize=9, color=INK)
    a2.annotate(r"$2^{-1}=%d$, at $\frac{1}{2}$" % zeros[0], (s, c), xytext=(5, 16), textcoords="offset points", fontsize=8.5, color=TEAL)
    a2.annotate(r"$\pi=%d$, at $-\frac{1}{2}$" % counts[0], (-s, c), xytext=(-5, 16), textcoords="offset points", fontsize=8.5, color=TEAL, ha="right")
    a2.annotate("$1$", one, xytext=(7, -2), textcoords="offset points", fontsize=9, color=INK)
    a2.annotate(r"position $%d$" % counts[0], (s, -c), xytext=(6, -13), textcoords="offset points", fontsize=8, color=GREY)
    a2.annotate(r"position $%d$" % zeros[0], (-s, -c), xytext=(-6, -13), textcoords="offset points", fontsize=8, color=GREY, ha="right")
    a2.text(s + 0.07, 0.42, r"$\mathcal{C}$", fontsize=11, color=TEAL, ha="left", va="center")
    a2.text(-s - 0.07, 0.42, r"$\mathcal{C}_{-1}$", fontsize=11, color=TEAL, ha="right", va="center")
    a2.text(0.0, -1.3, "momentum meridian", fontsize=8.5, color=RED, ha="center", va="center")
    a2.text(-1.04, ze - 0.02, "energy\n" + r"$L_{\kappa+1}$", fontsize=8.5, color=PURPLE, ha="right", va="center")
    a2.text(c + 0.06, zq + 0.02, r"$L_{2^{-1}}$", fontsize=8.5, color=TEAL, ha="left", va="center")
    a2.set_title("(b)", fontsize=10, loc="left", pad=2)

    # (c) the two circles, each seen from its own side of the momentum meridian, the points at their phases [chart positions]
    xc, n = 1.3, p - 1
    def P3(m):                                                       # the point of a circle at the longitude of the phase m
        t = math.tan(TAU * m / n); y = s * t
        return y, math.sqrt(max(0.0, 1 - s * s * (1 + t * t)))
    a3.plot([0, 0], [-1.12, 1.12], color=RED, lw=1.5, zorder=2)
    for cx, table, filled, name in ((xc, zeros, True, r"zeros, $\mathcal{C}$"), (-xc, counts, False, r"counts, $\mathcal{C}_{-1}$")):
        a3.plot([cx + c * math.cos(t) for t in ring], [c * math.sin(t) for t in ring], color=TEAL, lw=2.4, zorder=2, solid_capstyle="round")
        a3.plot([cx, cx], [-1.12, 1.12], color=BLUE, lw=1.2, zorder=1)
        for m in sorted(table):                                      # the half-turn of the point at the phase m: the same point of the other circle
            x, y = P3(m)
            a3.plot(cx + x, y, "o", ms=5.5, mfc=TEAL if filled else "white", mec=TEAL, mew=1.3, zorder=5)
            a3.text(cx + x * 1.12, y + 0.2, f"${table[m]}$", ha="center", va="center", fontsize=9.5, color=INK, zorder=6)
        a3.text(cx, 0.2, name, ha="center", va="center", fontsize=9, color=TEAL, zorder=4,
                bbox={"boxstyle": "round,pad=0.15", "fc": "white", "ec": "none"})
    a3.annotate("", xy=(-0.36, -0.42), xytext=(0.36, -0.42), arrowprops={"arrowstyle": "->", "color": INK, "lw": 0.9}, zorder=6)
    a3.text(0.0, -0.64, "half-turn\nof the drive", ha="center", va="center", fontsize=8.5, color=INK, zorder=5,
            bbox={"boxstyle": "round,pad=0.15", "fc": "white", "ec": "none"})
    a3.text(0.0, -1.3, "momentum meridian", fontsize=8.5, color=RED, ha="center", va="center")
    a3.text(xc + 0.08, -1.26, "prime meridian", fontsize=8.5, color=BLUE, ha="left", va="center")
    a3.text(-xc - 0.08, -1.26, "prime meridian", fontsize=8.5, color=BLUE, ha="right", va="center")
    a3.set_title("(c)", fontsize=10, loc="left", pad=2)
    fig.savefig(os.path.join(out, "fig_circle.pdf"), bbox_inches="tight", metadata=META)
    fig.savefig(os.path.join(out, "fig_circle.png"), dpi=150, bbox_inches="tight"); plt.close(fig)


def fig_primespec(out):
    heights = rh.HEIGHTS[:10] + [52.970321]                          # the classical heights below 56 [import]
    t0, dt, steps = 0.0, 0.01, 5601
    grid = [t0 + j * dt for j in range(steps)]
    norm = lambda es, lo, hi: [e / max(e2 for t, e2 in zip(grid, es) if lo <= t <= hi) for e in es]
    fig, (a1, a2) = plt.subplots(2, 1, figsize=(7.4, 5.6), sharex=True, gridspec_kw={"hspace": 0.16})
    for depth, col, lab in ((13, "#2a7f62", r"$\mathbb{F}_{173}$: depth $13$, six primes"), (39, PURPLE, r"$\mathbb{F}_{1549}$: depth $39$, twelve primes")):
        a1.plot(grid, norm(rh.spectrum(depth, t0, dt, steps), 10, 36), color=col, lw=1.3, label=lab)
    a2.plot(grid, norm(rh.spectrum(10 ** 6, t0, dt, steps, kind="mangoldt"), 10, 52), color=INK, lw=0.9)
    for ax in (a1, a2):
        ax.axvspan(10, 36, color="#000000", alpha=0.05, lw=0)
        for z in heights: ax.axvline(z, color=INK, lw=0.6, ls=(0, (2, 3)))
        ax.set_xlim(0, 56); ax.set_ylim(0, 1.08); ax.tick_params(labelsize=8.5)
        for sp in ("top", "right"): ax.spines[sp].set_visible(False)
    a1.set_ylabel(r"$E_{\mathsf{q}}(t)$, normalised"); a1.set_title("(a)", fontsize=10, loc="left")
    a1.legend(frameon=False, fontsize=8.5, loc="lower right", bbox_to_anchor=(1.0, 1.0), ncol=2, borderaxespad=0.2)
    a2.set_xlabel(r"height $t$"); a2.set_ylabel("normalised")
    a2.set_title(r"(b)  depth $10^{6}$, the von Mangoldt weight", fontsize=10, loc="left")
    fig.savefig(os.path.join(out, "fig_primespec.pdf"), bbox_inches="tight", metadata=META)
    fig.savefig(os.path.join(out, "fig_primespec.png"), dpi=110, bbox_inches="tight"); plt.close(fig)


def fig_primecount(out, H=39):
    """The count of the primes on the window of depth H at the heights of rh.EMERGENCE: Riemann's formula with the zeros
    below each height (a), and the count from the window's own dual below the same height (b). The legends give the
    bound of rh.EMERGENCE on the difference from the count at the half-integers 2.5 to H - 0.5."""
    reds, blues = ["#e3a39a", "#c9604f", "#8f2416"], ["#a9c1ea", "#5f86d0", "#1f3f94"]
    primes = rh.window_weights(H)[0]; heights = [e[0] for e in rh.EMERGENCE]
    lo, hi, steps = 1.5, H + 1.0, 1200
    xs = [lo * (hi / lo) ** (j / steps) * (1 + 1e-9) for j in range(steps + 1)]                 # even steps of log x; no x is a label
    half = [n + 0.5 for n in range(2, H)]; count = lambda x: sum(1 for l in primes if l < x)
    formula = lambda pts: list(zip(*[rh.riemann_counts(x, heights) if x >= 2 else [0.0] * len(heights) for x in pts]))
    window = lambda pts: [[rh.window_count(H, T, x) for x in pts] for T in heights]
    curves = {"zeros": (formula(xs), formula(half)), "window": (window(xs), window(half))}
    fig, axes = plt.subplots(2, 1, figsize=(6.27, 5.2), sharex=True)
    stair_x = [lo] + [p for p in primes for _ in (0, 1)] + [hi]; stair_y = [k for k in range(len(primes) + 1) for _ in (0, 1)]
    for ax, kind, cols in ((axes[0], "zeros", reds), (axes[1], "window", blues)):
        for ys, yh, (T, nz, b_window, b_zeros, _), col in zip(*curves[kind], rh.EMERGENCE, cols):
            dev = max(abs(y - count(x)) for y, x in zip(yh, half)); bound = b_zeros if kind == "zeros" else b_window
            assert dev <= bound and nz == sum(1 for g in rh.HEIGHTS if g < T)
            lab = (f"{nz} zeros, below {T:.0f}" if kind == "zeros" else f"dual below {T:.0f}") + f"  (within {bound:.2f})"
            ax.plot(xs, ys, color=col, lw=1.3, label=lab, zorder=3)
        ax.plot(stair_x, stair_y, color=INK, lw=1.7, zorder=2, label=r"$\pi(x)$, the count of the window's primes")
        for p in primes: ax.axvline(p, color=GREY, lw=0.45, alpha=0.5, zorder=1)
        ax.set_xlim(lo, hi); ax.set_ylim(-0.6, len(primes) + 1.2); ax.set_ylabel("count of primes up to $x$", fontsize=9.5)
        ax.tick_params(labelsize=9)
        ax.legend(loc="lower right", fontsize=9, frameon=True, facecolor="white", edgecolor="none", framealpha=1.0, handlelength=1.6,
                  labelspacing=0.35, borderpad=0.25).set_zorder(4)
        for sp in ("top", "right"): ax.spines[sp].set_visible(False)
    axes[1].set_xlabel(r"position $x$ on the prime meridian", fontsize=9.5)
    axes[0].set_title(r"(a) Continuum: Riemann's formula, the zeros of $\zeta$", fontsize=10, loc="left", color=reds[2], pad=4)
    axes[1].set_title(r"(b) The window of $\mathbb{F}_{1549}$: twelve primes, no zero used", fontsize=10, loc="left", color=blues[2], pad=4)
    fig.tight_layout(h_pad=1.0)
    fig.savefig(os.path.join(out, "fig_primecount.pdf"), metadata=META)
    fig.savefig(os.path.join(out, "fig_primecount.png"), dpi=150); plt.close(fig)


if __name__ == "__main__":
    out = sys.argv[1] if len(sys.argv) > 1 else os.path.join(os.path.dirname(os.path.abspath(__file__)), "figures", "paper")
    os.makedirs(out, exist_ok=True)
    fig_circle(out); fig_primespec(out); fig_primecount(out)
    print("written:", ", ".join(sorted(f for f in os.listdir(out) if f.startswith(("fig_circle", "fig_primespec", "fig_primecount")))))
