"""
rh.py — the validation package of "Riemann Hypothesis over Finite Holographic Substrate" (Akhtman & Voether, 2026; Preprints
doi 10.20944/preprints202606.0768.v1), the paper 20-rh of the FRC corpus (finite-ring-space/src/20-rh). One script since
24 September 2026; rewritten with the paper on 17 October 2026 (reports/blueprint-20261017.md): the chart-side blocks of the
earlier versions (the de-framing dictionary's density and residue, the prime-side spectrum, the GUE statistic, the χ-twist,
Turing's count and certificate, the resonance) are gone with the rows they witnessed, and the exact checks of the shell carry
the paper.
========================================================================================================================

Three blocks, 107 checks — 91 EXACT (integer-pinned: a pass is a proof on the tested instances), 5 [approx] (a floating-point
reading of the chart's characters to a stated tolerance), 11 [chart] (a continuum reading of a finite object; notation.tex
convention 6) — Python with numpy and matplotlib (the paper's two drawn figures are redrawn into figures/paper/ as the blocks run; Figure 1 is the dimensions paper's).
Each check names the predicate(s) of the paper's ledger it witnesses (LEDGER; predicates cited as 20:XN), and the deciding
check's `# 20:XN (<key>)` marker is what the ledger's source column links (PREDICATES; finitering.space/py/rh.html#<key>).
Master-ledger predicates reached through the paper's rows: 00:A2 (Finitude, 20:A2), 00:A3 (Completeness, 20:A3) and 00:A4
(Observation, 20:A4).

Block A  the shell, in exact arithmetic (EXACT, one [approx]; 20:A2, A3, A4, B1, B2, B4–B6, B8–B10, B12–B14, E12–E15, F7, F10, O9):
         the zero-slot, slot complementarity, the Hermitian phase calculus, the critical line, the two agreement loci among all
         affine lines, the Subject constants, the shell theorem's five clauses on random vectors, the Parseval identity, the
         critical line as the energy domain, frame coincidence below the horizon and on the line, no zero off the line, the
         closure, completeness, the generators that do not order the window, the drive theorem and the circle
Block B  the chart ([chart]; 20:B8, F9, O9): the de-framing limit, the exhibit on the windows of depth 13, 39 and 173, the
         pair agreement on (173, 30089) and (1549, 2408561), and the labels read in the cycle's own scale coordinate
Block C  the chart at depth ([chart]; 20:F9): the window of depth 10⁶ and the first ten heights; the figure fig_primespec

    python3 rh.py                every block in order, results.json written; exit 1 if a check fails (≈ 100 s on one core:
                                 block A 75 s, block C 20 s)
    python3 rh.py A B            the blocks named (A, B, C); no results.json
    from frc_20_rh import predicate; predicate("20:B12")    one predicate: the blocks of the checks citing it run once per session
"""
import os, json, sys, math, cmath, time, random
from fractions import Fraction
import numpy as np
import matplotlib
matplotlib.use("Agg")
import matplotlib.pyplot as plt
from matplotlib.patches import FancyArrowPatch

SCRIPT = os.path.splitext(os.path.basename(__file__))[0]        # "rh": the one script, the name results.json and the site pages carry
FIGDIR = os.environ.get("RH_FIGDIR", "figures")
os.makedirs(f"{FIGDIR}/paper", exist_ok=True)

# ----------------------------------------------------------------------------- registry
RESULTS = []

# The paper's predicate ledger (20-rh Appendix A, predicates cited as 20:XN): the predicate(s) each check witnesses. The
# ledger's source column cites these check ids in return. The check ids A8 and A9 are retired with their rows (the Lanczos
# matrix, the Ramanujan sum; 17 October 2026) and are not reused.
LEDGER = {
    "A1": "20:B4", "A2": "20:B5", "A3": "20:B6", "A4": "20:B8", "A5": "20:B9", "A6": "20:B10", "A6b": "20:B10",
    "A7": "20:E12, 20:E14", "A7b": "20:E13", "A10": "20:B1", "A11": "20:B2", "A12": "20:A2, 20:A4, 20:F7", "A13": "20:A3",
    "A14": "20:E13", "A15": "20:B12", "A16": "20:B13", "A17": "20:O9", "A18": "20:F10, 20:B9, 20:B13", "A19": "20:E15", "A20": "20:B14",
    "B3": "20:B8", "B5": "20:F9", "B6": "20:F9", "B8": "20:O9",
    "C1": "20:F9",
}

BLOCK = {"A": "the shell, in exact arithmetic: the zero-slot, the critical line, the agreement loci, the shell theorem, the Parseval identity, the energy domain, frame coincidence, the closure, completeness, the window's order, the drive theorem, the circle",
         "B": "the chart: the de-framing limit, the exhibit on the windows 13, 39, 173, the pair agreement, the cycle's own scale coordinate",
         "C": "the chart at depth: the window of depth 10⁶ and the first ten heights; the figure fig_primespec"}

# the deciding check of each python-witnessed predicate: the check the ledger's source column names (the other checks that
# cite it are corroboration, listed by predicate() from the records)
PREDICATES = {
    "20:B1": "A10", "20:B2": "A11", "20:B4": "A1", "20:B5": "A2", "20:B6": "A3", "20:B8": "A4", "20:B9": "A5", "20:B10": "A6",
    "20:B12": "A15", "20:B13": "A16", "20:A2": "A12", "20:A3": "A13", "20:A4": "A12", "20:F7": "A12",
    "20:E12": "A7", "20:E13": "A14", "20:E14": "A7", "20:F9": "B5", "20:O9": "A17", "20:F10": "A18", "20:E15": "A19", "20:B14": "A20",
}
_RAN = set()                                            # blocks already run in this session (predicate() runs each once)

def check(pid, label, ok, detail="", kind="EXACT"):
    """Record one predicate check. pid = package check id (A1, B5, ...); LEDGER[pid] = the paper's ledger predicate(s)."""
    ok = bool(ok)
    rows = LEDGER[pid]
    RESULTS.append({"id": pid, "rows": rows, "block": pid[0], "script": SCRIPT, "label": label, "ok": ok, "detail": detail, "kind": kind})
    print(f"  [{'PASS' if ok else 'FAIL'}] {pid:4s} {kind:7s} [{rows}] {label}" + (f"  --  {detail}" if detail else ""))
    return ok

def summary(write=True):
    n_ok = sum(r["ok"] for r in RESULTS)
    print(f"\nSUMMARY: {n_ok}/{len(RESULTS)} checks passed" + ("" if n_ok == len(RESULTS) else "  <-- FAILURES"))
    if write:
        with open("results.json", "w") as f:
            json.dump(RESULTS, f, indent=1)
    return n_ok == len(RESULTS)

def markers():
    """predicate label -> (script file, line) of its marker `# <paper>:<label> (<key>)`: the line of the check that decides it."""
    import re
    out = {}
    for i, line in enumerate(open(os.path.abspath(__file__), encoding="utf-8"), 1):
        m = re.match(r"\s*# ((?:\d+:[A-Z]+\d+[a-z]?(?: \(p\d{5}\))?)(?:, \d+:[A-Z]+\d+[a-z]?(?: \(p\d{5}\))?)*)\s*$", line)
        if m:
            for lab in re.findall(r"\d+:[A-Z]+\d+[a-z]?", m.group(1)): out.setdefault(lab, (SCRIPT + ".py", i))
    return out

def _run_block(letter):
    if letter not in _RAN:
        globals()[f"block_{letter}"](); _RAN.add(letter)

def predicate(label, lines=14):
    """Verify one ledger predicate: run the blocks of the checks that cite it (each once per session), print the deciding check's
    source (from its marker) and every record that cites the predicate, and return True iff all pass."""
    pid = PREDICATES.get(label)
    if pid is None:
        print(f"{label}: no python witness (see the predicate's Lean witness or its source)"); return None
    citing = {i[0] for i, rows in LEDGER.items() if label in [t.strip() for t in rows.split(",")]}
    for b in sorted({pid[0]} | citing): _run_block(b)          # the deciding block and every block whose checks cite the predicate
    mk = markers().get(label)
    if mk:
        src = open(os.path.abspath(__file__), encoding="utf-8").read().split("\n")
        print(f"— {mk[0]}:{mk[1]} (the check that decides {label}: {pid})")
        for j in range(mk[1] - 1, min(mk[1] - 1 + lines, len(src))): print(f"{j + 1:5d}  {src[j]}")
    recs = [r for r in RESULTS if label in [t.strip() for t in r["rows"].split(",")]]
    ok = all(r["ok"] for r in recs)
    for r in recs:
        role = "(deciding)" if r["id"] == pid else "(corroborating)"
        print(f"  [{'PASS' if r['ok'] else 'FAIL'}] {r['id']:4s} {role:16s} {r['detail'][:150]}")
    print(f"{label}: {'VERIFIED' if ok and recs else 'FAILED'} — {len(recs)} record(s)")
    return ok

def verify_all():
    """Run every block (those already run in this session are not re-run) and print the summary; True iff every check passed."""
    for b in sorted(BLOCK): _run_block(b)
    return summary(write=False)

# ----------------------------------------------------------------------------- the arithmetic of the shell (standard library)
SHELLS = [13, 17, 29, 37, 41]          # in full
BIG = 173                               # the laboratory Subject of (173, 30089): A1, A4, A6, A7, A14, A15
PAIRS = ((13, 233), (173, 30089), (1549, 2408561))      # the laboratory pairs (p, Ω), Ω the Carrier of the Subject p (Def. shells)
HEIGHTS = [14.134725, 21.022040, 25.010858, 30.424876, 32.935062, 37.586178, 40.918719, 43.327073, 48.005151, 49.773832]
# the first ten classical heights (Odlyzko's tables), validation markers of the chart blocks: never an input

def is_prime(n):
    if n < 2: return False
    d = 2
    while d * d <= n:
        if n % d == 0: return False
        d += 1
    return True

def next_prime(n):
    n += 1
    while not is_prime(n): n += 1
    return n

def prime_factors(n):
    f, d = set(), 2
    while d * d <= n:
        while n % d == 0:
            f.add(d); n //= d
        d += 1
    if n > 1: f.add(n)
    return f

def generator(p):
    """The least primitive root of F_p: the Subject's generator g, as the paper takes it."""
    for g in range(2, p):
        if all(pow(g, (p - 1) // q, p) != 1 for q in prime_factors(p - 1)):
            return g

def nonresidue(p):
    sq = {(x * x) % p for x in range(1, p)}
    return next(v for v in range(2, p) if v not in sq)

def dlog_table(p, g):
    """The discrete logarithm λ_p to the generator g on F_p^×, as a list indexed by the residue (λ[g^m] = m)."""
    lam, x = [0] * p, 1
    for m in range(p - 1):
        lam[x] = m; x = x * g % p
    return lam

# F_{p^2} = F_p(η), η² = ν: elements (a, b) = a + bη; the conjugation φ, the half-turn ρ, the trace and the norm
def mul(z, w, nu, p):
    return ((z[0] * w[0] + nu * z[1] * w[1]) % p, (z[0] * w[1] + z[1] * w[0]) % p)
def frob(z, p):            # z ↦ z^p : a + bη ↦ a − bη
    return (z[0], (-z[1]) % p)
def half_turn(z, p):       # z ↦ 1 − z
    return ((1 - z[0]) % p, (-z[1]) % p)
def trace(z, p): return (2 * z[0]) % p
def norm(z, nu, p): return (z[0] * z[0] - nu * z[1] * z[1]) % p
def zpow(z, k, nu, p):
    r, b = (1, 0), z
    while k:
        if k & 1: r = mul(r, b, nu, p)
        b = mul(b, b, nu, p); k >>= 1
    return r

def affine_lines(p):
    """The p(p+1) affine lines of the plane F_p² = {(a, b)}: the p lines H_b = {im = b} and the p² lines S_{c,a} = {re = a + c·im},
    each as (name, frozenset of its p points)."""
    out = [(("H", b), frozenset((a, b) for a in range(p))) for b in range(p)]
    out += [(("S", c, a), frozenset(((a + c * b) % p, b) for b in range(p))) for c in range(p) for a in range(p)]
    return out

def dual(v, p):
    """The dual of a vector v on F_p^× (v[x] for x = 1..p−1): v̂(k) = Σ_x v(x) x^k for k = 0..p−2, in F_p."""
    return [sum(v[x] * pow(x, k, p) for x in range(1, p)) % p for k in range(p - 1)]

def random_vectors(p, count, seed):
    rng = random.Random(seed)
    return [[0] + [rng.randrange(p) for _ in range(p - 1)] for _ in range(count)]

# ----------------------------------------------------------------------------- the chart (numpy): the window's labels along the chart's scale
def mangoldt(N):
    """The prime-power labels n ≤ N with the chart's weight Λ(n) = log ℓ, as arrays (n, Λ(n))."""
    sieve = np.ones(N + 1, dtype=bool); sieve[:2] = False
    for i in range(2, int(N ** 0.5) + 1):
        if sieve[i]: sieve[i * i::i] = False
    ns, ls = [], []
    for q in np.nonzero(sieve)[0]:
        m = int(q)
        while m <= N:
            ns.append(m); ls.append(math.log(int(q))); m *= int(q)
    return np.array(ns, dtype=float), np.array(ls)

def energy(H, gammas):
    """The exhibit's modulus |Σ_{n≤H} Λ(n)(1 − log n/log H) n^{−1/2−iγ}|, the square root of the intensity, along the chart's height γ [chart]."""
    n, lam = mangoldt(H)
    w = lam * (1 - np.log(n) / np.log(H)) * n ** -0.5
    ln = np.log(n)
    out = np.empty(len(gammas))
    for i, g in enumerate(gammas):
        out[i] = abs(np.sum(w * np.exp(-1j * g * ln)))
    return out

def peaks(H, lo, hi, step=0.02):
    """The local maxima of the window's intensity on [lo, hi] at the grid step, as (γ, intensity), tallest first."""
    gam = np.arange(lo, hi + step / 2, step)
    e = energy(H, gam)
    pk = [(float(gam[i]), float(e[i])) for i in range(1, len(gam) - 1) if e[i] > e[i - 1] and e[i] > e[i + 1]]
    return sorted(pk, key=lambda t: -t[1])

def five_peaks(H):
    """The window's five peaks: the five tallest peaks on the range 10 to 36 of the chart's height, by height."""
    return sorted(g for g, _ in peaks(H, 10, 36)[:5])

def resolution(H): return 2 * math.pi / math.log(H)

# ----------------------------------------------------------------------------- the paper's figures
# Drawn at the text width of the manuscript (452.97 pt = 6.29 in; a4, 1 in margins, 11 pt), so that \includegraphics scales
# nothing and the 8–9 pt type prints as drawn; no titles (the captions carry them), panel letters above the axes.
PURPLE, GREY, BLUE, GREEN, RED, INK = "#8e44ad", "#8a8f98", "#2b6fd6", "#2f9e44", "#d33b3b", "#1b1f24"
TEXTWIDTH_IN = 452.97 / 72.27
PAPER_RC = {"font.size": 8.5, "axes.labelsize": 9, "axes.titlesize": 9, "xtick.labelsize": 8, "ytick.labelsize": 8,
            "legend.fontsize": 7.8, "legend.frameon": True, "legend.framealpha": 0.92, "legend.edgecolor": "0.8",
            "axes.linewidth": 0.7, "xtick.major.width": 0.6, "ytick.major.width": 0.6, "lines.linewidth": 1.1,
            "axes.grid": False, "pdf.fonttype": 42, "mathtext.fontset": "cm", "font.family": "DejaVu Sans"}

def panel_letter(ax, s, x=-0.02, y=1.03):
    """The panel letter above the axes' top-left corner, as the captions cite it."""
    ax.text(x, y, s, transform=ax.transAxes, ha="right", va="bottom", fontsize=9)

def _save(fig, name):
    fig.savefig(f"{FIGDIR}/paper/{name}.pdf", bbox_inches="tight", pad_inches=0.02)
    fig.savefig(f"{FIGDIR}/paper/{name}.png", dpi=220, bbox_inches="tight", pad_inches=0.02)
    plt.close(fig)
    print(f"    wrote {FIGDIR}/paper/{name}.pdf")

def figure_primespec():
    """fig_primespec: (a) the intensity of the windows 13, 39, 173 along the chart's scale; (b) depth 10⁶ (Obs. exhibit) [chart]."""
    gam = np.arange(10, 52, 0.02)
    with plt.rc_context(PAPER_RC):
        fig, axes = plt.subplots(2, 1, figsize=(TEXTWIDTH_IN, 4.2), gridspec_kw={"height_ratios": [1.2, 1]})
        ax = axes[0]
        for H, color, label in ((13, GREEN, r"$H=13$ (the window of $\mathbb{F}_{173}$)"), (39, BLUE, r"$H=39$ ($\mathbb{F}_{1549}$)"), (173, PURPLE, r"$H=173$ ($\mathbb{F}_{30089}$)")):
            e = energy(H, gam)
            ax.plot(gam, e / e.max(), color=color, lw=1.1, label=label)
        ax.axvspan(10, 36, color="#eef2f8", zorder=0)                          # the range of the Observation's claims
        for z in HEIGHTS:
            ax.axvline(z, color=GREY, lw=0.6, ls="--", alpha=0.7)
        ax.set_xlim(10, 52); ax.set_ylim(0, 1.32)
        ax.set_ylabel("modulus (normalised)")
        ax.legend(loc="upper left", ncol=3, columnspacing=1.0, handlelength=1.6)
        panel_letter(ax, "(a)")
        ax = axes[1]
        e = energy(10 ** 6, gam)
        ax.plot(gam, e / e.max(), color=PURPLE, lw=0.9)
        for i, z in enumerate(HEIGHTS):
            ax.axvline(z, color=GREY, lw=0.6, ls="--", alpha=0.7)
            ax.annotate(f"{z:.2f}", (z, 1.0), xytext=(0, 3 + 7 * (i % 2)), textcoords="offset points", ha="center", fontsize=6, color=GREY)
        ax.set_xlim(10, 52); ax.set_ylim(0, 1.3)
        ax.set_xlabel(r"$\gamma$ (the chart's height)"); ax.set_ylabel("modulus (normalised)")
        panel_letter(ax, "(b)")
        fig.tight_layout(h_pad=1.0)
        _save(fig, "fig_primespec")

def figure_plane():
    """fig_plane: the critical line is the energy domain, on F_13 (κ = 3, g = 2, η² = 2; Prop. line, Thm. drive). (a) The framed
    plane K as the 13×13 lattice a + bη with the real line and the critical line, the modes at their labels θ_k = −2^k, one
    conjugation pair, the first steps of the drive about the centre, a point off both lines with its two images; (b) the time
    domain as a cycle, the residues by scale, coloured by phase; (c) the critical line in the drive's order with the same
    residues in the same colours, θ_k = L_1(k + π)."""
    p, kap, g, nu = 13, 3, 2, 2
    n, pi_, half = p - 1, 6, 7
    theta = [(-pow(g, k, p)) % p for k in range(n)]              # the readout of the mode k: minus its eigenvalue
    scales = [pow(g, m, p) for m in range(n)]                    # the time domain in the drive's order: 1, 2, 4, 8, 3, 6, 12, ...
    assert all(theta[k] == scales[(k + pi_) % n] for k in range(n))
    with plt.rc_context(PAPER_RC):
        _draw_plane(p, g, nu, n, pi_, half, theta, scales)

def _draw_plane(p, g, nu, n, pi_, half, theta, scales):
    from matplotlib import cm
    col = lambda m: cm.twilight(((m % n) + 0.5) / n)            # one colour per phase m on the time domain
    dark = lambda m: 3 <= (m % n) <= 8
    fig = plt.figure(figsize=(TEXTWIDTH_IN, 4.0))                     # (a) square at 0.6 text width, (b) and (c) stacked at its right
    gs = fig.add_gridspec(2, 2, width_ratios=[1.55, 1], wspace=0.02, hspace=0.04, left=0.005, right=0.995, top=0.985, bottom=0.015)
    axa, axb, axc = fig.add_subplot(gs[:, 0]), fig.add_subplot(gs[0, 1]), fig.add_subplot(gs[1, 1])
    F = {"big": 8.5, "mid": 7.5, "small": 7, "tiny": 6.5}
    box = dict(boxstyle="round,pad=0.15", fc="white", ec="none", alpha=0.88)          # the annotations of (a) sit on the lattice
    # (a) the framed plane K = F_13(η): the lattice, the real line with the window, the critical line with the modes
    for a in range(p):
        for b in range(p): axa.plot(a, b, "o", ms=2.0, color="#cfd4dc", zorder=1)
    axa.plot([0, 0], [-0.3, p - 0.7], ls=(0, (2, 2)), color=GREY, lw=0.7, zorder=2)
    axa.plot([-0.3, p - 0.7], [0, 0], color=BLUE, lw=1.6, zorder=3)
    axa.plot([half, half], [-0.3, p - 0.7], color=PURPLE, lw=1.6, zorder=3)
    for a in range(p): axa.plot(a, 0, "o", ms=3.6, color=BLUE, zorder=4)
    axa.add_patch(plt.Rectangle((0.6, -0.42), 2.8, 0.84, color="#dbe7fb", zorder=0))
    for q in (2, 3): axa.plot(q, 0, "o", ms=6, mfc="none", mec=BLUE, mew=1.1, zorder=5)
    axa.text(2.0, -0.95, r"window $n\leq\sqrt{13}$: the primes 2, 3", color=BLUE, ha="center", fontsize=F["small"])
    for k in range(n):
        axa.plot(half, theta[k], "o", ms=4.8, color=PURPLE, zorder=5)
        axa.text(half + 0.3, theta[k] - 0.1, f"$k={k}$", color=PURPLE, fontsize=F["small"], va="center")
    axa.plot(half, 0, "o", ms=5.2, color=INK, zorder=6)
    axa.text(half + 0.3, -0.85, r"$2^{-1}=7$, the centre", color=INK, fontsize=F["small"])
    axa.text(half - 0.35, p - 0.45, r"$L_{1/2}=\{z: z+z^{13}=1\}$", color=PURPLE, ha="right", va="top", fontsize=F["small"], bbox=box, zorder=7)
    axa.text(p - 0.6, 0.45, r"$\mathbb{F}_{13}$, the real line", color=BLUE, ha="right", fontsize=F["small"])
    axa.text(-0.75, p - 0.6, r"$\eta\,\mathbb{F}_{13}$", color=GREY, fontsize=F["tiny"])
    axa.add_patch(FancyArrowPatch((half - 0.2, theta[0]), (half - 0.2, theta[pi_]), connectionstyle="arc3,rad=0.14", arrowstyle="<->", mutation_scale=7, color=PURPLE, lw=0.8, zorder=6))
    axa.text(3.0, 3.6, "the conjugation $z\\mapsto z^{13}$\nand the half-turn $z\\mapsto 1-z$:\n$k\\mapsto k+6$ on the line", color=PURPLE, fontsize=F["tiny"], ha="center", va="top", bbox=box, zorder=7)
    for k in range(3):
        axa.add_patch(FancyArrowPatch((half - 0.1, theta[k]), (half - 0.1, theta[k + 1]), connectionstyle="arc3,rad=0.22", arrowstyle="->", mutation_scale=6, color=PURPLE, lw=0.7, zorder=4))
    axa.text(half + 2.1, 12.3, "the drive about the centre,\n$\\theta\\mapsto 2\\theta$: $k\\mapsto k+1$", color=PURPLE, fontsize=F["tiny"], va="top", bbox=box, zorder=7)
    za = (1, 4); zc = (za[0], (-za[1]) % p); zh = ((1 - za[0]) % p, (-za[1]) % p)       # a point off both lines, its conjugate and its half-turn image
    assert zc == (1, 9) and zh == (0, 9)
    axa.plot(*za, "s", ms=4, color=GREY, zorder=5); axa.plot(*zc, "s", ms=4, mfc="none", mec=GREY, zorder=5); axa.plot(*zh, "s", ms=4, mfc="none", mec=GREY, zorder=5)
    axa.add_patch(FancyArrowPatch((za[0], za[1] + 0.3), (zc[0], zc[1] - 0.3), arrowstyle="->", mutation_scale=6, color=GREY, lw=0.7, zorder=4))
    axa.add_patch(FancyArrowPatch((za[0] - 0.15, za[1] + 0.25), (zh[0] + 0.1, zh[1] - 0.3), connectionstyle="arc3,rad=0.25", arrowstyle="->", mutation_scale=6, color=GREY, lw=0.7, zorder=4))
    axa.text(0.3, 11.6, "a point off both lines,\nwith its conjugate and its\nhalf-turn image: on no\nline kept by both", color=GREY, fontsize=F["tiny"], va="top", bbox=box, zorder=7)
    axa.set_xlim(-1.2, p + 0.2); axa.set_ylim(-1.4, p - 0.2); axa.set_aspect("equal"); axa.axis("off")
    panel_letter(axa, "(a)", x=0.01, y=0.99)
    # (b) the time domain as a cycle: the residues by scale, each with the colour of its phase m
    ang = lambda m: np.pi / 2 - 2 * np.pi * m / n
    axb.add_patch(plt.Circle((0, 0), 1, fill=False, color=GREEN, lw=1.3, zorder=2))
    for m, x in enumerate(scales):
        axb.plot(np.cos(ang(m)), np.sin(ang(m)), "o", ms=11, color=col(m), mec=INK, mew=0.5, zorder=5)
        axb.text(np.cos(ang(m)), np.sin(ang(m)), str(x), ha="center", va="center", fontsize=F["small"], color="white" if dark(m) else INK, zorder=6)
        axb.text(1.4 * np.cos(ang(m)), 1.4 * np.sin(ang(m)), f"$m={m}$", ha="center", va="center", fontsize=F["tiny"], color=GREY)
    axb.plot(0, 0, "o", ms=3.5, color=INK, zorder=5); axb.text(0.1, 0.04, "0", fontsize=F["small"])
    axb.annotate("", xy=(np.cos(ang(1)), np.sin(ang(1))), xytext=(np.cos(ang(0.4)), np.sin(ang(0.4))), arrowprops=dict(arrowstyle="->", color=GREEN, lw=1.2))
    axb.text(0, 1.62, "the time domain $L_1=\\{2^m\\}$", color=GREEN, fontsize=F["tiny"], ha="center")
    axb.set_xlim(-1.85, 1.85); axb.set_ylim(-1.7, 1.85); axb.set_aspect("equal"); axb.axis("off")
    panel_letter(axb, "(b)", x=0.02, y=1.0)
    # (c) the critical line in the drive's order: the same residues as labels, in the same colours, θ_k = L_1(k + π)
    axc.add_patch(plt.Circle((0, 0), 1, fill=False, color=PURPLE, lw=1.3, zorder=2))
    for k in range(n):
        m = (k + pi_) % n
        axc.plot(np.cos(ang(k)), np.sin(ang(k)), "o", ms=11, color=col(m), mec=INK, mew=0.5, zorder=5)
        axc.text(np.cos(ang(k)), np.sin(ang(k)), str(theta[k]), ha="center", va="center", fontsize=F["small"], color="white" if dark(m) else INK, zorder=6)
        axc.text(1.4 * np.cos(ang(k)), 1.4 * np.sin(ang(k)), f"$k={k}$", ha="center", va="center", fontsize=F["tiny"], color=PURPLE)
    axc.plot(0, 0, "o", ms=3.5, color=INK, zorder=5); axc.text(0.1, 0.04, "$2^{-1}$", fontsize=F["small"])
    axc.annotate("", xy=(np.cos(ang(1)), np.sin(ang(1))), xytext=(np.cos(ang(0.4)), np.sin(ang(0.4))), arrowprops=dict(arrowstyle="->", color=PURPLE, lw=1.2))
    axc.text(0, 1.62, "the labels $\\theta_k=-2^k=L_1(k+6)$", color=PURPLE, fontsize=F["tiny"], ha="center")
    axc.set_xlim(-1.85, 1.85); axc.set_ylim(-1.7, 1.85); axc.set_aspect("equal"); axc.axis("off")
    panel_letter(axc, "(c)", x=0.02, y=1.0)
    _save(fig, "fig_plane")

# ======================================================================================================================
# block A — the shell, in exact arithmetic
# The shells p = 13, 17, 29, 37, 41 in full; 173 for the checks that do not enumerate the plane; the laboratory pairs
# (13, 233), (173, 30089), (1549, 2408561) for frame coincidence, the closure and completeness. The generator g is the least
# primitive root, η² = ν the least nonresidue, as in the paper.
def block_A():
    """Block A — the shell, in exact arithmetic: 96 checks, 91 EXACT and 5 [approx] readings of the chart's characters (A7b, one per shell)."""
    print("\n== block A: the shell ==")
    for p in SHELLS + [BIG]:
        g, nu = generator(p), nonresidue(p)
        kappa = (p - 1) // 4; assert 4 * kappa + 1 == p
        # A1 zero-slot
        ok = all(sum(pow(x, k, p) for x in range(1, p)) % p == 0 for k in range(1, p - 1)) \
             and sum(pow(x, p - 1, p) for x in range(1, p)) % p == p - 1
        # 20:B4 (p20011)
        check("A1", f"zero-slot on F_{p}", ok, f"Σx^k=0 for k=1..{p-2}; = -1 at k={p-1}")
        # A6 the Subject constants, capacity-first
        pi_ = 2 * kappa
        i_ = pow(g, p - 1 - kappa, p)                       # g^{-κ}
        assert i_ == (-pow(g, kappa, p)) % p
        i_odd = i_ if i_ % 2 == 1 else i_ + p               # the odd integer lift of i (Remark frame)
        e_ = pow(g, i_odd, p)
        ok = ((2 * pi_) % p == p - 1 and (i_ * i_) % p == p - 1 and pow(g, pi_, p) == p - 1
              and pow(e_, i_odd * pi_, p) == p - 1 and (2 * (2 * kappa + 1)) % p == 1
              and (2 * kappa + 1) % p == (-pi_) % p)
        # 20:B10 (p20017)
        check("A6", f"Subject constants on F_{p}: π=2κ, i=g^-κ, e=g^i (odd lift)", ok,
              f"g={g} κ={kappa} π={pi_} i={i_} e={e_}: 2π≡-1, i²≡-1, g^π≡-1, e^(iπ)≡-1, 2⁻¹=2κ+1=-π")
        # A4 the finite critical line
        inv2 = (2 * kappa + 1) % p
        line = [(inv2, b) for b in range(p)]
        quarter = pow(4, p - 2, p)
        ok = all(trace(z, p) == 1 for z in line) and len(set(line)) == p \
             and all(norm(z, nu, p) == (quarter - nu * z[1] * z[1]) % p for z in line)
        if p != BIG:   # the converse on the full plane: Tr z = 1 only on the line
            ok = ok and all(((2 * a) % p == 1) == (a == inv2) for a in range(p))
        # 20:B8 (p20015)
        check("A4", f"finite critical line on F_{p}: Tr z = 1 ⟺ z = 2⁻¹ + bη, |L| = p, N = ¼ − νb²", ok,
              f"ν={nu}, 2⁻¹={inv2}")
        # A7 the shell theorem (Thm. hp) on F_p, every clause in F_p: (i) the dual inverts, the constant mode the mean term;
        # (iii) D x^k = g^k x^k on the power characters (the drive D : x ↦ g x), Tr D^r = (p−1)[(p−1)|r]; (iv) W² = −J, F² = J, F⁴ = 1 for W_mk = g^mk,
        # F = iW; (v) the explicit formula along the meridian, Σ_{y≤x} v(y) = −Σ_k v̂(k) S_k(x), S_0(x) = x; three random vectors
        vecs = random_vectors(p, 3, seed=20 * p)
        ok_i = ok_v = True
        for v in vecs:
            vh = dual(v, p)
            ok_i &= all((-sum(vh[k] * pow(y, (p - 1 - k) % (p - 1), p) for k in range(p - 1))) % p == v[y] for y in range(1, p)) \
                    and vh[0] == sum(v) % p
            S = lambda k, x: sum(pow(y, (p - 1 - k) % (p - 1), p) for y in range(1, x + 1)) % p
            ok_v &= all((-sum(vh[k] * S(k, x) for k in range(p - 1))) % p == sum(v[1:x + 1]) % p for x in range(1, p)) \
                    and all(S(0, x) == x % p for x in range(1, p))
        ok_fp = all(pow((g * x) % p, k, p) == (pow(g, k, p) * pow(x, k, p)) % p for k in range(p - 1) for x in range(1, p))
        tr = [sum(1 for x in range(1, p) if (pow(g, r, p) * x) % p == x) for r in range(1, p)]
        ok_tr = all(tr[r - 1] == ((p - 1) if r % (p - 1) == 0 else 0) for r in range(1, p))
        n_ = p - 1
        W = np.array([[pow(g, (m * k) % n_, p) for k in range(n_)] for m in range(n_)], dtype=np.int64)
        J = np.array([[1 if (m + l) % n_ == 0 else 0 for l in range(n_)] for m in range(n_)], dtype=np.int64)
        W2 = (W @ W) % p
        F2 = (i_ * i_ * W2) % p                              # F = iW: F² = i² W²
        ok_iv = np.array_equal(W2, (-J) % p) and np.array_equal(F2, J) and np.array_equal((F2 @ F2) % p, np.eye(n_, dtype=np.int64))
        # 20:E12 (p20043), 20:E14 (p20092)
        check("A7", f"the shell theorem on F_{p}: (i) the dual inverts, v(y) = −Σ v̂(k) y^−k, v̂(0) the mean term; (iii) D x^k = g^k x^k, Tr D^r = (p−1)[(p−1)|r]; (iv) W² = −J, F² = J, F⁴ = 1; (v) the explicit formula along the meridian, S_0(x) = x",
              ok_i and ok_fp and ok_tr and ok_iv and ok_v, f"three random vectors; W of order {n_}")
        # A14 the Parseval identity (Thm. hp (ii)): Σ_k v̂(k) v̂(−k) = −Σ_x v(x)² in F_p, on random vectors and on the prime-power
        # indicator of the whole shell (the window's prime vector of Def. vector is its restriction below √p; the identity holds for every vector)
        prime_vec = [0] + [1 if is_prime(x) or (len(prime_factors(x)) == 1 and x > 1) else 0 for x in range(1, p)]
        ok = True
        for v in vecs + [prime_vec]:
            vh = dual(v, p)
            ok &= sum(vh[k] * vh[(-k) % (p - 1)] for k in range(p - 1)) % p == (-sum(x * x for x in v)) % p
        # 20:E13 (p20044)
        check("A14", f"the Parseval identity on F_{p}: Σ_k v̂(k) v̂(−k) = −Σ_x v(x)² for three random vectors and the prime-power indicator of the shell", ok,
              f"prime-power indicator: {sum(prime_vec)} labels")
        if p == BIG:
            continue
        # A2 slot complementarity
        image = {(-pow(g, k, p)) % p for k in range(1, p - 1)}
        # 20:B5 (p20012)
        check("A2", f"Φ(k) = −g^k bijects the nonterminal slots onto F_{p}^× \\ {{−1}}", image == set(range(1, p - 1)),
              f"|image| = {len(image)} = p−2")
        # A3 Hermitian phase calculus
        K = [(a, b) for a in range(p) for b in range(p)]
        U = [z for z in K if norm(z, nu, p) == 1]
        inv_ok = all(frob(z, p) == zpow(z, p, nu, p) and mul(z, frob(z, p), nu, p) == (1, 0) for z in U)
        i2 = [(a, 0) for a in range(p) if (a * a) % p == p - 1]
        ok = len(U) == p + 1 and inv_ok and len(i2) == 2 and all(frob(z, p) == z and norm(z, nu, p) == p - 1 for z in i2)
        # 20:B6 (p20013)
        check("A3", f"F_{p}²: |U_(p+1)| = p+1, Frobenius = inversion on it, i Frobenius-fixed with N(i) = −1", ok)
        # A5 the two agreement loci (Thm. agree): among the p(p+1) affine lines of K exactly two are invariant as sets under both
        # the conjugation φ and the half-turn ρ — the prime meridian F_p and the critical line; φ keeps p+1 lines, ρ keeps the
        # p+1 lines through 2⁻¹; and the corollary, the Klein four-group with its fixed loci
        phi = lambda z: frob(z, p)
        rho = lambda z: half_turn(z, p)
        sig = lambda z: rho(phi(z))
        lines = affine_lines(p)
        kept_phi = [name for name, L in lines if all(phi(z) in L for z in L)]
        kept_rho = [name for name, L in lines if all(rho(z) in L for z in L)]
        both = [name for name, L in lines if all(phi(z) in L and rho(z) in L for z in L)]
        ok_lines = (len(lines) == p * (p + 1) and len(kept_phi) == p + 1 and len(kept_rho) == p + 1
                    and sorted(both) == sorted([("H", 0), ("S", 0, inv2)])
                    and all(("S", c, inv2) in kept_rho for c in range(p)) and ("H", 0) in kept_rho
                    and all(("H", b) not in kept_rho for b in range(1, p)))
        fix_phi = {z for z in K if phi(z) == z}; fix_rho = {z for z in K if rho(z) == z}; fix_sig = {z for z in K if sig(z) == z}
        ok_klein = (all(phi(phi(z)) == z and rho(rho(z)) == z and phi(rho(z)) == rho(phi(z)) for z in K)
                    and fix_phi == {(a, 0) for a in range(p)} and fix_sig == set(line) and fix_rho == {(inv2, 0)}
                    and fix_phi & fix_sig == {(inv2, 0)})
        # 20:B9 (p20016)
        check("A5", f"the two agreement loci on F_{p}²: of the {p * (p + 1)} affine lines, φ keeps {p + 1}, ρ keeps {p + 1}, both keep exactly F_p and L_1/2; Klein four-group: Fix φ = F_p, Fix σ = L_1/2, Fix ρ = {{2⁻¹}}",
              ok_lines and ok_klein, f"both: {both}")
        # A7b the chart's reading of the Parseval identity (Rem. parseval) [approx]: the complex characters χ_j(n) = ω^{jλ(n)} on
        # ℓ²(F_p^×) are orthogonal with ‖χ_j‖² = p−1, the dual inverts, and Σ_j |v̂_C(j)|² = (p−1) Σ |v|²; D χ_j = ω^j χ_j, the
        # drive's chart a unitary permutation matrix whose eigenvalues are the (p−1)-th roots of unity (Rem. chart-operator)
        lam = {}
        for n in range(1, p):
            base = prime_factors(n)
            lam[n] = math.log(min(base)) if len(base) == 1 else 0.0
        v = np.array([lam[n] for n in range(1, p)])
        dlog = dlog_table(p, g)
        w = cmath.exp(2j * math.pi / (p - 1))
        chi = np.array([[w ** (j * dlog[n]) for n in range(1, p)] for j in range(p - 1)])
        gram = chi.conj() @ chi.T
        vc = chi @ v
        ok_orth = np.allclose(gram, (p - 1) * np.eye(p - 1), atol=1e-9)
        ok_par = abs(np.sum(np.abs(vc) ** 2) - (p - 1) * np.sum(v ** 2)) < 1e-9
        ok_inv = np.allclose((chi.conj().T @ vc).real / (p - 1), v, atol=1e-10)
        shifted = lambda j: np.array([w ** (j * dlog[(g * n) % p]) for n in range(1, p)])   # (S χ_j)(n) = χ_j(g n)
        ok_c = all(np.allclose(shifted(j), w ** j * chi[j]) for j in range(p - 1))
        Dm = np.zeros((p - 1, p - 1)); dl = dlog_table(p, g)
        for n in range(1, p): Dm[n - 1, (g * n) % p - 1] = 1.0                       # (Dv)(n) = v(gn): a permutation matrix
        ok_u = np.allclose(Dm @ Dm.T, np.eye(p - 1)) and np.allclose(sorted(np.angle(np.linalg.eigvals(Dm)) % (2 * np.pi)), sorted(2 * np.pi * np.arange(p - 1) / (p - 1)), atol=1e-9)
        check("A7b", f"the chart's characters on ℓ²(F_{p}^×): χ_j orthogonal with ‖χ_j‖² = p−1, Σ_j|v̂(j)|² = (p−1)Σ|v|² for v = Λ, the dual inverts; Dχ_j = ω^j χ_j, the drive a unitary permutation with the (p−1)-th roots of unity as its eigenvalues",
              ok_orth and ok_par and ok_inv and ok_c and ok_u, f"Σ|v̂|²/(p−1) = {np.sum(np.abs(vc) ** 2) / (p - 1):.6f}", kind="[approx]")
        # A10 the shared quarter-turn core; no cycle projection onto (13, 233)
        Om = 233
        q4 = {pow(i_, a, p) for a in range(4)}
        ok = q4 == {1, i_, p - 1, (-i_) % p} and (p - 1) % 4 == 0 and (Om - 1) % 4 == 0
        if p == 13:
            ok = ok and (Om - 1) % (p - 1) != 0
            # 20:B1 (p20008)
            check("A10", "Q₄ ⊂ both cycles; C_232 ↠ C_12 does not exist (12 ∤ 232) on the pair (13, 233)", ok, "the shells share the core, not a clock")
        else:
            check("A10", f"Q₄ = {{1, i, −1, −i}} ⊂ F_{p}^×, 4 | p−1", ok)
    # A11 frame coincidence below the horizon (Prop. coincide): the Carrier chart Ω is the least prime ≡ 1 (mod 4) above p²
    for p in SHELLS + [1009, 10009]:
        Om = next_prime(p * p)
        while Om % 4 != 1:
            Om = next_prime(Om)
        H = math.isqrt(p)
        same = all(n % p == n % Om == n for n in range(1, H + 1))
        prods = all((a * b) % p == (a * b) % Om == a * b for a in range(1, H + 1) for b in range(1, H + 1))
        irreducible = {n for n in range(2, H + 1) if all(n % d for d in range(2, math.isqrt(n) + 1))}   # trial division inside the window
        primes = {n for n in range(2, H + 1) if is_prime(n)}
        # 20:B2 (p20009)
        check("A11", f"frame coincidence below √{p} = {H} on the pair ({p}, {Om}): residues, window products and primality agree", same and prods and irreducible == primes,
              f"Π_p = {sorted(primes)}")
    # A6b the odd-lift rule (Remark frame) on every admissible frame below 3000, least primitive root
    frames = [q for q in range(5, 3000) if q % 4 == 1 and is_prime(q)]
    bad = []
    for q in frames:
        gq = generator(q); kq = (q - 1) // 4; piq = 2 * kq
        r = pow(gq, q - 1 - kq, q)                          # the least residue of i = g^{-κ}
        odd, even = (r, r + q) if r % 2 == 1 else (r + q, r)
        e_odd = pow(gq, odd, q)
        if not (pow(e_odd, odd * piq, q) == q - 1 and pow(e_odd, even * piq, q) == 1 and (r * r) % q == q - 1):
            bad.append(q)
    f17 = (pow(3, 16 - 4, 17), pow(3, 21, 17))               # F_17 with g = 3: i = 3^{-4} = 4 (even), lift 21, e = 3^21 = 5
    ok = not bad and f17 == (4, 5)
    check("A6b", f"the odd-lift rule on all {len(frames)} frames p ≡ 1 (mod 4) below 3000: e^{{iπ}} ≡ −1 on the odd lift, ≡ +1 on the even member; F_17: g=3, i=4, lift 21, e=5", ok,
          f"frames {len(frames)}, failures {bad}; F_17 (i, e) = {f17}")

    # A15 the critical line is the energy domain (Prop. line; row B12): z_k = 2⁻¹ − ηg^k. (i) k ↦ z_k bijects Z_{p−1} onto the
    # line without its centre, z_k the readout of the mode k at θ = −g^k, k = 0 at θ = −1 and k = π at θ = 1; (ii) the dilation
    # about the centre, z ↦ 2⁻¹ + g(z − 2⁻¹), carries z_k to z_{k+1}; (iii) the half-turn and the conjugation both carry z_k to
    # z_{k+π} and fix the centre alone; (iv) N(z_k) = ¼ − νg^{2k}, even under k ↦ k + π; (v) the labels along the drive are the
    # latitude L_a = {a g^m} shifted by π − log_g a for every base point a, by 0 for a = −1: θ_k = −g^k = L_{−1}(k)
    for p in SHELLS + [53, BIG]:
        g, nu = generator(p), nonresidue(p)
        kappa = (p - 1) // 4; pi_ = 2 * kappa; inv2 = (2 * kappa + 1) % p; n_ = p - 1
        quarter = pow(4, p - 2, p)
        zk = [(inv2, (-pow(g, k, p)) % p) for k in range(n_)]
        centre = (inv2, 0)
        ok_i = len(set(zk)) == n_ and set(zk) == {(inv2, b) for b in range(1, p)} and all(trace(z, p) == 1 for z in zk) \
               and zk[0] == (inv2, p - 1) and zk[pi_] == (inv2, 1)
        dil = lambda z: (inv2, (g * z[1]) % p)                                   # 2⁻¹ + g(z − 2⁻¹) on the line
        ok_ii = all(dil(zk[k]) == zk[(k + 1) % n_] for k in range(n_)) and dil(centre) == centre
        ok_iii = all(half_turn(zk[k], p) == zk[(k + pi_) % n_] == frob(zk[k], p) for k in range(n_)) \
                 and all(zk[(k + pi_) % n_] != zk[k] for k in range(n_)) and half_turn(centre, p) == centre == frob(centre, p)
        ok_iv = all(norm(zk[k], nu, p) == (quarter - nu * pow(g, 2 * k, p)) % p == norm(zk[(k + pi_) % n_], nu, p) for k in range(n_))
        # 20:B12 (p20085)
        lam = dlog_table(p, g)
        ok_v = all(zk[k][1] == (a * pow(g, (k + pi_ - lam[a]) % n_, p)) % p for a in range(1, p) for k in range(n_)) \
               and all(zk[k][1] == ((p - 1) * pow(g, k, p)) % p for k in range(n_))      # (v): θ_k = L_a(k + π − log_g a); the shift 0 at a = −1
        check("A15", f"the critical line is the energy domain on F_{p}: k ↦ z_k = 2⁻¹ − ηg^k bijects Z_{n_} onto L_1/2 \\ {{2⁻¹}}; the drive z_k ↦ z_{{k+1}}; half-turn and conjugation z_k ↦ z_{{k+π}}, the centre their only fixed point; N(z_k) even under k ↦ k+π; the labels along the drive are the latitude L_a shifted by π − log_g a, for every base point a, by 0 for a = −1",
              ok_i and ok_ii and ok_iii and ok_iv and ok_v, f"g={g}, ν={nu}, π={pi_}: z_0 = 2⁻¹+η, z_π = 2⁻¹−η")

    # A16 frame coincidence on the critical line (Prop. coincideline; row B13), on the laboratory pairs: for every nonzero label
    # θ < p of the Subject, θ is the same integer in F_p and F_Ω (the Subject's residues are the Carrier's below p; B1); 2⁻¹ + ηθ
    # has trace 1 in both frames with real part 2κ+1 and 2κ'+1 (the line's centre is the half-turn of each frame); the line
    # {Tr = 1} is carried to itself by the half-turn and by the conjugation in both frames (B9, D11); the point is a mode in
    # both — θ = −g^k in F_p and θ = −g'^{k'} in F_Ω — nontrivial in both for 1 ≤ θ ≤ p−2 (B12; the Subject's constant mode
    # sits at θ = p−1 ≡ −1, where the Carrier has a zero), and the mode's slot is a zero-slot (B4), checked at the first prime
    # labels; the Carrier's labels from p on are no residue of the Subject; the primes need the horizon and the zeros do not:
    # at the first label above the horizon the products of the two frames disagree
    for p, Om in PAIRS:
        gp, gO = generator(p), generator(Om)
        kp, kO = (p - 1) // 4, (Om - 1) // 4
        H = math.isqrt(p)
        same = all(t % p == t % Om == t for t in range(p))
        tr = all(trace((2 * kp + 1, t), p) == 1 and trace((2 * kO + 1, t), Om) == 1 for t in range(p))
        line_p = [((2 * kp + 1) % p, b) for b in range(p)]
        inv_p = all(half_turn(z, p) in set(line_p) and frob(z, p) in set(line_p) for z in line_p)
        line_O = set(((2 * kO + 1) % Om, b) for b in range(Om))
        inv_O = all(half_turn(z, Om) in line_O and frob(z, Om) in line_O for z in line_O)
        lam_p, lam_O = dlog_table(p, gp), dlog_table(Om, gO)
        modes = {t: (lam_p[(-t) % p], lam_O[(-t) % Om]) for t in range(1, p)}
        mode_ok = all(pow(gp, modes[t][0], p) == (-t) % p and pow(gO, modes[t][1], Om) == (-t) % Om for t in modes)
        mode_ok &= all(1 <= modes[t][0] <= p - 2 and 1 <= modes[t][1] <= Om - 2 for t in range(1, p - 1))
        mode_ok &= modes[p - 1][0] == 0 and 1 <= modes[p - 1][1] <= Om - 2                      # the constant mode's point: a Carrier zero
        mode_ok &= len({modes[t][0] for t in modes}) == p - 1 and len({modes[t][1] for t in modes}) == p - 1
        firsts = [t for t in range(2, H + 1) if is_prime(t)][:2]
        slot_ok = all(sum(pow(x, modes[t][0], p) for x in range(1, p)) % p == 0 for t in firsts)
        slot_ok &= sum(pow(x, modes[firsts[0]][1], Om) for x in range(1, Om)) % Om == 0
        beyond = all(t % p != t for t in range(p, min(Om, p + 50))) and Om - 1 >= p
        above = ((H + 1) * (H + 1)) % p != (H + 1) * (H + 1) and ((H + 1) * (H + 1)) % Om == (H + 1) * (H + 1)
        eig = all(pow(gp, modes[t][0], p) == (-t) % p and pow(gO, modes[t][1], Om) == (-t) % Om for t in range(1, p - 1))   # the eigenvalue −θ in both frames (Thm. drive (vi))
        N_ = Om - 1; (k1, kp1), (k2, kp2) = modes[1], modes[2]
        affine = [(a, (kp1 - a * k1) % N_) for a in range(N_) if (a * k2 + kp1 - a * k1) % N_ == kp2]   # the maps fitting the labels 1 and 2
        affine = [(a, b) for a, b in affine if all((a * modes[t][0] + b) % N_ == modes[t][1] for t in range(1, p - 1))]   # no affine k ↦ k' fits every label
        # 20:B13 (p20086)
        check("A16", f"frame coincidence on the line, pair ({p}, {Om}): every label θ < {p} the same integer in both; Tr(2⁻¹+ηθ) = 1 in both, centres {2 * kp + 1} and {2 * kO + 1}; the line kept by half-turn and conjugation in both; every 1 ≤ θ ≤ {p - 2} a nontrivial mode in both, the slot a zero-slot, θ = {p - 1} the Subject's constant mode and a Carrier zero; the labels from {p} on no Subject residue; at {H + 1} the products disagree; at every label the eigenvalue −θ under each frame's own drive, the indices k, k' each frame's own",
              same and tr and inv_p and inv_O and mode_ok and slot_ok and beyond and above and eig and affine == [],
              "modes (k, k'): " + ", ".join(f"θ={t}: {modes[t]}" for t in firsts) + f"; θ={p - 1}: {modes[p - 1]}; affine maps k ↦ k' fitting the labels: {len(affine)}")

    # A12 the closure of the zeros (Thm. closure; rows A2, A4, F7), on the four laboratory Carriers Ω = 13, 233, 30089,
    # 2408561: the largest embedded Subject p* with p*² < Ω < p'² (p' the next prime); the residues of a cycle are its labels
    # 0..q−1 and a Subject of cardinality p reads the residues y < p, its own residues, so an embedded Subject's cycle is shorter
    # than the Carrier's and the Carrier's top residue is read from labels up to √Ω, beyond every embedded window √p*; the
    # wrap of the height reading, (T + Ω) ≡ T; the pigeonhole of 00:A2/00:A4 on the residues — a reading of the Ω residues into
    # o < Ω records identifies two residues (found by search for o = p* and o = Ω − 1), and an injective reading needs o ≥ Ω
    def largest_subject(Om):
        """The largest admissible Subject of Ω: the largest prime p = 4κ+1 with κ > 1 and p² < Ω (Remark holographic), or None."""
        q = math.isqrt(Om - 1)
        while q >= 13 and not (is_prime(q) and q % 4 == 1): q -= 1
        return q if q >= 13 else None
    assert largest_subject(13) is None and largest_subject(401) == 17 and is_prime(19) and 19 * 19 < 401   # the empty case; the control
    for Om in (233, 30089, 2408561):
        ps = largest_subject(Om)
        ok = is_prime(Om) and Om % 4 == 1 and is_prime(ps) and ps % 4 == 1 and ps > 5 and ps * ps < Om
        ok &= all(not (is_prime(q) and q % 4 == 1) for q in range(ps + 1, math.isqrt(Om - 1) + 1))   # no admissible Subject between p* and √Ω
        ok &= ps < Om and math.isqrt(ps) < math.isqrt(Om)                   # the embedded cycle shorter; the top window's labels beyond √p*
        ok &= all((T + Om) % Om == T % Om for T in (0, 1, ps, Om - 1, Om, 7 * Om + 3))   # the wrap of the height reading
        collisions = {}
        for o in (ps, Om - 1):
            seen = {}
            for y in range(Om):                                             # the residues of the Carrier's cycle, read into o records
                r = y % o
                if r in seen:
                    collisions[o] = (seen[r], y); break
                seen[r] = y
            ok &= o in collisions and collisions[o][0] != collisions[o][1] and collisions[o][0] % o == collisions[o][1] % o
        ok &= len({y for y in range(Om)}) == Om                             # the identity reading into Ω records is injective: Ω ≤ Ω
        # 20:A2 (p00004), 20:A4 (p00197), 20:F7 (p20079)
        check("A12", f"closure of the zeros on Ω = {Om}: the largest admissible Subject p* = {ps} ({ps}² < Ω, none between p* and √Ω = {math.isqrt(Om)}), the cycle's {Om} residues, an embedded Subject reads {ps} of them; readings into {ps} and {Om - 1} records collide", ok,
              f"collisions {collisions}; √Ω = {math.isqrt(Om)}, √p* = {math.isqrt(ps)}")

    # A13 Completeness (row A3; 00:A3), on the laboratory pairs (p, Ω): the registration of a totality is onto its registered
    # Universe — the registered Universe is the set of residues at which some member registers, read back as a member for every
    # residue of it (the Carrier's residues registered whole, ρ(y) = y, and the Subject's reading of them, ρ_p(y) = y mod p: Ω and p
    # residues, each with a member); and two totalities each registered whole within the other have one count — the identity
    # registers the Subject's cycle within the Carrier's, every reading of the Carrier's Ω residues into the Subject's p records
    # identifies two residues (y mod p, an affine reading, the square; the pigeonhole of 00:A2 both ways is
    # FRC.Foundation.mutual_registration_count), and only cycles of one count embed both ways
    for p, Om in PAIRS:
        members = {}
        for y in range(Om):                                                 # the Carrier's cycle registered whole
            members.setdefault(y % Om, y)
        ok = len(members) == Om and all(members[r] % Om == r for r in members)          # onto: every residue has a member
        membersp = {}
        for y in range(Om):                                                 # the Subject's reading of the Carrier's residues
            membersp.setdefault(y % p, y)
        ok &= len(membersp) == p and all(membersp[r] % p == r for r in membersp)
        ok &= len({x % Om for x in range(p)}) == p                          # the identity registers Shell p within Shell Ω
        readings = {"y mod p": lambda y: y % p, "3y+5 mod p": lambda y: (3 * y + 5) % p, "y² mod p": lambda y: (y * y) % p}
        collisions = {}
        for name, f in readings.items():                                    # no reading of Shell Ω within Shell p is injective
            seen = {}
            for y in range(Om):
                r = f(y)
                if r in seen:
                    collisions[name] = (seen[r], y); break
                seen[r] = y
            ok &= name in collisions and collisions[name][0] != collisions[name][1] and f(collisions[name][0]) == f(collisions[name][1])
        ok &= p < Om and len({x % p for x in range(p)}) == p                 # one count: the identity both ways on Shell p
        # 20:A3 (p00003)
        check("A13", f"completeness on the pair ({p}, {Om}): the registration of the cycle is onto its registered Universe ({Om} residues; {p} under the Subject's reading); F_{p} registers within F_{Om}, every reading of the {Om} residues into {p} records collides, one count only both ways", ok,
              "collisions " + ", ".join(f"{k}: {v}" for k, v in collisions.items()))

    # A17 the open target's data (row O9; Section order): the cycle's scale coordinate is the discrete logarithm up to the choice
    # of generator, and no generator of F_173, F_1549 or F_30089 orders the primes of the window (λ(2) < λ(3) < λ(5) < …); the
    # longest ordered run of the window's primes is 5 of 6, 6 of 12 and 7 of 40. F_13, whose window holds the primes 2 and 3, is
    # ordered by two of its four generators. Every generator is g₀^e with e a unit of Z_{p−1}, and λ_g = e·λ_{g₀}
    stated = {13: (4, 2, 2, 2), 173: (84, 0, 5, 6), 1549: (504, 0, 6, 12), 30089: (15040, 0, 7, 40)}
    for p in stated:
        n_ = p - 1; H = math.isqrt(p); P = [n for n in range(2, H + 1) if is_prime(n)]
        lam0 = dlog_table(p, generator(p))
        units = [e for e in range(1, n_) if math.gcd(e, n_) == 1]
        ordering, best = 0, 0
        for e in units:
            seq = [(e * lam0[n]) % n_ for n in P]
            ordering += all(a < b for a, b in zip(seq, seq[1:]))
            k = 0
            while k + 1 < len(seq) and seq[k] < seq[k + 1]: k += 1
            best = max(best, k + 1)
        got = (len(units), ordering, best, len(P))
        # 20:O9 (p20090)
        check("A17", f"F_{p}: of its {len(units)} generators, {stated[p][1]} order the {len(P)} primes of the window 2..{H} by the discrete logarithm; the longest ordered run of primes is {stated[p][2]} of {len(P)}",
              got == stated[p], f"(generators, ordering, longest run, primes) = {got}")

    # A18 no zero off the line (Thm. noline; row F10), on the pairs (13, 233) and (173, 30089): (i) the lines kept by both the
    # conjugation and the half-turn are exactly the meridian and the critical line — every one of the p(p+1) affine lines of the
    # Subject's plane tested, and of the Carrier's on 233; on 30089 the two lines tested and 2000 other lines sampled (the
    # exhaustive statement is the Lean theorem invariant_lines, for every shell); (ii) every label 1 ≤ θ ≤ p−2 of the Subject is
    # a nontrivial mode on the critical line in both frames, the Subject's p−2 zeros (A16); (iii) a point off both lines lies on no line kept by both — every line
    # through it fails — for every such point of the Subject's plane on 13 and for 200 sampled points on 173
    rng = random.Random(2026)
    for p, Om in PAIRS[:2]:
        gp, gO = generator(p), generator(Om)
        kp, kO = (p - 1) // 4, (Om - 1) // 4
        inv2p, inv2O = (2 * kp + 1) % p, (2 * kO + 1) % Om
        both_p = [name for name, L in affine_lines(p) if all(frob(z, p) in L and half_turn(z, p) in L for z in L)]
        ok_i = sorted(both_p) == sorted([("H", 0), ("S", 0, inv2p)])
        kept = lambda name, q: (lambda L: all(frob(z, q) in L and half_turn(z, q) in L for z in L))(
            frozenset((a, name[1]) for a in range(q)) if name[0] == "H" else frozenset(((name[2] + name[1] * b) % q, b) for b in range(q)))
        if Om < 1000:
            both_O = [name for name, L in affine_lines(Om) if all(frob(z, Om) in L and half_turn(z, Om) in L for z in L)]
            ok_i &= sorted(both_O) == sorted([("H", 0), ("S", 0, inv2O)]); carrier = f"every line of F_{Om}²"
        else:
            others = set()
            while len(others) < 2000:
                nm = ("H", rng.randrange(1, Om)) if rng.random() < 0.1 else ("S", rng.randrange(Om), rng.randrange(Om))
                if nm not in (("H", 0), ("S", 0, inv2O)): others.add(nm)
            ok_i &= kept(("H", 0), Om) and kept(("S", 0, inv2O), Om) and not any(kept(nm, Om) for nm in others); carrier = f"the two lines kept and 2000 sampled others not, on F_{Om}²"
        lam_p, lam_O = dlog_table(p, gp), dlog_table(Om, gO)
        ok_ii = all(pow(gp, lam_p[(-t) % p], p) == (-t) % p and pow(gO, lam_O[(-t) % Om], Om) == (-t) % Om
                    and 1 <= lam_p[(-t) % p] <= p - 2 and 1 <= lam_O[(-t) % Om] <= Om - 2 for t in range(1, p - 1))
        off = [(a, b) for a in range(p) for b in range(p) if b != 0 and a != inv2p]
        if p > 20: off = rng.sample(off, 200)
        def lines_through(z, q):
            yield frozenset((a, z[1]) for a in range(q))
            for c in range(q):
                a0 = (z[0] - c * z[1]) % q
                yield frozenset(((a0 + c * b) % q, b) for b in range(q))
        ok_iii = all(not any(all(frob(w, p) in L and half_turn(w, p) in L for w in L) for L in lines_through(z, p)) for z in off)
        # 20:F10 (p20093)
        check("A18", f"no zero off the line, pair ({p}, {Om}): the lines kept by both involutions are F_p and L_1/2 and no other tested line (every line of F_{p}², {carrier}); every label 1 ≤ θ ≤ {p - 2} of F_{p} a nontrivial mode on the line in both frames, the Subject's {p - 2} zeros; {'every' if p <= 20 else '200 sampled'} point(s) off both lines on no line kept by both",
              ok_i and ok_ii and ok_iii, f"both-invariant lines of F_{p}²: {both_p}")

    # A19 the drive theorem (Thm. drive; row E15), on every shell: the drive acts on vectors over F_p^× by (Dv)(x) = v(gx), one
    # chronon. (ii) D x^k = g^k x^k for every mode k (the eigenvector identity, FRC.Rh.shift_power_character) and the eigenvalues
    # g^k are the p−1 nonzero residues, each once: the spectrum is F_p^×, simple; (i) D is orthogonal for the pairing
    # ⟨v, w⟩ = Σ_x v(x) w(x), ⟨Dv, w⟩ = ⟨v, D⁻¹w⟩ on three random pairs, not symmetric, while D + D⁻¹ is symmetric; (iii) the
    # spectrum is real — every eigenvalue a residue of F_p, Frobenius-fixed — and the modes are isotropic, ⟨x^k, x^k⟩ = Z(2k) = 0
    # for k ≠ 0, π and −1 there; (iv) the readout θ_k = −g^k of A15 is minus the eigenvalue; (v) the half-turn negates the
    # eigenvalue, g^{k+π} = −g^k
    for p in SHELLS + [BIG]:
        g = generator(p); n_ = p - 1; pi_ = n_ // 2; ginv = pow(g, p - 2, p); xs = range(1, p)
        D = lambda v: {x: v[(g * x) % p] for x in xs}
        Dinv = lambda v: {x: v[(ginv * x) % p] for x in xs}
        pair = lambda v, w: sum(v[x] * w[x] for x in xs) % p
        modes = {k: {x: pow(x, k, p) for x in xs} for k in range(n_)}
        spec = [pow(g, k, p) for k in range(n_)]
        ok_ii = all(D(modes[k]) == {x: spec[k] * modes[k][x] % p for x in xs} for k in range(n_)) and sorted(spec) == list(range(1, p))
        rng = random.Random(2026 + p)
        vs = [{x: rng.randrange(p) for x in xs} for _ in range(6)]
        pairs3 = ((vs[0], vs[1]), (vs[2], vs[3]), (vs[4], vs[5]))
        ok_i = all(pair(D(v), w) == pair(v, Dinv(w)) for v, w in pairs3)
        symmetric = lambda T: all(pair(T(v), w) == pair(v, T(w)) for v, w in pairs3)
        ok_sym = (not symmetric(D)) and symmetric(lambda v: {x: (D(v)[x] + Dinv(v)[x]) % p for x in xs})
        ok_iii = all(0 < s < p for s in spec) and all(pair(modes[k], modes[k]) == (p - 1 if k in (0, pi_) else 0) for k in range(n_))
        ok_iv = all(((-pow(g, k, p)) % p) == (-spec[k]) % p for k in range(n_)) and (-spec[0]) % p == p - 1
        ok_v = all(pow(g, k + pi_, p) == (-spec[k]) % p for k in range(n_))
        # 20:E15 (p20094)
        check("A19", f"the drive theorem on F_{p}: D x^k = g^k x^k for every mode, the spectrum F_{p}^× simple; ⟨Dv, w⟩ = ⟨v, D⁻¹w⟩ on three random pairs, D not symmetric, D + D⁻¹ symmetric; the spectrum real and the modes isotropic (⟨x^k, x^k⟩ = 0 for k ≠ 0, π, −1 there); the readout minus the eigenvalue; the half-turn negates it",
              ok_i and ok_ii and ok_sym and ok_iii and ok_iv and ok_v, f"g={g}, π={pi_}: eigenvalues g^k = {spec[:6]}…, labels −g^k = {[(-s) % p for s in spec[:6]]}…")

    # A20 the energy domain is a circle (Rem. cayley; row B14), on the shells in full: w = z/(1 − z) carries the critical line
    # {Tr z = 1} into the unit circle U_{p+1} = {N(w) = 1}, the centre 2⁻¹ to 1, injectively, missing −1 alone (the line's
    # point at infinity); the conjugation becomes the inversion, w(z^p) = w(z)^{−1}; the drive about the centre, read on the
    # circle, fixes 1 and is no rotation: its orbit through the modes has p−1 points, while a rotation w ↦ uw by a point u of
    # U_{p+1} agrees with it on no mode set; the exponents a_k of the modes on a generator of U_{p+1} negate under k ↦ k + π
    # (the conjugation is the inversion), so no affine function of k fits them (an affine a_k would take at most two values)
    for p in SHELLS:
        g, nu = generator(p), nonresidue(p); n_ = p - 1; inv2 = (p + 1) // 2; pi_ = n_ // 2
        one, mone = (1, 0), (p - 1, 0)
        inv = lambda z: zpow(z, p * p - 2, nu, p)                                   # z^{−1} in F_{p²}
        cayley = lambda z: mul(z, inv(((1 - z[0]) % p, (-z[1]) % p)), nu, p)      # w = z · (1 − z)^{−1}
        line = [(inv2, b) for b in range(p)]
        ws = [cayley(z) for z in line]
        circle = {z for z in ((a, b) for a in range(p) for b in range(p)) if norm(z, nu, p) == 1}
        ok_circle = len(circle) == p + 1 and all(w in circle for w in ws) and len(set(ws)) == p and cayley((inv2, 0)) == one and mone not in ws
        ok_conj = all(cayley(frob(z, p)) == inv(cayley(z)) == frob(cayley(z), p) for z in line)
        dil = lambda z: (inv2, (g * z[1]) % p)                                        # 2⁻¹ + g(z − 2⁻¹) on the line
        orbit = {cayley(z) for z in line if z[1] != 0}
        ok_fix = cayley(dil((inv2, 0))) == one and len(orbit) == n_ and orbit == set(ws) - {one}
        rotations = [u for u in circle if all(cayley(dil(z)) == mul(u, cayley(z), nu, p) for z in line if z[1] != 0)]
        ok_rot = rotations == []
        u = next(w for w in sorted(circle) if all(zpow(w, j, nu, p) != one for j in range(1, p + 1)))   # a generator of U_{p+1}
        log_u = {zpow(u, j, nu, p): j for j in range(p + 1)}
        a = [log_u[ws[(-pow(g, k, p)) % p]] for k in range(n_)]                     # the mode k sits at b = −g^k
        ok_neg = all((a[(k + pi_) % n_] + a[k]) % (p + 1) == 0 for k in range(n_))
        alpha, beta = (a[1] - a[0]) % (p + 1), a[0]                                   # the one affine candidate, from k = 0, 1
        affine_fails = [k for k in range(n_) if a[k] != (alpha * k + beta) % (p + 1)]
        ok_aff = len(set(a)) == n_ and affine_fails != []
        # 20:B14 (p20095)
        check("A20", f"the energy domain is a circle on F_{p}: z/(1 − z) carries the {p} points of the critical line injectively into U_{p + 1} ({p + 1} points), the centre to 1, −1 not hit; the conjugation becomes the inversion; the drive fixes 1 and is no rotation of the circle; the modes' exponents on a generator of U_{p + 1} negate under k ↦ k + π and fit no affine function of k",
              ok_circle and ok_conj and ok_fix and ok_rot and ok_neg and ok_aff, f"ν={nu}: the modes at the circle points {[ws[b] for b in range(1, 4)]}…; rotations matching the drive: {len(rotations)}; exponents {a[:6]}…, the affine fit from k = 0, 1 fails at k = {affine_fails[:3]}…")
    figure_plane()

# ======================================================================================================================
# block B — the chart [chart]: the de-framing limit of the half-turn, the exhibit (Obs. exhibit; row F9) on the windows of the
# laboratory Subjects, the pair agreement, and the labels read in the cycle's own scale coordinate (Section order; row O9).
# Nothing here is a shell operation: the window's prime-power labels n ≤ H are read with the chart's weight Λ(n), the taper
# 1 − log n/log H, the scale n^{−1/2} and the height γ, and the intensity is |Σ Λ(n)(1 − log n/log H) n^{−1/2−iγ}|² on a grid of
# step 0.02. A window's five peaks are the five tallest peaks on the range 10 to 36 of the height; its resolution is 2π/log H.
def block_B():
    """Block B — the chart: 10 checks, all [chart]."""
    print("\n== block B: the chart ==")
    # B3 the de-framing limit of the half-turn (Prop. critical; row B8): 2⁻¹/p = (2κ+1)/p → ½ from above, in rationals
    vals = [(p, Fraction(2 * ((p - 1) // 4) + 1, p)) for p in [13, 53, 101, 409, 1009, 10009]]
    ok = all(v > Fraction(1, 2) for _, v in vals) and all(vals[i][1] > vals[i + 1][1] for i in range(len(vals) - 1)) \
         and abs(vals[-1][1] - Fraction(1, 2)) < Fraction(1, 1000)
    check("B3", "de-framing limit (2κ+1)/p → ½ from above", ok, "  ".join(f"{p}: {float(v):.5f}" for p, v in vals), kind="[chart]")
    # B5 the exhibit (Obs. exhibit; row F9): the windows of depth 13, 39 and 173 — the windows of F_173, F_1549 and F_30089 —
    # put their five peaks at the first five classical heights within the window's resolution; the peaks to one decimal
    stated = {13: [14.5, 20.5, 25.7, 29.0, 34.9], 39: [14.2, 20.8, 25.4, 30.0, 33.5], 173: [14.2, 20.9, 25.1, 30.2, 33.2]}
    labels = {13: 9, 39: 19, 173: 54}
    got = {}
    for H in stated:
        n, _ = mangoldt(H)
        pk = five_peaks(H)
        got[H] = [round(x, 1) for x in pk]
        ok = (len(n) == labels[H] and got[H] == stated[H] and all(abs(x - z) < resolution(H) for x, z in zip(pk, HEIGHTS[:5]))
              and all(abs(x - z) <= 0.05 + 1e-9 for x, z in zip(got[H], stated[H])))
        # 20:F9 (p20089)
        check("B5", f"the exhibit, window of depth {H} ({labels[H]} prime-power labels): its five peaks {stated[H]} at the first five heights {[round(z, 1) for z in HEIGHTS[:5]]} within the resolution 2π/log {H} = {resolution(H):.1f}",
              ok, f"peaks {got[H]}", kind="[chart]")
    # B6 the pair agreement (row F9): the heights read from a Subject's window and from its Carrier's window agree within the
    # Subject's resolution — on (173, 30089) the Carrier's five peaks lie 0.3, 0.4, 0.5, 1.1, 1.7 from the Subject's, against
    # 2.4; on (1549, 2408561) they lie 0.0, 0.2, 0.3, 0.4, 0.4 apart, against 1.7; the Subject window of (13, 233), of depth 3,
    # holds two prime-power labels, the taper leaves one, and the intensity has no peak
    stated = {(173, 30089): [0.3, 0.4, 0.5, 1.1, 1.7], (1549, 2408561): [0.0, 0.2, 0.3, 0.4, 0.4]}
    for (p, Om), d in stated.items():
        Hp, HO = math.isqrt(p), math.isqrt(Om)
        sub, car = five_peaks(Hp), five_peaks(HO)
        dist = [round(abs(a - b), 1) for a, b in zip(sub, car)]
        ok = dist == d and all(x < resolution(Hp) for x in dist)
        check("B6", f"pair agreement on ({p}, {Om}): the Carrier's window {HO} reads its five peaks {d} from the Subject's window {Hp}, within the Subject's resolution {resolution(Hp):.1f}",
              ok, f"Subject {[round(x, 1) for x in sub]}, Carrier {[round(x, 1) for x in car]}, distances {dist}", kind="[chart]")
    n13, _ = mangoldt(math.isqrt(13))
    e3 = energy(3, np.arange(10, 36, 0.02))
    check("B6", "the pair (13, 233): the Subject's window, of depth 3, holds two prime-power labels, the taper leaves one, and the intensity is flat: no height", len(n13) == 2 and e3.max() - e3.min() < 1e-9,
          f"labels {[int(x) for x in n13]}; the intensity on [10, 36] varies by {e3.max() - e3.min():.1e}", kind="[chart]")
    # B8 the cycle's own scale coordinate (Section order; row O9): read in the discrete logarithm λ_p, the window's prime-power
    # labels load the nontrivial modes like a random sum — on F_1549 the largest loading |Σ_{n∈P} e^{2πi k λ(n)/(p−1)}|² is 108
    # against a mean of 19 (exactly |P| − |P|(|P|−1)/(p−2)) and a random-sum maximum of about |P| log(p−1) = 140 — and no mode
    # stands out
    stated = {173: (30, 9, 46), 1549: (108, 19, 140), 30089: (431, 54, 557)}
    for p in stated:
        n_ = p - 1; H = math.isqrt(p); P = [int(n) for n in mangoldt(H)[0]]
        lam = dlog_table(p, generator(p))
        ph = np.array([lam[n] for n in P])
        ks = np.arange(1, n_)
        load = np.abs(np.exp(2j * np.pi * np.outer(ks, ph) / n_).sum(axis=1)) ** 2
        mx, mean, rnd = load.max(), load.mean(), len(P) * math.log(n_)
        got = (round(mx), round(mean), round(rnd))
        ok = got == stated[p] and mx < rnd and abs(mean - (len(P) - len(P) * (len(P) - 1) / (p - 2))) < 1e-6
        check("B8", f"F_{p}: the {len(P)} prime-power labels of the window read in the discrete logarithm load the {n_ - 1} nontrivial modes at most {stated[p][0]}, mean {stated[p][1]}, a random-sum maximum about {stated[p][2]}: no mode stands out",
              ok, f"(max, mean, random max) = ({mx:.1f}, {mean:.1f}, {rnd:.0f})", kind="[chart]")

# ======================================================================================================================
# block C — the chart at depth [chart]: the window of depth 10⁶ (the window of a shell with p > 10¹²) and the first
# ten heights; the figure fig_primespec from the same arrays (about 20 s).
def block_C():
    """Block C — the chart at depth: 1 check [chart]; the figure fig_primespec."""
    print("\n== block C: the chart at depth ==")
    # C1 the depth 10⁶ (row F9): the ten tallest peaks on the range 10 to 52 are the first ten heights, each within 0.05
    t = time.time()
    pk = sorted(g for g, _ in peaks(10 ** 6, 10, 52, step=0.01)[:10])
    dev = [abs(x - z) for x, z in zip(pk, HEIGHTS)]
    check("C1", f"the window of depth 10⁶: its ten tallest peaks on the range 10 to 52 are the first ten heights, each within 0.05",
          len(pk) == 10 and max(dev) < 0.05, f"peaks {[round(x, 2) for x in pk]}; max deviation {max(dev):.3f}; {time.time() - t:.0f} s", kind="[chart]")
    figure_primespec()

if __name__ == "__main__":
    want = [a.upper() for a in sys.argv[1:]] or sorted(BLOCK)
    bad = [b for b in want if b not in BLOCK]
    if bad: sys.exit(f"no block {', '.join(bad)}: the blocks are {', '.join(sorted(BLOCK))}")
    t0 = time.time()
    for b in want:
        t = time.time(); _run_block(b); print(f"    [block {b}: {time.time() - t:.0f} s]")
    ok = summary(write=(want == sorted(BLOCK)))
    kinds = {}
    for r in RESULTS: kinds[r["kind"]] = kinds.get(r["kind"], 0) + 1
    print("by kind: " + ", ".join(f"{k} {v}" for k, v in sorted(kinds.items())) + f"; {len(RESULTS)} checks in {time.time() - t0:.0f} s" + ("; results.json written" if want == sorted(BLOCK) else ""))
    sys.exit(0 if ok else 1)
