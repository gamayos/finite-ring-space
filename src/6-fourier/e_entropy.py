"""
e_entropy.py — block E: the cyclotomic observer readout and the entropy on the meridian cycle
===========================================================================================
Paper statements decided (Section 9, Subsection sec:entropy). The readout of Definition def:readout
realises the fractional family on C^n through the observer's continuum chart σ_C: X ↦ ζ_n, Y ↦ +√n —
the canonical DFT projectors with the eigenvalue refinement g^{−ℓs} ↦ ζ_n^{−ℓs}. Floating point
enters here and only here; the kinds are marked.

  E1  def:readout          the readout algebra: Ĝ = Σ_k X^{k²} satisfies Ĝ² = 2n X^κ modulo Φ_n(X) —
      (EXACT)              exact integer polynomial arithmetic; and both specialisations: σ_C gives
                           (Σ ζ^{k²})² = 2n i, ρ gives G² = 2i in F_p (the reduction used in thm:multiplicity)
  E2  prop:entropy         H(0) = H(2κ) = 0, H(κ) = H(3κ) = log n for every site-localised input δ_j
  E3  prop:entropy         B_0 and B_κ mutually unbiased (every overlap 1/n); Maassen–Uffink
                           H_{B_0} + H_{B_κ} ≥ log n on random states, saturated by the localised states;
                           the comb (δ_0 + δ_6)/√2 at n = 12 gives log 2 + log 6 = log 12
  E4  prop:closedform      the readout of F^[s] δ_0 is two-valued, p_0 = 1 − (n−1)t_s/n, p_j = t_s/n, with
                           t_s = (2 − ζ^{2s} − ζ^{−2s})/4 = sin²(πs/2κ); H(s) the closed form; strictly
                           increasing on 0 ≤ s ≤ κ; two oscillations per cycle
  E5  §9 table, fig        p = 13: H(s)/log n = 0, .44, .91, 1, .91, .44, 0, .44, .91, 1, .91, .44;
      entropy13            regenerates figures/entropy-cycle-f13.{pdf,png}
  E6  rem:input-dep        δ_1 at p = 13: H(1)/log n = 0.55 against 0.44 for δ_0; δ_j meets Π_1, Π_3 exactly
                           when j ∉ {0, 2κ}; δ_{2κ} gives the δ_0 curve
  E7  def:readout          the Galois twist X ↦ ζ^u relabels the δ_0 curve by s ↦ us on every unit u and
                           leaves the cardinal values of every δ_j invariant (the relabelling of the
                           intermediate curve of δ_j, j ∉ {0, 2κ}, holds for u = −1 only — see README)

Shells: n = 4, 12, 16, 28, 36, 40 (p = 5, 13, 17, 29, 37, 41).
"""
import os
import numpy as np
from fcommon import check, Frame, SHELLS, FIGDIR

def cyclotomic(n):
    """Φ_n(X) as an integer coefficient array (low to high), by exact division of X^n − 1."""
    def polydiv_exact(a, b):                       # a / b, b monic, integer, exact
        a = list(a); q = [0] * (len(a) - len(b) + 1)
        for i in range(len(q) - 1, -1, -1):
            q[i] = a[i + len(b) - 1]
            for j in range(len(b)):
                a[i + j] -= q[i] * b[j]
        assert all(x == 0 for x in a[:len(b) - 1]), "inexact"
        return q
    poly = [-1] + [0] * (n - 1) + [1]               # X^n − 1
    for d in range(1, n):
        if n % d == 0:
            poly = polydiv_exact(poly, cyclotomic(d))
    return poly

def polymod_cyc(a, n):
    """Reduce a polynomial modulo X^n − 1 (exponents mod n)."""
    r = [0] * n
    for k, c in enumerate(a):
        r[k % n] += c
    return r

def polymul_cyc(a, b, n):
    r = [0] * n
    for i, x in enumerate(a):
        if x:
            for j, y in enumerate(b):
                if y:
                    r[(i + j) % n] += x * y
    return r

def polyrem(a, b):
    """Remainder of a modulo monic integer b (exact integer arithmetic)."""
    a = list(a)
    while len(a) >= len(b):
        c = a[-1]
        if c:
            for j in range(len(b)):
                a[len(a) - len(b) + j] -= c * b[j]
        a.pop()
    return a

def dft_family(n, u=1):
    """The readout family on C^n under the chart X ↦ ζ_n^u: the canonical DFT projectors and
    F^[s] = Σ_ℓ ζ^{−uℓs} Π_ℓ (Definition def:readout; entropy_meridian_cycle.py of the paper's code/)."""
    kap = n // 4
    z = np.exp(2j * np.pi * u / n)
    D = np.array([[z ** (j * k) for k in range(n)] for j in range(n)]) / np.sqrt(n)
    iota = z ** (-kap)
    Ds = [np.eye(n)]
    for _ in range(3):
        Ds.append(Ds[-1] @ D)
    P = [sum(iota ** (-l * r) * Ds[r] for r in range(4)) / 4 for l in range(4)]
    assert np.allclose(sum(P), np.eye(n)) and all(np.allclose(Pl @ Pl, Pl) for Pl in P)
    return D, P, (lambda s: sum(z ** (-l * s) * P[l] for l in range(4)))

def entropy(vec):
    q = np.abs(vec) ** 2; q = q / q.sum(); q = q[q > 1e-15]
    return float(-(q * np.log(q)).sum()) + 0.0          # (+0.0 clears a signed zero)

def delta(n, j):
    e = np.zeros(n); e[j] = 1.0
    return e

def run():
    print("block E — the cyclotomic observer readout")
    frames = {p: Frame(p) for p in SHELLS}

    # E1 — the readout algebra identity, exact
    ok, det = True, []
    for p in SHELLS:
        f = frames[p]; n, k = f.n, f.kap
        G = [0] * n
        for kk in range(n):
            G[(kk * kk) % n] += 1                                      # Ĝ = Σ_k X^{k²} mod X^n − 1
        G2 = polymul_cyc(G, G, n)
        G2[k] -= 2 * n                                                 # Ĝ² − 2n X^κ
        rem = polyrem(G2, cyclotomic(n))
        ok &= all(c == 0 for c in rem)
        z = np.exp(2j * np.pi / n)
        ok &= abs(sum(z ** (kk * kk) for kk in range(n)) ** 2 - 2 * n * 1j) < 1e-9
        ok &= (f.gauss() ** 2 % p == 2 * f.i % p)
        det.append(f"n={n}: deg Φ_n = {len(cyclotomic(n)) - 1}")
    check("E1", "Ĝ² = 2n X^κ modulo Φ_n(X) (exact integer arithmetic); under σ_C: (Σ ζ^{k²})² = 2n i; under ρ: G² = 2i in F_p", ok, "; ".join(det))

    # E2 — cardinal values for every localised input
    ok = True
    for p in SHELLS:
        f = frames[p]; n, k = f.n, f.kap
        D, P, frft = dft_family(n)
        for j in range(n):
            e = delta(n, j)
            ok &= abs(entropy(frft(0) @ e)) < 1e-9 and abs(entropy(frft(2 * k) @ e)) < 1e-9
            ok &= abs(entropy(frft(k) @ e) - np.log(n)) < 1e-9 and abs(entropy(frft(3 * k) @ e) - np.log(n)) < 1e-9
        ok &= np.allclose(frft(0), np.eye(n)) and np.allclose(frft(k), D) and np.allclose(frft(2 * k), D @ D)
    check("E2", "H(0) = H(2κ) = 0, H(κ) = H(3κ) = log n for every δ_j", ok, f"n ∈ {[p - 1 for p in SHELLS]}", kind="[approx]")

    # E3 — mutually unbiased bases, Maassen–Uffink, the comb
    ok, rng = True, np.random.default_rng(6)
    for p in SHELLS:
        n = p - 1; k = n // 4
        D, P, frft = dft_family(n)
        Bk = frft(k)                                                    # the columns of B_κ = F^[κ] B_0
        ok &= np.allclose(np.abs(Bk) ** 2, 1.0 / n)                     # every overlap |<b_0,j|b_κ,l>|² = 1/n
        for _ in range(200):
            psi = rng.normal(size=n) + 1j * rng.normal(size=n); psi /= np.linalg.norm(psi)
            ok &= entropy(psi) + entropy(Bk.conj().T @ psi) >= np.log(n) - 1e-9
        e = delta(n, 0)
        ok &= abs(entropy(e) + entropy(Bk.conj().T @ e) - np.log(n)) < 1e-9
    D, P, frft = dft_family(12)
    comb = (delta(12, 0) + delta(12, 6)) / np.sqrt(2)
    h0, hk = entropy(comb), entropy(frft(3).conj().T @ comb)
    ok &= abs(h0 - np.log(2)) < 1e-9 and abs(hk - np.log(6)) < 1e-9 and abs(h0 + hk - np.log(12)) < 1e-9
    check("E3", "B_0, B_κ mutually unbiased (overlaps 1/n); H_{B_0} + H_{B_κ} ≥ log n on random states, saturated by δ_j; the comb (δ_0+δ_6)/√2 at n = 12: log 2 + log 6 = log 12",
          ok, f"comb: H_0 = {h0:.4f} = log 2, H_κ = {hk:.4f} = log 6; 200 random states per shell", kind="[approx]")

    # E4 — the closed form
    ok = True
    curves = {}
    for p in SHELLS:
        n = p - 1; k = n // 4
        D, P, frft = dft_family(n)
        z = np.exp(2j * np.pi / n)
        H = []
        for s in range(n):
            psi = frft(s) @ delta(n, 0); q = np.abs(psi) ** 2
            ts = ((2 - z ** (2 * s) - z ** (-2 * s)) / 4).real
            ok &= abs(ts - np.sin(np.pi * s / (2 * k)) ** 2) < 1e-12
            ok &= abs(q[0] - (1 - (n - 1) * ts / n)) < 1e-9 and np.allclose(q[1:], ts / n, atol=1e-9)
            H.append(entropy(psi))
            if 1e-15 < ts:
                p0 = 1 - (n - 1) * ts / n
                Hcf = -(p0 * np.log(p0) + (n - 1) * (ts / n) * np.log(ts / n))
            else:
                Hcf = 0.0
            ok &= abs(Hcf - H[-1]) < 1e-9
        H = np.array(H); curves[p] = H
        ok &= all(H[s + 1] > H[s] + 1e-9 for s in range(k))               # strictly increasing on [0, κ]
        ok &= np.allclose(H, H[(np.arange(n) + 2 * k) % n]) and np.allclose(H, H[(-np.arange(n)) % n])   # period 2κ, symmetric
        ok &= all(1e-9 < H[s] < np.log(n) - 1e-9 for s in range(n) if s % k)                             # strictly intermediate
    check("E4", "F^[s] δ_0 has the two-valued readout p_0 = 1 − (n−1)t_s/n, p_j = t_s/n, t_s = (2−ζ^{2s}−ζ^{−2s})/4 = sin²(πs/2κ); H(s) the closed form, strictly increasing on [0, κ], period 2κ, strictly intermediate off the cardinal indices",
          ok, f"n ∈ {[p - 1 for p in SHELLS]}", kind="[approx]")

    # E5 — the p = 13 table and the figure
    n = 12; H = curves[13]; Hn = H / np.log(n)
    table = [0, .44, .91, 1, .91, .44, 0, .44, .91, 1, .91, .44]
    ok = all(abs(round(float(Hn[s]), 2) - table[s]) < 1e-9 for s in range(n))
    try:
        import matplotlib
        matplotlib.use("Agg")
        import matplotlib.pyplot as plt
        plt.rcParams.update({"font.family": "serif", "font.size": 11, "mathtext.fontset": "cm", "axes.linewidth": 0.8})
        s = np.arange(n)
        fig, ax = plt.subplots(figsize=(6.2, 3.5))
        ax.axhline(1.0, ls="--", lw=0.8, color="0.5")
        ax.text(n - 0.1, 1.005, r"$\log n$", ha="right", va="bottom", color="0.4", fontsize=10)
        ax.plot(s, Hn, "-", color="0.25", lw=1.3, zorder=1)
        ax.plot(s, Hn, "o", color="0.25", ms=4, zorder=2)
        for kk, col in {0: "tab:blue", 3: "tab:red", 6: "tab:green", 9: "tab:orange"}.items():
            ax.plot(kk, Hn[kk], "o", color=col, ms=8, zorder=3)
        ax.annotate("$M_0$", (0, 0), textcoords="offset points", xytext=(2, 8), color="tab:blue")
        ax.annotate("$M_{2\\kappa}$ (parity)", (6, 0), textcoords="offset points", xytext=(-6, 8), ha="center", color="tab:green")
        ax.annotate("$M_\\kappa$ (Fourier)", (3, 1), textcoords="offset points", xytext=(0, -16), ha="center", color="tab:red")
        ax.annotate("$M_{3\\kappa}$", (9, 1), textcoords="offset points", xytext=(0, -16), ha="center", color="tab:orange")
        ax.set_xlabel(r"meridian index $s\in\mathbb{Z}_{4\kappa}$")
        ax.set_ylabel(r"normalised entropy $H(s)/\log n$")
        ax.set_xticks(range(n)); ax.set_ylim(-0.05, 1.12); ax.set_xlim(-0.4, n - 0.6)
        ax.spines[["top", "right"]].set_visible(False)
        fig.tight_layout()
        for ext in ("pdf", "png"):
            fig.savefig(os.path.join(FIGDIR, f"entropy-cycle-f13.{ext}"), bbox_inches="tight", dpi=150)
        plt.close(fig)
        figmsg = f"wrote {FIGDIR}/entropy-cycle-f13.pdf/.png"
    except ImportError:
        figmsg = "matplotlib absent: figure not written"
    check("E5", "p = 13: H(s)/log n = 0, .44, .91, 1, .91, .44, 0, .44, .91, 1, .91, .44 (fig:entropy13)", ok,
          "H/log n = " + ", ".join(f"{x:.4f}" for x in Hn) + "; " + figmsg, kind="[approx]")

    # E6 — input dependence
    D, P, frft = dft_family(12)
    H1 = np.array([entropy(frft(s) @ delta(12, 1)) for s in range(12)]) / np.log(12)
    H6 = np.array([entropy(frft(s) @ delta(12, 6)) for s in range(12)]) / np.log(12)
    ok = abs(round(float(H1[1]), 2) - 0.55) < 1e-9 and abs(round(float(Hn[1]), 2) - 0.44) < 1e-9
    ok &= np.allclose(H6, Hn) and not np.allclose(H1, Hn)
    for p in SHELLS:
        nn = p - 1; kk = nn // 4
        Dp, Pp, fr = dft_family(nn)
        for j in range(nn):
            odd = np.linalg.norm(Pp[1] @ delta(nn, j)) + np.linalg.norm(Pp[3] @ delta(nn, j))
            ok &= ((odd < 1e-12) == (j in (0, 2 * kk)))
    check("E6", "δ_1 at p = 13: H(1)/log n = 0.55 against 0.44 for δ_0; δ_j meets the odd projectors exactly when j ∉ {0, 2κ}; δ_{2κ} reproduces the δ_0 curve",
          ok, f"δ_1: H(1)/log n = {H1[1]:.4f}; δ_0: {Hn[1]:.4f}", kind="[approx]")

    # E7 — the Galois twist
    ok, n_units = True, 0
    for p in SHELLS:
        nn = p - 1; kk = nn // 4
        base = curves[p]
        for u in range(1, nn):
            if np.gcd(u, nn) != 1:
                continue
            Du, Pu, fru = dft_family(nn, u); n_units += 1
            Hu = np.array([entropy(fru(s) @ delta(nn, 0)) for s in range(nn)])
            ok &= np.allclose(Hu, base[(u * np.arange(nn)) % nn], atol=1e-9)             # s ↦ us on the δ_0 curve
            for j in range(nn):
                e = delta(nn, j)
                ok &= abs(entropy(fru(0) @ e)) < 1e-9 and abs(entropy(fru(2 * kk) @ e)) < 1e-9
                ok &= abs(entropy(fru(kk) @ e) - np.log(nn)) < 1e-9 and abs(entropy(fru(3 * kk) @ e) - np.log(nn)) < 1e-9
    check("E7", "X ↦ ζ^u relabels the δ_0 curve by s ↦ us on every unit u; the cardinal values of every δ_j are invariant under every twist",
          ok, f"{n_units} twists over the six shells", kind="[approx]")

if __name__ == "__main__":
    import fcommon
    run(); fcommon.summary(write=False)
