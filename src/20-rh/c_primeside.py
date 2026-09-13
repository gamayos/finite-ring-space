"""
c_primeside.py — block C: the spectrum from the prime side, ζ never evaluated ([approx])
=======================================================================================
Every construction here uses only {Λ(n)} (sieved), their logarithms, and the archimedean
phase θ(T) from log Γ. The Riemann heights enter as validation markers only.
Paper-local predicates:

  C1  Obs. primespec  the scale-spectrum |Σ_N(γ)| of the tapered comb, N = 10⁶, peaks at the first six
                      heights (paper: 14.14, 21.02, 25.02, 30.40, 32.96, 37.57; the peak is the taper's, of width ~2π/log N)
  C2  Obs. trace      the raw secular condition Ñ_N(T) = n − ½ recovers the first ten heights: mean error
                      4.4×10⁻⁵, maximum 1.5×10⁻⁴ (at γ₁) at N = 10⁶; 3.6×10⁻⁴ at 10³; 6×10⁻⁵ at 10⁵
  C2b Obs. trace      the pole-corrected secular condition N̂_N(T) = n − ½ (Prop. combformula): mean error 3.4×10⁻⁵
                      (max 6.6×10⁻⁵) at 10⁶, 2.3×10⁻⁵ at 10⁷, 1.3×10⁻⁵ (max 2.8×10⁻⁵) at 10⁸ — falling with depth
  C2c Obs. trace      the raw condition does not sharpen past 10⁷: mean 2.7×10⁻⁵ at 10⁷ and 4.2×10⁻⁵ at 10⁸, the γ₁
                      error growing from 1.5×10⁻⁴ (10⁶) to 2.6×10⁻⁴ (10⁸) — the pole term, largest at the lowest height
  C3  Obs. matrix     the colleague matrix of the Chebyshev fit of Ξ(T) = cos(π N̂_N(T)) on [10, 52] at N = 10⁶:
                      mean error 4.8×10⁻⁵ at dimension 520, 3.5×10⁻⁵ by 620, converging to the corrected roots' own 3.4×10⁻⁵
  C4  Obs. jacobi     the comb-built Jacobi matrix of the corrected secular roots: real-symmetric tridiagonal, eigenvalues =
                      the roots to 10⁻¹², the heights to 3.4×10⁻⁵; the ten recurrence coefficients a, b as stated
  C5  Prop. gauge     the additive injection −i d/du + V_comb is gauge-trivial: spacing standard
                      deviation 0.08 (absolute; 0.11 of the mean spacing 0.72) against 0.39 of the mean
                      for the heights (package finding: the paper's two figures use two conventions)

Figures: fig_prime_spectrum.pdf (C1), fig_operator_spectrum.pdf (C2, C3, C5).
"""
import math
import numpy as np
import matplotlib
matplotlib.use("Agg")
import matplotlib.pyplot as plt
from rhcommon import (check, Comb, count_raw, count_corrected, secular_roots, colleague_roots, jacobi_from_points,
                      HEIGHTS, nearest_errors, theta, FIGDIR, FAST, Timer)

# the paper's stated numbers
PEAKS_STATED = [14.14, 21.02, 25.02, 30.40, 32.96, 37.57]
A_STATED = [34.314, 31.021, 31.179, 31.763, 32.812, 36.227, 35.012, 37.157, 36.092, 37.564]
B_STATED = [11.178, 10.431, 9.579, 8.263, 7.008, 8.415, 7.048, 4.093, 4.110]

def windows(n_heights=10, half=0.5):
    return [(n + 1, HEIGHTS[n] - half, HEIGHTS[n] + half) for n in range(n_heights)]

def additive_spectrum(U=15.0, M=2048, potential_scale=5.0):
    """H = −i d/du + V_comb on a periodic log-grid of length U (Prop. gauge)."""
    du = U / M
    k = np.fft.fftfreq(M, d=du) * 2 * np.pi
    F = np.fft.fft(np.eye(M), axis=0) / np.sqrt(M)
    D = F.conj().T @ np.diag(k) @ F
    D = 0.5 * (D + D.conj().T)
    from rhcommon import von_mangoldt_support
    Np = int(math.e ** U) + 1
    n, lam = von_mangoldt_support(Np)
    V = np.zeros(M)
    for nn, ll in zip(n, lam):
        j = int(round(math.log(nn) / du)) % M
        V[j] += ll / math.sqrt(nn) / du
    H = D + np.diag(potential_scale * V)
    H = 0.5 * (H + H.conj().T)
    return np.sort(np.linalg.eigvalsh(H))

def run():
    print("\n== block C: the prime-side realisation, ζ never evaluated ==")
    N = 10 ** 6
    with Timer(f"comb to {N}"):
        comb = Comb(N)
    # C1 peaks of the scale-spectrum
    with Timer("scale-spectrum"):
        gs = np.arange(10.0, 40.0, 0.005)
        sig = comb.sigma(gs)
    peaks = [gs[i] for i in range(1, len(gs) - 1) if sig[i] > sig[i - 1] and sig[i] > sig[i + 1]]
    top = sorted(sorted(peaks, key=lambda g: -sig[np.argmin(np.abs(gs - g))])[:6])
    err1 = [abs(t - h) for t, h in zip(top, HEIGHTS[:6])]
    err_stated = [abs(t - h) for t, h in zip(top, PEAKS_STATED)]
    base = np.median(sig)
    ratio = min(sig[np.argmin(np.abs(gs - t))] for t in top) / base
    check("C1", "scale-spectrum peaks at the stated 14.14 … 37.57 (within 0.015) and at γ_1..γ_6 (within 0.05, the taper's width); each peak ≥ 4× the baseline",
          max(err_stated) < 0.015 and max(err1) < 0.05 and ratio > 4,
          "peaks " + ", ".join(f"{t:.2f}" for t in top) + f"; max |peak − γ| {max(err1):.3f}; min peak/baseline {ratio:.1f}", kind="[approx]")
    # C2 secular roots at three depths
    errs = {}
    for depth in ([10 ** 3, 10 ** 5, 10 ** 6] if not FAST else [10 ** 5, 10 ** 6]):
        c = comb if depth == N else Comb(depth)
        roots = secular_roots(c, windows())
        e = np.abs(roots - HEIGHTS[:10]); errs[depth] = (e.mean(), e.max())
    e6 = errs[10 ** 6]
    ok = abs(e6[0] - 4.4e-5) < 0.6e-5 and abs(e6[1] - 1.46e-4) < 0.15e-4 and (FAST or errs[10 ** 3][0] < 6e-4) and errs[10 ** 5][0] < 1e-4
    check("C2", "raw secular condition: ten heights to mean 4.4e-5, max 1.5e-4 (γ₁) at N = 10⁶; 3.6e-4 at 10³, 6e-5 at 10⁵", ok,
          "; ".join(f"N={d:.0e}: mean {m:.2e} max {x:.2e}" for d, (m, x) in errs.items()), kind="[approx]")
    # C2b, C2c: the pole-corrected secular condition against the raw one, with depth (Prop. combformula)
    deep = [10 ** 6, 10 ** 7] + ([10 ** 8] if not FAST else [])
    raw_e, cor_e = {}, {}
    with Timer(f"secular roots, raw and corrected, to {deep[-1]:.0e}"):
        for depth in deep:
            c = comb if depth == N else Comb(depth)
            er = np.abs(secular_roots(c, windows()) - HEIGHTS[:10]); ec = np.abs(secular_roots(c, windows(), corrected=True) - HEIGHTS[:10])
            raw_e[depth] = (er.mean(), er.max(), er[0]); cor_e[depth] = (ec.mean(), ec.max(), ec[0])
            if depth != N: del c
    c6 = cor_e[10 ** 6]
    ok = (abs(c6[0] - 3.4e-5) < 0.4e-5 and abs(c6[1] - 6.6e-5) < 0.8e-5 and abs(cor_e[10 ** 7][0] - 2.3e-5) < 0.4e-5
          and (FAST or (abs(cor_e[10 ** 8][0] - 1.3e-5) < 0.3e-5 and cor_e[10 ** 8][1] < 3.2e-5))
          and all(cor_e[deep[i + 1]][0] < cor_e[deep[i]][0] for i in range(len(deep) - 1)))
    check("C2b", "pole-corrected secular condition: mean 3.4e-5 (max 6.6e-5) at 10⁶, 2.3e-5 at 10⁷, 1.3e-5 (max 2.8e-5) at 10⁸; falling with depth", ok,
          "; ".join(f"N={d:.0e}: mean {m:.2e} max {x:.2e} γ₁ {g:.2e}" for d, (m, x, g) in cor_e.items()), kind="[approx]")
    ok = (abs(raw_e[10 ** 7][0] - 2.7e-5) < 0.4e-5 and (FAST or (abs(raw_e[10 ** 8][0] - 4.2e-5) < 0.5e-5 and raw_e[10 ** 8][0] > raw_e[10 ** 7][0]
          and abs(raw_e[10 ** 8][2] - 2.6e-4) < 0.3e-4 and raw_e[10 ** 8][2] > raw_e[10 ** 6][2])))
    check("C2c", "raw secular condition does not sharpen past 10⁷: mean 2.7e-5 at 10⁷, 4.2e-5 at 10⁸; γ₁ error 1.5e-4 (10⁶) → 2.6e-4 (10⁸): the pole term", ok,
          "; ".join(f"N={d:.0e}: mean {m:.2e} max {x:.2e} γ₁ {g:.2e}" for d, (m, x, g) in raw_e.items()), kind="[approx]")
    roots6 = secular_roots(comb, windows(), corrected=True)
    # C4 Jacobi (of the corrected secular roots)
    J = jacobi_from_points(roots6)
    ev = np.sort(np.linalg.eigvalsh(J))
    a, b = np.diag(J), np.diag(J, 1)
    ok = (np.allclose(J, J.T) and np.max(np.abs(np.triu(J, 2))) == 0 and np.max(np.abs(ev - roots6)) < 1e-12
          and np.max(np.abs(a - A_STATED)) < 2e-3 and np.max(np.abs(b - B_STATED)) < 2e-3
          and abs(np.mean(np.abs(ev - HEIGHTS[:10])) - 3.4e-5) < 0.4e-5)
    check("C4", "Jacobi matrix of the corrected roots: real-symmetric tridiagonal; eig = roots to 1e-12; a, b as stated; heights to 3.4e-5", ok,
          f"max|eig−roots| = {np.max(np.abs(ev - roots6)):.1e}; a[0..2] = {a[0]:.3f}, {a[1]:.3f}, {a[2]:.3f}; b[0] = {b[0]:.3f}", kind="[approx]")
    # C3 colleague matrix of the corrected secular determinant
    with Timer("colleague matrices"):
        degs = [180, 260, 340, 420, 520, 620] if not FAST else [340, 520]
        conv = {d: float(np.mean(nearest_errors(colleague_roots(comb, 10.0, 52.0, d, corrected=True), HEIGHTS[:10]))) for d in degs}
    ok = abs(conv[520] - 4.8e-5) < 0.6e-5 and (FAST or abs(conv[620] - 3.5e-5) < 0.5e-5)
    check("C3", "colleague matrix of cos(π N̂_N) on [10,52], N = 10⁶: mean error 4.8e-5 at dim 520, 3.5e-5 by 620 (the roots' own 3.4e-5)", ok,
          "; ".join(f"dim {d}: {v:.2e}" for d, v in conv.items()), kind="[approx]")
    eig520 = colleague_roots(comb, 10.0, 52.0, 520, corrected=True)
    # C5 additive injection
    with Timer("additive operator"):
        ev_add = additive_spectrum()
    eva = ev_add[(ev_add > 10) & (ev_add < 50)]
    da, dh = np.diff(eva), np.diff(HEIGHTS[:10])
    cv_add, cv_h = np.std(da) / np.mean(da), np.std(dh) / np.mean(dh)
    check("C5", "additive −i d/du + V_comb has a uniform spectrum: spacing std 0.08 (0.11 of its mean) against 0.39 of the mean for the heights",
          abs(np.std(da) - 0.08) < 0.01 and cv_add < 0.15 and abs(cv_h - 0.39) < 0.02,
          f"additive: std {np.std(da):.3f} on mean spacing {np.mean(da):.3f} (ratio {cv_add:.3f}); heights: std {np.std(dh):.2f} on mean {np.mean(dh):.2f} (ratio {cv_h:.3f}) — the paper's 0.08 is the absolute std, its 0.39 the ratio", kind="[approx]")
    # ---- figures
    fig, ax = plt.subplots(1, 2, figsize=(12, 3.8))
    ax[0].plot(gs, sig, color="#10325f", lw=1.0)
    for h in HEIGHTS[:6]: ax[0].axvline(h, color="#c0392b", ls="--", lw=0.8)
    ax[0].plot(top, [sig[np.argmin(np.abs(gs - t))] for t in top], "o", color="#e67e22")
    ax[0].set_xlabel(r"$\gamma$"); ax[0].set_ylabel(r"$|\Sigma_N(\gamma)|$"); ax[0].set_title(f"C1: scale-spectrum of the comb, N = 10⁶ (peaks vs heights)")
    for Ndepth, col in [(10 ** 4, "#9ec5e8"), (10 ** 5, "#5b9bd5"), (10 ** 6, "#10325f")]:
        c = comb if Ndepth == N else Comb(Ndepth)
        g2 = np.arange(13.0, 15.3, 0.002)
        ax[1].plot(g2, c.sigma(g2) / c.sigma(HEIGHTS[0]), color=col, lw=1.1, label=f"N = 10^{int(math.log10(Ndepth))}")
    ax[1].axvline(HEIGHTS[0], color="#c0392b", ls="--", lw=0.8); ax[1].set_xlabel(r"$\gamma$"); ax[1].legend(fontsize=8)
    ax[1].set_title(r"peak at $\gamma_1$ sharpens with depth, width $\sim 2\pi/\log N$")
    plt.tight_layout(); plt.savefig(f"{FIGDIR}/fig_prime_spectrum.pdf", bbox_inches="tight"); plt.savefig(f"{FIGDIR}/fig_prime_spectrum.png", dpi=110, bbox_inches="tight"); plt.close()
    print(f"    wrote {FIGDIR}/fig_prime_spectrum.pdf")
    Tg = np.arange(11.0, 40.0, 0.02)
    NB = theta(Tg) / math.pi + 1.0; NC = count_raw(comb, Tg); NH = count_corrected(comb, Tg)
    fig, ax = plt.subplots(1, 3, figsize=(13.5, 4.2))
    ax[0].plot(Tg, NC, color="#10325f", lw=1.4, label=r"raw $\tilde{N}_N(T)=\theta/\pi+1+S_{\rm comb}$")
    ax[0].plot(Tg, NH, color="#1f6b4a", lw=1.0, ls="--", label=r"pole-corrected $\hat{N}_N(T)$")
    ax[0].plot(Tg, NB, color="#9ec5e8", lw=1.3, label=r"$\theta(T)/\pi+1$")
    for n in range(2, 9): ax[0].axhline(n - 0.5, color="#bbb", lw=0.6, ls=":")
    for g in HEIGHTS[:6]: ax[0].axvline(g, color="#c0392b", lw=0.8, ls="--", alpha=0.7)
    ax[0].set_xlim(11, 40); ax[0].set_ylim(1, 9); ax[0].set_xlabel("$T$"); ax[0].set_ylabel("raw comb count")
    ax[0].set_title(r"C2/C2b: secular condition, count $= n-\frac{1}{2}$ at the heights", fontsize=10); ax[0].legend(fontsize=8, loc="upper left")
    ax[1].vlines(HEIGHTS[:10], 0, 1, color="#c0392b", ls="--", lw=1.1, label="heights (markers)")
    ax[1].plot(eig520, 0.5 * np.ones_like(eig520), "o", color="#10325f", ms=7, label="colleague eigenvalues")
    ax[1].set_xlim(10, 52); ax[1].set_ylim(0, 1); ax[1].set_yticks([]); ax[1].set_xlabel(r"$\gamma$")
    ax[1].set_title(f"C3: colleague matrix (corrected), dim 520, mean err {conv[520]:.1e}", fontsize=10); ax[1].legend(fontsize=8, loc="lower center")
    axin = ax[1].inset_axes([0.10, 0.58, 0.42, 0.32]); axin.semilogy(list(conv), list(conv.values()), "o-", color="#1f6b4a", ms=3.5)
    axin.set_title("mean error vs dimension", fontsize=7); axin.tick_params(labelsize=6)
    ax[2].vlines(eva, 0.55, 0.95, color="#1f6b4a", lw=1.0); ax[2].vlines(HEIGHTS[(HEIGHTS > 10) & (HEIGHTS < 50)], 0.05, 0.45, color="#c0392b", lw=1.4)
    ax[2].set_xlim(10, 50); ax[2].set_ylim(0, 1); ax[2].set_yticks([0.25, 0.75]); ax[2].set_yticklabels(["heights", "dilation\n+ comb"], fontsize=8.5)
    ax[2].set_xlabel(r"$\gamma$"); ax[2].set_title("C5: additive injection is gauge-trivial", fontsize=10)
    plt.tight_layout(); plt.savefig(f"{FIGDIR}/fig_operator_spectrum.pdf", bbox_inches="tight"); plt.savefig(f"{FIGDIR}/fig_operator_spectrum.png", dpi=110, bbox_inches="tight"); plt.close()
    print(f"    wrote {FIGDIR}/fig_operator_spectrum.pdf")
    return comb

if __name__ == "__main__":
    from rhcommon import summary
    run(); summary(write=False)
