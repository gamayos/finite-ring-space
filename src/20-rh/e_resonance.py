"""
e_resonance.py — block E: resonance, antipode, horizon-scale resolution, square-root cancellation
=================================================================================================
The units-chart side of the construction: Ramanujan sums c_q(n) as the standing waves of the
additive meridian, the Möbius-weighted resonance R_L(n) = Σ_{q≤L} μ(q)/φ(q) c_q(n), its limit the
von Mangoldt weight (Theorem resonance), the energy at the antipode (Obs. antipode), the resolving
band at the Subject horizon (Obs. horizon), and the 1/√p flatness of every single multiplicative-
chart mode against the prime indicator (Prop. flat, Obs. flat). Paper-local predicates:

  E1a Thm. resonance (b)  EXACT     Λ = μ ∗ log on the divisor lattice: −Σ_{d|n} μ(d) log d = log ℓ on prime powers
                                    ℓ^k, 0 otherwise — verified symbolically (sympy) for n ≤ 300, in floating point
                                    for n ≤ 5000
  E1b Thm. resonance (a),(c) [approx]  Hardy: R_L(n) → (φ(n)/n) Λ(n) (Cesàro mean to L = 4000, prime powers ≤ 13:
                                    within 0.02, and nearer that limit than Λ(n)); the intertwiner (n/φ(n)) R → Λ
  E1c Def. resonance / Fig. emergence [approx]  Ψ_L(N) = Σ_{n≤N} (n/φ(n)) R_L(n) → ψ(N): the maximal deviation on
                                    N ≤ 30 falls monotonically over L = 15, 60, 240
  E2a Obs. antipode  EXACT     per-mode energy μ²(q)/φ(q) on squarefree q: 1, ½, ¼, ⅙ at q = 2, 3, 5, 7, with its
                                    unique maximum among the nonconstant modes at the antipode q = 2 (all 2 ≤ q ≤ 2000; q = 1 ties)
  E2b Obs. antipode  [approx]  the additive-transform band energy of the prime indicator on Z/10007, Parseval-
                                    normalised over the bins within three of each a/q, peaks at the antipode and
                                    follows 1/φ(q): 1153 > 592 > 301 > 205 at q = 2, 3, 5, 7 (the paper's figures,
                                    restated on 2026-09-13 from the unnormalised 1220 > 640 > 323 > 214)
  E3  Obs. horizon   [approx]  the resolving threshold L*(H) — the least bandwidth at which R_L separates every prime
                                    power in {2..H} from every non-prime-power — exists for H = 6..50 and tracks the
                                    horizon, L* < 6H, far below the field scale H²
  E4  Obs. flat      [approx]  the maximal correlation of the prime indicator with a multiplicative-chart mode χ_j
                                    is a small multiple of the 1/√(p−2) floor of Prop. flat: 0.077 against 0.0315 at
                                    p = 1009 (2.4×); 0.0087 against 0.0032 over the modes of p = 100049 (2.7×); by
                                    contrast the units-chart resonance correlates 0.90 with the primes in its window

Figures: fig_obstruction.pdf (E3, E4), fig_emergence_frc.pdf (E1c beside the classical reconstruction of ψ from zeros).
"""
import math
import numpy as np
import matplotlib
matplotlib.use("Agg")
import matplotlib.pyplot as plt
from math import gcd
import sympy as sp
from rhcommon import check, sieve_primes, von_mangoldt_support, riemann_zeros, FIGDIR, FAST, Timer

# ------------------------------------------------------------------ arithmetic tables
def sieve_mu_phi(M):
    mu = np.ones(M + 1, dtype=int); phi = np.arange(M + 1); comp = np.zeros(M + 1, dtype=bool); primes = []
    mu[0] = 0
    for i in range(2, M + 1):
        if not comp[i]:
            primes.append(i); mu[i] = -1; phi[i] = i - 1
        for q in primes:
            if i * q > M: break
            comp[i * q] = True
            if i % q == 0:
                mu[i * q] = 0; phi[i * q] = phi[i] * q; break
            mu[i * q] = -mu[i]; phi[i * q] = phi[i] * (q - 1)
    return mu, phi

def divisors(n):
    return [d for d in range(1, n + 1) if n % d == 0]

def ramanujan(q, n, mu):
    """Kluyver: c_q(n) = Σ_{d | gcd(q,n)} d μ(q/d), an integer."""
    g = gcd(q, n)
    return sum(d * mu[q // d] for d in divisors(g))

def resonance_table(Qmax, Nmax, mu, phi):
    """cum[L, n] = R_L(n) = Σ_{q≤L} μ(q)/φ(q) c_q(n), L = 0..Qmax, n = 0..Nmax."""
    C = np.zeros((Qmax + 1, Nmax + 1))
    for q in range(1, Qmax + 1):
        for n in range(1, Nmax + 1):
            C[q, n] = ramanujan(q, n, mu)
    w = np.array([0.0] + [mu[q] / phi[q] for q in range(1, Qmax + 1)])
    return np.cumsum(w[:, None] * C, axis=0)

def von_mangoldt_array(N):
    n, lam = von_mangoldt_support(N)
    out = np.zeros(N + 1); out[n.astype(int)] = lam
    return out

def dlog_table(p):
    g = int(sp.primitive_root(p)); lam = np.zeros(p, dtype=np.int64); x = 1
    for k in range(p - 1):
        lam[x] = k; x = (x * g) % p
    return lam

def chart_mode_correlations(p):
    """|corr(1_Π, χ_j)| for every nontrivial multiplicative-chart mode χ_j(n) = ω^{j λ_p(n)} on F_p^×, by FFT
    over the discrete logarithm; returns (max, the exact root-mean-square 1/√(p−2) of Prop. flat, the array)."""
    lam = dlog_table(p)
    ind = np.zeros(p); ind[sieve_primes(p - 1)] = 1.0
    u = np.zeros(p - 1); u[lam[1:]] = ind[1:]                # u[m] = 1_Π(g^m)
    u = u - u.mean()
    F = np.fft.fft(u)
    corr = np.abs(F[1:]) / (np.linalg.norm(u) * math.sqrt(p - 1))
    return float(corr.max()), 1 / math.sqrt(p - 2), corr

def pearson(a, b):
    a = a - a.mean(); b = b - b.mean()
    return float(a @ b / (np.linalg.norm(a) * np.linalg.norm(b)))

def run():
    print("\n== block E: resonance, antipode, horizon, square-root cancellation ==")
    Qmax, Nmax = 320, 60
    mu, phi = sieve_mu_phi(max(Qmax, 5000))
    with Timer("resonance table"):
        cum = resonance_table(Qmax, Nmax, mu, phi)
    Lam = von_mangoldt_array(5000)
    # ---------------- E1a: Λ = μ * log, exact
    sym_ok = True
    for n in range(2, 301):
        expr = sp.expand_log(-sum(sp.Integer(int(mu[d])) * sp.log(d) for d in divisors(n) if d > 1), force=True)
        f = sp.factorint(n)
        target = sp.log(list(f)[0]) if len(f) == 1 else sp.Integer(0)
        if sp.simplify(expr - target) != 0:
            sym_ok = False; break
    flt = np.array([-sum(mu[d] * math.log(d) for d in divisors(n) if d > 1) for n in range(2, 5001)])
    flt_ok = np.max(np.abs(flt - Lam[2:5001])) < 1e-9
    check("E1a", "Λ = μ ∗ log: −Σ_{d|n} μ(d) log d = Λ(n), symbolic for n ≤ 300, floating point for n ≤ 5000", sym_ok and flt_ok,
          f"symbolic {'ok' if sym_ok else 'FAIL'}; max float deviation {np.max(np.abs(flt - Lam[2:5001])):.1e}", kind="EXACT")
    # ---------------- E1b: Hardy's limit and the intertwiner (Cesàro mean over L ≤ 4000, conditional convergence)
    Qhi = 4000 if not FAST else 1500
    with Timer(f"Cesàro resonance to L = {Qhi}"):
        cumhi = resonance_table(Qhi, 14, mu, phi)
    pps = [2, 3, 4, 5, 7, 8, 9, 11, 13]; comp = [6, 10, 12, 14]
    R = {n: float(cumhi[1:Qhi + 1, n].mean()) for n in pps + comp}
    hardy = all(abs(R[n] - phi[n] / n * Lam[n]) < 0.02 and abs(R[n] - phi[n] / n * Lam[n]) < abs(R[n] - Lam[n]) for n in pps)
    zero_ok = all(abs(R[n]) < 0.02 for n in comp)
    inter = all(abs(n / phi[n] * R[n] - Lam[n]) < 0.03 for n in pps)
    check("E1b", "Hardy: R_L(n) → (φ(n)/n) Λ(n) on prime powers, → 0 off them; intertwiner (n/φ(n)) R → Λ = log ℓ", hardy and zero_ok and inter,
          f"R(2) = {R[2]:.4f} vs ½ log 2 = {0.5 * Lam[2]:.4f}; R(9) = {R[9]:.4f} vs ⅔ log 3 = {2 / 3 * Lam[9]:.4f}; (13/12) R(13) = {13 / 12 * R[13]:.4f} vs log 13 = {Lam[13]:.4f}; max |R| off prime powers {max(abs(R[n]) for n in comp):.3f}", kind="[approx]")
    # ---------------- E1c: the staircase from the modes
    ns = np.arange(2, 31); psi = np.cumsum(Lam[2:31])
    def Psi(L): return np.cumsum([n / phi[n] * cum[L, n] for n in ns])
    devs = [float(np.max(np.abs(Psi(L) - psi))) for L in (15, 60, 240)]
    check("E1c", "Ψ_L(N) → ψ(N) on N ≤ 30: maximal deviation falls monotonically over L = 15, 60, 240", devs[0] > devs[1] > devs[2],
          "max |Ψ_L − ψ| = " + ", ".join(f"{d:.3f}" for d in devs), kind="[approx]")
    # ---------------- E2a: the per-mode energy, exact
    from fractions import Fraction
    E = {q: Fraction(int(mu[q] ** 2), int(phi[q])) for q in range(2, 2001)}
    ok = (E[2], E[3], E[5], E[7]) == (Fraction(1), Fraction(1, 2), Fraction(1, 4), Fraction(1, 6)) and all(E[q] < 1 for q in E if q != 2)
    check("E2a", "per-mode energy μ²(q)/φ(q) = 1, ½, ¼, ⅙ at q = 2, 3, 5, 7; unique maximum among the nonconstant modes at the antipode q = 2 (2 ≤ q ≤ 2000)", ok,
          "energies " + ", ".join(f"q={q}: {E[q]}" for q in (2, 3, 5, 7, 11)), kind="EXACT")
    # ---------------- E2b: the additive-transform band energy (reported against the paper's figures, not pinned)
    p4 = 10007
    ind = np.zeros(p4); ind[sieve_primes(p4 - 1)] = 1.0
    F = np.fft.fft(ind); norm2 = float(ind @ ind)
    band = {}
    for q in (2, 3, 5, 7):
        e = 0.0
        for a in range(1, q):
            if gcd(a, q) == 1:
                kc = a * p4 / q
                e += sum(abs(F[k % p4]) ** 2 for k in range(int(math.floor(kc)) - 3, int(math.ceil(kc)) + 4))
        band[q] = e / norm2
    law = [band[q] * phi[q] / band[2] for q in (3, 5, 7)]
    stated = {2: 1153, 3: 592, 5: 301, 7: 205}
    ok = band[2] > band[3] > band[5] > band[7] and all(abs(band[q] - stated[q]) < 2 for q in stated) and all(0.85 < r < 1.25 for r in law)
    check("E2b", "additive-transform band energy of the prime indicator on Z/10007 (Parseval-normalised, bins within 3 of a/q): 1153 > 592 > 301 > 205, the law 1/φ(q)", ok,
          " > ".join(f"q={q}: {band[q]:.0f}" for q in (2, 3, 5, 7)) + f"; φ(q)·E_q/E_2 = " + ", ".join(f"{r:.2f}" for r in law), kind="[approx]")
    # ---------------- E3: the resolving threshold
    Hs = list(range(6, 51, 2)); Ls = []
    for H in Hs:
        pp = [n for n in range(2, H + 1) if Lam[n] > 0]; npp = [n for n in range(2, H + 1) if Lam[n] == 0]
        Lstar = next((L for L in range(2, Qmax + 1) if min(cum[L, n] for n in pp) > max(abs(cum[L, n]) for n in npp)), None)
        Ls.append(Lstar)
    ok = all(L is not None for L in Ls) and all(L < 6 * H for L, H in zip(Ls, Hs)) and all(L < H * H for L, H in zip(Ls, Hs) if H >= 8)
    ratio = [L / H for L, H in zip(Ls, Hs)]
    check("E3", "resolving threshold L*(H) exists for H = 6..50 and tracks the horizon: L* < 6H ≪ H²", ok,
          f"L*/H in [{min(ratio):.2f}, {max(ratio):.2f}]; L*(12) = {Ls[Hs.index(12)]}, L*(20) = {Ls[Hs.index(20)]}, L*(50) = {Ls[-1]}", kind="[approx]")
    # ---------------- E4: square-root cancellation of every chart mode
    with Timer("chart-mode correlations"):
        m1, f1, corr1 = chart_mode_correlations(1009)
        p5 = int(sp.nextprime(100_000))
        while p5 % 4 != 1: p5 = int(sp.nextprime(p5))
        m5, f5, _ = chart_mode_correlations(p5)
    cum200 = resonance_table(80, 200, mu, phi)
    rn = np.arange(2, 201); res_corr = pearson(np.array([1.0 if sp.isprime(int(n)) else 0.0 for n in rn]), np.array([cum200[80, n] for n in rn]))
    ok = (abs(m1 - 0.077) < 0.005 and abs(f1 - 0.0315) < 0.0005 and abs(m1 / f1 - 2.43) < 0.03
          and abs(m5 - 0.0087) < 0.0005 and abs(f5 - 0.0032) < 0.0001 and abs(m5 / f5 - 2.75) < 0.03 and res_corr > 0.85)
    check("E4", "max chart-mode correlation with the primes is a small multiple of the 1/√(p−2) floor: 0.077 vs 0.0315 (p = 1009, 2.4×), 0.0087 vs 0.0032 (p = 100049, 2.7×); resonance correlates 0.90", ok,
          f"p = 1009: max {m1:.4f}, floor {f1:.4f}, ratio {m1 / f1:.3f}; p = {p5}: max {m5:.4f} over {(p5 - 1) // 2} mode pairs, floor {f5:.4f}, ratio {m5 / f5:.3f}; corr(1_Π, R_80) on n ≤ 200 = {res_corr:.2f}", kind="[approx]")
    # ---------------- figures
    FIN, TEAL = "#3b34a8", "#1f9e8a"
    fig, ax = plt.subplots(1, 2, figsize=(12, 4.0))
    ax[0].plot(np.arange(1, len(corr1) // 2 + 1), corr1[:len(corr1) // 2], color=TEAL, lw=0.6)
    ax[0].axhline(f1, color="#888", ls="--", lw=1, label=r"floor $1/\sqrt{p-2}$")
    ax[0].axhline(res_corr, color=FIN, lw=1.8, label=f"units-chart resonance ({res_corr:.2f})")
    ax[0].set_ylim(0, 1); ax[0].set_xlabel("chart mode index $j$"); ax[0].set_ylabel(r"$|{\rm corr}(1_\Pi,\chi_j)|$")
    ax[0].set_title(f"E4: chart modes are blind to primality (p = 1009, max {m1:.3f})", fontsize=10); ax[0].legend(fontsize=8, loc="center right")
    ax[1].plot(Hs, Ls, "o-", color=FIN, lw=1.4, ms=4, label=r"resolving scale $L^*(H)$")
    ax[1].plot(Hs, Hs, "--", color=TEAL, lw=1.2, label=r"horizon $H=\lfloor\sqrt{p}\rfloor$")
    ax[1].plot(Hs, [h * h for h in Hs], ":", color="#b00", lw=1.5, label=r"field $p\sim H^2$")
    ax[1].set_yscale("log"); ax[1].set_xlabel("window horizon $H$"); ax[1].set_ylabel("frequency scale")
    ax[1].set_title("E3: the resolving band sits at the horizon", fontsize=10); ax[1].legend(fontsize=8, loc="upper left")
    plt.tight_layout(); plt.savefig(f"{FIGDIR}/fig_obstruction.pdf", bbox_inches="tight"); plt.savefig(f"{FIGDIR}/fig_obstruction.png", dpi=110, bbox_inches="tight"); plt.close()
    print(f"    wrote {FIGDIR}/fig_obstruction.pdf")
    # emergence: classical zeros (left) against units-chart modes (right)
    import mpmath as mp
    g = riemann_zeros(80)
    X0, X1 = 2, 30
    xs = np.linspace(X0 + 0.02, X1, 1400)
    rho = [mp.mpc(0.5, float(gg)) for gg in g]
    def psi_M(x, M):
        s = sum(2 * mp.re(mp.power(x, r) / r) for r in rho[:M])
        return float(x - mp.log(2 * mp.pi) - 0.5 * mp.log(1 - x ** -2) - s)
    CL = ["#f0a8a8", "#df6b6b", "#c0392b"]; FR = ["#a8c4ec", "#5f8fd6", "#1f5fbf"]; GRIDC = "#d9d9d9"
    fig, ax = plt.subplots(2, 2, figsize=(13.5, 8.2))
    A = ax[0, 0]
    for i, m in enumerate([1, 2, 3]):
        A.plot(xs, [float(-2 * mp.re(mp.power(x, rho[m - 1]) / rho[m - 1])) for x in xs], color=CL[i], lw=1.4, label=fr"$\rho_{m}=\frac{{1}}{{2}}+i\,{float(g[m - 1]):.2f}$")
    A.axhline(0, color=GRIDC, lw=0.8); A.set_title("classical spectral modes: the zeros"); A.set_xlabel("$x$"); A.set_ylabel(r"$-2\,{\rm Re}\,x^{\rho_m}/\rho_m$"); A.legend(fontsize=8); A.set_xlim(X0, X1)
    B = ax[0, 1]
    for i, q in enumerate([2, 3, 5]):
        B.step(ns, [mu[q] / phi[q] * ramanujan(q, int(n), mu) for n in ns], where="mid", color=FR[i], lw=1.5, label=fr"$q={q}$ (energy {E[q]})")
    B.axhline(0, color=GRIDC, lw=0.8); B.set_title(r"units-chart modes $\frac{\mu(q)}{\varphi(q)}c_q$ for $q=2,3,5$ (decreasing energy)"); B.set_xlabel("$n$"); B.legend(fontsize=8); B.set_xlim(X0, X1)
    C = ax[1, 0]
    C.step(np.concatenate([[X0], ns]), np.concatenate([[0], psi]), where="post", color="#111", lw=2.0, label=r"$\psi(x)$")
    for i, M in enumerate([5, 20, 80]):
        C.plot(xs, [psi_M(x, M) for x in xs], color=CL[i], lw=1.3, label=f"{M} zeros")
    C.set_title(r"classical: $\psi(x)$ from $M$ zeros"); C.set_xlabel("$x$"); C.legend(fontsize=8, loc="upper left"); C.set_xlim(X0, X1); C.set_ylim(0, X1 + 4)
    D = ax[1, 1]
    D.step(np.concatenate([[X0], ns]), np.concatenate([[0], psi]), where="post", color="#111", lw=2.0, label=r"$\psi(N)$")
    for i, L in enumerate([15, 60, 240]):
        D.plot(ns, Psi(L), color=FR[i], lw=1.4, label=f"bandwidth $L={L}$ (max dev {devs[i]:.2f})")
    D.set_title(r"E1c: $\Psi_L(N)=\sum_{n\leq N}\frac{n}{\varphi(n)}R_L(n)$ from $L$ units-chart modes"); D.set_xlabel("$N$"); D.legend(fontsize=8, loc="upper left"); D.set_xlim(X0, X1); D.set_ylim(0, X1 + 4)
    plt.tight_layout(); plt.savefig(f"{FIGDIR}/fig_emergence_frc.pdf", bbox_inches="tight"); plt.savefig(f"{FIGDIR}/fig_emergence_frc.png", dpi=110, bbox_inches="tight"); plt.close()
    print(f"    wrote {FIGDIR}/fig_emergence_frc.pdf")

if __name__ == "__main__":
    from rhcommon import summary
    run(); summary(write=False)
