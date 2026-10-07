"""frc.chart_quantum — the quantum readings in floating point (chart tier; ledger migration, task LM35, 7 October 2026).

The chart theme holds the readings against the continuum, the only place where floats appear (frc/themes.py, rank 30).
This file holds the floating-point computations of 22-quantum's validation package (src/22-quantum): the CHSH sweep of
the composite gate, the Gaussian envelope of the dilation dephasing, the sampled √m illustration, and the hardware
compilations of the forced bases. Each returns numbers that the ledger file compares with exact bounds. The package
used numpy. This file uses `math`, `cmath` and `random` only, so the framework stays free of third-party imports.

    chsh_sweep(n)                   max, min and an argmax of E(Δ₁) + E(Δ₂) + E(Δ₃) − E(Δ₂ + Δ₃ − Δ₁), E(Δ) = cos(2πΔ/n)
    envelope(M, n, taus)            |Σ_E p_E e^{iEθ}| against exp(−σ²θ²/2) for the binomial p_E on 0..M, θ = 2πτ/n
    sampled_scaling(m, k, nph, s)   the mean of |Σ_i ζ^{θ_i}|²/m over k draws of m uniform phases on C_nph, seed s
    emulation()                     the largest deviations of the 12- and 16-level compilations from their exact laws
"""
import cmath
import math
import random


def chsh_sweep(n=80):
    """The exhaustive sweep over n³ setting differences (Δ₄ = Δ₂ + Δ₃ − Δ₁): (max S, min S, an argmax)."""
    E = [math.cos(2 * math.pi * d / n) for d in range(n)]
    best, worst, arg = -10.0, 10.0, None
    for d1 in range(n):
        for d2 in range(n):
            s12, base = E[d1] + E[d2], d2 - d1
            for d3 in range(n):
                S = s12 + E[d3] - E[(base + d3) % n]
                if S > best: best, arg = S, (d1, d2, d3, (base + d3) % n)
                if S < worst: worst = S
    return best, worst, arg


def envelope(M, n, taus):
    """[(τ, |χ(θ)|, exp(−σ²θ²/2))] for the binomial distribution on 0..M (σ² = M/4) and θ = 2πτ/n."""
    out = []
    for tau in taus:
        th = 2 * math.pi * tau / n
        chi = abs(sum(math.comb(M, E) / 2 ** M * cmath.exp(1j * E * th) for E in range(M + 1)))
        out.append((tau, chi, math.exp(-(M / 4) * th * th / 2)))
    return out


def sampled_scaling(m=10000, draws=200, nph=8, seed=5):
    """The mean over `draws` samples of |Σ_i ζ^{θ_i}|²/m, θ_i uniform on 0..nph−1 (nph a power of two below 256)."""
    rng = random.Random(seed)
    z = [cmath.exp(2j * math.pi * k / nph) for k in range(nph)]
    table = bytes(b % nph for b in range(256))
    vals = []
    for _ in range(draws):
        th = rng.getrandbits(8 * m).to_bytes(m, "little").translate(table)
        s = sum(th.count(k) * z[k] for k in range(nph))
        vals.append(abs(s) ** 2 / m)
    return sum(vals) / len(vals)


# ---- the hardware compilations (22-quantum, Appendix B, the package's emulation.py) ---------------------------------
def _mm(A, B): return [[sum(A[i][k] * B[k][j] for k in range(len(B))) for j in range(len(B[0]))] for i in range(len(A))]
def _dag(A): return [[A[j][i].conjugate() for j in range(len(A))] for i in range(len(A[0]))]
def _kron(A, B): return [[A[i // len(B)][j // len(B[0])] * B[i % len(B)][j % len(B[0])] for j in range(len(A[0]) * len(B[0]))]
                         for i in range(len(A) * len(B))]
def _eye(n): return [[complex(i == j) for j in range(n)] for i in range(n)]
def _dev(A, B): return max(abs(a - b) for ra, rb in zip(A, B) for a, b in zip(ra, rb))
def _apply(U, v): return [sum(U[i][k] * v[k] for k in range(len(v))) for i in range(len(U))]
def _normed(v):
    r = math.sqrt(sum(abs(x) ** 2 for x in v))
    return [x / r for x in v]


def emulation():
    """The largest deviation of each law from its exact value: {"M1u", "M1b", "M2", "M3", "M4", "M5u", "M5"}."""
    dev = {}
    F4 = [[1j ** (r * l) / 2 for l in range(4)] for r in range(4)]
    U = _kron(_eye(3), F4)                                        # the 12-level forced basis, |α, ℓ⟩
    Ud = _dag(U)
    dev["M1u"] = _dev(_mm(U, Ud), _eye(12))
    d = 0.0
    for r in range(4):
        for al in range(3):
            v = [0j] * 12
            for l in range(4): v[al * 4 + l] = 1j ** (r * l) / 2
            e = [complex(i == al * 4 + r) for i in range(12)]
            d = max(d, max(abs(a - b) for a, b in zip(_apply(Ud, v), e)))
    dev["M1b"] = d
    z12 = cmath.exp(2j * math.pi / 12)
    d = 0.0
    for s in range(12):                                           # winding states: the channel s mod 4, uniform outcomes
        psi = _normed([z12 ** (s * (al + 3 * l)) for al in range(3) for l in range(4)])
        pr = [abs(x) ** 2 for x in _apply(Ud, psi)]
        d = max(d, max(abs(pr[al * 4 + r] - ((1 / 3) if (r - s) % 4 == 0 else 0.0)) for al in range(3) for r in range(4)))
    dev["M2"] = d
    om, d = cmath.exp(2j * math.pi / 3), 0.0
    for s in (0, 1, 5):                                           # doublets: the three-outcome interference law
        for j in range(12):
            lam = z12 ** j
            psi = _normed([z12 ** (s * (al + 3 * l)) + lam * z12 ** ((s + 4) * (al + 3 * l)) for al in range(3) for l in range(4)])
            pr = [abs(x) ** 2 for x in _apply(Ud, psi)]
            d = max(d, max(abs(pr[al * 4 + s % 4] - abs(1 + lam * om ** al) ** 2 / 6) for al in range(3)))
    dev["M3"] = d
    h = 1 / math.sqrt(2)
    H, I2 = [[h, h], [h, -h]], _eye(2)
    CS = [[complex(i == j) * (1j if i == 3 else 1) for j in range(4)] for i in range(4)]
    SWAP = [[1, 0, 0, 0], [0, 0, 1, 0], [0, 1, 0, 0], [0, 0, 0, 1]]
    dev["M4"] = _dev(_mm(_mm(_mm(SWAP, _kron(I2, H)), CS), _kron(H, I2)), F4)
    F8 = [[cmath.exp(2j * math.pi * r * l / 8) / math.sqrt(8) for l in range(8)] for r in range(8)]
    U16 = _kron(_eye(2), F8)
    U16d = _dag(U16)
    dev["M5u"] = _dev(_mm(U16, U16d), _eye(16))
    z16, d = cmath.exp(2j * math.pi / 16), 0.0
    for s in (0, 3, 9):                                           # the σ_x doublet law over the π/40 sweep
        for j in range(80):
            lam = cmath.exp(2j * math.pi * 8 * j / 640)
            psi = _normed([z16 ** (s * (al + 2 * l)) + lam * z16 ** ((s + 8) * (al + 2 * l)) for al in range(2) for l in range(8)])
            pr = [abs(x) ** 2 for x in _apply(U16d, psi)]
            d = max(d, abs(pr[s % 8] - abs(1 + lam) ** 2 / 4), abs(pr[8 + s % 8] - abs(1 - lam) ** 2 / 4))
    dev["M5"] = d
    return dev
