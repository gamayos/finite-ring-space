"""frc.chart_quantum — the quantum readings against the continuum (chart tier; ledger migration, task LM35, 7 October
2026; the exact sweep of 15 October 2026).

The chart theme holds the readings against the continuum (frc/themes.py, rank 30). This file holds the continuum
readings of 22-quantum: the CHSH sweep of the composite gate, decided exactly by certified rational brackets on
cos(πk/40) (the alternating series on the chart's π bracket) against the bracket of 2√2, and the Gaussian envelope of
the dilation dephasing, a floating-point reading the ledger file compares with a stated tolerance. The package's
sampled √m illustration and its floating-point hardware compilations (its rows retired with block V on 15 October
2026) are not carried. This file uses `math` and `cmath` only.

    cos_brackets(n)                 [(lo, hi)] with lo ≤ cos(2πk/n) ≤ hi for k < n, exact rationals, width below 10⁻¹⁸
    chsh_bound(n)                   the n³ setting triples sorted by their brackets: below 2√2 for certain, or at it
    chsh_sweep(n)                   max, min and an argmax of E(Δ₁) + E(Δ₂) + E(Δ₃) − E(Δ₂ + Δ₃ − Δ₁) in floating point
    envelope(M, n, taus)            |Σ_E p_E e^{iEθ}| against exp(−σ²θ²/2) for the binomial p_E on 0..M, θ = 2πτ/n
"""
import cmath
import math
from fractions import Fraction as Q

from frc import chart as CH


def _cos_series_bracket(x, terms=24):
    """cos x for a rational 0 ≤ x ≤ 4 by the alternating Taylor series: (lo, hi) between two consecutive partial sums
    (the terms decrease from the second on, so the sum lies between any two consecutive partial sums beyond it)."""
    sums, term = [], Q(1)
    s = Q(0)
    for j in range(terms):
        s += term
        sums.append(s)
        term = -term * x * x / ((2 * j + 1) * (2 * j + 2))
    a, b = sums[-2], sums[-1]
    return (min(a, b), max(a, b))


def cos_brackets(n=80):
    """Certified brackets on cos(2πk/n), k < n: cos is decreasing on [0, π], and cos(2π − y) = cos y folds the second
    half; π is the chart's Machin bracket, so each value is bracketed by exact rationals."""
    pi_lo, pi_hi = CH.pi_bracket()
    out = []
    for k in range(n):
        kk = k if 2 * k <= n else n - k                                      # fold: cos(2πk/n) = cos(2π(n−k)/n)
        x_lo, x_hi = 2 * kk * pi_lo / n, 2 * kk * pi_hi / n                  # 0 ≤ x ≤ π, cos decreasing
        lo = _cos_series_bracket(x_hi)[0]
        hi = _cos_series_bracket(x_lo)[1]
        out.append((lo, hi))
    return out


def chsh_bound(n=80, digits=24):
    """The n³ triples (Δ₁, Δ₂, Δ₃), Δ₄ = Δ₂ + Δ₃ − Δ₁: with S = E(Δ₁) + E(Δ₂) + E(Δ₃) − E(Δ₄) bracketed by the cosine
    brackets, widened to `digits` decimals in fixed-point integers, (below, at, over) — the number of triples whose
    bracket lies below the bracket of 2√2 for certain, those whose bracket meets it (the saturating set, decided by the
    ring identity), and those above it (none)."""
    N = 10 ** digits
    br = [(math.floor(lo * N), math.ceil(hi * N)) for lo, hi in cos_brackets(n)]
    s8_lo, s8_hi = CH.sqrt_bracket(8, digits)
    s8_lo, s8_hi = math.floor(s8_lo * N), math.ceil(s8_hi * N)
    below, at, over = 0, [], []
    for d1 in range(n):
        l1, h1 = br[d1]
        for d2 in range(n):
            l12, h12 = l1 + br[d2][0], h1 + br[d2][1]
            base = d2 - d1
            for d3 in range(n):
                d4 = (base + d3) % n
                lo = l12 + br[d3][0] - br[d4][1]
                hi = h12 + br[d3][1] - br[d4][0]
                if hi < s8_lo: below += 1
                elif lo > s8_hi: over.append((d1, d2, d3, d4))
                else: at.append((d1, d2, d3, d4))
    return below, at, over


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
