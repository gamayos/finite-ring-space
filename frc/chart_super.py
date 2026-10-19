"""frc.chart_super — the chart theme's readings of the super theme (the master's G19 and G20; 19 October 2026): the
self-dual point and the vortex line tension in floating point, the universal numbers of the transition, and the Airy
vortex-core ladder by bisection on the Sturm counts.

Floats live here and nowhere in the super theme (gate G09): frc/super.py decides every exact clause (the ring identities
in ℤ[√2], the lattice maps, the polynomial closures, Sturm's counts in Fractions), and this module reads the same objects
against the continuum — the readings of 34-super's scripts m2, m3, m4, m6 and m8 that are not finite arithmetic.
Standard library only.

    beta_star()                β* = ½ ln(1 + √2): sinh 2β* = 1, tanh β* = √2 − 1 to 10⁻¹²
    tau(beta)                  the vortex line tension τ(β) = 2β + ln tanh β; τ(β*) = 0, τ > 0 above, τ < 0 below
    dual(beta)                 the Kramers–Wannier involution sinh 2β sinh 2β̃ = 1, β* its fixed point
    universal_numbers()        the stiffness jump 2/π, the gap ratio 2π/e^γ = 3.528, the heat jump 12/(7ζ(3)) = 1.426
    airy_ladder(N, L)          E₁ (even), E₂ (odd), E₃ (even) by bisection on the float Sturm counts; ρ = (E₃ − E₂)/(E₂ − E₁)
"""
import math

# ---- declared data ---------------------------------------------------------------------------------------------------------
EULER_GAMMA = 0.5772156649015329          # the Euler–Mascheroni constant (the BCS gap ratio 2π/e^γ)
ZETA_3 = 1.2020569031595943               # Apéry's constant (the BCS heat-capacity jump 12/(7ζ(3)))
GAP_RATIO_BCS = 3.5276                    # 2Δ₀/kT_c, the established BCS number read in 34-super (m3, m4, m8)
HEAT_JUMP_BCS = 1.4261                    # ΔC/γT_c (m8)
AIRY = {"ai_prime": (1.0187929716, 3.2481975822, 4.8200992112),      # |a′_k|, the zeros of Ai′ (the even levels)
        "ai": (2.3381074105, 4.0879494441, 5.5205598281)}           # |a_k|, the zeros of Ai (the odd levels)


# ---- the self-dual point and the vortex line tension (00:G19; 34-super C5, m2, m3) ---------------------------------------
def beta_star():
    """β* = ½ ln(1 + √2), the fixed point of sinh 2β sinh 2β̃ = 1."""
    return 0.5 * math.log(1 + math.sqrt(2))


def tau(beta):
    """The Onsager interface tension, the 't Hooft-loop (vortex line) tension in the ordered phase: τ(β) = 2β + ln tanh β."""
    return 2 * beta + math.log(math.tanh(beta))


def dual(beta):
    """β̃ with sinh 2β sinh 2β̃ = 1: the Kramers–Wannier involution."""
    return math.asinh(1 / math.sinh(2 * beta)) / 2


def self_dual_readings():
    """The floating-point residuals of the self-dual point and the involution: sinh 2β* − 1, tanh β* − (√2 − 1), τ(β*),
    τ(8) − 16, dual(dual(β)) − β at β = 0.2, 0.6, 1.0, dual(β*) − β*, and dual(β* + 0.3) − β* (negative: the map swaps the
    phases)."""
    b = beta_star()
    return dict(sinh=math.sinh(2 * b) - 1, tanh=math.tanh(b) - (math.sqrt(2) - 1), tau0=tau(b), tau8=tau(8.0) - 16.0,
                involution=[dual(dual(t)) - t for t in (0.2, 0.6, 1.0)], fixed=dual(b) - b, swap=dual(b + 0.3) - b)


def fmt(x, spec):
    """format(float(x), spec): the exact tiers print through the chart (as frc.chart.show)."""
    return format(float(x), spec)


def tension_profile(steps=(0.001, 0.05, 0.2, 0.5, 1.0, 2.0)):
    """τ at β* + d for the offsets d (the paper's grid), and τ(β* − 0.05)."""
    b = beta_star()
    return [tau(b + d) for d in steps], tau(b - 0.05)


# ---- the universal numbers of the transition (34-super C6, m3, m4, m8) -------------------------------------------------------
def universal_numbers():
    """The 2-D stiffness jump K(T_c⁻) = 2/π (Nelson–Kosterlitz), the BCS gap ratio 2Δ₀/kT_c = 2π/e^γ and the BCS heat jump
    ΔC/γT_c = 12/(7ζ(3)): framed-transcendental readings, rational multiples of π, e^γ and ζ(3)."""
    return dict(jump=2 / math.pi, gap_ratio=2 * math.pi / math.exp(EULER_GAMMA), heat_jump=12 / (7 * ZETA_3))


# ---- the Airy vortex-core ladder (00:G20; 34-super D1, m6) ------------------------------------------------------------------
def _sturm(diag, off2, lam):
    """Sturm's count in floating point: the eigenvalues below lam of the tridiagonal with diagonal diag and squared
    off-diagonals off2 (a list, one per link)."""
    cnt, q = 0, None
    for k, d in enumerate(diag):
        q = d - lam - (off2[k - 1] / q if k else 0.0)
        if q == 0.0: q = -1e-300
        if q < 0: cnt += 1
    return cnt


def _kth(diag, off2, k, lo, hi, iters=80):
    """The k-th eigenvalue (k = 0 the lowest) by bisection on the count."""
    for _ in range(iters):
        mid = (lo + hi) / 2
        if _sturm(diag, off2, mid) > k: hi = mid
        else: lo = mid
    return (lo + hi) / 2


def airy_ladder(N=200, L=16):
    """The three lowest levels of the linear well V = |x| on the symmetric interval, by parity: the even operator (Neumann
    at the origin, the first link's squared coupling 2/h⁴ after the symmetrising rescaling, frc.super.even_grid) gives
    E₁ and E₃, the odd operator (Dirichlet, frc.hadrons.airy_grid) gives E₂; the ratio ρ = (E₃ − E₂)/(E₂ − E₁) against the
    equal-spacing 1 of the harmonic (CdGM) minigap. Returns (E₁, E₂, E₃, ρ) and the Airy zeros they approach."""
    h = L / (N + 1)
    even = [2 / h ** 2 + k * h for k in range(0, N + 1)]; even_off = [2 / h ** 4] + [1 / h ** 4] * (N - 1)
    odd = [2 / h ** 2 + k * h for k in range(1, N + 1)]; odd_off = [1 / h ** 4] * (N - 1)
    e1, e3 = _kth(even, even_off, 0, 0.0, 12.0), _kth(even, even_off, 1, 0.0, 12.0)
    e2 = _kth(odd, odd_off, 0, 0.0, 12.0)
    zeros = (AIRY["ai_prime"][0], AIRY["ai"][0], AIRY["ai_prime"][1])
    return (e1, e2, e3, (e3 - e2) / (e2 - e1)), zeros


def airy_ratio():
    """ρ from the Airy zeros themselves: (|a′₂| − |a₁|)/(|a₁| − |a′₁|) = 0.690."""
    a1, a2 = AIRY["ai_prime"][0], AIRY["ai_prime"][1]; b1 = AIRY["ai"][0]
    return (a2 - b1) / (b1 - a1)
