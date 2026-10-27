"""frc.chart_gravity — the chart readings of 21-gravity (the chart theme; 10 October 2026).

The floating-point side of 21-gravity's rows, every numeral anchored to the ledger's scale import (frc/chart.py: ln Ω =
283.5, Ω = 1.3 × 10¹²³, the entailed H₀ = 67.4): the lattice Green's function on ℤ³ against 1/4πr, the
strong field (the exact profile, the photon sphere and the shadow, the ringdown, the innermost stable orbit and the
accretion efficiency, the operational cut and the capacity ratio, the echo factor, the Sgr A* and M87* angles), the floor
and the crossover (the root η against e^{−√x}, the crossover's slopes, the Tully–Fisher deep limit, the RAR identity,
the discriminant against the simple interpolant), the turnaround radius, the preferred-frame scale, the gravitomagnetic
dipole's Lense–Thirring rate and the ergosurface, the radiative dispersion and the helicity, the two readings of the nonlinear completion, the
2PN periastron excess of PSR J0737−3039, the tilt and the scale-path probe, the seeded Kuramoto chain of the
flux-conservation lemma, and the ringdown of the exponential reading (the eikonal pair and the ℓ = 2 mode of the chart's wave
operator by third-order WKB along the tortoise coordinate, a truncated power series doing the derivatives; 00:E14). Floats are allowed here and nowhere in the exact tiers; the standard library only. The Lean
side is lean/FrcMathlib/Theme/Strong.lean (Mathlib, the brackets). Every comparison with measured data is [data].
"""
import cmath
import math
import random

from frc import chart as C
from frc import relaxation as RX

LN_OMEGA = float(C.LN_OMEGA)                       # the ledger's ln Ω (00:A7, 00:L8)
OMEGA = math.exp(LN_OMEGA)                         # Ω on the chart, 1.3 × 10¹²³
G_SI, MSUN, MPC_M = 6.674e-11, 1.989e30, float(C.MPC_KM) * 1e3
A0_FIT, A0_SYST = float(C.A0_FIT[0]), float(C.A0_FIT[1])
PI, E, TWO_E = math.pi, math.e, 2 * math.e                 # the chart's constants, for the ledger file (which carries no float)


# ---- the registered relaxation against its Kuramoto chart (21:C28, [chart] readout) ------------------------------------------------
def window_relaxation(N=60, B=81, mu0=None):
    """One link on C_N relaxing under the re-registration rule (frc.relaxation.relax) with the readout replaced by the grid
    floor ⌊B |sin(2πμ/N)|⌋ [chart] (the readout map is declared on the real-quadratic strata only): the exact accumulator
    against the Kuramoto flow sampled at the quanta (Σ 1/sin over the levels passed) and the continuous flow
    (N/2π) ln(tan(πμ₀/N)/tan(πμ/N)). Returns (the alignment chronon, the largest lag against the sampled flow, the largest
    lag against the continuous flow, the pulses fired)."""
    mu0 = N // 2 - 1 if mu0 is None else mu0
    M = {mu: (int(B * abs(math.sin(2 * math.pi * mu / N))) if mu % (N // 2) else 0) for mu in range(-(N // 2), N // 2 + 1)}
    traj, word, _ = RX.relax(N, mu0, M, B=B, chronons=20 * N)
    first = {}
    for t, mu in enumerate(traj): first.setdefault(mu, t)
    sampled = lambda mu: sum(1 / math.sin(2 * math.pi * k / N) for k in range(mu + 1, mu0 + 1))
    flow = lambda mu: (N / (2 * math.pi)) * math.log(math.tan(math.pi * mu0 / N) / math.tan(math.pi * mu / N))
    lag_s = max(abs(first[mu] - sampled(mu)) for mu in range(1, mu0))
    lag_f = max(abs(first[mu] - flow(mu)) for mu in range(1, mu0))
    return first[0], lag_s, lag_f, sum(word[:first[0]])


def count_vs_sine(N, B=81):
    """[chart] the largest |M(μ) − B sin(2πμ/N)| over the mismatches of C_N, the window counts of frc.relaxation.current_counts
    against the sine: the readout's grid bound times B plus the allocation's half unit."""
    M = RX.current_counts(N, B)
    return max(abs(M[mu] - B * abs(math.sin(2 * math.pi * mu / N))) for mu in range(0, N // 2 + 1))


# ---- the Newtonian layer: the lattice Green's function (21:C2) ---------------------------------------------
def lattice_green(r, M=300):
    """G(r, 0, 0) on ℤ³, the exact Montroll kernel with the k₁ integral done in closed form:
    G = (1/4π²) ∫∫ ρ^r / √(a² − 4) dk₂ dk₃ with a = 6 − 2cos k₂ − 2cos k₃ and ρ = (a − √(a² − 4))/2; the 1/(2|k|)
    singularity at the origin is subtracted and integrated exactly (∫_{[−π,π]²} dk/|k| = 8π ln(1 + √2)); the midpoint rule
    on M² cells. G(0) = 0.252731 (Watson) and G(1) = G(0) − 1/6 at M = 300 to six places."""
    h = 2 * math.pi / M
    tot = 0.0
    for i in range(M):
        k2 = -math.pi + (i + 0.5) * h
        c2 = math.cos(k2)
        for j in range(M):
            k3 = -math.pi + (j + 0.5) * h
            a = 6 - 2 * c2 - 2 * math.cos(k3)
            s = math.sqrt(a * a - 4)
            tot += ((a - s) / 2) ** r / s - 1 / (2 * math.hypot(k2, k3))
    return (tot * h * h + 4 * math.pi * math.log(1 + math.sqrt(2))) / (4 * math.pi * math.pi)


def green_ratios(rs=(3, 5, 8, 12), M=300):
    """4πr G(r) against 1: the Newtonian limit 1 + O(r⁻²) of the lattice potential (1.038, 1.012, 1.004, 1.002)."""
    return {r: 4 * math.pi * r * lattice_green(r, M) for r in rs}


def green_slope(rs=(5, 8, 12), M=300):
    """The log–log slope of G(r) over r ≥ 5, against −1."""
    xs = [math.log(r) for r in rs]; ys = [math.log(lattice_green(r, M)) for r in rs]
    return loglog_fit(xs, ys)


def loglog_fit(xs, ys):
    """The least-squares slope of ys against xs."""
    n = len(xs); mx = sum(xs) / n; my = sum(ys) / n
    return sum((x - mx) * (y - my) for x, y in zip(xs, ys)) / sum((x - mx) ** 2 for x in xs)


# ---- the strong field (21:C12, C13, P1, P7) ----------------------------------------------------------------------------
def u_exact(r, Gm=1.0, n=4000):
    """u(r) = ∫_r^∞ arcsin(Gm/s²) ds = r ∫_0^1 arcsin(a x²)/x² dx with a = Gm/r², by Simpson on (0, 1]."""
    a = Gm / r / r

    def f(x):
        return a if x == 0 else math.asin(min(1.0, a * x * x)) / (x * x)
    h = 1.0 / n
    s = f(0) + f(1) + sum((4 if i % 2 else 2) * f(i * h) for i in range(1, n))
    return r * s * h / 3


def deflection(Gm=1.0, b=1.0, Z=2000.0, n=200000):
    """The Fermat deflection in the index n = 1 + 2Gm/(c² r): α = ∫ −∂_b [2Gm/√(b² + z²)] dz = 2Gm b ∫ dz/(b² + z²)^{3/2}
    over the line, by Simpson on [−Z, Z] with the tail 2 · 2Gm b/(Z²) … added as 4Gm/b · (1 − Z/√(b² + Z²)); against 4Gm/b."""
    f = lambda z: 2 * Gm * b / (b * b + z * z) ** 1.5
    h = 2 * Z / n
    s = f(-Z) + f(Z) + sum((4 if i % 2 else 2) * f(-Z + i * h) for i in range(1, n))
    body = s * h / 3
    tail = 4 * Gm / b * (1 - Z / math.sqrt(b * b + Z * Z))
    return body + tail, 4 * Gm / b


def horizonless(Gm=1.0, n=4000):
    """The interior of the exact profile: below the slip core r_* = √(Gm) the integrand arcsin(Gm/s²) saturates at π/2,
    so u(r) = u(r_*) + (π/2)(r_* − r) on [0, r_*] and u(0) = u(r_*) + (π/2) r_* is finite; the clock-rate factor e^{−2u}
    is bounded below by e^{−2u(0)} > 0 everywhere — no horizon, no singularity (21:X3). With arcsin x ≤ (π/2) x on [0, 1],
    u(r_*) ≤ (π/2) r_*, so u(0) ≤ π r_*. Returns (u(0), e^{−2u(0)}, the bound π r_*, the minimum of e^{−2u} on a grid)."""
    rs = math.sqrt(Gm)
    u_star = u_exact(rs, Gm, n)
    u0 = u_star + math.pi / 2 * rs
    grid = [k * rs / 50 for k in range(0, 51)] + [rs * (1 + k / 10) for k in range(1, 101)]
    def u(r): return u_star + math.pi / 2 * (rs - r) if r <= rs else u_exact(r, Gm, n)
    low = min(math.exp(-2 * u(r)) for r in grid)
    return u0, math.exp(-2 * u0), math.pi * rs, low


def curvature_import(lam=float(C.LAMBDA_FIT), lp=float(C.PLANCK_LENGTH)):
    """The scale import read as the curvature of the closed chart (21:X1): Λ ℓ_P², the measured curvature in Planck units;
    the de Sitter entropy S = 3π/(Λ ℓ_P²) and Ω = 4S + 1 with ln Ω against the ledger's 283.5; log₁₀(Λ ℓ_P² · Ω), which is
    log₁₀ 12π = 1.58 (Λ ∼ 1/Ω within two decades, the constant the chart's); the 122 orders as log₁₀ S and −log₁₀(Λ ℓ_P²);
    the chronon τ/t_P = (√π/2)/√S; and the horizon r_H/ℓ_P against √Ω/(2√π)."""
    lam_pl = lam * lp * lp
    S = 3 * math.pi / lam_pl
    omega = 4 * S + 1
    return {"lambda_planck": lam_pl, "S": S, "omega": omega, "ln_omega": math.log(omega),
            "log10_lambda_omega": math.log10(lam_pl * omega), "log10_12pi": math.log10(12 * math.pi),
            "orders_S": math.log10(S), "orders_lambda": -math.log10(lam_pl),
            "chronon": math.sqrt(math.pi) / 2 / math.sqrt(S), "horizon": math.sqrt(S / math.pi),
            "horizon_ratio": math.sqrt(S / math.pi) / (math.sqrt(omega) / (2 * math.sqrt(math.pi)))}


def profile_series(r, Gm=1.0):
    """The exact profile's series Gm/r (1 + (Gm/r²)²/30 + (Gm/r²)⁴/120) against the quadrature u_exact(r)."""
    a = Gm / r / r
    return Gm / r * (1 + a * a / 30 + a ** 4 / 120), u_exact(r, Gm)


def photon_sphere(Gm=1.0):
    """The minimum of b(r) = r e^{2u(r)} on a grid about 2Gm: r_ph and b_c against 2Gm and 2e·Gm."""
    best = None
    r = 1.6 * Gm
    while r <= 2.4 * Gm:
        b = r * math.exp(2 * u_exact(r, Gm))
        if best is None or b < best[1]: best = (r, b)
        r += 0.01 * Gm
    return best


def shadow_ringdown():
    """δ = 2e/(3√3) − 1 (the shadow, +4.63 %) and 3√3/(2e) − 1 (the ringdown, −4.42 %)."""
    return 2 * math.e / (3 * math.sqrt(3)) - 1, 3 * math.sqrt(3) / (2 * math.e) - 1


def angular_shadows():
    """The Sgr A* and M87* shadows in μas: GR (3√3) against the exponential zone (2e)."""
    Msun_km = 1.47662
    out = {}
    for name, M, D_kpc in (("Sgr A*", 4.297e6, 8.277), ("M87*", 6.5e9, 16.8e3)):
        theta_g = M * Msun_km * 1e3 / (D_kpc * 3.0857e19) * 206264.806e6
        out[name] = (2 * 3 * math.sqrt(3) * theta_g, 2 * 2 * math.e * theta_g)
    return out


def isco():
    """The exponential metric's circular orbits (G = m = 1): W = e^{−2/r} + L² e^{−4/r}/r²; marginal stability at
    r = 3 + √5 with the circular L²; the energy E = √W there and the efficiency 1 − E."""
    def W(r, L2): return math.exp(-2 / r) + L2 * math.exp(-4 / r) / r ** 2

    def L2_of(r, h=1e-4):
        dA = (math.exp(-2 / (r + h)) - math.exp(-2 / (r - h))) / (2 * h)
        dB = (math.exp(-4 / (r + h)) / (r + h) ** 2 - math.exp(-4 / (r - h)) / (r - h) ** 2) / (2 * h)
        return -dA / dB

    def Wrr(r, L2, h=1e-4): return (W(r + h, L2) - 2 * W(r, L2) + W(r - h, L2)) / h ** 2
    r = 3 + math.sqrt(5)
    L2 = L2_of(r); E = math.sqrt(W(r, L2)); L = math.sqrt(L2)
    mom = L * math.exp(-4 / r) / (E * r ** 2)
    return {"r": r, "E": E, "eff": 1 - E, "eff_schw": 1 - math.sqrt(8 / 9), "Wrr": Wrr(r, L2), "ratio": mom * 6 * math.sqrt(6)}


def operational_cut(M):
    """The slip core r_* = √M, the cut r_f = 2M/ln Ω (G = c = 1, M in Planck masses): r_* < r_f < M iff M > (ln Ω/2)²;
    the round-trip factor e^{2u(r_f)} = Ω; the capacity ratio 1/ln²Ω; the echo factor Ω/ln²Ω."""
    rs, rf = math.sqrt(M), 2 * M / LN_OMEGA
    return {"r_star": rs, "r_f": rf, "ordered": rs < rf < M, "threshold": (LN_OMEGA / 2) ** 2,
            "round_trip": math.exp(2 * (M / rf)), "capacity_ratio": 1 / LN_OMEGA ** 2, "echo": OMEGA / LN_OMEGA ** 2}


# ---- the floor, the crossover and the running (21:C4, C19, P3, P4, P5, X2) ---------------------------------------------
def floor(h0_kms=float(C.H0_ENTAILED)):
    """a₀ = cH₀/2π in m s⁻² (the chart theme's reading, 00:L1)."""
    return C.floor(h0_kms)


def ratio(x):
    """g_obs/g_N = 1/(1 − e^{−√x}), x = g_N/a₀."""
    return 1.0 / (1.0 - math.exp(-math.sqrt(x)))


def loglog_slope(x, h=1e-5):
    f1 = math.log(x * ratio(x)); f2 = math.log(x * math.exp(h) * ratio(x * math.exp(h)))
    return (f2 - f1) / h


def eta_reach(s, a):
    """The exact root η = (1 − √(1 − w²))/w, w = 1 − s, raised to a, against the reading e^{−√x}, √x = a√(2s)."""
    w = 1.0 - s
    eta = (1 - math.sqrt(1 - w * w)) / w
    return eta ** a, math.exp(-a * math.sqrt(2 * s))


def interpolant_discriminant(x=5.0):
    """The crossover 1/(1 − e^{−√x}) against the simple interpolant ν(x) = ½ + √(¼ + 1/x) at g_N = 5a₀: the two approaches
    to Newton differ by 0.051, the paper's discriminant (the Mathlib brackets 1.11966 < ratio < 1.11967,
    1.17082 < ν < 1.17083)."""
    simple = 0.5 + math.sqrt(0.25 + 1.0 / x)
    return ratio(x), simple, simple - ratio(x)


def tully_fisher(M_solar, radii_kpc=(30.0, 100.0, 300.0)):
    """The rotation curve of a point mass on the radial acceleration relation, v(r) = √(g_obs r) with
    g_obs = g_N/(1 − e^{−√(g_N/a₀)}) and g_N = GM/r², against the deep limit's asymptote (GMa₀)^{1/4}: returns the
    asymptote in m s⁻¹ and, per radius, (r, v(r), v(r)⁴/GMa₀) — the ratio above 1, falling to it as r grows."""
    GM, a0 = G_SI * M_solar * MSUN, A0_FIT
    curve = []
    for r_kpc in radii_kpc:
        r = r_kpc * 1e-3 * MPC_M
        gN = GM / r ** 2
        v = math.sqrt(gN * ratio(gN / a0) * r)
        curve.append((r_kpc, v, v ** 4 / (GM * a0)))
    return (GM * a0) ** 0.25, curve


def turnaround(mass_solar=5e12, h0_kms=70.0):
    """(Gm/H²)^{1/3} in Mpc for the Local Group."""
    H = h0_kms * 1e3 / MPC_M
    return (G_SI * mass_solar * MSUN / H ** 2) ** (1 / 3) / MPC_M


def redshift_linear(u):
    """1 − e^{−u} against u: the linear reading of the clock rate, |1 − e^{−u} − u| ≤ u²."""
    return abs(1 - math.exp(-u) - u) <= u * u


def running_shift(z, omega_l):
    """The Tully–Fisher zero-point at redshift z under the running floor, E(z)^{1/4} (the chart theme's reading, 00:P1)."""
    return C.tully_fisher_shift(z, omega_l)


def expansion_rate(z, omega_l):
    """E(z) = H(z)/H₀ on the rival chart (flat ΛCDM), the chart theme's reading."""
    return C.e_of_z(z, omega_l)


# ---- the preferred-frame scale, the dragging and the ergosurface (21:C10, C17, P2) --------------------------------------
def preferred_frame_scale():
    """1/√Ω on the chart: 3 × 10⁻⁶²."""
    return math.exp(-LN_OMEGA / 2)


def lense_thirring(J, r):
    """The Lense–Thirring form 2J/r³ (G = c = 1), the on-axis dragging rate; see dragging_field for its derivation."""
    return 2 * J / r ** 3


def dragging_field(J=0.3, r=10.0, h=1e-3, probe=(3.0, 2.0, 4.0)):
    """The gravitomagnetic dipole of the spin J ẑ, A(x) = J × x/|x|³ (the quarter-turn dual of the monopole, 21:C17):
    off the source each component is harmonic and the field is divergence-free (second central differences at the probe
    point), and its curl is J(3(ẑ·r̂)r̂ − ẑ)/r³ — on the axis 2J/r³ (the Lense–Thirring rate), on the equator −J/r³.
    Returns the on-axis and equatorial curl components along ẑ, the largest |∇²A_i| and |∇·A| at the probe."""
    def A(x, y, z):
        d = (x * x + y * y + z * z) ** 1.5
        return (-J * y / d, J * x / d, 0.0)

    def curl(x, y, z):
        dAz_dy = (A(x, y + h, z)[2] - A(x, y - h, z)[2]) / (2 * h); dAy_dz = (A(x, y, z + h)[1] - A(x, y, z - h)[1]) / (2 * h)
        dAx_dz = (A(x, y, z + h)[0] - A(x, y, z - h)[0]) / (2 * h); dAz_dx = (A(x + h, y, z)[2] - A(x - h, y, z)[2]) / (2 * h)
        dAy_dx = (A(x + h, y, z)[1] - A(x - h, y, z)[1]) / (2 * h); dAx_dy = (A(x, y + h, z)[0] - A(x, y - h, z)[0]) / (2 * h)
        return (dAz_dy - dAy_dz, dAx_dz - dAz_dx, dAy_dx - dAx_dy)

    x, y, z = probe
    lap = max(abs((A(x + h, y, z)[i] + A(x - h, y, z)[i] + A(x, y + h, z)[i] + A(x, y - h, z)[i] + A(x, y, z + h)[i] + A(x, y, z - h)[i] - 6 * A(x, y, z)[i]) / h ** 2) for i in range(3))
    div = abs((A(x + h, y, z)[0] - A(x - h, y, z)[0] + A(x, y + h, z)[1] - A(x, y - h, z)[1] + A(x, y, z + h)[2] - A(x, y, z - h)[2]) / (2 * h))
    scale = max(abs(a) for a in A(x, y, z)) / (x * x + y * y + z * z)      # |A|/r²: the size of the second derivatives
    return {"axis": curl(0.0, 0.0, r)[2], "equator": curl(r, 0.0, 0.0)[2], "laplacian": lap / scale, "divergence": div / scale,
            "transverse": max(abs(curl(0.0, 0.0, r)[0]), abs(curl(0.0, 0.0, r)[1]))}


def ergosurface(a):
    """The outer root of e^{−4/r} = 4a²/r⁴ (equatorial, G = c = M = 1), the O(a²) ergosurface of the horizonless body."""
    f = lambda r: math.exp(-4.0 / r) - 4 * a * a / r ** 4
    prev, roots, r = None, [], 0.05
    while r < 8.0:
        v = f(r)
        if prev is not None and prev[1] * v < 0:
            lo, hi = prev[0], r
            for _ in range(60):
                mid = 0.5 * (lo + hi)
                if f(lo) * f(mid) <= 0: hi = mid
                else: lo = mid
            roots.append(0.5 * (lo + hi))
        prev = (r, v); r += 0.002
    return max(roots) if roots else float("nan")


# ---- the radiative sector (21:C15) ------------------------------------------------------------------------------------------
def dispersion(kvec):
    """ω² = Σ 4 sin²(k_i/2) on the cubic lattice (κ = χ = 1)."""
    return sum(4 * math.sin(k / 2) ** 2 for k in kvec)


def group_velocity(k, h=1e-6):
    w = math.sqrt(dispersion((k, 0, 0)))
    return (math.sqrt(dispersion((k + h, 0, 0))) - w) / h


def helicity_angle(deg):
    """Rotating the field about k by ψ rotates (h₊, h×) by 2ψ: spin two."""
    psi = math.radians(deg); c, s = math.cos(psi), math.sin(psi)
    R = [[c, -s, 0], [s, c, 0], [0, 0, 1]]
    hp = [[1 / math.sqrt(2), 0, 0], [0, -1 / math.sqrt(2), 0], [0, 0, 0]]
    hx = [[0, 1 / math.sqrt(2), 0], [1 / math.sqrt(2), 0, 0], [0, 0, 0]]
    mm = lambda A, B: [[sum(A[i][k] * B[k][j] for k in range(3)) for j in range(3)] for i in range(3)]
    RT = [[R[j][i] for j in range(3)] for i in range(3)]
    aR = lambda M: mm(R, mm(M, RT))
    dot = lambda A, B: sum(A[i][j] * B[i][j] for i in range(3) for j in range(3))
    M = [[dot(hp, aR(hp)), dot(hp, aR(hx))], [dot(hx, aR(hp)), dot(hx, aR(hx))]]
    return math.degrees(math.atan2(M[1][0], M[0][0]))


# ---- the nonlinear completion's two readings (21:C11) ------------------------------------------------------------------------
def schwarzschild_as_exponential(U):
    """g₀₀ of the isotropic Schwarzschild form equals e^{−2ψ} with ψ = 2 artanh(U/2); the exponential reading composes,
    e^{−(a+b)} = e^{−a}e^{−b}, the Schwarzschild reading f(x) = (1 − x/2)/(1 + x/2) does not."""
    psi = 2 * math.atanh(U / 2)
    schw = ((1 - U / 2) / (1 + U / 2)) ** 2
    return abs(math.exp(-2 * psi) - schw)


def composition_violation(a, b):
    f = lambda x: (1 - x / 2) / (1 + x / 2)
    return abs(math.exp(-(a + b)) - math.exp(-a) * math.exp(-b)), abs(f(a + b) - f(a) * f(b))


def laplacian_psi(r, Gm=1.0, h=1e-3):
    """The Laplacian of ψ = Gm/r + (Gm/r)³/12 is nonzero (self-sourced), that of u = Gm/r vanishes."""
    psi = lambda s: Gm / s + (Gm / s) ** 3 / 12
    d = lambda s: (psi(s + h) - psi(s - h)) / (2 * h)
    return ((r + h) ** 2 * d(r + h) - (r - h) ** 2 * d(r - h)) / (2 * h) / r ** 2


def sine_model_flux(N=9, m0=4.0, iters=4000, rate=0.15, m1=2.0):
    """The static sine-coupled model on [0, N)³ with Dirichlet boundary: the flux through boxes about the source equals
    the demand (the nonlinear Gauss law), the deviation from the linear model scales as the cube of the source, and
    with a second source m1 two sites away the flux through the box enclosing both equals m0 + m1 (the two-source cut flux).
    Returns (the one-source fluxes at R = 1, 2, 3, the scaling power, the two-source flux)."""
    idx = lambda x, y, z: (x * N + y) * N + z
    V = N ** 3
    interior = [(x, y, z) for x in range(1, N - 1) for y in range(1, N - 1) for z in range(1, N - 1)]
    nb = {idx(x, y, z): [idx(x + 1, y, z), idx(x - 1, y, z), idx(x, y + 1, z), idx(x, y - 1, z), idx(x, y, z + 1), idx(x, y, z - 1)]
          for (x, y, z) in interior}

    def solve(sources, sine=True):
        u = [0.0] * V; m = [0.0] * V
        for pos, mass in sources: m[idx(*pos)] = mass
        for _ in range(iters):
            drive = {}
            for i, ns in nb.items():
                s = sum((math.sin(u[j] - u[i]) if sine else (u[j] - u[i])) for j in ns) + m[i]
                drive[i] = s
            for i, s in drive.items(): u[i] += rate * s
        return u

    def flux_box(u, c, R, sine=True):
        F = 0.0
        for x in range(c[0] - R, c[0] + R + 1):
            for y in range(c[1] - R, c[1] + R + 1):
                for z in range(c[2] - R, c[2] + R + 1):
                    if max(abs(x - c[0]), abs(y - c[1]), abs(z - c[2])) != R: continue
                    i = idx(x, y, z)
                    for (dx, dy, dz) in ((1, 0, 0), (-1, 0, 0), (0, 1, 0), (0, -1, 0), (0, 0, 1), (0, 0, -1)):
                        xo, yo, zo = x + dx, y + dy, z + dz
                        if max(abs(xo - c[0]), abs(yo - c[1]), abs(zo - c[2])) > R:
                            d = u[i] - u[idx(xo, yo, zo)]
                            F += math.sin(d) if sine else d
        return F
    c = (N // 2, N // 2, N // 2)
    u1 = solve([(c, m0)])
    fluxes = [flux_box(u1, c, R) for R in (1, 2, 3)]
    devs = []
    for mm in (1.0, 2.0):
        us, ul = solve([(c, mm)]), solve([(c, mm)], sine=False)
        devs.append(max(abs(a - b) for a, b in zip(us, ul)))
    power = math.log(devs[1] / devs[0]) / math.log(2.0)
    u2 = solve([((c[0] - 1, c[1], c[2]), m0), ((c[0] + 1, c[1], c[2]), m1)])
    return fluxes, power, flux_box(u2, c, 2)


# ---- the 2PN periastron excess (21:P6) ----------------------------------------------------------------------------------------
def periastron_excess(M_solar=2.5871, Pb=8834.535, ecc=0.0878):
    """δ(Δω)/Δω_1PN = U_p (2 + e²/2)/6 for PSR J0737−3039, with U_p = GM/(c² p) on the semi-latus rectum."""
    M = M_solar * MSUN; c = float(C.C_LIGHT)
    a = (G_SI * M * Pb ** 2 / (4 * math.pi ** 2)) ** (1.0 / 3.0)
    p_slr = a * (1 - ecc ** 2)
    Up = G_SI * M / (c ** 2 * p_slr)
    return Up, Up * (2 + ecc ** 2 / 2) / 6.0


# ---- the primordial tilt (21:C18, P8) ---------------------------------------------------------------------------------------
def tilt():
    return C.tilt()


def tilt_sensitivity():
    """The tilt's sensitivity to the count: d(ln ln Ω) per factor two in S is ln 2/ln Ω = 0.244 % at 283.5 (21:P8)."""
    return math.log(2.0) / LN_OMEGA


def scale_path_probe(K):
    """K² λ₁ with λ₁ = 4 sin²(π/(2(K + 1))), the first eigenvalue of the finite scale-path Laplacian, against π²."""
    return K * K * 4 * math.sin(math.pi / (2 * (K + 1))) ** 2


# ---- the flux-conservation chain (21:C19's lemma) ------------------------------------------------------------------------------
def kuramoto_chain(noise, M=20, dt=0.05, T=120_000, burn=40_000, b=0.3, seed=3):
    """Site 0 driven by the torque b, site M pinned: the time-averaged transport through every link equals b, with or
    without the ambient noise (seeded). Returns (mean flux, max deviation)."""
    rng = random.Random(seed)
    th = [0.0] * (M + 1); J = [0.0] * M
    sq = math.sqrt(dt)
    for step in range(T):
        flux = [math.sin(-(th[i + 1] - th[i])) for i in range(M)]
        dth = [0.0] * (M + 1)
        for i in range(M):
            dth[i] -= flux[i]; dth[i + 1] += flux[i]
        dth[0] += b
        for i in range(M):
            eta = rng.gauss(0, noise) / sq if (noise and 0 < i < M) else 0.0
            th[i] += dt * (dth[i] + eta)
        th[M] = 0.0
        if step >= burn:
            for i in range(M): J[i] += flux[i] * dt
    Jbar = [j / ((T - burn) * dt) for j in J]
    mean = sum(Jbar) / M
    return mean, max(abs(j - b) for j in Jbar)


# ---- the apsidal bound on the physical Carrier (38:C13) ---------------------------------------------------------------------
def apsidal_bound(ln_omega=LN_OMEGA, mercury=8.0e-8):
    """The bound κ/S < 1/(√Ω + 1) on the physical Carrier (ln Ω = 283.5) in decades, against Mercury's apsidal fraction
    per revolution (43″ per century over 415 revolutions: 8.0 × 10⁻⁸ [data]): the bound is 10⁻⁶¹·⁶ and Mercury sits
    54 orders above it, so no hosted Subject registers an observed precession (38:C13). No quantity above Ω is formed:
    the gap is read in the fraction, not in the square of the shell that would carry it."""
    log10_omega = ln_omega / math.log(10)
    log10_bound = -log10_omega / 2
    log10_mercury = math.log10(mercury)
    return {"log10_bound": log10_bound, "log10_mercury": log10_mercury, "orders_above": log10_mercury - log10_bound,
            "log10_omega": log10_omega}


# ---- the ringdown of the exponential reading: the eikonal pair and the phase mode (00:E14; 16 October 2026) ----------
class Series:
    """A truncated power series Σ c_k t^k in floats (order N): the derivatives of a composition read as k! c_k. Used for
    the tortoise coordinate s (ds = m dr) of a static spherical chart: r(s) about a point and a potential V(r(s))."""
    N = 8

    def __init__(self, c):
        self.c = (list(map(float, c)) + [0.0] * self.N)[:self.N]

    @classmethod
    def const(cls, x): return cls([x])

    @classmethod
    def var(cls, x0): return cls([x0, 1.0])

    def __add__(self, o):
        o = o if isinstance(o, Series) else Series.const(o)
        return Series([a + b for a, b in zip(self.c, o.c)])
    __radd__ = __add__

    def __neg__(self): return Series([-a for a in self.c])

    def __sub__(self, o): return self + (-(o if isinstance(o, Series) else Series.const(o)))

    def __rsub__(self, o): return Series.const(o) - self

    def __mul__(self, o):
        if not isinstance(o, Series): return Series([a * o for a in self.c])
        out = [0.0] * self.N
        for i, a in enumerate(self.c):
            if a == 0.0: continue
            for j in range(self.N - i): out[i + j] += a * o.c[j]
        return Series(out)
    __rmul__ = __mul__

    def inv(self):
        """1/f for f with f(0) ≠ 0, by the recurrence b_0 = 1/a_0, b_n = −(Σ_{k≥1} a_k b_{n−k})/a_0."""
        a = self.c; b = [0.0] * self.N; b[0] = 1.0 / a[0]
        for n in range(1, self.N): b[n] = -sum(a[k] * b[n - k] for k in range(1, n + 1)) / a[0]
        return Series(b)

    def __truediv__(self, o): return self * (o.inv() if isinstance(o, Series) else 1.0 / o)

    def __rtruediv__(self, o): return Series.const(o) * self.inv()

    def __pow__(self, k):
        out = Series.const(1.0)
        for _ in range(k): out = out * self
        return out

    def exp(self):
        """e^f by the recurrence g' = f' g: n g_n = Σ_{k≥1} k a_k g_{n−k}."""
        a = self.c; g = [0.0] * self.N; g[0] = math.exp(a[0])
        for n in range(1, self.N): g[n] = sum(k * a[k] * g[n - k] for k in range(1, n + 1)) / n
        return Series(g)

    def deriv(self, k):
        """The k-th derivative at the expansion point, k! c_k."""
        return math.factorial(k) * self.c[k]


def tortoise_series(r0, drds):
    """r(s) about s₀ with r(s₀) = r₀ and dr/ds = drds(r): the coefficients a_{k+1} = [drds(r)]_k/(k + 1), pass by pass."""
    a = [r0] + [0.0] * (Series.N - 1)
    for k in range(Series.N - 1):
        g = drds(Series(a))
        a[k + 1] = g.c[k] / (k + 1)
    return Series(a)


def potential_derivatives(V, drds, r0):
    """V_k = d^k V/ds^k at r₀ for k = 0..6, the potential V(r) read along the tortoise coordinate."""
    return [V(tortoise_series(r0, drds)).deriv(k) for k in range(7)]


def potential_peak(V, drds, lo, hi, it=200):
    """The maximum of V along s between the radii lo and hi: the root of V₁ by bisection (V₁ changes sign once there)."""
    f = lambda r: potential_derivatives(V, drds, r)[1]
    a, b = lo, hi
    fa = f(a)
    for _ in range(it):
        m = 0.5 * (a + b); fm = f(m)
        if (fa > 0) == (fm > 0): a, fa = m, fm
        else: b = m
    return 0.5 * (a + b)


def wkb3(V, drds, lo, hi, n=0):
    """The fundamental quasinormal frequency by the third-order WKB formula of Iyer and Will [import], the potential's
    tortoise derivatives exact to the series order: (r_peak, ω) with ω² = V₀ + Λ − i(n + ½)√(−2V₂)(1 + Ω)."""
    r0 = potential_peak(V, drds, lo, hi)
    V0, V1, V2, V3, V4, V5, V6 = potential_derivatives(V, drds, r0)
    a = n + 0.5
    Lam = (1 / 8) * (V4 / V2) * (0.25 + a * a) - (1 / 288) * (V3 / V2) ** 2 * (7 + 60 * a * a)
    Om = (1 / (-2 * V2)) * ((5 / 6912) * (V3 / V2) ** 4 * (77 + 188 * a * a)
                            - (1 / 384) * (V3 ** 2 * V4 / V2 ** 3) * (51 + 100 * a * a)
                            + (1 / 2304) * (V4 / V2) ** 2 * (67 + 68 * a * a)
                            + (1 / 288) * (V3 * V5 / V2 ** 2) * (19 + 28 * a * a)
                            - (1 / 288) * (V6 / V2) * (5 + 4 * a * a))
    om2 = complex(V0 + Lam) - 1j * a * (-2 * V2) ** 0.5 * (1 + Om)
    return r0, cmath.sqrt(om2)


def exponential_drds(M=1.0):
    """dr/ds = e^{−2M/r} on the exponential reading (ds = e^{2u} dr, u = M/r)."""
    return lambda r: (-2.0 * M / r).exp()


def exponential_potential(l, M=1.0, coupling="index"):
    """The ℓ-potential on the exponential reading: the chart's wave operator's, e^{−4u}[ℓ(ℓ+1)/r² + 2M/r³ − M²/r⁴] (the wave
    equation with the all-orders index e^{2u}, the one wave operator of the chart), or the Regge–Wheeler-type coupling e^{−4u}[ℓ(ℓ+1)/r² − 6M/r³ + 3M²/r⁴] [import]."""
    L = l * (l + 1)
    if coupling == "index":
        return lambda r: (-4.0 * M / r).exp() * (L / r ** 2 + 2.0 * M / r ** 3 - M * M / r ** 4)
    return lambda r: (-4.0 * M / r).exp() * (L / r ** 2 - 6.0 * M / r ** 3 + 3.0 * M * M / r ** 4)


def schwarzschild(l, M=1.0, spin=0):
    """Schwarzschild's controls: dr/ds = f = 1 − 2M/r and V = f(ℓ(ℓ+1)/r² + 2M(1 − s²)/r³) for spin s = 0 (scalar) or 2
    (axial, the Regge–Wheeler potential)."""
    L = l * (l + 1); c = 2.0 * M * (1 - spin * spin)
    f = lambda r: 1.0 - 2.0 * M / r
    return (lambda r: f(r) * (L / r ** 2 + c / r ** 3)), f


def eikonal_pair(M=1.0):
    """The eikonal pair of the exponential reading read off the series: Ω_c² = V₀ and λ² = −V₂/(2V₀) for the potential
    e^{−4u}/r² at its peak; both equal 1/(2eM) in closed form (r_c = 2M, b_c = 2eM)."""
    V = lambda r: (-4.0 * M / r).exp() / r ** 2
    r0 = potential_peak(V, exponential_drds(M), 1.5 * M, 3.0 * M)
    V0, V1, V2 = potential_derivatives(V, exponential_drds(M), r0)[:3]
    return r0, math.sqrt(V0), math.sqrt(-V2 / (2 * V0)), 1.0 / (2 * math.e * M)


def impact_series(M=1.0):
    """h(r) = r² e^{4M/r} = b(r)² about r = 2M: h′(2M) and h″(2M) (the closed forms 0 and 2e²)."""
    h = (lambda r: r ** 2 * (4.0 * M / r).exp())(Series.var(2.0 * M))
    return h.deriv(1), h.deriv(2), 2 * math.e ** 2


def ringdown_table():
    """The ringdown numbers of 00:E14 in one table (floats here, read as Fractions by the ledger file): the eikonal pair and
    the impact function's derivatives at 2M; the WKB3 controls against Leaver's Schwarzschild ℓ = 2 modes [import]; the
    exponential reading's ℓ = 2 mode in the two couplings against the time-domain values of 21 September 2026; the eikonal
    value (ℓ + ½)/(2eM) at ℓ = 2; the (2,2,0) shifts against Kerr's 0.373672 [import] and GW250114's half-widths
    (δf̂₂₂₀ = 0.02 ± 0.02 at 90 % [data])."""
    r0, om_c, lam, closed = eikonal_pair()
    h1, h2, h2c = impact_series()
    leaver = {0: complex(0.483644, -0.096759), 2: complex(0.373672, -0.088962)}
    ctrl = {}
    for spin in (0, 2):
        V, f = schwarzschild(2, spin=spin)
        ctrl[spin] = wkb3(V, f, 2.5, 4.0)[1]
    _, mode = wkb3(exponential_potential(2), exponential_drds(), 1.5, 3.0)
    _, rw = wkb3(exponential_potential(2, coupling="rw"), exponential_drds(), 1.5, 3.0)
    td, td_rw = complex(0.464149, -0.092253), complex(0.344778, -0.085086)
    eik = 2.5 / (2 * E)
    kerr = 0.373672
    ratio = 3 * math.sqrt(3) / (2 * E)
    shifts = {"phase": td.real / kerr - 1, "eikonal": ratio - 1, "rw": td_rw.real / kerr - 1}
    half = {k: (v - 0.02) / 0.02 for k, v in shifts.items()}
    return {"r_c": r0, "omega_c": om_c, "lambda": lam, "closed": closed, "h1": h1, "h2": h2, "h2_closed": h2c, "ratio": ratio,
            "controls": ctrl, "control_error": max(abs(ctrl[s] - leaver[s]) for s in (0, 2)),
            "mode": mode, "mode_error": abs(mode - td), "rw": rw, "rw_error": abs(rw - td_rw),
            "mode_over_eikonal": mode.real / eik, "shifts": shifts, "half_widths": half}


def green_anisotropy(N=64, n=4):
    """[chart] The cubic lattice Green's function (−ΔG = δ, Δ the graph Laplacian) at x = (3n, 0, 0) and y = (n, n, n), the
    same shortest-path count 3n, from the periodic box sum G_N(x) = N⁻³ Σ_k cos(k·x)/(6 − 2 Σ cos k_i) over k ≠ 0, the box
    constant fixed by Watson's value G(0) = 1.516386/6 at the origin. Returns (4π|x|₂ G(x), 4π|y|₂ G(y), G(y)/G(x)): the first
    two near 1 (the Euclidean leading term, Lemma green), the ratio near √3 (the anisotropy at equal path count)."""
    ks = [2 * math.pi * j / N for j in range(N)]
    c = [math.cos(k) for k in ks]
    pts = ((0, 0, 0), (3 * n, 0, 0), (n, n, n))
    acc = [0.0, 0.0, 0.0]
    for i in range(N):
        for j in range(N):
            cij = c[i] + c[j]
            for l in range(N):
                if i == 0 and j == 0 and l == 0:
                    continue
                w = 1.0 / (6.0 - 2.0 * (cij + c[l]))
                for t, (x, y, z) in enumerate(pts):
                    acc[t] += w * math.cos(ks[i] * x + ks[j] * y + ks[l] * z)
    g0, gx, gy = (a / N ** 3 for a in acc)
    shift = 1.516386059151978 / 6 - g0                       # G(0) = W₃/6, Watson's integral W₃ = 1.516386…
    Gx, Gy = gx + shift, gy + shift
    return 4 * math.pi * 3 * n * Gx, 4 * math.pi * math.sqrt(3) * n * Gy, Gy / Gx
