"""frc.chart_gravity — the chart readings of 21-gravity (the chart theme; 10 October 2026).

The floating-point side of 21-gravity's rows, every numeral anchored to the ledger's scale import (frc/chart.py: ln Ω =
283.5, Ω = 1.3 × 10¹²³, the entailed H₀ = 67.4): the lattice Green's function on ℤ³ against 1/4πr, the
strong field (the exact profile, the photon sphere and the shadow, the ringdown, the innermost stable orbit and the
accretion efficiency, the operational cut and the capacity ratio, the echo factor, the Sgr A* and M87* angles), the floor
and the crossover (the root η against e^{−√x}, the crossover's slopes, the Tully–Fisher deep limit, the RAR identity,
the discriminant against the simple interpolant), the turnaround radius, the preferred-frame scale, the Lense–Thirring
rate and the ergosurface, the radiative dispersion and the helicity, the two readings of the nonlinear completion, the
2PN periastron excess of PSR J0737−3039, the tilt and the scale-path probe, and the seeded Kuramoto chain of the
flux-conservation lemma. Floats are allowed here and nowhere in the exact tiers; the standard library only. The Lean
side is lean/FrcLedger/Theme/Strong.lean (Mathlib, the brackets). Every comparison with measured data is [data].
"""
import math
import random

from frc import chart as C

LN_OMEGA = float(C.LN_OMEGA)                       # the ledger's ln Ω (00:A7, 00:L8)
OMEGA = math.exp(LN_OMEGA)                         # Ω on the chart, 1.3 × 10¹²³
G_SI, MSUN, MPC_M = 6.674e-11, 1.989e30, float(C.MPC_KM) * 1e3
A0_FIT, A0_SYST = float(C.A0_FIT[0]), float(C.A0_FIT[1])
PI, E, TWO_E = math.pi, math.e, 2 * math.e                 # the chart's constants, for the ledger file (which carries no float)


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


def tully_fisher(M_solar):
    v = (G_SI * M_solar * MSUN * A0_FIT) ** 0.25
    return v, abs(v ** 4 - G_SI * M_solar * MSUN * A0_FIT) / (G_SI * M_solar * MSUN * A0_FIT)


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
    return 2 * J / r ** 3


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


def sine_model_flux(N=9, m0=4.0, iters=4000, rate=0.15):
    """The static sine-coupled model on [0, N)³ with Dirichlet boundary: the flux through boxes about the source equals
    the demand (the nonlinear Gauss law), and the deviation from the linear model scales as the cube of the source."""
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
    return fluxes, power


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
