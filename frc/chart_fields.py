"""frc.chart_fields — the readings of 27-fields against the continuum (the chart theme; ledger migration, task LM35,
7 October 2026).

The chart theme holds the floats (frc/themes.py, rank 30). This file serves the continuum-comparison layer of the paper
27-fields, whose ledger file frc/ledgers/p27_fields.py decides every exact clause itself and compares these readings
with rational bounds (it converts each float exactly, with Fraction). Each function computes what one script of the
paper's validation package (src/27-fields) computes in floating point, with the same parameters: the lattice Coulomb
coefficient, the two-charge energies, the saturation profile, the low-curvature and window residues, the strong-coupling
string tensions, the Weyl integral of SU(3), the transmutation scales, the one-loop running, the winding overlaps and
the measured Koide reading. The standard library only: the lattice transforms are done by separable cosine sums.

The measured constants are declared data (DATA), one table per script, each with the script's own numerals.
"""
import math
import random
from fractions import Fraction as Q

# ---- declared data: the measured constants of each script, as the script states them ---------------------------------
DATA = {
    "o2_numbers": dict(alpha0_inv=Q("137.035999084"), alpha_MZ_inv=Q("127.951"), m_P=Q("1.220890e19"), m_p=Q("0.9382720813")),
    "weak_current": dict(G_F=Q("1.1663787e-5"), v=Q("246.21965")),
    "v_scale": dict(m_P=Q("1.220890e19"), H0=Q("1.437e-42"), v=Q("246.220"), M_W=Q("80.377"), M_Z=Q("91.1876"),
                    a2inv_MZ=Q("29.6"), alpha_s_MZ=Q("0.118"), v_ref=Q("246.21965")),
    "p6": dict(M_P=Q("1.220890e19"), M_Z=Q("91.1876"), alpha_s_MZ=Q("0.1179"), m_p=Q("0.9383")),
    "p8": dict(m_p=Q("0.938"), alpha_GUT=Q(1, 40), hbar_GeV_s=Q("6.582e-25"), year_s=Q("3.156e7"),
               M_X=(Q("1e16"), Q("1e18"), Q("1.22e19"))),
    "p9b": dict(gen1=(Q("2.2e-3"), Q("4.7e-3"), Q("0.511e-3")), gen2=(Q("1.27"), Q("0.093"), Q("0.1057")),
                gen3=(Q("172.7"), Q("4.18"), Q("1.777"))),
    "p1": dict(M_Z=Q("91.1876"), ainv_em=Q("127.951"), sin2=Q("0.23121"), alpha_s=Q("0.1179"),
               b=(Q(41, 10), Q(-19, 6), Q(-7))),
    "p7": dict(v=Q("174.0"), m_b=Q("4.18"), m_tau=Q("1.777"), M_R=(Q("1e13"), Q("1e14"), Q("1e15"), Q("1e16")),
               y=(Q(1), Q("0.3")), N=60, T=12),
    "koide": dict(m_e=Q("0.51099895"), m_mu=Q("105.6583755"), m_tau=Q("1776.86")),
}


def _f(x): return float(x)


# ---- electromagnetism: the periodic lattice Green's function (em1_prototype) -----------------------------------------
def _fold(L):
    """Wavenumbers 0..L/2 with their multiplicities in 0..L−1 (the symbol is even in each coordinate)."""
    h = L // 2
    return [(k, 1 if k == 0 or 2 * k == L else 2) for k in range(h + 1)]


def _inv_symbol(L, ks):
    c = [math.cos(2 * math.pi * k / L) for k in ks]
    n = len(ks)
    f = [[[0.0] * n for _ in range(n)] for _ in range(n)]
    for a in range(n):
        for b in range(n):
            for d in range(n):
                s = 2 * (3 - c[a] - c[b] - c[d])
                f[a][b][d] = 1.0 / s if s > 1e-12 else 0.0          # the zero mode removed (neutralising background)
    return f


def green_points(L, pts):
    """φ(x) = (1/L³) Σ_{k≠0} cos(2πk·x/L)/λ_k, λ_k = 2(3 − Σ cos 2πk_i/L), the solution of −Δφ = δ₀ − 1/L³ on the periodic
    L³, at the points pts = [(a, b, c)] with 0 ≤ a ≤ b ≤ c (φ is invariant under signed permutations), by separable sums."""
    kw = _fold(L); ks = [k for k, _ in kw]; ws = [w for _, w in kw]; n = len(ks)
    f = _inv_symbol(L, ks)
    xs = sorted({v for p in pts for v in p})
    cs = {x: [math.cos(2 * math.pi * k * x / L) for k in ks] for x in xs}
    wf = [[[ws[d] * f[a][b][d] for d in range(n)] for b in range(n)] for a in range(n)]
    g = {}                                                         # g[(a, b)][z] = Σ_d w_d f(a, b, d) cos(k_d z)
    for a in range(n):
        for b in range(a, n):
            row = wf[a][b]
            g[(a, b)] = {z: sum(map(float.__mul__, row, cs[z])) for z in xs}
    yz = sorted({(p[1], p[2]) for p in pts})
    h = {}
    for a in range(n):
        for (y, z) in yz:
            h[(a, y, z)] = sum(ws[b] * g[(min(a, b), max(a, b))][z] * cs[y][b] for b in range(n))
    return {p: sum(ws[a] * h[(a, p[1], p[2])] * cs[p[0]][a] for a in range(n)) / L ** 3 for p in pts}


def coulomb_fit(L=128):
    """The Coulomb coefficient of the periodic lattice Green's function: the three-term model φ = C/r + a + b r² fitted by
    least squares to every lattice point with 2 ≤ r ≤ L/6 (r by the minimum image). Returns (C, 1/4π, the relative rms
    residual, φ(0))."""
    R = L // 6
    pts, mult = [], {}
    for a in range(R + 1):
        for b in range(a, R + 1):
            for c in range(b, R + 1):
                r2 = a * a + b * b + c * c
                if 4 <= r2 <= R * R:
                    pts.append((a, b, c))
                    perms = len(set(_perms3((a, b, c))))
                    mult[(a, b, c)] = perms * 2 ** sum(1 for v in (a, b, c) if v)
    phi = green_points(L, pts + [(0, 0, 0)])
    S = [[0.0] * 3 for _ in range(3)]; t = [0.0] * 3
    for p in pts:
        r = math.sqrt(sum(v * v for v in p)); m = mult[p]; row = (1 / r, 1.0, r * r)
        for i in range(3):
            t[i] += m * row[i] * phi[p]
            for j in range(3): S[i][j] += m * row[i] * row[j]
    C, a0, b0 = _solve3(S, t)
    num = den = tot = 0.0
    for p in pts:
        r = math.sqrt(sum(v * v for v in p)); m = mult[p]
        num += m * (phi[p] - (C / r + a0 + b0 * r * r)) ** 2; den += m * abs(phi[p]); tot += m
    return C, 1 / (4 * math.pi), math.sqrt(num / tot) / (den / tot), phi[(0, 0, 0)]


def _perms3(t):
    a, b, c = t
    return [(a, b, c), (a, c, b), (b, a, c), (b, c, a), (c, a, b), (c, b, a)]


def _solve3(S, t):
    def det(M): return (M[0][0] * (M[1][1] * M[2][2] - M[1][2] * M[2][1]) - M[0][1] * (M[1][0] * M[2][2] - M[1][2] * M[2][0])
                        + M[0][2] * (M[1][0] * M[2][1] - M[1][1] * M[2][0]))
    D = det(S)
    return [det([[t[i] if j == k else S[i][j] for j in range(3)] for i in range(3)]) / D for k in range(3)]


def green_axis(L, seps):
    """G(s) = φ(s, 0, 0) on the periodic L³: the interaction energy q₁q₂G(s) of two unit charges at separation s."""
    kw = _fold(L); ks = [k for k, _ in kw]; ws = [w for _, w in kw]; n = len(ks)
    f = _inv_symbol(L, ks)
    H = [sum(ws[b] * ws[d] * f[a][b][d] for b in range(n) for d in range(n)) for a in range(n)]
    return [sum(ws[a] * H[a] * math.cos(2 * math.pi * ks[a] * s / L) for a in range(n)) / L ** 3 for s in seps]


def sign_dichotomy(L=48, seps=(6, 8, 10, 12, 16, 20)):
    """The two-charge energies: U_EM(r) = +G(r) (the field-quadratic action, like charges) and U_grav(r) = −G(r)."""
    G = green_axis(L, seps)
    return list(seps), G, [-x for x in G]


# ---- the saturation profile of the capacity-bounded Gauss law (p2) ------------------------------------------------------
def _E(r, q=1.0, kappa=1.0):
    x = q / (4 * math.pi * kappa * r * r)
    return math.asin(x) if x <= 1.0 else None


def saturation_potential(r, R=1e4, n=200000):
    """A₀(r) = ∫_r^R E dr′ with 4πr²κ sin E = q (κ = q = 1), midpoint rule with n steps (p2's numerals)."""
    h = (R - r) / n
    return sum(_E(r + (i + 0.5) * h) for i in range(n)) * h


def saturation_self_energy(rmin, R=1e4, n=400000):
    """U = ∫_{rmin}^R ½E² 4πr² dr, midpoint rule (p2's numerals)."""
    h = (R - rmin) / n; s = 0.0
    for i in range(n):
        rr = rmin + (i + 0.5) * h; e = _E(rr)
        if e is not None: s += 0.5 * e * e * 4 * math.pi * rr * rr * h
    return s


def saturation_core():
    return math.sqrt(1 / (4 * math.pi))


# ---- the finite gauge correspondence (correspondence) ----------------------------------------------------------------
def s_fund_diag(xs, eps):
    """S(exp(iεX)) = 1 − (1/n) Re Tr exp(iεX) for a diagonal X = diag(xs)."""
    xs, eps = [float(x) for x in xs], float(eps)
    return 1 - sum(math.cos(eps * x) for x in xs) / len(xs)


def window_residue(H, eps=0.05, seed=0):
    """The chain of H SU(2) links U_k = exp(iεX_k), X_k = ½ a_k·σ with random unit directions a_k: the summed per-link
    residue Σ|S(U_k) − (ε²/4) Tr X_k²| and the distance |Hol − 1| (Frobenius) of the holonomy from the identity."""
    rng = random.Random(seed); eps = float(eps)
    res = 0.0; hol = ((1 + 0j, 0j), (0j, 1 + 0j))
    for _ in range(H):
        a = [rng.gauss(0, 1) for _ in range(3)]; nrm = math.sqrt(sum(x * x for x in a)); a = [x / nrm for x in a]
        c, s = math.cos(eps / 2), math.sin(eps / 2)
        U = ((c + 1j * s * a[2], 1j * s * (a[0] - 1j * a[1])), (1j * s * (a[0] + 1j * a[1]), c - 1j * s * a[2]))
        S = 1 - 0.5 * (U[0][0] + U[1][1]).real
        ym = eps ** 2 / 4 * 0.5 * sum(x * x for x in a)
        res += abs(S - ym)
        hol = tuple(tuple(sum(hol[i][k] * U[k][j] for k in range(2)) for j in range(2)) for i in range(2))
    near = math.sqrt(sum(abs(hol[i][j] - (1 if i == j else 0)) ** 2 for i in range(2) for j in range(2)))
    return res, near


def c1_traces(traces, d, beta):
    """c₁(β) = Σ m (t/d) e^{βt/d} / Σ m e^{βt/d} over a trace multiset {t: m}."""
    beta = float(beta)
    Z = sum(m * math.exp(beta * t / d) for t, m in traces.items())
    return sum(m * t / d * math.exp(beta * t / d) for t, m in traces.items()) / Z


def quadrature_error(N):
    """The midpoint sum of f(x) = cos(0.7x) + 0.3x² on [−1, 1] with N cells against its integral."""
    xs = [-1 + 1.0 / N + i * (2 - 2.0 / N) / (N - 1) for i in range(N)]
    approx = sum(math.cos(0.7 * x) + 0.3 * x * x for x in xs) / N * 2.0
    return abs(approx - (2.0 * math.sin(0.7) / 0.7 + 0.3 * (2.0 / 3.0)))


# ---- the strong sector: strong-coupling string tensions (qcd, string_tension) -----------------------------------------
def bessel_I(v, beta, kmax=60):
    beta = float(beta)
    return sum((beta / 2) ** (2 * k + v) / (math.factorial(k) * math.factorial(k + v)) for k in range(kmax))


def sigma_U1(beta):
    """σ = −ln(I₁/I₀): the U(1) single-plaquette coefficient."""
    return -math.log(bessel_I(1, beta) / bessel_I(0, beta))


def sigma_ZN(beta, N):
    beta = float(beta)
    ths = [2 * math.pi * k / N for k in range(N)]
    Z = sum(math.exp(beta * math.cos(t)) for t in ths)
    return -math.log(sum(math.cos(t) * math.exp(beta * math.cos(t)) for t in ths) / Z)


def c1_su3(beta, n=120):
    """c₁^{SU(3)}(β) = ⟨(1/3) Re χ e^{β Re χ/3}⟩ over SU(3), by the Weyl integration formula on an n × n periodic grid of
    the maximal torus (the trapezoidal rule, exponentially accurate for this smooth periodic integrand)."""
    num = den = 0.0; beta = float(beta)
    cs = [complex(math.cos(2 * math.pi * k / n), math.sin(2 * math.pi * k / n)) for k in range(n)]
    for i in range(n):
        z1 = cs[i]
        for j in range(n):
            z2 = cs[j]; z3 = (z1 * z2).conjugate()
            v = abs((z1 - z2) * (z1 - z3) * (z2 - z3)) ** 2
            x = (z1 + z2 + z3).real / 3.0
            w = math.exp(beta * x) * v
            num += x * w; den += w
    return num / den


def su3_fit(betas=(0.02, 0.04, 0.06, 0.08, 0.10, 0.12), n=120):
    """The least-squares fit c₁ = a β + b β² + c β³ to c1_su3 at small β (string_tension's fit): (a, b, c)."""
    vals = [c1_su3(b, n) for b in betas]
    rows = [(b, b * b, b ** 3) for b in betas]
    S = [[sum(r[i] * r[j] for r in rows) for j in range(3)] for i in range(3)]
    t = [sum(r[i] * v for r, v in zip(rows, vals)) for i in range(3)]
    return _solve3(S, t)


# ---- the electroweak scale against the transmutation forms (v_scale) --------------------------------------------------
def v_scale():
    d = {k: _f(v) for k, v in DATA["v_scale"].items()}
    mP, MW, v, MZ = d["m_P"], d["M_W"], d["v"], d["M_Z"]
    out = dict(b_fit_MW=8 * math.pi ** 2 / math.log(mP / MW), b_fit_v=8 * math.pi ** 2 / math.log(mP / v))
    b2 = 19 / 6
    out["L_b2"] = mP * math.exp(-8 * math.pi ** 2 / b2)
    out["mu_IR"] = MZ * math.exp(-2 * math.pi * d["a2inv_MZ"] / b2)
    out["as_MP_needed"] = 2 * math.pi / (7.0 * 45.0)
    out["as_MP_run"] = 1.0 / (1.0 / d["alpha_s_MZ"] + (7.0 / (2 * math.pi)) * math.log(mP / MZ))
    out["vc"] = mP * math.exp(-(2 * math.pi) ** 2)
    out["v1"] = 2 ** 1.5 * mP * math.exp(-(2 * math.pi) ** 2)
    return out


# ---- asymptotic freedom and the QCD scale (p6) ------------------------------------------------------------------------
def lambda_qcd(b0, alpha_s=None, mu=None):
    """Λ = μ exp(−2π/(b₀ α_s(μ))), by default at the M_Z anchor of p6."""
    d = DATA["p6"]
    a = _f(alpha_s if alpha_s is not None else d["alpha_s_MZ"]); m = _f(mu if mu is not None else d["M_Z"])
    return m * math.exp(-2 * math.pi / (_f(b0) * a))


def proton_planck_exponent():
    """2 ln(M_P/m_p): (m_p/M_P)² = e^{−that}."""
    d = DATA["p6"]
    return 2 * math.log(_f(d["M_P"]) / _f(d["m_p"]))


# ---- one-loop running (p1) -----------------------------------------------------------------------------------------------
def unification_scale():
    """The scale where α₁ = α₂ under one-loop running from M_Z: M_Z exp(2π(α₁⁻¹ − α₂⁻¹)/(b₁ − b₂))."""
    d = DATA["p1"]
    a1 = 0.6 * (1 - _f(d["sin2"])) * _f(d["ainv_em"]); a2 = _f(d["sin2"]) * _f(d["ainv_em"])
    b = [_f(x) for x in d["b"]]
    return _f(d["M_Z"]) * math.exp(2 * math.pi * (a1 - a2) / (b[0] - b[1]))


# ---- the winding overlap (p7) and the measured Koide reading (koide) ---------------------------------------------------
def winding_overlaps(N=60, T=12, kmax=6):
    """|Σ_{t<T} ζ_N^{kt}|/T for k = 0 .. kmax − 1."""
    return [abs(sum(complex(math.cos(2 * math.pi * k * t / N), math.sin(2 * math.pi * k * t / N)) for t in range(T))) / T
            for k in range(kmax)]


def koide_measured():
    """The charged-lepton Q = Σm/(Σ√m)² and ρ² = |â₁|²/â₀² with â_k = Σ_j √m_j ω^{−jk}, ω = e^{2πi/3}."""
    d = DATA["koide"]
    m = [_f(d["m_e"]), _f(d["m_mu"]), _f(d["m_tau"])]
    a = [math.sqrt(x) for x in m]
    Qm = sum(m) / sum(a) ** 2
    w = complex(-0.5, math.sqrt(3) / 2)
    a1 = abs(sum(a[j] * w ** (-j) for j in range(3)))
    return Qm, (a1 / sum(a)) ** 2


# ---- the bare coupling (o2_numbers) ---------------------------------------------------------------------------------------
def o2_numbers():
    """(1/α_bare = 4π, the EM/gravity hierarchy α/(m_p/m_P)², the gap (1/α)/(4π))."""
    d = DATA["o2_numbers"]
    alpha0 = 1 / _f(d["alpha0_inv"])
    grav = (_f(d["m_p"]) / _f(d["m_P"])) ** 2
    return 4 * math.pi, alpha0 / grav, (1 / alpha0) / (4 * math.pi)
