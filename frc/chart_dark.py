"""frc.chart_dark — the readings of 32-dark against the continuum and the SPARC tables (the chart theme; 32-dark's
migration, 18 October 2026).

The chart theme holds the floats (frc/themes.py, rank 30). This file serves the continuum-comparison layer of the paper
32-dark, whose ledger file frc/ledgers/p32_dark.py decides every exact clause through frc/dark.py and compares these
readings with rational bounds (it converts each float exactly, with Fraction). Each function computes what one script
of the paper's validation package (src/32-dark) computes in floating point, with the same inputs: the floor a₀ = cH₀/2π
and its comparison with the fitted g_†, the Λ-face of the floor and Λ = 3π/S, the interpolation ν(x) = 1/(1 − e^{−√x})
against the simple rational form, the deep and Newtonian slopes, the chart angle, the Tully–Fisher speed and slope, the
exponential disk's rotation curve (the Bessel kernel by quadrature) with and without an external field, the scatter law
and its bound, the SPARC residuals at the fixed floor (the tables under frc/data/sparc/, read by their published byte
layout), the within-galaxy scatter and the amplitude-sum boost from the rotation curves, the binned shape test of the
two forms, the stationary Fokker–Planck slope of the noisy link, E(z)^{1/4}, the wide-binary and pressure-supported
numbers, and the first-passage reduction's coefficient and wrap term. The standard library only.

The measured constants are declared data (DATA), each with its source. The three SPARC tables (Lelli, McGaugh and
Schombert 2016, Table 1; Lelli et al. 2017, the data behind Figure 2; the rotation-curve decompositions Rotmod_LTG) are
the paper's confrontation data (row A7), copied from the package's data/ into frc/data/sparc/.
"""
import io
import math
import os
import zipfile
from fractions import Fraction as Q

from frc import chart as CH

# ---- declared data ------------------------------------------------------------------------------------------------------
DATA = {
    "constants": dict(c=Q(CH.C_LIGHT), G=Q("6.67430e-11"), M_sun=Q("1.98847e30"), AU=Q("1.495978707e11"),
                      Mpc_m=CH.MPC_KM * 1000, l_P=CH.PLANCK_LENGTH),            # SI; CODATA 2018 G, IAU 2015 M_⊙ and 2012 AU
    "cosmology": dict(H0=CH.H0_ENTAILED, g_dagger=CH.A0_FIT[0], g_dagger_err=CH.A0_FIT[1],   # km s⁻¹ Mpc⁻¹; m s⁻² (McGaugh 2016)
                      S=Q("3.3e122"), Omega_m=Q("0.315")),                      # the de Sitter entropy (32:A1); Planck 2018 Ω_m
    "galactic": dict(g_ext_over_a0=Q("1.8"), binary_mass=Q("1.5"),               # the Galactic field at the Sun in units of a₀; M_⊙
                     efe_disk=(Q("6e10"), Q(3), Q(40)),                          # M_⊙, R_d in kpc, the outer radius in kpc (eq. efe)
                     disk=(Q("5e10"), Q(3)), btfr_mass=Q("5e10"),                # the figure's disk and the Tully–Fisher mass, M_⊙
                     efe_fields=(Q(0), Q("0.03"), Q("0.1"), Q("0.5"))),          # g_ext/a₀ of the four curves
    "link": dict(D=(Q("0.3"), Q("0.6")), tilts=(Q("0.01"), Q("0.02"), Q("0.04"), Q("0.08"), Q("0.16"), Q("0.32"))),
    "sparc": dict(dir=os.path.join(os.path.dirname(os.path.abspath(__file__)), "data", "sparc"),
                  rar="RAR.mrt", sample="SPARC_Lelli2016c.mrt", rotmod="Rotmod_LTG.zip",
                  ml_disk=Q("0.5"), ml_bulge=Q("0.7"), max_rel_err=Q("0.10"), min_inc=Q(30), min_points=5),
}

LN10 = math.log(10)
BIN_EDGES = ("-2", "-1.5", "-1", "-0.5", "0", "0.5", "1", "1.5")           # the bins of log₁₀ x of the SPARC scatter test


def _f(x): return float(x)


# ---- the floor and the cosmological constant ------------------------------------------------------------------------------------------
def floor():
    """a₀ = cH₀/2π in m s⁻² at the entailed H₀ (32:C2, 32:X2; the chart theme's floor)."""
    return CH.floor(DATA["cosmology"]["H0"])


def floor_comparison():
    """(a₀, the percentage below the fitted g_†, the deficit in units of g_†'s systematic)."""
    a0 = floor(); g, e = _f(DATA["cosmology"]["g_dagger"]), _f(DATA["cosmology"]["g_dagger_err"])
    return a0, 100 * (g - a0) / g, (g - a0) / e


def lambda_face(S=None):
    """The floor read from the entropy alone: r_H = √(S/π) ℓ_P, H_Λ = c/r_H, (r_H, H_Λ, cH_Λ/2π) (32:X10)."""
    S = _f(DATA["cosmology"]["S"] if S is None else S)
    rH = math.sqrt(S / math.pi) * _f(DATA["constants"]["l_P"])
    HL = _f(DATA["constants"]["c"]) / rH
    return rH, HL, _f(DATA["constants"]["c"]) * HL / (2 * math.pi)


def lambda_measured():
    """The fitted Λ (Planck 2018, the chart theme's LAMBDA_FIT in m⁻²) in Planck units, Λ ℓ_P²."""
    return _f(CH.LAMBDA_FIT) * _f(CH.PLANCK_LENGTH) ** 2


def lambda_planck(S=None):
    """Λ = 3/r_H² = 3π/S in Planck units, and the product ΛS (32:C11, 32:X9)."""
    S = _f(DATA["cosmology"]["S"] if S is None else S)
    lam = 3 * math.pi / S
    return lam, lam * S


# ---- the interpolation ----------------------------------------------------------------------------------------------------------------
def nu(x):
    """ν(x) = 1/(1 − e^{−√x}), the registration factor g_obs/g_b."""
    x = _f(x)
    return 1 / (1 - math.exp(-math.sqrt(x)))


def nu_simple(x):
    """The simple rational interpolant with the same limits, (1 + √(1 + 4/x))/2."""
    x = _f(x)
    return 0.5 * (1 + math.sqrt(1 + 4 / x))


def _logspace(lo, hi, n):
    return [10 ** (lo + (hi - lo) * k / (n - 1)) for k in range(n)]


def discriminant(n=30001):
    """max(ν_simple − ν) over 0.1 ≤ x ≤ 100 on a log grid: (the maximum, its x, the maximum in dex) (32:C6, 32:X4)."""
    best = (0.0, 0.0, 0.0)
    for x in _logspace(-1, 2, n):
        d = nu_simple(x) - nu(x)
        if d > best[0]: best = (d, x, math.log10(nu_simple(x) / nu(x)))
    return best


def log_slope(f, x1, x2):
    return (math.log(f(x2)) - math.log(f(x1))) / (math.log(x2) - math.log(x1))


def slopes():
    """(the deep slope of x ν(x) over 10⁻³..10⁻², the Newtonian slope over 10²..10³)."""
    g = lambda x: x * nu(x)
    return log_slope(g, 1e-3, 1e-2), log_slope(g, 1e2, 1e3)


def tan_alpha(x):
    """tan α(x) with sin²α = e^{−√x}: √(e^{−√x}/(1 − e^{−√x}))."""
    e = math.exp(-math.sqrt(_f(x)))
    return math.sqrt(e / (1 - e))


def chart_angle(x=1.0):
    """α(x) = arcsin(e^{−√x/2}) in degrees; 37.3° at the floor."""
    return math.degrees(math.asin(math.exp(-math.sqrt(x) / 2)))


# ---- the Tully–Fisher relation and the exponential disk --------------------------------------------------------------------------------
def _si():
    c = DATA["constants"]
    return _f(c["G"]), _f(c["M_sun"]), _f(c["Mpc_m"]) / 1000, _f(c["AU"])


def btfr_speed(mass_sun=None):
    """v_flat = (GMa₀)^{1/4} in km s⁻¹ (32:C5, 32:X3)."""
    G, Msun, kpc, AU = _si()
    M = _f(DATA["galactic"]["btfr_mass"] if mass_sun is None else mass_sun) * Msun
    return (G * M * floor()) ** 0.25 / 1e3


def btfr_slope():
    """d ln v_flat / d ln M between 10⁸ and 10¹² M_⊙: 1/4."""
    return log_slope(lambda m: btfr_speed(m), 1e8, 1e12)


def _simpson(f, a, b, n=2000):
    """Composite Simpson's rule on [a, b] with n (even) intervals."""
    h = (b - a) / n
    s = f(a) + f(b)
    for k in range(1, n):
        s += (4 if k % 2 else 2) * f(a + k * h)
    return s * h / 3


def bessel_i(n, x):
    """I_n(x) = (1/π) ∫₀^π e^{x cos θ} cos(nθ) dθ."""
    return _simpson(lambda t: math.exp(x * math.cos(t)) * math.cos(n * t), 0.0, math.pi) / math.pi


def bessel_k(n, x):
    """K_n(x) = ∫₀^∞ e^{−x cosh t} cosh(nt) dt, the tail cut sixty e-folds below the integrand's peak e^{−x}."""
    tmax = math.acosh(1 + 60 / x)
    return _simpson(lambda t: math.exp(-x * math.cosh(t)) * math.cosh(n * t), 0.0, tmax, 4000)


def disk_curve(mass_sun, rd_kpc, radii_kpc, g_ext_over_a0=0.0):
    """The exponential disk's Newtonian speed v_b and the registered speed v_obs = √(r g_in ν((g_in + g_ext)/a₀)) in
    km s⁻¹ at the radii (kpc): v_b² = 2 (GM/R_d) y² (I₀K₀ − I₁K₁)(y), y = r/2R_d (Freeman 1970) (32:C5, 32:C9)."""
    G, Msun, kpc, AU = _si()
    a0 = floor(); M = mass_sun * Msun; Rd = rd_kpc * kpc; gext = g_ext_over_a0 * a0
    vb, vo = [], []
    for rk in radii_kpc:
        r = rk * kpc; y = r / (2 * Rd)
        vb2 = 2 * (G * M / Rd) * y * y * (bessel_i(0, y) * bessel_k(0, y) - bessel_i(1, y) * bessel_k(1, y))
        gin = vb2 / r
        gobs = gin * nu((gin + gext) / a0)
        vb.append(math.sqrt(vb2) / 1e3); vo.append(math.sqrt(gobs * r) / 1e3)
    return vb, vo


def efe_speeds():
    """The outer rotation speed of the fixed disk (DATA galactic.efe_disk) at g_ext/a₀ = 0, 0.03, 0.1, 0.5: the
    external-field downturn (32:C9, 32:X6)."""
    M, Rd, rout = (_f(v) for v in DATA["galactic"]["efe_disk"])
    return [disk_curve(M, Rd, [rout], _f(ge))[1][0] for ge in DATA["galactic"]["efe_fields"]]


def rotation_curve():
    """The figure's disk (5 × 10¹⁰ M_⊙, R_d = 3 kpc) over 0.1–30 kpc: (the peak baryonic speed, the mean registered
    speed over 20–30 kpc, the Tully–Fisher speed of its mass) in km s⁻¹ (32:C5)."""
    M, Rd = (_f(v) for v in DATA["galactic"]["disk"])
    radii = [0.1 + 29.9 * k / 299 for k in range(300)]
    vb, vo = disk_curve(M, Rd, radii)
    outer = [v for r, v in zip(radii, vo) if r >= 20]
    return max(vb), sum(outer) / len(outer), btfr_speed(M)


# ---- the scatter law -------------------------------------------------------------------------------------------------------------------
def scatter_law(x, r):
    """σ(x, σ_v/v) = (2 tan α(x)/ln 10)·arctan(σ_v/v) in dex (32:C8, 32:P2)."""
    return 2 * tan_alpha(x) / LN10 * math.atan(_f(r))


def scatter_at_angle(x, da_deg):
    """σ = (2 tan α(x)/ln 10) δα for a spread δα in degrees."""
    return 2 * tan_alpha(x) / LN10 * math.radians(_f(da_deg))


def delta_alpha_bound(sigma_dex=0.04, x=1.0):
    """The spread δα in degrees that gives σ = sigma_dex at x: δα = σ ln10/(2 tan α(x))."""
    return math.degrees(_f(sigma_dex) * LN10 / (2 * tan_alpha(x)))


def scatter_rise(xs=(1e-2, 1e-3, 1e-4)):
    """tan α(x)·x^{1/4} at deep x: → 1, the x^{−1/4} rise."""
    return [tan_alpha(x) * x ** 0.25 for x in xs]


# ---- the SPARC tables -----------------------------------------------------------------------------------------------------------------
def _path(key): return os.path.join(DATA["sparc"]["dir"], DATA["sparc"][key])


def load_rar():
    """The 2692 points of the radial acceleration relation (Lelli et al. 2017, the data behind Figure 2): the columns
    log g_bar, its error, log g_obs, its error, by the file's byte layout (bytes 1–6, 8–11, 13–18, 20–23)."""
    rows = []
    with open(_path("rar"), encoding="utf-8") as fh:
        dashes = 0                                        # the data follow the third line of dashes
        for line in fh:
            if line.startswith("-" * 20):
                dashes += 1; continue
            if dashes < 3 or len(line) < 23: continue
            rows.append((float(line[0:6]), float(line[7:11]), float(line[12:18]), float(line[19:23])))
    return rows


def load_sample():
    """Table 1 of Lelli, McGaugh and Schombert (2016): name → (inclination in degrees, V_flat in km s⁻¹, the quality
    flag). The table's rows carry the nineteen fields of its byte-by-byte description in that order (Galaxy, T, D, e_D,
    f_D, Inc, e_Inc, L, e_L, R_eff, SB_eff, R_disk, SB_disk, M_HI, R_HI, V_flat, e_V_flat, Q, Ref.) with wider spacing
    than the description states, so the fields are split on whitespace; the data follow the fourth line of dashes."""
    out = {}
    with open(_path("sample"), encoding="utf-8") as fh:
        dashes = 0
        for line in fh:
            if line.startswith("-" * 20):
                dashes += 1; continue
            p = line.split()
            if dashes < 4 or len(p) != 19: continue
            out[p[0]] = (float(p[5]), float(p[15]), int(p[17]))
    return out


def load_rotmods():
    """The rotation-curve decompositions (Rotmod_LTG): name → rows (R kpc, V_obs, e_V, V_gas, V_disk, V_bul)."""
    out = {}
    with zipfile.ZipFile(_path("rotmod")) as z:
        for fn in sorted(z.namelist()):
            if not fn.endswith("_rotmod.dat"): continue
            name = os.path.basename(fn)[:-len("_rotmod.dat")]
            rows = []
            for line in io.StringIO(z.read(fn).decode("utf-8")):
                if line.startswith("#") or not line.strip(): continue
                p = line.split()
                rows.append(tuple(float(v) for v in p[:6]))
            out[name] = rows
    return out


def _mean(xs): return sum(xs) / len(xs)


def _std(xs):
    m = _mean(xs)
    return math.sqrt(sum((x - m) ** 2 for x in xs) / len(xs))


def _median(xs):
    s = sorted(xs); n = len(s)
    return s[n // 2] if n % 2 else 0.5 * (s[n // 2 - 1] + s[n // 2])


def _percentile(xs, q):
    s = sorted(xs); k = (len(s) - 1) * q / 100; i = int(math.floor(k)); j = min(i + 1, len(s) - 1)
    return s[i] + (s[j] - s[i]) * (k - i)


def _ranks(xs):
    order = sorted(range(len(xs)), key=lambda i: xs[i]); r = [0] * len(xs)
    for k, i in enumerate(order): r[i] = k
    return r


def spearman(a, b):
    ra, rb = _ranks(a), _ranks(b); ma, mb = _mean(ra), _mean(rb)
    cov = sum((x - ma) * (y - mb) for x, y in zip(ra, rb))
    return cov / math.sqrt(sum((x - ma) ** 2 for x in ra) * sum((y - mb) ** 2 for y in rb))


def residual_slope(x):
    """d log(g_b ν)/d log g_b = 1 − (√x/2) e^{−√x}/(1 − e^{−√x}), the error propagation of log g_b."""
    s = math.sqrt(x); e = math.exp(-s)
    return 1 - 0.5 * s * e / (1 - e)


def sparc_residuals():
    """The SPARC points at the fixed floor: (n, the rms residual log g_obs − log(g_b ν(g_b/a₀)), the error-expected rms,
    the intrinsic scatter √(rms² − expected²), the mean residual, {(lo, hi): (count, intrinsic scatter) in the bin of
    log₁₀ x, the edges BIN_EDGES as strings}) (32:C8, 32:X5, 32:P2)."""
    a0 = floor(); rows = load_rar()
    res, err, lx = [], [], []
    for lgb, egb, lgo, ego in rows:
        gb = 10 ** lgb; x = gb / a0
        res.append(lgo - math.log10(gb * nu(x)))
        err.append(math.sqrt(ego ** 2 + (residual_slope(x) * egb) ** 2))
        lx.append(math.log10(x))
    rms = _std(res); exp_rms = math.sqrt(_mean([e * e for e in err]))
    intr = math.sqrt(max(rms ** 2 - exp_rms ** 2, 0.0))
    bins = {}
    for lo, hi in zip(BIN_EDGES[:-1], BIN_EDGES[1:]):
        idx = [i for i, v in enumerate(lx) if float(lo) <= v < float(hi)]
        if len(idx) < 2: continue
        rr = [res[i] for i in idx]; ee = [err[i] for i in idx]
        bins[(lo, hi)] = (len(idx), math.sqrt(max(_std(rr) ** 2 - _mean([e * e for e in ee]), 0.0)))
    return len(rows), rms, exp_rms, intr, _mean(res), bins


def sparc_within_galaxy():
    """The within-galaxy intrinsic scatter of the SPARC disks (Q ≤ 2, i > 30°, V_flat > 0, points with δV/V < 10 %, at
    least five of them) against 1/V_flat: (the number of disks, the median within-galaxy intrinsic scatter, Spearman's ρ
    of the intrinsic scatter with 1/V_flat) (32:Y2's exposure, read in 32:C8's check)."""
    a0 = floor(); G, Msun, kpc, AU = _si(); S = DATA["sparc"]
    sample = load_sample(); curves = load_rotmods()
    mld, mlb, maxrel, minc, minn = _f(S["ml_disk"]), _f(S["ml_bulge"]), _f(S["max_rel_err"]), _f(S["min_inc"]), S["min_points"]
    intr, inv_vf = [], []
    for name in sorted(curves):
        if name not in sample: continue
        inc, vflat, q = sample[name]
        if q == 3 or inc < minc or vflat <= 0: continue
        rg, eg = [], []
        for R, Vobs, eV, Vgas, Vdisk, Vbul in curves[name]:
            vb2 = Vgas * abs(Vgas) + mld * Vdisk ** 2 + mlb * Vbul ** 2
            if vb2 <= 0 or Vobs <= 0 or eV / Vobs >= maxrel: continue
            gbg = vb2 * 1e6 / (R * kpc); gog = Vobs ** 2 * 1e6 / (R * kpc)
            rg.append(math.log10(gog) - math.log10(gbg * nu(gbg / a0))); eg.append(2 * eV / Vobs / LN10)
        if len(rg) < minn: continue
        intr.append(math.sqrt(max(_std(rg) ** 2 - _mean([e * e for e in eg]), 0.0))); inv_vf.append(1 / vflat)
    return len(intr), _median(intr), spearman(intr, inv_vf)


def sparc_amplitude_boost():
    """If a galaxy's gas, disk and bulge added as amplitudes, the RAR would rise by ½ log₁₀ N_eff with
    N_eff = (Σ√g_i)²/Σg_i over its components at each radius: (the number of points, the median boost in dex, the 16th
    and 84th percentiles) (32:Y1's within-galaxy constraint, read in 32:C8's check)."""
    S = DATA["sparc"]; mld, mlb = _f(S["ml_disk"]), _f(S["ml_bulge"])
    boost = []
    for rows in load_rotmods().values():
        for R, Vobs, eV, Vgas, Vdisk, Vbul in rows:
            comps = [c for c in (max(Vgas * abs(Vgas), 0.0), mld * Vdisk ** 2, mlb * Vbul ** 2) if c > 0]
            if not comps: continue
            neff = sum(math.sqrt(c) for c in comps) ** 2 / sum(comps)
            boost.append(0.5 * math.log10(neff))
    return len(boost), _median(boost), _percentile(boost, 16), _percentile(boost, 84)


def binned_shape(grid=(0.8e-10, 1.6e-10, 801)):
    """The named test of 32:B8 on the binned relation: 0.2-dex bins of log g_b with at least ten points, each bin's
    mean log g_obs with its scatter as the uncertainty; both forms with a₀ free on a grid. Returns (the bin count,
    the exponential form's best a₀ and χ², the simple form's best a₀ and χ², floor/fit, the largest departure of the
    binned relation from the exponential form in the band 2 < x < 10 as a fraction of the bin scatter, the band's χ²
    of both forms, the fixed-floor χ² of both forms) (32:C6, 32:X4, 32:X11, 32:P6)."""
    a0 = floor(); rows = load_rar()
    edges = [-12.0 + 0.2 * k for k in range(18)]
    bins = []
    for lo, hi in zip(edges[:-1], edges[1:]):
        sel = [lgo for lgb, egb, lgo, ego in rows if lo <= lgb < hi]
        if len(sel) < 10: continue
        bins.append((0.5 * (lo + hi), _mean(sel), _std(sel)))

    def chi2(form, a, band=False):
        tot = 0.0; worst = 0.0
        for cb, mb, eb in bins:
            x = 10 ** cb / a
            if band and not (2 < x < 10): continue
            r = (mb - math.log10(10 ** cb * form(x))) / eb
            tot += r * r; worst = max(worst, abs(r))
        return tot, worst

    lo, hi, n = grid
    best = {}
    for name, form in (("exp", nu), ("simple", nu_simple)):
        vals = [(chi2(form, lo + (hi - lo) * k / (n - 1))[0], lo + (hi - lo) * k / (n - 1)) for k in range(n)]
        c, a = min(vals)
        best[name] = (a, c)
    a_e, c_e = best["exp"]; a_s, c_s = best["simple"]
    band_e = chi2(nu, a_e, True); band_s = chi2(nu_simple, a_s, True)
    return (len(bins), a_e, c_e, a_s, c_s, a0 / a_e, band_e[1], band_e[0], band_s[0], chi2(nu, a0)[0], chi2(nu_simple, a0)[0])


def monotone_grid(n=2001):
    """x ν(x) strictly increasing on a log grid 10⁻⁴..10⁴: True when every step rises (32:X11, 32:P6)."""
    xs = _logspace(-4, 4, n)
    return all(x1 * nu(x1) < x2 * nu(x2) for x1, x2 in zip(xs[:-1], xs[1:]))


# ---- the noisy link's stationary solution ------------------------------------------------------------------------------------------
def mean_sin(T, D, n=4000):
    """⟨sin φ⟩ in the stationary density of dφ = (T − sin φ)dt + √(2D) dW on the circle: P(φ) ∝ e^{−U(φ)/D} ∫_φ^{φ+2π}
    e^{U(ψ)/D} dψ with U = −Tφ − cos φ; the inner integral from the cumulative trapezoid over one period and the
    periodicity e^{U(ψ+2π)/D} = e^{−2πT/D} e^{U(ψ)/D} (32:C4)."""
    h = 2 * math.pi / n
    phi = [k * h for k in range(n + 1)]
    g = [math.exp((-T * p - math.cos(p)) / D) for p in phi]            # e^{U/D} on [0, 2π]
    cum = [0.0]
    for k in range(n): cum.append(cum[-1] + 0.5 * (g[k] + g[k + 1]) * h)
    total = cum[-1]; decay = math.exp(-2 * math.pi * T / D)
    P = [math.exp(-(-T * p - math.cos(p)) / D) * ((total - cum[k]) + decay * cum[k]) for k, p in enumerate(phi[:-1])]
    norm = sum(P) * h
    return sum(math.sin(p) * q for p, q in zip(phi[:-1], P)) * h / norm


def fokker_planck_slope(D):
    """At the noise level D: (the small-tilt log-slope d ln T/d ln⟨sin φ⟩ over the three smallest tilts, the boosts
    T/⟨sin φ⟩ at every tilt) — the mean response Newtonian, the boost constant to rising (32:C4)."""
    D = _f(D); tilts = [_f(t) for t in DATA["link"]["tilts"]]
    flux = [mean_sin(t, D) for t in tilts]
    xs = [math.log(f) for f in flux[:3]]; ys = [math.log(t) for t in tilts[:3]]
    mx, my = _mean(xs), _mean(ys)
    slope = sum((x - mx) * (y - my) for x, y in zip(xs, ys)) / sum((x - mx) ** 2 for x in xs)
    return slope, [t / f for t, f in zip(tilts, flux)]


# ---- the predictions ---------------------------------------------------------------------------------------------------------------------
def e_of_z(z):
    """E(z) = √(Ω_m(1 + z)³ + 1 − Ω_m) at the declared Ω_m."""
    om = _f(DATA["cosmology"]["Omega_m"])
    return math.sqrt(om * (1 + z) ** 3 + 1 - om)


def tully_fisher_shift(z):
    """v_flat(z)/v_flat(0) = E(z)^{1/4} under the running floor a₀(z) = cH(z)/2π (32:P1)."""
    return e_of_z(_f(z)) ** 0.25


def ez_quarter():
    """(the percentages E(z)^{1/4} − 1 at z = 0.5, 1, 2; cH(1)/2π in m s⁻²; the rise a₀(1) − a₀(0))."""
    a0 = floor()
    return [100 * (tully_fisher_shift(z) - 1) for z in (0.5, 1.0, 2.0)], a0 * e_of_z(1.0), a0 * (e_of_z(1.0) - 1)


def wide_binaries(separations_kau=(10, 20, 40)):
    """At the separations (kAU), a 1.5 M_⊙ pair in the Galactic field g_ext = 1.8 a₀: [(s, g_b/a₀, y = (g_b + g_ext)/a₀,
    ν(y), the velocity enhancement √ν − 1 in per cent)] (32:P3)."""
    G, Msun, kpc, AU = _si(); a0 = floor()
    gext = _f(DATA["galactic"]["g_ext_over_a0"]) * a0; M = _f(DATA["galactic"]["binary_mass"]) * Msun
    out = []
    for s in separations_kau:
        g = G * M / (s * 1e3 * AU) ** 2; y = (g + gext) / a0; n = nu(y)
        out.append((s, g / a0, y, n, 100 * (math.sqrt(n) - 1)))
    return out


def coherence_offsets(ratios=(0.5, 1.0)):
    """log₁₀ √w with w = 1/(1 + (σ_v/v)²) at the dispersion ratios: the pressure-supported offset in dex (32:P4)."""
    return [0.5 * math.log10(1 / (1 + r * r)) for r in ratios]


def nu_core(xs=(0.1, 0.25)):
    """ν at the cluster-core accelerations g_b/a₀ = 0.1, 0.25, and the boosts √6 and √(8/3) (32:X8)."""
    return [nu(x) for x in xs], math.sqrt(6), math.sqrt(8 / 3)


# ---- the first-passage reduction ---------------------------------------------------------------------------------------------------
def passage_reduction(s):
    """(arccosh(e^s)/√(2s) − 1)/s → 1/6: the coefficient of the controlled reduction (32:C7)."""
    s = _f(s)
    return (math.acosh(math.exp(s)) / math.sqrt(2 * s) - 1) / s


def wrap_term(N=200, a=8, s=0.02):
    """The killed walk on Z_N against the line at per-step survival e^{−s}, f = e^{−arccosh e^s}: (the two-image
    difference (f^a + f^{N−a})/(1 + f^N) − f^a = f^{N−a}(1 − f^{2a})/(1 + f^N), the wrap term f^{N−a}) (32:C7)."""
    d = math.acosh(math.exp(s)); f = math.exp(-d)
    wrap = f ** (N - a)
    return wrap * (1 - f ** (2 * a)) / (1 + f ** N), wrap
