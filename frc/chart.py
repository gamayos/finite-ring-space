"""frc.chart — the chart theme: the readings against the continuum (ledger migration, task LM30, 6 October 2026).

The chart theme is the one python theme with floats (frc/themes.py, rank 30): the readings of the finite results
against the continuum. Its cosmology section serves the chart clauses of the master's rows A8 (the scale import's
numerals S and Ω; the ledger's ln Ω for L8), L1 (the floor), L3 (the octant record depth and its outputs), L8 (the primordial tilt) and
P1 (the running floor).

Each reading is computed twice: in floating point (`math`), and as a certified bracket in exact rational arithmetic,
π from Machin's formula with the alternating-series remainder and e^x from its Taylor series with the tail bound. The
brackets follow the Lean theorems of lean/FrcLedger/Theme/Chart.lean, which certify the same numerals from π to six
places, e to nine and the Taylor tail. A bracket is a pair (lo, hi) of Fractions with lo < value < hi.

The chart's numerals are declared data: the speed of light, the megaparsec, the Julian year, the octant depth of the
row's depth numeral, the stellar age, the ledger's ln Ω, the fitted values and their errors. That the octant is the record depth, that the
floor is the synchronisation threshold and that ln Ω is the tilt's e-fold count are the rows' realisation clauses.
"""
import math
from fractions import Fraction as Q

# ---- declared data -------------------------------------------------------------------------------------------------
C_LIGHT = 299792458                       # m s⁻¹, exact (SI)
MPC_KM = Q("3.0856775814913673e19")       # km per megaparsec (IAU 2015)
JULIAN_YEAR = Q(36525, 100) * 86400       # s
AGE_GYR = Q("13.79")                      # the row's octant depth numeral, Gyr: the channel-1 consistency reading (00:L3, 14:P3)
STELLAR_AGE = (Q("13.61"), Q("0.34"))     # the fit-independent stellar age and its error, Gyr (14:P3, 14:A8)
H0_ENTAILED = Q("67.4")                   # the entailed rate, km s⁻¹ Mpc⁻¹ (00:L1, 00:L3, 21:P3)
OMEGA_L_FIT = (Q("0.685"), Q("0.007"))    # Planck 2018 Ω_Λ and its error (14:A8)
A0_FIT = (Q("1.20e-10"), Q("0.24e-10"))   # the fitted floor and its systematic, m s⁻² (21:P3)
TILT_FIT = (Q("-0.0351"), Q("0.0042"))    # Planck 2018 n_s − 1 and its error (00:L8)
H0_ERR = Q("1.7")                         # the stellar age's error carried to the rate, rounded (14:P3)
LADDER_FIT = (Q("73.0"), Q("1.0"))        # the Cepheid ladder's H₀ (Riess 2022), km s⁻¹ Mpc⁻¹ (00:L3, 14-entropy)
LAMBDA_FIT = Q("1.088e-52")              # Planck 2018 Λ, m⁻², the fit's cosmological constant (14:A1, 14:C1; 00:A8)
PLANCK_LENGTH = Q("1.616255e-35")         # ℓ_P, m (CODATA 2018; 00:A8)
LN_OMEGA = Q("283.5")                     # the ledger's ln Ω, the numeral of every chart reading (00:A8, 00:L8); recomputed from Λ and ℓ_P by ln_omega_bracket


# ---- floating point --------------------------------------------------------------------------------------------------
def tanh_octant():
    """tanh(3π/8), the octant's rate factor."""
    return math.tanh(3 * math.pi / 8)


def omega_lambda():
    """Ω_Λ = tanh²(3π/8), the octant's landing in the rival chart (00:L3, 14:C7)."""
    return tanh_octant() ** 2


def lcdm_age(omega):
    """The rival chart's age identity t₀H_Λ = (2/3) artanh √Ω_Λ (14:A8), on 0 ≤ Ω_Λ < 1."""
    return 2 / 3 * math.atanh(math.sqrt(omega))


def locus():
    """The age–rate locus t H₀ = (π/4)/tanh(3π/8) (00:L3, 14:P3)."""
    return (math.pi / 4) / tanh_octant()


def hubble(age_gyr=AGE_GYR):
    """H₀ in km s⁻¹ Mpc⁻¹ read on the locus at the octant depth `age_gyr` (00:L3)."""
    return locus() / (float(age_gyr) * 1e9 * float(JULIAN_YEAR)) * float(MPC_KM)


def floor(h0_kms=H0_ENTAILED):
    """The floor a₀ = cH₀/2π in m s⁻², H₀ in km s⁻¹ Mpc⁻¹ (00:L1)."""
    return C_LIGHT * float(h0_kms) * 1e3 / (float(MPC_KM) * 1e3) / (2 * math.pi)


def tilt(ln_omega=LN_OMEGA):
    """The tilt's committed form n_s − 1 = −π²/ln Ω (00:L8)."""
    return -math.pi ** 2 / float(ln_omega)


def sigma(value, fit):
    """(value − fit)/error for fit = (centre, error)."""
    return (value - float(fit[0])) / float(fit[1])


def e_of_z(z, omega_l):
    """E(z) = H(z)/H₀ in flat ΛCDM, the rival chart's expansion rate: √((1 − Ω_Λ)(1 + z)³ + Ω_Λ)."""
    return math.sqrt((1 - omega_l) * (1 + z) ** 3 + omega_l)


def tully_fisher_shift(z, omega_l):
    """The Tully–Fisher zero-point at redshift z relative to z = 0 under the running floor: E(z)^{1/4} (00:P1)."""
    return e_of_z(z, omega_l) ** 0.25


# ---- certified brackets in rational arithmetic -------------------------------------------------------------------------
def _atan_bracket(x, n):
    """arctan(x) for 0 < x < 1 between consecutive partial sums of its alternating series: (lo, hi)."""
    s, term = Q(0), x
    sums = []
    for k in range(n + 2):
        s += (-1) ** k * term / (2 * k + 1)
        sums.append(s)
        term *= x * x
    a, b = sums[-2], sums[-1]
    return (min(a, b), max(a, b))


def pi_bracket(n=12):
    """π by Machin's formula, π = 16 arctan(1/5) − 4 arctan(1/239): (lo, hi) with lo < π < hi."""
    a_lo, a_hi = _atan_bracket(Q(1, 5), n)
    b_lo, b_hi = _atan_bracket(Q(1, 239), n)
    return (16 * a_lo - 4 * b_hi, 16 * a_hi - 4 * b_lo)


def exp_bracket(x, n=40):
    """e^x for a rational 0 ≤ x < n + 2: the Taylor sum to degree n and the sum plus the tail bound
    x^{n+1}/(n+1)! · (n+2)/(n+2−x)."""
    s, term = Q(0), Q(1)
    for k in range(n + 1):
        s += term
        term = term * x / (k + 1)
    return (s, s + term * Q(n + 2) / (n + 2 - x))


def tanh_octant_bracket():
    """tanh(3π/8) = (E − 1)/(E + 1) with E = e^{3π/4}, increasing in E: the bracket from those of π and exp."""
    p_lo, p_hi = pi_bracket()
    e_lo, e_hi = exp_bracket(3 * p_lo / 4)[0], exp_bracket(3 * p_hi / 4)[1]
    return ((e_lo - 1) / (e_lo + 1), (e_hi - 1) / (e_hi + 1))


def omega_lambda_bracket():
    t_lo, t_hi = tanh_octant_bracket()
    return (t_lo ** 2, t_hi ** 2)


def locus_bracket():
    (p_lo, p_hi), (t_lo, t_hi) = pi_bracket(), tanh_octant_bracket()
    return (p_lo / 4 / t_hi, p_hi / 4 / t_lo)


def hubble_bracket(age_gyr=AGE_GYR):
    """H₀ in km s⁻¹ Mpc⁻¹ on the locus at the octant depth: locus/t times the megaparsec in km."""
    lo, hi = locus_bracket()
    t = age_gyr * 10 ** 9 * JULIAN_YEAR
    return (lo / t * MPC_KM, hi / t * MPC_KM)


def floor_bracket(h0_kms=H0_ENTAILED):
    """a₀ = cH₀/2π in m s⁻² with H₀ = h0_kms km s⁻¹ Mpc⁻¹, decreasing in π."""
    p_lo, p_hi = pi_bracket()
    h = h0_kms / MPC_KM                   # s⁻¹ (km s⁻¹ over km)
    return (C_LIGHT * h / (2 * p_hi), C_LIGHT * h / (2 * p_lo))


def tilt_bracket(ln_omega=LN_OMEGA):
    """The magnitude π²/ln Ω of the tilt."""
    p_lo, p_hi = pi_bracket()
    return (p_lo ** 2 / ln_omega, p_hi ** 2 / ln_omega)


def _atanh_bracket(t, n):
    """artanh(t) for a rational 0 < t < 1: the partial sum of Σ t^{2k+1}/(2k+1) to n terms, and the sum plus the tail
    bound t^{2n+1}/((2n+1)(1 − t²))."""
    s, term = Q(0), t
    for k in range(n):
        s += term / (2 * k + 1)
        term *= t * t
    return (s, s + term / ((2 * n + 1) * (1 - t * t)))


def log_bracket(x, n=20):
    """ln x for a rational x > 0: 2 artanh((x − 1)/(x + 1)) from the artanh bracket; (lo, hi) with lo < ln x < hi."""
    t = (x - 1) / (x + 1)
    if t == 0: return (Q(0), Q(0))
    lo, hi = _atanh_bracket(abs(t), n)
    return (2 * lo, 2 * hi) if t > 0 else (-2 * hi, -2 * lo)


def log10_bracket():
    """ln 10 = 3 ln 2 + ln(5/4)."""
    (a, b), (c, d) = log_bracket(Q(2)), log_bracket(Q(5, 4))
    return (3 * a + c, 3 * b + d)


def sqrt_bracket(q, digits=40):
    """√q for a rational q > 0: the integer square root at `digits` decimals, (lo, hi) with lo ≤ √q < hi."""
    N = 10 ** digits
    n = math.isqrt(int(q * N * N))
    return (Q(n, N), Q(n + 1, N))


def horizon_radius_bracket(lam=LAMBDA_FIT):
    """r_H = c/H_Λ = √(3/Λ) in m: the de Sitter radius of the fit's Λ (14-entr's Λ face, instrument 1)."""
    return sqrt_bracket(3 / lam)


def hubble_lambda_bracket(lam=LAMBDA_FIT):
    """H_Λ = c√(Λ/3) in km s⁻¹ Mpc⁻¹."""
    lo, hi = sqrt_bracket(lam / 3)
    return (C_LIGHT * lo * MPC_KM, C_LIGHT * hi * MPC_KM)            # s⁻¹ times the megaparsec in km


def entropy_bracket(lam=LAMBDA_FIT, lp=PLANCK_LENGTH):
    """S = π (r_H/ℓ_P)² = 3π/(Λ ℓ_P²): the de Sitter entropy of the import, in Planck units; the bracket is π's."""
    p_lo, p_hi = pi_bracket()
    r2 = 3 / lam / lp ** 2
    return (p_lo * r2, p_hi * r2)


def omega_bracket(lam=LAMBDA_FIT, lp=PLANCK_LENGTH):
    """Ω = 4S + 1 on the chart."""
    lo, hi = entropy_bracket(lam, lp)
    return (4 * lo + 1, 4 * hi + 1)


def ln_omega_bracket(lam=LAMBDA_FIT, lp=PLANCK_LENGTH):
    """ln Ω = ln(Ω/10¹²³) + 123 ln 10, the mantissa's logarithm from the artanh series."""
    lo, hi = omega_bracket(lam, lp)
    (a, b), (c, d) = log_bracket(lo / 10 ** 123), log_bracket(hi / 10 ** 123)
    l10 = log10_bracket()
    return (a + 123 * l10[0], d + 123 * l10[1])


def entropy(lam=LAMBDA_FIT, lp=PLANCK_LENGTH):
    """S in floating point."""
    return math.pi * (math.sqrt(3 / float(lam)) / float(lp)) ** 2


def ln_omega(lam=LAMBDA_FIT, lp=PLANCK_LENGTH):
    """ln(4S + 1) in floating point."""
    return math.log(4 * entropy(lam, lp) + 1)


def show(x, spec):
    """A bracket end or a reading, printed: format(float(x), spec) (the exact tiers print through the chart)."""
    return format(float(x), spec)


def rate_error_bracket(age=STELLAR_AGE):
    """The age's error carried to the rate read on it: H₀ · σ_t/t over the bracket of H₀ (00:L3, 14:P3)."""
    lo, hi = hubble_bracket(age[0])
    return (lo * age[1] / age[0], hi * age[1] / age[0])


def ladder_pull_bracket(age_gyr=STELLAR_AGE[0]):
    """(H_ladder − H₀)/√(1.7² + 1.0²), the ladder's pull on the rate read on the stellar age, errors combined, over the
    bracket of H₀; the square root bracketed by (1.9723, 1.9724), whose squares straddle 3.89."""
    s_lo, s_hi = Q("1.9723"), Q("1.9724")
    assert s_lo ** 2 < H0_ERR ** 2 + LADDER_FIT[1] ** 2 < s_hi ** 2
    lo, hi = hubble_bracket(age_gyr)
    return ((LADDER_FIT[0] - hi) / s_hi, (LADDER_FIT[0] - lo) / s_lo)


def sigma_bracket(bracket, fit):
    """(value − fit)/error over a bracket of the value, the error positive."""
    return ((bracket[0] - fit[0]) / fit[1], (bracket[1] - fit[0]) / fit[1])
