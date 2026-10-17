"""frc.chart_flavour — the readings of 28-flavour against the continuum (the chart theme; 28-flavour's migration,
17 October 2026).

The chart theme holds the floats (frc/themes.py, rank 30). This file serves the continuum-comparison layer of the paper
28-flavour, whose ledger file frc/ledgers/p28_flavour.py decides every exact clause through frc/flavour.py and compares
these readings with rational bounds (it converts each float exactly, with Fraction). Each function computes what one
script of the paper's validation package (src/28-flavour) computes in floating point, with the same inputs: the
charged-lepton Koide value and the circulant data (a, r, δ) of each sector, the up-quark Koide value in three schemes,
the Georgi–Jarlskog dressing and double ratio, the cube invariants and the lock relations, the Gatto relation and its
phase, the effective Froggatt–Nielsen powers, the leading-order spectrum, the reactor-angle estimate, the TM2 relation
and its band, the lopsided split's two angles, the neutrino floor, the signed circulant on both orderings, the Majorana
band, the scale readings and the fine-structure anchor. The standard library only: the eigenvectors of a symmetric
3×3 matrix are computed by Jacobi rotations.

The measured constants are declared data (DATA), each table with its source: the masses as the validation suite states
them (PDG; the leptons to the PDG precision, the light quarks MS-bar at 2 GeV, m_c(m_c), m_b(m_b), the pole top), the
pole and MS-bar(M_Z) up sets of quark_amp.py and revision_checks.py, the NuFIT 6.0 splittings and angles (normal
ordering without Super-Kamiokande atmospheric data; the inverted |Δm²₃₂|), V_us, and the constants of scale_a.py and
alpha_probe.py.
"""
import math
from fractions import Fraction as Q

from frc import chart_fields as CF

# ---- declared data ------------------------------------------------------------------------------------------------------
DATA = {
    "leptons": dict(m_e=Q("0.51099895"), m_mu=Q("105.6583755"), m_tau=Q("1776.86")),                    # MeV, PDG
    "down": dict(m_d=Q("4.67"), m_s=Q("93.4"), m_b=Q("4180")),                                     # MeV, MS-bar 2 GeV, m_b(m_b)
    "up": dict(m_u=Q("2.16"), m_c=Q("1270"), m_t=Q("172570")),                                       # MeV, the working scheme
    "up_pole": dict(m_u=Q("2.2"), m_c=Q("1670"), m_t=Q("172800")),                                   # MeV, pole charm and top
    "up_mz": dict(m_u=Q("1.27"), m_c=Q("619"), m_t=Q("168300")),                                     # MeV, MS-bar at M_Z
    "ckm": dict(V_us=Q("0.2243"), lam_tier_b=Q("0.225"), sigma=Q("1.3")),                              # the Cabibbo parameter; tier_b's λ and σ
    "pmns": dict(s12sq=Q("0.307"), s13sq=Q("0.02215"), s13=Q("0.1488"), th13_deg=Q("8.57"),
                 th23_nosk=Q("48.5"), th23_sk=Q("43.3"), th23_lo=Q("41.0"), th23_hi=Q("50.6"),
                 dcp_sk_deg=Q("212")),                                                                 # NuFIT 6.0, normal ordering
    "nu": dict(dm21=Q("7.49e-5"), dm31=Q("2.513e-3"), dm32_io=Q("2.484e-3")),                         # eV², NuFIT 6.0
    "scales": dict(v=Q("246.22"), M_P=Q("1.22e19"), m_t=Q("172.57"), m_tau=Q("1.77686")),              # GeV
    "alpha": dict(alpha0_inv=Q("137.035999084"), m_P=Q("1.220890e19"), m_p=Q("0.9382720813"),
                  m_e=Q("0.51099895e-3"), b_em_sum=Q(32, 3)),                                        # GeV; b_em = (4/3)·Σ Q² N_c = (4/3)·8 over three generations
}

TWO_PI_THIRD = 2 * math.pi / 3
SQRT2, SQRT3, FOUR_PI = math.sqrt(2), math.sqrt(3), 4 * math.pi        # the continuum constants the ledger file compares with


def _f(x): return float(x)


def _masses(table):
    return [_f(v) for v in DATA[table].values()]


# ---- the Koide value and the circulant data of a sector ----------------------------------------------------------------
def koide(masses):
    a = [math.sqrt(m) for m in masses]
    return sum(masses) / sum(a) ** 2


def circulant_data(masses):
    """(Q, a, r, δ) of a sector: a = Σ√m/3, r = √(6Q − 2), δ from √m_heaviest = a(1 + r cos δ) (the heaviest at k = 0,
    the lightest at k = 1, the middle at k = 2)."""
    s = [math.sqrt(m) for m in masses]
    a = sum(s) / 3
    Qv = koide(masses)
    r = math.sqrt(6 * Qv - 2)
    delta = math.acos((s[2] / a - 1) / r)
    return Qv, a, r, delta


def spectrum_check(masses):
    """The reconstruction √m_k = a(1 + r cos(δ + 2πk/3)) for k = (1, 2, 0) against the three √m (the largest deviation)."""
    Qv, a, r, d = circulant_data(masses)
    pred = [a * (1 + r * math.cos(d + TWO_PI_THIRD * k)) for k in (1, 2, 0)]
    return max(abs(p - math.sqrt(m)) for p, m in zip(pred, masses))


def koide_measured():
    """(Q_ℓ, Q_ℓ − 2/3, dQ/dm_τ per MeV, ρ, the democratic angle in degrees, r, δ_ℓ, a² in MeV)."""
    m = _masses("leptons")
    Qv, a, r, d = circulant_data(m)
    h = 1e-3
    dQ = (koide([m[0], m[1], m[2] + h]) - koide([m[0], m[1], m[2] - h])) / (2 * h)
    s = [math.sqrt(x) for x in m]
    rho = math.sqrt(max(3 * sum(x * x for x in s) - sum(s) ** 2, 0) / 2) / sum(s)
    angle = math.degrees(math.acos(sum(s) / math.sqrt(3 * sum(x * x for x in s))))
    return Qv, Qv - 2 / 3, dQ, rho, angle, r, d, a * a


def lepton_spectrum_residual():
    """The largest deviation of the circulant reconstruction from the three measured √m of the charged leptons."""
    return spectrum_check(_masses("leptons"))


def electron_prediction():
    """m_e from m_μ, m_τ with r = √2 exactly: a and δ solved from the two heavier masses, the electron the k = 1 root."""
    me, mmu, mtau = _masses("leptons")
    target = math.sqrt(mmu / mtau)
    lo, hi = 0.0, math.pi / 3
    f = lambda d: (1 + math.sqrt(2) * math.cos(d + 2 * TWO_PI_THIRD)) / (1 + math.sqrt(2) * math.cos(d)) - target
    for _ in range(200):                              # bisection: f increases with δ on (0, π/3)
        mid = (lo + hi) / 2
        if f(mid) < 0: lo = mid
        else: hi = mid
    d = (lo + hi) / 2
    a = math.sqrt(mtau) / (1 + math.sqrt(2) * math.cos(d))
    return (a * (1 + math.sqrt(2) * math.cos(d + TWO_PI_THIRD))) ** 2, d


def up_schemes():
    """Q_u in the working scheme, with pole masses and MS-bar at M_Z; r_u in the working and pole schemes."""
    out = {}
    for key in ("up", "up_pole", "up_mz"):
        Qv, a, r, d = circulant_data(_masses(key))
        out[key] = (Qv, r, d)
    return out


def down_sector():
    """(Q_d, r_d, δ_d) and the Georgi–Jarlskog-dressed lepton spectrum's Q (3m_e, m_μ/3, m_τ)."""
    Qd, a, rd, dd = circulant_data(_masses("down"))
    me, mmu, mtau = _masses("leptons")
    return Qd, rd, dd, koide([3 * me, mmu / 3, mtau])


def phase_lock():
    """(δ_ℓ, δ_d, δ_u, δ_u with the pole charm mass): the lock 1 : 1/2 : 1/3 in the working scheme, 0.388 pole."""
    dl = circulant_data(_masses("leptons"))[3]
    dd = circulant_data(_masses("down"))[3]
    du = circulant_data(_masses("up"))[3]
    dup = circulant_data(_masses("up_pole"))[3]
    return dl, dd, du, dup


def cube_invariants():
    """c = cos 3δ of each sector from its masses through the circulant determinant: ∏√m = a³ + 2|b|³ c − 3a|b|², with
    a = Σ√m/3 and |b| = ra/2; returns (c_ℓ, c_d, c_u)."""
    out = []
    for key in ("leptons", "down", "up"):
        m = _masses(key); s = [math.sqrt(x) for x in m]
        Qv, a, r, d = circulant_data(m)
        b = r * a / 2
        out.append((s[0] * s[1] * s[2] - a ** 3 + 3 * a * b * b) / (2 * b ** 3))
    return tuple(out)


# ---- the texture, Gatto and Georgi–Jarlskog ------------------------------------------------------------------------------
def gatto():
    """(√(m_d/m_s), √(m_u/m_c), the relation at φ = π/2, the band ends at φ = 0 and φ = π, the φ in degrees solving
    |√(m_d/m_s) − e^{iφ}√(m_u/m_c)| = V_us)."""
    md, ms, mb = _masses("down"); mu, mc, mt = _masses("up"); Vus = _f(DATA["ckm"]["V_us"])
    x, y = math.sqrt(md / ms), math.sqrt(mu / mc)
    at90 = math.sqrt(x * x + y * y)
    # |x − y e^{iφ}|² = x² + y² − 2xy cos φ = V_us²
    c = (x * x + y * y - Vus * Vus) / (2 * x * y)
    phi = math.degrees(math.acos(max(-1.0, min(1.0, c))))
    return x, y, at90, (abs(x - y), x + y), phi


def effective_powers():
    """log(m_i/m_3)/log λ for the down, lepton and up sectors at λ = V_us."""
    lam = _f(DATA["ckm"]["V_us"])
    out = {}
    for key in ("down", "leptons", "up"):
        m = _masses(key)
        out[key] = (math.log(m[0] / m[2]) / math.log(lam), math.log(m[1] / m[2]) / math.log(lam))
    return out


def gj_double_ratio():
    me, mmu, mtau = _masses("leptons"); md, ms, mb = _masses("down")
    return (mmu / me) / (ms / md), ms / md, mtau / mb


def lo_ratio():
    """(7 − 4√3, the observed m_μ/m_τ)."""
    me, mmu, mtau = _masses("leptons")
    return 7 - 4 * math.sqrt(3), mmu / mtau


# ---- the mixing ----------------------------------------------------------------------------------------------------------
def theta13():
    """(sin θ_C/√2, the measured sin θ₁₃, the excess, θ₁₂ + θ_C in degrees)."""
    d = DATA["pmns"]; Vus = _f(DATA["ckm"]["V_us"])
    est = Vus / math.sqrt(2); s13 = _f(d["s13"])
    th12 = math.degrees(math.asin(math.sqrt(_f(d["s12sq"])))); thC = math.degrees(math.asin(Vus))
    return est, s13, est / s13 - 1, th12 + thC


def tm2_cos(th13_deg, th23_deg):
    """cos δ_CP = cot 2θ₂₃ (1 − 2s₁₃²)/(s₁₃ √(2 − 3s₁₃²)), the TM2 relation (eq. tm2 of the paper)."""
    s = math.sin(math.radians(th13_deg)); t = math.radians(th23_deg)
    return (math.cos(2 * t) / math.sin(2 * t)) * (1 - 2 * s * s) / (s * math.sqrt(2 - 3 * s * s))


def tm2_readings():
    """|δ_CP| in degrees at θ₂₃ = 45°, the NuFIT 6.0 best fits without and with atmospheric data, 49°; the band over the
    3σ range; the drive-sign band (204°, 310°); the exact-TM2 solar value."""
    d = DATA["pmns"]; t13 = _f(d["th13_deg"])
    deg = lambda c: math.degrees(math.acos(max(-1.0, min(1.0, c))))
    at = {lab: deg(tm2_cos(t13, th)) for lab, th in (("45", 45.0), ("48.5", _f(d["th23_nosk"])), ("49", 49.0), ("43.3", _f(d["th23_sk"])))}
    lo, hi = _f(d["th23_lo"]), _f(d["th23_hi"])
    band = [deg(tm2_cos(t13, lo + (hi - lo) * k / 400)) for k in range(401)]
    solar = 1 / (3 * (1 - _f(d["s13sq"])))
    signs = (tm2_cos(t13, _f(d["th23_sk"])) > 0, math.cos(math.radians(_f(d["dcp_sk_deg"]))) < 0)
    return at, (min(band), max(band)), (360 - max(band), 360 - min(band)), solar, signs


def _jacobi_eig(H, sweeps=60):
    """Eigenvalues (ascending) and eigenvectors (columns) of a real symmetric 3×3 matrix by Jacobi rotations."""
    A = [row[:] for row in H]; V = [[1.0 if i == j else 0.0 for j in range(3)] for i in range(3)]
    for _ in range(sweeps):
        off = sum(A[i][j] ** 2 for i in range(3) for j in range(3) if i != j)
        if off < 1e-30: break
        for p in range(3):
            for q in range(p + 1, 3):
                if abs(A[p][q]) < 1e-300: continue
                theta = (A[q][q] - A[p][p]) / (2 * A[p][q])
                t = (1 if theta >= 0 else -1) / (abs(theta) + math.sqrt(theta * theta + 1))
                c = 1 / math.sqrt(t * t + 1); s = t * c
                for k in range(3):
                    akp, akq = A[k][p], A[k][q]
                    A[k][p], A[k][q] = c * akp - s * akq, s * akp + c * akq
                for k in range(3):
                    apk, aqk = A[p][k], A[q][k]
                    A[p][k], A[q][k] = c * apk - s * aqk, s * apk + c * aqk
                for k in range(3):
                    vkp, vkq = V[k][p], V[k][q]
                    V[k][p], V[k][q] = c * vkp - s * vkq, s * vkp + c * vkq
    order = sorted(range(3), key=lambda i: A[i][i])
    return [A[i][i] for i in order], [[V[k][i] for i in order] for k in range(3)]


def _mm(A, B): return [[sum(A[i][k] * B[k][j] for k in range(3)) for j in range(3)] for i in range(3)]
def _tr(A): return [[A[j][i] for j in range(3)] for i in range(3)]


def lopsided():
    """tier_b's lopsided mechanism at λ = 0.225, σ = 1.3: M_d with σ in the (3,2) slot, M_u diagonal; the CKM θ₂₃ from
    the left rotations of M_u and M_d, the PMNS θ₂₃ from the left rotation of M_e = M_dᵀ, the hidden right angle of M_d.
    Returns (θ_CKM23, θ_PMNS23, θ_right) in degrees."""
    lam = _f(DATA["ckm"]["lam_tier_b"]); sig = _f(DATA["ckm"]["sigma"])
    Md = [[lam ** 4, lam ** 3, 0.0], [lam ** 3, lam ** 2, 0.0], [0.0, sig, 1.0]]
    Mu = [[lam ** 8, 0.0, 0.0], [0.0, lam ** 4, 0.0], [0.0, 0.0, 1.0]]
    left = lambda M: _jacobi_eig(_mm(M, _tr(M)))[1]
    right = lambda M: _jacobi_eig(_mm(_tr(M), M))[1]
    th23 = lambda U: math.degrees(math.atan2(abs(U[1][2]), abs(U[2][2])))
    return th23(_mm(_tr(left(Mu)), left(Md))), th23(left(_tr(Md))), th23(right(Md))


# ---- the neutrinos --------------------------------------------------------------------------------------------------------
def neutrino_floor():
    """√Δm²₂₁ + √Δm²₃₁ in meV at NuFIT 6.0 (the m₁ = 0 floor), with the two square roots."""
    d = DATA["nu"]
    m2, m3 = math.sqrt(_f(d["dm21"])), math.sqrt(_f(d["dm31"]))
    return 1e3 * (m2 + m3), 1e3 * m2, 1e3 * m3


def _amps(delta): return [1 + math.sqrt(2) * math.cos(delta + TWO_PI_THIRD * k) for k in range(3)]


def signed_circulant(inverted=False, n=720000):
    """The signed circulant with r = √2 solving the two measured splittings: √m_k = A(1 + √2 cos(δ + 2πk/3)), one
    amplitude negative. Returns (δ_ν, the masses in meV ascending, Σm_ν in meV, the signed Q, the positive-root Q, the
    lightest amplitude 1 + √2 cos θ, the distance in radians of the lightest state's angle from the zero at 3π/4)."""
    d = DATA["nu"]; dm21 = _f(d["dm21"])
    big = _f(d["dm32_io"]) if inverted else _f(d["dm31"])    # IO: m₂² − m₃² = |Δm²₃₂|; NO: m₃² − m₁² = Δm²₃₁
    target = dm21 / big
    best = None
    for i in range(n):
        delta = i * 2 * math.pi / n
        v = _amps(delta); m = sorted(x * x for x in v)
        if inverted: num, den = m[2] ** 2 - m[1] ** 2, m[2] ** 2 - m[0] ** 2       # (m₂² − m₁²)/(m₂² − m₃²)
        else: num, den = m[1] ** 2 - m[0] ** 2, m[2] ** 2 - m[0] ** 2             # (m₂² − m₁²)/(m₃² − m₁²)
        if den <= 0: continue
        err = abs(num / den - target)
        if best is None or err < best[0]: best = (err, delta, v)
    _, delta, v = best
    m = [x * x for x in v]; s = sorted(m)
    scale = math.sqrt(big / (s[2] ** 2 - s[0] ** 2))
    masses = sorted(1e3 * x * scale for x in m)
    amps = [x * math.sqrt(scale) for x in v]
    Qs = sum(x * x for x in amps) / sum(amps) ** 2
    Qpos = sum(x * x for x in amps) / sum(abs(x) for x in amps) ** 2
    k = min(range(3), key=lambda j: v[j] * v[j])
    angle = (delta + TWO_PI_THIRD * k) % (2 * math.pi)
    return delta % TWO_PI_THIRD, masses, sum(masses), Qs, Qpos, v[k], abs(angle - 3 * math.pi / 4)


def majorana_band(m1_meV=0.0):
    """The two terms c₁₃² s₁₂² m₂ and s₁₃² m₃ (meV) at the floor masses, the band |t₂ ± t₃| with the m₁ term, over the
    Majorana phases: (t₁, t₂, t₃, low, high)."""
    d = DATA["pmns"]; s12sq, s13sq = _f(d["s12sq"]), _f(d["s13sq"])
    _, m2, m3 = neutrino_floor()
    t1 = (1 - s13sq) * (1 - s12sq) * m1_meV; t2 = (1 - s13sq) * s12sq * m2; t3 = s13sq * m3
    return t1, t2, t3, abs(t2 - t3) - t1, t1 + t2 + t3


# ---- the scales and the fine-structure anchor ---------------------------------------------------------------------------------
def scales():
    """(ln(M_P/v), y_t = √2 m_t/v, y_τ = √2 m_τ/v, the lepton scale a² in MeV from the charged leptons)."""
    d = {k: _f(v) for k, v in DATA["scales"].items()}
    a2 = koide_measured()[7]
    return math.log(d["M_P"] / d["v"]), math.sqrt(2) * d["m_t"] / d["v"], math.sqrt(2) * d["m_tau"] / d["v"], a2


def alpha_anchor():
    """(4π, α_GUT⁻¹ at the one-loop α₁ = α₂ scale of 27-fields' p1 data, that scale in GeV, the one-loop fermion sum
    Δα⁻¹ = (b_em/2π) ln(M_P/m_e) added to 4π, the EM/gravity hierarchy α (m_P/m_p)²)."""
    d = {k: _f(v) for k, v in DATA["alpha"].items()}
    mu_U = CF.unification_scale()
    p1 = CF.DATA["p1"]
    a1_inv_MZ = 0.6 * (1 - _f(p1["sin2"])) * _f(p1["ainv_em"])
    b1 = _f(p1["b"][0])
    a_gut_inv = a1_inv_MZ - b1 / (2 * math.pi) * math.log(mu_U / _f(p1["M_Z"]))
    dalpha = d["b_em_sum"] / (2 * math.pi) * math.log(d["m_P"] / d["m_e"])
    hier = (1 / d["alpha0_inv"]) * (d["m_P"] / d["m_p"]) ** 2
    return 4 * math.pi, a_gut_inv, mu_U, dalpha, hier
