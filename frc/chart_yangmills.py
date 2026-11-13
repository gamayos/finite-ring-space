"""frc.chart_yangmills — the chart theme's readings of 46-yangmills (7–8 November 2026): the measured colour factors of LEP
against the frame's Casimirs, the one-loop run of the strong coupling between laboratory scales, the lattice anchors of the
pure-gauge sector (the glueball mass in units of √σ by three determinations, the deconfinement temperature), the tensions
as logarithms of the exact plaquette coefficients, and the chart's relativistic wrap operator of 35-hadrons C17 with its
family of kinetic multiplicities and tensions. Everything in this file is a chart reading [chart] or an import [import].

Standard library only. Every measured number is a declared rational with its uncertainty; the one-loop run uses the
logarithm of the chart (a float) and is compared through exact conversion. The one Ω-hard scale √σ enters nowhere in this
file as a numeral: the anchors are ratios.

    LEP                                   C_A, C_F (four-jet angular correlations) and C_A/C_F (jet multiplicities), with errors
    LATTICE                               m(0⁺⁺)/T_c, T_c/√σ for SU(3) and SU(2), the glueball ladder r₀m, r₀√σ, the direct continuum m(0⁺⁺)/√σ
    m0pp_determinations()                 the determinations of m(0⁺⁺)/√σ: the r₀ route with two inputs, 3.70(6) and 3.63(10), and the direct 3.405(21)
    ALPHA_S                               α_s(M_Z) (world average) and α_s(m_τ) (τ decays), the quark-mass thresholds
    within(value, centre, error, k)       |value − centre| ≤ k·error, exactly
    one_loop(alpha0, mu0, mu, nf_steps)   1/α(μ) = 1/α(μ₀) + (b₀(n_f)/2π) ln(μ/μ₀) piecewise across the thresholds
    run_to_tau()                          α_s(M_Z) → α_s(m_b) → α_s(m_τ) at one loop, the e-fold counts of each step
    b1(nf), two_loop(...), run_to_tau_two_loop()   the imported two-loop coefficient and the two-loop run (a chart reading)
    wrap_spectrum(a, kappa, k, N, L)      the lowest k eigenvalues of the chart operator a|p| + ϰ r on N sites (35-hadrons C17's construction)
    wrap_family()                         the candidate operators of D5 against the three lattice determinations [chart]
    short_range_route(), plaquette_channel()   the two chart routes of the former task T01, both failing (8 November 2026) [chart]
    adjoint_ratio(theta)                  the chart's tension ratio σ₈/σ₃ = ln c₈ / ln c₃ at the stiffness ϑ of a cell
"""
import math
from fractions import Fraction as Q

from frc import yangmills as Y

LEP = dict(C_A=(Q("2.89"), Q("0.21")), C_F=(Q("1.30"), Q("0.09")), ratio=(Q("2.22"), Q("0.11")),
           source="Kluth, QCD studies at LEP, hep-ex/0406058 (the combined four-jet fits; DELPHI's multiplicity ratio)")

LATTICE = dict(m0pp_over_Tc=(Q("5.73"), Q("0.09")),                # Hasenbusch–Necco, hep-lat/0409067, eq. (7): an average of literature r₀m through T_c r₀ = 0.7498(50)
               Tc_over_sqrt_sigma_su3=(Q("0.6462"), Q("0.0030")),  # Lucini–Teper–Wenger, JHEP 01 (2004) 061 (hep-lat/0307017), Table 6
               Tc_over_sqrt_sigma_su2=(Q("0.7091"), Q("0.0036")),
               r0m=dict(scalar=(Q("4.21"), Q("0.11")), tensor=(Q("5.85"), Q("0.02")), pseudoscalar=(Q("6.33"), Q("0.07"))),   # Morningstar–Peardon, r₀ m
               r0_sqrt_sigma=(Q("1.160"), Q("0.006")),             # Athenodorou–Teper, JHEP 11 (2020) 172, √σ = 1.160(6)/r₀
               m0pp_over_sqrt_sigma_direct=(Q("3.405"), Q("0.021")),   # Athenodorou–Teper 2020, the continuum extrapolation in a²σ
               m0pp_star_direct=(Q("5.855"), Q("0.041")))              # Athenodorou–Teper 2020, Table 17: the first scalar excitation, m/√σ

ALPHA_S = dict(MZ=(Q("0.1180"), Q("0.0009")), mtau=(Q("0.312"), Q("0.015")),
               scales=dict(MZ=Q("91.1876"), mb=Q("4.18"), mtau=Q("1.77686")))


def fmt(x, nd=3):
    """A rational or float as a decimal string with nd digits (the chart tier formats; the exact tier calls no float)."""
    return f"{float(x):.{nd}f}"


def m0pp_over_sqrt_sigma():
    """m(0⁺⁺)/√σ = (m/T_c)(T_c/√σ) for SU(3), with the error propagated in quadrature on the relative errors (a chart reading)."""
    (a, da), (b, db) = LATTICE["m0pp_over_Tc"], LATTICE["Tc_over_sqrt_sigma_su3"]
    v = a * b
    rel = math.sqrt(float(da / a) ** 2 + float(db / b) ** 2)
    return v, Q(repr(rel)) * v


def m0pp_determinations():
    """The lattice determinations of m(0⁺⁺)/√σ for SU(3), each a chart reading with its own error: the product
    (m/T_c)(T_c/√σ) = 3.70(6) (Hasenbusch–Necco's 5.73(9), itself an average of literature r₀m through T_c r₀ = 0.7498, times
    LTW's 0.6462(30)); the r₀ route r₀m / r₀√σ = 4.21(11)/1.160(6) = 3.63(10) (Morningstar–Peardon); the direct continuum
    extrapolation 3.405(21) (Athenodorou–Teper 2020). Since 0.7498/0.6462 = 1.160, the first two share r₀√σ and differ only in
    the r₀m input: two independent routes, the r₀ route with two inputs and the direct one. They spread over 9 %, far beyond the
    quoted errors; no single one is the bracket (the audit of 8 November 2026)."""
    v, dv = m0pp_over_sqrt_sigma()
    (a, da), (b, db) = LATTICE["r0m"]["scalar"], LATTICE["r0_sqrt_sigma"]
    r = a / b; dr = Q(repr(math.sqrt(float(da / a) ** 2 + float(db / b) ** 2))) * r
    d, dd = LATTICE["m0pp_over_sqrt_sigma_direct"]
    return dict(via_Tc=(v, dv), via_r0=(r, dr), direct=(d, dd))


def glueball_ladder():
    """The lattice ratios m(2⁺⁺)/m(0⁺⁺) and m(0⁻⁺)/m(0⁺⁺) from the r₀ masses."""
    s, t, p = (LATTICE["r0m"][k][0] for k in ("scalar", "tensor", "pseudoscalar"))
    return t / s, p / s


def within(value, centre, error, k=1):
    """|value − centre| ≤ k·error, every operand exact."""
    return abs(Q(value) - Q(centre)) <= k * Q(error)


def one_loop(alpha0, mu0, mu, steps):
    """1/α(μ) = 1/α(μ₀) + Σ (b₀(n_f)/2π) ln(μ_{i+1}/μ_i) across the thresholds `steps` = [(n_f, μ_end), …] from μ₀ down to μ.
    Returns α(μ) and the list of e-fold counts ln(μ_i/μ_{i+1})."""
    inv = 1.0 / float(alpha0); cur = float(mu0); efolds = []
    for nf, end in steps:
        end = float(end); e = math.log(cur / end); efolds.append(e)
        inv -= float(Y.b0(nf)) / (2 * math.pi) * e; cur = end
    return 1.0 / inv, efolds


def b1(nf, N=3):
    """[import] The two-loop coefficient b₁ = (34/3)C_A² − (20/3)C_A T_F n_f − 4C_F T_F n_f = 102 − 38n_f/3 for SU(3): the chart's,
    imported beside b₀'s form (46:A4); nothing of it is derived here."""
    return Q(102) - Q(38, 3) * nf


def two_loop(alpha0, mu0, mu, steps, n=4000):
    """α(μ) from the chart's two-loop equation dα/d ln μ = −(b₀/2π)α² − (b₁/8π²)α³, integrated by a fourth-order Runge–Kutta step
    in ln μ across the thresholds `steps` = [(n_f, μ_end), …] from μ₀ down to μ (a chart reading; the one-loop law is one_loop)."""
    a = float(alpha0); cur = float(mu0)
    for nf, end in steps:
        end = float(end); b0 = float(Y.b0(nf)); bb1 = float(b1(nf))
        t0, t1 = math.log(cur), math.log(end); h = (t1 - t0) / n
        f = lambda x: -(b0 / (2 * math.pi)) * x * x - (bb1 / (8 * math.pi ** 2)) * x ** 3
        for _ in range(n):
            k1 = f(a); k2 = f(a + h * k1 / 2); k3 = f(a + h * k2 / 2); k4 = f(a + h * k3)
            a += h * (k1 + 2 * k2 + 2 * k3 + k4) / 6
        cur = end
    return a


def run_to_tau_two_loop():
    """α_s(M_Z) = 0.1180 → α_s(m_b) → α_s(m_τ) at two loops with the imported b₁: 0.224 and 0.313 against the τ-decay 0.312(15)."""
    s = ALPHA_S["scales"]
    a_b = two_loop(ALPHA_S["MZ"][0], s["MZ"], s["mb"], [(5, s["mb"])])
    a_t = two_loop(ALPHA_S["MZ"][0], s["MZ"], s["mtau"], [(5, s["mb"]), (4, s["mtau"])])
    return dict(alpha_mb=a_b, alpha_mtau=a_t, measured_mtau=ALPHA_S["mtau"])


def run_to_tau():
    """α_s(M_Z) = 0.1180 → α_s(m_b) (n_f = 5) → α_s(m_τ) (n_f = 4) at one loop; the τ-decay value for comparison."""
    s = ALPHA_S["scales"]
    a_b, e1 = one_loop(ALPHA_S["MZ"][0], s["MZ"], s["mb"], [(5, s["mb"])])
    a_t, e2 = one_loop(ALPHA_S["MZ"][0], s["MZ"], s["mtau"], [(5, s["mb"]), (4, s["mtau"])])
    return dict(alpha_mb=a_b, alpha_mtau=a_t, efolds=e2, measured_mtau=ALPHA_S["mtau"])


# ---------------------------------------------------------------- Phase 2: the minimal wrap (study §7, decision D5)
GLUEBALL_LATTICE = dict(m0pp_star_r0=(Q("6.50"), Q("0.44")),       # Morningstar–Peardon, r₀ m(0⁺⁺*), the first radial excitation
                        m0pp_r0=(Q("4.21"), Q("0.11")))


def wrap_spectrum(a=1, kappa=1, k=3, N=600, L=30, m=48, C=0.0, rc=1.0):
    """[chart] The lowest k eigenvalues of the chart's relativistic wrap operator H = a|p| + ϰ r — the one-body operator of
    35-hadrons C17 (a continuum operator on the half-line, read on N sites of [0, L] with Dirichlet ends) with the kinetic
    multiplicity a and the tension ϰ as parameters: |p| = T^{1/2} diagonal in the sine basis of the finite-difference Laplacian,
    r through the sine transform, a Lanczos iteration of depth m with full reorthogonalisation and bisection on the small
    tridiagonal (chart_hadrons.relativistic_ground). E₀(1, 1) = 2.232 is the nucleon's scale (35-hadrons C17). Nothing in the
    operator is a frame object; the frame enters only through the tension ϰ (yangmills.adjoint_over_fundamental_squared).
    With C > 0 the short-range term −C/max(r, r_c) is added (the T01 route (a) of 8 November 2026): the Coulomb law with the
    cutoff r_c in units of 1/√σ, the shadow of the finite Green's function of 27-fields C3."""
    h = L / (N + 1)
    pk = [a * 2 * math.sin(math.pi * j / (2 * (N + 1))) / h for j in range(1, N + 1)]
    c0 = math.sqrt(2 / (N + 1))
    S = [[c0 * math.sin(i * j * math.pi / (N + 1)) for j in range(1, N + 1)] for i in range(1, N + 1)]
    xs = [kappa * j * h - (C / max(j * h, rc) if C else 0.0) for j in range(1, N + 1)]
    def matvec(c):
        v = [sum(map(float.__mul__, row, c)) for row in S]
        v = [x * y for x, y in zip(xs, v)]
        w = [sum(map(float.__mul__, row, v)) for row in S]
        return [p * q + r for p, q, r in zip(pk, c, w)]
    q = [1.0 / math.sqrt(N)] * N; Qs = [q]; alpha = []; beta = []
    for _ in range(m):
        w = matvec(Qs[-1]); al = sum(x * y for x, y in zip(w, Qs[-1])); alpha.append(al)
        for qq in Qs:
            d_ = sum(x * y for x, y in zip(w, qq)); w = [x - d_ * y for x, y in zip(w, qq)]
        bn = math.sqrt(sum(x * x for x in w))
        if bn < 1e-12: break
        beta.append(bn); Qs.append([x / bn for x in w])
    n = len(alpha); off2 = [b * b for b in beta]
    def cnt(lam):
        c_, qv = 0, 1.0
        for i in range(n):
            qv = alpha[i] - lam - (off2[i - 1] / qv if i else 0.0)
            if qv == 0.0: qv = -1e-300
            if qv < 0: c_ += 1
        return c_
    def kth(j):
        lo, hi = -100.0, 100.0
        for _ in range(60):
            mid = (lo + hi) / 2
            if cnt(mid) > j: hi = mid
            else: lo = mid
        return (lo + hi) / 2
    return [kth(j) for j in range(k)]


def alpha_s_one_loop(mu_over_sqrt_sigma, b0=9, lam_ratio=2):
    """[chart] The one-loop coupling of 35-hadrons at the scale μ, α_s(μ) = 2π/(b₀ ln(μ/Λ)) with b₀ = 9 and √σ/Λ = 2
    (chart_hadrons.DATA['scales']): α_s(√σ) = 1.007 at the one scale, the transmutation value."""
    return 2 * math.pi / (b0 * math.log(lam_ratio * mu_over_sqrt_sigma))


HERBST = {1: 2 / math.pi, 2: 4 / math.pi}        # a|p| − C/r is bounded below iff C ≤ 2a/π (Herbst 1977; Kato's inequality)


def short_range_route(cutoffs=(1.0, 0.5, 0.25), a=2, kappa=2.0, CA=3, N=240, L=18, m=40):
    """[chart] T01 route (a): the two-adjoint operator a|p| + ϰ r − C/max(r, r_c) with the colour factor C_A = 3 and the frame's
    one-loop coupling read at the bound state's own mass, C = C_A α_s(E₀√σ), solved self-consistently (secant on
    g(E) = E₀(C(E)) − E) for each cutoff; and the declared coupling at the one scale, C = C_A α_s(√σ) = 3.02, at r_c = 1.
    Returns the Herbst bounds, the collapse value, and (E₀, C) per cutoff or None where the iteration runs away (E₀ ≤ Λ/√σ = 1/2,
    where the one-loop law has no value). The result of 8 November 2026: 3.54, 3.09, 2.61 at r_c = 1, 1/2, 1/4 and no fixed
    point at 1/8 — the eigenvalue is the cutoff's, and the cell's size in units of 1/√σ is set by the stiffness of the cell."""
    def ground(C, rc): return wrap_spectrum(a, kappa, 1, N, L, m, C, rc)[0]
    declared = CA * alpha_s_one_loop(1.0)
    out = dict(herbst=dict(HERBST), declared_coupling=declared, collapse_rc1=ground(declared, 1.0), fixed_points={})
    for rc in cutoffs:
        def g(Ev): return ground(CA * alpha_s_one_loop(Ev), rc) - Ev
        E0, E1 = 3.5, 3.3
        try:
            g0, g1 = g(E0), g(E1); sol = None
            for _ in range(12):
                if abs(g1) < 2e-4: sol = E1; break
                if g1 == g0: break
                E2 = E1 - g1 * (E1 - E0) / (g1 - g0)
                if E2 <= 0.55: break                                    # below Λ/√σ: the law has no value, the iteration has run away
                E0, g0, E1 = E1, g1, E2; g1 = g(E1)
            out["fixed_points"][rc] = (sol, CA * alpha_s_one_loop(sol)) if sol else None
        except ValueError:                                              # log of a non-positive argument: run away
            out["fixed_points"][rc] = None
    return out


def fixed_point_bisect(a, kappa, rc, lo, hi, CA=3, N=240, L=18, m=40, steps=30):
    """[chart] The self-consistent bound state of a|p| + ϰr − C/max(r, r_c) with C = C_A α_s(E₀√σ): the root of g(E) = E₀(C(E)) − E
    bracketed in [lo, hi] by bisection (the secant of short_range_route finds one root; this finds the one in a given bracket),
    or None when g has one sign at both ends (the review of 8 November 2026: a failing iteration is not a proof of no root)."""
    def g(E): return wrap_spectrum(a, kappa, 1, N, L, m, CA * alpha_s_one_loop(E), rc)[0] - E
    glo, ghi = g(lo), g(hi)
    if (glo > 0) == (ghi > 0): return None
    for _ in range(steps):
        mid = (lo + hi) / 2; gm = g(mid)
        if (gm > 0) == (glo > 0): lo, glo = mid, gm
        else: hi = mid
    return (lo + hi) / 2


def short_range_review():
    """[chart] The numbers of 46:C10 after the review of 8 November 2026, every value an exact rational of its float and every key a
    string, so that the ledger file (an exact tier, gate G09) handles no float: the declared coupling C = C_A α_s(√σ) and the two-body
    Herbst value 4/π; the ground energy of 2|p| + 2r − C/max(r, r_c) at r_c = 1, 1/2, 1/4, 1/8 cells with the declared coupling, each
    above the elementary bound −C/r_c; the two-body fixed points with the running coupling (the upper root by the secant of
    short_range_route, the lower by bisection) at r_c = 1, 1/2, 1/4 and none at 1/8; the maximum of g(E) on a scan of 149 energies
    E ∈ [0.6, 8] (step 0.05) at 1/8, the energy at which it is reached and the count (a sampled finding, no theorem of no root;
    the review of 8 November 2026, second round); the one-body form's roots at r_c = 2 and 10 and none found at one cell."""
    r = short_range_route(cutoffs=(1.0, 0.5, 0.25, 0.125)); dc = r["declared_coupling"]
    def q(x): return None if x is None else Q(repr(float(x)))
    rcs = {"1": 1.0, "1/2": 0.5, "1/4": 0.25, "1/8": 0.125}
    collapse = {k: q(wrap_spectrum(2, 2.0, 1, 240, 18, 40, dc, rc)[0]) for k, rc in rcs.items()}
    fixed = {k: ((q(v[0]), q(v[1])) if v else None) for k, v in ((k, r["fixed_points"][rc]) for k, rc in rcs.items())}
    low = {k: q(fixed_point_bisect(2, 2.0, rc, lo, hi)) for k, rc, lo, hi in (("1", 1.0, 0.6, 1.0), ("1/2", 0.5, 0.9, 1.5), ("1/4", 0.25, 1.5, 2.0))}
    energies = [Q(6, 10) + Q(k, 20) for k in range(149)]                                      # 0.6, 0.65, …, 8.0
    scan = [wrap_spectrum(2, 2.0, 1, 240, 18, 40, 3 * alpha_s_one_loop(float(E)), 0.125)[0] - float(E) for E in energies]
    i_max = max(range(len(scan)), key=lambda i: scan[i])
    one = {k: q(fixed_point_bisect(1, 2.0, rc, lo, hi)) for k, rc, lo, hi in (("2", 2.0, 2.5, 3.0), ("10", 10.0, 3.0, 3.5), ("1", 1.0, 0.6, 8.0))}
    return dict(declared=q(dc), herbst_two=q(r["herbst"][2]), collapse_rc1=q(r["collapse_rc1"]), collapse=collapse, fixed=fixed, low=low,
                scan_max=q(scan[i_max]), scan_at=energies[i_max], scan_n=len(scan), one=one, bound={k: -q(dc) / Q(k) for k in rcs})


MUNSTER_0PP = [Q(0), Q(-3), Q(9), Q(-27, 2), Q(-7), Q(-297, 2), Q(858827, 10240), Q(47641149, 71680)]
# [import] the SU(3) 0⁺⁺ glueball mass of the strong-coupling expansion, a m = −4 ln u + Σ_k M_k u^k to u⁷, u = c₃ the fundamental
# character coefficient (Münster, Nucl. Phys. B190 (1981) 439; as quoted by Langelage, Münster, Philipsen, PoS LATTICE2007 201, arXiv:0710.0512, eq. 2.16)


def chart_cells(ns=range(11), b0=11, g=2):
    """[chart] 46:B6: the stiffness of the chart's cells. The one-loop law is a law of powers, W(w₂)/W(w₁) = (w₁/w₂)^{b₀} for
    W = e^{−8π²ϑ}: a scale lower by gⁿ has W higher by g^{b₀n}, and W = e^{−8π²} at channel unity. The stiffness is the chart's
    logarithm of 1/W in the unit 8π², ϑ_n = 1 − n b₀ ln g / 8π². Returns the cells {n: ϑ_n}, the step, the number of steps to
    W = 1, whether the logarithm of the powers gives the same ϑ_n, and the cell's size a√σ = √(−ln c₃) on the computed terms."""
    S0 = 8 * math.pi ** 2; step = b0 * math.log(g) / S0
    cells = {n: 1 - n * step for n in ns}
    law = all(abs(-(-S0 + b0 * n * math.log(g)) / S0 - cells[n]) < 1e-12 for n in cells)
    c3 = Y.c1_series(3, 8)
    size = {n: math.sqrt(-math.log(sum(float(x) * cells[n] ** k for k, x in enumerate(c3)))) for n in cells}
    return dict(cells=cells, step=step, steps_to_one=1 / step, law=law, size=size)


def plaquette_channel(ns=(9, 8, 7, 6, 4, 3, 2)):
    """[chart] T01 route (b): the 0⁺⁺ channel of the strong-coupling expansion — the closed fundamental loop, the adjoint string's
    own excitation at strong coupling — beyond the leading term −4 ln u of the paper's Section 6. m/√σ = a m / √(a²σ) with the
    imported mass series MUNSTER_0PP by order (1, 3, 5, 7) and the tension at leading order a²σ = −ln u (46:A7; the known u⁴–u⁸
    corrections move it below 0.5 % for u ≤ 0.2). The frame's u = c₃ from the ϑ⁷ list of 46:C7 at the chart's cells (46:B6) and
    at channel unity, where u is the exact sum 23/54. Returns the table by cell, with u and the order spread, and the row of
    channel unity."""
    c = Y.c1_series(3, 8); th = chart_cells()["cells"]
    def am(u, order): return -4 * math.log(u) + sum(float(MUNSTER_0PP[k]) * u ** k for k in range(1, order + 1))
    def row(u):
        sig = math.sqrt(-math.log(u))
        vals = {o: am(u, o) / sig for o in (1, 3, 5, 7)}
        hi = [vals[o] for o in (3, 5, 7)]
        return dict(u=u, leading=4 * sig, orders=vals, spread=max(hi) - min(hi))        # the spread of the orders 3, 5, 7
    u1 = sum(c)                                                                        # the exact sum at channel unity
    return dict(table={n: row(sum(float(x) * th[n] ** k for k, x in enumerate(c))) for n in ns}, unity=dict(row(float(u1)), exact=u1))


def wrap_family(spec=None):
    """[chart] The candidate operators of decision D5 for the glueball as a registration of two residue-0 constituents, each
    candidate's E₀ = Δ/√σ by the dilation symmetry of the chart operator, E₀(a|p| + ϰr) = √(aϰ) E₀(|p| + r), against the three
    lattice determinations of m(0⁺⁺)/√σ (m0pp_determinations): a ∈ {1, 2} (the one-body form of 35-hadrons C17; one |p| per
    massless constituent — both the chart's kinematics), ϰ ∈ {1, 2, 9/4} (one fundamental wrap; the adjoint wrap, two fundamental
    wraps up to the factor 9/8, with the ratio computed to order ϑ⁴ — yangmills.adjoint_over_fundamental_squared; Casimir
    scaling C_A/C_F, the chart's intermediate-distance import). Returns the table with each candidate's offset from each
    determination, the ϰ-free radial ratios E₁/E₀, E₂/E₀, the lattice radial ratio, and the effective tension each determination
    would need (none of them a frame value)."""
    spec = spec or wrap_spectrum(1, 1, 3)
    E0 = spec[0]
    det = m0pp_determinations()
    table = []
    for a in (1, 2):
        for kappa in (Q(1), Q(2), Q(9, 4)):
            e = math.sqrt(a * float(kappa)) * E0
            off = {k: e / float(v) - 1 for k, (v, dv) in det.items()}
            inside = {k: float(v - dv) <= e <= float(v + dv) for k, (v, dv) in det.items()}
            table.append(dict(a=a, kappa=kappa, E0=e, off=off, inside=inside))
    s, ds = GLUEBALL_LATTICE["m0pp_star_r0"]; g, dg = GLUEBALL_LATTICE["m0pp_r0"]
    r_lat = float(s / g); dr = r_lat * math.sqrt(float(ds / s) ** 2 + float(dg / g) ** 2)
    kappa_eff = {k: {a: (float(v) / E0) ** 2 / a for a in (1, 2)} for k, (v, dv) in det.items()}
    return dict(E=spec, table=table, determinations=det, ratios=(spec[1] / E0, spec[2] / E0), lattice_radial=(r_lat, dr),
                kappa_eff=kappa_eff)


def adjoint_ratio_table(ns=(10, 9, 8, 7, 6, 5)):
    """[chart] adjoint_ratio at the chart's cells (46:B6): {n: σ₈/σ₃}; the chart tier forms the floats."""
    th = chart_cells()["cells"]
    return {n: adjoint_ratio(th[n])[0] for n in ns}


def adjoint_ratio(theta, n=8):
    """[chart] The chart's tension ratio σ₈/σ₃ = ln c₈(ϑ) / ln c₃(ϑ) at the stiffness ϑ of a cell, from the exact series c₃, c₈
    of yangmills (the logarithm is the chart's): 1.976, 1.976, 1.982, 1.992, 2.006, 2.022 at the cells n = 10 to 5. Returns the
    ratio and the two tensions."""
    c3 = Y.c1_series(3, n); c8 = Y.c_adj_series(n)
    s3 = -math.log(sum(float(c) * theta ** k for k, c in enumerate(c3)))
    s8 = -math.log(sum(float(c) * theta ** k for k, c in enumerate(c8)))
    return s8 / s3, s3, s8
