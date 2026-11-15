"""frc.chart_hadrons — the chart theme's readings of 35-hadrons (19 October 2026): the PDG masses against the exact relations,
the anchored spectrum, the single-scale ratios, the finite confinement operator's decimals against the Airy zeros, the baryon
eigenvalue E₀ of |p| + r and the forward landing of the constituent ratios.

Standard library only. The measured masses are declared rationals (MeV/c², PDG 2024, isospin-averaged where the paper averages
them) and every confrontation is computed in Fractions; the eigenvalue readouts are floats of the grid stated in DATA — the
finite-difference H^(N) = −u'' + x u by bisection on the Sturm count, the relativistic H_G = |p| + r by a Lanczos iteration
in the sine basis, where |p| = T^{1/2} is diagonal (2 sin(kπ/2(N+1))/h) and the position operator acts through the sine
transform. The paper's package (src/35-hadrons, numpy) computed the same operators on the grids N = 2200..4000; the
readouts move with the grid (F_rel 3.47, 3.50, 3.51, 3.52 at N = 300, 600, 1000, 3000) and the rows' tolerances hold on
every grid from N = 600 (the blueprint's finding 7, decision D6). The one Ω-hard scale √(ħcσ) = 440 MeV enters once, declared
here; the electromagnetic coupling α is the imported constant.

    pdg()                                 the isospin averages and the charged states as Fractions
    confrontations()                      GMO, the decuplet spacings and spread, the third difference, the links, A_light,
                                          Coleman–Glashow and the orderings, heavy-quark symmetry, the vector nonet
    anchored_spectrum()                   m_l, m_s, v_ll from {N, Λ, Δ}; the eight masses, the residuals, the largest
    single_scale()                        λ_l, m_s/m_l, λ_hf, λ_N, the gap at √(ħcσ) = 440 MeV
    residual_orders()                     the GMO residual over Ξ − N, the third difference over the spacing
    airy_readout(N, L)                    the four lowest eigenvalues of H^(N) by bisection, against the Airy zeros; ε₁/ε₀
    nonrelativistic_contact(N, L)         ε₀ and |u'(0)|² of H^(N) by inverse iteration (→ 1, the Airy normalisation)
    relativistic_ground(N, L, m)          E₀, E₁ and |u'(0)|² of |p| + r by the Lanczos iteration in the sine basis
    forward_landing(N, L)                 F_rel, α_s at the scale, v_ll/m_l and λ_hf at α_s = 0.93 and 1.00, λ_l forward
    em_magnitude()                        α √(ħcσ) (1/3) against the lattice QED splitting

The revision of 14 November 2026 adds, with their data: the heavy-quark relation with isospin-averaged mesons and their
spin averages; the strength of the flavour breaking and the thresholds of the first-order relations, each relation written
as an equality of two averages of masses; the second order of the pairwise model against the data; Coleman–Glashow against
its measurement errors; the wrap operator's readings E₀, E₁/E₀ and the contact value C = (u₁/x₁)² on the declared grid
(600 sites of [0, 30]). The readings move with the grid (C = 3.50, 3.51, 3.52 at 600, 1200, 2400 sites); the ledger's rows
carry the numerals of the declared grid.

    heavy_averaged()                      D, D*, B averaged over the charge states, B* = B + (M_B* − M_B); the spin averages;
                                          the residual of M_Λb − M_Λc; m_c, m_b; the size (ħσ/c³)(1/m_c − 1/m_b) of the omitted terms
    thresholds()                          ε_s = (M_Λ − M_N)/M_N, ε_s² × the span of each multiplet, the two-average residuals
    second_order_reading()                the pairwise model's second order at the anchored constituents; the measured values
    cg_within_error()                     the difference of the two sides of Coleman–Glashow against their errors
    np_lattice()                          the lattice separation of M_n − M_p against the measured splitting
    wrap_readings(N, L)                   E₀, E₁/E₀ and C of |p| + r on the grid, computed once per grid

The revision of 15 November 2026. Units: the scale is the energy √(ħcσ), named sqrt_sigma in the data, with its numeral in
MeV; a mass is held by its numeral in MeV/c²; a pure number λ is a rest energy over the scale, M c²/√(ħcσ), the quotient of
the two numerals. No constant is set to 1. The mass of the nucleon is read by the winding law, λ_k² = (3/2)π + 2πk, and
the operator |p| + r is the body's Hamiltonian in the length unit √(ħc/σ): the paper takes its contact value alone.

    winding_law(k), winding_readings()    λ_k = √((3/2)π + 2πk); λ_N, the scale at which the law reads the nucleon mass, the
                                          nucleon at the imported scale
    hamiltonian_readings(N, L)            E₀, E₁ and C of the body's Hamiltonian on the grid; the squares of the two levels
                                          over π/2, where the law has 3 and 7
    joint_solution_law(N, L)              λ_hf, λ_l and (M_Δ − M_N)/M_N from 3λ_l − ¾λ_hf = λ_N and λ_hf λ_l = (2ρ/9) C α_s
    radial_ratio_law()                    √(7/3) against the Breit–Wigner and the pole ratios of N(1440)
    register_levels(p)                    the two lowest levels of the register's Hamiltonian |X| + F⁻¹|X|F on the odd
                                          functions of C_p, in the unit √(2π/p)
"""
import math
from fractions import Fraction as Q

# ---- declared data ------------------------------------------------------------------------------------------------------
DATA = {
    "octet": dict(p=Q("938.272"), n=Q("939.565"), Lam=Q("1115.683"), Sp=Q("1189.37"), S0=Q("1192.642"), Sm=Q("1197.449"),
                  X0=Q("1314.86"), Xm=Q("1321.71")),                                                   # MeV/c², PDG 2024
    "decuplet": dict(Del=Q("1232.0"), Ssp=Q("1382.8"), Ss0=Q("1383.7"), Ssm=Q("1387.2"), Xs0=Q("1531.80"), Xsm=Q("1535.0"),
                     Om=Q("1672.45")),
    "heavy": dict(Lc=Q("2286.46"), Lb=Q("5619.60"), D0=Q("1864.84"), B0=Q("5279.66"), Sc=Q("2453.5"), Scs=Q("2518.4")),
    "vector": dict(rho=Q("775.26"), ome=Q("782.66"), Ks0=Q("891.67"), Ksp=Q("895.55"), phi=Q("1019.46")),
    "scales": dict(sqrt_sigma=Q("440"), alpha_inv=Q("137.036"), qed_np=Q("1.00"), b0=9, lam_ratio=2, rho_cc=Q(1, 2)),   # the scale √(ħcσ) in MeV (Ω-hard, 35:Z1); 1/α; the lattice QED part of M_n − M_p in MeV/c² (Borsányi 2015); b₀ and √(ħcσ)/Λ; the qq colour weight
    "airy": ("2.33811", "4.08795", "5.52056", "6.78671"),                                              # the Airy zeros −a_k
    "grid": dict(airy=(4000, 30), rel=(600, 30), lanczos=40, register=64),                             # the finite grids, the Lanczos depth, the depth on the register
    "targets": dict(lam_l=Q("0.822"), lam_hf=Q("0.444"), vm=Q("0.540"), E0=Q("2.232"), alpha_s_hf=Q("0.93")),   # the paper's constituent readouts
    "heavy_mesons": dict(D0=Q("1864.84"), Dp=Q("1869.66"), Ds0=Q("2006.85"), Dsp=Q("2010.26"), Bp=Q("5279.41"), B0=Q("5279.72"),
                         dB=Q("45.21")),                                                              # MeV/c², PDG 2024; dB = M_B* − M_B
    "errors": dict(cg_lhs=Q("0.21"), cg_rhs=Q("0.08")),                                                # MeV/c²: (n − p) + (Ξ⁻ − Ξ⁰) = 8.14(21), Σ⁻ − Σ⁺ = 8.08(8)
    "n1440": dict(bw_lo=Q("1410"), bw=Q("1440"), bw_hi=Q("1470"), pole=Q("1370")),                     # MeV/c²: the Breit–Wigner mass and range, the pole's real part
    "delta_pole": Q("1210"),                                                                           # MeV/c²: the real part of the Δ(1232) pole
    "lattice_np": dict(qcd=Q("2.52"), qcd_err=Q("0.30"), qed=Q("-1.00"), qed_err=Q("0.16")),           # MeV/c²: M_n − M_p from the quark masses and from electromagnetism (Borsányi 2015)
}


def pdg():
    """The isospin averages the paper uses and the charged states."""
    o, d, h, v = DATA["octet"], DATA["decuplet"], DATA["heavy"], DATA["vector"]
    avg = lambda *xs: sum(xs, Q(0)) / len(xs)
    out = dict(o); out.update(h); out.update(rho=v["rho"], ome=v["ome"], phi=v["phi"])
    out.update(N=avg(o["p"], o["n"]), Sig=avg(o["Sp"], o["S0"], o["Sm"]), Xi=avg(o["X0"], o["Xm"]), Del=d["Del"],
               Sgs=avg(d["Ssp"], d["Ss0"], d["Ssm"]), Xis=avg(d["Xs0"], d["Xsm"]), Om=d["Om"], Ks=avg(v["Ks0"], v["Ksp"]))
    return out


def fmt(x, nd=3, sign=False):
    """A rational or float as a decimal string with nd places (the ledger tier formats its details through this)."""
    return f"{float(x):{'+' if sign else ''}.{nd}f}"


# ---- the confrontations ---------------------------------------------------------------------------------------------------
def confrontations():
    """Every PDG confrontation of the paper, exact in Fractions (floats only in the caller's display)."""
    m = pdg()
    gmo_l, gmo_r = (m["N"] + m["Xi"]) / 2, (3 * m["Lam"] + m["Sig"]) / 4
    sp = [m["Sgs"] - m["Del"], m["Xis"] - m["Sgs"], m["Om"] - m["Xis"]]
    beta = (m["Om"] - m["Del"]) / 3
    third = m["Del"] - 3 * m["Sgs"] + 3 * m["Xis"] - m["Om"]
    l1, r1 = m["Sig"] - m["Lam"], Q(2, 3) * ((m["Del"] - m["N"]) - (m["Sgs"] - m["Sig"]))
    l2, r2 = m["Sgs"] - m["Sig"], m["Xis"] - m["Xi"]
    cg_l, cg_r = (m["n"] - m["p"]) + (m["Xm"] - m["X0"]), m["Sm"] - m["Sp"]
    hqs_b, hqs_m = m["Lb"] - m["Lc"], m["B0"] - m["D0"]
    return dict(
        gmo=dict(lhs=gmo_l, rhs=gmo_r, residual=(gmo_r - gmo_l) / gmo_r),
        spacing=dict(spacings=sp, beta=beta, spread=(max(sp) - min(sp)) / beta, strange_step=(m["Xi"] - m["N"]) / 2),
        third=dict(value=third, relative=third / m["Om"]),
        links=dict(l1=l1, r1=r1, rel1=(l1 - r1) / l1, l2=l2, r2=r2, rel2=(l2 - r2) / l2),
        hyperfine=dict(A_light=Q(2, 3) * (m["Del"] - m["N"]), ll_pair=m["Sgs"] - m["Sig"]),
        cg=dict(lhs=cg_l, rhs=cg_r, residual=(cg_l - cg_r) / cg_r, n_minus_p=m["n"] - m["p"], sigma0_minus_lambda=m["S0"] - m["Lam"]),
        heavy=dict(baryon=hqs_b, meson=hqs_m, residual=(hqs_b - hqs_m) / hqs_m, ratio=(m["Scs"] - m["Sc"]) / (m["Sgs"] - m["Sig"])),
        vector=dict(residual=(2 * m["Ks"] - m["rho"] - m["phi"]) / (m["rho"] + m["phi"]), Ks_pred=(m["rho"] + m["phi"]) / 2,
                    Ks_rel=((m["rho"] + m["phi"]) / 2 - m["Ks"]) / m["Ks"], ome_rel=(m["rho"] - m["ome"]) / m["ome"], b=(m["phi"] - m["rho"]) / 2),
    )


def anchored_spectrum():
    """The octet and decuplet from the anchors N, Λ, Δ: (m_l, m_s, v_ll, v_ls, v_ss), the masses and residuals per baryon,
    and the largest residual over the five predictions."""
    from frc import hadrons as H
    m = pdg()
    ml, ms, v, vls, vss = H.anchor_constituents(m["N"], m["Lam"], m["Del"])
    table = {t: (H.baryon_mass(t, ml, ms, v, vls, vss), m[t]) for t in H.BARYONS}
    res = {t: (frc - pdgv) / pdgv for t, (frc, pdgv) in table.items()}
    worst = max(abs(res[t]) for t in H.BARYONS if t not in ("N", "Lam", "Del"))
    return (ml, ms, v, vls, vss), table, res, worst


def single_scale():
    """At √(ħcσ) = 440 MeV: λ_l = m_l c²/√(ħcσ), m_s/m_l, λ_hf = v_ll c²/√(ħcσ), λ_N = M_N c²/√(ħcσ), the gap's ratio and M_Λ − M_N."""
    (ml, ms, v, _, _), _, _, _ = anchored_spectrum()
    s = DATA["scales"]["sqrt_sigma"]; m = pdg()
    return dict(lam_l=ml / s, ms_over_ml=ms / ml, lam_hf=v / s, mN_over_s=m["N"] / s, gap_over_s=(ms - ml) / s, gap=m["Lam"] - m["N"],
                vm=v / ml, m_l=ml, m_s=ms, v_ll=v)


def residual_orders():
    """The second-order residuals as fractions of the leading splittings: GMO over Ξ − N, the third difference over the spacing."""
    m = pdg(); c = confrontations()
    return dict(gmo=abs(c["gmo"]["rhs"] - c["gmo"]["lhs"]) / (m["Xi"] - m["N"]), third=abs(c["third"]["value"]) / c["spacing"]["beta"])


def em_magnitude():
    """α √(ħcσ) × (1/3), the one-body charge difference p − n, against the rest energy of the lattice QED splitting, 1.00 MeV."""
    s = DATA["scales"]
    v = s["sqrt_sigma"] / s["alpha_inv"] * Q(1, 3)
    return dict(value=v, qed=s["qed_np"], relative=(v - s["qed_np"]) / s["qed_np"])


# ---- the finite confinement operator: the decimals --------------------------------------------------------------------------
def _sturm_float(diag, off2, lam):
    cnt, q = 0, 1.0
    for k, d in enumerate(diag):
        q = d - lam - (off2 / q if k else 0.0)
        if q == 0.0: q = -1e-300
        if q < 0: cnt += 1
    return cnt


def _kth_eigen(diag, off2, k, lo, hi, iters=60):
    for _ in range(iters):
        mid = (lo + hi) / 2
        if _sturm_float(diag, off2, mid) > k: hi = mid
        else: lo = mid
    return (lo + hi) / 2


def airy_readout(N=None, L=None):
    """The four lowest eigenvalues of H^(N) = −u'' + x u (N sites of [0, L]) by bisection on the float Sturm count, the Airy
    zeros they approach, the differences, and ε₁/ε₀."""
    N, L = (N, L) if N else DATA["grid"]["airy"]
    h = L / (N + 1); diag = [2 / h ** 2 + k * h for k in range(1, N + 1)]; off2 = 1 / h ** 4
    eps = [_kth_eigen(diag, off2, k, 0.0, 12.0) for k in range(4)]
    zeros = [float(Q(z)) for z in DATA["airy"]]
    return eps, zeros, [e - z for e, z in zip(eps, zeros)], eps[1] / eps[0]


def _thomas(a, b, c, d):
    """Solve the tridiagonal system with sub-diagonal a, diagonal b, super-diagonal c (lists), right side d."""
    n = len(b); cp = [0.0] * n; dp = [0.0] * n
    cp[0] = c[0] / b[0] if n > 1 else 0.0; dp[0] = d[0] / b[0]
    for i in range(1, n):
        den = b[i] - a[i - 1] * cp[i - 1]
        cp[i] = c[i] / den if i < n - 1 else 0.0
        dp[i] = (d[i] - a[i - 1] * dp[i - 1]) / den
    x = [0.0] * n; x[-1] = dp[-1]
    for i in range(n - 2, -1, -1): x[i] = dp[i] - cp[i] * x[i + 1]
    return x


def nonrelativistic_contact(N=None, L=None, iters=40):
    """ε₀ and |u'(0)|² of the normalised ground state of H^(N) (∫u² = h Σ u² = 1) by inverse iteration at the shift 2.3:
    the contact overlap tends to 1, the Airy normalisation identity ∫_{a₁}^∞ Ai² = Ai'(a₁)²."""
    N, L = (N, L) if N else DATA["grid"]["rel"]
    h = L / (N + 1); x = [k * h for k in range(1, N + 1)]
    shift = 2.3
    b = [2 / h ** 2 + xi - shift for xi in x]; a = [-1 / h ** 2] * (N - 1); c = [-1 / h ** 2] * (N - 1)
    u = [math.exp(-xi) for xi in x]
    for _ in range(iters):
        u = _thomas(a, b, c, u); nrm = math.sqrt(sum(t * t for t in u) * h); u = [t / nrm for t in u]
    Hu = [(2 * u[i] - (u[i - 1] if i else 0.0) - (u[i + 1] if i < N - 1 else 0.0)) / h ** 2 + x[i] * u[i] for i in range(N)]
    eps0 = sum(p * q for p, q in zip(Hu, u)) * h
    if u[0] < 0: u = [-t for t in u]
    return eps0, (u[0] / h) ** 2


def relativistic_ground(N=None, L=None, m=None):
    """E₀, E₁ and |u'(0)|² of H_G = |p| + r on N sites of [0, L]: |p| = T^{1/2} is diagonal in the sine basis of the
    finite-difference Laplacian T, with entries 2 sin(kπ/2(N+1))/h; the position operator acts through the sine transform;
    the lowest eigenpairs by a Lanczos iteration of depth m with full reorthogonalisation, the small tridiagonal solved by
    bisection and inverse iteration; the ground vector transformed back to the grid for the contact value."""
    N, L = (N, L) if N else DATA["grid"]["rel"]; m = m or DATA["grid"]["lanczos"]
    h = L / (N + 1)
    pk = [2 * math.sin(math.pi * k / (2 * (N + 1))) / h for k in range(1, N + 1)]
    c0 = math.sqrt(2 / (N + 1))
    S = [[c0 * math.sin(k * j * math.pi / (N + 1)) for j in range(1, N + 1)] for k in range(1, N + 1)]   # symmetric, orthogonal
    xs = [j * h for j in range(1, N + 1)]
    def matvec(c):
        v = [sum(map(float.__mul__, row, c)) for row in S]
        v = [x * y for x, y in zip(xs, v)]
        w = [sum(map(float.__mul__, row, v)) for row in S]
        return [p * q + r for p, q, r in zip(pk, c, w)]
    q = [1.0 / math.sqrt(N)] * N; Qs = [q]; alpha = []; beta = []
    for _ in range(m):
        w = matvec(Qs[-1]); a = sum(x * y for x, y in zip(w, Qs[-1])); alpha.append(a)
        for qq in Qs:
            d_ = sum(x * y for x, y in zip(w, qq)); w = [x - d_ * y for x, y in zip(w, qq)]
        bn = math.sqrt(sum(x * x for x in w))
        if bn < 1e-12: break
        beta.append(bn); Qs.append([x / bn for x in w])
    k = len(alpha); off2 = [b * b for b in beta]
    def cnt(lam):
        c_, qv = 0, 1.0
        for i in range(k):
            qv = alpha[i] - lam - (off2[i - 1] / qv if i else 0.0)
            if qv == 0.0: qv = -1e-300
            if qv < 0: c_ += 1
        return c_
    def kth(j):
        lo, hi = 0.0, 50.0
        for _ in range(60):
            mid = (lo + hi) / 2
            if cnt(mid) > j: hi = mid
            else: lo = mid
        return (lo + hi) / 2
    E0, E1 = kth(0), kth(1)
    # the ground vector of the small tridiagonal by inverse iteration, then on the grid
    y = [1.0] * k
    for _ in range(3):
        y = _thomas(beta[:k - 1], [a - (E0 - 1e-7) for a in alpha], beta[:k - 1], y)
        nrm = math.sqrt(sum(t * t for t in y)); y = [t / nrm for t in y]
    c = [sum(y[i] * Qs[i][j] for i in range(k)) for j in range(N)]                   # the sine-basis coefficients
    u = [sum(map(float.__mul__, row, c)) for row in S]                                  # on the grid
    nrm = math.sqrt(sum(t * t for t in u) * h); u = [t / nrm for t in u]
    if u[0] < 0: u = [-t for t in u]
    return E0, E1, (u[0] / h) ** 2


def forward_landing(N=None, L=None):
    """The forward evaluation on the grid: F_rel = |u'(0)|²_rel/|u'(0)|²_n.r., α_s = 2π/(b₀ ln(√(ħcσ)/Λ)), the contact term
    v_ll/m_l = (2ρ/9) F_rel α_s/λ_l² at the hyperfine-required α_s and at the transmutation value, λ_hf = (v_ll/m_l) λ_l,
    and λ_l = (E₀ + (3/4)λ_hf)/3 from the exact spin split."""
    N, L = (N, L) if N else DATA["grid"]["rel"]
    e0n, cn = nonrelativistic_contact(N, L)
    E0, E1, cr = relativistic_ground(N, L)
    F = cr / cn
    s = DATA["scales"]; t = DATA["targets"]
    alpha_s = 2 * math.pi / (s["b0"] * math.log(s["lam_ratio"]))
    K = (2 * float(s["rho_cc"]) / 9) * F
    ll = float(t["lam_l"]); hf = float(t["lam_hf"])
    out = {}
    for a_s, tag in ((float(t["alpha_s_hf"]), "hf"), (1.0, "transmutation")):
        vm = K * a_s / ll ** 2; out[tag] = dict(alpha_s=a_s, vm=vm, lam_hf=vm * ll)
    return dict(eps0=e0n, contact_nr=cn, E0=E0, E1=E1, contact_rel=cr, F_rel=F, alpha_s=alpha_s, lam_l_fwd=(E0 + 0.75 * hf) / 3, **out)


# ---- the revision of 14 November 2026: the readings of the revised rows ---------------------------------------------------
def heavy_averaged():
    """The heavy-quark relation with isospin-averaged mesons (35:P7): D, D* and B averaged over their two charge states,
    B* the averaged B plus the measured splitting, the spin averages M̄ = ¼(M_P + 3M_V); the residual of M_Λb − M_Λc
    against M̄_B − M̄_D; the pseudoscalars alone; the hyperfine shifts −¾(M_V − M_P); Λ_b from Λ_c; the constituent
    masses m_c, m_b from Λ_c, Λ_b and the size (ħσ/c³)(1/m_c − 1/m_b) of the terms of order 1/m_Q; the hyperfine ratio."""
    h, hm, m = DATA["heavy"], DATA["heavy_mesons"], pdg()
    D, Ds, B = (hm["D0"] + hm["Dp"]) / 2, (hm["Ds0"] + hm["Dsp"]) / 2, (hm["Bp"] + hm["B0"]) / 2
    Bs = B + hm["dB"]
    Dbar, Bbar = (D + 3 * Ds) / 4, (B + 3 * Bs) / 4
    baryon, meson = h["Lb"] - h["Lc"], Bbar - Dbar
    (ml, ms, v, _, _), _, _, _ = anchored_spectrum()
    mc, mb = h["Lc"] - 2 * ml + Q(3, 4) * v, h["Lb"] - 2 * ml + Q(3, 4) * v
    s_ = DATA["scales"]["sqrt_sigma"]
    return dict(D=D, Ds=Ds, B=B, Bs=Bs, Dbar=Dbar, Bbar=Bbar, baryon=baryon, meson=meson, residual=baryon - meson,
                relative=(baryon - meson) / meson, pseudoscalar=B - D, pseudoscalar_rel=(baryon - (B - D)) / (B - D),
                shift_D=-Q(3, 4) * (Ds - D), shift_B=-Q(3, 4) * hm["dB"], Lb_pred=h["Lc"] + meson,
                Lb_rel=(h["Lc"] + meson - h["Lb"]) / h["Lb"], m_c=mc, m_b=mb, omitted=s_ * s_ * (1 / mc - 1 / mb),
                ratio=(h["Scs"] - h["Sc"]) / (m["Sgs"] - m["Sig"]), ms_over_mc=ms / mc)


def thresholds():
    """The strength of the flavour breaking ε_s = (M_Λ − M_N)/M_N and the thresholds ε_s² × the span of the multiplet
    (35:P1, P2, P9, P10). A first-order relation is written as an equality of two averages of masses and its residual
    is the difference of the two sides: the octet ½(N + Ξ) − ¼(3Λ + Σ); the decuplet Σ* − ½(Δ + Ξ*) and Ξ* − ½(Σ* + Ω);
    the vector nonet K* − ½(ρ + φ), with ω − ρ beside it."""
    m = pdg(); eps = (m["Lam"] - m["N"]) / m["N"]; e2 = eps * eps
    return dict(eps=eps, eps2=e2,
                octet=dict(residual=(m["N"] + m["Xi"]) / 2 - (3 * m["Lam"] + m["Sig"]) / 4, threshold=e2 * (m["Xi"] - m["N"])),
                decuplet=dict(residuals=(m["Sgs"] - (m["Del"] + m["Xis"]) / 2, m["Xis"] - (m["Sgs"] + m["Om"]) / 2),
                              threshold=e2 * (m["Om"] - m["Del"])),
                vector=dict(residual=m["Ks"] - (m["rho"] + m["phi"]) / 2, omega=m["ome"] - m["rho"], threshold=e2 * (m["phi"] - m["rho"])),
                anchors=dict(threshold=e2 * (m["Om"] - m["N"])))


def second_order_reading():
    """The second order of the pairwise model against the data (35:C20). At the anchored constituents the model gives the
    octet residual ⅛ v_ll (1 − z)² and both decuplet second differences ¼ v_ll (1 − z)², z = m_l/m_s, all positive. The
    measured octet residual ½(N + Ξ) − ¼(3Λ + Σ), the measured second differences Δ − 2Σ* + Ξ* and Σ* − 2Ξ* + Ω, and the
    measured third difference."""
    (ml, ms, v, _, _), _, _, _ = anchored_spectrum(); m = pdg()
    sq = v * (1 - ml / ms) ** 2
    return dict(model_octet=sq / 8, model_decuplet=sq / 4,
                octet=(m["N"] + m["Xi"]) / 2 - (3 * m["Lam"] + m["Sig"]) / 4,
                second=(m["Del"] - 2 * m["Sgs"] + m["Xis"], m["Sgs"] - 2 * m["Xis"] + m["Om"]),
                third=m["Del"] - 3 * m["Sgs"] + 3 * m["Xis"] - m["Om"])


def cg_within_error():
    """Coleman–Glashow against its measurement errors (35:P6): the difference of (n − p) + (Ξ⁻ − Ξ⁰) and Σ⁻ − Σ⁺, and
    whether its square is below the sum of the squares of the two errors."""
    c = confrontations()["cg"]; e = DATA["errors"]; d = c["lhs"] - c["rhs"]
    return dict(lhs=c["lhs"], rhs=c["rhs"], difference=d, err_lhs=e["cg_lhs"], err_rhs=e["cg_rhs"],
                within=d * d < e["cg_lhs"] ** 2 + e["cg_rhs"] ** 2)


def np_lattice():
    """The lattice separation of M_n − M_p (35:A10) against the measured splitting: the sum of its two parts, and whether
    the measured value lies within the combined error."""
    l = DATA["lattice_np"]; o = DATA["octet"]; tot = l["qcd"] + l["qed"]; meas = o["n"] - o["p"]
    return dict(total=tot, measured=meas, within=(tot - meas) ** 2 < l["qcd_err"] ** 2 + l["qed_err"] ** 2,
                qcd_above_qed=l["qcd"] > -l["qed"])


_WRAP = {}


def wrap_readings(N=None, L=None):
    """E₀, E₁/E₀ and the contact value C = (u₁/x₁)² of the wrap operator H_G = |p| + r (35:B7) on N sites of [0, L], the
    lowest eigenvector normalised by x₁ Σ u_j² = 1; computed once per grid (relativistic_ground)."""
    N, L = (N, L) if N else DATA["grid"]["rel"]
    if (N, L) not in _WRAP:
        E0, E1, C = relativistic_ground(N, L)
        _WRAP[(N, L)] = dict(E0=E0, E1=E1, ratio=E1 / E0, C=C)
    return _WRAP[(N, L)]


# ---- the revision of 15 November 2026: the winding law, the body's Hamiltonian, the register ---------------------------------
def winding_law(k=0):
    """The chart's reading of the winding law (35:C24): λ_k² = (3/2)π + 2πk; its positive root."""
    return math.sqrt(1.5 * math.pi + 2 * math.pi * k)


def winding_readings():
    """35:C24 [chart] — λ_N = √(3π/2); the scale √(ħcσ) = M_N c²/λ_N at which the law reads the nucleon mass (MeV); the
    nucleon at the imported scale (MeV/c²) and its excess over the measured mass; the measured ratio at the imported scale."""
    m = pdg(); s_ = float(DATA["scales"]["sqrt_sigma"]); mN = float(m["N"]); lam = winding_law(0)
    return dict(lam_N=lam, lam_1=winding_law(1), scale=mN / lam, MN_at_scale=lam * s_, excess=(lam * s_ - mN) / mN,
                measured=m["N"] / DATA["scales"]["sqrt_sigma"])


def hamiltonian_readings(N=None, L=None):
    """35:C17 [chart] — the two lowest levels E₀, E₁ and the contact value C of the body's Hamiltonian on the grid
    (wrap_readings), and the squares of the two levels over π/2, where the winding law has 3 and 7."""
    w = wrap_readings(N, L)
    return dict(E0=w["E0"], E1=w["E1"], C=w["C"], ratio=w["ratio"], sq0=w["E0"] ** 2 / (math.pi / 2), sq1=w["E1"] ** 2 / (math.pi / 2))


def joint_solution_law(N=None, L=None):
    """35:C19 [chart] — the joint solution on the winding law. With λ_N = √(3π/2), the contact value C of the body's
    Hamiltonian on the grid, K = (2ρ/9) C and α_s = 2π/(b₀ ln 2): the pair 3λ_l − ¾λ_hf = λ_N, λ_hf λ_l = K α_s has the
    positive root λ_hf = (−λ_N + √(λ_N² + 9Kα_s))/(3/2) with λ_l = (λ_N + ¾λ_hf)/3, and (M_Δ − M_N)/M_N = (3/2)λ_hf/λ_N.
    Beside it: the measured ratio, the ratio at the Δ pole, and the coupling that the measured ratio would need."""
    w = wrap_readings(N, L); C = w["C"]; lam = winding_law(0); sc = DATA["scales"]; m = pdg()
    alpha_s = 2 * math.pi / (sc["b0"] * math.log(sc["lam_ratio"]))
    K = (2 * float(sc["rho_cc"]) / 9) * C
    lam_hf = (-lam + math.sqrt(lam * lam + 9 * K * alpha_s)) / 1.5; lam_l = (lam + 0.75 * lam_hf) / 3
    measured = (m["Del"] - m["N"]) / m["N"]
    lh_m = float(measured) * lam / 1.5; ll_m = (lam + 0.75 * lh_m) / 3
    return dict(lam_N=lam, C=C, alpha_s=alpha_s, lam_hf=lam_hf, lam_l=lam_l, ratio=1.5 * lam_hf / lam, measured=measured,
                pole=(DATA["delta_pole"] - m["N"]) / m["N"], alpha_needed=lh_m * ll_m / K,
                residual_nucleon=3 * lam_l - 0.75 * lam_hf - lam, residual_rule=lam_hf * lam_l - K * alpha_s)


def radial_ratio_law():
    """35:P12 [chart] — the radial ratio λ₁/λ₀ = √(7/3) of the winding law against N(1440): the Breit–Wigner ratios at the
    ends of the measured range and at its centre, and the pole ratio, each over the nucleon mass."""
    m = pdg(); r = DATA["n1440"]
    return dict(ratio=math.sqrt(7 / 3), law=winding_law(1) / winding_law(0), bw_lo=r["bw_lo"] / m["N"], bw=r["bw"] / m["N"],
                bw_hi=r["bw_hi"] / m["N"], pole=r["pole"] / m["N"])


def _lowest_level(matvec, start, depth, against=()):
    """The lowest Ritz value and vector of a symmetric matvec by a Lanczos iteration with full reorthogonalisation in two
    passes, on the complement of the unit vectors `against`; the small tridiagonal by bisection and inverse iteration."""
    dot = lambda a, b: sum(map(float.__mul__, a, b))
    def clean(w):
        for u in against:
            d_ = dot(w, u); w = [x - d_ * y for x, y in zip(w, u)]
        return w
    q = clean(list(start)); nrm = math.sqrt(dot(q, q)); Qs = [[x / nrm for x in q]]; alpha = []; beta = []
    for _ in range(depth):
        w = clean(matvec(Qs[-1])); alpha.append(dot(w, Qs[-1])); size = math.sqrt(dot(w, w))
        for _pass in (0, 1):                                                           # twice: orthogonality holds when w is small
            for qq in Qs:
                d_ = dot(w, qq); w = [x - d_ * y for x, y in zip(w, qq)]
            w = clean(w)
        bn = math.sqrt(dot(w, w))
        if bn < 1e-10 * size: break                                                    # the Krylov space is exhausted
        beta.append(bn); Qs.append([x / bn for x in w])
    k = len(alpha); off2 = [b * b for b in beta]
    def cnt(lam):
        c_, qv = 0, 1.0
        for i in range(k):
            qv = alpha[i] - lam - (off2[i - 1] / qv if i else 0.0)
            if qv == 0.0: qv = -1e-300
            if qv < 0: c_ += 1
        return c_
    lo, hi = min(alpha) - sum(beta) - 1.0, max(alpha) + sum(beta) + 1.0
    for _ in range(80):
        mid = (lo + hi) / 2
        if cnt(mid) > 0: hi = mid
        else: lo = mid
    E = (lo + hi) / 2
    if k == 1: return E, Qs[0]
    y = [1.0] * k
    for _ in range(3):
        y = _thomas(beta[:k - 1], [a - (E - 1e-7 * (1 + abs(E))) for a in alpha], beta[:k - 1], y)
        n_ = math.sqrt(dot(y, y)); y = [t / n_ for t in y]
    u = [sum(y[i] * Qs[i][j] for i in range(k)) for j in range(len(start))]
    n_ = math.sqrt(dot(u, u))
    return E, [t / n_ for t in u]


_REGISTER = {}


def register_levels(p, depth=None):
    """35:C25 (iv) [chart] — the two lowest levels of the register's Hamiltonian H_p = |X| + F⁻¹|X|F on the odd functions
    of C_p, in the unit √(2π/p) with the chart's π. On the odd functions F⁻¹|X|F is S D S, with D the step counts
    1, …, (p − 1)/2 and S the sine matrix (2/√p) sin(2πxy/p), symmetric and orthogonal. The lowest level by a Lanczos
    iteration; the second by the same iteration on the complement of the lowest state. A second level above the first
    is the simplicity of the lowest. Computed once per Subject."""
    depth = depth or DATA["grid"]["register"]
    if (p, depth) not in _REGISTER:
        m = (p - 1) // 2; c0 = 2 / math.sqrt(p)
        S = [[c0 * math.sin(2 * math.pi * x * y / p) for y in range(1, m + 1)] for x in range(1, m + 1)]
        D = [float(x) for x in range(1, m + 1)]
        def matvec(v):
            a = [sum(map(float.__mul__, row, v)) for row in S]
            a = [x * y for x, y in zip(D, a)]
            b = [sum(map(float.__mul__, row, a)) for row in S]
            return [d * x + y for d, x, y in zip(D, v, b)]
        unit = math.sqrt(2 * math.pi / p)
        rho = [x * unit for x in D]
        E0, u0 = _lowest_level(matvec, [r * math.exp(-r) for r in rho], min(depth, m))
        E1, _ = _lowest_level(matvec, [r * (r - 2.0) * math.exp(-r) for r in rho], min(depth, m - 1), against=(u0,))
        _REGISTER[(p, depth)] = dict(E0=E0 * unit, E1=E1 * unit, dim=m)
    return _REGISTER[(p, depth)]
