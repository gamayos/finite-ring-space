"""frc.chart_hadrons — the chart theme's readings of 35-hadrons (19 October 2026): the PDG masses against the exact relations,
the anchored spectrum, the single-scale ratios, the finite confinement operator's decimals against the Airy zeros, the baryon
eigenvalue E₀ of |p| + r and the forward landing of the constituent ratios.

Standard library only. The measured masses are declared rationals (MeV, PDG 2024, isospin-averaged where the paper averages
them) and every confrontation is computed in Fractions; the eigenvalue readouts are floats of the grid stated in DATA — the
finite-difference H^(N) = −u'' + x u by bisection on the Sturm count, the relativistic H_G = |p| + r by a Lanczos iteration
in the sine basis, where |p| = T^{1/2} is diagonal (2 sin(kπ/2(N+1))/h) and the position operator acts through the sine
transform. The paper's package (src/35-hadrons, numpy) computed the same operators on the grids N = 2200..4000; the
readouts move with the grid (F_rel 3.47, 3.50, 3.51, 3.52 at N = 300, 600, 1000, 3000) and the rows' tolerances hold on
every grid from N = 600 (the blueprint's finding 7, decision D6). The one Ω-hard scale √σ = 440 MeV enters once, declared
here; the electromagnetic coupling α is the imported constant.

    pdg()                                 the isospin averages and the charged states as Fractions
    confrontations()                      GMO, the decuplet spacings and spread, the third difference, the links, A_light,
                                          Coleman–Glashow and the orderings, heavy-quark symmetry, the vector nonet
    anchored_spectrum()                   m_l, m_s, v_ll from {N, Λ, Δ}; the eight masses, the residuals, the largest
    single_scale()                        λ_l, m_s/m_l, λ_hf, M_N/√σ, the gap at √σ = 440
    residual_orders()                     the GMO residual over Ξ − N, the third difference over the spacing
    airy_readout(N, L)                    the four lowest eigenvalues of H^(N) by bisection, against the Airy zeros; ε₁/ε₀
    nonrelativistic_contact(N, L)         ε₀ and |u'(0)|² of H^(N) by inverse iteration (→ 1, the Airy normalisation)
    relativistic_ground(N, L, m)          E₀, E₁ and |u'(0)|² of |p| + r by the Lanczos iteration in the sine basis
    forward_landing(N, L)                 F_rel, α_s(√σ), v_ll/m_l and λ_hf at α_s = 0.93 and 1.00, λ_l forward
    em_magnitude()                        α √σ (1/3) against the lattice QED splitting
"""
import math
from fractions import Fraction as Q

# ---- declared data ------------------------------------------------------------------------------------------------------
DATA = {
    "octet": dict(p=Q("938.272"), n=Q("939.565"), Lam=Q("1115.683"), Sp=Q("1189.37"), S0=Q("1192.642"), Sm=Q("1197.449"),
                  X0=Q("1314.86"), Xm=Q("1321.71")),                                                   # MeV, PDG 2024
    "decuplet": dict(Del=Q("1232.0"), Ssp=Q("1382.8"), Ss0=Q("1383.7"), Ssm=Q("1387.2"), Xs0=Q("1531.80"), Xsm=Q("1535.0"),
                     Om=Q("1672.45")),
    "heavy": dict(Lc=Q("2286.46"), Lb=Q("5619.60"), D0=Q("1864.84"), B0=Q("5279.66"), Sc=Q("2453.5"), Scs=Q("2518.4")),
    "vector": dict(rho=Q("775.26"), ome=Q("782.66"), Ks0=Q("891.67"), Ksp=Q("895.55"), phi=Q("1019.46")),
    "scales": dict(sqrt_sigma=Q("440"), alpha_inv=Q("137.036"), qed_np=Q("1.00"), b0=9, lam_ratio=2, rho_cc=Q(1, 2)),   # √σ MeV (Ω-hard, 35:Z1); 1/α; the lattice QED part of M_n − M_p (Borsányi 2015); b₀ and √σ/Λ; the qq colour weight
    "airy": ("2.33811", "4.08795", "5.52056", "6.78671"),                                              # the Airy zeros −a_k
    "grid": dict(airy=(4000, 30), rel=(600, 30), lanczos=40),                                          # the finite grids and the Lanczos depth
    "targets": dict(lam_l=Q("0.822"), lam_hf=Q("0.444"), vm=Q("0.540"), E0=Q("2.232"), alpha_s_hf=Q("0.93")),   # the paper's constituent readouts
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
    """At √σ = 440 MeV: λ_l = m_l/√σ, m_s/m_l, λ_hf = v_ll/√σ, M_N/√σ, (m_s − m_l)/√σ and M_Λ − M_N."""
    (ml, ms, v, _, _), _, _, _ = anchored_spectrum()
    s = DATA["scales"]["sqrt_sigma"]; m = pdg()
    return dict(lam_l=ml / s, ms_over_ml=ms / ml, lam_hf=v / s, mN_over_s=m["N"] / s, gap_over_s=(ms - ml) / s, gap=m["Lam"] - m["N"],
                vm=v / ml, m_l=ml, m_s=ms, v_ll=v)


def residual_orders():
    """The second-order residuals as fractions of the leading splittings: GMO over Ξ − N, the third difference over the spacing."""
    m = pdg(); c = confrontations()
    return dict(gmo=abs(c["gmo"]["rhs"] - c["gmo"]["lhs"]) / (m["Xi"] - m["N"]), third=abs(c["third"]["value"]) / c["spacing"]["beta"])


def em_magnitude():
    """α √σ × (1/3), the one-body charge difference p − n, against the lattice QED splitting 1.00 MeV."""
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
    """The forward evaluation on the grid: F_rel = |u'(0)|²_rel/|u'(0)|²_n.r., α_s(√σ) = 2π/(b₀ ln(√σ/Λ)), the contact term
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
