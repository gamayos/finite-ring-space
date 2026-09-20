"""
d_classification.py — block D: the classification and the Euler-product discriminator (00:D12)
=============================================================================================
Proposition turing: C(T) ≤ N_crit(T) ≤ N(T); RH below T is N = N_crit; C = N is Turing's practical
certificate; the shell reads N from the comb (raw count, uncertified) and C from the de-framing
(sign changes of the main sum). Definition screen: the classical hypothesis is read as the screen
value N − N_crit = 0. Numerical Observation dh: the value is discriminating — the Davenport–
Heilbronn function f (no Euler product) opens a phantom deficit of 2 at its first off-line pair
while its constituent L(s, χ) closes with deficit 0; on the comb side the secular condition
lands two "on-line" roots on the phantom height and the raw count near it does not settle with
depth; the ζ comb behaves the same way at ζ's own singularity to the right of the line, the pole.

Paper-local predicates:

  D1  Prop. turing / Def. screen     [approx]  at T = 15, 30, 50.3 the raw comb count Ñ_N rounds to the exact
                                                N = 1, 3, 10, and the sign changes of the horizon main sum Z_M on
                                                (0, T) — the de-framing side — give C = 1, 3, 10 = N (Turing's
                                                certificate read on the shell, both readings uncertified)
  D2a Obs. dh  [approx]  Λ_f(½ + it) is real to 10⁻²⁰ (self-dual normalisation of the DH function)
  D2b Obs. dh  [approx]  argument principle per band on [0, 87]: N_f = 45 strip zeros against C_f = 43 on-line sign
                         changes, the deficit 2 opening only in the band holding the off-line pair
                         s = 0.8085171825 + 85.6993484854 i (validated |f(s)| < 10⁻⁶); |Z_f| dips to 0.357 at
                         t = 85.71 without crossing; positive control L(s, χ): 45 = 45, deficit 0 in every band
  D2c Obs. dh  [approx]  negative control: the secular condition on the Λ_f comb returns two "on-line" roots in
                         [84, 87], 85.63 / 85.76 (comb to 10⁵) and 85.65 / 85.75 (4×10⁵), at the phantom height —
                         the upward crossings of the levels 43.5 and 44.5 between the exact counts 43 and 45.
                         (Package finding: at 4×10⁵ the unsettled count also swings below 42.5 and above 45.5 in
                         [85.3, 86.1], adding two crossing pairs the paper's sentence does not mention; at 10⁵ the
                         excursion stays within (42.5, 45.5) and the two roots are the only crossings.)
  D2d Obs. dh  [approx]  the raw DH comb count at t = 85.9 drifts monotonically with depth, 45.14 → 45.73 over
                         5×10⁴ … 8×10⁵ (exact 45); at 85.3 it reads 42.66 … 42.73 (exact 43; the paper's two figures
                         are the endpoint depths, the interior depths dip to 42.64); away from the pair it is
                         stable: 28.005 ± 0.002 at 60.3 and 43.00 ± 0.01 at 84.0
  D2e Obs. dh  [approx]  the ζ comb at the pole: at t = 1 (exact 0) the raw count reads +0.09, −0.26, +0.36, −0.08,
                         −0.81, −1.42, −1.46 at depths 10⁴ … 8×10⁷; at t = 5 within ±0.02; at t = 10 within ±0.003;
                         at t = 15 within 2×10⁻³ of 1 at every depth; at t = 30 from 3.04 to 2.998; at 50.3 within
                         10⁻² of 10 (depths to 8×10⁵)
  D2f Prop. combformula, Obs. dh  [approx]  the pole-corrected ζ count N̂_N at t = 1 reads 0.0051, 0.0032, 0.0022, 0.0016, 0.0015,
                         0.0013, 0.0012 at the same depths (exact 0), falling monotonically; at t = 5 and 10 within 4×10⁻⁴ from
                         10⁶ on, falling in magnitude; at 15, 30, 50.3 the correction is below 10⁻³ and raw and corrected agree
  D2g Rem. combsettle, Obs. dh    [approx]  the DH drift is the zero term of the off-line zero ρ₀: the count corrected by it and its constant reads
                         44.960, 44.964, 44.967, 44.970, 44.972 at t = 85.9 (raw 45.14 … 45.73; exact 45) and 43.035 → 43.022
                         at 85.3 (raw 42.66 … 42.73; exact 43), both monotone toward the exact count
  D3  Prop. combformula  [approx]  the identity's validation arm: the corrected tapered sum Σ_w − Π_N − log((s−1)/s) against
                         log ζ(½ + it) (mpmath) at t = 1, 5, 10, 15, 30: the real-part error falls with depth at every height
                         (0.0049 at t = 1, depth 8×10⁷) and the imaginary part is the corrected count of D2f
  D4  Prop. turing (frame-exact inputs)  [approx]  on the shells p = 97, 1009, 4801 (primes ≡ 1 mod 4; ceilings T = 2πp ≈ 609, 6340,
                         30166) the raw count from the frame-exact comb of depth ⌊√p⌋ = 9, 31, 69, evaluated midway between
                         consecutive zeros just below the ceiling (the test heights chosen with the validation arm: zeros from
                         Z(t) sign changes, the count from mpmath nzeros), rounds to the exact N(t) at every midpoint: maximum
                         deviation 0.079, 0.107, 0.164 (within 0.08, 0.11, 0.17); the 10⁶ comb within 0.002

The "ζ never evaluated" discipline does not bind the control arms (Hurwitz zeta functions are
evaluated there). Figure: fig_dh.pdf. Master ledger: 00:D12.
"""
import math
import numpy as np
import mpmath as mp
import matplotlib
matplotlib.use("Agg")
import matplotlib.pyplot as plt
from scipy.optimize import brentq
from scipy.special import loggamma
from rhcommon import (check, Comb, von_mangoldt_support, count_raw, count_corrected, pole_term, pole_count_term, theta, HEIGHTS, FIGDIR, FAST, Timer)

mp.mp.dps = 20
I = mp.mpc(0, 1)
CHI = {1: mp.mpc(1), 2: I, 3: -I, 4: mp.mpc(-1)}                 # complex character mod 5, χ(2) = i
KAPPA = (mp.sqrt(10 - 2 * mp.sqrt(5)) - 2) / (mp.sqrt(5) - 1)
TAU = sum(CHI[a] * mp.expjpi(mp.mpf(2 * a) / 5) for a in (1, 2, 3, 4))
EPS_HALF = mp.sqrt(TAU / (I * mp.sqrt(5)))                       # half-phase of the root number of χ
RHO_OFF = mp.mpc("0.8085171825", "85.6993484854")               # Titchmarsh: the first off-line pair, with 1 − s̄
T_HI = 87.0
DEPTHS_DH = [50_000, 100_000, 200_000, 400_000, 800_000]
DEPTHS_Z = [10 ** 4, 10 ** 5, 10 ** 6, 10 ** 7, 2 * 10 ** 7, 4 * 10 ** 7, 8 * 10 ** 7] if not FAST else [10 ** 4, 10 ** 5, 10 ** 6, 10 ** 7]
STATED_T1 = [0.09, -0.26, 0.36, -0.08, -0.81, -1.42, -1.46]

# ------------------------------------------------------------------ the validation arm: f and L(s, χ) via Hurwitz zeta
def L_pair(s):
    z = {a: mp.zeta(s, mp.mpf(a) / 5) for a in (1, 2, 3, 4)}
    five = mp.power(5, -s)
    return five * sum(CHI[a] * z[a] for a in (1, 2, 3, 4)), five * sum(mp.conj(CHI[a]) * z[a] for a in (1, 2, 3, 4))

def pair_values(s):
    """(L(s,χ), f(s)) with f = (1 − iκ)/2 L(s,χ) + (1 + iκ)/2 L(s,χ̄)."""
    Lchi, Lbar = L_pair(s)
    return Lchi, (1 - I * KAPPA) / 2 * Lchi + (1 + I * KAPPA) / 2 * Lbar

def gamma_factor(s):
    return mp.power(5 / mp.pi, (s + 1) / 2) * mp.gamma((s + 1) / 2)

def hardy_pair(t):
    """Hardy-normalised on-line readouts (Z_χ(t), Z_f(t)), both real: |Z| = |value on the line|."""
    s = mp.mpf(1) / 2 + I * t
    g = gamma_factor(s); ph = g / abs(g)
    Lchi, f = pair_values(s)
    return ph * Lchi / EPS_HALF, ph * f

def theta_f(t):
    """Twisted archimedean phase of the conductor-5 odd Γ-factor: Im log Γ(¾ + it/2) + (t/2) log(5/π)."""
    t = np.asarray(t, float)
    return np.imag(loggamma(0.75 + 0.5j * t)) + 0.5 * t * math.log(5 / math.pi)

def sign_changes(ts, vals):
    pos = []
    for k in range(1, len(ts)):
        a, b = vals[k - 1], vals[k]
        if a * b < 0:
            pos.append(ts[k - 1] + (ts[k] - ts[k - 1]) * a / (a - b))
    return np.array(pos)

def winding(fn_values, corners, step):
    """Winding numbers of several functions around a rectangle, by continuous phase tracking with
    adaptive refinement; fn_values(s) returns a tuple of complex values (one per function)."""
    (s0, s1, s2, s3) = corners
    sides = [(s0, s1), (s1, s2), (s2, s3), (s3, s0)]
    total = None
    for a, b in sides:
        n = max(2, int(abs(b - a) / step) + 1)
        pts = [a + (b - a) * k / (n - 1) for k in range(n)]
        vals = [fn_values(s) for s in pts]
        m = len(vals[0])
        acc = np.zeros(m)
        stack = list(zip(pts[:-1], pts[1:], vals[:-1], vals[1:], [0] * (n - 1)))
        while stack:
            pa, pb, va, vb, depth = stack.pop()
            d = np.array([float(mp.arg(vb[i] / va[i])) for i in range(m)])
            if np.max(np.abs(d)) > 0.8 and depth < 12:
                pm = (pa + pb) / 2; vm = fn_values(pm)
                stack.append((pa, pm, va, vm, depth + 1)); stack.append((pm, pb, vm, vb, depth + 1))
            else:
                acc += d
        total = acc if total is None else total + acc
    w = total / (2 * math.pi)
    assert np.max(np.abs(w - np.round(w))) < 0.05, f"non-integer winding {w}"
    return np.round(w).astype(int)

# ------------------------------------------------------------------ the generalized von Mangoldt comb of f
def dh_lambda(M):
    """Λ_f(n) for n ≤ M from −f'/f = Σ Λ_f(n) n^{−s}, by the divisor recursion a_n log n = Σ_{d|n} Λ_f(d) a_{n/d}, a_1 = 1."""
    kappa = float(KAPPA)
    n = np.arange(M + 1)
    cvals = np.array([0, 1, 1j, -1j, -1], dtype=complex)[n % 5]
    a = ((1 - 1j * kappa) / 2 * cvals + (1 + 1j * kappa) / 2 * np.conj(cvals)).real
    logs = np.log(np.maximum(n, 1).astype(float))
    Lf = np.zeros(M + 1); conv = np.zeros(M + 1)
    for k in range(2, M + 1):
        Lf[k] = a[k] * logs[k] - conv[k]
        if Lf[k] != 0.0:
            ms = np.arange(2, M // k + 1)
            conv[k * ms] += Lf[k] * a[ms]
    return Lf

def comb_support_from(Lf):
    def lam_fn(N):
        idx = np.nonzero(Lf[:N + 1])[0]
        return idx.astype(float), Lf[idx]
    return lam_fn

def count_at_depths(n_all, lam_all, t, depths, theta_fn, const):
    """Raw comb count at height t for several depths from one support (taper log N per depth)."""
    logn = np.log(n_all); out = []
    for N in depths:
        m = n_all <= N
        w = 0.5 * (1 + np.cos(np.pi * logn[m] / math.log(N)))
        terms = lam_all[m] / (np.sqrt(n_all[m]) * logn[m]) * w * np.sin(t * logn[m])
        out.append(float(theta_fn(t)) / math.pi + const - math.fsum(terms) / math.pi)
    return np.array(out)

def corrected_at_depths(n_all, lam_all, t, depths):
    """Pole-corrected ζ count N̂_N(t) at several depths from one support (Prop. combformula)."""
    raw = count_at_depths(n_all, lam_all, t, depths, theta, 1.0)
    return raw - np.array([pole_count_term(N, t) for N in depths])

def zero_cut_term(N, t, rho0):
    """The zero term of one fixed zero ρ₀ = β₀ + iγ₀ to the right of the line (½ < β₀ < 3/2) at s = ½ + it
    (Remark combsettle): Π^{(ρ₀)}_N(s) = ∫_0^L W(u/L) (e^{(ρ₀−s)u} − e^{(ρ₀−1−s)u}) du/u, L = log N. The image of the
    regulariser h_{ρ₀}(w) = log((w−ρ₀)/(w−ρ₀+1)) under the window inversion of Prop. combformula (i) is −Π^{(ρ₀)}_N,
    the term the zero contributes to the smoothed sum. The routine evaluates this one integral at depth N and
    asserts nothing about a limit N → ∞: the paper does not extend the identity of Prop. combformula to a series
    with infinitely many zeros to the right of the line. The Davenport–Heilbronn correction
    N̂_{f,N} = Ñ_{f,N} + Im[Π^{(ρ₀)}_N(s) + h_{ρ₀}(s)]/π (dh_corrected_at_depths, D2g) is validated over the depths
    listed there."""
    L = math.log(N); a = rho0 - mp.mpc(0.5, t); b = a - 1
    f = lambda u: 0.5 * (1 + mp.cos(mp.pi * u / L)) * (mp.exp(a * u) - mp.exp(b * u)) / u
    return mp.quad(f, mp.linspace(0, L, 40))

def dh_corrected_at_depths(n_all, lam_all, t, depths):
    """The DH comb count corrected by the zero term of ρ₀ and its constant (D2g; Remark combsettle):
    N̂_{f,N} = Ñ_{f,N} + Im[Π^{(ρ₀)}_N(s) + h_{ρ₀}(s)]/π, with h_{ρ₀}(s) = −H0 below."""
    s = mp.mpc(0.5, t); H0 = mp.log((s - RHO_OFF + 1) / (s - RHO_OFF))
    raw = count_at_depths(n_all, lam_all, t, depths, theta_f, 0.0)
    return raw + np.array([float(mp.im(zero_cut_term(N, t, RHO_OFF) - H0)) / math.pi for N in depths])

def Z_main(t):
    """The horizon-length Riemann–Siegel main sum (Definition deframe), the de-framing side of Proposition turing."""
    N = int(math.floor(math.sqrt(t / (2 * math.pi))))
    th = float(theta(t))
    return 2 * sum(math.cos(th - t * math.log(n)) / math.sqrt(n) for n in range(1, N + 1))

def run():
    print("\n== block D: the screen reading and its Davenport–Heilbronn control (Prop. turing, Def. screen, Obs. dh) ==")
    # ---------------- D1: the two readings on ζ
    comb = Comb(10 ** 6)
    Tq = np.array([15.0, 30.0, 50.3]); exact = [1, 3, 10]
    raw = count_raw(comb, Tq)
    tgrid = np.arange(0.5, 50.3, 0.02)
    zm = np.array([Z_main(t) for t in tgrid])
    Cm = [int(np.sum(zm[:-1][tgrid[:-1] < T] * zm[1:][tgrid[:-1] < T] < 0)) for T in Tq]
    ok = all(int(round(r)) == e for r, e in zip(raw, exact)) and Cm == exact
    check("D1", "Ñ_N rounds to N = 1, 3, 10 at T = 15, 30, 50.3; sign changes of the main sum Z_M give C = 1, 3, 10 = N", ok,
          "raw " + ", ".join(f"{r:.4f}" for r in raw) + f"; C_M = {Cm}", kind="[approx]")
    # ---------------- D2a: reality of Λ_f on the line
    with mp.workdps(30):
        im = max(abs(mp.im(gamma_factor(mp.mpf(1) / 2 + I * t) * pair_values(mp.mpf(1) / 2 + I * t)[1])) for t in np.linspace(0.7, 86.3, 25))
    check("D2a", "the completed Λ_f(½ + it) is real on the line to 10⁻²⁰", im < 1e-20, f"max |Im Λ_f| = {float(im):.1e} over 25 heights", kind="[approx]")
    # ---------------- D2b: strip counts by the argument principle against on-line sign changes
    with Timer("on-line grid (Hurwitz zeta)"):
        dt = 0.02 if not FAST else 0.04
        ts = np.arange(0.1, T_HI + dt / 2, dt)
        Zc = np.empty_like(ts); Zf = np.empty_like(ts)
        for k, t in enumerate(ts):
            zc, zf = hardy_pair(mp.mpf(float(t)))
            assert abs(mp.im(zc)) < 1e-9 and abs(mp.im(zf)) < 1e-9
            Zc[k], Zf[k] = float(mp.re(zc)), float(mp.re(zf))
    zeros_f, zeros_c = sign_changes(ts, Zf), sign_changes(ts, Zc)
    off_err = abs(pair_values(RHO_OFF)[1])
    band = (ts > 85.0) & (ts < 86.5); k_dip = np.argmin(np.abs(Zf[band])); t_dip, z_dip = ts[band][k_dip], abs(Zf[band][k_dip])
    # band boundaries: multiples of 3, nudged away from every on-line zero of both functions
    allz = np.concatenate([zeros_f, zeros_c])
    bounds = [0.1]
    for b in np.arange(3.0, T_HI + 0.1, 3.0):
        while np.min(np.abs(allz - b)) < 0.15: b += 0.2
        bounds.append(min(b, T_HI))
    with Timer(f"argument principle on {len(bounds) - 1} bands (Hurwitz zeta)"):
        step = 0.05 if not FAST else 0.1
        Nf_band, Nc_band = [], []
        for lo, hi in zip(bounds[:-1], bounds[1:]):
            corners = (mp.mpc(-1.5, lo), mp.mpc(2.5, lo), mp.mpc(2.5, hi), mp.mpc(-1.5, hi))
            wc, wf = winding(pair_values, corners, step)
            Nc_band.append(wc); Nf_band.append(wf)
    Cf_band = [int(np.sum((zeros_f > lo) & (zeros_f < hi))) for lo, hi in zip(bounds[:-1], bounds[1:])]
    Cc_band = [int(np.sum((zeros_c > lo) & (zeros_c < hi))) for lo, hi in zip(bounds[:-1], bounds[1:])]
    deficit_f = np.array(Nf_band) - np.array(Cf_band); deficit_c = np.array(Nc_band) - np.array(Cc_band)
    kband = next(i for i, (lo, hi) in enumerate(zip(bounds[:-1], bounds[1:])) if lo < 85.6993 < hi)
    ok = (sum(Nf_band) == 45 and len(zeros_f) == 43 and sum(Nc_band) == 45 and len(zeros_c) == 45
          and deficit_f[kband] == 2 and all(d == 0 for i, d in enumerate(deficit_f) if i != kband) and all(d == 0 for d in deficit_c)
          and off_err < 1e-6 and abs(z_dip - 0.357) < 0.01 and abs(t_dip - 85.71) < 0.03)
    check("D2b", "argument principle on [0,87]: f: 45 strip zeros vs 43 on-line, deficit 2 only in the band of the off-line pair; L(s,χ): 45 = 45, deficit 0 everywhere", ok,
          f"f: N = {sum(Nf_band)}, C = {len(zeros_f)}, deficit by band {[int(d) for d in deficit_f]}; L(s,χ): N = {sum(Nc_band)}, C = {len(zeros_c)}; "
          f"|f(s_off)| = {float(off_err):.1e}; |Z_f| dips to {z_dip:.3f} at t = {t_dip:.2f}", kind="[approx]")
    # ---------------- D2c, D2d: the comb side of f
    with Timer("Λ_f comb to 8e5 (divisor recursion)"):
        Lf = dh_lambda(DEPTHS_DH[-1])
    lam_fn = comb_support_from(Lf)
    roots, extra, excursion = {}, {}, {}
    for M in (10 ** 5, 4 * 10 ** 5):
        c = Comb(M, lam_fn=lam_fn)
        tt = np.linspace(84, 87, 601); v = count_raw(c, tt, const=0.0, theta_fn=theta_f)
        cross = []                                   # every half-integer crossing (t, level, direction)
        for i in range(len(tt) - 1):
            lo, hi = v[i], v[i + 1]
            for h in np.arange(math.floor(min(lo, hi)) + 0.5, max(lo, hi), 1.0):
                if (lo - h) * (hi - h) < 0:
                    cross.append((brentq(lambda t: count_raw(c, t, const=0.0, theta_fn=theta_f) - h, tt[i], tt[i + 1]), h, np.sign(hi - lo)))
        # the phantom roots: the upward crossings of the two levels 43.5, 44.5 between the exact counts 43 (below the pair) and 45 (above)
        roots[M] = sorted(t for t, h, d in cross if h in (43.5, 44.5) and d > 0)
        extra[M] = sorted((round(t, 2), h) for t, h, d in cross if h not in (43.5, 44.5))
        excursion[M] = (v[(tt > 85) & (tt < 86.4)].min(), v[(tt > 85) & (tt < 86.4)].max())
    ok = (len(roots[10 ** 5]) == 2 and len(roots[4 * 10 ** 5]) == 2 and len(extra[10 ** 5]) == 0
          and np.allclose(roots[10 ** 5], [85.63, 85.76], atol=0.015) and np.allclose(roots[4 * 10 ** 5], [85.65, 85.75], atol=0.015))
    check("D2c", "the secular condition on the Λ_f comb returns two 'on-line' roots at the phantom height: 85.63/85.76 (10⁵), 85.65/85.75 (4×10⁵)", ok,
          f"10⁵: {np.round(roots[10 ** 5], 3).tolist()} (no other crossing in [84,87]; count excursion {excursion[10 ** 5][0]:.2f}–{excursion[10 ** 5][1]:.2f}); "
          f"4×10⁵: {np.round(roots[4 * 10 ** 5], 3).tolist()}, plus the swing of the unsettled count through the levels {sorted(set(float(h) for _, h in extra[4 * 10 ** 5]))} "
          f"(excursion {excursion[4 * 10 ** 5][0]:.2f}–{excursion[4 * 10 ** 5][1]:.2f}; crossing pairs at {[t for t, _ in extra[4 * 10 ** 5]]})", kind="[approx]")
    idx = np.nonzero(Lf)[0]; nf, lf = idx.astype(float), Lf[idx]
    scan = {t: count_at_depths(nf, lf, t, DEPTHS_DH, theta_f, 0.0) for t in (85.9, 85.3, 60.3, 84.0)}
    s859 = scan[85.9]
    ok = (np.allclose(s859, [45.14, 45.27, 45.41, 45.57, 45.73], atol=0.015) and np.all(np.diff(s859) > 0)
          and abs(scan[85.3][0] - 42.66) < 0.006 and abs(scan[85.3][-1] - 42.73) < 0.006 and scan[85.3].min() > 42.63 and scan[85.3].max() < 42.74
          and np.all(np.abs(scan[60.3] - 28.005) < 0.003) and np.all(np.abs(scan[84.0] - 43.0) < 0.011))
    check("D2d", "raw DH comb count drifts monotonically at t = 85.9 (45.14 → 45.73) and reads 42.66 … 42.73 at 85.3 (interior depths dip to 42.64); stable at 60.3 (28.005 ± 0.002) and 84.0 (43.00 ± 0.01)", ok,
          "; ".join(f"t={t}: " + ", ".join(f"{v:.3f}" for v in vals) for t, vals in scan.items()), kind="[approx]")
    # ---------------- D2e: the ζ comb at the pole
    with Timer(f"ζ comb support to {DEPTHS_Z[-1]:.0e}"):
        n_all, lam_all = von_mangoldt_support(DEPTHS_Z[-1])
    z1 = count_at_depths(n_all, lam_all, 1.0, DEPTHS_Z, theta, 1.0)
    z5 = count_at_depths(n_all, lam_all, 5.0, DEPTHS_Z, theta, 1.0)
    z10 = count_at_depths(n_all, lam_all, 10.0, DEPTHS_Z, theta, 1.0)
    z15 = count_at_depths(n_all, lam_all, 15.0, DEPTHS_Z, theta, 1.0)
    z30 = count_at_depths(n_all, lam_all, 30.0, DEPTHS_Z, theta, 1.0)
    z503 = count_at_depths(n_all, lam_all, 50.3, [d for d in DEPTHS_Z if d <= 8 * 10 ** 5] + [8 * 10 ** 5], theta, 1.0)
    k = len(DEPTHS_Z)
    ok = (np.allclose(z1, STATED_T1[:k], atol=0.015) and np.all(np.abs(z5) < 0.021) and np.all(np.abs(z10) < 0.0031)
          and np.all(np.abs(z15 - 1) < 2e-3) and abs(z30[0] - 3.04) < 0.006 and abs(z30[-1] - (2.998 if not FAST else z30[-1])) < 0.002
          and np.all(np.abs(z503 - 10) < 1e-2))
    check("D2e", "ζ comb at the pole: t = 1 reads +0.09, −0.26, +0.36, −0.08, −0.81, −1.42, −1.46 with depth (exact 0); t = 5, 10 within ±0.02, ±0.003; t = 15 within 2e-3 of 1; t = 30 3.04 → 2.998; t = 50.3 within 1e-2 of 10", ok,
          "t=1: " + ", ".join(f"{v:+.2f}" for v in z1) + "; t=5: max|·| " + f"{np.max(np.abs(z5)):.3f}" + "; t=10: " + f"{np.max(np.abs(z10)):.4f}"
          + "; t=15: max dev " + f"{np.max(np.abs(z15 - 1)):.1e}" + f"; t=30: {z30[0]:.3f} → {z30[-1]:.3f}; t=50.3: max dev {np.max(np.abs(z503 - 10)):.1e}", kind="[approx]")
    # ---------------- D2f: the pole-corrected ζ count settles (Prop. combformula)
    c1 = corrected_at_depths(n_all, lam_all, 1.0, DEPTHS_Z); c5 = corrected_at_depths(n_all, lam_all, 5.0, DEPTHS_Z); c10 = corrected_at_depths(n_all, lam_all, 10.0, DEPTHS_Z)
    stated_c1 = [0.0051, 0.0032, 0.0022, 0.0016, 0.0015, 0.0013, 0.0012][:k]
    i6 = DEPTHS_Z.index(10 ** 6)
    ok = (np.allclose(c1, stated_c1, atol=0.0003) and np.all(np.diff(c1) < 0) and np.all(np.abs(c5[i6:]) < 4e-4) and np.all(np.abs(c10[i6:]) < 4e-4)
          and np.all(np.diff(np.abs(c5)) < 0) and np.all(np.diff(np.abs(c10)) < 0))
    check("D2f", "pole-corrected ζ count at t = 1: 0.0051, 0.0032, 0.0022, 0.0016, 0.0015, 0.0013, 0.0012 (exact 0), monotone; t = 5, 10 within 4e-4 from 10⁶ on, falling", ok,
          "t=1: " + ", ".join(f"{v:+.4f}" for v in c1) + "; t=5: " + ", ".join(f"{v:+.5f}" for v in c5) + "; t=10: " + ", ".join(f"{v:+.5f}" for v in c10), kind="[approx]")
    # ---------------- D2g: the DH drift is the zero term of the off-line zero (Remark combsettle)
    with Timer("DH corrected counts"):
        d859 = dh_corrected_at_depths(nf, lf, 85.9, DEPTHS_DH); d853 = dh_corrected_at_depths(nf, lf, 85.3, DEPTHS_DH)
    ok = (np.allclose(d859, [44.960, 44.964, 44.967, 44.970, 44.972], atol=0.002) and np.all(np.diff(d859) > 0)
          and np.allclose(d853, [43.035, 43.031, 43.028, 43.025, 43.022], atol=0.002) and np.all(np.diff(d853) < 0))
    check("D2g", "DH count corrected by the zero term of ρ₀ and its constant: 44.960 → 44.972 at 85.9 (raw 45.14 → 45.73; exact 45), 43.035 → 43.022 at 85.3 (exact 43), monotone toward the exact count", ok,
          "t=85.9: " + ", ".join(f"{v:.4f}" for v in d859) + "; t=85.3: " + ", ".join(f"{v:.4f}" for v in d853), kind="[approx]")
    # ---------------- D3: the identity against log ζ (validation arm: mpmath)
    logn_all = np.log(n_all); re_err = {}
    for t, Nc in ((1.0, 0), (5.0, 0), (10.0, 0), (15.0, 1), (30.0, 3)):
        sc = mp.mpc(0.5, t); lz_re = float(mp.log(abs(mp.zeta(sc))))
        errs = []
        for N in DEPTHS_Z:
            m = n_all <= N; L = math.log(N); w = 0.5 * (1 + np.cos(np.pi * logn_all[m] / L))
            S = np.sum(lam_all[m] * w / (np.sqrt(n_all[m]) * logn_all[m]) * np.exp(-1j * t * logn_all[m]))
            errs.append(abs((S - pole_term(N, t) - complex(mp.log((sc - 1) / sc))).real - lz_re))
        re_err[t] = np.array(errs)
    ok = all(np.all(np.diff(e) < 0) for e in re_err.values()) and re_err[1.0][-1] < (0.0052 if not FAST else 0.0065)
    check("D3", "the identity's validation arm: Re(Σ_w − Π_N − log((s−1)/s)) → log|ζ(½+it)| at t = 1, 5, 10, 15, 30, the error falling with depth (0.0049 at t = 1, 8×10⁷)", ok,
          "; ".join(f"t={t}: " + " → ".join(f"{v:.4f}" for v in (e[0], e[len(e)//2], e[-1])) for t, e in re_err.items()), kind="[approx]")
    # ---------------- D4: the count from the frame-exact comb on one shell (Proposition turing)
    with Timer("frame-exact shells"):
        shells = [97, 1009] + ([4801] if not FAST else [])          # primes ≡ 1 (mod 4): admissible Subject shells
        dev_fe, dev_deep, dev_smooth, npts = {}, {}, {}, {}
        deep = Comb(10 ** 6)
        for p_sh in shells:
            Tc = 2 * math.pi * p_sh; depth = int(math.floor(math.sqrt(p_sh)))
            grid = np.arange(Tc - 12.0, Tc + 1e-9, 0.1); zv = np.array([float(mp.siegelz(t)) for t in grid])
            zs = np.array([brentq(lambda t: float(mp.siegelz(t)), grid[i], grid[i + 1], xtol=1e-7)
                           for i in range(len(grid) - 1) if zv[i] * zv[i + 1] < 0])
            mids = 0.5 * (zs[1:] + zs[:-1]); nz = np.array([int(mp.nzeros(t)) for t in mids]); npts[p_sh] = len(mids)
            v = count_raw(Comb(depth), mids); vd = count_raw(deep, mids)
            vs = np.array([float(theta(t)) / math.pi + 1 for t in mids])       # the control: the smooth term alone
            dev_fe[p_sh] = (float(np.max(np.abs(v - nz))), bool(np.all(np.round(v) == nz)))
            dev_deep[p_sh] = (float(np.max(np.abs(vd - nz))), bool(np.all(np.round(vd) == nz)))
            dev_smooth[p_sh] = (float(np.max(np.abs(vs - nz))), bool(np.all(np.round(vs) == nz)))
    stated = {97: 0.079, 1009: 0.107, 4801: 0.164}
    stated_smooth = {97: (0.268, True), 1009: (0.498, True), 4801: (0.523, False)}
    ok = (all(r for _, r in dev_fe.values()) and all(r for _, r in dev_deep.values())
          and all(abs(dev_fe[p_sh][0] - stated[p_sh]) < 0.02 for p_sh in shells) and max(d for d, _ in dev_deep.values()) < 0.004
          and all(abs(dev_smooth[p_sh][0] - stated_smooth[p_sh][0]) < 0.02 and dev_smooth[p_sh][1] == stated_smooth[p_sh][1] for p_sh in shells))
    check("D4", "frame-exact count on one shell: at p = 97, 1009, 4801 (T = 2πp) the depth-⌊√p⌋ comb, midway between consecutive zeros below the ceiling, rounds to the exact N(t) at every midpoint (max deviation 0.079, 0.107, 0.164 — within 0.08, 0.11, 0.17); the 10⁶ comb within 0.002; the control θ(t)/π + 1 alone deviates by 0.27, 0.498, 0.52 and fails to round at one midpoint of p = 4801", ok,
          "; ".join(f"p={p_sh} (depth {int(math.sqrt(p_sh))}, {npts[p_sh]} midpoints): max dev {dev_fe[p_sh][0]:.3f} (10⁶ comb {dev_deep[p_sh][0]:.3f}; smooth term alone {dev_smooth[p_sh][0]:.3f}, rounds {dev_smooth[p_sh][1]})" for p_sh in shells), kind="[approx]")
    # ---------------- figure
    with Timer("window grid [84,87]"):
        tw = np.arange(84.0, 87.0 + 1e-9, 0.005 if not FAST else 0.01)
        Zcw = np.empty_like(tw); Zfw = np.empty_like(tw)
        for j, t in enumerate(tw):
            zc, zf = hardy_pair(mp.mpf(float(t))); Zcw[j], Zfw[j] = float(mp.re(zc)), float(mp.re(zf))
    crimson, gray = "#c8102e", "0.40"
    fig, ax = plt.subplots(1, 3, figsize=(16, 4.3), gridspec_kw={"width_ratios": [1.15, 1.0, 1.0]})
    ax[0].axhline(0, color="0.65", lw=0.8)
    ax[0].plot(tw, Zcw, color=gray, lw=1.6, label=r"$Z_\chi(t)$: constituent $L(s,\chi)$ (crosses)")
    ax[0].plot(tw, Zfw, color=crimson, lw=2.0, label=r"$Z_f(t)$: Davenport–Heilbronn (dips, no crossing)")
    ax[0].axvline(float(mp.im(RHO_OFF)), color=crimson, lw=1.0, ls=":")
    ax[0].set_xlim(84, 87); ax[0].set_ylim(-7.2, 1.7); ax[0].set_xlabel("$t$"); ax[0].set_ylabel("rotated on-line value")
    ax[0].set_title(f"D2b: the phantom on the line — dip {z_dip:.3f} at t = {t_dip:.2f}", fontsize=10); ax[0].legend(loc="lower left", fontsize=8)
    # staircases: strip count from the band windings, on-line count from the sign changes
    xs_on = np.concatenate([[0], np.sort(zeros_f), [T_HI]]); ys_on = np.concatenate([[0], np.arange(1, len(zeros_f) + 1), [len(zeros_f)]])
    # strip count: on-line zeros plus the band excess placed at the off-line height
    jumps = sorted([(z, 1) for z in zeros_f] + [(float(mp.im(RHO_OFF)), int(deficit_f[kband]))])
    xs_s, ys_s, c = [0.0], [0], 0
    for z, j in jumps: xs_s.append(z); c += j; ys_s.append(c)
    xs_s.append(T_HI); ys_s.append(c)
    ax[1].step(xs_s, ys_s, where="post", color=crimson, lw=1.9, label=r"$N_f(t)$: strip count (argument principle by band)")
    ax[1].step(xs_on, ys_on, where="post", color=gray, lw=1.4, ls="--", label=r"$N_{\rm crit}(t)$: on-line sign changes")
    ax[1].axvline(float(mp.im(RHO_OFF)), color=crimson, lw=1.0, ls=":")
    ax[1].set_xlim(0, T_HI); ax[1].set_ylim(0, 47.5); ax[1].set_xlabel("$t$"); ax[1].set_ylabel("cumulative zero count")
    ax[1].set_title(f"deficit on [0,87]: $N_f={sum(Nf_band)}$, $C={len(zeros_f)}$; control $L(s,\\chi)$: {sum(Nc_band)}={len(zeros_c)}", fontsize=10)
    ax[1].legend(loc="upper left", fontsize=8)
    axins = ax[1].inset_axes([0.60, 0.08, 0.38, 0.40])
    axins.step(xs_s, ys_s, where="post", color=crimson, lw=1.9); axins.step(xs_on, ys_on, where="post", color=gray, lw=1.4, ls="--")
    axins.set_xlim(84, 87); axins.set_ylim(40, 46.5); axins.tick_params(labelsize=7); axins.set_title(r"$N_f-N_{\rm crit}=2$", fontsize=8)
    # depth drift
    ax[2].semilogx(DEPTHS_DH, scan[85.9], "o-", color=crimson, label="DH comb, t = 85.9 (exact 45)")
    ax[2].semilogx(DEPTHS_DH, scan[84.0], "s-", color="#e59866", label="DH comb, t = 84.0 (exact 43)")
    ax[2].axhline(45, color=crimson, lw=0.8, ls=":"); ax[2].axhline(43, color="#e59866", lw=0.8, ls=":")
    ax2 = ax[2].twinx()
    ax2.semilogx(DEPTHS_Z, z1, "^-", color="#10325f", label="ζ comb, t = 1 (exact 0)")
    ax2.semilogx(DEPTHS_Z, c1, "^--", color="#1f6b4a", label="ζ comb, t = 1, pole-corrected")
    ax2.semilogx(DEPTHS_Z, z15, "v-", color="#5b9bd5", label="ζ comb, t = 15 (exact 1)")
    ax2.axhline(0, color="#10325f", lw=0.8, ls=":"); ax2.axhline(1, color="#5b9bd5", lw=0.8, ls=":")
    ax[2].set_xlabel("comb depth $N$"); ax[2].set_ylabel("raw DH count", color=crimson); ax2.set_ylabel("raw ζ count", color="#10325f")
    ax[2].set_title("D2d–D2f: the raw count near a singularity, and the pole-corrected count", fontsize=10)
    h1, l1 = ax[2].get_legend_handles_labels(); h2, l2 = ax2.get_legend_handles_labels(); ax[2].legend(h1 + h2, l1 + l2, fontsize=7.5, loc="upper center", bbox_to_anchor=(0.5, -0.17), ncol=2)
    plt.tight_layout(); plt.savefig(f"{FIGDIR}/fig_dh.pdf", bbox_inches="tight"); plt.savefig(f"{FIGDIR}/fig_dh.png", dpi=110, bbox_inches="tight"); plt.close()
    print(f"    wrote {FIGDIR}/fig_dh.pdf")

if __name__ == "__main__":
    from rhcommon import summary
    run(); summary(write=False)
