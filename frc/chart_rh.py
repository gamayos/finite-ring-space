"""frc.chart_rh — 20-rh's readings in floating point (chart tier; ledger migration, task LM36, 7 October 2026).

The chart theme holds the readings against the continuum, the only place where floats appear (frc/themes.py, rank 30).
This file holds the floating-point computations of 20-rh's validation package (src/20-rh/rh.py) that the ledger file
frc/ledgers/p20_rh.py reproduces: the complex characters of the cycle, the Lanczos matrix of a multiset, the
Riemann–Siegel phase and the horizon-length main sum, Hardy's Z by Euler–Maclaurin, and the logarithmic weights of the
resonance. The package used numpy, scipy, sympy and mpmath. This file uses `math` and `cmath` only, so the framework
stays free of third-party imports. Each function returns numbers that the ledger file compares with the package's
stated values; the exact parts (the Ramanujan sums, the resonance in rationals) come from frc/horizon.py.

    HEIGHTS                          the first thirty zero heights of ζ (Odlyzko's tables), validation markers only
    characters(p, g)                 the complex reading of the shell theorem on ℓ²(F_p^×): mean, orthonormality, shift
    lanczos(x)                       the Jacobi matrix (a, b) of the unit-weight measure Σ δ_{x_i}, and its eigenvalues
    theta(t), z_horizon(t)           the Riemann–Siegel phase and the main sum of length ⌊√(t/2π)⌋
    hardy_z(t)                       Z(t) = e^{iθ(t)} ζ(½ + it), ζ by Euler–Maclaurin
    mobius_log_deviation, cesaro_means, hardy_limits, staircase_deviation, band_energy
                                     Λ = μ ∗ log in floating point, the Cesàro limits, the staircase, the band energies
    mode_correlations(p, g)          |corr(1_Π, χ_j)| for every nontrivial chart mode, by a mixed-radix FFT
"""
import cmath
import math

HEIGHTS = [
    14.134725141734693, 21.022039638771555, 25.010857580145688, 30.424876125859513, 32.935061587739189,
    37.586178158825671, 40.918719012147495, 43.327073280914999, 48.005150881167159, 49.773832477672302,
    52.970321477714460, 56.446247697063394, 59.347044002602353, 60.831778524609809, 65.112544048081606,
    67.079810529494173, 69.546401711173979, 72.067157674481907, 75.704690699083933, 77.144840068874805,
    79.337375020249367, 82.910380854086030, 84.735492980517050, 87.425274613125229, 88.809111207634465,
    92.491899270558484, 94.651344040519886, 95.870634228245309, 98.831194218193692, 101.317851005731392]


def vm_float(n, base):
    """Λ(n) in floating point from the prime-power base ℓ of n (None off the prime powers)."""
    return math.log(base) if base else 0.0


# ---- block A: the complex reading of the shell theorem, the Jacobi matrix ------------------------------------------
def characters(p, g, base):
    """The complex characters χ_j(n) = ω^{j λ(n)} on F_p^× (λ the discrete log to g, ω = e^{2πi/(p−1)}) against the
    vector v(n) = Λ(n): (the mean on the trivial mode and the expansion, orthonormality, S χ_j = ω^j χ_j, the mean).
    `base(n)` is the prime-power base of n or None. Tolerance 10⁻¹⁰, as the package's."""
    n = p - 1
    v = [vm_float(m, base(m)) for m in range(1, p)]
    dlog = {}
    x = 1
    for m in range(n):
        dlog[x] = m; x = x * g % p
    w = cmath.exp(2j * math.pi / n)
    chi = [[w ** (j * dlog[m]) for m in range(1, p)] for j in range(n)]
    coef = [sum(chi[j][i].conjugate() * v[i] for i in range(n)) / n for j in range(n)]
    mean = sum(v) / n
    ok_mean = abs(coef[0].real - mean) < 1e-12
    for i in range(n):
        nontriv = sum(coef[j] * chi[j][i] for j in range(1, n)).real
        full = sum(coef[j] * chi[j][i] for j in range(n)).real
        ok_mean = ok_mean and abs(nontriv - (v[i] - mean)) < 1e-10 and abs(full - v[i]) < 1e-10
    ok_orth = all(abs(sum(chi[j][i].conjugate() * chi[k][i] for i in range(n)) / n - (1 if j == k else 0)) < 1e-10
                  for j in range(n) for k in range(n))
    ok_c = all(abs(w ** (j * dlog[g * m % p]) - w ** j * chi[j][m - 1]) < 1e-10 for j in range(n) for m in range(1, p))
    return ok_mean, ok_orth, ok_c, mean


def _sturm_count(a, b, lam):
    """The number of eigenvalues below lam of the symmetric tridiagonal matrix (a on the diagonal, b off it)."""
    c, d = 0, 1.0
    for i in range(len(a)):
        d = a[i] - lam - (b[i - 1] ** 2 / d if i else 0.0)
        if d == 0.0: d = -1e-300
        if d < 0: c += 1
    return c


def lanczos(x):
    """The Jacobi matrix of the unit-weight measure Σ δ_{x_i} (Stieltjes–Lanczos with full reorthogonalisation) and its
    eigenvalues by Sturm bisection: (a, b, eigenvalues ascending)."""
    K = len(x)
    V = [[1 / math.sqrt(K)] * K]
    a, b = [], []
    r = [x[i] * V[0][i] for i in range(K)]
    a.append(sum(V[0][i] * r[i] for i in range(K))); r = [r[i] - a[0] * V[0][i] for i in range(K)]
    for j in range(1, K):
        bj = math.sqrt(sum(t * t for t in r)); b.append(bj)
        vj = [t / bj for t in r]
        for vk in V:
            dot = sum(vk[i] * vj[i] for i in range(K)); vj = [vj[i] - dot * vk[i] for i in range(K)]
        nv = math.sqrt(sum(t * t for t in vj)); vj = [t / nv for t in vj]; V.append(vj)
        r = [x[i] * vj[i] for i in range(K)]
        a.append(sum(vj[i] * r[i] for i in range(K)))
        r = [r[i] - a[j] * vj[i] - b[j - 1] * V[j - 1][i] for i in range(K)]
    lo, hi = min(a) - 2 * sum(b) - 1, max(a) + 2 * sum(b) + 1
    ev = []
    for k in range(K):
        l, h = lo, hi
        for _ in range(200):
            m = (l + h) / 2
            if m in (l, h): break
            if _sturm_count(a, b, m) > k: h = m
            else: l = m
        ev.append((l + h) / 2)
    return a, b, ev


# ---- block B: the de-framing dictionary ------------------------------------------------------------------------------
def theta(t):
    """The Riemann–Siegel phase θ(t) = Im log Γ(¼ + it/2) − (t/2) log π, by its asymptotic series (error below 10⁻¹⁰ for
    t ≥ 10)."""
    return (t / 2 * math.log(t / (2 * math.pi)) - t / 2 - math.pi / 8 + 1 / (48 * t) + 7 / (5760 * t ** 3)
            + 31 / (80640 * t ** 5) + 127 / (430080 * t ** 7))


def z_horizon(t):
    """The Riemann–Siegel main sum of length ⌊√(t/2π)⌋, the shell horizon √p at T = 2πp; no remainder."""
    N = int(math.sqrt(t / (2 * math.pi))); th = theta(t)
    return 2 * sum(math.cos(th - t * math.log(n)) / math.sqrt(n) for n in range(1, N + 1))


_B2K = [(1, 6), (-1, 30), (1, 42), (-1, 30), (5, 66), (-691, 2730), (7, 6), (-3617, 510)]


def zeta(s):
    """ζ(s) for Re s = ½ by Euler–Maclaurin with N ≈ |t|/π + 20 terms and eight Bernoulli corrections."""
    N = int(abs(s.imag) / math.pi) + 20
    tot = sum(cmath.exp(-s * math.log(n)) for n in range(1, N))
    Ns = cmath.exp(-s * math.log(N))
    tot += N * Ns / (s - 1) + Ns / 2
    poch, fact = s, 2
    for k, (num, den) in enumerate(_B2K, 1):
        term = num / den / fact * poch * Ns / N ** (2 * k - 1)
        tot += term
        poch *= (s + 2 * k - 1) * (s + 2 * k); fact *= (2 * k + 1) * (2 * k + 2)
    return tot


def hardy_z(t):
    """Hardy's Z(t) = e^{iθ(t)} ζ(½ + it), real on the line."""
    return (cmath.exp(1j * theta(t)) * zeta(complex(0.5, t))).real


def deframe(stated, ts, T0):
    """Block B's readings: the zero density (1/2π) log p at the stated p; the sign changes of the horizon main sum on ts
    against the heights in (ts[0], ts[-1]); the median residue |Z_horizon − Z| at the heights T0 + 0.123 i, i = 1..15,
    and the fitted log-log slope."""
    dens = {p: math.log(p) / (2 * math.pi) for p in stated}
    zh = [z_horizon(t) for t in ts]
    sc = [ts[i] for i in range(len(ts) - 1) if zh[i] * zh[i + 1] < 0]
    inwin = [h for h in HEIGHTS if ts[0] < h < ts[-1]]
    dev = [min(abs(s - h) for s in sc) for h in inwin]
    err = []
    for t0 in T0:
        e = sorted(abs(z_horizon(t0 + 0.123 * i) - hardy_z(t0 + 0.123 * i)) for i in range(1, 16))
        err.append(e[7])
    X = [math.log(t) for t in T0]; Y = [math.log(e) for e in err]
    mx, my = sum(X) / len(X), sum(Y) / len(Y)
    slope = sum((x - mx) * (y - my) for x, y in zip(X, Y)) / sum((x - mx) ** 2 for x in X)
    return dens, sc, inwin, dev, err, slope


def linspace(a, b, n):
    """n equally spaced points from a to b, as numpy's linspace."""
    return [a + (b - a) * i / (n - 1) for i in range(n)]


# ---- block E: the logarithmic weights ---------------------------------------------------------------------------------
def mobius_log_deviation(N, mu, divisors, base):
    """max over 2 ≤ n ≤ N of |−Σ_{d|n, d>1} μ(d) log d − Λ(n)| in floating point."""
    return max(abs(-sum(mu[d] * math.log(d) for d in divisors(n) if d > 1) - vm_float(n, base(n))) for n in range(2, N + 1))


def hardy_limits(R, phi, base, pps, comp):
    """Cesàro means R(n) (rationals in) against (φ(n)/n) Λ(n): Hardy's limit on the prime powers, 0 off them, and the
    intertwiner (n/φ(n)) R → Λ. Returns (hardy, zero, inter, R as floats)."""
    Rf = {n: float(R[n]) for n in R}
    lam = {n: vm_float(n, base(n)) for n in Rf}
    hardy = all(abs(Rf[n] - phi[n] / n * lam[n]) < 0.02 and abs(Rf[n] - phi[n] / n * lam[n]) < abs(Rf[n] - lam[n]) for n in pps)
    zero = all(abs(Rf[n]) < 0.02 for n in comp)
    inter = all(abs(n / phi[n] * Rf[n] - lam[n]) < 0.03 for n in pps)
    return hardy, zero, inter, Rf, lam


def cesaro_means(Qhi, ns, mu, phi, c):
    """The Cesàro means over L = 1..Qhi of R_L(n) = Σ_{q≤L} μ(q)/φ(q) c_q(n), in floating point, for n in ns."""
    out = {}
    for n in ns:
        cum, tot = 0.0, 0.0
        for q in range(1, Qhi + 1):
            if mu[q]: cum += mu[q] / phi[q] * c(q, n, mu)
            tot += cum
        out[n] = tot / Qhi
    return out


def staircase_deviation(Psi, base, N):
    """max over 2 ≤ n ≤ N of |Ψ(n) − ψ(n)|, Ψ a list of rationals indexed from n = 2, ψ the Chebyshev function."""
    psi, out = 0.0, 0.0
    for i, n in enumerate(range(2, N + 1)):
        psi += vm_float(n, base(n)); out = max(out, abs(float(Psi[i]) - psi))
    return out


def band_energy(ind, qs, width=3):
    """The additive-transform band energy of the indicator `ind` on Z/p, Parseval-normalised: for each q, the sum of
    |F(k)|² over the bins within `width` of a·p/q, gcd(a, q) = 1, divided by ‖ind‖²."""
    p = len(ind); ones = [m for m in range(p) if ind[m]]
    norm2 = float(len(ones)); out = {}
    for q in qs:
        e = 0.0
        for a in range(1, q):
            if math.gcd(a, q) != 1: continue
            kc = a * p / q
            for k in range(int(math.floor(kc)) - 3, int(math.ceil(kc)) + 4):
                z = sum(cmath.exp(-2j * math.pi * (k % p) * m / p) for m in ones)
                e += abs(z) ** 2
        out[q] = e / norm2
    return out


def fft(a):
    """The discrete Fourier transform F[k] = Σ_m a[m] e^{−2πi km/n}, mixed radix (numpy's convention)."""
    n = len(a)
    if n == 1: return list(a)
    r = next(d for d in range(2, n + 1) if n % d == 0)
    m = n // r
    Y = [fft(a[j::r]) for j in range(r)]
    w = [cmath.exp(-2j * math.pi * k / n) for k in range(n)]
    out = [0j] * n
    for s in range(r):
        for k in range(m):
            idx = k + m * s
            out[idx] = sum(Y[j][k] * w[(j * idx) % n] for j in range(r))
    return out


def mode_correlations(p, dlog, is_prime):
    """|corr(1_Π, χ_j)| for every nontrivial multiplicative-chart mode on F_p^× by FFT over the discrete logarithm
    (`dlog[x]` for x in 1..p−1): (the maximum, the root-mean-square floor 1/√(p−2), the list)."""
    u = [0.0] * (p - 1)
    for x in range(1, p): u[dlog[x]] = 1.0 if is_prime(x) else 0.0
    mean = sum(u) / len(u); u = [t - mean for t in u]
    F = fft(u); nu = math.sqrt(sum(t * t for t in u))
    corr = [abs(F[k]) / (nu * math.sqrt(p - 1)) for k in range(1, p - 1)]
    return max(corr), 1 / math.sqrt(p - 2), corr


def pearson(a, b):
    """The Pearson correlation of two sequences of numbers (rationals in)."""
    a = [float(x) for x in a]; b = [float(x) for x in b]
    ma, mb = sum(a) / len(a), sum(b) / len(b)
    a = [x - ma for x in a]; b = [x - mb for x in b]
    return sum(x * y for x, y in zip(a, b)) / math.sqrt(sum(x * x for x in a) * sum(y * y for y in b))


def ratio(x, y):
    """x / y in floating point (x, y rationals or floats)."""
    return float(x) / float(y)
