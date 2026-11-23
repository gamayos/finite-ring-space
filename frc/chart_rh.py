"""frc.chart_rh — 20-rh's readings in floating point (chart tier; ledger migration, 7 October 2026).

The chart theme holds the readings against the continuum, the only place where floats appear (frc/themes.py, rank 31 since 19 October 2026, the super theme at 30).
This file holds the floating-point computations of 20-rh's validation package (src/20-rh/rh.py) that the ledger file
frc/ledgers/p20_rh.py reproduces. Since the rewrite of the paper (17 October 2026, reports/blueprint-20261017.md) the
ledger file uses the exhibit's energy along the chart's height, the chart's characters and the discrete-logarithm
loading; the earlier readings (the Lanczos matrix, the Riemann–Siegel phase and the horizon-length main sum, Hardy's Z by
Euler–Maclaurin, the resonance's weights, the mode correlations) stay as the chart theme's library and are tested, but
witness no row. This file uses `math` and `cmath` only, so the framework stays free of third-party imports. Each
function returns numbers that the ledger file compares with the package's stated values; the exact parts come from
frc/horizon.py.

    HEIGHTS                          the first eighty zero heights of ζ, imported data of the readings (20:A6): the first thirty from
                                     Odlyzko's tables, the next fifty written from mpmath.zetazero; all eighty equal the file zeros1 of
                                     the tables (the first 100,000 zeros) at its nine decimals
    window_weights(H, kind)          the weighted labels of a window (the primes, or the prime powers with log ℓ) and the mean
    spectrum(H, t0, dt, steps, kind, sigma), maxima(t0, dt, es), peaks(H, count, lo, hi)
                                     the spectrum of a window |Σ (λ(n) − λ̄) n^{σ+it}| (20:D13) and its peaks
    subset_control(H)                the exhibit's protocol on every subset of the labels of a window (20:D14)
    expint(z), label_step(u, T), window_count(H, T, x), riemann_counts(x, heights), emergence_reading()
                                     the count of a window from its dual below a height, and Riemann's formula cut at
                                     the same height (20:D16)
    vector_count(labels, T, x, weights), count_bound(labels, x, weights), bound_reading()
                                     the count of a real vector on a list of labels below a height and the bound on its
                                     difference from the count of the vector below a position (20:D17)
    power_tail(M, H, s)              Σ n^s over M ≤ n ≤ H by the Euler–Maclaurin formula
    characters_parseval(p, g, base)  the chart's characters on ℓ²(F_p^×): orthogonality, Parseval, inversion, the shift
    dlog_loading(p, labels, lam)     the window's labels read in the discrete logarithm: the loadings of the nontrivial modes
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
    92.491899270558484, 94.651344040519886, 95.870634228245309, 98.831194218193692, 101.317851005731392,
    103.725538040478339, 105.446623052326094, 107.168611184276408, 111.029535543169675, 111.874659176992637,
    114.320220915452713, 116.226680320857554, 118.790782865976217, 121.370125002420646, 122.946829293552588,
    124.256818554345767, 127.516683879596495, 129.578704199956051, 131.087688530932657, 133.497737202997586,
    134.756509753373871, 138.116042054533443, 139.736208952121389, 141.123707404021124, 143.111845807620633,
    146.000982486765519, 147.422765342559602, 150.053520420784880, 150.925257612241467, 153.024693811198896,
    156.112909294237868, 157.597591817594060, 158.849988171420499, 161.188964137596028, 163.030709687181987,
    165.537069187900419, 167.184439978174513, 169.094515415568821, 169.911976479411699, 173.411536519591553,
    174.754191523365726, 176.441434297710419, 178.377407776099977, 179.916484020256996, 182.207078484366462,
    184.874467848387509, 185.598783677707471, 187.228922583501852, 189.416158656016937, 192.026656360713787,
    193.079726603845704, 195.265396679529235, 196.876481840958317, 198.015309676251912, 201.264751943703789]


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


# ---- the spectrum of a window [chart] (Obs. exhibit; rows D13, D14, D15), 21 November 2026 -----------------------------
# The labels 1..H carry a weight (1 on the primes, or log l on the prime powers l^a); its mean over the labels is removed;
# the label n is read as n^(sigma + i t). Pure python; the constant part beyond `head` labels is summed by the
# Euler-Maclaurin formula, so the depth 10^6 costs about 4 ms a height.
def window_weights(H, kind="primes"):
    """The labels n <= H with a nonzero weight, their weights, and the mean of the weight over the labels 1..H.
    kind "primes": 1 on the primes; kind "mangoldt": log l on the prime powers l^a (the von Mangoldt weight)."""
    sieve = bytearray([1]) * (H + 1); sieve[0:2] = b"\0\0"
    for i in range(2, math.isqrt(H) + 1):
        if sieve[i]: sieve[i * i::i] = bytearray(len(sieve[i * i::i]))
    labels, weights = [], []
    for l in range(2, H + 1):
        if sieve[l]:
            if kind == "primes":
                labels.append(l); weights.append(1.0)
            else:
                q, w = l, math.log(l)
                while q <= H:
                    labels.append(q); weights.append(w); q *= l
    return labels, weights, sum(weights) / H


def power_tail(M, H, s):
    """The sum of n^s over M <= n <= H by the Euler-Maclaurin formula with three corrections (no zeta is evaluated);
    for |s| <= 60 and M >= 2000 the next correction is below 1e-13 of M^Re(s)."""
    f = lambda x, e: cmath.exp(e * math.log(x))
    out = (f(H, s + 1) - f(M, s + 1)) / (s + 1) + (f(H, s) + f(M, s)) / 2
    out += s / 12 * (f(H, s - 1) - f(M, s - 1))
    out -= s * (s - 1) * (s - 2) / 720 * (f(H, s - 3) - f(M, s - 3))
    out += s * (s - 1) * (s - 2) * (s - 3) * (s - 4) / 30240 * (f(H, s - 5) - f(M, s - 5))
    return out


def spectrum(H, t0, dt, steps, kind="primes", sigma=-0.5, head=2000):
    """E(t) = |sum over n <= H of (weight(n) - mean) n^(sigma + i t)| at t = t0 + j dt, j = 0..steps-1.
    The weighted labels and the first labels of the constant part are summed term by term; beyond `head` labels the
    constant part's sum is the Euler-Maclaurin tail."""
    labels, weights, mean = window_weights(H, kind)
    M = min(H, head)
    ln = [math.log(n) for n in labels]
    z = [w * math.exp(sigma * x) * cmath.exp(1j * t0 * x) for w, x in zip(weights, ln)]
    r = [cmath.exp(1j * dt * x) for x in ln]
    lh = [math.log(n) for n in range(1, M + 1)]
    zh = [math.exp(sigma * x) * cmath.exp(1j * t0 * x) for x in lh]
    rh = [cmath.exp(1j * dt * x) for x in lh]
    out = []
    for j in range(steps):
        const = sum(zh)
        if H > M:
            const += power_tail(M + 1, H, complex(sigma, t0 + j * dt))
        out.append(abs(sum(z) - mean * const))
        z = [a * b for a, b in zip(z, r)]
        zh = [a * b for a, b in zip(zh, rh)]
    return out


def maxima(t0, dt, es):
    """The local maxima of a sampled spectrum, each refined by the parabola through its three samples: (t, height),
    tallest first."""
    out = []
    for i in range(1, len(es) - 1):
        a, b, c = es[i - 1], es[i], es[i + 1]
        if b > a and b >= c:
            d = (a - c) / (2 * (a - 2 * b + c))
            out.append((t0 + (i + d) * dt, b - (a - c) * d / 4))
    return sorted(out, key=lambda p: -p[1])


def peaks(H, count, lo, hi, dt=0.01, kind="primes", sigma=-0.5):
    """The `count` tallest maxima of the window's spectrum on lo <= t <= hi, by height: [(t, height)]."""
    steps = int(round((hi - lo) / dt)) + 1
    return sorted(maxima(lo, dt, spectrum(H, lo, dt, steps, kind, sigma))[:count])


# The exhibit's readings (20:D14, D15): the windows with the bound of their five peaks, and the deep window's exponents.
WINDOWS = ((13, 0.18), (39, 0.21), (173, 0.27), (1551, 0.21))
DEEP_SIGMAS = (-0.5, -0.25, -0.75, 0.0, -1.0)


def window_reading():
    """The reading of 20:D14 on the windows of the laboratory Subjects 173 and 1549 (depth 13 and 39) and of the
    laboratory Carriers 30089 and 2408561 (depth 173 and 1551): the prime vector with its mean removed sums to 0, the
    spectrum is even in the height, and the five tallest peaks on 10 <= t <= 36 lie within the window's bound of the first
    five heights. Returns (ok, detail)."""
    ok, parts = True, []
    for H, bound in WINDOWS:
        labels, weights, mean = window_weights(H)
        free = sum(weights) - mean * H                                   # the weights with their mean removed, summed over the H labels
        up, down = spectrum(H, 14.0, 7.0, 4), spectrum(H, -14.0, -7.0, 4)    # E at 14, 21, 28, 35 and at their negatives
        pk = peaks(H, 5, 10.0, 36.0)
        d = max(abs(t - h) for (t, _), h in zip(pk, HEIGHTS))
        ok &= abs(free) < 1e-9 and all(abs(a - b) < 1e-9 for a, b in zip(up, down)) and d <= bound
        parts.append(f"{H}: {d:.3f}")
    return ok, "largest distances " + ", ".join(parts)


def subset_control(H=13, bound=0.18, nxt=0.26, lo=10.0, hi=36.0, dt=0.01):
    """The control of 20:D14 at depth H: every proper nonempty subset of the labels 1..H read as the support of a vector,
    by the protocol of the exhibit (mean removed, the five tallest maxima on lo <= t <= hi, sorted, against the first five
    heights). A subset and its complement give the same spectrum, so the subsets without the label 1 list each pair once:
    2^(H-1) - 1 pairs. A pair with fewer than five maxima on the range is counted and lies within no bound (13 pairs at
    depth 13). The primes' pair alone lies within `bound`, it is the closest of all, and the next pair is at `nxt` to two
    decimals. Returns (ok, detail)."""
    steps = int(round((hi - lo) / dt)) + 1
    ln = [math.log(n) for n in range(1, H + 1)]
    cols = [[math.exp(-0.5 * x) * cmath.exp(1j * (lo + j * dt) * x) for j in range(steps)] for x in ln]
    total = [sum(c[j] for c in cols) for j in range(steps)]
    primes = set(window_weights(H)[0])
    run, inside, size = [0j] * steps, [False] * (H + 1), 0
    best, second, within, pairs, short, best_set = None, None, 0, 0, 0, None
    for i in range(1, 2 ** (H - 1)):                                     # Gray code over the labels 2..H: one label changes at a step
        n = 2 + ((i & -i).bit_length() - 1)
        col = cols[n - 1]
        if inside[n]:
            run = [a - b for a, b in zip(run, col)]; size -= 1
        else:
            run = [a + b for a, b in zip(run, col)]; size += 1
        inside[n] = not inside[n]
        frac = size / H
        five = sorted(maxima(lo, dt, [abs(a - frac * t) for a, t in zip(run, total)])[:5])
        pairs += 1
        if len(five) < 5:
            short += 1; continue
        d = max(abs(t - h) for (t, _), h in zip(five, HEIGHTS))
        within += d <= bound
        if best is None or d < best:
            best, second, best_set = d, best, {m for m in range(2, H + 1) if inside[m]}
        elif second is None or d < second:
            second = d
    ok = pairs == 2 ** (H - 1) - 1 and within == 1 and best_set == primes and best <= bound < second and abs(second - nxt) <= 0.005
    ok &= short == 13 or H != 13                                             # at depth 13 thirteen pairs have fewer than five maxima on the range
    return ok, f"{pairs} pairs of subsets: {within} within {bound}, the primes' pair at {best:.3f}, the next at {second:.3f}, {short} with fewer than five maxima"


def deep_reading(H=10 ** 6):
    """The evaluation of 20:D15 at depth H with the von Mangoldt weight: at a label n a mode has the modulus n^sigma, the
    spectrum is at most the sum of the moduli, the ten tallest peaks on 10 <= t <= 52 lie within 0.045 of the first ten
    heights. Returns (ok, detail)."""
    labels, weights, mean = window_weights(H, "mangoldt")
    pk = peaks(H, 10, 10.0, 52.0, dt=0.02, kind="mangoldt")
    d = max(abs(t - h) for (t, _), h in zip(pk, HEIGHTS))
    weight = dict(zip(labels, weights))
    cap = sum(abs(weight.get(n, 0.0) - mean) * n ** -0.5 for n in range(1, H + 1))    # the sum of the moduli at sigma = -1/2
    ok = d <= 0.045 and max(h for _, h in pk) <= cap
    ok &= all(abs(abs(n ** complex(s, t)) - n ** s) < 1e-9 * n ** s for n in (2, 13, H) for s in DEEP_SIGMAS for t in (HEIGHTS[0], HEIGHTS[9]))
    return ok, f"largest distance {d:.3f}"


# The emergence of the count (20:D16): the exponential integral, the step of a label, the count of a window from its
# dual, and Riemann's formula cut at a height. The heights with the number of zeros below each and the three bounds:
# the window's count against the count, Riemann's formula against the count, the two against each other.
EULER = 0.5772156649015329                                               # Euler's constant, the constant term of the series of Ei
MOBIUS = (0, 1, -1, -1, 0, -1, 1, -1)                                    # the Moebius function at 0..7: positions below 256
EMERGENCE = ((35.0, 5, 0.38, 0.48, 0.14), (78.0, 20, 0.21, 0.22, 0.10), (202.0, 80, 0.11, 0.15, 0.10))


def expint(z):
    """The exponential integral Ei(z) of a complex z off the negative real axis: gamma + log z + the sum of z^k/(k k!)
    for |z| <= 6 and in the sector |Im z| < Re z, and elsewhere the continued fraction of E1 at -z with
    Ei(z) = -E1(-z) +- i pi, the sign that of Im z. The readings below use it on the positive reals up to 4 and on
    arguments (1/2 + it) u with t >= 14, where it agrees with scipy.special.expi and exp1 and with mpmath.ei to 1e-14."""
    z = complex(z)
    if abs(z) <= 6.0 or abs(z.imag) < z.real:
        out, term = EULER + cmath.log(z), 1.0 + 0j
        for k in range(1, 400):
            term *= z / k
            out += term / k
            if abs(term) < 1e-17 * max(1.0, abs(out)): break
        return out
    w = -z
    b = w + 1.0; c = None; d = 1.0 / b; h = d
    for i in range(1, 400):
        a = -i * i; b += 2.0
        d = 1.0 / (a * d + b); c = b if c is None else b + a / c
        ratio_ = c * d; h *= ratio_
        if abs(ratio_ - 1.0) < 1e-15: break
    return -h * cmath.exp(-w) + (1j * math.pi if z.imag >= 0 else -1j * math.pi)


def label_step(u, T):
    """The step of one label in the count below the height T: (1/2 pi) times the integral over -T <= t <= T of
    e^((1/2 - it) u)/(1/2 - it), with u = log(x/n). It is Im Ei((1/2 + iT) u)/pi, plus 1 for u < 0, and at the label
    itself, u = 0, it is arctan(2T)/pi, the middle of the step."""
    if u == 0: return math.atan(2.0 * T) / math.pi
    return expint(complex(0.5, T) * u).imag / math.pi + (1.0 if u < 0 else 0.0)


def window_count(H, T, x):
    """The count of the window of depth H from its dual below the height T (20:D16), at a position x: (1/2 pi) times
    the integral over -T <= t <= T of w^(t) x^(1/2 - it)/(1/2 - it), with w^(t) the sum of n^(-1/2 + it) over the
    primes n of the window, its Dirichlet polynomial. Label by label it is the sum of the steps."""
    return sum(label_step(math.log(x / n), T) for n in window_weights(H)[0])


def riemann_counts(x, heights):
    """Riemann's formula for the count of the primes up to x, cut at the zeros below each of the heights (20:A6):
    the sum over n of mu(n)/n f(x^(1/n)), with f(y) = li(y) - the sum over the zeros of li(y^rho) - log 2 + the integral
    of 1/(u (u^2 - 1) log u) over u >= y, and li(y^rho) = Ei(rho log y). The terms with x^(1/n) < 2 are left out, as in
    the formula itself."""
    out = [0.0] * len(heights)
    for n in range(1, int(math.log2(x)) + 1):
        if not MOBIUS[n]: continue
        ly = math.log(x) / n
        f = lambda s: 1.0 / (s * math.expm1(2.0 * s))                    # the integral, in s = log u, by Simpson's rule on [ly, ly + 12]
        tail = (f(ly) + f(ly + 12.0) + sum((4 if j % 2 else 2) * f(ly + 0.02 * j) for j in range(1, 600))) * 0.02 / 3
        base = expint(ly).real - math.log(2.0) + tail
        zeros = [0.0] * len(heights)
        for g in HEIGHTS:
            e = expint(complex(0.5, g) * ly).real
            for j, T in enumerate(heights):
                if g < T: zeros[j] += e
        for j in range(len(heights)): out[j] += MOBIUS[n] / n * (base - 2.0 * zeros[j])
    return out


def emergence_reading(H=39):
    """The reading of 20:D16 on the window of the laboratory Subject 1549 (depth 39, twelve primes) at the heights 35,
    78 and 202, which have 5, 20 and 80 zeros of positive height below them. At the half-integers 2.5 to 38.5 the count from the window's
    dual lies within 0.38, 0.21 and 0.11 of the count of the primes, Riemann's formula within 0.48, 0.22 and 0.15, and
    the two within 0.14, 0.10 and 0.10 of each other. At the twelve prime labels each reads the middle of the step, the
    count less one half, within its own bound. The bounds between the two are for the half-integers: at the prime label
    23 and the height 78 the two differ by 0.106. Returns (ok, detail)."""
    primes = window_weights(H)[0]
    xs = [n + 0.5 for n in range(2, H)]
    true = [sum(1 for l in primes if l < x) for x in xs]
    middle = [sum(1 for l in primes if l <= p) - 0.5 for p in primes]
    heights = [e[0] for e in EMERGENCE]
    formula = [riemann_counts(x, heights) for x in xs]
    at_labels = [riemann_counts(float(p), heights) for p in primes]
    ok, parts = len(primes) == 12, []
    for j, (T, zeros, b_window, b_zeros, b_both) in enumerate(EMERGENCE):
        w = [window_count(H, T, x) for x in xs]; r = [row[j] for row in formula]
        dw = max(abs(a - c) for a, c in zip(w, true)); dr = max(abs(a - c) for a, c in zip(r, true)); db = max(abs(a - b) for a, b in zip(w, r))
        lw = max(abs(window_count(H, T, p) - m) for p, m in zip(primes, middle)); lr = max(abs(row[j] - m) for row, m in zip(at_labels, middle))
        ok &= sum(1 for g in HEIGHTS if g < T) == zeros and dw <= b_window and dr <= b_zeros and db <= b_both and lw <= b_window and lr <= b_zeros
        parts.append(f"{T:.0f}: {dw:.3f}, {dr:.3f}, {db:.3f} ({lw:.3f}, {lr:.3f})")
    gap = abs(window_count(H, 78.0, 23.0) - at_labels[primes.index(23)][heights.index(78.0)])
    ok &= abs(gap - 0.106) < 0.0005 and gap > EMERGENCE[1][4]                # above the bound 0.10 that holds between the two at the half-integers
    return ok, ("largest differences (the window's count, Riemann's formula, between the two; in brackets the first two at the prime labels, "
                "from the count less one half) at the heights " + "; ".join(parts) + f"; at the label 23 and the height 78 the two differ by {gap:.3f}")


# The bound of the count (20:D17): the count of a real vector on a list of labels below a height, and the bound
# B(x)/T on its difference from the count of the vector below a position x that is no label.
def vector_count(labels, T, x, weights=None):
    """The count below the height T of a real vector on a list of labels, at a position x: the sum over the labels of
    the weight times the step of the label. Without weights the vector is the indicator of the labels."""
    weights = weights or [1.0] * len(labels)
    return sum(w * label_step(math.log(x / n), T) for n, w in zip(labels, weights))


def count_bound(labels, x, weights=None):
    """B(x) of 20:D17 for a real vector on a list of labels, at a position x that is no label: (1/pi) times the sum
    over the labels of |w(n)| sqrt(x/n)/|log(x/n)|. The count below the height T lies within B(x)/T of the count of the
    vector below x (the theorem FRC.Chart.Perron.count_bound, on Mathlib)."""
    weights = weights or [1.0] * len(labels)
    return sum(abs(w) * math.sqrt(x / n) / abs(math.log(x / n)) for n, w in zip(labels, weights)) / math.pi


def bound_reading(H=39):
    """The reading of 20:D17. On the windows of depth 13 and H, at the half-integers and the heights 35, 67, 78 and
    202, for the prime vector and for the indicator vector of all the labels, the count lies within B(x)/T of the count
    of the vector below x; so it does for a signed vector on the labels of depth H at the quarter positions. For
    H = 39 the prime vector has B(x) <= 33.14 at the half-integers 2.5 to 38.5: the bound is at most
    0.95, 0.43 and 0.17 at the heights 35, 78 and 202 and below one half from the height 67 on, and the nearest integer
    to the count at the height 67 is the count of the primes. Returns (ok, detail)."""
    ok, worst = True, 0.0
    heights = (35.0, 67.0, 78.0, 202.0)
    for depth in (13, H):
        xs = [n + 0.5 for n in range(2, depth)]
        for labels in (window_weights(depth)[0], list(range(1, depth + 1))):
            for T in heights:
                for x in xs:
                    ratio = abs(vector_count(labels, T, x) - sum(1 for n in labels if n < x)) * T / count_bound(labels, x)
                    worst = max(worst, ratio); ok &= ratio <= 1.0
    labels = list(range(1, H + 1)); signed = [(-1.0) ** n * (1 + n % 3) / 2 for n in labels]
    for T in heights:
        for x in [n + 0.25 for n in range(0, H + 1)]:
            below = sum(w for n, w in zip(labels, signed) if n < x)
            ratio = abs(vector_count(labels, T, x, signed) - below) * T / count_bound(labels, x, signed)
            worst = max(worst, ratio); ok &= ratio <= 1.0
    primes = window_weights(H)[0]; xs = [n + 0.5 for n in range(2, H)]
    top = max(count_bound(primes, x) for x in xs)
    ok &= top <= 33.14 and 33.14 / 67.0 < 0.5
    ok &= all(math.ceil(100 * 33.14 / T) / 100 == b for T, b in ((35.0, 0.95), (78.0, 0.43), (202.0, 0.17)))
    ok &= all(round(vector_count(primes, 67.0, x)) == sum(1 for n in primes if n < x) for x in xs)
    return ok, f"largest B(x) at the half-integers of depth {H}: {top:.3f}; largest ratio of a difference to its bound: {worst:.3f}"


def characters_parseval(p, g, base):
    """The chart's characters χ_j(n) = ω^{jλ(n)} on ℓ²(F_p^×) (λ the discrete log to g, ω = e^{2πi/(p−1)}) against v = Λ:
    (orthogonal with ‖χ_j‖² = p−1, Σ_j |v̂(j)|² = (p−1)Σ|v|², the dual inverts, S χ_j = ω^j χ_j, Σ|v̂|²/(p−1)); tolerance 10⁻⁹."""
    n = p - 1
    v = [vm_float(m, base(m)) for m in range(1, p)]
    dlog = {}
    x = 1
    for m in range(n):
        dlog[x] = m; x = x * g % p
    w = cmath.exp(2j * math.pi / n)
    chi = [[w ** (j * dlog[m]) for m in range(1, p)] for j in range(n)]
    vc = [sum(chi[j][i] * v[i] for i in range(n)) for j in range(n)]
    ok_orth = all(abs(sum(chi[j][i].conjugate() * chi[k][i] for i in range(n)) - (n if j == k else 0)) < 1e-9
                  for j in range(n) for k in range(n))
    par = sum(abs(c) ** 2 for c in vc)
    ok_par = abs(par - n * sum(t * t for t in v)) < 1e-9
    ok_inv = all(abs(sum(chi[j][i].conjugate() * vc[j] for j in range(n)).real / n - v[i]) < 1e-10 for i in range(n))
    ok_c = all(abs(w ** (j * dlog[g * m % p]) - w ** j * chi[j][m - 1]) < 1e-10 for j in range(n) for m in range(1, p))
    return ok_orth, ok_par, ok_inv, ok_c, par / n


def dlog_loading(p, labels, lam):
    """The window's labels read in the discrete logarithm λ: the loadings |Σ_{n} e^{2πi k λ(n)/(p−1)}|² of the nontrivial modes
    k = 1..p−2, as (max, mean, |labels| log(p−1))."""
    n = p - 1
    ph = [lam[x] for x in labels]
    loads = []
    for k in range(1, n):
        loads.append(abs(sum(cmath.exp(2j * math.pi * k * l / n) for l in ph)) ** 2)
    return max(loads), sum(loads) / len(loads), len(labels) * math.log(n)
