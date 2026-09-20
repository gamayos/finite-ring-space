"""
rhcommon.py — shared primitives for the 20-rh validation package
=================================================================
"Riemann Hypothesis over Finite Holographic Substrate" (Akhtman & Voether, 2026),
validation package of the FRC corpus (finite-ring-space/src/20-rh). Each check names the row(s) of the paper's predicate
ledger it witnesses (LEDGER below; rows cited as 20:XN), and the ledger's source column cites the check ids.

Everything the block scripts share:
  * the von Mangoldt comb Λ(n) (sieved) and its raised-cosine taper in log n;
  * the archimedean scale-phase θ(T) from log Γ (never from ζ);
  * the raw comb count  Ñ_N(T) = θ(T)/π + 1 + S_comb(T)  (Proposition turing; Obs. trace) and the pole-corrected
    count  N̂_N(T) = Ñ_N(T) − (1/π) Im[Π_N(½+iT) + log((s−1)/s)]  (Proposition combformula), Π_N the explicit
    pole term of the smoothed explicit formula — the raw count carries it and has no limit in N, the corrected
    count settles;
  * the secular roots (half-integer crossings of N̂_N, or of Ñ_N for the raw reading), the colleague matrix
    and the comb-built Jacobi matrix (Obs. matrix, Def. jacobi);
  * the first Riemann heights, used only as validation markers — never as inputs;
  * the PASS/FAIL registry that every block reports into (results.json).

Kinds (notation.tex convention 6): EXACT checks are integer-pinned; [approx] checks
compare a floating-point observation with the value the paper states, to a stated
tolerance; [chart] marks a continuum reading of a finite object.
"""
import os, json, math, time
import numpy as np
from scipy.special import loggamma
from scipy.optimize import brentq

FAST = os.environ.get("RH_FAST", "0") == "1"      # reduced depths for a quick run
FIGDIR = os.environ.get("RH_FIGDIR", "figures")
os.makedirs(FIGDIR, exist_ok=True)

# ----------------------------------------------------------------------------- registry
RESULTS = []

# The paper's predicate ledger (20-rh Appendix A, rows cited as 20:XN): the row(s) each
# check witnesses. The ledger's source column cites these check ids in return.
LEDGER = {
    "A1": "20:B4", "A2": "20:B5", "A3": "20:B6", "A4": "20:B8", "A5": "20:B9", "A6": "20:B10", "A6b": "20:B10", "A7": "20:E1, 20:E12, 20:E13",
    "A7b": "20:E1, 20:E12, 20:E13", "A8": "20:E9", "A9": "20:B7", "A10": "20:B1", "A11": "20:B2",
    "B1": "20:D2", "B2": "20:D3", "B3": "20:B8", "B4": "20:D4",
    "C1": "20:E5", "C2": "20:E6", "C2b": "20:E6, 20:E8", "C2c": "20:E6", "C3": "20:E8", "C4": "20:E9", "C5": "20:E10", "C6": "20:E11", "C6b": "20:E3",
    "C7a": "20:E14, 20:E15", "C7b": "20:E15", "C7c": "20:E14, 20:E16",
    "D1": "20:F1", "D2a": "20:F3", "D2b": "20:F3", "D2c": "20:F4", "D2d": "20:F4", "D2e": "20:F5",
    "D2f": "20:F5, 20:F8", "D2g": "20:F4, 20:F8", "D3": "20:F8", "D4": "20:F1",
    "E1a": "20:C2", "E1b": "20:C2", "E1c": "20:C3", "E2a": "20:B11", "E2b": "20:B11", "E3": "20:C4", "E4": "20:C6",
}

def check(pid, label, ok, detail="", kind="EXACT"):
    """Record one predicate check. pid = package check id (A1, C3, ...); LEDGER[pid] = the paper's ledger row(s)."""
    ok = bool(ok)
    rows = LEDGER.get(pid, "")
    import sys as _sys
    script = _sys._getframe(1).f_globals.get("__name__", "")
    if script == "__main__":
        script = os.path.splitext(os.path.basename(_sys.argv[0]))[0]
    RESULTS.append({"id": pid, "rows": rows, "script": script, "label": label, "ok": ok, "detail": detail, "kind": kind})
    print(f"  [{'PASS' if ok else 'FAIL'}] {pid:4s} {kind:7s} [{rows}] {label}" + (f"  --  {detail}" if detail else ""))
    return ok

def summary(write=True):
    n_ok = sum(r["ok"] for r in RESULTS)
    print(f"\nSUMMARY: {n_ok}/{len(RESULTS)} checks passed" + ("" if n_ok == len(RESULTS) else "  <-- FAILURES"))
    if write:
        with open("results.json", "w") as f:
            json.dump(RESULTS, f, indent=1)
    return n_ok == len(RESULTS)

# ----------------------------------------------------------------------------- primes / comb
def sieve_primes(N):
    s = np.ones(N + 1, dtype=bool); s[:2] = False
    for i in range(2, int(N ** 0.5) + 1):
        if s[i]:
            s[i * i::i] = False
    return np.nonzero(s)[0]

def von_mangoldt_support(N):
    """Prime powers n = p^k <= N with Λ(n) = log p. Returns (n, Λ(n)) as float arrays, sorted."""
    primes = sieve_primes(N)
    ns, lam = [primes.astype(np.float64)], [np.log(primes)]
    k = 2
    while True:
        pk = primes[primes <= N ** (1.0 / k)].astype(np.float64) ** k
        if len(pk) == 0:
            break
        ns.append(pk); lam.append(np.log(pk ** (1.0 / k))); k += 1
    n_all = np.concatenate(ns); lam_all = np.concatenate(lam)
    order = np.argsort(n_all)
    return n_all[order], lam_all[order]

class Comb:
    """The tapered von Mangoldt comb to depth N.

    S_comb(T) = -(1/π) Σ_{n<=N} Λ(n)/(√n log n) · w(n) · sin(T log n),
    w(n) = ½(1 + cos(π log n / log N))   — the raised-cosine (Cesàro) taper of Obs. primespec.
    """
    def __init__(self, N, lam_fn=None):
        self.N = int(N)
        if lam_fn is None:
            n, lam = von_mangoldt_support(self.N)
        else:                                   # a generalized comb (Davenport–Heilbronn)
            n, lam = lam_fn(self.N)
        self.n, self.lam = n, lam
        self.logn = np.log(n)
        self.w = 0.5 * (1.0 + np.cos(np.pi * self.logn / math.log(self.N)))
        self.amp = self.lam / (np.sqrt(n) * self.logn) * self.w

    NBLK = 1 << 18      # comb terms per block (memory: NBLK × 64 doubles ≈ 128 MB at most)

    def S(self, T):
        """S_comb at scalar or array T, chunked over T and over the comb (a scalar in gives a float out)."""
        T = np.atleast_1d(np.asarray(T, dtype=float))
        out = np.zeros(len(T))
        for s in range(0, len(T), 64):
            blk = T[s:s + 64]
            for a in range(0, len(self.logn), self.NBLK):
                out[s:s + 64] -= (self.amp[a:a + self.NBLK, None] * np.sin(np.outer(self.logn[a:a + self.NBLK], blk))).sum(0)
        out /= math.pi
        return out if out.size > 1 else float(out[0])

    def sigma(self, gamma):
        """|Σ_N(γ)| = |Σ Λ(n) n^{-1/2-iγ} w(n)|, the scale-spectrum of Obs. primespec (scalar in, float out)."""
        gamma = np.atleast_1d(np.asarray(gamma, float))
        coef = self.lam * self.w / np.sqrt(self.n)
        out = np.empty(len(gamma))
        for s in range(0, len(gamma), 64):
            blk = gamma[s:s + 64]
            acc = np.zeros(len(blk), dtype=complex)
            for a in range(0, len(self.logn), self.NBLK):
                acc += (coef[a:a + self.NBLK, None] * np.exp(-1j * np.outer(self.logn[a:a + self.NBLK], blk))).sum(0)
            out[s:s + 64] = np.abs(acc)
        return out if out.size > 1 else float(out[0])

def theta(T):
    """Riemann–Siegel θ(T) = Im log Γ(¼ + iT/2) − (T/2) log π  — the archimedean phase, from Γ only."""
    T = np.asarray(T, dtype=float)
    return np.imag(loggamma(0.25 + 0.5j * T)) - 0.5 * T * math.log(math.pi)

def count_raw(comb, T, const=1.0, theta_fn=theta):
    """Ñ_N(T) = θ(T)/π + const + S_comb(T): the raw comb count (Proposition turing; uncertified)."""
    T = np.atleast_1d(np.asarray(T, float))
    val = theta_fn(T) / math.pi + const + comb.S(T)
    return val if val.size > 1 else float(val[0])

# ----------------------------------------------------------------------------- the pole term (Prop. combformula)
def pole_term(N, T):
    """Π_N(½ + iT) = ∫_0^L W(u/L) (e^{(½−iT)u} − e^{−(½+iT)u}) du/u,  L = log N  — the pole term of the smoothed
    explicit formula for the tapered log-ζ series, Σ_{n≤N} Λ(n) W(log n/L) n^{−s}/log n = Π_N(s) + J_N(s) (Prop.
    combformula (i), under the hypothesis of no zero to the right of the line), with J_N(s) → log((s−1)ζ(s)/s) for
    s not a zero (Prop. combformula (iv)). Written as ∫_0^L g(u) e^{−iTu} du, g(u) = W(u/L)·2 sinh(u/2)/u, and integrated with
    QUADPACK's oscillatory weights. Returns the complex value. Its size is (π²/2) √N/(|½−iT| L)³ (1 + O(1/L)):
    the raw count carries it and has no limit as N → ∞."""
    from scipy.integrate import quad
    L = math.log(N)
    g = lambda u: (0.5 * (1.0 + math.cos(math.pi * u / L))) * (2.0 * math.sinh(0.5 * u) / u if u > 1e-12 else 1.0)
    re = quad(g, 0.0, L, weight="cos", wvar=T, limit=1000)[0]
    im = -quad(g, 0.0, L, weight="sin", wvar=T, limit=1000)[0]
    return complex(re, im)

def pole_count_term(N, T):
    """(1/π) Im[Π_N(½+iT) + log((s−1)/s)] — the term the raw count carries beyond the exact count (Prop. combformula);
    Im log((s−1)/s) = π − 2 arctan(2T)."""
    return pole_term(N, T).imag / math.pi + 1.0 - (2.0 / math.pi) * math.atan(2.0 * T)

_POLE_CACHE = {}
def count_corrected(comb, T):
    """N̂_N(T) = Ñ_N(T) − (1/π) Im[Π_N + log((s−1)/s)]: the pole-corrected comb count (Prop. combformula; Obs. trace).
    For ζ only (const = 1, the archimedean phase θ); a Dirichlet L-function has no pole and no correction."""
    T = np.atleast_1d(np.asarray(T, float))
    corr = np.array([_POLE_CACHE.setdefault((comb.N, float(t)), pole_count_term(comb.N, float(t))) for t in T])
    val = count_raw(comb, T) - corr
    return val if val.size > 1 else float(val[0])

def secular_roots(comb, windows, const=1.0, theta_fn=theta, corrected=False):
    """The secular roots: solutions of N̂_N(T) = n − ½ (corrected=True) or Ñ_N(T) = n − ½ (raw) in each (n, lo, hi)
    window (Obs. trace)."""
    roots = []
    for n, lo, hi in windows:
        if corrected:
            f = lambda T: count_corrected(comb, T) - (n - 0.5)
        else:
            f = lambda T: count_raw(comb, T, const, theta_fn) - (n - 0.5)
        roots.append(brentq(f, lo, hi, xtol=1e-12))
    return np.array(roots)

def crossings(count_fn, lo, hi, step=0.1):
    """Brackets of every half-integer crossing of a count on [lo, hi], from the count alone: (level, a, b, direction).
    No reference height enters; the heights are compared only afterwards."""
    ts = np.arange(lo, hi + 1e-9, step); v = np.asarray(count_fn(ts), float)
    out = []
    for i in range(len(ts) - 1):
        for h in np.arange(math.floor(min(v[i], v[i + 1])) + 0.5, max(v[i], v[i + 1]), 1.0):
            if (v[i] - h) * (v[i + 1] - h) < 0:
                out.append((float(h), float(ts[i]), float(ts[i + 1]), int(np.sign(v[i + 1] - v[i]))))
    return out

def secular_roots_scan(comb, lo, hi, const=1.0, theta_fn=theta, corrected=False, step=0.1):
    """The secular roots on [lo, hi] with brackets from the count itself (Obs. trace): every upward half-integer
    crossing refined by Brent's method. Returns (roots, levels, extra) — extra lists any downward or repeated crossing."""
    f = (lambda T: count_corrected(comb, T)) if corrected else (lambda T: count_raw(comb, T, const, theta_fn))
    cr = crossings(f, lo, hi, step)
    up = [(h, a, b) for h, a, b, d in cr if d > 0]
    levels = [h for h, _, _ in up]
    extra = [(h, a) for h, a, b, d in cr if d < 0] + [(h, a) for h, a, b in up if levels.count(h) > 1]
    roots = np.array([brentq(lambda T: float(np.atleast_1d(f(T))[0]) - h, a, b, xtol=1e-12) for h, a, b in up])
    return roots, levels, extra

# ----------------------------------------------------------------------------- matrices
def colleague_roots(comb, TA, TB, deg, corrected=False):
    """Eigenvalues of the colleague matrix of the Chebyshev fit of the secular determinant Ξ(T) = cos(π N̂_N(T))
    (corrected=True; Obs. matrix) or cos(π Ñ_N(T)) (raw) on [TA, TB]. Returns the real roots inside the window."""
    from numpy.polynomial import chebyshev as Ch
    xs = np.cos(np.pi * (np.arange(deg + 1) + 0.5) / (deg + 1))
    T = 0.5 * (TB + TA) + 0.5 * (TB - TA) * xs
    cnt = count_corrected(comb, T) if corrected else count_raw(comb, T)
    c = Ch.chebfit(xs, np.cos(math.pi * cnt), deg)
    n = len(c) - 1
    a = c[:-1] / c[-1]
    M = np.zeros((n, n)); M[0, 1] = 1.0
    for k in range(1, n - 1):
        M[k, k - 1] = 0.5; M[k, k + 1] = 0.5
    M[n - 1, n - 2] = 0.5
    M[-1, :] -= 0.5 * a
    ev = np.linalg.eigvals(M)
    ev = ev[np.abs(ev.imag) < 1e-5].real
    ev = ev[(ev > -1) & (ev < 1)]
    return np.sort(0.5 * (TB + TA) + 0.5 * (TB - TA) * ev)

def jacobi_from_points(x):
    """Real-symmetric tridiagonal Jacobi matrix of the unit-weight measure Σ δ_{x_i} (Stieltjes–Lanczos,
    full reorthogonalisation). Its eigenvalues are exactly the x_i (Def. jacobi)."""
    x = np.asarray(x, float); K = len(x)
    A = np.diag(x); V = np.zeros((K, K))
    v = np.ones(K) / math.sqrt(K); V[:, 0] = v
    alpha = np.zeros(K); beta = np.zeros(max(K - 1, 0))
    r = A @ v; alpha[0] = v @ r; r = r - alpha[0] * v
    for j in range(1, K):
        beta[j - 1] = np.linalg.norm(r)
        vj = r / beta[j - 1]
        for k in range(j):
            vj -= (V[:, k] @ vj) * V[:, k]
        vj /= np.linalg.norm(vj); V[:, j] = vj
        r = A @ vj; alpha[j] = vj @ r
        r = r - alpha[j] * vj - beta[j - 1] * V[:, j - 1]
    return np.diag(alpha) + np.diag(beta, 1) + np.diag(beta, -1)

# ----------------------------------------------------------------------------- validation markers
# The first thirty nontrivial zero heights of ζ (Odlyzko's tables). Validation markers only:
# no construction in this package takes them as input.
HEIGHTS = np.array([
    14.134725141734693, 21.022039638771555, 25.010857580145688, 30.424876125859513, 32.935061587739189,
    37.586178158825671, 40.918719012147495, 43.327073280914999, 48.005150881167159, 49.773832477672302,
    52.970321477714460, 56.446247697063394, 59.347044002602353, 60.831778524609809, 65.112544048081606,
    67.079810529494173, 69.546401711173979, 72.067157674481907, 75.704690699083933, 77.144840068874805,
    79.337375020249367, 82.910380854086030, 84.735492980517050, 87.425274613125229, 88.809111207634465,
    92.491899270558484, 94.651344040519886, 95.870634228245309, 98.831194218193692, 101.317851005731392])

def riemann_zeros(n, dps=18):
    """The first n zero heights γ_k of ζ from mpmath's zetazero, cached on disk. Validation markers only."""
    path = os.path.join(FIGDIR, f".zeros_{n}.npy")
    if os.path.exists(path):
        return np.load(path)
    import mpmath as mp
    with mp.workdps(dps):
        g = np.array([float(mp.im(mp.zetazero(k))) for k in range(1, n + 1)])
    np.save(path, g)
    return g

def nearest_errors(roots, heights):
    rec = np.array([roots[np.argmin(np.abs(roots - g))] for g in heights])
    return np.abs(rec - heights)

class Timer:
    def __init__(self, name): self.name = name
    def __enter__(self): self.t = time.time(); return self
    def __exit__(self, *a): print(f"    ({self.name}: {time.time() - self.t:.1f} s)")
