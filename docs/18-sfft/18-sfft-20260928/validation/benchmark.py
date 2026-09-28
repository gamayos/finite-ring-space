"""
NumPy timing of the streaming algorithms against the direct per-index baseline
(Table 2 of the paper). Correctness is asserted on every run. Timings are
machine-specific; the machine is printed. Integer arithmetic throughout.

Direct: build F^{[s]} as a matrix from the projectors for each s, then multiply.
Algorithm A: scalar coefficients, three general multiplications per element-step.
Algorithm B: contribution arrays multiplied elementwise by 2^{-l} with NumPy `%`
             (NumPy has no shift-and-reduce primitive; the compiled benchmark in
             bench/stream.c measures the shift form).
"""
import numpy as np, time, platform, sys, statistics

def is_prime(m):
    if m < 2: return False
    d = 2
    while d * d <= m:
        if m % d == 0: return False
        d += 1
    return True

def order(a, p):
    n = p - 1; o = n; m = n; q = 2; fs = []
    while q * q <= m:
        if m % q == 0:
            fs.append(q)
            while m % q == 0: m //= q
        q += 1
    if m > 1: fs.append(m)
    for q in fs:
        while o % q == 0 and pow(a, o // q, p) == 1: o //= q
    return o

def setup(p, g):
    n = p - 1; k = n // 4; i = pow(g, -k, p)
    jj, kk = np.meshgrid(np.arange(n), np.arange(n))
    W = np.array([[pow(g, (a * b) % n, p) for b in range(n)] for a in range(n)], dtype=np.int64)
    F = (i * W) % p
    inv4 = pow(4, -1, p); ii = pow(i, -1, p)
    Fr = [np.eye(n, dtype=np.int64)]
    for r in range(1, 4): Fr.append((Fr[-1] @ F) % p)
    Pis = []
    for l in range(4):
        Pi = np.zeros((n, n), dtype=np.int64)
        for r in range(4): Pi = (Pi + pow(ii, l * r, p) * Fr[r]) % p
        Pis.append((inv4 * Pi) % p)
    return Pis, n

def direct(v, Pis, p, n, g):
    out = []
    for s in range(n):
        Fs = np.zeros((n, n), dtype=np.int64)
        for l in range(4): Fs = (Fs + pow(g, (-l * s) % n, p) * Pis[l]) % p
        out.append((Fs @ v) % p)
    return out

def alg_A(v, Pis, p, n, g):
    u = [(Pis[l] @ v) % p for l in range(4)]
    c = [1, 1, 1]; mu = [pow(g, -l, p) for l in (1, 2, 3)]
    out = []
    for s in range(n):
        out.append((u[0] + c[0] * u[1] + c[1] * u[2] + c[2] * u[3]) % p)
        c = [(c[l] * mu[l]) % p for l in range(3)]
    return out

def alg_B(v, Pis, p, n, g):
    u = [(Pis[l] @ v) % p for l in range(4)]
    a1, a2, a3 = u[1].copy(), u[2].copy(), u[3].copy()
    h1, h2, h3 = (pow(g, -l, p) for l in (1, 2, 3))
    out = []
    for s in range(n):
        out.append((u[0] + a1 + a2 + a3) % p)
        a1 = (h1 * a1) % p; a2 = (h2 * a2) % p; a3 = (h3 * a3) % p
    return out

def time_it(f, reps):
    ts = []
    for _ in range(reps):
        t0 = time.perf_counter(); f(); ts.append(time.perf_counter() - t0)
    return statistics.mean(ts), statistics.median(ts)

if __name__ == "__main__":
    REPS = 30
    print(f"machine: {platform.machine()} {platform.system()} {platform.release()}; python {platform.python_version()}; numpy {np.__version__}; reps {REPS}")
    print(f"{'p':>5} {'n':>5} | {'direct mean':>11} {'median':>8} | {'A mean':>9} {'median':>8} | {'B mean':>9} {'median':>8} | {'dir/A':>6} {'dir/B':>6} {'A/B':>5}")
    cls = [p for p in range(5, 200) if is_prime(p) and p % 4 == 1 and order(2, p) == p - 1]
    for p in cls:
        Pis, n = setup(p, 2)
        v = np.random.default_rng(42).integers(0, p, n).astype(np.int64)
        od = direct(v, Pis, p, n, 2); oa = alg_A(v, Pis, p, n, 2); ob = alg_B(v, Pis, p, n, 2)
        assert all(np.array_equal(od[s], oa[s]) and np.array_equal(od[s], ob[s]) for s in range(n)), p
        md, dd = time_it(lambda: direct(v, Pis, p, n, 2), REPS)
        ma, da = time_it(lambda: alg_A(v, Pis, p, n, 2), REPS)
        mb, db = time_it(lambda: alg_B(v, Pis, p, n, 2), REPS)
        print(f"{p:>5} {n:>5} | {md:11.5f} {dd:8.5f} | {ma:9.5f} {da:8.5f} | {mb:9.5f} {db:8.5f} | {md/ma:6.1f} {md/mb:6.1f} {ma/mb:5.2f}  correct")
    for p, g in ((41, 6), (157, 5)):
        Pis, n = setup(p, g)
        v = np.random.default_rng(1).integers(0, p, n).astype(np.int64)
        od = direct(v, Pis, p, n, g); oa = alg_A(v, Pis, p, n, g)
        assert all(np.array_equal(od[s], oa[s]) for s in range(n))
        print(f"Algorithm A correct at p={p}, g={g} (2 not primitive, ord(2)={order(2,p)})")
