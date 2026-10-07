"""frc.chart_fourier — 6-fourier's observer readout in floating point (chart tier; ledger migration, task LM36, 7 October 2026).

The chart theme holds the readings against the continuum, the only place where floats appear (frc/themes.py, rank 30).
This file holds the floating-point side of 6-fourier's validation package (src/6-fourier/fourier.py, block E): the
readout of the fractional family on ℂ^n through the observer's chart X ↦ ζ_n^u, Y ↦ +√n (the canonical DFT projectors
with the eigenvalue refinement g^{−ℓs} ↦ ζ_n^{−ℓs}), the Shannon entropy of a Born vector, and the entropy checks of the
paper's Section 9. The package used numpy. This file uses `math`, `cmath` and `random` only; its random states come from
`random.Random`, so the sampled states differ from numpy's while the bounds they test are the same.

    Readout(n, u)                    D, the projectors P_ℓ, F^[s] (a matrix) and F^[s] δ_j (a column)
    entropy(vec)                     −Σ q log q over the Born vector q = |vec|²/‖vec‖²
    gauss_square(n)                  |(Σ_k ζ^{k²})² − 2n i|
    cardinal, mub, comb, closed_form, normalised, input_dependence, twist, uncertainty
                                     the checks E2–E8, each (ok, numbers)
"""
import cmath
import math
import random


def _mm(A, B):
    Bt = list(zip(*B))
    return [[sum(a * b for a, b in zip(r, c)) for c in Bt] for r in A]


class Readout:
    """The readout family on ℂ^n under the chart X ↦ ζ_n^u: D = (ζ^{jk})/√n, Π_ℓ = ¼ Σ_r ι^{−ℓr} D^r with ι = ζ^{−κ},
    and F^[s] = Σ_ℓ ζ^{−uℓs} Π_ℓ, ζ = e^{2πiu/n}."""
    def __init__(self, n, u=1):
        self.n, self.k = n, n // 4
        self.z = cmath.exp(2j * math.pi * u / n)
        r = math.sqrt(n)
        self.D = [[self.z ** (j * k) / r for k in range(n)] for j in range(n)]
        iota = self.z ** (-self.k)
        Ds = [[[1.0 + 0j if a == b else 0j for b in range(n)] for a in range(n)]]
        for _ in range(3): Ds.append(_mm(Ds[-1], self.D))
        self.Ds = Ds
        self.P = [[[sum(iota ** (-l * rr) * Ds[rr][a][b] for rr in range(4)) / 4 for b in range(n)] for a in range(n)] for l in range(4)]
        self._w = {}

    def weights(self, s):
        if s not in self._w: self._w[s] = [self.z ** (-l * s) for l in range(4)]
        return self._w[s]

    def matrix(self, s):
        w = self.weights(s)
        return [[sum(w[l] * self.P[l][a][b] for l in range(4)) for b in range(self.n)] for a in range(self.n)]

    def column(self, s, j):
        """F^[s] δ_j."""
        w = self.weights(s)
        return [sum(w[l] * self.P[l][a][j] for l in range(4)) for a in range(self.n)]


def entropy(vec):
    q = [abs(x) ** 2 for x in vec]; t = sum(q)
    return -sum(x / t * math.log(x / t) for x in q if x / t > 1e-15) + 0.0


def apply_h(M, v):
    """M^† v."""
    n = len(M)
    return [sum(M[a][b].conjugate() * v[a] for a in range(n)) for b in range(n)]


def random_state(n, rng):
    v = [complex(rng.gauss(0, 1), rng.gauss(0, 1)) for _ in range(n)]
    r = math.sqrt(sum(abs(x) ** 2 for x in v))
    return [x / r for x in v]


def close(a, b, tol=1e-9):
    return all(abs(x - y) <= tol + 1e-5 * abs(y) for x, y in zip(a, b))       # numpy's allclose (rtol 1e-5, atol tol)


def gauss_square(n):
    z = cmath.exp(2j * math.pi / n)
    return abs(sum(z ** (k * k) for k in range(n)) ** 2 - 2 * n * 1j)


def cardinal(n):
    """E2: H(0) = H(2κ) = 0 and H(κ) = H(3κ) = log n on every δ_j; F^[0] = I, F^[κ] = D, F^[2κ] = D²."""
    R = Readout(n); k = n // 4; ok = True
    for j in range(n):
        ok = ok and abs(entropy(R.column(0, j))) < 1e-9 and abs(entropy(R.column(2 * k, j))) < 1e-9
        ok = ok and abs(entropy(R.column(k, j)) - math.log(n)) < 1e-9 and abs(entropy(R.column(3 * k, j)) - math.log(n)) < 1e-9
    flat = lambda M: [x for row in M for x in row]
    ok = ok and close(flat(R.matrix(0)), flat(R.Ds[0])) and close(flat(R.matrix(k)), flat(R.D)) and close(flat(R.matrix(2 * k)), flat(R.Ds[2]))
    return ok


def mub(n, rng, states=200):
    """E3: B_κ mutually unbiased to B_0; Maassen–Uffink on random states; δ_0 saturates."""
    R = Readout(n); k = n // 4; Bk = R.matrix(k); ok = True
    ok = ok and all(abs(abs(x) ** 2 - 1 / n) <= 1e-8 + 1e-5 / n for row in Bk for x in row)
    for _ in range(states):
        psi = random_state(n, rng)
        ok = ok and entropy(psi) + entropy(apply_h(Bk, psi)) >= math.log(n) - 1e-9
    e = [1.0 if a == 0 else 0.0 for a in range(n)]
    return ok and abs(entropy(e) + entropy(apply_h(Bk, e)) - math.log(n)) < 1e-9


def comb():
    """E3: the comb (δ_0 + δ_6)/√2 at n = 12: (H_0, H_κ)."""
    R = Readout(12); c = [0j] * 12; c[0] = c[6] = 1 / math.sqrt(2)
    h0, hk = entropy(c), entropy(apply_h(R.matrix(3), c))
    ok = abs(h0 - math.log(2)) < 1e-9 and abs(hk - math.log(6)) < 1e-9 and abs(h0 + hk - math.log(12)) < 1e-9
    return ok, h0, hk


def closed_form(n):
    """E4: the two-valued readout of F^[s] δ_0 and its entropy H(s): (ok, the curve H)."""
    R = Readout(n); k = n // 4; z = cmath.exp(2j * math.pi / n); ok = True; H = []
    for s in range(n):
        psi = R.column(s, 0); q = [abs(x) ** 2 for x in psi]
        ts = ((2 - z ** (2 * s) - z ** (-2 * s)) / 4).real
        ok = ok and abs(ts - math.sin(math.pi * s / (2 * k)) ** 2) < 1e-12
        ok = ok and abs(q[0] - (1 - (n - 1) * ts / n)) < 1e-9 and close(q[1:], [ts / n] * (n - 1))
        H.append(entropy(psi))
        if 1e-15 < ts:
            p0 = 1 - (n - 1) * ts / n
            Hcf = -(p0 * math.log(p0) + (n - 1) * (ts / n) * math.log(ts / n))
        else:
            Hcf = 0.0
        ok = ok and abs(Hcf - H[-1]) < 1e-9
    ok = ok and all(H[s + 1] > H[s] + 1e-9 for s in range(k))
    ok = ok and close(H, [H[(s + 2 * k) % n] for s in range(n)]) and close(H, [H[(-s) % n] for s in range(n)])
    ok = ok and all(1e-9 < H[s] < math.log(n) - 1e-9 for s in range(n) if s % k)
    return ok, H


def normalised(H, n):
    """H / log n, the entropy curve normalised."""
    return [h / math.log(n) for h in H]


def rounds_to(x, t):
    """round(x, 2) equals the stated two-place value t (a rational with denominator 100)."""
    return abs(round(x, 2) - float(t)) < 1e-9


def input_dependence(Hn, shells):
    """E6: δ_1 against δ_0 at n = 12, δ_6 reproducing δ_0, δ_j meeting the odd projectors exactly off {0, 2κ}."""
    R = Readout(12)
    H1 = [entropy(R.column(s, 1)) / math.log(12) for s in range(12)]
    H6 = [entropy(R.column(s, 6)) / math.log(12) for s in range(12)]
    ok = rounds_to(H1[1], 0.55) and rounds_to(Hn[1], 0.44) and close(H6, Hn) and not close(H1, Hn)
    for p in shells:
        nn = p - 1; kk = nn // 4; Rp = Readout(nn)
        for j in range(nn):
            odd = math.sqrt(sum(abs(Rp.P[1][a][j]) ** 2 for a in range(nn))) + math.sqrt(sum(abs(Rp.P[3][a][j]) ** 2 for a in range(nn)))
            ok = ok and ((odd < 1e-12) == (j in (0, 2 * kk)))
    return ok, H1


def twist(curves, shells, H1):
    """E7: the Galois twist X ↦ ζ^u on the six shells: (ok, units, relabelled pairs, h5, h3)."""
    ok, n_units, n_pairs = True, 0, 0
    for p in shells:
        nn = p - 1; kk = nn // 4; base = curves[p]; R1 = Readout(nn)
        for u in range(1, nn):
            if math.gcd(u, nn) != 1: continue
            Ru = Readout(nn, u); n_units += 1
            Hu = [entropy(Ru.column(s, 0)) for s in range(nn)]
            ok = ok and close(Hu, [base[(u * s) % nn] for s in range(nn)])
            for j in range(nn):
                ok = ok and abs(entropy(Ru.column(0, j))) < 1e-9 and abs(entropy(Ru.column(2 * kk, j))) < 1e-9
                ok = ok and abs(entropy(Ru.column(kk, j)) - math.log(nn)) < 1e-9 and abs(entropy(Ru.column(3 * kk, j)) - math.log(nn)) < 1e-9
                if u == nn - 1:
                    Hj = [entropy(R1.column(s, j)) for s in range(nn)]
                    ok = ok and close([entropy(Ru.column(s, j)) for s in range(nn)], [Hj[(-s) % nn] for s in range(nn)])
            eta = 1 if u % 4 == 1 else -1
            ok = ok and all((eta * u * j - j) % nn == 0 for j in (0, kk, 2 * kk, 3 * kk))
            perm = [(eta * u * x) % nn for x in range(nn)]
            for j in range(nn):
                if (eta * u * j - j) % nn: continue
                for s in range(nn):
                    tw = [abs(x) ** 2 for x in Ru.column(s, j)]; un = [abs(x) ** 2 for x in R1.column((u * s) % nn, j)]
                    st, su = sum(tw), sum(un)
                    ok = ok and close([x / st for x in tw], [un[q] / su for q in perm])
                n_pairs += 1
    R5, R12 = Readout(12, 5), Readout(12)
    h5 = entropy(R5.column(1, 1)) / math.log(12)
    ok = ok and rounds_to(h5, 0.44) and rounds_to(H1[1], 0.55)
    c1t = [entropy(R5.column(s, 1)) / math.log(12) for s in range(12)]
    ok = ok and not any(close(c1t, [H1[(v * s) % 12] for s in range(12)]) for v in (1, 5, 7, 11))
    c3 = [entropy(R12.column(s, 3)) for s in range(12)]; c3t = [entropy(R5.column(s, 3)) for s in range(12)]
    h3 = c3[1] / math.log(12)
    ok = ok and close(c3, c3t) and rounds_to(h3, 0.42)
    return ok, n_units, n_pairs, h5, h3


def uncertainty(shells, rng, stated, states=40):
    """E8: the fractional uncertainty relation and the p = 13 bound −2 log c(s)/log n: (ok, the bound)."""
    ok = True
    for p in shells:
        n = p - 1; k = n // 4; R = Readout(n); z = cmath.exp(2j * math.pi / n)
        for s in range(n):
            Fs = R.matrix(s); c2 = max(abs(x) for row in Fs for x in row) ** 2
            ts = ((2 - z ** (2 * s) - z ** (-2 * s)) / 4).real
            p0 = 1 - (n - 1) / n * ts
            ok = ok and c2 >= max(1.0 / n, p0) - 1e-12 and abs(abs(Fs[0][0]) ** 2 - p0) < 1e-9
            ok = ok and (abs(c2 - 1.0 / n) < 1e-9) == (s in (k, 3 * k)) and (abs(c2 - 1.0) < 1e-9) == (s in (0, 2 * k))
            for _ in range(states):
                psi = random_state(n, rng)
                ok = ok and entropy(psi) + entropy(apply_h(Fs, psi)) >= -math.log(c2) - 1e-9
    R = Readout(12)
    bound = [-2 * math.log(max(abs(x) for row in R.matrix(s) for x in row)) / math.log(12) for s in range(12)]
    ok = ok and all(rounds_to(b, t) for b, t in zip(bound, stated))
    return ok, bound
