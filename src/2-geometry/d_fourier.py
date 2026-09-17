"""
d_fourier.py — block D: Fourier duality on the phase cycle (2:F1, F3, F4, F5, F6)
=================================================================================
Section 6 of the paper, on (13, 2), (13, 11), (17, 3), (29, 2): the principal root (prop:principal-root, D1);
the inversion W^−1 = −(g^−jk) (prop:ring-dft-inverse, D2); the polynomial reading F(v)_k = P_v(g^k)
(prop:polynomial-form, D3); the covariance under g → g^u (prop:ring-dft-covariance, D4); and the external
transport chi(g^m) = exp(−2 pi i m/n) with its step, half-period and quarter-turn identities
(prop:datum-role-transport, D5; CHART).
"""
import math, random
import geocommon as gc

FRAMES = [(13, 2), (13, 11), (17, 3), (29, 2)]

def dft_checks(p, g):
    n = p - 1; k = (p - 1) // 4
    W = [[pow(g, j * kk, p) for j in range(n)] for kk in range(n)]
    Winv = [[(-pow(g, -j * kk, p)) % p for j in range(n)] for kk in range(n)]
    mul = lambda A, B: [[sum(A[r][t] * B[t][c] for t in range(n)) % p for c in range(n)] for r in range(n)]
    I = [[int(r == c) for c in range(n)] for r in range(n)]
    d1 = pow(g, n, p) == 1 and all(sum(pow(g, j * kk, p) for j in range(n)) % p == 0 for kk in range(1, n)) and (n * (p - 1)) % p == 1
    d2 = mul(W, Winv) == I and mul(Winv, W) == I
    rnd = random.Random(p)
    v = [rnd.randrange(p) for _ in range(n)]
    Fv = [sum(v[j] * pow(g, j * kk, p) for j in range(n)) % p for kk in range(n)]
    Pv = lambda x: sum(v[j] * pow(x, j, p) for j in range(n)) % p
    d3 = all(Fv[kk] == Pv(pow(g, kk, p)) for kk in range(n))
    d4 = True
    for u in gc.units(n):
        gp = pow(g, u, p); vp = [v[u * j % n] for j in range(n)]
        Fvp = [sum(vp[j] * pow(gp, j * kk, p) for j in range(n)) % p for kk in range(n)]
        d4 &= Fvp == Fv
    chi = lambda m: complex(math.cos(-2 * math.pi * m / n), math.sin(-2 * math.pi * m / n))
    i = gc.quarter_turn(p, g); li = next(m for m in range(n) if pow(g, m, p) == i)
    d5 = all(abs(chi(m + 1) - chi(1) * chi(m)) < 1e-12 and abs(chi(m + 2 * k) + chi(m)) < 1e-12
             and abs(chi(m + li) - 1j * chi(m)) < 1e-12 for m in range(n))
    d5 &= len({(round(chi(m).real, 9), round(chi(m).imag, 9)) for m in range(n)}) == n
    return d1, d2, d3, d4, d5

def run():
    ok = [True] * 5
    for p, g in FRAMES:
        d = dft_checks(p, g); ok = [a and b for a, b in zip(ok, d)]
    gc.check("D1", "g a principal root: g^n = 1, sum_j g^{jk} = 0 for 0 < k < n, n^-1 = -1", ok[0])
    gc.check("D2", "inversion W^-1 = -(g^{-jk}) on (13, 2), (13, 11), (17, 3), (29, 2)", ok[1])
    gc.check("D3", "polynomial reading F(v)_k = P_v(g^k)", ok[2])
    gc.check("D4", "covariance F_{g^u}(v') = F_g(v) with v'_j = v_{uj}", ok[3])
    gc.check("D5", "external transport chi(g^m) = exp(-2 pi i m/n), injective: step, half-period, quarter-turn", ok[4], kind="CHART")

if __name__ == "__main__":
    run(); gc.summary(write=False)
