"""
c_chi.py — block C, continued: the χ-twisted comb and the generalized hypothesis ([approx])
==========================================================================================
Proposition chi states that the construction goes through verbatim for a real (quadratic)
character; Numerical Observation chi supports it for χ_{−4} (conductor 4, odd, root number 1).
Two arms:

  * the construction arm — the twisted secular condition N_χ(T) = θ_χ(T)/π + S^χ_comb(T), with
    θ_χ(t) = Im log Γ(¾ + it/2) + (t/2) log(4/π) and the χ-weighted tapered comb Λ_χ(n) = χ(n)Λ(n),
    with no pole term; L never evaluated;
  * the validation arm — L(s, χ_{−4}) = 4^{−s}[ζ(s, ¼) − ζ(s, ¾)] via Hurwitz zeta (mpmath), its
    completed form real on the line, its zeros located as sign changes.

Paper-local predicates:

  C7a Obs. chi  [approx]  N_χ evaluated at the first six zeros of L(s, χ_{−4}) (validation arm) reads
                          0.4997, 1.4998, 2.4999, 3.4999, 4.4999, 5.4998
  C7b Obs. chi  [approx]  solving the twisted secular condition with the N = 10⁶ comb recovers the six
                          heights 6.0209, 10.2438, 12.9881, 16.3426, 18.2920, 21.4506 to mean error
                          8.6×10⁻⁵ (the floor of the untwisted case, Obs. trace)
  C7c Obs. chi  [approx]  the complex character χ mod 5 with χ(2) = i (odd, conductor 5): the half-phase
                          W(χ)^{−1/2} Λ(½ + it, χ) is real on the line (validation arm, Hurwitz zeta); the
                          twisted count (1/π)[θ_χ(T) − θ_χ(0)] + (1/π) Im[Σ^χ_w(½+iT) − Σ^χ_w(½)], with
                          θ_χ(t) = Im log Γ(¾ + it/2) + (t/2) log(5/π) and no pole term, reads the exact
                          integers 1 … 14 midway between the fifteen zeros below 40; its half-integer
                          crossings, bracketed by the count alone, recover the fifteen heights with the
                          N = 10⁶ comb to mean error 8.0×10⁻⁵ (max 2.0×10⁻⁴), L never evaluated (ledger E16)
"""
import math
import numpy as np
import mpmath as mp
from scipy.special import loggamma
from scipy.optimize import brentq
from rhcommon import secular_roots_scan
from rhcommon import check, Comb, von_mangoldt_support, count_raw, FAST, Timer

mp.mp.dps = 20
HEIGHTS_CHI_STATED = [6.0209, 10.2438, 12.9881, 16.3426, 18.2920, 21.4506]
NCHI_STATED = [0.4997, 1.4998, 2.4999, 3.4999, 4.4999, 5.4998]

def chi4(n):
    """χ_{−4}(n): 0 on even n, +1 on n ≡ 1, −1 on n ≡ 3 (mod 4)."""
    n = np.asarray(n)
    return np.where(n % 2 == 0, 0.0, np.where(n % 4 == 1, 1.0, -1.0))

def twisted_support(N):
    """(n, χ(n)Λ(n)) on the prime powers ≤ N with χ(n) ≠ 0."""
    n, lam = von_mangoldt_support(N)
    c = chi4(n.astype(np.int64))
    keep = c != 0
    return n[keep], (c * lam)[keep]

def theta_chi(T):
    T = np.asarray(T, float)
    return np.imag(loggamma(0.75 + 0.5j * T)) + 0.5 * T * math.log(4 / math.pi)

def Lambda_chi_line(t):
    """Completed Λ(½ + it, χ_{−4}) = (4/π)^{(s+1)/2} Γ((s+1)/2) L(s, χ); real for this character (root number 1)."""
    s = mp.mpf(1) / 2 + mp.mpc(0, 1) * t
    L = mp.power(4, -s) * (mp.zeta(s, mp.mpf(1) / 4) - mp.zeta(s, mp.mpf(3) / 4))
    return mp.power(4 / mp.pi, (s + 1) / 2) * mp.gamma((s + 1) / 2) * L

def run():
    print("\n== block C (continued): the χ-twisted comb, χ = χ_{−4} (Prop. chi, Obs. chi) ==")
    # validation arm: the completed L is real on the line; its first six zeros by sign change + refinement
    with Timer("Hurwitz-zeta validation arm"):
        ts = np.arange(1.0, 23.0, 0.01)
        vals = [Lambda_chi_line(float(t)) for t in ts]
        im_max = max(abs(mp.im(v)) for v in vals)
        re = np.array([float(mp.re(v)) for v in vals])
        idx = np.nonzero(re[:-1] * re[1:] < 0)[0]
        zeros = np.array([brentq(lambda t: float(mp.re(Lambda_chi_line(t))), ts[i], ts[i + 1], xtol=1e-10) for i in idx])[:6]
    ok_real = im_max < 1e-15
    # construction arm
    N = 10 ** 6
    with Timer(f"twisted comb to {N}"):
        comb = Comb(N, lam_fn=twisted_support)
    nchi = count_raw(comb, zeros, const=0.0, theta_fn=theta_chi)
    ok = ok_real and len(zeros) == 6 and np.max(np.abs(zeros - HEIGHTS_CHI_STATED)) < 6e-5 and np.max(np.abs(nchi - NCHI_STATED)) < 6e-5
    check("C7a", "N_χ at the first six zeros of L(s, χ_{−4}) reads 0.4997 … 5.4998 (completed L real on the line)", ok,
          "zeros " + ", ".join(f"{z:.4f}" for z in zeros) + "; N_χ " + ", ".join(f"{v:.4f}" for v in nchi) + f"; max|Im Λ| = {float(im_max):.1e}", kind="[approx]")
    # construction arm: the brackets come from the twisted count itself (its half-integer crossings on [3, 23]); the
    # reference zeros of the validation arm enter only in the error reported
    roots, levels, extra = secular_roots_scan(comb, 3.0, 23.0, const=0.0, theta_fn=theta_chi)
    assert levels == [k + 0.5 for k in range(6)] and not extra, f"crossings {levels}, extra {extra}"
    err = np.abs(roots - zeros)
    check("C7b", "twisted secular condition, N = 10⁶ comb, L never evaluated: six heights to mean error 8.6e-5", abs(err.mean() - 8.6e-5) < 1.5e-5,
          "roots " + ", ".join(f"{r:.4f}" for r in roots) + f"; mean error {err.mean():.2e}, max {err.max():.2e}", kind="[approx]")
    run_complex()

# ----------------------------------------------------------------------------- C7c: the complex character mod 5
CHI5 = np.array([0, 1, 1j, -1j, -1], dtype=complex)        # χ(n) by n mod 5: χ(1)=1, χ(2)=i, χ(3)=−i, χ(4)=−1
MP_CHI5 = {1: mp.mpc(1), 2: mp.mpc(0, 1), 3: mp.mpc(0, -1), 4: mp.mpc(-1)}

class ComplexTwistedComb:
    """The χ-weighted tapered comb for a complex character: Σ^χ_w(½ + iT) = Σ_{n≤N} χ(n)Λ(n) w(n) n^{−½−iT}/log n, and
    S(T) = (1/π) Im[Σ^χ_w(½+iT) − Σ^χ_w(½)] — the comb side of the twisted count, the difference from height 0
    removing the constant of the complex case (Obs. chi). Exposes N and S(T) so that the scan of rhcommon applies."""
    def __init__(self, N, chi_table):
        self.N = int(N)
        n, lam = von_mangoldt_support(self.N)
        logn = np.log(n); L = math.log(self.N)
        w = 0.5 * (1.0 + np.cos(np.pi * logn / L))
        self.logn = logn
        self.coef = lam * w / (np.sqrt(n) * logn) * chi_table[(n % len(chi_table)).astype(int)]
        self.sigma0 = np.sum(self.coef)
    def sigma_w(self, T):
        T = np.atleast_1d(np.asarray(T, float))
        out = np.empty(len(T), dtype=complex)
        for s in range(0, len(T), 64):
            blk = T[s:s + 64]
            out[s:s + 64] = (self.coef[:, None] * np.exp(-1j * np.outer(self.logn, blk))).sum(0)
        return out
    def S(self, T):
        T = np.atleast_1d(np.asarray(T, float))
        val = (self.sigma_w(T) - self.sigma0).imag / math.pi
        return val if val.size > 1 else float(val[0])

def theta_chi5(T):
    T = np.asarray(T, float)
    return np.imag(loggamma(0.75 + 0.5j * T)) + 0.5 * T * math.log(5 / math.pi)

def theta_chi5_from0(T):
    return theta_chi5(T) - theta_chi5(0.0)

def L_chi5(s):
    return mp.power(5, -s) * sum(MP_CHI5[a] * mp.zeta(s, mp.mpf(a) / 5) for a in (1, 2, 3, 4))

def Z_chi5_factory():
    """Z_χ(t) = W(χ)^{−1/2} Λ(½ + it, χ) with Λ(s, χ) = (5/π)^{(s+1)/2} Γ((s+1)/2) L(s, χ) and W(χ) = τ(χ)/(i√5): real on the line."""
    I = mp.mpc(0, 1)
    tau = sum(MP_CHI5[a] * mp.expjpi(mp.mpf(2 * a) / 5) for a in (1, 2, 3, 4))
    W = tau / (I * mp.sqrt(5)); Whalf = mp.sqrt(W)
    def Z(t):
        s = mp.mpf(1) / 2 + I * t
        return mp.power(5 / mp.pi, (s + 1) / 2) * mp.gamma((s + 1) / 2) * L_chi5(s) / Whalf
    return Z, W

def run_complex():
    print("\n== block C (continued): the complex character χ mod 5, χ(2) = i (Prop. chi, Obs. chi; ledger E16) ==")
    with Timer("Hurwitz-zeta validation arm, χ mod 5"):
        Z, W = Z_chi5_factory()
        ts = np.arange(0.0, 40.0, 0.02)
        zv = [Z(float(t)) for t in ts]
        im_max = float(max(abs(mp.im(z)) for z in zv))
        re = np.array([float(mp.re(z)) for z in zv])
        idx = np.nonzero(re[:-1] * re[1:] < 0)[0]
        zeros = np.array([brentq(lambda t: float(mp.re(Z(t))), ts[i], ts[i + 1], xtol=1e-10) for i in idx])
    N = 10 ** 6
    with Timer(f"complex twisted comb to {N}"):
        comb = ComplexTwistedComb(N, CHI5)
    mids = 0.5 * (zeros[1:] + zeros[:-1])
    cnt = count_raw(comb, mids, const=0.0, theta_fn=theta_chi5_from0)
    ok_count = len(zeros) == 15 and np.max(np.abs(cnt - np.arange(1, len(zeros)))) < 0.05
    ok_real = abs(float(abs(W)) - 1.0) < 1e-15 and im_max < 1e-15
    # the brackets come from the twisted count itself; the validation arm's zeros enter only in the error reported
    roots, levels, extra = secular_roots_scan(comb, 2.0, 40.0, const=0.0, theta_fn=theta_chi5_from0)
    assert levels == [k + 0.5 for k in range(15)] and not extra, f"crossings {levels}, extra {extra}"
    err = np.abs(roots - zeros)
    check("C7c", "χ mod 5 complex: Z_χ real on the line; the twisted count reads 1 … 14 between the fifteen zeros below 40; "
          "the secular condition (N = 10⁶ comb, brackets from the count alone, L never evaluated) recovers the fifteen heights to mean error 8.0e-5 (max 2.0e-4)",
          ok_real and ok_count and abs(err.mean() - 8.0e-5) < 1.5e-5 and err.max() < 2.5e-4,
          f"|W| = {float(abs(W)):.15f}, max|Im Z_χ| = {im_max:.1e}; {len(zeros)} zeros {zeros[0]:.4f} … {zeros[-1]:.4f}; count at midpoints "
          + ", ".join(f"{c:.3f}" for c in cnt) + "; roots " + ", ".join(f"{r:.4f}" for r in roots[:3]) + f" … {roots[-1]:.4f}; mean error {err.mean():.2e}, max {err.max():.2e}",
          kind="[approx]")

if __name__ == "__main__":
    from rhcommon import summary
    run(); summary(write=False)
