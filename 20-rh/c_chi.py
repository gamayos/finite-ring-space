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
"""
import math
import numpy as np
import mpmath as mp
from scipy.special import loggamma
from scipy.optimize import brentq
from rhcommon import check, Comb, von_mangoldt_support, count_raw, secular_roots, FAST, Timer

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
    windows = [(k + 1, z - 0.5, z + 0.5) for k, z in enumerate(zeros)]
    roots = secular_roots(comb, windows, const=0.0, theta_fn=theta_chi)
    err = np.abs(roots - zeros)
    check("C7b", "twisted secular condition, N = 10⁶ comb, L never evaluated: six heights to mean error 8.6e-5", abs(err.mean() - 8.6e-5) < 1.5e-5,
          "roots " + ", ".join(f"{r:.4f}" for r in roots) + f"; mean error {err.mean():.2e}, max {err.max():.2e}", kind="[approx]")

if __name__ == "__main__":
    from rhcommon import summary
    run(); summary(write=False)
