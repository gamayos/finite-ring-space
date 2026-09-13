#!/usr/bin/env python3
# -*- coding: utf-8 -*-
"""
longitudinal.py
===============
Probe of the LONGITUDINAL (additive <-> multiplicative) transformation as the non-linear
mechanism for binary Goldbach in finite ring cosmology.

The latitudinal (Fourier / quarter-turn) transform is linear and parity-limited; the
longitudinal transform converts additive relations to multiplicative ones and is non-linear.
Transporting the Goldbach relation g^a + g^b = n through it produces KLOOSTERMAN sums --- the
canonical non-linear additive/multiplicative coupling --- whose control is the function-field
Riemann Hypothesis (Weil's bound; Frobenius eigenvalues), the same structure FRC's RH
realisation is built on.

Tests:
  L1  the longitudinal object is Kloosterman: N(s) = #{x in F_P^x : x + x^{-1} = s}
      is reconstructed exactly from the Kloosterman Fourier coefficients K(k,k;P).
  L2  Weil bound: |K(u,v;P)| <= 2 sqrt(P)  (square-root cancellation = function-field RH).
  L3  Frobenius / function-field-RH governance: the normalised traces K/sqrt(P) obey the
      Sato-Tate (Catalan) moments  E[t^2]=1, E[t^4]=2, E[t^6]=5  --- the SAME Frobenius
      statistics FRC realises for the Riemann zeros.
  L4  averaged cancellation of  sum_{p<=C} K(m,n;p)  vs the trivial bound sum|K| and the
      square-root (random-walk) baseline sqrt(sum K^2).

SCOPE.  L1-L3 confirm the mechanism is real and FRC-native: the longitudinal object is
Kloosterman, square-root bounded, and governed by the function-field-RH/Frobenius structure
the programme already realises.  L4 measures base-level averaging cancellation.  NONE of this
proves binary Goldbach.  The cancellation L4 exhibits (complete Kloosterman sums summed over
the modulus) is classically accessible and does NOT by itself defeat the binary L^2-mass
deficit; the binary-sufficiency question lives in the finer incomplete/bilinear regime, where
the spectral (Kuznetsov) gain is marginal, and is open.  This script tests the MECHANISM, not
the conjecture.

Dependencies: numpy, sympy.
"""
import numpy as np
from sympy import primerange

PASS = 0
def ok(tag, cond, msg):
    global PASS
    assert cond, f"FAIL {tag}: {msg}"
    print(f"PASS {tag}: {msg}"); PASS += 1

e = lambda t: np.exp(2j * np.pi * t)

def inverses(P):
    inv = np.zeros(P, dtype=np.int64)
    for x in range(1, P):
        inv[x] = pow(x, P - 2, P)          # Fermat inverse
    return inv

def kloosterman(u, v, P, inv):
    x = np.arange(1, P)
    return float(np.sum(e((u * x + v * inv[x]) / P)).real)   # Kloosterman sums are real

# --------------------------------------------------------------------------- L1
P = 1009; inv = inverses(P)
xs = np.arange(1, P)
N = np.bincount((xs + inv[xs]) % P, minlength=P)             # direct count of x + x^{-1} = s
Kdiag = np.array([float(np.sum(e(k * (xs + inv[xs]) / P)).real) for k in range(P)])  # K(k,k;P)
Nrec = np.rint(np.real(np.fft.ifft(Kdiag))).astype(int)      # N(s) = (1/P) sum_k K(k,k) e(-ks/P)
ok("L1", np.array_equal(Nrec, N),
   f"P={P}: additive relation x+x^(-1)=s reconstructed exactly from Kloosterman coeffs "
   f"K(k,k;P) -> the longitudinal transform produces Kloosterman sums")

# --------------------------------------------------------------------------- L2
mx = max(abs(kloosterman(u, v, P, inv)) for u in range(1, 40) for v in range(1, 40)) / np.sqrt(P)
ok("L2", mx <= 2.0 + 1e-9,
   f"P={P}: max |K(u,v;P)| / sqrt(P) = {mx:.3f} <= 2 (Weil bound; the function-field-RH cancellation)")

# --------------------------------------------------------------------------- L3
t = np.array([kloosterman(u, 1, P, inv) for u in range(1, P)]) / np.sqrt(P)   # normalised traces
m2, m4, m6 = float(np.mean(t**2)), float(np.mean(t**4)), float(np.mean(t**6))
ok("L3", abs(m2 - 1) < 0.05 and abs(m4 - 2) < 0.05 and abs(m6 - 5) < 0.15,
   f"P={P}: Sato-Tate moments E[t^2]={m2:.3f}(=1) E[t^4]={m4:.3f}(=2) E[t^6]={m6:.3f}(=5), "
   f"Catalan -> the longitudinal object obeys the Frobenius/function-field-RH statistics FRC realises")

# --------------------------------------------------------------------------- L4
print("# L4  averaged cancellation of sum_p K(m,n;p) (base-level; necessary, not sufficient for binary)")
for (m, n) in [(1, 1), (1, 7)]:
    Ks = []
    for p in primerange(3, 4000):
        Ks.append(kloosterman(m, n, p, inverses(p)))
    Ks = np.array(Ks)
    actual = abs(np.sum(Ks)); trivial = np.sum(np.abs(Ks)); sqrtc = np.sqrt(np.sum(Ks**2))
    ok("L4", actual < 0.5 * sqrtc + 1e-9,
       f"m,n={m,n}: |sum_p K|={actual:.1f}  trivial sum|K|={trivial:.1f}  sqrt-baseline={sqrtc:.1f}  "
       f"actual/trivial={actual/trivial:.3f}  actual/sqrt={actual/sqrtc:.2f} (cancellation beyond random)")

print(f"\nlongitudinal: all checks passed ({PASS} checks)")
print("NOTE: mechanism confirmed and FRC-native (L1-L3); base-level averaging cancellation present (L4).")
print("This does NOT prove binary Goldbach -- the binary-sufficient incomplete/bilinear cancellation is open.")
