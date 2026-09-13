#!/usr/bin/env python3
# -*- coding: utf-8 -*-
"""
transform_charts.py  (26-pnp, item 2 anchor: V1 + V3)
Representation-relativity made concrete on a structured (convolution) problem:
the same target is FAR in the position chart and NEAR in the Fourier chart,
because the Fourier transform diagonalises convolution and is forward-computable (FFT).
  V1  cyclic convolution: position chart O(n^2) vs Fourier chart O(n log n).
  V3  the diagonalising transform (FFT) is itself in P: T, T^{-1} poly and exact.
"""
import time, numpy as np
rng = np.random.default_rng(0)

def direct_conv(a, b):                       # position chart: O(n^2)
    return np.convolve(a, b)

def fourier_conv(a, b):                      # Fourier chart: O(n log n)
    n = len(a) + len(b) - 1
    m = 1 << (n-1).bit_length()
    return np.fft.irfft(np.fft.rfft(a, m) * np.fft.rfft(b, m), m)[:n]

print(f"{'n':>7} {'position (s)':>13} {'Fourier (s)':>12} {'pos/Fourier':>12} {'max|diff|':>11}")
ns, tpos, tfou = [], [], []
for n in (2048, 4096, 8192, 16384):
    a = rng.standard_normal(n); b = rng.standard_normal(n)
    t0=time.perf_counter(); c1=direct_conv(a,b); tp=time.perf_counter()-t0
    t0=time.perf_counter(); c2=fourier_conv(a,b); tf=time.perf_counter()-t0
    ns.append(n); tpos.append(tp); tfou.append(tf)
    print(f"{n:>7} {tp:>13.4f} {tf:>12.5f} {tp/tf:>12.1f} {np.max(np.abs(c1-c2)):>11.2e}")

bp=np.polyfit(np.log(ns), np.log(tpos),1)[0]
bf=np.polyfit(np.log(ns), np.log(tfou),1)[0]
print(f"\nposition chart ~ n^({bp:.2f}) (the O(n^2) direct sum)")
print(f"Fourier  chart ~ n^({bf:.2f}) (the O(n log n) FFT) -- same target, near in one chart, far in the other")

# V3: the transform itself is in P and exact (T and T^{-1} polynomial)
x = rng.standard_normal(1<<16)
err = np.max(np.abs(np.fft.ifft(np.fft.fft(x)).real - x))
print(f"\nFFT round-trip on n=2^16: max|T^-1 T x - x| = {err:.2e}  -- the diagonalising transform is forward-computable (P).")
