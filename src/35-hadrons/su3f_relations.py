#!/usr/bin/env python3
# WP2/WP3 - the SU(3)_F baryon mass relations, exact and scale-cancelling.
#
# Framed-rational / 1-algebra: the identities are proved in exact rational arithmetic
# (Fraction) as coefficient-vector identities, valid for EVERY value of the parameters, so
# the confinement scale sqrt(sigma) (Omega-hard, D6c) cancels. No RNG, no logs, no fit.
# The PDG confrontation is the single labelled [approx] readout at the end.
#
# Structure of the wrapped composite (master eq. of the blueprint):
#   M_B = sqrt(sigma) * [ f_fl(B) + kappa_hf g_spin(B) ] + Delta^EM_B .
# Within one spin multiplet g_spin is constant, so the spin term is an overall shift and the
# SU(3)_F relations live entirely in f_fl, the flavour structure. f_fl is taken linear in the
# strange-seed count at leading order (one fixed wrap increment per strange constituent), the
# increment fixed upstream by the chi_3 current-mass ratio (28-flavour). Linearity is the
# only structural input; the relations below are identities given it.

from fractions import Fraction as F

def zero_vec(v):
    return all(x == 0 for x in v)

def lincomb(coeffs, vecs):
    n = len(vecs[0])
    out = [F(0)] * n
    for c, v in zip(coeffs, vecs):
        for i in range(n):
            out[i] += F(c) * v[i]
    return out

print("== WP3a: Gell-Mann-Okubo octet relation as an exact identity ==")
# Octet first-order breaking operator  M = M0 + a*Y + b*[ I(I+1) - Y^2/4 ]  (the 8 of SU(3)_F).
# Coefficient vectors in the basis (M0, a, b):
#   I(I+1) - Y^2/4  for each isomultiplet:
#     N : Y=+1, I=1/2 -> 3/4 - 1/4 = 1/2
#     L : Y= 0, I=0   -> 0
#     S : Y= 0, I=1   -> 2
#     X : Y=-1, I=1/2 -> 1/2
octet = {
    "N": (F(1), F( 1), F(1, 2)),
    "L": (F(1), F( 0), F(0)),
    "S": (F(1), F( 0), F(2)),
    "X": (F(1), F(-1), F(1, 2)),
}
# GMO:  (N + X)/2 = (3 L + S)/4   <=>   2N + 2X - 3L - S = 0
gmo = lincomb([2, 2, -3, -1], [octet["N"], octet["X"], octet["L"], octet["S"]])
print(f"  2*N + 2*X - 3*L - S  (in basis M0,a,b) = {tuple(str(x) for x in gmo)}")
print(f"  -> identity holds for ALL (M0,a,b): {zero_vec(gmo)}   (sqrt(sigma) and breaking params cancel)")
assert zero_vec(gmo)

print("\n== WP3b: decuplet equal spacing as an exact identity ==")
# Decuplet operator linear in strange-seed count n_s:  M = alpha + beta*n_s .
# Coefficient vectors in basis (alpha, beta):  n_s = 0,1,2,3 for Delta, Sigma*, Xi*, Omega.
dec = {
    "D":  (F(1), F(0)),   # Delta    n_s=0
    "S*": (F(1), F(1)),   # Sigma*   n_s=1
    "X*": (F(1), F(2)),   # Xi*      n_s=2
    "O":  (F(1), F(3)),   # Omega    n_s=3
}
# equal spacing <=> the second differences vanish:
d1 = lincomb([1, -2, 1], [dec["D"], dec["S*"], dec["X*"]])   # D - 2S* + X*
d2 = lincomb([1, -2, 1], [dec["S*"], dec["X*"], dec["O"]])   # S* - 2X* + O
print(f"  D - 2 S* + X*  = {tuple(str(x) for x in d1)}")
print(f"  S* - 2 X* + O  = {tuple(str(x) for x in d2)}")
print(f"  -> equal spacing holds for ALL (alpha,beta): {zero_vec(d1) and zero_vec(d2)}")
assert zero_vec(d1) and zero_vec(d2)
print("  the common spacing is beta = (M_Omega - M_Delta)/3, one strange-seed wrap increment.")

# =====================================================================================
# [approx] PDG 2024 confrontation. Isospin-averaged masses, MeV, as exact rationals.
# This is the single labelled continuum readout; the identities above are the framed result.
# =====================================================================================
print("\n== [approx] PDG 2024 confrontation (isospin-averaged, MeV) ==")
def avg(*xs):
    s = F(0)
    for x in xs:
        s += F(str(x))
    return s / len(xs)

mN = avg(938.272, 939.565)
mL = F("1115.683")
mS = avg(1189.37, 1192.642, 1197.449)
mX = avg(1314.86, 1321.71)

lhs = (mN + mX) / 2
rhs = (3 * mL + mS) / 4
res = (rhs - lhs) / rhs
print(f"  octet:  (N+X)/2 = {float(lhs):8.2f}   (3L+S)/4 = {float(rhs):8.2f}   "
      f"residual = {float(res)*100:+.2f}%   [approx]")

mD  = F("1232.0")
mSs = avg(1382.8, 1383.7, 1387.2)
mXs = avg(1531.80, 1535.0)
mO  = F("1672.45")
sp = [mSs - mD, mXs - mSs, mO - mXs]
mean = sum(sp, F(0)) / 3
spread = (max(sp) - min(sp)) / mean
print(f"  decuplet spacings (MeV): {float(sp[0]):.1f}, {float(sp[1]):.1f}, {float(sp[2]):.1f}"
      f"   mean increment beta = {float(mean):.1f}   spread = {float(spread)*100:.1f}%   [approx]")
print(f"  decuplet beta from equal spacing (M_O - M_D)/3 = {float((mO-mD)/3):.1f} MeV   [approx]")
print(f"  octet strange step (X - N)/2 = {float((mX-mN)/2):.1f} MeV/strange   [approx]")

print("\nWP3 PASS: GMO and decuplet equal spacing are exact, parameter-free, scale-cancelling")
print("identities; PDG confirms them to 0.57% (octet) and a 9.2% spacing spread (decuplet).")
print("Forward (WP5): the Coleman-Glashow isospin relation p-n + Xi^- - Xi^0 = Sigma^- - Sigma^+.")
