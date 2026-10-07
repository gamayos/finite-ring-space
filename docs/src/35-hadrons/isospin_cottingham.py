#!/usr/bin/env python3
# WP5 - isospin and electromagnetic splittings, and the octet hyperfine fine structure.
#
# Framed-rational / 1-algebra: the Coleman-Glashow relation and the spin correlators are exact
# rational identities; the EM weights are exact charge-squared rationals. No RNG, no logs, no
# fit. PDG enters once as the labelled [approx] readout.
#
# Isospin breaking has two additive (one-body) sources: the d-u current-mass seed (28-flavour,
# with theta-bar = 0 placing the breaking in the up-down sector, D6d) and the electromagnetic
# self-energy. Write a single isospin-breaking unit delta = delta_d - delta_u per (d <- u) swap.

from fractions import Fraction as F

def zero(v):
    return all(x == 0 for x in v)

def lincomb(cs, vs):
    n = len(vs[0]); out = [F(0)] * n
    for c, v in zip(cs, vs):
        for i in range(n):
            out[i] += F(c) * v[i]
    return out

print("== WP5a: Coleman-Glashow as an exact one-body identity ==")
# Each octet isospin splitting, in units of delta = delta_d - delta_u, counting (d minus u) content:
#   n - p           : udd - uud = 1*delta
#   Xi^- - Xi^0     : dss - uss = 1*delta
#   Sigma^- - Sigma^+ : dds - uus = 2*delta
# basis (delta,): coefficient vectors
np_   = (F(1),)
XimX0 = (F(1),)
SmSp  = (F(2),)
cg = lincomb([1, 1, -1], [np_, XimX0, SmSp])     # (n-p) + (Xi^- - Xi^0) - (Sigma^- - Sigma^+)
print(f"  (n-p) + (Xi^- - Xi^0) - (Sigma^- - Sigma^+)  in units of delta = {tuple(str(x) for x in cg)}")
print(f"  -> Coleman-Glashow identity holds for ALL delta: {zero(cg)}   (EM self-energy cancels)")
assert zero(cg)

print("\n== WP5b: n heavier than p, from the d-u seed vs charge-squared EM ==")
# delta = (m_d - m_u) + (EM_d - EM_u). One-body EM self-energy ~ Q^2.
Qu, Qd = F(2, 3), F(-1, 3)
emu, emd = Qu * Qu, Qd * Qd          # charge-squared weights
print(f"  charge-squared EM weights: Q_u^2 = {emu}, Q_d^2 = {emd}  -> EM(u) > EM(d), so EM_d - EM_u < 0")
print(f"  proton uud has sum Q^2 = {Qu*Qu+Qu*Qu+Qd*Qd}; neutron udd has sum Q^2 = {Qu*Qu+Qd*Qd+Qd*Qd}")
print( "  so EM makes the proton heavier; the observed n > p requires the mass seed m_d - m_u to win.")
print( "  delta = (m_d - m_u) [+] + (EM_d - EM_u) [-];  sign(delta) = sign(n-p) > 0 fixes m_d > m_u (28-flavour seed).")

print("\n== WP5c: the Sigma-Lambda splitting as octet hyperfine fine structure ==")
# Lambda and Sigma^0 share content uds but differ in the light (ud) pair spin:
#   Lambda: (ud) spin-0 ;  Sigma: (ud) spin-1.  Exact spin correlators:
SuSd_L = F(-3, 4)                     # ud spin-0: S_u.S_d = -3/4
SuSd_S = F( 1, 4)                     # ud spin-1: S_u.S_d = +1/4
# strange coupling to the ud pair: <S_s.(S_u+S_d)> = 1/2[S(S+1) - S_ud(S_ud+1) - 3/4]
def Ss_dot_pair(twoS, twoSud):
    S = F(twoS, 2); Sud = F(twoSud, 2)
    return F(1, 2) * (S * (S + 1) - Sud * (Sud + 1) - F(3, 4))
SsPair_L = Ss_dot_pair(1, 0)          # Lambda: ud spin-0, total 1/2 -> 0
SsPair_S = Ss_dot_pair(1, 2)          # Sigma : ud spin-1, total 1/2 -> -1
print(f"  ud pair  S_u.S_d:   Lambda {SuSd_L}   Sigma {SuSd_S}   (difference {SuSd_S - SuSd_L})")
print(f"  s-to-pair <S_s.(S_u+S_d)>: Lambda {SsPair_L}   Sigma {SsPair_S}")
# hyperfine: H = a_ll (S_u.S_d) + a_ls <S_s.(S_u+S_d)> ,  a_ls < a_ll since 1/(m_l m_s) < 1/(m_l^2)
# M_Sigma - M_Lambda = a_ll (1/4 - (-3/4)) + a_ls (-1 - 0) = a_ll - a_ls > 0
print(f"  M_Sigma - M_Lambda = a_ll*({SuSd_S - SuSd_L}) + a_ls*({SsPair_S - SsPair_L}) = a_ll - a_ls")
print( "  since a_ls = a_ll*(m_l/m_s) < a_ll, M_Sigma - M_Lambda = a_ll(1 - m_l/m_s) > 0: Sigma heavier (derived).")

print("\n== [approx] PDG 2024 confrontation ==")
p, n = F("938.272"), F("939.565")
Sp, S0, Sm = F("1189.37"), F("1192.642"), F("1197.449")
X0, Xm = F("1314.86"), F("1321.71")
L = F("1115.683")
lhs = (n - p) + (Xm - X0)
rhs = Sm - Sp
print(f"  Coleman-Glashow: (n-p)+(Xi^- - Xi^0) = {float(lhs):.3f} MeV  vs  Sigma^- - Sigma^+ = {float(rhs):.3f} MeV"
      f"   residual = {float((lhs-rhs)/rhs)*100:+.2f}%   [approx]")
print(f"  n - p = {float(n-p):.3f} MeV  > 0  (mass seed wins over EM)   [approx]")
print(f"  M_Sigma0 - M_Lambda = {float(S0 - L):.1f} MeV  > 0  (spin-1 ud pair, hyperfine)   [approx]")

print("\nWP5 PASS: Coleman-Glashow is an exact one-body identity (PDG 0.8%); n>p sign fixed by the")
print("d-u seed over charge-squared EM; the Sigma-Lambda ordering is derived hyperfine fine structure.")
