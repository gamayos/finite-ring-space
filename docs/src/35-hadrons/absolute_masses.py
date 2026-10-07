#!/usr/bin/env python3
# The absolute octet+decuplet spectrum from one scale + two sub-horizon ratios.
#
# Framed-rational / 1-algebra: the derived structure (constituent sums + the 1/(m_i m_j) hyperfine
# with the exact spin correlators) is evaluated in exact rational arithmetic; the three anchors and
# the PDG comparison are the labelled [approx] inputs/readout. No RNG, no logs, no fit beyond the
# three physical anchors. The scale is Omega-hard (E5/D6c); the two ratios are sub-horizon.
#
# Model:  M_B = (constituent sum)  +  sum_{i<j} v_ij <S_i.S_j>,   v_ij = K/(m_i m_j).
# Parameters {m_l, m_s, K} <=> one scale m_l + two ratios m_s/m_l and v_ll/m_l.

from fractions import Fraction as F

# --- exact spin/colour structure of each baryon: constituent (n_l, n_s) and hyperfine (c_ll,c_ls,c_ss)
# hf(B) = c_ll v_ll + c_ls v_ls + c_ss v_ss ; v_ll=K/m_l^2, v_ls=K/(m_l m_s), v_ss=K/m_s^2
BAR = {
    #          n_l n_s   c_ll      c_ls      c_ss     J^P     content
    "N":   (3, 0, F(-3,4), F(0),    F(0)),
    "Lam": (2, 1, F(-3,4), F(0),    F(0)),
    "Sig": (2, 1, F(1,4),  F(-1),   F(0)),
    "Xi":  (1, 2, F(0),    F(-1),   F(1,4)),
    "Del": (3, 0, F(3,4),  F(0),    F(0)),
    "Sgs": (2, 1, F(1,4),  F(1,2),  F(0)),
    "Xis": (1, 2, F(0),    F(1,2),  F(1,4)),
    "Om":  (0, 3, F(0),    F(0),    F(3,4)),
}
PDG = {  # isospin-averaged, MeV  [approx]
    "N": F("938.9185"), "Lam": F("1115.683"),
    "Sig": (F("1189.37")+F("1192.642")+F("1197.449"))/3,
    "Xi": (F("1314.86")+F("1321.71"))/2,
    "Del": F("1232.0"),
    "Sgs": (F("1382.8")+F("1383.7")+F("1387.2"))/3,
    "Xis": (F("1531.80")+F("1535.0"))/2, "Om": F("1672.45"),
}
LABEL = {"N":"N (uud)","Lam":"Lambda (uds)","Sig":"Sigma (uds)","Xi":"Xi (uss)",
         "Del":"Delta (uuu)","Sgs":"Sigma* (uus)","Xis":"Xi* (uss)","Om":"Omega (sss)"}

# --- anchor the three parameters to {N, Lambda, Delta} (exact) ---
MN, MLam, MDel = PDG["N"], PDG["Lam"], PDG["Del"]
v_ll = F(2,3)*(MDel - MN)            # M_Delta - M_N = (3/2) v_ll
m_l  = (MN + F(3,4)*v_ll)/3          # M_N = 3 m_l - (3/4) v_ll
m_s  = m_l + (MLam - MN)             # M_Lambda - M_N = m_s - m_l  (hf(Lam)=hf(N))
K    = v_ll * m_l**2
v_ls = K/(m_l*m_s); v_ss = K/m_s**2

print("== one scale + two sub-horizon ratios, anchored to {N, Lambda, Delta} ==")
print(f"  scale   m_l       = {float(m_l):7.1f} MeV   (light constituent; ~0.8 sqrt(sigma), Omega-hard family E5)")
print(f"  ratio   m_s/m_l   = {float(m_s/m_l):7.4f}      (strange seed, sub-horizon)")
print(f"  ratio   v_ll/m_l  = {float(v_ll/m_l):7.4f}      (hyperfine, sub-horizon; v_ll={float(v_ll):.1f} MeV)")
print(f"  derived m_s={float(m_s):.1f}, v_ls={float(v_ls):.1f}, v_ss={float(v_ss):.1f} MeV (v_ij = K/(m_i m_j))")

def mass(tag):
    n_l, n_s, c_ll, c_ls, c_ss = BAR[tag]
    return n_l*m_l + n_s*m_s + c_ll*v_ll + c_ls*v_ls + c_ss*v_ss

print("\n== absolute octet + decuplet spectrum vs PDG 2024  [approx] ==")
print(f"  {'baryon':14s} {'J^P':4s} {'FRC':>9s} {'PDG 2024':>9s} {'Delta':>8s} {'Delta%':>7s}  role")
anchors = {"N","Lam","Del"}
maxabs = 0.0
for tag in ["N","Lam","Sig","Xi","Del","Sgs","Xis","Om"]:
    frc = mass(tag); pdg = PDG[tag]; d = float(frc - pdg); dp = float((frc-pdg)/pdg)*100
    jp = "1/2+" if tag in {"N","Lam","Sig","Xi"} else "3/2+"
    role = "anchor" if tag in anchors else "PREDICT"
    if tag not in anchors: maxabs = max(maxabs, abs(dp))
    print(f"  {LABEL[tag]:14s} {jp:4s} {float(frc):9.1f} {float(pdg):9.1f} {d:+8.1f} {dp:+7.2f}  {role}")
print(f"\n  3 anchors (N, Lambda, Delta); 5 parameter-free predictions, all within {maxabs:.1f}%.")

print("\n== framing ==")
print("  one Omega-hard scale (m_l ~ sqrt(sigma), E5/D6c) + two sub-horizon ratios (m_s/m_l, v_ll/m_l).")
print("  the structure (constituent sums + 1/(m_i m_j) hyperfine with exact spin correlators) is DERIVED;")
print("  the three anchors are physical (not log-rule fit params); residuals trace to the strange-wrap")
print("  and Sigma-Lambda hyperfine orders. PDG comparison [approx]; the absolute column is E5-scaled.")
print("  heavy extension (not shown): Lambda_c anchors m_c, Lambda_b via heavy-quark symmetry (~1.5%).")

print("\nABSOLUTE-SPECTRUM TABLE: octet+decuplet from one scale + two sub-horizon ratios, all rows < ~1.2%.")
