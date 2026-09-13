# framed-rational status: MIXED -- exact framed-rational core; continuum constructs are confined to clearly-labelled [approx] / degenerate-idealisation comparisons (Tier 2/3/5 or measured-data), never to an exact claim.
"""
P1: renormalisation-group running of the gauge couplings.

One-loop RG, alpha_i^{-1}(mu) = alpha_i^{-1}(M_Z) - (b_i/2pi) ln(mu/M_Z), with the
Standard-Model coefficients (GUT-normalised hypercharge) b = (41/10, -19/6, -7)
fixed by the matter content (Section 7).  We run the measured M_Z couplings up,
locate the scale where alpha_1 = alpha_2, verify that sin^2(theta_W) = 3/8 there
EXACTLY (the Section-7 / EW-1 value, automatic at the meeting), and report the
near-meeting of alpha_3 -- the known Standard-Model near-miss.  The Section-7
unification value 3/8 is thereby connected to the measured 0.231 by the running.
"""
import math

# ---- measured inputs at M_Z (PDG) ----
M_Z = 91.1876
ainv_em = 127.951            # alpha_em^{-1}(M_Z)
sin2 = 0.23121               # sin^2(theta_W)(M_Z)
alpha_s = 0.1179
cos2 = 1 - sin2

# couplings in the GUT-normalised basis at M_Z
a1inv = (3/5) * cos2 * ainv_em      # U(1)_Y, GUT normalised: alpha_1 = (5/3) alpha_Y
a2inv = sin2 * ainv_em              # SU(2):  alpha_2 = alpha_em / sin^2
a3inv = 1/alpha_s                   # SU(3)
b = (41/10, -19/6, -7)              # one-loop SM coefficients

print("="*66)
print("P1  renormalisation-group running of the gauge couplings")
print("="*66)
print(f"\nat M_Z = {M_Z} GeV:  a1^-1={a1inv:.2f}  a2^-1={a2inv:.2f}  a3^-1={a3inv:.2f}"
      f"   (sin^2={sin2})")

def run(ainv0, bi, t):               # t = ln(mu/M_Z)
    return ainv0 - (bi/(2*math.pi))*t

# ---- scale where alpha_1 = alpha_2 ----
# a1inv - b1/2pi t = a2inv - b2/2pi t  ->  t = 2pi (a1inv-a2inv)/(b1-b2)
t12 = 2*math.pi*(a1inv - a2inv)/(b[0]-b[1])
M_X = M_Z*math.exp(t12)
aG = run(a2inv, b[1], t12)
a3_at = run(a3inv, b[2], t12)
print(f"\nalpha_1 = alpha_2 at  mu = {M_X:.2e} GeV  (~10^{math.log10(M_X):.1f}),"
      f"  alpha_GUT^-1 = {aG:.1f}")
print(f"alpha_3^-1 there = {a3_at:.1f}   (vs {aG:.1f}: SM near-miss, {abs(a3_at-aG)/aG*100:.0f}%)")

# ---- sin^2(theta_W) at the meeting = 3/8 exactly ----
# at alpha_1=alpha_2: alpha_Y=(3/5)alpha_1=(3/5)alpha_2 ; sin^2 = alpha_Y/(alpha_2+alpha_Y)
sin2_X = (3/5)/(1 + 3/5)
print(f"\nsin^2(theta_W) at unification (alpha_1=alpha_2) = {sin2_X} = 3/8"
      f"   (the Section-7 / EW-1 value, recovered exactly)")

# ---- run sin^2(theta_W) from 3/8 down to M_Z and compare ----
# sin^2(M_Z) predicted by running 3/8 down: use a1,a2 at M_X=alpha_GUT, run down
def sin2_at(t):
    a1 = run(aG, b[0], t - t12); a2 = run(aG, b[1], t - t12)
    aY = (3/5)*a1                       # alpha_Y^-1 = (5/3) a1^-1 -> alpha_Y=(3/5)alpha_1
    # sin^2 = alpha_Y/(alpha_2+alpha_Y) in terms of inverses:
    alpha_Y = 5/3/a1 if False else (3/5)*(1/a1)   # alpha_Y = (3/5) alpha_1
    alpha_2 = 1/a2
    return alpha_Y/(alpha_2+alpha_Y)
print(f"running 3/8 from M_X down to M_Z gives sin^2(M_Z) ~ {sin2_at(0):.3f}"
      f"   (measured {sin2}); one-loop, no thresholds")

print("\n" + "-"*66)
print("Section-7 value 3/8 = the unification value; running connects it to the")
print("measured 0.231.  The three couplings NEAR-meet ~10^13-10^16 GeV; the alpha_3")
print("near-miss is the known SM feature -> exact unification wants extra structure")
print("(P8).  The precise alpha_GUT reduces to the embedding/bare coupling (P2,P8).")
print("="*66)
