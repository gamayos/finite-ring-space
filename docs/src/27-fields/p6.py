# framed-rational status: MIXED -- exact framed-rational core; continuum constructs are confined to clearly-labelled [approx] / degenerate-idealisation comparisons (Tier 2/3/5 or measured-data), never to an exact claim.
"""
P6: asymptotic freedom and Lambda_QCD.

(a) SIGN of asymptotic freedom from the gluon self-coupling (P5):
    b0 = (11/3) C_A - (2/3) n_f T_F  =  11 - (2/3) n_f   for SU(3) (C_A=3, T_F=1/2).
    The +11 is anti-screening from the gluon self-coupling (non-abelian, P5);
    the -2/3 n_f screens.  b0>0 (asymptotic freedom) for the derived matter content;
    an abelian U(1) has b0 = -(4/3) n_f < 0 (screening, no AF).
(b) Lambda_QCD by dimensional transmutation: Lambda = mu exp(-2pi/(b0 alpha_s(mu))),
    exponentially below the substrate (Planck) scale -> the ~20-order QCD/Planck gap.
(c) m_proton ~ Lambda_QCD, so gravity's weakness for ordinary matter
    (m_p/m_P)^2 = exp(-4pi/(b0 alpha_s)) is the SQUARE of the dimensional-transmutation
    factor: O2's hierarchy for protons IS QCD dimensional transmutation, squared.
"""
import math
from fractions import Fraction as Fr

print("="*68)
print("P6  asymptotic freedom and the QCD scale")
print("="*68)

# ---- (a) the sign: b0 from the self-coupling ----
def b0_SU3(nf): return Fr(11,1) - Fr(2,3)*nf      # = (11/3)*3 - (2/3) nf
def b0_U1(nf):  return -Fr(4,3)*nf                 # abelian QED-like (screening)
print("\n(a) beta-function coefficient  b0 = (11/3)C_A - (2/3) n_f  (SU(3): 11 - (2/3)n_f)")
print("    the +11 is anti-screening from the GLUON SELF-COUPLING (P5, C_A=3)")
for nf in (0, 2, 6, 16, 17):
    b = b0_SU3(nf)
    print(f"    n_f={nf:2d}:  b0(SU3) = {b} = {float(b):+.2f}  ->  {'asymptotically FREE' if b>0 else 'not free'}"
          f"     [abelian U(1): b0 = {b0_U1(nf)} (screening)]")
print("    one generation n_f=2 (u,d): b0=29/3>0 ; three generations n_f=6: b0=7>0.")

# ---- (b) Lambda_QCD by dimensional transmutation ----
M_P = 1.220890e19          # Planck mass, GeV
M_Z = 91.1876
print("\n(b) Lambda_QCD = mu * exp(-2 pi / (b0 alpha_s(mu)))   (dimensional transmutation)")
# using the measured anchor alpha_s(M_Z)=0.1179, b0(n_f=5)=23/3
b0_5 = float(b0_SU3(5))
als_MZ = 0.1179
Lam = M_Z*math.exp(-2*math.pi/(b0_5*als_MZ))
print(f"    anchor alpha_s(M_Z=91 GeV)=0.118, b0(n_f=5)={b0_5:.2f}:"
      f"  Lambda_QCD ~ {Lam*1000:.0f} MeV  (observed ~200-300 MeV)")
# the hierarchy from the substrate scale with an O(1) bare coupling
print("    from the substrate scale with an O(1) bare coupling:")
for als_MP, b0v in [(1/40, 7.0), (1/50, 7.0), (1/45, 7.67)]:
    lnratio = 2*math.pi/(b0v*als_MP)
    ratio = math.exp(-lnratio)
    print(f"      alpha_s(M_P)={als_MP:.4f}, b0={b0v}:  Lambda/M_P = exp(-{lnratio:.1f}) = {ratio:.1e}"
          f"   -> Lambda ~ {ratio*M_P*1000:.0f} MeV")

# ---- (c) the gravity connection: (m_p/m_P)^2 = (dim transmutation)^2 ----
m_p = 0.9383
print("\n(c) the proton mass is the QCD scale, exponentially below the Planck mass:")
print(f"    m_p/m_P = {m_p/M_P:.2e} = exp(-{math.log(M_P/m_p):.1f})   (dimensional transmutation)")
print(f"    gravitational coupling  (m_p/m_P)^2 = {(m_p/M_P)**2:.2e} = exp(-{2*math.log(M_P/m_p):.1f})")
print("    => O2's '10^-38 gravitational coupling of protons' IS the SQUARE of the QCD")
print("       dimensional-transmutation factor.  Gravity is weak for ordinary matter")
print("       because the proton mass is exp(-2pi/(b0 alpha_s)) below the Planck scale.")
print("="*68)
print("AF sign derived from the self-coupling; the exponential QCD/Planck hierarchy is")
print("dimensional transmutation; the precise b0 reduces to the matter content (sect 7),")
print("the precise Lambda to the bare coupling (P2/P8) + running.  sigma ~ Lambda^2 (QCD-1).")
print("="*68)
