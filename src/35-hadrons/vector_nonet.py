#!/usr/bin/env python3
# Stage 1 of the hadron extension: the meson Carrier residue and the vector-meson nonet.
#
# Framed-rational: the residue and the equal-spacing identity are exact (finite field / rationals);
# the absolute table and PDG comparison are the labelled [approx] readout. No RNG, no logs, no fit
# beyond the two anchors. Shares the colour frame, SU(3)_F, colour-magnetic hyperfine and scale
# sqrt(sigma) with the baryon sector. The pseudoscalars are Goldstone bosons (chiral companion).

from fractions import Fraction as F
from itertools import product

# ---- meson Carrier residue: q qbar colour singlet = the trace of 3 (x) 3bar = residue 1, B=0 ----
print("== meson = Carrier residue 1 (B=0): the trace invariant of 3 (x) 3bar ==")
# rebuild SU(3,F_2) over F_4 (as in carrier_residue.py), confirm the q-qbar contraction is invariant.
EXP={1:0,2:1,3:2}; ANTI={0:1,1:2,2:3}
fadd=lambda a,b:a^b
fmul=lambda a,b:0 if(a==0 or b==0)else ANTI[(EXP[a]+EXP[b])%3]
fconj=lambda a:0 if a==0 else ANTI[(2*EXP[a])%3]
I3=(1,0,0,0,1,0,0,0,1)
def matmul(A,B):
    C=[0]*9
    for i in range(3):
        for j in range(3):
            s=0
            for k in range(3): s=fadd(s,fmul(A[3*i+k],B[3*k+j]))
            C[3*i+j]=s
    return tuple(C)
def dag(A): return tuple(fconj(A[3*j+i]) for i in range(3) for j in range(3))
def det3(A):
    a,b,c,d,e,f,g,h,i=A
    return fadd(fadd(fmul(a,fadd(fmul(e,i),fmul(f,h))),fmul(b,fadd(fmul(d,i),fmul(f,g)))),fmul(c,fadd(fmul(d,h),fmul(e,g))))
G=[M for M in product(range(4),repeat=9) if det3(M)==1 and matmul(dag(M),M)==I3]
print(f"  |SU(3,F_2)| = {len(G)}; the unitary (Hermitian) contraction v^a wbar_a is preserved by every U")
print(f"  (U^dag U = I for all U): the q-qbar singlet is the 1-dim invariant of 3 (x) 3bar = 1 (+) 8.")
# triality: quark +1, antiquark -1 -> 0 (mod 3): colourless, B = (n_q - n_qbar)/3 = 0.
print(f"  triality 1 + (-1) = 0 -> colour-singlet meson, residue 1, baryon number B = 0.")
print(f"  residue series now complete: photon 2, gluon 0, baryon 1 (Lambda^3), meson 1 (trace, B=0).")
assert len(G)==216

# ---- vector nonet spectroscopy (S=1, <S_q.S_qbar> = +1/4; same colour-magnetic operator) ----
print("\n== vector nonet: equal spacing (linear strangeness), exact identity ==")
# within the spin-1 nonet the hyperfine is a common shift, so mass differences are pure strangeness:
# M(n_s) = a + b n_s, n_s = 0 (rho,omega), 1 (K*), 2 (phi). basis (a,b):
rho=(F(1),F(0)); Kstar=(F(1),F(1)); phi=(F(1),F(2))
eq = [2*Kstar[i]-rho[i]-phi[i] for i in range(2)]      # 2 K* - rho - phi
print(f"  2 M_K* - M_rho - M_phi (in basis a,b) = {tuple(str(x) for x in eq)}  -> identity: {all(x==0 for x in eq)}")
assert all(x==0 for x in eq)
print("  i.e. M_K* - M_rho = M_phi - M_K* : the vector analogue of the decuplet equal spacing.")

print("\n== [approx] PDG 2024 vector nonet ==")
Mrho=F("775.26"); Mome=F("782.66"); MKs=(F("891.67")+F("895.55"))/2; Mphi=F("1019.46")
lhs=2*MKs; rhs=Mrho+Mphi
print(f"  equal spacing: 2 M_K* = {float(lhs):.1f}  vs  M_rho + M_phi = {float(rhs):.1f} MeV  ({float((lhs-rhs)/rhs)*100:+.2f}%)")
# absolute table: anchor rho (n_s=0) and phi (n_s=2); predict K* (n_s=1) and omega (ideal mixing = rho)
a=Mrho; b=(Mphi-Mrho)/2
pred={"rho":(a,Mrho,"anchor"),"omega":(a,Mome,"predict (ideal mixing = rho)"),
      "K*":(a+b,MKs,"predict (equal spacing)"),"phi":(a+2*b,Mphi,"anchor")}
print("\n  meson      content   FRC     PDG      Delta%   role")
for nm,(frc,pdg,role) in pred.items():
    cont={"rho":"u-dbar","omega":"(uu+dd)","K*":"u-sbar","phi":"s-sbar"}[nm]
    print(f"  {nm:6s} {cont:9s} {float(frc):7.1f} {float(pdg):7.1f} {float((frc-pdg)/pdg)*100:+7.2f}  {role}")
print(f"\n  strange increment b = (M_phi - M_rho)/2 = {float(b):.1f} MeV (meson strange excess;")
print(f"  cf. baryon Lambda-N gap 176.8 MeV -- the meson constituent masses are the 2-body confinement")
print(f"  eigenvalues, distinct from the 3-body baryon values, same sqrt(sigma) and same mechanism).")

print("\n== the vector-pseudoscalar split and the Goldstone caveat ==")
print("  the same colour-magnetic operator gives <S_q.S_qbar> = +1/4 (vector) vs -3/4 (pseudoscalar).")
print("  the pseudoscalars (pi, K, eta, eta') are Goldstone bosons of chiral symmetry breaking,")
print("  anomalously light (m_pi ~ 140 << 2 m_l): NOT constituent states -> the chiral companion,")
print("  not treated here. The vector nonet is the constituent-model hadron the present tools fit.")

print("\nSTAGE 1: meson residue 1 (B=0) completes the residue series; the vector nonet obeys the")
print("equal-spacing relation 2 M_K* = M_rho + M_phi to ~0.5%, ideal mixing M_omega ~ M_rho, from the")
print("same SU(3)_F + colour-magnetic structure and the one scale sqrt(sigma).")
