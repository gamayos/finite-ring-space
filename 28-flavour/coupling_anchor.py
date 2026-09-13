#!/usr/bin/env python3
# -*- coding: utf-8 -*-
"""
The coupling anchor (ledger A7/A8): the lattice->continuum matching of the bare alpha=1/4pi.
The bare coupling alpha_bare=1/4pi is EXACT (channel unity) -- but it is a per-link LATTICE
coupling at the substrate spacing a~ell_P, not the continuum renormalised coupling.  The two
differ by a finite matching Z, computed in lattice perturbation theory.  This resolves the
'too strong' puzzle (1/4pi = alpha^-1 12.6 is stronger than the continuum unified coupling
~42) -- the bare lattice coupling is ALWAYS stronger than the continuum, the standard
lattice-continuum offset.  The matching is ONE object that, with the derived spectrum, fixes
all the IR couplings (alpha, alpha_s -> Lambda_QCD) and through them the EW exponent c: it
consolidates the three residuals (the alpha digit, Lambda_QCD, v) into one.
Continuum/data computation (RG running, perturbative matching) -- a labelled demonstration.
"""
import numpy as np
pi=np.pi
MZ=91.1876; MP=1.220890e19

# couplings at M_Z (GUT-normalised a1)
aem_inv=127.951; s2w=0.23121; a3=0.1181
a2_inv=aem_inv*s2w; aY_inv=aem_inv*(1-s2w); a1_inv=(3/5)*aY_inv; a3_inv=1/a3
b=np.array([41/10,-19/6,-7])                          # SM one-loop (GUT norm)
abare_inv=4*pi
t=np.log(MP/MZ)
def run(inv0,bi,tt): return inv0-(bi/(2*pi))*tt

print(f"alpha_bare^-1 = 4pi = {abare_inv:.3f}   (the EXACT bare LATTICE coupling, channel unity)")
print(f"at M_Z: a1^-1={a1_inv:.2f} a2^-1={a2_inv:.2f} a3^-1={a3_inv:.2f}")

print("\n--- continuum couplings run up to the substrate scale M_P ---")
for tag,mu in [("M_P",MP)]:
    tt=np.log(mu/MZ)
    aMP=[run(a1_inv,b[0],tt),run(a2_inv,b[1],tt),run(a3_inv,b[2],tt)]
    print(f"  at {tag}: a1^-1={aMP[0]:.1f} a2^-1={aMP[1]:.1f} a3^-1={aMP[2]:.1f}")

# approximate unification (a1=a2)
tU=(a1_inv-a2_inv)/((b[0]-b[1])/(2*pi))
muU=MZ*np.exp(tU); aGUT_inv=run(a1_inv,b[0],tU); a3U=run(a3_inv,b[2],tU)
print(f"\n  a1=a2 unify at mu~{muU:.1e} GeV, alpha_GUT^-1={aGUT_inv:.1f}; "
      f"a3^-1={a3U:.1f} there (the ~{100*abs(aGUT_inv-a3U)/aGUT_inv:.0f}% near-miss = A10)")

print("\n--- the lattice->continuum matching (the anchor) ---")
Delta=aGUT_inv-abare_inv
print(f"  bare LATTICE alpha^-1 = 4pi = {abare_inv:.1f}  vs  continuum unified alpha_GUT^-1 = {aGUT_inv:.1f}")
print(f"  matching  Delta(alpha^-1) = {Delta:.1f}  (continuum WEAKER than bare lattice)")
print(f"  -> the 'too strong' is the standard lattice-continuum offset: the bare lattice")
print(f"     coupling is always stronger than the continuum (cf Lambda_MSbar/Lambda_lat >> 1,")
print(f"     e.g. ~28.8 for SU(3)), by a finite matching Z computable in lattice PT.")

print("\n--- consolidation: ONE anchor fixes alpha, Lambda_QCD, v ---")
print("  All gauge couplings descend from the single bare 1/4pi at the substrate; the matching")
print("  + RG running gives the three IR couplings -> alpha(0) (from a1,a2), Lambda_QCD (from a3,")
print("  dimensional transmutation), and v (from the Higgs CW, driven by y_t~1).  So the alpha")
print("  digit, Lambda_QCD, and the EW exponent c are ONE residual: the matching Z (= A7).")

print(f"\n  Lambda_QCD = M_P exp(-2pi/(b0 alpha_s)) and v = M_P exp(-c) are BOTH exponentials of the")
print(f"  matched coupling at the substrate -- once the matching Z fixes alpha_s and the running,")
print(f"  both dimensionful scales follow.  (the rough one-loop value is scale-scheme sensitive;")
print(f"  the proton mass ~ Lambda_QCD is the IR image, the NNLO/anchor residual.)")
print("\nRESIDUAL: the precise matching Z for the FRC Wilson action (lattice PT) = A7, the one")
print("bounded computation that closes alpha(0), Lambda_QCD, and v together.")
