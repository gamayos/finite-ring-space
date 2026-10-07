#!/usr/bin/env python3
# =====================================================================
#  firstpassage_finite.py -- the finite-cycle first-passage law and the
#  controlled reduction to e^{-sqrt(x)}  (Proposition `prop:passage').
#
#  Referee point #2: the manuscript used the Brownian transform
#  E[e^{-s T_a}] = e^{-a sqrt(2s)} without a finite-shell error bound.
#  Here we (A) verify the EXACT discrete-line transform
#       E[e^{-s T_a}] = e^{-a arccosh(e^s)},
#  (B) bound its deviation from the Brownian sqrt-form, which is O(s) and
#  hence O(Omega^{-1/2}) at the substrate step rate, and (C) solve the
#  killed walk on the FINITE cycle Z_{N} and show the wrap correction is
#  exponentially negligible for a barrier below the coherence horizon.
#  No floats where an identity is claimed (mpmath at 60 digits).
# =====================================================================
import mpmath as mp
mp.mp.dps = 60

def hr(t): print("\n"+"="*70+"\n"+t+"\n"+"="*70)

# ---------------------------------------------------------------------
# A. exact single-step factor and the arccosh transform (an identity)
#    f(z) = (1 - sqrt(1-z^2))/z  solves (z/2) f^2 - f + (z/2) = 0;
#    at z=e^{-s},  f = e^{-arccosh(e^s)}  exactly.
# ---------------------------------------------------------------------
hr("A. f(e^{-s}) = e^{-arccosh(e^s)}  (exact single-step identity)")
for s in [mp.mpf('1.0'), mp.mpf('0.1'), mp.mpf('1e-3'), mp.mpf('1e-6')]:
    z = mp.e**(-s)
    f = (1 - mp.sqrt(1 - z**2))/z
    g = mp.e**(-mp.acosh(mp.e**s))
    quad = (z/2)*f**2 - f + (z/2)     # should be 0
    print(f"  s={mp.nstr(s,3):>8}: f={mp.nstr(f,12)}  e^-arccosh={mp.nstr(g,12)}  "
          f"|f-g|={mp.nstr(abs(f-g),3)}  quad={mp.nstr(abs(quad),3)}")

# ---------------------------------------------------------------------
# B. exact exponent gamma(s)=arccosh(e^s) vs Brownian sqrt(2s):
#    gamma(s) = sqrt(2s) (1 + s/12 + ...), so the RELATIVE error is O(s).
# ---------------------------------------------------------------------
hr("B. arccosh(e^s) = sqrt(2s)(1 + s/6 + s^2/120 + ...);  relative error = O(s)")
print(f"  {'s':>10} {'arccosh(e^s)':>16} {'sqrt(2s)':>16} {'rel.err':>12} {'rel.err/s':>10}")
for s in [mp.mpf('1e-1'), mp.mpf('1e-2'), mp.mpf('1e-3'), mp.mpf('1e-4')]:
    gamma = mp.acosh(mp.e**s)
    brown = mp.sqrt(2*s)
    rel = (gamma-brown)/brown
    print(f"  {mp.nstr(s,2):>10} {mp.nstr(gamma,10):>16} {mp.nstr(brown,10):>16} "
          f"{mp.nstr(rel,4):>12} {mp.nstr(rel/s,4):>10}")
print("  -> rel.err/s -> 1/6: the reduction is controlled, error linear in the step rate s.")

# substrate step rate: chronon/Hubble ~ 1/sqrt(Omega), Omega ~ 1e122.
# (rel.err = s/6 + O(s^2); evaluate the leading series term to avoid the
#  catastrophic cancellation of arccosh(e^s)-sqrt(2s) at s~1e-61.)
Omega = mp.mpf('1e122')
s_sub = 1/mp.sqrt(Omega)
rel_sub = s_sub/6
print(f"\n  substrate: s ~ Omega^-1/2 = {mp.nstr(s_sub,3)};  relative exponent error "
      f"~ s/6 = {mp.nstr(rel_sub,3)}")
print(f"  => the resolvable-window reading e^{{-sqrt x}} is carrier-exact to ~{mp.nstr(rel_sub,1)}.")

# ---------------------------------------------------------------------
# C. killed walk on the FINITE cycle Z_N: exact escape vs the line.
#    Barrier (absorbing) at a, source at 0, per-step survival z=e^{-s};
#    solve the linear recurrence for the escape (first-passage) generating
#    value exactly, compare to the infinite-line f(z)^a.
# ---------------------------------------------------------------------
hr("C. finite cycle Z_N: escape vs infinite line  (wrap correction)")
def escape_cycle(N, a, z):
    # states 0..N-1 on a cycle; absorbing barrier at site a; start at 0.
    # E[z^{T_a}] = sum over paths weighted z^steps until first hit of a.
    # Solve h_i = E[z^{T_a} | start i]; h_a = 1; for i != a:
    #   h_i = (z/2)(h_{i-1} + h_{i+1})  (indices mod N), killed by z<1.
    n = N
    A = mp.zeros(n, n); b = mp.zeros(n, 1)
    for i in range(n):
        if i == a:
            A[i, i] = 1; b[i] = 1
        else:
            A[i, i] = 1
            A[i, (i-1) % n] += -z/2
            A[i, (i+1) % n] += -z/2
    h = mp.lu_solve(A, b)
    return h[0]
def escape_line(a, z):
    f = (1 - mp.sqrt(1 - z**2))/z
    return f**a
for (N, a, s) in [(40, 5, mp.mpf('0.05')), (80, 5, mp.mpf('0.05')), (200, 8, mp.mpf('0.02'))]:
    z = mp.e**(-s)
    ec = escape_cycle(N, a, z); el = escape_line(a, z)
    print(f"  N={N:>4} a={a} s={mp.nstr(s,2)}:  cycle={mp.nstr(ec,12)}  line={mp.nstr(el,12)}  "
          f"|diff|={mp.nstr(abs(ec-el),3)}  (~e^-(N-a)arccosh(e^s)={mp.nstr(mp.e**(-(N-a)*mp.acosh(mp.e**s)),2)})")
print("  -> wrap correction vanishes ~ e^{-(N-a)}; for a << sqrt(Omega) it is carrier-negligible.")

hr("VERDICT")
print("""  * the exact carrier transform is e^{-a arccosh(e^s)} (A), an identity;
  * its reduction to the Brownian e^{-a sqrt(2s)} = e^{-sqrt x} has relative
    error O(s) = O(Omega^{-1/2}) ~ 1e-61 at the substrate step (B);
  * on the finite cycle the wrap correction is O(e^{-(N-a) arccosh(e^s)}), negligible for a
    barrier below the coherence horizon sqrt(Omega) (C).
  => e^{-sqrt x} is the resolvable-window reading of an exact finite-cycle
     law, carrier-exact to O(Omega^{-1/2}); independently it is the amplitude
     identity of Proposition prop:born (exact in Z[i]).""")
