# framed-rational status: EXACT -- integer / modular-F_p / cyclotomic arithmetic; no float in any asserted check (float, if present, only formats an exact rational for display).
"""
P4: maximal parity violation (V-A) from the Frobenius branch.

The spinor's boost phase lives on the norm-one cycle U = C_{q+1} of K = F_{q^2}.
Frobenius sigma(z) = z^q = z^{-1} on U: it INVERTS the cycle -- parity/helicity
reversal.  The drive advances the boost phase by a step delta; it commutes with
Frobenius only if delta^2 = 0 (i.e. eta^2 = 1), so for a generic drive it BREAKS
parity.

The two chiralities are the spinor (drive-aligned, winds +delta) and its Frobenius
conjugate (winds -delta).  The weak connection transports the phase forward by
delta.  Over one drive period the coupling to the LEFT (drive-aligned) spinor adds
coherently (relative phase 0 -> sum = N), while to the RIGHT (Frobenius) spinor it
oscillates (relative phase 2 delta -> sum = 0 by character orthogonality).  Hence
the weak SU(2) couples to the left branch only: maximal V-A, exact.

This is the same coherent-vs-incoherent structure (N vs 0, the m vs sqrt(m) of the
synchronisation lemmas) that gives gravity universal attraction; chirality is the
coherence of the spinor winding with the drive.  Everything below is exact in
Z/(q+1) and its cyclotomic characters.
"""
import math

def boost_cycle(q):
    return q + 1                                  # |U| = q+1, U ~ Z/(q+1)

def frobenius_is_inversion(q):
    N = boost_cycle(q)
    # sigma(a) = q*a mod N  (since sigma(z)=z^q);  z^{q+1}=1 => q ≡ -1 (mod N)
    return all((q * a) % N == (-a) % N for a in range(N))

def commutator_with_frobenius(q, delta):
    """drive D: a->a+delta ; Frobenius S: a->-a.  Return whether D∘S == S∘D on U."""
    N = boost_cycle(q)
    DS = [((-a) % N + delta) % N for a in range(N)]   # drive after Frobenius
    SD = [(-((a + delta) % N)) % N for a in range(N)]  # Frobenius after drive
    return DS == SD

def coupling_coherence(q, delta):
    """Sum over one drive period of the weak connection's overlap with each branch,
    exact over Z/N: left (relative phase 0) = N; right = sum_tau zeta_N^{2 delta tau},
    a geometric series equal to N if N | 2 delta and EXACTLY 0 otherwise (no float)."""
    N = boost_cycle(q)
    left = N                                       # sum of zeta^0 over N terms
    right = N if (2 * delta) % N == 0 else 0       # exact character-sum value
    return left, right

print("=" * 66)
print("P4  maximal parity violation (V-A) from the Frobenius branch")
print("=" * 66)
print("\n[A] Frobenius = inversion on the boost cycle (parity/helicity reversal)")
for q in (3, 5, 7, 13):
    print(f"    q={q:2d}: |U|=q+1={q+1:2d},  sigma(z)=z^q = z^-1 on U : {frobenius_is_inversion(q)}")

print("\n[B] the drive breaks parity unless eta^2=1  (D∘S = S∘D  iff  2*delta ≡ 0)")
for q, delta in [(3, 1), (3, 2), (7, 1), (7, 3)]:
    N = q + 1
    print(f"    q={q}, drive step delta={delta} (eta^2=1? {2*delta % N == 0}):"
          f"  drive commutes with Frobenius = {commutator_with_frobenius(q, delta)}")

print("\n[C] coherence of the weak coupling over one drive period")
print("    LEFT = drive-aligned (coherent, sum=N) ; RIGHT = Frobenius (incoherent)")
for q in (3, 5, 7, 13):
    N = q + 1
    delta = 1                                       # generator drive, gcd(delta,N) handled below
    # choose delta coprime to N for a true generator where possible
    delta = next(d for d in range(1, N) if math.gcd(d, N) == 1)
    L, R = coupling_coherence(q, delta)
    print(f"    q={q:2d} (N={N:2d}, delta={delta}):  left coupling = {L} (=N={N}),"
          f"   right coupling = {R}  (exactly 0)")

print("\n[D] exactness: the right-branch sum is a character sum over Z/N,")
print("    sum_tau zeta_N^{2 delta tau} = N if 2 delta ≡ 0 (mod N), else 0;")
print("    for a generator drive (gcd(delta,N)=1) and N>2, 2 delta != 0 -> exactly 0.")
print("    => the Frobenius (right) branch decouples EXACTLY: maximal V-A.")
print("    Universal: all fermions ride the one drive, so all share one chirality.")
print("=" * 66)
