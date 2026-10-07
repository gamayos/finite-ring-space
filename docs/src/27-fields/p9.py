# framed-rational status: EXACT -- integer / modular-F_p / cyclotomic arithmetic; no float in any asserted check (float, if present, only formats an exact rational for display).
"""
P9: generation replication -- the Galois-conjugate lead.

Matter conjugates under the Galois group of the substrate's extension tower.
Frobenius x->x^q on F_{q^n} has order n, so an element of F_{q^n} (not in a
subfield) has exactly n Galois conjugates -- an n-fold orbit of algebraically
identical objects differing only by the Frobenius label.

  quadratic extension F_{q^2}: Galois Z_2 -> 2 conjugates = the 2 CHIRALITIES (P4);
  cubic    extension F_{q^3}: Galois Z_3 -> 3 conjugates = 3 GENERATIONS (lead).

Galois conjugates share their minimal polynomial, hence all algebraic (gauge)
properties: this is GENERATION UNIVERSALITY -- the generations identical except
for the label, the mass difference coming from the per-conjugate winding overlap
(P7).  Degrees 2 and 3 are coprime, so chirality and generations are independent
(Z_2 x Z_3 = Z_6 over F_{q^6}), matching that leptons have generations but no colour.

The orbit sizes are computed exactly as the orbits of multiplication-by-q on
Z/(q^n - 1) (the exponent lattice of a generator); orbit size = degree.
OPEN KERNEL: why the matter extension is CUBIC (degree 3, not 2 or 4).
"""
from math import gcd

def frobenius_orbits(q, n):
    """Orbits of x -> x^q on F_{q^n}^x, as orbits of *q on Z/(q^n-1)."""
    N = q**n - 1
    seen = set(); orbits = []
    for a in range(N):
        if a in seen: continue
        orb = []; b = a
        while b not in seen:
            seen.add(b); orb.append(b); b = (b*q) % N
        orbits.append(orb)
    return orbits

def report(q, n, label):
    orbits = frobenius_orbits(q, n)
    sizes = sorted({len(o) for o in orbits})
    maxsize = max(len(o) for o in orbits)
    nmax = sum(1 for o in orbits if len(o) == maxsize)
    print(f"  F_{{{q}^{n}}} (Galois Z_{n}): Frobenius orbit sizes on F^x = {sizes};"
          f"  {nmax} orbits of full size {maxsize}  -> {label}")
    return maxsize

print("="*68)
print("P9  generations as Galois conjugates of the substrate's extension tower")
print("="*68)
print("\nFrobenius x->x^q on F_{q^n} has order n; a primitive element has n conjugates.")
print()
for q in (2, 3, 5):
    print(f" q={q}:")
    s2 = report(q, 2, "2 CHIRALITIES (quadratic, P4)")
    s3 = report(q, 3, "3 GENERATIONS (cubic, the lead)")
    s6 = report(q, 6, "Z_6 = Z_2 x Z_3 (chirality x generations)")
    print(f"    degree of chirality ext = {s2}, of generation ext = {s3},"
          f"  coprime: {gcd(s2,s3)==1}  (independent sectors)")
    print()

print("-"*68)
print("Generation universality: conjugates share a minimal polynomial, hence all")
print("gauge quantum numbers -- the 3 generations identical except for mass.")
print("The number = the Galois degree; chirality is the degree-2 (quadratic) case,")
print("derived in P4; generations the degree-3 (cubic) case.  EXACTLY 3 = cubic degree.")
print("OPEN KERNEL: why the matter extension is cubic (4th role x->x^3, rank-3 colour,")
print("cube-root sector are the entry points).  P9 remains a lead, not a derivation.")
print("="*68)
