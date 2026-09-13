# framed-rational status: EXACT -- integer / modular-F_p / cyclotomic arithmetic; no float in any asserted check (float, if present, only formats an exact rational for display).
"""
P11: the substrate residue  Omega = 5 (mod 12).

(a) Arithmetic: symmetry-completeness needs 4 | Omega-1 (the quarter-turn, in the
    split torus of order Omega-1, complex QM); colour triality needs 3 | Omega+1
    (the Z_3 centre, in the non-split torus of order Omega+1).  By CRT,
        Omega = 1 (mod 4)  AND  Omega = 2 (mod 3)  <=>  Omega = 5 (mod 12).
    The two conditions sit in the two non-trivial frame tori.
(b) Status: =1 mod 4 is DEFINITIONAL (the corpus's symmetry-complete shell, complex
    QM); =2 mod 3 is the colour-centre / stable-matter condition.
(c) Forced vs selection -- relational resolution: the Carrier is the totality and the
    Subject is within it (no external multiverse), so the residue is FORCED by the
    self-consistency of an observer-bearing substrate, not selected among cosmoi.
(d) Reduction: the residue is the arithmetic shadow of the four-fold (Q_4, mod 4)
    and the cubic (colour/generations, mod 3) structures.
"""
from sympy import isprime, primerange

print("="*68)
print("P11  the substrate residue  Omega = 5 (mod 12)")
print("="*68)

# ---- (a) CRT: the two conditions <=> 5 mod 12 ----
print("\n(a) CRT over residues mod 12:")
for r in range(12):
    c4 = (r % 4 == 1)        # quarter-turn / complex QM (4 | Omega-1)
    c3 = (r % 3 == 2)        # colour Z_3 centre        (3 | Omega+1)
    if c4 and c3:
        print(f"    Omega = {r} mod 12 :  (=1 mod4: {c4})  AND  (=2 mod3: {c3})  <-- the unique residue")
print("    => Omega = 5 (mod 12) is the unique residue with BOTH; 5 mod4=1, 5 mod3=2.")
print("    quarter-turn lives in the Omega-1 (split) torus; colour Z_3 in the Omega+1 (non-split) torus.")

# ---- (c) density among primes: Dirichlet 1/phi(12) = 1/4 ----
import collections
cnt = collections.Counter(p % 12 for p in primerange(5, 200000))
tot = sum(cnt[r] for r in (1,5,7,11))
print("\n  density of large primes by residue mod 12 (Dirichlet 1/4 each):")
for r in (1,5,7,11):
    print(f"    p = {r:2d} mod 12 : {cnt[r]/tot:.3f}")
print(f"    => Omega = 5 mod 12 (admissible substrate) has density 1/4 among primes;")
print(f"       admissible Omega near 10^122 are abundant (Dirichlet).")

# ---- corpus example shells ----
print("\n  corpus example shells mod 12 (all symmetry-complete, =1 mod 4):")
for p in (13, 53, 61, 157, 421):
    print(f"    F_{p}: {p} mod 12 = {p%12}  ({'=5: has colour Z_3' if p%12==5 else '=1: cube roots in base field, no colour centre'})")
print("    (small shells illustrate the structure; the cosmic Omega ~ 10^122 needs")
print("     the extra colour condition =2 mod 3, hence =5 mod 12.)")

print("\n(c) RELATIONAL resolution (forced, not selected):")
print("    The Carrier is the totality; the Subject (observer, composite matter) is a")
print("    nested shell WITHIN it.  There is no external multiverse to select among.")
print("    A self-consistent observer-bearing substrate must host its own observers,")
print("    which requires complex QM (=1 mod 4) and colour-confined matter (=2 mod 3).")
print("    Hence Omega = 5 mod 12 is FORCED by self-consistency, not anthropically chosen.")
print("\n(d) The residue is the arithmetic shadow of the four-fold (Q_4, mod 4) and the")
print("    cubic (colour/generations, mod 3); not an independent free parameter.")
print("="*68)
