"""
a_datum.py — block A: the Euclidean datum and the involutions (2:B3, D1–D8)
============================================================================
Section 2 (the frame) and Section 4 (symmetry axes and structural data) of the paper, on the shells
p ∈ {5, 13, 17, 29, 37, 41} and every primitive generator.  \\label(s): prop:half-period,
def:quarter-turn-subgroup, prop:quarter-turn, rem:observer-canonical-e, rem:exponential-unit (A1);
prop:primitive-orbit, prop:no-canonical-e (A2); rem:frame-transport (A3); the Euler identity of 00:C14 (A4);
prop:shell-negation, prop:k4-shell (A5); rem:euclidean-conjugation (A6).
"""
import math
from collections import Counter
import geocommon as gc

def run():
    # A1 half-period, quarter-turn of order four, i = −g^κ with i² = −1, 2π = −1, e = g^i (2:D1–D4)
    ok = True; det = []
    for p, k in gc.SHELLS:
        pi = 2 * k
        for g in gc.generators(p):
            i = gc.quarter_turn(p, g)
            ok &= pow(g, pi, p) == p - 1 and (i * i) % p == p - 1 and pow(g, 4 * k, p) == 1 and gc.order(pow(g, k, p), p) == 4
            ok &= (2 * pi) % p == p - 1
            Q = {x for x in range(1, p) if pow(x, 4, p) == 1}
            ok &= Q == {1, p - 1, i, (-i) % p}
        g = gc.generators(p)[0]; i = gc.quarter_turn(p, g)
        det.append(f"p={p}: g={g}, i={i}, e=g^i={pow(g, i, p)}, pi={pi}")
    gc.check("A1", "half-period g^pi = -1; i = -g^k of order 4 with i^2 = -1; Q_p = {±1, ±i}; 2pi = -1; e = g^i", ok, "; ".join(det[:3]))

    # A2 the primitive generators form one orbit g^u, u a unit mod p−1 (2:B3)
    ok = True
    for p, k in gc.SHELLS:
        gens = set(gc.generators(p)); g = min(gens)
        orbit = {pow(g, u, p) for u in gc.units(p - 1)}
        ok &= orbit == gens and len(gens) == len(gc.units(p - 1))
    gc.check("A2", "generators = {g^u : gcd(u, p-1) = 1}, one Aut(C_{p-1})-torsor", ok)

    # A3 orientation classes: i' = i iff u ≡ 1 (mod 4), i' = −i iff u ≡ 3 (mod 4) (2:D5)
    ok = True; det = []
    for p, k in gc.SHELLS:
        g = gc.generators(p)[0]; i = gc.quarter_turn(p, g)
        for u in gc.units(p - 1):
            ip = gc.quarter_turn(p, pow(g, u, p))
            ok &= (ip == i) == (u % 4 == 1) and (ip == (-i) % p) == (u % 4 == 3)
        same = sum(1 for u in gc.units(p - 1) if u % 4 == 1)
        det.append(f"p={p}: {same} of {len(gc.generators(p))} generators keep i")
    gc.check("A3", "orientation classes of the quarter-turn under g -> g^u: kept for u = 1, flipped for u = 3 (mod 4)", ok, "; ".join(det))

    # A4 the Euler identity e^{iπ} = g^{2κ i²} = (−1)^i, −1 iff the residue i is odd (2:D6, 00:C14)
    ok = True; det = []
    for p, k in gc.SHELLS:
        for g in gc.generators(p):
            i = gc.quarter_turn(p, g); e = pow(g, i, p)
            ok &= pow(e, i * 2 * k, p) == (p - 1 if i % 2 else 1)
        odd = [g for g in gc.generators(p) if gc.quarter_turn(p, g) % 2 == 1]
        det.append(f"p={p}: i odd for g in {odd[:6]}{'...' if len(odd) > 6 else ''} ({len(odd)}/{len(gc.generators(p))})")
    ok &= gc.quarter_turn(13, 2) == 5 and gc.quarter_turn(17, 3) == 4 and gc.quarter_turn(17, 6) == 13
    gc.check("A4", "Euler identity e^{i pi} = (-1)^i with i the residue representative; F13 g=2 odd, F17 g=3 even", ok, "; ".join(det[:3]))

    # A5 negation/inversion orbits: F_p^x \ Q_p splits into κ−1 orbits of size four (2:D7, 1:B2)
    ok = True
    for p, k in gc.SHELLS:
        Q = {x for x in range(1, p) if pow(x, 4, p) == 1}
        seen, orbits = set(), 0
        for x in range(1, p):
            if x in Q or x in seen: continue
            orb = {x, (-x) % p, pow(x, -1, p), (-pow(x, -1, p)) % p}
            ok &= len(orb) == 4; seen |= orb; orbits += 1
        ok &= len(Q) == 4 and orbits == k - 1
        R = lambda x: (-x) % p; I = lambda x: pow(x, -1, p)
        ok &= all(R(R(x)) == x and I(I(x)) == x and R(I(x)) == I(R(x)) for x in range(1, p))
    gc.check("A5", "R, I commuting involutions; <R,I>-orbits off Q_p have four elements, k-1 of them", ok)

    # A6 Euclidean conjugation: an involution of pairs; the pair map (a, b) -> a + b i is p-to-one (2:D8)
    ok = True
    for p, k in gc.SHELLS:
        g = gc.generators(p)[0]; i = gc.quarter_turn(p, g)
        fibres = Counter((a + b * i) % p for a in range(p) for b in range(p))
        ok &= set(fibres.values()) == {p} and len(fibres) == p
        C = lambda a, b: (a, (-b) % p)
        ok &= all(C(*C(a, b)) == (a, b) for a in range(p) for b in range(p))
        a, b = 0, 1; a2, b2 = i, 0        # 0 + 1·i = i + 0·i, but the conjugates differ: not a map of the field
        ok &= (a + b * i) % p == (a2 + b2 * i) % p and (a - b * i) % p != (a2 - b2 * i) % p
    gc.check("A6", "conjugation is an involution of the pairs, not of the field (the pair map is p-to-one)", ok)

if __name__ == "__main__":
    run(); gc.summary(write=False)
