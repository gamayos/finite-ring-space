"""frc.quantum — the unequal-cycle composite (the quantum theme; ledger migration, task LM28, 6 October 2026).

The python side of `lean/FrcCore/Theme/Quantum.lean`: a composite of parts with registration periods n_j, driven jointly
one step per chronon. The joint period, the orbits of the joint drive and their offsets, and the characters of the
composite in a prime shell with their sums along the drive. Exact integers only, the standard library only (gate G09).
The first ledger to use it is the master's block file frc/ledgers/master/quantum.py.

    joint_period(ns)            the least t > 0 at which every part returns, by search
    orbits(a, b)                the orbits of (x, y) ↦ (x + 1, y + 1) on ℤ/a × ℤ/b, by enumeration
    offset(x, y, g)             the conserved offset (x − y) mod g
    reach(x, y, x2, y2, a, b)   a chronon t carrying (x, y) to (x2, y2), by search, or None
    root_of_unity(q, N)         an element of order N in 𝔽_q (N | q − 1)
    character_sums(q, a, b, T)  for every character (ζ_a, ζ_b) of ℤ/a × ℤ/b in 𝔽_q: Σ_{t<T} (ζ_a ζ_b)^t, with χ(v) ≠ 1 or not
"""
from math import gcd, lcm

from frc import arith


def joint_period(ns):
    t = 1
    while any(t % n for n in ns): t += 1
    return t


def orbits(a, b):
    seen, out = set(), []
    for x in range(a):
        for y in range(b):
            if (x, y) in seen: continue
            orb, s = [], (x, y)
            while s not in seen:
                seen.add(s); orb.append(s); s = ((s[0] + 1) % a, (s[1] + 1) % b)
            out.append(orb)
    return out


def offset(x, y, g):
    return (x - y) % g


def reach(x, y, x2, y2, a, b):
    for t in range(a * b):
        if (x + t) % a == x2 and (y + t) % b == y2: return t
    return None


def root_of_unity(q, N):
    """An element of order exactly N in 𝔽_q^× (N | q − 1)."""
    g = arith.primitive_root(q)
    return pow(g, (q - 1) // N, q)


def character_sums(q, a, b, T):
    """[(moved, Σ_{t<T} (ζ_a ζ_b)^t mod q)] over the a·b characters ζ_a = ω_a^j, ζ_b = ω_b^k of ℤ/a × ℤ/b."""
    wa, wb = root_of_unity(q, a), root_of_unity(q, b)
    out = []
    for j in range(a):
        for k in range(b):
            z = pow(wa, j, q) * pow(wb, k, q) % q
            out.append((z != 1, sum(pow(z, t, q) for t in range(T)) % q))
    return out
