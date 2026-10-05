"""frc.carrier — the Carrier on its chart Ω = 4S + 1 (the carrier theme; ledger migration, task LM22, 5 October 2026).

The python side of `lean/FrcCore/Theme/Carrier.lean`: the register in S alone, the triality root, the octant and the
window ladder, every residue found without a generator. Exact integers only, the standard library only (gate G09).

    capacity(Om)              S with Ω = 4S + 1, Ω prime
    register(S)               the register {Ω, S, G, c², ħ, c, k_B, h} generator-free in S: a dict
    triality_roots(Om)        every root of x² + x + 1, by search
    octant(Om)                ζ = a^((Ω−1)/8) with a = half_power(Ω): an element of order eight, or None when 8 ∤ Ω − 1
    tsirelson(z, Om)          (ζ + ζ⁷)² mod Ω
    horizon(p)                the Subject's horizon ⌊√p⌋: the largest x with x² ≤ p
    quarter_root(Om)          the Carrier's quarter-root window: the largest x with x⁴ < Ω
    coherence(Om)             the coherence window: the largest x with x² < Ω
"""
from math import isqrt

from frc import arith
from frc.foundation import half_power, quarter_turn


def capacity(Om):
    """S = (Ω − 1)/4 for a prime Ω ≡ 1 (mod 4)."""
    if not (arith.is_prime(Om) and Om % 4 == 1): raise ValueError(f"capacity: {Om} is not a prime 4S + 1")
    return (Om - 1) // 4


def octant(Om):
    """ζ = a^((Ω−1)/8) with a^((Ω−1)/2) = −1: ζ⁴ = −1, ζ⁸ = 1, an element of order eight (Carrier.lean,
    `octant_sector`, the backward direction). None when 8 ∤ Ω − 1."""
    if (Om - 1) % 8: return None
    return pow(half_power(Om), (Om - 1) // 8, Om)


def tsirelson(z, Om):
    """(ζ + ζ⁷)² mod Ω: 2 when ζ⁴ = −1 (Carrier.lean, `tsirelson`)."""
    s = (z + pow(z, 7, Om)) % Om
    return s * s % Om


def register(S):
    """The Carrier register generator-free in S (master B7): Ω = 4S + 1; c² = 2S + 1 = 2⁻¹; G = 2S = −c²; ħ = a^S with
    a^(2S) = −1; h = −ħ; when S is even, c = (ζ + ζ⁷)·c² from the octant's ζ (c² = 2⁻¹, (ζ + ζ⁷)² = 2) and k_B = ħ c⁻¹,
    so k_B c = ħ and k_B² = −2. When S is odd, c and k_B are None: 2⁻¹ is no square (B7, B14). Representatives are fixed
    by the construction (the least non-residue); the pairs {±c}, {±ħ}, {±k_B} are the register's content (B10)."""
    Om = 4 * S + 1
    capacity(Om)
    c2, G = (2 * S + 1) % Om, (2 * S) % Om
    hbar = quarter_turn(Om)
    z = octant(Om)
    c = (z + pow(z, 7, Om)) * c2 % Om if z is not None else None
    kB = hbar * arith.inverse(c, Om) % Om if c is not None else None
    return {"Om": Om, "S": S, "G": G, "c2": c2, "hbar": hbar, "h": (Om - hbar) % Om, "c": c, "kB": kB}


def triality_roots(Om):
    """Every x in [0, Ω) with x² + x + 1 ≡ 0 (mod Ω), by search."""
    return [x for x in range(Om) if (x * x + x + 1) % Om == 0]


def horizon(p):
    """⌊√p⌋, the largest x with x² ≤ p."""
    return isqrt(p)


def quarter_root(Om):
    """The largest x with x⁴ < Ω (Ω ≥ 1)."""
    x = isqrt(isqrt(Om))
    while (x + 1) ** 4 < Om: x += 1
    while x ** 4 >= Om: x -= 1
    return x


def coherence(Om):
    """The largest x with x² < Ω (Ω ≥ 1): ⌊√(Ω − 1)⌋."""
    return isqrt(Om - 1)
