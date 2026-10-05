"""frc.foundation — the prime shell without a generator (the foundation theme; ledger migration, task LM22, 5 October 2026).

The python side of `lean/FrcCore/Theme/Foundation.lean`: what the prime shell F_p yields with no drive assumed. Exact
integers only, the standard library only (gate G09). A helper enters the theme when the first ledger that uses it
migrates (task LM16); the first is the Carrier's block file (frc/ledgers/master/carrier.py).

    half_power(p)            a residue a with a^((p−1)/2) = −1, the least non-residue (Euler's criterion)
    quarter_turn(p)          ħ = a^((p−1)/4) for that a: ħ² = −1 on p ≡ 1 (mod 4), the Lean proof's construction
    quarter_turns(p)         every root of x² = −1, by search (the second method)
    square_roots(a, p)       every root of x² = a, by search
    fermat_holds(p)          a^(p−1) = 1 for every nonzero a, by computation
"""
from frc import arith


def half_power(p):
    """The least a with a^((p−1)/2) ≡ −1 (mod p), for an odd prime p: a non-residue, as Euler's criterion finds it.
    Foundation.lean's `exists_pow_half` proves one exists (X^((p−1)/2) − 1 has at most (p−1)/2 roots)."""
    if not (arith.is_prime(p) and p % 2 == 1): raise ValueError(f"half_power: {p} is not an odd prime")
    a = arith.nonresidue(p)
    assert pow(a, (p - 1) // 2, p) == p - 1
    return a


def quarter_turn(p):
    """ħ = a^((p−1)/4) with a = half_power(p): ħ² = a^((p−1)/2) = −1. Generator-free (Foundation.lean,
    `exists_quarter_turn`); p ≡ 1 (mod 4) required."""
    if p % 4 != 1: raise ValueError(f"quarter_turn: {p} ≢ 1 (mod 4)")
    return pow(half_power(p), (p - 1) // 4, p)


def square_roots(a, p):
    """Every x in [0, p) with x² ≡ a (mod p), by search: O(p)."""
    a %= p
    return [x for x in range(p) if x * x % p == a]


def quarter_turns(p):
    """Every root of x² ≡ −1 (mod p), by search."""
    return square_roots(p - 1, p)


def fermat_holds(p):
    """a^(p−1) ≡ 1 (mod p) for every a in [1, p), by computation (Foundation.lean, `fermat`)."""
    return all(pow(a, p - 1, p) == 1 for a in range(1, p))
