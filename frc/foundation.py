"""frc.foundation — the prime shell without a generator (the foundation theme; ledger migration, tasks LM22 and LM23,
5 October 2026).

The python side of `lean/FrcCore/Theme/Foundation.lean` and `lean/FrcCore/Theme/Drive.lean`: what the prime shell F_p
yields with no drive assumed, the successor cycle on q points, and the drive that every prime carries. Exact integers
only, the standard library only (gate G09). A helper enters the theme when the first ledger that uses it migrates (task
LM16): the Carrier's block file (frc/ledgers/master/carrier.py), then the foundation's (frc/ledgers/master/foundation.py).

    half_power(p)            a residue a with a^((p−1)/2) = −1, the least non-residue (Euler's criterion)
    quarter_turn(p)          ħ = a^((p−1)/4) for that a: ħ² = −1 on p ≡ 1 (mod 4), the Lean proof's construction
    quarter_turns(p)         every root of x² = −1, by search (the second method)
    square_roots(a, p)       every root of x² = a, by search
    fermat_holds(p)          a^(p−1) = 1 for every nonzero a, by computation
    successor_orbit(q, x)    the orbit of x under x ↦ x + 1 on [0, q), until it returns (A5)
    principal_ideal(a, q)    the multiples of a mod q, the least ideal holding a (A10)
    is_complete(q)           every nonzero residue's ideal holds 1, by search: no proper nonzero ideal (A10)
    zero_divisors(q)         the pairs (a, b) of nonzero residues with a b = 0, by search
    element_order(x, p)      the least n ≥ 1 with xⁿ = 1, by iteration, no factorisation (Drive.lean, `exists_order`)
    drive(p)                 the primitive root the Lean proof builds, generator-free (Drive.lean, `exists_drive`)
    collision(rho, n)        two points i < j < n with rho(i) = rho(j), by search, or None (A4, `observer_part`)
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


def successor_orbit(q, x=0):
    """The orbit x, x + 1, … of the successor C_q on [0, q) (q ≥ 1), iterated until it returns to x: its points in
    order. Foundation.lean's `successor_cycle` proves the return comes after exactly q steps."""
    x %= q
    orbit, y = [x], (x + 1) % q
    while y != x:
        orbit.append(y); y = (y + 1) % q
    return orbit


def principal_ideal(a, q):
    """The multiples r·a mod q, r in [0, q): the least ideal of Z/q holding a, sorted."""
    return sorted({r * a % q for r in range(q)})


def is_complete(q):
    """True iff the ideal of every nonzero residue holds 1, by search (q ≥ 2): then every ideal holding a nonzero a holds
    its multiples and so 1, and the ring Z/q has no proper nonzero ideal. Foundation.lean's `isPrime_iff_complete`."""
    return all(any(r * a % q == 1 for r in range(q)) for a in range(1, q))


def zero_divisors(q):
    """Every pair (a, b) of nonzero residues mod q with a·b ≡ 0, by search."""
    return [(a, b) for a in range(1, q) for b in range(1, q) if a * b % q == 0]


def element_order(x, p):
    """The least n ≥ 1 with xⁿ ≡ 1 (mod p), by iteration: no factorisation (x a unit mod p)."""
    x %= p
    y, n = x, 1
    while y != 1 % p:
        y = y * x % p; n += 1
        if n > p: raise ValueError(f"element_order: {x} is not a unit mod {p}")
    return n


def drive(p):
    """The primitive root of the prime p that Drive.lean's proof builds, generator-free: for each prime power qᵉ ∥ p − 1,
    the least a ≥ 1 with a^((p−1)/q) ≠ 1 (the root bound guarantees one) and z_q = a^((p−1)/qᵉ), of order qᵉ; the drive is
    the product of the z_q (orders of coprime prime powers multiply). p = 2 gives 1."""
    if not arith.is_prime(p): raise ValueError(f"drive: {p} is not prime")
    n, g = p - 1, 1
    for q, e in sorted(arith.factorize(n).items()):
        a = next(a for a in range(1, p) if pow(a, n // q, p) != 1)
        g = g * pow(a, n // q ** e, p) % p
    return g


def collision(rho, n):
    """Two points i < j < n with rho(i) == rho(j), the first j in order (by search), or None when rho is injective on
    [0, n). Foundation.lean's `observer_part` searches the same way."""
    seen = {}
    for j in range(n):
        v = rho(j)
        if v in seen: return seen[v], j
        seen[v] = j
    return None
