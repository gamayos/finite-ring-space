"""
chart_localization.py  --  the description-length vs counting-distance gap.

Supports Definition (localizing chart), Proposition (existence is free; the
selector is the content) and the lucky-chart Remark of Section 5 of the
P-vs-NP paper.  Exact, deterministic, no randomness.

Claim exhibited.  In the scale chart x = g^m of F_P the discrete logarithm m
is the *counting distance* from the identity to x along the orbit (one step =
x -> g*x).  The map x |-> m is a bijection of F_P^x onto {1,...,P-1}; hence the
counting distance is spread uniformly up to P-1 = 2^ell - O(1), while the
witness m is *named* in ell = ceil(log2 P) bits.  Short to name (ell bits) is
not short to find (up to 2^ell counting steps).  The ascent g^m is O(ell) by
square-and-multiply.  This is exactly the gap that makes a localizing chart
exist for free (it is named by m) yet not be forward-selectable.
"""
import math


def generator(P):
    """Least primitive root mod P (P prime), by a direct orbit check."""
    for g in range(2, P):
        x, seen = 1, set()
        for _ in range(P - 1):
            x = (x * g) % P
            seen.add(x)
        if len(seen) == P - 1:
            return g
    raise RuntimeError("no generator found")


def report(P):
    g = generator(P)
    # counting distance to each element = its discrete log (orbit ordinal)
    x, dlog = 1, {}
    for k in range(1, P):
        x = (x * g) % P
        dlog.setdefault(x, k)
    # the counting distances are exactly a permutation of 1..P-1 (a bijection)
    assert sorted(dlog.values()) == list(range(1, P)), "dlog not a bijection"
    ell = math.ceil(math.log2(P))                  # bits to NAME a witness
    mean_count = sum(dlog.values()) / (P - 1)       # mean steps to FIND it
    max_count = max(dlog.values())                  # = P-1 = 2^ell - O(1)
    ascent_bits = sum(k.bit_length() for k in range(1, P)) / (P - 1)
    return g, ell, mean_count, max_count, ascent_bits


if __name__ == "__main__":
    print(f"{'P':>8} {'g':>4} {'ell=name bits':>14} {'mean find-steps':>16} "
          f"{'max find-steps':>15} {'ascent bits':>12}")
    for P in [101, 1009, 10007, 100003]:
        g, ell, mc, xc, ab = report(P)
        print(f"{P:>8} {g:>4} {ell:>14} {mc:>16.1f} {xc:>15} {ab:>12.1f}")
    print()
    print("find-steps ~ 2^ell  (exponential in input size ell);")
    print("name-bits and ascent ~ ell  (polynomial in input size).")
    print("dlog is a bijection onto the orbit ordinals 1..P-1: a witness's")
    print("coordinate is O(ell) bits, its counting distance is up to 2^ell.")
    print("Hence the localizing chart exists (named by the answer) but is not")
    print("forward-selectable -- short to name is not short to find.")
