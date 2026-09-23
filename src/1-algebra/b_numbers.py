"""
b_numbers.py — block B: the framed numbers, the charts and the horizon (EXACT; B3 CHART in exact rationals)
===========================================================================================================
Paper statements decided (Sections 4–5; ledger predicates 1:D2, 1:D4, 1:D6, 1:E2, 1:F1, 1:V1):

  B1  def:integers (1:D2)          the window W_H = {|z| ≤ H}: z ↦ z mod p injective iff 2H < p; sums read back
                                   iff 4H < p; products read back whenever 2H² < p (sufficient; the product set is
                                   sparse, so the bound is not sharp) — swept over every H
  B2  thm:scale-periodicity (1:D4) the residue grids G_n = (x g^{−n})_x are (p−1)-periodic in n; the rational
                                   grids (x/g^n) with g lifted to Z are not
  B3  prop:r-rationals, thm:approx the chart of the grid [chart]: every r with |r| ≤ H g^{−n} lies within 1/(2gⁿ)
      (1:D6)                       of some x/gⁿ, x ∈ W_H (exact rationals); at (13, 2) no grid point of step ≤ 1/8
                                   lies within 1/16 of 33/10 — range and resolution trade off at fixed window
  B4  prop:Cp-field (1:E2)         F_p[X]/(X²+1) has zero divisors on the shell ((u+X)(u−X) = 0, factors nonzero);
                                   X²+1 has no root, hence the quotient is a field, exactly for p ≡ 3 (mod 4)
  B5  thm:no-south-pole (1:F1)     2s = 0 ⇒ s = 0 on every odd prime; 2·(2κ+1) = 1: the half-turn 2⁻¹ = 2κ+1
  B6  (1:V1)                       the Euclidean step count against the bound k ≤ ⌊log₂ p⌋+1 (lem:euclid-bound):
                                   p = 59 (55, 34) needs 7 > 6; p = 1009 (987, 610) needs 13 > 10; first excess at 59
"""
from fractions import Fraction
try:
    from .algcommon import check, SHELLS, CONTROLS, primitive_roots, kappa, sqrt_neg_one, is_prime
except ImportError:                       # run in place (python3 b_numbers.py)
    from algcommon import check, SHELLS, CONTROLS, primitive_roots, kappa, sqrt_neg_one, is_prime

def run():
    print("block B — the framed numbers, the charts and the horizon")

    # B1 — the window law, the three thresholds as iff over every H
    ok, det = True, []
    for p in [13, 17, 29]:
        for H in range(1, p):
            W = range(-H, H + 1)
            inj = len({z % p for z in W}) == len(W)
            sums = len({(x + y) % p for x in W for y in W}) == len({x + y for x in W for y in W})
            prods = len({(x * y) % p for x in W for y in W}) == len({x * y for x in W for y in W})
            ok &= (inj == (2 * H < p)) and (sums == (4 * H < p)) and ((2 * H * H < p) <= prods)   # products: sufficient, not necessary (the product set is sparse)
        det.append(f"p={p}: H = 1..{p-1} swept")
    # predicate 1:D2
    check("B1", "z ↦ z mod p injective on W_H iff 2H < p; sums read back iff 4H < p; products read back whenever 2H² < p", ok, "; ".join(det))

    # B2 — scale-periodicity: in the field yes, in Q no
    ok, det = True, []
    for p, g in [(13, 11), (13, 2), (17, 3), (29, 2)]:
        assert g in primitive_roots(p)
        grid = lambda n: tuple((x * pow(g, -n, p)) % p for x in range(p))
        ok &= all(grid(n) == grid(n + p - 1) for n in range(2 * (p - 1)))
        ok &= all(grid(n) != grid(n + d) for n in range(p - 1) for d in range(1, p - 1))   # exact period p−1
        qgrid = lambda n: tuple(Fraction(x, g ** n) for x in range(p))
        ok &= all(qgrid(n) != qgrid(n + p - 1) for n in range(3))
        det.append(f"({p},{g}): period {p-1} in F_p, none in Q")
    # predicate 1:D4
    check("B2", "G_n = (x g^{−n})_x is (p−1)-periodic in the field, with exact period p−1; the rational grids x/gⁿ are not periodic",
          ok, "; ".join(det))

    # B3 — the chart of the grid: the trade-off holds; its range at (13, 2)
    ok, det = True, []
    p, g, H = 13, 2, 12
    for n in range(0, 8):
        step = Fraction(1, g ** n)
        for num in range(-40, 41):                                    # r = num/8 · H g^{−n}, a sample within the range
            r = Fraction(num, 40) * H * step
            x = round(r / step)                                        # x = round(r gⁿ), |x| ≤ H
            ok &= (abs(x) <= H) and (abs(r - x * step) <= step / 2)
    r, tol = Fraction(33, 10), Fraction(1, 16)
    near = [(x, n) for n in range(3, 13) for x in range(p) if abs(Fraction(x, g ** n) - r) < tol]
    ok &= (near == []) and all(Fraction(x, g ** n) <= Fraction(3, 2) for n in range(3, 13) for x in range(p))
    best = min((abs(Fraction(x, g ** n) - r), x, n) for n in range(13) for x in range(p))
    ok &= (best[1:] == (7, 1) and best[0] == Fraction(1, 5))
    det.append(f"trade-off on {8*81} sampled reals at (13,2), H=12; range: no x/2^n (n ≥ 3, x < 13) within 1/16 of 33/10, best 7/2 at error 1/5")
    check("B3", "|r| ≤ H g^{−n} ⇒ some x/gⁿ, x ∈ W_H, within 1/(2gⁿ); at (13, 2) no point of step ≤ 1/8 within 1/16 of r = 33/10: range and resolution trade off at fixed window",
          ok, "; ".join(det), kind="CHART")

    # B4 — the complex chart is not an extension: zero divisors iff −1 is a square
    ok, det = True, []
    for p in [5, 13, 17, 29, 37]:
        u = sqrt_neg_one(p)[0]
        # in F_p[X]/(X²+1): elements a + bX, product (a+bX)(c+dX) = (ac − bd) + (ad + bc)X
        mul = lambda A, B: ((A[0] * B[0] - A[1] * B[1]) % p, (A[0] * B[1] + A[1] * B[0]) % p)
        ok &= (mul((u, 1), ((-u) % p, 1)) == (0, 0)) and (u, 1) != (0, 0) and ((-u) % p, 1) != (0, 0)
        det.append(f"p={p}: (u+X)(u−X)=0 with u={u}")
    for p in CONTROLS:
        ok &= (sqrt_neg_one(p) == [])                                    # X²+1 irreducible: the quotient is the field F_{p²}
        mul = lambda A, B: ((A[0] * B[0] - A[1] * B[1]) % p, (A[0] * B[1] + A[1] * B[0]) % p)
        elems = [(a, b) for a in range(p) for b in range(p) if (a, b) != (0, 0)]
        ok &= all(mul(A, B) != (0, 0) for A in elems for B in elems)    # no zero divisors
    # predicate 1:E2
    check("B4", "F_p[X]/(X²+1) has zero divisors on the shell (p ≡ 1 mod 4); it is a field exactly when p ≡ 3 (mod 4)",
          ok, "; ".join(det) + f"; fields at p ∈ {CONTROLS} (no zero divisors, exhaustive)")

    # B5 — no element of additive order two; the half-turn
    ok, det = True, []
    for p in [q for q in range(3, 200) if is_prime(q)]:
        ok &= ([s for s in range(p) if (2 * s) % p == 0] == [0])
        if p % 4 == 1:
            k = kappa(p)
            ok &= ((2 * (2 * k + 1)) % p == 1) and (2 * k + 1 == (p + 1) // 2)
    # predicate 1:F1
    check("B5", "2s = 0 ⇒ s = 0 for every odd prime < 200; on the shell 2⁻¹ = 2κ+1 = (p+1)/2, the residue past the antipode", ok, "primes 3..199")

    # B6 — the Euclidean step count against the bound ⌊log₂ p⌋+1 (recorded under V1)
    def steps(a, b):
        k = 0
        while b:
            a, b = b, a % b
            if b: k += 1
        return k
    fib = [1, 1]
    while fib[-1] < 2000: fib.append(fib[-1] + fib[-2])
    first = None
    for p in [q for q in range(5, 2000) if is_prime(q)]:
        worst = max(steps(fib[i + 1], fib[i]) for i in range(1, len(fib) - 1) if fib[i + 1] < p)
        if worst > p.bit_length():
            first = p; break
    ok = (steps(55, 34) == 7 and (59).bit_length() == 6 and steps(987, 610) == 13 and (1009).bit_length() == 10 and first == 59)
    ok &= (fib[3] == 3 and fib[3] < 2 ** 2)                               # F_4 = 3 < 2^{4−2}: the Fibonacci bound 2^{k−2} does not hold at k = 4
    check("B6", "the Euclidean step count against ⌊log₂p⌋+1: (55,34) needs 7 > ⌊log₂59⌋+1 = 6; (987,610) needs 13 > 10; first excess at p = 59; F_4 = 3 < 4",
          ok, "a ≥ b convention, consecutive Fibonacci pairs below p")

if __name__ == "__main__":
    import algcommon
    run(); algcommon.summary(write=False)
