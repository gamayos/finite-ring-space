"""frc.arith, each value computed two ways (task LM15): the function against an independent brute force or a second
algorithm, on every small case and on fixed large ones."""
import unittest
from math import gcd, isqrt
from frc import arith as A

N_SMALL = 20_000


def trial_prime(n):
    if n < 2: return False
    return all(n % d for d in range(2, isqrt(n) + 1))


def trial_factor(n):
    out, d = {}, 2
    while d * d <= n:
        while n % d == 0: out[d] = out.get(d, 0) + 1; n //= d
        d += 1
    if n > 1: out[n] = out.get(n, 0) + 1
    return out


def brute_order(a, n):
    x, k = a % n, 1
    while x != 1 % n: x = x * a % n; k += 1
    return k


class Primality(unittest.TestCase):
    def test_small_against_trial_division(self):
        for n in range(-5, N_SMALL): self.assertEqual(A.is_prime(n), trial_prime(n), n)

    def test_strong_pseudoprimes_are_composite(self):
        # strong pseudoprimes to bases 2; 2 and 3; 2, 3 and 5; …; the first 12 primes (OEIS A014233), and Carmichael numbers
        for n in (2047, 1373653, 25326001, 3215031751, 2152302898747, 3474749660383, 341550071728321,
                  3825123056546413051, 318665857834031151167461, 561, 1105, 1729, 2465, 2821, 6601, 8911):
            self.assertFalse(A.is_prime(n), n)
            self.assertNotEqual(A.factorize(n), {n: 1})

    def test_known_primes(self):
        for p in (2408561, 30089, 233, 2 ** 31 - 1, 2 ** 61 - 1, 10 ** 18 + 9, 10 ** 24 + 7, 3317044064679887385961813):
            self.assertTrue(A.is_prime(p), p)

    def test_range_is_stated(self):
        self.assertRaises(ValueError, A.is_prime, 2 ** 89 - 1)                 # a prime above the range: no proof stated
        self.assertFalse(A.is_prime(A.PRIME_RANGE + 2))                         # a small factor decides at any size
        self.assertRaises(ValueError, A.factorize, 3 * (2 ** 89 - 1))

    def test_laboratory_carrier(self):
        om = 2408561; s = (om - 1) // 4
        self.assertTrue(A.is_prime(om)); self.assertEqual((s % 2, s % 3), (0, 1))


class Factorisation(unittest.TestCase):
    def test_small_against_trial_division(self):
        for n in range(1, N_SMALL): self.assertEqual(A.factorize(n), trial_factor(n), n)

    def test_large_products(self):
        cases = [(2 ** 31 - 1) * (2 ** 61 - 1), 1000003 * 1000033 * 999983, (10 ** 9 + 7) ** 2 * 10007, 2 ** 40 * 3 ** 7 * 2408561,
                 600851475143, 2 ** 67 - 1, 10 ** 18 + 1]
        for n in cases:
            f = A.factorize(n)
            prod = 1
            for p, e in f.items():
                self.assertTrue(trial_prime(p) if p < 10 ** 12 else A.is_prime(p)); prod *= p ** e
            self.assertEqual(prod, n)
        self.assertEqual(A.factorize(2 ** 67 - 1), {193707721: 1, 761838257287: 1})        # Cole, 1903

    def test_phi_and_carmichael_against_counting(self):
        for n in range(1, 600):
            units = [a for a in range(n) if gcd(a, n) == 1] if n > 1 else [0]
            self.assertEqual(A.phi(n), len(units), n)
            lam = 1
            for a in units:
                k = brute_order(a, n) if n > 1 else 1
                lam = lam * k // gcd(lam, k)
            self.assertEqual(A.carmichael(n), lam, n)


class Orders(unittest.TestCase):
    def test_order_against_brute_force(self):
        for n in range(2, 400):
            for a in range(1, n):
                if gcd(a, n) == 1: self.assertEqual(A.order(a, n), brute_order(a, n), (a, n))
        self.assertRaises(ValueError, A.order, 4, 8)

    def test_primitive_roots_against_brute_force(self):
        for n in range(2, 700):
            units = {a for a in range(1, n) if gcd(a, n) == 1}
            gens = sorted(g for g in units if {pow(g, k, n) for k in range(1, len(units) + 1)} == units)
            if gens:
                self.assertEqual(A.primitive_root(n), gens[0], n)
                self.assertEqual(A.primitive_roots(n), gens, n)
                self.assertTrue(all(A.is_primitive_root(g, n) for g in gens))
            else:
                self.assertRaises(ValueError, A.primitive_root, n)

    def test_shell_drives(self):
        # the drive of the shells the corpus names: 2 on 13, 3 on 17, 2 on 29, 3 on 233; the laboratory Carrier's least root
        for p, g in ((13, 2), (17, 3), (29, 2), (233, 3)): self.assertEqual(A.primitive_root(p), g)
        g = A.primitive_root(2408561)
        self.assertEqual(A.order(g, 2408561), 2408560)


class Residues(unittest.TestCase):
    PRIMES = [p for p in range(3, 2000) if trial_prime(p)]

    def test_legendre_against_squares_and_jacobi(self):
        for p in self.PRIMES:
            squares = {x * x % p for x in range(1, p)}
            for a in range(-3, p + 3):
                want = 0 if a % p == 0 else (1 if a % p in squares else -1)
                self.assertEqual(A.legendre(a, p), want, (a, p))
                self.assertEqual(A.jacobi(a, p), want, (a, p))

    def test_jacobi_multiplicative_in_n(self):
        for m in range(1, 120, 2):
            for n in range(1, 120, 2):
                for a in range(-4, 40):
                    self.assertEqual(A.jacobi(a, m * n), A.jacobi(a, m) * A.jacobi(a, n), (a, m, n))

    def test_sqrt_mod_and_nonresidue(self):
        for p in self.PRIMES:
            z = A.nonresidue(p)
            self.assertEqual(z, min(a for a in range(2, p) if pow(a, (p - 1) // 2, p) == p - 1))
            for a in range(p):
                if a == 0 or A.legendre(a, p) == 1:
                    r = A.sqrt_mod(a, p)
                    self.assertEqual(r * r % p, a); self.assertLessEqual(r, p - r if r else 0)
                else:
                    self.assertRaises(ValueError, A.sqrt_mod, a, p)

    def test_quarter_turn_on_the_laboratory_carrier(self):
        om = 2408561; i = A.sqrt_mod(om - 1, om)
        self.assertEqual(i * i % om, om - 1)


class Remainders(unittest.TestCase):
    def test_inverse_and_crt(self):
        for n in range(2, 300):
            for a in range(n):
                if gcd(a, n) == 1: self.assertEqual(a * A.inverse(a, n) % n, 1)
                else: self.assertRaises(ValueError, A.inverse, a, n)
        for m in range(1, 40):
            for n in range(1, 40):
                for x in range(0, m * n, 7):
                    r = A.crt([x % m, x % n], [m, n]); L = m * n // gcd(m, n)
                    self.assertEqual(r, x % L)

    def test_valuation(self):
        for n in range(1, 3000):
            for p in (2, 3, 5):
                k = A.valuation(n, p)
                self.assertEqual(n % p ** k, 0); self.assertNotEqual(n % p ** (k + 1), 0)


if __name__ == "__main__":
    unittest.main()
