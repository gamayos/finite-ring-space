"""The foundation and carrier themes' python (frc/foundation.py, frc/carrier.py; task LM22): each value computed two
ways, by the theme's generator-free construction and by search, on every prime below a bound; and the master's
Carrier block file green, its markers on its deciding checks."""
import unittest
from frc import arith
from frc.foundation import half_power, quarter_turn, quarter_turns, square_roots, fermat_holds
from frc.carrier import capacity, register, octant, tsirelson, triality_roots, horizon, quarter_root, coherence

PRIMES = [p for p in range(3, 1200) if arith.is_prime(p)]


class FoundationTest(unittest.TestCase):
    def test_half_power_and_quarter_turn(self):
        for p in PRIMES:
            a = half_power(p)
            self.assertEqual(a, min(x for x in range(1, p) if not square_roots(x, p)))     # the least non-square, by search
            if p % 4 == 1:
                h = quarter_turn(p); roots = quarter_turns(p)
                self.assertIn(h, roots); self.assertEqual(sorted(roots), sorted({h, p - h}))
            else:
                self.assertEqual(quarter_turns(p), []); self.assertRaises(ValueError, quarter_turn, p)
        self.assertRaises(ValueError, half_power, 9)

    def test_fermat(self):
        for p in PRIMES[:60]: self.assertTrue(fermat_holds(p))
        self.assertFalse(fermat_holds(15))


class CarrierTest(unittest.TestCase):
    def test_register(self):
        for Om in (p for p in PRIMES if p % 4 == 1):
            S = capacity(Om); r = register(S)
            self.assertEqual(r["c2"] * 2 % Om, 1); self.assertEqual((r["G"] + r["c2"]) % Om, 0)
            self.assertEqual(r["hbar"] ** 2 % Om, Om - 1); self.assertEqual((r["hbar"] + r["h"]) % Om, 0)
            roots = square_roots(r["c2"], Om)
            self.assertEqual(bool(roots), S % 2 == 0)                                           # c exists iff S even, by search
            if S % 2 == 0:
                self.assertIn(r["c"], roots)
                self.assertEqual(r["kB"] * r["c"] % Om, r["hbar"]); self.assertEqual(r["kB"] ** 2 % Om, Om - 2)
            else:
                self.assertIsNone(r["c"]); self.assertIsNone(r["kB"])

    def test_octant_and_triality(self):
        for Om in PRIMES:
            z = octant(Om)
            eight = [x for x in range(1, Om) if pow(x, 8, Om) == 1 and pow(x, 4, Om) != 1]    # the elements of order eight, by search
            self.assertEqual(z is not None, bool(eight))
            if z is not None:
                self.assertIn(z, eight); self.assertEqual(tsirelson(z, Om), 2)
            if Om > 3: self.assertEqual(bool(triality_roots(Om)), Om % 3 == 1)

    def test_windows(self):
        for n in range(1, 3000):
            self.assertEqual(horizon(n), max(x for x in range(n + 1) if x * x <= n))
            self.assertEqual(quarter_root(n), max(x for x in range(n + 1) if x ** 4 < n) if n > 0 else 0)
            self.assertEqual(coherence(n), max(x for x in range(n + 1) if x * x < n))


class MasterCarrierTest(unittest.TestCase):
    def test_block_file(self):
        from frc.ledgers.master import carrier as L
        self.assertTrue(L.R.verify_all())
        marks = L.R.markers()
        for lab, pid in L.R.predicates.items():
            self.assertIn(lab, marks)
        self.assertEqual(sorted(L.PROOFS), sorted(L.LEAN))                                   # every bound row has its key in the key file


if __name__ == "__main__":
    unittest.main()
