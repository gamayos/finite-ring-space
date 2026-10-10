"""frc/drift.py (the gravity theme; 21-gravity): each exact face computed a second way — the register by direct residue
arithmetic, the defect's period by brute return, the locked sum by enumeration, the series against closed forms."""
import random
import unittest
from fractions import Fraction
from math import gcd

from frc import arith
from frc import drift as D


class RegisterTest(unittest.TestCase):
    def test_calibration_and_register(self):
        for p in (5, 13, 17, 29, 37, 1373):
            k = (p - 1) // 4
            self.assertTrue(D.calibration(p))
            self.assertTrue(all(D.newton_register(p)))
            self.assertEqual(2 * (2 * k) % p, p - 1)                       # 2G = −1 directly
            self.assertEqual(pow(2, p - 2, p), 2 * k + 1)                  # c² = 2⁻¹
            g = arith.primitive_root(p)
            self.assertTrue(all(D.hbar_root(p, g)))
            self.assertEqual(pow(g, 2 * k, p), p - 1)                      # ħ² = g^{2κ} = −1
        self.assertFalse(D.calibration(7))                                 # not 1 mod 4: (4κ)² = 4 ≠ 1 with κ = 1

    def test_channel(self):
        for p in (5, 13, 17, 29, 37, 41):
            self.assertTrue(D.channel_q4(p))
            self.assertEqual(gcd(p - 1, 2 * (p + 1)), 4)                   # the gcd form of the channel
        self.assertFalse(D.channel_q4(7))


class DefectTest(unittest.TestCase):
    def test_period_by_brute_return(self):
        rng = random.Random(1)
        for _ in range(100):
            nA, nB = rng.randint(2, 30), rng.randint(2, 30)
            L, q, a, T = D.defect(nA, nB, rng.randint(0, nA - 1), rng.randint(0, nB - 1))
            self.assertEqual(L * q, nA * nB)
            self.assertEqual(D.first_return(L // q, a), T)
            self.assertEqual(T, next(t for t in range(1, L // q + 1) if (t * a) % (L // q) == 0))
        self.assertEqual(D.defect(60, 28, 1, 1), (420, 4, 8, 105))

    def test_pair_tally_and_locked_sum(self):
        for p in (13, 17):
            self.assertTrue(all(D.pair_tally_identity(p, z) for z in range(1, p)))
        self.assertEqual(D.locked_sum(4, 3), (9, 3))
        self.assertEqual(D.locked_sum(5, 2), (4, 2))

    def test_gauss_and_compression(self):
        J = [[0, 2, -1], [-2, 0, 3], [1, -3, 0]]
        self.assertTrue(D.gauss_law(J, {0}))
        self.assertTrue(D.gauss_law(J, {0, 1}))
        self.assertTrue(D.compression_identity(5, {0, 1}))


class SeriesTest(unittest.TestCase):
    def test_exp_against_factorials(self):
        from math import factorial
        e = D.Series.exp(D.Series.var(7))
        self.assertEqual(e.c, [Fraction(1, factorial(k)) for k in range(7)])
        U = D.Series.var(6)
        self.assertEqual((D.Series.exp(U) * D.Series.exp(-U)).c, [1, 0, 0, 0, 0, 0])
        self.assertEqual(((1 + U) / (1 + U)).c, [1, 0, 0, 0, 0, 0])

    def test_pn_faces(self):
        pn = D.pn_coefficients(5)
        self.assertTrue(pn["ok"]); self.assertEqual((pn["beta"], pn["gamma"]), (1, 1))
        self.assertTrue(D.two_body_1pn(3))
        self.assertTrue(D.pn_orbit_inputs(5)["ok"])
        self.assertEqual(D.static_profile_coefficients(2), [Fraction(1), Fraction(1, 30)])
        self.assertTrue(D.scale_invariant_exponent())
        self.assertTrue(D.dilution(7, 11))

    def test_roots_and_words(self):
        ok, eta = D.registration_root(Fraction(3, 5), Fraction(4, 5))
        self.assertTrue(ok); self.assertEqual(eta, Fraction(1, 3))
        self.assertTrue(D.chebyshev_weight(5, 2, Fraction(1, 2)))
        self.assertTrue(D.christoffel(3, 8))
        self.assertEqual(D.largest_remainder([Fraction(1, 2), Fraction(1, 3), Fraction(1, 6)], 7)[0], [4, 2, 1])
        self.assertTrue(D.ledger_identity(2, Fraction(5, 3), 4, 9))
        for p in (13, 17):
            nu = next(v for v in range(2, p) if pow(v, (p - 1) // 2, p) == p - 1)
            self.assertTrue(D.frobenius_trace(p, nu, 5, 3, 4))

    def test_binding_and_fold(self):
        self.assertEqual(D.binding(N=4, m1=2, m2=3), (True, True, True, True))
        self.assertTrue(D.fold_return(17, 8, 4))


if __name__ == "__main__":
    unittest.main()
