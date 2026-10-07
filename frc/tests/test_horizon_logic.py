"""The horizon and logic themes' python (frc/horizon.py, frc/logic.py; task LM26): each value computed two ways, and the
master's block files horizon.py and logic.py green, their markers on their deciding checks."""
import random
import unittest
from itertools import product

from frc import arith
from frc.foundation import drive
from frc.horizon import zeta, mode_coeffs, expand, shift, fixed_points, readout, trace
from frc.logic import fval, table, free_vars, random_formula, random_structure, successor_counterexample

SHELLS = [p for p in range(5, 120) if p % 4 == 1 and arith.is_prime(p)]


class HorizonTest(unittest.TestCase):
    def test_zeta(self):
        for p in SHELLS:
            g = drive(p)
            for k in range(1, p):
                self.assertEqual(zeta(p, k), sum(pow(g, j * k, p) for j in range(p - 1)) % p)    # over the powers of g
            self.assertEqual(zeta(p, p - 1), p - 1)

    def test_expansion(self):
        rng = random.Random(5)
        for p in SHELLS[:8]:
            g, n = drive(p), p - 1
            v = [rng.randrange(p) for _ in range(n)]
            c = mode_coeffs(p, g, v)
            self.assertEqual([expand(p, g, c, j) for j in range(n)], v)
            self.assertEqual(c[0], (-sum(v)) % p)                                     # the constant mode: −Σ v
            e = [1 if j == 0 else 0 for j in range(n)]                               # the indicator of x = 1: c_k = −1
            self.assertEqual(mode_coeffs(p, g, e), [p - 1] * n)

    def test_shift_and_readout(self):
        for p in SHELLS:
            g, n = drive(p), p - 1
            for r in range(0, 2 * n + 1, 3):
                self.assertEqual(len(fixed_points(p, g, r)), n if r % n == 0 else 0)
                self.assertEqual(sorted(shift(p, g, r, x) for x in range(1, p)), list(range(1, p)))   # a permutation
            self.assertEqual({trace(p, readout(p, t)) for t in range(p)}, {1})
            self.assertEqual(2 * readout(p, 0)[0] % p, 1)


class LogicTest(unittest.TestCase):
    def test_two_evaluators(self):
        rng = random.Random(7)
        for m in (1, 2, 3):
            M = random_structure(rng, m)
            for _ in range(150):
                k = rng.randrange(1, 3)
                phi = random_formula(rng, 4, k)
                self.assertLessEqual(free_vars(phi), k)
                T = table(M, phi, k)
                for a in product(range(m), repeat=k):
                    self.assertEqual(fval(M, a, phi), a in T)
                    self.assertNotEqual(fval(M, a, phi), fval(M, a, ("neg", phi)))

    def test_no_finite_successor(self):
        for n in range(1, 6):
            self.assertIsNone(successor_counterexample(n))


class MasterBlockZTest(unittest.TestCase):
    def test_block_files(self):
        from frc.ledgers.master import horizon as H, logic as L
        for F in (H, L):
            self.assertTrue(F.R.verify_all())
            marks = F.R.markers()
            for lab in F.R.predicates: self.assertIn(lab, marks)
            self.assertEqual(sorted(F.PROOFS), sorted(F.LEAN))
            self.assertEqual(F.BLOCK, "Z")


if __name__ == "__main__":
    unittest.main()
