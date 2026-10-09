"""The chart theme's python (frc/chart.py; task LM30): each certified bracket contains its floating-point reading and
is narrow, the brackets agree with a second rational method, and the master's chart file is green, its markers on its
deciding checks."""
import math
import unittest
from fractions import Fraction as Q

from frc import chart as C


class ChartTest(unittest.TestCase):
    def test_pi(self):
        lo, hi = C.pi_bracket()
        self.assertTrue(lo < hi and hi - lo < Q(1, 10 ** 15))
        self.assertLess(abs(float(lo) - math.pi), 1e-15)
        lo2, hi2 = C.pi_bracket(4)                       # a coarser bracket contains the finer one
        self.assertTrue(lo2 <= lo and hi <= hi2)

    def test_exp(self):
        for x in (Q(0), Q(1, 3), Q(1), Q(7, 3)):
            lo, hi = C.exp_bracket(x)
            self.assertTrue(lo <= hi and hi - lo < Q(1, 10 ** 15))
            self.assertLess(abs(float(lo) - math.exp(float(x))), 1e-12)
        lo, hi = C.exp_bracket(Q(1), 8)                  # e: the bracket of degree 8 contains Mathlib's nine places
        self.assertTrue(lo < Q("2.7182818286") and Q("2.7182818283") < hi)

    def test_readings(self):
        for b, f in ((C.tanh_octant_bracket(), C.tanh_octant()), (C.omega_lambda_bracket(), C.omega_lambda()),
                     (C.locus_bracket(), C.locus()), (C.hubble_bracket(), C.hubble()), (C.floor_bracket(), C.floor()),
                     (C.tilt_bracket(), -C.tilt())):
            self.assertTrue(b[0] < b[1] and b[1] - b[0] < abs(b[0]) / 10 ** 12)
            self.assertLess(abs(f - float(b[0])), abs(f) * 1e-12)

    def test_inversion(self):
        # the rival chart's age identity lands on π/4 exactly at tanh²(3π/8), and its inverse returns it
        self.assertAlmostEqual(C.lcdm_age(C.omega_lambda()), math.pi / 4, places=13)
        self.assertAlmostEqual(math.tanh(3 / 2 * math.pi / 4) ** 2, C.omega_lambda(), places=15)

    def test_running(self):
        self.assertEqual(C.e_of_z(0, Q(7, 10)), 1)
        self.assertAlmostEqual(C.tully_fisher_shift(1, 0.7) ** 4, C.e_of_z(1, 0.7), places=12)


class MasterChartTest(unittest.TestCase):
    def test_block_file(self):
        from frc.ledgers.master import chart as L
        self.assertTrue(L.R.verify_all())
        marks = L.R.markers()
        for lab in L.R.predicates: self.assertIn(lab, marks)
        self.assertEqual(sorted(L.CHART), sorted(L.LEAN))
        self.assertEqual(L.BLOCK, "ALP")                 # A7 (the scale import; A8 until the relabel of 9 October) bound since the push of 8 October 2026
        self.assertFalse(hasattr(L, "PROOFS"))           # the chart rows are not bound as theorem rows (gate G08)


if __name__ == "__main__":
    unittest.main()
