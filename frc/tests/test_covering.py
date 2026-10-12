"""frc/covering.py (the subject theme; 38-s13): the sky, the flow and the covering computed a second way — the labels
by direct residue arithmetic, the fibre product by the Chinese remainder theorem, the tick arithmetic against signed
differences, the covering against the slot rule written out, the parity decider against the enumerated covering."""
import unittest
from fractions import Fraction
from math import gcd

from frc import covering as CV


class SkyTest(unittest.TestCase):
    def test_labels(self):
        for k in range(13):
            for t in range(40):
                self.assertEqual(CV.label(13, 2, k, t), k * pow(2, (t - k) % 12, 13) % 13)
        self.assertEqual(len(CV.node_field(13)), 72)
        self.assertEqual(len(CV.node_field(17)), 4 * 2 * 16)

    def test_fibre_product(self):
        for m, n in ((12, 8), (12, 232), (6, 10), (4, 6)):
            d = gcd(m, n)
            cnt, L, inj, eq = CV.fibre_product(m, n, d)
            self.assertEqual(cnt, m * n // d); self.assertEqual(L, m * n // d); self.assertTrue(inj and eq)
        self.assertEqual(CV.composed_rate(13, 233), Fraction(61, 696))
        self.assertEqual(CV.pair_space(13, 233)[0], 696)


class FlowTest(unittest.TestCase):
    def test_tick(self):
        for n in (12, 24, 232, 464):
            for k in range(n):
                for b in range(0, 3 * n, 7):
                    self.assertEqual(CV.tick(n, k, b), (k - b) % n)
            self.assertTrue(all(CV.stations(n, k) == (0, n // 2) for k in range(n)))
            self.assertTrue(all(all(CV.half_turn(n // 2, x)) for x in range(n)))

    def test_stations_and_step(self):
        self.assertEqual(CV.capacity_stations(13), [1, 2, 3, 10, 11, 12])
        self.assertEqual(CV.capacity_stations(17), [1, 2, 3, 4, 13, 14, 15, 16])
        step, rhs, eq, den = CV.step_law()
        self.assertTrue(eq); self.assertEqual(den, 9048); self.assertEqual(step, Fraction(9029, 9048))
        self.assertEqual(CV.tower_period(13, 2)[:2], (12, True))
        self.assertEqual(CV.quarter_classes(13, 2)[0][1], [2, 5, 6])


class CoveringTest(unittest.TestCase):
    def test_slot_rule(self):
        p = 13
        for m in range(1, p):
            for t in CV.capacity_stations(p):
                u = m * t
                w, r = divmod(u, p)
                row = r if w % 2 == 0 else p - r                     # the tent fold written out
                self.assertEqual(CV.tent(p, u), row if r else (0 if w % 2 == 0 else p))
                s, e, k = CV.slot(p, m, 0, t)
                self.assertEqual((s, e), (min(t, p - t) - 1, w % 2))

    def test_covering_law(self):
        for p in (5, 13, 17, 29):
            law = CV.covering_law(p)
            k = (p - 1) // 4
            self.assertTrue(law["complete"] and law["law"] and law["position"] and law["balance"])
            self.assertEqual((law["nodes"], law["slots"]), (2 * k * (p - 1), 4 * k * (p - 1)))
            self.assertTrue(CV.reflection_identity(p) and CV.decider(p))
        self.assertTrue(CV.parity_table())
        fl = CV.family_law(13)
        self.assertTrue(fl["M0"] and fl["M3"] and fl["passages5"] and fl["drawn_iff_m_ge_4"])

    def test_momentum_dual(self):
        self.assertEqual([r for _, r, _ in CV.momentum_dual(13, 5)], [5, 10, 11, 2, 3, 8])
        self.assertEqual(CV.passages(13, 5), [Fraction(13, 5), Fraction(52, 5)])
        self.assertEqual(CV.ramification(13, 2), (Fraction(13, 4), True))
        self.assertEqual(CV.ramification(13, 1), (Fraction(13, 2), False))
        self.assertTrue(all(CV.fusion()))


if __name__ == "__main__":
    unittest.main()
