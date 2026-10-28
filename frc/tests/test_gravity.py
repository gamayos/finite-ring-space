"""The gravity theme's python (frc/gravity.py; task LM27): each value computed two ways, and the master's block file
gravity.py green, its markers on its deciding checks."""
import unittest
from fractions import Fraction

from frc import arith
from frc.gravity import (squares, conic_points, sphere_points, sphere_brute, record, area, rate_mass, temperature,
                         response, merger_area)

SHELLS = [p for p in range(5, 60) if p % 4 == 1 and arith.is_prime(p)]


class GravityTest(unittest.TestCase):
    def test_squares(self):
        for p in SHELLS:
            r = squares(p)
            self.assertEqual(sum(r), p)
            self.assertEqual([r[v] for v in range(1, p)], [1 + arith.legendre(v, p) for v in range(1, p)])   # 1 + χ(v)

    def test_sphere(self):
        for p in SHELLS[:5]:
            for a in range(p):
                self.assertEqual(sphere_points(p, a), sphere_brute(p, a))
            k = (p - 1) // 4
            self.assertEqual(sphere_points(p, k * k % p), p * (p + 1))
            self.assertEqual(sphere_points(p, 0), p * p)

    def test_conic(self):
        for p in SHELLS:
            brute = [0] * p
            for x in range(p):
                for y in range(p): brute[(x * x + y * y) % p] += 1
            self.assertEqual([conic_points(p, c) for c in range(p)], brute)

    def test_thermo(self):
        for p in SHELLS:
            S, A, M = record(p), area(p), rate_mass(p)
            self.assertEqual(4 * S + 1, p * p)
            self.assertEqual(Fraction(S), Fraction(A, 4) * (1 - Fraction(1, p)))
            self.assertEqual(S, M * (M - 1))
            self.assertEqual(temperature(p), response(p) * (1 + Fraction(1, p)))
        for a in range(1, 40):
            for b in range(1, 40):
                self.assertEqual(merger_area(a, b), 2 * a * b)


class MasterGravityTest(unittest.TestCase):
    def test_block_file(self):
        from frc.ledgers.master import gravity as G
        self.assertTrue(G.R.verify_all())
        marks = G.R.markers()
        for lab in G.R.predicates: self.assertIn(lab, marks)
        self.assertEqual(sorted(set(G.PROOFS) | set(G.CHART)), sorted(G.LEAN))       # E14 is bound on Mathlib (CHART) since 16 October 2026
        for lab, libs in G.LEAN.items():
            self.assertEqual("core" in libs, lab in G.PROOFS, lab)
            self.assertEqual("ml" in libs, lab in G.CHART, lab)
        self.assertEqual(G.LEAN["E14"], "ml")
        self.assertEqual(G.CHART["E14"], ["FRC.Strong.eikonal_pair", "FRC.Strong.shadow_bracket"])
        self.assertEqual(G.BLOCK, "CE")                   # C21, the dilation rigidity theorem, since 20 October 2026
        self.assertIn("00:C21", G.PREDICATES)

    def test_dilation_rigidity(self):
        """The dilation rigidity theorem's exact pieces (frc/drift.py), each a second way."""
        from frc import drift as D
        from frc.foundation import drive
        from fractions import Fraction
        for p in (13, 29):
            g = drive(p); q4, i, sq, nrm, odd = D.quarter_channel(p, g)
            self.assertEqual((q4, sq, nrm, odd), (4, True, True, True))
            self.assertEqual(i, pow(g, (p - 1) - (p - 1) // 4, p))          # g^{−κ} = g^{p−1−κ}
            self.assertEqual(D.ppn_no_character(p), [(1, 0)])
            self.assertTrue(D.ppn_defect(p))
        c, efac, law, defect = D.composition_series(8)
        self.assertEqual(c, efac); self.assertTrue(law); self.assertEqual(defect, {(1, 1): Fraction(4)})
        self.assertEqual(c[3], Fraction(-1, 6))
        every, half, station, quarter = D.spinor_cover(13, 2)
        self.assertTrue(every and half and station and quarter)


if __name__ == "__main__":
    unittest.main()
