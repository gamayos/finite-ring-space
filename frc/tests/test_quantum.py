"""The quantum theme's python (frc/quantum.py; task LM28): each value computed two ways, and the master's block file
quantum.py green, its markers on its deciding checks."""
import unittest
from math import gcd, lcm

from frc.quantum import joint_period, orbits, offset, reach, root_of_unity, character_sums


class QuantumTest(unittest.TestCase):
    def test_joint_period(self):
        for a in range(1, 25):
            for b in range(1, 25):
                self.assertEqual(joint_period([a, b]), lcm(a, b))
                self.assertEqual(joint_period([a, b]) * gcd(a, b), a * b)

    def test_orbits(self):
        for a in range(1, 13):
            for b in range(1, 13):
                g = gcd(a, b)
                orbs = orbits(a, b)
                self.assertEqual(len(orbs), g)
                for o in orbs:
                    x, y = o[0]
                    for x2, y2 in o: self.assertIsNotNone(reach(x, y, x2, y2, a, b))
                    self.assertEqual({offset(u, v, g) for u, v in o}, {offset(x, y, g)})

    def test_dephasing(self):
        q = 61                                   # 60 = lcm(4, 6, 10, 12, 15, 20, …)
        for N in (4, 6, 10, 12, 15):
            w = root_of_unity(q, N)
            self.assertEqual(pow(w, N, q), 1)
            self.assertTrue(all(pow(w, d, q) != 1 for d in range(1, N)))
        for a, b in [(4, 6), (3, 5), (6, 10)]:
            for moved, s in character_sums(q, a, b, lcm(a, b)):
                self.assertEqual(s, 0 if moved else lcm(a, b) % q)


class MasterQuantumTest(unittest.TestCase):
    def test_block_file(self):
        from frc.ledgers.master import quantum as Q
        self.assertTrue(Q.R.verify_all())
        marks = Q.R.markers()
        for lab in Q.R.predicates: self.assertIn(lab, marks)
        self.assertEqual(sorted(Q.PROOFS), sorted(Q.LEAN))
        self.assertEqual(Q.BLOCK, "F")


if __name__ == "__main__":
    unittest.main()
