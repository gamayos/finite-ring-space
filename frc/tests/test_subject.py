"""The subject theme's python (frc/subject.py; task LM24): each value computed two ways, by the theme's helper and by a
second method (search, closed form or the other side of a theorem), on every prime p = 4κ + 1 below a bound; and the
master's Subject block file green, its markers on its deciding checks."""
import unittest
from frc import arith
from frc.extension import Ext
from frc.foundation import quarter_turns
from frc.subject import (frame, frames, euler, chirality, fold_image, fold_solutions, two_parts, channel,
                         projective_line, direction, torsor, boost_act)

SHELLS = [p for p in range(5, 800) if p % 4 == 1 and arith.is_prime(p)]


class SubjectTest(unittest.TestCase):
    def test_frame(self):
        for p in SHELLS:
            k, g, pi, i = frame(p)
            self.assertTrue(arith.is_primitive_root(g, p))                                    # by the factorisation of p − 1
            self.assertEqual((k, pi), ((p - 1) // 4, (p - 1) // 2))
            self.assertIn(i, quarter_turns(p))                                                # i² = −1, by search
        self.assertRaises(ValueError, frame, 7)

    def test_frames(self):
        for p in SHELLS[:20]:
            self.assertEqual(frames(p), arith.primitive_roots(p))
            self.assertEqual(len(frames(p)), arith.phi(p - 1))

    def test_euler_and_chirality(self):
        for p in SHELLS[:25]:
            g = frame(p)[1]
            for j in range(p):
                self.assertEqual(euler(g, j, p), pow(-1, j, p))                               # (−1)^j, closed form
            for g2 in frames(p):
                u = chirality(g, g2, p)
                self.assertEqual(pow(g, u, p), g2)
                self.assertEqual(arith.order(g2, p), p - 1)
            self.assertIsNone(chirality(g, 0, p))

    def test_fold(self):
        for p in SHELLS:
            k, g, _, _ = frame(p)
            img = fold_image(p, g)
            self.assertEqual(sorted(img), sorted(pow(g, 3 * k * r + 4 * s, p) for r in range(4) for s in range(k)))   # g^{3κr+4s}
            sols = fold_solutions(k)
            self.assertEqual(bool(sols), k % 2 == 1)
            for r, s in sols: self.assertEqual(pow(g, 3 * k * r + 4 * s, p), g)              # the solution folds to g itself

    def test_two_parts(self):
        for p in SHELLS[:40]:
            for Om in SHELLS[:40]:
                a, b, m, cover, car = two_parts(p, Om)
                self.assertEqual(2 ** a, (p - 1) & -(p - 1)); self.assertEqual(2 ** b, (Om - 1) & -(Om - 1))   # lowest set bit
                self.assertEqual(2 ** m * cover, car)

    def test_channel(self):
        for p in SHELLS:
            h = quarter_turns(p)[0]
            sign, q4 = channel(p, h)
            self.assertEqual(sign, [1, p - 1])
            self.assertEqual(sorted(q4), sorted({1, p - 1, h, p - h}))
            self.assertEqual(sorted(q4), sorted(x for x in range(1, p) if pow(x, 4, p) == 1))   # Fermat: x^{2(p+1)} = x⁴

    def test_torsor(self):
        for p in SHELLS[:12]:
            for nu in (arith.nonresidue(p), frame(p)[1]):
                K = Ext(p, nu)
                tors = {P: torsor(P, nu, p) for P in projective_line(p)}
                self.assertEqual(set(tors.values()), set(K.norm_one()))                       # onto the torus, by search
                for P, t in tors.items():
                    u = direction(P, nu, p)
                    self.assertEqual(t, K.mul(u, K.inv(K.conj(u))))                           # u/ū, the second form
                    self.assertEqual(boost_act(u, (0, 1), nu, p), P)                          # u_P carries the origin to P
                self.assertEqual((tors[(0, 1)], tors[(1, 0)]), ((1, 0), (p - 1, 0)))


class MasterSubjectTest(unittest.TestCase):
    def test_block_file(self):
        from frc.ledgers.master import subject as L
        self.assertTrue(L.R.verify_all())
        marks = L.R.markers()
        for lab, pid in L.R.predicates.items():
            self.assertIn(lab, marks)
        self.assertEqual(sorted(L.PROOFS), sorted(L.LEAN))
        self.assertEqual(L.BLOCK, "C")


if __name__ == "__main__":
    unittest.main()
