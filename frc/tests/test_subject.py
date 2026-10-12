"""The subject theme's python (frc/subject.py; task LM24): each value computed two ways, by the theme's helper and by a
second method (search, closed form or the other side of a theorem), on every prime p = 4κ + 1 below a bound; and the
master's Subject block file green, its markers on its deciding checks."""
import unittest
from frc import arith
from frc.extension import Ext
from frc.foundation import quarter_turns
from frc import subject as SB
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


class PairTest(unittest.TestCase):
    """The pair (p, Ω) of 38-s13: every value against a second computation."""
    def test_instance(self):
        self.assertTrue(all(SB.admissible(13, 233).values()))
        self.assertEqual(SB.pair(13, 233, 2), (3, 58, 5, 3, 5))
        q, hb, z8 = SB.carrier_roots(233, 78)
        self.assertEqual((q, hb, z8), (pow(78, 58, 233), 233 - pow(78, 58, 233), pow(78, 29, 233)))
        self.assertEqual(SB.two_squares(233), ((13, 8), (89, 144)))
        self.assertEqual(SB.fibonacci(13)[-1], 233)

    def test_tower(self):
        for kappa in range(1, 300, 2):
            a, b = SB.tower_solution(kappa)
            self.assertEqual(4 * a, kappa * b + 1)
            self.assertEqual(b, 3 if kappa % 4 == 1 else 1)
        self.assertRaises(ValueError, SB.tower_solution, 4)

    def test_window_and_rates(self):
        for p in SHELLS[:30]:
            k, heights, sym = SB.window(p)
            self.assertEqual(heights, [h for h in range(p) if 4 * h < p])
            self.assertEqual(len(sym), p - 1)
            self.assertTrue(SB.pairwise_conservation(p)[0])
        for p, Om in ((13, 233), (5, 233), (29, 857)):
            ang, per, om1, cov = SB.leak_rate(p, Om)
            self.assertEqual(per, om1); self.assertEqual(cov * 2, om1)
            L, half, hp, hO = SB.joint_cycle(p, Om)
            self.assertEqual(L, SB.least_return(p, Om)); self.assertEqual((hp, hO), (0, (Om - 1) // 2))
            self.assertEqual(SB.apsidal_bound(p, Om), (True, True))
        self.assertEqual(SB.apsidal_bound(53, 157), (False, False))

    def test_kill_and_pisano(self):
        kt = SB.kill_test()
        self.assertEqual((kt["v_O"], kt["core_quarter"], kt["subject_face"], kt["lcm"]), (22, 28, 129, 156))
        self.assertEqual(SB.pisano(233), 52); self.assertEqual(SB.pisano(30089), 30088)


if __name__ == "__main__":
    unittest.main()
