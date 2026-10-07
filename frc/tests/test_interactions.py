"""The interactions theme's python (frc/interactions.py; task LM29): each value computed two ways, and the master's
block file interactions.py green, its markers on its deciding checks."""
import unittest
from fractions import Fraction
from itertools import combinations

from frc.interactions import bit, cnt, emul, fifth, gen16, col, wk, y6, q6, koide_q, koide_rho2


class InteractionsTest(unittest.TestCase):
    def test_subsets(self):
        self.assertEqual(gen16(), sorted(sum(1 << i for i in c) for k in (0, 2, 4) for c in combinations(range(5), k)))
        for S in range(32):
            self.assertEqual(cnt(S, 0, 5), bin(S).count("1"))

    def test_signs(self):
        # e_S as the ordered product of its directions: the sign of e_S e_T is the parity of the merge permutation
        for S in range(16):
            for T in range(16):
                s, U = emul(S, T)
                if S & T: self.assertEqual(s, 0); continue
                seq = [i for i in range(4) if bit(S, i)] + [i for i in range(4) if bit(T, i)]
                inv = sum(1 for x in range(len(seq)) for y in range(x + 1, len(seq)) if seq[x] > seq[y])
                self.assertEqual((s, U), ((-1) ** inv, S | T))

    def test_generation(self):
        self.assertEqual(sorted(fifth(S) for S in range(16)), gen16())
        self.assertEqual(sum(y6(S) for S in gen16()), 0)
        self.assertEqual(sorted(q6(S) for S in gen16()), sorted([0, 0, 4, 4, 4, -4, -4, -4, -2, -2, -2, 2, 2, 2, 6, -6]))

    def test_koide(self):
        self.assertEqual(koide_q([1, 1, 1]), Fraction(1, 3))
        p, w = 13, 3
        for a in ([1, 2, 3], [5, 0, 7], [2, 2, 9]):
            hat, l, r = koide_rho2(a, p, w)
            self.assertEqual(l, r)


class MasterInteractionsTest(unittest.TestCase):
    def test_block_file(self):
        from frc.ledgers.master import interactions as I
        self.assertTrue(I.R.verify_all())
        marks = I.R.markers()
        for lab in I.R.predicates: self.assertIn(lab, marks)
        self.assertEqual(sorted(I.PROOFS), sorted(I.LEAN))
        self.assertEqual(I.BLOCK, "G")


if __name__ == "__main__":
    unittest.main()
