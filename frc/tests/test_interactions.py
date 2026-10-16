"""The interactions theme's python (frc/interactions.py; task LM29): each value computed two ways, and the master's
block file interactions.py green, its markers on its deciding checks. Since the 27-fields migration (16 October 2026)
also the exact side of the finite gauge correspondence: the roots of unity in Q(ζ_M) against the complex roots, the
Wilson weight against 1 − cos, 2T's quaternions and traces, the area law's rational function against its float value."""
import cmath
import math
import unittest
from fractions import Fraction
from itertools import combinations

from frc import interactions as I
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


class CorrespondenceTest(unittest.TestCase):
    """The finite gauge correspondence's exact functions (16 October 2026): the ledger file p27_fields' B1, B2, B4."""

    def test_cyclotomic_forms(self):
        # the canonical form is the remainder modulo Φ_n, linear, and zero exactly on the kernel of cyclo_zero
        for n in (2, 3, 4, 6, 12, 15, 52):
            f = I.cyclotomic(n); d = len(f) - 1
            pw = I.cyclo_powers(n, 2 * n + 3)
            for m, v in enumerate(pw):
                self.assertEqual(len(v), d)
                self.assertEqual(v, I.cyclo_reduce([0] * m + [1], n))              # x^m reduced, two ways
                self.assertEqual(v, pw[m % n])                                     # ζ^n = 1
            self.assertEqual(I.cyclo_reduce([-1] + [0] * (n - 1) + [1], n), [0] * d)
            self.assertTrue(I.cyclo_zero([-1] + [0] * (n - 1) + [1], n))
            a, b = [1, 2, 0, -1], [3, 0, 1]
            self.assertEqual(I.poly_mul(a, b), [3, 6, 1, -1, 0, -1])
            ra, rb, rab = I.cyclo_reduce(a, n), I.cyclo_reduce(b, n), I.cyclo_reduce(I.poly_mul(a, b), n)
            self.assertEqual(rab, I.cyclo_reduce(I.poly_mul(ra, rb), n))             # reduction respects the product

    def test_roots_of_unity(self):
        for M in (1, 2, 3, 4, 6, 12, 52, 60):
            roots = I.roots_of_unity(M)
            self.assertEqual(len(roots), M)
            self.assertEqual([r.index(1) for r in roots], list(range(M)))
            hom, inj = I.roots_embed(M)
            self.assertTrue(hom and inj, M)
            for j, r in enumerate(roots):                                          # the canonical form at ζ = e^{2πi/M}
                z = sum(c * cmath.exp(2j * math.pi * k / M) for k, c in enumerate(I.cyclo_reduce(r, M)))
                self.assertAlmostEqual(abs(z - cmath.exp(2j * math.pi * j / M)), 0, places=12)

    def test_wilson_weight(self):
        for M in (2, 3, 7, 12, 52, 60):
            ident, pos = I.wilson_weight(M)
            self.assertTrue(ident and pos, M)
            pw = I.cyclo_powers(M, M)
            for k in range(M):                                                     # 2(1 − Re ζ^k) against 2(1 − cos 2πk/M)
                w = [2 * p0 - pk - pm for p0, pk, pm in zip(pw[0], pw[k], pw[(-k) % M])]
                z = sum(c * cmath.exp(2j * math.pi * i / M) for i, c in enumerate(w))
                self.assertAlmostEqual(z.imag, 0, places=12)
                self.assertAlmostEqual(z.real, 2 * (1 - math.cos(2 * math.pi * k / M)), places=12)
                self.assertEqual(any(w), k != 0)

    def test_tetrahedral(self):
        G, closed, unit, traces = I.tetrahedral_quaternions()
        self.assertEqual((len(G), len(set(G)), closed, unit), (24, 24, True, True))
        self.assertEqual(traces, {2: 1, -2: 1, 0: 6, 1: 8, -1: 8})
        self.assertEqual(sum(traces.values()), 24)
        self.assertTrue(all(I.su2_unitary(x) for x in G))
        self.assertFalse(I.su2_unitary((Fraction(1), Fraction(1), Fraction(0), Fraction(0))))      # norm 2
        self.assertTrue(I.trace_class_function(G))
        self.assertEqual((I.sl2_order(2), I.sl2_order(3), I.sl2_order(5)), (6, 24, 120))          # q(q² − 1)
        for x in G:                                                                # the trace is 2a and the Gaussian det is 1
            M = I.su2_matrix(x)
            tr = (M[0][0][0] + M[1][1][0], M[0][0][1] + M[1][1][1])
            self.assertEqual(tr, (2 * x[0], 0))
        self.assertEqual(I.gauss_mul((1, 2), (3, -1)), (5, 5))
        self.assertEqual(I.gauss_conj((1, 2)), (1, -2))

    def test_area_law(self):
        N, D, positive = I.area_law_rational()
        self.assertTrue(positive)
        self.assertEqual(N, [Fraction(c) for c in (-1, -4, 0, 4, 1)])
        self.assertEqual(D, [Fraction(c) for c in (1, 8, 6, 8, 1)])
        self.assertTrue(I.positive_beyond_one([1, -2, 1]) and I.positive_beyond_one([0, 0, 1]))     # (x − 1)², x²
        self.assertFalse(I.positive_beyond_one([-1]) or I.positive_beyond_one([-2, 1]) or I.positive_beyond_one([0]))
        for x in (Fraction(11, 10), Fraction(3, 2), Fraction(7), Fraction(1000)):
            c1 = I.area_law_rational(x)[3]
            self.assertTrue(0 < c1 < 1)
            xf = float(x)
            self.assertAlmostEqual(float(c1), sum(float(c) * xf ** k for k, c in enumerate(N)) / sum(float(c) * xf ** k for k, c in enumerate(D)), places=12)
        self.assertEqual(I.area_law_rational(Fraction(3, 2))[3], Fraction(185, 937))
        self.assertEqual(sum(N), 0)                                                # c₁(β = 0) = 0: N(1) = 0


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
