"""The frame and extension themes' python (frc/shell.py, frc/extension.py; tasks LM16 and LM20): each value computed two
ways, by the theme's method and by brute force or a closed form."""
import itertools, unittest
from frc import arith
from frc.shell import kappa, squares, nonsquares, is_square, generators, Q, value_counts, isotropic_count, orthogonal_order, \
    o_plus_4, o_minus_4, mat_mul, preserves, closure
from frc.extension import Ext, ext_value_counts, boost

SHELLS = (5, 13, 17, 29)


class ShellTest(unittest.TestCase):
    def test_classes(self):
        for p in SHELLS:
            S, N = squares(p), nonsquares(p)
            self.assertEqual(kappa(p), (p - 1) // 4)
            self.assertEqual(len(S), (p - 1) // 2); self.assertEqual(sorted(S + N), list(range(1, p)))
            self.assertEqual([x for x in range(1, p) if is_square(x, p)], S)
            self.assertEqual([x for x in range(1, p) if arith.legendre(x, p) == 1], S)
            self.assertEqual(generators(p), arith.primitive_roots(p))
        self.assertRaises(ValueError, kappa, 7)

    def test_forms(self):
        for p in (5, 13):
            for coeffs in ((1, 1), ((-2) % p, 1, 1), ((-nonsquares(p)[0]) % p, 1, 1, 1)):
                brute = [0] * p
                for v in itertools.product(range(p), repeat=len(coeffs)): brute[Q(coeffs, v, p)] += 1
                self.assertEqual(value_counts(coeffs, p), brute)
            nu = nonsquares(p)[0]
            self.assertEqual(isotropic_count(((-nu) % p, 1, 1, 1), p), p ** 3 - p * p + p)        # the elliptic type
            self.assertEqual(isotropic_count(((-1) % p, 1, 1, 1), p), p ** 3 + p * p - p)         # the hyperbolic type
        self.assertEqual(orthogonal_order(((-2) % 5, 1, 1, 1), 5), o_minus_4(5))
        self.assertEqual(orthogonal_order(((-1) % 5, 1, 1, 1), 5), o_plus_4(5))
        self.assertEqual(o_minus_4(5), 31200)

    def test_matrices(self):
        p = 7; I = ((1, 0), (0, 1)); R = ((0, 6), (1, 0))                                            # a quarter-turn of the plane
        self.assertEqual(mat_mul(R, mat_mul(R, mat_mul(R, R, p), p), p), I)
        self.assertEqual(len(closure([R], p)), 4)
        self.assertTrue(preserves(R, (1, 1), p)); self.assertFalse(preserves(((2, 0), (0, 1)), (1, 1), p))


class ExtensionTest(unittest.TestCase):
    def test_field(self):
        for p in (5, 13):
            nu = nonsquares(p)[0]; K = Ext(p, nu)
            for x in K.elements()[:40]:
                for y in K.elements()[::7]:
                    self.assertEqual(K.norm(K.mul(x, y)), K.norm(x) * K.norm(y) % p)                # the norm is multiplicative
                    self.assertEqual(K.conj(K.mul(x, y)), K.mul(K.conj(x), K.conj(y)))
                self.assertEqual(K.conj(x), K.pow(x, p))                                              # conjugation is Frobenius
                if x != (0, 0): self.assertEqual(K.mul(x, K.inv(x)), (1, 0))
            self.assertEqual(len(K.norm_one()), p + 1)
            self.assertTrue(all(K.is_square_ext((a, 0)) for a in range(1, p)))
            self.assertRaises(ValueError, Ext, p, 1)

    def test_forms_and_boosts(self):
        p = 5; nu = 2; K = Ext(p, nu); q = p * p
        self.assertEqual(ext_value_counts(K, [(-nu) % p, 1, 1, 1])[(0, 0)], q ** 3 + q * q - q)
        for g, b in K.norm_one():
            self.assertTrue(preserves(boost(g, b, nu, p), ((-nu) % p, 1), p))


if __name__ == "__main__":
    unittest.main()
