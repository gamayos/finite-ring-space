"""frc/lattice.py (the gravity theme; 21-gravity): the difference operators and the shift theorem checked a second way —
the adjoint identity by explicit matrices, the shift theorem against the fourier theme's transform, the Fierz–Pauli
functional's invariance against a wrong coefficient, the tree count against Kirchhoff's n."""
import random
import unittest
from fractions import Fraction

from frc import arith
from frc import lattice as LT


class CycleTest(unittest.TestCase):
    def test_central_difference_matrix_is_antisymmetric(self):
        n = 7
        M = [[0] * n for _ in range(n)]
        for i in range(n):
            e = [int(j == i) for j in range(n)]
            col = LT.cdiff(e, n)
            for r in range(n): M[r][i] = col[r]
        self.assertTrue(all(M[i][j] == -M[j][i] for i in range(n) for j in range(n)))
        rng = random.Random(3)
        for n in (3, 4, 9, 16):
            f = [rng.randint(-5, 5) for _ in range(n)]; g = [rng.randint(-5, 5) for _ in range(n)]
            self.assertTrue(LT.adjoint_identity(f, g, n))
            self.assertTrue(LT.forward_adjoint_identity(f, g, n))

    def test_shift_theorem_against_fourier_theme(self):
        from frc.fourier import identity, matmul
        p, n = 13, 12
        g = arith.primitive_root(p)
        z = LT.root_of_unity(p, n, g)
        self.assertEqual(z, g)
        v = [3, 1, 4, 1, 5, 9, 2, 6, 5, 3, 5, 8]
        self.assertTrue(all(LT.shift_theorem(p, n, g, v, a) for a in range(n)))
        F = [[pow(z, (j * k) % n, p) for j in range(n)] for k in range(n)]
        self.assertEqual([sum(F[k][x] * v[x] for x in range(n)) % p for k in range(n)], LT.dft(v, z, p))
        self.assertEqual(matmul(F, identity(n), p), F)

    def test_laplacian_symbol_and_trees(self):
        even, zeros = LT.laplacian_symbol_even(13, 2)
        self.assertTrue(even); self.assertEqual(zeros, [0])
        for n in (3, 4, 7, 10):
            self.assertEqual(LT.tree_count(n), n)
        self.assertEqual(LT.two_shift_run(2, 1, 4), [0, -1, -3, -6, -10])
        self.assertTrue(LT.two_shift_law(5, 3, 12))


class FierzPauliTest(unittest.TestCase):
    def test_invariance_and_control(self):
        self.assertTrue(LT.fp_gauge_invariant(3, 4, seed=2))
        self.assertFalse(LT.fp_gauge_invariant(3, 4, seed=2, kind="forward"))
        h, xi = LT.random_fields(3, 4, seed=2)
        g = LT.gauge_shift(xi, 3, 4)
        h2 = {k: {x: h[k][x] + g[k][x] for x in h[k]} for k in h}
        E1, E2 = LT.fp_energy(h, 3, 4), LT.fp_energy(h2, 3, 4)
        self.assertEqual(E1, E2)
        self.assertNotEqual(E1, 0)
        self.assertTrue(LT.fp_gauge_invariant(3, 4, seed=2, kind="central") and LT.fp_energy(h, 3, 4, eta=[1, 1, 1, 1]) == LT.fp_energy(h2, 3, 4, eta=[1, 1, 1, 1]))

    def test_symbol_lines_and_tt_rank(self):
        ok1, ok2, ns1, ns2 = LT.fierz_pauli_line(samples=10)
        self.assertTrue(ok1 and ok2)
        self.assertEqual([ns2[0][i] / ns2[0][0] for i in range(4)], [1, -2, 2, -1])
        self.assertEqual(LT.tt_rank((0, 0, 1)), 2)
        self.assertEqual(LT.tt_rank((2, 3, 6)), 2)


if __name__ == "__main__":
    unittest.main()
