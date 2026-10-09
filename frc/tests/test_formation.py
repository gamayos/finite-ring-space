"""The logic theme's formation file (frc/formation.py; 29-finitism, 9 October 2026): each value computed two ways —
the minimal realization against a direct search for realizing universes, the swap's parity against a direct count, the
buffer frame's reach against the level formula, the induction schema against exhaustive enumeration, the second-order
evaluation against tables of satisfying assignments — and the ledger file p29_finitism.py green with its markers."""
import random
import unittest
from itertools import product

from frc.formation import (passes, minimal, pad, double, swap, is_automorphism, count_invariant, swap_invariant, buffer,
                           chain, reachable, least_below, finite_induction_holds, records, record, random_universe,
                           random_passed_trace, sval2, sval2_table, so_arities, random_sformula, closed)
from frc.logic import random_structure, successor_counterexample


class FormationTest(unittest.TestCase):
    def test_minimal_and_padding(self):
        rng = random.Random(29)
        for _ in range(200):
            U = random_universe(rng, rng.randrange(2, 8))
            T, e = random_passed_trace(rng, U)
            self.assertTrue(passes(T, U, e))
            M = minimal(T)
            self.assertTrue(closed(M) and M[0] == T[0] and passes(T, M, list(range(T[0]))))
            # a second way: among all universes on t objects, the minimal one is one that realizes T under the identity
            t = T[0]
            if t <= 3:
                found = [form for form in product([None] + list(range(t)), repeat=t) if passes(T, (t, list(form)), list(range(t)))]
                self.assertIn(M[1], [list(f) for f in found])
            for B in (0, 1, 5, 40):
                P = pad(M, B + 1)
                self.assertTrue(passes(T, P, list(range(t))) and P[0] > B)

    def test_double_and_swap(self):
        rng = random.Random(7)
        for _ in range(200):
            U = random_universe(rng, rng.randrange(1, 8))
            n = U[0]
            if not closed(U): continue
            W = double(U)
            sigma = [swap(U, x) for x in range(2 * n)]
            self.assertTrue(is_automorphism(W, sigma))
            self.assertTrue(all(sigma[x] != x and sigma[sigma[x]] == x for x in range(2 * n)))
            T, e = random_passed_trace(rng, U)
            self.assertTrue(passes(T, W, e))
            for _ in range(5):
                D0 = [rng.randrange(2) == 0 for _ in range(n)]
                D = D0 + D0
                self.assertTrue(swap_invariant(W, D))
                c = count_invariant(W, D)
                self.assertEqual(c, 2 * sum(D0))                         # the parity, two ways
                self.assertNotEqual(c, 1)

    def test_buffer(self):
        for sigma in (1, 2, 3):
            for D in (1, 2, 5, 17):
                M, form = buffer(sigma, D)
                self.assertEqual(M, sigma * (D + 1))
                seeds = [s * (D + 1) for s in range(sigma)]
                for r in range(D + 1):
                    self.assertEqual(len(reachable((M, form), seeds, r)), sigma * (r + 1))
                for s in range(sigma):
                    for k in range(D + 1):
                        self.assertEqual(chain(sigma, D, s, k), s * (D + 1) + k)
                        if k < D: self.assertEqual(form[chain(sigma, D, s, k)], chain(sigma, D, s, k + 1))
                    self.assertIsNone(form[chain(sigma, D, s, D)])
        self.assertTrue(2 * 2 ** 4 < buffer(2, 17)[0] and 2 ** 4 < 17)

    def test_induction_and_least(self):
        rng = random.Random(3)
        for _ in range(500):
            n = rng.randrange(0, 16)
            P = [rng.randrange(2) == 0 for _ in range(n)]
            self.assertTrue(finite_induction_holds(P))
            fails = [x for x in range(n) if not P[x]]
            self.assertEqual(least_below([not p for p in P], n), fails[0] if fails else None)
        self.assertTrue(all(successor_counterexample(n) is None for n in range(1, 7)))

    def test_records(self):
        for s in (2, 3, 5, 32):
            for K in range(0, 12):
                self.assertEqual(records(s, K), (s ** (K + 1) - 1) // (s - 1))      # the geometric sum, closed form
                self.assertLess(records(s, K), s ** (K + 1))
        rng = random.Random(11)
        for _ in range(50):
            T, _ = random_passed_trace(rng, random_universe(rng, rng.randrange(1, 7)))
            self.assertEqual(len(record(T)), T[0] * T[0])

    def test_second_order(self):
        rng = random.Random(29)
        for _ in range(60):
            m = rng.randrange(1, 4)
            M = random_structure(rng, m)
            phi = random_sformula(rng, 3, 0, 0, 0)
            ke, ks, kr = so_arities(phi)
            self.assertEqual((ke, ks, kr), (0, 0, 0))
            v = sval2(M, (), (), (), phi)
            tab = sval2_table(M, phi, 0, 0, 0, 2)
            self.assertEqual(v, ((), (), ()) in tab)                              # the two evaluators agree on sentences
            neg = ("neg", phi)
            self.assertNotEqual(sval2(M, (), (), (), neg), v)                         # completeness and consistency


if __name__ == "__main__":
    unittest.main()
