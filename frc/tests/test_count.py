"""The count theme (frc/count.py; 20-rh's revision of 21 November 2026): its helpers computed two ways, every statement
of lean/FrcCore/Theme/Count.lean and Theme/Circle.lean on the shells 13, 17, 29 and 173, and false variants refused: a wrong capacity κ or S, a table that is not the Gram table, a vector that is not read back."""
import unittest

from frc import arith
from frc import count as CT
from frc import horizon as H

SHELLS = (13, 17, 29, 173)


class HelpersTest(unittest.TestCase):
    def test_generators(self):
        for p in SHELLS:
            gs = CT.generators(p)
            self.assertEqual(len(gs), arith.phi(p - 1))
            self.assertEqual(gs[0], arith.primitive_root(p))
            for g in gs: self.assertEqual(len({pow(g, m, p) for m in range(p - 1)}), p - 1)

    def test_gram_two_ways(self):
        for p in SHELLS[:3]:
            P = CT.gram_table(p)
            self.assertEqual(len(P), 2 * p - 3)
            for k in range(p - 1):
                for m in range(p - 1):
                    self.assertEqual(CT.gram(p, k, m), P[k + m])
                    self.assertEqual(P[k + m], H.zeta(p, k + m))                   # the Gram entry is the finite zeta at k + m
            self.assertEqual([n for n, v in enumerate(P) if v], [0, p - 1])        # −1 at the multiples of p − 1, zero elsewhere
            self.assertEqual(P[0], p - 1)

    def test_mode_expansion_reads_a_vector_back(self):
        for p in SHELLS[:3]:
            for v in (CT.delta(p, 1), CT.delta(p, p - 1), CT.fixed_sequence(p, 7)):
                c = CT.mode_coefficients(p, v)
                self.assertEqual(CT.mode_values(p, c), v)
                self.assertEqual(c[0], (-sum(v)) % p)                              # the constant part is minus the sum
            c = [0] * (p - 1); c[3] = 1                                             # the mode of count 3 has the one coefficient
            self.assertEqual(CT.mode_coefficients(p, [pow(x, 3, p) for x in range(1, p)]), c)

    def test_frequency_and_quarter_turn(self):
        for p in SHELLS:
            kap, g = (p - 1) // 4, arith.primitive_root(p)
            i = CT.quarter_turn(p, kap, g)
            self.assertEqual(i, pow(g, p - 1 - kap, p))                             # −g^κ = g^(−κ)
            self.assertEqual(i * i % p, p - 1)
            half = pow(2, p - 2, p)
            for k in range(p - 1):
                self.assertEqual(CT.frequency(p, kap, i, k), (-i * (k + half)) % p)
                self.assertEqual((half + i * CT.frequency(p, kap, i, k)) % p, (k + 1) % p)

    def test_run_shifts(self):
        for p in SHELLS[:3]:
            self.assertEqual(CT.run_shifts(p, 0), {1})                              # the run from 0 asks for 2c = 1 alone
            self.assertEqual(CT.run_shifts(p, 1), {1})
            self.assertEqual(CT.run_shifts(p, p - 1), {3})                          # the run from p − 1: 2c = 3
            self.assertGreater(len(CT.run_shifts(p, 2)), 1)


class StatementsTest(unittest.TestCase):
    def test_every_statement_on_the_shells(self):
        for p in SHELLS:
            kap = (p - 1) // 4; P = CT.gram_table(p); gs = CT.generators(p)[:4]
            vecs = [(y, CT.delta(p, y)) for y in (1, 2, p - 1)] + [("s", CT.fixed_sequence(p, 3))]
            self.assertTrue(CT.count_conjugate(p)); self.assertTrue(CT.count_adjoint(p, P)); self.assertTrue(CT.count_adjoint(p, P, direct=p < 30))
            self.assertTrue(CT.gram_rows(p, P, (1, p - 2)))
            self.assertTrue(CT.count_adjoint_vector(p, [(a, b) for a in vecs for b in vecs]))
            self.assertTrue(CT.half_forced(p)); self.assertTrue(CT.count_run(p, [0, 1, 5])); self.assertTrue(CT.count_run_only(p, [0, 1]))
            self.assertTrue(CT.zeros_fill(p)); self.assertTrue(CT.zeros_fill_ends(p)); self.assertTrue(CT.energy_order(p, kap))
            self.assertTrue(CT.cardinal_zeros(p, kap)); self.assertTrue(CT.carrier_centre(p, kap)); self.assertTrue(CT.half_unique(p, kap))
            self.assertTrue(CT.origin_unit_symmetry(p)); self.assertTrue(CT.zero_shared(p, 233 if p < 233 else 30089))
            for g in gs:
                self.assertTrue(CT.mode_stride(p, g) if p < 100 else True)
                for f in (CT.zero_count, CT.zero_conjugate, CT.centre_mode, CT.pair_invariant, CT.cardinal_modes): self.assertTrue(f(p, kap, g), f.__name__)
                self.assertTrue(CT.generator_skew(p, kap, g, P))
                self.assertTrue(CT.modes_orthogonal(p, P)); self.assertTrue(CT.generator_selfadjoint(p, kap, g, P))
                self.assertTrue(CT.generator_selfadjoint_vector(p, kap, g, [(a, b) for a in vecs[:6] for b in vecs[:6]]))
                self.assertTrue(CT.circle_pair(p, g)); self.assertTrue(CT.circle_point(p, g))
                for f in (CT.circle_frequency, CT.circle_meridians, CT.circle_count, CT.circle_counts, CT.circle_place_cycle, CT.circle_place_even, CT.circle_quarter_turn):
                    self.assertTrue(f(p, kap, g), f.__name__)
                self.assertTrue(CT.circle_phase(p, g)); self.assertTrue(CT.circle_place_phase(p, g)); self.assertTrue(CT.circle_parallels(p, kap, g))
            self.assertTrue(CT.circle_place(p)); self.assertTrue(CT.circle_quarter_closes(p))
            om = 233 if p == 13 else 30089                                      # a shell with p² below it
            self.assertTrue(CT.zeros_not_held(p, om)); self.assertTrue(CT.zeros_not_held(p, om, lambda y: (y * y + 1) % p))
            self.assertTrue(CT.zeros_collide(233, 230)); self.assertTrue(CT.zeros_collide(233, 230, lambda y: max(0, y - 3)))   # 231 zeros, 230 states

    def test_the_circle_of_f13(self):
        p, kap, g = 13, 3, 2
        points = dict((m, a) for a, m in CT.circle_points(p, g))
        self.assertEqual(sorted(points), [0, 1, 2, 4, 5, 6, 7, 8, 10, 11])          # every phase but κ = 3 and 3κ = 9
        near = {m: points[m] * pow(g, m, p) % p for m in (0, 1, 2, 10, 11)}           # the phases 0, ±1, ±2
        self.assertEqual(near, {10: 10, 11: 8, 0: 7, 1: 6, 2: 4})                    # the zeros of the circle
        counts = {m: (-points[m]) * pow(g, -m % (p - 1), p) % p for m in near}       # the point (−a, −m)
        self.assertEqual(counts, {m: z - 1 for m, z in near.items()})                # the count of each zero: 9, 7, 6, 5, 3
        places = CT.circle_places(p, kap, g)
        self.assertEqual([places.get(j) for j in range(12)], [7, 5, 6, 11, 4, 12, None, 2, 10, 3, 8, 9])
        squares = {x * x % p for x in range(1, p)}
        self.assertEqual(sorted(r for r in range(2, p) if r * (1 - r) % p not in squares), [2, 3, 5, 9, 11, 12])   # the zeros with no point
        gi = pow(g, p - 2, p); pair = lambda a, m: (a * pow(g, m, p) % p, a * pow(gi, m, p) % p)
        level = lambda c: sorted({pair(a, m) for a in range(1, p) for m in range(p - 1) if sum(pair(a, m)) % p == c})
        self.assertEqual(level(1), [(4, 10), (6, 8), (7, 7), (8, 6), (10, 4)])       # the critical circle: a zero and its conjugate
        self.assertEqual(level(p - 1), [(3, 9), (5, 7), (6, 6), (7, 5), (9, 3)])     # its half-turn: a count and its conjugate
        self.assertEqual(level(2), sorted(tuple(2 * x % p for x in t) for t in level(1)))                          # the level 2 is the circle doubled

    def test_false_variants_are_refused(self):
        p, kap = 13, 3; P = CT.gram_table(p); g = 2
        self.assertFalse(CT.cardinal_zeros(p, 2)); self.assertFalse(CT.carrier_centre(p, 2)); self.assertFalse(CT.half_unique(p, 2))
        self.assertFalse(CT.energy_order(p, 2)); self.assertFalse(CT.zero_shared(173, 13))
        self.assertFalse(CT.zero_count(p, 2, g)); self.assertFalse(CT.centre_mode(p, 2, g)); self.assertFalse(CT.cardinal_modes(p, 2, g))
        self.assertFalse(CT.zero_conjugate(p, 2, g)); self.assertFalse(CT.pair_invariant(p, 2, g))
        self.assertFalse(CT.count_adjoint(p, [1] * len(P)))                         # a table that is not the Gram table
        self.assertFalse(CT.circle_meridians(p, 2, g)); self.assertFalse(CT.circle_count(p, 2, g)); self.assertFalse(CT.circle_counts(p, 2, g))
        self.assertFalse(CT.circle_place_cycle(p, 2, g)); self.assertFalse(CT.circle_place_even(p, kap, 3))   # 3 is a square of F_13 and no generator
        self.assertFalse(CT.circle_parallels(p, 2, g))                              # a wrong capacity: the prime meridian's residue is not c·(2κ + 1)
        self.assertFalse(CT.generator_skew(p, kap, g, [1] * len(P)))
        self.assertFalse(CT.modes_orthogonal(p, [1] * len(P))); self.assertFalse(CT.generator_selfadjoint(p, kap, g, [1] * len(P)))
        self.assertFalse(CT.zeros_not_held(13, 169)); self.assertFalse(CT.zeros_not_held(1, 233))   # 13² is not below 169; a shell of one state
        self.assertEqual(len({max(0, y - 2) for y in range(2, 233)}), 231)          # 231 states hold the 231 zeros of the shell 233
        self.assertFalse(CT.zeros_collide(233, 13, lambda y: y))                    # no reading into 13 states
        self.assertFalse(CT.count_adjoint_vector(p, [((1, CT.delta(p, 1)), (2, [1] * (p - 2)))]))   # a vector of the wrong length is not read back
        self.assertTrue(CT.origin_unit_symmetry(p, pairs=[(1, 0), (p - 1, 1), (2, 5)]))


if __name__ == "__main__":
    unittest.main()
