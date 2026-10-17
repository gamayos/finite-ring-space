"""The quantum theme's python (frc/quantum.py; task LM28): each value computed two ways, and the master's block file
quantum.py green, its markers on its deciding checks."""
import unittest
from math import gcd, lcm

from frc.quantum import joint_period, orbits, offset, reach, root_of_unity, character_sums, cycle, division_fold, core_cosets, fusion
from frc.arith import is_prime, order


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

    def test_division_fold(self):
        """00:F4: the fold against the order computed by arith.order, the cycle against the powers, the fibres against the
        cosets of the roots of x⁴ = 1 found by search."""
        for q, g in [(13, 2), (17, 3), (29, 2), (157, 5), (157, pow(5, 13, 157)), (421, pow(2, 15, 421))]:
            n = order(g, q)
            self.assertEqual(cycle(q, g), [pow(g, e, q) for e in range(n)])
            k = n // 4
            fold = division_fold(q, g)
            self.assertEqual(len(fold), n)
            self.assertEqual(sorted(fold.values()), sorted(cycle(q, g)))
            for (r, s), x in fold.items(): self.assertEqual(x, pow(g, 3 * k * r + s, q))
            roots4 = sorted(x for x in range(1, q) if pow(x, 4, q) == 1)
            fib = core_cosets(q, g)
            self.assertEqual(len(fib), k)
            for s, f in enumerate(fib): self.assertEqual(sorted(f), sorted(pow(g, s, q) * w % q for w in roots4))
        with self.assertRaises(ValueError): division_fold(7, 3)                      # order 6, no quarter
        with self.assertRaises(ValueError): core_cosets(13, 3)                       # order 3

    def test_fusion(self):
        """00:F6: fusion against the gcd and against a direct reachability search."""
        for a in range(1, 15):
            for b in range(1, 15):
                self.assertEqual(fusion(a, b), gcd(a, b) == 1)
                self.assertEqual(fusion(a, b), all(reach(0, 0, x, y, a, b) is not None for x in range(a) for y in range(b)))


class MasterQuantumTest(unittest.TestCase):
    def test_block_file(self):
        from frc.ledgers.master import quantum as Q
        self.assertTrue(Q.R.verify_all())
        marks = Q.R.markers()
        for lab in Q.R.predicates: self.assertIn(lab, marks)
        self.assertEqual(sorted(Q.PROOFS), sorted(Q.LEAN))
        self.assertEqual(Q.BLOCK, "F")
        self.assertEqual(sorted(Q.PREDICATES), ["00:F2", "00:F4", "00:F5", "00:F6"])

    def _mutant(self, block, name, fake):
        """Run one block of a fresh copy of the block file with the theme function `name` replaced; the checks' verdicts."""
        import importlib, sys
        sys.modules.pop("frc.ledgers.master.quantum", None)
        Q = importlib.import_module("frc.ledgers.master.quantum")
        setattr(Q, name, fake)
        Q.R.run_block(block)
        out = {r["id"]: r["ok"] for r in Q.R.results}
        sys.modules.pop("frc.ledgers.master.quantum", None)
        return out

    def test_mutations(self):
        """The checks fail on a wrong theme function: Q1 on a fold that is no bijection (the product fold on every capacity),
        Q2 on a conjugation that is the identity, Q3 on fibres that are not cosets, B1 on fusion read off the lcm, on orbits
        with the right count and the wrong members and on a wrong offset, B2 on fusion always true and on a drive of the
        wrong order, B3 on a wrong root of unity."""
        from frc import quantum as T
        from frc.subject import frame as frame_drive_frame
        frame_drive = lambda p: frame_drive_frame(p)[1]
        def prod_fold(q, g):                                                         # the product fold iʳ (g⁴)ˢ in the place of iʳ gˢ
            n = len(T.cycle(q, g)); k = n // 4; i = pow(g, 3 * k, q); g4 = pow(g, 4, q)
            return {(r, s): pow(i, r, q) * pow(g4, s, q) % q for r in range(4) for s in range(k)}
        self.assertFalse(self._mutant("Q", "division_fold", prod_fold)["Q1"])
        def slices(q, g):                                                            # consecutive quarters of the cycle, not cosets
            cyc = T.cycle(q, g); return [frozenset(cyc[4 * s:4 * s + 4]) for s in range(len(cyc) // 4)]
        self.assertFalse(self._mutant("Q", "core_cosets", slices)["Q3"])
        self.assertFalse(self._mutant("B", "fusion", lambda a, b: lcm(a, b) == max(a, b))["B1"])
        self.assertFalse(self._mutant("B", "fusion", lambda a, b: True)["B2"])
        self.assertFalse(self._mutant("B", "root_of_unity", lambda q, N: 1)["B3"])
        def chunks(a, b):                                                            # the right count, the wrong members
            g, T = gcd(a, b), lcm(a, b); st = [(x, y) for x in range(a) for y in range(b)]
            return [st[j * T:(j + 1) * T] for j in range(g)]
        self.assertFalse(self._mutant("B", "orbits", chunks)["B1"])
        self.assertFalse(self._mutant("B", "offset", lambda x, y, g: x % g)["B1"])
        self.assertFalse(self._mutant("B", "frame", lambda p: (43, pow(frame_drive(p), 2, p), 86, 0))["B2"])   # the drive squared: order 86
        class ConjId(T.Cyclotomic):
            def conj(self, a): return a
        self.assertFalse(self._mutant("Q", "Cyclotomic", ConjId)["Q2"])


if __name__ == "__main__":
    unittest.main()
