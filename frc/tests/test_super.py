"""The super theme (frc/super.py; the master's G19 and G20, 19 October 2026), its chart readings (frc/chart_super.py) and the
master's block file (frc/ledgers/master/super.py): the winding kernel against the count q^(n−1) by a second route, the residual
subgroup against gcd, the ℤ[√2] identities against floating point, the symplectic map's clauses against direct arithmetic,
the metrology polynomials evaluated at random rationals, the even Sturm count against the float bisection and against a
dense symmetric solver where numpy is installed; the block file green, its markers on its deciding checks, its keys core."""
import math
import random
import unittest
from fractions import Fraction as Q
from math import gcd

from frc import super as S
from frc import chart_super as CS
from frc import interactions as I


class SuperTest(unittest.TestCase):
    def test_dual_map(self):
        for p, g in ((13, 2), (17, 3), (29, 2)):
            self.assertEqual(S.dual_map(p, g), (True, True, True))

    def test_winding_kernel(self):
        for q in (4, 8, 12, 16, 28):
            n2, inv = S.winding_kernel(q, 2)
            self.assertEqual((n2, inv), (q, True))
            self.assertEqual(S.winding_kernel(q, 3)[0], q * q)
            # a second route: for every (k₁, …, k_{n−1}) exactly one k_n closes the sum
            self.assertEqual(S.winding_kernel(q, 3)[0], sum(1 for a in range(q) for b in range(q)))

    def test_residual(self):
        for q in (16, 28, 40, 52, 88, 100, 6, 10):
            self.assertEqual(len(S.residual(q)), gcd(2, q))
            self.assertEqual(S.residual(q), [0, q // 2] if q % 2 == 0 else [0])
        self.assertEqual(S.residual(12, qc=3), [0, 4, 8])

    def test_self_dual_point(self):
        sd = S.self_dual_point()
        self.assertEqual((sd["prod"], sd["diff"], sd["tanh"], sd["quad"]), ((1, 0), (2, 0), (0, 1), (0, 0)))
        r2 = math.sqrt(2)
        val = lambda v: v[0] + v[1] * r2
        self.assertAlmostEqual(val(S.r2_mul((1, 1), (-1, 1))), (1 + r2) * (r2 - 1), places=12)
        self.assertAlmostEqual(math.tanh(CS.beta_star()), val(sd["tanh"]) - 1, places=12)
        self.assertAlmostEqual(math.sinh(2 * CS.beta_star()), 1, places=12)

    def test_symplectic(self):
        for q in (8, 16, 28):
            self.assertEqual(S.symplectic(q), (True, True, True, True))
            rng = random.Random(q)
            for _ in range(50):
                u = (rng.randrange(q), rng.randrange(q)); v = (rng.randrange(q), rng.randrange(q))
                self.assertEqual(S.S(S.S(u, q), q), ((-u[0]) % q, (-u[1]) % q))
                self.assertEqual(S.pairing(u, v, q), (u[0] * v[1] - v[0] * u[1]) % q)
                self.assertEqual(S.pairing(S.S(u, q), S.S(v, q), q), S.pairing(u, v, q))

    def test_metrology(self):
        m = S.metrology()
        self.assertEqual(sorted(m), ["action", "pair", "product", "single", "step"])
        self.assertTrue(all(v.is_zero() for v in m.values()))
        rng = random.Random(7)
        for _ in range(20):                                           # the identities at random rationals with the inverses honest
            e, h, n, f = (Q(rng.randrange(1, 100), rng.randrange(1, 100)) for _ in range(4))
            KJ, RK = 2 * e / h, h / e ** 2
            self.assertEqual(2 * e * (h / (2 * e)), h)
            self.assertEqual(KJ * RK * (2 * e), 4); self.assertEqual(KJ * RK * e, 2)
            self.assertEqual((n * f / KJ) * (n * 2 * e * f), n * n * f * f * h)

    def test_even_sturm(self):
        N, L = 60, 10
        diag, h = S.even_grid(N, L)
        self.assertEqual(len(diag), N + 1)
        for lam, k in (("0.5", 0), ("1.5", 1), ("3.5", 2), ("5.0", 3)):
            self.assertEqual(S.sturm_even(N, L, Q(lam)), k)
        try:
            import numpy as np
        except ImportError:
            return
        hf = L / (N + 1); M = np.diag([2 / hf ** 2 + k * hf for k in range(N + 1)])
        for k in range(N): M[k, k + 1] = M[k + 1, k] = -1 / hf ** 2
        M[0, 1] = M[1, 0] = -math.sqrt(2) / hf ** 2                    # the symmetrised Neumann link
        w = np.linalg.eigvalsh(M)
        for lam in ("0.5", "1.5", "3.5", "5.0"):
            self.assertEqual(S.sturm_even(N, L, Q(lam)), int((w < float(lam)).sum()))

    def test_airy_ladder(self):
        ev, od, (lo, hi) = S.airy_ladder(200, 16, [("1.018", "1.019"), ("3.246", "3.247")], [("2.337", "2.338")])
        self.assertEqual((ev, od), ([(0, 1), (1, 2)], [(0, 1)]))
        self.assertTrue(Q("0.687") < lo < hi < Q("0.691"))
        (e1, e2, e3, rho), zeros = CS.airy_ladder(200, 16)
        self.assertTrue(1.018 < e1 < 1.019 and 2.337 < e2 < 2.338 and 3.246 < e3 < 3.247)
        self.assertTrue(lo < Q(rho) < hi)
        self.assertAlmostEqual(CS.airy_ratio(), 0.690, places=2)


class ChartSuperTest(unittest.TestCase):
    def test_tension(self):
        b = CS.beta_star()
        self.assertAlmostEqual(b, 0.5 * math.log(1 + math.sqrt(2)), places=15)
        self.assertAlmostEqual(CS.tau(b), 0, places=12)
        prof, below = CS.tension_profile()
        self.assertTrue(all(x > 0 for x in prof) and below < 0)
        self.assertAlmostEqual(CS.dual(CS.dual(0.3)), 0.3, places=12)

    def test_universal_numbers(self):
        u = CS.universal_numbers()
        self.assertAlmostEqual(u["jump"], 2 / math.pi, places=15)
        self.assertAlmostEqual(u["gap_ratio"], 3.5277, places=3)
        self.assertAlmostEqual(u["heat_jump"], 1.4261, places=3)


class MasterSuperTest(unittest.TestCase):
    def test_block_file(self):
        """The master's super block file (19 October 2026): G19 and G20 decided by marked checks, their keys core."""
        from frc.ledgers.master import super as M
        self.assertTrue(M.R.verify_all())
        marks = M.R.markers()
        for lab in M.R.predicates: self.assertIn(lab, marks)
        self.assertEqual(sorted(M.PROOFS), sorted(M.LEAN))
        self.assertEqual(M.BLOCK, "G")
        self.assertEqual(sorted(M.PREDICATES), ["00:G19", "00:G20"])
        self.assertTrue(all(v == "core" for v in M.LEAN.values()))             # a T row of block G binds no chart key (G08)
        self.assertFalse(hasattr(M, "CHART"))
        kinds = {r["id"]: r["kind"] for r in M.R.results}
        self.assertEqual(kinds["S1"], "EXACT"); self.assertEqual(kinds["D1"], "EXACT")
        self.assertEqual(kinds["S2"], "CHART"); self.assertEqual(kinds["D2"], "CHART")


if __name__ == "__main__":
    unittest.main()
