"""22-quantum's ledger file (frc/ledgers/p22_quantum.py; task LM35): the quantum theme's ring and matrix helpers and the
chart file frc/chart_quantum.py, each value computed two ways; the ledger file green, its markers on its deciding checks
with the keys of the generated table, and its blocks covering every record of the package's results.json."""
import cmath
import itertools
import json
import math
import random
import re
import unittest
from fractions import Fraction as Q
from pathlib import Path

from frc import arith
from frc import chart_quantum as CQ
from frc.quantum import Cyclotomic, cyclotomic_poly, charpoly, nonneg_spectrum, partial_transpose

ROOT = Path(__file__).resolve().parents[2]


def evaluate(R, a, n):
    """An element of ℤ[ζ_n] as a complex number, ζ = e^{2πi/n}."""
    z = cmath.exp(2j * math.pi / n)
    return sum(complex(c) * z ** i for i, c in enumerate(a))


class CyclotomicTest(unittest.TestCase):
    def test_degree_and_roots(self):
        for n in range(1, 61):
            R = Cyclotomic(n)
            self.assertEqual(len(cyclotomic_poly(n)) - 1, arith.phi(n))
            self.assertEqual(R.zeta(n), R.one)
            self.assertEqual(R.sum(R.zeta(k) for k in range(n)), R.zero if n > 1 else R.one)
            for k in range(n):
                self.assertEqual(R.mul(R.zeta(k), R.conj(R.zeta(k))), R.one)
                self.assertEqual(R.conj(R.zeta(k)), R.zeta(-k))

    def test_against_the_complex_numbers(self):
        rnd = random.Random(22)
        for n in (5, 7, 8, 12, 16, 28, 40, 60, 80):
            R = Cyclotomic(n)
            for _ in range(20):
                a = R.from_exponents((rnd.randrange(n), rnd.randint(-3, 3)) for _ in range(5))
                b = R.from_exponents((rnd.randrange(n), Q(rnd.randint(-3, 3), rnd.randint(1, 4))) for _ in range(5))
                self.assertLess(abs(evaluate(R, R.mul(a, b), n) - evaluate(R, a, n) * evaluate(R, b, n)), 1e-9)
                self.assertLess(abs(evaluate(R, R.conj(a), n) - evaluate(R, a, n).conjugate()), 1e-9)

    def test_shadow_is_a_homomorphism(self):
        for n, p in ((12, 157), (80, 641), (28, 421)):
            R, v = Cyclotomic(n), pow(arith.primitive_root(p), (p - 1) // n, p)
            rnd = random.Random(n)
            for _ in range(20):
                a = R.from_exponents((rnd.randrange(n), rnd.randint(-5, 5)) for _ in range(6))
                b = R.from_exponents((rnd.randrange(n), rnd.randint(-5, 5)) for _ in range(6))
                self.assertEqual(R.shadow(R.mul(a, b), p, v), R.shadow(a, p, v) * R.shadow(b, p, v) % p)
                self.assertEqual(R.shadow(R.add(a, b), p, v), (R.shadow(a, p, v) + R.shadow(b, p, v)) % p)


class MatrixTest(unittest.TestCase):
    @staticmethod
    def det(M):
        """The determinant by the Leibniz formula."""
        n, out = len(M), 0
        for perm in itertools.permutations(range(n)):
            sgn = (-1) ** sum(1 for i in range(n) for j in range(i + 1, n) if perm[i] > perm[j])
            out += sgn * math.prod(M[i][perm[i]] for i in range(n))
        return out

    def test_charpoly(self):
        rnd = random.Random(3)
        for n in (2, 3, 4):
            for _ in range(10):
                M = [[Q(rnd.randint(-4, 4), rnd.randint(1, 3)) for _ in range(n)] for _ in range(n)]
                c = charpoly(M)
                for x in (Q(0), Q(1), Q(-2), Q(5, 3)):
                    xm = [[(x if i == j else 0) - M[i][j] for j in range(n)] for i in range(n)]
                    self.assertEqual(sum(ck * x ** (n - k) for k, ck in enumerate(c)), self.det(xm))

    def test_spectrum_signs(self):
        rnd = random.Random(4)
        for _ in range(20):
            A = [[rnd.randint(-3, 3) for _ in range(4)] for _ in range(4)]
            G = [[sum(A[k][i] * A[k][j] for k in range(4)) for j in range(4)] for i in range(4)]     # a Gram matrix
            self.assertTrue(nonneg_spectrum(G))
            self.assertFalse(nonneg_spectrum([[-x for x in row] for row in G]) and any(any(row) for row in G))

    def test_partial_transpose(self):
        rnd = random.Random(5)
        for _ in range(10):
            M = [[rnd.randint(-5, 5) for _ in range(4)] for _ in range(4)]
            self.assertEqual(partial_transpose(partial_transpose(M)), M)
            self.assertEqual(sum(partial_transpose(M)[i][i] for i in range(4)), sum(M[i][i] for i in range(4)))
        bell = [[Q(1, 2) if a in (0, 3) and b in (0, 3) else 0 for b in range(4)] for a in range(4)]
        self.assertFalse(nonneg_spectrum(partial_transpose(bell)))           # the Bell state is NPT
        self.assertTrue(nonneg_spectrum(bell))


class ChartQuantumTest(unittest.TestCase):
    def test_chsh(self):
        best, worst, arg = CQ.chsh_sweep(16)
        self.assertAlmostEqual(best, 2 * math.sqrt(2), places=12)
        self.assertAlmostEqual(worst, -2 * math.sqrt(2), places=12)
        E = lambda d: math.cos(2 * math.pi * d / 16)
        self.assertAlmostEqual(E(arg[0]) + E(arg[1]) + E(arg[2]) - E(arg[3]), best, places=14)

    def test_envelope_and_sample(self):
        tau, chi, gauss = CQ.envelope(8, 40, (0,))[0]
        self.assertAlmostEqual(chi, 1, places=14); self.assertEqual(gauss, 1)
        self.assertLess(abs(CQ.sampled_scaling(2000, 50, 8, 1) - 1), 0.3)

    def test_emulation(self):
        self.assertTrue(all(d < 1e-12 for d in CQ.emulation().values()))


class LedgerTest(unittest.TestCase):
    def test_ledger_file(self):
        from frc.ledgers import p22_quantum as L
        self.assertTrue(L.R.verify_all())
        marks = L.R.markers()
        for lab in L.R.predicates: self.assertIn(lab, marks)
        self.assertEqual(L.PAPER, "22-quantum")
        self.assertEqual(L.LEAN, {})
        for lab, pid in L.PREDICATES.items():                               # each deciding check cites its predicate
            self.assertIn(lab, [x.strip() for x in L.LEDGER[pid].split(",")])

    def test_markers_carry_the_keys(self):
        from frc.ledgers import p22_quantum as L
        text = Path(L.__file__).read_text(encoding="utf-8")
        found = 0
        for line in text.splitlines():
            if re.match(r"\s*# 22:[A-Z]+\d+ \(p22\d{3}\)", line):
                for lab, key in re.findall(r"22:([A-Z]+\d+) \((p22\d{3})\)", line):
                    self.assertEqual(L.KEYS[lab], key); found += 1
        self.assertEqual(found, len(L.PREDICATES))

    @unittest.skipUnless((ROOT / "src" / "22-quantum" / "results.json").exists(), "the package src/22-quantum is not in this tree")
    def test_every_package_record_is_covered(self):
        from frc.ledgers import p22_quantum as L
        records = json.loads((ROOT / "src" / "22-quantum" / "results.json").read_text(encoding="utf-8"))
        self.assertEqual(len(records), 17)
        self.assertEqual({r["script"] for r in records}, set(L.SUITE.values()))
        for r in records:
            blocks = [b for b, s in L.SUITE.items() if s == r["script"]]
            cited = {x.strip() for pid, rows in L.LEDGER.items() if pid[0] in blocks for x in rows.split(",")}
            self.assertEqual({x.strip() for x in r["rows"].split(",")}, cited, r["id"])


if __name__ == "__main__":
    unittest.main()
