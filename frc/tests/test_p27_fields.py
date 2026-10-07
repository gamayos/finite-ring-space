"""The ledger file of 27-fields (frc/ledgers/p27_fields.py; task LM35), the interactions theme's exact algebra it uses
(frc/interactions.py) and the chart file of its readings (frc/chart_fields.py): each helper computed two ways, and the
ledger green, its markers on its deciding checks, its checks covering the package's 28 records row for row and class
for class."""
import json
import math
import re
import unittest
from collections import Counter
from fractions import Fraction
from pathlib import Path

from frc import arith
from frc import interactions as I
from frc import chart_fields as CF

ROOT = Path(__file__).resolve().parents[2]


class AlgebraTest(unittest.TestCase):
    def test_poly(self):
        names = ("i", "g")
        i, g = I.Poly.var(names, "i"), I.Poly.var(names, "g")
        self.assertEqual((g + i) * (g - i), g * g + 1)
        self.assertEqual((i * g).conj(), -(i * g))
        self.assertEqual(((g + i) ** 2).real(), g * g - 1)
        self.assertTrue((i * i + 1).is_zero())

    def test_cyclotomic(self):
        for n in range(1, 31):
            f = I.cyclotomic(n)
            self.assertEqual(len(f) - 1, arith.phi(n))
            prod = [1]                                       # x^n − 1 = Π_{d | n} Φ_d
            for d in range(1, n + 1):
                if n % d == 0:
                    c = I.cyclotomic(d)
                    prod = [sum(prod[i] * c[k - i] for i in range(len(prod)) if 0 <= k - i < len(c)) for k in range(len(prod) + len(c) - 1)]
            self.assertEqual(prod, [-1] + [0] * (n - 1) + [1])
        for N in range(2, 16):
            for k in range(2 * N):
                self.assertEqual(I.cyclo_zero(I.char_sum(N, k), N), k % N != 0)

    def test_cos_and_green(self):
        for L in (1, 2, 3, 4, 6):
            for m in range(L):
                self.assertAlmostEqual(float(I.cos_rational(m, L)), math.cos(2 * math.pi * m / L), places=14)
        for L in (3, 4, 6):
            pts = [(0, 0, 0), (0, 0, 1), (0, 1, 1), (1, 1, 1)]
            fl = CF.green_points(L, pts)
            for p in pts:
                self.assertAlmostEqual(float(I.green_exact(L, p)), fl[p], places=12)
        self.assertEqual(I.green_exact(4, (1, 0, 0)), Fraction(257, 7680))

    def test_maxwell(self):
        pars, rows = I.maxwell_constraints(4)
        c = I.maxwell_form(4)
        self.assertTrue(all(sum(r.get(a, 0) * c[a] for a in r) == 0 for r in rows))
        S0, S2 = I.symbol_taylor(I.kernel_of(c))
        P = I.transverse_projector()
        self.assertTrue(all(x == 0 for r in S0 for x in r))
        self.assertEqual(S2, [[[[x / 2 for x in b] for b in a] for a in m] for m in P])
        basis = I.nullspace(rows, len(pars))
        self.assertEqual(len(basis), 2)
        self.assertEqual(len(pars) - I.rank_mod(rows, len(pars), 2147483647), 2)

    def test_unitary_groups(self):
        def order_U(n, q):
            r = q ** (n * (n - 1) // 2)
            for k in range(1, n + 1): r *= q ** k - (-1) ** k
            return r
        for (n, F) in ((2, I.Fq2(3, 0, 2)), (3, I.Fq2(2, 1, 1)), (2, I.Fq2(5, 0, 2))):
            q = F.q
            U = I.unitary_frames(F, n, det_one=False)
            self.assertEqual(len(U), order_U(n, q))
            self.assertEqual(len(I.unitary_frames(F, n)), order_U(n, q) // (q + 1))
            count = 1
            for m in range(1, n + 1): count *= I.unit_vectors(F, m)
            self.assertEqual(count, order_U(n, q))

    def test_binary_tetrahedral(self):
        G = I.binary_tetrahedral(); Gs = set(G)
        self.assertEqual(len(Gs), 24)
        self.assertTrue(all(I.qmul(x, y) in Gs and I.qconj(x) in Gs for x in G for y in G))
        one = (1, 0, 0, 0)
        def order(x):
            k, y = 1, x
            while y != one: y = I.qmul(y, x); k += 1
            return k
        self.assertEqual(Counter(order(x) for x in G), Counter({1: 1, 2: 1, 3: 8, 4: 6, 6: 8}))

    def test_c1(self):
        G = I.binary_tetrahedral(); traces = Counter(int(2 * x[0]) for x in G)
        N, D = I.c1_from_traces(traces, 2)
        mom = [Fraction(sum(m * t ** k for t, m in traces.items()), 24) for k in range(8)]
        ser = I.moment_c1_series(mom, 2, 7)
        for beta in (0.05, 0.3, 1.0, 2.5):
            x = math.exp(beta / 2)
            closed = sum(float(c) * x ** k for k, c in enumerate(N)) / sum(float(c) * x ** k for k, c in enumerate(D))
            self.assertAlmostEqual(closed, CF.c1_traces(traces, 2, beta), places=12)
            if beta < 0.1:
                self.assertAlmostEqual(sum(float(c) * beta ** k for k, c in enumerate(ser)), closed, places=10)
        r = I.bessel_ratio_series(0, 8)                      # I₁/I₀ against the chart's Bessel sums
        self.assertAlmostEqual(sum(float(c) * 0.05 ** k for k, c in enumerate(r)), CF.bessel_I(1, 0.05) / CF.bessel_I(0, 0.05), places=11)

    def test_su3_moments(self):
        self.assertEqual([I.su3_moment(k, k) for k in range(4)], [1, 1, 2, 6])
        self.assertEqual((I.su3_moment(3, 0), I.su3_moment(2, 1), I.su3_moment(1, 0)), (1, 0, 0))


class ChartFieldsTest(unittest.TestCase):
    def test_axis(self):
        L = 12
        G = CF.green_axis(L, (1, 2, 3))
        P = CF.green_points(L, [(0, 0, 1), (0, 0, 2), (0, 0, 3)])
        for g, p in zip(G, ((0, 0, 1), (0, 0, 2), (0, 0, 3))): self.assertAlmostEqual(g, P[p], places=13)

    def test_readings(self):
        self.assertLess(CF.quadrature_error(200), CF.quadrature_error(100))
        r1, _ = CF.window_residue(10, seed=1)
        self.assertAlmostEqual(r1, 10 * abs(1 - math.cos(0.025) - 0.05 ** 2 / 8), places=15)
        self.assertAlmostEqual(CF.c1_su3(0.1), 0.1 / 18 + 0.01 / 216, places=6)


class LedgerTest(unittest.TestCase):
    def test_ledger_file(self):
        from frc.ledgers import p27_fields as L
        self.assertTrue(L.R.verify_all())
        self.assertEqual(L.PAPER, "27-fields")
        self.assertEqual(L.LEAN, {})
        src = (ROOT / "frc" / "ledgers" / "p27_fields.py").read_text(encoding="utf-8").split("\n")
        marks = L.R.markers()
        for lab, pid in L.R.predicates.items():
            self.assertIn(lab, marks)
            line = next(j for j in range(marks[lab][1], len(src)) if src[j].strip())
            self.assertIn(f'ck("{pid}"', src[line], lab)        # the marker sits on its deciding check
            self.assertIn(f"{lab} ({L.KEYS[lab.split(':')[1]]})", src[marks[lab][1] - 1])

    @unittest.skipUnless((ROOT / "src" / "27-fields" / "results.json").exists(), "the package src/27-fields is not in this tree")
    def test_package_records(self):
        """Every record of the package's results.json is reproduced: its rows are the union of its checks' rows, its class
        is theirs, and every row a check cites names the record's script in its source cell."""
        from frc.ledgers import p27_fields as L
        recs = {r["id"]: r for r in json.loads((ROOT / "src" / "27-fields" / "results.json").read_text(encoding="utf-8"))}
        self.assertEqual(sorted("fld." + f for f in set(L.FAMILY.values())), sorted(recs))
        self.assertEqual(sorted(L.FAMILY), sorted(L.LEDGER))
        rows = {}
        for pid, fam in L.FAMILY.items():
            rows.setdefault(fam, set()).update(t.strip() for t in L.LEDGER[pid].split(","))
            self.assertEqual(L.KIND[fam], recs["fld." + fam]["kind"], pid)
        for fam, rs in rows.items():
            self.assertEqual(rs, {t.strip() for t in recs["fld." + fam]["rows"].split(",")}, fam)
        led = json.loads((ROOT / "docs" / "27-fields" / "27-fields-ledger.json").read_text(encoding="utf-8"))
        source = {r["label"]: re.sub(r"\\allowbreak|\s|\\", "", r.get("source") or "") for b in led["blocks"] for r in b["rows"]}
        for pid, fam in L.FAMILY.items():
            for t in L.LEDGER[pid].split(","):
                self.assertIn("src{fld." + fam + "}", source[t.strip().split(":")[1]], (pid, t))


if __name__ == "__main__":
    unittest.main()
