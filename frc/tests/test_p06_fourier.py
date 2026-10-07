"""6-fourier's ledger file (frc/ledgers/p06_fourier.py; task LM36): the fourier theme's ranks, shift and monomial test and
the chart file frc/chart_fourier.py, each value computed two ways; the ledger file green, its markers on its deciding
checks with the keys of the generated table, and its records those of the package (src/6-fourier/results.json)."""
import io
import json
import math
import random
import re
import unittest
from contextlib import redirect_stdout
from pathlib import Path

from frc import arith
from frc import chart_fourier as CF
from frc import fourier as FT

ROOT = Path(__file__).resolve().parents[2]
_RUN = {}


def ledger():
    """The ledger file, run once per session (its blocks take about a minute)."""
    from frc.ledgers import p06_fourier as L
    if "ok" not in _RUN:
        with redirect_stdout(io.StringIO()):
            _RUN["ok"] = L.R.verify_all()
    return L


class ThemeTest(unittest.TestCase):
    def test_rank_two_ways(self):
        rnd = random.Random(6)
        for p in (5, 13, 17):
            for _ in range(20):
                n = rnd.randint(1, 6)
                A = [[rnd.randrange(p) for _ in range(n)] for _ in range(n)]
                det = 0                                                      # the rank is full iff the determinant is nonzero
                if n == 1: det = A[0][0] % p
                else:
                    from itertools import permutations
                    for perm in permutations(range(n)):
                        sgn = (-1) ** sum(1 for i in range(n) for j in range(i + 1, n) if perm[i] > perm[j])
                        det += sgn * math.prod(A[i][perm[i]] for i in range(n))
                    det %= p
                self.assertEqual(FT.rank_mod(A, p) == n, det != 0)
            self.assertEqual(FT.rank_mod([[1, 2], [2, 4]], p), 1 if p != 2 else 1)

    def test_shift_and_monomial(self):
        for n in (4, 12):
            S = FT.shift_matrix(n)
            self.assertTrue(FT.is_monomial(S))
            v = list(range(n))
            self.assertEqual([sum(S[k][j] * v[j] for j in range(n)) for k in range(n)], [v[(k - 1) % n] for k in range(n)])
            self.assertEqual(FT.matpow(S, n, 97), FT.identity(n))
        self.assertFalse(FT.is_monomial([[1, 1], [0, 1]]))


class ChartTest(unittest.TestCase):
    def test_readout_projectors(self):
        R = CF.Readout(12)
        for l in range(4):                                                   # Σ Π_ℓ = I and the columns of F^[s] two ways
            for a in range(12):
                self.assertLess(abs(sum(R.P[m][a][a] for m in range(4)) - 1), 1e-9)
        M = R.matrix(5)
        for j in range(12):
            self.assertLess(max(abs(x - M[a][j]) for a, x in enumerate(R.column(5, j))), 1e-12)

    def test_entropy_and_gauss(self):
        self.assertAlmostEqual(CF.entropy([1, 1, 1, 1]), math.log(4), places=12)
        self.assertEqual(CF.entropy([0, 1, 0]), 0.0)
        for n in (4, 12, 16, 28):
            self.assertLess(CF.gauss_square(n), 1e-9)


class LedgerTest(unittest.TestCase):
    def test_ledger_file(self):
        L = ledger()
        self.assertTrue(_RUN["ok"])
        marks = L.R.markers()
        for lab in L.R.predicates: self.assertIn(lab, marks)
        self.assertEqual(L.PAPER, "6-fourier")
        for lab, pid in L.PREDICATES.items():
            self.assertIn(lab, [x.strip() for x in L.LEDGER[pid].split(",")])
        for lab in L.LEAN:
            self.assertTrue(f"6:{lab}" in L.PREDICATES or lab in L.LEAN_ONLY, lab)
        self.assertEqual(arith.primitive_root(41), 6)

    def test_markers_carry_the_keys(self):
        from frc.ledgers import p06_fourier as L
        text = Path(L.__file__).read_text(encoding="utf-8")
        found = 0
        for line in text.splitlines():
            if re.match(r"\s*# 6:[A-Z]+\d+ \(p06\d{3}\)", line):
                for lab, key in re.findall(r"6:([A-Z]+\d+) \((p06\d{3})\)", line):
                    self.assertEqual(L.KEYS[lab], key); found += 1
        self.assertEqual(found, len(L.PREDICATES))

    @unittest.skipUnless((ROOT / "src" / "6-fourier" / "results.json").exists(), "the package src/6-fourier is not in this tree")
    def test_records_are_the_package_records(self):
        from frc.registry import _ALIAS
        L = ledger()
        records = json.loads((ROOT / "src" / "6-fourier" / "results.json").read_text(encoding="utf-8"))
        self.assertEqual(len(records), 39)
        self.assertEqual([(r["id"], r["rows"], r["ok"], _ALIAS.get(r["kind"], r["kind"]), r["label"]) for r in records],
                         [(r["id"], r["rows"], r["ok"], r["kind"], r["label"]) for r in L.R.results])


if __name__ == "__main__":
    unittest.main()
