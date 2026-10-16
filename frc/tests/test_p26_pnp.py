"""26-pnp's ledger file (frc/ledgers/p26_pnp.py, 16 October 2026) and the horizon theme's ladder (frc/ladder.py): the
ascent and the descent with their counts against pow and against each other, the index dynamics against the closed
form, the Gauss sum against the complex numbers, the transform against the matrix and against floating point, the
affine solver against exhaustion; the ledger file green, its markers on its deciding checks with the keys of the
generated table, every deciding check deciding what its label says (a mutated ladder fails it)."""
import cmath
import math
import random
import re
import unittest
from fractions import Fraction as Q
from math import isqrt
from pathlib import Path

from frc import arith
from frc import ladder as LD
from frc.quantum import Cyclotomic

ROOT = Path(__file__).resolve().parents[2]


class LadderTest(unittest.TestCase):
    def test_sqmul_against_pow_and_the_bound(self):
        rnd = random.Random(26)
        for p in (13, 101, 10007, 1000003):
            g = arith.primitive_root(p)
            for e in [0, 1, 2, p - 2, p // 3] + [rnd.randrange(p) for _ in range(50)]:
                v, ops = LD.sqmul(g, e, p)
                v2, ops2 = LD.sqmul_ltr(g, e, p)
                self.assertEqual(v, pow(g, e, p)); self.assertEqual(v2, pow(g, e, p))
                self.assertLessEqual(ops, 2 * LD.bits(e)); self.assertLessEqual(ops2, 2 * LD.bits(e))
                self.assertLessEqual(ops, 2 * p.bit_length())

    def test_bits_is_the_bit_length(self):
        for e in range(2000):
            self.assertEqual(LD.bits(e), len(bin(e)) - 2 if e else 0)
            self.assertTrue(2 ** (LD.bits(e) - 1) <= e < 2 ** LD.bits(e) if e else LD.bits(e) == 0)

    def test_bsgs_recovers_every_index(self):
        for p in (13, 17, 53, 101, 1009):
            g, n = arith.primitive_root(p), p - 1
            m = isqrt(n) + 1
            for x in range(n):
                i, j, giant = LD.bsgs(g, pow(g, x, p), p)
                self.assertEqual((j + m * i) % n, x)
                self.assertLess(j, m); self.assertLess(giant, m)
                self.assertTrue(LD.descends(g, pow(g, x, p), p, m))
                self.assertEqual(LD.dlog(g, pow(g, x, p), p), x)
            self.assertIsNone(LD.bsgs(g, 0, p))                      # 0 is no power of g
            self.assertFalse(LD.descends(g, 0, p, m))

    def test_bsgs_with_a_short_table_fails_honestly(self):
        # with m² < n some targets are out of reach: the verdict is False, never a wrong index
        p, g = 101, 2
        hits = sum(LD.descends(g, pow(g, x, p), p, 5) for x in range(100))
        self.assertLess(hits, 100)
        for x in range(100):
            res = LD.bsgs(g, pow(g, x, p), p, 5)
            if res is not None:
                i, j, _ = res
                self.assertEqual(pow(g, j + 5 * i, p), pow(g, x, p))

    def test_phase_index_and_tower(self):
        for p in (13, 101, 1009):
            g, n = arith.primitive_root(p), p - 1
            for m in range(n):
                for k in (2, 3, 5):
                    for r in range(4):
                        it, closed = LD.phase_index(g, m, k, r, p)
                        self.assertEqual(it, closed)
                        x = pow(g, m, p)
                        for _ in range(r): x = pow(x, k, p)
                        self.assertEqual(x, it)
            for j in range(n):
                a, b = LD.tower(g, j, p)
                self.assertEqual(a, b); self.assertEqual(a, pow(g, pow(g, j, p), p))

    def test_power_image_and_bezout(self):
        for p in (13, 101, 1009):
            n = p - 1
            g = arith.primitive_root(p)
            for k in range(1, 30):
                d, a, b = LD.bezout(k, n)
                self.assertEqual(d, math.gcd(k, n)); self.assertEqual(a * k, b * n + d)
                self.assertGreater(a, 0); self.assertGreaterEqual(b, 0)
                img = LD.power_image(k, p)
                self.assertEqual(len(img), n // d)
                self.assertEqual(img, sorted({pow(pow(g, d, p), i, p) for i in range(n // d)}))

    def test_recentre_and_index_table(self):
        for p in (13, 101):
            g, n = arith.primitive_root(p), p - 1
            tab = LD.index_table(g, p)
            self.assertEqual(sorted(tab), list(range(1, p)))
            for m in range(n):
                self.assertEqual(LD.recentre(n, m, m), 1 % n)
                self.assertEqual(sorted(LD.recentre(n, m, j) for j in range(n)), list(range(n)))
                self.assertEqual(tab[pow(g, m, p)], m)

    def test_gauss_sum_against_the_complex_numbers(self):
        for p in (13, 17):
            g, n = arith.primitive_root(p), p - 1
            N = p * n
            C = Cyclotomic(N)
            ind = {pow(g, t, p): t for t in range(n)}
            for nu in (1, 2, 3):
                G = sum(cmath.exp(2j * math.pi * nu * ind[x] / n) * cmath.exp(2j * math.pi * x / p) for x in range(1, p))
                self.assertLess(abs(abs(G) ** 2 - p), 1e-9)
                self.assertEqual(LD.gauss_norm(p, g, nu, C), C.const(p))
            Cp = Cyclotomic(p)
            for c in range(p):
                self.assertEqual(LD.ramanujan(p, c, Cp), Cp.const(n if c == 0 else -1))
            self.assertTrue(all(LD.mul_perm(c, p) for c in range(1, p)))
            self.assertFalse(LD.mul_perm(0, p))

    def test_ntt_against_the_matrix_and_the_fft(self):
        import numpy as np
        for q, n, w in ((17, 8, 2), (257, 256, 3), (7681, 256, pow(17, (7680) // 256, 7681))):
            self.assertEqual(pow(w, n, q), 1); self.assertEqual(pow(w, n // 2, q), q - 1)
            rnd = random.Random(q)
            a = [rnd.randrange(q) for _ in range(n)]
            A, ops = LD.ntt(a, w, q)
            self.assertEqual(A, [sum(a[t] * pow(w, k * t % n, q) for t in range(n)) % q for k in range(n)])
            self.assertEqual(ops, (n // 2) * (n.bit_length() - 1))
            b, _ = LD.intt(A, w, q)
            self.assertEqual(b, a)
            c1, o1 = LD.convolve_direct(a, a, q); c2, o2 = LD.convolve_ntt(a, a, w, q)
            self.assertEqual(c1, c2); self.assertEqual(o1, n * n); self.assertLess(o2, o1)
        # the cyclic convolution agrees with floating point on small integers
        n = 16; a = [1, 2, 3, 4] + [0] * 12; b = [5, 6, 7] + [0] * 13
        q, w = 65537, pow(3, 65536 // 16, 65537)
        c, _ = LD.convolve_ntt(a, b, w, q)
        f = np.rint(np.fft.ifft(np.fft.fft(a) * np.fft.fft(b)).real).astype(int).tolist()
        self.assertEqual(c, [x % q for x in f])

    def test_affine_f2_against_exhaustion(self):
        rnd = random.Random(2)
        for _ in range(60):
            m, n = rnd.randint(1, 5), rnd.randint(1, 7)
            rows = [[rnd.randint(0, 1) for _ in range(n + 1)] for _ in range(m)]
            res = LD.affine_f2(rows, n)
            sols = LD.f2_solutions(rows, n)
            if res is None:
                self.assertEqual(sols, [])
            else:
                w0, basis = res
                span = set()
                for mask in range(1 << len(basis)):
                    v = list(w0)
                    for t, bv in enumerate(basis):
                        if mask >> t & 1: v = [x ^ y for x, y in zip(v, bv)]
                    span.add(tuple(v))
                self.assertEqual(span, {tuple(s) for s in sols})
                self.assertEqual(len(sols), 2 ** len(basis))


class LedgerTest(unittest.TestCase):
    def test_ledger_file(self):
        from frc.ledgers import p26_pnp as L
        for b in sorted(L.BLOCK): L.R.run_block(b)
        self.assertTrue(L.R.summary(write=False, expect=list(L.LEDGER)))
        self.assertEqual({r["id"] for r in L.R.results}, set(L.LEDGER))
        for lab, pid in L.PREDICATES.items():
            self.assertIn(lab, L.LEDGER[pid], (lab, pid))
        self.assertEqual({r["kind"] for r in L.R.results if r["id"] in ("L2", "H1")}, {"CHART"})
        self.assertTrue(all(r["kind"] == "EXACT" for r in L.R.results if r["id"] not in ("L2", "H1")))

    def test_markers_carry_the_keys(self):
        from frc.ledgers import p26_pnp as L
        text = Path(L.__file__).read_text(encoding="utf-8")
        found = {}
        for line in text.splitlines():
            if re.match(r"\s*# 26:[A-Z]+\d+ \(p26\d{3}\)", line):
                for lab, key in re.findall(r"26:([A-Z]+\d+) \((p26\d{3})\)", line):
                    self.assertNotIn(lab, found, f"{lab}: two markers")
                    found[lab] = key
        self.assertEqual(set("26:" + lab for lab in found), set(L.PREDICATES))
        if L.KEYS:
            for lab, key in found.items(): self.assertEqual(L.KEYS[lab], key)

    def test_deciding_checks_decide(self):
        """Each deciding check fails when the computation it tests is wrong: the function it rests on (the ladder's, the
        horizon theme's `fixed_points`, the chart's `omega_bracket`) is replaced by a wrong one and the block re-run.
        L2 (the scalar -i(s + 1/2) in Q(i)[nu]) and C2 (the counting distances by `pow`) are inline arithmetic on the
        host's integers and rest on no function of the framework: a mutation cannot reach them."""
        from frc.ledgers import p26_pnp as L
        import frc.ladder as LDm
        import frc.horizon as HZm
        import frc.chart as CHm
        mutations = {
            "A1": (LDm, "sqmul", lambda b, e, p: (pow(b, e, p), 3 * LD.bits(e) + 1)),
            "D1": (LDm, "bsgs", lambda g, h, p, m=None: (0, 0, 0)),
            "R1": (LDm, "tower", lambda g, j, p: (pow(g, j, p), pow(g, j + 1, p))),
            "R2": (LDm, "phase_index", lambda g, m, k, r, p: (pow(g, m, p), pow(g, m + r, p))),
            "R3": (LDm, "bsgs", lambda g, h, p, m=None: (1, 0, 0)),
            "R4": (LDm, "power_image", lambda k, p: list(range(1, p))),
            "C1": (LDm, "recentre", lambda n, m, j: j),
            "C3": (LDm, "dlog", lambda g, h, p: 0),
            "T1": (LDm, "ntt", lambda a, w, q: (list(a), 0)),
            "W1": (LDm, "affine_f2", lambda rows, n: ([0] * n, [])),
            "L4": (LDm, "gauss_norm", lambda p, g, nu, C=None: (C or Cyclotomic(p * (p - 1))).const(p - 1)),
            "L1": (HZm, "fixed_points", lambda p, g, r: list(range(1, p))),
            "H1": (CHm, "omega_bracket", lambda: (Q(2 ** 405), Q(2 ** 405 + 1))),   # a bracket of 406 bits, below the import
        }
        for pid, (mod, name, bad) in mutations.items():
            orig = getattr(mod, name)
            setattr(mod, name, bad)
            try:
                L.R.results = [r for r in L.R.results if r["block"] != pid[0]]
                L.R._ran.discard(pid[0])
                L.R.run_block(pid[0])
                rec = next(r for r in L.R.results if r["id"] == pid)
                self.assertFalse(rec["ok"], f"{pid} stayed green with {name} mutated")
            finally:
                setattr(mod, name, orig)
                L.R.results = [r for r in L.R.results if r["block"] != pid[0]]
                L.R._ran.discard(pid[0])
        for b in sorted(L.BLOCK): L.R.run_block(b)
        self.assertTrue(all(r["ok"] for r in L.R.results))


if __name__ == "__main__":
    unittest.main()
