"""20-rh's ledger file (frc/ledgers/p20_rh.py; task LM36): the horizon theme's resonance arithmetic and the chart file
frc/chart_rh.py, each value computed two ways; the ledger file green, its markers on its deciding checks with the keys of
the generated table, and its records those of the package's blocks A, B and E (src/20-rh/results.json)."""
import cmath
import io
import json
import math
import re
import unittest
from contextlib import redirect_stdout
from fractions import Fraction as Q
from pathlib import Path

from frc import arith
from frc import chart_rh as CR
from frc import horizon as H

ROOT = Path(__file__).resolve().parents[2]


class ResonanceTest(unittest.TestCase):
    def test_mobius_phi_and_prime_powers(self):
        mu, phi = H.mobius_phi(600)
        for n in range(1, 601):
            f = arith.factorize(n) if n > 1 else {}
            self.assertEqual(phi[n], arith.phi(n))
            self.assertEqual(mu[n], 0 if any(e > 1 for e in f.values()) else (-1) ** len(f))
            self.assertEqual(H.prime_power_base(n), next(iter(f)) if len(f) == 1 else None)

    def test_ramanujan_sum_two_ways(self):
        mu, phi = H.mobius_phi(200)
        for q in range(1, 41):
            for n in range(0, 41):
                g = math.gcd(q, n) if n else q                                  # von Sterneck's closed form
                von_sterneck = mu[q // g] * phi[q] // phi[q // g]
                self.assertEqual(H.ramanujan_c(q, n, mu), von_sterneck, (q, n))
                direct = sum(cmath.exp(2j * math.pi * a * n / q) for a in range(1, q + 1) if math.gcd(a, q) == 1)
                self.assertLess(abs(direct - H.ramanujan_c(q, n, mu)), 1e-9)

    def test_resonance_and_mangoldt(self):
        mu, phi = H.mobius_phi(200)
        cum = H.resonance(30, 20, mu, phi)
        for L in (1, 7, 30):
            for n in range(1, 21):
                self.assertEqual(cum[L][n], sum(Q(mu[q], phi[q]) * H.ramanujan_c(q, n, mu) for q in range(1, L + 1)))
        for n in range(2, 200):
            exact = H.log_free_mangoldt(n, mu)
            self.assertEqual(exact, H.prime_power_base(n) or 1)
            self.assertAlmostEqual(math.log(exact), -sum(mu[d] * math.log(d) for d in H.divisors(n) if d > 1), places=12)


class ChartTest(unittest.TestCase):
    def test_fft_against_the_sum(self):
        for n in (1, 2, 6, 12, 13, 36, 52):
            a = [math.sin(3 * k + 1) for k in range(n)]
            F = CR.fft(a)
            for k in range(n):
                self.assertLess(abs(F[k] - sum(a[m] * cmath.exp(-2j * math.pi * k * m / n) for m in range(n))), 1e-9)

    def test_lanczos_spectrum(self):
        x = [1.5, 2.25, 3.0, 7.75, 11.0, 11.5]
        a, b, ev = CR.lanczos(x)
        self.assertLess(max(abs(u - v) for u, v in zip(ev, x)), 1e-12)
        self.assertAlmostEqual(sum(a), sum(x), places=12)                     # the trace

    def test_hardy_z_at_the_heights(self):
        for h in CR.HEIGHTS[:10]:
            self.assertLess(abs(CR.hardy_z(h)), 1e-6)
        for t in (20.0, 40.0, 100.0):                                         # the Riemann–Siegel main sum within its remainder
            self.assertLess(abs(CR.z_horizon(t) - CR.hardy_z(t)), 1.5 * (t / (2 * math.pi)) ** -0.25)

    def test_characters_and_correlations(self):
        self.assertTrue(all(CR.characters(13, 2, H.prime_power_base)[:3]))
        g = arith.primitive_root(1009); dlog, x = {}, 1
        for k in range(1008): dlog[x] = k; x = x * g % 1009
        m, floor, corr = CR.mode_correlations(1009, dlog, arith.is_prime)
        self.assertAlmostEqual(math.sqrt(sum(c * c for c in corr) / len(corr)), floor, delta=1e-3)   # Parseval: the mean square


class LedgerTest(unittest.TestCase):
    def test_ledger_file(self):
        from frc.ledgers import p20_rh as L
        with redirect_stdout(io.StringIO()):
            self.assertTrue(L.R.verify_all())
        marks = L.R.markers()
        for lab in L.R.predicates: self.assertIn(lab, marks)
        self.assertEqual(L.PAPER, "20-rh")
        for lab, pid in L.PREDICATES.items():                               # each deciding check cites its predicate
            self.assertIn(lab, [x.strip() for x in L.LEDGER[pid].split(",")])
        for lab in L.LEAN:                                                  # every Lean row has a python check, or is Lean-only
            self.assertTrue(f"20:{lab}" in L.PREDICATES or lab in L.LEAN_ONLY, lab)

    def test_markers_carry_the_keys(self):
        from frc.ledgers import p20_rh as L
        text = Path(L.__file__).read_text(encoding="utf-8")
        found = 0
        for line in text.splitlines():
            if re.match(r"\s*# 20:[A-Z]+\d+ \(p20\d{3}\)", line):
                for lab, key in re.findall(r"20:([A-Z]+\d+) \((p20\d{3})\)", line):
                    self.assertEqual(L.KEYS[lab], key); found += 1
        self.assertEqual(found, len(L.PREDICATES))

    @unittest.skipUnless((ROOT / "src" / "20-rh" / "results.json").exists(), "the package src/20-rh is not in this tree")
    def test_records_are_the_package_records(self):
        from frc.ledgers import p20_rh as L
        from frc.registry import _ALIAS
        records = [r for r in json.loads((ROOT / "src" / "20-rh" / "results.json").read_text(encoding="utf-8")) if r["block"] in L.BLOCK]
        with redirect_stdout(io.StringIO()):
            L.R.verify_all()
        mine = L.R.results
        self.assertEqual(len(records), 73)
        self.assertEqual([(r["id"], r["rows"], r["ok"], _ALIAS.get(r["kind"], r["kind"]), r["label"]) for r in records],
                         [(r["id"], r["rows"], r["ok"], r["kind"], r["label"]) for r in mine])


if __name__ == "__main__":
    unittest.main()
