"""20-rh's ledger file (frc/ledgers/p20_rh.py; task LM36, rewritten with the paper on 17 October 2026): the horizon theme's
resonance arithmetic and the chart file frc/chart_rh.py, each value computed two ways; the ledger file green, its markers on
its deciding checks with the keys of the generated table, and its records those of the package's blocks A, D, G and X
(src/20-rh/results.json)."""
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
        for h in CR.HEIGHTS:                                                  # all eighty heights
            self.assertLess(abs(CR.hardy_z(h)), 1e-6)
        for t in (20.0, 40.0, 100.0):                                         # the Riemann–Siegel main sum within its remainder
            self.assertLess(abs(CR.z_horizon(t) - CR.hardy_z(t)), 1.5 * (t / (2 * math.pi)) ** -0.25)

    def test_exhibit_two_ways(self):
        labels, weights, mean = CR.window_weights(173, "mangoldt")
        self.assertEqual(sorted(labels), [n for n in range(2, 174) if H.prime_power_base(n)])
        for n, l in zip(labels, weights): self.assertAlmostEqual(l, math.log(H.prime_power_base(n)), places=12)
        self.assertEqual(CR.window_weights(13)[:2], ([2, 3, 5, 7, 11, 13], [1.0] * 6))
        for kind, sigma in (("primes", -0.5), ("mangoldt", -0.25)):                # the spectrum against the direct sum
            labels, weights, mean = CR.window_weights(39, kind); w = dict(zip(labels, weights))
            for t, v in zip((14.1, 21.1, 28.1), CR.spectrum(39, 14.1, 7.0, 3, kind, sigma)):
                direct = abs(sum((w.get(n, 0.0) - mean) * n ** complex(sigma, t) for n in range(1, 40)))
                self.assertAlmostEqual(v, direct, places=10)
        for s in (complex(-0.5, 14.13), complex(0.0, 51.7), complex(-1.0, 30.0)):   # the Euler–Maclaurin tail against the sum
            direct = sum(n ** s for n in range(2001, 30001))
            self.assertLess(abs(CR.power_tail(2001, 30000, s) - direct), 1e-10 * abs(direct))
        deep = CR.spectrum(30000, 14.0, 7.0, 3, "mangoldt")                         # the tail inside the spectrum
        labels, weights, mean = CR.window_weights(30000, "mangoldt"); w = dict(zip(labels, weights))
        for t, v in zip((14.0, 21.0, 28.0), deep):
            self.assertAlmostEqual(v, abs(sum((w.get(n, 0.0) - mean) * n ** complex(-0.5, t) for n in range(1, 30001))), places=7)
        self.assertEqual([round(t, 2) for t, _ in CR.peaks(13, 5, 10.0, 36.0)], [14.2, 20.85, 25.09, 30.3, 33.07])
        self.assertEqual(len(CR.maxima(10.0, 0.01, CR.spectrum(13, 10.0, 0.01, 2601))), 9)
        self.assertAlmostEqual(CR.expint(1.0).real, 1.8951178163559368, places=13)        # Ei(1) and Ei at a complex argument, as scipy.special.expi and mpmath.ei give them; the step of a label; the eighty heights
        self.assertLess(abs(CR.expint(complex(0.5, 60.0) * 0.4) - (-0.04667002980588406+3.121586046726238j)), 1e-12)
        self.assertLess(abs(CR.label_step(0.4, 60.0) - 1.0), 0.01); self.assertLess(abs(CR.label_step(-0.7, 60.0)), 0.01)
        self.assertEqual((len(CR.HEIGHTS), sum(1 for h in CR.HEIGHTS if h < 202.0)), (80, 80)); self.assertEqual(CR.HEIGHTS, sorted(CR.HEIGHTS))
        self.assertEqual(round(CR.window_count(13, 202.0, 12.5), 1), 5.0)        # five primes below 12.5
        self.assertEqual(CR.label_step(0.0, 60.0), math.atan(120.0) / math.pi)        # at the label itself: the middle of the step
        self.assertEqual(round(CR.window_count(13, 202.0, 13.0), 1), 5.5)        # at the label 13: six primes, less one half
        self.assertEqual(round(abs(CR.window_count(39, 78.0, 23.0) - CR.riemann_counts(23.0, [78.0])[0]), 3), 0.106)        # at a prime label the two counts differ by more than 0.10
        self.assertLess(abs(CR.vector_count([2, 3, 5], 50.0, 4.5) - 2.0), CR.count_bound([2, 3, 5], 4.5) / 50.0)        # the bound of 20:D17
        self.assertLess(abs(CR.vector_count([2, 3, 5], 50.0, 4.5, [1.5, -2.0, 4.0]) + 0.5), CR.count_bound([2, 3, 5], 4.5, [1.5, -2.0, 4.0]) / 50.0)        # a signed vector
        self.assertTrue(all(CR.polynomial_exact(B) for B in (1, 2, 7, 21)))        # the polynomial of 20:D18
        self.assertLess(CR.nearest_mode(CR.mode_table(13, [1, 4]), [0.3, 2.9]), 10 * 2 / 5)        # the primes 2 and 3 on the shell 13 (g = 2): B = 1
        self.assertAlmostEqual(CR.count_bound([2], 2.0 * math.e), math.sqrt(math.e) / math.pi, places=12)        # one label: √(x/n)/(π |log(x/n)|)
        self.assertLessEqual(max(CR.spectrum(3, 10.0, 0.5, 20, sigma=0.0)), 4 / 3 + 1e-12)   # depth 3 at σ = 0: E ≤ Σ|λ − λ̄| = 4/3
        self.assertTrue(all(CR.characters_parseval(13, 2, H.prime_power_base)[:4]))
        lam = {}; x = 1
        for m in range(12): lam[x] = m; x = x * 2 % 13
        mx, mean, rnd = CR.dlog_loading(13, [2, 3, 4, 8, 9], lam)
        self.assertAlmostEqual(mean, 5 - 5 * 4 / 11, places=9)                 # the exact mean |P| − |P|(|P|−1)/(p−2)
        self.assertAlmostEqual(rnd, 5 * math.log(12), places=12)

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
            if re.match(r"\s*# 20:[A-Z]+\d+ \(p\d{5}\)", line):
                for lab, key in re.findall(r"20:([A-Z]+\d+) \((p\d{5})\)", line):
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
        self.assertEqual(len(records), 99)        # the package of 23 November 2026: blocks A, D, G and X, with the circle's rows G13 and G14, the count's rows D16 and D17 and the rows D18 and D19 of the modes near the heights
        self.assertEqual([(r["id"], r["rows"], r["ok"], _ALIAS.get(r["kind"], r["kind"]), r["label"]) for r in records],
                         [(r["id"], r["rows"], r["ok"], r["kind"], r["label"]) for r in mine])


if __name__ == "__main__":
    unittest.main()
