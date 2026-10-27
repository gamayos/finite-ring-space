"""frc/relaxation.py (the relaxation theme; 21-gravity): the Kuramoto form, the pulse law, the re-registration rule and
the framed readout a second way — the tally gradient by direct residue arithmetic at sampled points, the pulse word
against integer division and the Christoffel word, the odd kernels against the central difference, the accumulator's
run against its stated bounds, the readout map against 22-quantum's worked instance (23/54 at scale 4)."""
import random
import unittest
from fractions import Fraction
from math import isqrt

from frc import lattice as LT
from frc import relaxation as RX

class KuramotoFormTest(unittest.TestCase):
    """The Kuramoto form and the pulse law (21:C26, C27; Theme/Relaxation.lean) a second way: the tally gradient by
    direct residue arithmetic at sampled points, the pulse sequence against integer division and the Christoffel word."""
    def test_tally_gradient(self):
        for p in (5, 13, 17, 37):
            ok, pairs = RX.tally_gradient(p)
            self.assertTrue(ok); self.assertEqual(pairs, (p - 1) ** 2)
        p, z, g = 13, 5, 2
        w, h = pow(z, p - 2, p), pow(g, p - 2, p)
        self.assertEqual((2 + z * g + w * h - (2 + z * h + w * g)) % p, (g - h) * (z - w) % p)
        self.assertEqual((1 - z) * (1 - w) % p, (2 - z - w) % p)

    def test_pulse_sequence(self):
        for N, M in ((12, 5), (7, 3), (10, 10), (9, 1), (54, 23), (641, 114), (60, 0), (1, 1)):
            ok, word = RX.pulse_sequence(N, M)
            self.assertTrue(ok); self.assertEqual(len(word), N); self.assertEqual(word.count("1"), M)
            counts = [0]
            for ch in word: counts.append(counts[-1] + int(ch))
            self.assertEqual(counts, [(k * M) // N for k in range(N + 1)])
        self.assertFalse(RX.pulse_sequence(5, 7)[0])                            # more quanta than chronons: no unit-capacity word
        self.assertEqual(RX.pulse_sequence(12, 5)[1], "001010010101")

    def test_odd_kernels_and_leakage_form(self):
        for p, n in ((5, 4), (13, 7), (17, 5)):
            ok, count = RX.odd_kernels(p, n)
            self.assertTrue(ok); self.assertEqual(count, p)
        rng = random.Random(5)
        for n in (3, 4, 7, 12, 25):
            f = [rng.randint(-20, 20) for _ in range(n)]
            self.assertTrue(RX.bdiff_fdiff_identity(f, n)); self.assertTrue(RX.leakage_form_identity(f, n))
            Ff = RX.fdiff(f, n)
            self.assertEqual(sum(x * x for x in Ff), sum((f[(i + 1) % n] - f[i]) ** 2 for i in range(n)))
            self.assertEqual(RX.lap(f, n), [f[(i + 1) % n] + f[(i - 1) % n] - 2 * f[i] for i in range(n)])
        self.assertEqual(RX.kernel(1, 0, 12, [1, 2, 3], 3, 13), LT.cdiff([1, 2, 3], 3) and [x % 13 for x in LT.cdiff([1, 2, 3], 3)])
        self.assertNotEqual(RX.kernel(1, 1, 12, [1, 2, 3], 3, 13), [x % 13 for x in LT.cdiff([1, 2, 3], 3)])   # an even part is no multiple of Δ


class WindowTest(unittest.TestCase):
    """The pulse accumulator (21:C28) and the framed readout (21:C29)."""
    def test_accumulator(self):
        for N in (8, 12):
            M = RX.current_counts(N)
            mu0 = N // 2 - 1
            traj, word, accs = RX.relax(N, mu0, M, chronons=500)
            first = {}
            for t, mu in enumerate(traj): first.setdefault(mu, t)
            self.assertLessEqual(first[0], RX.budget(M, 81, mu0))
            self.assertEqual(sum(word[:first[0]]), mu0); self.assertEqual(sum(word[first[0]:]), 0)
            self.assertTrue(all(traj[t + 1] <= traj[t] <= traj[t + 1] + 1 for t in range(len(traj) - 1)))
            self.assertTrue(all(a < 81 for a in accs))
        # the pulse law at a constant rate on a long level: 57 pulses per 81 chronons
        counts = {mu: 57 for mu in range(-100, 101)}; counts[0] = 0
        traj, word, _ = RX.relax(400, 100, counts, chronons=81)
        self.assertEqual(sum(word), 57); self.assertEqual(RX.pulse_sequence(81, 57)[1], "".join(map(str, word)))

    def test_readout(self):
        r, s4 = RX.readout(Fraction(2, 8), Fraction(1, 8), 2)          # (2 + √2)/8, 22-quantum's Bell weight
        self.assertEqual((r, s4), (Fraction(23, 54), 114))
        self.assertTrue(RX.isqrt_bound(2 * 3 ** 8, 114)); self.assertFalse(RX.isqrt_bound(2 * 3 ** 8, 115))
        self.assertEqual(RX.count(81, Fraction(23, 54)), 35)             # the largest-remainder instance of 22-quantum (35 of 81)
        self.assertEqual(RX.count(81, Fraction(1, 2)), 41); self.assertEqual(RX.count(80, Fraction(1, 2)), 40)
        self.assertEqual(RX.current_counts(8)[1], 57); self.assertEqual(RX.current_counts(12)[2], 70)
        self.assertEqual(RX.current_counts(12, B=243, n=5)[2], 210)     # √3/2 at the next scale: s₅ = 420 = 3 s₄, the readout 70/81 again, 243 · 70/81 = 210
        for N in (8, 12): self.assertTrue(RX.gradient_on_stratum(N))


if __name__ == "__main__":
    unittest.main()
