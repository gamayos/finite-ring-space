"""The fourier and projective themes' python (frc/fourier.py, frc/projective.py; task LM25): each value computed two
ways, and the master's block files fourier.py and projective.py green, their markers on their deciding checks."""
import unittest
from frc import arith
from frc.foundation import drive
from frc.fourier import transform, identity, matmul, matpow, projectors, frft, meridian
from frc.projective import mul, det, act, normal, pclass, line, boost, borel, pgl2, factor

SHELLS = [p for p in range(5, 60) if p % 4 == 1 and arith.is_prime(p)]


class FourierTest(unittest.TestCase):
    def test_transform(self):
        for p in SHELLS:
            W, J, F = transform(p, drive(p))
            self.assertEqual(matmul(F, F, p), J)
            self.assertEqual(matmul(W, W, p), [[(-v) % p for v in row] for row in J])
            self.assertEqual(matpow(F, 4, p), identity(p - 1))

    def test_projectors(self):
        for p in SHELLS[:4]:
            g = drive(p); n = p - 1; i = (-pow(g, n // 4, p)) % p
            _, _, F = transform(p, g)
            P = projectors(p, g)
            S = [[sum(P[l][k][j] for l in range(4)) % p for j in range(n)] for k in range(n)]
            self.assertEqual(S, identity(n))                                        # Σ Π_ℓ = I
            for l in range(4):
                for m in range(4):
                    PP = matmul(P[l], P[m], p)
                    self.assertEqual(PP, P[l] if l == m else [[0] * n for _ in range(n)])
                self.assertEqual(matmul(F, P[l], p), [[pow(i, l, p) * v % p for v in row] for row in P[l]])   # eigenvalue i^ℓ

    def test_frft(self):
        for p in SHELLS[:4]:
            g = drive(p); P = projectors(p, g); F1 = frft(p, g, 1, P)
            for s in range(p - 1):
                self.assertEqual(frft(p, g, s, P), matpow(F1, s, p))                # second method: powers of F^[1]

    def test_meridian(self):
        p, g, k = 13, 2, 3
        self.assertEqual(meridian(p, g, k, 2), [0, 4, 8, 12, 3, 7, 11])           # 6:D5's ladder


class ProjectiveTest(unittest.TestCase):
    def test_pgl2_count(self):
        for p in (5, 13):
            self.assertEqual(len(pgl2(p)), p * (p * p - 1))

    def test_factor(self):
        for p in (5, 13, 17):
            nu = arith.nonresidue(p)
            for M in pgl2(p)[::7]:
                N, (a, b, e), (al, be) = factor(M, nu, p)
                self.assertEqual(tuple(N * v % p for v in M), mul(borel(a, b, e, p), boost(nu, al, be, p), p))
                self.assertEqual(det(mul(M, M, p), p), det(M, p) ** 2 % p)

    def test_action(self):
        p = 13
        for M in pgl2(p)[::11]:
            imgs = {normal(act(M, P, p), p) for P in line(p)}
            self.assertEqual(len(imgs), p + 1)                                      # a bijection of ℙ¹
            self.assertEqual(pclass(pclass(M, p), p), pclass(M, p))


class MasterBlockFilesTest(unittest.TestCase):
    def test_block_files(self):
        from frc.ledgers.master import fourier as L1, projective as L2
        for L in (L1, L2):
            self.assertTrue(L.R.verify_all())
            marks = L.R.markers()
            for lab in L.R.predicates: self.assertIn(lab, marks)
            self.assertEqual(sorted(L.PROOFS), sorted(L.LEAN))
            self.assertEqual(L.BLOCK, "C")


if __name__ == "__main__":
    unittest.main()
