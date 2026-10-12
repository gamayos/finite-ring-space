"""The fourier and projective themes' python (frc/fourier.py, frc/projective.py; task LM25): each value computed two
ways, and the master's block files fourier.py and projective.py green, their markers on their deciding checks."""
import unittest
from frc import arith
from frc.foundation import drive
from frc.fourier import transform, identity, matmul, matpow, projectors, frft, meridian
from frc import projective as PJ
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


class FibrationTest(unittest.TestCase):
    """The frame triple and the two fibrations (38:A9, X4, B6) at p = 5 and 13, each count a second way."""
    def test_triple_and_fibrations(self):
        for p in (5, 13):
            nu = next(a for a in range(2, p) if pow(a, (p - 1) // 2, p) == p - 1)
            n, d, b, bij = PJ.frame_triple(p, nu)
            self.assertTrue(bij); self.assertEqual(n, p * (p * p - 1))
            sp, ns = PJ.split_fibration(p), PJ.nonsplit_fibration(p, nu)
            self.assertEqual((sp["base"], ns["base"]), (p * (p + 1), p * (p - 1)))
            self.assertTrue(sp["orbit_is_quadric"] and sp["fibres_are_cosets"] and ns["section"] and ns["fibres"])
            self.assertEqual(len(PJ.circle(p)), p - 1)
            self.assertEqual(PJ.sphere(p, 1), p * (p + 1)); self.assertEqual(PJ.sphere(p, nu), p * (p - 1))
            self.assertEqual(PJ.involutions(p), (1, p * p))
            i = PJ.unit(p)
            self.assertEqual(i[0] * i[0] % p, p - 1)
            for M in pgl2(p)[:50]:
                self.assertEqual(PJ.conj(M, i, p), tuple(x * pow(det(M, p), -1, p) % p for x in mul(mul(M, i, p), PJ.adj(M, p), p)))


if __name__ == "__main__":
    unittest.main()
