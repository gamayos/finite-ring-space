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
        self.assertEqual(sorted(L2.PREDICATES), ["00:C19", "00:C22", "00:C27"])      # C22 and C27 bound 20 October 2026
        self.assertTrue(all(v == "core" for v in L2.LEAN.values()))
        kinds = {r["id"]: r["kind"] for r in L2.R.results}
        self.assertTrue(all(k == "EXACT" for k in kinds.values()))


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


class SpinTest(unittest.TestCase):
    """The frame group has one form and the adjoint action (00:C27, 00:C22; frc/projective.py's Spin section, 20 October 2026):
    each record a second way — the unitary condition against the symplectic identity Mᵀ J M = det(M) J, the census against
    the class equation, the quadric counts against the character sums, SO₃ against the quadric's orbit count."""
    def test_unitary(self):
        from frc.extension import Ext
        for p in (5, 13):
            nu = next(a for a in range(2, p) if pow(a, (p - 1) // 2, p) == p - 1)
            K = Ext(p, nu); H, herm = PJ.hermitian_wJ(p, nu)
            self.assertTrue(herm)
            J = (K.scalar(0), K.scalar(1), K.scalar(p - 1), K.scalar(0))
            for M in PJ.sl2(p)[::max(1, p * p)] + [(1, 1, 0, 1), (2, 3, 1, 2 if p == 5 else 2)]:
                if (M[0] * M[3] - M[1] * M[2]) % p != 1: continue
                A = PJ.embed(K, M)
                # Mᵀ J M = det(M) J = J on SL₂, hence unitary for wJ
                At = (A[0], A[2], A[1], A[3])
                self.assertEqual(PJ.xmul(K, PJ.xmul(K, At, J), A), J)
                self.assertTrue(PJ.unitary(K, H, A))
            # a non-rational element of SL₂(𝔽_{p²}) is not unitary
            w = (0, 1); a = (1, 1); b = w; c = K.scalar(0); d = K.inv(a)
            self.assertEqual(PJ.xdet(K, (a, b, c, d)), K.scalar(1))
            self.assertFalse(PJ.unitary(K, H, (a, b, c, d)))
        self.assertEqual(PJ.su2_is_sl2(5, 2, full=True), (True, 120, 15600, 120))
        self.assertEqual(PJ.su2_identity_count(5, 2), 120)

    def test_census_and_quadrics(self):
        for p in (5, 13):
            nu = next(a for a in range(2, p) if pow(a, (p - 1) // 2, p) == p - 1)
            counts, expected, orders, inv = PJ.element_census(p)
            self.assertEqual(counts, expected); self.assertEqual(sum(counts.values()), p ** 3 - p); self.assertEqual(inv, 1)
            self.assertEqual(orders["unip+"], {p}); self.assertEqual(orders["unip-"], {2 * p})
            s4, s31, h3, s22, fr, ci, hy = PJ.quadric_counts(p, nu)
            # the character sums: #{x² + y² + z² + w² = 1} = p³ − p on p = 4κ + 1, the circle p − 1, the hyperbola p + 1
            self.assertEqual({s4, s31, h3, s22, fr}, {p ** 3 - p}); self.assertEqual((ci, hy), (p - 1, p + 1))
            r = PJ.unit(p)[0]
            self.assertEqual(PJ.psl2_image(p, r), (p * (p * p - 1) // 2, p * (p * p - 1)))

    def test_so3(self):
        for p in (5, 13):
            n_img, n_g, dets, orth, O3 = PJ.so3(p)
            self.assertEqual((n_img, n_g, dets, orth), (p * (p * p - 1), p * (p * p - 1), {1}, True))
            self.assertEqual(O3, 2 * p * (p * p - 1))
            # |O₃| a second way: |O(Q)| = 2·|SO₃| and |SO₃| = |PGL₂| = (points of the unit quadric a² + bc = 1) × |stabiliser C_{p−1}|
            self.assertEqual(O3 // 2, p * (p + 1) * (p - 1))
            syl, nU, gen, tin = PJ.no_section_split(p)
            self.assertEqual((syl, nU, gen), (p + 1, p * (p - 1), p * (p * p - 1) // 2)); self.assertTrue(tin)


if __name__ == "__main__":
    unittest.main()
