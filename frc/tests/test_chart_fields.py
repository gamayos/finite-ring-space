"""The chart file of 27-fields (frc/chart_fields.py): the continuum readings the ledger file's CHART checks read, at
their known values (the 27-fields migration, 16 October 2026). The lattice Coulomb coefficient ratio 1.004, the U(1)
string tension σ(0.5) = 1.4168, the measured Koide Q = 0.66666 and ρ² = 0.5, the v scale 247.2 GeV, and the readings
against their exact counterparts in frc/interactions.py."""
import math
import unittest
from fractions import Fraction

from frc import chart_fields as CF
from frc import interactions as I


class CoulombTest(unittest.TestCase):
    def test_coulomb_fit(self):
        C, target, resid, g0 = CF.coulomb_fit(128)
        self.assertAlmostEqual(target, 1 / (4 * math.pi), places=15)
        self.assertAlmostEqual(C / target, 1.004, places=3)
        self.assertLess(resid, 0.02)
        self.assertAlmostEqual(g0, 0.2510, places=4)

    def test_sign_dichotomy(self):
        seps, Uem, Ugr = CF.sign_dichotomy(48)
        self.assertEqual(seps, [6, 8, 10, 12, 16, 20])
        self.assertEqual([-u for u in Uem], Ugr)
        self.assertTrue(all(a > b > 0 for a, b in zip(Uem, Uem[1:])))

    def test_saturation(self):
        self.assertAlmostEqual(CF.saturation_core() ** 2, 1 / (4 * math.pi), places=15)
        self.assertAlmostEqual(20 * CF.saturation_potential(20), 1 / (4 * math.pi), delta=0.001)


class StrongTest(unittest.TestCase):
    def test_string_tension(self):
        self.assertAlmostEqual(CF.sigma_U1(0.5), 1.4168, places=4)
        self.assertAlmostEqual(CF.sigma_U1(0.5), -math.log(CF.bessel_I(1, 0.5) / CF.bessel_I(0, 0.5)), places=14)
        self.assertAlmostEqual(CF.sigma_ZN(0.5, 400), CF.sigma_U1(0.5), places=12)      # Z_N → U(1) as N grows
        betas = (0.2, 0.5, 1.0, 2.0, 4.0)
        s = [CF.sigma_U1(b) for b in betas]
        self.assertTrue(all(a > b > 0 for a, b in zip(s, s[1:])))
        self.assertTrue(all(CF.sigma_ZN(b, 3) > 0 for b in betas))

    def test_c1_against_exact(self):
        _, _, _, traces = I.tetrahedral_quaternions()
        N, D, _ = I.area_law_rational()
        for beta in (0.2, 0.5, 1.0, 2.5):
            x = math.exp(beta / 2)
            closed = sum(float(c) * x ** k for k, c in enumerate(N)) / sum(float(c) * x ** k for k, c in enumerate(D))
            self.assertAlmostEqual(CF.c1_traces(traces, 2, beta), closed, places=12)
        self.assertAlmostEqual(CF.c1_traces(traces, 2, 0.5), 0.1237, places=4)
        self.assertAlmostEqual(CF.c1_su3(0.1), 0.1 / 18 + 0.01 / 216, places=6)
        a, b, _ = CF.su3_fit()
        self.assertAlmostEqual(a, 1 / 18, places=4)
        self.assertAlmostEqual(b, 1 / 216, places=4)

    def test_qcd_scale(self):
        lam = CF.lambda_qcd(Fraction(23, 3))                                     # b₀ at n_f = 5
        self.assertTrue(0.05 < lam < 0.5)
        self.assertAlmostEqual(CF.proton_planck_exponent(), 88.0, delta=0.1)


class ScalesTest(unittest.TestCase):
    def test_v_scale(self):
        r = CF.v_scale()
        self.assertAlmostEqual(r["v1"], 247.2, delta=0.1)
        self.assertAlmostEqual(r["vc"], 87.4, delta=0.05)
        self.assertAlmostEqual(r["v1"] / r["vc"], 2 ** 1.5, places=12)
        self.assertAlmostEqual(r["b_fit_MW"], 2.0, delta=0.01)
        self.assertTrue(1e8 < r["L_b2"] < 1e9)

    def test_unification(self):
        self.assertTrue(1e12 < CF.unification_scale() < 1e14)

    def test_o2_numbers(self):
        inv_bare, hier, gap = CF.o2_numbers()
        self.assertAlmostEqual(inv_bare, 4 * math.pi, places=14)
        self.assertAlmostEqual(gap, 10.905, places=3)
        self.assertAlmostEqual(hier / 1.2355e36, 1, places=3)


class CorrespondenceReadingsTest(unittest.TestCase):
    def test_low_curvature(self):
        xs = (Fraction(1, 2), Fraction(-1, 2))
        for eps in (0.1, 0.01, 0.001):
            self.assertAlmostEqual(CF.s_fund_diag(xs, eps) / eps ** 2, 1 / 8, delta=eps ** 2)
        r10, _ = CF.window_residue(10, seed=10); r100, _ = CF.window_residue(100, seed=100)
        self.assertAlmostEqual(r100 / r10, 10, delta=0.5)

    def test_quadrature(self):
        e = [CF.quadrature_error(N) for N in (50, 100, 200)]
        self.assertTrue(e[0] > e[1] > e[2] > 0)


class FlavourTest(unittest.TestCase):
    def test_koide(self):
        Qm, r2 = CF.koide_measured()
        self.assertAlmostEqual(Qm, 0.66666, places=5)
        self.assertAlmostEqual(r2, 0.5, places=4)

    def test_winding(self):
        ov = CF.winding_overlaps(60, 12)
        self.assertAlmostEqual(ov[0], 1.0, places=15)
        self.assertTrue(all(a > b for a, b in zip(ov, ov[1:])))
        self.assertAlmostEqual(ov[5], 0.0, places=12)                              # k T = N: a full winding


if __name__ == "__main__":
    unittest.main()
