"""frc/chart_gravity.py (the chart theme; 21-gravity): the chart readings against closed forms and known constants — the
lattice Green's function against Watson's constant and G(1) = G(0) − 1/6, the deflection against 4Gm/b, the photon
sphere and the ISCO against their closed forms, the operational cut against the scale import, the tilt against the
chart theme, the Kuramoto chain's quiet run against its exact fixed point."""
import math
import unittest

from frc import chart as C
from frc import chart_gravity as CG


class GreenTest(unittest.TestCase):
    def test_watson_and_the_neighbour(self):
        g0, g1 = CG.lattice_green(0, 200), CG.lattice_green(1, 200)
        self.assertAlmostEqual(g0, 0.2527310098, places=5)
        self.assertAlmostEqual(g1, g0 - 1 / 6, places=5)                   # (6 − 2Σcos)G = δ at the origin: 6G(0) − 6G(1) = 1
        self.assertLess(abs(CG.green_slope((5, 8, 12), 200) + 1), 0.02)


class StrongFieldTest(unittest.TestCase):
    def test_deflection_and_profile(self):
        a, t = CG.deflection(Gm=0.5, b=2.0)
        self.assertAlmostEqual(a, t, places=8)
        self.assertAlmostEqual(CG.u_exact(10.0), 0.1 * (1 + 1e-4 / 30), places=9)
        self.assertAlmostEqual(*CG.profile_series(4.0), places=8)

    def test_photon_sphere_and_isco(self):
        r, b = CG.photon_sphere()
        self.assertAlmostEqual(r, 2.0, delta=0.05)                          # the exact profile shifts the pure-exponential minimum (r = 2, b = 2e) by 1 %
        self.assertAlmostEqual(b, 2 * math.e, delta=0.02)
        sh, rd = CG.shadow_ringdown()
        self.assertAlmostEqual((1 + sh) * (1 + rd), 1.0, places=12)
        i = CG.isco()
        self.assertAlmostEqual(i["r"], 3 + math.sqrt(5), places=12)
        r = i["r"]
        self.assertAlmostEqual(i["E"], math.exp(-1 / r) * math.sqrt((r - 1) / (r - 2)), places=6)   # E² = e^{−2/r}(r − 1)/(r − 2) on the circular orbit
        self.assertLess(abs(i["Wrr"]), 1e-6)

    def test_operational_cut_reads_the_import(self):
        self.assertEqual(CG.LN_OMEGA, float(C.LN_OMEGA))
        cut = CG.operational_cut(1e5)
        self.assertAlmostEqual(cut["r_f"] * CG.LN_OMEGA, 2e5, places=6)
        self.assertAlmostEqual(cut["threshold"], (283.5 / 2) ** 2, places=6)
        self.assertAlmostEqual(math.log(cut["round_trip"]), 283.5, places=9)
        self.assertEqual(CG.preferred_frame_scale(), math.exp(-283.5 / 2))


class FloorTest(unittest.TestCase):
    def test_floor_tilt_and_crossover(self):
        self.assertAlmostEqual(CG.floor(), float(C.floor()), places=20)
        self.assertAlmostEqual(CG.tilt(), -math.pi ** 2 / 283.5, places=12)
        self.assertAlmostEqual(CG.ratio(1e-4) * math.sqrt(1e-4), 1.0, delta=0.01)   # deep: ratio ≈ 1/√x
        self.assertAlmostEqual(CG.loglog_slope(1e-8), 0.5, places=3)
        r, nu, d = CG.interpolant_discriminant(5.0)
        self.assertAlmostEqual(d, nu - r, places=15)
        v, resid = CG.tully_fisher(1e9)
        self.assertLess(resid, 1e-12)

    def test_kuramoto_quiet_fixed_point(self):
        mean, dev = CG.kuramoto_chain(0.0, M=5, T=6000, burn=2000)
        self.assertAlmostEqual(mean, 0.3, delta=0.01)
        self.assertLess(dev, 0.01)


class RadiativeTest(unittest.TestCase):
    def test_dispersion_and_helicity(self):
        self.assertAlmostEqual(CG.dispersion((0.1, 0.2, 0.3)), 0.01 + 0.04 + 0.09, delta=1e-3)
        self.assertAlmostEqual(CG.group_velocity(1e-4), 1.0, places=5)
        self.assertAlmostEqual(CG.helicity_angle(20), 40.0, places=9)
        self.assertAlmostEqual(CG.schwarzschild_as_exponential(0.4), 0.0, places=12)


if __name__ == "__main__":
    unittest.main()
