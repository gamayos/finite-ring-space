"""The ledger file of 32-dark (frc/ledgers/p32_dark.py; the 32-dark migration of 18 October 2026), the dark theme's exact
arithmetic it uses (frc/dark.py) and the chart file of its readings (frc/chart_dark.py): each helper computed two ways,
and the ledger green, every check EXACT or CHART, its markers on its deciding checks, its checks reproducing the
package's records but the two simulations (decision D5; the rows the package cited on the realisation B8, the open rows
Y1, Y2 and the retired V2 carry no witness after the migration; the rows the ledger file witnesses beyond the package
are 32:C9, X6, C11, X9, X10, X11, P5, P6, Z1)."""
import json
import math
import random
import re
import unittest
from fractions import Fraction
from pathlib import Path

from frc import dark as D
from frc import chart_dark as CD
from frc.registry import MARKER

ROOT = Path(__file__).resolve().parents[2]

# the checks that are continuum readings, and the chart clauses split from an exact parent
CHART_CHECKS = {"A2", "B2c", "B3c", "C1c", "C2c", "D1", "D2", "E2c", "F1", "G1", "G2", "G3", "G4", "G5"}
SUFFIXED = ("B2c", "B3c", "C1c", "C2c", "E2c")                       # the chart clauses beside an exact parent
SPLIT = ("B3c", "C2c", "E2c")                                         # of them, those reproducing their parent's record (B2c and C1c reproduce deep_regime_fp and interpolation)
# the rows the ledger file decides or corroborates beyond the package's records, and the package rows left unwitnessed
ADDED_ROWS = {"32:C9", "32:X6", "32:C11", "32:X9", "32:X10", "32:X11", "32:P5", "32:P6", "32:Z1"}
DROPPED_ROWS = {"32:B8", "32:Y1", "32:Y2", "32:V2"}
NOT_REPRODUCED = {"dark.deep_regime", "dark.make_figures"}                     # the seeded simulation and the figure script (D5)
# the theorem rows that are readings alone (no core declaration), and the rows with a Mathlib reading
READINGS = {"C2", "C8", "C9", "C11", "X2", "X5", "X6", "X9", "X10", "X11", "P1", "P2", "P3", "P4", "P6"}
ML_ROWS = {"C2", "C4", "C5", "C6", "C7", "C8", "C9", "C10", "C11", "X2", "X3", "X4", "X5", "X6", "X7", "X8", "X9", "X10",
           "X11", "P1", "P2", "P3", "P4", "P6"}


def _rows(s): return [t.strip() for t in s.split(",") if t.strip()]


class DarkTest(unittest.TestCase):
    def test_gauss_box(self):
        box = D.GaussBox(5)
        zero = {p: Fraction(0) for p in box.boundary}
        rng = random.Random(5)
        src = {p: Fraction(rng.randint(-3, 3), 2) for p in box.interior if rng.random() < 0.3}
        U = box.field(src, zero)
        for p in box.interior:                                           # the solved field satisfies the equation at every site
            self.assertEqual(6 * U[p] - sum(U[q] for q in box.nbrs(p)), src.get(p, Fraction(0)))
        self.assertEqual(box.flux(U, 1), sum(src.values()))              # the flux through R = 1 is the enclosed charge
        self.assertEqual(box.flux(U, 0), src.get(box.centre, Fraction(0)))
        # linearity: the field of the sum is the sum of the fields
        noise = {p: Fraction(rng.randint(-9, 9), 4) for p in box.boundary}
        Un = box.field({}, noise); Usn = box.field(src, noise)
        self.assertEqual(Usn, D.superposition(U, Un))
        self.assertEqual(D.gauss_law(seed=7), (1, 1, 0, 1))

    def test_amplitude(self):
        GI = D.GI
        for n in range(1, 9):
            self.assertEqual(D.incoherent_mean(n), n)
            self.assertEqual(D.coherent_count(GI, GI.el(0, 1), n), (n * n, n * n))
        rng = random.Random(3)
        us = [GI.el(rng.randint(-4, 4), rng.randint(-4, 4)) for _ in range(5)]
        lhs, rhs = D.sign_pattern_total(GI, us)
        self.assertEqual(lhs, rhs)
        self.assertEqual(rhs, 32 * sum(GI.norm(u) for u in us))
        K = D.shell_ext(17)
        self.assertEqual(K.nu, 3)
        lhs, rhs = D.sign_pattern_total(K, [(1, 2), (3, 5), (0, 1)])
        self.assertEqual(lhs, rhs)

    def test_passage(self):
        for z in (Fraction(3, 5), Fraction(5, 13), Fraction(8, 17), Fraction(7, 25), Fraction(20, 29)):
            f, g = D.passage_roots(z)
            self.assertEqual(f * g, 1)
            self.assertEqual(D.passage_residual(z, f), 0)
            self.assertEqual(D.passage_residual(z, g), 0)
            u = 1 / z
            self.assertEqual(D.passage_factor(u), (f, g))                # f = u − √(u² − 1) at u = 1/z
            self.assertAlmostEqual(float(f), math.exp(-math.acosh(float(u))), places=14)
        self.assertIsNone(D.passage_roots(Fraction(1, 2)))              # 1 − 1/4 is not a rational square
        # the two-image form solves the killed walk's recurrence on the whole cycle
        N, a, z = 12, 3, Fraction(3, 5); f = D.passage_roots(z)[0]
        h = [(f ** ((i - a) % N) + f ** (N - (i - a) % N)) / (1 + f ** N) for i in range(N)]
        h[a] = Fraction(1)
        for i in range(N):
            if i != a: self.assertEqual(h[i], z / 2 * (h[(i - 1) % N] + h[(i + 1) % N]))
        self.assertEqual(h[0], D.cycle_escape(N, a, z))
        self.assertEqual(h[0], D.cycle_closed(N, a, f))

    def test_coherence(self):
        self.assertEqual(D.n_eff([4, 1, 1]), Fraction(8, 3))
        self.assertEqual(D.coherence_sum([4, 1, 1], 1), 16)
        self.assertEqual(D.coherence_sum([4, 1, 1], 0), 6)
        self.assertEqual(D.coherence_sum([4, 1, 1], Fraction(1, 2)), 11)
        self.assertIsNone(D.n_eff([2, 1]))
        self.assertEqual(D.tully_fisher(Fraction(2, 3), Fraction(3, 2), 16), (16, 16, 4, 4))
        self.assertIsNone(D.tully_fisher(1, 1, 2))
        K = D.shell_ext(13)
        zeta = next(z for z in ((a, b) for a in range(13) for b in range(13)) if z not in ((0, 0), (1, 0)) and K.pow(z, 7) == (1, 0))
        self.assertEqual(D.phasor_cycle_sum(K, zeta, 7), (0, 0))
        fac, divs, ratios = D.divisor_lattice(360)
        self.assertEqual((fac, len(divs)), ({2: 3, 3: 2, 5: 1}, 24))
        self.assertEqual([d * r for d, r in zip(divs, ratios)], [360] * 24)


class ChartDarkTest(unittest.TestCase):
    def test_floor_and_lambda(self):
        a0, pct, sig = CD.floor_comparison()
        self.assertAlmostEqual(a0, 299792458 * 67.4e3 / 3.0856775814913673e22 / (2 * math.pi), places=24)
        self.assertAlmostEqual(pct / 100, 1 - a0 / 1.2e-10, places=12)
        rH, HL, face = CD.lambda_face()
        self.assertAlmostEqual(face, 299792458 ** 2 / (2 * 1.616255e-35 * math.sqrt(math.pi * 3.3e122)), places=20)
        lam, lamS = CD.lambda_planck()
        self.assertAlmostEqual(lam, 3 / (rH / 1.616255e-35) ** 2, places=130)
        self.assertAlmostEqual(lamS, 3 * math.pi, places=12)

    def test_interpolation(self):
        for x in (0.01, 0.5, 5.0, 50.0):
            self.assertAlmostEqual(CD.nu(x), 1 / (1 - math.exp(-math.sqrt(x))), places=14)
            self.assertAlmostEqual(CD.tan_alpha(x) ** 2, 1 / (math.exp(math.sqrt(x)) - 1), places=12)
            self.assertAlmostEqual(math.sin(math.radians(CD.chart_angle(x))) ** 2, math.exp(-math.sqrt(x)), places=12)
        dmax, xmax, ddex = CD.discriminant(3001)
        self.assertAlmostEqual(dmax, CD.nu_simple(xmax) - CD.nu(xmax), places=15)
        self.assertTrue(CD.monotone_grid(201))
        self.assertAlmostEqual(CD.scatter_law(1.0, 0.1), 2 * CD.tan_alpha(1.0) / math.log(10) * math.atan(0.1), places=15)
        self.assertAlmostEqual(CD.scatter_at_angle(1.0, CD.delta_alpha_bound(0.04, 1.0)), 0.04, places=12)

    def test_bessel_and_disk(self):
        # I₀(1), I₁(1), K₀(1), K₁(1) to twelve digits (Abramowitz and Stegun 9.8)
        self.assertAlmostEqual(CD.bessel_i(0, 1.0), 1.2660658777520084, places=12)
        self.assertAlmostEqual(CD.bessel_i(1, 1.0), 0.5651591039924851, places=12)
        self.assertAlmostEqual(CD.bessel_k(0, 1.0), 0.42102443824070834, places=12)
        self.assertAlmostEqual(CD.bessel_k(1, 1.0), 0.6019072301972346, places=12)
        try:
            from scipy.special import i0, i1, k0, k1
        except ImportError:
            i0 = None
        if i0:
            for x in (0.02, 0.3, 2.5, 6.5):
                self.assertAlmostEqual(CD.bessel_i(0, x) / i0(x), 1, places=12)
                self.assertAlmostEqual(CD.bessel_i(1, x) / i1(x), 1, places=12)
                self.assertAlmostEqual(CD.bessel_k(0, x) / k0(x), 1, places=12)
                self.assertAlmostEqual(CD.bessel_k(1, x) / k1(x), 1, places=12)
        # the disk's Newtonian speed at large radius tends to the point mass's, the registered one to the Tully–Fisher speed
        G, Msun, kpc, AU = CD._si(); M = 5e10
        vb, vo = CD.disk_curve(M, 3.0, [300.0])                     # y = 50: the disk's v² is 1.00045 of the point mass's
        self.assertAlmostEqual(vb[0] / (math.sqrt(G * M * Msun / (300 * kpc)) / 1e3), 1.000225, places=5)
        self.assertAlmostEqual(vo[0] / CD.btfr_speed(M), 1, places=1)
        self.assertAlmostEqual(CD.btfr_speed(M), (G * M * Msun * CD.floor()) ** 0.25 / 1e3, places=12)
        # with an external field the registered speed is lower at every radius
        vb2, vo2 = CD.disk_curve(M, 3.0, [5.0, 20.0, 40.0], 0.1)
        for a, b in zip(vo2, CD.disk_curve(M, 3.0, [5.0, 20.0, 40.0])[1]): self.assertLess(a, b)

    def test_fokker_planck(self):
        # the small-tilt boost against the Lifson–Jackson mobility: T/⟨sin φ⟩ → 1/(1 − I₀(1/D)⁻²)
        for Dn in (0.3, 0.6):
            slope, boost = CD.fokker_planck_slope(Dn)
            self.assertAlmostEqual(boost[0], 1 / (1 - CD.bessel_i(0, 1 / Dn) ** -2), places=3)
            self.assertAlmostEqual(slope, 1.0, places=2)
        # the stationary density integrates ⟨sin φ⟩ = T − ⟨φ̇⟩ with ⟨φ̇⟩ ≥ 0: 0 < ⟨sin φ⟩ < T
        for T in (0.05, 0.3):
            m = CD.mean_sin(T, 0.4)
            self.assertTrue(0 < m < T)

    def test_sparc_loaders(self):
        rar = CD.load_rar()
        self.assertEqual(len(rar), 2693)
        self.assertEqual(rar[0], (-11.23, 0.04, -10.68, 0.08))
        sample = CD.load_sample()
        self.assertEqual(len(sample), 175)
        self.assertEqual(sample["CamB"], (65.0, 0.0, 2))
        self.assertEqual(sample["NGC3109"][2], 1)
        curves = CD.load_rotmods()
        self.assertEqual(len(curves), 175)
        self.assertEqual(curves["D512-2"][0], (0.96, 22.90, 2.71, 4.08, 14.85, 0.00))
        self.assertAlmostEqual(CD.residual_slope(1.0), 1 - 0.5 * math.exp(-1) / (1 - math.exp(-1)), places=15)
        self.assertAlmostEqual(CD.spearman([1, 2, 3, 4], [10, 20, 30, 40]), 1.0, places=15)
        self.assertAlmostEqual(CD.spearman([1, 2, 3, 4], [4, 3, 2, 1]), -1.0, places=15)

    def test_predictions(self):
        pct, a1, rise = CD.ez_quarter()
        om = 0.315
        for p, z in zip(pct, (0.5, 1.0, 2.0)):
            self.assertAlmostEqual(p / 100 + 1, (om * (1 + z) ** 3 + 1 - om) ** 0.125, places=12)
        self.assertAlmostEqual(a1, CD.floor() * math.sqrt(om * 8 + 1 - om), places=22)
        for s, gb_a0, y, n, pct_ in CD.wide_binaries():
            self.assertAlmostEqual(y, gb_a0 + 1.8, places=12)
            self.assertAlmostEqual(n, CD.nu(y), places=12)
        o1, o2 = CD.coherence_offsets()
        self.assertAlmostEqual(o1, 0.5 * math.log10(0.8), places=15)
        self.assertAlmostEqual(o2, -0.5 * math.log10(2), places=15)
        self.assertAlmostEqual(CD.passage_reduction(1e-4), 1 / 6, places=5)
        diff, wrap = CD.wrap_term(40, 5, 0.05)
        d = math.acosh(math.exp(0.05)); f = math.exp(-d)
        self.assertAlmostEqual(diff, (f ** 5 + f ** 35) / (1 + f ** 40) - f ** 5, places=14)


class LedgerTest(unittest.TestCase):
    def test_ledger_file(self):
        from frc.ledgers import p32_dark as L
        self.assertTrue(L.R.verify_all())
        self.assertEqual(L.PAPER, "32-dark")
        # the Lean side: every row with a declaration has a deciding python check (gate G12; no Lean-only row), every
        # theorem row has a core declaration except the fifteen readings, and the Mathlib readings are the twenty-four of
        # the blueprint
        self.assertEqual(L.LEAN_ONLY, ())
        for lab in L.LEAN: self.assertIn(f"32:{lab}", L.PREDICATES, lab)
        if L.LEAN:                                                          # the table is empty until make_ledgers runs
            for lab in L.R.predicates:
                lab = lab.split(":")[1]
                if lab[0] in "CXP" and lab not in READINGS:
                    self.assertEqual(L.LEAN[lab].split(", ")[0], "core", lab)
            for lab in READINGS: self.assertEqual(L.LEAN[lab], "ml", lab)
            self.assertEqual({lab for lab, v in L.LEAN.items() if "ml" in v}, ML_ROWS)
        self.assertEqual(sorted(L.FAMILY), sorted(L.LEDGER))
        # the kinds: EXACT or CHART, one per check, 23 checks, the chart ones labelled [chart]
        kinds = {r["id"]: r["kind"] for r in L.R.results}
        self.assertEqual(len(kinds), 23)
        self.assertEqual(sorted(kinds), sorted(L.LEDGER))
        self.assertEqual(set(kinds.values()), {"EXACT", "CHART"})
        self.assertEqual({pid for pid, k in kinds.items() if k == "CHART"}, CHART_CHECKS)
        for r in L.R.results:
            self.assertEqual(r["kind"] == "CHART", "[chart]" in r["label"], r["id"])
            self.assertNotIn("[approx]", r["label"], r["id"])
        for pid in SUFFIXED:                                         # a chart clause beside its exact parent
            self.assertEqual(kinds[pid[:-1]], "EXACT", pid)
            if pid in SPLIT: self.assertEqual(L.FAMILY[pid], L.FAMILY[pid[:-1]], pid)
        # every T row of the paper is decided by one check, the Ω row Z1 by the lattice check
        led = json.loads((ROOT / "docs" / "32-dark" / "32-dark-ledger.json").read_text(encoding="utf-8"))
        rows = [r for b in led["blocks"] for r in b["rows"]]
        if not any(r["label"] == "V3" for r in rows):                       # the ledger JSON carries the migrated rows
            trows = {f"32:{r['label']}" for r in rows if r["tag"] == "T"}
            self.assertEqual(trows, {k for k in L.PREDICATES if k[3] in "CXP"})
            self.assertEqual({r["label"]: r["key"] for r in rows}, L.KEYS)
        self.assertEqual({k for k in L.PREDICATES if k[3] == "Z"}, {"32:Z1"})
        # the markers: one marker line per decided predicate, on the line before its deciding check, with the row's key
        src = (ROOT / "frc" / "ledgers" / "p32_dark.py").read_text(encoding="utf-8").split("\n")
        marks = L.R.markers()
        for lab, pid in L.R.predicates.items():
            self.assertIn(lab, marks)
            line = next(j for j in range(marks[lab][1], len(src)) if src[j].strip())
            self.assertIn(f'R.check("{pid}"', src[line], lab)        # the marker sits on its deciding check
            self.assertIn(f"{lab} ({L.KEYS[lab.split(':')[1]]})", src[marks[lab][1] - 1])
            marker_lines = [j for j, s in enumerate(src) if MARKER.match(s) and re.search(rf"(?<![\w:]){re.escape(lab)}(?![\w])", s)]
            self.assertEqual(len(marker_lines), 1, lab)

    @unittest.skipUnless((ROOT / "src" / "32-dark" / "results.json").exists(), "the package src/32-dark is not in this tree")
    def test_package_records(self):
        """Every record of the package's results.json but the two simulations is reproduced by at least one check, every
        row a record cites is witnessed by some check (the realisation B8, the open rows Y1, Y2 and the retired V2
        excepted), a record the package classed EXACT has an EXACT deciding check (its chart clause, if any, split off
        with the suffix c), and every row a check cites that the package also cites names the deciding check in its
        source cell once the ledger carries the tokens."""
        from frc.ledgers import p32_dark as L
        L.R.verify_all()
        recs = {r["id"]: r for r in json.loads((ROOT / "src" / "32-dark" / "results.json").read_text(encoding="utf-8"))}
        families = {"dark." + f for f in L.FAMILY.values() if f}
        self.assertEqual(sorted(families | NOT_REPRODUCED), sorted(recs))
        self.assertEqual({pid for pid, f in L.FAMILY.items() if f is None}, {"D2", "F1", "Z1"})
        kinds = {r["id"]: r["kind"] for r in L.R.results}
        witnessed = set()
        for pid, fam in L.FAMILY.items():
            witnessed.update(_rows(L.LEDGER[pid]))
            if fam is None: continue
            self.assertIn(recs["dark." + fam]["kind"], ("EXACT", "SIM", "CHART"))
            if recs["dark." + fam]["kind"] == "EXACT":
                self.assertEqual(kinds[pid[:-1] if pid.endswith("c") else pid], "EXACT", pid)
        package = set()
        for rec in recs.values(): package.update(_rows(rec["rows"]))
        self.assertLessEqual(package - DROPPED_ROWS, witnessed)
        self.assertLessEqual(witnessed - package, ADDED_ROWS)
        led = json.loads((ROOT / "docs" / "32-dark" / "32-dark-ledger.json").read_text(encoding="utf-8"))
        keys = {r["label"]: r["key"] for b in led["blocks"] for r in b["rows"] if r["tag"] == "T"}
        source = {r["label"]: re.sub(r"\\allowbreak|\s|\\", "", r.get("source") or "") for b in led["blocks"] for r in b["rows"]}
        if any("pywit{dark}" in s for s in source.values()):                   # the ledger carries the tokens
            for lab, pid in L.R.predicates.items():
                l = lab.split(":")[1]
                if l in source and keys.get(l):
                    self.assertIn("pywit{dark}{" + keys[l] + "}{" + l + "}", source[l], (pid, lab))


if __name__ == "__main__":
    unittest.main()
