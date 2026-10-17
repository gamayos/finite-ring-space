"""The ledger file of 28-flavour (frc/ledgers/p28_flavour.py; the 28-flavour migration of 17 October 2026), the flavour
theme's exact algebra it uses (frc/flavour.py) and the chart file of its readings (frc/chart_flavour.py): each helper
computed two ways, and the ledger green, every check EXACT or CHART, its markers on its deciding checks, its checks
reproducing the package's 16 records (the rows the package cited on the import A2 and the realisations B3, B4 carry no
witness after the migration; the rows the ledger file witnesses beyond the package are 28:X8, P3, P7, C12)."""
import json
import math
import random
import re
import unittest
from fractions import Fraction
from pathlib import Path

from frc import flavour as FL
from frc import chart_flavour as CFL
from frc.registry import MARKER

ROOT = Path(__file__).resolve().parents[2]

# the checks that are continuum readings, and the chart clauses split from an exact parent
CHART_CHECKS = {"A3c", "B1c", "B2c", "B3c", "C1c", "C2c", "C3c", "D1", "D2c", "E2c", "F2", "H1", "H2", "H3", "Z1", "Z3",
                "Z4", "Z4b"}
SPLIT = ("A3c", "B1c", "B2c", "B3c", "C1c", "C2c", "C3c")             # D2c and E2c reproduce records of their own (tm2_jointfit, neutrino)
# the rows the ledger file decides or corroborates beyond the package's records, and the package rows left unwitnessed
ADDED_ROWS = {"28:X8", "28:P3", "28:P7", "28:C12"}
DROPPED_ROWS = {"28:A2", "28:B3", "28:B4"}
# the rows with a Mathlib reading (the chart theme's FrcLedger/Theme/Flavour.lean)
ML_ROWS = {"C3", "C4", "C6", "C7", "C9", "C10", "X1", "X2", "X3", "X4", "X5", "X6", "X7", "X9", "X10", "X11", "P1", "P2", "P3",
           "P5", "P6", "P7", "P8"}


def _rows(s): return [t.strip() for t in s.split(",") if t.strip()]


class FlavourTest(unittest.TestCase):
    def test_qomega(self):
        w = FL.OMEGA
        self.assertEqual(w ** 3, 1)
        self.assertEqual(1 + w + w * w, 0)
        self.assertEqual(w.conj(), w * w)
        self.assertEqual(w.norm(), 1)
        self.assertEqual((1 - w).norm(), 3)
        z = FL.QOmega(Fraction(3, 2), Fraction(-5, 7))
        self.assertEqual(z * z.conj(), FL.QOmega(z.norm()))
        self.assertEqual(z + z.conj(), FL.QOmega(z.re2()))
        self.assertEqual((z - z.conj()) * (z - z.conj()), FL.QOmega(-z.im2sq()))

    def test_circulant(self):
        rng = random.Random(3)
        for _ in range(10):
            a, b, c = (FL.QOmega(Fraction(rng.randint(-9, 9), rng.randint(1, 5)), Fraction(rng.randint(-9, 9), rng.randint(1, 5))) for _ in range(3))
            self.assertTrue(FL.eigen_identities(a, b, c))
            self.assertTrue(FL.transpose_eigen(a, b, c))
            M = FL.circ(a, b, c)
            self.assertTrue(FL.is_circ(M) and FL.is_circ(FL.adj3(M)) and FL.is_circ(FL.mmul(M, M)))
            self.assertEqual(FL.det3(M), FL.eigenvalues(a, b, c)[0] * FL.eigenvalues(a, b, c)[1] * FL.eigenvalues(a, b, c)[2])
        # the Koide functional on rational eigenvalues equals the chart's Q on their squares
        lam = [Fraction(7, 2), Fraction(1, 3), Fraction(5, 4)]
        self.assertAlmostEqual(float(FL.koide_functional(lam)), CFL.koide([float(l * l) for l in lam]), places=14)

    def test_shells(self):
        for p in (17, 53, 89):
            S = FL.Shell(p); K = S.K
            self.assertEqual(K.pow(S.omega, 3), (1, 0))
            self.assertEqual(K.add(K.add(K.mul(S.omega, S.omega), S.omega), (1, 0)), (0, 0))
            self.assertEqual((S.i * S.i) % p, p - 1)
            self.assertEqual((2 * S.h) % p, 1)
            self.assertEqual(K.mul(S.s3, S.s3), (3 % p, 0))
            self.assertTrue(FL.norms_two_three(p))
            self.assertTrue(FL.boundary(p, a=3)[0])
            self.assertTrue(FL.trace_relations(p))
            self.assertTrue(FL.jarlskog_framed(p))
            ls, Qv, b = S.koide_point(1, Fraction(1, 2))
            self.assertEqual(Qv, S.frac(Fraction(2, 3)))
            self.assertEqual(S.K.norm(b), S.frac(Fraction(1, 2)))
        with self.assertRaises(ValueError): FL.Shell(13)                          # 13 ≡ 1 (mod 12): no shell of the paper

    def test_texture_and_mixing(self):
        down, up, Ed, Eu = FL.texture_exponents()
        self.assertEqual((down, up), ((4, 2, 0), (8, 4, 0)))
        M, e11, e12 = FL.gst_relation(Fraction(3, 5), Fraction(4, 5), Fraction(-16, 9), 1)       # m₁ = −m₂ s²/c²: the texture zero
        self.assertTrue(e11 and e12 and M[0][0] == 0)
        self.assertEqual(M[0][1], (Fraction(-16, 9) - 1) * Fraction(12, 25))
        self.assertEqual(FL.protected_column(), (True, True, True))
        tri, q, J2 = FL.magic_matrix()
        self.assertTrue(tri and q)
        self.assertEqual(J2, Fraction(1, 108))
        self.assertAlmostEqual(math.sqrt(float(J2)), 1 / (6 * math.sqrt(3)), places=15)
        self.assertEqual(FL.colour_count(), (3, 1, 9))
        self.assertEqual(FL.sixteen(), (True, True, (1, 10, 5)))
        rng = random.Random(4)
        for _ in range(5):
            L, R = FL.random_matrix(rng), FL.random_matrix(rng)
            self.assertTrue(FL.lopsided_transpose(L, [Fraction(1), Fraction(2), Fraction(3)], R))
            mD = FL.random_circ(rng)
            self.assertTrue(FL.transpose_fixed_point(Fraction(2, 3), mD))
            self.assertTrue(FL.seesaw_closure(mD, FL.random_circ(rng))[0])


class ChartFlavourTest(unittest.TestCase):
    def test_koide(self):
        Qv, dev, dQ, rho, angle, r, dl, a2 = CFL.koide_measured()
        self.assertAlmostEqual(Qv, 2 / 3 + dev, places=15)
        self.assertAlmostEqual(Qv, 1 / 3 + 2 / 3 * rho * rho, places=6)        # the Parseval form on the measured masses
        self.assertAlmostEqual(math.cos(math.radians(angle)) ** 2, 1 / (3 * Qv), places=12)
        self.assertAlmostEqual(r, math.sqrt(6 * Qv - 2), places=15)
        self.assertLess(CFL.spectrum_check([float(x) for x in CFL.DATA["leptons"].values()]), 1e-9)
        me_pred, d = CFL.electron_prediction()
        self.assertAlmostEqual(d, dl, places=4)

    def test_mixing(self):
        self.assertAlmostEqual(CFL.tm2_cos(8.57, 45.0), 0.0, places=15)
        # the relation against the direct PMNS construction: cos δ from |U_μ1|² in the standard parametrisation at the
        # TM2 point sin²θ₁₂ = 1/(3c₁₃²)
        th13, th23 = math.radians(8.57), math.radians(49.0)
        s13, c13 = math.sin(th13), math.cos(th13); s23, c23 = math.sin(th23), math.cos(th23)
        s12 = math.sqrt(1 / (3 * c13 * c13)); c12 = math.sqrt(1 - s12 * s12)
        cosd = CFL.tm2_cos(8.57, 49.0)
        Umu2_sq = c12 * c12 * c23 * c23 + s12 * s12 * s23 * s23 * s13 * s13 - 2 * c12 * c23 * s12 * s23 * s13 * cosd
        self.assertAlmostEqual(Umu2_sq, 1 / 3, places=12)                        # TM2: the second column trimaximal, |U_μ2|² = 1/3
        at, band, drive, solar, signs = CFL.tm2_readings()
        self.assertAlmostEqual(drive[0], 360 - band[1], places=12)
        ckm, pmns, right = CFL.lopsided()
        self.assertAlmostEqual(pmns, right, places=9)

    def test_neutrinos(self):
        tot, m2, m3 = CFL.neutrino_floor()
        self.assertAlmostEqual(tot, m2 + m3, places=12)
        no = CFL.signed_circulant(False, n=72000)
        d = CFL.DATA["nu"]
        m = [x / 1e3 for x in no[1]]
        self.assertAlmostEqual((m[1] ** 2 - m[0] ** 2) / (m[2] ** 2 - m[0] ** 2), float(d["dm21"]) / float(d["dm31"]), places=5)
        self.assertAlmostEqual(m[2] ** 2 - m[0] ** 2, float(d["dm31"]), places=12)
        self.assertAlmostEqual(no[3], 2 / 3, places=9)
        t1, t2, t3, lo, hi = CFL.majorana_band(0.0)
        self.assertAlmostEqual(lo, t2 - t3, places=12); self.assertAlmostEqual(hi, t2 + t3, places=12)

    def test_jacobi(self):
        H = [[2.0, 1.0, 0.5], [1.0, 3.0, 0.2], [0.5, 0.2, 1.0]]
        vals, V = CFL._jacobi_eig(H)
        for j in range(3):
            v = [V[k][j] for k in range(3)]
            Hv = [sum(H[i][k] * v[k] for k in range(3)) for i in range(3)]
            for i in range(3): self.assertAlmostEqual(Hv[i], vals[j] * v[i], places=10)
        self.assertEqual(vals, sorted(vals))


class LedgerTest(unittest.TestCase):
    def test_ledger_file(self):
        from frc.ledgers import p28_flavour as L
        self.assertTrue(L.R.verify_all())
        self.assertEqual(L.PAPER, "28-flavour")
        # the Lean side: every row with a declaration has a deciding python check (gate G12; no Lean-only row), every
        # theorem row has a core declaration except the four pure readings C9, X9, P6, P7, and the Mathlib readings are
        # the twenty-three of the blueprint
        self.assertEqual(L.LEAN_ONLY, ())
        for lab in L.LEAN: self.assertIn(f"28:{lab}", L.PREDICATES, lab)
        if L.LEAN:                                                          # the table is empty until make_ledgers runs
            for lab in L.R.predicates:
                lab = lab.split(":")[1]
                if lab[0] in "CXP" and lab not in ("C9", "X9", "P6", "P7"):
                    self.assertEqual(L.LEAN[lab].split(", ")[0], "core", lab)
            self.assertEqual({lab for lab, v in L.LEAN.items() if "ml" in v}, ML_ROWS)
        self.assertEqual(sorted(L.FAMILY), sorted(L.LEDGER))
        # the kinds: EXACT or CHART, one per check, 31 checks, the chart ones labelled [chart]
        kinds = {r["id"]: r["kind"] for r in L.R.results}
        self.assertEqual(len(kinds), 31)
        self.assertEqual(sorted(kinds), sorted(L.LEDGER))
        self.assertEqual(set(kinds.values()), {"EXACT", "CHART"})
        self.assertEqual({pid for pid, k in kinds.items() if k == "CHART"}, CHART_CHECKS)
        for r in L.R.results:
            self.assertEqual(r["kind"] == "CHART", "[chart]" in r["label"], r["id"])
            self.assertNotIn("[approx]", r["label"], r["id"])
        for pid in SPLIT:                                            # a chart clause split from its exact parent
            parent = pid[:-1]
            self.assertEqual(kinds[parent], "EXACT", pid)
            self.assertEqual(L.FAMILY[pid], L.FAMILY[parent], pid)
        # every T row of the paper is decided by one check; the Ω rows Z1, Z3, Z4 and Z2 by chart readings
        led = json.loads((ROOT / "docs" / "28-flavour" / "28-flavour-ledger.json").read_text(encoding="utf-8"))
        trows = {f"28:{r['label']}" for b in led["blocks"] for r in b["rows"] if r["tag"] == "T" and not r["label"].startswith("V")}
        self.assertEqual(trows, {k for k in L.PREDICATES if k[3] in "CXP"})
        # the markers: one marker line per decided predicate, on the line before its deciding check, with the row's key
        src = (ROOT / "frc" / "ledgers" / "p28_flavour.py").read_text(encoding="utf-8").split("\n")
        marks = L.R.markers()
        for lab, pid in L.R.predicates.items():
            self.assertIn(lab, marks)
            line = next(j for j in range(marks[lab][1], len(src)) if src[j].strip())
            self.assertIn(f'R.check("{pid}"', src[line], lab)        # the marker sits on its deciding check
            self.assertIn(f"{lab} ({L.KEYS[lab.split(':')[1]]})", src[marks[lab][1] - 1])
            marker_lines = [j for j, s in enumerate(src) if MARKER.match(s) and re.search(rf"(?<![\w:]){re.escape(lab)}(?![\w])", s)]
            self.assertEqual(len(marker_lines), 1, lab)

    @unittest.skipUnless((ROOT / "src" / "28-flavour" / "results.json").exists(), "the package src/28-flavour is not in this tree")
    def test_package_records(self):
        """Every record of the package's results.json is reproduced by at least one check, every row a record cites is
        witnessed by some check (the import A2 and the realisations B3, B4 excepted: they carry no witness after the
        migration), a record the package classed EXACT has only EXACT checks, and every row a check cites that the
        package also cites names the deciding check in its source cell once the ledger carries the tokens."""
        from frc.ledgers import p28_flavour as L
        L.R.verify_all()
        recs = {r["id"]: r for r in json.loads((ROOT / "src" / "28-flavour" / "results.json").read_text(encoding="utf-8"))}
        self.assertEqual(sorted("flv." + f for f in set(L.FAMILY.values())), sorted(recs))
        kinds = {r["id"]: r["kind"] for r in L.R.results}
        witnessed = set()
        for pid, fam in L.FAMILY.items():
            witnessed.update(_rows(L.LEDGER[pid]))
            self.assertIn(recs["flv." + fam]["kind"], ("EXACT", "MIXED", "APPROX"))
            if recs["flv." + fam]["kind"] == "EXACT": self.assertEqual(kinds[pid], "EXACT", pid)
        package = set()
        for rec in recs.values(): package.update(_rows(rec["rows"]))
        self.assertLessEqual(package - DROPPED_ROWS, witnessed)
        self.assertLessEqual(witnessed - package, ADDED_ROWS)
        led = json.loads((ROOT / "docs" / "28-flavour" / "28-flavour-ledger.json").read_text(encoding="utf-8"))
        keys = {r["label"]: r["key"] for b in led["blocks"] for r in b["rows"] if r["tag"] == "T"}
        source = {r["label"]: re.sub(r"\\allowbreak|\s|\\", "", r.get("source") or "") for b in led["blocks"] for r in b["rows"]}
        if any("pywit{flavour}" in s for s in source.values()):                 # the ledger carries the tokens
            for lab, pid in L.R.predicates.items():
                l = lab.split(":")[1]
                if l in source and keys.get(l):
                    self.assertIn("pywit{flavour}{" + keys[l] + "}{" + l + "}", source[l], (pid, lab))


if __name__ == "__main__":
    unittest.main()
