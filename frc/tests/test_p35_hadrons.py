"""The ledger file of 35-hadrons (frc/ledgers/p35_hadrons.py; the 35-hadrons migration of 19 October 2026), the hadrons theme's
exact arithmetic it uses (frc/hadrons.py) and the chart file of its readings (frc/chart_hadrons.py): the colour group against
a brute force over the 4⁹ matrices and the order formula, the moments against the dimension sums, the identities against an
independent evaluation at random rationals, the Sturm count against the float bisection, the Lanczos eigenvalue against a
dense solver where numpy is installed; the ledger green, every check EXACT or CHART, its markers on its deciding checks, its
checks reproducing the package's records but the figure script (the rows the package cited on the realisations B1 and B5
and the retired V3 carry no witness after the migration; A5 and F1 are the checks beyond the package)."""
import itertools
import json
import random
import re
import unittest
from fractions import Fraction
from pathlib import Path

from frc import hadrons as H
from frc import chart_hadrons as CH
from frc import interactions as I
from frc.registry import MARKER

ROOT = Path(__file__).resolve().parents[2]

CHART_CHECKS = {"D1", "D2", "D3", "D4", "D5", "D6", "D7", "D8", "D9", "D10", "E2", "E3", "F2", "F3", "F4", "G1"}
BEYOND_PACKAGE = {"A5", "F1"}                                          # the flavour cube and the exact Sturm brackets
DROPPED_ROWS = {"35:B1", "35:B5", "35:V1", "35:V2", "35:V3"}            # the realisations' tokens and the verification rows
NOT_REPRODUCED = {"had.make_figures"}                                  # the figure script
# the theorem rows that are readings alone (no core declaration) and the rows with a Mathlib reading
READINGS = {"C10", "C22", "X11", "P7"}
CORE_ONLY = {"C1", "C15", "X1", "X2", "X3", "X7", "P4", "P5", "Z1"}


def _rows(s): return [t.strip() for t in s.split(",") if t.strip()]


class HadronsTest(unittest.TestCase):
    def test_colour_group(self):
        F, G = H.colour_group()
        self.assertEqual(len(G), 216)
        q = 2; self.assertEqual(len(G), q ** 3 * (q * q - 1) * (q ** 3 + 1))          # |SU(3, q)|
        self.assertEqual(I.unit_vectors(F, 3), q ** 2 * (q ** 3 + 1))
        # brute force over the 4⁹ matrices
        one = H.identity(F); els = F.elements(); n = 0
        for ent in itertools.product(els, repeat=9):
            A = (ent[0:3], ent[3:6], ent[6:9])
            if I.det(F, A) == F.one and I.mat_mul(F, I.dagger(F, A), A) == one: n += 1
        self.assertEqual(n, 216)
        self.assertEqual(sorted(H.centre(F, G)), sorted(H.colour_scalars(F)))

    def test_colourless_content(self):
        F, G = H.colour_group()
        self.assertEqual(H.colourless_content(F, G), (1, 0, 0, 1))
        # Λ² by the minors is the conjugate action in the Hodge-dual order of the wedge basis (e₁∧e₂, e₀∧e₂, e₀∧e₁ ↔ e₀, e₁, e₂;
        # no signs in characteristic 2), so the two agree on every vector after the reversal
        for g in G[:40]:
            w = H.wedge2(F, g); c = H.conj_matrix(F, g)
            for v in itertools.product(F.elements(), repeat=3):
                self.assertEqual(H.mat_vec(F, w, v), tuple(reversed(H.mat_vec(F, c, tuple(reversed(v))))))
        self.assertTrue(H.hermitian_invariant(F, G))

    def test_weyl_moments(self):
        E, c = H.weyl_moments()
        self.assertEqual(E, {(1, 1): 1, (2, 0): 0, (2, 2): 2, (3, 1): 0, (3, 0): 1, (4, 1): 3, (3, 3): 6})
        # dimension sums: 3 ⊗ 3̄ = 1 ⊕ 8, 3 ⊗ 3 = 6 ⊕ 3̄, 3³ = 10 ⊕ 8 ⊕ 8 ⊕ 1
        self.assertEqual(c["singlet_3x3bar"] * 1 + c["adjoint_in_3x3bar"] * 8, 9)
        self.assertEqual(c["singlet_3x3"], 0)
        mults, d27, d56, s56 = H.flavour_cube()
        self.assertEqual((mults, d27, d56, s56), ({"1": 1, "8": 2, "10": 1}, 27, 56, 56))
        self.assertEqual(sum(int(k) * v for k, v in mults.items()), 27)
        self.assertEqual(sum(v * v for v in mults.values()), 6)

    def test_arithmetic(self):
        self.assertEqual(H.colour_factor(), (Fraction(4, 3), Fraction(-2), Fraction(-8), Fraction(-8, 3)))
        self.assertEqual((H.g_spin(1), H.g_spin(3)), (Fraction(-3, 4), Fraction(3, 4)))
        self.assertEqual(H.hyperfine_eigenvalues()[:3], (Fraction(2), Fraction(-2), Fraction(3, 2)))
        self.assertEqual(H.charge_structure([Fraction(2, 3)] * 2 + [Fraction(-1, 3)]), (Fraction(1), Fraction(0)))
        self.assertEqual(H.charge_structure([Fraction(2, 3)] + [Fraction(-1, 3)] * 2), (Fraction(2, 3), Fraction(-1, 3)))
        self.assertEqual(H.character_coefficients(3), (Fraction(1, 18), Fraction(1, 36)))
        self.assertTrue(H.correlator_sums())

    def test_identities_at_random_rationals(self):
        rng = random.Random(35)
        def r(): return Fraction(rng.randrange(-50, 50), rng.randrange(1, 9))
        for _ in range(50):
            M0, a, b = r(), r(), r()
            N, L, S, X = M0 + a + b / 2, M0, M0 + 2 * b, M0 - a + b / 2
            self.assertEqual(2 * N + 2 * X - 3 * L - S, 0)
            al, be = r(), r(); M = [al + be * k for k in range(4)]
            self.assertEqual(M[0] - 2 * M[1] + M[2], 0); self.assertEqual(M[1] - 2 * M[2] + M[3], 0)
            d, A, rr = r(), r(), r(); q = Fraction(1, 4)
            D, Ss, Xs, O = M0 + 3 * A / 4, M0 + d + A * q * (1 + 2 * rr), M0 + 2 * d + A * q * (2 * rr + rr * rr), M0 + 3 * d + 3 * A * rr * rr / 4
            self.assertEqual(D - 3 * Ss + 3 * Xs - O, 0)
            Nn, Ll, Sg, Xi = M0 - 3 * A / 4, M0 + d - 3 * A / 4, M0 + d + A * (q - rr), M0 + 2 * d + A * (rr * rr * q - rr)
            self.assertEqual((Sg - Ll) - Fraction(2, 3) * ((D - Nn) - (Ss - Sg)), 0)
            self.assertEqual((Ss - Sg) - (Xs - Xi), 0)
            aa, bb = r(), r(); self.assertEqual(2 * (aa + bb) - aa - (aa + 2 * bb), 0)
        for p in (H.gmo_vector(), *H.spacing_vectors(), H.third_difference(), *H.hyperfine_links(), H.coleman_glashow(),
                  H.vector_spacing(), H.gap_identity(), *H.spin_split()):
            self.assertTrue(p.is_zero())

    def test_shells(self):
        self.assertTrue(H.admissible_shells(range(5000)))
        self.assertTrue(H.shells_ok([53, 173, 389, 1373]))
        self.assertFalse(H.shells_ok([13]))                                  # 13 ≡ 1 (mod 12)

    def test_sturm_against_bisection(self):
        N, L = 400, 20
        diag, off2, _ = H.airy_grid(N, L)
        eps, _, _, _ = CH.airy_readout(N, L)
        for k, e in enumerate(eps):
            lo, hi = Fraction(e) - Fraction(1, 10 ** 4), Fraction(e) + Fraction(1, 10 ** 4)
            self.assertEqual(H.sturm_count(diag, off2, lo), k)
            self.assertEqual(H.sturm_count(diag, off2, hi), k + 1)
        # the four brackets of the ledger on the paper's grid
        self.assertEqual(H.sturm_brackets(4000, 30, [("2.338", "2.339"), ("4.087", "4.088"), ("5.520", "5.521"), ("6.786", "6.787")]),
                         [(0, 1), (1, 2), (2, 3), (3, 4)])

    def test_relativistic_ground(self):
        E0, E1, cr = CH.relativistic_ground(300, 25)
        self.assertAlmostEqual(E0, 2.23155, places=4); self.assertAlmostEqual(E1, 3.32740, places=3); self.assertAlmostEqual(cr, 3.4729, places=3)
        try:
            import numpy as np
        except ImportError:
            return
        N, L = 300, 25; h = L / (N + 1)
        T = np.diag(2 / h ** 2 * np.ones(N)) + np.diag(-np.ones(N - 1) / h ** 2, 1) + np.diag(-np.ones(N - 1) / h ** 2, -1)
        w, V = np.linalg.eigh(T); absP = (V * np.sqrt(np.abs(w))) @ V.T
        ev = np.linalg.eigvalsh(absP + np.diag(np.arange(1, N + 1) * h))
        self.assertAlmostEqual(E0, float(ev[0]), places=6); self.assertAlmostEqual(E1, float(ev[1]), places=5)

    def test_nonrelativistic_contact(self):
        e0, c = CH.nonrelativistic_contact(600, 30)
        self.assertAlmostEqual(e0, 2.33788, places=4); self.assertAlmostEqual(c, 0.9990, places=3)
        eps, zeros, diff, ratio = CH.airy_readout()
        self.assertTrue(all(abs(d) < 5e-5 for d in diff)); self.assertAlmostEqual(ratio, 1.7484, places=4)

    def test_confrontations(self):
        c = CH.confrontations(); m = CH.pdg()
        self.assertEqual(m["N"], Fraction("938.9185"))
        self.assertTrue(Fraction("0.0056") < c["gmo"]["residual"] < Fraction("0.0058"))
        self.assertEqual(c["third"]["value"], Fraction("6.05"))
        self.assertEqual(c["cg"]["n_minus_p"], Fraction("1.293"))
        (ml, ms, v, _, _), table, res, worst = CH.anchored_spectrum()
        self.assertEqual(ml, (m["N"] + Fraction(3, 4) * v) / 3); self.assertEqual(ms - ml, m["Lam"] - m["N"])
        self.assertTrue(Fraction("0.0111") < worst < Fraction("0.0112"))
        self.assertEqual(CH.single_scale()["gap"], Fraction("176.7645"))

    def test_ledger_green_and_kinds(self):
        from frc.ledgers import p35_hadrons as L
        for b in sorted(L.BLOCK): L.R.run_block(b)
        self.assertTrue(L.R.summary(write=False, expect=list(L.LEDGER)))
        self.assertEqual(len(L.LEDGER), 34)
        recs = {r["id"]: r for r in L.R.results}
        self.assertEqual(set(L.LEDGER), set(recs))
        for cid, r in recs.items():
            self.assertEqual(r["kind"], "CHART" if cid in CHART_CHECKS else "EXACT", cid)
            self.assertEqual(r["label"].startswith("[chart]"), cid in CHART_CHECKS, cid)
            self.assertTrue(r["ok"], cid)
        self.assertEqual({k for k, v in L.FAMILY.items() if v is None}, BEYOND_PACKAGE)
        self.assertEqual(set(L.LEDGER), set(L.FAMILY))

    def test_markers_and_predicates(self):
        from frc.ledgers import p35_hadrons as L
        src = (ROOT / "frc" / "ledgers" / "p35_hadrons.py").read_text(encoding="utf-8")
        marks = L.R.markers()
        for pred, cid in L.PREDICATES.items():
            self.assertIn(pred, marks, pred)
            self.assertIn(pred, _rows(L.LEDGER[cid]), pred)
            key = L.KEYS[pred.split(":")[1]]
            self.assertRegex(src, rf"# (?:[^\n]*, )?{re.escape(pred)} \({key}\)")
        # every content T row and Z1 decided; the dropped rows nowhere
        rows = json.loads((ROOT / "docs" / "35-hadrons" / "35-hadrons-ledger.json").read_text(encoding="utf-8")) if (ROOT / "docs" / "35-hadrons" / "35-hadrons-ledger.json").exists() else None
        decided = set(L.PREDICATES)
        self.assertEqual(len(decided), 48)
        witnessed = {r for v in L.LEDGER.values() for r in _rows(v)}
        self.assertEqual(witnessed & DROPPED_ROWS, set())
        self.assertEqual(witnessed, decided)
        if rows:
            labels = {r["label"]: r for b in rows["blocks"] for r in b["rows"]}
            for pred in decided:
                lab = pred.split(":")[1]
                self.assertIn(labels[lab]["tag"], ("T", "Ω"), pred)

    def test_package_records_reproduced(self):
        from frc.ledgers import p35_hadrons as L
        rec = ROOT / "src" / "35-hadrons" / "results.json"
        if not rec.exists(): return
        d = json.loads(rec.read_text(encoding="utf-8"))
        fams = {r["id"] for r in d}                                    # one record per family, had.<script>
        reproduced = {"had." + v for v in L.FAMILY.values() if v}
        missing = {f for f in fams if f.startswith("had.")} - reproduced
        self.assertEqual(reproduced - fams, set())
        self.assertEqual(missing, NOT_REPRODUCED)


class MasterHadronsTest(unittest.TestCase):
    def test_block_file(self):
        """The master's hadrons block file (19 October 2026): G8, G9, G10 decided by marked checks, their keys core."""
        from frc.ledgers.master import hadrons as M
        self.assertTrue(M.R.verify_all())
        marks = M.R.markers()
        for lab in M.R.predicates: self.assertIn(lab, marks)
        self.assertEqual(sorted(M.PROOFS), sorted(M.LEAN))
        self.assertEqual(M.BLOCK, "G")
        self.assertEqual(sorted(M.PREDICATES), ["00:G10", "00:G8", "00:G9"])
        self.assertTrue(all(v == "core" for v in M.LEAN.values()))             # a T row of block G binds no chart key (G08)
        kinds = {r["id"]: r["kind"] for r in M.R.results}
        self.assertEqual(kinds["B1"], "CHART"); self.assertEqual(kinds["S1"], "EXACT")


if __name__ == "__main__":
    unittest.main()
