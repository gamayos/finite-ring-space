"""The ledger file of 46-yangmills (frc/ledgers/p46_yangmills.py; Phases 1–2 of the paper home, 7–8 November 2026), the yangmills
theme's exact arithmetic (frc/yangmills.py) and the chart file (frc/chart_yangmills.py): the norm-one torus against the
eigenvector count by brute force on small shells, the centre against the order formula's torsion, the F_4 residue counts
against the compact Weyl moments and an independent fixed-vector enumeration, the plaquette series against the Bessel ratio
and the finite-group quotient of interactions.c1_from_traces, the drive exponent against pow, the one-loop run against a
direct evaluation; the ledger green, every check EXACT or CHART, its markers on its deciding checks."""
import math
import re
import unittest
from fractions import Fraction as Q
from itertools import product
from pathlib import Path

from frc import arith as A
from frc import interactions as I
from frc import yangmills as Y
from frc import chart_yangmills as CY
from frc.registry import MARKER

ROOT = Path(__file__).resolve().parents[2]
CHART_CHECKS = {"E1", "E2", "E3", "F2", "F3", "G1", "G2"}


class YangMillsTest(unittest.TestCase):
    def test_nonsplit_torus_brute_force(self):
        # on the shells 13 and 29: every pair (a, b) with a² − νb² = 1, and the eigenvectors of multiplication by a + b√ν on F_p²
        for p in (13, 29):
            nu = next(x for x in range(2, p) if A.legendre(x, p) == -1)
            T = Y.nonsplit_torus(p, nu)
            brute = [(a, b) for a in range(p) for b in range(p) if (a * a - nu * b * b) % p == 1]
            self.assertEqual(sorted(T), sorted(brute)); self.assertEqual(len(T), p + 1)
            for a, b in T:
                # the matrix of multiplication by a + b√ν in the basis 1, √ν: [[a, νb], [b, a]]; an eigenvector exists iff some
                # nonzero (x, y) satisfies M v = λ v for a λ in F_p
                M = ((a, nu * b % p), (b, a))
                has = any(((M[0][0] * x + M[0][1] * y) % p, (M[1][0] * x + M[1][1] * y) % p) == (lam * x % p, lam * y % p)
                          for lam in range(p) for x in range(p) for y in range(p) if (x, y) != (0, 0))
                self.assertEqual(has, Y.has_eigenvalue(p, a, b, nu), (p, a, b))
            n, k, ev = Y.fixed_lines_nonsplit(p, nu); self.assertEqual((n, k), (p + 1, 2))

    def test_split_torus(self):
        for p in Y.shells_below(60):
            self.assertEqual(sorted(Y.fixed_lines_split(p, A.primitive_root(p))), [(0, 1), (1, 0)])

    def test_centre(self):
        for q in list(range(2, 60)) + [233, 30089, 2408561]:
            self.assertEqual(Y.centre_order(q), 3 if (q + 1) % 3 == 0 else 1)
            self.assertEqual(Y.admissible(q), q % 4 == 1 and q % 3 == 2)

    def test_residue_series(self):
        F, G = Y.H.colour_group()
        series, content = Y.residue_series(F, G)
        w, _ = Y.weyl_residues()
        self.assertEqual({k: series[k] for k in ("gluon", "baryon", "meson", "glueball")}, w)
        self.assertEqual(content, (1, 0, 0, 1))
        # the gluon's fixed vectors by enumeration: no nonzero traceless matrix is fixed by every element
        n = 3; fixed = 0
        zero = tuple(tuple(F.zero for _ in range(n)) for _ in range(n))
        for entries in product(F.elements(), repeat=n * n):
            M = tuple(tuple(entries[i * n + j] for j in range(n)) for i in range(n))
            if M == zero: continue
            tr = F.add(F.add(M[0][0], M[1][1]), M[2][2])
            if tr != F.zero: continue
            if all(I.mat_mul(F, I.mat_mul(F, g, M), I.dagger(F, g)) == M for g in G[:40]) and \
               all(I.mat_mul(F, I.mat_mul(F, g, M), I.dagger(F, g)) == M for g in G):
                fixed += 1
        self.assertEqual(fixed, 0)

    def test_casimirs_b0(self):
        c = Y.casimirs(3); self.assertEqual((c["C_F"], c["C_A"], c["T_F"], c["ratio"]), (Q(4, 3), 3, Q(1, 2), Q(9, 4)))
        for nf in range(0, 20): self.assertEqual(Y.b0(nf), 11 - Q(2 * nf, 3))
        self.assertEqual(Y.casimirs(2)["C_F"], Q(3, 4))

    def test_drive_exponent(self):
        for p in (13, 173):
            ok, g = Y.drive_exponents_unique(p); self.assertTrue(ok)
            for w in range(1, p): self.assertEqual(pow(g, Y.drive_exponent(p, g, w), p), w)

    def test_c1_series(self):
        s2 = Y.c1_series(2, 9)
        # I₂(β)/I₁(β) = β/4 − β³/96 + β⁵/1536 − β⁷/23040 + …, from the Bessel series of interactions
        bes = I.bessel_ratio_series(1, 9)
        self.assertEqual(s2, bes)
        s3 = Y.c1_series(3, 7)
        self.assertEqual(s3[:3], [Q(0), Q(1, 18), Q(1, 216)])
        s2t, tr = Y.c1_series_2T(7); self.assertEqual(sum(tr.values()), 24)
        # the finite-group rational function N(x)/D(x) in x = e^{β/2} of interactions.c1_from_traces, expanded at β = 0.1
        N, D = I.c1_from_traces(tr, 2); beta = 0.1; x = math.exp(beta / 2)
        val = sum(float(c) * x ** k for k, c in enumerate(N)) / sum(float(c) * x ** k for k, c in enumerate(D))
        ser = sum(float(c) * beta ** k for k, c in enumerate(s2t))
        self.assertAlmostEqual(val, ser, places=9)

    def test_chart(self):
        r = CY.run_to_tau(); self.assertAlmostEqual(r["alpha_mtau"], 0.2794, places=3)
        v, dv = CY.m0pp_over_sqrt_sigma(); self.assertTrue(Q("3.69") < v < Q("3.71"))

    def test_adjoint_series(self):
        # the adjoint coefficient by an independent route: E[(χχ̄ − 1) X^k] from the moments directly, and c₈ = Σ_k m_k (β/3)^k/k! / (8 Σ_k E[X^k] (β/3)^k/k!)
        from math import comb, factorial
        E = I.su3_moment
        mX = [sum(comb(k, j) * E(j, k - j) for j in range(k + 1)) / Q(2 ** k) for k in range(7)]
        m8 = [sum(comb(k, j) * (E(j + 1, k - j + 1) - E(j, k - j)) for j in range(k + 1)) / Q(2 ** k) for k in range(7)]
        num = [m8[k] / Q(3) ** k / factorial(k) / 8 for k in range(6)]; den = [mX[k] / Q(3) ** k / factorial(k) for k in range(6)]
        self.assertEqual(I.ps_div(num, den, 6), Y.c_adj_series(8)[:6])
        self.assertEqual(m8[1], 0); self.assertEqual(m8[2], Q(1, 2))                 # no singlet in 8 ⊗ 3, 8 ⊗ 3̄; E[χ₈ (Re χ)²] = 1/2
        s = Y.adjoint_wrap_excess(3); self.assertEqual(s[:3], [Q(0), Q(1, 18), Q(-1, 1296)])
        # the log-free ratio c₈/c₃² by an independent division of the two series
        c3 = Y.c1_series(3, 8); c8 = Y.c_adj_series(8)
        r = I.ps_div(c8[2:], I.ps_mul(c3[1:], c3[1:], 6), 5)
        self.assertEqual(r, Y.adjoint_over_fundamental_squared(5)); self.assertEqual(r[0], Q(9, 8)); self.assertEqual(r[1] / r[0], Q(-1, 18))

    def test_frame_moments_f4(self):
        # the finite frame's own moments over F_4 against the compact multiplicities, and the generating pair
        F, G = Y.H.colour_group()
        gens = Y.generators(F, G); self.assertLessEqual(len(gens), 3)
        m = Y.frame_moments_f4(F, G, 3)
        self.assertTrue(all(fin == cpt for fin, cpt in m.values()))
        self.assertEqual(m[(1, 1)], (1, 1)); self.assertEqual(m[(3, 0)], (1, 1)); self.assertEqual(m[(2, 1)], (0, 0))
        # the centre of SU(3, F_2) by elements
        self.assertEqual(len(Y.H.centre(F, G)), 3)
        # the excess series against the floats: σ₈ − 2σ₃ + ln(9/8) at β = 0.5
        k, s3, s8 = CY.adjoint_ratio(0.5); self.assertAlmostEqual(s8 - 2 * s3 + math.log(9 / 8), sum(float(c) * 0.5 ** i for i, c in enumerate(Y.adjoint_wrap_excess(4))), places=4)

    def test_wrap_spectrum(self):
        from frc import chart_hadrons as CH
        e0, e1, _ = CH.relativistic_ground()
        spec = CY.wrap_spectrum(1, 1, 2)
        self.assertAlmostEqual(spec[0], e0, places=3); self.assertAlmostEqual(spec[1], e1, places=2)
        self.assertAlmostEqual(CY.wrap_spectrum(2, 1, 1, N=300)[0], math.sqrt(2) * CY.wrap_spectrum(1, 1, 1, N=300)[0], places=2)

    def test_t01_routes(self):
        r = CY.short_range_route(cutoffs=(1.0, 0.5))
        self.assertGreater(r["declared_coupling"], r["herbst"][2])                      # C = 3.02 > 4/π: no ground state
        self.assertLess(r["collapse_rc1"], 1.9)
        self.assertAlmostEqual(r["fixed_points"][1.0][0], 3.54, places=1); self.assertAlmostEqual(r["fixed_points"][0.5][0], 3.08, places=1)
        pc = CY.plaquette_channel(); T = pc["table"]
        self.assertAlmostEqual(T["0.06"]["leading"], 4 * math.sqrt(-math.log(0.06)), places=9)   # the paper's leading term
        self.assertTrue(all(T[u]["orders"][7] > 4.7 for u in ("0.06", "0.10", "0.15", "0.20")))
        self.assertLess(T["0.30"]["orders"][7], 4.0)
        self.assertAlmostEqual(float(pc["u_of_beta"]["1"]), 0.06013, places=5)      # against the exact SU(3) integral (0.06013)

    def test_ledger_green_and_markers(self):
        from frc.ledgers import p46_yangmills as L
        self.assertTrue(L.R.verify_all())
        kinds = {r["id"]: r["kind"] for r in L.R.results}
        self.assertEqual({k for k, v in kinds.items() if v == "CHART"}, CHART_CHECKS)
        self.assertTrue(all(v in ("EXACT", "CHART") for v in kinds.values()))
        src = (ROOT / "frc" / "ledgers" / "p46_yangmills.py").read_text(encoding="utf-8")
        marked = set()
        for line in src.splitlines():
            m = MARKER.match(line)
            if m: marked |= set(re.findall(r"\d+:[A-Z]+\d+[a-z]?", m.group(1)))
        self.assertEqual(marked, set(L.PREDICATES))
        for lab, pid in L.PREDICATES.items(): self.assertIn(lab, L.LEDGER[pid])


if __name__ == "__main__":
    unittest.main()
