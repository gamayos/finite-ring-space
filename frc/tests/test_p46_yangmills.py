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
CHART_CHECKS = {"E1", "E2", "E3", "E4", "F2", "F3", "F4", "G1", "G2"}


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
        for q in list(range(2, 60)) + [173, 1549]:          # the laboratory Subjects (the frame is the Subject's)
            self.assertEqual(Y.centre_order(q), 3 if (q + 1) % 3 == 0 else 1)
            self.assertEqual(Y.full_centre(q), q % 3 == 2)

    def test_carrier_triality(self):
        for _, Om in Y.LAB_PAIRS:                            # colour's triality is the Carrier's relation Ω ≡ 5 (mod 12) (46:B5)
            c = Y.carrier_triality(Om); self.assertTrue(c["ok"], c)
        self.assertTrue(Y.carrier_triality(173)["ok"])       # 173 ≡ 5 (mod 12)
        for p in (13, 1549):                                 # 3 | p − 1: the cube roots of unity are residues of the shell
            c = Y.carrier_triality(p); self.assertFalse(c["ok"]); self.assertFalse(c["5 mod 12"])

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
        e = Y.casimirs_from_exponents()                                       # round 03: the frame's own source, no lift
        self.assertEqual((e["form_F"], e["form_A"], e["ratio_T"], e["T_A"]), ((2, 2, 2), (12, 12, 12), 6, 3))
        self.assertEqual((e["C_F"], e["C_A"], e["ratio"], e["singlet"]), (Q(4, 3), 3, Q(9, 4), -8))
        for p in (13, 173, 1549):
            s = Y.split_torus_exponents(p); self.assertEqual(s["ratio"], 6); self.assertEqual(sum(s["exponents"]) % (p * p - 1), 0)
        self.assertEqual(Y.split_torus_exponents(13)["exponents"], [1, 12, 155])

    def test_series_window(self):
        w = Y.series_window(6)
        self.assertEqual({d: w["first_changed"][d] for d in range(2, 8)}, {2: (1, 0), 3: (2, 1), 4: (3, 2), 5: (4, 3), 6: (5, 4), 7: (None, 5)})
        self.assertEqual(w["window"][13], (10, 9))

    def test_drive_exponent(self):
        for p in (13, 173):
            ok, g = Y.drive_exponents_unique(p); self.assertTrue(ok)
            for w in range(1, p): self.assertEqual(pow(g, Y.drive_exponent(p, g, w), p), w)

    def test_c1_series(self):
        s2 = Y.c1_series(2, 9)
        # I₂(β)/I₁(β) = β/4 − β³/96 + β⁵/1536 − β⁷/23040 + …, from the Bessel series of interactions
        bes = I.bessel_ratio_series(1, 9)
        self.assertEqual(s2, [c * 4 ** k for k, c in enumerate(bes)])                 # Wilson's coupling of SU(2) is 4ϑ
        s3 = Y.c1_series(3, 7)
        self.assertEqual(s3[:3], [Q(0), Q(1, 3), Q(1, 6)])
        s2t, tr = Y.c1_series_2T(7); self.assertEqual(sum(tr.values()), 24)
        # the finite-group rational function N(x)/D(x) in x = e^{β/2} of interactions.c1_from_traces, expanded at β = 0.1
        N, D = I.c1_from_traces(tr, 2); beta = 0.1; x = math.exp(beta / 2)
        val = sum(float(c) * x ** k for k, c in enumerate(N)) / sum(float(c) * x ** k for k, c in enumerate(D))
        ser = sum(float(c) * (beta / 4) ** k for k, c in enumerate(s2t))
        self.assertAlmostEqual(val, ser, places=9)

    def test_chart(self):
        r = CY.run_to_tau(); self.assertAlmostEqual(r["alpha_mtau"], 0.2794, places=3)
        v, dv = CY.m0pp_over_sqrt_sigma(); self.assertTrue(Q("3.69") < v < Q("3.71"))

    def test_adjoint_series(self):
        # the adjoint coefficient by an independent route: E[(χχ̄ − 1) X^k] from the moments directly, and c₈ = Σ_k m_k (2ϑ)^k/k! / (8 Σ_k E[X^k] (2ϑ)^k/k!)
        from math import comb, factorial
        E = I.su3_moment
        mX = [sum(comb(k, j) * E(j, k - j) for j in range(k + 1)) / Q(2 ** k) for k in range(7)]
        m8 = [sum(comb(k, j) * (E(j + 1, k - j + 1) - E(j, k - j)) for j in range(k + 1)) / Q(2 ** k) for k in range(7)]
        num = [m8[k] * 2 ** k / factorial(k) / 8 for k in range(6)]; den = [mX[k] * 2 ** k / factorial(k) for k in range(6)]
        self.assertEqual(I.ps_div(num, den, 6), Y.c_adj_series(8)[:6])
        self.assertEqual(m8[1], 0); self.assertEqual(m8[2], Q(1, 2))                 # no singlet in 8 ⊗ 3, 8 ⊗ 3̄; E[χ₈ (Re χ)²] = 1/2
        s = Y.adjoint_wrap_excess(3); self.assertEqual(s[:3], [Q(0), Q(1, 3), Q(-1, 36)])
        # the log-free ratio c₈/c₃² by an independent division of the two series
        c3 = Y.c1_series(3, 8); c8 = Y.c_adj_series(8)
        r = I.ps_div(c8[2:], I.ps_mul(c3[1:], c3[1:], 6), 5)
        self.assertEqual(r, Y.adjoint_over_fundamental_squared(5)); self.assertEqual(r[0], Q(9, 8)); self.assertEqual(r[1] / r[0], Q(-1, 3))

    def test_frame_moments_f4(self):
        # the finite frame's own moments over F_4 against the compact multiplicities, and the generating pair
        F, G = Y.H.colour_group()
        gens = Y.generators(F, G); self.assertLessEqual(len(gens), 3)
        m = Y.frame_moments_f4(F, G, 3)
        self.assertTrue(all(fin == cpt for fin, cpt in m.values()))
        self.assertEqual(m[(1, 1)], (1, 1)); self.assertEqual(m[(3, 0)], (1, 1)); self.assertEqual(m[(2, 1)], (0, 0))
        # the centre of SU(3, F_2) by elements
        self.assertEqual(len(Y.H.centre(F, G)), 3)
        # the excess series against the floats: σ₈ − 2σ₃ + ln(9/8) at ϑ = 0.05
        k, s3, s8 = CY.adjoint_ratio(0.05); self.assertAlmostEqual(s8 - 2 * s3 + math.log(9 / 8), sum(float(c) * 0.05 ** i for i, c in enumerate(Y.adjoint_wrap_excess(4))), places=4)

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
        self.assertAlmostEqual(T[9]["leading"], 4 * math.sqrt(-math.log(T[9]["u"])), places=9)   # the paper's leading term
        self.assertTrue(all(T[n]["orders"][7] > 5.0 for n in (9, 8, 7, 6)))
        self.assertLess(T[3]["orders"][7], 4.0)
        self.assertEqual(pc["unity"]["exact"], Q(23, 54))                           # the computed terms at channel unity
        self.assertAlmostEqual(sum(float(c) / 6 ** k for k, c in enumerate(Y.c1_series(3, 8))), 0.06013, places=5)      # against the exact SU(3) integral at Wilson's β = 1
        cc = CY.chart_cells(); self.assertTrue(cc["law"]); self.assertAlmostEqual(cc["step"], 0.09657, places=5)

    def test_frame_window(self):
        self.assertEqual(Y.first_departure_bounds(13), (26, 49)); self.assertEqual(Y.frame_window_orders(13), (25, 24, 23))
        for q in (2, 3, 13): self.assertEqual(Y.binomial_table(q, q), Y.binomial_table_expected(q, q))
        self.assertEqual(Y.row_identity(2), (162, 0)); self.assertTrue(Y.frobenius_tensor_fixed(2))
        self.assertEqual(Y.frobenius_weights(3), [(1, 1, 5), (1, 5, 1), (5, 1, 1)]); self.assertEqual(len(Y.frobenius_tensor(3)), 1008)
        M = Y.frame_counts_small_field(2, 5); self.assertEqual(M[(4, 1)], 4); self.assertEqual(M[(2, 2)], 2); self.assertEqual(M[(3, 0)], 1)

    def test_spectral_amplitude(self):
        self.assertEqual(Y.z3_mul((0, 1), (0, 1)), (-1, -1)); self.assertEqual(Y.z3_conj((0, 1)), (-1, -1)); self.assertEqual(Y.z3_pow((0, 1), 3), (1, 0))
        n, E, pw = Y.nonsplit_amplitude_exponents(13); self.assertEqual((n, E), (157, [1, 12, 144])); self.assertEqual(pw[0], 3); self.assertEqual(len(pw), 7)
        self.assertTrue(all(t["gcd_nonsplit_cycle"] == 1 for t in Y.subject_phase_table()))
        amp = Y.spectral_amplitude_instance()
        self.assertEqual(amp["distribution"], {(3, 0): 64, (0, 3): 64, (-3, -3): 64, (0, 0): 24}); self.assertEqual(amp["sum"], (0, 0))
        self.assertEqual(amp["moments"][(1, 1)], (8, 0)); self.assertEqual(amp["classes"], 16)
        T = Y.transfer_tally_instance(amp)
        self.assertTrue(T["annihilated"] and T["K_one_zero"]); self.assertEqual(T["multiplicities"], {144: 9, 36: 36, 0: 144, -72: 27})
        self.assertEqual(Y.transfer_annihilator_coefficients(), [0, 373248, -7776, -108, 1])
        from fractions import Fraction
        self.assertEqual(T["mean"]["eigenvalues"], {Fraction(2, 3): 9, Fraction(1, 6): 36, Fraction(0): 144, Fraction(-1, 3): 27})   # the step K = A/216
        self.assertEqual((T["mean"]["trace"], T["mean"]["trace2"]), ((3, 0), (8, 0))); self.assertEqual(Y.transfer_annihilator_mean(), [0, 2, -9, -27, 54])

    def test_subject_spectrum(self):
        expansion = {"a1": 1, "a2": 1, "a3": -1, "moment": 3, "trivial": 0}
        for q in (3, 4, 5, 7, 13, 173, 1549): self.assertEqual(Y.amplitude_coefficients(q), expansion)
        for q in (3, 5, 13):
            d = Y.amplitude_coefficients_direct(q); self.assertEqual({k: d[k] for k in expansion}, expansion)
        self.assertEqual(Y.amplitude_coefficients_direct(13)["classes"], 184)
        for q in (3, 4, 5, 8, 9):                                                # the identity of the proof, class by class
            i = Y.amplitude_identity_classwise(q); self.assertTrue(i["ok"]); self.assertEqual(i["failures"], 0)
        self.assertEqual(len(Y.su3_class_list(13)[0]), 184)
        s = Y.transfer_spectrum_subject(13); self.assertTrue(s["ok"]); self.assertEqual(s["levels"], (5167344, 369096, -344929)); self.assertEqual(s["zero"], 800885251)
        from fractions import Fraction
        self.assertEqual(s["eigenvalues"], (Fraction(1, 157), Fraction(1, 2198), Fraction(-1, 2352)))                 # the eigenvalues of the step with the frame's mean
        self.assertEqual(Y.transfer_spectrum_subject(1549)["eigenvalues"], (Fraction(1, 2397853), Fraction(1, 3716672150), Fraction(-1, 3719070000)))
        self.assertEqual(Y.transfer_spectrum_subject(1549)["levels"], (13822563889181430000, 8917783154310600, -8912033462496097))
        self.assertEqual(Y.transfer_spectrum_subject(3)["levels"], (864, 216, -189)); self.assertEqual(Y.su3_order(3), 6048)

    def test_ring(self):
        from fractions import Fraction
        for q in (3, 4, 5, 7, 13, 173, 1549):
            g = Y.ring_gap(q); self.assertTrue(g["ok"]); self.assertEqual(g["gap"], Fraction(1, q + 1))
            self.assertEqual(g["third"], Fraction(q * q - q + 1, (q + 1) ** 2 * (q - 1)))
        self.assertEqual(Y.ring_step(13)["multipliers"], (Fraction(1, 157), Fraction(1, 2198), Fraction(-1, 2352)))
        self.assertIsNone(Y.split_torus_characters(3, 1)); self.assertIsNone(Y.split_torus_characters(13, 6))
        self.assertEqual(Y.split_torus_characters(13, 1), {"chi1": (0,), "chi2": (1, 11), "chi3": ()})
        h = Fraction(1, 2198)
        self.assertEqual(Y.ring_step_split(13, 1, 2), {0: Fraction(1, 157), 11: h, 3: h, 9: h, 1: h})
        for p, v in ((13, 10), (173, 163), (1549, 1367)):                       # the tally modulo p, the same for every length of the ring
            r = Y.ring_residue(p, 1, 2); self.assertTrue(r["ok"]); self.assertEqual((r["tally"], r["paired"]), (v, v * v % p))
        self.assertEqual(Y.ring_residue(7, 1, 2, g=3)["tally"], 0)              # 7/344 at q = 7, the direct mean over the rungs
        G = Y.ring_gluing_instance(); self.assertTrue(G["ok"]); self.assertEqual(G["values"][0]["mean"], (8, 0))
        self.assertEqual(G["values"][0]["brute"], (373248, 0))                  # the same as a sum over the 216² pairs of rungs

    def test_spectrum_in_pi(self):
        from fractions import Fraction
        for p, pi in ((13, 6), (173, 86), (1549, 774)):                         # 46:C21, the spectrum in 2π = p − 1
            s = Y.spectrum_in_pi(p); self.assertTrue(s["ok"]); self.assertEqual(s["pi"], pi)
            self.assertEqual(s["gap"], Fraction(1, 2 * pi + 2)); self.assertEqual(s["degrees"][2], 8 * pi * (pi + 1) ** 2)
            self.assertEqual(s["cycles"], (2 * pi * (2 * pi + 2), s["degrees"][0]))             # the orders of the two cycles in 2π
            self.assertTrue(Fraction(12072, 100000) < s["chart"][0] < s["chart"][1] < Fraction(12073, 100000))
        self.assertEqual(Y.spectrum_in_pi(13)["degrees"], (157, 2198, 2352))

    def test_product_channels(self):
        pc = Y.product_channels(); self.assertTrue(pc["ok"])                    # 46:C22
        self.assertEqual(pc["A"], [1, 0, 1, 2, 8]); self.assertEqual(pc["instance"]["fixed"], [0, 1, 7, 57])
        self.assertEqual(pc["channels"]["two glueballs"], (8, 57))
        self.assertEqual(Y.frame_counts_small_field(2, 8, pairs=[(3, 3), (4, 4)]), {(3, 3): 11, (4, 4): 92})    # the same counts by the solver on words

    def test_uniform_boundary(self):
        u = Y.uniform_boundary_tally(13, 1, 2); self.assertTrue(u["ok"])        # 46:C23
        self.assertEqual(u["values"], (10, 0, 0, 2, 5, 12, 5, 2, 0, 0, 10, 3)); self.assertEqual(u["others"], (3, 6, 9, 12))
        self.assertEqual(u["paired"], (9, 0, 0, 4, 12, 1, 12, 4, 0, 0, 9, 9)); self.assertEqual(u["five"], (10, 0, 1, 2, 5, 10, 5, 2, 1, 0, 10, 5))
        self.assertEqual(u["period"], 12); self.assertEqual(u["coefficients"], (3, 5, 11, 5, 2, 4, 11, 4, 2, 5, 11, 5))
        self.assertEqual(Y.uniform_boundary_tally(13, 2, 4)["period"], 6)
        self.assertEqual(Y.table_type4(13, 7), {"eigenvalues": (7, 7, 0), "chi1": [(-12, 7), (1, 0)], "chi2": [(14, 7)], "chi3": []})
        for p, first in ((173, 43), (1549, 387)):
            v = Y.uniform_boundary_tally(p, 1, 2); self.assertTrue(v["ok"]); self.assertEqual(v["others"], (first, 2 * first, 3 * first, 4 * first))
        w = Y.uniform_boundary_tally(13, 2, 3); self.assertTrue(w["ok"]); self.assertEqual(len(w["others"]), 4 + 6 - 2)
        self.assertEqual(w["values"][11], 3)

    def test_three_rings(self):
        for q in (3, 4, 5, 7, 8, 9, 11, 13, 16, 17):                             # 46:C25
            self.assertEqual(Y.triple_multiplicities(q), Y.triple_multiplicity_forms(q))
        t = Y.three_rings_tally(13, 1, 2, 3); self.assertTrue(t["ok"])
        self.assertEqual(t["W"], (6, 0, 0, 0, 9, 1, 9, 0, 0, 0, 6, 6)); self.assertEqual(t["regular"], (1, 5, 7, 11))
        self.assertEqual([Y.three_rings_tally(p, 1, 2, 3)["W"][0] for p in (13, 173, 1549)], [6, 25, 616])
        self.assertEqual([Y.three_rings_tally(p, 1, 2, 3)["n122"] for p in (13, 173, 1549)], [2, 4, 2])
        self.assertEqual(Y.three_rings_tally(13, 1, 2, 4)["regular"], (1, 2, 4, 5, 7, 8, 10, 11))

    def test_window_readings(self):
        w = Y.window_readings(13)                                                # 46:C24
        self.assertEqual((w["pairs"], w["nonzero"], len(w["zero"])), (351, 117, 52))
        self.assertEqual(w["count"], {(1, 13): 2574, (13, 1): 2574}); self.assertEqual((w["agree"], w["bound"], w["shift"]), (True, True, True))
        self.assertEqual(w["residues"][0][:3], [0, 9, 11])                       # ϑ/3 + ϑ²/6: 3⁻¹ = 9 and 6⁻¹ = 11 on 13

    def test_shell_series(self):
        s = Y.shell_series(13, 25)                                               # 46:C26
        self.assertEqual(s["h"][:12], [0, 1, 1, 0, 8, 11, 8, 10, 6, 8, 10, 2]); self.assertTrue(s["product"]); self.assertFalse(any(s["power"]))
        self.assertTrue(all(x == 0 for x in s["h"][12:22]) and s["h"][22:] == [1, 3, 3])   # the integers read 0 from the order 12 through 21

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
