"""The ledger file of 35-hadrons (frc/ledgers/p35_hadrons.py; the 35-hadrons migration of 19 October 2026), the hadrons theme's
exact arithmetic it uses (frc/hadrons.py) and the chart file of its readings (frc/chart_hadrons.py): the colour group against
a brute force over the 4⁹ matrices and the order formula, the moments against the dimension sums, the identities against an
independent evaluation at random rationals, the Sturm count against the float bisection, the Lanczos eigenvalue against a
dense solver where numpy is installed; the ledger green, every check EXACT or CHART, its markers on its deciding checks, its
checks descending from the package's records but the figure script (A5, B8, B9, F1 and F5 are the checks without a record).
The revision of 14 November 2026 adds the registrations of the frame against a direct enumeration, the fixed vectors of
the products against the classical moments, the second order and the heavy-quark identity at random rationals, the
readings of the revised rows, and the wrap operator on three grids against a dense solver where numpy is installed.
The revision of 15 November 2026 adds the Carrier register's relations on the three laboratory Carriers against a search
for the roots, the winding law's residues on the three Subjects, the drive's odd classes against a direct enumeration, the
register's commutator against the matrices, the winding law's readings, and the register's levels against a dense solver
(F6 to F9 and G2 are checks without a record of the package)."""
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

CHART_CHECKS = {"D1", "D2", "D3", "D4", "D5", "D6", "D7", "D8", "D9", "D10", "E1", "F2", "F3", "F4", "F5", "F7", "F9", "G1"}
BEYOND_PACKAGE = {"A5", "B8", "B9", "F1", "F5", "F6", "F7", "F8", "F9", "G2", "G3"}   # the flavour cube, the heavy-quark identity, the scaling, the Sturm brackets, the radial ratio, the winding law, the register
DROPPED_ROWS = {"35:B1", "35:B5", "35:Z1", "35:C6", "35:C22", "35:C23", "35:P8", "35:P11"}   # the rows without a check, and the withdrawn and retired ones
NOT_REPRODUCED = {"had.make_figures"}                                  # the figure script
# the theorem rows that are readings alone (no core declaration) and the rows with a Mathlib reading
READINGS = {"P12"}
CORE_ONLY = {"C1", "C14", "C15", "X1", "X2", "X3", "X7", "P4", "P5"}


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
                  H.vector_spacing(), H.gap_identity(), *H.spin_split(), *H.second_order(), *H.second_order_pairs(), *H.hqs_identity()):
            self.assertTrue(p.is_zero())

    def test_registrations(self):
        """The lines the frame maps to themselves, against a direct enumeration on a generating set; the abelianisation; the
        fixed vectors of the products against the classical moments where the two agree."""
        F, G = H.colour_group()
        gens = H.generating_set(F, G); units = [x for x in F.elements() if x != F.zero]
        ls = H.lines(F); self.assertEqual(len(ls), 21)
        for act in (lambda g: g, lambda g: H.wedge2(F, g), lambda g: H.conj_matrix(F, g)):
            kept = [v for v in ls if all(H.mat_vec(F, act(g), v) in [tuple(F.mul(x, c) for c in v) for x in units] for g in gens)]
            self.assertEqual(kept, []); self.assertEqual(H.invariant_lines(F, G, act), [])
        self.assertEqual(len(H.derived_subgroup(F, G)), 54); self.assertEqual(H.abelianisation_order(F, G), 4)
        self.assertEqual(H.pairing_fixed_dim(F, G), (1, True))
        E, _ = H.weyl_moments()
        self.assertEqual([H.fixed_dim(F, G, a, b) for a, b in ((0, 0), (1, 1), (2, 0), (3, 0), (0, 3))], [1, 1, 0, 1, 1])
        self.assertEqual((H.fixed_dim(F, G, 1, 1), H.fixed_dim(F, G, 2, 0), H.fixed_dim(F, G, 3, 0)), (E[(1, 1)], E[(2, 0)], E[(3, 0)]))
        self.assertEqual((H.fixed_dim(F, G, 2, 2), H.fixed_dim(F, G, 3, 1)), (2, 0))

    def test_second_order_and_heavy_at_random_rationals(self):
        rng = random.Random(3514)
        def r(): return Fraction(rng.randrange(1, 60), rng.randrange(1, 9))
        q = Fraction(1, 4)
        for _ in range(50):
            ml, ms, v = r(), r(), r(); z = ml / ms; vls, vss = v * z, v * z * z
            M = {t: H.baryon_mass(t, ml, ms, v, vls, vss) for t in H.BARYONS}
            sq = v * (1 - z) ** 2
            self.assertEqual((M["N"] + M["Xi"]) / 2 - (3 * M["Lam"] + M["Sig"]) / 4, sq / 8)
            self.assertEqual(M["Del"] - 2 * M["Sgs"] + M["Xis"], sq / 4); self.assertEqual(M["Sgs"] - 2 * M["Xis"] + M["Om"], sq / 4)
            mb, mc, wb, wc = r(), r(), r(), r()
            Lb, Lc = mb + 2 * ml - 3 * q * v, mc + 2 * ml - 3 * q * v
            avg = lambda mQ, w: ((mQ + ml - 3 * q * w) + 3 * (mQ + ml + q * w)) / 4
            self.assertEqual(Lb - Lc, mb - mc); self.assertEqual(Lb - Lc, avg(mb, wb) - avg(mc, wc))
        sums, one, two = H.coleman_glashow_sums()
        self.assertEqual((one, two), (0, 0)); self.assertEqual(sums["p"], (Fraction(1), Fraction(0)))
        self.assertTrue(H.scales_with_masses()); self.assertEqual(len(H.model_masses()), 24)

    def test_revised_readings(self):
        h = CH.heavy_averaged()
        self.assertEqual(h["baryon"], Fraction("3333.14")); self.assertEqual(h["meson"], Fraction("3340.24375"))
        self.assertEqual(h["residual"], Fraction("-7.10375")); self.assertEqual(h["Lb_pred"], Fraction("5626.70375"))
        t = CH.thresholds()
        self.assertEqual(t["vector"]["residual"], Fraction("-3.75")); self.assertEqual(t["vector"]["omega"], Fraction("7.4"))
        self.assertTrue(abs(t["octet"]["residual"]) < t["octet"]["threshold"])
        so = CH.second_order_reading()
        self.assertEqual(so["third"], Fraction("6.05")); self.assertTrue(so["octet"] < 0 < so["model_octet"])
        self.assertTrue(CH.cg_within_error()["within"]); self.assertTrue(CH.np_lattice()["within"])
        j = CH.joint_solution_law()
        self.assertAlmostEqual(j["lam_hf"], 0.46624, places=4); self.assertAlmostEqual(j["lam_l"], 0.84016, places=4)
        self.assertAlmostEqual(j["ratio"], 0.32217, places=4); self.assertAlmostEqual(j["alpha_needed"], 0.9717, places=3)
        self.assertAlmostEqual(3 * j["lam_l"] - 0.75 * j["lam_hf"], j["lam_N"], places=12)
        self.assertAlmostEqual(j["lam_hf"] * j["lam_l"], (2 * 0.5 / 9) * j["C"] * j["alpha_s"], places=12)
        rr = CH.radial_ratio_law()
        self.assertAlmostEqual(rr["ratio"] ** 2, 7 / 3, places=12); self.assertAlmostEqual(rr["law"], rr["ratio"], places=12)
        self.assertTrue(rr["pole"] < rr["bw_lo"] < rr["ratio"] < rr["bw"] < rr["bw_hi"])

    def test_winding_law_readings(self):
        """λ_k² = (3/2)π + 2πk; the scale at which the law reads the nucleon mass, and the nucleon at the imported scale; the
        squares of the Hamiltonian's two levels over π/2 beside the law's 3 and 7."""
        import math
        for k in range(4): self.assertAlmostEqual(CH.winding_law(k) ** 2, 1.5 * math.pi + 2 * math.pi * k, places=12)
        w = CH.winding_readings(); m = CH.pdg()
        self.assertAlmostEqual(w["lam_N"], 2.1708038, places=6); self.assertAlmostEqual(w["scale"], 432.521, places=3)
        self.assertAlmostEqual(w["MN_at_scale"], 955.154, places=3); self.assertAlmostEqual(w["excess"], 0.01729, places=4)
        self.assertAlmostEqual(w["scale"] * w["lam_N"], float(m["N"]), places=9)
        self.assertEqual(w["measured"], m["N"] / CH.DATA["scales"]["sqrt_sigma"])
        self.assertTrue(float(w["measured"]) < w["lam_N"])
        h = CH.hamiltonian_readings()
        self.assertAlmostEqual(h["sq0"], 3.17158, places=4); self.assertAlmostEqual(h["sq1"], 7.05552, places=4)
        self.assertAlmostEqual(h["ratio"], 1.49151, places=4); self.assertTrue(h["ratio"] < CH.radial_ratio_law()["ratio"])

    def test_carrier_register(self):
        """The Carrier register on the three laboratory Carriers: the roots of −1 and of 2⁻¹ against a search, (ħc)² ≡ 2S for
        the four pairs, 4c⁴ ≡ 1, h = −ħ a root of −1 with h + ħ ≡ 0, and the winding law M² ≡ N hcσ from 4M²c⁴ ≡ N hcσ."""
        for Om in H.CARRIERS:
            S, hb, cs = H.register_roots(Om)
            self.assertEqual(Om, 4 * S + 1)
            if Om < 10 ** 5:
                self.assertEqual(sorted(x for x in range(Om) if (x * x + 1) % Om == 0), sorted(hb))
                self.assertEqual(sorted(x for x in range(Om) if (2 * x * x - 1) % Om == 0), sorted(cs))
            for x in hb: self.assertEqual((x * x + 1) % Om, 0)
            for x in cs: self.assertEqual((2 * x * x - 1) % Om, 0)
            rows, twoS, fourth = H.scale_register(Om)
            self.assertEqual(twoS, 2 * S); self.assertEqual(len(rows), 4)
            self.assertEqual({r[2] for r in rows}, {2 * S}); self.assertEqual((2 * S + pow(2, -1, Om)) % Om, 0)
            self.assertTrue(fourth)
            four_c4, pairs, law = H.winding_register(Om)
            self.assertEqual(four_c4, [1, 1]); self.assertEqual(pairs, [(Om - 1, 0)] * 2); self.assertTrue(law)
            free, g, ratios = H.winding_root_free(Om)
            self.assertEqual(len(free), 4); self.assertTrue(all(r[2] for r in free)); self.assertTrue(g and ratios)
            self.assertEqual(len({2 * (Om - h) * c % Om for h, c, _ in free}), 2)      # 2hc takes two values, a pair
        self.assertEqual(H.register_roots(233), (58, (89, 144), (74, 159)))

    def test_subject_residues_and_drive(self):
        """The winding law's residues (4k + 3)κ on the three Subjects, with 4λ² + N ≡ 0; the drive's odd powers against a
        direct enumeration (none is ±1, so no odd class of the drive is real); the register's commutator against the matrices."""
        for p in H.SUBJECTS:
            kap, res, turn = H.winding_residues(p)
            self.assertEqual(p, 4 * kap + 1); self.assertTrue(turn)
            for k, (r, ok) in enumerate(res):
                self.assertEqual(r, (4 * k + 3) * kap % p); self.assertTrue(ok); self.assertEqual((4 * r + 4 * k + 3) % p, 0)
            self.assertEqual((res[1][0] - res[0][0]) % p, (p - 1) % p)                 # one radial step: one turn of the drive
            g = 2
            self.assertEqual(sorted(pow(g, j, p) for j in range(p - 1)), list(range(1, p)))   # 2 generates the drive's cycle
            odd, real, units = H.drive_odd_classes(p, g)
            self.assertEqual((odd, real, units), ((p - 1) // 2, 0, 0))
            self.assertEqual([j for j in range(1, p - 1, 2) if pow(g, j, p) in (1, p - 1)], [])
            q, z, c = H.register_commutator(p, g)
            self.assertEqual(q % p, 1); self.assertEqual(pow(z, p, q), 1); self.assertNotEqual(z % q, 1); self.assertNotEqual(c, 0)
        self.assertEqual([H.register_commutator(p, 2) for p in H.SUBJECTS], [(53, 16, 34), (347, 4, 174), (6197, 16, 4364)])
        for p in H.SUBJECTS[:2]:
            q, vec = H.register_commutator_direct(p, 2)
            self.assertEqual((q, vec[2]), (H.register_commutator(p, 2)[0], H.register_commutator(p, 2)[2]))
            self.assertEqual([(a + b) % q for a, b in zip(vec[1:], reversed(vec[1:]))], [0] * (p - 1))   # the image is odd

    def test_register_levels(self):
        """The two lowest levels of the register's Hamiltonian on the odd functions of C_p: the Lanczos values against a
        dense solver (numpy) on 13 and 173; the second level above the first on the three Subjects."""
        import math
        lv = {p: CH.register_levels(p) for p in H.SUBJECTS}
        for p, (e0, e1) in ((13, ("2.2519", "3.3870")), (173, ("2.2324", "3.3302")), (1549, ("2.2323", "3.3300"))):
            self.assertEqual((f"{lv[p]['E0']:.4f}", f"{lv[p]['E1']:.4f}"), (e0, e1)); self.assertTrue(lv[p]["E1"] - lv[p]["E0"] > 1)
            self.assertEqual(lv[p]["dim"], (p - 1) // 2)
        try:
            import numpy as np
        except ImportError:
            return
        for p in (13, 173):
            m = (p - 1) // 2; x = np.arange(1, m + 1)
            S = (2 / math.sqrt(p)) * np.sin(2 * math.pi * np.outer(x, x) / p)
            self.assertTrue(np.allclose(S @ S, np.eye(m), atol=1e-10))
            E = np.linalg.eigvalsh(np.diag(x.astype(float)) + S @ np.diag(x.astype(float)) @ S) * math.sqrt(2 * math.pi / p)
            self.assertAlmostEqual(lv[p]["E0"], float(E[0]), places=7); self.assertAlmostEqual(lv[p]["E1"], float(E[1]), places=6)

    def test_wrap_operator_on_three_grids(self):
        """The body's Hamiltonian on 600, 1200 and 2400 sites by a dense solver (numpy): E₀ 2.2320, 2.2322, 2.2323 and
        C 3.50, 3.51, 3.52; the joint solution on the winding law on 2400 sites 0.468, 0.841, 0.323; the 600-site values
        against the chart's."""
        try:
            import numpy as np
        except ImportError:
            return
        import math
        a_s = 2 * math.pi / (9 * math.log(2)); lam = math.sqrt(1.5 * math.pi); out = {}
        for n in (600, 1200, 2400):
            h = 30.0 / (n + 1); x = h * np.arange(1, n + 1)
            T = (2 * np.eye(n) - np.eye(n, k=1) - np.eye(n, k=-1)) / h ** 2
            w, V = np.linalg.eigh(T); P = (V * np.sqrt(np.abs(w))) @ V.T
            E, U = np.linalg.eigh(P + np.diag(x)); u = U[:, 0] / math.sqrt(h)
            E0, C = float(E[0]), float((u[0] / h) ** 2); K = (2 * 0.5 / 9) * C
            lh = (-lam + math.sqrt(lam * lam + 9 * K * a_s)) / 1.5
            out[n] = (E0, float(E[1] / E[0]), C, lh, (lam + 0.75 * lh) / 3, 1.5 * lh / lam)
        for n, e0, c in ((600, "2.2320", "3.50"), (1200, "2.2322", "3.51"), (2400, "2.2323", "3.52")):
            self.assertEqual(f"{out[n][0]:.4f}", e0); self.assertEqual(f"{out[n][2]:.2f}", c)
        self.assertEqual(tuple(f"{v:.3f}" for v in out[2400][3:]), ("0.468", "0.841", "0.323"))
        self.assertEqual(tuple(f"{v:.3f}" for v in out[600][3:]), ("0.466", "0.840", "0.322"))
        wr = CH.wrap_readings(); j = CH.joint_solution_law()
        self.assertAlmostEqual(wr["E0"], out[600][0], places=6); self.assertAlmostEqual(wr["ratio"], out[600][1], places=5)
        self.assertAlmostEqual(wr["C"], out[600][2], places=3); self.assertAlmostEqual(j["ratio"], out[600][5], places=4)

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
        self.assertEqual(len(L.LEDGER), 41)
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
        self.assertEqual(len(decided), 47)
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
