"""p27_fields — the ledger file of 27-fields (ledger migration, task LM35, 7 October 2026; the 27-fields migration,
16 October 2026).

"Standard-Model Interactions over Finite Substrate" (Akhtman and Voether, preprint 2026; doi 10.20944/preprints202606.1328.v1).
The paper's predicate ledger is docs/27-fields/27-fields-ledger.json. This file binds its python-witnessed predicates to
the framework: the table of keys (generated from the ledger by ci/make_ledgers.py) and the checks of eight blocks. The
exact checks call the interactions theme (frc/interactions.py) and, for the closed role ladder, the horizon theme
(frc/ladder.py); the continuum readings call the chart theme (frc/chart.py, frc/chart_fields.py) and compare its
readings with rational bounds. Each check names the predicate(s) it witnesses (LEDGER) and carries a `# 27:XN (<key>)`
marker when it decides one (PREDICATES).

The checks are EXACT or CHART, one kind per check. An EXACT check decides by integer, finite-field, rational or
cyclotomic arithmetic; no float decides anything. A CHART check is a continuum reading: floats, transcendental
functions, measured data, dimensional estimates; its label carries "[chart]". The paper's own classes were EXACT, MIXED
and APPROX, one per package record (src/27-fields, twenty-eight scripts run by fldcommon.py); the checks of 7 October
carried their record's class. On 16 October 2026 (the 27-fields migration) MIXED and APPROX split: each mixed check whose
two halves both carry content became an exact check under the old label and a chart check under the label with the
suffix c (B1/B1c, B4/B4c, C8/C8c, E5/E5c, F6/F6c); a check whose float clause only illustrated an exact clause was
retagged EXACT; a check that is wholly a continuum reading was retagged CHART; and the APPROX checks of the finite gauge
correspondence B1, B2 and B4 became EXACT (the roots of unity in Q(ζ_M), the 24 quaternions of 2T over Q, the area law's
rational function positive beyond x = 1), the rest CHART. FAMILY names the package record (fld.<script>) each check
reproduces. The package stays the paper's published witness until its release pins the framework (tasks LM33, LM36).
The Lean side (16 October 2026): the theorems of the interactions theme (Theme/Interactions.lean, Theme/Unitary.lean) and its
kernel-decided certificates (Theme/Fields.lean), the paper module FrcCore/Fields.lean, and the chart readings on Mathlib
(FrcMathlib/Theme/Fields.lean); the keys in Keys/Interactions.lean, the certificates Ledgers/P27Fields.lean.

No check reads the scale import, and no numeral above Ω is formed. The "Ω ≡ 5 (mod 12)" of F7 is the Carrier's residue
clause, decided in the integers; E8 reads the centre of the colour frame on the shells.

The revision of 16 November 2026 (27-fields-20260625/reports/revision-blueprint-20261116.md, task T22): the checks of
the lift (B5) and of the torsion period (F8) retire with their clauses; B3 keeps the compact expansion; C7 and C9 state
the boost's cancellation; C11 and C12 decide the rows 27:C13 and 27:C14, the root of the drive and the two branches.
The revision of 17 November 2026 (27-fields-20260625/reports/review-20261117-1-adjudication.md): C13 decides the row
27:C15, the diagonal torus over K and its two cycles; A1 runs on both cycles; A5 names the sides L ≥ 4; H3 carries the
square of a Hermitian amplitude matrix.
The revision of 17 November 2026, pass 9 (27-fields-20260625/reports/review-20261117-2-adjudication.md): C14 runs the
units of K, the two readings of a weight and the rotations of the row 27:C15; C15 decides the row 27:C16, one charge
system in the frame of rank five; A2 and B1 run on the split and the unitary cycles of the three Subjects.
Pass 10 of the same day (27-fields-20260625/reports/pass10-dryrun-20261117.md): C16 decides the row 27:P10, no fractional
charge without colour, and the kernel of the product of the hypercharge cycle with the two frames.
Pass 11 of the same day (27-fields-20260625/reports/pass11-dryrun-20261117.md): C17 decides the row 27:C17, the Frobenius
parity of a tally, and C18 reads the lift of one chronon to the doublet for the rows 27:C15 and 27:C4.
The pass of 27 November 2026 (27-fields-20260625/reports/colour-rank-20261127/t18/): C19 decides the row 27:C18,
commutation and the internal frame; E9, E10 and E11 decide the rows 27:C19, C20 and C21, the blocks of the lift of the
drive, the exact constraints on the colour rank and the integers of the one-loop form; the chart check E12 decides the
row 27:C22, the colour rank in the imported one-loop law.

    python3 -m frc.ledgers.p27_fields         every block, the census; exit 1 if a check fails (≈ 40 s)
    python3 -m frc.ledgers.p27_fields C       one block (A to H)
    from frc.ledgers.p27_fields import R; R.predicate("27:C5")    one predicate: its blocks run once per session

Blocks:  A  electromagnetism: the finite U(1), Maxwell's uniqueness, the bare coupling     (27:C2, C3, X1, X2, X3)
         B  the finite gauge correspondence                                              (27:C1, C7, C12)
         C  the weak sector: the SU(2) connection, the breaking, the spectrum, the roots of the drive, commutation
                                                                                         (27:C4–C6, C10, C13, C14, C18, X1, X3–X6)
         D  the electroweak scale against the gauge transmutation form                   (27:Z1)
         E  the strong sector: SU(3) over F_4 and on the laboratory Subjects, the string tension, the β-function,
            the rank of the colour frame                                                 (27:C7, C8, C19–C22, X1, X7, Z1)
         F  matter: one generation, unification, the generations, the residue mod 12      (27:C6, C8–C11, X8, X9, P1, P2, P4, P6, P7)
         G  the running couplings and the mass mechanism                                 (27:C6, P3, P5, Z1)
         H  flavour: the Koide form and the strong-CP angle                              (27:X10, X11, P8, P9)

Checks: 68, of them 49 EXACT and 19 CHART (A3, A4, A11, A12, B1c, B3, B4c, C8c, D1, E2, E5c, E7, E12, F3, F6c, G2,
G3, G4, H2). The notebook frc/ledgers/p27_fields.ipynb runs one predicate per cell, the cell's id its key (gate G13).
"""
import random
import sys
from collections import Counter
from fractions import Fraction as Q
from itertools import product
from math import comb, gcd, isqrt

from frc.registry import Registry
from frc import arith
from frc import interactions as I
from frc import ladder as LD
from frc import chart as CH
from frc import chart_fields as CF

# ---- generated by ci/make_ledgers.py from docs/27-fields/27-fields-ledger.json; edit the ledger, not this table ----
PAPER = "27-fields"
KEYS = {"A1": "p27001", "A2": "p27002", "A3": "p27003", "A4": "p27004", "A5": "p27005", "A6": "p27006", "B1": "p00046", "B2": "p27008", "B3": "p27009", "B4": "p27010", "B5": "p27011", "B6": "p00047", "B7": "p27021", "B8": "p28011", "B9": "p28007", "B10": "p27054", "B11": "p27055", "B12": "p27056", "C1": "p27013", "C2": "p27014", "C3": "p27015", "C4": "p27016", "C5": "p27017", "C6": "p27018", "C7": "p27019", "C8": "p27020", "C9": "p27053", "C10": "p27022", "C11": "p27023", "C12": "p27049", "C13": "p27051", "C14": "p27052", "C15": "p27057", "C16": "p27058", "C17": "p27060", "C18": "p27061", "C19": "p27062", "C20": "p27063", "C21": "p27064", "C22": "p27065", "X1": "p27024", "X2": "p27025", "X3": "p27026", "X4": "p27027", "X5": "p27028", "X6": "p27029", "X7": "p27030", "X8": "p27031", "X9": "p27032", "X10": "p27033", "X11": "p27034", "P1": "p27035", "P2": "p27036", "P3": "p27037", "P4": "p27038", "P5": "p27039", "P6": "p27040", "P7": "p27041", "P8": "p27042", "P9": "p27043", "P10": "p27059", "Z1": "p27047"}       # every row of the ledger: its label and its accession key
LEAN = {"C1": "core, ml", "C2": "core", "C3": "core", "C4": "core", "C5": "core", "C6": "core, ml", "C7": "core, ml", "C8": "core", "C9": "core", "C10": "core", "C11": "core", "C13": "core", "C14": "core", "C15": "core", "C16": "core", "C17": "core", "C18": "core", "C19": "core", "C20": "core", "C21": "core", "X1": "core", "X2": "core", "X3": "core", "X4": "core", "X5": "core", "X6": "core", "X7": "core, ml", "X8": "core", "X9": "core", "X10": "core", "X11": "core", "P1": "core", "P2": "core", "P3": "core, ml", "P4": "core, ml", "P5": "core, ml", "P6": "core", "P7": "core", "P8": "core", "P9": "core", "P10": "core"}       # the rows with a Lean declaration: the libraries whose key files prove them
# ---- end of the generated table ----

LEAN_ONLY = ()                  # the predicates with a Lean declaration and no python check (gate G12): none

# The paper's predicate ledger (predicates cited as 27:XN): the predicate(s) each check witnesses. The union over a
# family's checks contains the package's row list for that family (fldcommon.LEDGER); since 16 October 2026 the checks
# also witness the rows the package did not (27:X1, P2, P6, P7, C12), and the chart check B3 witnesses the row 27:C12 in
# place of 27:C1. The checks C11 and C12 (16 November 2026), C13 to C18 (17 November 2026) and C19 and E9 to E12
# (27 November 2026) reproduce no package record.
LEDGER = {
    "A1": "27:C2", "A2": "27:X2, 27:C2", "A3": "27:C3, 27:C2", "A4": "27:C2, 27:C3", "A5": "27:C2, 27:X3, 27:X1", "A6": "27:X3, 27:C2",
    "A7": "27:C2, 27:C3", "A8": "27:C3", "A9": "27:C2", "A10": "27:C2", "A11": "27:C2", "A12": "27:C2",
    "B1": "27:C1", "B1c": "27:C1", "B2": "27:C1", "B3": "27:C12", "B4": "27:C7, 27:C1", "B4c": "27:C7, 27:C1",
    "C1": "27:C4", "C2": "27:C4, 27:X1", "C3": "27:C5, 27:X5", "C4": "27:C6, 27:X4", "C5": "27:C5, 27:X5, 27:X3", "C6": "27:C5, 27:X5",
    "C7": "27:C4", "C8": "27:C6", "C8c": "27:C6", "C9": "27:C4", "C10": "27:C10", "C11": "27:C13, 27:X6", "C12": "27:C14, 27:X6",
    "C13": "27:C15", "C14": "27:C15", "C15": "27:C16", "C16": "27:P10, 27:C16", "C17": "27:C17", "C18": "27:C15, 27:C4",
    "C19": "27:C18",
    "D1": "27:Z1",
    "E1": "27:C7", "E2": "27:X7", "E3": "27:C7", "E4": "27:X7, 27:C7", "E5": "27:X7, 27:C7", "E5c": "27:X7, 27:C7", "E6": "27:X7",
    "E7": "27:Z1", "E8": "27:C7, 27:C8, 27:X1", "E9": "27:C19", "E10": "27:C20", "E11": "27:C21", "E12": "27:C22",
    "F1": "27:C8, 27:X8, 27:C6, 27:P2, 27:P6, 27:P7", "F2": "27:C9, 27:X8", "F3": "27:P4", "F4": "27:C9, 27:X8", "F5": "27:C10",
    "F6": "27:C10, 27:X9, 27:P1, 27:P2, 27:P6, 27:P7", "F6c": "27:C10, 27:X9, 27:P1", "F7": "27:C11",
    "G1": "27:C6", "G2": "27:P3", "G3": "27:P5", "G4": "27:Z1",
    "H1": "27:X10, 27:P8", "H2": "27:P8", "H3": "27:X11, 27:P9", "H4": "27:X11, 27:P9",
}

# the package record (fld.<script>) each check reproduces (a chart check with the suffix c reproduces its parent's record)
FAMILY = {
    "A1": "em1_prototype", "A2": "em1_prototype", "A3": "em1_prototype", "A4": "em1_prototype",
    "A5": "enumerate_maxwell", "A6": "enumerate_maxwell", "A7": "audit_finitism", "A8": "audit_finitism",
    "A9": "audit_finitism", "A10": "audit_finitism", "A11": "o2_numbers", "A12": "p2",
    "B1": "correspondence", "B1c": "correspondence", "B2": "correspondence", "B3": "correspondence", "B4": "correspondence",
    "B4c": "correspondence",
    "C1": "p3", "C2": "ew1", "C3": "ew1", "C4": "ew1", "C5": "weak_spectrum", "C6": "weak_spectrum",
    "C7": "weak_current", "C8": "weak_current", "C8c": "weak_current", "C9": "p4", "C10": "p10",
    "C11": "push", "C12": "push",                                          # the record reports/d218-push-20261116 of the paper, no package record
    "C13": "review2",                                                      # the record reports/review-20261117-1-adjudication of the paper, no package record
    "C14": "review3", "C15": "review3", "C16": "review3", "C17": "review3", "C18": "review3",   # the record reports/review-20261117-2-adjudication of the paper, no package record
    "C19": "rank", "E9": "rank", "E10": "rank", "E11": "rank", "E12": "rank",   # the record reports/colour-rank-20261127/t18 of the paper, no package record
    "D1": "v_scale",
    "E1": "qcd", "E2": "qcd", "E3": "p5", "E4": "string_tension", "E5": "string_tension", "E5c": "string_tension", "E6": "p6",
    "E7": "p6", "E8": "missing_rank",
    "F1": "generation", "F2": "p8", "F3": "p8", "F4": "p8b", "F5": "p9", "F6": "p9b", "F6c": "p9b", "F7": "p11",
    "G1": "p1", "G2": "p1", "G3": "p7", "G4": "p7",
    "H1": "koide", "H2": "koide", "H3": "strongcp", "H4": "strongcp",
}

BLOCK = {"A": "electromagnetism: the finite U(1), Maxwell's uniqueness, the bare coupling",
         "B": "the finite gauge correspondence",
         "C": "the weak sector: the SU(2) connection, the breaking, the spectrum, the roots of the drive, commutation",
         "D": "the electroweak scale against the gauge transmutation form",
         "E": "the strong sector: SU(3) over F_4 and on the laboratory Subjects, the string tension, the β-function, the rank of the colour frame",
         "F": "matter: one generation, unification, the generations, the residue mod 12",
         "G": "the running couplings and the mass mechanism",
         "H": "flavour: the Koide form and the strong-CP angle"}

# the deciding check of each witnessed predicate (the other checks that touch it are corroboration)
PREDICATES = {
    "27:C1": "B2", "27:C2": "A5", "27:C3": "A3", "27:C4": "C2", "27:C5": "C6", "27:C6": "C4", "27:C7": "E8", "27:C8": "F1",
    "27:C9": "F4", "27:C10": "F6", "27:C11": "F7", "27:C12": "B3", "27:C13": "C11", "27:C14": "C12", "27:C15": "C13", "27:C16": "C15", "27:P10": "C16", "27:C17": "C17",
    "27:C18": "C19", "27:C19": "E9", "27:C20": "E10", "27:C21": "E11", "27:C22": "E12",
    "27:X1": "A5", "27:X2": "A2", "27:X3": "A6", "27:X4": "C4", "27:X5": "C6", "27:X6": "C11", "27:X7": "E4", "27:X8": "F1",
    "27:X9": "F6", "27:X10": "H1", "27:X11": "H3",
    "27:P1": "F6", "27:P2": "F6", "27:P3": "G2", "27:P4": "F3", "27:P5": "G3", "27:P6": "F6", "27:P7": "F6", "27:P8": "H2",
    "27:P9": "H3",
    "27:Z1": "D1",
}

R = Registry("27", "fields", LEDGER, PREDICATES, sources=[__file__])

PI = CH.pi_bracket()                                  # π between two rationals (Machin; the chart theme)


def _within(x, centre, tol):
    """|x − centre| < tol, x a float of the chart converted exactly."""
    return abs(Q(x) - centre) < tol


def _pi_scaled_within(value_over_pi, centre, tol):
    """|v/π − centre| < tol for both ends of the bracket of π (v > 0)."""
    return all(abs(value_over_pi / p - centre) < tol for p in PI)


# ------------------------------------------------------------------------------------------------------------
# block A: electromagnetism (27:C2, C3, X1, X2, X3)
# The finite U(1) lives on the phase cycle Z/M (em1_prototype). Its plaquette flux, Wilson action, covariant difference
# and global phases are gauge invariant as integer identities. The holonomy of a loop is the enclosed flux (discrete
# Stokes). The lattice Green's function carries the Coulomb coefficient 1/4π on the chart, and the field-quadratic action
# makes like charges repel. The range-1 gauge- and cube-invariant quadratic actions form a space of dimension 2 on
# L = 4, 5, 6: one relevant operator, Maxwell's transverse projector, and one irrelevant one (enumerate_maxwell); that
# uniqueness is the gauging of the phase frame (27:X1). audit_finitism makes the same claims with no float, and o2_numbers
# and p2 read the bare coupling 1/4π on the chart.
@R.block("A", BLOCK["A"])
def block_A():
    """Block A — electromagnetism: A1–A12 (A3, A4, A11, A12 CHART)."""
    # A1 gauge invariance on Z/M for M = p − 1 and M = p + 1 on the Subjects 13, 173, 1549 (the split and the unitary cycle of
    #    the row 27:C15), on 200 random
    #    configurations each (L = 4). The Wilson action is a function of the plaquette values, so their multiset decides it.
    rng = random.Random(20260615); L = 4; n = L ** 3; ok = True; det = []
    for M in (12, 14, 172, 174, 1548, 1550):
        okF = okS = okC = okG = True
        for _ in range(200):
            A = [[rng.randrange(M) for _ in range(n)] for _ in range(3)]
            lam = [rng.randrange(M) for _ in range(n)]; phi = [rng.randrange(M) for _ in range(n)]
            Ap = I.gauge_transform(A, lam, M, L)
            vals, valsp = [], []
            for i in range(3):
                for j in range(i + 1, 3):
                    F, Fp = I.plaquette(A, i, j, M, L), I.plaquette(Ap, i, j, M, L)
                    okF &= F == Fp; vals += F; valsp += Fp
            okS &= Counter(vals) == Counter(valsp)
            phip = [(a + b) % M for a, b in zip(phi, lam)]
            okC &= I.gauge_transform([[(-a) % M for a in row] for row in A], phi, M, L) == \
                I.gauge_transform([[(-a) % M for a in row] for row in Ap], phip, M, L)       # φ(x+e_i) − φ(x) − A_i(x)
            c = rng.randrange(M)
            okG &= I.gauge_transform(A, [c] * n, M, L) == A
        ok &= okF and okS and okC and okG
        det.append(f"M={M}: {okF} {okS} {okC} {okG}")
    R.check("A1", "plaquette flux, Wilson action, covariant difference and global superselection gauge-invariant over Z/M, "
            "M = p − 1 and M = p + 1 on the Subjects 13, 173, 1549 (the split and the unitary cycle), on 200 random configurations each (L = 4)", ok, "; ".join(det))

    # A2 discrete Stokes: the holonomy of a rectangle is the enclosed flux mod M, and adjacent rectangles add
    rng = random.Random(156); L = 8; ok_s = ok_a = True
    for M in (12, 14, 172, 174, 1548, 1550):
        for _ in range(100):
            Ax = {(x, y): rng.randrange(M) for x in range(L) for y in range(L)}
            Ay = {(x, y): rng.randrange(M) for x in range(L) for y in range(L)}
            F = {(x, y): (Ax[(x, y)] + Ay[((x + 1) % L, y)] - Ax[(x, (y + 1) % L)] - Ay[(x, y)]) % M
                 for x in range(L) for y in range(L)}
            a, b = rng.randrange(2, L), rng.randrange(2, L)
            enclosed = sum(F[(x, y)] for x in range(a) for y in range(b)) % M
            ok_s &= I.holonomy(Ax, Ay, 0, 0, a, b, L, M) == enclosed
            a2 = rng.randrange(1, L - a + 1)
            ok_a &= (I.holonomy(Ax, Ay, 0, 0, a, b, L, M) + I.holonomy(Ax, Ay, a, 0, a2, b, L, M)) % M == \
                I.holonomy(Ax, Ay, 0, 0, a + a2, b, L, M)
    # 27:X2 (p27025)
    R.check("A2", "charge = winding: the holonomy of a loop is the enclosed flux mod M (discrete Stokes) and additive over "
            "adjacent loops, M = p − 1 and M = p + 1 on the Subjects 13, 173, 1549, 100 random fields each (L = 8)", ok_s and ok_a, f"Stokes {ok_s}, additive {ok_a}")

    # A3 [chart] the Coulomb coefficient of the L = 128 periodic lattice Green's function (the chart theme's separable sums)
    C, target, resid, g0 = CF.coulomb_fit(128)
    ratio = Q(C) / Q(target)
    # 27:C3 (p27015)
    R.check("A3", "[chart] the lattice Green's function on L = 128 carries the Coulomb coefficient: C/(1/4π) within 2 %, the "
            "fit residual below 2 %", abs(ratio - 1) < Q(2, 100) and Q(resid) < Q(2, 100),
            f"C = {C:.5f}, 1/4π = {target:.5f}, ratio = {C / target:.4f}, rel. residual = {100 * resid:.2f} %, g(0) = {g0:.4f}",
            kind="CHART")

    # A4 [chart] the sign: like charges repel under the field-quadratic action, gravity's linear coupling attracts (L = 48)
    seps, Uem, Ugr = CF.sign_dichotomy(48)
    em = all(Q(Uem[i]) > Q(Uem[i + 1]) > 0 for i in range(len(seps) - 1))
    gr = all(Q(Ugr[i]) < Q(Ugr[i + 1]) < 0 for i in range(len(seps) - 1))
    R.check("A4", "[chart] like charges repel (U_EM > 0, falling with r) and gravity attracts (U < 0, deepening as r → 0) at "
            "r = 6 … 20 on L = 48", em and gr, "U_EM×1e3 = " + ", ".join(f"{1000 * u:.3f}" for u in Uem), kind="CHART")

    # A5 Maxwell's plaquette action is admissible (L = 5), and the admissible space has exact corank 2 on L = 4, 5, 6. The
    #    gauge condition K(k)d(k) = 0 has the exponents −1, 0, 1, 2 in each direction; they are distinct modulo L exactly
    #    for L ≥ 4, so the constraint system on the coefficients is the same for every side L ≥ 4.
    pars, rows5 = I.maxwell_constraints(5)
    cM = I.maxwell_form(5)
    ok = all(sum(r.get(a, 0) * cM[a] for a in r) == 0 for r in rows5) and any(cM)
    det = [f"{len(pars)} range-1 parameters"]
    adm = {}
    for L in (4, 5, 6):
        pars, rows = I.maxwell_constraints(L)
        rk = I.rank_mod(rows, len(pars), (1 << 61) - 1)
        basis = I.nullspace(rows, len(pars))
        adm[L] = basis
        ok &= len(pars) - rk == 2 == len(basis)
        det.append(f"L={L}: corank {len(pars) - rk} over F_(2^61-1), rational nullity {len(basis)}")
    # 27:C2 (p27014), 27:X1 (p27024)
    R.check("A5", "Maxwell's plaquette action is gauge- and hypercubic-invariant; the range-1 translation-, gauge- and "
            "hypercubic-invariant quadratic actions have exact corank 2 on L = 4, 5, 6; the exponents −1, 0, 1, 2 of the gauge "
            "condition are distinct modulo L exactly for L ≥ 4, so the constraint system is that of every side L ≥ 4: the "
            "gauging of the phase frame by the one recipe leaves no choice of operator",
            ok and all((len({e % L_ for e in (-1, 0, 1, 2)}) == 4) == (L_ >= 4) for L_ in range(2, 12)), "; ".join(det))

    # A6 the split: the quadratic part of the cosine symbol has rank 1 on the admissible space, its image is the
    #    transverse projector |k|²δ − kk (exactly), the constant part vanishes, so the second operator is O(k⁴)
    P = I.transverse_projector(); ok = True; det = []
    flat = lambda S0, S2: [x for r in S0 for x in r] + [x for a in S2 for b in a for c in b for x in c]
    for L in (4, 5, 6):
        vecs = [flat(*I.symbol_taylor(I.kernel_of(v))) for v in adm[L]]
        rk = len(vecs[0]) - len(I.nullspace([{k: v[k] for k in range(len(v)) if v[k]} for v in vecs], len(vecs[0])))
        rel = next(v for v in vecs if any(v))
        S2 = rel[9:]; Pf = [x for a in P for b in a for c in b for x in c]
        lam = next(s / p for s, p in zip(S2, Pf) if p)
        proj = all(s == lam * p for s, p in zip(S2, Pf)) and lam != 0 and not any(rel[:9])
        ok &= rk == 1 and proj
        det.append(f"L={L}: {rk} relevant + {len(vecs) - rk} irrelevant, relevant = {lam} × transverse projector")
    # 27:X3 (p27026)
    R.check("A6", "the admissible space splits into one relevant O(k²) operator, exactly the transverse projector "
            "|k|²δ − kk, and one irrelevant O(k⁴) operator, on L = 4, 5, 6", ok, "; ".join(det))

    # A7 F(dλ) = 0 on all 64 basis gauge fields of L = 4, hence for every λ by linearity. A constant gauge is inert.
    L = 4; worst = 0
    for s in range(L ** 3):
        lam = [int(x == s) for x in range(L ** 3)]
        A = I.gradient(lam, L)
        for i in range(3):
            for j in range(i + 1, 3):
                worst = max(worst, max(abs(v) for v in I.plaquette(A, i, j, None, L)))
    const = all(v == 0 for row in I.gradient([7] * L ** 3, L) for v in row)
    R.check("A7", "F(dλ) = 0 exactly on all 64 basis gauge fields (L = 4), and the gradient of a constant vanishes",
            worst == 0 and const, f"max |F| = {worst}")

    # A8 the L = 4 Green's function in exact rationals (the quarter-turn DFT): two unit charges at separation 1
    axis = [I.green_exact(4, (k, 0, 0)) for k in range(4)]
    R.check("A8", "the L = 4 Coulomb Green's function is an exact rational: U(separation 1) = 257/7680, and "
            "G(0,0,0) > G(1,0,0) > G(2,0,0)", axis[1] == Q(257, 7680) and axis[0] > axis[1] > axis[2],
            "G(n,0,0) = " + ", ".join(str(g) for g in axis))

    # A9 the admissible nullity by the integer Gram matrix of the constraints (the package's route), rank mod two primes
    pars, rows = I.maxwell_constraints(4); npar = len(pars)
    gram = [[0] * npar for _ in range(npar)]
    for r in rows:
        items = list(r.items())
        for a, x in items:
            for b, y in items: gram[a][b] += x * y
    grows = [{b: gram[a][b] for b in range(npar) if gram[a][b]} for a in range(npar)]
    rk = max(I.rank_mod(grows, npar, 2147483647), I.rank_mod(grows, npar, 2147483629))
    R.check("A9", "the O1 admissible nullity is 2 by the exact rank of the integer Gram matrix (123 range-1 parameters, L = 4)",
            npar - rk == 2 and npar == 123, f"parameters {npar}, rank {rk}, nullity {npar - rk}")

    # A10 the Wilson action is cyclotomic: 1 − cos(2πF/M) = 1 − (ζ^F + ζ^−F)/2 lies in Q(ζ_M). Its values at (12, 1),
    #     (12, 3), (52, 13), (8, 1) are 1 − √3/2, 1, 1, 1 − √2/2, decided by the square of 2cos and by the sign of cos.
    def zc(M, F):
        v = [0] * M; v[F % M] += 1; v[(-F) % M] += 1
        return v
    def zsq(v, M):
        w = [0] * M
        for a, x in enumerate(v):
            for b, y in enumerate(v): w[(a + b) % M] += x * y
        return w
    def is_value(M, F, sq, sign):
        v = zsq(zc(M, F), M); v[0] -= sq
        quarter = Q(F, M) % 1
        positive = quarter < Q(1, 4) or quarter > Q(3, 4)
        return I.cyclo_zero(v, M) and (sign == 0 or positive == (sign > 0))
    ok = is_value(12, 1, 3, 1) and I.cyclo_zero(zc(12, 3), 12) and I.cyclo_zero(zc(52, 13), 52) and is_value(8, 1, 2, 1)
    R.check("A10", "1 − cos(2πF/M) is exact in Q(ζ_M): 2cos(2π/12) = √3, cos(2π·3/12) = cos(2π·13/52) = 0, 2cos(2π/8) = √2",
            ok, "(12,1): 1 − √3/2; (12,3): 1; (52,13): 1; (8,1): 1 − √2/2")

    # A11 [chart] the bare coupling as phase-channel capacity: 1/α_bare = 4π, the hierarchy α/(m_p/m_P)² on the measured
    #     constants, the gap 4π/9 → 137.04 of the electron, of index 3 on the charge cycle
    inv_bare, ratio_f, gap_f = CF.o2_numbers(); d = CF.DATA["o2_numbers"]
    hier = d["m_P"] ** 2 / (d["alpha0_inv"] * d["m_p"] ** 2)
    ok = _pi_scaled_within(Q(inv_bare), 4, Q(1, 10 ** 12)) and 10 ** 36 < hier < 2 * 10 ** 36 and abs(Q(ratio_f) / hier - 1) < Q(1, 10 ** 9)
    ok &= _pi_scaled_within(d["alpha0_inv"] / 4, Q(10905, 1000), Q(1, 100))
    ok &= _pi_scaled_within(d["alpha0_inv"] * 9 / 4, Q(98145, 1000), Q(1, 100))             # the electron, of index 3: (1/α)/(4π/9)
    R.check("A11", "[chart] 1/α_bare = 4π for the unit index of the charge cycle and 4π/9 for the electron, of index 3; the EM/gravity hierarchy α/(m_p/m_P)² on the measured m_p, m_P and α lies in "
            "[10³⁶, 2·10³⁶]; the gap 4π/9 → 137.04 is a factor 98.1 (the open part)", ok,
            f"hierarchy = {ratio_f:.3e}, gap = {gap_f:.3f} for the unit index, {9 * gap_f:.2f} for the electron", kind="CHART")

    # A12 [chart] the order-one coefficient 1, and the saturation profile 4πr² sin E = q with its core and self-energy
    a20 = Q(CF.saturation_potential(20)) * 20
    rstar = Q(CF.saturation_core()); U = Q(CF.saturation_self_energy(CF.saturation_core()))
    ok = all(abs(a20 * 4 * p - 1) < Q(1, 100) for p in PI)                           # r·A₀(20) against 1/4π within 1 %
    ok &= all(abs(rstar ** 2 * 4 * p - 1) < Q(1, 10 ** 12) for p in PI)            # r* = (4π)^(−1/2)
    ok &= all(Q(1, 2) < U * 8 * p * rstar < 2 for p in PI) and U > 0             # U of the order q²/(8πr*)
    R.check("A12", "[chart] α_bare = q²/4π = 1/4π with coefficient 1 (q = 1, the unit index of the charge cycle, one phase quantum); the weak-field Coulomb "
            "coefficient r·A₀(r) of the saturation profile 4πr² sin E = q at r = 20 within 1 % of 1/4π; the core r* = (4π)^(−1/2); "
            "a finite self-energy of the order q²/(8πr*)", ok,
            f"r·A₀(20) = {CH.show(a20, '.5f')}, r* = {CH.show(rstar, '.5f')}, U(>r*) = {CH.show(U, '.4f')}", kind="CHART")


# ------------------------------------------------------------------------------------------------------------
# block B: the finite gauge correspondence (27:C1, C7, C12)
# correspondence.py has eight blocks. Z_M embeds in U(1) with a positive Wilson weight (A). SU(2, F_3) = 2T is a finite
# subgroup of SU(2, C) of order 24 = |SL(2, F_3)|, with S ≥ 0 (B) and S a class function (D). Near the identity
# S = (ε²/2n) Tr X² + O(ε⁴), the Yang–Mills term (C), and the window residue grows linearly in H (E). The area law σ > 0
# follows from positivity on 2T (F). The character lift is fixed on the shells (G). Finite quadrature converges on the
# near-identity ball (H). Since 16 October 2026 A, B, D and F are decided exactly (B1, B2, B4: Q(ζ_M), the quaternions
# over Q, Q[x]); C, E, G and H are the chart's resolvable-window reading (B3, B5, row 27:C12), with B1c and B4c the
# chart clauses of B1 and B4.
@R.block("B", BLOCK["B"])
def block_B():
    """Block B — the finite gauge correspondence: B1, B2, B4 EXACT; B1c, B3, B4c, B5 CHART."""
    # B1 (A) Z_M -> U(1), j -> ζ^j, exactly in Q(ζ_M) for M = p − 1 and p + 1 on 13, 173, 1549: a homomorphism (x^j x^k reduced modulo Φ_M
    #    is ζ^{(j+k) mod M}, since ζ^M = 1), injective (the M canonical forms are distinct), and the Wilson weight
    #    1 − Re ζ^k = |1 − ζ^k|²/2 as an identity of Z[ζ_M], positive off k ≡ 0
    ok = True; det = []
    for M in (12, 14, 172, 174, 1548, 1550):
        hom, inj = I.roots_embed(M); ident, pos = I.wilson_weight(M)
        ok &= hom and inj and ident and pos and len(I.roots_of_unity(M)) == M
        det.append(f"M={M}: homomorphism {hom}, injective {inj}, weight identity {ident}, positive off 0 {pos}")
    R.check("B1", "Z_M embeds in U(1) as the M-th roots of unity, exactly in Q(ζ_M): j ↦ ζ^j is a homomorphism and injective "
            "on Z/M for M = 12, 14, 172, 174, 1548, 1550 (the split and the unitary cycles of the Subjects 13, 173, 1549); the Wilson weight "
            "1 − Re ζ^k = |1 − ζ^k|²/2 is an identity of Z[ζ_M], so it is ≥ 0, and it vanishes only at k ≡ 0", ok, "; ".join(det))

    # B1c [chart] the window residue of the embedding, 2π/M, at M = 1000
    res = 2 * PI[1] / 1000
    R.check("B1c", "[chart] the residue 2π/M of the embedding Z_M → U(1) at M = 1000 is below 10⁻²", res < Q(1, 100),
            f"2π/M < {CH.show(res, '.5f')}", kind="CHART")

    # B2 (B, D) 2T is 24 unit quaternions with integer and half-integer coordinates, each an SU(2) matrix over the Gaussian
    #    rationals, closed under the quaternion product. |SL(2, F_3)| = 24. S(U) = 1 − ½ Re Tr U is nonnegative and a class
    #    function (all 24 × 24 pairs, exact).
    G, closed, unit, traces = I.tetrahedral_quaternions()
    su2 = all(I.su2_unitary(x) for x in G)
    sl23 = I.sl2_order(3)
    S = [1 - x[0] for x in G]                                                     # 1 − ½ Re Tr U, Tr U = 2a
    cls = I.trace_class_function(G)
    ok = len(G) == 24 == len(set(G)) and closed and unit and su2 and sl23 == 24
    ok &= traces == {2: 1, -2: 1, 0: 6, 1: 8, -1: 8} and min(S) >= 0 and cls
    # 27:C1 (p27013)
    R.check("B2", "SU(2, F_3) = 2T is a finite subgroup of SU(2, C), exactly over Q: 24 unit quaternions with integer and "
            "half-integer coordinates, closed under the quaternion product, each unitary with det 1 over the Gaussian rationals; "
            "|SL(2, F_3)| = 24; the trace multiset {2:1, −2:1, 0:6, 1:8, −1:8}; S(U) = 1 − ½ Re Tr U ≥ 0 on 2T and a class "
            "function", ok, f"|2T| = {len(G)}, |SL(2,F_3)| = {sl23}, closed {closed}, unit {unit}, min S = {min(S)}")

    # B3 (C) [chart] low curvature, read in the chart: S/ε² → Tr X²/2n for SU(2) and SU(3) with an O(ε⁴) residue. The
    #    statement is the compact group's.
    x2, x3 = (Q(1, 2), Q(-1, 2)), (Q(1, 2), Q(-1, 2), Q(0))
    c2, c3 = sum(x * x for x in x2) / 4, sum(x * x for x in x3) / 6                 # Tr X²/(2n)
    eps = Q(1, 1000)
    ok = abs(Q(CF.s_fund_diag(x2, eps)) / eps ** 2 - c2) < Q(1, 10 ** 6)
    res = [(Q(CF.s_fund_diag(x2, e)) - c2 * e ** 2) / e ** 4 for e in (Q(1, 10), Q(1, 100), Q(1, 1000))]
    ok &= max(abs(r) for r in res) < 1
    ok &= abs(Q(CF.s_fund_diag(x3, eps)) / eps ** 2 - c3) < Q(1, 1000)
    # 27:C12 (p27049)
    R.check("B3", "[chart] the low-curvature expansion of the compact Wilson action: S(exp iεX) = (ε²/2n) Tr X² + O(ε⁴), the "
            "Yang–Mills coefficient 1/(2n), for SU(2) (c = 1/8) and SU(3) (c = 1/12), the residue below ε⁴ at ε = 1/10, "
            "1/100 and 1/1000", ok, f"c = {c2}, {c3}", kind="CHART")

    # B4 (F) the area law from positivity on 2T, exactly. Σχ = 0, and c₁(β) = N(x)/D(x) in x = e^{β/2}, with
    #    N = (x − 1)(x³ + 5x² + 5x + 1) and D − N = 4x³ + 6x² + 12x + 2. N, D and D − N are positive for every x > 1 by the
    #    Taylor shift to x = 1 + y, so 0 < c₁ < 1 and σ = −ln c₁ > 0 for every β > 0.
    Nn, Dd, positive = I.area_law_rational()
    exact = sum(t * m for t, m in traces.items()) == 0 and positive
    exact &= Nn == [Q(c) for c in (-1, -4, 0, 4, 1)] and Dd == [Q(c) for c in (1, 8, 6, 8, 1)]
    c1_at = I.area_law_rational(Q(3, 2))[3]                                       # one rational x > 1, exactly
    exact &= 0 < c1_at < 1
    R.check("B4", "the area law's coefficient on 2T, exactly: Σχ = 0 over the trace multiset; c₁(β) = "
            "(x⁴ + 4x³ − 4x − 1)/(x⁴ + 8x³ + 6x² + 8x + 1), x = e^{β/2}, has numerator, denominator and their difference "
            "positive for every x > 1 (the Taylor shift to x = 1 + y), so 0 < c₁ < 1 and σ = −ln c₁ > 0 for every β > 0",
            exact, f"c₁(x = 3/2) = {c1_at}")

    # B4c [chart] the same c₁ on the chart at β = 0.2, 0.5, 1.0: in (0, 1) and increasing in β
    vals = [Q(CF.c1_traces(traces, 2, b)) for b in (Q(2, 10), Q(5, 10), Q(1))]
    R.check("B4c", "[chart] c₁(β) of 2T on the chart at β = 0.2, 0.5, 1.0 lies in (0, 1) and increases with β, so σ = −ln c₁ "
            "is positive and falling", all(0 < c < 1 for c in vals) and vals[0] < vals[1] < vals[2],
            "c₁ = " + ", ".join(CH.show(c, ".3f") for c in vals), kind="CHART")


# ------------------------------------------------------------------------------------------------------------
# block C: the weak sector (27:C4, C5, C6, C10, X1, X3–X6)
# p3 builds SU(2, F_3) over K = F_9 with its Wilson invariance and the centraliser of a diagonal frame move. ew1 reads the
# drive's weights on the Subjects 13, 173, 1549 (the gauging of the spinor frame, 27:X1), with the neutral mass matrix, ρ = 1 and the
# Weinberg angle from the charge spectrum. weak_spectrum takes the mass form of the template's covariant term at the
# broken vacuum over Q, and on the Subject's extension K at 13, 173 and 1549. weak_current sums the V − A characters and
# derives G_F (C8), read against the measured G_F on the chart (C8c). p4 decouples the Frobenius branch. p10 reads
# chirality relative to the drive.
@R.block("C", BLOCK["C"])
def block_C():
    """Block C — the weak sector: C1–C10 EXACT, C8c CHART."""
    # C1 SU(2, 3) over F_9 = F_3[i] has order 24 and its Wilson trace is invariant exhaustively. The plaquette and the
    #    doublet transform covariantly. The diagonal frame move diag(i, −i) commutes with the diagonal frame moves alone, a
    #    unitary cycle of order 4.
    K = I.Fq2(3, 0, 2)
    SU2 = [((a, b), (c, d)) for a, b, c, d in product(K.elements(), repeat=4)
           if I.mat_mul(K, I.dagger(K, ((a, b), (c, d))), ((a, b), (c, d))) == ((K.one, K.zero), (K.zero, K.one))
           and I.det(K, ((a, b), (c, d))) == K.one]
    mm = lambda X, Y: I.mat_mul(K, X, Y); inv = lambda X: I.dagger(K, X); tr = lambda X: I.trace(K, X)
    ok = len(SU2) == 24 == 3 * (9 - 1)
    ok &= any(mm(X, Y) != mm(Y, X) for X in SU2 for Y in SU2) and all(tr(X)[1] == 0 for X in SU2)
    ok &= all(tr(mm(mm(g, X), inv(g))) == tr(X) for g in SU2 for X in SU2)
    Uab, Ubc, Ucd, Uda = SU2[5], SU2[11], SU2[17], SU2[23]; ga, gb, gc, gd = SU2[3], SU2[8], SU2[14], SU2[20]
    P = mm(mm(Uab, Ubc), mm(Ucd, Uda))
    U2 = [mm(mm(ga, Uab), inv(gb)), mm(mm(gb, Ubc), inv(gc)), mm(mm(gc, Ucd), inv(gd)), mm(mm(gd, Uda), inv(ga))]
    P2 = mm(mm(U2[0], U2[1]), mm(U2[2], U2[3]))
    ok &= P2 == mm(mm(ga, P), inv(ga)) and tr(P2) == tr(P)
    psi_a, psi_b = (SU2[1][0][0], SU2[1][1][0]), (SU2[2][0][0], SU2[2][1][0])
    sub = lambda u, w: tuple(K.sub(x, y) for x, y in zip(u, w))
    D = sub(psi_a, I.matvec(K, Uab, psi_b)); D2 = sub(I.matvec(K, ga, psi_a), I.matvec(K, U2[0], I.matvec(K, gb, psi_b)))
    ok &= D2 == I.matvec(K, ga, D)
    t = (0, 1); drive = ((t, K.zero), (K.zero, K.conj(t)))
    cent = sum(1 for X in SU2 if mm(drive, X) == mm(X, drive))
    ok &= drive in SU2 and cent == 4
    R.check("C1", "SU(2, F_3) over F_9: order 24, non-abelian, Tr ∈ F_3; Tr(gMg⁻¹) = Tr M exhaustively; the "
            "plaquette conjugates and the doublet is covariant; the diagonal frame move diag(i, −i) has centraliser of order "
            "exactly 4, the unitary cycle", ok,
            f"|SU(2,3)| = {len(SU2)}, Tr P = {tr(P)}, centraliser {cent}")

    # C2 the drive on the Subjects 13, 173, 1549. Ad_drive fixes H and scales E, F by g^{±2}. A matrix commutes with
    #    the drive exactly when it is diagonal (X·δ − δ·X has the entries b(h − g) and c(g − h) off the diagonal), so the
    #    matrices of determinant 1 that commute with the drive are the split cycle diag(a, a⁻¹), one for each of the p − 1
    #    nonzero residues; an element of the boost cycle with b ≠ 0 does not commute with the drive. No set of frame moves is enumerated: the
    #    loops run over the residues of the shell and over 300 products of the generators.
    ok = True; det = []
    for p in (13, 173, 1549):
        g = arith.primitive_root(p)
        mul = lambda X, Y, p=p: ((X[0] * Y[0] + X[1] * Y[2]) % p, (X[0] * Y[1] + X[1] * Y[3]) % p,
                                 (X[2] * Y[0] + X[3] * Y[2]) % p, (X[2] * Y[1] + X[3] * Y[3]) % p)
        ti = pow(g, p - 2, p); drive, drive_i = (g, 0, 0, ti), (ti, 0, 0, g)
        eig = {}
        for name, Xb in (("H", (1, 0, 0, p - 1)), ("E", (0, 1, 0, 0)), ("F", (0, 0, 1, 0))):
            Y = mul(mul(drive, Xb), drive_i); c = next(i for i in range(4) if Xb[i])
            eig[name] = Y[c] * pow(Xb[c], p - 2, p) % p
            assert all(Y[i] == eig[name] * Xb[i] % p for i in range(4))
        ok &= eig["H"] == 1 and eig["E"] == g * g % p != 1 and eig["F"] == ti * ti % p != 1 and eig["E"] * eig["F"] % p == 1
        ok &= all((mul((1, b, 0, 1), drive) == mul(drive, (1, b, 0, 1))) == (b == 0) for b in range(p))
        ok &= all((mul((1, 0, c, 1), drive) == mul(drive, (1, 0, c, 1))) == (c == 0) for c in range(p))
        torus = {(a, 0, 0, pow(a, p - 2, p)) for a in range(1, p)}
        ok &= len(torus) == p - 1 and all(T[0] * T[3] % p == 1 and mul(T, drive) == mul(drive, T) for T in torus)
        rng = random.Random(p); M = (1, 0, 0, 1)
        for _ in range(300):
            M = mul(M, rng.choice(((1, 1, 0, 1), (0, p - 1, 1, 0), (1, 0, 1, 1), drive)))
            ok &= (M[0] * M[3] - M[1] * M[2]) % p == 1 and (mul(M, drive) == mul(drive, M)) == (M[1] == 0 and M[2] == 0)
        sq = {x * x % p for x in range(p)}; nu = next(x for x in range(2, p) if x not in sq)
        a, b = next((a, b) for a in range(p) for b in range(1, p) if (a * a - nu * b * b) % p == 1)
        ns = (a, nu * b % p, b, a)
        ok &= mul(ns, drive) != mul(drive, ns)
        det.append(f"F_{p}: g = {g}, weights H {eig['H']}, E {eig['E']}, F {eig['F']}, split cycle of {len(torus)}, ν = {nu}")
    ok &= det[0].startswith("F_13: g = 2, weights H 1, E 4, F 10, split cycle of 12")
    # 27:C4 (p27016)
    R.check("C2", "the weights of the transport of two chronons, diag(g, g⁻¹), on the Subjects 13, 173, 1549: Ad_drive H = H, and E, F are scaled by g^{±2} ≠ 1 (4 and "
            "10 on 13); a matrix over the shell commutes with it exactly when it is diagonal, and the diagonal "
            "matrices of determinant 1 are the split cycle diag(a, a⁻¹), one for each of the p − 1 nonzero residues; an "
            "element of the boost cycle with b ≠ 0 does not commute: the gauging of the spinor frame", ok, "; ".join(det))

    # C3 the neutral (W₃, B) mass matrix ¼v²[[g², −gg'], [−gg', g'²]] has determinant 0 (the photon) and trace M_Z²
    names = ("g", "gp", "v"); gg, gp, v = (I.Poly.var(names, x) for x in names)
    M2 = [[gg * gg * v * v * Q(1, 4), -gg * gp * v * v * Q(1, 4)], [-gg * gp * v * v * Q(1, 4), gp * gp * v * v * Q(1, 4)]]
    MW2, MZ2 = gg * gg * v * v * Q(1, 4), (gg * gg + gp * gp) * v * v * Q(1, 4)
    ok = (M2[0][0] * M2[1][1] - M2[0][1] * M2[1][0]).is_zero() and M2[0][0] + M2[1][1] == MZ2
    ok &= MW2 * (gg * gg + gp * gp) == MZ2 * gg * gg                              # ρ = M_W²/(M_Z² cos²θ_W) = 1
    R.check("C3", "the neutral (W₃, B) mass matrix has a zero eigenvalue (the photon) and the other M_Z² = (g² + g'²)v²/4; "
            "custodial ρ = 1 as a polynomial identity", ok, f"M_Z² = {MZ2}")

    # C4 the Weinberg angle from the charge spectrum: Tr T₃²/Tr Q² = 1/2 for a lone lepton doublet, 3/8 for a generation
    def sin2(ferm):
        t3 = sum(Q(a) ** 2 * m for a, qq, m in ferm); q2 = sum(Q(qq) ** 2 * m for a, qq, m in ferm)
        return t3 / q2, t3, q2
    lep = [(Q(1, 2), 0, 1), (Q(-1, 2), -1, 1)]
    gen = [(Q(1, 2), 0, 1), (Q(-1, 2), -1, 1), (0, 1, 1), (Q(1, 2), Q(2, 3), 3), (Q(-1, 2), Q(-1, 3), 3), (0, Q(-2, 3), 3),
           (0, Q(1, 3), 3)]
    s_lep, s_gen, t3, q2 = sin2(lep)[0], *sin2(gen)
    # 27:C6 (p27018), 27:X4 (p27027)
    R.check("C4", "sin²θ_W = Tr T₃²/Tr Q²: 1/2 for a lone lepton doublet, 3/8 for a complete generation (Tr T₃² = 2, "
            "Tr Q² = 16/3)", s_lep == Q(1, 2) and t3 == 2 and q2 == Q(16, 3) and s_gen == Q(3, 8), f"{s_lep}, {s_gen}")

    # C5 the mass form of the template's covariant term (A4) at the broken vacuum over Q: M²_ab = Re (X_a φ₀)†(X_b φ₀), with
    #    X = (gT₁, gT₂, gT₃, g'Y) and φ₀ = (0, v). The eigenvectors e₁, e₂ (M_W²), (0, 0, g', g) (0, the photon) and
    #    (0, 0, g, −g') (M_Z²) are independent, so the spectrum is {0, M_W² (×2), M_Z²}. At sin²θ_W = 3/8 the ratio
    #    M_W²/M_Z² is cos²θ_W = 5/8.
    names = ("i", "g", "gp", "v"); iu, gg, gp, v = (I.Poly.var(names, x) for x in names)
    h = Q(1, 2); z = I.Poly.const(names, 0)
    T = [[[z, h + z], [h + z, z]], [[z, -iu * h], [iu * h, z]], [[h + z, z], [z, -h + z]], [[h + z, z], [z, h + z]]]
    X = [[[gg * e for e in row] for row in T[0]], [[gg * e for e in row] for row in T[1]],
         [[gg * e for e in row] for row in T[2]], [[gp * e for e in row] for row in T[3]]]
    phi0 = [z, v]
    Xphi = [[Xa[r][0] * phi0[0] + Xa[r][1] * phi0[1] for r in range(2)] for Xa in X]
    M2 = [[(Xphi[a][0].conj() * Xphi[b][0] + Xphi[a][1].conj() * Xphi[b][1]).real() for b in range(4)] for a in range(4)]
    MW2, MZ2 = gg * gg * v * v * Q(1, 4), (gg * gg + gp * gp) * v * v * Q(1, 4)
    apply = lambda vec: [sum((M2[a][b] * vec[b] for b in range(4)), z) for a in range(4)]
    vecs = {"e1": ([1 + z, z, z, z], MW2), "e2": ([z, 1 + z, z, z], MW2), "photon": ([z, z, gp, gg], z),
            "Z": ([z, z, gg, -gp], MZ2)}
    ok = all(all((x - lamb * y).is_zero() for x, y in zip(apply(vec), vec)) for vec, lamb in vecs.values())
    ok &= not (gp * (-gp) - gg * gg).is_zero()                                      # the 4 eigenvectors' determinant −(g² + g'²) ≠ 0
    ok &= MW2 * (gg * gg + gp * gp) == MZ2 * gg * gg
    ok &= (M2[2][2] * M2[3][3] - M2[2][3] * M2[3][2]).is_zero()
    ok &= Q(1) / (1 + (Q(3, 8) / (1 - Q(3, 8)))) == Q(5, 8)                        # g'²/g² = 3/5 ⇒ cos²θ_W = 5/8
    R.check("C5", "the spectrum of the template's mass form over Q: eigenvalues {0, g²v²/4 (×2), (g² + g'²)v²/4}, the "
            "photon the exact kernel ∝ (0, 0, g', g), ρ = 1, det(W₃, B) ≡ 0, M_W²/M_Z² = 5/8 at sin²θ_W = 3/8", ok,
            f"M²[W1,W2] = {M2[0][1]} (the real part)")

    def prim_roots(p_):
        fs = [f for f in range(2, p_) if (p_ - 1) % f == 0 and all(f % d for d in range(2, isqrt(f) + 1))]
        return [g_ for g_ in range(2, p_) if all(pow(g_, (p_ - 1) // f, p_) != 1 for f in fs)]
    # C6 the mass form of the doublet on the Subject's extension (16 November 2026). K = F_p[η], η² = ν a nonsquare of the
    #    shell, the Frobenius σ(η) = −η the conjugation, an element a pair (x, y) = x + yη. The generators are the
    #    anti-Hermitian T₁ = ½[[0,1],[−1,0]], T₂ = (η/2)[[0,1],[1,0]], T₃ = (η/2)diag(1,−1), T₄ = (η/2)·1, with couplings
    #    g, g, g, g'. Q_ab = ½(⟨X_aφ₀, X_bφ₀⟩ + ⟨X_bφ₀, X_aφ₀⟩) at the unit vacuum φ₀ = (0, 1) and B_ab = −2 tr(T_aT_b) take
    #    values in the shell; B = diag(1, −ν, −ν, −ν). The operator B⁻¹Q has the photon (0, 0, g', g) as kernel, the value
    #    g²/4 on (1,0,0,0) and (0,1,0,0), and (g² + g'²)/4 on (0, 0, g, −g'); the four vectors have the determinant
    #    −(g² + g'²). T₃ + T₄ fixes the vacuum. On the Subjects 13, 173, 1549, at every nonsquare ν of 13 and seven of 173
    #    and of 1549, at three couplings each. At g' = ±i g the neutral block is nonzero and squares to zero (the excluded
    #    case). At the frame's rational g'² = (3/5) g² the ratio is 5/8; 15 is a square on 173 and 1549 and not on 13.
    def mass_form(p_, nu, g1, g2):
        add = lambda u, w: ((u[0] + w[0]) % p_, (u[1] + w[1]) % p_)
        mul = lambda u, w: ((u[0] * w[0] + nu * u[1] * w[1]) % p_, (u[0] * w[1] + u[1] * w[0]) % p_)
        conj = lambda u: (u[0], (-u[1]) % p_); S = lambda x: (x % p_, 0); h = (p_ + 1) // 2; eh = (0, h)
        T = [[[S(0), S(h)], [S(-h), S(0)]], [[S(0), eh], [eh, S(0)]], [[eh, S(0)], [S(0), conj(eh)]], [[eh, S(0)], [S(0), eh]]]
        good = all(add(conj(A[c][r]), A[r][c]) == (0, 0) for A in T for r in range(2) for c in range(2))      # σ(T)ᵀ = −T
        cpl = (g1, g1, g1, g2); phi = (S(0), S(1))
        act = lambda A, u: [add(mul(A[r][0], u[0]), mul(A[r][1], u[1])) for r in range(2)]
        X = [[mul(S(cpl[a]), e) for e in act(T[a], phi)] for a in range(4)]
        good &= [add(x, y) for x, y in zip(act(T[2], phi), act(T[3], phi))] == [(0, 0), (0, 0)]               # T₃ + T₄ fixes the vacuum
        herm = lambda u, w: add(mul(conj(u[0]), w[0]), mul(conj(u[1]), w[1]))
        Q2 = [[add(herm(X[a], X[b]), herm(X[b], X[a])) for b in range(4)] for a in range(4)]                  # twice the form
        tr2 = lambda A, C: add(add(mul(A[0][0], C[0][0]), mul(A[0][1], C[1][0])), add(mul(A[1][0], C[0][1]), mul(A[1][1], C[1][1])))
        Bk = [[mul(S(-2), tr2(T[a], T[b])) for b in range(4)] for a in range(4)]
        good &= all(e[1] == 0 for row in Q2 + Bk for e in row)                                                # both forms are on the shell
        Q = [[e[0] * h % p_ for e in row] for row in Q2]; B = [[e[0] for e in row] for row in Bk]
        good &= B == [[(1, (-nu) % p_, (-nu) % p_, (-nu) % p_)[a] if a == b else 0 for b in range(4)] for a in range(4)]
        inv = lambda x: pow(x, p_ - 2, p_); M = [[inv(B[a][a]) * Q[a][b] % p_ for b in range(4)] for a in range(4)]
        mw = g1 * g1 * inv(4) % p_; mz = (g1 * g1 + g2 * g2) * inv(4) % p_
        good &= M == [[mw, 0, 0, 0], [0, mw, 0, 0], [0, 0, mw, -g1 * g2 * inv(4) % p_], [0, 0, -g1 * g2 * inv(4) % p_, g2 * g2 * inv(4) % p_]]
        app = lambda w: [sum(M[a][b] * w[b] for b in range(4)) % p_ for a in range(4)]
        eig = lambda w, lam: app(w) == [lam * x % p_ for x in w]
        good &= eig((1, 0, 0, 0), mw) and eig((0, 1, 0, 0), mw) and eig((0, 0, g2, g1), 0) and eig((0, 0, g1, (-g2) % p_), mz)
        return good, mw, mz, M
    ok = True; det = []
    for p_ in (13, 173, 1549):
        nons = [n for n in range(2, p_) if pow(n, (p_ - 1) // 2, p_) == p_ - 1]; nons = nons if p_ == 13 else nons[:7]
        im = pow(prim_roots(p_)[0], p_ - 1 - (p_ - 1) // 4, p_); ok &= im * im % p_ == p_ - 1
        for nu in nons:
            for g1, g2 in ((1, 2), (3, 5), (2, 9)):
                good, mw, mz, M = mass_form(p_, nu, g1, g2)
                indep = (g2 * (-g2) - g1 * g1) % p_                                                           # det of (g', g), (g, −g')
                ok &= good and mw != 0 and mz != 0 and indep == (-(g1 * g1 + g2 * g2)) % p_ != 0 and mw * (g1 * g1 + g2 * g2) % p_ == mz * g1 * g1 % p_
            for sg in (1, -1):                                                                                # g' = ±i g: g² + g'² = 0
                good, mw, mz, M = mass_form(p_, nu, 1, sg * im % p_)
                N = [[M[2][2], M[2][3]], [M[3][2], M[3][3]]]
                ok &= good and mz == 0 and N != [[0, 0], [0, 0]] and all(sum(N[r][k] * N[k][c] for k in range(2)) % p_ == 0 for r in range(2) for c in range(2))
        r35 = 3 * pow(5, p_ - 2, p_) % p_; roots = [x for x in range(p_) if x * x % p_ == r35]                # g'² = (3/5) g²
        ok &= (pow(15, (p_ - 1) // 2, p_) == 1) == bool(roots) == (p_ != 13)
        for x in roots:
            good, mw, mz, M = mass_form(p_, nons[0], 1, x); ok &= good and 8 * mw % p_ == 5 * mz % p_
        det.append(f"F_{p_}: {len(nons)} nonsquares, g'/g = {roots if roots else 'none'}")
    # 27:C5 (p27017), 27:X5 (p27028)
    R.check("C6", "the mass form of the doublet on K = F_p[η] with the Frobenius as conjugation, at the unit vacuum: Q and the "
            "invariant form B = diag(1, −ν, −ν, −ν) are on the shell; B⁻¹Q has the photon (0, 0, g', g) as kernel, g²/4 twice "
            "and (g² + g'²)/4, the four eigenvectors of determinant −(g² + g'²); on 13, 173, 1549 at three couplings and six or "
            "seven nonsquares ν; at g' = ±i g the neutral block squares to zero; at g'² = (3/5)g² the ratio is 5/8, with g' on "
            "173 and 1549 and not on 13", ok, "; ".join(det))

    # C7 the cancellation of a boost over its cycle: Σ_τ ζ_N^0 = N and Σ_τ ζ_N^{2τ} = 0 in Q(ζ_N), N = q + 1, for
    #    the Subjects q = 13, 173, 1549. The average (1/N) Σ_τ diag(1, ζ^{2τ}) = diag(1, 0) is idempotent.
    ok = True
    for q in (13, 173, 1549):
        N = q + 1; left = I.char_sum(N, 0)
        ok &= left[0] == N and not any(left[1:]) and I.cyclo_zero(I.char_sum(N, 2), N)
    for q in (13, 173, 1549):
        N = q + 1
        PL = (Q(I.char_sum(N, 0)[0], N), Q(0) if I.cyclo_zero(I.char_sum(N, 2), N) else None)
        ok &= PL == (1, 0) and (PL[0] * PL[0], PL[1] * PL[1]) == PL
    R.check("C7", "the cancellation of a boost over its cycle: Σζ⁰ = N and Σζ_N^{2τ} = 0 exactly on the boost cycles of the Subjects 13, 173, 1549; the "
            "average of diag(1, ζ^{2τ}) over the cycle is diag(1, 0), idempotent", ok)

    # C8 the four-fermion amplitude: G_F/√2 = g²/(8M_W²) = 1/(2v²) with M_W² = g²v²/4, so G_F = 1/(√2 v²), a polynomial
    #    identity in g and v
    names = ("g", "v"); gg, v = (I.Poly.var(names, x) for x in names)
    MW2 = gg * gg * v * v * Q(1, 4)
    sym = 8 * MW2 == 2 * v * v * gg * gg                                          # g²/(8 M_W²) = 1/(2 v²)
    R.check("C8", "the four-fermion amplitude: G_F/√2 = g²/(8M_W²) = 1/(2v²) from M_W² = g²v²/4, so G_F = 1/(√2 v²), as a "
            "polynomial identity in g and v", sym, f"8 M_W² = {8 * MW2}")

    # C8c [chart] the reading at v = 246.21965 GeV meets the measured G_F within 0.01 %, compared squared as 2(G_F v²)²
    #     against 1
    d = CF.DATA["weak_current"]; x2 = 2 * (d["G_F"] * d["v"] ** 2) ** 2
    num = (1 - Q(1, 10 ** 4)) ** 2 < x2 < (1 + Q(1, 10 ** 4)) ** 2
    R.check("C8c", "[chart] 1/(√2 v²) at v = 246.22 GeV agrees with the measured G_F within 0.01 %, compared squared as "
            "2(G_F v²)² against 1", num, f"√2 G_F v² = √{CH.show(x2, '.8f')}", kind="CHART")

    # C9 the Frobenius inverts the boost cycle, exact in Z/(q + 1); a boost's sum over the cycle; the drive's image on
    #    the cycle is the half-turn δ = N/2, whose sum is N, and no element of the cycle squares to −1 on a Subject
    ok = True
    for q in (13, 173, 1549):
        N = q + 1
        ok &= all(q * a % N == (-a) % N for a in range(N))                       # Frobenius z -> z^q is inversion
    for q, dl in ((13, 1), (13, 7), (173, 1), (173, 87), (1549, 1), (1549, 775)):
        N = q + 1
        DS = [((-a) % N + dl) % N for a in range(N)]; SD = [(-((a + dl) % N)) % N for a in range(N)]
        ok &= (DS == SD) == ((2 * dl) % N == 0)
    for q in (13, 173, 1549):
        N = q + 1; dl = next(x for x in range(1, N) if gcd(x, N) == 1)
        right = N if (2 * dl) % N == 0 else 0
        ok &= right == 0 and I.cyclo_zero(I.char_sum(N, 2 * dl), N)
    for p_ in (13, 173, 1549):
        N = p_ + 1; half = N // 2
        ok &= N % 2 == 0 and (2 * half) % N == 0 and N % 4 == 2                # the half-turn's sum is N; no element of order 4
    R.check("C9", "Frobenius inverts the boost cycle C_{p+1} of the Subjects 13, 173, 1549; a boost commutes with it iff 2δ ≡ 0 (mod N); "
            "over its cycle a boost of a generator step sums to 0; the drive's image is the half-turn δ = N/2, whose sum is "
            "N, and p + 1 ≡ 2 (mod 4)", ok)

    # C10 handedness is relational: the two orientation conventions disagree on the label (the relabelling theorem
    #     orientation_flip): on a boost's cycle the branch of exponent 0 sums to N, the branch of exponent 2εδ, ε = ±1
    #     the orientation convention, sums to 0 for either
    #     sign (the inverse exponent 2(N − δ) as well as 2δ); the convention names the aligned branch L (ε = +1) or R (ε = −1).
    ok = True; labels = {}
    for q in (13, 173, 1549):
        N = q + 1; dl = next(x for x in range(1, N) if gcd(x, N) == 1)
        for eps in (1, -1):
            counter = (2 * eps * dl) % N                                              # the counter-aligned branch's exponent
            aligned = I.char_sum(N, 0)
            ok &= aligned[0] == N and not any(aligned[1:]) and counter != 0 and I.cyclo_zero(I.char_sum(N, counter), N)
            labels[(q, eps)] = "L" if eps > 0 else "R"
        ok &= labels[(q, 1)] != labels[(q, -1)]
    R.check("C10", "handedness is relational: the conventions ε = ±1 disagree on the absolute label (L against R); on a "
            "boost's cycle the branch of exponent 0 sums to N and the branch of exponent 2εδ sums to 0 for either sign "
            "(on the boost cycles of the Subjects 13, 173, 1549)", ok)

    # C11 chirality is the root of the drive (16 November 2026). K = F_p[η], η² = g, an element a pair (x, y) = x + yη. The
    #     four matrices are over the shell: γ⁰ = e₀⊗1, γ¹ = e₁⊗1, γ² = ω⊗a₂, γ³ = ω⊗b₂ with e₀ = [[0,−g],[1,0]],
    #     e₁ = diag(1,−1), ω = e₀e₁, a₂ = [[0,1],[g⁻¹,0]], b₂ = i a₂ e₁. They have the Clifford relations of
    #     diag(−g, 1, 1, 1); Γ = γ⁰γ¹γ²γ³ is over the shell, with Γ² = −g and (i⁻¹Γ)² = g; −g is a nonsquare, so Γ has no
    #     eigenvalue on the shell and a + bΓ is idempotent only for (a, b) = (0, 0), (1, 0); over K the idempotents
    #     (1 ± (iη)⁻¹Γ)/2 have trace 2, are not over the shell, and are exchanged by the Frobenius on the entries; η^p = −η.
    #     On 13, 173, 1549 with the least primitive root (the idempotents by enumeration of all pairs), and on every frame
    #     of the three Subjects (every primitive root as the drive's multiplier). The matrices η b⊗c, a⊗1, b⊗a, b⊗b are not over the shell: on 13 their
    #     idempotent has every entry on the shell.
    def roots_of_drive(p_, g_, enum=False):
        add = lambda u, v: ((u[0] + v[0]) % p_, (u[1] + v[1]) % p_)
        mul = lambda u, v: ((u[0] * v[0] + g_ * u[1] * v[1]) % p_, (u[0] * v[1] + u[1] * v[0]) % p_)
        Z, O, E = (0, 0), (1, 0), (0, 1)
        def mm(A, B):
            out = []
            for i_ in range(len(A)):
                row = []
                for j_ in range(len(A)):
                    acc = Z
                    for k_ in range(len(A)): acc = add(acc, mul(A[i_][k_], B[k_][j_]))
                    row.append(acc)
                out.append(row)
            return out
        kron = lambda A, B: [[mul(A[i_ // 2][j_ // 2], B[i_ % 2][j_ % 2]) for j_ in range(4)] for i_ in range(4)]
        sc = lambda c_, A: [[mul(c_, x) for x in row] for row in A]
        emb = lambda M: [[(x % p_, 0) for x in row] for row in M]
        a, b_ = emb([[0, 1], [1, 0]]), emb([[1, 0], [0, -1]]); c = mm(a, b_); I2 = emb([[1, 0], [0, 1]]); I4 = kron(I2, I2)
        kap = (p_ - 1) // 4; im = pow(g_, p_ - 1 - kap, p_)                      # i = g^{−κ}
        e0, e1 = emb([[0, -g_], [1, 0]]), b_; om = mm(e0, e1); a2 = emb([[0, 1], [pow(g_, p_ - 2, p_), 0]]); b2 = sc((im, 0), mm(a2, e1))
        G = [kron(e0, I2), kron(e1, I2), kron(om, a2), kron(om, b2)]
        Gold = [sc(E, kron(b_, c)), kron(a, I2), kron(b_, a), kron(b_, b_)]       # γ⁰ carries η: not over the shell
        sq = [(-g_) % p_, 1, 1, 1]
        anti = lambda A, B: all(add(x, y) == Z for r1, r2 in zip(mm(A, B), mm(B, A)) for x, y in zip(r1, r2))
        good = all(mm(G[m], G[m]) == sc((sq[m], 0), I4) for m in range(4))
        good &= all(anti(G[m], G[k_]) for m in range(4) for k_ in range(m + 1, 4))
        Gam = mm(mm(G[0], G[1]), mm(G[2], G[3]))
        good &= all(x[1] == 0 for M_ in G + [Gam] for row in M_ for x in row)      # the four matrices and Γ are over the shell
        good &= im * im % p_ == p_ - 1 and mm(Gam, Gam) == sc(((-g_) % p_, 0), I4)
        iG = sc((pow(im, p_ - 2, p_), 0), Gam)
        good &= mm(iG, iG) == sc((g_, 0), I4) and all(anti(Gam, G[m]) for m in range(4))
        good &= pow((-g_) % p_, (p_ - 1) // 2, p_) == p_ - 1                       # −g is a nonsquare: no eigenvalue on the shell
        ie = (0, im); inv_ie = mul(ie, (pow((-g_) % p_, p_ - 2, p_), 0))          # (iη)⁻¹ = iη/(−g)
        good &= mul(ie, ie) == ((-g_) % p_, 0) and mul(ie, inv_ie) == O
        half = ((p_ + 1) // 2, 0); proj = []
        for sign in (1, p_ - 1):
            P = [[mul(half, add(I4[r][s_], mul((sign, 0), mul(inv_ie, Gam[r][s_])))) for s_ in range(4)] for r in range(4)]
            tr = Z
            for r in range(4): tr = add(tr, P[r][r])
            good &= mm(P, P) == P and tr == (2, 0); proj.append(P)
        frob = lambda M_: [[(x[0], (-x[1]) % p_) for x in row] for row in M_]
        good &= frob(proj[0]) == proj[1] and any(x[1] for row in proj[0] for x in row)   # σ exchanges the two; neither is over the shell
        good &= pow((-pow(4 * g_, p_ - 2, p_)) % p_, (p_ - 1) // 2, p_) == p_ - 1        # −1/(4g) is a nonsquare: no b ≠ 0 with g b² = −1/4
        if enum:                                                                 # every pair: a² − g b² = a and 2ab = b only at (0, 0), (1, 0)
            good &= [(a_, b3) for a_ in range(p_) for b3 in range(p_) if (a_ * a_ - g_ * b3 * b3 - a_) % p_ == 0 and (2 * a_ * b3 - b3) % p_ == 0] == [(0, 0), (1, 0)]
        if p_ == 13:                                                             # the matrices that carry η: the idempotent is on the shell
            Go = mm(mm(Gold[0], Gold[1]), mm(Gold[2], Gold[3]))
            Po = [[mul(half, add(I4[r][s_], mul(inv_ie, Go[r][s_]))) for s_ in range(4)] for r in range(4)]
            good &= mm(Po, Po) == Po and all(x[1] == 0 for row in Po for x in row) and any(x[1] for row in Go for x in row)
        x = O
        for _ in range(p_): x = mul(x, E)
        good &= x == (0, p_ - 1)                                                 # η^p = −η: the Frobenius negates η
        return good
    ok = all(roots_of_drive(p_, prim_roots(p_)[0], enum=True) for p_ in (13, 173, 1549))
    frames = [(p_, g_) for p_ in (13, 173, 1549) for g_ in prim_roots(p_)]
    ok &= len(frames) == 4 + 84 + 504 and all(roots_of_drive(p_, g_) for p_, g_ in frames)
    # 27:C13 (p27051), 27:X6 (p27029)
    R.check("C11", "chirality is the root of the drive: four matrices over the shell with the Clifford relations of "
            "diag(−g, 1, 1, 1); Γ = γ⁰γ¹γ²γ³ has Γ² = −g and (i⁻¹Γ)² = g; −g is a nonsquare, so Γ has no eigenvalue on the "
            "shell and F_p[Γ] has the idempotents 0 and 1 only; over K the idempotents (1 ± (iη)⁻¹Γ)/2 have trace 2 and the "
            "Frobenius exchanges them; η^p = −η; on 13, 173, 1549 with every primitive root as the drive's multiplier", ok, f"{len(frames)} frames")

    # C12 the two branches along the drive (16 November 2026). D = diag(η, η⁻¹) is the drive's unimodular lift: σ(D) = −D,
    #     D² = diag(g, g⁻¹) is over the shell with determinant 1. For A over the shell σ(A) = A, and σ(DA) = −DA: on the
    #     group that SL₂(F_p) and D generate, σ(A) = χ(A)A with χ the parity of the count of D. A sesquilinear tally
    #     h(v, w) = Σ σ(v_k) w_k is equal on A and σ(A). 300 products of the generators on each of 13, 173 and 1549.
    def branches(p_, g_, mats):
        add = lambda u, v: ((u[0] + v[0]) % p_, (u[1] + v[1]) % p_)
        mul = lambda u, v: ((u[0] * v[0] + g_ * u[1] * v[1]) % p_, (u[0] * v[1] + u[1] * v[0]) % p_)
        neg = lambda u: ((-u[0]) % p_, (-u[1]) % p_); sig = lambda u: (u[0], (-u[1]) % p_)
        mm = lambda A, B: [[add(mul(A[i_][0], B[0][j_]), mul(A[i_][1], B[1][j_])) for j_ in range(2)] for i_ in range(2)]
        smat = lambda A: [[sig(x) for x in row] for row in A]; nmat = lambda A: [[neg(x) for x in row] for row in A]
        ginv = pow(g_, p_ - 2, p_)
        D = [[(0, 1), (0, 0)], [(0, 0), (0, ginv)]]                              # η and η⁻¹ = η/g
        good = smat(D) == nmat(D) and mm(D, D) == [[(g_, 0), (0, 0)], [(0, 0), (ginv, 0)]]
        act = lambda A, v: [add(mul(A[0][0], v[0]), mul(A[0][1], v[1])), add(mul(A[1][0], v[0]), mul(A[1][1], v[1]))]
        h = lambda v, w: add(mul(sig(v[0]), w[0]), mul(sig(v[1]), w[1]))
        v, w = [(1, 2), (3, 5)], [(7, 1), (2, 11)]
        for M in mats:
            A = [[(M[0] % p_, 0), (M[1] % p_, 0)], [(M[2] % p_, 0), (M[3] % p_, 0)]]
            DA = mm(D, A); DAD = mm(DA, D)
            good &= smat(A) == A and smat(DA) == nmat(DA) and smat(DAD) == DAD
            good &= h(act(smat(DA), v), act(smat(DA), w)) == h(act(DA, v), act(DA, w))
        return good
    ok = True
    for p_ in (13, 173, 1549):
        rng = random.Random(p_); M = (1, 0, 0, 1); mats = []
        for _ in range(300):
            t = rng.choice(((1, 1, 0, 1), (0, p_ - 1, 1, 0), (1, 0, 1, 1)))
            M = ((M[0] * t[0] + M[1] * t[2]) % p_, (M[0] * t[1] + M[1] * t[3]) % p_,
                 (M[2] * t[0] + M[3] * t[2]) % p_, (M[2] * t[1] + M[3] * t[3]) % p_)
            mats.append(M)
        ok &= all((m[0] * m[3] - m[1] * m[2]) % p_ == 1 for m in mats) and branches(p_, prim_roots(p_)[0], mats)
    # 27:C14 (p27052)
    R.check("C12", "the two branches along the drive: the lift D = diag(η, η⁻¹) has σ(D) = −D and D² over the shell; σ(A) = A "
            "on SL₂(F_p), σ(DA) = −DA and σ(DAD) = DAD, so σ(A) = χ(A)A with χ the parity of the chronon count; a "
            "sesquilinear tally is equal on A and σ(A); 300 products of the generators on each of 13, 173 and 1549", ok)

    # C13 the diagonal torus over K = F_p[η] and its two cycles (17 November 2026), on 13, 173, 1549. An element of K is a
    #     pair (x, y) = x + yη, η² = g, σ(η) = −η. The drive is δ = diag(g, g⁻¹) in the basis of the vacuum (0, 1). A matrix
    #     over K commutes with δ exactly when it is diagonal. The points of the torus diag(x, x⁻¹) over the shell are the
    #     split cycle, of p − 1 points; its unitary points diag(w, σ(w)), σ(w)w = 1, are a cycle of p + 1 points; they meet
    #     in ±1. A unitary point keeps the Hermitian form, and the pair (diag(w, σ(w)), w) acts as diag(w², 1) and fixes the
    #     vacuum. E and F have the weights ±2: g^{±2} on the drive, w^{±2} on the unitary cycle; every point fixes the
    #     massless generator η diag(1, 0). The drive is no unitary point: δ†δ = diag(g², g⁻²), and Ad_δ T₁ is not
    #     anti-Hermitian. The integers below (p − 1)/2 in absolute value are distinguished on both cycles. The loops run over
    #     K, a set of p² < Ω elements, and over 400 sampled matrices.
    ok = True; det = []
    for p_ in (13, 173, 1549):
        g_ = arith.primitive_root(p_); h_ = pow(g_, p_ - 2, p_); i2 = pow(2, p_ - 2, p_)
        add = lambda u, v, p_=p_: ((u[0] + v[0]) % p_, (u[1] + v[1]) % p_)
        mul = lambda u, v, p_=p_, g_=g_: ((u[0] * v[0] + g_ * u[1] * v[1]) % p_, (u[0] * v[1] + u[1] * v[0]) % p_)
        sig = lambda u, p_=p_: (u[0], (-u[1]) % p_); neg = lambda u, p_=p_: ((-u[0]) % p_, (-u[1]) % p_)
        Z0, O1, ETA = (0, 0), (1, 0), (0, 1); sc = lambda a, p_=p_: (a % p_, 0)
        mm = lambda A, B: tuple(tuple(add(mul(A[i][0], B[0][j]), mul(A[i][1], B[1][j])) for j in range(2)) for i in range(2))
        dag = lambda A: tuple(tuple(sig(A[j][i]) for j in range(2)) for i in range(2)); I2 = ((O1, Z0), (Z0, O1))
        dia = lambda x, y: ((x, Z0), (Z0, y))
        N1 = [(x, y) for x in range(p_) for y in range(p_) if (x * x - g_ * y * y) % p_ == 1]      # σ(w)w = 1
        D, Di = dia(sc(g_), sc(h_)), dia(sc(h_), sc(g_)); E_, F_ = ((Z0, O1), (Z0, Z0)), ((Z0, Z0), (O1, Z0))
        ok &= len(N1) == p_ + 1 and sorted(w[0] for w in N1 if w[1] == 0) == [1, p_ - 1]
        rng = random.Random(1000 + p_); rk = lambda: (rng.randrange(p_), rng.randrange(p_))
        for _ in range(400):
            X = ((rk(), rk() if rng.randrange(10) < 7 else Z0), (rk() if rng.randrange(10) < 7 else Z0, rk()))
            ok &= (mm(X, D) == mm(D, X)) == (X[0][1] == Z0 and X[1][0] == Z0)
        P = dia(ETA, Z0)                                                         # T₃ + T₄ = η diag(1, 0)
        ok &= mm(mm(D, E_), Di) == ((Z0, sc(g_ * g_)), (Z0, Z0)) and mm(mm(D, F_), Di) == ((Z0, Z0), (sc(h_ * h_), Z0))
        ok &= mm(mm(D, P), Di) == P and mm(dag(D), D) == dia(sc(g_ * g_), sc(h_ * h_)) != I2
        T1 = ((Z0, sc(i2)), (sc(-i2), Z0)); A1_ = mm(mm(D, T1), Di)
        ok &= dag(T1) == tuple(tuple(neg(x) for x in r) for r in T1) and dag(A1_) != tuple(tuple(neg(x) for x in r) for r in A1_)
        for w in N1[:: max(1, len(N1) // 60)]:
            U = dia(w, sig(w)); Ui = dia(sig(w), w); w2 = mul(w, w)
            ok &= mm(dag(U), U) == I2 and mul(w, sig(w)) == O1
            ok &= mm(mm(U, E_), Ui) == ((Z0, w2), (Z0, Z0)) and mm(mm(U, F_), Ui) == ((Z0, Z0), (mul(sig(w), sig(w)), Z0))
            ok &= mm(mm(U, P), Ui) == P and (mul(w, mul(w, Z0)), mul(w, mul(sig(w), O1))) == (Z0, O1)
            ok &= dia(mul(w, w), mul(w, sig(w))) == dia(w2, O1)
        fs = [f for f in range(2, p_ + 2) if (p_ + 1) % f == 0 and all(f % d_ for d_ in range(2, isqrt(f) + 1))]
        def kpow(u, e):
            r = O1
            while e:
                if e & 1: r = mul(r, u)
                u = mul(u, u); e >>= 1
            return r
        w0 = next(w for w in N1 if all(kpow(w, (p_ + 1) // f) != O1 for f in fs))     # a generator of the unitary cycle
        m_ = (p_ - 1) // 2; rng_n = range(-m_ + 1, m_)
        ok &= len({kpow(w0, n_ % (p_ + 1)) for n_ in rng_n}) == len(rng_n) == len({pow(g_, n_ % (p_ - 1), p_) for n_ in rng_n})
        det.append(f"F_{p_}: split cycle {p_ - 1}, unitary cycle {len(N1)}, δ†δ = diag({g_ * g_ % p_}, {h_ * h_ % p_})")
    # 27:C15 (p27057)
    R.check("C13", "the diagonal torus over K and its two cycles on the Subjects 13, 173, 1549: a matrix over K commutes with "
            "the transport of two chronons exactly when it is diagonal (400 sampled matrices each); the split cycle has p − 1 points and the unitary "
            "cycle p + 1, and they meet in ±1; a unitary point keeps the Hermitian form, and the pair (diag(w, σ(w)), w) fixes "
            "the vacuum; E and F have the weights ±2, read as g^{±2} on the transport of two chronons and as w^{±2} on the unitary cycle, and every "
            "point fixes the massless generator; the transport of two chronons is no unitary point; the integers below (p − 1)/2 in absolute value "
            "are distinguished on both cycles", ok, "; ".join(det))

    # C14 the units of K, the two readings of a weight, and the split cycles of the doublet's frame, on the Subjects 13,
    #     173, 1549 (the review of 17 November 2026, second report). A unit x = a + bη of K has the norm N = a² − g b², a
    #     split point, and the quotient x/σ(x) = x²/N, a unitary point, with x² = N · x/σ(x); the quotient is 1 exactly when
    #     b = 0, and the quotients are all the p + 1 unitary points. A weight n reads n mod p − 1 and n mod p + 1: the pairs
    #     of readings are the pairs of equal parity, each from two weights below p² − 1, with the two lifts of the text below
    #     p² − 1; the inverse power x⁻ᵏ, 0 < k < p − 1, is the weight p² − 1 − k, which reads p − 1 − k and p + 1 − k; the
    #     Frobenius fixes a split point and inverts a unitary point; the weights −4 … 6 are distinct on both cycles. The rotations
    #     R(a), a ≠ 0, have entries of the shell, c² + s² = 1, the eigenvectors (1, ±i) with a and a⁻¹, R(a)R(b) = R(ab);
    #     R(g) keeps the Hermitian form and moves the generator η diag(1, 0) of the photon, which the drive fixes. The loops
    #     run over K on 13 and 173 and over 4000 sampled units on 1549, and over the residues and the weights below p² − 1.
    ok = True; det = []
    for p_ in (13, 173, 1549):
        g_ = arith.primitive_root(p_); inv = lambda a, p_=p_: pow(a, p_ - 2, p_)
        mul = lambda u, v, p_=p_, g_=g_: ((u[0] * v[0] + g_ * u[1] * v[1]) % p_, (u[0] * v[1] + u[1] * v[0]) % p_)
        sig = lambda u, p_=p_: (u[0], (-u[1]) % p_)
        def quotient(x, p_=p_, g_=g_, mul=mul, inv=inv):
            n_ = (x[0] * x[0] - g_ * x[1] * x[1]) % p_
            x2 = mul(x, x); k_ = inv(n_)
            return n_, (x2[0] * k_ % p_, x2[1] * k_ % p_)
        rng = random.Random(900 + p_)
        units = [(a, b) for a in range(p_) for b in range(p_) if (a, b) != (0, 0)] if p_ < 200 else \
            [(rng.randrange(1, p_), rng.randrange(p_)) for _ in range(3000)] + [(rng.randrange(p_), rng.randrange(1, p_)) for _ in range(1000)]
        for x in units:
            n_, u = quotient(x)
            ok &= n_ != 0 and mul(sig(u), u) == (1, 0) and mul(x, x) == mul((n_, 0), u) and mul(sig(x), x) == (n_, 0)
            ok &= (u == (1, 0)) == (x[1] == 0)
        N1 = {(x, y) for x in range(p_) for y in range(p_) if (x * x - g_ * y * y) % p_ == 1}
        ok &= {quotient((1, s_))[1] for s_ in range(p_)} | {quotient((0, 1))[1]} == N1 and quotient((0, 1))[1] == (p_ - 1, 0)
        for w in list(N1)[:: max(1, len(N1) // 60)]:                             # the Frobenius inverts a unitary point
            ok &= mul(sig(w), w) == (1, 0) and mul(mul(sig(w), sig(w)), mul(w, w)) == (1, 0)
        ok &= all(sig((a, 0)) == (a, 0) for a in range(1, p_))                     # and fixes a split point
        pairs = Counter((n_ % (p_ - 1), n_ % (p_ + 1)) for n_ in range(p_ * p_ - 1))
        ok &= len(pairs) == (p_ * p_ - 1) // 2 and set(pairs.values()) == {2} and all((a - b) % 2 == 0 for a, b in pairs)
        ok &= len({v % (p_ - 1) for v in range(-4, 7)}) == 11 == len({v % (p_ + 1) for v in range(-4, 7)})   # the weights −4 … 6
        def kpow(x, e, mul=mul):
            r_ = (1, 0)
            while e:
                if e & 1: r_ = mul(r_, x)
                x = mul(x, x); e >>= 1
            return r_
        ok &= all((p_ * p_ - 1 - k) % (p_ - 1) == p_ - 1 - k and (p_ * p_ - 1 - k) % (p_ + 1) == p_ + 1 - k for k in range(1, p_ - 1))
        for x in units[:: max(1, len(units) // 40)]:                              # the inverse power x⁻ᵏ is the weight p² − 1 − k
            k = rng.randrange(1, p_ - 1); ok &= mul(kpow(x, p_ * p_ - 1 - k), kpow(x, k)) == (1, 0)
        m_ = (p_ - 1) // 2
        for _ in range(2000):
            b_ = rng.randrange(p_ + 1); a_ = rng.randrange(b_ % 2, p_ - 1, 2)
            n_ = a_ + (p_ - 1) * ((a_ - b_) // 2) if a_ >= b_ else a_ + (p_ - 1) * (m_ - (b_ - a_) // 2 + 1)
            ok &= n_ % (p_ - 1) == a_ and n_ % (p_ + 1) == b_ and n_ < p_ * p_ - 1
        i_ = pow(g_, (p_ - 1) - (p_ - 1) // 4, p_); i2 = inv(2)                        # i = g^(−κ), i² = −1
        rot = {}
        for a in range(1, p_):
            c_, s_ = (a + inv(a)) * i2 % p_, i_ * ((inv(a) - a) % p_) % p_ * i2 % p_
            rot[a] = (c_, s_)
            ok &= (c_ * c_ + s_ * s_) % p_ == 1 and (c_ + i_ * s_) % p_ == a and (c_ - i_ * s_) % p_ == inv(a)
            ok &= (-s_ + c_ * i_) % p_ == a * i_ % p_ and (-s_ - c_ * i_) % p_ == (-inv(a) * i_) % p_
        ok &= i_ * i_ % p_ == p_ - 1 and len(set(rot.values())) == p_ - 1
        for _ in range(2000):
            a, b = rng.randrange(1, p_), rng.randrange(1, p_); (ca, sa), (cb, sb) = rot[a], rot[b]
            ok &= ((ca * cb - sa * sb) % p_, (sa * cb + ca * sb) % p_) == rot[a * b % p_]
        cg, sg = rot[g_]                                                           # R(g) P R(g)⁻¹ for P = diag(1, 0)
        ok &= ((cg * cg) % p_, (-cg * sg) % p_, (-cg * sg) % p_, (sg * sg) % p_) != (1, 0, 0, 0)
        ok &= {(c_, s_) for c_, s_ in rot.values() if s_ == 0} == {(1, 0), (p_ - 1, 0)}       # the two kinds of cycle meet in ±1
        det.append(f"F_{p_}: {len(units)} units, {len(N1)} quotients, {len(pairs)} pairs of readings, {len(rot)} rotations")
    R.check("C14", "the units of K on the Subjects 13, 173, 1549: the square of a unit is its norm times the quotient x/σ(x), "
            "the quotient is unitary and is 1 exactly on the split points, and the quotients are all the p + 1 unitary points; the "
            "readings of the weights below p² − 1 on the two cycles are the pairs of equal parity, each twice, and an inverse "
            "power x⁻ᵏ is the weight p² − 1 − k; the Frobenius "
            "fixes a split point and inverts a unitary point; the rotations R(a) have entries of the shell, c² + s² = 1, the eigenvectors (1, ±i), "
            "R(a)R(b) = R(ab), and R(g) moves the generator of the photon", ok, "; ".join(det))

    # C15 one charge system in the frame of rank five, on the Subjects 13, 173, 1549 (the review of 17 November 2026,
    #     second report). A unitary point is u^k for a generator u of the unitary cycle, so a diagonal point with unitary
    #     entries is its list of exponents mod p + 1. The hypercharge cycle (−2, −2, −2, 3, 3)k has determinant one and is
    #     faithful, and it is the scalar 3k on the doublet. The charge cycle (1, 1, 1, −3, 0)k has determinant one, fixes
    #     the vacuum, and is the identity on the doublet exactly at 3k = 0, where it is (k, k, k, 0, 0), the centre of the
    #     colour frame. On the sixteen states the weights are 6Y and −3Q, with −3Q the number of colour indices less 3 on
    #     the charged direction, so a charge is an integer exactly when the number of colour indices is a multiple of 3.
    #     The sixth powers have the index gcd(6, p + 1) and the squares the index 2; 3k = 1 has a solution exactly when
    #     the colour frame has no centre; a point of the charge cycle is a product of the hypercharge cycle with the two
    #     unitary frames exactly when it is a square. The points are also taken as elements of K and multiplied there.
    #     The centre of the stabiliser: a matrix of rank three over K that commutes with diag(u, u², u³), u a generator of
    #     the unitary cycle, and with the two permutation matrices of adjacent colour directions is a scalar; the 27 linear
    #     equations in its nine entries have rank 8 over K. The check forms three named matrices and enumerates none.
    ok = True; det = []
    Y6, Q3n = (-2, -2, -2, 3, 3), (1, 1, 1, -3, 0)
    states = [S for S in product((0, 1), repeat=5) if sum(S) % 2 == 0]
    Yh = (Q(-1, 3), Q(-1, 3), Q(-1, 3), Q(1, 2), Q(1, 2)); T3 = (0, 0, 0, Q(1, 2), Q(-1, 2))
    ok &= len(states) == 16
    for S in states:
        y_, q_ = sum(Yh[j] for j in range(5) if S[j]), sum(Yh[j] + T3[j] for j in range(5) if S[j])
        col_ = S[0] + S[1] + S[2]
        ok &= sum(Y6[j] for j in range(5) if S[j]) == 6 * y_ and sum(Q3n[j] for j in range(5) if S[j]) == -3 * q_ == col_ - 3 * S[3]
        ok &= (q_.denominator == 1) == (col_ % 3 == 0)
    ok &= sum(Y6) == 0 and sum(Q3n) == 0 and Q3n[4] == 0
    for p_ in (13, 173, 1549):
        g_ = arith.primitive_root(p_); M_ = p_ + 1
        mul = lambda u, v, p_=p_, g_=g_: ((u[0] * v[0] + g_ * u[1] * v[1]) % p_, (u[0] * v[1] + u[1] * v[0]) % p_)
        sig = lambda u, p_=p_: (u[0], (-u[1]) % p_)
        def kpow(u, e, mul=mul):
            r = (1, 0)
            while e:
                if e & 1: r = mul(r, u)
                u = mul(u, u); e >>= 1
            return r
        N1 = [(x, y) for x in range(p_) for y in range(p_) if (x * x - g_ * y * y) % p_ == 1]
        fs = [f for f in range(2, M_ + 1) if M_ % f == 0 and all(f % d_ for d_ in range(2, isqrt(f) + 1))]
        u0 = next(w for w in N1 if all(kpow(w, M_ // f) != (1, 0) for f in fs))               # a generator of the unitary cycle
        ok &= len(N1) == M_ and kpow(u0, M_) == (1, 0)
        ok &= [k for k in range(M_) if all(e * k % M_ == 0 for e in Y6)] == [0]                # the hypercharge cycle is faithful
        ker = [k for k in range(M_) if Q3n[3] * k % M_ == 0]                                  # the charge cycle on the doublet
        ok &= len(ker) == gcd(3, M_) and all(tuple(e * k % M_ for e in Q3n) == (k, k, k, 0, 0) and 3 * k % M_ == 0 for k in ker)
        ok &= M_ // len({6 * k % M_ for k in range(M_)}) == gcd(6, M_) and M_ // len({2 * k % M_ for k in range(M_)}) == 2
        ok &= M_ // len({3 * k % M_ for k in range(M_)}) == gcd(3, M_)
        ok &= any(3 * k % M_ == 1 for k in range(M_)) == (gcd(3, M_) == 1)
        sixth = {6 * k % M_ for k in range(M_)}                                             # q(u) is a product exactly at the squares
        ok &= [k for k in range(M_) if 3 * k % M_ in sixth] == list(range(0, M_, 2))
        for w in N1[:: max(1, len(N1) // 80)]:                                               # the same on the elements of K
            wi = sig(w); w2, w3 = mul(wi, wi), mul(w, mul(w, w))
            ok &= mul(w, wi) == (1, 0) and mul(mul(mul(w2, w2), w2), mul(w3, w3)) == (1, 0)
            ok &= mul(mul(w, mul(w, w)), mul(wi, mul(wi, wi))) == (1, 0)
            ok &= ((w2, w3) == ((1, 0), (1, 0))) == (w == (1, 0))
            ok &= (mul(wi, mul(wi, wi)) == (1, 0)) == (w3 == (1, 0))
        add = lambda u, v, p_=p_: ((u[0] + v[0]) % p_, (u[1] + v[1]) % p_)
        neg = lambda u, p_=p_: ((-u[0]) % p_, (-u[1]) % p_)
        def kinv(u, p_=p_, g_=g_):
            n_ = pow((u[0] * u[0] - g_ * u[1] * u[1]) % p_, p_ - 2, p_); return (u[0] * n_ % p_, (-u[1]) * n_ % p_)
        Z_, O_ = (0, 0), (1, 0); d_ = [u0, mul(u0, u0), mul(u0, mul(u0, u0))]
        ok &= len(set(d_)) == 3 and all(mul(sig(x), x) == O_ for x in d_)                    # three distinct unitary entries
        Dm = [[d_[i] if i == j else Z_ for j in range(3)] for i in range(3)]
        P12 = [[Z_, O_, Z_], [O_, Z_, Z_], [Z_, Z_, O_]]; P23 = [[O_, Z_, Z_], [Z_, Z_, O_], [Z_, O_, Z_]]
        rows = []
        for X in (Dm, P12, P23):                                                             # (A X − X A)_{ij}, linear in the nine entries of A
            for i in range(3):
                for j in range(3):
                    r_ = [Z_] * 9
                    for k in range(3):
                        r_[3 * i + k] = add(r_[3 * i + k], X[k][j]); r_[3 * k + j] = add(r_[3 * k + j], neg(X[i][k]))
                    rows.append(r_)
        rank = 0
        for c in range(9):                                                                   # elimination over K
            piv = next((r for r in range(rank, len(rows)) if rows[r][c] != Z_), None)
            if piv is None: continue
            rows[rank], rows[piv] = rows[piv], rows[rank]; iv = kinv(rows[rank][c])
            rows[rank] = [mul(iv, x) for x in rows[rank]]
            for r in range(len(rows)):
                if r != rank and rows[r][c] != Z_:
                    f_ = rows[r][c]; rows[r] = [add(x, neg(mul(f_, y))) for x, y in zip(rows[r], rows[rank])]
            rank += 1
        ok &= rank == 8                                                                      # the commutant is the scalars
        det.append(f"F_{p_}: index of the sixth powers {gcd(6, M_)}, centre of order {len(ker)}, commutant of rank {9 - rank}")
    # 27:C16 (p27058)
    R.check("C15", "one charge system in the frame of rank five on the Subjects 13, 173, 1549: the hypercharge cycle "
            "diag(w⁻², w⁻², w⁻², w³, w³) and the charge cycle diag(u, u, u, u⁻³, 1) have determinant one, the first is "
            "faithful and is the scalar w³ on the doublet, the second fixes the vacuum and is the identity on the doublet "
            "exactly at u³ = 1, the centre of the colour frame; on the sixteen states the weights are 6Y and −3Q, and a "
            "charge is an integer exactly when the number of colour indices is a multiple of 3; the sixth powers of the "
            "unitary cycle have the index gcd(6, p + 1): 2, 6 and 2, and the squares of the charge cycle are its points that are "
            "products of the hypercharge cycle with the unitary frames of the two blocks; a matrix of rank three over K that "
            "commutes with a diagonal matrix of three distinct unitary entries and with the permutation matrices is a scalar", ok, "; ".join(det))

    # C16 no fractional charge without colour, on the sixteen states, their conjugates and their pairwise products, and the
    #     kernel of the product of the hypercharge cycle with the two frames on the Subjects 13, 173, 1549 (pass 10 of 17
    #     November 2026). A vector index in a colour direction has the weights 6Y = −2 and −3Q = 1, one in the charged
    #     direction of the doublet 3 and −3, one in the neutral direction 3 and 0; a conjugate index has the opposite
    #     weights. So −3Q is congruent modulo 3 to the net number of colour indices and 6Y modulo 2 to the net number of
    #     doublet indices, on every state, and a state whose net number of colour indices is a multiple of three has an
    #     integer charge. A state that the frame moves diag(u, v, 1/(uv)) of the colour frame fix has equal net numbers of
    #     indices in the three directions while it has fewer than p + 1 indices, read here on at most four; on the Subject
    #     173 a point x ≠ 1 of the centre multiplies a state by x^n, which is one exactly when three divides n. A triple of a hypercharge point u^k and scalars of the two blocks gives the identity exactly at
    #     the scalars u^{2k} and u^{−3k}; their determinants are one exactly when 6k = 0, on gcd(6, p + 1) points: 2 on the
    #     shells p ≡ 1 (mod 12) and 6 on the shells p ≡ 5 (mod 12).
    ok = True; det = []
    Y6, Q3n = (-2, -2, -2, 3, 3), (1, 1, 1, -3, 0)
    states = [S for S in product((0, 1), repeat=5) if sum(S) % 2 == 0]
    W = []                                                                                 # (6Y, −3Q, net colour, net doublet) of a state and of its conjugate
    for S in states:
        w_ = (sum(Y6[j] for j in range(5) if S[j]), sum(Q3n[j] for j in range(5) if S[j]), S[0] + S[1] + S[2], S[3] + S[4])
        W += [w_, tuple(-x for x in w_)]
    cong = lambda w_: (w_[1] - w_[2]) % 3 == 0 and (w_[0] - w_[3]) % 2 == 0
    ok &= len(W) == 32 and all(cong(w_) for w_ in W)
    ok &= all(cong(tuple(a + b for a, b in zip(u_, v_))) for u_ in W for v_ in W)             # the products of two states
    ok &= all(Q(-(u_[1] + v_[1]), 3).denominator == 1 for u_ in W for v_ in W if (u_[2] + v_[2]) % 3 == 0)   # an integer charge without net colour
    ok &= any(Q(-w_[1], 3).denominator == 3 for w_ in W)                                    # and the quarks have thirds
    for p_ in (13, 173, 1549):
        M_ = p_ + 1; d_ = gcd(6, M_)
        ker = [k for k in range(M_) if 6 * k % M_ == 0]
        ok &= len(ker) == d_ == {1: 2, 5: 6}[p_ % 12] and ker == [r * (M_ // d_) for r in range(d_)]
        for k in range(M_):                                                                # y(u^k) times the scalars u^{2k} and u^{−3k} is the identity
            ok &= all((Y6[j] * k + (2 * k if j < 3 else -3 * k)) % M_ == 0 for j in range(5))
            ok &= ((3 * 2 * k) % M_ == 0) == (k in ker) == ((2 * -3 * k) % M_ == 0)
        idx = [t for t in product(range(5), repeat=6) if sum(t) <= 4]                      # (a1, a2, a3, b1, b2, b3): at most four indices
        fixed = [t for t in idx if (t[0] + t[5] - t[2] - t[3]) % M_ == 0 and (t[1] + t[5] - t[2] - t[4]) % M_ == 0]
        ok &= all(t[0] - t[3] == t[1] - t[4] == t[2] - t[5] for t in fixed)                # equal net numbers in the three directions
        ok &= all((sum(t[:3]) - sum(t[3:])) % 3 == 0 for t in fixed) and len(fixed) > 1
        cen = [k for k in range(1, M_) if 3 * k % M_ == 0]                                 # the points x ≠ 1 of the centre, x = u^k
        ok &= (len(cen) == 2) == (p_ % 12 == 5) and len(cen) in (0, 2)
        ok &= all(((k * n_) % M_ == 0) == (n_ % 3 == 0) for k in cen for n_ in range(M_))
        det.append(f"F_{p_}: p mod 12 = {p_ % 12}, kernel of order {len(ker)}, {len(fixed)} fixed index sets of at most four, centre of order {len(cen) + 1}")
    # 27:P10 (p27059)
    R.check("C16", "no fractional charge without colour: on the sixteen states, their conjugates and their pairwise products "
            "−3Q is congruent modulo 3 to the net number of colour indices and 6Y modulo 2 to the net number of doublet indices, "
            "so a state whose net number of colour indices is a multiple of three has an integer charge; a state of at most four "
            "indices that the diagonal frame moves of the colour frame fix has equal net numbers of indices in the three "
            "directions, and a point of the centre fixes a state exactly when three divides its net number; the kernel of the "
            "product of the hypercharge cycle with the two frames on the Subjects 13, 173, 1549 has gcd(6, p + 1) points, 2 on "
            "the shells p ≡ 1 (mod 12) and 6 on the shells p ≡ 5 (mod 12)", ok, "; ".join(det))

    # C17 the Frobenius parity of a tally (pass 11 of 17 November 2026), on 13, 173, 1549, in K = F_p[η], η² = g, an element a
    #     pair (x, y) = x + yη. Frame moves of determinant one come from the Cayley transform of an anti-Hermitian matrix, by
    #     fixed seeds; no set of frame moves is formed. For a frame move U the difference O(U) = tr U − tr U⁻¹ lies in ηF_p.
    #     The density T₁ = Σ ε tr(F_μν F_ρσ), F = U − U†, on the six plaquettes of a cell lies in the shell, and λ⁻¹T₁, with
    #     λ = iη the eigenvalue of Γ on the occupied root (λ² = −g), lies in ηF_p and does not change with Γ → −Γ, λ → −λ.
    #     For Hermitian A_u, A_d the determinant J of the commutator of A_u² and A_d² lies in ηF_p, is invariant under a
    #     generation-frame move, and is 0 when the two commute. The products J·O(U) and J·λ⁻¹T₁ lie in the shell, and the
    #     Frobenius on all the data fixes them.
    def parity(p_, g_):
        P = lambda x, y=0: (x % p_, y % p_)
        ad = lambda x, y: ((x[0] + y[0]) % p_, (x[1] + y[1]) % p_)
        ng = lambda x: (-x[0] % p_, -x[1] % p_)
        ml = lambda x, y: ((x[0] * y[0] + g_ * x[1] * y[1]) % p_, (x[0] * y[1] + x[1] * y[0]) % p_)
        cj = lambda x: (x[0], -x[1] % p_)
        def iv(x):
            n_ = pow((x[0] * x[0] - g_ * x[1] * x[1]) % p_, p_ - 2, p_); return (x[0] * n_ % p_, -x[1] * n_ % p_)
        Z, I1 = P(0), P(1)
        def sm(xs):
            t = Z
            for x in xs: t = ad(t, x)
            return t
        m3 = lambda A, B: tuple(tuple(sm(ml(A[i][k], B[k][j]) for k in range(3)) for j in range(3)) for i in range(3))
        a3 = lambda A, B, s=1: tuple(tuple(ad(A[i][j], B[i][j] if s == 1 else ng(B[i][j])) for j in range(3)) for i in range(3))
        dg = lambda A: tuple(tuple(cj(A[j][i]) for j in range(3)) for i in range(3))
        fb = lambda A: tuple(tuple(cj(x) for x in r) for r in A)
        e3 = tuple(tuple(P(int(i == j)) for j in range(3)) for i in range(3))
        t3 = lambda A: sm(A[i][i] for i in range(3))
        def d3(A):
            c = lambda i, j, k, l: ad(ml(A[1][i], A[2][j]), ng(ml(A[1][k], A[2][l])))
            return sm((ml(A[0][0], c(1, 2, 2, 1)), ng(ml(A[0][1], c(0, 2, 2, 0))), ml(A[0][2], c(0, 1, 1, 0))))
        def i3(A):
            d = iv(d3(A)); c = lambda i, j: ad(ml(A[(j + 1) % 3][(i + 1) % 3], A[(j + 2) % 3][(i + 2) % 3]),
                                              ng(ml(A[(j + 1) % 3][(i + 2) % 3], A[(j + 2) % 3][(i + 1) % 3])))
            return tuple(tuple(ml(c(i, j), d) for j in range(3)) for i in range(3))
        rng = random.Random(27000 + p_)
        def herm():
            A = [[Z] * 3 for _ in range(3)]
            for i in range(3):
                A[i][i] = P(rng.randrange(p_))
                for j in range(i + 1, 3):
                    A[i][j] = P(rng.randrange(p_), rng.randrange(p_)); A[j][i] = cj(A[i][j])
            return tuple(tuple(r) for r in A)
        def unitary():
            while True:
                S_ = tuple(tuple(ml(P(0, 1), x) for x in r) for r in herm())           # ηH is anti-Hermitian
                if d3(a3(e3, S_, -1)) == Z: continue
                U = m3(a3(e3, S_), i3(a3(e3, S_, -1)))
                U = m3(((iv(d3(U)), Z, Z), (Z, I1, Z), (Z, Z, I1)), U)                  # the determinant is a unitary point
                assert m3(dg(U), U) == e3 and d3(U) == I1
                return U
        odd = lambda z: z[0] == 0
        shell = lambda z: z[1] == 0
        com = lambda A, B: a3(m3(A, B), m3(B, A), -1)
        U = unitary()
        while t3(U)[1] == 0: U = unitary()
        V = unitary(); Ui = dg(U); O = ad(t3(U), ng(t3(Ui)))
        ok_ = m3(U, Ui) == e3 and t3(Ui) == cj(t3(U)) and odd(O) and O != Z
        ok_ &= ad(t3(m3(m3(V, U), dg(V))), ng(t3(m3(m3(V, Ui), dg(V))))) == O            # gauge invariant
        ok_ &= ad(t3(fb(U)), ng(t3(dg(fb(U))))) == ng(O)                                # the Frobenius negates it
        while True:
            Au, Ad = herm(), herm(); Mu, Md = m3(Au, Au), m3(Ad, Ad); J = d3(com(Mu, Md))
            if J != Z: break
        W = unitary(); cjg = lambda A: m3(m3(W, A), dg(W))
        ok_ &= odd(J) and d3(com(cjg(Mu), cjg(Md))) == J and d3(com(fb(Mu), fb(Md))) == ng(J)
        Ad2 = a3(m3(Au, Au), Au); ok_ &= d3(com(Mu, m3(Ad2, Ad2))) == Z                 # a polynomial in A_u commutes with it
        ok_ &= dg(com(Mu, Md)) == tuple(tuple(ng(x) for x in r) for r in com(Mu, Md))   # the commutator is anti-Hermitian
        hol = {}
        for m_, n_ in ((0, 1), (0, 2), (0, 3), (1, 2), (1, 3), (2, 3)):
            X = unitary(); hol[(m_, n_)] = X; hol[(n_, m_)] = dg(X)
        F_ = {k_: a3(v_, dg(v_), -1) for k_, v_ in hol.items()}
        def eps(q):
            s_ = 1
            for x in range(4):
                for y in range(x + 1, 4):
                    if q[x] > q[y]: s_ = -s_
            return s_
        perms = [q for q in product(range(4), repeat=4) if len(set(q)) == 4]
        def T1of(Fs):
            t = Z
            for q in perms:
                v_ = t3(m3(Fs[(q[0], q[1])], Fs[(q[2], q[3])])); t = ad(t, v_ if eps(q) == 1 else ng(v_))
            return t
        T1 = T1of(F_); T1s = T1of({k_: fb(v_) for k_, v_ in F_.items()})
        i_ = pow(g_, p_ - 1 - (p_ - 1) // 4, p_); lam = P(0, i_)
        T2 = ml(iv(lam), T1)
        ok_ &= i_ * i_ % p_ == p_ - 1 and ml(lam, lam) == P(-g_) and pow(p_ - g_, (p_ - 1) // 2, p_) == p_ - 1
        ok_ &= shell(T1) and T1 != Z and T1s == T1 and odd(T2) and ml(iv(ng(lam)), ng(T1)) == T2
        ok_ &= shell(ml(J, O)) and ml(J, O) != Z and shell(ml(J, T2)) and ml(J, T2) != Z
        ok_ &= ml(ng(J), ml(iv(ng(lam)), T1s)) == ml(J, T2)                             # the Frobenius on all the data
        return ok_, f"F_{p_}: O = {O[1]}η, J = {J[1]}η, T₁ = {T1[0]}, J·O = {ml(J, O)[0]}, J·λ⁻¹T₁ = {ml(J, T2)[0]}"
    ok = True; det = []
    for p_ in (13, 173, 1549):
        o_, d_ = parity(p_, prim_roots(p_)[0]); ok &= o_; det.append(d_)
    # 27:C17 (p27060)
    R.check("C17", "the Frobenius parity of a tally on the Subjects 13, 173, 1549: for a frame move U of determinant one the "
            "difference tr U − tr U⁻¹ lies in ηF_p, is gauge invariant and is negated by the Frobenius; the density T₁ of a "
            "cell lies in the shell and λ⁻¹T₁ in ηF_p, unchanged by Γ → −Γ with λ → −λ; the determinant J of the commutator of "
            "two squares of Hermitian matrices lies in ηF_p, is invariant under a generation-frame move and is 0 when they "
            "commute; the products J·(tr U − tr U⁻¹) and J·λ⁻¹T₁ lie in the shell, are not 0 on the samples, and the Frobenius "
            "on all the data fixes them", ok, "; ".join(det))

    # C18 the lift of one chronon to the doublet (pass 11 of 17 November 2026), on 13, 173, 1549. D = diag(η, η⁻¹) has
    #     determinant one, D² = diag(g, g⁻¹) and σ(D) = −D, and D is η⁻¹ times diag(g, 1). D moves a point z of the shell to gz
    #     and its square to g²z. The conjugation by D multiplies E and F by g and g⁻¹, and that by D² by g² and g⁻². D
    #     multiplies the Hermitian pairings of the two components by −g and −g⁻¹. A ray [x : y] is kept by one chronon exactly
    #     when x = 0 or y = 0. The entry η has the norm −g and the quotient η/σ(η) = −1.
    ok = True; det = []
    for p_ in (13, 173, 1549):
        g_ = prim_roots(p_)[0]; gi = pow(g_, p_ - 2, p_); rng = random.Random(2700 + p_)
        ml = lambda x, y: ((x[0] * y[0] + g_ * x[1] * y[1]) % p_, (x[0] * y[1] + x[1] * y[0]) % p_)
        cj = lambda x: (x[0], -x[1] % p_)
        def iv(x):
            n_ = pow((x[0] * x[0] - g_ * x[1] * x[1]) % p_, p_ - 2, p_); return (x[0] * n_ % p_, -x[1] * n_ % p_)
        eta = (0, 1); etai = iv(eta); one = (1, 0); zero = (0, 0); sh = lambda a: (a % p_, 0)
        ok &= ml(eta, etai) == one and ml(eta, eta) == sh(g_) and ml(etai, etai) == sh(gi)          # det D = 1, D² = diag(g, g⁻¹)
        ok &= cj(eta) == (0, p_ - 1) and cj(etai) == (0, -etai[1] % p_)                             # σ(D) = −D
        ok &= ml(etai, sh(g_)) == eta and ml(etai, one) == etai                                     # D = η⁻¹ diag(g, 1)
        zs = [rng.randrange(1, p_) for _ in range(20)]
        ok &= all(ml(ml(eta, sh(z)), iv(etai)) == sh(g_ * z) for z in zs)                           # z ↦ gz
        ok &= all(ml(sh(g_ * z), iv(sh(gi))) == sh(g_ * g_ * z) for z in zs)                        # D²: z ↦ g²z
        ok &= ml(eta, iv(etai)) == sh(g_) and ml(etai, iv(eta)) == sh(gi)                           # E ↦ gE, F ↦ g⁻¹F
        ok &= ml(cj(eta), eta) == sh(-g_) and ml(cj(etai), etai) == sh(-gi)                         # the pairings
        ok &= (-g_) % p_ != 1 and g_ * g_ % p_ != 1 and g_ % p_ != 1
        rays = [((rng.randrange(p_), rng.randrange(p_)), (rng.randrange(p_), rng.randrange(p_))) for _ in range(40)] + [(zero, one), (one, zero)]
        ok &= all((ml(ml(sh(g_), x), y) == ml(x, y)) == (x == zero or y == zero) for x, y in rays)  # the kept rays
        ok &= ml(eta, iv(cj(eta))) == sh(-1)                                                        # the quotient η/σ(η)
        det.append(f"F_{p_}: g = {g_}, weights {g_} and {gi}, pairings {(-g_) % p_} and {(-gi) % p_}")
    # (C18 decides no row; the rows C15 and C4 keep their deciding checks C13 and C2)
    R.check("C18", "the lift of one chronon to the doublet on the Subjects 13, 173, 1549: D = diag(η, η⁻¹) has determinant one, "
            "D² = diag(g, g⁻¹) and σ(D) = −D; D moves a point of the shell by one chronon and D² by two; the conjugation by D "
            "multiplies E and F by g and g⁻¹, and D multiplies the Hermitian pairings of the two components by −g and −g⁻¹; a "
            "ray is kept by one chronon exactly when one of its two components is 0 (42 rays each); the entry η has the norm "
            "−g and the quotient −1", ok, "; ".join(det))

    # C19 commutation and the internal frame (27 November 2026), on 13, 173, 1549. The matrices that commute with the two
    #     unipotent frame moves on the frame plane V, or on its symmetric square, are the scalars: dimension 1. On
    #     V ⊗ K^r (r = 2, 3, 5) and on Sym²(V) ⊗ K³ they are the 1 ⊗ A: dimension r². The frame moves keep the form
    #     v² − 4uw of the symmetric square, with determinant one. A scalar λ keeps its Hermitian form exactly when
    #     σ(λ)λ = 1: every element of K on 13, where p + 1 scalars keep it, and 400 elements on 173 and 1549.
    ok = True; det = []
    for p_ in (13, 173, 1549):
        g_ = prim_roots(p_)[0]; K = I.Fq2(p_, 0, g_); rng = random.Random(2761 + p_)
        U, L_, D = [[1, 1], [0, 1]], [[1, 0], [1, 1]], [[g_, 0], [0, pow(g_, p_ - 2, p_)]]
        S = lambda A: I.sym2_move(A, p_); e = lambda r: [[int(i == j) for j in range(r)] for i in range(r)]
        dims = [I.commutant_dim([U, L_], p_), I.commutant_dim([S(U), S(L_)], p_)]
        dims += [I.commutant_dim([I.kron(U, e(r), p_), I.kron(L_, e(r), p_)], p_) for r in (2, 3, 5)]
        dims.append(I.commutant_dim([I.kron(S(U), e(3), p_), I.kron(S(L_), e(3), p_)], p_))
        ok &= dims == [1, 1, 4, 9, 25, 9]
        B = [[0, 0, -2 % p_], [0, 1, 0], [-2 % p_, 0, 0]]                                  # the form v² − 4uw
        mm = lambda X, Y: [[sum(a * b for a, b in zip(r, c)) % p_ for c in zip(*Y)] for r in X]
        for A in (U, L_, D):
            M = S(A); ok &= mm(mm([list(c) for c in zip(*M)], B), M) == B
            ok &= I.det(K, tuple(tuple(K.scalar(x) for x in r) for r in M)) == K.one
        elems = K.elements() if p_ == 13 else [(rng.randrange(p_), rng.randrange(p_)) for _ in range(400)]
        keep = 0
        for lam in elems:
            n_ = K.mul(K.conj(lam), lam)
            keeps = all(K.mul(n_, K.scalar(b)) == K.scalar(b) for r in B for b in r)
            ok &= keeps == (n_ == K.one); keep += keeps
        ok &= p_ != 13 or keep == p_ + 1
        det.append(f"F_{p_}: dimensions {dims}")
    # 27:C18 (p27061)
    R.check("C19", "commutation and the internal frame on the Subjects 13, 173, 1549: the matrices that commute with the two "
            "unipotent frame moves on the frame plane V and on its symmetric square are the scalars (dimension 1), and on "
            "V ⊗ K^r (r = 2, 3, 5) and Sym²(V) ⊗ K³ they are the 1 ⊗ A (dimension r²); the frame moves keep the form v² − 4uw "
            "of the symmetric square with determinant one, and a scalar keeps its Hermitian form exactly when its norm is one "
            "(p + 1 scalars on 13)", ok, "; ".join(det))


# ------------------------------------------------------------------------------------------------------------
# block D: the electroweak scale against the gauge transmutation form (27:Z1)
# The weak coupling at the channel's normalisation is g² = 24: the electron's coupling is α = 9/4π (27:C2), the frame's
# rational is sin²θ_W = 3/8 (27:C6), and e = g sin θ_W. With b₂ = 19/6 the form m_P exp(−8π²/b₂g²) lands at 4 × 10¹⁸ GeV,
# and it reaches M_W only for b = 0.083. The SU(2) infrared scale is far below v. The QCD control is consistent. The check
# is a continuum reading on the measured scales: CHART. The row 27:Y1 was withdrawn on 21 November 2026 with its check D2.
@R.block("D", BLOCK["D"])
def block_D():
    """Block D — the electroweak scale: D1 CHART."""
    r = CF.v_scale()
    ok = _within(r["g2"], 24, Q(1, 10 ** 9)) and 4 * 10 ** 18 < Q(r["L_b2"]) < 5 * 10 ** 18
    ok &= _within(r["b_fit_MW"], Q(83, 1000), Q(1, 1000)) and Q(r["mu_IR"]) < Q(1, 10 ** 20)
    ok &= _within(Q(r["as_MP_needed"]) / Q(r["as_MP_run"]), 1, Q(1, 10))
    # 27:Z1 (p27047)
    R.check("D1", "[chart] v against the gauge transmutation form at the coupling of the channel's normalisation, g² = 24 (the "
            "electron's α = 9/4π, sin²θ_W = 3/8, e = g sin θ_W): b₂ = 19/6 gives 4 × 10¹⁸ GeV, and the form reaches M_W only for "
            "b = 0.083; the SU(2) infrared scale is below 10⁻²⁰ GeV; the QCD control agrees within 10 %: the absolute scales lie "
            "beyond the coherence horizon",
            ok, f"g² = {r['g2']:.0f}, b = {r['b_fit_MW']:.3f}, Λ(b₂) = {r['L_b2']:.2e} GeV, μ_IR = {r['mu_IR']:.1e} GeV, "
                f"α_s(M_P) {r['as_MP_needed']:.4f} vs {r['as_MP_run']:.4f}", kind="CHART")


# ------------------------------------------------------------------------------------------------------------
# block E: the strong sector (27:C7, C8, X1, X7, Z1)
# qcd.py builds SU(3, 2) over F_4, of order 216 with centre Z_3 (E1), and the strong-coupling string tensions of U(1)
# and Z_N on the chart (E2). p5.py gauges the colour frame over F_4. string_tension.py gives c₁ as an exact character sum,
# in closed form on 2T and as the series β/18 + β²/216 for SU(3) (E4, E5), with its resolved-window fit on the chart
# (E5c). p6.py has b₀ = 11 − (2/3)n_f (E6) and Λ_QCD by transmutation on the chart (E7). missing_rank.py has the rank
# tower and two frame moves of SU(3, F_p) on the Subjects 13, 173, 1549: the gauging of the colour frame (E8, 27:X1).
# The pass of 27 November 2026 has the blocks of the lift of the drive (E9), the exact constraints on the colour rank
# (E10), the integers of the one-loop form (E11) and the colour rank in the imported one-loop law on the chart (E12).
@R.block("E", BLOCK["E"])
def block_E():
    """Block E — the strong sector: E1, E3–E6, E8–E11 EXACT; E2, E5c, E7, E12 CHART."""
    F4 = I.Fq2(2, 1, 1)                                                          # F_4 = F_2[w], w² = w + 1
    code = lambda x: x[0] + 2 * x[1]                                             # 0, 1, w, w² as the package's 0, 1, 2, 3
    su3 = sorted(I.unitary_frames(F4, 3), key=lambda M: tuple(code(e) for row in M for e in row))
    cube = [x for x in F4.elements() if x != F4.zero and F4.mul(x, F4.conj(x)) == F4.one and F4.pow(x, 3) == F4.one]
    scal = lambda x: tuple(tuple(x if i == j else F4.zero for j in range(3)) for i in range(3))
    mm0 = lambda X, Y: I.mat_mul(F4, X, Y)
    centre = [g for g in su3 if all(mm0(g, h) == mm0(h, g) for h in su3)]         # the centre, by the 216² products
    # E1 the laboratory model SU(3, 2) by its orthonormal frames over F_4: order 216, the centre the scalar cube roots of unity
    R.check("E1", "the laboratory model SU(3, 2) over F_4 has order 216 by exhaustive enumeration; the centre, by all 216² products, "
            "is the three scalar cube roots of unity (Z_3, colour triality)",
            len(su3) == 216 and len(cube) == 3 and sorted(centre) == sorted(scal(x) for x in cube),
            f"|SU(3,2)| = {len(su3)}, centre Z_{len(centre)}")

    # E2 [chart] the strong-coupling string tension σ = −ln c₁(β): U(1) (σ(0.5) = 1.4168, positive, decreasing), Z₃ positive
    s = {b: Q(CF.sigma_U1(b)) for b in (Q(2, 10), Q(5, 10), Q(1), Q(2), Q(4))}
    bs = sorted(s)
    ok = abs(s[Q(1, 2)] - Q(14168, 10000)) < Q(1, 1000) and all(s[a] > s[b] > 0 for a, b in zip(bs, bs[1:]))
    ok &= all(Q(CF.sigma_ZN(b, 3)) > 0 for b in bs)
    R.check("E2", "[chart] the U(1) string tension σ(0.5) = 1.4168, positive and decreasing in β (0.2 … 4.0); σ_Z₃(β) > 0", ok,
            f"σ_U(1)(0.5) = {CH.show(s[Q(1, 2)], '.4f')}", kind="CHART")

    # E3 the gluon connection over F_4: the plaquette conjugates, Tr P invariant exhaustively, the commutator plaquette of
    #    two non-commuting links ≠ I against = I for the diagonal U(1) control, the triplet covariant
    mm = lambda X, Y: I.mat_mul(F4, X, Y); inv = lambda X: I.dagger(F4, X); tr = lambda X: I.trace(F4, X)
    one = tuple(tuple(F4.one if i == j else F4.zero for j in range(3)) for i in range(3))
    Uab, Ubc, Ucd, Uda = su3[7], su3[40], su3[123], su3[200]; ga, gb, gc, gd = su3[3], su3[55], su3[150], su3[210]
    P = mm(mm(Uab, Ubc), mm(Ucd, Uda))
    U2 = [mm(mm(ga, Uab), inv(gb)), mm(mm(gb, Ubc), inv(gc)), mm(mm(gc, Ucd), inv(gd)), mm(mm(gd, Uda), inv(ga))]
    P2 = mm(mm(U2[0], U2[1]), mm(U2[2], U2[3]))
    ok = P2 == mm(mm(ga, P), inv(ga)) and tr(P2) == tr(P) and all(tr(mm(mm(g, P), inv(g))) == tr(P) for g in su3)
    X, Y = next((X, Y) for X in su3 for Y in su3 if mm(X, Y) != mm(Y, X))
    Fc = mm(mm(X, Y), mm(inv(X), inv(Y)))
    w = (0, 1); w2 = F4.mul(w, w)
    dg = lambda a, b, c: ((a, F4.zero, F4.zero), (F4.zero, b, F4.zero), (F4.zero, F4.zero, c))
    D1, D2 = dg(F4.one, w, w2), dg(w, F4.one, w2)
    Fab = mm(mm(D1, D2), mm(inv(D1), inv(D2)))
    el = {0: (0, 0), 1: (1, 0), 2: (0, 1), 3: (1, 1)}
    psi_a, psi_b = tuple(el[c] for c in (1, 2, 0)), tuple(el[c] for c in (0, 1, 3))
    vsub = lambda u, v: tuple(F4.sub(x, y) for x, y in zip(u, v))
    Dq = vsub(psi_a, I.matvec(F4, Uab, psi_b)); Dq2 = vsub(I.matvec(F4, ga, psi_a), I.matvec(F4, U2[0], I.matvec(F4, gb, psi_b)))
    ok &= Fc != one and Fab == one and Dq2 == I.matvec(F4, ga, Dq) and len(su3) == 216
    R.check("E3", "the SU(3, F_4) gluon connection: the plaquette conjugates and Tr P is invariant over all of SU(3, 2); the "
            "commutator plaquette U₁U₂U₁⁻¹U₂⁻¹ ≠ I (gluon self-coupling), = I for the abelian control; the triplet covariant", ok,
            f"Tr P = {tr(P)}")

    # E4 the string tension, exact. S₃ and 2T satisfy character orthogonality, with the trace multiset of 2T
    #    {2:1, −2:1, 0:6, 1:8, −1:8}. The moments of 2T give c₁^{2T}(β) = β/4 + …, equal to the continuum SU(2) series
    #    I₂/I₁ through β⁴. σ > 0 for every β > 0 by the closed form of B4. |SU(3, 2)| = 216 and its centre is Z_3.
    chars = {"triv": (1, 1, 1), "sgn": (1, -1, 1), "std": (2, 0, -1)}; sizes = (1, 3, 2)
    ok = all(sum(s_ * c for s_, c in zip(sizes, chars[r])) == 0 for r in ("sgn", "std"))
    ok &= all(Q(sum(s_ * c * c for s_, c in zip(sizes, chars[r])), 6) == 1 for r in chars)
    G, closed, unit, traces = I.tetrahedral_quaternions()
    ok &= len(G) == 24 and closed and unit
    ok &= traces == {2: 1, -2: 1, 0: 6, 1: 8, -1: 8} and sum(t * m for t, m in traces.items()) == 0
    mom = [Q(sum(m * t ** k for t, m in traces.items()), 24) for k in range(8)]
    c2T = I.moment_c1_series(mom, 2, 7); cSU2 = I.bessel_ratio_series(1, 7)
    ok &= c2T[0] == 0 and c2T[1] == Q(1, 4) and c2T[:5] == cSU2[:5] and c2T[5] != cSU2[5]      # the difference starts at β⁵
    ok &= I.area_law_rational()[2]                                                # 0 < c₁ < 1 for every x > 1 (B4)
    ok &= len(su3) == 216 and len(centre) == 3 and (2 + 1) % 3 == 0
    # 27:X7 (p27030)
    R.check("E4", "the string tension in closed form on 2T: S₃ and 2T character orthogonality; |2T| = 24 in SU(2, C) with traces "
            "{2:1, −2:1, 0:6, 1:8, −1:8}; c₁^{2T} = β/4 + … agrees with continuum SU(2) through β⁴; σ > 0 for every β > 0 by "
            "the closed form of B4; |SU(3, 2)| = 216, centre Z_3", ok,
            f"c₁^2T series {[str(c) for c in c2T[:6]]}; I₂/I₁ {[str(c) for c in cSU2[:6]]}")

    # E5 colour SU(3): c₁ = β/18 + β²/216 + … exactly, from the Haar moments of the fundamental character (the Weyl
    #    constant term)
    mom = []
    for k in range(5):
        mom.append(sum(comb(k, j) * I.su3_moment(j, k - j) for j in range(k + 1)) * Q(1, 2 ** k))
    c3 = I.moment_c1_series(mom, 3, 4)
    R.check("E5", "colour SU(3): c₁ = β/18 + β²/216 + … exactly, from the Haar moments of the fundamental character (the "
            "Weyl constant term)", c3[:3] == [0, Q(1, 18), Q(1, 216)], f"series {[str(c) for c in c3]}")

    # E5c [chart] the package's fit on the chart agrees with the series within 10⁻⁴, σ^{SU(3)} > 0 at β = 0.2 … 8,
    #     and the U(1) normalisation σ(0.5) = 1.4168
    a, b, _ = CF.su3_fit()
    ok = abs(Q(a) - Q(1, 18)) < Q(1, 10 ** 4) and abs(Q(b) - Q(1, 216)) < Q(1, 10 ** 4)
    ok &= all(0 < Q(CF.c1_su3(be)) < 1 for be in (Q(2, 10), Q(5, 10), Q(1), Q(2), Q(4), Q(8)))
    ok &= abs(Q(CF.sigma_U1(Q(1, 2))) - Q(14168, 10000)) < Q(1, 1000)
    R.check("E5c", "[chart] the fit of c₁^{SU(3)} on the chart agrees with β/18 + β²/216 within 10⁻⁴; σ^{SU(3)}(β) > 0 at "
            "β = 0.2 … 8; the U(1) normalisation σ(0.5) = 1.4168", ok, f"fit {a:.6f} β + {b:.6f} β²", kind="CHART")

    # E6 asymptotic freedom: b₀ = 11 − (2/3)n_f exactly, positive up to n_f = 16, while the abelian b₀ is negative
    b0 = lambda nf: 11 - Q(2, 3) * nf; bU = lambda nf: -Q(4, 3) * nf
    ok = b0(2) == Q(29, 3) and b0(6) == 7 and b0(16) > 0 and b0(17) < 0 and all(bU(n_) < 0 for n_ in (2, 6, 16))
    R.check("E6", "b₀ = 11 − (2/3)n_f as exact rationals: 29/3 at n_f = 2, 7 at n_f = 6, positive up to 16, negative at 17; the "
            "abelian b₀ < 0", ok)

    # E7 [chart] Λ_QCD by one-loop transmutation from the M_Z anchor (n_f = 5) lies in the 50–500 MeV decade, and
    #    (m_p/m_P)² = e^{−88}
    lam = Q(CF.lambda_qcd(b0(5))); ex = Q(CF.proton_planck_exponent())
    ok = Q(5, 100) < lam < Q(5, 10) and abs(ex - 88) < Q(1, 10)
    R.check("E7", "[chart] Λ_QCD = M_Z exp(−2π/(b₀α_s)) at n_f = 5 lies in 50–500 MeV; (m_p/m_P)² = e^{−88.0}", ok,
            f"Λ = {CH.show(lam * 1000, '.0f')} MeV, 2 ln(m_P/m_p) = {CH.show(ex, '.2f')}", kind="CHART")

    # E8 the rank tower and two frame moves of the colour frame. On the laboratory Carriers 233, 30089, 2408561 and on
    #    the Subject 173, all ≡ 5 (mod 12), gcd(n, x + 1) = n for n = 1, 2, 3. On each Subject 13, 173, 1549, over
    #    K = F_p[η]: a diagonal matrix of norm-one entries with product 1 and the cyclic permutation matrix are unitary of
    #    determinant 1, do not commute, and the trace of their commutator is a class function. The norm-one cube roots of
    #    unity number gcd(3, p + 1). No set of vectors or of frame moves is enumerated.
    A_ok = all([gcd(n_, x + 1) for n_ in (1, 2, 3)] == [1, 2, 3] and x % 12 == 5 for x in (233, 30089, 2408561, 173))
    r3 = min(n_ for n_ in range(1, 13) if gcd(n_, 6) % 3 == 0); r2 = min(n_ for n_ in range(1, 13) if gcd(n_, 6) % 2 == 0)
    ok = A_ok and r3 == 3 and r2 == 2; det = []
    for p_ in (13, 173, 1549):
        K = I.Fq2(p_, 0, arith.primitive_root(p_))
        u = K.pow((1, 1), p_ - 1)                                              # (1 + η)^(p − 1), of norm one
        u2 = K.mul(u, u); u3 = K.inv(K.mul(u, u2))
        m3 = (-3) % p_; r = next((x for x in range(p_) if x * x % p_ == m3), None)   # √−3: on the shell, or a multiple of η
        s3 = (r, 0) if r is not None else (0, next(c for c in range(p_) if c * c * arith.primitive_root(p_) % p_ == m3))
        i2 = K.scalar(pow(2, p_ - 2, p_)); roots = [K.one] + [K.mul(K.add(K.scalar(p_ - 1), t), i2) for t in (s3, K.mul(K.scalar(p_ - 1), s3))]
        ok &= len(set(roots)) == 3 and all(K.pow(x, 3) == K.one for x in roots)
        cube = sum(1 for x in roots if K.norm(x) == 1)
        U1 = ((u, K.zero, K.zero), (K.zero, u2, K.zero), (K.zero, K.zero, u3))
        U2 = ((K.zero, K.one, K.zero), (K.zero, K.zero, K.one), (K.one, K.zero, K.zero))
        one = tuple(tuple(K.one if i == j else K.zero for j in range(3)) for i in range(3))
        mm = lambda X, Y, K=K: I.mat_mul(K, X, Y); dg_ = lambda X, K=K: I.dagger(K, X)
        unit = mm(dg_(U1), U1) == one and mm(dg_(U2), U2) == one and K.norm(u) == 1 and u != K.one and u2 != u
        dets = I.det(K, U1) == K.one and I.det(K, U2) == K.one
        Up = mm(mm(U1, U2), mm(dg_(U1), dg_(U2)))
        gi = I.trace(K, mm(mm(U2, Up), dg_(U2))) == I.trace(K, Up)
        ok &= unit and dets and gi and Up != one and cube == gcd(3, p_ + 1)
        det.append(f"F_{p_}: cube roots of norm one {cube}")
    ok &= comb(5, 0) + comb(5, 2) + comb(5, 4) == 16
    ok &= [gcd(3, q_ + 1) for q_ in (13, 173, 1549)] == [1, 3, 1]              # the centre of order 3 on the Subject 173 alone
    # 27:C7 (p27019)
    R.check("E8", "the rank tower: gcd(n, x + 1) = n for n = 1, 2, 3 on the laboratory Carriers 233, 30089, 2408561 and on the "
            "Subject 173, all ≡ 5 (mod 12); the centre of order 3 on the Subject 173 and not on 13 or 1549, with as many "
            "norm-one cube roots of unity; minimal ranks 3 (colour) and 2 (isospin), the gauging of the colour frame; on each "
            "Subject two frame moves of SU(3, F_p), unitary, det 1, non-commuting, the trace of their commutator a class "
            "function; dim Λ^even(K⁵) = 16", ok, "; ".join(det))

    # E9 the drive and the blocks of the internal frame (27 November 2026), on 13, 173, 1549, for the colour ranks m = 1
    #    to 4. The lift of one chronon is diag(1, …, 1, η, η⁻¹), with three distinct values. A vector is fixed exactly
    #    when its last two entries are 0. A matrix over K commutes with the lift exactly when its entries between
    #    directions of different value are 0: the blocks of rank m, 1 and 1, with m² + 2 free entries. The same holds for
    #    two chronons, diag(1, …, 1, g, g⁻¹).
    ok = True; det = []
    for p_ in (13, 173, 1549):
        g_ = arith.primitive_root(p_); K = I.Fq2(p_, 0, g_); rng = random.Random(2762 + p_)
        eta = (0, 1); etai = K.inv(eta); rnd = lambda: (rng.randrange(p_), rng.randrange(p_))
        ok &= K.mul(eta, eta) == K.scalar(g_) and len({K.one, eta, etai}) == 3 and len({1, g_, pow(g_, p_ - 2, p_)}) == 3
        for m in (1, 2, 3, 4):
            n = m + 2
            for vals in ([K.one] * m + [eta, etai], [K.one] * m + [K.scalar(g_), K.inv(K.scalar(g_))]):
                Dh = tuple(tuple(vals[i] if i == j else K.zero for j in range(n)) for i in range(n))
                ok &= sum(vals[i] == vals[j] for i in range(n) for j in range(n)) == m * m + 2
                for _ in range(10):
                    X = tuple(tuple(rnd() for _ in range(n)) for _ in range(n))
                    Xb = tuple(tuple(X[i][j] if vals[i] == vals[j] else K.zero for j in range(n)) for i in range(n))
                    ok &= I.mat_mul(K, Dh, Xb) == I.mat_mul(K, Xb, Dh)                           # the blocks commute
                    ok &= (I.mat_mul(K, Dh, X) == I.mat_mul(K, X, Dh)) == (X == Xb)              # and no other matrix does
                    v = tuple(rnd() for _ in range(n)); w = v[:m] + (K.zero, K.zero)
                    ok &= I.matvec(K, Dh, w) == w                                                # the colour frame is fixed
                    ok &= (I.matvec(K, Dh, v) == v) == (v == w)                                  # and no other vector is
        det.append(f"F_{p_}: 1, η, η⁻¹ distinct, g = {g_}")
    # 27:C19 (p27062)
    R.check("E9", "the drive and the blocks of the internal frame on the Subjects 13, 173, 1549, colour ranks 1 to 4: the lift "
            "of one chronon diag(1, …, 1, η, η⁻¹) has three distinct values; the vectors it fixes are those of the colour "
            "frame; a matrix over K commutes with it exactly when it has the blocks of rank m, 1 and 1 (m² + 2 free "
            "entries; 10 matrices and 10 vectors each); the same for two chronons", ok, "; ".join(det))

    # E10 the exact constraints on the colour rank m of an internal frame of rank m + 2 (27 November 2026).
    #     (i) The weights of the even exterior algebra are closed under negation exactly when the rank n is even (n = 2
    #     to 10). On 13, 173, 1549 and n = 4 to 7, on 40 diagonal frame moves of determinant one each, the conjugate of
    #     the trace on the even half is the trace on the even half (n even) or on the odd half (n odd), the two traces
    #     differ by ∏(1 − z_i), and some frame move separates them.
    #     (ii) x² + x + 1 has no root on the Carriers 233, 30089, 2408561. On the Subject 173 (3 | p + 1) its two roots
    #     lie in K with norm one, and ω^m = 1 exactly when 3 | m (m = 1 to 12). On 13 and 1549 the roots are residues
    #     of the shell, and their norm is not one.
    #     (iii) One generation holds every exterior power of the colour frame twice (m = 2 to 10). The index of the k-th
    #     power is C(m − 2, k − 1)/2 and the index sum of a generation is 2^(m−2), by enumeration for m = 2 to 10 and by
    #     the binomial sum for m = 2 to 408. The two constraints leave m = 3, 9, 15 below 20.
    ok = all((I.even_weights(n) == sorted(tuple(-x for x in v) for v in I.even_weights(n))) == (n % 2 == 0) for n in range(2, 11))
    rng = random.Random(27112026); det = []
    for p_ in (13, 173, 1549):
        K = I.Fq2(p_, 0, arith.primitive_root(p_))
        def unit():                                                                  # x/σ(x), a point of the unitary cycle
            while True:
                x = (rng.randrange(p_), rng.randrange(p_))
                if K.norm(x): return K.mul(K.mul(x, x), K.scalar(pow(K.norm(x), p_ - 2, p_)))
        for n in (4, 5, 6, 7):
            sep = False
            for _ in range(40):
                z = [unit() for _ in range(n - 1)]; pr = K.one
                for u in z: pr = K.mul(pr, u)
                z.append(K.conj(pr)); half = [K.zero, K.zero]                        # the last entry makes the determinant one
                for S in range(2 ** n):
                    w = K.one
                    for i_ in range(n):
                        if S >> i_ & 1: w = K.mul(w, z[i_])
                    half[bin(S).count("1") % 2] = K.add(half[bin(S).count("1") % 2], w)
                ok &= K.conj(half[0]) == half[n % 2]
                diff = K.one
                for u in z: diff = K.mul(diff, K.sub(K.one, u))
                ok &= K.sub(half[0], half[1]) == diff; sep |= half[0] != half[1]
            ok &= sep
    ok &= all(Om % 12 == 5 and pow(Om - 3, (Om - 1) // 2, Om) == Om - 1 for Om in (233, 30089, 2408561))   # −3 is no square
    K = I.Fq2(173, 0, arith.primitive_root(173))
    roots = [x for x in K.elements() if x[1] and K.add(K.add(K.mul(x, x), x), K.one) == K.zero]
    ok &= len(roots) == 2 and all(K.norm(w) == 1 for w in roots)
    ok &= all((K.pow(w, m) == K.one) == (m % 3 == 0) for w in roots for m in range(1, 13))
    for q_ in (13, 1549):
        rs = [a for a in range(q_) if (a * a + a + 1) % q_ == 0]; ok &= len(rs) == 2 and all(a * a % q_ != 1 for a in rs)
    for m in range(2, 11):
        n = m + 2; count = Counter(S & (2 ** m - 1) for S in range(2 ** n) if bin(S).count("1") % 2 == 0)
        ok &= len(count) == 2 ** m and set(count.values()) == {2}
        idx = [I.exterior_index(m, k) for k in range(m + 1)]
        ok &= idx == [Q(comb(m - 2, k - 1), 2) if 1 <= k <= m - 1 else 0 for k in range(m + 1)] and 2 * sum(idx) == 2 ** (m - 2)
    ok &= all(sum(comb(m - 2, k - 1) for k in range(1, m)) == 2 ** (m - 2) for m in range(2, 409))
    ok &= [m for m in range(1, 20) if m % 3 == 0 and m % 2 == 1] == [3, 9, 15]
    # 27:C20 (p27063)
    R.check("E10", "the exact constraints on the colour rank m of a frame of rank m + 2: the generation is its own conjugate "
            "exactly when m is even (the weights for ranks 2 to 10; the traces of 40 diagonal frame moves of determinant one "
            "on the Subjects 13, 173, 1549, ranks 4 to 7); on the Subject 173 the triality scalar has determinant one "
            "exactly when 3 | m, and x² + x + 1 has no root on the Carriers 233, 30089, 2408561; one generation holds every "
            "exterior power of the colour frame twice, with the index sum 2^(m−2) on the ranks 2 to 408; the two constraints "
            "leave 3, 9, 15 below 20", ok)

    # E11 the integers of the one-loop form on the colour ranks 2 to 408 (27 November 2026): 11m − 3·2^(m−1) for three
    #     generations and 11m − 2^(m−1) for one. The first is positive for m = 2 to 5, the second for m = 2 to 7. A
    #     multiple of three with the first positive is three, and an odd multiple of three with the second positive is
    #     three. The largest integer formed is 3·2^407.
    three = [m for m in range(2, 409) if I.one_loop_integer(m, 3) > 0]; one = [m for m in range(2, 409) if I.one_loop_integer(m, 1) > 0]
    ok = three == [2, 3, 4, 5] and one == [2, 3, 4, 5, 6, 7]
    ok &= [I.one_loop_integer(m, 3) for m in three] == [16, 21, 20, 7] and [I.one_loop_integer(m, 1) for m in one] == [20, 29, 36, 39, 34, 13]
    ok &= [m for m in three if m % 3 == 0] == [3] and [m for m in one if m % 3 == 0 and m % 2 == 1] == [3]
    ok &= [m for m in three if m % 2 == 1] == [3, 5]                                    # without the triality
    # 27:C21 (p27064)
    R.check("E11", "the integers of the one-loop form on the colour ranks 2 to 408: 11m − 3·2^(m−1) is 16, 21, 20, 7 for m = 2 "
            "to 5 and not positive from 6; 11m − 2^(m−1) is 20, 29, 36, 39, 34, 13 for m = 2 to 7 and not positive from 8; a "
            "multiple of three with the first positive is three, and an odd multiple of three with the second positive is "
            "three", ok, f"positive at {three} and at {one}")

    # E12 [chart] the colour rank (27 November 2026). The imported one-loop law, read on a frame of rank m with G
    #     generations of index sum 2^(m−2), has b₀ = (11/3)m − (2/3)·G·2^(m−2): 29/3 and 7 at m = 3, the values of E6. With
    #     b₀ > 0 above three generations and the triality the rank is three; with b₀ > 0 for one generation, the triality
    #     and the odd rank it is three. The frame then has rank five and a generation sixteen states. The range 2 to 408
    #     against ln Ω = 283.5, read between 283.45 and 283.55: the largest integer formed, 3·2^407, lies below Ω, and
    #     from the rank 409 a generation has 2^410 states or more, above Ω.
    b0 = lambda m, G: Q(11, 3) * m - Q(2, 3) * G * 2 ** (m - 2)
    ok = b0(3, 1) == Q(29, 3) and b0(3, 3) == 7 and all(3 * b0(m, G) == I.one_loop_integer(m, G) for m in range(2, 409) for G in (1, 3))
    ok &= [m for m in range(2, 409) if m % 3 == 0 and b0(m, 3) > 0] == [3]
    ok &= [m for m in range(2, 409) if m % 3 == 0 and m % 2 == 1 and b0(m, 1) > 0] == [3]
    ok &= b0(6, 3) < 0 and b0(9, 1) < 0 and b0(6, 1) > 0                                # six: the generations or the odd rank
    ok &= 3 + 2 == 5 and 2 ** (5 - 1) == 16
    ln2, ln3 = CH.log_bracket(Q(2)), CH.log_bracket(Q(3)); tol = Q(1, 20)
    ok &= 407 * ln2[1] + ln3[1] < CH.LN_OMEGA - tol and 410 * ln2[0] > CH.LN_OMEGA + tol
    # 27:C22 (p27065)
    R.check("E12", "[chart] the colour rank in the imported one-loop law: b₀ = (11/3)m − (2/3)·G·2^(m−2) is 29/3 and 7 at m = 3; "
            "with b₀ > 0 above three generations and the triality the rank is three, and with b₀ > 0 for one generation, the "
            "triality and the odd rank it is three; the frame has rank five and a generation sixteen states; 3·2^407 lies "
            "below Ω and 2^410 above, with ln Ω = 283.5", ok,
            f"407 ln 2 + ln 3 < {CH.show(407 * ln2[1] + ln3[1], '.2f')}, 410 ln 2 > {CH.show(410 * ln2[0], '.2f')}", kind="CHART")


# ------------------------------------------------------------------------------------------------------------
# block F: matter (27:C6, C8–C11, X8, X9, P1, P2, P4, P6, P7)
# generation.py reads one generation as the spinor of K³ ⊕ K² (F1: the matter content, which the exclusion rows P2, P6,
# P7 rest on). p8.py and p8b.py give the spinorial unification argument, the X, Y as the colour–isospin off-block and
# the proton lifetime (F3, a dimensional estimate on the chart). p9.py counts Frobenius orbits. p9b.py splits the roles
# 1 + 3 (F6, with the ladder's closure from the horizon theme: no further sector, the deciding check of P2, P6, P7) and
# orders the masses (F6c, on the measured masses). p11.py derives Ω ≡ 5 (mod 12).
@R.block("F", BLOCK["F"])
def block_F():
    """Block F — matter: F1, F2, F4–F7 EXACT; F3, F6c CHART."""
    # F1 the 16 = 1 ⊕ 5̄ ⊕ 10: sixteen Weyl fermions with ΣY = ΣY³ = 0 and Tr T₃²/Tr Q² = 3/8. The 6Y multiset equals
    #    that of the theme's even subsets read 3 + 2 (gen16, y6).
    h = Q(1, 2)
    GEN = [("Q", 3, [h, -h], Q(1, 6)), ("u^c", 3, [Q(0)], Q(-2, 3)), ("d^c", 3, [Q(0)], Q(1, 3)),
           ("L", 1, [h, -h], Q(-1, 2)), ("e^c", 1, [Q(0)], Q(1)), ("nu^c", 1, [Q(0)], Q(0))]
    nW = sum(c * len(t) for _, c, t, _ in GEN)
    sY = sum(c * len(t) * y for _, c, t, y in GEN); sY3 = sum(c * len(t) * y ** 3 for _, c, t, y in GEN)
    T3 = sum(c * sum(x * x for x in t) for _, c, t, _ in GEN); Q2 = sum(c * sum((x + y) ** 2 for x in t) for _, c, t, y in GEN)
    charges = {x + y for _, c, t, y in GEN for x in t}
    wsum = all(any(y == a * Q(-1, 3) + b * h for a in range(-3, 4) for b in range(-2, 3)) for _, _, _, y in GEN)
    six = Counter(6 * y for _, c, t, y in GEN for _ in range(c * len(t)))
    ok = nW == 16 and sY == 0 and sY3 == 0 and charges == {Q(2, 3), Q(-1, 3), Q(-2, 3), Q(1, 3), Q(0), Q(-1), Q(1)}
    ok &= T3 / Q2 == Q(3, 8) and wsum and six == Counter(I.y6(S) for S in I.gen16())
    # 27:C8 (p27020), 27:X8 (p27031)
    R.check("F1", "one generation as the spinor of K³ ⊕ K²: sixteen Weyl fermions, hypercharges weight sums of (−1/3, +1/2), "
            "charges {±2/3, ±1/3, 0, ±1}, ΣY = ΣY³ = 0, Tr T₃²/Tr Q² = 3/8: the matter content that the exclusion predictions "
            "rest on", ok, f"Tr T₃² = {T3}, Tr Q² = {Q2}")

    # F2 the spinorial argument: 1 + 5 + 10 = 16
    R.check("F2", "the generation pieces of the irreducible SO(10) spinor: 1 + 5 + 10 = 16", 1 + 5 + 10 == 16)

    # F3 [chart] the proton lifetime τ_p ~ M_X⁴/(α_GUT² m_p⁵) in years, a dimensional estimate on the declared numerals. It
    #    is 10⁴⁸ yr at the Planck scale, above row P4's bound 10⁴⁵, and 4.6 × 10³⁵ yr at 10¹⁶ GeV, above the Super-K bound 10³⁴.
    d = CF.DATA["p8"]
    tau = {M: M ** 4 / (d["alpha_GUT"] ** 2 * d["m_p"] ** 5) * d["hbar_GeV_s"] / d["year_s"] for M in d["M_X"]}
    Ms = sorted(tau)
    ok = all(tau[b] / tau[a] == (b / a) ** 4 for a, b in zip(Ms, Ms[1:])) and tau[Ms[-1]] >= 10 ** 45 and tau[Ms[0]] > 10 ** 34
    # 27:P4 (p27038)
    R.check("F3", "[chart] τ_p ∝ M_X⁴; τ_p at the Planck scale ≥ 10⁴⁵ yr (row P4's bound); τ_p at M_X = 10¹⁶ GeV above the "
            "Super-K bound 10³⁴ yr", ok, ", ".join(f"{CH.show(M, '.1e')} GeV: {CH.show(tau[M], '.1e')} yr" for M in Ms), kind="CHART")

    # F4 the X, Y as the colour–isospin off-block: dim SU(5) − dim(SU(3) × SU(2) × U(1)) = 24 − 12 = 12 = 2·(3·2)
    su5, sm, off, so10 = 5 ** 2 - 1, (3 ** 2 - 1) + (2 ** 2 - 1) + 1, 2 * (3 * 2), 10 * 9 // 2
    # 27:C9 (p27053)
    R.check("F4", "the X, Y leptoquarks are the colour–isospin off-block: 24 − 12 = 12 = the 3 × 2 off-block over K; "
            "dim SO(10) = 45; 1 + 5 + 10 = 16", su5 == 24 and sm == 12 and su5 - sm == off == 12 and so10 == 45 and 1 + 5 + 10 == 16)

    # F5 generations as Galois conjugates: the orbits of x -> x^q on F_{q^n}^× (multiplication by q on Z/(q^n − 1))
    def orbits(q, n):
        N = q ** n - 1; seen = set(); out = []
        for a in range(N):
            if a in seen: continue
            orb = []; b = a
            while b not in seen: seen.add(b); orb.append(b); b = b * q % N
            out.append(orb)
        return out
    ok = True
    for q in (2, 3):
        fo = {n: orbits(q, n) for n in (2, 3)}
        ok &= {n: max(len(o) for o in fo[n]) for n in fo} == {2: 2, 3: 3}
        ok &= all(all(n % len(o) == 0 for o in fo[n]) for n in fo)
    R.check("F5", "Frobenius orbits on F_{q^n}^× for the laboratory fields q = 2, 3: full orbits of size 2 and 3 for n = 2 and 3, "
            "every orbit size dividing the degree; the degrees 2 and 3 coprime, the labels (k mod 2, k mod 3) of the exponents k < 6 "
            "the six pairs", ok and gcd(2, 3) == 1 and len({(k % 2, k % 3) for k in range(6)}) == 6)

    # F6 the closed role ladder and its 1 + 3 split. The fifth step returns to counting: on the Subjects 13, 173,
    #    1549 the tower g^(g^j) is read with its exponent modulo p − 1, an index on the cycle, for every j (the horizon
    #    theme's tower, as 26-pnp's closure). One role is non-generative (counting, the bosonic Carrier), three are
    #    generative (the generations): no fifth interaction, no fourth generation, no further sector.
    ok = True; det = []
    for p in (13, 173, 1549):
        g, n = arith.primitive_root(p), p - 1
        closes = all(LD.tower(g, j, p)[0] == LD.tower(g, j, p)[1] for j in range(n))    # g^(g^j) = g^((g^j) mod n)
        acts = any(pow(g, j, p) >= n for j in range(n))                                   # the reduction is not vacuous
        ok &= closes and acts
        det.append(f"F_{p}: g = {g}, the tower exponent read modulo {n} for all {n} indices")
    # 27:C10 (p27022), 27:X9 (p27032), 27:P1 (p27035), 27:P2 (p27036), 27:P6 (p27040), 27:P7 (p27041)
    R.check("F6", "the closed role ladder: the fifth step returns to counting (on the Subjects 13, 173, 1549 the tower g^(g^j) is "
            "read with its exponent modulo p − 1, an index on the cycle, for every j, and the reduction is not vacuous): iterated "
            "exponentiation opens no fifth role; the count 4 = 1 + 3 (one non-generative role, the bosonic Carrier, three "
            "generative, the generations) is the realisation B6's reading of the closed ladder, not decided here", ok, "; ".join(det))

    # F6c [chart] the generations ordered by the ladder: the geometric-mean masses of the three generations from the
    #     measured quark and lepton masses, gen1 < gen2 < gen3, each step above ×40 (compared cubed, in rationals)
    d = CF.DATA["p9b"]
    pr = [d[g][0] * d[g][1] * d[g][2] for g in ("gen1", "gen2", "gen3")]
    ok = pr[0] < pr[1] < pr[2] and pr[1] / pr[0] > 40 ** 3 and pr[2] / pr[1] > 40 ** 3
    R.check("F6c", "[chart] the generations ordered as the ladder orders the roles: the geometric-mean masses from the measured "
            "quark and lepton masses satisfy gen1 < gen2 < gen3, each step above ×40", ok,
            "step ratios³ " + ", ".join(CH.show(pr[i + 1] / pr[i], ".3g") for i in range(2)), kind="CHART")

    # F7 Ω ≡ 5 (mod 12) as the CRT conjunction, on the laboratory Subjects and Carriers
    subjects, carriers = (13, 173, 1549), (233, 30089, 2408561)
    ok = {r for r in range(12) if r % 4 == 1 and r % 3 == 2} == {5}
    ok &= all(p % 4 == 1 for p in subjects) and [p for p in subjects if p % 12 == 5] == [173]
    ok &= all(c % 12 == 5 and c % 4 == 1 and (c + 1) % 3 == 0 for c in carriers)
    ok &= all(p * p < c < p * p * p for p, c in zip(subjects, carriers))
    # 27:C11 (p27023)
    R.check("F7", "5 is the unique residue mod 12 with r ≡ 1 (mod 4) and r ≡ 2 (mod 3), the residue clause Ω ≡ 5 (mod 12) as a "
            "CRT conjunction; the laboratory Carriers 233, 30089, 2408561 have this residue; the Subjects 13, 173, 1549 are "
            "≡ 1 (mod 4), 173 alone ≡ 5 (mod 12); on each pair p² < Ω < p³", ok)



# ------------------------------------------------------------------------------------------------------------
# block G: the running couplings and the mass mechanism (27:C6, P3, P5, Z1)
# p1.py runs the measured M_Z couplings at one loop with b = (41/10, −19/6, −7) (G2, on the chart), and sin²θ_W = 3/8
# where α₁ = α₂ (G1, exact). p7.py reads the seesaw scale, b–τ unification and the winding-overlap hierarchy (G3, G4, on
# the chart).
@R.block("G", BLOCK["G"])
def block_G():
    """Block G — the running couplings and the mass mechanism: G1 EXACT; G2–G4 CHART."""
    # G1 at α₁ = α₂ (GUT-normalised hypercharge, α_Y = (3/5)α₁): sin²θ_W = α_Y/(α₂ + α_Y) = (3/5)/(1 + 3/5) = 3/8
    s = Q(3, 5) / (1 + Q(3, 5))
    R.check("G1", "sin²θ_W = (3/5)/(1 + 3/5) = 3/8 exactly where α₁ = α₂", s == Q(3, 8), str(s))

    # G2 [chart] the running in rationals on the measured couplings, since π cancels from the couplings at the meeting.
    #    The α₃ near-miss is below 20 %; the chart reads the meeting scale in [10¹², 10¹⁴] GeV. The clause "3/8 runs back
    #    to the measured value" of 16 October was an identity (one-loop running is linear, so running up and back returns
    #    the input exactly) and is gone (17 October 2026).
    d = CF.DATA["p1"]; b1, b2, b3 = d["b"]
    a1, a2, a3 = Q(3, 5) * (1 - d["sin2"]) * d["ainv_em"], d["sin2"] * d["ainv_em"], 1 / d["alpha_s"]
    u = (a1 - a2) / (b1 - b2)                                                     # t₁₂/2π
    aG, a3X = a2 - b2 * u, a3 - b3 * u
    miss = abs(a3X - aG) / aG
    MX = Q(CF.unification_scale())
    ok = miss < Q(1, 5) and 10 ** 12 < MX < 10 ** 14
    # 27:P3 (p27037)
    R.check("G2", "[chart] one-loop running of the measured M_Z couplings with b = (41/10, −19/6, −7): α₁ = α₂ at M_X in "
            "[10¹², 10¹⁴] GeV, where sin²θ_W = 3/8 by the normalisation (G1); the α₃ near-miss below 20 %", ok,
            f"M_X = {CH.show(MX, '.2e')} GeV, α_GUT⁻¹ = {CH.show(aG, '.1f')}, α₃⁻¹ = {CH.show(a3X, '.1f')}, "
            f"near-miss {CH.show(100 * miss, '.0f')} %", kind="CHART")

    # G3 [chart] the seesaw m_ν = y²v²/M_R reaches 0.01–0.1 eV for M_R = 10¹⁴–10¹⁵ GeV, and m_b/m_τ lies in the band 2–3
    d = CF.DATA["p7"]
    band = [y ** 2 * d["v"] ** 2 / MR * 10 ** 9 for MR in d["M_R"][1:3] for y in d["y"]]
    ok = any(Q(1, 100) < m < Q(1, 10) for m in band) and 2 < d["m_b"] / d["m_tau"] < 3
    # 27:P5 (p27039)
    R.check("G3", "[chart] the seesaw y²v²/M_R reaches 0.01–0.1 eV for M_R = 10¹⁴–10¹⁵ GeV; m_b/m_τ = 2.35 in the b–τ band 2–3",
            ok, "m_ν (eV) = " + ", ".join(CH.show(m, ".3f") for m in band) + f"; m_b/m_τ = {CH.show(d['m_b'] / d['m_tau'], '.2f')}",
            kind="CHART")

    # G4 [chart] the winding overlap |Σ_{t<T} ζ_N^{kt}|/T (N = 60, T = 12): 1 at k = 0 and decreasing in k = 0 … 5
    ov = [Q(x) for x in CF.winding_overlaps(d["N"], d["T"])]
    ok = abs(ov[0] - 1) < Q(1, 10 ** 12) and all(ov[k] > ov[k + 1] for k in range(5))
    R.check("G4", "[chart] the winding overlap |Σζ^{kτ}|/T is 1 at k = 0 and decreases in the winding distance k = 0 … 5", ok,
            ", ".join(CH.show(x, ".3f") for x in ov), kind="CHART")


# ------------------------------------------------------------------------------------------------------------
# block H: flavour (27:X10, X11, P8, P9)
# koide.py proves the framed-rational Koide identity over the Subject 173 (p ≡ 5 mod 12), with the cube root of unity in
# F_{p²} = F_p(√−3) (H1), and reads the measured charged leptons on the chart (H2). strongcp.py shows that Hermitian mass
# matrices over the extension K = F_p[η] of the Subjects 13, 173, 1549 have their determinant in F_p, its class in K×/F_p× trivial, while [M_u, M_d] ≠ 0 (H3).
SHELLS_5MOD12 = (173,)                                                       # the laboratory Subject with p ≡ 5 (mod 12)


@R.block("H", BLOCK["H"])
def block_H():
    """Block H — flavour: H1, H3 EXACT; H2 CHART."""
    # H1 over each shell −3 is a non-residue and ω = (−1 + θ)/2 has order 3. The eigenvalues λ_k = a + bω^k + b^pω^{−k}
    #    lie in F_p, with Σλ = 3a, Σλ² = 3a² + 6N(b) and Q = 1/3 + (2/3)ρ². So ρ² = N(b)/a² = 1/2 gives Q = 2/3.
    ok = True
    for p in SHELLS_5MOD12:
        K = I.Fq2(p, 0, -3); i2, i3 = pow(2, p - 2, p), pow(3, p - 2, p)
        ok &= p % 12 == 5 and pow(p - 3, (p - 1) // 2, p) == p - 1
        om = ((-i2) % p, i2); ok &= K.pow(om, 3) == K.one and om != K.one
        oms = [K.one, om, K.mul(om, om)]
        for a in (1, 2, 7):
            for b in ((1, 1), (2, 1), (3, 2)):
                lam = []
                for k in range(3):
                    e = K.add(K.add(K.scalar(a), K.mul(b, oms[k])), K.mul(K.conj(b), oms[(-k) % 3]))
                    ok &= e[1] == 0; lam.append(e[0])
                S1, S2, nb = sum(lam) % p, sum(x * x for x in lam) % p, K.norm(b)
                ok &= S1 == 3 * a % p and S2 == (3 * a * a + 6 * nb) % p
                Qk = S2 * pow(S1 * S1 % p, p - 2, p) % p; rho2 = nb * pow(a * a % p, p - 2, p) % p
                ok &= Qk == (i3 + 2 * i3 * rho2) % p
        ok &= (i3 + 2 * i3 * i2) % p == 2 * i3 % p
    # the Parseval form on the Subjects 13 and 1549, where 3 | p − 1 and ω is on the shell: 3 Σ a_j² = â_0² + 2 â_1 â_{−1},
    # with â_k = Σ a_j ω^{−jk}; the triples (i, 7i + 3, i² + 1), i < 200, of each
    for p in (13, 1549):
        om = next(x for x in range(2, p) if (x * x + x + 1) % p == 0); ok &= pow(om, 3, p) == 1
        triples = ((i % p, (7 * i + 3) % p, (i * i + 1) % p) for i in range(200))
        for a in triples:
            h0 = sum(a) % p; h1 = sum(x * pow(om, (-j) % 3, p) for j, x in enumerate(a)) % p
            hm = sum(x * pow(om, j, p) for j, x in enumerate(a)) % p
            ok &= 3 * sum(x * x for x in a) % p == (h0 * h0 + 2 * h1 * hm) % p
    # 27:X10 (p27033)
    R.check("H1", "the framed-rational Koide identity over the Subject 173 (p ≡ 5 mod 12): Σλ = 3a, "
            "Σλ² = 3a² + 6N(b), Q = 1/3 + (2/3)ρ², and ρ² = 1/2 gives Q = 2/3 exactly; on the Subjects 13 and 1549, with ω on "
            "the shell, the Parseval form 3Σa_j² = â_0² + 2â_1â_{−1} on 200 sampled triples each", ok)

    # H2 [chart] the measured charged-lepton Q against 2/3 (10⁻⁴) and ρ² against 1/2 (10⁻³)
    Qm, r2 = CF.koide_measured()
    # 27:P8 (p27042)
    R.check("H2", "[chart] the measured charged-lepton Q = Σm/(Σ√m)² is 2/3 within 10⁻⁴ and ρ² is 1/2 within 10⁻³",
            _within(Qm, Q(2, 3), Q(1, 10 ** 4)) and _within(r2, Q(1, 2), Q(1, 1000)), f"Q = {Qm:.6f}, ρ² = {r2:.5f}", kind="CHART")

    # H3 Hermitian circulant and textured up/down mass matrices over K = F_p[η], η² the least nonsquare, on the Subjects
    #    13, 173, 1549: det ∈ F_p, det(M_u M_d) ∈ F_p, [M_u, M_d] ≠ 0; the square M = A² of a Hermitian amplitude matrix A
    #    has det M = (det A)², a nonzero square of the shell
    ok = True; n_ = 0
    for p in (13, 173, 1549):
        K = I.Fq2(p, 0, next(n for n in range(2, p) if pow(n, (p - 1) // 2, p) == p - 1))
        def herm_m(diag, up):
            return ((K.scalar(diag[0]), up[0], up[1]), (K.conj(up[0]), K.scalar(diag[1]), up[2]),
                    (K.conj(up[1]), K.conj(up[2]), K.scalar(diag[2])))
        b = (2, 1)
        Hc = herm_m((7, 7, 7), (b, K.conj(b), b))
        Hu = herm_m((3, 7, 11), ((1, 1), (2, 3), (4, 1))); Hd = herm_m((2, 5, 13), ((3, 2), (1, 4), (5, 2)))
        dc, du, dd = I.det(K, Hc), I.det(K, Hu), I.det(K, Hd)
        checks = [dc[1] == 0 and dc != K.zero, du[1] == 0 and du != K.zero, dd[1] == 0 and dd != K.zero, K.mul(du, dd)[1] == 0,
                  I.mat_mul(K, Hu, Hd) != I.mat_mul(K, Hd, Hu)]
        for A_, d_ in ((Hc, dc), (Hu, du), (Hd, dd)):
            dM = I.det(K, I.mat_mul(K, A_, A_))
            checks.append(dM == K.mul(d_, d_) and dM[1] == 0 and dM != K.zero and pow(dM[0], (p - 1) // 2, p) == 1)
        ok &= all(checks); n_ += len(checks)
    # 27:X11 (p27034), 27:P9 (p27043)
    R.check("H3", "the determinants of the mass matrices over K = F_p[η] on the Subjects 13, 173, 1549: Hermitian circulant and textured mass "
            "matrices have det ∈ F_p, nonzero (its class in K×/F_p× trivial), det(M_u M_d) ∈ F_p, and [M_u, M_d] ≠ 0; the square "
            "M = A² of a Hermitian amplitude matrix has det M = (det A)², a nonzero square of the shell", ok, f"{n_} exact checks")

    # H4 the Wilson term under orientation reversal (17 October 2026): on the 24 elements of 2T over the Gaussian rationals
    #    and on all 216 elements of SU(3, 2) over F_4, U⁻¹ = U† and Tr U⁻¹ = conj Tr U, so the plaquette term Tr U + conj Tr U
    #    is unchanged by U ↦ U⁻¹: the Wilson term is even under the inversion. 2T first: the inverse of a unit quaternion
    #    is its conjugate, the matrix trace 2a is real, so Tr U⁻¹ = Tr U = conj Tr U.
    G, _, _, _ = I.tetrahedral_quaternions()
    ok = all(I.qmul(g, I.qconj(g)) == (1, 0, 0, 0) for g in G)
    for g in G:
        M, Mi = I.su2_matrix(g), I.su2_matrix(I.qconj(g))
        trM = tuple(a + b for a, b in zip(M[0][0], M[1][1])); trMi = tuple(a + b for a, b in zip(Mi[0][0], Mi[1][1]))
        ok &= trMi == I.gauss_conj(trM) and trM[1] == 0 and I.gauss_mul(trMi, (1, 0)) == trM
    F4 = I.Fq2(2, 1, 1); su3 = I.unitary_frames(F4, 3)
    one = tuple(tuple(F4.one if i == j else F4.zero for j in range(3)) for i in range(3))
    mm = lambda X, Y: I.mat_mul(F4, X, Y); dg = lambda X: I.dagger(F4, X); tr = lambda X: I.trace(F4, X)
    re2 = lambda U: F4.add(tr(U), F4.conj(tr(U)))                                 # Tr U + conj Tr U, the Wilson term
    ok &= len(su3) == 216 and all(mm(U, dg(U)) == one and mm(dg(U), U) == one for U in su3)
    ok &= all(tr(dg(U)) == F4.conj(tr(U)) and re2(dg(U)) == re2(U) for U in su3)
    # 27:X11 (p27034), 27:P9 (p27043) — corroboration of H3's rows: the evenness of the Wilson term
    R.check("H4", "the Wilson term Tr U + conj Tr U is even under orientation reversal U → U⁻¹ = U† on the 24 elements of 2T "
            "and all 216 elements of SU(3, 2) over F_4: the Wilson term is of the class that row B11 declares", ok,
            f"{len(G)} + {len(su3)} elements")


if __name__ == "__main__":
    want = [a.upper() for a in sys.argv[1:]] or sorted(BLOCK)
    bad = [b for b in want if b not in BLOCK]
    if bad: sys.exit(f"no block {', '.join(bad)}: the blocks are {', '.join(sorted(BLOCK))}")
    for b in want: R.run_block(b)
    sys.exit(0 if R.summary(write=False, expect=list(LEDGER) if want == sorted(BLOCK) else None) else 1)
