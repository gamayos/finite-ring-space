"""p46_yangmills — the ledger file of 46-yangmills (Phases 1–2 of the paper home, 7 November 2026; the repair of 8 November).

"Yang–Mills and the Mass Gap over Finite Holographic Substrate" (Akhtman, in preparation; 46-yangmills-20261107/reports/
study.md). The paper's predicate ledger is drafted in 46-yangmills-20261107/reports/ledger-draft-20261107.md; until the
manuscript's ledger appendix exists and the site writes docs/46-yangmills/46-yangmills-ledger.json, the table of keys below
is written by hand from the draft and this file carries no generated-table markers, so ci/make_ledgers.py leaves it alone
(Phase 3 adds the markers and lets the tool write the table, the certificates and the notebook).

The checks are EXACT or CHART, one kind per check. An EXACT check decides by finite-field, integer or rational arithmetic:
the norm-one torus of F_p[√ν] on the laboratory Subjects and its eigenvalues, the split torus's fixed lines,
the arithmetic of the centre's order formula gcd(3, q + 1) and the centre of SU(3, F_2) by elements, the residue series over
F_4 by linear algebra on SU(3, F_2) (the hadrons theme's group) and by the singlet multiplicities, the finite frame's own
moments over F_4, the Casimirs and b₀ as rationals, the discrete logarithm on the shells, the plaquette coefficients c₃ and
c₈ to order β⁷ with rational coefficients and their ratio to that order; no float decides anything. A CHART check reads
a measured or lattice number, declared as a rational with its error in frc/chart_yangmills.py, against the frame's exact
value, runs the chart's one-loop law with its logarithm, reads the tensions as logarithms of the exact series, or runs the
chart's relativistic wrap operator on a grid; its label carries "[chart]".

The Lean side: the theorems of the yangmills theme (lean/FrcCore/Theme/YangMills.lean) — the no-shell-root theorem for the
norm-one elements of the extension, the arithmetic of the centre's order formula on the sweep, the singlet-multiplicity
identities behind the glueball and the adjoint wrap (glueball_singlet, adjoint_two_sheets), the Casimir and b₀ rationals,
the drive exponent's existence and uniqueness from the frame — over the extension, frame and hadrons themes. The key file and the certificate follow the
ledger's JSON in Phase 3.

The laboratory instances are the pairs (13, 233), (173, 30089) and (1549, 2408561), with a sweep over the shells p = 4κ + 1
below 200 (the author's ruling of 7 November 2026). The colour frame is the Subject's (the author's ruling of 8 November 2026):
SU(3) over the Subject's quadratic extension F_p[√ν], with the full centre on the Subjects p ≡ 5 (mod 12); the Carrier has no
frame and no extension, so no torus or group is formed over F_Ω. No numeral above Ω ∼ 10¹²³ is formed.

    python3 -m frc.ledgers.p46_yangmills         every block, the census; exit 1 if a check fails (≈ 25 s: the F_4 linear algebra 12 s, the wrap spectrum 5 s)
    python3 -m frc.ledgers.p46_yangmills A       one block (A to F)
    from frc.ledgers.p46_yangmills import R; R.predicate("46:C1")    one predicate: its blocks run once per session

Blocks:  A  the registrations of the colour frame: the tori, the centre, the residue series   (46:C1, C2, C3, X1, X2)
         B  the Casimirs and the window rational                                                 (46:C4, C5, X4)
         C  the drive exponent                                                                   (46:C6)
         D  the tension's coefficient to order β⁷                                                (46:C7)
         E  the chart: LEP, the one-loop run, the lattice anchors                                (46:P1, P2, X4, C8)
         F  the minimal wrap (Phase 2, D5): the adjoint wrap, the operator family, the chart's tension ratio (46:C9, C12)
         G  the two routes of the former task T01, both obstructed (8 November 2026)                   (46:C10, C11)

Checks: 21, of them 13 EXACT and 8 CHART (E1–E3, F2–F4, G1, G2).
"""
import sys
from fractions import Fraction as Q

from frc.registry import Registry
from frc import arith as A
from frc import yangmills as Y
from frc import chart_yangmills as CY

PAPER = "46-yangmills"
# hand-written from reports/ledger-draft-20261107.md (Phases 1–2, the repair and the audit of 8 November, 34 rows); the generated table replaces it in Phase 3
KEYS = {"A1": "p46001", "A2": "p46002", "A3": "p46003", "A4": "p46004", "A5": "p46005", "A6": "p46006", "A7": "p46031", "A8": "p46032",
        "A9": "p46034", "A10": "p46035",                                       # the audit of 8 November 2026: Steinberg's restriction theorem, Casimir scaling
        "B1": "p46007", "B2": "p46008", "B3": "p46009",
        "C1": "p46010", "C2": "p46011", "C3": "p46012", "C4": "p46013", "C5": "p46014", "C6": "p46015", "C7": "p46016", "C8": "p46017",
        "C9": "p46030",
        "X1": "p46018", "X2": "p46019", "X3": "p46020", "X4": "p46021", "X5": "p46022",
        "C10": "p46037", "C11": "p46038", "C12": "p46036", "A11": "p46039",   # the push on T01 (8 November 2026): the two obstructions, the family's miss, Münster's series
        "A12": "p46040", "C13": "p46041", "T04": "p46042",                    # the push on T02 (8 November 2026): the Hughes–Nielsen form, the two rationals, the derivation of the form
        "P3": "p46043",                                                       # T03 resolved (8 November 2026): the radial ratio of the operator form staked
        "P1": "p46023", "P2": "p46024", "Z1": "p46026",                       # p46027 (V1) retired 8 November 2026: block V deprecated
        }                                                                     # p46025 (Y1), p46028 (T01), p46029 (T02), p46033 (T03) retired 8 November 2026: Y1 withdrawn, T01 closed by obstruction, T02 closed by C13, T03 by P3
LEAN = {}                       # written by make_predicates/make_ledgers in Phase 3

LEAN_ONLY = ()

LEDGER = {
    "A1": "46:C1, 46:X1, 46:X2", "A2": "46:C1", "A3": "46:C2", "A4": "46:C3, 46:X2", "A5": "46:C3", "A6": "46:C2",
    "B1": "46:C4, 46:X4", "B2": "46:C5", "B3": "46:C13",
    "C1": "46:C6",
    "D1": "46:C7", "D2": "46:C7",
    "E1": "46:P1, 46:X4", "E2": "46:P2", "E3": "46:C8",
    "F1": "46:C9", "F2": "46:C12", "F3": "46:C9", "F4": "46:P3",
    "G1": "46:C10", "G2": "46:C11",
}

BLOCK = {"A": "the registrations of the colour frame: the non-split torus without a fixed line, the split torus with two, the centre Z_3 on the Subjects p ≡ 5 (mod 12), the residue series closed by the glueball",
         "B": "the Casimirs of the frame, the window rational b₀ and the two rationals of the one-loop coefficient",
         "C": "the drive exponent: every winding rate is one power of the drive",
         "D": "the tension's coefficient: the single-plaquette coefficient to order β⁷ with rational coefficients",
         "E": "the chart: the LEP colour factors, the one-loop run between laboratory scales, the lattice anchors",
         "F": "the minimal wrap: the adjoint plaquette coefficient is the square of the fundamental one up to the factor 9/8, with the ratio computed to order β⁴; the chart's operator family against the three lattice determinations; the chart's tension ratio; the operator form's radial ratio against the lattice and the nucleon",
         "G": "the two routes of the former task T01: the short-range term collapses at the declared coupling and is the cutoff's number with the running one; the plaquette channel's series gives 4.8 or more where its orders agree"}

PREDICATES = {"46:C1": "A1", "46:X1": "A1", "46:X2": "A1", "46:C2": "A3", "46:C3": "A4",
              "46:C4": "B1", "46:X4": "B1", "46:C5": "B2", "46:C13": "B3", "46:C6": "C1", "46:C7": "D1",
              "46:P1": "E1", "46:P2": "E2", "46:C8": "E3", "46:C9": "F1", "46:C12": "F2", "46:P3": "F4", "46:C10": "G1", "46:C11": "G2"}

R = Registry("46", "yangmills", LEDGER, PREDICATES, sources=[__file__])

LAB = Y.LAB_PAIRS
SWEEP = Y.shells_below(200)


def _nonsquare(p):
    return next(x for x in range(2, p) if A.legendre(x, p) == -1)


# ------------------------------------------------------------------------------------------------------------
@R.block("A", BLOCK["A"])
def block_A():
    """Block A — the registrations of the colour frame."""
    # A1 the non-split torus C_{p+1} of F_p[√ν] on the laboratory Subjects: p + 1 norm-one elements, exactly two
    #    of them (the scalars ±1) with an eigenvalue in F_p; every other element's characteristic polynomial x² − 2a x + 1 has
    #    the nonsquare discriminant 4ν b², so no line of F_p² is fixed by the torus: the gluon, the residue 0, is never
    #    registered alone
    shells = [p for p, _ in LAB]                                               # the Subjects only: the frame is the Subject's (8 November 2026)
    res = {}
    ok = True
    for p in shells:
        n, k, ev = Y.fixed_lines_nonsplit(p, _nonsquare(p))
        res[p] = (n, k); ok &= n == p + 1 and k == 2 and sorted(a for a, b in ev) == [1, p - 1] and all(b == 0 for _, b in ev)
    for p in SWEEP:
        n, k, _ = Y.fixed_lines_nonsplit(p, _nonsquare(p)); ok &= n == p + 1 and k == 2
    # 46:C1 (p46010), 46:X1 (p46018), 46:X2 (p46019)
    R.check("A1", "the non-split torus has no shell eigenvalue: on the Subjects 13, 173, 1549 "
            "and the 21 shells below 200 the norm-one torus of F_p[√ν] has p + 1 elements, of which exactly the two scalars ±1 "
            "have an eigenvalue in F_p; every non-scalar element's characteristic polynomial x² − 2ax + 1 has the nonsquare "
            "discriminant 4νb², so no line of F_p² is mapped to itself by every element of the torus: the gluon's residue is 0", ok,
            ", ".join(f"{p}: {n} elements, {k} with an eigenvalue" for p, (n, k) in res.items()))

    # A2 the split torus diag(g, g⁻¹), g a generator, fixes exactly the two coordinate lines of P¹(F_p): the photon's residue 2
    ok = True; det = {}
    for p in [q for q, _ in LAB] + SWEEP:
        fl = Y.fixed_lines_split(p, A.primitive_root(p)); det[p] = len(fl); ok &= sorted(fl) == [(0, 1), (1, 0)]
    R.check("A2", "the split torus fixes exactly two lines: on the laboratory Subjects and the sweep, diag(g, g⁻¹) with g the drive "
            "fixes [1 : 0] and [0 : 1] and no other point of P¹(F_p) (g² ≠ 1), the two F_p-fixed lines that are the photon's two "
            "helicities, residue 2 (12-primer §6), against the non-split torus's none", ok, f"fixed lines {sorted(set(det.values()))} on {len(det)} shells")

    # A3 the centre of SU(3, F_q) is Z_{gcd(3, q+1)}: Z_3 exactly when q ≡ 2 (mod 3), with q ≡ 1 (mod 4) that is q ≡ 5 (mod 12);
    #    the colour frame is the Subject's (the ruling of 8 November 2026): the Subject 173 carries the centre, 13 and 1549 (q ≡ 1 mod 12) do not
    orders = {p: Y.centre_order(p) for p, _ in LAB}
    ok = orders[13] == 1 and orders[173] == 3 and orders[1549] == 1 and Y.admissible(173) and not Y.admissible(13) and not Y.admissible(1549)
    ok &= all((Y.centre_order(p) == 3) == (p % 3 == 2) == Y.admissible(p) for p in SWEEP)
    ok &= [p for p in SWEEP if Y.admissible(p)] == [5, 17, 29, 41, 53, 89, 101, 113, 137, 149, 173, 197]
    # 46:C2 (p46011)
    R.check("A3", "the triality centre: |Z(SU(3, F_q))| = gcd(3, q + 1), Z_3 exactly on q ≡ 2 (mod 3), hence on q ≡ 5 (mod 12) for a "
            "shell; of the Subjects 173 carries it (173 ≡ 5) and 13, 1549 do not (≡ 1 mod 12); 12 of the 21 shells below 200 carry it: "
            "the colour frame is the Subject's, and these are its admissible instances", ok, f"centre orders {orders}")

    # A4 the residue series over F_4 on SU(3, F_2): no nonzero traceless matrix fixed by the adjoint action (gluon 0), det the one
    #    invariant of Λ³ (baryon 1), the commutant of the fundamental one-dimensional (meson 1), the commutant of the adjoint
    #    one-dimensional (glueball 1: the singlet of 8 ⊗ 8 once)
    F, G = Y.H.colour_group()
    series, content = Y.residue_series(F, G)
    ok = series == dict(gluon=0, baryon=1, meson=1, glueball=1, fundamental_commutant=1) and content == (1, 0, 0, 1) and len(G) == 216
    # 46:C3 (p46012)
    R.check("A4", "the residue series closes with the glueball, over F_4 on the 216 elements of SU(3, F_2): the adjoint action on the "
            "eight traceless matrices fixes no nonzero vector (gluon 0), the determinant is the one invariant of Λ³ (baryon 1), the "
            "commutant of the fundamental is the scalars (meson 1, the Hermitian contraction), and the commutant of the adjoint is "
            "one-dimensional (glueball 1, the singlet of 8 ⊗ 8 once): photon 2, gluon 0, baryon 1, meson 1, glueball 1", ok,
            f"{series}, content {content}")

    # A5 the same counts by the Weyl constant terms of SU(3): E[|χ|²] − 1 = 0, E[χ³] = 1, E[|χ|²] = 1, E[|χ|⁴] − 2E[|χ|²] + 1 = 1
    w, E = Y.weyl_residues()
    ok = w == dict(gluon=0, baryon=1, meson=1, glueball=1) and E == {(1, 1): 1, (3, 0): 1, (2, 2): 2}
    R.check("A5", "the residue series by the Weyl constant terms of SU(3): the adjoint has no invariant (E[χχ̄] − 1 = 0), 3 ⊗ 3 ⊗ 3 one "
            "singlet (E[χ³] = 1), 3 ⊗ 3̄ one (E[χχ̄] = 1), 8 ⊗ 8 one (E[χ²χ̄²] − 2E[χχ̄] + 1 = 2 − 2 + 1 = 1): the finite-field counts and "
            "the singlet multiplicities of the compact reading agree", ok, f"moments {E}")

    # A6 the centre by elements: the three elements of the 216-element SU(3, F_2) commuting with every element are the scalars of
    #    norm one, gcd(3, 2 + 1) = 3 of them — the one enumerable instance of 27-fields Proposition su3, which A3 only evaluates
    F, G = Y.H.colour_group()
    Z = Y.H.centre(F, G)
    ok = len(Z) == 3 == Y.centre_order(2) and sorted(Z) == sorted(Y.H.colour_scalars(F))
    R.check("A6", "the centre of SU(3, F_2) by elements: exactly three of the 216 elements commute with every element, the scalars "
            "x·I with x³ = 1 — gcd(3, 2 + 1) = 3, the order formula of 27-fields Proposition su3 at its one enumerable instance", ok,
            f"|Z| = {len(Z)}")


# ------------------------------------------------------------------------------------------------------------
@R.block("B", BLOCK["B"])
def block_B():
    """Block B — the Casimirs and b₀."""
    c = Y.casimirs(3)
    ok = c == dict(C_F=Q(4, 3), C_A=Q(3), T_F=Q(1, 2), ratio=Q(9, 4))
    cf, sumTT, sumll, per_pair = Y.H.colour_factor(3)
    ok &= cf == Q(4, 3) and sumll == -8 and per_pair == Q(-8, 3)
    # 46:C4 (p46013), 46:X4 (p46021)
    R.check("B1", "the Casimirs of the colour frame: C_F = (N² − 1)/2N = 4/3, C_A = N = 3, T_F = 1/2, C_A/C_F = 9/4, and the colour "
            "factor of the singlet Σ λ·λ = −8 (−8/3 per pair; 35-hadrons C4) — exact rationals, the quantities LEP measured", ok, f"{c}")

    vals = {nf: Y.b0(nf) for nf in range(0, 17)}
    ok = vals[3] == 9 and vals[4] == Q(25, 3) and vals[5] == Q(23, 3) and vals[6] == 7
    ok &= all(vals[nf] > 0 for nf in range(0, 17)) and Y.b0(17) < 0 and all(vals[nf] == 11 - Q(2 * nf, 3) for nf in vals)
    # 46:C5 (p46014)
    R.check("B2", "the window rational b₀ = (11/3) C_A − (4/3) T_F n_f = 11 − 2n_f/3: 9, 25/3, 23/3, 7 for n_f = 3, 4, 5, 6, positive "
            "for every n_f ≤ 16 (asymptotic freedom's sign for the matter content n_f ≤ 16, 27-fields Proposition af) and negative from 17",
            ok, ", ".join(f"n_f={nf}: {vals[nf]}" for nf in (3, 4, 5, 6)))

    # B3 the two rationals of the one-loop coefficient (the push on T02, 8 November 2026). Hughes–Nielsen: b₀ = Σ (−1)^{2s}[(2s)² − 1/3] T(R)
    #    over the species, one complex scalar, one Weyl fermion, one real vector each once (46:A12, imported). The spin term (2s)² = −2 Tr(J₁₂²)
    #    with J₁₂ = e₁₂ − e₂₁ on the vector and (i/2)σ₃ on the Weyl spinor; the charge term 1/3 the leading Faulhaber coefficient of the
    #    scalar loop's midpoint sum 3 Σ_{k<N} (N − 2k − 1)² = N(N² − 1), whose complete cycle N = p vanishes on the shell
    spin = {"scalar": Q(0), "Weyl": -2 * Q(2 * (Q(1, 2) ** 2) * -1), "vector": -2 * Q(2 * -1)}            # −2 Tr(J²): J² = −1/4·I₂ on the spinor, diag(−1, −1, 0, 0) on the vector
    def species_sum(nf, ns=0): return 3 * (spin["vector"] - Q(1, 3)) - nf * (spin["Weyl"] - Q(1, 3)) - ns * Q(1, 2) * (spin["scalar"] - Q(1, 3))
    def faul(N): return sum((N - 2 * k - 1) ** 2 for k in range(N))
    ok = spin == {"scalar": 0, "Weyl": 1, "vector": 4} and all(species_sum(nf) == Y.b0(nf) for nf in range(0, 17))
    ok &= all(3 * faul(N) == N * (N * N - 1) for N in range(1, 3000))
    for p in (13, 173, 1549):
        inv3 = pow(3, -1, p)
        ok &= faul(p) % p == 0 and all(faul(N) % p == (N * (N * N - 1) * inv3) % p for N in range(1, min(p, 400)))
    # 46:C13 (p46041)
    R.check("B3", "the two rationals of the one-loop coefficient are the frame's: the spin term (2s)² = −2 Tr(J₁₂²) is 0, 1, 4 on the scalar, the "
            "Weyl spinor and the vector; the charge term 1/3 is the leading Faulhaber coefficient of the scalar loop's midpoint sum, "
            "3 Σ_{k<N} (N − 2k − 1)² = N(N² − 1) for every N (checked to 3000, and as residues on 13, 173, 1549), whose complete cycle N = p "
            "vanishes on the shell; the species sum of Hughes–Nielsen with C_A = 3, T_F = 1/2 is 11 − 2n_f/3, the window rational of C5", ok,
            f"spin terms {dict((k, str(v)) for k, v in spin.items())}; Σ_{{k<10}} = {faul(10)} = 10·99/3; Σ at N = p ≡ 0 on 13, 173, 1549; "
            + ", ".join(f"n_f={nf}: {species_sum(nf)}" for nf in (0, 3, 6)))


# ------------------------------------------------------------------------------------------------------------
@R.block("C", BLOCK["C"])
def block_C():
    """Block C — the drive exponent."""
    ok = True; gens = {}
    for p in [q for q, _ in LAB] + SWEEP:
        u, g = Y.drive_exponents_unique(p); ok &= u; gens[p] = g
    # the exponent of a product adds: g^(m+n) — the chart's ln(μ₁μ₂) = ln μ₁ + ln μ₂, on the Subject 173
    p, g = 173, gens[173]
    ok &= all((Y.drive_exponent(p, g, w1) + Y.drive_exponent(p, g, w2)) % (p - 1) == Y.drive_exponent(p, g, w1 * w2 % p)
              for w1 in range(1, 40) for w2 in range(1, 40))
    # 46:C6 (p46015)
    R.check("C1", "the drive exponent: on the Subjects 13, 173, 1549 and the 21 shells below 200 the powers g⁰ … g^{p−2} of the drive "
            "are a permutation of the nonzero residues, so every winding rate w has exactly one exponent n < p − 1 with gⁿ = w, and "
            "the exponent of a product is the sum of the exponents (mod p − 1) — the discrete logarithm of 26-pnp on the shells",
            ok, f"generators {dict((p, gens[p]) for p, _ in LAB)}")


# ------------------------------------------------------------------------------------------------------------
@R.block("D", BLOCK["D"])
def block_D():
    """Block D — the plaquette coefficient."""
    s3 = Y.c1_series(3, 8)
    ok = s3 == [Q(0), Q(1, 18), Q(1, 216), Q(0), Q(-5, 93312), Q(-1, 186624), Q(7, 33592320), Q(59, 604661760)]
    # 46:C7 (p46016)
    R.check("D1", "the tension's coefficient to order β⁷: the fundamental plaquette coefficient of SU(3) with the real Wilson action, "
            "c₃(β) = β/18 + β²/216 + 0·β³ − 5β⁴/93312 − β⁵/186624 + 7β⁶/33592320 + 59β⁷/604661760 modulo β⁸, every coefficient a rational built from "
            "the singlet multiplicities of the tensor powers of the triplet (the constant terms of the Weyl character polynomial; the "
            "frame's own multiplicities agree in the degrees that enter through β³, block F); 27-fields C7's β/18 + β²/216 continued", ok,
            ", ".join(str(c) for c in s3[1:]))

    s2 = Y.c1_series(2, 7); s2t, tr = Y.c1_series_2T(7)
    ok = s2 == [Q(0), Q(1, 4), Q(0), Q(-1, 96), Q(0), Q(1, 1536), Q(0)] and s2t[:5] == s2[:5] and s2t[5] == Q(1, 1280)
    ok &= tr == {2: 1, -2: 1, 0: 6, 1: 8, -1: 8} and s2t[5] - s2[5] == Q(1, 7680)
    R.check("D2", "the exact finite instance: 2T = SU(2, F_3) from its 24 unit quaternions (traces 2, −2 once, 0 six times, ±1 eight times) "
            "gives the fundamental coefficient β/4 − β³/96 + β⁵/1280 + …, against the multiplicity series of SU(2), β/4 − β³/96 + β⁵/1536 + …: the same "
            "coefficients through β³, the first difference β⁵/7680 (27-fields Theorem corr2T)", ok, f"2T {[str(c) for c in s2t[1:6]]}")


# ------------------------------------------------------------------------------------------------------------
@R.block("E", BLOCK["E"])
def block_E():
    """Block E — the chart confrontations."""
    c = Y.casimirs(3)
    ok = CY.within(c["C_A"], *CY.LEP["C_A"]) and CY.within(c["C_F"], *CY.LEP["C_F"]) and CY.within(c["ratio"], *CY.LEP["ratio"])
    ok &= not CY.within(0, *CY.LEP["C_A"]) and not CY.within(1, *CY.LEP["C_F"])          # the abelian alternative excluded
    # 46:P1 (p46023)
    R.check("E1", "[chart] the colour factors against LEP: C_A = 3 within 2.89 ± 0.21, C_F = 4/3 within 1.30 ± 0.09, C_A/C_F = 9/4 "
            "within 2.22 ± 0.11 (one standard deviation each); the abelian values C_A = 0, C_F = 1 lie outside — the frame's Casimirs "
            "are what the four-jet angular correlations measured", ok, f"LEP {CY.LEP['C_A'][0]}±{CY.LEP['C_A'][1]}, {CY.LEP['C_F'][0]}±{CY.LEP['C_F'][1]}", kind="CHART")

    r = CY.run_to_tau(); r2 = CY.run_to_tau_two_loop()
    a_t, a_b = Q(repr(r["alpha_mtau"])), Q(repr(r["alpha_mb"]))
    a_t2 = Q(repr(r2["alpha_mtau"]))
    m, dm = CY.ALPHA_S["mtau"]
    ok = Q("0.27") < a_t < Q("0.29") and Q("0.21") < a_b < Q("0.22") and a_t < m          # one loop lies below the measured value by the known higher orders
    ok &= abs(a_t - m) < Q("0.05") and len(r["efolds"]) == 2 and Q("3.9") < Q(repr(sum(r["efolds"]))) < Q("4.0")
    ok &= abs(a_t2 - m) < dm                                                                  # the imported two-loop term closes the gap
    # 46:P2 (p46024)
    R.check("E2", "[chart] the one-loop run between laboratory scales: from α_s(M_Z) = 0.1180 the law 1/α(μ) = 1/α(μ₀) + (b₀/2π) ln(μ/μ₀) "
            "with the thresholds n_f = 5 to m_b and 4 to m_τ gives α_s(m_b) = 0.212 and α_s(m_τ) = 0.279 against the τ-decay 0.312 ± 0.015 "
            "(2.2 standard deviations below); with the imported two-loop coefficient b₁ = 102 − 38n_f/3 the run gives α_s(m_τ) = 0.313, "
            "within one standard deviation; 3.94 e-folds from M_Z to m_τ", ok,
            f"α_s(m_b) = {CY.fmt(a_b, 4)}, α_s(m_τ) = {CY.fmt(a_t, 4)} (one loop), {CY.fmt(a_t2, 4)} (two loops), e-folds {[CY.fmt(e, 3) for e in r['efolds']]}", kind="CHART")

    det = CY.m0pp_determinations(); t, pm = CY.glueball_ladder()
    (v, dv), (r, dr), (d, dd) = det["via_Tc"], det["via_r0"], det["direct"]
    ok = Q("3.64") < v < Q("3.76") and dv < Q("0.07") and Q("3.6") < r < Q("3.66") and d == Q("3.405")
    ok &= Q("1.38") < t < Q("1.40") and Q("1.50") < pm < Q("1.51") and (v - d) > 3 * (dv + dd)      # the spread exceeds the quoted errors
    # 46:C8 (p46017)
    R.check("E3", "[chart] the lattice anchors of the pure-gauge sector, declared for the minimal-wrap row: m(0⁺⁺)/√σ by two routes — the r₀ "
            "route with two inputs, (m/T_c)(T_c/√σ) = 5.73(9) × 0.6462(30) = 3.70(6) (Hasenbusch–Necco's r₀m average through T_c r₀ = 0.7498) "
            "and r₀m/r₀√σ = 4.21(11)/1.160(6) = 3.63(10) (Morningstar–Peardon), and the direct continuum extrapolation 3.405(21) — a spread "
            "of 9 %, beyond the quoted errors; the ladder m(2⁺⁺)/m(0⁺⁺) = 1.39, m(0⁻⁺)/m(0⁺⁺) = 1.50; T_c/√σ = 0.6462(30) (SU(3)), "
            "0.7091(36) (SU(2)) — the targets λ_gb must meet, none a result of this ledger", ok,
            f"m(0⁺⁺)/√σ = {CY.fmt(v)}({CY.fmt(dv, 2)}), {CY.fmt(r)}({CY.fmt(dr, 2)}), {CY.fmt(d)}({CY.fmt(dd)}); ladder {CY.fmt(t)}, {CY.fmt(pm)}", kind="CHART")


# ------------------------------------------------------------------------------------------------------------
@R.block("F", BLOCK["F"])
def block_F():
    """Block F — the minimal wrap (Phase 2, decision D5; the repair of 8 November): the exact adjoint identity, the chart's
    operator family against the three lattice determinations, and the chart's tension ratio."""
    # F1 the adjoint plaquette coefficient c₈ = β²/288 + β³/2592 + 0·β⁴ − β⁵/186624 + … and the exact ratio c₈/c₃² = (9/8)(1 − β/18 +
    #    β²/432 + β³/2592 + …): the β¹ coefficient of c₈ vanishes (no singlet in 8 ⊗ 3 or 8 ⊗ 3̄) and its β² coefficient is (1/2)/(18 · 8)
    #    — the adjoint wrap is two fundamental wraps up to the factor 9/8, with the ratio computed to order β⁴; the two multiplicity identities
    #    behind it hold on the finite frame itself: the fixed vectors of 3^{⊗a} ⊗ 3̄^{⊗b} over F_4 under SU(3, F_2), a + b ≤ 4, equal
    #    the compact multiplicities (27-fields Lemma charlift at its enumerable instance)
    c8 = Y.c_adj_series(8); ratio = Y.adjoint_over_fundamental_squared(5)
    ok = c8[:6] == [Q(0), Q(0), Q(1, 288), Q(1, 2592), Q(0), Q(-1, 186624)]
    ok &= ratio == [Q(9, 8), Q(-1, 16), Q(1, 384), Q(1, 2304), Q(7, 829440)]
    ok &= [x / Q(9, 8) for x in ratio[:4]] == [Q(1), Q(-1, 18), Q(1, 432), Q(1, 2592)]
    m = Y.frame_moments_f4(degree=4)
    ok &= all(fin == cpt for fin, cpt in m.values())
    E = lambda a, b: m[(a, b)][0]
    ok &= E(2, 1) + E(1, 2) - E(1, 0) - E(0, 1) == 0                                      # the β¹ coefficient of c₈ on the frame
    ok &= E(3, 1) + 2 * E(2, 2) + E(1, 3) - E(2, 0) - 2 * E(1, 1) - E(0, 2) == 2        # 4 · E[(χχ̄ − 1)(Re χ)²] = 2 on the frame
    # 46:C9 (p46030)
    R.check("F1", "the adjoint wrap: the adjoint plaquette coefficient c₈(β) = β²/288 + β³/2592 − β⁵/186624 + … has no β¹ term (no singlet "
            "in 8 ⊗ 3 or 8 ⊗ 3̄), and c₈/c₃² = (9/8)(1 − β/18 + β²/432 + β³/2592 + …) to order β⁴: two fundamental wraps at leading order "
            "up to the factor 9/8; the two multiplicity identities behind the leading terms hold on the enumerable instance SU(3, F_2) "
            "over F_4 by enumeration, and every moment of the instance of degree ≤ 4 equals its compact reading", ok,
            f"c₈ {[str(c) for c in c8[2:6]]}, c₈/c₃² {[str(c) for c in ratio[:4]]}, frame moments {len(m)} agree")

    # F2 the chart's operator family of D5 against the three lattice determinations: E₀(a|p| + ϰr) = √(aϰ)·2.232 (the chart operator's
    #    dilation symmetry, which the grid reproduces); a ∈ {1, 2} (35-hadrons' one-body form; one |p| per constituent — both the chart's
    #    kinematics), ϰ ∈ {1, 2, 9/4}; no member inside any determination's error; the ϰ-free radial ratio E₁/E₀ = 1.49 against the
    #    lattice 0⁺⁺*/0⁺⁺ = 1.54(11); the effective tension each determination would need, 2.75 / 2.64 / 2.33 (a = 1) or 1.38 / 1.32 /
    #    1.16 (a = 2), none a frame value
    spec = CY.wrap_spectrum(1, 1, 3); f = CY.wrap_family(spec)
    E0 = Q(repr(spec[0]))
    ok = Q("2.231") < E0 < Q("2.233") and not any(any(row["inside"].values()) for row in f["table"])
    e22 = next(row["E0"] for row in f["table"] if row["a"] == 2 and row["kappa"] == 2)
    e19 = next(row for row in f["table"] if row["a"] == 1 and row["kappa"] == Q(9, 4))
    ok &= Q("4.46") < Q(repr(e22)) < Q("4.47") and Q("3.34") < Q(repr(e19["E0"])) < Q("3.35")
    ok &= Q("-0.02") < Q(repr(e19["off"]["direct"])) < Q("-0.015") and Q("-0.10") < Q(repr(e19["off"]["via_Tc"])) < Q("-0.09")
    r1, r2 = (Q(repr(x)) for x in f["ratios"]); rl, drl = (Q(repr(x)) for x in f["lattice_radial"])
    ok &= Q("1.49") < r1 < Q("1.493") and abs(r1 - rl) < drl
    ke = f["kappa_eff"]; ok &= Q("2.7") < Q(repr(ke["via_Tc"][1])) < Q("2.8") and Q("2.3") < Q(repr(ke["direct"][1])) < Q("2.35")
    d21 = Q(repr(CY.wrap_spectrum(2, 1, 1)[0]))                                          # the dilation symmetry on the grid, off the identity pair:
    ok &= abs(d21 * d21 - 2 * E0 * E0) < Q("0.01")                                       # E₀(2|p| + r)² = 2 E₀(|p| + r)², in exact rationals
    # 46:C12 (p46036)
    R.check("F2", "[chart] the chart's wrap-operator family against the lattice: E₀(a|p| + ϰr) = √(aϰ)·2.232 (the dilation symmetry of the "
            "chart operator, reproduced on the grid to 10⁻³), a ∈ {1, 2}, ϰ ∈ {1, 2, 9/4}: 2.232, 3.157, 3.348, 3.157, 4.464, 4.735 — none "
            "inside the error of any determination, 3.70(6), 3.63(10), 3.405(21); the nearest, one-body with Casimir scaling, lies 1.7 % "
            "below the direct value and 10 % below the r₀ route's upper input; the two-body members with ϰ = 2, 9/4 lie 20–40 % above every "
            "determination; the ϰ-free radial ratio E₁/E₀ = 1.49 meets the lattice 0⁺⁺*/0⁺⁺ = 1.54(11); the effective tension each "
            "determination needs (2.75, 2.64, 2.33 one-body) is no frame value", ok,
            f"E = {[CY.fmt(e, 4) for e in spec]}, family {[CY.fmt(row['E0']) for row in f['table']]}, E₁/E₀ = {CY.fmt(r1, 4)} vs "
            f"{CY.fmt(rl)} ± {CY.fmt(drl)}, ϰ_eff(a=1) {', '.join(CY.fmt(ke[k][1]) for k in ('via_Tc', 'via_r0', 'direct'))}", kind="CHART")

    # F3 the chart's tension ratio: σ₈/σ₃ = ln c₈ / ln c₃ at real β in the regime β ≪ 1 lies between 1.97 and 2.02 for 0.1 ≤ β ≤ 3 and
    #    equals 2 at no coupling of the range — the chart reading of F1's exact ratio; the logarithm belongs here, not in F1
    vals = {b: Q(repr(v)) for b, v in CY.adjoint_ratio_table().items()}                  # the chart tier forms the floats
    ok = all(Q("1.97") < v < Q("2.02") for v in vals.values()) and all(v != 2 for v in vals.values())
    ok &= vals["0.5"] < vals["1"] < vals["2"] < vals["3"] and vals["0.1"] > vals["0.5"]
    R.check("F3", "[chart] the chart's tension ratio σ₈/σ₃ = ln c₈(β)/ln c₃(β), read on the computed terms at real β = 0.1, 0.5, 1, 2, 3 "
            "(the first two inside the regime β ≪ 1): 1.978, 1.975, 1.977, 1.993, 2.019 — within 2 % of two fundamental wraps and equal to "
            "2 at none of the five; the chart's reading of F1's ratio (9/8)(1 − β/18 + …)", ok,
            ", ".join(f"β={b}: {CY.fmt(v, 4)}" for b, v in vals.items()), kind="CHART")

    # F4 the radial ratio of the operator form (T03 resolved, 8 November 2026): E₁/E₀ and E₂/E₀ of a|p| + ϰr are free of a and ϰ (the dilation
    #    symmetry); E₁/E₀ = 1.49 against the lattice 0⁺⁺*/0⁺⁺ = 1.54(11) (Morningstar–Peardon, r₀ masses) and the nucleon's N(1440)/N(939) = 1.53;
    #    the nonrelativistic ladder p²/2 + r has the Airy ratio a₂/a₁ = 4.088/2.338 = 1.75, outside the lattice bracket
    spec1 = CY.wrap_spectrum(1, 1, 3); spec2 = CY.wrap_spectrum(2, Q(9, 4), 3)
    q1 = Q(repr(spec1[1])) / Q(repr(spec1[0])); q2 = Q(repr(spec1[2])) / Q(repr(spec1[0])); q1b = Q(repr(spec2[1])) / Q(repr(spec2[0]))
    airy = Q("4.08795") / Q("2.33811"); roper = Q(1440, 939)
    ok = Q("1.49") < q1 < Q("1.493") and abs(q1 - q1b) < Q("0.002") and Q("1.86") < q2 < Q("1.87")
    ok &= abs(q1 - rl) < drl / 2 and airy > rl + drl and Q("1.74") < airy < Q("1.76")
    ok &= abs(roper - q1) < Q("0.03") * q1
    # 46:P3 (p46043)
    R.check("F4", "[chart] the radial ratio of the operator form: E₁/E₀ = 1.49 and E₂/E₀ = 1.86 for every a and ϰ (the dilation symmetry, the same "
            "on (1, 1) and (2, 9/4) to 10⁻³), a property of the chart's operator form and of nothing in the frame; against the lattice "
            "0⁺⁺*/0⁺⁺ = 1.54(11) it lies within half a standard deviation, while the nonrelativistic ladder's Airy ratio 1.75 lies outside the "
            "bracket; the nucleon's N(1440)/N(939) = 1.53 lies within 3 %", ok,
            f"E₁/E₀ = {CY.fmt(q1, 4)} ((2, 9/4): {CY.fmt(q1b, 4)}), E₂/E₀ = {CY.fmt(q2, 4)}, lattice {CY.fmt(rl)} ± {CY.fmt(drl)}, Airy {CY.fmt(airy, 4)}, "
            f"Roper {CY.fmt(roper, 4)}", kind="CHART")


# ------------------------------------------------------------------------------------------------------------
@R.block("G", BLOCK["G"])
def block_G():
    """Block G — the two routes of the former task T01 (the push of 8 November 2026), both obstructed."""
    # G1 route (a): a|p| + ϰr − C/max(r, r_c) with C = C_A α_s. The Herbst bound: bounded below iff C ≤ 2a/π. The declared coupling
    #    α_s(√σ) = 1.007 gives C = 3.02 > 4/π: no ground state (the grid at r_c = 1 cell gives 1.8, falling without bound as r_c → 0).
    #    The coupling run to the bound state's mass gives a fixed point only above a cutoff: 3.54, 3.08, 2.61 at r_c = 1, 1/2, 1/4
    #    (in 1/√σ) and none at 1/8 — the number is the cutoff's, and the cell's size in units of 1/√σ is the chart's β
    r = CY.short_range_route(cutoffs=(1.0, 0.5, 0.25, 0.125))
    fp = r["fixed_points"]; dc = Q(repr(r["declared_coupling"]))
    ok = Q("3.0") < dc < Q("3.05") and dc > Q(repr(r["herbst"][2])) and Q(repr(r["collapse_rc1"])) < Q("1.9")
    ok &= fp[1.0] is not None and Q("3.5") < Q(repr(fp[1.0][0])) < Q("3.6")
    ok &= fp[0.5] is not None and Q("3.0") < Q(repr(fp[0.5][0])) < Q("3.15")
    ok &= fp[0.25] is not None and Q("2.55") < Q(repr(fp[0.25][0])) < Q("2.7")
    ok &= fp[0.125] is None
    ok &= all(v is None or Q(repr(v[1])) < Q(repr(r["herbst"][2])) for v in fp.values())        # every fixed point lies below the two-body bound
    # 46:C10 (p46037)
    R.check("G1", "[chart] the short-range route is obstructed: with the declared coupling α_s(√σ) = 1.007 the two-adjoint term has C = C_A α_s = "
            "3.02 above the Herbst bounds 2/π (one-body) and 4/π (two-body), so the operator has no ground state (1.8 at one cell of cutoff, "
            "falling without bound); with the coupling run by the one-loop law to the bound state's mass the fixed point exists only above a "
            "cutoff — 3.54, 3.08, 2.61 at r_c = 1, 1/2, 1/4 and none at 1/8 — so the eigenvalue is the cutoff's, and the cell's size in "
            "units of 1/√σ is the chart's β, which no row fixes", ok,
            f"C_declared = {CY.fmt(dc, 3)}, collapse {CY.fmt(r['collapse_rc1'])}; fixed points " +
            ", ".join(f"r_c={rc}: " + (f"E₀={CY.fmt(v[0])} (C={CY.fmt(v[1])})" if v else "none") for rc, v in fp.items()), kind="CHART")

    # G2 route (b): the 0⁺⁺ channel of the strong-coupling expansion (the plaquette, the closed fundamental loop) with Münster's series
    #    to u⁷ and the tension at leading order; the frame's u = c₃(β). The orders 3, 5, 7 agree within 1 % up to u = 0.20 (β = 3), where
    #    the ratio is 4.8; at u = 0.30, where it would reach the lattice bracket 3.4–3.7, they disagree by 10 %; the scaling region is u ≈ 0.42
    pc = CY.plaquette_channel(); T = pc["table"]
    v7 = {u: Q(repr(row["orders"][7])) for u, row in T.items()}; sp = {u: Q(repr(row["spread"])) / v7[u] for u, row in T.items()}
    ok = Q("6.5") < v7["0.06"] < Q("6.7") and Q("5.9") < v7["0.10"] < Q("5.95") and Q("4.7") < v7["0.20"] < Q("4.8")
    ok &= all(sp[u] < Q("0.01") for u in ("0.06", "0.10", "0.15", "0.20")) and sp["0.30"] > Q("0.09")
    ok &= Q("3.5") < v7["0.30"] < Q("4.0") and all(v7[u] > Q("3.7") for u in ("0.06", "0.10", "0.15", "0.20", "0.25"))
    ub = {b: Q(repr(float(u))) for b, u in pc["u_of_beta"].items()}
    ok &= Q("0.0601") < ub["1"] < Q("0.0602") and Q("0.203") < ub["3"] < Q("0.2031") and Q("0.42") < ub["6"] < Q("0.43")
    # 46:C11 (p46038)
    R.check("G2", "[chart] the plaquette channel is obstructed: with the imported 0⁺⁺ series to u⁷ and the frame's u = c₃(β), m/√σ = 6.6, 5.9, "
            "5.3, 4.8 at u = 0.06, 0.10, 0.15, 0.20 (β = 1 to 3), the orders 3, 5, 7 agreeing within 1 %; the lattice bracket 3.4–3.7 is reached "
            "only at u = 0.30 (β ≈ 4.3), where the orders disagree by 10 %, and the scaling region is u ≈ 0.42 (β = 6): in the regime the frame's "
            "content controls, the channel's ratio is 4.8 or more", ok,
            ", ".join(f"u={u}: {CY.fmt(v7[u])} (spread {CY.fmt(sp[u] * 100, 1)} %)" for u in v7) + "; u(β): " +
            ", ".join(f"β={b}: {CY.fmt(x, 4)}" for b, x in ub.items()), kind="CHART")


if __name__ == "__main__":
    args = [a for a in sys.argv[1:] if not a.startswith("--")]
    if args:
        for b in args: R.run_block(b)
        ok = R.summary(write=False)
    else: ok = R.verify_all()
    sys.exit(0 if ok else 1)
