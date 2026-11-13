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
c₈ to order ϑ⁷ with rational coefficients and their ratio to that order; no float decides anything. A CHART check reads
a measured or lattice number, declared as a rational with its error in frc/chart_yangmills.py, against the frame's exact
value, runs the chart's one-loop law with its logarithm, reads the tensions as logarithms of the exact series, or runs the
chart's relativistic wrap operator on a grid; its label carries "[chart]".

The Lean side: the theorems of the yangmills theme (lean/FrcCore/Theme/YangMills.lean) — the no-shell-root theorem for the
norm-one elements of the extension, the arithmetic of the centre's order formula on the sweep, the singlet-multiplicity
identities behind the glueball and the adjoint wrap (glueball_singlet, adjoint_two_sheets), the Casimir and b₀ rationals,
the drive exponent's existence and uniqueness from the frame, the arithmetic of the spectral amplitude (the plane's cycles, the
phase table, the Z[ζ₃] identities of the instance and the transfer tally's bookkeeping; spectral_amplitude, frame_cycle_trace, instance_amplitude,
instance_transfer; the Subjects' spectrum and the degree identity, subject_spectrum, degree_identity), and the frame's root elements on the three Subjects
(frame_root_elements, 46:A9) — over the extension, frame and hadrons themes. The key file and the certificate follow the
ledger's JSON in Phase 3.

The laboratory instances are the pairs (13, 233), (173, 30089) and (1549, 2408561), with a sweep over the shells p = 4κ + 1
below 200 (the author's ruling of 7 November 2026). Colour's triality is the Carrier's relation Ω ≡ 5 (mod 12), and the Subject reads
colour in its unitary frame (the author's decisions of 11 November 2026, 46:B5): SU(3) over the Subject's quadratic extension F_p[√ν],
with the centre of order three where 3 | p + 1; the Carrier has no frame and no completed extension, so no torus or group is formed over F_Ω. No numeral above Ω ∼ 10¹²³ is formed.

    python3 -m frc.ledgers.p46_yangmills         every block, the census; exit 1 if a check fails (2–4 min: the F_4 linear algebra 12 s, the wrap spectrum 5 s, the frame's counts at q = 2, 3 about a minute, the amplitude and the transfer tally 5 s)
    python3 -m frc.ledgers.p46_yangmills A       one block (A to F)
    from frc.ledgers.p46_yangmills import R; R.predicate("46:C1")    one predicate: its blocks run once per session

Blocks:  A  the registrations of the unitary frame: the tori, the centre, the residue series  (46:C1, C2, C3, X1, X2, P4)
         B  the Casimirs and the window rational                                                 (46:C4, C5, X4)
         C  the drive exponent                                                                   (46:C6)
         D  the tension's coefficient to order ϑ⁷, the series' window, the frame's window and multiplicities   (46:A9, C7, C14, C15, C24, C26)
         E  the chart: LEP, the one-loop run, the lattice anchors                                (46:P1, P2, X4, C8)
         F  the minimal wrap (Phase 2, D5): the adjoint wrap, the operator family, the chart's tension ratio (46:C9, C12)
         G  the two chart routes of the former task T01, both failing (8 November 2026)                 (46:C10, C11)
         H  the spectral amplitude of a plaquette, the transfer tally on the instance (9 November 2026) and on the Subjects (10 November 2026)   (46:C16, C17, C18, C19)

Checks: 35, of them 26 EXACT and 9 CHART (E1–E4, F2–F4, G1, G2).
"""
import sys
from math import comb
from itertools import combinations, product
from fractions import Fraction as Q

from frc.registry import Registry
from frc import arith as A
from frc import yangmills as Y
from frc import chart_yangmills as CY
from frc.extension import Ext

# ---- generated by ci/make_ledgers.py from docs/46-yangmills/46-yangmills-ledger.json; edit the ledger, not this table ----
PAPER = "46-yangmills"
KEYS = {"A1": "p46001", "A2": "p46002", "A3": "p46003", "A4": "p46004", "A5": "p46005", "A6": "p46006", "A7": "p46031", "A8": "p46032", "A9": "p46034", "A10": "p46035", "A11": "p46039", "A12": "p46040", "A13": "p46052", "A14": "p46059", "A15": "p46060", "A16": "p46069", "A17": "p46073", "A18": "p46074", "A19": "p46075", "B1": "p46007", "B2": "p46008", "B3": "p46009", "B4": "p46055", "B5": "p46063", "B6": "p46070", "C1": "p46010", "C2": "p46011", "C3": "p46012", "C4": "p46013", "C5": "p46014", "C6": "p46015", "C7": "p46016", "C8": "p46017", "C9": "p46030", "C10": "p46037", "C11": "p46071", "C12": "p46036", "C13": "p46041", "C14": "p46051", "C15": "p46053", "C16": "p46056", "C17": "p46057", "C18": "p46058", "C19": "p46061", "C20": "p46062", "C21": "p46064", "C22": "p46065", "C23": "p46066", "C24": "p46067", "C25": "p46068", "C26": "p46072", "X1": "p46018", "X2": "p46019", "X3": "p46020", "X4": "p46021", "X5": "p46022", "P1": "p46023", "P2": "p46024", "P3": "p46043", "P4": "p46076", "Z1": "p46026"}       # every row of the ledger: its label and its accession key
LEAN = {"A9": "core", "C1": "core", "C2": "core", "C3": "core", "C4": "core, ml", "C5": "core", "C6": "core", "C7": "core", "C9": "core", "C10": "core, ml", "C11": "core, ml", "C12": "core, ml", "C13": "core, ml", "C14": "core", "C15": "core", "C16": "core", "C17": "core", "C18": "core", "C19": "core", "C20": "core", "C21": "core, ml", "C22": "core", "C23": "core", "C24": "core", "C25": "core", "C26": "core", "X1": "core", "X2": "core", "X4": "core", "P1": "core", "P2": "core, ml", "P3": "core, ml", "P4": "core"}       # the rows with a Lean declaration: the libraries whose key files prove them
# ---- end of the generated table ----

LEAN_ONLY = ()                  # the predicates with a Lean declaration and no python check (gate G12): none

LEDGER = {
    "A1": "46:C1, 46:X1, 46:X2", "A2": "46:C1", "A3": "46:C2", "A4": "46:C3, 46:X2", "A5": "46:C3, 46:P4", "A6": "46:C2",
    "B1": "46:C4, 46:X4", "B2": "46:C5", "B3": "46:C13",
    "C1": "46:C6",
    "D1": "46:C7", "D2": "46:C7", "D3": "46:C14", "D4": "46:C15, 46:A9", "D5": "46:C24", "D6": "46:C26",
    "E1": "46:P1, 46:X4", "E2": "46:P2", "E3": "46:C8", "E4": "46:B6",
    "F1": "46:C9", "F2": "46:C12", "F3": "46:C9", "F4": "46:P3",
    "G1": "46:C10", "G2": "46:C11",
    "H1": "46:C16", "H2": "46:C17", "H3": "46:C18", "H4": "46:C19", "H5": "46:C20", "H6": "46:C21", "H7": "46:C22", "H8": "46:C23", "H9": "46:C25",
}

BLOCK = {"A": "the registrations of the unitary frame: the norm-one cycle without a fixed line, the split torus with two, the centre of order gcd(3, p + 1) with the Carriers' residue 5 (mod 12), the residue series on the instance, the states of residue 0 on the Subjects",
         "B": "the Casimirs of the frame, the window rational b₀ and the two rationals of the one-loop coefficient",
         "C": "the drive exponent: every winding rate is one power of the drive",
         "D": "the tension's coefficient: the single-plaquette coefficient to order ϑ⁷ with rational coefficients, the series' window — the corollary of A9 on the orders the frame fixes — and the frame's window through degree 2p − 1 with the Frobenius tensor that ends it by degree 4p − 3; the multiplicities of the frame (A9) are decided with the window",
         "E": "the chart: the LEP colour factors, the one-loop run between laboratory scales, the lattice anchors, the chart's cells",
         "F": "the minimal wrap: the adjoint plaquette coefficient is the square of the fundamental one up to the factor 9/8, with the ratio computed to order ϑ⁴; the chart's operator family against the three lattice determinations; the chart's tension ratio; the operator form's radial ratio against the lattice and the nucleon",
         "G": "the two routes of the former task T01: the short-range term collapses at the declared coupling and is the cutoff's number with the running one; the plaquette channel's series gives 4.8 or more where its orders agree",
         "H": "the spectral amplitude of a plaquette: its finite properties and singular values, its values and moments on the 216 elements of the instance, the transfer tally, the step of one plaquette with the frame's mean, with its exact spectrum 2/3, 1/6, 0, −1/3 and its annihilated trivial channel, and on the Subjects the amplitude's character expansion w = χ₁ + χ₂ − χ₃ from the generic character table with the tally's three eigenvalues 1/(q²−q+1), 1/(q³+1), −1/((q+1)²(q−1)), the tally of the ring and the gap 1/(q+1) of the transfer tally"}

PREDICATES = {
    "46:C1": "A1", "46:X1": "A1", "46:X2": "A1", "46:C2": "A3", "46:C3": "A4",
    "46:C4": "B1", "46:X4": "B1", "46:C5": "B2", "46:C13": "B3", "46:C6": "C1", "46:C7": "D1", "46:C14": "D3", "46:C15": "D4", "46:A9": "D4", "46:C24": "D5", "46:C26": "D6",
    "46:P1": "E1", "46:P2": "E2", "46:C8": "E3", "46:B6": "E4", "46:C9": "F1", "46:C12": "F2", "46:P3": "F4", "46:P4": "A5", "46:C10": "G1", "46:C11": "G2",
    "46:C16": "H1", "46:C17": "H2", "46:C18": "H3", "46:C19": "H4", "46:C20": "H5", "46:C21": "H6", "46:C22": "H7", "46:C23": "H8", "46:C25": "H9",
}

R = Registry("46", "yangmills", LEDGER, PREDICATES, sources=[__file__])

LAB = Y.LAB_PAIRS
SWEEP = Y.shells_below(200)


def _nonsquare(p):
    return next(x for x in range(2, p) if A.legendre(x, p) == -1)


# ---- the multiplicities of the frame (46:A9; decision D140, 13 November 2026): the vectors that SL_3 over the plane fixes as a
#      kernel of integer matrices modulo p, four root elements of the frame, and the rank of the pairing-and-determinant tensors;
#      exact, on dicts ----------------------------------------------------------------------------------------------------------
def _rank_sparse(rows, p):
    """The rank modulo p of a list of sparse integer rows (dicts column → entry), by elimination on the dicts; exact."""
    piv = {}
    for r in rows:
        r = {c: v % p for c, v in r.items() if v % p}
        while r:
            c = min(r); q = piv.get(c)
            if q is None:
                inv = pow(r[c], -1, p); piv[c] = {k: v * inv % p for k, v in r.items()}; break
            f = r[c]
            for k, v in q.items():
                w = (r.get(k, 0) - f * v) % p
                if w: r[k] = w
                else: r.pop(k, None)
    return len(piv)


def _rank_sparse_plane(rows, K):
    """The rank over the plane K = F_p(√2) of a list of sparse rows with entries in K (pairs), by the same elimination; exact."""
    piv = {}; zero = (0, 0)
    for r in rows:
        r = {c: v for c, v in r.items() if v != zero}
        while r:
            c = min(r); q = piv.get(c)
            if q is None:
                inv = K.inv(r[c]); piv[c] = {k: K.mul(v, inv) for k, v in r.items()}; break
            f = r[c]
            for k, v in q.items():
                w = K.sub(r.get(k, zero), K.mul(f, v))
                if w != zero: r[k] = w
                else: r.pop(k, None)
    return len(piv)


def sl3_fixed_count(p, a, b, zero_weight=False):
    """46:A9(i) — the dimension of the kernel modulo p of the integer matrices D_st^(k), 1 ≤ k ≤ a + b, on the words of 3^{⊗a} ⊗ 3̄^{⊗b}:
    D_st^(k) is the coefficient of z^k in the action of 1 + zE_st (on 3 the letter t becomes s; on 3̄ the letter s becomes t, with
    the sign −1). The four pairs (s, t) = (0,1), (1,2), (1,0), (2,1) are used. Over the plane of p, which has more than a + b
    elements at every degree used here, the kernel is the space of the vectors that their elements 1 + zE_st fix; these elements
    generate SL_3 over the plane, so the kernel is the kernel of all six pairs. The rank is computed on the transposed matrix,
    one sparse row for each word. With zero_weight the words are those of weight (k, k, k), with as many letters e_l less letters
    e_l* for l = 0, 1, 2. The matrices carry a word to words of one other weight, so the kernel is the sum of its parts of each
    weight; over the plane of a Subject the diagonal elements of SL_3 fix only the words of weight (k, k, k) at the degrees
    used, so the part of weight (k, k, k) is the whole kernel there."""
    n = a + b; N = 3 ** n; rows = []; count = 0
    for w in product(range(3), repeat=n):
        if zero_weight:
            wt = [0, 0, 0]
            for i, l in enumerate(w): wt[l] += 1 if i < a else -1
            if not wt[0] == wt[1] == wt[2]: continue
        count += 1; r = {}
        for ri, (s, t) in enumerate(((0, 1), (1, 2), (1, 0), (2, 1))):
            pos = [i for i in range(a) if w[i] == t] + [i for i in range(a, n) if w[i] == s]
            for k in range(1, len(pos) + 1):
                for sub in combinations(pos, k):
                    v = list(w); sign = 1
                    for i in sub:
                        if i < a: v[i] = s
                        else: v[i] = t; sign = -sign
                    idx = 0
                    for l in v: idx = idx * 3 + l
                    r[(ri * (n + 1) + k) * N + idx] = sign
        rows.append(r)
    return count - _rank_sparse(rows, p)


def frame_root_elements(p):
    """Four elements of the frame SU(3, F_p) of the Hermitian form ξ₀η̄₂ + ξ₁η̄₁ + ξ₂η̄₀ over the plane F_p(√2) (46:A9(iii)):
    x(λ, μ) = 1 + λE_01 − λ̄E_12 + μE_02 with μ + μ̄ + λλ̄ = 0, at (λ, μ) = (1, −1/2 + √2) and (√2, 1 + √2), where −1/2 is the
    residue (p − 1)/2, and their transposes. The plane is F_p(√2), with 2 a nonsquare of the shell, as on the Subjects 13, 173 and
    1549. Returns the pairs (element, inverse) as 3 × 3 tuples over the plane; each is verified
    here: x x⁻¹ = 1 and xᵀ J x̄ = J for the antidiagonal J. The determinant of a triangular matrix with the diagonal 1 is 1."""
    K = Ext(p, 2); z, o = (0, 0), (1, 0); neg_half = (p - 1) // 2
    def mul(A, B): return tuple(tuple(K.add(K.add(K.mul(A[i][0], B[0][j]), K.mul(A[i][1], B[1][j])), K.mul(A[i][2], B[2][j]))
                                      for j in range(3)) for i in range(3))
    def tr(A): return tuple(tuple(A[j][i] for j in range(3)) for i in range(3))
    I3 = ((o, z, z), (z, o, z), (z, z, o)); J = ((z, z, o), (z, o, z), (o, z, z))
    out = []
    for t, u in (((1, 0), (neg_half, 1)), ((0, 1), (1, 1))):
        assert K.add(K.add(u, K.conj(u)), K.mul(t, K.conj(t))) == z
        x = ((o, t, u), (z, o, K.neg(K.conj(t))), (z, z, o)); xi = ((o, K.neg(t), K.conj(u)), (z, o, K.conj(t)), (z, z, o))
        for g, gi in ((x, xi), (tr(x), tr(xi))):
            gb = tuple(tuple(K.conj(e) for e in row) for row in g)
            assert mul(g, gi) == I3 and mul(mul(tr(g), J), gb) == J
            out.append((g, gi))
    return out


def frame_root_fixed_count(p, a, b):
    """46:A9(iii) — the dimension over the plane F_p(√2) of the space of vectors of 3^{⊗a} ⊗ 3̄^{⊗b} fixed by the four elements of
    frame_root_elements(p), which act on 3 as themselves and on 3̄ by the inverse transpose. The frame fixes no more vectors than
    these four elements do, and it fixes every vector that SL_3 over the plane fixes."""
    K = Ext(p, 2); n = a + b; zero = (0, 0); rows = []
    for g, gi in frame_root_elements(p):
        gd = tuple(tuple(gi[j][i] for j in range(3)) for i in range(3))
        for w in product(range(3), repeat=n):
            r = {}
            def expand(i, idx, coef):
                if i == n:
                    r[idx] = K.add(r.get(idx, zero), coef); return
                m = g if i < a else gd
                for l in range(3):
                    e = m[w[i]][l]
                    if e != zero: expand(i + 1, idx * 3 + l, K.mul(coef, e))
            expand(0, 0, (1, 0))
            own = 0
            for l in w: own = own * 3 + l
            r[own] = K.sub(r.get(own, zero), (1, 0))
            rows.append(r)
    return 3 ** n - _rank_sparse_plane(rows, K)


def pairing_determinant_rank(p, a, b):
    """46:A9(ii) — the rank modulo p of the pairing-and-determinant tensors of 3^{⊗a} ⊗ 3̄^{⊗b}: the products, over a partition of
    the a + b slots, of pairings Σ_l e_l ⊗ e_l* on two slots of opposite type and of determinant tensors ε, ε* on three slots of
    one type. Every such tensor is listed, as a sparse integer vector on the words, and the rank is computed by elimination."""
    perms = (((0, 1, 2), 1), ((1, 2, 0), 1), ((2, 0, 1), 1), ((0, 2, 1), -1), ((2, 1, 0), -1), ((1, 0, 2), -1))
    def split(slots, e):                                        # the ways to take e triples out of the slots: (triples, the rest)
        if e == 0: yield (), tuple(slots); return
        first = slots[0]                                        # the first slot is in a triple or stays
        for i in range(1, len(slots)):
            for j in range(i + 1, len(slots)):
                rest = slots[1:i] + slots[i + 1:j] + slots[j + 1:]
                for tr, left in split(rest, e - 1): yield ((first, slots[i], slots[j]),) + tr, left
        if len(slots) - 1 >= 3 * e:
            for tr, left in split(slots[1:], e): yield tr, (first,) + left
    def matchings(xs, ys):
        if not xs: yield (); return
        for i, y in enumerate(ys):
            for more in matchings(xs[1:], ys[:i] + ys[i + 1:]): yield ((xs[0], y),) + more
    n = a + b; rows = []
    for e in range(a // 3 + 1):
        m = a - 3 * e; f, rem = divmod(b - m, 3)
        if m > b or rem: continue
        for tv, sv in split(tuple(range(a)), e):
            for td, sd in split(tuple(range(a, n)), f):
                for match in matchings(sv, sd):
                    vec = {}
                    for letters in product(range(3), repeat=m):
                        for choice in product(perms, repeat=e + f):
                            w = [0] * n; sign = 1
                            for (i, j), l in zip(match, letters): w[i] = l; w[j] = l
                            for tri, (pm, sg) in zip(tv + td, choice):
                                sign *= sg
                                for slot, letter in zip(tri, pm): w[slot] = letter
                            idx = 0
                            for l in w: idx = idx * 3 + l
                            vec[idx] = vec.get(idx, 0) + sign
                    rows.append(vec)
    return _rank_sparse(rows, p)


def frame_multiplicities(p):
    """46:A9 on a Subject p on which 2 is a nonsquare, as on 13, 173 and 1549 — Proposition prop:mult decided against the compact count Y.I.su3_moment. (i) The kernel modulo p of
    the integer matrices has the compact dimension at each of the 21 pairs of degree at most 5 (sl3_fixed_count), and on the
    words of weight (k, k, k) at the seven pairs with b ≤ a and 3 | a − b of degrees 6 to 9. (ii) The pairing-and-determinant
    tensors have the compact rank at the twelve pairs with b ≤ a and 3 | a − b of degree at most 9 (pairing_determinant_rank).
    (iii) Four root elements of the frame fix as many vectors at (1, 1), (3, 0) and (2, 2) (frame_root_fixed_count). With them:
    6 is invertible on the shell; the plane has more than a + b + min(a, b) elements for every degree a + b ≤ 2p − 1; and the
    degree 9 satisfies 9 + 2 ≤ p."""
    low = [(a, d - a) for d in range(6) for a in range(d + 1)]
    wide = [(a, b) for a in range(10) for b in range(a + 1) if a + b <= 9 and (a - b) % 3 == 0]
    high = [k for k in wide if sum(k) >= 6]
    compact = {k: Y.I.su3_moment(*k) for k in low + wide}
    plane = {k: sl3_fixed_count(p, *k) for k in low}
    zero = {k: sl3_fixed_count(p, *k, zero_weight=True) for k in high}
    span = {k: pairing_determinant_rank(p, *k) for k in wide}
    roots = {k: frame_root_fixed_count(p, *k) for k in ((1, 1), (3, 0), (2, 2))}
    checks = {"plane": len(low) == 21 and all(plane[k] == compact[k] for k in low),
              "zero": len(high) == 7 and all(zero[k] == compact[k] for k in high),
              "span": len(wide) == 12 and all(span[k] == compact[k] for k in wide),
              "roots": all(roots[k] == compact[k] for k in roots), "six": (6 * pow(6, -1, p)) % p == 1,
              "size": p * p > (2 * p - 1) + (p - 1), "degree": 9 + 2 <= p}
    return {"p": p, "compact": compact, "plane": plane, "zero": zero, "span": span, "roots": roots, "checks": checks,
            "ok": all(checks.values())}


# ------------------------------------------------------------------------------------------------------------
@R.block("A", BLOCK["A"])
def block_A():
    """Block A — the registrations of the unitary frame."""
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
    R.check("A1", "the norm-one cycle has no shell eigenvalue: on the Subjects 13, 173, 1549 "
            "and the 21 shells below 200 the norm-one cycle of F_p[√ν], its norm-one elements, has p + 1 elements, of which exactly the two scalars ±1 "
            "have an eigenvalue in F_p; every non-scalar element's characteristic polynomial x² − 2ax + 1 has the nonsquare "
            "discriminant 4νb², so no line of F_p² is mapped to itself by every element of the circle: the gluon's residue is 0", ok,
            ", ".join(f"{p}: {n} elements, {k} with an eigenvalue" for p, (n, k) in res.items()))

    # A2 the split torus diag(g, g⁻¹), g a generator, fixes exactly the two coordinate lines of P¹(F_p): the photon's residue 2
    ok = True; det = {}
    for p in [q for q, _ in LAB] + SWEEP:
        fl = Y.fixed_lines_split(p, A.primitive_root(p)); det[p] = len(fl); ok &= sorted(fl) == [(0, 1), (1, 0)]
    R.check("A2", "the split torus fixes exactly two lines: on the laboratory Subjects and the sweep, diag(g, g⁻¹) with g the drive "
            "fixes [1 : 0] and [0 : 1] and no other point of P¹(F_p) (g² ≠ 1), the two F_p-fixed lines that are the photon's two "
            "helicities, residue 2 (12-primer §6), against the norm-one cycle's none", ok, f"fixed lines {sorted(set(det.values()))} on {len(det)} shells")

    # A3 the centre of SU(3, F_q) is Z_{gcd(3, q+1)}: of order three exactly when q ≡ 2 (mod 3); the Subject 173 has it, 13 and 1549 do
    #    not, and no condition on a Subject's prime follows: colour's triality is the Carrier's relation Ω ≡ 5 (mod 12) (46:B5), decided
    #    on the three laboratory Carriers
    orders = {p: Y.centre_order(p) for p, _ in LAB}
    ok = orders[13] == 1 and orders[173] == 3 and orders[1549] == 1 and Y.full_centre(173) and not Y.full_centre(13) and not Y.full_centre(1549)
    ok &= all((Y.centre_order(p) == 3) == (p % 3 == 2) == Y.full_centre(p) for p in SWEEP)
    ok &= [p for p in SWEEP if Y.full_centre(p)] == [5, 17, 29, 41, 53, 89, 101, 113, 137, 149, 173, 197]
    car = {Om: Y.carrier_triality(Om) for _, Om in LAB}
    ok &= all(c["ok"] for c in car.values()) and not any(Y.carrier_triality(p)["ok"] for p in (13, 1549))
    # 46:C2 (p46011)
    R.check("A3", "the centre of the unitary frame: |Z(SU(3, F_q))| = gcd(3, q + 1), of order three exactly on q ≡ 2 (mod 3); of the "
            "Subjects 173 has it and 13, 1549 do not; 12 of the 21 shells below 200 have it. Colour's triality is the Carrier's: the "
            "Carriers 233, 30089, 2408561 are 5 (mod 12), x² + x + 1 has no root on them, and its roots are the norm-one pairs "
            "(0, 1) and (−1, −1) of residues", ok, f"centre orders {orders}; Carriers modulo 12: {[Om % 12 for _, Om in LAB]}")

    # A4 the residue series over F_4 on SU(3, F_2): no nonzero traceless matrix fixed by the adjoint action (gluon 0), det the one
    #    invariant of Λ³ (baryon 1), the commutant of the fundamental one-dimensional (meson 1), the commutant of the adjoint
    #    one-dimensional (glueball 1: the singlet of 8 ⊗ 8 once)
    F, G = Y.H.colour_group()
    series, content = Y.residue_series(F, G)
    ok = series == dict(gluon=0, baryon=1, meson=1, glueball=1, fundamental_commutant=1) and content == (1, 0, 0, 1) and len(G) == 216
    # 46:C3 (p46012)
    R.check("A4", "the residue series on the instance, over F_4 on the 216 elements of SU(3, F_2): the adjoint action on the "
            "eight traceless matrices fixes no nonzero vector (gluon 0), the determinant is the one invariant of Λ³ (baryon 1), the "
            "commutant of the fundamental is the scalars (meson 1, the Hermitian contraction), and the commutant of the adjoint is "
            "one-dimensional (glueball 1, the singlet of 8 ⊗ 8 once): photon 2, gluon 0, baryon 1, meson 1, glueball 1", ok,
            f"{series}, content {content}")

    # A5 the same counts by the Weyl constant terms of SU(3): E[|χ|²] − 1 = 0, E[χ³] = 1, E[|χ|²] = 1, E[|χ|⁴] − 2E[|χ|²] + 1 = 1.
    #    The states of residue 0 (46:P4; decisions D146 (a) and D147 (a), 13 November 2026): on the three Subjects the triplet has no
    #    vector fixed by SL_3 over the plane and 3 ⊗ 3̄ has one, the pairing (the kernel of the integer matrices of 46:A9), and the
    #    frame's four root elements fix as many. The frame has no nontrivial character into the plane, so an invariant line is a
    #    fixed line, and neither the triplet nor the adjoint has one. The confrontation of P4 is the import A19.
    w, E = Y.weyl_residues()
    ok = w == dict(gluon=0, baryon=1, meson=1, glueball=1) and E == {(1, 1): 1, (3, 0): 1, (2, 2): 2}
    zero = {p: (sl3_fixed_count(p, 1, 0), sl3_fixed_count(p, 1, 1), frame_root_fixed_count(p, 1, 0), frame_root_fixed_count(p, 1, 1))
            for p, _ in LAB}
    ok &= all(v == (0, 1, 0, 1) for v in zero.values()) and Y.I.su3_moment(1, 0) == 0 and Y.I.su3_moment(1, 1) == 1
    # 46:P4 (p46076)
    R.check("A5", "the residue series by the Weyl constant terms of SU(3): the adjoint has no invariant (E[χχ̄] − 1 = 0), 3 ⊗ 3 ⊗ 3 one "
            "singlet (E[χ³] = 1), 3 ⊗ 3̄ one (E[χχ̄] = 1), 8 ⊗ 8 one (E[χ²χ̄²] − 2E[χχ̄] + 1 = 2 − 2 + 1 = 1): the finite-field counts and "
            "the singlet multiplicities of the compact reading agree; the states of residue 0: on the Subjects 13, 173, 1549 the triplet "
            "has no fixed vector and 3 ⊗ 3̄ has one, the pairing, under SL_3 over the plane and under four root elements of the frame, so "
            "the triplet and the adjoint have no frame-invariant line, and a quark and a gluon are states of residue 0", ok,
            f"moments {E}; fixed vectors of the triplet and of 3 ⊗ 3̄ under SL_3 and under the root elements, on 13: {zero[13]}")

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
    e = Y.casimirs_from_exponents()                                           # the frame's own source (round 03, 9 November 2026): the torus exponents
    ok &= e["form_F"] == (2, 2, 2) and e["form_A"] == (12, 12, 12) and e["ratio_T"] == 6 and e["T_A"] == 3
    ok &= e["C_F"] == c["C_F"] and e["C_A"] == c["C_A"] and e["ratio"] == c["ratio"] and e["singlet"] == -8
    ok &= all(Y.split_torus_exponents(p)["ratio"] == 6 for p in (13, 173, 1549))
    # 46:C4 (p46013), 46:X4 (p46021)
    R.check("B1", "the Casimirs of the unitary frame from its torus exponents: the fundamental's (a, b, −a−b) and the adjoint's six differences "
            "have second moments 2 and 12 times a² + ab + b², so T_A/T_F = 6 and, with the chart's normalisation T_F = 1/2, C_F = 4/3, C_A = 3, "
            "C_A/C_F = 9/4 — the compact values, with no lift; the singlet Σ λ·λ = −8 (−8/3 per pair; 35-hadrons C4); the identity read on the "
            "split torus (n, (p−1)n, −pn) of the Subjects 13, 173, 1549", ok, f"{c}; forms {e['form_F']}, {e['form_A']}")

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
    ok = s3 == [Q(0), Q(1, 3), Q(1, 6), Q(0), Q(-5, 72), Q(-1, 24), Q(7, 720), Q(59, 2160)] and sum(s3) == Q(23, 54)
    # 46:C7 (p46016)
    R.check("D1", "the tension's coefficient to order ϑ⁷: the fundamental plaquette coefficient of SU(3) in the stiffness of the connection (A16), "
            "c₃(ϑ) = ϑ/3 + ϑ²/6 + 0·ϑ³ − 5ϑ⁴/72 − ϑ⁵/24 + 7ϑ⁶/720 + 59ϑ⁷/2160 modulo ϑ⁸, summing to 23/54 at channel unity, every coefficient a rational built from "
            "the singlet multiplicities of the tensor powers of the triplet (the constant terms of the Weyl character polynomial; the "
            "frame's own multiplicities agree in the degrees that enter through ϑ³, block F); 27-fields C7's β/18 + β²/216, in Wilson's coupling β = 6ϑ, continued", ok,
            ", ".join(str(c) for c in s3[1:]))

    s2 = Y.c1_series(2, 7); s2t, tr = Y.c1_series_2T(7)
    ok = s2 == [Q(0), Q(1), Q(0), Q(-2, 3), Q(0), Q(2, 3), Q(0)] and s2t[:5] == s2[:5] and s2t[5] == Q(4, 5)
    ok &= tr == {2: 1, -2: 1, 0: 6, 1: 8, -1: 8} and s2t[5] - s2[5] == Q(2, 15)
    R.check("D2", "the exact finite instance: 2T = SU(2, F_3) from its 24 unit quaternions (traces 2, −2 once, 0 six times, ±1 eight times) "
            "gives the fundamental coefficient ϑ − 2ϑ³/3 + 4ϑ⁵/5 + …, against the multiplicity series of SU(2), ϑ − 2ϑ³/3 + 2ϑ⁵/3 + …: the same "
            "coefficients through ϑ³, the first difference 2ϑ⁵/15 (27-fields Theorem corr2T, there in Wilson's coupling 4ϑ)", ok, f"2T {[str(c) for c in s2t[1:6]]}")

    # D3 the series' window, the corollary of A9 (the push on T06, 9 November 2026): the ϑ^k coefficient of c₃ is built from the invariant
    #    counts of degree ≤ k + 1, that of c₈ from degree ≤ k + 2 — by perturbation of the counts degree by degree — so with A9 the frame's
    #    series equal the compact ones through ϑ^{p−3}, ϑ^{p−4}: ϑ¹⁰, ϑ⁹ on 13 (the paper computes ϑ⁷). On the instance, where the equalities of A9 do not apply,
    #    the departure at degree 5 (M(4,1) = 4 against 3) puts c₃'s ϑ⁴ at 0 and c₈'s ϑ³ at 1/8.
    w = Y.series_window(8)
    ok = all(w["first_changed"][d] == ((d - 1 if d - 1 < 8 else None), d - 2) for d in range(2, 10))
    ok &= w["window"] == {13: (10, 9), 173: (170, 169), 1549: (1546, 1545)} and all(v[0] >= 7 and v[1] >= 7 for v in w["window"].values())
    inst = Y.instance_series_departure()                                       # the instance's own counts over F_4 (two nullspaces, ~10 s)
    ok &= inst["M41"] == 4 and inst["M14"] == 4 and inst["compact41"] == 3
    ok &= inst["c3_instance"][:4] == inst["c3_compact"][:4] and inst["c3_instance"][4] == 0 and inst["c3_compact"][4] == Q(-5, 72)
    ok &= inst["c8_instance"][:3] == inst["c8_compact"][:3] and inst["c8_instance"][3] == Q(1, 8) and inst["c8_compact"][3] == Q(1, 12)
    # 46:C14 (p46051)
    R.check("D3", "the series' window, the corollary of A9: the ϑ^k coefficient of c₃ depends on the invariant counts of degree ≤ k + 1 and that "
            "of c₈ on degree ≤ k + 2 (raising the counts of degree d by one moves c₃ first at ϑ^{d−1} and c₈ at ϑ^{d−2}), so the frame's coefficients "
            "are built from the compact counts through ϑ^{p−3}, ϑ^{p−4}: ϑ¹⁰, ϑ⁹ on the Subject 13, ϑ¹⁷⁰, ϑ¹⁶⁹ on 173, ϑ¹⁵⁴⁶, ϑ¹⁵⁴⁵ on 1549, all beyond the ϑ⁷ "
            "computed; on the instance SU(3, F_2), where the equalities of A9 do not apply, M(4,1) = M(1,4) = 4 against the compact 3 puts c₃'s ϑ⁴ coefficient at 0 "
            "(compact −5/72) and c₈'s ϑ³ at 1/8 (compact 1/12)", ok,
            f"first changes {w['first_changed']}; instance c₃ {[str(c) for c in inst['c3_instance']]}, c₈ {[str(c) for c in inst['c8_instance']]}")

    # D4 the frame's window and its first departure (46:C15; the T07 pushes of 9 November 2026): for odd p the frame's invariant counts
    #    are the compact ones through degree 2p − 1 (the coordinate SU(2) subgroups and finite Schur–Weyl, imported as A13), and the
    #    Frobenius tensor v_q = Σ sgn(i,j,k) S(i^{2q−1} j^{q−2} k^{q−1}) ⊗ e_k* at (4q − 4, 1) is a frame invariant outside the
    #    pairing-and-determinant span for every q — the image of the frame's hermitian pairing under a map of GL_3(K)-modules, K the
    #    field of q² elements, whose equivariance is the row-operation identity with its binomial table. Decided here: the table by Lucas on the Subjects and the
    #    small fields, the identity word by word for every z at q = 2, 3, the diagonal multipliers, g^{(q)} = ḡ = g^{−T} on the generators,
    #    v₂ fixed by the generators of SU(3, F_2), the weights of v_q's words, the finite counts at q = 3 (the compact ones through degree 8,
    #    M(8,1) = 1 against 0 at degree 9: d_* = 9; at q = 2 the compact ones through degree 5 except M(4,1) = 4: d_* = 5), and the bounds and
    #    orders on the Subjects. The multiplicities of the frame (46:A9; decision D140, 13 November 2026) are decided here as well. On the
    #    three Subjects: the kernel modulo p of the integer matrices of the elements 1 + zE_st at every pair of degree at most 5 and, on the
    #    words of weight (k, k, k), at the pairs of degrees 6 to 9; the vectors that four root elements of the frame fix; and the rank of
    #    the pairing-and-determinant tensors through degree 9. Modulo 3 the kernel and the rank are computed at every pair of degree at
    #    most 5, the window of the field of three elements, where the proposition's division by 6 is not available; the rank is also
    #    computed modulo 2 through degree 5 and modulo 3 through degree 8.
    bt = all(Y.binomial_table(q, q) == Y.binomial_table_expected(q, q) for q in (2, 3, 13, 173, 1549))
    ri2, ri3 = Y.row_identity(2), Y.row_identity(3)
    ok = bt and ri2 == (162, 0) and ri3 == (432, 0) and Y.diagonal_multipliers(13) and Y.diagonal_multipliers(1549)
    ok &= Y.frobenius_identification(2) == (2, True) and Y.frobenius_identification(3) == (2, True)
    ok &= Y.frobenius_tensor_fixed(2) and len(Y.frobenius_tensor(2)) == 24 and len(Y.frobenius_tensor(3)) == 1008
    ok &= Y.frobenius_weights(2) == [(0, 0, 3), (0, 3, 0), (3, 0, 0)] and Y.frobenius_weights(3) == [(1, 1, 5), (1, 5, 1), (5, 1, 1)]
    M3 = Y.frame_counts_small_field(3, 9, pairs={(a, b) for a in range(10) for b in range(10) if a + b <= 8} | {(8, 1)})   # numpy, exact; ≈ 55 s
    ok &= all(M3[k] == Y.I.su3_moment(*k) for k in M3 if sum(k) <= 8) and M3[(8, 1)] == 1 and Y.I.su3_moment(8, 1) == 0
    M2 = Y.frame_counts_small_field(2, 5)                                        # the instance by the same solver: d_*(2) = 5
    ok &= M2[(4, 1)] == 4 and Y.I.su3_moment(4, 1) == 3 and all(M2[k] == Y.I.su3_moment(*k) for k in M2 if k != (4, 1))
    ok &= all(Y.first_departure_bounds(p) == (2 * p, 4 * p - 3) for p, _ in LAB) and Y.frame_window_orders(13) == (25, 24, 23)
    fm = {p: frame_multiplicities(p) for p, _ in LAB}                         # 46:A9 on the three Subjects
    ok &= all(fm[p]["ok"] for p in fm) and all(fm[p]["roots"] == {(1, 1): 1, (3, 0): 1, (2, 2): 2} for p in fm)
    ok &= all(fm[p]["plane"][(4, 1)] == 3 and fm[p]["plane"][(2, 1)] == 0 and fm[p]["zero"][(6, 3)] == 47 and fm[p]["zero"][(9, 0)] == 42 for p in fm)
    ok &= all(fm[p]["span"][(4, 4)] == 23 and fm[p]["span"][(7, 1)] == 21 and fm[p]["span"][(6, 3)] == 47 for p in fm)
    low = [(a, d - a) for d in range(6) for a in range(d + 1)]                 # the 21 pairs of degree at most 5
    wide = [(a, b) for a in range(9) for b in range(a + 1) if a + b <= 8 and (a - b) % 3 == 0]
    ok &= all(sl3_fixed_count(3, a, b) == pairing_determinant_rank(3, a, b) == Y.I.su3_moment(a, b) for a, b in low)   # the window of F_3, over F_9
    ok &= all(pairing_determinant_rank(2, a, b) == Y.I.su3_moment(a, b) for a, b in wide if a + b <= 5)
    ok &= all(pairing_determinant_rank(3, a, b) == Y.I.su3_moment(a, b) for a, b in wide)
    # 46:C15 (p46053), 46:A9 (p46034)
    R.check("D4", "the frame's window and its first departure: for odd p the frame's invariant counts are the compact ones through degree "
            "2p − 1, and the Frobenius tensor v_q at (4q − 4, 1) is a frame invariant beyond them for every q, so the first departure d_* lies "
            "in [2p, 4p − 3] — [26, 49] on the Subject 13, [346, 689] on 173, [3098, 6193] on 1549 — and the series are the compact ones "
            "through ϑ^{2p−2}, ϑ^{2p−3}: ϑ²⁴, ϑ²³ on 13; the binomial table of the row-operation identity on the Subjects and the small fields, "
            "the identity for every z (162 cases at q = 2, 432 at q = 3), the diagonal multipliers, ḡ = g^{−T} = g^{(q)} on the generators, "
            "v₂ fixed by SU(3, F_2), the weights of v_q's words a permutation of (2q − 1, q − 2, q − 2); at q = 3 the counts are the compact "
            "ones through degree 8 and M(8,1) = 1 against 0, so d_*(3) = 9; at q = 2 they are the compact ones through degree 5 except M(4,1) = 4 against 3, so d_*(2) = 5; "
            "the multiplicities of the frame (Prop. prop:mult) on the Subjects 13, 173, 1549: modulo p the integer matrices of the elements "
            "1 + zE_st have a kernel of the compact dimension at each of the 21 pairs of degree at most 5 and, on the words of weight (k, k, k), "
            "at the seven pairs of degrees 6 to 9; four root elements of the frame fix as many vectors at (1,1), (3,0), (2,2); the "
            "pairing-and-determinant tensors have the compact rank through degree 9; modulo 3 the kernel and the tensors' rank are the compact "
            "count at each of the 21 pairs of degree at most 5; the rank is the compact count modulo 2 through degree 5 and modulo 3 through degree 8", ok,
            f"row identity {ri2}, {ri3}; q = 3 counts {sorted((k, v) for k, v in M3.items() if sum(k) >= 8)}; "
            f"on 13 the kernel at degree 5 {sorted((k, v) for k, v in fm[13]['plane'].items() if sum(k) == 5)}, "
            f"on the words of weight (k, k, k) {fm[13]['zero']}, the root elements {fm[13]['roots']}")

    # D5 what a reading keeps of the window (46:C24; round 05, 11 November 2026; the audit with the four tests, 12 November 2026):
    #    the counts of D4 are equal as integers and a residue keeps less — on 13 the pair (1, 13) has 2574 = 13 · 198 invariants (the
    #    hook formula on (5, 4, 4): 13!/(840 · 120 · 24)) and reads 0, with 52 of the 117 nonzero counts of the window; below ϑ^p the
    #    coefficients of D3's series are computed in the arithmetic of the shell, by the recursion of the quotient on residues; from
    #    ϑ^p on k! reads 0, and no reading is stated.
    w13 = Y.window_readings(13)
    ok = w13["pairs"] == 351 and w13["nonzero"] == 117 and len(w13["zero"]) == 52 and w13["zero"][:2] == [(1, 13), (13, 1)]
    ok &= w13["count"][(1, 13)] == 2574 == 13 * 198 and 6227020800 == 2574 * (840 * 120 * 24)
    ok &= w13["residues"] == ([0, 9, 11, 0, 3, 7, 4, 10, 4, 3, 2, 5, 0], [0, 0, 5, 12, 0, 7, 8, 10, 9, 6, 2, 11, 3])
    ok &= w13["agree"] and w13["bound"] and w13["shift"]
    fact = {}
    for p, _ in LAB:
        r = 1
        for j in range(2, p): r = r * j % p                                     # (p − 1)!, every product reduced at once
        fact[p] = r
        ok &= r == p - 1 and (2 * pow(2, p - 2, p)) % p == 1 and (3 * pow(3, p - 2, p)) % p == 1
    ok &= all(sum(pow(p * p, i, p) for i in range(d)) % p == 1 for p, _ in LAB for d in (1, 2, 3, 8, 2574))   # the lines of a nonzero fixed space
    # 46:C24 (p46067)
    R.check("D5", "what a reading keeps of the window: on the Subject 13 the window has 351 pairs, 117 with a nonzero count, and 52 of these "
            "counts are multiples of 13, the first at (1, 13) with 2574 = 13 · 198 invariants (13!/(840 · 120 · 24) by the hook formula on "
            "(5, 4, 4)), so the count reads 0 on a space of 2574 independent invariants; below ϑ¹³ the coefficients of c₃ and c₈ are computed "
            "in the arithmetic of the shell, by the recursion of the quotient on residues from the residues of the counts, and read 0, 9, 11, "
            "0, 3, 7, 4, 10, 4, 3, 2, 5, 0 and 0, 0, 5, 12, 0, 7, 8, 10, 9, 6, 2, 11, 3; they are the residues of the rational coefficients, "
            "whose denominators divide 3 · k! and 8 · k!, and they are the same when every count moves by a multiple of 13; on "
            "the Subjects 13, 173, 1549 the factorial (p − 1)! reads p − 1 and 2, 3 have inverses, so the factors 2, 3 and 1, …, p − 1 of the "
            "denominators below ϑ^p are units; from ϑ^p on k! holds the factor p and reads 0, and no reading is stated; the count of "
            "invariant lines of a nonzero fixed space reads 1 for the dimensions 1, 2, 3, 8 and 2574 on the three Subjects, since every "
            "term of 1 + p² + … after the first reads 0", ok,
            f"13: zero-reading pairs by degree {w13['zero'][:6]}…; c₃ below ϑ¹³ reads {w13['residues'][0]}, c₈ reads {w13['residues'][1]}; "
            f"(p − 1)! reads {fact}")

    # D6 the series on the shell (D119, 12 November 2026; the push on T25). d_R c_R = Σ h_k ϑ^k/k! with integers h_k, whose recursion
    #    h_k = n_k − Σ_j C(k, j) d_j h_{k−j} has no division and runs on residues at every order. In the series' arithmetic every f with
    #    f(0) = 0 has f^p = 0 on the shell, so a reading that respects sums and products sends ϑ to 0; three finite expressions at channel unity differ
    c3, c8 = Y.c1_series(3, 25), Y.c_adj_series(24)
    h3 = [3 * Y._fact(k) * c for k, c in enumerate(c3)]; h8 = [8 * Y._fact(k) * c for k, c in enumerate(c8)]
    ok = all(x.denominator == 1 for x in h3 + h8) and h3[:8] == [0, 1, 1, 0, -5, -15, 21, 413] and h8[:8] == [0, 0, 2, 4, 0, -40, -148, 252]
    s = Y.shell_series(13, 25)
    ok &= s["h"] == [int(x) % 13 for x in h3] and s["product"] and not any(s["power"])        # beyond ϑ¹³ too; (3c₃)¹³ = 0
    for p, _ in LAB:                                                                           # (ϑ^k/k!)^p = Π_{i ≤ p} C(ik, k) · ϑ^{kp}/(kp)!
        for k in (1, 2, 3):
            f = 1
            for i in range(1, p + 1): f = f * comb(i * k, k) % p                                # reduced at once; k = 1 is p!
            ok &= f == 0 and comb(k * p, k) % p == 0
    inv = lambda x: pow(x % 13, 11, 13)
    a = [s["h"][k] * inv(3 * Y._fact(k)) % 13 for k in range(13)]
    N = sum(s["n"][k] * inv(3 * Y._fact(k)) for k in range(13)) % 13; D = sum(s["d"][k] * inv(Y._fact(k)) for k in range(13)) % 13
    sums = (sum(a) % 13, N * inv(D) % 13, 23 * inv(54) % 13)
    ok &= sums == (6, 4, 5)
    # 46:C26 (p46072)
    R.check("D6", "the series on the shell: d_R c_R = Σ h_k ϑ^k/k! with integers h_k through the orders 24 and 23 (0, 1, 1, 0, −5, −15, 21, 413 for c₃ and "
            "0, 0, 2, 4, 0, −40, −148, 252 for c₈); on the Subject 13 the recursion h_k = n_k − Σ_j C(k, j) d_j h_{k−j}, which has no division, gives on "
            "residues the residues of these integers through the order 24, beyond ϑ¹³, and the 13th power of 3c₃ under the binomial convolution has no "
            "nonzero coefficient; the factor Π_{i ≤ p} C(ik, k) of the p-th power of ϑ^k/k!, k = 1, 2, 3, reads 0 on 13, 173 and 1549 with its last "
            "term C(kp, k), and for k = 1 it is p!, so a reading that respects sums and products sends ϑ to 0; at channel unity on 13 the sum of the terms of c₃ below ϑ¹³ reads 6, the quotient of the two truncated sums reads 4 and "
            "the sum 23/54 of the computed terms through ϑ⁷ reads 5", ok,
            f"h(c₃) {[int(x) for x in h3[:8]]}, h(c₈) {[int(x) for x in h8[:8]]}; on 13 h_k reads {s['h']}; sums {sums}")


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

    # E4 the chart's cells (D111 and D112, 12 November 2026). The one-loop law is a law of powers: with W = e^{−8π²ϑ} a scale lower by gⁿ
    #    has W higher by g^{b₀n}, and W = e^{−8π²} at channel unity. The stiffness is the chart's logarithm of 1/W in the unit 8π²
    cc = CY.chart_cells(); th = {n: Q(repr(x)) for n, x in cc["cells"].items()}; step = Q(repr(cc["step"]))
    ok = cc["law"] and th[0] == 1 and Q("0.09656") < step < Q("0.09658") and th[10] > 0 > 1 - 11 * step
    ok &= Q("10.35") < Q(repr(cc["steps_to_one"])) < Q("10.36") and all(Y.drive_exponents_unique(p)[1] == 2 for p, _ in LAB)
    ok &= all((11 * n) < p - 1 for n in range(11) for p in (173, 1549)) and (11 * 10) // 12 == 9           # the exponent b₀n within one window, and its wraps on 13
    size = {n: Q(repr(cc["size"][n])) for n in (9, 0)}
    ok &= abs(size[9] - Q("1.75")) < Q("0.005") and abs(size[0] - Q("0.92")) < Q("0.005")
    # 46:B6 (p46070)
    R.check("E4", "[chart] the chart's cells: the one-loop law is a law of powers, W(w₂)/W(w₁) = (w₁/w₂)^{b₀} with W = e^{−8π²ϑ}, so a scale n "
            "drive steps below channel unity has W higher by g^{b₀n} and the stiffness ϑ_n = 1 − n b₀ ln g/8π², the chart's logarithm of 1/W in the "
            "unit 8π²; with b₀ = 11 and the drive g = 2 of the three laboratory Subjects one step is 0.0966, the stiffness is positive through n = 10 "
            "and W reaches 1 after 10.36 steps; the exponent 11n stays within one window of the drive on 173 and 1549 and wraps on 13; the cell's "
            "size a√σ on the computed terms is 1.75 at n = 9 and 0.92 at channel unity", ok,
            f"step {CY.fmt(step, 5)}; ϑ_n: " + ", ".join(f"{n}: {CY.fmt(th[n], 4)}" for n in sorted(th)) + f"; a√σ {CY.fmt(size[9])}, {CY.fmt(size[0])}", kind="CHART")


# ------------------------------------------------------------------------------------------------------------
@R.block("F", BLOCK["F"])
def block_F():
    """Block F — the minimal wrap (Phase 2, decision D5; the repair of 8 November): the exact adjoint identity, the chart's
    operator family against the three lattice determinations, and the chart's tension ratio."""
    # F1 the adjoint plaquette coefficient c₈ = ϑ²/8 + ϑ³/12 + 0·ϑ⁴ − ϑ⁵/24 + … and the exact ratio c₈/c₃² = (9/8)(1 − ϑ/3 +
    #    ϑ²/12 + ϑ³/12 + …): the ϑ¹ coefficient of c₈ vanishes (no singlet in 8 ⊗ 3 or 8 ⊗ 3̄) and its ϑ² coefficient is 2 · (1/2)/8
    #    — the adjoint wrap is two fundamental wraps up to the factor 9/8, with the ratio computed to order ϑ⁴; the two multiplicity identities
    #    behind it hold on the finite frame itself: the fixed vectors of 3^{⊗a} ⊗ 3̄^{⊗b} over F_4 under SU(3, F_2), a + b ≤ 4, equal
    #    the compact multiplicities (27-fields Lemma charlift at its enumerable instance)
    c8 = Y.c_adj_series(8); ratio = Y.adjoint_over_fundamental_squared(5)
    ok = c8[:6] == [Q(0), Q(0), Q(1, 8), Q(1, 12), Q(0), Q(-1, 24)]
    ok &= ratio == [Q(9, 8), Q(-3, 8), Q(3, 32), Q(3, 32), Q(7, 640)]
    ok &= [x / Q(9, 8) for x in ratio[:4]] == [Q(1), Q(-1, 3), Q(1, 12), Q(1, 12)]
    m = Y.frame_moments_f4(degree=4)
    ok &= all(fin == cpt for fin, cpt in m.values())
    E = lambda a, b: m[(a, b)][0]
    ok &= E(2, 1) + E(1, 2) - E(1, 0) - E(0, 1) == 0                                      # the ϑ¹ coefficient of c₈ on the frame
    ok &= E(3, 1) + 2 * E(2, 2) + E(1, 3) - E(2, 0) - 2 * E(1, 1) - E(0, 2) == 2        # 4 · E[(χχ̄ − 1)(Re χ)²] = 2 on the frame
    # 46:C9 (p46030)
    R.check("F1", "the adjoint wrap: the adjoint plaquette coefficient c₈(ϑ) = ϑ²/8 + ϑ³/12 − ϑ⁵/24 + … has no ϑ¹ term (no singlet "
            "in 8 ⊗ 3 or 8 ⊗ 3̄), and c₈/c₃² = (9/8)(1 − ϑ/3 + ϑ²/12 + ϑ³/12 + …) to order ϑ⁴: two fundamental wraps at leading order "
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

    # F3 the chart's tension ratio: σ₈/σ₃ = ln c₈ / ln c₃ at the chart's cells n = 10 to 5 (46:B6) lies between 1.97 and 2.03 and
    #    equals 2 at no cell — the chart reading of F1's exact ratio; the logarithm belongs here, not in F1
    vals = {n: Q(repr(v)) for n, v in CY.adjoint_ratio_table().items()}                  # the chart tier forms the floats
    ok = all(Q("1.97") < v < Q("2.03") for v in vals.values()) and all(v != 2 for v in vals.values())
    ok &= vals[9] < vals[10] and vals[9] < vals[8] < vals[7] < vals[6] < vals[5]
    ok &= all(abs(vals[n] - Q(x)) < Q("0.0005") for n, x in ((10, "1.976"), (9, "1.976"), (8, "1.982"), (7, "1.992"), (6, "2.006"), (5, "2.022")))
    R.check("F3", "[chart] the chart's tension ratio σ₈/σ₃ = ln c₈(ϑ)/ln c₃(ϑ), read on the computed terms at the chart's cells "
            "n = 10, 9, 8, 7, 6, 5 (B6): 1.976, 1.976, 1.982, 1.992, 2.006, 2.022 — within 2 % of two fundamental wraps and equal to "
            "2 at none of the six; the chart's reading of F1's ratio (9/8)(1 − ϑ/3 + …)", ok,
            ", ".join(f"n={n}: {CY.fmt(v, 4)}" for n, v in vals.items()), kind="CHART")

    # F4 the radial ratio of the operator form (T03 resolved, 8 November 2026): E₁/E₀ and E₂/E₀ of a|p| + ϰr are free of a and ϰ (the dilation
    #    symmetry); E₁/E₀ = 1.49 against the lattice 0⁺⁺*/0⁺⁺ = 1.54(11) (Morningstar–Peardon, r₀ masses) and the nucleon's N(1440)/N(939) = 1.53;
    #    the nonrelativistic ladder p²/2 + r has the Airy ratio a₂/a₁ = 4.088/2.338 = 1.75, outside the lattice bracket
    spec1 = CY.wrap_spectrum(1, 1, 3); spec2 = CY.wrap_spectrum(2, Q(9, 4), 3)
    q1 = Q(repr(spec1[1])) / Q(repr(spec1[0])); q2 = Q(repr(spec1[2])) / Q(repr(spec1[0])); q1b = Q(repr(spec2[1])) / Q(repr(spec2[0]))
    airy = Q("4.08795") / Q("2.33811"); roper = Q(1440, 939)
    ok = Q("1.49") < q1 < Q("1.493") and abs(q1 - q1b) < Q("0.002") and Q("1.86") < q2 < Q("1.87")
    ok &= abs(q1 - rl) < drl / 2 and airy > rl + drl and Q("1.74") < airy < Q("1.76")
    r20 = CY.LATTICE["m0pp_star_direct"][0] / CY.LATTICE["m0pp_over_sqrt_sigma_direct"][0]                        # the 2020 continuum ratio 5.855(41)/3.405(21)
    dr20 = Q("0.016")                                                                                             # its quoted error: the two relative errors in quadrature, the masses taken as uncorrelated
    dr20_max = r20 * (Q(41, 5855) + Q(21, 3405))                                                                  # the largest error any correlation allows (anticorrelated): the two terms added, exact
    ok &= Q("1.715") < r20 < Q("1.725") and r20 - q1 > 14 * dr20 and r20 - q1 > 10 * dr20_max and abs(airy - r20) < 2 * dr20
    ok &= abs(roper - q1) < Q("0.03") * q1
    # 46:P3 (p46043)
    R.check("F4", "[chart] the radial ratio of the operator form: E₁/E₀ = 1.49 and E₂/E₀ = 1.86 for every a and ϰ (the dilation symmetry, the same "
            "on (1, 1) and (2, 9/4) to 10⁻³), a property of the chart's operator form and of nothing in the frame; against the lattice "
            "0⁺⁺*/0⁺⁺ = 1.54(11) it lies within half a standard deviation, while the nonrelativistic ladder's Airy ratio 1.75 lies outside the "
            "bracket; the 2020 continuum determination 5.855(41)/3.405(21) = 1.72(2) (Athenodorou–Teper) excludes 1.49 by fourteen standard "
            "deviations with the two masses taken as uncorrelated (the quoted 0.016) and by more than ten for any correlation (the "
            "anticorrelated error 0.0226 is the largest); the Airy 1.75 lies within two of it under the same assumption and from 1.3 to 21 "
            "across the correlations, a comparison the covariance decides: the one-body form fails for the glueball, for every a and ϰ; the nucleon's "
            "N(1440)/N(939) = 1.53 lies within 3 %", ok,
            f"E₁/E₀ = {CY.fmt(q1, 4)} ((2, 9/4): {CY.fmt(q1b, 4)}), E₂/E₀ = {CY.fmt(q2, 4)}, lattice 1999 {CY.fmt(rl)} ± {CY.fmt(drl)}, "
            f"2020 {CY.fmt(r20, 3)} ± {CY.fmt(dr20, 3)} (at most ± {CY.fmt(dr20_max, 4)}), Airy {CY.fmt(airy, 4)}, Roper {CY.fmt(roper, 4)}", kind="CHART")


# ------------------------------------------------------------------------------------------------------------
@R.block("G", BLOCK["G"])
def block_G():
    """Block G — the two chart routes of the former task T01 (the push of 8 November 2026), both failing: results about the chart's objects, not about the finite theory (round 03)."""
    # G1 route (a): a|p| + ϰr − C/max(r, r_c) with C = C_A α_s. The Herbst bound: bounded below iff C ≤ 2a/π. The declared coupling
    #    α_s(√σ) = 1.007 gives C = 3.02 > 4/π: the cutoff cannot be removed (the grid at r_c = 1 cell gives 1.8, falling as r_c shrinks; the
    #    singular operator is unbounded below by Herbst's theorem, not by the grid; with the cutoff retained the operator has a ground state
    #    above −C/r_c).
    #    The coupling run to the bound state's mass gives a fixed point only above a cutoff: 3.54, 3.08, 2.61 at r_c = 1, 1/2, 1/4
    #    (in 1/√σ) and none at 1/8 — the number is the cutoff's, and the cell's size in units of 1/√σ is set by the stiffness of the cell
    r = CY.short_range_review(); dc = r["declared"]; fp = r["fixed"]                           # every number an exact rational of the chart's float
    ok = Q("3.0") < dc < Q("3.05") and dc > r["herbst_two"] and r["collapse_rc1"] < Q("1.9")
    ok &= fp["1"] is not None and Q("3.5") < fp["1"][0] < Q("3.6")
    ok &= fp["1/2"] is not None and Q("3.0") < fp["1/2"][0] < Q("3.15")
    ok &= fp["1/4"] is not None and Q("2.55") < fp["1/4"][0] < Q("2.7")
    ok &= fp["1/8"] is None
    ok &= all(v is None or v[1] < r["herbst_two"] for v in fp.values())                        # every fixed point lies below the two-body bound
    # the review of 8 November 2026: the regularised operator has a ground state at every cutoff (bounded below by −C/r_c); the collapse is
    #    the cutoff's removal; a failing iteration is not a proof of no root — the roots by bisection, both branches, and the one-body form
    coll = r["collapse"]
    ok &= Q("0.3") < coll["1/2"] < Q("0.5") and Q("-1.6") < coll["1/4"] < Q("-1.4") and Q("-4.4") < coll["1/8"] < Q("-4.2")
    ok &= all(coll[k] > r["bound"][k] for k in coll)                                            # the elementary lower bound −C/r_c
    low = r["low"]
    ok &= all(v is not None for v in low.values()) and Q("0.8") < low["1"] < Q("0.9") and Q("1.6") < low["1/4"] < Q("1.7")
    ok &= r["scan_max"] < Q("-0.15") and r["scan_n"] == 149 and Q("2.2") <= r["scan_at"] <= Q("2.3")   # at 1/8 cell the residual stays below −0.15 on the 149-energy scan, its maximum near 2.25
    one = r["one"]
    ok &= one["1"] is None and Q("2.4") < one["2"] < Q("2.6") and Q("3.0") < one["10"] < Q("3.1")
    # 46:C10 (p46037)
    R.check("G1", "[chart] the short-range route of the chart fails: with the declared coupling α_s(√σ) = 1.007 the two-adjoint term has C = C_A α_s = "
            "3.02 above the Herbst bounds 2/π (one-body) and 4/π (two-body), so the cutoff cannot be removed (E₀ = 1.8, 0.4, −1.5, −4.3 at "
            "1, 1/2, 1/4, 1/8 cells, falling as the cutoff shrinks — the singular operator is unbounded below by Herbst's theorem, not by the grid, "
            "whose spacing 18/241 resolves no cutoff below 1/16; with the cutoff retained the operator is bounded below by −C/r_c); with the coupling "
            "run by the one-loop law to the bound state's mass each form has fixed points at the larger sampled cutoffs and none found at the smaller — "
            "two bodies: 3.54, 3.08, 2.61 at r_c = 1, 1/2, 1/4 (each with a lower second root) and none found at 1/8 on a scan of 149 energies in "
            "[0.6, 8], a sampled finding; one body: 2.5 at r_c = 2, 3.0 at r_c = 10, none found at one cell — so the eigenvalue is the cutoff's, and the "
            "cell's size in units of 1/√σ is set by the stiffness of the cell, "
            "which no row fixes", ok,
            f"C_declared = {CY.fmt(dc, 3)}, collapse {CY.fmt(r['collapse_rc1'])}, {', '.join(CY.fmt(coll[k]) for k in ('1/2', '1/4', '1/8'))} at 1/2, 1/4, 1/8; "
            f"lower roots {', '.join(CY.fmt(v) for v in low.values())}; one-body r_c = 2, 10: {CY.fmt(one['2'])}, {CY.fmt(one['10'])}; fixed points " +
            ", ".join(f"r_c={rc}: " + (f"E₀={CY.fmt(v[0])} (C={CY.fmt(v[1])})" if v else "none") for rc, v in fp.items()), kind="CHART")

    # G2 route (b): the 0⁺⁺ channel of the strong-coupling expansion (the plaquette, the closed fundamental loop) with Münster's series
    #    to u⁷ and the tension at leading order, with u the sum of the computed terms of the frame's c₃ through ϑ⁷ at the chart's cells (46:B6). The orders 3, 5, 7 agree within 1 %
    #    at the cells n = 9 to 6; at n = 3 and at n = 2 one order alone lies in the lattice bracket 3.4–3.7; at channel unity the terms sum to u = 23/54
    pc = CY.plaquette_channel(); T = pc["table"]; U = pc["unity"]
    v = {n: {o: Q(repr(T[n]["orders"][o])) for o in (3, 5, 7)} for n in T}; sp = {n: Q(repr(T[n]["spread"])) / v[n][7] for n in T}
    u = {n: Q(repr(T[n]["u"])) for n in T}
    ok = all(abs(u[n] - Q(x)) < Q("0.00005") for n, x in ((9, "0.0465"), (8, "0.0842"), (7, "0.1246"), (6, "0.1671"), (4, "0.2553"), (3, "0.2994"), (2, "0.3425")))                              # the cells' u to four decimals
    ok &= Q("6.85") < v[9][7] < Q("6.95") and Q("6.15") < v[8][7] < Q("6.25") and Q("5.55") < v[7][7] < Q("5.65") and Q("5.05") < v[6][7] < Q("5.15")
    ok &= all(sp[n] < Q("0.01") for n in (9, 8, 7, 6)) and all(min(v[n].values()) > Q("3.7") for n in (9, 8, 7, 6, 4))
    inb = lambda x: Q("3.4") < x < Q("3.7")
    ok &= [inb(v[3][o]) for o in (3, 5, 7)] == [False, True, False] and [inb(v[2][o]) for o in (3, 5, 7)] == [True, False, False]
    ok &= all(abs(v[4][o] - Q(x)) < Q("0.05") for o, x in ((3, "4.3"), (5, "4.2"), (7, "4.2")))
    ok &= all(abs(v[n][o] - Q(x)) < Q("0.005") for n, o, x in ((3, 3, "3.98"), (3, 5, "3.60"), (3, 7, "3.79"), (2, 3, "3.64"), (2, 5, "2.87"), (2, 7, "3.36")))
    vu = {o: Q(repr(U["orders"][o])) for o in (3, 5, 7)}
    ok &= U["exact"] == Q(23, 54) and all(abs(vu[o] - Q(x)) < Q("0.005") for o, x in ((3, "2.95"), (5, "0.45"), (7, "2.82")))
    # 46:C11 (p46071)
    R.check("G2", "[chart] the plaquette channel of the chart fails: with the imported 0⁺⁺ series to u⁷ and u the sum of the computed terms of the frame's c₃ through ϑ⁷ at the chart's cells (B6), "
            "m/√σ = 6.9, 6.2, 5.6, 5.1 at the cells n = 9, 8, 7, 6 (u = 0.046, 0.084, 0.125, 0.167), the orders 3, 5, 7 agreeing within 1 %; at n = 4 "
            "the orders give 4.3, 4.2, 4.2, above the lattice bracket 3.4–3.7; at n = 3 (u = 0.299) they give 3.98, 3.60, 3.79 and at n = 2 they give "
            "3.64, 2.87, 3.36, one order alone inside and not the same one; at channel unity the terms sum to u = 23/54 and the orders give 2.95, 0.45, 2.82: the series' tail "
            "is not bounded", ok,
            ", ".join(f"n={n}: u={CY.fmt(u[n], 4)}, {CY.fmt(v[n][7])} (spread {CY.fmt(sp[n] * 100, 1)} %)" for n in sorted(T, reverse=True))
            + f"; channel unity by order: {CY.fmt(vu[3])}, {CY.fmt(vu[5])}, {CY.fmt(vu[7])}", kind="CHART")


# ------------------------------------------------------------------------------------------------------------
@R.block("H", BLOCK["H"])
def block_H():
    """Block H — the spectral amplitude of a plaquette (46:B4) and the transfer tally on the instance (the T09 record of 9 November
    2026): its finite properties and singular values (C16), its values and moments on the 216 elements (C17), the transfer
    tally's spectrum (C18). Every number is integer or finite-field arithmetic in Z[ζ₃] and F_4."""
    # H1 the amplitude's finite properties (46:C16): on every element of SU(3, F_2) the semisimple part by powers (U = U_s U_n, the
    #    exponent 4 for all 216), the eigenvalues of U_s in F_4, the trace's reduction Σλ_j = Tr U, the class-function property, the
    #    inverse-conjugation w(U⁻¹) = w̄(U), and on the 189 elements of even order the pattern (λ, λ, λ⁻²) with λ³ = 1 — here every such
    #    U_s is scalar, so w = 3η with η³ = 1 (2η + η⁻² = 3η); the full sum vanishes (3 | q + 1, the centre of order 3). On the Subjects
    #    the plane's cycle of p² − 1 units, its gcd with the Carrier's cycle Ω − 1, the centre of order 3 on 173 only, and the
    #    second cycle's order p² − p + 1 prime to Ω − 1 on all three: no phase of the second cycle is a Carrier phase (the order-157 amplitude
    #    ζ + ζ¹² + ζ¹⁴⁴ on the Subject 13, its paired weight 3 + six distinct nontrivial phases, not rational).
    amp = Y.spectral_amplitude_instance()
    dist, even, mom, tot = amp["distribution"], amp["even_order"], amp["moments"], amp["sum"]
    ok = sum(dist.values()) == 216 and tot == (0, 0) and amp["classes"] == 16
    ok &= sum(even.values()) == 189 and set(even) == {(3, 0), (0, 3), (-3, -3)}                 # every element of even order has w = 3η
    ok &= Y.z3_mul((0, 1), (0, 1)) == (-1, -1) and Y.z3_mul(Y.z3_mul((0, 1), (0, 1)), (0, 1)) == (1, 0)   # z² = −1 − z, z³ = 1
    tab = Y.subject_phase_table()
    ok &= [t["plane"] for t in tab] == [168, 29928, 2399400] and [t["gcd_plane_cycle"] for t in tab] == [8, 8, 40]
    ok &= [t["centre3"] for t in tab] == [False, True, False] and all(t["gcd_nonsplit_cycle"] == 1 for t in tab)
    n157, E157, pw157 = Y.nonsplit_amplitude_exponents(13)
    ok &= n157 == 157 and E157 == [1, 12, 144] and pw157 == {0: 3, 11: 1, 14: 1, 25: 1, 132: 1, 143: 1, 146: 1}
    ok &= Y.centre_order(2) == 3
    # the second cycle in the arithmetic of the plane alone (Proposition prop:amplitude(i), (ii)), for a matrix with the characteristic
    #    polynomial of a generator of that cycle: C is the companion matrix over F_p(√2) of x³ − t x² + t̄ x − 1 (a frame element with
    #    this characteristic polynomial is conjugate to it over the plane); C has the order m = p² − p + 1 and no eigenvalue on the plane
    #    (C^(p²) − C is invertible); C, D = C^(p²) and E = C^(−p) are the three roots of the polynomial: their sum is t·1, the sum of
    #    their pairwise products t̄·1 and their product 1, so C^k + D^k + E^k = Tr(C^k)·1 for every power; the powers are also run one
    #    by one over the whole cycle on 13 and 173
    z, o = (0, 0), (1, 0); pm_one = [o, z, z, z, o, z, z, z, o]; pm_scal = lambda c: [c, z, z, z, c, z, z, z, c]
    def pm_mul(Kx, P, Q):
        return [Kx.add(Kx.add(Kx.mul(P[3 * i], Q[j]), Kx.mul(P[3 * i + 1], Q[3 + j])), Kx.mul(P[3 * i + 2], Q[6 + j])) for i in range(3) for j in range(3)]
    def pm_pow(Kx, P, n):
        R = pm_one
        while n:
            if n & 1: R = pm_mul(Kx, R, P)
            P = pm_mul(Kx, P, P); n >>= 1
        return R
    pm_add = lambda Kx, P, Q: [Kx.add(a, b) for a, b in zip(P, Q)]
    cyc = {}
    for p, t in ((13, (9, 4)), (173, (166, 160)), (1549, (1275, 523))):
        Kx = Ext(p, 2); m = p * p - p + 1; tb = Kx.conj(t); C = [z, z, o, o, z, Kx.neg(tb), z, o, t]; mu = Kx.mul
        D = pm_pow(Kx, C, p * p); E = pm_pow(Kx, C, m - p)
        ok &= pm_pow(Kx, C, m) == pm_one and all(pm_pow(Kx, C, m // r) != pm_one for r in Y._factor(m))
        N = [Kx.sub(a, b) for a, b in zip(D, C)]                                # D − C, with a nonzero determinant
        det = Kx.add(Kx.sub(mu(N[0], Kx.sub(mu(N[4], N[8]), mu(N[5], N[7]))), mu(N[1], Kx.sub(mu(N[3], N[8]), mu(N[5], N[6])))),
                     mu(N[2], Kx.sub(mu(N[3], N[7]), mu(N[4], N[6]))))
        ok &= det != z and pm_add(Kx, pm_add(Kx, C, D), E) == pm_scal(t) and pm_mul(Kx, pm_mul(Kx, C, D), E) == pm_one
        ok &= pm_add(Kx, pm_add(Kx, pm_mul(Kx, C, D), pm_mul(Kx, D, E)), pm_mul(Kx, E, C)) == pm_scal(tb)
        cyc[p] = (m, None)
        if p in (13, 173):                                                        # every power of the cycle, one by one
            Pk, Qk, Rk = pm_one, pm_one, pm_one; bad = 0; tr = set()
            for k in range(m):
                tk = Kx.add(Kx.add(Pk[0], Pk[4]), Pk[8]); tr.add(tk)
                bad += pm_add(Kx, pm_add(Kx, Pk, Qk), Rk) != pm_scal(tk)
                Pk, Qk, Rk = pm_mul(Kx, Pk, C), pm_mul(Kx, Qk, D), pm_mul(Kx, Rk, E)
            ok &= bad == 0 and Pk == pm_one; cyc[p] = (m, len(tr))
    ok &= pm_pow(Ext(173, 2), [z, z, o, o, z, (7, 160), z, o, (166, 160)], 9919) == pm_scal((86, 155))   # the centre of order 3 on 173
    ok &= [cyc[p] for p in (13, 173, 1549)] == [(157, 53), (29757, 9921), (2397853, None)]
    # 46:C16 (p46056)
    R.check("H1", "the spectral amplitude's finite properties (Prop. prop:amplitude): on the 216 elements of SU(3, F_2) the semisimple part by "
            "powers (the exponent 4 for every element), the eigenvalues of U_s in F_4 with Σλ_j = Tr U, a class function with w(U⁻¹) = w̄(U); "
            "the 189 elements of even order have U_s scalar, w = 3η with η³ = 1 (2η + η⁻² = 3η), and the full sum over the group vanishes "
            "(a central element of order 3); on the Subjects the plane's cycle has p² − 1 = 168, 29928, 2399400 units with gcd(p² − 1, Ω − 1) = 8, 8, 40, a centre of "
            "order 3 on 173 only, and the order p² − p + 1 of the second cycle prime to Ω − 1 on all three: the order-157 amplitude ζ + ζ¹² + ζ¹⁴⁴ of the "
            "Subject 13 has no Carrier phase and its paired weight 3 + ζ¹¹ + ζ¹⁴ + ζ²⁵ + ζ¹³² + ζ¹⁴³ + ζ¹⁴⁶ is not rational; in the arithmetic of the "
            "plane alone the companion matrix C of x³ − t x² + t̄ x − 1, t = (9, 4), (166, 160), (1275, 523), the characteristic polynomial of a "
            "generator of the second cycle, has the order p² − p + 1 and no eigenvalue on the plane, and C, C^(p²), C^(−p) have the sum t·1, the "
            "sum of pairwise products t̄·1 and the product 1, so C^k + C^(kp²) + C^(−kp) = Tr(C^k)·1 for every power; the powers run one by one "
            "over the whole cycle on 13 and 173", ok,
            f"distribution {dict(sorted(dist.items()))}, even-order {dict(sorted(even.items()))}, sum {tot}, classes {amp['classes']}; " +
            "; ".join(f"p={t['p']}: p²−1={t['plane']}, gcd(p²−1,Ω−1)={t['gcd_plane_cycle']}, centre3={t['centre3']}, gcd(p²−p+1,Ω−1)={t['gcd_nonsplit_cycle']}" for t in tab) +
            f"; order-157 exponents {E157}, paired {dict(sorted(pw157.items()))}; the second cycle: " +
            ", ".join(f"p={p}: a cycle of {cyc[p][0]} powers, " + (f"run one by one, {cyc[p][1]} distinct traces" if cyc[p][1] else "not run one by one") for p in cyc))

    # H2 the amplitude on the instance (46:C17): the values 3, 3ζ₃, 3ζ₃² on 64 elements each and 0 on 24; the moments μ_{1,1}, μ_{3,0},
    #    μ_{2,2} = 8, 24, 72 against the invariant counts 1, 1, 2 of the frame (block A's residue series; frame_counts_small_field);
    #    the two involutions U = antidiag(1,1,1), V = antidiag(t, 1, t²) with w = 3 and w(UV) = 0, UV of order 3: no representation
    #    of dimension 3 over Q(ζ₃) has this character (an involution of character value 3 acts as the identity)
    counts = Y.frame_counts_small_field(2, 4)
    ok = dist == {(3, 0): 64, (0, 3): 64, (-3, -3): 64, (0, 0): 24}
    ok &= mom == {(1, 1): (8, 0), (3, 0): (24, 0), (2, 2): (72, 0)}
    ok &= (counts[(1, 1)], counts[(3, 0)], counts[(2, 2)]) == (1, 1, 2)
    U, V, wU, wV, wUV, oUV = amp["involutions"]
    ok &= wU == (3, 0) and wV == (3, 0) and wUV == (0, 0) and oUV == 3
    ok &= all(Y.element_order(amp["F"], X) == 2 for X in (U, V))
    # 46:C17 (p46057)
    R.check("H2", "the spectral amplitude on the instance (Thm. thm:amplitude): on the 216 elements the values 3, 3ζ₃, 3ζ₃² on 64 elements "
            "each and 0 on 24 (the 192 nonzero values from scalar semisimple parts); the moments (1/216) Σ w^a w̄^b at (1,1), (3,0), (2,2) are "
            "8, 24, 72 against the frame's invariant counts 1, 1, 2; the involutions U, V have w = 3 and their product of order 3 has w = 0, "
            "so w is the character of no representation over Q(ζ₃)", ok,
            f"distribution {dict(sorted(dist.items()))}; moments {mom}; counts {(counts[(1, 1)], counts[(3, 0)], counts[(2, 2)])}; w(U), w(V), w(UV) = {wU}, {wV}, {wUV}, ord(UV) = {oUV}")

    # H3 the transfer tally on the instance (46:C18): the step of one plaquette with the frame's mean, (Kf)(x) = ⟨w(x⁻¹y) f(y)⟩_y, on the
    #    216 elements. The matrix A = 216 K of the entries w(x⁻¹y) is in Z[ζ₃], by integer matrices: A(A + 72)(A − 36)(A − 144) = 0
    #    exactly, which is K(3K + 1)(6K − 1)(3K − 2) = 0; the nullities of A − λI for λ = 144, 36, 0, −72 are 9, 36, 144, 27 (modulo a
    #    prime ≡ 1 mod 3, each at least the exact one, and summing to 216 as the exact ones do), so K has the eigenvalues 2/3, 1/6, 0, −1/3
    #    with these multiplicities; tr K = 3 and tr K² = 8, the moment of 46:C17; K·1 = 0 (the trivial channel annihilated, so no ratio to
    #    it exists); the eigenvalue −1/3 and the quadratic value −1/72 at (1, −1, −1) on (I, U, V): not a positive operator
    T = Y.transfer_tally_instance(amp)
    mults = T["multiplicities"]; mean = T["mean"]
    ok = T["trace"] == (648, 0) and T["trace2"] == (373248, 0) and T["annihilated"] and T["K_one_zero"]
    ok &= mults == {144: 9, 36: 36, 0: 144, -72: 27} and sum(mults.values()) == 216
    ok &= mean["eigenvalues"] == {Q(2, 3): 9, Q(1, 6): 36, Q(0): 144, Q(-1, 3): 27}
    ok &= mean["trace"] == (3, 0) and mean["trace2"] == (8, 0) and mean["trace2"][0] == mom[(1, 1)][0]
    ok &= sum(e * m for e, m in mean["eigenvalues"].items()) == 3 and sum(e * e * m for e, m in mean["eigenvalues"].items()) == 8
    ok &= mean["quadratic"] == (Q(-1, 72), 0) and Y.transfer_annihilator_coefficients() == [0, 373248, -7776, -108, 1]
    ok &= Y.transfer_annihilator_mean() == [0, 2, -9, -27, 54]
    # 46:C18 (p46058)
    R.check("H3", "the transfer tally on the instance (Thm. thm:transfer): the step of one plaquette with the frame's mean, (Kf)(x) = ⟨w(x⁻¹y) f(y)⟩_y, "
            "on SU(3, F_2) has the eigenvalues 2/3, 1/6, 0, −1/3 with multiplicities 9, 36, 144, 27 — K(3K + 1)(6K − 1)(3K − 2) = 0, decided "
            "exactly in Z[ζ₃] on the matrix 216 K of the entries w(x⁻¹y), tr K = 3, tr K² = 8 — the trivial channel annihilated (K·1 = 0), and "
            "with the eigenvalue −1/3 and the quadratic value −1/72 on (I, U, V) it is not a positive operator", ok,
            f"eigenvalues {{{', '.join(f'{e}: {m}' for e, m in mean['eigenvalues'].items())}}}; tr K = {mean['trace'][0]}, tr K² = {mean['trace2'][0]}; annihilated {T['annihilated']}; "
            f"K·1 = 0: {T['K_one_zero']}; quadratic {mean['quadratic'][0]}; polynomial {Y.transfer_annihilator_mean()}; on 216 K: traces {T['trace']}, {T['trace2']}, multiplicities {mults}")


    # H4 the transfer tally on the Subjects (46:C19): the amplitude's character expansion w = χ₁ + χ₂ − χ₃ (the first members of the
    #    families of degrees q² − q + 1, q³ + 1, (q+1)²(q−1) of the generic character table, A15), by exact character sums over the eight
    #    class types on q = 3, 4, 5, 7, 13, 173, 1549 — the coefficients 1, 1, −1, the moment Σ a² = 3 (so no other character occurs),
    #    the trivial coefficient 0 (the frame's mean of w is 0); the same five sums from the explicit class list traced down from its exponent tables
    #    on q ≤ 13; the spectrum of the step with the frame's mean on the three Subjects: the eigenvalues 1/(q²−q+1), 1/(q³+1),
    #    −1/((q+1)²(q−1)) with multiplicities the squared degrees, tr K = Σ d²e = 3, tr K² = Σ d²e² = 3, a zero eigenvalue of positive
    #    multiplicity, the third eigenvalue negative; Σ a χ(1) = 3 as the identity (q² − q + 1) + (q³ + 1) = (q+1)²(q−1) + 3 on
    #    1 ≤ q ≤ 2000. The orders of the laboratory frames enter the multiplicity of the zero eigenvalue only
    frames = (3, 4, 5, 7, 13, 173, 1549)
    coef = {q: Y.amplitude_coefficients(q) for q in frames}
    ok = all(coef[q] == {"a1": 1, "a2": 1, "a3": -1, "moment": 3, "trivial": 0} for q in frames)
    direct = {q: Y.amplitude_coefficients_direct(q) for q in (3, 4, 5, 7, 13)}
    ok &= all({k: direct[q][k] for k in ("a1", "a2", "a3", "moment", "trivial")} == coef[q] for q in direct)
    ok &= [direct[q]["classes"] for q in (3, 4, 5, 7, 13)] == [14, 22, 40, 58, 184]
    spec = {p: Y.transfer_spectrum_subject(p) for p in (13, 173, 1549)}
    ok &= all(spec[p]["ok"] for p in spec)
    ok &= spec[13]["eigenvalues"] == (Q(1, 157), Q(1, 2198), Q(-1, 2352))
    ok &= spec[173]["eigenvalues"] == (Q(1, 29757), Q(1, 5177718), Q(-1, 5207472))
    ok &= spec[1549]["eigenvalues"] == (Q(1, 2397853), Q(1, 3716672150), Q(-1, 3719070000))
    ok &= spec[13]["degrees"] == (157, 2198, 2352) and spec[13]["zero"] == 800885251
    ok &= all((q * q - q + 1) + (q ** 3 + 1) == (q + 1) ** 2 * (q - 1) + 3 for q in range(1, 2001))
    ident = [Y.amplitude_identity_classwise(q) for q in (3, 4, 5, 7, 8, 9, 11, 13, 16, 17, 19, 23, 25, 27, 29, 31, 32)]
    ok &= all(i["ok"] for i in ident) and sum(i["classes"] for i in ident) == 6518
    # 46:C19 (p46061)
    R.check("H4", "the transfer tally on the Subjects (Thm. thm:subjects): w = χ₁ + χ₂ − χ₃ holds class by class on the class lists of the "
            "17 prime powers 3 ≤ q ≤ 32 (6518 classes), the identity of the proof for every q ≥ 3; on q = 3, 4, 5, 7, 13, 173, 1549 the exact character sums give "
            "w = χ₁ + χ₂ − χ₃ on the first members of the families of degrees q² − q + 1, q³ + 1, (q+1)²(q−1), with Σ a² = 3 (no other "
            "character) and the frame's mean of w equal to 0; the sums from the explicit class list agree on q ≤ 13; the step with the frame's "
            "mean has the eigenvalues 1/(q²−q+1), 1/(q³+1), −1/((q+1)²(q−1)) with multiplicities the squared degrees on 13, 173, 1549 "
            "(1/157, 1/2198, −1/2352 on 13), tr K = 3, tr K² = 3, a zero eigenvalue of positive multiplicity, the third eigenvalue negative; "
            "Σ a χ(1) = 3 on 1 ≤ q ≤ 2000", ok,
            f"identity class by class: {sum(i['classes'] for i in ident)} classes, {sum(i['failures'] for i in ident)} failures; "
            + "; ".join(f"q={q}: {coef[q]}" for q in frames) + "; direct " + "; ".join(f"q={q}: {direct[q]['classes']} classes, N={direct[q]['N']}" for q in direct)
            + "; " + "; ".join(f"p={p}: eigenvalues {', '.join(str(e) for e in spec[p]['eigenvalues'])}, zero multiplicity {spec[p]['zero']}" for p in spec))

    # H5 the tally of the ring and the gap of the transfer tally (46:C20): the tally is the frame's mean over the rungs (46:B3), and one
    #    plaquette multiplies the terms of χ₁, χ₂, χ₃ by 1/d₁, 1/d₂, −1/d₃, the eigenvalues of 46:C19; on the seven frames d₂ = (q+1) d₁,
    #    d₃ = (q+1)(q² − 1) and d₃ − d₂ = (q+1)(q−2) > 0, so 1/d₁ > 1/d₂ > 1/d₃ and the gap is d₁/d₂ = 1/(q+1), the third ratio
    #    d₁/d₃ = (1/(q+1)) (q²−q+1)/(q²−1); the degrees are 1, 1, −1 modulo q, so the three multipliers reduce to 1; the table's
    #    characters on the classes with the eigenvalues g^k, 1, g^{−k} (g^{2k} ≠ 1) are 1, ζ^k + ζ^{−k}, 0 for every such k; the tally of
    #    one plaquette on those classes 1/d₁ + (1/d₂)(ζ^j + ζ^{−j})(ζ^k + ζ^{−k}) as an exponent table (on the Subject 13); with unit
    #    boundary links the tally is tr Kⁿ = Σ aⁿ d^{2−n}: 3, 3 and 1/d₁ + 1/d₂ − 1/d₃ for n = 1, 2, 3; the gluing identity of the ring
    #    on the instance SU(3, F_2), n = 2, by brute force over the rungs on six boundary words in Q(ζ₃), with no character table.
    #    No order of a frame enters the statements on the seven frames. On a Subject the multipliers are framed rationals with the
    #    residue 1 modulo p, so every coefficient has the residue 1 and the tally is the same for every number of plaquettes:
    #    1 + (g^j + g^{−j})(g^k + g^{−k}) on the classes above — 10, 163, 1367 at g = 2, (j, k) = (1, 2) on 13, 173, 1549 — the paired
    #    weight its square, and 3 with unit boundary links; the exact tally of one plaquette reduces to it. At any boundary classes:
    #    on every class of the table's list each value of χ₁, χ₂, χ₃ under e ↦ −e equals its value under e ↦ q·e (the seven frames,
    #    the three Subjects among them), so the reduction of the conjugate value is the p-th power of the reduced value, the reduced
    #    tally lies in the quadratic extension K of the Subject, and the paired weight reduces to its norm, a residue of the shell;
    #    with h₁ = s₁ and h₂ of the eigenvalues √2, −√2/2, −1, outside the shell, the reduced tally is −1 − (5/4)√2 in K = F_p(√2),
    #    outside the shell, and its norm is the residue of −17/8: 6, 106, 966 on the three Subjects
    step = {q: Y.ring_step(q) for q in frames}
    gap = {q: Y.ring_gap(q) for q in frames}
    ok = all(gap[q]["ok"] for q in frames)
    ok &= [gap[p]["gap"] for p in (13, 173, 1549)] == [Q(1, 14), Q(1, 174), Q(1, 1550)]
    ok &= step[13]["multipliers"] == (Q(1, 157), Q(1, 2198), Q(-1, 2352)) and all(step[p]["multipliers"] == spec[p]["eigenvalues"] for p in spec)
    regular = {}
    for q in frames:
        vals = [Y.split_torus_characters(q, k) for k in range(1, q - 1)]
        reg = [(k, v) for k, v in zip(range(1, q - 1), vals) if v is not None]
        ok &= all(v == {"chi1": (0,), "chi2": tuple(sorted((k % (q - 1), (-k) % (q - 1)))), "chi3": ()} for k, v in reg)
        ok &= all((v is None) == ((2 * k) % (q - 1) == 0) for k, v in zip(range(1, q - 1), vals))
        regular[q] = len(reg)
    ok &= regular[3] == 0 and regular[4] == 2 and regular[13] == 10
    Z1 = Y.ring_step_split(13, 1, 2)
    ok &= Z1 == {0: Q(1, 157), 11: Q(1, 2198), 3: Q(1, 2198), 9: Q(1, 2198), 1: Q(1, 2198)}
    unit = {}
    for q in frames:                                  # the unit boundary: tr Kⁿ = Σ aⁿ d^{2−n} for n = 1, 2, 3, by the step from n = 1
        d = step[q]["degrees"]; e = step[q]["multipliers"]
        term = [dd * dd * ee for dd, ee in zip(d, e)]                     # n = 1: χ(1)² a/d
        t1 = sum(term); term = [t * ee for t, ee in zip(term, e)]; t2 = sum(term); term = [t * ee for t, ee in zip(term, e)]; t3 = sum(term)
        ok &= (t1, t2) == (3, 3) and t3 == Q(1, d[0]) + Q(1, d[1]) - Q(1, d[2])
        unit[q] = t3
    glue = Y.ring_gluing_instance(amp)
    ok &= glue["ok"]
    resid = {p: Y.ring_residue(p, 1, 2) for p in (13, 173, 1549)}             # the framed rational arithmetic of the Subject, modulo p
    ok &= all(resid[p]["ok"] for p in resid)
    ok &= [resid[p]["tally"] for p in (13, 173, 1549)] == [10, 163, 1367] and [resid[p]["paired"] for p in (13, 173, 1549)] == [9, 100, 595]
    def moved(terms, N, m):                                                 # the exponent table of a value under e ↦ m·e
        t = {}
        for c, e in terms: t[(m * e) % N] = t.get((m * e) % N, 0) + c
        return {e: c for e, c in t.items() if c}
    conj_ok = {}
    for q in frames:                                                          # the conjugate value is the value with every exponent times q, class by class
        classes, N = Y.su3_class_list(q)
        conj_ok[q] = all(moved(v, N, -1) == moved(v, N, q) for cl in classes for v in cl[2:5])
        del classes                                                           # the list of the Subject 1549 holds 2,400,952 classes
    ok &= all(conj_ok.values())
    plane = {}
    for p in (13, 173, 1549):                                                 # h₁ = s₁ and h₂ of the eigenvalues √2, −√2/2, −1, in K = F_p(√2)
        Kx = Ext(p, 2); half = pow(2, -1, p); mu = (0, 1); e2 = Kx.inv(Kx.conj(mu)); e3 = Kx.mul(Kx.conj(mu), Kx.inv(mu))   # μ, μ^{−p}, μ^{p−1}
        ok &= e2 == (0, (-half) % p) and e3 == ((-1) % p, 0) and Kx.mul(Kx.mul(mu, e2), e3) == (1, 0)
        b1, b2 = e3, Kx.add(mu, e2)                                           # the reduced χ₁, χ₂ at h₂ (the table's entry of type 7; χ₃ = 0)
        a1, a2 = (1, 0), ((2 + half) % p, 0)                                  # at s₁: 1 and g + g⁻¹, g = 2
        red = Kx.add(Kx.mul(a1, Kx.conj(b1)), Kx.mul(a2, Kx.conj(b2)))        # Σ χ̄ᵢ(h₁) χ̄ᵢ(h₂⁻¹), every coefficient reading 1
        redc = Kx.add(Kx.mul(Kx.conj(a1), b1), Kx.mul(Kx.conj(a2), b2))       # the reduction of the conjugate tally
        ok &= red == ((-1) % p, (-5 * pow(4, -1, p)) % p) and red[1] != 0 and redc == Kx.conj(red) and Kx.pow(red, p) == Kx.conj(red)
        ok &= Kx.mul(red, redc) == (Kx.norm(red), 0) and Kx.norm(red) == (-17 * pow(8, -1, p)) % p
        plane[p] = (red, Kx.norm(red))
    ok &= [plane[p] for p in (13, 173, 1549)] == [((12, 2), 6), ((172, 42), 106), ((1548, 386), 966)]
    # 46:C20 (p46062)
    R.check("H5", "the tally of the ring and the gap of the transfer tally (Thm. thm:ring): the tally is the frame's mean over the rungs, and one "
            "plaquette multiplies the terms of χ₁, χ₂, χ₃ by 1/d₁, 1/d₂, −1/d₃; on q = 3, 4, 5, 7, 13, 173, 1549 the degrees have "
            "d₂ = (q+1) d₁, d₃ = (q+1)(q² − 1) and d₃ > d₂, so the gap is d₁/d₂ = 1/(q+1) — 1/14, 1/174, 1/1550 on the Subjects — the third "
            "ratio is (1/(q+1)) (q²−q+1)/(q²−1), and the degrees are 1, 1, −1 modulo q; on the classes with the eigenvalues g^k, 1, g^{−k} "
            "(g^{2k} ≠ 1) the table's entry of type 7 gives the characters 1, ζ^k + ζ^{−k}, 0 for every such k (none at q = 3); the tally of one "
            "plaquette there is 1/d₁ + (1/d₂)(ζ^j + ζ^{−j})(ζ^k + ζ^{−k}), evaluated on 13; with unit boundary links the tally is 3, 3 and "
            "1/d₁ + 1/d₂ − 1/d₃ for one, two and three plaquettes; modulo p on the Subjects the three multipliers are framed rationals with the "
            "residue 1, so the tally is the same for every number of plaquettes, 1 + (g^j + g^{−j})(g^k + g^{−k}) on those classes — 10, 163, 1367 "
            "at g = 2, (j, k) = (1, 2) — and 3 with unit boundary links; at any boundary classes the reduced tally lies in the quadratic "
            "extension K of the Subject, the reduction of the conjugate tally is its conjugate there (on every class of the table's list the "
            "conjugate value of χ₁, χ₂, χ₃ is the value with both roots of unity raised to the power q, on the seven frames), and the paired weight reduces to its norm, a "
            "residue of the shell — with h₁ = s₁ and h₂ of the eigenvalues √2, −√2/2, −1, outside the shell, the reduced tally is −1 − (5/4)√2 "
            "and the paired weight reduces to −17/8: 6, 106, 966 on 13, 173, 1549; decided directly, with no character table: the gluing identity of the "
            "ring on SU(3, F_2), n = 2, on six boundary words by brute force over the rungs in Q(ζ₃)", ok,
            "; ".join(f"q={q}: gap {gap[q]['gap']}, third {gap[q]['third']}, {regular[q]} classes, three plaquettes {unit[q]}" for q in frames)
            + f"; Z₁(s₁,s₂) on 13: {{{', '.join(f'{e}: {v}' for e, v in sorted(Z1.items()))}}}; instance, means: "
            + ", ".join(f"({v['mean'][0]}, {v['mean'][1]})" for v in glue["values"])
            + "; modulo p: " + ", ".join(f"p={p}: tally {resid[p]['tally']}, paired weight {resid[p]['paired']}" for p in resid)
            + "; with eigenvalues outside the shell: "
            + ", ".join(f"p={p}: reduced tally {plane[p][0][0]} + {plane[p][0][1]}√2, paired weight {plane[p][1]}" for p in plane))
    # H6 the spectrum in 2π (46:C21): on the three Subjects the degrees, the gap and the third ratio as expressions in π = (p − 1)/2,
    #    the residues 2π ≡ −1 and 2π + 2 ≡ 1 modulo p, the orders of the two cycles of H1 as expressions in 2π, and the chart's
    #    numeral 0.1207 by a rational enclosure of the classical π
    sp = {p: Y.spectrum_in_pi(p) for p in (13, 173, 1549)}
    ok = all(sp[p]["ok"] for p in sp) and [sp[p]["pi"] for p in (13, 173, 1549)] == [6, 86, 774]
    ok &= [sp[p]["degrees"][0] for p in (13, 173, 1549)] == [157, 29757, 2397853]
    ok &= [sp[p]["gap"] for p in (13, 173, 1549)] == [Q(1, 14), Q(1, 174), Q(1, 1550)]
    orders = {t["p"]: (t["plane"], t["nonsplit"]) for t in Y.subject_phase_table()}             # the two cycles of H1
    ok &= all(sp[p]["cycles"] == orders[p] for p in sp)
    ok &= [sp[p]["cycles"] for p in (13, 173, 1549)] == [(168, 157), (29928, 29757), (2399400, 2397853)]
    # 46:C21 (p46064)
    R.check("H6", "the spectrum in 2π (Cor. cor:pi): with 2π = p − 1 the phase cycle of the shell, π = 6, 86, 774 on the Subjects 13, 173, "
            "1549, the degrees are d₁ = 4π² + 2π + 1, d₂ = (2π + 2) d₁, d₃ = 8π(π + 1)², the gap of the transfer tally is 1/(2π + 2) and the "
            "third ratio is (4π² + 2π + 1)/(8π(π + 1)²), pure numbers and one expression on every Subject; the two cycles of Def. "
            "def:amplitude have the orders 2π(2π + 2) = p² − 1 and 4π² + 2π + 1 = p² − p + 1, the second the numeral of d₁; "
            "2π ≡ −1 and 2π + 2 ≡ 1 modulo p, "
            "the residue 1 of the levels; [chart] with the classical π in (3.1415926, 3.1415927) the gap lies in (0.12072, 0.12073), by "
            "rational arithmetic", ok,
            "; ".join(f"p={p}: π={sp[p]['pi']}, d₁={sp[p]['degrees'][0]}, gap {sp[p]['gap']}, third {sp[p]['third']}, "
                      f"cycles {sp[p]['cycles'][0]} and {sp[p]['cycles'][1]}" for p in sp))
    # H7 the product channels (46:C22): the fixed dimensions of 8^{⊗n} by the binomial inversion of the counts M(k, k), the compact
    #    counts on the Subjects (the window 46:C15) and the direct three-step count on the instance, with the counts of invariant lines
    pc = Y.product_channels()
    # 46:C22 (p46065)
    R.check("H7", "the product channels (Prop. prop:products): where 3 is invertible 3 ⊗ 3̄ = 1 ⊕ 8, so the frame fixes "
            "A_n = Σ_k (−1)^{n−k} C(n, k) M(k, k) dimensions of 8^{⊗n}; on the Subjects 13, 173, 1549 the counts M(k, k) are the compact "
            "1, 1, 2, 6, 23 (degree at most 8 ≤ 2p − 1), so A = 0, 1, 2, 8: two mesons and three gluons have d = 2 and p² + 1 = 170, 29930, "
            "2399402 invariant lines, a meson and a glueball d = 3, two glueballs d = 8; on the 216 elements of SU(3, F_2) the diagonal torus "
            "fixes 2, 22, 170, 1366 dimensions of 8^{⊗n}, n = 1, …, 4, the normal subgroup of order 27 fixes 0, 8, 56, 456 and the frame "
            "0, 1, 7, 57, so M(k, k) = 1, 1, 2, 11, 92: three gluons have d = 7 and 5461 lines, a meson and a glueball d = 8, two glueballs "
            "d = 57 — the instance departs beyond degree 4", pc["ok"],
            "; ".join(f"{k}: d = {v[0]} on the Subjects, {v[1]} on the instance" for k, v in pc["channels"].items()))
    # H8 the tally with the same boundary links at every step (46:C23): the boundary classes are those of t^n and b^n, read from the
    #    table's entries at the unit, at a = −1 and on the split torus; the five powers at the regular lengths, the other lengths
    ub = {p: Y.uniform_boundary_tally(p, 1, 2) for p, _ in Y.LAB_PAIRS}
    more = [Y.uniform_boundary_tally(13, j, k) for j in range(1, 12) if j != 6 for k in range(1, 12) if k != 6]
    more += [Y.uniform_boundary_tally(173, 2, 5), Y.uniform_boundary_tally(1549, 3, 1)]
    ok = (all(u["ok"] for u in ub.values()) and all(u["ok"] for u in more)
          and ub[13]["values"] == (10, 0, 0, 2, 5, 12, 5, 2, 0, 0, 10, 3)
          and ub[13]["five"] == (10, 0, 1, 2, 5, 10, 5, 2, 1, 0, 10, 5) and ub[13]["paired"] == (9, 0, 0, 4, 12, 1, 12, 4, 0, 0, 9, 9)
          and ub[13]["coefficients"] == (3, 5, 11, 5, 2, 4, 11, 4, 2, 5, 11, 5)
          and [ub[p]["period"] for p in (13, 173, 1549)] == [12, 172, 1548] and Y.uniform_boundary_tally(13, 2, 4)["period"] == 6
          and [ub[p]["others"] for p in (13, 173, 1549)] == [(3, 6, 9, 12), (43, 86, 129, 172), (387, 774, 1161, 1548)])
    # 46:C23 (p46066)
    R.check("H8", "the tally with the same boundary links at every step (Prop. prop:uniform): with t and b in the classes s_j, s_k at "
            "every step the boundary classes are those of t^n and b^n; on the Subjects 13, 173, 1549 with (j, k) = (1, 2), on 13 for "
            "all 100 pairs j, k with g^{2j}, g^{2k} ≠ 1 and on two further pairs, the table's entries give at every regular length the residue "
            "1 + g^{(j+k)n} + g^{−(j+k)n} + g^{(j−k)n} + g^{−(j−k)n}; the other lengths are those with g^{2jn} = 1 or g^{2kn} = 1, with "
            "the residues 1 + c(y), −c(y), 3, 1, −1; at the length p − 1 the residue is 3; on 13 the lengths 1 to 12 read 10, 0, 0, 2, "
            "5, 12, 5, 2, 0, 0, 10, 3, and the other lengths are the multiples of 3, 43, 387 on the three Subjects; the least period is "
            "(p − 1)/gcd(j, k, p − 1) and a period of the paired weight, 12 for (1, 2) and 6 for (2, 4) on 13; the residue is Σ_r F_r g^{rn} "
            "with F_r = 0 unless gcd(j, k, p − 1) divides r, and on 13 the coefficients for (1, 2) are 3, 5, 11, 5, 2, 4, 11, 4, 2, 5, 11, 5", ok,
            "; ".join(f"p={p}: other lengths {ub[p]['others']}, least period {ub[p]['period']}" for p in ub))
    # H9 three rings on common links (46:C25): the numbers of invariants of the triples of characters from the class lists, their
    #    forms in q, and on the Subjects the residue of the tally on the split classes
    powers = (3, 4, 5, 7, 8, 9, 13, 16, 19, 25, 27, 31, 37, 43, 49, 61, 64, 67, 73, 79, 81,
              11, 17, 23, 29, 32, 41, 47, 53, 59, 71, 83, 89, 101, 107, 113, 125, 173)
    ok = all(Y.triple_multiplicities(q) == Y.triple_multiplicity_forms(q) for q in powers)
    ok &= sum(1 for q in powers if q >= 9 and (q + 1) % 3) >= 16 and sum(1 for q in powers if q >= 9 and (q + 1) % 3 == 0) >= 16
    cube = lambda f: (f[(1, 1, 1)] + 3 * f[(1, 2, 2)] - 6 * f[(1, 2, 3)] + 3 * f[(1, 3, 3)] + f[(2, 2, 2)] - 3 * f[(2, 2, 3)]
                      + 3 * f[(2, 3, 3)] - f[(3, 3, 3)] + 3 * f[(1, 1, 2)] - 3 * f[(1, 1, 3)])
    ok &= all(cube(Y.triple_multiplicity_forms(q)) == 6 for q in powers + (1549,))
    tr = {p: Y.three_rings_tally(p, 1, 2, 3) for p, _ in Y.LAB_PAIRS}
    more3 = [Y.three_rings_tally(13, j, k, l) for j in (1, 2, 4, 5) for k in (1, 2, 3) for l in (1, 4, 5)]
    more3 += [Y.three_rings_tally(173, 2, 5, 7), Y.three_rings_tally(1549, 3, 1, 8)]
    ok &= (all(t["ok"] for t in tr.values()) and all(t["ok"] for t in more3)
           and [tr[p]["W"][0] for p in (13, 173, 1549)] == [6, 25, 616] and [tr[p]["n122"] for p in (13, 173, 1549)] == [2, 4, 2]
           and tr[13]["W"] == (6, 0, 0, 0, 9, 1, 9, 0, 0, 0, 6, 6) and tr[13]["regular"] == (1, 5, 7, 11))
    # 46:C25 (p46068)
    R.check("H9", "three rings on common links (Prop. prop:triple): the numbers N(i, j, k) of invariants of the frame in the products of "
            "three of the characters χ₁, χ₂, χ₃, from the class lists at 37 prime powers and on the Subject 173, are 1, 0, 0, e + 1, e, e, "
            "eq, e(q + 1), e(q + 2), e(q + 1) + (e² − 1)/2 with e = gcd(3, q + 1), sixteen prime powers q ≥ 9 for each value of e; "
            "Σ a_i a_j a_k N(i, j, k) = 6, the mean of w³; on the Subjects 13, 173, 1549, with the same boundary link at every step in the "
            "classes s_1, s_2, s_3, the tally's residue at every length whose three classes are regular is 1 + N(1,2,2) (c_x c_y + c_x c_z + "
            "c_y c_z), c_m = m + m⁻¹, with N(1,2,2) = 2, 4, 2 and N(2,2,2) of the residue 0; the first length reads 6, 25, 616; with unit "
            "links the residue is 6; on 13 the lengths 1 to 12 read 6, 0, 0, 0, 9, 1, 9, 0, 0, 0, 6, 6 and the regular ones are 1, 5, 7, 11; "
            "the same on 36 further triples of classes on 13 and on one each on 173 and 1549", ok,
            "; ".join(f"p={p}: N(1,2,2) = {tr[p]['n122']}, first length {tr[p]['W'][0]}, {len(tr[p]['regular'])} regular lengths" for p in tr))


if __name__ == "__main__":
    args = [a for a in sys.argv[1:] if not a.startswith("--")]
    if args:
        for b in args: R.run_block(b)
        ok = R.summary(write=False)
    else: ok = R.verify_all()
    sys.exit(0 if ok else 1)
