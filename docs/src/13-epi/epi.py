"""
epi.py — the validation package of "Finite Field Realisation of the Classical Constants π and e" (Akhtman, 2026; Preprints
doi 10.20944/preprints202607.1141.v1), the paper 13-epi of the FRC corpus (finite-ring-space/src/13-epi); one script since
24 September 2026 (the registry epicommon.py and the six suites validate_e, validate_pi, validate_pi2, validate_towers,
kurepa_wall, frame_invariants merged; the two C passes stay beside it as kurepa_wall.c and frame_invariants.c, compiled on the
fly — a pure-python pass to a smaller bound runs without a compiler).
========================================================================================================================

One script, six blocks, forty family checks of exact micro-checks, standard library only. Every check is exact: integers,
residues, exact rationals (fractions.Fraction); the external targets e and π enter only as certified rational brackets of
the paper's own chains (the subfactorial chain for e, the Machin chain for π), and the binary64 constants enter as the
objects of study of the readout theorems (compared exactly with correctly rounded framed rationals). No floating-point
reference value of either constant decides any check; the few floating-point figures printed (a Pearson correlation, a
median, the Gauss sums) are [approx]-tagged diagnostics of the paper and decide nothing.

A check of the registry is a *family* of micro-checks — one labelled claim of a block (e.R1, pi.W1, pi2.B2, tow.H,
kur.K1, …) — and names the predicate(s) of the paper's ledger it witnesses (LEDGER; predicates cited as 13:XN); the
deciding family's `# 13:XN (<key>)` marker is what the ledger's source column links (PREDICATES;
finitering.space/src/13-epi/epi.html#<key>). Master-ledger predicates reached through the paper predicates: 00:B8
(13:J1, 13:J3), 00:B9 (13:J4, 13:J5), 00:C13 (13:J3), 00:C14 (13:B2, 13:H2), 00:B1 (13:B4), 00:C24 (13:G7 with A8, the
third-order wall) and 00:C26 (13:E5, the four chains as E- and G-partial sums); 13:Y1 and 13:Y3 are the paper's
hypotheses (block Y, tag O).

    python3 epi.py                every block, results.json written; exit 1 if a family check fails (≈ 40 s, ≈ 30 s of it the C pass over 22 043 primes)
    python3 epi.py pi tow         the blocks named (e, pi, pi2, tow, kur, frm); no results.json
    from frc_13_epi import predicate; predicate("13:F2")    one predicate: its blocks run once per session
"""
import os, json, sys, re, shutil, subprocess, time, math
from collections import OrderedDict
from fractions import Fraction
from fractions import Fraction as F
from fractions import Fraction as Fr
from decimal import Decimal, getcontext
from math import comb, gcd
import math as _m

SCRIPT = os.path.splitext(os.path.basename(__file__))[0]        # "epi": the one script, the name results.json and the site pages carry
HERE = os.path.dirname(os.path.abspath(__file__))              # the C sources beside the script

RESULTS = []
MICRO = []             # (script tag, family, label, ok)

LEDGER = {
    # validate_e.py
    "e.R1": "13:D3",
    "e.R2": "13:D4, 13:I1",
    "e.R3": "13:D4",
    "e.R4": "13:D5, 13:E5",
    "e.W1": "13:F1, 13:F2",
    "e.W2": "13:F3",
    "e.W3": "13:F4",
    "e.W4": "13:F6",
    "e.W5": "13:F8, 13:Y1",
    "e.S1": "13:F5, 13:I1",
    "e.A1": "13:H4, 13:I1",
    "e.N1": "13:H5, 13:I1",
    # validate_pi.py
    "pi.R1": "13:E2, 13:C5",
    "pi.R2": "13:G8",
    "pi.R3": "13:E4, 13:E5, 13:I2",
    "pi.R4": "13:E3",
    "pi.W1": "13:G1, 13:G2, 13:I2",
    "pi.W2": "13:G2",
    "pi.S1": "13:G4",
    "pi.S2": "13:G4, 13:I2, 13:J6",
    "pi.S3": "13:G4, 13:G10",
    "pi.L1": "13:G5, 13:G8",
    "pi.V1": "13:G6",
    # validate_pi2.py
    "pi2.A1": "13:G3",
    "pi2.A2": "13:G3, 13:I2",
    "pi2.B1": "13:G7",
    "pi2.B2": "13:G7",
    "pi2.C1": "13:G6",
    "pi2.C2": "13:G6",
    "pi2.C3": "13:G6",
    "pi2.C4": "13:G6",
    "pi2.D1": "13:G7",
    "pi2.D2": "13:G5",
    # validate_towers.py
    "tow.E": "13:F7, 13:B3",
    "tow.P": "13:G9, 13:B3",
    "tow.C": "13:C3",
    "tow.O": "13:B2",
    "tow.H": "13:J2, 13:J3, 13:J5",
    "tow.W": "13:J1, 13:J2, 13:G2, 13:H2, 13:I4",
    # kurepa_wall.c
    "kur.K1": "13:F2, 13:J6, 13:Y1",
    # frame_invariants.c
    "frm.I1": "13:I5, 13:Y3",
}

LABELS = {
    "e.R1": "superexponential enclosure of the derangement chain ε_n = n!/!n: |ε_n − e| < 8/(n+1)! and the alternating enclosure ε_even < e < ε_odd for 2 ≤ n ≤ 60, against the chain's own certified bracket",
    "e.R2": "binary64 readout: the IEEE-754 double nearest e is the correctly rounded ε_18 = 18!/!18 = 6402373705728000/2355301661033953, and n = 18 is minimal (ε_17 fails readout equality)",
    "e.R3": "100-digit determination: n = 70 is the least n with 8/(n+1)! < 10⁻¹⁰⁰, and ε_70 agrees with the certified value of e in its first 101 significant characters",
    "e.R4": "feasibility selection: the exact step counts of the derangement chain for 2⁻ᵏ precision, k = 24, 53, 333, are n = 11, 18, 70 (the paper's table; the compound-chain column is the chart-side estimate e·2^{k−1})",
    "e.W1": "the wall of e on p ∈ {5, 13, 29, 101, 257, 1009, 10007}: Wilson reflection 1/k! ≡ −(−1)^k (p−1−k)! for every k < p; the wall identity !(p−1) ≡ K(p) with K(p) = Σ_{k<p} k! the left factorial; K(p) ≢ 0, so the terminal residue [ε_{p−1}] = −K(p)⁻¹ exists on every sample shell",
    "e.W2": "antiperiodicity !(n+p) ≡ −!n (mod p) over a full period n < p on the seven sample shells; the blind set Z₀(p) = {n < p : !n ≡ 0} always contains 1 and never p−1 there",
    "e.W3": "series duals at the wall for p ∈ {7, 13, 29, 101, 257, 1009}: Σ(−1)^k/k! ≡ −K(p), Σ 1/k! ≡ −A(p); the group law breaks, K(p)·A(p) ≡ 3, 0, 21, 28, 132, 258, never 1; the asymmetry at p = 13: A(13) ≡ 0, K(13) ≡ 10",
    "e.W4": "the p = 13 picture: the residue line [ε_n]₁₃, n = 2 … 12, is 2, 3, 7, 11, 1, 6, blind, 2, 8, 10, 9 (blind at n = 8, !8 = 13·1141), terminating on the wall invariant 9 = −K(13)⁻¹, the reading of 6/5 and of 11/7",
    "e.W5": "the tail identity j!·!(p−1−j) ≡ (−1)^j (K(p) − K(j)) for every j < p on the seven sample shells (j = 0 the wall identity), and the collision reading of the blind set: n ∈ Z₀(p) exactly when the partial sum K(p−1−n) collides with K(p); K(p−2) ≡ K(p) is the forced collision n = 1, and Kurepa's hypothesis at p is K(0) = 0 ≢ K(p)",
    "e.S1": "blind-scale statistics over the 501 primes in (1000, 5000): |Z₀(p)| distributes as 1¹⁶⁹ 2²⁰⁹ 3⁹² 4²² 5⁶ 6² 7¹, mean 1.996 (exact counts; the Poisson(1) reading of the excess is the paper's [approx] model, not a predicate)",
    "e.A1": "radian calibration over p < 10⁶: 39 175 shells p ≡ 1 (mod 4); exactly 260 of them satisfy |θ − 1| < 0.01 for one chirality, θ = 2π λ(i)/(p−1), decided with π as a Machin bracket of width < 10⁻¹⁰⁰; the best six (p, λ(i)) are (778933, 123966), (497773, 79227), (962237, 153133), (261017, 41537), (345181, 54945), (891997, 141986) in that order",
    "e.N1": "the null experiment over the 210 primes p ≡ 1 (mod 4), 5 < p < 3000: the index condition gcd(s, p−1) = gcd(λ(±i), p−1) linking the exponential unit to the wall residue −K(p)⁻¹ is solvable for exactly 94 primes (44.8 %, the gcd-coincidence rate); the Pearson correlation of the two angular addresses (≈ −0.10) is printed as the paper's [approx] reading",
    "pi.R1": "the Wallis pair v_n = 2·16ⁿ/((2n+1)C(2n,n)²), w_n = 16ⁿ/(n C(2n,n)²): v_n < π < w_n for n ≤ 300 against Machin brackets of width < 10⁻⁴²⁰, the exact width identity w_n − v_n = w_n/(2n+1), and strict monotonicity",
    "pi.R2": "the p = 13 picture: the residue line [w_n]₁₃, n = 1 … 6, is 4, 5, 10, 9, 6, 11",
    "pi.R3": "the Machin chain M_N: the IEEE-754 double nearest π is the correctly rounded M_10 and N = 10 is minimal; |M_N − π| < 17/((2N+3)5^{2N+3}) for 2 ≤ N ≤ 39; 100 decimal digits fixed at N = 71; the alternating pairing of the two arctangent series gives a certified two-sided enclosure at (12, 4) terms",
    "pi.R4": "the arcsin chain s_n = 3 Σ_{k≤n} C(2k,k)/((2k+1)16^k): the tail bound |π − s_n| < 4⁻ⁿ/(2n+3) for 1 ≤ n ≤ 120, against the Machin bracket",
    "pi.W1": "the legibility window on p ∈ {5, 13, 29, 101, 257, 1009, 10007}: p ∤ C(2n,n) for 1 ≤ n ≤ m = (p−1)/2 and p | C(2n,n) for m < n < p; the half-wall terminus [w_m] ≡ −2 = m⁻¹ = 4π_A; the lower chain blind exactly at the wall (2m+1 = p)",
    "pi.W2": "the wall residue −2 is universal: [w_m] ≡ −2 also for p ≡ 3 (mod 4), p ∈ {7, 23, 1031}",
    "pi.S1": "second order at the half wall for p ∈ {13, 29, 37, 41, 53, 101}: Morley's congruence (−1)^m C(p−1,m) ≡ 4^{p−1} (mod p³) and the formula w_m ≡ −2 + 2p(q_p(4) − 1) (mod p²)",
    "pi.S2": "the π-Wieferich search: 4^{p−1} ≡ 1 + p (mod p²) holds for exactly p ∈ {5, 45827} among the primes below 10⁶ (the normalised quotients' moments over p < 2·10⁴ are printed as the paper's [approx] reading)",
    "pi.S3": "the π-Wieferich condition in three forms on p ∈ {5, 13, 29, 37, 41, 53, 101, 45827}: q_p(4) = 2q_p(2) + p·q_p(2)² exactly, 4^{p−1} ≡ 1 + p (mod p²) iff q_p(4) ≡ 1 iff 2q_p(2) ≡ 1 (mod p); Eisenstein's 2q_p(2) ≡ −H_{(p−1)/2}; and the OEIS A355959 form (p+2)^{p−1} ≡ 1 (mod p²) iff 2q_p(2) ≡ 1, holding at 5 and 45827 only",
    "pi.L1": "Lucas revivals: [v_p] ≡ 8 for p ∈ {5, 7, 11, 13, 29, 37}; on p = 13, C(26,13) ≡ 2 = C(2,1)·C(0,0), C(28,14) ≡ 4 = C(2,1)² digitwise, and the two-digit revival scales number exactly (2κ)² = 36",
    "pi.V1": "first-order wall vanishing: σ_p = Σ_{k<m} C(2k,k)/((2k+1)16^k) ≡ 0 (mod p) for all 428 odd primes 5 ≤ p < 3000, with σ_3 = 1 the sole exception; the rational numerator of σ_p is divisible by p for 5 ≤ p < 200",
    "pi2.A1": "Gauss's central-binomial congruence C(2κ,κ) ≡ 2a* (mod p), a* ≡ 1 (mod 4) the odd part of p = a² + b², for all 211 primes p ≡ 1 (mod 4) below 3000",
    "pi2.A2": "the quarter-wall two-squares invariant [w_κ] = κ⁻¹(2a)⁻² = −(a²)⁻¹ = (b²)⁻¹ (mod p) for the same 211 primes; on p = 13 = 3² + 2², [w_3] = 10 = −(9)⁻¹",
    "pi2.B1": "Sun's supercongruence σ_p ≡ 0 (mod p²) re-verified in exact rational arithmetic for all primes 5 ≤ p < 300",
    "pi2.B2": "the third-order Bernoulli law σ_p/p² ≡ (−1)^{(p+1)/2} B_{p−3}/36 (mod p) for all sixty primes 5 ≤ p < 300, B_{p−3} from the exact Bernoulli recurrence",
    "pi2.C1": "the binomial transfer C(2k,k) ≡ (−4)^k C(m,k) (mod p) for k < m on p ∈ {11, 13, 29, 37}",
    "pi2.C2": "Lerch's congruence H_{(p−1)/2} ≡ −2 q_p(2) (mod p) for all primes 5 ≤ p < 500",
    "pi2.C3": "the Wallis evaluation L_m = Σ_j C(m,j)(−1)^j/(2j+1) = 4^m (m!)²/(2m+1)! over Q for m ≤ 60",
    "pi2.C4": "the key identity A_m + B_m = 2L_m over Q for m ≤ 60, with A = 2(F(½) − F(0)), B = 2(F(1) − F(½)), L = F(1) − F(0) for the formal antiderivative F of the expanded (1 − s²)^m — coefficient bookkeeping only",
    "pi2.D1": "the blind-range Euler congruence Σ_{m<k<p} C(2k,k)/((2k+1)16^k) ≡ p E_{p−3}/3 (mod p²) for all primes 5 ≤ p < 80",
    "pi2.D2": "the first revival to second order, v_p ≡ 8 + 16p(2q_p(2) − 1) (mod p²), for p ∈ {5, 7, 11, 13, 29, 37}",
    "tow.E": "the fixed-shell tower of e on p = 13 and 29, grades m ≤ 3: !(mp) ≡ (−1)^m, the shell reading [q_m] = e_p exactly, and q_m inside the certified window around e",
    "tow.P": "the fixed-shell tower of π on p = 13 and 29, n = p, p²: C(2n,n) ≡ 2, 16ⁿ ≡ 16, δ_p = ⟨−34⟩, the shell reading [π̂_{p,r}] = π_A exactly, and the r = 1 member inside the certified brackets",
    "tow.C": "the Cayley quarter-turn map C(x) = (1 + ix)/(1 − ix) on F_13 and F_29: C(0) = 1, C(1) = i, and the composition law C(x)C(y) = C((x+y)/(1−xy)) on every pair where the denominators are units",
    "tow.O": "orientation transport on F_13 and F_29, exhaustively over the units u of the exponent cycle: g' = g^u re-derives i' = i when u ≡ 1 (mod 4) and i' = −i when u ≡ 3 (mod 4)",
    "tow.H": "the height run over all 500 shells p ≡ 1 (mod 4), p ≤ 8009, in the smallest-primitive-root frame with H minimised over the two chiralities: π_A = [−1/2] pinned at height 2 on every shell; H(e_p) ≤ 2√p on every shell; exactly 68 shells with H ≤ 10; height 2 on exactly {13, 1933, 4177, 5857} (median H/√p ≈ 0.525 printed as the diagnostic)",
    "tow.W": "the wrap-free window and the calibration pin on p ∈ {13, 29, 101, 997, 8009}: ⌊√p⌋² < p and 2⌊√p⌋ < p; the pinning relation 2π_A + 1 ≡ 0; the half-turn tautology g^{2κ} = −1 for the smallest primitive root; the quarter-turn pin i² + 1 ≡ 0",
    "kur.K1": "Kurepa's wall in the derangement form for all 22 043 odd primes p < 2.5·10⁵ (kurepa_wall.c, one O(p) pass per prime in 128-bit modular arithmetic): !(p−1) ≡ K(p) (mod p) and K(p) ≢ 0 (mod p), zero failures of either condition",
    "frm.I1": "the three frame invariants of the two constants on the 4 783 shells p ≡ 1 (mod 4) below 10⁵ (frame_invariants.c): every triple (K(p) mod p, q_p(4) mod p, a + b i) exact — p = 13: (10, 6, −3+2i), p = 1093 the one shell with q_p(4) = 0 — the 4×4×4 contingency table of (K/p, q_p(4)/p, φ/π) and its chi-square 59.6 on 63 df exact, the means 0.502, 0.499 and variances 0.0828, 0.0831 by certified rational bounds; the independence reading is the paper's [approx] statement",
}

BLOCK = {"e": "the derangement chain of e: the wall, the blind statistics, the calibration scan, the null experiment", "pi": "the chains of π: Wallis, Machin, arcsin; the window, the terminus, Morley, the Wieferich search, the revivals",      # check-id prefix -> the block (the function block_<name> below)
         "pi2": "the quarter invariant, Sun's supercongruence and the Bernoulli law, the proof ingredients", "tow": "the fixed-shell towers, the Cayley map, orientation transport, the height run, the pins",
         "kur": "the Kurepa wall over the 22 043 odd primes below 2.5e5 (a C pass)", "frm": "the frame invariants of the 4 783 shells p ≡ 1 (mod 4) below 1e5 (a C pass)"}
_FAM = [None, None]

# the deciding family of each witnessed predicate: the one whose checks decide the predicate's statement (the other families
# that touch it are corroboration, listed by predicate() from the records)
PREDICATES = {
    "13:B2": "tow.O", "13:B3": "tow.E", "13:C3": "tow.C", "13:C5": "pi.R1", "13:D3": "e.R1", "13:D4": "e.R2",
    "13:D5": "e.R4", "13:E2": "pi.R1", "13:E3": "pi.R4", "13:E4": "pi.R3", "13:E5": "pi.R3", "13:F1": "e.W1",
    "13:F2": "e.W1", "13:F3": "e.W2", "13:F4": "e.W3", "13:F5": "e.S1", "13:F6": "e.W4", "13:F7": "tow.E",
    "13:F8": "e.W5", "13:G1": "pi.W1", "13:G2": "pi.W1", "13:G3": "pi2.A1", "13:G4": "pi.S1", "13:G5": "pi.L1",
    "13:G6": "pi.V1", "13:G8": "pi.R2", "13:G9": "tow.P", "13:G10": "pi.S3", "13:H2": "tow.W", "13:H5": "e.N1",
    "13:I1": "e.R2", "13:I2": "pi.R3", "13:I4": "tow.W", "13:I5": "frm.I1", "13:J1": "tow.W", "13:J2": "tow.H",
    "13:J3": "tow.H", "13:J5": "tow.H", "13:J6": "kur.K1", "13:Y1": "kur.K1", "13:Y3": "frm.I1",
}
_FAM = [None, None]
_RAN = set()                                            # blocks already run in this session (predicate() runs each once)

def markers():
    """predicate label -> (script file, line) of its marker `# <paper>:<label> (<key>)`: the line of the check that decides it."""
    import re
    out = {}
    for i, line in enumerate(open(os.path.abspath(__file__), encoding="utf-8"), 1):
        m = re.match(r"\s*# ((?:\d+:[A-Z]+\d+[a-z]?(?: \(p\d{5}\))?)(?:, \d+:[A-Z]+\d+[a-z]?(?: \(p\d{5}\))?)*)\s*$", line)
        if m:
            for lab in re.findall(r"\d+:[A-Z]+\d+[a-z]?", m.group(1)): out.setdefault(lab, (SCRIPT + ".py", i))
    return out

def _run_block(name):
    if name not in _RAN:
        globals()[f"block_{name}"](); _RAN.add(name)

def predicate(label, lines=14):
    """Verify one ledger predicate: run the blocks of the families that cite it (each once per session), print the deciding
    check's source (from its marker) and every family record that cites the predicate, and return True iff all pass."""
    fam = PREDICATES.get(label)
    if fam is None:
        print(f"{label}: no python witness (see the predicate's Lean witness or its source)"); return None
    citing = {f.split(".")[0] for f, rows in LEDGER.items() if label in [t.strip() for t in rows.split(",")]}
    for b in [b for b in BLOCK if b in {fam.split(".")[0]} | citing]: _run_block(b)     # the deciding block and every block whose families cite the predicate
    mk = markers().get(label)
    if mk:
        src = open(os.path.abspath(__file__), encoding="utf-8").read().split("\n")
        print(f"— {mk[0]}:{mk[1]} (the check that decides {label}; family {fam})")
        for j in range(mk[1] - 1, min(mk[1] - 1 + lines, len(src))): print(f"{j + 1:5d}  {src[j]}")
    else:
        print(f"— {SCRIPT}.py, block {fam.split('.')[0]} (the whole block witnesses {label})")
    recs = [r for r in RESULTS if label in [t.strip() for t in r["rows"].split(",")]]
    ok = all(r["ok"] for r in recs)
    for r in recs:
        role = "(deciding)" if r["id"] == fam else "(corroborating)"
        print(f"  [{'PASS' if r['ok'] else 'FAIL'}] {r['id']:8s} {role:16s} {r['detail']}")
    print(f"{label}: {'VERIFIED' if ok and recs else 'FAILED'} — {len(recs)} family record(s)")
    return ok

def verify_all():
    """Run every block (those already run in this session are not re-run) and print the summary; True iff every family check passed."""
    for b in BLOCK: _run_block(b)                          # in the declared order
    return summary(write=False)

def family(tag, fam):
    _FAM[0], _FAM[1] = tag, fam

def chk(label, ok, tag=None, fam=None):
    """A micro-check, recorded under the current (tag, family); never exits."""
    MICRO.append((tag or _FAM[0], fam or _FAM[1], label, bool(ok)))
    if not ok:
        print(f"    FAIL: {label}")

def flush(tag, order=None, details=None):
    fams = OrderedDict()
    for t, fam, label, ok in MICRO:
        if t == tag:
            fams.setdefault(fam, []).append(ok)
    for fam in (order or fams):
        oks = fams.get(fam, [])
        d = f"{len(oks)} exact micro-checks"
        if details and fam in details:
            d += "; " + details[fam]
        check(f"{tag}.{fam}", ok=bool(oks) and all(oks), detail=d)

def check(pid, ok, detail="", kind="EXACT", label=None):
    ok = bool(ok)
    rows = LEDGER.get(pid, "")
    label = label or LABELS.get(pid, pid)
    RESULTS.append({"id": pid, "rows": rows, "block": pid.split(".")[0], "script": SCRIPT, "label": label, "ok": ok, "detail": detail, "kind": kind})
    print(f"  [{'PASS' if ok else 'FAIL'}] {pid:7s} {kind:5s} [{rows}] {label[:110]}" + (f"  --  {detail}" if detail else ""))
    return ok

def summary(write=True):
    n_ok = sum(r["ok"] for r in RESULTS)
    print(f"\nSUMMARY: {n_ok}/{len(RESULTS)} checks passed ({len(MICRO)} exact micro-checks)" + ("" if n_ok == len(RESULTS) else "  <-- FAILURES"))
    if write:
        with open("results.json", "w") as f:
            json.dump(RESULTS, f, indent=1, ensure_ascii=False)
    return n_ok == len(RESULTS)

# ------------------------------------------------------------------------------------------------------------
# block e — validate_e.py: FRC emergence of e: verification suite.
# Sections:
#   [1] Metric emergence of e from the derangement chain n!/D_n (exact rationals).
#   [2] Frame-internal arithmetic: antiperiodicity, blind scales, wall identity, series duals.
#   [3] Angular unit e_t = g^{i_t}: two-valued angle, radian calibration search over p < 10^6.
#   [4] Null experiment: pointwise identification g^{i_t} = k(e)-residue solvability statistics.
#
# Package form (2026-09): the memorandum script as written, its PASS/FAIL lines and the paper's stated figures turned
# into registry predicates (families e.R1-R4, e.W1-W5, e.S1, e.A1, e.N1). The radian-calibration scan of [3] now decides
# |theta - 1| < 0.01 and the ordering of the best shells in exact rational arithmetic with pi as a Machin bracket
# (width < 1e-100), as the paper states; the binary64 constant math.e is the object of study of the readout theorem
# and is compared exactly with the correctly rounded framed rationals. Every check is exact; the Pearson correlation
# of [4] is printed as the paper's [approx] reading and decides nothing.
OUT_e = []
def log_e(s=""):
    print(s); OUT_e.append(str(s))

def pi_bracket(N=80):
    """Certified Machin bracket L < pi < U by alternating pairing; width < 1e-100 at N = 80."""
    def S(x, N):
        run, part = Fraction(0), []
        for k in range(N + 2):
            run += Fraction((-1)**k, (2*k + 1) * x**(2*k + 1)); part.append(run)
        return min(part[N], part[N+1]), max(part[N], part[N+1])
    l5, u5 = S(5, N); l239, u239 = S(239, N)
    return 16*l5 - 4*u239, 16*u5 - 4*l239

# ---------- helpers ----------
def sieve_e(N):
    comp = bytearray(N + 1)
    for i in range(2, int(N**0.5) + 1):
        if not comp[i]:
            comp[i*i::i] = b'\x01' * len(comp[i*i::i])
    return [i for i in range(2, N + 1) if not comp[i]]

def derangements_exact(N):
    D = [1, 0]
    for n in range(2, N + 1):
        D.append(n * D[n-1] + (-1)**n)
    return D

def e_fraction(K=260):
    s, f = Fraction(0), 1
    for k in range(K):
        if k: f *= k
        s += Fraction(1, f)
    return s   # |s - e| < 3/K! < 10^-500 for K=260

def frac_to_dec(fr, prec=140):
    getcontext().prec = prec
    return Decimal(fr.numerator) / Decimal(fr.denominator)

_DIAG = [""]

def block_e():
    """Block e — the derangement chain of e — enclosure, readouts, feasibility, the Kurepa wall, antiperiodicity, duals, the p = 13 line, blind statistics, radian calibration, the null experiment (e.R1 … e.N1)."""
    global E, D, fact, NMAX
    # =========================================================
    log_e("="*72); log_e("[1] METRIC EMERGENCE: the chain eps_n = n!/D_n")
    log_e("="*72)
    E = e_fraction(300)
    NMAX = 110
    D = derangements_exact(NMAX)
    fact = [1]
    for n in range(1, NMAX + 1): fact.append(fact[-1] * n)

    # (a) error bound |n!/D_n - e| < 8/(n+1)!  and alternating enclosure
    bound_ok, encl_ok = True, True
    for n in range(2, 61):
        err = Fraction(fact[n], D[n]) - E
        if abs(err) >= Fraction(8, fact[n+1]): bound_ok = False
        if (err > 0) != (n % 2 == 1): encl_ok = False   # sign(eps_n - e) = (-1)^{n+1}
    log_e(f"(a) |n!/D_n - e| < 8/(n+1)! for n=2..60 : {'PASS' if bound_ok else 'FAIL'}")
    log_e(f"    alternating enclosure eps_even < e < eps_odd : {'PASS' if encl_ok else 'FAIL'}")
    # 13:D3 (p13019)
    family("e", "R1")
    chk("|n!/D_n - e| < 8/(n+1)! for n = 2..60", bound_ok)
    chk("alternating enclosure eps_even < e < eps_odd for n = 2..60", encl_ok)

    # (b) minimal n whose framed rational rounds to the IEEE-754 double nearest e
    target = math.e
    n_double = None
    for n in range(2, 40):
        if float(Fraction(fact[n], D[n])) == target:
            n_double = n; break
    log_e(f"(b) minimal n with float(n!/D_n) == IEEE-double(e): n = {n_double}")
    log_e(f"    n!/D_n at n={n_double}: {fact[n_double]}/{D[n_double]}")
    log_e(f"    |eps_17 - e| = {float(abs(Fraction(fact[17],D[17])-E)):.3e},  half-ulp(e) = {math.ulp(math.e)/2:.3e}")
    # 13:D4 (p13020), 13:I1 (p13048)
    family("e", "R2")
    chk("minimal n with float(n!/D_n) == binary64(e) is n = 18", n_double == 18)
    chk("eps_18 = 6402373705728000/2355301661033953", Fraction(fact[18], D[18]) == Fraction(6402373705728000, 2355301661033953))
    chk("eps_17 fails readout equality", float(Fraction(fact[17], D[17])) != target)
    chk("|eps_17 - e| exceeds the half-ulp 2^-53 and |eps_18 - e| lies below it", abs(Fraction(fact[17], D[17]) - E) > Fraction(1, 2**53) > abs(Fraction(fact[18], D[18]) - E))

    # (c) 100-digit determination
    n100 = None
    for n in range(2, NMAX):
        if Fraction(8, fact[n+1]) < Fraction(1, 10**100):
            n100 = n; break
    d_chain = frac_to_dec(Fraction(fact[n100], D[n100]), 130)
    d_e     = frac_to_dec(E, 130)
    match = 0
    s1, s2 = str(d_chain), str(d_e)
    for a, b in zip(s1, s2):
        if a == b: match += 1
        else: break
    log_e(f"(c) 100-digit precision reached at n = {n100}; leading agreement with e: {match-1} chars")
    log_e(f"    e            = {str(d_e)[:105]}")
    log_e(f"    {n100}!/D_{n100}     = {str(d_chain)[:105]}")
    family("e", "R3")
    chk("least n with 8/(n+1)! < 10^-100 is n = 70", n100 == 70)
    chk("70!/D_70 agrees with e in at least 101 leading characters (100 significant digits)", match - 1 >= 101)

    # (d) feasibility comparison with (1+1/n)^n
    log_e("(d) precision-cost comparison (steps n needed for 2^-k):")
    # 13:D5 (p13021)
    family("e", "R4")
    for k in (24, 53, 333):
        # derangement chain: 8/(n+1)! < 2^-k
        n1 = 2
        while Fraction(8, fact[n1+1]) >= Fraction(1, 2**k): n1 += 1
        # compound chain: |(1+1/n)^n - e| ~ e/(2n) -> n ~ e*2^{k-1}
        n2 = math.e * 2**(k-1)
        log_e(f"    k={k:3d}:  derangement chain n = {n1:3d}   |   (1+1/n)^n chain n ~ {n2:.2e}")
        chk(f"derangement chain reaches 2^-{k} at n = {(24, 53, 333).index(k) and [11, 18, 70][(24, 53, 333).index(k)] or 11}", n1 == [11, 18, 70][(24, 53, 333).index(k)])

    # =========================================================
    log_e(); log_e("="*72); log_e("[2] FRAME-INTERNAL ARITHMETIC (per-prime structure)")
    log_e("="*72)

    def d_mod(p, upto):
        """derangement residues D_0..D_upto mod p via recurrence"""
        d = [1 % p, 0]
        s = -1
        for n in range(2, upto + 1):
            s = -s
            d.append((n * d[n-1] + s) % p)
        return d

    def kurepa_mod(p):
        f, s = 1, 1
        for k in range(1, p):
            f = f * k % p
            s = (s + f) % p
        return s

    def alt_fact_mod(p):
        f, s, sg = 1, 1, 1
        for k in range(1, p):
            f = f * k % p
            sg = -sg
            s = (s + sg * f) % p
        return s % p

    sample_primes = [5, 13, 29, 101, 257, 1009, 10007]
    log_e(f"{'p':>6} | D_(p-1)==!p | antiperiod D_(n+p)==-D_n | wall residue k(e)= -(!p)^-1 | blind set Z0(p)")
    for p in sample_primes:
        d = d_mod(p, 2*p)
        kp = kurepa_mod(p)
        wall = (d[p-1] == kp)
        anti = all(d[n+p] == (-d[n]) % p for n in range(0, p))
        z0 = [n for n in range(p) if d[n] == 0]
        ke = (-pow(kp, -1, p)) % p if kp else None
        # 13:F1 (p13027), 13:F2 (p13028)
        family("e", "W1")
        f_ = [1]
        for k in range(1, p): f_.append(f_[-1] * k % p)
        chk(f"p={p}: Wilson reflection 1/k! == -(-1)^k (p-1-k)! for all k < p", all(pow(f_[k], -1, p) == (-(-1)**k * f_[p-1-k]) % p for k in range(p)))
        chk(f"p={p}: wall identity D_(p-1) == K(p)", wall)
        chk(f"p={p}: K(p) != 0, the terminal residue -(K(p))^-1 exists", kp != 0)
        # 13:F3 (p13029)
        family("e", "W2")
        chk(f"p={p}: antiperiodicity D_(n+p) == -D_n over a full period", anti)
        chk(f"p={p}: 1 in Z0(p) and p-1 not in Z0(p)", 1 in z0 and (p-1) not in z0)
        # the tail identity and the collision reading of the blind set (13:F8; the Y1 push of 2026-09-18)
        # 13:F8 (p13066)
        family("e", "W5")
        Kj = [0]
        for k in range(p): Kj.append((Kj[-1] + f_[k]) % p)          # Kj[j] = K(j) = sum_{k<j} k! mod p
        chk(f"p={p}: tail identity j! D_(p-1-j) == (-1)^j (K(p) - K(j)) for all j < p", all(f_[j] * d[p-1-j] % p == ((-1)**j * (Kj[p] - Kj[j])) % p for j in range(p)))
        chk(f"p={p}: blind set = collisions of the partial sums: Z0(p) = {{p-1-j : K(j) == K(p), j <= p-2}}", set(z0) == {p-1-j for j in range(p-1) if Kj[j] == Kj[p]})
        chk(f"p={p}: the forced collision K(p-2) == K(p) (n = 1) and K(0) = 0 != K(p) (Kurepa at p)", Kj[p-2] == Kj[p] and Kj[p] != 0)
        log_e(f"{p:6d} |   {'PASS' if wall else 'FAIL'}      |          {'PASS' if anti else 'FAIL'}           |    {ke!s:>8}                | {z0 if len(z0)<=8 else str(z0[:8])+'...'} (|Z0|={len(z0)})")

    # series duals
    log_e()
    log_e("Series duals at the wall:  S- := sum (-1)^k/k! == -!p ;  S+ := sum 1/k! == -A(p)")
    dual_ok = True
    prod_examples = []
    for p in [7, 13, 29, 101, 257, 1009]:
        invf, f = [1], 1
        for k in range(1, p):
            f = f * k % p
            invf.append(pow(f, -1, p))
        Sm = sum(((-1)**k) * invf[k] for k in range(p)) % p
        Sp = sum(invf[k] for k in range(p)) % p
        kp, ap = kurepa_mod(p), alt_fact_mod(p)
        if Sm != (-kp) % p or Sp != (-ap) % p: dual_ok = False
        prod_examples.append((p, (kp * ap) % p))
    log_e(f"  duals verified for p in [7,13,29,101,257,1009]: {'PASS' if dual_ok else 'FAIL'}")
    log_e(f"  group-law breaking at the wall: (!p * A(p)) mod p = {prod_examples}  (would be == 1 if exp(1)exp(-1)=1 survived)")
    # 13:F4 (p13030)
    family("e", "W3")
    chk("series duals S- == -K(p), S+ == -A(p) for p in [7, 13, 29, 101, 257, 1009]", dual_ok)
    chk("K(p) A(p) mod p = 3, 0, 21, 28, 132, 258 (never 1)", [v for _, v in prod_examples] == [3, 0, 21, 28, 132, 258])
    chk("asymmetry at p = 13: A(13) == 0 and K(13) == 10", alt_fact_mod(13) == 0 and kurepa_mod(13) == 10)
    # the p = 13 picture: the residue line of eps_n, n = 2..12
    # 13:F6 (p13032)
    family("e", "W4")
    d13 = d_mod(13, 13)
    line13 = [None if d13[n] == 0 else (math.factorial(n) % 13) * pow(d13[n], -1, 13) % 13 for n in range(2, 13)]
    log_e(f"  p=13 residue line [eps_n]_13, n=2..12: {['blind' if v is None else v for v in line13]}")
    chk("p=13: [eps_n]_13 for n = 2..12 is 2, 3, 7, 11, 1, 6, blind, 2, 8, 10, 9", line13 == [2, 3, 7, 11, 1, 6, None, 2, 8, 10, 9])
    chk("p=13: D_8 = 14833 = 13 * 1141 (the blind scale)", D[8] == 14833 == 13 * 1141)
    chk("p=13: the wall invariant 9 = -(K(13))^-1 = [6/5] = [11/7]", (-pow(kurepa_mod(13), -1, 13)) % 13 == 9 == 6 * pow(5, -1, 13) % 13 == 11 * pow(7, -1, 13) % 13)

    # blind-scale statistics
    log_e()
    primes_stat = [p for p in sieve_e(5000) if 1000 < p < 5000]
    sizes = []
    for p in primes_stat:
        d = d_mod(p, p - 1)
        z = sum(1 for n in range(p) if (d[n] if n < len(d) else None) == 0)
        sizes.append(z)
    from collections import Counter
    cnt = Counter(sizes)
    mean = sum(sizes)/len(sizes)
    log_e(f"Blind-scale statistics over {len(primes_stat)} primes in (1000,5000):")
    log_e(f"  |Z0(p)| distribution: {dict(sorted(cnt.items()))},  mean = {mean:.3f}")
    log_e(f"  (n=1 is always blind since D_1=0; excess over 1 has mean {mean-1:.3f}, Poisson(1) predicts 1.000)")
    # 13:F5 (p13031)
    family("e", "S1")
    chk("501 primes in (1000, 5000)", len(primes_stat) == 501)
    chk("|Z0(p)| distribution 1:169, 2:209, 3:92, 4:22, 5:6, 6:2, 7:1", dict(cnt) == {1: 169, 2: 209, 3: 92, 4: 22, 5: 6, 6: 2, 7: 1})
    chk("mean |Z0(p)| = 1000/501 = 1.996", Fraction(sum(sizes), len(sizes)) == Fraction(1000, 501))

    # =========================================================
    log_e(); log_e("="*72); log_e("[3] ANGULAR UNIT e_t = g^{i_t}: radian calibration over p < 10^6")
    log_e("="*72)
    LIM = 1000000
    primes = sieve_e(LIM)
    PI_LO, PI_HI = pi_bracket(80)                 # certified rational bracket of pi, width < 1e-100
    best = []
    count_001 = 0
    n_p1mod4 = 0
    near = []                                     # candidates for the best list, screened in floating point, decided exactly
    for p in primes:
        if p % 4 != 1: continue
        n_p1mod4 += 1
        # sqrt(-1) mod p via a quadratic nonresidue
        a = 2
        while pow(a, (p-1)//2, p) != p - 1: a += 1
        r = pow(a, (p-1)//4, p)
        for rr in (r, p - r):
            # |theta - 1| < 1/100 with theta = 2 pi rr/(p-1): decided as the rational inequality
            # 99 (p-1) < 200 pi rr < 101 (p-1), pi replaced by its bracket (margin >> width)
            if 99*(p-1) < 200*PI_LO*rr and 200*PI_HI*rr < 101*(p-1): count_001 += 1
            delta_f = abs(2*math.pi*rr/(p-1) - 1.0)          # screening only
            if delta_f < 0.001: near.append((p, rr))
    # exact ordering of the candidates: delta = |2 pi rr/(p-1) - 1| with pi the bracket midpoint (the ordering is
    # decided at margins >> 1e-100)
    PI_MID = (PI_LO + PI_HI) / 2
    best = sorted((abs(2*PI_MID*rr/(p-1) - 1), p, rr) for p, rr in near)
    log_e(f"primes p==1 (mod 4) below 10^6: {n_p1mod4}")
    log_e(f"frames with |theta_t - 1 rad| < 0.01: {count_001}  (equidistribution predicts ~ {2*0.01/(2*math.pi)*n_p1mod4*2:.0f} over both orientations)")
    log_e("best radian-calibrated frames (p, i_t-label r, theta_t, |theta_t - 1|):")
    for delta, p, rr in best[:6]:
        log_e(f"  p={p:7d}  r={rr:7d}  theta={float(2*PI_MID*rr/(p-1)):.9f}  delta={float(delta):.3e}")
    family("e", "A1")
    chk("39175 primes p == 1 (mod 4) below 10^6", n_p1mod4 == 39175)
    chk("exactly 260 shells with |theta - 1| < 0.01 (exact rational decision, pi as a Machin bracket)", count_001 == 260)
    chk("the best six (p, lambda(i)) in order: (778933,123966), (497773,79227), (962237,153133), (261017,41537), (345181,54945), (891997,141986)",
        [(p, rr) for _, p, rr in best[:6]] == [(778933, 123966), (497773, 79227), (962237, 153133), (261017, 41537), (345181, 54945), (891997, 141986)])
    chk("the best shell is calibrated below 4e-5 and above 3.9e-5", Fraction(39, 10**6) < best[0][0] < Fraction(4, 10**5))

    # =========================================================
    log_e(); log_e("="*72); log_e("[4] NULL EXPERIMENT: pointwise g^{i_t} == k(e)-wall-residue?")
    log_e("="*72)
    def primitive_root(p):
        fac = []
        m = p - 1; d = 2
        while d*d <= m:
            if m % d == 0:
                fac.append(d)
                while m % d == 0: m //= d
            d += 1
        if m > 1: fac.append(m)
        for g in range(2, p):
            if all(pow(g, (p-1)//q, p) != 1 for q in fac):
                return g
        return None

    solvable, total = 0, 0
    corr_x, corr_y = [], []
    for p in [q for q in sieve_e(3000) if q % 4 == 1 and q > 5]:
        kp = kurepa_mod(p)
        if kp == 0: continue
        Ep = (-pow(kp, -1, p)) % p            # wall residue of e
        g0 = primitive_root(p)
        # index table
        ind = {}
        x = 1
        for m in range(p - 1):
            ind[x] = m
            x = x * g0 % p
        s = ind[Ep]
        a = 2
        while pow(a, (p-1)//2, p) != p - 1: a += 1
        r = pow(a, (p-1)//4, p)
        ok = (math.gcd(s, p-1) == math.gcd(r, p-1)) or (math.gcd(s, p-1) == math.gcd(p - r, p-1))
        solvable += ok; total += 1
        corr_x.append(min(r, p-r)/(p-1)); corr_y.append(s/(p-1))
    # Pearson correlation
    mx = sum(corr_x)/len(corr_x); my = sum(corr_y)/len(corr_y)
    num = sum((x-mx)*(y-my) for x, y in zip(corr_x, corr_y))
    den = math.sqrt(sum((x-mx)**2 for x in corr_x) * sum((y-my)**2 for y in corr_y))
    log_e(f"p==1(4), 5<p<3000: some frame g with g^(i_t) == -(!p)^(-1) exists for {solvable}/{total} primes ({100*solvable/total:.1f}%)")
    log_e(f"Pearson correlation between angular address of i_t and of the wall residue: {num/den:+.4f}")
    log_e("=> solvability is gcd-coincidence noise, no invariant identification; the two objects are distinct projections.")
    # 13:H5 (p13047)
    family("e", "N1")
    chk("210 primes p == 1 (mod 4), 5 < p < 3000, with K(p) != 0", total == 210)
    chk("the index condition is solvable for exactly 94 of them", solvable == 94)
    _DIAG[0] = f"Pearson correlation of the angular addresses {num/den:+.3f} (the paper's [approx] reading)"


    flush("e", order=["R1", "R2", "R3", "R4", "W1", "W2", "W3", "W4", "W5", "S1", "A1", "N1"], details={"N1": _DIAG[0]})

# ------------------------------------------------------------------------------------------------------------
# block pi — validate_pi.py: FRC emergence of pi: verification suite.
# Sections:
#   [1] Radial chains: Wallis central-binomial pair (v_n, w_n) enclosure; Machin readout.
#   [2] Wall arithmetic: legibility window [1,2t], empty blind set, hard wall, residue -2.
#   [3] Second order: Morley congruence, W mod p^2 = Fermat-quotient formula, pi-Wieferich search.
#   [4] Lucas revivals and digitwise self-similarity.
#   [5] arcsin(1/2) chain: wall vanishing T(p) == 0 test and second-order pattern hunt.
#   [6] Angular exactness and Gauss-sum saturation.
#
#
# Package form (2026-09): the memorandum script as written, its PASS/FAIL lines and the paper's stated figures turned
# into registry predicates (families pi.R1-R4, pi.W1-W2, pi.S1-S3, pi.L1, pi.V1); the arcsin tail bound (pi.R4) and
# the universality of the first revival (pi.L1) are added. Every predicate is exact (integers, exact rationals; pi as
# the exact Machin bracket PI). The Fermat-quotient moments of [3], the pattern hunt of [5] and the Gauss sums of [6]
# are the paper's [approx] diagnostics: printed, deciding nothing.
OUT_pi = []
def log_pi(s=""):
    print(s); OUT_pi.append(str(s))

def sieve_pi(N):
    c = bytearray(N + 1)
    for i in range(2, int(N**0.5) + 1):
        if not c[i]: c[i*i::i] = b'\x01' * len(c[i*i::i])
    return [i for i in range(3, N + 1) if not c[i]]

# reference pi to ~420 digits via exact Machin
def pi_fraction(N=320):
    def arctan_inv(x, N):
        s = Fraction(0)
        for k in range(N + 1):
            s += Fraction((-1)**k, (2*k + 1) * x**(2*k + 1))
        return s
    return 16*arctan_inv(5, N) - 4*arctan_inv(239, N)
PI = pi_fraction(320)

def Sg(N): return sum(Fraction((-1)**k, 2*k+1) for k in range(N+1))

def block_pi():
    """Block pi — the Wallis, Machin and arcsin chains of π, the legibility window and the −2 terminus, Morley and the π-Wieferich search, Lucas revivals, the first-order arcsin vanishing (pi.R1 … pi.V1)."""
    # =========================================================
    log_pi("="*72); log_pi("[1] RADIAL CHAINS")
    log_pi("="*72)
    # Wallis pair
    def vw(n):
        C = comb(2*n, n)
        w = Fraction(16**n, n * C * C)
        v = Fraction(2 * 16**n, (2*n + 1) * C * C)
        return v, w
    encl = True; ident = True; mono = True
    prev_v, prev_w = vw(1)
    for n in range(1, 301):
        v, w = vw(n)
        if not (v < PI < w): encl = False
        if w - v != w / (2*n + 1): ident = False
        if n > 1 and not (v > prev_v and w < prev_w): mono = False
        if n > 1: prev_v, prev_w = v, w
    log_pi(f"(a) Wallis pair: v_n < pi < w_n for n=1..300: {'PASS' if encl else 'FAIL'}; "
        f"exact width identity w-v=w/(2n+1): {'PASS' if ident else 'FAIL'}; strict monotonicity: {'PASS' if mono else 'FAIL'}")
    v50, w50 = vw(50)
    log_pi(f"    example n=50: width = {float(w50-v50):.4e} ~ pi/101 = {math.pi/101:.4e}  (O(1/n) rate)")
    # 13:C5 (p13016), 13:E2 (p13023)
    family("pi", "R1")
    chk("v_n < pi < w_n for n = 1..300 (Machin bracket)", encl)
    chk("exact width identity w_n - v_n = w_n/(2n+1)", ident)
    chk("v_n strictly increasing, w_n strictly decreasing", mono)
    # p=13 showcase residue line (round-01: anchors the manuscript's displayed line)
    p13_line = [pow(16, n, 13) * pow(n * pow(math.comb(2*n, n), 2, 13) % 13, -1, 13) % 13 for n in range(1, 7)]
    log_pi(f"    p=13 residue line [w_n]_13, n=1..6: {p13_line} " + ("PASS" if p13_line == [4, 5, 10, 9, 6, 11] else "FAIL"))
    # 13:G8 (p13041)
    family("pi", "R2")
    chk("p=13: [w_n]_13 for n = 1..6 is 4, 5, 10, 9, 6, 11", p13_line == [4, 5, 10, 9, 6, 11])

    # Machin chain: M_N with both arctans truncated at N
    def machin(N):
        def S(x, N): return sum(Fraction((-1)**k, (2*k+1)*x**(2*k+1)) for k in range(N+1))
        return 16*S(5, N) - 4*S(239, N)
    n_double = None
    for N in range(2, 25):
        if float(machin(N)) == math.pi:
            n_double = N; break
    log_pi(f"(b) Machin chain: minimal N with float(M_N) == IEEE-double(pi): N = {n_double}")
    err_bound_ok = all(abs(machin(N) - PI) < Fraction(17, (2*N+3)*5**(2*N+3)) for N in range(2, 40))
    log_pi(f"    error bound |M_N - pi| < 17/((2N+3) 5^(2N+3)) for N=2..39: {'PASS' if err_bound_ok else 'FAIL'}")
    N100 = None
    for N in range(60, 90):
        if abs(machin(N) - PI) < Fraction(1, 10**101): N100 = N; break
    log_pi(f"    100-decimal-digit determination at N = {N100}")
    # enclosure via alternating pairing
    def S_pair(x, N):  # (lower, upper) alternating bounds for arctan(1/x)
        s = Fraction(0); terms = [Fraction((-1)**k, (2*k+1)*x**(2*k+1)) for k in range(N+2)]
        partial = []
        run = Fraction(0)
        for t in terms:
            run += t; partial.append(run)
        lo = min(partial[N], partial[N+1]); hi = max(partial[N], partial[N+1])
        return lo, hi
    l5, u5 = S_pair(5, 12); l239, u239 = S_pair(239, 4)
    lo, hi = 16*l5 - 4*u239, 16*u5 - 4*l239
    log_pi(f"    fQ-native certified enclosure at (12,4) terms: pi in ({float(lo):.16f}, {float(hi):.16f}): {'PASS' if lo < PI < hi else 'FAIL'}")
    # 13:E4 (p13025), 13:E5 (p13026), 13:I2 (p13049)
    family("pi", "R3")
    chk("minimal N with float(M_N) == binary64(pi) is N = 10", n_double == 10)
    chk("binary64(pi) = 884279719003555/281474976710656 = float(M_10)", Fraction(math.pi) == Fraction(884279719003555, 281474976710656) and float(machin(10)) == math.pi)
    chk("|M_N - pi| < 17/((2N+3) 5^(2N+3)) for N = 2..39", err_bound_ok)
    chk("100 decimal digits fixed at N = 71 (|M_71 - pi| < 10^-101, first N with that property from 60)", N100 == 71)
    chk("certified enclosure at (12, 4) terms contains pi and has width below 2^-52", lo < PI < hi and hi - lo < Fraction(1, 2**52))
    chk("Gregory brackets 4 S_(2m+1) < pi < 4 S_(2m) of width 4/(4m+3), m <= 40", all(4*Sg(2*m+1) < PI < 4*Sg(2*m) and 4*Sg(2*m) - 4*Sg(2*m+1) == Fraction(4, 4*m+3) for m in range(1, 41)))
    # arcsin chain tail bound (Definition arcsin): |pi - s_n| < 4^-n/(2n+3) for 1 <= n <= 120
    # 13:E3 (p13024)
    family("pi", "R4")
    s_run = Fraction(0); tail_ok = True
    for n in range(0, 121):
        s_run += Fraction(comb(2*n, n), (2*n+1) * 16**n)
        if n >= 1 and not abs(PI - 3*s_run) < Fraction(1, 4**n * (2*n+3)): tail_ok = False
    chk("arcsin chain s_n = 3 sum C(2k,k)/((2k+1)16^k): |pi - s_n| < 4^-n/(2n+3) for n = 1..120", tail_ok)

    # feasibility table
    log_pi("(c) precision-cost (terms n for 2^-k):")
    for k in (24, 53, 333):
        nL = 2**k            # Leibniz/Wallis ~ error 1/n
        nM = math.ceil((k*math.log(2)/math.log(5) - 3)/2)   # Machin ~ 5^{-2N}
        nA = math.ceil(k/2)  # arcsin(1/2) ~ 4^{-n}
        log_pi(f"    k={k:3d}: Wallis/Leibniz ~ {nL:.1e}   Machin ~ {nM}   arcsin(1/2) ~ {nA}   (e-chain reference: {[11,18,70][(24,53,333).index(k)]})")

    # =========================================================
    log_pi(); log_pi("="*72); log_pi("[2] WALL ARITHMETIC (mod p)")
    log_pi("="*72)
    def Cmod_track(p, nmax):
        """return list over n=1..nmax of (vp, unit) for C(2n,n): p-adic valuation and unit part mod p"""
        res = []
        e, u = 0, 1  # C(2,1)=2 handled in loop start from n=0: C(0,0)=1
        # iterate C(2(n+1),n+1) = C(2n,n)*2*(2n+1)/(n+1)
        cur_e, cur_u = 0, 1
        for n in range(0, nmax):
            num = 2*(2*n + 1); den = n + 1
            while num % p == 0: num //= p; cur_e += 1
            while den % p == 0: den //= p; cur_e -= 1
            cur_u = cur_u * (num % p) % p
            cur_u = cur_u * pow(den % p, -1, p) % p
            res.append((cur_e, cur_u))  # this is C(2(n+1), n+1)
        return res

    samples = [5, 13, 29, 101, 257, 1009, 10007]
    log_pi(f"{'p':>6} | window [1,2t] all legible | (2t,p) all blind | k(w_wall) | v blind at wall (den=p)")
    for p in samples:
        t2 = (p - 1)//2
        trk = Cmod_track(p, p - 1)
        legible = all(trk[n-1][0] == 0 for n in range(1, t2 + 1))
        blind   = all(trk[n-1][0] >= 1 for n in range(t2 + 1, p))
        e_, u_ = trk[t2 - 1]  # C(2*2t choose 2t) = C(p-1, (p-1)/2)
        wall = pow(16, t2, p) * pow(t2 % p, -1, p) * pow(u_*u_ % p, -1, p) % p if e_ == 0 else None
        log_pi(f"{p:6d} |          {'PASS' if legible else 'FAIL'}          |      {'PASS' if blind else 'FAIL'}      |   {(wall - p) if wall and wall > p//2 else wall}      |  2*2t+1 = {2*t2+1} = p: {'YES' if 2*t2+1==p else 'NO'}")
        # 13:G1 (p13034), 13:G2 (p13035)
        family("pi", "W1")
        chk(f"p={p}: p does not divide C(2n,n) for 1 <= n <= m", legible)
        chk(f"p={p}: p divides C(2n,n) for m < n < p", blind)
        chk(f"p={p}: [w_m] == -2 == m^-1 == 4 pi_A", wall == p - 2 == pow(t2, -1, p) == 4 * t2 % p)
        chk(f"p={p}: the lower chain is blind exactly at the wall, 2m+1 = p", 2*t2 + 1 == p)

    # also p == 3 mod 4
    p3ok = True
    for p in [7, 23, 1031]:
        m = (p-1)//2
        C = 1
        for n in range(m): C = C * 2*(2*n+1) % p * pow(n+1, -1, p) % p
        wall = pow(16, m, p) * pow(m, -1, p) * pow(C*C % p, -1, p) % p
        if wall != p - 2: p3ok = False
    log_pi(f"universal wall residue -2 also for p == 3 (mod 4) [7, 23, 1031]: {'PASS' if p3ok else 'FAIL'}")
    family("pi", "W2")
    chk("[w_m] == -2 for p == 3 (mod 4), p in {7, 23, 1031}", p3ok)

    # =========================================================
    log_pi(); log_pi("="*72); log_pi("[3] SECOND ORDER: Morley, Fermat quotient, pi-Wieferich")
    log_pi("="*72)
    morley_ok = True; formula_ok = True
    rows = []
    for p in [13, 29, 37, 41, 53, 101]:
        m = (p-1)//2
        C = comb(p-1, m)
        # Morley mod p^3
        if ((-1)**m * C - pow(4, p-1, p**3)) % p**3 != 0: morley_ok = False
        W = Fraction(16**m, m * C * C)
        k2 = W.numerator * pow(W.denominator, -1, p*p) % (p*p)
        q4 = (pow(4, p-1, p*p) - 1)//p % p
        pred = (-2 + 2*p*(q4 - 1)) % (p*p)
        if k2 != pred: formula_ok = False
        rows.append((p, (k2 - p*p) , q4))
    log_pi(f"Morley: (-1)^m C(p-1,m) == 4^(p-1) (mod p^3) for p in [13..101]: {'PASS' if morley_ok else 'FAIL'}")
    log_pi(f"Second-order wall formula W == -2 + 2p(q_p(4)-1) (mod p^2): {'PASS' if formula_ok else 'FAIL'}")
    log_pi(f"  (p, W mod p^2 as negative lift, q_p(4) mod p): {rows[:4]}")
    # 13:G4 (p13037)
    family("pi", "S1")
    chk("Morley (-1)^m C(p-1,m) == 4^(p-1) (mod p^3) for p in {13, 29, 37, 41, 53, 101}", morley_ok)
    chk("w_m == -2 + 2p(q_p(4) - 1) (mod p^2) for the same primes", formula_ok)
    chk("q_p(4) == 2 q_p(2) (mod p) for the same primes", all((pow(4, p-1, p*p) - 1)//p % p == 2 * ((pow(2, p-1, p*p) - 1)//p) % p for p in [13, 29, 37, 41, 53, 101]))

    # pi-Wieferich search: 4^(p-1) == 1 + p (mod p^2)
    hits = []
    LIM = 1000000
    for p in sieve_pi(LIM):
        if pow(4, p-1, p*p) == (1 + p) % (p*p):
            hits.append(p)
    log_pi(f"pi-Wieferich primes (W == -2 mod p^2), p < 10^6: {hits if hits else 'none'}  "
        f"(heuristic expectation ~ sum 1/p ~ {sum(1/q for q in sieve_pi(LIM)):.2f} ... over the range)")
    family("pi", "S2")
    chk("pi-Wieferich primes below 10^6 are exactly {5, 45827}", hits == [5, 45827])

    # the pi-Wieferich condition in three forms, Eisenstein's harmonic form and the OEIS A355959 form (13:G10)
    # 13:G10 (p13067)
    family("pi", "S3")
    S3 = [5, 13, 29, 37, 41, 53, 101, 45827]
    def fq(a, p): return (pow(a, p-1, p*p) - 1)//p             # the Fermat quotient q_p(a) reduced to [0, p)
    def fq_exact(a, p): return (a**(p-1) - 1)//p               # the Fermat quotient as the integer (a^(p-1) - 1)/p
    def H(m, p): return sum(pow(j, -1, p) for j in range(1, m+1)) % p
    chk("q_p(4) = 2 q_p(2) + p q_p(2)^2 exactly (as integers) for p in {5, 13, 29, 37, 41, 53, 101, 45827}",
        all(fq_exact(4, p) == 2*fq_exact(2, p) + p*fq_exact(2, p)**2 for p in S3))
    chk("the three forms agree on the same primes: 4^(p-1) == 1 + p (mod p^2) iff q_p(4) == 1 iff 2 q_p(2) == 1 (mod p)",
        all((pow(4, p-1, p*p) == (1 + p) % (p*p)) == (fq(4, p) % p == 1) == (2*fq(2, p) % p == 1) for p in S3))
    chk("Eisenstein: 2 q_p(2) == -H_((p-1)/2) (mod p), H_m = sum_(j<=m) 1/j, on the same primes",
        all(2*fq(2, p) % p == (-H((p-1)//2, p)) % p for p in S3))
    chk("OEIS A355959: (p+2)^(p-1) == 1 (mod p^2) iff 2 q_p(2) == 1 (mod p) on the same primes, holding at 5 and 45827 only",
        all((pow(p+2, p-1, p*p) == 1) == (2*fq(2, p) % p == 1) for p in S3)
        and [p for p in S3 if pow(p+2, p-1, p*p) == 1] == [5, 45827])

    # distribution of q_p(4) mod p (uniformity check via normalized mean/var on p<20000)
    vals = []
    for p in sieve_pi(20000):
        q4 = (pow(4, p-1, p*p) - 1)//p % p
        vals.append(q4/p)
    mean = sum(vals)/len(vals); var = sum((x-mean)**2 for x in vals)/len(vals)
    log_pi(f"q_p(4)/p over p<20000: mean {mean:.4f} (uniform: 0.5), variance {var:.4f} (uniform: 0.0833)")

    # =========================================================
    log_pi(); log_pi("="*72); log_pi("[4] LUCAS REVIVALS AND SELF-SIMILARITY")
    log_pi("="*72)
    p = 13
    Cv = comb(26, 13) % p
    vres = 2 * pow(16, 13, p) * pow((27 % p) * Cv * Cv % p, -1, p) % p
    log_pi(f"p=13: C(26,13) mod 13 = {Cv} = C(2,1)*C(0,0); k(v_13) = {vres} (predicted universal 8: {'PASS' if vres==8 else 'FAIL'})")
    C28 = comb(28, 14) % 13
    log_pi(f"p=13, n=14=(1,1)_13: C(28,14) mod 13 = {C28} = C(2,1)^2 = 4 digitwise (Lucas): {'PASS' if C28==4 else 'FAIL'}")
    # density of legible n in [p, p^2): digits all <= (p-1)/2 and n not = 0 mod p etc.
    p = 13; cnt = 0
    for n in range(p, p*p):
        a, b = divmod(n, p)
        if a <= 6 and b <= 6 and n % p != 0 and comb(2*n, n) % p != 0: cnt += 1
    log_pi(f"p=13: legible w-scales in [13,169): {cnt}/156 = {cnt/156:.3f} (prediction ((2t+1)/p)^2-ish = {(7/13)**2:.3f}, minus n==0 mod p column)")
    # 13:G5 (p13038)
    family("pi", "L1")
    chk("p=13: C(26,13) == 2 == C(2,1) C(0,0) (mod 13) and [v_13] == 8", Cv == 2 and vres == 8)
    chk("p=13: C(28,14) == 4 == C(2,1)^2 (mod 13), Lucas digitwise", C28 == 4)
    chk("p=13: two-digit revival scales in [13, 169) number exactly (2 kappa)^2 = 36", cnt == 36)
    chk("[v_p] == 8 universally, p in {5, 7, 11, 13, 29, 37}", all(2 * pow(16, q, q) * pow((2*q+1) % q * pow(comb(2*q, q), 2, q) % q, -1, q) % q == 8 % q for q in [5, 7, 11, 13, 29, 37]))

    # =========================================================
    log_pi(); log_pi("="*72); log_pi("[5] ARCSIN(1/2) CHAIN WALL: T(p) and second order")
    log_pi("="*72)
    def T_mod(p):
        m = (p-1)//2
        s = 0; C = 1  # C(0,0)
        inv16 = pow(16, -1, p)
        pw = 1
        for k in range(m):
            if k > 0:
                C = C * 2*(2*k-1) % p * pow(k, -1, p) % p
                pw = pw * inv16 % p
            s = (s + C * pw % p * pow(2*k+1, -1, p)) % p
        return s
    zero_all = True; tested = 0
    for p in sieve_pi(3000):
        if p == 3:
            if T_mod(p) == 0: zero_all = False; log_pi("  T(3) == 0 (expected nonzero: sole exception)!")
            continue
        if T_mod(p) != 0: zero_all = False; log_pi(f"  T({p}) != 0 !")
        tested += 1
    log_pi(f"T(p) := sum_(k=0)^(m-1) C(2k,k)/((2k+1)16^k) == 0 (mod p) for all odd primes 5<=p<3000 (p=3 is the sole exception, T(3)={T_mod(3)}): {'PASS' if zero_all else 'FAIL'} ({tested} primes)")
    # 13:G6 (p13039)
    family("pi", "V1")
    chk("sigma_p == 0 (mod p) for all 428 odd primes 5 <= p < 3000", zero_all and tested == 428)
    chk("sigma_3 = 1, the sole exception", T_mod(3) == 1)

    # second order: sigma/p mod p, pattern hunt
    def euler_numbers_mod(p, upto):
        E = [0]*(upto+1); E[0] = 1
        for n in range(1, upto//2 + 1):
            s = 0
            for j in range(n):
                s += comb(2*n, 2*j) * E[2*j]
            E[2*n] = (-s) % p
        return E
    def two_squares(p):
        # p = a^2 + b^2, p == 1 mod 4; a odd normalized a == 1 mod 4? return (a,b) a odd
        for a in range(1, int(p**0.5)+1):
            b2 = p - a*a
            b = int(b2**0.5)
            if b*b == b2: 
                if a % 2 == 1: return a, b
                return b, a
        return None
    log_pi("second-order invariant T2(p) := (sigma/p) mod p, sigma the exact rational partial sum:")
    log_pi(f"{'p':>4} | T2 | E_(p-3) | q_p(2) | a (p=a^2+b^2) | T2/E | T2/q2")
    pat = []
    for p in [q for q in sieve_pi(200) if q > 3]:
        m = (p-1)//2
        sigma = sum(Fraction(comb(2*k,k), (2*k+1)*16**k) for k in range(m))
        num, den = sigma.numerator, sigma.denominator
        chk(f"p={p}: the rational sigma_p has numerator divisible by p and denominator prime to p", num % p == 0 and den % p != 0)
        T2 = (num//p) * pow(den, -1, p) % p
        E = euler_numbers_mod(p, p-3)[p-3]
        q2 = (pow(2, p-1, p*p) - 1)//p % p
        ts = two_squares(p) if p % 4 == 1 else None
        rE = T2 * pow(E, -1, p) % p if E else None
        rq = T2 * pow(q2, -1, p) % p if q2 else None
        pat.append((p, T2, E, q2, ts, rE, rq))
        log_pi(f"{p:4d} | {T2:3d} | {E:5d} | {q2:4d} | {str(ts):>10} | {str(rE):>4} | {str(rq):>4}")

    # also Leibniz wall U(p) and ratio to E_(p-3)
    log_pi()
    log_pi("Leibniz wall U(p) := sum_(k=0)^(m-1) (-1)^k/(2k+1) mod p, ratio to E_(p-3):")
    for p in [q for q in sieve_pi(120) if q > 3]:
        m = (p-1)//2
        U = sum((-1)**k * pow(2*k+1, -1, p) for k in range(m)) % p
        E = euler_numbers_mod(p, p-3)[p-3]
        r = U * pow(E, -1, p) % p if E else None
        log_pi(f"  p={p:3d}: U={U:3d}  E_(p-3)={E:4d}  U/E={r}")

    # =========================================================
    log_pi(); log_pi("="*72); log_pi("[6] ANGULAR EXACTNESS AND GAUSS SUM")
    log_pi("="*72)
    for p in [13, 101, 1009, 10007]:
        re = sum(math.cos(2*math.pi*(x*x % p)/p) for x in range(p))
        im = sum(math.sin(2*math.pi*(x*x % p)/p) for x in range(p))
        log_pi(f"  p={p:6d}: Gauss sum = {re:.6f} + {im:.2e} i;  sqrt(p) = {math.sqrt(p):.6f}  (class: +sqrt(p) if p==1 mod 4, +i*sqrt(p) if p==3 mod 4)")
    log_pi("angle of -1 on the multiplicative circle: 2pi * (2t)/(4t) = pi exactly, every frame, both chiralities.")


    flush("pi", order=["R1", "R2", "R3", "R4", "W1", "W2", "S1", "S2", "S3", "L1", "V1"])

# ------------------------------------------------------------------------------------------------------------
# block pi2 — validate_pi2.py: Follow-up: quarter-wall two-squares invariant, arcsin supercongruence, proof sanity checks.
#
# Package form (2026-09): the script as written, its PASS/FAIL lines turned into registry predicates
# (families pi2.A1-A2, pi2.B1-B2, pi2.C1-C4, pi2.D1-D2). Exact arithmetic only: integers and fractions.Fraction.
OUT_pi2 = []
def log_pi2(s=""):
    print(s); OUT_pi2.append(str(s))

def sieve_pi2(N):
    c = bytearray(N + 1)
    for i in range(2, int(N**0.5) + 1):
        if not c[i]: c[i*i::i] = b'\x01' * len(c[i*i::i])
    return [i for i in range(3, N + 1) if not c[i]]

def two_squares(p):
    for a in range(1, int(p**0.5) + 1):
        b = int((p - a*a)**0.5)
        if a*a + b*b == p:
            return (a, b) if a % 2 == 1 else (b, a)
    return None

def block_pi2():
    """Block pi2 — the two-squares quarter invariant, Sun's supercongruence and the Bernoulli law, the proof ingredients, the blind-range Euler congruence, the revival to p² (pi2.A1 … pi2.D2)."""
    # ---- [A] Quarter-wall: Gauss congruence C(2t,t) == 2a (mod p), a odd, a == 1 (mod 4);
    #          and k(w_t) == -(a^2)^{-1} == (b^2)^{-1} (mod p)
    log_pi2("[A] QUARTER-WALL TWO-SQUARES INVARIANT, all p == 1 (mod 4), p < 3000")
    ok_g, ok_w, cnt = True, True, 0
    for p in [q for q in sieve_pi2(3000) if q % 4 == 1]:
        t = (p - 1)//4
        a, b = two_squares(p)
        astar = a if a % 4 == 1 else -a           # Gauss normalization
        C = 1
        for n in range(t): C = C * 2*(2*n+1) % p * pow(n+1, -1, p) % p   # C(2t,t) mod p
        if C != (2*astar) % p: ok_g = False; log_pi2(f"  Gauss fails at p={p}")
        # 13:G3 (p13036)
        chk(f"p={p}: C(2t,t) == 2a* (mod p)", C == (2*astar) % p, "pi2", "A1")
        kw = pow(16, t, p) * pow(t % p, -1, p) % p * pow(C*C % p, -1, p) % p
        if kw != (-pow(a*a % p, -1, p)) % p or kw != pow(b*b % p, -1, p) % p:
            ok_w = False; log_pi2(f"  wall formula fails at p={p}")
        chk(f"p={p}: [w_t] == -(a^2)^-1 == (b^2)^-1 (mod p)", kw == (-pow(a*a % p, -1, p)) % p == pow(b*b % p, -1, p) % p, "pi2", "A2")
        cnt += 1
    log_pi2(f"  Gauss congruence C(2t,t) == 2a* (mod p): {'PASS' if ok_g else 'FAIL'} ({cnt} primes)")
    log_pi2(f"  k(w_t) == -(a^2)^(-1) == (b^2)^(-1) (mod p): {'PASS' if ok_w else 'FAIL'}")
    p = 13; a, b = two_squares(13)
    log_pi2(f"  example p=13 = {a}^2+{b}^2: k(w_3) = {pow(16,3,13)*pow(3,-1,13)*pow(pow(comb(6,3),2,13),-1,13)%13} = -(9)^(-1) = 10")
    chk("211 primes p == 1 (mod 4) below 3000", cnt == 211, "pi2", "A1")
    chk("p=13 = 3^2 + 2^2: [w_3] = 10 = -(9)^-1", (a, b) == (3, 2) and pow(16,3,13)*pow(3,-1,13)*pow(pow(comb(6,3),2,13),-1,13) % 13 == 10 == (-pow(9, -1, 13)) % 13, "pi2", "A2")

    # ---- [B] arcsin supercongruence: sigma == 0 (mod p^2) and third-order invariant
    log_pi2(); log_pi2("[B] ARCSIN CHAIN sigma_p := sum_(k=0)^((p-3)/2) C(2k,k)/((2k+1)16^k)")
    ok2 = True
    rows = []
    def euler_mod(p, upto):
        E = [0]*(upto+1); E[0] = 1 % p
        for n in range(1, upto//2 + 1):
            s = sum(comb(2*n, 2*j) * E[2*j] for j in range(n))
            E[2*n] = (-s) % p
        return E
    def bernoulli_upto(N):
        """Exact Bernoulli numbers B_0..B_N via sum C(n+1,k) B_k = 0."""
        B = [Fraction(0)] * (N + 1); B[0] = Fraction(1)
        for n in range(1, N + 1):
            B[n] = -sum(Fraction(comb(n+1, k)) * B[k] for k in range(n)) / (n + 1)
        return B
    BERN = bernoulli_upto(297)
    for p in [q for q in sieve_pi2(300) if q >= 5]:
        m = (p-1)//2
        sig = sum(Fraction(comb(2*k, k), (2*k+1)*16**k) for k in range(m))
        num, den = sig.numerator, sig.denominator
        if num % (p*p) != 0: ok2 = False; log_pi2(f"  p^2 fails at p={p}")
        chk(f"p={p}: sigma_p == 0 (mod p^2)", num % (p*p) == 0 and den % p != 0, "pi2", "B1")
        T3 = (num//(p*p)) % p * pow(den % p, -1, p) % p
        Bpm3 = BERN[p-3]
        bmod = Bpm3.numerator % p * pow(Bpm3.denominator % p, -1, p) % p
        law = (-1)**((p+1)//2) * bmod % p * pow(36, -1, p) % p
        rows.append((p, T3, law))
        chk(f"p={p}: sigma_p/p^2 == (-1)^((p+1)/2) B_(p-3)/36 (mod p)", T3 == law, "pi2", "B2")
    log_pi2(f"  sigma == 0 (mod p^2) for all 5 <= p < 300: {'PASS' if ok2 else 'FAIL'}")
    okB3 = all(T3 == law for _, T3, law in rows)
    log_pi2(f"  third-order Bernoulli law sigma/p^2 == (-1)^((p+1)/2) B_(p-3)/36 (mod p), 5<=p<300: "
        f"{'PASS' if okB3 else 'FAIL'} ({len(rows)} primes)  [mod-p^3 reading of Sun Conj. 5.1 + Wolstenholme refinement]")
    log_pi2("  p, sigma/p^2 mod p, law: " + str([(p, t, l) for p, t, l in rows[:8]]))
    chk("sixty primes 5 <= p < 300", len(rows) == 60, "pi2", "B2")

    # ---- [C] proof sanity checks
    log_pi2(); log_pi2("[C] PROOF INGREDIENTS")
    okc = True
    for p in [11, 13, 29, 37]:
        m = (p-1)//2
        for k in range(m):
            if comb(2*k, k) % p != pow(-4, k, p) * comb(m, k) % p: okc = False
    log_pi2(f"  C(2k,k) == (-4)^k binom(m,k) (mod p), k < m: {'PASS' if okc else 'FAIL'}")
    chk("C(2k,k) == (-4)^k C(m,k) (mod p) for k < m, p in {11, 13, 29, 37}", okc, "pi2", "C1")
    okl = True
    for p in [q for q in sieve_pi2(500) if q >= 5]:
        m = (p-1)//2
        H = sum(pow(j, -1, p) for j in range(1, m+1)) % p
        q2 = (pow(2, p-1, p*p) - 1)//p % p
        if H != (-2*q2) % p: okl = False
    log_pi2(f"  Lerch: H_((p-1)/2) == -2 q_p(2) (mod p): {'PASS' if okl else 'FAIL'}")
    chk("Lerch H_((p-1)/2) == -2 q_p(2) (mod p) for 5 <= p < 500", okl, "pi2", "C2")
    okI = True
    for m in range(1, 61):
        L = sum(Fraction(comb(m, j)*(-1)**j, 2*j+1) for j in range(m+1))
        if L != Fraction(4**m * math.factorial(m)**2, math.factorial(2*m+1)): okI = False
    log_pi2(f"  L_m = sum binom(m,j)(-1)^j/(2j+1) = 4^m (m!)^2/(2m+1)!, m<=60: {'PASS' if okI else 'FAIL'}")
    chk("L_m = 4^m (m!)^2/(2m+1)! over Q for m <= 60", okI, "pi2", "C3")
    okB = True
    for m in range(1, 61):
        y = Fraction(-1, 4)
        B = sum(comb(m, k)*y**k/(k+m+1) for k in range(m+1))
        A = sum(comb(m, k)*y**k/(2*k+1) for k in range(m+1))
        L = sum(Fraction(comb(m, j)*(-1)**j, 2*j+1) for j in range(m+1))
        # finite proof route (round-01): F = formal antiderivative of expanded (1-s^2)^m;
        # A = 2(F(1/2)-F(0)), B = 2(F(1)-F(1/2)), 2L = 2(F(1)-F(0)) -- coefficient bookkeeping only
        def F(s):
            return sum(Fraction(comb(m, j)*(-1)**j) * s**(2*j+1) / (2*j+1) for j in range(m+1))
        if A + B != 2*L: okB = False
        if A != 2*(F(Fraction(1, 2)) - F(Fraction(0))): okB = False
        if B != 2*(F(Fraction(1)) - F(Fraction(1, 2))): okB = False
        if L != F(Fraction(1)) - F(Fraction(0)): okB = False
    log_pi2(f"  key identity A_m + B_m = 2 L_m over Q, via formal-antiderivative bookkeeping, m<=60: {'PASS' if okB else 'FAIL'}")
    chk("A_m + B_m = 2 L_m with A = 2(F(1/2)-F(0)), B = 2(F(1)-F(1/2)), L = F(1)-F(0) for m <= 60", okB, "pi2", "C4")

    # ---- [D] blind-range Euler congruence and refined revival residue
    log_pi2(); log_pi2("[D] BLIND-RANGE AND REVIVAL REFINEMENTS")
    okU = True
    for p in [q for q in sieve_pi2(80) if q >= 5]:
        m = (p-1)//2
        Us = sum(Fraction(comb(2*k, k), (2*k+1)*16**k) for k in range(m+1, p))
        E = euler_mod(p, p-3)[p-3]
        lhs = Us.numerator * pow(Us.denominator, -1, p*p) % (p*p)
        rhs = p*E % (p*p) * pow(3, -1, p*p) % (p*p)
        if lhs != rhs: okU = False
    log_pi2(f"  blind-range sum == p*E_(p-3)/3 (mod p^2), 5<=p<80: {'PASS' if okU else 'FAIL'}  [known: van Hamme-Sun family]")
    chk("blind-range sum == p E_(p-3)/3 (mod p^2) for 5 <= p < 80", okU, "pi2", "D1")
    okR = True
    for p in [5, 7, 11, 13, 29, 37]:
        v = Fraction(2*16**p, (2*p+1)*comb(2*p, p)**2)
        lhs = v.numerator * pow(v.denominator, -1, p*p) % (p*p)
        q2 = (pow(2, p-1, p*p) - 1)//p % p
        if lhs != (8 + 16*p*(2*q2 - 1)) % (p*p): okR = False
    log_pi2(f"  first revival v_p == 8 + 16p(2q_p(2)-1) (mod p^2): {'PASS' if okR else 'FAIL'}  [via Wolstenholme]")
    chk("v_p == 8 + 16p(2 q_p(2) - 1) (mod p^2) for p in {5, 7, 11, 13, 29, 37}", okR, "pi2", "D2")


    flush("pi2", order=["A1", "A2", "B1", "B2", "C1", "C2", "C3", "C4", "D1", "D2"])

# ------------------------------------------------------------------------------------------------------------
# block tow — validate_towers.py: validate_towers.py -- 13-epi fixed-shell towers, Cayley identities, orientation rule.
# Exact arithmetic only: integers and fractions.Fraction. No floats anywhere.
# External comparisons use the paper's own certified rational brackets.
# Package form (2026-09): the paper's script as written, its micro-checks reported to the registry under the
# families tow.E (e-tower), tow.P (π-tower), tow.C (Cayley), tow.O (orientation), tow.H (height run), tow.W (window
# and pins); a failing micro-check_tow prints and fails its family without stopping the run.
def check_tow(name, cond):
    chk(name, cond)

def subfact(n):
    d = [1, 0]
    for k in range(2, n+1):
        d.append(k*d[-1] + (-1)**k)
    return d[n]

def C(n, k):
    return math.comb(n, k)

def e_brackets(n):
    """Certified bracket for e via the subfactorial chain: eps_{2m} < e < eps_{2m+1}."""
    lo = F(math.factorial(2*n), subfact(2*n))
    hi = F(math.factorial(2*n+1), subfact(2*n+1))
    return lo, hi

def pi_brackets(m):
    """Certified Machin brackets: L_m < pi < U_m (alternating pairing)."""
    def AN(x, N):
        return sum(F((-1)**k, (2*k+1)*x**(2*k+1)) for k in range(N+1))
    L = 16*AN(5, 2*m+1) - 4*AN(239, 2*m)
    U = 16*AN(5, 2*m)   - 4*AN(239, 2*m+1)
    return L, U

def centered(x, p):
    x %= p
    return x - p if x > (p-1)//2 else x

def primitive_root(p):
    fac = set()
    n = p-1
    d = 2
    while d*d <= n:
        while n % d == 0:
            fac.add(d); n //= d
        d += 1
    if n > 1: fac.add(n)
    for g in range(2, p):
        if all(pow(g, (p-1)//q, p) != 1 for q in fac):
            return g
    raise ValueError

def block_tow():
  """Block tow — the fixed-shell towers, the Cayley map, orientation transport, the height run, the wrap-free window and the pins (tow.E … tow.W)."""
  for p in (13, 29):
    kap = (p-1)//4
    g = primitive_root(p)
    i = pow(g, p-1-kap, p)              # i = g^{-kap}
    # 13:H2 (p13044), 13:I4 (p13051), 13:J1 (p13052)
    family("tow", "W")
    check_tow(f"p={p}: i^2 = -1", (i*i) % p == p-1)
    lam = i                              # label lift: canonical representative read as exponent
    eP = pow(g, lam, p)
    piA = (2*kap) % p

    # --- e-tower: q_m = ((mp)! + delta_m)/!(mp), shell reading = eP, external -> e ---
    # 13:B3 (p13010), 13:F7 (p13033)
    family("tow", "E")
    for m in (1, 2, 3):
        delta = centered(((-1)**m * eP) % p, p)
        num = math.factorial(m*p) + delta
        den = subfact(m*p)
        check_tow(f"p={p} e-tower grade {m}: !(mp) == (-1)^m (mod p)", den % p == ((-1)**m) % p)
        check_tow(f"p={p} e-tower grade {m}: shell reading = e_p", (num * pow(den % p, p-2, p)) % p == eP)
        lo, hi = e_brackets(max(m*p//2, 12))
        q = F(num, den)
        # the paper's certificate: |q - e| < (mp)!/( !(mp) !(mp+1) ) + pi_F/!(mp)
        width = F(math.factorial(m*p), den*subfact(m*p+1)) + F((p-1)//2, den)
        check_tow(f"p={p} e-tower grade {m}: |q - e| inside certified window",
              q > lo - width and q < hi + width)

    # --- pi-tower: (2*16^n + delta)/((2n+1) C(2n,n)^2), n = p^r ---
    # 13:G9 (p13042)
    family("tow", "P")
    for r in (1, 2):
        n = p**r
        Cb = C(2*n, n)
        Bn = (2*n+1) * Cb * Cb
        check_tow(f"p={p} pi-tower r={r}: C(2n,n) == 2 (mod p)", Cb % p == 2)
        check_tow(f"p={p} pi-tower r={r}: 16^n == 16 (mod p)", pow(16, n, p) == 16 % p)
        delta = centered((piA * Bn - 2*pow(16, n)) % p, p)
        check_tow(f"p={p} pi-tower r={r}: delta = centered(-34)", delta == centered(-34 % p, p))
        num = 2*pow(16, n) + delta
        check_tow(f"p={p} pi-tower r={r}: shell reading = pi_A",
              (num * pow(Bn % p, p-2, p)) % p == piA)
        if r == 1:
            L, U = pi_brackets(8)
            v = F(num, Bn)
            check_tow(f"p={p} pi-tower r=1: member below the certified upper bracket", v < U)
            check_tow(f"p={p} pi-tower r=1: member above v_n floor", v > F(2*4**n, (2*n+1)*Cb*Cb) - F(1))

    # --- Cayley identities, exhaustive where denominators are units ---
    # 13:C3 (p13014)
    family("tow", "C")
    cnt = 0
    for x in range(p):
        for y in range(p):
            dx, dy = (1 - i*x) % p, (1 - i*y) % p
            dxy = (1 - x*y) % p
            if dx and dy and dxy:
                num_c = ((x + y) * pow(dxy, p-2, p)) % p
                dc = (1 - i*num_c) % p
                if dc:
                    Cx = ((1 + i*x) * pow(dx, p-2, p)) % p
                    Cy = ((1 + i*y) * pow(dy, p-2, p)) % p
                    Cc = ((1 + i*num_c) * pow(dc, p-2, p)) % p
                    if (Cx*Cy) % p != Cc:
                        check_tow(f"p={p} Cayley composition at ({x},{y})", False)
                    cnt += 1
    check_tow(f"p={p} Cayley composition exhaustive ({cnt} pairs)", True)
    check_tow(f"p={p} Cayley C(0)=1", ((1) * pow(1, p-2, p)) % p == 1)
    check_tow(f"p={p} Cayley C(1)=i", ((1+i) * pow((1-i) % p, p-2, p)) % p == i)

    # --- orientation rule: u = 1 mod 4 preserves i, u = 3 mod 4 conjugates ---
    # 13:B2 (p13009)
    family("tow", "O")
    for u in range(1, p-1):
        if math.gcd(u, p-1) != 1:
            continue
        gp = pow(g, u, p)
        ip = pow(gp, p-1-kap, p)
        if u % 4 == 1:
            if ip != i: check_tow(f"p={p} orientation u={u} (u=1 mod 4) preserves i", False)
        else:
            if ip != (p - i) % p: check_tow(f"p={p} orientation u={u} (u=3 mod 4) conjugates i", False)
    check_tow(f"p={p} orientation-transport rule exhaustive over units", True)


  _run_tail()

# --- two-level horizon law: minimal framed-rational heights ---
def minheight(x, p):
    best = p
    for b in range(1, best+1):
        a = (x*b) % p
        a = a - p if a > p//2 else a
        h = max(abs(a), b)
        if h < best: best = h
        if b > best: break
    return best

# Full-population height run (round-02): all shells p == 1 (mod 4), p <= 8009;
# smallest-primitive-root frame, H minimized over the two chirality units.
def _sieve(N):
    c = bytearray(N+1)
    for i in range(2, _m.isqrt(N)+1):
        if not c[i]: c[i*i::i] = b'\x01'*len(c[i*i::i])
    return [i for i in range(3, N+1) if not c[i]]
def _run_tail():
  # 13:J2 (p13053), 13:J3 (p13054), 13:J5 (p13056)
  family("tow", "H")
  hs = []
  pin_ok = True; band_ok = True
  for p in [q for q in _sieve(8009) if q % 4 == 1]:
      kap = (p-1)//4
      g = primitive_root(p)                      # iterates from 2: the smallest primitive root
      e_neg = pow(g, pow(g, p-1-kap, p), p)      # exponential unit, oriented chirality  i = g^{-kap}
      e_pos = pow(g, pow(g, kap, p), p)          # exponential unit, conjugate chirality i' = g^{+kap}
      piA = (2*kap) % p
      if not ((piA * (-2)) % p == 1 and minheight(piA, p) == 2): pin_ok = False
      h = min(minheight(e_neg, p), minheight(e_pos, p))
      if h > 2*_m.isqrt(p): band_ok = False
      hs.append((p, h, _m.isqrt(p)))
  check_tow("pi_A = [-1/2] pinned at height 2 on all 500 shells p <= 8009", pin_ok and len(hs) == 500)
  check_tow("H(e_p) within the horizon band 2 sqrt(p) on every shell", band_ok)
  small = sorted(p for p, h, s in hs if h <= 10)
  exc2 = sorted(p for p, h, s in hs if h == 2)
  ratios = sorted(h/s for p, h, s in hs)
  med = (ratios[249] + ratios[250]) / 2
  _MED[0] = med
  check_tow("small-height shells (H <= 10): exactly 68", len(small) == 68)
  check_tow("height-2 shells exactly {13, 1933, 4177, 5857}", exc2 == [13, 1933, 4177, 5857])
  # growth reading (exact counts; the generic-growth interpretation is DFI-equidistribution [import])
  print(f"height run: 500 shells, median H/sqrt(p) = {med:.3f}, H<=10: {len(small)}, height-2: {exc2}")


  # --- accessible window: wrap-free below sqrt(p); pinning relations; the half-turn tautology ---
  family("tow", "W")
  for p in (13, 29, 101, 997, 8009):
      s = _m.isqrt(p)
      check_tow(f"p={p}: wrap-free window (isqrt(p)^2 < p, sums below p)", s*s < p and 2*s < p)
      kap = (p-1)//4
      piA = (2*kap) % p
      check_tow(f"p={p}: pinning relation 2*pi_A + 1 == 0 (the shell calibration)", (2*piA + 1) % p == 0)
      g = primitive_root(p)
      check_tow(f"p={p}: half-turn tautology g^(2 kap) == -1 (the exact angular carrier of pi)", pow(g, 2*kap, p) == p - 1)
      i = pow(g, p-1-kap, p)
      check_tow(f"p={p}: quarter-turn pin i^2 + 1 == 0", (i*i + 1) % p == 0)
  flush("tow", order=list("EPCOHW"), details={"H": f"median H/sqrt(p) = {_MED[0]:.3f} (diagnostic)"})

_MED = [0.0]

# ------------------------------------------------------------------------------------------------------------
# block kur — kurepa_wall.py: kurepa_wall.py — the Kurepa wall of e in the derangement form, for all odd primes p < 2.5e5 (block kur.K1).
#
# Compiles and runs kurepa_wall.c (one O(p) pass per prime in 128-bit modular arithmetic, checking
# !(p-1) == K(p) (mod p) and K(p) != 0 (mod p)), and turns its summary line into the registry predicate: 22 043 primes
# checked, zero failures of either condition. A C compiler (cc/gcc/clang) is required; Colab and Debian/macOS provide
# one. Without a compiler the block runs the same pass in pure Python to the bound 2·10⁴ (2 261 primes) and records
# the reduced bound in the check's detail.
N_kur = 250000

def compile_c_kur():
    for cc in ("cc", "gcc", "clang"):
        if shutil.which(cc):
            exe = os.path.join(HERE, "kurepa_wall")
            r = subprocess.run([cc, "-O2", os.path.join(HERE, "kurepa_wall.c"), "-o", exe], capture_output=True, text=True)
            if r.returncode == 0:
                return exe
            print(f"    {cc} failed: {r.stderr.strip()[:200]}")
    return None

def python_pass_kur(N_kur):
    comp = bytearray(N_kur + 1)
    for i in range(2, int(N_kur**0.5) + 1):
        if not comp[i]: comp[i*i::i] = b"\x01" * len(comp[i*i::i])
    checked = kfail = cfail = 0
    for p in range(3, N_kur + 1, 2):
        if comp[p]: continue
        f = s = D = 1; sign = -1
        for k in range(1, p):
            f = f * k % p
            s = (s + f) % p
            D = (D * k + sign) % p
            sign = -sign
        if s == 0: kfail += 1
        if D != s: cfail += 1
        checked += 1
    return checked, kfail, cfail

def block_kur():
    """Block kur — !(p−1) ≡ K(p) and K(p) ≢ 0 for all 22 043 odd primes p < 2.5·10⁵ (kurepa_wall.c, compiled on the fly; a pure-python pass to a smaller bound without a compiler) (kur.K1)."""
    t = time.time()
    exe = compile_c_kur()
    if exe:
        out = subprocess.run([exe, str(N_kur)], capture_output=True, text=True).stdout
        print("    " + out.strip().replace("\n", "\n    "))
        m = re.search(r"primes_checked=(\d+) kurepa_vanishing=(\d+) wall_congruence_failures=(\d+)", out)
        checked, kfail, cfail = (int(x) for x in m.groups()) if m else (0, 1, 1)
        # 13:J6 (p13057), 13:Y1 (p13061)
        family("kur", "K1")
        chk(f"{checked} odd primes p < {N_kur}: exactly 22043", checked == 22043)
        chk("K(p) != 0 (mod p) for every prime checked", kfail == 0)
        chk("!(p-1) == K(p) (mod p) for every prime checked", cfail == 0)
        flush("kur", details={"K1": f"kurepa_wall.c, N = {N_kur}, {time.time() - t:.0f} s"})
    else:
        n = 20000
        checked, kfail, cfail = python_pass_kur(n)
        family("kur", "K1")
        chk(f"{checked} odd primes p < {n}: exactly 2261", checked == 2261)
        chk("K(p) != 0 (mod p) for every prime checked", kfail == 0)
        chk("!(p-1) == K(p) (mod p) for every prime checked", cfail == 0)
        flush("kur", details={"K1": f"NO C COMPILER: pure-Python pass to N_kur = {n} only ({checked} primes), {time.time() - t:.0f} s"})

# ------------------------------------------------------------------------------------------------------------
# block frm — frame_invariants.py: frame_invariants.py — the three frame invariants of the two constants on the 4 783 shells p ≡ 1 (mod 4) below 10⁵
# (block frm.I1; 13:I5).
#
# Compiles and runs frame_invariants.c (one O(p) pass per prime: K(p) mod p, q_p(4) mod p, and p = a² + b² with a ≡ 1
# (mod 4), b > 0 even) and decides, in exact arithmetic, the paper's stated figures: the shell count; the triples at
# p = 13, 233, 30089 and at the Wieferich prime 1093 (q_1093(4) = 0); the 4×4×4 contingency table of (K/p, q_p(4)/p,
# φ/π) against the quarter bins — the first two by rational comparison, the third by the sign of a and |a| against b —
# and its chi-square as an exact rational; the marginal means and variances of K/p and q_p(4)/p by certified rational
# bounds of width 10⁻¹², rounded as the paper states them. The moments of φ/π and of a/√p (the arcsine law) use float arctangents and are
# printed as [approx] readings; the independence reading (chi-square 59.6 on 63 df) is the paper's [approx] statement
# and decides nothing. A C compiler is required; without one the block runs the same pass in pure Python to the bound
# 2·10⁴ and records the reduced bound.
N_frm = 100000

def compile_c_frm():
    for cc in ("cc", "gcc", "clang"):
        if shutil.which(cc):
            exe = os.path.join(HERE, "frame_invariants")
            r = subprocess.run([cc, "-O2", os.path.join(HERE, "frame_invariants.c"), "-o", exe, "-lm"], capture_output=True, text=True)
            if r.returncode == 0:
                return exe
            print(f"    {cc} failed: {r.stderr.strip()[:200]}")
    return None

def python_pass_frm(N_frm):
    comp = bytearray(N_frm + 1)
    for i in range(2, int(N_frm**0.5) + 1):
        if not comp[i]: comp[i*i::i] = b"\x01" * len(comp[i*i::i])
    rows = []
    for p in range(5, N_frm, 4):
        if comp[p]: continue
        f = s = 1
        for k in range(1, p):
            f = f * k % p; s = (s + f) % p
        q4 = (pow(4, p - 1, p * p) - 1) // p
        a = b = 0
        for x in range(1, math.isqrt(p) + 1, 2):
            y = math.isqrt(p - x * x)
            if y * y == p - x * x: a, b = x, y; break
        rows.append((p, s, q4, a if a % 4 == 1 else -a, b))
    return rows

def parse(out):
    return [tuple(int(t) for t in line.split()) for line in out.strip().splitlines() if line.strip()]

def quarter_bin(x):                       # x a Fraction in [0, 1): the index of its quarter
    return min(3, int(4 * x))

def angle_bin(a, b):                      # φ = arg(a + b i) with b > 0: the quarter of φ/π, decided in integers
    if a > 0: return 0 if b < a else 1    # φ < π/4  iff b < a ; else φ ∈ [π/4, π/2)  (a = b never: p odd)
    return 2 if b > -a else 3             # φ ∈ [π/2, 3π/4) iff b > |a| ; else [3π/4, π)

S = 10 ** 12

def moments(xs):
    """Certified bounds on the mean and the variance of the rationals num/den, as (lo, hi) pairs of Fractions:
    each term is bracketed by floor(num*S/den)/S and its successor, so the mean lies in an interval of width 1/S and the
    variance E[x^2] - E[x]^2 in an interval of width < 3/S; no float enters."""
    n = len(xs)
    lo1 = sum(num * S // den for num, den in xs); hi1 = lo1 + n
    lo2 = sum(num * num * S // (den * den) for num, den in xs); hi2 = lo2 + n
    m_lo, m_hi = Fr(lo1, n * S), Fr(hi1, n * S)
    v_lo, v_hi = Fr(lo2, n * S) - m_hi ** 2, Fr(hi2, n * S) - m_lo ** 2
    return (m_lo, m_hi), (v_lo, v_hi)

def rounds_to(bounds, digits, target):
    lo, hi = bounds
    return round(lo, digits) == target and round(hi, digits) == target

def block_frm():
    """Block frm — the triples (K(p)/p, q_p(4)/p, φ/π) on the 4 783 shells p ≡ 1 (mod 4) below 10⁵ (frame_invariants.c, compiled on the fly) (frm.I1)."""
    t = time.time()
    exe = compile_c_frm()
    if exe:
        r = subprocess.run([exe, str(N_frm)], capture_output=True, text=True)
        rows, bound = parse(r.stdout), N_frm
    else:
        bound = 20000
        rows = python_pass_frm(bound)
    n = len(rows)
    byp = {p: (K, q, a, b) for p, K, q, a, b in rows}
    # exact consistency of every triple
    consistent = all(0 < K < p and 0 <= q < p and a % 4 == 1 and b % 2 == 0 and b > 0 and a * a + b * b == p for p, K, q, a, b in rows)
    # the 4×4×4 table, exact
    table = {}
    for p, K, q, a, b in rows:
        key = (quarter_bin(Fr(K, p)), quarter_bin(Fr(q, p)), angle_bin(a, b))
        table[key] = table.get(key, 0) + 1
    E = Fr(n, 64)
    chi = sum((Fr(table.get((i, j, k), 0)) - E) ** 2 / E for i in range(4) for j in range(4) for k in range(4))
    (meanK, varK), (meanQ, varQ) = moments([(K, p) for p, K, q, a, b in rows]), moments([(q, p) for p, K, q, a, b in rows])
    phi = [math.atan2(b, a) / math.pi for p, K, q, a, b in rows]
    meanP = sum(phi) / n; varP = sum((x - meanP) ** 2 for x in phi) / n
    cosv = [a / math.sqrt(p) for p, K, q, a, b in rows]
    meanC = sum(cosv) / n; varC = sum((x - meanC) ** 2 for x in cosv) / n
    print(f"    {n} shells p = 1 (mod 4) below {bound}; K/p: mean {float(meanK[0]):.4f} var {float(varK[0]):.4f}; q_p(4)/p: mean {float(meanQ[0]):.4f} var {float(varQ[0]):.4f} (certified rational bounds, width 1e-12)")
    print(f"    phi/pi: mean {meanP:.4f} var {varP:.4f} [approx]; a/sqrt p: mean {meanC:.3f} var {varC:.3f} [approx] (arcsine law: 0, 1/2); uniform law: 1/2, 1/12 = 0.0833")
    print(f"    4x4x4 table against the product of the quarter bins: chi-square {float(chi):.2f} on 63 df (exact rational {chi.numerator}/{chi.denominator}) [approx reading: consistent with independence]")
    # 13:I5 (p13068), 13:Y3 (p13063)
    family("frm", "I1")
    if bound == N_frm:
        chk("exactly 4783 shells p = 1 (mod 4) below 10^5", n == 4783)
        chk("the triples at p = 13, 233, 30089 are (10, 6, -3+2i), (69, 14, 13+8i), (5260, 7666, -67+160i)",
            byp.get(13) == (10, 6, -3, 2) and byp.get(233) == (69, 14, 13, 8) and byp.get(30089) == (5260, 7666, -67, 160))
        chk("the Wieferich prime 1093 is the one shell with q_p(4) = 0 (q_p(2) = 0 gives q_p(4) = 2q_p(2) + p q_p(2)^2 = 0)",
            byp.get(1093, (0, -1))[1] == 0 and sum(1 for p, K, q, a, b in rows if q == 0) == 1)
        chk("means of K/p and q_p(4)/p round to 0.502 and 0.499, variances to 0.0828 and 0.0831 (certified rational bounds)",
            rounds_to(meanK, 3, Fr(502, 1000)) and rounds_to(meanQ, 3, Fr(499, 1000)) and rounds_to(varK, 4, Fr(828, 10000)) and rounds_to(varQ, 4, Fr(831, 10000)))
        chk("the 4x4x4 chi-square is an exact rational in [59.5, 59.7] (the paper's 59.6 on 63 df)", Fr(595, 10) <= chi <= Fr(597, 10))
    else:
        chk(f"NO C COMPILER: {n} shells p = 1 (mod 4) below {bound} (pure-Python pass)", n > 0)
    chk("every triple consistent: 0 < K(p) < p, 0 <= q_p(4) < p, a = 1 (mod 4), b > 0 even, a^2 + b^2 = p", consistent)
    chk("the 64 cells of the table sum to the shell count", sum(table.values()) == n)
    flush("frm", details={"I1": f"frame_invariants.c, N = {bound}, {time.time() - t:.0f} s" if bound == N_frm else f"NO C COMPILER: pure-Python pass to N = {bound}, {time.time() - t:.0f} s"})

if __name__ == "__main__":
    import time
    want = [a.lower() for a in sys.argv[1:]] or list(BLOCK)
    bad = [b for b in want if b not in BLOCK]
    if bad: sys.exit(f"no block {', '.join(bad)}: the blocks are {', '.join(BLOCK)}")
    t0 = time.time()
    for b in want:
        t = time.time(); print(f"— block {b}"); _run_block(b); print(f"    [block {b}: {time.time() - t:.1f} s]")
    ok = summary(write=(want == list(BLOCK)))
    print(f"{len(RESULTS)} family checks, {len(MICRO)} exact micro-checks, {time.time() - t0:.1f} s" + ("; results.json written" if want == list(BLOCK) else ""))
    sys.exit(0 if ok else 1)
