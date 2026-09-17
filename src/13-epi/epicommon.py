"""
epicommon.py — shared registry for the 13-epi validation package
=================================================================
"Finite Field Realisation of the Classical Constants π and e" (Akhtman, 2026), validation package of the FRC corpus
(finite-ring-space/src/13-epi). Every check is exact: integers, residues, exact rationals (fractions.Fraction); the
external targets e and π enter only as certified rational brackets of the paper's own chains (the subfactorial chain
for e, the Machin chain for π), and the binary64 constants enter as the objects of study of the readout theorems
(compared exactly with correctly rounded framed rationals). No floating-point reference value of either constant
decides any check; the few floating-point figures printed (a Pearson correlation, a median, the Gauss sums) are
[approx]-tagged diagnostics of the paper and decide nothing.

A check of the registry is a *family* of micro-checks — one labelled claim of a script (e.R1, pi.W1, pi2.B2, tow.H,
kur.K1, …) — and names the row(s) of the paper's predicate ledger it witnesses (LEDGER; rows cited as 13:XN). The
ledger's source column cites these check ids in return. Master-ledger rows reached through the paper rows:
00:B8 (13:J1, 13:J3), 00:B9 (13:J4, 13:J5), 00:C13 (13:J3), 00:C14 (13:B2, 13:H2), 00:B1 (13:B4),
00:C24 (13:O2's closed clause, the third-order wall) and 00:C26 (13:O3, the four chains as E- and G-partial sums); 13:O1–O3 stay the paper's open rows, their master rows T7–T9 withdrawn 17 Sep 2026 (obstruction records in reports/daily-push).
"""
import os, json, sys
from collections import OrderedDict

RESULTS = []
MICRO = []             # (script tag, family, label, ok)

LEDGER = {
    # validate_e.py
    "e.R1": "13:D3",
    "e.R2": "13:D4, 13:I1",
    "e.R3": "13:D4",
    "e.R4": "13:D5",
    "e.W1": "13:F1, 13:F2",
    "e.W2": "13:F3",
    "e.W3": "13:F4",
    "e.W4": "13:F6",
    "e.S1": "13:F5, 13:I1",
    "e.A1": "13:H4, 13:I1",
    "e.N1": "13:H5, 13:I1",
    # validate_pi.py
    "pi.R1": "13:E2, 13:C5",
    "pi.R2": "13:G8",
    "pi.R3": "13:E4, 13:I2",
    "pi.R4": "13:E3",
    "pi.W1": "13:G1, 13:G2, 13:I2",
    "pi.W2": "13:G2",
    "pi.S1": "13:G4",
    "pi.S2": "13:G4, 13:I2",
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
    "tow.H": "13:J2, 13:J3",
    "tow.W": "13:J1, 13:J2, 13:G2, 13:H2, 13:I4",
    # kurepa_wall.c
    "kur.K1": "13:F2, 13:O1",
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
}

SCRIPT = {"e": "validate_e", "pi": "validate_pi", "pi2": "validate_pi2", "tow": "validate_towers", "kur": "kurepa_wall"}
_FAM = [None, None]

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
    RESULTS.append({"id": pid, "rows": rows, "script": SCRIPT.get(pid.split(".")[0], pid.split(".")[0]), "label": label, "ok": ok, "detail": detail, "kind": kind})
    print(f"  [{'PASS' if ok else 'FAIL'}] {pid:7s} {kind:5s} [{rows}] {label[:110]}" + (f"  --  {detail}" if detail else ""))
    return ok

def summary(write=True):
    n_ok = sum(r["ok"] for r in RESULTS)
    print(f"\nSUMMARY: {n_ok}/{len(RESULTS)} checks passed ({len(MICRO)} exact micro-checks)" + ("" if n_ok == len(RESULTS) else "  <-- FAILURES"))
    if write:
        with open("results.json", "w") as f:
            json.dump(RESULTS, f, indent=1, ensure_ascii=False)
    return n_ok == len(RESULTS)
