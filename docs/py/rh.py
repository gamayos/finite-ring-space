"""
rh.py — the validation package of "Riemann Hypothesis over Finite Holographic Substrate" (Akhtman & Voether, 2026; Preprints
doi 10.20944/preprints202606.0768.v1), the paper 20-rh of the FRC corpus (finite-ring-space/src/20-rh). One script since
24 September 2026; rewritten with the paper on 17 October 2026; revised with the paper on 21 November 2026: the count
readout replaces the readout on the framed plane (the critical circle, rows G13 and G14, on 22 November). The checks of the rows that left are gone with them (A2 to A5, A15 to
A18, A20, and the chart blocks B and C), and one check per row of the count readout and of the classical statements enters
(blocks G and X).
========================================================================================================================

Four blocks, 99 checks — 89 EXACT (integer-pinned: a pass is a proof on the tested instances) and 10 [approx] (floating-point
readings to a stated tolerance: the chart's characters, and in block D the spectrum of the window's primes, the count of a window from its dual and the bound on its difference from the count) — Python with numpy, which block A's chart characters alone use.
Each check cites the predicate(s) of the paper's ledger it witnesses (LEDGER; predicates cited as 20:XN), and the deciding
check's `# 20:XN (<key>)` marker is what the ledger's source column links (PREDICATES; finitering.space/py/rh.html#<key>).
The records are those of the framework's ledger file frc/ledgers/p20_rh.py, check for check. The paper's Figures 2, 3 and 4
are drawn by make_figures.py beside this script, from its functions.

Block A  the shell, in exact arithmetic (EXACT, five [approx]; 20:A2, A3, A4, B1, B2, B4, B10, E12–E15, F7): the zero-slot, the
         Subject constants, the shell theorem's clauses on random vectors, the Parseval identity, frame coincidence within the
         observational horizon, the closure, completeness, the drive theorem
Block D  the prime vector in the chart ([approx], D19 EXACT; 20:D14, D15, D16, D17, D18, D19): the spectrum of the window's primes against the classical
         heights, the deep window, the count of a window from its dual against π(x) and Riemann's formula, and the bound on its
         difference from the count of the vector, a mode near every height, and the value of a mode at one label
Block G  the count readout (EXACT; 20:G2, G3, G5–G7, G9, G10, G12–G14, F7): the count operator, the forced half, the generator, the
         zeros, their centre and order, the cardinal modes, the Carrier's chart, the critical circle, on the pairs (13, 233), (173, 30089),
         (1549, 2408561)
Block X  the classical statements on the shell (EXACT; 20:X1–X3): the ½ of the critical line, the pole and the functional
         equation, the ½ of the dilation generator

    python3 rh.py                every block in order, results.json written; exit 1 if a check fails (≈ 25 s on one core)
    python3 rh.py A G            the blocks named (A, D, G, X); no results.json
    from frc_20_rh import predicate; predicate("20:G6")    one predicate: the blocks of the checks citing it run once per session
"""
import os, json, sys, math, cmath, time, random, types
from functools import lru_cache
import numpy as np

SCRIPT = os.path.splitext(os.path.basename(__file__))[0]        # "rh": the one script, the name results.json and the site pages carry

# ----------------------------------------------------------------------------- registry
RESULTS = []

# The paper's predicate ledger (20-rh Appendix A, predicates cited as 20:XN): the predicate(s) each check witnesses. The
# ledger's source column cites these check ids in return. The check ids A8 and A9 are retired with their rows (the Lanczos
# matrix, the Ramanujan sum; 17 October 2026), and A2 to A5, A15 to A18, A20, B3 to B8 and C1 with theirs (21 November 2026).
# None is reused.
LEDGER = {
    "A1": "20:B4", "A6": "20:B10", "A6b": "20:B10",
    "A7": "20:E12, 20:E14", "A7b": "20:E13", "A10": "20:B1", "A11": "20:B2", "A12": "20:A2, 20:A4, 20:F7", "A13": "20:A3",
    "A14": "20:E13", "A19": "20:E15",
    "D14": "20:D14", "D15": "20:D15", "D16": "20:D16", "D17": "20:D17", "D18": "20:D18", "D19": "20:D19",
    "G2": "20:G2", "G3": "20:G3", "G5": "20:G5", "G6": "20:G6, 20:F7", "G7": "20:G7", "G9": "20:G9", "G10": "20:G10", "G12": "20:G12", "G13": "20:G13", "G14": "20:G14",
    "X1": "20:X1", "X2": "20:X2", "X3": "20:X3",
}

BLOCK = {"A": "the shell, in exact arithmetic: the zero-slot, the Subject constants, the shell theorem, the Parseval identity, frame coincidence, the closure, completeness, the drive theorem",
         "D": "the prime vector in the chart: the spectrum of the window's primes against the classical heights, the deep window, the count of a window from its dual with its bound, a mode near every height, and the value of a mode at one label",
         "G": "the count readout: the count operator, the forced half, the generator, the zeros, their centre and order, the cardinal modes, the Carrier's chart, the critical circle",
         "X": "the classical statements on the shell: the ½ of the critical line, the pole and the functional equation, the ½ of the dilation generator"}

# the deciding check of each python-witnessed predicate: the check the ledger's source column links (the other checks that
# cite it are corroboration, listed by predicate() from the records)
PREDICATES = {
    "20:B1": "A10", "20:B2": "A11", "20:B4": "A1", "20:B10": "A6",
    "20:A2": "A12", "20:A3": "A13", "20:A4": "A12", "20:F7": "A12",
    "20:E12": "A7", "20:E13": "A14", "20:E14": "A7", "20:E15": "A19",
    "20:D14": "D14", "20:D15": "D15", "20:D16": "D16", "20:D17": "D17", "20:D18": "D18", "20:D19": "D19",
    "20:G2": "G2", "20:G3": "G3", "20:G5": "G5", "20:G6": "G6", "20:G7": "G7", "20:G9": "G9", "20:G10": "G10", "20:G12": "G12", "20:G13": "G13", "20:G14": "G14",
    "20:X1": "X1", "20:X2": "X2", "20:X3": "X3",
}
_RAN = set()                                            # blocks already run in this session (predicate() runs each once)

def check(pid, label, ok, detail="", kind="EXACT"):
    """Record one predicate check. pid = package check id (A1, B5, ...); LEDGER[pid] = the paper's ledger predicate(s)."""
    ok = bool(ok)
    rows = LEDGER[pid]
    RESULTS.append({"id": pid, "rows": rows, "block": pid[0], "script": SCRIPT, "label": label, "ok": ok, "detail": detail, "kind": kind})
    print(f"  [{'PASS' if ok else 'FAIL'}] {pid:4s} {kind:7s} [{rows}] {label}" + (f"  --  {detail}" if detail else ""))
    return ok

def summary(write=True):
    n_ok = sum(r["ok"] for r in RESULTS)
    print(f"\nSUMMARY: {n_ok}/{len(RESULTS)} checks passed" + ("" if n_ok == len(RESULTS) else "  <-- FAILURES"))
    if write:
        with open("results.json", "w") as f:
            json.dump(RESULTS, f, indent=1)
    return n_ok == len(RESULTS)

def markers():
    """predicate label -> (script file, line) of its marker `# <paper>:<label> (<key>)`: the line of the check that decides it."""
    import re
    out = {}
    for i, line in enumerate(open(os.path.abspath(__file__), encoding="utf-8"), 1):
        m = re.match(r"\s*# ((?:\d+:[A-Z]+\d+[a-z]?(?: \(p\d{5}\))?)(?:, \d+:[A-Z]+\d+[a-z]?(?: \(p\d{5}\))?)*)\s*$", line)
        if m:
            for lab in re.findall(r"\d+:[A-Z]+\d+[a-z]?", m.group(1)): out.setdefault(lab, (SCRIPT + ".py", i))
    return out

def _run_block(letter):
    if letter not in _RAN:
        globals()[f"block_{letter}"](); _RAN.add(letter)

def predicate(label, lines=14):
    """Verify one ledger predicate: run the blocks of the checks that cite it (each once per session), print the deciding check's
    source (from its marker) and every record that cites the predicate, and return True iff all pass."""
    pid = PREDICATES.get(label)
    if pid is None:
        print(f"{label}: no python witness (see the predicate's Lean witness or its source)"); return None
    citing = {i[0] for i, rows in LEDGER.items() if label in [t.strip() for t in rows.split(",")]}
    for b in sorted({pid[0]} | citing): _run_block(b)          # the deciding block and every block whose checks cite the predicate
    mk = markers().get(label)
    if mk:
        src = open(os.path.abspath(__file__), encoding="utf-8").read().split("\n")
        print(f"— {mk[0]}:{mk[1]} (the check that decides {label}: {pid})")
        for j in range(mk[1] - 1, min(mk[1] - 1 + lines, len(src))): print(f"{j + 1:5d}  {src[j]}")
    recs = [r for r in RESULTS if label in [t.strip() for t in r["rows"].split(",")]]
    ok = all(r["ok"] for r in recs)
    for r in recs:
        role = "(deciding)" if r["id"] == pid else "(corroborating)"
        print(f"  [{'PASS' if r['ok'] else 'FAIL'}] {r['id']:4s} {role:16s} {r['detail'][:150]}")
    print(f"{label}: {'VERIFIED' if ok and recs else 'FAILED'} — {len(recs)} record(s)")
    return ok

def verify_all():
    """Run every block (those already run in this session are not re-run) and print the summary; True iff every check passed."""
    for b in sorted(BLOCK): _run_block(b)
    return summary(write=False)

# ----------------------------------------------------------------------------- the arithmetic of the shell (standard library)
SHELLS = [13, 17, 29, 37, 41]          # in full
BIG = 173                               # the laboratory Subject of (173, 30089): A1, A6, A7, A14, A19
PAIRS = ((13, 233), (173, 30089), (1549, 2408561))      # the laboratory pairs (p, Ω), Ω the Carrier of the Subject p (Def. shells)

def is_prime(n):
    if n < 2: return False
    d = 2
    while d * d <= n:
        if n % d == 0: return False
        d += 1
    return True

def next_prime(n):
    n += 1
    while not is_prime(n): n += 1
    return n

def prime_factors(n):
    f, d = set(), 2
    while d * d <= n:
        while n % d == 0:
            f.add(d); n //= d
        d += 1
    if n > 1: f.add(n)
    return f

def generator(p):
    """The least primitive root of F_p: the Subject's generator g, as the paper takes it."""
    for g in range(2, p):
        if all(pow(g, (p - 1) // q, p) != 1 for q in prime_factors(p - 1)):
            return g

def dlog_table(p, g):
    """The discrete logarithm λ_p to the generator g on F_p^×, as a list indexed by the residue (λ[g^m] = m)."""
    lam, x = [0] * p, 1
    for m in range(p - 1):
        lam[x] = m; x = x * g % p
    return lam

# F_{p^2} = F_p(η), η² = ν: elements (a, b) = a + bη; the conjugation φ, the reflection ρ, the trace and the norm
def dual(v, p):
    """The dual of a vector v on F_p^× (v[x] for x = 1..p−1): v̂(k) = Σ_x v(x) x^k for k = 0..p−2, in F_p."""
    return [sum(v[x] * pow(x, k, p) for x in range(1, p)) % p for k in range(p - 1)]

def random_vectors(p, count, seed):
    rng = random.Random(seed)
    return [[0] + [rng.randrange(p) for _ in range(p - 1)] for _ in range(count)]

# ----------------------------------------------------------------------------- the count readout (the functions of the framework's count theme, frc/count.py)
# The modes of a shell p are the powers x ↦ x^k on the nonzero residues, k = 0, …, p − 2. The count of a mode is k. For a
# count k ≥ 1 the zero is k + 1 and the conjugate count is p − 1 − k. One function per theorem of lean/FrcCore/Theme/Count.lean
# and Theme/Circle.lean, under its name; each returns True when the statement holds on the shell it is given. Blocks G and X call them as CT.<name>.
def generators(p):
    """The generators of the cycle of the shell p, ascending."""
    qs = prime_factors(p - 1)
    return [g for g in range(2, p) if all(pow(g, (p - 1) // q, p) != 1 for q in qs)]


def gram_table(p):
    """P[n] = Σ_{x≠0} x^n for n = 0 … 2p − 4, by running powers; the Gram entry of two modes is P[k + m]."""
    xs, cur, P = list(range(1, p)), [1] * (p - 1), []
    for _ in range(2 * p - 3):
        P.append(sum(cur) % p)
        cur = [c * x % p for c, x in zip(cur, xs)]
    return P


def gram(p, k, m):
    """The Gram entry ⟨x^k, x^m⟩ = Σ_{x≠0} x^k x^m, by the direct sum."""
    return sum(pow(x, k, p) * pow(x, m, p) for x in range(1, p)) % p


def frequency(p, kap, i, k):
    """The frequency of the count k: γ_k = −i(k + 2⁻¹), with 2⁻¹ = 2κ + 1."""
    return (-i * (k + 2 * kap + 1)) % p


def quarter_turn(p, kap, g):
    """The Subject's quarter-turn i = g^(−κ) = −g^κ."""
    return (-pow(g, kap, p)) % p


def mode_coefficients(p, v):
    """c_k = −Σ_x v(x) x^{−k} for k = 0 … p − 2; v is indexed by x − 1."""
    inv, cur, cs = [pow(x, p - 2, p) for x in range(1, p)], [1] * (p - 1), []
    for _ in range(p - 1):
        cs.append((-sum(a * b for a, b in zip(v, cur))) % p)
        cur = [c * ix % p for c, ix in zip(cur, inv)]
    return cs


def mode_values(p, cs):
    """The vector with the mode coefficients cs, at x = 1 … p − 1 (Horner)."""
    out = []
    for x in range(1, p):
        acc = 0
        for c in reversed(cs): acc = (acc * x + c) % p
        out.append(acc)
    return out


def delta(p, y):
    """The indicator of the residue y, indexed by x − 1."""
    return [1 if x == y else 0 for x in range(1, p)]


def fixed_sequence(p, seed):
    """A fixed integer sequence reduced mod p (s ↦ 1103515245 s + 12345 mod 2³¹): a test vector with no random source."""
    out, s = [], seed
    for _ in range(p - 1):
        s = (1103515245 * s + 12345) % (1 << 31)
        out.append(s % p)
    return out


def run_shifts(p, start):
    """The values 2c that the nonconstant conjugate pairs of the run of counts [start, start + p − 1) ask for."""
    n = p - 1
    by_class = {a % n: a for a in range(start, start + n)}
    return {(-(a + by_class[(n - cls) % n])) % p for cls, a in by_class.items() if cls}


# ---- one function per declaration of lean/FrcCore/Theme/Count.lean -----------------------------------------------------

def mode_stride(p, g):
    """At x = g^m the mode of count k has the value g^(km): (g^m)^k = (g^k)^m = g^(km), every m and k below p − 1."""
    n = p - 1; tab = [pow(g, m, p) for m in range(n)]
    return all(pow(tab[m], k, p) == pow(tab[k], m, p) == pow(g, k * m, p) for m in range(n) for k in range(n))


def count_conjugate(p):
    """The conjugate of a count 1 ≤ k ≤ p − 2 is p − 1 − k, again in 1 … p − 2, and the two counts add to −1."""
    return all(1 <= p - 1 - k <= p - 2 and (k + (p - 1 - k) + 1) % p == 0 for k in range(1, p - 1))


def count_adjoint(p, P, direct=False):
    """(k + m + 1)·⟨x^k, x^m⟩ ≡ 0 for 1 ≤ k ≤ p − 2, 0 ≤ m ≤ p − 2; the Gram entries from the table P, or by direct sums."""
    return all((k + m + 1) * (gram(p, k, m) if direct else P[k + m]) % p == 0 for k in range(1, p - 1) for m in range(p - 1))


def gram_rows(p, P, ks):
    """The table P against the direct Gram sums on the rows ks."""
    return all(gram(p, k, m) == P[k + m] for k in ks for m in range(p - 1))


def count_adjoint_vector(p, pairs):
    """⟨Nv, w⟩ + ⟨v, Nw⟩ + ⟨v, w⟩ ≡ −c_0·d_0 on pairs of vectors given by their values; N acts on the mode coefficients.
    pairs: [((name, v), (name, w))]; each vector is first read back from its mode coefficients."""
    cache = {}

    def prep(key, v):
        if key not in cache:
            c = mode_coefficients(p, v)
            if mode_values(p, c) != v: return None
            cache[key] = (v, c, mode_values(p, [k * ck % p for k, ck in enumerate(c)]))
        return cache[key]

    for (ka, va), (kb, vb) in pairs:
        A, B = prep(ka, va), prep(kb, vb)
        if A is None or B is None: return False
        (v, c, Nv), (w, d, Nw) = A, B
        lhs = (sum(a * b for a, b in zip(Nv, w)) + sum(a * b for a, b in zip(v, Nw)) + sum(a * b for a, b in zip(v, w))) % p
        if lhs != (-c[0] * d[0]) % p: return False
    return True


def half_forced(p, ks=None):
    """For every residue c: ((k + c) + (p − 1 − k + c) ≡ 0 for every count k) ⇔ 2c ≡ 1. ks: the counts tried (default all)."""
    ks = range(1, p - 1) if ks is None else ks
    return all(all(((k + c) + (p - 1 - k + c)) % p == 0 for k in ks) == (2 * c % p == 1) for c in range(p))


def count_run(p, ms, ks=None):
    """On the run of counts that starts at m(p − 1): its counts at k and at p − 1 − k add to −(2m + 1), for 0 ≤ k < p."""
    ks = range(0, p) if ks is None else ks
    return all(((m * (p - 1) + k) + (m * (p - 1) + (p - 1 - k)) + (2 * m + 1)) % p == 0 for m in ms for k in ks)


def count_run_only(p, ms):
    """A run of p − 1 consecutive counts has one skew shift exactly when it starts at m(p − 1) or at m(p − 1) + 1."""
    for m in ms:
        for r in range(0, p - 1):
            need = run_shifts(p, m * (p - 1) + r)
            if (need != {(2 * m + 1) % p}) if r in (0, 1) else (len(need) < 2): return False
    return True


def zero_count(p, kap, g):
    """i² = −1 and 2⁻¹ + iγ_k = k + 1 for 0 ≤ k < 2p; for a count k ≥ 1 this residue is the zero of the mode."""
    i = quarter_turn(p, kap, g); half = 2 * kap + 1
    return i * i % p == p - 1 and all((half + i * frequency(p, kap, i, k)) % p == (k + 1) % p for k in range(0, 2 * p))


def zeros_fill(p):
    """The zeros k + 1 of the counts 1 ≤ k ≤ p − 2 are the residues other than 0 and 1."""
    return {(k + 1) % p for k in range(1, p - 1)} == set(range(p)) - {0, 1}


def zeros_fill_ends(p):
    """The same statement on a large shell, by the number of counts and the two ends of the range."""
    ks = range(1, p - 1)
    return len(ks) == p - 2 and (ks[0] + 1) % p == 2 and (ks[-1] + 1) % p == p - 1


def zero_conjugate(p, kap, g):
    """For every k ≤ p − 1, (p − 1 − k) + 1 ≡ 1 − (k + 1) and γ_(p−1−k) = −γ_k as residues; for 1 ≤ k ≤ p − 2 these are the zero and the frequency of the conjugate mode."""
    i = quarter_turn(p, kap, g)
    return all((p - 1 - k + 1) % p == (1 - (k + 1)) % p and frequency(p, kap, i, p - 1 - k) == (-frequency(p, kap, i, k)) % p
               for k in range(0, p))


def generator_skew(p, kap, g, P):
    """(γ_k + γ_m)·⟨x^k, x^m⟩ ≡ 0 unless both modes are constant."""
    i = quarter_turn(p, kap, g); fr = [frequency(p, kap, i, k) for k in range(p - 1)]
    return all((fr[k] + fr[m]) * P[k + m] % p == 0 for k in range(p - 1) for m in range(p - 1) if k > 0 or m > 0)


def centre_mode(p, kap, g):
    """The mode of count π = 2κ is its own conjugate, its zero is 2⁻¹, its frequency is 0, and it is the one such mode."""
    i = quarter_turn(p, kap, g)
    return (2 * kap + 2 * kap == p - 1 and 2 * (2 * kap + 1) % p == 1 and frequency(p, kap, i, 2 * kap) == 0
            and [k for k in range(p - 1) if frequency(p, kap, i, k) == 0] == [2 * kap])


def pair_invariant(p, kap, g):
    """ρ(1 − ρ) = 2⁻² + γ² = −k(k + 1), the same for a count and its conjugate."""
    i = quarter_turn(p, kap, g); half = 2 * kap + 1
    for k in range(0, p):
        inv = (-k * (k + 1)) % p; kd = p - 1 - k
        if (k + 1) * (1 - (k + 1)) % p != inv or (half * half + frequency(p, kap, i, k) ** 2) % p != inv: return False
        if kd * (kd + 1) % p != k * (k + 1) % p: return False
    return True


def energy_order(p, kap):
    """The counts 2κ − j and 2κ + j are conjugate, their zeros are 2⁻¹ − j and 2⁻¹ + j, and the lesser count of the pair,
    2κ − j, falls from 2κ to 1 as j runs from 0 to 2κ − 1."""
    half = 2 * kap + 1
    for j in range(0, 2 * kap + 1):
        lo, hi = 2 * kap - j, 2 * kap + j
        if lo + hi != p - 1 or (hi + 1) % p != (half + j) % p or (lo + 1 + j) % p != half % p or min(lo, hi) != lo: return False
    return [min(2 * kap - j, 2 * kap + j) for j in range(0, 2 * kap)] == list(range(2 * kap, 0, -1))


def cardinal_modes(p, kap, g):
    """A mode has all its values in {1, −1, i, −i} exactly when its count is 0, κ, 2κ or 3κ."""
    i = quarter_turn(p, kap, g); four = {1, p - 1, i, (-i) % p}; card = {0, kap, 2 * kap, 3 * kap}
    return all(all(pow(x, k, p) in four for x in range(1, p)) == (k in card) for k in range(p - 1))


def cardinal_zeros(p, kap):
    """The zeros of the counts 0, κ, 2κ, 3κ are 1, 3·4⁻¹, 2⁻¹, 4⁻¹: 4(κ + 1) ≡ 3, 2(2κ + 1) ≡ 1, 4(3κ + 1) ≡ 1."""
    return p == 4 * kap + 1 and 4 * (kap + 1) % p == 3 % p and 2 * (2 * kap + 1) % p == 1 and 4 * (3 * kap + 1) % p == 1


def carrier_centre(p, S, ks=None):
    """On a shell of cardinality 4S + 1, with no frame: twice 2S is −1, and k + (p − 1 − k) is twice 2S for every k < p;
    for a count k ≥ 1 the second term is its conjugate."""
    c2 = 2 * (2 * S) % p; ks = range(0, p) if ks is None else ks
    return p == 4 * S + 1 and (c2 + 1) % p == 0 and all((k + (p - 1 - k)) % p == c2 for k in ks)


def origin_unit_symmetry(p, pairs=None, xs=None):
    """x ↦ a·x + b keeps the pair {0, 1} exactly for (a, b) = (1, 0) and (−1, 1); x = 1 − x exactly when 2x = 1.
    pairs: the (a, b) tried (default every pair); xs: the residues tried for the fixed point (default every residue)."""
    it = ((a, b) for a in range(p) for b in range(p)) if pairs is None else pairs
    if any(({b % p, (a + b) % p} == {0, 1}) != ((a, b) in ((1, 0), (p - 1, 1))) for a, b in it): return False
    half = (p + 1) // 2; xs = range(p) if xs is None else xs
    return all((x == (1 - x) % p) == (2 * x % p == 1) for x in xs) and 2 * half % p == 1


def zero_shared(p, om):
    """Every label k + 1 below p is the same integer on the Subject p and on the chart of a larger shell om: the zero of a
    nonconstant mode, and the label 1 of the constant mode."""
    return p <= om and all((k + 1) % p == k + 1 == (k + 1) % om for k in range(0, p - 1))


def zeros_collide(om, o, reading=None):
    """A reading of the residues of the shell om into o < om − 2 states identifies two of the zeros 2, …, om − 1.
    The reading is y ↦ y mod o when none is given; any reading into the states 0 … o − 1 may be passed."""
    read = reading or (lambda y: y % o); seen = set()
    if not o < om - 2: return False
    for z in range(2, om):
        r = read(z)
        if not 0 <= r < o: return False
        if r in seen: return True
        seen.add(r)
    return False


def zeros_not_held(p, om, reading=None):
    """For 2 ≤ p and p² < om the p states of a Subject are fewer than the om − 2 zeros of the chart of the shell om, and
    the reading given, of its residues into p states, identifies two zeros."""
    return 2 <= p and p * p < om and p + 2 <= p * p and p < om - 2 and zeros_collide(om, p, reading)


def half_unique(p, kap):
    """The inverse of 2 is unique: 2x ≡ 1 exactly when x = 2κ + 1."""
    return [x for x in range(p) if 2 * x % p == 1] == [2 * kap + 1]


# ---- one function per declaration of lean/FrcCore/Theme/Circle.lean: the critical circle (20:G13, G14) ------------------
# The paper writes z for the residue t = ρ/(1 − ρ) of these functions and d for the sum c.

def circle_points(p, g):
    """The points of the critical circle of the frame (p, g): the pairs (a, m), 0 ≤ m < p − 1, with a·(g^m + g^{−m}) ≡ 1.
    The pair (−a, m + 2κ) is the same point of the sphere."""
    gi = pow(g, p - 2, p); out = []
    for m in range(p - 1):
        s = (pow(g, m, p) + pow(gi, m, p)) % p
        if s: out.append((pow(s, p - 2, p), m))
    return out


def circle_pair(p, g):
    """On the circle a point carries a zero ρ ≠ 0, 1, its mirror carries 1 − ρ, and a² = ρ(1 − ρ)."""
    gi = pow(g, p - 2, p)
    for a, m in circle_points(p, g):
        r, rm = a * pow(g, m, p) % p, a * pow(gi, m, p) % p
        if r in (0, 1) or rm != (1 - r) % p or a * a % p != r * (1 - r) % p: return False
    return True


def circle_frequency(p, kap, g):
    """A zero and its reflection differ by 2iγ_k: (k + 1) − (1 − (k + 1)) ≡ 2iγ_k, for 0 ≤ k < 2p."""
    i = quarter_turn(p, kap, g)
    return all(((k + 1) - (1 - (k + 1))) % p == 2 * i * frequency(p, kap, i, k) % p for k in range(0, 2 * p))


def circle_meridians(p, kap, g):
    """No point of the circle on the momentum meridian (u² = −1) or at the origin; on the prime meridian the one point is
    the centre 2⁻¹, of frequency 0."""
    i = quarter_turn(p, kap, g)
    for u in (i, (-i) % p):
        v = pow(u, p - 2, p)
        if u * u % p != p - 1 or any((a * u + a * v) % p == 1 for a in range(p)): return False
    if any((0 * u + 0 * pow(u, p - 2, p)) % p == 1 for u in range(1, p)): return False
    return [x for x in range(p) if (x + x) % p == 1] == [2 * kap + 1] and frequency(p, kap, i, 2 * kap) == 0


def circle_point(p, g):
    """A zero ρ has a point on the circle exactly when ρ(1 − ρ) is a square, and then the two pairs (a, m) and
    (−a, m + 2κ), one point of the sphere."""
    half = (p - 1) // 2; squares = {x * x % p for x in range(1, p)}; at = {}
    for a, m in circle_points(p, g):
        at.setdefault(a * pow(g, m, p) % p, []).append((a, m))
    for r in range(2, p):
        pts = at.get(r, [])
        if (len(pts) > 0) != (r * (1 - r) % p in squares): return False
        if pts and not (len(pts) == 2 and pts[1] == ((-pts[0][0]) % p, pts[0][1] + half)): return False
    return True


def circle_count(p, kap, g):
    """The circle has a point at the phase m exactly when g^{2m} ≠ −1; among the phases below 2κ that excludes κ alone;
    the phase m + 2κ gives the same point with the position −a; the 2κ − 1 points carry 2κ − 1 distinct zeros."""
    pts = dict((m, a) for a, m in circle_points(p, g))
    if any((m in pts) != (pow(g, 2 * m, p) != p - 1) for m in range(p - 1)): return False
    if [m for m in range(2 * kap) if pow(g, 2 * m, p) == p - 1] != [kap]: return False
    if any((-pts[m]) * pow(g, m + 2 * kap, p) % p != pts[m] * pow(g, m, p) % p or pts[m + 2 * kap] != (-pts[m]) % p
           for m in range(2 * kap) if m != kap): return False
    zeros = [pts[m] * pow(g, m, p) % p for m in range(2 * kap) if m != kap]
    return len(zeros) == 2 * kap - 1 == len(set(zeros))


def circle_places(p, kap, g):
    """The places j of the latitude cycle, 0 ≤ j < p − 1, and the zero ρ_j = g^j/(1 + g^j) at each; the place j = 2κ,
    where g^j = −1, carries none."""
    return {j: pow(g, j, p) * pow(1 + pow(g, j, p), p - 2, p) % p for j in range(p - 1) if j != 2 * kap}


def circle_place(p):
    """Every zero ρ is t/(1 + t) for exactly one t, namely ρ/(1 − ρ), with t ≠ 0, −1; such a t gives a zero; the inverse
    of t gives 1 − ρ."""
    inv = lambda x: pow(x, p - 2, p)
    for r in range(2, p):
        ts = [t for t in range(p) if r * (1 + t) % p == t]
        if ts != [r * inv(1 - r) % p] or ts[0] in (0, p - 1): return False
        t = ts[0]
        if (1 - r) * (1 + inv(t)) % p != inv(t): return False
    return all((t * inv(1 + t) % p) not in (0, 1) for t in range(1, p - 1))


def circle_place_cycle(p, kap, g):
    """The zeros stand on the latitude cycle: t = g^j for one j < p − 1, never j = 2κ, where 1 + g^j ≡ 0; the p − 2 other
    places carry the p − 2 zeros, once each; the centre 2⁻¹ is the place 0, and the place −j carries 1 − ρ_j."""
    n = p - 1; rho = circle_places(p, kap, g)
    return ((1 + pow(g, 2 * kap, p)) % p == 0 and sorted(rho.values()) == list(range(2, p)) and rho[0] == 2 * kap + 1
            and all(rho[(-j) % n] == (1 - rho[j]) % p for j in rho))


def circle_place_even(p, kap, g):
    """The even places: g^j is a square exactly when j is even, exactly then ρ_j(1 − ρ_j) is a square, and the place 2m
    is the point of the sphere on the circle at the phase m."""
    n = p - 1; rho = circle_places(p, kap, g); squares = {x * x % p for x in range(1, p)}
    if any((pow(g, j, p) in squares) != (j % 2 == 0) for j in range(n)): return False
    if any((j % 2 == 0) != (r * (1 - r) % p in squares) for j, r in rho.items()): return False
    return all(a * pow(g, m, p) % p == rho[2 * m % n] for a, m in circle_points(p, g))


def circle_quarter_turn(p, kap, g):
    """2ρ_j − 1 = (t − 1)/(t + 1) at t = g^j; the map x ↦ (x − 1)/(x + 1) has the square x ↦ −1/x, four steps return x
    on the residues other than 0 and ±1, and its fixed points are the two roots ±i of x² = −1."""
    inv = lambda x: pow(x, p - 2, p); i = quarter_turn(p, kap, g)
    Q = lambda x: (x - 1) * inv(x + 1) % p
    if any((2 * r - 1) % p != Q(pow(g, j, p)) for j, r in circle_places(p, kap, g).items()): return False
    xs = [x for x in range(1, p) if (x + 1) % p and (Q(x) + 1) % p]
    if any(Q(Q(x)) * x % p != p - 1 for x in xs): return False
    return sorted(x for x in range(p) if x * (x + 1) % p == (x - 1) % p) == sorted((i, (-i) % p))


def circle_counts(p, kap, g):
    """The counts: for a point (a, m) of the circle with the zero ρ = k + 1, the point (−a, −m) carries the count k
    and its mirror (−a, m) carries −ρ, the count of the conjugate mode; the two add to −1; on the prime meridian the
    one point with x + x ≡ −1 is π = 2κ."""
    gi = pow(g, p - 2, p)
    for a, m in circle_points(p, g):
        r = a * pow(g, m, p) % p; k = (r - 1) % p
        far, mirror = (-a) * pow(gi, m, p) % p, (-a) * pow(g, m, p) % p
        if far != k or mirror != (-r) % p or mirror != (p - 1 - k) % p or (far + mirror) % p != p - 1: return False
    return [x for x in range(p) if (x + x) % p == p - 1] == [2 * kap]


def circle_phase(p, g):
    """One point of the circle at each phase: the position a with a·(g^m + g^{−m}) ≡ 1 is the one inverse of the sum,
    found by search over every residue, and there is none where the sum vanishes; residues ρ and 1 − ρ of a point and
    its mirror put the point on the circle."""
    gi = pow(g, p - 2, p)
    for m in range(p - 1):
        u, v = pow(g, m, p), pow(gi, m, p); s = (u + v) % p
        if [a for a in range(p) if a * s % p == 1] != ([pow(s, p - 2, p)] if s else []): return False
        if any((a * u + a * v) % p != 1 for a in range(p) if a * v % p == (1 - a * u) % p): return False
    return True


def circle_parallels(p, kap, g):
    """The sets of constant sum: for c ≠ 0 the pairs (a, m) with a·(g^m + g^{−m}) ≡ c are the pairs of the circle with
    the position multiplied by c; the sum vanishes exactly at a = 0 and where g^{2m} ≡ −1; negating the position sends
    the sum c to the sum −c; the sums 1 and −1 share no pair; on the prime meridian the sum c has the one residue
    c·2⁻¹. Every pair (a, m) is sorted by its sum, so each set is found by search."""
    gi = pow(g, p - 2, p); half = 2 * kap + 1; n = p - 1
    s = [(pow(g, m, p) + pow(gi, m, p)) % p for m in range(n)]
    level = [set() for _ in range(p)]
    for m in range(n):
        for a in range(p): level[a * s[m] % p].add((a, m))
    C = level[1]
    if any(level[c] != {(c * a % p, m) for a, m in C} for c in range(1, p)): return False
    if level[0] != {(a, m) for m in range(n) for a in range(p) if a == 0 or pow(g, 2 * m, p) == p - 1}: return False
    if any(((-a) % p, m) not in level[(p - c) % p] for c in (1, 2, p - 1) for a, m in level[c]): return False
    return not (C & level[p - 1]) and all([x for x in range(p) if (x + x) % p == c] == [c * half % p] for c in range(p))


def circle_place_phase(p, g):
    """The phase of an even place: a point (a, m) of the circle carries g^{2m}/(1 + g^{2m}), the zero at the place 2m."""
    return all(a * pow(g, m, p) * (1 + pow(g, 2 * m, p)) % p == pow(g, 2 * m, p) for a, m in circle_points(p, g))


def circle_quarter_closes(p):
    """With y = −1/x and w = −1/y, w = x: four steps of x ↦ (x − 1)/(x + 1) return x; and −1/x = x exactly when x² ≡ −1."""
    inv = lambda x: pow(x, p - 2, p); neg_inv = lambda x: (p - 1) * inv(x) % p
    return all(neg_inv(neg_inv(x)) == x and ((neg_inv(x) == x) == (x * x % p == p - 1)) for x in range(1, p))


# The value of a mode at one label (20:D19; Theme/Steps.lean, 23 November 2026). A nonzero residue y is x^k·g^r with
# r < W when y is fewer than W steps of the drive after a power of x on the latitude cycle.
def scale_table(p, g):
    """The scale of every nonzero residue on the latitude cycle: table[x] = m with g^m = x, 0 ≤ m < p − 1."""
    table, x = [0] * p, 1
    for m in range(p - 1):
        table[x] = m; x = x * g % p
    return table


def step_width(p, g, x, table=None):
    """The least W for which every nonzero residue is x^k·g^r with r < W: the powers of x are marked at their places
    of the latitude cycle, and one pass along the cycle counts the steps of the drive from a marked place."""
    n = p - 1
    table = table or scale_table(p, g)
    marked, y = [False] * n, 1
    while not marked[table[y]]:
        marked[table[y]] = True; y = y * x % p
    worst = run = 0
    for place in range(1, n + 1):                               # the place 0 is marked: x^0 = 1
        run = 0 if marked[place % n] else run + 1
        if run > worst: worst = run
    return worst + 1


def power_steps(p, g, x, M, table=None):
    """A residue x with the distinct powers x^0, …, x^M, M ≥ 1: every nonzero residue is x^k·g^r with r < W, for the
    least W with M·W ≥ p − 1 (and so for every larger W)."""
    powers, y = set(), 1
    for _ in range(M + 1):
        powers.add(y); y = y * x % p
    return M >= 1 and len(powers) == M + 1 and step_width(p, g, x, table) <= -(-(p - 1) // M)


def label_pair(p, l):
    """The pair (N, W) of 20:D19 for a label l ≥ 2 (the paper's M and V): N the largest exponent with l^N < p, W the
    least number of steps with N·W ≥ p − 1. Every N' ≤ N and every W' with N'·W' ≥ p − 1 has W' ≥ W, so the statement at (N, W)
    gives it at (N', W')."""
    N = 0
    while l ** (N + 1) < p: N += 1
    return N, -(-(p - 1) // N)


def label_steps(p, g, l, table=None):
    """20:D19 at the label l, 2 ≤ l < p: every nonzero residue is l^k·g^r with r < W, at the largest N and the least W."""
    N, W = label_pair(p, l)
    return N >= 1 and power_steps(p, g, l, N, table) and step_width(p, g, l, table) <= W


CT = types.SimpleNamespace(**{f.__name__: f for f in (generators, gram_table, gram, frequency, quarter_turn, mode_coefficients, mode_values, delta, fixed_sequence, run_shifts, mode_stride, count_conjugate, count_adjoint, gram_rows, count_adjoint_vector, half_forced, count_run, count_run_only, zero_count, zeros_fill, zeros_fill_ends, zero_conjugate, generator_skew, centre_mode, pair_invariant, energy_order, cardinal_modes, cardinal_zeros, carrier_centre, origin_unit_symmetry, zero_shared, zeros_collide, zeros_not_held, half_unique,
                                                            circle_points, circle_pair, circle_frequency, circle_meridians, circle_point, circle_count, circle_places, circle_place,
                                                            circle_place_cycle, circle_place_even, circle_quarter_turn, circle_counts, circle_phase, circle_parallels, circle_place_phase, circle_quarter_closes,
                                                            scale_table, step_width, power_steps, label_pair, label_steps)})

# ---- the spectrum of a window [chart] (Obs. exhibit; rows D13, D14, D15), 21 November 2026 -----------------------------
# The labels 1..H of a window of depth H, the paper's q, carry a weight (1 on the primes, or log l on the prime powers l^a); its mean over the labels is removed;
# the label n is read as n^(sigma + i t). Pure python; the constant part beyond `head` labels is summed by the
# Euler-Maclaurin formula, so the depth 10^6 costs about 4 ms a height.
def window_weights(H, kind="primes"):
    """The labels n <= H with a nonzero weight, their weights, and the mean of the weight over the labels 1..H.
    kind "primes": 1 on the primes; kind "mangoldt": log l on the prime powers l^a (the von Mangoldt weight)."""
    sieve = bytearray([1]) * (H + 1); sieve[0:2] = b"\0\0"
    for i in range(2, math.isqrt(H) + 1):
        if sieve[i]: sieve[i * i::i] = bytearray(len(sieve[i * i::i]))
    labels, weights = [], []
    for l in range(2, H + 1):
        if sieve[l]:
            if kind == "primes":
                labels.append(l); weights.append(1.0)
            else:
                q, w = l, math.log(l)
                while q <= H:
                    labels.append(q); weights.append(w); q *= l
    return labels, weights, sum(weights) / H


def power_tail(M, H, s):
    """The sum of n^s over M <= n <= H by the Euler-Maclaurin formula with three corrections (no zeta is evaluated);
    for |s| <= 60 and M >= 2000 the next correction is below 1e-13 of M^Re(s)."""
    f = lambda x, e: cmath.exp(e * math.log(x))
    out = (f(H, s + 1) - f(M, s + 1)) / (s + 1) + (f(H, s) + f(M, s)) / 2
    out += s / 12 * (f(H, s - 1) - f(M, s - 1))
    out -= s * (s - 1) * (s - 2) / 720 * (f(H, s - 3) - f(M, s - 3))
    out += s * (s - 1) * (s - 2) * (s - 3) * (s - 4) / 30240 * (f(H, s - 5) - f(M, s - 5))
    return out


def spectrum(H, t0, dt, steps, kind="primes", sigma=-0.5, head=2000):
    """E(t) = |sum over n <= H of (weight(n) - mean) n^(sigma + i t)| at t = t0 + j dt, j = 0..steps-1.
    The weighted labels and the first labels of the constant part are summed term by term; beyond `head` labels the
    constant part's sum is the Euler-Maclaurin tail."""
    labels, weights, mean = window_weights(H, kind)
    M = min(H, head)
    ln = [math.log(n) for n in labels]
    z = [w * math.exp(sigma * x) * cmath.exp(1j * t0 * x) for w, x in zip(weights, ln)]
    r = [cmath.exp(1j * dt * x) for x in ln]
    lh = [math.log(n) for n in range(1, M + 1)]
    zh = [math.exp(sigma * x) * cmath.exp(1j * t0 * x) for x in lh]
    rh = [cmath.exp(1j * dt * x) for x in lh]
    out = []
    for j in range(steps):
        const = sum(zh)
        if H > M:
            const += power_tail(M + 1, H, complex(sigma, t0 + j * dt))
        out.append(abs(sum(z) - mean * const))
        z = [a * b for a, b in zip(z, r)]
        zh = [a * b for a, b in zip(zh, rh)]
    return out


def maxima(t0, dt, es):
    """The local maxima of a sampled spectrum, each refined by the parabola through its three samples: (t, height),
    tallest first."""
    out = []
    for i in range(1, len(es) - 1):
        a, b, c = es[i - 1], es[i], es[i + 1]
        if b > a and b >= c:
            d = (a - c) / (2 * (a - 2 * b + c))
            out.append((t0 + (i + d) * dt, b - (a - c) * d / 4))
    return sorted(out, key=lambda p: -p[1])


def peaks(H, count, lo, hi, dt=0.01, kind="primes", sigma=-0.5):
    """The `count` tallest maxima of the window's spectrum on lo <= t <= hi, by height: [(t, height)]."""
    steps = int(round((hi - lo) / dt)) + 1
    return sorted(maxima(lo, dt, spectrum(H, lo, dt, steps, kind, sigma))[:count])


# The exhibit's readings (20:D14, D15): the windows with the bound of their five peaks, and the deep window's exponents.
WINDOWS = ((13, 0.18), (39, 0.21), (173, 0.27), (1551, 0.21))
DEEP_SIGMAS = (-0.5, -0.25, -0.75, 0.0, -1.0)


def window_reading():
    """The reading of 20:D14 on the windows of the laboratory Subjects 173 and 1549 (depth 13 and 39) and of the
    laboratory Carriers 30089 and 2408561 (depth 173 and 1551): the prime vector with its mean removed sums to 0, the
    spectrum is even in the height, and the five tallest peaks on 10 <= t <= 36 lie within the window's bound of the first
    five heights. Returns (ok, detail)."""
    ok, parts = True, []
    for H, bound in WINDOWS:
        labels, weights, mean = window_weights(H)
        free = sum(weights) - mean * H                                   # the weights with their mean removed, summed over the H labels
        up, down = spectrum(H, 14.0, 7.0, 4), spectrum(H, -14.0, -7.0, 4)    # E at 14, 21, 28, 35 and at their negatives
        pk = peaks(H, 5, 10.0, 36.0)
        d = max(abs(t - h) for (t, _), h in zip(pk, HEIGHTS))
        ok &= abs(free) < 1e-9 and all(abs(a - b) < 1e-9 for a, b in zip(up, down)) and d <= bound
        parts.append(f"{H}: {d:.3f}")
    return ok, "largest distances " + ", ".join(parts)


def subset_control(H=13, bound=0.18, nxt=0.26, lo=10.0, hi=36.0, dt=0.01):
    """The control of 20:D14 at depth H: every proper nonempty subset of the labels 1..H read as the support of a vector,
    by the protocol of the exhibit (mean removed, the five tallest maxima on lo <= t <= hi, sorted, against the first five
    heights). A subset and its complement give the same spectrum, so the subsets without the label 1 list each pair once:
    2^(H-1) - 1 pairs. A pair with fewer than five maxima on the range is counted and lies within no bound (13 pairs at
    depth 13). The primes' pair alone lies within `bound`, it is the closest of all, and the next pair is at `nxt` to two
    decimals. Returns (ok, detail)."""
    steps = int(round((hi - lo) / dt)) + 1
    ln = [math.log(n) for n in range(1, H + 1)]
    cols = [[math.exp(-0.5 * x) * cmath.exp(1j * (lo + j * dt) * x) for j in range(steps)] for x in ln]
    total = [sum(c[j] for c in cols) for j in range(steps)]
    primes = set(window_weights(H)[0])
    run, inside, size = [0j] * steps, [False] * (H + 1), 0
    best, second, within, pairs, short, best_set = None, None, 0, 0, 0, None
    for i in range(1, 2 ** (H - 1)):                                     # Gray code over the labels 2..H: one label changes at a step
        n = 2 + ((i & -i).bit_length() - 1)
        col = cols[n - 1]
        if inside[n]:
            run = [a - b for a, b in zip(run, col)]; size -= 1
        else:
            run = [a + b for a, b in zip(run, col)]; size += 1
        inside[n] = not inside[n]
        frac = size / H
        five = sorted(maxima(lo, dt, [abs(a - frac * t) for a, t in zip(run, total)])[:5])
        pairs += 1
        if len(five) < 5:
            short += 1; continue
        d = max(abs(t - h) for (t, _), h in zip(five, HEIGHTS))
        within += d <= bound
        if best is None or d < best:
            best, second, best_set = d, best, {m for m in range(2, H + 1) if inside[m]}
        elif second is None or d < second:
            second = d
    ok = pairs == 2 ** (H - 1) - 1 and within == 1 and best_set == primes and best <= bound < second and abs(second - nxt) <= 0.005
    ok &= short == 13 or H != 13                                             # at depth 13 thirteen pairs have fewer than five maxima on the range
    return ok, f"{pairs} pairs of subsets: {within} within {bound}, the primes' pair at {best:.3f}, the next at {second:.3f}, {short} with fewer than five maxima"


def deep_reading(H=10 ** 6):
    """The evaluation of 20:D15 at depth H with the von Mangoldt weight: at a label n a mode has the modulus n^sigma, the
    spectrum is at most the sum of the moduli, the ten tallest peaks on 10 <= t <= 52 lie within 0.045 of the first ten
    heights. Returns (ok, detail)."""
    labels, weights, mean = window_weights(H, "mangoldt")
    pk = peaks(H, 10, 10.0, 52.0, dt=0.02, kind="mangoldt")
    d = max(abs(t - h) for (t, _), h in zip(pk, HEIGHTS))
    weight = dict(zip(labels, weights))
    cap = sum(abs(weight.get(n, 0.0) - mean) * n ** -0.5 for n in range(1, H + 1))    # the sum of the moduli at sigma = -1/2
    ok = d <= 0.045 and max(h for _, h in pk) <= cap
    ok &= all(abs(abs(n ** complex(s, t)) - n ** s) < 1e-9 * n ** s for n in (2, 13, H) for s in DEEP_SIGMAS for t in (HEIGHTS[0], HEIGHTS[9]))
    return ok, f"largest distance {d:.3f}"


# The emergence of the count (20:D16): the exponential integral, the step of a label, the count of a window from its
# dual, and Riemann's formula cut at a height. The heights with the number of zeros below each and the three bounds:
# the window's count against the count, Riemann's formula against the count, the two against each other.
EULER = 0.5772156649015329                                               # Euler's constant, the constant term of the series of Ei
MOBIUS = (0, 1, -1, -1, 0, -1, 1, -1)                                    # the Moebius function at 0..7: positions below 256
EMERGENCE = ((35.0, 5, 0.38, 0.48, 0.14), (78.0, 20, 0.21, 0.22, 0.10), (202.0, 80, 0.11, 0.15, 0.10))


def expint(z):
    """The exponential integral Ei(z) of a complex z off the negative real axis: gamma + log z + the sum of z^k/(k k!)
    for |z| <= 6 and in the sector |Im z| < Re z, and elsewhere the continued fraction of E1 at -z with
    Ei(z) = -E1(-z) +- i pi, the sign that of Im z. The readings below use it on the positive reals up to 4 and on
    arguments (1/2 + it) u with t >= 14, where it agrees with scipy.special.expi and exp1 and with mpmath.ei to 1e-14."""
    z = complex(z)
    if abs(z) <= 6.0 or abs(z.imag) < z.real:
        out, term = EULER + cmath.log(z), 1.0 + 0j
        for k in range(1, 400):
            term *= z / k
            out += term / k
            if abs(term) < 1e-17 * max(1.0, abs(out)): break
        return out
    w = -z
    b = w + 1.0; c = None; d = 1.0 / b; h = d
    for i in range(1, 400):
        a = -i * i; b += 2.0
        d = 1.0 / (a * d + b); c = b if c is None else b + a / c
        ratio_ = c * d; h *= ratio_
        if abs(ratio_ - 1.0) < 1e-15: break
    return -h * cmath.exp(-w) + (1j * math.pi if z.imag >= 0 else -1j * math.pi)


def label_step(u, T):
    """The step of one label in the count below the height T: (1/2 pi) times the integral over -T <= t <= T of
    e^((1/2 - it) u)/(1/2 - it), with u = log(x/n). It is Im Ei((1/2 + iT) u)/pi, plus 1 for u < 0, and at the label
    itself, u = 0, it is arctan(2T)/pi, the middle of the step."""
    if u == 0: return math.atan(2.0 * T) / math.pi
    return expint(complex(0.5, T) * u).imag / math.pi + (1.0 if u < 0 else 0.0)


def window_count(H, T, x):
    """The count of the window of depth H from its dual below the height T (20:D16), at a position x: (1/2 pi) times
    the integral over -T <= t <= T of w^(t) x^(1/2 - it)/(1/2 - it), with w^(t) the sum of n^(-1/2 + it) over the
    primes n of the window, its Dirichlet polynomial. Label by label it is the sum of the steps."""
    return sum(label_step(math.log(x / n), T) for n in window_weights(H)[0])


def riemann_counts(x, heights):
    """Riemann's formula for the count of the primes up to x, cut at the zeros below each of the heights (20:A6):
    the sum over n of mu(n)/n f(x^(1/n)), with f(y) = li(y) - the sum over the zeros of li(y^rho) - log 2 + the integral
    of 1/(u (u^2 - 1) log u) over u >= y, and li(y^rho) = Ei(rho log y). The terms with x^(1/n) < 2 are left out, as in
    the formula itself."""
    out = [0.0] * len(heights)
    for n in range(1, int(math.log2(x)) + 1):
        if not MOBIUS[n]: continue
        ly = math.log(x) / n
        f = lambda s: 1.0 / (s * math.expm1(2.0 * s))                    # the integral, in s = log u, by Simpson's rule on [ly, ly + 12]
        tail = (f(ly) + f(ly + 12.0) + sum((4 if j % 2 else 2) * f(ly + 0.02 * j) for j in range(1, 600))) * 0.02 / 3
        base = expint(ly).real - math.log(2.0) + tail
        zeros = [0.0] * len(heights)
        for g in HEIGHTS:
            e = expint(complex(0.5, g) * ly).real
            for j, T in enumerate(heights):
                if g < T: zeros[j] += e
        for j in range(len(heights)): out[j] += MOBIUS[n] / n * (base - 2.0 * zeros[j])
    return out


def emergence_reading(H=39):
    """The reading of 20:D16 on the window of the laboratory Subject 1549 (depth 39, twelve primes) at the heights 35,
    78 and 202, which have 5, 20 and 80 zeros of positive height below them. At the half-integers 2.5 to 38.5 the count from the window's
    dual lies within 0.38, 0.21 and 0.11 of the count of the primes, Riemann's formula within 0.48, 0.22 and 0.15, and
    the two within 0.14, 0.10 and 0.10 of each other. At the twelve prime labels each reads the middle of the step, the
    count less one half, within its own bound. The bounds between the two are for the half-integers: at the prime label
    23 and the height 78 the two differ by 0.106. Returns (ok, detail)."""
    primes = window_weights(H)[0]
    xs = [n + 0.5 for n in range(2, H)]
    true = [sum(1 for l in primes if l < x) for x in xs]
    middle = [sum(1 for l in primes if l <= p) - 0.5 for p in primes]
    heights = [e[0] for e in EMERGENCE]
    formula = [riemann_counts(x, heights) for x in xs]
    at_labels = [riemann_counts(float(p), heights) for p in primes]
    ok, parts = len(primes) == 12, []
    for j, (T, zeros, b_window, b_zeros, b_both) in enumerate(EMERGENCE):
        w = [window_count(H, T, x) for x in xs]; r = [row[j] for row in formula]
        dw = max(abs(a - c) for a, c in zip(w, true)); dr = max(abs(a - c) for a, c in zip(r, true)); db = max(abs(a - b) for a, b in zip(w, r))
        lw = max(abs(window_count(H, T, p) - m) for p, m in zip(primes, middle)); lr = max(abs(row[j] - m) for row, m in zip(at_labels, middle))
        ok &= sum(1 for g in HEIGHTS if g < T) == zeros and dw <= b_window and dr <= b_zeros and db <= b_both and lw <= b_window and lr <= b_zeros
        parts.append(f"{T:.0f}: {dw:.3f}, {dr:.3f}, {db:.3f} ({lw:.3f}, {lr:.3f})")
    gap = abs(window_count(H, 78.0, 23.0) - at_labels[primes.index(23)][heights.index(78.0)])
    ok &= abs(gap - 0.106) < 0.0005 and gap > EMERGENCE[1][4]                # above the bound 0.10 that holds between the two at the half-integers
    return ok, ("largest differences (the window's count, Riemann's formula, between the two; in brackets the first two at the prime labels, "
                "from the count less one half) at the heights " + "; ".join(parts) + f"; at the label 23 and the height 78 the two differ by {gap:.3f}")


# The bound of the count (20:D17): the count of a real vector on a list of labels below a height, and the bound
# B(x)/T on its difference from the count of the vector below a position x that is no label.
def vector_count(labels, T, x, weights=None):
    """The count below the height T of a real vector on a list of labels, at a position x: the sum over the labels of
    the weight times the step of the label. Without weights the vector is the indicator of the labels."""
    weights = weights or [1.0] * len(labels)
    return sum(w * label_step(math.log(x / n), T) for n, w in zip(labels, weights))


def count_bound(labels, x, weights=None):
    """B(x) of 20:D17 for a real vector on a list of labels, at a position x that is no label: (1/pi) times the sum
    over the labels of |w(n)| sqrt(x/n)/|log(x/n)|. The count below the height T lies within B(x)/T of the count of the
    vector below x (the theorem FRC.Chart.Perron.count_bound, on Mathlib)."""
    weights = weights or [1.0] * len(labels)
    return sum(abs(w) * math.sqrt(x / n) / abs(math.log(x / n)) for n, w in zip(labels, weights)) / math.pi


def bound_reading(H=39):
    """The reading of 20:D17. On the windows of depth 13 and H, at the half-integers and the heights 35, 67, 78 and
    202, for the prime vector and for the indicator vector of all the labels, the count lies within B(x)/T of the count
    of the vector below x; so it does for a signed vector on the labels of depth H at the quarter positions. For
    H = 39 the prime vector has B(x) <= 33.14 at the half-integers 2.5 to 38.5: the bound is at most
    0.95, 0.43 and 0.17 at the heights 35, 78 and 202 and below one half from the height 67 on, and the nearest integer
    to the count at the height 67 is the count of the primes. Returns (ok, detail)."""
    ok, worst = True, 0.0
    heights = (35.0, 67.0, 78.0, 202.0)
    for depth in (13, H):
        xs = [n + 0.5 for n in range(2, depth)]
        for labels in (window_weights(depth)[0], list(range(1, depth + 1))):
            for T in heights:
                for x in xs:
                    ratio = abs(vector_count(labels, T, x) - sum(1 for n in labels if n < x)) * T / count_bound(labels, x)
                    worst = max(worst, ratio); ok &= ratio <= 1.0
    labels = list(range(1, H + 1)); signed = [(-1.0) ** n * (1 + n % 3) / 2 for n in labels]
    for T in heights:
        for x in [n + 0.25 for n in range(0, H + 1)]:
            below = sum(w for n, w in zip(labels, signed) if n < x)
            ratio = abs(vector_count(labels, T, x, signed) - below) * T / count_bound(labels, x, signed)
            worst = max(worst, ratio); ok &= ratio <= 1.0
    primes = window_weights(H)[0]; xs = [n + 0.5 for n in range(2, H)]
    top = max(count_bound(primes, x) for x in xs)
    ok &= top <= 33.14 and 33.14 / 67.0 < 0.5
    ok &= all(math.ceil(100 * 33.14 / T) / 100 == b for T, b in ((35.0, 0.95), (78.0, 0.43), (202.0, 0.17)))
    ok &= all(round(vector_count(primes, 67.0, x)) == sum(1 for n in primes if n < x) for x in xs)
    return ok, f"largest B(x) at the half-integers of depth {H}: {top:.3f}; largest ratio of a difference to its bound: {worst:.3f}"


# A mode near every height (20:D18): the polynomial of the proof in exact integers, and the smallest sum over the modes
# of the squared distances to given complex numbers of modulus one [chart].
def polynomial_exact(B):
    """The polynomial of 20:D18 in exact integers: (1 - x) * sum_{s<B} (s+1)(B-s) x^s = sum_{s<=B} (B-2s) x^s, and the
    sums of the squared coefficients are B(B+1)(B+2)((B+1)^2+1)/30 and B(B+1)(B+2)/3, of ratio 10/((B+1)^2+1)."""
    a = [(s + 1) * (B - s) for s in range(B)]
    prod = [0] * (B + 1)
    for s, c in enumerate(a):
        prod[s] += c; prod[s + 1] -= c
    return (prod == [B - 2 * s for s in range(B + 1)]
            and 30 * sum(c * c for c in a) == B * (B + 1) * (B + 2) * ((B + 1) ** 2 + 1)
            and 3 * sum(c * c for c in prod) == B * (B + 1) * (B + 2))


def mode_table(p, scales):
    """The modes at labels of given scales, in the chart of the cycle: for each mode k < p - 1 the cosine and the sine
    of the angle 2 pi (k * scale mod (p - 1))/(p - 1) of its value at each label."""
    n = p - 1
    cols = []
    for a in scales:
        ang = [2 * math.pi * ((k * a) % n) / n for k in range(n)]
        cols += [[math.cos(x) for x in ang], [math.sin(x) for x in ang]]
    return list(zip(*cols))


def nearest_mode(table, angles):
    """The smallest sum over the modes of the squared distances |chi_k(l_j) - u_j|^2 to the complex numbers
    u_j = e^{i angle_j} of modulus one: 2m minus twice the largest sum over j of cos(angle of the mode - angle_j)."""
    w = []
    for a in angles: w += [math.cos(a), math.sin(a)]
    return 2 * len(angles) - 2 * max(sum(x * y for x, y in zip(row, w)) for row in table)


def heights_reading(cases):
    """The evaluation of 20:D18. A case is (p, primes, B, scales): distinct primes of the window of the shell p with
    product^B < p, and their scales on the latitude cycle. For each case, at each of the heights t = 0.5, 1, ..., 100
    (u_j = l_j^{it}), the smallest sum over the modes of |chi_k(l_j) - u_j|^2 is at most 10 m/((B + 1)^2 + 1) (the
    theorem FRC.Chart.Heights.mode_near_height, on Mathlib). For the primes 2 and 3 on the Subject 1549: B = 4, the
    bound is 10/13, and at each of these heights the smallest sum is at most 0.01. Returns (ok, detail)."""
    heights = [0.5 * i for i in range(1, 201)]
    ok, ratio, stated = True, 0.0, None
    for p, primes, B, scales in cases:
        m, table = len(primes), mode_table(p, scales)
        bound = 10 * m / ((B + 1) ** 2 + 1)
        worst = max(nearest_mode(table, [t * math.log(l) for l in primes]) for t in heights)
        ok &= worst <= bound + 1e-9
        ratio = max(ratio, worst / bound)
        if (p, tuple(primes)) == (1549, (2, 3)):
            stated = (B, bound, worst)
            ok &= B == 4 and abs(bound - 10 / 13) < 1e-12 and worst <= 0.01
    ok &= stated is not None
    return ok, (f"primes 2 and 3 on the Subject 1549: B = {stated[0]}, bound {stated[1]:.4f}, largest of the smallest sums at the 200 heights: {stated[2]:.6f}; "
                f"largest ratio of a smallest sum to its bound over {len(cases)} cases: {ratio:.3f}")


HEIGHTS = [14.134725141734693, 21.022039638771555, 25.010857580145688, 30.424876125859513, 32.935061587739189,
           37.586178158825671, 40.918719012147495, 43.327073280914999, 48.005150881167159, 49.773832477672302,
           52.970321477714460, 56.446247697063394, 59.347044002602353, 60.831778524609809, 65.112544048081606,
           67.079810529494173, 69.546401711173979, 72.067157674481907, 75.704690699083933, 77.144840068874805,
           79.337375020249367, 82.910380854086030, 84.735492980517050, 87.425274613125229, 88.809111207634465,
           92.491899270558484, 94.651344040519886, 95.870634228245309, 98.831194218193692, 101.317851005731392,
           103.725538040478339, 105.446623052326094, 107.168611184276408, 111.029535543169675, 111.874659176992637,
           114.320220915452713, 116.226680320857554, 118.790782865976217, 121.370125002420646, 122.946829293552588,
           124.256818554345767, 127.516683879596495, 129.578704199956051, 131.087688530932657, 133.497737202997586,
           134.756509753373871, 138.116042054533443, 139.736208952121389, 141.123707404021124, 143.111845807620633,
           146.000982486765519, 147.422765342559602, 150.053520420784880, 150.925257612241467, 153.024693811198896,
           156.112909294237868, 157.597591817594060, 158.849988171420499, 161.188964137596028, 163.030709687181987,
           165.537069187900419, 167.184439978174513, 169.094515415568821, 169.911976479411699, 173.411536519591553,
           174.754191523365726, 176.441434297710419, 178.377407776099977, 179.916484020256996, 182.207078484366462,
           184.874467848387509, 185.598783677707471, 187.228922583501852, 189.416158656016937, 192.026656360713787,
           193.079726603845704, 195.265396679529235, 196.876481840958317, 198.015309676251912, 201.264751943703789]   # the first eighty heights, 20:A6 [import]
CR = types.SimpleNamespace(HEIGHTS=HEIGHTS, window_weights=window_weights, power_tail=power_tail, spectrum=spectrum, maxima=maxima, peaks=peaks,
                           window_reading=window_reading, deep_reading=deep_reading, subset_control=subset_control,
                           expint=expint, label_step=label_step, window_count=window_count, riemann_counts=riemann_counts, emergence_reading=emergence_reading,
                           vector_count=vector_count, count_bound=count_bound, bound_reading=bound_reading,
                           polynomial_exact=polynomial_exact, mode_table=mode_table, nearest_mode=nearest_mode, heights_reading=heights_reading)

# ======================================================================================================================
# block A — the shell, in exact arithmetic
# The shells p = 13, 17, 29, 37, 41 in full, and 173; the laboratory Carriers for the closure and the laboratory pairs
# (13, 233), (173, 30089), (1549, 2408561) for completeness. The generator g is the least primitive root, as in the paper.
def block_A():
    """Block A — the shell, in exact arithmetic: 54 checks, 49 EXACT and 5 [approx] readings of the chart's characters (A7b, one per shell)."""
    print("\n== block A: the shell ==")
    for p in SHELLS + [BIG]:
        g = generator(p)
        kappa = (p - 1) // 4; assert 4 * kappa + 1 == p
        # A1 zero-slot
        ok = all(sum(pow(x, k, p) for x in range(1, p)) % p == 0 for k in range(1, p - 1)) \
             and sum(pow(x, p - 1, p) for x in range(1, p)) % p == p - 1
        # 20:B4 (p20011)
        check("A1", f"zero-slot on F_{p}", ok, f"Σx^k=0 for k=1..{p-2}; = -1 at k={p-1}")
        # A6 the Subject constants, capacity-first
        pi_ = 2 * kappa
        i_ = pow(g, p - 1 - kappa, p)                       # g^{-κ}
        assert i_ == (-pow(g, kappa, p)) % p
        i_odd = i_ if i_ % 2 == 1 else i_ + p               # the odd integer lift of i (Remark frame)
        e_ = pow(g, i_odd, p)
        ok = ((2 * pi_) % p == p - 1 and (i_ * i_) % p == p - 1 and pow(g, pi_, p) == p - 1
              and pow(e_, i_odd * pi_, p) == p - 1 and (2 * (2 * kappa + 1)) % p == 1
              and (2 * kappa + 1) % p == (-pi_) % p)
        # 20:B10 (p20017)
        check("A6", f"Subject constants on F_{p}: π=2κ, i=g^-κ, e=g^i (odd lift)", ok,
              f"g={g} κ={kappa} π={pi_} i={i_} e={e_}: 2π≡-1, i²≡-1, g^π≡-1, e^(iπ)≡-1, 2⁻¹=2κ+1=-π")
        # A7 the shell theorem (Thm. hp) on F_p, every clause in F_p: (i) the dual inverts, the constant mode the mean term;
        # (iii) D x^k = g^k x^k on the power characters (the drive D : x ↦ g x), Tr D^r = (p−1)[(p−1)|r]; (iv) W² = −J, F² = J, F⁴ = 1 for W_mk = g^mk,
        # F = iW; (v) the explicit formula along the meridian, Σ_{y≤x} v(y) = −Σ_k v̂(k) S_k(x), S_0(x) = x; three random vectors
        vecs = random_vectors(p, 3, seed=20 * p)
        ok_i = ok_v = True
        for v in vecs:
            vh = dual(v, p)
            ok_i &= all((-sum(vh[k] * pow(y, (p - 1 - k) % (p - 1), p) for k in range(p - 1))) % p == v[y] for y in range(1, p)) \
                    and vh[0] == sum(v) % p
            S = lambda k, x: sum(pow(y, (p - 1 - k) % (p - 1), p) for y in range(1, x + 1)) % p
            ok_v &= all((-sum(vh[k] * S(k, x) for k in range(p - 1))) % p == sum(v[1:x + 1]) % p for x in range(1, p)) \
                    and all(S(0, x) == x % p for x in range(1, p))
        ok_fp = all(pow((g * x) % p, k, p) == (pow(g, k, p) * pow(x, k, p)) % p for k in range(p - 1) for x in range(1, p))
        tr = [sum(1 for x in range(1, p) if (pow(g, r, p) * x) % p == x) for r in range(1, p)]
        ok_tr = all(tr[r - 1] == ((p - 1) if r % (p - 1) == 0 else 0) for r in range(1, p))
        n_ = p - 1
        W = np.array([[pow(g, (m * k) % n_, p) for k in range(n_)] for m in range(n_)], dtype=np.int64)
        J = np.array([[1 if (m + l) % n_ == 0 else 0 for l in range(n_)] for m in range(n_)], dtype=np.int64)
        W2 = (W @ W) % p
        F2 = (i_ * i_ * W2) % p                              # F = iW: F² = i² W²
        ok_iv = np.array_equal(W2, (-J) % p) and np.array_equal(F2, J) and np.array_equal((F2 @ F2) % p, np.eye(n_, dtype=np.int64))
        # 20:E12 (p20043), 20:E14 (p20092)
        check("A7", f"the shell theorem on F_{p}: (i) the dual inverts, v(y) = −Σ v̂(k) y^−k, v̂(0) the mean term; (iii) D x^k = g^k x^k, Tr D^r = (p−1)[(p−1)|r]; (iv) W² = −J, F² = J, F⁴ = 1; (v) the explicit formula along the meridian, S_0(x) = x",
              ok_i and ok_fp and ok_tr and ok_iv and ok_v, f"three random vectors; W of order {n_}")
        # A14 the Parseval identity (Thm. hp (ii)): Σ_k v̂(k) v̂(−k) = −Σ_x v(x)² in F_p, on random vectors and on the prime-power
        # indicator of the whole shell (the window's prime vector of Def. vector is its restriction to the window; the identity holds for every vector)
        prime_vec = [0] + [1 if is_prime(x) or (len(prime_factors(x)) == 1 and x > 1) else 0 for x in range(1, p)]
        ok = True
        for v in vecs + [prime_vec]:
            vh = dual(v, p)
            ok &= sum(vh[k] * vh[(-k) % (p - 1)] for k in range(p - 1)) % p == (-sum(x * x for x in v)) % p
        # 20:E13 (p20044)
        check("A14", f"the Parseval identity on F_{p}: Σ_k v̂(k) v̂(−k) = −Σ_x v(x)² for three random vectors and the prime-power indicator of the shell", ok,
              f"prime-power indicator: {sum(prime_vec)} labels")
        if p == BIG:
            continue
        # A7b the chart's reading of the Parseval identity (Rem. parseval) [approx]: the complex characters χ_j(n) = ω^{jλ(n)} on
        # ℓ²(F_p^×) are orthogonal with ‖χ_j‖² = p−1, the dual inverts, and Σ_j |v̂_C(j)|² = (p−1) Σ |v|²; D χ_j = ω^j χ_j, the
        # drive's chart a unitary permutation matrix whose eigenvalues are the (p−1)-th roots of unity (Rem. chart-operator)
        lam = {}
        for n in range(1, p):
            base = prime_factors(n)
            lam[n] = math.log(min(base)) if len(base) == 1 else 0.0
        v = np.array([lam[n] for n in range(1, p)])
        dlog = dlog_table(p, g)
        w = cmath.exp(2j * math.pi / (p - 1))
        chi = np.array([[w ** (j * dlog[n]) for n in range(1, p)] for j in range(p - 1)])
        gram = chi.conj() @ chi.T
        vc = chi @ v
        ok_orth = np.allclose(gram, (p - 1) * np.eye(p - 1), atol=1e-9)
        ok_par = abs(np.sum(np.abs(vc) ** 2) - (p - 1) * np.sum(v ** 2)) < 1e-9
        ok_inv = np.allclose((chi.conj().T @ vc).real / (p - 1), v, atol=1e-10)
        shifted = lambda j: np.array([w ** (j * dlog[(g * n) % p]) for n in range(1, p)])   # (S χ_j)(n) = χ_j(g n)
        ok_c = all(np.allclose(shifted(j), w ** j * chi[j]) for j in range(p - 1))
        Dm = np.zeros((p - 1, p - 1)); dl = dlog_table(p, g)
        for n in range(1, p): Dm[n - 1, (g * n) % p - 1] = 1.0                       # (Dv)(n) = v(gn): a permutation matrix
        ok_u = np.allclose(Dm @ Dm.T, np.eye(p - 1)) and np.allclose(sorted(np.angle(np.linalg.eigvals(Dm)) % (2 * np.pi)), sorted(2 * np.pi * np.arange(p - 1) / (p - 1)), atol=1e-9)
        check("A7b", f"the chart's characters on ℓ²(F_{p}^×): χ_j orthogonal with ‖χ_j‖² = p−1, Σ_j|v̂(j)|² = (p−1)Σ|v|² for v = Λ, the dual inverts; Dχ_j = ω^j χ_j, the drive a unitary permutation with the (p−1)-th roots of unity as its eigenvalues",
              ok_orth and ok_par and ok_inv and ok_c and ok_u, f"Σ|v̂|²/(p−1) = {np.sum(np.abs(vc) ** 2) / (p - 1):.6f}", kind="[approx]")
        # A10 the shared quarter-turn core; no cycle projection onto (13, 233)
        Om = 233
        q4 = {pow(i_, a, p) for a in range(4)}
        ok = q4 == {1, i_, p - 1, (-i_) % p} and (p - 1) % 4 == 0 and (Om - 1) % 4 == 0
        if p == 13:
            ok = ok and (Om - 1) % (p - 1) != 0
            # 20:B1 (p20008)
            check("A10", "Q₄ ⊂ both cycles; C_232 ↠ C_12 does not exist (12 ∤ 232) on the pair (13, 233)", ok, "the shells share the core, not a clock")
        else:
            check("A10", f"Q₄ = {{1, i, −1, −i}} ⊂ F_{p}^×, 4 | p−1", ok)
    # A11 frame coincidence within the observational horizon (Prop. coincide): the Carrier chart Ω is the least prime ≡ 1 (mod 4) above p²
    for p in SHELLS + [1009, 10009]:
        Om = next_prime(p * p)
        while Om % 4 != 1:
            Om = next_prime(Om)
        q = max(n for n in range(1, p) if n * n < p)                # the observational horizon: the largest label with q² < p
        same = all(n % p == n % Om == n for n in range(1, q + 1))
        prods = all((a * b) % p == (a * b) % Om == a * b for a in range(1, q + 1) for b in range(1, q + 1))
        irreducible = {n for n in range(2, q + 1) if all(n % d for d in range(2, math.isqrt(n) + 1))}   # trial division inside the window
        primes = {n for n in range(2, q + 1) if is_prime(n)}
        # 20:B2 (p20009)
        check("A11", f"frame coincidence within the observational horizon q = {q} of F_{p}, q² < {p}, on the pair ({p}, {Om}): residues, products and primality agree", same and prods and irreducible == primes,
              f"Π_p = {sorted(primes)}")
    # A6b the odd-lift rule (Remark frame) on every admissible frame below 3000, least primitive root
    frames = [q for q in range(5, 3000) if q % 4 == 1 and is_prime(q)]
    bad = []
    for q in frames:
        gq = generator(q); kq = (q - 1) // 4; piq = 2 * kq
        r = pow(gq, q - 1 - kq, q)                          # the least residue of i = g^{-κ}
        odd, even = (r, r + q) if r % 2 == 1 else (r + q, r)
        e_odd = pow(gq, odd, q)
        if not (pow(e_odd, odd * piq, q) == q - 1 and pow(e_odd, even * piq, q) == 1 and (r * r) % q == q - 1):
            bad.append(q)
    f17 = (pow(3, 16 - 4, 17), pow(3, 21, 17))               # F_17 with g = 3: i = 3^{-4} = 4 (even), lift 21, e = 3^21 = 5
    ok = not bad and f17 == (4, 5)
    check("A6b", f"the odd-lift rule on all {len(frames)} frames p ≡ 1 (mod 4) below 3000: e^{{iπ}} ≡ −1 on the odd lift, ≡ +1 on the even member; F_17: g=3, i=4, lift 21, e=5", ok,
          f"frames {len(frames)}, failures {bad}; F_17 (i, e) = {f17}")

    # A12 the closure of the zeros (Thm. closure; rows A2, A4, F7), on the four laboratory Carriers Ω = 13, 233, 30089,
    # 2408561: the largest embedded Subject p* with p*² < Ω < p'² (p' the next prime); the residues of a cycle are its labels
    # 0..q−1 and a Subject of cardinality p reads the residues y < p, its own residues, so an embedded Subject's cycle is shorter
    # than the Carrier's and the Carrier's top residue is read from labels up to the horizon of Ω, beyond the horizon of every embedded Subject; the
    # wrap of the height reading, (T + Ω) ≡ T; the pigeonhole of 00:A2/00:A4 on the residues — a reading of the Ω residues into
    # o < Ω records identifies two residues (found by search for o = p* and o = Ω − 1), and an injective reading needs o ≥ Ω
    def largest_subject(Om):
        """The largest admissible Subject of Ω: the largest prime p = 4κ+1 with κ > 1 and p² < Ω (Remark holographic), or None."""
        q = math.isqrt(Om - 1)
        while q >= 13 and not (is_prime(q) and q % 4 == 1): q -= 1
        return q if q >= 13 else None
    assert largest_subject(13) is None and largest_subject(401) == 17 and is_prime(19) and 19 * 19 < 401   # the empty case; the control
    for Om in (233, 30089, 2408561):
        ps = largest_subject(Om)
        ok = is_prime(Om) and Om % 4 == 1 and is_prime(ps) and ps % 4 == 1 and ps > 5 and ps * ps < Om
        ok &= all(not (is_prime(q) and q % 4 == 1) for q in range(ps + 1, math.isqrt(Om - 1) + 1))   # no larger admissible Subject with its square below Ω
        ok &= ps < Om and math.isqrt(ps) < math.isqrt(Om)                   # the embedded cycle shorter; the top window's labels beyond the horizon of p*
        ok &= all((T + Om) % Om == T % Om for T in (0, 1, ps, Om - 1, Om, 7 * Om + 3))   # the wrap of the height reading
        collisions = {}
        for o in (ps, Om - 1):
            seen = {}
            for y in range(Om):                                             # the residues of the Carrier's cycle, read into o states
                r = y % o
                if r in seen:
                    collisions[o] = (seen[r], y); break
                seen[r] = y
            ok &= o in collisions and collisions[o][0] != collisions[o][1] and collisions[o][0] % o == collisions[o][1] % o
        ok &= len({y for y in range(Om)}) == Om                             # the identity reading into Ω states is injective: Ω ≤ Ω
        ok &= CT.zeros_not_held(ps, Om) and CT.zeros_not_held(ps, Om, lambda y: (7 * y + 3) % ps)   # p* < Ω − 2: each reading tried identifies two zeros
        spare = [max(0, y - 1) for y in range(Om)]                          # a reading into Ω − 1 states: its one collision is 0 with 1,
        ok &= len(set(spare)) == Om - 1 and spare[0] == spare[1] and len(set(spare[2:])) == Om - 2   # and it keeps the Ω − 2 zeros apart
        ok &= len({y - 2 for y in range(2, Om)}) == Om - 2                    # Ω − 2 states hold the zeros
        # 20:A2 (p00004), 20:A4 (p00197), 20:F7 (p20079)
        check("A12", f"closure of the zeros on Ω = {Om}: the largest admissible Subject p* = {ps} ({ps}² < Ω, and no larger prime 4κ + 1 has its square below Ω), the cycle's {Om} residues, an embedded Subject reads {ps} of them; readings into {ps} and {Om - 1} states collide; the {Om - 2} zeros are more than the {ps} states, and every reading tried identifies two zeros; a reading into {Om - 1} states keeps the zeros apart and identifies 0 with 1 alone", ok,
              f"collisions {collisions}; the horizons of the chart F_Ω and of p*: {math.isqrt(Om)}, {math.isqrt(ps)}")

    # A13 Completeness (row A3; 00:A3), on the laboratory pairs (p, Ω): the registration of a totality is onto its registered
    # Universe — the registered Universe is the set of residues at which some member registers, read back as a member for every
    # residue of it (the Carrier's residues registered whole, ρ(y) = y, and the Subject's reading of them, ρ_p(y) = y mod p: Ω and p
    # residues, each with a member); and two totalities each registered whole within the other have one count — the identity
    # registers the Subject's cycle within the Carrier's, every reading of the Carrier's Ω residues into the Subject's p records
    # identifies two residues (y mod p, an affine reading, the square; the pigeonhole of 00:A2 both ways is
    # FRC.Foundation.mutual_registration_count), and only cycles of one count embed both ways
    for p, Om in PAIRS:
        members = {}
        for y in range(Om):                                                 # the Carrier's cycle registered whole
            members.setdefault(y % Om, y)
        ok = len(members) == Om and all(members[r] % Om == r for r in members)          # onto: every residue has a member
        membersp = {}
        for y in range(Om):                                                 # the Subject's reading of the Carrier's residues
            membersp.setdefault(y % p, y)
        ok &= len(membersp) == p and all(membersp[r] % p == r for r in membersp)
        ok &= len({x % Om for x in range(p)}) == p                          # the identity registers Shell p within Shell Ω
        readings = {"y mod p": lambda y: y % p, "3y+5 mod p": lambda y: (3 * y + 5) % p, "y² mod p": lambda y: (y * y) % p}
        collisions = {}
        for name, f in readings.items():                                    # no reading of Shell Ω within Shell p is injective
            seen = {}
            for y in range(Om):
                r = f(y)
                if r in seen:
                    collisions[name] = (seen[r], y); break
                seen[r] = y
            ok &= name in collisions and collisions[name][0] != collisions[name][1] and f(collisions[name][0]) == f(collisions[name][1])
        ok &= p < Om and len({x % p for x in range(p)}) == p                 # one count: the identity both ways on Shell p
        # 20:A3 (p00003)
        check("A13", f"completeness on the pair ({p}, {Om}): the registration of the cycle is onto its registered Universe ({Om} residues; {p} under the Subject's reading); F_{p} registers within F_{Om}, every reading of the {Om} residues into {p} records collides, one count only both ways", ok,
              "collisions " + ", ".join(f"{k}: {v}" for k, v in collisions.items()))

    # A19 the drive theorem (Thm. drive; row E15), on every shell: the drive acts on vectors over F_p^× by (Dv)(x) = v(gx), one
    # chronon. (ii) D x^k = g^k x^k for every mode k (the eigenvector identity, FRC.Rh.shift_power_character) and the eigenvalues
    # g^k are the p−1 nonzero residues, each once: the spectrum is F_p^×, simple; (i) D is orthogonal for the pairing
    # ⟨v, w⟩ = Σ_x v(x) w(x), ⟨Dv, w⟩ = ⟨v, D⁻¹w⟩ on three random pairs, not symmetric, while D + D⁻¹ is symmetric; (iii) the
    # spectrum is real — every eigenvalue a residue of F_p, Frobenius-fixed — and the modes are isotropic, ⟨x^k, x^k⟩ = Z(2k) = 0
    # for k ≠ 0, π and −1 there; (iv) at x = g^m the mode of count k has the value g^(km) (FRC.Horizon.mode_stride)
    for p in SHELLS + [BIG]:
        g = generator(p); n_ = p - 1; pi_ = n_ // 2; ginv = pow(g, p - 2, p); xs = range(1, p)
        D = lambda v: {x: v[(g * x) % p] for x in xs}
        Dinv = lambda v: {x: v[(ginv * x) % p] for x in xs}
        pair = lambda v, w: sum(v[x] * w[x] for x in xs) % p
        modes = {k: {x: pow(x, k, p) for x in xs} for k in range(n_)}
        spec = [pow(g, k, p) for k in range(n_)]
        ok_ii = all(D(modes[k]) == {x: spec[k] * modes[k][x] % p for x in xs} for k in range(n_)) and sorted(spec) == list(range(1, p))
        rng = random.Random(2026 + p)
        vs = [{x: rng.randrange(p) for x in xs} for _ in range(6)]
        pairs3 = ((vs[0], vs[1]), (vs[2], vs[3]), (vs[4], vs[5]))
        ok_i = all(pair(D(v), w) == pair(v, Dinv(w)) for v, w in pairs3)
        symmetric = lambda T: all(pair(T(v), w) == pair(v, T(w)) for v, w in pairs3)
        ok_sym = (not symmetric(D)) and symmetric(lambda v: {x: (D(v)[x] + Dinv(v)[x]) % p for x in xs})
        ok_iii = all(0 < s < p for s in spec) and all(pair(modes[k], modes[k]) == (p - 1 if k in (0, pi_) else 0) for k in range(n_))
        ok_iv = CT.mode_stride(p, g)
        # 20:E15 (p20094)
        check("A19", f"the drive theorem on F_{p}: D x^k = g^k x^k for every mode, the spectrum F_{p}^× simple; ⟨Dv, w⟩ = ⟨v, D⁻¹w⟩ on three random pairs, D not symmetric, D + D⁻¹ symmetric; the spectrum real and the modes isotropic (⟨x^k, x^k⟩ = 0 for k ≠ 0, π, −1 there); at x = g^m the mode of count k has the value g^(km)",
              ok_i and ok_ii and ok_sym and ok_iii and ok_iv, f"g={g}, π={pi_}: eigenvalues g^k = {spec[:6]}…")


def heights_cases():
    """The cases of 20:D18, in exact integers, on the Subjects 13, 173 and 1549: the first primes of the window while
    their product is below p; the largest B with product^B < p; the scales of the primes on the latitude cycle. The
    monomials with exponents up to B are below p and distinct, and the polynomial identities hold for B up to 60.
    Returns (ok, cases) for CR.heights_reading."""
    ok = all(CR.polynomial_exact(B) for B in range(1, 61))
    cases = []
    for p in (13, 173, 1549):
        g = generator(p); table = CT.scale_table(p, g); q = math.isqrt(p - 1)
        primes, P = [], 1
        for l in (2, 3, 5, 7):
            if l > q or P * l >= p: break
            primes.append(l); P *= l
            B = 1
            while P ** (B + 1) < p: B += 1
            tuples, values = [()], set()
            for _ in primes: tuples = [r + (e,) for r in tuples for e in range(B + 1)]
            for r in tuples:
                v = 1
                for x, e in zip(primes, r): v *= x ** e
                ok &= v < p; values.add(v)
            ok &= len(values) == (B + 1) ** len(primes)
            cases.append((p, list(primes), B, [table[x] for x in primes]))
    return ok, cases


def label_cases():
    """The cases of 20:D19: every label from 2 of the windows of the Subjects 13, 173 and 1549; and the residues g^j,
    j = 2, 3, 4, 6, 12, with all their powers. For the label 3 on the Subject 1549 the pair (N, W) is (6, 258), and the
    powers of 3 stand 6 places apart. Returns (ok, the number of labels)."""
    ok, count = True, 0
    for p in (13, 173, 1549):
        g = generator(p); table = CT.scale_table(p, g)
        for l in range(2, math.isqrt(p - 1) + 1):
            ok &= CT.label_steps(p, g, l, table); count += 1
        for j in (2, 3, 4, 6, 12):
            x = pow(g, j, p)
            if x != 1: ok &= CT.power_steps(p, g, x, (p - 1) // math.gcd(j, p - 1) - 1, table)
    g = generator(1549)
    return ok and CT.label_pair(1549, 3) == (6, 258) and CT.step_width(1549, g, 3) == 6, count


# ======================================================================================================================
# block D — the prime vector in the chart [chart]
# The spectrum of a window against the classical heights (rows D13, D14, D15), the count of a window from its dual with its bound (rows D16, D17), a mode near every height (row D18) and the value of a mode at one label (row D19).
# ======================================================================================================================
def block_D():
    """Block D — the prime vector in the chart: 5 floating-point evaluations, two compared with the classical heights, with the control over the subsets of the window of depth 13, the count of a window from its dual with its bound, and a mode near every height, computed in the chart tier (the depth 10⁶ takes about 15 s); and the value of a mode at one label, in exact integers."""
    ok, detail = CR.window_reading()
    ok2, detail2 = CR.subset_control()
    ok, detail = ok and ok2, detail + "; " + detail2
    # 20:D14 (p20113)
    check("D14", "the window's primes show the heights [chart]: on the windows of depth 13, 39, 173 and 1551 the prime vector with its mean removed sums to 0, E(−t) = E(t), and the five tallest peaks of E on 10 ≤ t ≤ 36 lie within 0.18, 0.21, 0.27 and 0.21 of the first five heights; of the 4095 pairs of complementary subsets of the 13 labels, read the same way, the primes' pair alone lies within 0.18, the closest of all, the next at 0.26; 13 pairs have fewer than five maxima on the range",
            ok, detail, kind="[approx]")
    ok, detail = CR.deep_reading()
    # 20:D15 (p20114)
    check("D15", "the deep window [chart]: at a label n a mode has the modulus n^σ and E(t) ≤ Σ|λ(n) − λ̄| n^σ; with the von Mangoldt weight at depth 10⁶ the ten tallest peaks on 10 ≤ t ≤ 52 lie within 0.045 of the first ten heights",
            ok, detail, kind="[approx]")
    ok, detail = CR.emergence_reading()
    # 20:D16 (p20116)
    check("D16", "the count of a window from its dual [chart]: on the window of depth 39, the twelve primes of the Subject 1549, at the half-integers 2.5 to 38.5 and the heights 35, 78 and 202, the count C_T lies within 0.38, 0.21 and 0.11 of π(x), the count of the primes; Riemann's formula with the 5, 20 and 80 zeros of positive height below the same heights lies within 0.48, 0.22 and 0.15 of it, and the two lie within 0.14, 0.10 and 0.10 of each other; at the twelve prime labels each reads π(x) − 1/2, the middle of the step, within its own bound, and at the label 23 and the height 78 the two differ by 0.106",
            ok, detail, kind="[approx]")
    ok, detail = CR.bound_reading()
    # 20:D17 (p20117)
    check("D17", "the bound of the count [chart]: on the windows of depth 13 and 39, at the half-integers and the heights 35, 67, 78 and 202, for the prime vector and for the indicator vector of all the labels, and at the quarter positions for a signed vector on the labels of depth 39, the count C_T lies within B(x)/T of the count of the vector below x, with B(x) = (1/π) Σ |w(n)| √(x/n)/|log(x/n)|; on the window of depth 39 the prime vector has B(x) ≤ 33.14 at the half-integers, so the bound is at most 0.95, 0.43 and 0.17 at the heights 35, 78 and 202 and below one half from the height 67 on, and the nearest integer to the count at the height 67 is π(x)",
            ok, detail, kind="[approx]")
    ok, cases = heights_cases()
    ok2, detail = CR.heights_reading(cases)
    # 20:D18 (p20118)
    check("D18", "a mode near every height [chart]: on the Subjects 13, 173 and 1549, for the first primes of the window with product^B < p, the smallest sum over the modes of the squared distances |χ_k(ℓ_j) − ℓ_j^{it}|² is at most 10m/((B+1)²+1) at each of the heights 0.5, 1, …, 100; for the primes 2 and 3 on the Subject 1549, B = 4, the bound is 10/13 and the smallest sum is at most 0.01 at each of these heights; the polynomial of the proof and the distinct monomials in exact integers",
            ok and ok2, detail, kind="[approx]")
    ok, count = label_cases()
    # 20:D19 (p20119)
    check("D19", "the value of a mode at one label: for every label ℓ ≥ 2 of the windows of the Subjects 13, 173 and 1549, every nonzero residue is ℓ^k g^r with r < V, at the largest M with ℓ^M < p and the least V with MV ≥ p − 1; for the label 3 on the Subject 1549, M = 6 and V = 258, and the powers of 3 stand 6 places apart",
            ok, f"{count} labels on three Subjects")


# ======================================================================================================================
# blocks G and X: the count readout and the classical statements (20:G2, G3, G5–G7, G9, G10, G12–G14, X1–X3; the revision of
# 21 November 2026, the critical circle's rows G13 and G14 on 22 November), on the laboratory pairs (13, 233), (173, 30089), (1549, 2408561). One check per row. A check is the
# conjunction of the theorems of the row's Lean cell (lean/FrcCore/Theme/Count.lean and Theme/Circle.lean, and the horizon theme's zero-slot and
# half), each computed by the count section's function of the same name and held once per pair in count_facts.
# A statement with a generator runs on every generator of 13 and 173 and on the least three of 1549 (the cardinal modes on
# the least one). A statement without a generator runs on the Carrier's chart too: in full on 233, and on 30089 and 2408561
# in full or on the ranges that count_facts names.
def conic_count(p, kap):
    """Under X = 2ρ − 1 and Y = 2a the circle's relation a² = ρ(1 − ρ) is the conic X² + Y² = 1. Its count is the classical
    one the paper cites, with no Lean declaration: p − 1 points on the shell. Two have Y = 0, at ρ = 0 and ρ = 1. The others
    come in pairs ±Y, one pair for each of the 2κ − 1 zeros ρ ≠ 0, 1 with ρ(1 − ρ) a square."""
    roots, h = {}, pow(2, p - 2, p)
    for y in range(p): roots.setdefault(y * y % p, []).append(y)
    pts = [(x, y) for x in range(p) for y in roots.get((1 - x * x) % p, [])]
    zeros = {(x + 1) * h % p for x, y in pts if y}
    squares = {y * y % p for y in range(1, p)}
    return (len(pts) == p - 1 and sorted((x + 1) * h % p for x, y in pts if y == 0) == [0, 1]
            and all(((y * h) ** 2 - (x + 1) * h * (1 - (x + 1) * h)) % p == 0 for x, y in pts)
            and len(pts) - 2 == 2 * len(zeros) and len(zeros) == 2 * kap - 1
            and zeros == {r for r in range(2, p) if r * (1 - r) % p in squares})


@lru_cache(maxsize=None)
def count_facts(p, Om):
    """The count theme's statements on the pair (p, Ω): theorem name -> verdict; with them the generators and the vector pairs read."""
    kap, S = (p - 1) // 4, (Om - 1) // 4
    gs = CT.generators(p) if p < 1000 else CT.generators(p)[:3]
    P = CT.gram_table(p)
    if p < 1000: vecs = [(("delta", y), CT.delta(p, y)) for y in range(1, p)]                # every indicator
    else: vecs = [(("delta", y), CT.delta(p, y)) for y in (1, 2, 3, 2 * kap, 2 * kap + 1, p - 2, p - 1)] + [(("sequence", s), CT.fixed_sequence(p, s)) for s in (1, 2, 3)]
    pairs = [(a, b) for a in vecs for b in vecs]
    near = [0, 1, 2, S, 2 * S, 2 * S + 1, Om - 2, Om - 1]                                    # the Carrier's residues tried where the full range is out of reach
    affine = None if Om < 1000 else [(a, b) for a in near for b in near]
    return {
        "generators": len(gs), "pairs": len(pairs),
        "zero_slot": P[0] == p - 1 and all(P[k] == 0 for k in range(1, p - 1)),
        "half_inverse": 2 * (2 * kap + 1) % p == 1 and (2 * kap + 1 + 2 * kap) % p == 0 and 2 * (2 * S + 1) % Om == 1 and (2 * S + 1 + 2 * S) % Om == 0,
        "half_unique": CT.half_unique(p, kap) and CT.half_unique(Om, S),
        "count_conjugate": CT.count_conjugate(p) and CT.count_conjugate(Om),
        "count_adjoint": CT.count_adjoint(p, P, direct=p < 100) and (p < 100 or CT.gram_rows(p, P, (1, 2, 2 * kap, p - 2))),
        "count_adjoint_vector": CT.count_adjoint_vector(p, pairs),
        "half_forced": CT.half_forced(p) and CT.half_forced(Om),
        "count_run": CT.count_run(p, list(range(6)) + [p - 2, p - 1, p, 2 * p + 3]) and CT.count_run(Om, [0, 1, 2, Om - 1], None if Om < 10 ** 5 else near),
        "count_run_only": CT.count_run_only(p, [0, 1, 2] if p > 1000 else [0, 1, 2, 3, 7]) and (Om > 1000 or CT.count_run_only(Om, [0, 1, 2])),
        "zero_count": all(CT.zero_count(p, kap, g) for g in gs),
        "zeros_fill": CT.zeros_fill(p) and (CT.zeros_fill(Om) if Om < 10 ** 5 else CT.zeros_fill_ends(Om)),
        "zero_conjugate": all(CT.zero_conjugate(p, kap, g) for g in gs),
        "constant_frequency": all((-CT.frequency(p, kap, CT.quarter_turn(p, kap, g), 0)) % p not in {CT.frequency(p, kap, CT.quarter_turn(p, kap, g), k) for k in range(p - 1)} for g in gs),
        "generator_skew": all(CT.generator_skew(p, kap, g, P) for g in gs),
        "centre_mode": all(CT.centre_mode(p, kap, g) for g in gs),
        "pair_invariant": all(CT.pair_invariant(p, kap, g) for g in gs),
        "energy_order": CT.energy_order(p, kap),
        "cardinal_modes": all(CT.cardinal_modes(p, kap, g) for g in (gs if p < 1000 else gs[:1])),
        "cardinal_zeros": CT.cardinal_zeros(p, kap) and CT.cardinal_zeros(Om, S),
        "carrier_centre": CT.carrier_centre(p, kap) and CT.carrier_centre(Om, S),
        "origin_unit_symmetry": CT.origin_unit_symmetry(p) and CT.origin_unit_symmetry(Om, affine),
        "zero_shared": CT.zero_shared(p, Om),
        "circle_pair": all(CT.circle_pair(p, g) for g in gs),
        "circle_frequency": all(CT.circle_frequency(p, kap, g) for g in gs),
        "circle_meridians": all(CT.circle_meridians(p, kap, g) for g in gs),
        "circle_point": all(CT.circle_point(p, g) for g in gs),
        "circle_count": all(CT.circle_count(p, kap, g) for g in gs),
        "circle_counts": all(CT.circle_counts(p, kap, g) for g in gs),
        "circle_conic": conic_count(p, kap),
        "circle_place": CT.circle_place(p),
        "circle_place_cycle": all(CT.circle_place_cycle(p, kap, g) for g in gs),
        "circle_place_even": all(CT.circle_place_even(p, kap, g) for g in gs),
        "circle_quarter_turn": all(CT.circle_quarter_turn(p, kap, g) for g in gs),
        "circle_phase": all(CT.circle_phase(p, g) for g in (gs if p < 1000 else gs[:1])),
        "circle_parallels": all(CT.circle_parallels(p, kap, g) for g in (gs if p < 1000 else gs[:1])),
        "circle_place_phase": all(CT.circle_place_phase(p, g) for g in gs),
        "circle_quarter_closes": CT.circle_quarter_closes(p),
    }


def block_G():
    """Block G — the count readout: 30 exact checks, ten rows on the three laboratory pairs."""
    print("\n== block G: the count readout ==")
    for p, Om in PAIRS:
        f = count_facts(p, Om); kap, S = (p - 1) // 4, (Om - 1) // 4
        read = f"{f['generators']} generators" if p < 1000 else f"the least {f['generators']} generators"
        # 20:G2 (p20097)
        check("G2", f"the count operator on F_{p}: a count k ≥ 1 and its conjugate add to −1, on the chart of F_{Om} too; (k + m + 1)⟨x^k, x^m⟩ = 0 for every mode k ≥ 1 and every mode m; ⟨Nv, w⟩ + ⟨v, Nw⟩ + ⟨v, w⟩ = −c₀d₀ on {f['pairs']} pairs of vectors",
                f["count_conjugate"] and f["count_adjoint"] and f["count_adjoint_vector"],
                "every pair of indicators of a residue" if p < 1000 else "seven indicators and three fixed sequences, every pair")
        # 20:G3 (p20098)
        check("G3", f"the half is forced on F_{p}: N + c is skew on the nonconstant modes exactly when 2c ≡ 1, for every residue c, on the chart of F_{Om} too; the run of counts from m(p − 1) asks for 2c ≡ 2m + 1, and so does the run one above; a run from any other start has no such c",
                f["half_forced"] and f["count_run"] and f["count_run_only"], f"2⁻¹ = {2 * kap + 1}; every start of a run for m = 0, 1, 2" + ("" if p > 1000 else ", 3, 7"))
        # 20:G5 (p20100)
        check("G5", f"the generator H = −i(N + 2⁻¹) on F_{p}: (γ_k + γ_m)⟨x^k, x^m⟩ = 0 unless both modes are constant; the conjugate of a nonconstant mode has the frequency −γ_k, and −γ_0 is the frequency of no mode",
                f["generator_skew"] and f["zero_conjugate"] and f["constant_frequency"], read)
        # 20:G6 (p20101)
        check("G6", f"the zeros on F_{p}: 2⁻¹ + iγ_k = k + 1; the zeros of the nonconstant modes are the residues other than 0 and 1, on the chart of F_{Om} too; the conjugate mode has the zero 1 − ρ_k; x ↦ 1 − x is the one affine map besides the identity that keeps the pair of origin and unit",
                f["zero_count"] and f["zeros_fill"] and f["zero_conjugate"] and f["origin_unit_symmetry"], f"{read}; every affine map of F_{p}")
        # 20:G7 (p20102)
        check("G7", f"the centre on F_{p}: the mode of count π = {2 * kap} is its own conjugate; its zero is 2⁻¹ = 2κ + 1 = −π = {2 * kap + 1}, the one residue with 2x ≡ 1 and the one fixed point of x ↦ 1 − x; its frequency is 0 and no other mode's; ρ(1 − ρ) = 2⁻² + γ² = −k(k + 1) for a count and its conjugate",
                f["centre_mode"] and f["pair_invariant"] and f["half_inverse"] and f["half_unique"] and f["origin_unit_symmetry"], read)
        # 20:G9 (p20104)
        check("G9", f"the order of the zeros on F_{p}: the counts π − j and π + j are conjugate, with their zeros at 2⁻¹ − j and 2⁻¹ + j; the smaller count π − j falls from π = {2 * kap} to 1 as j runs from 0 to π − 1",
                f["energy_order"] and f["pair_invariant"], f"{2 * kap} pairs")
        # 20:G10 (p20105)
        check("G10", f"the cardinal modes on F_{p}: a mode has all its values in {{1, i, −1, −i}} exactly when its count is 0, κ, 2κ or 3κ; these modes stand at 1, 3·4⁻¹, 2⁻¹, 4⁻¹ = 1, {kap + 1}, {2 * kap + 1}, {3 * kap + 1}",
                f["cardinal_modes"] and f["cardinal_zeros"], read if p < 1000 else "the least generator")
        # 20:G12 (p20107)
        check("G12", f"the chart of the Carrier F_{Om}, with no generator: the conjugate of a count 1 ≤ k ≤ Ω − 2 is Ω − 1 − k and the two add to −1; the centre of the zeros is 2⁻¹ = 2S + 1 = −G = {2 * S + 1}, with G = 2S; the counts 0, S, 2S, 3S stand at 1, 3·4⁻¹, 2⁻¹, 4⁻¹; every zero of the Subject F_{p} is the same integer there, and its constant mode stands at 1 on both",
                f["carrier_centre"] and f["cardinal_zeros"] and f["count_conjugate"] and f["zero_shared"], f"S = {S}; every count 1 … Ω − 2 of the chart")
        # 20:G13 (p20111)
        check("G13", f"the critical circle on F_{p}: a point a·g^m of the sphere and its mirror a·g^−m represent a zero and the zero of the conjugate mode exactly when a(g^m + g^−m) = 1, with a² = ρ(1 − ρ), and the two zeros differ by 2iγ_k; one point at each phase below π but κ, none on the momentum meridian or at the origin, the centre 2⁻¹ = {2 * kap + 1} alone on the prime meridian; a zero has a point exactly when ρ(1 − ρ) is a square, and then one: {2 * kap - 1} points with distinct zeros; under X = 2ρ − 1, Y = 2a the relation a² = ρ(1 − ρ) is the conic X² + Y² = 1, with its classical count of {p - 1} points, two at a = 0 and the others in pairs ±a on those zeros; the points with a(g^m + g^−m) = d are the circle with its positions multiplied by d, and the sum 0 is the momentum meridian with the origin; the half-turn of the drive gives the points with the sum −1, which carry the counts, π = {2 * kap} on the prime meridian, and share no point with the circle",
                f["circle_pair"] and f["circle_frequency"] and f["circle_meridians"] and f["circle_point"] and f["circle_count"] and f["circle_counts"] and f["circle_conic"] and f["circle_phase"] and f["circle_parallels"],
                read if p < 1000 else f"{read}; the parallels and the phases on the least generator")
        # 20:G14 (p20115)
        check("G14", f"the zeros on the latitude cycle of F_{p}: every zero is z/(1 + z) for one z = ρ/(1 − ρ) ≠ 0, −1; with z = g^j the {p - 2} zeros stand at the places j ≠ π of C_{p - 1}, the centre at the place 0 and the conjugate zero at −j; the point of the sphere on the circle at the phase m is the even place 2m; 2ρ − 1 = (z − 1)/(z + 1); the map x ↦ (x − 1)/(x + 1) has the square x ↦ −1/x, four steps return x where they are defined, and its fixed points are ±i",
                f["circle_place"] and f["circle_place_cycle"] and f["circle_place_even"] and f["circle_quarter_turn"] and f["circle_place_phase"] and f["circle_quarter_closes"], read)


def block_X():
    """Block X — the classical statements on the shell: 9 exact checks, three rows on the three laboratory pairs."""
    print("\n== block X: the classical statements ==")
    for p, Om in PAIRS:
        f = count_facts(p, Om); kap, S = (p - 1) // 4, (Om - 1) // 4
        # 20:X1 (p20108)
        check("X1", f"the ½ of the critical line on the pair ({p}, {Om}): the centre of the zeros is the inverse of 2, which is −π = {2 * kap + 1} on the Subject and −G = {2 * S + 1} on the Carrier's chart",
                f["half_inverse"] and f["carrier_centre"], f"π = {2 * kap}, G = {2 * S}")
        # 20:X2 (p20109)
        check("X2", f"the pole and the functional equation on F_{p}: Z_p vanishes at every nonconstant mode and is −1 at the constant mode, which stands at 1 and is no zero; a mode and its conjugate have the zeros ρ and 1 − ρ, and x ↦ 1 − x is the symmetry of origin and unit",
                f["zero_slot"] and f["zero_conjugate"] and f["origin_unit_symmetry"])
        # 20:X3 (p20110)
        check("X3", f"the ½ of the dilation generator on F_{p}: the shift that makes the count operator skew on the nonconstant modes is forced, 2c ≡ 1; with H = −i(N + 2⁻¹), (γ_k + γ_m)⟨x^k, x^m⟩ = 0 unless both modes are constant",
                f["half_forced"] and f["generator_skew"], f"2⁻¹ = {2 * kap + 1}")


if __name__ == "__main__":
    want = [a.upper() for a in sys.argv[1:]] or sorted(BLOCK)
    bad = [b for b in want if b not in BLOCK]
    if bad: sys.exit(f"no block {', '.join(bad)}: the blocks are {', '.join(sorted(BLOCK))}")
    t0 = time.time()
    for b in want:
        t = time.time(); _run_block(b); print(f"    [block {b}: {time.time() - t:.0f} s]")
    ok = summary(write=(want == sorted(BLOCK)))
    kinds = {}
    for r in RESULTS: kinds[r["kind"]] = kinds.get(r["kind"], 0) + 1
    print("by kind: " + ", ".join(f"{k} {v}" for k, v in sorted(kinds.items())) + f"; {len(RESULTS)} checks in {time.time() - t0:.0f} s" + ("; results.json written" if want == sorted(BLOCK) else ""))
    sys.exit(0 if ok else 1)
