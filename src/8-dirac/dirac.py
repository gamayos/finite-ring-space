"""
dirac.py — the validation package of "Schrödinger and Dirac Dynamics over Finite Substrate" (Akhtman, 2026; Preprints
doi 10.20944/preprints202510.1486.v2), the paper 8-dirac of the FRC corpus (finite-ring-space/src/8-dirac), added with the
paper's predicate ledger (13 September 2026); one script since 24 September 2026 (the registry dcommon.py, the library
finite_checks.py and the eight block scripts merged).
========================================================================================================================

One script, eight blocks, 52 family checks over 3 848 exact micro-checks, standard library only. Every check is exact
integer arithmetic over F_p and K = F_p[w]/(w² − ν): no floats, no random sampling. A family is the labelled claim of a
block (fin.S1, o2.C3i, o8.X7, …), one check of the registry, identified as <block>.<family>, and names the predicate(s) of
the paper's ledger it witnesses (LEDGER; predicates cited as 8:<label>) — the deciding family's `# 8:<label> (<key>)`
marker is what the ledger's source column links (PREDICATES; finitering.space/src/8-dirac/#<key>); the family
checks are listed on the public page from results.json. Where a predicate is proved in Lean (lean/FrcCore/Dirac.lean with
no axioms, lean/FrcLedger/Dirac.lean on Mathlib), the check here is the instance the reader can run. Master-ledger
predicates reached through the paper predicates: 00:C3 (8:B4), 00:C8 (8:B5, 8:B6), 00:B10 (8:B5).

    python3 dirac.py              every block, results.json written; exit 1 if a family check fails (≈ 1 min)
    python3 dirac.py o8 lat       the named blocks; no results.json
    from frc_8_dirac import predicate; predicate("8:D9")    one predicate: its block runs once per session

Blocks:  fin    the F_13 worked examples (the paper's p = 13 computations)      fin.S1–S3
         shell  the free evolution is the drive; the F_17 numbers               shell.Z1–Z4
         o2     the canonical Lorentzian coefficient ν = g                      o2.C1–C9
         o7     the parity grading and the factorisation ν = c²·(2g)            o7.P1–P6
         o134   boost torus, Cayley transform, orbit periods                    o134.O1a–O4d
         o8     symmetric Dirac dynamics and the spinor form                    o8.X1–X9
         lat    the latitude indices of the shell reading                       lat.L1–L5
         o9     signature as a square-class dichotomy                           o9.S1–S4

Kinds: every check is EXACT (integer-pinned computations in F_p, F_{p²} or exact rationals; a pass is a proof on the
tested instances).
"""
from __future__ import annotations
import os, json, sys
from collections import OrderedDict
from dataclasses import dataclass
from math import gcd, lcm

SCRIPT = os.path.splitext(os.path.basename(__file__))[0]        # "dirac": the one script, the name results.json and the site pages carry

# ----------------------------------------------------------------------------- registry
RESULTS = []           # one record per family check
MICRO = []             # (block, family, label, ok) — every micro-check

# check id -> the paper's predicate(s) it witnesses (the `rows` field of results.json)
LEDGER = {
    "fin.S1": "8:E2", "fin.S2": "8:C4, 8:C6, 8:E3", "fin.S3": "8:D2, 8:D6, 8:D7, 8:D8, 8:D12",
    "shell.Z1": "8:F3", "shell.Z2": "8:F3", "shell.Z3": "8:F4", "shell.Z4": "8:D5, 8:D12",
    "o2.C1": "8:B3", "o2.C2": "8:B2", "o2.C3i": "8:B3", "o2.C3a": "8:B3", "o2.C4": "8:B3", "o2.C5": "8:B3", "o2.C6": "8:D5",
    "o2.C7": "8:B4", "o2.C8": "8:B4, 8:D12", "o2.C9": "8:B4",
    "o7.P1": "8:B5", "o7.P2": "8:B4", "o7.P3": "8:B4", "o7.P4": "8:B5", "o7.P5": "8:B6", "o7.P6": "8:B6",
    "o134.O1a": "8:D5", "o134.O1b": "8:D5", "o134.O1c": "8:D5", "o134.O1d": "8:D5", "o134.O1e": "8:D12",
    "o134.O3a": "8:C5", "o134.O3b": "8:C5", "o134.O4a": "8:C6, 8:E4", "o134.O4b": "8:E4", "o134.O4c": "8:E4", "o134.O4d": "8:E4",
    "o8.X1": "8:D9", "o8.X2": "8:D9", "o8.X3": "8:D9", "o8.X4": "8:D9", "o8.X5": "8:D10", "o8.X6": "8:D10", "o8.X7": "8:F4", "o8.X8": "8:D11",
    "o8.X9": "8:F4",
    "lat.L1": "8:F2", "lat.L2": "8:F2", "lat.L3": "8:F2", "lat.L4": "8:F2", "lat.L5": "8:F2",
    "o9.S1": "8:B7", "o9.S2": "8:B7", "o9.S3": "8:B7", "o9.S4": "8:B7",
}

# check id -> the claim it decides (the family lines of the block banners, condensed)
LABELS = {
    "fin.S1": "power maps on F_13^×: image counts (p−1)/gcd(ε, p−1) and loss factors gcd(ε, p−1) for ε = 1, 2, 3, 4, 6, 12",
    "fin.S2": "Cayley step of H = −Δ on F_13 at α = c: U^13 = I; every trace-zero α = kc admissible with exact order 13 (k ≠ 0)",
    "fin.S3": "F_13 Dirac example: Clifford relations for η = diag(−2,1,1,1); S⁻¹γ^μS boost formulas; transported γ̂⁰ = 10γ⁰ − 4γ¹, γ̂¹ = −2γ⁰ + 10γ¹; A = 10, B = 2; covariance on a sample field",
    "shell.Z1": "the drive pullback is a permutation operator with D χ_k = g^{−k} χ_k on every character and cycle point (p = 13, 17)",
    "shell.Z2": "isotropy: ⟨χ_k, χ_k⟩ = 0 except k = 0, (p−1)/2 with eigenvalues ±1",
    "shell.Z3": "sector separation: ord(g⁻¹) = p − 1 > 2, the free evolution is no Cayley step of a Frobenius-fixed Hamiltonian",
    "shell.Z4": "F_17 example: i = 3^{−4} = 4, 2, i, e squares, g nonsquare; ν = 3, A = 15, B = 1, A² − νB² = 1; |G_3| = 18, |G_2| = 14; an order-3 boost at 17, none at 13",
    "o2.C1": "every primitive g is a nonsquare on every symmetry-complete shell p < 2000",
    "o2.C2": "the nonsquare class is unique: the product of two nonsquares is a square",
    "o2.C3i": "i = g^{−κ} is a square iff κ is even (8 | p − 1), on every symmetry-complete shell p < 2000",
    "o2.C3a": "2, 2⁻¹, −2 are squares iff κ is even: on κ-even shells g is the only named nonsquare",
    "o2.C4": "e = g^i has no stable square class (counterexamples both ways)",
    "o2.C5": "flip stability: [g⁻¹] = [g]",
    "o2.C6": "|G_ν| = p + 1 with ν = g, by exhaustive enumeration on small shells",
    "o2.C7": "F_13 anchor: g = 2 = ν, i = 5, 2⁻¹ = 7 nonsquare (κ odd, non-admissible)",
    "o2.C8": "F_17 anchor: 2, i = 4, e squares, only g = 3 nonsquare, |G_3| = 18",
    "o2.C9": "lab Carrier Ω = 2,408,561: g = 6 nonsquare; 2, 2⁻¹, −2, i = ħ = 18,688 squares; c = √(2⁻¹) = 171,106 base-rational",
    "o7.P1": "squares = ⟨g²⟩: the square class is the drive-step parity, exhaustive on every primitive g of F_13, F_17, Euler form on p < 2000",
    "o7.P2": "ν = c² · (2g) exactly (2c² = 1); lab-Carrier instance 1,204,281 · 12 = 6 = g",
    "o7.P3": "[c²] even iff κ even, [2g] odd iff κ even, the product odd on every shell",
    "o7.P4": "on κ-even shells every element of Q₄ = {1, i, −1, −i} is a square: the chart grading carries no signature",
    "o7.P5": "N(gx) = g² N(x), g² a square (registered transport even), g odd, x² = g unsolvable in F_p",
    "o7.P6": "gauge stability: dlog_g(g⁻¹) = −1 odd — the flip preserves the parity class",
    "o134.O1a": "kernel of (x, y) ↦ Λ(x, y) is the scalar line: p − 1 preimages per boost, |G_ν| = p + 1",
    "o134.O1b": "Hilbert 90: A − Bw = z/z̄, z F_p^× ↦ z/z̄ a bijection onto N¹",
    "o134.O1c": "G_ν is cyclic: an element of order p + 1 exists",
    "o134.O1d": "an order-3 boost exists iff 3 | p + 1 (17 yes, 13 no)",
    "o134.O1e": "F_17 is the minimal admissible shell: κ = 4 even, κ ≡ 1 (mod 3), p ≡ 5 (mod 12), no smaller symmetry-complete p",
    "o134.O3a": "the Cayley map φ(λ) = (1+aλ)/(1−aλ), a ∈ K⁻ nonzero, bijects P¹(F_p) onto N¹ with φ(∞) = −1",
    "o134.O3b": "the unitary group of one channel is N¹ = C_{p+1}",
    "o134.O4a": "kinetic case: H = −Δ nilpotent, U unipotent, ord(U) = p",
    "o134.O4b": "potential case: H = M_V diagonal, eigenphases in N¹, ord(U) = p + 1 (13 → 14, 17 → 18)",
    "o134.O4c": "mixed case: ord(U) = 1563 for H = −Δ + M_id at p = 5",
    "o134.O4d": "composite: the order of a block-diagonal pair is the lcm (13, 14 → 182)",
    "o8.X1": "plain adjoints: (γ⁰)† = −γ⁰, (γ¹)† = −γ¹, (γ²)† = +γ², (γ³)† = −γ³ (p = 5, 13, 17)",
    "o8.X2": "the spinor twist X = γ⁰γ¹γ³: Hermitian, X² = ν, commutes with γ⁰, γ¹, γ³, anticommutes with γ²; X⁻¹(γ^μ)†X = −γ^μ for all μ",
    "o8.X3": "the γ⁰-twist fails: signs remain mixed",
    "o8.X4": "T − T⁻¹ nilpotent and anti-self-adjoint; D^s X-self-adjoint and nilpotent",
    "o8.X5": "1+1 at p = 5: H = D^s X-self-adjoint, the Cayley step X-unitary, unipotent with ord(U) = 25 = p²",
    "o8.X6": "massive: H = D^s − mI, ord(U) = lcm(p-power, ord_{N¹} φ(−m)) for m = 1, 2 at p = 5",
    "o8.X7": "the cycle Laplacian Δ_Φ is self-adjoint, its Cayley steps commute with D, the composite is unitary (p = 13)",
    "o8.X8": "spin lift vs the spinor form: S(x,y)# = S(x,−y) = δS⁻¹; the transport scales the X-form by N(z), norm-one lifts preserve it",
    "o8.X9": "the dispersion relation on the cycle: −Δ_Φ χ_k = (2 − g^k − g^{−k}) χ_k for every k (F_13); D^s − m invertible for m ≠ 0",
    "lat.L1": "ladder bounds: the energy index κ + 1 is the first rung past the midpoint of the ladder 1 … 2κ",
    "lat.L2": "one shift, two ladders: m ↦ m + κ is multiplication by g^κ = ±i; a ↦ a + κ sends 1 ↦ κ + 1",
    "lat.L3": "κ = −4⁻¹, so the energy radius is 1 + κ = 3·4⁻¹",
    "lat.L4": "terminal latitude: π = 2κ = −2⁻¹ = −c²; on the Carrier π_Ω = 2S",
    "lat.L5": "chart consistency: the unit-norm circle has p − 1 points; the energy circle carries norm 9/16",
    "o9.S1": "the Euclidean form t² + x² + y² + z² has p³ + p² − p zeros on every symmetry-complete shell p < 60",
    "o9.S2": "the form −νt² + x² + y² + z², ν = g, has p³ − p² + p zeros",
    "o9.S3": "p = 13: the counts are 2353 and 2041",
    "o9.S4": "over F_{p²} every element of F_p is a square: the extension erases the dichotomy",
}

BLOCK = OrderedDict([      # check-id prefix -> the block (the function block_<name> below), in the run order
    ("fin", "the F_13 worked examples: power maps, the Cayley step of H = −Δ, the Dirac example (worked_checks over finite_checks until 24 September 2026)"),
    ("shell", "the free evolution is the drive; the F_17 numbers (shell_checks)"),
    ("o2", "the canonical Lorentzian coefficient ν = g (o2_checks)"),
    ("o7", "the parity grading and the factorisation ν = c²·(2g) (o7_checks)"),
    ("o134", "the boost torus, the Cayley transform and the orbit periods (o134_checks)"),
    ("o8", "symmetric Dirac dynamics and the spinor form (o8_checks)"),
    ("lat", "the latitude indices of the shell reading (latitude_checks)"),
    ("o9", "signature as a square-class dichotomy (o9_signature_counts)"),
])

# the deciding family of each witnessed predicate: the first check the ledger's source column names, the one whose verdict
# decides the predicate's statement (the other families that touch it are corroboration, listed by predicate() from the records)
PREDICATES = {
    "8:B2": "o2.C2",       "8:B3": "o2.C1",       "8:B4": "o7.P2",       "8:B5": "o7.P1",
    "8:B6": "o7.P5",       "8:B7": "o9.S1",       "8:C4": "fin.S2",      "8:C5": "o134.O3a",
    "8:C6": "fin.S2",      "8:D2": "fin.S3",      "8:D5": "o134.O1a",    "8:D6": "fin.S3",
    "8:D7": "fin.S3",      "8:D8": "fin.S3",      "8:D9": "o8.X1",       "8:D10": "o8.X5",
    "8:D11": "o8.X8",      "8:D12": "fin.S3",     "8:E2": "fin.S1",      "8:E3": "fin.S2",
    "8:E4": "o134.O4a",    "8:F2": "lat.L1",      "8:F3": "shell.Z1",    "8:F4": "shell.Z3",
}
_TAG = [None]
_RAN = set()                                            # blocks already run in this session (predicate() runs each once)

def check(pid, ok, detail="", kind="EXACT", label=None):
    """Record one family check. pid = <block>.<family>; LEDGER[pid] = the paper predicate(s) it witnesses."""
    ok = bool(ok)
    rows = LEDGER.get(pid, "")
    label = label or LABELS.get(pid, pid)
    RESULTS.append({"id": pid, "rows": rows, "block": pid.split(".")[0], "script": SCRIPT, "label": label, "ok": ok, "detail": detail, "kind": kind})
    print(f"  [{'PASS' if ok else 'FAIL'}] {pid:9s} {kind:5s} [{rows}] {label}" + (f"  --  {detail}" if detail else ""))
    return ok

def summary(write=True):
    n_ok = sum(r["ok"] for r in RESULTS)
    print(f"\nSUMMARY: {n_ok}/{len(RESULTS)} checks passed ({len(MICRO)} exact micro-checks)" + ("" if n_ok == len(RESULTS) else "  <-- FAILURES"))
    if write:
        with open("results.json", "w") as f:
            json.dump(RESULTS, f, indent=1, ensure_ascii=False)
    return n_ok == len(RESULTS)

def chk(label, ok, tag=None):
    """A micro-check: label = '<family> …' (the family is the first token); recorded under the current block, never exits."""
    fam = label.split()[0]
    MICRO.append((tag or _TAG[0] or "?", fam, label, bool(ok)))
    if not ok:
        print(f"    FAIL: {label}")

def begin(tag):
    _TAG[0] = tag

def flush(tag, order=None):
    """Aggregate the micro-checks of a block into one registry check per family."""
    fams = OrderedDict()
    for t, fam, label, ok in MICRO:
        if t == tag:
            fams.setdefault(fam, []).append(ok)
    for fam in (order or fams):
        oks = fams.get(fam, [])
        check(f"{tag}.{fam}", ok=bool(oks) and all(oks), detail=f"{len(oks)} exact micro-checks")
    _TAG[0] = None

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
    for b in [b for b in BLOCK if b in {fam.split(".")[0]} | citing]: _run_block(b)     # the deciding block and every block whose families cite the predicate, in the run order
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
        print(f"  [{'PASS' if r['ok'] else 'FAIL'}] {r['id']:9s} {role:16s} {r['detail']}")
    print(f"{label}: {'VERIFIED' if ok and recs else 'FAILED'} — {len(recs)} family record(s)")
    return ok

def verify_all():
    """Run every block (those already run in this session are not re-run) and print the summary; True iff every family check passed."""
    for b in BLOCK: _run_block(b)
    return summary(write=False)

# ------------------------------------------------------------------------------------------------------------
# the F_13 library (finite_checks.py until 24 September 2026): the paper's p = 13 computations, kept verbatim —
# the coefficient field F_13[w]/(w² − 2) as pairs, the matrix and field-map arithmetic, and the three printing
# checks power_map_counts(), schrodinger_check(), dirac_check() of the manuscript's examples (callable; block fin
# turns their arithmetic into registered checks).
#
# Exact finite checks for the FRC Schrodinger-Dirac manuscript.
#
# This script reproduces the p=13 computations stated in the manuscript:
# 1. image counts and loss factors for power maps on F_p^x,
# 2. the Cayley admissibility set and propagator orders for the Euclidean Schrodinger example,
# 3. the Clifford relations, transported gamma formulas, and explicit boost covariance for the Dirac example.

P = 13
NU = 2

def mod_inv(a: int, p: int = P) -> int:
    return pow(a % p, -1, p)

def find_square_root(value: int, p: int = P) -> int:
    value %= p
    for x in range(p):
        if (x * x) % p == value:
            return x
    raise ValueError(f"no square root of {value} in F_{p}")

G = 2  # the frame's drive multiplier, F_13(t;0,1,2); nu = g is canonical
KAP = (P - 1) // 4
IT = pow(pow(G, P - 2, P), KAP, P)  # derived orientation i = g^{-kappa} = 5
assert IT == 5 and (IT * IT) % P == P - 1

@dataclass(frozen=True)
class Fp2:
    a: int
    b: int

    def __post_init__(self) -> None:
        object.__setattr__(self, "a", self.a % P)
        object.__setattr__(self, "b", self.b % P)

    def __add__(self, other: "Fp2") -> "Fp2":
        return Fp2(self.a + other.a, self.b + other.b)

    def __sub__(self, other: "Fp2") -> "Fp2":
        return Fp2(self.a - other.a, self.b - other.b)

    def __neg__(self) -> "Fp2":
        return Fp2(-self.a, -self.b)

    def __mul__(self, other: "Fp2") -> "Fp2":
        return Fp2(self.a * other.a + NU * self.b * other.b, self.a * other.b + self.b * other.a)

    def conj(self) -> "Fp2":
        return Fp2(self.a, -self.b)

    def norm(self) -> int:
        return (self.a * self.a - NU * self.b * self.b) % P

    def inv(self) -> "Fp2":
        n = self.norm()
        ninv = mod_inv(n, P)
        z = self.conj()
        return Fp2(z.a * ninv, z.b * ninv)

    def __truediv__(self, other: "Fp2") -> "Fp2":
        return self * other.inv()

    def __pow__(self, exponent: int) -> "Fp2":
        if exponent < 0:
            return (self.inv()) ** (-exponent)
        result = ONE
        base = self
        e = exponent
        while e:
            if e & 1:
                result = result * base
            base = base * base
            e >>= 1
        return result

    def is_zero(self) -> bool:
        return self.a == 0 and self.b == 0

    def __repr__(self) -> str:
        return f"Fp2({self.a},{self.b})"

ZERO = Fp2(0, 0)
ONE = Fp2(1, 0)
C = Fp2(0, 1)
I_T = Fp2(IT, 0)

def scalar(x: int) -> Fp2:
    return Fp2(x, 0)

def zero_matrix(n: int, m: int) -> list[list[Fp2]]:
    return [[ZERO for _ in range(m)] for _ in range(n)]

def identity(n: int) -> list[list[Fp2]]:
    out = zero_matrix(n, n)
    for i in range(n):
        out[i][i] = ONE
    return out

def mat_add(a: list[list[Fp2]], b: list[list[Fp2]]) -> list[list[Fp2]]:
    return [[a[i][j] + b[i][j] for j in range(len(a[0]))] for i in range(len(a))]

def mat_sub(a: list[list[Fp2]], b: list[list[Fp2]]) -> list[list[Fp2]]:
    return [[a[i][j] - b[i][j] for j in range(len(a[0]))] for i in range(len(a))]

def scalar_mul(s: Fp2, a: list[list[Fp2]]) -> list[list[Fp2]]:
    return [[s * a[i][j] for j in range(len(a[0]))] for i in range(len(a))]

def mat_mul(a: list[list[Fp2]], b: list[list[Fp2]]) -> list[list[Fp2]]:
    n = len(a)
    m = len(b[0])
    k = len(b)
    out = zero_matrix(n, m)
    for i in range(n):
        for j in range(m):
            total = ZERO
            for t in range(k):
                total = total + a[i][t] * b[t][j]
            out[i][j] = total
    return out

def mat_pow(a: list[list[Fp2]], exponent: int) -> list[list[Fp2]]:
    result = identity(len(a))
    base = a
    e = exponent
    while e:
        if e & 1:
            result = mat_mul(result, base)
        base = mat_mul(base, base)
        e >>= 1
    return result

def mat_eq(a: list[list[Fp2]], b: list[list[Fp2]]) -> bool:
    return all(a[i][j] == b[i][j] for i in range(len(a)) for j in range(len(a[0])))

def mat_inv(a: list[list[Fp2]]) -> list[list[Fp2]]:
    n = len(a)
    aug = [row[:] + eye_row[:] for row, eye_row in zip(a, identity(n))]
    for col in range(n):
        pivot = None
        for row in range(col, n):
            if not aug[row][col].is_zero():
                pivot = row
                break
        if pivot is None:
            raise ValueError("matrix is singular")
        aug[col], aug[pivot] = aug[pivot], aug[col]
        inv_pivot = aug[col][col].inv()
        aug[col] = [inv_pivot * entry for entry in aug[col]]
        for row in range(n):
            if row == col:
                continue
            factor = aug[row][col]
            if factor.is_zero():
                continue
            aug[row] = [aug[row][j] - factor * aug[col][j] for j in range(2 * n)]
    return [row[n:] for row in aug]

def block_matrix(a: list[list[Fp2]], b: list[list[Fp2]], c: list[list[Fp2]], d: list[list[Fp2]]) -> list[list[Fp2]]:
    top = [ra + rb for ra, rb in zip(a, b)]
    bottom = [rc + rd for rc, rd in zip(c, d)]
    return top + bottom

def vec_zero(n: int) -> list[Fp2]:
    return [ZERO for _ in range(n)]

def vec_add(a: list[Fp2], b: list[Fp2]) -> list[Fp2]:
    return [x + y for x, y in zip(a, b)]

def vec_sub(a: list[Fp2], b: list[Fp2]) -> list[Fp2]:
    return [x - y for x, y in zip(a, b)]

def vec_is_zero(v: list[Fp2]) -> bool:
    return all(x.is_zero() for x in v)

def mat_vec_mul(a: list[list[Fp2]], v: list[Fp2]) -> list[Fp2]:
    out = vec_zero(len(a))
    for i in range(len(a)):
        total = ZERO
        for j in range(len(v)):
            total = total + a[i][j] * v[j]
        out[i] = total
    return out

def point_add(x: tuple[int, int, int, int], y: tuple[int, int, int, int]) -> tuple[int, int, int, int]:
    return tuple((x[i] + y[i]) % P for i in range(4))

def point_sub(x: tuple[int, int, int, int], y: tuple[int, int, int, int]) -> tuple[int, int, int, int]:
    return tuple((x[i] - y[i]) % P for i in range(4))

def int_mat_point_mul(a: list[list[int]], x: tuple[int, int, int, int]) -> tuple[int, int, int, int]:
    out: list[int] = []
    for row in a:
        total = 0
        for coeff, value in zip(row, x):
            total += coeff * value
        out.append(total % P)
    return tuple(out)  # type: ignore[return-value]

def canonical_field(field: dict[tuple[int, int, int, int], list[Fp2]]) -> dict[tuple[int, int, int, int], list[Fp2]]:
    return {point: value for point, value in field.items() if not vec_is_zero(value)}

def field_add(a: dict[tuple[int, int, int, int], list[Fp2]], b: dict[tuple[int, int, int, int], list[Fp2]]) -> dict[tuple[int, int, int, int], list[Fp2]]:
    out = {point: value[:] for point, value in a.items()}
    for point, value in b.items():
        out[point] = vec_add(out.get(point, vec_zero(4)), value)
    return canonical_field(out)

def diff_apply(field: dict[tuple[int, int, int, int], list[Fp2]], shift: tuple[int, int, int, int]) -> dict[tuple[int, int, int, int], list[Fp2]]:
    support = set(field)
    candidates = support | {point_sub(point, shift) for point in support}
    out: dict[tuple[int, int, int, int], list[Fp2]] = {}
    for point in candidates:
        forward = field.get(point_add(point, shift), vec_zero(4))
        current = field.get(point, vec_zero(4))
        out[point] = vec_sub(forward, current)
    return canonical_field(out)

def dirac_apply(
    field: dict[tuple[int, int, int, int], list[Fp2]],
    gamma_family: list[list[list[Fp2]]],
    frame: list[tuple[int, int, int, int]],
) -> dict[tuple[int, int, int, int], list[Fp2]]:
    out: dict[tuple[int, int, int, int], list[Fp2]] = {}
    for gamma, shift in zip(gamma_family, frame):
        diff = diff_apply(field, shift)
        transformed = {point: mat_vec_mul(gamma, value) for point, value in diff.items()}
        out = field_add(out, transformed)
    return canonical_field(out)

def transport_apply(
    field: dict[tuple[int, int, int, int], list[Fp2]],
    lambda_matrix: list[list[int]],
    spin_matrix: list[list[Fp2]],
) -> dict[tuple[int, int, int, int], list[Fp2]]:
    out: dict[tuple[int, int, int, int], list[Fp2]] = {}
    for point, value in field.items():
        target = int_mat_point_mul(lambda_matrix, point)
        out[target] = mat_vec_mul(spin_matrix, value)
    return canonical_field(out)

def field_eq(
    a: dict[tuple[int, int, int, int], list[Fp2]],
    b: dict[tuple[int, int, int, int], list[Fp2]],
) -> bool:
    return canonical_field(a) == canonical_field(b)

def power_map_counts() -> None:
    print("Power map counts on F_p^x")
    for epsilon in [1, 2, 3, 4, 6, 12]:
        image = {pow(x, epsilon, P) for x in range(1, P)}
        loss = (P - 1) / len(image)
        print(
            f"  epsilon={epsilon:2d}: image_size={len(image):2d}, "
            f"formula={(P - 1) // gcd(epsilon, P - 1):2d}, loss_factor={int(loss):2d}"
        )

def schrodinger_check() -> None:
    n = P
    eye = identity(n)
    shift = zero_matrix(n, n)
    shift_inv = zero_matrix(n, n)
    for j in range(n):
        shift[(j - 1) % n][j] = ONE
        shift_inv[(j + 1) % n][j] = ONE
    delta = mat_sub(mat_add(shift, shift_inv), scalar_mul(scalar(2), eye))
    hamiltonian = scalar_mul(scalar(-1), delta)
    left = mat_sub(eye, scalar_mul(C, hamiltonian))
    right = mat_add(eye, scalar_mul(C, hamiltonian))
    cayley = mat_mul(mat_inv(left), right)
    u13 = mat_pow(cayley, 13)
    print("Schrodinger check")
    print(f"  det-denominator-invertible = {True}")
    print(f"  U^13 = I                 = {mat_eq(u13, eye)}")
    print("  admissible alpha=k*c and exact orders")

    def cayley_for(k: int) -> list[list[Fp2]]:
        alpha = Fp2(0, k)
        left_k = mat_sub(eye, scalar_mul(alpha, hamiltonian))
        right_k = mat_add(eye, scalar_mul(alpha, hamiltonian))
        return mat_mul(mat_inv(left_k), right_k)

    def matrix_order(matrix: list[list[Fp2]], bound: int = 5000) -> int:
        current = identity(len(matrix))
        for exponent in range(1, bound + 1):
            current = mat_mul(current, matrix)
            if mat_eq(current, eye):
                return exponent
        raise ValueError("order search failed")

    for k in range(P):
        try:
            u_k = cayley_for(k)
            print(f"    k={k:2d}: admissible=True, order={matrix_order(u_k)}")
        except ValueError:
            print(f"    k={k:2d}: admissible=False, order=NA")

def gamma_matrices() -> tuple[list[list[Fp2]], list[list[Fp2]], list[list[Fp2]], list[list[Fp2]]]:
    i2 = [[ONE, ZERO], [ZERO, ONE]]
    sigma1 = [[ZERO, ONE], [ONE, ZERO]]
    sigma2 = [[ZERO, -I_T], [I_T, ZERO]]
    sigma3 = [[ONE, ZERO], [ZERO, -ONE]]
    zero2 = [[ZERO, ZERO], [ZERO, ZERO]]
    beta = block_matrix(zero2, i2, i2, zero2)
    rho1 = block_matrix(zero2, sigma1, scalar_mul(Fp2(-1, 0), sigma1), zero2)
    rho2 = block_matrix(zero2, sigma2, scalar_mul(Fp2(-1, 0), sigma2), zero2)
    rho3 = block_matrix(zero2, sigma3, scalar_mul(Fp2(-1, 0), sigma3), zero2)
    gamma0 = scalar_mul(I_T * C, beta)
    gamma1 = scalar_mul(I_T, rho1)
    gamma2 = scalar_mul(I_T, rho2)
    gamma3 = scalar_mul(I_T, rho3)
    return gamma0, gamma1, gamma2, gamma3

def anticommutator(a: list[list[Fp2]], b: list[list[Fp2]]) -> list[list[Fp2]]:
    return mat_add(mat_mul(a, b), mat_mul(b, a))

def dirac_check() -> None:
    gamma0, gamma1, gamma2, gamma3 = gamma_matrices()
    eta = [-NU, 1, 1, 1]
    gammas = [gamma0, gamma1, gamma2, gamma3]
    ok = True
    for mu in range(4):
        for nu in range(4):
            lhs = anticommutator(gammas[mu], gammas[nu])
            rhs = zero_matrix(4, 4)
            coeff = scalar(2 * eta[mu] if mu == nu else 0)
            for i in range(4):
                rhs[i][i] = coeff
            ok = ok and mat_eq(lhs, rhs)

    x = scalar(1)
    y = scalar(1)
    delta = scalar(1 - NU)
    delta_inv = delta.inv()
    m = mat_mul(gamma0, gamma1)
    s = mat_add(identity(4), m)
    s_inv = scalar_mul(delta_inv, mat_sub(identity(4), m))

    a_coeff = scalar(1 + NU) / scalar(1 - NU)
    b_coeff = scalar(-2) / scalar(1 - NU)

    lhs0 = mat_mul(mat_mul(s_inv, gamma0), s)
    rhs0 = mat_add(scalar_mul(a_coeff, gamma0), scalar_mul(scalar(NU) * b_coeff, gamma1))

    lhs1 = mat_mul(mat_mul(s_inv, gamma1), s)
    rhs1 = mat_add(scalar_mul(b_coeff, gamma0), scalar_mul(a_coeff, gamma1))

    transported0 = mat_mul(mat_mul(s, gamma0), s_inv)
    transported1 = mat_mul(mat_mul(s, gamma1), s_inv)
    rhs0_transport = mat_add(scalar_mul(a_coeff, gamma0), scalar_mul(-scalar(NU) * b_coeff, gamma1))
    rhs1_transport = mat_add(scalar_mul(-b_coeff, gamma0), scalar_mul(a_coeff, gamma1))

    a_int = a_coeff.a
    b_int = b_coeff.a
    lambda_matrix = [
        [a_int, b_int, 0, 0],
        [(NU * b_int) % P, a_int, 0, 0],
        [0, 0, 1, 0],
        [0, 0, 0, 1],
    ]
    boosted_frame = [
        (a_int, (NU * b_int) % P, 0, 0),
        (b_int, a_int, 0, 0),
        (0, 0, 1, 0),
        (0, 0, 0, 1),
    ]
    sample_field = {
        (0, 0, 0, 0): [ONE, C, ZERO, scalar(2)],
        (1, 2, 0, 0): [scalar(3), ZERO, I_T, ONE],
        (5, 0, 1, 0): [ZERO, scalar(4), C, scalar(7)],
    }
    transported_gammas = [transported0, transported1, gamma2, gamma3]
    standard_frame = [
        (1, 0, 0, 0),
        (0, 1, 0, 0),
        (0, 0, 1, 0),
        (0, 0, 0, 1),
    ]
    lhs_covariance = dirac_apply(
        transport_apply(sample_field, lambda_matrix, s),
        transported_gammas,
        boosted_frame,
    )
    rhs_covariance = transport_apply(
        dirac_apply(sample_field, gammas, standard_frame),
        lambda_matrix,
        s,
    )

    print("Dirac check")
    print(f"  Clifford relations       = {ok}")
    print(f"  boost formula gamma^0    = {mat_eq(lhs0, rhs0)}")
    print(f"  boost formula gamma^1    = {mat_eq(lhs1, rhs1)}")
    print(f"  transported gamma^0      = {mat_eq(transported0, rhs0_transport)}")
    print(f"  transported gamma^1      = {mat_eq(transported1, rhs1_transport)}")
    print(f"  covariance sample check  = {field_eq(lhs_covariance, rhs_covariance)}")
    print(f"  A coefficient            = {a_coeff}")
    print(f"  B coefficient            = {b_coeff}")

# ------------------------------------------------------------------------------------------------------------
# block fin — the F_13 worked examples (worked_checks over finite_checks until 24 September 2026)
#
# The F_13 worked examples as registered checks (EXACT).
#
# Drives finite_checks.py (the paper's p = 13 computations, kept verbatim as the library) and turns its printed
# booleans into predicates:
#
#   S1  Power-map counts on F_13^× (Prop. power-map-count): image size (p−1)/gcd(ε, p−1) and loss factor
#       gcd(ε, p−1) for ε = 1, 2, 3, 4, 6, 12; each nonempty fibre of size gcd.
#   S2  The Euclidean Schrödinger example (Example cayley-13, Thm. cayley-preservation, Cor. finite periodicity,
#       Thm. period-dichotomy): H = −Δ on F_13, α = c: U^13 = I; every trace-zero α = kc is admissible
#       (H nilpotent), with exact order 13 for k ≠ 0 and 1 for k = 0; U is unitary for the Hermitian form.
#   S3  The Dirac example (Example dirac-13; Prop. clifford, Prop. spin-conjugation, Prop. transported-dirac-form,
#       Cor. boost-covariance): Clifford relations with η = diag(−2, 1, 1, 1); the boost formulas S⁻¹γ⁰S =
#       Aγ⁰ + νBγ¹, S⁻¹γ¹S = Bγ⁰ + Aγ¹; the transported γ̂⁰ = Aγ⁰ − νBγ¹, γ̂¹ = −Bγ⁰ + Aγ¹ with A = 10, B = 2;
#       the covariance identity D_{Λ,S} T ψ = T D_{E0} ψ on a sample field.
def block_fin():
    """Block fin — the F_13 worked examples as registered checks (EXACT): fin.S1–S3."""
    # S1 — power maps
    ok = True
    # 8:E2 (p08035)
    for eps in (1, 2, 3, 4, 6, 12):
        image = {pow(x, eps, P) for x in range(1, P)}
        d = gcd(eps, P - 1)
        ok &= (len(image) == (P - 1) // d) and all(sum(1 for x in range(1, P) if pow(x, eps, P) == y) == d for y in image)
    check("fin.S1", ok, "ε = 1, 2, 3, 4, 6, 12 on F_13^×; fibres of size gcd(ε, 12)")

    # S2 — the Schrödinger example
    n = P
    eye = identity(n)
    shift, shift_inv = zero_matrix(n, n), zero_matrix(n, n)
    for j in range(n):
        shift[(j - 1) % n][j] = ONE; shift_inv[(j + 1) % n][j] = ONE
    delta = mat_sub(mat_add(shift, shift_inv), scalar_mul(scalar(2), eye))
    H = scalar_mul(scalar(-1), delta)
    def cayley_for(alpha):
        return mat_mul(mat_inv(mat_sub(eye, scalar_mul(alpha, H))), mat_add(eye, scalar_mul(alpha, H)))
    def order(M, bound=200):
        cur = identity(n)
        for e in range(1, bound + 1):
            cur = mat_mul(cur, M)
            if mat_eq(cur, eye): return e
        return None
    # 8:C6 (p08020), 8:E3 (p08036)
    U = cayley_for(C)
    ok = mat_eq(mat_pow(U, 13), eye)
    orders = {}
    for k in range(P):
        try:
            Uk = cayley_for(Fp2(0, k)); orders[k] = order(Uk)
        except ValueError:
            orders[k] = None
    ok &= all(orders[k] == 13 for k in range(1, P)) and orders[0] == 1
    # unitarity: U^† U = I with the conjugate-transpose over K = F_13[w]/(w²−2), conj(a + bw) = a − bw
    def dagger(M):
        return [[Fp2(M[j][i].a, (-M[j][i].b) % P) for j in range(n)] for i in range(n)]
    # 8:C4 (p08018)
    ok &= mat_eq(mat_mul(dagger(U), U), eye)
    check("fin.S2", ok, f"U^13 = I; orders {sorted(set(orders.values()))}; U†U = I")

    # S3 — the Dirac example
    g0, g1, g2, g3 = gamma_matrices()
    gammas = [g0, g1, g2, g3]; eta = [-NU, 1, 1, 1]
    ok = True
    # 8:D2 (p08022)
    for mu in range(4):
        for nu in range(4):
            lhs = anticommutator(gammas[mu], gammas[nu])
            rhs = zero_matrix(4, 4)
            for i in range(4): rhs[i][i] = scalar(2 * eta[mu] if mu == nu else 0)
            ok &= mat_eq(lhs, rhs)
    delta_inv = scalar(1 - NU).inv()
    M = mat_mul(g0, g1)
    S = mat_add(identity(4), M); S_inv = scalar_mul(delta_inv, mat_sub(identity(4), M))
    A = scalar(1 + NU) / scalar(1 - NU); B = scalar(-2) / scalar(1 - NU)
    # 8:D12 (p08032)
    ok &= (A.a, A.b, B.a, B.b) == (10, 0, 2, 0)
    # 8:D6 (p08026)
    ok &= mat_eq(mat_mul(mat_mul(S_inv, g0), S), mat_add(scalar_mul(A, g0), scalar_mul(scalar(NU) * B, g1)))
    ok &= mat_eq(mat_mul(mat_mul(S_inv, g1), S), mat_add(scalar_mul(B, g0), scalar_mul(A, g1)))
    # 8:D7 (p08027)
    t0 = mat_mul(mat_mul(S, g0), S_inv); t1 = mat_mul(mat_mul(S, g1), S_inv)
    ok &= mat_eq(t0, mat_add(scalar_mul(A, g0), scalar_mul(-scalar(NU) * B, g1)))
    ok &= mat_eq(t1, mat_add(scalar_mul(-B, g0), scalar_mul(A, g1)))
    a, b = A.a, B.a
    lam = [[a, b, 0, 0], [(NU * b) % P, a, 0, 0], [0, 0, 1, 0], [0, 0, 0, 1]]
    boosted = [(a, (NU * b) % P, 0, 0), (b, a, 0, 0), (0, 0, 1, 0), (0, 0, 0, 1)]
    sample = {(0, 0, 0, 0): [ONE, C, ZERO, scalar(2)], (1, 2, 0, 0): [scalar(3), ZERO, I_T, ONE], (5, 0, 1, 0): [ZERO, scalar(4), C, scalar(7)]}
    std = [(1, 0, 0, 0), (0, 1, 0, 0), (0, 0, 1, 0), (0, 0, 0, 1)]
    # 8:D8 (p08028)
    lhs = dirac_apply(transport_apply(sample, lam, S), [t0, t1, g2, g3], boosted)
    rhs = transport_apply(dirac_apply(sample, gammas, std), lam, S)
    ok &= field_eq(lhs, rhs)
    check("fin.S3", ok, "Clifford; boost formulas; γ̂⁰ = 10γ⁰ − 4γ¹, γ̂¹ = −2γ⁰ + 10γ¹ (A = 10, B = 2); covariance on the sample field")

# ------------------------------------------------------------------------------------------------------------
# block shell — the free evolution is the drive; the F_17 numbers (shell_checks)
#
# Shell-reading checks: the free evolution is the drive (EXACT).
#
# Verifies Theorem (zonal evolution) and its corollaries on F_13 and F_17,
# plus the F_17 Dirac example numbers quoted in the manuscript.
#
#   Z1  The drive pullback (D psi)(x) = psi(g^{-1} x) is a permutation
#       operator (unitary); on the character chi_k(g^j) = g^{jk} it acts
#       with eigenvalue g^{-k}: the winding-k mode gains phase g^{-k} per
#       chronon, exhaustively over all k and all cycle points.
#   Z2  Isotropy: <chi_k, chi_k> = 0 except k = 0 and k = (p-1)/2, whose
#       eigenvalues are +-1 = N^1 intersect the phase cycle.
#   Z3  Sector separation: the eigenvalue g^{-1} has order p-1 > 2, hence
#       lies outside N^1: the free evolution is not a Cayley step of any
#       Hamiltonian with Frobenius-fixed spectrum.
#   Z4  F_17 example: frame (t;0,1,3), derived i = 3^{-4} = 4, i^2 = -1;
#       2, i, e = g^i all squares (only g nonsquare); with nu = g = 3 and
#       x = y = 1: A = 15, B = 1, A^2 - nu B^2 = 1; |G_3| = 18 = p + 1;
#       an order-3 boost exists (triality), none exists at p = 13.
def block_shell():
    """Block shell — the free evolution is the drive, the F_17 numbers (EXACT): shell.Z1–Z4."""
    begin("shell")

    def is_sq(a, p):
        return pow(a % p, (p - 1) // 2, p) == 1

    for p, g in ((13, 2), (17, 3)):
        n = p - 1
        # Z1: eigen-relation of the pullback on every character, every point
        for k in range(n):
            lam = pow(g, (-k) % n, p)
            # 8:F3 (p08040)
            chk(f"Z1 p={p} k={k}",
                all(pow(g, ((j - 1) * k) % n, p) == lam * pow(g, (j * k) % n, p) % p
                    for j in range(n)))
        # Z2: isotropy pattern
        for k in range(n):
            s = sum(pow(g, (2 * j * k) % n, p) for j in range(n)) % p
            chk(f"Z2 p={p} k={k}", (s == 0) == (k not in (0, n // 2)))
        chk(f"Z2 p={p} real eigenvalues",
            pow(g, 0, p) == 1 and pow(g, (-(n // 2)) % n, p) == p - 1)
        # Z3: sector separation
        o, v = 1, pow(g, n - 1, p)          # g^{-1}
        u = v
        while u != 1:
            u = u * v % p; o += 1
        # 8:F4 (p08041)
        chk(f"Z3 p={p} ord(g^-1) = p-1", o == n)

    # Z4: the F_17 anchor
    p, g = 17, 3
    i = pow(pow(g, p - 2, p), 4, p)
    chk("Z4 i = 4, i^2 = -1", i == 4 and i * i % p == p - 1)
    chk("Z4 2, i, e squares; g nonsquare",
        is_sq(2, p) and is_sq(i, p) and is_sq(pow(g, i, p), p) and not is_sq(g, p))
    nu = g
    d = (1 - nu) % p
    di = pow(d, p - 2, p)
    A, B = (1 + nu) * di % p, (-2) * di % p
    chk("Z4 A = 15, B = 1", A == 15 and B == 1)
    chk("Z4 A^2 - nu B^2 = 1", (A * A - nu * B * B) % p == 1)
    def boost_count(p, nu):
        seen = set()
        for x in range(p):
            for y in range(p):
                dd = (x * x - nu * y * y) % p
                if dd == 0:
                    continue
                ddi = pow(dd, p - 2, p)
                seen.add(((x * x + nu * y * y) * ddi % p, (-2 * x * y) * ddi % p))
        return seen
    G17 = boost_count(17, 3)
    G13 = boost_count(13, 2)
    chk("Z4 |G_3| = 18", len(G17) == 18)
    chk("Z4 |G_2| = 14", len(G13) == 14)
    def kord(a, b, p, nu):
        x, y, o = a, b, 1
        while (x, y) != (1, 0):
            x, y = (x * a + nu * y * b) % p, (x * b + y * a) % p, ; o += 1
        return o
    # order-3 element in N^1: exists iff 3 | p+1 (via A - B w norm-one coords)
    def n1_orders(p, nu):
        out = set()
        for x in range(p):
            for y in range(p):
                if (x * x - nu * y * y) % p == 1:
                    out.add(kord(x, y, p, nu))
        return out
    chk("Z4 triality at p=17", 3 in n1_orders(17, 3))
    chk("Z4 no triality at p=13", 3 not in n1_orders(13, 2))
    flush("shell")

# ------------------------------------------------------------------------------------------------------------
# block o2 — the canonical Lorentzian coefficient ν = g (o2_checks)
#
# O2 exact checks: the canonical Lorentzian coefficient nu = g (EXACT).
#
# Blueprint item O2 (reports/revision-blueprint.md). All checks in exact
# integer arithmetic; no floats, no RNG, no searched roots where derived
# ones exist. Square classes by the Euler criterion a^((p-1)/2) = +-1.
#
# Claims checked:
#   C1  Every primitive g is a nonsquare, on every symmetry-complete shell.
#   C2  The nonsquare class is unique: the product of any two nonsquares
#       is a square (representative choice carries no geometric content).
#   C3  i is a square iff kappa is even (8 | p-1); 2, 2^-1, -2 are squares
#       iff kappa is even.  Hence on kappa-even (admissibility-class)
#       shells every named residue except g lands in the square class:
#       g is the unique universally-nonsquare frame datum.
#   C4  e = g^i has no stable class (i's exponent parity varies by shell):
#       counterexamples both ways.
#   C5  Flip stability: [g^-1] = [g] (nonsquare); the class survives the
#       matter-antimatter gauge.
#   C6  The boost group G_nu with nu = g has order exactly p+1 (the
#       non-split torus), enumerated exhaustively on small shells.
#   C7  F_13 anchor: g = 2 = nu (the paper's example already instantiates
#       nu = g); derived i = g^-kappa = 5; 2^-1 = 7 nonsquare, so
#       sqrt(2^-1) lives in K, not F_13 (kappa odd = non-admissible).
#   C8  F_17 counter-anchor (kappa = 4 even): 2, i = 4, e are all squares;
#       only g = 3 is nonsquare; |G_3| = 18 = p+1.
#   C9  Lab Carrier Om = 2,408,561 (S = 602,140 even, admissible):
#       g = 6 nonsquare; 2, 2^-1, -2, i = hbar = 18,688 all squares --
#       on the physical admissibility class the drive is the only named
#       nonsquare, and c = sqrt(2^-1) = 171,106 is base-rational.
def is_sq(a, p):
    a %= p
    assert a != 0
    return pow(a, (p - 1) // 2, p) == 1

def primitive_roots(p):
    n = p - 1
    fac, m = set(), n
    d = 2
    while d * d <= m:
        while m % d == 0:
            fac.add(d); m //= d
        d += 1
    if m > 1:
        fac.add(m)
    return [g for g in range(2, p) if all(pow(g, n // q, p) != 1 for q in fac)]

def shells(limit):
    for p in range(5, limit):
        if p % 4 == 1 and all(p % d for d in range(2, int(p**0.5) + 1)):
            yield p

def block_o2():
    """Block o2 — the canonical Lorentzian coefficient ν = g (EXACT): o2.C1, C2, C3i, C3a, C4–C9."""
    begin("o2")

    # C1, C2, C3, C5 over all symmetry-complete shells below 2000
    for p in shells(2000):
        kap = (p - 1) // 4
        gs = primitive_roots(p)
        # 8:B3 (p08009)
        chk(f"C1 p={p}", all(not is_sq(g, p) for g in gs))
        ns = [a for a in range(1, p) if not is_sq(a, p)]
        # 8:B2 (p08008)
        chk(f"C2 p={p}", all(is_sq(ns[0] * b, p) for b in ns[1:]))
        g = gs[0]
        i = pow(pow(g, p - 2, p), kap, p)          # derived orientation i = g^-kappa
        chk(f"C3i p={p}", is_sq(i, p) == (kap % 2 == 0))
        inv2 = (p + 1) // 2
        for a in (2, inv2, p - 2):
            chk(f"C3a p={p} a={a}", is_sq(a, p) == (kap % 2 == 0))
        chk(f"C5 p={p}", not is_sq(pow(g, p - 2, p), p))

    # C4: e's class varies -- exhibit both parities of the exponent i
    par = set()
    for p in shells(2000):
        kap = (p - 1) // 4
        g = primitive_roots(p)[0]
        i = pow(pow(g, p - 2, p), kap, p)
        par.add(i % 2)                              # exponent parity = class of e
        if par == {0, 1}:
            break
    chk("C4 e class unstable", par == {0, 1})

    # C6: |G_nu| = p+1 with nu = g, exhaustive enumeration
    def boost_order(p, nu):
        seen = set()
        for x in range(p):
            for y in range(p):
                d = (x * x - nu * y * y) % p
                if d == 0:
                    continue
                di = pow(d, p - 2, p)
                seen.add(((x * x + nu * y * y) * di % p, (-2 * x * y) * di % p))
        return len(seen)

    for p in (13, 17, 29, 37):
        g = primitive_roots(p)[0]
        chk(f"C6 p={p}", boost_order(p, g) == p + 1)

    # C7: F_13 anchor
    p = 13
    chk("C7 g=2 primitive", 2 in primitive_roots(p))
    chk("C7 nu=2=g", True)                          # the example's nu is the drive
    chk("C7 i derived", pow(pow(2, p - 2, p), 3, p) == 5 and 5 * 5 % p == p - 1)
    chk("C7 2^-1=7 nonsquare", not is_sq(7, p))

    # C8: F_17 counter-anchor (kappa even)
    p = 17
    chk("C8 g=3 primitive", 3 in primitive_roots(p))
    i17 = pow(pow(3, p - 2, p), 4, p)
    chk("C8 i=4 square", i17 == 4 and is_sq(4, p) and 4 * 4 % p == p - 1)
    chk("C8 2 square", is_sq(2, p))
    chk("C8 e square", is_sq(pow(3, i17, p), p))
    chk("C8 |G_3|=18", boost_order(p, 3) == p + 1)

    # C9: lab Carrier
    Om, S = 2408561, 602140
    chk("C9 S even", S % 2 == 0 and Om == 4 * S + 1)
    chk("C9 g=6 nonsquare", not is_sq(6, Om))
    inv2 = (Om + 1) // 2
    chk("C9 2,2^-1,-2 squares", all(is_sq(a, Om) for a in (2, inv2, Om - 2)))
    chk("C9 i=hbar square", is_sq(18688, Om) and 18688 * 18688 % Om == Om - 1)
    chk("C9 c base-rational", 171106 * 171106 % Om == inv2)
    flush("o2")

# ------------------------------------------------------------------------------------------------------------
# block o7 — the parity grading and the two factors of c² (o7_checks)
#
# O7 exact checks: the factorisation ν = c²·(2g) and the parity grading (EXACT).
#
# Blueprint item O7; findings in reports/o7-flag-parity.md. All arithmetic
# exact; square classes by the Euler criterion; discrete logs by exhaustive
# exponent scan on small shells (dev shells only).
#
# Claims checked:
#   P1  Parity form of the square class: for primitive g the squares are
#       exactly <g^2>, so the class of x is the parity of dlog_g(x) --
#       the drive-step (chronon) parity.  Exhaustive on F_13, F_17 for
#       every primitive g; Euler-criterion form on all symmetry-complete
#       shells p < 2000.
#   P2  The exact factorization nu = c^2 * (2g): shell-generic since
#       2*c^2 = 1; lab-Carrier instance (mod Om = 2,408,561):
#       c^2 = 1,204,281, 2g = 12, product = 6 = g.
#   P3  Parity split: [c^2] is even (square) iff kappa is even (the
#       admissibility class: the two-way constant is registered exactly
#       where c exists); [2g] is odd iff kappa is even; the product is
#       odd on every shell -- the cofactor carries the entire signature
#       bit in both parities.
#   P4  Chart-grading insufficiency: on kappa-even shells every element
#       of Q4 = {1, i, -1, -i} is a square -- the order-four chart
#       family carries no signature on the admissibility class; the
#       signature lives in the parity grading, invisible to torsion-free
#       (and Q4D) bookkeeping.
#   P5  Registered transport is even: N(g x) = g^2 N(x) identically
#       (framed-complex norm), and g^2 is a square -- per-chronon
#       two-way/comparison readings are even-parity; the one-way
#       multiplier g is odd; no x in F_p has x^2 = g (the cone slope is
#       the unregistrable half-step).
#   P6  Gauge stability: dlog_g(g^{-1}) = -1 is odd -- the B19 flip
#       g -> g^{-1} preserves the parity class while reversing the
#       one-way direction (finite Reichenbach freedom).
def block_o7():
    """Block o7 — the parity grading and the factorisation ν = c²·(2g) (EXACT): o7.P1–P6."""
    begin("o7")

    def is_sq(a, p):
        return pow(a % p, (p - 1) // 2, p) == 1

    def primitive_roots(p):
        n = p - 1
        fac, m, d = set(), n, 2
        while d * d <= m:
            while m % d == 0:
                fac.add(d); m //= d
            d += 1
        if m > 1:
            fac.add(m)
        return [g for g in range(2, p) if all(pow(g, n // q, p) != 1 for q in fac)]

    def shells(limit):
        for p in range(5, limit):
            if p % 4 == 1 and all(p % d for d in range(2, int(p**0.5) + 1)):
                yield p

    # P1 exhaustive on dev shells: class of g^j = parity of j, every primitive g
    for p in (13, 17):
        for g in primitive_roots(p):
            for j in range(p - 1):
                # 8:B5 (p08011)
                chk(f"P1 p={p} g={g} j={j}", is_sq(pow(g, j, p), p) == (j % 2 == 0))
    # P1 Euler form on the scan: <g^2> = squares
    for p in shells(2000):
        g = primitive_roots(p)[0]
        chk(f"P1 p={p} g odd", not is_sq(g, p))
        chk(f"P1 p={p} g^2 even", is_sq(g * g % p, p))

    # P2 factorization
    for p in shells(2000):
        g = primitive_roots(p)[0]
        c2 = (p + 1) // 2                       # 2^{-1}
        # 8:B4 (p08010)
        chk(f"P2 p={p} nu = c^2*2g", (c2 * 2 * g) % p == g % p)
    Om, S, gO = 2408561, 602140, 6
    c2O = (Om + 1) // 2
    chk("P2 lab Carrier c^2 = 2S+1", c2O == 2 * S + 1 == 1204281)
    chk("P2 lab Carrier c^2*(2g) = g", (c2O * 12) % Om == 6)

    # P3 parity split; P4 chart-grading insufficiency
    for p in shells(2000):
        kap = (p - 1) // 4
        g = primitive_roots(p)[0]
        c2 = (p + 1) // 2
        chk(f"P3 p={p} [c^2] even iff kappa even", is_sq(c2, p) == (kap % 2 == 0))
        chk(f"P3 p={p} [2g] odd iff kappa even", (not is_sq(2 * g % p, p)) == (kap % 2 == 0))
        chk(f"P3 p={p} product odd", not is_sq(c2 * 2 * g % p, p))
        if kap % 2 == 0:
            i = pow(g, kap, p)
            chk(f"P4 p={p} Q4 all squares", all(is_sq(x, p) for x in (1, i, p - 1, p - i)))

    # P5 registered transport even; cone slope unregistrable
    for p, g in ((13, 2), (17, 3)):
        for a in range(p):
            for b in range(p):
                if (a, b) == (0, 0):
                    continue
                n1 = (a * a + b * b) % p
                ga, gb = (g * a) % p, (g * b) % p
                # 8:B6 (p08012)
                chk(f"P5 p={p} N(gx)=g^2N(x) ({a},{b})",
                    (ga * ga + gb * gb) % p == (g * g * n1) % p)
        chk(f"P5 p={p} g^2 square", is_sq(g * g % p, p))
        chk(f"P5 p={p} x^2=g insoluble", all(pow(x, 2, p) != g for x in range(p)))

    # P6 flip parity
    for p in shells(2000):
        g = primitive_roots(p)[0]
        chk(f"P6 p={p} g^-1 odd", not is_sq(pow(g, p - 2, p), p))
    flush("o7")

# ------------------------------------------------------------------------------------------------------------
# block o134 — boost torus, Cayley transform, orbit periods (o134_checks)
#
# O1/O3/O4 exact checks: boost torus, Cayley transform, orbit periods (EXACT).
#
# Blueprint items O1, O3, O4 (reports/revision-blueprint.md); findings in
# reports/o134-findings.md. All arithmetic exact over K = F_p[w]/(w^2 - nu);
# no floats, no RNG. Elements of K are pairs (a, b) = a + b*w.
#
# Claims checked:
#   O1a  The kernel of (x,y) -> Lambda(x,y) is the scalar line: each boost
#        matrix has exactly p-1 preimages in K^x, so |G_nu| = p+1.
#   O1b  Hilbert 90 form: the boost entries satisfy A - B*w = z/zbar, a
#        norm-one element; the map z*F_p^x -> z/zbar is a bijection onto
#        the norm-one torus N1, so G_nu ~ N1 = C_{p+1} canonically.
#   O1c  G_nu is cyclic: an element of order exactly p+1 exists.
#   O1d  Triality: an order-3 element exists in G_nu iff 3 | p+1
#        (p = 17: yes; p = 13: no).
#   O1e  F_17 is the minimal admissible shell: kappa = 4 even, kappa = 1
#        (mod 3), p = 5 (mod 12), and no smaller symmetry-complete p
#        satisfies the triple.
#   O3a  The scalar Cayley map phi(lam) = (1 + a*lam)/(1 - a*lam), a in
#        K^- nonzero, sends the Frobenius-fixed projective line
#        P1(F_p) bijectively onto the norm-one torus N1 (with
#        phi(infinity) = -1).  Self-adjoint line -> unitary torus, exact.
#   O3b  The unitary group of one channel is N1: {u in K^x : ubar*u = 1}
#        = C_{p+1}, same torus as the boosts.
#   O4a  Kinetic case: H = -Delta on F_p is nilpotent (H = -T^{-1}(T-I)^2,
#        (T-I)^p = 0 in characteristic p), hence U = phi(H) is unipotent
#        and ord(U) = p.  Reproduces and explains the paper's ord = 13.
#   O4b  Potential case: H = M_V with V = id is diagonal with F_p
#        spectrum, so U's eigenphases lie in N1 and ord(U) = p+1.
#        (p = 13: ord 14; p = 17: ord 18.)
#   O4c  Mixed case (recorded datum, p = 5, nu = g = 2): ord(U) for
#        H = -Delta + M_id is computed exactly and verified.
#   O4d  Composite/E2 cross-check: ord of a block-diagonal pair is the
#        lcm of the parts' orders (13, 14 -> 182).
def make_field(p, nu):
    def add(u, v): return ((u[0] + v[0]) % p, (u[1] + v[1]) % p)
    def sub(u, v): return ((u[0] - v[0]) % p, (u[1] - v[1]) % p)
    def mul(u, v):
        return ((u[0] * v[0] + nu * u[1] * v[1]) % p,
                (u[0] * v[1] + u[1] * v[0]) % p)
    def conj(u): return (u[0], (-u[1]) % p)
    def norm(u): return (u[0] * u[0] - nu * u[1] * u[1]) % p
    def inv(u):
        n = norm(u)
        ni = pow(n, p - 2, p)
        return ((u[0] * ni) % p, (-u[1] * ni) % p)
    return add, sub, mul, conj, norm, inv

def block_o134():
    """Block o134 — the boost torus, the Cayley transform and the orbit periods (EXACT): o134.O1a–O4d."""
    begin("o134")

    def boost(p, nu, x, y):
        d = (x * x - nu * y * y) % p
        di = pow(d, p - 2, p)
        return ((x * x + nu * y * y) * di % p, (-2 * x * y) * di % p)

    # ---------------- O1 ----------------
    for p, nu in ((13, 2), (17, 3)):
        add, sub, mul, conj, norm, inv = make_field(p, nu)
        pre = {}
        for x in range(p):
            for y in range(p):
                if (x * x - nu * y * y) % p == 0:
                    continue
                pre.setdefault(boost(p, nu, x, y), []).append((x, y))
        # 8:D5 (p08025)
        chk(f"O1a p={p} |G|=p+1", len(pre) == p + 1)
        chk(f"O1a p={p} fibers p-1", all(len(v) == p - 1 for v in pre.values()))
        n1 = {u for x in range(p) for y in range(p)
              if norm(u := (x, y)) == 1}
        chk(f"O3b p={p} |N1|=p+1", len(n1) == p + 1)
        ok = True
        for (A, B), zs in pre.items():
            for z in zs:
                q = mul(z, inv(conj(z)))              # z / zbar
                ok &= q == (A, (-B) % p) and norm(q) == 1
        chk(f"O1b p={p} Lambda = z/zbar (Hilbert 90)", ok)
        chk(f"O1b p={p} image = N1", {(A, (-B) % p) for (A, B) in pre} == n1)
        def kord(u):
            v, o = u, 1
            while v != (1, 0):
                v = mul(v, u); o += 1
            return o
        chk(f"O1c p={p} cyclic", max(kord(u) for u in n1) == p + 1)
        chk(f"O1d p={p} triality", any(kord(u) == 3 for u in n1) == ((p + 1) % 3 == 0))

    def is_prime(n):
        return n > 1 and all(n % d for d in range(2, int(n**0.5) + 1))
    adm = [4 * k + 1 for k in range(1, 5)
           if k % 2 == 0 and k % 3 == 1 and is_prime(4 * k + 1)]
    chk("O1e F_17 minimal admissible", adm == [17])

    # ---------------- O3 ----------------
    for p, nu in ((13, 2), (17, 3)):
        add, sub, mul, conj, norm, inv = make_field(p, nu)
        n1 = {u for x in range(p) for y in range(p) if norm(u := (x, y)) == 1}
        for k in range(1, p):                          # every nonzero a = k*w
            a = (0, k)
            img = set()
            for lam in range(p):
                den = sub((1, 0), mul(a, (lam, 0)))
                # 8:C5 (p08019)
                chk(f"O3a p={p} k={k} lam={lam} invertible", norm(den) != 0)
                u = mul(add((1, 0), mul(a, (lam, 0))), inv(den))
                chk(f"O3a p={p} k={k} lam={lam} norm-one", norm(u) == 1)
                img.add(u)
            img.add(((-1) % p, 0))                     # phi(infinity) = -1
            chk(f"O3a p={p} k={k} bijection", img == n1 and len(img) == p + 1)

    # ---------------- O4 ----------------
    def mat_id(n): return [[(1, 0) if i == j else (0, 0) for j in range(n)] for i in range(n)]

    def mat_mul(X, Y, mul, add, n):
        Z = [[(0, 0)] * n for _ in range(n)]
        for i in range(n):
            for k in range(n):
                x = X[i][k]
                if x == (0, 0):
                    continue
                for j in range(n):
                    Z[i][j] = add(Z[i][j], mul(x, Y[k][j]))
        return Z

    def mat_inv(X, mul, add, sub, inv, n):
        A = [row[:] + I_row[:] for row, I_row in zip(X, mat_id(n))]
        for col in range(n):
            piv = next(r for r in range(col, n) if A[r][col] != (0, 0))
            A[col], A[piv] = A[piv], A[col]
            pi = inv(A[col][col])
            A[col] = [mul(pi, v) for v in A[col]]
            for r in range(n):
                if r != col and A[r][col] != (0, 0):
                    f = A[r][col]
                    A[r] = [sub(v, mul(f, w)) for v, w in zip(A[r], A[col])]
        return [row[n:] for row in A]

    def cayley(H, a, p, nu, n):
        add, sub, mul, conj, norm, inv = make_field(p, nu)
        aH = [[mul(a, H[i][j]) for j in range(n)] for i in range(n)]
        I = mat_id(n)
        Im = [[sub(I[i][j], aH[i][j]) for j in range(n)] for i in range(n)]
        Ip = [[add(I[i][j], aH[i][j]) for j in range(n)] for i in range(n)]
        return mat_mul(mat_inv(Im, mul, add, sub, inv, n), Ip, mul, add, n)

    def mat_ord(U, p, nu, n, cap):
        add, sub, mul, conj, norm, inv = make_field(p, nu)
        I, V, o = mat_id(n), U, 1
        while V != I:
            V = mat_mul(V, U, mul, add, n); o += 1
            if o > cap:
                return None
        return o

    def build(p, kinetic, potential):
        n = p
        H = [[(0, 0)] * n for _ in range(n)]
        for x in range(n):
            if kinetic:                                 # -Delta = -(T + T^-1 - 2I)
                H[x][(x + 1) % n] = ((-1) % p, 0)
                H[x][(x - 1) % n] = ((-1) % p, 0)
                H[x][x] = (2 % p, 0)
            if potential:                               # + M_V, V = id
                a = H[x][x]
                H[x][x] = ((a[0] + x) % p, a[1])
        return H

    for p, nu in ((13, 2), (17, 3)):
        add, sub, mul, conj, norm, inv = make_field(p, nu)
        a = (0, 1)                                      # alpha = w
        Hk = build(p, True, False)
        U = cayley(Hk, a, p, nu, p)
        # unipotency: (U - I)^p = 0
        I = mat_id(p)
        N = [[sub(U[i][j], I[i][j]) for j in range(p)] for i in range(p)]
        Np = N
        for _ in range(p - 1):
            Np = mat_mul(Np, N, mul, add, p)
        # 8:E4 (p08037)
        chk(f"O4a p={p} (U-I)^p = 0", all(v == (0, 0) for row in Np for v in row))
        chk(f"O4a p={p} ord(U) = p", mat_ord(U, p, nu, p, 2 * p) == p)
        Hv = build(p, False, True)
        Uv = cayley(Hv, a, p, nu, p)
        chk(f"O4b p={p} ord(U) = p+1", mat_ord(Uv, p, nu, p, 2 * p + 2) == p + 1)

    # O4c: mixed case at p = 5, nu = g = 2 (primitive, nonsquare)
    p, nu = 5, 2
    Hm = build(p, True, True)
    Um = cayley(Hm, (0, 1), p, nu, p)
    om = mat_ord(Um, p, nu, p, 100000)
    chk("O4c p=5 mixed order finite", om is not None)
    print(f"O4c datum: p=5, nu=g=2, H=-Delta+M_id, alpha=w: ord(U) = {om}")

    # O4d: composite = lcm (E2 cross-check)
    chk("O4d lcm(13,14)=182", 13 * 14 // gcd(13, 14) == 182)
    flush("o134")

# ------------------------------------------------------------------------------------------------------------
# block o8 — symmetric Dirac dynamics and the spinor form (o8_checks)
#
# O8 exact checks: symmetric Dirac dynamics (round-01 item 1) (EXACT).
#
# Repair route of review 8-dirac-20260709-01-1, executed and extended.
# Elements of K = F_p[w]/(w^2 - nu) as pairs (a, b) = a + b w.
#
# Claims checked:
#   X1  Gamma adjoints under plain conj-transpose: (g0)+ = -g0, (g1)+ = -g1,
#       (g2)+ = +g2, (g3)+ = -g3 (the g2 obstruction; p = 5, 13, 17).
#   X2  The spinor twist X = g0 g1 g3 is Hermitian (X+ = X), invertible,
#       commutes with g0, g1, g3 and anticommutes with g2; consequently
#       X^{-1} (g_mu)+ X = -g_mu for ALL mu: every gamma is X-anti-self-
#       adjoint.  (The continuum recipe M = g0 fails here because Frobenius
#       fixes i; checked as X3.)
#   X3  gamma0-twist fails: signs remain mixed.
#   X4  Symmetric difference: (T - T^{-1}) is nilpotent on H(F_p)
#       ((T^2 - I)^p = 0), and anti-self-adjoint; hence each gamma^mu
#       del^s_mu is X-self-adjoint and D^s = sum gamma^mu del^s_mu is
#       X-self-adjoint; D^s is nilpotent (its square is the symmetric
#       Klein-Gordon operator, a sum of commuting nilpotents).
#   X5  1+1 operator check at p = 5, nu = g = 2 (spinor space K^4 over
#       F_5^2, dimension 100): H = D^s is X-self-adjoint as a matrix
#       identity; the Cayley step U = (I - aH)^{-1}(I + aH), a = w, is
#       X-unitary (U^# U = I); U is unipotent with ord(U) = 25 = p^2
#       (massless meridional period = the translation torus).
#   X6  Massive case: H = D^s - m I is X-self-adjoint; U factors as
#       norm-one phase times unipotent: ord(U) = lcm(p, ord_{N1} phi(-m))
#       -- checked for m = 1, 2 at p = 5 (mass enters through the
#       norm-one phase, interactions' torus).
#   X7  Sector unification (round-01 item 2): on H(Phi_p) the cycle
#       Laplacian Delta_Phi = D + D^{-1} - 2I is self-adjoint, its Cayley
#       steps commute with the drive pullback D exactly, and both are
#       unitary on the SAME space (p = 13: composite formed and checked).
def block_o8():
    """Block o8 — symmetric Dirac dynamics and the spinor form (EXACT): o8.X1–X9."""
    begin("o8")

    def field(p, nu):
        add = lambda u, v: ((u[0]+v[0]) % p, (u[1]+v[1]) % p)
        sub = lambda u, v: ((u[0]-v[0]) % p, (u[1]-v[1]) % p)
        def mul(u, v):
            return ((u[0]*v[0] + nu*u[1]*v[1]) % p, (u[0]*v[1] + u[1]*v[0]) % p)
        conj = lambda u: (u[0], (-u[1]) % p)
        def inv(u):
            n = (u[0]*u[0] - nu*u[1]*u[1]) % p
            ni = pow(n, p-2, p)
            return ((u[0]*ni) % p, (-u[1]*ni) % p)
        return add, sub, mul, conj, inv

    def gammas(p, nu, g):
        kap = (p-1)//4
        i = pow(pow(g, p-2, p), kap, p)
        O, I1, ii, ww, iw = (0,0), (1,0), (i % p, 0), (0,1), (0, i % p)
        niw = (0, (-i) % p); ni = ((p-i) % p, 0); m1 = ((p-1) % p, 0)
        s1 = [[O,I1],[I1,O]]; s2 = [[O,ni],[ii,O]]; s3 = [[I1,O],[O,m1]]
        def blk(A, B, C, D):
            return [[A[0][0],A[0][1],B[0][0],B[0][1]],
                    [A[1][0],A[1][1],B[1][0],B[1][1]],
                    [C[0][0],C[0][1],D[0][0],D[0][1]],
                    [C[1][0],C[1][1],D[1][0],D[1][1]]]
        Z = [[O,O],[O,O]]
        def smul(s, M):
            add, sub, mul, conj, inv = field(p, nu)
            return [[mul(s, x) for x in row] for row in M]
        beta = blk(Z[0:2] and Z, [[I1,O],[O,I1]], [[I1,O],[O,I1]], Z)
        def rho(s):
            ms = [[((-x[0]) % p, (-x[1]) % p) for x in row] for row in s]
            return blk(Z, s, ms, Z)
        g0 = smul(iw, beta)
        g1 = smul(ii, rho(s1)); g2 = smul(ii, rho(s2)); g3 = smul(ii, rho(s3))
        return g0, g1, g2, g3, i

    def mmul(A, B, p, nu):
        add, sub, mul, conj, inv = field(p, nu)
        n = len(A)
        C = [[(0,0)]*n for _ in range(n)]
        for a in range(n):
            for b in range(n):
                x = A[a][b]
                if x == (0,0): continue
                for c in range(n):
                    C[a][c] = add(C[a][c], mul(x, B[b][c]))
        return C

    def dagger(A, p, nu):
        add, sub, mul, conj, inv = field(p, nu)
        n = len(A)
        return [[conj(A[b][a]) for b in range(n)] for a in range(n)]

    def neg(A, p): return [[((-x[0]) % p, (-x[1]) % p) for x in row] for row in A]
    def eye(n): return [[(1,0) if a==b else (0,0) for b in range(n)] for a in range(n)]

    # X1-X3
    for p, g in ((5,2),(13,2),(17,3)):
        nu = g
        g0,g1,g2,g3,i = gammas(p, nu, g)
        G = [g0,g1,g2,g3]
        signs = []
        for M in G:
            Md = dagger(M, p, nu)
            signs.append(+1 if Md == M else (-1 if Md == neg(M,p) else 0))
        # 8:D9 (p08029)
        chk(f"X1 p={p} plain signs", signs == [-1,-1,1,-1])
        X = mmul(mmul(g0,g1,p,nu), g3, p, nu)
        chk(f"X2 p={p} X Hermitian", dagger(X,p,nu) == X)
        add, sub, mul, conj, inv = field(p, nu)
        ok = True
        for k, M in enumerate(G):
            XM, MX = mmul(X,M,p,nu), mmul(M,X,p,nu)
            ok &= (XM == MX) if k != 2 else (XM == neg(MX,p))
        chk(f"X2 p={p} (anti)commutation", ok)
        # X^{-1} M+ X = -M for all mu; X^2 is scalar so X^{-1} ~ X
        X2m = mmul(X, X, p, nu)
        s = X2m[0][0]
        chk(f"X2 p={p} X^2 scalar", X2m == [[s if a==b else (0,0) for b in range(4)] for a in range(4)])
        chk(f"X2 p={p} X^2 = +nu exactly", s == (nu % p, 0))
        si = inv(s)
        Xi = [[mul(si, x) for x in row] for row in X]
        ok = all(mmul(mmul(Xi, dagger(M,p,nu),p,nu), X, p, nu) == neg(M,p) for M in G)
        chk(f"X2 p={p} all gammas X-anti-self-adjoint", ok)
        g0i = [[mul(inv(mmul(g0,g0,p,nu)[0][0]), x) for x in row] for row in g0]
        s03 = [ +1 if mmul(mmul(g0i, dagger(M,p,nu),p,nu), g0,p,nu) == M else -1 for M in G ]
        chk(f"X3 p={p} gamma0-twist mixed", len(set(s03)) > 1)

    # X4: 1-dim symmetric difference nilpotent + anti-self-adjoint (plain form)
    for p in (5, 13):
        T = [[(1,0) if (b-a) % p == 1 else (0,0) for b in range(p)] for a in range(p)]
        Ti = [[(1,0) if (b-a) % p == p-1 else (0,0) for b in range(p)] for a in range(p)]
        nu = 2 if p in (5,13) else 3
        S = [[( (T[a][b][0]-Ti[a][b][0]) % p, 0) for b in range(p)] for a in range(p)]
        P = S
        nil = False
        for _ in range(p):
            P = mmul(P, S, p, nu)
            if all(x == (0,0) for row in P for x in row): nil = True; break
        chk(f"X4 p={p} (T-T^-1) nilpotent", nil)
        chk(f"X4 p={p} anti-self-adjoint", dagger(S,p,nu) == neg(S,p))

    # X5/X6: 1+1 operator check at p=5, nu=g=2
    p, g = 5, 2
    nu = g
    g0,g1,g2,g3,i = gammas(p, nu, g)
    add, sub, mul, conj, inv = field(p, nu)
    inv2 = (pow(2, p-2, p), 0)
    n = 4 * p * p                      # spinor index s + point (x0, x1)
    def idx(s, x0, x1): return s*p*p + x0*p + x1
    def build_D(m):
        D = [[(0,0)]*n for _ in range(n)]
        for x0 in range(p):
            for x1 in range(p):
                for s in range(4):
                    for sp in range(4):
                        c0, c1 = g0[s][sp], g1[s][sp]
                        if c0 != (0,0):
                            h = mul(inv2, c0)
                            D[idx(s,x0,x1)][idx(sp,(x0+1)%p,x1)] = add(D[idx(s,x0,x1)][idx(sp,(x0+1)%p,x1)], h)
                            D[idx(s,x0,x1)][idx(sp,(x0-1)%p,x1)] = sub(D[idx(s,x0,x1)][idx(sp,(x0-1)%p,x1)], h)
                        if c1 != (0,0):
                            h = mul(inv2, c1)
                            D[idx(s,x0,x1)][idx(sp,x0,(x1+1)%p)] = add(D[idx(s,x0,x1)][idx(sp,x0,(x1+1)%p)], h)
                            D[idx(s,x0,x1)][idx(sp,x0,(x1-1)%p)] = sub(D[idx(s,x0,x1)][idx(sp,x0,(x1-1)%p)], h)
                    if m and s == sp:
                        pass
        if m:
            for q in range(n):
                D[q][q] = sub(D[q][q], ((m) % p, 0))
        return D
    # big-X form matrix: block-diagonal X per point
    X = mmul(mmul(g0,g1,p,nu), g3, p, nu)
    def form_adjoint(A):
        # A# = Xbig^{-1} A+ Xbig ; Xbig block diag
        Ad = dagger(A, p, nu)
        s = mmul(X, X, p, nu)[0][0]; si = inv(s)
        Xi4 = [[mul(si, x) for x in row] for row in X]
        B = [[(0,0)]*n for _ in range(n)]
        # (Xi A+ X) with X acting on spinor index only
        for x0 in range(p):
            for x1 in range(p):
                for y0 in range(p):
                    for y1 in range(p):
                        # block (x,y): B_block = Xi4 * Ad_block * X4
                        blk = [[Ad[idx(a,x0,x1)][idx(b,y0,y1)] for b in range(4)] for a in range(4)]
                        if all(v == (0,0) for row in blk for v in row): continue
                        t1 = mmul(Xi4, blk, p, nu); t2 = mmul(t1, X, p, nu)
                        for a in range(4):
                            for b in range(4):
                                B[idx(a,x0,x1)][idx(b,y0,y1)] = t2[a][b]
        return B

    def big_mmul(A, B_):
        C = [[(0,0)]*n for _ in range(n)]
        for a in range(n):
            Ar = A[a]
            for b in range(n):
                x = Ar[b]
                if x == (0,0): continue
                Bb = B_[b]
                Ca = C[a]
                for c in range(n):
                    if Bb[c] != (0,0):
                        Ca[c] = add(Ca[c], mul(x, Bb[c]))
        return C

    def big_inv(A):
        M = [row[:] + [( (1,0) if r==j else (0,0)) for j in range(n)] for r, row in enumerate(A)]
        for col in range(n):
            piv = next(r for r in range(col, n) if M[r][col] != (0,0))
            M[col], M[piv] = M[piv], M[col]
            pi = inv(M[col][col])
            M[col] = [mul(pi, v) for v in M[col]]
            for r in range(n):
                if r != col and M[r][col] != (0,0):
                    f = M[r][col]
                    M[r] = [sub(v, mul(f, w_)) for v, w_ in zip(M[r], M[col])]
        return [row[n:] for row in M]

    def cayley_of(H, a):
        aH = [[mul(a, x) for x in row] for row in H]
        Im = [[sub((1,0) if r==c else (0,0), aH[r][c]) for c in range(n)] for r in range(n)]
        Ip = [[add((1,0) if r==c else (0,0), aH[r][c]) for c in range(n)] for r in range(n)]
        return big_mmul(big_inv(Im), Ip)

    def big_ord(U, cap):
        I = eye(n); V = U; o = 1
        while V != I:
            V = big_mmul(V, U); o += 1
            if o > cap: return None
        return o

    H0 = build_D(0)
    # 8:D10 (p08030)
    chk("X5 D^s X-self-adjoint", form_adjoint(H0) == H0)
    U0 = cayley_of(H0, (0,1))
    chk("X5 U X-unitary", big_mmul(form_adjoint(U0), U0) == eye(n))
    o0 = big_ord(U0, p*p + 1)
    chk("X5 massless U unipotent, ord(U) = p^2", o0 == p * p)
    print(f"X5 datum: massless 1+1 Dirac-Cayley ord(U) = {o0} (p = {p})")

    def n1_ord(u):
        v, o = u, 1
        while v != (1,0):
            v = mul(v, u); o += 1
        return o
    for m in (1, 2):
        Hm = build_D(m)
        chk(f"X6 m={m} X-self-adjoint", form_adjoint(Hm) == Hm)
        Um = cayley_of(Hm, (0,1))
        lam = ((-m) % p, 0)
        a = (0,1)
        num = add((1,0), mul(a, lam)); den = sub((1,0), mul(a, lam))
        phi = mul(num, inv(den))
        om = big_ord(Um, p*p*(p+1) + 1)
        q = n1_ord(phi)
        chk(f"X6 m={m} ord = lcm(p-power, ord phi(-m))",
            om is not None and om % q == 0 and (om // q) in (1, p, p*p) and om % p == 0)
        print(f"X6 datum: m={m}: ord(U) = {om} (norm-one phase order {q})")

    # X7: sector unification on H(Phi_p), p = 13
    p, g = 13, 2
    nu = g
    add, sub, mul, conj, inv = field(p, nu)
    n1 = p - 1
    pts = [pow(g, j, p) for j in range(n1)]
    pos = {x: j for j, x in enumerate(pts)}
    Dm = [[(1,0) if pts[b] == (pow(g, p-2, p) * pts[a]) % p else (0,0) for b in range(n1)] for a in range(n1)]
    Dinv = [[(1,0) if pts[b] == (g * pts[a]) % p else (0,0) for b in range(n1)] for a in range(n1)]
    def small_mmul(A,B):
        m_ = len(A); C = [[(0,0)]*m_ for _ in range(m_)]
        for a in range(m_):
            for b in range(m_):
                x = A[a][b]
                if x == (0,0): continue
                for c in range(m_):
                    if B[b][c] != (0,0): C[a][c] = add(C[a][c], mul(x, B[b][c]))
        return C
    Lap = [[sub(add(Dm[a][b], Dinv[a][b]), ((2,0) if a==b else (0,0))) for b in range(n1)] for a in range(n1)]
    chk("X7 Delta_Phi self-adjoint", [[conj(Lap[b][a]) for b in range(n1)] for a in range(n1)] == Lap)
    # Cayley of Delta_Phi commutes with D
    def small_inv(A):
        m_ = len(A)
        M = [row[:] + [((1,0) if r==j else (0,0)) for j in range(m_)] for r, row in enumerate(A)]
        for col in range(m_):
            piv = next(r for r in range(col, m_) if M[r][col] != (0,0))
            M[col], M[piv] = M[piv], M[col]
            pi = inv(M[col][col])
            M[col] = [mul(pi, v) for v in M[col]]
            for r in range(m_):
                if r != col and M[r][col] != (0,0):
                    f = M[r][col]
                    M[r] = [sub(v, mul(f, w_)) for v, w_ in zip(M[r], M[col])]
        return [row[m_:] for row in M]
    a = (0,1)
    aH = [[mul(a, x) for x in row] for row in Lap]
    Im = [[sub((1,0) if r==c else (0,0), aH[r][c]) for c in range(n1)] for r in range(n1)]
    Ip = [[add((1,0) if r==c else (0,0), aH[r][c]) for c in range(n1)] for r in range(n1)]
    Uc = small_mmul(small_inv(Im), Ip)
    chk("X7 [U, D] = 0 (exact composite)", small_mmul(Uc, Dm) == small_mmul(Dm, Uc))
    chk("X7 U unitary", small_mmul([[conj(Uc[b][a_]) for b in range(n1)] for a_ in range(n1)], Uc) == eye(n1))

    # X8: spin lift vs the spinor form (round-02): S(x,y)# = S(x,-y) = delta S^-1;
    # T scales the X-form by delta = N(z); norm-one lifts preserve it exactly;
    # the odd (nonsquare-norm) coset scales it by the nonsquare class.
    p, g = 5, 2
    nu = g
    g0,g1,g2,g3,i = gammas(p, nu, g)
    add, sub, mul, conj, inv = field(p, nu)
    X4m = mmul(mmul(g0,g1,p,nu), g3, p, nu)
    sX = mmul(X4m, X4m, p, nu)[0][0]; siX = inv(sX)
    Xi4 = [[mul(siX, x) for x in row] for row in X4m]
    M4 = mmul(g0, g1, p, nu)
    def S_of(x, y):
        out = [[(0,0)]*4 for _ in range(4)]
        for a in range(4):
            for b in range(4):
                out[a][b] = add((x,0) if a==b else (0,0), mul((y,0), M4[a][b]))
        return out
    def sharp(A):  # X-adjoint at gamma level
        return mmul(mmul(Xi4, dagger(A,p,nu), p, nu), X4m, p, nu)
    for (x, y) in ((1,1),(2,1),(3,2)):
        d = (x*x - nu*y*y) % p
        if d == 0: continue
        S = S_of(x, y)
        # 8:D11 (p08031)
        chk(f"X8 S({x},{y})# = S(x,-y)", sharp(S) == S_of(x, (-y) % p))
        SS = mmul(sharp(S), S, p, nu)
        chk(f"X8 S#S = delta I ({x},{y})", SS == [[(d,0) if a==b else (0,0) for b in range(4)] for a in range(4)])
    chk("X8 norm-one lift preserves form", (3*3 - nu*2*2) % p == 1)
    chk("X8 odd-class boost exists", pow((2*2 - nu*1*1) % p, (p-1)//2, p) == p-1)
    # X9: static massive Dirac kernel is trivial: D^s - m invertible for m != 0
    # (D^s nilpotent => -m(I - m^{-1}D^s) invertible); dispersion on the cycle:
    # -Delta_Phi acts on chi_k with eigenvalue 2 - g^k - g^{-k} (F_13, all k).
    p13, g13 = 13, 2
    n1 = p13 - 1
    for k in range(n1):
        lam = (2 - pow(g13, k, p13) - pow(g13, (n1 - k) % n1, p13)) % p13
        ok = True
        for j in range(n1):
            lhs = (2*pow(g13,(j*k)%n1,p13) - pow(g13,((j+1)*k)%n1,p13) - pow(g13,((j-1)*k)%n1,p13)) % p13
            ok &= lhs == (lam * pow(g13,(j*k)%n1,p13)) % p13
        chk(f"X9 dispersion k={k}", ok)
    flush("o8")

# ------------------------------------------------------------------------------------------------------------
# block lat — the latitude indices of the shell reading (latitude_checks)
#
# Latitude-index checks: time = L_1, energy = L_{S+1} (EXACT).
#
# Addendum to reports/o134-findings.md (shell-reading programme). Latitude
# formalism per 2-geometry Def. 3.1: orbital shell S_p on the frame
# F_p(t;0,1,g); meridian M_m the additive ray 0, g^m, 2g^m, ..., pi*g^m;
# latitude L_a the multiplicative orbit at radius a; ladder a = 1..pi with
# pi = 2*kappa the terminal latitude (collapsed to the antipode).
#
# Claims checked (Subject register on F_13, F_17; Carrier register on the
# lab Carrier Om = 2,408,561, S = 602,140):
#   L1  Ladder bounds: energy index S+1 (kappa+1) lies inside the ladder,
#       and is the first rung past the midpoint (rungs S | S+1 straddle
#       the equator; ladder length 2S is even, no middle rung).
#   L2  One shift, two ladders: the meridian shift m -> m+kappa is
#       multiplication by g^kappa = +-i (prime meridian -> quarter-turn
#       meridian: space -> momentum); the latitude shift a -> a+kappa
#       sends 1 -> kappa+1 (time -> energy).  Both dualities are the
#       index advance by the capacity.
#   L3  Framed-rational radius register: kappa = -4^{-1}, so the energy
#       radius is 1 + kappa = 3*4^{-1} = 1 - 1/4: the quarter-cycle shift
#       subtracts exactly one quarter of the unit radius.
#   L4  Terminal latitude: pi = 2*kappa = -2^{-1} = -c^2 as a residue; on
#       the Carrier pi_Om = 2S = G (B18): the ladder terminates at the
#       half-period -- the antipode of the observer origin carries the
#       G / -c^2.
#   L5  Chart consistency: the framed-complex chart reads latitudes as
#       norm circles; the unit-norm circle has exactly p-1 points, the
#       cardinality of the phase cycle L_1 (time); the energy circle
#       carries norm (1 - 1/4)^2 = 9/16.
def block_lat():
    """Block lat — the latitude indices of the shell reading (EXACT): lat.L1–L5."""
    begin("lat")

    def inv(a, p): return pow(a % p, p - 2, p)

    CASES = [(13, 2), (17, 3), (2408561, 6)]          # (p, g); Carrier last

    for p, g in CASES:
        kap = (p - 1) // 4
        pi = 2 * kap
        # L1: ladder bounds and midpoint straddle
        # 8:F2 (p08039)
        chk(f"L1 p={p} in-ladder", 1 <= kap + 1 <= pi)
        chk(f"L1 p={p} past-half", kap + 1 == pi // 2 + 1 and pi % 2 == 0)
        # L2: meridian shift by kappa is the quarter-turn
        gk = pow(g, kap, p)
        chk(f"L2 p={p} g^kappa = +-i", pow(gk, 2, p) == p - 1)
        ray = [a % p for a in range(1, pi + 1)]        # prime meridian labels
        chk(f"L2 p={p} ray*i = quarter-turn ray",
            [(a * gk) % p for a in ray] == [(a * gk) % p for a in range(1, pi + 1)]
            and (1 * gk) % p == gk)                    # unit -> quarter-turn
        chk(f"L2 p={p} latitude shift 1 -> kappa+1", 1 + kap == kap + 1)
        # L3: radius register
        chk(f"L3 p={p} kappa = -1/4", kap % p == (p - inv(4, p)) % p)
        chk(f"L3 p={p} energy radius = 3/4 = 1 - 1/4",
            (kap + 1) % p == 3 * inv(4, p) % p == (1 - inv(4, p)) % p)
        # L4: terminal latitude residue identities
        inv2 = inv(2, p)
        chk(f"L4 p={p} pi = -2^-1", pi % p == (p - inv2) % p)
        chk(f"L4 p={p} pi = -c^2", (p - pi) % p == inv2)  # -pi = 2^-1 = c^2
        # L5: unit-norm circle count = p-1 = |phase cycle| (p = 1 mod 4)
        if p < 100:
            cnt = sum(1 for a in range(p) for b in range(p)
                      if (a * a + b * b) % p == 1)
            chk(f"L5 p={p} |norm-1 circle| = p-1", cnt == p - 1)
        chk(f"L5 p={p} energy norm = 9/16",
            pow(kap + 1, 2, p) == 9 * inv(16, p) % p)

    # Carrier-register readings (B18 web)
    Om, S = 2408561, 602140
    chk("L4 Carrier 2S = G", (2 * S) % Om == 1204280)         # G = 2S
    chk("L4 Carrier -2S = c^2", (Om - 2 * S) % Om == (Om + 1) // 2)  # -pi = c^2
    chk("L3 Carrier S+1 = 3/4", (S + 1) % Om == 3 * inv(4, Om) % Om)
    flush("lat")

# ------------------------------------------------------------------------------------------------------------
# block o9 — signature as a square-class dichotomy (o9_signature_counts)
#
# O9 exact checks: signature is a square-class dichotomy on F_p (EXACT).
#
# Remark rem:signature-record (Section 2); ledger row 8:B7. All arithmetic exact; no floats.
#
# Claims checked, on every symmetry-complete shell p = 4k+1 < 60:
#   S1  The Euclidean form t^2+x^2+y^2+z^2 has p^3+p^2-p zeros in F_p^4
#       (square discriminant: hyperbolic, Witt index 2).
#   S2  The form -nu t^2+x^2+y^2+z^2 with nu the canonical nonsquare g has
#       p^3-p^2+p zeros (nonsquare discriminant: elliptic, Witt index 1).
#   S3  At p = 13 the counts are 2353 and 2041.
#   S4  Over F_{p^2} every element of F_p is a square: nu = w^2 for some
#       w in F_{p^2}, so the extension erases the dichotomy.
def is_prime(n):
    if n < 2: return False
    i = 2
    while i * i <= n:
        if n % i == 0: return False
        i += 1
    return True

def primitive_root(p):
    order = p - 1
    fac = []; m = order; d = 2
    while d * d <= m:
        if m % d == 0:
            fac.append(d)
            while m % d == 0: m //= d
        d += 1
    if m > 1: fac.append(m)
    for g in range(2, p):
        if all(pow(g, order // q, p) != 1 for q in fac): return g
    raise RuntimeError

def zero_count(p, a_t):
    # number of (t,x,y,z) with a_t*t^2 + x^2 + y^2 + z^2 = 0 in F_p
    sq = [0] * p
    for v in range(p): sq[v * v % p] += 1
    # distribution of x^2+y^2+z^2
    conv2 = [0] * p
    for u in range(p):
        for v in range(p):
            conv2[(u + v) % p] += sq[u] * sq[v]
    conv3 = [0] * p
    for u in range(p):
        for v in range(p):
            conv3[(u + v) % p] += conv2[u] * sq[v]
    total = 0
    for t in range(p):
        need = (-a_t * t * t) % p
        total += conv3[need]
    return total

def block_o9():
    """Block o9 — signature as a square-class dichotomy (EXACT): o9.S1–S4."""
    ok1 = ok2 = ok4 = True; c13 = None
    for p in range(5, 60):
        if not is_prime(p) or p % 4 != 1: continue
        g = primitive_root(p)
        e = zero_count(p, 1)
        q = zero_count(p, (-g) % p)   # the form -g t^2 + x^2 + y^2 + z^2
        ok1 &= e == p**3 + p**2 - p
        ok2 &= q == p**3 - p**2 + p
        ok4 &= (p * p - 1) // 2 % (p - 1) == 0      # F_p^x has order p-1 | (p^2-1)/2: every a in F_p^x is a square in F_{p^2}
        if p == 13: c13 = (e, q)
    # 8:B7 (p08013)
    check("o9.S1", ok1, "p = 5 … 53, p ≡ 1 (mod 4)")
    check("o9.S2", ok2, "ν = g the smallest primitive root")
    check("o9.S3", c13 == (2353, 2041), f"p = 13: {c13}")
    check("o9.S4", ok4, "(p² − 1)/2 ≡ 0 (mod p − 1)")

if __name__ == "__main__":
    import time
    want = [a.lower() for a in sys.argv[1:]] or list(BLOCK)
    bad = [b for b in want if b not in BLOCK]
    if bad: sys.exit(f"no block {', '.join(bad)}: the blocks are {', '.join(BLOCK)}")
    t0 = time.time()
    for b in want:
        t = time.time(); print(f"— block {b}"); _run_block(b); print(f"    [block {b}: {time.time() - t:.1f} s]")
    ok = summary(write=(want == list(BLOCK)))
    print(f"{len(RESULTS)} family checks, {len(MICRO)} exact micro-checks, {time.time() - t0:.0f} s" + ("; results.json written" if want == list(BLOCK) else ""))
    sys.exit(0 if ok else 1)
