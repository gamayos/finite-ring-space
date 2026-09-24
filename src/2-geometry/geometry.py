"""
geometry.py — the validation package of "Geometry and Constants in Finite Ring Continuum" (Akhtman, Symmetry 2026, 18, 751;
doi 10.3390/sym18050751), the paper 2-geometry of the FRC corpus (finite-ring-space/src/2-geometry), added with the paper's
predicate ledger (Appendix A, 17 September 2026, from the corpus script validation/verify_geometry.py; one script since
24 September 2026, the four block scripts merged).
========================================================================================================================

One script, four blocks, eighteen checks, standard library only. Each check names the predicate(s) of the paper's ledger it
witnesses (LEDGER below; predicates cited as 2:XN) under a `# 2:XN (<key>)` marker, the key the predicate's accession key,, and the ledger's source column links the
marker of the check that decides each predicate (PREDICATES below; finitering.space/src/2-geometry/#<key>).
Where a predicate is proved in Lean (lean/FrcLedger/Geometry.lean on Mathlib, or lean/FrcCore with no axioms), the check here
is the instance the reader can run; the witnesses decide the same statements at different generality.

    python3 geometry.py           every block, results.json written; exit 1 if a check fails (≈ 2 s)
    python3 geometry.py C         one block (A, B, C or D); no results.json
    from frc_2_geometry import predicate; predicate("2:D1")    one predicate: its block runs once per session

Blocks:  A  the Euclidean datum and the involutions                 EXACT          (2:B3, D1–D8)
         B  the orbital shell and its spherical completion          EXACT          (2:B4, C2–C4)
         C  the external spherical comparison                       CHART / EXACT  (2:E2–E4)
         D  Fourier duality on the phase cycle                      EXACT / CHART  (2:F1, F3–F6)

Everything the blocks share:
  * the shell datum: p = 4κ+1 prime, the primitive generators of F_p, the oriented quarter-turn i = −g^κ,
    the half-period π = 2κ, the phase cycle of length n = p − 1;
  * exact arithmetic in F_p (python int, reduced mod p) and in Q (fractions.Fraction);
  * the PASS/FAIL registry every block reports into (results.json).

Kinds: EXACT checks are integer-pinned computations in F_p or exact rationals (a pass is a proof on the tested
instances); CHART checks decide a [chart] predicate — the reading of the shell against R or C — in floats with the
closed forms checked.
"""
import os, json, sys, math, random
from collections import Counter, defaultdict
from fractions import Fraction

SCRIPT = os.path.splitext(os.path.basename(__file__))[0]        # "geometry": the one script, the name results.json and the site pages carry

# The shells (p, κ): p = 4κ+1 prime.
SHELLS = [(5, 1), (13, 3), (17, 4), (29, 7), (37, 9), (41, 10)]

# ----------------------------------------------------------------------------- registry
RESULTS = []

# The paper's predicate ledger (Appendix A, predicates cited as 2:XN): the predicate(s) each check witnesses.
LEDGER = {
    "A1": "2:D1, 2:D2, 2:D3, 2:D4", "A2": "2:B3", "A3": "2:D5", "A4": "2:D6", "A5": "2:D7", "A6": "2:D8",
    "B1": "2:C2", "B2": "2:C3", "B3": "2:B4, 2:C4",
    "C1": "2:E2", "C2": "2:E3", "C2b": "2:E3", "C3": "2:E4",
    "D1": "2:F1", "D2": "2:F3", "D3": "2:F4", "D4": "2:F5", "D5": "2:F6",
}

BLOCK = {"A": "the Euclidean datum and the involutions",                 # check-id prefix -> the block (the function block_<letter> below)
         "B": "the orbital shell and its spherical completion",
         "C": "the external spherical comparison",
         "D": "Fourier duality on the phase cycle"}

# the deciding check of each witnessed predicate: the one whose verdict decides the predicate's statement (the other checks that
# touch it are corroboration, listed by predicate() from the records)
PREDICATES = {
    "2:B3": "A2", "2:B4": "B3",
    "2:C2": "B1", "2:C3": "B2", "2:C4": "B3",
    "2:D1": "A1", "2:D2": "A1", "2:D3": "A1", "2:D4": "A1", "2:D5": "A3", "2:D6": "A4", "2:D7": "A5", "2:D8": "A6",
    "2:E2": "C1", "2:E3": "C2", "2:E4": "C3",
    "2:F1": "D1", "2:F3": "D2", "2:F4": "D3", "2:F5": "D4", "2:F6": "D5",
}
_RAN = set()                                            # blocks already run in this session (predicate() runs each once)

def check(pid, label, ok, detail="", kind="EXACT"):
    """Record one predicate check. pid = package check id; LEDGER[pid] = the paper statement(s) decided."""
    ok = bool(ok)
    rows = LEDGER.get(pid, "")
    RESULTS.append({"id": pid, "rows": rows, "block": pid[0], "script": SCRIPT, "label": label, "ok": ok, "detail": detail, "kind": kind})
    print(f"  [{'PASS' if ok else 'FAIL'}] {pid:4s} {kind:6s} [{rows}] {label}" + (f"  --  {detail}" if detail else ""))
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
    """Verify one ledger predicate: run the block of the check that decides it (once per session), print that check's source
    (from its marker) and every record that cites the predicate, and return True iff all pass."""
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

# ----------------------------------------------------------------------------- the shell datum
def is_prime(n):
    return n > 1 and all(n % q for q in range(2, int(n ** .5) + 1))

def order(x, p):
    """The multiplicative order of x in F_p^x."""
    k, y = 1, x % p
    while y != 1:
        y = y * x % p; k += 1
    return k

def generators(p):
    """The primitive generators of F_p^x, in increasing order."""
    return [g for g in range(2, p) if order(g, p) == p - 1]

def units(n):
    """The units of Z_n: u in [1, n) coprime to n."""
    return [u for u in range(1, n) if math.gcd(u, n) == 1]

def kappa(p):
    assert is_prime(p) and p % 4 == 1, p
    return (p - 1) // 4

def quarter_turn(p, g):
    """The oriented quarter-turn i = −g^κ (00:C7, 2:A2)."""
    return (-pow(g, kappa(p), p)) % p

for _p, _k in SHELLS:
    assert is_prime(_p) and _p == 4 * _k + 1, (_p, _k)

# ------------------------------------------------------------------------------------------------------------
# block A: the Euclidean datum and the involutions (2:B3, D1–D8)
# Section 2 (the frame) and Section 4 (symmetry axes and structural data) of the paper, on the shells
# p ∈ {5, 13, 17, 29, 37, 41} and every primitive generator.  \label(s): prop:half-period,
# def:quarter-turn-subgroup, prop:quarter-turn, rem:observer-canonical-e, rem:exponential-unit (A1);
# prop:primitive-orbit, prop:no-canonical-e (A2); rem:frame-transport (A3); the Euler identity of 00:C14 (A4);
# prop:shell-negation, prop:k4-shell (A5); rem:euclidean-conjugation (A6).
def block_A():
    """Block A — the Euclidean datum and the involutions (EXACT): A1–A6."""
    # A1 half-period, quarter-turn of order four, i = −g^κ with i² = −1, 2π = −1, e = g^i (2:D1–D4)
    ok = True; det = []
    for p, k in SHELLS:
        pi = 2 * k
        for g in generators(p):
            i = quarter_turn(p, g)
            ok &= pow(g, pi, p) == p - 1 and (i * i) % p == p - 1 and pow(g, 4 * k, p) == 1 and order(pow(g, k, p), p) == 4
            ok &= (2 * pi) % p == p - 1
            Q = {x for x in range(1, p) if pow(x, 4, p) == 1}
            ok &= Q == {1, p - 1, i, (-i) % p}
        g = generators(p)[0]; i = quarter_turn(p, g)
        det.append(f"p={p}: g={g}, i={i}, e=g^i={pow(g, i, p)}, pi={pi}")
    # 2:D1 (p02013), 2:D2 (p02014), 2:D3 (p02015), 2:D4 (p02016)
    check("A1", "half-period g^pi = -1; i = -g^k of order 4 with i^2 = -1; Q_p = {±1, ±i}; 2pi = -1; e = g^i", ok, "; ".join(det[:3]))

    # A2 the primitive generators form one orbit g^u, u a unit mod p−1 (2:B3)
    ok = True
    for p, k in SHELLS:
        gens = set(generators(p)); g = min(gens)
        orbit = {pow(g, u, p) for u in units(p - 1)}
        ok &= orbit == gens and len(gens) == len(units(p - 1))
    # 2:B3 (p02007)
    check("A2", "generators = {g^u : gcd(u, p-1) = 1}, one Aut(C_{p-1})-torsor", ok)

    # A3 orientation classes: i' = i iff u ≡ 1 (mod 4), i' = −i iff u ≡ 3 (mod 4) (2:D5)
    ok = True; det = []
    for p, k in SHELLS:
        g = generators(p)[0]; i = quarter_turn(p, g)
        for u in units(p - 1):
            ip = quarter_turn(p, pow(g, u, p))
            ok &= (ip == i) == (u % 4 == 1) and (ip == (-i) % p) == (u % 4 == 3)
        same = sum(1 for u in units(p - 1) if u % 4 == 1)
        det.append(f"p={p}: {same} of {len(generators(p))} generators keep i")
    # 2:D5 (p02017)
    check("A3", "orientation classes of the quarter-turn under g -> g^u: kept for u = 1, flipped for u = 3 (mod 4)", ok, "; ".join(det))

    # A4 the Euler identity e^{iπ} = g^{2κ i²} = (−1)^i, −1 iff the residue i is odd (2:D6, 00:C14)
    ok = True; det = []
    for p, k in SHELLS:
        for g in generators(p):
            i = quarter_turn(p, g); e = pow(g, i, p)
            ok &= pow(e, i * 2 * k, p) == (p - 1 if i % 2 else 1)
        odd = [g for g in generators(p) if quarter_turn(p, g) % 2 == 1]
        det.append(f"p={p}: i odd for g in {odd[:6]}{'...' if len(odd) > 6 else ''} ({len(odd)}/{len(generators(p))})")
    ok &= quarter_turn(13, 2) == 5 and quarter_turn(17, 3) == 4 and quarter_turn(17, 6) == 13
    # 2:D6 (p02018)
    check("A4", "Euler identity e^{i pi} = (-1)^i with i the residue representative; F13 g=2 odd, F17 g=3 even", ok, "; ".join(det[:3]))

    # A5 negation/inversion orbits: F_p^x \ Q_p splits into κ−1 orbits of size four (2:D7, 1:B2)
    ok = True
    for p, k in SHELLS:
        Q = {x for x in range(1, p) if pow(x, 4, p) == 1}
        seen, orbits = set(), 0
        for x in range(1, p):
            if x in Q or x in seen: continue
            orb = {x, (-x) % p, pow(x, -1, p), (-pow(x, -1, p)) % p}
            ok &= len(orb) == 4; seen |= orb; orbits += 1
        ok &= len(Q) == 4 and orbits == k - 1
        R = lambda x: (-x) % p; I = lambda x: pow(x, -1, p)
        ok &= all(R(R(x)) == x and I(I(x)) == x and R(I(x)) == I(R(x)) for x in range(1, p))
    # 2:D7 (p02019)
    check("A5", "R, I commuting involutions; <R,I>-orbits off Q_p have four elements, k-1 of them", ok)

    # A6 Euclidean conjugation: an involution of pairs; the pair map (a, b) -> a + b i is p-to-one (2:D8)
    ok = True
    for p, k in SHELLS:
        g = generators(p)[0]; i = quarter_turn(p, g)
        fibres = Counter((a + b * i) % p for a in range(p) for b in range(p))
        ok &= set(fibres.values()) == {p} and len(fibres) == p
        C = lambda a, b: (a, (-b) % p)
        ok &= all(C(*C(a, b)) == (a, b) for a in range(p) for b in range(p))
        a, b = 0, 1; a2, b2 = i, 0        # 0 + 1·i = i + 0·i, but the conjugates differ: not a map of the field
        ok &= (a + b * i) % p == (a2 + b2 * i) % p and (a - b * i) % p != (a2 - b2 * i) % p
    # 2:D8 (p02020)
    check("A6", "conjugation is an involution of the pairs, not of the field (the pair map is p-to-one)", ok)

# ------------------------------------------------------------------------------------------------------------
# block B: the orbital shell and its spherical completion (2:B4, C2, C3, C4)
# Section 3 of the paper: the complex S_p of def:orbital-shell coded as vertices, edges and faces; the
# completion (the terminal latitude collapsed to S); the counts of rem:cell-counts (B1); closedness — every edge
# in two faces, every vertex link one cycle — of thm:combinatorial-sphere, exhaustive on p ∈ {5, 13, 17, 29} (B2);
# the cellular automorphisms: the reindexing ρ_u is cellular only for u = ±1, the dihedral maps are, the meridian
# reversal is a map of the completion only (prop:phase-frame-change, prop:shell-covariance; B3).
B_SHELLS = (5, 13, 17, 29)                    # the shells of block B (the package's SHELLS carry κ)

def shell(p):
    """The orbital shell S_p of Def. 3.1: vertices, edges, faces; and its completion."""
    k = (p - 1) // 4; pi = 2 * k; n = p - 1
    V = ["N"] + [(a, m) for a in range(1, pi + 1) for m in range(n)]
    E = set()
    for m in range(n):
        E.add(frozenset(["N", (1, m)]))
        for a in range(1, pi): E.add(frozenset([(a, m), (a + 1, m)]))
        for a in range(1, pi + 1): E.add(frozenset([(a, m), (a, (m + 1) % n)]))
    F = []
    for m in range(n):
        F.append(("N", (1, m), (1, (m + 1) % n)))
        for a in range(1, pi): F.append(((a, m), (a + 1, m), (a + 1, (m + 1) % n), (a, (m + 1) % n)))
    col = lambda v: "S" if (v != "N" and v[0] == pi) else v      # the completion: L_pi collapsed to S
    Vc = sorted({col(v) for v in V}, key=str)
    Ec = {frozenset(map(col, e)) for e in E if len({col(v) for v in e}) == 2}
    Fc = []
    for f in F:
        cf = []
        for v in map(col, f):
            if v not in cf: cf.append(v)
        Fc.append(tuple(cf))
    return V, E, F, Vc, Ec, Fc

def closed_surface(V, E, F):
    """Every edge in exactly two faces; every vertex link a single cycle."""
    edge_faces = defaultdict(list)
    for fi, f in enumerate(F):
        for j in range(len(f)): edge_faces[frozenset([f[j], f[(j + 1) % len(f)]])].append(fi)
    if set(edge_faces) != set(E) or any(len(v) != 2 for v in edge_faces.values()): return False
    for v in V:
        around = [fi for fi, f in enumerate(F) if v in f]
        adj = defaultdict(set)
        for fi in around:
            f = F[fi]; j = f.index(v)
            for w in (f[(j - 1) % len(f)], f[(j + 1) % len(f)]):
                for fj in edge_faces[frozenset([v, w])]:
                    if fj != fi: adj[fi].add(fj)
        if any(len(s) != 2 for s in adj.values()): return False
        seen, stack = set(), [around[0]]
        while stack:
            x = stack.pop()
            if x in seen: continue
            seen.add(x); stack.extend(adj[x])
        if seen != set(around): return False
    return True

def block_B():
    """Block B — the orbital shell and its spherical completion (EXACT): B1–B3."""
    # B1 the counts and the Euler characteristics (2:C2)
    ok = True; det = []
    for p in B_SHELLS:
        k = (p - 1) // 4; pi = 2 * k; n = p - 1
        V, E, F, Vc, Ec, Fc = shell(p)
        ok &= (len(V), len(E), len(F)) == (pi * n + 1, 2 * pi * n, pi * n) and len(V) - len(E) + len(F) == 1
        ok &= (len(Vc), len(Ec), len(Fc)) == ((pi - 1) * n + 2, (2 * pi - 1) * n, pi * n) and len(Vc) - len(Ec) + len(Fc) == 2
        det.append(f"p={p}: |V|,|E|,|F| = {len(V)},{len(E)},{len(F)}, chi=1; completion {len(Vc)},{len(Ec)},{len(Fc)}, chi=2")
    # 2:C2 (p02010)
    check("B1", "cell counts of S_p and of its completion, chi = 1 and chi = 2 (Remark 3.4)", ok, "; ".join(det))

    # B2 the completion is a closed surface (chi = 2, a sphere); S_p itself is not closed (2:C3)
    ok = True; det = []
    for p in B_SHELLS:
        V, E, F, Vc, Ec, Fc = shell(p)
        closed = closed_surface(Vc, Ec, Fc)
        ok &= closed and not closed_surface(V, E, F)
        det.append(f"p={p}: completion closed={closed}, S_p closed=False")
    # 2:C3 (p02011)
    check("B2", "the completion is a closed surface with chi = 2 (a sphere) by exhaustive incidence; S_p has a boundary", ok, "; ".join(det))

    # B3 cellular automorphisms: rho_u iff u = ±1; the dihedral maps; meridian reversal on the completion only (2:B4, 2:C4)
    ok = True; det = []
    for p in B_SHELLS:
        k = (p - 1) // 4; pi = 2 * k; n = p - 1
        V, E, F, Vc, Ec, Fc = shell(p)
        faces = lambda FF, f: sorted(Counter(tuple(sorted(map(str, map(f, x)))) for x in FF).items())
        cellular = lambda f, EE, FF: {frozenset(map(f, e)) for e in EE} == EE and faces(FF, f) == faces(FF, lambda v: v)
        good = []
        for u in units(n):
            rho = lambda v: v if v in ("N", "S") else (v[0], v[1] * u % n)
            if cellular(rho, E, F): good.append(u)
            ok &= cellular(rho, E, F) == (u in (1, n - 1)) and cellular(rho, Ec, Fc) == (u in (1, n - 1))
        for c in range(n):
            for s_ in (1, -1):
                dih = lambda v: v if v in ("N", "S") else (v[0], (s_ * v[1] + c) % n)
                ok &= cellular(dih, E, F)
        sig = lambda v: "S" if v == "N" else "N" if v == "S" else (pi - v[0], v[1])
        ok &= cellular(sig, Ec, Fc)
        ok &= sum(1 for v in V if v == "N") == 1 and sum(1 for v in V if v != "N" and v[0] == pi) == n
        det.append(f"p={p}: rho_u cellular only for u in {good} of {len(units(n))} units")
    # 2:B4 (p02008), 2:C4 (p02012)
    check("B3", "rho_u (m -> um) is cellular iff u = ±1; the dihedral maps are; meridian reversal is a map of the completion only", ok, "; ".join(det))

# ------------------------------------------------------------------------------------------------------------
# block C: the external spherical comparison (2:E2, E3, E4)
# Section 5 of the paper.  C1 (CHART): the base-grid covering radius of the comparison map Xi_{13,g} against the
# bound sqrt2·pi/(p−1) of prop:grid-density.  C2 (EXACT, rationals): the fixed-shell scale grid {x/g^n : |x| ≤ 2κ}
# has a covering radius in [0, 1] bounded below by ½ min(g^−m, 1 − 2κ g^−(m+1)) at every depth — the bounded
# precision of a fixed shell, prop:fixed-shell-density and thm:operational-precision (C2b: the covering radius
# exceeds ε = 1/20 on every tested shell).  C3 (CHART): across the tower of shells the grids resolve every target (1:G2).
def fib_sphere(N):
    pts = []
    ga = math.pi * (3 - math.sqrt(5))
    for j in range(N):
        z = 1 - 2 * (j + .5) / N; r = math.sqrt(1 - z * z); t = ga * j
        pts.append((r * math.cos(t), r * math.sin(t), z))
    return pts

def geod(u, v): return math.acos(max(-1., min(1., u[0] * v[0] + u[1] * v[1] + u[2] * v[2])))

def fixed_shell_radius(p, g, N, H=None):
    """Covering radius in [0,1] of {x/g^n : 0 <= x <= H, n <= N}; H = 2κ (the balanced window) by default."""
    k = (p - 1) // 4; H = 2 * k if H is None else H
    pts = sorted({Fraction(x, g ** n) for n in range(N + 1) for x in range(0, H + 1) if x <= g ** n})
    return max(b - a for a, b in zip(pts, pts[1:])) / 2

def lower_bound(p, g, H=None):
    """½ min(g^−m, 1 − H g^−(m+1)) with m = floor(log_g(H+1)): the cut of lean fixed_shell_bound."""
    k = (p - 1) // 4; H = 2 * k if H is None else H; m = 0
    while g ** (m + 1) <= H + 1: m += 1
    return min(Fraction(1, g ** m), 1 - Fraction(H, g ** (m + 1))) / 2

def tower_best(t, shells, N=12):
    best = 1.
    for p, g in shells:
        k = (p - 1) // 4
        for n in range(N + 1):
            for x in range(0, 2 * k + 1):
                best = min(best, abs(t - x / g ** n))
    return best

def block_C():
    """Block C — the external spherical comparison (C1, C3 CHART; C2 EXACT rationals): C1–C3."""
    # C1 the base-grid covering radius at p = 13 within sqrt2·pi/(p−1) (2:E2) — chart
    p = 13; pi = 6; n = 12
    grid = [(0., 0., 1.), (0., 0., -1.)]
    for a in range(1, pi + 1):
        th = math.pi * a / pi
        for m in range(n):
            ph = 2 * math.pi * m / n
            grid.append((math.sin(th) * math.cos(ph), math.sin(th) * math.sin(ph), math.cos(th)))
    cov = max(min(geod(x, y) for y in grid) for x in fib_sphere(60000))
    bound = math.sqrt(2) * math.pi / (p - 1)
    # 2:E2 (p02022)
    check("C1", "base-grid covering radius at p = 13 within the bound sqrt2 pi/(p-1)", cov <= bound,
             f"measured {cov:.4f} rad, bound {bound:.4f} rad", kind="CHART")

    # C2 the fixed-shell refinement is bounded (2:E3) — exact rationals
    ok = True; det = []
    for p, g in [(13, 2), (13, 11), (13, 6), (17, 3), (29, 2), (173, 2)]:
        radii = [fixed_shell_radius(p, g, N) for N in (3, 6, 12, 24)]
        lb = lower_bound(p, g)
        radii_p = [fixed_shell_radius(p, g, N, p - 1) for N in (12, 24)]; lb_p = lower_bound(p, g, p - 1)
        ok &= all(r >= lb for r in radii) and radii[-1] == radii[-2] and all(r >= lb_p for r in radii_p) and radii_p[0] == radii_p[1]
        det.append(f"({p},{g}): radius {radii[-1]} >= {lb}")
    # 2:E3 (p02023)
    check("C2", "fixed-shell covering radius stabilises at >= 1/2 min(g^-m, 1 - H g^-(m+1)) for every depth (H = 2k and H = p-1)", ok, "; ".join(det[:4]))
    eps = Fraction(1, 20)
    viol = [(p, g) for p, g in [(13, 2), (13, 11), (17, 3), (29, 2)] if fixed_shell_radius(p, g, 40) > eps]
    check("C2b", "fixed-shell density at eps = 1/20: the covering radius exceeds 1/20 on every tested shell", viol == [(13, 2), (13, 11), (17, 3), (29, 2)],
             f"shells with covering radius > 1/20 at N = 40: {viol}")

    # C3 the tower of shells resolves every target (2:E4, 1:G2) — chart
    targets = [0.9, 1 / 3, math.pi / 4, math.sqrt(2) - 1]
    tower = [(p, 2) for p in (13, 29, 173, 1013, 4093)]
    errs = [tower_best(t, tower) for t in targets]
    single = [tower_best(t, [(13, 2)]) for t in targets]
    # 2:E4 (p02024)
    check("C3", "the tower of shells (p = 13..4093, g = 2) brings every target within 1/2048; the single shell (13, 2) does not",
             all(e <= 1 / 2048 for e in errs) and max(single) > 1 / 16,
             "tower errors " + ", ".join(f"{e:.2e}" for e in errs) + "; single shell " + ", ".join(f"{e:.3f}" for e in single), kind="CHART")

# ------------------------------------------------------------------------------------------------------------
# block D: Fourier duality on the phase cycle (2:F1, F3, F4, F5, F6)
# Section 6 of the paper, on (13, 2), (13, 11), (17, 3), (29, 2): the principal root (prop:principal-root, D1);
# the inversion W^−1 = −(g^−jk) (prop:ring-dft-inverse, D2); the polynomial reading F(v)_k = P_v(g^k)
# (prop:polynomial-form, D3); the covariance under g → g^u (prop:ring-dft-covariance, D4); and the external
# transport chi(g^m) = exp(−2 pi i m/n) with its step, half-period and quarter-turn identities
# (prop:datum-role-transport, D5; CHART).
FRAMES = [(13, 2), (13, 11), (17, 3), (29, 2)]

def dft_checks(p, g):
    n = p - 1; k = (p - 1) // 4
    W = [[pow(g, j * kk, p) for j in range(n)] for kk in range(n)]
    Winv = [[(-pow(g, -j * kk, p)) % p for j in range(n)] for kk in range(n)]
    mul = lambda A, B: [[sum(A[r][t] * B[t][c] for t in range(n)) % p for c in range(n)] for r in range(n)]
    I = [[int(r == c) for c in range(n)] for r in range(n)]
    d1 = pow(g, n, p) == 1 and all(sum(pow(g, j * kk, p) for j in range(n)) % p == 0 for kk in range(1, n)) and (n * (p - 1)) % p == 1
    d2 = mul(W, Winv) == I and mul(Winv, W) == I
    rnd = random.Random(p)
    v = [rnd.randrange(p) for _ in range(n)]
    Fv = [sum(v[j] * pow(g, j * kk, p) for j in range(n)) % p for kk in range(n)]
    Pv = lambda x: sum(v[j] * pow(x, j, p) for j in range(n)) % p
    d3 = all(Fv[kk] == Pv(pow(g, kk, p)) for kk in range(n))
    d4 = True
    for u in units(n):
        gp = pow(g, u, p); vp = [v[u * j % n] for j in range(n)]
        Fvp = [sum(vp[j] * pow(gp, j * kk, p) for j in range(n)) % p for kk in range(n)]
        d4 &= Fvp == Fv
    chi = lambda m: complex(math.cos(-2 * math.pi * m / n), math.sin(-2 * math.pi * m / n))
    i = quarter_turn(p, g); li = next(m for m in range(n) if pow(g, m, p) == i)
    d5 = all(abs(chi(m + 1) - chi(1) * chi(m)) < 1e-12 and abs(chi(m + 2 * k) + chi(m)) < 1e-12
             and abs(chi(m + li) - 1j * chi(m)) < 1e-12 for m in range(n))
    d5 &= len({(round(chi(m).real, 9), round(chi(m).imag, 9)) for m in range(n)}) == n
    return d1, d2, d3, d4, d5

def block_D():
    """Block D — Fourier duality on the phase cycle (EXACT; D5 CHART): D1–D5."""
    ok = [True] * 5
    for p, g in FRAMES:
        d = dft_checks(p, g); ok = [a and b for a, b in zip(ok, d)]
    # 2:F1 (p02025)
    check("D1", "g a principal root: g^n = 1, sum_j g^{jk} = 0 for 0 < k < n, n^-1 = -1", ok[0])
    # 2:F3 (p02027)
    check("D2", "inversion W^-1 = -(g^{-jk}) on (13, 2), (13, 11), (17, 3), (29, 2)", ok[1])
    # 2:F4 (p02028)
    check("D3", "polynomial reading F(v)_k = P_v(g^k)", ok[2])
    # 2:F5 (p02029)
    check("D4", "covariance F_{g^u}(v') = F_g(v) with v'_j = v_{uj}", ok[3])
    # 2:F6 (p02030)
    check("D5", "external transport chi(g^m) = exp(-2 pi i m/n), injective: step, half-period, quarter-turn", ok[4], kind="CHART")

if __name__ == "__main__":
    import time
    want = [a.upper() for a in sys.argv[1:]] or sorted(BLOCK)
    bad = [b for b in want if b not in BLOCK]
    if bad: sys.exit(f"no block {', '.join(bad)}: the blocks are {', '.join(sorted(BLOCK))}")
    t0 = time.time()
    for b in want:
        t = time.time(); _run_block(b); print(f"    [block {b}: {time.time() - t:.1f} s]")
    ok = summary(write=(want == sorted(BLOCK)))
    kinds = {}
    for r in RESULTS: kinds[r["kind"]] = kinds.get(r["kind"], 0) + 1
    print("by kind: " + ", ".join(f"{k} {v}" for k, v in sorted(kinds.items())) + f"; {len(RESULTS)} checks in {time.time() - t0:.1f} s" + ("; results.json written" if want == sorted(BLOCK) else ""))
    sys.exit(0 if ok else 1)
