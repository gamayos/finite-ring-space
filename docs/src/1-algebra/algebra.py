"""
algebra.py — the validation package of "Relativistic Algebra over Finite Ring Continuum" (Akhtman, Axioms 2025, 14, 636;
doi 10.3390/axioms14080636), the paper 1-algebra of the FRC corpus (finite-ring-space/src/1-algebra), added with the paper's
predicate ledger (Appendix A, 16 September 2026; one script since 24 September 2026, the three block scripts merged).
========================================================================================================================

One script, three blocks, sixteen checks, standard library only. Each check names the predicate(s) of the paper's ledger
it witnesses (LEDGER below; predicates cited as 1:XN) under a `# predicate 1:XN` marker, and the ledger's source column
links the marker in return (finitering.space/src/1-algebra/algebra.html#<key>). The paper \\label(s) a check decides are
in the block banners. Seven master-ledger predicates of the corpus cite this paper (00:A8, B1, B8, B11, C9, C10, Y3); the
predicates of the paper ledger that the master carries are listed in the site generator.

    python3 algebra.py            every block, results.json written; exit 1 if a check fails (≈ 25 s)
    python3 algebra.py C          one block (A, B or C); no results.json
    from frc_1_algebra import predicate; predicate("1:B2")     one predicate: its block runs once per session

Blocks:  A  the shell, its frame and the orbital complex          EXACT          (1:B2–B4, C2, C4)
         B  the framed numbers, the charts and the horizon         EXACT / CHART  (1:D2, D4, D6, E2, F1; B6 decides no predicate)
         C  the conjecture of the conclusion, clause by clause     EXACT / CHART  (1:G1–G5)

Everything the blocks share:
  * the shell datum: p = 4κ+1 prime, the primitive roots of F_p, the oriented quarter-turn i = −g^κ;
  * exact arithmetic in F_p (python int, reduced mod p) and in Q (fractions.Fraction);
  * the PASS/FAIL registry every block reports into (results.json).

Kinds: EXACT checks are integer-pinned computations in F_p or exact rationals (a pass is a proof on the
tested instances); CHART checks decide a [chart] predicate — a statement about the reading of the shell against
Q or R — in exact rationals.
"""
import os, json, sys, math, random, itertools
from fractions import Fraction
from decimal import Decimal, getcontext

SCRIPT = os.path.splitext(os.path.basename(__file__))[0]        # "algebra": the one script, the name results.json and the site pages carry

# The shells: p = 4κ+1 prime; the controls: p ≡ 3 (mod 4).
SHELLS = [5, 13, 17, 29, 37, 41, 173]
CONTROLS = [7, 11, 19, 23]

# ----------------------------------------------------------------------------- registry
RESULTS = []

# The paper's predicate ledger (Appendix A, predicates cited as 1:XN): the predicate(s) each check witnesses.
LEDGER = {
    "A1": "1:B2", "A2": "1:B3", "A3": "1:B4", "A4": "1:C2", "A5": "1:C4",
    "B1": "1:D2", "B2": "1:D4", "B3": "1:D6", "B4": "1:E2", "B5": "1:F1", "B6": "",          # B6 (the Euclidean step count) decides no predicate of the ledger
    "C1": "1:G1", "C2": "1:G2", "C3": "1:G3", "C4": "1:G4", "C5": "1:G5",
}

BLOCK = {"A": "the shell, its frame and the orbital complex",             # check-id prefix -> the block (the function block_<letter> below)
         "B": "the framed numbers, the charts and the horizon",
         "C": "the conjecture of the conclusion, clause by clause"}

# the deciding check of each witnessed predicate: the one whose verdict decides the predicate's statement (the other checks that
# touch it are corroboration, listed by predicate() from the records)
PREDICATES = {
    "1:B2": "A1", "1:B3": "A2", "1:B4": "A3", "1:C2": "A4", "1:C4": "A5",
    "1:D2": "B1", "1:D4": "B2", "1:E2": "B4", "1:F1": "B5",                       # D6: B3 witnesses it in LEDGER but carries no marker (as before the merge)
    "1:G1": "C1", "1:G2": "C2", "1:G3": "C3", "1:G4": "C4", "1:G5": "C5",
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
    """predicate label -> (script file, line) of its `# predicate …` marker: the line of the check that decides it."""
    import re
    out = {}
    for i, line in enumerate(open(os.path.abspath(__file__), encoding="utf-8"), 1):
        m = re.match(r"\s*# predicate (.*)", line)
        if m:
            for lab in m.group(1).split(","): out.setdefault(lab.strip(), (SCRIPT + ".py", i))
    return out

def _run_block(letter):
    if letter not in _RAN:
        globals()[f"block_{letter}"](); _RAN.add(letter)

def predicate(label, lines=14):
    """Verify one ledger predicate: run the block of the check that decides it (once per session), print that check's source
    (from its `# predicate` marker) and every record that cites the predicate, and return True iff all pass."""
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
    if n < 2: return False
    d = 2
    while d * d <= n:
        if n % d == 0: return False
        d += 1
    return True

def prime_factors(n):
    f, d = set(), 2
    while d * d <= n:
        while n % d == 0:
            f.add(d); n //= d
        d += 1
    if n > 1: f.add(n)
    return f

def primitive_roots(p):
    n = p - 1
    fac = prime_factors(n)
    return [g for g in range(2, p) if all(pow(g, n // q, p) != 1 for q in fac)]

def kappa(p):
    assert p % 4 == 1 and is_prime(p), p
    return (p - 1) // 4

def quarter_turn(p, g):
    """i = −g^κ, the oriented quarter-turn of the frame (τ; 0, 1, g)."""
    return (-pow(g, kappa(p), p)) % p

def sqrt_neg_one(p):
    return sorted(x for x in range(1, p) if (x * x) % p == p - 1)

# ------------------------------------------------------------------------------------------------------------
# block A: the shell, its frame and the orbital complex (EXACT, integer-pinned)
# Paper statements decided (Sections 2–3; ledger predicates 1:B2–B4, 1:C2, 1:C4):
#
#   A1  thm:symmetric-completeness   the fourth roots of unity are Q4 = {1, i, −1, −i}; under the Klein four-group
#       (1:B2)                       ⟨x ↦ −x, x ↦ x⁻¹⟩, Q4 is the union of the two size-2 orbits {±1}, {±i}, and
#                                    F_p^× \\ Q4 splits into exactly κ−1 orbits of size 4; for p ≡ 3 (mod 4) no i
#   A2  (1:B3)                       i = −g^κ satisfies i² = −1 for every primitive root g; {−g^κ, g^κ} are the two
#                                    square roots of −1; on F_13 with g = 2, i = 5
#   A3  def:framed-field,            φ_{a,b}(x) = a + bx is a ring isomorphism (F_p, +, ·) → (F_p, ⊕, ⊗) on every
#       lem:affine-invariance (1:B4) frame (a, b), b ≠ 0; the unit of the relabelled field is a + b, and b is the
#                                    unit only when a = 0
#   A4  prop:frame-group (1:C2)      ⟨T_a, S_m⟩ = Aff(F_p) of order p(p−1), simply transitive on the frames
#   A5  def:orbit-sphere (1:C4)      M_n(a) = M_{n+2κ}(−a), L_a(m) = L_{−a}(m+2κ); p−1 distinct meridian lists in
#                                    2κ great circles; 2κ latitude pairs; vertex count (p−1)²/2 + 1
#
# Shells: p ∈ {5, 13, 17, 29, 37, 41, 173} for A1–A2; p ∈ {13, 17} for A3–A5 (exhaustive over frames and pairs).
def klein_orbits(p):
    seen, orbits = set(), []
    for x in range(1, p):
        if x in seen: continue
        inv = pow(x, -1, p)
        orb = {x, (-x) % p, inv, (-inv) % p}
        seen |= orb; orbits.append(orb)
    return orbits

def block_A():
    """Block A — the shell, its frame and the orbital complex (EXACT, integer-pinned): A1–A5."""
    print("block A — the shell, its frame and the orbital complex")

    # A1 — symmetry completeness
    ok, det = True, []
    for p in SHELLS:
        k = kappa(p); orbits = klein_orbits(p)
        Q4 = {1, p - 1} | set(sqrt_neg_one(p))
        small = [o for o in orbits if len(o) < 4]
        big = [o for o in orbits if len(o) == 4]
        ok &= (len(Q4) == 4 and set().union(*small) == Q4 and sorted(len(o) for o in small) == [2, 2])
        ok &= (len(big) == k - 1 and len(big) + len(small) == k + 1)
        ok &= all(pow(x, 4, p) == 1 for x in Q4) and sum(1 for x in range(1, p) if pow(x, 4, p) == 1) == 4
        det.append(f"p={p}: Q4={sorted(Q4)}, {len(big)} orbits of size 4 = κ−1")
    for p in CONTROLS:
        orbits = klein_orbits(p)
        ok &= (sqrt_neg_one(p) == [] and sorted(len(o) for o in orbits) == [2] + [4] * ((p - 3) // 4))
    # predicate 1:B2
    check("A1", "Q4 = {1,i,−1,−i} the unique order-4 subgroup, two Klein orbits of size 2, κ−1 orbits of size 4; no i for p ≡ 3 (mod 4)",
          ok, "; ".join(det) + f"; controls p ∈ {CONTROLS}")

    # A2 — the oriented quarter-turn
    ok, det = True, []
    for p in SHELLS:
        k = kappa(p); roots = set(sqrt_neg_one(p)); n = 0
        for g in primitive_roots(p):
            i = quarter_turn(p, g)
            ok &= ((i * i) % p == p - 1) and ({i, pow(g, k, p)} == roots) and (pow(g, 2 * k, p) == p - 1); n += 1
        det.append(f"p={p}: {n} primitive roots")
    ok &= (quarter_turn(13, 2) == 5)
    # predicate 1:B3
    check("A2", "i = −g^κ, i² = −1 for every primitive root; {−g^κ, g^κ} the two square roots of −1; g^{2κ} = −1; F_13, g = 2: i = 5",
          ok, "; ".join(det))

    # A3 — the affine frame: ring isomorphism, the unit a + b
    ok, n = True, 0
    for p in [13, 17]:
        for a in range(p):
            for b in range(1, p):
                inv = lambda X: ((X - a) * pow(b, -1, p)) % p
                phi = lambda x: (a + b * x) % p
                oplus = lambda X, Y: (a + b * (inv(X) + inv(Y))) % p
                otimes = lambda X, Y: (a + b * (inv(X) * inv(Y))) % p
                ok &= all(phi((x + y) % p) == oplus(phi(x), phi(y)) and phi((x * y) % p) == otimes(phi(x), phi(y))
                          for x in range(p) for y in range(p))
                ok &= (len({phi(x) for x in range(p)}) == p)
                ok &= all(otimes((a + b) % p, y) == y for y in range(p))
                ok &= ((a == 0) == all(otimes(b, y) == y for y in range(p)))
                n += 1
    # predicate 1:B4
    check("A3", "φ_{a,b} = a + bx a ring isomorphism onto (F_p, ⊕, ⊗) on every frame; unit a + b; b the unit iff a = 0",
          ok, f"{n} frames on p ∈ {{13, 17}}, all pairs (x, y)")

    # A4 — the frame group
    ok, det = True, []
    for p in [13, 17]:
        frames = [(a, b) for a in range(p) for b in range(1, p)]
        comp = lambda f, g: ((f[0] + f[1] * g[0]) % p, (f[1] * g[1]) % p)     # f∘g as affine maps x ↦ a + b x
        ok &= (len(frames) == p * (p - 1))
        ok &= all(comp(f, g) in set(frames) for f in frames for g in frames)  # closure
        # simple transitivity: for each (φ, φ') exactly one ψ with ψ∘φ = φ'
        cnt = 0
        for f in frames:
            for f2 in frames:
                sols = [psi for psi in frames if comp(psi, f) == f2]
                ok &= (len(sols) == 1); cnt += 1
        det.append(f"p={p}: |Aff| = {len(frames)} = p(p−1), {cnt} frame pairs, one carrier each")
    # predicate 1:C2
    check("A4", "⟨T_a, S_m⟩ = Aff(F_p), order p(p−1), simply transitive on the frames (a, b)", ok, "; ".join(det))

    # A5 — the orbital complex: involutions and counts
    ok, det = True, []
    for p in [13, 17]:
        k = kappa(p); g = primitive_roots(p)[0]; n2 = 2 * k
        M = lambda n, a: (a * pow(g, n, p)) % p
        L = lambda a, m: (a * pow(g, m, p)) % p
        ok &= all(M(n, a) == M(n + n2, (-a) % p) for n in range(p - 1) for a in range(p))
        ok &= all(L(a, m) == L((-a) % p, m + n2) for a in range(1, p) for m in range(p - 1))
        mer = {tuple(M(n, a) for a in range(p)) for n in range(p - 1)}
        circles = {frozenset({tuple(M(n, a) for a in range(p)), tuple(M(n + n2, a) for a in range(p))}) for n in range(p - 1)}
        latpairs = {frozenset({tuple(L(a, m) for m in range(p - 1)), tuple(L((-a) % p, m) for m in range(p - 1))}) for a in range(1, p)}
        ok &= (len(mer) == p - 1 and len(circles) == 2 * k and len(latpairs) == 2 * k)
        V = (p - 1) * (2 * k) + 1
        ok &= (V == (p - 1) ** 2 // 2 + 1)
        det.append(f"p={p}: {len(mer)} meridian lists, {len(circles)} great circles, {len(latpairs)} latitude pairs, |V| = {V}")
    # predicate 1:C4
    check("A5", "M_n(a) = M_{n+2κ}(−a), L_a(m) = L_{−a}(m+2κ); p−1 meridian lists in 2κ circles; 2κ latitude pairs; |V| = (p−1)²/2 + 1",
          ok, "; ".join(det))

# ------------------------------------------------------------------------------------------------------------
# block B: the framed numbers, the charts and the horizon (EXACT; B3 CHART in exact rationals)
# Paper statements decided (Sections 4–5; ledger predicates 1:D2, 1:D4, 1:D6, 1:E2, 1:F1; B6 decides no predicate):
#
#   B1  def:integers (1:D2)          the window W_H = {|z| ≤ H}: z ↦ z mod p injective iff 2H < p; sums read back
#                                    iff 4H < p; products read back whenever 2H² < p (sufficient; the product set is
#                                    sparse, so the bound is not sharp) — swept over every H
#   B2  thm:scale-periodicity (1:D4) the residue grids G_n = (x g^{−n})_x are (p−1)-periodic in n; the rational
#                                    grids (x/g^n) with g lifted to Z are not
#   B3  prop:r-rationals, thm:approx the chart of the grid [chart]: every r with |r| ≤ H g^{−n} lies within 1/(2gⁿ)
#       (1:D6)                       of some x/gⁿ, x ∈ W_H (exact rationals); at (13, 2) no grid point of step ≤ 1/8
#                                    lies within 1/16 of 33/10 — range and resolution trade off at fixed window
#   B4  prop:Cp-field (1:E2)         F_p[X]/(X²+1) has zero divisors on the shell ((u+X)(u−X) = 0, factors nonzero);
#                                    X²+1 has no root, hence the quotient is a field, exactly for p ≡ 3 (mod 4)
#   B5  thm:no-south-pole (1:F1)     2s = 0 ⇒ s = 0 on every odd prime; 2·(2κ+1) = 1: the half-turn 2⁻¹ = 2κ+1
#   B6  (no predicate)               the Euclidean step count against the bound k ≤ ⌊log₂ p⌋+1 (lem:euclid-bound):
#                                    p = 59 (55, 34) needs 7 > 6; p = 1009 (987, 610) needs 13 > 10; first excess at 59
def block_B():
    """Block B — the framed numbers, the charts and the horizon (EXACT; B3 CHART in exact rationals): B1–B6."""
    print("block B — the framed numbers, the charts and the horizon")

    # B1 — the window law, the three thresholds as iff over every H
    ok, det = True, []
    for p in [13, 17, 29]:
        for H in range(1, p):
            W = range(-H, H + 1)
            inj = len({z % p for z in W}) == len(W)
            sums = len({(x + y) % p for x in W for y in W}) == len({x + y for x in W for y in W})
            prods = len({(x * y) % p for x in W for y in W}) == len({x * y for x in W for y in W})
            ok &= (inj == (2 * H < p)) and (sums == (4 * H < p)) and ((2 * H * H < p) <= prods)   # products: sufficient, not necessary (the product set is sparse)
        det.append(f"p={p}: H = 1..{p-1} swept")
    # predicate 1:D2
    check("B1", "z ↦ z mod p injective on W_H iff 2H < p; sums read back iff 4H < p; products read back whenever 2H² < p", ok, "; ".join(det))

    # B2 — scale-periodicity: in the field yes, in Q no
    ok, det = True, []
    for p, g in [(13, 11), (13, 2), (17, 3), (29, 2)]:
        assert g in primitive_roots(p)
        grid = lambda n: tuple((x * pow(g, -n, p)) % p for x in range(p))
        ok &= all(grid(n) == grid(n + p - 1) for n in range(2 * (p - 1)))
        ok &= all(grid(n) != grid(n + d) for n in range(p - 1) for d in range(1, p - 1))   # exact period p−1
        qgrid = lambda n: tuple(Fraction(x, g ** n) for x in range(p))
        ok &= all(qgrid(n) != qgrid(n + p - 1) for n in range(3))
        det.append(f"({p},{g}): period {p-1} in F_p, none in Q")
    # predicate 1:D4
    check("B2", "G_n = (x g^{−n})_x is (p−1)-periodic in the field, with exact period p−1; the rational grids x/gⁿ are not periodic",
          ok, "; ".join(det))

    # B3 — the chart of the grid: the trade-off holds; its range at (13, 2)
    ok, det = True, []
    p, g, H = 13, 2, 12
    for n in range(0, 8):
        step = Fraction(1, g ** n)
        for num in range(-40, 41):                                    # r = num/8 · H g^{−n}, a sample within the range
            r = Fraction(num, 40) * H * step
            x = round(r / step)                                        # x = round(r gⁿ), |x| ≤ H
            ok &= (abs(x) <= H) and (abs(r - x * step) <= step / 2)
    r, tol = Fraction(33, 10), Fraction(1, 16)
    near = [(x, n) for n in range(3, 13) for x in range(p) if abs(Fraction(x, g ** n) - r) < tol]
    ok &= (near == []) and all(Fraction(x, g ** n) <= Fraction(3, 2) for n in range(3, 13) for x in range(p))
    best = min((abs(Fraction(x, g ** n) - r), x, n) for n in range(13) for x in range(p))
    ok &= (best[1:] == (7, 1) and best[0] == Fraction(1, 5))
    det.append(f"trade-off on {8*81} sampled reals at (13,2), H=12; range: no x/2^n (n ≥ 3, x < 13) within 1/16 of 33/10, best 7/2 at error 1/5")
    check("B3", "|r| ≤ H g^{−n} ⇒ some x/gⁿ, x ∈ W_H, within 1/(2gⁿ); at (13, 2) no point of step ≤ 1/8 within 1/16 of r = 33/10: range and resolution trade off at fixed window",
          ok, "; ".join(det), kind="CHART")

    # B4 — the complex chart is not an extension: zero divisors iff −1 is a square
    ok, det = True, []
    for p in [5, 13, 17, 29, 37]:
        u = sqrt_neg_one(p)[0]
        # in F_p[X]/(X²+1): elements a + bX, product (a+bX)(c+dX) = (ac − bd) + (ad + bc)X
        mul = lambda A, B: ((A[0] * B[0] - A[1] * B[1]) % p, (A[0] * B[1] + A[1] * B[0]) % p)
        ok &= (mul((u, 1), ((-u) % p, 1)) == (0, 0)) and (u, 1) != (0, 0) and ((-u) % p, 1) != (0, 0)
        det.append(f"p={p}: (u+X)(u−X)=0 with u={u}")
    for p in CONTROLS:
        ok &= (sqrt_neg_one(p) == [])                                    # X²+1 irreducible: the quotient is the field F_{p²}
        mul = lambda A, B: ((A[0] * B[0] - A[1] * B[1]) % p, (A[0] * B[1] + A[1] * B[0]) % p)
        elems = [(a, b) for a in range(p) for b in range(p) if (a, b) != (0, 0)]
        ok &= all(mul(A, B) != (0, 0) for A in elems for B in elems)    # no zero divisors
    # predicate 1:E2
    check("B4", "F_p[X]/(X²+1) has zero divisors on the shell (p ≡ 1 mod 4); it is a field exactly when p ≡ 3 (mod 4)",
          ok, "; ".join(det) + f"; fields at p ∈ {CONTROLS} (no zero divisors, exhaustive)")

    # B5 — no element of additive order two; the half-turn
    ok, det = True, []
    for p in [q for q in range(3, 200) if is_prime(q)]:
        ok &= ([s for s in range(p) if (2 * s) % p == 0] == [0])
        if p % 4 == 1:
            k = kappa(p)
            ok &= ((2 * (2 * k + 1)) % p == 1) and (2 * k + 1 == (p + 1) // 2)
    # predicate 1:F1
    check("B5", "2s = 0 ⇒ s = 0 for every odd prime < 200; on the shell 2⁻¹ = 2κ+1 = (p+1)/2, the residue past the antipode", ok, "primes 3..199")

    # B6 — the Euclidean step count against the bound ⌊log₂ p⌋+1 (recorded under V1)
    def steps(a, b):
        k = 0
        while b:
            a, b = b, a % b
            if b: k += 1
        return k
    fib = [1, 1]
    while fib[-1] < 2000: fib.append(fib[-1] + fib[-2])
    first = None
    for p in [q for q in range(5, 2000) if is_prime(q)]:
        worst = max(steps(fib[i + 1], fib[i]) for i in range(1, len(fib) - 1) if fib[i + 1] < p)
        if worst > p.bit_length():
            first = p; break
    ok = (steps(55, 34) == 7 and (59).bit_length() == 6 and steps(987, 610) == 13 and (1009).bit_length() == 10 and first == 59)
    ok &= (fib[3] == 3 and fib[3] < 2 ** 2)                               # F_4 = 3 < 2^{4−2}: the Fibonacci bound 2^{k−2} does not hold at k = 4
    check("B6", "the Euclidean step count against ⌊log₂p⌋+1: (55,34) needs 7 > ⌊log₂59⌋+1 = 6; (987,610) needs 13 > 10; first excess at p = 59; F_4 = 3 < 4",
          ok, "a ≥ b convention, consecutive Fibonacci pairs below p")

# ------------------------------------------------------------------------------------------------------------
# block C: the conjecture of the conclusion, clause by clause (EXACT; C2–C4 CHART)
# The conclusion conjectures that the finite substrate supports polynomial equation solving, limit-like
# approximation and ε-approximation of continuous symmetries (ledger predicate 1:Y1).  Predicates 1:G1–G4 decide it:
#
#   C1  (1:G1)  solving: f ∈ F_p[X] has a root in F_p iff gcd(f, X^p − X) ≠ 1, and deg gcd = the number of
#               distinct roots — every monic polynomial of degree ≤ 3 over F_13 (2197) and F_17 (4913), by
#               brute-force roots against the Euclidean gcd            [exact]
#   C2  (1:G2)  limit-like approximation across shells: for r ∈ {π, e, √2, 33/10, 1/3} and ε = 10^−k
#               (k = 2..8) the construction n = ⌈log₂(1/ε)⌉, x = round(r·2ⁿ), p = the first prime ≡ 1 (mod 4)
#               beyond 2|x|+1 gives |r − x/2ⁿ| < ε with |x| ≤ 2κ      [chart: r read as a rational to 60 digits]
#   C3  (1:G3)  the circle net: for N = p − 1 on every shell the rounding k(θ) = ⌊Nθ/2π + ½⌋ has angle error
#               ≤ π/N, chord error |e^{2πik/N} − e^{iθ}| ≤ π/N, and group-law defect |k(θ₁)+k(θ₂)−k(θ₁+θ₂)| ≤ 1,
#               on a grid of 4N angles plus 20000 random pairs           [chart]
#   C4  (1:G4)  the SO(3) obstruction: the covering radii of the finite rotation groups in the rotation-angle
#               metric — tetrahedral π/2, octahedral arccos((2√2−1)/4) ≈ 62.80°, icosahedral
#               ε₀ = arccos((3√5−1)/8) ≈ 44.48° (the deep hole of the 600-cell, cos = φ²/2√2), cyclic and
#               dihedral ≥ π/2 (they lie in an O(2)) — by exhaustive group closure and a sampled maximin;
#               no finite subgroup of SO(3) is an ε-net for ε < ε₀      [chart; the list of groups is A3, Klein]
#   C5  (1:G5)  the window resolves SO(3): the framed quaternions W_H⁴ = {q ∈ Z⁴ : |q_i| ≤ H}, normalised, are an
#               ε-net of SO(3) with ε ≤ 2·arcsin(1/H) (round H·s to the lattice: |Hs − q| ≤ 1, so the angle is
#               ≤ arcsin(1/H)); measured ε(1) ≈ 60.8°, ε(2) ≈ 41.0°, ε(3) ≈ 30.0°; 2·arcsin(1/3) = 38.9° < ε₀, so on
#               the shell p = 73 the window H = 3 out-resolves every finite subgroup; products of window quaternions
#               have entries in W_{4H²} and read back exactly from the shell when 8H² < p (20000 random pairs on
#               F_73, H = 3)                                              [chart; the read-back is exact]

# ---------------------------------------------------------------- polynomial arithmetic over F_p (lists, low degree first)
def p_trim(a):
    while a and a[-1] == 0: a.pop()
    return a
def p_mod(a, b, p):
    a = a[:]; db = len(b) - 1; inv = pow(b[-1], -1, p)
    while len(a) - 1 >= db and a:
        c = (a[-1] * inv) % p; s = len(a) - 1 - db
        for i, bi in enumerate(b): a[s + i] = (a[s + i] - c * bi) % p
        p_trim(a)
    return a
def p_gcd(a, b, p):
    a, b = p_trim(a[:]), p_trim(b[:])
    while b: a, b = b, p_mod(a, b, p)
    if a: inv = pow(a[-1], -1, p); a = [(c * inv) % p for c in a]
    return a
def p_eval(a, x, p):
    r = 0
    for c in reversed(a): r = (r * x + c) % p
    return r

def block_C():
    """Block C — the conjecture of the conclusion, clause by clause (EXACT; C2–C5 CHART): C1–C5."""
    print("block C — the conjecture of the conclusion, clause by clause")

    # C1 — solving: roots exist iff gcd(f, X^p − X) ≠ 1; deg gcd counts the distinct roots
    ok, det = True, []
    for p, dmax in [(13, 3), (17, 3)]:
        xp_minus_x = [0] * (p + 1); xp_minus_x[p] = 1; xp_minus_x[1] = (xp_minus_x[1] - 1) % p
        n = 0
        for d in range(1, dmax + 1):
            for coeffs in itertools.product(range(p), repeat=d):
                f = list(coeffs) + [1]                                  # monic of degree d
                roots = {x for x in range(p) if p_eval(f, x, p) == 0}
                g = p_gcd(f, xp_minus_x, p)
                ok &= ((len(g) - 1) == len(roots)) and ((len(roots) > 0) == (len(g) > 1)); n += 1
        det.append(f"p={p}: {n} monic polynomials of degree ≤ {dmax}")
    # predicate 1:G1
    check("C1", "f has a root in F_p iff gcd(f, X^p − X) ≠ 1; deg gcd(f, X^p − X) = number of distinct roots (exhaustive, degree ≤ 3)",
          ok, "; ".join(det))

    # C2 — limit-like approximation across the tower of shells
    getcontext().prec = 60
    reals = {"π": Fraction(Decimal("3.14159265358979323846264338327950288419716939937510582097494")),
             "e": Fraction(Decimal("2.71828182845904523536028747135266249775724709369995957496697")),
             "√2": Fraction(Decimal("1.41421356237309504880168872420969807856967187537694807317668")),
             "33/10": Fraction(33, 10), "1/3": Fraction(1, 3)}
    def next_shell(m):                                                  # the first prime ≡ 1 (mod 4) beyond m
        q = m + 1
        while not (q % 4 == 1 and is_prime(q)): q += 1
        return q
    ok, det = True, []
    for name, r in reals.items():
        for k in range(2, 9):
            eps = Fraction(1, 10 ** k); n = math.ceil(math.log2(10 ** k)); x = round(r * 2 ** n)
            p = next_shell(2 * abs(x) + 1); kap = (p - 1) // 4
            ok &= (abs(r - Fraction(x, 2 ** n)) < eps) and (abs(x) <= 2 * kap) and p % 4 == 1 and is_prime(p)
        det.append(f"{name}: ε=10⁻⁸ → n={n}, p={p}")
    # predicate 1:G2
    check("C2", "for every r and ε some shell p = 4κ+1 carries x/2ⁿ, |x| ≤ 2κ, within ε of r (five reals, ε = 10⁻²..10⁻⁸)",
          ok, "; ".join(det), kind="CHART")

    # C3 — the circle net and the group-law defect on every shell
    ok, det = True, []
    rnd = random.Random(1)
    for p in SHELLS:
        N = p - 1
        k = lambda th: math.floor(N * th / (2 * math.pi) + 0.5)
        worst_angle = worst_chord = 0.0; worst_defect = 0
        thetas = [2 * math.pi * j / (4 * N) for j in range(4 * N)] + [rnd.uniform(0, 2 * math.pi) for _ in range(2000)]
        for th in thetas:
            kk = k(th); worst_angle = max(worst_angle, abs(th - 2 * math.pi * kk / N))
            worst_chord = max(worst_chord, abs(complex(math.cos(2 * math.pi * kk / N), math.sin(2 * math.pi * kk / N)) - complex(math.cos(th), math.sin(th))))
        for _ in range(20000):
            a, b = rnd.uniform(0, 2 * math.pi), rnd.uniform(0, 2 * math.pi)
            worst_defect = max(worst_defect, abs(k(a) + k(b) - k(a + b)))
        ok &= (worst_angle <= math.pi / N + 1e-12) and (worst_chord <= math.pi / N + 1e-12) and (worst_defect <= 1)
        det.append(f"p={p}: angle {worst_angle:.4f} ≤ π/N={math.pi / N:.4f}, defect ≤ {worst_defect}")
    # predicate 1:G3
    check("C3", "k(θ) = ⌊Nθ/2π + ½⌋, N = p−1: angle and chord error ≤ π/N, group-law defect ≤ 1, on every shell",
          ok, "; ".join(det), kind="CHART")

    # C4 — the SO(3) obstruction: covering radii of the finite rotation groups
    def qmul(a, b):
        w1, x1, y1, z1 = a; w2, x2, y2, z2 = b
        return (w1*w2 - x1*x2 - y1*y2 - z1*z2, w1*x2 + x1*w2 + y1*z2 - z1*y2, w1*y2 - x1*z2 + y1*w2 + z1*x2, w1*z2 + x1*y2 - y1*x2 + z1*w2)
    def rot(axis, ang):
        n = math.sqrt(sum(c * c for c in axis)); s = math.sin(ang / 2) / n
        return (math.cos(ang / 2), s * axis[0], s * axis[1], s * axis[2])
    def closure(gens):
        G, frontier = [(1.0, 0.0, 0.0, 0.0)], [(1.0, 0.0, 0.0, 0.0)]
        while frontier:
            new = []
            for a in frontier:
                for g in gens:
                    b = qmul(a, g)
                    if not any(sum((u - v) ** 2 for u, v in zip(b, c)) < 1e-18 for c in G): G.append(b); new.append(b)
            frontier = new
        return G
    def dist(q, G):                                                     # rotation-angle distance from q to the group
        return 2 * math.acos(min(1.0, max(abs(sum(u * v for u, v in zip(q, g))) for g in G)))
    def covering_radius(G, samples=20000, refine=60):
        best = 0.0
        pts = []
        for _ in range(samples):
            v = [rnd.gauss(0, 1) for _ in range(4)]; n = math.sqrt(sum(c * c for c in v)); pts.append(tuple(c / n for c in v))
        pts.sort(key=lambda q: -dist(q, G))
        for q in pts[:12]:
            cur, step = dist(q, G), 0.05
            for _ in range(refine):
                cands = []
                for _ in range(48):
                    v = [c + step * rnd.gauss(0, 1) for c in q]; n = math.sqrt(sum(c * c for c in v)); cands.append(tuple(c / n for c in v))
                c = max(cands, key=lambda q: dist(q, G)); dc = dist(c, G)
                if dc > cur: q, cur = c, dc
                else: step *= 0.7
            best = max(best, cur)
        return best
    phi = (1 + 5 ** 0.5) / 2
    groups = {"tetrahedral": closure([rot((0, 0, 1), math.pi), rot((1, 1, 1), 2 * math.pi / 3)]),
              "octahedral": closure([rot((0, 0, 1), math.pi / 2), rot((1, 1, 1), 2 * math.pi / 3)]),
              "icosahedral": closure([rot((0, 0, 1), math.pi), rot((1, 1, 1), 2 * math.pi / 3), rot((0, 1, phi), 2 * math.pi / 5)])}
    exact = {"tetrahedral": math.pi / 2, "octahedral": math.acos((2 * 2 ** 0.5 - 1) / 4), "icosahedral": math.acos((3 * 5 ** 0.5 - 1) / 8)}
    ok, det = True, []
    ok &= [len(G) for G in groups.values()] == [24, 48, 120]           # the binary groups: 2 × 12, 24, 60
    for name, G in groups.items():
        r = covering_radius(G); ok &= abs(r - exact[name]) < 2e-3
        det.append(f"{name}: {math.degrees(r):.2f}° (exact {math.degrees(exact[name]):.2f}°)")
    # cyclic and dihedral groups lie in an O(2): rotations about an axis and half-turns about axes normal to it; the
    # rotation q = (w,x,y,z) with w²+z² = x²+y² = ½ is at distance 2·arccos(1/√2) = π/2 from every element of O(2)
    q = (0.5 ** 0.5 * math.cos(0.3), 0.5 ** 0.5 * math.cos(1.1), 0.5 ** 0.5 * math.sin(1.1), 0.5 ** 0.5 * math.sin(0.3))
    d_o2 = 2 * math.acos(max(math.hypot(q[0], q[3]), math.hypot(q[1], q[2])))
    ok &= abs(d_o2 - math.pi / 2) < 1e-12
    eps0 = min(exact.values()); ok &= abs(eps0 - exact["icosahedral"]) < 1e-15 and eps0 < math.pi / 2
    det.append(f"cyclic/dihedral (in O(2)): ≥ {math.degrees(d_o2):.2f}°; ε₀ = {math.degrees(eps0):.4f}° = {eps0:.6f} rad")
    # predicate 1:G4
    check("C4", "covering radii in SO(3): tetrahedral π/2, octahedral arccos((2√2−1)/4), icosahedral arccos((3√5−1)/8) = ε₀ ≈ 44.48°, cyclic/dihedral ≥ π/2; no finite subgroup is an ε-net for ε < ε₀",
          ok, "; ".join(det), kind="CHART")

    # C5 — the window resolves SO(3): the normalised framed quaternions are a 2·arcsin(1/H)-net, composing exactly on the shell
    ok, det = True, []
    for H in [1, 2, 3]:
        pts = [q for q in itertools.product(range(-H, H + 1), repeat=4) if any(q)]
        seen, W = set(), []
        for q in pts:                                                   # one representative per rotation (q and −q)
            n = math.sqrt(sum(c * c for c in q)); u = tuple(c / n for c in q)
            key = tuple(round(c, 9) for c in (u if next(c for c in u if abs(c) > 1e-12) > 0 else tuple(-c for c in u)))
            if key not in seen: seen.add(key); W.append(u)
        bound = 2 * math.asin(1 / H)
        samples = []
        for _ in range(3000):
            v = [rnd.gauss(0, 1) for _ in range(4)]; n = math.sqrt(sum(c * c for c in v)); samples.append(tuple(c / n for c in v))
        ds = [dist(q, W) for q in samples]
        ok &= max(ds) <= bound + 1e-12                                   # the elementary bound, on every sample
        # the rounding witness itself, on every sample: q = round(H s) is within arcsin(1/H)
        for s_ in samples:
            q = tuple(round(H * c) for c in s_)
            if any(q):
                n = math.sqrt(sum(c * c for c in q)); cosang = abs(sum(a * b for a, b in zip(s_, q))) / n
                ok &= 2 * math.acos(min(1.0, cosang)) <= bound + 1e-12
        measured = covering_radius(W, samples=4000, refine=40)
        ok &= measured <= bound + 1e-9
        det.append(f"H={H}: {len(W)} rotations, measured {math.degrees(measured):.1f}° ≤ bound {math.degrees(bound):.1f}°")
    ok &= 2 * math.asin(1 / 3) < math.acos((3 * 5 ** 0.5 - 1) / 8)     # H = 3 beats every finite subgroup
    # exact composition on the shell p = 73 > 8·3² = 72: the product of two window quaternions reads back from F_73
    p, H = 73, 3
    def qmul_int(a, b):
        w1, x1, y1, z1 = a; w2, x2, y2, z2 = b
        return (w1*w2 - x1*x2 - y1*y2 - z1*z2, w1*x2 + x1*w2 + y1*z2 - z1*y2, w1*y2 - x1*z2 + y1*w2 + z1*x2, w1*z2 + x1*y2 - y1*x2 + z1*w2)
    read = lambda r: r - p if r > (p - 1) // 2 else r                   # the window reading of a residue
    n_pairs = 0
    for _ in range(20000):
        a = tuple(rnd.randint(-H, H) for _ in range(4)); b = tuple(rnd.randint(-H, H) for _ in range(4))
        exact = qmul_int(a, b); modp = qmul_int(tuple(c % p for c in a), tuple(c % p for c in b))
        ok &= all(read(c % p) == e for c, e in zip(modp, exact)) and all(abs(e) <= 4 * H * H for e in exact); n_pairs += 1
    det.append(f"2·arcsin(1/3) = {math.degrees(2 * math.asin(1/3)):.1f}° < ε₀; composition on F_{p}, H={H}: {n_pairs} pairs read back exactly")
    # predicate 1:G5
    check("C5", "the normalised window quaternions W_H⁴ are a 2·arcsin(1/H)-net of SO(3) (H = 1, 2, 3), 38.9° < ε₀ at H = 3; their products read back exactly from the shell when 8H² < p",
          ok, "; ".join(det), kind="CHART")

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
