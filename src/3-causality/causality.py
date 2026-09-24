"""
causality.py — the validation package of "Euclidean–Lorentzian Dichotomy and Algebraic Causality in Finite Ring Continuum"
(Akhtman, Entropy 2025, 27, 1098; doi 10.3390/e27111098), the paper 3-causality of the FRC corpus
(finite-ring-space/src/3-causality), added with the paper's predicate ledger (Appendix A, 17 September 2026; one script
since 24 September 2026, the four block scripts merged).
========================================================================================================================

One script, four blocks, sixteen checks, standard library only. Each check names the predicate(s) of the paper's ledger it
witnesses (LEDGER below; predicates cited as 3:XN) under a `# 3:XN (<key>)` marker, the key the predicate's accession key,
and the ledger's source column links the marker of the check that decides each predicate (PREDICATES below;
finitering.space/src/3-causality/#<key>). Where a predicate is proved in Lean (lean/FrcCore/Causality.lean,
no axioms; lean/FrcLedger/Causality.lean on Mathlib), the check here is the instance the reader can run.

    python3 causality.py          every block, results.json written; exit 1 if a check fails (≈ 10 s)
    python3 causality.py C        one block (A, B, C or D); no results.json
    from frc_3_causality import predicate; predicate("3:B2")    one predicate: its block runs once per session

Blocks:  A  the square classes and the nonexistence theorem     EXACT  (3:B1–B3)
         B  the signature on the shell and in the extension     EXACT  (3:B4–B7)
         C  the finite Lorentz boosts                           EXACT  (3:C2–C5)
         D  the worked shell F_13                               EXACT  (3:D1)

Everything the blocks share:
  * the shell datum: p = 4κ+1 prime, the square classes S = (F_p^×)² and N = F_p^× \\ S, the primitive generators;
  * the quadratic extension K = F_p(√ν) = F_{p²} as pairs (a, b) = a + b√ν, with its Frobenius conjugation and norm;
  * the diagonal form Q_ν(t, x, y, z) = −ν t² + x² + y² + z² and the value distributions that count its zeros;
  * the PASS/FAIL registry every block reports into (results.json).

Kinds: EXACT checks are integer-pinned computations in F_p, F_{p²} or exact rationals (a pass is a proof on the
tested instances); CHART checks decide a [chart] predicate.
"""
import os, json, sys, math, random

SCRIPT = os.path.splitext(os.path.basename(__file__))[0]        # "causality": the one script, the name results.json and the site pages carry

# The shells (p, κ): p = 4κ+1 prime.
SHELLS = [(5, 1), (13, 3), (17, 4), (29, 7), (37, 9), (41, 10)]

# ----------------------------------------------------------------------------- registry
RESULTS = []

# The paper's predicate ledger (Appendix A, predicates cited as 3:XN): the predicate(s) each check witnesses.
LEDGER = {
    "A1": "3:B2", "A2": "3:B3", "A3": "3:B1", "A4": "3:B2",
    "B1": "3:B4", "B2": "3:B5", "B3": "3:B6", "B4": "3:B7", "B5": "3:B5",
    "C1": "3:C2", "C2": "3:C2", "C3": "3:C3", "C4": "3:C5", "C5": "3:C4",
    "D1": "3:D1", "D2": "3:D1",
}

BLOCK = {"A": "the square classes and the nonexistence theorem",           # check-id prefix -> the block (the function block_<letter> below)
         "B": "the signature on the shell and its collapse in the extension",
         "C": "the finite Lorentz boosts",
         "D": "the worked shell F_13"}

# the deciding check of each witnessed predicate: the one whose verdict decides the predicate's statement (the other checks that
# touch it are corroboration, listed by predicate() from the records)
PREDICATES = {
    "3:B1": "A3", "3:B2": "A1", "3:B3": "A2",
    "3:B4": "B1", "3:B5": "B2", "3:B6": "B3", "3:B7": "B4",
    "3:C2": "C1", "3:C3": "C3", "3:C4": "C5", "3:C5": "C4",
    "3:D1": "D1",
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
    k, y = 1, x % p
    while y != 1:
        y = y * x % p; k += 1
    return k

def generators(p):
    """The primitive generators of F_p^x, in increasing order."""
    return [g for g in range(2, p) if order(g, p) == p - 1]

def squares(p):
    """The nonzero squares S = (F_p^x)^2."""
    return sorted({x * x % p for x in range(1, p)})

def nonsquares(p):
    S = set(squares(p))
    return [x for x in range(1, p) if x not in S]

def is_square(x, p):
    return x % p != 0 and pow(x % p, (p - 1) // 2, p) == 1

def kappa(p):
    assert is_prime(p) and p % 4 == 1, p
    return (p - 1) // 4

# ----------------------------------------------------------------------------- the quadratic extension K = F_p(√ν)
class Ext:
    """F_{p²} = F_p[X]/(X² − ν) for a nonsquare ν: elements are pairs (a, b) = a + b√ν."""
    def __init__(self, p, nu):
        assert not is_square(nu, p), (p, nu)
        self.p, self.nu = p, nu % p
    def add(self, x, y): return ((x[0] + y[0]) % self.p, (x[1] + y[1]) % self.p)
    def sub(self, x, y): return ((x[0] - y[0]) % self.p, (x[1] - y[1]) % self.p)
    def neg(self, x): return ((-x[0]) % self.p, (-x[1]) % self.p)
    def mul(self, x, y):
        p, nu = self.p, self.nu
        return ((x[0] * y[0] + nu * x[1] * y[1]) % p, (x[0] * y[1] + x[1] * y[0]) % p)
    def conj(self, x): return (x[0], (-x[1]) % self.p)          # the Frobenius x ↦ x^p
    def norm(self, x): return (x[0] * x[0] - self.nu * x[1] * x[1]) % self.p
    def inv(self, x):
        n = self.norm(x); assert n != 0
        ni = pow(n, -1, self.p); c = self.conj(x)
        return (c[0] * ni % self.p, c[1] * ni % self.p)
    def pow(self, x, k):
        r = (1, 0)
        while k:
            if k & 1: r = self.mul(r, x)
            x = self.mul(x, x); k >>= 1
        return r
    def elements(self): return [(a, b) for a in range(self.p) for b in range(self.p)]
    def is_square_ext(self, x):
        """x is a square in K iff x^((p²−1)/2) = 1 (x ≠ 0)."""
        return x != (0, 0) and self.pow(x, (self.p * self.p - 1) // 2) == (1, 0)
    def scalar(self, a): return (a % self.p, 0)
    def norm_one(self):
        """The norm-one group N¹ = {z : z z̄ = 1}."""
        return [z for z in self.elements() if self.norm(z) == 1]

# ----------------------------------------------------------------------------- the form and its value distributions
def Q(coeffs, v, p):
    return sum(a * x * x for a, x in zip(coeffs, v)) % p

def value_counts(coeffs, p):
    """counts[w] = #{v in F_p^n : Q(v) = w}, by convolving the one-variable distributions (O(n p²))."""
    dist = [1] + [0] * (p - 1)                      # the empty form: Q = 0 once
    for a in coeffs:
        one = [0] * p
        for x in range(p): one[a * x * x % p] += 1
        new = [0] * p
        for u in range(p):
            if dist[u]:
                for w in range(p):
                    if one[w]: new[(u + w) % p] += dist[u] * one[w]
        dist = new
    return dist

def isotropic_count(coeffs, p):
    """#{v : Q(v) = 0}, the zero vector included."""
    return value_counts(coeffs, p)[0]

def orthogonal_order(coeffs, p):
    """|O(Q)| for a diagonal form by frame counting: the number of ordered orthogonal frames (v_0, …, v_n) with
    Q(v_i) = a_i, i.e. ∏_i #{v in <e_i, …, e_n> : Q(v) = a_i} (Witt: the count in the complement depends only on the
    isometry class of the restricted form)."""
    n = 1
    for i, a in enumerate(coeffs):
        n *= value_counts(coeffs[i:], p)[a % p]
    return n

def o_plus_4(q): return 2 * q * q * (q * q - 1) ** 2          # |O_4^+(q)|, Witt index 2
def o_minus_4(q): return 2 * q * q * (q ** 4 - 1)            # |O_4^-(q)|, Witt index 1

for _p, _k in SHELLS:
    assert is_prime(_p) and _p == 4 * _k + 1, (_p, _k)

# ------------------------------------------------------------------------------------------------------------
# block A: the square classes and the nonexistence theorem (3:B1, B2, B3)
# Section 2 of the paper: the two square classes of F_p^x with −1 a square (p ≡ 1 mod 4); no c ∈ F_p has c² = ν for a
# nonsquare ν, and for c ≠ 0 every coefficient of −c²t² + x² + y² + z² is a square (thm:nonexistence, with c ≠ 0
# made explicit — c = 0 gives a degenerate form); the absorption lemma by rescaling, no root of a_0 needed
# (lem:square-class-absorption); the class of ν as the datum, canonically ν = g (8:B2, B3).
def block_A():
    """Block A — the square classes and the nonexistence theorem (EXACT): A1–A4."""
    # A1 the square classes, −1 a square, c² and −c² squares, no causal square root (3:B2)
    ok = True; det = []
    for p, k in SHELLS:
        S, N = squares(p), nonsquares(p)
        ok &= len(S) == len(N) == (p - 1) // 2 and (p - 1) in S
        ok &= all(c * c % p in S and (-c * c) % p in S for c in range(1, p))
        ok &= all(c * c % p != nu for c in range(p) for nu in N)
        det.append(f"p={p}: |S|=|N|={len(S)}, -1={p-1} in S")
    # 3:B2 (p03006)
    check("A1", "F_p^x splits into two classes of (p-1)/2; -1, c^2 and -c^2 are squares (c != 0); no c with c^2 in N", ok, "; ".join(det[:3]))

    # A2 the absorption lemma: coefficients in one class => Q = a_0 sum (w_i X_i)^2 with w_i^2 = a_i/a_0;
    #    no root of a_0 is used: a_0 in N has none, and -a_i stays in N (3:B3)
    ok = True; det = []
    for p, k in SHELLS[:3]:
        S, N = squares(p), nonsquares(p)
        sq = {}
        for w in range(1, p): sq.setdefault(w * w % p, w)          # a square root of each square
        for cls in (S, N):
            for a0 in cls:
                for a1 in cls:
                    for a2 in cls:
                        for a3 in cls:
                            a = (a0, a1, a2, a3); inv0 = pow(a0, -1, p)
                            ws = [sq.get(ai * inv0 % p) for ai in a]
                            ok &= all(w is not None for w in ws) and all((a0 * w * w) % p == ai for w, ai in zip(ws, a))
        # u_0 with u_0^2 = a_0 exists only for a_0 in S; -a_i for a_i in N is in N again
        ok &= all(nu not in sq for nu in N) and all((-nu) % p in N for nu in N)
        det.append(f"p={p}: {len(S)**4 + len(N)**4} one-class coefficient tuples absorbed")
    # 3:B3 (p03007)
    check("A2", "one square class => Q equivalent to a_0 (sum of squares) by w_i^2 = a_i/a_0; no root of a_0 exists for a_0 in N, and -a_i stays in N", ok, "; ".join(det))

    # A3 the class is the datum: g is a nonsquare for every primitive root; Q_nu depends on nu only through its class,
    #    Q_{nu w^2}(t, x, y, z) = Q_nu(w t, x, y, z) (3:B1)
    ok = True
    for p, k in SHELLS:
        ok &= all(not is_square(g, p) for g in generators(p))
        nu = nonsquares(p)[0]
        for w in range(1, p):
            nu2 = nu * w * w % p
            ok &= all(Q((-nu2, 1, 1, 1), (t, x, y, z), p) == Q((-nu, 1, 1, 1), (w * t, x, y, z), p)
                      for t in range(p) for x in range(0, p, 3) for y in (0, 1) for z in (0, 2))
    # 3:B1 (p03005)
    check("A3", "every primitive root g is a nonsquare (nu = g canonical); Q_nu depends on nu only through its class", ok)

    # A4 c in F_p^x gives a Euclidean form; c = 0 a degenerate one (3:B2)
    ok = True
    for p, k in SHELLS[:4]:
        for c in range(1, p):
            coeffs = ((-c * c) % p, 1, 1, 1)
            ok &= all(is_square(a, p) for a in coeffs)
            ok &= isotropic_count(coeffs, p) == p ** 3 + p * p - p        # hyperbolic count: the Euclidean type
        ok &= isotropic_count((0, 1, 1, 1), p) != p ** 3 + p * p - p        # c = 0: degenerate, not of either type
    check("A4", "-c^2 t^2 + x^2 + y^2 + z^2 (c != 0) has p^3 + p^2 - p zeros: the Euclidean (hyperbolic) type; c = 0 degenerate", ok)

# ------------------------------------------------------------------------------------------------------------
# block B: the signature on the shell and its collapse in the extension (3:B4, B5, B6, B7)
# The dichotomy is decided by counting.  On F_p the form Q_ν = −ν t² + x² + y² + z² has p³ − p² + p zeros when ν is a
# nonsquare (the elliptic, minus type: Witt index 1, the Lorentzian class) and p³ + p² − p when ν is a square (the
# hyperbolic, plus type: Witt index 2, the Euclidean class); the isometry groups are O_4^−(p) of order 2p²(p⁴−1) and
# O_4^+(p) of order 2p²(p²−1)², counted by orthogonal frames (B1, B3).  Over K = F_{p²} every element of F_p is a
# square, Q_ν has q³ + q² − q zeros with q = p² and |O(Q_ν, K)| = 2q²(q²−1)²: the plus type — the extension is where
# the dichotomy collapses, not where it arises (B2).  The causal classes — the null cone and the two classes of
# non-null vectors by the square class of Q_ν(v) — are invariant under every isometry and under rescaling (B4).
def ext_value_counts(K, coeffs):
    """counts[w] = #{v in K^n : Q(v) = w} for K = F_{p²} (elements as pairs), by convolution."""
    els = K.elements(); idx = {z: i for i, z in enumerate(els)}
    dist = {(0, 0): 1}
    for a in coeffs:
        one = {}
        for x in els:
            w = K.mul(K.scalar(a) if isinstance(a, int) else a, K.mul(x, x)); one[w] = one.get(w, 0) + 1
        new = {}
        for u, cu in dist.items():
            for w, cw in one.items():
                s = K.add(u, w); new[s] = new.get(s, 0) + cu * cw
        dist = new
    return dist

def ext_orthogonal_order(K, coeffs):
    n = 1
    for i, a in enumerate(coeffs):
        n *= ext_value_counts(K, coeffs[i:]).get(K.scalar(a), 0)
    return n

def block_B():
    """Block B — the signature on the shell and its collapse in the extension (EXACT): B1–B5."""
    # B1 the zero counts on the shell decide the type (3:B4); agrees with 8:B7 (2353, 2041 at p = 13)
    ok = True; det = []
    for p, k in SHELLS:
        S, N = squares(p), nonsquares(p)
        for nu in N:
            ok &= isotropic_count(((-nu) % p, 1, 1, 1), p) == p ** 3 - p * p + p
        for nu in S:
            ok &= isotropic_count(((-nu) % p, 1, 1, 1), p) == p ** 3 + p * p - p
        ok &= all(not is_square((-nu) % p, p) for nu in N)     # the discriminant -nu is a nonsquare for nu in N
        det.append(f"p={p}: {p**3 - p*p + p} zeros (nu in N), {p**3 + p*p - p} (nu in S)")
    # 3:B4 (p03008)
    check("B1", "Q_nu has p^3 - p^2 + p zeros for nu nonsquare (elliptic, Witt index 1) and p^3 + p^2 - p for nu square (hyperbolic, Witt index 2), every nu", ok, "; ".join(det[:4]))

    # B2 over K = F_{p^2} the dichotomy collapses: nu = c^2, Q_nu of the plus type, q^3 + q^2 - q zeros, |O| = 2q^2(q^2-1)^2 (3:B5)
    ok = True; det = []
    for p in (5, 13):
        nu = nonsquares(p)[0]; K = Ext(p, nu); q = p * p
        c = (0, 1)
        ok &= K.mul(c, c) == (nu, 0)                                              # c^2 = nu in K
        ok &= all(K.is_square_ext((a, 0)) for a in range(1, p))                    # every element of F_p is a square in K
        z = ext_value_counts(K, [(-nu) % p, 1, 1, 1])[(0, 0)]
        ok &= z == q ** 3 + q * q - q
        det.append(f"p={p}: q={q}, {z} zeros of Q_nu over K = q^3+q^2-q")
        if p == 5:
            o = ext_orthogonal_order(K, [(-nu) % p, 1, 1, 1])
            ok &= o == o_plus_4(q)
            det.append(f"|O(Q_nu, F_25)| = {o} = 2q^2(q^2-1)^2 (plus type; the minus type would be {o_minus_4(q)})")
    # 3:B5 (p03009)
    check("B2", "over K = F_{p^2}: nu = c^2, every element of F_p a square, Q_nu of the plus type (Witt index 2)", ok, "; ".join(det))

    # B3 the isometry groups on the shell by frame counting (3:B6)
    ok = True; det = []
    for p in (5, 13, 17):
        nu = nonsquares(p)[0]; s = squares(p)[1] if p > 5 else squares(p)[0]
        om = orthogonal_order(((-nu) % p, 1, 1, 1), p); op = orthogonal_order(((-s) % p, 1, 1, 1), p)
        ok &= om == o_minus_4(p) and op == o_plus_4(p)
        det.append(f"p={p}: |O(Q_nu)|={om} = 2p^2(p^4-1); Euclidean {op} = 2p^2(p^2-1)^2")
    # 3:B6 (p03010)
    check("B3", "|O(Q_nu, F_p)| = 2p^2(p^4-1) (O_4^-) and |O(Euclidean)| = 2p^2(p^2-1)^2 (O_4^+) by frame counting", ok, "; ".join(det))

    # B4 the causal classes: null cone, square class, nonsquare class; sizes; invariance under isometries and rescaling (3:B7)
    ok = True; det = []
    rnd = random.Random(3)
    for p in (5, 13):
        nu = nonsquares(p)[0]; coeffs = ((-nu) % p, 1, 1, 1)
        cls = {}
        for t in range(p):
            for x in range(p):
                for y in range(p):
                    for z in range(p):
                        w = Q(coeffs, (t, x, y, z), p)
                        cls[(t, x, y, z)] = 0 if w == 0 else (1 if is_square(w, p) else 2)
        sizes = [sum(1 for v in cls.values() if v == i) for i in range(3)]
        ok &= sizes == [p ** 3 - p * p + p, (p - 1) * (p ** 3 + p) // 2, (p - 1) * (p ** 3 + p) // 2]
        # the reflection along a non-isotropic w: v -> v - 2 B(v,w)/Q(w) w, an isometry; rescaling v -> lambda v
        B = lambda u, w: sum(a * ui * wi for a, ui, wi in zip(coeffs, u, w)) % p
        ws = [w for w in cls if cls[w] != 0]; rnd.shuffle(ws)
        for w in ws[:60]:
            qw_inv = pow(Q(coeffs, w, p), -1, p)
            for v in rnd.sample(list(cls), 200):
                f = 2 * B(v, w) * qw_inv % p
                v2 = tuple((vi - f * wi) % p for vi, wi in zip(v, w))
                ok &= Q(coeffs, v2, p) == Q(coeffs, v, p) and cls[v2] == cls[v]
        for lam in range(1, p):
            ok &= all(cls[tuple(lam * vi % p for vi in v)] == cls[v] for v in rnd.sample(list(cls), 300))
        det.append(f"p={p}: null {sizes[0]}, square class {sizes[1]}, nonsquare class {sizes[2]}")
    # 3:B7 (p03011)
    check("B4", "the null cone and the two non-null classes (square class of Q_nu(v)) partition F_p^4 with sizes p^3-p^2+p, (p-1)(p^3+p)/2 each; invariant under reflections and rescaling", ok, "; ".join(det))

    # B5 the anisotropic kernel and the isotropic planes (3:B5): x^2 - nu t^2 = 0 only trivially; (y, z) = (1, i) null;
    #    for nu = w^2 the (t, x) plane is hyperbolic too
    ok = True
    for p, k in SHELLS:
        nu = nonsquares(p)[0]; i = next(x for x in range(p) if x * x % p == p - 1)
        ok &= all((x * x - nu * t * t) % p != 0 for t in range(1, p) for x in range(p))
        ok &= (1 + i * i) % p == 0
        w = 2; s = w * w % p
        ok &= (w * w - s * 1) % p == 0 and isotropic_count(((-s) % p, 1), p) == 2 * p - 1 and isotropic_count(((-nu) % p, 1), p) == 1
    check("B5", "x^2 - nu t^2 is anisotropic (nu nonsquare); y^2 + z^2 and x^2 - w^2 t^2 are hyperbolic planes: Witt index 1 vs 2 from the decomposition", ok)

# ------------------------------------------------------------------------------------------------------------
# block C: the finite Lorentz boosts (3:C1–C5)
# Section 3 of the paper.  The boosts of Q_ν(t, x) = −ν t² + x² over the shell are Λ(γ, b) = [[γ, b], [νb, γ]]
# with γ² − νb² = 1: the norm-one group N¹ of K = F_p(√ν), cyclic of order p + 1 (the non-split torus; 8:D5), with
# Λ(z₁)Λ(z₂) = Λ(z₁z₂) (C1); the whole of SO(Q_ν, F_p) in dimension 2, by exhaustion (C2).  The velocity v = −νb/γ is a
# shell quantity (γ ≠ 0 always), γ²(ν − v²) = ν, and the velocities compose by v₁₂ = (v₁+v₂)/(1 + v₁v₂/ν) exactly, the
# denominator never zero (C3).  The family Λ(u), u = g^{Δm} ∈ F_p^x, has a = (u − u⁻¹)/(2c) outside F_p
# for u ≠ ±1: a matrix over K, preserving Q_ν over K where Q_ν is Euclidean — the split torus of order p − 1, the
# extension's rotations (C4).  In 1+3 dimensions the x-boosts with O(3, F_p) generate O(Q_ν, F_5) = O_4^−(5), order
# 31 200 (C5).
def boost(g, b, nu, p):
    return ((g % p, b % p), (nu * b % p, g % p))

def mat_mul(A, B, p):
    n = len(A)
    return tuple(tuple(sum(A[i][k] * B[k][j] for k in range(n)) % p for j in range(n)) for i in range(n))

def preserves(M, coeffs, p):
    n = len(coeffs)
    import itertools
    for v in itertools.product(range(p), repeat=n):
        w = tuple(sum(M[i][j] * v[j] for j in range(n)) % p for i in range(n))
        if Q(coeffs, w, p) != Q(coeffs, v, p): return False
    return True

def closure(gens, p, limit=None):
    """The group generated by gens (tuples of tuples) by breadth-first multiplication."""
    n = len(gens[0]); I = tuple(tuple(int(i == j) for j in range(n)) for i in range(n))
    seen = {I}; frontier = [I]
    while frontier:
        nxt = []
        for A in frontier:
            for G in gens:
                Bm = mat_mul(A, G, p)
                if Bm not in seen:
                    seen.add(Bm); nxt.append(Bm)
                    if limit and len(seen) > limit: return seen
        frontier = nxt
    return seen

def block_C():
    """Block C — the finite Lorentz boosts (EXACT): C1–C5."""
    # C1 the norm-one group: order p + 1, cyclic, Lambda(z) preserves Q_nu, Lambda(z1 z2) = Lambda(z1) Lambda(z2) (3:C2)
    ok = True; det = []
    for p, k in SHELLS:
        nu = nonsquares(p)[0]; K = Ext(p, nu); N1 = K.norm_one()
        ok &= len(N1) == p + 1
        ok &= any(all(K.pow(z, d) != (1, 0) for d in range(1, p + 1)) for z in N1)          # an element of order p+1: cyclic
        coeffs = ((-nu) % p, 1)
        for z in N1:
            ok &= preserves(boost(z[0], z[1], nu, p), coeffs, p)
        for z1 in N1[:8]:
            for z2 in N1:
                z = K.mul(z1, z2)
                ok &= mat_mul(boost(*z1, nu, p), boost(*z2, nu, p), p) == boost(*z, nu, p)
        det.append(f"p={p}: |N^1|={len(N1)}")
    # 3:C2 (p03013)
    check("C1", "the boosts Lambda(gamma, b), gamma^2 - nu b^2 = 1, form the norm-one cycle of order p+1; each preserves Q_nu; Lambda(z1)Lambda(z2) = Lambda(z1 z2)", ok, "; ".join(det))

    # C2 SO(Q_nu, F_p) in dimension 2 is exactly the boosts: p + 1 matrices for nu nonsquare, p - 1 for nu square (3:C2)
    ok = True; det = []
    for p in (5, 13, 17):
        nu = nonsquares(p)[0]; s = squares(p)[-1]
        for coeff, expect in ((nu, p + 1), (s, p - 1)):
            coeffs = ((-coeff) % p, 1); n = 0; shape = True
            for a in range(p):
                for b in range(p):
                    for c in range(p):
                        for d in range(p):
                            M = ((a, b), (c, d))
                            if (a * d - b * c) % p == 1 and preserves(M, coeffs, p):
                                n += 1; shape &= (d == a and c == coeff * b % p)
            ok &= n == expect and shape
            det.append(f"p={p}, nu={coeff}: |SO|={n}")
    check("C2", "SO(Q_nu, F_p) in 1+1 dimensions has p+1 elements (nu nonsquare, non-split torus), p-1 (nu square, split torus), all of the shape [[g, b], [nu b, g]]", ok, "; ".join(det))

    # C3 velocity: gamma != 0, v = -nu b / gamma in F_p, gamma^2 (nu - v^2) = nu, exact Einstein addition (3:C3)
    ok = True; det = []
    for p, k in SHELLS:
        nu = nonsquares(p)[0]; K = Ext(p, nu); N1 = K.norm_one()
        ok &= all(z[0] != 0 for z in N1)
        vel = {}
        for z in N1:
            g, b = z; v = (-nu * b * pow(g, -1, p)) % p; vel[z] = v
            ok &= (g * g * (nu - v * v)) % p == nu % p
        ok &= len(set(vel.values())) == (p + 1) // 2                                   # v is 2-to-1 (z and -z)
        for z1 in N1:
            for z2 in N1:
                v1, v2 = vel[z1], vel[z2]; z12 = K.mul(z1, z2)
                den = (1 + v1 * v2 * pow(nu, -1, p)) % p
                ok &= den != 0 and vel[z12] == (v1 + v2) * pow(den, -1, p) % p
        det.append(f"p={p}: {(p + 1) // 2} velocities")
    # 3:C3 (p03014)
    check("C3", "gamma != 0 on every boost; v = -nu b/gamma; gamma^2 (nu - v^2) = nu; v12 = (v1 + v2)/(1 + v1 v2/nu) exactly, denominator never zero", ok, "; ".join(det[:3]))

    # C4 the family Lambda(u), u = g^{Delta m} in F_p^x: entries in K \ F_p, preserves Q_nu over K, the split torus of order p-1 (3:C5)
    ok = True; det = []
    for p in (13, 17):
        nu = nonsquares(p)[0]; K = Ext(p, nu); g = generators(p)[0]; c = (0, 1); c_inv = K.inv(c)
        two_inv = pow(2, -1, p)
        seen = set()
        for dm in range(p - 1):
            u = (pow(g, dm, p), 0); ui = K.inv(u)
            gam = K.mul(K.scalar(two_inv), K.add(u, ui)); a = K.mul(K.mul(K.scalar(two_inv), K.sub(u, ui)), c_inv)
            ok &= gam[1] == 0 and (a[0] == 0) and ((a[1] != 0) == (u[0] not in (1, p - 1)))   # gamma in F_p, a in c.F_p
            ok &= K.sub(K.mul(gam, gam), K.mul(K.scalar(nu), K.mul(a, a))) == (1, 0)          # gamma^2 - nu a^2 = 1 in K
            # Lambda(u) preserves Q_nu over K on a sample of K^2
            for t in K.elements()[:5]:
                for x in K.elements()[7:12]:
                    t2 = K.add(K.mul(gam, t), K.mul(a, x)); x2 = K.add(K.mul(K.scalar(nu), K.mul(a, t)), K.mul(gam, x))
                    q = lambda tt, xx: K.add(K.neg(K.mul(K.scalar(nu), K.mul(tt, tt))), K.mul(xx, xx))
                    ok &= q(t2, x2) == q(t, x)
            seen.add((gam, a))
        ok &= len(seen) == p - 1
        det.append(f"p={p}: {len(seen)} matrices Lambda(u), a in c.F_p, a not in F_p for u != +-1")
    # 3:C5 (p03016)
    check("C4", "the family Lambda(u), u = g^dm in F_p^x: gamma in F_p but a in c.F_p (not in F_p for u != +-1); preserves Q_nu over K; p-1 matrices, the split torus", ok, "; ".join(det))

    # C5 1+3: the x-boosts with O(3, F_5) generate O(Q_nu, F_5) = O_4^-(5) of order 31200; O(3, F_5) has order 240 (3:C4)
    p = 5; nu = nonsquares(p)[0]; K = Ext(p, nu); N1 = K.norm_one()
    z0 = next(z for z in N1 if all(K.pow(z, d) != (1, 0) for d in range(1, p + 1)))
    Lx = ((z0[0], z0[1], 0, 0), (nu * z0[1] % p, z0[0], 0, 0), (0, 0, 1, 0), (0, 0, 0, 1))
    coeffs = ((-nu) % p, 1, 1, 1)
    def reflection(w):
        qw = Q(coeffs, w, p); qi = pow(qw, -1, p)
        M = []
        for i in range(4):
            row = []
            for j in range(4):
                e = tuple(int(k == j) for k in range(4))
                Bw = sum(a * ei * wi for a, ei, wi in zip(coeffs, e, w)) % p
                row.append((int(i == j) - 2 * Bw * qi * w[i]) % p)
            M.append(tuple(row))
        return tuple(M)
    spatial = [(0, 1, 0, 0), (0, 0, 1, 0), (0, 0, 0, 1), (0, 1, 1, 0), (0, 1, 2, 0), (0, 0, 1, 2), (0, 1, 1, 1)]
    spatial = [w for w in spatial if Q(coeffs, w, p) != 0]
    O3 = closure([reflection(w) for w in spatial], p)
    G = closure([Lx] + [reflection(w) for w in spatial], p)
    ok = len(O3) == 2 * p * (p * p - 1) and len(G) == o_minus_4(p) and all(preserves(M, coeffs, p) for M in list(G)[:200])
    # 3:C4 (p03015)
    check("C5", "at p = 5 the x-boosts and O(3, F_p) (order 240) generate O(Q_nu, F_p) = O_4^-(5) of order 31200", ok,
             f"|O(3,F_5)|={len(O3)}, generated group {len(G)}")

# ------------------------------------------------------------------------------------------------------------
# block D: the worked shell F_13 (3:D1)
# The paper's worked shell: S = {1, 3, 4, 9, 10, 12}, N = {2, 5, 6, 7, 8, 11}; ν = 2 = g (the drive,
# canonically); X² − 2 irreducible; K = F_169 with c = √2 ∉ F_13; the null cone of Q_2 has 2041 points on the shell
# (elliptic) and 4 855 201 over K (q³ + q² − q, hyperbolic); the 14 boosts of N¹ with their 7 velocities; Λ(u) at
# u = 2 has a = −5/(2c) ∉ F_13.
def block_D():
    """Block D — the worked shell F_13 (EXACT): D1–D2."""
    p = 13; nu = 2
    S, N = squares(p), nonsquares(p)
    ok = S == [1, 3, 4, 9, 10, 12] and N == [2, 5, 6, 7, 8, 11]
    ok &= 2 in generators(p) and not is_square(2, p)
    ok &= all((x * x - 2) % p != 0 for x in range(p))                        # X^2 - 2 irreducible
    K = Ext(p, nu); c = (0, 1)
    ok &= K.mul(c, c) == (2, 0) and c[1] != 0
    ok &= isotropic_count((-2 % p, 1, 1, 1), p) == 2041
    N1 = K.norm_one(); ok &= len(N1) == 14
    vel = sorted({(-nu * b * pow(g, -1, p)) % p for g, b in N1}); ok &= len(vel) == 7
    u = (2, 0); ui = K.inv(u); a = K.mul(K.mul(K.scalar(pow(2, -1, p)), K.sub(u, ui)), K.inv(c))
    ok &= a[0] == 0 and a[1] != 0 and K.sub(u, ui) == ((2 - 7) % p, 0)      # u^-1 = 7, u - u^-1 = -5, a = -5/(2c)
    # 3:D1 (p03017)
    check("D1", "F_13: S = {1,3,4,9,10,12}, N = {2,5,6,7,8,11}; nu = 2 = g; X^2 - 2 irreducible; c = sqrt 2 in K \\ F_13; 2041 null points; 14 boosts, 7 velocities", ok,
             f"boosts (gamma, b): {N1}; velocities {vel}")
    # D2 the same numbers by Lean's count: nullCount 13 2 = 2041 (the core decides it by the kernel) — here the exhaustive loop
    n = sum(1 for t in range(p) for x in range(p) for y in range(p) for z in range(p) if (-2 * t * t + x * x + y * y + z * z) % p == 0)
    check("D2", "the null cone of Q_2 on F_13 counted vector by vector: 2041 = 13^3 - 13^2 + 13", n == 2041 == p ** 3 - p * p + p)

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
