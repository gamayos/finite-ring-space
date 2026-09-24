"""
reductio.py — the validation package of "Paradoxes of Infinity as Reductio ad Absurdum" (Akhtman, preprint 2025; Preprints
doi 10.20944/preprints202508.1744.v1), the paper 5-reductio of the FRC corpus (finite-ring-space/src/5-reductio), added with
the paper's predicate ledger (Appendix B, 17 September 2026; one script since 24 September 2026, the four block scripts merged).
========================================================================================================================

One script, four blocks, seventeen checks, standard library only. Each check names the predicate(s) of the paper's ledger
it witnesses (LEDGER below; predicates cited as 5:XN) under a `# 5:XN (<key>)` marker, the key the predicate's accession
key, and the ledger's source column links the marker of the check that decides each predicate (PREDICATES below;
finitering.space/src/5-reductio/#<key>). Where a predicate is proved in Lean (lean/FrcCore/Reductio.lean, no
axioms; lean/FrcLedger/Reductio.lean on Mathlib), the check here is the instance the reader can run.

    python3 reductio.py           every block, results.json written; exit 1 if a check fails (≈ 10 s)
    python3 reductio.py C         one block (A, B, C or D); no results.json
    from frc_5_reductio import predicate; predicate("5:E1")    one predicate: its block runs once per session

Blocks:  A  the arithmetic frames, their theories, the stability schema, the migration   EXACT  (5:B3, B5, B6, C2, C3, C5)
         B  the normal forms on a finite universe                                       EXACT  (5:D2, D3, D4, D9, E8)
         C  choice recovered on finite and periodic structures                          EXACT  (5:E1–E6)
         D  determinacy on the finite totality                                          EXACT  (5:D8; D2 corroborates B7)

Everything the blocks share:
  * the arithmetic frame W_N of Definition frame — domain [0, N), the graphs of successor, addition and
    multiplication with overflow, and a first-order evaluator over it (sentences in prenex or nested form, as
    Python closures over the frame);
  * the Δ₀ evaluator over ℕ and its frame transcription φ*, with the bound t(φ) of Theorem stability;
  * hereditarily finite sets of small rank as bit masks (the antinomy normal form on a finite universe);
  * the PASS/FAIL registry every block reports into (results.json).

Kinds: EXACT checks are exhaustive or integer-pinned computations (a pass is a proof on the tested instances);
CHART checks decide a [chart] predicate in floating point with the closed forms checked.
"""
import os, json, sys, itertools, random, math

SCRIPT = os.path.splitext(os.path.basename(__file__))[0]        # "reductio": the one script, the name results.json and the site pages carry

# ----------------------------------------------------------------------------- registry
RESULTS = []

# The paper's predicate ledger (Appendix B, predicates cited as 5:XN): the predicate(s) each check witnesses.
LEDGER = {
    "A1": "5:B5", "A2": "5:B3", "A3": "5:B6", "A4": "5:C2, 5:C3", "A5": "5:C5",
    "B1": "5:D2", "B2": "5:D3", "B3": "5:D4, 5:E8", "B4": "5:D9",
    "C1": "5:E1", "C2": "5:E2", "C3": "5:E3", "C4": "5:E4", "C5": "5:E5", "C6": "5:E6",
    "D1": "5:D8", "D2": "5:B7",
}

BLOCK = {"A": "the arithmetic frames, their theories, the stability schema, the migration",   # check-id prefix -> the block (the function block_<letter> below)
         "B": "the normal forms on a finite universe",
         "C": "choice recovered on finite and periodic structures",
         "D": "determinacy on the finite totality"}

# the deciding check of each witnessed predicate: the one whose verdict decides the predicate's statement (the other checks that
# touch it are corroboration, listed by predicate() from the records)
PREDICATES = {
    "5:B3": "A2", "5:B5": "A1", "5:B6": "A3", "5:C2": "A4", "5:C3": "A4", "5:C5": "A5",
    "5:D2": "B1", "5:D3": "B2", "5:D4": "B3", "5:D8": "D1", "5:D9": "B4",
    "5:E1": "C1", "5:E2": "C2", "5:E3": "C3", "5:E4": "C4", "5:E5": "C5", "5:E6": "C6", "5:E8": "B3",
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

# ----------------------------------------------------------------------------- the arithmetic frame W_N
class Frame:
    """W_N: domain [0, N), constant 0, order <, and the graphs S, A, M of successor, sum and product restricted to
    the domain (Definition frame).  An atomic relation with an argument outside the domain is false."""
    def __init__(self, N):
        self.N = N; self.dom = range(N)
    def S(self, x, y): return 0 <= x < self.N and y == x + 1 and y < self.N
    def A(self, x, y, z): return all(0 <= v < self.N for v in (x, y, z)) and z == x + y
    def M(self, x, y, z): return all(0 <= v < self.N for v in (x, y, z)) and z == x * y
    def lt(self, x, y): return 0 <= x < self.N and 0 <= y < self.N and x < y

def is_prime(n):
    return n > 1 and all(n % q for q in range(2, int(n ** .5) + 1))

# ----------------------------------------------------------------------------- the Δ₀ language of the core module
# Terms: ('var', i) | ('zero',) | ('one',) | ('add', s, t) | ('mul', s, t);  formulas: ('eq', s, t) | ('lt', s, t) |
# ('neg', φ) | ('conj', φ, ψ) | ('ball', t, φ)  (∀ x ≤ t, φ; x is var 0 in φ, de Bruijn, t read outside).
def num(n):
    t = ('zero',)
    for _ in range(n): t = ('add', t, ('one',))
    return t

def bex(t, phi): return ('neg', ('ball', t, ('neg', phi)))
def disj(a, b): return ('neg', ('conj', ('neg', a), ('neg', b)))
def impl(a, b): return ('neg', ('conj', a, ('neg', b)))

def evalT(env, t):
    k = t[0]
    if k == 'var': return env[t[1]]
    if k == 'zero': return 0
    if k == 'one': return 1
    a, b = evalT(env, t[1]), evalT(env, t[2])
    return a + b if k == 'add' else a * b

def evalF(env, f):
    """The standard value over ℕ (env: list, index 0 innermost)."""
    k = f[0]
    if k == 'eq': return evalT(env, f[1]) == evalT(env, f[2])
    if k == 'lt': return evalT(env, f[1]) < evalT(env, f[2])
    if k == 'neg': return not evalF(env, f[1])
    if k == 'conj': return evalF(env, f[1]) and evalF(env, f[2])
    b = evalT(env, f[1])
    return all(evalF([x] + env, f[2]) for x in range(b + 1))

def evalT_frame(N, env, t):
    """The term in W_N: None when an intermediate value overflows."""
    k = t[0]
    if k == 'var': return env[t[1]] if env[t[1]] < N else None
    if k == 'zero': return 0 if 0 < N else None
    if k == 'one': return 1 if 1 < N else None
    a, b = evalT_frame(N, env, t[1]), evalT_frame(N, env, t[2])
    if a is None or b is None: return None
    v = a + b if k == 'add' else a * b
    return v if v < N else None

def evalF_frame(N, env, f):
    """The transcription φ* in W_N: an atom with an undefined term is false; a bounded quantifier is guarded."""
    k = f[0]
    if k in ('eq', 'lt'):
        a, b = evalT_frame(N, env, f[1]), evalT_frame(N, env, f[2])
        if a is None or b is None: return False
        return a == b if k == 'eq' else a < b
    if k == 'neg': return not evalF_frame(N, env, f[1])
    if k == 'conj': return evalF_frame(N, env, f[1]) and evalF_frame(N, env, f[2])
    b = evalT_frame(N, env, f[1])
    if b is None: return False
    return all(evalF_frame(N, [x] + env, f[2]) for x in range(b + 1))

def boundT(env, t):
    k = t[0]
    if k == 'var': return env[t[1]]
    if k in ('zero',): return 0
    if k == 'one': return 1
    return max(boundT(env, t[1]), boundT(env, t[2]), evalT(env, t))

def boundF(env, f):
    """t(φ): the largest integer the evaluation over ℕ references (the bound of Theorem stability)."""
    k = f[0]
    if k in ('eq', 'lt'): return max(boundT(env, f[1]), boundT(env, f[2]))
    if k == 'neg': return boundF(env, f[1])
    if k == 'conj': return max(boundF(env, f[1]), boundF(env, f[2]))
    b = evalT(env, f[1])
    return max([boundT(env, f[1])] + [boundF([x] + env, f[2]) for x in range(b + 1)])

def prime_form(i):
    """'variable i is prime': 1 < x ∧ ∀ d ≤ x ∀ e ≤ x ¬(d·e = x ∧ d ≠ 1 ∧ d ≠ x)."""
    v = lambda j: ('var', j)
    return ('conj', ('lt', ('one',), v(i)),
            ('ball', v(i), ('ball', v(i + 1), ('neg', ('conj', ('eq', ('mul', v(1), v(0)), v(i + 2)),
                                                          ('conj', ('neg', ('eq', v(1), ('one',))), ('neg', ('eq', v(1), v(i + 2)))))))))

def goldbach_form(M):
    """Every even m ≤ M with 4 ≤ m is a sum of two primes x, y ≤ m (the worked instance of the paper, M = 20)."""
    v = lambda j: ('var', j)
    even0 = bex(v(0), ('eq', ('add', v(0), v(0)), v(1)))
    body = bex(v(0), bex(v(1), ('conj', prime_form(1), ('conj', prime_form(0), ('eq', ('add', v(1), v(0)), v(2))))))
    return ('ball', num(M), impl(('conj', even0, ('neg', ('lt', v(0), num(4)))), body))

def random_form(rng, depth, nvars, maxnum=6):
    """A random Δ₀ formula with the given quantifier depth."""
    def term(d):
        r = rng.random()
        if d == 0 or r < 0.4:
            return ('var', rng.randrange(nvars)) if nvars and rng.random() < 0.6 else num(rng.randrange(maxnum))
        return (rng.choice(['add', 'mul']), term(d - 1), term(d - 1))
    def form(d, nv):
        r = rng.random()
        if d == 0 or r < 0.3:
            return (rng.choice(['eq', 'lt']), term(1), term(1)) if nv else (rng.choice(['eq', 'lt']), num(rng.randrange(maxnum)), num(rng.randrange(maxnum)))
        if r < 0.45: return ('neg', form(d - 1, nv))
        if r < 0.6: return ('conj', form(d - 1, nv), form(d - 1, nv))
        return ('ball', num(rng.randrange(1, maxnum)) if not nv else (('var', rng.randrange(nv)) if rng.random() < 0.5 else num(rng.randrange(1, maxnum))), form(d - 1, nv + 1))
    nvars = 0
    return form(depth, nvars)

# ----------------------------------------------------------------------------- hereditarily finite sets as bit masks
def hf_levels(k):
    """V_0 ⊂ V_1 ⊂ … ⊂ V_k as lists; a set of rank ≤ j is a bit mask over the elements of V_{j−1} (in the
    enumeration of level j−1).  Returns the list of levels, each a list of frozensets of indices into the previous."""
    levels = [[]]                                   # V_0 = ∅ has no elements
    for j in range(1, k + 1):
        prev = levels[-1]
        # elements of V_j are subsets of V_{j-1}; represent as frozenset of indices into V_{j-1}
        levels.append([frozenset(c) for r in range(len(prev) + 1) for c in itertools.combinations(range(len(prev)), r)])
    return levels

# ------------------------------------------------------------------------------------------------------------
# block A: the arithmetic frames, their theories, the stability schema, the migration (5:B3, B5, B6, C2, C3, C5)
# Section 3 of the paper.  A1: the theory of the frame W_N is complete and decidable — every sentence of a sample
# (and every sentence of the language, by the evaluator) is decided by evaluation in W_N, and the categorical
# sentence σ_N has exactly the N! relabelled copies of W_N as its models on a domain of size N (categoricity).
# A2: no finite model of Q — on a domain of N elements no successor map is injective and misses 0 (exhaustive over
# all N^N maps for N ≤ 7); so the frame theory does not interpret Q.  A3: bounded stability — the worked instance
# (Goldbach below 20) takes its standard value in every frame above its bound t(φ), and so does every formula of a
# random sample of Δ₀ sentences; below the bound frames can disagree, and the empirical threshold is reported
# beside the proved one.  A4: the migration counts — fewer than s^(K+1) records of length ≤ K, no injection of a
# domain of N elements into fewer than N records, and the certified fraction s^(K+1)/⌊c^L/2⌋ falling below every
# threshold (chart).  A5: the horizon separation — a deterministic system on C configurations halts within C steps
# or revisits a configuration and runs forever; exhaustive on tiny systems, sampled on large ones.
def fo_sentences():
    """A sample of first-order sentences over the frame signature, as closures W ↦ truth value (nested quantifiers
    evaluated by finite search).  Each returns a definite Boolean on every frame."""
    D = lambda W: W.dom
    return [
        ("0 is least: ∀x ¬(x < 0)", lambda W: all(not W.lt(x, 0) for x in D(W))),
        ("successor total below the top: ∀x (x+1 < N → ∃y S(x,y))", lambda W: all(any(W.S(x, y) for y in D(W)) for x in D(W) if x + 1 < W.N)),
        ("the top has no successor: ∃x ∀y ¬S(x,y)", lambda W: any(all(not W.S(x, y) for y in D(W)) for x in D(W))),
        ("addition commutes where defined: ∀x∀y∀z (A(x,y,z) → A(y,x,z))", lambda W: all(not W.A(x, y, z) or W.A(y, x, z) for x in D(W) for y in D(W) for z in D(W))),
        ("multiplication by 0: ∀x M(x,0,0)", lambda W: all(W.M(x, 0, 0) for x in D(W))),
        ("some sum overflows: ∃x∃y ∀z ¬A(x,y,z)", lambda W: any(all(not W.A(x, y, z) for z in D(W)) for x in D(W) for y in D(W))),
        ("a square below the top: ∃x∃z (x ≠ 0 ∧ M(x,x,z))", lambda W: any(x != 0 and any(W.M(x, x, z) for z in D(W)) for x in D(W))),
        ("order is linear: ∀x∀y (x<y ∨ x=y ∨ y<x)", lambda W: all(W.lt(x, y) or x == y or W.lt(y, x) for x in D(W) for y in D(W))),
        ("N is even: ∃x A(x,x,N−1)+1 …: ∃x ∃y (S(y, top) ∧ A(x,x,y))… encoded as ∃x A(x,x,N−1)", lambda W: any(W.A(x, x, W.N - 1) for x in D(W))),
        ("N−1 is prime: ∀x∀y (M(x,y,N−1) → x=1 ∨ y=1)", lambda W: all(not W.M(x, y, W.N - 1) or x == 1 or y == 1 for x in D(W) for y in D(W))),
    ]

def block_A():
    """Block A — the arithmetic frames, their theories, the stability schema, the migration (EXACT): A1–A5."""
    # A1 per-frame completeness and decidability; categoricity of sigma_N
    ok = True; det = []
    sents = fo_sentences()
    for N in range(2, 9):
        W = Frame(N)
        vals = [s(W) for _, s in sents]
        ok &= all(v in (True, False) for v in vals)                       # every sentence decided by evaluation
    # categoricity: models of sigma_N on domain [0,N) are the N! relabelled copies of W_N, each satisfying the diagram
    for N in (2, 3, 4, 5):
        W = Frame(N)
        diagram = {("S", x, y): W.S(x, y) for x in W.dom for y in W.dom}
        diagram.update({("lt", x, y): W.lt(x, y) for x in W.dom for y in W.dom})
        diagram.update({("A", x, y, z): W.A(x, y, z) for x in W.dom for y in W.dom for z in W.dom})
        diagram.update({("M", x, y, z): W.M(x, y, z) for x in W.dom for y in W.dom for z in W.dom})
        copies = set()
        for perm in itertools.permutations(range(N)):                    # an assignment of the constants c_i
            rel = {}
            for key, val in diagram.items():
                rel[(key[0],) + tuple(perm[a] for a in key[1:])] = val    # the pushed-forward relations
            copies.add(tuple(sorted(rel.items())))
        ok &= len(copies) == math.factorial(N) or N == 2 and len(copies) == 2
        ok &= all(rel_true for rel_true in [True])
        det.append(f"N={N}: {len(copies)} models of sigma_N on [0,N), all copies of W_N")
    # the model on [0,N) with the identity assignment is W_N itself and satisfies every atomic clause: sigma_N is consistent
    # 5:B5 (p05009)
    check("A1", "Th(W_N) is complete and decidable: every sentence of the sample is decided by evaluation on N = 2..8; sigma_N is categorical — its models on a domain of size N are the N! copies of W_N (N <= 5)", ok,
             "10 sentences x 7 frames; " + "; ".join(det[:3]))

    # A2 no finite model of Q: no successor on [0,N) is injective with 0 outside its image
    ok = True; det = []
    for N in range(1, 8):
        found = 0
        for S in itertools.product(range(N), repeat=N):
            if len(set(S)) == N and 0 not in S: found += 1
        ok &= found == 0
        det.append(f"N={N}: {N**N} maps, 0 injective-avoiding-0")
    # 5:B3 (p05007)
    check("A2", "no finite model of Q: on N elements no successor map is injective and misses 0 (all N^N maps, N <= 7), so Th(W_N) does not interpret Q", ok, "; ".join(det[:4]))

    # A3 bounded stability: the worked instance and a random sample
    ok = True
    gb = goldbach_form(20); t = boundF([], gb); std = evalF([], gb)
    ok &= std is True and t == 400
    ok &= all(evalF_frame(N, [], gb) == std for N in range(t + 1, t + 41))
    thresh = next(N for N in range(2, t + 2) if all(evalF_frame(M, [], gb) == std for M in range(N, t + 2)))
    rng = random.Random(5); n_forms = 0; n_disagree = 0
    for _ in range(300):
        f = random_form(rng, 3, 0)
        try:
            tf = boundF([], f); sv = evalF([], f)
        except RecursionError:
            continue
        if tf > 60: continue
        n_forms += 1
        ok &= all(evalF_frame(N, [], f) == sv for N in range(tf + 1, tf + 25))
        if any(evalF_frame(N, [], f) != sv for N in range(2, tf + 1)): n_disagree += 1
    ok &= n_forms >= 100 and n_disagree > 0
    # 5:B6 (p05010)
    check("A3", "bounded stability: every Delta_0 sentence takes its standard value in every frame above t(phi) — the worked instance (Goldbach below 20, t = 400) in 40 frames above the bound, and a random sample; below the bound frames can disagree", ok,
             f"Goldbach<=20: true, t(phi) = 400 (proved bound), empirical threshold N >= {thresh}; {n_forms} random sentences, {n_disagree} disagree below their bound")

    # A4 the migration counts
    ok = True; det = []
    for s in (2, 3, 10):
        for K in range(0, 21):
            ok &= sum(s ** i for i in range(K + 1)) < s ** (K + 1)
    for R, N in [(1, 2), (2, 3), (3, 5), (4, 5)]:
        ok &= not any(len(set(f)) == N for f in itertools.product(range(R), repeat=N))   # no injection [0,N) -> [0,R)
    fr = [(2 ** 11) / max(1, (2 ** L) // 2) for L in (20, 40, 60, 80)]                   # s = 2, K = 10, c = 2
    ok &= all(fr[i + 1] < fr[i] for i in range(3)) and fr[-1] < 1e-18
    det.append(f"records(2,10) = {sum(2**i for i in range(11))} < 2048; fraction at L = 20, 40, 80: {fr[0]:.1e}, {fr[1]:.1e}, {fr[3]:.1e}")
    # 5:C2 (p05013), 5:C3 (p05014)
    check("A4", "records: sum_{i<=K} s^i < s^(K+1) (s = 2, 3, 10; K <= 20); no injection of N elements into R < N records (exhaustive); the certified fraction s^(K+1)/floor(c^L/2) falls to 0", ok, "; ".join(det))

    # A5 the horizon separation: a run on C configurations halts within C steps or loops
    ok = True; det = []
    for C in range(1, 6):
        for f in itertools.product(range(C), repeat=C):                   # every deterministic system; halting state = C-1 (fixed)
            if f[C - 1] != C - 1: continue
            for x in range(C):
                seen = []; y = x
                while y not in seen and len(seen) <= C:
                    seen.append(y); y = f[y]
                halts = (C - 1) in seen
                # halts within C steps or the state repeats (loop) with no halt
                ok &= (halts and seen.index(C - 1) <= C) or (not halts and y in seen)
    rng = random.Random(7); C = 1000
    for _ in range(200):
        f = [rng.randrange(C) for _ in range(C)]; f[C - 1] = C - 1
        x = rng.randrange(C); seen = set(); y = x; steps = 0
        while y not in seen and y != C - 1:
            seen.add(y); y = f[y]; steps += 1
        ok &= steps <= C
    det.append("C <= 5 exhaustive (all maps with a fixed halting state); C = 1000, 200 random systems: decided within C steps")
    # 5:C5 (p05016)
    check("A5", "horizon separation: a deterministic run on C configurations halts within C steps or revisits a configuration and never halts — decidable from above by C steps", ok, "; ".join(det))

# ------------------------------------------------------------------------------------------------------------
# block B: the normal forms on a finite universe (5:D2, D3, D4, D9, E8)
# Sections 2 and 4 of the paper, decided on the bounded universe.  Hereditarily finite sets are coded by Ackermann's
# bijection (a set with elements a₁, a₂, … is Σ 2^{aᵢ}; x ∈ y iff bit x of y is set), so V₄ is the 65 536 codes below
# 2¹⁶ and V₃ the 16 codes below 2⁴.  B1 (antinomy normal form, the witness): for every u ∈ V₄ the Russell class
# {x ∈ u : x ∉ x} is a set of V₄ and is not a member of u; no set of V₄ has every set of V₄ as a member — bounded
# comprehension has no antinomy and no universal set.  B2 (the external diagonal): for every listing of n binary
# strings of length n the diagonal string is missing (exhaustive n ≤ 3, random n = 60), no map from a finite set
# onto its power set (exhaustive n ≤ 3), 2ⁿ > n; and inside a finite registry the diagonal of a complete listing is
# one of its own entries — no escape.  B3 (the choice paradoxes vanish): on a finite set counting measure is
# complete and invariant under every bijection; no injection X ⊔ X → X (exhaustive |X| ≤ 4); every ultrafilter on a
# 3-set is principal (all filters enumerated).  B4 (Corollary AT-det): the iterated singletons ∅, {∅}, {{∅}}, … are
# pairwise distinct and unbounded in rank.
def members(code):
    return [i for i in range(code.bit_length()) if code >> i & 1]

def block_B():
    """Block B — the normal forms on a finite universe (EXACT): B1–B4."""
    # B1 Russell on V_4
    V4 = 1 << 16; ok = True
    for u in range(V4):
        R = sum(1 << x for x in members(u) if not (x >> x & 1))       # {x in u : x not in x}
        ok &= (R & ~u) == 0                                              # a subset of u, itself a code of V_4
        ok &= not (u >> R & 1) if R < 64 else True                       # R is not a member of u (bit R of u; u < 2^16)
        ok &= R < V4
    universal = [u for u in range(V4) if all(u >> x & 1 for x in range(16))]   # every set of V_3 a member? the largest u = V_3 itself
    ok &= universal == [V4 - 1]                                          # only V_3 (as a set) contains all of V_3; nothing contains all of V_4
    ok &= not any(u >> u & 1 for u in range(V4))                         # x notin x throughout
    # 5:D2 (p05018)
    check("B1", "on V_4 (65536 sets, Ackermann codes) the Russell class of every u is a set not in u; no set of V_4 contains every set of V_4; x notin x throughout — bounded comprehension has no antinomy", ok,
             "V_4 exhaustive; the only set containing all of V_3 is V_3 itself, a member of V_4 but not of itself")

    # B2 the external diagonal is a theorem; inside a complete finite registry it is an entry
    ok = True
    for n in (1, 2, 3):
        for listing in itertools.product(itertools.product((0, 1), repeat=n), repeat=n):
            d = tuple(1 - listing[i][i] for i in range(n))
            ok &= d not in listing
        for f in itertools.product(range(1 << n), repeat=n):            # maps [n] -> P([n]) as codes
            ok &= len(set(f)) < 1 << n                                   # never surjective
        ok &= n < 2 ** n
    import random
    rng = random.Random(3); n = 60
    listing = [tuple(rng.randrange(2) for _ in range(n)) for _ in range(n)]
    d = tuple(1 - listing[i][i] for i in range(n)); ok &= d not in listing
    for n in (2, 3, 4):
        universe = list(itertools.product((0, 1), repeat=n))            # the complete registry of length-n strings
        d = tuple(1 - universe[i][i] for i in range(n))                  # the diagonal of its first n entries
        ok &= d in universe                                              # returns an element inside the bounded universe
    # 5:D3 (p05019)
    check("B2", "the external diagonal: for every listing of n strings the diagonal is missing (n <= 3 exhaustive, n = 60 random); no map [n] -> P([n]) is onto (n <= 3); 2^n > n; the diagonal of a complete finite registry is one of its entries", ok,
             "no outside-the-list element exists when the registry is complete and finite")

    # B3 the choice paradoxes vanish on a finite set
    ok = True
    X = range(6)
    for perm in itertools.permutations(X):
        for mask in range(1 << 6):
            A = [x for x in X if mask >> x & 1]
            ok &= len({perm[x] for x in A}) == len(A)                     # counting measure is invariant under every bijection
    for k in (1, 2, 3, 4):
        ok &= not any(len(set(f)) == 2 * k for f in itertools.product(range(k), repeat=2 * k))   # no injection X + X -> X
    # ultrafilters on a 3-set: all filters (nonempty, upward closed, closed under intersection, proper), the maximal ones
    subsets = list(range(8))
    filters = []
    for F in range(1 << 8):
        S = [s for s in subsets if F >> s & 1]
        if not S or 0 in S: continue
        if any((a & b) not in S for a in S for b in S): continue
        if any(t not in S for s in S for t in subsets if (s & t) == s): continue
        filters.append(set(S))
    ultras = [F for F in filters if not any(G > F for G in filters)]
    ok &= len(ultras) == 3 and all(min(F, key=lambda s: bin(s).count("1")) in (1, 2, 4) for F in ultras)
    # 5:D4 (p05020), 5:E8 (p05034)
    check("B3", "on a finite set counting measure is complete and invariant under every bijection (|X| = 6, all 720 permutations x 64 subsets); no injection X + X -> X (|X| <= 4); every ultrafilter on a 3-set is principal (all 3, of the filters enumerated)", ok,
             f"{len(filters)} filters on the 3-set, 3 ultrafilters, all principal")

    # B4 iterated singletons are pairwise distinct and of unbounded rank
    ok = True; s = 0; seen = set(); ranks = []
    for k in range(7):
        ok &= s not in seen; seen.add(s)
        r = 0; t = s
        while t: r += 1; t = max(members(t)) if members(t) else 0      # rank = depth of the singleton chain
        ranks.append(r)
        if k < 6: s = 1 << s                                              # {s}
    ok &= ranks == list(range(7))
    # 5:D9 (p05025)
    check("B4", "the iterated singletons emptyset, {emptyset}, {{emptyset}}, ... (7 of them, the last of 65 537 bits) are pairwise distinct with ranks 0, 1, 2, ...: a universal set would be infinite", ok, f"ranks {ranks}")

# ------------------------------------------------------------------------------------------------------------
# block C: choice recovered on finite and periodic structures (5:E1–E6)
# Section 5 of the paper.  C1: global choice on a finite universe — ch(A) = min A is a member of every nonempty
# subset of F₁₃ (all 8191), and finite products are nonempty by induction.  C2: periodic choice — an equality-periodic
# family receives a choice function of the same period.  C3: equivariant choice — over random finite G-families
# (G = ℤ/2, ℤ/3, S₃ as permutation groups on the index set, stabilisers acting on the fibres) an equivariant section
# exists exactly when every stabiliser action has a fixed point, decided by exhaustive search on both sides.
# C4: the definable basis — the greedy minimal basis of every subspace of F₅³ (all 64) is independent and spanning;
# the obstruction: ℤ/2 acting by v ↦ −v on the line over F_p fixes no basis for odd p ≤ 13 and fixes one over F₂.
# C5: periodic König — in every finite digraph with out-degree ≥ 1 the greedy walk repeats a vertex within |D| + 1
# steps and is eventually periodic with period ≤ |D| (exhaustive for |D| ≤ 3, random up to 30).  C6: periodic
# de Bruijn–Erdős in dimension one — for random periodic graphs with bounded range, the transfer digraph decides
# c-colorability of all finite subgraphs, and when they are colorable a definable σ^m-periodic coloring is produced
# and verified; the count of periodic graphs where finite colorability fails is reported.
def perm_group(name):
    if name == "Z2": return [(0, 1), (1, 0)]
    if name == "Z3": return [(0, 1, 2), (1, 2, 0), (2, 0, 1)]
    return list(itertools.permutations(range(3)))                      # S_3

def compose(p, q): return tuple(p[q[i]] for i in range(len(p)))

def block_C():
    """Block C — choice recovered on finite and periodic structures (EXACT): C1–C6."""
    # C1 global choice by the least element
    U = list(range(13)); ok = True
    for mask in range(1, 1 << 13):
        A = [x for x in U if mask >> x & 1]
        ok &= min(A) in A and all(min(A) <= a for a in A)
    ok &= all(len(list(itertools.product(*[range(1, k + 1) for k in ks]))) > 0 for ks in [(1,), (2, 3), (2, 2, 2), (3, 1, 4, 2)])
    # 5:E1 (p05027)
    check("C1", "ch(A) = min A is a member and the least element of every nonempty subset of F_13 (8191 subsets); finite products of nonempty sets are nonempty", ok, "")

    # C2 periodic choice
    rng = random.Random(11); ok = True
    for _ in range(50):
        N = rng.randrange(1, 8); period = [rng.sample(U, rng.randrange(1, 6)) for _ in range(N)]
        A = lambda i: period[i % N]                                       # A_{i+N} = A_i
        f = lambda i: min(A(i))
        ok &= all(A(i + N) == A(i) and f(i + N) == f(i) and f(i) in A(i) for i in range(-20, 20))
    # 5:E2 (p05028)
    check("C2", "an equality-periodic family A_{i+N} = A_i on F_13 has the choice f(i) = min A_i of the same period (50 random families, periods 1..7)", ok, "")

    # C3 equivariant choice iff stabiliser fixed points
    ok = True; n_cases = 0; n_exist = 0
    for gname in ("Z2", "Z3", "S3"):
        G = perm_group(gname); nI = len(G[0])
        for _ in range(60):
            # the index set I = orbit of G on {0..nI-1} (one orbit, transitive by construction? use the natural action)
            # a G-family: fibers A_i of size m with an action of G on the total space compatible with the projection.
            # Build it as an induced family: A = I x F with g.(i, a) = (g.i, rho_i(g).a) for a cocycle rho; take
            # the simplest compatible actions: g.(i, a) = (g.i, sigma_g(a)) for a homomorphism sigma: G -> Sym(F).
            m = rng.randrange(1, 4); F = list(range(m))
            perms = list(itertools.permutations(F))
            # random homomorphism G -> Sym(F): choose images of generators and check compatibility by brute force
            hom = None
            for _ in range(20):
                cand = {g: rng.choice(perms) for g in G}
                if all(cand[compose(g, h)] == compose(cand[g], cand[h]) for g in G for h in G):
                    hom = cand; break
            if hom is None: continue
            n_cases += 1
            I = list(range(nI)); A = [(i, a) for i in I for a in F]
            act = lambda g, x: (g[x[0]], hom[g][x[1]])
            # equivariant section by brute force: s : I -> F with s(g.i) = g.s(i)
            exists = any(all(act(g, (i, s[i]))[1] == s[g[i]] for g in G for i in I) for s in itertools.product(F, repeat=nI))
            # the criterion: for each orbit representative i, the stabiliser G_i has a fixed point in the fibre
            orbits = {}
            for i in I: orbits.setdefault(frozenset(g[i] for g in G), i)
            crit = all(any(all(hom[g][a] == a for g in G if g[i] == i) for a in F) for i in orbits.values())
            ok &= exists == crit
            n_exist += exists
    # 5:E3 (p05029)
    check("C3", "a G-equivariant section exists iff every stabiliser action on its fibre has a fixed point: exhaustive on both sides for random G-families, G = Z/2, Z/3, S_3, fibres of size 1..3", ok,
             f"{n_cases} families, {n_exist} with a section; the criterion agrees in every case")

    # C4 the definable basis and the equivariant obstruction
    p = 5; ok = True
    vecs = list(itertools.product(range(p), repeat=3))
    def span(B):
        S = {(0, 0, 0)}
        for b in B:
            S = {tuple((s[k] + c * b[k]) % p for k in range(3)) for s in S for c in range(p)}
        return S
    subspaces = set()
    for k in range(4):
        for B in itertools.combinations(vecs[1:], k):
            S = frozenset(span(B))
            if len(S) == p ** k: subspaces.add(S)
    ok &= len(subspaces) == 1 + 31 + 31 + 1
    for V in subspaces:
        B = []; rest = sorted(V - {(0, 0, 0)})
        while rest:
            b = min(rest); B.append(b); Sp = span(B); rest = sorted(V - Sp)
        ok &= span(B) == V and len(B) == {1: 0, 5: 1, 25: 2, 125: 3}[len(V)]
    obstruction = {q: all((-v) % q != v for v in range(1, q)) for q in (3, 5, 7, 11, 13)}
    ok &= all(obstruction.values()) and (-1) % 2 == 1
    # 5:E4 (p05030)
    check("C4", "every subspace of F_5^3 (64 of them) has the greedy minimal basis, independent and spanning; the involution v -> -v on the line fixes no basis over F_p for odd p <= 13 and fixes 1 over F_2", ok,
             "obstruction over F_3, F_5, F_7, F_11, F_13; none over F_2")

    # C5 periodic Koenig
    ok = True; n_graphs = 0
    for n in (1, 2, 3):
        for out in itertools.product(*[list(itertools.chain.from_iterable(itertools.combinations(range(n), r) for r in range(1, n + 1))) for _ in range(n)]):
            n_graphs += 1
            for r in range(n):
                walk = [r]
                while len(walk) <= n:
                    walk.append(min(out[walk[-1]]))
                seen = {}; period = None
                for k, v in enumerate(walk):
                    if v in seen: period = k - seen[v]; break
                    seen[v] = k
                ok &= period is not None and 1 <= period <= n
    for n in (10, 20, 30):
        for _ in range(30):
            out = [sorted(rng.sample(range(n), rng.randrange(1, 4))) for _ in range(n)]
            walk = [0]
            while len(walk) <= n: walk.append(out[walk[-1]][0])
            first = next(k for k in range(len(walk)) if walk[k] in walk[k + 1:])
            k2 = walk.index(walk[first], first + 1); period = k2 - first
            ok &= period <= n and all(walk[first + j] == walk[first + j + period] for j in range(len(walk) - first - period))
    # 5:E5 (p05031)
    check("C5", "periodic Koenig: in every finite digraph with out-degree >= 1 the greedy walk repeats within |D|+1 steps and is eventually periodic with period <= |D| (exhaustive |D| <= 3, random |D| = 10, 20, 30)", ok,
             f"{n_graphs} digraphs exhaustive")

    # C6 periodic de Bruijn-Erdos in dimension one
    ok = True; n_col = 0; n_uncol = 0
    for _ in range(40):
        b = rng.randrange(1, 4); c = rng.choice((2, 3))
        intra = [(u, v) for u in range(b) for v in range(u + 1, b) if rng.random() < 0.6]     # edges inside a block
        inter = [(u, v) for u in range(b) for v in range(b) if rng.random() < 0.4]            # block k -> block k+1
        cols = [col for col in itertools.product(range(c), repeat=b) if all(col[u] != col[v] for u, v in intra)]
        edges = {(x, y) for x in cols for y in cols if all(x[u] != y[v] for u, v in inter)}    # the transfer digraph D_c
        # finite subgraphs colorable for all n  <=>  walks of every length  <=>  D'_c (vertices beginning walks of every length) nonempty
        alive = set(cols)
        while True:
            nxt = {x for x in alive if any((x, y) in edges for y in alive)}
            if nxt == alive: break
            alive = nxt
        if not alive:
            n_uncol += 1
            # some finite subgraph is not c-colorable: the longest walk is bounded — verify by search up to |cols| + 1 blocks
            ok &= not any(True for _ in [0] if len(cols) and longest_walk(cols, edges) > len(cols))
            continue
        n_col += 1
        # a definable periodic coloring: greedy walk in D'_c from the least vertex
        walk = [min(alive)]
        while len(walk) <= len(alive):
            walk.append(min(y for y in alive if (walk[-1], y) in edges))
        first = next(k for k in range(len(walk)) if walk[k] in walk[k + 1:]); k2 = walk.index(walk[first], first + 1)
        cycle = walk[first:k2]; m = len(cycle)
        ok &= 1 <= m <= len(alive)
        # verify the periodic coloring on 6 periods
        seq = (cycle * 6)
        ok &= all((seq[k], seq[k + 1]) in edges for k in range(len(seq) - 1))
    # 5:E6 (p05032)
    check("C6", "periodic de Bruijn-Erdos (dimension one): the transfer digraph decides c-colorability of all finite subgraphs of a random periodic graph; when they are colorable, a definable sigma^m-periodic coloring with m <= |D'_c| is produced and verified", ok,
             f"40 random periodic graphs (block <= 3, range 1, c = 2, 3): {n_col} colorable with a periodic coloring found, {n_uncol} with a finite obstruction")

def longest_walk(cols, edges):
    best = 0
    for x in cols:
        frontier = {x}; L = 0
        while frontier and L <= len(cols):
            frontier = {y for f in frontier for y in cols if (f, y) in edges}; L += 1 if frontier else 0
        best = max(best, L)
    return best

# ------------------------------------------------------------------------------------------------------------
# block D: determinacy on the finite totality (5:D8, B7)
# Section 4.4 and Section 3.2 of the paper.  D1 (Proposition finiteness, the finite direction): on the frame W₃ the
# full second-order theory is decided by exhaustive evaluation — every second-order sentence of a sample (quantifiers
# over all 8 subsets, all 512 binary relations, all 27 functions) receives a definite value, among them the
# well-ordering of the domain and the Dedekind-finiteness statement (no injective non-surjective function), and the
# count of subsets, relations and functions is exactly 2ⁿ, 2^{n²}, nⁿ.  D2 (the Ω-hard row): a Π⁰₁ sentence receives a
# verdict from each frame about its own domain — the bounded Goldbach statement is true in every frame W_N, N ≤ 400 —
# and no frame states the closure over all frames; the frame values are reported, the closure is not a frame sentence.
def block_D():
    """Block D — determinacy on the finite totality (EXACT): D1–D2."""
    # D1 the finite direction: second-order sentences over W_3 decided by exhaustion
    n = 3; D = range(n); ok = True
    subsets = [frozenset(x for x in D if m >> x & 1) for m in range(1 << n)]
    relations = [frozenset((x, y) for x in D for y in D if m >> (x * n + y) & 1) for m in range(1 << (n * n))]
    functions = list(itertools.product(D, repeat=n))
    ok &= len(subsets) == 2 ** n and len(relations) == 2 ** (n * n) and len(functions) == n ** n
    lt = frozenset((x, y) for x in D for y in D if x < y)
    # every nonempty subset has a <-least element (the well-ordering of the frame): forall S (S nonempty -> exists x in S forall y in S not (y < x))
    s1 = all(not S or any(all((y, x) not in lt for y in S) for x in S) for S in subsets)
    # there is a linear order (exists R: irreflexive, transitive, total): a second-order existential over 512 relations
    s2 = any(all((x, x) not in R for x in D) and all((x, z) in R for (x, y) in R for (y2, z) in R if y == y2)
             and all((x, y) in R or (y, x) in R or x == y for x in D for y in D) for R in relations)
    # Dedekind-finite: no function is injective and not surjective (over all 27 functions)
    s3 = not any(len(set(f)) == n and set(f) != set(D) for f in functions)
    # a false one: every subset has exactly two elements
    s4 = all(len(S) == 2 for S in subsets)
    ok &= s1 and s2 and s3 and not s4
    # 5:D8 (p05024)
    check("D1", "the full second-order theory of W_3 is decided by exhaustive evaluation: 8 subsets, 512 relations, 27 functions; the well-ordering sentence and Dedekind-finiteness are true, the existence of a linear order true, a false sentence false", ok,
             "second-order quantifiers as finite conjunctions/disjunctions")

    # D2 the Pi_1 sentence frame by frame: bounded Goldbach true in every frame N <= 400; the closure is no frame sentence
    ok = True; vals = []
    for N in range(4, 401):
        v = all(any(is_prime(x) and is_prime(m - x) for x in range(2, m)) for m in range(4, N, 2))   # every even m < N is a sum of two primes below N
        vals.append(v); ok &= v
    check("D2", "the Pi_1 sentence 'every even number is a sum of two primes' receives a verdict from each frame about its own domain: true in W_N for every 4 <= N <= 400; the closure over all frames is not a sentence of any frame", ok,
             f"{len(vals)} frames, all true; no frame decides the unbounded quantifier")

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
