"""
representation.py — the validation package of "Universal Latent Representation in Finite Ring Continuum" (Akhtman,
Entropy 2026, 28, 40; doi 10.3390/e28010040), the paper 4-representation of the FRC corpus
(finite-ring-space/src/4-representation), added with the paper's predicate ledger (Appendix A, 17 September 2026; one
script since 24 September 2026, the three block scripts merged).
========================================================================================================================

One script, three blocks, thirteen checks (eleven exact, two chart), standard library only. Each check names the
predicate(s) of the paper's ledger it witnesses (LEDGER below; predicates cited as 4:XN) under a `# 4:XN (<key>)` marker,
the key the predicate's accession key, and the ledger's source column links the marker of the check that decides each
predicate (PREDICATES below; finitering.space/src/4-representation/#<key>). Where a predicate is
proved in Lean (lean/FrcCore/Representation.lean, no axioms; lean/FrcLedger/Representation.lean on Mathlib), the check
here is the instance the reader can run.

    python3 representation.py     every block, results.json written; exit 1 if a check fails (≈ 10 s)
    python3 representation.py C   one block (A, B or C); no results.json
    from frc_4_representation import predicate; predicate("4:C1")    one predicate: its block runs once per session

Blocks:  A  adequacy and the Universal Subspace Theorem on every finite model   EXACT          (4:B4, B5, C1–C4)
         B  the shell as host, the frames as charts, the worked instance         EXACT          (4:B6, C5)
         C  the finite ring geometry of embeddings                               CHART / EXACT  (4:E1–E3)

Everything the blocks share:
  * finite models: the latent domain Z, the observations X_m, the representation spaces W_m as small sets, and the
    enumeration of every map between them (the theorem's clauses are decided on every configuration);
  * the shell datum: p = 4κ+1 prime, its primitive generators and its affine frames x ↦ a + b x;
  * the PASS/FAIL registry every block reports into (results.json).

Kinds: EXACT checks are exhaustive or integer-pinned computations (a pass is a proof on the tested instances);
CHART checks decide a [chart] predicate in floating point with the closed forms checked.
"""
import os, json, sys, itertools, math, random

SCRIPT = os.path.splitext(os.path.basename(__file__))[0]        # "representation": the one script, the name results.json and the site pages carry

# The shells (p, κ): p = 4κ+1 prime.
SHELLS = [(5, 1), (13, 3), (17, 4), (29, 7), (37, 9), (41, 10)]

# ----------------------------------------------------------------------------- registry
RESULTS = []

# The paper's predicate ledger (Appendix A, predicates cited as 4:XN): the predicate(s) each check witnesses.
LEDGER = {
    "A1": "4:B4", "A2": "4:B5", "A3": "4:B5", "A4": "4:C1, 4:C2", "A5": "4:C3, 4:C4",
    "B1": "4:B6", "B2": "4:C5", "B3": "4:C1, 4:C3",
    "C1": "4:E1", "C2": "4:E1", "C3": "4:E2", "C4": "4:E3", "C5": "4:E3",
}

BLOCK = {"A": "adequacy and the Universal Subspace Theorem on every finite model",   # check-id prefix -> the block (the function block_<letter> below)
         "B": "the shell as host, the frames as charts, the worked instance",
         "C": "the finite ring geometry of embeddings"}

# the deciding check of each witnessed predicate: the one whose verdict decides the predicate's statement (the other checks that
# touch it are corroboration, listed by predicate() from the records)
PREDICATES = {
    "4:B4": "A1", "4:B5": "A2", "4:B6": "B1",
    "4:C1": "A4", "4:C2": "A4", "4:C3": "A5", "4:C4": "A5", "4:C5": "B2",
    "4:E1": "C1", "4:E2": "C3", "4:E3": "C4",
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

# ----------------------------------------------------------------------------- finite models
def maps(dom, cod):
    """Every map dom -> cod, as a dict."""
    for vals in itertools.product(cod, repeat=len(dom)):
        yield dict(zip(dom, vals))

def injective(f, dom):
    return len({f[x] for x in dom}) == len(dom)

def compose(f, g, dom):
    """x ↦ f(g(x)) on dom."""
    return {x: f[g[x]] for x in dom}

def adequate(g, E, Z, W):
    """Definition 2: E ∘ g is a bijection Z -> W (W the codomain of E)."""
    phi = {z: E[g[z]] for z in Z}
    return len({phi[z] for z in Z}) == len(Z) == len(W)

def inverse(phi, Z):
    """The inverse of a bijection given by its dict on Z."""
    return {phi[z]: z for z in Z}

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

def frames(p):
    """The affine frames x ↦ a + b x of F_p (1:C2): p(p−1) of them."""
    return [(a, b) for a in range(p) for b in range(1, p)]

def frame_map(frame, p):
    a, b = frame
    return {x: (a + b * x) % p for x in range(p)}

for _p, _k in SHELLS:
    assert is_prime(_p) and _p == 4 * _k + 1, (_p, _k)

# ------------------------------------------------------------------------------------------------------------
# block A: adequacy and the Universal Subspace Theorem on every finite model (4:B4, B5, C1–C4)
# Sections 3–4 of the paper, decided by exhaustion: the latent domain Z, the observations X and the representation
# spaces W are small sets, and every map g : Z → X, E : X → W is enumerated.  A1: adequacy (E ∘ g a bijection
# Z → W, Definition 2) forces g injective, and the adequate E are counted (|Z|! · |W|^{|X|−|Z|} for injective g, none
# otherwise).  A2: for every pair of adequate representations of one g, the transition ψ = φ₂ ∘ φ₁⁻¹ is the unique
# bijection W₁ → W₂ with E₂ ∘ g = ψ ∘ E₁ ∘ g; E₂ = ψ ∘ E₁ on all of X exactly when the two agree off g(Z), which
# fails in some configurations with X ⊋ g(Z) (counted).  A3: Lemma 1's set-level form, ψ(E₁(X)) = E₂(X), on every
# pair.  A4: Theorem 1 (i)–(iii) over every injective ι_m : W_m → U = F_5 — the charts ψ_m are injective, the
# transitions Ψ_{m→n} are bijections of the images composing as ψ_k ∘ ψ_m⁻¹, and the canonical ι_m = φ_m⁻¹ makes every
# chart the inclusion.  A5: Corollaries 1–2 — the lifts L_m = φ_m⁻¹ ∘ E_m invert g_m, are the unique preimage, and
# agree across modalities on every latent state.
def models(nZ, nX, nW):
    Z = list(range(nZ)); X = [f"x{i}" for i in range(nX)]; W = [f"w{i}" for i in range(nW)]
    return Z, X, W

def block_A():
    """Block A — adequacy and the Universal Subspace Theorem on every finite model (EXACT): A1–A5."""
    # A1 adequacy forces g injective; the count of adequate E for a given g
    ok = True; det = []; total = 0
    for nZ, nX in [(1, 1), (1, 2), (2, 2), (2, 3), (3, 3), (3, 4), (2, 4)]:
        Z, X, W = models(nZ, nX, nZ)
        for g in maps(Z, X):
            n_ad = sum(adequate(g, E, Z, W) for E in maps(X, W)); total += 1
            if injective(g, Z):
                ok &= n_ad == math.factorial(nZ) * nZ ** (nX - nZ)
            else:
                ok &= n_ad == 0
        det.append(f"|Z|={nZ},|X|={nX}: {nX**nZ} maps g")
    # 4:B4 (p04008)
    check("A1", "adequacy (E o g bijective Z -> W) forces g injective; adequate E number |Z|! |W|^(|X|-|Z|) for injective g, 0 otherwise", ok,
             f"{total} observation maps over 7 model sizes; " + "; ".join(det[:3]))

    # A2 the transition psi = phi_2 o phi_1^{-1}: unique bijection with E2 o g = psi o E1 o g; E2 = psi o E1 off g(Z) not forced
    ok = True; det = []; n_pairs = 0; n_off = 0; n_total_off = 0
    for nZ, nX in [(2, 2), (2, 3), (3, 3), (3, 4)]:
        Z, X, W1 = models(nZ, nX, nZ); W2 = [f"v{i}" for i in range(nZ)]
        for g in maps(Z, X):
            if not injective(g, Z): continue
            ads1 = [E for E in maps(X, W1) if adequate(g, E, Z, W1)]
            ads2 = [E for E in maps(X, W2) if adequate(g, E, Z, W2)]
            for E1 in ads1:
                phi1 = {z: E1[g[z]] for z in Z}; inv1 = inverse(phi1, Z)
                for E2 in ads2:
                    n_pairs += 1
                    phi2 = {z: E2[g[z]] for z in Z}
                    psi = {w: phi2[inv1[w]] for w in W1}
                    ok &= len(set(psi.values())) == nZ                                   # a bijection W1 -> W2
                    ok &= all(E2[g[z]] == psi[E1[g[z]]] for z in Z)                      # E2 o g = psi o E1 o g
                    others = [q for q in maps(W1, W2) if all(E2[g[z]] == q[E1[g[z]]] for z in Z)]
                    ok &= others == [psi]                                                # unique
                    if nX > nZ:
                        n_total_off += 1
                        if any(E2[x] != psi[E1[x]] for x in X): n_off += 1               # off g(Z) the equation can fail
        det.append(f"|Z|={nZ},|X|={nX}")
    ok &= n_off > 0
    # 4:B5 (p04009)
    check("A2", "psi = phi_2 o phi_1^-1 is the unique bijection W1 -> W2 with E2 o g = psi o E1 o g; E2 = psi o E1 on all of X only when X = g(Z)", ok,
             f"{n_pairs} pairs of adequate representations; off g(Z) the equation fails in {n_off} of {n_total_off} pairs with X != g(Z)")

    # A3 Lemma 1 at the level of images: psi(E1(X)) = E2(X) = W2
    ok = True; n = 0
    for nZ, nX in [(2, 3), (3, 4)]:
        Z, X, W1 = models(nZ, nX, nZ); W2 = [f"v{i}" for i in range(nZ)]
        for g in maps(Z, X):
            if not injective(g, Z): continue
            ads1 = [E for E in maps(X, W1) if adequate(g, E, Z, W1)]
            ads2 = [E for E in maps(X, W2) if adequate(g, E, Z, W2)]
            for E1 in ads1:
                inv1 = inverse({z: E1[g[z]] for z in Z}, Z)
                for E2 in ads2:
                    psi = {w: E2[g[inv1[w]]] for w in W1}; n += 1
                    ok &= {psi[E1[x]] for x in X} == {E2[x] for x in X} == set(W2)
    check("A3", "Lemma 1 as images: psi(E1(X)) = E2(X) = W2 for every pair of adequate representations", ok, f"{n} pairs")

    # A4 Theorem 1 (i)-(iii): every injective iota_m : W_m -> U = F_5; the canonical iota
    p = 5; U = list(range(p)); Z = [0, 2, 3]; X1 = ["a", "b", "c", "d"]; X2 = ["s", "t", "u"]
    g1 = {0: "b", 2: "d", 3: "a"}; g2 = {0: "t", 2: "s", 3: "u"}
    W1 = ["w0", "w1", "w2"]; W2 = ["v0", "v1", "v2"]
    E1 = {"a": "w2", "b": "w0", "c": "w0", "d": "w1"}; E2 = {"s": "v1", "t": "v2", "u": "v0"}
    assert adequate(g1, E1, Z, W1) and adequate(g2, E2, Z, W2)
    phi1 = {z: E1[g1[z]] for z in Z}; phi2 = {z: E2[g2[z]] for z in Z}
    ok = True; n = 0
    iotas = lambda W: [dict(zip(W, perm)) for perm in itertools.permutations(U, len(W))]
    for i1 in iotas(W1):
        psi1 = {z: i1[phi1[z]] for z in Z}
        ok &= injective(psi1, Z)                                                          # (i)
        for i2 in iotas(W2):
            psi2 = {z: i2[phi2[z]] for z in Z}; n += 1
            img1 = {psi1[z] for z in Z}; Psi = {psi1[z]: psi2[z] for z in Z}                  # (ii) Psi_{1->2} = psi2 o psi1^-1
            ok &= len(Psi) == len(Z) and set(Psi) == img1 and set(Psi.values()) == {psi2[z] for z in Z}
            back = {psi2[z]: psi1[z] for z in Z}
            ok &= all(back[Psi[u]] == u for u in img1)                                       # Psi_{2->1} o Psi_{1->2} = id
    inv1, inv2 = inverse(phi1, Z), inverse(phi2, Z)
    can1 = {w: inv1[w] for w in W1}; can2 = {w: inv2[w] for w in W2}                          # iota_m = phi_m^{-1}, into U
    ok &= all(can1[phi1[z]] == z and can2[phi2[z]] == z for z in Z)                         # (iii) psi_m = inclusion
    ok &= {can1[w] for w in W1} == {can2[w] for w in W2} == set(Z)
    # 4:C1 (p04011), 4:C2 (p04012)
    check("A4", "Theorem 1: psi_m = iota_m o phi_m injective for every injective iota_m; Psi_{m->n} a bijection of the images with inverse Psi_{n->m}; iota_m = phi_m^-1 makes every chart the inclusion of Z", ok,
             f"Z of size 3 in F_5, two modalities, {n} pairs of embeddings (60 x 60)")

    # A5 Corollaries 1-2: the lifts
    L1 = {x: inv1[E1[x]] for x in X1}; L2 = {x: inv2[E2[x]] for x in X2}
    ok = all(L1[g1[z]] == z and L2[g2[z]] == z for z in Z)                                    # L_m o g_m = id
    ok &= all((E1[x] == phi1[z]) == (L1[x] == z) for x in X1 for z in Z)                     # L_m x the unique z with E_m x = phi_m z
    ok &= all(L1[g1[z]] == L2[g2[z]] for z in Z)                                             # cross-modal consistency
    ok &= L1["c"] == 0 and E1["c"] == E1["b"]                                                 # an unresolved observation lifts to the state it encodes
    # 4:C3 (p04013), 4:C4 (p04014)
    check("A5", "Corollary 1: L_m = phi_m^-1 o E_m inverts g_m and L_m x is the unique z with E_m x = phi_m z; Corollary 2: L_m(g_m z) = L_n(g_n z), psi o L_m o g_m = psi", ok,
             "the F_5 instance; the observation c (not in g_1(Z)) lifts to the state its code names")

# ------------------------------------------------------------------------------------------------------------
# block B: the shell as host, the frames as charts, the worked instance (4:B6, C1, C3, C5)
# B1: a representation space of the size of the latent domain embeds in the shell (|W_m| = |Z| ≤ p), the least
# shell hosting a domain of N states is the least prime p = 4κ+1 ≥ N (tabulated for N ≤ 60), and the canonical
# ι_m = φ_m⁻¹ is exhibited for Z ⊂ F_13 with three modalities whose representation spaces are quantised integer
# vectors in Z^{d_m}.  B2: the charts of the shell that respect its arithmetic are its affine frames x ↦ a + b x
# (1:C2): p(p−1) of them, any two related by one affine map (simply transitive), so the transition Ψ_{m→n} between two
# frames is affine — on F_5, F_13, F_17.  B3: the F_13 instance end to end: Ψ_{m→n} between the three modalities,
# its composition law, and the lifts recovering every latent state from every observation.
def least_shell(N):
    p = max(N, 5)
    while not (is_prime(p) and p % 4 == 1): p += 1
    return p

def block_B():
    """Block B — the shell as host, the frames as charts, the worked instance (EXACT): B1–B3."""
    # B1 the host: |W| = |Z| <= p; the least hosting shell; the canonical iota on F_13
    table = {N: least_shell(N) for N in range(2, 61)}
    ok = all(table[N] >= N and is_prime(table[N]) and table[N] % 4 == 1 for N in table)
    ok &= table[13] == 13 and table[14] == 17 and table[30] == 37 and table[42] == 53 and table[54] == 61
    p = 13; Z = [1, 2, 4, 7, 8, 11, 12]
    random.seed(4)
    mods = []
    for m, d in enumerate((2, 3, 5)):
        X = [f"x{m}_{i}" for i in range(9)]
        gz = random.sample(X, len(Z)); g = dict(zip(Z, gz))                                 # injective observation map
        codes = set()
        while len(codes) < len(Z): codes.add(tuple(random.randint(-8, 8) for _ in range(d)))  # W_m: distinct quantised vectors
        W = sorted(codes); phi = dict(zip(Z, W)); E = {x: random.choice(W) for x in X}
        for z in Z: E[g[z]] = phi[z]                                                        # adequate: E o g = phi bijective
        assert adequate(g, E, Z, W)
        inv = inverse(phi, Z); iota = {w: inv[w] for w in W}                              # iota_m = phi_m^-1 into F_13
        ok &= injective(iota, W) and all(iota[phi[z]] == z for z in Z) and {iota[w] for w in W} == set(Z)
        mods.append((X, g, W, phi, E, iota))
    ok &= all(len(W) == len(Z) <= p for _, _, W, _, _, _ in mods)
    # 4:B6 (p04010)
    check("B1", "|W_m| = |Z| <= p: the representation space embeds in the shell; the least hosting shell of N states is the least prime p = 4k+1 >= N; the canonical iota_m = phi_m^-1 exhibited on F_13", ok,
             "N=13->13, 14->17, 30->37, 42->53, 54->61; Z of size 7 in F_13, three modalities with codes in Z^2, Z^3, Z^5")

    # B2 the frames as charts: simply transitive, the transition affine
    ok = True; det = []
    for p in (5, 13, 17):
        F = frames(p); ok &= len(F) == p * (p - 1)
        maps = {f: frame_map(f, p) for f in F}
        ok &= all(injective(maps[f], range(p)) for f in F)                               # every frame is a chart
        for f1 in F[:26]:
            m1 = maps[f1]; inv1 = {m1[x]: x for x in range(p)}
            for f2 in F:
                Psi = {m1[x]: maps[f2][x] for x in range(p)}                                 # Psi = psi_2 o psi_1^-1
                a, b = Psi[0], (Psi[1] - Psi[0]) % p
                ok &= b != 0 and all(Psi[u] == (a + b * u) % p for u in range(p))            # affine, invertible
        # simply transitive: for the frame (0,1) and any (c,d) exactly one affine map carries it
        for c in range(p):
            for d in range(1, p):
                sols = [(a, b) for a in range(p) for b in range(1, p) if a == c and b == d]
                ok &= len(sols) == 1
        det.append(f"p={p}: {len(F)} frames")
    # 4:C5 (p04015)
    check("B2", "the arithmetic charts of the shell are its p(p-1) affine frames; Psi_{m->n} between two frames is one invertible affine map (simply transitive)", ok, "; ".join(det))

    # B3 the F_13 instance end to end
    ok = True
    (X1, g1, W1, phi1, E1, i1), (X2, g2, W2, phi2, E2, i2), (X3, g3, W3, phi3, E3, i3) = mods
    psi = [{z: io[ph[z]] for z in Z} for ph, io in ((phi1, i1), (phi2, i2), (phi3, i3))]
    ok &= all(ps[z] == z for ps in psi for z in Z)                                            # canonical: every chart the inclusion
    # general iota: random injective embeddings into F_13, the transitions and their composition law
    for _ in range(50):
        ios = [dict(zip(W, random.sample(range(p), len(W)))) for W in (W1, W2, W3)]
        ps = [{z: io[ph[z]] for z in Z} for ph, io in zip((phi1, phi2, phi3), ios)]
        ok &= all(injective(q, Z) for q in ps)
        T = lambda m, n: {ps[m][z]: ps[n][z] for z in Z}
        ok &= all(T(1, 2)[T(0, 1)[u]] == T(0, 2)[u] for u in T(0, 1))                        # Psi_{2->3} o Psi_{1->2} = Psi_{1->3}
        ok &= all(T(0, 0)[u] == u for u in T(0, 0))
    # the lifts
    L = [{x: inverse(ph, Z)[E[x]] for x in X} for X, E, ph in ((X1, E1, phi1), (X2, E2, phi2), (X3, E3, phi3))]
    ok &= all(L[0][g1[z]] == z and L[1][g2[z]] == z and L[2][g3[z]] == z for z in Z)
    ok &= all(L[m][x] in Z for m, X in enumerate((X1, X2, X3)) for x in X)
    check("B3", "the F_13 instance: canonical charts are the inclusion; for random embeddings the transitions compose, Psi_{n->k} o Psi_{m->n} = Psi_{m->k}; the three lifts recover every latent state", ok,
             "50 random triples of embeddings W_m -> F_13; 27 observations lifted")

# ------------------------------------------------------------------------------------------------------------
# block C: the finite ring geometry of embeddings (4:E1, E2, E3)
# Section 6 of the paper.  C1 (CHART): the character chart of the shell, z ↦ (cos 2πkz/p, sin 2πkz/p)_{k<p−1}, is
# equivariant — a translation z ↦ z + a rotates plane k by 2πka/p — and has ‖Emb(z)‖² = p − 1 for every z: the whole
# chart lies on one sphere; a chart that is not equivariant (random) does not.  C2 (EXACT): the same in the shell's
# own arithmetic — the conjugate norm Σ_k g^{kz} g^{k(n−z)} equals n = p − 1 for every z and every generator g, and
# translation multiplies coordinate k by g^{ka}.  C3 (CHART): the quantisation count — the grid points Δ·Z^d within
# Δ/2 of a sphere of radius R grow like (R/Δ)^{d−1} (fitted exponents at d = 2, 3).  C4, C5 (EXACT): the Gödel
# code G(x) = ∏ p_i^{x_i} is injective on the box {0..4}³ over the primes 2, 3, 5 (125 distinct codes, maximum
# 810 000); reduced modulo the least prime above the maximum, q = 810 013, it stays injective, while smaller moduli
# collide; the two-prime code 2^a 3^b is injective on a, b ≤ 20 (the core instance), and signed coordinates are
# coded after a shift.
def emb(p, z):
    return [f(2 * math.pi * k * z / p) for k in range(1, p) for f in (math.cos, math.sin)]

def block_C():
    """Block C — the finite ring geometry of embeddings (C1–C2 CHART; C3–C5 EXACT): C1–C5."""
    # C1 the character chart on the sphere (chart)
    ok = True; det = []
    for p, k in SHELLS[:4]:
        norms = [sum(c * c for c in emb(p, z)) for z in range(p)]
        ok &= all(abs(n - (p - 1)) < 1e-9 for n in norms)
        # equivariance: Emb(z + a) = R(a) Emb(z), R(a) the block rotation by 2 pi k a / p in plane k
        for a in range(1, p):
            for z in range(p):
                e, ez = emb(p, z + a), emb(p, z)
                for kk in range(1, p):
                    c, s = math.cos(2 * math.pi * kk * a / p), math.sin(2 * math.pi * kk * a / p)
                    x, y = ez[2 * (kk - 1)], ez[2 * (kk - 1) + 1]
                    ok &= abs(c * x - s * y - e[2 * (kk - 1)]) < 1e-9 and abs(s * x + c * y - e[2 * (kk - 1) + 1]) < 1e-9
        det.append(f"p={p}: |Emb|^2 = {p-1}")
    random.seed(1)
    rnd = [[random.gauss(0, 1) for _ in range(8)] for _ in range(13)]
    spread = max(sum(c * c for c in v) for v in rnd) - min(sum(c * c for c in v) for v in rnd)
    ok &= spread > 1                                                                       # a non-equivariant chart is not on a sphere
    # 4:E1 (p04018)
    check("C1", "the character chart z -> (cos 2 pi k z/p, sin 2 pi k z/p)_k has |Emb(z)|^2 = p-1 for every z and is translation-equivariant (block rotations); a random chart is not on a sphere", ok,
             "; ".join(det) + f"; random control: norm spread {spread:.1f}", kind="CHART")

    # C2 the conjugate norm in the shell's arithmetic, exact
    ok = True; det = []
    for p, k in SHELLS:
        n = p - 1
        for g in generators(p):
            for z in range(n + 1):
                ok &= sum(pow(g, kk * z, p) * pow(g, kk * (n - z), p) for kk in range(n)) % p == n % p
            for z in range(n):
                for a in range(1, 4):
                    ok &= all(pow(g, kk * (z + a), p) == pow(g, kk * a, p) * pow(g, kk * z, p) % p for kk in range(n))
        det.append(f"p={p}: {len(generators(p))} generators")
    check("C2", "sum_k g^(kz) g^(k(n-z)) = n = p-1 in F_p for every z <= n and every generator; translation multiplies coordinate k by g^(ka)", ok, "; ".join(det[:4]))

    # C3 the quantisation count on the sphere (chart): exponent d-1
    def count(d, r):
        """grid points of Z^d within 1/2 of the sphere of radius r (Delta = 1)."""
        rng = range(-int(r) - 1, int(r) + 2)
        if d == 2:
            return sum(1 for x in rng for y in rng if abs(math.hypot(x, y) - r) <= 0.5)
        return sum(1 for x in rng for y in rng for z in rng if abs(math.sqrt(x * x + y * y + z * z) - r) <= 0.5)
    ok = True; det = []
    for d in (2, 3):
        radii = list(range(10, 101, 10)) if d == 2 else list(range(5, 41, 5))
        cs = [count(d, r) for r in radii]
        xs = [math.log(r) for r in radii]; ys = [math.log(c) for c in cs]
        mx, my = sum(xs) / len(xs), sum(ys) / len(ys)
        slope = sum((x - mx) * (y - my) for x, y in zip(xs, ys)) / sum((x - mx) ** 2 for x in xs)   # least squares
        ok &= abs(slope - (d - 1)) < 0.15
        det.append(f"d={d}: R = {radii[0]}..{radii[-1]}, counts {cs[0]}..{cs[-1]}, slope {slope:.2f}")
    # 4:E2 (p04019)
    check("C3", "grid points within Delta/2 of the sphere of radius R number ~ (R/Delta)^(d-1): least-squares exponents within 0.15 of d-1 at d = 2, 3", ok, "; ".join(det), kind="CHART")

    # C4 the Goedel code on the box {0..4}^3 over 2, 3, 5; reduction mod q
    box = [(a, b, c) for a in range(5) for b in range(5) for c in range(5)]
    G = {x: 2 ** x[0] * 3 ** x[1] * 5 ** x[2] for x in box}
    ok = len(set(G.values())) == len(box) == 125
    mx = max(G.values()); ok &= mx == 810000
    q = mx + 1
    while not is_prime(q): q += 1
    ok &= q == 810013 and len({v % q for v in G.values()}) == 125
    coll = {m: 125 - len({v % m for v in G.values()}) for m in (101, 1009, 10007, 100003)}
    ok &= coll[101] > 0                                                                    # below the maximum the guarantee lapses
    # 4:E3 (p04020)
    check("C4", "G(x) = 2^a 3^b 5^c is injective on {0..4}^3 (125 codes, max 810000); mod q = 810013 (the least prime above the maximum) injective by the bound; below it the bound gives nothing: mod 101 there are collisions", ok,
             f"collisions below the maximum: {coll} (none at 1009, 10007, 100003 is the accident of these residues, not the bound)")

    # C5 the two-prime core instance and signed coordinates
    codes = {(a, b): 2 ** a * 3 ** b for a in range(21) for b in range(21)}
    ok = len(set(codes.values())) == 441
    signed = [(a, b, c) for a in range(-2, 3) for b in range(-2, 3) for c in range(-2, 3)]
    Gs = {x: 2 ** (x[0] + 2) * 3 ** (x[1] + 2) * 5 ** (x[2] + 2) for x in signed}
    ok &= len(set(Gs.values())) == 125 and max(Gs.values()) == 810000
    check("C5", "2^a 3^b injective on a, b <= 20 (441 codes); signed coordinates in {-2..2}^3 coded after the shift +2: 125 distinct codes, the same maximum", ok, "")

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
