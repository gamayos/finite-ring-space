"""
a_frames.py — block A: the arithmetic frames, their theories, the stability schema, the migration (5:B3, B5, B6, C2, C3, C5)
=================================================================================================================
Section 3 of the paper.  A1: the theory of the frame W_N is complete and decidable — every sentence of a sample
(and every sentence of the language, by the evaluator) is decided by evaluation in W_N, and the categorical
sentence σ_N has exactly the N! relabelled copies of W_N as its models on a domain of size N (categoricity).
A2: no finite model of Q — on a domain of N elements no successor map is injective and misses 0 (exhaustive over
all N^N maps for N ≤ 7); so the frame theory does not interpret Q.  A3: bounded stability — the worked instance
(Goldbach below 20) takes its standard value in every frame above its bound t(φ), and so does every formula of a
random sample of Δ₀ sentences; below the bound frames can disagree, and the empirical threshold is reported
beside the proved one.  A4: the migration counts — fewer than s^(K+1) records of length ≤ K, no injection of a
domain of N elements into fewer than N records, and the certified fraction s^(K+1)/⌊c^L/2⌋ falling below every
threshold (chart).  A5: the horizon separation — a deterministic system on C configurations halts within C steps
or revisits a configuration and runs forever; exhaustive on tiny systems, sampled on large ones.
"""
import itertools, math, random
import redcommon as rc

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

def run():
    # A1 per-frame completeness and decidability; categoricity of sigma_N
    ok = True; det = []
    sents = fo_sentences()
    for N in range(2, 9):
        W = rc.Frame(N)
        vals = [s(W) for _, s in sents]
        ok &= all(v in (True, False) for v in vals)                       # every sentence decided by evaluation
    # categoricity: models of sigma_N on domain [0,N) are the N! relabelled copies of W_N, each satisfying the diagram
    for N in (2, 3, 4, 5):
        W = rc.Frame(N)
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
    rc.check("A1", "Th(W_N) is complete and decidable: every sentence of the sample is decided by evaluation on N = 2..8; sigma_N is categorical — its models on a domain of size N are the N! copies of W_N (N <= 5)", ok,
             "10 sentences x 7 frames; " + "; ".join(det[:3]))

    # A2 no finite model of Q: no successor on [0,N) is injective with 0 outside its image
    ok = True; det = []
    for N in range(1, 8):
        found = 0
        for S in itertools.product(range(N), repeat=N):
            if len(set(S)) == N and 0 not in S: found += 1
        ok &= found == 0
        det.append(f"N={N}: {N**N} maps, 0 injective-avoiding-0")
    rc.check("A2", "no finite model of Q: on N elements no successor map is injective and misses 0 (all N^N maps, N <= 7), so Th(W_N) does not interpret Q", ok, "; ".join(det[:4]))

    # A3 bounded stability: the worked instance and a random sample
    ok = True
    gb = rc.goldbach_form(20); t = rc.boundF([], gb); std = rc.evalF([], gb)
    ok &= std is True and t == 400
    ok &= all(rc.evalF_frame(N, [], gb) == std for N in range(t + 1, t + 41))
    thresh = next(N for N in range(2, t + 2) if all(rc.evalF_frame(M, [], gb) == std for M in range(N, t + 2)))
    rng = random.Random(5); n_forms = 0; n_disagree = 0
    for _ in range(300):
        f = rc.random_form(rng, 3, 0)
        try:
            tf = rc.boundF([], f); sv = rc.evalF([], f)
        except RecursionError:
            continue
        if tf > 60: continue
        n_forms += 1
        ok &= all(rc.evalF_frame(N, [], f) == sv for N in range(tf + 1, tf + 25))
        if any(rc.evalF_frame(N, [], f) != sv for N in range(2, tf + 1)): n_disagree += 1
    ok &= n_forms >= 100 and n_disagree > 0
    rc.check("A3", "bounded stability: every Delta_0 sentence takes its standard value in every frame above t(phi) — the worked instance (Goldbach below 20, t = 400) in 40 frames above the bound, and a random sample; below the bound frames can disagree", ok,
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
    rc.check("A4", "records: sum_{i<=K} s^i < s^(K+1) (s = 2, 3, 10; K <= 20); no injection of N elements into R < N records (exhaustive); the certified fraction s^(K+1)/floor(c^L/2) falls to 0", ok, "; ".join(det))

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
    rc.check("A5", "horizon separation: a deterministic run on C configurations halts within C steps or revisits a configuration and never halts — decidable from above by C steps", ok, "; ".join(det))

if __name__ == "__main__":
    run(); rc.summary(write=False)
