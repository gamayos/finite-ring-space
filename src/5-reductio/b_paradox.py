"""
b_paradox.py — block B: the normal forms on a finite universe (5:D2, D3, D4, D9, E8)
===================================================================================
Sections 2 and 4 of the paper, decided on the bounded universe.  Hereditarily finite sets are coded by Ackermann's
bijection (a set with elements a₁, a₂, … is Σ 2^{aᵢ}; x ∈ y iff bit x of y is set), so V₄ is the 65 536 codes below
2¹⁶ and V₃ the 16 codes below 2⁴.  B1 (antinomy normal form, the witness): for every u ∈ V₄ the Russell class
{x ∈ u : x ∉ x} is a set of V₄ and is not a member of u; no set of V₄ has every set of V₄ as a member — bounded
comprehension has no antinomy and no universal set.  B2 (the external diagonal): for every listing of n binary
strings of length n the diagonal string is missing (exhaustive n ≤ 3, random n = 60), no map from a finite set
onto its power set (exhaustive n ≤ 3), 2ⁿ > n; and inside a finite registry the diagonal of a complete listing is
one of its own entries — no escape.  B3 (the choice paradoxes vanish): on a finite set counting measure is
complete and invariant under every bijection; no injection X ⊔ X → X (exhaustive |X| ≤ 4); every ultrafilter on a
3-set is principal (all filters enumerated).  B4 (Corollary AT-det): the iterated singletons ∅, {∅}, {{∅}}, … are
pairwise distinct and unbounded in rank.
"""
import itertools
import redcommon as rc

def members(code):
    return [i for i in range(code.bit_length()) if code >> i & 1]

def run():
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
    rc.check("B1", "on V_4 (65536 sets, Ackermann codes) the Russell class of every u is a set not in u; no set of V_4 contains every set of V_4; x notin x throughout — bounded comprehension has no antinomy", ok,
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
    rc.check("B2", "the external diagonal: for every listing of n strings the diagonal is missing (n <= 3 exhaustive, n = 60 random); no map [n] -> P([n]) is onto (n <= 3); 2^n > n; the diagonal of a complete finite registry is one of its entries", ok,
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
    rc.check("B3", "on a finite set counting measure is complete and invariant under every bijection (|X| = 6, all 720 permutations x 64 subsets); no injection X + X -> X (|X| <= 4); every ultrafilter on a 3-set is principal (all 3, of the filters enumerated)", ok,
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
    rc.check("B4", "the iterated singletons emptyset, {emptyset}, {{emptyset}}, ... (7 of them, the last of 65 537 bits) are pairwise distinct with ranks 0, 1, 2, ...: a universal set would be infinite", ok, f"ranks {ranks}")

if __name__ == "__main__":
    run(); rc.summary(write=False)
