"""frc.sets — finite sets for the normal forms of 5-reductio: hereditarily finite sets by Ackermann's coding and by ranks,
the Russell class, the iterated singletons, counting measure, small permutation groups and the transfer digraph's walks
(the logic theme; 5-reductio's migration, 21 October 2026).

Moved from the package src/5-reductio/reductio.py, which stays the paper's published witness until its release pins the
framework. Everything is exact: integer bit masks and tuples. The Lean side is lean/FrcCore/Theme/Sets.lean (the antinomy
as a theorem of separation, hereditarily finite sets as trees, counting measure, no doubling, principal ultrafilters),
Theme/Equivariant.lean (the equivariant section criterion) and Theme/Transfer.lean (the periodic walk).

* Ackermann's coding: a set with members a₁, a₂, … is Σ 2^aᵢ, so `x ∈ u` iff bit x of u is set; `members(u)` lists them,
  `russell(u)` is the code of {x ∈ u : x ∉ x}, `singleton(x) = 2^x`, `chain(n)` the n-th iterated singleton of ∅ (5:D2, D9).
* `hf_levels(k)`: V₀ ⊂ … ⊂ V_k as lists of frozensets of indices (the ranks).
* `measure(A, n)`: counting measure of a subset of [0, n) given as a bit mask; `is_bijection`, `image` (5:E8).
* `perm_group(name)`, `compose(p, q)`: ℤ/2, ℤ/3 and S₃ as permutation tuples; `longest_walk(cols, edges)`: the longest walk
  in a finite digraph, |cols| + 1 standing for "walks of every length" (5:E3, E6).
"""
import itertools

def hf_levels(k):
    """V_0 ⊂ V_1 ⊂ … ⊂ V_k as lists; a set of rank ≤ j is a bit mask over the elements of V_{j−1} (in the
    enumeration of level j−1).  Returns the list of levels, each a list of frozensets of indices into the previous."""
    levels = [[]]                                   # V_0 = ∅ has no elements
    for j in range(1, k + 1):
        prev = levels[-1]
        # elements of V_j are subsets of V_{j-1}; represent as frozenset of indices into V_{j-1}
        levels.append([frozenset(c) for r in range(len(prev) + 1) for c in itertools.combinations(range(len(prev)), r)])
    return levels

def members(code):
    return [i for i in range(code.bit_length()) if code >> i & 1]

def russell(u):
    """The code of {x ∈ u : x ∉ x}; on Ackermann codes no x is a member of itself, so it is u itself (checked)."""
    return sum(1 << x for x in members(u) if not (x >> x & 1))

def singleton(x):
    """The code of {x}."""
    return 1 << x

def chain(n):
    """The n-th iterated singleton of the empty set: ∅, {∅}, {{∅}}, …; its rank is n."""
    s = 0
    for _ in range(n): s = singleton(s)
    return s

def rank(code):
    """The rank of a hereditarily finite set: one more than the largest rank of a member, 0 for ∅."""
    return 0 if code == 0 else 1 + max(rank(m) for m in members(code))

def measure(A, n):
    """Counting measure of the subset A ⊆ [0, n) (a bit mask)."""
    return sum(1 for x in range(n) if A >> x & 1)

def image(A, sigma, n):
    """The image of the subset A ⊆ [0, n) under the map sigma (a tuple)."""
    return sum(1 << sigma[x] for x in range(n) if A >> x & 1)

def perm_group(name):
    if name == "Z2": return [(0, 1), (1, 0)]
    if name == "Z3": return [(0, 1, 2), (1, 2, 0), (2, 0, 1)]
    return list(itertools.permutations(range(3)))                      # S_3

def compose(p, q): return tuple(p[q[i]] for i in range(len(p)))

def longest_walk(cols, edges):
    best = 0
    for x in cols:
        frontier = {x}; L = 0
        while frontier and L <= len(cols):
            frontier = {y for f in frontier for y in cols if (f, y) in edges}; L += 1 if frontier else 0
        best = max(best, L)
    return best
