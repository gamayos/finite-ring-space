"""
d_determinacy.py — block D: determinacy on the finite totality (5:D8, B7)
========================================================================
Section 4.4 and Section 3.2 of the paper.  D1 (Proposition finiteness, the finite direction): on the frame W₃ the
full second-order theory is decided by exhaustive evaluation — every second-order sentence of a sample (quantifiers
over all 8 subsets, all 512 binary relations, all 27 functions) receives a definite value, among them the
well-ordering of the domain and the Dedekind-finiteness statement (no injective non-surjective function), and the
count of subsets, relations and functions is exactly 2ⁿ, 2^{n²}, nⁿ.  D2 (the Ω-hard row): a Π⁰₁ sentence receives a
verdict from each frame about its own domain — the bounded Goldbach statement is true in every frame W_N, N ≤ 400 —
and no frame states the closure over all frames; the frame values are reported, the closure is not a frame sentence.
"""
import itertools
import redcommon as rc

def run():
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
    rc.check("D1", "the full second-order theory of W_3 is decided by exhaustive evaluation: 8 subsets, 512 relations, 27 functions; the well-ordering sentence and Dedekind-finiteness are true, the existence of a linear order true, a false sentence false", ok,
             "second-order quantifiers as finite conjunctions/disjunctions")

    # D2 the Pi_1 sentence frame by frame: bounded Goldbach true in every frame N <= 400; the closure is no frame sentence
    ok = True; vals = []
    for N in range(4, 401):
        v = all(any(rc.is_prime(x) and rc.is_prime(m - x) for x in range(2, m)) for m in range(4, N, 2))   # every even m < N is a sum of two primes below N
        vals.append(v); ok &= v
    rc.check("D2", "the Pi_1 sentence 'every even number is a sum of two primes' receives a verdict from each frame about its own domain: true in W_N for every 4 <= N <= 400; the closure over all frames is not a sentence of any frame", ok,
             f"{len(vals)} frames, all true; no frame decides the unbounded quantifier")

if __name__ == "__main__":
    run(); rc.summary(write=False)
