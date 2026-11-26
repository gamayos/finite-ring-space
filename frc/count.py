"""frc.count — the count readout of a shell (the count theme; 20-rh's revision of 21 November 2026).

The python side of `lean/FrcCore/Theme/Count.lean`, `lean/FrcCore/Theme/Circle.lean`, `lean/FrcCore/Theme/Steps.lean`, `Theme/Thue.lean`, `Theme/WindowModes.lean`, `Theme/Pairing.lean` and `Theme/Primes.lean`. The modes of a shell p are the powers x ↦ x^k on the nonzero
residues, k = 0, …, p − 2. The count of a mode is k. For a count k ≥ 1 the zero is ρ_k = k + 1 and the conjugate count is
p − 1 − k. The pairing is ⟨v, w⟩ = Σ_{x≠0} v(x) w(x), the count operator N acts on the mode coefficients by c_k ↦ k c_k,
and on a frame (p = 4κ + 1, g a drive, i = −g^κ) the frequency of the count k is γ_k = −i(k + 2⁻¹), 2⁻¹ = 2κ + 1.
Exact integers mod p only, the standard library only (gate G09).

One function per Lean declaration, under its name. Each returns True when the statement holds on the shell it is given,
over the range it is given (the whole shell where no range is named). The statements that take no generator (p alone,
or p with κ) run on a Carrier's chart as on a Subject.

    generators(p)                       the generators of the cycle of the shell p
    gram_table(p)                       P[n] = Σ_{x≠0} x^n for n ≤ 2p − 4; ⟨x^k, x^m⟩ = P[k + m]
    gram(p, k, m), gram_rows(p, P, ks)  ⟨x^k, x^m⟩ by the direct sum; the table against the direct sums on the rows ks
    quarter_turn(p, κ, g)               i = −g^κ
    frequency(p, κ, i, k)               γ_k = −i(k + 2κ + 1)
    mode_coefficients(p, v)             c_k = −Σ_x v(x) x^{−k}, k = 0 … p − 2 (v indexed by x − 1)
    mode_values(p, c)                   the vector Σ_k c_k x^k at x = 1 … p − 1
    delta(p, y), fixed_sequence(p, s)   test vectors: the indicator of y; a fixed integer sequence, no random source
    run_shifts(p, start)                the values 2c that the nonconstant conjugate pairs of a run of counts ask for

    mode_stride, count_conjugate, count_adjoint, count_adjoint_vector, half_forced, count_run, count_run_only,
    zero_count, zeros_fill (zeros_fill_ends on a large shell), zero_conjugate, generator_skew, centre_mode, pair_invariant,
    energy_order, cardinal_modes, cardinal_zeros, carrier_centre, origin_unit_symmetry, zero_shared, half_unique,
    zeros_collide, zeros_not_held (20:F7; a reading of the residues into states may be passed)

The pairing of a vector with the conjugate of another, [v, w] = Σ_{x≠0} v(x)·w(x⁻¹) (20:G15, 23 November 2026).

    pairing_entry(p, P, k, m)           [x^k, x^m] from the Gram table

    modes_orthogonal, generator_selfadjoint, generator_selfadjoint_vector                                 (20:G15)

The critical circle (Theme/Circle.lean, 22 November 2026). A point of the orbital sphere is a position a with a phase m
and carries a·g^m; its mirror carries a·g^{−m}; the circle is the set of the points with a·(g^m + g^{−m}) ≡ 1.

The paper writes z for the residue t = ρ/(1 − ρ) of these functions and d for the sum c.

    circle_points(p, g)                 the pairs (a, m) of the circle; (−a, m + 2κ) is the same point of the sphere
    circle_places(p, κ, g)              the zero g^j/(1 + g^j) at each place j ≠ 2κ of the latitude cycle

    circle_pair, circle_frequency, circle_meridians, circle_point, circle_count, circle_counts,
    circle_phase, circle_parallels                                                                        (20:G13)
    circle_place, circle_place_cycle, circle_place_even, circle_quarter_turn,
    circle_place_phase, circle_quarter_closes                                                             (20:G14)

The value of a mode at one label (Theme/Steps.lean, 23 November 2026). A nonzero residue y is x^k·g^r with r < W when y is
fewer than W steps of the drive after a power of x on the latitude cycle.

    scale_table(p, g)                   the scale of every nonzero residue on the latitude cycle
    step_width(p, g, x)                 the least W for the residue x, by marking its powers and one pass along the cycle
    label_pair(p, l)                    (N, W) for a label: the largest N with l^N < p, the least W with N·W ≥ p − 1

    power_steps, label_steps                                                                              (20:D19)

The window (Theme/Thue.lean, Theme/WindowModes.lean, Theme/Primes.lean, Theme/Pairing.lean; 26 November 2026). The window of a
shell is its labels 1, …, q, with q the largest label with q² < p. A product of primes is a choice of exponents.

    window(p)                           (q, the primes up to q)
    prime_values(p)                     the values of every mode at the primes of the window
    square_pairs(p)                     the labels a ≤ b of the window with a² + b² = p
    reflected_table(p, pairs)           R(k, m) = Σ_{x≠0,1} x^k(1 − x)^m
    products_below(bound, S)            the products of members of S below the bound, one for each choice of exponents

    run_eigenvalue                                                                                        (20:G3)
    thue_ne_zero, mode_fixed, mode_sign, mode_signed_power                                                (20:G17)
    prime_products_distinct, relation_wrapped, primes_unique_generators, mode_iff_relations,
    mode_relations_two_primes                                                                             (20:G18)
    two_squares, two_squares_unique                                                                       (20:G19)
    reflected_value, reflected_zero, reflected_ne_zero, reflected_conjugate, reflected_exclusive          (20:G20)
"""
import math

from frc import arith


def generators(p):
    """The generators of the cycle of the shell p, ascending."""
    qs = arith.prime_factors(p - 1)
    return [g for g in range(2, p) if all(pow(g, (p - 1) // q, p) != 1 for q in qs)]


def gram_table(p):
    """P[n] = Σ_{x≠0} x^n for n = 0 … 2p − 4, by running powers; the Gram entry of two modes is P[k + m]."""
    xs, cur, P = list(range(1, p)), [1] * (p - 1), []
    for _ in range(2 * p - 3):
        P.append(sum(cur) % p)
        cur = [c * x % p for c, x in zip(cur, xs)]
    return P


def gram(p, k, m):
    """The Gram entry ⟨x^k, x^m⟩ = Σ_{x≠0} x^k x^m, by the direct sum."""
    return sum(pow(x, k, p) * pow(x, m, p) for x in range(1, p)) % p


def frequency(p, kap, i, k):
    """The frequency of the count k: γ_k = −i(k + 2⁻¹), with 2⁻¹ = 2κ + 1."""
    return (-i * (k + 2 * kap + 1)) % p


def quarter_turn(p, kap, g):
    """The Subject's quarter-turn i = g^(−κ) = −g^κ."""
    return (-pow(g, kap, p)) % p


def mode_coefficients(p, v):
    """c_k = −Σ_x v(x) x^{−k} for k = 0 … p − 2; v is indexed by x − 1."""
    inv, cur, cs = [pow(x, p - 2, p) for x in range(1, p)], [1] * (p - 1), []
    for _ in range(p - 1):
        cs.append((-sum(a * b for a, b in zip(v, cur))) % p)
        cur = [c * ix % p for c, ix in zip(cur, inv)]
    return cs


def mode_values(p, cs):
    """The vector with the mode coefficients cs, at x = 1 … p − 1 (Horner)."""
    out = []
    for x in range(1, p):
        acc = 0
        for c in reversed(cs): acc = (acc * x + c) % p
        out.append(acc)
    return out


def delta(p, y):
    """The indicator of the residue y, indexed by x − 1."""
    return [1 if x == y else 0 for x in range(1, p)]


def fixed_sequence(p, seed):
    """A fixed integer sequence reduced mod p (s ↦ 1103515245 s + 12345 mod 2³¹): a test vector with no random source."""
    out, s = [], seed
    for _ in range(p - 1):
        s = (1103515245 * s + 12345) % (1 << 31)
        out.append(s % p)
    return out


def run_shifts(p, start):
    """The values 2c that the nonconstant conjugate pairs of the run of counts [start, start + p − 1) ask for."""
    n = p - 1
    by_class = {a % n: a for a in range(start, start + n)}
    return {(-(a + by_class[(n - cls) % n])) % p for cls, a in by_class.items() if cls}


# ---- one function per declaration of lean/FrcCore/Theme/Count.lean -----------------------------------------------------

def mode_stride(p, g):
    """At x = g^m the mode of count k has the value g^(km): (g^m)^k = (g^k)^m = g^(km), every m and k below p − 1."""
    n = p - 1; tab = [pow(g, m, p) for m in range(n)]
    return all(pow(tab[m], k, p) == pow(tab[k], m, p) == pow(g, k * m, p) for m in range(n) for k in range(n))


def count_conjugate(p):
    """The conjugate of a count 1 ≤ k ≤ p − 2 is p − 1 − k, again in 1 … p − 2, and the two counts add to −1."""
    return all(1 <= p - 1 - k <= p - 2 and (k + (p - 1 - k) + 1) % p == 0 for k in range(1, p - 1))


def count_adjoint(p, P, direct=False):
    """(k + m + 1)·⟨x^k, x^m⟩ ≡ 0 for 1 ≤ k ≤ p − 2, 0 ≤ m ≤ p − 2; the Gram entries from the table P, or by direct sums."""
    return all((k + m + 1) * (gram(p, k, m) if direct else P[k + m]) % p == 0 for k in range(1, p - 1) for m in range(p - 1))


def gram_rows(p, P, ks):
    """The table P against the direct Gram sums on the rows ks."""
    return all(gram(p, k, m) == P[k + m] for k in ks for m in range(p - 1))


def count_adjoint_vector(p, pairs):
    """⟨Nv, w⟩ + ⟨v, Nw⟩ + ⟨v, w⟩ ≡ −c_0·d_0 on pairs of vectors given by their values; N acts on the mode coefficients.
    pairs: [((name, v), (name, w))]; each vector is first read back from its mode coefficients."""
    cache = {}

    def prep(key, v):
        if key not in cache:
            c = mode_coefficients(p, v)
            if mode_values(p, c) != v: return None
            cache[key] = (v, c, mode_values(p, [k * ck % p for k, ck in enumerate(c)]))
        return cache[key]

    for (ka, va), (kb, vb) in pairs:
        A, B = prep(ka, va), prep(kb, vb)
        if A is None or B is None: return False
        (v, c, Nv), (w, d, Nw) = A, B
        lhs = (sum(a * b for a, b in zip(Nv, w)) + sum(a * b for a, b in zip(v, Nw)) + sum(a * b for a, b in zip(v, w))) % p
        if lhs != (-c[0] * d[0]) % p: return False
    return True


def half_forced(p, ks=None):
    """For every residue c: ((k + c) + (p − 1 − k + c) ≡ 0 for every count k) ⇔ 2c ≡ 1. ks: the counts tried (default all)."""
    ks = range(1, p - 1) if ks is None else ks
    return all(all(((k + c) + (p - 1 - k + c)) % p == 0 for k in ks) == (2 * c % p == 1) for c in range(p))


def count_run(p, ms, ks=None):
    """On the run of counts that starts at m(p − 1): its counts at k and at p − 1 − k add to −(2m + 1), for 0 ≤ k < p."""
    ks = range(0, p) if ks is None else ks
    return all(((m * (p - 1) + k) + (m * (p - 1) + (p - 1 - k)) + (2 * m + 1)) % p == 0 for m in ms for k in ks)


def count_run_only(p, ms):
    """A run of p − 1 consecutive counts has one skew shift exactly when it starts at m(p − 1) or at m(p − 1) + 1."""
    for m in ms:
        for r in range(0, p - 1):
            need = run_shifts(p, m * (p - 1) + r)
            if (need != {(2 * m + 1) % p}) if r in (0, 1) else (len(need) < 2): return False
    return True


def zero_count(p, kap, g):
    """i² = −1 and 2⁻¹ + iγ_k = k + 1 for 0 ≤ k < 2p; for a count k ≥ 1 this residue is the zero of the mode."""
    i = quarter_turn(p, kap, g); half = 2 * kap + 1
    return i * i % p == p - 1 and all((half + i * frequency(p, kap, i, k)) % p == (k + 1) % p for k in range(0, 2 * p))


def zeros_fill(p):
    """The zeros k + 1 of the counts 1 ≤ k ≤ p − 2 are the residues other than 0 and 1."""
    return {(k + 1) % p for k in range(1, p - 1)} == set(range(p)) - {0, 1}


def zeros_fill_ends(p):
    """The same statement on a large shell, by the number of counts and the two ends of the range."""
    ks = range(1, p - 1)
    return len(ks) == p - 2 and (ks[0] + 1) % p == 2 and (ks[-1] + 1) % p == p - 1


def zero_conjugate(p, kap, g):
    """For every k ≤ p − 1, (p − 1 − k) + 1 ≡ 1 − (k + 1) and γ_(p−1−k) = −γ_k as residues; for 1 ≤ k ≤ p − 2 these are the zero and the frequency of the conjugate mode."""
    i = quarter_turn(p, kap, g)
    return all((p - 1 - k + 1) % p == (1 - (k + 1)) % p and frequency(p, kap, i, p - 1 - k) == (-frequency(p, kap, i, k)) % p
               for k in range(0, p))


def generator_skew(p, kap, g, P):
    """(γ_k + γ_m)·⟨x^k, x^m⟩ ≡ 0 unless both modes are constant."""
    i = quarter_turn(p, kap, g); fr = [frequency(p, kap, i, k) for k in range(p - 1)]
    return all((fr[k] + fr[m]) * P[k + m] % p == 0 for k in range(p - 1) for m in range(p - 1) if k > 0 or m > 0)


def pairing_entry(p, P, k, m):
    """[x^k, x^m] = Σ_{x≠0} x^k·x^(−m), the pairing [v, w] = Σ_{x≠0} v(x)·w(x⁻¹) on two modes: the entry P[k + m'] of the Gram table, with m' the count of the conjugate of the mode m."""
    return P[k + (-m) % (p - 1)]


def modes_orthogonal(p, P):
    """The modes are orthogonal for the pairing [v, w]: [x^k, x^m] ≡ −1 for k = m and 0 otherwise; four rows of the table against the direct sums."""
    n = p - 1; ms = range(n) if p < 1000 else (0, 1, 2, n // 2, n - 2, n - 1)
    direct = all(sum(pow(x, k, p) * pow(x, (n - m) % n, p) for x in range(1, p)) % p == pairing_entry(p, P, k, m) for k in (0, 1, n // 2, n - 1) for m in ms)
    return direct and all(pairing_entry(p, P, k, m) == (p - 1 if k == m else 0) for k in range(n) for m in range(n))


def generator_selfadjoint(p, kap, g, P):
    """γ_k·[x^k, x^m] ≡ γ_m·[x^k, x^m] for every two modes."""
    i = quarter_turn(p, kap, g); fr = [frequency(p, kap, i, k) for k in range(p - 1)]; n = p - 1
    return all((fr[k] - fr[m]) * pairing_entry(p, P, k, m) % p == 0 for k in range(n) for m in range(n))


def generator_selfadjoint_vector(p, kap, g, pairs):
    """[Hv, w] ≡ [v, Hw] on pairs of vectors given by their values; H acts on the mode coefficients, and w(x⁻¹) is taken from the values of w.
    pairs: [((name, v), (name, w))]; each vector is first read back from its mode coefficients."""
    i = quarter_turn(p, kap, g); fr = [frequency(p, kap, i, k) for k in range(p - 1)]
    inv = [pow(x, p - 2, p) - 1 for x in range(1, p)]                                    # the index of x⁻¹
    cache = {}

    def prep(key, v):
        if key not in cache:
            c = mode_coefficients(p, v)
            if mode_values(p, c) != v: return None
            cache[key] = (v, mode_values(p, [f * ck % p for f, ck in zip(fr, c)]))
        return cache[key]

    def pairing(a, b):
        return sum(a[x] * b[inv[x]] for x in range(p - 1)) % p

    for (ka, va), (kb, vb) in pairs:
        A, B = prep(ka, va), prep(kb, vb)
        if A is None or B is None: return False
        (v, Hv), (w, Hw) = A, B
        if pairing(Hv, w) != pairing(v, Hw): return False
    return True


def run_eigenvalue(p, ms, ks=None, cs=None):
    """In the run of counts from m(p − 1) the class k is listed as m(p − 1) + k, and N + (c + m) has the eigenvalue k + c at it, for every residue c tried."""
    ks = range(1, p - 1) if ks is None else ks
    cs = (0, 1, (p + 1) // 2, p - 1) if cs is None else cs
    return all(((m * (p - 1) + k) + (c + m)) % p == (k + c) % p for m in ms for k in ks for c in cs)


def window(p):
    """The window of the shell: the largest label q with q² < p, and the primes up to q."""
    q = math.isqrt(p - 1)
    return q, [n for n in range(2, q + 1) if all(n % d for d in range(2, math.isqrt(n) + 1))]


def thue_ne_zero(p):
    """Thue's lemma: every nonzero residue is ±a·b⁻¹ for two labels a, b of the window."""
    q, _ = window(p); seen = set()
    for b in range(1, q + 1):
        bi = pow(b, -1, p)
        for a in range(1, q + 1):
            r = a * bi % p; seen.add(r); seen.add(p - r)
    return len(seen) == p - 1


def prime_values(p):
    """The values of the modes at the primes of the window: row k holds ℓ^k for the primes ℓ ≤ q, for the counts k < p − 1."""
    _, primes = window(p)
    return [tuple(pow(l, k, p) for l in primes) for k in range(p - 1)]


def mode_fixed(p, T=None):
    """The values at the primes of the window fix a mode: no two counts below p − 1 have the same values."""
    T = prime_values(p) if T is None else T
    return len(set(T)) == p - 1


def mode_sign(p, kap, T=None):
    """The values at the primes of the window are all ±1 exactly for the counts 0 and π = 2κ."""
    T = prime_values(p) if T is None else T
    return [k for k in range(p - 1) if all(v in (1, p - 1) for v in T[k])] == [0, 2 * kap]


def mode_signed_power(p, kap, js=None, T=None):
    """The values at the primes of the window are all ±ℓ^j exactly for the counts j and π + j, for every count j tried (default all)."""
    T = prime_values(p) if T is None else T
    for j in (range(p - 1) if js is None else js):
        hit = {k for k in range(p - 1) if all(v == w or v == p - w for v, w in zip(T[k], T[j]))}
        if hit != {j, (j + 2 * kap) % (p - 1)}: return False
    return True


def square_pairs(p):
    """The pairs of labels a ≤ b of the window with a² + b² = p."""
    q, _ = window(p)
    return [(a, b) for a in range(1, q + 1) for b in (math.isqrt(p - a * a),) if a <= b <= q and a * a + b * b == p]


def two_squares(p):
    """p = a² + b² for two labels of the window, and the square roots of −1 on the shell are ±a·b⁻¹."""
    S = square_pairs(p)
    if not S: return False
    a, b = S[0]; r = a * pow(b, -1, p) % p
    return r * r % p == p - 1 and [x for x in range(1, p) if x * x % p == p - 1] == sorted((r, p - r))


def two_squares_unique(p):
    """The two squares are unique up to their order."""
    return len(square_pairs(p)) == 1


def binomial_mod(m, d, p):
    """C(m, d) mod p for m < p."""
    if d < 0 or d > m: return 0
    d = min(d, m - d); num = den = 1
    for i in range(1, d + 1): num = num * (m - d + i) % p; den = den * i % p
    return num * pow(den, -1, p) % p


def reflected_table(p, pairs=None):
    """The reflected pairing R(k, m) = Σ_{x≠0,1} x^k (1 − x)^m on F_p: (k, m) -> R(k, m), for every two nonconstant modes, or for the pairs given, each with (k, p − 1 − k) and (p − 1 − k, p − 1 − m)."""
    if pairs is None:
        xs = range(2, p)
        A = [[pow(x, k, p) for x in xs] for k in range(1, p - 1)]
        B = [[pow(1 - x, m, p) for x in xs] for m in range(1, p - 1)]
        return {(k + 1, m + 1): sum(a * b for a, b in zip(ra, rb)) % p for k, ra in enumerate(A) for m, rb in enumerate(B)}
    want = set()
    for k, m in pairs: want |= {(k, m), (k, p - 1 - k), (p - 1 - k, p - 1 - m)}
    return {(k, m): sum(pow(x, k, p) * pow(1 - x, m, p) for x in range(2, p)) % p for k, m in sorted(want)}


def reflected_value(p, T):
    """R(k, m) = −(−1)^k·C(m, p − 1 − k) for two nonconstant modes."""
    return all(r == (-1 if k % 2 == 0 else 1) * binomial_mod(m, p - 1 - k, p) % p for (k, m), r in T.items())


def reflected_zero(p, T):
    """R(k, m) = 0 when k + m < p − 1."""
    return all(r == 0 for (k, m), r in T.items() if k + m < p - 1)


def reflected_ne_zero(p, T):
    """R(k, m) ≠ 0 when k + m ≥ p − 1."""
    return all(r != 0 for (k, m), r in T.items() if k + m >= p - 1)


def reflected_conjugate(p, T):
    """A mode and its conjugate have the reflected pairing −(−1)^k."""
    return all(T[(k, p - 1 - k)] == (-1 if k % 2 == 0 else 1) % p for (k, m) in T if (k, p - 1 - k) in T)


def reflected_exclusive(p, T):
    """For k + m ≠ p − 1 exactly one of R(k, m) and R(p − 1 − k, p − 1 − m) is 0: the first when k + m < p − 1."""
    return all((r == 0) == (k + m < p - 1) and (T[(p - 1 - k, p - 1 - m)] == 0) == (k + m > p - 1)
               for (k, m), r in T.items() if k + m != p - 1 and (p - 1 - k, p - 1 - m) in T)


def products_below(bound, S):
    """The products below the bound of members of S (each ≥ 2), one for each choice of exponents."""
    S = sorted(S); out = [1]; stack = [(1, 0)]
    while stack:
        n, i = stack.pop()
        for j in range(i, len(S)):
            m = n * S[j]
            if m >= bound: break
            out.append(m); stack.append((m, j))
    return out


def prime_products_distinct(p, S=None):
    """Products below p of primes of the window (or of the members of S) with different exponents are different residues."""
    out = products_below(p, window(p)[1] if S is None else S)
    return len(set(out)) == len(out)


def relation_wrapped(p, factor=4):
    """Every relation between primes of the window has wrapped: among their products below factor·p, two with one residue are never both below p; and two with one residue exist."""
    seen = {}; found = False
    for n in products_below(factor * p, window(p)[1]):
        r = n % p
        if r in seen:
            found = True
            if max(n, seen[r]) < p: return False
            seen[r] = min(n, seen[r])
        else: seen[r] = n
    return found


def generates(q, S):
    """Every label 1 ≤ n ≤ q is a product of members of S."""
    got = {1}
    for n in range(2, q + 1):
        if any(n % s == 0 and n // s in got for s in S): got.add(n)
    return len(got) == q


def generating_free_sets(p):
    """Exhaustive over the sets of labels 2 ≤ s ≤ q: those that generate the labels of the window and whose products below p with different exponents are different."""
    q, _ = window(p); labels = list(range(2, q + 1)); out = []
    for mask in range(1 << len(labels)):
        S = [s for i, s in enumerate(labels) if mask >> i & 1]
        if generates(q, S) and prime_products_distinct(p, S): out.append(S)
    return out


def primes_unique_generators(p, exhaustive=False):
    """The primes of the window are the one generating set of labels with distinct products. The primes generate and have distinct products; a set without a prime ℓ does not generate, since no smaller label divides ℓ; a set with the primes and a composite label c has two products c. exhaustive: every set of labels is tried as well."""
    q, primes = window(p)
    if not (generates(q, primes) and prime_products_distinct(p)): return False
    if any(l % s == 0 for l in primes for s in range(2, l)): return False
    for c in range(2, q + 1):
        if c not in primes:
            n, fac = c, []
            for l in primes:
                while n % l == 0: n //= l; fac.append(l)
            if n != 1 or len(fac) < 2 or prime_products_distinct(c + 1, [c] + primes): return False
    return not exhaustive or generating_free_sets(p) == [primes]


def tuples(vals, r):
    """Every r-tuple over vals."""
    out = [()]
    for _ in range(r): out = [t + (v,) for t in out for v in vals]
    return out


def mode_iff_relations(p):
    """Exhaustive: residues X at the primes of the window satisfy every relation ∏ℓ^e = 1, 0 ≤ e < p − 1, exactly when they are the values of a mode."""
    _, primes = window(p); r = len(primes)
    rel = [e for e in tuples(range(p - 1), r) if math.prod(pow(l, a, p) for l, a in zip(primes, e)) % p == 1]
    modes = set(prime_values(p))
    return all(all(math.prod(pow(x, a, p) for x, a in zip(X, e)) % p == 1 for e in rel) == (X in modes) for X in tuples(range(1, p), r))


def mode_relations_two_primes(p, g, ks=None):
    """On the relations ℓ_i^{d_j} = ℓ_j^{d_i} between two primes of the window, with d the logarithms to the base g: the logarithms and p − 1 have no common factor, the values of every mode tried satisfy the relations, and the values with one of them multiplied by g do not."""
    _, primes = window(p); log = {}; x = 1
    for t in range(p - 1): log[x] = t; x = x * g % p
    d = [log[l] for l in primes]; c = p - 1
    for t in d: c = math.gcd(c, t)
    if c != 1: return False
    ok = lambda X: all(pow(X[i], d[j], p) == pow(X[j], d[i], p) for i in range(len(d)) for j in range(i + 1, len(d)))
    for k in (range(p - 1) if ks is None else ks):
        X = [pow(l, k, p) for l in primes]
        if not ok(X) or any(ok(X[:i] + [X[i] * g % p] + X[i + 1:]) for i in range(len(X))): return False
    return True


def centre_mode(p, kap, g):
    """The mode of count π = 2κ is its own conjugate, its zero is 2⁻¹, its frequency is 0, and it is the one such mode."""
    i = quarter_turn(p, kap, g)
    return (2 * kap + 2 * kap == p - 1 and 2 * (2 * kap + 1) % p == 1 and frequency(p, kap, i, 2 * kap) == 0
            and [k for k in range(p - 1) if frequency(p, kap, i, k) == 0] == [2 * kap])


def pair_invariant(p, kap, g):
    """ρ(1 − ρ) = 2⁻² + γ² = −k(k + 1), the same for a count and its conjugate."""
    i = quarter_turn(p, kap, g); half = 2 * kap + 1
    for k in range(0, p):
        inv = (-k * (k + 1)) % p; kd = p - 1 - k
        if (k + 1) * (1 - (k + 1)) % p != inv or (half * half + frequency(p, kap, i, k) ** 2) % p != inv: return False
        if kd * (kd + 1) % p != k * (k + 1) % p: return False
    return True


def energy_order(p, kap):
    """The counts 2κ − j and 2κ + j are conjugate, their zeros are 2⁻¹ − j and 2⁻¹ + j, and the lesser count of the pair,
    2κ − j, falls from 2κ to 1 as j runs from 0 to 2κ − 1."""
    half = 2 * kap + 1
    for j in range(0, 2 * kap + 1):
        lo, hi = 2 * kap - j, 2 * kap + j
        if lo + hi != p - 1 or (hi + 1) % p != (half + j) % p or (lo + 1 + j) % p != half % p or min(lo, hi) != lo: return False
    return [min(2 * kap - j, 2 * kap + j) for j in range(0, 2 * kap)] == list(range(2 * kap, 0, -1))


def cardinal_modes(p, kap, g):
    """A mode has all its values in {1, −1, i, −i} exactly when its count is 0, κ, 2κ or 3κ."""
    i = quarter_turn(p, kap, g); four = {1, p - 1, i, (-i) % p}; card = {0, kap, 2 * kap, 3 * kap}
    return all(all(pow(x, k, p) in four for x in range(1, p)) == (k in card) for k in range(p - 1))


def cardinal_zeros(p, kap):
    """The zeros of the counts 0, κ, 2κ, 3κ are 1, 3·4⁻¹, 2⁻¹, 4⁻¹: 4(κ + 1) ≡ 3, 2(2κ + 1) ≡ 1, 4(3κ + 1) ≡ 1."""
    return p == 4 * kap + 1 and 4 * (kap + 1) % p == 3 % p and 2 * (2 * kap + 1) % p == 1 and 4 * (3 * kap + 1) % p == 1


def carrier_centre(p, S, ks=None):
    """On a shell of cardinality 4S + 1, with no frame: twice 2S is −1, and k + (p − 1 − k) is twice 2S for every k < p;
    for a count k ≥ 1 the second term is its conjugate."""
    c2 = 2 * (2 * S) % p; ks = range(0, p) if ks is None else ks
    return p == 4 * S + 1 and (c2 + 1) % p == 0 and all((k + (p - 1 - k)) % p == c2 for k in ks)


def origin_unit_symmetry(p, pairs=None, xs=None):
    """x ↦ a·x + b keeps the pair {0, 1} exactly for (a, b) = (1, 0) and (−1, 1); x = 1 − x exactly when 2x = 1.
    pairs: the (a, b) tried (default every pair); xs: the residues tried for the fixed point (default every residue)."""
    it = ((a, b) for a in range(p) for b in range(p)) if pairs is None else pairs
    if any(({b % p, (a + b) % p} == {0, 1}) != ((a, b) in ((1, 0), (p - 1, 1))) for a, b in it): return False
    half = (p + 1) // 2; xs = range(p) if xs is None else xs
    return all((x == (1 - x) % p) == (2 * x % p == 1) for x in xs) and 2 * half % p == 1


def zero_shared(p, om):
    """Every label k + 1 below p is the same integer on the Subject p and on the chart of a larger shell om: the zero of a
    nonconstant mode, and the label 1 of the constant mode."""
    return p <= om and all((k + 1) % p == k + 1 == (k + 1) % om for k in range(0, p - 1))


def zeros_collide(om, o, reading=None):
    """A reading of the residues of the shell om into o < om − 2 states identifies two of the zeros 2, …, om − 1.
    The reading is y ↦ y mod o when none is given; any reading into the states 0 … o − 1 may be passed."""
    read = reading or (lambda y: y % o); seen = set()
    if not o < om - 2: return False
    for z in range(2, om):
        r = read(z)
        if not 0 <= r < o: return False
        if r in seen: return True
        seen.add(r)
    return False


def zeros_not_held(p, om, reading=None):
    """For 2 ≤ p and p² < om the p states of a Subject are fewer than the om − 2 zeros of the chart of the shell om, and
    the reading given, of its residues into p states, identifies two zeros."""
    return 2 <= p and p * p < om and p + 2 <= p * p and p < om - 2 and zeros_collide(om, p, reading)


def half_unique(p, kap):
    """The inverse of 2 is unique: 2x ≡ 1 exactly when x = 2κ + 1."""
    return [x for x in range(p) if 2 * x % p == 1] == [2 * kap + 1]


def circle_points(p, g):
    """The points of the critical circle of the frame (p, g): the pairs (a, m), 0 ≤ m < p − 1, with a·(g^m + g^{−m}) ≡ 1.
    The pair (−a, m + 2κ) is the same point of the sphere."""
    gi = pow(g, p - 2, p); out = []
    for m in range(p - 1):
        s = (pow(g, m, p) + pow(gi, m, p)) % p
        if s: out.append((pow(s, p - 2, p), m))
    return out


def circle_pair(p, g):
    """On the circle a point carries a zero ρ ≠ 0, 1, its mirror carries 1 − ρ, and a² = ρ(1 − ρ)."""
    gi = pow(g, p - 2, p)
    for a, m in circle_points(p, g):
        r, rm = a * pow(g, m, p) % p, a * pow(gi, m, p) % p
        if r in (0, 1) or rm != (1 - r) % p or a * a % p != r * (1 - r) % p: return False
    return True


def circle_frequency(p, kap, g):
    """A zero and its reflection differ by 2iγ_k: (k + 1) − (1 − (k + 1)) ≡ 2iγ_k, for 0 ≤ k < 2p."""
    i = quarter_turn(p, kap, g)
    return all(((k + 1) - (1 - (k + 1))) % p == 2 * i * frequency(p, kap, i, k) % p for k in range(0, 2 * p))


def circle_meridians(p, kap, g):
    """No point of the circle on the momentum meridian (u² = −1) or at the origin; on the prime meridian the one point is
    the centre 2⁻¹, of frequency 0."""
    i = quarter_turn(p, kap, g)
    for u in (i, (-i) % p):
        v = pow(u, p - 2, p)
        if u * u % p != p - 1 or any((a * u + a * v) % p == 1 for a in range(p)): return False
    if any((0 * u + 0 * pow(u, p - 2, p)) % p == 1 for u in range(1, p)): return False
    return [x for x in range(p) if (x + x) % p == 1] == [2 * kap + 1] and frequency(p, kap, i, 2 * kap) == 0


def circle_point(p, g):
    """A zero ρ has a point on the circle exactly when ρ(1 − ρ) is a square, and then the two pairs (a, m) and
    (−a, m + 2κ), one point of the sphere."""
    half = (p - 1) // 2; squares = {x * x % p for x in range(1, p)}; at = {}
    for a, m in circle_points(p, g):
        at.setdefault(a * pow(g, m, p) % p, []).append((a, m))
    for r in range(2, p):
        pts = at.get(r, [])
        if (len(pts) > 0) != (r * (1 - r) % p in squares): return False
        if pts and not (len(pts) == 2 and pts[1] == ((-pts[0][0]) % p, pts[0][1] + half)): return False
    return True


def circle_count(p, kap, g):
    """The circle has a point at the phase m exactly when g^{2m} ≠ −1; among the phases below 2κ that excludes κ alone;
    the phase m + 2κ gives the same point with the position −a; the 2κ − 1 points carry 2κ − 1 distinct zeros."""
    pts = dict((m, a) for a, m in circle_points(p, g))
    if any((m in pts) != (pow(g, 2 * m, p) != p - 1) for m in range(p - 1)): return False
    if [m for m in range(2 * kap) if pow(g, 2 * m, p) == p - 1] != [kap]: return False
    if any((-pts[m]) * pow(g, m + 2 * kap, p) % p != pts[m] * pow(g, m, p) % p or pts[m + 2 * kap] != (-pts[m]) % p
           for m in range(2 * kap) if m != kap): return False
    zeros = [pts[m] * pow(g, m, p) % p for m in range(2 * kap) if m != kap]
    return len(zeros) == 2 * kap - 1 == len(set(zeros))


def circle_places(p, kap, g):
    """The places j of the latitude cycle, 0 ≤ j < p − 1, and the zero ρ_j = g^j/(1 + g^j) at each; the place j = 2κ,
    where g^j = −1, carries none."""
    return {j: pow(g, j, p) * pow(1 + pow(g, j, p), p - 2, p) % p for j in range(p - 1) if j != 2 * kap}


def circle_place(p):
    """Every zero ρ is t/(1 + t) for exactly one t, namely ρ/(1 − ρ), with t ≠ 0, −1; such a t gives a zero; the inverse
    of t gives 1 − ρ."""
    inv = lambda x: pow(x, p - 2, p)
    for r in range(2, p):
        ts = [t for t in range(p) if r * (1 + t) % p == t]
        if ts != [r * inv(1 - r) % p] or ts[0] in (0, p - 1): return False
        t = ts[0]
        if (1 - r) * (1 + inv(t)) % p != inv(t): return False
    return all((t * inv(1 + t) % p) not in (0, 1) for t in range(1, p - 1))


def circle_place_cycle(p, kap, g):
    """The zeros stand on the latitude cycle: t = g^j for one j < p − 1, never j = 2κ, where 1 + g^j ≡ 0; the p − 2 other
    places carry the p − 2 zeros, once each; the centre 2⁻¹ is the place 0, and the place −j carries 1 − ρ_j."""
    n = p - 1; rho = circle_places(p, kap, g)
    return ((1 + pow(g, 2 * kap, p)) % p == 0 and sorted(rho.values()) == list(range(2, p)) and rho[0] == 2 * kap + 1
            and all(rho[(-j) % n] == (1 - rho[j]) % p for j in rho))


def circle_place_even(p, kap, g):
    """The even places: g^j is a square exactly when j is even, exactly then ρ_j(1 − ρ_j) is a square, and the place 2m
    is the point of the sphere on the circle at the phase m."""
    n = p - 1; rho = circle_places(p, kap, g); squares = {x * x % p for x in range(1, p)}
    if any((pow(g, j, p) in squares) != (j % 2 == 0) for j in range(n)): return False
    if any((j % 2 == 0) != (r * (1 - r) % p in squares) for j, r in rho.items()): return False
    return all(a * pow(g, m, p) % p == rho[2 * m % n] for a, m in circle_points(p, g))


def circle_quarter_turn(p, kap, g):
    """2ρ_j − 1 = (t − 1)/(t + 1) at t = g^j; the map x ↦ (x − 1)/(x + 1) has the square x ↦ −1/x, four steps return x
    on the residues other than 0 and ±1, and its fixed points are the two roots ±i of x² = −1."""
    inv = lambda x: pow(x, p - 2, p); i = quarter_turn(p, kap, g)
    Q = lambda x: (x - 1) * inv(x + 1) % p
    if any((2 * r - 1) % p != Q(pow(g, j, p)) for j, r in circle_places(p, kap, g).items()): return False
    xs = [x for x in range(1, p) if (x + 1) % p and (Q(x) + 1) % p]
    if any(Q(Q(x)) * x % p != p - 1 for x in xs): return False
    return sorted(x for x in range(p) if x * (x + 1) % p == (x - 1) % p) == sorted((i, (-i) % p))


def circle_counts(p, kap, g):
    """The counts: for a point (a, m) of the circle with the zero ρ = k + 1, the point (−a, −m) carries the count k
    and its mirror (−a, m) carries −ρ, the count of the conjugate mode; the two add to −1; on the prime meridian the
    one point with x + x ≡ −1 is π = 2κ."""
    gi = pow(g, p - 2, p)
    for a, m in circle_points(p, g):
        r = a * pow(g, m, p) % p; k = (r - 1) % p
        far, mirror = (-a) * pow(gi, m, p) % p, (-a) * pow(g, m, p) % p
        if far != k or mirror != (-r) % p or mirror != (p - 1 - k) % p or (far + mirror) % p != p - 1: return False
    return [x for x in range(p) if (x + x) % p == p - 1] == [2 * kap]


def circle_phase(p, g):
    """One point of the circle at each phase: the position a with a·(g^m + g^{−m}) ≡ 1 is the one inverse of the sum,
    found by search over every residue, and there is none where the sum vanishes; residues ρ and 1 − ρ of a point and
    its mirror put the point on the circle."""
    gi = pow(g, p - 2, p)
    for m in range(p - 1):
        u, v = pow(g, m, p), pow(gi, m, p); s = (u + v) % p
        if [a for a in range(p) if a * s % p == 1] != ([pow(s, p - 2, p)] if s else []): return False
        if any((a * u + a * v) % p != 1 for a in range(p) if a * v % p == (1 - a * u) % p): return False
    return True


def circle_parallels(p, kap, g):
    """The sets of constant sum: for c ≠ 0 the pairs (a, m) with a·(g^m + g^{−m}) ≡ c are the pairs of the circle with
    the position multiplied by c; the sum vanishes exactly at a = 0 and where g^{2m} ≡ −1; negating the position sends
    the sum c to the sum −c; the sums 1 and −1 share no pair; on the prime meridian the sum c has the one residue
    c·2⁻¹. Every pair (a, m) is sorted by its sum, so each set is found by search."""
    gi = pow(g, p - 2, p); half = 2 * kap + 1; n = p - 1
    s = [(pow(g, m, p) + pow(gi, m, p)) % p for m in range(n)]
    level = [set() for _ in range(p)]
    for m in range(n):
        for a in range(p): level[a * s[m] % p].add((a, m))
    C = level[1]
    if any(level[c] != {(c * a % p, m) for a, m in C} for c in range(1, p)): return False
    if level[0] != {(a, m) for m in range(n) for a in range(p) if a == 0 or pow(g, 2 * m, p) == p - 1}: return False
    if any(((-a) % p, m) not in level[(p - c) % p] for c in (1, 2, p - 1) for a, m in level[c]): return False
    return not (C & level[p - 1]) and all([x for x in range(p) if (x + x) % p == c] == [c * half % p] for c in range(p))


def circle_place_phase(p, g):
    """The phase of an even place: a point (a, m) of the circle carries g^{2m}/(1 + g^{2m}), the zero at the place 2m."""
    return all(a * pow(g, m, p) * (1 + pow(g, 2 * m, p)) % p == pow(g, 2 * m, p) for a, m in circle_points(p, g))


def circle_quarter_closes(p):
    """With y = −1/x and w = −1/y, w = x: four steps of x ↦ (x − 1)/(x + 1) return x; and −1/x = x exactly when x² ≡ −1."""
    inv = lambda x: pow(x, p - 2, p); neg_inv = lambda x: (p - 1) * inv(x) % p
    return all(neg_inv(neg_inv(x)) == x and ((neg_inv(x) == x) == (x * x % p == p - 1)) for x in range(1, p))


# The value of a mode at one label (20:D19; Theme/Steps.lean, 23 November 2026). A nonzero residue y is x^k·g^r with
# r < W when y is fewer than W steps of the drive after a power of x on the latitude cycle.
def scale_table(p, g):
    """The scale of every nonzero residue on the latitude cycle: table[x] = m with g^m = x, 0 ≤ m < p − 1."""
    table, x = [0] * p, 1
    for m in range(p - 1):
        table[x] = m; x = x * g % p
    return table


def step_width(p, g, x, table=None):
    """The least W for which every nonzero residue is x^k·g^r with r < W: the powers of x are marked at their places
    of the latitude cycle, and one pass along the cycle counts the steps of the drive from a marked place."""
    n = p - 1
    table = table or scale_table(p, g)
    marked, y = [False] * n, 1
    while not marked[table[y]]:
        marked[table[y]] = True; y = y * x % p
    worst = run = 0
    for place in range(1, n + 1):                               # the place 0 is marked: x^0 = 1
        run = 0 if marked[place % n] else run + 1
        if run > worst: worst = run
    return worst + 1


def power_steps(p, g, x, M, table=None):
    """A residue x with the distinct powers x^0, …, x^M, M ≥ 1: every nonzero residue is x^k·g^r with r < W, for the
    least W with M·W ≥ p − 1 (and so for every larger W)."""
    powers, y = set(), 1
    for _ in range(M + 1):
        powers.add(y); y = y * x % p
    return M >= 1 and len(powers) == M + 1 and step_width(p, g, x, table) <= -(-(p - 1) // M)


def label_pair(p, l):
    """The pair (N, W) of 20:D19 for a label l ≥ 2 (the paper's M and V): N the largest exponent with l^N < p, W the
    least number of steps with N·W ≥ p − 1. Every N' ≤ N and every W' with N'·W' ≥ p − 1 has W' ≥ W, so the statement at (N, W)
    gives it at (N', W')."""
    N = 0
    while l ** (N + 1) < p: N += 1
    return N, -(-(p - 1) // N)


def label_steps(p, g, l, table=None):
    """20:D19 at the label l, 2 ≤ l < p: every nonzero residue is l^k·g^r with r < W, at the largest N and the least W."""
    N, W = label_pair(p, l)
    return N >= 1 and power_steps(p, g, l, N, table) and step_width(p, g, l, table) <= W
