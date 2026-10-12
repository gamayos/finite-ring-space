"""frc.covering — the sky, the flow and the covering of the minimal pair (the subject theme; 38-s13, 12 October 2026).

The python side of the sky, flow and meridian rows of 38-s13 (blocks B, C, D of its ledger) and of the kernel-decided
instances in `lean/FrcCore/S13.lean`, with the general theorems in `lean/FrcCore/Theme/Pair.lean`: the node field and
its retarded labels, the mounting, the sky chronon as a fibre product, the tick arithmetic of the flow on C_{Ω−1} and its
double cover, the capacity stations, the step law, the tower period, the quarter classes, the momentum dual, the
covering of the node field by the winding family with its multiplicities, the ramification and the fusion, the
reflection identity, the eight-case parity table and the decider at every shell, the family law. Exact integers and
fractions only, the standard library only (gate G09). The ledger file that uses it: frc/ledgers/p38_s13.py.

    node_field(p)                     the (shell, route, row) triples of the κ shells, two routes and p − 1 rows (38:B1)
    label(p, g, k, t)                 the retarded label of row k at chronon t: k · g^{(t − k) mod (p − 1)} (38:B1)
    mounting(p, g)                    (dlog 3, the C₂₄ steps of 120°, quarter-blindness, 3·48 + 12) at the instance (38:B3)
    fibre_product(m, n, d)            the pairs (x mod m, y mod n) with x ≡ y (mod d): m n / d of them; the lcm's injection (38:B4)
    tick(n, k, b)                     the flow law as a tick count on C_n: (k − b) mod n (38:C1; Pair.tick)
    stations(n, k)                    home at b = k, the parity image at b = k + n/2 (38:C5; Pair.tick_half)
    half_turn(m, x)                   on C_{2m}: two half turns are the identity, the reflection is the negation (38:C4; Pair.half_turn)
    composed_rate(p, Om)              1/(p − 1) + 1/(Ω − 1) as a fraction: 61/696 at the instance (38:B7)
    pair_space(p, Om)                 the class-compatible pairs between two (home, home) events, each once (38:B7)
    capacity_stations(p)              the parameters t with 4·min(t, p − t) < p: {1..κ} ∪ {p − κ..p − 1} (38:D1)
    step_law()                        11/12 + 1/13 + 1/232 = 1 − (1/156 − 1/232) as exact fractions (38:D2)
    tower_period(p, g)                the drive's period p − 1 = 4κ and the seam p/2 between the rows (38:D3)
    quarter_classes(p, g)             the four classes dlog mod 4, three cells each at p = 13 (38:D5)
    tent(p, u)                        the tent fold of u = mt: u − pw on even sheets w, p(w + 1) − u on odd (38:D6, D7)
    slot(p, m, ray, t)                the node (shell, route, row) the slot (m, ray, t) lands on
    covering(p)                       the multiplicity of every node under the windings 1..p − 1, both rays, the stations (38:D7)
    covering_law(p)                   the multiplicities are 1 on odd rows and 3 on even, the counts and the position law (38:D7, D12)
    momentum_dual(p, m)               the stations and the sheet parities of the winding m (m = 5 at the instance) (38:D6)
    passages(p, m)                    the axis passages t = pj/m inside the drawn segments [0, p/4] ∪ [3p/4, p] (38:D6, D13)
    ramification(p, m)                t_{1/2} = p/(2m): inside the first drawn segment iff m ≥ 2 (38:D8)
    fusion()                          5·39 ≡ −13 (mod 104) (38:D9)
    reflection_identity(p)            ⌊ab/p⌋ + ⌊(p − a)b/p⌋ = b − 1 for all 0 < a, b < p (38:D12; Pair.reflection_identity)
    parity_table()                    the eight-case table: μ = 3 iff k̄ = 0, μ ∈ {1, 3}, the position law (38:D12; Pair.parity_table)
    decider(p)                        the four-candidate wraps against the constructed covering at every shell (38:D12)
    family_law(p)                     the one meridian law: winding 1 is M₀, winding 5 is M₃, the 144 slots drawn (38:D13)
"""
from fractions import Fraction
from math import gcd


# ---- the sky (38:B1, B3, B4, B7) -------------------------------------------------------------------------------------
def node_field(p):
    """The node field of a Subject p = 4κ + 1: κ shells (0..κ − 1), two routes (0 direct, 1 echo), p − 1 rows (1..p − 1);
    72 = 3·2·12 nodes at the instance."""
    k = (p - 1) // 4
    return [(s, e, r) for s in range(k) for e in range(2) for r in range(1, p)]


def label(p, g, k, t):
    """The retarded label of row k at chronon t: the cell's residue k times the drive state t − k, read modulo p − 1 —
    one chronon of lookback per row (38:B1)."""
    n = p - 1
    return k % p * pow(g, (t + n - k % n) % n, p) % p


def mounting(p, g):
    """The mounting at the instance (38:B3): dlog 3 = 4 (×3 = g⁴, four drive steps, 3³ = 1), 120° = 8 steps of C₂₄
    (24/3), quarter-blind (8 ≡ 4 ≡ 0 mod 4, 4 ≡ 1 mod 3), and the count 3·48 + 12 = p(p − 1)."""
    dl = next(j for j in range(p - 1) if pow(g, j, p) == 3 % p)
    return {"dlog3": dl, "order3": pow(3, 3, p) == 1, "steps120": 24 // 3, "quarter_blind": (8 % 4, 4 % 4, 4 % 3),
            "count": 3 * 48 + 12 == p * (p - 1)}


def fibre_product(m, n, d):
    """The fibre product of C_m and C_n over C_d (d | m, n): the pairs (x, y) with x ≡ y (mod d) number m n / d, and
    t ↦ (t mod m, t mod n) injects C_{lcm(m, n)} onto them; returns (count, lcm, injective onto the pairs, count == lcm)."""
    pairs = [(x, y) for x in range(m) for y in range(n) if x % d == y % d]
    L = m * n // gcd(m, n)
    image = {(t % m, t % n) for t in range(L)}
    return len(pairs), L, len(image) == L and image == set(pairs), len(pairs) == L


def composed_rate(p, Om):
    """1/(p − 1) + 1/(Ω − 1) as a fraction: 1/12 + 1/232 = 61/696 at the instance (38:B7)."""
    return Fraction(1, p - 1) + Fraction(1, Om - 1)


def pair_space(p, Om):
    """Between two (home, home) events (t < lcm) every class-compatible pair (t mod (p − 1), t mod (Ω − 1)) occurs
    exactly once: returns (the number of compatible pairs, the lcm, injective)."""
    return fibre_product(p - 1, Om - 1, gcd(p - 1, Om - 1))


# ---- the flow (38:C1, C3, C4, C5) --------------------------------------------------------------------------------------
def tick(n, k, b):
    """The flow law as a tick count on the cycle of n ticks: row k at clock b stands at (k − b) mod n (Pair.tick)."""
    return (k + (n - b % n)) % n


def stations(n, k):
    """Row k is home (count 0) at b = k and at its parity image (count n/2) at b = k + n/2 (38:C5)."""
    return tick(n, k, k), tick(n, k, k + n // 2)


def half_turn(m, x):
    """On C_{2m}: two half turns return x, the reflection x ↦ 2m − x is the negation, and the rim m is its own
    reflection (38:C4; Pair.half_turn)."""
    n = 2 * m
    return (x + m + m) % n == x % n, (x + (n - x % n)) % n == 0, (n - m % n) % n == m % n


# ---- the meridians (38:D1, D2, D3, D5, D6, D8, D9) ----------------------------------------------------------------------
def capacity_stations(p):
    """The parameters t with 4·min(t, p − t) < p: {1..κ} ∪ {p − κ..p − 1}; {1, 2, 3, 10, 11, 12} at p = 13 (38:D1)."""
    return [t for t in range(1, p) if 4 * min(t, p - t) < p]


def step_law():
    """The step 11π/12 + π/13 + π/232 against π − (π/156 − π/232), as exact fractions of π (38:D2)."""
    step = Fraction(11, 12) + Fraction(1, 13) + Fraction(1, 232)
    leak = Fraction(1, 156) - Fraction(1, 232)
    return step, 1 - leak, step == 1 - leak, step.denominator


def tower_period(p, g):
    """The drive's period p − 1 = 4κ (g^{p−1} = 1, no shorter return) and the seam p/2 between the rows (p − 1)/2 and
    (p + 1)/2 (38:D3)."""
    n = p - 1
    period = next(t for t in range(1, n + 1) if pow(g, t, p) == 1)
    return period, period == n, (n // 2, n // 2 + 1), 2 * (n // 2) < p < 2 * (n // 2 + 1)


def quarter_classes(p, g):
    """The four quarter classes on 𝔽_p^×: the cells by dlog mod 4; each class has κ cells (38:D5)."""
    dl = {}
    x = 1
    for j in range(p - 1):
        dl[x] = j
        x = x * g % p
    classes = {c: sorted(a for a in dl if dl[a] % 4 == c) for c in range(4)}
    return classes, all(len(v) == (p - 1) // 4 for v in classes.values())


def tent(p, u):
    """The tent fold of u on the cycle of 2p: u − pw on an even sheet w = ⌊u/p⌋, p(w + 1) − u on an odd one."""
    w = u // p
    return u - p * w if w % 2 == 0 else p * (w + 1) - u


def slot(p, m, ray, t):
    """The node (shell, route, row) that the slot (winding m, ray ∈ {0, 1}, parameter t) lands on: the row by the tent
    fold of u = mt, the route flipped on odd sheets, the shell min(t, p − t) − 1."""
    u = m * t
    w = u // p
    return min(t, p - t) - 1, (ray + w) % 2, tent(p, u)


def covering(p):
    """The multiplicity of every node of the node field under the windings 1..p − 1, both rays and the capacity
    stations: a dict node -> list of slots (38:D7)."""
    cov = {}
    for m in range(1, p):
        for ray in range(2):
            for t in capacity_stations(p):
                cov.setdefault(slot(p, m, ray, t), []).append((m, ray, t))
    return cov


def covering_law(p):
    """The covering parity law at p (38:D7, D12): every node is covered, with multiplicity 3 on the even rows and 1 on
    the odd rows; the odd sector's single slot is direct (t ≤ κ) on the odd shells a and echo on the even; direct and
    echo slots balance. Returns the dict of findings."""
    k = (p - 1) // 4
    nodes = node_field(p)
    cov = covering(p)
    slots = sum(len(v) for v in cov.values())
    complete = all(n in cov for n in nodes) and set(cov) == set(nodes)
    law = all(len(cov[n]) == (3 if n[2] % 2 == 0 else 1) for n in nodes)
    once = sum(1 for n in nodes if len(cov[n]) == 1)
    thrice = sum(1 for n in nodes if len(cov[n]) == 3)
    position = True
    for (s, e, r), ss in cov.items():
        a = s + 1
        if r % 2 == 1:
            direct = sum(1 for (_, _, t) in ss if t <= k)
            position &= len(ss) == 1 and ((a % 2 == 1) == (direct == 1))
        else:
            direct = sum(1 for (_, _, t) in ss if t <= k)
            position &= len(ss) == 3 and ((direct, len(ss) - direct) == ((1, 2) if a % 2 == 1 else (2, 1)))
    direct_total = sum(1 for ss in cov.values() for (_, _, t) in ss if t <= k)
    return {"nodes": len(nodes), "slots": slots, "complete": complete, "law": law, "once": once, "thrice": thrice,
            "sum": once + 3 * thrice, "position": position, "balance": direct_total == slots - direct_total}


def momentum_dual(p, m):
    """The stations of the winding m at the capacity parameters: (t, row, sheet parity) in order; at m = 5, p = 13 the
    rows 5, 10, 11 (direct) and 2, 3, 8 (echo), the route flipping at t = 3, 10 (38:D6)."""
    return [(t, tent(p, m * t), (m * t // p) % 2) for t in capacity_stations(p)]


def passages(p, m):
    """The axis passages t = pj/m (0 < j < m) that lie in the drawn segments [0, p/4] ∪ [3p/4, p], as fractions."""
    return [Fraction(p * j, m) for j in range(1, m) if 4 * p * j <= p * m or 4 * p * j >= 3 * p * m]


def ramification(p, m):
    """t_{1/2} = p/(2m) and whether it lies in the first drawn segment [0, p/4]: iff m ≥ 2 (38:D8)."""
    t = Fraction(p, 2 * m)
    return t, 4 * t <= p


def fusion():
    """5·39 ≡ −13 (mod 104): the quarter fold enacts the quarter (38:D9)."""
    return (5 * 39 + 13) % 104 == 0, 104 == 8 * 13, 39 == 3 * 13


# ---- the covering parity theorem (38:D12) -------------------------------------------------------------------------------
def reflection_identity(p):
    """⌊ab/p⌋ + ⌊(p − a)b/p⌋ = b − 1 for all 0 < a, b < p (Pair.reflection_identity)."""
    return all(a * b // p + (p - a) * b // p == b - 1 for a in range(1, p) for b in range(1, p))


def mu(A, B, C, D):
    """The multiplicity from the four candidate wraps, which must be even, odd, odd, even (Pair.mu)."""
    return (A % 2 == 0) + (B % 2 == 1) + (C % 2 == 1) + (D % 2 == 0)


def parity_table():
    """The eight-case table (Lemma *The all-shell parity table*): over ā, M̄, α ∈ {0, 1} with k̄ = ā M̄ + α, the four
    candidates match iff α = 0, α = ā, α = M̄, α = 1 + ā + M̄; μ = 3 iff k̄ = 0 and μ ∈ {1, 3}; on an odd row the match
    is direct iff ā = 1 (Pair.parity_table)."""
    ok = True
    for ab in range(2):
        for Mb in range(2):
            for al in range(2):
                kb = (ab * Mb + al) % 2
                m = (al == 0) + (al == ab) + (al == Mb) + (al == (1 + ab + Mb) % 2)
                ok &= m == (3 if kb == 0 else 1) and m in (1, 3)
                if kb == 1: ok &= (ab == 1) == ((al == 0) or (al == ab))
    return ok


def decider(p):
    """At every shell a ≤ κ and row k of p: with M = k a⁻¹ and the wraps A = ⌊aM/p⌋, B = ⌊(p − M)a/p⌋, C = ⌊M(p − a)/p⌋,
    D = ⌊(p − M)(p − a)/p⌋: the four identities A + B = a − 1, A + C = M − 1, C + D = p − 1 − a, B + D = p − 1 − M; aM = pA + k;
    μ = 3 iff k even, μ ∈ {1, 3}; on odd rows the match is direct iff a odd; and μ equals the constructed covering's
    multiplicity (38:D12)."""
    k_ = (p - 1) // 4
    cov = covering(p)
    ok = True
    for a in range(1, k_ + 1):
        inv = pow(a, -1, p)
        for k in range(1, p):
            M = k * inv % p
            A, B, C, D = a * M // p, (p - M) * a // p, M * (p - a) // p, (p - M) * (p - a) // p
            ok &= A + B == a - 1 and A + C == M - 1 and C + D == p - 1 - a and B + D == p - 1 - M and a * M == p * A + k
            m = mu(A, B, C, D)
            ok &= m == (3 if k % 2 == 0 else 1)
            if k % 2 == 1: ok &= (a % 2 == 1) == (A % 2 == 0 or B % 2 == 1)
            # the node of shell a and row k has m slots over both routes: m per route
            ok &= all(len(cov[(a - 1, e, k)]) == m for e in range(2))
    return ok


def family_law(p=13):
    """The one meridian law (38:D13): winding 1 is M₀ (rows t, no flip), winding 5 is M₃ (rows 5, 10, 11, 2, 3, 8 with
    the flips at t = 3, 10), the 24 drawn curves place 144 stations on the 72 nodes with the parity multiplicities, the
    drawn passages of winding 5 are 13/5 and 52/5, and a passage is drawn iff m ≥ 4."""
    st = capacity_stations(p)
    m0 = all(tent(p, t) == t and (t // p) % 2 == 0 for t in st)
    m3 = [r for (_, r, _) in momentum_dual(p, 5)] == [5, 10, 11, 2, 3, 8] and [f for (_, _, f) in momentum_dual(p, 5)] == [0, 0, 1, 1, 0, 0]
    law = covering_law(p)
    p5 = passages(p, 5) == [Fraction(13, 5), Fraction(52, 5)]
    drawn = all((len(passages(p, m)) >= 1) == (m >= 4) for m in range(2, p))
    return {"M0": m0, "M3": m3, "slots": law["slots"], "nodes": law["nodes"], "law": law["law"], "passages5": p5, "drawn_iff_m_ge_4": drawn}
