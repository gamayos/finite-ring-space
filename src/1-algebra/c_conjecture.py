"""
c_conjecture.py — block C: the conjecture of the conclusion, clause by clause (EXACT; C2–C4 CHART)
=================================================================================================
The conclusion conjectures that the finite substrate supports polynomial equation solving, limit-like
approximation and ε-approximation of continuous symmetries (ledger predicate 1:Y1).  Predicates 1:G1–G4 decide it:

  C1  (1:G1)  solving: f ∈ F_p[X] has a root in F_p iff gcd(f, X^p − X) ≠ 1, and deg gcd = the number of
              distinct roots — every monic polynomial of degree ≤ 3 over F_13 (2197) and F_17 (4913), by
              brute-force roots against the Euclidean gcd            [exact]
  C2  (1:G2)  limit-like approximation across shells: for r ∈ {π, e, √2, 33/10, 1/3} and ε = 10^−k
              (k = 2..8) the construction n = ⌈log₂(1/ε)⌉, x = round(r·2ⁿ), p = the first prime ≡ 1 (mod 4)
              beyond 2|x|+1 gives |r − x/2ⁿ| < ε with |x| ≤ 2κ      [chart: r read as a rational to 60 digits]
  C3  (1:G3)  the circle net: for N = p − 1 on every shell the rounding k(θ) = ⌊Nθ/2π + ½⌋ has angle error
              ≤ π/N, chord error |e^{2πik/N} − e^{iθ}| ≤ π/N, and group-law defect |k(θ₁)+k(θ₂)−k(θ₁+θ₂)| ≤ 1,
              on a grid of 4N angles plus 20000 random pairs           [chart]
  C4  (1:G4)  the SO(3) obstruction: the covering radii of the finite rotation groups in the rotation-angle
              metric — tetrahedral π/2, octahedral arccos((2√2−1)/4) ≈ 62.80°, icosahedral
              ε₀ = arccos((3√5−1)/8) ≈ 44.48° (the deep hole of the 600-cell, cos = φ²/2√2), cyclic and
              dihedral ≥ π/2 (they lie in an O(2)) — by exhaustive group closure and a sampled maximin;
              no finite subgroup of SO(3) is an ε-net for ε < ε₀      [chart; the list of groups is A3, Klein]
  C5  (1:G5)  the window resolves SO(3): the framed quaternions W_H⁴ = {q ∈ Z⁴ : |q_i| ≤ H}, normalised, are an
              ε-net of SO(3) with ε ≤ 2·arcsin(1/H) (round H·s to the lattice: |Hs − q| ≤ 1, so the angle is
              ≤ arcsin(1/H)); measured ε(1) ≈ 60.8°, ε(2) ≈ 41.0°, ε(3) ≈ 30.0°; 2·arcsin(1/3) = 38.9° < ε₀, so on
              the shell p = 73 the window H = 3 out-resolves every finite subgroup; products of window quaternions
              have entries in W_{4H²} and read back exactly from the shell when 8H² < p (20000 random pairs on
              F_73, H = 3)                                              [chart; the read-back is exact]
"""
import math, random, itertools
from fractions import Fraction
from decimal import Decimal, getcontext
try:
    from .algcommon import check, SHELLS, is_prime, kappa
except ImportError:                       # run in place (python3 c_conjecture.py)
    from algcommon import check, SHELLS, is_prime, kappa

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

def run():
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
    import algcommon
    run(); algcommon.summary(write=False)
