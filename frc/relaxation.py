"""frc.relaxation — the Kuramoto form as exact identities, the pulse law and the readout window (the relaxation theme;
21-gravity, 26–27 October 2026).

The python side of `lean/FrcCore/Theme/Relaxation.lean` and `Theme/Window.lean`: the pair-tally current as the tally's
drive gradient and the failure tally as the mismatch norm (21:C26), the odd adjacency-local kernels as the line of the
central difference, the incidence composite as the Laplacian and the leakage form as the Laplacian form (21:C9, C22),
the pulse law of unit capacity (21:C27), the re-registration rule as a pulse accumulator and its termination (21:C28),
and the framed readout map of 22-quantum (Definition readout) on the real-quadratic strata, where the window count of
the link's current is the readout of the sine (21:C29). Exact integers and fractions; the standard library only (gate G09).
The ledger file that uses it: frc/ledgers/p21_gravity.py; the experiment that led to it:
21-gravity-20260623/reports/relaxation-window-20261027.md.

    tally_gradient(p)                W(zg) − W(zg⁻¹) = (g − g⁻¹)(z − z⁻¹) and (1 − z)(1 − z⁻¹) = E on every z, g ∈ 𝔽_p^× (the Kuramoto form)
    odd_kernels(p, n, seed)          the odd adjacency-local kernels of 𝔽_p are the line a·Δ (the central difference), exhaustively
    bdiff_fdiff_identity(f, n)       ∂̄(∂f) = Δf: the adjoint composite of the forward difference is the cycle Laplacian
    leakage_form_identity(f, n)      Σ (∂f)² = −Σ f Δf: the leakage quadratic form is the Laplacian form
    pulse_sequence(N, M)             the pulse law: s_k = ⌊kM/N⌋ with its remainder, increments 0 or 1, s_N = M, the Christoffel word
    two_cos(N, mu), two_sin(N, mu)   ζ^μ ± ζ^{−μ} on C_8 and C_12 as p + q√m, exact (the real-quadratic strata)
    isqrt_bound(x, s)                the grid bound s² ≤ x < (s + 1)²
    readout(p, q, m, g, n)           R_n(w) = (u gⁿ + v s_n)/(b gⁿ) of w = p + q√m = (u + v√m)/b, a Fraction (22-quantum, Def. readout)
    count(B, r)                      the registered count of B runs by the largest-remainder rule over (event, none): the half-up rounding of B r
    current_counts(N, B, g, n)       M(μ) for every mismatch μ of C_N: the window count of |sin(2πμ/N)| read through the map
    relax(N, mu0, M, B, a)           the re-registration rule: the pulse accumulator with the counts M, the Carrier defect a; the trajectory
    budget(M, B, mu0)                Σ_{μ=1}^{μ₀} ⌈B/M(μ)⌉, the termination bound of FRC.Relaxation.terminates
"""
import random
from fractions import Fraction
from math import gcd, isqrt

from frc.drift import christoffel
from frc.lattice import cdiff


# ---- the pair tally and its current (21:C26) ---------------------------------------------------------------------------------
def tally_gradient(p):
    """The Kuramoto form as exact identities on 𝔽_p, exhaustively over every link ratio z and every drive step g in 𝔽_p^×
    (w = z⁻¹, h = g⁻¹): the current z − w is the centred drive-difference of the pair tally W(z, w) = 2 + z + w,
    W(zg, wh) − W(zh, wg) = (g − h)(z − w); the failure tally E = 2 − z − w is the norm of the link mismatch,
    (1 − z)(1 − w) = E; and E + W = 4. Returns (ok, the number of (z, g) pairs)."""
    ok, pairs = True, 0
    W = lambda z, w: (2 + z + w) % p
    for z in range(1, p):
        w = pow(z, p - 2, p)
        ok &= ((1 - z) * (1 - w)) % p == (2 - z - w) % p and (W(z, w) + (2 - z - w)) % p == 4 % p
        for g in range(1, p):
            h = pow(g, p - 2, p)
            ok &= (W(z * g % p, w * h % p) - W(z * h % p, w * g % p)) % p == ((g - h) * (z - w)) % p
            pairs += 1
    return ok, pairs

# ---- the leakage map: the odd kernels, the incidence composite and the leakage form (21:C9, C22) ----------------------
def fdiff(f, n):
    """The forward difference (f(i+1) − f(i)) on the cycle of n sites."""
    return [f[(i + 1) % n] - f[i] for i in range(n)]


def bdiff(f, n):
    """The backward difference (f(i) − f(i−1)) on the cycle of n sites."""
    return [f[i] - f[(i - 1) % n] for i in range(n)]


def lap(f, n):
    """The cycle Laplacian (f(i+1) + f(i−1) − 2 f(i))."""
    return [f[(i + 1) % n] + f[(i - 1) % n] - 2 * f[i] for i in range(n)]


def kernel(a, b, c, f, n, p):
    """The adjacency-local shift-invariant kernel (Tf)(i) = a f(i+1) + b f(i) + c f(i−1) on 𝔽_p."""
    return [(a * f[(i + 1) % n] + b * f[i] + c * f[(i - 1) % n]) % p for i in range(n)]


def odd_kernels(p, n, seed=26):
    """Every adjacency-local shift-invariant kernel (a, b, c) ∈ 𝔽_p³ that is odd under edge reversal, (c, b, a) = −(a, b, c),
    is a multiple of the central difference and nothing else is: exhaustively over the p³ kernels, the odd ones are
    exactly the p kernels (a, 0, −a), each equal to a·Δ on random fields of 𝔽_p on the cycle of n sites, and no even
    kernel other than zero is odd. Returns (ok, the number of odd kernels)."""
    rng = random.Random(seed)
    fields = [[rng.randrange(p) for _ in range(n)] for _ in range(3)]
    odd = [(a, b, c) for a in range(p) for b in range(p) for c in range(p) if c == (-a) % p and b == (-b) % p]
    ok = len(odd) == p and all(b == 0 and c == (-a) % p for a, b, c in odd)
    for a, b, c in odd:
        for f in fields:
            ok &= kernel(a, b, c, f, n, p) == [(a * d) % p for d in cdiff(f, n)]
    ok &= all((a, 0, (-a) % p) in set(odd) for a in range(p))
    return ok, len(odd)


def bdiff_fdiff_identity(f, n):
    """∂̄(∂f) = Δf on the cycle: the adjoint composite of the forward difference (the incidence map) is the Laplacian."""
    return bdiff(fdiff(f, n), n) == lap(f, n)


def leakage_form_identity(f, n):
    """Σ_i (∂f)(i)² = −Σ_i f(i) (Δf)(i): the leakage quadratic form is the Laplacian form (the quadratic free energy)."""
    Ff, Lf = fdiff(f, n), lap(f, n)
    return sum(x * x for x in Ff) == -sum(f[i] * Lf[i] for i in range(n))



# ---- the pulse law (21:C27) --------------------------------------------------------------------------------------------------
def pulse_sequence(N, M):
    """The pulse law of unit capacity: for a transfer of M ≤ N quanta over N chronons, the counts s_k = ⌊kM/N⌋ with their
    remainders r_k satisfy s_k N + r_k = kM and r_k < N (the quotient–remainder form of FRC.Relaxation.pulse_law), the
    increments s_{k+1} − s_k are 0 or 1 (at most one quantum per chronon, none returned), s_0 = 0, s_N = M, and the
    increment word is the Christoffel word at rate M/N (frc.drift.christoffel). Returns (ok, the increment word as a string)."""
    s = [(k * M) // N for k in range(N + 1)]
    r = [(k * M) % N for k in range(N + 1)]
    ok = M <= N and all(s[k] * N + r[k] == k * M and r[k] < N for k in range(N + 1))
    inc = [s[k + 1] - s[k] for k in range(N)]
    ok &= all(d in (0, 1) for d in inc) and s[0] == 0 and s[N] == M and sum(inc) == M
    ok &= M == 0 or christoffel(M, N)
    return ok, "".join(str(d) for d in inc)


# ---- the readout window: the real-quadratic strata, the framed readout map, the counts (21:C29) ---------------------------------
STRATA = {8: 2, 12: 3}                       # the cycles whose two-way weights lie in Q(√2) and Q(√3), where 22-quantum's readout map is declared


def two_cos(N, mu):
    """ζ^μ + ζ^{−μ} = 2 cos(2πμ/N) on C_8 or C_12 as (p, q, m): p + q√m, exact."""
    mu %= N
    if N == 8:
        t = {0: (2, 0), 1: (0, 1), 2: (0, 0), 3: (0, -1), 4: (-2, 0), 5: (0, -1), 6: (0, 0), 7: (0, 1)}
    elif N == 12:
        t = {0: (2, 0), 1: (0, 1), 2: (1, 0), 3: (0, 0), 4: (-1, 0), 5: (0, -1), 6: (-2, 0), 7: (0, -1), 8: (-1, 0), 9: (0, 0), 10: (1, 0), 11: (0, 1)}
    else:
        raise ValueError("the real-quadratic strata: N = 8 or 12")
    p, q = t[mu]
    return Fraction(p), Fraction(q), STRATA[N]


def two_sin(N, mu):
    """(ζ^μ − ζ^{−μ})/i = 2 sin(2πμ/N) on C_8 or C_12 as (p, q, m), exact: twice the current."""
    mu %= N
    if N == 8:
        t = {0: (0, 0), 1: (0, 1), 2: (2, 0), 3: (0, 1), 4: (0, 0), 5: (0, -1), 6: (-2, 0), 7: (0, -1)}
    elif N == 12:
        t = {0: (0, 0), 1: (1, 0), 2: (0, 1), 3: (2, 0), 4: (0, 1), 5: (1, 0), 6: (0, 0), 7: (-1, 0), 8: (0, -1), 9: (-2, 0), 10: (0, -1), 11: (-1, 0)}
    else:
        raise ValueError("the real-quadratic strata: N = 8 or 12")
    p, q = t[mu]
    return Fraction(p), Fraction(q), STRATA[N]


def gradient_on_stratum(N):
    """W(μ+1) − W(μ−1) = −(2 sin 2π/N)(2 sin 2πμ/N) on the stratum for every μ: the chart of FRC.Relaxation.tally_gradient."""
    ok = True
    for mu in range(N):
        a, b, s1, s2 = two_cos(N, mu + 1), two_cos(N, mu - 1), two_sin(N, 1), two_sin(N, mu)
        prod = (s1[0] * s2[0] + s1[1] * s2[1] * s1[2], s1[0] * s2[1] + s1[1] * s2[0])
        ok &= (a[0] - b[0], a[1] - b[1]) == (-prod[0], -prod[1])
    return ok


def isqrt_bound(x, s):
    """The grid bound of the readout: s² ≤ x < (s + 1)²."""
    return s * s <= x < (s + 1) * (s + 1)


def readout(p, q, m, g=3, n=4):
    """The framed readout R_n(w) of w = p + q√m = (u + v√m)/b (22-quantum, Definition readout): (u gⁿ + v s_n)/(b gⁿ) with
    s_n = ⌊√(m g^{2n})⌋ by integer square root; a Fraction. Returns (R_n, s_n)."""
    b = p.denominator * q.denominator // gcd(p.denominator, q.denominator)
    u, v = int(p * b), int(q * b)
    d = gcd(gcd(abs(u), abs(v)), b)
    u, v, b = u // d, v // d, b // d
    s = isqrt(m * g ** (2 * n))
    return Fraction(u * g ** n + v * s, b * g ** n), s


def count(B, r):
    """The registered count of B runs for an event of readout r ∈ [0, 1], by the largest-remainder rule over the two outcomes
    (the event, its absence): the provisional ⌊B r⌋ plus the residual unit when the event's remainder is at least the
    other's (ties to the event, the first outcome) — the half-up rounding of B r, FRC.Relaxation.count."""
    prov = [int(B * r), int(B * (1 - r))]
    rem = [B * r - prov[0], B * (1 - r) - prov[1]]
    left = B - sum(prov)
    order = sorted((0, 1), key=lambda j: (-rem[j], j))
    for j in order[:left]: prov[j] += 1
    return prov[0]


def current_counts(N, B=81, g=3, n=4):
    """M(μ) for −N/2 ≤ μ ≤ N/2: the window count of the current's magnitude |sin(2πμ/N)| = |(ζ^μ − ζ^{−μ})/2i|, read through the
    readout map at scale n over B runs; 0 at alignment and at anti-alignment."""
    M = {}
    for mu in range(-(N // 2), N // 2 + 1):
        p, q, m = two_sin(N, mu)
        p, q = p / 2, q / 2
        assert p == 0 or q == 0                        # on the strata each value is rational or a rational multiple of √m
        sgn = (1 if p + q > 0 else -1) if p + q != 0 else 0     # the sign of p + q√m, exact
        if sgn == 0: M[mu] = 0; continue
        r, _ = readout(p * sgn, q * sgn, m, g, n)
        M[mu] = count(B, r)
    return M


# ---- the re-registration rule: the pulse accumulator (21:C28) ------------------------------------------------------------------
def relax(N, mu0, M, B=81, a=0, chronons=2000):
    """The registered mismatch μ_t of one link under the re-registration rule (FRC.Relaxation.step, run): each chronon the
    Carrier advances the relative phase by a (the defect of Lemma relcycle), the accumulator gains the window count M(μ) of
    the present mismatch, and when it reaches B one pulse fires — the chart moves one quantum toward alignment, the
    accumulator keeps the remainder. Returns (the trajectory, the pulse word, the accumulators)."""
    mu, acc, traj, word, accs = mu0, 0, [mu0], [], [0]
    for _ in range(chronons):
        acc += M[mu]
        pulse = 0
        if acc >= B:
            acc -= B; pulse = 1 if mu > 0 else (-1 if mu < 0 else 0)
        mu = mu + a - pulse
        mu = (mu + N // 2) % N - N // 2
        traj.append(mu); word.append(abs(pulse)); accs.append(acc)
    return traj, word, accs


def budget(M, B, mu0):
    """Σ_{μ=1}^{μ₀} ⌈B/M(μ)⌉: the chronon bound of FRC.Relaxation.terminates with k(μ) the least k with k·M(μ) ≥ B."""
    return sum(-(-B // M[mu]) for mu in range(1, mu0 + 1))


# ---- the spine's counting identities (27 October 2026; FRC.Static, FRC.Relaxation.quiet_run, dwell_two_values) ----------------
def first_return(L, a):
    """The first t ≥ 1 with t·a ≡ 0 (mod L): FRC.Drift.firstReturn."""
    t = 1
    while (t * a) % L: t += 1
    return t


def leakage_count(L, a, T):
    """(leakage, returns) over the window [0, T): the chronons at which the relative cycle of defect a on C_L fails to close
    and those at which it returns; leakage + returns = T, and the returns are 0 and the multiples of the first return below T
    (FRC.Static.leakage_add_returns, leakage_eq)."""
    leak = sum(1 for t in range(T) if (t * a) % L)
    return leak, T - leak


def dwell_gaps(N, mu0, B=81, M=None):
    """The dwell at each level of one run under the rule (relax): after the first pulse the carry is below the count, and the
    dwell d at a level of count M satisfies (d − 1)·M < B < (d + 1)·M, so d is ⌊B/M⌋ or ⌊B/M⌋ + 1 — the registered
    rate M/B and the dwell per quantum as the two faces of one window count (FRC.Relaxation.dwell_two_values; the
    Christoffel gaps of Lemma isopair). Returns the list of (μ, dwell, M(μ)) from μ₀ down to 1."""
    M = current_counts(N, B) if M is None else M
    traj, _, _ = relax(N, mu0, M, B=B, chronons=20 * N)
    first = {}
    for t, mu in enumerate(traj): first.setdefault(mu, t)
    return [(mu, first[mu - 1] - first[mu], M[mu]) for mu in range(mu0, 0, -1)]


def cut_area(r):
    """The cut weight of the graph ball of radius r in the cubic chart, 6(2r² + 2r + 1) (FRC.Static.cutArea)."""
    return 6 * (2 * r * r + 2 * r + 1)


def static_exterior(kappa, m, r):
    """The cut form of the static profile: a static locked transfer exists at the cut r iff the enclosed demand m is within the
    cut's capacity, m ≤ κ·A_r (FRC.Static.static_iff)."""
    return m <= kappa * cut_area(r)


def slip_radius(kappa, m):
    """The first radius at which the static exterior exists: the slip core's edge, with 12κ(r − 1)² < m ≤ 30κr² for r ≥ 1
    (FRC.Static.exterior_of_sq, slip_of_sq): r_* between √(m/30κ) and √(m/12κ) + 1."""
    r = 0
    while not static_exterior(kappa, m, r): r += 1
    return r


def selection_instance(p, g, m):
    """Character selection on 𝔽_p (FRC.Static.selection): with g^m ≢ 1 the only sequence of grade 0 (invariant under the
    drive) that also has grade m is zero, since (g^m − 1)·f = 0 forces f = 0 on a prime shell. None when g^m ≡ 1."""
    gm = pow(g, m, p)
    if gm == 1: return None
    return all(((gm - 1) * f) % p != 0 for f in range(1, p))
