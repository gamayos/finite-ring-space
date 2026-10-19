"""super — superconductivity on the split torus (the super theme, 19 October 2026): the master's G19 and G20, developed in
the master without a paper ledger (34-super is unpublished; its theorems C1, C3–C5, C9, C10 and its prediction D1 are the
content).

Exact throughout: the integers and Fractions, the ring ℤ[√2] as integer pairs, the charge–flux lattice ℤ_q ⊕ ℤ_q, the
metrology products as polynomials (frc.interactions.Poly), and the even and odd Airy ladders by Sturm's count of the finite
operator −u'' + x u on [0, L] through the hadrons theme's tridiagonal (frc.hadrons.sturm_count). No float decides anything.

    dual_map(p, g)             the dual map on the cycle ℤ_q, q = p − 1, is the shell transform F = iW with F² = J, F⁴ = I (34-super C1)
    winding_kernel(q, n)       the n-tuples of ℤ_q of total winding 0: q^(n−1) of them; for n = 2 the inverse pairs (k, −k)
    residual(q, qc)            the vorticities b with qc·b ≡ 0 (mod q): the subgroup the charge-qc condensate leaves deconfined
    self_dual_point()          (1 + w)(w − 1) = 1, (1 + w) − (w − 1) = 2, (2 + w)(w − 1) = w in ℤ[√2]: sinh 2β* = 1, tanh β* = √2 − 1, τ(β*) = 0
    symplectic(q)              S(a, b) = (b, −a) on ℤ_q ⊕ ℤ_q: S² = −I, S⁴ = I, the pairing ab' − a'b invariant, the objects mapped
    metrology()                (2e)(h/2e) = h, K_J R_K Q = 4 (Q = 2e), 2 (Q = e), the Josephson and phase-slip steps, as polynomial identities with e⁻¹, h⁻¹ as variables
    even_grid, sturm_even      the even (Neumann) finite operator and Sturm's count in Fractions
    airy_ladder(N, L, ...)     the brackets of E₁ (even), E₂ (odd), E₃ (even) and the bounds on ρ = (E₃ − E₂)/(E₂ − E₁)
"""
from fractions import Fraction as Q
from itertools import product
from math import gcd

from frc import fourier as F
from frc import hadrons as H
from frc import interactions as I


# ---- the dual map is the quarter-turn transform (00:G19; 34-super C1) --------------------------------------------------------
def dual_map(p, g):
    """On the cycle ℤ_q of the frame (p, g), q = p − 1 with 4 | q: the Dirac pairing ⟨a, b⟩ = ω^{ab} is the kernel of the
    shell transform F = iW (frc.fourier.transform), and F² = J (the reversal), F⁴ = I: the dual map is Q₄, the order-four
    quarter-turn (Transform.lean: F_sq, J_sq). Returns (F² == J, F⁴ == I, q % 4 == 0)."""
    W, J, Fm = F.transform(p, g)
    F2 = F.matmul(Fm, Fm, p); F4 = F.matmul(F2, F2, p)
    return F2 == J, F4 == F.identity(p - 1), (p - 1) % 4 == 0


# ---- the winding kernel and the residual subgroup (00:G19; 34-super C3, C4) ----------------------------------------------
def winding_kernel(q, n):
    """The n-tuples of ℤ_q with total winding 0 (the kernel of Σ: (ℤ_q)^n → ℤ_q): their number is q^(n−1); for n = 2 every
    one is an inverse pair (k, −k). Returns (count, inverse) with inverse True when n = 2 and every tuple is (k, −k mod q)."""
    tuples = [t for t in product(range(q), repeat=n) if sum(t) % q == 0]
    inverse = n != 2 or all(b == (-a) % q for a, b in tuples)
    return len(tuples), inverse


def residual(q, qc=2):
    """The vorticities b in ℤ_q with qc·b ≡ 0 (mod q): the subgroup the charge-qc condensate leaves unconfined, of order
    gcd(qc, q) — ℤ₂ for qc = 2 and 4 | q (the split torus of Ω ≡ 5 (mod 12))."""
    return [b for b in range(q) if (qc * b) % q == 0]


# ---- the self-dual point in ℤ[√2] (00:G19; 34-super C5) -------------------------------------------------------------------
def r2_mul(x, y):
    """(a + b√2)(c + d√2) = (ac + 2bd) + (ad + bc)√2 on integer pairs."""
    return (x[0] * y[0] + 2 * x[1] * y[1], x[0] * y[1] + x[1] * y[0])


def self_dual_point():
    """With w = √2 and x = e^{2β*} = 1 + w: (1 + w)(w − 1) = 1 (so x − x⁻¹ = (1 + w) − (w − 1) = 2 and sinh 2β* = 1),
    (2 + w)(w − 1) = w (so tanh β* = (x − 1)/(x + 1) = w/(2 + w) = w − 1 = √2 − 1), and τ(β*) = 2β* + ln tanh β* =
    ln[(1 + w)(w − 1)] = ln 1 = 0; x² − 2x − 1 = 0 is the fixed point of sinh 2β sinh 2β̃ = 1. Returns the three products and
    the quadratic, as pairs (a, b) = a + b√2."""
    one, w = (1, 0), (0, 1)
    x, xi = (1, 1), (-1, 1)                                  # 1 + √2 and √2 − 1 = x⁻¹
    prod = r2_mul(x, xi)                                     # (1 + √2)(√2 − 1) = 1
    diff = (x[0] - xi[0], x[1] - xi[1])                      # x − x⁻¹ = 2
    tanh = r2_mul((2, 1), xi)                                # (2 + √2)(√2 − 1) = √2
    quad = r2_mul(x, x); quad = (quad[0] - 2 * x[0] - 1, quad[1] - 2 * x[1])   # x² − 2x − 1 = 0
    return dict(prod=prod, diff=diff, tanh=tanh, quad=quad, one=one, w=w)


# ---- the symplectic quarter-turn on the charge–flux lattice (00:G20; 34-super C9) ---------------------------------------
def S(v, q):
    """S(a, b) = (b, −a) on ℤ_q ⊕ ℤ_q."""
    a, b = v
    return (b % q, (-a) % q)


def pairing(u, v, q):
    """The Dirac pairing ω((a, b), (a', b')) = ab' − a'b (mod q)."""
    return (u[0] * v[1] - v[0] * u[1]) % q


def symplectic(q):
    """Over every pair of ℤ_q ⊕ ℤ_q: S² = −I, S⁴ = I; over every two points the pairing is S-invariant; the condensate (2, 0)
    goes to (0, −2) and the unit vortex (0, 1) to the unit charge (1, 0). Returns the four verdicts."""
    pts = [(a, b) for a in range(q) for b in range(q)]
    sq = all(S(S(v, q), q) == ((-v[0]) % q, (-v[1]) % q) for v in pts)
    quart = all(S(S(S(S(v, q), q), q), q) == v for v in pts)
    inv = all(pairing(S(u, q), S(v, q), q) == pairing(u, v, q) for u in pts for v in pts)
    objects = S((2, 0), q) == (0, (-2) % q) and S((0, 1), q) == (1, 0)
    return sq, quart, inv, objects


# ---- the metrology closure (00:G20; 34-super C10) --------------------------------------------------------------------------
def metrology():
    """With e, h, their inverses E = e⁻¹, Hi = h⁻¹, the step index n and the frequency f as polynomial variables: the action
    quantum (2e)(h·E/2) − h·(eE) is the zero polynomial (so (2e)(h/2e) = h when eE = 1); the closure K_J R_K Q with
    K_J = 2e·Hi, R_K = h·E·E: for Q = 2e it is 4 (eE)²(h Hi) and for Q = e it is 2 (eE)²(h Hi), both as zero polynomials
    of the difference; the Josephson step V_n = n f/K_J = n(h/2e)f satisfies V_n K_J = n f (eE)(h Hi), and the phase-slip
    step I_n = n(2e)f is its S-image with V_n I_n = n² f² h (eE): the two quantisation constants (h/2e) and (2e) multiply
    to the action quantum. Returns the five differences (dict action, pair, single, step, product), each the zero polynomial."""
    names = ("e", "h", "E", "Hi", "n", "f")
    e, h, E, Hi, n, f = (I.Poly.var(names, x) for x in names)
    action = (2 * e) * (h * E * Q(1, 2)) - h * (e * E)
    KJ, RK = 2 * e * Hi, h * E * E
    pair = KJ * RK * (2 * e) - 4 * (e * E) * (e * E) * (h * Hi)
    single = KJ * RK * e - 2 * (e * E) * (e * E) * (h * Hi)
    Vn, In = n * f * h * E * Q(1, 2), n * (2 * e) * f
    step = Vn * KJ - n * f * (e * E) * (h * Hi)
    product = Vn * In - n * n * f * f * h * (e * E)
    return dict(action=action, pair=pair, single=single, step=step, product=product)


# ---- the even and odd Airy ladders by Sturm's count (00:G20; 34-super D1) ------------------------------------------------
def even_grid(N, L):
    """The even (Neumann) finite operator −u'' + x u on the sites x_k = k h, k = 0 … N, h = L/(N+1), with u(−h) = u(h) at
    the origin and u(L) = 0: the diagonal 2/h² + k h and, after the symmetrising rescaling of the origin, the squared
    off-diagonal 2/h⁴ on the first link and 1/h⁴ on the others."""
    h = Q(L, N + 1)
    return [2 / h ** 2 + k * h for k in range(0, N + 1)], h


def sturm_even(N, L, lam):
    """Sturm's count of the even operator's eigenvalues below lam, exact in Fractions."""
    diag, h = even_grid(N, L); off2 = 1 / h ** 4
    cnt, q = 0, None
    for k, d in enumerate(diag):
        c2 = 2 * off2 if k == 1 else off2
        q = d - lam - (c2 / q if k else 0)
        if q == 0: q = -Q(1, 10 ** 30)
        if q < 0: cnt += 1
    return cnt


def airy_ladder(N, L, even_brackets, odd_brackets):
    """The Sturm counts at the ends of the brackets of the even levels (E₁, E₃, …) and the odd levels (E₂, E₄, …), and the
    exact bounds on ρ = (E₃ − E₂)/(E₂ − E₁) from the first three brackets: (lo, hi) with
    lo = (E₃⁻ − E₂⁺)/(E₂⁺ − E₁⁻) and hi = (E₃⁺ − E₂⁻)/(E₂⁻ − E₁⁺)."""
    ev = [(sturm_even(N, L, Q(lo)), sturm_even(N, L, Q(hi))) for lo, hi in even_brackets]
    diag, off2, _ = H.airy_grid(N, L)
    od = [(H.sturm_count(diag, off2, Q(lo)), H.sturm_count(diag, off2, Q(hi))) for lo, hi in odd_brackets]
    (e1l, e1h), (e3l, e3h) = (Q(a) for a in even_brackets[0]), (Q(a) for a in even_brackets[1])
    e2l, e2h = (Q(a) for a in odd_brackets[0])
    rho = ((e3l - e2h) / (e2h - e1l), (e3h - e2l) / (e2l - e1h))
    return ev, od, rho
