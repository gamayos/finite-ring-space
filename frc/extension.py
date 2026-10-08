"""frc.extension — the quadratic extension of the shell (the extension theme; ledger migration, tasks LM16 and LM20).

K = F_p(√ν) = F_{p²} for a nonsquare ν, as pairs (a, b) = a + b√ν: its arithmetic, the Frobenius conjugation and the
norm, the norm-one group N¹ (the non-split torus, cyclic of order p + 1), the diagonal forms over K, and the boost
Λ(γ, b) = [[γ, b], [νb, γ]] of the norm-one element γ + b√ν. Exact integers only (gate G09). The first ledger to use
it was 3-causality (task LM20).

    Ext(p, nu)                                 the field K: add, sub, neg, mul, conj, norm, inv, pow, elements, scalar,
                                               is_square_ext, norm_one
    ext_value_counts, ext_orthogonal_order     a diagonal form over K: its value distribution and |O(Q, K)|
    boost(g, b, nu, p)                         Λ(γ, b) as a matrix over F_p

The two strata of probability (00:C10, the witness 22:stratum.py; the master's block file master/extension.py, 8 October
2026): the ring ℤ[w]/(w² − ν) or 𝔽_p[w]/(w² − ν) for any ν (split when ν is a square, as w² = 2 on Ω = 641), the python
side of Theme/Quadratic.lean's `Ext p ν` and of Theme/Extension.lean's strata section:
    Quad(nu, p=None)            the ring: el, add, neg, mul, conj, trace, norm, pow, on_line (the tally line b = 0)
    pair_tally(Q, z, k, m)      z^k z̄^(k+m) + z̄^k z^(k+m), the conjugate-pair trace tally, and its tally-line value
                                (N(z)^k · tr(z^m), 0)
    trace_seq(Q, z, n)          t_0 … t_n, t_m = tr(z^m); t_{m+2} + N(z) t_m = tr(z) t_{m+1}
    dial_tally(q, N)            over 𝔽_q with ζ of order N | q − 1: Σ_θ w±(θ), Σ_θ w₊ w₋ for w±(θ) = 2 ± (ζ^θ + ζ^−θ)
"""
from frc.shell import is_square, generators


class Ext:
    """F_{p²} = F_p[X]/(X² − ν) for a nonsquare ν: elements are pairs (a, b) = a + b√ν."""
    def __init__(self, p, nu):
        if is_square(nu, p): raise ValueError(f"Ext: {nu} is a square mod {p}")
        self.p, self.nu = p, nu % p
    def add(self, x, y): return ((x[0] + y[0]) % self.p, (x[1] + y[1]) % self.p)
    def sub(self, x, y): return ((x[0] - y[0]) % self.p, (x[1] - y[1]) % self.p)
    def neg(self, x): return ((-x[0]) % self.p, (-x[1]) % self.p)
    def mul(self, x, y):
        p, nu = self.p, self.nu
        return ((x[0] * y[0] + nu * x[1] * y[1]) % p, (x[0] * y[1] + x[1] * y[0]) % p)
    def conj(self, x): return (x[0], (-x[1]) % self.p)          # the Frobenius x ↦ x^p
    def norm(self, x): return (x[0] * x[0] - self.nu * x[1] * x[1]) % self.p
    def inv(self, x):
        n = self.norm(x)
        if n == 0: raise ZeroDivisionError("Ext.inv: zero")
        ni = pow(n, -1, self.p); c = self.conj(x)
        return (c[0] * ni % self.p, c[1] * ni % self.p)
    def pow(self, x, k):
        r = (1, 0)
        while k:
            if k & 1: r = self.mul(r, x)
            x = self.mul(x, x); k >>= 1
        return r
    def elements(self): return [(a, b) for a in range(self.p) for b in range(self.p)]
    def is_square_ext(self, x):
        """x is a square in K iff x^((p²−1)/2) = 1 (x ≠ 0)."""
        return x != (0, 0) and self.pow(x, (self.p * self.p - 1) // 2) == (1, 0)
    def scalar(self, a): return (a % self.p, 0)
    def norm_one(self):
        """The norm-one group N¹ = {z : z z̄ = 1}."""
        return [z for z in self.elements() if self.norm(z) == 1]


def ext_value_counts(K, coeffs):
    """counts[w] = #{v in K^n : Q(v) = w} for K = F_{p²} (elements as pairs), by convolution; a coefficient is an
    integer (a scalar of F_p) or an element of K."""
    els = K.elements()
    dist = {(0, 0): 1}
    for a in coeffs:
        one = {}
        for x in els:
            w = K.mul(K.scalar(a) if isinstance(a, int) else a, K.mul(x, x)); one[w] = one.get(w, 0) + 1
        new = {}
        for u, cu in dist.items():
            for w, cw in one.items():
                s = K.add(u, w); new[s] = new.get(s, 0) + cu * cw
        dist = new
    return dist


def ext_orthogonal_order(K, coeffs):
    """|O(Q, K)| for a diagonal form over K by frame counting (as frc.shell.orthogonal_order)."""
    n = 1
    for i, a in enumerate(coeffs):
        n *= ext_value_counts(K, coeffs[i:]).get(K.scalar(a), 0)
    return n


def boost(g, b, nu, p):
    """The boost Λ(γ, b) = [[γ, b], [νb, γ]] over F_p; it preserves x² − ν t² when γ² − νb² = 1."""
    return ((g % p, b % p), (nu * b % p, g % p))


# ------------------------------------------------------------------------------------------------------------
# the two strata of probability (00:C10): the quadratic ring and the two reductions

class Quad:
    """The ring ℤ[w]/(w² − ν) (p None) or 𝔽_p[w]/(w² − ν), ν a square or not: elements are pairs (a, b) = a + b w.
    The python side of lean/FrcCore/Theme/Quadratic.lean's `Ext p ν`; the tally line is the elements (a, 0)."""

    def __init__(self, nu, p=None):
        self.nu, self.p = nu, p

    def red(self, x): return x % self.p if self.p else x
    def el(self, a, b=0): return (self.red(a), self.red(b))
    def add(self, x, y): return self.el(x[0] + y[0], x[1] + y[1])
    def neg(self, x): return self.el(-x[0], -x[1])
    def mul(self, x, y): return self.el(x[0] * y[0] + self.nu * x[1] * y[1], x[0] * y[1] + x[1] * y[0])
    def conj(self, x): return self.el(x[0], -x[1])
    def trace(self, x): return self.red(2 * x[0])
    def norm(self, x): return self.red(x[0] * x[0] - self.nu * x[1] * x[1])
    def on_line(self, x): return x[1] == 0

    def pow(self, x, n):
        out = self.el(1)
        for _ in range(n): out = self.mul(out, x)
        return out


def pair_tally(Q, z, k, m):
    """The conjugate-pair trace tally z^k z̄^(k+m) + z̄^k z^(k+m) in Q, and the tally-line element (N(z)^k · tr(z^m), 0)
    it equals (Extension.lean: conjugate_pair_tally)."""
    zb = Q.conj(z)
    lhs = Q.add(Q.mul(Q.pow(z, k), Q.pow(zb, k + m)), Q.mul(Q.pow(zb, k), Q.pow(z, k + m)))
    return lhs, Q.el(Q.red(Q.norm(z) ** k) * Q.trace(Q.pow(z, m)))


def trace_seq(Q, z, n):
    """t_0 … t_n, t_m = tr(z^m); t_{m+2} + N(z) t_m = tr(z) t_{m+1} (Extension.lean: trace_recurrence)."""
    return [Q.trace(Q.pow(z, m)) for m in range(n + 1)]


def dial_tally(q, N):
    """Over 𝔽_q with ζ of order N (N | q − 1): the dial-ensemble sums Σ_θ w₊(θ), Σ_θ w₋(θ), Σ_θ w₊(θ) w₋(θ) for
    w±(θ) = 2 ± (ζ^θ + ζ^−θ), θ < N, as residues (Extension.lean: dial_tally); the complete character sums cancel."""
    if (q - 1) % N: raise ValueError(f"dial_tally: {N} does not divide {q} - 1")
    z = pow(generators(q)[0], (q - 1) // N, q); zi = pow(z, N - 1, q)
    sp = sm = spm = 0
    for t in range(N):
        c = (pow(z, t, q) + pow(zi, t, q)) % q
        wp, wm = (2 + c) % q, (2 - c) % q
        sp, sm, spm = (sp + wp) % q, (sm + wm) % q, (spm + wp * wm) % q
    return sp, sm, spm


# ---- the pair tally on the Q₄ core (00:C11; 22-quantum Prop. gleason, Extension.lean section Tally) ----
GI = Quad(-1)                    # ℤ[i] as pairs (a, b)


def ipow(n):
    """i^n in ℤ[i]."""
    return [(1, 0), (0, 1), (-1, 0), (0, -1)][n % 4]


def q4_kernel(c):
    """K_c(d) = Σ_r c_r i^{rd}, the tally combination of the four characters, as the list K_c(0..3)."""
    return [GI.el(sum(cr * ipow(r * d)[0] for r, cr in enumerate(c)), sum(cr * ipow(r * d)[1] for r, cr in enumerate(c))) for d in range(4)]


def q4_winding(k):
    """The pure winding ψ_k(u) = i^{ku} restricted to the fibre."""
    return [ipow(k * u) for u in range(4)]


def q4_tally(K, psi):
    """F(K, ψ) = Σ_{u,v} K(v − u) ψ_u conj(ψ_v) on one fibre of four points."""
    tot = GI.el(0)
    for u in range(4):
        for v in range(4):
            tot = GI.add(tot, GI.mul(GI.mul(K[(v - u) % 4], psi[u]), GI.conj(psi[v])))
    return tot


def q4_inversion(K, r):
    """Σ_d K(d) i^{−rd}: four times the coefficient c_r of an admissible kernel."""
    tot = GI.el(0)
    for d in range(4): tot = GI.add(tot, GI.mul(K[d], ipow(-r * d)))
    return tot


def q4_dft_det():
    """The determinant of the core DFT matrix (i^{ru})_{r,u<4} in ℤ[i], by the Leibniz expansion."""
    import itertools
    M = [[ipow(r * u) for u in range(4)] for r in range(4)]
    det = GI.el(0)
    for perm in itertools.permutations(range(4)):
        sign = (-1) ** sum(1 for a in range(4) for b in range(a + 1, 4) if perm[a] > perm[b])
        term = GI.el(sign)
        for r in range(4): term = GI.mul(term, M[r][perm[r]])
        det = GI.add(det, term)
    return det

