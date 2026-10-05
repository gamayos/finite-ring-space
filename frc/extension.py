"""frc.extension — the quadratic extension of the shell (the extension theme; ledger migration, tasks LM16 and LM20).

K = F_p(√ν) = F_{p²} for a nonsquare ν, as pairs (a, b) = a + b√ν: its arithmetic, the Frobenius conjugation and the
norm, the norm-one group N¹ (the non-split torus, cyclic of order p + 1), the diagonal forms over K, and the boost
Λ(γ, b) = [[γ, b], [νb, γ]] of the norm-one element γ + b√ν. Exact integers only (gate G09). The first ledger to use
it was 3-causality (task LM20).

    Ext(p, nu)                                 the field K: add, sub, neg, mul, conj, norm, inv, pow, elements, scalar,
                                               is_square_ext, norm_one
    ext_value_counts, ext_orthogonal_order     a diagonal form over K: its value distribution and |O(Q, K)|
    boost(g, b, nu, p)                         Λ(γ, b) as a matrix over F_p
"""
from frc.shell import is_square


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
