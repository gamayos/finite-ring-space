"""Discrete Fierz-Pauli gauge invariance: exact (3+1) integer identity.

Validates the manuscript's claim (Eq. dfp, Prop. coupling/uniqueness, Prop. spacetime)
that the discrete Fierz-Pauli functional is exactly invariant under the discrete gauge
orbit
  h_mn -> h_mn + D_m xi_n + D_n xi_m
on the (3+1) periodic chart -- the same four-frame the uniqueness script works in.

The test is exact, not floating point. Fields are integer-valued and the functional is
evaluated in integer arithmetic with the dfp coefficients cleared to integers (1,-1,-2,+2)
and the undivided central difference D f = roll(f,-1) - roll(f,+1), which is integer and
anti-self-adjoint on the periodic cycle. Gauge invariance is then the exact integer identity
E[h + Dxi-symmetrised] - E[h] == 0. By the Schwartz-Zippel lemma a nonzero polynomial
identity in the field components fails on random integer points with negligible probability,
so an exact zero on random fields certifies the algebraic identity. Forward differences are
not anti-self-adjoint and the identity fails, retained as a control.
"""
import numpy as np

rng = np.random.default_rng(7)
d, N = 4, 6                       # (3+1) periodic lattice (t,x,y,z), N^d sites
eta = np.diag([-1] + [1]*(d-1))   # integer Minkowski signature

def D(f, mu, kind):
    if kind == "central":
        return np.roll(f, -1, axis=mu) - np.roll(f, 1, axis=mu)   # undivided central: integer, D^T = -D
    return np.roll(f, -1, axis=mu) - f                            # forward: integer, not anti-self-adjoint

def E_FP(h, kind):
    """Integer Fierz-Pauli functional (dfp coefficients x4 -> +1,-1,-2,+2). h symmetric in (m,n)."""
    hu = np.einsum('ma,nb,ab...->mn...', eta, eta, h)             # indices raised
    tr = np.einsum('mn,mn...->...', eta, h)                       # trace h
    E = 0
    for lam in range(d):
        dh  = np.stack([[D(h[m, n],  lam, kind) for n in range(d)] for m in range(d)])
        dhu = np.stack([[D(hu[m, n], lam, kind) for n in range(d)] for m in range(d)])
        E += int(eta[lam, lam]) * int(np.sum(dh * dhu))          # +1 D_l h_mn D^l h^mn
        dtr = D(tr, lam, kind)
        E -= int(eta[lam, lam]) * int(np.sum(dtr * dtr))         # -1 D_l h  D^l h
    divu = np.stack([sum(D(hu[m, n], m, kind) for m in range(d)) for n in range(d)])  # D_m h^mn
    divd = np.einsum('na,a...->n...', eta, divu)
    E -= 2 * int(np.sum(divu * divd))                            # -2 D_m h^mn D^l h_ln
    dtrv = np.stack([D(tr, n, kind) for n in range(d)])
    E += 2 * int(np.sum(divu * dtrv))                            # +2 D_m h^mn D_n h
    return int(E)

def gauge_shift(xi, kind):
    return np.stack([[D(xi[n], m, kind) + D(xi[m], n, kind) for n in range(d)] for m in range(d)])

h = rng.integers(-3, 4, size=(d, d) + (N,) * d)
h = h + h.transpose(1, 0, *range(2, 2 + d))                      # symmetric integer field
xi = rng.integers(-3, 4, size=(d,) + (N,) * d)

ok = True
for kind in ("central", "forward"):
    E0 = E_FP(h, kind)
    E1 = E_FP(h + gauge_shift(xi, kind), kind)
    inv = (E1 == E0)
    if inv:
        print(f"  {kind:8s} differences: gauge invariance exact (integer identity, D^T = -D)")
    else:
        print(f"  {kind:8s} differences: gauge invariance broken (E1 - E0 = {E1 - E0})")
    if kind == "central" and not inv:
        ok = False
    if kind == "forward" and inv:
        print("    (unexpected: forward differences invariant)")

print("\nPASS" if ok else "\nFAIL",
      "- discrete (3+1) FP gauge invariance: exact integer identity for central differences")
