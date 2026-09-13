"""Discrete Fierz-Pauli gauge invariance test.

Validates the manuscript's claim (Eq. dfp, Prop. on coupling/uniqueness) that the
discrete Fierz-Pauli functional is exactly invariant under the discrete gauge orbit
  h_mn -> h_mn + D_m xi_n + D_n xi_m
on a periodic chart. Tests both central and forward differences: the continuum
invariance proof requires an anti-self-adjoint difference operator (D^T = -D),
which holds for central differences and fails for forward differences.
"""
import numpy as np

rng = np.random.default_rng(7)
d, N = 3, 8                      # d-dim periodic lattice (t,x,y), N^d sites
eta = np.diag([-1.0] + [1.0]*(d-1))

def diff(f, mu, kind):
    if kind == "central":
        return 0.5*(np.roll(f, -1, axis=mu) - np.roll(f, 1, axis=mu))
    return np.roll(f, -1, axis=mu) - f          # forward

def E_FP(h, kind):
    """h: array (d,d,N,..,N) symmetric in first two indices."""
    hu = np.einsum('ma,nb,ab...->mn...', eta, eta, h)     # indices raised
    tr = np.einsum('mn,mn...->...', eta, h)               # trace h
    E = 0.0
    for lam in range(d):
        dh  = np.stack([[diff(h[m,n],  lam, kind) for n in range(d)] for m in range(d)])
        dhu = np.stack([[diff(hu[m,n], lam, kind) for n in range(d)] for m in range(d)])
        E += 0.25*eta[lam,lam]*np.sum(dh*dhu)             # 1/4 D_l h_mn D^l h^mn
        dtr = diff(tr, lam, kind)
        E -= 0.25*eta[lam,lam]*np.sum(dtr*dtr)            # -1/4 D_l h D^l h
    divu = np.stack([sum(diff(hu[m, n], m, kind) for m in range(d))
                     for n in range(d)])                  # D_m h^mn  (index n free)
    divd = np.einsum('na,a...->n...', eta, divu)          # lowered
    E -= 0.5*np.sum(divu*divd)                            # -1/2 D_m h^mn D^l h_ln
    dtrv = np.stack([diff(tr, n, kind) for n in range(d)])
    E += 0.5*np.sum(divu*dtrv)                            # +1/2 D_m h^mn D_n h
    return E

def gauge_shift(xi, kind):
    dh = np.empty((d,d)+xi.shape[1:])
    for m in range(d):
        for n in range(d):
            dh[m,n] = diff(xi[n], m, kind) + diff(xi[m], n, kind)
    return dh

h  = rng.normal(size=(d,d)+(N,)*d); h = 0.5*(h + h.transpose(1,0,*range(2,2+d)))
xi = rng.normal(size=(d,)+(N,)*d)

ok = True
for kind in ("central", "forward"):
    E0 = E_FP(h, kind)
    E1 = E_FP(h + gauge_shift(xi, kind), kind)
    rel = abs(E1-E0)/abs(E0)
    status = "exact (machine precision)" if rel < 1e-12 else f"VIOLATED (rel. change {rel:.3e})"
    print(f"  {kind:8s} differences: gauge invariance {status}")
    if kind == "central" and rel >= 1e-12: ok = False
    if kind == "forward" and rel < 1e-12:
        print("    (unexpected: forward differences invariant)")
print("PASS" if ok else "FAIL", "- discrete FP gauge invariance (central differences)")
