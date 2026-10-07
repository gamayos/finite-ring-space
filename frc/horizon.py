"""frc.horizon — the shell theorem in the 𝔽_p reading (the horizon theme; ledger migration, task LM26, 6 October 2026).

The python side of `lean/FrcCore/Theme/Horizon.lean`: on a frame (p = 4κ + 1, g a drive, n = p − 1) the finite zeta
Z(k) = Σ_{x≠0} x^k, the coefficients of a vector in the power modes x ↦ x^k, the scale-shift x ↦ g^r x and its fixed
points, and the readout z(θ) = 2⁻¹ + θη on the self-dual line Tr z = 1. Exact integers mod p only, the standard library
only (gate G09). The first ledger to use it is the master's block file frc/ledgers/master/horizon.py.

    zeta(p, k)                   Z(k) = Σ_{x=1}^{p−1} x^k mod p
    mode_coeffs(p, g, v)         c_k = −Σ_{l<n} v_l g^((n−l)k), k < n: the Lean proof's coefficients
    expand(p, g, c, j)           Σ_{k<n} c_k (g^j)^k, the vector at the point x = g^j
    shift(p, g, r, x)            g^r x
    fixed_points(p, g, r)        the nonzero residues x with g^r x = x
    readout(p, theta)            (2⁻¹, θ): the point 2⁻¹ + θη as (real part, η-part), 2⁻¹ = 2κ + 1
    trace(p, z)                  Tr z = 2 Re z
"""


def zeta(p, k):
    """The finite zeta Z(k) = Σ_{x≠0} x^k on the shell p."""
    return sum(pow(x, k, p) for x in range(1, p)) % p


def mode_coeffs(p, g, v):
    """The coefficients of the vector v (indexed by the cycle, v[j] at x = g^j) in the power modes: c_k = −Σ_l v_l g^((n−l)k)."""
    n = p - 1
    return [(-sum(v[l] * pow(g, (n - l) * k, p) for l in range(n))) % p for k in range(n)]


def expand(p, g, c, j):
    """The expansion Σ_k c_k (g^j)^k at the point x = g^j."""
    x = pow(g, j, p)
    return sum(ck * pow(x, k, p) for k, ck in enumerate(c)) % p


def shift(p, g, r, x):
    """The scale-shift x ↦ g^r x."""
    return pow(g, r, p) * x % p


def fixed_points(p, g, r):
    """The nonzero residues the scale-shift x ↦ g^r x fixes."""
    return [x for x in range(1, p) if shift(p, g, r, x) == x]


def readout(p, theta):
    """The readout z(θ) = 2⁻¹ + θη as the pair (2κ + 1, θ)."""
    return ((p - 1) // 2 + 1) % p, theta % p


def trace(p, z):
    """The trace Tr(a + bη) = 2a."""
    return 2 * z[0] % p
