"""frc.hadrons — the hadrons theme: the exact content of 35-hadrons above the interactions theme (19 October 2026).

The colour frame, the colourless content of the exterior algebra, the Weyl constant terms of SU(3), the flavour and isospin
relations as polynomial identities, the Casimir, spin and charge arithmetic, the admissible shells and the exact Sturm count
of the finite confinement operator — the arithmetic that frc/ledgers/p35_hadrons.py decides with, every function integer,
finite-field or rational (no float). The chart readings (the PDG masses, the Airy decimals, the baryon eigenvalue) live in
frc/chart_hadrons.py. The Lean side is lean/FrcCore/Theme/Hadrons.lean; the Mathlib readings lean/FrcLedger/Theme/Hadrons.lean.

    colour_group(), colour_scalars(F), centre(F, G), fixed_vectors(F, G, action), wedge2(F, g), colourless_content(F, G)
                                          SU(3, F_2) over F_4 by orthonormal frames (interactions.unitary_frames); its centre
                                          by the commutation table; the vectors fixed by every element on the fundamental,
                                          on Λ²(3) (the 2 × 2 minors, and the conjugate action) and on Λ³(3) = det
    triality(nq, nqbar)                   (n_q − n_q̄) mod 3
    hermitian_invariant(F, G)             g†g = I on every element: the q q̄ contraction is invariant
    weyl_moments()                        E[χ^a χ̄^b] over SU(3) (interactions.su3_moment) and the contents they decide
    casimir(N), colour_factor(), g_spin(n), hyperfine_eigenvalues(), pair_correlators(), charge_structure(qs)
    character_coefficients(N)             c₁ = β/(2N²), c_adj = β²/(2N)² at leading order
    gmo_vector(), spacing_vectors(), third_difference(), hyperfine_links(), coleman_glashow(), vector_spacing()
                                          the relations as zero polynomials (interactions.Poly) over the parameters
    gap_identity(), spin_split()          M_Λ − M_N = m_s − m_l; λ_l = (M_N + M_Δ)/6, M_Δ − M_N = (3/2)λ_hf
    flavour_cube()                        3 ⊗ 3 ⊗ 3 = 10 ⊕ 8 ⊕ 8 ⊕ 1 by the moments; 27, 56
    admissible_shells(ks), shells_ok(shells)   3 | Ω + 1 on Ω ≡ 5 (mod 12)
    airy_grid(N, L), sturm_count(diag, off2, lam), sturm_brackets(N, L, brackets)
                                          the tridiagonal H^(N) = −u'' + x u on N sites of [0, L] in Fractions; Sturm's count
                                          of the eigenvalues below λ; the brackets that hold exactly one eigenvalue each
"""
from fractions import Fraction as Q
from itertools import product
from math import comb

from frc import interactions as I


# ---- the colour frame over F_4 -------------------------------------------------------------------------------------------
def colour_field():
    """F_4 = F_2[t]/(t² + t + 1) as interactions.Fq2 (t² − t − 1 over F_2)."""
    return I.Fq2(2, 1, 1)


def colour_group(F=None):
    """SU(3, F_2) by orthonormal frames: the list of its 216 elements (tuples of rows over F_4)."""
    F = F or colour_field()
    return F, I.unitary_frames(F, 3)


def colour_scalars(F):
    """The scalar matrices x·I with x of norm 1: the three cube roots of unity."""
    units = [x for x in F.elements() if x != F.zero and F.norm(x) == 1]
    return [tuple(tuple(x if i == j else F.zero for j in range(3)) for i in range(3)) for x in units]


def identity(F):
    return tuple(tuple(F.one if i == j else F.zero for j in range(3)) for i in range(3))


def centre(F, G):
    """The elements commuting with every element of G."""
    return [g for g in G if all(I.mat_mul(F, g, h) == I.mat_mul(F, h, g) for h in G)]


def commutant(F, G, gens):
    """The elements of G commuting with every element of gens."""
    return [g for g in G if all(I.mat_mul(F, g, h) == I.mat_mul(F, h, g) for h in gens)]


def mat_vec(F, A, v):
    return tuple(_dot(F, A[i], v) for i in range(len(A)))


def _dot(F, r, c):
    s = F.zero
    for a, b in zip(r, c): s = F.add(s, F.mul(a, b))
    return s


def conj_matrix(F, A):
    """The entrywise conjugate: on SU(3), Λ²g = (g⁻¹)ᵀ det g = ḡ."""
    return tuple(tuple(F.conj(x) for x in r) for r in A)


def wedge2(F, A):
    """The action on Λ²(3) in the basis e₀∧e₁, e₀∧e₂, e₁∧e₂: the 2 × 2 minors."""
    pairs = [(0, 1), (0, 2), (1, 2)]
    def minor(rows, cols):
        (i, j), (k, l) = rows, cols
        return F.sub(F.mul(A[i][k], A[j][l]), F.mul(A[i][l], A[j][k]))
    return tuple(tuple(minor(pr, pc) for pc in pairs) for pr in pairs)


def fixed_vectors(F, G, action=None):
    """The nonzero vectors v with (action g) v = v for every g in G; action None is the fundamental."""
    act = action or (lambda g: g)
    zero = (F.zero,) * 3
    return [v for v in product(F.elements(), repeat=3) if v != zero and all(mat_vec(F, act(g), v) == v for g in G)]


def colourless_content(F, G):
    """The trivial-representation content of Λ^k(3), k = 0..3: (1, #fixed on 3, #fixed on Λ², 1 if det g = 1 on all)."""
    f1 = fixed_vectors(F, G)
    f2 = fixed_vectors(F, G, lambda g: wedge2(F, g))
    f2c = fixed_vectors(F, G, lambda g: conj_matrix(F, g))
    assert len(f2) == len(f2c)
    k3 = 1 if all(I.det(F, g) == F.one for g in G) else 0
    return (1, len(f1), len(f2), k3)


def hermitian_invariant(F, G):
    """g†g = I for every g: the Hermitian form, hence the q q̄ contraction, is invariant."""
    one = identity(F)
    return all(I.mat_mul(F, I.dagger(F, g), g) == one for g in G)


def triality(nq, nqbar):
    return (nq - nqbar) % 3


# ---- the Weyl constant terms of SU(3) --------------------------------------------------------------------------------------
def weyl_moments():
    """E[χ^a χ̄^b] for the pairs the hadron rows use, and the contents they decide: the singlet of 3 ⊗ 3̄ (1), none in
    3 ⊗ 3 (0), the adjoint once in 3 ⊗ 3̄ (E[χ²χ̄²] − E[χχ̄] = 1) and absent from 3 ⊗ 3 (E[χ³χ̄] − E[χ²] = 0), one singlet in
    3 ⊗ 3 ⊗ 3 (1), the adjoint twice there (E[χ⁴χ̄] − E[χ³] = 2), the squared multiplicities Σ m² = E[χ³χ̄³] = 6."""
    E = {(a, b): I.su3_moment(a, b) for (a, b) in [(1, 1), (2, 0), (2, 2), (3, 1), (3, 0), (4, 1), (3, 3)]}
    content = dict(singlet_3x3bar=E[(1, 1)], singlet_3x3=E[(2, 0)], adjoint_in_3x3bar=E[(2, 2)] - E[(1, 1)],
                   adjoint_in_3x3=E[(3, 1)] - E[(2, 0)], singlet_cube=E[(3, 0)], adjoint_in_cube=E[(4, 1)] - E[(3, 0)],
                   sum_sq_cube=E[(3, 3)])
    return E, content


def flavour_cube():
    """3 ⊗ 3 ⊗ 3 = 10 ⊕ 8 ⊕ 8 ⊕ 1: the contents by the moments, the dimension count 27 = 10 + 8 + 8 + 1, the symmetric
    spin–flavour cube Sym³(6) of C(8, 3) = 56 = 10·4 + 8·2 states."""
    _, c = weyl_moments()
    mults = {"1": c["singlet_cube"], "8": c["adjoint_in_cube"]}
    rest = 27 - mults["1"] * 1 - mults["8"] * 8                       # the dimension left for the rest
    sumsq_rest = c["sum_sq_cube"] - mults["1"] ** 2 - mults["8"] ** 2
    mults["10"] = 1 if (rest == 10 and sumsq_rest == 1) else 0        # one irreducible of dimension 10
    return mults, 3 ** 3, comb(8, 3), 10 * 4 + 8 * 2


# ---- the Casimir, spin and charge arithmetic -----------------------------------------------------------------------------
def casimir(N):
    """C₂ of the fundamental of SU(N), T-normalised: (N² − 1)/(2N)."""
    return Q(N * N - 1, 2 * N)


def colour_factor(N=3):
    """Σ_{i<j} T_i·T_j = (C₂(1) − N C₂(N))/2 on the colour singlet of N quarks; λ = 2T gives Σ λ·λ = 4 Σ T·T; per pair."""
    sumTT = (0 - N * casimir(N)) / 2
    sumll = 4 * sumTT
    return casimir(N), sumTT, sumll, sumll / comb(N, 2)


def g_spin(n):
    """Σ_{i<j} S_i·S_j for three spin-1/2 quarks at total spin S = n/2: ½S(S+1) − 9/8."""
    S = Q(n, 2)
    return Q(1, 2) * S * (S + 1) - Q(9, 8)


def hyperfine_eigenvalues():
    """(−8/3)·g_spin on the octet and the decuplet, their separation and the spin lever 3/2."""
    per_pair = colour_factor()[3]
    g1, g3 = g_spin(1), g_spin(3)
    return per_pair * g1, per_pair * g3, g3 - g1, per_pair * g3 - per_pair * g1


def pair_correlators():
    """The light pair S_u·S_d at spin 0 and 1, and S_s·(S_u + S_d) at total spin 1/2 for the pair spins 0 and 1."""
    def ss(n):                               # S·S of two spin-1/2 at total spin n/2: ½[S(S+1) − 3/2]
        S = Q(n, 2); return Q(1, 2) * (S * (S + 1) - Q(3, 2))
    def s_pair(n_tot, n_pair):               # ½[S(S+1) − S_ud(S_ud+1) − 3/4]
        S, Sp = Q(n_tot, 2), Q(n_pair, 2); return Q(1, 2) * (S * (S + 1) - Sp * (Sp + 1) - Q(3, 4))
    return dict(ud_spin0=ss(0), ud_spin1=ss(2), s_pair_lambda=s_pair(1, 0), s_pair_sigma=s_pair(1, 2))


def charge_structure(qs):
    """One-body Σ Q² and two-body Σ_{i<j} Q_iQ_j of a quark content."""
    one = sum(q * q for q in qs)
    two = sum(qs[i] * qs[j] for i in range(len(qs)) for j in range(i + 1, len(qs)))
    return one, two


QUARK_CHARGE = {"u": Q(2, 3), "d": Q(-1, 3), "s": Q(-1, 3)}


def character_coefficients(N=3):
    """The single-plaquette coefficients at leading order: c₁ = β/(2N²) (the fundamental) and c_adj = β²/(2N)² (the adjoint)."""
    return Q(1, 2 * N * N), Q(1, (2 * N) ** 2)


# ---- the relations as polynomial identities --------------------------------------------------------------------------------
def _P(names):
    return {n: I.Poly.var(names, n) for n in names}


def gmo_vector():
    """2N + 2Ξ − 3Λ − Σ with M = M₀ + aY + b[I(I+1) − Y²/4]: the zero polynomial in (M₀, a, b)."""
    v = _P(("M0", "a", "b")); M0, a, b = v["M0"], v["a"], v["b"]
    N = M0 + a + b * Q(1, 2); L = M0; S = M0 + b * 2; X = M0 - a + b * Q(1, 2)
    return N * 2 + X * 2 - L * 3 - S


def spacing_vectors():
    """The two second differences of M(n_s) = α + β n_s: zero polynomials in (α, β)."""
    v = _P(("alpha", "beta")); al, be = v["alpha"], v["beta"]
    M = [al + be * k for k in range(4)]
    return M[0] - M[1] * 2 + M[2], M[1] - M[2] * 2 + M[3]


def _hyperfine_model():
    """The linear-seed pairwise-hyperfine model: A_ij = A (m/m_i)(m/m_j), r = m/m_s; decuplet pairs +1/4; octet correlators."""
    v = _P(("M0", "d", "A", "r")); M0, d, A, r = v["M0"], v["d"], v["A"], v["r"]
    q = Q(1, 4)
    dec = dict(D=M0 + A * Q(3, 4), Ss=M0 + d + A * q * (1 + r * 2), Xs=M0 + d * 2 + A * q * (r * 2 + r * r), O=M0 + d * 3 + A * Q(3, 4) * r * r)
    octet = dict(N=M0 - A * Q(3, 4), L=M0 + d - A * Q(3, 4), S=M0 + d + A * (q - r), X=M0 + d * 2 + A * (r * r * q - r))
    return dec, octet


def third_difference():
    """M_Δ − 3M_Σ* + 3M_Ξ* − M_Ω in the model: the zero polynomial in (M₀, d, A, r)."""
    dec, _ = _hyperfine_model()
    return dec["D"] - dec["Ss"] * 3 + dec["Xs"] * 3 - dec["O"]


def hyperfine_links():
    """(M_Σ − M_Λ) − (2/3)[(M_Δ − M_N) − (M_Σ* − M_Σ)] and (M_Σ* − M_Σ) − (M_Ξ* − M_Ξ): zero polynomials."""
    dec, o = _hyperfine_model()
    l1 = (o["S"] - o["L"]) - ((dec["D"] - o["N"]) - (dec["Ss"] - o["S"])) * Q(2, 3)
    l2 = (dec["Ss"] - o["S"]) - (dec["Xs"] - o["X"])
    return l1, l2


def coleman_glashow():
    """(n − p) + (Ξ⁻ − Ξ⁰) − (Σ⁻ − Σ⁺) in one-body units δ (the d − u content 1, 1, 2): the zero polynomial."""
    v = _P(("delta",)); dl = v["delta"]
    return dl * 1 + dl * 1 - dl * 2


def vector_spacing():
    """2M_K* − M_ρ − M_φ with M = a + b n_s: the zero polynomial in (a, b)."""
    v = _P(("a", "b")); a, b = v["a"], v["b"]
    return (a + b) * 2 - a - (a + b * 2)


def gap_identity():
    """M_Λ − M_N − (m_s − m_l) with M_N = 3m_l − (3/4)v, M_Λ = 2m_l + m_s − (3/4)v: the zero polynomial."""
    v = _P(("ml", "ms", "v")); ml, ms, vv = v["ml"], v["ms"], v["v"]
    return (ml * 2 + ms - vv * Q(3, 4)) - (ml * 3 - vv * Q(3, 4)) - (ms - ml)


def spin_split():
    """(M_N + M_Δ)/6 − λ_l and (M_Δ − M_N) − (3/2)λ_hf with M_N = 3λ_l − (3/4)λ_hf, M_Δ = 3λ_l + (3/4)λ_hf: zero polynomials."""
    v = _P(("l", "f")); l, f = v["l"], v["f"]
    MN = l * 3 - f * Q(3, 4); MD = l * 3 + f * Q(3, 4)
    return (MN + MD) * Q(1, 6) - l, (MD - MN) - f * Q(3, 2)


def anchor_constituents(MN, ML, MD):
    """The constituent values from the anchors N, Λ, Δ (exact rational arithmetic on rational inputs): v_ll = (2/3)(M_Δ − M_N),
    m_l = (M_N + (3/4)v_ll)/3, m_s = m_l + (M_Λ − M_N), K = v_ll m_l²; v_ls = K/(m_l m_s), v_ss = K/m_s²."""
    v = Q(2, 3) * (MD - MN); ml = (MN + Q(3, 4) * v) / 3; ms = ml + (ML - MN); K = v * ml * ml
    return ml, ms, v, K / (ml * ms), K / (ms * ms)


# (n_l, n_s, c_ll, c_ls, c_ss): the constituent counts and the pair correlators of the octet and the decuplet
BARYONS = {
    "N": (3, 0, Q(-3, 4), Q(0), Q(0)), "Lam": (2, 1, Q(-3, 4), Q(0), Q(0)), "Sig": (2, 1, Q(1, 4), Q(-1), Q(0)),
    "Xi": (1, 2, Q(0), Q(-1), Q(1, 4)), "Del": (3, 0, Q(3, 4), Q(0), Q(0)), "Sgs": (2, 1, Q(1, 4), Q(1, 2), Q(0)),
    "Xis": (1, 2, Q(0), Q(1, 2), Q(1, 4)), "Om": (0, 3, Q(0), Q(0), Q(3, 4)),
}
OCTET = ("N", "Lam", "Sig", "Xi")


def baryon_mass(tag, ml, ms, v_ll, v_ls, v_ss):
    nl, ns, cll, cls, css = BARYONS[tag]
    return nl * ml + ns * ms + cll * v_ll + cls * v_ls + css * v_ss


def correlator_sums():
    """Σ_pairs <S_i·S_j> of every baryon equals g_spin of its multiplet: −3/4 on the octet, +3/4 on the decuplet."""
    return all(sum(BARYONS[t][2:], Q(0)) == (g_spin(1) if t in OCTET else g_spin(3)) for t in BARYONS)


# ---- the admissible shells -----------------------------------------------------------------------------------------------
def admissible_shells(ks):
    """Ω = 12k + 5 for k in ks: each has 3 | Ω + 1 (and 2 | Ω + 1, Ω + 1 ≡ 2 mod 4)."""
    return all((12 * k + 5 + 1) % 3 == 0 and (12 * k + 5 + 1) % 2 == 0 and (12 * k + 5 + 1) % 4 == 2 for k in ks)


def shells_ok(shells):
    return all(s % 12 == 5 and (s + 1) % 3 == 0 for s in shells)


# ---- the finite confinement operator: Sturm's count in Fractions ------------------------------------------------------------
def airy_grid(N, L):
    """H^(N) = −u'' + x u on N interior sites of [0, L], h = L/(N+1): the diagonal 2/h² + k h and the squared off-diagonal 1/h⁴."""
    h = Q(L, N + 1)
    return [2 / h ** 2 + k * h for k in range(1, N + 1)], 1 / h ** 4, h


def sturm_count(diag, off2, lam):
    """The number of eigenvalues of the symmetric tridiagonal (diag; constant squared off-diagonal off2) below lam, by the
    Sturm sequence q_k = d_k − λ − off2/q_{k−1}, exact in Fractions; a zero term is read as a sign change of its own."""
    cnt, q = 0, None
    for k, d in enumerate(diag):
        q = d - lam - (off2 / q if k else 0)
        if q == 0: q = Q(1, 10 ** 30) * (-1)      # the exact zero: an eigenvalue at λ; counted below
        if q < 0: cnt += 1
    return cnt


def sturm_brackets(N, L, brackets):
    """For each (lo, hi) in order, the Sturm counts at lo and hi: exactly one eigenvalue in (lo, hi) and k below lo for the
    k-th bracket means counts (k, k + 1)."""
    diag, off2, _ = airy_grid(N, L)
    return [(sturm_count(diag, off2, Q(lo)), sturm_count(diag, off2, Q(hi))) for lo, hi in brackets]
