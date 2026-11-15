"""frc.hadrons — the hadrons theme: the exact content of 35-hadrons above the interactions theme (19 October 2026; the
revision of 14 November 2026 adds the registrations of the frame, the second order of the pairwise model, the spin-averaged
heavy-quark identity, the charge sums of Coleman–Glashow and the scaling of the model masses; the revision of 15 November
2026 adds the Carrier register of the scale and of the winding law, and the drive on the odd functions of the register).

The colour frame, the colourless content of the exterior algebra, the lines the frame maps to themselves, the Weyl constant
terms of SU(3), the flavour and isospin relations as polynomial identities, the Casimir, spin and charge arithmetic, the
admissible shells and the exact Sturm count of the finite confinement operator — the arithmetic that frc/ledgers/p35_hadrons.py decides with, every function integer,
finite-field or rational (no float). The chart readings (the PDG masses, the Airy decimals, the baryon eigenvalue) live in
frc/chart_hadrons.py. The Lean side is lean/FrcCore/Theme/Hadrons.lean; the Mathlib readings lean/FrcMathlib/Theme/Hadrons.lean.

    colour_group(), colour_scalars(F), centre(F, G), fixed_vectors(F, G, action), wedge2(F, g), colourless_content(F, G)
                                          SU(3, F_2) over F_4 by orthonormal frames (interactions.unitary_frames); its centre
                                          by the commutation table; the vectors fixed by every element on the fundamental,
                                          on Λ²(3) (the 2 × 2 minors, and the conjugate action) and on Λ³(3) = det
    lines(F), invariant_lines(F, G, action)   the 21 lines of F_4³ and those that every element maps to itself (a registration)
    derived_subgroup(F, G), abelianisation_order(F, G)
                                          the commutator subgroup by closure; |G/[G, G]| = 4, coprime to |F_4^×| = 3
    pairing_fixed_dim(F, G)               dim {X ∈ M_3(F_4) : g X g† = X}: 1, the scalars — the pairing line of 3 ⊗ 3̄
    generating_set(F, G), fixed_dim(F, G, a, b)
                                          a generating set by closure; the dimension of the vectors of 3^{⊗a} ⊗ 3̄^{⊗b} that
                                          the frame fixes, by elimination over F_4 (2 at (2, 2), 0 at (3, 1) and (2, 0))
    triality(nq, nqbar)                   (n_q − n_q̄) mod 3
    hermitian_invariant(F, G)             g†g = I on every element: the q q̄ contraction is invariant
    weyl_moments()                        E[χ^a χ̄^b] over SU(3) (interactions.su3_moment) and the contents they decide
    casimir(N), colour_factor(), g_spin(n), hyperfine_eigenvalues(), pair_correlators(), charge_structure(qs)
    character_coefficients(N)             c₁ = β/(2N²), c_adj = β²/(2N)² at leading order
    gmo_vector(), spacing_vectors(), third_difference(), hyperfine_links(), coleman_glashow(), vector_spacing()
                                          the relations as zero polynomials (interactions.Poly) over the parameters
    gap_identity(), spin_split()          M_Λ − M_N = m_s − m_l; λ_l = (M_N + M_Δ)/6, M_Δ − M_N = (3/2)λ_hf
    second_order(), second_order_pairs()  the octet residual (A/8)(1 − r)² and the two decuplet second differences (A/4)(1 − r)²
                                          of the pairwise model; the same in the pair coefficients, ⅛ and ¼ of v_ll − 2v_ls + v_ss
    hqs_identity()                        M_Λb − M_Λc = m_b − m_c = M̄_B − M̄_D, M̄ = ¼(M_P + 3M_V)
    coleman_glashow_sums()                Σ Q_i² and Σ_{i<j} Q_iQ_j of the six states; both combinations vanish
    model_masses(), scales_with_masses()  every mass expression of the models, each of degree one in its dimensionful parameters
    flavour_cube()                        3 ⊗ 3 ⊗ 3 = 10 ⊕ 8 ⊕ 8 ⊕ 1 by the moments; 27, 56
    admissible_shells(ks), shells_ok(shells)   3 | Ω + 1 on Ω ≡ 5 (mod 12)
    airy_grid(N, L), sturm_count(diag, off2, lam), sturm_brackets(N, L, brackets)
                                          the tridiagonal H^(N) = −u'' + x u on N sites of [0, L] in Fractions; Sturm's count
                                          of the eigenvalues below λ; the brackets that hold exactly one eigenvalue each
    register_roots(Om), scale_register(Om), winding_register(Om)
                                          the roots ħ of −1 and c of 2⁻¹ on a Carrier Ω = 4S + 1; (ħc)² ≡ 2S; 4c⁴ ≡ 1 and
                                          h = −ħ, so that 4M²c⁴ ≡ N·hcσ is M² ≡ N·hcσ
    winding_residues(p, kmax)             on a Subject p = 4κ + 1 the residues (4k + 3)κ ≡ −(4k + 3)/4; a radial step adds p − 1
    drive_odd_classes(p, g)               the odd exponents of the drive below p − 1: none a multiple of 2κ, no odd power ±1
    kernel_sum(p, q, zeta, t), register_commutator(p, g), register_commutator_direct(p, g)
                                          the Hamiltonian of the register |X| + F⁻¹|X|F against the drive, over F_q with a
                                          root of unity of order p: the commutator on δ₁ − δ₋₁ at the residue g is not zero
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


# ---- registration: the lines the frame maps to themselves ----------------------------------------------------------------
def lines(F, n=3):
    """The lines of F_4ⁿ, each named by its vector whose first nonzero entry is one: (4ⁿ − 1)/3 of them, 21 at n = 3."""
    out = []
    for v in product(F.elements(), repeat=n):
        lead = next((x for x in v if x != F.zero), None)
        if lead == F.one: out.append(v)
    return out


def invariant_lines(F, G, action=None):
    """The lines of F_4³ that every element of G maps to itself under `action` (None: the fundamental): g v is a nonzero
    multiple of v for every g. A registration of a state is such a line of its representation space (35:B6)."""
    act = action or (lambda g: g)
    units = [x for x in F.elements() if x != F.zero]
    mats = [act(g) for g in G]
    def kept(v):
        multiples = [tuple(F.mul(x, c) for c in v) for x in units]
        return all(mat_vec(F, a, v) in multiples for a in mats)
    return [v for v in lines(F) if kept(v)]


def derived_subgroup(F, G):
    """The subgroup generated by the commutators g h g⁻¹ h⁻¹ (g⁻¹ = g† on a unitary frame), by closure under products."""
    inv = {g: I.dagger(F, g) for g in G}
    gens = {I.mat_mul(F, I.mat_mul(F, g, h), I.mat_mul(F, inv[g], inv[h])) for g in G for h in G}
    seen, frontier = set(gens), list(gens)
    while frontier:
        nxt = []
        for x in frontier:
            for c in gens:
                y = I.mat_mul(F, x, c)
                if y not in seen: seen.add(y); nxt.append(y)
        frontier = nxt
    return seen


def abelianisation_order(F, G):
    """|G| / |[G, G]|. For SU(3, F_2) it is 4, coprime to |F_4^×| = 3: the frame has no nontrivial homomorphism into F_4^×,
    so a line that the frame maps to itself is a line that it fixes."""
    return len(G) // len(derived_subgroup(F, G))


def _nullity(F, rows, ncols):
    """The dimension of the solution space of a homogeneous linear system over F_4 (rows of coefficients), by elimination."""
    M = [list(r) for r in dict.fromkeys(tuple(r) for r in rows)]; rank = 0
    for col in range(ncols):
        piv = next((i for i in range(rank, len(M)) if M[i][col] != F.zero), None)
        if piv is None: continue
        M[rank], M[piv] = M[piv], M[rank]
        inv = F.inv(M[rank][col]); M[rank] = [F.mul(inv, x) for x in M[rank]]
        for i in range(len(M)):
            if i != rank and M[i][col] != F.zero:
                f = M[i][col]; M[i] = [F.sub(x, F.mul(f, y)) for x, y in zip(M[i], M[rank])]
        rank += 1
    return ncols - rank


def pairing_fixed_dim(F, G):
    """The dimension of {X ∈ M_3(F_4) : g X g† = X for every g}, the vectors of 3 ⊗ 3̄ that the frame fixes, and whether
    the identity spans it with trace one: (1, True) — the pairing line is the one fixed line of 3 ⊗ 3̄, and no nonzero
    traceless matrix is fixed (the adjoint holds no fixed line)."""
    E = [tuple(tuple(F.one if (r, c) == (i, j) else F.zero for c in range(3)) for r in range(3)) for i in range(3) for j in range(3)]
    flat = lambda M: [x for row in M for x in row]
    rows = []
    for g in G:
        gd = I.dagger(F, g)
        img = [flat(I.mat_mul(F, I.mat_mul(F, g, e), gd)) for e in E]
        for k in range(9):
            rows.append([F.sub(img[j][k], flat(E[j])[k]) for j in range(9)])
    one = identity(F)
    fixed_one = all(I.mat_mul(F, I.mat_mul(F, g, one), I.dagger(F, g)) == one for g in G)
    trace_one = F.add(F.add(one[0][0], one[1][1]), one[2][2]) == F.one
    return _nullity(F, rows, 9), fixed_one and trace_one


def generating_set(F, G):
    """A generating set of G: elements are added, in the list's order, while the closure under products is not all of G."""
    one = identity(F); gens, seen = [], {one}
    for g in G:
        if g in seen: continue
        gens.append(g); frontier = list(seen)
        while frontier:
            nxt = []
            for x in frontier:
                for c in gens:
                    y = I.mat_mul(F, x, c)
                    if y not in seen: seen.add(y); nxt.append(y)
            frontier = nxt
        if len(seen) == len(G): break
    return gens


def _kron(F, A, B):
    n, m = len(A), len(B)
    return tuple(tuple(F.mul(A[i // m][j // m], B[i % m][j % m]) for j in range(n * m)) for i in range(n * m))


def fixed_dim(F, G, a, b):
    """The dimension of the space of vectors of 3^{⊗a} ⊗ 3̄^{⊗b} that every element of the frame fixes (the anti-triplet
    acts by the entrywise conjugate), on a generating set, by elimination over F_4. An invariant map from 3^{⊗c} ⊗ 3̄^{⊗d}
    to 3^{⊗a} ⊗ 3̄^{⊗b} is a fixed vector of 3^{⊗(a+d)} ⊗ 3̄^{⊗(b+c)}."""
    dim = 3 ** (a + b); rows = []
    for g in generating_set(F, G):
        M = ((F.one,),)
        for _ in range(a): M = _kron(F, M, g)
        gc = conj_matrix(F, g)
        for _ in range(b): M = _kron(F, M, gc)
        for i in range(dim):
            rows.append([F.sub(M[i][j], F.one if i == j else F.zero) for j in range(dim)])
    return _nullity(F, rows, dim)


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


def second_order():
    """The second order of the pairwise model (35:C11), A = v_ll, r = m_l/m_s: ½(N + Ξ) − ¼(3Λ + Σ) − (A/8)(1 − r)² and the
    two decuplet second differences minus (A/4)(1 − r)², zero polynomials in (M₀, d, A, r)."""
    dec, o = _hyperfine_model()
    v = _P(("M0", "d", "A", "r")); A, r = v["A"], v["r"]
    sq = A * (1 - r) * (1 - r)
    octet = (o["N"] + o["X"]) * Q(1, 2) - (o["L"] * 3 + o["S"]) * Q(1, 4) - sq * Q(1, 8)
    return octet, dec["D"] - dec["Ss"] * 2 + dec["Xs"] - sq * Q(1, 4), dec["Ss"] - dec["Xs"] * 2 + dec["O"] - sq * Q(1, 4)


def second_order_pairs():
    """The same three combinations with the pair coefficients independent: the octet residual is ⅛(v_ll − 2v_ls + v_ss) and
    each decuplet second difference ¼(v_ll − 2v_ls + v_ss); zero polynomials in (m_l, m_s, v_ll, v_ls, v_ss)."""
    v = _P(("ml", "ms", "vll", "vls", "vss")); a = [v[k] for k in ("ml", "ms", "vll", "vls", "vss")]
    M = {t: baryon_mass(t, *a) for t in BARYONS}
    c = v["vll"] - v["vls"] * 2 + v["vss"]
    return ((M["N"] + M["Xi"]) * Q(1, 2) - (M["Lam"] * 3 + M["Sig"]) * Q(1, 4) - c * Q(1, 8),
            M["Del"] - M["Sgs"] * 2 + M["Xis"] - c * Q(1, 4), M["Sgs"] - M["Xis"] * 2 + M["Om"] - c * Q(1, 4))


def hqs_identity():
    """The heavy-quark relation in the pairwise model (35:C10): Λ_Q = m_Q + 2m_l − (3/4)v_ll (the light pair at spin 0, no
    hyperfine term with the heavy quark); a heavy meson has M_P = m_Q + m_l − (3/4)w_Q and M_V = m_Q + m_l + (1/4)w_Q, so
    its spin average M̄ = ¼(M_P + 3M_V) is m_Q + m_l. (M_Λb − M_Λc) − (m_b − m_c) and (M_Λb − M_Λc) − (M̄_B − M̄_D) are
    zero polynomials in (m_b, m_c, m_l, v_ll, w_b, w_c)."""
    v = _P(("mb", "mc", "ml", "v", "wb", "wc")); mb, mc, ml, vv, wb, wc = (v[k] for k in ("mb", "mc", "ml", "v", "wb", "wc"))
    Lb, Lc = mb + ml * 2 - vv * Q(3, 4), mc + ml * 2 - vv * Q(3, 4)
    avg = lambda mQ, w: ((mQ + ml - w * Q(3, 4)) + (mQ + ml + w * Q(1, 4)) * 3) * Q(1, 4)
    return (Lb - Lc) - (mb - mc), (Lb - Lc) - (avg(mb, wb) - avg(mc, wc))


CG_STATES = {"p": "uud", "n": "udd", "X0": "uss", "Xm": "dss", "Sp": "uus", "Sm": "dds"}


def coleman_glashow_sums():
    """The one-body sums Σ Q_i² and the two-body sums Σ_{i<j} Q_iQ_j of the six states of Coleman–Glashow, and the
    combination (n − p) + (Ξ⁻ − Ξ⁰) − (Σ⁻ − Σ⁺) of each: both zero, so an electromagnetic term with flavour-blind
    coefficients keeps the identity."""
    s = {k: charge_structure([QUARK_CHARGE[q] for q in c]) for k, c in CG_STATES.items()}
    comb_ = lambda i: (s["n"][i] - s["p"][i]) + (s["Xm"][i] - s["X0"][i]) - (s["Sm"][i] - s["Sp"][i])
    return s, comb_(0), comb_(1)


def model_masses():
    """Every mass expression of the paper's models, with the names of its dimensionful parameters: the first-order octet
    operator, the decuplet, the pairwise model (r = m_l/m_s is a pure number), the vector nonet, the constituent nucleon and
    Λ, and the heavy baryons and mesons."""
    out = []
    v = _P(("M0", "a", "b")); M0, a, b = v["M0"], v["a"], v["b"]
    out += [(m, ("M0", "a", "b")) for m in (M0 + a + b * Q(1, 2), M0, M0 + b * 2, M0 - a + b * Q(1, 2))]
    v = _P(("alpha", "beta")); out += [(v["alpha"] + v["beta"] * k, ("alpha", "beta")) for k in range(4)]
    dec, o = _hyperfine_model(); out += [(m, ("M0", "d", "A")) for m in list(dec.values()) + list(o.values())]
    v = _P(("a", "b")); out += [(v["a"] + v["b"] * k, ("a", "b")) for k in range(3)]
    v = _P(("ml", "ms", "v")); out += [(m, ("ml", "ms", "v")) for m in (v["ml"] * 3 - v["v"] * Q(3, 4), v["ml"] * 2 + v["ms"] - v["v"] * Q(3, 4))]
    v = _P(("mb", "mc", "ml", "v", "wb", "wc")); dims = ("mb", "mc", "ml", "v", "wb", "wc")
    out += [(v["mb"] + v["ml"] * 2 - v["v"] * Q(3, 4), dims), (v["mb"] + v["ml"] - v["wb"] * Q(3, 4), dims), (v["mc"] + v["ml"] + v["wc"] * Q(1, 4), dims)]
    return out


def scales_with_masses():
    """Every monomial of every model mass has total degree one in the dimensionful parameters: a mass is the scale times a
    pure number, and a relation among the masses holds for every value of the scale (35:X13)."""
    def degree_one(poly, dims):
        idx = [poly.names.index(d) for d in dims]
        return bool(poly.terms) and all(sum(e[i] for i in idx) == 1 for e in poly.terms)
    return all(degree_one(m, dims) for m, dims in model_masses())


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


# ---- the revision of 15 November 2026: the Carrier register and the drive on the register ------------------------------------
CARRIERS = (233, 30089, 2408561)                        # the laboratory Carriers
SUBJECTS = (13, 173, 1549)                              # the laboratory Subjects, each with the drive 2


def register_roots(Om):
    """The roots of the Carrier register on Ω = 4S + 1 (35:A11): S, the two roots ħ of −1 and the two roots c of 2⁻¹, by
    Tonelli–Shanks. S even is the existence of c."""
    from frc import arith
    S = (Om - 1) // 4
    if not (arith.is_prime(Om) and Om == 4 * S + 1 and S % 2 == 0): raise ValueError(f"register_roots: {Om} is not a prime 4S + 1 with S even")
    hb = arith.sqrt_mod(Om - 1, Om); c = arith.sqrt_mod(arith.inverse(2, Om), Om)
    assert hb * hb % Om == Om - 1 and 2 * c * c % Om == 1
    return S, (hb, Om - hb), (c, Om - c)


def scale_register(Om):
    """35:C26 — (ħc)² ≡ −2⁻¹ ≡ 2S on the Carrier Ω, for both roots ħ of −1 and both roots c of 2⁻¹: the list of
    (ħ, c, (ħc)² mod Ω), and 2S. The fourth power of the scale √(ħcσ) is then 2S σ²: a sample of tensions σ confirms it."""
    S, hs, cs = register_roots(Om)
    rows = [(h, c, (h * c) ** 2 % Om) for h in hs for c in cs]
    fourth = all(pow(h * c * sg, 2, Om) == 2 * S * sg * sg % Om for h in hs for c in cs for sg in (1, 2, 3, 5, Om - 7))
    return rows, 2 * S, fourth


def winding_register(Om, counts=(3, 7, 11)):
    """35:C24 — the winding law in the Carrier register. From 2c² ≡ 1 follows 4c⁴ ≡ 1, so 4M²c⁴ ≡ N·hcσ is M² ≡ N·hcσ;
    h = −ħ is the other root of −1. Returns 4c⁴ mod Ω for both roots c, (h² mod Ω, (h + ħ) mod Ω) for both roots ħ, and
    whether, for the counts N and a sample of tensions σ, the solution M² of 4M²c⁴ ≡ N·hcσ equals N·hcσ."""
    from frc import arith
    S, hs, cs = register_roots(Om)
    four_c4 = [4 * pow(c, 4, Om) % Om for c in cs]
    pairs = [((Om - h) ** 2 % Om, (h + (Om - h)) % Om) for h in hs]
    law = all(n * (Om - h) * c * sg * arith.inverse(4 * pow(c, 4, Om), Om) % Om == n * (Om - h) * c * sg % Om
              for h in hs for c in cs for n in counts for sg in (1, 2, 3, 5, Om - 7))
    return four_c4, pairs, law


def winding_root_free(Om, counts=(3, 7, 11)):
    """35:C27 — no choice of the roots enters the winding law. With G ≡ −2⁻¹, the residue of 2G + 1 ≡ 0, the Planck mass squared
    ħc/G is 2hc for both roots ħ of −1 and both roots c of 2⁻¹. Dividing M² ≡ N·hcσ by it gives (M/m_P)² ≡ N·σ/2, and
    M²c⁴ over ħcσ gives N·S: the same residues on the four choices. Returns the list of (ħ, c, whether ħc/G ≡ 2hc),
    whether 2G + 1 ≡ 0, and whether the two ratios hold for the counts N and a sample of tensions σ on every choice."""
    from frc import arith
    S, hs, cs = register_roots(Om)
    G = (Om - arith.inverse(2, Om)) % Om; half = arith.inverse(2, Om)
    rows = [(h, c, h * c * arith.inverse(G, Om) % Om == 2 * (Om - h) * c % Om) for h in hs for c in cs]
    ratios = all(n * (Om - h) * c * sg * arith.inverse(h * c * arith.inverse(G, Om), Om) % Om == n * sg * half % Om
                 and n * (Om - h) * c * sg * pow(c, 4, Om) * arith.inverse(h * c * sg, Om) % Om == n * S % Om
                 for h in hs for c in cs for n in counts for sg in (1, 2, 3, 5, Om - 7))
    return rows, (2 * G + 1) % Om == 0, ratios


def winding_residues(p, kmax=3):
    """35:C24 — on a Subject p = 4κ + 1 the squares of the ratios are the residues (4k + 3)κ: 4·(4k + 3)κ + (4k + 3) ≡ 0
    (mod p), since 4κ ≡ −1; one radial step adds 4κ = p − 1. Returns κ and, for k below kmax, the residue and the check."""
    kap = (p - 1) // 4
    assert p == 4 * kap + 1
    return kap, [((4 * k + 3) * kap % p, (4 * (4 * k + 3) * kap + (4 * k + 3)) % p == 0) for k in range(kmax)], 4 * kap == p - 1


def drive_odd_classes(p, g):
    """35:C25 (ii) — the drive on the odd functions of the register. The characters χⁿ of the nonzero residues have
    U χⁿ = ω⁻ⁿ χⁿ, with ω of order p − 1, and χⁿ is odd exactly for odd n; ωⁿ is real only if 2κ divides n. Returns the
    number of odd exponents below p − 1 (the dimension 2κ of the odd functions), the number of them that 2κ divides, and
    the number of odd powers of the drive below p − 1 that are 1 or −1 in the shell."""
    kap = (p - 1) // 4
    odd = range(1, p - 1, 2)
    return len(odd), sum(1 for n in odd if n % (2 * kap) == 0), sum(1 for n in odd if pow(g, n, p) in (1, p - 1))


def _prime_one_mod(p):
    from frc import arith
    q = p + 1
    while not arith.is_prime(q): q += p
    return q


def _root_of_order(p, q):
    m = (q - 1) // p; r = 2
    while pow(r, m, q) == 1: r += 1
    return pow(r, m, q)


def kernel_sum(p, q, zeta, t):
    """p·w(t) over F_q: Σ_y |y| ζ^{yt} (mod q), |y| = min(y, p − y) the step count; w is the kernel of F⁻¹|X|F."""
    return sum(min(y, p - y) * pow(zeta, y * t % p, q) for y in range(p)) % q


def register_commutator(p, g):
    """35:C25 (i) — the Hamiltonian of the register H_p = |X| + F⁻¹|X|F does not commute with the drive U on the odd
    functions. Over F_q, q the least prime ≡ 1 (mod p), with ζ of order p: p times the commutator on the odd function
    δ₁ − δ₋₁, at the residue g, is p(|g| − 1) + K(2) − K(2g), K the kernel sum. A value that is not zero over F_q is not
    zero in the cyclotomic integers. Returns (q, ζ, the value mod q)."""
    q = _prime_one_mod(p); z = _root_of_order(p, q)
    ab = lambda x: min(x % p, p - x % p)
    return q, z, (p * (ab(g) - 1) + kernel_sum(p, q, z, 2) - kernel_sum(p, q, z, 2 * g)) % q


def register_commutator_direct(p, g):
    """The same commutator by the matrices over F_q: p·(H U − U H)(δ₁ − δ₋₁) at every residue (for small p)."""
    q = _prime_one_mod(p); z = _root_of_order(p, q); gi = pow(g, p - 2, p)
    ab = lambda x: min(x % p, p - x % p)
    K = [kernel_sum(p, q, z, t) for t in range(p)]
    Hm = lambda f: [(p * ab(x) * f[x] + sum(K[(x - y) % p] * f[y] for y in range(p))) % q for x in range(p)]
    U = lambda f: [f[gi * x % p] for x in range(p)]
    v = [0] * p; v[1] = 1; v[p - 1] = q - 1
    a, b = Hm(U(v)), U(Hm(v))
    return q, [(x - y) % q for x, y in zip(a, b)]
