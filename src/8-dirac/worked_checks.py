#!/usr/bin/env python3
"""The F_13 worked examples as registered checks (EXACT).

Drives finite_checks.py (the paper's p = 13 computations, kept verbatim as the library) and turns its printed
booleans into predicates:

  S1  Power-map counts on F_13^× (Prop. power-map-count): image size (p−1)/gcd(ε, p−1) and loss factor
      gcd(ε, p−1) for ε = 1, 2, 3, 4, 6, 12; each nonempty fibre of size gcd.
  S2  The Euclidean Schrödinger example (Example cayley-13, Thm. cayley-preservation, Cor. finite periodicity,
      Thm. period-dichotomy): H = −Δ on F_13, α = c: U^13 = I; every trace-zero α = kc is admissible
      (H nilpotent), with exact order 13 for k ≠ 0 and 1 for k = 0; U is unitary for the Hermitian form.
  S3  The Dirac example (Example dirac-13; Prop. clifford, Prop. spin-conjugation, Prop. transported-dirac-form,
      Cor. boost-covariance): Clifford relations with η = diag(−2, 1, 1, 1); the boost formulas S⁻¹γ⁰S =
      Aγ⁰ + νBγ¹, S⁻¹γ¹S = Bγ⁰ + Aγ¹; the transported γ̂⁰ = Aγ⁰ − νBγ¹, γ̂¹ = −Bγ⁰ + Aγ¹ with A = 10, B = 2;
      the covariance identity D_{Λ,S} T ψ = T D_{E0} ψ on a sample field.
Class: EXACT.
"""
from math import gcd
import finite_checks as fc
from dcommon import check

def run():
    P, NU = fc.P, fc.NU
    # S1 — power maps
    ok = True
    for eps in (1, 2, 3, 4, 6, 12):
        image = {pow(x, eps, P) for x in range(1, P)}
        d = gcd(eps, P - 1)
        ok &= (len(image) == (P - 1) // d) and all(sum(1 for x in range(1, P) if pow(x, eps, P) == y) == d for y in image)
    check("fin.S1", ok, "ε = 1, 2, 3, 4, 6, 12 on F_13^×; fibres of size gcd(ε, 12)")

    # S2 — the Schrödinger example
    n = P
    eye = fc.identity(n)
    shift, shift_inv = fc.zero_matrix(n, n), fc.zero_matrix(n, n)
    for j in range(n):
        shift[(j - 1) % n][j] = fc.ONE; shift_inv[(j + 1) % n][j] = fc.ONE
    delta = fc.mat_sub(fc.mat_add(shift, shift_inv), fc.scalar_mul(fc.scalar(2), eye))
    H = fc.scalar_mul(fc.scalar(-1), delta)
    def cayley_for(alpha):
        return fc.mat_mul(fc.mat_inv(fc.mat_sub(eye, fc.scalar_mul(alpha, H))), fc.mat_add(eye, fc.scalar_mul(alpha, H)))
    def order(M, bound=200):
        cur = fc.identity(n)
        for e in range(1, bound + 1):
            cur = fc.mat_mul(cur, M)
            if fc.mat_eq(cur, eye): return e
        return None
    U = cayley_for(fc.C)
    ok = fc.mat_eq(fc.mat_pow(U, 13), eye)
    orders = {}
    for k in range(P):
        try:
            Uk = cayley_for(fc.Fp2(0, k)); orders[k] = order(Uk)
        except ValueError:
            orders[k] = None
    ok &= all(orders[k] == 13 for k in range(1, P)) and orders[0] == 1
    # unitarity: U^† U = I with the conjugate-transpose over K = F_13[w]/(w²−2), conj(a + bw) = a − bw
    def dagger(M):
        return [[fc.Fp2(M[j][i].a, (-M[j][i].b) % P) for j in range(n)] for i in range(n)]
    ok &= fc.mat_eq(fc.mat_mul(dagger(U), U), eye)
    check("fin.S2", ok, f"U^13 = I; orders {sorted(set(orders.values()))}; U†U = I")

    # S3 — the Dirac example
    g0, g1, g2, g3 = fc.gamma_matrices()
    gammas = [g0, g1, g2, g3]; eta = [-NU, 1, 1, 1]
    ok = True
    for mu in range(4):
        for nu in range(4):
            lhs = fc.anticommutator(gammas[mu], gammas[nu])
            rhs = fc.zero_matrix(4, 4)
            for i in range(4): rhs[i][i] = fc.scalar(2 * eta[mu] if mu == nu else 0)
            ok &= fc.mat_eq(lhs, rhs)
    delta_inv = fc.scalar(1 - NU).inv()
    M = fc.mat_mul(g0, g1)
    S = fc.mat_add(fc.identity(4), M); S_inv = fc.scalar_mul(delta_inv, fc.mat_sub(fc.identity(4), M))
    A = fc.scalar(1 + NU) / fc.scalar(1 - NU); B = fc.scalar(-2) / fc.scalar(1 - NU)
    ok &= (A.a, A.b, B.a, B.b) == (10, 0, 2, 0)
    ok &= fc.mat_eq(fc.mat_mul(fc.mat_mul(S_inv, g0), S), fc.mat_add(fc.scalar_mul(A, g0), fc.scalar_mul(fc.scalar(NU) * B, g1)))
    ok &= fc.mat_eq(fc.mat_mul(fc.mat_mul(S_inv, g1), S), fc.mat_add(fc.scalar_mul(B, g0), fc.scalar_mul(A, g1)))
    t0 = fc.mat_mul(fc.mat_mul(S, g0), S_inv); t1 = fc.mat_mul(fc.mat_mul(S, g1), S_inv)
    ok &= fc.mat_eq(t0, fc.mat_add(fc.scalar_mul(A, g0), fc.scalar_mul(-fc.scalar(NU) * B, g1)))
    ok &= fc.mat_eq(t1, fc.mat_add(fc.scalar_mul(-B, g0), fc.scalar_mul(A, g1)))
    a, b = A.a, B.a
    lam = [[a, b, 0, 0], [(NU * b) % P, a, 0, 0], [0, 0, 1, 0], [0, 0, 0, 1]]
    boosted = [(a, (NU * b) % P, 0, 0), (b, a, 0, 0), (0, 0, 1, 0), (0, 0, 0, 1)]
    sample = {(0, 0, 0, 0): [fc.ONE, fc.C, fc.ZERO, fc.scalar(2)], (1, 2, 0, 0): [fc.scalar(3), fc.ZERO, fc.I_T, fc.ONE], (5, 0, 1, 0): [fc.ZERO, fc.scalar(4), fc.C, fc.scalar(7)]}
    std = [(1, 0, 0, 0), (0, 1, 0, 0), (0, 0, 1, 0), (0, 0, 0, 1)]
    lhs = fc.dirac_apply(fc.transport_apply(sample, lam, S), [t0, t1, g2, g3], boosted)
    rhs = fc.transport_apply(fc.dirac_apply(sample, gammas, std), lam, S)
    ok &= fc.field_eq(lhs, rhs)
    check("fin.S3", ok, "Clifford; boost formulas; γ̂⁰ = 10γ⁰ − 4γ¹, γ̂¹ = −2γ⁰ + 10γ¹ (A = 10, B = 2); covariance on the sample field")

if __name__ == "__main__":
    import dcommon
    run(); dcommon.summary(write=False)
