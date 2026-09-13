"""
b_fractional.py — block B: the fractional family F^[s] = Σ_ℓ g^{−ℓs} Π_ℓ (EXACT, integer-pinned)
=================================================================================================
Paper statements decided (Section 5; master ledger rows 00:C2, 00:C7):

  B1  lem:projectors        Π_ℓ² = Π_ℓ, Π_ℓ Π_m = 0 (ℓ ≠ m), Σ_ℓ Π_ℓ = I, F Π_ℓ = i^ℓ Π_ℓ
  B2  thm:FRC-FrFT          additivity F^[s+r] = F^[s] F^[r] on every pair (s, r) ∈ Z_{4κ}²      (00:C2)
  B3  thm:FRC-FrFT          cardinal values F^[0] = I, F^[κ] = F, F^[2κ] = J, F^[3κ] = F⁻¹, F^[4κ] = I;
                            (F^[1])^κ = F                                                     (00:C2)
  B4  thm:faithful          s ↦ F^[s] injective on Z_{4κ} (p = 5 included: the surviving odd projector
                            carries a faithful character)
  B5  lem:multiplicity      m_ℓ = rank Π_ℓ = dim ker(F − i^ℓ I); m_0 + m_2 = 2κ+1, m_1 + m_3 = 2κ−1;
                            m_0, m_2 ≥ 1; m_1, m_3 ≥ 1 for κ ≥ 2; at p = 5 exactly one of Π_1, Π_3 is 0
  B6  rem:multiplicities    p = 13: g = 2 gives (3,3,4,2) with Tr F = 4, g = 6 gives (4,2,3,3) with Tr F = 9;
                            the vertex relabelling m ↦ um conjugates F(g) to F(g^{u²}) by a permutation
  B7  thm:multiplicity      G = Σ_k g^{k²} = ε(1+i); the two patterns (κ,κ,κ+1,κ−1) / (κ+1,κ−1,κ,κ);
                            ε(g⁻¹) = −ε(g); ε(g^u) = (κ/u) ε(g) for u ≡ 1 (mod 4); the classes equally
                            populated on every shell; the 38 primitive frames of p ∈ {5,13,17,29,37} (and
                            the 16 of p = 41); the table frames with κ ≥ 2 in class ε = +1; p = 5:
                            (2,0,1,1) at g = 2 (ε = −1), (1,1,2,0) at g = 3 (ε = +1)
  B8  thm:multiplicity      the proof's identities: G G* = −2, G² = 2i, Tr F = iG, Tr F² = 2, Tr F³ = iG*,
      (proof)               m_ℓ ≡ ¼ Σ_r i^{−ℓr} Tr F^r (mod p)
  B9  rem:classification    every exponent lift a_ℓ ≡ ℓ (mod 4) is additive with the same cardinal
                            skeleton; the family canonical in the chart g^u with u² ≢ 1 (mod 4κ) does not
                            commute with F — at p = 29, u = 5 (u² = 25 ≢ 1 mod 28)
  B10 rem:gt-covariance     the conjugate reframing (g, i) ↦ (g⁻¹, −i): operator relations, cardinal
      00:C7 (transform      values, additivity and faithfulness hold on the conjugate frame, while the
      layer)                multiplicity tuple flips between the two patterns (chart data); exactly
                            F' = −F⁻¹ and Π'_ℓ = Π_{ℓ+2}

Shells: p = 5, 13, 17, 29, 37, 41; every primitive frame for B7.
"""
import numpy as np
from fcommon import check, Frame, TABLE, SHELLS, primitive_roots, mm, eq, rank_mod_p, matpow, jacobi

def run():
    print("block B — the fractional family")
    frames = {p: Frame(p) for p in SHELLS}

    # B1 — the projectors
    ok = True
    for p in SHELLS:
        f = frames[p]; Pi = f.Pi
        S = np.zeros((f.n, f.n), dtype=np.int64)
        for l in range(4):
            S = (S + Pi[l]) % p
            ok &= eq(mm(Pi[l], Pi[l], p), Pi[l], p)
            ok &= eq(mm(f.F, Pi[l], p), pow(f.i, l, p) * Pi[l], p)
            for m in range(4):
                if m != l:
                    ok &= eq(mm(Pi[l], Pi[m], p), np.zeros_like(S), p)
        ok &= eq(S, f.I(), p)
    check("B1", "Π_ℓ² = Π_ℓ, Π_ℓ Π_m = 0, Σ Π_ℓ = I, F Π_ℓ = i^ℓ Π_ℓ", ok, f"p ∈ {SHELLS}")

    # B2 — additivity on every pair
    ok, npairs = True, 0
    for p in SHELLS:
        f = frames[p]
        fam = [f.frft(s) for s in range(f.n)]
        for s in range(f.n):
            for r in range(f.n):
                ok &= eq(mm(fam[s], fam[r], p), fam[(s + r) % f.n], p); npairs += 1
        f._fam = fam
    check("B2", "F^[s+r] = F^[s] F^[r] on every pair (s, r) of Z_{4κ}", ok, f"{npairs} pairs over p ∈ {SHELLS}")

    # B3 — cardinal values
    ok = True
    for p in SHELLS:
        f = frames[p]; fam = f._fam; k = f.kap
        F3 = matpow(f.F, 3, p)
        ok &= eq(fam[0], f.I(), p) and eq(fam[k], f.F, p) and eq(fam[2 * k], f.J, p) and eq(fam[3 * k], F3, p)
        ok &= eq(mm(F3, f.F, p), f.I(), p)                       # F³ = F⁻¹
        ok &= eq(matpow(fam[1], k, p), f.F, p)
    check("B3", "F^[0] = I, F^[κ] = F, F^[2κ] = J, F^[3κ] = F⁻¹, F^[4κ] = I; (F^[1])^κ = F", ok, f"p ∈ {SHELLS}")

    # B4 — faithfulness
    ok = True
    for p in SHELLS:
        f = frames[p]; fam = f._fam
        ok &= all(not eq(fam[s], f.I(), p) for s in range(1, f.n))
        ok &= len({fam[s].tobytes() for s in range(f.n)}) == f.n
    check("B4", "s ↦ F^[s] is injective on Z_{4κ}: the 4κ members are pairwise distinct (p = 5 included)", ok, f"p ∈ {SHELLS}")

    # B5 — the multiplicity lemma
    ok, det = True, []
    for p in SHELLS:
        f = frames[p]; m = f.mults()
        for l in range(4):
            ok &= (m[l] == f.n - rank_mod_p((f.F - pow(f.i, l, p) * f.I()) % p, p))
        ok &= (m[0] + m[2] == 2 * f.kap + 1 and m[1] + m[3] == 2 * f.kap - 1 and m[0] >= 1 and m[2] >= 1)
        ok &= (m[1] >= 1 and m[3] >= 1) if f.kap >= 2 else ((m[1] == 0) != (m[3] == 0))
        det.append(f"p={p}: {m}")
    check("B5", "m_ℓ = rank Π_ℓ = dim ker(F − i^ℓ I); m_0+m_2 = 2κ+1, m_1+m_3 = 2κ−1; m_0, m_2 ≥ 1; m_1, m_3 ≥ 1 for κ ≥ 2; p = 5: one odd projector vanishes", ok, "; ".join(det))

    # B6 — multiplicities are chart data
    f2, f6 = Frame(13, 2), Frame(13, 6)
    ok = (f2.mults() == (3, 3, 4, 2) and f6.mults() == (4, 2, 3, 3))
    ok &= (int(np.trace(f2.F)) % 13 == 4 and int(np.trace(f6.F)) % 13 == 9)
    ok &= (pow(2, 5, 13) == 6)                                    # same orientation class: 6 = 2^5, 5 ≡ 1 (mod 4)
    nconj = 0
    for p in SHELLS:
        f = frames[p]
        for u in range(1, f.n):
            if np.gcd(u, f.n) != 1:
                continue
            fu = Frame(p, pow(f.g, u * u, p))
            perm = [(u * k) % f.n for k in range(f.n)]
            ok &= eq(fu.F, f.F[np.ix_(perm, perm)], p); nconj += 1
    check("B6", "p = 13: g = 2 gives (3,3,4,2), Tr F = 4; g = 6 gives (4,2,3,3), Tr F = 9; m ↦ um carries F(g) to F(g^{u²}) by a permutation", ok, f"{nconj} relabellings over p ∈ {SHELLS}")

    # B7 — the multiplicity dichotomy on every primitive frame
    ok, det, n38 = True, [], 0
    for p in SHELLS:
        f0 = frames[p]; k = f0.kap
        prims = primitive_roots(p)
        eps = {}
        for g in prims:
            f = Frame(p, g); e = f.epsilon()
            ok &= (e is not None)
            eps[g] = e
            want = (k, k, k + 1, k - 1) if e == 1 else (k + 1, k - 1, k, k)
            ok &= (f.mults() == want)
        for g in prims:
            ok &= (eps[pow(g, p - 2, p)] == -eps[g])                                     # conjugate law
            for u in range(1, f0.n):
                if np.gcd(u, f0.n) == 1 and u % 4 == 1:
                    ok &= (eps[pow(g, u, p)] == jacobi(k, u) * eps[g])                # Jacobi law
        ok &= (2 * sum(1 for g in prims if eps[g] == 1) == len(prims))                 # even split
        if k >= 2:
            ok &= (eps[f0.g] == 1)                                                       # the table frames
        if p != 41:
            n38 += len(prims)
        det.append(f"p={p}: {len(prims)} frames, ε=+1 on {sum(1 for g in prims if eps[g] == 1)}")
    ok &= (n38 == 38)
    ok &= (Frame(5, 2).mults() == (2, 0, 1, 1) and Frame(5, 2).epsilon() == -1)
    ok &= (Frame(5, 3).mults() == (1, 1, 2, 0) and Frame(5, 3).epsilon() == 1)
    check("B7", "G = ε(1+i), the two patterns, ε(g⁻¹) = −ε(g), ε(g^u) = (κ/u) ε(g), classes equally populated; 38 frames of p ∈ {5,…,37} and 16 of p = 41; p = 5: (2,0,1,1) at g = 2, (1,1,2,0) at g = 3",
          ok, "; ".join(det))

    # B8 — the proof's identities
    ok = True
    for p in SHELLS:
        for g in primitive_roots(p):
            f = Frame(p, g)
            G = f.gauss(); Gs = sum(f.gpow(-k * k) for k in range(f.n)) % p
            ok &= (G * Gs % p == p - 2 and G * G % p == 2 * f.i % p)
            tr = [int(np.trace(f.Fpow(r))) % p for r in range(4)]
            ok &= (tr[1] == f.i * G % p and tr[2] == 2 and tr[3] == f.i * Gs % p)
            m = f.mults()
            inv_i = pow(f.i, p - 2, p)
            for l in range(4):
                ok &= (m[l] % p == f.inv4 * sum(pow(inv_i, l * r, p) * tr[r] for r in range(4)) % p)
    check("B8", "G G* = −2, G² = 2i, Tr F = iG, Tr F² = 2, Tr F³ = iG*, m_ℓ ≡ ¼ Σ_r i^{−ℓr} Tr F^r (mod p)", ok, "every primitive frame of the six shells")

    # B9 — classification: exponent lifts and the non-commuting chart
    f = frames[13]; ok = True
    for a in [(0, 1, 2, 3), (0, 5, 2, 3), (4, 1, 6, 7), (0, 1, 2, 11)]:
        U = [sum(f.gpow(-a[l] * s) * f.Pi[l] for l in range(4)) % 13 for s in range(12)]
        ok &= all(eq(mm(U[s], U[r], 13), U[(s + r) % 12], 13) for s in range(12) for r in range(12))
        ok &= eq(U[0], f.I(), 13) and eq(U[3], f.F, 13) and eq(U[6], f.J, 13) and eq(U[9], matpow(f.F, 3, 13), 13)
    f29 = frames[29]; f29u = Frame(29, pow(f29.g, 5, 29))
    ok &= (25 % 28 != 1)
    noncomm = not eq(mm(f29u.frft(1), f29.F, 29), mm(f29.F, f29u.frft(1), 29), 29)
    ok &= noncomm
    scan = []
    for p in SHELLS:
        f0 = frames[p]
        for u in range(1, f0.n):
            if np.gcd(u, f0.n) == 1 and (u * u) % f0.n != 1:
                fu = Frame(p, pow(f0.g, u, p))
                scan.append((p, u, not eq(mm(fu.frft(1), f0.F, p), mm(f0.F, fu.frft(1), p), p)))
    check("B9", "exponent lifts a_ℓ ≡ ℓ (mod 4) are additive with the cardinal skeleton (p = 13); the chart g^5 at p = 29 (u² ≢ 1 mod 28) does not commute with F",
          ok, f"non-commuting at p = 29, u = 5: {noncomm}; all charts with u² ≢ 1 (mod 4κ) on the six shells non-commuting: {all(x[2] for x in scan)} ({len(scan)} charts)")

    # B10 — the conjugate reframing (00:C7, transform layer)
    ok, det = True, []
    for p in SHELLS:
        f = frames[p]; fc = f.conjugate(); k = f.kap
        ok &= (fc.i == (-f.i) % p)
        Finv = matpow(f.F, 3, p)
        ok &= eq(fc.F, (-Finv) % p, p)                                             # F' = −F⁻¹
        ok &= eq(mm(fc.F, fc.F, p), f.J, p) and eq(matpow(fc.F, 4, p), f.I(), p)
        famc = [fc.frft(s) for s in range(f.n)]
        ok &= eq(famc[0], f.I(), p) and eq(famc[k], fc.F, p) and eq(famc[2 * k], f.J, p)
        ok &= all(eq(mm(famc[s], famc[r], p), famc[(s + r) % f.n], p) for s in range(f.n) for r in range(0, f.n, 3))
        ok &= len({M.tobytes() for M in famc}) == f.n
        ok &= all(eq(fc.Pi[l], f.Pi[(l + 2) % 4], p) for l in range(4))                 # Π'_ℓ = Π_{ℓ+2}
        m, mc = f.mults(), fc.mults()
        ok &= (mc == (m[2], m[3], m[0], m[1]) and {m, mc} == {(k, k, k + 1, k - 1), (k + 1, k - 1, k, k)})
        det.append(f"p={p}: {m} ↦ {mc}")
    check("B10", "the conjugate frame (g⁻¹, −i) keeps the operator relations, cardinal values, additivity and faithfulness; its multiplicity tuple is the other pattern; F' = −F⁻¹, Π'_ℓ = Π_{ℓ+2}",
          ok, "; ".join(det))

if __name__ == "__main__":
    import fcommon
    run(); fcommon.summary(write=False)
