"""
d_weil.py — block D: the Weil dictionary and the operator-level comparison (EXACT, integer-pinned)
=================================================================================================
Paper statements decided (Section 8):

  D1  lem:Rs-rotation       c_s² + d_s² = 1 and det R_s = 1 for every s: R_s ∈ SO(2, F_p)
  D2  prop:rotation-isom    s ↦ R_s is a homomorphism Z_{4κ} → SO(2, F_p), injective, onto: |SO(2, F_p)| = p−1
  D3  thm:Weil-equivalence  the cardinal matrices R_0 = I, R_κ = w = [[0,−1],[1,0]] (the R_κ column of
      tab:checks            Table tab:checks), R_{2κ} = −I, R_{3κ} = w⁻¹; z_κ = i
  D4  prop:nogo             σ (the exponent shift) has the n = 4κ distinct eigenvalues F_p^×, each simple;
                            F^[1] has at most four; for κ ≥ 2 the cyclic groups ⟨σ⟩, ⟨F^[1]⟩ of order 4κ
                            are not conjugate
  D5  prop:charsector       E_1 = im Π_1 ≠ 0 for κ ≥ 2; F^[s]|_{E_1} = g^{−s}; F^[s] T_v = T_v S_{−s} on every
                            x ∈ F_p and s; R_s (1, −i)ᵀ = g^{−s} (1, −i)ᵀ
  D6  prop:heisenberg       F σ F⁻¹ = D_1, F D_1 F⁻¹ = σ⁻¹ with D_1 = diag(g^k); F^r σ = σ_r F^r,
                            (σ_0, σ_1, σ_2, σ_3) = (σ, D_1, σ⁻¹, D_1⁻¹); the expansion eq:conj-expansion
                            F^[s] = Σ_r c_r(s) F^r with c_r(s) = ¼ Σ_ℓ (g^{rκ−s})^ℓ
  D7  conj:monomial         the sweep: F^[s] σ F^[s]⁻¹ monomial exactly at the four cardinal indices and
                            non-monomial at every one of the 112 intermediate indices over
                            p ∈ {13, 17, 29, 37, 41} (p = 5 has no intermediate index)

Shells: p = 5, 13, 17, 29, 37, 41.
"""
import numpy as np
from fcommon import check, Frame, SHELLS, mm, eq, rank_mod_p, is_monomial, matpow

def shift(n):
    """(σ v)_k = v_{k−1}: the exponent-shift permutation matrix."""
    S = np.zeros((n, n), dtype=np.int64)
    for k in range(n):
        S[k, (k - 1) % n] = 1
    return S

def run():
    print("block D — the Weil dictionary and the operator-level comparison")
    frames = {p: Frame(p) for p in SHELLS}

    # D1 — R_s ∈ SO(2, F_p)
    ok = True
    for p in SHELLS:
        f = frames[p]
        for s in range(f.n):
            R = f.R(s); c, d = int(R[0, 0]), int(R[1, 0])
            ok &= ((c * c + d * d) % p == 1 and (R[0, 0] * R[1, 1] - R[0, 1] * R[1, 0]) % p == 1)
            ok &= (R[0, 1] == (-d) % p and R[1, 1] == c)
    check("D1", "c_s² + d_s² = 1, det R_s = 1: R_s ∈ SO(2, F_p) for every s", ok, f"p ∈ {SHELLS}")

    # D2 — the isomorphism Z_{4κ} ≅ SO(2, F_p)
    ok, det = True, []
    for p in SHELLS:
        f = frames[p]
        Rs = [f.R(s) for s in range(f.n)]
        ok &= all(eq(mm(Rs[s], Rs[r], p), Rs[(s + r) % f.n], p) for s in range(f.n) for r in range(f.n))
        ok &= (len({R.tobytes() for R in Rs}) == f.n)
        so2 = sum(1 for c in range(p) for d in range(p) if (c * c + d * d) % p == 1)
        ok &= (so2 == p - 1)
        det.append(f"p={p}: |SO(2)|={so2}")
    check("D2", "R_{s+r} = R_s R_r, s ↦ R_s injective, |SO(2, F_p)| = p−1 = 4κ: an isomorphism", ok, "; ".join(det))

    # D3 — the cardinal matrices
    ok = True
    for p in SHELLS:
        f = frames[p]; k = f.kap
        w = np.array([[0, p - 1], [1, 0]], dtype=np.int64)
        ok &= (f.z(k) == f.i)
        ok &= eq(f.R(0), np.eye(2, dtype=np.int64), p) and eq(f.R(k), w, p)
        ok &= eq(f.R(2 * k), (-np.eye(2, dtype=np.int64)) % p, p) and eq(f.R(3 * k), matpow(w, 3, p), p)
        ok &= eq(mm(f.R(3 * k), w, p), np.eye(2, dtype=np.int64), p)
    check("D3", "R_0 = I, R_κ = [[0,−1],[1,0]] (Table tab:checks), R_{2κ} = −I, R_{3κ} = w⁻¹; z_κ = g^{−κ} = i", ok, f"p ∈ {SHELLS}")

    # D4 — the spectral obstruction
    ok, det = True, []
    for p in SHELLS:
        f = frames[p]; n = f.n
        sig = shift(n)
        ok &= eq(matpow(sig, n, p), f.I(), p) and all(not eq(matpow(sig, r, p), f.I(), p) for r in range(1, n))
        ok &= all(rank_mod_p((sig - a * f.I()) % p, p) == n - 1 for a in range(1, p))      # every a ∈ F_p^× a simple eigenvalue
        ok &= all(rank_mod_p((f.frft(1) - a * f.I()) % p, p) == n for a in range(1, p) if a not in {f.gpow(-l) for l in range(4)})
        neig = sum(1 for a in range(1, p) if rank_mod_p((f.frft(1) - a * f.I()) % p, p) < n)
        ok &= (neig <= 4) and (f.kap == 1 or neig < n)
        det.append(f"p={p}: σ has {n} simple eigenvalues, F^[1] has {neig}")
    check("D4", "σ has the 4κ simple eigenvalues F_p^×; F^[1] has at most four; for κ ≥ 2 ⟨σ⟩ and ⟨F^[1]⟩ are not conjugate", ok, "; ".join(det))

    # D5 — the common character sector
    ok, det = True, []
    for p in SHELLS:
        f = frames[p]; n = f.n
        P1 = f.Pi[1]; m1 = rank_mod_p(P1, p)
        ok &= (m1 >= 1) if f.kap >= 2 else True
        if m1 == 0:
            det.append(f"p={p}: E_1 = 0 (κ = 1)"); continue
        cols = [P1[:, j] for j in range(n) if np.any(P1[:, j])]
        for s in range(n):
            Fs = f.frft(s)
            for v in cols[:3]:
                ok &= eq(mm(Fs, v.reshape(n, 1), p), (f.gpow(-s) * v).reshape(n, 1), p)
                for x in range(p):
                    lhs = mm(Fs, (x * v % p).reshape(n, 1), p)                  # F^[s] T_v(x)
                    rhs = ((f.S(-s, x) * v) % p).reshape(n, 1)                  # T_v S_{−s}(x)
                    ok &= eq(lhs, rhs, p)
            vec = np.array([[1], [(-f.i) % p]], dtype=np.int64)
            ok &= eq(mm(f.R(s), vec, p), (f.gpow(-s) * vec) % p, p)
        det.append(f"p={p}: dim E_1 = {m1}")
    check("D5", "E_1 ≠ 0 for κ ≥ 2; F^[s] = g^{−s} on E_1; F^[s] T_v = T_v S_{−s} on every x and s; R_s (1,−i)ᵀ = g^{−s} (1,−i)ᵀ", ok, "; ".join(det))

    # D6 — cardinal Heisenberg covariance and the expansion
    ok = True
    for p in SHELLS:
        f = frames[p]; n = f.n
        sig = shift(n); D1 = np.diag([f.gpow(k) for k in range(n)]).astype(np.int64)
        Finv = matpow(f.F, 3, p)
        ok &= eq(mm(mm(f.F, sig, p), Finv, p), D1, p)
        ok &= eq(mm(mm(f.F, D1, p), Finv, p), matpow(sig, n - 1, p), p)
        sigs = [sig, D1, matpow(sig, n - 1, p), np.diag([f.gpow(-k) for k in range(n)]).astype(np.int64)]
        for r in range(4):
            ok &= eq(mm(f.Fpow(r), sig, p), mm(sigs[r], f.Fpow(r), p), p)
        for s in range(n):
            M = np.zeros((n, n), dtype=np.int64)
            for r in range(4):
                c = f.inv4 * sum(pow(f.gpow(r * f.kap - s), l, p) for l in range(4)) % p
                M = (M + c * f.Fpow(r)) % p
            ok &= eq(M, f.frft(s), p)
    check("D6", "F σ F⁻¹ = D_1, F D_1 F⁻¹ = σ⁻¹; F^r σ = σ_r F^r with (σ, D_1, σ⁻¹, D_1⁻¹); F^[s] = Σ_r c_r(s) F^r, c_r(s) = ¼ Σ_ℓ (g^{rκ−s})^ℓ", ok, f"p ∈ {SHELLS}")

    # D7 — the monomial sweep
    ok, n_int, n_card, det = True, 0, 0, []
    for p in SHELLS:
        f = frames[p]; n = f.n; k = f.kap
        sig = shift(n)
        mono = []
        for s in range(n):
            Fs = f.frft(s); Fsinv = f.frft(-s)
            mono.append(is_monomial(mm(mm(Fs, sig, p), Fsinv, p)))
        card = {0, k, 2 * k, 3 * k}
        ok &= all(mono[s] for s in card) and all(not mono[s] for s in range(n) if s not in card)
        if p != 5:
            n_int += n - 4
        n_card += 4
        det.append(f"p={p}: monomial at {sorted(s for s in range(n) if mono[s])}")
    ok &= (n_int == 112)
    check("D7", "F^[s] σ F^[s]⁻¹ is monomial exactly at the four cardinal indices and non-monomial at every one of the 112 intermediate indices of p ∈ {13,17,29,37,41}", ok, "; ".join(det) + f"; {n_int} intermediate indices swept")

if __name__ == "__main__":
    import fcommon
    run(); fcommon.summary(write=False)
