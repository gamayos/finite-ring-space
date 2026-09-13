"""
a_shell.py — block A: the frame datum and the shell Fourier operator (EXACT, integer-pinned)
==========================================================================================
Paper statements decided (Sections 3–4; master ledger rows 00:C2, 00:C14):

  A1  §3 shell data, tab:checks   p = 4κ+1, the generator g of Table tab:checks is the smallest primitive
                                   root, i = −g^κ = g^{−κ} = g^{3κ}, i² ≡ −1, π = 2κ, 2π ≡ −1, g^π ≡ −1,
                                   −π ≡ 2⁻¹, e = g^i; the table's (κ, g, i) on all six shells
  A2  §3 (Euler identity)          e^{iπ} = g^{2κ(i mod 2)} ≡ −1 exactly when the quarter-turn residue i is
      00:C14                       odd; the conjugate reframing (g, i) ↦ (g⁻¹, −i) toggles the parity, so
                                   exactly one member of each conjugate pair carries e^{iπ} ≡ −1 — on every
                                   primitive frame of the six shells; anchor F_13(t;0,1,2): i = 5, 6^{iπ} ≡ −1
  A3  rem:gt-covariance            the relabelling g' = g^u, u ∈ Z_{4κ}^×: i' = i iff u ≡ 1 (mod 4), i' = −i
                                   iff u ≡ 3 (mod 4); e' = g^{ui} ≠ e whenever i(u−1) ≢ 0 (mod 4κ), as at
                                   p = 13, g = 2, u = 5: e' = 2 ≠ 6 = e
  A4  lem:W-square, prop:F-cycle   W² = −J, (iW)² = J, (iW)⁴ = I on the six shells (the three boolean
      tab:checks; 00:C2            columns of Table tab:checks)
  A5  rem:unitary-norm             the square roots of 1/n = −1 in F_p are exactly ±i; (cW)² = J iff c = ±i
  A6  lem:JF-decomp                WJ = JW, FJ = JF; dim V⁺ = 2κ+1, dim V⁻ = 2κ−1

Shells: p = 5, 13, 17, 29, 37, 41 (Table tab:checks), every primitive frame of each for A2 and A3.
"""
import numpy as np
from fcommon import check, Frame, TABLE, SHELLS, primitive_roots, mm, eq, rank_mod_p, matpow

def run():
    print("block A — the frame datum and the shell Fourier operator")
    frames = {p: Frame(p) for p in SHELLS}

    # A1 — the shell data and the table
    ok, rows = True, []
    for p, kap, g, i in TABLE:
        f = frames[p]
        ok &= (p == 4 * kap + 1 and f.kap == kap and f.g == g and f.i == i)
        ok &= (f.i == (-pow(g, kap, p)) % p == pow(g, p - 1 - kap, p) == pow(g, 3 * kap, p))
        ok &= (f.i * f.i % p == p - 1)
        ok &= (f.pi == 2 * kap and (2 * f.pi) % p == p - 1 and pow(g, f.pi, p) == p - 1)
        ok &= ((-f.pi) % p == f.inv2)
        ok &= (f.e == pow(g, i, p))
        rows.append(f"F_{p}(κ={kap}, g={g}, i={i}, e={f.e})")
    check("A1", "p = 4κ+1, g the smallest primitive root, i = −g^κ = g^{−κ}, i² ≡ −1, π = 2κ, 2π ≡ −1, g^π ≡ −1, −π ≡ 2⁻¹, e = g^i; Table tab:checks (κ, g, i)",
          ok, "; ".join(rows))

    # A2 — the Euler identity on the odd member (00:C14)
    ok, n_frames, n_carry = True, 0, 0
    for p in SHELLS:
        for g in primitive_roots(p):
            f = Frame(p, g)
            euler = pow(f.e, f.i * f.pi, p)                       # e^{iπ} = (g^i)^{iπ}
            ok &= (euler == pow(g, f.pi * (f.i % 2), p))          # = g^{2κ (i mod 2)}
            ok &= ((euler == p - 1) == (f.i % 2 == 1))            # ≡ −1 iff i odd
            fc = f.conjugate()
            ok &= (fc.i == (-f.i) % p and fc.i % 2 != f.i % 2)    # the conjugate toggles the parity
            carries_c = pow(fc.e, fc.i * fc.pi, p) == p - 1
            ok &= ((euler == p - 1) != carries_c)                 # exactly one member of the pair
            n_frames += 1; n_carry += (euler == p - 1)
    f13 = frames[13]
    ok &= (f13.i == 5 and f13.e == 6 and pow(6, 5 * 6, 13) == 12 and pow(6, 6, 13) == 12)
    check("A2", "e^{iπ} = g^{2κ(i mod 2)} ≡ −1 exactly on the odd quarter-turn; the conjugate reframing toggles it, one member of each pair carries it",
          ok, f"{n_frames} primitive frames of p ∈ {SHELLS}, {n_carry} carry e^{{iπ}} ≡ −1 (one per conjugate pair); F_13(t;0,1,2): i = 5, e = 6, 6^{{30}} = 6^{{6}} ≡ −1")

    # A3 — the u-relabelling
    ok = True
    for p in SHELLS:
        f = frames[p]
        for u in range(1, f.n):
            if np.gcd(u, f.n) != 1:
                continue
            fu = Frame(p, pow(f.g, u, p))
            ok &= (fu.i == f.i) if u % 4 == 1 else (fu.i == (-f.i) % p)
            if u % 4 == 1:
                ok &= (fu.e == pow(f.g, u * f.i, p))
                ok &= ((fu.e != f.e) == ((f.i * (u - 1)) % f.n != 0))
    f5 = Frame(13, pow(2, 5, 13))
    ok &= (f5.i == f13.i and f5.e == 2 and f13.e == 6 and pow(6, 5, 13) == 2)
    check("A3", "g' = g^u: the quarter-turn flips only on u ≡ 3 (mod 4); e' = g^{ui} ≠ e iff i(u−1) ≢ 0 (mod 4κ); at p = 13, u = 5: e' = 2 ≠ 6",
          ok, "every unit u of Z_{4κ} on the six shells; F_13, g' = 2^5 = 6: i' = 5, e' = 6^5 = 2")

    # A4 — the operator identities of Table tab:checks (00:C2)
    ok, det = True, []
    for p in SHELLS:
        f = frames[p]
        W2 = mm(f.W, f.W, p); F2 = mm(f.F, f.F, p); F4 = mm(F2, F2, p)
        a, b, c = eq(W2, (-f.J) % p, p), eq(F2, f.J, p), eq(F4, f.I(), p)
        ok &= a and b and c
        det.append(f"p={p}: {a},{b},{c}")
    check("A4", "W² = −J, (iW)² = J, (iW)⁴ = I on the six shells of Table tab:checks", ok, "; ".join(det))

    # A5 — the unitary normalisation read in the field
    ok = True
    for p in SHELLS:
        f = frames[p]
        roots = sorted(c for c in range(p) if c * c % p == p - 1)
        ok &= (roots == sorted([f.i, (-f.i) % p]))
        ok &= ((1 * pow(f.n, p - 2, p)) % p == p - 1)                        # 1/n = −1
        for c in range(1, p):
            ok &= (eq(mm(c * f.W % p, c * f.W % p, p), f.J, p) == (c in roots))
    check("A5", "the square roots of 1/n ≡ −1 in F_p are exactly ±i, the two unitary normalisations of W: (cW)² = J iff c = ±i", ok, f"every c ∈ F_p^× tested on p ∈ {SHELLS}")

    # A6 — the symmetric/antisymmetric decomposition
    ok, det = True, []
    for p in SHELLS:
        f = frames[p]
        ok &= eq(mm(f.W, f.J, p), mm(f.J, f.W, p), p) and eq(mm(f.F, f.J, p), mm(f.J, f.F, p), p)
        dplus = f.n - rank_mod_p((f.J - f.I()) % p, p); dminus = f.n - rank_mod_p((f.J + f.I()) % p, p)
        ok &= (dplus == 2 * f.kap + 1 and dminus == 2 * f.kap - 1)
        det.append(f"p={p}: dim V⁺={dplus}, V⁻={dminus}")
    check("A6", "WJ = JW, FJ = JF; dim V⁺ = 2κ+1, dim V⁻ = 2κ−1", ok, "; ".join(det))

if __name__ == "__main__":
    import fcommon
    run(); fcommon.summary(write=False)
