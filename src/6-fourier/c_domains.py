"""
c_domains.py — block C: representation domains and the coordinate-side zoom (EXACT, integer-pinned)
==================================================================================================
Paper statements decided (Sections 6–7; master ledger row 00:C2):

  C1  def:domain            every F^[s] is invertible (rank 4κ over F_p); its eigenvalues g^{−ℓs} are
                            nonzero, so the meridional bases B_s = F^[s] B_0 are bases
  C2  cor:distinct-domains  the 4κ framed (ordered) bases B_0, …, B_{4κ−1} are pairwise distinct
  C3  rem:ordered-bases     B_{s+2κ} = B_s as unordered sets (F^[s+2κ] = F^[s] J, J a coordinate
                            permutation): the cycle carries exactly 2κ unordered measurement bases
  C4  prop:meridian-scale   S_r(M_m) = M_{m+r} for every (m, r) ∈ Z_{4κ}², as ordered lists  (00:C2)
  C5  cor:effective-step    consecutive entries of M_m differ by g^m; S_{r+(p−1)} = S_r
      rem:framed-rational
  C6  ex:zoom-13            p = 13, g = 2: M_0 … M_3 as printed (steps 1, 2, 4, 8); the no-wrap window of
      thm:zoom, rem:two-    rem:two-layers — with w = π = 6 the listing stays unwrapped for w·2^r < 13, i.e.
      layers                r ≤ 1, and wraps from M_2 on

Shells: p = 5, 13, 17, 29, 37, 41.
"""
import numpy as np
from fcommon import check, Frame, SHELLS, mm, eq, rank_mod_p

def run():
    print("block C — representation domains and the coordinate-side zoom")
    frames = {p: Frame(p) for p in SHELLS}

    # C1 — invertibility
    ok = True
    for p in SHELLS:
        f = frames[p]
        fam = [f.frft(s) for s in range(f.n)]; f._fam = fam
        ok &= all(rank_mod_p(M, p) == f.n for M in fam)
        ok &= all(f.gpow(-l * s) != 0 for s in range(f.n) for l in range(4))
    check("C1", "every F^[s] has full rank 4κ over F_p; the eigenvalues g^{−ℓs} are nonzero", ok, f"p ∈ {SHELLS}")

    # C2 — the framed bases are pairwise distinct
    ok = True
    for p in SHELLS:
        f = frames[p]
        ordered = {tuple(map(tuple, M.T)) for M in f._fam}          # B_s = the ordered columns of F^[s]
        ok &= (len(ordered) == f.n)
    check("C2", "the 4κ framed bases B_s = F^[s] B_0 are pairwise distinct", ok, f"p ∈ {SHELLS}")

    # C3 — unordered bases: the parity identification
    ok, det = True, []
    for p in SHELLS:
        f = frames[p]; k = f.kap
        ok &= all(eq(f._fam[(s + 2 * k) % f.n], mm(f._fam[s], f.J, p), p) for s in range(f.n))
        unordered = {frozenset(map(tuple, M.T)) for M in f._fam}
        ok &= (len(unordered) == 2 * k)
        det.append(f"p={p}: {f.n} framed, {len(unordered)} unordered")
    check("C3", "F^[s+2κ] = F^[s] J, so B_{s+2κ} = B_s as unordered bases: 4κ framed domains, exactly 2κ measurement bases", ok, "; ".join(det))

    # C4 — meridian-scale covariance
    ok, npairs = True, 0
    for p in SHELLS:
        f = frames[p]
        for m in range(f.n):
            Mm = f.meridian(m)
            for r in range(f.n):
                ok &= (tuple(f.S(r, x) for x in Mm) == f.meridian(m + r)); npairs += 1
    check("C4", "S_r(M_m) = M_{m+r} on every (m, r), as ordered lists", ok, f"{npairs} pairs over p ∈ {SHELLS}")

    # C5 — the effective step and the periodicity
    ok = True
    for p in SHELLS:
        f = frames[p]
        for m in range(f.n):
            Mm = f.meridian(m)
            ok &= all((Mm[a + 1] - Mm[a]) % p == f.gpow(m) for a in range(f.pi))
        ok &= all(f.S(r + p - 1, x) == f.S(r, x) for r in range(f.n) for x in range(p))
    check("C5", "consecutive entries of M_m differ by the effective step g^m; S_{r+(p−1)} = S_r", ok, f"p ∈ {SHELLS}")

    # C6 — the ladder at p = 13 and the no-wrap window
    f = frames[13]
    ladder = {0: (0, 1, 2, 3, 4, 5, 6), 1: (0, 2, 4, 6, 8, 10, 12), 2: (0, 4, 8, 12, 3, 7, 11), 3: (0, 8, 3, 11, 6, 1, 9)}
    ok = (f.g == 2 and f.i == 5 and f.pi == 6 and all(f.meridian(m) == ladder[m] for m in ladder))
    ok &= all(f.gpow(m) == 2 ** m for m in range(4))
    w = f.pi
    unwrapped = [m for m in range(f.n) if w * 2 ** m < 13]
    wraps = [m for m in range(4) if any(a * 2 ** m >= 13 for a in range(w + 1))]
    ok &= (unwrapped == [0, 1] and wraps == [2, 3])
    check("C6", "p = 13, g = 2: M_0…M_3 = the printed ladder at steps 1, 2, 4, 8; the no-wrap window w·g^r < p with w = π = 6 holds for r ≤ 1 and the listing wraps from M_2", ok, f"unwrapped meridians {unwrapped}, wrapping {wraps}")

if __name__ == "__main__":
    import fcommon
    run(); fcommon.summary(write=False)
