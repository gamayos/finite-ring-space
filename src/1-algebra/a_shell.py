"""
a_shell.py — block A: the shell, its frame and the orbital complex (EXACT, integer-pinned)
==========================================================================================
Paper statements decided (Sections 2–3; ledger predicates 1:B2–B4, 1:C2, 1:C4):

  A1  thm:symmetric-completeness   the fourth roots of unity are Q4 = {1, i, −1, −i}; under the Klein four-group
      (1:B2)                       ⟨x ↦ −x, x ↦ x⁻¹⟩, Q4 is the union of the two size-2 orbits {±1}, {±i}, and
                                   F_p^× \\ Q4 splits into exactly κ−1 orbits of size 4; for p ≡ 3 (mod 4) no i
  A2  (1:B3)                       i = −g^κ satisfies i² = −1 for every primitive root g; {−g^κ, g^κ} are the two
                                   square roots of −1; on F_13 with g = 2, i = 5
  A3  def:framed-field,            φ_{a,b}(x) = a + bx is a ring isomorphism (F_p, +, ·) → (F_p, ⊕, ⊗) on every
      lem:affine-invariance (1:B4) frame (a, b), b ≠ 0; the unit of the relabelled field is a + b, and b is the
                                   unit only when a = 0
  A4  prop:frame-group (1:C2)      ⟨T_a, S_m⟩ = Aff(F_p) of order p(p−1), simply transitive on the frames
  A5  def:orbit-sphere (1:C4)      M_n(a) = M_{n+2κ}(−a), L_a(m) = L_{−a}(m+2κ); p−1 distinct meridian lists in
                                   2κ great circles; 2κ latitude pairs; vertex count (p−1)²/2 + 1

Shells: p ∈ {5, 13, 17, 29, 37, 41, 173} for A1–A2; p ∈ {13, 17} for A3–A5 (exhaustive over frames and pairs).
"""
try:
    from .algcommon import check, SHELLS, CONTROLS, primitive_roots, kappa, quarter_turn, sqrt_neg_one
except ImportError:                       # run in place (python3 a_shell.py)
    from algcommon import check, SHELLS, CONTROLS, primitive_roots, kappa, quarter_turn, sqrt_neg_one

def klein_orbits(p):
    seen, orbits = set(), []
    for x in range(1, p):
        if x in seen: continue
        inv = pow(x, -1, p)
        orb = {x, (-x) % p, inv, (-inv) % p}
        seen |= orb; orbits.append(orb)
    return orbits

def run():
    print("block A — the shell, its frame and the orbital complex")

    # A1 — symmetry completeness
    ok, det = True, []
    for p in SHELLS:
        k = kappa(p); orbits = klein_orbits(p)
        Q4 = {1, p - 1} | set(sqrt_neg_one(p))
        small = [o for o in orbits if len(o) < 4]
        big = [o for o in orbits if len(o) == 4]
        ok &= (len(Q4) == 4 and set().union(*small) == Q4 and sorted(len(o) for o in small) == [2, 2])
        ok &= (len(big) == k - 1 and len(big) + len(small) == k + 1)
        ok &= all(pow(x, 4, p) == 1 for x in Q4) and sum(1 for x in range(1, p) if pow(x, 4, p) == 1) == 4
        det.append(f"p={p}: Q4={sorted(Q4)}, {len(big)} orbits of size 4 = κ−1")
    for p in CONTROLS:
        orbits = klein_orbits(p)
        ok &= (sqrt_neg_one(p) == [] and sorted(len(o) for o in orbits) == [2] + [4] * ((p - 3) // 4))
    # predicate 1:B2
    check("A1", "Q4 = {1,i,−1,−i} the unique order-4 subgroup, two Klein orbits of size 2, κ−1 orbits of size 4; no i for p ≡ 3 (mod 4)",
          ok, "; ".join(det) + f"; controls p ∈ {CONTROLS}")

    # A2 — the oriented quarter-turn
    ok, det = True, []
    for p in SHELLS:
        k = kappa(p); roots = set(sqrt_neg_one(p)); n = 0
        for g in primitive_roots(p):
            i = quarter_turn(p, g)
            ok &= ((i * i) % p == p - 1) and ({i, pow(g, k, p)} == roots) and (pow(g, 2 * k, p) == p - 1); n += 1
        det.append(f"p={p}: {n} primitive roots")
    ok &= (quarter_turn(13, 2) == 5)
    # predicate 1:B3
    check("A2", "i = −g^κ, i² = −1 for every primitive root; {−g^κ, g^κ} the two square roots of −1; g^{2κ} = −1; F_13, g = 2: i = 5",
          ok, "; ".join(det))

    # A3 — the affine frame: ring isomorphism, the unit a + b
    ok, n = True, 0
    for p in [13, 17]:
        for a in range(p):
            for b in range(1, p):
                inv = lambda X: ((X - a) * pow(b, -1, p)) % p
                phi = lambda x: (a + b * x) % p
                oplus = lambda X, Y: (a + b * (inv(X) + inv(Y))) % p
                otimes = lambda X, Y: (a + b * (inv(X) * inv(Y))) % p
                ok &= all(phi((x + y) % p) == oplus(phi(x), phi(y)) and phi((x * y) % p) == otimes(phi(x), phi(y))
                          for x in range(p) for y in range(p))
                ok &= (len({phi(x) for x in range(p)}) == p)
                ok &= all(otimes((a + b) % p, y) == y for y in range(p))
                ok &= ((a == 0) == all(otimes(b, y) == y for y in range(p)))
                n += 1
    # predicate 1:B4
    check("A3", "φ_{a,b} = a + bx a ring isomorphism onto (F_p, ⊕, ⊗) on every frame; unit a + b; b the unit iff a = 0",
          ok, f"{n} frames on p ∈ {{13, 17}}, all pairs (x, y)")

    # A4 — the frame group
    ok, det = True, []
    for p in [13, 17]:
        frames = [(a, b) for a in range(p) for b in range(1, p)]
        comp = lambda f, g: ((f[0] + f[1] * g[0]) % p, (f[1] * g[1]) % p)     # f∘g as affine maps x ↦ a + b x
        ok &= (len(frames) == p * (p - 1))
        ok &= all(comp(f, g) in set(frames) for f in frames for g in frames)  # closure
        # simple transitivity: for each (φ, φ') exactly one ψ with ψ∘φ = φ'
        cnt = 0
        for f in frames:
            for f2 in frames:
                sols = [psi for psi in frames if comp(psi, f) == f2]
                ok &= (len(sols) == 1); cnt += 1
        det.append(f"p={p}: |Aff| = {len(frames)} = p(p−1), {cnt} frame pairs, one carrier each")
    # predicate 1:C2
    check("A4", "⟨T_a, S_m⟩ = Aff(F_p), order p(p−1), simply transitive on the frames (a, b)", ok, "; ".join(det))

    # A5 — the orbital complex: involutions and counts
    ok, det = True, []
    for p in [13, 17]:
        k = kappa(p); g = primitive_roots(p)[0]; n2 = 2 * k
        M = lambda n, a: (a * pow(g, n, p)) % p
        L = lambda a, m: (a * pow(g, m, p)) % p
        ok &= all(M(n, a) == M(n + n2, (-a) % p) for n in range(p - 1) for a in range(p))
        ok &= all(L(a, m) == L((-a) % p, m + n2) for a in range(1, p) for m in range(p - 1))
        mer = {tuple(M(n, a) for a in range(p)) for n in range(p - 1)}
        circles = {frozenset({tuple(M(n, a) for a in range(p)), tuple(M(n + n2, a) for a in range(p))}) for n in range(p - 1)}
        latpairs = {frozenset({tuple(L(a, m) for m in range(p - 1)), tuple(L((-a) % p, m) for m in range(p - 1))}) for a in range(1, p)}
        ok &= (len(mer) == p - 1 and len(circles) == 2 * k and len(latpairs) == 2 * k)
        V = (p - 1) * (2 * k) + 1
        ok &= (V == (p - 1) ** 2 // 2 + 1)
        det.append(f"p={p}: {len(mer)} meridian lists, {len(circles)} great circles, {len(latpairs)} latitude pairs, |V| = {V}")
    # predicate 1:C4
    check("A5", "M_n(a) = M_{n+2κ}(−a), L_a(m) = L_{−a}(m+2κ); p−1 meridian lists in 2κ circles; 2κ latitude pairs; |V| = (p−1)²/2 + 1",
          ok, "; ".join(det))

if __name__ == "__main__":
    import algcommon
    run(); algcommon.summary(write=False)
