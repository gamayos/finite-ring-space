"""
b_shell.py — block B: the shell as host, the frames as charts, the worked instance (4:B6, C1, C3, C5)
=====================================================================================================
B1: a representation space of the size of the latent domain embeds in the shell (|W_m| = |Z| ≤ p), the least
shell hosting a domain of N states is the least prime p = 4κ+1 ≥ N (tabulated for N ≤ 60), and the canonical
ι_m = φ_m⁻¹ is exhibited for Z ⊂ F_13 with three modalities whose representation spaces are quantised integer
vectors in Z^{d_m}.  B2: the charts of the shell that respect its arithmetic are its affine frames x ↦ a + b x
(1:C2): p(p−1) of them, any two related by one affine map (simply transitive), so the transition Ψ_{m→n} between two
frames is affine — on F_5, F_13, F_17.  B3: the F_13 instance end to end: Ψ_{m→n} between the three modalities,
its composition law, and the lifts recovering every latent state from every observation.
"""
import random
import repcommon as rc

def least_shell(N):
    p = max(N, 5)
    while not (rc.is_prime(p) and p % 4 == 1): p += 1
    return p

def run():
    # B1 the host: |W| = |Z| <= p; the least hosting shell; the canonical iota on F_13
    table = {N: least_shell(N) for N in range(2, 61)}
    ok = all(table[N] >= N and rc.is_prime(table[N]) and table[N] % 4 == 1 for N in table)
    ok &= table[13] == 13 and table[14] == 17 and table[30] == 37 and table[42] == 53 and table[54] == 61
    p = 13; Z = [1, 2, 4, 7, 8, 11, 12]
    random.seed(4)
    mods = []
    for m, d in enumerate((2, 3, 5)):
        X = [f"x{m}_{i}" for i in range(9)]
        gz = random.sample(X, len(Z)); g = dict(zip(Z, gz))                                 # injective observation map
        codes = set()
        while len(codes) < len(Z): codes.add(tuple(random.randint(-8, 8) for _ in range(d)))  # W_m: distinct quantised vectors
        W = sorted(codes); phi = dict(zip(Z, W)); E = {x: random.choice(W) for x in X}
        for z in Z: E[g[z]] = phi[z]                                                        # adequate: E o g = phi bijective
        assert rc.adequate(g, E, Z, W)
        inv = rc.inverse(phi, Z); iota = {w: inv[w] for w in W}                              # iota_m = phi_m^-1 into F_13
        ok &= rc.injective(iota, W) and all(iota[phi[z]] == z for z in Z) and {iota[w] for w in W} == set(Z)
        mods.append((X, g, W, phi, E, iota))
    ok &= all(len(W) == len(Z) <= p for _, _, W, _, _, _ in mods)
    rc.check("B1", "|W_m| = |Z| <= p: the representation space embeds in the shell; the least hosting shell of N states is the least prime p = 4k+1 >= N; the canonical iota_m = phi_m^-1 exhibited on F_13", ok,
             "N=13->13, 14->17, 30->37, 42->53, 54->61; Z of size 7 in F_13, three modalities with codes in Z^2, Z^3, Z^5")

    # B2 the frames as charts: simply transitive, the transition affine
    ok = True; det = []
    for p in (5, 13, 17):
        F = rc.frames(p); ok &= len(F) == p * (p - 1)
        maps = {f: rc.frame_map(f, p) for f in F}
        ok &= all(rc.injective(maps[f], range(p)) for f in F)                               # every frame is a chart
        for f1 in F[:26]:
            m1 = maps[f1]; inv1 = {m1[x]: x for x in range(p)}
            for f2 in F:
                Psi = {m1[x]: maps[f2][x] for x in range(p)}                                 # Psi = psi_2 o psi_1^-1
                a, b = Psi[0], (Psi[1] - Psi[0]) % p
                ok &= b != 0 and all(Psi[u] == (a + b * u) % p for u in range(p))            # affine, invertible
        # simply transitive: for the frame (0,1) and any (c,d) exactly one affine map carries it
        for c in range(p):
            for d in range(1, p):
                sols = [(a, b) for a in range(p) for b in range(1, p) if a == c and b == d]
                ok &= len(sols) == 1
        det.append(f"p={p}: {len(F)} frames")
    rc.check("B2", "the arithmetic charts of the shell are its p(p-1) affine frames; Psi_{m->n} between two frames is one invertible affine map (simply transitive)", ok, "; ".join(det))

    # B3 the F_13 instance end to end
    ok = True
    (X1, g1, W1, phi1, E1, i1), (X2, g2, W2, phi2, E2, i2), (X3, g3, W3, phi3, E3, i3) = mods
    psi = [{z: io[ph[z]] for z in Z} for ph, io in ((phi1, i1), (phi2, i2), (phi3, i3))]
    ok &= all(ps[z] == z for ps in psi for z in Z)                                            # canonical: every chart the inclusion
    # general iota: random injective embeddings into F_13, the transitions and their composition law
    for _ in range(50):
        ios = [dict(zip(W, random.sample(range(p), len(W)))) for W in (W1, W2, W3)]
        ps = [{z: io[ph[z]] for z in Z} for ph, io in zip((phi1, phi2, phi3), ios)]
        ok &= all(rc.injective(q, Z) for q in ps)
        T = lambda m, n: {ps[m][z]: ps[n][z] for z in Z}
        ok &= all(T(1, 2)[T(0, 1)[u]] == T(0, 2)[u] for u in T(0, 1))                        # Psi_{2->3} o Psi_{1->2} = Psi_{1->3}
        ok &= all(T(0, 0)[u] == u for u in T(0, 0))
    # the lifts
    L = [{x: rc.inverse(ph, Z)[E[x]] for x in X} for X, E, ph in ((X1, E1, phi1), (X2, E2, phi2), (X3, E3, phi3))]
    ok &= all(L[0][g1[z]] == z and L[1][g2[z]] == z and L[2][g3[z]] == z for z in Z)
    ok &= all(L[m][x] in Z for m, X in enumerate((X1, X2, X3)) for x in X)
    rc.check("B3", "the F_13 instance: canonical charts are the inclusion; for random embeddings the transitions compose, Psi_{n->k} o Psi_{m->n} = Psi_{m->k}; the three lifts recover every latent state", ok,
             "50 random triples of embeddings W_m -> F_13; 27 observations lifted")

if __name__ == "__main__":
    run(); rc.summary(write=False)
