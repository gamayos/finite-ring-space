"""
a_adequacy.py — block A: adequacy and the Universal Subspace Theorem on every finite model (4:B4, B5, C1–C4)
=============================================================================================================
Sections 3–4 of the paper, decided by exhaustion: the latent domain Z, the observations X and the representation
spaces W are small sets, and every map g : Z → X, E : X → W is enumerated.  A1: adequacy (E ∘ g a bijection
Z → W, Definition 2) forces g injective, and the adequate E are counted (|Z|! · |W|^{|X|−|Z|} for injective g, none
otherwise).  A2: for every pair of adequate representations of one g, the transition ψ = φ₂ ∘ φ₁⁻¹ is the unique
bijection W₁ → W₂ with E₂ ∘ g = ψ ∘ E₁ ∘ g; E₂ = ψ ∘ E₁ on all of X exactly when the two agree off g(Z), which
fails in some configurations with X ⊋ g(Z) (counted).  A3: Lemma 1's set-level form, ψ(E₁(X)) = E₂(X), on every
pair.  A4: Theorem 1 (i)–(iii) over every injective ι_m : W_m → U = F_5 — the charts ψ_m are injective, the
transitions Ψ_{m→n} are bijections of the images composing as ψ_k ∘ ψ_m⁻¹, and the canonical ι_m = φ_m⁻¹ makes every
chart the inclusion.  A5: Corollaries 1–2 — the lifts L_m = φ_m⁻¹ ∘ E_m invert g_m, are the unique preimage, and
agree across modalities on every latent state.
"""
import itertools, math
import repcommon as rc

def models(nZ, nX, nW):
    Z = list(range(nZ)); X = [f"x{i}" for i in range(nX)]; W = [f"w{i}" for i in range(nW)]
    return Z, X, W

def run():
    # A1 adequacy forces g injective; the count of adequate E for a given g
    ok = True; det = []; total = 0
    for nZ, nX in [(1, 1), (1, 2), (2, 2), (2, 3), (3, 3), (3, 4), (2, 4)]:
        Z, X, W = models(nZ, nX, nZ)
        for g in rc.maps(Z, X):
            n_ad = sum(rc.adequate(g, E, Z, W) for E in rc.maps(X, W)); total += 1
            if rc.injective(g, Z):
                ok &= n_ad == math.factorial(nZ) * nZ ** (nX - nZ)
            else:
                ok &= n_ad == 0
        det.append(f"|Z|={nZ},|X|={nX}: {nX**nZ} maps g")
    rc.check("A1", "adequacy (E o g bijective Z -> W) forces g injective; adequate E number |Z|! |W|^(|X|-|Z|) for injective g, 0 otherwise", ok,
             f"{total} observation maps over 7 model sizes; " + "; ".join(det[:3]))

    # A2 the transition psi = phi_2 o phi_1^{-1}: unique bijection with E2 o g = psi o E1 o g; E2 = psi o E1 off g(Z) not forced
    ok = True; det = []; n_pairs = 0; n_off = 0; n_total_off = 0
    for nZ, nX in [(2, 2), (2, 3), (3, 3), (3, 4)]:
        Z, X, W1 = models(nZ, nX, nZ); W2 = [f"v{i}" for i in range(nZ)]
        for g in rc.maps(Z, X):
            if not rc.injective(g, Z): continue
            ads1 = [E for E in rc.maps(X, W1) if rc.adequate(g, E, Z, W1)]
            ads2 = [E for E in rc.maps(X, W2) if rc.adequate(g, E, Z, W2)]
            for E1 in ads1:
                phi1 = {z: E1[g[z]] for z in Z}; inv1 = rc.inverse(phi1, Z)
                for E2 in ads2:
                    n_pairs += 1
                    phi2 = {z: E2[g[z]] for z in Z}
                    psi = {w: phi2[inv1[w]] for w in W1}
                    ok &= len(set(psi.values())) == nZ                                   # a bijection W1 -> W2
                    ok &= all(E2[g[z]] == psi[E1[g[z]]] for z in Z)                      # E2 o g = psi o E1 o g
                    others = [q for q in rc.maps(W1, W2) if all(E2[g[z]] == q[E1[g[z]]] for z in Z)]
                    ok &= others == [psi]                                                # unique
                    if nX > nZ:
                        n_total_off += 1
                        if any(E2[x] != psi[E1[x]] for x in X): n_off += 1               # off g(Z) the equation can fail
        det.append(f"|Z|={nZ},|X|={nX}")
    ok &= n_off > 0
    rc.check("A2", "psi = phi_2 o phi_1^-1 is the unique bijection W1 -> W2 with E2 o g = psi o E1 o g; E2 = psi o E1 on all of X only when X = g(Z)", ok,
             f"{n_pairs} pairs of adequate representations; off g(Z) the equation fails in {n_off} of {n_total_off} pairs with X != g(Z)")

    # A3 Lemma 1 at the level of images: psi(E1(X)) = E2(X) = W2
    ok = True; n = 0
    for nZ, nX in [(2, 3), (3, 4)]:
        Z, X, W1 = models(nZ, nX, nZ); W2 = [f"v{i}" for i in range(nZ)]
        for g in rc.maps(Z, X):
            if not rc.injective(g, Z): continue
            ads1 = [E for E in rc.maps(X, W1) if rc.adequate(g, E, Z, W1)]
            ads2 = [E for E in rc.maps(X, W2) if rc.adequate(g, E, Z, W2)]
            for E1 in ads1:
                inv1 = rc.inverse({z: E1[g[z]] for z in Z}, Z)
                for E2 in ads2:
                    psi = {w: E2[g[inv1[w]]] for w in W1}; n += 1
                    ok &= {psi[E1[x]] for x in X} == {E2[x] for x in X} == set(W2)
    rc.check("A3", "Lemma 1 as images: psi(E1(X)) = E2(X) = W2 for every pair of adequate representations", ok, f"{n} pairs")

    # A4 Theorem 1 (i)-(iii): every injective iota_m : W_m -> U = F_5; the canonical iota
    p = 5; U = list(range(p)); Z = [0, 2, 3]; X1 = ["a", "b", "c", "d"]; X2 = ["s", "t", "u"]
    g1 = {0: "b", 2: "d", 3: "a"}; g2 = {0: "t", 2: "s", 3: "u"}
    W1 = ["w0", "w1", "w2"]; W2 = ["v0", "v1", "v2"]
    E1 = {"a": "w2", "b": "w0", "c": "w0", "d": "w1"}; E2 = {"s": "v1", "t": "v2", "u": "v0"}
    assert rc.adequate(g1, E1, Z, W1) and rc.adequate(g2, E2, Z, W2)
    phi1 = {z: E1[g1[z]] for z in Z}; phi2 = {z: E2[g2[z]] for z in Z}
    ok = True; n = 0
    iotas = lambda W: [dict(zip(W, perm)) for perm in itertools.permutations(U, len(W))]
    for i1 in iotas(W1):
        psi1 = {z: i1[phi1[z]] for z in Z}
        ok &= rc.injective(psi1, Z)                                                          # (i)
        for i2 in iotas(W2):
            psi2 = {z: i2[phi2[z]] for z in Z}; n += 1
            img1 = {psi1[z] for z in Z}; Psi = {psi1[z]: psi2[z] for z in Z}                  # (ii) Psi_{1->2} = psi2 o psi1^-1
            ok &= len(Psi) == len(Z) and set(Psi) == img1 and set(Psi.values()) == {psi2[z] for z in Z}
            back = {psi2[z]: psi1[z] for z in Z}
            ok &= all(back[Psi[u]] == u for u in img1)                                       # Psi_{2->1} o Psi_{1->2} = id
    inv1, inv2 = rc.inverse(phi1, Z), rc.inverse(phi2, Z)
    can1 = {w: inv1[w] for w in W1}; can2 = {w: inv2[w] for w in W2}                          # iota_m = phi_m^{-1}, into U
    ok &= all(can1[phi1[z]] == z and can2[phi2[z]] == z for z in Z)                         # (iii) psi_m = inclusion
    ok &= {can1[w] for w in W1} == {can2[w] for w in W2} == set(Z)
    rc.check("A4", "Theorem 1: psi_m = iota_m o phi_m injective for every injective iota_m; Psi_{m->n} a bijection of the images with inverse Psi_{n->m}; iota_m = phi_m^-1 makes every chart the inclusion of Z", ok,
             f"Z of size 3 in F_5, two modalities, {n} pairs of embeddings (60 x 60)")

    # A5 Corollaries 1-2: the lifts
    L1 = {x: inv1[E1[x]] for x in X1}; L2 = {x: inv2[E2[x]] for x in X2}
    ok = all(L1[g1[z]] == z and L2[g2[z]] == z for z in Z)                                    # L_m o g_m = id
    ok &= all((E1[x] == phi1[z]) == (L1[x] == z) for x in X1 for z in Z)                     # L_m x the unique z with E_m x = phi_m z
    ok &= all(L1[g1[z]] == L2[g2[z]] for z in Z)                                             # cross-modal consistency
    ok &= L1["c"] == 0 and E1["c"] == E1["b"]                                                 # an unresolved observation lifts to the state it encodes
    rc.check("A5", "Corollary 1: L_m = phi_m^-1 o E_m inverts g_m and L_m x is the unique z with E_m x = phi_m z; Corollary 2: L_m(g_m z) = L_n(g_n z), psi o L_m o g_m = psi", ok,
             "the F_5 instance; the observation c (not in g_1(Z)) lifts to the state its code names")

if __name__ == "__main__":
    run(); rc.summary(write=False)
