## Quarter-turn transport (Lemma lem:transport): for an embedded cycle C_n of
## the phase cycle of F_P (n = 4*kappa_n dividing P-1 = 4*kappa), the winding
## reduction Pi: g^a -> g_n^{a mod n} carries the ambient quarter-turn
## i = g^{-kappa} onto the shell label i_n = g_n^{-kappa_n} iff
## kappa = kappa_n (mod n); onto the conjugate -i_n iff kappa = -kappa_n
## (mod n); and onto a half-turn-preserving image iff kappa = +-kappa_n
## (mod n). kappa mod 4 is the coarsest transport invariant.
## Instances (all exact, criterion checked against the computed elements):
##   (K1) F_157 -> C_12: kappa = 39 = 3 = kappa_12 (mod 12): faithful;
##   (K2) F_421 -> C_12: 105 = 9 = -3 (mod 12): conjugate;
##   (K3) F_421 -> C_60 and C_28: both conjugate (105 = -15 mod 60; = -7 mod 28);
##   (K4) F_421 -> C_4 = Q4: faithful (105 = 1 mod 4);
##   (K5) F_641 -> C_40: 160 = 0 (mod 40): Pi(i) = 1, even the half-turn fails;
##   (K6) F_157 -> C_52: 39 = -13 (mod 52): conjugate.
def report(label, ok):
    print(('PASS ' if ok else 'FAIL ') + label)
    assert ok, label

def order(a, mod):
    x, k = 1, 0
    while True:
        x, k = (x*a) % mod, k+1
        if x == 1:
            return k

def transport(P, g, n):
    N = P - 1
    kap, kn = N // 4, n // 4
    assert P % 4 == 1 and N % n == 0 and n % 4 == 0 and order(g, P) == N
    gS = pow(g, N//n, P)
    i_n = pow(gS, n - kn, P)                 # i_n = gS^{-kappa_n}
    Pi_i = pow(gS, (N - kap) % n, P)         # Pi(i) = gS^{-kappa mod n}
    faithful = kap % n == kn % n
    conjugate = kap % n == (n - kn) % n
    half = kap % (n//2) == kn % (n//2)
    okA = (Pi_i == i_n) == faithful
    okB = (Pi_i == P - i_n) == conjugate
    okC = ((Pi_i * Pi_i) % P == P - 1) == half
    return okA and okB and okC, faithful, conjugate, half, Pi_i

ok, f, c, h, _ = transport(157, 5, 12)
report('K1: F_157 -> C_12: 39 = 3 = kappa_12 (mod 12): Pi(i) = i_12, faithful',
       ok and f and not c)
ok, f, c, h, _ = transport(421, 2, 12)
report('K2: F_421 -> C_12: 105 = 9 = -3 (mod 12): Pi(i) = -i_12, conjugate',
       ok and (not f) and c and h)
o1 = transport(421, 2, 60); o2 = transport(421, 2, 28)
report('K3: F_421 -> C_60, C_28: both conjugate charts',
       o1[0] and (not o1[1]) and o1[2] and o2[0] and (not o2[1]) and o2[2])
ok, f, c, h, _ = transport(421, 2, 4)
report('K4: F_421 -> C_4 = Q4: 105 = 1 (mod 4): faithful', ok and f)
ok, f, c, h, Pi_i = transport(641, 3, 40)
report('K5: F_641 -> C_40: 160 = 0 (mod 40): Pi(i) = 1, half-turn fails',
       ok and (not f) and (not c) and (not h) and Pi_i == 1)
ok, f, c, h, _ = transport(157, 5, 52)
report('K6: F_157 -> C_52: 39 = -13 (mod 52): Pi(i) = -i_52, conjugate',
       ok and (not f) and c and h)
print('transport: all checks passed')
