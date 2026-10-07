#!/usr/bin/env python3
"""Unified counting checks (round-01, W-J / W-N): exact integer arithmetic only.

1. Christoffel registration pattern: at rational rate a/b the drive registers
   exactly a advances per recurrence b, with gaps taking exactly two values
   floor(b/a), ceil(b/a) of mean b/a  (Lemma isopair's tally identity).
2. Censored geometric identity (the [approx] chart of the gap spectrum),
   checked symbolically over the rationals.
3. The readout worked instance of the quantum paper (Omega=641, g=3):
   s_4 = 114, R_4 = 23/54 and 2/27, largest-remainder allocation 35+34+6+6 = 81.
4. Negative control: naive prefix counts violate unit discrepancy already at
   B = 108 (Kesten), so the theorem is stated over complete recurrences.
5. Per-stratum split at B = 2, 3 on Omega = 641: over the complete dial
   recurrence the outcome-string tallies equal |dial| times the
   Galois-symmetric multinomial coefficients of (W+ + W-)^B = 4^B,
   with W(j) = 2 +/- r_j the dial-shifted Bell weights, exactly in Z[sqrt(2)]
   and as residues mod 641.
"""
from fractions import Fraction
from itertools import product

ok = True
def chk(name, cond):
    global ok
    ok = ok and bool(cond)
    print(('PASS ' if cond else 'FAIL ') + name)

# ---- 1. Christoffel words: five (a,b) pairs incl. 23/54 ----
for a, b in ((23, 54), (2, 27), (1, 5), (3, 8), (7, 12)):
    marks = [((k + 1) * a) // b - (k * a) // b for k in range(b)]  # 0/1 registration word
    regs = sum(marks)
    gaps, run = [], 0
    idx = [k for k in range(b) if marks[k] == 1]
    gaps = [((idx[(i + 1) % len(idx)] - idx[i]) % b) or b for i in range(len(idx))]
    gapset = sorted(set(gaps))
    chk(f"christoffel a/b={a}/{b}: a regs per recurrence, two-valued gaps",
        regs == a and set(gapset) <= {b // a, -(-b // a)} and
        Fraction(sum(gaps), len(gaps)) == Fraction(b, a))

# ---- 2. censored identity E[min(G,T)] = (1-(1-q)^T)/q over Q ----
q = Fraction(1, 7); T = 11
lhs = sum(k * q * (1 - q) ** (k - 1) for k in range(1, T)) + T * (1 - q) ** (T - 1)
rhs = (1 - (1 - q) ** T) / q
chk("censored geometric identity (exact rational, q=1/7, T=11)", lhs == rhs)

# ---- 3. the readout worked instance ----
from math import isqrt
s4 = isqrt(2 * 3 ** 8)
R4 = Fraction(2 * 81 + s4, 8 * 81)
chk("s_4 = 114 and R_4 = 23/54", s4 == 114 and R4 == Fraction(23, 54))
weights = [Fraction(23, 54), Fraction(23, 54), Fraction(2, 27), Fraction(2, 27)]
B = 81
prov = [int(B * w) for w in weights]
resid = B - sum(prov)
rema = sorted(range(4), key=lambda j: (B * weights[j]) - prov[j], reverse=True)
for j in rema[:resid]:
    prov[j] += 1
chk("largest-remainder allocation 35+34+6+6 = 81, discrepancy <= 1",
    sorted(prov, reverse=True) == [35, 34, 6, 6] and
    all(abs(prov[j] - B * weights[j]) <= 1 for j in range(4)))

# ---- 4. negative control: prefix counts against out-of-lattice thresholds ----
# Threshold counts along the raw drive orbit (3^k mod 641 below the grid
# rational's scaled threshold) are NOT discrepancy-bounded (Kesten: bounded
# prefix discrepancy only for thresholds in the orbit's own lattice); the
# theorem is therefore stated over complete recurrences, where counts are forced.
Om_, g_ = 641, 3
th = Fraction(23, 54)
x, c, viol_B = 1, 0, None
for B in range(1, 200):
    if x < th * Om_:
        c += 1
    x = x * g_ % Om_
    if abs(c - B * th) >= 2 and viol_B is None:
        viol_B = B
chk(f"negative control: raw-orbit prefix count breaks unit discrepancy (first at B={viol_B})",
    viol_B is not None)

# ---- 5. per-stratum split, B = 2, 3, Omega = 641 ----
Om = 641
r = 67  # sqrt(2) mod 641
assert (r * r) % Om == 2
g = 3
z8 = pow(g, (Om - 1) // 8, Om)          # primitive 8th root
dial = [(pow(z8, 2 * j + 1, Om) + pow(z8, -(2 * j + 1), Om)) % Om for j in range(8)]
chk("dial values are +/- sqrt2 mod 641 and sum to zero",
    set(dial) == {r % Om, (-r) % Om} and sum(dial) % Om == 0)

# exact Z[sqrt2] arithmetic: elements as (rational part, sqrt2 part)
def mul(x, y):
    return (x[0] * y[0] + 2 * x[1] * y[1], x[0] * y[1] + x[1] * y[0])
for B in (2, 3):
    total = [0] * (2 ** B)
    for j_idx, rj_sign in enumerate([+1, -1] * 4):   # dial recurrence: r_j alternates +r,-r
        Wp = (2, rj_sign)   # 2 + r_j
        Wm = (2, -rj_sign)  # 2 - r_j
        for si, string in enumerate(product((0, 1), repeat=B)):
            t = (1, 0)
            for bit in string:
                t = mul(t, Wp if bit == 0 else Wm)
            # accumulate rational part; sqrt2 parts must cancel over the dial
            total[si] = total[si] + t[0] if isinstance(total[si], int) else total[si]
    # recompute properly with both parts
    tallies = []
    for string in product((0, 1), repeat=B):
        acc = (0, 0)
        for rj_sign in [+1, -1] * 4:
            t = (1, 0)
            for bit in string:
                t = mul(t, (2, rj_sign) if bit == 0 else (2, -rj_sign))
            acc = (acc[0] + t[0], acc[1] + t[1])
        tallies.append((string, acc))
    dialN = 8
    # Galois-symmetric coefficient = rational part of prod W_{s_i} at r_j=+sqrt2
    def sym_coeff(string):
        t = (1, 0)
        for bit in string:
            t = mul(t, (2, 1) if bit == 0 else (2, -1))
        return t[0]
    all_ok = all(acc[1] == 0 and acc[0] == dialN * sym_coeff(st) for st, acc in tallies)
    tot = sum(acc[0] for _, acc in tallies)
    chk(f"B={B}: string tallies = |dial| x Galois-symmetric coefficients; total = 4^B x |dial| ({tot} = {4**B*8})",
        all_ok and tot == (4 ** B) * dialN)
    # residue check mod 641
    res_ok = True
    for st, acc in tallies:
        acc_res = 0
        for rj in dial:
            t = 1
            for bit in st:
                t = t * ((2 + rj) if bit == 0 else (2 - rj)) % Om
            acc_res = (acc_res + t) % Om
        if acc_res != (dialN * sym_coeff(st)) % Om:
            res_ok = False
    chk(f"B={B}: residue tallies mod 641 agree", res_ok)

print("\nALL PASS" if ok else "\nFAILURES PRESENT")
raise SystemExit(0 if ok else 1)
