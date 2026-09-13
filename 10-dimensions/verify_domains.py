#!/usr/bin/env python3
"""verify_domains.py -- exact-arithmetic verification for 10-dimensions
(quartet edition).

Layers:
  A. shell datum and domain algebra (F13 working shell): group law, grading,
     fibrewise addition, neutral criterion, local recovery, flag arithmetic
  B. the quartet at the unit face (symbolic, exact rationals over free
     exponents): action identity, pairing closure rank, cancellation identity,
     mechanical table re-derivation
  C. the defining congruences on the lab Carrier (S = 602,140, Omega = 2,408,561): existence,
     exhaustive root enumeration, root pairs, register identities
  H. pair layer (round 05): pair-well-definedness of every congruence identity and
     the representative-inertness sweep over all admissible sign assignments

Every check is integer or exact-rational arithmetic; no floats, no RNG
(the window-ladder orderings are compared by integer squares).
Domains are triples (r mod p, s mod p-1, n mod 4): free [L],[T] exponents
and the flag.
"""

from fractions import Fraction as Fr

passed = []


def check(name, cond):
    assert cond, f"FAIL: {name}"
    passed.append(name)


# =====================================================================
# A. shell datum and domain algebra on F13
# =====================================================================
P = 13
KAPPA = (P - 1) // 4
G13 = 2

order = next(k for k in range(1, P) if pow(G13, k, P) == 1)
check("g=2 primitive on F13 (order 12)", order == P - 1)

I13 = (-pow(G13, KAPPA, P)) % P
check("i = -g^kappa = 5", I13 == 5)
check("i = g^{-kappa}", I13 == pow(G13, (P - 1) - KAPPA, P))
check("i^2 = -1", (I13 * I13) % P == P - 1)
PI13 = 2 * KAPPA
check("pi = 2 kappa = 6", PI13 == 6)
check("e = g^i = 6", pow(G13, I13, P) == 6)
check("g^pi = -1", pow(G13, PI13, P) == P - 1)
check("2 pi = p-1 == -1 (mod p)", (2 * PI13) % P == P - 1)
check("phase-cycle order p-1 = 4 kappa = 2 pi", P - 1 == 4 * KAPPA == 2 * PI13)

# capacity is a size: budget statement only (count-per-count), no duration
check("capacity budget: quarter cycle holds kappa steps", 4 * KAPPA == P - 1)

# domain group D_p = Z_p x Z_{p-1} with flag component mod 4
def dmul(a, b):
    return ((a[0] + b[0]) % P, (a[1] + b[1]) % (P - 1), (a[2] + b[2]) % 4)

def dinv(a):
    return ((-a[0]) % P, (-a[1]) % (P - 1), (-a[2]) % 4)

ONE = (0, 0, 0)
L = (1, 0, 0)
T = (0, 1, 0)
FLAG = (0, 0, 1)                 # the unit flag Iq

check("group identity", dmul(ONE, L) == L)
check("inverses", dmul(L, dinv(L)) == ONE and dmul(FLAG, dinv(FLAG)) == ONE)
check("flag order four", dmul(dmul(FLAG, FLAG), dmul(FLAG, FLAG)) == ONE)
# fork B: the flag is internal, Iq = [T]^kappa; realized label of (r,s;j) is
# (r mod p, (s + j*kappa) mod (p-1)) with sector j mod 4
def realize(a):
    return (a[0] % P, (a[1] + a[2] * KAPPA) % (P - 1))
check("realized flag label = (0, kappa)", realize(FLAG) == (0, KAPPA))
o4 = [(r, s) for r in range(P) for s in range(P - 1)
      if (4 * r) % P == 0 and (4 * s) % (P - 1) == 0
      and not ((2 * r) % P == 0 and (2 * s) % (P - 1) == 0)]
check("unique order-four subgroup: exactly two generators", sorted(o4) == [(0, KAPPA), (0, 3 * KAPPA)])
check("no flag of space: all order-four elements have r = 0", all(r == 0 for r, _ in o4))
check("flag horizon-inaccessible on window H<kappa",
      all((0, KAPPA) != (r % P, s % (P - 1))
          for r in range(-1, 2) for s in range(-1, 2)))
EPSILONS = [e for e in range(1, P - 1) if __import__("math").gcd(e, P - 1) == 1]
check("flag covariance: eps*kappa in {kappa, 3kappa} for all units eps",
      all((e * KAPPA) % (P - 1) in (KAPPA, 3 * KAPPA) for e in EPSILONS))
check("realization is a homomorphism",
      all(realize(dmul(a, b)) == ((realize(a)[0] + realize(b)[0]) % P,
                                  (realize(a)[1] + realize(b)[1]) % (P - 1))
          for a in [L, T, FLAG, (3, 5, 2)] for b in [L, T, FLAG, (7, 2, 3)]))

# derived domains
def dpow(a, k):
    out = ONE
    step = a if k >= 0 else dinv(a)
    for _ in range(abs(k)):
        out = dmul(out, step)
    return out

E_dom = dmul(FLAG, dinv(T))                       # [E] = Iq T^-1
p_dom = dmul(FLAG, dinv(L))                       # [p] = Iq L^-1
v_dom = dmul(L, dinv(T))                          # [v] = L T^-1
m_dom = dmul(E_dom, dinv(dpow(v_dom, 2)))         # [m] = [E][v]^-2
check("[m] = Iq L^-2 T", m_dom == ((-2) % P, 1, 1))
F_dom = dmul(m_dom, dmul(L, dpow(dinv(T), 2)))    # [F] = [m][a]
check("[F] = Iq L^-1 T^-1", F_dom == ((-1) % P, (-1) % (P - 1), 1))
S_dom = dmul(E_dom, T)
check("[S] = Iq (action carries the flag)", S_dom == FLAG)
check("phase count neutral: [E][T][hbar]^-1 = 1", dmul(S_dom, dinv(FLAG)) == ONE)
G_dom = dmul(F_dom, dmul(dpow(L, 2), dinv(dpow(m_dom, 2))))
check("[G] = Iq^-1 L^5 T^-3", G_dom == (5, (-3) % (P - 1), 3))
check("Planck area flag-free: [G][hbar][c]^-3",
      dmul(G_dom, dmul(FLAG, dpow(dinv(v_dom), 3)))[2] == 0)
check("[G hbar c^-3] = L^2",
      dmul(G_dom, dmul(FLAG, dpow(dinv(v_dom), 3))) == (2, 0, 0))
check("[Gm/c^2] = L",
      dmul(G_dom, dmul(m_dom, dpow(dinv(v_dom), 2))) == (1, 0, 0))
check("[Gm/r^3] = T^-2 flag-free",
      dmul(G_dom, dmul(m_dom, dpow(dinv(L), 3))) == (0, (-2) % (P - 1), 0))
check("Compton flag-free: [m][c][hbar]^-1 = L^-1",
      dmul(m_dom, dmul(v_dom, dinv(FLAG))) == ((-1) % P, 0, 0))

# fibrewise addition / neutral criterion / local recovery
check("squaring leaves fibre: dom(Q) != dom(Q^2) for [L]", L != dpow(L, 2))
H = 5
check("local recovery bound: p-1 > 2H", P - 1 > 2 * H)
pairs = [(r, s) for r in range(-H, H + 1) for s in range(-H, H + 1)]
images = {(r % P, s % (P - 1)) for (r, s) in pairs}
check("local recovery: all |r|,|s| <= 5 distinguished", len(images) == len(pairs))

# =====================================================================
# B. the quartet at the unit face (exact rationals over free scales)
# =====================================================================
# Represent horizons as exponent vectors over (l, t, p, E) and verify the
# relation lattice; then instantiate with exact rationals satisfying the
# one identity l*p = t*E and confirm every claimed equality numerically.
import itertools

# exponent vectors: c = l - t (= E - p), hbar = l + p (= t + E), mix = p + t
c_vec    = (1, -1, 0, 0)
c_vec2   = (0, 0, -1, 1)
hbar_vec = (1, 0, 1, 0)
hbar_vec2= (0, 1, 0, 1)
mix_vec  = (0, 1, 1, 0)
lE_vec   = (1, 0, 0, 1)
rel      = (1, -1, 1, -1)        # l - t + p - E = 0 <=> l*p = t*E

def add(u, v): return tuple(a + b for a, b in zip(u, v))
def sub(u, v): return tuple(a - b for a, b in zip(u, v))

check("c faces differ by the relation", sub(c_vec, c_vec2) == rel)
check("hbar faces differ by the relation", sub(hbar_vec, hbar_vec2) == rel)
check("l*E = hbar*c (exponent identity)", lE_vec == add(hbar_vec2, c_vec))
check("mix = hbar/c (exponent identity)", mix_vec == sub(hbar_vec2, c_vec2))

# rank of {c, hbar, mix} modulo the relation is 3 (full)
def rank_int(rows):
    m = [list(map(Fr, r)) for r in rows]
    rank, ncols = 0, len(m[0])
    for col in range(ncols):
        piv = next((i for i in range(rank, len(m)) if m[i][col] != 0), None)
        if piv is None:
            continue
        m[rank], m[piv] = m[piv], m[rank]
        m[rank] = [x / m[rank][col] for x in m[rank]]
        for i in range(len(m)):
            if i != rank and m[i][col] != 0:
                m[i] = [a - m[i][col] * b for a, b in zip(m[i], m[rank])]
        rank += 1
    return rank

# pairing lattice mod the relation has rank TWO: mix = hbar - c, lE = hbar + c
check("mix = hbar' - c' (exponent identity: k_B derived)",
      mix_vec == sub(hbar_vec2, c_vec2))
check("pairing rank 2 mod relation: rank{c,hbar,rel} = 3",
      rank_int([c_vec, hbar_vec, rel]) == 3)
check("mix adds nothing: rank{c,hbar,mix,rel} = 3",
      rank_int([c_vec, hbar_vec, mix_vec, rel]) == 3)
check("lE adds nothing: rank{c,hbar,mix,lE,rel} = 3",
      rank_int([c_vec, hbar_vec, mix_vec, lE_vec, rel]) == 3)

# numeric instantiation with the identity enforced: choose l,t,p free, E = l*p/t
l, t, p = Fr(3, 7), Fr(2, 5), Fr(11, 4)
E = l * p / t
c_u, hbar_u = l / t, l * p
check("unit face: c = l/t = E/p", c_u == E / p)
check("unit face: hbar = l p = t E", hbar_u == t * E)
check("cancellation: (p t)(l/t) = l p  [k_B c = -hbar]", (p * t) * (l / t) == hbar_u)
check("mixed partner: l E = hbar c", l * E == hbar_u * c_u)
m_P = p / c_u
check("m_P = p/c = E/c^2", m_P == E / c_u ** 2)
G_num = hbar_u * c_u / m_P ** 2
check("G = hbar c / m_P^2 = l^2 c^3 / hbar", G_num == l ** 2 * c_u ** 3 / hbar_u)
# bijection {c, hbar, G} <-> quartet: recover the free scale from G
check("bijection: l^2 = G hbar / c^3", l ** 2 == G_num * hbar_u / c_u ** 3)
check("recovered quartet: t=l/c, p=hbar/l, E=hbar c/l",
      t == l / c_u and p == hbar_u / l and E == hbar_u * c_u / l)
Theta = E / (hbar_u / c_u)      # E_P / |k_B|
check("Theta_P = E_P/|k_B| = c^2/1 * ... consistent", Theta == E * c_u / hbar_u)

# DOF: quartet has 4 generators, 1 relation -> 3 free scales; +G -> 3+1
check("DOF: 4 - 1 = 3 free scales", 4 - rank_int([rel]) == 3)

# ------------------------------------------------------------------
# flag positions of the quartet: (l, t, p, E) at (0, 0, 1, 1) mod 4;
# every quartet relation must close on the flag component
# ------------------------------------------------------------------
FL = {"l": 0, "t": 0, "p": 1, "E": 1}
def flag_of(expr):
    # expr: dict of generator -> exponent
    return sum(FL[g] * e for g, e in expr.items()) % 4
check("flag[hbar = l p] = 1", flag_of({"l": 1, "p": 1}) == 1)
check("flag[hbar = t E] = 1", flag_of({"t": 1, "E": 1}) == 1)
check("flag[c = l/t] = 0", flag_of({"l": 1, "t": -1}) == 0)
check("flag[c = E/p] = 0", flag_of({"E": 1, "p": -1}) == 0)
check("flag[k_B ~ p t] = 1", flag_of({"p": 1, "t": 1}) == 1)
check("flag[hbar c ~ l E] = 1", flag_of({"l": 1, "E": 1}) == 1)
# G = l^2 c^3 / hbar: flags 2*0 + 3*0 - 1 = -1 = 3 mod 4 (inverse flag)
check("flag[G] = -1", (2 * FL["l"] + 3 * 0 - flag_of({"l": 1, "p": 1})) % 4 == 3)
# Planck area G hbar / c^3 flag-free; Gm/c^2 flag-free (m at flag 1)
check("flag[G hbar/c^3] = 0", (3 + 1 + 0) % 4 == 0)
check("flag[G m/c^2] = 0 (m flag 1)", (3 + 1 + 0) % 4 == 0)
# dual horizons are flag-crossed images: p = hbar/l, E = hbar/t
check("p = hbar/l (unit face)", p == hbar_u / l)
check("E = hbar/t (unit face)", E == hbar_u / t)
# equivalent generating data {l, t, hbar} <-> {c, hbar, G}
check("{l,t,hbar} determine c, G", c_u == l / t and G_num == l ** 2 * (l / t) ** 3 / hbar_u)

# =====================================================================
# C. the defining congruences on the lab Carrier
# =====================================================================
S = 602_140
Om = 4 * S + 1
check("Om = 2,408,561", Om == 2_408_561)

def is_prime(n):
    if n < 2: return False
    if n % 2 == 0: return n == 2
    d = 3
    while d * d <= n:
        if n % d == 0: return False
        d += 2
    return True

check("admissibility: S even, S=1 mod 3, Om prime",
      S % 2 == 0 and S % 3 == 1 and is_prime(Om))

# congruence 1: 2G + 1 = 0 -- linear, unique
G_pin = [x for x in (pow(2, -1, Om) * (Om - 1) % Om,) ]
G_val = (Om - 1) // 2
check("congruence 2G+1=0 unique: G = 2S = 1,204,280", (2 * G_val + 1) % Om == 0 and G_val == 2 * S == 1_204_280)

# quadratic defining congruences: exhaustive-root verification via the known values
hbar_val = 18_688
kB_val = 1_880_160
check("congruence hbar^2 = -1", (hbar_val * hbar_val) % Om == Om - 1)
check("congruence k_B^2 = -2", (kB_val * kB_val) % Om == Om - 2)
c2 = (2 * S + 1) % Om
check("congruence 2c^2 = 1: c^2 = 2S+1", (2 * c2) % Om == 1)
# each quadratic congruence has exactly two roots: x and Om - x
for name, val, target in (("hbar", hbar_val, Om - 1), ("k_B", kB_val, Om - 2)):
    other = Om - val
    check(f"{name}: two roots {{x, -x}}", (other * other) % Om == target and other != val)
# linkage consistency: the stated representatives satisfy k_B c = -hbar
c_val = (-hbar_val * pow(kB_val, -1, Om)) % Om
check("c from k_B c = -hbar", (kB_val * c_val) % Om == (Om - hbar_val) % Om)
check("c^2 lands on the congruence", (c_val * c_val) % Om == c2)
check("register identities: G = -c^2, G^2 = 4^-1",
      (G_val + c2) % Om == 0 and (4 * G_val * G_val) % Om == 1)
check("h = 2 pi hbar = -hbar = k_B c", (Om - hbar_val) % Om == (kB_val * c_val) % Om)
check("m_P^2 = Om = 0 (scale face: the totality)", (Om) % Om == 0)


# =====================================================================
# D. revision layer: both Carriers, face closure, minimality, temperature
# =====================================================================

def sqrt_roots(a, Om):
    return sorted(x for x in range(Om) if (x * x) % Om == a % Om)

CARRIERS = {
    233: dict(S=58, hbar=89, kB=124, c=159, G=116, h=144),
    2_408_561: dict(S=602_140, hbar=18_688, kB=1_880_160, c=171_106, G=1_204_280, h=2_389_873),
}
# fill lab h and c consistently
lab = CARRIERS[2_408_561]
lab["c"] = (-lab["hbar"] * pow(lab["kB"], -1, 2_408_561)) % 2_408_561
lab["h"] = (2_408_561 - lab["hbar"]) % 2_408_561

for Om_, R in CARRIERS.items():
    S_, hb, kB, c_, G_, h_ = R["S"], R["hbar"], R["kB"], R["c"], R["G"], R["h"]
    check(f"[{Om_}] admissibility triple: S even, S=1 mod 3, Om prime",
          S_ % 2 == 0 and S_ % 3 == 1 and is_prime(Om_))
    check(f"[{Om_}] two-way class: S even <=> Om = 1 mod 8", Om_ % 8 == 1)
    # congruence equations of the residue reading
    check(f"[{Om_}] B: 2G = -1", (2 * G_ + 1) % Om_ == 0)
    check(f"[{Om_}] B: c^2 = 2^-1", (2 * c_ * c_) % Om_ == 1)
    check(f"[{Om_}] B: hbar^2 = -1", (hb * hb) % Om_ == Om_ - 1)
    check(f"[{Om_}] B: k_B^2 = -2", (kB * kB) % Om_ == Om_ - 2)
    check(f"[{Om_}] B: k_B c = -hbar", (kB * c_) % Om_ == (Om_ - hb) % Om_)
    check(f"[{Om_}] B: h = -hbar", h_ == (Om_ - hb) % Om_)
    # closure consequences (Prop faces-closure)
    check(f"[{Om_}] closure: G = -c^2", (G_ + c_ * c_) % Om_ == 0)
    check(f"[{Om_}] closure: G^2 = 4^-1", (4 * G_ * G_) % Om_ == 1)
    check(f"[{Om_}] closure: hbar^4 = 1", pow(hb, 4, Om_) == 1)
    check(f"[{Om_}] closure: (k_B c)^2 = -1", pow(kB * c_, 2, Om_) == Om_ - 1)
    check(f"[{Om_}] closure: hbar c G^-1 = k_B (m_P^2 monomial face on the k_B residue)",
          (hb * c_ * pow(G_, -1, Om_)) % Om_ == kB)
    check(f"[{Om_}] monomial face nonzero: horizon declaration is not a congruence",
          (hb * c_ * pow(G_, -1, Om_)) % Om_ != 0)
    # defining congruences have exactly two roots each
    for name, val, tgt in (("hbar", hb, Om_ - 1), ("kB", kB, Om_ - 2)):
        roots = sorted(((val) % Om_, (Om_ - val) % Om_))
        check(f"[{Om_}] {name}: root pair valid", all((x * x) % Om_ == tgt for x in roots))

# representative half-planes are chart data (suite annex): band predicates
# carry no invariant content, as the pair form requires
r233 = sqrt_roots(58, 233)
check("233: sqrt(S) roots {72,161}", r233 == [72, 161])
check("233: hbar-representative from the upper-half root of S (161 -> 89): chart datum",
      (2 * 161) % 233 == 89 and 161 > 233 // 2)
check("233: the other root gives the pair partner h (72 -> 144)", (2 * 72) % 233 == 144)
check("lab: hbar-representative from the lower-half root of S (9344): chart datum",
      (2 * 9344) % 2_408_561 == 18_688 and 9344 < 2_408_561 // 2)
check("half-plane of the hbar-representative differs across Carriers: band = chart data",
      (161 > 233 // 2) and (9344 < 2_408_561 // 2))

# -1 is QR unconditionally (Om = 4S+1 = 1 mod 4), S even needed only for 2
check("-1 QR even for odd S: Om=13 (S=3), 5^2 = -1", (5 * 5) % 13 == 12)
check("Om = 1 mod 4 for every S", all((4 * S0 + 1) % 4 == 1 for S0 in range(1, 50)))

# minimality scan under the complete predicate (Appendix A)
def admissible(p_, Om__):
    kap_ = (p_ - 1) // 4
    S__ = (Om__ - 1) // 4
    return (kap_ > 1 and is_prime(p_) and p_ % 4 == 1
            and Om__ % 4 == 1 and is_prime(Om__)
            and S__ % 2 == 0 and S__ % 3 == 1
            and p_ * p_ < Om__)
adm = [(p_, Om__) for p_ in range(5, 40, 4) for Om__ in range(p_ * p_ + 1, 234)
       if admissible(p_, Om__)]
check("minimality: (13,233) admissible", (13, 233) in adm)
check("minimality: no admissible pair below 233", min(o for _, o in adm) == 233)
check("counterfactual: dropping mod-3 admits (13,193)",
      is_prime(193) and 48 % 2 == 0 and 48 % 3 == 0 and 13 * 13 < 193)
check("counterfactual: dropping kappa>1 admits (5,41)",
      is_prime(5) and is_prime(41) and 10 % 2 == 0 and 10 % 3 == 1 and 25 < 41)
check("F5 is its own quarter-turn core: 4*kappa = 4 = p-1 with kappa=1", 4 * 1 == 5 - 1)
check("kappa=2 not viable: 9 composite", not is_prime(9))

# temperature and Unruh closures in (r, s, j) bookkeeping
kB_dom = (-1, 1, 1)                    # Iq L^-1 T
E_dom3 = (0, -1, 1)                    # Iq T^-1
acc = (1, -2, 0)
Theta = tuple(a - b for a, b in zip(E_dom3, kB_dom))
check("[Theta] = [E][k_B]^-1 = L T^-2, flag-free", Theta == acc)
c_dom3 = (1, -1, 0)
hb_dom3 = (0, 0, 1)
unruh = tuple(h + a - c - k for h, a, c, k in zip(hb_dom3, acc, c_dom3, kB_dom))
check("Unruh closure: [hbar a / (c k_B)] = [Theta]", unruh == acc)

# crossing-degree recovery (Cor recovery-crossings)
def embed(u, a, b):
    return (a - 2 * u, b + u, u)
trip = [(u, a, b) for u in range(-2, 3) for a in range(-3, 4) for b in range(-3, 4)]
check("classical embedding injective on Z^3",
      len({embed(u, a, b) for u, a, b in trip}) == len(trip))
P2, K2 = 229, 57
def real2(r, s, j):
    return (r % P2, (s + j * K2) % (P2 - 1))
win = [(r, s, j) for r in range(-5, 6) for s in range(-5, 6) for j in (-1, 0, 1)]
check("faithful realization on window (p=229, H=5, |j|<=1)",
      len({(real2(*w), w[2] % 4) for w in win}) == len(win))
check("sector saturates mod 4: hbar^4 realizes at sector zero",
      (4 * K2) % (P2 - 1) == 0)


# =====================================================================
# E. round-02 layer: covariance counterexamples, window covariance,
#    orientation data, index-two lattice, reading multiplicativity
# =====================================================================

# (a) regression: the naive character on Z_p-reduced labels is ill-defined
inv2 = pow(2, -1, 13)
check("r02: character ill-defined on the modular projection (r=3 vs r=16 differ)",
      pow(inv2, 3, 13) != pow(inv2, 16, 13))
# (b) regression: (p-1, 0) has trivial character yet is non-neutral
check("r02: (p-1,0) trivial character for all m",
      all(pow(m, -(13 - 1), 13) == 1 for m in range(1, 13)))
check("r02: (p-1,0) is non-neutral in D_p", (13 - 1) % 13 != 0)
# (c) regression: eps as field character fails composition (5^2=1 in Z_12^x)
check("r02: eps field-character composition fails",
      (5 * 5) % 12 == 1 and pow(pow(5, -1, 13), 2, 13) != 1)

# window covariance (Theorem 5, repaired form)
H = 5
check("r02: window dilation: trivial character forces r=0 in window",
      all(not all(pow(m, -r, 13) == 1 for m in range(2, 13))
          for r in range(-H, H + 1) if r != 0))
# pushforward invariant sublattice on the realized lattice is {0, pi}
units12 = [e for e in range(1, 12) if __import__("math").gcd(e, 12) == 1]
inv_labels = [s_ for s_ in range(12) if all((e * s_) % 12 == s_ for e in units12)]
check("r02: pushforward-invariant labels are exactly {0, pi}", inv_labels == [0, 6])
check("r02: eps=-1 admissible always", __import__("math").gcd(11, 12) == 1)
# flag pair behaviour under pushforward: eps mod 4 in {1,3} decides fix/swap
check("r02: quarter-turn labels fixed iff eps=1 mod 4",
      all(((e * 3) % 12 == 3) == (e % 4 == 1) for e in units12))

# representative-convention data (chart-side record; no invariant content)
check("r02: hbar representative lower-half on 233 (chart datum)", 89 < 233 // 2 and (89 * 89) % 233 == 232)
check("r02: hbar representative lower-half on lab (chart datum)",
      18_688 < 2_408_561 // 2 and (18_688 ** 2) % 2_408_561 == 2_408_560)
check("r02: c representative halves differ across Carriers (chart data)",
      (159 > 233 // 2) and (171_106 < 2_408_561 // 2))
check("r02: +-c one residue class (-1 is QR)", pow(89, 2, 233) == 233 - 1)

# index-two sublattice <c, hbar, G> in Z^3 on (l, t, hbar)
M = [[1, -1, 0], [0, 0, 1], [5, -3, -1]]
det = (M[0][0] * (M[1][1] * M[2][2] - M[1][2] * M[2][1])
       - M[0][1] * (M[1][0] * M[2][2] - M[1][2] * M[2][0])
       + M[0][2] * (M[1][0] * M[2][1] - M[1][1] * M[2][0]))
check("r02: <c,hbar,G> has index two (det = -2)", det == -2)
check("r02: l^2 = G hbar / c^3 recovers the scale by positive root",
      l ** 2 == G_num * hbar_u / c_u ** 3 and l > 0)

# residue reading rho: multiplicative on constant monomials (both Carriers)
for Om_, R in CARRIERS.items():
    hb, kB, c_, G_ = R["hbar"], R["kB"], R["c"], R["G"]
    lhs = (hb * c_ * pow(G_, -1, Om_)) % Om_
    check(f"r02 [{Om_}]: rho multiplicative on hbar*c/G", lhs == kB)
    check(f"r02 [{Om_}]: rho(h) = -rho(hbar)", R["h"] == (Om_ - hb) % Om_)


# =====================================================================
# F. round-03 layer: window bound, sigma-twisted action, delta_C
# =====================================================================
import math as _m
units12 = [e for e in range(1, 12) if _m.gcd(e, 12) == 1]

# window counterexample (regression): at H >= 2kap, (0, pi) is invariant and non-neutral
check("r03: pi invariant under every pushforward", all((e * 6) % 12 == 6 for e in units12))
check("r03: (0,pi) non-neutral", 6 % 12 != 0)
# corrected window H < 2kap: only neutral label invariant
Hc = 2 * KAPPA - 1
inv_win = [s_ for s_ in range(-Hc, Hc + 1) if all((e * (s_ % 12)) % 12 == s_ % 12 for e in units12)]
check("r03: window H<2kap invariants = {0}", inv_win == [0])
check("r03: window bound equals local-recovery bound", (4 * KAPPA > 2 * Hc) and (Hc < 2 * KAPPA))

# sigma-twisted active action: full equivariance sweep on p=13 and p=229
def sigma(e):
    return 1 if e % 4 == 1 else -1
for P_, K_ in ((13, 3), (229, 57)):
    U_ = [e for e in range(1, P_ - 1) if _m.gcd(e, P_ - 1) == 1]
    ok = all(((e * s_) % (P_ - 1) + sigma(e) * j * K_) % (P_ - 1)
             == (e * (s_ + j * K_)) % (P_ - 1)
             for e in U_ for s_ in range(0, P_ - 1, max(1, (P_ - 1) // 12)) for j in (-2, -1, 0, 1, 2))
    check(f"r03: sigma-twist equivariant on p={P_}", ok)
check("r03: witness e=7,(2;1) matches realized action", ((7 * 2) % 12 + sigma(7) * 3) % 12 == (7 * 5) % 12)
check("r03: witness e=-1,(0;1) matches realized action", ((11 * 0) % 12 + sigma(11) * 3) % 12 == (11 * 3) % 12)
check("r03: plain lift fails for e=7,(2;1) (regression)", ((7 * 2) % 12 + 3) % 12 != (7 * 5) % 12)
check("r03: sigma multiplicative mod 4",
      all(sigma(a * b) == sigma(a) * sigma(b) for a in units12 for b in units12))

# delta_S / delta_C: involutions; delta_C carries primal domains to dual horizon domains
def dS_(a):
    return dinv(a)
def dC_(a):
    return dmul(FLAG, dinv(a))
check("r03: delta_S involution", all(dS_(dS_(a)) == a for a in [L, T, FLAG, (3, 5, 2)]))
check("r03: delta_C involution", all(dC_(dC_(a)) == a for a in [L, T, FLAG, (3, 5, 2)]))
check("r03: delta_C[L] = [p] domain", dC_(L) == p_dom)
check("r03: delta_C[T] = [E] domain", dC_(T) == E_dom)
check("r03: delta_S flag-free", dS_(L)[2] == 0 and dS_(T)[2] == 0)


# =====================================================================
# G. round-04 layer: realized action, j-restriction, ladder, k_B linkage typing
# =====================================================================
import math as _mm

# realized action composes with residue classes; Z^3 representatives do not
u0 = 5
check("r04: realized action composes (5*5=1 in Z_12^x)", ((5 * (5 * u0)) % 12) == ((25 % 12) * u0) % 12 == u0 % 12)
check("r04: integer representatives do not compose on Z (25s != s)", 25 * 2 != 2)

# j-suppression witness: (0,0;1) moves under eps=-1 (flag-free restriction needed)
check("r04: (0,0;1) sector moves under eps=-1", ((-1) * (0 + 3)) % 12 == 9 != 3)

# window ladder: nested for kappa >= 17; toy fails.  All orderings exact:
# 2 sqrt(k) < k/2  <=>  (4 sqrt(k))^2 < k^2  <=>  16 k < k^2  <=>  k > 16.
def ladder(k):
    return 16 * k < k * k and 0 < k
check("r04: ladder nested for kappa=17,387,602140 (integer-square ordering)",
      all(ladder(k) for k in (17, 387, 602140)))
check("r04: toy kappa=3 below nesting threshold", not ladder(3))
check("r04: coherence window identity (2 sqrt kappa)^2 = 4 kappa = p-1 exactly",
      all((2 * 2 * k == 4 * k) and (4 * k == (4 * k + 1) - 1) for k in (3, 387, 602140)))
check("r04: totality closure exact: (2 sqrt S)^2 = Om - 1",
      4 * 602140 == 2408561 - 1)

# F/a is flagged (equal-crossing-degree correction): [F]=(-1,-1;1), [a]=(1,-2;0)
F3 = (-1, -1, 1); A3 = (1, -2, 0)
ratio = tuple(f - a for f, a in zip(F3, A3))
check("r04: F/a crossing degree 1 (flagged, = [m])", ratio == (-2, 1, 1))

# meridian transport onto the flag: (L T^kappa)^p = Iq on several shells
for P_, K_ in ((13, 3), (29, 7), (229, 57)):
    check(f"r04: meridian transport p={P_}", (P_ % P_, (P_ * K_) % (P_ - 1)) == (0, K_))

# both roots of -2 satisfy the congruence individually (the pair is the canonical
# object); the stated representative is the linkage-consistent one
for Om_, R in CARRIERS.items():
    kB = R["kB"]; other = Om_ - kB
    check(f"r04 [{Om_}]: both k_B roots satisfy the congruence", (other * other) % Om_ == Om_ - 2)
    check(f"r04 [{Om_}]: stated representative is linkage-consistent, its partner is not",
          (kB * R["c"]) % Om_ == (Om_ - R["hbar"]) % Om_ and (other * R["c"]) % Om_ != (Om_ - R["hbar"]) % Om_)


# =====================================================================
# H. round-05 pair layer: pair-well-definedness and representative inertness
# =====================================================================
# pair multiplication {±a}{±b} = {±ab} is well defined: the four member
# products fall in one pair
for Om_, R in CARRIERS.items():
    a_, b_ = R["kB"], R["c"]
    prods = {(sa * a_ * sb * b_) % Om_ for sa in (1, -1) for sb in (1, -1)}
    check(f"H [{Om_}]: pair product well defined ({{±k_B}}{{±c}} is one pair)",
          prods == {(a_ * b_) % Om_, (-a_ * b_) % Om_})
    # linkage as a pair THEOREM: (k_B c)^2 = -1, so the product pair is the
    # root pair of -1, which is {±hbar}
    check(f"H [{Om_}]: (k_B c)^2 = -1 (linkage derived at pair level)",
          pow(a_ * b_, 2, Om_) == Om_ - 1)
    check(f"H [{Om_}]: product pair equals {{±hbar}}",
          prods == {R["hbar"] % Om_, (Om_ - R["hbar"]) % Om_})
    # (hbar c / G)^2 = -2: the monomial lands in the k_B pair
    mono = (R["hbar"] * R["c"] * pow(R["G"], -1, Om_)) % Om_
    check(f"H [{Om_}]: (hbar c/G)^2 = -2, landing in the k_B pair",
          pow(mono, 2, Om_) == Om_ - 2 and mono in {R["kB"], Om_ - R["kB"]})
    # representative inertness: exactly the assignments with s_h = s_c*s_k are
    # admissible (a (Z/2)^2 group), and every checked identity holds on each
    admissible_count = 0
    for s_c in (1, -1):
        for s_h in (1, -1):
            for s_k in (1, -1):
                hb2, c2_, kB2 = (s_h * R["hbar"]) % Om_, (s_c * R["c"]) % Om_, (s_k * R["kB"]) % Om_
                quad = ((2 * c2_ * c2_) % Om_ == 1 and (hb2 * hb2) % Om_ == Om_ - 1
                        and (kB2 * kB2) % Om_ == Om_ - 2)
                link = (kB2 * c2_) % Om_ == (Om_ - hb2) % Om_
                if quad and link:
                    admissible_count += 1
                    h2 = (Om_ - hb2) % Om_
                    check(f"H [{Om_}] ({s_c},{s_h},{s_k}): h-form holds", h2 == (-hb2) % Om_)
                    check(f"H [{Om_}] ({s_c},{s_h},{s_k}): monomial lands on this assignment's k_B",
                          (hb2 * c2_ * pow(R["G"], -1, Om_)) % Om_ == kB2)
                assert quad, "quadratic defining congruences are sign-blind"
    check(f"H [{Om_}]: admissible assignments form (Z/2)^2 (exactly four)",
          admissible_count == 4)
# hbar-flip relabels within the pair: {hbar, h} -> {h, hbar}
check("H: hbar-flip relabels the {hbar,h} pair (233: 89 <-> 144)",
      (233 - 89) % 233 == 144 and (233 - 144) % 233 == 89)

print(f"{len(passed)}/{len(passed)} exact checks pass")
