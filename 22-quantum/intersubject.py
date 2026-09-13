## intersubject.py
## Open item (3): consistency of sequential registrations by distinct Subjects.
## Two Subjects S, S' read one Object O in the Carrier F_421. Cores
##   K  = Phi_S  cap Phi_O = C_d,   K' = Phi_S' cap Phi_O = C_d',
##   common core  K^ = K cap K' = C_e,  e = gcd(d, d') = gcd(n_S, n_S', n_O),
## with 4 | e for symmetry-complete shells; generically K^ = Q4 (e = 4).
##
## Result (verified, exact arithmetic in the ledger Z[zeta_{n_O}]; no floats):
##  (I)  Order-independent joint refinement. The S- and S'-fibre partitions of
##       Phi_O refine to the partition by K^; each non-empty joint cell
##       C = F_a cap F'_a' is one K^-coset, the same for both registration orders.
##  (II) Shared-core agreement. For a winding psi_s the selection rule lets S
##       register only in channels r = s (mod d) and S' only in r' = s (mod d');
##       both reduce to the one core index s (mod e), so S and S' induce the
##       identical core character eta_{s mod e} on K^ -- the same quarter-turn datum.
##  (III) No contradiction; order-independence on the shared cell. A sequence is
##       realisable in a given order exactly when its first registration is
##       selection-allowed, the fibres meet, and the channels agree on K^
##       (r = r' mod e). For ANY realisable sequence, in EITHER order, the joint
##       cell C is one K^-coset and the post-state restricted to C is the core
##       character eta_{s mod e}. So the two Subjects never assign different
##       values to the shared core. The post-state off the shared cell sits on
##       the last frame's fibre -- ordinary back-action, not a contradiction.
##
## Carrier F_421 (g = 2, N = 420). Configurations:
##   A  O_29 read by S = S_61 and S' = S_13   (equal cores, K = K' = Q4)
##   B  O_61 read by S = S_29 and S' = S_13   (embedded cores, K = Q4 < K' = C_12)
##   R  abstract C_24, cores C_12 and C_8     (incomparable, gcd = C_4): part (I)

from math import gcd
from itertools import product

PASS = 0
def report(label, ok):
    global PASS
    print(('PASS ' if ok else 'FAIL ') + label)
    assert ok, label
    PASS += 1

def lcm(a, b):
    return a * b // gcd(a, b)

# ----------------------------------------------------------------------
# Exact cyclotomic ring Z[zeta_n] = Z[x]/(Phi_n), integer coefficients.
# ----------------------------------------------------------------------
def _trim(a):
    while len(a) > 1 and a[-1] == 0:
        a.pop()
    return a

def _mul(a, b):
    r = [0] * (len(a) + len(b) - 1)
    for i, x in enumerate(a):
        if x:
            for j, y in enumerate(b):
                r[i + j] += x * y
    return _trim(r)

def _divexact(a, b):                       # exact quotient, b monic
    a = a[:]; db = len(b) - 1; q = [0] * (len(a) - db)
    for i in range(len(a) - 1, db - 1, -1):
        c = a[i]
        if c:
            q[i - db] = c
            for j, bc in enumerate(b):
                a[i - db + j] -= c * bc
    return _trim(q)

def _mod(a, m):                            # remainder mod monic m
    a = a[:]; dm = len(m) - 1
    while len(a) - 1 >= dm and not (len(a) == 1 and a[0] == 0):
        if a[-1] == 0:
            a.pop(); continue
        c = a[-1]; sh = len(a) - 1 - dm
        for j, mc in enumerate(m):
            a[sh + j] -= c * mc
        _trim(a)
    return _trim(a)

_CYC = {}
def cyclotomic(n):
    if n in _CYC:
        return _CYC[n]
    num = [-1] + [0] * (n - 1) + [1]       # x^n - 1
    for d in range(1, n):
        if n % d == 0:
            num = _divexact(num, cyclotomic(d))
    _CYC[n] = num
    return num

class Cyc:
    __slots__ = ('n', 'a')
    def __init__(self, n, a):
        self.n = n
        self.a = _mod(a, cyclotomic(n))
    @staticmethod
    def mono(n, e, k=1):
        e %= n
        return Cyc(n, [0] * e + [k])
    @staticmethod
    def zero(n):
        return Cyc(n, [0])
    def __add__(s, t):
        m = max(len(s.a), len(t.a)); r = [0] * m
        for i, v in enumerate(s.a): r[i] += v
        for i, v in enumerate(t.a): r[i] += v
        return Cyc(s.n, r)
    def __mul__(s, t):
        return Cyc(s.n, _mul(s.a, t.a))
    def conj(s):                            # zeta -> zeta^{-1}
        out = Cyc.zero(s.n)
        for e, v in enumerate(s.a):
            if v:
                out = out + Cyc.mono(s.n, (-e) % s.n, v)
        return out
    def is_zero(s):
        return len(s.a) == 1 and s.a[0] == 0
    def __eq__(s, t):
        return (s + Cyc(s.n, [-c for c in t.a])).is_zero()

# self-test: sum of all d-th roots of unity vanishes in Z[zeta_n].
_s = Cyc.zero(28)
for ell in range(4):
    _s = _s + Cyc.mono(28, 7 * ell)
report('ring Z[zeta_28] exact: 1 + i + i^2 + i^3 = 0 (cyclotomic reduction)', _s.is_zero())

# ----------------------------------------------------------------------
# Carrier and observation.  States are sparse dicts {exponent: Cyc} (nonzero only).
# ----------------------------------------------------------------------
p, g = 421, 2
N = p - 1
def order_mod(a, p):
    x, k = 1, 0
    while True:
        x = (x * a) % p; k += 1
        if x == 1: return k
report('admissibility: 421 = 4*105+1 prime-shell, g = 2 primitive (order 420)',
       p % 4 == 1 and order_mod(g, p) == N)

def fibre(nO, d, alpha):
    step = nO // d
    return frozenset((alpha + step * ell) % nO for ell in range(d))

def eta(nO, d, r, ell):
    return Cyc.mono(nO, (nO // d) * r * ell)

def amplitude(state, nO, d, r, alpha):
    step = nO // d; acc = Cyc.zero(nO)
    for ell in range(d):
        j = (alpha + step * ell) % nO
        v = state.get(j)
        if v is not None:
            acc = acc + eta(nO, d, r, ell).conj() * v
    return acc

def luders(state, nO, d, r, alpha):        # sparse post-state on the fibre
    psi = amplitude(state, nO, d, r, alpha)
    if psi.is_zero():
        return {}
    step = nO // d; out = {}
    for ell in range(d):
        j = (alpha + step * ell) % nO
        out[j] = eta(nO, d, r, ell) * psi
    return out

def winding(nO, s):
    return {j: Cyc.mono(nO, s * j) for j in range(nO)}

def support(state):
    return frozenset(state.keys())

def restrict(state, cell):
    return {j: state[j] for j in cell if j in state}

def proportional(X, Y):                    # equal support, proportional by one ledger scalar
    SX, SY = support(X), support(Y)
    if SX != SY or not SX:
        return SX == SY
    S = sorted(SX)
    for i in S:
        for j in S:
            if not (X[i] * Y[j] == X[j] * Y[i]):
                return False
    return True

def k_cosets(nO, e):
    step = nO // e; seen, out = set(), []
    for a in range(nO):
        cs = frozenset((a + step * ell) % nO for ell in range(e))
        if cs not in seen:
            seen.add(cs); out.append(cs)
    return out

def transported_char(nO, e, idx, coset):   # eta_idx of K^ transported on one K^-coset
    rep = min(coset); step = nO // e; out = {}
    for j in coset:
        ell = ((j - rep) // step) % e
        out[j] = Cyc.mono(nO, (nO // e) * idx * ell)
    return out

# ----------------------------------------------------------------------
# Configurations.
# ----------------------------------------------------------------------
A = dict(nO=28, nS=60, nSp=12, tag="A  O_29 | S=S_61, S'=S_13  (equal cores Q4)")
B = dict(nO=60, nS=28, nSp=12, tag="B  O_61 | S=S_29, S'=S_13  (embedded, K=Q4 < K'=C_12)")
for cfg in (A, B):
    nO, nS, nSp = cfg['nO'], cfg['nS'], cfg['nSp']
    d, dp = gcd(nS, nO), gcd(nSp, nO)
    e = gcd(gcd(nS, nSp), nO)
    cfg.update(d=d, dp=dp, e=e)
    report(f"[{cfg['tag']}] cores d={d}, d'={dp}, common e={e}; 4|e and e=|Q4|=4",
           e == gcd(d, dp) and e % 4 == 0 and e == 4)

# ======================================================================
# (I) Order-independent joint refinement.
# ======================================================================
for cfg in (A, B):
    nO, d, dp, e = cfg['nO'], cfg['d'], cfg['dp'], cfg['e']
    F = [fibre(nO, d, a) for a in range(nO // d)]
    Fp = [fibre(nO, dp, a) for a in range(nO // dp)]
    K = set(k_cosets(nO, e)); ok, cells = True, 0
    for f in F:
        for fp in Fp:
            it = f & fp
            if it:
                cells += 1
                if it != (fp & f) or frozenset(it) not in K:
                    ok = False
    report(f"[{cfg['tag']}] (I) each joint cell C = F cap F' is one K^-coset, order-symmetric", ok)
    report(f"[{cfg['tag']}] (I) joint refinement = partition by K^ ([Phi_O:K^]={nO//e} cells)",
           cells == nO // e)

nO = 24; F = [fibre(nO, 12, a) for a in range(2)]; Fp = [fibre(nO, 8, a) for a in range(3)]
K = set(k_cosets(nO, 4)); ok, cells = True, 0
for f in F:
    for fp in Fp:
        it = f & fp
        if it:
            cells += 1
            if it != (fp & f) or frozenset(it) not in K:
                ok = False
report("R  C_24 incomparable cores C_12,C_8 (gcd C_4): (I) joint cells are C_4 cosets, "
       "order-symmetric", ok)
report("R  C_24 incomparable: refinement = partition by C_4 ([24:4]=6 cells)", cells == 6)

# ======================================================================
# (II) Shared-core agreement via the selection rule, every winding.
# ======================================================================
for cfg in (A, B):
    nO, d, dp, e = cfg['nO'], cfg['d'], cfg['dp'], cfg['e']
    ok_sel = ok_chr = True
    for s in range(nO):
        st = winding(nO, s)
        live = {r for r in range(d)
                if any(not amplitude(st, nO, d, r, a).is_zero() for a in range(nO // d))}
        livep = {r for r in range(dp)
                 if any(not amplitude(st, nO, dp, r, a).is_zero() for a in range(nO // dp))}
        if live != {s % d} or livep != {s % dp}:
            ok_sel = False; break
        if (s % d) % e != s % e or (s % dp) % e != s % e:
            ok_sel = False; break
        ch  = [eta(nO, e, (s % d) % e, ell) for ell in range(e)]
        chp = [eta(nO, e, (s % dp) % e, ell) for ell in range(e)]
        chs = [eta(nO, e, s % e, ell) for ell in range(e)]
        if not (all(x == y for x, y in zip(ch, chp)) and all(x == y for x, y in zip(ch, chs))):
            ok_chr = False; break
    report(f"[{cfg['tag']}] (II) selection: live(S)={{s mod d}}, live(S')={{s mod d'}}, "
           f"both reduce to s mod 4 (all {nO} windings)", ok_sel)
    report(f"[{cfg['tag']}] (II) S and S' induce the identical core character "
           f"eta_(s mod 4) on Q4 (all windings)", ok_chr)

# ======================================================================
# (III) Realisability, no contradiction, order-independence on the shared cell.
# ======================================================================
def seq(state, first, second, nO):
    (d1, r1, a1), (d2, r2, a2) = first, second
    s1 = luders(state, nO, d1, r1, a1)
    if not s1:
        return {}
    return luders(s1, nO, d2, r2, a2)

for cfg in (A, B):
    nO, d, dp, e = cfg['nO'], cfg['d'], cfg['dp'], cfg['e']
    nout, noutp = nO // d, nO // dp
    Kset = set(k_cosets(nO, e))
    ok_pred = ok_value = ok_both = True
    n_fwd = n_both = 0
    for s in range(lcm(d, dp)):                          # residue-exhaustive winding inputs
        st = winding(nO, s)
        for (r, a, rp, ap) in product(range(d), range(nout), range(dp), range(noutp)):
            C = fibre(nO, d, a) & fibre(nO, dp, ap)
            meet = bool(C)
            agree = (r % e) == (rp % e)
            pred_f = meet and (r % d == s % d) and agree
            pred_r = meet and (rp % dp == s % dp) and agree
            fwd = seq(st, (d, r, a), (dp, rp, ap), nO)
            rev = seq(st, (dp, rp, ap), (d, r, a), nO)
            if bool(fwd) != pred_f or bool(rev) != pred_r:
                ok_pred = False
            ref = transported_char(nO, e, s % e, C) if meet else None
            if fwd:
                n_fwd += 1
                if frozenset(C) not in Kset or not proportional(restrict(fwd, C), ref):
                    ok_value = False
            if rev:
                if frozenset(C) not in Kset or not proportional(restrict(rev, C), ref):
                    ok_value = False
            if fwd and rev:
                n_both += 1
                if not proportional(restrict(fwd, C), restrict(rev, C)):
                    ok_both = False
    report(f"[{cfg['tag']}] (III) realisability predicate exact, both orders "
           f"(first selection-allowed, fibres meet, r=r' mod 4)", ok_pred)
    report(f"[{cfg['tag']}] (III) every realisable sequence reads core value "
           f"eta_(s mod 4) on the K^-coset C  [{n_fwd} forward cases]", ok_value)
    report(f"[{cfg['tag']}] (III) both-order sequences agree on the shared cell C "
           f"[{n_both} cases]", ok_both)

# ======================================================================
# (III') Gaussian-integer superposition input (config A): shared-cell agreement.
# ======================================================================
nO, d, dp, e = A['nO'], A['d'], A['dp'], A['e']
nout, noutp = nO // d, nO // dp; iexp = nO // 4
st = {}
for j in range(nO):
    acc = Cyc.zero(nO)
    for s in range(nO):
        cs = Cyc.mono(nO, 0, 1 + s) + Cyc.mono(nO, iexp, 1 + (s % 5))
        acc = acc + cs * Cyc.mono(nO, s * j)
    if not acc.is_zero():
        st[j] = acc
ok_sup, both = True, 0
for (r, a, rp, ap) in product(range(d), range(nout), range(dp), range(noutp)):
    C = fibre(nO, d, a) & fibre(nO, dp, ap)
    fwd = seq(st, (d, r, a), (dp, rp, ap), nO)
    rev = seq(st, (dp, rp, ap), (d, r, a), nO)
    if fwd and rev:
        both += 1
        if not proportional(restrict(fwd, C), restrict(rev, C)):
            ok_sup = False
report(f"[{A['tag']}] (III') Gaussian-integer superposition input: {both} both-order "
       f"sequences, all agree on the shared cell", ok_sup)

# ======================================================================
# Teeth: channels disagreeing on Q4 (r != r' mod 4) are forbidden in BOTH orders.
# ======================================================================
nO, d, dp, e = A['nO'], A['d'], A['dp'], A['e']
nout, noutp = nO // d, nO // dp
st = winding(nO, 1); bad = []
for (r, a, rp, ap) in product(range(d), range(nout), range(dp), range(noutp)):
    if (r % e) != (rp % e):
        fwd = seq(st, (d, r, a), (dp, rp, ap), nO)
        rev = seq(st, (dp, rp, ap), (d, r, a), nO)
        bad.append(bool(fwd) or bool(rev))
report("[teeth] channels disagreeing on Q4 (r != r' mod 4) are null in BOTH orders "
       "-- inconsistency would show as nullity, never as a contradiction",
       len(bad) > 0 and not any(bad))

print(f"\nintersubject: {PASS}/{PASS} checks passing (exact arithmetic in Z[zeta_n], no floats)")
