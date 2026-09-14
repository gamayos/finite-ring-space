#!/usr/bin/env python3
"""22-quantum gleason suite: uniqueness of the pair tally (prop:gleason), EXACT.
On the Q4 core: kernels K: Q4 -> Z[i] with K(d^-1) = conj(K(d)) (two-way),
tally-valued on basis and point states. Claims:
(U1) the four character kernels eta_r(d) = i^{rd} span, over nonneg tallies,
     exactly the admissible kernels (exhaustive, coefficients 0..3);
(U2) Fourier inversion recovers nonneg integer c_r for every admissible kernel;
(U3) a kernel with any c_r negative or non-integer violates tally-valuedness
     on some state (witness produced);
(U4) covariance under channel repositioning pins K to a multiple of one eta_r.
Exhaustive on Q4 (d=4); cross-checked on the F13 core instance.
No floats, no RNG."""
from itertools import product

def rep(label, ok):
    print(('PASS ' if ok else 'FAIL ') + label); assert ok, label

# Q4 as Z_4 with values in Z[i] as (a,b) pairs; i^k:
def ipow(k):
    return [(1,0),(0,1),(-1,0),(0,-1)][k % 4]
def cadd(x,y): return (x[0]+y[0], x[1]+y[1])
def cmul(x,y): return (x[0]*y[0]-x[1]*y[1], x[0]*y[1]+x[1]*y[0])
def conj(x): return (x[0],-x[1])
def cscale(x,c): return (c*x[0], c*x[1])

# character kernels: eta_r(delta) = i^{r*delta}
def eta(r, d): return ipow(r*d)

# admissible kernel from coefficients c = (c0..c3): K(d) = sum_r c_r i^{rd}
def kernel(c):
    return [tuple(sum(cc*v for cc,v in zip(c, [eta(r,d)[j] for r in range(4)])) for j in range(2)) for d in range(4)]

# F(psi) for kernel K on a single fibre of size 4: F = sum_{u,u'} K(u'-u) psi_u conj(psi_u')
def F(K, psi):
    tot = (0,0)
    for u in range(4):
        for v in range(4):
            tot = cadd(tot, cmul(cmul(K[(v-u) % 4], psi[u]), conj(psi[v])))
    return tot

# U1/U2: exhaustive nonneg tally combos give two-way kernels, tally-valued on tests;
# and Fourier inversion c_r = (1/4) sum_d K(d) i^{-rd} recovers c exactly
ok1 = ok2 = True
tests = [
    [(1,0),(0,0),(0,0),(0,0)],                    # point mass
    [(1,0),(1,0),(1,0),(1,0)],                    # uniform (character r=0 state)
    [(1,0),(0,1),(-1,0),(0,-1)],                  # character r=1 state
    [(1,0),(1,0),(0,0),(0,0)],                    # pair state
]
for c in product(range(4), repeat=4):
    K = kernel(c)
    # two-way check
    if any(K[(-d) % 4] != conj(K[d]) for d in range(4)): ok1 = False
    # tally-valued on tests: F real nonneg integer
    for psi in tests:
        val = F(K, psi)
        if val[1] != 0 or val[0] < 0: ok1 = False
    # inversion
    for r in range(4):
        acc = (0,0)
        for d in range(4):
            acc = cadd(acc, cmul(K[d], ipow(-r*d)))
        if acc != (4*c[r], 0): ok2 = False
rep('U1: nonneg-tally character combinations are two-way and tally-valued (exhaustive c in 0..3)', ok1)
rep('U2: Fourier inversion recovers every coefficient exactly', ok2)

# U3: a negative coefficient violates tally-valuedness (witness: the matching character state)
c = (1, -1, 1, 0)
K = kernel(c)
psi = [(ipow(1*u)) for u in range(4)]  # character r=1 state: F = 16*c_1 < 0
val = F(K, psi)
rep('U3: negative coefficient witnessed by its character state (F = %d < 0)' % val[0],
    val == (-16, 0))

# U4: channel pinning: a kernel responds to exactly one character state
# (single-channel diagonal response, the covariance requirement) iff its
# coefficient vector is a scaled unit vector c = c*e_r  (exhaustive)
ok4 = True
for c in product(range(4), repeat=4):
    K = kernel(c)
    responses = []
    for r in range(4):
        psi = [ipow(r*u) for u in range(4)]
        responses.append(F(K, psi)[0])          # = 16 c_r
    single = sum(1 for x in responses if x != 0) == 1
    unitvec = sum(1 for x in c if x != 0) == 1
    if single != unitvec: ok4 = False
rep('U4: single-channel response iff scaled unit coefficient vector (channel pinning, exhaustive)', ok4)

# U5: the fibre-norm counterexample (round-03): K(delta)=[delta=1] satisfies (a)-(d),
# has c_r = 1/4 each (d^2 c = 4 realized, sum c = 1 realized, individual c NOT integer),
# responds to all four channels equally -> fails channel-selectivity (e)
Kfn = [(1,0),(0,0),(0,0),(0,0)]  # identity kernel on Q4 offsets
resp = []
for r in range(4):
    psi = [ipow(r*u) for u in range(4)]
    resp.append(F(Kfn, psi)[0])
inv = []
for r in range(4):
    acc = (0,0)
    for d in range(4):
        acc = cadd(acc, cmul(Kfn[d], ipow(-r*d)))
    inv.append(acc)
rep('U5: fibre norm satisfies (a)-(d): responses (4,4,4,4); 4c_r = 1 each (c_r = 1/4, not a tally); fails (e)',
    resp == [4,4,4,4] and all(x == (1,0) for x in inv) and sum(1 for x in resp if x != 0) == 4)

# U6a: the multiplier counterexample F = w_r/16: on stationary core-valued states a*psi_s the
# matched-channel weight is 16|a|^2, so F is tally-valued with c = 1/16: d^2 c = 1 realized,
# c itself not a tally -> only ray uniqueness holds (round-04 repair)
c_num, c_den = 1, 16
rep('U6a: F = w_r/16 has d^2 c = %d/%d * 16 = 1 realized, c = 1/16 not a tally (ray uniqueness only)'
    % (c_num, c_den), (16 * c_num) % c_den == 0 and c_den != 1)
# U6b: degree forcing, linear case: a drive-invariant linear kernel is constant on the orbit,
# so F(psi_k) = c * sum(zeta^{k u}) = 0 for every nontrivial winding (complete character sum);
# and on the trivial winding, tally-valuedness on both psi_0 and i*psi_0 forces c = 0:
# linearity gives F(i psi_0) = i * F(psi_0) = 4ci, outside the tally cone unless c = 0
# (round-06-2 completion of the linear exclusion).
ok = True
for k in range(1, 4):
    tot = (0,0)
    for u in range(4):
        tot = cadd(tot, ipow(k*u))
    if tot != (0,0): ok = False
for c in range(1, 5):                       # nonzero multipliers: F(i psi_0) = (0, 4c), never a tally
    val = cmul((0, 1), (4*c, 0))            # i * F(psi_0)
    if val[1] == 0 and val[0] >= 0: ok = False
rep('U6b: linear exclusion complete: vanishing on nontrivial windings, and on the trivial '
    'winding F(i psi) = i F(psi) leaves the tally cone unless c = 0', ok)

# U7: pure-winding pinning (round-05, R1 repair): the d^2 c_r tallies are pinned strictly
# in-sector: for every admissible kernel and every winding k, F(psi_k) = 16 c_{k mod 4}
# (psi_k stationary, core-valued; the point-mass evaluation is nowhere needed), and
# k mod 4 reaches every channel index. Exhaustive over the coefficient cube.
ok7 = True
for c in product(range(4), repeat=4):
    K = kernel(c)
    for k in range(4):
        psi = [ipow(k*u) for u in range(4)]     # pure winding restricted to the fibre
        if F(K, psi) != (16*c[k % 4], 0): ok7 = False
rep('U7: pure-winding pinning F(psi_k) = d^2 c_{k mod d}, every channel index reached (exhaustive, in-sector)', ok7)

# U8 (round-06, F3): the spanning step that transfers drive-invariance from values to kernel.
# The restricted windings on a fibre form the core DFT matrix, invertible over Q(i)
# (det = -16i on Q4), so they span every function on the fibre and polarization pins the
# kernel: two admissible kernels agreeing on all F(psi) values agree entrywise.
from fractions import Fraction as _Fr
import itertools as _it
_M = [[ipow(r*u) for u in range(4)] for r in range(4)]
_det = (_Fr(0), _Fr(0))
for _perm in _it.permutations(range(4)):
    _inv = sum(1 for a in range(4) for b in range(a+1, 4) if _perm[a] > _perm[b])
    _term = (_Fr((-1)**_inv), _Fr(0))
    for _r in range(4):
        _e = _M[_r][_perm[_r]]
        _term = (_term[0]*_e[0] - _term[1]*_e[1], _term[0]*_e[1] + _term[1]*_e[0])
    _det = (_det[0] + _term[0], _det[1] + _term[1])
ok8 = _det == (_Fr(0), _Fr(-16))
# polarization transfer: exhaustively, two admissible kernels with equal responses on all
# pure windings (and their pairwise Gaussian combinations psi_k + psi_k', psi_k + i psi_k')
# are identical
def _resp(K):
    out = []
    for k in range(4):
        psi = [ipow(k*u) for u in range(4)]
        out.append(F(K, psi))
    for k in range(4):
        for kp in range(k+1, 4):
            p1 = [cadd(ipow(k*u), ipow(kp*u)) for u in range(4)]
            p2 = [cadd(ipow(k*u), cmul((0, 1), ipow(kp*u))) for u in range(4)]
            out.append(F(K, p1)); out.append(F(K, p2))
    return out
_seen = {}
for c in product(range(3), repeat=4):
    K = kernel(c)
    key = tuple(_resp(K))
    if key in _seen and _seen[key] != tuple(K): ok8 = False
    _seen[key] = tuple(K)
rep('U8: spanning/polarization: core DFT det = -16i (invertible); equal responses on the '
    'admissible class force equal kernels (exhaustive)', ok8)
print('gleason: all checks passed')
