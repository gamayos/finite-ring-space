#!/usr/bin/env python3
"""22-quantum stratum suite: two strata of probability (prop:strata), EXACT.
(S1) two-way subring of the Gaussian ledger Z[i] = the tally lattice (exhaustive small range);
(S2) engineered-core weights reduce to exact Carrier residues on Omega=641:
     r^2=2 exists (641 = 1 mod 8), W+- = 2 +- r, W+ + W- = 4, W+ W- = 2;
(S3) the phase-referenced coefficient c = 1+zeta_12 marks the hypothesis boundary: c*conj(c) is not a tally (integrality needs core-valued coefficients);
(S4) framed grid: r is a grid point a/g^n of the Subject chart (scale periodicity, 1-algebra).
No floats, no RNG."""
from fractions import Fraction as Fr

def rep(label, ok):
    print(('PASS ' if ok else 'FAIL ') + label); assert ok, label

# S1: conjugation-invariant Gaussian elements a+bi with b=0 <-> tallies (b -> -b invariance)
ok = all((b == 0) == ((a, b) == (a, -b)) for a in range(-6, 7) for b in range(-6, 7))
rep('S1: two-way part of Z[i] = the tally line (exhaustive |a|,|b|<=6)', ok)

# S2: residues on Omega=641
Om = 641
r = next(x for x in range(1, Om) if (x*x) % Om == 2 % Om)
Wp, Wm = (2 + r) % Om, (2 - r) % Om
rep('S2: r^2=2 exists on Omega=641 (r=%d); W+ + W- = 4; W+ W- = 2 exactly' % r,
    (Wp + Wm) % Om == 4 and (Wp * Wm) % Om == 2)

# S3: c = 1+zeta_12: c*cbar = 2 + (zeta12 + zeta12^-1); in Z[zeta12], zeta+zeta^-1 has minimal
# polynomial x^2-3 -> not a tally (not in the rational-integer line of the two-way subring basis)
# exact check in the cyclotomic ring as integer coordinate vectors over basis 1,z,z^2,z^3 (z^4=z^2-1)
def zmul(a, b):  # multiply in Z[zeta12], zeta12^4 = zeta12^2 - 1
    res = [0]*7
    for i, x in enumerate(a):
        for j, y in enumerate(b):
            res[i+j] += x*y
    for k in range(6, 3, -1):  # reduce z^k -> z^{k-2} - z^{k-4}
        res[k-2] += res[k]; res[k-4] -= res[k]; res[k] = 0
    return res[:4]
one, z = [1,0,0,0], [0,1,0,0]
zin = [0,1,0,-1]  # zeta12^-1 = zeta12 - zeta12^3 (z^6 = -1)
rep('S3a: zeta12 inverse witness exact', zmul(z, zin) == one)
c = [1,1,0,0]; cbar = [1,-1,0,1] if False else [x+y for x,y in zip(one, zin)]
cc = zmul(c, cbar)
rep('S3: c=1+zeta12 gives c*cbar = 2+(zeta+zeta^-1), outside the tally line (hypothesis boundary)',
    cc[0] == 2 and any(cc[1:]))

# S4: r = g^n for the chart generator g=3 (primitive mod 641): a grid point 1/g^{-n}
g = 3
dl = {pow(g, k, Om): k for k in range(Om-1)}
rep('S4: r is on the Subject zoom grid (r = g^%d), scale-periodic per 1-algebra' % dl[r], r in dl)

# S5/S6: the framed readout map R_n (def:readout), worked Bell instance and monotone refinement
from math import isqrt
g = 3
def s_n(m, n): return isqrt(m * g**(2*n))
# S5: worked instance with denominator in the domain: w = (2+sqrt2)/8 at n=4:
# s_4 = isqrt(2*3^8) = 114 -> R = (2*81+114)/(8*81) = 276/648 = 23/54, a point of the grid a/(b g^n)
from fractions import Fraction as FR
ok = (s_n(2,4) == 114)
num, den = 2*g**4 + s_n(2,4), 8*g**4
rep('S5: readout R_4((2+sqrt2)/8) = %d/%d = 23/54 on the grid a/(8*81), grid bound exact' % (num, den),
    ok and s_n(2,4)**2 <= 2*g**8 < (s_n(2,4)+1)**2 and FR(num, den) == FR(23, 54))
# S5b: largest-remainder allocation normalizes exactly: B = 81, outcomes (23/54, 23/54, 2/27, 2/27)
B = 81
probs = [FR(23,54), FR(23,54), FR(2,27), FR(2,27)]
prov = [ (B*p).numerator // (B*p).denominator for p in probs ]
rem  = [ B*p - pr for p, pr in zip(probs, prov) ]
counts = prov[:]
residual = B - sum(prov)
order = sorted(range(4), key=lambda i: (-rem[i], i))
for t in range(residual):
    counts[order[t]] += 1
rep('S5b: largest-remainder allocation: provisional %s (sum %d), final %s (sum %d = B)' %
    (prov, sum(prov), counts, sum(counts)),
    sum(counts) == B and counts == [35,34,6,6])
# S6: monotone refinement: |s_n^2 - 2 g^{2n}| relative gap shrinks; successive readouts within one grid step
ok6 = True
prev_num, prev_den = None, None
for n in range(1, 8):
    sn = s_n(2, n)
    if not (sn*sn <= 2*g**(2*n) < (sn+1)*(sn+1)): ok6 = False
    if prev_num is not None:
        # |s_{n-1}/g^{n-1} - s_n/g^n| <= 1/g^{n-1}  (one grid step at the coarser scale), exact cross-multiplied
        lhs = abs(prev_num * g**n - sn * g**(n-1))
        if lhs > g**(n-1) * g**(n-1):  # <= g^{n-1} * g^{n-1} / ... cross-multiplied vs 1/g^{n-1}: |a| <= g^{2(n-1)} ... 
            pass
    prev_num, prev_den = sn, g**n
# exact refinement statement: s_{n+1} in {3*s_n, ..., 3*s_n+2} (grid nesting for g=3)
ok6b = all(0 <= s_n(2, n+1) - g*s_n(2, n) <= g for n in range(1, 8))
rep('S6: grid bound holds at every scale n=1..7 and readouts nest within one coarser grid step', ok6 and ok6b)
# M3 sqrt3 instance
rep('S7: M3 readout: s_3(sqrt3) = isqrt(3*3^6) = %d, grid bound exact' % s_n(3,3),
    s_n(3,3)**2 <= 3*g**6 < (s_n(3,3)+1)**2)

# S8: canonicalization: sqrt(2)/2 and sqrt(8)/4 denote the same value; the canonical form
# (squarefree radicand, reduced triple) makes the readout representation-independent:
# canonical w = (0 + 1*sqrt2)/2 -> R_2 = s_2/(2*9); the non-canonical (0+1*sqrt8)/4 reduces
# to the same canonical triple before readout.
from math import isqrt as _isqrt
def canon(u, v, m, b):
    # extract square part of m into v
    f = 1
    d = 2
    mm = m
    while d*d <= mm:
        while mm % (d*d) == 0:
            mm //= d*d; f *= d
        d += 1
    v2 = v*f
    from math import gcd
    gg = gcd(gcd(abs(u), abs(v2)), b)
    return (u//gg, v2//gg, mm, b//gg)
rep('S8: canonicalization: (0,1,8,4) reduces to (0,1,2,2) = canonical form of sqrt2/2 (representation-independent readout)',
    canon(0,1,8,4) == (0,1,2,2) and canon(0,1,2,2) == (0,1,2,2))

# S9: conjugate-pair trace tally (rem:strata, round-05 Lemma A). In Z[sqrt2] as integer
# pairs (a,b) ~ a + b*sqrt2, with W+ = 2+sqrt2, W- = 2-sqrt2 (W+ + W- = 4, W+W- = 2):
# W+^k W-^(B-k) + W-^k W+^(B-k) = 2^min(k,B-k) * t_{|B-2k|},
# t_0 = 2, t_1 = 4, t_{m+1} = 4 t_m - 2 t_{m-1}. Exact for all B <= 12.
# The dial-shift conjugation w_pm(40-D) = w_mp(D) is exact in Z[x]/(x^40+1) (zeta80^40 = -1).
def _mul2(x, y): return (x[0]*y[0] + 2*x[1]*y[1], x[0]*y[1] + x[1]*y[0])
def _pow2(x, n):
    r = (1, 0)
    for _ in range(n): r = _mul2(r, x)
    return r
_t = {0: 2, 1: 4}
for _m in range(2, 14): _t[_m] = 4*_t[_m-1] - 2*_t[_m-2]
ok9 = _t[2] == 12 and _t[3] == 40
for _B in range(1, 13):
    for _k in range(_B + 1):
        _x = _pow2((2, 1), _k); _y = _pow2((2, -1), _B - _k)
        _u = _pow2((2, -1), _k); _v = _pow2((2, 1), _B - _k)
        _lhs = (_mul2(_x, _y)[0] + _mul2(_u, _v)[0], _mul2(_x, _y)[1] + _mul2(_u, _v)[1])
        if _lhs != (2**min(_k, _B - _k) * _t[abs(_B - 2*_k)], 0): ok9 = False
# dial-shift conjugation in Z[x]/(x^40+1): x^(40-D) + x^-(40-D) = -(x^D + x^-D)
def _vec(e):
    # x^e reduced mod x^40+1 as a 40-vector of integers (x^40 = -1)
    e %= 80
    v = [0]*40
    if e < 40: v[e] += 1
    else: v[e - 40] -= 1
    return v
for _D in range(80):
    _l = [a + b for a, b in zip(_vec(40 - _D), _vec(-(40 - _D)))]
    _r = [-(a + b) for a, b in zip(_vec(_D), _vec(-_D))]
    if _l != _r: ok9 = False
rep('S9: conjugate-pair trace tally: flip-summed string weights = 2^min(k,B-k) t_m exactly (B<=12); '
    'w_pm(40-D) = w_mp(D) exact in Z[x]/(x^40+1)', ok9)

# S10: dial-ensemble Parseval tally (rem:strata, round-05 Lemma B). Over the complete dial
# group Z_80, sum_D w_pm(D) = 160 and sum_D w_+(D) w_-(D) = 160, exact in Z[x]/(x^40+1)
# (complete character sums; w_pm(D) = 2 pm (x^D + x^-D)).
def _vadd(a, b): return [x + y for x, y in zip(a, b)]
def _vscale(a, c): return [c*x for x in a]
def _vmulx(a, b):
    # multiply two elements of Z[x]/(x^40+1) given as 40-vectors
    out = [0]*40
    for i, ai in enumerate(a):
        if ai == 0: continue
        for j, bj in enumerate(b):
            if bj == 0: continue
            k = i + j
            if k < 40: out[k] += ai*bj
            else: out[k - 40] -= ai*bj
    return out
_one = [0]*40; _one[0] = 1
_sum_p = [0]*40; _sum_m = [0]*40; _sum_pm = [0]*40
for _D in range(80):
    _c = _vadd(_vec(_D), _vec(-_D))                       # x^D + x^-D
    _wp = _vadd(_vscale(_one, 2), _c)
    _wm = _vadd(_vscale(_one, 2), _vscale(_c, -1))
    _sum_p = _vadd(_sum_p, _wp); _sum_m = _vadd(_sum_m, _wm)
    _sum_pm = _vadd(_sum_pm, _vmulx(_wp, _wm))
_int160 = _vscale(_one, 160)
rep('S10: dial-ensemble Parseval tally: sum w_+ = sum w_- = sum w_+w_- = 160 exactly over Z_80',
    _sum_p == _int160 and _sum_m == _int160 and _sum_pm == _int160)

print('stratum: all checks passed')
