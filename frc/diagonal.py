"""frc.diagonal — the diagonal under finitude: the names a dense coding spends, the threshold, the decoders and the
dense-coded instance (the logic theme; 25-godel's migration, 20 October 2026).

Moved from the package src/25-godel/godel.py (block D's name count, block G's `_dense`), which stays the paper's published
witness until its release pins the framework. Everything is exact: integer arithmetic, written formulas as strings, a model
checker on small prime fields. The Lean side is lean/FrcCore/Theme/Diagonal.lean (the syntax, mention cost, the decoders)
and Theme/Threshold.lean (the name-cost bound, k*, the threshold).

* `name_cost(k, a)`: the total length of the k shortest names over a letters; `delta_names`, `lambda_names`: the least
  name cost of δ and λ with k coordinates in v and k₁ in u (25:F4); `admits(k, k1, d, a)`: the name count leaves an
  instance open in digit form; `k_star(a, d)`, `threshold(a, d)`: the largest admitted k below 6a^(⌊d/3⌋+1) and t = d·k*
  (25:F6), the same search as the Lean's `kstar`; `fit_table`, `last_k`: the one-scale threshold by bisection.
* `dense()`: the formulas of 25:F7 and F8 (Int_J, inrange, Pow, Dig, the access formulas, Diag), their printer over the
  32-symbol alphabet, the independent reader, a model checker for small prime fields with range hints, and the instance
  as strings at D symbols per element; returned as a namespace. `deep(fn)` runs fn with the stack and recursion limit the
  nested formulas need (`threading`, no arithmetic).
"""
import sys, itertools, math, random, threading

def name_cost(k, a):
    """The total length of the k shortest distinct names over an alphabet of a letters: a names of one letter, a^2 of two, …"""
    cost, L = 0, 1
    while k > 0:
        take = min(k, a ** L); cost += take * L; k -= take; L += 1
    return cost

def delta_names(k, k1, a):
    """The least total length of the variable names in the diagonal formula delta(u) = Ev (Diag(u, v) & theta(v)) with k
    coordinates in v and k1 in u: k + k1 distinct variables, each coordinate of v named three times (the block, Diag, theta)
    and each of u once (Diag).  Of k + k1 distinct names the k + k1 shortest cost least, and the weight 3 goes to the k
    shortest of them."""
    return 2 * name_cost(k, a) + name_cost(k + k1, a)

def lambda_names(k, k1, a):
    """The least number of symbols the coordinates cost in lambda = delta(code of delta): each coordinate of v named three
    times, and a closed term of at least one symbol in each of the k1 places of u."""
    return 3 * name_cost(k, a) + k1

def admits(k, k1, d, a):
    """The name count leaves an instance open, in digit form: lambda's symbols fit a code of k coordinates and delta's a
    code of k1, a code of j coordinates over a structure of d digits holding fewer than d*j letters."""
    return lambda_names(k, k1, a) < d * k and delta_names(k, k1, a) < d * k1

def fit_table(m, a, d, upto):
    """[n_0, n_1, …, n_upto], n_j the largest n with a^n <= m^j: the longest strings an injective coding by j-tuples can
    reach.  For a^(d-1) <= m < a^d each step adds d - 1 or d."""
    out, P, Q, n = [0], 1, 1, 0
    for _ in range(upto):
        P *= m; Q *= a ** (d - 1); n += d - 1
        if Q * a <= P: Q *= a; n += 1
        assert Q <= P < Q * a
        out.append(n)
    return out

def last_k(w, a, strict=False):
    """The largest k with delta_names(k, k, a) <= w*k (< w*k if strict), 0 if none: the template at one scale.
    delta_names(k, k)/k does not decrease with k (proved in the comment of block D; D5 checks it for a = 2..5, k <= 20000),
    so the k that pass form an initial segment and bisection finds its end.  The doubling stops because the quotient is
    unbounded (bound (i) there)."""
    good = (lambda k: delta_names(k, k, a) < w * k) if strict else (lambda k: delta_names(k, k, a) <= w * k)
    if not good(1): return 0
    lo, hi = 1, 2
    while good(hi): hi *= 2
    while lo < hi - 1:
        mid = (lo + hi) // 2
        if good(mid): lo = mid
        else: hi = mid
    return lo

def k_star(a, d):
    """k*(M) for a structure of d base-a digits: the largest k below 6a^(floor(d/3)+1) that some k1 admits, 0 if none (25:F6;
    the Lean's `FRC.Diagonal.kstar`). By λ's count an admitted k1 lies below d*k - 3*name_cost(k, a)."""
    J = d // 3 + 1
    best = 0
    for k in range(1, 6 * a ** J):
        bound = d * k - 3 * name_cost(k, a)
        if bound > 0 and any(admits(k, k1, d, a) for k1 in range(bound)): best = k
    return best

def threshold(a, d):
    """t(M) = d * k*(M) (25:F6)."""
    return d * k_star(a, d)

def deep(fn):
    """Run fn in a thread with a large stack: the formulas of block G nest tens of thousands of quantifiers."""
    box = {}
    def run():
        try: box["r"] = fn()
        except BaseException as e: box["e"] = e
    lim, stack = sys.getrecursionlimit(), threading.stack_size()
    sys.setrecursionlimit(1 << 22); threading.stack_size(1 << 29)
    try:
        t = threading.Thread(target=run); t.start(); t.join()
    finally:
        sys.setrecursionlimit(lim); threading.stack_size(stack)
    if "e" in box: raise box["e"]
    return box.get("r")

class Dense:
    """The namespace dense() returns: its formulas, printer, reader, model checker and instance builders as attributes."""
    def __init__(self, **kw): self.__dict__.update(kw)

# The dense-coded instance of 25:F7, F8 and G8 (Section 5.2, Lemma decoders, Theorem instance, Corollary windowtruth).
#
# Language: +, * and the constants 0, ..., f (the elements 0..15) and g (16), over the field F_p.  Alphabet: the 32 symbols
# of SYMS.  A variable is a letter (u, v, x) and an index of fixed width.  A string is coded D symbols per element in
# base 32, the pad symbol being the digit 0.  The proofs, for every prime under the stated side conditions:
#   (1) seg_J(x, w) <=> x = w n for some 0 <= n < 2^J.  J = 0: x = 0.  Step: x = y + b w with b in {0, 1} and
#       y = 2w n', so x = w (2n' + b).  Int_J(x) = seg_J(x, 1): for 2^J <= p it defines {0, ..., 2^J - 1}.
#   (2) inrange(t, N), for N <= 2^E and 2^(E+1) < p: t and m lie in [0, 2^E) and t + m + 1 = N in F_p; both sides are
#       below p as integers, so the equation holds in the integers and t < N.  Conversely m = N - 1 - t.
#   (3) Pow(r, z), for 2^e <= p: by induction r = w sum b_j 2^j and z = prod c^(2^j b_j) for bits b_j; the bits of r are
#       unique, so z = beta^r and r < 2^e.
#   (4) Dig(y, r, s), for 2^(b n + 1) < p, n <= 2^e, 2^(e+1) <= p: if it holds then r < n, z = beta^r, z2 = beta^(n-1-r),
#       s < beta, lo < z, hi < z2, so lo + z (s + beta hi) is an integer below beta^n < p and equals y: s is digit r
#       of y.  Conversely the digits of y < beta^n are witnesses.
#   (5) Diag(u, v), for p > 2^(5D+5) and every u_j < 32^D: the auxiliary variables are confined by (2) and by the
#       access formulas to ranges below 2^E, so every equation among them is an equation of integers.  The cases (copy
#       before the blocks, in a block before and after the token, after the blocks; numeral; pad) partition the positions
#       below D k, and in each the symbol is unique.  The clause on v forces every v_i < 32^D by (4).  So Diag(u, v)
#       holds iff v codes F(u): the string of u with the token of u_i replaced by the numeral of the element u_i.
#   (6) The fixed point: delta carries its own layout constants as numerals of fixed width.  The numerals of lambda denote
#       the coordinates of the code of delta.  By (5), Diag(code delta, v) holds iff v = code lambda.  So
#       F_p |= lambda iff theta(code lambda).
def dense():
    """The formulas of block G, their printer, a model checker for small prime fields, and the instance as strings."""
    SYMS = " 0123456789abcdefg+*=()&|~EAuvx>"          # code = index; ' ' pads
    assert len(SYMS) == 32 and len(set(SYMS)) == 32
    CODE = {c: i for i, c in enumerate(SYMS)}
    HEX = "0123456789abcdef"
    CONSTVAL = {c: i for i, c in enumerate(HEX)}; CONSTVAL['g'] = 16
    HINT = {}                                            # id(formula) -> (variable, bound term, formula): the formula implies 0 <= variable < bound

    def V(n): return ('var', n)
    def C(ch): return ('const', ch)
    def add(a, b): return ('add', a, b)
    def mul(a, b): return ('mul', a, b)
    def eq(a, b): return ('eq', a, b)
    def AND(*fs): return ('and', list(fs))
    def OR(*fs): return ('or', list(fs))
    def imp(a, b): return ('imp', a, b)
    def al(n, f): return ('all', n, f)
    def ex(names, f):
        for n in reversed(names if isinstance(names, (list, tuple)) else [names]): f = ('ex', n, f)
        return f
    ZERO, ONE = C('0'), C('1')

    def num(n, width):
        """The Horner numeral of n in base 16 with exactly `width` digits: (c0+(g*(c1+(g*( ... 0)))))."""
        assert 0 <= n < 16 ** width, (n, width)
        t = ZERO
        for i in reversed(range(width)): t = add(C(HEX[(n >> (4 * i)) & 15]), mul(C('g'), t))
        return t

    def numstr(n, width):
        return "".join("(" + HEX[(n >> (4 * i)) & 15] + "+(g*" for i in range(width)) + "0" + "))" * width

    def pr(node, out, sub=None):
        k = node[0]
        if k == 'var': out.append(sub.get(node[1], node[1]) if sub else node[1])
        elif k == 'const': out.append(node[1])
        elif k in ('add', 'mul'):
            out.append('('); pr(node[1], out, sub); out.append('+' if k == 'add' else '*'); pr(node[2], out, sub); out.append(')')
        elif k == 'eq': pr(node[1], out, sub); out.append('='); pr(node[2], out, sub)
        elif k in ('and', 'or'):
            out.append('(')
            for i, f in enumerate(node[1]):
                if i: out.append('&' if k == 'and' else '|')
                pr(f, out, sub)
            out.append(')')
        elif k == 'imp': out.append('('); pr(node[1], out, sub); out.append('>'); pr(node[2], out, sub); out.append(')')
        elif k == 'not': out.append('~'); pr(node[1], out, sub)
        else: out.append('E' if k == 'ex' else 'A'); out.append(node[1]); pr(node[2], out, sub)

    def show(node, sub=None):
        out = []; pr(node, out, sub); return "".join(out)

    # -- the model checker
    class Ev:
        """Truth of a formula in the field F_p.  A quantifier runs over a candidate set that contains every value of its
        variable on which the body (for a universal: the guard of the implication) can hold; each candidate is then
        evaluated in full.  Candidates come from equations solved for the variable (cand), or from a registered range
        (HINT), which Part 1 verifies exhaustively on the same field."""
        def __init__(s, p, naive=False): s.p = p; s.memo = {}; s.fvc = {}; s.fvt = {}; s.ct = {}; s.hints_used = 0; s.naive = naive
        def fv(s, n):
            r = s.fvc.get(id(n))
            if r is not None: return r[1]
            k = n[0]
            if k == 'var': r = frozenset([n[1]])
            elif k == 'const': r = frozenset()
            elif k in ('add', 'mul', 'eq', 'imp'): r = s.fv(n[1]) | s.fv(n[2])
            elif k in ('and', 'or'): r = frozenset().union(*[s.fv(f) for f in n[1]])
            elif k == 'not': r = s.fv(n[1])
            else: r = s.fv(n[2]) - {n[1]}
            s.fvc[id(n)] = (n, r); return r          # the node is kept alive, so its id is never reused
        def tv(s, t, env):
            k = t[0]
            if k == 'var': return env[t[1]]
            if k == 'const': return CONSTVAL[t[1]] % s.p
            closed = not s.fv(t)
            if closed and id(t) in s.ct: return s.ct[id(t)]
            a = s.tv(t[1], env); b = s.tv(t[2], env)
            r = (a + b) % s.p if k == 'add' else (a * b) % s.p
            if closed: s.ct[id(t)] = r
            return r
        def ok(s, t, env, blocked): return all(v in env and v not in blocked for v in s.fv(t))
        def solve(s, x, e, env, blocked):
            A, B = e[1], e[2]
            ia, ib = x in s.fv(A), x in s.fv(B)
            if ia == ib: return None
            if ib: A, B = B, A
            if not s.ok(B, env, blocked): return None
            tgt = s.tv(B, env); t = A
            while t[0] != 'var':
                l, r = t[1], t[2]
                il, ir = x in s.fv(l), x in s.fv(r)
                if il and ir: return None
                other, nxt = (r, l) if il else (l, r)
                if not s.ok(other, env, blocked): return None
                ov = s.tv(other, env)
                if t[0] == 'add': tgt = (tgt - ov) % s.p
                else:
                    if ov == 0: return None
                    tgt = tgt * pow(ov, -1, s.p) % s.p
                t = nxt
            return {tgt}
        def cand(s, x, f, env, blocked):
            k = f[0]
            if k == 'eq': return s.solve(x, f, env, blocked)
            if k == 'and':
                res = None
                for g in f[1]:
                    if x not in s.fv(g):
                        if g[0] == 'eq' and s.ok(g, env, blocked) and s.tv(g[1], env) != s.tv(g[2], env): return set()
                        continue
                    c = s.cand(x, g, env, blocked)
                    if c is not None: res = c if res is None else (res & c)
                return res
            if k == 'or':
                res = set()
                for g in f[1]:
                    if x not in s.fv(g): return None
                    c = s.cand(x, g, env, blocked)
                    if c is None: return None
                    res |= c
                return res
            if k == 'ex':
                if f[1] == x: return None
                return s.cand(x, f[2], env, blocked | {f[1]})
            return None
        def domain(s, x, f, env):
            if s.naive: return range(s.p)                 # every quantifier over the whole field
            c = s.cand(x, f, env, frozenset())
            if c is not None: return c
            h = HINT.get(id(f))
            if h is not None and h[0] == x and s.ok(h[1], env, frozenset()): s.hints_used += 1; return range(s.tv(h[1], env))
            return range(s.p)
        def ev(s, f, env):
            k = f[0]
            if k == 'eq': return s.tv(f[1], env) == s.tv(f[2], env)
            if k == 'and':
                for g in f[1]:
                    if not s.ev(g, env): return False
                return True
            if k == 'or':
                for g in f[1]:
                    if s.ev(g, env): return True
                return False
            if k == 'not': return not s.ev(f[1], env)
            if k == 'imp': return (not s.ev(f[1], env)) or s.ev(f[2], env)
            fl = s.fvt.get(id(f))
            if fl is None: fl = s.fvt[id(f)] = tuple(sorted(s.fv(f)))
            key = (id(f),) + tuple(env[v] for v in fl)
            r = s.memo.get(key)
            if r is not None: return r
            x, body = f[1], f[2]
            had = x in env; old = env.get(x)
            if k == 'ex':
                r = False
                for val in s.domain(x, body, env):
                    env[x] = val
                    if s.ev(body, env): r = True; break
            else:
                r = True
                for val in (s.domain(x, body[1], env) if body[0] == 'imp' else range(s.p)):
                    env[x] = val
                    if not s.ev(body, env): r = False; break
            if had: env[x] = old
            else: env.pop(x, None)
            s.memo[key] = r; return r

    # -- the formulas
    class Gen:
        def __init__(s, wx=2, cw=10): s.wx = wx; s.cw = cw
        def X(s, i): return 'x' + format(i, '0%dx' % s.wx)
        def K(s, n): return num(n, s.cw)
        # -- x in {w*n : 0 <= n < 2^J}
        def seg(s, x, w, J, P, Q):
            if J == 0: return eq(V(x), ZERO)
            y, w2 = P
            return ex(y, AND(OR(eq(V(x), V(y)), eq(V(x), add(V(y), V(w)))),
                             ex(w2, AND(eq(V(w2), add(V(w), V(w))), s.seg(y, w2, J - 1, Q, P)))))
        # -- Int_J(t): t in [0, 2^J)     (true initial segment when 2^J <= p)
        def Int(s, t, J):
            X, W = s.X(0), s.X(1)
            return ex([X, W], AND(eq(V(X), t), eq(V(W), ONE), s.seg(X, W, J, (s.X(2), s.X(3)), (s.X(4), s.X(5)))))
        # -- 0 <= t < N, for N <= 2^E and 2^(E+1) < p
        def inrange(s, t, N, E):
            m, om = s.X(18), s.X(19)
            return ex(m, AND(eq(add(add(t, V(m)), ONE), N),
                             al(om, imp(OR(eq(V(om), t), eq(V(om), V(m))), s.Int(V(om), E)))))
        # -- z = (2^bbits)^r and 0 <= r < 2^e; needs 2^e <= p (the binary expansion of r is then unique)
        def powrec(s, r, z, c, w, e, A, B):
            if e == 0: return AND(eq(V(r), ZERO), eq(V(z), ONE))
            r1, z1, w2, c2 = A
            return ex([r1, z1], AND(OR(AND(eq(V(r), V(r1)), eq(V(z), V(z1))),
                                       AND(eq(V(r), add(V(r1), V(w))), eq(V(z), mul(V(z1), V(c))))),
                                    ex([w2, c2], AND(eq(V(w2), add(V(w), V(w))), eq(V(c2), mul(V(c), V(c))),
                                                     s.powrec(r1, z1, c2, w2, e - 1, B, A)))))
        def Pow(s, rt, zt, bbits, e):
            R, Z, Cc, W = (s.X(i) for i in (6, 7, 8, 9))
            A = tuple(s.X(i) for i in (10, 11, 12, 13)); B = tuple(s.X(i) for i in (14, 15, 16, 17))
            return ex([R, Z, Cc, W], AND(eq(V(R), rt), eq(V(Z), zt), eq(V(Cc), num(1 << bbits, 2)), eq(V(W), ONE),
                                         s.powrec(R, Z, Cc, W, e, A, B)))
        # -- st is digit number rt of yt in base 2^bbits, for yt < (2^bbits)^nd; needs 2^(bbits*nd+1) < p, nd <= 2^e and 2^(e+1) <= p
        def Dig(s, yt, rt, st, bbits, nd, e):
            z, z2, lo, hi, m1, m2, om, r2 = (s.X(i) for i in range(20, 28))
            beta = num(1 << bbits, 2); J = bbits * nd
            ints = al(om, imp(OR(eq(V(om), V(lo)), eq(V(om), V(m1)), eq(V(om), V(hi)), eq(V(om), V(m2))), s.Int(V(om), J)))
            f4 = ex([m1, m2], AND(eq(add(add(V(lo), V(m1)), ONE), V(z)), eq(add(add(V(hi), V(m2)), ONE), V(z2)), ints))
            f3 = ex([lo, hi], AND(eq(yt, add(V(lo), mul(V(z), add(st, mul(beta, V(hi)))))), f4))
            f2 = ex(z2, AND(s.Pow(V(r2), V(z2), bbits, e), f3))
            f1 = ex(z, AND(s.Pow(rt, V(z), bbits, e), f2))
            return ex(r2, AND(eq(add(add(rt, V(r2)), ONE), s.K(nd)), s.inrange(st, beta, bbits), f1))
        def access(s, jv, xv, cls, cnt, wtok, iw):
            return ('or', [AND(eq(V(jv), num(i, iw)), eq(V(xv), V(cls + format(i, '0%dx' % wtok)))) for i in range(cnt)])
        # -- Diag(u, v): the string coded by v is the string coded by u with the token of u_i replaced by the numeral of u_i
        def diag(s, P):
            q, i, r, y, sv, j, x, rr, t, io, ro, h, o, c, qs, mm = (s.X(n) for n in range(32, 48))
            D, k, k1, H, S, B, R0, WU, N1, E = (P[n] for n in 'D k k1 H S B R0 WU N1 E'.split())
            W = 8 * H + 1; B2 = B - WU + W; NL = N1 + k1 * (W - WU); NOUT = D * k
            assert NL <= NOUT <= 1 << E and S + k1 * B <= N1 <= D * k1 and R0 + WU <= B
            K = s.K; cd = P['codes']; sym = lambda ch: K(cd[ch])
            rng = lambda tt, n: s.inrange(tt, K(n), E)
            digA = lambda yt, rt, st: s.Dig(yt, rt, st, P['SB'], D, P['ea'])
            digH = lambda yt, rt, st: s.Dig(yt, rt, st, P['NB'], H, P['eh'])
            def exr(xn, n, *conj):
                body = AND(rng(V(xn), n), *conj); HINT[id(body)] = (xn, K(n), body); return ('ex', xn, body)
            numsym = OR(
                exr(h, H, ex(o, AND(eq(V(t), add(mul(V(h), K(6)), V(o))), rng(V(o), 6),
                    OR(AND(eq(V(o), K(0)), eq(V(sv), sym('('))),
                       AND(eq(V(o), K(1)), ex(c, AND(digH(V(x), V(h), V(c)), eq(V(sv), add(V(c), sym('0')))))),
                       AND(eq(V(o), K(2)), eq(V(sv), sym('+'))),
                       AND(eq(V(o), K(3)), eq(V(sv), sym('('))),
                       AND(eq(V(o), K(4)), eq(V(sv), sym('g'))),
                       AND(eq(V(o), K(5)), eq(V(sv), sym('*'))))))),
                AND(eq(V(t), K(6 * H)), eq(V(sv), sym('0'))),
                exr(mm, 2 * H, eq(V(t), add(K(6 * H + 1), V(mm))), eq(V(sv), sym(')'))))
            src = OR(AND(rng(V(q), S), eq(V(qs), V(q))),
                     exr(io, k1, ex(ro, AND(eq(V(q), add(add(K(S), mul(V(io), K(B2))), V(ro))), rng(V(ro), R0),
                                            eq(V(qs), add(add(K(S), mul(V(io), K(B))), V(ro)))))),
                     exr(io, k1, ex(ro, AND(eq(V(q), add(add(K(S + R0 + W), mul(V(io), K(B2))), V(ro))), rng(V(ro), B2 - R0 - W),
                                            eq(V(qs), add(add(K(S + R0 + WU), mul(V(io), K(B))), V(ro)))))),
                     exr(mm, N1 - S - k1 * B, eq(V(q), add(K(S + k1 * B2), V(mm))), eq(V(qs), add(K(S + k1 * B), V(mm)))))
            copy = exr(rr, D, ex(qs, AND(eq(V(qs), add(mul(V(j), K(D)), V(rr))), src, digA(V(x), V(rr), V(sv)))))
            numc = ex(t, AND(eq(V(q), add(add(K(S + R0), mul(V(j), K(B2))), V(t))), rng(V(t), W), numsym))
            pad = ex(mm, AND(eq(V(q), add(K(NL), V(mm))), s.Int(V(mm), E), eq(V(sv), sym(' '))))
            out = OR(pad, ex([j, x], AND(s.access(j, x, 'u', k1, P['wu'], P['iwu']), OR(copy, numc))))
            body = ex([i, r], AND(eq(V(q), add(mul(V(i), K(D)), V(r))), rng(V(r), D),
                      ex(y, AND(s.access(i, y, 'v', k, P['wv'], P['iwv']), ex(sv, AND(digA(V(y), V(r), V(sv)), out))))))
            guard = rng(V(q), NOUT); HINT[id(guard)] = (q, K(NOUT), guard)
            return al(q, imp(guard, body))

    # -- the reference substitution, and an independent reader of printed formulas
    def F_ref(us, P):
        """The substitution on strings, from its definition (no case analysis on output positions)."""
        D, k, k1, H, S, B, R0, WU, N1 = (P[n] for n in 'D k k1 H S B R0 WU N1'.split())
        SB, NB, cd = P['SB'], P['NB'], P['codes']
        sin = [(us[q // D] >> (SB * (q % D))) & ((1 << SB) - 1) for q in range(N1)]
        def NUM(xv):
            o = []
            for hh in range(H): o += [cd['('], cd['0'] + ((xv >> (NB * hh)) & ((1 << NB) - 1)), cd['+'], cd['('], cd['g'], cd['*']]
            return o + [cd['0']] + [cd[')']] * (2 * H)
        out = sin[:S]
        for ii in range(k1):
            b = S + ii * B
            out += sin[b:b + R0] + NUM(us[ii]) + sin[b + R0 + WU:b + B]
        out += sin[S + k1 * B:N1]
        out += [cd[' ']] * (D * k - len(out))
        return out

    def pack(symlist, D, SB):
        return [sum(c << (SB * r) for r, c in enumerate(symlist[i:i + D])) for i in range(0, len(symlist), D)]

    def primes_upto(n): return [q for q in range(2, n + 1) if all(q % d for d in range(2, math.isqrt(q) + 1))]

    def read_back(s, wid):
        """An independent reader of a printed formula (fixed name widths `wid` per letter): the formula as a tree."""
        n = len(s); match = [0] * n; st = []
        for i, c in enumerate(s):
            if c == '(': st.append(i)
            elif c == ')': match[st.pop()] = i
        assert not st
        def paren_is_term(i):
            j = i + 1
            while True:
                c = s[j]
                if c == '(': j = match[j] + 1; continue
                if c in '+*': return True
                if c in '=&|>)': return False
                j += 1
        def term(i):
            c = s[i]
            if c in wid: w = wid[c]; return ('var', s[i:i + 1 + w]), i + 1 + w
            if c in CONSTVAL: return ('const', c), i + 1
            assert c == '(', (c, i)
            a, i = term(i + 1); op = s[i]; assert op in '+*'; b, i = term(i + 1); assert s[i] == ')'
            return ('add' if op == '+' else 'mul', a, b), i + 1
        def form(i):
            c = s[i]
            if c in 'EA':
                v, j = term(i + 1); assert v[0] == 'var'; f, j = form(j); return ('ex' if c == 'E' else 'all', v[1], f), j
            if c == '~': f, j = form(i + 1); return ('not', f), j
            if c == '(' and not paren_is_term(i):
                f, j = form(i + 1); fs = [f]; op = None
                while s[j] != ')':
                    assert s[j] in '&|>' and op in (None, s[j]); op = s[j]; f, j = form(j + 1); fs.append(f)
                if op == '>': assert len(fs) == 2; return ('imp', fs[0], fs[1]), j + 1
                return ('or' if op == '|' else 'and', fs), j + 1
            a, j = term(i); assert s[j] == '='; b, j = term(j + 1); return ('eq', a, b), j
        f, j = form(0); assert j == n; return f
    def same(a, b):
        stack = [(a, b)]
        while stack:
            a, b = stack.pop()
            if a[0] != b[0]:
                if {a[0], b[0]} == {'and', 'or'} and len(a[1]) == len(b[1]) == 1: stack.append((a[1][0], b[1][0])); continue
                return False
            k = a[0]
            if k in ('var', 'const'):
                if a[1] != b[1]: return False
            elif k in ('and', 'or'):
                if len(a[1]) != len(b[1]): return False
                stack.extend(zip(a[1], b[1]))
            elif k in ('ex', 'all'):
                if a[1] != b[1]: return False
                stack.append((a[2], b[2]))
            elif k == 'not': stack.append((a[1], b[1]))
            else: stack.append((a[1], b[1])); stack.append((a[2], b[2]))
        return True
    def free_vars(node):
        """The free variables of a formula or term, in one pass (a counter of the binders in force)."""
        free, bound, stack = set(), {}, [(node, 0)]
        while stack:
            n, leaving = stack.pop()
            if leaving: bound[n] -= 1; continue
            k = n[0]
            if k == 'var':
                if not bound.get(n[1]): free.add(n[1])
            elif k == 'const': pass
            elif k in ('and', 'or'): stack.extend((f, 0) for f in n[1])
            elif k in ('ex', 'all'): bound[n[1]] = bound.get(n[1], 0) + 1; stack.append((n[1], 1)); stack.append((n[2], 0))
            elif k == 'not': stack.append((n[1], 0))
            else: stack.append((n[1], 0)); stack.append((n[2], 0))
        return free
    def instance(D, k1, theta_of=None):
        """delta(u) = Ev (Diag(u, v) & theta(v)) at D symbols per element, as a formula and as a string.  The layout constants
        S and |delta| are written with fixed width, so writing them does not move the layout.  If delta does not fill u,
        the formula is None and the string is the one built with placeholder constants (of the same length)."""
        g = Gen(); SB, NB = 5, 4
        H = -(-SB * D // NB); W = 8 * H + 1
        wu, iwu, wv, iwv = 3, 3, 4, 4
        WU = 1 + wu; IDX = 8 * iwu + 1
        B = 1 + 3 + 1 + IDX + 1 + 3 + 1 + WU + 1 + 1; R0 = 1 + 3 + 1 + IDX + 1 + 3 + 1
        k = k1 + -(-k1 * (W - WU) // D)                    # v has room for the lambda of a delta that fills u
        assert k1 <= 16 ** wu and k <= 16 ** wv
        E = (D * k - 1).bit_length(); ea = (D - 1).bit_length(); eh = (H - 1).bit_length()
        assert D <= 1 << ea and H <= 1 << eh and NB * H <= SB * D + 3      # side conditions of Dig; p > 2^(5D+5) gives the rest
        vt = ['v%04x' % i for i in range(k)]; ut = ['u%03x' % i for i in range(k1)]
        if theta_of is None:                               # the sample theta: v_0 + ... + v_(k-1) = 0, which depends on every coordinate
            t = V(vt[0])
            for nm in vt[1:]: t = add(t, V(nm))
            theta = eq(t, ZERO)
        else: theta = theta_of(vt)
        P = dict(D=D, k=k, k1=k1, H=H, S=0, B=B, R0=R0, WU=WU, N1=D * k1, E=E, SB=SB, NB=NB, ea=ea, eh=eh, wu=wu, iwu=iwu, wv=wv, iwv=iwv, codes=CODE)
        s0 = show(ex(vt, AND(g.diag(P), theta)))
        P = dict(P, S=s0.index('u') - R0, N1=len(s0), W=W, theta_len=len(show(theta)))
        if len(s0) > D * k1: return g, P, None, None, s0, vt, ut
        dg = g.diag(P); delta = ex(vt, AND(dg, theta)); s = show(delta)
        assert len(s) == len(s0) and s.index('u') - R0 == P['S']
        return g, P, dg, delta, s, vt, ut
    def instance_checks(D, k1, theta_of=None, reader=True, sample=200000):
        """The instance as strings: a dict of verdicts and the numbers the labels state."""
        g, P, dg, delta, s, vt, ut = instance(D, k1, theta_of)
        k, H, S, B, R0, WU, N1, W = (P[n] for n in 'k H S B R0 WU N1 W'.split())
        B2 = B - WU + W; NL = N1 + k1 * (W - WU); r = dict(P=P, N1=N1, NL=NL, k=k)
        r['alphabet'] = set(s) <= set(SYMS) - {' '}
        r['fills_u'] = N1 <= D * k1
        r['tokens'] = s.count('u') == k1 and all(s[S + i * B + R0:S + i * B + R0 + WU] == ut[i] for i in range(k1))
        r['free'] = free_vars(delta) == set(ut) and free_vars(dg) == set(ut) | set(vt)
        r['reader'] = same(read_back(s, {'x': 2, 'u': 3, 'v': 4}), delta) if reader else None
        sp = s + ' ' * (D * k1 - N1)
        us = [sum(CODE[c] << (5 * q) for q, c in enumerate(sp[i * D:(i + 1) * D])) for i in range(k1)]
        r['code'] = all(u < 32 ** D for u in us) and "".join(SYMS[(us[q // D] >> (5 * (q % D))) & 31] for q in range(N1)) == s
        nums = [numstr(u, H) for u in us]
        r['numerals'] = (all(nums[i] == show(num(us[i], H)) for i in (0, 1, k1 // 2, k1 - 1)) and all(len(x) == W for x in nums) and
                         all(sum(HEX.index(nums[i][1 + 6 * h]) << (4 * h) for h in range(H)) == us[i] for i in range(k1)))
        lam = show(delta, sub=dict(zip(ut, nums)))
        parts = [s[:S]]
        for i in range(k1):
            b = S + i * B; parts += [s[b:b + R0], nums[i], s[b + R0 + WU:b + B]]
        parts.append(s[S + k1 * B:])
        r['lambda'] = lam == "".join(parts) and len(lam) == NL and 'u' not in lam
        r['fills_v'] = NL <= D * k
        def rule(q):                                       # the case analysis written in Diag
            if q >= NL: return ' '
            if q < S: return sp[q]
            if q < S + k1 * B2:
                i, o = divmod(q - S, B2)
                if o < R0: return sp[S + i * B + o]
                if o < R0 + W:
                    t = o - R0
                    if t < 6 * H:
                        h, w = divmod(t, 6)
                        return HEX[(us[i] >> (4 * h)) & 15] if w == 1 else "(?+(g*"[w]
                    return '0' if t == 6 * H else ')'
                return sp[S + i * B + (o - R0 - W) + R0 + WU]
            return sp[S + k1 * B + (q - S - k1 * B2)]
        rnd = random.Random(1); lamp = lam + ' ' * (D * k - NL)
        qs = set(rnd.randrange(D * k) for _ in range(sample))
        for i in (0, 1, k1 // 3, k1 - 1):
            for off in list(range(-3, R0 + 3)) + list(range(R0 + W - 3, B2 + 3)) + list(range(R0 + 6 * H - 8, R0 + 6 * H + 8)): qs.add(S + i * B2 + off)
        qs |= set(range(max(0, S - 5), S + 5)) | set(range(NL - 5, min(NL + 5, D * k))) | {0, D * k - 1}
        qs = [q for q in qs if 0 <= q < D * k]
        r['cases'] = all(rule(q) == lamp[q] for q in qs); r['n_cases'] = len(qs)
        r['ranges'] = D * k <= 1 << P['E'] and max(NL, S + k1 * B2, D * k) < 16 ** g.cw
        r['parts'] = (sum(1 + len(n) for n in vt), len(show(dg)), P['theta_len'],
                      len(show(g.access('x21', 'x23', 'v', k, P['wv'], P['iwv']))), len(show(g.access('x25', 'x26', 'u', k1, P['wu'], P['iwu']))))
        return r
    return Dense(**locals())
