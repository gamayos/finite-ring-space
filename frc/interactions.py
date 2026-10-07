"""frc.interactions — one generation and the Koide form (the interactions theme; ledger migration, task LM29, 6 October
2026).

The python side of `lean/FrcCore/Theme/Interactions.lean`: the reflection algebra of four directions on subsets
(bitmasks), the fifth direction, the spinor 16 read 3 + 2 with its hypercharges and charges, and the Koide form of an
amplitude vector on the cube-root orbit. Exact integers and fractions only, the standard library only (gate G09). The
first ledger to use it is the master's block file frc/ledgers/master/interactions.py.

    bit(S, i), cnt(S, lo, hi)     direction i in S; the directions lo ≤ i < hi in S
    emul(S, T)                     e_S e_T = (sign, S ∪ T) for disjoint S, T, else (0, 0)
    fifth(S)                       e_S (|S| even) or e_S e_4 (|S| odd)
    gen16()                        the even subsets of five directions
    col(S), wk(S), y6(S), q6(S)    colour and weak indices, 6Y = −2|S∩C| + 3|S∩W|, 6Q = 6T₃ + 6Y
    koide_q(a)                     Q = Σ a² / (Σ a)², a Fraction
    koide_rho2(a, p, w)            ρ² = â₁â₂/â₀² in 𝔽_p with ω = w, ω² + ω + 1 = 0
"""
from fractions import Fraction


def bit(S, i):
    return (S >> i) & 1 == 1


def cnt(S, lo, hi):
    return sum(1 for i in range(lo, hi) if bit(S, i))


def emul(S, T):
    if S & T & 31: return (0, 0)
    inv = sum(1 for s in range(5) for t in range(5) if bit(S, s) and bit(T, t) and t < s)
    return (1 if inv % 2 == 0 else -1, S | T)


def fifth(S):
    return S if cnt(S, 0, 4) % 2 == 0 else S | 16


def gen16():
    return [S for S in range(32) if cnt(S, 0, 5) % 2 == 0]


def col(S): return cnt(S, 0, 3)
def wk(S): return cnt(S, 3, 5)
def y6(S): return -2 * col(S) + 3 * wk(S)
def q6(S): return 3 * ((1 if bit(S, 3) else -1) if wk(S) == 1 else 0) + y6(S)


def koide_q(a):
    return Fraction(sum(x * x for x in a), sum(a) ** 2)


def koide_rho2(a, p, w):
    """(â₀, â₁, â₂, 3Σa², â₀² + 2â₁â₂) in 𝔽_p, â_k = Σ_j a_j ω^{jk}."""
    hat = [sum(a[j] * pow(w, j * k, p) for j in range(3)) % p for k in range(3)]
    return hat, 3 * sum(x * x for x in a) % p, (hat[0] ** 2 + 2 * hat[1] * hat[2]) % p
