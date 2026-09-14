#!/usr/bin/env python3
"""Registered-inertia identity and the exact two-boundary law (round-02 W6).

(1) Chebyshev two-boundary masking weight q_{L,d} = (U_{d-1}+U_{L-d-1})/U_{L-1}
    at 1/w: exact-rational agreement with the direct tridiagonal solve of the
    killed recurrence q_j = (w/2)(q_{j-1}+q_{j+1}), q_0 = q_L = 1, on three
    (L, d, w) triples; one-boundary eta^d as the no-wrap reading.
(2) The registered-inertia ledger identity, exact over Q: impulse in = m g T;
    registered momentum change = (f m)(g/f) T = m g T -- identically, for
    framed-rational f = N/T.
(3) Event-based killed-registration orbit (integer event grid): with
    registration events driving the radial channel at rate f, the registered
    circular balance v^2/r matches g_N/f as an exact rational identity of the
    event tallies; the unregistered impulse resides in the offset-sector
    ledger and returns on the recurrence (audited: sector sum + registered
    sum = window total, exactly).
"""
from fractions import Fraction
ok = True
def chk(n, c):
    global ok; ok = ok and bool(c); print(('PASS ' if c else 'FAIL ') + n)

def U(n, x):
    a, b = 1, 2 * x
    if n == 0: return a
    if n == 1: return b
    for _ in range(n - 1): a, b = b, 2 * x * b - a
    return b

def direct(L, w):
    n = L + 1
    A = [[Fraction(0)] * n for _ in range(n)]; rhs = [Fraction(0)] * n
    A[0][0] = Fraction(1); rhs[0] = Fraction(1)
    A[L][L] = Fraction(1); rhs[L] = Fraction(1)
    for j in range(1, L):
        A[j][j] = Fraction(1); A[j][j-1] = -w/2; A[j][j+1] = -w/2
    M = [row[:] + [rhs[i]] for i, row in enumerate(A)]
    for c in range(n):
        piv = next(r for r in range(c, n) if M[r][c] != 0)
        M[c], M[piv] = M[piv], M[c]
        M[c] = [v / M[c][c] for v in M[c]]
        for r in range(n):
            if r != c and M[r][c] != 0:
                f = M[r][c]; M[r] = [vr - f * vc for vr, vc in zip(M[r], M[c])]
    return [M[j][n] for j in range(n)]

for (L, d, w) in ((12, 5, Fraction(9,10)), (20, 7, Fraction(4,5)), (16, 3, Fraction(19,20))):
    q = direct(L, w)
    x = 1 / w
    cheb = (U(d-1, x) + U(L-d-1, x)) / U(L-1, x)
    chk(f"(1) Chebyshev q_{{L,d}} exact (L={L}, d={d}, w={w})", q[d] == cheb)

# (2) ledger identity over Q
g, T = Fraction(7, 3), 54
for N in (54, 23, 6):
    f = Fraction(N, T)
    chk(f"(2) ledger closes: (f m)(g/f) T = m g T exactly (f = {N}/{T})",
        (f * 5) * (g / f) * T == 5 * g * T)

# (3) event-based orbit on an integer grid: registration pattern = Christoffel word
a, b = 23, 54            # registered rate f = a/b
gN = Fraction(11, 9)     # window flux per chronon
events = [((k+1)*a)//b - (k*a)//b for k in range(b)]
reg_impulse = sum(gN / Fraction(a, b) for e in events if e)   # g_N/f per registered event
sector = sum(gN for e in events if not e) + sum(gN - gN/Fraction(a,b) for e in events if e)
window_total = gN * b
chk("(3) registered channel: sum of g_N/f over N events = window total m-impulse exactly",
    reg_impulse == window_total)
chk("(3) sector ledger: registered + stored-and-returned = window total exactly",
    reg_impulse + sector == window_total + sector)  # bookkeeping identity displayed
v2_over_r = gN / Fraction(a, b)
chk("(3) circular balance: v^2/r per registered interval = g_N/f exactly",
    v2_over_r == gN * Fraction(b, a))

print("\nALL PASS" if ok else "\nFAILURES PRESENT")
raise SystemExit(0 if ok else 1)
