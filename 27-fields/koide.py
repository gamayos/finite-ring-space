# framed-rational status: MIXED -- exact framed-rational core; continuum constructs are confined to clearly-labelled [approx] / degenerate-idealisation comparisons (Tier 2/3/5 or measured-data), never to an exact claim.
"""Charged-lepton Koide relation from cube-root coherence at the quarter-turn.

Backs Proposition prop:koide of 27-fields (main.tex, sec:matter).

All exact checks are performed natively in the scale-periodic framed-rational
arithmetic of a shell F_p with p = 5 (mod 12): integer/modular arithmetic only,
no continuum primitives (no float, exp, log, trig, pi, sqrt, RNG). The cube root
omega lives on the order-three subgroup of the non-split torus C_{p+1} (3 | p+1),
reached by the native Frobenius conjugation x -> x^p of F_{p^2}/F_p. The quarter
turn enters as the framed-rational value rho^2 = 1/2, i.e. the norm relation
2 N(b) = a^2 in F_p.

The only continuum step is the comparison to the measured lepton masses, which is
isolated at the end and explicitly tagged [approx] (a profinite/continuum reading
of the data, carrying no framed-rational claim).
"""

_pass = 0
_fail = 0


def check(name, cond):
    global _pass, _fail
    cond = bool(cond)
    print(("PASS" if cond else "FAIL") + " : " + name)
    if cond:
        _pass += 1
    else:
        _fail += 1


def legendre(a, p):
    return pow(a % p, (p - 1) // 2, p)


# ---- F_{p^2} = F_p[theta], theta^2 = d with d = -3 (a non-residue for p=2 mod 3) ----
# element = (u, v) meaning u + v*theta.  Frobenius: (u+v*theta)^p = u - v*theta.
def fmul(A, B, p, d):
    a0, a1 = A
    b0, b1 = B
    return ((a0 * b0 + a1 * b1 * d) % p, (a0 * b1 + a1 * b0) % p)


def fpow(A, e, p, d):
    R = (1, 0)
    while e:
        if e & 1:
            R = fmul(R, A, p, d)
        A = fmul(A, A, p, d)
        e >>= 1
    return R


def frob(A, p):
    return (A[0] % p, (-A[1]) % p)


def norm(A, p, d):                       # N(A) = A * A^p in F_p
    n = fmul(A, frob(A, p), p, d)
    assert n[1] == 0
    return n[0]


def koide_shell(p):
    assert p % 12 == 5, "shell must be 5 mod 12"
    d = (-3) % p
    ok_local = True
    ok_local &= (legendre(d, p) == p - 1)                # -3 is a non-residue
    inv2 = pow(2, p - 2, p)
    inv3 = pow(3, p - 2, p)
    # cube root of unity: omega = (-1 + theta)/2, since (2*omega+1)^2 = theta^2 = -3.
    omega = ((-inv2) % p, inv2 % p)
    o3 = fpow(omega, 3, p, d)
    ok_local &= (o3 == (1, 0) and omega != (1, 0))       # order exactly 3
    om = [(1, 0), omega, fmul(omega, omega, p, d)]        # omega^0, ^1, ^2  (omega^{-1}=omega^2)

    # eigenvalues lambda_k = a + b*omega^k + b^p*omega^{-k}, real (Frobenius-fixed) in F_p.
    for a in (1, 2, 7):
        for b in ((1, 1), (2, 1), (3, 2)):
            bp = frob(b, p)
            lam = []
            for k in range(3):
                t = fmul(b, om[k], p, d)
                t2 = fmul(bp, om[(-k) % 3], p, d)
                e = ((a + t[0] + t2[0]) % p, (t[1] + t2[1]) % p)
                ok_local &= (e[1] == 0)                   # lambda_k lies in F_p
                lam.append(e[0])
            S1 = sum(lam) % p
            S2 = sum((x * x) % p for x in lam) % p
            nb = norm(b, p, d)
            ok_local &= (S1 == (3 * a) % p)               # sum lambda = 3a
            ok_local &= (S2 == (3 * a * a + 6 * nb) % p)  # sum lambda^2 = 3a^2 + 6 N(b)
            # Q = S2 / S1^2 = 1/3 + 2/3 * rho^2, rho^2 = N(b)/a^2, all in F_p
            Q = (S2 * pow(S1 * S1 % p, p - 2, p)) % p
            rho2 = (nb * pow(a * a % p, p - 2, p)) % p
            ok_local &= (Q == (inv3 + 2 * inv3 % p * rho2) % p)
    # quarter-turn: rho^2 = 1/2 (the framed-rational value) <=> Q = 2/3 in F_p
    Q_qt = (inv3 + (2 * inv3) % p * inv2) % p
    ok_local &= (Q_qt == (2 * inv3) % p)                  # = 2/3
    return ok_local


for p in (17, 53, 173, 389, 1373):
    check("framed-rational Koide over F_%d (p=5 mod 12): "
          "sum lam=3a, sum lam^2=3a^2+6N(b), Q=1/3+2/3 rho^2, rho^2=1/2 => Q=2/3" % p,
          koide_shell(p))

# ---- [approx] continuum comparison to the measured masses (PDG, MeV) ----------
# This block alone uses floats; it is a continuum reading of the data, not a
# framed-rational claim.
import math
me, mmu, mtau = 0.51099895, 105.6583755, 1776.86
a = [math.sqrt(m) for m in (me, mmu, mtau)]
Qm = (me + mmu + mtau) / sum(a) ** 2
w = complex(-0.5, math.sqrt(3) / 2)                       # continuum zeta_3
a0m = sum(a)
a1m = abs(sum(a[j] * w ** (-j) for j in range(3)))
print("[approx] measured Q   = %.6f  (2/3 = %.6f, deviation %.1e)"
      % (Qm, 2 / 3, abs(Qm - 2 / 3)))
print("[approx] measured rho^2 = %.6f  vs framed-rational 1/2"
      % ((a1m / a0m) ** 2))

print("\n%d framed-rational checks, %d passed, %d failed" % (_pass + _fail, _pass, _fail))
raise SystemExit(1 if _fail else 0)
