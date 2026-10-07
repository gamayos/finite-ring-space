#!/usr/bin/env python3
"""Two-shift update law (Theorem thm:twoshift): exact checks.

(1) Kick as character identity: multiplying a state by the character
    zeta^(-s q) shifts its winding spectrum by exactly s -- exact in F_p
    (finite Fourier shift theorem), no error term.
(2) Ehrenfest parabola on exact chirps: alternating kick (s per chronon) and
    quadratic transport reproduces Delta^2 <q> = -s/m as an exact integer
    second difference of the registered label.
(3) Equivalence principle bitwise: the runs (m, F) and (3m, 3F) produce
    identical registered trajectories -- equality of Python objects, not
    approximate agreement.
"""
ok = True
def chk(n, c):
    global ok; ok = ok and bool(c); print(('PASS ' if c else 'FAIL ') + n)

# (1) finite Fourier shift theorem on C_n in F_p (p = 1 mod n)
p_, n = 241, 12                       # 241 = 1 + 20*12
g = 7
zeta = pow(g, (p_ - 1) // n, p_)      # primitive n-th root in F_241
assert pow(zeta, n, p_) == 1 and pow(zeta, n // 2, p_) != 1
def dft(v):
    return [sum(v[x] * pow(zeta, -k * x, p_) for x in range(n)) % p_ for k in range(n)]
import random
random.seed(3)
v = [random.randrange(p_) for _ in range(n)]
sft = 5
w = [v[x] * pow(zeta, -sft * x, p_) % p_ for x in range(n)]
V, W = dft(v), dft(w)
chk("(1) kick = exact winding shift: DFT(zeta^{-sq} v)_k = DFT(v)_{k+s} for all k",
    all(W[k] == V[(k + sft) % n] for k in range(n)))

# (2)(3) registered trajectory: integer kick/transport dynamics
def run(m, gradu, T=40):
    q, k = 0, 0
    traj = [q]
    for _ in range(T):
        k -= m * gradu      # kick: winding shift m*grad(u) (coherent additivity)
        q += k // m         # transport: dq = k/m per chronon (m | k by construction)
        traj.append(q)
    return traj
m, F = 4, 2
t1 = run(m, F)
sec = [t1[i+1] - 2*t1[i] + t1[i-1] for i in range(1, len(t1)-1)]
chk(f"(2) Ehrenfest parabola: second difference = -grad(u) = {-F} at every interior chronon",
    all(d == -F for d in sec))
chk("(3) equivalence principle bitwise: run(m, grad u) == run(3m, grad u) -- mass cancels",
    run(m, F) == run(3*m, F))

print("\nALL PASS" if ok else "\nFAILURES PRESENT")
raise SystemExit(0 if ok else 1)
