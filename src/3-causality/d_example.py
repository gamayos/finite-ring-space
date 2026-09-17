"""
d_example.py — block D: the worked shell F_13 (3:D1)
=====================================================
The paper's worked shell: S = {1, 3, 4, 9, 10, 12}, N = {2, 5, 6, 7, 8, 11}; ν = 2 = g (the drive,
canonically); X² − 2 irreducible; K = F_169 with c = √2 ∉ F_13; the null cone of Q_2 has 2041 points on the shell
(elliptic) and 4 855 201 over K (q³ + q² − q, hyperbolic); the 14 boosts of N¹ with their 7 velocities; Λ(u) at
u = 2 has a = −5/(2c) ∉ F_13.
"""
import lcommon as lc

def run():
    p = 13; nu = 2
    S, N = lc.squares(p), lc.nonsquares(p)
    ok = S == [1, 3, 4, 9, 10, 12] and N == [2, 5, 6, 7, 8, 11]
    ok &= 2 in lc.generators(p) and not lc.is_square(2, p)
    ok &= all((x * x - 2) % p != 0 for x in range(p))                        # X^2 - 2 irreducible
    K = lc.Ext(p, nu); c = (0, 1)
    ok &= K.mul(c, c) == (2, 0) and c[1] != 0
    ok &= lc.isotropic_count((-2 % p, 1, 1, 1), p) == 2041
    N1 = K.norm_one(); ok &= len(N1) == 14
    vel = sorted({(-nu * b * pow(g, -1, p)) % p for g, b in N1}); ok &= len(vel) == 7
    u = (2, 0); ui = K.inv(u); a = K.mul(K.mul(K.scalar(pow(2, -1, p)), K.sub(u, ui)), K.inv(c))
    ok &= a[0] == 0 and a[1] != 0 and K.sub(u, ui) == ((2 - 7) % p, 0)      # u^-1 = 7, u - u^-1 = -5, a = -5/(2c)
    lc.check("D1", "F_13: S = {1,3,4,9,10,12}, N = {2,5,6,7,8,11}; nu = 2 = g; X^2 - 2 irreducible; c = sqrt 2 in K \\ F_13; 2041 null points; 14 boosts, 7 velocities", ok,
             f"boosts (gamma, b): {N1}; velocities {vel}")
    # D2 the same numbers by Lean's count: nullCount 13 2 = 2041 (the core decides it by the kernel) — here the exhaustive loop
    n = sum(1 for t in range(p) for x in range(p) for y in range(p) for z in range(p) if (-2 * t * t + x * x + y * y + z * z) % p == 0)
    lc.check("D2", "the null cone of Q_2 on F_13 counted vector by vector: 2041 = 13^3 - 13^2 + 13", n == 2041 == p ** 3 - p * p + p)

if __name__ == "__main__":
    run(); lc.summary(write=False)
