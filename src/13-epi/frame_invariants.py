"""frame_invariants.py — the three frame invariants of the two constants on the 4 783 shells p ≡ 1 (mod 4) below 10⁵
(block frm.I1; 13:I5).

Compiles and runs frame_invariants.c (one O(p) pass per prime: K(p) mod p, q_p(4) mod p, and p = a² + b² with a ≡ 1
(mod 4), b > 0 even) and decides, in exact arithmetic, the paper's stated figures: the shell count; the triples at
p = 13, 233, 30089 and at the Wieferich prime 1093 (q_1093(4) = 0); the 4×4×4 contingency table of (K/p, q_p(4)/p,
φ/π) against the quarter bins — the first two by rational comparison, the third by the sign of a and |a| against b —
and its chi-square as an exact rational; the marginal means and variances of K/p and q_p(4)/p as exact rationals,
rounded as the paper states them. The moments of φ/π and of a/√p (the arcsine law) use float arctangents and are
printed as [approx] readings; the independence reading (chi-square 59.6 on 63 df) is the paper's [approx] statement
and decides nothing. A C compiler is required; without one the block runs the same pass in pure Python to the bound
2·10⁴ and records the reduced bound.
"""
import math, os, shutil, subprocess, time
from fractions import Fraction as Fr
from epicommon import chk, family, flush

N = 100000
HERE = os.path.dirname(os.path.abspath(__file__))

def compile_c():
    for cc in ("cc", "gcc", "clang"):
        if shutil.which(cc):
            exe = os.path.join(HERE, "frame_invariants")
            r = subprocess.run([cc, "-O2", os.path.join(HERE, "frame_invariants.c"), "-o", exe, "-lm"], capture_output=True, text=True)
            if r.returncode == 0:
                return exe
            print(f"    {cc} failed: {r.stderr.strip()[:200]}")
    return None

def python_pass(N):
    comp = bytearray(N + 1)
    for i in range(2, int(N**0.5) + 1):
        if not comp[i]: comp[i*i::i] = b"\x01" * len(comp[i*i::i])
    rows = []
    for p in range(5, N, 4):
        if comp[p]: continue
        f = s = 1
        for k in range(1, p):
            f = f * k % p; s = (s + f) % p
        q4 = (pow(4, p - 1, p * p) - 1) // p
        a = b = 0
        for x in range(1, math.isqrt(p) + 1, 2):
            y = math.isqrt(p - x * x)
            if y * y == p - x * x: a, b = x, y; break
        rows.append((p, s, q4, a if a % 4 == 1 else -a, b))
    return rows

def parse(out):
    return [tuple(int(t) for t in line.split()) for line in out.strip().splitlines() if line.strip()]

def quarter_bin(x):                       # x a Fraction in [0, 1): the index of its quarter
    return min(3, int(4 * x))

def angle_bin(a, b):                      # φ = arg(a + b i) with b > 0: the quarter of φ/π, decided in integers
    if a > 0: return 0 if b < a else 1    # φ < π/4  iff b < a ; else φ ∈ [π/4, π/2)  (a = b never: p odd)
    return 2 if b > -a else 3             # φ ∈ [π/2, 3π/4) iff b > |a| ; else [3π/4, π)

def run():
    t = time.time()
    exe = compile_c()
    if exe:
        r = subprocess.run([exe, str(N)], capture_output=True, text=True)
        rows, bound = parse(r.stdout), N
    else:
        bound = 20000
        rows = python_pass(bound)
    n = len(rows)
    byp = {p: (K, q, a, b) for p, K, q, a, b in rows}
    # exact consistency of every triple
    consistent = all(0 < K < p and 0 <= q < p and a % 4 == 1 and b % 2 == 0 and b > 0 and a * a + b * b == p for p, K, q, a, b in rows)
    # the 4×4×4 table, exact
    table = {}
    for p, K, q, a, b in rows:
        key = (quarter_bin(Fr(K, p)), quarter_bin(Fr(q, p)), angle_bin(a, b))
        table[key] = table.get(key, 0) + 1
    E = Fr(n, 64)
    chi = sum((Fr(table.get((i, j, k), 0)) - E) ** 2 / E for i in range(4) for j in range(4) for k in range(4))
    meanK = sum(Fr(K, p) for p, K, q, a, b in rows) / n; varK = sum((Fr(K, p) - meanK) ** 2 for p, K, q, a, b in rows) / n
    meanQ = sum(Fr(q, p) for p, K, q, a, b in rows) / n; varQ = sum((Fr(q, p) - meanQ) ** 2 for p, K, q, a, b in rows) / n
    phi = [math.atan2(b, a) / math.pi for p, K, q, a, b in rows]
    meanP = sum(phi) / n; varP = sum((x - meanP) ** 2 for x in phi) / n
    cosv = [a / math.sqrt(p) for p, K, q, a, b in rows]
    meanC = sum(cosv) / n; varC = sum((x - meanC) ** 2 for x in cosv) / n
    print(f"    {n} shells p = 1 (mod 4) below {bound}; K/p: mean {float(meanK):.4f} var {float(varK):.4f}; q_p(4)/p: mean {float(meanQ):.4f} var {float(varQ):.4f} (exact rationals)")
    print(f"    phi/pi: mean {meanP:.4f} var {varP:.4f} [approx]; a/sqrt p: mean {meanC:.3f} var {varC:.3f} [approx] (arcsine law: 0, 1/2); uniform law: 1/2, 1/12 = 0.0833")
    print(f"    4x4x4 table against the product of the quarter bins: chi-square {float(chi):.2f} on 63 df (exact rational {chi.numerator}/{chi.denominator}) [approx reading: consistent with independence]")
    family("frm", "I1")
    if bound == N:
        chk("exactly 4783 shells p = 1 (mod 4) below 10^5", n == 4783)
        chk("the triples at p = 13, 233, 30089 are (10, 6, -3+2i), (69, 14, 13+8i), (5260, 7666, -67+160i)",
            byp.get(13) == (10, 6, -3, 2) and byp.get(233) == (69, 14, 13, 8) and byp.get(30089) == (5260, 7666, -67, 160))
        chk("the Wieferich prime 1093 is the one shell with q_p(4) = 0 (q_p(2) = 0 gives q_p(4) = 2q_p(2) + p q_p(2)^2 = 0)",
            byp.get(1093, (0, -1))[1] == 0 and sum(1 for p, K, q, a, b in rows if q == 0) == 1)
        chk("means of K/p and q_p(4)/p round to 0.502 and 0.499, variances to 0.0828 and 0.0831 (exact rationals)",
            round(meanK, 3) == Fr(502, 1000) and round(meanQ, 3) == Fr(499, 1000) and round(varK, 4) == Fr(828, 10000) and round(varQ, 4) == Fr(831, 10000))
        chk("the 4x4x4 chi-square is an exact rational in [59.5, 59.7] (the paper's 59.6 on 63 df)", Fr(595, 10) <= chi <= Fr(597, 10))
    else:
        chk(f"NO C COMPILER: {n} shells p = 1 (mod 4) below {bound} (pure-Python pass)", n > 0)
    chk("every triple consistent: 0 < K(p) < p, 0 <= q_p(4) < p, a = 1 (mod 4), b > 0 even, a^2 + b^2 = p", consistent)
    chk("the 64 cells of the table sum to the shell count", sum(table.values()) == n)
    flush("frm", details={"I1": f"frame_invariants.c, N = {bound}, {time.time() - t:.0f} s" if bound == N else f"NO C COMPILER: pure-Python pass to N = {bound}, {time.time() - t:.0f} s"})

if __name__ == "__main__":
    import epicommon
    run(); epicommon.summary(write=False)
