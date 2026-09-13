"""kurepa_wall.py — the Kurepa wall of e in the derangement form, for all odd primes p < 2.5e5 (block kur.K1).

Compiles and runs kurepa_wall.c (one O(p) pass per prime in 128-bit modular arithmetic, checking
!(p-1) == K(p) (mod p) and K(p) != 0 (mod p)), and turns its summary line into the registry predicate: 22 043 primes
checked, zero failures of either condition. A C compiler (cc/gcc/clang) is required; Colab and Debian/macOS provide
one. Without a compiler the block runs the same pass in pure Python to the bound 2·10⁴ (2 261 primes) and records
the reduced bound in the check's detail.
"""
import os, re, shutil, subprocess, sys, time
from epicommon import chk, family, flush

N = 250000
HERE = os.path.dirname(os.path.abspath(__file__))

def compile_c():
    for cc in ("cc", "gcc", "clang"):
        if shutil.which(cc):
            exe = os.path.join(HERE, "kurepa_wall")
            r = subprocess.run([cc, "-O2", os.path.join(HERE, "kurepa_wall.c"), "-o", exe], capture_output=True, text=True)
            if r.returncode == 0:
                return exe
            print(f"    {cc} failed: {r.stderr.strip()[:200]}")
    return None

def python_pass(N):
    comp = bytearray(N + 1)
    for i in range(2, int(N**0.5) + 1):
        if not comp[i]: comp[i*i::i] = b"\x01" * len(comp[i*i::i])
    checked = kfail = cfail = 0
    for p in range(3, N + 1, 2):
        if comp[p]: continue
        f = s = D = 1; sign = -1
        for k in range(1, p):
            f = f * k % p
            s = (s + f) % p
            D = (D * k + sign) % p
            sign = -sign
        if s == 0: kfail += 1
        if D != s: cfail += 1
        checked += 1
    return checked, kfail, cfail

def run():
    t = time.time()
    exe = compile_c()
    if exe:
        out = subprocess.run([exe, str(N)], capture_output=True, text=True).stdout
        print("    " + out.strip().replace("\n", "\n    "))
        m = re.search(r"primes_checked=(\d+) kurepa_vanishing=(\d+) wall_congruence_failures=(\d+)", out)
        checked, kfail, cfail = (int(x) for x in m.groups()) if m else (0, 1, 1)
        family("kur", "K1")
        chk(f"{checked} odd primes p < {N}: exactly 22043", checked == 22043)
        chk("K(p) != 0 (mod p) for every prime checked", kfail == 0)
        chk("!(p-1) == K(p) (mod p) for every prime checked", cfail == 0)
        flush("kur", details={"K1": f"kurepa_wall.c, N = {N}, {time.time() - t:.0f} s"})
    else:
        n = 20000
        checked, kfail, cfail = python_pass(n)
        family("kur", "K1")
        chk(f"{checked} odd primes p < {n}: exactly 2261", checked == 2261)
        chk("K(p) != 0 (mod p) for every prime checked", kfail == 0)
        chk("!(p-1) == K(p) (mod p) for every prime checked", cfail == 0)
        flush("kur", details={"K1": f"NO C COMPILER: pure-Python pass to N = {n} only ({checked} primes), {time.time() - t:.0f} s"})

if __name__ == "__main__":
    import epicommon
    run(); epicommon.summary(write=False)
