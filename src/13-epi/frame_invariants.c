/* 13-epi: the three frame invariants of the two constants on the shells p = 1 (mod 4) below N (13:I5).
   For each such prime p: K(p) = sum_{k<p} k! mod p (the wall of e, 13:F2), q_p(4) = (4^(p-1) - 1)/p mod p (the wall
   of pi at second order, 13:G4), and the two-squares decomposition p = a^2 + b^2 with a odd, a = 1 (mod 4) by sign,
   b > 0 even (the angular address phi = arg(a + b i), 13:G3).  One O(p) pass per prime for K(p) in 64-bit modular
   arithmetic (p < 2^32); the square root by integer search.  Output: one line per shell, "p K q4 a b".
   Build: cc -O2 -o frame_invariants frame_invariants.c -lm.   Usage: frame_invariants N   (N = 100000 in the package). */
#include <stdio.h>
#include <stdlib.h>
#include <stdint.h>
#include <math.h>
typedef unsigned __int128 u128;
static uint64_t mulmod(uint64_t a, uint64_t b, uint64_t m) { return (uint64_t)((u128)a * b % m); }
static uint64_t powmod(uint64_t b, uint64_t e, uint64_t m) { uint64_t r = 1; b %= m; while (e) { if (e & 1) r = mulmod(r, b, m); b = mulmod(b, b, m); e >>= 1; } return r; }
int main(int argc, char **argv) {
    uint64_t N = argc > 1 ? strtoull(argv[1], 0, 10) : 100000;
    char *s = calloc(N + 1, 1);
    for (uint64_t i = 2; i * i <= N; i++) if (!s[i]) for (uint64_t j = i * i; j <= N; j += i) s[j] = 1;
    uint64_t count = 0;
    for (uint64_t p = 5; p < N; p++) {
        if (s[p] || p % 4 != 1) continue;
        uint64_t f = 1, K = 1;                                   /* K = 0! + 1! + ... + (p-1)!  mod p */
        for (uint64_t k = 1; k < p; k++) { f = mulmod(f, k, p); K += f; if (K >= p) K -= p; }
        uint64_t q4 = (uint64_t)(((u128)powmod(4, p - 1, p * p) - 1) / p);
        uint64_t a = 0, b = 0;
        for (uint64_t x = 1; x * x <= p; x += 2) {
            uint64_t r = p - x * x, y = (uint64_t)sqrt((double)r);
            while (y * y < r) y++; while (y * y > r) y--;
            if (y * y == r) { a = x; b = y; break; }
        }
        long sa = (a % 4 == 1) ? (long)a : -(long)a;
        printf("%llu %llu %llu %ld %llu\n", (unsigned long long)p, (unsigned long long)K, (unsigned long long)q4, sa, (unsigned long long)b);
        count++;
    }
    fprintf(stderr, "shells=%llu\n", (unsigned long long)count);
    return 0;
}
