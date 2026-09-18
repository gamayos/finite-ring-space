/* 13-epi: the pi-Wieferich search (13:G10, 13:Y2) -- the primes with 4^(p-1) = 1 + p (mod p^2), equivalently
   2 q_p(2) = 1 (mod p) for the Fermat quotient q_p(2) = (2^(p-1) - 1)/p (OEIS A355959, (p+2)^(p-1) = 1 (mod p^2)).
   Segmented sieve over [lo, hi), p < 2^32; for each odd prime p: r = 2^(p-1) mod p^2 by square-and-multiply in
   128-bit integers, q = (r - 1)/p, test 2q = 1 (mod p).  Also records the distribution of q_p(2)/p in 16 bins of
   the unit interval (the paper's [approx] equidistribution reading) and the near hits |2q - 1| <= 2 (mod p).
   Build: cc -O2 -o pi_wieferich pi_wieferich.c -lm.   Usage: pi_wieferich lo hi   (hits, counts, bins, time).
   Record: results_wieferich.txt -- [3, 2^32): 203,280,220 odd primes, hits {5, 45827}, 74 s on one core.      */
#include <stdio.h>
#include <stdlib.h>
#include <stdint.h>
#include <string.h>
#include <math.h>
#include <time.h>

typedef unsigned __int128 u128;

static inline uint64_t mulmod(uint64_t a, uint64_t b, uint64_t m) { return (uint64_t)((u128)a * b % m); }
static uint64_t powmod(uint64_t b, uint64_t e, uint64_t m) {
    uint64_t r = 1; b %= m;
    while (e) { if (e & 1) r = mulmod(r, b, m); b = mulmod(b, b, m); e >>= 1; }
    return r;
}

int main(int argc, char **argv) {
    uint64_t lo = strtoull(argv[1], 0, 10), hi = strtoull(argv[2], 0, 10);
    if (lo < 3) lo = 3;
    uint32_t sq = (uint32_t)sqrt((double)hi) + 2;
    /* small primes */
    char *sm = calloc(sq + 1, 1);
    uint32_t *sp = malloc(sizeof(uint32_t) * (sq / 2 + 10)); uint32_t nsp = 0;
    for (uint32_t i = 2; i <= sq; i++) if (!sm[i]) { sp[nsp++] = i; for (uint64_t j = (uint64_t)i * i; j <= sq; j += i) sm[j] = 1; }
    const uint64_t SEG = 1u << 22;
    char *seg = malloc(SEG);
    uint64_t count = 0, hits = 0, near = 0, mod1 = 0, hits1 = 0;
    uint64_t bins[16] = {0};
    clock_t t0 = clock();
    for (uint64_t base = lo; base < hi; base += SEG) {
        uint64_t top = base + SEG < hi ? base + SEG : hi;
        memset(seg, 0, top - base);
        for (uint32_t i = 0; i < nsp; i++) {
            uint64_t q = sp[i]; if (q * q >= top) break;
            uint64_t start = (base + q - 1) / q * q; if (start < q * q) start = q * q;
            for (uint64_t j = start; j < top; j += q) seg[j - base] = 1;
        }
        for (uint64_t n = base; n < top; n++) {
            if (seg[n - base] || (n & 1) == 0) continue;
            uint64_t p = n;
            if (p < 3) continue;
            /* p^2 must fit in 64 bits: p < 2^32 */
            if (p >= 4294967296ULL) { fprintf(stderr, "p >= 2^32 not supported in 64-bit path\n"); return 1; }
            uint64_t p2 = p * p;
            uint64_t r = powmod(2, p - 1, p2);          /* 2^(p-1) mod p^2 */
            uint64_t q = (r - 1) / p;                    /* Fermat quotient q_p(2) mod p */
            count++;
            if (p % 4 == 1) mod1++;
            bins[(int)((16.0 * q) / p)]++;
            uint64_t two_q = (2 * q) % p;
            if (two_q == 1) { hits++; if (p % 4 == 1) hits1++; printf("HIT p=%llu q_p(2)=%llu p mod 4 = %llu\n", (unsigned long long)p, (unsigned long long)q, (unsigned long long)(p % 4)); fflush(stdout); }
            else if (two_q <= 3 || two_q >= p - 2) { near++; }
        }
    }
    double secs = (double)(clock() - t0) / CLOCKS_PER_SEC;
    printf("range [%llu, %llu): primes %llu (p = 1 mod 4: %llu); pi-Wieferich hits %llu (of which p = 1 mod 4: %llu); near hits |2q-1| <= 2: %llu; %.1f s\n",
           (unsigned long long)lo, (unsigned long long)hi, (unsigned long long)count, (unsigned long long)mod1,
           (unsigned long long)hits, (unsigned long long)hits1, (unsigned long long)near, secs);
    printf("bins of q_p(2)/p in [0,1): ");
    for (int i = 0; i < 16; i++) printf("%llu ", (unsigned long long)bins[i]);
    printf("\n");
    return 0;
}
