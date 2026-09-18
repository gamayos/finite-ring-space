/* 13-epi: the pi-Wieferich search beyond 2^32 (13:G4, 13:G10) -- 4^(p-1) = 1 + p (mod p^2), i.e. 2 q_p(2) = 1
   (mod p); OEIS A355959.  128-bit Montgomery arithmetic modulo p^2 for p < 2^63, self-checked against the 64-bit
   path of pi_wieferich.c below 2^32 (third argument: any value switches the self-test on).
   Build: cc -O2 -o pi_wieferich128 pi_wieferich128.c -lm.   Usage: pi_wieferich128 lo hi [selftest]
   Record: results_wieferich.txt -- [2^32, 2^34) and [2^34, 2^35): 1,276,926,058 primes, no hit, 43 min in all;
   the OEIS entry's bound a(3) > 107,659,373,057 (Alekseyev 2023) lies beyond this range.                        */
#include <stdio.h>
#include <stdlib.h>
#include <stdint.h>
#include <string.h>
#include <math.h>
#include <time.h>

typedef unsigned __int128 u128;

/* ---- 128-bit Montgomery: N odd, R = 2^128 ---- */
typedef struct { u128 N, Ninv_neg; u128 R2; } mont;   /* Ninv_neg = -N^{-1} mod 2^128; R2 = R^2 mod N */

static u128 inv128(u128 n) {           /* n odd: inverse mod 2^128 by Newton */
    u128 x = n;                         /* correct to 3 bits (n*n = 1 mod 8) */
    for (int i = 0; i < 7; i++) x *= 2 - n * x;
    return x;
}
static u128 mod128(u128 a, u128 n) { return a % n; }

static inline void mul128x128(u128 a, u128 b, u128 *hi, u128 *lo) {
    uint64_t a0 = (uint64_t)a, a1 = (uint64_t)(a >> 64), b0 = (uint64_t)b, b1 = (uint64_t)(b >> 64);
    u128 p00 = (u128)a0 * b0, p01 = (u128)a0 * b1, p10 = (u128)a1 * b0, p11 = (u128)a1 * b1;
    u128 mid = (p00 >> 64) + (uint64_t)p01 + (uint64_t)p10;
    *lo = (mid << 64) | (uint64_t)p00;
    *hi = p11 + (p01 >> 64) + (p10 >> 64) + (mid >> 64);
}
static inline u128 mont_redc(const mont *m, u128 hi, u128 lo) {  /* (hi*2^128 + lo) * R^{-1} mod N */
    u128 q = lo * m->Ninv_neg;                     /* mod 2^128 */
    u128 qh, ql; mul128x128(q, m->N, &qh, &ql);    /* q*N */
    /* t = (hi:lo + q*N) >> 128 ; lo + ql == 0 mod 2^128, carry iff lo != 0 */
    u128 carry = (lo != 0);
    u128 t = hi + qh + carry;
    if (t >= m->N) t -= m->N;
    return t;
}
static inline u128 mont_mul(const mont *m, u128 a, u128 b) { u128 hi, lo; mul128x128(a, b, &hi, &lo); return mont_redc(m, hi, lo); }
static void mont_init(mont *m, u128 N) {
    m->N = N; m->Ninv_neg = (u128)0 - inv128(N);
    /* R mod N then square: R = 2^128; R mod N = (2^128 - N*floor) : compute as ((u128)0 - N) % N */
    u128 rmod = ((u128)0 - N) % N;                 /* 2^128 mod N */
    m->R2 = (u128)0; { /* R2 = rmod^2 mod N via repeated doubling (N < 2^126 assumed) */
        u128 x = rmod, y = rmod, acc = 0;
        /* schoolbook: acc = x*y mod N with doubling — 128 steps */
        for (int i = 127; i >= 0; i--) { acc = (acc << 1) % N; if ((y >> i) & 1) { acc += x; if (acc >= N) acc -= N; } }
        m->R2 = acc;
    }
}
static u128 mont_pow(const mont *m, u128 base, uint64_t e) {   /* base plain; returns plain */
    u128 bm = mont_mul(m, base % m->N, m->R2);     /* to Montgomery form */
    u128 r = mont_mul(m, 1, m->R2);                /* 1 in Montgomery form = R mod N */
    while (e) { if (e & 1) r = mont_mul(m, r, bm); bm = mont_mul(m, bm, bm); e >>= 1; }
    return mont_mul(m, r, 1);                       /* out of Montgomery form */
}

static inline uint64_t mulmod64(uint64_t a, uint64_t b, uint64_t m) { return (uint64_t)((u128)a * b % m); }
static uint64_t powmod64(uint64_t b, uint64_t e, uint64_t m) { uint64_t r = 1; b %= m; while (e) { if (e & 1) r = mulmod64(r, b, m); b = mulmod64(b, b, m); e >>= 1; } return r; }

int main(int argc, char **argv) {
    uint64_t lo = strtoull(argv[1], 0, 10), hi = strtoull(argv[2], 0, 10);
    int selftest = argc > 3;
    if (lo < 3) lo = 3;
    uint64_t sq = (uint64_t)sqrt((double)hi) + 2;
    char *sm = calloc(sq + 1, 1);
    uint32_t *sp = malloc(sizeof(uint32_t) * (sq / 2 + 10)); uint32_t nsp = 0;
    for (uint64_t i = 2; i <= sq; i++) if (!sm[i]) { sp[nsp++] = (uint32_t)i; for (uint64_t j = i * i; j <= sq; j += i) sm[j] = 1; }
    const uint64_t SEG = 1u << 23;
    char *seg = malloc(SEG);
    uint64_t count = 0, hits = 0, near = 0, mod1 = 0, hits1 = 0, mism = 0;
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
            uint64_t p = n; if (p < 3) continue;
            u128 p2 = (u128)p * p;
            mont m; mont_init(&m, p2);
            u128 r = mont_pow(&m, 2, p - 1);
            u128 q128 = (r - 1) / p;                  /* < p */
            uint64_t q = (uint64_t)q128;
            if (selftest && p < 4294967296ULL) {
                uint64_t r64 = powmod64(2, p - 1, p * p); uint64_t q64 = (r64 - 1) / p;
                if (q64 != q) { mism++; if (mism < 5) printf("MISMATCH p=%llu q128=%llu q64=%llu\n", (unsigned long long)p, (unsigned long long)q, (unsigned long long)q64); }
            }
            count++;
            if (p % 4 == 1) mod1++;
            bins[(int)((16.0 * (double)q) / (double)p)]++;
            uint64_t two_q = (uint64_t)(((u128)2 * q) % p);
            if (two_q == 1) { hits++; if (p % 4 == 1) hits1++; printf("HIT p=%llu q_p(2)=%llu p mod 4 = %llu\n", (unsigned long long)p, (unsigned long long)q, (unsigned long long)(p % 4)); fflush(stdout); }
            else if (two_q <= 3 || two_q >= p - 2) near++;
        }
    }
    double secs = (double)(clock() - t0) / CLOCKS_PER_SEC;
    printf("range [%llu, %llu): primes %llu (p = 1 mod 4: %llu); pi-Wieferich hits %llu (p = 1 mod 4: %llu); near |2q-1| <= 2: %llu; mismatches %llu; %.1f s\n",
           (unsigned long long)lo, (unsigned long long)hi, (unsigned long long)count, (unsigned long long)mod1,
           (unsigned long long)hits, (unsigned long long)hits1, (unsigned long long)near, (unsigned long long)mism, secs);
    printf("bins of q_p(2)/p in [0,1): "); for (int i = 0; i < 16; i++) printf("%llu ", (unsigned long long)bins[i]); printf("\n");
    return 0;
}
