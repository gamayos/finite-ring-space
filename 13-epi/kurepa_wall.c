/* Verify for all odd primes p <= N:
   (1) D_{p-1} == !p (mod p), where D_n are derangement numbers and !p = sum_{k=0}^{p-1} k!
   (2) !p != 0 (mod p)  [Kurepa non-vanishing in the tested range]
   Single O(p) pass per prime. */
#include <stdio.h>
#include <stdint.h>
#include <stdlib.h>
typedef unsigned long long u64;
typedef __uint128_t u128;

int main(int argc, char **argv) {
    u64 N = (argc > 1) ? strtoull(argv[1], 0, 10) : 200000ULL;
    char *comp = calloc(N + 1, 1);
    for (u64 i = 2; i * i <= N; i++)
        if (!comp[i]) for (u64 j = i * i; j <= N; j += i) comp[j] = 1;

    u64 checked = 0, kfail = 0, cfail = 0;
    for (u64 p = 3; p <= N; p += 2) {
        if (comp[p]) continue;
        u64 f = 1;      /* k! mod p, starts at 0! = 1 */
        u64 s = 1;      /* running sum of k!, starts with k=0 term */
        u64 D = 1;      /* D_0 = 1 */
        int sign = -1;  /* (-1)^k for k = 1 */
        for (u64 k = 1; k < p; k++) {
            f = (u64)((u128)f * k % p);
            s += f; if (s >= p) s -= p;
            D = (u64)((u128)D * k % p);
            if (sign < 0) { D = (D == 0) ? p - 1 : D - 1; }
            else          { D += 1; if (D >= p) D -= p; }
            sign = -sign;
        }
        if (s == 0)  { kfail++; printf("KUREPA VANISHES p=%llu\n", p); }
        if (D != s)  { cfail++; printf("CONGRUENCE FAIL p=%llu D=%llu s=%llu\n", p, D, s); }
        checked++;
    }
    printf("primes_checked=%llu kurepa_vanishing=%llu wall_congruence_failures=%llu\n",
           checked, kfail, cfail);
    return 0;
}
