/* Streaming inner loop of the fractional Fourier orbit: Algorithm A (scalar
   coefficients, general modular multiplication) versus Algorithm B (contribution
   arrays updated by halving, i.e. shift-and-reduce), for primes p = 4k+1 with
   primitive root 2.  Residues are 32-bit lanes.  The four spectral components are
   random residues: the streaming phase does not depend on how they were obtained.
   Usage: ./stream REPS p1 p2 ...   Output: one line per prime.
   Build: cc -O2 -o stream stream.c  (and cc -O1 for the non-vectorised figures). */
#include <stdio.h>
#include <stdint.h>
#include <stdlib.h>
#include <time.h>

static double now(void){struct timespec t;clock_gettime(CLOCK_MONOTONIC,&t);return t.tv_sec+1e-9*t.tv_nsec;}
static uint64_t mulmod(uint64_t a,uint64_t b,uint64_t p){return a*b%p;}
static uint64_t powmod(uint64_t b,uint64_t e,uint64_t p){uint64_t r=1;b%=p;while(e){if(e&1)r=mulmod(r,b,p);b=mulmod(b,b,p);e>>=1;}return r;}
static int is_prime(uint32_t m){if(m<2)return 0;for(uint32_t d=2;(uint64_t)d*d<=m;d++)if(m%d==0)return 0;return 1;}
static int two_is_primitive(uint32_t p){uint32_t n=p-1,m=n;for(uint32_t q=2;(uint64_t)q*q<=m;q++){if(m%q==0){if(powmod(2,n/q,p)==1)return 0;while(m%q==0)m/=q;}}if(m>1&&powmod(2,n/m,p)==1)return 0;return 1;}
static inline uint32_t half(uint32_t a,uint32_t p){return (a+(p&(0u-(a&1u))))>>1;}  /* a*2^{-1} mod p */

int main(int argc,char**argv){
  if(argc<3){fprintf(stderr,"usage: %s REPS p ...\n",argv[0]);return 2;}
  int reps=atoi(argv[1]);
  printf("p,n,A_mod_ns,A_barrett_ns,B_half_ns,ratio_Amod_B,ratio_Abar_B\n");
  for(int ai=2;ai<argc;ai++){
    uint32_t p=(uint32_t)atol(argv[ai]);
    if(!is_prime(p)||p%4!=1||!two_is_primitive(p)){fprintf(stderr,"%u: not a prime = 1 mod 4 with primitive root 2; skipped\n",p);continue;}
    uint32_t n=p-1;
    uint32_t *u0=malloc(4ul*n),*u1=malloc(4ul*n),*u2=malloc(4ul*n),*u3=malloc(4ul*n),*w=malloc(4ul*n);
    uint32_t *a1=malloc(4ul*n),*a2=malloc(4ul*n),*a3=malloc(4ul*n);
    srand(1); for(uint32_t j=0;j<n;j++){u0[j]=rand()%p;u1[j]=rand()%p;u2[j]=rand()%p;u3[j]=rand()%p;}
    uint64_t h1=powmod(2,n-1,p),h2=powmod(2,n-2,p),h3=powmod(2,n-3,p);  /* 2^{-1},2^{-2},2^{-3} */
    uint64_t hA=0,hAb=0,hB=0; double tA,tAb,tB,t0;
    /* Algorithm A with runtime % */
    t0=now();
    for(int r=0;r<reps;r++){uint64_t c1=1,c2=1,c3=1;uint64_t h=1469598103934665603ull;
      for(uint32_t s=0;s<n;s++){
        for(uint32_t j=0;j<n;j++)w[j]=(uint32_t)((u0[j]+c1*u1[j]+c2*u2[j]+c3*u3[j])%p);
        for(uint32_t j=0;j<n;j+=97)h=(h^w[j])*1099511628211ull;
        c1=c1*h1%p;c2=c2*h2%p;c3=c3*h3%p;}
      hA=h;}
    tA=(now()-t0)/reps;
    /* Algorithm A with Barrett reduction (m = floor(2^64/p)) */
    t0=now();
    {uint64_t m=(uint64_t)(((unsigned __int128)1<<64)/p);
     for(int r=0;r<reps;r++){uint64_t c1=1,c2=1,c3=1;uint64_t h=1469598103934665603ull;
      for(uint32_t s=0;s<n;s++){
        for(uint32_t j=0;j<n;j++){uint64_t x=u0[j]+c1*u1[j]+c2*u2[j]+c3*u3[j];
          uint64_t q=(uint64_t)(((unsigned __int128)x*m)>>64);uint64_t t=x-q*p;if(t>=p)t-=p;w[j]=(uint32_t)t;}
        for(uint32_t j=0;j<n;j+=97)h=(h^w[j])*1099511628211ull;
        c1=c1*h1%p;c2=c2*h2%p;c3=c3*h3%p;}
      hAb=h;}}
    tAb=(now()-t0)/reps;
    /* Algorithm B: additions and halvings only */
    t0=now();
    for(int r=0;r<reps;r++){for(uint32_t j=0;j<n;j++){a1[j]=u1[j];a2[j]=u2[j];a3[j]=u3[j];}
      uint64_t h=1469598103934665603ull;
      for(uint32_t s=0;s<n;s++){
        for(uint32_t j=0;j<n;j++){uint32_t x=u0[j]+a1[j];if(x>=p)x-=p;x+=a2[j];if(x>=p)x-=p;x+=a3[j];if(x>=p)x-=p;w[j]=x;
          a1[j]=half(a1[j],p);
          a2[j]=half(half(a2[j],p),p);
          a3[j]=half(half(half(a3[j],p),p),p);}
        for(uint32_t j=0;j<n;j+=97)h=(h^w[j])*1099511628211ull;}
      hB=h;}
    tB=(now()-t0)/reps;
    if(hA!=hB||hA!=hAb){fprintf(stderr,"%u: orbit hashes differ\n",p);return 1;}
    double N=(double)n*n;
    printf("%u,%u,%.3f,%.3f,%.3f,%.2f,%.2f\n",p,n,tA/N*1e9,tAb/N*1e9,tB/N*1e9,tA/tB,tAb/tB);
    free(u0);free(u1);free(u2);free(u3);free(w);free(a1);free(a2);free(a3);
  }
  return 0;
}
