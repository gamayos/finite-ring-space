# Construction 1, EXACT no-go (framed-rational, zero floating point).
# Linear Kuramoto statics L u = source on a 5^3 box, Dirichlet boundary, exact rationals.
# Verifies the discrete Gauss law: net synchronisation flux through any closed surface
# enclosing the source = enclosed cardinality, EXACTLY; a source-free (noise) field carries
# zero net flux; hence source+noise has the same enclosed flux as the source. The mean force
# is therefore independent of the floor noise: Lemma fluxnoise, exact.
from fractions import Fraction as Fr
import itertools, random
N=5
pts=list(itertools.product(range(N),repeat=3))
def interior(p): return all(0<c<N-1 for c in p)
I=[p for p in pts if interior(p)]; pos={p:i for i,p in enumerate(I)}; M=len(I)
ctr=(2,2,2)
def nbrs(p):
    x,y,z=p
    for d in((1,0,0),(-1,0,0),(0,1,0),(0,-1,0),(0,0,1),(0,0,-1)):
        yield (x+d[0],y+d[1],z+d[2])
def solve(A,b):
    n=len(b); A=[r[:] for r in A]; b=b[:]
    for c in range(n):
        piv=next(r for r in range(c,n) if A[r][c]!=0)
        A[c],A[piv]=A[piv],A[c]; b[c],b[piv]=b[piv],b[c]
        inv=Fr(1)/A[c][c]; A[c]=[v*inv for v in A[c]]; b[c]*=inv
        for r in range(n):
            if r!=c and A[r][c]!=0:
                f=A[r][c]; A[r]=[a-f*x for a,x in zip(A[r],A[c])]; b[r]-=f*b[c]
    return b
def field(rho, bvals):                      # bvals: dict of fixed boundary values
    A=[[Fr(0)]*M for _ in range(M)]; b=[Fr(0)]*M
    for p in I:
        i=pos[p]; A[i][i]=Fr(6)
        for q in nbrs(p):
            if q in pos: A[i][pos[q]]-=1
            else: b[i]+=bvals.get(q,Fr(0))
        b[i]+=rho.get(p,Fr(0))
    x=solve(A,b); U=dict(bvals)
    for p in I: U[p]=x[pos[p]]
    return U
def flux(U,R):
    tot=Fr(0)
    for p in pts:
        if max(abs(p[0]-2),abs(p[1]-2),abs(p[2]-2))>R: continue
        for q in nbrs(p):
            if max(abs(q[0]-2),abs(q[1]-2),abs(q[2]-2))>R:
                tot += U.get(p,Fr(0))-U.get(q,Fr(0))
    return tot
zero_b={p:Fr(0) for p in pts if not interior(p)}
Us=field({ctr:Fr(1)}, zero_b)
print("EXACT discrete Gauss law (rational):")
for R in (0,1): print(f"  unit point source: flux(R={R}) = {flux(Us,R)}   (enclosed = 1)")
random.seed(1)
nb_b={p:Fr(random.randint(-9,9),4) for p in pts if not interior(p)}
Un=field({}, nb_b)
print(f"  source-free noise field: flux(R=1) = {flux(Un,1)}   (no enclosed source -> 0)")
Usn=field({ctr:Fr(1)}, nb_b)
print(f"  source+noise: flux(R=1) = {flux(Usn,1)}   == source-alone {flux(Us,1)} ? {flux(Usn,1)==flux(Us,1)}")
print("PASS" if flux(Us,1)==Fr(1) and flux(Un,1)==Fr(0) and flux(Usn,1)==Fr(1) else "FAIL")
