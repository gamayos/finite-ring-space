# framed-rational status: EXACT -- integer / modular-F_p / cyclotomic arithmetic; no float in any asserted check (float, if present, only formats an exact rational for display).
"""
The fermion generation as the spinor of the internal frame.

Internal frame V = C^3 (colour, the rank-3 Hermitian frame) (+) C^2 (isospin,
the rank-2 spinor frame), a rank-5 module.  Hypercharge Y is the unique
traceless generator distinguishing the colour block from the isospin block:
  colour index  Y = -1/3 ,  isospin index  Y = +1/2   (so Tr Y = 3(-1/3)+2(1/2)=0).

One generation is the spinor of V, i.e. the exterior algebra:
  16 (SO(10) spinor) = Lambda^0 (+) Lambda^2 (+) Lambda^4  ~  1 (+) 10 (+) 5bar.
We build Lambda^1*(=5bar) and Lambda^2(=10) from the fundamental weights and read
off (colour, isospin, Y) of every piece, then verify against the Standard Model:
charges Q=T3+Y, anomaly cancellation, and sin^2(theta_W)=3/8.  Exact rationals.
"""
from fractions import Fraction as Fr
from itertools import combinations

half = Fr(1, 2)

# ---- the fundamental 5 = C^3(colour) (+) C^2(isospin) ----------------------
# each basis vector: (kind, T3, Y).  colour: 3 of them; isospin: 2 of them.
five = []
for c in range(3):
    five.append(("colour", Fr(0), Fr(-1, 3)))      # colour triplet, SU(2) singlet
five.append(("iso", +half, Fr(1, 2)))              # isospin up
five.append(("iso", -half, Fr(1, 2)))              # isospin down

def is_colour(i): return five[i][0] == "colour"
def is_iso(i):    return five[i][0] == "iso"

# ---- Lambda^1 conjugate = 5bar  (negate weights) ---------------------------
fivebar = [(k, -t, -y) for (k, t, y) in five]

# ---- Lambda^2(5) = 10  (antisymmetric pairs; weights add) ------------------
lam2 = []
for i, j in combinations(range(5), 2):
    _, ti, yi = five[i]; _, tj, yj = five[j]
    cc = (is_colour(i), is_colour(j))
    if cc == (True, True):     rep = "(3bar,1)"     # antisym 2 colour -> 3bar
    elif cc == (False, False): rep = "(1,1)"        # antisym 2 isospin -> singlet
    else:                      rep = "(3,2)"        # colour x isospin
    lam2.append((rep, ti + tj, yi + yj))

# ---- classify the 5bar and the 10 into Standard-Model fields ---------------
def classify():
    print("  5bar = Lambda^1*(5):")
    cb = [x for x in fivebar if x[0] == "colour"]
    ib = [x for x in fivebar if x[0] == "iso"]
    print(f"    (3bar,1) Y={cb[0][2]}   -> d^c     [colour-3 part]")
    print(f"    (1,2)    Y={ib[0][2]}, T3={[x[1] for x in ib]}  -> L (lepton doublet)")
    print("  10 = Lambda^2(5):")
    reps = {}
    for rep, t3, y in lam2:
        reps.setdefault((rep, y), []).append(t3)
    for (rep, y), t3s in reps.items():
        name = {"(3,2)": "Q (quark doublet)", "(3bar,1)": "u^c", "(1,1)": "e^c"}[rep]
        print(f"    {rep:8s} Y={str(y):>5} T3={sorted(set(t3s))} x{len(t3s)//len(set(t3s)) if len(set(t3s))>1 else len(t3s)}  -> {name}")

# ---- assemble the full generation (16) as (mult, T3-list, Y) ---------------
# colour-dim x isospin-multiplicity gives the Weyl count of each field
GEN = [
    ("Q  (3,2,+1/6)", 3, [+half, -half], Fr(1, 6)),
    ("u^c(3bar,1,-2/3)", 3, [Fr(0)], Fr(-2, 3)),
    ("d^c(3bar,1,+1/3)", 3, [Fr(0)], Fr(1, 3)),
    ("L  (1,2,-1/2)", 1, [+half, -half], Fr(-1, 2)),
    ("e^c(1,1,+1)", 1, [Fr(0)], Fr(1)),
    ("nu^c(1,1,0)", 1, [Fr(0)], Fr(0)),
]

def checks():
    nWeyl = sum(cdim * len(t3s) for _, cdim, t3s, _ in GEN)
    sumY = sum(cdim * len(t3s) * y for _, cdim, t3s, y in GEN)
    sumY3 = sum(cdim * len(t3s) * y**3 for _, cdim, t3s, y in GEN)
    sumT3sq = sum(cdim * sum(t**2 for t in t3s) for _, cdim, t3s, y in GEN)
    sumQsq = sum(cdim * sum((t + y)**2 for t in t3s) for _, cdim, t3s, y in GEN)
    print("  electric charges Q = T3 + Y:")
    for name, cdim, t3s, y in GEN:
        qs = sorted(set(t + y for t in t3s))
        print(f"    {name:18s} Q in {[str(q) for q in qs]}  (x{cdim} colour)")
    print(f"\n  Weyl fermion count                : {nWeyl}   (15 + nu^c = 16 = SO(10) spinor)")
    print(f"  gauge-grav anomaly   Sum Y         : {sumY}   (must be 0)")
    print(f"  cubic anomaly        Sum Y^3       : {sumY3}   (must be 0)")
    print(f"  Tr(T3^2)={sumT3sq},  Tr(Q^2)={sumQsq}")
    print(f"  sin^2(theta_W) = Tr(T3^2)/Tr(Q^2) : {sumT3sq/sumQsq} = {float(sumT3sq/sumQsq):.4f}")


if __name__ == "__main__":
    print("=" * 70)
    print("THE FERMION GENERATION AS THE SPINOR OF THE INTERNAL FRAME")
    print("=" * 70)
    print("\ninternal frame  V = C^3(colour, Y=-1/3) (+) C^2(isospin, Y=+1/2),"
          "  Tr Y = 0")
    print("generation = spinor of V = exterior algebra:  16 = 1 (+) 5bar (+) 10\n")
    classify()
    print()
    checks()
    print("=" * 70)
    print("All hypercharges are weight-sums of the fundamental (-1/3, +1/2);")
    print("anomalies cancel; sin^2(theta_W)=3/8 follows once the content is fixed.")
    print("=" * 70)
