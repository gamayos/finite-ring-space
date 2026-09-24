"""
fourier.py — the validation package of "Scale-Shift and Fractional Fourier Transform as Rotations over Finite Holographic
Substrate" (Akhtman, 2026; doi 10.20944/preprints202606.0127.v1), the paper 6-fourier of the FRC corpus
(finite-ring-space/src/6-fourier), added with the paper's predicate ledger (13 September 2026; one script since
24 September 2026, the five block scripts merged).
========================================================================================================================

One script, five blocks, thirty-seven checks, numpy (matplotlib for the one figure). Each check names the predicate(s) of the
paper's ledger it witnesses (LEDGER below; predicates cited as 6:XN) under a `# 6:XN (<key>)` marker, and the ledger's
source column links the marker in return (finitering.space/src/6-fourier/#<key>). The paper \\label(s) a
check decides are in the block banners. Three master-ledger predicates of the corpus are reached through the paper's:
00:C2 (6:B5, 6:C3, 6:D4), 00:C14 (6:B2), 00:C7 on the transform layer (6:C9).

    python3 fourier.py            every block, results.json written; exit 1 if a check fails (≈ 6 s)
    python3 fourier.py D          one block (A, B, C, D or E); no results.json
    from frc_6_fourier import predicate; predicate("6:C3")     one predicate: its block runs once per session

Blocks:  A  the frame datum and the shell Fourier operator     EXACT            (6:B1–B3, B5–B7)
         B  the fractional family F^[s]                        EXACT            (6:C2–C9)
         C  representation domains and the coordinate zoom     EXACT            (6:D1, D2, D4, D5)
         D  the Weil dictionary, the operator-level comparison EXACT            (6:E2, E3, E5–E8)
         E  the cyclotomic observer readout, the entropy cycle EXACT / [approx] (6:F2–F7)

Everything the blocks share:
  * the frame datum of a shell: p = 4κ+1, the smallest primitive root g (the generators of Table `tab:checks`),
    the oriented quarter-turn i = −g^κ, π = 2κ, e = g^i;
  * exact matrix arithmetic over F_p (numpy int64, reduced mod p after every product);
  * the shell Fourier matrix W_{kj} = g^{jk}, the reversal J, the normalised operator F = iW, the four projectors Π_ℓ,
    the fractional family F^[s] = Σ_ℓ g^{−ℓs} Π_ℓ, rank mod p;
  * the PASS/FAIL registry every block reports into (results.json).

Kinds: EXACT checks are integer-pinned computations in F_p (a pass is a proof on the tested instances); [approx] checks
compare a floating-point observation with the value the paper states, to a stated tolerance (block E, the cyclotomic
observer readout on C^n; E1 is exact integer polynomial arithmetic). Block E regenerates the paper's one numerical
figure into FIGDIR (figures/, or $FOURIER_FIGDIR).
"""
import os, json, sys, re
import numpy as np

SCRIPT = os.path.splitext(os.path.basename(__file__))[0]        # "fourier": the one script, the name results.json and the site pages carry
FIGDIR = os.environ.get("FOURIER_FIGDIR", "figures")             # block E writes the figure here (created when the block runs)

# The shells of Table tab:checks (p, κ, g, i); the package recomputes g and i and checks the table.
TABLE = [(5, 1, 2, 3), (13, 3, 2, 5), (17, 4, 3, 4), (29, 7, 2, 17), (37, 9, 2, 6), (41, 10, 6, 9)]
SHELLS = [p for p, _, _, _ in TABLE]

# ----------------------------------------------------------------------------- registry
RESULTS = []

# The paper's predicate ledger (Appendix A, predicates cited as 6:XN): the predicate(s) each check witnesses.
LEDGER = {
    "A1": "6:B1", "A2": "6:B2", "A3": "6:B3", "A4": "6:B5", "A5": "6:B6", "A6": "6:B7",
    "B1": "6:C2", "B2": "6:C3", "B3": "6:C3", "B4": "6:C4", "B5": "6:C5", "B6": "6:C6", "B7": "6:C7", "B8": "6:C7",
    "B9": "6:C8", "B10": "6:C9",
    "C1": "6:D1", "C2": "6:D2", "C3": "6:D2", "C4": "6:D4", "C5": "6:D4", "C6": "6:D5",
    "D1": "6:E2", "D2": "6:E2", "D3": "6:E3", "D4": "6:E5", "D5": "6:E6", "D6": "6:E7", "D7": "6:E7", "D8": "6:E8",
    "E1": "6:F2", "E2": "6:F3", "E3": "6:F3", "E4": "6:F4", "E5": "6:F5", "E6": "6:F6", "E7": "6:F7",
}
# The master-ledger predicates of the corpus witnessed through the paper's: 00:C2 (6:B5, 6:C3, 6:D4), 00:C14 (6:B2),
# 00:C7 on the transform layer (6:C9).

BLOCK = {"A": "the frame datum and the shell Fourier operator",          # check-id prefix -> the block (the function block_<letter> below)
         "B": "the fractional family F^[s]",
         "C": "representation domains and the coordinate zoom",
         "D": "the Weil dictionary and the operator-level comparison",
         "E": "the cyclotomic observer readout and the entropy cycle"}

# the deciding check of each witnessed predicate: the one whose verdict decides the predicate's statement (the other checks
# that touch it are corroboration, listed by predicate() from the records): the first check of a two-check predicate, except
# E2 (D2, the isomorphism and the count; D1's membership corroborates) and E7 (D6, the covariance identities; D7 the sweep)
PREDICATES = {
    "6:B1": "A1", "6:B2": "A2", "6:B3": "A3", "6:B5": "A4", "6:B6": "A5", "6:B7": "A6",
    "6:C2": "B1", "6:C3": "B2", "6:C4": "B4", "6:C5": "B5", "6:C6": "B6", "6:C7": "B7", "6:C8": "B9", "6:C9": "B10",
    "6:D1": "C1", "6:D2": "C2", "6:D4": "C4", "6:D5": "C6",
    "6:E2": "D2", "6:E3": "D3", "6:E5": "D4", "6:E6": "D5", "6:E7": "D6", "6:E8": "D8",
    "6:F2": "E1", "6:F3": "E2", "6:F4": "E4", "6:F5": "E5", "6:F6": "E6", "6:F7": "E7",
}
_RAN = set()                                            # blocks already run in this session (predicate() runs each once)

def check(pid, label, ok, detail="", kind="EXACT"):
    """Record one predicate check. pid = package check id; LEDGER[pid] = the paper statement(s) decided."""
    ok = bool(ok)
    rows = LEDGER.get(pid, "")
    RESULTS.append({"id": pid, "rows": rows, "block": pid[0], "script": SCRIPT, "label": label, "ok": ok, "detail": detail, "kind": kind})
    print(f"  [{'PASS' if ok else 'FAIL'}] {pid:4s} {kind:7s} [{rows}] {label}" + (f"  --  {detail}" if detail else ""))
    return ok

def summary(write=True):
    n_ok = sum(r["ok"] for r in RESULTS)
    print(f"\nSUMMARY: {n_ok}/{len(RESULTS)} checks passed" + ("" if n_ok == len(RESULTS) else "  <-- FAILURES"))
    if write:
        with open("results.json", "w") as f:
            json.dump(RESULTS, f, indent=1)
    return n_ok == len(RESULTS)

def markers():
    """predicate label -> (script file, line) of its marker `# <paper>:<label> (<key>)`: the line of the check that decides it."""
    out = {}
    for i, line in enumerate(open(os.path.abspath(__file__), encoding="utf-8"), 1):
        m = re.match(r"\s*# ((?:\d+:[A-Z]+\d+[a-z]?(?: \(p\d{5}\))?)(?:, \d+:[A-Z]+\d+[a-z]?(?: \(p\d{5}\))?)*)\s*$", line)
        if m:
            for lab in re.findall(r"\d+:[A-Z]+\d+[a-z]?", m.group(1)): out.setdefault(lab, (SCRIPT + ".py", i))
    return out

def _run_block(letter):
    if letter not in _RAN:
        globals()[f"block_{letter}"](); _RAN.add(letter)

def predicate(label, lines=14):
    """Verify one ledger predicate: run the block of the check that decides it (once per session), print that check's source
    (from its marker) and every record that cites the predicate, and return True iff all pass."""
    pid = PREDICATES.get(label)
    if pid is None:
        print(f"{label}: no python witness (see the predicate's Lean witness or its source)"); return None
    citing = {i[0] for i, rows in LEDGER.items() if label in [t.strip() for t in rows.split(",")]}
    for b in sorted({pid[0]} | citing): _run_block(b)          # the deciding block and every block whose checks cite the predicate
    mk = markers().get(label)
    if mk:
        src = open(os.path.abspath(__file__), encoding="utf-8").read().split("\n")
        print(f"— {mk[0]}:{mk[1]} (the check that decides {label}: {pid})")
        for j in range(mk[1] - 1, min(mk[1] - 1 + lines, len(src))): print(f"{j + 1:5d}  {src[j]}")
    recs = [r for r in RESULTS if label in [t.strip() for t in r["rows"].split(",")]]
    ok = all(r["ok"] for r in recs)
    for r in recs:
        role = "(deciding)" if r["id"] == pid else "(corroborating)"
        print(f"  [{'PASS' if r['ok'] else 'FAIL'}] {r['id']:4s} {role:16s} {r['detail'][:150]}")
    print(f"{label}: {'VERIFIED' if ok and recs else 'FAILED'} — {len(recs)} record(s)")
    return ok

def verify_all():
    """Run every block (those already run in this session are not re-run) and print the summary; True iff every check passed."""
    for b in sorted(BLOCK): _run_block(b)
    return summary(write=False)

# ----------------------------------------------------------------------------- the frame datum
def prime_factors(n):
    f, d = set(), 2
    while d * d <= n:
        while n % d == 0:
            f.add(d); n //= d
        d += 1
    if n > 1: f.add(n)
    return f

def order(a, p):
    o, x = 1, a % p
    while x != 1:
        x = x * a % p; o += 1
    return o

def primitive_root(p):
    """The smallest primitive root of F_p (the generators of Table tab:checks)."""
    for g in range(2, p):
        if all(pow(g, (p - 1) // q, p) != 1 for q in prime_factors(p - 1)):
            return g

def primitive_roots(p):
    return [g for g in range(2, p) if order(g, p) == p - 1]

class Frame:
    """The framed shell F_p(t; 0, 1, g): p = 4κ+1, g primitive, i = −g^κ (the oriented quarter-turn,
    clockwise phase convention eq:it-def), π = 2κ, e = g^i, n = p−1 = 4κ."""
    def __init__(self, p, g=None):
        assert p % 4 == 1
        self.p, self.n, self.kap = p, p - 1, (p - 1) // 4
        self.g = primitive_root(p) if g is None else g
        assert order(self.g, p) == p - 1
        self.i = (-pow(self.g, self.kap, p)) % p
        self.pi = 2 * self.kap
        self.e = pow(self.g, self.i, p)
        self.inv2 = pow(2, p - 2, p)
        self.inv4 = pow(4, p - 2, p)
        self._W = self._F = self._Pi = None

    def conjugate(self):
        """The conjugate reframing (g, i) ↦ (g⁻¹, −i)."""
        return Frame(self.p, pow(self.g, self.p - 2, self.p))

    def gpow(self, k):
        return pow(self.g, int(k) % self.n, self.p)

    # --- matrices over F_p (int64, entries in [0, p))
    @property
    def W(self):
        if self._W is None:
            self._W = np.array([[self.gpow(j * k) for j in range(self.n)] for k in range(self.n)], dtype=np.int64)   # W_{k,j} = g^{jk}
        return self._W

    @property
    def F(self):
        if self._F is None:
            self._F = (self.i * self.W) % self.p
        return self._F

    @property
    def J(self):
        return J_matrix(self.n)

    def I(self):
        return np.eye(self.n, dtype=np.int64)

    @property
    def Pi(self):
        """The four projectors Π_ℓ = ¼ Σ_{r=0}^{3} i^{−ℓr} F^r (eq:projector-def)."""
        if self._Pi is None:
            Fs = [self.I()]
            for _ in range(3):
                Fs.append(mm(Fs[-1], self.F, self.p))
            inv_i = pow(self.i, self.p - 2, self.p)
            self._Pi = []
            for ell in range(4):
                P = np.zeros((self.n, self.n), dtype=np.int64)
                for r in range(4):
                    P = (P + pow(inv_i, ell * r, self.p) * Fs[r]) % self.p
                self._Pi.append((self.inv4 * P) % self.p)
            self._Fpows = Fs
        return self._Pi

    def Fpow(self, r):
        self.Pi
        return self._Fpows[r % 4]

    def frft(self, s):
        """F^[s] = Σ_ℓ g^{−ℓ s} Π_ℓ (eq:FRC-FrFT-def), s ∈ Z_{4κ}."""
        M = np.zeros((self.n, self.n), dtype=np.int64)
        for ell, P in enumerate(self.Pi):
            M = (M + self.gpow(-ell * s) * P) % self.p
        return M

    def mults(self):
        """(m_0, m_1, m_2, m_3) = rank Π_ℓ over F_p."""
        return tuple(rank_mod_p(P, self.p) for P in self.Pi)

    def gauss(self):
        """The frame's exponent-cycle Gauss sum G = Σ_{k ∈ Z_{4κ}} g^{k²} (thm:multiplicity)."""
        return sum(self.gpow(k * k) for k in range(self.n)) % self.p

    def epsilon(self):
        """The sign ε with G = ε(1+i), or None if G is neither."""
        G, onepi = self.gauss(), (1 + self.i) % self.p
        return 1 if G == onepi else (-1 if G == (-onepi) % self.p else None)

    # --- coordinate side
    def meridian(self, m):
        """M_m = {a g^m : a ∈ I_p}, I_p = {0, …, π} (eq:meridian-def, eq:Ip-zoom), as the ordered tuple."""
        em = self.gpow(m)
        return tuple((a * em) % self.p for a in range(self.pi + 1))

    def S(self, r, x):
        """The meridian-scale map S_r(x) = g^r x (def:scale-map)."""
        return (self.gpow(r) * x) % self.p

    # --- the Weil side
    def z(self, s):
        return self.gpow(-s)                                       # z_s = g^{−s} (eq:zs-def)

    def R(self, s):
        """R_s = [[c_s, −d_s], [d_s, c_s]], c_s = (z+z⁻¹)/2, d_s = (z−z⁻¹)/(2i) (eq:csds-def, eq:Rs-def)."""
        p, z = self.p, self.z(s)
        zi = pow(z, p - 2, p)
        c = ((z + zi) * self.inv2) % p
        d = ((z - zi) * self.inv2 * pow(self.i, p - 2, p)) % p
        return np.array([[c, (-d) % p], [d, c]], dtype=np.int64)

# ----------------------------------------------------------------------------- matrix arithmetic mod p
def mm(A, B, p):
    return (A @ B) % p

def J_matrix(n):
    J = np.zeros((n, n), dtype=np.int64)
    for k in range(n):
        J[k, (-k) % n] = 1
    return J

def eq(A, B, p):
    return bool(np.array_equal(A % p, B % p))

def rank_mod_p(M, p):
    A = (M % p).astype(np.int64).copy()
    n, m = A.shape
    r = 0
    for col in range(m):
        piv = next((i for i in range(r, n) if A[i, col] % p), None)
        if piv is None:
            continue
        A[[r, piv]] = A[[piv, r]]
        A[r] = (A[r] * pow(int(A[r, col]), p - 2, p)) % p
        for i in range(n):
            if i != r and A[i, col]:
                A[i] = (A[i] - A[i, col] * A[r]) % p
        r += 1
        if r == n:
            break
    return r

def is_monomial(M):
    """Exactly one nonzero entry in every row and every column."""
    nz = (M != 0)
    return bool(np.all(nz.sum(0) == 1) and np.all(nz.sum(1) == 1))

def matpow(M, k, p):
    R = np.eye(M.shape[0], dtype=np.int64)
    for _ in range(k):
        R = mm(R, M, p)
    return R

def jacobi(a, n):
    """The Jacobi symbol (a/n), n odd positive."""
    assert n > 0 and n % 2 == 1
    a %= n; result = 1
    while a:
        while a % 2 == 0:
            a //= 2
            if n % 8 in (3, 5): result = -result
        a, n = n, a
        if a % 4 == 3 and n % 4 == 3: result = -result
        a %= n
    return result if n == 1 else 0

# ------------------------------------------------------------------------------------------------------------
# Block A — the frame datum and the shell Fourier operator (EXACT, integer-pinned)
# ================================================================================
# Paper statements decided (Sections 3–4; master ledger rows 00:C2, 00:C14):
#
#   A1  §3 shell data, tab:checks   p = 4κ+1, the generator g of Table tab:checks is the smallest primitive
#                                    root, i = −g^κ = g^{−κ} = g^{3κ}, i² ≡ −1, π = 2κ, 2π ≡ −1, g^π ≡ −1,
#                                    −π ≡ 2⁻¹, e = g^i; the table's (κ, g, i) on all six shells
#   A2  §3 (Euler identity)          e^{iπ} = g^{2κ(i mod 2)} ≡ −1 exactly when the quarter-turn residue i is
#       00:C14                       odd; the conjugate reframing (g, i) ↦ (g⁻¹, −i) toggles the parity, so
#                                    exactly one member of each conjugate pair carries e^{iπ} ≡ −1 — on every
#                                    primitive frame of the six shells; anchor F_13(t;0,1,2): i = 5, 6^{iπ} ≡ −1
#   A3  rem:gt-covariance            the relabelling g' = g^u, u ∈ Z_{4κ}^×: i' = i iff u ≡ 1 (mod 4), i' = −i
#                                    iff u ≡ 3 (mod 4); e' = g^{ui} ≠ e whenever i(u−1) ≢ 0 (mod 4κ), as at
#                                    p = 13, g = 2, u = 5: e' = 2 ≠ 6 = e
#   A4  lem:W-square, prop:F-cycle   W² = −J, (iW)² = J, (iW)⁴ = I on the six shells (the three boolean
#       tab:checks; 00:C2            columns of Table tab:checks)
#   A5  rem:unitary-norm             the square roots of 1/n = −1 in F_p are exactly ±i; (cW)² = J iff c = ±i
#   A6  lem:JF-decomp                WJ = JW, FJ = JF; dim V⁺ = 2κ+1, dim V⁻ = 2κ−1
#
# Shells: p = 5, 13, 17, 29, 37, 41 (Table tab:checks), every primitive frame of each for A2 and A3.
def block_A():
    """Block A — the frame datum and the shell Fourier operator (EXACT, integer-pinned): A1–A6."""
    print("block A — the frame datum and the shell Fourier operator")
    frames = {p: Frame(p) for p in SHELLS}

    # A1 — the shell data and the table
    ok, rows = True, []
    for p, kap, g, i in TABLE:
        f = frames[p]
        ok &= (p == 4 * kap + 1 and f.kap == kap and f.g == g and f.i == i)
        ok &= (f.i == (-pow(g, kap, p)) % p == pow(g, p - 1 - kap, p) == pow(g, 3 * kap, p))
        ok &= (f.i * f.i % p == p - 1)
        ok &= (f.pi == 2 * kap and (2 * f.pi) % p == p - 1 and pow(g, f.pi, p) == p - 1)
        ok &= ((-f.pi) % p == f.inv2)
        ok &= (f.e == pow(g, i, p))
        rows.append(f"F_{p}(κ={kap}, g={g}, i={i}, e={f.e})")
    # 6:B1 (p06008)
    check("A1", "p = 4κ+1, g the smallest primitive root, i = −g^κ = g^{−κ}, i² ≡ −1, π = 2κ, 2π ≡ −1, g^π ≡ −1, −π ≡ 2⁻¹, e = g^i; Table tab:checks (κ, g, i)",
          ok, "; ".join(rows))

    # A2 — the Euler identity on the odd member (00:C14)
    ok, n_frames, n_carry = True, 0, 0
    for p in SHELLS:
        for g in primitive_roots(p):
            f = Frame(p, g)
            euler = pow(f.e, f.i * f.pi, p)                       # e^{iπ} = (g^i)^{iπ}
            ok &= (euler == pow(g, f.pi * (f.i % 2), p))          # = g^{2κ (i mod 2)}
            ok &= ((euler == p - 1) == (f.i % 2 == 1))            # ≡ −1 iff i odd
            fc = f.conjugate()
            ok &= (fc.i == (-f.i) % p and fc.i % 2 != f.i % 2)    # the conjugate toggles the parity
            carries_c = pow(fc.e, fc.i * fc.pi, p) == p - 1
            ok &= ((euler == p - 1) != carries_c)                 # exactly one member of the pair
            n_frames += 1; n_carry += (euler == p - 1)
    f13 = frames[13]
    ok &= (f13.i == 5 and f13.e == 6 and pow(6, 5 * 6, 13) == 12 and pow(6, 6, 13) == 12)
    # 6:B2 (p06009)
    check("A2", "e^{iπ} = g^{2κ(i mod 2)} ≡ −1 exactly on the odd quarter-turn; the conjugate reframing toggles it, one member of each pair carries it",
          ok, f"{n_frames} primitive frames of p ∈ {SHELLS}, {n_carry} carry e^{{iπ}} ≡ −1 (one per conjugate pair); F_13(t;0,1,2): i = 5, e = 6, 6^{{30}} = 6^{{6}} ≡ −1")

    # A3 — the u-relabelling
    ok = True
    for p in SHELLS:
        f = frames[p]
        for u in range(1, f.n):
            if np.gcd(u, f.n) != 1:
                continue
            fu = Frame(p, pow(f.g, u, p))
            ok &= (fu.i == f.i) if u % 4 == 1 else (fu.i == (-f.i) % p)
            if u % 4 == 1:
                ok &= (fu.e == pow(f.g, u * f.i, p))
                ok &= ((fu.e != f.e) == ((f.i * (u - 1)) % f.n != 0))
    f5 = Frame(13, pow(2, 5, 13))
    ok &= (f5.i == f13.i and f5.e == 2 and f13.e == 6 and pow(6, 5, 13) == 2)
    # 6:B3 (p06010)
    check("A3", "g' = g^u: the quarter-turn flips only on u ≡ 3 (mod 4); e' = g^{ui} ≠ e iff i(u−1) ≢ 0 (mod 4κ); at p = 13, u = 5: e' = 2 ≠ 6",
          ok, "every unit u of Z_{4κ} on the six shells; F_13, g' = 2^5 = 6: i' = 5, e' = 6^5 = 2")

    # A4 — the operator identities of Table tab:checks (00:C2)
    ok, det = True, []
    for p in SHELLS:
        f = frames[p]
        W2 = mm(f.W, f.W, p); F2 = mm(f.F, f.F, p); F4 = mm(F2, F2, p)
        a, b, c = eq(W2, (-f.J) % p, p), eq(F2, f.J, p), eq(F4, f.I(), p)
        ok &= a and b and c
        det.append(f"p={p}: {a},{b},{c}")
    # 6:B5 (p06012)
    check("A4", "W² = −J, (iW)² = J, (iW)⁴ = I on the six shells of Table tab:checks", ok, "; ".join(det))

    # A5 — the unitary normalisation read in the field
    ok = True
    for p in SHELLS:
        f = frames[p]
        roots = sorted(c for c in range(p) if c * c % p == p - 1)
        ok &= (roots == sorted([f.i, (-f.i) % p]))
        ok &= ((1 * pow(f.n, p - 2, p)) % p == p - 1)                        # 1/n = −1
        for c in range(1, p):
            ok &= (eq(mm(c * f.W % p, c * f.W % p, p), f.J, p) == (c in roots))
    # 6:B6 (p06013)
    check("A5", "the square roots of 1/n ≡ −1 in F_p are exactly ±i, the two unitary normalisations of W: (cW)² = J iff c = ±i", ok, f"every c ∈ F_p^× tested on p ∈ {SHELLS}")

    # A6 — the symmetric/antisymmetric decomposition
    ok, det = True, []
    for p in SHELLS:
        f = frames[p]
        ok &= eq(mm(f.W, f.J, p), mm(f.J, f.W, p), p) and eq(mm(f.F, f.J, p), mm(f.J, f.F, p), p)
        dplus = f.n - rank_mod_p((f.J - f.I()) % p, p); dminus = f.n - rank_mod_p((f.J + f.I()) % p, p)
        ok &= (dplus == 2 * f.kap + 1 and dminus == 2 * f.kap - 1)
        det.append(f"p={p}: dim V⁺={dplus}, V⁻={dminus}")
    # 6:B7 (p06014)
    check("A6", "WJ = JW, FJ = JF; dim V⁺ = 2κ+1, dim V⁻ = 2κ−1", ok, "; ".join(det))

# ------------------------------------------------------------------------------------------------------------
# Block B — the fractional family F^[s] = Σ_ℓ g^{−ℓs} Π_ℓ (EXACT, integer-pinned)
# ===============================================================================
# Paper statements decided (Section 5; master ledger rows 00:C2, 00:C7):
#
#   B1  lem:projectors        Π_ℓ² = Π_ℓ, Π_ℓ Π_m = 0 (ℓ ≠ m), Σ_ℓ Π_ℓ = I, F Π_ℓ = i^ℓ Π_ℓ
#   B2  thm:FRC-FrFT          additivity F^[s+r] = F^[s] F^[r] on every pair (s, r) ∈ Z_{4κ}²      (00:C2)
#   B3  thm:FRC-FrFT          cardinal values F^[0] = I, F^[κ] = F, F^[2κ] = J, F^[3κ] = F⁻¹, F^[4κ] = I;
#                             (F^[1])^κ = F                                                     (00:C2)
#   B4  thm:faithful          s ↦ F^[s] injective on Z_{4κ} (p = 5 included: the surviving odd projector
#                             carries a faithful character)
#   B5  lem:multiplicity      m_ℓ = rank Π_ℓ = dim ker(F − i^ℓ I); m_0 + m_2 = 2κ+1, m_1 + m_3 = 2κ−1;
#                             m_0, m_2 ≥ 1; m_1, m_3 ≥ 1 for κ ≥ 2; at p = 5 exactly one of Π_1, Π_3 is 0
#   B6  rem:multiplicities    p = 13: g = 2 gives (3,3,4,2) with Tr F = 4, g = 6 gives (4,2,3,3) with Tr F = 9;
#                             the vertex relabelling m ↦ um conjugates F(g) to F(g^{u²}) by a permutation
#   B7  thm:multiplicity      G = Σ_k g^{k²} = ε(1+i); the two patterns (κ,κ,κ+1,κ−1) / (κ+1,κ−1,κ,κ);
#                             ε(g⁻¹) = −ε(g); ε(g^u) = (κ/u) ε(g) for u ≡ 1 (mod 4); the classes equally
#                             populated on every shell; the 38 primitive frames of p ∈ {5,13,17,29,37} (and
#                             the 16 of p = 41); the table frames with κ ≥ 2 in class ε = +1; p = 5:
#                             (2,0,1,1) at g = 2 (ε = −1), (1,1,2,0) at g = 3 (ε = +1)
#   B8  thm:multiplicity      the proof's identities: G G* = −2, G² = 2i, Tr F = iG, Tr F² = 2, Tr F³ = iG*,
#       (proof)               m_ℓ ≡ ¼ Σ_r i^{−ℓr} Tr F^r (mod p)
#   B9  rem:classification    every exponent lift a_ℓ ≡ ℓ (mod 4) is additive with the same cardinal
#                             skeleton; the family canonical in the chart g^u with u² ≢ 1 (mod 4κ) does not
#                             commute with F — at p = 29, u = 5 (u² = 25 ≢ 1 mod 28)
#   B10 rem:gt-covariance     the conjugate reframing (g, i) ↦ (g⁻¹, −i): operator relations, cardinal
#       00:C7 (transform      values, additivity and faithfulness hold on the conjugate frame, while the
#       layer)                multiplicity tuple flips between the two patterns (chart data); exactly
#                             F' = −F⁻¹ and Π'_ℓ = Π_{ℓ+2}
#
# Shells: p = 5, 13, 17, 29, 37, 41; every primitive frame for B7.
def block_B():
    """Block B — the fractional family F^[s] = Σ_ℓ g^{−ℓs} Π_ℓ (EXACT, integer-pinned): B1–B10."""
    print("block B — the fractional family")
    frames = {p: Frame(p) for p in SHELLS}

    # B1 — the projectors
    ok = True
    for p in SHELLS:
        f = frames[p]; Pi = f.Pi
        S = np.zeros((f.n, f.n), dtype=np.int64)
        for l in range(4):
            S = (S + Pi[l]) % p
            ok &= eq(mm(Pi[l], Pi[l], p), Pi[l], p)
            ok &= eq(mm(f.F, Pi[l], p), pow(f.i, l, p) * Pi[l], p)
            for m in range(4):
                if m != l:
                    ok &= eq(mm(Pi[l], Pi[m], p), np.zeros_like(S), p)
        ok &= eq(S, f.I(), p)
    # 6:C2 (p06016)
    check("B1", "Π_ℓ² = Π_ℓ, Π_ℓ Π_m = 0, Σ Π_ℓ = I, F Π_ℓ = i^ℓ Π_ℓ", ok, f"p ∈ {SHELLS}")

    # B2 — additivity on every pair
    ok, npairs = True, 0
    for p in SHELLS:
        f = frames[p]
        fam = [f.frft(s) for s in range(f.n)]
        for s in range(f.n):
            for r in range(f.n):
                ok &= eq(mm(fam[s], fam[r], p), fam[(s + r) % f.n], p); npairs += 1
        f._fam = fam
    # 6:C3 (p06017)
    check("B2", "F^[s+r] = F^[s] F^[r] on every pair (s, r) of Z_{4κ}", ok, f"{npairs} pairs over p ∈ {SHELLS}")

    # B3 — cardinal values
    ok = True
    for p in SHELLS:
        f = frames[p]; fam = f._fam; k = f.kap
        F3 = matpow(f.F, 3, p)
        ok &= eq(fam[0], f.I(), p) and eq(fam[k], f.F, p) and eq(fam[2 * k], f.J, p) and eq(fam[3 * k], F3, p)
        ok &= eq(mm(F3, f.F, p), f.I(), p)                       # F³ = F⁻¹
        ok &= eq(matpow(fam[1], k, p), f.F, p)
    check("B3", "F^[0] = I, F^[κ] = F, F^[2κ] = J, F^[3κ] = F⁻¹, F^[4κ] = I; (F^[1])^κ = F", ok, f"p ∈ {SHELLS}")

    # B4 — faithfulness
    ok = True
    for p in SHELLS:
        f = frames[p]; fam = f._fam
        ok &= all(not eq(fam[s], f.I(), p) for s in range(1, f.n))
        ok &= len({fam[s].tobytes() for s in range(f.n)}) == f.n
    # 6:C4 (p06018)
    check("B4", "s ↦ F^[s] is injective on Z_{4κ}: the 4κ members are pairwise distinct (p = 5 included)", ok, f"p ∈ {SHELLS}")

    # B5 — the multiplicity lemma
    ok, det = True, []
    for p in SHELLS:
        f = frames[p]; m = f.mults()
        for l in range(4):
            ok &= (m[l] == f.n - rank_mod_p((f.F - pow(f.i, l, p) * f.I()) % p, p))
        ok &= (m[0] + m[2] == 2 * f.kap + 1 and m[1] + m[3] == 2 * f.kap - 1 and m[0] >= 1 and m[2] >= 1)
        ok &= (m[1] >= 1 and m[3] >= 1) if f.kap >= 2 else ((m[1] == 0) != (m[3] == 0))
        det.append(f"p={p}: {m}")
    # 6:C5 (p06019)
    check("B5", "m_ℓ = rank Π_ℓ = dim ker(F − i^ℓ I); m_0+m_2 = 2κ+1, m_1+m_3 = 2κ−1; m_0, m_2 ≥ 1; m_1, m_3 ≥ 1 for κ ≥ 2; p = 5: one odd projector vanishes", ok, "; ".join(det))

    # B6 — multiplicities are chart data
    f2, f6 = Frame(13, 2), Frame(13, 6)
    ok = (f2.mults() == (3, 3, 4, 2) and f6.mults() == (4, 2, 3, 3))
    ok &= (int(np.trace(f2.F)) % 13 == 4 and int(np.trace(f6.F)) % 13 == 9)
    ok &= (pow(2, 5, 13) == 6)                                    # same orientation class: 6 = 2^5, 5 ≡ 1 (mod 4)
    nconj = 0
    for p in SHELLS:
        f = frames[p]
        for u in range(1, f.n):
            if np.gcd(u, f.n) != 1:
                continue
            fu = Frame(p, pow(f.g, u * u, p))
            perm = [(u * k) % f.n for k in range(f.n)]
            ok &= eq(fu.F, f.F[np.ix_(perm, perm)], p); nconj += 1
    # 6:C6 (p06020)
    check("B6", "p = 13: g = 2 gives (3,3,4,2), Tr F = 4; g = 6 gives (4,2,3,3), Tr F = 9; m ↦ um carries F(g) to F(g^{u²}) by a permutation", ok, f"{nconj} relabellings over p ∈ {SHELLS}")

    # B7 — the multiplicity dichotomy on every primitive frame
    ok, det, n38 = True, [], 0
    for p in SHELLS:
        f0 = frames[p]; k = f0.kap
        prims = primitive_roots(p)
        eps = {}
        for g in prims:
            f = Frame(p, g); e = f.epsilon()
            ok &= (e is not None)
            eps[g] = e
            want = (k, k, k + 1, k - 1) if e == 1 else (k + 1, k - 1, k, k)
            ok &= (f.mults() == want)
        for g in prims:
            ok &= (eps[pow(g, p - 2, p)] == -eps[g])                                     # conjugate law
            for u in range(1, f0.n):
                if np.gcd(u, f0.n) == 1 and u % 4 == 1:
                    ok &= (eps[pow(g, u, p)] == jacobi(k, u) * eps[g])                # Jacobi law
        ok &= (2 * sum(1 for g in prims if eps[g] == 1) == len(prims))                 # even split
        if k >= 2:
            ok &= (eps[f0.g] == 1)                                                       # the table frames
        if p != 41:
            n38 += len(prims)
        det.append(f"p={p}: {len(prims)} frames, ε=+1 on {sum(1 for g in prims if eps[g] == 1)}")
    ok &= (n38 == 38)
    ok &= (Frame(5, 2).mults() == (2, 0, 1, 1) and Frame(5, 2).epsilon() == -1)
    ok &= (Frame(5, 3).mults() == (1, 1, 2, 0) and Frame(5, 3).epsilon() == 1)
    # 6:C7 (p06021)
    check("B7", "G = ε(1+i), the two patterns, ε(g⁻¹) = −ε(g), ε(g^u) = (κ/u) ε(g), classes equally populated; 38 frames of p ∈ {5,…,37} and 16 of p = 41; p = 5: (2,0,1,1) at g = 2, (1,1,2,0) at g = 3",
          ok, "; ".join(det))

    # B8 — the proof's identities
    ok = True
    for p in SHELLS:
        for g in primitive_roots(p):
            f = Frame(p, g)
            G = f.gauss(); Gs = sum(f.gpow(-k * k) for k in range(f.n)) % p
            ok &= (G * Gs % p == p - 2 and G * G % p == 2 * f.i % p)
            tr = [int(np.trace(f.Fpow(r))) % p for r in range(4)]
            ok &= (tr[1] == f.i * G % p and tr[2] == 2 and tr[3] == f.i * Gs % p)
            m = f.mults()
            inv_i = pow(f.i, p - 2, p)
            for l in range(4):
                ok &= (m[l] % p == f.inv4 * sum(pow(inv_i, l * r, p) * tr[r] for r in range(4)) % p)
    check("B8", "G G* = −2, G² = 2i, Tr F = iG, Tr F² = 2, Tr F³ = iG*, m_ℓ ≡ ¼ Σ_r i^{−ℓr} Tr F^r (mod p)", ok, "every primitive frame of the six shells")

    # B9 — classification: exponent lifts and the non-commuting chart
    f = frames[13]; ok = True
    for a in [(0, 1, 2, 3), (0, 5, 2, 3), (4, 1, 6, 7), (0, 1, 2, 11)]:
        U = [sum(f.gpow(-a[l] * s) * f.Pi[l] for l in range(4)) % 13 for s in range(12)]
        ok &= all(eq(mm(U[s], U[r], 13), U[(s + r) % 12], 13) for s in range(12) for r in range(12))
        ok &= eq(U[0], f.I(), 13) and eq(U[3], f.F, 13) and eq(U[6], f.J, 13) and eq(U[9], matpow(f.F, 3, 13), 13)
    f29 = frames[29]; f29u = Frame(29, pow(f29.g, 5, 29))
    ok &= (25 % 28 != 1)
    noncomm = not eq(mm(f29u.frft(1), f29.F, 29), mm(f29.F, f29u.frft(1), 29), 29)
    ok &= noncomm
    scan = []
    for p in SHELLS:
        f0 = frames[p]
        for u in range(1, f0.n):
            if np.gcd(u, f0.n) == 1 and (u * u) % f0.n != 1:
                fu = Frame(p, pow(f0.g, u, p))
                scan.append((p, u, not eq(mm(fu.frft(1), f0.F, p), mm(f0.F, fu.frft(1), p), p)))
    # 6:C8 (p06022)
    check("B9", "exponent lifts a_ℓ ≡ ℓ (mod 4) are additive with the cardinal skeleton (p = 13); the chart g^5 at p = 29 (u² ≢ 1 mod 28) does not commute with F",
          ok, f"non-commuting at p = 29, u = 5: {noncomm}; all charts with u² ≢ 1 (mod 4κ) on the six shells non-commuting: {all(x[2] for x in scan)} ({len(scan)} charts)")

    # B10 — the conjugate reframing (00:C7, transform layer)
    ok, det = True, []
    for p in SHELLS:
        f = frames[p]; fc = f.conjugate(); k = f.kap
        ok &= (fc.i == (-f.i) % p)
        Finv = matpow(f.F, 3, p)
        ok &= eq(fc.F, (-Finv) % p, p)                                             # F' = −F⁻¹
        ok &= eq(mm(fc.F, fc.F, p), f.J, p) and eq(matpow(fc.F, 4, p), f.I(), p)
        famc = [fc.frft(s) for s in range(f.n)]
        ok &= eq(famc[0], f.I(), p) and eq(famc[k], fc.F, p) and eq(famc[2 * k], f.J, p)
        ok &= all(eq(mm(famc[s], famc[r], p), famc[(s + r) % f.n], p) for s in range(f.n) for r in range(0, f.n, 3))
        ok &= len({M.tobytes() for M in famc}) == f.n
        ok &= all(eq(fc.Pi[l], f.Pi[(l + 2) % 4], p) for l in range(4))                 # Π'_ℓ = Π_{ℓ+2}
        m, mc = f.mults(), fc.mults()
        ok &= (mc == (m[2], m[3], m[0], m[1]) and {m, mc} == {(k, k, k + 1, k - 1), (k + 1, k - 1, k, k)})
        det.append(f"p={p}: {m} ↦ {mc}")
    # 6:C9 (p06023)
    check("B10", "the conjugate frame (g⁻¹, −i) keeps the operator relations, cardinal values, additivity and faithfulness; its multiplicity tuple is the other pattern; F' = −F⁻¹, Π'_ℓ = Π_{ℓ+2}",
          ok, "; ".join(det))

# ------------------------------------------------------------------------------------------------------------
# Block C — representation domains and the coordinate-side zoom (EXACT, integer-pinned)
# =====================================================================================
# Paper statements decided (Sections 6–7; master ledger row 00:C2):
#
#   C1  def:domain            every F^[s] is invertible (rank 4κ over F_p); its eigenvalues g^{−ℓs} are
#                             nonzero, so the meridional bases B_s = F^[s] B_0 are bases
#   C2  cor:distinct-domains  the 4κ framed (ordered) bases B_0, …, B_{4κ−1} are pairwise distinct
#   C3  rem:ordered-bases     B_{s+2κ} = B_s as unordered sets (F^[s+2κ] = F^[s] J, J a coordinate
#                             permutation): the cycle carries exactly 2κ unordered measurement bases
#   C4  prop:meridian-scale   S_r(M_m) = M_{m+r} for every (m, r) ∈ Z_{4κ}², as ordered lists  (00:C2)
#   C5  cor:effective-step    consecutive entries of M_m differ by g^m; S_{r+(p−1)} = S_r
#       rem:framed-rational
#   C6  ex:zoom-13            p = 13, g = 2: M_0 … M_3 as printed (steps 1, 2, 4, 8); the no-wrap window of
#       thm:zoom, rem:two-    rem:two-layers — with w = π = 6 the listing stays unwrapped for w·2^r < 13, i.e.
#       layers                r ≤ 1, and wraps from M_2 on
#
# Shells: p = 5, 13, 17, 29, 37, 41.
def block_C():
    """Block C — representation domains and the coordinate-side zoom (EXACT, integer-pinned): C1–C6."""
    print("block C — representation domains and the coordinate-side zoom")
    frames = {p: Frame(p) for p in SHELLS}

    # C1 — invertibility
    ok = True
    for p in SHELLS:
        f = frames[p]
        fam = [f.frft(s) for s in range(f.n)]; f._fam = fam
        ok &= all(rank_mod_p(M, p) == f.n for M in fam)
        ok &= all(f.gpow(-l * s) != 0 for s in range(f.n) for l in range(4))
    # 6:D1 (p06024)
    check("C1", "every F^[s] has full rank 4κ over F_p; the eigenvalues g^{−ℓs} are nonzero", ok, f"p ∈ {SHELLS}")

    # C2 — the framed bases are pairwise distinct
    ok = True
    for p in SHELLS:
        f = frames[p]
        ordered = {tuple(map(tuple, M.T)) for M in f._fam}          # B_s = the ordered columns of F^[s]
        ok &= (len(ordered) == f.n)
    # 6:D2 (p06025)
    check("C2", "the 4κ framed bases B_s = F^[s] B_0 are pairwise distinct", ok, f"p ∈ {SHELLS}")

    # C3 — unordered bases: the parity identification
    ok, det = True, []
    for p in SHELLS:
        f = frames[p]; k = f.kap
        ok &= all(eq(f._fam[(s + 2 * k) % f.n], mm(f._fam[s], f.J, p), p) for s in range(f.n))
        unordered = {frozenset(map(tuple, M.T)) for M in f._fam}
        ok &= (len(unordered) == 2 * k)
        det.append(f"p={p}: {f.n} framed, {len(unordered)} unordered")
    check("C3", "F^[s+2κ] = F^[s] J, so B_{s+2κ} = B_s as unordered bases: 4κ framed domains, exactly 2κ measurement bases", ok, "; ".join(det))

    # C4 — meridian-scale covariance
    ok, npairs = True, 0
    for p in SHELLS:
        f = frames[p]
        for m in range(f.n):
            Mm = f.meridian(m)
            for r in range(f.n):
                ok &= (tuple(f.S(r, x) for x in Mm) == f.meridian(m + r)); npairs += 1
    # 6:D4 (p06027)
    check("C4", "S_r(M_m) = M_{m+r} on every (m, r), as ordered lists", ok, f"{npairs} pairs over p ∈ {SHELLS}")

    # C5 — the effective step and the periodicity
    ok = True
    for p in SHELLS:
        f = frames[p]
        for m in range(f.n):
            Mm = f.meridian(m)
            ok &= all((Mm[a + 1] - Mm[a]) % p == f.gpow(m) for a in range(f.pi))
        ok &= all(f.S(r + p - 1, x) == f.S(r, x) for r in range(f.n) for x in range(p))
    check("C5", "consecutive entries of M_m differ by the effective step g^m; S_{r+(p−1)} = S_r", ok, f"p ∈ {SHELLS}")

    # C6 — the ladder at p = 13 and the no-wrap window
    f = frames[13]
    ladder = {0: (0, 1, 2, 3, 4, 5, 6), 1: (0, 2, 4, 6, 8, 10, 12), 2: (0, 4, 8, 12, 3, 7, 11), 3: (0, 8, 3, 11, 6, 1, 9)}
    ok = (f.g == 2 and f.i == 5 and f.pi == 6 and all(f.meridian(m) == ladder[m] for m in ladder))
    ok &= all(f.gpow(m) == 2 ** m for m in range(4))
    w = f.pi
    unwrapped = [m for m in range(f.n) if w * 2 ** m < 13]
    wraps = [m for m in range(4) if any(a * 2 ** m >= 13 for a in range(w + 1))]
    ok &= (unwrapped == [0, 1] and wraps == [2, 3])
    # 6:D5 (p06028)
    check("C6", "p = 13, g = 2: M_0…M_3 = the printed ladder at steps 1, 2, 4, 8; the no-wrap window w·g^r < p with w = π = 6 holds for r ≤ 1 and the listing wraps from M_2", ok, f"unwrapped meridians {unwrapped}, wrapping {wraps}")

# ------------------------------------------------------------------------------------------------------------
# Block D — the Weil dictionary and the operator-level comparison (EXACT, integer-pinned)
# =======================================================================================
# Paper statements decided (Section 8):
#
#   D1  lem:Rs-rotation       c_s² + d_s² = 1 and det R_s = 1 for every s: R_s ∈ SO(2, F_p)
#   D2  prop:rotation-isom    s ↦ R_s is a homomorphism Z_{4κ} → SO(2, F_p), injective, onto: |SO(2, F_p)| = p−1
#   D3  thm:Weil-equivalence  the cardinal matrices R_0 = I, R_κ = w = [[0,−1],[1,0]] (the R_κ column of
#       tab:checks            Table tab:checks), R_{2κ} = −I, R_{3κ} = w⁻¹; z_κ = i
#   D4  prop:nogo             σ (the exponent shift) has the n = 4κ distinct eigenvalues F_p^×, each simple;
#                             F^[1] has at most four; for κ ≥ 2 the cyclic groups ⟨σ⟩, ⟨F^[1]⟩ of order 4κ
#                             are not conjugate
#   D5  prop:charsector       E_1 = im Π_1 ≠ 0 for κ ≥ 2; F^[s]|_{E_1} = g^{−s}; F^[s] T_v = T_v S_{−s} on every
#                             x ∈ F_p and s; R_s (1, −i)ᵀ = g^{−s} (1, −i)ᵀ
#   D6  prop:heisenberg       F σ F⁻¹ = D_1, F D_1 F⁻¹ = σ⁻¹ with D_1 = diag(g^k); F^r σ = σ_r F^r,
#                             (σ_0, σ_1, σ_2, σ_3) = (σ, D_1, σ⁻¹, D_1⁻¹); the expansion eq:conj-expansion
#                             F^[s] = Σ_r c_r(s) F^r with c_r(s) = ¼ Σ_ℓ (g^{rκ−s})^ℓ
#   D7  prop:heisenberg       the sweep: F^[s] σ F^[s]⁻¹ monomial exactly at the four cardinal indices and
#                             non-monomial at every one of the 112 intermediate indices over
#                             p ∈ {13, 17, 29, 37, 41} (p = 5 has no intermediate index)
#   D8  thm:monomial          cardinal exclusivity: off j ∈ {−1, 0, 1} row 0 of F^[s] σ F^[s]⁻¹ is x⁻¹ times a
#                             quadratic in x = g^j with leading coefficient i(c₀+c₂)c₃(−s) ≠ 0, so at least 4κ−5
#                             nonzero entries for every non-cardinal s; every shell p ≡ 1 (mod 4) below 200
#
# Shells: p = 5, 13, 17, 29, 37, 41 (D8: every shell below 200).
def shift(n):
    """(σ v)_k = v_{k−1}: the exponent-shift permutation matrix."""
    S = np.zeros((n, n), dtype=np.int64)
    for k in range(n):
        S[k, (k - 1) % n] = 1
    return S

def block_D():
    """Block D — the Weil dictionary and the operator-level comparison (EXACT, integer-pinned): D1–D8."""
    print("block D — the Weil dictionary and the operator-level comparison")
    frames = {p: Frame(p) for p in SHELLS}

    # D1 — R_s ∈ SO(2, F_p)
    ok = True
    for p in SHELLS:
        f = frames[p]
        for s in range(f.n):
            R = f.R(s); c, d = int(R[0, 0]), int(R[1, 0])
            ok &= ((c * c + d * d) % p == 1 and (R[0, 0] * R[1, 1] - R[0, 1] * R[1, 0]) % p == 1)
            ok &= (R[0, 1] == (-d) % p and R[1, 1] == c)
    check("D1", "c_s² + d_s² = 1, det R_s = 1: R_s ∈ SO(2, F_p) for every s", ok, f"p ∈ {SHELLS}")

    # D2 — the isomorphism Z_{4κ} ≅ SO(2, F_p)
    ok, det = True, []
    for p in SHELLS:
        f = frames[p]
        Rs = [f.R(s) for s in range(f.n)]
        ok &= all(eq(mm(Rs[s], Rs[r], p), Rs[(s + r) % f.n], p) for s in range(f.n) for r in range(f.n))
        ok &= (len({R.tobytes() for R in Rs}) == f.n)
        so2 = sum(1 for c in range(p) for d in range(p) if (c * c + d * d) % p == 1)
        ok &= (so2 == p - 1)
        det.append(f"p={p}: |SO(2)|={so2}")
    # 6:E2 (p06031)
    check("D2", "R_{s+r} = R_s R_r, s ↦ R_s injective, |SO(2, F_p)| = p−1 = 4κ: an isomorphism", ok, "; ".join(det))

    # D3 — the cardinal matrices
    ok = True
    for p in SHELLS:
        f = frames[p]; k = f.kap
        w = np.array([[0, p - 1], [1, 0]], dtype=np.int64)
        ok &= (f.z(k) == f.i)
        ok &= eq(f.R(0), np.eye(2, dtype=np.int64), p) and eq(f.R(k), w, p)
        ok &= eq(f.R(2 * k), (-np.eye(2, dtype=np.int64)) % p, p) and eq(f.R(3 * k), matpow(w, 3, p), p)
        ok &= eq(mm(f.R(3 * k), w, p), np.eye(2, dtype=np.int64), p)
    # 6:E3 (p06032)
    check("D3", "R_0 = I, R_κ = [[0,−1],[1,0]] (Table tab:checks), R_{2κ} = −I, R_{3κ} = w⁻¹; z_κ = g^{−κ} = i", ok, f"p ∈ {SHELLS}")

    # D4 — the spectral obstruction
    ok, det = True, []
    for p in SHELLS:
        f = frames[p]; n = f.n
        sig = shift(n)
        ok &= eq(matpow(sig, n, p), f.I(), p) and all(not eq(matpow(sig, r, p), f.I(), p) for r in range(1, n))
        ok &= all(rank_mod_p((sig - a * f.I()) % p, p) == n - 1 for a in range(1, p))      # every a ∈ F_p^× a simple eigenvalue
        ok &= all(rank_mod_p((f.frft(1) - a * f.I()) % p, p) == n for a in range(1, p) if a not in {f.gpow(-l) for l in range(4)})
        neig = sum(1 for a in range(1, p) if rank_mod_p((f.frft(1) - a * f.I()) % p, p) < n)
        ok &= (neig <= 4) and (f.kap == 1 or neig < n)
        det.append(f"p={p}: σ has {n} simple eigenvalues, F^[1] has {neig}")
    # 6:E5 (p06034)
    check("D4", "σ has the 4κ simple eigenvalues F_p^×; F^[1] has at most four; for κ ≥ 2 ⟨σ⟩ and ⟨F^[1]⟩ are not conjugate", ok, "; ".join(det))

    # D5 — the common character sector
    ok, det = True, []
    for p in SHELLS:
        f = frames[p]; n = f.n
        P1 = f.Pi[1]; m1 = rank_mod_p(P1, p)
        ok &= (m1 >= 1) if f.kap >= 2 else True
        if m1 == 0:
            det.append(f"p={p}: E_1 = 0 (κ = 1)"); continue
        cols = [P1[:, j] for j in range(n) if np.any(P1[:, j])]
        for s in range(n):
            Fs = f.frft(s)
            for v in cols[:3]:
                ok &= eq(mm(Fs, v.reshape(n, 1), p), (f.gpow(-s) * v).reshape(n, 1), p)
                for x in range(p):
                    lhs = mm(Fs, (x * v % p).reshape(n, 1), p)                  # F^[s] T_v(x)
                    rhs = ((f.S(-s, x) * v) % p).reshape(n, 1)                  # T_v S_{−s}(x)
                    ok &= eq(lhs, rhs, p)
            vec = np.array([[1], [(-f.i) % p]], dtype=np.int64)
            ok &= eq(mm(f.R(s), vec, p), (f.gpow(-s) * vec) % p, p)
        det.append(f"p={p}: dim E_1 = {m1}")
    # 6:E6 (p06035)
    check("D5", "E_1 ≠ 0 for κ ≥ 2; F^[s] = g^{−s} on E_1; F^[s] T_v = T_v S_{−s} on every x and s; R_s (1,−i)ᵀ = g^{−s} (1,−i)ᵀ", ok, "; ".join(det))

    # D6 — cardinal Heisenberg covariance and the expansion
    ok = True
    for p in SHELLS:
        f = frames[p]; n = f.n
        sig = shift(n); D1 = np.diag([f.gpow(k) for k in range(n)]).astype(np.int64)
        Finv = matpow(f.F, 3, p)
        ok &= eq(mm(mm(f.F, sig, p), Finv, p), D1, p)
        ok &= eq(mm(mm(f.F, D1, p), Finv, p), matpow(sig, n - 1, p), p)
        sigs = [sig, D1, matpow(sig, n - 1, p), np.diag([f.gpow(-k) for k in range(n)]).astype(np.int64)]
        for r in range(4):
            ok &= eq(mm(f.Fpow(r), sig, p), mm(sigs[r], f.Fpow(r), p), p)
        for s in range(n):
            M = np.zeros((n, n), dtype=np.int64)
            for r in range(4):
                c = f.inv4 * sum(pow(f.gpow(r * f.kap - s), l, p) for l in range(4)) % p
                M = (M + c * f.Fpow(r)) % p
            ok &= eq(M, f.frft(s), p)
    # 6:E7 (p06036)
    check("D6", "F σ F⁻¹ = D_1, F D_1 F⁻¹ = σ⁻¹; F^r σ = σ_r F^r with (σ, D_1, σ⁻¹, D_1⁻¹); F^[s] = Σ_r c_r(s) F^r, c_r(s) = ¼ Σ_ℓ (g^{rκ−s})^ℓ", ok, f"p ∈ {SHELLS}")

    # D7 — the monomial sweep
    ok, n_int, n_card, det = True, 0, 0, []
    for p in SHELLS:
        f = frames[p]; n = f.n; k = f.kap
        sig = shift(n)
        mono = []
        for s in range(n):
            Fs = f.frft(s); Fsinv = f.frft(-s)
            mono.append(is_monomial(mm(mm(Fs, sig, p), Fsinv, p)))
        card = {0, k, 2 * k, 3 * k}
        ok &= all(mono[s] for s in card) and all(not mono[s] for s in range(n) if s not in card)
        if p != 5:
            n_int += n - 4
        n_card += 4
        det.append(f"p={p}: monomial at {sorted(s for s in range(n) if mono[s])}")
    ok &= (n_int == 112)
    check("D7", "F^[s] σ F^[s]⁻¹ is monomial exactly at the four cardinal indices and non-monomial at every one of the 112 intermediate indices of p ∈ {13,17,29,37,41}", ok, "; ".join(det) + f"; {n_int} intermediate indices swept")

    # D8 — cardinal exclusivity as a theorem (thm:monomial): off j ∈ {−1, 0, 1} row 0 of F^[s] σ F^[s]⁻¹ is
    # i[(c₀+c₂)(c'₃x + c'₁x⁻¹) + (c₁+c₃)(c'₀+c'₂)], x = g^j, c_r = c_r(s), c'_r = c_r(−s): x⁻¹ times a quadratic in x whose leading
    # coefficient i(c₀+c₂)c'₃ is nonzero for every non-cardinal s (c₀+c₂ = (1+g^{−2s})/2, every c_r(±s) ≠ 0), so the row has at
    # least 4κ−5 nonzero entries. Checked on every shell p ≡ 1 (mod 4) below 200 (the quadratic's coefficients, the entry formula
    # against the direct product, the count), five of the six shells of Table tab:checks among them (p = 5 has no such index).
    ok, n_int8, worst, det = True, 0, None, []
    for p in [q for q in range(13, 200) if q % 4 == 1 and all(q % d for d in range(2, int(q ** 0.5) + 1))]:
        f = frames.get(p) or Frame(p); n, k, inv2 = f.n, f.kap, pow(2, p - 2, p)
        sig = shift(n)
        c = lambda r, t: f.inv4 * sum(pow(f.gpow(r * k - t), l, p) for l in range(4)) % p
        for s in range(n):
            if s % k == 0:
                continue
            cs, cps = [c(r, s) for r in range(4)], [c(r, -s) for r in range(4)]
            c02 = (cs[0] + cs[2]) % p
            ok &= all(x != 0 for x in cs + cps) and c02 == inv2 * (1 + f.gpow(-2 * s)) % p and c02 != 0
            lead, cst = f.i * c02 * cps[3] % p, f.i * c02 * cps[1] % p
            ok &= lead != 0 and cst != 0
            row = (mm(f.frft(s)[:1], sig, p) @ f.frft(-s)) % p                 # row 0 of F^[s] σ F^[s]⁻¹, by the product
            D0 = [f.i * (c02 * (cps[3] * f.gpow(j) + cps[1] * f.gpow(-j)) + (cs[1] + cs[3]) * (cps[0] + cps[2])) % p for j in range(n)]
            ok &= all(row[0, j] == D0[j] for j in range(n) if j not in {n - 1, 0, 1})
            nz = int(np.count_nonzero(row)); roots = sum(1 for j in range(n) if D0[j] == 0)
            ok &= roots <= 2 and nz >= n - 5
            worst = nz if worst is None else min(worst, nz)
            n_int8 += 1
        det.append(f"p={p}")
    ok &= len(det) == 20 and n_int8 == 1920                                         # the twenty shells 13..197, Σ(p−5)
    # 6:E8 (p06050)
    check("D8", "cardinal exclusivity (thm:monomial): row 0 of F^[s] σ F^[s]⁻¹ is x⁻¹ times a quadratic in x = g^j off j ∈ {−1,0,1}, leading coefficient i(c₀+c₂)c₃(−s) ≠ 0, at least 4κ−5 nonzero entries for every non-cardinal s, every shell p ≡ 1 (mod 4) below 200", ok,
          f"{len(det)} shells, {n_int8} non-cardinal indices; fewest nonzero entries in row 0: {worst}")

# ------------------------------------------------------------------------------------------------------------
# Block E — the cyclotomic observer readout and the entropy on the meridian cycle
# ===============================================================================
# Paper statements decided (Section 9, Subsection sec:entropy). The readout of Definition def:readout
# realises the fractional family on C^n through the observer's continuum chart σ_C: X ↦ ζ_n, Y ↦ +√n —
# the canonical DFT projectors with the eigenvalue refinement g^{−ℓs} ↦ ζ_n^{−ℓs}. Floating point
# enters here and only here; the kinds are marked.
#
#   E1  def:readout          the readout algebra: Ĝ = Σ_k X^{k²} satisfies Ĝ² = 2n X^κ modulo Φ_n(X) —
#       (EXACT)              exact integer polynomial arithmetic; and both specialisations: σ_C gives
#                            (Σ ζ^{k²})² = 2n i, ρ gives G² = 2i in F_p (the reduction used in thm:multiplicity)
#   E2  prop:entropy         H(0) = H(2κ) = 0, H(κ) = H(3κ) = log n for every site-localised input δ_j
#   E3  prop:entropy         B_0 and B_κ mutually unbiased (every overlap 1/n); Maassen–Uffink
#                            H_{B_0} + H_{B_κ} ≥ log n on random states, saturated by the localised states;
#                            the comb (δ_0 + δ_6)/√2 at n = 12 gives log 2 + log 6 = log 12
#   E4  prop:closedform      the readout of F^[s] δ_0 is two-valued, p_0 = 1 − (n−1)t_s/n, p_j = t_s/n, with
#                            t_s = (2 − ζ^{2s} − ζ^{−2s})/4 = sin²(πs/2κ); H(s) the closed form; strictly
#                            increasing on 0 ≤ s ≤ κ; two oscillations per cycle
#   E5  §9 table, fig        p = 13: H(s)/log n = 0, .44, .91, 1, .91, .44, 0, .44, .91, 1, .91, .44;
#       entropy13            regenerates figures/entropy-cycle-f13.{pdf,png}
#   E6  rem:input-dep        δ_1 at p = 13: H(1)/log n = 0.55 against 0.44 for δ_0; δ_j meets Π_1, Π_3 exactly
#                            when j ∉ {0, 2κ}; δ_{2κ} gives the δ_0 curve
#   E7  def:readout          the Galois twist X ↦ ζ^u relabels the δ_0 curve by s ↦ us on every unit u and
#                            leaves the cardinal values of every δ_j invariant; u = −1 relabels every δ_j;
#                            for j ∉ {0, 2κ} a twist u ≢ ±1 changes the curve (n = 12, δ_1, u = 5: 0.55 ↦ 0.44)
#
# Shells: n = 4, 12, 16, 28, 36, 40 (p = 5, 13, 17, 29, 37, 41).
def cyclotomic(n):
    """Φ_n(X) as an integer coefficient array (low to high), by exact division of X^n − 1."""
    def polydiv_exact(a, b):                       # a / b, b monic, integer, exact
        a = list(a); q = [0] * (len(a) - len(b) + 1)
        for i in range(len(q) - 1, -1, -1):
            q[i] = a[i + len(b) - 1]
            for j in range(len(b)):
                a[i + j] -= q[i] * b[j]
        assert all(x == 0 for x in a[:len(b) - 1]), "inexact"
        return q
    poly = [-1] + [0] * (n - 1) + [1]               # X^n − 1
    for d in range(1, n):
        if n % d == 0:
            poly = polydiv_exact(poly, cyclotomic(d))
    return poly

def polymod_cyc(a, n):
    """Reduce a polynomial modulo X^n − 1 (exponents mod n)."""
    r = [0] * n
    for k, c in enumerate(a):
        r[k % n] += c
    return r

def polymul_cyc(a, b, n):
    r = [0] * n
    for i, x in enumerate(a):
        if x:
            for j, y in enumerate(b):
                if y:
                    r[(i + j) % n] += x * y
    return r

def polyrem(a, b):
    """Remainder of a modulo monic integer b (exact integer arithmetic)."""
    a = list(a)
    while len(a) >= len(b):
        c = a[-1]
        if c:
            for j in range(len(b)):
                a[len(a) - len(b) + j] -= c * b[j]
        a.pop()
    return a

def dft_family(n, u=1):
    """The readout family on C^n under the chart X ↦ ζ_n^u: the canonical DFT projectors and
    F^[s] = Σ_ℓ ζ^{−uℓs} Π_ℓ (Definition def:readout; entropy_meridian_cycle.py of the paper's code/)."""
    kap = n // 4
    z = np.exp(2j * np.pi * u / n)
    D = np.array([[z ** (j * k) for k in range(n)] for j in range(n)]) / np.sqrt(n)
    iota = z ** (-kap)
    Ds = [np.eye(n)]
    for _ in range(3):
        Ds.append(Ds[-1] @ D)
    P = [sum(iota ** (-l * r) * Ds[r] for r in range(4)) / 4 for l in range(4)]
    assert np.allclose(sum(P), np.eye(n)) and all(np.allclose(Pl @ Pl, Pl) for Pl in P)
    return D, P, (lambda s: sum(z ** (-l * s) * P[l] for l in range(4)))

def entropy(vec):
    q = np.abs(vec) ** 2; q = q / q.sum(); q = q[q > 1e-15]
    return float(-(q * np.log(q)).sum()) + 0.0          # (+0.0 clears a signed zero)

def delta(n, j):
    e = np.zeros(n); e[j] = 1.0
    return e

def block_E():
    """Block E — the cyclotomic observer readout and the entropy on the meridian cycle: E1–E7."""
    print("block E — the cyclotomic observer readout")
    os.makedirs(FIGDIR, exist_ok=True)
    frames = {p: Frame(p) for p in SHELLS}

    # E1 — the readout algebra identity, exact
    ok, det = True, []
    for p in SHELLS:
        f = frames[p]; n, k = f.n, f.kap
        G = [0] * n
        for kk in range(n):
            G[(kk * kk) % n] += 1                                      # Ĝ = Σ_k X^{k²} mod X^n − 1
        G2 = polymul_cyc(G, G, n)
        G2[k] -= 2 * n                                                 # Ĝ² − 2n X^κ
        rem = polyrem(G2, cyclotomic(n))
        ok &= all(c == 0 for c in rem)
        z = np.exp(2j * np.pi / n)
        ok &= abs(sum(z ** (kk * kk) for kk in range(n)) ** 2 - 2 * n * 1j) < 1e-9
        ok &= (f.gauss() ** 2 % p == 2 * f.i % p)
        det.append(f"n={n}: deg Φ_n = {len(cyclotomic(n)) - 1}")
    # 6:F2 (p06038)
    check("E1", "Ĝ² = 2n X^κ modulo Φ_n(X) (exact integer arithmetic); under σ_C: (Σ ζ^{k²})² = 2n i; under ρ: G² = 2i in F_p", ok, "; ".join(det))

    # E2 — cardinal values for every localised input
    ok = True
    for p in SHELLS:
        f = frames[p]; n, k = f.n, f.kap
        D, P, frft = dft_family(n)
        for j in range(n):
            e = delta(n, j)
            ok &= abs(entropy(frft(0) @ e)) < 1e-9 and abs(entropy(frft(2 * k) @ e)) < 1e-9
            ok &= abs(entropy(frft(k) @ e) - np.log(n)) < 1e-9 and abs(entropy(frft(3 * k) @ e) - np.log(n)) < 1e-9
        ok &= np.allclose(frft(0), np.eye(n)) and np.allclose(frft(k), D) and np.allclose(frft(2 * k), D @ D)
    # 6:F3 (p06039)
    check("E2", "H(0) = H(2κ) = 0, H(κ) = H(3κ) = log n for every δ_j", ok, f"n ∈ {[p - 1 for p in SHELLS]}", kind="[approx]")

    # E3 — mutually unbiased bases, Maassen–Uffink, the comb
    ok, rng = True, np.random.default_rng(6)
    for p in SHELLS:
        n = p - 1; k = n // 4
        D, P, frft = dft_family(n)
        Bk = frft(k)                                                    # the columns of B_κ = F^[κ] B_0
        ok &= np.allclose(np.abs(Bk) ** 2, 1.0 / n)                     # every overlap |<b_0,j|b_κ,l>|² = 1/n
        for _ in range(200):
            psi = rng.normal(size=n) + 1j * rng.normal(size=n); psi /= np.linalg.norm(psi)
            ok &= entropy(psi) + entropy(Bk.conj().T @ psi) >= np.log(n) - 1e-9
        e = delta(n, 0)
        ok &= abs(entropy(e) + entropy(Bk.conj().T @ e) - np.log(n)) < 1e-9
    D, P, frft = dft_family(12)
    comb = (delta(12, 0) + delta(12, 6)) / np.sqrt(2)
    h0, hk = entropy(comb), entropy(frft(3).conj().T @ comb)
    ok &= abs(h0 - np.log(2)) < 1e-9 and abs(hk - np.log(6)) < 1e-9 and abs(h0 + hk - np.log(12)) < 1e-9
    check("E3", "B_0, B_κ mutually unbiased (overlaps 1/n); H_{B_0} + H_{B_κ} ≥ log n on random states, saturated by δ_j; the comb (δ_0+δ_6)/√2 at n = 12: log 2 + log 6 = log 12",
          ok, f"comb: H_0 = {h0:.4f} = log 2, H_κ = {hk:.4f} = log 6; 200 random states per shell", kind="[approx]")

    # E4 — the closed form
    ok = True
    curves = {}
    for p in SHELLS:
        n = p - 1; k = n // 4
        D, P, frft = dft_family(n)
        z = np.exp(2j * np.pi / n)
        H = []
        for s in range(n):
            psi = frft(s) @ delta(n, 0); q = np.abs(psi) ** 2
            ts = ((2 - z ** (2 * s) - z ** (-2 * s)) / 4).real
            ok &= abs(ts - np.sin(np.pi * s / (2 * k)) ** 2) < 1e-12
            ok &= abs(q[0] - (1 - (n - 1) * ts / n)) < 1e-9 and np.allclose(q[1:], ts / n, atol=1e-9)
            H.append(entropy(psi))
            if 1e-15 < ts:
                p0 = 1 - (n - 1) * ts / n
                Hcf = -(p0 * np.log(p0) + (n - 1) * (ts / n) * np.log(ts / n))
            else:
                Hcf = 0.0
            ok &= abs(Hcf - H[-1]) < 1e-9
        H = np.array(H); curves[p] = H
        ok &= all(H[s + 1] > H[s] + 1e-9 for s in range(k))               # strictly increasing on [0, κ]
        ok &= np.allclose(H, H[(np.arange(n) + 2 * k) % n]) and np.allclose(H, H[(-np.arange(n)) % n])   # period 2κ, symmetric
        ok &= all(1e-9 < H[s] < np.log(n) - 1e-9 for s in range(n) if s % k)                             # strictly intermediate
    # 6:F4 (p06040)
    check("E4", "F^[s] δ_0 has the two-valued readout p_0 = 1 − (n−1)t_s/n, p_j = t_s/n, t_s = (2−ζ^{2s}−ζ^{−2s})/4 = sin²(πs/2κ); H(s) the closed form, strictly increasing on [0, κ], period 2κ, strictly intermediate off the cardinal indices",
          ok, f"n ∈ {[p - 1 for p in SHELLS]}", kind="[approx]")

    # E5 — the p = 13 table and the figure
    n = 12; H = curves[13]; Hn = H / np.log(n)
    table = [0, .44, .91, 1, .91, .44, 0, .44, .91, 1, .91, .44]
    ok = all(abs(round(float(Hn[s]), 2) - table[s]) < 1e-9 for s in range(n))
    try:
        import matplotlib
        matplotlib.use("Agg")
        import matplotlib.pyplot as plt
        plt.rcParams.update({"font.family": "serif", "font.size": 11, "mathtext.fontset": "cm", "axes.linewidth": 0.8})
        s = np.arange(n)
        fig, ax = plt.subplots(figsize=(6.2, 3.5))
        ax.axhline(1.0, ls="--", lw=0.8, color="0.5")
        ax.text(n - 0.1, 1.005, r"$\log n$", ha="right", va="bottom", color="0.4", fontsize=10)
        ax.plot(s, Hn, "-", color="0.25", lw=1.3, zorder=1)
        ax.plot(s, Hn, "o", color="0.25", ms=4, zorder=2)
        for kk, col in {0: "tab:blue", 3: "tab:red", 6: "tab:green", 9: "tab:orange"}.items():
            ax.plot(kk, Hn[kk], "o", color=col, ms=8, zorder=3)
        ax.annotate("$M_0$", (0, 0), textcoords="offset points", xytext=(2, 8), color="tab:blue")
        ax.annotate("$M_{2\\kappa}$ (parity)", (6, 0), textcoords="offset points", xytext=(-6, 8), ha="center", color="tab:green")
        ax.annotate("$M_\\kappa$ (Fourier)", (3, 1), textcoords="offset points", xytext=(0, -16), ha="center", color="tab:red")
        ax.annotate("$M_{3\\kappa}$", (9, 1), textcoords="offset points", xytext=(0, -16), ha="center", color="tab:orange")
        ax.set_xlabel(r"meridian index $s\in\mathbb{Z}_{4\kappa}$")
        ax.set_ylabel(r"normalised entropy $H(s)/\log n$")
        ax.set_xticks(range(n)); ax.set_ylim(-0.05, 1.12); ax.set_xlim(-0.4, n - 0.6)
        ax.spines[["top", "right"]].set_visible(False)
        fig.tight_layout()
        for ext in ("pdf", "png"):
            fig.savefig(os.path.join(FIGDIR, f"entropy-cycle-f13.{ext}"), bbox_inches="tight", dpi=150)
        plt.close(fig)
        figmsg = f"wrote {FIGDIR}/entropy-cycle-f13.pdf/.png"
    except ImportError:
        figmsg = "matplotlib absent: figure not written"
    # 6:F5 (p06041)
    check("E5", "p = 13: H(s)/log n = 0, .44, .91, 1, .91, .44, 0, .44, .91, 1, .91, .44 (fig:entropy13)", ok,
          "H/log n = " + ", ".join(f"{x:.4f}" for x in Hn) + "; " + figmsg, kind="[approx]")

    # E6 — input dependence
    D, P, frft = dft_family(12)
    H1 = np.array([entropy(frft(s) @ delta(12, 1)) for s in range(12)]) / np.log(12)
    H6 = np.array([entropy(frft(s) @ delta(12, 6)) for s in range(12)]) / np.log(12)
    ok = abs(round(float(H1[1]), 2) - 0.55) < 1e-9 and abs(round(float(Hn[1]), 2) - 0.44) < 1e-9
    ok &= np.allclose(H6, Hn) and not np.allclose(H1, Hn)
    for p in SHELLS:
        nn = p - 1; kk = nn // 4
        Dp, Pp, fr = dft_family(nn)
        for j in range(nn):
            odd = np.linalg.norm(Pp[1] @ delta(nn, j)) + np.linalg.norm(Pp[3] @ delta(nn, j))
            ok &= ((odd < 1e-12) == (j in (0, 2 * kk)))
    # 6:F6 (p06042)
    check("E6", "δ_1 at p = 13: H(1)/log n = 0.55 against 0.44 for δ_0; δ_j meets the odd projectors exactly when j ∉ {0, 2κ}; δ_{2κ} reproduces the δ_0 curve",
          ok, f"δ_1: H(1)/log n = {H1[1]:.4f}; δ_0: {Hn[1]:.4f}", kind="[approx]")

    # E7 — the Galois twist
    ok, n_units = True, 0
    for p in SHELLS:
        nn = p - 1; kk = nn // 4
        base = curves[p]
        D1_, P1_, fr1 = dft_family(nn)
        for u in range(1, nn):
            if np.gcd(u, nn) != 1:
                continue
            Du, Pu, fru = dft_family(nn, u); n_units += 1
            Hu = np.array([entropy(fru(s) @ delta(nn, 0)) for s in range(nn)])
            ok &= np.allclose(Hu, base[(u * np.arange(nn)) % nn], atol=1e-9)             # s ↦ us on the δ_0 curve
            for j in range(nn):
                e = delta(nn, j)
                ok &= abs(entropy(fru(0) @ e)) < 1e-9 and abs(entropy(fru(2 * kk) @ e)) < 1e-9
                ok &= abs(entropy(fru(kk) @ e) - np.log(nn)) < 1e-9 and abs(entropy(fru(3 * kk) @ e) - np.log(nn)) < 1e-9
                if u == nn - 1:                                                           # the conjugate twist relabels every input
                    Hj = np.array([entropy(fr1(s) @ e) for s in range(nn)])
                    ok &= np.allclose([entropy(fru(s) @ e) for s in range(nn)], Hj[(-np.arange(nn)) % nn], atol=1e-9)
    D5, P5, fr5 = dft_family(12, 5)
    h5 = entropy(fr5(1) @ delta(12, 1)) / np.log(12)
    ok &= abs(round(h5, 2) - 0.44) < 1e-9 and abs(round(float(H1[1]), 2) - 0.55) < 1e-9     # δ_1, u = 5: 0.55 ↦ 0.44
    # 6:F7 (p06043)
    check("E7", "X ↦ ζ^u relabels the δ_0 curve by s ↦ us on every unit u; the cardinal values of every δ_j are invariant under every twist; u = −1 relabels every δ_j; δ_1 at n = 12 under u = 5: H(1)/log n 0.55 ↦ 0.44",
          ok, f"{n_units} twists over the six shells; δ_1, u = 5: {h5:.4f}", kind="[approx]")


if __name__ == "__main__":
    import time
    want = [a.upper() for a in sys.argv[1:]] or sorted(BLOCK)
    bad = [b for b in want if b not in BLOCK]
    if bad: sys.exit(f"no block {', '.join(bad)}: the blocks are {', '.join(sorted(BLOCK))}")
    t0 = time.time()
    for b in want:
        t = time.time(); _run_block(b); print(f"    [block {b}: {time.time() - t:.1f} s]")
    ok = summary(write=(want == sorted(BLOCK)))
    kinds = {}
    for r in RESULTS: kinds[r["kind"]] = kinds.get(r["kind"], 0) + 1
    print("by kind: " + ", ".join(f"{k} {v}" for k, v in sorted(kinds.items())) + f"; {len(RESULTS)} checks in {time.time() - t0:.1f} s" + ("; results.json written" if want == sorted(BLOCK) else ""))
    sys.exit(0 if ok else 1)
