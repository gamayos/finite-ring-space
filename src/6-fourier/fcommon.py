"""
fcommon.py — shared primitives for the 6-fourier validation package
===================================================================
"Scale-Shift and Fractional Fourier Transform as Rotations over Finite Holographic Substrate"
(Akhtman, 2026), validation package of the FRC corpus (finite-ring-space/src/6-fourier).

The paper carries no predicate ledger of its own; its machine-verified claims are the labelled
statements of Sections 3–9 (Table `tab:checks`, the theorems, lemmas, propositions, remarks and the
one conjecture). Each check names the paper `\\label`(s) it decides (LEDGER below) and, where a row of
the corpus master ledger (00-ledger, rows cited as 00:XN) is witnessed, that row.

Everything the block scripts share:
  * the frame datum of a shell: p = 4κ+1, the smallest primitive root g (the generators of
    Table `tab:checks`), the oriented quarter-turn i = −g^κ, π = 2κ, e = g^i;
  * exact matrix arithmetic over F_p (numpy int64, reduced mod p after every product);
  * the shell Fourier matrix W_{kj} = g^{jk}, the reversal J, the normalised operator F = iW,
    the four projectors Π_ℓ, the fractional family F^[s] = Σ_ℓ g^{−ℓs} Π_ℓ, rank mod p;
  * the PASS/FAIL registry every block reports into (results.json).

Kinds: EXACT checks are integer-pinned computations in F_p (a pass is a proof on the tested
instances); [approx] checks compare a floating-point observation with the value the paper states, to
a stated tolerance (block E, the cyclotomic observer readout on C^n).
"""
import os, json, sys
import numpy as np

FIGDIR = os.environ.get("FOURIER_FIGDIR", "figures")
os.makedirs(FIGDIR, exist_ok=True)

# The shells of Table tab:checks (p, κ, g, i); the package recomputes g and i and checks the table.
TABLE = [(5, 1, 2, 3), (13, 3, 2, 5), (17, 4, 3, 4), (29, 7, 2, 17), (37, 9, 2, 6), (41, 10, 6, 9)]
SHELLS = [p for p, _, _, _ in TABLE]

# ----------------------------------------------------------------------------- registry
RESULTS = []

# Package check id -> the paper statement(s) decided (by \label) and the master-ledger row witnessed.
LEDGER = {
    # block A — the frame datum and the shell Fourier operator
    "A1": "§3 shell data (eq:it-def, rem:capacity), tab:checks",
    "A2": "§3 Euler identity on the odd member; 00:C14",
    "A3": "rem:gt-covariance",
    "A4": "lem:W-square, prop:F-cycle, tab:checks; 00:C2",
    "A5": "rem:unitary-norm",
    "A6": "lem:JF-decomp",
    # block B — the fractional family
    "B1": "lem:projectors",
    "B2": "thm:FRC-FrFT (eq:additivity); 00:C2",
    "B3": "thm:FRC-FrFT (eq:cardinal-FrFT); 00:C2",
    "B4": "thm:faithful",
    "B5": "lem:multiplicity",
    "B6": "rem:multiplicities",
    "B7": "thm:multiplicity",
    "B8": "thm:multiplicity (proof: G G* = −2, G² = 2i, the traces)",
    "B9": "rem:classification",
    "B10": "rem:gt-covariance (registered objects invariant under the conjugate reframing); 00:C7",
    # block C — domains and the coordinate-side zoom
    "C1": "def:domain",
    "C2": "cor:distinct-domains",
    "C3": "rem:ordered-bases",
    "C4": "prop:meridian-scale; 00:C2",
    "C5": "cor:effective-step, rem:framed-rational (S_{r+(p−1)} = S_r)",
    "C6": "ex:zoom-13, thm:zoom (the no-wrap window)",
    # block D — the Weil dictionary and the operator-level comparison
    "D1": "lem:Rs-rotation",
    "D2": "prop:rotation-isom",
    "D3": "thm:Weil-equivalence (the cardinal matrices), tab:checks",
    "D4": "prop:nogo",
    "D5": "prop:charsector",
    "D6": "prop:heisenberg",
    "D7": "conj:monomial (the 112-index sweep)",
    # block E — the cyclotomic observer readout
    "E1": "def:readout (the reduction ρ, Ĝ² = 2nX^κ)",
    "E2": "prop:entropy (cardinal values)",
    "E3": "prop:entropy (mutually unbiased bases, Maassen–Uffink, the comb)",
    "E4": "prop:closedform",
    "E5": "§9 table H(s)/log n, fig:entropy13",
    "E6": "rem:input-dep",
    "E7": "def:readout (the Galois twist relabels the intermediate curve)",
}

def check(pid, label, ok, detail="", kind="EXACT"):
    """Record one predicate check. pid = package check id; LEDGER[pid] = the paper statement(s) decided."""
    ok = bool(ok)
    rows = LEDGER.get(pid, "")
    script = sys._getframe(1).f_globals.get("__name__", "")
    if script == "__main__":
        script = os.path.splitext(os.path.basename(sys.argv[0]))[0]
    RESULTS.append({"id": pid, "rows": rows, "script": script, "label": label, "ok": ok, "detail": detail, "kind": kind})
    print(f"  [{'PASS' if ok else 'FAIL'}] {pid:4s} {kind:7s} [{rows}] {label}" + (f"  --  {detail}" if detail else ""))
    return ok

def summary(write=True):
    n_ok = sum(r["ok"] for r in RESULTS)
    print(f"\nSUMMARY: {n_ok}/{len(RESULTS)} checks passed" + ("" if n_ok == len(RESULTS) else "  <-- FAILURES"))
    if write:
        with open("results.json", "w") as f:
            json.dump(RESULTS, f, indent=1)
    return n_ok == len(RESULTS)

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
