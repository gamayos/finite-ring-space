"""
rh.py — the validation package of "Riemann Hypothesis over Finite Holographic Substrate" (Akhtman & Voether, 2026; Preprints
doi 10.20944/preprints202606.0768.v1, whose first version is "Riemann Hypothesis over the Holographic Substrate: a Finite-Field
Dictionary and the Screen Reading"), the paper 20-rh of the FRC corpus
(finite-ring-space/src/20-rh); one script since 24 September 2026 (the registry rhcommon.py and the seven block scripts
a_shell, b_deframe, c_primeside, c_gue, c_chi, d_classification, e_resonance merged, the three prime-side scripts as one block C).
========================================================================================================================

One script, six blocks, 110 checks — 66 EXACT (integer-pinned), 41 [approx] (a floating-point observation against the value
the paper states, to a stated tolerance), 3 [chart] (a continuum reading of a finite object; notation.tex convention 6) —
Python with numpy, scipy, mpmath, sympy and matplotlib (the blocks redraw their diagnostic figures into figures/ and the paper's
three numerical figures, at the page width, into figures/paper/). Each
check names the predicate(s) of the paper's ledger it witnesses (LEDGER; predicates cited as 20:XN), and the deciding check's
`# 20:XN (<key>)` marker is what the ledger's source column links (PREDICATES; finitering.space/src/20-rh/#<key>). Since the
cut of 15 October 2026 (T05 of reports/blueprint-20261013.md) the checks of the retired rows (the staircase, the horizon-scale
resolution, the semiclassical cutoff, the prime-side spectrum, the GUE statistic, the χ-twist, ...) still run as illustrations,
marked "illustration: 20:XN retired 2026-10-15", and witness no row; since T11 of the same day (every theorem row with a python
and a Lean witness) so do the checks of the resonance, the bare main sum, the raw secular condition, the Davenport–Heilbronn
comb and the pole-corrected count (20:C2, D4, E6, F3–F5, F8). Master-ledger predicates reached through the paper
predicates: 00:D11 (the shell theorem, 20:E12) and 00:D12 (the cells and the hosted theorem, 20:D5, 20:F2).

Block A  the shell theorem and the exact shell arithmetic, the closure's instances, completeness (EXACT; 20:A2, A3, A4, B1–B10, E1, E12, E13, F7)
Block B  the de-framing dictionary ([chart], [approx]; illustrations since the cut: the density, the residue, the bare main sum)
Block C  the spectrum from the prime side, ζ never evaluated ([approx]; illustrations since the cut: the secular condition, the GUE statistic, the χ-twist)
Block D  Turing's count on the shell, the phantom, the Davenport–Heilbronn controls, the smoothed explicit formula, the strip,
         the finite control, the cells by the argument principle ([approx], EXACT; 20:D5, D8, D9, F1; the Davenport–Heilbronn
         comb and the pole-corrected count illustrations since the cut)
Block E  resonance (EXACT; illustrations since the cut: the resonance, the antipode, the horizon-scale resolution, the flatness)
Block T  Turing's certificate over the laboratory Carriers' cycles: Ω = 233, 30089, 2408561, every cell clean ([approx] in
         double precision with explicit bounds; 20:F2; the largest read from its embedded record, RH_CERT_FULL=1 recomputes it)

Everything the blocks share (the former rhcommon.py):
  * the von Mangoldt comb Λ(n) (sieved) and its raised-cosine taper in log n;
  * the archimedean scale-phase θ(T) from log Γ (never from ζ);
  * the raw comb count  Ñ_N(T) = θ(T)/π + 1 + S_comb(T)  (Proposition turing; Obs. trace) and the pole-corrected
    count  N̂_N(T) = Ñ_N(T) − (1/π) Im[Π_N(½+iT) + log((s−1)/s)]  (Proposition combformula), Π_N the explicit
    pole term of the smoothed explicit formula — the raw count carries it and has no limit in N, the corrected
    count settles;
  * the secular roots (half-integer crossings of N̂_N, or of Ñ_N for the raw reading), the colleague matrix
    and the comb-built Jacobi matrix (Obs. matrix, Def. jacobi);
  * the first Riemann heights, used only as validation markers — never as inputs;
  * the PASS/FAIL registry that every block reports into (results.json).

    python3 rh.py                every block in order, results.json written; exit 1 if a check fails (≈ 8 min: the 10⁸ comb of
                                 block C and the 8×10⁷ comb of block D are the slow parts; RH_FAST=1 runs reduced depths in ≈ 3 min,
                                 and the records then differ from the paper's)
    python3 rh.py A E            the blocks named (A, B, C, D, E, T); no results.json
    from frc_20_rh import predicate; predicate("20:F1")    one predicate: the blocks of the checks citing it run once per session
"""
import os, json, sys, math, cmath, time
from math import gcd
from fractions import Fraction
import numpy as np
import sympy as sp
import mpmath as mp
from scipy.special import loggamma, lambertw
from scipy.optimize import brentq
import matplotlib
matplotlib.use("Agg")
import matplotlib.pyplot as plt

SCRIPT = os.path.splitext(os.path.basename(__file__))[0]        # "rh": the one script, the name results.json and the site pages carry
FAST = os.environ.get("RH_FAST", "0") == "1"      # reduced depths for a quick run (the records then differ from the paper's)
FIGDIR = os.environ.get("RH_FIGDIR", "figures")
os.makedirs(FIGDIR, exist_ok=True)
os.makedirs(f"{FIGDIR}/paper", exist_ok=True)

# ----------------------------------------------------------------------------- the paper's figures
# The blocks draw their diagnostic figures (titles carrying the check ids) and, from the same arrays, the paper's figures:
# drawn at the text width of the manuscript (452.97 pt = 6.29 in, a4 with 1 in margins, 11 pt), so that \includegraphics scales
# nothing and the 8–9 pt type prints as drawn; no titles (the captions carry them), panel letters above the axes (16 October 2026).
TEXTWIDTH_IN = 452.97 / 72.27
PAPER_RC = {"font.size": 8.5, "axes.labelsize": 9, "axes.titlesize": 9, "xtick.labelsize": 8, "ytick.labelsize": 8,
            "legend.fontsize": 7.8, "legend.frameon": True, "legend.framealpha": 0.92, "legend.edgecolor": "0.8",
            "axes.linewidth": 0.7, "xtick.major.width": 0.6, "ytick.major.width": 0.6, "lines.linewidth": 1.1,
            "axes.grid": False, "pdf.fonttype": 42, "mathtext.fontset": "cm", "font.family": "DejaVu Sans"}
INK, RED, BLUE, ORANGE, NAVY, CRIMSON, GRAY = "#1a1a1a", "#c0392b", "#1f5fbf", "#e67e22", "#10325f", "#c8102e", "0.40"

def panel_letter(ax, s):
    """The panel letter above the axes' top-left corner, as the captions cite it."""
    ax.text(-0.02, 1.03, s, transform=ax.transAxes, ha="right", va="bottom", fontsize=9)

def paper_figure(name, draw, height):
    """Draw one paper figure under PAPER_RC at the text width into FIGDIR/paper/<name>.pdf (and .png), restoring the rc."""
    with plt.rc_context(PAPER_RC):
        fig, ax = plt.subplots(1, 2, figsize=(TEXTWIDTH_IN, height), gridspec_kw={"width_ratios": [1.55, 1.0]} if name != "fig_dh" else None)
        draw(fig, ax)
        fig.tight_layout(w_pad=1.2)
        fig.savefig(f"{FIGDIR}/paper/{name}.pdf", bbox_inches="tight", pad_inches=0.02)
        fig.savefig(f"{FIGDIR}/paper/{name}.png", dpi=220, bbox_inches="tight", pad_inches=0.02)
        plt.close(fig)
    print(f"    wrote {FIGDIR}/paper/{name}.pdf")

# ----------------------------------------------------------------------------- registry
RESULTS = []

# The paper's predicate ledger (20-rh Appendix A, predicates cited as 20:XN): the predicate(s) each
# check witnesses. The ledger's source column cites these check ids in return.
LEDGER = {
    "A1": "20:B4", "A2": "20:B5", "A3": "20:B6", "A4": "20:B8", "A5": "20:B9", "A6": "20:B10", "A6b": "20:B10", "A7": "20:E1, 20:E12, 20:E13",
    "A7b": "20:E1, 20:E12, 20:E13", "A8": "", "A9": "20:B7", "A10": "20:B1", "A11": "20:B2", "A12": "20:A2, 20:A4, 20:F7", "A13": "20:A3",
    "B1": "", "B2": "", "B3": "20:B8", "B4": "",
    "C1": "", "C2": "", "C2b": "", "C2c": "", "C3": "", "C4": "", "C5": "", "C6": "", "C6b": "",
    "C7a": "", "C7b": "", "C7c": "",
    "D1": "20:F1", "D2a": "", "D2b": "", "D2c": "", "D2d": "", "D2e": "",
    "D2f": "", "D2g": "", "D3": "", "D4": "20:F1",
    "D6a": "20:D8", "D6b": "20:D8", "D6c": "20:D9", "D7a": "20:D5", "D7b": "20:D5",
    "E1a": "", "E1b": "", "E1c": "", "E2a": "", "E2b": "", "E3": "", "E4": "",
    "T1": "20:F2", "T2": "20:F2", "T3": "20:F2",
}

BLOCK = {"A": "the shell theorem and the exact shell arithmetic (a_shell.py until 24 September 2026)",      # check-id prefix -> the block (the function block_<letter> below)
         "B": "the de-framing dictionary: zero density, the reconstruction residue, the horizon-length main sum (b_deframe.py)",
         "C": "the spectrum from the prime side with ζ never evaluated, the GUE statistics of the target spectrum, the χ-twisted comb (c_primeside.py, c_gue.py, c_chi.py)",
         "D": "Turing's count on the shell, the phantom, the Davenport–Heilbronn controls, the smoothed explicit formula (d_classification.py)",
         "E": "resonance, antipode, horizon-scale resolution, square-root cancellation (e_resonance.py)",
         "T": "Turing's certificate over the laboratory Carriers' cycles: every cell clean (Thm. hosted; 15 October 2026)"}

# the deciding check of each python-witnessed predicate: the first check the ledger's source column names (the other checks that
# cite it are corroboration, listed by predicate() from the records)
PREDICATES = {
    "20:B1": "A10", "20:B2": "A11", "20:B4": "A1", "20:B5": "A2", "20:B6": "A3", "20:B7": "A9", "20:B8": "A4", "20:B9": "A5",
    "20:B10": "A6", "20:A2": "A12", "20:A3": "A13", "20:A4": "A12", "20:F7": "A12",
    "20:E1": "A7", "20:E12": "A7", "20:E13": "A7b", "20:F1": "D1", "20:D8": "D6a", "20:D9": "D6c", "20:D5": "D7a", "20:F2": "T1",
}
_RAN = set()                                            # blocks already run in this session (predicate() runs each once)

def check(pid, label, ok, detail="", kind="EXACT"):
    """Record one predicate check. pid = package check id (A1, C3, ...); LEDGER[pid] = the paper's ledger predicate(s)."""
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
    import re
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
    """Verify one ledger predicate: run the blocks of the checks that cite it (each once per session), print the deciding check's
    source (from its marker) and every record that cites the predicate, and return True iff all pass."""
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

# ----------------------------------------------------------------------------- the shared primitives (rhcommon.py until 24 September 2026)
# ----------------------------------------------------------------------------- primes / comb
def sieve_primes(N):
    s = np.ones(N + 1, dtype=bool); s[:2] = False
    for i in range(2, int(N ** 0.5) + 1):
        if s[i]:
            s[i * i::i] = False
    return np.nonzero(s)[0]

def von_mangoldt_support(N):
    """Prime powers n = p^k <= N with Λ(n) = log p. Returns (n, Λ(n)) as float arrays, sorted."""
    primes = sieve_primes(N)
    ns, lam = [primes.astype(np.float64)], [np.log(primes)]
    k = 2
    while True:
        pk = primes[primes <= N ** (1.0 / k)].astype(np.float64) ** k
        if len(pk) == 0:
            break
        ns.append(pk); lam.append(np.log(pk ** (1.0 / k))); k += 1
    n_all = np.concatenate(ns); lam_all = np.concatenate(lam)
    order = np.argsort(n_all)
    return n_all[order], lam_all[order]

class Comb:
    """The tapered von Mangoldt comb to depth N.

    S_comb(T) = -(1/π) Σ_{n<=N} Λ(n)/(√n log n) · w(n) · sin(T log n),
    w(n) = ½(1 + cos(π log n / log N))   — the raised-cosine (Cesàro) taper of Obs. primespec.
    """
    def __init__(self, N, lam_fn=None):
        self.N = int(N)
        if lam_fn is None:
            n, lam = von_mangoldt_support(self.N)
        else:                                   # a generalized comb (Davenport–Heilbronn)
            n, lam = lam_fn(self.N)
        self.n, self.lam = n, lam
        self.logn = np.log(n)
        self.w = 0.5 * (1.0 + np.cos(np.pi * self.logn / math.log(self.N)))
        self.amp = self.lam / (np.sqrt(n) * self.logn) * self.w

    NBLK = 1 << 18      # comb terms per block (memory: NBLK × 64 doubles ≈ 128 MB at most)

    def S(self, T):
        """S_comb at scalar or array T, chunked over T and over the comb (a scalar in gives a float out)."""
        T = np.atleast_1d(np.asarray(T, dtype=float))
        out = np.zeros(len(T))
        for s in range(0, len(T), 64):
            blk = T[s:s + 64]
            for a in range(0, len(self.logn), self.NBLK):
                out[s:s + 64] -= (self.amp[a:a + self.NBLK, None] * np.sin(np.outer(self.logn[a:a + self.NBLK], blk))).sum(0)
        out /= math.pi
        return out if out.size > 1 else float(out[0])

    def sigma(self, gamma):
        """|Σ_N(γ)| = |Σ Λ(n) n^{-1/2-iγ} w(n)|, the scale-spectrum of Obs. primespec (scalar in, float out)."""
        gamma = np.atleast_1d(np.asarray(gamma, float))
        coef = self.lam * self.w / np.sqrt(self.n)
        out = np.empty(len(gamma))
        for s in range(0, len(gamma), 64):
            blk = gamma[s:s + 64]
            acc = np.zeros(len(blk), dtype=complex)
            for a in range(0, len(self.logn), self.NBLK):
                acc += (coef[a:a + self.NBLK, None] * np.exp(-1j * np.outer(self.logn[a:a + self.NBLK], blk))).sum(0)
            out[s:s + 64] = np.abs(acc)
        return out if out.size > 1 else float(out[0])

def theta(T):
    """Riemann–Siegel θ(T) = Im log Γ(¼ + iT/2) − (T/2) log π  — the archimedean phase, from Γ only."""
    T = np.asarray(T, dtype=float)
    return np.imag(loggamma(0.25 + 0.5j * T)) - 0.5 * T * math.log(math.pi)

def count_raw(comb, T, const=1.0, theta_fn=theta):
    """Ñ_N(T) = θ(T)/π + const + S_comb(T): the raw comb count (Proposition turing; uncertified)."""
    T = np.atleast_1d(np.asarray(T, float))
    val = theta_fn(T) / math.pi + const + comb.S(T)
    return val if val.size > 1 else float(val[0])

# ----------------------------------------------------------------------------- the pole term (Prop. combformula)
def pole_term(N, T):
    """Π_N(½ + iT) = ∫_0^L W(u/L) (e^{(½−iT)u} − e^{−(½+iT)u}) du/u,  L = log N  — the pole term of the smoothed
    explicit formula for the tapered log-ζ series, Σ_{n≤N} Λ(n) W(log n/L) n^{−s}/log n = Π_N(s) + J_N(s) (Prop.
    combformula (i), under the hypothesis of no zero to the right of the line), with J_N(s) → log((s−1)ζ(s)/s) for
    s not a zero (Prop. combformula (iv)). Written as ∫_0^L g(u) e^{−iTu} du, g(u) = W(u/L)·2 sinh(u/2)/u, and integrated with
    QUADPACK's oscillatory weights. Returns the complex value. Its size is (π²/2) √N/(|½−iT| L)³ (1 + O(1/L)):
    the raw count carries it and has no limit as N → ∞."""
    from scipy.integrate import quad
    L = math.log(N)
    g = lambda u: (0.5 * (1.0 + math.cos(math.pi * u / L))) * (2.0 * math.sinh(0.5 * u) / u if u > 1e-12 else 1.0)
    re = quad(g, 0.0, L, weight="cos", wvar=T, limit=1000)[0]
    im = -quad(g, 0.0, L, weight="sin", wvar=T, limit=1000)[0]
    return complex(re, im)

def pole_count_term(N, T):
    """(1/π) Im[Π_N(½+iT) + log((s−1)/s)] — the term the raw count carries beyond the exact count (Prop. combformula);
    Im log((s−1)/s) = π − 2 arctan(2T)."""
    return pole_term(N, T).imag / math.pi + 1.0 - (2.0 / math.pi) * math.atan(2.0 * T)

_POLE_CACHE = {}
def count_corrected(comb, T):
    """N̂_N(T) = Ñ_N(T) − (1/π) Im[Π_N + log((s−1)/s)]: the pole-corrected comb count (Prop. combformula; Obs. trace).
    For ζ only (const = 1, the archimedean phase θ); a Dirichlet L-function has no pole and no correction."""
    T = np.atleast_1d(np.asarray(T, float))
    corr = np.array([_POLE_CACHE.setdefault((comb.N, float(t)), pole_count_term(comb.N, float(t))) for t in T])
    val = count_raw(comb, T) - corr
    return val if val.size > 1 else float(val[0])

def secular_roots(comb, windows, const=1.0, theta_fn=theta, corrected=False):
    """The secular roots: solutions of N̂_N(T) = n − ½ (corrected=True) or Ñ_N(T) = n − ½ (raw) in each (n, lo, hi)
    window (Obs. trace)."""
    roots = []
    for n, lo, hi in windows:
        if corrected:
            f = lambda T: count_corrected(comb, T) - (n - 0.5)
        else:
            f = lambda T: count_raw(comb, T, const, theta_fn) - (n - 0.5)
        roots.append(brentq(f, lo, hi, xtol=1e-12))
    return np.array(roots)

def crossings(count_fn, lo, hi, step=0.1):
    """Brackets of every half-integer crossing of a count on [lo, hi], from the count alone: (level, a, b, direction).
    No reference height enters; the heights are compared only afterwards."""
    ts = np.arange(lo, hi + 1e-9, step); v = np.asarray(count_fn(ts), float)
    out = []
    for i in range(len(ts) - 1):
        for h in np.arange(math.floor(min(v[i], v[i + 1])) + 0.5, max(v[i], v[i + 1]), 1.0):
            if (v[i] - h) * (v[i + 1] - h) < 0:
                out.append((float(h), float(ts[i]), float(ts[i + 1]), int(np.sign(v[i + 1] - v[i]))))
    return out

def secular_roots_scan(comb, lo, hi, const=1.0, theta_fn=theta, corrected=False, step=0.1):
    """The secular roots on [lo, hi] with brackets from the count itself (Obs. trace): every upward half-integer
    crossing refined by Brent's method. Returns (roots, levels, extra) — extra lists any downward or repeated crossing."""
    f = (lambda T: count_corrected(comb, T)) if corrected else (lambda T: count_raw(comb, T, const, theta_fn))
    cr = crossings(f, lo, hi, step)
    up = [(h, a, b) for h, a, b, d in cr if d > 0]
    levels = [h for h, _, _ in up]
    extra = [(h, a) for h, a, b, d in cr if d < 0] + [(h, a) for h, a, b in up if levels.count(h) > 1]
    roots = np.array([brentq(lambda T: float(np.atleast_1d(f(T))[0]) - h, a, b, xtol=1e-12) for h, a, b in up])
    return roots, levels, extra

# ----------------------------------------------------------------------------- matrices
def colleague_roots(comb, TA, TB, deg, corrected=False):
    """Eigenvalues of the colleague matrix of the Chebyshev fit of the secular determinant Ξ(T) = cos(π N̂_N(T))
    (corrected=True; Obs. matrix) or cos(π Ñ_N(T)) (raw) on [TA, TB]. Returns the real roots inside the window."""
    from numpy.polynomial import chebyshev as Ch
    xs = np.cos(np.pi * (np.arange(deg + 1) + 0.5) / (deg + 1))
    T = 0.5 * (TB + TA) + 0.5 * (TB - TA) * xs
    cnt = count_corrected(comb, T) if corrected else count_raw(comb, T)
    c = Ch.chebfit(xs, np.cos(math.pi * cnt), deg)
    n = len(c) - 1
    a = c[:-1] / c[-1]
    M = np.zeros((n, n)); M[0, 1] = 1.0
    for k in range(1, n - 1):
        M[k, k - 1] = 0.5; M[k, k + 1] = 0.5
    M[n - 1, n - 2] = 0.5
    M[-1, :] -= 0.5 * a
    ev = np.linalg.eigvals(M)
    ev = ev[np.abs(ev.imag) < 1e-5].real
    ev = ev[(ev > -1) & (ev < 1)]
    return np.sort(0.5 * (TB + TA) + 0.5 * (TB - TA) * ev)

def jacobi_from_points(x):
    """Real-symmetric tridiagonal Jacobi matrix of the unit-weight measure Σ δ_{x_i} (Stieltjes–Lanczos,
    full reorthogonalisation). Its eigenvalues are exactly the x_i (Def. jacobi)."""
    x = np.asarray(x, float); K = len(x)
    A = np.diag(x); V = np.zeros((K, K))
    v = np.ones(K) / math.sqrt(K); V[:, 0] = v
    alpha = np.zeros(K); beta = np.zeros(max(K - 1, 0))
    r = A @ v; alpha[0] = v @ r; r = r - alpha[0] * v
    for j in range(1, K):
        beta[j - 1] = np.linalg.norm(r)
        vj = r / beta[j - 1]
        for k in range(j):
            vj -= (V[:, k] @ vj) * V[:, k]
        vj /= np.linalg.norm(vj); V[:, j] = vj
        r = A @ vj; alpha[j] = vj @ r
        r = r - alpha[j] * vj - beta[j - 1] * V[:, j - 1]
    return np.diag(alpha) + np.diag(beta, 1) + np.diag(beta, -1)

# ----------------------------------------------------------------------------- validation markers
# The first thirty nontrivial zero heights of ζ (Odlyzko's tables). Validation markers only:
# no construction in this package takes them as input.
HEIGHTS = np.array([
    14.134725141734693, 21.022039638771555, 25.010857580145688, 30.424876125859513, 32.935061587739189,
    37.586178158825671, 40.918719012147495, 43.327073280914999, 48.005150881167159, 49.773832477672302,
    52.970321477714460, 56.446247697063394, 59.347044002602353, 60.831778524609809, 65.112544048081606,
    67.079810529494173, 69.546401711173979, 72.067157674481907, 75.704690699083933, 77.144840068874805,
    79.337375020249367, 82.910380854086030, 84.735492980517050, 87.425274613125229, 88.809111207634465,
    92.491899270558484, 94.651344040519886, 95.870634228245309, 98.831194218193692, 101.317851005731392])

def riemann_zeros(n, dps=18):
    """The first n zero heights γ_k of ζ from mpmath's zetazero, cached on disk. Validation markers only."""
    path = os.path.join(FIGDIR, f".zeros_{n}.npy")
    if os.path.exists(path):
        return np.load(path)
    with mp.workdps(dps):
        g = np.array([float(mp.im(mp.zetazero(k))) for k in range(1, n + 1)])
    np.save(path, g)
    return g

def nearest_errors(roots, heights):
    rec = np.array([roots[np.argmin(np.abs(roots - g))] for g in heights])
    return np.abs(rec - heights)

class Timer:
    def __init__(self, name): self.name = name
    def __enter__(self): self.t = time.time(); return self
    def __exit__(self, *a): print(f"    ({self.name}: {time.time() - self.t:.1f} s)")

# ======================================================================================================================
# block A — a_shell.py (until 24 September 2026), its former docstring:
# a_shell.py — block A: the shell theorem and the exact shell arithmetic (EXACT, integer-pinned)
# =============================================================================================
# Master ledger predicate 00:D11 (the shell theorem, 20-rh Thm. hp); paper ledger predicates 20:B1–B11, 20:E1, 20:E9, 20:E12–E13. Package checks:
#
#   A1  Thm. zeroslot     zero-slot: Σ_{x∈F_p^×} x^k = 0 for every nonterminal k, = −1 on the terminal slot
#   A2  Thm. compl        slot complementarity: Φ(k) = −g^k bijects the nonterminal slots onto F_p^× \ {−1}
#   A3  Lem. K            Hermitian phase calculus on F_{p²} = F_p(η), η² = ν a non-residue: |U_{p+1}| = p+1,
#                         Frobenius = inversion on U_{p+1}, i = √−1 Frobenius-fixed and off the circle (N(i) = −1)
#   A4  Prop. critical    the finite critical line: Tr z = 1 exactly on z = 2⁻¹ + bη; |L_{1/2}| = p;
#                         N(z) = ¼ − νb²; 2⁻¹ = 2κ+1 = −π (capacity-first)
#   A5  Thm. agree        the Klein four-group ⟨φ, ρ⟩ and its fixed loci F_p, L_{1/2}, {2⁻¹}; F_p ∩ L_{1/2} = {2⁻¹}
#   A6  §1.3 (register)   the Subject constants: π = 2κ, 2π ≡ −1, i = g^{−κ}, i² ≡ −1, e = g^i on the odd
#                         lift, g^π ≡ −1, e^{iπ} ≡ −1  (F_13: g = 2, κ = 3, i = 5, e = 6)
#   A6b Rem. frame        the odd-lift rule on every frame p ≡ 1 (mod 4) below 3000, least primitive root: with r the
#                         least residue of i, the lift is r if odd else r + p; on it e^{iπ} ≡ −1, on the even member
#                         e^{r'π} ≡ +1, so the lift matters in an exponent (F_17: g = 3, i = 4, lift 21, e = 5)
#   A7  Thm. hp (iii)     EXACT: the scale-shift on the power characters, S x^k = g^k x^k in F_p, and its trace
#                         Tr S^r = (p−1)·[(p−1) | r] (§10.2: the shell's trace carries no prime data) — integer arithmetic
#   A7b Thm. hp (i),(iii) [approx]: the complex reading — the constant mode carries the mean v̄ = ψ(p−1)/(p−1),
#                         the nontrivial characters carry v − v̄·1 (Rem. parseval), the normalised characters χ_j/√(p−1) are orthonormal and
#                         S χ_j = ω^j χ_j on ℓ²(F_p^×) — floating-point roots of unity, tolerance 10⁻¹⁰
#   A8  Def. jacobi       [approx]: self-adjointness is free: any real multiset is the spectrum of a real-symmetric
#                         tridiagonal matrix (Def. jacobi), checked on the first ten heights in floating point (10⁻¹¹)
#   A9  Prop. ground      EXACT: flat ground state, the Ramanujan sum c_p(n) = −1 for every n ≢ 0 (mod p), computed in
#                         F_q with a primitive p-th root of unity (q the least prime ≡ 1 mod p): Σ_{a=1}^{p−1} ω^{an} ≡ −1
#   A10 Def. shells       the shared structure of two shells is the quarter-turn core Q₄ (4 | p−1, 4 | Ω−1);
#                         on the laboratory pair (13, 233) the cycle projection C_{Ω−1} → C_{p−1} does not
#                         exist (12 ∤ 232) — the negative check behind the round-02 chronon paragraph
#   A11 Prop. coincide    frame coincidence below the horizon √p: residues, window products and primality
#                         (trial division inside the window) agree between F_p and the Carrier chart F_Ω,
#                         Ω the least prime ≡ 1 (mod 4) above p²
#   A12 Thm. closure      the closure of the heights on the laboratory Carriers Ω = 13, 233, 30089, 2408561: the
#                         largest embedded Subject p* = 3, 13, 173, 1549 (p*² < Ω < p'²), the cells of the cycle as its
#                         residues, the embedded cycle shorter, the wrap of the height reading, the pigeonhole of
#                         00:A2/00:A4 on the cells (rows A2, A4, F7)
#   A13 Completeness      row A3 (00:A3) on the laboratory pairs (p, Ω): the registration of the cycle is onto its registered
#                         Universe (every residue of it has a member, whole and under the Subject's reading), the Subject's cycle
#                         registers within the Carrier's, no reading of the Carrier's cycle within the Subject's is injective, one
#                         count both ways (FRC.Foundation.registration_onto, mutual_registration_count)
#
# Shells: p = 13, 17, 29, 37, 41 in full (all p² points of F_{p²}); 173 for A1, A4, A6; 1009 and 10009 for A11.
# Kinds: A1–A7, A6b, A9–A13 are integer arithmetic (EXACT); A7b and A8 use floating-point roots of unity and eigenvalues ([approx]).

SHELLS = [13, 17, 29, 37, 41]
BIG = 173

def prime_factors(n):
    f, d = set(), 2
    while d * d <= n:
        while n % d == 0:
            f.add(d); n //= d
        d += 1
    if n > 1: f.add(n)
    return f

def generator(p):
    for g in range(2, p):
        if all(pow(g, (p - 1) // q, p) != 1 for q in prime_factors(p - 1)):
            return g

def nonresidue(p):
    sq = {(x * x) % p for x in range(1, p)}
    return next(v for v in range(2, p) if v not in sq)

# F_{p^2} = F_p(η), η² = ν: elements (a, b) = a + bη
def mul(z, w, nu, p):
    return ((z[0] * w[0] + nu * z[1] * w[1]) % p, (z[0] * w[1] + z[1] * w[0]) % p)
def frob(z, p):            # z ↦ z^p : a + bη ↦ a − bη
    return (z[0], (-z[1]) % p)
def trace(z, p): return (2 * z[0]) % p
def norm(z, nu, p): return (z[0] * z[0] - nu * z[1] * z[1]) % p
def zpow(z, k, nu, p):
    r, b = (1, 0), z
    while k:
        if k & 1: r = mul(r, b, nu, p)
        b = mul(b, b, nu, p); k >>= 1
    return r

def block_A():
    """Block A — the shell theorem and the exact shell arithmetic: 62 checks on the shells p = 13, 17, 29, 37, 41 (173, 1009, 10009 and the frames below 3000 for single checks), 56 integer-exact and 6 [approx]."""
    print("\n== block A: the shell theorem (00:D11) ==")
    for p in SHELLS + [BIG]:
        g, nu = generator(p), nonresidue(p)
        kappa = (p - 1) // 4; assert 4 * kappa + 1 == p
        # A1 zero-slot
        ok = all(sum(pow(x, k, p) for x in range(1, p)) % p == 0 for k in range(1, p - 1)) \
             and sum(pow(x, p - 1, p) for x in range(1, p)) % p == p - 1
        # 20:B4 (p20011)
        check("A1", f"zero-slot on F_{p}", ok, f"Σx^k=0 for k=1..{p-2}; = -1 at k={p-1}")
        # A6 the Subject constants, capacity-first
        pi_ = 2 * kappa
        i_ = pow(g, p - 1 - kappa, p)                       # g^{-κ}
        assert i_ == (-pow(g, kappa, p)) % p
        i_odd = i_ if i_ % 2 == 1 else i_ + p               # the odd integer lift of i (Remark frame)
        e_ = pow(g, i_odd, p)
        ok = ((2 * pi_) % p == p - 1 and (i_ * i_) % p == p - 1 and pow(g, pi_, p) == p - 1
              and pow(e_, i_odd * pi_, p) == p - 1 and (2 * (2 * kappa + 1)) % p == 1
              and (2 * kappa + 1) % p == (-pi_) % p)
        # 20:B10 (p20017)
        check("A6", f"Subject constants on F_{p}: π=2κ, i=g^-κ, e=g^i (odd lift)", ok,
              f"g={g} κ={kappa} π={pi_} i={i_} e={e_}: 2π≡-1, i²≡-1, g^π≡-1, e^(iπ)≡-1, 2⁻¹=2κ+1=-π")
        # A4 the finite critical line
        inv2 = (2 * kappa + 1) % p
        line = [(inv2, b) for b in range(p)]
        ok = all(trace(z, p) == 1 for z in line) and len(set(line)) == p \
             and all(norm(z, nu, p) == (pow(4, p - 2, p) - nu * z[1] * z[1]) % p for z in line)
        if p != BIG:   # the converse on the full plane: Tr z = 1 only on the line
            ok = ok and all(((2 * a) % p == 1) == (a == inv2) for a in range(p))
        # 20:B8 (p20015)
        check("A4", f"finite critical line on F_{p}: Tr z = 1 ⟺ z = 2⁻¹ + bη, |L| = p, N = ¼ − νb²", ok,
              f"ν={nu}, 2⁻¹={inv2}")
        if p == BIG:
            continue
        # A2 slot complementarity
        image = {(-pow(g, k, p)) % p for k in range(1, p - 1)}
        # 20:B5 (p20012)
        check("A2", f"Φ(k) = −g^k bijects the nonterminal slots onto F_{p}^× \\ {{−1}}", image == set(range(1, p - 1)),
              f"|image| = {len(image)} = p−2")
        # A3 Hermitian phase calculus
        K = [(a, b) for a in range(p) for b in range(p)]
        U = [z for z in K if norm(z, nu, p) == 1]
        inv_ok = all(frob(z, p) == zpow(z, p, nu, p) and mul(z, frob(z, p), nu, p) == (1, 0) for z in U)
        i2 = [(a, 0) for a in range(p) if (a * a) % p == p - 1]
        ok = len(U) == p + 1 and inv_ok and len(i2) == 2 and all(frob(z, p) == z and norm(z, nu, p) == p - 1 for z in i2)
        # 20:B6 (p20013)
        check("A3", f"F_{p}²: |U_(p+1)| = p+1, Frobenius = inversion on it, i Frobenius-fixed with N(i) = −1", ok)
        # A5 Klein four-group
        phi = lambda z: frob(z, p)
        rho = lambda z: ((1 - z[0]) % p, (-z[1]) % p)
        sig = lambda z: rho(phi(z))
        fix_phi = {z for z in K if phi(z) == z}; fix_rho = {z for z in K if rho(z) == z}; fix_sig = {z for z in K if sig(z) == z}
        ok = (all(phi(phi(z)) == z and rho(rho(z)) == z and phi(rho(z)) == rho(phi(z)) for z in K)
              and fix_phi == {(a, 0) for a in range(p)} and fix_sig == set(line) and fix_rho == {(inv2, 0)}
              and fix_phi & fix_sig == {(inv2, 0)})
        # 20:B9 (p20016)
        check("A5", f"Klein four-group on F_{p}²: Fix φ = F_p, Fix σ = L_1/2, Fix ρ = {{2⁻¹}}, F_p ∩ L_1/2 = {{2⁻¹}}", ok)
        # A9 flat ground state, in exact arithmetic: a primitive p-th root of unity ω in F_q, q ≡ 1 (mod p) prime
        q = p + 1
        while not (q % p == 1 and sp.isprime(q)): q += p
        gq = sp.primitive_root(q); om = pow(gq, (q - 1) // p, q)
        assert pow(om, p, q) == 1 and om != 1
        cp = [sum(pow(om, a * n, q) for a in range(1, p)) % q for n in range(1, p)]
        # 20:B7 (p20014)
        check("A9", f"c_{p}(n) ≡ −1 (mod {q}) for n ≠ 0: Σ_a ω^{{an}} in F_{q}, ω of order {p}", all(c == q - 1 for c in cp))
        # A7 spectral content and the two readings of the characters
        lam = {}
        for n in range(1, p):
            m, q = n, None
            for d in range(2, n + 1):
                if n % d == 0:
                    q = d; break
            if q is None: lam[n] = 0.0; continue
            while m % q == 0: m //= q
            lam[n] = math.log(q) if m == 1 else 0.0
        v = np.array([lam[n] for n in range(1, p)])
        dlog = {pow(g, m, p): m for m in range(p - 1)}
        w = cmath.exp(2j * math.pi / (p - 1))
        chi = np.array([[w ** (j * dlog[n]) for n in range(1, p)] for j in range(p - 1)])
        coef = chi.conj() @ v / (p - 1)
        mean = v.mean()
        recon_nontriv = (coef[1:] @ chi[1:]).real
        ok_mean = abs(coef[0].real - mean) < 1e-12 and np.allclose(recon_nontriv, v - mean, atol=1e-10) \
                  and np.allclose((coef @ chi).real, v, atol=1e-10)
        gram = chi.conj() @ chi.T / (p - 1)
        ok_orth = np.allclose(gram, np.eye(p - 1), atol=1e-10)
        # S f(x) = f(g x): power characters in F_p, complex characters on ℓ²
        ok_fp = all(pow((g * x) % p, k, p) == (pow(g, k, p) * pow(x, k, p)) % p for k in range(p - 1) for x in range(1, p))
        shifted = lambda j: np.array([w ** (j * dlog[(g * n) % p]) for n in range(1, p)])   # (S χ_j)(n) = χ_j(g n)
        ok_c = all(np.allclose(shifted(j), w ** j * chi[j]) for j in range(p - 1))
        tr = [sum(1 for x in range(1, p) if (pow(g, r, p) * x) % p == x) for r in range(1, p)]
        ok_tr = all(tr[r - 1] == ((p - 1) if r % (p - 1) == 0 else 0) for r in range(1, p))
        # 20:E1 (p20032), 20:E12 (p20043)
        check("A7", f"F_{p}: S x^k = g^k x^k on the power characters (integer arithmetic); Tr S^r = (p−1)[(p−1)|r]", ok_fp and ok_tr)
        # 20:E13 (p20044)
        check("A7b", f"ℓ²(F_{p}^×): mean v̄ = ψ(p−1)/(p−1) on the trivial mode, v − v̄·1 on the nontrivial characters, χ_j/√(p−1) orthonormal; Sχ_j = ω^j χ_j",
              ok_mean and ok_orth and ok_c, f"v̄ = {mean:.6f} (= log 27720/12 at p = 13)" if p == 13 else "", kind="[approx]")
        # A10 the shared quarter-turn core; no cycle projection onto (13, 233)
        Om = 233
        q4 = {pow(i_, a, p) for a in range(4)}
        ok = q4 == {1, i_, p - 1, (-i_) % p} and (p - 1) % 4 == 0 and (Om - 1) % 4 == 0
        if p == 13:
            ok = ok and (Om - 1) % (p - 1) != 0
            # 20:B1 (p20008)
            check("A10", "Q₄ ⊂ both cycles; C_232 ↠ C_12 does not exist (12 ∤ 232) on the pair (13, 233)", ok, "the shells share the core, not a clock")
        else:
            check("A10", f"Q₄ = {{1, i, −1, −i}} ⊂ F_{p}^×, 4 | p−1", ok)
    # A11 frame coincidence below the horizon (Prop. coincide): the Carrier chart Ω is the least prime ≡ 1 (mod 4) above p²

    for p in SHELLS + [1009, 10009]:
        Om = int(sp.nextprime(p * p))
        while Om % 4 != 1:
            Om = int(sp.nextprime(Om))
        H = math.isqrt(p)
        same = all(n % p == n % Om == n for n in range(1, H + 1))
        prods = all((a * b) % p == (a * b) % Om == a * b for a in range(1, H + 1) for b in range(1, H + 1))
        irreducible = {n for n in range(2, H + 1) if all(n % d for d in range(2, math.isqrt(n) + 1))}   # trial division inside the window
        primes = {n for n in range(2, H + 1) if sp.isprime(n)}
        # 20:B2 (p20009)
        check("A11", f"frame coincidence below √{p} = {H} on the pair ({p}, {Om}): residues, window products and primality agree", same and prods and irreducible == primes,
              f"Π_p = {sorted(primes)}")
    # A6b the odd-lift rule (Remark frame) on every admissible frame below 3000, least primitive root
    frames = [q for q in range(5, 3000) if q % 4 == 1 and sp.isprime(q)]
    bad = []
    for q in frames:
        gq = int(sp.primitive_root(q)); kq = (q - 1) // 4; piq = 2 * kq
        r = pow(gq, q - 1 - kq, q)                          # the least residue of i = g^{-κ}
        odd, even = (r, r + q) if r % 2 == 1 else (r + q, r)
        e_odd = pow(gq, odd, q)
        if not (pow(e_odd, odd * piq, q) == q - 1 and pow(e_odd, even * piq, q) == 1 and (r * r) % q == q - 1):
            bad.append(q)
    f17 = (pow(3, 16 - 4, 17), pow(3, 21, 17))               # F_17 with g = 3: i = 3^{-4} = 4 (even), lift 21, e = 3^21 = 5
    ok = not bad and f17 == (4, 5)
    check("A6b", f"the odd-lift rule on all {len(frames)} frames p ≡ 1 (mod 4) below 3000: e^{{iπ}} ≡ −1 on the odd lift, ≡ +1 on the even member; F_17: g=3, i=4, lift 21, e=5", ok,
          f"frames {len(frames)}, failures {bad}; F_17 (i, e) = {f17}")
    # A8 self-adjointness is free
    J = jacobi_from_points(HEIGHTS[:10])
    ev = np.sort(np.linalg.eigvalsh(J))
    ok = np.allclose(J, J.T) and np.max(np.abs(np.triu(J, 2))) == 0 and np.max(np.abs(ev - HEIGHTS[:10])) < 1e-11
    check("A8", "any real multiset is the spectrum of a real-symmetric tridiagonal matrix (Lanczos on ten heights, floating point)", ok,
          f"max|eig(J) − height| = {np.max(np.abs(ev - HEIGHTS[:10])):.1e}", kind="[approx]")

    # A12 the closure of the heights (Thm. closure; rows A2, A4, F7), on the four laboratory Carriers Ω = 13, 233, 30089,
    # 2408561: the largest embedded Subject p* with p*² < Ω < p'² (p' the next prime); the cells of a cycle are its residues
    # 0..q−1 and a Subject of cardinality p reads the cells y < p, its own residues, so an embedded Subject's cycle is shorter
    # than the Carrier's and the Carrier's top cell is read from labels up to √Ω, beyond every embedded window √p*; the
    # wrap of the height reading, (T + Ω) ≡ T; the pigeonhole of 00:A2/00:A4 on the cells — a reading of the Ω cells into
    # o < Ω records identifies two cells (found by search for o = p* and o = Ω − 1), and an injective reading needs o ≥ Ω
    for Om in (13, 233, 30089, 2408561):
        ps = int(sp.prevprime(math.isqrt(Om) + 1)); pn = int(sp.nextprime(ps))
        ok = sp.isprime(Om) and Om % 4 == 1 and sp.isprime(ps) and sp.isprime(pn) and ps * ps < Om < pn * pn
        ok &= all(not sp.isprime(q) for q in range(ps + 1, pn))            # p* the largest prime below √Ω
        ok &= ps < Om and math.isqrt(ps) < math.isqrt(Om)                   # the embedded cycle shorter; the top cell's labels beyond √p*
        ok &= all((T + Om) % Om == T % Om for T in (0, 1, ps, Om - 1, Om, 7 * Om + 3))   # the wrap of the height reading
        collisions = {}
        for o in (ps, Om - 1):
            seen = {}
            for y in range(Om):                                             # the cells of the Carrier's cycle, read into o records
                r = y % o
                if r in seen:
                    collisions[o] = (seen[r], y); break
                seen[r] = y
            ok &= o in collisions and collisions[o][0] != collisions[o][1] and collisions[o][0] % o == collisions[o][1] % o
        ok &= len({y for y in range(Om)}) == Om                             # the identity reading into Ω records is injective: Ω ≤ Ω
        # 20:F7 (p20079)
        check("A12", f"closure of the heights on Ω = {Om}: p* = {ps} ({ps}² < Ω < {pn}²), the cycle's {Om} cells, an embedded Subject reads {ps} of them; readings into {ps} and {Om - 1} records collide", ok,
              f"collisions {collisions}; √Ω = {math.isqrt(Om)}, √p* = {math.isqrt(ps)}")

    # A13 Completeness (row A3; 00:A3), on the laboratory pairs (p, Ω) = (13, 233), (173, 30089), (1549, 2408561): the
    # registration of a totality is onto its registered Universe — the registered Universe is the set of residues at which some
    # member registers, read back as a member for every residue of it (the Carrier's cells registered whole, ρ(y) = y, and the
    # Subject's reading of them, ρ_p(y) = y mod p: Ω and p residues, each with a member); and two totalities each registered
    # whole within the other have one count — the identity registers the Subject's cycle within the Carrier's, every reading of
    # the Carrier's Ω cells into the Subject's p records identifies two cells (y mod p, an affine reading, the square; the
    # pigeonhole of 00:A2 both ways is FRC.Foundation.mutual_registration_count), and only cycles of one count embed both ways
    for p, Om in ((13, 233), (173, 30089), (1549, 2408561)):
        members = {}
        for y in range(Om):                                                 # the Carrier's cycle registered whole
            members.setdefault(y % Om, y)
        ok = len(members) == Om and all(members[r] % Om == r for r in members)          # onto: every residue has a member
        membersp = {}
        for y in range(Om):                                                 # the Subject's reading of the Carrier's cells
            membersp.setdefault(y % p, y)
        ok &= len(membersp) == p and all(membersp[r] % p == r for r in membersp)
        ok &= len({x % Om for x in range(p)}) == p                          # the identity registers Shell p within Shell Ω
        readings = {"y mod p": lambda y: y % p, "3y+5 mod p": lambda y: (3 * y + 5) % p, "y² mod p": lambda y: (y * y) % p}
        collisions = {}
        for name, f in readings.items():                                    # no reading of Shell Ω within Shell p is injective
            seen = {}
            for y in range(Om):
                r = f(y)
                if r in seen:
                    collisions[name] = (seen[r], y); break
                seen[r] = y
            ok &= name in collisions and collisions[name][0] != collisions[name][1] and f(collisions[name][0]) == f(collisions[name][1])
        ok &= p < Om and len({x % p for x in range(p)}) == p                 # one count: the identity both ways on Shell p
        # 20:A3 (p00003)
        check("A13", f"completeness on the pair ({p}, {Om}): the registration of the cycle is onto its registered Universe ({Om} residues; {p} under the Subject's reading); F_{p} registers within F_{Om}, every reading of the {Om} cells into {p} records collides, one count only both ways", ok,
              "collisions " + ", ".join(f"{k}: {v}" for k, v in collisions.items()))

# ======================================================================================================================
# block B — b_deframe.py (until 24 September 2026), its former docstring:
# b_deframe.py — block B: the de-framing dictionary and its consequences ([chart], [approx])
# =========================================================================================
# The dictionary of Definition deframe: a shell of cardinality p reads ζ on the line to height
# T = 2πp with the Riemann–Siegel main sum of length √p = √(T/2π); a height is the scale
# coordinate of the shell that reads it (T/2π = p). Paper-local predicates:
#
#   B1  Prop. density   [chart]  smooth zero density at T = 2πp equals the shell scale-depth (1/2π) log p:
#                                 0.6226, 0.9891, 1.3556, 1.7220 at p = 50, 500, 5·10³, 5·10⁴ (a substitution
#                                 into the Riemann–von Mangoldt formula; a consistency of the dictionary)
#   B2  Obs. residue    [approx] the finite-horizon reconstruction error |Z_horizon − Z| scales as p^{-1/4}
#                                 (unconditional: truncation of the main sum), fitted slope ≈ −1/4
#   B3  Prop. critical  [chart]  the de-framing limit of the critical real part: 2⁻¹/p = (2κ+1)/p → ½
#   B4  Def. deframe    [approx] the horizon-length main sum (length ⌊√(t/2π)⌋, weight n^{-1/2}) tracks Z(t)
#                                 through the first ten zeros: sign changes of the main sum on [10, 55]
#                                 bracket every one of γ_1..γ_10 (the on-line reading of Proposition turing)
#
# The Hardy Z function Z(t) enters here as the classical side of the correspondence (the paper's
# "ζ never evaluated" discipline binds the prime-side realisation of block C, not this dictionary
# check). Figure: fig_deframing.pdf.


def Z_true(t):
    return float(mp.siegelz(t))

def Z_horizon(t):
    """Riemann–Siegel main sum of length ⌊√(t/2π)⌋ = the shell horizon √p at T = 2πp; no remainder."""
    N = int(mp.floor(mp.sqrt(t / (2 * mp.pi))))
    th = mp.siegeltheta(t)
    return float(2 * mp.fsum(mp.cos(th - t * mp.log(n)) / mp.sqrt(n) for n in range(1, N + 1)))

def block_B():
    """Block B — the de-framing dictionary: the zero density as shell scale-depth, the reconstruction residue, the horizon-length main sum through the first zeros; 4 checks ([chart], [approx])."""
    mp.mp.dps = 18
    print("\n== block B: the de-framing dictionary (Def. deframe) ==")
    # B1 density
    stated = {50: 0.6226, 500: 0.9891, 5000: 1.3556, 50000: 1.7220}
    got = {p: math.log(p) / (2 * math.pi) for p in stated}
    ok = all(abs(got[p] - stated[p]) < 6e-5 for p in stated)
    # illustration: 20:D2 retired 2026-10-15 (T05)
    check("B1", "smooth zero density at T = 2πp is (1/2π) log p", ok,
          "  ".join(f"p={p}: {got[p]:.4f}" for p in stated), kind="[chart]")
    # B3 de-framing limit
    vals = [(p, (2 * ((p - 1) // 4) + 1) / p) for p in [13, 53, 101, 409, 1009, 10009]]
    ok = all(v > 0.5 for _, v in vals) and all(vals[i][1] > vals[i + 1][1] for i in range(len(vals) - 1)) and abs(vals[-1][1] - 0.5) < 1e-3
    check("B3", "de-framing limit (2κ+1)/p → ½ from above", ok, "  ".join(f"{p}: {v:.5f}" for p, v in vals), kind="[chart]")
    # B4 main sum brackets the first ten zeros
    with Timer("horizon sums on [10,55]"):
        ts = np.linspace(10, 55, 700 if not FAST else 350)
        zt = np.array([Z_true(t) for t in ts]); zh = np.array([Z_horizon(t) for t in ts])
    sc = ts[:-1][zh[:-1] * zh[1:] < 0]
    inwin = HEIGHTS[(HEIGHTS > 10) & (HEIGHTS < 55)]              # γ_1..γ_11
    dev = [float(np.min(np.abs(sc - g))) for g in inwin]
    ok = len(sc) == len(inwin) and max(dev) < 0.5
    # illustration: 20:D4 retired 2026-10-15 (T11)
    check("B4", "the bare horizon-length main sum has one sign change per zero on [10,55], each within 0.5 of γ_n", ok,
          f"{len(sc)} sign changes for {len(inwin)} zeros; max deviation {max(dev):.2f} (1–2 terms only at these heights)", kind="[approx]")
    # B2 residue scaling
    with Timer("residue scan"):
        T0 = np.array([40, 80, 160, 320, 640, 1280, 2560, 5120] if not FAST else [40, 80, 160, 320, 640, 1280])
        err = []
        for t0 in T0:
            e = [abs(Z_horizon(float(t0) + 0.123 * i) - Z_true(float(t0) + 0.123 * i)) for i in range(1, 16)]
            err.append(float(np.median(e)))
    slope = np.polyfit(np.log(T0), np.log(err), 1)[0]
    # illustration: 20:D3 retired 2026-10-15 (T05)
    check("B2", "reconstruction residue ∝ p^{-1/4}: fitted log-log slope in [−0.40, −0.10]", -0.40 < slope < -0.10,
          f"slope = {slope:.3f}", kind="[approx]")
    # figure
    fig, ax = plt.subplots(1, 3, figsize=(15, 4.3))
    ax[0].axhline(0, color="#ccc", lw=0.8)
    for g in HEIGHTS[:10]: ax[0].axvline(g, color="#ccc", lw=0.8, ls=":")
    ax[0].plot(ts, zt, color="#1a1a1a", lw=1.5, label=r"$Z(t)$")
    ax[0].plot(ts, zh, color="#c0392b", lw=1.3, ls="--", label=r"horizon sum, $N=\lfloor\sqrt{t/2\pi}\rfloor$")
    ax[0].plot(HEIGHTS[:10], [0] * 10, "o", color="#1f5fbf", ms=5, zorder=5, label=r"zeros $\gamma_n$")
    ax[0].set_xlabel(r"height $t$ ($=2\pi p$ at shell scale $p$)"); ax[0].set_ylabel(r"$Z(t)$"); ax[0].set_ylim(-6, 6)
    ax[0].set_title("B4: de-framing = finite Riemann–Siegel"); ax[0].legend(fontsize=8)
    ps = np.logspace(1.3, 5, 30)
    ax[1].plot(ps, np.log(ps) / (2 * np.pi), color="#1a1a1a", lw=1.8, label=r"$\frac{1}{2\pi}\log\frac{T}{2\pi}$, $T=2\pi p$")
    ax[1].plot(list(stated), [got[p] for p in stated], "o", color="#c0392b", label=r"shell scale-depth $\frac{1}{2\pi}\log p$")
    ax[1].set_xscale("log"); ax[1].set_xlabel("shell cardinality $p$"); ax[1].set_ylabel("zeros per unit height")
    ax[1].set_title("B1: zero density = shell scale-depth [chart]"); ax[1].legend(fontsize=8)
    ax[2].loglog(T0, err, "o-", color="#c0392b", lw=1.4, label=r"median $|Z_{\rm horizon}-Z|$")
    ax[2].loglog(T0, T0 ** -0.25, color="#1a1a1a", ls="--", label=r"$t^{-1/4}=p^{-1/4}$")
    ax[2].set_xlabel(r"height $t$ ($=2\pi p$)"); ax[2].set_ylabel("reconstruction error")
    ax[2].set_title(f"B2: residue $\\propto p^{{-1/4}}$ (slope {slope:.2f})"); ax[2].legend(fontsize=8)
    plt.tight_layout(); plt.savefig(f"{FIGDIR}/fig_deframing.pdf", bbox_inches="tight"); plt.savefig(f"{FIGDIR}/fig_deframing.png", dpi=110, bbox_inches="tight"); plt.close()
    print(f"    wrote {FIGDIR}/fig_deframing.pdf")
    # the paper's Figure "the reading of ζ on the line": (a) the main sum of the window through the first ten zeros, (b) the residue
    def _reading(fig, ax):
        a = ax[0]; a.axhline(0, color="0.8", lw=0.6)
        for g in HEIGHTS[:10]: a.axvline(g, color="0.85", lw=0.6, ls=":")
        a.plot(ts, zt, color=INK, lw=1.2, label=r"$Z(t)$")
        a.plot(ts, zh, color=RED, lw=1.1, ls="--", label=r"main sum to $\lfloor\sqrt{t/2\pi}\rfloor$")
        a.plot(HEIGHTS[:10], [0] * 10, "o", color=BLUE, ms=3.6, zorder=5, label=r"zeros $\gamma_n$")
        a.set_xlim(10, 55); a.set_ylim(-6.3, 7.6); a.set_yticks([-6, -4, -2, 0, 2, 4, 6]); a.set_xlabel(r"height $t$"); a.set_ylabel(r"$Z(t)$")
        a.legend(loc="upper center", ncol=3, columnspacing=1.0, handlelength=1.6); panel_letter(a, "(a)")
        b = ax[1]; b.loglog(T0, err, "o-", color=RED, lw=1.1, ms=3.6, label=r"median $|Z_M-Z|$")
        b.loglog(T0, T0 ** -0.25, color=INK, ls="--", lw=1.0, label=r"$t^{-1/4}$")
        b.set_xlabel(r"height $t$"); b.set_ylabel("residue"); b.legend(loc="lower left"); panel_letter(b, "(b)")
    paper_figure("fig_reading", _reading, 2.45)

# ======================================================================================================================
# block C — c_primeside.py (until 24 September 2026), its former docstring:
# c_primeside.py — block C: the spectrum from the prime side, ζ never evaluated ([approx])
# =======================================================================================
# Every construction here uses only {Λ(n)} (sieved), their logarithms, and the archimedean
# phase θ(T) from log Γ. The Riemann heights enter as validation markers only.
# Paper-local predicates:
#
#   C1  Obs. primespec  the scale-spectrum |Σ_N(γ)| of the tapered comb, N = 10⁶, peaks at the first six
#                       heights (paper: 14.14, 21.02, 25.02, 30.40, 32.96, 37.57; the peak is the taper's, of width ~2π/log N)
#   (Root search: the brackets of every root are the half-integer crossings of the count itself on [10, 52], found by a
#    0.1 scan and refined by Brent's method; the reference heights enter only in the errors reported.)
#   C2  Obs. trace      the raw secular condition Ñ_N(T) = n − ½ recovers the first ten heights: mean error
#                       4.4×10⁻⁵, maximum 1.5×10⁻⁴ (at γ₁) at N = 10⁶; 3.6×10⁻⁴ at 10³; 6×10⁻⁵ at 10⁵
#   C2b Obs. trace      the pole-corrected secular condition N̂_N(T) = n − ½ (Prop. combformula): mean error 3.4×10⁻⁵
#                       (max 6.6×10⁻⁵) at 10⁶, 2.3×10⁻⁵ at 10⁷, 1.3×10⁻⁵ (max 2.8×10⁻⁵) at 10⁸ — falling with depth
#   C2c Obs. trace      the raw condition does not sharpen past 10⁷: mean 2.7×10⁻⁵ at 10⁷ and 4.2×10⁻⁵ at 10⁸, the γ₁
#                       error growing from 1.5×10⁻⁴ (10⁶) to 2.6×10⁻⁴ (10⁸) — the pole term, largest at the lowest height
#   C3  Obs. matrix     the colleague matrix of the Chebyshev fit of Ξ(T) = cos(π N̂_N(T)) on [10, 52] at N = 10⁶:
#                       mean error 4.8×10⁻⁵ at dimension 520, 3.5×10⁻⁵ by 620, converging to the corrected roots' own 3.4×10⁻⁵
#   C4  Obs. jacobi     the comb-built Jacobi matrix of the corrected secular roots: real-symmetric tridiagonal, eigenvalues =
#                       the roots to 10⁻¹², the heights to 3.4×10⁻⁵; the ten recurrence coefficients a, b as stated
#   C5  Prop. gauge     the additive injection −i d/du + V_comb is gauge-trivial: spacing standard
#                       deviation 0.08 (absolute; 0.11 of the mean spacing 0.72) against 0.39 of the mean
#                       for the heights (package finding: the paper's two figures use two conventions)
#
# Figures: fig_prime_spectrum.pdf (C1), fig_operator_spectrum.pdf (C2, C3, C5).

# the paper's stated numbers
PEAKS_STATED = [14.14, 21.02, 25.02, 30.40, 32.96, 37.57]
A_STATED = [34.314, 31.021, 31.179, 31.763, 32.812, 36.227, 35.012, 37.157, 36.092, 37.564]
B_STATED = [11.178, 10.431, 9.579, 8.263, 7.008, 8.415, 7.048, 4.093, 4.110]

LO, HI = 10.0, 52.0          # the shell window of Obs. trace/matrix; the ten roots are the crossings of ½ … 9½ found on it

def roots_on_window(comb, corrected):
    """Ten secular roots from the count alone (brackets by a 0.1 scan of the window, Brent refinement); the reference
    heights enter only in the error reported afterwards. Fails loudly if the crossings are not exactly ½ … 9½, once each."""
    roots, levels, extra = secular_roots_scan(comb, LO, HI, corrected=corrected)
    assert levels == [k + 0.5 for k in range(10)] and not extra, f"crossings {levels}, extra {extra}"
    return roots

def additive_spectrum(U=15.0, M=2048, potential_scale=5.0):
    """H = −i d/du + V_comb on a periodic log-grid of length U (Prop. gauge)."""
    du = U / M
    k = np.fft.fftfreq(M, d=du) * 2 * np.pi
    F = np.fft.fft(np.eye(M), axis=0) / np.sqrt(M)
    D = F.conj().T @ np.diag(k) @ F
    D = 0.5 * (D + D.conj().T)
    Np = int(math.e ** U) + 1
    n, lam = von_mangoldt_support(Np)
    V = np.zeros(M)
    for nn, ll in zip(n, lam):
        j = int(round(math.log(nn) / du)) % M
        V[j] += ll / math.sqrt(nn) / du
    H = D + np.diag(potential_scale * V)
    H = 0.5 * (H + H.conj().T)
    return np.sort(np.linalg.eigvalsh(H))

def _C_primeside():
    print("\n== block C: the prime-side realisation, ζ never evaluated ==")
    N = 10 ** 6
    with Timer(f"comb to {N}"):
        comb = Comb(N)
    # C1 peaks of the scale-spectrum
    with Timer("scale-spectrum"):
        gs = np.arange(10.0, 40.0, 0.005)
        sig = comb.sigma(gs)
    peaks = [gs[i] for i in range(1, len(gs) - 1) if sig[i] > sig[i - 1] and sig[i] > sig[i + 1]]
    top = sorted(sorted(peaks, key=lambda g: -sig[np.argmin(np.abs(gs - g))])[:6])
    err1 = [abs(t - h) for t, h in zip(top, HEIGHTS[:6])]
    err_stated = [abs(t - h) for t, h in zip(top, PEAKS_STATED)]
    base = np.median(sig)
    ratio = min(sig[np.argmin(np.abs(gs - t))] for t in top) / base
    # illustration: 20:E5 retired 2026-10-15 (T05)
    check("C1", "scale-spectrum peaks at the stated 14.14 … 37.57 (within 0.015) and at γ_1..γ_6 (within 0.05, the taper's width); each peak ≥ 4× the baseline",
          max(err_stated) < 0.015 and max(err1) < 0.05 and ratio > 4,
          "peaks " + ", ".join(f"{t:.2f}" for t in top) + f"; max |peak − γ| {max(err1):.3f}; min peak/baseline {ratio:.1f}", kind="[approx]")
    # C2 secular roots at three depths
    errs = {}
    for depth in ([10 ** 3, 10 ** 5, 10 ** 6] if not FAST else [10 ** 5, 10 ** 6]):
        c = comb if depth == N else Comb(depth)
        roots = roots_on_window(c, corrected=False)
        e = np.abs(roots - HEIGHTS[:10]); errs[depth] = (e.mean(), e.max())
    e6 = errs[10 ** 6]
    ok = abs(e6[0] - 4.4e-5) < 0.6e-5 and abs(e6[1] - 1.46e-4) < 0.15e-4 and (FAST or errs[10 ** 3][0] < 6e-4) and errs[10 ** 5][0] < 1e-4
    # illustration: 20:E6 retired 2026-10-15 (T11)
    check("C2", "raw secular condition: ten heights to mean 4.4e-5, max 1.5e-4 (γ₁) at N = 10⁶; 3.6e-4 at 10³, 6e-5 at 10⁵", ok,
          "; ".join(f"N={d:.0e}: mean {m:.2e} max {x:.2e}" for d, (m, x) in errs.items()), kind="[approx]")
    # C2b, C2c: the pole-corrected secular condition against the raw one, with depth (Prop. combformula)
    deep = [10 ** 6, 10 ** 7] + ([10 ** 8] if not FAST else [])
    raw_e, cor_e = {}, {}
    with Timer(f"secular roots, raw and corrected, to {deep[-1]:.0e}"):
        for depth in deep:
            c = comb if depth == N else Comb(depth)
            er = np.abs(roots_on_window(c, corrected=False) - HEIGHTS[:10]); ec = np.abs(roots_on_window(c, corrected=True) - HEIGHTS[:10])
            raw_e[depth] = (er.mean(), er.max(), er[0]); cor_e[depth] = (ec.mean(), ec.max(), ec[0])
            if depth != N: del c
    c6 = cor_e[10 ** 6]
    ok = (abs(c6[0] - 3.4e-5) < 0.4e-5 and abs(c6[1] - 6.6e-5) < 0.8e-5 and abs(cor_e[10 ** 7][0] - 2.3e-5) < 0.4e-5
          and (FAST or (abs(cor_e[10 ** 8][0] - 1.3e-5) < 0.3e-5 and cor_e[10 ** 8][1] < 3.2e-5))
          and all(cor_e[deep[i + 1]][0] < cor_e[deep[i]][0] for i in range(len(deep) - 1)))
    check("C2b", "pole-corrected secular condition: mean 3.4e-5 (max 6.6e-5) at 10⁶, 2.3e-5 at 10⁷, 1.3e-5 (max 2.8e-5) at 10⁸; falling with depth", ok,
          "; ".join(f"N={d:.0e}: mean {m:.2e} max {x:.2e} γ₁ {g:.2e}" for d, (m, x, g) in cor_e.items()), kind="[approx]")
    ok = (abs(raw_e[10 ** 7][0] - 2.7e-5) < 0.4e-5 and (FAST or (abs(raw_e[10 ** 8][0] - 4.2e-5) < 0.5e-5 and raw_e[10 ** 8][0] > raw_e[10 ** 7][0]
          and abs(raw_e[10 ** 8][2] - 2.6e-4) < 0.3e-4 and raw_e[10 ** 8][2] > raw_e[10 ** 6][2])))
    check("C2c", "raw secular condition does not sharpen past 10⁷: mean 2.7e-5 at 10⁷, 4.2e-5 at 10⁸; γ₁ error 1.5e-4 (10⁶) → 2.6e-4 (10⁸): the pole term", ok,
          "; ".join(f"N={d:.0e}: mean {m:.2e} max {x:.2e} γ₁ {g:.2e}" for d, (m, x, g) in raw_e.items()), kind="[approx]")
    roots6 = roots_on_window(comb, corrected=True)
    # C4 Jacobi (of the corrected secular roots)
    J = jacobi_from_points(roots6)
    ev = np.sort(np.linalg.eigvalsh(J))
    a, b = np.diag(J), np.diag(J, 1)
    ok = (np.allclose(J, J.T) and np.max(np.abs(np.triu(J, 2))) == 0 and np.max(np.abs(ev - roots6)) < 1e-12
          and np.max(np.abs(a - A_STATED)) < 2e-3 and np.max(np.abs(b - B_STATED)) < 2e-3
          and abs(np.mean(np.abs(ev - HEIGHTS[:10])) - 3.4e-5) < 0.4e-5)
    # illustration: 20:E9 retired 2026-10-15 (T05)
    check("C4", "Jacobi matrix of the corrected roots: real-symmetric tridiagonal; eig = roots to 1e-12; a, b as stated; heights to 3.4e-5", ok,
          f"max|eig−roots| = {np.max(np.abs(ev - roots6)):.1e}; a[0..2] = {a[0]:.3f}, {a[1]:.3f}, {a[2]:.3f}; b[0] = {b[0]:.3f}", kind="[approx]")
    # C3 colleague matrix of the corrected secular determinant
    with Timer("colleague matrices"):
        degs = [180, 260, 340, 420, 520, 620] if not FAST else [340, 520]
        conv = {d: float(np.mean(nearest_errors(colleague_roots(comb, 10.0, 52.0, d, corrected=True), HEIGHTS[:10]))) for d in degs}
    ok = abs(conv[520] - 4.8e-5) < 0.6e-5 and (FAST or abs(conv[620] - 3.5e-5) < 0.5e-5)
    # illustration: 20:E8 retired 2026-10-15 (T05)
    check("C3", "colleague matrix of cos(π N̂_N) on [10,52], N = 10⁶: mean error 4.8e-5 at dim 520, 3.5e-5 by 620 (the roots' own 3.4e-5)", ok,
          "; ".join(f"dim {d}: {v:.2e}" for d, v in conv.items()), kind="[approx]")
    eig520 = colleague_roots(comb, 10.0, 52.0, 520, corrected=True)
    # C5 additive injection
    with Timer("additive operator"):
        ev_add = additive_spectrum()
    eva = ev_add[(ev_add > 10) & (ev_add < 50)]
    da, dh = np.diff(eva), np.diff(HEIGHTS[:10])
    cv_add, cv_h = np.std(da) / np.mean(da), np.std(dh) / np.mean(dh)
    # illustration: 20:E10 retired 2026-10-15 (T05)
    check("C5", "additive −i d/du + V_comb has a uniform spectrum: spacing std 0.08 (0.11 of its mean) against 0.39 of the mean for the heights",
          abs(np.std(da) - 0.08) < 0.01 and cv_add < 0.15 and abs(cv_h - 0.39) < 0.02,
          f"additive: std {np.std(da):.3f} on mean spacing {np.mean(da):.3f} (ratio {cv_add:.3f}); heights: std {np.std(dh):.2f} on mean {np.mean(dh):.2f} (ratio {cv_h:.3f}) — the paper's 0.08 is the absolute std, its 0.39 the ratio", kind="[approx]")
    # ---- figures
    fig, ax = plt.subplots(1, 2, figsize=(12, 3.8))
    ax[0].plot(gs, sig, color="#10325f", lw=1.0)
    for h in HEIGHTS[:6]: ax[0].axvline(h, color="#c0392b", ls="--", lw=0.8)
    ax[0].plot(top, [sig[np.argmin(np.abs(gs - t))] for t in top], "o", color="#e67e22")
    ax[0].set_xlabel(r"$\gamma$"); ax[0].set_ylabel(r"$|\Sigma_N(\gamma)|$"); ax[0].set_title(f"C1: scale-spectrum of the comb, N = 10⁶ (peaks vs heights)")
    g2 = np.arange(13.0, 15.3, 0.002); sharp = {}
    for Ndepth, col in [(10 ** 4, "#9ec5e8"), (10 ** 5, "#5b9bd5"), (10 ** 6, "#10325f")]:
        c = comb if Ndepth == N else Comb(Ndepth)
        sharp[Ndepth] = (col, c.sigma(g2) / c.sigma(HEIGHTS[0]))
        ax[1].plot(g2, sharp[Ndepth][1], color=col, lw=1.1, label=f"N = 10^{int(math.log10(Ndepth))}")
    ax[1].axvline(HEIGHTS[0], color="#c0392b", ls="--", lw=0.8); ax[1].set_xlabel(r"$\gamma$"); ax[1].legend(fontsize=8)
    ax[1].set_title(r"peak at $\gamma_1$ sharpens with depth, width $\sim 2\pi/\log N$")
    plt.tight_layout(); plt.savefig(f"{FIGDIR}/fig_prime_spectrum.pdf", bbox_inches="tight"); plt.savefig(f"{FIGDIR}/fig_prime_spectrum.png", dpi=110, bbox_inches="tight"); plt.close()
    print(f"    wrote {FIGDIR}/fig_prime_spectrum.pdf")
    # the paper's Figure "the zero heights from the prime side": (a) the scale-spectrum with its peaks, (b) the peak at γ₁ sharpening
    def _primespec(fig, ax):
        a = ax[0]
        for h in HEIGHTS[:6]: a.axvline(h, color=RED, ls="--", lw=0.7)
        a.plot(gs, sig, color=NAVY, lw=0.9, label=r"$|\Sigma_N(\gamma)|$, $N=10^{6}$")
        a.plot(top, [sig[np.argmin(np.abs(gs - t))] for t in top], "o", color=ORANGE, ms=4, label="peaks, from the primes alone")
        a.plot([], [], color=RED, ls="--", lw=0.7, label=r"zero heights $\gamma_n$")
        a.set_xlim(10, 40); a.set_ylim(0, 10.2); a.set_xlabel(r"scale frequency $\gamma$"); a.set_ylabel("amplitude"); a.legend(loc="upper right"); panel_letter(a, "(a)")
        b = ax[1]
        for Ndepth, (col, curve) in sharp.items():
            b.plot(g2, curve, color=col, lw=1.1, label=rf"$N=10^{{{int(math.log10(Ndepth))}}}$")
        b.axvline(HEIGHTS[0], color=RED, ls="--", lw=0.7); b.set_xlim(13, 15.3); b.set_ylim(0, 1.32); b.set_xlabel(r"$\gamma$"); b.set_ylabel(r"amplitude at $\gamma_1$, normalised")
        b.legend(loc="upper left"); panel_letter(b, "(b)")
    paper_figure("fig_primespec", _primespec, 2.45)
    Tg = np.arange(11.0, 40.0, 0.02)
    NB = theta(Tg) / math.pi + 1.0; NC = count_raw(comb, Tg); NH = count_corrected(comb, Tg)
    fig, ax = plt.subplots(1, 3, figsize=(13.5, 4.2))
    ax[0].plot(Tg, NC, color="#10325f", lw=1.4, label=r"raw $\tilde{N}_N(T)=\theta/\pi+1+S_{\rm comb}$")
    ax[0].plot(Tg, NH, color="#1f6b4a", lw=1.0, ls="--", label=r"pole-corrected $\hat{N}_N(T)$")
    ax[0].plot(Tg, NB, color="#9ec5e8", lw=1.3, label=r"$\theta(T)/\pi+1$")
    for n in range(2, 9): ax[0].axhline(n - 0.5, color="#bbb", lw=0.6, ls=":")
    for g in HEIGHTS[:6]: ax[0].axvline(g, color="#c0392b", lw=0.8, ls="--", alpha=0.7)
    ax[0].set_xlim(11, 40); ax[0].set_ylim(1, 9); ax[0].set_xlabel("$T$"); ax[0].set_ylabel("raw comb count")
    ax[0].set_title(r"C2/C2b: secular condition, count $= n-\frac{1}{2}$ at the heights", fontsize=10); ax[0].legend(fontsize=8, loc="upper left")
    ax[1].vlines(HEIGHTS[:10], 0, 1, color="#c0392b", ls="--", lw=1.1, label="heights (markers)")
    ax[1].plot(eig520, 0.5 * np.ones_like(eig520), "o", color="#10325f", ms=7, label="colleague eigenvalues")
    ax[1].set_xlim(10, 52); ax[1].set_ylim(0, 1); ax[1].set_yticks([]); ax[1].set_xlabel(r"$\gamma$")
    ax[1].set_title(f"C3: colleague matrix (corrected), dim 520, mean err {conv[520]:.1e}", fontsize=10); ax[1].legend(fontsize=8, loc="lower center")
    axin = ax[1].inset_axes([0.10, 0.58, 0.42, 0.32]); axin.semilogy(list(conv), list(conv.values()), "o-", color="#1f6b4a", ms=3.5)
    axin.set_title("mean error vs dimension", fontsize=7); axin.tick_params(labelsize=6)
    ax[2].vlines(eva, 0.55, 0.95, color="#1f6b4a", lw=1.0); ax[2].vlines(HEIGHTS[(HEIGHTS > 10) & (HEIGHTS < 50)], 0.05, 0.45, color="#c0392b", lw=1.4)
    ax[2].set_xlim(10, 50); ax[2].set_ylim(0, 1); ax[2].set_yticks([0.25, 0.75]); ax[2].set_yticklabels(["heights", "dilation\n+ comb"], fontsize=8.5)
    ax[2].set_xlabel(r"$\gamma$"); ax[2].set_title("C5: additive injection is gauge-trivial", fontsize=10)
    plt.tight_layout(); plt.savefig(f"{FIGDIR}/fig_operator_spectrum.pdf", bbox_inches="tight"); plt.savefig(f"{FIGDIR}/fig_operator_spectrum.png", dpi=110, bbox_inches="tight"); plt.close()
    print(f"    wrote {FIGDIR}/fig_operator_spectrum.pdf")
    return comb

# ======================================================================================================================
# block C, continued — c_gue.py (until 24 September 2026), its former docstring:
# c_gue.py — block C, continued: random-matrix statistics of the target spectrum ([approx])
# =========================================================================================
# The zero heights read as the target spectrum of the scale-evolution operator (Definition
# specmap: ρ ↦ −i(ρ − ½)). The heights here are computed independently with mpmath's zetazero
# and serve as the validation markers of Numerical Observation gue; no construction of the
# package takes them as input. Paper-local predicates:
#
#   C6  Obs. gue   [approx]  unfolded spacings of the first 240 zeros show GUE level repulsion, not
#                            Poisson: P(s < ½) = 0.05 (GUE ≈ 0.12, Poisson ≈ 0.39), variance 0.13
#                            (GUE ≈ 0.18, Poisson 1)
#   C6b Fig. hp    [chart]   the eigenvalue count N(T) lies on the Berry–Keating semiclassical
#                            (T/2π)(log(T/2π) − 1) + 7/8: density (1/2π) log p at T = 2πp, the shell
#                            scale-depth (Proposition density, block B)
#
# Figure: fig_hilbert_polya.pdf.

def unfold(g):
    """Smooth counting function N̄(γ) = (γ/2π) log(γ/2πe) + 7/8: unfolded ordinates with unit mean spacing."""
    return g / (2 * math.pi) * np.log(g / (2 * math.pi * math.e)) + 7.0 / 8.0

def gue_wigner(s):
    return 32 / math.pi ** 2 * s ** 2 * np.exp(-4 * s ** 2 / math.pi)

def _C_gue():
    print("\n== block C (continued): GUE level repulsion of the target spectrum (Obs. gue) ==")
    n = 240 if not FAST else 120
    with Timer(f"first {n} zeros (mpmath zetazero)"):
        g = riemann_zeros(n)
    u = unfold(g)
    s = np.diff(u); s = s / s.mean()
    p_half = float(np.mean(s < 0.5)); var = float(np.var(s))
    # reference values of the two ensembles (Wigner surmise for GUE; exponential for Poisson)
    from scipy.integrate import quad
    gue_half = quad(gue_wigner, 0, 0.5)[0]; gue_var = 3 * math.pi / 8 - 1
    poi_half = 1 - math.exp(-0.5); poi_var = 1.0
    tol = 0.02 if not FAST else 0.04
    ok = abs(p_half - 0.05) < tol and abs(var - 0.13) < 0.03 and p_half < 0.5 * poi_half and var < 0.5 * poi_var
    # illustration: 20:E11 retired 2026-10-15 (T05)
    check("C6", "unfolded spacings of the first 240 zeros: P(s<½) ≈ 0.05, variance ≈ 0.13 (repulsion; far from Poisson)", ok,
          f"P(s<½) = {p_half:.3f} (GUE {gue_half:.3f}, Poisson {poi_half:.3f}); var = {var:.3f} (GUE {gue_var:.3f}, Poisson 1)", kind="[approx]")
    # C6b: the count against Berry–Keating
    Ts = np.linspace(10, g[-1], 200)
    Ncount = np.searchsorted(g, Ts)
    Nsemi = Ts / (2 * math.pi) * (np.log(Ts / (2 * math.pi)) - 1) + 7.0 / 8.0
    dev = np.abs(Ncount - Nsemi)
    # illustration: 20:E3 retired 2026-10-15 (T05)
    check("C6b", "eigenvalue count N(T) within 1.5 of the Berry–Keating smooth count on [10, γ_240]", dev.max() < 1.5,
          f"max |N − N̄| = {dev.max():.2f}; mean = {dev.mean():.2f}", kind="[chart]")
    # figure
    fig, ax = plt.subplots(1, 2, figsize=(13, 4.4))
    A = ax[0]
    A.hist(s, bins=np.linspace(0, 3, 16), density=True, color="#1f5fbf", alpha=0.55, edgecolor="white", label=f"ζ zeros (first {n})")
    xx = np.linspace(0, 3, 400)
    A.plot(xx, gue_wigner(xx), color="#16a085", lw=2.2, label="GUE (Wigner surmise)")
    A.plot(xx, np.exp(-xx), color="#1a1a1a", lw=1.4, ls="--", label="Poisson")
    A.set_xlabel("normalised spacing $s$"); A.set_ylabel("$P(s)$"); A.set_xlim(0, 3)
    A.set_title(f"C6: level repulsion — $P(s<\\frac{{1}}{{2}})={p_half:.2f}$, var $={var:.2f}$", fontsize=10); A.legend(fontsize=8.5)
    B = ax[1]
    B.step(np.concatenate([[10], g]), np.arange(n + 1), where="post", color="#1f5fbf", lw=1.4, label=r"$N(T)=\#\{\gamma_k\leq T\}$")
    B.plot(Ts, Nsemi, color="#c0392b", lw=2.0, ls="--", label=r"Berry–Keating $\frac{T}{2\pi}(\log\frac{T}{2\pi}-1)+\frac{7}{8}$")
    B.set_xlabel(r"$T$ ($=2\pi p$ at shell scale $p$)"); B.set_ylabel("$N(T)$"); B.set_xlim(10, g[-1])
    B.set_title(r"C6b: density $\frac{1}{2\pi}\log\frac{T}{2\pi}=\frac{1}{2\pi}\log p$, the shell scale-depth", fontsize=10)
    B.legend(fontsize=8.5, loc="upper left")
    plt.tight_layout(); plt.savefig(f"{FIGDIR}/fig_hilbert_polya.pdf", bbox_inches="tight"); plt.savefig(f"{FIGDIR}/fig_hilbert_polya.png", dpi=110, bbox_inches="tight"); plt.close()
    print(f"    wrote {FIGDIR}/fig_hilbert_polya.pdf")

# ======================================================================================================================
# block C, continued — c_chi.py (until 24 September 2026), its former docstring:
# c_chi.py — block C, continued: the χ-twisted comb and the generalized hypothesis ([approx])
# ==========================================================================================
# Definition chi states that the construction goes through verbatim for a real (quadratic)
# character; Numerical Observation chi supports it for χ_{−4} (conductor 4, odd, root number 1).
# Two arms:
#
#   * the construction arm — the twisted secular condition N_χ(T) = θ_χ(T)/π + S^χ_comb(T), with
#     θ_χ(t) = Im log Γ(¾ + it/2) + (t/2) log(4/π) and the χ-weighted tapered comb Λ_χ(n) = χ(n)Λ(n),
#     with no pole term; L never evaluated;
#   * the validation arm — L(s, χ_{−4}) = 4^{−s}[ζ(s, ¼) − ζ(s, ¾)] via Hurwitz zeta (mpmath), its
#     completed form real on the line, its zeros located as sign changes.
#
# Paper-local predicates:
#
#   C7a Obs. chi  [approx]  N_χ evaluated at the first six zeros of L(s, χ_{−4}) (validation arm) reads
#                           0.4997, 1.4998, 2.4999, 3.4999, 4.4999, 5.4998
#   C7b Obs. chi  [approx]  solving the twisted secular condition with the N = 10⁶ comb recovers the six
#                           heights 6.0209, 10.2438, 12.9881, 16.3426, 18.2920, 21.4506 to mean error
#                           8.6×10⁻⁵ (the floor of the untwisted case, Obs. trace)
#   C7c Obs. chi  [approx]  the complex character χ mod 5 with χ(2) = i (odd, conductor 5): the half-phase
#                           W(χ)^{−1/2} Λ(½ + it, χ) is real on the line (validation arm, Hurwitz zeta); the
#                           twisted count (1/π)[θ_χ(T) − θ_χ(0)] + (1/π) Im[Σ^χ_w(½+iT) − Σ^χ_w(½)], with
#                           θ_χ(t) = Im log Γ(¾ + it/2) + (t/2) log(5/π) and no pole term, reads the exact
#                           integers 1 … 14 midway between the fifteen zeros below 40; its half-integer
#                           crossings, bracketed by the count alone, recover the fifteen heights with the
#                           N = 10⁶ comb to mean error 8.0×10⁻⁵ (max 2.0×10⁻⁴), L never evaluated (ledger E16)

HEIGHTS_CHI_STATED = [6.0209, 10.2438, 12.9881, 16.3426, 18.2920, 21.4506]
NCHI_STATED = [0.4997, 1.4998, 2.4999, 3.4999, 4.4999, 5.4998]

def chi4(n):
    """χ_{−4}(n): 0 on even n, +1 on n ≡ 1, −1 on n ≡ 3 (mod 4)."""
    n = np.asarray(n)
    return np.where(n % 2 == 0, 0.0, np.where(n % 4 == 1, 1.0, -1.0))

def twisted_support(N):
    """(n, χ(n)Λ(n)) on the prime powers ≤ N with χ(n) ≠ 0."""
    n, lam = von_mangoldt_support(N)
    c = chi4(n.astype(np.int64))
    keep = c != 0
    return n[keep], (c * lam)[keep]

def theta_chi(T):
    T = np.asarray(T, float)
    return np.imag(loggamma(0.75 + 0.5j * T)) + 0.5 * T * math.log(4 / math.pi)

def Lambda_chi_line(t):
    """Completed Λ(½ + it, χ_{−4}) = (4/π)^{(s+1)/2} Γ((s+1)/2) L(s, χ); real for this character (root number 1)."""
    s = mp.mpf(1) / 2 + mp.mpc(0, 1) * t
    L = mp.power(4, -s) * (mp.zeta(s, mp.mpf(1) / 4) - mp.zeta(s, mp.mpf(3) / 4))
    return mp.power(4 / mp.pi, (s + 1) / 2) * mp.gamma((s + 1) / 2) * L

def _C_chi():
    mp.mp.dps = 20
    print("\n== block C (continued): the χ-twisted comb, χ = χ_{−4} (Def. chi, Obs. chi) ==")
    # validation arm: the completed L is real on the line; its first six zeros by sign change + refinement
    with Timer("Hurwitz-zeta validation arm"):
        ts = np.arange(1.0, 23.0, 0.01)
        vals = [Lambda_chi_line(float(t)) for t in ts]
        im_max = max(abs(mp.im(v)) for v in vals)
        re = np.array([float(mp.re(v)) for v in vals])
        idx = np.nonzero(re[:-1] * re[1:] < 0)[0]
        zeros = np.array([brentq(lambda t: float(mp.re(Lambda_chi_line(t))), ts[i], ts[i + 1], xtol=1e-10) for i in idx])[:6]
    ok_real = im_max < 1e-15
    # construction arm
    N = 10 ** 6
    with Timer(f"twisted comb to {N}"):
        comb = Comb(N, lam_fn=twisted_support)
    nchi = count_raw(comb, zeros, const=0.0, theta_fn=theta_chi)
    ok = ok_real and len(zeros) == 6 and np.max(np.abs(zeros - HEIGHTS_CHI_STATED)) < 6e-5 and np.max(np.abs(nchi - NCHI_STATED)) < 6e-5
    # illustration: 20:E14, 20:E15 retired 2026-10-15 (T05)
    check("C7a", "N_χ at the first six zeros of L(s, χ_{−4}) reads 0.4997 … 5.4998 (completed L real on the line)", ok,
          "zeros " + ", ".join(f"{z:.4f}" for z in zeros) + "; N_χ " + ", ".join(f"{v:.4f}" for v in nchi) + f"; max|Im Λ| = {float(im_max):.1e}", kind="[approx]")
    # construction arm: the brackets come from the twisted count itself (its half-integer crossings on [3, 23]); the
    # reference zeros of the validation arm enter only in the error reported
    roots, levels, extra = secular_roots_scan(comb, 3.0, 23.0, const=0.0, theta_fn=theta_chi)
    assert levels == [k + 0.5 for k in range(6)] and not extra, f"crossings {levels}, extra {extra}"
    err = np.abs(roots - zeros)
    check("C7b", "twisted secular condition, N = 10⁶ comb, L never evaluated: six heights to mean error 8.6e-5", abs(err.mean() - 8.6e-5) < 1.5e-5,
          "roots " + ", ".join(f"{r:.4f}" for r in roots) + f"; mean error {err.mean():.2e}, max {err.max():.2e}", kind="[approx]")
    _C_chi_complex()

# ----------------------------------------------------------------------------- C7c: the complex character mod 5
CHI5 = np.array([0, 1, 1j, -1j, -1], dtype=complex)        # χ(n) by n mod 5: χ(1)=1, χ(2)=i, χ(3)=−i, χ(4)=−1
MP_CHI5 = {1: mp.mpc(1), 2: mp.mpc(0, 1), 3: mp.mpc(0, -1), 4: mp.mpc(-1)}

class ComplexTwistedComb:
    """The χ-weighted tapered comb for a complex character: Σ^χ_w(½ + iT) = Σ_{n≤N} χ(n)Λ(n) w(n) n^{−½−iT}/log n, and
    S(T) = (1/π) Im[Σ^χ_w(½+iT) − Σ^χ_w(½)] — the comb side of the twisted count, the difference from height 0
    removing the constant of the complex case (Obs. chi). Exposes N and S(T) so that the scan of the shared primitives applies."""
    def __init__(self, N, chi_table):
        self.N = int(N)
        n, lam = von_mangoldt_support(self.N)
        logn = np.log(n); L = math.log(self.N)
        w = 0.5 * (1.0 + np.cos(np.pi * logn / L))
        self.logn = logn
        self.coef = lam * w / (np.sqrt(n) * logn) * chi_table[(n % len(chi_table)).astype(int)]
        self.sigma0 = np.sum(self.coef)
    def sigma_w(self, T):
        T = np.atleast_1d(np.asarray(T, float))
        out = np.empty(len(T), dtype=complex)
        for s in range(0, len(T), 64):
            blk = T[s:s + 64]
            out[s:s + 64] = (self.coef[:, None] * np.exp(-1j * np.outer(self.logn, blk))).sum(0)
        return out
    def S(self, T):
        T = np.atleast_1d(np.asarray(T, float))
        val = (self.sigma_w(T) - self.sigma0).imag / math.pi
        return val if val.size > 1 else float(val[0])

def theta_chi5(T):
    T = np.asarray(T, float)
    return np.imag(loggamma(0.75 + 0.5j * T)) + 0.5 * T * math.log(5 / math.pi)

def theta_chi5_from0(T):
    return theta_chi5(T) - theta_chi5(0.0)

def L_chi5(s):
    return mp.power(5, -s) * sum(MP_CHI5[a] * mp.zeta(s, mp.mpf(a) / 5) for a in (1, 2, 3, 4))

def Z_chi5_factory():
    """Z_χ(t) = W(χ)^{−1/2} Λ(½ + it, χ) with Λ(s, χ) = (5/π)^{(s+1)/2} Γ((s+1)/2) L(s, χ) and W(χ) = τ(χ)/(i√5): real on the line."""
    I = mp.mpc(0, 1)
    tau = sum(MP_CHI5[a] * mp.expjpi(mp.mpf(2 * a) / 5) for a in (1, 2, 3, 4))
    W = tau / (I * mp.sqrt(5)); Whalf = mp.sqrt(W)
    def Z(t):
        s = mp.mpf(1) / 2 + I * t
        return mp.power(5 / mp.pi, (s + 1) / 2) * mp.gamma((s + 1) / 2) * L_chi5(s) / Whalf
    return Z, W

def _C_chi_complex():
    print("\n== block C (continued): the complex character χ mod 5, χ(2) = i (Def. chi, Obs. chi; ledger E16) ==")
    with Timer("Hurwitz-zeta validation arm, χ mod 5"):
        Z, W = Z_chi5_factory()
        ts = np.arange(0.0, 40.0, 0.02)
        zv = [Z(float(t)) for t in ts]
        im_max = float(max(abs(mp.im(z)) for z in zv))
        re = np.array([float(mp.re(z)) for z in zv])
        idx = np.nonzero(re[:-1] * re[1:] < 0)[0]
        zeros = np.array([brentq(lambda t: float(mp.re(Z(t))), ts[i], ts[i + 1], xtol=1e-10) for i in idx])
    N = 10 ** 6
    with Timer(f"complex twisted comb to {N}"):
        comb = ComplexTwistedComb(N, CHI5)
    mids = 0.5 * (zeros[1:] + zeros[:-1])
    cnt = count_raw(comb, mids, const=0.0, theta_fn=theta_chi5_from0)
    ok_count = len(zeros) == 15 and np.max(np.abs(cnt - np.arange(1, len(zeros)))) < 0.05
    ok_real = abs(float(abs(W)) - 1.0) < 1e-15 and im_max < 1e-15
    # the brackets come from the twisted count itself; the validation arm's zeros enter only in the error reported
    roots, levels, extra = secular_roots_scan(comb, 2.0, 40.0, const=0.0, theta_fn=theta_chi5_from0)
    assert levels == [k + 0.5 for k in range(15)] and not extra, f"crossings {levels}, extra {extra}"
    err = np.abs(roots - zeros)
    # illustration: 20:E16 retired 2026-10-15 (T05)
    check("C7c", "χ mod 5 complex: Z_χ real on the line; the twisted count reads 1 … 14 between the fifteen zeros below 40; "
          "the secular condition (N = 10⁶ comb, brackets from the count alone, L never evaluated) recovers the fifteen heights to mean error 8.0e-5 (max 2.0e-4)",
          ok_real and ok_count and abs(err.mean() - 8.0e-5) < 1.5e-5 and err.max() < 2.5e-4,
          f"|W| = {float(abs(W)):.15f}, max|Im Z_χ| = {im_max:.1e}; {len(zeros)} zeros {zeros[0]:.4f} … {zeros[-1]:.4f}; count at midpoints "
          + ", ".join(f"{c:.3f}" for c in cnt) + "; roots " + ", ".join(f"{r:.4f}" for r in roots[:3]) + f" … {roots[-1]:.4f}; mean error {err.mean():.2e}, max {err.max():.2e}",
          kind="[approx]")

def block_C():
    """Block C — the spectrum from the prime side with ζ never evaluated (the scale-spectrum, the secular condition raw and pole-corrected to depth 10⁸, the colleague and Jacobi matrices, the additive injection), the GUE statistics of the target spectrum, the χ-twisted comb for χ₋₄ and for the complex character mod 5; 12 checks ([approx], [chart])."""
    _C_primeside(); _C_gue(); _C_chi()

# ======================================================================================================================
# block D — d_classification.py (until 24 September 2026), its former docstring:
# d_classification.py — block D: the classification and the Euler-product discriminator (00:D12)
# =============================================================================================
# Proposition turing: C(T) ≤ N_crit(T) ≤ N(T); RH below T is N = N_crit; C = N is Turing's practical
# certificate; the shell reads N from the comb (raw count, uncertified) and C from the de-framing
# (sign changes of the main sum). Definition screen: the classical hypothesis is read as the screen
# value N − N_crit = 0. Numerical Observation dh: the value is discriminating — the Davenport–
# Heilbronn function f (no Euler product) opens a phantom deficit of 2 at its first off-line pair
# while its constituent L(s, χ) closes with deficit 0; on the comb side the secular condition
# lands two "on-line" roots on the phantom height and the raw count near it does not settle with
# depth; the ζ comb behaves the same way at ζ's own singularity to the right of the line, the pole.
#
# Paper-local predicates:
#
#   D1  Prop. turing / Def. screen     [approx]  at T = 15, 30, 50.3 the raw comb count Ñ_N rounds to the exact
#                                                 N = 1, 3, 10, and the sign changes of the horizon main sum Z_M on
#                                                 (0, T) — the de-framing side — give C = 1, 3, 10 = N (Turing's
#                                                 certificate read on the shell, both readings uncertified)
#   D2a Obs. dh  [approx]  Λ_f(½ + it) is real to 10⁻²⁰ (self-dual normalisation of the DH function)
#   D2b Obs. dh  [approx]  argument principle per band on [0, 87]: N_f = 45 strip zeros against C_f = 43 on-line sign
#                          changes, the deficit 2 opening only in the band holding the off-line pair
#                          s = 0.8085171825 + 85.6993484854 i (validated |f(s)| < 10⁻⁶); |Z_f| dips to 0.357 at
#                          t = 85.71 without crossing; positive control L(s, χ): 45 = 45, deficit 0 in every band
#   D2c Obs. dh  [approx]  negative control: the secular condition on the Λ_f comb returns two "on-line" roots in
#                          [84, 87], 85.63 / 85.76 (comb to 10⁵) and 85.65 / 85.75 (4×10⁵), at the phantom height —
#                          the upward crossings of the levels 43.5 and 44.5 between the exact counts 43 and 45.
#                          (Package finding: at 4×10⁵ the unsettled count also swings below 42.5 and above 45.5 in
#                          [85.3, 86.1], adding two crossing pairs the paper's sentence does not mention; at 10⁵ the
#                          excursion stays within (42.5, 45.5) and the two roots are the only crossings.)
#   D2d Obs. dh  [approx]  the raw DH comb count at t = 85.9 drifts monotonically with depth, 45.14 → 45.73 over
#                          5×10⁴ … 8×10⁵ (exact 45); at 85.3 it reads 42.66 … 42.73 (exact 43; the paper's two figures
#                          are the endpoint depths, the interior depths dip to 42.64); away from the pair it is
#                          stable: 28.005 ± 0.002 at 60.3 and 43.00 ± 0.01 at 84.0
#   D2e Obs. dh  [approx]  the ζ comb at the pole: at t = 1 (exact 0) the raw count reads +0.09, −0.26, +0.36, −0.08,
#                          −0.81, −1.42, −1.46 at depths 10⁴ … 8×10⁷; at t = 5 within ±0.02; at t = 10 within ±0.003;
#                          at t = 15 within 2×10⁻³ of 1 at every depth; at t = 30 from 3.04 to 2.998; at 50.3 within
#                          10⁻² of 10 (depths to 8×10⁵)
#   D2f Prop. combformula, Obs. dh  [approx]  the pole-corrected ζ count N̂_N at t = 1 reads 0.0051, 0.0032, 0.0022, 0.0016, 0.0015,
#                          0.0013, 0.0012 at the same depths (exact 0), falling monotonically; at t = 5 and 10 within 4×10⁻⁴ from
#                          10⁶ on, falling in magnitude; at 15, 30, 50.3 the correction is below 10⁻³ and raw and corrected agree
#   D2g Rem. combsettle, Obs. dh    [approx]  the DH drift is the zero term of the off-line zero ρ₀: the count corrected by it and its constant reads
#                          44.960, 44.964, 44.967, 44.970, 44.972 at t = 85.9 (raw 45.14 … 45.73; exact 45) and 43.035 → 43.022
#                          at 85.3 (raw 42.66 … 42.73; exact 43), both monotone toward the exact count
#   D3  Prop. combformula  [approx]  the identity's validation arm: the corrected tapered sum Σ_w − Π_N − log((s−1)/s) against
#                          log ζ(½ + it) (mpmath) at t = 1, 5, 10, 15, 30: the real-part error falls with depth at every height
#                          (0.0049 at t = 1, depth 8×10⁷) and the imaginary part is the corrected count of D2f
#   D4  Prop. turing (frame-exact inputs)  [approx]  on the shells p = 97, 1009, 4801 (primes ≡ 1 mod 4; ceilings T = 2πp ≈ 609, 6340,
#                          30166) the raw count from the frame-exact comb of depth ⌊√p⌋ = 9, 31, 69, evaluated midway between
#                          consecutive zeros just below the ceiling (the test heights chosen with the validation arm: zeros from
#                          Z(t) sign changes, the count from mpmath nzeros), rounds to the exact N(t) at every midpoint: maximum
#                          deviation 0.079, 0.107, 0.164 (within 0.08, 0.11, 0.17); the 10⁶ comb within 0.002
#
# The "ζ never evaluated" discipline does not bind the control arms (Hurwitz zeta functions are
# evaluated there). Figure: fig_dh.pdf. Master ledger: 00:D12.

mp.mp.dps = 20
I = mp.mpc(0, 1)
CHI = {1: mp.mpc(1), 2: I, 3: -I, 4: mp.mpc(-1)}                 # complex character mod 5, χ(2) = i
KAPPA = (mp.sqrt(10 - 2 * mp.sqrt(5)) - 2) / (mp.sqrt(5) - 1)
TAU = sum(CHI[a] * mp.expjpi(mp.mpf(2 * a) / 5) for a in (1, 2, 3, 4))
EPS_HALF = mp.sqrt(TAU / (I * mp.sqrt(5)))                       # half-phase of the root number of χ
RHO_OFF = mp.mpc("0.8085171825", "85.6993484854")               # Titchmarsh: the first off-line pair, with 1 − s̄
T_HI = 87.0
DEPTHS_DH = [50_000, 100_000, 200_000, 400_000, 800_000]
DEPTHS_Z = [10 ** 4, 10 ** 5, 10 ** 6, 10 ** 7, 2 * 10 ** 7, 4 * 10 ** 7, 8 * 10 ** 7] if not FAST else [10 ** 4, 10 ** 5, 10 ** 6, 10 ** 7]
STATED_T1 = [0.09, -0.26, 0.36, -0.08, -0.81, -1.42, -1.46]

# ------------------------------------------------------------------ the validation arm: f and L(s, χ) via Hurwitz zeta
def L_pair(s):
    z = {a: mp.zeta(s, mp.mpf(a) / 5) for a in (1, 2, 3, 4)}
    five = mp.power(5, -s)
    return five * sum(CHI[a] * z[a] for a in (1, 2, 3, 4)), five * sum(mp.conj(CHI[a]) * z[a] for a in (1, 2, 3, 4))

def pair_values(s):
    """(L(s,χ), f(s)) with f = (1 − iκ)/2 L(s,χ) + (1 + iκ)/2 L(s,χ̄)."""
    Lchi, Lbar = L_pair(s)
    return Lchi, (1 - I * KAPPA) / 2 * Lchi + (1 + I * KAPPA) / 2 * Lbar

def gamma_factor(s):
    return mp.power(5 / mp.pi, (s + 1) / 2) * mp.gamma((s + 1) / 2)

def hardy_pair(t):
    """Hardy-normalised on-line readouts (Z_χ(t), Z_f(t)), both real: |Z| = |value on the line|."""
    s = mp.mpf(1) / 2 + I * t
    g = gamma_factor(s); ph = g / abs(g)
    Lchi, f = pair_values(s)
    return ph * Lchi / EPS_HALF, ph * f

def theta_f(t):
    """Twisted archimedean phase of the conductor-5 odd Γ-factor: Im log Γ(¾ + it/2) + (t/2) log(5/π)."""
    t = np.asarray(t, float)
    return np.imag(loggamma(0.75 + 0.5j * t)) + 0.5 * t * math.log(5 / math.pi)

def sign_changes(ts, vals):
    pos = []
    for k in range(1, len(ts)):
        a, b = vals[k - 1], vals[k]
        if a * b < 0:
            pos.append(ts[k - 1] + (ts[k] - ts[k - 1]) * a / (a - b))
    return np.array(pos)

def winding(fn_values, corners, step):
    """Winding numbers of several functions around a rectangle, by continuous phase tracking with
    adaptive refinement; fn_values(s) returns a tuple of complex values (one per function)."""
    (s0, s1, s2, s3) = corners
    sides = [(s0, s1), (s1, s2), (s2, s3), (s3, s0)]
    total = None
    for a, b in sides:
        n = max(2, int(abs(b - a) / step) + 1)
        pts = [a + (b - a) * k / (n - 1) for k in range(n)]
        vals = [fn_values(s) for s in pts]
        m = len(vals[0])
        acc = np.zeros(m)
        stack = list(zip(pts[:-1], pts[1:], vals[:-1], vals[1:], [0] * (n - 1)))
        while stack:
            pa, pb, va, vb, depth = stack.pop()
            d = np.array([float(mp.arg(vb[i] / va[i])) for i in range(m)])
            if np.max(np.abs(d)) > 0.8 and depth < 12:
                pm = (pa + pb) / 2; vm = fn_values(pm)
                stack.append((pa, pm, va, vm, depth + 1)); stack.append((pm, pb, vm, vb, depth + 1))
            else:
                acc += d
        total = acc if total is None else total + acc
    w = total / (2 * math.pi)
    assert np.max(np.abs(w - np.round(w))) < 0.05, f"non-integer winding {w}"
    return np.round(w).astype(int)

# ------------------------------------------------------------------ the generalized von Mangoldt comb of f
def dh_lambda(M):
    """Λ_f(n) for n ≤ M from −f'/f = Σ Λ_f(n) n^{−s}, by the divisor recursion a_n log n = Σ_{d|n} Λ_f(d) a_{n/d}, a_1 = 1."""
    kappa = float(KAPPA)
    n = np.arange(M + 1)
    cvals = np.array([0, 1, 1j, -1j, -1], dtype=complex)[n % 5]
    a = ((1 - 1j * kappa) / 2 * cvals + (1 + 1j * kappa) / 2 * np.conj(cvals)).real
    logs = np.log(np.maximum(n, 1).astype(float))
    Lf = np.zeros(M + 1); conv = np.zeros(M + 1)
    for k in range(2, M + 1):
        Lf[k] = a[k] * logs[k] - conv[k]
        if Lf[k] != 0.0:
            ms = np.arange(2, M // k + 1)
            conv[k * ms] += Lf[k] * a[ms]
    return Lf

def comb_support_from(Lf):
    def lam_fn(N):
        idx = np.nonzero(Lf[:N + 1])[0]
        return idx.astype(float), Lf[idx]
    return lam_fn

def count_at_depths(n_all, lam_all, t, depths, theta_fn, const):
    """Raw comb count at height t for several depths from one support (taper log N per depth)."""
    logn = np.log(n_all); out = []
    for N in depths:
        m = n_all <= N
        w = 0.5 * (1 + np.cos(np.pi * logn[m] / math.log(N)))
        terms = lam_all[m] / (np.sqrt(n_all[m]) * logn[m]) * w * np.sin(t * logn[m])
        out.append(float(theta_fn(t)) / math.pi + const - math.fsum(terms) / math.pi)
    return np.array(out)

def corrected_at_depths(n_all, lam_all, t, depths):
    """Pole-corrected ζ count N̂_N(t) at several depths from one support (Prop. combformula)."""
    raw = count_at_depths(n_all, lam_all, t, depths, theta, 1.0)
    return raw - np.array([pole_count_term(N, t) for N in depths])

def zero_cut_term(N, t, rho0):
    """The zero term of one fixed zero ρ₀ = β₀ + iγ₀ to the right of the line (½ < β₀ < 3/2) at s = ½ + it
    (Remark combsettle): Π^{(ρ₀)}_N(s) = ∫_0^L W(u/L) (e^{(ρ₀−s)u} − e^{(ρ₀−1−s)u}) du/u, L = log N. The image of the
    regulariser h_{ρ₀}(w) = log((w−ρ₀)/(w−ρ₀+1)) under the window inversion of Prop. combformula (i) is −Π^{(ρ₀)}_N,
    the term the zero contributes to the smoothed sum. The routine evaluates this one integral at depth N and
    asserts nothing about a limit N → ∞: the paper does not extend the identity of Prop. combformula to a series
    with infinitely many zeros to the right of the line. The Davenport–Heilbronn correction
    N̂_{f,N} = Ñ_{f,N} + Im[Π^{(ρ₀)}_N(s) + h_{ρ₀}(s)]/π (dh_corrected_at_depths, D2g) is validated over the depths
    listed there."""
    L = math.log(N); a = rho0 - mp.mpc(0.5, t); b = a - 1
    f = lambda u: 0.5 * (1 + mp.cos(mp.pi * u / L)) * (mp.exp(a * u) - mp.exp(b * u)) / u
    return mp.quad(f, mp.linspace(0, L, 40))

def dh_corrected_at_depths(n_all, lam_all, t, depths):
    """The DH comb count corrected by the zero term of ρ₀ and its constant (D2g; Remark combsettle):
    N̂_{f,N} = Ñ_{f,N} + Im[Π^{(ρ₀)}_N(s) + h_{ρ₀}(s)]/π, with h_{ρ₀}(s) = −H0 below."""
    s = mp.mpc(0.5, t); H0 = mp.log((s - RHO_OFF + 1) / (s - RHO_OFF))
    raw = count_at_depths(n_all, lam_all, t, depths, theta_f, 0.0)
    return raw + np.array([float(mp.im(zero_cut_term(N, t, RHO_OFF) - H0)) / math.pi for N in depths])

def Z_main(t):
    """The horizon-length Riemann–Siegel main sum (Definition deframe), the de-framing side of Proposition turing."""
    N = int(math.floor(math.sqrt(t / (2 * math.pi))))
    th = float(theta(t))
    return 2 * sum(math.cos(th - t * math.log(n)) / math.sqrt(n) for n in range(1, N + 1))

def block_D():
    """Block D — Turing's count on the shell (T = 15, 30, 50.3 and the frame-exact combs of p = 97, 1009, 4801), the phantom of the Davenport–Heilbronn function on the line and on the comb side, the ζ comb at its pole raw and corrected, the smoothed explicit formula's validation arm; 10 checks ([approx])."""
    mp.mp.dps = 20
    print("\n== block D: the screen reading and its Davenport–Heilbronn control (Prop. turing, Def. screen, Obs. dh) ==")
    # ---------------- D1: the two readings on ζ
    comb = Comb(10 ** 6)
    Tq = np.array([15.0, 30.0, 50.3]); exact = [1, 3, 10]
    raw = count_raw(comb, Tq)
    tgrid = np.arange(0.5, 50.3, 0.02)
    zm = np.array([Z_main(t) for t in tgrid])
    Cm = [int(np.sum(zm[:-1][tgrid[:-1] < T] * zm[1:][tgrid[:-1] < T] < 0)) for T in Tq]
    ok = all(int(round(r)) == e for r, e in zip(raw, exact)) and Cm == exact
    # 20:F1 (p20047)
    check("D1", "Ñ_N rounds to N = 1, 3, 10 at T = 15, 30, 50.3; sign changes of the main sum Z_M give C = 1, 3, 10 = N", ok,
          "raw " + ", ".join(f"{r:.4f}" for r in raw) + f"; C_M = {Cm}", kind="[approx]")
    # ---------------- D2a: reality of Λ_f on the line
    with mp.workdps(30):
        im = max(abs(mp.im(gamma_factor(mp.mpf(1) / 2 + I * t) * pair_values(mp.mpf(1) / 2 + I * t)[1])) for t in np.linspace(0.7, 86.3, 25))
    # illustration: 20:F3 retired 2026-10-15 (T11)
    check("D2a", "the completed Λ_f(½ + it) is real on the line to 10⁻²⁰", im < 1e-20, f"max |Im Λ_f| = {float(im):.1e} over 25 heights", kind="[approx]")
    # ---------------- D2b: strip counts by the argument principle against on-line sign changes
    with Timer("on-line grid (Hurwitz zeta)"):
        dt = 0.02 if not FAST else 0.04
        ts = np.arange(0.1, T_HI + dt / 2, dt)
        Zc = np.empty_like(ts); Zf = np.empty_like(ts)
        for k, t in enumerate(ts):
            zc, zf = hardy_pair(mp.mpf(float(t)))
            assert abs(mp.im(zc)) < 1e-9 and abs(mp.im(zf)) < 1e-9
            Zc[k], Zf[k] = float(mp.re(zc)), float(mp.re(zf))
    zeros_f, zeros_c = sign_changes(ts, Zf), sign_changes(ts, Zc)
    off_err = abs(pair_values(RHO_OFF)[1])
    band = (ts > 85.0) & (ts < 86.5); k_dip = np.argmin(np.abs(Zf[band])); t_dip, z_dip = ts[band][k_dip], abs(Zf[band][k_dip])
    # band boundaries: multiples of 3, nudged away from every on-line zero of both functions
    allz = np.concatenate([zeros_f, zeros_c])
    bounds = [0.1]
    for b in np.arange(3.0, T_HI + 0.1, 3.0):
        while np.min(np.abs(allz - b)) < 0.15: b += 0.2
        bounds.append(min(b, T_HI))
    with Timer(f"argument principle on {len(bounds) - 1} bands (Hurwitz zeta)"):
        step = 0.05 if not FAST else 0.1
        Nf_band, Nc_band = [], []
        for lo, hi in zip(bounds[:-1], bounds[1:]):
            corners = (mp.mpc(-1.5, lo), mp.mpc(2.5, lo), mp.mpc(2.5, hi), mp.mpc(-1.5, hi))
            wc, wf = winding(pair_values, corners, step)
            Nc_band.append(wc); Nf_band.append(wf)
    Cf_band = [int(np.sum((zeros_f > lo) & (zeros_f < hi))) for lo, hi in zip(bounds[:-1], bounds[1:])]
    Cc_band = [int(np.sum((zeros_c > lo) & (zeros_c < hi))) for lo, hi in zip(bounds[:-1], bounds[1:])]
    deficit_f = np.array(Nf_band) - np.array(Cf_band); deficit_c = np.array(Nc_band) - np.array(Cc_band)
    kband = next(i for i, (lo, hi) in enumerate(zip(bounds[:-1], bounds[1:])) if lo < 85.6993 < hi)
    ok = (sum(Nf_band) == 45 and len(zeros_f) == 43 and sum(Nc_band) == 45 and len(zeros_c) == 45
          and deficit_f[kband] == 2 and all(d == 0 for i, d in enumerate(deficit_f) if i != kband) and all(d == 0 for d in deficit_c)
          and off_err < 1e-6 and abs(z_dip - 0.357) < 0.01 and abs(t_dip - 85.71) < 0.03)
    check("D2b", "argument principle on [0,87]: f: 45 strip zeros vs 43 on-line, deficit 2 only in the band of the off-line pair; L(s,χ): 45 = 45, deficit 0 everywhere", ok,
          f"f: N = {sum(Nf_band)}, C = {len(zeros_f)}, deficit by band {[int(d) for d in deficit_f]}; L(s,χ): N = {sum(Nc_band)}, C = {len(zeros_c)}; "
          f"|f(s_off)| = {float(off_err):.1e}; |Z_f| dips to {z_dip:.3f} at t = {t_dip:.2f}", kind="[approx]")
    # ---------------- D2c, D2d: the comb side of f
    with Timer("Λ_f comb to 8e5 (divisor recursion)"):
        Lf = dh_lambda(DEPTHS_DH[-1])
    lam_fn = comb_support_from(Lf)
    roots, extra, excursion = {}, {}, {}
    for M in (10 ** 5, 4 * 10 ** 5):
        c = Comb(M, lam_fn=lam_fn)
        tt = np.linspace(84, 87, 601); v = count_raw(c, tt, const=0.0, theta_fn=theta_f)
        cross = []                                   # every half-integer crossing (t, level, direction)
        for i in range(len(tt) - 1):
            lo, hi = v[i], v[i + 1]
            for h in np.arange(math.floor(min(lo, hi)) + 0.5, max(lo, hi), 1.0):
                if (lo - h) * (hi - h) < 0:
                    cross.append((brentq(lambda t: count_raw(c, t, const=0.0, theta_fn=theta_f) - h, tt[i], tt[i + 1]), h, np.sign(hi - lo)))
        # the phantom roots: the upward crossings of the two levels 43.5, 44.5 between the exact counts 43 (below the pair) and 45 (above)
        roots[M] = sorted(t for t, h, d in cross if h in (43.5, 44.5) and d > 0)
        extra[M] = sorted((round(t, 2), h) for t, h, d in cross if h not in (43.5, 44.5))
        excursion[M] = (v[(tt > 85) & (tt < 86.4)].min(), v[(tt > 85) & (tt < 86.4)].max())
    ok = (len(roots[10 ** 5]) == 2 and len(roots[4 * 10 ** 5]) == 2 and len(extra[10 ** 5]) == 0
          and np.allclose(roots[10 ** 5], [85.63, 85.76], atol=0.015) and np.allclose(roots[4 * 10 ** 5], [85.65, 85.75], atol=0.015))
    # illustration: 20:F4 retired 2026-10-15 (T11)
    check("D2c", "the secular condition on the Λ_f comb returns two 'on-line' roots at the phantom height: 85.63/85.76 (10⁵), 85.65/85.75 (4×10⁵)", ok,
          f"10⁵: {np.round(roots[10 ** 5], 3).tolist()} (no other crossing in [84,87]; count excursion {excursion[10 ** 5][0]:.2f}–{excursion[10 ** 5][1]:.2f}); "
          f"4×10⁵: {np.round(roots[4 * 10 ** 5], 3).tolist()}, plus the swing of the unsettled count through the levels {sorted(set(float(h) for _, h in extra[4 * 10 ** 5]))} "
          f"(excursion {excursion[4 * 10 ** 5][0]:.2f}–{excursion[4 * 10 ** 5][1]:.2f}; crossing pairs at {[t for t, _ in extra[4 * 10 ** 5]]})", kind="[approx]")
    idx = np.nonzero(Lf)[0]; nf, lf = idx.astype(float), Lf[idx]
    scan = {t: count_at_depths(nf, lf, t, DEPTHS_DH, theta_f, 0.0) for t in (85.9, 85.3, 60.3, 84.0)}
    s859 = scan[85.9]
    ok = (np.allclose(s859, [45.14, 45.27, 45.41, 45.57, 45.73], atol=0.015) and np.all(np.diff(s859) > 0)
          and abs(scan[85.3][0] - 42.66) < 0.006 and abs(scan[85.3][-1] - 42.73) < 0.006 and scan[85.3].min() > 42.63 and scan[85.3].max() < 42.74
          and np.all(np.abs(scan[60.3] - 28.005) < 0.003) and np.all(np.abs(scan[84.0] - 43.0) < 0.011))
    check("D2d", "raw DH comb count drifts monotonically at t = 85.9 (45.14 → 45.73) and reads 42.66 … 42.73 at 85.3 (interior depths dip to 42.64); stable at 60.3 (28.005 ± 0.002) and 84.0 (43.00 ± 0.01)", ok,
          "; ".join(f"t={t}: " + ", ".join(f"{v:.3f}" for v in vals) for t, vals in scan.items()), kind="[approx]")
    # ---------------- D2e: the ζ comb at the pole
    with Timer(f"ζ comb support to {DEPTHS_Z[-1]:.0e}"):
        n_all, lam_all = von_mangoldt_support(DEPTHS_Z[-1])
    z1 = count_at_depths(n_all, lam_all, 1.0, DEPTHS_Z, theta, 1.0)
    z5 = count_at_depths(n_all, lam_all, 5.0, DEPTHS_Z, theta, 1.0)
    z10 = count_at_depths(n_all, lam_all, 10.0, DEPTHS_Z, theta, 1.0)
    z15 = count_at_depths(n_all, lam_all, 15.0, DEPTHS_Z, theta, 1.0)
    z30 = count_at_depths(n_all, lam_all, 30.0, DEPTHS_Z, theta, 1.0)
    z503 = count_at_depths(n_all, lam_all, 50.3, [d for d in DEPTHS_Z if d <= 8 * 10 ** 5] + [8 * 10 ** 5], theta, 1.0)
    k = len(DEPTHS_Z)
    ok = (np.allclose(z1, STATED_T1[:k], atol=0.015) and np.all(np.abs(z5) < 0.021) and np.all(np.abs(z10) < 0.0031)
          and np.all(np.abs(z15 - 1) < 2e-3) and abs(z30[0] - 3.04) < 0.006 and abs(z30[-1] - (2.998 if not FAST else z30[-1])) < 0.002
          and np.all(np.abs(z503 - 10) < 1e-2))
    # illustration: 20:F5 retired 2026-10-15 (T11)
    check("D2e", "ζ comb at the pole: t = 1 reads +0.09, −0.26, +0.36, −0.08, −0.81, −1.42, −1.46 with depth (exact 0); t = 5, 10 within ±0.02, ±0.003; t = 15 within 2e-3 of 1; t = 30 3.04 → 2.998; t = 50.3 within 1e-2 of 10", ok,
          "t=1: " + ", ".join(f"{v:+.2f}" for v in z1) + "; t=5: max|·| " + f"{np.max(np.abs(z5)):.3f}" + "; t=10: " + f"{np.max(np.abs(z10)):.4f}"
          + "; t=15: max dev " + f"{np.max(np.abs(z15 - 1)):.1e}" + f"; t=30: {z30[0]:.3f} → {z30[-1]:.3f}; t=50.3: max dev {np.max(np.abs(z503 - 10)):.1e}", kind="[approx]")
    # ---------------- D2f: the pole-corrected ζ count settles (Prop. combformula)
    c1 = corrected_at_depths(n_all, lam_all, 1.0, DEPTHS_Z); c5 = corrected_at_depths(n_all, lam_all, 5.0, DEPTHS_Z); c10 = corrected_at_depths(n_all, lam_all, 10.0, DEPTHS_Z)
    stated_c1 = [0.0051, 0.0032, 0.0022, 0.0016, 0.0015, 0.0013, 0.0012][:k]
    i6 = DEPTHS_Z.index(10 ** 6)
    ok = (np.allclose(c1, stated_c1, atol=0.0003) and np.all(np.diff(c1) < 0) and np.all(np.abs(c5[i6:]) < 4e-4) and np.all(np.abs(c10[i6:]) < 4e-4)
          and np.all(np.diff(np.abs(c5)) < 0) and np.all(np.diff(np.abs(c10)) < 0))
    # illustration: 20:F8 retired 2026-10-15 (T11)
    check("D2f", "pole-corrected ζ count at t = 1: 0.0051, 0.0032, 0.0022, 0.0016, 0.0015, 0.0013, 0.0012 (exact 0), monotone; t = 5, 10 within 4e-4 from 10⁶ on, falling", ok,
          "t=1: " + ", ".join(f"{v:+.4f}" for v in c1) + "; t=5: " + ", ".join(f"{v:+.5f}" for v in c5) + "; t=10: " + ", ".join(f"{v:+.5f}" for v in c10), kind="[approx]")
    # ---------------- D2g: the DH drift is the zero term of the off-line zero (Remark combsettle)
    with Timer("DH corrected counts"):
        d859 = dh_corrected_at_depths(nf, lf, 85.9, DEPTHS_DH); d853 = dh_corrected_at_depths(nf, lf, 85.3, DEPTHS_DH)
    ok = (np.allclose(d859, [44.960, 44.964, 44.967, 44.970, 44.972], atol=0.002) and np.all(np.diff(d859) > 0)
          and np.allclose(d853, [43.035, 43.031, 43.028, 43.025, 43.022], atol=0.002) and np.all(np.diff(d853) < 0))
    check("D2g", "DH count corrected by the zero term of ρ₀ and its constant: 44.960 → 44.972 at 85.9 (raw 45.14 → 45.73; exact 45), 43.035 → 43.022 at 85.3 (exact 43), monotone toward the exact count", ok,
          "t=85.9: " + ", ".join(f"{v:.4f}" for v in d859) + "; t=85.3: " + ", ".join(f"{v:.4f}" for v in d853), kind="[approx]")
    # ---------------- D3: the identity against log ζ (validation arm: mpmath)
    logn_all = np.log(n_all); re_err = {}
    for t, Nc in ((1.0, 0), (5.0, 0), (10.0, 0), (15.0, 1), (30.0, 3)):
        sc = mp.mpc(0.5, t); lz_re = float(mp.log(abs(mp.zeta(sc))))
        errs = []
        for N in DEPTHS_Z:
            m = n_all <= N; L = math.log(N); w = 0.5 * (1 + np.cos(np.pi * logn_all[m] / L))
            S = np.sum(lam_all[m] * w / (np.sqrt(n_all[m]) * logn_all[m]) * np.exp(-1j * t * logn_all[m]))
            errs.append(abs((S - pole_term(N, t) - complex(mp.log((sc - 1) / sc))).real - lz_re))
        re_err[t] = np.array(errs)
    ok = all(np.all(np.diff(e) < 0) for e in re_err.values()) and re_err[1.0][-1] < (0.0052 if not FAST else 0.0065)
    check("D3", "the identity's validation arm: Re(Σ_w − Π_N − log((s−1)/s)) → log|ζ(½+it)| at t = 1, 5, 10, 15, 30, the error falling with depth (0.0049 at t = 1, 8×10⁷)", ok,
          "; ".join(f"t={t}: " + " → ".join(f"{v:.4f}" for v in (e[0], e[len(e)//2], e[-1])) for t, e in re_err.items()), kind="[approx]")
    # ---------------- D4: the count from the frame-exact comb on one shell (Proposition turing)
    with Timer("frame-exact shells"):
        shells = [97, 1009] + ([4801] if not FAST else [])          # primes ≡ 1 (mod 4): admissible Subject shells
        dev_fe, dev_deep, dev_smooth, npts = {}, {}, {}, {}
        deep = Comb(10 ** 6)
        for p_sh in shells:
            Tc = 2 * math.pi * p_sh; depth = int(math.floor(math.sqrt(p_sh)))
            grid = np.arange(Tc - 12.0, Tc + 1e-9, 0.1); zv = np.array([float(mp.siegelz(t)) for t in grid])
            zs = np.array([brentq(lambda t: float(mp.siegelz(t)), grid[i], grid[i + 1], xtol=1e-7)
                           for i in range(len(grid) - 1) if zv[i] * zv[i + 1] < 0])
            mids = 0.5 * (zs[1:] + zs[:-1]); nz = np.array([int(mp.nzeros(t)) for t in mids]); npts[p_sh] = len(mids)
            v = count_raw(Comb(depth), mids); vd = count_raw(deep, mids)
            vs = np.array([float(theta(t)) / math.pi + 1 for t in mids])       # the control: the smooth term alone
            dev_fe[p_sh] = (float(np.max(np.abs(v - nz))), bool(np.all(np.round(v) == nz)))
            dev_deep[p_sh] = (float(np.max(np.abs(vd - nz))), bool(np.all(np.round(vd) == nz)))
            dev_smooth[p_sh] = (float(np.max(np.abs(vs - nz))), bool(np.all(np.round(vs) == nz)))
    stated = {97: 0.079, 1009: 0.107, 4801: 0.164}
    stated_smooth = {97: (0.268, True), 1009: (0.498, True), 4801: (0.523, False)}
    ok = (all(r for _, r in dev_fe.values()) and all(r for _, r in dev_deep.values())
          and all(abs(dev_fe[p_sh][0] - stated[p_sh]) < 0.02 for p_sh in shells) and max(d for d, _ in dev_deep.values()) < 0.004
          and all(abs(dev_smooth[p_sh][0] - stated_smooth[p_sh][0]) < 0.02 and dev_smooth[p_sh][1] == stated_smooth[p_sh][1] for p_sh in shells))
    check("D4", "frame-exact count on one shell: at p = 97, 1009, 4801 (T = 2πp) the depth-⌊√p⌋ comb, midway between consecutive zeros below the ceiling, rounds to the exact N(t) at every midpoint (max deviation 0.079, 0.107, 0.164 — within 0.08, 0.11, 0.17); the 10⁶ comb within 0.002; the control θ(t)/π + 1 alone deviates by 0.27, 0.498, 0.52 and fails to round at one midpoint of p = 4801", ok,
          "; ".join(f"p={p_sh} (depth {int(math.sqrt(p_sh))}, {npts[p_sh]} midpoints): max dev {dev_fe[p_sh][0]:.3f} (10⁶ comb {dev_deep[p_sh][0]:.3f}; smooth term alone {dev_smooth[p_sh][0]:.3f}, rounds {dev_smooth[p_sh][1]})" for p_sh in shells), kind="[approx]")
    # ---------------- figure
    with Timer("window grid [84,87]"):
        tw = np.arange(84.0, 87.0 + 1e-9, 0.005 if not FAST else 0.01)
        Zcw = np.empty_like(tw); Zfw = np.empty_like(tw)
        for j, t in enumerate(tw):
            zc, zf = hardy_pair(mp.mpf(float(t))); Zcw[j], Zfw[j] = float(mp.re(zc)), float(mp.re(zf))
    crimson, gray = "#c8102e", "0.40"
    fig, ax = plt.subplots(1, 3, figsize=(16, 4.3), gridspec_kw={"width_ratios": [1.15, 1.0, 1.0]})
    ax[0].axhline(0, color="0.65", lw=0.8)
    ax[0].plot(tw, Zcw, color=gray, lw=1.6, label=r"$Z_\chi(t)$: constituent $L(s,\chi)$ (crosses)")
    ax[0].plot(tw, Zfw, color=crimson, lw=2.0, label=r"$Z_f(t)$: Davenport–Heilbronn (dips, no crossing)")
    ax[0].axvline(float(mp.im(RHO_OFF)), color=crimson, lw=1.0, ls=":")
    ax[0].set_xlim(84, 87); ax[0].set_ylim(-7.2, 1.7); ax[0].set_xlabel("$t$"); ax[0].set_ylabel("rotated on-line value")
    ax[0].set_title(f"D2b: the phantom on the line — dip {z_dip:.3f} at t = {t_dip:.2f}", fontsize=10); ax[0].legend(loc="lower left", fontsize=8)
    # staircases: strip count from the band windings, on-line count from the sign changes
    xs_on = np.concatenate([[0], np.sort(zeros_f), [T_HI]]); ys_on = np.concatenate([[0], np.arange(1, len(zeros_f) + 1), [len(zeros_f)]])
    # strip count: on-line zeros plus the band excess placed at the off-line height
    jumps = sorted([(z, 1) for z in zeros_f] + [(float(mp.im(RHO_OFF)), int(deficit_f[kband]))])
    xs_s, ys_s, c = [0.0], [0], 0
    for z, j in jumps: xs_s.append(z); c += j; ys_s.append(c)
    xs_s.append(T_HI); ys_s.append(c)
    ax[1].step(xs_s, ys_s, where="post", color=crimson, lw=1.9, label=r"$N_f(t)$: strip count (argument principle by band)")
    ax[1].step(xs_on, ys_on, where="post", color=gray, lw=1.4, ls="--", label=r"$N_{\rm crit}(t)$: on-line sign changes")
    ax[1].axvline(float(mp.im(RHO_OFF)), color=crimson, lw=1.0, ls=":")
    ax[1].set_xlim(0, T_HI); ax[1].set_ylim(0, 47.5); ax[1].set_xlabel("$t$"); ax[1].set_ylabel("cumulative zero count")
    ax[1].set_title(f"deficit on [0,87]: $N_f={sum(Nf_band)}$, $C={len(zeros_f)}$; control $L(s,\\chi)$: {sum(Nc_band)}={len(zeros_c)}", fontsize=10)
    ax[1].legend(loc="upper left", fontsize=8)
    axins = ax[1].inset_axes([0.60, 0.08, 0.38, 0.40])
    axins.step(xs_s, ys_s, where="post", color=crimson, lw=1.9); axins.step(xs_on, ys_on, where="post", color=gray, lw=1.4, ls="--")
    axins.set_xlim(84, 87); axins.set_ylim(40, 46.5); axins.tick_params(labelsize=7); axins.set_title(r"$N_f-N_{\rm crit}=2$", fontsize=8)
    # depth drift
    ax[2].semilogx(DEPTHS_DH, scan[85.9], "o-", color=crimson, label="DH comb, t = 85.9 (exact 45)")
    ax[2].semilogx(DEPTHS_DH, scan[84.0], "s-", color="#e59866", label="DH comb, t = 84.0 (exact 43)")
    ax[2].axhline(45, color=crimson, lw=0.8, ls=":"); ax[2].axhline(43, color="#e59866", lw=0.8, ls=":")
    ax2 = ax[2].twinx()
    ax2.semilogx(DEPTHS_Z, z1, "^-", color="#10325f", label="ζ comb, t = 1 (exact 0)")
    ax2.semilogx(DEPTHS_Z, c1, "^--", color="#1f6b4a", label="ζ comb, t = 1, pole-corrected")
    ax2.semilogx(DEPTHS_Z, z15, "v-", color="#5b9bd5", label="ζ comb, t = 15 (exact 1)")
    ax2.axhline(0, color="#10325f", lw=0.8, ls=":"); ax2.axhline(1, color="#5b9bd5", lw=0.8, ls=":")
    ax[2].set_xlabel("comb depth $N$"); ax[2].set_ylabel("raw DH count", color=crimson); ax2.set_ylabel("raw ζ count", color="#10325f")
    ax[2].set_title("D2d–D2f: the raw count near a singularity, and the pole-corrected count", fontsize=10)
    h1, l1 = ax[2].get_legend_handles_labels(); h2, l2 = ax2.get_legend_handles_labels(); ax[2].legend(h1 + h2, l1 + l2, fontsize=7.5, loc="upper center", bbox_to_anchor=(0.5, -0.17), ncol=2)
    plt.tight_layout(); plt.savefig(f"{FIGDIR}/fig_dh.pdf", bbox_inches="tight"); plt.savefig(f"{FIGDIR}/fig_dh.png", dpi=110, bbox_inches="tight"); plt.close()
    print(f"    wrote {FIGDIR}/fig_dh.pdf")
    # the paper's Figure "the Euler-product discriminator": (a) the phantom on the line, (b) the deficit staircase with its inset;
    # the depth panel above stays a diagnostic of the package
    toff = float(mp.im(RHO_OFF))
    def _dh(fig, ax):
        a = ax[0]; a.axhline(0, color="0.75", lw=0.6)
        a.plot(tw, Zcw, color=GRAY, lw=1.2, label=r"$Z_\chi(t)$, the constituent $L(s,\chi)$")
        a.plot(tw, Zfw, color=CRIMSON, lw=1.5, label=r"$Z_f(t)$, Davenport–Heilbronn")
        a.axvline(toff, color=CRIMSON, lw=0.8, ls=":")
        a.text(toff + 0.06, 2.05, "off-line pair at $t=85.70$", fontsize=7.5, color=CRIMSON, ha="left", va="top")
        a.set_xlim(84, 87); a.set_ylim(-7.2, 2.4); a.set_xlabel("$t$"); a.set_ylabel("rotated on-line value"); a.legend(loc="lower right"); panel_letter(a, "(a)")
        b = ax[1]
        b.step(xs_s, ys_s, where="post", color=CRIMSON, lw=1.4, label=r"$N_f(t)$, strip count")
        b.step(xs_on, ys_on, where="post", color=GRAY, lw=1.0, ls="--", label=r"$N_{\mathrm{crit}}(t)$, on-line count")
        b.axvline(toff, color=CRIMSON, lw=0.8, ls=":")
        b.set_xlim(0, T_HI); b.set_ylim(0, 47.5); b.set_xlabel("$t$"); b.set_ylabel("cumulative zero count"); b.legend(loc="upper left"); panel_letter(b, "(b)")
        axins = b.inset_axes([0.56, 0.08, 0.41, 0.35])
        axins.step(xs_s, ys_s, where="post", color=CRIMSON, lw=1.4); axins.step(xs_on, ys_on, where="post", color=GRAY, lw=1.0, ls="--")
        axins.fill_between([toff, T_HI], [43, 43], [45, 45], color=CRIMSON, alpha=0.12, step="post")
        axins.set_xlim(84, 87); axins.set_ylim(41, 46.6); axins.set_xticks([84, 85, 86, 87]); axins.set_yticks([42, 44, 46]); axins.tick_params(labelsize=6.5, length=2)
        axins.text(84.12, 45.15, r"$N_f-N_{\mathrm{crit}}=2$", fontsize=7, color=CRIMSON, ha="left", va="bottom")
    paper_figure("fig_dh", _dh, 2.55)

    # ---------------- D6: the strip (Thm. strip, row D8) and the finite negative control (row D9); 13 October 2026
    # D6a the Davenport–Heilbronn zero off the line and its Klein-four orbit: f(ρ) = 0 at ρ = 0.808517182457 + 85.6993484854 i
    # (A8), f(1 − ρ) = 0 and f(ρ̄) = 0 (the functional equation and the reality of the coefficients), 0 < Re ρ < 1, Re ρ ≠ ½;
    # for ζ the strip is a theorem (Mathlib, Thm. strip): ζ(s) ≠ 0 for Re s ≥ 1, checked here at four points as a sanity reading
    mp.mp.dps = 20
    rho = mp.mpc("0.808517182457", "85.6993484854")
    vals = [abs(pair_values(s)[1]) for s in (rho, 1 - rho, mp.conj(rho))]
    zeta_right = [abs(mp.zeta(s)) for s in (mp.mpf(1) + 20j, mp.mpf(2), mp.mpc(1, 85.7), mp.mpc(1.5, 1000))]
    ok = all(v < mp.mpf(10) ** -9 for v in vals) and 0 < rho.real < 1 and abs(rho.real - mp.mpf(1) / 2) > 0.3 and all(z > 0.1 for z in zeta_right)
    # 20:D8 (p20080)
    check("D6a", "the strip: the DH zero ρ = 0.8085 + 85.699 i has 0 < Re ρ < 1 off the line, with f(1 − ρ) = f(ρ̄) = 0 (the Klein-four orbit); ζ ≠ 0 on four points with Re s ≥ 1", ok,
          f"|f| at ρ, 1−ρ, ρ̄ = {[float(v) for v in vals]}; |ζ| on Re s ≥ 1: min {float(min(zeta_right)):.3f}", kind="[approx]")
    # D6b the DH prime vector: Λ_f from the divisor recursion is supported outside the prime powers, and a(n) is not multiplicative
    Lf = dh_lambda(40)
    supp = [n for n in range(2, 41) if abs(Lf[n]) > 1e-12]
    pp = {n for n in range(2, 41) if len(prime_factors(n)) == 1}
    outside = [n for n in supp if n not in pp]
    kappa = float(KAPPA); a = lambda n: [0, 1, kappa, -kappa, -1][n % 5]
    ok = outside[:8] == [6, 12, 14, 18, 21, 24, 26, 28] and abs(a(6) - a(2) * a(3)) > 1.0 and abs(a(6) - 1) < 1e-15
    check("D6b", "the DH prime vector Λ_f from the divisor recursion is supported outside the prime powers (6, 12, 14, 18, 21, 24, 26, 28, …), and a(n) is not multiplicative: a(6) = 1 against a(2)a(3) = −κ²", ok,
          f"support outside prime powers below 40: {outside}; a(6) = {a(6):.3f}, a(2)a(3) = {a(2) * a(3):.3f}", kind="[approx]")
    # D6c the finite negative control (Thm. negative_control13, row D9): over F_13(√2), P(X) = ((X − 2)² − 2)((X + 1)² − 2) has exactly the
    # roots 2 ± η and −1 ± η, traces 4, 4, 11, 11 against the line's 1 (Tr z = 1 ⟺ Re z = 2⁻¹ = 7), the root set closed under conjugation and
    # under X ↦ 1 − X: finitude, conjugation and the reflection force no root onto the line
    p13, nu13 = 13, 2
    E = [(a_, b_) for a_ in range(p13) for b_ in range(p13)]
    add = lambda z, w: ((z[0] + w[0]) % p13, (z[1] + w[1]) % p13)
    sub = lambda z, w: ((z[0] - w[0]) % p13, (z[1] - w[1]) % p13)
    sq = lambda z: mul(z, z, nu13, p13)
    P = lambda z: mul(sub(sq(sub(z, (2, 0))), (2, 0)), sub(sq(add(z, (1, 0))), (2, 0)), nu13, p13)
    roots = sorted(z for z in E if P(z) == (0, 0))
    expected = sorted([(2, 1), (2, 12), (12, 1), (12, 12)])
    traces = [trace(z, p13) for z in roots]
    line = [z for z in E if trace(z, p13) == 1]
    conj_closed = all(((z[0], (-z[1]) % p13) in roots) for z in roots)
    half_turn_closed = all((((1 - z[0]) % p13, (-z[1]) % p13) in roots) for z in roots)   # 1 − z = (1 − a) − bη
    ok = roots == expected and traces == [4, 4, 11, 11] and all(z[0] == 7 for z in line) and len(line) == 13 and conj_closed and half_turn_closed \
         and all((x * x) % p13 != nu13 for x in range(1, p13))
    # 20:D9 (p20083)
    check("D6c", "the finite negative control over F_13(√2): ((X−2)²−2)((X+1)²−2) has exactly the roots 2 ± η, −1 ± η, traces 4, 4, 11, 11 against the line's 1, the root set closed under conjugation and under X ↦ 1 − X; none on the line", ok,
          f"roots {roots}, traces {traces}, the line Re z = 7 ({len(line)} points)")
    # ---------------- D7: the cells of the cycle (Def./Prop. cells, row D5); 13 October 2026
    # on Ω = 13 and 233 the cycle's Ω cells [2πy, 2π(y+1)): N_y the zeros of ζ in the cell (the argument principle, mpmath nzeros), C_y
    # the sign changes of Z on the cell (the Riemann–Siegel formula with the first remainder term, a grid refined where a change is close);
    # C_y ≤ N_y on every cell; every cell clean (C_y = N_y) and the totals agree, N(2πΩ) = Σ N_y = 21, 1038; about log y zeros per cell
    def Z_rs(t):
        t = np.asarray(t, float); a = np.sqrt(t / (2 * np.pi)); N = np.floor(a).astype(int); pfrac = a - N
        th = np.imag(loggamma(0.25 + 0.5j * t)) - 0.5 * t * np.log(np.pi)
        main = np.zeros_like(t)
        for n in range(1, int(N.max()) + 1):
            m = N >= n
            main[m] += 2 * np.cos(th[m] - t[m] * np.log(n)) / np.sqrt(n)
        psi = np.cos(2 * np.pi * (pfrac * pfrac - pfrac - 1 / 16)) / np.cos(2 * np.pi * pfrac)
        return main + (-1) ** (N - 1) * a ** -0.5 * psi
    for Om in (13, 233):
        counts = [int(mp.nzeros(2 * mp.pi * (y + 1))) - int(mp.nzeros(2 * mp.pi * y)) for y in range(Om)]
        changes = []
        for y in range(Om):
            lo, hi = 2 * math.pi * y, 2 * math.pi * (y + 1)
            ts = np.linspace(lo, hi, 400 if y > 0 else 400); zs = Z_rs(ts) if y > 0 else None
            if y == 0:                                   # the first cell holds no zero (the first ordinate is 14.13 > 2π)
                changes.append(0); continue
            sc = int(np.sum(zs[:-1] * zs[1:] < 0))
            if sc < counts[y]:                            # refine the grid where a close pair may hide
                ts = np.linspace(lo, hi, 4000); zs = Z_rs(ts); sc = int(np.sum(zs[:-1] * zs[1:] < 0))
            changes.append(sc)
        total = int(mp.nzeros(2 * mp.pi * Om))
        ok = all(c <= n for c, n in zip(changes, counts)) and changes == counts and sum(counts) == total and total == {13: 21, 233: 1038}[Om]
        tail = counts[-10:]
        # 20:D5 (p20029)
        check(f"D7{'a' if Om == 13 else 'b'}", f"the cells of the cycle on Ω = {Om}: N_y from the argument principle, C_y from the sign changes of Z on each cell; C_y ≤ N_y and C_y = N_y on all {Om} cells, Σ N_y = N(2πΩ) = {total}", ok,
              f"zeros per cell: max {max(counts)}, last ten {tail} against log y ≈ {math.log(Om):.2f}; empty cells {sum(1 for c in counts if c == 0)}", kind="[approx]")

# ======================================================================================================================
# block E — e_resonance.py (until 24 September 2026), its former docstring:
# e_resonance.py — block E: resonance, antipode, horizon-scale resolution, square-root cancellation
# =================================================================================================
# The units-chart side of the construction: Ramanujan sums c_q(n) as the standing waves of the
# additive meridian, the Möbius-weighted resonance R_L(n) = Σ_{q≤L} μ(q)/φ(q) c_q(n), its limit the
# von Mangoldt weight (Theorem resonance), the energy at the antipode (Obs. antipode), the resolving
# band at the Subject horizon (Obs. horizon), and the 1/√p flatness of every single multiplicative-
# chart mode against the prime indicator (Prop. flat, Obs. flat). Paper-local predicates:
#
#   E1a Thm. resonance (b)  EXACT     Λ = μ ∗ log on the divisor lattice: −Σ_{d|n} μ(d) log d = log ℓ on prime powers
#                                     ℓ^k, 0 otherwise — verified symbolically (sympy) for n ≤ 300, in floating point
#                                     for n ≤ 5000
#   E1b Thm. resonance (a),(c) [approx]  Hardy: R_L(n) → (φ(n)/n) Λ(n) (Cesàro mean to L = 4000, prime powers ≤ 13:
#                                     within 0.02, and nearer that limit than Λ(n)); the intertwiner (n/φ(n)) R → Λ
#   E1c Def. resonance / Fig. emergence [approx]  Ψ_L(N) = Σ_{n≤N} (n/φ(n)) R_L(n) → ψ(N): the maximal deviation on
#                                     N ≤ 30 falls monotonically over L = 15, 60, 240
#   E2a Obs. antipode  EXACT     per-mode energy μ²(q)/φ(q) on squarefree q: 1, ½, ¼, ⅙ at q = 2, 3, 5, 7, with its
#                                     unique maximum among the nonconstant modes at the antipode q = 2 (all 2 ≤ q ≤ 2000; q = 1 ties)
#   E2b Obs. antipode  [approx]  the additive-transform band energy of the prime indicator on Z/10007, Parseval-
#                                     normalised over the bins within three of each a/q, peaks at the antipode and
#                                     follows 1/φ(q): 1153 > 592 > 301 > 205 at q = 2, 3, 5, 7 (the paper's figures,
#                                     restated on 2026-09-13 from the unnormalised 1220 > 640 > 323 > 214)
#   E3  Obs. horizon   [approx]  the resolving threshold L*(H) — the least bandwidth at which R_L separates every prime
#                                     power in {2..H} from every non-prime-power — exists for H = 6..50 and tracks the
#                                     horizon, L* < 6H, far below the field scale H²
#   E4  Obs. flat      [approx]  the maximal correlation of the prime indicator with a multiplicative-chart mode χ_j
#                                     is a small multiple of the 1/√(p−2) floor of Prop. flat: 0.077 against 0.0315 at
#                                     p = 1009 (2.4×); 0.0087 against 0.0032 over the modes of p = 100049 (2.7×); by
#                                     contrast the units-chart resonance correlates 0.90 with the primes in its window
#
# Figures: fig_obstruction.pdf (E3, E4), fig_emergence_frc.pdf (E1c beside the classical reconstruction of ψ from zeros).

# ------------------------------------------------------------------ arithmetic tables
def sieve_mu_phi(M):
    mu = np.ones(M + 1, dtype=int); phi = np.arange(M + 1); comp = np.zeros(M + 1, dtype=bool); primes = []
    mu[0] = 0
    for i in range(2, M + 1):
        if not comp[i]:
            primes.append(i); mu[i] = -1; phi[i] = i - 1
        for q in primes:
            if i * q > M: break
            comp[i * q] = True
            if i % q == 0:
                mu[i * q] = 0; phi[i * q] = phi[i] * q; break
            mu[i * q] = -mu[i]; phi[i * q] = phi[i] * (q - 1)
    return mu, phi

def divisors(n):
    return [d for d in range(1, n + 1) if n % d == 0]

def ramanujan(q, n, mu):
    """Kluyver: c_q(n) = Σ_{d | gcd(q,n)} d μ(q/d), an integer."""
    g = gcd(q, n)
    return sum(d * mu[q // d] for d in divisors(g))

def resonance_table(Qmax, Nmax, mu, phi):
    """cum[L, n] = R_L(n) = Σ_{q≤L} μ(q)/φ(q) c_q(n), L = 0..Qmax, n = 0..Nmax."""
    C = np.zeros((Qmax + 1, Nmax + 1))
    for q in range(1, Qmax + 1):
        for n in range(1, Nmax + 1):
            C[q, n] = ramanujan(q, n, mu)
    w = np.array([0.0] + [mu[q] / phi[q] for q in range(1, Qmax + 1)])
    return np.cumsum(w[:, None] * C, axis=0)

def von_mangoldt_array(N):
    n, lam = von_mangoldt_support(N)
    out = np.zeros(N + 1); out[n.astype(int)] = lam
    return out

def dlog_table(p):
    g = int(sp.primitive_root(p)); lam = np.zeros(p, dtype=np.int64); x = 1
    for k in range(p - 1):
        lam[x] = k; x = (x * g) % p
    return lam

def chart_mode_correlations(p):
    """|corr(1_Π, χ_j)| for every nontrivial multiplicative-chart mode χ_j(n) = ω^{j λ_p(n)} on F_p^×, by FFT
    over the discrete logarithm; returns (max, the exact root-mean-square 1/√(p−2) of Prop. flat, the array)."""
    lam = dlog_table(p)
    ind = np.zeros(p); ind[sieve_primes(p - 1)] = 1.0
    u = np.zeros(p - 1); u[lam[1:]] = ind[1:]                # u[m] = 1_Π(g^m)
    u = u - u.mean()
    F = np.fft.fft(u)
    corr = np.abs(F[1:]) / (np.linalg.norm(u) * math.sqrt(p - 1))
    return float(corr.max()), 1 / math.sqrt(p - 2), corr

def pearson(a, b):
    a = a - a.mean(); b = b - b.mean()
    return float(a @ b / (np.linalg.norm(a) * np.linalg.norm(b)))

def block_E():
    """Block E — the units-chart resonance and the von Mangoldt weight, the staircase from the modes, the antipode, the resolving band at the horizon, the √p-flatness of the chart modes; 7 checks (EXACT, [approx])."""
    mp.mp.dps = 20
    print("\n== block E: resonance, antipode, horizon, square-root cancellation ==")
    Qmax, Nmax = 320, 60
    mu, phi = sieve_mu_phi(max(Qmax, 5000))
    with Timer("resonance table"):
        cum = resonance_table(Qmax, Nmax, mu, phi)
    Lam = von_mangoldt_array(5000)
    # ---------------- E1a: Λ = μ * log, exact
    sym_ok = True
    for n in range(2, 301):
        expr = sp.expand_log(-sum(sp.Integer(int(mu[d])) * sp.log(d) for d in divisors(n) if d > 1), force=True)
        f = sp.factorint(n)
        target = sp.log(list(f)[0]) if len(f) == 1 else sp.Integer(0)
        if sp.simplify(expr - target) != 0:
            sym_ok = False; break
    flt = np.array([-sum(mu[d] * math.log(d) for d in divisors(n) if d > 1) for n in range(2, 5001)])
    flt_ok = np.max(np.abs(flt - Lam[2:5001])) < 1e-9
    # illustration: 20:C2 retired 2026-10-15 (T11)
    check("E1a", "Λ = μ ∗ log: −Σ_{d|n} μ(d) log d = Λ(n), symbolic for n ≤ 300, floating point for n ≤ 5000", sym_ok and flt_ok,
          f"symbolic {'ok' if sym_ok else 'FAIL'}; max float deviation {np.max(np.abs(flt - Lam[2:5001])):.1e}", kind="EXACT")
    # ---------------- E1b: Hardy's limit and the intertwiner (Cesàro mean over L ≤ 4000, conditional convergence)
    Qhi = 4000 if not FAST else 1500
    with Timer(f"Cesàro resonance to L = {Qhi}"):
        cumhi = resonance_table(Qhi, 14, mu, phi)
    pps = [2, 3, 4, 5, 7, 8, 9, 11, 13]; comp = [6, 10, 12, 14]
    R = {n: float(cumhi[1:Qhi + 1, n].mean()) for n in pps + comp}
    hardy = all(abs(R[n] - phi[n] / n * Lam[n]) < 0.02 and abs(R[n] - phi[n] / n * Lam[n]) < abs(R[n] - Lam[n]) for n in pps)
    zero_ok = all(abs(R[n]) < 0.02 for n in comp)
    inter = all(abs(n / phi[n] * R[n] - Lam[n]) < 0.03 for n in pps)
    check("E1b", "Hardy: R_L(n) → (φ(n)/n) Λ(n) on prime powers, → 0 off them; intertwiner (n/φ(n)) R → Λ = log ℓ", hardy and zero_ok and inter,
          f"R(2) = {R[2]:.4f} vs ½ log 2 = {0.5 * Lam[2]:.4f}; R(9) = {R[9]:.4f} vs ⅔ log 3 = {2 / 3 * Lam[9]:.4f}; (13/12) R(13) = {13 / 12 * R[13]:.4f} vs log 13 = {Lam[13]:.4f}; max |R| off prime powers {max(abs(R[n]) for n in comp):.3f}", kind="[approx]")
    # ---------------- E1c: the staircase from the modes
    ns = np.arange(2, 31); psi = np.cumsum(Lam[2:31])
    def Psi(L): return np.cumsum([n / phi[n] * cum[L, n] for n in ns])
    devs = [float(np.max(np.abs(Psi(L) - psi))) for L in (15, 60, 240)]
    # illustration: 20:C3 retired 2026-10-15 (T05)
    check("E1c", "Ψ_L(N) → ψ(N) on N ≤ 30: maximal deviation falls monotonically over L = 15, 60, 240", devs[0] > devs[1] > devs[2],
          "max |Ψ_L − ψ| = " + ", ".join(f"{d:.3f}" for d in devs), kind="[approx]")
    # ---------------- E2a: the per-mode energy, exact
    E = {q: Fraction(int(mu[q] ** 2), int(phi[q])) for q in range(2, 2001)}
    ok = (E[2], E[3], E[5], E[7]) == (Fraction(1), Fraction(1, 2), Fraction(1, 4), Fraction(1, 6)) and all(E[q] < 1 for q in E if q != 2)
    # illustration: 20:B11 retired 2026-10-15 (T05)
    check("E2a", "per-mode energy μ²(q)/φ(q) = 1, ½, ¼, ⅙ at q = 2, 3, 5, 7; unique maximum among the nonconstant modes at the antipode q = 2 (2 ≤ q ≤ 2000)", ok,
          "energies " + ", ".join(f"q={q}: {E[q]}" for q in (2, 3, 5, 7, 11)), kind="EXACT")
    # ---------------- E2b: the additive-transform band energy (reported against the paper's figures, not pinned)
    p4 = 10007
    ind = np.zeros(p4); ind[sieve_primes(p4 - 1)] = 1.0
    F = np.fft.fft(ind); norm2 = float(ind @ ind)
    band = {}
    for q in (2, 3, 5, 7):
        e = 0.0
        for a in range(1, q):
            if gcd(a, q) == 1:
                kc = a * p4 / q
                e += sum(abs(F[k % p4]) ** 2 for k in range(int(math.floor(kc)) - 3, int(math.ceil(kc)) + 4))
        band[q] = e / norm2
    law = [band[q] * phi[q] / band[2] for q in (3, 5, 7)]
    stated = {2: 1153, 3: 592, 5: 301, 7: 205}
    ok = band[2] > band[3] > band[5] > band[7] and all(abs(band[q] - stated[q]) < 2 for q in stated) and all(0.85 < r < 1.25 for r in law)
    check("E2b", "additive-transform band energy of the prime indicator on Z/10007 (Parseval-normalised, bins within 3 of a/q): 1153 > 592 > 301 > 205, the law 1/φ(q)", ok,
          " > ".join(f"q={q}: {band[q]:.0f}" for q in (2, 3, 5, 7)) + f"; φ(q)·E_q/E_2 = " + ", ".join(f"{r:.2f}" for r in law), kind="[approx]")
    # ---------------- E3: the resolving threshold
    Hs = list(range(6, 51, 2)); Ls = []
    for H in Hs:
        pp = [n for n in range(2, H + 1) if Lam[n] > 0]; npp = [n for n in range(2, H + 1) if Lam[n] == 0]
        Lstar = next((L for L in range(2, Qmax + 1) if min(cum[L, n] for n in pp) > max(abs(cum[L, n]) for n in npp)), None)
        Ls.append(Lstar)
    ok = all(L is not None for L in Ls) and all(L < 6 * H for L, H in zip(Ls, Hs)) and all(L < H * H for L, H in zip(Ls, Hs) if H >= 8)
    ratio = [L / H for L, H in zip(Ls, Hs)]
    # illustration: 20:C4 retired 2026-10-15 (T05)
    check("E3", "resolving threshold L*(H) exists for H = 6..50 and tracks the horizon: L* < 6H ≪ H²", ok,
          f"L*/H in [{min(ratio):.2f}, {max(ratio):.2f}]; L*(12) = {Ls[Hs.index(12)]}, L*(20) = {Ls[Hs.index(20)]}, L*(50) = {Ls[-1]}", kind="[approx]")
    # ---------------- E4: square-root cancellation of every chart mode
    with Timer("chart-mode correlations"):
        m1, f1, corr1 = chart_mode_correlations(1009)
        p5 = int(sp.nextprime(100_000))
        while p5 % 4 != 1: p5 = int(sp.nextprime(p5))
        m5, f5, _ = chart_mode_correlations(p5)
    cum200 = resonance_table(80, 200, mu, phi)
    rn = np.arange(2, 201); res_corr = pearson(np.array([1.0 if sp.isprime(int(n)) else 0.0 for n in rn]), np.array([cum200[80, n] for n in rn]))
    ok = (abs(m1 - 0.077) < 0.005 and abs(f1 - 0.0315) < 0.0005 and abs(m1 / f1 - 2.43) < 0.03
          and abs(m5 - 0.0087) < 0.0005 and abs(f5 - 0.0032) < 0.0001 and abs(m5 / f5 - 2.75) < 0.03 and res_corr > 0.85)
    # illustration: 20:C6 retired 2026-10-15 (T05)
    check("E4", "max chart-mode correlation with the primes is a small multiple of the 1/√(p−2) floor: 0.077 vs 0.0315 (p = 1009, 2.4×), 0.0087 vs 0.0032 (p = 100049, 2.7×); resonance correlates 0.90", ok,
          f"p = 1009: max {m1:.4f}, floor {f1:.4f}, ratio {m1 / f1:.3f}; p = {p5}: max {m5:.4f} over {(p5 - 1) // 2} mode pairs, floor {f5:.4f}, ratio {m5 / f5:.3f}; corr(1_Π, R_80) on n ≤ 200 = {res_corr:.2f}", kind="[approx]")
    # ---------------- figures
    FIN, TEAL = "#3b34a8", "#1f9e8a"
    fig, ax = plt.subplots(1, 2, figsize=(12, 4.0))
    ax[0].plot(np.arange(1, len(corr1) // 2 + 1), corr1[:len(corr1) // 2], color=TEAL, lw=0.6)
    ax[0].axhline(f1, color="#888", ls="--", lw=1, label=r"floor $1/\sqrt{p-2}$")
    ax[0].axhline(res_corr, color=FIN, lw=1.8, label=f"units-chart resonance ({res_corr:.2f})")
    ax[0].set_ylim(0, 1); ax[0].set_xlabel("chart mode index $j$"); ax[0].set_ylabel(r"$|{\rm corr}(1_\Pi,\chi_j)|$")
    ax[0].set_title(f"E4: chart modes are blind to primality (p = 1009, max {m1:.3f})", fontsize=10); ax[0].legend(fontsize=8, loc="center right")
    ax[1].plot(Hs, Ls, "o-", color=FIN, lw=1.4, ms=4, label=r"resolving scale $L^*(H)$")
    ax[1].plot(Hs, Hs, "--", color=TEAL, lw=1.2, label=r"horizon $H=\lfloor\sqrt{p}\rfloor$")
    ax[1].plot(Hs, [h * h for h in Hs], ":", color="#b00", lw=1.5, label=r"field $p\sim H^2$")
    ax[1].set_yscale("log"); ax[1].set_xlabel("window horizon $H$"); ax[1].set_ylabel("frequency scale")
    ax[1].set_title("E3: the resolving band sits at the horizon", fontsize=10); ax[1].legend(fontsize=8, loc="upper left")
    plt.tight_layout(); plt.savefig(f"{FIGDIR}/fig_obstruction.pdf", bbox_inches="tight"); plt.savefig(f"{FIGDIR}/fig_obstruction.png", dpi=110, bbox_inches="tight"); plt.close()
    print(f"    wrote {FIGDIR}/fig_obstruction.pdf")
    # emergence: classical zeros (left) against units-chart modes (right)
    g = riemann_zeros(80)
    X0, X1 = 2, 30
    xs = np.linspace(X0 + 0.02, X1, 1400)
    rho = [mp.mpc(0.5, float(gg)) for gg in g]
    def psi_M(x, M):
        s = sum(2 * mp.re(mp.power(x, r) / r) for r in rho[:M])
        return float(x - mp.log(2 * mp.pi) - 0.5 * mp.log(1 - x ** -2) - s)
    CL = ["#f0a8a8", "#df6b6b", "#c0392b"]; FR = ["#a8c4ec", "#5f8fd6", "#1f5fbf"]; GRIDC = "#d9d9d9"
    fig, ax = plt.subplots(2, 2, figsize=(13.5, 8.2))
    A = ax[0, 0]
    for i, m in enumerate([1, 2, 3]):
        A.plot(xs, [float(-2 * mp.re(mp.power(x, rho[m - 1]) / rho[m - 1])) for x in xs], color=CL[i], lw=1.4, label=fr"$\rho_{m}=\frac{{1}}{{2}}+i\,{float(g[m - 1]):.2f}$")
    A.axhline(0, color=GRIDC, lw=0.8); A.set_title("classical spectral modes: the zeros"); A.set_xlabel("$x$"); A.set_ylabel(r"$-2\,{\rm Re}\,x^{\rho_m}/\rho_m$"); A.legend(fontsize=8); A.set_xlim(X0, X1)
    B = ax[0, 1]
    for i, q in enumerate([2, 3, 5]):
        B.step(ns, [mu[q] / phi[q] * ramanujan(q, int(n), mu) for n in ns], where="mid", color=FR[i], lw=1.5, label=fr"$q={q}$ (energy {E[q]})")
    B.axhline(0, color=GRIDC, lw=0.8); B.set_title(r"units-chart modes $\frac{\mu(q)}{\varphi(q)}c_q$ for $q=2,3,5$ (decreasing energy)"); B.set_xlabel("$n$"); B.legend(fontsize=8); B.set_xlim(X0, X1)
    C = ax[1, 0]
    C.step(np.concatenate([[X0], ns]), np.concatenate([[0], psi]), where="post", color="#111", lw=2.0, label=r"$\psi(x)$")
    for i, M in enumerate([5, 20, 80]):
        C.plot(xs, [psi_M(x, M) for x in xs], color=CL[i], lw=1.3, label=f"{M} zeros")
    C.set_title(r"classical: $\psi(x)$ from $M$ zeros"); C.set_xlabel("$x$"); C.legend(fontsize=8, loc="upper left"); C.set_xlim(X0, X1); C.set_ylim(0, X1 + 4)
    D = ax[1, 1]
    D.step(np.concatenate([[X0], ns]), np.concatenate([[0], psi]), where="post", color="#111", lw=2.0, label=r"$\psi(N)$")
    for i, L in enumerate([15, 60, 240]):
        D.plot(ns, Psi(L), color=FR[i], lw=1.4, label=f"bandwidth $L={L}$ (max dev {devs[i]:.2f})")
    D.set_title(r"E1c: $\Psi_L(N)=\sum_{n\leq N}\frac{n}{\varphi(n)}R_L(n)$ from $L$ units-chart modes"); D.set_xlabel("$N$"); D.legend(fontsize=8, loc="upper left"); D.set_xlim(X0, X1); D.set_ylim(0, X1 + 4)
    plt.tight_layout(); plt.savefig(f"{FIGDIR}/fig_emergence_frc.pdf", bbox_inches="tight"); plt.savefig(f"{FIGDIR}/fig_emergence_frc.png", dpi=110, bbox_inches="tight"); plt.close()
    print(f"    wrote {FIGDIR}/fig_emergence_frc.pdf")


# ======================================================================================================================
# block T — Turing's certificate over the laboratory Carriers' cycles (15 October 2026, T03 of reports/blueprint-20261013.md)
# =======================================================================================
# For a Carrier Ω the cycle of heights is [0, 2πΩ). The certificate decides N(2πΩ) = C(2πΩ): every zero of ζ with ordinate
# below 2πΩ is simple and on the line, cell by cell (Thm. hosted, row 20:F2). Method (Turing 1953; Lehman 1970; Brent 1979;
# the constants of Trudgian 2011 for t ≥ 168π):
#   * Z(t) by the Riemann–Siegel formula with the first correction term and Gabcke's remainder bound |R_1| ≤ 0.053 τ^{-5/4}
#     (τ = t/2π, t ≥ 200), in double precision with an explicit rounding bound; a sign is certified only where |Z| exceeds
#     both bounds;
#   * Gram points g_n (θ(g_n) = nπ) by Newton from the Lambert-W initial value; g_n is good when (−1)^n Z(g_n) > 0 is
#     certified; a Gram block is the span between consecutive good Gram points; Rosser's rule for a block of k Gram
#     intervals: at least k certified sign changes of Z in it (a grid of m points per interval, refined where fewer are found);
#   * Turing's theorem at a good Gram point g_n: if the blocks after g_n covering h Gram intervals satisfy Rosser's rule and
#     g_{n+h} − g_n > 2.067 + 0.059 log(g_{n+h}/2π), then S(g_n) ≤ 0; with the same on the blocks before, S(g_n) = 0, that is
#     N(g_n) = n + 1; the certified sign changes below g_n then equal N(g_n) or fall short, and equality gives C = N: every
#     zero below g_n simple and on the line. The rule may fail in the interior (Lehman 1970; Brent 1979: the first exception
#     at g_13999825): a block short at the finest grid keeps its brackets, and its union with two blocks on each side is read
#     at the finest grid, the missing zeros lying in a neighbour; the count is pinned by the two ends, not by the interior;
#   * below the first good Gram point above 168π the count and the sign changes are the host's at twenty-five digits (mpmath).
# The cells: N_y is the number of certified sign-change brackets in [2πy, 2π(y+1)); a bracket straddling a cell boundary is
# bisected with certified signs until it lies in one cell.
#   T1  Thm. hosted  [approx]  Ω = 233: N(2πΩ) = 1038, every cell clean (≈ 1.5 min, the low range by mpmath)
#   T2  Thm. hosted  [approx]  Ω = 30089: N(2πΩ) = 280186, every cell clean (≈ 1.5 min)
#   T3  Thm. hosted  [approx]  Ω = 2408561: N(2πΩ) = 32984135, every cell clean — the embedded record CERT_2408561 of this
#                              script's run of 15 October 2026 (RH_CERT_FULL=1 recomputes it, about an hour on one core)

TWO_PI = 2 * math.pi
EPS = 2.0 ** -52


def cert_gram_points(n):
    """g_n with θ(g_n) = nπ, by Newton from the Lambert-W initial value (vectorised)."""
    n = np.asarray(n, float)
    x = (n + 7 / 8) / math.e
    t = TWO_PI * (n + 7 / 8) / np.real(lambertw(x))
    for _ in range(6):
        t = t - (theta(t) - n * math.pi) / (0.5 * np.log(t / TWO_PI))
    return t


# Ψ(p) = cos(2π(p² − p − 1/16)) / cos(2πp) and its third derivative, with the removable singularities at p = 1/4, 3/4
_p = sp.symbols("p")
_Psi = sp.cos(2 * sp.pi * (_p ** 2 - _p - sp.Rational(1, 16))) / sp.cos(2 * sp.pi * _p)
_Psi3 = sp.diff(_Psi, _p, 3)
_f0 = sp.lambdify(_p, _Psi, "numpy")
_f3 = sp.lambdify(_p, _Psi3, "numpy")
_ser = {}
for _c in (sp.Rational(1, 4), sp.Rational(3, 4)):
    _s0 = sp.series(_Psi, _p, _c, 10).removeO()
    _s3 = sp.diff(_s0, _p, 3)
    _ser[float(_c)] = (sp.lambdify(_p, _s0, "numpy"), sp.lambdify(_p, _s3, "numpy"))


def cert_psi_c0_c1(p):
    p = np.asarray(p, float)
    c0 = np.empty_like(p); c3 = np.empty_like(p)
    near = np.zeros(p.shape, bool)
    for c, (f0s, f3s) in _ser.items():
        m = np.abs(p - c) < 0.02
        c0[m] = f0s(p[m]); c3[m] = f3s(p[m]); near |= m
    c0[~near] = _f0(p[~near]); c3[~near] = _f3(p[~near])
    return c0, -c3 / (96 * math.pi ** 2)


def cert_Z_certified(t):
    """Z(t) with the first correction term, and the bound |error| ≤ Gabcke's R_1 + the rounding bound. t ≥ 200."""
    t = np.asarray(t, float)
    tau = t / TWO_PI
    a = np.sqrt(tau)
    N = np.floor(a).astype(np.int64)
    p = a - N
    th = theta(t)
    main = np.zeros_like(t)
    fp = np.zeros_like(t)
    Nmax = int(N.max())
    for n in range(1, Nmax + 1):
        m = N >= n
        if n == 1:
            main += 2 * np.cos(th)
            fp += 2 * (np.abs(th) * 4 * EPS + EPS)
        else:
            ln = math.log(n); inv = 1 / math.sqrt(n)
            main[m] += 2 * np.cos(th[m] - t[m] * ln) * inv
            fp[m] += 2 * ((np.abs(th[m]) + t[m] * ln) * 4 * EPS + EPS) * inv
    c0, c1 = cert_psi_c0_c1(p)
    corr = (-1.0) ** (N - 1) * tau ** -0.25 * (c0 + c1 * tau ** -0.5)
    bound = 0.053 * tau ** -1.25 + fp + 1e-13 * (np.abs(main) + 1)
    return main + corr, bound


def cert_certified_signs(t):
    z, b = cert_Z_certified(t)
    s = np.zeros(len(t), np.int8)
    s[z > b] = 1; s[z < -b] = -1
    return z, s


def cert_brackets(ts, s):
    """Brackets (t_i, t_j) of consecutive certified points with opposite signs; uncertified points skipped."""
    idx = np.nonzero(s)[0]
    if len(idx) < 2: return np.zeros((0, 2))
    sc = s[idx]
    ch = np.nonzero(sc[:-1] * sc[1:] < 0)[0]
    return np.stack([ts[idx[ch]], ts[idx[ch + 1]]], axis=1)


def certify(Om, log=print, grid=4, max_grid=4096, chunk=20000, window=2, cache=None):
    """Turing's certificate over the cycle of the Carrier Ω: the record and the per-cell counts (block T)."""
    T = TWO_PI * Om
    t0 = time.time()
    # --- the low range by the host at high precision (mpmath): below the first good Gram point above 168π
    import mpmath as mp
    mp.mp.dps = 25
    n_a = int(math.ceil((theta(168 * math.pi + 2) / math.pi)))
    g = cert_gram_points(np.arange(n_a, n_a + 40))
    z, s = cert_certified_signs(g)
    good = s * ((-1) ** (np.arange(n_a, n_a + 40) % 2)) > 0
    i = int(np.argmax(good)); n_a += i; g_a = float(g[i])
    N_low = int(mp.nzeros(g_a))
    assert N_low == n_a + 1, (N_low, n_a + 1)
    low_grid = np.linspace(14.0, g_a, 40 * N_low)
    low_z = np.array([float(mp.siegelz(x)) for x in low_grid])
    low_s = np.sign(low_z).astype(np.int8)
    low_br = cert_brackets(low_grid, low_s)
    assert len(low_br) == N_low, (len(low_br), N_low)
    log(f"  low range: g_{n_a} = {g_a:.3f}, N = {N_low} zeros, {len(low_br)} sign changes of Z (mpmath, 25 digits) [{time.time()-t0:.0f} s]")
    # --- Gram points and their signs up to beyond T
    n_b_guess = int(theta(T) / math.pi) + 60
    ns = np.arange(n_a, n_b_guess + 1)
    if cache and os.path.exists(cache):
        z = np.load(cache); gs, ss = z["gs"], z["ss"]; assert len(gs) == len(ns)
        log(f"  Gram points and signs read from {cache}")
    else:
        gs = np.empty(len(ns)); ss = np.zeros(len(ns), np.int8)
        for c in range(0, len(ns), chunk):
            gg = cert_gram_points(ns[c:c + chunk]); gs[c:c + chunk] = gg
            ss[c:c + chunk] = cert_certified_signs(gg)[1]
        if cache: np.savez(cache, gs=gs, ss=ss)
    par = np.where(ns % 2 == 0, 1, -1).astype(np.int8)
    good = (ss * par) > 0
    log(f"  Gram points g_{n_a}..g_{ns[-1]}: {len(ns)}, good {int(good.sum())} ({100*good.mean():.1f} %), uncertified signs {int((ss == 0).sum())} [{time.time()-t0:.0f} s]")
    gi = np.nonzero(good)[0]
    # --- the blocks: between consecutive good Gram points; Rosser's rule by certified sign changes on a grid.
    # Memory-bounded (15 October, second version): the blocks are arrays, the grids are built per batch of blocks of one
    # length, the brackets are collected per batch; no per-block Python objects.
    nblocks = len(gi) - 1; blen = np.diff(gi)
    log(f"  blocks: {nblocks}, longest {int(blen.max())} Gram intervals")
    br_parts = [low_br]
    cert_brackets_fn = cert_brackets
    # blocks of length 1 with the Gram points' own certified signs: one change each (the two signs differ by goodness)
    one = gi[np.nonzero(blen == 1)[0]]
    br_parts.append(np.column_stack([gs[one], gs[one + 1]]))
    del one
    # longer blocks: grids, refined where fewer than k changes are found
    pend = np.nonzero(blen > 1)[0]                    # block indices
    viol = np.zeros(nblocks, bool)
    m = grid
    def signs_of(flat):
        s = np.zeros(len(flat), np.int8)
        for c in range(0, len(flat), chunk):
            s[c:c + chunk] = cert_certified_signs(flat[c:c + chunk])[1]
        return s
    while len(pend) and m <= max_grid:
        nxt = []
        for k in np.unique(blen[pend]):
            sel = pend[blen[pend] == k]; L = int(k) * m + 1
            nb_batch = max(1, min(len(sel), 2 * chunk // L))
            for c in range(0, len(sel), nb_batch):
                ids = sel[c:c + nb_batch]; nb = len(ids)
                A = gs[gi[ids]]; Bv = gs[gi[ids] + k]
                ts = A[:, None] + (Bv - A)[:, None] * np.linspace(0.0, 1.0, L)[None, :]
                s = signs_of(ts.ravel()).reshape(nb, L)
                last = np.maximum.accumulate(np.where(s != 0, np.arange(L)[None, :], 0), axis=1)   # index of the last certified point at or before i
                prev = last[:, :-1]; cur = s[:, 1:]
                rows = np.arange(nb)[:, None]
                change = (cur != 0) & (s[rows, prev] * cur < 0)
                cnt = change.sum(axis=1)
                ok = cnt >= k
                keep = ok | (m * 4 > max_grid)                     # at the last grid the short blocks keep their brackets too (the exceptions)
                if keep.any():
                    r, i = np.nonzero(change[keep])
                    tso = ts[keep]; pro = prev[keep]
                    br_parts.append(np.column_stack([tso[r, pro[r, i]], tso[r, i + 1]]))
                if (~ok).any():
                    nxt.append(ids[~ok])
        nxt = np.concatenate(nxt) if nxt else np.zeros(0, np.int64)
        log(f"    grid {m} per Gram interval: {len(pend)} blocks, {len(nxt)} short of Rosser's rule [{time.time()-t0:.0f} s]")
        pend = nxt; m *= 4
    viol[pend] = True
    violations = pend
    # the exceptions to Rosser's rule (Lehman 1970, Brent 1979): a block short of its count at the finest grid has its missing
    # zeros in a neighbouring block; the union of the block with `window` blocks on each side is read at the finest grid, its
    # brackets replacing the coarse ones, and the union is resolved when its certified sign changes reach its Gram intervals.
    # The count below the Turing point does not depend on the rule holding in the interior: it is pinned by the host's count
    # at g_a and Turing's theorem at g_n; the rule drives the refinement, and the unions name where the grid looked harder.
    unions = []
    if len(violations):
        log(f"  blocks short of Rosser's rule at grid {max_grid}: {len(violations)}, Gram indices {[int(ns[gi[j]]) for j in violations[:10]]}")
        spans = sorted((max(0, j - window), min(nblocks - 1, j + window)) for j in violations)
        merged = []
        for a, b in spans:
            if merged and a <= merged[-1][1] + 1: merged[-1] = (merged[-1][0], max(merged[-1][1], b))
            else: merged.append((a, b))
        fine_parts = []
        for (ja, jb) in merged:
            a = gi[ja]; b = gi[jb + 1]; k = int(b - a); L = k * max_grid + 1
            ts = np.linspace(gs[a], gs[b], L); s = signs_of(ts)
            br = cert_brackets_fn(ts, s)
            resolved = len(br) >= k; host_pts = 0
            if not resolved and (s == 0).any():
                # a pair of zeros closer than the double-precision certificate resolves (|Z| between them below the bound): the
                # uncertified points of the union are read by the host at thirty digits, as the low range is, and the signs
                # of the union are completed with them
                mp.mp.dps = 30
                unc = np.nonzero(s == 0)[0]; host_pts = len(unc)
                for i_ in unc:
                    zv = mp.siegelz(mp.mpf(float(ts[i_])))
                    s[i_] = 1 if zv > 0 else (-1 if zv < 0 else 0)
                br = cert_brackets_fn(ts, s)
                resolved = len(br) >= k
            short = [int(ns[gi[j]]) for j in violations if ja <= j <= jb]           # the Gram indices of the short blocks in the union
            unions.append(dict(blocks=[int(ja), int(jb)], gram=[int(ns[a]), int(ns[b])], short=short, intervals=k, changes=int(len(br)), host_points=int(host_pts), resolved=bool(resolved)))
            fine_parts.append(br)
            log(f"    union of blocks {ja}..{jb} (g_{ns[a]}..g_{ns[b]}, {k} Gram intervals): {len(br)} certified sign changes at grid {max_grid}"
                + (f", {host_pts} uncertified points read by the host at thirty digits" if host_pts else "") + f" — {'resolved' if resolved else 'UNRESOLVED'}")
        # the coarse brackets inside the unions are replaced by the fine ones
        lo = np.array([gs[gi[ja]] for ja, jb in merged]); hi = np.array([gs[gi[jb + 1]] for ja, jb in merged])
        def outside(br):
            mid = 0.5 * (br[:, 0] + br[:, 1])
            inside = np.zeros(len(br), bool)
            for l_, h_ in zip(lo, hi): inside |= (mid > l_) & (mid < h_)
            return br[~inside]
        br_parts = [outside(br) for br in br_parts if len(br)] + fine_parts
    # --- Turing's theorem at the end point: the last good Gram point g_n ≥ T with the blocks after it satisfying the bound
    B = lambda t: 2.067 + 0.059 * math.log(t / TWO_PI)
    n_end = None
    for j in range(len(gi) - 1, -1, -1):
        a = gi[j]
        if gs[a] < T: break
        ok = False; h = 0
        for jj in range(j, len(gi) - 1):
            if viol[jj]: break
            h = gi[jj + 1] - a
            if gs[a + h] - gs[a] > B(gs[a + h]): ok = True; break
        if ok: n_end = (j, a, h)
    assert n_end is not None, "no certifiable end point in range"
    j, a, h = n_end
    n_cert = int(ns[a]); g_cert = float(gs[a])
    log(f"  Turing at g_{n_cert} = {g_cert:.3f} (≥ T = {T:.3f}): the blocks after it span {int(h)} Gram intervals, {gs[a+h]-g_cert:.3f} > {B(gs[a+h]):.3f}; N(g_{n_cert}) = {n_cert + 1}")
    # the blocks before the point over the bound's span satisfy Rosser's rule (S(g_n) ≥ 0; the symmetric half of Turing's theorem)
    before_ok = False; hb = 0
    for jj in range(j - 1, -1, -1):
        if viol[jj]: break
        hb = a - gi[jj]
        if gs[a] - gs[a - hb] > B(gs[a]): before_ok = True; break
    log(f"  the blocks before g_{n_cert} span {int(hb)} Gram intervals, {gs[a]-gs[a-hb]:.3f} {'>' if before_ok else '<='} {B(gs[a]):.3f}: S(g_{n_cert}) {'≥ 0' if before_ok else 'not bounded below'}")
    # --- the count
    allbr = np.concatenate([br for br in br_parts if len(br)]); del br_parts
    allbr = allbr[allbr[:, 1] <= g_cert + 1e-9]
    C_cert = len(allbr)
    log(f"  certified sign changes below g_{n_cert}: {C_cert} against N = {n_cert + 1}: {'EQUAL' if C_cert == n_cert + 1 else 'DEFICIT ' + str(n_cert + 1 - C_cert)}")
    ok_total = (C_cert == n_cert + 1) and before_ok and all(u["resolved"] for u in unions)
    # --- the zeros below T, and the cells
    work = allbr[allbr[:, 0] < T]; del allbr            # brackets below T and those straddling T
    def cell(x): return np.floor(x / TWO_PI).astype(np.int64)
    # bisect brackets that straddle T or a cell boundary (certified signs), until each lies in one cell
    need = cell(work[:, 0]) != cell(work[:, 1])
    it = 0
    while need.any() and it < 60:
        w = work[need]
        mid = 0.5 * (w[:, 0] + w[:, 1])
        smid = signs_of(mid); sl = signs_of(w[:, 0])
        left = (smid * sl) < 0          # the change is in the left half
        unc = smid == 0
        w2 = w.copy()
        w2[left, 1] = mid[left]; w2[~left & ~unc, 0] = mid[~left & ~unc]
        w2[unc, 0] = w[unc, 0] + 0.37 * (w[unc, 1] - w[unc, 0])   # an uncertified midpoint: shrink from an off-centre point
        work[need] = w2
        need = cell(work[:, 0]) != cell(work[:, 1]); it += 1
    assert not need.any(), "a bracket could not be confined to one cell"
    work = work[work[:, 1] <= T]
    N_T = len(work)
    cells = np.bincount(cell(work[:, 0]), minlength=Om)[:Om]
    rec = dict(Omega=Om, T=T, n_low=n_a, g_low=g_a, N_low=N_low, n_end=n_cert, g_end=g_cert, N_end=n_cert + 1, C_end=C_cert,
               gram_points=len(ns), good_fraction=float(good.mean()), uncertified=int((ss == 0).sum()), blocks=nblocks,
               longest_block=int(blen.max()), rosser_violations=len(violations), rosser_unions=unions, turing_bound_intervals=int(h),
               turing_before_intervals=int(hb),
               N_T=N_T, cells_max=int(cells.max()), cells_empty=int((cells == 0).sum()), cells_last10=cells[-10:].tolist(),
               cells_sum=int(cells.sum()), certified=bool(ok_total and N_T == cells.sum()), seconds=round(time.time() - t0, 1))
    log(f"  N(2πΩ) = {N_T}, every zero simple and on the line: {rec['certified']}; cells: max {rec['cells_max']}, empty {rec['cells_empty']}, last ten {rec['cells_last10']} [{rec['seconds']} s]")
    return rec, cells


# The record of the run of certify(2408561) of 15 October 2026 (the cloud container, one core, the memory-bounded block phase):
# the sdist ships the script alone, so T3 reads this record unless RH_CERT_FULL=1 recomputes it (about an hour).
CERT_2408561 = {
    "Omega": 2408561,
    "T": 15133435.08664577,
    "n_low": 290,
    "g_low": 530.5318655440009,
    "N_low": 291,
    "n_end": 32984135,
    "g_end": 15133435.125860486,
    "N_end": 32984136,
    "C_end": 32984136,
    "gram_points": 32983905,
    "good_fraction": 0.8464814581536055,
    "uncertified": 231,
    "blocks": 27920263,
    "longest_block": 7,
    "rosser_violations": 4,
    "rosser_unions": [
        {
            "blocks": [
                11921435,
                11921439
            ],
            "gram": [
                13999520,
                13999529
            ],
            "intervals": 9,
            "changes": 9,
            "host_points": 0,
            "resolved": True,
            "short": [
                13999525
            ]
        },
        {
            "blocks": [
                20663429,
                20663433
            ],
            "gram": [
                24360728,
                24360736
            ],
            "intervals": 8,
            "changes": 8,
            "host_points": 22,
            "resolved": True,
            "short": [
                24360730
            ]
        },
        {
            "blocks": [
                26069384,
                26069388
            ],
            "gram": [
                30783327,
                30783333
            ],
            "intervals": 6,
            "changes": 6,
            "host_points": 0,
            "resolved": True,
            "short": [
                30783329
            ]
        },
        {
            "blocks": [
                26193457,
                26193461
            ],
            "gram": [
                30930925,
                30930932
            ],
            "intervals": 7,
            "changes": 7,
            "host_points": 0,
            "resolved": True,
            "short": [
                30930927
            ]
        }
    ],
    "turing_bound_intervals": 7,
    "turing_before_intervals": 7,
    "N_T": 32984135,
    "cells_max": 17,
    "cells_empty": 2,
    "cells_last10": [
        15,
        15,
        14,
        15,
        14,
        15,
        14,
        16,
        14,
        14
    ],
    "cells_sum": 32984135,
    "certified": True,
    "seconds": 1916.6
}


def block_T():
    """Block T — Turing's certificate over the cycles of the laboratory Carriers 233, 30089 and 2408561 (Thm. hosted, row F2)."""
    print("\n== block T: Turing's certificate over the laboratory cycles (Thm. hosted, row F2) ==")
    here = os.path.dirname(os.path.abspath(__file__))
    for pid, Om in (("T1", 233), ("T2", 30089), ("T3", 2408561)):
        rec_path = os.path.join(here, f"turing_{Om}.json")
        if Om == 2408561 and not os.environ.get("RH_CERT_FULL"):
            rec = CERT_2408561; source = "the recorded run of 15 October 2026 (RH_CERT_FULL=1 recomputes it)"
        else:
            rec, cells = certify(Om, log=lambda s: print("   " + s))
            try: json.dump(rec, open(rec_path, "w"), indent=1)
            except OSError: pass
            source = "computed now"
        expected = {233: 1038, 30089: 280186, 2408561: 32984135}[Om]
        unions = rec.get("rosser_unions", [])
        ok = rec["certified"] and rec["N_T"] == expected and rec["C_end"] == rec["N_end"] and all(u["resolved"] for u in unions)
        # 20:F2 (p20081)
        check(pid, f"Turing's certificate over the cycle of Ω = {Om}: N(g_{rec['n_end']}) = {rec['N_end']} by Turing's theorem, {rec['C_end']} certified sign changes; N(2πΩ) = {rec['N_T']}, every cell clean", ok,
              f"{source}; Gram points {rec['gram_points']}, good {100*rec['good_fraction']:.1f} %, uncertified {rec['uncertified']}, blocks {rec['blocks']}, longest {rec['longest_block']}, exceptions to Rosser's rule {rec['rosser_violations']} ({sum(u['resolved'] for u in unions)} unions resolved at the finest grid), Turing span {rec['turing_bound_intervals']} after / {rec.get('turing_before_intervals', '?')} before; cells max {rec['cells_max']}, empty {rec['cells_empty']}, last ten {rec['cells_last10']}; {rec['seconds']} s",
              kind="[approx]")

if __name__ == "__main__":
    want = [a.upper() for a in sys.argv[1:]] or sorted(BLOCK)
    bad = [b for b in want if b not in BLOCK]
    if bad: sys.exit(f"no block {', '.join(bad)}: the blocks are {', '.join(sorted(BLOCK))}")
    t0 = time.time()
    for b in want:
        t = time.time(); _run_block(b); print(f"    [block {b}: {time.time() - t:.0f} s]")
    ok = summary(write=(want == sorted(BLOCK)))
    kinds = {}
    for r in RESULTS: kinds[r["kind"]] = kinds.get(r["kind"], 0) + 1
    print("by kind: " + ", ".join(f"{k} {v}" for k, v in sorted(kinds.items())) + f"; {len(RESULTS)} checks in {time.time() - t0:.0f} s" + ("; results.json written" if want == sorted(BLOCK) else ""))
    sys.exit(0 if ok else 1)
