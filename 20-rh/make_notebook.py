"""Builds validate_20rh.ipynb (the Colab driver of the 20-rh validation package). Run: python3 make_notebook.py"""
import nbformat as nbf

COLAB = "https://colab.research.google.com/github/gamayos/frc-numerics/blob/main/20-rh/validate_20rh.ipynb"
nb = nbf.v4.new_notebook()
nb.metadata = {"kernelspec": {"display_name": "Python 3", "language": "python", "name": "python3"},
               "language_info": {"name": "python"}, "colab": {"provenance": [], "toc_visible": True}}
cells = []
md = lambda s: cells.append(nbf.v4.new_markdown_cell(s))
code = lambda s: cells.append(nbf.v4.new_code_cell(s))

md(f"""# 20-rh — validation package
[![Open In Colab](https://colab.research.google.com/assets/colab-badge.svg)]({COLAB})

**Paper.** *Riemann Hypothesis over Finite Holographic Substrate* (Akhtman & Voether, 2026), `20-rh` of the FRC corpus.
**Package.** `frc-numerics/20-rh` — seven block scripts driven by this notebook. Every cell below names the labelled
statements of the paper it checks (`Theorem`, `Proposition`, `Numerical Observation`, `Definition` — by their `\\label`
as printed in the paper), lists the paper-local predicates as the block scripts register them, and gives the master-ledger
row of the corpus they witness (`00:D11` the shell theorem, `00:D12` the classical hypothesis as a screen value).
The package regenerates every numerical figure of the paper (`figures/`); the one qualitative illustration
(`carrier-domains.png`) is not a computation and is omitted.

**Kinds.** `EXACT` checks are integer-pinned finite computations (a pass is a proof on the tested instances);
`[approx]` checks compare a floating-point observation with the value the paper states, to a stated tolerance;
`[chart]` marks a continuum reading of a finite object. The discipline of the construction — *ζ never evaluated* —
binds blocks A–C: every construction there uses only the sieved von Mangoldt comb, its logarithms, and the archimedean
phase from log Γ; the Riemann heights appear as validation markers only. The control arms of block D evaluate Hurwitz
zeta functions, as the paper says they do.

**Run.** Cell by cell, or *Runtime → Run all*. Full depths take ≈ 4 min on Colab (the 8×10⁷ comb of block D is the
largest object); set `FAST = True` in the second cell for reduced depths (≈ 2 min; the same 75 predicates, the deep
tails of the depth scans shortened). The last cell writes `results.json` and fails loudly if any predicate fails.""")

code("""# --- environment: clone the package if this notebook is not already running inside it (Colab), install the two
# non-default dependencies. numpy, scipy, matplotlib are standard on Colab; mpmath and sympy are usually present too.
import os, sys, subprocess
if not os.path.exists("rhcommon.py"):
    if not os.path.exists("frc-numerics"):
        subprocess.run(["git", "clone", "--depth", "1", "https://github.com/gamayos/frc-numerics.git"], check=True)
    os.chdir("frc-numerics/20-rh")
subprocess.run([sys.executable, "-m", "pip", "install", "-q", "--disable-pip-version-check", "numpy>=1.24", "scipy>=1.10", "mpmath>=1.3", "sympy>=1.12", "matplotlib>=3.7"],
               check=True, env={**os.environ, "PIP_ROOT_USER_ACTION": "ignore"})
print("working directory:", os.getcwd())""")

code("""FAST = False                      # True: reduced depths (≈ 2 min); False: the paper's depths (≈ 4 min)
import os
os.environ["RH_FAST"] = "1" if FAST else "0"
os.environ["RH_FIGDIR"] = "figures"
import importlib, rhcommon
importlib.reload(rhcommon)        # a fresh registry if the notebook is re-run
from IPython.display import Image, display
def show(name): display(Image(filename=f"figures/{name}.png"))
print("FAST =", FAST)""")

md("""## Block A — the shell theorem and the exact shell arithmetic  (`a_shell.py`, EXACT, master ledger **00:D11**)
Shells p = 13, 17, 29, 37, 41 in full (every point of F_{p²}); p = 173 for A1, A4, A6. Integer arithmetic only.

| id | paper statement | predicate |
|---|---|---|
| A1 | Theorem `zeroslot` | Σ_{x∈F_p^×} x^k = 0 for every nonterminal k; = −1 on the terminal slot |
| A2 | Theorem `compl` | Φ(k) = −g^k bijects the nonterminal slots onto F_p^× ∖ {−1} |
| A3 | Lemma `K` | on F_{p²} = F_p(η): \\|U_{p+1}\\| = p+1, Frobenius = inversion on it, i = √−1 Frobenius-fixed with N(i) = −1 |
| A4 | Proposition `critical` | the finite critical line: Tr z = 1 ⟺ z = 2⁻¹ + bη; \\|L_{1/2}\\| = p; N(z) = ¼ − νb²; 2⁻¹ = 2κ+1 = −π |
| A5 | Theorem `agree` | the Klein four-group ⟨φ, ρ⟩ and its fixed loci F_p, L_{1/2}, {2⁻¹}; F_p ∩ L_{1/2} = {2⁻¹} |
| A6 | §1.3 (the Subject register) | π = 2κ, 2π ≡ −1, i = g^{−κ}, i² ≡ −1, e = g^i on the odd representative, e^{iπ} ≡ −1 |
| A7 | Theorem `hp` (i), (iii); Remark `parseval` | the constant mode carries the mean v̄ = ψ(p−1)/(p−1), the nontrivial characters carry v − v̄·1; S x^k = g^k x^k in F_p and S χ_j = ω^j χ_j on ℓ²(F_p^×); Tr S^r = (p−1)·[(p−1) \\| r] |
| A8 | Theorem `hp` (iv), Definition `jacobi` | self-adjointness is free: any real multiset is the spectrum of a real-symmetric tridiagonal matrix |
| A9 | Proposition `ground` | the Ramanujan sum c_p(n) = −1 for every n ≢ 0 (mod p) |
| A10 | Definition `shells` (the shared quarter-turn core) | Q₄ ⊂ both cycles; on the pair (13, 233) the projection C_{Ω−1} → C_{p−1} does not exist (12 ∤ 232) |""")
code("import a_shell; a_shell.run()")

md("""## Block B — the de-framing dictionary  (`b_deframe.py`, [chart] / [approx])
Definition `deframe`: a shell of cardinality p reads ζ on the line to height T = 2πp with the Riemann–Siegel main sum of
length √p; a height is the scale coordinate of the shell that reads it. The Hardy Z function enters as the classical side of the
dictionary only.

| id | paper statement | predicate | kind |
|---|---|---|---|
| B1 | Proposition `density` | smooth zero density at T = 2πp is (1/2π) log p: 0.6226, 0.9891, 1.3556, 1.7220 at p = 50, 500, 5·10³, 5·10⁴ | [chart] |
| B2 | Numerical Observation `residue` | the finite-horizon residue \\|Z_horizon − Z\\| ∝ p^{−1/4} (log-log slope ≈ −1/4) | [approx] |
| B3 | Proposition `critical` (de-framing limit) | 2⁻¹/p = (2κ+1)/p → ½ from above | [chart] |
| B4 | Definition `deframe` | the horizon-length main sum has one sign change per zero on [10, 55], each within 0.5 of γ_n | [approx] |""")
code("import b_deframe; b_deframe.run(); show('fig_deframing')")

md("""## Block C — the spectrum from the prime side, ζ never evaluated  (`c_primeside.py`, [approx])
Inputs: the sieved comb {Λ(n)}, its logarithms, the raised-cosine taper, and θ(T) from log Γ. Ñ_N(T) = θ(T)/π + 1 + S_comb(T).

| id | paper statement | predicate |
|---|---|---|
| C1 | Numerical Observation `primespec` | the scale-spectrum \\|Σ_N(γ)\\| of the N = 10⁶ comb peaks at the first six heights (paper: 14.14, 21.02, 25.02, 30.40, 32.96, 37.57) within 0.03 |
| C2 | Numerical Observation `trace` | the secular condition Ñ_N(T) = n − ½ recovers the first ten heights: mean 4.4×10⁻⁵, max 1.5×10⁻⁴ at N = 10⁶; 3.6×10⁻⁴ at 10³, 6×10⁻⁵ at 10⁵ |
| C3 | Numerical Observation `matrix` | the colleague matrix of the Chebyshev fit of cos(π Ñ_N) on [10, 52]: mean error 5.9×10⁻⁵ at dimension 520, ≈ 4.5×10⁻⁵ by 620 |
| C4 | Definition `jacobi`, Numerical Observation `jacobi` | the comb-built Jacobi matrix: real-symmetric tridiagonal, eigenvalues = secular roots to 10⁻¹², the stated a, b coefficients |
| C5 | Proposition `gauge` | the additive injection −i d/du + V_comb is gauge-trivial: spacing standard deviation 0.08 (absolute; 0.11 of the mean) against 0.39 of the mean for the heights (two conventions in the paper's sentence — README) |""")
code("import c_primeside; c_primeside.run(); show('fig_prime_spectrum'); show('fig_operator_spectrum')")

md("""### Block C, continued — random-matrix statistics of the target spectrum  (`c_gue.py`)
Definition `specmap` reads the heights as the target spectrum ρ ↦ −i(ρ − ½); the heights here are computed independently (mpmath `zetazero`).

| id | paper statement | predicate | kind |
|---|---|---|---|
| C6 | Numerical Observation `gue` | unfolded spacings of the first 240 zeros: P(s < ½) = 0.05 (GUE ≈ 0.12, Poisson ≈ 0.39), variance 0.13 (GUE ≈ 0.18, Poisson 1) | [approx] |
| C6b | Figure `hp` (right) | the count N(T) lies on the Berry–Keating (T/2π)(log(T/2π) − 1) + 7/8: density (1/2π) log p at T = 2πp | [chart] |""")
code("import c_gue; c_gue.run(); show('fig_hilbert_polya')")

md("""### Block C, continued — the χ-twisted comb  (`c_chi.py`, [approx])
Proposition `chi` (real character case), Numerical Observation `chi`: χ = χ_{−4}, θ_χ(t) = Im log Γ(¾ + it/2) + (t/2) log(4/π),
N_χ = θ_χ/π + S^χ_comb with no pole term; validation arm L(s, χ) = 4^{−s}[ζ(s, ¼) − ζ(s, ¾)] via Hurwitz zeta.

| id | predicate |
|---|---|
| C7a | N_χ at the first six zeros of L(s, χ_{−4}) reads 0.4997, 1.4998, 2.4999, 3.4999, 4.4999, 5.4998; the completed L is real on the line |
| C7b | the twisted secular condition with the N = 10⁶ comb, L never evaluated, recovers 6.0209, 10.2438, 12.9881, 16.3426, 18.2920, 21.4506 to mean error 8.6×10⁻⁵ |""")
code("import c_chi; c_chi.run()")

md("""## Block D — the classification and the Euler-product discriminator  (`d_classification.py`, [approx], master ledger **00:D12**)
Theorem `turing`: C ≤ N_crit ≤ N; RH below T is N = N_crit; C = N is Turing's practical certificate, read on the shell from the two
sides of the explicit formula (both readings uncertified). Corollary `conditional`: the classical hypothesis is the screen value
N − N_crit = 0. Numerical Observation `dh`: the value is discriminating. The control arms evaluate Hurwitz zeta functions.

| id | paper statement | predicate |
|---|---|---|
| D1 | Theorem `turing`, Corollary `conditional` | Ñ_N rounds to N = 1, 3, 10 at T = 15, 30, 50.3; sign changes of the horizon main sum give C = 1, 3, 10 = N |
| D2a | Numerical Observation `dh` | the completed Davenport–Heilbronn Λ_f(½ + it) is real to 10⁻²⁰ |
| D2b | Numerical Observation `dh` | argument principle by band on [0, 87]: f: 45 strip zeros vs 43 on-line sign changes, the deficit 2 opening only in the band of the off-line pair 0.8085171825 + 85.6993484854 i (validated \\|f\\| < 10⁻⁶); \\|Z_f\\| dips to 0.357 at 85.71; control L(s, χ): 45 = 45, deficit 0 in every band |
| D2c | Numerical Observation `dh` | the secular condition on the Λ_f comb lands two "on-line" roots on the phantom height: 85.63/85.76 (10⁵), 85.65/85.75 (4×10⁵) |
| D2d | Numerical Observation `dh` | the raw DH count at 85.9 drifts 45.14 → 45.73 over depths 5×10⁴ … 8×10⁵; 42.66 … 42.73 at 85.3; stable at 60.3 (28.005 ± 0.002) and 84.0 (43.00 ± 0.01) |
| D2e | Numerical Observation `dh` | the ζ comb at the pole: t = 1 reads +0.09, −0.26, +0.36, −0.08, −0.81, −1.42, −1.46 at depths 10⁴ … 8×10⁷; t = 5, 10 within ±0.02, ±0.003; t = 15 within 2×10⁻³ of 1; t = 30 from 3.04 to 2.998; t = 50.3 within 10⁻² of 10 |""")
code("import d_classification; d_classification.run(); show('fig_dh')")

md("""## Block E — resonance, antipode, horizon-scale resolution, square-root cancellation  (`e_resonance.py`)
The units-chart side: Ramanujan sums as the standing waves of the additive meridian, the Möbius-weighted resonance and its limit.

| id | paper statement | predicate | kind |
|---|---|---|---|
| E1a | Theorem `resonance` (b) | Λ = μ ∗ log on the divisor lattice: symbolic for n ≤ 300 (sympy), floating point for n ≤ 5000 | EXACT |
| E1b | Theorem `resonance` (a), (c) | Hardy: R_L(n) → (φ(n)/n) Λ(n) (Cesàro mean to L = 4000); the intertwiner (n/φ(n)) R → Λ = log ℓ | [approx] |
| E1c | Definition `resonance`, Figure `emergence` | Ψ_L(N) = Σ_{n≤N} (n/φ(n)) R_L(n) → ψ(N): the maximal deviation on N ≤ 30 falls over L = 15, 60, 240 | [approx] |
| E2a | Numerical Observation `antipode` | per-mode energy μ²(q)/φ(q) = 1, ½, ¼, ⅙ at q = 2, 3, 5, 7; unique global maximum at the antipode q = 2 | EXACT |
| E2b | Numerical Observation `antipode` | the additive-transform band energy of the prime indicator (p = 10007) peaks at the antipode and follows 1/φ(q) — reported against the paper's 1220 > 640 > 323 > 214, not pinned (normalisation unstated; README) | [approx] |
| E3 | Numerical Observation `horizon` | the resolving threshold L*(H) exists for H = 6 … 50 and tracks the horizon: L* < 6H ≪ H² | [approx] |
| E4 | Proposition `flat`, Numerical Observation `flat` | the maximal chart-mode correlation with the primes sits at the 1/√p floor: 0.08 vs 0.03 at p = 1009, 0.0087 vs 0.0032 over the 5×10⁴ modes of p ≈ 10⁵; the resonance correlates 0.90 | [approx] |""")
code("import e_resonance; e_resonance.run(); show('fig_obstruction'); show('fig_emergence_frc')")

md("""## Summary
Writes `results.json` (one record per predicate: id, label, kind, PASS/FAIL, detail) and raises if any predicate failed.""")
code("""ok = rhcommon.summary(write=True)
kinds = {}
for r in rhcommon.RESULTS: kinds[r["kind"]] = kinds.get(r["kind"], 0) + 1
print("by kind:", ", ".join(f"{k} {v}" for k, v in sorted(kinds.items())))
failed = [r["id"] for r in rhcommon.RESULTS if not r["ok"]]
assert ok, f"FAILED predicates: {failed}"
print("all predicates pass; figures in figures/, records in results.json")""")

nb.cells = cells
nbf.write(nb, "validate_20rh.ipynb")
print("wrote validate_20rh.ipynb with", len(cells), "cells")
