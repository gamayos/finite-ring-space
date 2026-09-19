"""Builds the Colab driver of the 20-rh validation package — 20-rh-main.ipynb (the corpus name, the one the public
ledger page links) and 20-rh-validate.ipynb (the name the paper's Reproducibility section pins at commit b2a3fcec);
the two are the same notebook. Run: python3 make_notebook.py"""
import nbformat as nbf

COLAB = "https://colab.research.google.com/github/gamayos/finite-ring-space/blob/main/src/20-rh/20-rh-main.ipynb"
nb = nbf.v4.new_notebook()
nb.metadata = {"kernelspec": {"display_name": "Python 3", "language": "python", "name": "python3"},
               "language_info": {"name": "python"}, "colab": {"provenance": [], "toc_visible": True}}
cells = []
md = lambda s: cells.append(nbf.v4.new_markdown_cell(s))
code = lambda s: cells.append(nbf.v4.new_code_cell(s))

md(f"""[![Open In Colab](https://colab.research.google.com/assets/colab-badge.svg)]({COLAB})

## Riemann Hypothesis over the Holographic Substrate (Akhtman & Voether, 2026)

**Validation Package.** `finite-ring-space/src/20-rh` — seven block scripts driven by this notebook, 94 checks (57 EXACT, 34 [approx],
3 [chart]). Each check names the row(s) of the paper's predicate ledger it witnesses (the paper's Appendix A, rows cited as `20:XN`;
public copy at `docs/20-rh/20-rh-ledger.html`), and the ledger's source column cites the check ids in return. Where a row is proved in
Lean (`lean/FrcCore/Rh.lean` with no axioms, or `lean/FrcLedger/Rh.lean` on Mathlib — the shell rows B2, B4–B10, C2, C5, E1, E12, E13),
the check here is the instance the reader can run. Master-ledger rows of the corpus reached through the paper rows: `00:D11` (the shell
theorem, `20:E12`) and `00:D12` (the classical hypothesis as a screen value, `20:F1–F2`). Every cell below names the labelled
statements of the paper it checks (`Theorem`, `Proposition`, `Numerical Observation`, `Definition` — by their `\\label` as printed
in the paper) and lists the paper-local predicates as the block scripts register them. The package regenerates every numerical
figure of the paper (`figures/`); the one qualitative illustration (`carrier-domains.png`) is not a computation and is omitted.

**Kinds.** `EXACT` checks are integer-pinned finite computations (a pass is a proof on the tested instances);
`[approx]` checks compare a floating-point observation with the value the paper states, to a stated tolerance;
`[chart]` marks a continuum reading of a finite object. The discipline of the construction — *ζ never evaluated* —
binds blocks A–C: every construction there uses only the sieved von Mangoldt comb, its logarithms, and the archimedean
phase from log Γ; the Riemann heights appear as validation markers only. The control arms of block D evaluate Hurwitz
zeta functions, as the paper says they do.

**Run.** Cell by cell, or *Runtime → Run all*. Full depths take ≈ 6 min on Colab (the 8×10⁷ comb of block D is the
largest object); set `FAST = True` in the second cell for reduced depths (≈ 2 min; the same 94 checks, the deep
tails of the depth scans shortened). The last cell writes `results.json` and fails loudly if any predicate fails.

**Ledger.** The paper's predicate ledger (Appendix A: 66 rows in blocks A–F, V, Z, cited as `20:XN`). Each check below prints the ledger row(s) it witnesses in square brackets, and `results.json` records them.""")

code("""# --- environment: clone the package if this notebook is not already running inside it (Colab), install the two
# non-default dependencies. numpy, scipy, matplotlib are standard on Colab; mpmath and sympy are usually present too.
import os, sys, subprocess
if not os.path.exists("rhcommon.py"):
    if not os.path.exists("finite-ring-space"):
        !git clone --filter=blob:none --sparse https://github.com/gamayos/finite-ring-space.git
        os.chdir("finite-ring-space")
        !git sparse-checkout set src/20-rh
        os.chdir("src/20-rh")
    else:
        os.chdir("finite-ring-space/src/20-rh")

!pip install -q --disable-pip-version-check "numpy>=1.24" "scipy>=1.10" "mpmath>=1.3" "sympy>=1.12" "matplotlib>=3.7"
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
Shells p = 13, 17, 29, 37, 41 in full (every point of F_{p²}); p = 173 for A1, A4, A6; 1009 and 10009 for A11. Integer arithmetic only.

| id | paper statement | predicate |
|---|---|---|
| A1 | Theorem `zeroslot` | Σ_{x∈F_p^×} x^k = 0 for every nonterminal k; = −1 on the terminal slot |
| A2 | Theorem `compl` | Φ(k) = −g^k bijects the nonterminal slots onto F_p^× ∖ {−1} |
| A3 | Lemma `K` | on F_{p²} = F_p(η): \\|U_{p+1}\\| = p+1, Frobenius = inversion on it, i = √−1 Frobenius-fixed with N(i) = −1 |
| A4 | Proposition `critical` | the finite critical line: Tr z = 1 ⟺ z = 2⁻¹ + bη; \\|L_{1/2}\\| = p; N(z) = ¼ − νb²; 2⁻¹ = 2κ+1 = −π |
| A5 | Theorem `agree` | the Klein four-group ⟨φ, ρ⟩ and its fixed loci F_p, L_{1/2}, {2⁻¹}; F_p ∩ L_{1/2} = {2⁻¹} |
| A6 | §1.3 (the Subject register) | π = 2κ, 2π ≡ −1, i = g^{−κ}, i² ≡ −1, e = g^i on the odd representative, e^{iπ} ≡ −1 |
| A7 | Theorem `hp` (iii), the F_p reading | S x^k = g^k x^k on the power characters, integer arithmetic; Tr S^r = (p−1)·[(p−1) \\| r] (EXACT) |
| A7b | Theorem `hp` (i), (iii); Remark `parseval` | on ℓ²(F_p^×) the constant mode carries the mean v̄ = ψ(p−1)/(p−1), the nontrivial characters carry v − v̄·1, orthonormal; S χ_j = ω^j χ_j ([approx], floating point) |
| A8 | Theorem `hp` (iv), Definition `jacobi` | self-adjointness is free: any real multiset is the spectrum of a real-symmetric tridiagonal matrix (Lanczos on ten heights; [approx], floating point) |
| A9 | Proposition `ground` | the Ramanujan sum c_p(n) = Σ_a ω^{an} ≡ −1 for every n ≢ 0 (mod p), in F_q with q ≡ 1 (mod p) and ω of order p (EXACT) |
| A10 | Definition `shells` (the shared quarter-turn core) | Q₄ ⊂ both cycles; on the pair (13, 233) the projection C_{Ω−1} → C_{p−1} does not exist (12 ∤ 232) |
| A11 | Proposition `coincide` | frame coincidence below √p: residues, window products and primality agree between F_p and the Carrier chart F_Ω (Ω the least prime ≡ 1 mod 4 above p²), on the five shells and on 1009, 10009 |

Ledger rows witnessed: 20:B1–B11, 20:E1, 20:E9, 20:E12–E13 (block A of the package is the source of rows B2, B4–B11, E1, E12, E13 and of V1).""")
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
| B4 | Definition `deframe` | the horizon-length main sum has one sign change per zero on [10, 55], each within 0.5 of γ_n | [approx] |

Ledger rows: 20:D2 (B1), 20:D3 (B2), 20:B8 (B3), 20:D4 (B4).""")
code("import b_deframe; b_deframe.run(); show('fig_deframing')")

md("""## Block C — the spectrum from the prime side, ζ never evaluated  (`c_primeside.py`, [approx])
Inputs: the sieved comb {Λ(n)}, its logarithms, the raised-cosine taper, and θ(T) from log Γ. The raw count Ñ_N(T) = θ(T)/π + 1 + S_comb(T)
carries the explicit pole term of the smoothed explicit formula (Proposition `combformula`) and has no limit in N; the pole-corrected
count N̂_N(T) = Ñ_N(T) − (1/π) Im[Π_N(½+iT) + log((s−1)/s)] settles. Both are computed from {Λ(n)}, θ and elementary functions.

| id | paper statement | predicate |
|---|---|---|
| C1 | Numerical Observation `primespec` | the scale-spectrum \\|Σ_N(γ)\\| of the N = 10⁶ comb peaks at the first six heights (paper: 14.14, 21.02, 25.02, 30.40, 32.96, 37.57) within 0.03 |
| C2 | Numerical Observation `trace` | the raw secular condition Ñ_N(T) = n − ½ recovers the first ten heights: mean 4.4×10⁻⁵, max 1.5×10⁻⁴ (γ₁) at N = 10⁶; 3.6×10⁻⁴ at 10³, 6×10⁻⁵ at 10⁵ |
| C2b | Proposition `combformula`, Numerical Observation `trace` | the pole-corrected secular condition N̂_N(T) = n − ½: mean 3.4×10⁻⁵ (max 6.6×10⁻⁵) at 10⁶, 2.3×10⁻⁵ at 10⁷, 1.3×10⁻⁵ (max 2.8×10⁻⁵) at 10⁸, falling with depth |
| C2c | Numerical Observation `trace` | the raw condition does not sharpen past 10⁷: mean 2.7×10⁻⁵ at 10⁷, 4.2×10⁻⁵ at 10⁸, the γ₁ error growing 1.5×10⁻⁴ → 2.6×10⁻⁴ — the pole term |
| C3 | Numerical Observation `matrix` | the colleague matrix of the Chebyshev fit of cos(π N̂_N) on [10, 52], N = 10⁶: mean error 4.8×10⁻⁵ at dimension 520, 3.5×10⁻⁵ by 620 |
| C4 | Definition `jacobi`, Numerical Observation `jacobi` | the comb-built Jacobi matrix of the corrected roots: real-symmetric tridiagonal, eigenvalues = roots to 10⁻¹², the stated a, b coefficients, heights to 3.4×10⁻⁵ |
| C5 | Proposition `gauge` | the additive injection −i d/du + V_comb is gauge-trivial: spacing standard deviation 0.11 of the mean (0.08 on a mean spacing 0.72) against 0.39 of the mean for the heights |

Ledger rows: 20:E5 (C1), 20:E6 (C2, C2b, C2c), 20:E8 (C2b, C3), 20:E9 (C4), 20:E10 (C5). The 10⁸ comb of C2b/C2c is skipped in FAST mode.""")
code("import c_primeside; c_primeside.run(); show('fig_prime_spectrum'); show('fig_operator_spectrum')")

md("""### Block C, continued — random-matrix statistics of the target spectrum  (`c_gue.py`)
Definition `specmap` reads the heights as the target spectrum ρ ↦ −i(ρ − ½); the heights here are computed independently (mpmath `zetazero`).

| id | paper statement | predicate | kind |
|---|---|---|---|
| C6 | Numerical Observation `gue` | unfolded spacings of the first 240 zeros: P(s < ½) = 0.05 (GUE ≈ 0.12, Poisson ≈ 0.39), variance 0.13 (GUE ≈ 0.18, Poisson 1) | [approx] |
| C6b | Figure `hp` (right) | the count N(T) lies on the Berry–Keating (T/2π)(log(T/2π) − 1) + 7/8: density (1/2π) log p at T = 2πp | [chart] |

Ledger rows: 20:E11 (C6), 20:E3 (C6b).""")
code("import c_gue; c_gue.run(); show('fig_hilbert_polya')")

md("""### Block C, continued — the χ-twisted comb  (`c_chi.py`, [approx])
Proposition `chi` (both cases), Numerical Observation `chi`: the real character χ = χ_{−4}, θ_χ(t) = Im log Γ(¾ + it/2) + (t/2) log(4/π),
N_χ = θ_χ/π + S^χ_comb with no pole term; validation arm L(s, χ) = 4^{−s}[ζ(s, ¼) − ζ(s, ¾)] via Hurwitz zeta; then the complex character
χ mod 5 with χ(2) = i, the count taken as a difference from height 0 and the root number's half-phase in the validation arm.

| id | predicate |
|---|---|
| C7a | N_χ at the first six zeros of L(s, χ_{−4}) reads 0.4997, 1.4998, 2.4999, 3.4999, 4.4999, 5.4998; the completed L is real on the line |
| C7b | the twisted secular condition with the N = 10⁶ comb, L never evaluated, recovers 6.0209, 10.2438, 12.9881, 16.3426, 18.2920, 21.4506 to mean error 8.6×10⁻⁵ |
| C7c | the complex character χ mod 5, χ(2) = i (odd): the half-phase W(χ)^{−1/2}Λ(½+it, χ) is real on the line; the twisted count (1/π)[θ_χ(T) − θ_χ(0)] + (1/π) Im[Σ^χ_w(½+iT) − Σ^χ_w(½)], no pole term, reads 1 … 14 midway between the fifteen zeros below 40; its half-integer crossings, bracketed by the count alone, recover the fifteen heights 6.1836 … 37.2720 to mean error 8.0×10⁻⁵ (max 2.0×10⁻⁴), L never evaluated — ledger 20:E16 |

Ledger rows: 20:E14–E16 (E16 by C7c).""")
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
| D2c | Numerical Observation `dh` | the secular condition on the Λ_f comb lands two "on-line" roots on the phantom height, the upward crossings of the levels 43.5 and 44.5: 85.63/85.76 (10⁵), 85.65/85.75 (4×10⁵); at 4×10⁵ the unsettled count also swings through 42.5 and 45.5 |
| D2d | Numerical Observation `dh` | the raw DH count at 85.9 drifts 45.14 → 45.73 over depths 5×10⁴ … 8×10⁵; 42.64 … 42.73 at 85.3; stable at 60.3 (28.005 ± 0.002) and 84.0 (43.00 ± 0.01) |
| D2e | Numerical Observation `dh` | the ζ comb at the pole: t = 1 reads +0.09, −0.26, +0.36, −0.08, −0.81, −1.42, −1.46 at depths 10⁴ … 8×10⁷; t = 5, 10 within ±0.02, ±0.003; t = 15 within 2×10⁻³ of 1; t = 30 from 3.04 to 2.998; t = 50.3 within 10⁻² of 10 |
| D2f | Proposition `combformula`, Numerical Observation `dh` | the pole-corrected ζ count at t = 1: 0.0051, 0.0032, 0.0022, 0.0016, 0.0015, 0.0013, 0.0012 at the same depths (exact 0), falling monotonically; t = 5, 10 within 4×10⁻⁴ from 10⁶ on |
| D2g | Remark `combsettle`, Numerical Observation `dh` | the DH drift is the zero term of the off-line zero ρ₀: corrected by it and its constant the count reads 44.960 → 44.972 at 85.9 (raw 45.14 → 45.73; exact 45) and 43.035 → 43.022 at 85.3 (exact 43), monotone |
| D3 | Proposition `combformula` | validation arm: Re(Σ_w − Π_N − log((s−1)/s)) → log \\|ζ(½+it)\\| (mpmath) at t = 1, 5, 10, 15, 30, the error falling with depth (0.0049 at t = 1, 8×10⁷) |
| D4 | Theorem `turing` (frame-exact inputs) | on the shells p = 97, 1009, 4801 (primes ≡ 1 mod 4; T = 2πp) the raw count from the frame-exact comb of depth ⌊√p⌋ = 9, 31, 69 evaluated midway between consecutive zeros just below the ceiling (the test heights chosen with the validation arm), rounds to the exact N(t) (mpmath `nzeros`) at every midpoint: maximum deviation 0.079, 0.107, 0.164 (within 0.08, 0.11, 0.17); the 10⁶ comb within 0.002 |

Ledger rows: 20:F1 (D1, D4), 20:F3 (D2a, D2b), 20:F4 (D2c, D2d, D2g), 20:F5 (D2e, D2f), 20:F8 (D2f, D2g, D3).""")
code("import d_classification; d_classification.run(); show('fig_dh')")

md("""## Block E — resonance, antipode, horizon-scale resolution, square-root cancellation  (`e_resonance.py`)
The units-chart side: Ramanujan sums as the standing waves of the additive meridian, the Möbius-weighted resonance and its limit.

| id | paper statement | predicate | kind |
|---|---|---|---|
| E1a | Theorem `resonance` (b) | Λ = μ ∗ log on the divisor lattice: symbolic for n ≤ 300 (sympy), floating point for n ≤ 5000 | EXACT |
| E1b | Theorem `resonance` (a), (c) | Hardy: R_L(n) → (φ(n)/n) Λ(n) (Cesàro mean to L = 4000); the intertwiner (n/φ(n)) R → Λ = log ℓ | [approx] |
| E1c | Definition `resonance`, Figure `emergence` | Ψ_L(N) = Σ_{n≤N} (n/φ(n)) R_L(n) → ψ(N): the maximal deviation on N ≤ 30 falls over L = 15, 60, 240 | [approx] |
| E2a | Numerical Observation `antipode` | per-mode energy μ²(q)/φ(q) = 1, ½, ¼, ⅙ at q = 2, 3, 5, 7; unique global maximum at the antipode q = 2 | EXACT |
| E2b | Numerical Observation `antipode` | the additive-transform band energy of the prime indicator on Z/10007 (Parseval-normalised, bins within 3 of a/q) peaks at the antipode and follows 1/φ(q): 1153 > 592 > 301 > 205 | [approx] |
| E3 | Numerical Observation `horizon` | the resolving threshold L*(H) exists for H = 6 … 50 and tracks the horizon: L* < 6H ≪ H² | [approx] |
| E4 | Proposition `flat`, Numerical Observation `flat` | the maximal chart-mode correlation with the primes is a small multiple of the 1/√(p−2) floor: 0.077 vs 0.0315 at p = 1009 (2.4×), 0.0087 vs 0.0032 over the modes of p = 100049 (2.7×); the resonance correlates 0.90 | [approx] |

Ledger rows: 20:C2 (E1a, E1b), 20:C3 (E1c), 20:B11 (E2a, E2b), 20:C4 (E3), 20:C6 (E4).""")
code("import e_resonance; e_resonance.run(); show('fig_obstruction'); show('fig_emergence_frc')")

md("""## Summary
Writes `results.json` (one record per check: id, ledger rows, label, kind, PASS/FAIL, detail) and raises if any check failed.""")
code("""ok = rhcommon.summary(write=True)
kinds = {}
for r in rhcommon.RESULTS: kinds[r["kind"]] = kinds.get(r["kind"], 0) + 1
print("by kind:", ", ".join(f"{k} {v}" for k, v in sorted(kinds.items())))
failed = [r["id"] for r in rhcommon.RESULTS if not r["ok"]]
assert ok, f"FAILED predicates: {failed}"
print("all predicates pass; figures in figures/, records in results.json")""")

nb.cells = cells
for name in ("20-rh-main.ipynb", "20-rh-validate.ipynb"):
    nbf.write(nb, name)
    print("wrote", name, "with", len(cells), "cells")
