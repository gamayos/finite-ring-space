"""Builds 6-fourier-main.ipynb (the Colab driver of the 6-fourier validation package). Run: python3 make_notebook.py"""
import json

NB = "6-fourier-main.ipynb"
COLAB = f"https://colab.research.google.com/github/gamayos/finite-ring-space/blob/main/src/6-fourier/{NB}"
cells = []
def md(s): cells.append({"cell_type": "markdown", "metadata": {}, "source": s})
def code(s): cells.append({"cell_type": "code", "metadata": {}, "execution_count": None, "outputs": [], "source": s})

md(f"""[![Open In Colab](https://colab.research.google.com/assets/colab-badge.svg)]({COLAB})

## Scale-Shift and Fractional Fourier Transform as Rotations over Finite Holographic Substrate (Akhtman, 2026)

**Validation Package.** `finite-ring-space/src/6-fourier` — five block scripts driven by this notebook, 36 checks. Every cell below names the labelled
statements of the paper it checks (`Theorem`, `Lemma`, `Proposition`, `Remark`, `Corollary`, `Example`, the one `Conjecture`, Table `tab:checks` — by
their `\\label` as printed in the paper), lists the paper's ledger rows the block witnesses (the paper's Appendix A, "Machine verification and predicate
ledger", rows cited as `6:XN`, 48 rows in blocks A–F, V, Y; public copy at `docs/6-fourier/6-fourier-ledger.html`; the ledger's source column names
the witness script, the check ids are listed on the public page from `results.json`), and gives the master-ledger rows
of the corpus reached through them (`00:C2` scale-shift duality and the fractional Fourier cycle, `00:C14` the quarter-turn as the odd member of the
±√−1 pair, `00:C7` the conjugate reframing on the transform layer). The package regenerates the paper's one numerical figure
(`figures/entropy-cycle-f13`); the framed complex-plane rendering `f13-C` is a drawing, not a computation, and its generator is kept as is.

**Kinds.** `EXACT` checks are integer-pinned computations in F_p (a pass is a proof on the tested instances); `[approx]` checks compare a
floating-point observation with the value the paper states, to a stated tolerance — they occur in block E only, where the cyclotomic
observer readout of Definition `readout` realises the family on ℂⁿ. Blocks A–D are exact modular arithmetic throughout: the six shells of
Table `tab:checks`, p = 5, 13, 17, 29, 37, 41, with every primitive frame of each where a statement ranges over frames.

**Run.** Cell by cell, or *Runtime → Run all*; ≈ 10 s on Colab. The last cell writes `results.json` and fails loudly if any check fails.""")

code("""# --- environment: clone the package if this notebook is not already running inside it (Colab). numpy and
# matplotlib are standard on Colab; nothing else is needed.
import os
if not os.path.exists("fcommon.py"):
    if not os.path.exists("finite-ring-space"):
        !git clone --filter=blob:none --sparse https://github.com/gamayos/finite-ring-space.git
        os.chdir("finite-ring-space")
        !git sparse-checkout set src/6-fourier
        os.chdir("src/6-fourier")
    else:
        os.chdir("finite-ring-space/src/6-fourier")
!pip install -q --disable-pip-version-check "numpy>=1.24" "matplotlib>=3.7"
print("working directory:", os.path.join(*os.getcwd().split(os.sep)[-3:]))""")

code("""import os, importlib
os.environ["FOURIER_FIGDIR"] = "figures"
import fcommon
importlib.reload(fcommon)         # a fresh registry if the notebook is re-run
from IPython.display import Image, display
def show(name): display(Image(filename=f"figures/{name}.png"))
print("shells:", fcommon.SHELLS)""")

md("""## Block A — the frame datum and the shell Fourier operator  (`a_shell.py`, EXACT; master ledger **00:C2**, **00:C14**)
The framed shell F_p(t; 0, 1, g): p = 4κ+1, g the generator of Table `tab:checks`, the oriented quarter-turn i = −g^κ, π = 2κ, e = g^i; the
shell Fourier matrix W_{kj} = g^{jk} and its normalisation F = iW.

| id | paper statement | predicate |
|---|---|---|
| A1 | §3 shell data (`it-def`, `capacity`), Table `tab:checks` | p = 4κ+1, g the smallest primitive root, i = −g^κ = g^{−κ}, i² ≡ −1, π = 2κ, 2π ≡ −1, g^π ≡ −1, −π ≡ 2⁻¹, e = g^i; the table's (κ, g, i) on all six shells |
| A2 | §3 (the Euler identity); **00:C14** | e^{iπ} = g^{2κ(i mod 2)} ≡ −1 exactly when the quarter-turn residue is odd; the conjugate reframing (g, i) ↦ (g⁻¹, −i) toggles the parity, so exactly one member of each conjugate pair carries e^{iπ} ≡ −1 — every primitive frame of the six shells; anchor F_13: i = 5, 6^{iπ} ≡ −1 |
| A3 | Remark `gt-covariance` | g' = g^u: the quarter-turn flips only on u ≡ 3 (mod 4); e' = g^{ui} ≠ e iff i(u−1) ≢ 0 (mod 4κ); p = 13, u = 5: e' = 2 ≠ 6 |
| A4 | Lemma `W-square`, Proposition `F-cycle`, Table `tab:checks`; **00:C2** | W² = −J, (iW)² = J, (iW)⁴ = I on the six shells |
| A5 | Remark `unitary-norm` | the square roots of 1/n ≡ −1 in F_p are exactly ±i: (cW)² = J iff c = ±i |
| A6 | Lemma `JF-decomp` | WJ = JW, FJ = JF; dim V⁺ = 2κ+1, dim V⁻ = 2κ−1 |

Ledger rows witnessed: 6:B1–B3, 6:B5–B7 (block B of the paper; master 00:C14 through B2, 00:C2 through B5).""")
code("import a_shell; a_shell.run()")

md("""## Block B — the fractional family F^[s] = Σ_ℓ g^{−ℓs} Π_ℓ  (`b_fractional.py`, EXACT; **00:C2**, **00:C7**)
Definition `FRC-FrFT-def`: the projectors Π_ℓ = ¼ Σ_r i^{−ℓr} F^r and the principal framed character lift.

| id | paper statement | predicate |
|---|---|---|
| B1 | Lemma `projectors` | Π_ℓ² = Π_ℓ, Π_ℓ Π_m = 0, Σ Π_ℓ = I, F Π_ℓ = i^ℓ Π_ℓ |
| B2 | Theorem `FRC-FrFT` (`additivity`); **00:C2** | F^[s+r] = F^[s] F^[r] on every pair (s, r) ∈ Z_{4κ}² — 4096 pairs |
| B3 | Theorem `FRC-FrFT` (`cardinal-FrFT`); **00:C2** | F^[0] = I, F^[κ] = F, F^[2κ] = J, F^[3κ] = F⁻¹, F^[4κ] = I; (F^[1])^κ = F |
| B4 | Theorem `faithful` | s ↦ F^[s] injective on Z_{4κ}, p = 5 included |
| B5 | Lemma `multiplicity` | m_ℓ = rank Π_ℓ = dim ker(F − i^ℓ I); m_0+m_2 = 2κ+1, m_1+m_3 = 2κ−1; m_0, m_2 ≥ 1; m_1, m_3 ≥ 1 for κ ≥ 2; at p = 5 one odd projector vanishes |
| B6 | Remark `multiplicities` | p = 13: (3,3,4,2) with Tr F = 4 at g = 2, (4,2,3,3) with Tr F = 9 at g = 6; m ↦ um conjugates F(g) to F(g^{u²}) by a permutation |
| B7 | Theorem `multiplicity` | G = Σ g^{k²} = ε(1+i); the two patterns; ε(g⁻¹) = −ε(g); ε(g^u) = (κ/u) ε(g); classes equally populated; the 38 primitive frames of p ∈ {5,13,17,29,37} (and the 16 of p = 41); p = 5: (2,0,1,1) at g = 2, (1,1,2,0) at g = 3 |
| B8 | Theorem `multiplicity` (proof) | G G* = −2, G² = 2i, Tr F = iG, Tr F² = 2, Tr F³ = iG*, m_ℓ ≡ ¼ Σ_r i^{−ℓr} Tr F^r (mod p) |
| B9 | Remark `classification` | every exponent lift a_ℓ ≡ ℓ (mod 4) is additive with the cardinal skeleton; the chart g^5 at p = 29 (u² ≢ 1 mod 28) does not commute with F |
| B10 | Remark `gt-covariance`; **00:C7** (transform layer) | the conjugate frame (g⁻¹, −i) keeps the operator relations, cardinal values, additivity and faithfulness; its multiplicity tuple is the other pattern; exactly F' = −F⁻¹ and Π'_ℓ = Π_{ℓ+2} |

Ledger rows witnessed: 6:C2–C9 (master 00:C2 through C3, 00:C7 through C9).""")
code("import b_fractional; b_fractional.run()")

md("""## Block C — representation domains and the coordinate-side zoom  (`c_domains.py`, EXACT; **00:C2**)
Definition `domain`: B_s = F^[s] B_0; Definition `scale-map`: S_r(x) = g^r x on the meridians M_m = {a g^m : a ∈ I_p}.

| id | paper statement | predicate |
|---|---|---|
| C1 | Definition `domain` | every F^[s] has full rank; the eigenvalues g^{−ℓs} are nonzero |
| C2 | Corollary `distinct-domains` | the 4κ framed bases are pairwise distinct |
| C3 | Remark `ordered-bases` | F^[s+2κ] = F^[s] J: 4κ framed domains, exactly 2κ unordered measurement bases |
| C4 | Proposition `meridian-scale`; **00:C2** | S_r(M_m) = M_{m+r} on every (m, r), as ordered lists |
| C5 | Corollary `effective-step`, Remark `framed-rational` | consecutive entries of M_m differ by g^m; S_{r+(p−1)} = S_r |
| C6 | Example `zoom-13`, Theorem `zoom`, Remark `two-layers` | the printed ladder M_0 … M_3 at steps 1, 2, 4, 8; the no-wrap window w g^r < p (w = π = 6) holds for r ≤ 1, the listing wraps from M_2 |

Ledger rows witnessed: 6:D1, 6:D2, 6:D4, 6:D5 (master 00:C2 through D4).""")
code("import c_domains; c_domains.run()")

md("""## Block D — the Weil dictionary and the operator-level comparison  (`d_weil.py`, EXACT)
The rotation R_s = [[c_s, −d_s], [d_s, c_s]] with z_s = g^{−s}; the exponent shift σ and the modulation D_1 = diag(g^k) on V.

| id | paper statement | predicate |
|---|---|---|
| D1 | Lemma `Rs-rotation` | c_s² + d_s² = 1, det R_s = 1 |
| D2 | Proposition `rotation-isom` | R_{s+r} = R_s R_r, injective, \\|SO(2, F_p)\\| = p − 1: an isomorphism Z_{4κ} ≅ SO(2, F_p) |
| D3 | Theorem `Weil-equivalence`, Table `tab:checks` | R_0 = I, R_κ = [[0,−1],[1,0]], R_{2κ} = −I, R_{3κ} = w⁻¹; z_κ = i |
| D4 | Proposition `nogo` | σ has the 4κ simple eigenvalues F_p^×; F^[1] has at most four; ⟨σ⟩ and ⟨F^[1]⟩ not conjugate for κ ≥ 2 |
| D5 | Proposition `charsector` | E_1 ≠ 0 for κ ≥ 2; F^[s] = g^{−s} on E_1; F^[s] T_v = T_v S_{−s}; R_s (1,−i)ᵀ = g^{−s} (1,−i)ᵀ |
| D6 | Proposition `heisenberg`, eq. `conj-expansion` | F σ F⁻¹ = D_1, F D_1 F⁻¹ = σ⁻¹; F^r σ = σ_r F^r; F^[s] = Σ_r c_r(s) F^r with c_r(s) = ¼ Σ_ℓ (g^{rκ−s})^ℓ |
| D7 | Conjecture `monomial` (the sweep) | F^[s] σ F^[s]⁻¹ monomial exactly at the four cardinal indices, non-monomial at all 112 intermediate indices of p ∈ {13, 17, 29, 37, 41} |

Ledger rows witnessed: 6:E2, 6:E3, 6:E5–E7 (the sweep of E7 is the verified half of the hypothesis 6:Y1).""")
code("import d_weil; d_weil.run()")

md("""## Block E — the cyclotomic observer readout and the entropy cycle  (`e_entropy.py`, EXACT / [approx])
Definition `readout`: the readout algebra A = Z[1/4n, X, Y, Y⁻¹]/(Φ_n(X), Y² − n) with the continuum chart σ_C (X ↦ ζ_n, Y ↦ +√n) and the
framed reduction ρ (X ↦ g, Y ↦ −i); on ℂⁿ the family is the canonical DFT projector family, and the Born vector of F^[s] δ_j gives H(s).

| id | paper statement | predicate | kind |
|---|---|---|---|
| E1 | Definition `readout` | Ĝ² = 2n X^κ modulo Φ_n(X), exact integer polynomial arithmetic; σ_C: (Σ ζ^{k²})² = 2n i; ρ: G² = 2i in F_p | EXACT |
| E2 | Proposition `entropy` | H(0) = H(2κ) = 0, H(κ) = H(3κ) = log n for every δ_j | [approx] |
| E3 | Proposition `entropy` | B_0, B_κ mutually unbiased; H_{B_0} + H_{B_κ} ≥ log n on random states, saturated by δ_j; the comb (δ_0+δ_6)/√2 at n = 12 gives log 2 + log 6 = log 12 | [approx] |
| E4 | Proposition `closedform` | the two-valued readout p_0 = 1 − (n−1)t_s/n, p_j = t_s/n, t_s = (2−ζ^{2s}−ζ^{−2s})/4 = sin²(πs/2κ); the closed-form H(s); strictly increasing on [0, κ]; period 2κ | [approx] |
| E5 | §9 table, Figure `entropy13` | p = 13: H(s)/log n = 0, .44, .91, 1, .91, .44, … ; regenerates `figures/entropy-cycle-f13` | [approx] |
| E6 | Remark `input-dep` | δ_1 at p = 13: H(1)/log n = 0.55 against 0.44; δ_j meets the odd projectors iff j ∉ {0, 2κ} | [approx] |
| E7 | Definition `readout` (the Galois twist) | X ↦ ζ^u relabels the δ_0 curve by s ↦ us on every unit u; the cardinal values of every δ_j are twist-invariant; u = −1 relabels every δ_j; δ_1 at n = 12 under u = 5: 0.55 ↦ 0.44 | [approx] |

Ledger rows witnessed: 6:F2–F7.""")
code("import e_entropy; e_entropy.run(); show('entropy-cycle-f13')")

md("""## Summary
Writes `results.json` (one record per check: id, the paper statement(s) decided and the master row witnessed, label, kind, PASS/FAIL, detail)
and raises if any check failed.""")
code("""ok = fcommon.summary(write=True)
kinds = {}
for r in fcommon.RESULTS: kinds[r["kind"]] = kinds.get(r["kind"], 0) + 1
print("by kind:", ", ".join(f"{k} {v}" for k, v in sorted(kinds.items())))
failed = [r["id"] for r in fcommon.RESULTS if not r["ok"]]
assert ok, f"FAILED checks: {failed}"
print("all checks pass; figure in figures/, records in results.json")""")

for k, c in enumerate(cells):
    c["id"] = f"cell-{k}"
nb = {"cells": cells, "nbformat": 4, "nbformat_minor": 5,
      "metadata": {"kernelspec": {"display_name": "Python 3", "language": "python", "name": "python3"},
                   "language_info": {"name": "python"}, "colab": {"provenance": [], "toc_visible": True}}}
try:
    import nbformat
    nbf = nbformat.from_dict(nb)
    nbformat.validate(nbf)
    nbformat.write(nbf, NB)
except ImportError:
    with open(NB, "w") as f:
        json.dump(nb, f, indent=1, ensure_ascii=False)
print(f"wrote {NB} with {len(cells)} cells")
