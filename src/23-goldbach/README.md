# Validation suite — *Binary Goldbach over Finite Substrate*

Exact-arithmetic verification of the quantitative claims in the manuscript
(`../main.tex`). Every substrate-native claim is checked in **framed-rational**
arithmetic — exact integer, rational, and cyclotomic computation, with no floating
point, no tolerances, and no limits. Field elements are residues below the
Subject-shell modulus `P`; derived integer aggregates (e.g. the additive energy
`Σ r(n)²`) are exact and may exceed `P`, staying within the Carrier `Ω`. The
classical second-moment analysis (which carries the transcendental von Mangoldt
weight `log p`) is kept strictly separate as a labelled *continuum comparison*.

## Contents

| File | Role | Checks |
|---|---|---|
| `goldbach.py` | The main suite: the graded chain of finite results (§2–§9 of the paper). | 41 |
| `longitudinal.py` | A probe of the longitudinal (additive↔multiplicative) transform — the non-linear / Kloosterman route to the residue. Mechanism only, not a proof. | 5 |

## Requirements

- Python ≥ 3.8
- `numpy` (used only for exact `int64` convolution / correlation)
- `sympy` (primes, factorisation, primitive roots, exact cyclotomic arithmetic)

```bash
pip install numpy sympy
```

## Running

```bash
python3 goldbach.py        # prints PASS lines; asserts on any failure
python3 longitudinal.py
```

Each script is self-contained (no reference to the wider corpus), deterministic,
and ends with a summary line. A non-zero exit or an `AssertionError` means a check
failed. Expected tail of `goldbach.py`:

```
goldbach: all checks passed (41 checks)
Part I framed-exact (integer/rational/cyclotomic, no floats); Part II continuum comparison.
```

## The framed-rational discipline

`goldbach.py` is split into two parts.

**Part I — framed-exact (substrate-native).** Integer, rational (`fractions.Fraction`),
and cyclotomic arithmetic only. No `numpy.fft`, no `numpy.exp/log/sqrt`, no floating-point
tolerances. Field elements are residues below the Subject-shell modulus `P`; exact derived
aggregates may exceed `P` but stay within the Carrier `Ω`. The cyclotomic magnitudes are
established through their exact ingredients rather than by floating evaluation:
`|g(χ)|² = P` follows from the additive and multiplicative orthogonality relations
(verified as exact bijections), and the Jacobi-sum form is confirmed to reproduce the
integer count `r(n)` **exactly** in `ℚ(ζ_{P−1})` (zero imaginary part) at small `P`.

**Part II — continuum comparison.** The classical Hardy–Littlewood / Montgomery–Vaughan
second moment uses the von Mangoldt weight `log p` — a transcendental, the additive→scale
measure Jacobian — so it is **not** a substrate-exactness claim. It is computed in floating
point *by design*, as the comparison chart against which the native results are read, and is
labelled as such in both the script and the paper's reproducibility appendix.

## Check-to-claim map (`goldbach.py`)

Tags `G1…G17` match the reproducibility appendix of the paper.

**Part I (framed-exact):**

- `G1` — the circle method is an exact finite identity (`eq:identity`): the integer
  group-ring square in `ℤ[ℤ_P]` equals an independent ordered-pair count.
- `G2` — the faithful window is admissible: `2M < P` (wrap-free) and primality is exact on `[2,M]`
  via trial factors `≤ isqrt(M)` (Lemma, *Faithfulness*).
- `G3` — finite Goldbach positivity `G(P)`: `r(n) > 0` for every even `n ∈ [4,M]`, to `P = 100003`.
- `G4` — the singular-series floor: the exact rational `∏_{p|n,p>2}(p−1)/(p−2) ≥ 1` (`= 1` iff a power of 2),
  and the major-term comet ratio `→ 2` (Proposition, *Exact floor*).
- `G5` — the exact additive-energy identity `Σ r(n)² = Σ d(m)²` (Proposition, *Exact Parseval variance*).
- `G8` — the no-symmetry lemma: the additive reflection has `W ∩ (−W) = ∅` (exact); the scaling/inversion overlaps sit at the random baseline (observed).
- `G10` — the Liouville endpoint sum `|Σ λ(m)| ≤ 2√M` at the listed shells (observed factorisation-parity diagnostic, not shell-uniform).
- `G11` — the exact mod-4 sector decomposition (Proposition, *Exact mod-4 decomposition*).
- `G12` — the Gaussian `D₄` lift: split primes `p ≡ 1 (4)` are norms with a full equal-norm orbit.
- `G13` — the quarter-turn symmetry on `V_P = F_P²`: the prime-norm indicator is `J`-invariant, so
  `S₂(Jξ) = S₂(ξ)` identically (a symmetry of the lifted array).
- `G16` — scale-periodic exactness: `|g(χ)|² = P` from the additive/multiplicative orthogonality bijections.
- `G17` — the Jacobi-sum spectral form (Theorem): `r(n)` is reproduced exactly in `ℚ(ζ_{P−1})`
  (with `|J| = √P` only for `χ,χ′,χχ′` nontrivial, and the exact boundary terms otherwise); the
  reflection-even/odd sectors at `P=101, n=20` sum to `r(n)` (`r_ee=3, r_oo=−1`), even–even `≥ 0`.

**Part II (continuum comparison):**

- `G6/G7` — von Mangoldt main-term tracking and the `D`-corrected Montgomery–Vaughan exceptional-set
  bound with threshold `δ = min(ρ−D)` (almost-all even `n` are sums of two primes).
- `G9` — the prime-only moment-hierarchy reduction: the supremum `μ_G = max|R_pp−ρ|/ρ = 0.909 < 1`
  and the `D`-corrected bulk moment `B₂ < 1`.
- `G14` — the exact conservation sum rule `Σ r(n) = |W|²` (integer); the oscillating multiplier and
  the insufficient top gap (`≈ 0.11`) are the comparison diagnosis.
- `G15` — the Friedlander–Iwaniec diagnostic: square-root cancellation present, binary `L²`-mass deficit growing.
- `G16b` — the Chebyshev flattening `Σ_{p≤M} log p / M → 1` (`log p` as the scale Jacobian).

## `longitudinal.py`

A mechanism probe for the non-linear (longitudinal, additive↔multiplicative) route:

- `L1` — the longitudinal object is Kloosterman (exact reconstruction of `N(s)`).
- `L2` — the Weil bound `|K| ≤ 2√P` (square-root cancellation = function-field RH).
- `L3` — the normalised traces obey the Sato–Tate / Catalan moments `1, 2, 5` — the same Frobenius
  statistics the programme realises for the Riemann zeros.
- `L4` — base-level averaged cancellation of complete Kloosterman sums over the modulus.

**Scope.** `L1–L3` confirm the mechanism is real and FRC-native; `L4` measures the classically
accessible averaging cancellation. None of this proves binary Goldbach — the binary-sufficiency
question lives in the finer incomplete/bilinear regime and is open. This script tests the
mechanism, not the conjecture; the non-linear development is carried further in the scale-domain
companion.

## Scope

The suite verifies an **exact finite reformulation**, an **almost-all theorem** with explicit
finite constants, and a **native spectral form** of the problem. It does **not** prove the binary
Goldbach conjecture: the terminal parity-sector positivity (`G17`) is exact, finite, and open.
