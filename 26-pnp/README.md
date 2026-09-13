# Validation scripts — 26-pnp

Machine checks for the load-bearing claims of *$\mathrm{P}$ versus $\mathrm{NP}$ as the
computational face of the horizon clause*. Each script is standalone, prints its own
pass/fail lines, and names the paper section it anchors.

Two registers are kept separate. **Exact** checks carry the structural facts of the
argument: they run float-free over the finite carrier (integer / `Fraction` / `sympy`
symbolic) with no random number generator, so a pass is a proof on the tested instances.
**Empirical** checks illustrate scaling only: they use wall-clock timing or floating-point
arithmetic, are seeded where random, and stand as evidence, not as load-bearing steps.

## Scripts

| Script | Paper section | Validates | Register |
|---|---|---|---|
| `closure_pnp.py` | §`sec:closure`, §`sec:owf` | The arithmetic ladder closes at four roles; ascent is counting along the orbit of the fourth (power) role; the one-way step is exactly the inverse of that last role (T1–T4). | Exact, no RNG |
| `chart_localization.py` | §`sec:pnp` | The localizing chart: the witness is named in `ell` bits but its counting distance is up to `2^ell`. Short to name is not short to find. | Exact, deterministic |
| `longitudinal_turn.py` | §`sec:quarterturns`, §`sec:transforms` | The longitudinal turn is the multiplicative DFT diagonalising the scale shift; the Gauss sum couples spectrum to frequency (`|g(χ)|²=P`); the two turns are the classical/quantum line. | Exact (18/18), one symbolic shadow |
| `dlog_asymmetry.py` | §`sec:owf` | Ascent (`g^j`) is flat in `log P`; descent (`dlog`) scales as `√P`. The hyperoperation asymmetry is the candidate source of the gap. | Empirical (timing) |
| `transform_charts.py` | §`sec:transforms` | Representation-relativity: the same convolution target is far in the position chart (`O(n²)`) and near in the Fourier chart (`O(n log n)`); the diagonalising transform is itself in P. | Empirical (numpy, seeded) |

## Running

```sh
python3 closure_pnp.py        # 4 checks, finite, no RNG
python3 chart_localization.py # exact bijection + gap report
python3 longitudinal_turn.py  # 18/18 checks
python3 dlog_asymmetry.py     # prints ascent/descent scaling fit
python3 transform_charts.py   # prints position/Fourier scaling fit
```

Dependencies: `sympy` (closure, longitudinal turn, dlog), `numpy` (transform charts).
`chart_localization.py` uses the standard library only.

## Expected results

```
closure_pnp:       all checks passed (4 checks). FINITE throughout, NO random number generator.
chart_localization: dlog bijection onto 1..P-1; find-steps ~ 2^ell, name-bits/ascent ~ ell.
longitudinal_turn: 18/18 checks pass (finite-field/integer exact; one symbolic continuum-shadow).
dlog_asymmetry:    ascent ~ P^(+0.06) (cost ~ log P); descent ~ P^(+0.52) (cost ~ √P).
transform_charts:  position ~ n^(1.7); Fourier sub-linear; FFT round-trip error ~ 1e-15.
```
