# The ledger's Lean witnesses

[![lean](https://github.com/gamayos/finite-ring-space/actions/workflows/lean.yml/badge.svg)](https://github.com/gamayos/finite-ring-space/actions/workflows/lean.yml)
[![Open In Colab](https://colab.research.google.com/assets/colab-badge.svg)](https://colab.research.google.com/github/gamayos/finite-ring-space/blob/main/lean/frc-lean-main.ipynb)

Rows of the papers' predicate ledgers proved as Lean 4 theorems over Mathlib. A Python witness in
`../src/<package>/` decides a row on the shells it sweeps; a theorem here decides it on every shell — the
statement is quantified over an arbitrary finite field `F` with `Fintype.card F = 4κ + 1`, a primitive root `g`,
and the paper's frame. Instance rows and refutations are decided by `decide` in the kernel.

| module | paper | rows | theorems |
|---|---|---|---|
| `FrcLedger/Fourier.lean` | 6-fourier | B5, B7 (master C2) | `W_sq`, `J_sq`, `W_mul_J_comm`, `quarter_turn_sq`, `shell_relations`, `shell_relations_zmod` |
| `FrcLedger/Algebra.lean` | 1-algebra | B2, B3, B4, C4, D2, D4, D5, E2, F1, G1–G3, V1 | `quarter_turn_exists`, `klein_orbit_four`, `card_fourth_roots`, `quarter_turn`, `affine_frame`, `meridian_involution`, `framed_integer_window`, `scale_periodic`, `complex_chart_zero_divisor`, `no_south_pole`, `s13_quarter_turn`, `euclid_step_count`, `approx_obstruction`, `root_iff_not_coprime`, `tower_density`, `circle_net`, `group_law_defect` |
| `FrcLedger/Geometry.lean` | 2-geometry | B3, C2, D1, D2, D5, D6, E3, F1, F3 | `half_period`, `quarter_turn_order`, `orientation_class`, `euler_identity`, `generator_orbit`, `principal_root`, `dft_inverse`, `euler_characteristic`, `fixed_shell_bound`, `fixed_shell_bound_lt_one`, `fixed_shell_gap`, `fixed_shell_gap_rat` |
| `FrcLedger/Causality.lean` | 3-causality | B2, B3, B5, C2, C3 | `no_causal_root`, `neg_sq_is_square`, `absorb`, `aniso_tx`, `boost_preserves`, `boost_comp`, `boost_orthogonal`, `gamma_ne_zero`, `gamma_velocity`, `velocity_addition` |

Every theorem's docstring opens with the row it decides (`/-- 1:B2 … -/`); the ledger's source column names the
theorem back (`\lean{Algebra.no_south_pole}`); `axioms.log` records, for every declaration, the axioms its proof
depends on. `sorryAx` (an unfinished proof) and `Lean.ofReduceBool` (`native_decide`) fail the build.

## Two libraries, three tiers

FRC is meant to be built from its first principles with no axioms at all, and the ledgers say per declaration
how far a witness is from that: **tier 0** — no axioms: a consequence of the definitions by the kernel's
computation and induction alone (green); **tier 1** — `propext` and `Quot.sound` only, extensionality and
quotients, constructive (teal); **tier 2** — the proof reaches `Classical.choice`: a correct classical theorem,
not yet the finitist witness (amber); red — anything else. On Mathlib every statement about a `Field` or a
`Fintype` is tier 2 by inheritance (its instances reach choice), so `FrcLedger/` — the modules above — is tier 2
throughout, and the substrate is built a second time without it:

**`FrcCore/`** — the shell, the frame and the Euclidean datum from first principles: no Mathlib, no imports beyond
Lean's prelude, and *every declaration prints "does not depend on any axioms"* (`check_core_axioms.py`, log in
`FrcCore/axioms.log`). Residues are `Shell p` with representatives `val < p` (no quotient); the frame
`Frame p κ g` carries `p = 4κ + 1` and a drive `g` that is primitive and generating — both decidable, certified
by `decide` on `𝔽₁₃`, `𝔽₁₇`, `𝔽₂₉`; sums are structural recursions; matrix identities are entrywise. Lean's own
`Nat` lemmas that carry `propext` are re-derived by induction in `FrcCore/Nat.lean`, including the division
algorithm from the definition of `Nat.mod`.

| core module | rows | declarations |
|---|---|---|
| `FrcCore/Nat.lean` | — | the arithmetic: cancellation, `mul_assoc`, the `%`-laws, `mod_spec`, `mod_unique`, subtraction, powers |
| `FrcCore/Pigeonhole.lean` | — | `NoDup`, `erase`, the pigeonhole on `[0, n)` and `[1, n]` |
| `FrcCore/Shell.lean` | — | the ring `Shell p`: the laws, negation by `add_neg`, powers, `neg_one_pow` |
| `FrcCore/Frame.lean` | 00:A8, 00:C1, 00:C7, 00:C14; 1:B3, F1; 2:D1, D2, D5, D6 | `IsPrimitive`, `Generates`, `Frame`, `generates` (the pigeonhole), `pow_inj`, `exists_inv`, `mul_eq_zero`, `sq_eq_one`, `half_period`, `quarter_turn_sq`, `quarter_turn_order`, `orientation_class`, `euler_identity`, `two_pi`, `no_south_pole` |
| `FrcCore/Orbit.lean` | 1:G1; 2:B3 | `generator_orbit`, `fermat` |
| `FrcCore/Sum.lean` | 2:F1, F3, F4, F5; 6:B5, B6, B7 | `sumRange`, `geom_sum_mul`, `principal_root`, `dft_inverse`, `W_sq`, `J_sq`, `F_sq`, `W_J_comm`, `sum_perm`, `dft_eq_polyEval`, `dft_covariance`, the `V = V⁺ ⊕ V⁻` decomposition |
| `FrcCore/Algebra.lean` | 1:B2, B4, C2, C4, D2, D4, D5, E2; 2:D7 | `klein_orbit_four`, `orbit_rep`, `orbit_rep_unique`, `affine_frame_unit`, `Affine.simply_transitive`, `frame_count`, `meridian_involution`, `window_injective`, `window_signed`, the read-backs, `scale_periodic`, `approx_obstruction`, `complex_chart_zero_divisor` |
| `FrcCore/Poly.lean` | 1:G1 | polynomials as coefficient sequences: `eval_mul`, `quot_linear_spec` (synthetic division), `root_bound`, `root_iff_common_factor` |
| `FrcCore/Quaternion.lean` | 1:G5 | the signed window and the framed quaternions: `read_mul`, `quaternion_window` |
| `FrcCore/Causality.lean` | 3:B2, B3, B5, C2, C3; B4, D1 [value] | the square classes and the Lorentzian plane: `no_causal_root`, `neg_sq_is_square`, `absorb`, `aniso_tx`, `norm_mul`, `boost_preserves`, `boost_comp_t`, `boost_comp_x`, `gamma_velocity`, `velocity_addition`; `null13`, `normOne_values` by `decide +kernel` |
| `FrcCore/Geometry.lean` | 2:B4, C2, C4, E3 | `euler_characteristic`, `fixed_shell_bound`, `fixed_shell_gap`, `rho_adj_iff`, `label_covariance` |
| `FrcCore/Complex.lean` | 2:B4, C2, C3 [value] | the orbital shell coded: `closed`, `cellular`; `closed5`, `closed13`, `closed17`, `open13`, `census13`, `counts13` by `decide +kernel` |
| `FrcCore/Instances.lean` | 1:B2, B3; 2:B3, D3, D6 [value] | `frame13`, `frame17a`, `frame17b`, `frame29`, `s13_datum`, `s13_euler`, `s17_orientation`, `s13_klein`, `s13_orbit` — all by `decide` |

The core in one file for the web editor, on plain Lean 4.34.0 (no Mathlib to load, seconds to elaborate):
`https://live.lean-lang.org/#project=lean-v4.34.0&url=https://raw.githubusercontent.com/gamayos/finite-ring-space/main/lean/web/FrcCore.lean`
(`make_core_web.py` regenerates it). The ledgers cite core declarations by full name
(`\lean{FRC.Shell.Frame.half_period}`); the rendered modules are under `docs/lean/core/`.

## Read it, run it

**In the browser, no install** — the Lean community's web editor, on its "Stable Release" project (the
toolchain pinned here), with the module as one self-contained file (`web/<module>.lean`, generated by
`make_web.py`). Click inside a proof for the goal state; edit and re-check.

- Algebra: `https://live.lean-lang.org/#project=mathlib-stable&url=https://raw.githubusercontent.com/gamayos/finite-ring-space/main/lean/web/Algebra.lean`
- Fourier: `https://live.lean-lang.org/#project=mathlib-stable&url=https://raw.githubusercontent.com/gamayos/finite-ring-space/main/lean/web/Fourier.lean`
- Geometry: `https://live.lean-lang.org/#project=mathlib-stable&url=https://raw.githubusercontent.com/gamayos/finite-ring-space/main/lean/web/Geometry.lean`
- Causality: `https://live.lean-lang.org/#project=mathlib-stable&url=https://raw.githubusercontent.com/gamayos/finite-ring-space/main/lean/web/Causality.lean`

**In VS Code, in the browser** — "Code ▸ Codespaces ▸ Create codespace" on the repository, or open the
`.devcontainer` in any devcontainer host: the setup script installs the toolchain and Mathlib's cache (minutes),
after which the infoview follows the cursor.

**In Colab** — the badge above: shell cells install `elan`, fetch the cache (≈7 GB unpacked; the slow step),
re-check every module and print the axioms. 10–15 minutes on a fresh runtime.

**Locally** — with [elan](https://github.com/leanprover/elan) installed:

```
cd lean
lake exe cache get        # Mathlib's compiled oleans, once
lake build                # the modules
lake env lean FrcLedger/Algebra.lean
python3 check_axioms.py   # regenerates axioms.log and applies the gate
```

## What the CI decides on every push (`.github/workflows/lean.yml`)

`lake build` against the pinned Mathlib; the compiled environment replayed through the kernel (`leanchecker`);
the axiom audit under the allowlist above (`axiom-audit`, root namespace `FRC`); `axioms.log` current;
`web/*.lean` current and compiling as single files. A weekly job builds the same modules against Mathlib
master, informationally, so a breaking change upstream is seen before the pin is next moved.

## Layout

```
lean-toolchain, lakefile.toml, lake-manifest.json   the pins (Lean v4.34.0; Mathlib by commit)
FrcLedger.lean, FrcLedger/<Module>.lean            the modules, one per paper
web/<Module>.lean                                   generated single-file copies for the web editor
axioms.log                                          generated, committed: one line per declaration
check_axioms.py, make_web.py, make_notebook.py      the generators and the gate
frc-lean-main.ipynb, .devcontainer/                 the Colab and Codespaces doors
```
