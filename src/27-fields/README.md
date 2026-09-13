# Validation suite — *Standard-Model Interactions over Finite Substrate*

**Repository:** <https://github.com/gamayos/frc-numerics/tree/main/27-fields>

This folder holds the computational verification for *Standard-Model Interactions over Finite Substrate* (`../main.tex`). The scripts are standalone, deterministic, take no input, and print a human-readable verdict; all exit non-zero on any failed check.

## Framed-rational discipline

Every script carries a one-line `# framed-rational status:` banner at the top, in one of three classes:

- **EXACT** — every asserted check is performed in integer, modular `𝔽_p`, `𝔽_{p²}`, or cyclotomic arithmetic. No floating point enters an asserted claim (a `float()` may appear only to format an exact rational for display). Nothing exceeds the totality `Ω`.
- **MIXED** — an exact framed-rational core, with continuum constructs (`exp`, `log`, trig, `√`, Haar integrals, measured data) confined to clearly-labelled `[approx]` / degenerate-idealisation comparisons (the Tier 2/3/5 correspondence and phenomenology, or comparison to PDG constants). The exact claim never depends on the float part.
- **[APPROX]** — by construction a continuum / degenerate-idealisation comparison (the finite-window correspondence to compact Yang–Mills, or a dimensional-transmutation estimate). These are not exact framed-rational claims; they are the observer-chart reading.

This is the corpus rule: an exact claim lives in finite, finite-field, or cyclotomic arithmetic; the continuum enters only as an explicitly labelled profinite/degenerate-idealisation approximation, and no realized magnitude exceeds `Ω`.

**Status.** All 28 scripts run and pass. The two scripts that carry an *exact* claim establish it directly in framed-rational arithmetic, with the continuum reading held as a labelled `[approx]`:

- `enumerate_maxwell.py` — the Maxwell-uniqueness **dimension** is the exact corank of the integer constraint Gram over `𝔽_p` (Gaussian elimination in a large prime field, balanced lift); the continuum dispersion-symbol reading that classifies the operator as the transverse projector is the labelled `[approx]` part, with its basis count cross-checked against the exact corank.
- `p4.py` — the V−A character cancellation `Σ_τ ζ_N^{2δτ}` is the exact geometric-series value: `N` if `N∣2δ`, else exactly `0`, in integer arithmetic.

`audit_finitism.py` is the standing cross-check that the load-bearing EM / O1 claims rest on integer/cyclotomic arithmetic, with no float or continuum step.

Class counts: **EXACT 15, MIXED 11, [APPROX] 2.**

## Requirements

- Python 3.10+
- `numpy` and `sympy` (only some scripts need them — see the table)
- no other dependencies; no network, no data files

```bash
pip install numpy sympy
```

## Running

```bash
python3 p1.py                                   # one script
for f in *.py; do echo "=== $f ==="; python3 "$f"; done   # whole suite
```

All scripts exit 0 and complete in seconds.

## Script → claim map

"Paper result" refers to the labelled results in `../main.tex`. "Status" is the framed-rational class above.

| script | status | paper result | what it verifies | arithmetic |
|---|---|---|---|---|
| `em1_prototype.py` | MIXED | EM ledger (Table); charge & Coulomb props | finite U(1): gauge-invariant plaquette flux and winding charge (**exact integers**); Coulomb coefficient vs the lattice Green's function and the EM-repels/gravity-attracts sign (`[approx]` continuum reading). The exact integer/cyclotomic form of these claims is in `audit_finitism.py`. | integer + lattice solve | numpy |
| `enumerate_maxwell.py` | MIXED | O1 uniqueness theorem | the admissible adjacency-local gauge+hypercubic quadratic space is **dim 2** (exact `𝔽_p` corank of the constraint Gram); the continuum symbol splits it into one Maxwell transverse-projector operator + one irrelevant `O(k⁴)` artifact (`[approx]` dispersion reading) | exact `𝔽_p` rank (+`[approx]` symbol) | numpy, sympy |
| `correspondence.py` | [APPROX] | Thm 4.x finite-window correspondence | the finite→compact correspondence (Thm `thm:corr`): abelian inclusion (A, exact), `q=3` `2T⊂SU(2)` embedding (B, exact), gauge invariance (D, exact), low-curvature Yang–Mills (C), window residue (E), area law (F), character lift (G), finite quadrature (H) — the C/E/F/G/H blocks are the continuum-comparison layer | exact (A,B,D) + continuum-comparison | numpy |
| `o2_numbers.py` | MIXED | bare-coupling prop | the EM coupling as phase-channel capacity: the `α_bare = 1/4π` bookkeeping (the `4π` a labelled continuum-comparison constant) and the `10³⁶` EM/gravity hierarchy as a reading of `Ω` | rational + continuum-comparison | — |
| `ew1.py` | EXACT | electroweak-breaking thm; ρ=1; Weinberg angle | drive/torus misalignment over `𝔽₁₃`: massless photon (drive-fixed Cartan), gapped `W±`, custodial `ρ=1`, `sin²θ_W = Tr(T₃²)/Tr(Q²) = 3/8` | exact (`𝔽₁₃`, rationals) | sympy |
| `weak_spectrum.py` | EXACT | propagating mass step (Prop 6.6) — D5a | the propagating `W,Z` spectrum as the Hessian of `S_ρ` at the broken vacuum: photon = exact kernel, `ρ=1` as `det≡0`, `M_W²/M_Z²=cos²θ_W=5/8` | exact (`ℚ`, `𝔽₁₃`, `𝔽₅`) | sympy |
| `weak_current.py` | MIXED | chiral V−A current & 4-fermion amplitude (Prop 6.2) — D5b | left coupling `N=q+1`, right `=Σ_τ ζ_N^{2δτ}=0` by orthogonality (exact, roots of unity); chiral projector `P_L=½(1−γ₅)`; the `G_F=1/(√2 v²)` comparison to the measured value is the `[approx]` part | exact cyclotomic + `[approx]` data | sympy |
| `v_scale.py` | [APPROX] | electroweak scale `M_EW` (Thm 5.6) — D5c | dimensional-transmutation estimate `M_EW ~ m_P·exp(−4π²) ≈ 87 GeV` (gauge-boson scale; vev `v=246.2 GeV` up to couplings); the exact coefficient is the **Ω-hard** cross-scale β-function | float (dimensional estimate) | — |
| `qcd.py` | MIXED | colour SU(3) & confinement props | QCD-2: `SU(3,𝔽_q)` Hermitian three-form, `|SU(3,2)|=216`, `Z₃` triality (**exact `𝔽₄`**); QCD-1: the strong-coupling string tension via Bessel/Boltzmann (`[approx]` compact-group reading) | exact (`𝔽₄`) + `[approx]` | numpy |
| `string_tension.py` | MIXED | confinement area law (Prop `prop:corrarea`) | the single-plaquette coefficient `c₁` as the **exact** finite-group character sum (`c₁^{SU(3)}=β/18+β²/216+…`); `σ=−ln c₁` is the `[approx]` continuum string-tension reading | exact char sum + `[approx]` log | numpy |
| `generation.py` | EXACT | the generation theorem | one generation as the spinor `16 = 1⊕5̄⊕10` of the rank-5 frame: traceless hypercharges, electric charges, `ΣY = ΣY³ = 0` anomaly cancellation | exact rationals | — |
| `koide.py` | MIXED | Koide relation (`prop:koide`) | `Q=⅓+⅔ρ²` and `ρ²=½` (the self-dual `2⁻¹`) exact over `𝔽_p`, `p≡5 (mod 12)`; the measured-mass `Q=0.66666` comparison is the isolated `[approx]` block | exact `𝔽_p`/`𝔽_{p²}` + `[approx]` data | — |
| `strongcp.py` | EXACT | strong-CP `θ̄=0` (`prop:strongcp`) | Hermitian quark mass matrices over `𝔽_{p²}/𝔽_p` have `det ∈ 𝔽_p` (so `arg det M_q=0`), while non-commuting up/down keep CKM free; `p≡5 (mod 12)` | exact `𝔽_{p²}` determinants | — |
| `p1.py` | MIXED | running prop | `sin²θ_W=3/8` at `α₁=α₂` (exact rational at the meeting); the one-loop RG run to `M_Z` and `M_X` is the `[approx]` continuum running | exact rational + `[approx]` RG | — |
| `p2.py` | MIXED | bare-coupling prop | the order-one coefficient is exactly 1 (channel unity, charge = action = phase quantum); the `4π` in `1/4π` is a labelled continuum-comparison constant | rational + continuum-comparison | — |
| `p3.py` | EXACT | weak-connection prop | the cell-local `SU(2,𝔽₃)` connection: Wilson action gauge-invariant by plaquette-trace conjugation, exhaustive over the group; doublet covariant | exact (`𝔽₉`) | — |
| `p4.py` | EXACT | parity-violation prop | maximal V−A: the drive-aligned branch sums to `N`, the Frobenius branch to `0` exactly (geometric-series character sum, integer-decidable) | exact (integer character sums) | — |
| `p5.py` | EXACT | gluon-connection prop | the cell-local `SU(3,𝔽₄)` gluon connection: exact Wilson gauge invariance, self-coupling `U₁U₂U₁⁻¹U₂⁻¹≠I`, masslessness | exact (`𝔽₄` integers) | numpy |
| `p6.py` | MIXED | asymptotic-freedom prop | `b₀=11−⅔n_f>0` (exact rational); `Λ_QCD = M_P exp(−2π/b₀α_s)` and `(m_p/M_P)²=exp(−88)` are the `[approx]` dimensional-transmutation reading | exact rational + `[approx]` | — |
| `p7.py` | MIXED | mass prop | the Yukawa mechanism and the seesaw/`b–τ`/FN structure; the spectrum itself is the **Ω-hard** flavour residual, shown via an `[approx]` winding demo | mechanism + `[approx]` | — |
| `p8.py` | EXACT | unification prop | the rank-5 frame and the `SU(5)/SO(10)` representation arithmetic (integer counting) | integer | — |
| `p8b.py` | EXACT | unification prop (X,Y) | `dim SU(5) − dim(SM) = 24 − 12 = 12 =` the `3×2` off-block (colour–isospin reframings); `16` irreducible under `SO(10)` | integer | — |
| `p9.py` | EXACT | Galois-conjugate prop | generations as Galois conjugates: orbit size = extension degree for `q = 2,3,5` | integer | — |
| `p9b.py` | EXACT | three-generations prop | the closed role ladder's `1+3` split: counting = bosonic carrier, three generative roles = three generations; the mass ordering | integer | — |
| `p10.py` | EXACT | chirality-selection prop | the orientation-flip `𝕚 ↦ −𝕚` invariance: absolute handedness is a relabelling with no frame-independent meaning | exact (integer) | — |
| `p11.py` | EXACT | substrate-residue prop | `Ω ≡ 5 (mod 12)` as the CRT conjunction of `4∣Ω−1` and `3∣Ω+1`, Dirichlet density `1/4` | exact | sympy |
| `missing_rank.py` | EXACT | colour-rank prop | the rank-tower `U(1),SU(2),SU(3)` forcing and the `PSU(3,5)` kinematics on the smallest admissible shell, by exact count | exact (integer) | — |
| `audit_finitism.py` | EXACT | §Finitism | establishes the load-bearing EM/O1 claims with no random sampling, no FFT, no float, no transcendentals: gauge identity exhaustive, rank = 2, Wilson action cyclotomic, Green's function `= 257/7680` on the `L=4` `ℤ[i]` torus | exact (`ℤ, 𝔽_p, ℚ(ζ_M), ℤ[i]`) | numpy, sympy |

## Representative expected output

- `enumerate_maxwell.py` → `dim(T&L&C&G) = 2`, exact `𝔽_p` corank; one relevant Maxwell operator (projector match `~2×10⁻⁷`) + one irrelevant `O(k⁴)` artifact.
- `ew1.py` → `sin²θ_W = 3/8`, `ρ = 1` exactly.
- `weak_current.py` → left `= N=q+1`, right `= 0` exactly (`q=3,5,7,13`); `G_F` comparison `[approx]`.
- `koide.py` → 5/5 framed-rational `𝔽_p` checks; measured `Q=0.66666` tagged `[approx]`.
- `strongcp.py` → 20/20: Hermitian `det ∈ 𝔽_p` (`θ̄=0`), `[M_u,M_d]≠0` (CKM free).
- `p4.py` → left `= N`, right `= 0` (exactly).
- `audit_finitism.py` → action `= 1 − √2/2 = 1 − (ζ₈+ζ₈⁻¹)/2`, a cyclotomic number, not a float.

## Conventions and notes

- **Exact where exact.** Claims the paper marks exact are computed in integer, `𝔽_p`, `𝔽_{p²}`, or cyclotomic arithmetic and verified exhaustively over a basis or group, never by sampling. `audit_finitism.py` cross-checks that no exact claim depends on a float or continuum step.
- **Continuum readings are labelled.** Coulomb `1/4πr`, the `4π`/`2π` geometric constants, the RG running, the dimensional-transmutation scales, the compact-group string tension, and comparisons to PDG constants are degenerate-idealisation `[approx]` readings (the finite-window correspondence and phenomenology), reported as such; the cross-scale running and the absolute scales are **Ω-hard**.
- **Nothing exceeds Ω.** No realized magnitude exceeds the totality; super-`Ω` quantities, where they appear in the argument, are formal (controlled) counts, not computed values.
- **Determinism.** No script's asserted result depends on randomness; results are reproducible bit-for-bit.
- **Orientation.** The convention `𝕀 = g^{−π/2}` is used throughout (see `p10.py`); do not flip it.
