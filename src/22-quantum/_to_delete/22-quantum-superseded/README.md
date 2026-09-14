# frc-quantum-numerics

Numeric validation suite for **"Quantum Observation over Finite Relational
Substrate"** (Y. Akhtman and E. Voether, June 2026) and the accompanying
technical notes (*Experimental Contact I–V*, *The Ω Ledger*), within the
Finite Ring Cosmology (FRC) programme.

Every machine-checkable claim of the manuscript is verified here by **exact
arithmetic** — modular integers, Gaussian integers, and cyclotomic rings
(integer polynomials reduced mod Φₙ) — with no floating point and no limits
wherever the claim itself is exact. Floating point appears only as the
numeric image of exact quantities (the exhaustive CHSH sweep confirming the
exact Tsirelson optimum, the hardware-emulation compilations, and a few
explicitly labelled numeric illustrations), never as the ground of an
exactness claim. Appendix B of the manuscript maps
every numbered Proposition/Theorem to its checks; the same mapping is
summarised below.

## Requirements

- Python ≥ 3.10
- `numpy`, `sympy` (the only third-party dependencies)

## Running

Each suite is self-contained and independent:

```sh
python3 validate.py      # and likewise for every other suite
```

Run everything:

```sh
for f in validate sorkin dispersion composite synchronisation renou bmv \
         decoherence equivalence granularity stratum gravfraction gleason \
         emulation omega intersubject transport; do
    python3 $f.py || exit 1
done
```

Expected output: one `PASS` line per check (187 in total), informational
`INFO` lines where noted, and a terminal `<suite>: all checks passed` per
suite. Any `FAIL` raises an assertion. Test states are fixed (no RNG); every
run is identical. Total runtime is a few minutes, dominated by
`composite.py` (an exhaustive 80³ CHSH sweep and Z[ζ₈₀] symbolics).

## Suites

| suite | checks | arithmetic | verifies (manuscript reference) |
|---|---|---|---|
| `validate.py` | 19 | F₁₅₇, F₄₂₁, Z[i], Z[ζ₁₂] | the single-system formalism: frame data and cores of both worked carriers, fibre partitions, selection rules over all channel pairs, drive eigenstates for all windings, forced-basis orthogonality/Parseval/Lüders on a fixed state, ledger selection rule, reduction commutation, the two-regime dichotomy (Lemma 3.2; Props. 3.3, 4.2–4.4, 5.2, 5.4; Thm. 5.6) |
| `sorkin.py` | 8 | Z[i], shadows mod 157 | Sorkin nullity I₃ = I₄ = 0 with I₂ ≠ 0 on F₁₅₇ and F₄₂₁; sub-horizon shadow exactness; wrap quantisation in pZ (Cor. 5.3, Rem. 5.10) |
| `dispersion.py` | 9 | F₁₃, F₁₆₉ (K = F_p²) | exact boost transport: Clifford relations, spin conjugation for all 168 boosts, group law, covariance over the full norm-one cycle on F₁₃⁴ spinor fields, Dirac→Klein–Gordon factorisation, full-cycle closure with the finite spinor double cover S^((p+1)/2) = −I (Rem. 3.7) |
| `composite.py` | 18 | F₆₄₁, Z[ζ₈₀], Z[ζ₈] | the composite gate: conserved offset, σₓ doublet readout (16×80 cases), singlet law E(Δ) = cos(πΔ/40), composite reduction, exact no-signalling, exhaustive 80³ CHSH sweep, Tsirelson saturation S = 2(ζ₈+ζ₈⁻¹), S² = 8 (Props. 7.2, 7.4–7.5; Thm. 7.7); and the unequal-cycle gate U1–U6 on F₄₂₁ (C₆₀, C₂₈): recurrence T′ = lcm(n_j/gcd(s_j,n_j)) over all 1680 winding vectors, gcd-offset superselection (sectors = Q₄), 1676/1676 orbit-nontrivial characters cancel against 4 sector labels, carrier-internal reduction, Born window guard (Prop. prop:unequal) |
| `synchronisation.py` | 26 | F₆₄₁, F₁₃, Z[ζ₁₆], Z[ζ₄] | the m-body extension of the conserved offset (composite.py C2) from a pair to an m-cell cluster of identical cells: offset vector conserved on all Nᵐ configs; every orbit length N; #orbits = Nᵐ⁻¹ with the offset vector a bijective orbit label (offset superselection); the synchronised orbit Δ unique with \|·\|² = m² coherent; offset-uniform average \|·\|² = m (rms √m) from exact character orthogonality — the equal-cycle case underwriting the locked cluster, exhaustive for m up to 6 (m-body synchronisation lemma; cf. Props. 7.2, 9.5) |
| `renou.py` | 10 | Q(ζ₈) (exact rationals) | the real-vs-complex network: Bell basis = orbit-sector states, entanglement swapping, full conditional table = complex-quantum table (3×6×4 entries), canonical witness = 6√2 as a ring identity, source independence as three exact statements — factorisation across the source cut (rank-1 / vanishing minors), separate offset conservation, product sector distribution (Prop. 7.10, Thm. 7.11) |
| `bmv.py` | 6 | Q(ζ₈₀) | the gravitational channel: C² = sin²(φ/2) exactly over the full sweep, Horodecki S²max = 4(1+C²) = 4 + |ad−bc|² exactly (> 4 for φ ≠ 0, = 8 at φ = π), drive commutation and no-signalling as exact ring identities, V² + C² = 1 as a ring identity (Prop. 9.1; Rem. 9.2) |
| `decoherence.py` | 7 | Q(ζ₄₀), Z[ζ₇] | forbidden collapse (contrast = 1 exactly at every drive time), dilation dephasing as the characteristic function of the internal winding distribution, Gaussian envelope, exact revival V(n) = 1; and the registered drive-frequency count integral and uniform (P = 1/7) for a distinct-eigenvalue superposition, the snapshot interference dephasing over the recurrence (Props. 9.3–9.4; Lemma 5.8) |
| `equivalence.py` | 5 | exact rational lattice Poisson | the two scaling laws: field linearity and exact m-coefficients (full gas sourcing), η = 0 identically, E\|Σζ^θ\|² = m exactly (character orthogonality) vs m² locked, sampled √m scaling as a numerical illustration (Prop. 9.5) |
| `granularity.py` | 7 | Q(ζ₈) (exact rationals) | the depth ceiling: denominator law 2^⌈k/2⌉ with minimality, tally-norm law 2^k (even) / 2^(k+1) (odd), the exact ceilings k* = max{k : d·W(k) < Ω} (unit core k* = 8 and Bell core d = 8 → k* = 6 in F₆₄₁; 404 and 202 at the corpus windows, by integer comparison), lift-ambiguity onset past k*, wrap discrepancies as multiples of Ω; the conductor-4 splitting law — the Gaussian Hadamard (1±i)/2 unitary and balanced over Q(i), reproducing the denominator and tally-norm laws with no ζ₈ (Prop. granularity) |
| `stratum.py` | 12 | Z[i], Z[ζ₁₂], F₆₄₁ | the two probability strata (Prop. strata): two-way part of the Gaussian ledger = the tally lattice (exhaustive); engineered-core weights as exact Carrier residues on Ω = 641 (r² = 2, W± = 2±r, W₊+W₋ = 4, W₊W₋ = 2); the chart-ring counterexample 1+ζ₁₂ excluded from the tally lattice; the zoom-grid witness r = gⁿ (scale periodicity); the framed readout map R_n by integer square root: the worked Bell-weight instance, grid-bound and nesting at every scale, and the M3 √3 instance; the conjugate-pair trace tally (flip-summed string weights = 2^min·t_m integers, dial-shift conjugation exact in Z[x]/(x⁴⁰+1)) and the dial-ensemble Parseval tally (160/160 by complete character sums) (Rem. rem:strata) |
| `gravfraction.py` | 12 | Z[ζ₁₆] | the coherent-fraction channel law (Prop. fcoh): synchronised branch phase ζ^(m_c a) exact; pairwise m_c1·m_c2 scaling; offset-spread systematic branch phase zero by complete character sums; envelope separation (\|sync\|² = m² vs complete spread = 0); the reduced channel Γ = χ_inc·ζ^(m_c a) assembled exactly, including a nonuniform thermal χ_inc instance; the complete-spread diagonality under the nondegeneracy hypothesis (every cross-branch differential a nontrivial character; F9 assumes, does not derive, the differentials) with an exact PPT instance; the exhaustive 15-partition classification of complete-spread states — NPT exactly at size-3 blocks, min PT eigenvalue exactly (1−√3)/4 (the joint-spread-character counterexample class); and the local-additivity theorem — additive spread phases never produce size-3 blocks and never entangle; the entangling class is non-additive joint geometry |
| `gleason.py` | 9 | Z[i], exhaustive Q₄ | uniqueness of the pair tally (Prop. gleason): nonneg-tally character combinations = the admissible two-way drive-invariant kernels (exhaustive); Fourier inversion exact; negative-coefficient witness; single-channel response iff scaled unit coefficient vector (channel pinning); the fibre-norm counterexample: satisfies (a)–(d) with c = 1/4, fails channel-selectivity (e); the w_r/16 multiplier instance (ray uniqueness only) and the linear-degree exclusion; the in-sector pure-winding pinning F(ψ_k) = d²c_{k mod d}, exhaustive; the spanning/polarization transfer — core DFT invertible (det −16i), equal responses on the admissible class force equal kernels |
| `emulation.py` | 7 | numeric (10⁻¹² vs exact refs) | the hardware compilations: I₃⊗QFT₄† (12-level) and I₂⊗QFT₈† (16-level) unitaries equal the forced bases, selection rules, uniform-outcome law, three-outcome interference law, σₓ doublet law at π/40; gate decomposition H–CS–H–SWAP; emits the two experiment cards (App. C) |
| `omega.py` | 4 | scale arithmetic | the Ω ledger: every floor below the anchor with recorded margins, joint window [8×10⁴⁹, ∞) containing Ω = 10¹²², scale coherence of √Ω and Ω^(1/4), identification of the binding floor; prints the full ledger table (§12) |
| `intersubject.py` | 22 | F₄₂₁, Z[ζₙ] (Φₙ-reduced) | inter-Subject consistency: two Subjects S, S′ reading one Object with equal cores (S₆₁, S₁₃ on O₂₉) and embedded cores (S₂₉, S₁₃ on O₆₁) — order-independent joint refinement to the common core, selection-rule agreement of S and S′ on the quarter-turn datum, realisability iff the channels agree on Q₄, and order-independence on the shared cell; Gaussian-integer superposition input and an incomparable-core (C₁₂, C₈ in C₂₄) refinement control (Prop. 4.6) |
| `transport.py` | 6 | F₁₅₇, F₄₂₁, F₆₄₁ | the quarter-turn transport trichotomy (Lemma lem:transport): winding reduction Π carries the ambient quarter-turn faithfully iff κ ≡ κₙ (mod n), conjugately iff κ ≡ −κₙ (mod n), κ mod 4 the coarsest invariant — faithful (F₁₅₇→C₁₂; F₄₂₁→Q₄), conjugate (F₄₂₁→C₆₀,C₂₈,C₁₂; F₁₅₇→C₅₂), broken (F₆₄₁→C₄₀: Π(i) = 1) |

**Totals: 17 suites, 187 checks, all passing.**

## Worked configurations

| carrier | generator | Subject(s) | Object(s) | core | quotient |
|---|---|---|---|---|---|
| F₁₅₇ | g = 5 | S₅₃ (C₅₂) | O₁₃ (C₁₂) | Q₄ | C₃ |
| F₄₂₁ | g = 2 | S₆₁ (C₆₀) | O₂₉ (C₂₈); O₁₃ (C₁₂) | Q₄; C₁₂ | C₇; C₁ |
| F₆₄₁ | g = 3 | S₄₁×2 (C₄₀) | O₁₇×2 (C₁₆) | C₈ | C₂ |

Orientation is derived, not conventional (pullback covariance and count
positivity): a shell of capacity κ has cardinality 𝗉 = 4κ+1 and oriented
quarter-turn 𝕀 = g^(−κ) = −g^κ; at the chart scale of a carrier Ω = 4S+1 the
quarter-turn is 𝕀 = g^(−S) — imaginary axis up from the unit, drive clockwise.
Registered probabilities are framed rationals (realized tallies over realized
tallies, heights below the window); structural weights live in the two-way
(chronon-parity-even) subring, coinciding with the tallies exactly on the
universal core Q₄ (Prop. strata).

## Reports

The technical notes are included as compiled PDFs; each suite's
results are written up in the corresponding report:

| report | suites covered | content |
|---|---|---|
| `report-exp1-nullity.pdf` | `sorkin`, `dispersion` | *Experimental Contact I* — Sorkin nullity and wrap quantisation; exact boost transport and the finite spinor double cover |
| `report-exp2-composite.pdf` | `composite` | *Experimental Contact II* — the composite gate and exact Tsirelson saturation |
| `report-exp3-network-gravity.pdf` | `renou`, `bmv` | *Experimental Contact III* — the real-vs-complex network game; the gravitational channel and the BMV forward prediction |
| `report-exp4-floor-ep.pdf` | `decoherence`, `equivalence` | *Experimental Contact IV* — forbidden collapse, the dilation floor with exact revival; the two scaling laws and the equivalence-principle null |
| `report-exp5-ceiling-emulation.pdf` | `granularity`, `emulation` | *Experimental Contact V* — the depth ceiling; the hardware compilations and experiment cards |
| `report-omega-ledger.pdf` | `omega` | *The Ω Ledger* — the consolidated falsifiability statement on one carrier scale |

The manuscript itself (`main.pdf` in the parent folder) integrates all of the
above; the reports remain the per-target accounts with their own
bibliographies.

## Design principles

1. **Exact where the claim is exact.** Ring identities are verified as ring
   identities (polynomial equality mod Φₙ, `Fraction` rationals, modular
   integers), never as numerical near-equality.
2. **Exhaustive where the domain is finite.** Selection rules sweep all
   channel pairs; boost identities sweep all group elements; the CHSH sweep
   covers all 80³ admissible setting triples.
3. **Shadows cross-checked.** Wherever the manuscript claims that the
   ledger-to-carrier reduction commutes, both sides are computed
   independently and compared element by element.
4. **Deterministic.** Fixed test states (no RNG); identical output on every run.

## Citation

If you use this suite, cite the manuscript: Y. Akhtman and E. Voether,
*Quantum Observation over Finite Relational Substrate*, 2026, and the FRC
corpus referenced therein. Related suites for other sectors of the programme:
`frc-rh` (Riemann realisation) and `frc-gravity-numerics` (gravitation).
