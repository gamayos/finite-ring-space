# validation/ — machine verification for *Dimensional Analysis over Finite Holographic Substrate*

Two scripts guard the manuscript: an exact-arithmetic suite that verifies every
algebraic claim the paper makes, and a source-gate script that verifies the
manuscript's own text against the register discipline of the corpus. Both are
deterministic — no randomness, no network, no dependencies beyond the Python 3
standard library. A green state means `200/200 exact checks pass` and all
gates `[PASS]` with exit code 0.

## Relation to the paper's claim discipline

Table 2 of the paper tags each headline claim T (theorem), D (definition),
R (realisation), I (import), or Ω-hard. The suite enforces that typing rather
than blurring it: claims tagged T are checked as identities that must hold;
claims tagged D or R are checked *at their algebraic faces* — the suite
verifies what the realisation implies, never that it is forced; the
realisations stand or fall with their stated falsifiers, not with the suite. The residue
layer is stated at pair level (round 05): the defining congruences fix each constant's sign
pair {x, −x} canonically, the linkage {±k_B}{±c} = {±ħ} is derived, and the
suite verifies that the representative convention it computes with is *inert*
— every checked identity is pair-well-defined and holds under all four
admissible sign assignments, on both Carriers. A check that "proved" a
realisation would be a bug.

The suite also verifies sharpness. Wherever the paper states a bound or a
restriction, the suite carries a witness just beyond it: the label (0, π) is
pushforward-invariant yet non-neutral, so the covariance window H < 2κ cannot
be widened; the flagged label (0, 0; 1) moves under ε = −1, so the flag-free
restriction cannot be dropped; the would-be temporal character fails
composition outright (5² ≡ 1 in Z₁₂^× while s ↦ 25s on Z), so its absence is a
theorem, not an omission.

## `verify_domains.py` — 200 exact checks in eight layers

All identity checks are integer or exact-rational (`fractions.Fraction`)
arithmetic; the window-ladder orderings are compared by integer squares, so the
suite is float-free. Structures exercised: the toy shell F₁₃ (κ = 3), the
shells p = 29 (κ = 7) and p = 229 (κ = 57), and both instantiated Carriers —
Ω = 233 (S = 58) and the lab Carrier Ω = 2,408,561 (S = 602,140).

- **A. Shell datum and domain algebra on F₁₃** (32 checks): frame datum
  (g = 2 primitive, i = −g^κ, π = 2κ, capacity budget 4κ = p−1); the domain
  group D_p = Z_p × Z_{p−1} with group law, inverses, and grading; the internal
  flag I_q = [T]^κ — unique order-four subgroup, both generators at r = 0 (no
  flag of space), horizon-inaccessibility on the bounded window, covariance of
  the generator pair under every admissible ε; realization as a homomorphism;
  derived domains ([m], [F], [S], [G], Compton, Planck-area, Schwarzschild,
  orbital-frequency closures); fibrewise addition and local recovery at H = 5.

- **B. The quartet at the unit face** (30 checks): exponent-vector verification
  of the relation lattice over the primitive triple {ℓ_P, t_P, ħ} — both faces
  of c and ħ differ by the single relation ℓp = tE; pairing rank two; k_B and
  ℓE add nothing (rank stays 3); numeric instantiation with exact rationals
  confirming every stated equality (cancellation |k_B|c = ħ, m_P, G, Θ_P, the
  bijection {c, ħ, G} ↔ quartet); the degrees-of-freedom count 4 − 1 = 3; and
  the flag positions (0,0,1,1) with closure of every quartet relation on the
  flag component.

- **C. The defining congruences on the lab Carrier** (13 checks): admissibility of
  S = 602,140; existence and uniqueness of the linear congruence 2G ≡ −1; the
  quadratic defining congruences ħ² ≡ −1, k_B² ≡ −2, 2c² ≡ 1 with their exact root pairs;
  the register identities G ≡ −c², G² ≡ 4⁻¹ and the h-form h = 2πħ ≡ −ħ; and
  the scale-face statement m_P² ≐ Ω ≡ 0.

- **D. Both Carriers, faces, minimality, temperature** (50 checks): the full
  congruence-and-closure system replayed on Ω = 233 and the lab Carrier, including the
  m_P² monomial face landing on the k_B residue (ħcG⁻¹ ≡ k_B) and its
  non-vanishing; the representative-convention annex (the √S-branch representatives sit in
  opposite halves on the two Carriers; the c halves differ — half-plane
  membership is chart data, carrying no invariant content); the admissibility
  minimality scan certifying (13, 233) with the
  counterfactuals (dropping the mod-3 clause admits (13, 193); dropping κ > 1
  admits (5, 41); κ = 2 gives composite 9); the temperature and Unruh domain
  closures [Θ] = [L][T]⁻²; and injectivity plus windowed faithfulness of the
  crossing-degree embedding M^u L^a T^b ↦ (a−2u, b+u; u).

- **E. Covariance: characters, pushforward, orientation, lattice index**
  (18 checks): the boundary witnesses that fix the covariance doctrine — the
  naive character is ill-defined on the modular projection, the label (p−1, 0) has
  trivial character yet is non-neutral, the ε-composition failure — together
  with window covariance below the bound, the pushforward-invariant labels
  {0, π}, the quarter-turn fix/swap criterion ε ≡ ±1 (mod 4), the
  representative-convention data on both Carriers, and the index-two sublattice ⟨c, ħ, G⟩
  (det = −2) with positive-root recovery of the scale.

- **F. Window bound, twisted action, dualities** (15 checks): the (0, π)
  witness forcing H < 2κ and window invariants = {0} below it; the σ-twisted
  action verified equivariant by full sweep on p = 13 and p = 229, with the
  plain-lift failure retained as its boundary witness; σ multiplicative mod 4;
  and δ_S, δ_C both involutions, δ_C carrying [L] ↦ [p], [T] ↦ [E], δ_S
  flag-free.

- **G. Realized action, window ladder, meridian transport, pair canonicity**
  (15 checks): realized-action composition against the Z³-representative failure;
  the flagged label (0, 0; 1) moving under ε = −1; the window ladder
  2√κ < κ/2 < κ < 2κ nested for every κ ≥ 17 and failing for the toy κ = 3
  (all orderings by integer squares), with the exact coherence identity
  (2√κ)² = p−1 and the exact totality closure (2√S)² = Ω−1; the flagged ratio
  F/a (equal-crossing-degree scope); meridian transport (L T^κ)^p = I_q on
  three shells; and the both-roots check on both Carriers — the pair, not a
  root, is the canonical object of the congruence system.

- **H. Pair layer** (27 checks): pair multiplication well defined
  ({±a}{±b} = {±ab}); the linkage derived at pair level ((k_Bc)² ≡ −1, so
  {±k_B}{±c} is the root pair of −1, which is {±ħ}); the monomial ħcG⁻¹
  landing in the k_B pair via (ħcG⁻¹)² ≡ −2; the representative-inertness
  sweep — of the eight sign assignments exactly the four with σ_ħ = σ_cσ_k are
  admissible, a (Z/2)² group, and the h-form and monomial landing hold on each;
  and the ħ-flip relabelling within the {ħ, h} pair.

## `check_gates.py` — 105 source gates

The gates read `sections/*.tex` and `mdpi.tex` and enforce the manuscript's
text discipline. The doctrine is symmetrical: every settled formulation
deposits a **required token** (the exact phrase must be present), and every
superseded formulation deposits a **verbatim ban** (it must never reappear) —
so no edit can silently drift the text away from its settled state.

The families: markup residue (no diff-build macros survive); the κ/τ/t role
gates (κ is a capacity, never a duration; τ is the Subject's now, never a
"temporal frame label"; no packet-tick temporalisation); the corpus blacklist
(phase carrier, carrier-internal, total entropy, …); the constructive register
(no referee-facing prose in the manuscript); the required forms (the frame
written (τ; 0, 1, g), the Object frame (t; q, k, v), the capacity-first
phase-cycle order 4κ = 2π = p−1, "symmetry-complete" invoked exactly once);
and the doctrine gates — presence of the internal-flag theorem, crossing
degree, the pair form of the defining congruences with the linkage derived rather than
declared, representative inertness, reframing action and window covariance,
the count-valued comparison doctrine, the window ladder and coherence window,
the atomic chronon, the equal-crossing-degree scope, meridian transport, the
realisation content, the Ω-hard thesis sentence of the instantiation subsection,
and the I = import key of Table 2 — with the corresponding superseded
phrasings (orientation imports, the residue reading, the residue-band
question, root-selection language) banned verbatim. The round-06 family
guards the holographic doctrine: the title *Dimensional Analysis over Finite
Holographic Substrate*, the holographic-substrate remark, the encoding
condition, the realisation legend, the h-form pair, the s13 citation, at
least three stated falsifiers, and "Finite Ring Cosmology" expanded exactly
once (in the primer) — with "bridge" as a doctrinal term, "bridge-class",
"interpretive content", and the old title banned verbatim.

## Usage

Run from the paper root (the directory containing `mdpi.tex`):

    python3 validation/verify_domains.py   # expects: 200/200 exact checks pass
    python3 validation/check_gates.py      # expects: all [PASS], exit 0

Both scripts exit nonzero on any failure. The public mirror of this suite
lives at
<https://github.com/gamayos/frc-numerics/tree/main/10-dimensions>.
