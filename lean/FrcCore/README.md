# FrcCore — the FRC substrate from first principles, with no axioms

A Lean 4 library on the kernel alone: no Mathlib, no `Classical.choice`, no `propext`, no `Quot.sound`.
Every declaration passes `#print axioms` with "does not depend on any axioms" (`python3 check_axioms.py`,
log in `axioms.log`). The residues of a shell are `Shell p` (`val < p`), a structure, not a quotient;
the frame `(τ; 0, 1, g)` is `Frame p κ g` (`p = 4κ + 1`, `g` primitive and generating — both decidable,
certified by `decide` on concrete shells); sums are structural recursions; matrix identities are stated
entrywise. Lean's own `Nat` lemmas that carry `propext` are re-derived by induction in `FrcCore/Nat.lean`,
including the division algorithm from the definition of `Nat.mod`.

Modules (in dependency order): `Nat` (arithmetic, the division algorithm), `Pigeonhole` (lists without
repetition), `Shell` (the ring), `Frame` (the datum: generation by the pigeonhole, half-period, quarter-turn,
orientation classes, Euler identity), `Orbit` (the generator orbit, Fermat), `Sum` (finite sums, the principal
root, the Fourier inversion, the polynomial reading and covariance, the four-cycle, `V = V⁺ ⊕ V⁻`), `Meridian`
(6-fourier: the meridian ladder as lists, the scale-shift as re-indexing and its effective step, the zoom ladder of `𝔽₁₃` by `decide`), `Fourier`
(the 6-fourier predicates named by key, conjunctions of the theorems of `Frame`, `Sum` and `Meridian` that prove them), `Algebra`
(1-algebra rows: the Klein orbits and their count, the frame group, the window and its read-backs), `Epi`
(13-epi: the derangement numbers by recurrence, antiperiodicity and the tower of `e` on every shell, orientation transport, the
wrap-free window, the residue lines and the wall products on `𝔽₁₃` and the wall shells by `decide`), `Dimensions`
(10-dimensions: the domain lattice as pairs of residues with its group law and powers, the unit flag of order four and the meridian
transport on every capacity, the crossed duality, the flagged readings, the linear pin, the root pairs and the linkage on every framed
Carrier; the order-four census of `D_13`, the two Carriers, the `(13, 233)` minimality scan and the realized domains by `decide +kernel`),
`Poly` (polynomials as coefficient sequences: evaluation, synthetic division, the root bound, the root
criterion of 1:G1), `Quaternion` (the signed window and the framed quaternions of 1:G5), `Causality` (the square classes, the
anisotropic and hyperbolic planes of the Lorentzian form, the norm-one boosts and the velocity law of 3-causality), `Representation`
(4-rep: adequacy, the transition and the lifts pointwise with bijections as data, the two-prime Gödel code, the character chart's constant norm), `Reductio`
(5-red: a Δ₀ language with its standard and frame evaluators and the bounded-stability schema with computed bound, the migration counts, iteration on a finite state space — repetition, eventual periodicity, the horizon separation — the least-element choice and its periodicity), `Geometry`
(2-geometry rows: the counts, the fixed-shell bound, adjacency and label covariance), `Complex` (the orbital
shell coded as a cell complex, closedness and the automorphism census decided by the kernel), `Instances`
(𝔽₁₃, 𝔽₁₇, 𝔽₂₉ by `decide`), `Rh` (20-rh: the zero-slot and slot complementarity on every shell, the half-turn arithmetic and the
Subject constants, the scale-shift's fixed-point count, the Ramanujan sum, the quadratic extension as pairs with the Klein four-group,
the critical line with the spectral readout and the norm-one circle, frame coincidence below the horizon; `𝔽₁₃(√2)`, `𝔽₅₃` and the pair `(13, 233)` by `decide`), `Entropy` (14-entropy: the quarter identity and the triality centre, the octant sector `8 ∣ 4S ⟺ 2 ∣ S` and the closure budget, the octant character `ζ = g^m` with `ζ⁴ = −1` and the Tsirelson square `(2(ζ + ζ⁻¹))² = 8` on every frame of even capacity, and the converse — a square root of `2` yields an element of order eight, so `2` is a square exactly on the frames of even capacity —, the nesting bound and trial division to the square root; the laboratory Carrier `2 408 561` prime with `S` even and `≡ 1 (mod 3)`, the octant on `𝔽₁₇` and its absence on `𝔽₁₃`, `𝔽₂₉`, the capacity axis and the nesting `37 → 1373 → 2 408 561` by `decide`), `Gravity` (21-gravity: the calibration congruence `4κ = −1`, `(4κ)² = 1`, the Newton residue `G = 2κ` with `2G = −1`, `(−2)G = 1`, the Gauss count and `G = −c²`, the action quantum `ħ = g^κ` with `ħ² = −1` and its root `r = ħc²`, `r² = κ`, on every frame; the count face `4S + 1 = p²`, `Sp = κA`; the registers of `𝔽₁₃`, `𝔽₁₇`, the merger instance and the laboratory Carrier `2 408 561` by `decide`), `Dirac` (8-dirac: the coefficient field `K = 𝔽_p[w]/(w² − ν)` on components with its conjugation and norm; chronon parity `g^m` a square ⟺ `m` even on every frame, the drive and its inverse nonsquares, the quarter-turn and `2`, `2⁻¹`, `−2` squares exactly on the frames of even capacity, the cofactor `2g` a square exactly on the odd ones; the latitude identities `4κ = −1`, `κ = −4⁻¹`, `2κ = −2⁻¹`; the drive's eigenvalues on the characters, the isotropy sum and the sector separation; by `decide +kernel` the zero counts of the two quadratic forms on `𝔽₅`, `𝔽₁₃`, the torus counts `14`, `18`, the Clifford relations, spin conjugation and the spinor twist on `𝔽₅`, `𝔽₁₃`, `𝔽₁₇`, the circulant Cayley step of `−Δ` on `𝔽₁₃` of order `13`, the potential periods `14`, `18`, the power-map counts, the minimal admissible shell `𝔽₁₇` and the laboratory Carrier's `c = 171 106`). `../web/FrcCore.lean` is the same library in one file for live.lean-lang.org — it needs no
Mathlib and compiles in two seconds under any Lean 4.34 project.

Build: `lake build` (toolchain `leanprover/lean4:v4.34.0`, no dependencies). Gate (from `lean/`): `python3 check_core_axioms.py`.
