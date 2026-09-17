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
root, the Fourier inversion, the polynomial reading and covariance, the four-cycle, `V = V⁺ ⊕ V⁻`), `Algebra`
(1-algebra rows: the Klein orbits and their count, the frame group, the window and its read-backs),
`Poly` (polynomials as coefficient sequences: evaluation, synthetic division, the root bound, the root
criterion of 1:G1), `Quaternion` (the signed window and the framed quaternions of 1:G5), `Causality` (the square classes, the
anisotropic and hyperbolic planes of the Lorentzian form, the norm-one boosts and the velocity law of 3-causality), `Geometry`
(2-geometry rows: the counts, the fixed-shell bound, adjacency and label covariance), `Complex` (the orbital
shell coded as a cell complex, closedness and the automorphism census decided by the kernel), `Instances`
(𝔽₁₃, 𝔽₁₇, 𝔽₂₉ by `decide`). `../web/FrcCore.lean` is the same library in one file for live.lean-lang.org — it needs no
Mathlib and compiles in two seconds under any Lean 4.34 project.

Build: `lake build` (toolchain `leanprover/lean4:v4.34.0`, no dependencies). Gate (from `lean/`): `python3 check_core_axioms.py`.
