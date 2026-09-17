# FrcCore — the FRC substrate from first principles, with no axioms

A Lean 4 library on the kernel alone: no Mathlib, no `Classical.choice`, no `propext`, no `Quot.sound`.
Every declaration passes `#print axioms` with "does not depend on any axioms" (`python3 check_axioms.py`,
log in `axioms.log`). The residues of a shell are `Shell p` (`val < p`), a structure, not a quotient;
the frame `(τ; 0, 1, g)` is `Frame p κ g` (`p = 4κ + 1`, `g` primitive and generating — both decidable,
certified by `decide` on concrete shells); sums are structural recursions; matrix identities are stated
entrywise. Lean's own `Nat` lemmas that carry `propext` are re-derived by induction in `FrcCore/Nat.lean`,
including the division algorithm from the definition of `Nat.mod`.

Modules (in dependency order): `Nat` (arithmetic), `Shell` (the ring), `Frame` (the datum: half-period,
quarter-turn, orientation classes, Euler identity), `Sum` (geometric sums, principal root, the Fourier
inversion), `Algebra` (1-algebra rows), `Geometry` (2-geometry rows), `Instances` (𝔽₁₃, 𝔽₁₇, 𝔽₂₉ by
`decide`). `../web/FrcCore.lean` is the same library in one file for live.lean-lang.org — it needs no
Mathlib and compiles in two seconds under any Lean 4.34 project.

Build: `lake build` (toolchain `leanprover/lean4:v4.34.0`, no dependencies). Gate (from `lean/`): `python3 check_core_axioms.py`.
