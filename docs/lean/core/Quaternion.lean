import FrcCore.Algebra
import FrcCore.Theme.Quaternion

/-!
# FrcCore.Quaternion — the framed quaternions of 1-algebra (a module kept for its name)

The framed quaternions, the window and the rotation layer moved to the algebra theme's `Theme/Quaternion.lean` on
6 November 2026 (the signed window integers to `Theme/Framed.lean`), every name unchanged. The predicates of 1:E5–E7
moved with the conversion of the paper to its module `Algebra.lean`, which imports the algebra theme's key file. This
module declares nothing; it imports both, so an import of `FrcCore.Quaternion` keeps resolving. No axioms.
-/
