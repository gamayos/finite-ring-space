import FrcCore.Algebra
import FrcCore.Theme.Quaternion

/-!
# FrcCore.Quaternion — the framed quaternions of 1-algebra (a module kept for its name)

The framed quaternions, the window and the rotation layer moved to the algebra theme's `Theme/Quaternion.lean` on
6 November 2026 (the signed window integers to `Theme/Framed.lean`), every name unchanged. The rotation layer left 1-algebra's ledger with the revision of the same day (it waits for a paper of its own), and
the paper's predicates live in its module `Algebra.lean`. This module declares nothing; it imports both, so an import
of `FrcCore.Quaternion` keeps resolving. No axioms.
-/
