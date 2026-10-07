import FrcCore.Keys.Logic

/-!
# FrcBridge.Logic — the bridge of the master's row Z1 (ledger migration, task LM34, landed with LM26)

A bridge states the clause two rows share and derives it from each row's core declaration. One namespace per pair,
`FRC.Bridge.<master>_<paper>`: `Clause` the shared clause, `from_master` and `from_paper` its two derivations. No axioms
(`check_core_axioms.py`).

* **00:Z1 and 25:C1 (master implies paper).** No finite structure interprets `Q`: on `n` elements an injective
  successor misses no element.

Z1's other counterparts have no core proof on the paper's side (25:C2, 5:B3 and 5:B5 are proved on Mathlib; 25:C3 has
no Lean), and 00:Z10 carries 20:E12's key p20043 itself.
-/

namespace FRC.Bridge

namespace Z1_25C1

/-- The clause 00:Z1 and 25:C1 share: on `n` elements an injective successor misses no element, so no finite structure
carries `Q`'s successor. -/
def Clause : Prop :=
  ∀ (n : Nat) (S : Nat → Nat), (∀ x, x < n → S x < n) → (∀ x y, x < n → y < n → S x = S y → x = y) →
    ∀ z, z < n → ¬ ∀ x, x < n → S x ≠ z

/-- From the master's key `FRC.Ledger.p00186` (00:Z1). -/
theorem from_master : Clause := FRC.Ledger.p00186.1

/-- From the paper's key `FRC.Ledger.p25010` (25:C1). -/
theorem from_paper : Clause := FRC.Ledger.p25010.2

end Z1_25C1

end FRC.Bridge
