import FrcCore.Keys.Foundation
import FrcCore.Keys.Logic
import FrcBridge.Carrier

/-!
# FrcBridge.Foundation — the bridges of the foundation's counterpart pairs (ledger migration, task LM34, landed with LM23)

A bridge states the clause two rows share and derives it from each row's core key, so the two keys are seen to agree on
it (`FrcBridge/Carrier.lean` sets the form). One namespace per pair, `FRC.Bridge.<master>_<paper>`: `Clause` the shared
clause, `from_master` and `from_paper` its two derivations. No axioms (`check_core_axioms.py`).

* **00:A5 and 5:C2 (overlap, LM10).** A part with fewer states than the whole holds no injective representation of
  it. The master's key reads the Carrier's points and finds two of them identified; the paper's states the pigeonhole
  on `[0, N)` beside its record bound.
* **00:A5 and 25:D1 (overlap, LM10).** The same clause against 25:D1's storage bound.

And the frame (00:A14 against the frame theme): every prime `p = 4κ + 1` carries a frame `(τ; 0, 1, g)` (`frame_exists`),
and with `frame_isPrime` (Lehmer, `FrcBridge/Carrier.lean`) the classical equivalence that `Frame.lean` left for
later: on `p = 4κ + 1`, a frame exists iff `p` is prime (`frame_iff_isPrime`).
-/

namespace FRC.Bridge

open FRC.Shell

/-- Every prime `p = 4κ + 1`, `κ > 0`, carries a frame: 00:A14's drive is primitive of order `p − 1`. -/
theorem frame_exists {p κ : Nat} [Pos p] (hp : FRC.Nat.isPrime p) (hcap : p = 4 * κ + 1) (hκ : 0 < κ) :
    ∃ g : Shell p, Frame p κ g :=
  match FRC.Ledger.p00164 hp with
  | ⟨g, hg, _⟩ => ⟨g, ⟨hcap, hκ, hg⟩⟩

/-- On `p = 4κ + 1`, `κ > 0`: a frame `(τ; 0, 1, g)` exists iff `p` is prime. -/
theorem frame_iff_isPrime {p κ : Nat} [Pos p] (hcap : p = 4 * κ + 1) (hκ : 0 < κ) :
    (∃ g : Shell p, Frame p κ g) ↔ FRC.Nat.isPrime p :=
  ⟨fun ⟨_, F⟩ => frame_isPrime F, fun hp => frame_exists hp hcap hκ⟩

/-- A part with fewer states than the whole holds no injective representation of it: no `f : [0, N) → [0, R)` with
`R < N` is injective on `[0, N)`. -/
def PartClause : Prop :=
  ∀ {N R : Nat}, R < N → ∀ f : Nat → Nat, (∀ i, i < N → f i < R) → ¬ ∀ i j, i < N → j < N → f i = f j → i = j

/-- The clause from the master's key `FRC.Ledger.p00159` (00:A5): read `f` on the `N` points of the shell `𝔽_N`; the
two points the key finds are distinct and identified. -/
theorem part_of_master : PartClause := fun {N R} hR f hf hinj =>
  match @FRC.Ledger.p00159 N R ⟨Nat.lt_of_le_of_lt (Nat.zero_le R) hR⟩ hR (fun x => f x.val) (fun x => hf x.val x.lt) with
  | ⟨x, y, hxy, e⟩ => hxy (ext (hinj x.val y.val x.lt y.lt e))

namespace A5_5C2

/-- The clause 00:A5 and 5:C2 share: a bounded part cannot mirror the whole. -/
def Clause : Prop := PartClause

/-- From the master's key `FRC.Ledger.p00159` (00:A5). -/
theorem from_master : Clause := part_of_master

/-- From the paper's key `FRC.Ledger.p05013` (5:C2, alias `FRC.Reductio.p05013`): its second clause. -/
theorem from_paper : Clause := fun hR f hf hinj => FRC.Ledger.p05013.2 hR f hf hinj

end A5_5C2

namespace A5_25D1

/-- The clause 00:A5 and 25:D1 share: a bounded agent has no faithful (injective) internal representation of the
domain. -/
def Clause : Prop := PartClause

/-- From the master's key `FRC.Ledger.p00159` (00:A5). -/
theorem from_master : Clause := part_of_master

/-- From the paper's key `FRC.Ledger.p25015` (25:D1, alias `FRC.Godel.p25015`). -/
theorem from_paper : Clause := fun hR f hf hinj => FRC.Ledger.p25015 hR f hf hinj

end A5_25D1

end FRC.Bridge
