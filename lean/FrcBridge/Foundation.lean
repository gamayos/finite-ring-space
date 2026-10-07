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

* **14:C6 ⇒ 00:B14 (paper ⇒ master; the audit's M4, 7 October 2026).** B14 is 14:C6's first clause on the Carrier's
  chart: with 00:A14's frame on every prime `Ω = 4S + 1`, 14:C6's key gives B14's key (`b14_of_14C6`). 14:C6 adds two
  clauses (the Tsirelson square and the laboratory instance), so the converse does not hold.

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

/-- 14:C6 ⇒ 00:B14: the master's key `FRC.Ledger.p00170` from the paper's key `FRC.Entropy.p14023` and 00:A14's frame
(`frame_exists`): on a prime `Ω = 4S + 1` an element of order eight exists iff `S` is even. -/
theorem b14_of_14C6 : ∀ {Ω : Nat} [Pos Ω] (S : Nat), FRC.Nat.isPrime Ω → Ω = 4 * S + 1 →
    ((∃ ζ : Shell Ω, ζ ^ 8 = 1 ∧ ζ ^ 4 ≠ 1) ↔ S % 2 = 0) := by
  intro Ω _ S hp hcap
  have hS : 0 < S := by
    match S, hcap with
    | 0, e => rw [e] at hp; exact absurd hp.1 (by decide)
    | k + 1, _ => exact Nat.zero_lt_succ k
  obtain ⟨g, F⟩ := frame_exists hp hcap hS
  have hk := FRC.Entropy.p14023.2.1 F
  have hne := frame_neg_one_ne_one F
  constructor
  · intro ⟨ζ, h8, h4⟩
    have h4' : ζ ^ 4 = -1 :=
      match Prime.sq_eq_one hp (by rw [← pow_add]; exact h8 : ζ ^ 4 * ζ ^ 4 = 1) with
      | .inl e => absurd e h4
      | .inr e => e
    obtain ⟨m, hm⟩ := hk.1 ⟨ζ, h4', h8⟩
    exact FRC.Nat.mod_unique (by decide) (by rw [hm, Nat.add_zero])
  · intro he
    obtain ⟨m, hm⟩ := FRC.Nat.mod_spec 2 (by decide) S
    rw [he, Nat.add_zero] at hm
    obtain ⟨ζ, h4, h8⟩ := hk.2 ⟨m, hm⟩
    exact ⟨ζ, h8, by rw [h4]; exact hne⟩

end FRC.Bridge
