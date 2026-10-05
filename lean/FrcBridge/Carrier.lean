import FrcCore.Keys.Carrier
import FrcCore.Dimensions
import FrcCore.Entropy

/-!
# FrcBridge.Carrier — the bridges of the Carrier's counterpart pairs (ledger migration, task LM34, landed with LM22)

A bridge states the clause two rows share and derives it from each row's core declaration, so the two keys are seen to
agree on it. One namespace per pair, `FRC.Bridge.<master>_<paper>`: `Clause` the shared clause, `from_master` and
`from_paper` its two derivations. The master's keys are on the Carrier's chart without a generator; the papers' on a
frame `(τ; 0, 1, g)`, which makes the shell prime (`frame_isPrime`), so the shared clause is stated on frames.
No axioms (`check_core_axioms.py`).

* **00:B7 and 10:E4 (overlap, LM06).** `G` exact: `2x + 1 = 0` iff `x = 2S`; and a square fixes its root up to sign.
* **00:B14 and 14:C6 (unclassified: B14 was split from L3 by LM10, after LM06).** The octant sector: an element with
  `ζ⁴ = −1` and `ζ⁸ = 1` exists iff the capacity is even.
-/

namespace FRC.Bridge

open FRC.Shell

/-- Every framed shell is prime: a frame `(τ; 0, 1, g)` has no zero divisors, and completeness is primality
(`Shell.Prime.isPrime_of_no_zero_divisors`). -/
theorem frame_isPrime {p κ : Nat} [Pos p] {g : Shell p} (F : Frame p κ g) : FRC.Nat.isPrime p :=
  Prime.isPrime_of_no_zero_divisors (Nat.le_of_lt F.two_lt_p) (fun h => F.mul_eq_zero h)

/-- `−1 ≠ 1` on a frame. -/
theorem frame_neg_one_ne_one {p κ : Nat} [Pos p] {g : Shell p} (F : Frame p κ g) : (-1 : Shell p) ≠ 1 :=
  Prime.neg_one_ne_one F.two_lt_p

namespace B7_10E4

/-- The clause 00:B7 and 10:E4 share, on a frame of capacity `S`: `G = 2S` is the one solution of `2x + 1 = 0`, and
`x² = y²` gives `x = ±y`. -/
def Clause (Ω S : Nat) [Pos Ω] : Prop :=
  (∀ x : Shell Ω, 2 * x + 1 = 0 ↔ x = ofNat (2 * S)) ∧ (∀ x y : Shell Ω, x * x = y * y → x = y ∨ x = -y)

/-- From the master's key `FRC.Ledger.p00165` (00:B7). -/
theorem from_master {Ω S : Nat} [Pos Ω] {g : Shell Ω} (F : Frame Ω S g) : Clause Ω S := by
  obtain ⟨_, _, hG2, hG, _, _, _, hsq, _⟩ := FRC.Ledger.p00165 S (frame_isPrime F) F.cap
  refine ⟨fun x => ⟨fun h => hG x (eq_neg_of_add_eq_zero h), fun h => ?_⟩, hsq⟩
  show 2 * x + 1 = 0
  rw [h, show (ofNat (2 * S) : Shell Ω) = Carrier.grav Ω S from rfl, hG2, neg_add]

/-- From the paper's key `FRC.Dimensions.p10027` (10:E4). -/
theorem from_paper {Ω S : Nat} [Pos Ω] {g : Shell Ω} (F : Frame Ω S g) : Clause Ω S := by
  obtain ⟨hG, hpair, _⟩ := FRC.Dimensions.p10027
  refine ⟨hG F, fun x y h => ?_⟩
  match Shell.instDecidableEq y 0 with
  | .isTrue hy =>
    rw [hy, mul_zero] at h
    have hx : x = 0 := match F.mul_eq_zero h with | .inl e => e | .inr e => e
    exact .inl (hx.trans hy.symm)
  | .isFalse hy => exact ((hpair F (y * y) y rfl hy).1 x).1 h

end B7_10E4

namespace B14_14C6

/-- The clause 00:B14 and 14:C6 share, on a frame of capacity `κ`: an element with `ζ⁴ = −1` and `ζ⁸ = 1` exists
iff `κ` is even. -/
def Clause (p κ : Nat) [Pos p] : Prop := (∃ ζ : Shell p, ζ ^ 4 = -1 ∧ ζ ^ 8 = 1) ↔ ∃ m, κ = 2 * m

/-- From the master's key `FRC.Ledger.p00170` (00:B14). -/
theorem from_master {p κ : Nat} [Pos p] {g : Shell p} (F : Frame p κ g) : Clause p κ := by
  have hk := FRC.Ledger.p00170 κ (frame_isPrime F) F.cap
  have hne := frame_neg_one_ne_one F
  constructor
  · intro ⟨ζ, h4, h8⟩
    have he := hk.1 ⟨ζ, h8, by rw [h4]; exact hne⟩
    obtain ⟨m, hm⟩ := FRC.Nat.mod_spec 2 (by decide) κ
    rw [he, Nat.add_zero] at hm
    exact ⟨m, hm⟩
  · intro ⟨m, hm⟩
    obtain ⟨ζ, h8, h4⟩ := hk.2 (FRC.Nat.mod_unique (by decide) (by rw [hm, Nat.add_zero]))
    refine ⟨ζ, ?_, h8⟩
    match Prime.sq_eq_one (frame_isPrime F) (by rw [← pow_add]; exact h8 : ζ ^ 4 * ζ ^ 4 = 1) with
    | .inl e => exact absurd e h4
    | .inr e => exact e

/-- From the paper's key `FRC.Entropy.p14023` (14:C6). -/
theorem from_paper {p κ : Nat} [Pos p] {g : Shell p} (F : Frame p κ g) : Clause p κ :=
  FRC.Entropy.p14023.2.1 F

end B14_14C6

end FRC.Bridge
