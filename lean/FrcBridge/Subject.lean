import FrcCore.Keys.Subject
import FrcCore.Theme.Subject
import FrcCore.Geometry
import FrcCore.Dirac
import FrcCore.Fourier
import FrcCore.Epi
import FrcCore.Dimensions

/-!
# FrcBridge.Subject — the bridges of the Subject's counterpart pairs (ledger migration, task LM34, landed with LM24)

A bridge states the clause two rows share and derives it from each row's core declaration, so the two keys are seen to
agree on it. One namespace per pair, `FRC.Bridge.<master>_<paper>`: `Clause` the shared clause, `from_master` and
`from_paper` its two derivations, on a frame `(τ; 0, 1, g)`. No axioms (`check_core_axioms.py`).

* **00:C1 and 2:D1 (master implies paper, LM06).** The half-period `g^{2κ} = −1`.
* **00:C3 and 8:B3 (overlap, LM09).** The drive is a nonsquare, and `2⁻¹` is a square iff `κ` is even.
* **00:C3 and 8:B4 (overlap, LM09).** `ν = g = 2⁻¹ · (2g)`, and `2g` is a square iff `κ` is odd.
* **00:C8 and 8:B5 (overlap, LM06).** `g^m` is a square iff `m` is even.
* **00:C8 and 8:B6 (overlap, LM06).** The inverse drive is a nonsquare.
* **00:C14 and 2:D6, 00:C14 and 6:B2 (master implies paper, LM06).** The Euler identity `(gⁱ)^{2κi} = (−1)ⁱ`.
* **00:C14 and 13:B2 (overlap, LM06).** Every frame is a power `g^u`, its quarter-turn `i` when `u ≡ 1 (mod 4)` and
  `−i` when `u ≡ 3`.
* **00:C20 and 8:F4 (overlap, LM06).** `C_{p−1}` meets `C_{p+1}` in the sign: `x^{p+1} = 1` with `x ≠ 0` forces
  `x = ±1`.
* **C13's part 10:G2 (overlap, LM06).** C13 is an X row with no key; the theme's `exponent_ladder`, on every capacity,
  gives paper 10's instances (`from_theme`).
-/

namespace FRC.Bridge

open FRC.Shell

namespace C1_2D1

/-- The clause 00:C1 and 2:D1 share: the half-period, `g^{2κ} = −1`. -/
def Clause (p κ : Nat) [Pos p] (g : Shell p) : Prop := g ^ (2 * κ) = -1

/-- From the master's key `FRC.Ledger.p00021` (00:C1). -/
theorem from_master {p κ : Nat} [Pos p] {g : Shell p} (F : Frame p κ g) : Clause p κ g := (FRC.Ledger.p00021 F).2.1

/-- From the paper's key `FRC.Geometry.p02013` (2:D1). -/
theorem from_paper {p κ : Nat} [Pos p] {g : Shell p} (F : Frame p κ g) : Clause p κ g := FRC.Geometry.p02013 F

end C1_2D1

namespace C3_8B3

/-- The clause 00:C3 and 8:B3 share: the drive is a nonsquare, and the half `2⁻¹` is a square iff `κ` is even. -/
def Clause (p κ : Nat) [Pos p] (g : Shell p) : Prop :=
  (¬ ∃ y : Shell p, y * y = g) ∧ ∀ h : Shell p, 2 * h = 1 → ((∃ r : Shell p, r * r = h) ↔ κ % 2 = 0)

/-- From the master's key `FRC.Ledger.p00150` (00:C3). -/
theorem from_master {p κ : Nat} [Pos p] {g : Shell p} (F : Frame p κ g) : Clause p κ g :=
  ⟨(FRC.Ledger.p00150.1 F).1, fun h h2 => ((FRC.Ledger.p00150.1 F).2.2 h h2).2.1⟩

/-- From the paper's key `FRC.Dirac.p08009` (8:B3). -/
theorem from_paper {p κ : Nat} [Pos p] {g : Shell p} (F : Frame p κ g) : Clause p κ g :=
  ⟨FRC.Dirac.p08009.1 F, fun _ h2 => (FRC.Dirac.p08009.2.2.2.1 F h2).2.1⟩

end C3_8B3

namespace C3_8B4

/-- The clause 00:C3 and 8:B4 share: `2⁻¹ · (2g) = g`, and `2g` is a square iff `κ` is odd. -/
def Clause (p κ : Nat) [Pos p] (g : Shell p) : Prop :=
  ∀ h : Shell p, 2 * h = 1 → h * (2 * g) = g ∧ ((∃ y : Shell p, y * y = 2 * g) ↔ κ % 2 = 1)

/-- From the master's key `FRC.Ledger.p00150` (00:C3). -/
theorem from_master {p κ : Nat} [Pos p] {g : Shell p} (F : Frame p κ g) : Clause p κ g := fun h h2 =>
  ⟨((FRC.Ledger.p00150.1 F).2.2 h h2).1, ((FRC.Ledger.p00150.1 F).2.2 h h2).2.2⟩

/-- From the paper's key `FRC.Dirac.p08010` (8:B4). -/
theorem from_paper {p κ : Nat} [Pos p] {g : Shell p} (F : Frame p κ g) : Clause p κ g := fun _ h2 =>
  FRC.Dirac.p08010.1 F h2

end C3_8B4

namespace C8_8B5

/-- The clause 00:C8 and 8:B5 share: `g^m` is a square iff `m` is even. -/
def Clause (p : Nat) [Pos p] (g : Shell p) : Prop := ∀ m : Nat, (∃ y : Shell p, y * y = g ^ m) ↔ m % 2 = 0

/-- From the master's key `FRC.Ledger.p00028` (00:C8). -/
theorem from_master {p κ : Nat} [Pos p] {g : Shell p} (F : Frame p κ g) : Clause p g := (FRC.Ledger.p00028.1 F).1

/-- From the paper's key `FRC.Dirac.p08011` (8:B5). -/
theorem from_paper {p κ : Nat} [Pos p] {g : Shell p} (F : Frame p κ g) : Clause p g := FRC.Dirac.p08011 F

end C8_8B5

namespace C8_8B6

/-- The clause 00:C8 and 8:B6 share: the inverse drive `g⁻¹` is a nonsquare. -/
def Clause (p : Nat) [Pos p] (g : Shell p) : Prop := ∀ y : Shell p, g * y = 1 → ¬ ∃ r : Shell p, r * r = y

/-- From the master's key `FRC.Ledger.p00028` (00:C8). -/
theorem from_master {p κ : Nat} [Pos p] {g : Shell p} (F : Frame p κ g) : Clause p g :=
  (FRC.Ledger.p00028.1 F).2.2.1

/-- From the paper's key `FRC.Dirac.p08012` (8:B6). -/
theorem from_paper {p κ : Nat} [Pos p] {g : Shell p} (F : Frame p κ g) : Clause p g := fun _ hy =>
  FRC.Dirac.p08012.2 F hy

end C8_8B6

namespace C14_Euler

/-- The clause 00:C14 shares with 2:D6 and with 6:B2: the Euler identity `(gⁱ)^{i·2κ} = (−1)ⁱ` for every lift `i`. -/
def Clause (p κ : Nat) [Pos p] (g : Shell p) : Prop :=
  ∀ i : Nat, (g ^ i) ^ (i * (2 * κ)) = if i % 2 = 0 then 1 else -1

/-- From the master's key `FRC.Ledger.p00034` (00:C14). -/
theorem from_master {p κ : Nat} [Pos p] {g : Shell p} (F : Frame p κ g) : Clause p κ g := (FRC.Ledger.p00034.1 F).1   -- the key's first conjunct since C14's rebinding of 9 October 2026

/-- From 2:D6's key `FRC.Geometry.p02018`. -/
theorem from_2D6 {p κ : Nat} [Pos p] {g : Shell p} (F : Frame p κ g) : Clause p κ g := FRC.Geometry.p02018.1 F

/-- From 6:B2's key `FRC.Fourier.p06009`. -/
theorem from_6B2 {p κ : Nat} [Pos p] {g : Shell p} (F : Frame p κ g) : Clause p κ g := FRC.Fourier.p06009 F

end C14_Euler

namespace C14_13B2

/-- The clause 00:C14 and 13:B2 share: every frame `g'` of the shell is a power `g^u`, and its quarter-turn is `g`'s
when `u ≡ 1 (mod 4)` and the negative when `u ≡ 3` (fixed within a chirality, flipped in the conjugate). -/
def Clause (p κ : Nat) [Pos p] (g : Shell p) : Prop :=
  ∀ g' : Shell p, Frame p κ g' → ∃ u : Nat, g ^ u = g' ∧
    (u % 4 = 1 → Frame.quarterTurn g' κ = Frame.quarterTurn g κ) ∧
    (u % 4 = 3 → Frame.quarterTurn g' κ = -Frame.quarterTurn g κ)

/-- From the master's key `FRC.Ledger.p00034` (00:C14). -/
theorem from_master {p κ : Nat} [Pos p] {g : Shell p} (F : Frame p κ g) : Clause p κ g := fun g' F' => by
  obtain ⟨u, _, e, _, h1, h3, _⟩ := (FRC.Ledger.p00034.1 F).2.2.2.2 g' F'
  exact ⟨u, e, h1, h3⟩

/-- From the paper's key `FRC.Epi.p13009` (13:B2), its orientation class, with `g' = g^u` found on the frame. -/
theorem from_paper {p κ : Nat} [Pos p] {g : Shell p} (F : Frame p κ g) : Clause p κ g := fun g' F' => by
  obtain ⟨u, _, e⟩ := F.eq_pow_of_ne_zero F'.g_ne_zero
  refine ⟨u, e, fun h => ?_, fun h => ?_⟩
  · rw [← e]; exact (FRC.Epi.p13009.2 F u).1 h
  · rw [← e]; exact (FRC.Epi.p13009.2 F u).2 h

end C14_13B2

namespace C20_8F4

/-- The clause 00:C20 and 8:F4 share: the winding sector `C_{p−1}` meets the boost torus `C_{p+1}` in the sign alone,
`x^{p+1} = 1` with `x ≠ 0` forcing `x = ±1`. -/
def Clause (p : Nat) [Pos p] : Prop := ∀ x : Shell p, x ≠ 0 → x ^ (p + 1) = 1 → x = 1 ∨ x = -1

/-- From the master's key `FRC.Ledger.p00040` (00:C20), with the frame's quarter-turn. -/
theorem from_master {p κ : Nat} [Pos p] {g : Shell p} (F : Frame p κ g) : Clause p := fun x hx e =>
  ((FRC.Ledger.p00040.1 (FRC.Subject.frame_isPrime F) F.quarter_turn_sq).1 x hx).1 e

/-- From the paper's key `FRC.Dirac.p08041` (8:F4), with Fermat's `x^{p+1} = x²` and the inverse drive `g^{p−2}`. -/
theorem from_paper {p κ : Nat} [Pos p] {g : Shell p} (F : Frame p κ g) : Clause p := fun x hx e => by
  have hp := FRC.Subject.frame_isPrime F
  have hpm : p - 1 = p - 2 + 1 := by
    match p, hp.1 with
    | k + 2, _ => rfl
  have hinv : g * g ^ (p - 2) = 1 := by rw [mul_comm, ← pow_succ, ← hpm, Prime.fermat hp F.g_ne_zero]
  have hx2 : x * x = 1 := by
    have e2 : p + 1 = p - 1 + 2 := by
      match p, hp.1 with
      | k + 2, _ => rfl
    rw [e2, pow_add, Prime.fermat hp hx, one_mul, pow_two] at e
    exact e
  exact (FRC.Dirac.p08041 F hinv).2 x hx2

end C20_8F4

namespace C13_10G2

/-- The clause C13's part 10:G2 states on paper 10's instances: the window ladder holds at `κ = 17`, `387` and
`602 140` and fails at the toy `κ = 3`, with the coherence identity `(2√κ)² = 4κ = p − 1`. -/
def Clause : Prop :=
  16 * 17 < 17 * 17 ∧ 16 * 387 < 387 * 387 ∧ 16 * 602140 < 602140 * 602140 ∧ ¬ 16 * 3 < 3 * 3 ∧
    ∀ κ : Nat, 2 * 2 * κ = 4 * κ + 1 - 1

/-- From the theme's `FRC.Subject.exponent_ladder`, on every capacity (C13 has no key). -/
theorem from_theme : Clause :=
  ⟨(FRC.Subject.exponent_ladder.1 17).2 (by decide), (FRC.Subject.exponent_ladder.1 387).2 (by decide),
   (FRC.Subject.exponent_ladder.1 602140).2 (by decide),
   fun h => absurd ((FRC.Subject.exponent_ladder.1 3).1 h) (by decide), FRC.Subject.exponent_ladder.2.2⟩

/-- From the paper's key `FRC.Dimensions.p10038` (10:G2). -/
theorem from_paper : Clause :=
  match FRC.Dimensions.p10038 with
  | ⟨h1, h2, h3, h4, h5, _⟩ => ⟨h1, h2, h3, h4, fun κ => (h5 κ).1.trans (h5 κ).2⟩

end C13_10G2

end FRC.Bridge
