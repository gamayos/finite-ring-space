import FrcCore.Keys.Fourier
import FrcCore.Keys.Frame

/-!
# FrcBridge.Fourier — the bridges of the master's rows C2 and C7 (ledger migration, task LM34, landed with LM25)

A bridge states the clause two rows share and derives it from each row's core declaration. One namespace per pair,
`FRC.Bridge.<master>_<paper>`: `Clause` the shared clause, `from_master` and `from_paper` its two derivations, on a
frame `(τ; 0, 1, g)`. No axioms (`check_core_axioms.py`).

* **00:C2 and 6:B5 (overlap, LM06).** The transform is the quarter-turn of the four-cycle: `F² = J`.
* **00:C2 and 6:D4 (overlap, LM06).** Dilation shifts the cycle index: `S_r(M_m) = M_{m+r}`.
* **00:C7 and 1:B3 (master implies paper, LM06).** The oriented quarter-turn `i = −g^κ` squares to `−1`.
-/

namespace FRC.Bridge

open FRC.Shell

namespace C2_6B5

/-- The clause 00:C2 and 6:B5 share, on a frame: `F² = J` on the cycle. -/
def Clause (p κ : Nat) [Pos p] (g : Shell p) : Prop :=
  ∀ k j, k < p - 1 → j < p - 1 → sumRange (fun l => Frame.Fmat g κ k l * Frame.Fmat g κ l j) (p - 1) = Frame.J (p - 1) k j

/-- From the master's key `FRC.Ledger.p00022` (00:C2): `F^{[κ]} F^{[κ]} = F^{[2κ]}` with the cardinal values. -/
theorem from_master {p κ : Nat} [Pos p] {g : Shell p} (F : Frame p κ g) : Clause p κ g := fun k j hk hj => by
  obtain ⟨z, hz⟩ := F.exists_inv F.g_ne_zero
  have K := FRC.Ledger.p00022 F hz
  have e := K.2.2.1 κ κ k j hk hj
  rw [← Nat.two_mul, (K.2.2.2.2.1 k j).2.2.1] at e
  rw [e]
  exact sum_congr _ (fun l _ => by rw [(K.2.2.2.2.1 k l).2.1, (K.2.2.2.2.1 l j).2.1])

/-- From the paper's key `FRC.Ledger.p06012` (6:B5). -/
theorem from_paper {p κ : Nat} [Pos p] {g : Shell p} (F : Frame p κ g) : Clause p κ g := fun k j _ _ =>
  FRC.Ledger.p06012.2.1 F k j

end C2_6B5

namespace C2_6D4

/-- The clause 00:C2 and 6:D4 share: the dilation `S_r` advances the meridian index, `S_r(M_m) = M_{m+r}`. -/
def Clause (p κ : Nat) [Pos p] (g : Shell p) : Prop :=
  ∀ m r, (meridian g κ m).map (scale g r) = meridian g κ (m + r)

/-- From the master's key `FRC.Ledger.p00022` (00:C2). -/
theorem from_master {p κ : Nat} [Pos p] {g : Shell p} (F : Frame p κ g) : Clause p κ g := by
  obtain ⟨z, hz⟩ := F.exists_inv F.g_ne_zero
  exact (FRC.Ledger.p00022 F hz).1

/-- From the paper's key `FRC.Ledger.p06027` (6:D4). -/
theorem from_paper {p κ : Nat} [Pos p] {g : Shell p} (_F : Frame p κ g) : Clause p κ g :=
  fun m r => FRC.Ledger.p06027.1 g κ m r

end C2_6D4

namespace C7_1B3

/-- The clause 00:C7 and 1:B3 share: the oriented quarter-turn `i = −g^κ` squares to `−1`. -/
def Clause (p κ : Nat) [Pos p] (g : Shell p) : Prop := Frame.quarterTurn g κ * Frame.quarterTurn g κ = -1

/-- From the master's key `FRC.Ledger.p00172` (00:C7): `i = (g⁻¹)^κ`, so `g^κ i = 1` and `i = −g^κ`. -/
theorem from_master {p κ : Nat} [Pos p] {g : Shell p} (F : Frame p κ g) : Clause p κ g := by
  obtain ⟨z, hz⟩ := F.exists_inv F.g_ne_zero
  have hzk := (FRC.Ledger.p00172 F hz).2.1
  have e : g ^ κ * z ^ κ = 1 := by rw [← mul_pow, hz, one_pow]
  rw [hzk] at e
  show -(g ^ κ) * -(g ^ κ) = -1
  rw [neg_mul_neg]
  have e' : g ^ κ * -(g ^ κ) = 1 := e
  rw [← mul_neg] at e'
  rw [← neg_neg (g ^ κ * g ^ κ), e']

/-- From the paper's key `FRC.Ledger.p01005` (1:B3). -/
theorem from_paper {p κ : Nat} [Pos p] {g : Shell p} (F : Frame p κ g) : Clause p κ g := FRC.Ledger.p01005.1 F

end C7_1B3

end FRC.Bridge
