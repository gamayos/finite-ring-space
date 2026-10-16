import FrcCore.Keys.Carrier
import FrcCore.Keys.Interactions

/-!
# FrcBridge.Interactions — the bridges of the interactions theme's counterpart pairs (27-fields, 16 October 2026)

A bridge states the clause two rows share and derives it from each row's core key, so the two keys are seen to agree
on it. One namespace per pair, `FRC.Bridge.<master>_<paper>`: `Clause` the shared clause, `from_master` and
`from_paper` its two derivations. No axioms (`check_core_axioms.py`).

* **00:B5 and 27:C11.** The substrate residue: `n ≡ 5 (mod 12)` iff `n ≡ 1 (mod 4)` and `n ≡ 2 (mod 3)`. The master's
  key states the two congruences as divisibilities, `4 ∣ n − 1` and `3 ∣ n + 1`; the paper's as residues. The bridge
  reads one as the other with the axiom-free remainder lemmas of `FrcCore/Nat.lean`.

The other pairs of 27-fields with core proofs on both sides share a theorem (00:G11 with 27:C8, 00:G16 with 27:P8,
00:G7 with 27:P9) or share no Lean clause (00:E1 with 27:C2, 00:G12 with 27:C8 and 27:X8); `coverage.json` records
each.
-/

namespace FRC.Bridge

namespace B5_27C11

/-- The clause 00:B5 and 27:C11 share: for every natural number `n`, `n ≡ 5 (mod 12)` iff `n ≡ 1 (mod 4)` and
`n ≡ 2 (mod 3)`. -/
def Clause : Prop := ∀ n : Nat, n % 12 = 5 ↔ n % 4 = 1 ∧ n % 3 = 2

/-- `k ∣ n` iff `n % k = 0`, for `0 < k` (`FRC.Nat.mod_spec`, `FRC.Nat.add_mul_mod_self_left`). -/
theorem dvd_iff_mod {n k : Nat} (hk : 0 < k) : k ∣ n ↔ n % k = 0 := by
  constructor
  · intro h
    obtain ⟨c, hc⟩ := h
    rw [hc, ← Nat.add_zero (k * c), FRC.Nat.add_mul_mod_self_left 0 c k hk]
    exact FRC.Nat.zero_mod k
  · intro h
    obtain ⟨q, hq⟩ := FRC.Nat.mod_spec k hk n
    rw [h, Nat.add_zero] at hq
    exact ⟨q, hq⟩

/-- A number with a nonzero residue is positive. -/
theorem one_le_of_mod_ne {n p r : Nat} (h : n % p = r) (hr : r ≠ 0) : 1 ≤ n := by
  cases n with
  | zero => exact absurd (h.symm.trans (FRC.Nat.zero_mod p)) hr
  | succ m => exact Nat.succ_le_succ (Nat.zero_le m)

/-- `n = (n − 1) + 1` for `1 ≤ n` (`FRC.Nat.sub_add_cancel`). -/
theorem pred_succ {n : Nat} (h : 1 ≤ n) : n = n - 1 + 1 := (FRC.Nat.sub_add_cancel h).symm

/-- From the master's key `FRC.Ledger.p00015` (00:B5): its first clause, `(4 ∣ n − 1 ∧ 3 ∣ n + 1) ↔ n % 12 = 5`, with
each divisibility read as a residue. -/
theorem from_master : Clause := by
  intro n
  have hm := FRC.Ledger.p00015.1 n
  constructor
  · intro h5
    obtain ⟨h4, h3⟩ := hm.2 h5
    have hn : 1 ≤ n := one_le_of_mod_ne h5 (by decide)
    have e4 : (n - 1) % 4 = 0 := (dvd_iff_mod (by decide)).1 h4
    have e3 : (n + 1) % 3 = 0 := (dvd_iff_mod (by decide)).1 h3
    constructor
    · rw [pred_succ hn, FRC.Nat.add_mod _ _ _ (by decide), e4]
    · rw [FRC.Nat.add_mod _ _ _ (by decide)] at e3
      have hr := FRC.Nat.mod_lt' n (by decide : 0 < 3)
      exact (by decide : ∀ r, r < 3 → (r + 1 % 3) % 3 = 0 → r = 2) (n % 3) hr e3
  · intro h
    obtain ⟨h4, h3⟩ := h
    have hn : 1 ≤ n := one_le_of_mod_ne h4 (by decide)
    apply hm.1
    constructor
    · apply (dvd_iff_mod (by decide)).2
      have e : (n - 1 + 1) % 4 = 1 := (pred_succ hn) ▸ h4
      rw [FRC.Nat.add_mod _ _ _ (by decide)] at e
      have hr := FRC.Nat.mod_lt' (n - 1) (by decide : 0 < 4)
      exact (by decide : ∀ r, r < 4 → (r + 1 % 4) % 4 = 1 → r = 0) ((n - 1) % 4) hr e
    · apply (dvd_iff_mod (by decide)).2
      rw [FRC.Nat.add_mod _ _ _ (by decide), h3]

/-- From the paper's key `FRC.Ledger.p27023` (27:C11): its first conjunct is the clause itself
(`FRC.Interactions.residue_five`). -/
theorem from_paper : Clause := FRC.Ledger.p27023.1

end B5_27C11

end FRC.Bridge
