import FrcCore.FrameCore

/-!
# FrcCore.Parity — the square class of the drive is the parity of its exponent (the frame theme)

On every frame `g^m` is a square exactly when the drive-step count `m` is even (8:B5, `parity_iff`); the drive and its
inverse are nonsquares (8:B3, 8:B6). Split from `Orbit.lean` by the ledger migration (task LM24), every name unchanged,
so that a theme needing the square class does not carry the orbit of the generators; `Orbit.lean` imports this file.
No axioms.
-/

namespace FRC
namespace Shell
namespace Frame
variable {p : Nat} [Pos p] {κ : Nat} {g : Shell p}

/-! ## The square class of the drive is the parity of its exponent (moved from 8-dirac, task LM17) -/

theorem two_mul_mod (l : Nat) : (2 * l) % 2 = 0 := by
  rw [← Nat.add_zero (2 * l)]; exact FRC.Nat.add_mul_mod_self_left 0 l 2 (Nat.zero_lt_succ 1)

theorem mod_two_of_mod_four_mul (m q : Nat) : (4 * q + m) % 2 = m % 2 := by
  have : 4 * q + m = 2 * (2 * q) + m := by rw [← FRC.Nat.mul_assoc]
  rw [this, FRC.Nat.add_mul_mod_self_left m (2 * q) 2 (Nat.zero_lt_succ 1)]

theorem mod_n_mod_two (F : Frame p κ g) (m : Nat) : (m % (p - 1)) % 2 = m % 2 := by
  match FRC.Nat.mod_spec (p - 1) F.n_pos m with
  | ⟨q, hq⟩ =>
    have e : m = 4 * (κ * q) + m % (p - 1) := by
      rw [← FRC.Nat.mul_assoc, ← F.n_eq]; exact hq
    calc (m % (p - 1)) % 2 = (4 * (κ * q) + m % (p - 1)) % 2 := (mod_two_of_mod_four_mul _ _).symm
      _ = m % 2 := by rw [← e]

/-- 8:B5 — the square class is chronon parity: on every frame, `g^m` is a square exactly when the drive-step
count `m` is even (Theorem `parity`). -/
theorem parity_iff (F : Frame p κ g) (m : Nat) : (∃ y : Shell p, y * y = g ^ m) ↔ m % 2 = 0 := by
  constructor
  · rintro ⟨y, hy⟩
    have hy0 : y ≠ 0 := fun h0 => F.pow_ne_zero m (by rw [← hy, h0, Shell.mul_zero])
    obtain ⟨l, hl, hgl⟩ := F.eq_pow_of_ne_zero hy0
    have h2 : g ^ (2 * l) = g ^ m := by
      rw [Nat.mul_comm, Shell.pow_mul, Shell.pow_two, hgl]; exact hy
    rw [F.pow_mod, F.pow_mod m] at h2
    have h3 := F.pow_inj (Nat.mod_lt _ F.n_pos) (Nat.mod_lt _ F.n_pos) h2
    rw [← mod_n_mod_two F m, ← h3, mod_n_mod_two F]
    exact two_mul_mod l
  · intro h
    match FRC.Nat.mod_spec 2 (Nat.zero_lt_succ 1) m with
    | ⟨q, hq⟩ =>
      rw [h, Nat.add_zero] at hq
      exact ⟨g ^ q, by rw [hq, Nat.mul_comm, Shell.pow_mul, Shell.pow_two]⟩

/-- 8:B3 — the drive is a nonsquare on every frame (`m = 1`). -/
theorem drive_nonsquare (F : Frame p κ g) : ¬ ∃ y : Shell p, y * y = g := fun ⟨y, hy⟩ =>
  Nat.noConfusion ((parity_iff F 1).1 ⟨y, by rw [Shell.pow_one]; exact hy⟩)

theorem mod_two_cases (m : Nat) : m % 2 = 0 ∨ m % 2 = 1 := by
  have := Nat.mod_lt m (Nat.zero_lt_succ 1)
  match m % 2, this with
  | 0, _ => exact .inl rfl
  | 1, _ => exact .inr rfl
  | k + 2, hk => exact absurd hk (Nat.not_lt_of_le (Nat.le_add_left 2 k))

theorem succ_mod_two_eq_zero_iff (m : Nat) : (m + 1) % 2 = 0 ↔ m % 2 = 1 := by
  rw [FRC.Nat.add_mod m 1 2 (Nat.zero_lt_succ 1)]
  rcases mod_two_cases m with h | h <;> rw [h]
  · exact ⟨fun e => Nat.noConfusion e, fun e => Nat.noConfusion e⟩
  · exact ⟨fun _ => rfl, fun _ => rfl⟩

/-- The inverse of the drive is `g^{p−2}`: every `y` with `g y = 1` is an odd power of `g`. -/
theorem inv_drive_odd (F : Frame p κ g) {y : Shell p} (hy : g * y = 1) :
    ∃ l, l < p - 1 ∧ g ^ l = y ∧ l % 2 = 1 := by
  have hy0 : y ≠ 0 := fun h0 => F.one_ne_zero (by rw [← hy, h0, Shell.mul_zero])
  obtain ⟨l, hl, hgl⟩ := F.eq_pow_of_ne_zero hy0
  refine ⟨l, hl, hgl, ?_⟩
  have h1 : g ^ (l + 1) = 1 := by rw [Shell.pow_succ, hgl, Shell.mul_comm]; exact hy
  have h2 := F.mod_eq_zero_of_pow_eq_one h1
  have h3 : l + 1 = p - 1 := by
    match Nat.lt_or_ge (l + 1) (p - 1) with
    | .inl hlt => exact absurd (by rw [FRC.Nat.mod_eq_of_lt hlt] at h2; exact h2) (Nat.succ_ne_zero l)
    | .inr hge => exact Nat.le_antisymm (Nat.succ_le_of_lt hl) hge
  have h4 : (l + 1) % 2 = 0 := by
    rw [h3, F.n_eq, ← Nat.add_zero (4 * κ), mod_two_of_mod_four_mul]
  exact (succ_mod_two_eq_zero_iff l).1 h4

/-- 8:B3, 8:B6 — the reframing flip preserves the class: the inverse of the drive is a nonsquare (an odd
power of `g`), so `[g⁻¹] = [g]`. -/
theorem inv_drive_nonsquare (F : Frame p κ g) {y : Shell p} (hy : g * y = 1) :
    ¬ ∃ r : Shell p, r * r = y := fun h => by
  obtain ⟨l, _, hgl, hodd⟩ := inv_drive_odd F hy
  rw [← hgl] at h
  have h2 := (parity_iff F l).1 h
  rw [hodd] at h2
  exact Nat.noConfusion h2

end Frame
end Shell
end FRC
