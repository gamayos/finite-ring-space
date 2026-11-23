import FrcCore.Theme.Window

/-!
# FrcCore.Theme.Forced — the forced rule in transfer units (the relaxation theme; 21 November 2026)

The re-registration rule of `Theme/Window.lean` with the Carrier's forcing added (21-gravity, Lemma 3.3(iv), the review
of 21 November 2026). The link's mismatch counted in transfers is one integer, `Ψ = B μ + (B − 1 − acc)`: the registered
quanta are `Ψ / B`, the accumulator `B − 1 − Ψ % B`, and under a forcing of `d` transfers per chronon the rule reads
`Ψ ↦ Ψ + d − M (Ψ / B)` (`fstep`, `frun`). `Nat` arithmetic throughout, with the division algorithm's quotient face from
`Theme/Window.lean` (`FRC.Nat.div_spec`, `div_unique`) rather than the library's lemmas, which carry `propext`; no axioms.

* `fstep_fixed` — a level whose count equals the forcing is fixed; `fstep_of_lt`, `fstep_of_gt` — the count falls by the
  excess `u = M μ − d`, rises by the deficit `w = d − M μ`.
* `level_of_bounds`, `level_mono`, `level_lt_of_lt`, `lt_of_level_lt`, `lt_level_top` — the level `Ψ / B`.
* `band_invariant`, `band_run` — the lock band `B m − u ≤ Ψ ≤ B m + w − 1` at the lock level `m` (`M (m − 1) + w = d`,
  `M m = d + u`) is invariant, for every later chronon; `band_translation`, `band_iterate` — on the band the step is the
  translation by `w` on the `u + w` values (`x ↦ (x + w) % (u + w)` with `x = Ψ + u − B m`), and `k` steps translate by
  `k w`; `band_return` — `k` chronons with `(u + w) ∣ k w` bring every band value back: every orbit has period
  `(u + w)/gcd(u, w)` (the least such `k`) and spends `w/(u + w)` of its chronons at level `m`, the counting of which
  is the python check's.
* `falls_within`, `descends`, `lock_invariant`, `locks` — the descent: from a level between `m` and `n` the count enters
  the band within `Σ_{μ = m}^{n} k μ` chronons (`k μ · u μ ≥ B`) and stays; the hypotheses name the levels `m..n` alone.
* `rises_within`, `ascends`, `lock_invariant_below`, `locks_from_below` — the ascent: from a level between `m − j` and
  `m − 1` (every such level short of the forcing by `w μ ≥ 1`, `k μ · w μ ≥ B`) the count enters the band within
  `Σ k μ` chronons and stays.
* `upperCount`, `band_balance`, `band_occupancy`, `band_occupancy_period`, `band_period` — the band's balance
  (`Ψ_t + N₂ u = Ψ + (t − N₂) w`), the occupation over any return (`N₂ (u + w) = p w`), the period `a + b` with exactly
  `b` chronons at level `m` for `u = g a`, `w = g b`, and its minimality when `b` is invertible modulo `a + b`.
The far window's readout of a clock (21:B12, 21:C12: `clockTicks`, `no_tick_iff`, `one_tick_outside`) is in
`Theme/Readout.lean`.
-/

namespace FRC.Relaxation

variable {M : Nat → Nat} {B : Nat}

/-- The link's mismatch counted in transfers, `Ψ = B μ + (B − 1 − acc)`: the registered quanta are `Ψ / B` and the
accumulator `B − 1 − Ψ % B`. With the Carrier forcing `d` transfers per chronon the rule reads `Ψ ↦ Ψ + d − M (Ψ / B)`:
one integer state carries the reference, the unresolved sector and the accumulator. -/
def fstep (M : Nat → Nat) (B d : Nat) (Ψ : Nat) : Nat := Ψ + d - M (Ψ / B)

/-- `t` chronons of the forced rule. -/
def frun (M : Nat → Nat) (B d : Nat) : Nat → Nat → Nat
  | 0, Ψ => Ψ
  | t + 1, Ψ => frun M B d t (fstep M B d Ψ)

variable {d : Nat}

theorem frun_zero (Ψ : Nat) : frun M B d 0 Ψ = Ψ := rfl

theorem frun_succ (t Ψ : Nat) : frun M B d (t + 1) Ψ = frun M B d t (fstep M B d Ψ) := rfl

theorem frun_succ' (t Ψ : Nat) : frun M B d (t + 1) Ψ = fstep M B d (frun M B d t Ψ) := by
  induction t generalizing Ψ with
  | zero => rfl
  | succ t ih => rw [frun_succ, ih]; rfl

/-- 21:C28 — a level whose count equals the forcing is fixed: the registered mismatch rests there. -/
theorem fstep_fixed {Ψ : Nat} (h : M (Ψ / B) = d) : fstep M B d Ψ = Ψ := by
  unfold fstep; rw [h, FRC.Nat.add_sub_cancel]

/-- At a level whose count exceeds the forcing by `u`, the transfer count falls by `u`. -/
theorem fstep_of_lt {Ψ u : Nat} (h : M (Ψ / B) = d + u) (hle : M (Ψ / B) ≤ Ψ + d) :
    fstep M B d Ψ + u = Ψ := by
  unfold fstep; rw [h]
  rw [h] at hle
  have hu : u ≤ Ψ := FRC.Nat.le_of_add_le_add_right (Nat.le_trans (Nat.le_of_eq (Nat.add_comm u d)) hle)
  -- Ψ + d − (d + u) = Ψ − u, through Ψ + d = (Ψ − u) + (d + u)
  have e : Ψ + d = (Ψ - u) + (d + u) := by
    rw [Nat.add_comm d u, ← Nat.add_assoc, FRC.Nat.sub_add_cancel hu]
  rw [e, FRC.Nat.add_sub_cancel, FRC.Nat.sub_add_cancel hu]

/-- At a level whose count falls short of the forcing by `w`, the transfer count rises by `w`. -/
theorem fstep_of_gt {Ψ w : Nat} (h : M (Ψ / B) + w = d) : fstep M B d Ψ = Ψ + w := by
  unfold fstep; rw [← h, Nat.add_comm (M (Ψ / B)) w, ← Nat.add_assoc, FRC.Nat.add_sub_cancel]

/-- The level of a transfer count between `B m` and `B m + (B − 1)` is `m`. -/
theorem level_of_bounds {Ψ m : Nat} (hlo : B * m ≤ Ψ) (hhi : Ψ < B * m + B) : Ψ / B = m :=
  FRC.Nat.div_unique (FRC.Nat.sub_lt_of_lt_add hhi hlo) (FRC.Nat.add_sub_of_le hlo).symm

/-- 21:C28 — the lock band is invariant. With `M (m − 1) + w = d` and `M m = d + u` (`u, w ≥ 1`: the count below the
forcing one quantum down, above it at `m`), the forced step keeps every transfer count of the band
`B m − u ≤ Ψ ≤ B m + w − 1` in the band: at level `m` the count falls by `u` and stays at or above `B m − u`, at level
`m − 1` it rises by `w` and stays at or below `B m + w − 1`. The registered mismatch moves between `m − 1` and `m` by the
translation of `band_translation`, the discrete lock-in of the Kuramoto chart. -/
theorem band_invariant (hM : ∀ μ, M μ ≤ B) {m u w : Nat} (hm : 0 < m) (hu : 0 < u)
    (hlo : M (m - 1) + w = d) (hhi : M m = d + u) {Ψ : Nat}
    (h1 : B * m ≤ Ψ + u) (h2 : Ψ + 1 ≤ B * m + w) :
    B * m ≤ fstep M B d Ψ + u ∧ fstep M B d Ψ + 1 ≤ B * m + w := by
  have huB : u ≤ B := Nat.le_trans (Nat.le_add_left u d) (Nat.le_trans (Nat.le_of_eq hhi.symm) (hM m))
  have hwB : w ≤ B := Nat.le_trans (Nat.le_add_left w (M (m - 1)))
    (Nat.le_trans (Nat.le_of_eq hlo) (Nat.le_trans (Nat.le_add_right d u) (Nat.le_trans (Nat.le_of_eq hhi.symm) (hM m))))
  have hBm : B ≤ B * m := Nat.le_mul_of_pos_right B hm
  cases Nat.lt_or_ge Ψ (B * m) with
  | inr hge =>
    have hlt : Ψ < B * m + B := Nat.lt_of_lt_of_le h2 (Nat.add_le_add_left hwB _)
    have hlev : Ψ / B = m := level_of_bounds hge hlt
    have hle : M (Ψ / B) ≤ Ψ + d := by
      rw [hlev]
      exact Nat.le_trans (hM m) (Nat.le_trans hBm (Nat.le_trans hge (Nat.le_add_right Ψ d)))
    have e : fstep M B d Ψ + u = Ψ := fstep_of_lt (by rw [hlev]; exact hhi) hle
    refine ⟨by rw [e]; exact hge, ?_⟩
    calc fstep M B d Ψ + 1 ≤ fstep M B d Ψ + u := Nat.add_le_add_left hu _
      _ = Ψ := e
      _ ≤ B * m + w := Nat.le_of_succ_le h2
  | inl hlt =>
    have hm1 : B * m = B * (m - 1) + B := by
      rw [← Nat.mul_succ, Nat.succ_eq_add_one, FRC.Nat.sub_add_cancel hm]
    have hlo' : B * (m - 1) ≤ Ψ := by
      have : B * (m - 1) + B ≤ Ψ + B := by
        rw [← hm1]; exact Nat.le_trans h1 (Nat.add_le_add_left huB Ψ)
      exact FRC.Nat.le_of_add_le_add_right this
    have hlev : Ψ / B = m - 1 := level_of_bounds hlo' (by rw [← hm1]; exact hlt)
    have e : fstep M B d Ψ = Ψ + w := fstep_of_gt (by rw [hlev]; exact hlo)
    refine ⟨?_, ?_⟩
    · rw [e, Nat.add_right_comm]; exact Nat.le_trans h1 (Nat.le_add_right _ w)
    · rw [e, Nat.add_right_comm]; exact Nat.add_le_add_right hlt w

/-- A transfer count below `B m` sits below level `m`. -/
theorem level_lt_of_lt (hB : 0 < B) {Ψ m : Nat} (h : Ψ < B * m) : Ψ / B < m := by
  cases Nat.lt_or_ge (Ψ / B) m with
  | inl hlt => exact hlt
  | inr hge =>
    exact absurd h (Nat.not_lt_of_le (Nat.le_trans (Nat.mul_le_mul_left B hge) (by
      have e := FRC.Nat.div_spec B hB Ψ
      exact Nat.le_trans (Nat.le_add_right _ _) (Nat.le_of_eq e.symm))))

/-- The level is monotone in the transfer count. -/
theorem level_mono (hB : 0 < B) {Ψ Ψ' : Nat} (h : Ψ' ≤ Ψ) : Ψ' / B ≤ Ψ / B := by
  cases Nat.lt_or_ge (Ψ / B) (Ψ' / B) with
  | inr hle => exact hle
  | inl hlt =>
    have e := FRC.Nat.div_spec B hB Ψ
    have e' := FRC.Nat.div_spec B hB Ψ'
    have hm : Ψ % B < B := FRC.Nat.mod_lt' Ψ hB
    have : Ψ < Ψ' := by
      calc Ψ = B * (Ψ / B) + Ψ % B := e
        _ < B * (Ψ / B) + B := Nat.add_lt_add_left hm _
        _ = B * (Ψ / B + 1) := (Nat.mul_succ B (Ψ / B)).symm
        _ ≤ B * (Ψ' / B) := Nat.mul_le_mul_left B hlt
        _ ≤ Ψ' := Nat.le_trans (Nat.le_add_right _ _) (Nat.le_of_eq e'.symm)
    exact absurd h (Nat.not_le_of_lt this)

/-- 21:C28 — at a level `m ≥ 1` whose count exceeds the forcing by `u ≥ 1`, the transfer count leaves the level downward
within `k` chronons whenever `k · u ≥ B`: some chronon `j ≤ k` has its level below `m`. The dwell at a level above the lock
is bounded by the window over the excess, `⌈B/(M m − d)⌉`, stated without division. -/
theorem falls_within (hM : ∀ μ, M μ ≤ B) (hB : 0 < B) {m u : Nat} (hm : 0 < m) (hmu : M m = d + u) {Ψ : Nat}
    (hlev : Ψ / B = m) (hhi : Ψ < B * m + B) {k : Nat} (hk : B ≤ k * u) :
    ∃ j, j ≤ k ∧ (frun M B d j Ψ) / B < m := by
  -- P j: either the run stayed at level m through j with Ψ_j + j u = Ψ, or some i ≤ j already sits below m
  have P : ∀ j, (frun M B d j Ψ + j * u = Ψ ∧ (frun M B d j Ψ) / B = m) ∨ ∃ i, i ≤ j ∧ (frun M B d i Ψ) / B < m := by
    intro j
    induction j with
    | zero => exact Or.inl ⟨by rw [frun_zero, Nat.zero_mul, Nat.add_zero], by rw [frun_zero]; exact hlev⟩
    | succ j ih =>
      rcases ih with ⟨hsum, hlj⟩ | ⟨i, hi, hlt⟩
      · have hge : B * m ≤ frun M B d j Ψ := by
          have e := FRC.Nat.div_spec B hB (frun M B d j Ψ)
          rw [hlj] at e; rw [e]; exact Nat.le_add_right _ _
        have hle : M ((frun M B d j Ψ) / B) ≤ frun M B d j Ψ + d := by
          rw [hlj]
          exact Nat.le_trans (hM m) (Nat.le_trans (Nat.le_mul_of_pos_right B hm) (Nat.le_trans hge (Nat.le_add_right _ _)))
        have e : fstep M B d (frun M B d j Ψ) + u = frun M B d j Ψ := fstep_of_lt (by rw [hlj]; exact hmu) hle
        have hsum' : frun M B d (j + 1) Ψ + (j + 1) * u = Ψ := by
          rw [frun_succ', Nat.succ_mul, ← Nat.add_assoc, Nat.add_right_comm, e]; exact hsum
        have hle' : frun M B d (j + 1) Ψ ≤ frun M B d j Ψ := by
          rw [frun_succ']; exact Nat.le_trans (Nat.le_add_right _ u) (Nat.le_of_eq e)
        have hmono := level_mono hB hle'
        rw [hlj] at hmono
        rcases Nat.eq_or_lt_of_le hmono with heq | hlt
        · exact Or.inl ⟨hsum', heq⟩
        · exact Or.inr ⟨j + 1, Nat.le_refl _, hlt⟩
      · exact Or.inr ⟨i, Nat.le_succ_of_le hi, hlt⟩
  rcases P k with ⟨hsum, hlk⟩ | ⟨i, hi, hlt⟩
  · -- at level m after k chronons, yet Ψ_k ≤ Ψ − B < B m: impossible
    exfalso
    have h1 : frun M B d k Ψ + B ≤ Ψ := by
      exact Nat.le_trans (Nat.add_le_add_left hk _) (Nat.le_of_eq hsum)
    have h2 : frun M B d k Ψ < B * m := by
      have : frun M B d k Ψ + B < B * m + B := Nat.lt_of_le_of_lt h1 hhi
      exact Nat.lt_of_add_lt_add_right this
    exact absurd (level_lt_of_lt hB h2) (by rw [hlk]; exact Nat.lt_irrefl m)
  · exact ⟨i, hi, hlt⟩

theorem frun_add (a b Ψ : Nat) : frun M B d (a + b) Ψ = frun M B d b (frun M B d a Ψ) := by
  induction a generalizing Ψ with
  | zero => rw [Nat.zero_add]; rfl
  | succ a ih => rw [Nat.succ_add, frun_succ, frun_succ, ih]

/-- A transfer count lies below the top of its level. -/
theorem lt_level_top (hB : 0 < B) (Ψ : Nat) : Ψ < B * (Ψ / B) + B := by
  have e := FRC.Nat.div_spec B hB Ψ
  calc Ψ = B * (Ψ / B) + Ψ % B := e
    _ < B * (Ψ / B) + B := Nat.add_lt_add_left (FRC.Nat.mod_lt' Ψ hB) _

/-- The chronon budget of the descent, `Σ_{μ = m}^{n} k μ` (zero below `m`). -/
def descentBudget (k : Nat → Nat) (m : Nat) : Nat → Nat
  | 0 => if m = 0 then k 0 else 0
  | n + 1 => (if m ≤ n + 1 then k (n + 1) else 0) + descentBudget k m n

/-- 21:C28 — the descent to the lock: when every level from `m` up to `n` has its count above the forcing
(`M μ = d + u μ`, `u μ ≥ 1`) and `k μ · u μ ≥ B`, a link whose transfer count sits at a level at most `n` reaches a level
below `m` within `Σ_{μ = m}^{n} k μ` chronons. The hypotheses speak of the levels `m..n` alone: the counts beyond the far
edge, which fall below the forcing, play no part. With `m = μ*` the lock level, the first chronon below `μ*` lands in the
lock band, which `band_invariant` then keeps. -/
theorem descends (hM : ∀ μ, M μ ≤ B) (hB : 0 < B) {m : Nat} (hm : 0 < m) (u k : Nat → Nat) :
    ∀ n, (∀ μ, m ≤ μ → μ ≤ n → 0 < u μ ∧ M μ = d + u μ) → (∀ μ, m ≤ μ → μ ≤ n → B ≤ k μ * u μ) →
      ∀ Ψ, Ψ / B ≤ n → ∃ j, j ≤ descentBudget k m n ∧ (frun M B d j Ψ) / B < m := by
  intro n
  induction n with
  | zero =>
    intro _ _ Ψ hΨ
    have h0 : Ψ / B = 0 := Nat.le_antisymm hΨ (Nat.zero_le _)
    exact ⟨0, Nat.zero_le _, by rw [frun_zero, h0]; exact hm⟩
  | succ n ih =>
    intro hu hk Ψ hΨ
    have hu' : ∀ μ, m ≤ μ → μ ≤ n → 0 < u μ ∧ M μ = d + u μ := fun μ h1 h2 => hu μ h1 (Nat.le_succ_of_le h2)
    have hk' : ∀ μ, m ≤ μ → μ ≤ n → B ≤ k μ * u μ := fun μ h1 h2 => hk μ h1 (Nat.le_succ_of_le h2)
    cases Nat.lt_or_ge (Ψ / B) (n + 1) with
    | inl hlt =>
      obtain ⟨j, hj, hl⟩ := ih hu' hk' Ψ (Nat.le_of_lt_succ hlt)
      exact ⟨j, Nat.le_trans hj (Nat.le_add_left _ _), hl⟩
    | inr hge =>
      have hlev : Ψ / B = n + 1 := Nat.le_antisymm hΨ hge
      cases Nat.lt_or_ge (n + 1) m with
      | inl hbelow => exact ⟨0, Nat.zero_le _, by rw [frun_zero, hlev]; exact hbelow⟩
      | inr hmle =>
        obtain ⟨hupos, hMu⟩ := hu (n + 1) hmle (Nat.le_refl _)
        have hpos : 0 < n + 1 := Nat.succ_pos n
        obtain ⟨j₁, hj₁, hl₁⟩ := falls_within hM hB hpos hMu hlev (by rw [← hlev]; exact lt_level_top hB Ψ) (hk (n + 1) hmle (Nat.le_refl _))
        obtain ⟨j₂, hj₂, hl₂⟩ := ih hu' hk' (frun M B d j₁ Ψ) (Nat.le_of_lt_succ hl₁)
        refine ⟨j₁ + j₂, ?_, by rw [frun_add]; exact hl₂⟩
        show j₁ + j₂ ≤ (if m ≤ n + 1 then k (n + 1) else 0) + descentBudget k m n
        rw [ite_eq_left hmle]
        exact Nat.add_le_add hj₁ hj₂

/-- A transfer count below level `m` lies below `B m`. -/
theorem lt_of_level_lt (hB : 0 < B) {Ψ m : Nat} (h : Ψ / B < m) : Ψ < B * m :=
  Nat.lt_of_lt_of_le (lt_level_top hB Ψ) (by rw [← Nat.mul_succ]; exact Nat.mul_le_mul_left B h)

/-- The band is kept for every later chronon. -/
theorem band_run (hM : ∀ μ, M μ ≤ B) {m u w : Nat} (hm : 0 < m) (hu : 0 < u)
    (hlo : M (m - 1) + w = d) (hhi : M m = d + u) {Ψ : Nat}
    (h1 : B * m ≤ Ψ + u) (h2 : Ψ + 1 ≤ B * m + w) :
    ∀ t, B * m ≤ frun M B d t Ψ + u ∧ frun M B d t Ψ + 1 ≤ B * m + w := by
  intro t
  induction t with
  | zero => exact ⟨h1, h2⟩
  | succ t ih =>
    rw [frun_succ']
    exact band_invariant hM hm hu hlo hhi ih.1 ih.2

/-- Along the forced relaxation from a level between the lock level `m` and `n`, the transfer count is at every chronon
either still at a level between `m` and `n` or inside the lock band: a step from a level above `m` lands at or above `m`
and no higher than before (the count falls), a step from level `m` lands in the band or stays at `m`, and the band is
invariant. Only the counts of the levels `m..n` enter. -/
theorem lock_invariant (hM : ∀ μ, M μ ≤ B) (hB : 0 < B) {m w n : Nat} (hm : 0 < m) (u : Nat → Nat)
    (hu : ∀ μ, m ≤ μ → μ ≤ n → 0 < u μ ∧ M μ = d + u μ) (hlo : M (m - 1) + w = d) (hmn : m ≤ n) (Ψ : Nat) :
    ∀ t, (m ≤ (frun M B d t Ψ) / B ∧ (frun M B d t Ψ) / B ≤ n) ∨
          (B * m ≤ frun M B d t Ψ + u m ∧ frun M B d t Ψ + 1 ≤ B * m + w) →
      (m ≤ (frun M B d (t + 1) Ψ) / B ∧ (frun M B d (t + 1) Ψ) / B ≤ n) ∨
          (B * m ≤ frun M B d (t + 1) Ψ + u m ∧ frun M B d (t + 1) Ψ + 1 ≤ B * m + w) := by
  intro t ht
  obtain ⟨hum, hMm⟩ := hu m (Nat.le_refl m) hmn
  rw [frun_succ']
  generalize frun M B d t Ψ = Φ at ht ⊢
  rcases ht with ⟨hlev, hlevn⟩ | hband
  · -- at a level ℓ with m ≤ ℓ ≤ n
    obtain ⟨hupos, hMu⟩ := hu (Φ / B) hlev hlevn
    have hge : B * (Φ / B) ≤ Φ := by
      have e := FRC.Nat.div_spec B hB Φ
      exact Nat.le_trans (Nat.le_add_right _ _) (Nat.le_of_eq e.symm)
    have hle : M (Φ / B) ≤ Φ + d :=
      Nat.le_trans (hM _) (Nat.le_trans (Nat.le_mul_of_pos_right B (Nat.lt_of_lt_of_le hm hlev)) (Nat.le_trans hge (Nat.le_add_right _ _)))
    have e : fstep M B d Φ + u (Φ / B) = Φ := fstep_of_lt hMu hle
    have hdown : fstep M B d Φ ≤ Φ := Nat.le_trans (Nat.le_add_right _ _) (Nat.le_of_eq e)
    have hlevn' : (fstep M B d Φ) / B ≤ n := Nat.le_trans (level_mono hB hdown) hlevn
    cases Nat.eq_or_lt_of_le hlev with
    | inr hgt =>
      -- strictly above m: the count stays at or above B m, so the level stays at or above m
      left
      have hΦm : B * m + B ≤ Φ := by
        rw [← Nat.mul_succ]; exact Nat.le_trans (Nat.mul_le_mul_left B hgt) hge
      have huB : u (Φ / B) ≤ B := Nat.le_trans (Nat.le_add_left _ d) (Nat.le_trans (Nat.le_of_eq hMu.symm) (hM _))
      have hnew : B * m ≤ fstep M B d Φ := by
        have : B * m + u (Φ / B) ≤ fstep M B d Φ + u (Φ / B) := by
          rw [e]; exact Nat.le_trans (Nat.add_le_add_left huB _) hΦm
        exact FRC.Nat.le_of_add_le_add_right this
      cases Nat.lt_or_ge ((fstep M B d Φ) / B) m with
      | inl hlt => exact absurd (lt_of_level_lt hB hlt) (Nat.not_lt_of_le hnew)
      | inr hge' => exact ⟨hge', hlevn'⟩
    | inl heq =>
      -- at the lock level: the count falls by u m; either it stays at level m or it lands in the band
      have heq' : Φ / B = m := heq.symm
      rw [heq'] at e
      cases Nat.lt_or_ge ((fstep M B d Φ) / B) m with
      | inr hge' => left; exact ⟨hge', hlevn'⟩
      | inl hlt =>
        right
        refine ⟨?_, ?_⟩
        · rw [e]; rw [heq'] at hge; exact hge
        · exact Nat.le_trans (lt_of_level_lt hB hlt) (Nat.le_add_right _ w)
  · right; exact band_invariant hM hm hum hlo hMm hband.1 hband.2

/-- 21:C28 — the forced relaxation locks. Let the lock level `m ≥ 1` have `M (m − 1) + w = d`, let every level `μ` from `m`
to `n` have its count above the forcing by `u μ ≥ 1` with `k μ · u μ ≥ B`, and let a link's transfer count sit at a level
between `m` and `n`. Then within `Σ_{μ = m}^{n} k μ` chronons the count enters the lock band `B m − u m ≤ Ψ ≤ B m + w − 1`
and stays in it at every later chronon: the registered mismatch is `m − 1` or `m` from then on, the discrete lock-in of the
locked state the cut form asserts, link by link. The counts beyond `n` (the far edge and the slip region, where the count
falls below the forcing) are not hypothesised. -/
theorem locks (hM : ∀ μ, M μ ≤ B) (hB : 0 < B) {m w : Nat} (hm : 0 < m) (u k : Nat → Nat) (n : Nat)
    (hu : ∀ μ, m ≤ μ → μ ≤ n → 0 < u μ ∧ M μ = d + u μ) (hk : ∀ μ, m ≤ μ → μ ≤ n → B ≤ k μ * u μ)
    (hlo : M (m - 1) + w = d) {Ψ : Nat} (hstart : m ≤ Ψ / B) (hΨ : Ψ / B ≤ n) :
    ∃ j, j ≤ descentBudget k m n ∧
      ∀ t, B * m ≤ frun M B d (j + t) Ψ + u m ∧ frun M B d (j + t) Ψ + 1 ≤ B * m + w := by
  have hmn : m ≤ n := Nat.le_trans hstart hΨ
  obtain ⟨hum, hMm⟩ := hu m (Nat.le_refl m) hmn
  obtain ⟨j, hj, hl⟩ := descends hM hB hm u k n hu hk Ψ hΨ
  have inv : ∀ t, (m ≤ (frun M B d t Ψ) / B ∧ (frun M B d t Ψ) / B ≤ n) ∨
      (B * m ≤ frun M B d t Ψ + u m ∧ frun M B d t Ψ + 1 ≤ B * m + w) := by
    intro t
    induction t with
    | zero => left; rw [frun_zero]; exact ⟨hstart, hΨ⟩
    | succ t ih => exact lock_invariant hM hB hm u hu hlo hmn Ψ t ih
  rcases inv j with ⟨hge, _⟩ | hband
  · exact absurd hl (Nat.not_lt_of_le hge)
  · refine ⟨j, hj, fun t => ?_⟩
    rw [frun_add]
    exact band_run hM hm hum hlo hMm hband.1 hband.2 t

/-! ## The band is a cyclic translation (the exact period and occupation) -/

/-- 21:C28 — on the lock band the forced step is the translation by `w` on the `u + w` values: with `x = Ψ + u − B m`
(`0 ≤ x < u + w`), the next count has `x' = (x + w) % (u + w)`. At level `m − 1` (`x < u`) the count rises by `w`; at
level `m` (`x ≥ u`) it falls by `u`, which is `x + w − (u + w)`. Hence every orbit on the band has period
`(u + w)/gcd(u, w)` and spends exactly `w/(u + w)` of its chronons at level `m`: the occupation is the fraction of the
`u + w` residues that lie in the upper block of `w`. -/
theorem band_translation (hM : ∀ μ, M μ ≤ B) {m u w : Nat} (hm : 0 < m) (hu : 0 < u)
    (hlo : M (m - 1) + w = d) (hhi : M m = d + u) {Ψ : Nat}
    (h1 : B * m ≤ Ψ + u) (h2 : Ψ + 1 ≤ B * m + w) :
    fstep M B d Ψ + u - B * m = (Ψ + u - B * m + w) % (u + w) := by
  have huB : u ≤ B := Nat.le_trans (Nat.le_add_left u d) (Nat.le_trans (Nat.le_of_eq hhi.symm) (hM m))
  have hwB : w ≤ B := Nat.le_trans (Nat.le_add_left w (M (m - 1)))
    (Nat.le_trans (Nat.le_of_eq hlo) (Nat.le_trans (Nat.le_add_right d u) (Nat.le_trans (Nat.le_of_eq hhi.symm) (hM m))))
  have hBm : B ≤ B * m := Nat.le_mul_of_pos_right B hm
  have hpos : 0 < u + w := Nat.lt_of_lt_of_le hu (Nat.le_add_right u w)
  cases Nat.lt_or_ge Ψ (B * m) with
  | inr hge =>
    -- level m: x ≥ u, the count falls by u, and x + w ≥ u + w
    have hlt : Ψ < B * m + B := Nat.lt_of_lt_of_le h2 (Nat.add_le_add_left hwB _)
    have hlev : Ψ / B = m := level_of_bounds hge hlt
    have hle : M (Ψ / B) ≤ Ψ + d := by
      rw [hlev]
      exact Nat.le_trans (hM m) (Nat.le_trans hBm (Nat.le_trans hge (Nat.le_add_right Ψ d)))
    have e : fstep M B d Ψ + u = Ψ := fstep_of_lt (by rw [hlev]; exact hhi) hle
    -- x = Ψ + u − B m = (Ψ − B m) + u, and x + w = (Ψ − B m) + (u + w)
    have ex : Ψ + u - B * m + w = (Ψ - B * m) + (u + w) := by
      have : Ψ + u - B * m = (Ψ - B * m) + u := by
        have e2 : Ψ + u = (Ψ - B * m) + u + B * m := by
          rw [Nat.add_right_comm, FRC.Nat.sub_add_cancel hge]
        rw [e2, FRC.Nat.add_sub_cancel]
      rw [this, Nat.add_assoc]
    have hsmall : Ψ - B * m < u + w := by
      have : Ψ - B * m + 1 ≤ w := by
        have h3 : Ψ - B * m + 1 + B * m ≤ w + B * m := by
          rw [Nat.add_right_comm, FRC.Nat.sub_add_cancel hge]; rw [Nat.add_comm w]; exact h2
        exact FRC.Nat.le_of_add_le_add_right h3
      exact Nat.lt_of_lt_of_le (Nat.lt_of_succ_le this) (Nat.le_add_left w u)
    rw [e, ex, FRC.Nat.mod_eq_sub_mod hpos (Nat.le_add_left _ _), FRC.Nat.add_sub_cancel, FRC.Nat.mod_eq_of_lt hsmall]
  | inl hlt =>
    -- level m − 1: x < u, the count rises by w, and x + w < u + w
    have hm1 : B * m = B * (m - 1) + B := by
      rw [← Nat.mul_succ, Nat.succ_eq_add_one, FRC.Nat.sub_add_cancel hm]
    have hlo' : B * (m - 1) ≤ Ψ := by
      have : B * (m - 1) + B ≤ Ψ + B := by
        rw [← hm1]; exact Nat.le_trans h1 (Nat.add_le_add_left huB Ψ)
      exact FRC.Nat.le_of_add_le_add_right this
    have hlev : Ψ / B = m - 1 := level_of_bounds hlo' (by rw [← hm1]; exact hlt)
    have e : fstep M B d Ψ = Ψ + w := fstep_of_gt (by rw [hlev]; exact hlo)
    have ex : fstep M B d Ψ + u - B * m = Ψ + u - B * m + w := by
      have e2 : Ψ + w + u = (Ψ + u - B * m + w) + B * m := by
        rw [Nat.add_right_comm (Ψ + u - B * m) w, FRC.Nat.sub_add_cancel h1, Nat.add_right_comm]
      rw [e, e2, FRC.Nat.add_sub_cancel]
    have hsmall : Ψ + u - B * m + w < u + w := by
      have : Ψ + u - B * m < u := by
        have h3 : Ψ + u - B * m + B * m < u + B * m := by
          rw [FRC.Nat.sub_add_cancel h1, Nat.add_comm u]; exact Nat.add_lt_add_right hlt u
        exact Nat.lt_of_add_lt_add_right h3
      exact Nat.add_lt_add_right this w
    rw [ex, FRC.Nat.mod_eq_of_lt hsmall]

/-- 21:C28 — `k` chronons on the band translate by `k w`: `x_k = (x + k w) % (u + w)`. -/
theorem band_iterate (hM : ∀ μ, M μ ≤ B) {m u w : Nat} (hm : 0 < m) (hu : 0 < u)
    (hlo : M (m - 1) + w = d) (hhi : M m = d + u) {Ψ : Nat}
    (h1 : B * m ≤ Ψ + u) (h2 : Ψ + 1 ≤ B * m + w) :
    ∀ k, frun M B d k Ψ + u - B * m = (Ψ + u - B * m + k * w) % (u + w) := by
  have hpos : 0 < u + w := Nat.lt_of_lt_of_le hu (Nat.le_add_right u w)
  intro k
  induction k with
  | zero =>
    rw [frun_zero, Nat.zero_mul, Nat.add_zero]
    have hsmall : Ψ + u - B * m < u + w := by
      have h3 : Ψ + u - B * m + B * m < u + w + B * m := by
        rw [FRC.Nat.sub_add_cancel h1]
        calc Ψ + u < B * m + w + u := Nat.add_lt_add_right (Nat.lt_of_succ_le h2) u
          _ = u + w + B * m := by rw [Nat.add_comm (B * m + w) u, ← Nat.add_assoc, Nat.add_comm (u + B * m) w,
                                      ← Nat.add_assoc, Nat.add_comm w u]
      exact Nat.lt_of_add_lt_add_right h3
    exact (FRC.Nat.mod_eq_of_lt hsmall).symm
  | succ k ih =>
    obtain ⟨g1, g2⟩ := band_run hM hm hu hlo hhi h1 h2 k
    rw [frun_succ', band_translation hM hm hu hlo hhi g1 g2, ih, FRC.Nat.mod_add_mod _ _ _ hpos, Nat.succ_mul,
      Nat.add_assoc]

/-- 21:C28 — the band's orbits return: whenever `u + w` divides `k w`, `k` chronons bring every band value back to itself
(the period `(u + w)/gcd(u, w)` is the least such `k`: `band_period` below). -/
theorem band_return (hM : ∀ μ, M μ ≤ B) {m u w : Nat} (hm : 0 < m) (hu : 0 < u)
    (hlo : M (m - 1) + w = d) (hhi : M m = d + u) {Ψ : Nat}
    (h1 : B * m ≤ Ψ + u) (h2 : Ψ + 1 ≤ B * m + w) {k : Nat} (hk : (k * w) % (u + w) = 0) :
    frun M B d k Ψ = Ψ := by
  have hpos : 0 < u + w := Nat.lt_of_lt_of_le hu (Nat.le_add_right u w)
  have hx := band_iterate hM hm hu hlo hhi h1 h2 k
  have hsmall : Ψ + u - B * m < u + w := by
    have h3 : Ψ + u - B * m + B * m < u + w + B * m := by
      rw [FRC.Nat.sub_add_cancel h1]
      calc Ψ + u < B * m + w + u := Nat.add_lt_add_right (Nat.lt_of_succ_le h2) u
        _ = u + w + B * m := by rw [Nat.add_comm (B * m + w) u, ← Nat.add_assoc, Nat.add_comm (u + B * m) w,
                                    ← Nat.add_assoc, Nat.add_comm w u]
    exact Nat.lt_of_add_lt_add_right h3
  rw [← FRC.Nat.add_mod_mod _ _ _ hpos, hk, Nat.add_zero, FRC.Nat.mod_eq_of_lt hsmall] at hx
  -- hx : frun k Ψ + u − B m = Ψ + u − B m, and both sides sit above B m − u
  obtain ⟨g1, _⟩ := band_run hM hm hu hlo hhi h1 h2 k
  have e1 : frun M B d k Ψ + u = Ψ + u := by
    calc frun M B d k Ψ + u = (frun M B d k Ψ + u - B * m) + B * m := (FRC.Nat.sub_add_cancel g1).symm
      _ = (Ψ + u - B * m) + B * m := by rw [hx]
      _ = Ψ + u := FRC.Nat.sub_add_cancel h1
  exact FRC.Nat.add_right_cancel e1

/-! ## The ascent -/

/-- 21:C28 — at a level `m` whose count falls short of the forcing by `w ≥ 1`, the transfer count leaves the level
upward within `k` chronons whenever `k · w ≥ B`: some chronon `j ≤ k` has its level above `m`. -/
theorem rises_within (hB : 0 < B) {m w : Nat} (hmw : M m + w = d) {Ψ : Nat}
    (hlev : Ψ / B = m) {k : Nat} (hk : B ≤ k * w) :
    ∃ j, j ≤ k ∧ m < (frun M B d j Ψ) / B := by
  have P : ∀ j, (frun M B d j Ψ = Ψ + j * w ∧ (frun M B d j Ψ) / B = m) ∨ ∃ i, i ≤ j ∧ m < (frun M B d i Ψ) / B := by
    intro j
    induction j with
    | zero => exact Or.inl ⟨by rw [frun_zero, Nat.zero_mul, Nat.add_zero], by rw [frun_zero]; exact hlev⟩
    | succ j ih =>
      rcases ih with ⟨hsum, hlj⟩ | ⟨i, hi, hlt⟩
      · have e : fstep M B d (frun M B d j Ψ) = frun M B d j Ψ + w := fstep_of_gt (by rw [hlj]; exact hmw)
        have hsum' : frun M B d (j + 1) Ψ = Ψ + (j + 1) * w := by
          rw [frun_succ', e, hsum, Nat.succ_mul, Nat.add_assoc]
        have hle' : frun M B d j Ψ ≤ frun M B d (j + 1) Ψ := by
          rw [frun_succ', e]; exact Nat.le_add_right _ _
        have hmono := level_mono hB hle'
        rw [hlj] at hmono
        rcases Nat.eq_or_lt_of_le hmono with heq | hlt
        · exact Or.inl ⟨hsum', heq.symm⟩
        · exact Or.inr ⟨j + 1, Nat.le_refl _, hlt⟩
      · exact Or.inr ⟨i, Nat.le_succ_of_le hi, hlt⟩
  rcases P k with ⟨hsum, hlk⟩ | ⟨i, hi, hlt⟩
  · exfalso
    -- at level m after k chronons, yet Ψ_k ≥ Ψ + B ≥ B (m + 1): impossible
    have hge : B * m ≤ Ψ := by
      have e := FRC.Nat.div_spec B hB Ψ
      rw [hlev] at e; rw [e]; exact Nat.le_add_right _ _
    have h1 : B * m + B ≤ frun M B d k Ψ := by
      rw [hsum]; exact Nat.add_le_add hge hk
    have h2 : m + 1 ≤ (frun M B d k Ψ) / B := by
      cases Nat.lt_or_ge ((frun M B d k Ψ) / B) (m + 1) with
      | inl hlt' => exact absurd (lt_of_level_lt hB hlt') (Nat.not_lt_of_le (by rw [Nat.mul_succ]; exact h1))
      | inr hge' => exact hge'
    rw [hlk] at h2; exact Nat.lt_irrefl m (Nat.lt_of_succ_le h2)
  · exact ⟨i, hi, hlt⟩

/-- The chronon budget of the ascent, `Σ_{μ = m − j}^{m − 1} k μ`. -/
def ascentBudget (k : Nat → Nat) (m : Nat) : Nat → Nat
  | 0 => 0
  | j + 1 => k (m - (j + 1)) + ascentBudget k m j

/-- 21:C28 — the ascent to the lock: when every level from `m − j` to `m − 1` has its count short of the forcing
(`M μ + w μ = d`, `w μ ≥ 1`) and `k μ · w μ ≥ B`, a link whose transfer count sits at a level at least `m − j` reaches a
level at least `m` within `Σ_{μ = m − j}^{m − 1} k μ` chronons. -/
theorem ascends (hB : 0 < B) {m : Nat} (w k : Nat → Nat)
    (hw : ∀ μ, μ < m → 0 < w μ ∧ M μ + w μ = d) (hk : ∀ μ, μ < m → B ≤ k μ * w μ) :
    ∀ j, j ≤ m → ∀ Ψ, m - j ≤ Ψ / B → ∃ t, t ≤ ascentBudget k m j ∧ m ≤ (frun M B d t Ψ) / B := by
  intro j
  induction j with
  | zero =>
    intro _ Ψ hΨ
    exact ⟨0, Nat.le_refl _, by rw [frun_zero]; exact hΨ⟩
  | succ j ih =>
    intro hj Ψ hΨ
    cases Nat.lt_or_ge (Ψ / B) (m - j) with
    | inr hge =>
      obtain ⟨t, ht, hl⟩ := ih (Nat.le_of_succ_le hj) Ψ hge
      exact ⟨t, Nat.le_trans ht (Nat.le_add_left _ _), hl⟩
    | inl hlt =>
      -- the level is exactly m − (j + 1)
      have hlev : Ψ / B = m - (j + 1) := by
        apply Nat.le_antisymm
        · have : Ψ / B + 1 ≤ m - j := hlt
          have e : m - j = m - (j + 1) + 1 := by
            rw [Nat.sub_succ]; exact (Nat.succ_pred_eq_of_pos (FRC.Nat.le_sub_of_add_le (by rw [Nat.add_comm]; exact hj))).symm
          rw [e] at this; exact Nat.le_of_succ_le_succ this
        · exact hΨ
      have hμ : m - (j + 1) < m := Nat.sub_lt (Nat.lt_of_lt_of_le (Nat.succ_pos j) hj) (Nat.succ_pos j)
      obtain ⟨hwpos, hMw⟩ := hw _ hμ
      obtain ⟨t₁, ht₁, hl₁⟩ := rises_within hB hMw hlev (hk _ hμ)
      obtain ⟨t₂, ht₂, hl₂⟩ := ih (Nat.le_of_succ_le hj) (frun M B d t₁ Ψ) (by
        have e : m - j = m - (j + 1) + 1 := by
          rw [Nat.sub_succ]; exact (Nat.succ_pred_eq_of_pos (FRC.Nat.le_sub_of_add_le (by rw [Nat.add_comm]; exact hj))).symm
        rw [e]; exact Nat.succ_le_of_lt hl₁)
      refine ⟨t₁ + t₂, ?_, by rw [frun_add]; exact hl₂⟩
      show t₁ + t₂ ≤ k (m - (j + 1)) + ascentBudget k m j
      exact Nat.add_le_add ht₁ ht₂

/-- Along the forced relaxation from a level below the lock level `m`, the transfer count is at every chronon either
still at a level below `m` or inside the lock band: a step from a level below `m − 1` lands below `m` (the count rises
by at most the window), a step from level `m − 1` stays there or lands in the band, and the band is invariant. -/
theorem lock_invariant_below (hM : ∀ μ, M μ ≤ B) (hB : 0 < B) {m u : Nat} (hm : 0 < m) (hu : 0 < u) (w : Nat → Nat)
    (hw : ∀ μ, μ < m → 0 < w μ ∧ M μ + w μ = d) (hhi : M m = d + u) (Ψ : Nat) :
    ∀ t, (frun M B d t Ψ) / B < m ∨ (B * m ≤ frun M B d t Ψ + u ∧ frun M B d t Ψ + 1 ≤ B * m + w (m - 1)) →
      (frun M B d (t + 1) Ψ) / B < m ∨ (B * m ≤ frun M B d (t + 1) Ψ + u ∧ frun M B d (t + 1) Ψ + 1 ≤ B * m + w (m - 1)) := by
  intro t ht
  have hm1 : m - 1 < m := Nat.sub_lt hm Nat.zero_lt_one
  obtain ⟨hwpos, hMw⟩ := hw (m - 1) hm1
  rw [frun_succ']
  generalize frun M B d t Ψ = Φ at ht ⊢
  rcases ht with hlev | hband
  · obtain ⟨hwl, hMl⟩ := hw (Φ / B) hlev
    have e : fstep M B d Φ = Φ + w (Φ / B) := fstep_of_gt hMl
    have hwB : w (Φ / B) ≤ B := Nat.le_trans (Nat.le_add_left _ (M (Φ / B))) (Nat.le_trans (Nat.le_of_eq hMl)
      (Nat.le_trans (Nat.le_add_right d u) (Nat.le_trans (Nat.le_of_eq hhi.symm) (hM m))))
    have htop : Φ < B * (Φ / B) + B := lt_level_top hB Φ
    cases Nat.lt_or_ge (Φ / B + 1) m with
    | inl hbelow =>
      -- a level below m − 1: the count rises by at most B, so the level stays below m
      left
      have : fstep M B d Φ < B * m := by
        rw [e]
        calc Φ + w (Φ / B) < B * (Φ / B) + B + w (Φ / B) := Nat.add_lt_add_right htop _
          _ ≤ B * (Φ / B) + B + B := Nat.add_le_add_left hwB _
          _ = B * (Φ / B + 1 + 1) := by rw [Nat.mul_succ, Nat.mul_succ]
          _ ≤ B * m := Nat.mul_le_mul_left B (Nat.succ_le_of_lt hbelow)
      exact level_lt_of_lt hB this
    | inr hge =>
      -- the level is m − 1: the count rises by w (m − 1); it stays at level m − 1 or lands in the band
      have hlev' : Φ / B = m - 1 := by
        apply Nat.le_antisymm (Nat.le_of_lt_succ (by rw [Nat.succ_eq_add_one, FRC.Nat.sub_add_cancel hm]; exact hlev))
        exact Nat.le_of_succ_le_succ (by rw [Nat.succ_eq_add_one, FRC.Nat.sub_add_cancel hm]; exact hge)
      rw [hlev'] at e
      cases Nat.lt_or_ge ((fstep M B d Φ) / B) m with
      | inl hlt => left; exact hlt
      | inr hge' =>
        right
        refine ⟨?_, ?_⟩
        · -- B m ≤ Φ' ≤ Φ' + u
          have : B * m ≤ fstep M B d Φ := by
            have e2 := FRC.Nat.div_spec B hB (fstep M B d Φ)
            exact Nat.le_trans (Nat.mul_le_mul_left B hge') (Nat.le_trans (Nat.le_add_right _ _) (Nat.le_of_eq e2.symm))
          exact Nat.le_trans this (Nat.le_add_right _ u)
        · -- Φ' = Φ + w (m − 1) ≤ B m − 1 + w (m − 1)
          rw [e, Nat.add_right_comm]
          have hΦ : Φ + 1 ≤ B * m := by
            have : Φ < B * (m - 1) + B := by rw [← hlev']; exact htop
            rw [← Nat.mul_succ, Nat.succ_eq_add_one, FRC.Nat.sub_add_cancel hm] at this
            exact this
          exact Nat.add_le_add_right hΦ _
  · right
    exact band_invariant hM hm hu (hw (m - 1) hm1).2 hhi hband.1 hband.2

/-- 21:C28 — the forced relaxation locks from below. Let the lock level `m ≥ 1` have `M m = d + u` (`u ≥ 1`) and every
level below `m` have its count short of the forcing by `w μ ≥ 1` with `k μ · w μ ≥ B`. A link whose transfer count sits
at a level at least `m − j` and below `m` enters the lock band `B m − u ≤ Ψ ≤ B m + w (m − 1) − 1` within
`Σ_{μ = m − j}^{m − 1} k μ` chronons and stays in it at every later chronon. -/
theorem locks_from_below (hM : ∀ μ, M μ ≤ B) (hB : 0 < B) {m u : Nat} (hm : 0 < m) (hu : 0 < u) (w k : Nat → Nat)
    (hw : ∀ μ, μ < m → 0 < w μ ∧ M μ + w μ = d) (hk : ∀ μ, μ < m → B ≤ k μ * w μ) (hhi : M m = d + u)
    {j : Nat} (hj : j ≤ m) {Ψ : Nat} (hstart : m - j ≤ Ψ / B) (hbelow : Ψ / B < m) :
    ∃ t, t ≤ ascentBudget k m j ∧
      ∀ s, B * m ≤ frun M B d (t + s) Ψ + u ∧ frun M B d (t + s) Ψ + 1 ≤ B * m + w (m - 1) := by
  obtain ⟨t, ht, hl⟩ := ascends hB w k hw hk j hj Ψ hstart
  have inv : ∀ s, (frun M B d s Ψ) / B < m ∨ (B * m ≤ frun M B d s Ψ + u ∧ frun M B d s Ψ + 1 ≤ B * m + w (m - 1)) := by
    intro s
    induction s with
    | zero => left; rw [frun_zero]; exact hbelow
    | succ s ih => exact lock_invariant_below hM hB hm hu w hw hhi Ψ s ih
  rcases inv t with hlt | hband
  · exact absurd hl (Nat.not_le_of_lt hlt)
  · refine ⟨t, ht, fun s => ?_⟩
    rw [frun_add]
    exact band_run hM hm hu (hw (m - 1) (Nat.sub_lt hm Nat.zero_lt_one)).2 hhi hband.1 hband.2 s

/-! ## The band's period and occupation (21:C28; the occupancy in the core, 22 November 2026) -/

/-- The chronons among the first `t` of the run from `Ψ` at which the transfer count is at least `B m`: on the band, the
chronons spent at level `m`, at each of which the count falls by `u`. -/
def upperCount (M : Nat → Nat) (B d m Ψ : Nat) : Nat → Nat
  | 0 => 0
  | t + 1 => upperCount M B d m Ψ t + (if B * m ≤ frun M B d t Ψ then 1 else 0)

theorem upperCount_zero : upperCount M B d m Ψ 0 = 0 := rfl

theorem upperCount_succ (t : Nat) :
    upperCount M B d m Ψ (t + 1) = upperCount M B d m Ψ t + (if B * m ≤ frun M B d t Ψ then 1 else 0) := rfl

theorem upperCount_le : ∀ t, upperCount M B d m Ψ t ≤ t
  | 0 => Nat.le_refl 0
  | t + 1 => by
    rw [upperCount_succ]
    cases Nat.decLe (B * m) (frun M B d t Ψ) with
    | isTrue h => rw [ite_eq_left h]; exact Nat.add_le_add (upperCount_le t) (Nat.le_refl 1)
    | isFalse h => rw [ite_eq_right h]; exact Nat.le_trans (upperCount_le t) (Nat.le_succ t)

/-- 21:C28 — the balance of the band: along a run on the band, the count rises by `w` at every chronon spent at level
`m − 1` and falls by `u` at every chronon spent at level `m`, so after `t` chronons with `N₂` of them at level `m`,
`Ψ_t + N₂ u = Ψ + (t − N₂) w`. -/
theorem band_balance (hM : ∀ μ, M μ ≤ B) {m u w : Nat} (hm : 0 < m) (hu : 0 < u)
    (hlo : M (m - 1) + w = d) (hhi : M m = d + u) {Ψ : Nat}
    (h1 : B * m ≤ Ψ + u) (h2 : Ψ + 1 ≤ B * m + w) :
    ∀ t, frun M B d t Ψ + upperCount M B d m Ψ t * u = Ψ + (t - upperCount M B d m Ψ t) * w := by
  have huB : u ≤ B := Nat.le_trans (Nat.le_add_left u d) (Nat.le_trans (Nat.le_of_eq hhi.symm) (hM m))
  have hwB : w ≤ B := Nat.le_trans (Nat.le_add_left w (M (m - 1)))
    (Nat.le_trans (Nat.le_of_eq hlo) (Nat.le_trans (Nat.le_add_right d u) (Nat.le_trans (Nat.le_of_eq hhi.symm) (hM m))))
  have hBm : B ≤ B * m := Nat.le_mul_of_pos_right B hm
  intro t
  induction t with
  | zero => rw [frun_zero, upperCount_zero, Nat.zero_mul, Nat.add_zero, Nat.sub_zero, Nat.zero_mul, Nat.add_zero]
  | succ t ih =>
    obtain ⟨g1, g2⟩ := band_run hM hm hu hlo hhi h1 h2 t
    have hN := upperCount_le (M := M) (B := B) (d := d) (m := m) (Ψ := Ψ) t
    rw [frun_succ', upperCount_succ]
    generalize hΦ : frun M B d t Ψ = Φ at ih g1 g2 ⊢
    generalize hN2 : upperCount M B d m Ψ t = N at ih hN ⊢
    cases Nat.decLe (B * m) Φ with
    | isTrue hge =>
      -- level m: the count falls by u, and N₂ gains one
      rw [ite_eq_left hge]
      have hlt : Φ < B * m + B := Nat.lt_of_lt_of_le g2 (Nat.add_le_add_left hwB _)
      have hlev : Φ / B = m := level_of_bounds hge hlt
      have hle : M (Φ / B) ≤ Φ + d := by
        rw [hlev]; exact Nat.le_trans (hM m) (Nat.le_trans hBm (Nat.le_trans hge (Nat.le_add_right Φ d)))
      have e : fstep M B d Φ + u = Φ := fstep_of_lt (by rw [hlev]; exact hhi) hle
      have hsub : t + 1 - (N + 1) = t - N := Nat.succ_sub_succ_eq_sub t N
      rw [hsub, Nat.add_mul, Nat.one_mul, ← Nat.add_assoc, Nat.add_right_comm, e]
      exact ih
    | isFalse hlt =>
      -- level m − 1: the count rises by w, and N₂ stays
      rw [ite_eq_right hlt, Nat.add_zero]
      have hlt' : Φ < B * m := Nat.lt_of_not_le hlt
      have hm1 : B * m = B * (m - 1) + B := by
        rw [← Nat.mul_succ, Nat.succ_eq_add_one, FRC.Nat.sub_add_cancel hm]
      have hlo' : B * (m - 1) ≤ Φ := by
        have : B * (m - 1) + B ≤ Φ + B := by
          rw [← hm1]; exact Nat.le_trans g1 (Nat.add_le_add_left huB Φ)
        exact FRC.Nat.le_of_add_le_add_right this
      have hlev : Φ / B = m - 1 := level_of_bounds hlo' (by rw [← hm1]; exact hlt')
      have e : fstep M B d Φ = Φ + w := fstep_of_gt (by rw [hlev]; exact hlo)
      have hsub : t + 1 - N = (t - N) + 1 := by
        have e := FRC.Nat.sub_add_cancel hN
        calc t + 1 - N = (t - N + N) + 1 - N := by rw [e]
          _ = (t - N + 1) + N - N := by rw [Nat.add_right_comm]
          _ = t - N + 1 := FRC.Nat.add_sub_cancel _ _
      rw [e, hsub, Nat.add_mul, Nat.one_mul, ← Nat.add_assoc, ← ih, Nat.add_right_comm]

/-- 21:C28 — the occupation over a return: whenever the run returns to its start after `p` chronons, the chronons spent
at level `m` number `N₂` with `N₂ (u + w) = p w`, exactly the fraction `w/(u + w)` of the period. -/
theorem band_occupancy (hM : ∀ μ, M μ ≤ B) {m u w : Nat} (hm : 0 < m) (hu : 0 < u)
    (hlo : M (m - 1) + w = d) (hhi : M m = d + u) {Ψ : Nat}
    (h1 : B * m ≤ Ψ + u) (h2 : Ψ + 1 ≤ B * m + w) {p : Nat} (hp : frun M B d p Ψ = Ψ) :
    upperCount M B d m Ψ p * (u + w) = p * w := by
  have hb := band_balance hM hm hu hlo hhi h1 h2 p
  have hN := upperCount_le (M := M) (B := B) (d := d) (m := m) (Ψ := Ψ) p
  rw [hp] at hb
  have e : upperCount M B d m Ψ p * u = (p - upperCount M B d m Ψ p) * w := FRC.Nat.add_left_cancel hb
  rw [Nat.mul_add, e, ← Nat.add_mul, FRC.Nat.sub_add_cancel hN]

/-- 21:C28 — the exact occupation of the period: with `u = g a`, `w = g b` (`g ≥ 1`), `a + b` chronons return every band
value to itself (`band_return`), and exactly `b` of them are spent at level `m`: the fraction `w/(u + w) = b/(a + b)`. -/
theorem band_occupancy_period (hM : ∀ μ, M μ ≤ B) {m g a b : Nat} (hm : 0 < m) (hg : 0 < g) (ha : 0 < a)
    (hlo : M (m - 1) + g * b = d) (hhi : M m = d + g * a) {Ψ : Nat}
    (h1 : B * m ≤ Ψ + g * a) (h2 : Ψ + 1 ≤ B * m + g * b) :
    frun M B d (a + b) Ψ = Ψ ∧ upperCount M B d m Ψ (a + b) = b := by
  have hu : 0 < g * a := Nat.mul_pos hg ha
  have hn : 0 < g * a + g * b := Nat.lt_of_lt_of_le hu (Nat.le_add_right _ _)
  have hret : frun M B d (a + b) Ψ = Ψ := by
    apply band_return hM hm hu hlo hhi h1 h2
    -- (a + b) (g b) = (g a + g b) b: a multiple of the band's length
    show ((a + b) * (g * b)) % (g * a + g * b) = 0
    have e : (a + b) * (g * b) = (g * a + g * b) * b := by
      rw [← Nat.mul_add, Nat.mul_comm (a + b), FRC.Nat.mul_assoc, Nat.mul_comm b (a + b), ← FRC.Nat.mul_assoc]
    rw [e, FRC.Nat.mul_mod_left' _ _ _ hn, FRC.Nat.mod_self _ hn, Nat.zero_mul, FRC.Nat.zero_mod]
  refine ⟨hret, ?_⟩
  have hocc := band_occupancy hM hm hu hlo hhi h1 h2 hret
  -- N₂ · g (a + b) = (a + b) · g b, hence N₂ = b
  have e1 : upperCount M B d m Ψ (a + b) * (g * (a + b)) = b * (g * (a + b)) := by
    rw [← Nat.mul_add] at hocc
    rw [hocc, Nat.mul_comm (a + b), ← FRC.Nat.mul_assoc, Nat.mul_comm g b, FRC.Nat.mul_assoc]
  have hpos : 0 < g * (a + b) := by rw [Nat.mul_add]; exact hn
  exact Nat.eq_of_mul_eq_mul_right hpos e1

/-- 21:C28 — the period is least when `a` and `b` are coprime, in the framework's invertible form (`s b ≡ 1 mod a + b`):
no chronon count `k` with `0 < k < a + b` returns a band value to itself, so `a + b = (u + w)/gcd(u, w)` is the period of
every orbit of the band and `b/(a + b)` its exact occupation of level `m`. -/
theorem band_period (hM : ∀ μ, M μ ≤ B) {m g a b s : Nat} (hm : 0 < m) (hg : 0 < g) (ha : 0 < a)
    (hs : (s * b) % (a + b) = 1)
    (hlo : M (m - 1) + g * b = d) (hhi : M m = d + g * a) {Ψ : Nat}
    (h1 : B * m ≤ Ψ + g * a) (h2 : Ψ + 1 ≤ B * m + g * b) {k : Nat} (hk0 : 0 < k) (hk : k < a + b) :
    frun M B d k Ψ ≠ Ψ := by
  intro hret
  have hu : 0 < g * a := Nat.mul_pos hg ha
  have hn : 0 < g * a + g * b := Nat.lt_of_lt_of_le hu (Nat.le_add_right _ _)
  have hab : 0 < a + b := Nat.lt_of_lt_of_le ha (Nat.le_add_right a b)
  -- the translation by k w returns x to itself: (x + k w) % n = x with x < n, so (k w) % n = 0
  have hx := band_iterate hM hm hu hlo hhi h1 h2 k
  rw [hret] at hx
  have hxlt : Ψ + g * a - B * m < g * a + g * b := by
    have h3 : Ψ + g * a - B * m + B * m < g * a + g * b + B * m := by
      rw [FRC.Nat.sub_add_cancel h1]
      calc Ψ + g * a < B * m + g * b + g * a := Nat.add_lt_add_right (Nat.lt_of_succ_le h2) _
        _ = g * a + g * b + B * m := by
          rw [Nat.add_comm (B * m + g * b) (g * a), ← Nat.add_assoc, Nat.add_comm (g * a + B * m) (g * b),
              ← Nat.add_assoc, Nat.add_comm (g * b) (g * a)]
    exact Nat.lt_of_add_lt_add_right h3
  have hkw : (k * (g * b)) % (g * a + g * b) = 0 := by
    -- from (x + r) % n = x with x < n: r % n = 0
    have h4 : (Ψ + g * a - B * m + (k * (g * b)) % (g * a + g * b)) % (g * a + g * b) = Ψ + g * a - B * m := by
      rw [FRC.Nat.add_mod_mod _ _ _ hn]; exact hx.symm
    have hr : (k * (g * b)) % (g * a + g * b) < g * a + g * b := FRC.Nat.mod_lt' _ hn
    generalize hR : (k * (g * b)) % (g * a + g * b) = r at h4 hr
    generalize hX : Ψ + g * a - B * m = x at h4 hxlt
    cases Nat.lt_or_ge (x + r) (g * a + g * b) with
    | inl hlt =>
      rw [FRC.Nat.mod_eq_of_lt hlt] at h4
      exact FRC.Nat.add_left_cancel (by rw [Nat.add_zero]; exact h4)
    | inr hge =>
      rw [FRC.Nat.mod_eq_sub_mod hn hge] at h4
      have hsm : x + r - (g * a + g * b) < g * a + g * b :=
        FRC.Nat.sub_lt_of_lt_add (Nat.lt_of_lt_of_le (Nat.add_lt_add hxlt hr) (Nat.le_refl _)) hge
      rw [FRC.Nat.mod_eq_of_lt hsm] at h4
      -- x + r − n = x forces r = n, against r < n
      have : x + r = x + (g * a + g * b) := by
        calc x + r = (x + r - (g * a + g * b)) + (g * a + g * b) := (FRC.Nat.sub_add_cancel hge).symm
          _ = x + (g * a + g * b) := by rw [h4]
      exact absurd (FRC.Nat.add_left_cancel this) (Nat.ne_of_lt hr)
  -- (k b) % (a + b) = 0, by cancelling g
  have hkb : (k * b) % (a + b) = 0 := by
    obtain ⟨q, hq⟩ := FRC.Nat.mod_spec (g * a + g * b) hn (k * (g * b))
    rw [hkw, Nat.add_zero] at hq
    -- k (g b) = (g a + g b) q, i.e. g (k b) = g ((a + b) q)
    have e : g * (k * b) = g * ((a + b) * q) := by
      rw [← Nat.mul_add] at hq
      rw [FRC.Nat.mul_left_comm g k b, hq, FRC.Nat.mul_assoc]
    have e' : k * b = (a + b) * q := Nat.eq_of_mul_eq_mul_left hg e
    rw [e', FRC.Nat.mul_mod_left' _ _ _ hab, FRC.Nat.mod_self _ hab, Nat.zero_mul, FRC.Nat.zero_mod]
  -- k ≡ k s b ≡ 0 (mod a + b), so (a + b) ∣ k, against 0 < k < a + b
  have hk1 : k % (a + b) = 0 := by
    have e1 : (k * (s * b)) % (a + b) = (k * 1) % (a + b) := by
      rw [← FRC.Nat.mul_mod_mod k (s * b) _ hab, hs]
    have e2 : (k * (s * b)) % (a + b) = 0 := by
      rw [← FRC.Nat.mul_assoc, Nat.mul_comm k s, FRC.Nat.mul_assoc, ← FRC.Nat.mul_mod_mod s (k * b) _ hab, hkb,
        Nat.mul_zero, FRC.Nat.zero_mod]
    rw [Nat.mul_one] at e1
    exact e1.symm.trans e2
  rw [FRC.Nat.mod_eq_of_lt hk] at hk1
  exact absurd hk1 (Nat.ne_of_gt hk0)

end FRC.Relaxation
