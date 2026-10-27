import FrcCore.Nat

/-!
# FrcCore.Theme.Window — the readout window: the pulse accumulator and the framed readout (the relaxation theme; 27 October 2026)

The registered dynamics of one link of 21-gravity, stated on counts alone (reports/relaxation-window-20261027.md):
the Subject's chart is the link's phase reference; each chronon the link's current at the registered mismatch `μ` is
read through the window as a count `M μ` of transfers per window `B`; an accumulator adds `M μ` per chronon and the
chart moves one quantum toward alignment each time it passes `B` (the pulse law of `FRC.Relaxation.pulse_law` with the
rate of the present mismatch). Nothing here uses the shell: the theorems are `Nat` arithmetic, with no axioms.

* `step`, `run` — the re-registration rule as a function of the state (the mismatch in quanta, the accumulator below the
  window); `run_add` composes runs.
* `step_mu_le`, `step_mu_ge` — the registered mismatch never grows and moves by at most one quantum per chronon;
  `run_acc_lt` — the accumulator stays below the window when every count is at most the window.
* `run_aligned` — alignment is a fixed point: with `M 0 = 0` the link stays aligned.
* `drops_within` — at a mismatch `μ ≥ 1` the chart moves within `k` chronons whenever `k · M μ ≥ B`: the dwell at a
  level is bounded by the window over the count (`⌈B / M μ⌉`, stated without division).
* `terminates` — from any mismatch `μ₀` the link reaches exact alignment within `Σ_{μ = 1}^{μ₀} k μ` chronons, `k μ` any
  bound with `k μ · M μ ≥ B`. The chart's Kuramoto flow has an exponential tail; the registered relaxation ends.
* `IsSqrt`, `isSqrt_unique`, `isSqrt_nest` — the grid bound of the framed readout map (22-quantum, Definition readout:
  `s_n = ⌊√(m g^{2n})⌋` as the two-sided bound `s² ≤ m g^{2n} < (s + 1)²`) and the nesting of the readouts across
  scales; `readoutNum`, `readoutDen`, `count` — the readout of a weight `(u + v√m)/b` at scale `n` as a framed rational,
  and the registered count of `B` runs over the two outcomes by the largest-remainder rule (the residual unit goes to the
  event when its remainder is at least the other's: the half-up rounding of `B R`).
* `readout_c8`, `readout_c12` — the window counts of the link's current on `C_8` and `C_12` at 22-quantum's worked scale
  (`g = 3`, `n = 4`, `B = 81`): 57, 81 and 41, 70, 81, decided by the kernel; `M/B` is the readout of `sin(2πμ/N)`.
* `quiet_run`, `fires_at`, `carry_lt` — the dwell at a level: while the accumulator stays below the window the chart
  does not move and the accumulator is `acc + k · M μ`; the chart moves at exactly the first `k + 1` with
  `B ≤ acc + (k + 1) · M μ`; the carry after a pulse is below the count.
* `dwell_two_values` — with carry `c < M` the dwell `d + 1` is `⌊B/M⌋` or `⌊B/M⌋ + 1`: the registered rate `M/B` and
  the dwell per quantum are the two faces of one window count (21:C7).
* `equivalence_cancel` — `(m g)/m = g`: the cardinality cancels inside the two-shift law (21:C4).

The quotient face of the division algorithm, `x = p · (x/p) + x % p` (`FRC.Nat.div_spec`) and its uniqueness
(`FRC.Nat.div_unique`), is derived first from the definition of `Nat.div` in `Init.Prelude` (a fuel recursion, as
`Nat.modCore` in `FrcCore.Nat`), since Lean's `Nat.mul_div_cancel_left` and `Nat.div_add_mod` carry `propext`.
-/

namespace FRC.Nat

/-! ## The division algorithm, the quotient face: from the definition of `Nat.div` -/

/-- The fuel of `Nat.div.go` does not matter once it exceeds the dividend. -/
theorem div_go_fuel {y : Nat} (hy : 0 < y) : ∀ (f1 f2 x : Nat) (h1 : x < f1) (h2 : x < f2),
    Nat.div.go y hy f1 x h1 = Nat.div.go y hy f2 x h2 := by
  intro f1
  induction f1 with
  | zero => intro f2 x h1; exact absurd h1 (Nat.not_lt_zero x)
  | succ f1 ih =>
    intro f2 x h1 h2
    cases f2 with
    | zero => exact absurd h2 (Nat.not_lt_zero x)
    | succ f2 =>
      show (if h : y ≤ x then Nat.div.go y hy f1 (x - y) _ + 1 else 0)
          = (if h : y ≤ x then Nat.div.go y hy f2 (x - y) _ + 1 else 0)
      exact match Nat.decLe y x with
        | .isTrue h => by rw [dite_eq_left h, dite_eq_left h, ih f2 (x - y) _ _]
        | .isFalse h => by rw [dite_eq_right h, dite_eq_right h]

/-- The recursion of `Nat.div`: `x / y = (x − y) / y + 1` for `y ≤ x`, else `0`. -/
theorem div_eq' (x y : Nat) (hy : 0 < y) : x / y = if y ≤ x then (x - y) / y + 1 else 0 := by
  show Nat.div x y = if y ≤ x then Nat.div (x - y) y + 1 else 0
  unfold Nat.div
  rw [dite_eq_left hy]
  show (if h : y ≤ x then Nat.div.go y hy x (x - y) _ + 1 else 0) = _
  exact match Nat.decLe y x with
    | .isTrue h => by
        rw [dite_eq_left h, ite_eq_left h, dite_eq_left hy, div_go_fuel hy x (x - y + 1) (x - y) _ _]
    | .isFalse h => by rw [dite_eq_right h, ite_eq_right h]

/-- The division algorithm, quotient face: `x = p · (x / p) + x % p`. -/
theorem div_spec (p : Nat) (hp : 0 < p) : ∀ x : Nat, x = p * (x / p) + x % p := by
  intro x
  induction x using Nat.strongRecOn with
  | _ x ih =>
    exact match Nat.decLe p x with
      | .isTrue h => by
          have ih' := ih (x - p) (Nat.sub_lt (Nat.lt_of_lt_of_le hp h) hp)
          rw [div_eq' x p hp, ite_eq_left h, mod_eq_sub_mod hp h, Nat.mul_succ, Nat.add_assoc, Nat.add_comm p,
            ← Nat.add_assoc, ← ih', sub_add_cancel h]
      | .isFalse h => by
          rw [div_eq' x p hp, ite_eq_right h, Nat.mul_zero, Nat.zero_add, mod_eq_of_lt (Nat.lt_of_not_le h)]

/-- The quotient is determined: if `x = p·q + r` with `r < p`, then `x / p = q`. -/
theorem div_unique {p x q r : Nat} (hr : r < p) (h : x = p * q + r) : x / p = q :=
  quot_unique (Nat.mod_lt x (pos_of_lt hr)) hr (by rw [← div_spec p (pos_of_lt hr) x]; exact h)

end FRC.Nat

namespace FRC.Relaxation

/-! ## The pulse accumulator (21:C28) -/

/-- The registered state of a link: the mismatch in quanta of the phase cycle and the accumulator, below the window. -/
structure State where
  mu : Nat
  acc : Nat

/-- One chronon of the re-registration rule: the accumulator gains the window count `M μ` of the present mismatch; when
it reaches the window `B` one pulse fires — the chart moves one quantum toward alignment and the accumulator keeps the
remainder. -/
def step (M : Nat → Nat) (B : Nat) (s : State) : State :=
  if B ≤ s.acc + M s.mu then ⟨s.mu - 1, s.acc + M s.mu - B⟩ else ⟨s.mu, s.acc + M s.mu⟩

/-- `t` chronons of the rule. -/
def run (M : Nat → Nat) (B : Nat) : Nat → State → State
  | 0, s => s
  | t + 1, s => run M B t (step M B s)

variable {M : Nat → Nat} {B : Nat}

theorem run_zero (s : State) : run M B 0 s = s := rfl

theorem run_succ (t : Nat) (s : State) : run M B (t + 1) s = run M B t (step M B s) := rfl

/-- Runs compose: `a + b` chronons are `a` chronons and then `b`. -/
theorem run_add (a b : Nat) (s : State) : run M B (a + b) s = run M B b (run M B a s) := by
  induction a generalizing s with
  | zero => rw [Nat.zero_add]; rfl
  | succ a ih =>
    rw [Nat.succ_add, run_succ, run_succ, ih]

/-- The last chronon of a run. -/
theorem run_succ' (t : Nat) (s : State) : run M B (t + 1) s = step M B (run M B t s) := by
  induction t generalizing s with
  | zero => rfl
  | succ t ih => rw [run_succ, ih]; rfl

/-- The fired step. -/
theorem step_fire {s : State} (h : B ≤ s.acc + M s.mu) : step M B s = ⟨s.mu - 1, s.acc + M s.mu - B⟩ := by
  unfold step; rw [ite_eq_left h]

/-- The quiet step. -/
theorem step_quiet {s : State} (h : ¬ B ≤ s.acc + M s.mu) : step M B s = ⟨s.mu, s.acc + M s.mu⟩ := by
  unfold step; rw [ite_eq_right h]

/-- 21:C28 — the registered mismatch never grows. -/
theorem step_mu_le (s : State) : (step M B s).mu ≤ s.mu := by
  cases Nat.lt_or_ge (s.acc + M s.mu) B with
  | inl h => rw [step_quiet (Nat.not_le_of_lt h)]; exact Nat.le_refl _
  | inr h => rw [step_fire h]; exact Nat.sub_le _ _

/-- 21:C28 — the registered mismatch moves by at most one quantum per chronon. -/
theorem step_mu_ge (s : State) : s.mu ≤ (step M B s).mu + 1 := by
  cases Nat.lt_or_ge (s.acc + M s.mu) B with
  | inl h => rw [step_quiet (Nat.not_le_of_lt h)]; exact Nat.le_add_right _ _
  | inr h =>
    rw [step_fire h]
    show s.mu ≤ s.mu - 1 + 1
    cases s.mu with
    | zero => exact Nat.zero_le _
    | succ m => exact Nat.le_refl _

/-- The accumulator stays below the window when every count is at most the window. -/
theorem step_acc_lt (hM : ∀ μ, M μ ≤ B) {s : State} (hs : s.acc < B) : (step M B s).acc < B := by
  cases Nat.lt_or_ge (s.acc + M s.mu) B with
  | inl h => rw [step_quiet (Nat.not_le_of_lt h)]; exact h
  | inr h =>
    rw [step_fire h]
    show s.acc + M s.mu - B < B
    exact FRC.Nat.sub_lt_of_lt_add (Nat.add_lt_add_of_lt_of_le hs (hM _)) h

theorem run_acc_lt (hM : ∀ μ, M μ ≤ B) (t : Nat) {s : State} (hs : s.acc < B) : (run M B t s).acc < B := by
  induction t generalizing s with
  | zero => exact hs
  | succ t ih => rw [run_succ]; exact ih (step_acc_lt hM hs)

theorem run_mu_le (t : Nat) (s : State) : (run M B t s).mu ≤ s.mu := by
  induction t generalizing s with
  | zero => exact Nat.le_refl _
  | succ t ih => rw [run_succ]; exact Nat.le_trans (ih _) (step_mu_le s)

/-- 21:C28 — alignment is a fixed point: with no current at alignment (`M 0 = 0`) the link stays aligned. -/
theorem step_aligned (h0 : M 0 = 0) {s : State} (hs : s.acc < B) (hmu : s.mu = 0) :
    (step M B s).mu = 0 ∧ (step M B s).acc = s.acc := by
  have h : ¬ B ≤ s.acc + M s.mu := by rw [hmu, h0, Nat.add_zero]; exact Nat.not_le_of_lt hs
  rw [step_quiet h]; exact ⟨hmu, by show s.acc + M s.mu = s.acc; rw [hmu, h0, Nat.add_zero]⟩

/-- 21:C28 — the aligned link stays aligned through every run. -/
theorem run_aligned (h0 : M 0 = 0) (t : Nat) {s : State} (hs : s.acc < B) (hmu : s.mu = 0) :
    (run M B t s).mu = 0 := by
  induction t generalizing s with
  | zero => exact hmu
  | succ t ih =>
    rw [run_succ]
    rcases step_aligned h0 hs hmu with ⟨h1, h2⟩
    exact ih (by rw [h2]; exact hs) h1

/-- While no pulse has fired the accumulator is `acc + j · M μ`: from a mismatch `μ ≥ 1`, after `j` chronons either
the mismatch has dropped or the state is `⟨μ, acc + j · M μ⟩`. -/
theorem run_dichotomy (j : Nat) {s : State} (hpos : 0 < s.mu) :
    (run M B j s).mu < s.mu ∨ ((run M B j s).mu = s.mu ∧ (run M B j s).acc = s.acc + j * M s.mu) := by
  induction j with
  | zero => exact Or.inr ⟨rfl, by show s.acc = s.acc + 0 * M s.mu; rw [Nat.zero_mul, Nat.add_zero]⟩
  | succ j ih =>
    have e : run M B (j + 1) s = step M B (run M B j s) := run_succ' j s
    rcases ih with h | ⟨hmu, hacc⟩
    · exact Or.inl (Nat.lt_of_le_of_lt (by rw [e]; exact step_mu_le _) h)
    · rw [e]
      cases Nat.lt_or_ge ((run M B j s).acc + M (run M B j s).mu) B with
      | inl hq =>
        rw [step_quiet (Nat.not_le_of_lt hq)]
        exact Or.inr ⟨hmu, by show (run M B j s).acc + M (run M B j s).mu = _; rw [hacc, hmu, Nat.succ_mul, Nat.add_assoc]⟩
      | inr hf =>
        rw [step_fire hf]
        show (run M B j s).mu - 1 < s.mu ∨ _
        rw [hmu]
        exact Or.inl (Nat.sub_lt hpos Nat.zero_lt_one)

/-- 21:C28 — the dwell at a mismatch `μ ≥ 1` is bounded by the window over the count: the chart moves within `k`
chronons whenever `k · M μ ≥ B`. -/
theorem drops_within (hM : ∀ μ, M μ ≤ B) {s : State} (hpos : 0 < s.mu) (hs : s.acc < B) {k : Nat}
    (hk : B ≤ k * M s.mu) : (run M B k s).mu < s.mu := by
  rcases run_dichotomy k hpos with h | ⟨_, hacc⟩
  · exact h
  · exact absurd (run_acc_lt hM k hs) (by
      rw [hacc]; exact Nat.not_lt_of_le (Nat.le_trans hk (Nat.le_add_left _ _)))

/-- The chronon budget `Σ_{μ = 1}^{n} k μ`. -/
def budget (k : Nat → Nat) : Nat → Nat
  | 0 => 0
  | n + 1 => k (n + 1) + budget k n

/-- 21:C28 — the registered relaxation terminates: with no current at alignment and a count of at least one quantum per
window at every other mismatch (`k μ · M μ ≥ B` for a bound `k`), a link at mismatch at most `n` reaches exact alignment
within `budget k n` chronons and stays there. -/
theorem terminates (hM : ∀ μ, M μ ≤ B) (h0 : M 0 = 0) (k : Nat → Nat) (hk : ∀ μ, 0 < μ → B ≤ k μ * M μ) :
    ∀ n, ∀ s : State, s.mu ≤ n → s.acc < B → (run M B (budget k n) s).mu = 0 := by
  intro n
  induction n with
  | zero =>
    intro s hn hs
    exact run_aligned h0 _ hs (Nat.le_antisymm hn (Nat.zero_le _))
  | succ n ih =>
    intro s hn hs
    show (run M B (k (n + 1) + budget k n) s).mu = 0
    rw [run_add]
    have hacc : (run M B (k (n + 1)) s).acc < B := run_acc_lt hM _ hs
    apply ih _ _ hacc
    cases Nat.lt_or_ge s.mu (n + 1) with
    | inl hlt => exact Nat.le_trans (run_mu_le _ _) (Nat.le_of_lt_succ hlt)
    | inr hge =>
      have hmu : s.mu = n + 1 := Nat.le_antisymm hn hge
      have hpos : 0 < s.mu := by rw [hmu]; exact Nat.succ_pos n
      have hd := drops_within hM hpos hs (k := k (n + 1)) (by rw [← hmu]; exact hk _ hpos)
      rw [hmu] at hd
      exact Nat.le_of_lt_succ hd

/-- 21:C28 — the basin form of `terminates`: the count hypothesis is needed only at the mismatches at or below the start,
since the mismatch never grows. A link starting below the antipode of `C_8` or `C_12`, where the exact window count
vanishes, is covered: it never reaches the antipode. -/
theorem terminates_basin (hM : ∀ μ, M μ ≤ B) (h0 : M 0 = 0) (k : Nat → Nat) :
    ∀ n, (∀ μ, 0 < μ → μ ≤ n → B ≤ k μ * M μ) →
      ∀ s : State, s.mu ≤ n → s.acc < B → (run M B (budget k n) s).mu = 0 := by
  intro n
  induction n with
  | zero =>
    intro _ s hn hs
    exact run_aligned h0 _ hs (Nat.le_antisymm hn (Nat.zero_le _))
  | succ n ih =>
    intro hk s hn hs
    show (run M B (k (n + 1) + budget k n) s).mu = 0
    rw [run_add]
    have hacc : (run M B (k (n + 1)) s).acc < B := run_acc_lt hM _ hs
    apply ih (fun μ hμ hle => hk μ hμ (Nat.le_succ_of_le hle)) _ _ hacc
    cases Nat.lt_or_ge s.mu (n + 1) with
    | inl hlt => exact Nat.le_trans (run_mu_le _ _) (Nat.le_of_lt_succ hlt)
    | inr hge =>
      have hmu : s.mu = n + 1 := Nat.le_antisymm hn hge
      have hpos : 0 < s.mu := by rw [hmu]; exact Nat.succ_pos n
      have hd := drops_within hM hpos hs (k := k (n + 1)) (by rw [← hmu]; exact hk _ hpos hn)
      rw [hmu] at hd
      exact Nat.le_of_lt_succ hd

/-! ## The framed readout on a real-quadratic stratum (22-quantum, Definition readout; 21:C29) -/

/-- The grid bound of the readout: `s` is the integer square root of `x`, `s² ≤ x < (s + 1)²`. -/
def IsSqrt (x s : Nat) : Prop := s * s ≤ x ∧ x < (s + 1) * (s + 1)

instance (x s : Nat) : Decidable (IsSqrt x s) := inferInstanceAs (Decidable (_ ∧ _))

/-- `a² < b² ⇒ a < b`, without the prelude's classical lemma. -/
theorem lt_of_sq_lt_sq {a b : Nat} (h : a * a < b * b) : a < b := by
  cases Nat.lt_or_ge a b with
  | inl hab => exact hab
  | inr hba => exact absurd (Nat.lt_of_lt_of_le h (Nat.mul_le_mul hba hba)) (Nat.lt_irrefl _)

/-- 21:C29 — the integer square root is unique: the readout's grid point is determined by its bound. -/
theorem isSqrt_unique {x s s' : Nat} (h : IsSqrt x s) (h' : IsSqrt x s') : s = s' :=
  Nat.le_antisymm (Nat.le_of_lt_succ (lt_of_sq_lt_sq (Nat.lt_of_le_of_lt h.1 h'.2)))
    (Nat.le_of_lt_succ (lt_of_sq_lt_sq (Nat.lt_of_le_of_lt h'.1 h.2)))

/-- 21:C29 — the readouts nest across scales (22-quantum's grid bound at every scale): if `s` is the root of `x` and
`s'` the root of `x · c²`, then `s c ≤ s' < (s + 1) c`. -/
theorem isSqrt_nest {x s s' c : Nat} (hc : 0 < c) (h : IsSqrt x s) (h' : IsSqrt (x * (c * c)) s') :
    s * c ≤ s' ∧ s' < (s + 1) * c := by
  have e1 : s * c * (s * c) = s * s * (c * c) := by
    rw [Nat.mul_assoc, Nat.mul_left_comm c, ← Nat.mul_assoc]
  have e2 : (s + 1) * c * ((s + 1) * c) = (s + 1) * (s + 1) * (c * c) := by
    rw [Nat.mul_assoc, Nat.mul_left_comm c, ← Nat.mul_assoc]
  constructor
  · -- `(s c)² = s² c² ≤ x c² < (s' + 1)²`
    apply Nat.le_of_lt_succ
    apply lt_of_sq_lt_sq
    rw [e1]
    exact Nat.lt_of_le_of_lt (Nat.mul_le_mul_right _ h.1) h'.2
  · -- `s'² ≤ x c² < (s + 1)² c² = ((s + 1) c)²`
    apply lt_of_sq_lt_sq
    rw [e2]
    exact Nat.lt_of_le_of_lt h'.1 (Nat.mul_lt_mul_of_pos_right h.2 (Nat.mul_pos hc hc))

/-- The readout of the weight `(u + v√m)/b` at scale `n`: the numerator `u gⁿ + v s` with `s` the root of `m g^{2n}`. -/
def readoutNum (u v s g n : Nat) : Nat := u * g ^ n + v * s

/-- Its denominator `b gⁿ`. -/
def readoutDen (b g n : Nat) : Nat := b * g ^ n

/-- The registered count of `B` runs over the two outcomes (the event, its absence) by the largest-remainder rule: the
provisional `⌊B R⌋`, and the residual unit when the event's remainder is at least the other's — the half-up rounding of
`B R = B num/den`. -/
def count (B num den : Nat) : Nat := (2 * B * num + den) / (2 * den)

/-- 21:C29 — `C_8` at 22-quantum's worked scale (`g = 3`, `n = 4`, `B = 81`): the root `s_4 = 114` of `2 · 3^8`, and the
window counts of the current `|sin(2πμ/8)|` — `√2/2 = (0 + 1·√2)/2` at `μ = 1, 3` reads `114/162`, count 57; `1` at `μ = 2`
reads `81/81`, count 81. -/
theorem readout_c8 :
    IsSqrt (2 * 3 ^ 8) 114 ∧ readoutNum 0 1 114 3 4 = 114 ∧ readoutDen 2 3 4 = 162 ∧
    count 81 (readoutNum 0 1 114 3 4) (readoutDen 2 3 4) = 57 ∧
    count 81 (readoutNum 1 0 114 3 4) (readoutDen 1 3 4) = 81 := by
  decide

/-- 21:C29 — `C_12` at the same scale: the root `s_4 = 140` of `3 · 3^8`, and the counts of `|sin(2πμ/12)|` — `1/2` at
`μ = 1, 5` reads `81/162`, count 41 (the half unit to the event); `√3/2 = (0 + 1·√3)/2` at `μ = 2, 4` reads `140/162`, count
70; `1` at `μ = 3`, count 81. -/
theorem readout_c12 :
    IsSqrt (3 * 3 ^ 8) 140 ∧
    count 81 (readoutNum 1 0 140 3 4) (readoutDen 2 3 4) = 41 ∧
    count 81 (readoutNum 0 1 140 3 4) (readoutDen 2 3 4) = 70 ∧
    count 81 (readoutNum 1 0 140 3 4) (readoutDen 1 3 4) = 81 := by
  decide

/-! ## The dwell at a level: the two faces of one window count (21:C7) -/

/-- 21:C7 — while the accumulator stays below the window the chart does not move and the accumulator grows by `M μ` per
chronon: after `k` chronons with `acc + k · M μ < B` the state is `⟨μ, acc + k · M μ⟩`. -/
theorem quiet_run (s : State) : ∀ k, s.acc + k * M s.mu < B → run M B k s = ⟨s.mu, s.acc + k * M s.mu⟩
  | 0, _ => by show s = ⟨s.mu, s.acc + 0 * M s.mu⟩; rw [Nat.zero_mul, Nat.add_zero]
  | k + 1, h => by
    have hk : s.acc + k * M s.mu < B :=
      Nat.lt_of_le_of_lt (Nat.add_le_add_left (Nat.mul_le_mul_right _ (Nat.le_succ k)) _) h
    have hq : ¬ B ≤ s.acc + k * M s.mu + M s.mu := by
      rw [Nat.add_assoc, ← Nat.succ_mul]; exact Nat.not_le_of_lt h
    rw [run_succ', quiet_run s k hk, step_quiet hq]
    show (⟨s.mu, s.acc + k * M s.mu + M s.mu⟩ : State) = ⟨s.mu, s.acc + (k + 1) * M s.mu⟩
    rw [Nat.succ_mul, Nat.add_assoc]

/-- The dwell at a level is the least `k + 1` with `B ≤ acc + (k + 1) · M μ`: the chart moves at exactly that chronon,
to `μ − 1`, and the accumulator keeps the carry `acc + (k + 1) · M μ − B`. -/
theorem fires_at (s : State) (k : Nat) (hq : s.acc + k * M s.mu < B) (hf : B ≤ s.acc + (k + 1) * M s.mu) :
    (run M B (k + 1) s).mu = s.mu - 1 ∧ (run M B (k + 1) s).acc = s.acc + (k + 1) * M s.mu - B := by
  have hf' : B ≤ s.acc + k * M s.mu + M s.mu := by rw [Nat.add_assoc, ← Nat.succ_mul]; exact hf
  rw [run_succ', quiet_run s k hq, step_fire hf']
  exact ⟨rfl, by show s.acc + k * M s.mu + M s.mu - B = _; rw [Nat.add_assoc, ← Nat.succ_mul]⟩

/-- The carry after a pulse is below the count: the next dwell is `⌊B/M⌋` or `⌈B/M⌉` (the Christoffel gaps of Lemma
isopair). -/
theorem carry_lt (s : State) (hacc : s.acc < B) (hfire : B ≤ s.acc + M s.mu) : (step M B s).acc < M s.mu := by
  rw [step_fire hfire]
  show s.acc + M s.mu - B < M s.mu
  exact FRC.Nat.sub_lt_of_lt_add (Nat.add_lt_add_right hacc _) hfire

/-- 21:C7 — with carry `c < M` and a count `0 < M`, the dwell `d + 1` (the least `k` with `B ≤ c + k M`, so
`c + d M < B ≤ c + (d + 1) M`) satisfies `B / M ≤ d + 1 ≤ B / M + 1`: the dwell is `⌊B/M⌋` or `⌊B/M⌋ + 1`, and the
registered rate `M/B` and the dwell per quantum are the two faces of one window count. Without division:
`d · M < B < (d + 2) · M` (the `h1`, `h2` of the proof). -/
theorem dwell_two_values (M B c d : Nat) (hM : 0 < M) (hc : c < M) (hq : c + d * M < B)
    (hf : B ≤ c + (d + 1) * M) : B / M ≤ d + 1 ∧ d + 1 ≤ B / M + 1 := by
  have hs : B = M * (B / M) + B % M := FRC.Nat.div_spec M hM B
  have hr : B % M < M := Nat.mod_lt B hM
  have h1 : d * M < B := Nat.lt_of_le_of_lt (Nat.le_add_left _ _) hq
  have h2 : B < M * (d + 1 + 1) := by
    rw [Nat.mul_comm, Nat.succ_mul]
    exact Nat.lt_of_le_of_lt hf (by rw [Nat.add_comm c]; exact Nat.add_lt_add_left hc _)
  constructor
  · -- `B / M ≤ d + 1`: else `M (d + 2) ≤ M (B / M) ≤ B < M (d + 2)`
    cases Nat.lt_or_ge (B / M) (d + 1 + 1) with
    | inl h => exact Nat.le_of_lt_succ h
    | inr h =>
      have h3 : M * (d + 1 + 1) ≤ B :=
        calc M * (d + 1 + 1) ≤ M * (B / M) := Nat.mul_le_mul_left M h
          _ ≤ M * (B / M) + B % M := Nat.le_add_right _ _
          _ = B := hs.symm
      exact absurd (Nat.lt_of_le_of_lt h3 h2) (Nat.lt_irrefl _)
  · -- `d ≤ B / M`: else `M (B / M + 1) ≤ M d < B < M (B / M + 1)`
    cases Nat.lt_or_ge (B / M) d with
    | inr h => exact Nat.succ_le_succ h
    | inl h =>
      have h3 : M * (B / M + 1) ≤ M * d := Nat.mul_le_mul_left M h
      have h4 : B < M * (B / M + 1) := by
        rw [Nat.mul_succ]
        calc B = M * (B / M) + B % M := hs
          _ < M * (B / M) + M := Nat.add_lt_add_left hr _
      have h5 : M * d ≤ B := by rw [Nat.mul_comm]; exact Nat.le_of_lt h1
      exact absurd (Nat.lt_of_lt_of_le h4 (Nat.le_trans h3 h5)) (Nat.lt_irrefl B)

/-- 21:C4, 21:X7 — the equivalence cancellation of the two-shift law: the kick shifts the winding by `m · g` (the `m` of
coherent additivity) and the transport moves the registered position by the winding over `m`; the displacement is `g`,
and the cardinality cancels inside the law. -/
theorem equivalence_cancel (m g : Nat) (hm : 0 < m) : (m * g) / m = g :=
  FRC.Nat.div_unique hm (by rw [Nat.add_zero (m * g)])

end FRC.Relaxation
