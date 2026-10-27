import FrcCore.Theme.Field
import FrcCore.Theme.Drift
import FrcCore.Theme.Window

/-!
# FrcCore.Theme.Static — the cut form of the static profile, the winding grading and the leakage count (the relaxation theme; 27 October 2026)

Three exact faces of 21-gravity's relaxation revision (reports/relaxation-window-20261027.md), on counts and on the
prime shell, with no axioms:

* `Static`, `static_iff`, `slip_of_exceeds` — the cut form of the exact static profile (Proposition exactprofile):
  a link carries at most `κ` quanta per chronon, a cut of `A r` links at most `κ · A r`, and a static locked transfer
  balances the enclosed demand `Q r` through every cut (the Gauss law of `FRC.Drift.gauss_law`); a static state exists
  exactly when `Q r ≤ κ · A r` at every cut, and slips wherever `Q r > κ · A r`.
* `cutArea`, `cutArea_mono`, `exterior_of_sq`, `slip_of_sq`, `slip_instance` — the cut weight `6(2r² + 2r + 1)` of the
  graph ball of radius `r` in the cubic chart (`FRC.Drift.cut_area_monotone`), monotone; a demand `m ≤ 12 κ r²` has its
  static exterior at `r`, a demand `m > 30 κ r²` (for `r ≥ 1`) slips there: the slip radius `r_*` sits between
  `√(m/30κ)` and `⌈√(m/12κ)⌉` (the chart's `r_* = √(Gm)` with `A_r = 4πr²` is the [chart] reading; the core carries the
  cut form exactly); the instance `m = 10⁴` at unit capacity, exterior from `r = 29`, decided by the kernel.
* `Graded`, `graded_mul`, `graded_const`, `equivariant_graded`, `selection` — the winding grading of the nonlinear
  completion (Theorem branch (i)): a sequence on the drive's orbit has grade `k` when one chronon multiplies it by
  `g^k`; grades add under products, a stationary offset has grade `0`, a drive-equivariant linear operation preserves
  the grade, and a sequence of grade `0` and of a grade `m` with `g^m ≠ 1` vanishes — no function of stationary offsets
  constitutes new onsite winding demand (21:C11).
* `leakage`, `returns`, `leakage_add_returns`, `returns_eq_div`, `leakage_eq` — the leakage count on the cycle (T14):
  the chronons below `T` at which the relative cycle of defect `a` on `C_L` fails to close are exactly the chronons off
  the return chain; the returns below `T ≥ 1` are `0` and the multiples of the first return, `⌊(T − 1)/T_def⌋ + 1`
  (`FRC.Drift.return_iff`), and the leakage is the rest. The count of multiples is pinned without division first
  (`count_multiples_spec`: `T ≤ c · d < T + d`), then read through `FRC.Nat.div_unique`.
-/

namespace FRC.Static

open FRC.Shell FRC.Shell.Frame

/-! ## The cut form of the exact static profile (21:C12) -/

/-- A static locked transfer on a radial partition: the cut `r` carries `t r` quanta per chronon, at most `κ` per link
over its `A r` links, and the transfer balances the enclosed demand `Q r` (the Gauss law of `FRC.Drift.gauss_law`). -/
def Static (κ : Nat) (A Q t : Nat → Nat) : Prop := (∀ r, t r ≤ κ * A r) ∧ (∀ r, t r = Q r)

/-- 21:C12 — a static locked state exists exactly when every cut can carry its enclosed demand, `Q r ≤ κ · A r`:
Proposition exactprofile's `ϰ A_r sin δ_r = Q_r` in its cut form. -/
theorem static_iff (κ : Nat) (A Q : Nat → Nat) : (∃ t, Static κ A Q t) ↔ ∀ r, Q r ≤ κ * A r :=
  ⟨fun ⟨t, ht⟩ r => by rw [← ht.2 r]; exact ht.1 r, fun h => ⟨Q, h, fun _ => rfl⟩⟩

/-- 21:C12 — slip exactly where the demand exceeds the cut's capacity: no static state through a cut with
`κ · A r < Q r`. -/
theorem slip_of_exceeds (κ : Nat) (A Q : Nat → Nat) (r : Nat) (h : κ * A r < Q r) : ¬ ∃ t, Static κ A Q t :=
  fun ht => Nat.lt_irrefl _ (Nat.lt_of_lt_of_le h ((static_iff κ A Q).mp ht r))

/-- The cut weight of the graph ball of radius `r` in the cubic chart, `6(2r² + 2r + 1)`
(`FRC.Drift.cut_area_monotone`). -/
def cutArea (r : Nat) : Nat := 6 * (2 * r * r + 2 * r + 1)

/-- 21:C12 — the cut weight grows with the radius. -/
theorem cutArea_mono (r : Nat) : cutArea r ≤ cutArea (r + 1) := Nat.le_of_lt (FRC.Drift.cut_area_monotone r).2

/-- 21:C12 — the static exterior exists wherever `12 κ r² ≥ m`: `cutArea r = 12r² + 12r + 6 ≥ 12 r²`, so the cut at
`r` carries the demand `m`. -/
theorem exterior_of_sq (κ m r : Nat) (h : m ≤ 12 * κ * (r * r)) : m ≤ κ * cutArea r := by
  have e : κ * (6 * (2 * r * r)) = 12 * κ * (r * r) := by
    rw [FRC.Nat.mul_assoc 2 r r, ← FRC.Nat.mul_assoc 6 2, FRC.Nat.mul_left_comm κ, ← FRC.Nat.mul_assoc]
  have h1 : 2 * r * r ≤ 2 * r * r + 2 * r + 1 := Nat.le_trans (Nat.le_add_right _ _) (Nat.le_add_right _ _)
  exact Nat.le_trans h (by rw [← e]; exact Nat.mul_le_mul_left κ (Nat.mul_le_mul_left 6 h1))

/-- 21:C12 — the static exterior fails wherever `30 κ r² < m` (for `r ≥ 1`): `12r + 6 ≤ 18 r²`, so
`cutArea r ≤ 30 r²` and the cut at `r` cannot carry the demand `m`. -/
theorem slip_of_sq (κ m r : Nat) (hr : 1 ≤ r) (h : 30 * κ * (r * r) < m) : κ * cutArea r < m := by
  have h2r : 2 * r ≤ 2 * (r * r) := by
    have := Nat.mul_le_mul_left (2 * r) hr
    rw [Nat.mul_one, FRC.Nat.mul_assoc] at this; exact this
  have hrr : 1 ≤ r * r := Nat.mul_le_mul hr hr
  have hcut : cutArea r ≤ 6 * (5 * (r * r)) := by
    show 6 * (2 * r * r + 2 * r + 1) ≤ 6 * (5 * (r * r))
    apply Nat.mul_le_mul_left 6
    have e : 2 * (r * r) + 2 * (r * r) + 1 * (r * r) = 5 * (r * r) := by
      rw [← FRC.Nat.add_mul, ← FRC.Nat.add_mul]
    rw [← e, FRC.Nat.mul_assoc 2 r r]
    exact Nat.add_le_add (Nat.add_le_add (Nat.le_refl _) h2r) (by rw [Nat.one_mul]; exact hrr)
  have e30 : κ * (6 * (5 * (r * r))) = 30 * κ * (r * r) := by
    rw [← FRC.Nat.mul_assoc 6 5, FRC.Nat.mul_left_comm κ, ← FRC.Nat.mul_assoc]
  exact Nat.lt_of_le_of_lt (by rw [← e30]; exact Nat.mul_le_mul_left κ hcut) h

/-- 21:C12 — a demand of `10⁴` at unit capacity: the cut at `r = 29` carries it (`cutArea 29 = 10446`) and the cut at
`r = 28` does not (`cutArea 28 = 9750`); the static exterior ends at `r = 29`, decided by the kernel. -/
theorem slip_instance : (10000 ≤ 1 * cutArea 29) ∧ (1 * cutArea 28 < 10000) := by decide

/-! ## The winding grading of the nonlinear completion (21:C11) -/

variable {p : Nat} [Pos p]

/-- A sequence on the drive's orbit has grade `k` when one chronon multiplies it by `g ^ k`. -/
def Graded (g : Shell p) (k : Nat) (f : Nat → Shell p) : Prop := ∀ x, f (x + 1) = g ^ k * f x

/-- 21:C11 — grades add under products: sources of grades `a` and `b` compose to grade `a + b`
(`FRC.Drift.character_composition`). -/
theorem graded_mul (g : Shell p) {a b : Nat} {f h : Nat → Shell p} (hf : Graded g a f) (hh : Graded g b h) :
    Graded g (a + b) (fun x => f x * h x) := fun x => by
  show f (x + 1) * h (x + 1) = g ^ (a + b) * (f x * h x)
  rw [hf x, hh x, pow_add, mul_mul_mul_comm]

/-- 21:C11 — a stationary relative-offset configuration carries grade `0`. -/
theorem graded_const (g : Shell p) (c : Shell p) : Graded g 0 (fun _ => c) := fun _ => by
  show c = g ^ 0 * c
  rw [pow_zero, one_mul]

/-- 21:C11 — an operation that commutes with the drive (`T f (x + 1) = T (f ∘ succ) x`, the hypothesis `hT`) and is
homogeneous of degree one pointwise (whenever `f'` is `c · f` at every chronon, `T f'` is `c · T f` at every chronon,
the hypothesis `hlin`, stated pointwise so that no function extensionality is used) sends grade-`k` sequences to
grade-`k` sequences: an adjacency-local drive-equivariant operation sends invariants to invariants. -/
theorem equivariant_graded (g : Shell p) (k : Nat) (T : (Nat → Shell p) → (Nat → Shell p))
    (hT : ∀ f x, T f (x + 1) = T (fun y => f (y + 1)) x)
    (hlin : ∀ (c : Shell p) (f f' : Nat → Shell p), (∀ y, f' y = c * f y) → ∀ x, T f' x = c * T f x)
    {f : Nat → Shell p} (hf : Graded g k f) : Graded g k (T f) := fun x => by
  rw [hT f x]
  exact hlin (g ^ k) f (fun y => f (y + 1)) hf x

/-- 21:C11, 21:X4 — character selection: a sequence of grade `0` that also has grade `m` with `g ^ m ≠ 1` vanishes
identically — a stationary offset configuration carries no winding demand. On the prime shell `(g^m − 1) f x = 0`
with `g^m − 1 ≠ 0` forces `f x = 0` (`FRC.Shell.Prime.mul_eq_zero`). -/
theorem selection (hp : FRC.Nat.isPrime p) (g : Shell p) (m : Nat) (hm : g ^ m ≠ 1) {f : Nat → Shell p}
    (h0 : Graded g 0 f) (hm' : Graded g m f) : ∀ x, f x = 0 := fun x => by
  have e : g ^ m * f x = f x := by rw [← hm' x, h0 x, pow_zero, one_mul]
  have hz : (g ^ m + -1) * f x = 0 := by rw [right_distrib, neg_one_mul, e, add_neg]
  rcases Prime.mul_eq_zero hp hz with h | h
  · exact absurd (Prime.eq_of_sub_eq_zero h) hm
  · exact h

/-! ## The leakage count on the cycle (21:C21, T14) -/

/-- The chronons below `T` at which the relative cycle of defect `a` on `C_L` does not return: the leakage count of the
window. -/
def leakage (L a T : Nat) : Nat := natCount (fun t => (t * a) % L ≠ 0) T

/-- The returns below `T`. -/
def returns (L a T : Nat) : Nat := natCount (fun t => (t * a) % L = 0) T

/-- 21:C21 — every chronon below `T` is a return or a leak: the leakage tally is the registered mismatch over the
window. -/
theorem leakage_add_returns (L a T : Nat) : leakage L a T + returns L a T = T := by
  rw [leakage, returns, ← FRC.Grav.natCount_or (fun t => (t * a) % L ≠ 0) (fun t => (t * a) % L = 0) (fun _ h => h) T]
  exact (natCount_congr _ _ T (fun x _ => ⟨fun _ => trivial, fun _ =>
    match Nat.decEq ((x * a) % L) 0 with
    | isTrue h => Or.inr h
    | isFalse h => Or.inl h⟩)).trans (FRC.Grav.natCount_true T)

/-- One chronon of the count of multiples of `d`: from `T ≤ c · d < T + d` for the count `c` below `T` to the same
bounds at `T + 1` for the count below `T + 1`. -/
theorem ceil_step (d T c : Nat) (hd : 0 < d) (h1 : T ≤ c * d) (h2 : c * d < T + d) :
    T + 1 ≤ (c + if T % d = 0 then 1 else 0) * d ∧ (c + if T % d = 0 then 1 else 0) * d < T + 1 + d :=
  match Nat.decEq (T % d) 0 with
  | isTrue h => by
    rw [ite_eq_left h]
    obtain ⟨q, hq⟩ := FRC.Nat.mod_spec d hd T
    rw [h, Nat.add_zero (d * q)] at hq
    -- `T = d q` and `d q ≤ c d < d q + d` pin the count: `c = q`
    have hcq : c = q := by
      apply Nat.le_antisymm
      · cases Nat.lt_or_ge c (q + 1) with
        | inl hlt => exact Nat.le_of_lt_succ hlt
        | inr hge =>
          have h3 : d * (q + 1) ≤ d * c := Nat.mul_le_mul_left d hge
          rw [Nat.mul_succ, ← hq, Nat.mul_comm d c] at h3
          exact absurd (Nat.lt_of_lt_of_le h2 h3) (Nat.lt_irrefl _)
      · cases Nat.lt_or_ge c q with
        | inr hge => exact hge
        | inl hlt =>
          have h3 : d * (c + 1) ≤ d * q := Nat.mul_le_mul_left d hlt
          rw [Nat.mul_succ, ← hq, Nat.mul_comm d c] at h3
          exact absurd (Nat.lt_of_lt_of_le (Nat.lt_add_of_pos_right hd) (Nat.le_trans h3 h1)) (Nat.lt_irrefl _)
    rw [hcq, Nat.succ_mul, Nat.mul_comm q d, ← hq]
    exact ⟨Nat.add_le_add_left hd T, Nat.add_lt_add_right (Nat.lt_succ_self T) d⟩
  | isFalse h => by
    rw [ite_eq_right h, Nat.add_zero c]
    refine ⟨?_, Nat.lt_of_lt_of_le h2 (Nat.add_le_add_right (Nat.le_succ T) d)⟩
    -- `T ≠ c d` since `c d ≡ 0`, so `T < c d`
    exact Nat.lt_of_le_of_ne h1 (fun e => h (by
      rw [e]; exact FRC.Nat.mod_unique (q := c) hd (by rw [Nat.mul_comm c d, Nat.add_zero (d * c)])))

/-- The multiples of `d` below `T`, counted, are `⌈T/d⌉`, stated without division: the count `c` has
`T ≤ c · d < T + d`. -/
theorem count_multiples_spec (d : Nat) (hd : 0 < d) :
    ∀ T, T ≤ natCount (fun t => t % d = 0) T * d ∧ natCount (fun t => t % d = 0) T * d < T + d
  | 0 => by
    show 0 ≤ 0 * d ∧ 0 * d < 0 + d
    rw [Nat.zero_mul, Nat.zero_add]; exact ⟨Nat.le_refl 0, hd⟩
  | T + 1 =>
    match count_multiples_spec d hd T with
    | ⟨h1, h2⟩ => ceil_step d T (natCount (fun t => t % d = 0) T) hd h1 h2

/-- The count below `T + 1` with `T + 1 ≤ c · d < T + 1 + d` is `⌊T/d⌋ + 1` (`FRC.Nat.div_unique`). -/
theorem floor_of_ceil (d T c : Nat) (h1 : T + 1 ≤ c * d) (h2 : c * d < T + 1 + d) : c = T / d + 1 :=
  match c, h1, h2 with
  | 0, h1, _ => by rw [Nat.zero_mul] at h1; exact absurd h1 (Nat.not_succ_le_zero T)
  | c' + 1, h1, h2 => by
    rw [Nat.succ_mul] at h1 h2
    have h3 : d * c' ≤ T := by rw [Nat.mul_comm]; exact Nat.le_of_lt_succ (Nat.lt_of_add_lt_add_right h2)
    have h4 : T < d * c' + d := by rw [Nat.mul_comm]; exact h1
    rw [FRC.Nat.div_unique (FRC.Nat.sub_lt_of_lt_add h4 h3) (FRC.Nat.add_sub_of_le h3).symm]

/-- 21:C21 — the returns are the multiples of the first return (`FRC.Drift.return_iff`). -/
theorem returns_eq_count (L a T : Nat) (hL : 0 < L) :
    returns L a T = natCount (fun t => t % FRC.Drift.firstReturn L a = 0) T :=
  natCount_congr _ _ T (fun t _ =>
    (FRC.Drift.return_iff L a t hL).trans (FRC.Nat.dvd_iff_mod (FRC.Drift.firstReturn_pos L a)))

/-- 21:C21, T14 — the returns below `T ≥ 1` are `0` and the multiples of the first return below `T`:
`⌊(T − 1)/T_def⌋ + 1`. -/
theorem returns_eq_div (L a T : Nat) (hL : 0 < L) (hT : 1 ≤ T) :
    returns L a T = (T - 1) / FRC.Drift.firstReturn L a + 1 :=
  match T, hT with
  | 0, hT => absurd hT (Nat.not_succ_le_zero 0)
  | T + 1, _ => by
    rw [returns_eq_count L a (T + 1) hL, FRC.Nat.add_sub_cancel T 1]
    obtain ⟨h1, h2⟩ := count_multiples_spec (FRC.Drift.firstReturn L a) (FRC.Drift.firstReturn_pos L a) (T + 1)
    exact floor_of_ceil _ _ _ h1 h2

/-- 21:C21, T14 — the leakage count of the window `T ≥ 1`: the chronons off the return chain,
`T − (⌊(T − 1)/T_def⌋ + 1)`. -/
theorem leakage_eq (L a T : Nat) (hL : 0 < L) (hT : 1 ≤ T) :
    leakage L a T = T - ((T - 1) / FRC.Drift.firstReturn L a + 1) := by
  have e := leakage_add_returns L a T
  rw [← returns_eq_div L a T hL hT]
  calc leakage L a T = leakage L a T + returns L a T - returns L a T := (FRC.Nat.add_sub_cancel _ _).symm
    _ = T - returns L a T := by rw [e]

end FRC.Static
