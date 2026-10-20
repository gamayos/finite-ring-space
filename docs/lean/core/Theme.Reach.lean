import FrcCore.Theme.Logic

/-!
# FrcCore.Theme.Reach — the part and the reach bound (the logic theme; 25-godel's migration, 20 October 2026)

What a bounded part of a finite structure can hold, certify and derive, in the core's grammar and with no axioms:

* the term calculus of the wrap lemma (`Tm`, `val`, `Agree`): a term evaluated by table lookups takes the same value in
  every table that agrees on the entries the evaluation consults, so a certificate keeps its warrant in the small world
  built on its cited entries (25:D4, 25:J2); a term with `ℓ` leaves performs `ℓ − 1` lookups;
* abundance: every closed term over `1` and `+` with `ℓ` leaves has the value `ℓ mod p` in `M_p`, so any two terms with
  the same leaf count give a true equation, and the truths outrun every budget (25:E1, 25:G1);
* the reach bound: fewer than `a^(B+1)` records of length at most `B`, a fraction below `1/N` of a cohort of `2^L` truths
  once `L ≥ a^(B+1) N` (25:E2);
* aliasing: a reading of `m` elements by `R < m` states has a fibre of at least `⌈m/R⌉ ≥ 2` elements, and every element
  outside a maximal faithfully read range shares its reading with one inside (25:D3);
* the length horizon: a certificate contains its end sentence, so nothing longer than the budget is certified (25:G1);
* the evaluation ceiling: the one-rule system that asserts a sentence on exhaustive evaluation is sound and complete, its
  derivation of `φ` is `φ` itself, and the step check costs `m^q` atomic evaluations under `q` quantifiers (25:G2);
* the bare evaluation calculus: a derivation of a global clause from its `m` instances has at least `m + 1` lines, beyond
  every budget `H < m`, while the universal rule is sound (25:E4);
* the trichotomy's middle cell on its finite parts: the sentences "at least `n` elements" with a free unary predicate have
  models of `N` elements with the predicate inhabited and with it empty for every `n ≤ N`, and no structure of `N`
  elements satisfies "at least `N + 1` elements" (25:H5).

The paper module `FrcCore/Godel.lean` keeps every old name as an alias.
-/

namespace FRC.Reach

open FRC.Logic

/-! ### 25:D4, 25:E1 — closed terms, their values, and the entries an evaluation consults -/

/-- Closed terms over one constant and one binary operation: the full binary trees. -/
inductive Tm where
  | one : Tm
  | op : Tm → Tm → Tm

/-- The value of a term in the structure with the constant read as `u` and the operation's table `f`. -/
def val (u : Nat) (f : Nat → Nat → Nat) : Tm → Nat
  | .one => u
  | .op s t => f (val u f s) (val u f t)

/-- `g` agrees with `f` on every table entry the evaluation of the term in `(u, f)` consults. -/
def Agree (u : Nat) (f g : Nat → Nat → Nat) : Tm → Prop
  | .one => True
  | .op s t => Agree u f g s ∧ Agree u f g t ∧ g (val u f s) (val u f t) = f (val u f s) (val u f t)

/-- The number of leaves of a term. -/
def leaves : Tm → Nat
  | .one => 1
  | .op s t => leaves s + leaves t

/-- The number of table lookups the evaluation of a term performs: one per operation. -/
def lookups : Tm → Nat
  | .one => 0
  | .op s t => lookups s + lookups t + 1

/-- 25:D4, 25:J2 (Lemma wrap (2), the trace argument) — a structure that agrees with `M` on the entries the evaluation
consults gives the term the same value: the verification succeeds there step for step. -/
theorem trace_transport (u : Nat) (f g : Nat → Nat → Nat) : ∀ t : Tm, Agree u f g t → val u g t = val u f t
  | .one, _ => rfl
  | .op s t, ⟨hs, ht, e⟩ => by
    show g (val u g s) (val u g t) = f (val u f s) (val u f t)
    rw [trace_transport u f g s hs, trace_transport u f g t ht]; exact e

/-- 25:D4, 25:J2 (Lemma wrap (2), the end sentence) — an equation verified by evaluation in `M` is true in every other
table that agrees with `M` on the cited entries: the certificate keeps its warrant in the small world. -/
theorem wrap_equation (u : Nat) (f g : Nat → Nat → Nat) (s t : Tm) (hs : Agree u f g s) (ht : Agree u f g t)
    (h : val u f s = val u f t) : val u g s = val u g t := by
  rw [trace_transport u f g s hs, trace_transport u f g t ht]; exact h

/-- 25:D4 (Lemma wrap (2), the size of the trace) — the evaluation of a term with `ℓ` leaves performs `ℓ − 1`
lookups. -/
theorem lookups_succ : ∀ t : Tm, lookups t + 1 = leaves t
  | .one => rfl
  | .op s t => by
    show lookups s + lookups t + 1 + 1 = leaves s + leaves t
    rw [← lookups_succ s, ← lookups_succ t]
    exact (FRC.Nat.add_add_add_comm (lookups s) 1 (lookups t) 1).symm

/-- 25:E1 (Lemma abundance, the value) — in `M_p` the closed term over `1` and `+` with `ℓ` leaves has the
value `ℓ mod p`, whatever its shape. -/
theorem value_leaves (p : Nat) (hp : 0 < p) :
    ∀ t : Tm, val (1 % p) (fun x y => (x + y) % p) t = leaves t % p
  | .one => rfl
  | .op s t => by
    show (val (1 % p) (fun x y => (x + y) % p) s + val (1 % p) (fun x y => (x + y) % p) t) % p = (leaves s + leaves t) % p
    rw [value_leaves p hp s, value_leaves p hp t]
    exact (FRC.Nat.add_mod (leaves s) (leaves t) p hp).symm

/-- 25:E1 (Lemma abundance, the cohort) — any two terms with the same number of leaves give a true equation
of `M_p`. -/
theorem equal_leaves_equal_value (p : Nat) (hp : 0 < p) (s t : Tm) (h : leaves s = leaves t) :
    val (1 % p) (fun x y => (x + y) % p) s = val (1 % p) (fun x y => (x + y) % p) t := by
  rw [value_leaves p hp s, value_leaves p hp t, h]

/-- The left comb with `n + 1` leaves: `((1 + 1) + 1) + …`. -/
def combL : Nat → Tm
  | 0 => .one
  | n + 1 => .op (combL n) .one

/-- The right comb with `n + 1` leaves: `1 + (1 + (1 + …))`. -/
def combR : Nat → Tm
  | 0 => .one
  | n + 1 => .op .one (combR n)

theorem leaves_combL : ∀ n, leaves (combL n) = n + 1
  | 0 => rfl
  | n + 1 => by show leaves (combL n) + 1 = n + 1 + 1; rw [leaves_combL n]

theorem leaves_combR : ∀ n, leaves (combR n) = n + 1
  | 0 => rfl
  | n + 1 => by show 1 + leaves (combR n) = n + 1 + 1; rw [leaves_combR n, Nat.add_comm]

/-- 25:G1, 25:E1 (Proposition lengthhorizon, "beyond every budget there are truths") — for every budget `B` the two combs
with `B + 1` leaves give a true equation of `M_p` whose sides have more than `B` leaves each, so more than `B`
symbols: a truth no certificate of length `B` contains. -/
theorem truths_beyond_budget (p : Nat) (hp : 0 < p) (B : Nat) :
    ∃ s t : Tm, leaves s = leaves t ∧ B < leaves s ∧
      val (1 % p) (fun x y => (x + y) % p) s = val (1 % p) (fun x y => (x + y) % p) t :=
  ⟨combL B, combR B, by rw [leaves_combL, leaves_combR], by rw [leaves_combL]; exact Nat.lt_succ_self B,
    equal_leaves_equal_value p hp _ _ (by rw [leaves_combL, leaves_combR])⟩

/-! ### 25:E2 — the reach bound -/

/-- 25:E2, 25:G7 (Proposition reach, the vanishing fraction in finite form) — against a cohort of `2^L` truths the
records of length at most `B` certify a fraction below `1/N` once `L ≥ a^(B+1)·N`: their number times `N` is
below `2^L`. -/
theorem reach_vanishes (a : Nat) (ha : 2 ≤ a) (B N L : Nat) (h : a ^ (B + 1) * N ≤ L) :
    FRC.Logic.records a B * N < 2 ^ L :=
  Nat.lt_of_le_of_lt
    (Nat.le_trans (Nat.mul_le_mul_right N (Nat.le_of_lt (FRC.Logic.records_lt a ha B))) h)
    Nat.lt_two_pow_self

/-! ### sums over an initial segment, for the fibre and derivation counts -/

/-- `g 0 + … + g (R − 1)`. -/
def sumBelow (g : Nat → Nat) : Nat → Nat
  | 0 => 0
  | R + 1 => sumBelow g R + g R

theorem sumBelow_congr {g h : Nat → Nat} : ∀ {R : Nat}, (∀ r, r < R → g r = h r) → sumBelow g R = sumBelow h R
  | 0, _ => rfl
  | R + 1, e => by
    show sumBelow g R + g R = sumBelow h R + h R
    rw [sumBelow_congr (fun r hr => e r (Nat.lt_succ_of_lt hr)), e R (Nat.lt_succ_self R)]

theorem sumBelow_add (g h : Nat → Nat) : ∀ R, sumBelow (fun r => g r + h r) R = sumBelow g R + sumBelow h R
  | 0 => rfl
  | R + 1 => by
    show sumBelow (fun r => g r + h r) R + (g R + h R) = sumBelow g R + g R + (sumBelow h R + h R)
    rw [sumBelow_add g h R]; exact FRC.Nat.add_add_add_comm _ _ _ _

theorem sumBelow_const (c : Nat) : ∀ R, sumBelow (fun _ => c) R = R * c
  | 0 => (Nat.zero_mul c).symm
  | R + 1 => by show sumBelow (fun _ => c) R + c = (R + 1) * c; rw [sumBelow_const c R, Nat.succ_mul]

theorem sumBelow_le_sumBelow {g h : Nat → Nat} : ∀ {R : Nat}, (∀ r, r < R → g r ≤ h r) → sumBelow g R ≤ sumBelow h R
  | 0, _ => Nat.le_refl 0
  | R + 1, e => Nat.add_le_add (sumBelow_le_sumBelow (fun r hr => e r (Nat.lt_succ_of_lt hr))) (e R (Nat.lt_succ_self R))

/-- The indicator `[x = r]` summed over `r < R` is `1` when `x < R` and `0` otherwise. -/
theorem sumBelow_indicator (x : Nat) : ∀ R, sumBelow (fun r => cond (decide (x = r)) 1 0) R = if x < R then 1 else 0
  | 0 => rfl
  | R + 1 => by
    show sumBelow (fun r => cond (decide (x = r)) 1 0) R + cond (decide (x = R)) 1 0 = if x < R + 1 then 1 else 0
    rw [sumBelow_indicator x R]
    match Nat.lt_or_ge x R with
    | .inl hlt =>
      have hne : x ≠ R := Nat.ne_of_lt hlt
      rw [ite_eq_left hlt, ite_eq_left (Nat.lt_succ_of_lt hlt), decide_eq_false hne]; rfl
    | .inr hge =>
      rw [ite_eq_right (Nat.not_lt_of_ge hge)]
      match Nat.eq_or_lt_of_le hge with
      | .inl heq => rw [decide_eq_true heq.symm, ite_eq_left (heq ▸ Nat.lt_succ_self R)]; rfl
      | .inr hgt =>
        have hne : x ≠ R := fun e => Nat.lt_irrefl R (e ▸ hgt)
        rw [decide_eq_false hne, ite_eq_right (Nat.not_lt_of_ge (Nat.succ_le_of_lt hgt))]; rfl

/-- If the sum of `g` over `r < R` exceeds `R · c`, some `g r` exceeds `c` (constructively, by the case split on `g R`). -/
theorem exists_gt_of_sumBelow_gt (g : Nat → Nat) (c : Nat) : ∀ R, R * c < sumBelow g R → ∃ r, r < R ∧ c < g r
  | 0, h => by rw [Nat.zero_mul] at h; exact absurd h (Nat.lt_irrefl 0)
  | R + 1, h => by
    match Nat.lt_or_ge c (g R) with
    | .inl hgt => exact ⟨R, Nat.lt_succ_self R, hgt⟩
    | .inr hle =>
      have h' : R * c < sumBelow g R := by
        have e : (R + 1) * c = R * c + c := Nat.succ_mul R c
        have : R * c + c < sumBelow g R + g R := e ▸ h
        exact Nat.lt_of_add_lt_add_right (Nat.lt_of_lt_of_le this (Nat.add_le_add_left hle _))
      match exists_gt_of_sumBelow_gt g c R h' with
      | ⟨r, hr, hc⟩ => exact ⟨r, Nat.lt_succ_of_lt hr, hc⟩

/-! ### 25:D3 — aliasing: the fibres of a reading -/

/-- The number of elements below `m` that the reading `ρ` sends to `r`. -/
def fibre (ρ : Nat → Nat) (r m : Nat) : Nat := count (fun i => decide (ρ i = r)) m

/-- The fibres of a reading into `[0, R)` partition `[0, m)`: their sizes sum to `m`. -/
theorem sumBelow_fibre (ρ : Nat → Nat) (R : Nat) : ∀ m, (∀ i, i < m → ρ i < R) → sumBelow (fun r => fibre ρ r m) R = m
  | 0, _ => sumBelow_const 0 R ▸ (Nat.mul_zero R).symm ▸ rfl
  | m + 1, h => by
    have e : ∀ r, fibre ρ r (m + 1) = fibre ρ r m + cond (decide (ρ m = r)) 1 0 := fun r => rfl
    rw [sumBelow_congr (fun r _ => e r), sumBelow_add, sumBelow_fibre ρ R m (fun i hi => h i (Nat.lt_succ_of_lt hi)),
      sumBelow_indicator, ite_eq_left (h m (Nat.lt_succ_self m))]

/-- 25:D3 (Lemma wrap (1), the fibre) — a reading of `m` elements by `R` states has a fibre of more than `c` elements
for every `c` with `R · c < m`: the largest such `c + 1` is `⌈m/R⌉`, stated without division. -/
theorem alias_fibre (ρ : Nat → Nat) (m R : Nat) (hρ : ∀ i, i < m → ρ i < R) (c : Nat) (hc : R * c < m) :
    ∃ r, r < R ∧ c + 1 ≤ fibre ρ r m := by
  have hsum : sumBelow (fun r => fibre ρ r m) R = m := sumBelow_fibre ρ R m hρ
  have hlt : R * c < sumBelow (fun r => fibre ρ r m) R := by rw [hsum]; exact hc
  match exists_gt_of_sumBelow_gt _ _ R hlt with
  | ⟨r, hr, hgt⟩ => exact ⟨r, hr, Nat.succ_le_of_lt hgt⟩

/-- 25:D3 (Lemma wrap (1), at least two) — with fewer states than elements some reading stands for at least two
elements (the pigeonhole of 25:D1, counted). -/
theorem alias_two (ρ : Nat → Nat) (m R : Nat) (hρ : ∀ i, i < m → ρ i < R) (h : R < m) :
    ∃ r, r < R ∧ 2 ≤ fibre ρ r m :=
  alias_fibre ρ m R hρ 1 (by rw [Nat.mul_one]; exact h)

/-- `S` is read faithfully: `ρ` is injective on the elements of `S` below `m`. -/
def Faithful (ρ : Nat → Nat) (S : Nat → Bool) (m : Nat) : Prop :=
  ∀ i j, i < m → j < m → S i = true → S j = true → ρ i = ρ j → i = j

/-- The range `S` with one more element `x`. -/
def adjoin (S : Nat → Bool) (x : Nat) : Nat → Bool := fun y => S y || decide (y = x)

theorem anyBelow_true_iff (f : Nat → Bool) : ∀ n, anyBelow f n = true ↔ ∃ x, x < n ∧ f x = true
  | 0 => ⟨fun h => Bool.noConfusion h, fun ⟨_, hx, _⟩ => absurd hx (Nat.not_lt_zero _)⟩
  | n + 1 => by
    show (f n || anyBelow f n) = true ↔ _
    have ih := anyBelow_true_iff f n
    match hf : f n with
    | true => exact ⟨fun _ => ⟨n, Nat.lt_succ_self n, hf⟩, fun _ => rfl⟩
    | false => exact ⟨fun h => match ih.1 h with | ⟨x, hx, e⟩ => ⟨x, Nat.lt_succ_of_lt hx, e⟩,
        fun ⟨x, hx, e⟩ => match Nat.lt_or_ge x n with
          | .inl hlt => ih.2 ⟨x, hlt, e⟩
          | .inr hge => Bool.noConfusion ((Nat.le_antisymm (Nat.le_of_lt_succ hx) hge ▸ e).symm.trans hf)⟩

/-- 25:D3 (Lemma wrap (1), the alias) — if `S` is a maximal faithfully read range (adjoining any element outside it
breaks injectivity), every element `x < m` outside `S` is read as an alias of an element inside it. -/
theorem alias_outside (ρ : Nat → Nat) (S : Nat → Bool) (m : Nat) (hS : Faithful ρ S m)
    (hmax : ∀ x, x < m → S x = false → ¬ Faithful ρ (adjoin S x) m) (x : Nat) (hx : x < m) (hxS : S x = false) :
    ∃ s, s < m ∧ S s = true ∧ ρ s = ρ x := by
  match h : anyBelow (fun s => S s && decide (ρ s = ρ x)) m with
  | true =>
    match (anyBelow_true_iff _ m).1 h with
    | ⟨s, hs, e⟩ => exact ⟨s, hs, band_l e, of_decide_eq_true (band_r e)⟩
  | false =>
    exfalso
    apply hmax x hx hxS
    intro i j hi hj hSi hSj hij
    have hno : ∀ s, s < m → S s = true → ρ s ≠ ρ x := fun s hs hSs e =>
      Bool.noConfusion (((anyBelow_true_iff _ m).2 ⟨s, hs, by rw [hSs, decide_eq_true e]; rfl⟩).symm.trans h)
    -- each of i, j is in S or equals x
    have ci : S i = true ∨ i = x := match hi' : S i with
      | true => .inl rfl
      | false => .inr (of_decide_eq_true (by
          have : (S i || decide (i = x)) = true := hSi
          rw [hi'] at this; exact this))
    have cj : S j = true ∨ j = x := match hj' : S j with
      | true => .inl rfl
      | false => .inr (of_decide_eq_true (by
          have : (S j || decide (j = x)) = true := hSj
          rw [hj'] at this; exact this))
    match ci, cj with
    | .inl si, .inl sj => exact hS i j hi hj si sj hij
    | .inl si, .inr ej => exact absurd (ej ▸ hij) (hno i hi si)
    | .inr ei, .inl sj => exact absurd (ei ▸ hij.symm) (hno j hj sj)
    | .inr ei, .inr ej => exact ei.trans ej.symm

/-! ### 25:G1, 25:G2 — certificates, the length horizon, the one-rule system -/

/-- The length of a formula over a relational signature, in symbols. -/
def fsize : FForm → Nat
  | .rel _ xs => xs.length + 1
  | .eq _ _ => 3
  | .neg φ => fsize φ + 1
  | .conj φ ψ => fsize φ + fsize ψ + 1
  | .all φ => fsize φ + 1

/-- The length of a record: the lengths of its lines. -/
def csize : List FForm → Nat
  | [] => 0
  | φ :: l => fsize φ + csize l

theorem fsize_le_csize_of_mem {φ : FForm} : ∀ {l : List FForm}, φ ∈ l → fsize φ ≤ csize l
  | _ :: l, .head _ => Nat.le_add_right (fsize φ) (csize l)
  | ψ :: l, .tail _ h => Nat.le_trans (fsize_le_csize_of_mem h) (Nat.le_add_left (csize l) (fsize ψ))

/-- 25:G1, 25:G7 (Proposition lengthhorizon) — a certificate contains its designated end sentence, so a record of length at
most `B` certifies no sentence longer than `B`: nothing longer than the budget is certifiable in any system. -/
theorem length_horizon (l : List FForm) (φ : FForm) (hmem : φ ∈ l) (B : Nat) (hB : csize l ≤ B) : fsize φ ≤ B :=
  Nat.le_trans (fsize_le_csize_of_mem hmem) hB

/-- 25:G1 (Proposition lengthhorizon, contrapositive) — a sentence longer than `H` has no derivation of length at most
`H` in any system whose derivations contain their conclusion. -/
theorem no_short_derivation (l : List FForm) (φ : FForm) (hmem : φ ∈ l) (H : Nat) (hφ : H < fsize φ) :
    ¬ csize l ≤ H := fun h => Nat.lt_irrefl H (Nat.lt_of_lt_of_le hφ (length_horizon l φ hmem H h))

/-- The one-rule system `D_tt`: a sentence is derived, in one line, exactly when exhaustive evaluation makes it true. -/
def DttDerives (M : FinStr) (env : Nat → Nat) (φ : FForm) : Prop := fval M env φ = true

/-- 25:G2 (Proposition dtruth, soundness and completeness) — `D_tt` derives exactly the true sentences. -/
theorem dtt_sound_complete (M : FinStr) (env : Nat → Nat) (φ : FForm) : DttDerives M env φ ↔ Sat M env φ :=
  fin_theory_decidable M φ env

/-- 25:G2 (Proposition dtruth, the ceiling) — the derivation of `φ` in `D_tt` is the line `φ`, of length `|φ|`: a truth
has a derivation of length at most `H` exactly when it is no longer than `H`. -/
theorem dtt_ceiling (M : FinStr) (env : Nat → Nat) (φ : FForm) (H : Nat) :
    (Sat M env φ ∧ csize [φ] ≤ H) ↔ (DttDerives M env φ ∧ fsize φ ≤ H) :=
  ⟨fun ⟨hs, hl⟩ => ⟨(fin_theory_decidable M φ env).2 hs, by simpa [csize] using hl⟩,
   fun ⟨hd, hl⟩ => ⟨(fin_theory_decidable M φ env).1 hd, by simpa [csize] using hl⟩⟩

/-- The atomic evaluations the exhaustive evaluator performs: each quantifier multiplies by the `m` elements. -/
def cost (M : FinStr) : FForm → Nat
  | .rel _ _ => 1
  | .eq _ _ => 1
  | .neg φ => cost M φ
  | .conj φ ψ => cost M φ + cost M ψ
  | .all φ => M.m * cost M φ

/-- A prefix of `q` universal quantifiers. -/
def allBlock : Nat → FForm → FForm
  | 0, φ => φ
  | q + 1, φ => .all (allBlock q φ)

/-- 25:G2 (Proposition dtruth, the step check) — under `q` quantifiers the step check of `D_tt` performs `m^q` times the
matrix's atomic evaluations. -/
theorem cost_allBlock (M : FinStr) : ∀ (q : Nat) (φ : FForm), cost M (allBlock q φ) = M.m ^ q * cost M φ
  | 0, φ => (Nat.one_mul _).symm
  | q + 1, φ => by
    show M.m * cost M (allBlock q φ) = M.m ^ (q + 1) * cost M φ
    rw [cost_allBlock M q φ, Nat.pow_succ, Nat.mul_comm (M.m ^ q) M.m, Nat.mul_assoc]

/-! ### 25:E4 — the bare evaluation calculus and the global clause -/

/-- A line of the bare calculus: an instance `φ(c)` checked by evaluation, or the universal rule. -/
inductive Line where
  | inst : Nat → Line
  | univ : Line

/-- Whether the instance `φ(c)` occurs among the lines. -/
def hasInst : List Line → Nat → Bool
  | [], _ => false
  | .inst d :: l, c => decide (d = c) || hasInst l c
  | .univ :: l, c => hasInst l c

/-- The number of lines that are the instance `φ(c)`. -/
def countInst : List Line → Nat → Nat
  | [], _ => 0
  | .inst d :: l, c => countInst l c + cond (decide (d = c)) 1 0
  | .univ :: l, c => countInst l c

/-- The universal rule applies when every one of the `m` instances is among the premises. -/
def RuleApplies (m : Nat) (l : List Line) : Prop := ∀ c, c < m → hasInst l c = true

theorem one_le_countInst : ∀ (l : List Line) (c : Nat), hasInst l c = true → 1 ≤ countInst l c
  | .inst d :: l, c, h => by
    show 1 ≤ countInst l c + cond (decide (d = c)) 1 0
    match hd : decide (d = c) with
    | true => exact Nat.le_add_left 1 _
    | false =>
      have h' : hasInst l c = true := by
        have : (decide (d = c) || hasInst l c) = true := h
        rw [hd] at this; exact this
      exact Nat.le_trans (one_le_countInst l c h') (Nat.le_add_right _ _)
  | .univ :: l, c, h => one_le_countInst l c h

theorem sumBelow_countInst_le (m : Nat) : ∀ l : List Line, sumBelow (fun c => countInst l c) m ≤ l.length
  | [] => by
    have e : sumBelow (countInst []) m = sumBelow (fun _ => 0) m := sumBelow_congr (fun _ _ => rfl)
    rw [e, sumBelow_const, Nat.mul_zero]; exact Nat.le_refl 0
  | .inst d :: l => by
    show sumBelow (fun c => countInst l c + cond (decide (d = c)) 1 0) m ≤ l.length + 1
    rw [sumBelow_add, sumBelow_indicator]
    exact Nat.add_le_add (sumBelow_countInst_le m l) (by split <;> decide)
  | .univ :: l => Nat.le_trans (sumBelow_countInst_le m l) (Nat.le_succ _)

/-- 25:E4 (Remark globalclause, the length) — a derivation whose universal rule applies lists all `m` instances, so it has
at least `m` lines before the rule and `m + 1` with it. -/
theorem global_clause_length (m : Nat) (l : List Line) (h : RuleApplies m l) : m ≤ l.length :=
  have h1 : sumBelow (fun _ => 1) m ≤ sumBelow (fun c => countInst l c) m :=
    sumBelow_le_sumBelow (fun c hc => one_le_countInst l c (h c hc))
  Nat.le_trans (by rw [sumBelow_const, Nat.mul_one] at h1; exact h1) (sumBelow_countInst_le m l)

/-- 25:E4 (Remark globalclause, the budget) — every derivation of a global clause in the bare calculus, the rule line
included (`l.length + 1` lines), has more than `m` lines, so none fits a budget `H < m`. -/
theorem global_clause_defeats_budget (m : Nat) (l : List Line) (h : RuleApplies m l) (H : Nat) (hH : H < m) :
    ¬ l.length + 1 ≤ H := fun hle =>
  have : m + 1 ≤ H := Nat.le_trans (Nat.add_le_add_right (global_clause_length m l h) 1) hle
  Nat.lt_irrefl H (Nat.lt_of_lt_of_le hH (Nat.le_of_succ_le this))

/-- 25:E4 (Remark globalclause, soundness) — the universal rule is sound: when the `m` instances of `φ` evaluate true in
the structure, the global clause `∀ x φ(x)` holds there. -/
theorem bare_rule_sound (M : FinStr) (env : Nat → Nat) (φ : FForm)
    (h : ∀ c, c < M.m → fval M (cons c env) φ = true) : Sat M env (.all φ) :=
  fun x hx => (fin_theory_decidable M φ (cons x env)).1 (h x hx)

/-! ### 25:H5 — the trichotomy's middle cell on its finite parts -/

/-- `x₀ ≠ x_k ∧ … ∧ x_{i−1} ≠ x_k`: the variable `k` differs from the first `i` variables. -/
def diffs : Nat → Nat → FForm
  | 0, _ => .eq 0 0
  | i + 1, k => .conj (diffs i k) (.neg (.eq i k))

/-- The first `n` variables are pairwise distinct. -/
def distinct : Nat → FForm
  | 0 => .eq 0 0
  | k + 1 => .conj (distinct k) (diffs k k)

/-- `∃ x φ`, with the language's one quantifier. -/
def exF (φ : FForm) : FForm := .neg (.all (.neg φ))

/-- A block of `n` existential quantifiers. -/
def exBlockF : Nat → FForm → FForm
  | 0, φ => φ
  | n + 1, φ => exF (exBlockF n φ)

/-- The sentence "at least `n` elements": `n` distinct elements exist. -/
def atLeast (n : Nat) : FForm := exBlockF n (distinct n)

/-- The sentence "the predicate `P` (relation symbol `0`) is inhabited". -/
def someP : FForm := exF (.rel 0 [0])

theorem sat_diffs (M : FinStr) (env : Nat → Nat) : ∀ (i k : Nat), Sat M env (diffs i k) ↔ ∀ j, j < i → env j ≠ env k
  | 0, _ => ⟨fun _ j hj => absurd hj (Nat.not_lt_zero j), fun _ => rfl⟩
  | i + 1, k =>
    have ih := sat_diffs M env i k
    ⟨fun h j hj =>
      have h' : Sat M env (diffs i k) ∧ ¬ env i = env k := h
      match Nat.lt_or_ge j i with
      | .inl hlt => ih.1 h'.1 j hlt
      | .inr hge => by
        have e : j = i := Nat.le_antisymm (Nat.le_of_lt_succ hj) hge
        subst e; exact h'.2,
     fun h => show Sat M env (diffs i k) ∧ ¬ env i = env k from
      ⟨ih.2 (fun j hj => h j (Nat.lt_succ_of_lt hj)), h i (Nat.lt_succ_self i)⟩⟩

theorem sat_distinct (M : FinStr) (env : Nat → Nat) :
    ∀ n, Sat M env (distinct n) ↔ ∀ j k, j < k → k < n → env j ≠ env k
  | 0 => ⟨fun _ _ k _ hk => absurd hk (Nat.not_lt_zero k), fun _ => rfl⟩
  | k + 1 =>
    have ih := sat_distinct M env k
    have id := sat_diffs M env k k
    ⟨fun h j k' hj hk' =>
      have h' : Sat M env (distinct k) ∧ Sat M env (diffs k k) := h
      match Nat.lt_or_ge k' k with
      | .inl hlt => ih.1 h'.1 j k' hj hlt
      | .inr hge => by
        have e : k' = k := Nat.le_antisymm (Nat.le_of_lt_succ hk') hge
        subst e; exact id.1 h'.2 j hj,
     fun h => show Sat M env (distinct k) ∧ Sat M env (diffs k k) from
      ⟨ih.2 (fun j k' hj hk' => h j k' hj (Nat.lt_succ_of_lt hk')), id.2 (fun j hj => h j k hj (Nat.lt_succ_self k))⟩⟩

/-- A witness below `m` gives the existential sentence. -/
theorem sat_exF_of (M : FinStr) (env : Nat → Nat) (φ : FForm) (x : Nat) (hx : x < M.m) (h : Sat M (cons x env) φ) :
    Sat M env (exF φ) := fun hall => hall x hx h

/-- Choosing the elements `k, k − 1, …` from the outside in: after `k` more quantifiers the first `n` variables read
`0, …, n − 1` in reverse order. -/
theorem sat_exBlock_distinct (M : FinStr) (n : Nat) (hn : n ≤ M.m) :
    ∀ (k : Nat) (env : Nat → Nat), k ≤ n → (∀ i, i < n - k → env i = i + k) → Sat M env (exBlockF k (distinct n))
  | 0, env, _, h => (sat_distinct M env n).2 (fun j k hj hk e => by
      rw [h j (by rw [Nat.sub_zero]; exact Nat.lt_trans hj hk), h k (by rw [Nat.sub_zero]; exact hk)] at e
      exact Nat.ne_of_lt hj (Nat.add_right_cancel e))
  | k + 1, env, hk, h =>
    sat_exF_of M env _ k (Nat.lt_of_lt_of_le (Nat.lt_of_lt_of_le (Nat.lt_succ_self k) hk) hn)
      (sat_exBlock_distinct M n hn k (cons k env) (Nat.le_of_succ_le hk) (fun i hi => by
        match i with
        | 0 => show k = 0 + k; exact (Nat.zero_add k).symm
        | i + 1 =>
          show env i = i + 1 + k
          have : i < n - (k + 1) := by
            have h1 : i + 1 < n - k := hi
            have h2 : n - k = n - (k + 1) + 1 := by
              rw [Nat.sub_succ]; exact (Nat.succ_pred_eq_of_pos (Nat.lt_of_le_of_lt (Nat.zero_le _) h1)).symm
            rw [h2] at h1; exact Nat.lt_of_succ_lt_succ h1
          rw [h i this, Nat.add_assoc, Nat.add_comm 1 k]))

/-- 25:H5 (Corollary trichotomy, cell (ii) on its finite parts) — a structure of `N` elements satisfies "at least `n`
elements" for every `n ≤ N`. -/
theorem atLeast_of_le (M : FinStr) (env : Nat → Nat) (n : Nat) (hn : n ≤ M.m) : Sat M env (atLeast n) :=
  sat_exBlock_distinct M n hn n env (Nat.le_refl n) (fun i hi => absurd hi (by rw [Nat.sub_self]; exact Nat.not_lt_zero i))

/-- No structure of `m < n` elements has `n` distinct elements: the chosen values collide (25:D1's pigeonhole). -/
theorem not_exBlock_distinct (M : FinStr) (n : Nat) (hn : M.m < n) :
    ∀ (k : Nat) (env : Nat → Nat), (∀ i, i < n - k → env i < M.m) → ¬ Sat M env (exBlockF k (distinct n))
  | 0, env, h, hs =>
    part_collides hn env (fun i hi => h i (by rw [Nat.sub_zero]; exact hi))
      (fun i j hi hj e => match Nat.lt_or_ge i j with
        | .inl hlt => absurd e ((sat_distinct M env n).1 hs i j hlt hj)
        | .inr hge => match Nat.eq_or_lt_of_le hge with
          | .inl heq => heq.symm
          | .inr hgt => absurd e.symm ((sat_distinct M env n).1 hs j i hgt hi))
  | k + 1, env, h, hs =>
    hs (fun x hx => not_exBlock_distinct M n hn k (cons x env) (fun i hi => by
      match i with
      | 0 => exact hx
      | i + 1 =>
        show env i < M.m
        apply h i
        have h1 : i + 1 < n - k := hi
        have h2 : n - k = n - (k + 1) + 1 := by
          rw [Nat.sub_succ]; exact (Nat.succ_pred_eq_of_pos (Nat.lt_of_le_of_lt (Nat.zero_le _) h1)).symm
        rw [h2] at h1; exact Nat.lt_of_succ_lt_succ h1))

/-- 25:H5 (Corollary trichotomy, cell (ii) on its finite parts) — no structure of `N` elements satisfies "at least
`N + 1` elements": the finite parts of the theory bound the models they admit. -/
theorem not_atLeast_succ (M : FinStr) (env : Nat → Nat) : ¬ Sat M env (atLeast (M.m + 1)) :=
  not_exBlock_distinct M (M.m + 1) (Nat.lt_succ_self M.m) (M.m + 1) env
    (fun i hi => absurd hi (by rw [Nat.sub_self]; exact Nat.not_lt_zero i))

/-- The structure of `N` elements with the predicate everywhere true. -/
def withP (N : Nat) : FinStr := ⟨N, fun _ _ => true⟩

/-- The structure of `N` elements with the predicate everywhere false. -/
def withoutP (N : Nat) : FinStr := ⟨N, fun _ _ => false⟩

/-- 25:H5 (Corollary trichotomy, cell (ii) on its finite parts) — for every `N ≥ 1` the first `N` sentences "at least
`n` elements" have a model of `N` elements with `∃ x P(x)` true and one with it false, so they decide neither it nor its
negation; and `∀ x ¬P(x)` settles it. -/
theorem middle_cell_undecided (N : Nat) (hN : 0 < N) (env : Nat → Nat) :
    (∀ n, n ≤ N → Sat (withP N) env (atLeast n)) ∧ Sat (withP N) env someP ∧
    (∀ n, n ≤ N → Sat (withoutP N) env (atLeast n)) ∧ ¬ Sat (withoutP N) env someP :=
  ⟨fun n hn => atLeast_of_le (withP N) env n hn,
   sat_exF_of (withP N) env _ 0 hN rfl,
   fun n hn => atLeast_of_le (withoutP N) env n hn,
   fun hs => hs (fun _ _ h => Bool.noConfusion h)⟩

end FRC.Reach
