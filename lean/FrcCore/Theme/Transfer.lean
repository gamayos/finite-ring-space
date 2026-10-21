import FrcCore.Theme.Reach

/-!
# The logic theme — the transfer digraph: walks of every length give a periodic walk

5-reductio's Theorem periodic-dbe (5:E6), the one-dimensional periodic de Bruijn–Erdős theorem, at the level of its
transfer digraph (21 October 2026): a finite digraph on `[0, n)` in which walks of every finite length exist has a
vertex that begins walks of every length, every such vertex has a successor of the same kind, and the greedy walk
inside that sub-digraph (the least good successor at each step) is eventually periodic with period at most `n`
(5:E5's pigeonhole, `repeat_below`). A proper colouring of `k` consecutive blocks of a periodic graph is a walk of
length `k − 1` in its transfer digraph, so the periodic walk is a periodic proper colouring; that passage is the
body's modelling and rests there. No Mathlib, no axioms: the stabilisation of the decreasing sets of good vertices
is proved by counting, and the periodic walk is built by bounded search.
-/

namespace FRC.Transfer

open FRC.Logic FRC.Reach

/-- `walks edge n v k`: in the digraph on `[0, n)` with edge relation `edge`, the vertex `v` begins a walk of `k`
edges. -/
def walks (edge : Nat → Nat → Bool) (n : Nat) (v : Nat) : Nat → Bool
  | 0 => true
  | k + 1 => anyBelow (fun w => edge v w && walks edge n w k) n

variable {edge : Nat → Nat → Bool} {n : Nat}

theorem walks_succ_iff (v k : Nat) :
    walks edge n v (k + 1) = true ↔ ∃ w, w < n ∧ edge v w = true ∧ walks edge n w k = true :=
  Iff.trans (anyBelow_true_iff _ n)
    ⟨fun ⟨w, hw, h⟩ => ⟨w, hw, band_l h, band_r h⟩, fun ⟨w, hw, h1, h2⟩ => ⟨w, hw, by rw [h1, h2]; rfl⟩⟩

/-- A walk of `k + 1` edges contains one of `k`. -/
theorem walks_of_succ (v : Nat) : ∀ k, walks edge n v (k + 1) = true → walks edge n v k = true
  | 0, _ => rfl
  | k + 1, h => by
    match (walks_succ_iff v (k + 1)).mp h with
    | ⟨w, hw, he, hk⟩ => exact (walks_succ_iff v k).mpr ⟨w, hw, he, walks_of_succ w k hk⟩

theorem walks_mono (v : Nat) : ∀ j k, j ≤ k → walks edge n v k = true → walks edge n v j = true
  | j, k, hjk, h => by
    match Nat.eq_or_lt_of_le hjk with
    | Or.inl e => exact e ▸ h
    | Or.inr hlt =>
      match k, hlt with
      | k' + 1, hlt' => exact walks_mono v j k' (Nat.le_of_lt_succ hlt') (walks_of_succ v k' h)

/-! ### The sets of good vertices decrease and stabilise -/

/-- The number of vertices below `n` that begin a walk of `k` edges. -/
def goodCount (edge : Nat → Nat → Bool) (n k : Nat) : Nat := count (fun v => walks edge n v k) n

theorem count_le_of_imp (f g : Nat → Bool) : ∀ m, (∀ x, x < m → f x = true → g x = true) → count f m ≤ count g m
  | 0, _ => Nat.le_refl 0
  | m + 1, h => by
    show count f m + cond (f m) 1 0 ≤ count g m + cond (g m) 1 0
    have ih := count_le_of_imp f g m (fun x hx => h x (Nat.lt_succ_of_lt hx))
    exact match hf : f m with
      | false => Nat.le_trans (Nat.add_le_add_right ih 0) (Nat.add_le_add_left (Nat.zero_le _) _)
      | true => by rw [h m (Nat.lt_succ_self m) hf]; exact Nat.add_le_add_right ih 1

theorem count_le (f : Nat → Bool) : ∀ m, count f m ≤ m
  | 0 => Nat.le_refl 0
  | m + 1 => by
    show count f m + cond (f m) 1 0 ≤ m + 1
    exact match f m with
      | true => Nat.add_le_add_right (count_le f m) 1
      | false => Nat.le_succ_of_le (count_le f m)

/-- Equal counts of nested predicates: the smaller one holds wherever the larger does. -/
theorem eq_of_count_eq (f g : Nat → Bool) : ∀ m, (∀ x, x < m → f x = true → g x = true) → count f m = count g m →
    ∀ x, x < m → g x = true → f x = true
  | 0, _, _, x, hx, _ => absurd hx (Nat.not_lt_zero x)
  | m + 1, h, e, x, hx, hg => by
    have h' : ∀ x, x < m → f x = true → g x = true := fun x hx => h x (Nat.lt_succ_of_lt hx)
    have ih := count_le_of_imp f g m h'
    have e' : count f m + cond (f m) 1 0 = count g m + cond (g m) 1 0 := e
    match Nat.lt_or_ge x m with
    | Or.inl hxm =>
      -- the last position agrees or f m = false ≤ g m; either way the counts below m are equal
      have em : count f m = count g m := by
        match hf : f m with
        | true =>
          rw [hf, h m (Nat.lt_succ_self m) hf] at e'
          exact Nat.add_right_cancel e'
        | false =>
          rw [hf] at e'
          exact match hgm : g m with
            | false => by rw [hgm] at e'; exact Nat.add_right_cancel e'
            | true => by
                rw [hgm] at e'
                exact absurd e' (Nat.ne_of_lt (Nat.lt_of_le_of_lt (Nat.add_le_add_right ih 0) (Nat.lt_succ_self _)))
      exact eq_of_count_eq f g m h' em x hxm hg
    | Or.inr hxm =>
      have ex : x = m := Nat.le_antisymm (Nat.le_of_lt_succ hx) hxm
      subst ex
      exact match hf : f x with
        | true => rfl
        | false => by
            rw [hf, hg] at e'
            exact absurd e' (Nat.ne_of_lt (Nat.lt_of_le_of_lt (Nat.add_le_add_right ih 0) (Nat.lt_succ_self _)))

/-- The good sets decrease: `goodCount (k+1) ≤ goodCount k`. -/
theorem goodCount_succ_le (k : Nat) : goodCount edge n (k + 1) ≤ goodCount edge n k :=
  count_le_of_imp _ _ n (fun v _ h => walks_of_succ v k h)

theorem goodCount_le_of_le : ∀ j k, j ≤ k → goodCount edge n k ≤ goodCount edge n j
  | j, k, hjk => count_le_of_imp _ _ n (fun v _ h => walks_mono v j k hjk h)

/-- When the good set stops shrinking it is stationary: `goodCount k₀ = goodCount (k₀+1)` gives
`walks v k₀ → walks v k` for every `k`. -/
theorem stationary (k₀ : Nat) (e : goodCount edge n k₀ = goodCount edge n (k₀ + 1)) :
    ∀ k, ∀ v, v < n → walks edge n v k₀ = true → walks edge n v k = true := by
  -- step: the (k₀+1)-good are exactly the k₀-good; then (k₀+2)-good = successors into k₀-good ∩ … by induction
  have back : ∀ v, v < n → walks edge n v k₀ = true → walks edge n v (k₀ + 1) = true :=
    eq_of_count_eq (fun v => walks edge n v (k₀ + 1)) (fun v => walks edge n v k₀) n
      (fun v _ h => walks_of_succ v k₀ h) e.symm
  have up : ∀ m, ∀ v, v < n → walks edge n v k₀ = true → walks edge n v (k₀ + m) = true := by
    intro m
    induction m with
    | zero => exact fun v _ h => h
    | succ m ih =>
      intro v hv h
      match (walks_succ_iff v k₀).mp (back v hv h) with
      | ⟨w, hw, he, hk⟩ => exact (walks_succ_iff v (k₀ + m)).mpr ⟨w, hw, he, ih w hw hk⟩
  intro k v hv h
  match Nat.lt_or_ge k k₀ with
  | Or.inl hlt => exact walks_mono v k k₀ (Nat.le_of_lt hlt) h
  | Or.inr hge =>
    have : k = k₀ + (k - k₀) := (FRC.Nat.add_sub_of_le hge).symm
    rw [this]; exact up (k - k₀) v hv h

/-- Among `k = 0, …, n` the decreasing counts, all at most `n`, repeat: some `k₀ ≤ n` is stationary. -/
theorem exists_stationary : ∃ k₀, k₀ ≤ n ∧ goodCount edge n k₀ = goodCount edge n (k₀ + 1) := by
  -- otherwise the counts drop strictly at every step below n + 1, so goodCount (n+1) + (n+1) ≤ goodCount 0 ≤ n
  have drop : ∀ m, (∀ k, k < m → goodCount edge n k ≠ goodCount edge n (k + 1)) →
      goodCount edge n m + m ≤ goodCount edge n 0 := by
    intro m
    induction m with
    | zero => exact fun _ => Nat.le_refl _
    | succ m ih =>
      intro h
      have ih' := ih (fun k hk => h k (Nat.lt_succ_of_lt hk))
      have hlt : goodCount edge n (m + 1) < goodCount edge n m :=
        Nat.lt_of_le_of_ne (goodCount_succ_le m) (fun e => h m (Nat.lt_succ_self m) e.symm)
      show goodCount edge n (m + 1) + (m + 1) ≤ goodCount edge n 0
      have h3 : goodCount edge n (m + 1) + (m + 1) ≤ goodCount edge n m + m := by
        rw [← Nat.add_assoc, Nat.add_right_comm]
        exact Nat.add_le_add_right (Nat.succ_le_of_lt hlt) m
      exact Nat.le_trans h3 ih'
  have dec : Decidable (∃ k, k < n + 1 ∧ goodCount edge n k = goodCount edge n (k + 1)) :=
    FRC.Shell.decExistsLT (fun k => goodCount edge n k = goodCount edge n (k + 1)) (n + 1)
  match dec with
  | isTrue ⟨k, hk, e⟩ => exact ⟨k, Nat.le_of_lt_succ hk, e⟩
  | isFalse hne =>
    exfalso
    have hall : ∀ k, k < n + 1 → goodCount edge n k ≠ goodCount edge n (k + 1) :=
      fun k hk e => hne ⟨k, hk, e⟩
    have h1 := drop (n + 1) hall
    have h2 : goodCount edge n 0 ≤ n := count_le _ n
    exact Nat.lt_irrefl (n + 1) (Nat.lt_of_le_of_lt (Nat.le_trans (Nat.le_add_left (n + 1) _) h1) (Nat.lt_succ_of_le h2))

/-! ### A vertex good for every length, and a good successor -/

/-- `allGood v`: `v` begins walks of every length. -/
def AllGood (edge : Nat → Nat → Bool) (n v : Nat) : Prop := ∀ k, walks edge n v k = true

/-- 5:E6 (Theorem periodic-dbe, the sub-digraph is nonempty) — if walks of every length exist, some vertex begins
walks of every length: the good sets decrease and stabilise, and a vertex of the stationary set is good for ever. -/
theorem exists_allGood (h : ∀ k, ∃ v, v < n ∧ walks edge n v k = true) : ∃ v, v < n ∧ AllGood edge n v :=
  match exists_stationary (edge := edge) (n := n) with
  | ⟨k₀, _, e⟩ => match h k₀ with
    | ⟨v, hv, hk⟩ => ⟨v, hv, fun k => stationary k₀ e k v hv hk⟩

/-- 5:E6 (Theorem periodic-dbe, out-degree one in the sub-digraph) — a vertex good for every length has a successor
good for every length. -/
theorem allGood_successor {v : Nat} (_hv : v < n) (hg : AllGood edge n v) :
    ∃ w, w < n ∧ edge v w = true ∧ AllGood edge n w :=
  match exists_stationary (edge := edge) (n := n) with
  | ⟨k₀, _, e⟩ => match (walks_succ_iff v k₀).mp (hg (k₀ + 1)) with
    | ⟨w, hw, he, hk⟩ => ⟨w, hw, he, fun k => stationary k₀ e k w hw hk⟩

/-! ### The greedy walk in the sub-digraph and its period -/

/-- The stationary length, by bounded search (`exists_stationary` gives it below `n + 1`). -/
def stationaryIndex (edge : Nat → Nat → Bool) (n : Nat) : Nat :=
  match leastBelow (fun k => decide (goodCount edge n k = goodCount edge n (k + 1))) (n + 1) with
  | some k => k
  | none => 0

theorem stationaryIndex_spec : goodCount edge n (stationaryIndex edge n) = goodCount edge n (stationaryIndex edge n + 1) :=
  match exists_stationary (edge := edge) (n := n) with
  | ⟨k₀, hk₀, e⟩ => by
    unfold stationaryIndex
    match hl : leastBelow (fun k => decide (goodCount edge n k = goodCount edge n (k + 1))) (n + 1) with
    | some k => exact of_decide_eq_true (leastBelow_spec _ (n + 1) k hl).2.1
    | none =>
      exfalso
      match leastBelow_some (fun k => decide (goodCount edge n k = goodCount edge n (k + 1))) (n + 1) k₀
          (Nat.lt_succ_of_le hk₀) (decide_eq_true e) with
      | ⟨y, hy⟩ => rw [hl] at hy; exact nomatch hy

/-- `good v`: `v` is good at the stationary length, hence for every length. -/
def good (edge : Nat → Nat → Bool) (n : Nat) (v : Nat) : Bool := walks edge n v (stationaryIndex edge n)

theorem allGood_of_good {v : Nat} (hv : v < n) (h : good edge n v = true) : AllGood edge n v :=
  fun k => stationary (stationaryIndex edge n) stationaryIndex_spec k v hv h

/-- The greedy step: the least good successor of `v`, or `v` itself when there is none (never, on good vertices). -/
def next (edge : Nat → Nat → Bool) (n : Nat) (v : Nat) : Nat :=
  match leastBelow (fun w => edge v w && good edge n w) n with
  | some w => w
  | none => v

theorem next_spec {v : Nat} (hv : v < n) (hg : good edge n v = true) :
    next edge n v < n ∧ edge v (next edge n v) = true ∧ good edge n (next edge n v) = true := by
  match allGood_successor hv (allGood_of_good hv hg) with
  | ⟨w, hw, he, hwg⟩ =>
    have hP : (edge v w && good edge n w) = true := by
      have hgw : good edge n w = true := hwg (stationaryIndex edge n)
      rw [he, hgw]; rfl
    unfold next
    match hl : leastBelow (fun w => edge v w && good edge n w) n with
    | some u =>
      have s := leastBelow_spec _ n u hl
      exact ⟨s.1, band_l s.2.1, band_r s.2.1⟩
    | none =>
      exfalso
      match leastBelow_some (fun w => edge v w && good edge n w) n w hw hP with
      | ⟨y, hy⟩ => rw [hl] at hy; exact nomatch hy

theorem next_lt {v : Nat} (hv : v < n) (hg : good edge n v = true) : next edge n v < n := (next_spec hv hg).1

/-- The greedy walk from a good vertex stays good. -/
theorem iter_good {v : Nat} (hv : v < n) (hg : good edge n v = true) :
    ∀ k, iter (next edge n) v k < n ∧ good edge n (iter (next edge n) v k) = true
  | 0 => ⟨hv, hg⟩
  | k + 1 =>
    have ih := iter_good hv hg k
    have s := next_spec ih.1 ih.2
    ⟨s.1, s.2.2⟩

/-- The greedy step on good vertices and the identity elsewhere, so that it maps `[0, n)` into itself. -/
def nextGood (edge : Nat → Nat → Bool) (n : Nat) (y : Nat) : Nat := cond (good edge n y) (next edge n y) y

theorem nextGood_lt {y : Nat} (hy : y < n) : nextGood edge n y < n := by
  unfold nextGood
  cases hgy : good edge n y
  · exact hy
  · exact next_lt hy hgy

theorem iterGood {v : Nat} (hv : v < n) (hg : good edge n v = true) :
    ∀ j, good edge n (iter (nextGood edge n) v j) = true ∧ iter (nextGood edge n) v j < n
  | 0 => ⟨hg, hv⟩
  | j + 1 => by
    have ih := iterGood hv hg j
    show good edge n (nextGood edge n (iter (nextGood edge n) v j)) = true ∧ nextGood edge n (iter (nextGood edge n) v j) < n
    have e : nextGood edge n (iter (nextGood edge n) v j) = next edge n (iter (nextGood edge n) v j) := by
      show cond (good edge n (iter (nextGood edge n) v j)) (next edge n (iter (nextGood edge n) v j))
          (iter (nextGood edge n) v j) = next edge n (iter (nextGood edge n) v j)
      rw [ih.1]; rfl
    rw [e]
    exact ⟨(next_spec ih.2 ih.1).2.2, (next_spec ih.2 ih.1).1⟩

theorem iterGood_edge {v : Nat} (hv : v < n) (hg : good edge n v = true) (k : Nat) :
    edge (iter (nextGood edge n) v k) (iter (nextGood edge n) v (k + 1)) = true := by
  have gk := iterGood hv hg k
  show edge (iter (nextGood edge n) v k) (nextGood edge n (iter (nextGood edge n) v k)) = true
  have e : nextGood edge n (iter (nextGood edge n) v k) = next edge n (iter (nextGood edge n) v k) := by
    show cond (good edge n (iter (nextGood edge n) v k)) (next edge n (iter (nextGood edge n) v k))
        (iter (nextGood edge n) v k) = next edge n (iter (nextGood edge n) v k)
    rw [gk.1]; rfl
  rw [e]
  exact (next_spec gk.2 gk.1).2.1

/-- 5:E6 (Theorem periodic-dbe, the periodic walk) — if the digraph on `[0, n)` has walks of every length, it has an
infinite walk `w` that is periodic with period `m`, `1 ≤ m ≤ n`: every step is an edge and `w (i + m) = w i`. The
walk is the greedy walk in the sub-digraph of vertices good for every length, read from its first return. -/
theorem periodic_walk (h : ∀ k, ∃ v, v < n ∧ walks edge n v k = true) :
    ∃ w : Nat → Nat, ∃ m, 0 < m ∧ m ≤ n ∧ (∀ i, w i < n) ∧ (∀ i, edge (w i) (w (i + 1)) = true) ∧ ∀ i, w (i + m) = w i :=
  match exists_allGood h with
  | ⟨v, hv, hg⟩ =>
    have hgood : good edge n v = true := hg _
    have hstep : ∀ y, y < n → nextGood edge n y < n := fun y hy => nextGood_lt hy
    match eventually_periodic (nextGood edge n) n hstep v hv with
    | ⟨i₀, p, hp, hpn, hper⟩ =>
      ⟨fun i => iter (nextGood edge n) v (i₀ + i), p, hp, hpn,
       fun i => iter_lt _ hstep hv _,
       fun i => by
         show edge (iter (nextGood edge n) v (i₀ + i)) (iter (nextGood edge n) v (i₀ + (i + 1))) = true
         rw [← Nat.add_assoc]
         exact iterGood_edge hv hgood (i₀ + i),
       fun i => by
         show iter (nextGood edge n) v (i₀ + (i + p)) = iter (nextGood edge n) v (i₀ + i)
         rw [← Nat.add_assoc]; exact hper i⟩

end FRC.Transfer

