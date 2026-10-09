import FrcCore.Theme.Logic

/-!
# Formation universes, traces and bounded certificates (prototype for 29-finitism, 9 October 2026)

The objects of `29-finitism` (The Undeclared Posit of Potential Infinity) in the core's grammar: a universe of
formations is a finite set of objects `0, …, size − 1` with a formation image `form x`, `none` where formation fails;
a trace is what a completed check reads — `t` mentioned objects and the formation atoms it asserts among them; a check
passes in a universe under a reading of its objects. No imports beyond the logic theme; no axioms.
-/

namespace FRC.Formation

/-- A universe of formations: `size` objects and the formation image `form x` of each (`none`: the act fails at `x`). -/
structure Universe where
  size : Nat
  form : Nat → Option Nat

/-- Closed: every formation image is an object of the universe. -/
def Universe.Closed (U : Universe) : Prop := ∀ x y, x < U.size → U.form x = some y → y < U.size

/-- The trace of a completed check: `t` mentioned objects `0, …, t − 1` and the formation atoms it asserts,
`atom i j = true` reading "the formation image of `i` is `j`". -/
structure Trace where
  t : Nat
  atom : Nat → Nat → Bool

/-- The check passes in `U` under the reading `e`: the mentioned objects are distinct objects of `U` and every asserted
formation holds there. The check reads nothing else (the locality clause of Definition agent). -/
def Passes (T : Trace) (U : Universe) (e : Nat → Nat) : Prop :=
  (∀ i, i < T.t → e i < U.size) ∧
  (∀ i j, i < T.t → j < T.t → e i = e j → i = j) ∧
  (∀ i j, i < T.t → j < T.t → T.atom i j = true → U.form (e i) = some (e j))

/-! ### Theorem idleness — every passed check passes in a finite universe of its trace's size -/

/-- The minimal realization: exactly the trace's objects, each formed to the least object the trace asserts for it. -/
def minimal (T : Trace) : Universe :=
  ⟨T.t, fun i => Logic.leastBelow (fun j => T.atom i j) T.t⟩

/-- 29:C2, 29:C7 — the minimal realization has exactly the trace's `t` objects. -/
theorem minimal_size (T : Trace) : (minimal T).size = T.t := rfl

/-- A passed check asserts at most one image per object: the atoms are functional on the trace. -/
theorem atoms_functional (T : Trace) (U : Universe) (e : Nat → Nat) (h : Passes T U e) :
    ∀ i j j', i < T.t → j < T.t → j' < T.t → T.atom i j = true → T.atom i j' = true → j = j' :=
  fun i j j' hi hj hj' ha ha' =>
    have e1 := h.2.2 i j hi hj ha
    have e2 := h.2.2 i j' hi hj' ha'
    h.2.1 j j' hj hj' (Option.some.inj (e1.symm.trans e2))

/-- 29:C2 — Theorem idleness (the core form): a check that passes anywhere passes in the finite universe of its own
trace, read by the identity: `t(r)` objects suffice. -/
theorem realized (T : Trace) (U : Universe) (e : Nat → Nat) (h : Passes T U e) :
    Passes T (minimal T) (fun i => i) := by
  refine ⟨fun i hi => hi, fun i j _ _ hij => hij, fun i j hi hj ha => ?_⟩
  show Logic.leastBelow (fun k => T.atom i k) T.t = some j
  obtain ⟨y, hy⟩ := Logic.leastBelow_some (fun k => T.atom i k) T.t j hj ha
  have sp := Logic.leastBelow_spec (fun k => T.atom i k) T.t y hy
  rw [hy, atoms_functional T U e h i y j hi sp.1 hj sp.2.1 ha]

/-- 29:C2 — the minimal realization is closed: every image it assigns is one of its objects. -/
theorem minimal_closed (T : Trace) : (minimal T).Closed := fun x y _ hxy =>
  (Logic.leastBelow_spec (fun k => T.atom x k) T.t y hxy).1

/-! ### Corollary symmetry (the bound clause) — padding: the check passes in universes of every larger size -/

/-- `U` with `k` fresh objects appended, formation failing at each. -/
def pad (U : Universe) (k : Nat) : Universe :=
  ⟨U.size + k, fun x => if x < U.size then U.form x else none⟩

theorem pad_size (U : Universe) (k : Nat) : (pad U k).size = U.size + k := rfl

theorem pad_form (U : Universe) (k x : Nat) (hx : x < U.size) : (pad U k).form x = U.form x := by
  show (if x < U.size then U.form x else none) = U.form x
  rw [ite_eq_left hx]

/-- 29:C4 — Corollary symmetry, the bound: a passed check passes unchanged after padding by any number of formations,
so for every `B` there is a realizing universe of more than `B` objects and the passing entails no bound. -/
theorem passes_pad (T : Trace) (U : Universe) (e : Nat → Nat) (h : Passes T U e) (k : Nat) :
    Passes T (pad U k) e := by
  refine ⟨fun i hi => Nat.lt_of_lt_of_le (h.1 i hi) (Nat.le_add_right _ _), h.2.1, fun i j hi hj ha => ?_⟩
  rw [pad_form U k (e i) (h.1 i hi)]; exact h.2.2 i j hi hj ha

/-- 29:C4 — the realization at every size: for every `k` the minimal realization padded by `k` fresh formations has
exactly `t + k` objects, is closed, and the check passes in it read by the identity. No size is entailed. -/
theorem realization_at_size (T : Trace) (U : Universe) (e : Nat → Nat) (h : Passes T U e) (k : Nat) :
    Passes T (pad (minimal T) k) (fun i => i) ∧ (pad (minimal T) k).size = T.t + k ∧ (pad (minimal T) k).Closed :=
  ⟨passes_pad T (minimal T) _ (realized T U e h) k, rfl, fun x y hx hxy => by
    have hxy' : (if x < T.t then (minimal T).form x else none) = some y := hxy
    match Nat.lt_or_ge x T.t with
    | .inl hlt =>
      rw [ite_eq_left hlt] at hxy'
      exact Nat.lt_of_lt_of_le (minimal_closed T x y hlt hxy') (Nat.le_add_right _ _)
    | .inr hge =>
      rw [ite_eq_right (Nat.not_lt.2 hge)] at hxy'
      cases hxy'⟩

/-! ### The cyclic exhibit of Proposition posits — the successor act on the cycle of `n` points -/

/-- The successor on the cycle of `n` points: `x ↦ x + 1 (mod n)`. -/
def cyc (n x : Nat) : Nat := (x + 1) % n

/-- 29:B4 — the act is total: it stays on the cycle. -/
theorem cyc_lt (n : Nat) (hn : 0 < n) (x : Nat) : cyc n x < n := FRC.Nat.mod_lt' _ hn

theorem cyc_iter (n : Nat) (hn : 0 < n) (x : Nat) (hx : x < n) : ∀ k, Logic.iter (cyc n) x k = (x + k) % n
  | 0 => (FRC.Nat.mod_eq_of_lt hx).symm
  | k + 1 => by
    show cyc n (Logic.iter (cyc n) x k) = (x + (k + 1)) % n
    rw [cyc_iter n hn x hx k]
    show ((x + k) % n + 1) % n = (x + (k + 1)) % n
    rw [FRC.Nat.mod_add_mod _ _ _ hn, Nat.add_assoc]

/-- 29:B4 — the act returns to its start after `n` steps: the orbit is a cycle, so iteration makes nothing new. -/
theorem cyc_return (n : Nat) (hn : 0 < n) (x : Nat) (hx : x < n) : Logic.iter (cyc n) x n = x := by
  rw [cyc_iter n hn x hx n, Nat.add_comm]
  have : (n + x) % n = (n * 1 + x) % n := by rw [Nat.mul_one]
  rw [this, FRC.Nat.add_mul_mod_self_left x 1 n hn, FRC.Nat.mod_eq_of_lt hx]

/-- The act is injective on the cycle. -/
theorem cyc_inj (n : Nat) (hn : 0 < n) : ∀ x y, x < n → y < n → cyc n x = cyc n y → x = y := fun x y hx hy e => by
  have key : ∀ z, z < n → cyc n z = if z + 1 < n then z + 1 else 0 := fun z hz => by
    show (z + 1) % n = _
    by_cases h : z + 1 < n
    · rw [ite_eq_left h]; exact FRC.Nat.mod_eq_of_lt h
    · rw [ite_eq_right h]
      have : z + 1 = n := Nat.le_antisymm (Nat.succ_le_of_lt hz) (Nat.le_of_not_lt h)
      rw [this]; exact FRC.Nat.mod_self n hn
  rw [key x hx, key y hy] at e
  by_cases h1 : x + 1 < n <;> by_cases h2 : y + 1 < n
  · rw [ite_eq_left h1, ite_eq_left h2] at e; exact Nat.succ.inj e
  · rw [ite_eq_left h1, ite_eq_right h2] at e; exact absurd e (Nat.succ_ne_zero x)
  · rw [ite_eq_right h1, ite_eq_left h2] at e; exact absurd e.symm (Nat.succ_ne_zero y)
  · have ex : x + 1 = n := Nat.le_antisymm (Nat.succ_le_of_lt hx) (Nat.le_of_not_lt h1)
    have ey : y + 1 = n := Nat.le_antisymm (Nat.succ_le_of_lt hy) (Nat.le_of_not_lt h2)
    exact Nat.succ.inj (ex.trans ey.symm)

/-- 29:B4 — every point of the cycle is already an image: the act produces no new formation (the pigeonhole, `inj_onto`). -/
theorem cyc_onto (n : Nat) (hn : 0 < n) (z : Nat) (hz : z < n) : ∃ x, x < n ∧ cyc n x = z :=
  Logic.inj_onto n (cyc n) (fun x _ => cyc_lt n hn x) (cyc_inj n hn) z hz

/-! ### Lemma boundary, Case 1 — the disjoint double, its swap, and the parity of invariant conditions -/

/-- The disjoint double `U ⊔ U`: the objects `x < n` the first copy, `n + x` the second, each formed inside its copy. -/
def double (U : Universe) : Universe :=
  ⟨U.size + U.size, fun x => if x < U.size then U.form x
    else match U.form (x - U.size) with | some y => some (U.size + y) | none => none⟩

/-- The swap of the two copies. -/
def swap (U : Universe) (x : Nat) : Nat := if x < U.size then U.size + x else x - U.size

theorem swap_lt (U : Universe) (x : Nat) (hx : x < (double U).size) : swap U x < (double U).size := by
  show (if x < U.size then U.size + x else x - U.size) < U.size + U.size
  by_cases h : x < U.size
  · rw [ite_eq_left h]; exact Nat.add_lt_add_left h _
  · rw [ite_eq_right h]
    exact Nat.lt_of_lt_of_le (FRC.Nat.sub_lt_of_lt_add hx (Nat.le_of_not_lt h)) (Nat.le_add_left _ _)

/-- 29:C6 — the swap is an involution. -/
theorem swap_swap (U : Universe) (x : Nat) (hx : x < (double U).size) : swap U (swap U x) = x := by
  show (if (if x < U.size then U.size + x else x - U.size) < U.size then U.size + (if x < U.size then U.size + x else x - U.size)
        else (if x < U.size then U.size + x else x - U.size) - U.size) = x
  by_cases h : x < U.size
  · rw [ite_eq_left h]
    have : ¬ U.size + x < U.size := Nat.not_lt.2 (Nat.le_add_right _ _)
    rw [ite_eq_right this, FRC.Nat.add_sub_cancel_left]
  · rw [ite_eq_right h]
    have hlt : x - U.size < U.size := FRC.Nat.sub_lt_of_lt_add hx (Nat.le_of_not_lt h)
    rw [ite_eq_left hlt, FRC.Nat.add_sub_of_le (Nat.le_of_not_lt h)]

/-- 29:C6 — the swap moves every object: no fixed point. -/
theorem swap_ne (U : Universe) (x : Nat) (hx : x < (double U).size) : swap U x ≠ x := by
  show (if x < U.size then U.size + x else x - U.size) ≠ x
  by_cases h : x < U.size
  · rw [ite_eq_left h]; intro e
    have : U.size + x = 0 + x := by rw [Nat.zero_add]; exact e
    exact Nat.lt_irrefl 0 (Nat.lt_of_lt_of_le (Nat.lt_of_le_of_lt (Nat.zero_le _) h) (Nat.le_of_eq (FRC.Nat.add_right_cancel this)))
  · rw [ite_eq_right h]; intro e
    have hx2 : x < U.size + U.size := hx
    have hpos : 0 < U.size := match hU0 : U.size, hx2 with
      | 0, hx0 => absurd hx0 (Nat.not_lt_zero x)
      | m + 1, _ => Nat.succ_pos m
    have : x - U.size < x := Nat.sub_lt (Nat.lt_of_lt_of_le hpos (Nat.le_of_not_lt h)) hpos
    rw [e] at this; exact Nat.lt_irrefl x this

theorem double_form_left (U : Universe) (x : Nat) (hx : x < U.size) : (double U).form x = U.form x := by
  show (if x < U.size then U.form x else _) = U.form x
  rw [ite_eq_left hx]

theorem double_form_right (U : Universe) (x : Nat) (_hx : x < U.size) :
    (double U).form (U.size + x) = match U.form x with | some y => some (U.size + y) | none => none := by
  show (if U.size + x < U.size then _ else match U.form (U.size + x - U.size) with | some y => some (U.size + y) | none => none) = _
  have : ¬ U.size + x < U.size := Nat.not_lt.2 (Nat.le_add_right _ _)
  rw [ite_eq_right this, FRC.Nat.add_sub_cancel_left]

theorem double_form_right' (U : Universe) (x : Nat) (h : ¬ x < U.size) :
    (double U).form x = match U.form (x - U.size) with | some y => some (U.size + y) | none => none := by
  show (if x < U.size then _ else match U.form (x - U.size) with | some y => some (U.size + y) | none => none) = _
  rw [ite_eq_right h]

/-- 29:C6 — the swap is an automorphism of the double: it commutes with formation. -/
theorem swap_form (U : Universe) (hU : U.Closed) (x : Nat) (hx : x < (double U).size) :
    (double U).form (swap U x) = match (double U).form x with | some y => some (swap U y) | none => none := by
  by_cases h : x < U.size
  · have hs : swap U x = U.size + x := by show (if x < U.size then _ else _) = _; rw [ite_eq_left h]
    rw [hs, double_form_right U x h, double_form_left U x h]
    match hf : U.form x with
    | none => rfl
    | some y =>
      have hy : y < U.size := hU x y h hf
      show some (U.size + y) = some (if y < U.size then U.size + y else y - U.size)
      rw [ite_eq_left hy]
  · have hxs : x - U.size < U.size := FRC.Nat.sub_lt_of_lt_add hx (Nat.le_of_not_lt h)
    have hs : swap U x = x - U.size := by show (if x < U.size then _ else _) = _; rw [ite_eq_right h]
    rw [hs, double_form_left U _ hxs, double_form_right' U x h]
    match hf : U.form (x - U.size) with
    | none => rfl
    | some y =>
      show some y = some (if U.size + y < U.size then _ else U.size + y - U.size)
      have : ¬ U.size + y < U.size := Nat.not_lt.2 (Nat.le_add_right _ _)
      rw [ite_eq_right this, FRC.Nat.add_sub_cancel_left]

/-- 29:C6 — a passed check passes in the double, read in the first copy. -/
theorem passes_double (T : Trace) (U : Universe) (e : Nat → Nat) (h : Passes T U e) : Passes T (double U) e := by
  refine ⟨fun i hi => Nat.lt_of_lt_of_le (h.1 i hi) (Nat.le_add_right _ _), h.2.1, fun i j hi hj ha => ?_⟩
  rw [double_form_left U (e i) (h.1 i hi)]; exact h.2.2 i j hi hj ha

/-- Counting over two blocks. -/
theorem count_add (f : Nat → Bool) (a : Nat) : ∀ b, Logic.count f (a + b) = Logic.count f a + Logic.count (fun i => f (a + i)) b
  | 0 => rfl
  | b + 1 => by
    show Logic.count f (a + b) + cond (f (a + b)) 1 0 = Logic.count f a + (Logic.count (fun i => f (a + i)) b + cond (f (a + b)) 1 0)
    rw [count_add f a b, Nat.add_assoc]

theorem count_congr {f g : Nat → Bool} : ∀ {n : Nat}, (∀ i, i < n → f i = g i) → Logic.count f n = Logic.count g n
  | 0, _ => rfl
  | n + 1, h => by
    show Logic.count f n + cond (f n) 1 0 = Logic.count g n + cond (g n) 1 0
    rw [count_congr (fun i hi => h i (Nat.lt_succ_of_lt hi)), h n (Nat.lt_succ_self n)]

/-- 29:C6 — Lemma boundary, Case 1: a condition invariant under the swap has an even number of satisfiers in the double,
its satisfiers come in pairs. -/
theorem invariant_count_even (U : Universe) (D : Nat → Bool)
    (hD : ∀ x, x < (double U).size → D (swap U x) = D x) :
    Logic.count D (double U).size = 2 * Logic.count D U.size := by
  show Logic.count D (U.size + U.size) = 2 * Logic.count D U.size
  rw [count_add D U.size U.size, Nat.two_mul]
  have : ∀ i, i < U.size → D (U.size + i) = D i := fun i hi => by
    have hs : swap U i = U.size + i := by show (if i < U.size then _ else _) = _; rw [ite_eq_left hi]
    rw [← hs]; exact hD i (Nat.lt_of_lt_of_le hi (Nat.le_add_right _ _))
  rw [count_congr this]

/-- 29:C6, 29:X1 — a swap-invariant condition has zero or at least two satisfiers, never exactly one. -/
theorem no_unique_invariant (U : Universe) (D : Nat → Bool)
    (hD : ∀ x, x < (double U).size → D (swap U x) = D x) : Logic.count D (double U).size ≠ 1 := by
  rw [invariant_count_even U D hD]
  intro h
  cases hc : Logic.count D U.size with
  | zero => rw [hc] at h; exact Nat.noConfusion h
  | succ c => rw [hc, Nat.mul_succ] at h; exact Nat.noConfusion (Nat.succ.inj h)

/-! ### Lemma boundary, Case 2 — the minimal realization confines satisfiers to the trace -/

/-- 29:C7, 29:X1 — Lemma boundary, Case 2: in the minimal realization a datum the trace never forms has no preimage,
so the backward condition "the object whose formation image is `x`" has zero satisfiers. -/
theorem no_preimage_in_minimal (T : Trace) (x : Nat) (hx : ∀ i, i < T.t → T.atom i x = false) :
    ∀ y, y < T.t → (minimal T).form y ≠ some x := fun y hy e =>
  have sp := Logic.leastBelow_spec (fun k => T.atom y k) T.t x e
  Bool.noConfusion ((hx y hy).symm.trans sp.2.1)

/-! ### Lemma innocence (ii) — induction is a theorem of every finite frame -/

/-- 29:B6, 29:E2, 29:X2 — Lemma innocence (ii): on the finite frame `[0, n)` the induction schema holds for every
property, from the least-number principle (`leastBelow`): a property true at `0` and closed under successor below `n`
holds below `n`. -/
theorem finite_induction (n : Nat) (P : Nat → Bool) (h0 : P 0 = true)
    (hs : ∀ x, x + 1 < n → P x = true → P (x + 1) = true) : ∀ x, x < n → P x = true := fun x hx => by
  match hP : P x with
  | true => rfl
  | false =>
    exfalso
    obtain ⟨m, hm⟩ := Logic.leastBelow_some (fun y => !P y) n x hx (by rw [hP]; rfl)
    have sp := Logic.leastBelow_spec (fun y => !P y) n m hm
    cases m with
    | zero => have := sp.2.1; rw [h0] at this; exact Bool.noConfusion this
    | succ k =>
      have hk : P k = true := by
        have := sp.2.2 k (Nat.lt_succ_self k)
        match hPk : P k with
        | true => rfl
        | false => rw [hPk] at this; exact Bool.noConfusion this
      have := sp.2.1; rw [hs k sp.1 hk] at this; exact Bool.noConfusion this

/-! ### Proposition illusion — the buffer frame -/

/-- The buffer frame: `σ` seeds, each the root of a chain of `D` formations; object `s (D + 1) + k` is seed `s` at
level `k ≤ D`; formation steps up the chain and fails at the top. -/
def buffer (σ D : Nat) : Universe :=
  ⟨σ * (D + 1), fun x => if x % (D + 1) < D ∧ x < σ * (D + 1) then some (x + 1) else none⟩

theorem buffer_size (σ D : Nat) : (buffer σ D).size = σ * (D + 1) := rfl

/-- 29:C8 — every object below the top level has a formation image: the act succeeds at every level `k < D`. -/
theorem buffer_forms (σ D x : Nat) (hx : x < σ * (D + 1)) (hk : x % (D + 1) < D) :
    (buffer σ D).form x = some (x + 1) := by
  show (if x % (D + 1) < D ∧ x < σ * (D + 1) then some (x + 1) else none) = some (x + 1)
  rw [ite_eq_left ⟨hk, hx⟩]

/-- 29:C8 — the image is fresh: one level up, inside the frame. -/
theorem buffer_fresh (σ D x : Nat) (hx : x < σ * (D + 1)) (hk : x % (D + 1) < D) :
    x + 1 < σ * (D + 1) ∧ (x + 1) % (D + 1) = x % (D + 1) + 1 := by
  have hD : 0 < D + 1 := Nat.succ_pos D
  obtain ⟨q, hq⟩ := FRC.Nat.mod_spec (D + 1) hD x
  have hr : x % (D + 1) + 1 < D + 1 := Nat.add_lt_add_right hk 1
  have e : x + 1 = (D + 1) * q + (x % (D + 1) + 1) := by rw [← Nat.add_assoc, ← hq]
  refine ⟨?_, FRC.Nat.mod_unique hr e⟩
  -- x + 1 < σ(D+1): x lies in block q, x + 1 stays in block q since its residue is below D + 1
  have hq' : q < σ := match Nat.lt_or_ge q σ with
    | .inl hlt => hlt
    | .inr hσ =>
      have h1 : σ * (D + 1) ≤ (D + 1) * q := by rw [Nat.mul_comm]; exact Nat.mul_le_mul_left _ hσ
      have h2 : (D + 1) * q ≤ x := by rw [hq]; exact Nat.le_add_right _ _
      absurd (Nat.lt_of_lt_of_le hx (Nat.le_trans h1 h2)) (Nat.lt_irrefl x)
  rw [e]
  calc (D + 1) * q + (x % (D + 1) + 1) < (D + 1) * q + (D + 1) := Nat.add_lt_add_left hr _
    _ = (D + 1) * (q + 1) := by rw [Nat.mul_succ]
    _ ≤ (D + 1) * σ := Nat.mul_le_mul_left _ hq'
    _ = σ * (D + 1) := Nat.mul_comm _ _

/-- The levels reached by iterating formation from a seed: `k` acts from seed `s` reach level `k`, for `k ≤ D`. -/
def chain (σ D s : Nat) : Nat → Option Nat
  | 0 => some (s * (D + 1))
  | k + 1 => match chain σ D s k with | some x => (buffer σ D).form x | none => none

/-- 29:C8 — `k` acts from seed `s` reach level `k`, for `k ≤ D`. -/
theorem chain_level (σ D s : Nat) (hs : s < σ) : ∀ k, k ≤ D → chain σ D s k = some (s * (D + 1) + k)
  | 0, _ => rfl
  | k + 1, hk => by
    show (match chain σ D s k with | some x => (buffer σ D).form x | none => none) = some (s * (D + 1) + (k + 1))
    rw [chain_level σ D s hs k (Nat.le_of_succ_le hk)]
    have hD : 0 < D + 1 := Nat.succ_pos D
    have hmod : (s * (D + 1) + k) % (D + 1) = k :=
      FRC.Nat.mod_unique (Nat.lt_of_lt_of_le (Nat.lt_succ_of_le (Nat.le_of_succ_le hk)) (Nat.le_refl _)) (by rw [Nat.mul_comm])
    have hlt : s * (D + 1) + k < σ * (D + 1) :=
      calc s * (D + 1) + k < s * (D + 1) + (D + 1) := Nat.add_lt_add_left (Nat.lt_succ_of_le (Nat.le_of_succ_le hk)) _
        _ = (s + 1) * (D + 1) := by rw [Nat.succ_mul]
        _ ≤ σ * (D + 1) := Nat.mul_le_mul_right _ hs
    show (buffer σ D).form (s * (D + 1) + k) = some (s * (D + 1) + (k + 1))
    rw [buffer_forms σ D _ hlt (by rw [hmod]; exact Nat.lt_of_succ_le hk)]
    rfl

/-- 29:C8, 29:X1 — Proposition illusion (i), (ii) in the core: in the buffer frame of `σ` seeds and `D` rounds, every
object reached by fewer than `D` acts from a seed has a formation image, and the image is one level further: no act on
a reachable object fails and no enumeration below the horizon `D` is exhausted. -/
theorem illusion (σ D s k : Nat) (hs : s < σ) (hk : k < D) :
    ∃ x y, chain σ D s k = some x ∧ (buffer σ D).form x = some y ∧ chain σ D s (k + 1) = some y ∧ x < y ∧
      y < (buffer σ D).size := by
  have hx := chain_level σ D s hs k (Nat.le_of_lt hk)
  have hy := chain_level σ D s hs (k + 1) hk
  refine ⟨s * (D + 1) + k, s * (D + 1) + (k + 1), hx, ?_, hy, Nat.lt_succ_self _, ?_⟩
  · have hmod : (s * (D + 1) + k) % (D + 1) = k :=
      FRC.Nat.mod_unique (Nat.lt_succ_of_lt hk) (by rw [Nat.mul_comm])
    have hlt : s * (D + 1) + k < σ * (D + 1) :=
      calc s * (D + 1) + k < s * (D + 1) + (D + 1) := Nat.add_lt_add_left (Nat.lt_succ_of_lt hk) _
        _ = (s + 1) * (D + 1) := by rw [Nat.succ_mul]
        _ ≤ σ * (D + 1) := Nat.mul_le_mul_right _ hs
    rw [buffer_forms σ D _ hlt (by rw [hmod]; exact hk)]; rfl
  · calc s * (D + 1) + (k + 1) < s * (D + 1) + (D + 1) := Nat.add_lt_add_left (Nat.succ_lt_succ hk) _
      _ = (s + 1) * (D + 1) := by rw [Nat.succ_mul]
      _ ≤ σ * (D + 1) := Nat.mul_le_mul_right _ hs

/-- 29:C8 — the frame's cardinality clause of Proposition illusion at an instance: two seeds, `D = 17 > 2^4`, so
`M = 36 > 2 · 2^{3+1}` for an agent of capacity `3` over two letters — decided by the kernel. -/
theorem illusion_instance : 2 * 2 ^ (3 + 1) < (buffer 2 17).size ∧ 2 ^ (3 + 1) < 17 := by decide

/-! ### Corollary asymmetry — a check terminates, and a trace is itself a bounded record -/

/-- 29:C3 — the check of a trace in a universe under a reading is decided by exhaustive evaluation over the `t` objects
and the `t²` atoms: a completed check is a terminating computation. -/
def decPasses (T : Trace) (U : Universe) (e : Nat → Nat) : Decidable (Passes T U e) :=
  have d1 : Decidable (∀ i, i < T.t → e i < U.size) := FRC.Shell.decForallLT (fun i => e i < U.size) T.t
  have d2' : Decidable (∀ i, i < T.t → ∀ j, j < T.t → e i = e j → i = j) :=
    @FRC.Shell.decForallLT (fun i => ∀ j, j < T.t → e i = e j → i = j)
      (fun i => @FRC.Shell.decForallLT (fun j => e i = e j → i = j) (fun _ => inferInstance) T.t) T.t
  have d2 : Decidable (∀ i j, i < T.t → j < T.t → e i = e j → i = j) :=
    @decidable_of_iff _ _ ⟨fun h i j hi hj => h i hi j hj, fun h i hi j hj => h i j hi hj⟩ d2'
  have d3' : Decidable (∀ i, i < T.t → ∀ j, j < T.t → T.atom i j = true → U.form (e i) = some (e j)) :=
    @FRC.Shell.decForallLT (fun i => ∀ j, j < T.t → T.atom i j = true → U.form (e i) = some (e j))
      (fun i => @FRC.Shell.decForallLT (fun j => T.atom i j = true → U.form (e i) = some (e j)) (fun _ => inferInstance) T.t) T.t
  have d3 : Decidable (∀ i j, i < T.t → j < T.t → T.atom i j = true → U.form (e i) = some (e j)) :=
    @decidable_of_iff _ _ ⟨fun h i j hi hj => h i hi j hj, fun h i hi j hj => h i j hi hj⟩ d3'
  @instDecidableAnd _ _ d1 (@instDecidableAnd _ _ d2 d3)

/-- The entries `f 0, …, f (n − 1)` as a list. -/
def rowList (f : Nat → Bool) : Nat → List Bool
  | 0 => []
  | n + 1 => rowList f n ++ [f n]

theorem length_append (l m : List Bool) : (l ++ m).length = l.length + m.length := by
  induction l with
  | nil => show m.length = 0 + m.length; rw [Nat.zero_add]
  | cons a l ih => show (l ++ m).length + 1 = (l.length + 1) + m.length; rw [ih, Nat.succ_add]

theorem rowList_length (f : Nat → Bool) : ∀ n, (rowList f n).length = n
  | 0 => rfl
  | n + 1 => by show (rowList f n ++ [f n]).length = n + 1; rw [length_append, rowList_length f n]; rfl

/-- The atom table of a trace, row by row: the record that encodes the check. -/
def record (T : Trace) : Nat → List Bool
  | 0 => []
  | i + 1 => record T i ++ rowList (T.atom i) T.t

/-- 29:C3 — Corollary asymmetry: a trace of `t` objects is a record of `t²` symbols, a bounded structural fact has a
certifying record, retained by every agent whose capacity covers it. -/
theorem record_length (T : Trace) : ∀ i, (record T i).length = i * T.t
  | 0 => by rw [Nat.zero_mul]; rfl
  | i + 1 => by
    show (record T i ++ rowList (T.atom i) T.t).length = (i + 1) * T.t
    rw [length_append, record_length T i, rowList_length, Nat.succ_mul]

/-- 29:C3 — the record of the whole trace has `t²` symbols. -/
theorem record_square (T : Trace) : (record T T.t).length = T.t * T.t := record_length T T.t

end FRC.Formation
