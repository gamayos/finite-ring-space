import FrcCore.Theme.Diagonal

/-!
# FrcCore.Theme.Threshold — the threshold of the dense coding (the logic theme; 25-godel's migration, 20 October 2026)

What the names of the diagonal template cost, and where the count closes (25:F6, 00:Z9), with no axioms. The `k`
shortest distinct names over `a` letters cost `c(k)` symbols (`nameCost`), and `kJ + 2 ≤ c(k) + 2a^J` for every `J`
(`nameCost_lower`): a name is one symbol at least, and at most `2a^j − 2` names have `j` letters or fewer. A dense instance
with `k` coordinates in `v` and `k₁` in `u` needs `2c(k) + c(k + k₁) < d·k₁` and `3c(k) + k₁ < d·k` (`admits`, 25:F4),
which force `k < 6a^{⌊d/3⌋+1}` (`admits_bound`; `k` has at most `⌊d/3⌋ + 4` base-`a` digits, `admits_digits`),
`k < 6a^{⌊d/4⌋+1}` at one scale (`one_scale_bound`), and nothing at `d ≤ 4` (`no_instance_small_d`). The largest admitted
`k` is `k*` (`kstar`, a bounded search that misses nothing, `kstar_max`), the threshold is `t = d·k*`, no instance codes
`λ` at length `n ≥ t` (`no_instance_at_threshold`, with 25:F4's digit bound), and `t < a^{d−1} ≤ m` in every structure
(`threshold_lt`, `threshold_digits`): for `d ≥ 13` and for `a ≥ 6` by `6d·a^{⌊d/3⌋+1} ≤ a^{d−1}`, the pairs with `a ≤ 5`
and `5 ≤ d ≤ 12` by the kernel's computation of `k*`. `⌊d/3⌋` and `⌊d/4⌋` are `third` and `quarter`, by recursion.
-/

namespace FRC.Diagonal

open FRC.Logic FRC.Reach

/-! ### 25:F6 — the threshold: the names the template must spend -/

/-- `⌊d/3⌋`, by the core's recursion (no division). -/
def third : Nat → Nat
  | 0 => 0
  | 1 => 0
  | 2 => 0
  | n + 3 => third n + 1

/-- `⌊d/4⌋`, by the core's recursion. -/
def quarter : Nat → Nat
  | 0 => 0
  | 1 => 0
  | 2 => 0
  | 3 => 0
  | n + 4 => quarter n + 1

theorem third_spec : ∀ d, 3 * third d ≤ d ∧ d < 3 * third d + 3
  | 0 => by decide
  | 1 => by decide
  | 2 => by decide
  | n + 3 => by
    have ih := third_spec n
    show 3 * (third n + 1) ≤ n + 3 ∧ n + 3 < 3 * (third n + 1) + 3
    rw [Nat.mul_succ]
    exact ⟨Nat.add_le_add_right ih.1 3, Nat.add_lt_add_right ih.2 3⟩

theorem quarter_spec : ∀ d, 4 * quarter d ≤ d ∧ d < 4 * quarter d + 4
  | 0 => by decide
  | 1 => by decide
  | 2 => by decide
  | 3 => by decide
  | n + 4 => by
    have ih := quarter_spec n
    show 4 * (quarter n + 1) ≤ n + 4 ∧ n + 4 < 4 * (quarter n + 1) + 4
    rw [Nat.mul_succ]
    exact ⟨Nat.add_le_add_right ih.1 4, Nat.add_lt_add_right ih.2 4⟩

/-- The number of names of a length between `L` and `j` over `a` letters: `a^L + … + a^j` (`0` when `j < L`). -/
def namesBetween (a L : Nat) : Nat → Nat
  | 0 => 0
  | j + 1 => namesBetween a L j + (if L ≤ j + 1 then a ^ (j + 1) else 0)

theorem namesBetween_zero_of_lt (a L : Nat) : ∀ j, j < L → namesBetween a L j = 0
  | 0, _ => rfl
  | j + 1, h => by
    show namesBetween a L j + (if L ≤ j + 1 then a ^ (j + 1) else 0) = 0
    rw [namesBetween_zero_of_lt a L j (Nat.lt_of_succ_lt h), ite_eq_right (Nat.not_le_of_gt h)]

theorem namesBetween_split (a L : Nat) (hL : 1 ≤ L) : ∀ j, L ≤ j → namesBetween a L j = a ^ L + namesBetween a (L + 1) j
  | 0, h => absurd (Nat.le_trans hL h) (Nat.not_le_of_gt Nat.zero_lt_one)
  | j + 1, h => by
    show namesBetween a L j + (if L ≤ j + 1 then a ^ (j + 1) else 0)
        = a ^ L + (namesBetween a (L + 1) j + (if L + 1 ≤ j + 1 then a ^ (j + 1) else 0))
    rw [ite_eq_left h]
    match Nat.lt_or_ge j L with
    | .inl hlt =>
      have e : L = j + 1 := Nat.le_antisymm h (Nat.succ_le_of_lt hlt)
      rw [namesBetween_zero_of_lt a L j hlt, namesBetween_zero_of_lt a (L + 1) j (Nat.lt_succ_of_lt hlt),
        ite_eq_right (fun h' : L + 1 ≤ j + 1 => Nat.lt_irrefl j (Nat.lt_of_lt_of_le hlt (Nat.le_of_succ_le_succ h'))), e]
      exact (Nat.zero_add _).trans (Nat.add_zero _).symm
    | .inr hge =>
      rw [namesBetween_split a L hL j hge, ite_eq_left (Nat.succ_le_succ hge), Nat.add_assoc]

theorem pow_le_namesBetween (a L : Nat) (hL : 1 ≤ L) (j : Nat) (h : L ≤ j) : a ^ L ≤ namesBetween a L j := by
  rw [namesBetween_split a L hL j h]; exact Nat.le_add_right _ _

/-- The cost of the `k` shortest names of length at least `L`: `a^L` of them cost `L` each, the rest are longer. -/
def costFrom (a : Nat) : Nat → Nat → Nat → Nat
  | 0, _, _ => 0
  | fuel + 1, L, k => if k ≤ a ^ L then k * L else a ^ L * L + costFrom a fuel (L + 1) (k - a ^ L)

/-- The total length of the `k` shortest distinct names over `a` letters: `a` of one letter, `a²` of two, …
(25:F4's `c(k)`). -/
def nameCost (a k : Nat) : Nat := costFrom a k 1 k

theorem lt_of_mul_lt_mul_left' {a b c : Nat} (h : c * a < c * b) : a < b :=
  Nat.lt_of_not_ge (fun hge => Nat.lt_irrefl _ (Nat.lt_of_lt_of_le h (Nat.mul_le_mul_left c hge)))

theorem sub_add_eq' (k x : Nat) : ∀ y, k - (x + y) = k - x - y
  | 0 => rfl
  | y + 1 => by
    show k - (x + y + 1) = k - x - (y + 1)
    rw [Nat.sub_succ, Nat.sub_succ, sub_add_eq' k x y]

theorem le_sub_add' (k x : Nat) : k ≤ k - x + x :=
  match Nat.lt_or_ge k x with
  | .inl h => by rw [FRC.Nat.sub_eq_zero_of_le (Nat.le_of_lt h), Nat.zero_add]; exact Nat.le_of_lt h
  | .inr h => by rw [FRC.Nat.sub_add_cancel h]; exact Nat.le_refl k

theorem sumBelow_le_mul (g : Nat → Nat) (c : Nat) (h : ∀ j, g j ≤ c) : ∀ J, sumBelow g J ≤ J * c := fun J =>
  Nat.le_trans (sumBelow_le_sumBelow (fun j _ => h j)) (Nat.le_of_eq (sumBelow_const c J))

theorem sumBelow_ite_le (c L : Nat) : ∀ J, sumBelow (fun j => if j < L then c else 0) J ≤ L * c
  | 0 => Nat.zero_le _
  | J + 1 => by
    show sumBelow (fun j => if j < L then c else 0) J + (if J < L then c else 0) ≤ L * c
    match Nat.lt_or_ge J L with
    | .inl hlt =>
      rw [ite_eq_left hlt]
      have h1 : sumBelow (fun j => if j < L then c else 0) J ≤ J * c :=
        sumBelow_le_mul _ c (fun j => by split <;> first | exact Nat.le_refl c | exact Nat.zero_le c) J
      have h2 : J * c + c ≤ L * c := by rw [← Nat.succ_mul]; exact Nat.mul_le_mul_right c (Nat.succ_le_of_lt hlt)
      exact Nat.le_trans (Nat.add_le_add_right h1 c) h2
    | .inr hge =>
      rw [ite_eq_right (Nat.not_lt_of_ge hge), Nat.add_zero]; exact sumBelow_ite_le c L J

/-- The lower bound behind 25:F6 (i): the `k` shortest names of length at least `L` cost at least
`Σ_{j<J} (k − N_L(j))`, `N_L(j)` the number of such names of length at most `j` — summed over the levels `j`, each name
contributes one to every level below its length. -/
theorem costFrom_lower (a : Nat) (ha : 0 < a) :
    ∀ fuel L k J, 1 ≤ L → k ≤ fuel → sumBelow (fun j => k - namesBetween a L j) J ≤ costFrom a fuel L k
  | 0, L, k, J, _, hk => by
    have e : k = 0 := Nat.le_zero.1 hk
    subst e
    have : sumBelow (fun j => 0 - namesBetween a L j) J = sumBelow (fun _ => 0) J :=
      sumBelow_congr (fun j _ => Nat.zero_sub _)
    rw [this, sumBelow_const, Nat.mul_zero]; exact Nat.le_refl 0
  | fuel + 1, L, k, J, hL, hk => by
    show sumBelow (fun j => k - namesBetween a L j) J
        ≤ (if k ≤ a ^ L then k * L else a ^ L * L + costFrom a fuel (L + 1) (k - a ^ L))
    match Nat.lt_or_ge (a ^ L) k with
    | .inr hle =>
      rw [ite_eq_left hle]
      -- each level below L contributes k, each level from L on contributes nothing
      have hpt : ∀ j, k - namesBetween a L j ≤ (if j < L then k else 0) := fun j =>
        match Nat.lt_or_ge j L with
        | .inl hj => by rw [ite_eq_left hj]; exact Nat.sub_le k _
        | .inr hj => by
          rw [ite_eq_right (Nat.not_lt_of_ge hj)]
          exact Nat.le_of_eq (FRC.Nat.sub_eq_zero_of_le (Nat.le_trans hle (pow_le_namesBetween a L hL j hj)))
      exact Nat.le_trans (sumBelow_le_sumBelow (fun j _ => hpt j))
        (Nat.le_trans (sumBelow_ite_le k L J) (Nat.le_of_eq (Nat.mul_comm L k)))
    | .inl hlt =>
      rw [ite_eq_right (Nat.not_le_of_gt hlt)]
      have hk' : k - a ^ L ≤ fuel :=
        Nat.le_of_lt_succ (Nat.lt_of_lt_of_le (Nat.sub_lt (Nat.lt_of_le_of_lt (Nat.zero_le _) hlt) (Nat.pow_pos ha)) hk)
      have ih := costFrom_lower a ha fuel (L + 1) (k - a ^ L) J (Nat.le_succ_of_le hL) hk'
      -- pointwise: k − N_L(j) ≤ (k − a^L) − N_{L+1}(j) + (if j < L then a^L else 0)
      have hpt : ∀ j, k - namesBetween a L j
          ≤ (k - a ^ L - namesBetween a (L + 1) j) + (if j < L then a ^ L else 0) := fun j =>
        match Nat.lt_or_ge j L with
        | .inl hj => by
          rw [ite_eq_left hj, namesBetween_zero_of_lt a L j hj, namesBetween_zero_of_lt a (L + 1) j (Nat.lt_succ_of_lt hj),
            Nat.sub_zero, Nat.sub_zero, FRC.Nat.sub_add_cancel (Nat.le_of_lt hlt)]
          exact Nat.le_refl k
        | .inr hj => by
          rw [ite_eq_right (Nat.not_lt_of_ge hj), Nat.add_zero, namesBetween_split a L hL j hj, sub_add_eq']
          exact Nat.le_refl _
      have hsum := sumBelow_le_sumBelow (R := J) (fun j _ => hpt j)
      rw [sumBelow_add] at hsum
      exact Nat.le_trans hsum (Nat.le_trans (Nat.add_le_add ih (sumBelow_ite_le (a ^ L) L J))
        (Nat.le_of_eq (by rw [Nat.add_comm, Nat.mul_comm])))

/-- `N(j) = a + … + a^j`, the names of length at most `j`, number at most `2a^j − 2` for `a ≥ 2`. -/
theorem namesBetween_one_le (a : Nat) (ha : 2 ≤ a) : ∀ j, namesBetween a 1 j + 2 ≤ 2 * a ^ j
  | 0 => show 0 + 2 ≤ 2 * 1 from Nat.le_refl 2
  | j + 1 => by
    show namesBetween a 1 j + (if 1 ≤ j + 1 then a ^ (j + 1) else 0) + 2 ≤ 2 * a ^ (j + 1)
    rw [ite_eq_left (Nat.succ_le_succ (Nat.zero_le j))]
    have ih := namesBetween_one_le a ha j
    have h2 : 2 * a ^ j ≤ a ^ (j + 1) := by rw [Nat.pow_succ, Nat.mul_comm (a ^ j) a]; exact Nat.mul_le_mul_right _ ha
    have : namesBetween a 1 j + a ^ (j + 1) + 2 = (namesBetween a 1 j + 2) + a ^ (j + 1) := by
      rw [Nat.add_right_comm]
    rw [this, Nat.two_mul]
    exact Nat.add_le_add (Nat.le_trans ih h2) (Nat.le_refl _)

/-- `Σ_{j<J} N(j) ≤ 2a^J − 2` for `a ≥ 2`. -/
theorem sumBelow_namesBetween_le (a : Nat) (ha : 2 ≤ a) : ∀ J, sumBelow (namesBetween a 1) J + 2 ≤ 2 * a ^ J
  | 0 => show 0 + 2 ≤ 2 * 1 from Nat.le_refl 2
  | J + 1 => by
    show sumBelow (namesBetween a 1) J + namesBetween a 1 J + 2 ≤ 2 * a ^ (J + 1)
    have ih := sumBelow_namesBetween_le a ha J
    have hN := namesBetween_one_le a ha J
    have h2 : 2 * a ^ J ≤ a ^ (J + 1) := by
      rw [Nat.pow_succ, Nat.mul_comm (a ^ J) a]; exact Nat.mul_le_mul_right _ ha
    have h4 : 2 * a ^ J + 2 * a ^ J ≤ 2 * a ^ (J + 1) := by
      rw [← Nat.two_mul]; exact Nat.mul_le_mul_left 2 h2
    have : sumBelow (namesBetween a 1) J + namesBetween a 1 J + 2
        = (sumBelow (namesBetween a 1) J + 2) + namesBetween a 1 J := by rw [Nat.add_right_comm]
    rw [this]
    exact Nat.le_trans (Nat.add_le_add ih (Nat.le_trans (Nat.le_add_right _ 2) hN)) h4

/-- 25:F6 (i), 00:Z9 — the name-cost bound: for every `J`, `kJ + 2 ≤ c(k) + 2a^J`: the `k` shortest names cannot all be
short. -/
theorem nameCost_lower (a : Nat) (ha : 2 ≤ a) (k J : Nat) : k * J + 2 ≤ nameCost a k + 2 * a ^ J := by
  have h1 : sumBelow (fun j => k - namesBetween a 1 j) J ≤ nameCost a k :=
    costFrom_lower a (Nat.lt_of_lt_of_le Nat.zero_lt_two ha) k 1 k J (Nat.le_refl 1) (Nat.le_refl k)
  have h2 : sumBelow (fun _ => k) J ≤ sumBelow (fun j => k - namesBetween a 1 j) J + sumBelow (namesBetween a 1) J := by
    rw [← sumBelow_add]; exact sumBelow_le_sumBelow (fun j _ => le_sub_add' k _)
  rw [sumBelow_const, Nat.mul_comm] at h2
  have h3 := sumBelow_namesBetween_le a ha J
  calc k * J + 2 ≤ sumBelow (fun j => k - namesBetween a 1 j) J + sumBelow (namesBetween a 1) J + 2 :=
        Nat.add_le_add_right h2 2
    _ = sumBelow (fun j => k - namesBetween a 1 j) J + (sumBelow (namesBetween a 1) J + 2) := Nat.add_assoc _ _ _
    _ ≤ nameCost a k + 2 * a ^ J := Nat.add_le_add h1 h3

/-- Every name has at least one letter: `c(k) ≥ k`. -/
theorem le_nameCost (a : Nat) (ha : 0 < a) (k : Nat) : k ≤ nameCost a k := by
  have h := costFrom_lower a ha k 1 k 1 (Nat.le_refl 1) (Nat.le_refl k)
  show k ≤ costFrom a k 1 k
  have e : sumBelow (fun j => k - namesBetween a 1 j) 1 = k := by
    show 0 + (k - 0) = k; rw [Nat.sub_zero, Nat.zero_add]
  rw [e] at h; exact h

/-- The least total length of the variable names in `δ(u) = ∃ v (Diag(u, v) ∧ θ(v))`: each coordinate of `v` named three
times, each of `u` once, the weight on the shortest names (25:F4). -/
def deltaNames (a k k₁ : Nat) : Nat := 2 * nameCost a k + nameCost a (k + k₁)

/-- The least number of symbols the coordinates cost in `λ = δ(⌜δ⌝)`: each coordinate of `v` three times and a closed term
of at least one symbol in each place of `u` (25:F4). -/
def lambdaNames (a k k₁ : Nat) : Nat := 3 * nameCost a k + k₁

/-- The name count leaves an instance open: `λ`'s symbols fit a code of `k` coordinates and `δ`'s a code of `k₁`, a tuple
of `j` coordinates over a structure of `d` digits holding fewer than `d·j` letters. -/
def admits (a d k k₁ : Nat) : Bool :=
  decide (lambdaNames a k k₁ < d * k) && decide (deltaNames a k k₁ < d * k₁)

theorem admits_lambda {a d k k₁ : Nat} (h : admits a d k k₁ = true) : 3 * nameCost a k + k₁ < d * k :=
  of_decide_eq_true (band_l h)

theorem admits_delta {a d k k₁ : Nat} (h : admits a d k k₁ = true) : 2 * nameCost a k + nameCost a (k + k₁) < d * k₁ :=
  of_decide_eq_true (band_r h)

theorem mul3_add_two {x y z : Nat} (h : x + 2 ≤ y + 2 * z) : 3 * x + 6 ≤ 3 * y + 6 * z := by
  have := Nat.mul_le_mul_left 3 h
  rw [Nat.mul_add, Nat.mul_add, ← FRC.Nat.mul_assoc] at this
  exact this

theorem mul2_add_two {x y z : Nat} (h : x + 2 ≤ y + 2 * z) : 2 * x + 4 ≤ 2 * y + 4 * z := by
  have := Nat.mul_le_mul_left 2 h
  rw [Nat.mul_add, Nat.mul_add, ← FRC.Nat.mul_assoc] at this
  exact this

theorem add_self_mul (k J : Nat) : (k + k) * J = 2 * (k * J) := by rw [FRC.Nat.add_mul, Nat.two_mul]

theorem two_add_two_add (x : Nat) : 2 * x + 4 + (2 * x + 2) = 4 * x + 6 := by
  rw [Nat.add_assoc, Nat.add_left_comm 4, ← Nat.add_assoc, ← Nat.two_mul, ← FRC.Nat.mul_assoc]

theorem add_four_add_two (y z w : Nat) : y + 4 * w + (z + 2 * w) = y + z + 6 * w := by
  rw [Nat.add_assoc, Nat.add_left_comm (4 * w), ← Nat.add_assoc, ← FRC.Nat.add_mul]

/-- 25:F6 (the bound), 00:Z9 — an admitted instance has `k < 6a^{⌊d/3⌋+1}`: from `3c(k) < dk` and the name-cost bound at
`J = ⌊d/3⌋ + 1`, where `3J ≥ d + 1`. -/
theorem admits_bound {a d k k₁ : Nat} (ha : 2 ≤ a) (h : admits a d k k₁ = true) : k < 6 * a ^ (third d + 1) := by
  have h3 : 3 * nameCost a k < d * k := Nat.lt_of_le_of_lt (Nat.le_add_right _ k₁) (admits_lambda h)
  have hJ : d + 1 ≤ 3 * (third d + 1) := by rw [Nat.mul_succ]; exact (third_spec d).2
  have h4 := mul3_add_two (nameCost_lower a ha k (third d + 1))
  have h5 : d * k + k ≤ 3 * (k * (third d + 1)) := by
    have := Nat.mul_le_mul_left k hJ
    rw [Nat.mul_succ, FRC.Nat.mul_left_comm, Nat.mul_comm k d] at this
    exact this
  have h6 : d * k + (k + 6) < d * k + 6 * a ^ (third d + 1) := by
    rw [← Nat.add_assoc]
    exact Nat.lt_of_le_of_lt (Nat.le_trans (Nat.add_le_add_right h5 6) h4) (Nat.add_lt_add_right h3 _)
  exact Nat.lt_of_le_of_lt (Nat.le_add_right k 6) (Nat.lt_of_add_lt_add_left h6)

/-- 25:F6 (the digit form), 00:Z9 — an admitted `k` has at most `⌊d/3⌋ + 4` base-`a` digits: `6a^J < a^{J+3}`. -/
theorem admits_digits {a d k k₁ : Nat} (ha : 2 ≤ a) (h : admits a d k k₁ = true) : k < a ^ (third d + 4) := by
  have h1 := admits_bound ha h
  have h2 : 6 * a ^ (third d + 1) < 8 * a ^ (third d + 1) :=
    FRC.Nat.mul_lt_mul_of_lt_of_pos (by decide) (Nat.pow_pos (Nat.lt_of_lt_of_le Nat.zero_lt_two ha))
  have h3 : 8 * a ^ (third d + 1) ≤ a ^ 3 * a ^ (third d + 1) :=
    Nat.mul_le_mul_right _ (Nat.pow_le_pow_left ha 3)
  have e : a ^ 3 * a ^ (third d + 1) = a ^ (third d + 4) := by
    rw [← FRC.Nat.pow_add, Nat.add_comm 3]
  exact Nat.lt_of_lt_of_le h1 (Nat.le_trans (Nat.le_of_lt h2) (e ▸ h3))

/-- 25:F6 (one scale) — with `k₁ = k` the count `2c(k) + c(2k) < dk` forces `k < 6a^{⌊d/4⌋+1}`. -/
theorem one_scale_bound {a d k : Nat} (ha : 2 ≤ a) (h : admits a d k k = true) : k < 6 * a ^ (quarter d + 1) := by
  have hdel : 2 * nameCost a k + nameCost a (k + k) < d * k := admits_delta h
  have hJ : d + 1 ≤ 4 * (quarter d + 1) := by rw [Nat.mul_succ]; exact (quarter_spec d).2
  have b1 := mul2_add_two (nameCost_lower a ha k (quarter d + 1))
  have b2 := nameCost_lower a ha (k + k) (quarter d + 1)
  rw [add_self_mul] at b2
  have h4 : 4 * (k * (quarter d + 1)) + 6 ≤ 2 * nameCost a k + nameCost a (k + k) + 6 * a ^ (quarter d + 1) := by
    have := Nat.add_le_add b1 b2
    rw [two_add_two_add, add_four_add_two] at this
    exact this
  have h5 : d * k + k ≤ 4 * (k * (quarter d + 1)) := by
    have := Nat.mul_le_mul_left k hJ
    rw [Nat.mul_succ, FRC.Nat.mul_left_comm, Nat.mul_comm k d] at this
    exact this
  have h6 : d * k + (k + 6) < d * k + 6 * a ^ (quarter d + 1) := by
    rw [← Nat.add_assoc]
    exact Nat.lt_of_le_of_lt (Nat.le_trans (Nat.add_le_add_right h5 6) h4) (Nat.add_lt_add_right hdel _)
  exact Nat.lt_of_le_of_lt (Nat.le_add_right k 6) (Nat.lt_of_add_lt_add_left h6)

/-- 25:F6 (small `d`) — for `d ≤ 4` no instance is admitted: `c(j) ≥ j` gives `k₁ < k` from `λ`'s count and `k < k₁`
from `δ`'s. -/
theorem no_instance_small_d {a d k k₁ : Nat} (ha : 0 < a) (hd : d ≤ 4) : admits a d k k₁ = false := by
  match h : admits a d k k₁ with
  | false => rfl
  | true =>
    exfalso
    have hlam := admits_lambda h
    have hdel := admits_delta h
    have c1 := le_nameCost a ha k
    have c2 := le_nameCost a ha (k + k₁)
    have h1 : 3 * k + k₁ < 4 * k :=
      Nat.lt_of_le_of_lt (Nat.add_le_add_right (Nat.mul_le_mul_left 3 c1) k₁)
        (Nat.lt_of_lt_of_le hlam (Nat.mul_le_mul_right k hd))
    have h2 : 3 * k + k₁ < 4 * k₁ := by
      have : 3 * k + k₁ ≤ 2 * nameCost a k + nameCost a (k + k₁) := by
        have e : 3 * k + k₁ = 2 * k + (k + k₁) := by
          rw [Nat.succ_mul 2 k, Nat.add_assoc]
        rw [e]; exact Nat.add_le_add (Nat.mul_le_mul_left 2 c1) c2
      exact Nat.lt_of_le_of_lt this (Nat.lt_of_lt_of_le hdel (Nat.mul_le_mul_right k₁ hd))
    -- k₁ < k from h1 and k < k₁ from h2
    have hk₁ : k₁ < k := by
      rw [Nat.succ_mul 3 k] at h1
      exact Nat.lt_of_add_lt_add_left h1
    have hk : k < k₁ := by
      rw [Nat.succ_mul 3 k₁, Nat.add_comm (3 * k₁) k₁, Nat.add_comm (3 * k) k₁] at h2
      exact lt_of_mul_lt_mul_left' (Nat.lt_of_add_lt_add_left h2)
    exact Nat.lt_irrefl k (Nat.lt_trans hk hk₁)

/-- Whether some `k₁` admits `k`: by `λ`'s count `k₁ < dk − 3c(k)`, so the search runs below that bound. -/
def admitsSome (a d k : Nat) : Bool := anyBelow (fun k₁ => admits a d k k₁) (d * k - 3 * nameCost a k)

theorem admitsSome_of {a d k k₁ : Nat} (h : admits a d k k₁ = true) : admitsSome a d k = true := by
  have hlam := admits_lambda h
  have hlt : k₁ < d * k - 3 * nameCost a k := by
    have h3 : 3 * nameCost a k ≤ d * k := Nat.le_of_lt (Nat.lt_of_le_of_lt (Nat.le_add_right _ k₁) hlam)
    have e := FRC.Nat.sub_add_cancel h3
    rw [← e, Nat.add_comm] at hlam
    exact Nat.lt_of_add_lt_add_right hlam
  exact (anyBelow_true_iff _ _).2 ⟨k₁, hlt, h⟩

/-- The largest `i < n` with `P i`, or `0` if there is none. -/
def largestBelow (P : Nat → Bool) : Nat → Nat
  | 0 => 0
  | n + 1 => if P n then n else largestBelow P n

theorem le_largestBelow (P : Nat → Bool) {i : Nat} (hi : P i = true) : ∀ n, i < n → i ≤ largestBelow P n
  | 0, h => absurd h (Nat.not_lt_zero i)
  | n + 1, h => by
    show i ≤ (if P n then n else largestBelow P n)
    match hP : P n with
    | true => rw [ite_eq_left rfl]; exact Nat.le_of_lt_succ h
    | false =>
      rw [ite_eq_right (by decide : ¬ (false = true))]
      have hne : i ≠ n := fun e => Bool.noConfusion (hi.symm.trans (e ▸ hP))
      exact le_largestBelow P hi n (Nat.lt_of_le_of_ne (Nat.le_of_lt_succ h) hne)

theorem largestBelow_lt (P : Nat → Bool) : ∀ n, 0 < n → largestBelow P n < n
  | 0, h => absurd h (Nat.lt_irrefl 0)
  | n + 1, _ => by
    show (if P n then n else largestBelow P n) < n + 1
    match hP : P n with
    | true => rw [ite_eq_left rfl]; exact Nat.lt_succ_self n
    | false =>
      rw [ite_eq_right (by decide : ¬ (false = true))]
      match n with
      | 0 => exact Nat.zero_lt_one
      | n + 1 => exact Nat.lt_succ_of_lt (largestBelow_lt P (n + 1) (Nat.succ_pos n))

theorem largestBelow_eq_zero (P : Nat → Bool) : ∀ n, (∀ i, i < n → P i = false) → largestBelow P n = 0
  | 0, _ => rfl
  | n + 1, h => by
    show (if P n then n else largestBelow P n) = 0
    rw [h n (Nat.lt_succ_self n), ite_eq_right (by decide : ¬ (false = true))]
    exact largestBelow_eq_zero P n (fun i hi => h i (Nat.lt_succ_of_lt hi))

/-- `k*(M)`: the largest `k` some `k₁` admits, searched below the bound `6a^{⌊d/3⌋+1}` (25:F6). -/
def kstar (a d : Nat) : Nat := largestBelow (admitsSome a d) (6 * a ^ (third d + 1))

/-- `t(M) = d · k*(M)`, the threshold length (25:F6). -/
def threshold (a d : Nat) : Nat := d * kstar a d

/-- 25:F6, 00:Z9 — the search misses nothing: every admitted `k` is at most `k*`. -/
theorem kstar_max {a d k k₁ : Nat} (ha : 2 ≤ a) (h : admits a d k k₁ = true) : k ≤ kstar a d :=
  le_largestBelow (admitsSome a d) (admitsSome_of h) _ (admits_bound ha h)

/-- 25:F6 — `k*(M) < 6a^{⌊d/3⌋+1}`, as the row states it. -/
theorem kstar_lt {a d : Nat} (ha : 1 ≤ a) : kstar a d < 6 * a ^ (third d + 1) :=
  largestBelow_lt _ _ (Nat.mul_pos (by decide) (Nat.pow_pos ha))

/-- 25:F6, 00:Z9 (the digit form) — `k*(M)` has at most `⌊d/3⌋ + 4` base-`a` digits. -/
theorem kstar_digits {a d : Nat} (ha : 2 ≤ a) : kstar a d < a ^ (third d + 4) := by
  have h2 : 6 * a ^ (third d + 1) < 8 * a ^ (third d + 1) :=
    FRC.Nat.mul_lt_mul_of_lt_of_pos (by decide) (Nat.pow_pos (Nat.lt_of_lt_of_le Nat.zero_lt_two ha))
  have h3 : 8 * a ^ (third d + 1) ≤ a ^ 3 * a ^ (third d + 1) :=
    Nat.mul_le_mul_right _ (Nat.pow_le_pow_left ha 3)
  have e : a ^ 3 * a ^ (third d + 1) = a ^ (third d + 4) := by rw [← FRC.Nat.pow_add, Nat.add_comm 3]
  exact Nat.lt_of_lt_of_le (kstar_lt (Nat.le_of_lt ha)) (Nat.le_trans (Nat.le_of_lt h2) (e ▸ h3))

/-- 25:F6 (ii), 00:Z9 — no instance codes `λ` at length `n ≥ t(M)`: with `k + 1` coordinates in `v` admitted and the
coding injective (`a^n ≤ m^(k+1)`, 25:F4) over a structure of `d` digits, `n < d(k + 1) ≤ d·k* = t(M)`. -/
theorem no_instance_at_threshold {a d k k₁ m n : Nat} (ha : 2 ≤ a) (h : admits a d (k + 1) k₁ = true)
    (hm : m < a ^ d) (hc : a ^ n ≤ m ^ (k + 1)) : n < threshold a d :=
  Nat.lt_of_lt_of_le (digit_bound (Nat.lt_of_lt_of_le Nat.zero_lt_two ha) hm hc)
    (Nat.mul_le_mul_left d (kstar_max ha h))

/-- For `d ≤ 4` the threshold is `0`: nothing is admitted. -/
theorem threshold_small_d {a d : Nat} (ha : 0 < a) (hd : d ≤ 4) : threshold a d = 0 := by
  show d * largestBelow (admitsSome a d) _ = 0
  rw [largestBelow_eq_zero (admitsSome a d) _ (fun k _ => by
    show anyBelow (fun k₁ => admits a d k k₁) _ = false
    rw [anyBelow_congr (fun k₁ _ => no_instance_small_d ha hd)]; exact anyBelow_false _), Nat.mul_zero]

theorem coef_pow_le {a : Nat} (ha : 2 ≤ a) (c e J : Nat) (hc : c ≤ 2 ^ e) : c * a ^ J ≤ a ^ (e + J) := by
  rw [FRC.Nat.pow_add]; exact Nat.mul_le_mul_right _ (Nat.le_trans hc (Nat.pow_le_pow_left ha e))

theorem coef_pow_le6 {a : Nat} (ha : 6 ≤ a) (c e J : Nat) (hc : c ≤ 6 ^ e) : c * a ^ J ≤ a ^ (e + J) := by
  rw [FRC.Nat.pow_add]; exact Nat.mul_le_mul_right _ (Nat.le_trans hc (Nat.pow_le_pow_left ha e))

theorem rearr4 (x y z : Nat) : 4 * x * (y * z) = x * y * (4 * z) := by
  rw [FRC.Nat.mul_assoc, FRC.Nat.mul_left_comm, FRC.Nat.mul_left_comm 4 y, ← FRC.Nat.mul_assoc]

/-- The step `d → d + 3` of the bound `6d·a^{⌊d/3⌋+1} ≤ a^{d−1}`: the left side gains at most the factor `4a`, the right
side `a³`. -/
theorem six_d_pow_step {a : Nat} (ha : 2 ≤ a) (d : Nat) (hd : 1 ≤ d)
    (h : 6 * d * a ^ (third d + 1) ≤ a ^ (d - 1)) : 6 * (d + 3) * a ^ (third (d + 3) + 1) ≤ a ^ (d + 2) := by
  have e3 : third (d + 3) + 1 = third d + 1 + 1 := rfl
  rw [e3]
  have h1 : 6 * (d + 3) ≤ 4 * (6 * d) := by
    have e1 : 6 * (d + 3) = 6 * d + 18 := by rw [Nat.mul_add]
    have e2 : 4 * (6 * d) = 6 * d + 18 * d := by rw [← FRC.Nat.mul_assoc, ← FRC.Nat.add_mul]
    rw [e1, e2]
    exact Nat.add_le_add_left (Nat.le_mul_of_pos_right 18 hd) _
  have h4 : 4 ≤ a ^ 2 := Nat.pow_le_pow_left ha 2
  have hpow : a ^ (third d + 1 + 1) = a ^ (third d + 1) * a := rfl
  have hd2 : a ^ (d + 2) = a ^ (d - 1) * (a ^ 2 * a) := by
    have e : d - 1 + 3 = d + 2 := congrArg (· + 2) (FRC.Nat.sub_add_cancel hd)
    rw [← e, FRC.Nat.pow_add]; rfl
  rw [hpow, hd2]
  calc 6 * (d + 3) * (a ^ (third d + 1) * a)
      ≤ 4 * (6 * d) * (a ^ (third d + 1) * a) := Nat.mul_le_mul_right _ h1
    _ = 6 * d * a ^ (third d + 1) * (4 * a) := rearr4 _ _ _
    _ ≤ a ^ (d - 1) * (a ^ 2 * a) := Nat.mul_le_mul h (Nat.mul_le_mul_right a h4)

/-- `6d·a^{⌊d/3⌋+1} ≤ a^{d−1}` for every `d ≥ 13` and `a ≥ 2`: the cases `13`, `14`, `15` and the step. -/
theorem six_d_pow_le_large {a : Nat} (ha : 2 ≤ a) :
    ∀ n, 6 * (13 + n) * a ^ (third (13 + n) + 1) ≤ a ^ (12 + n) := by
  have base0 : 6 * (13 + 0) * a ^ (third (13 + 0) + 1) ≤ a ^ (12 + 0) := coef_pow_le ha 78 7 5 (by decide)
  have base1 : 6 * (13 + 1) * a ^ (third (13 + 1) + 1) ≤ a ^ (12 + 1) := coef_pow_le ha 84 8 5 (by decide)
  have base2 : 6 * (13 + 2) * a ^ (third (13 + 2) + 1) ≤ a ^ (12 + 2) := coef_pow_le ha 90 8 6 (by decide)
  have step : ∀ n, 6 * (13 + n) * a ^ (third (13 + n) + 1) ≤ a ^ (12 + n)
      → 6 * (13 + (n + 3)) * a ^ (third (13 + (n + 3)) + 1) ≤ a ^ (12 + (n + 3)) := fun n h => by
    have e1 : 13 + n - 1 = 12 + n := by
      rw [Nat.add_comm 13 n, Nat.add_comm 12 n]; exact FRC.Nat.add_sub_cancel (n + 12) 1
    have h' : 6 * (13 + n) * a ^ (third (13 + n) + 1) ≤ a ^ (13 + n - 1) := by rw [e1]; exact h
    have := six_d_pow_step ha (13 + n) (Nat.le_add_right_of_le (by decide)) h'
    have e2 : 13 + (n + 3) = 13 + n + 3 := (Nat.add_assoc 13 n 3).symm
    have e3 : 12 + (n + 3) = 13 + n + 2 := by
      rw [Nat.add_comm n 3, ← Nat.add_assoc, Nat.add_assoc 13 n 2, Nat.add_comm n 2, ← Nat.add_assoc]
    rw [e2, e3]; exact this
  have all : ∀ n, (6 * (13 + n) * a ^ (third (13 + n) + 1) ≤ a ^ (12 + n)) ∧
      (6 * (13 + (n + 1)) * a ^ (third (13 + (n + 1)) + 1) ≤ a ^ (12 + (n + 1))) ∧
      (6 * (13 + (n + 2)) * a ^ (third (13 + (n + 2)) + 1) ≤ a ^ (12 + (n + 2))) := fun n => by
    induction n with
    | zero => exact ⟨base0, base1, base2⟩
    | succ n ih => exact ⟨ih.2.1, ih.2.2, step n ih.1⟩
  exact fun n => (all n).1

/-- `6d·a^{⌊d/3⌋+1} ≤ a^{d−1}` for `5 ≤ d ≤ 12` and `a ≥ 6`, each `d` by one bound `6d ≤ 6^{d−1−J}`. -/
theorem six_d_pow_le_mid {a : Nat} (ha : 6 ≤ a) (d : Nat) (h5 : 5 ≤ d) (h12 : d ≤ 12) :
    6 * d * a ^ (third d + 1) ≤ a ^ (d - 1) :=
  match d, h5, h12 with
  | 5, _, _ => coef_pow_le6 ha 30 2 2 (by decide)
  | 6, _, _ => coef_pow_le6 ha 36 2 3 (by decide)
  | 7, _, _ => coef_pow_le6 ha 42 3 3 (by decide)
  | 8, _, _ => coef_pow_le6 ha 48 4 3 (by decide)
  | 9, _, _ => coef_pow_le6 ha 54 4 4 (by decide)
  | 10, _, _ => coef_pow_le6 ha 60 5 4 (by decide)
  | 11, _, _ => coef_pow_le6 ha 66 6 4 (by decide)
  | 12, _, _ => coef_pow_le6 ha 72 6 5 (by decide)
  | 0, h, _ => absurd h (by decide)
  | 1, h, _ => absurd h (by decide)
  | 2, h, _ => absurd h (by decide)
  | 3, h, _ => absurd h (by decide)
  | 4, h, _ => absurd h (by decide)
  | n + 13, _, h => absurd h (Nat.not_le_of_gt (Nat.lt_of_lt_of_le (by decide) (Nat.le_add_left 13 n)))

/-- The pairs `(a, d)` with `a ≤ 5` and `5 ≤ d ≤ 12`: either the bound `6d·a^{⌊d/3⌋+1} ≤ a^{d−1}` holds or the kernel
computes `k*` and finds `t < a^{d−1}` — the fifteen pairs of the row's check D5, decided here. -/
theorem threshold_small_pairs : ∀ a, a < 6 → ∀ d, d < 13 → 2 ≤ a → 5 ≤ d →
    (6 * d * a ^ (third d + 1) ≤ a ^ (d - 1) ∨ threshold a d < a ^ (d - 1)) := by
  decide +kernel

/-- 25:F6 (iii), 25:G7, 00:Z9 — `t(M) < m` in every structure: `m` has `d` base-`a` digits (`a^{d−1} ≤ m`), and the threshold
`d·k*` has fewer: `k* < 6a^{⌊d/3⌋+1}` and `6d·a^{⌊d/3⌋+1} ≤ a^{d−1}` from `d = 13` on and for `a ≥ 6`, the small pairs
computed, nothing admitted at `d ≤ 4`. -/
theorem threshold_lt {a d m : Nat} (ha : 2 ≤ a) (hm : a ^ (d - 1) ≤ m) : threshold a d < m := by
  have ha1 : 0 < a := Nat.lt_of_lt_of_le Nat.zero_lt_two ha
  have hpos : 0 < m := Nat.lt_of_lt_of_le (Nat.pow_pos ha1) hm
  have viaG : 0 < d → 6 * d * a ^ (third d + 1) ≤ a ^ (d - 1) → threshold a d < m := fun hd hG => by
    show d * kstar a d < m
    have h1 : d * kstar a d < d * (6 * a ^ (third d + 1)) := Nat.mul_lt_mul_of_pos_left (kstar_lt ha1) hd
    have e : d * (6 * a ^ (third d + 1)) = 6 * d * a ^ (third d + 1) := by
      rw [FRC.Nat.mul_left_comm, ← FRC.Nat.mul_assoc]
    exact Nat.lt_of_lt_of_le h1 (Nat.le_trans (e ▸ hG) hm)
  match Nat.lt_or_ge d 5 with
  | .inl hd4 => rw [threshold_small_d ha1 (Nat.le_of_lt_succ hd4)]; exact hpos
  | .inr hd5 =>
    have hd : 0 < d := Nat.lt_of_lt_of_le (by decide) hd5
    match Nat.lt_or_ge d 13 with
    | .inr hd13 =>
      have hG := six_d_pow_le_large ha (d - 13)
      have e1 : 13 + (d - 13) = d := FRC.Nat.add_sub_of_le hd13
      have e2 : 12 + (d - 13) = d - 1 := by
        have h := congrArg (· - 1) e1
        have e : 13 + (d - 13) - 1 = 12 + (d - 13) := by
          rw [show 13 + (d - 13) = 12 + (d - 13) + 1 from (Nat.add_right_comm 12 (d - 13) 1).symm]
          exact FRC.Nat.add_sub_cancel _ 1
        rw [← e]; exact h
      rw [e1, e2] at hG
      exact viaG hd hG
    | .inl hd13 =>
      match Nat.lt_or_ge a 6 with
      | .inr ha6 => exact viaG hd (six_d_pow_le_mid ha6 d hd5 (Nat.le_of_lt_succ hd13))
      | .inl ha6 =>
        match threshold_small_pairs a ha6 d hd13 ha hd5 with
        | .inl hG => exact viaG hd hG
        | .inr hlt => exact Nat.lt_of_lt_of_le hlt hm

/-- 25:F6 (iii), 00:Z9, the digit form — the threshold has fewer base-`a` digits than `m`: `t(M) < a^{d−1}`. -/
theorem threshold_digits {a d : Nat} (ha : 2 ≤ a) : threshold a d < a ^ (d - 1) :=
  threshold_lt ha (Nat.le_refl _)

end FRC.Diagonal
