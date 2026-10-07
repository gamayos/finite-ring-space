import FrcCore.Series
import FrcCore.Transform
import FrcCore.Orbit

/-!
# FrcCore.Sum — finite sums on the shell, the geometric sum, the Fourier inversion

Sums over `l < n` are defined by structural recursion (`sumRange f (n+1) = sumRange f n + f n`): no
`Finset`, no quotient, no function extensionality — a congruence lemma (`sum_congr`) replaces `funext`.
The geometric sum gives the principal-root identity (2:F1, Prop. 6.1 of 2-geometry) and the entrywise
inversion of the shell Fourier matrix `W k j = g^{jk}`: `Σ_l W k l · (−g^{−lj}) = [k = j]` (2:F3,
Prop. 6.3; 6:B5 in matrix form). No axioms.

Since the ledger migration (task LM17) it also holds 20-rh's sums: peeling the first term, and the sum over the
nonzero residues reindexed by the drive. Since task LM22 the sums that need no frame (`sumRange` and its lemmas, the
geometric sum, the sums over lists and `sum_perm`) are in `Series.lean`, under their names; this module keeps the
frame's: the principal root, the Fourier inversion, the reversal and the eigenspaces. Since task LM25 the transform
(the principal root, the inversion, `rev`, `W`, `J`, `F` and their products) is in `Transform.lean`, names unchanged,
and since task LM36 the reindexing by the drive (`sum_units_eq_sum_pow`) is there too.
-/

namespace FRC
namespace Shell

variable {p : Nat} [Pos p]

namespace Frame
variable {κ : Nat} {g : Shell p}

/-- The shell Fourier transform of `v` at `k`: `Σ_{j<n} v_j g^{jk}`. -/
def dft (g : Shell p) (n : Nat) (v : Nat → Shell p) (k : Nat) : Shell p := sumRange (fun j => v j * g ^ (j * k)) n

/-- The polynomial `P_v(x) = Σ_{j<n} v_j x^j`. -/
def polyEval (n : Nat) (v : Nat → Shell p) (x : Shell p) : Shell p := sumRange (fun j => v j * x ^ j) n

/-- 2:F4 (Prop. 6.5) — the polynomial reading: `F_g(v)_k = P_v(g^k)`. -/
theorem dft_eq_polyEval (g : Shell p) (n : Nat) (v : Nat → Shell p) (k : Nat) :
    dft g n v k = polyEval n v (g ^ k) := by
  unfold dft polyEval
  apply sum_congr; intro j _
  rw [Nat.mul_comm j k, pow_mul]

/-- The reindexing `j ↦ u·j mod n` is injective on `[0, n)` when `u` is invertible mod `n`. -/
theorem mul_mod_inj (F : Frame p κ g) {u : Nat} (hu : Coprime u (p - 1)) {i j : Nat} (hi : i < p - 1) (hj : j < p - 1)
    (h : (u * i) % (p - 1) = (u * j) % (p - 1)) : i = j := by
  have hn := F.n_pos
  match hu with
  | ⟨a, _, ha⟩ =>
    have key : ∀ i, i < p - 1 → (a * (u * i)) % (p - 1) = i := by
      intro i hi
      match FRC.Nat.mod_spec (p - 1) hn (a * u) with
      | ⟨q, hq⟩ =>
        rw [ha] at hq
        rw [← FRC.Nat.mul_assoc, hq, FRC.Nat.add_mul, Nat.one_mul, FRC.Nat.mul_assoc,
          FRC.Nat.add_mul_mod_self_left _ _ _ hn, FRC.Nat.mod_eq_of_lt hi]
    rw [← key i hi, ← key j hj, ← FRC.Nat.mul_mod_mod _ _ _ hn, h, FRC.Nat.mul_mod_mod _ _ _ hn]

/-- 2:F5 (Prop. 6.7) — covariance under generator change: for `g' = g^u` (`u` invertible mod `n`) and
`v'_j = v_{u·j mod n}`, `F_{g'}(v')_k = F_g(v)_k`. -/
theorem dft_covariance (F : Frame p κ g) {u : Nat} (hu : Coprime u (p - 1)) (v : Nat → Shell p) (k : Nat) :
    dft (g ^ u) (p - 1) (fun j => v ((u * j) % (p - 1))) k = dft g (p - 1) v k := by
  have hn := F.n_pos
  unfold dft
  have e : ∀ j, v ((u * j) % (p - 1)) * (g ^ u) ^ (j * k) = v ((u * j) % (p - 1)) * g ^ (((u * j) % (p - 1)) * k) := by
    intro j
    rw [← pow_mul, F.pow_mod (u * (j * k)), F.pow_mod (((u * j) % (p - 1)) * k), FRC.Nat.mod_mul_mod _ _ _ hn,
      ← FRC.Nat.mul_assoc]
  rw [sum_congr _ (fun j _ => e j)]
  exact sum_perm (fun l => v l * g ^ (l * k)) (fun j => (u * j) % (p - 1)) (p - 1)
    (fun j _ => Nat.mod_lt _ hn) (fun i j hi hj h => F.mul_mod_inj hu hi hj h)

/-! ### 6:B7 — the eigenspaces of the reversal: `V = V⁺ ⊕ V⁻`, `dim V⁺ = 2κ + 1`, `dim V⁻ = 2κ − 1` -/

/-- `v` is symmetric under the reversal: `v (rev k) = v k` for `k < n`. -/
def Symm (n : Nat) (v : Nat → Shell p) : Prop := ∀ k, k < n → v (rev n k) = v k

/-- `v` is antisymmetric under the reversal: `v (rev k) = −v k` for `k < n`. -/
def Antisymm (n : Nat) (v : Nat → Shell p) : Prop := ∀ k, k < n → v (rev n k) = -(v k)

theorem rev_eq_sub {n k : Nat} (hk : k < n) (hk0 : 0 < k) : rev n k = n - k := rev_of_pos hk hk0

/-- 6:B7 — a symmetric vector is determined by its `2κ + 1` coordinates `v 0, …, v (2κ)`. -/
theorem symm_determined (F : Frame p κ g) {v w : Nat → Shell p} (hv : Symm (p - 1) v) (hw : Symm (p - 1) w)
    (h : ∀ k, k ≤ 2 * κ → v k = w k) : ∀ k, k < p - 1 → v k = w k := by
  intro k hk
  exact match Nat.lt_or_ge k (2 * κ + 1) with
    | Or.inl hlt => h k (Nat.le_of_lt_succ hlt)
    | Or.inr hge =>
      -- k > 2κ: rev k = n − k ≤ 2κ − 1
      have hk0 : 0 < k := Nat.lt_of_lt_of_le (Nat.zero_lt_succ _) hge
      have hr : rev (p - 1) k ≤ 2 * κ := by
        rw [rev_eq_sub hk hk0]
        apply FRC.Nat.sub_le_of_le_add
        rw [← F.four_kappa]
        exact Nat.add_le_add_left (Nat.le_of_lt hge) _
      calc v k = v (rev (p - 1) k) := (hv k hk).symm
        _ = w (rev (p - 1) k) := h _ hr
        _ = w k := hw k hk

/-- 6:B7 — every assignment of the `2κ + 1` coordinates extends to a symmetric vector. -/
theorem symm_extend (F : Frame p κ g) (c : Nat → Shell p) :
    ∃ v : Nat → Shell p, Symm (p - 1) v ∧ ∀ k, k ≤ 2 * κ → v k = c k := by
  refine ⟨fun k => if k ≤ 2 * κ then c k else c (rev (p - 1) k), ?_, fun k hk => by
    show (if k ≤ 2 * κ then c k else c (rev (p - 1) k)) = c k
    rw [ite_eq_left hk]⟩
  intro k hk
  show (if rev (p - 1) k ≤ 2 * κ then c (rev (p - 1) k) else c (rev (p - 1) (rev (p - 1) k)))
      = (if k ≤ 2 * κ then c k else c (rev (p - 1) k))
  rw [rev_rev hk]
  exact match Nat.decLe k (2 * κ), Nat.decLe (rev (p - 1) k) (2 * κ) with
    | isTrue h1, isTrue h2 => by
        rw [ite_eq_left h1, ite_eq_left h2]
        -- both k and n − k are ≤ 2κ: k = 0 (rev 0 = 0) or k = 2κ (rev = 2κ)
        exact match Nat.decEq k 0 with
          | isTrue e => by rw [e, rev_zero _ F.n_pos]
          | isFalse e => by
              have hk0 := Nat.pos_of_ne_zero e
              rw [rev_eq_sub hk hk0] at h2 ⊢
              -- n − k ≤ 2κ and k ≤ 2κ force k = 2κ
              have h3 : p - 1 ≤ 2 * κ + k := FRC.Nat.le_add_of_sub_le (Nat.le_of_lt hk) h2
              rw [← F.four_kappa] at h3
              have hk2 : k = 2 * κ := Nat.le_antisymm h1 (FRC.Nat.le_of_add_le_add_left h3)
              rw [hk2, ← F.four_kappa, FRC.Nat.add_sub_cancel]
    | isTrue h1, isFalse h2 => by rw [ite_eq_left h1, ite_eq_right h2]
    | isFalse h1, isTrue h2 => by rw [ite_eq_right h1, ite_eq_left h2]
    | isFalse h1, isFalse h2 => by
        rw [ite_eq_right h1, ite_eq_right h2]
        -- impossible: k > 2κ and n − k > 2κ would give n > 4κ
        exact absurd (by
          have hk0 : 0 < k := Nat.lt_of_lt_of_le (Nat.zero_lt_succ _) (Nat.lt_of_not_le h1)
          rw [rev_eq_sub hk hk0] at h2
          have a1 := Nat.lt_of_not_le h1
          have a2 := Nat.lt_of_not_le h2
          have := Nat.add_lt_add a1 a2
          rw [FRC.Nat.add_sub_of_le (Nat.le_of_lt hk), F.four_kappa] at this
          exact this) (Nat.lt_irrefl _)

/-- 6:B7 — an antisymmetric vector vanishes at the two fixed points of the reversal, `0` and `2κ`. -/
theorem antisymm_fixed (F : Frame p κ g) {v : Nat → Shell p} (hv : Antisymm (p - 1) v) :
    v 0 = 0 ∧ v (2 * κ) = 0 := by
  have hn := F.n_pos
  have h0 : v 0 = -(v 0) := by rw [← hv 0 hn, rev_zero _ hn]
  have h2 : v (2 * κ) = -(v (2 * κ)) := by
    rw [← hv (2 * κ) F.two_kappa_lt, rev_eq_sub F.two_kappa_lt F.two_kappa_pos, ← F.four_kappa, FRC.Nat.add_sub_cancel]
  exact ⟨F.eq_zero_of_eq_neg h0, F.eq_zero_of_eq_neg h2⟩

/-- 6:B7 — an antisymmetric vector is determined by its `2κ − 1` coordinates `v 1, …, v (2κ − 1)`. -/
theorem antisymm_determined (F : Frame p κ g) {v w : Nat → Shell p} (hv : Antisymm (p - 1) v)
    (hw : Antisymm (p - 1) w) (h : ∀ k, 0 < k → k < 2 * κ → v k = w k) : ∀ k, k < p - 1 → v k = w k := by
  intro k hk
  exact match Nat.decEq k 0 with
    | isTrue e => by rw [e, (F.antisymm_fixed hv).1, (F.antisymm_fixed hw).1]
    | isFalse e0 => match Nat.decEq k (2 * κ) with
      | isTrue e => by rw [e, (F.antisymm_fixed hv).2, (F.antisymm_fixed hw).2]
      | isFalse e2 => match Nat.lt_or_ge k (2 * κ) with
        | Or.inl hlt => h k (Nat.pos_of_ne_zero e0) hlt
        | Or.inr hge =>
          have hgt : 2 * κ < k := Nat.lt_of_le_of_ne hge (fun e => e2 e.symm)
          have hk0 : 0 < k := Nat.lt_of_lt_of_le F.two_kappa_pos hge
          have hr1 : 0 < rev (p - 1) k := by
            rw [rev_eq_sub hk hk0]
            refine Nat.lt_of_add_lt_add_right (n := k) ?_
            rw [Nat.zero_add, FRC.Nat.sub_add_cancel (Nat.le_of_lt hk)]; exact hk
          have hr2 : rev (p - 1) k < 2 * κ := by
            rw [rev_eq_sub hk hk0]
            refine Nat.lt_of_add_lt_add_right (n := k) ?_
            rw [FRC.Nat.sub_add_cancel (Nat.le_of_lt hk), ← F.four_kappa]
            exact Nat.add_lt_add_left hgt _
          calc v k = -(-(v k)) := (neg_neg _).symm
            _ = -(v (rev (p - 1) k)) := by rw [hv k hk]
            _ = -(w (rev (p - 1) k)) := by rw [h _ hr1 hr2]
            _ = -(-(w k)) := by rw [hw k hk]
            _ = w k := neg_neg _

/-- 6:B7 — every assignment of the `2κ − 1` inner coordinates extends to an antisymmetric vector. -/
theorem antisymm_extend (F : Frame p κ g) (c : Nat → Shell p) :
    ∃ v : Nat → Shell p, Antisymm (p - 1) v ∧ ∀ k, 0 < k → k < 2 * κ → v k = c k := by
  refine ⟨fun k => if k = 0 then 0 else if k = 2 * κ then 0 else if k < 2 * κ then c k else -(c (rev (p - 1) k)),
    ?_, fun k hk0 hk2 => by
      show (if k = 0 then 0 else if k = 2 * κ then 0 else if k < 2 * κ then c k else -(c (rev (p - 1) k))) = c k
      rw [ite_eq_right (Nat.ne_of_gt hk0), ite_eq_right (Nat.ne_of_lt hk2), ite_eq_left hk2]⟩
  intro k hk
  have hn := F.n_pos
  show (if rev (p - 1) k = 0 then 0 else if rev (p - 1) k = 2 * κ then 0 else if rev (p - 1) k < 2 * κ then c (rev (p - 1) k) else -(c (rev (p - 1) (rev (p - 1) k))))
      = -(if k = 0 then 0 else if k = 2 * κ then 0 else if k < 2 * κ then c k else -(c (rev (p - 1) k)))
  match Nat.decEq k 0 with
  | isTrue e => rw [e, rev_zero _ hn, ite_eq_left rfl, ite_eq_left rfl, neg_zero]
  | isFalse e0 =>
    have hk0 := Nat.pos_of_ne_zero e0
    have hrk : rev (p - 1) k = p - 1 - k := rev_eq_sub hk hk0
    have hr0 : rev (p - 1) k ≠ 0 := fun h => by
      rw [hrk] at h
      have := FRC.Nat.sub_add_cancel (Nat.le_of_lt hk)
      rw [h, Nat.zero_add] at this
      exact Nat.lt_irrefl _ (this ▸ hk)
    match Nat.decEq k (2 * κ) with
    | isTrue e =>
      have : rev (p - 1) k = 2 * κ := by rw [hrk, e, ← F.four_kappa, FRC.Nat.add_sub_cancel]
      rw [ite_eq_right hr0, ite_eq_left this, ite_eq_right e0, ite_eq_left e, neg_zero]
    | isFalse e2 =>
      have hr2 : rev (p - 1) k ≠ 2 * κ := fun h => e2 (by
        have := rev_rev hk
        rw [h] at this
        rw [← this, rev_eq_sub F.two_kappa_lt F.two_kappa_pos, ← F.four_kappa, FRC.Nat.add_sub_cancel])
      rw [ite_eq_right hr0, ite_eq_right hr2, ite_eq_right e0, ite_eq_right e2]
      match Nat.lt_or_ge k (2 * κ) with
      | Or.inl hlt =>
        have hge : ¬ rev (p - 1) k < 2 * κ := fun h => by
          rw [hrk] at h
          have := Nat.add_lt_add h hlt
          rw [FRC.Nat.sub_add_cancel (Nat.le_of_lt hk), F.four_kappa] at this
          exact Nat.lt_irrefl _ this
        rw [ite_eq_right hge, ite_eq_left hlt, rev_rev hk]
      | Or.inr hge =>
        have hlt' : ¬ k < 2 * κ := Nat.not_lt_of_le hge
        have hgt : 2 * κ < k := Nat.lt_of_le_of_ne hge (fun e => e2 e.symm)
        have hr : rev (p - 1) k < 2 * κ := by
          rw [hrk]
          refine Nat.lt_of_add_lt_add_right (n := k) ?_
          rw [FRC.Nat.sub_add_cancel (Nat.le_of_lt hk), ← F.four_kappa]
          exact Nat.add_lt_add_left hgt _
        rw [ite_eq_left hr, ite_eq_right hlt', neg_neg]

/-- 6:B7 — the decomposition `V = V⁺ ⊕ V⁻`: with `h = 2⁻¹`, `v = v⁺ + v⁻` where `v⁺ k = h(v k + v (rev k))`
is symmetric and `v⁻ k = h(v k − v (rev k))` antisymmetric; the decomposition is unique. -/
theorem symm_antisymm_decomp (F : Frame p κ g) (v : Nat → Shell p) :
    ∃ vp vm : Nat → Shell p, Symm (p - 1) vp ∧ Antisymm (p - 1) vm ∧ ∀ k, k < p - 1 → v k = vp k + vm k := by
  match F.exists_inv F.two_ne_zero with
  | ⟨h, hh⟩ =>
    refine ⟨fun k => h * (v k + v (rev (p - 1) k)), fun k => h * (v k + -(v (rev (p - 1) k))), ?_, ?_, ?_⟩
    · intro k hk; show h * (v (rev (p - 1) k) + v (rev (p - 1) (rev (p - 1) k))) = h * (v k + v (rev (p - 1) k))
      rw [rev_rev hk, add_comm]
    · intro k hk; show h * (v (rev (p - 1) k) + -(v (rev (p - 1) (rev (p - 1) k)))) = -(h * (v k + -(v (rev (p - 1) k))))
      rw [rev_rev hk, mul_neg, neg_add_rev, neg_neg, add_comm]
    · intro k _
      show v k = h * (v k + v (rev (p - 1) k)) + h * (v k + -(v (rev (p - 1) k)))
      rw [← left_distrib, add_add_add_comm, add_neg, add_zero, ← two_mul', ← mul_assoc, mul_comm h, hh, one_mul]

/-- 6:B7 — the decomposition is unique: a vector that is both symmetric and antisymmetric is zero, so the
symmetric and antisymmetric parts of `v` are determined. -/
theorem symm_antisymm_unique (F : Frame p κ g) {a b : Nat → Shell p} (ha : Symm (p - 1) a) (hb : Antisymm (p - 1) b)
    (h : ∀ k, k < p - 1 → a k + b k = 0) : ∀ k, k < p - 1 → a k = 0 ∧ b k = 0 := by
  intro k hk
  have h1 := h k hk
  have h2 := h (rev (p - 1) k) (rev_lt F.n_pos k)
  rw [ha k hk, hb k hk] at h2
  -- a k + b k = 0 and a k − b k = 0 give 2 a k = 0
  have ha0 : a k = 0 := F.no_south_pole _ (by
    rw [two_mul']
    calc a k + a k = (a k + b k) + (a k + -(b k)) := by
          rw [add_add_add_comm, add_neg, add_zero]
      _ = 0 := by rw [h1, h2, add_zero])
  refine ⟨ha0, ?_⟩
  rw [ha0, zero_add] at h1; exact h1

end Frame

end Shell
end FRC
