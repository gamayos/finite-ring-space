import FrcCore.Theme.Heisenberg
import FrcCore.Theme.Dichotomy

/-!
# FrcCore.Theme.Spectra — the spectra of the shift and of the family: the obstruction (the fourier theme)

The seventh file of the fourier theme (6-fourier's blueprint of 8 October 2026, task T08). Vectors on the cycle are
`Nat → Shell p` and a matrix acts by `(A v)_k = Σ_{l<n} A_{kl} v_l`. The shift `σ` has every nonzero residue as an
eigenvalue, with the geometric vector `(y^j)_j` for `b = y⁻¹` (Fermat: `y^n = 1`); an eigenvalue of `F^{[s]}` is one
of the four `(z^s)^ℓ`, since `Π_m F^{[s]} = (z^s)^m Π_m` and `v = Σ_m Π_m v` (6:E9). So no invertible `T` has
`T σ T⁻¹ = F^{[s]}` for `κ ≥ 2`: the `4κ` eigenvalues of `σ` would be eigenvalues of `F^{[s]}`, at most four, and
`no_mirror` refuses the injection of `[0, 4κ)` into `[0, 4)` (6:E5). No axioms.
-/

namespace FRC
namespace Shell
namespace Frame

variable {p : Nat} [Pos p]

/-! ## Vectors and matrices on the cycle -/

/-- `(A v)_k = Σ_{l<n} A_{kl} v_l`. -/
def act (A : Nat → Nat → Shell p) (v : Nat → Shell p) (n k : Nat) : Shell p := sumRange (fun l => A k l * v l) n

/-- `(A B)_{kj} = Σ_{l<n} A_{kl} B_{lj}`. -/
def mmul (A B : Nat → Nat → Shell p) (n k j : Nat) : Shell p := sumRange (fun l => A k l * B l j) n

/-- `v` is an eigenvector of `A` for the eigenvalue `lam`: nonzero on the cycle, with `A v = lam v` there. -/
def IsEigen (A : Nat → Nat → Shell p) (n : Nat) (lam : Shell p) (v : Nat → Shell p) : Prop :=
  (∃ k, k < n ∧ v k ≠ 0) ∧ ∀ k, k < n → act A v n k = lam * v k

/-- `(A B) v = A (B v)`. -/
theorem act_mmul (A B : Nat → Nat → Shell p) (v : Nat → Shell p) (n k : Nat) :
    act (mmul A B n) v n k = act A (act B v n) n k := by
  show sumRange (fun j => sumRange (fun l => A k l * B l j) n * v j) n =
    sumRange (fun l => A k l * sumRange (fun j => B l j * v j) n) n
  rw [sum_congr _ (fun j _ => (sum_mul_right _ _ _).symm), sum_swap (fun j l => A k l * B l j * v j) n n]
  exact sum_congr _ (fun l _ => by
    rw [← sum_mul_left]
    exact sum_congr _ (fun j _ => mul_assoc _ _ _))

theorem act_smul (A : Nat → Nat → Shell p) (v : Nat → Shell p) (c : Shell p) (n k : Nat) :
    act A (fun l => c * v l) n k = c * act A v n k := by
  show sumRange (fun l => A k l * (c * v l)) n = c * sumRange (fun l => A k l * v l) n
  rw [sum_congr _ (fun l _ => mul_left_comm _ _ _), sum_mul_left]

theorem act_idm (v : Nat → Shell p) {n k : Nat} (hk : k < n) : act idm v n k = v k := by
  show sumRange (fun l => idm k l * v l) n = v k
  rw [sum_eq_single hk (fun l _ hne => by rw [idm_ne (fun e => hne e.symm), zero_mul]), idm_self, one_mul]

variable {κ : Nat} {g : Shell p}

/-! ## The shift's spectrum (6:E9) -/

/-- `(σ v)_k = v_{k−1}`, the index `k − 1` read as `(k + (n − 1)) mod n`. -/
theorem shift_act (F : Frame p κ g) (v : Nat → Shell p) {k : Nat} (hk : k < p - 1) :
    act (shift p) v (p - 1) k = v ((k + (p - 1 - 1)) % (p - 1)) := by
  show sumRange (fun l => (if (l + 1) % (p - 1) = k then (1 : Shell p) else 0) * v l) (p - 1) = _
  rw [sum_eq_single (FRC.Nat.mod_lt' _ F.n_pos) (fun l hl hne => by
    rw [ite_eq_right (fun e => hne (by rw [← pred_succ_mod F hl, e])), zero_mul])]
  rw [ite_eq_left (succ_pred_mod F hk), one_mul]

/-- `y^l = y^{l mod n}` for an `n`-th root of unity. -/
theorem pow_mod_of_root {y : Shell p} {n : Nat} (hn : 0 < n) (hy : y ^ n = 1) (l : Nat) : y ^ l = y ^ (l % n) := by
  obtain ⟨c, hc⟩ := FRC.Nat.mod_spec n hn l
  rw [congrArg (fun e => y ^ e) hc, pow_add, pow_mul, hy, one_pow, one_mul]

/-- Fermat on the cycle: every unit has `y^{p−1} = 1`. -/
theorem unit_pow_n (F : Frame p κ g) {y : Shell p} (hy : y ≠ 0) : y ^ (p - 1) = 1 := by
  obtain ⟨m, _, e⟩ := F.eq_pow_of_ne_zero hy
  rw [← e, pow_mul_comm, F.pow_n, one_pow]

/-- 6:E9, every nonzero residue `b` is an eigenvalue of the shift, with the geometric eigenvector `(y^j)_j = (b^{−j})_j`,
`b y = 1`: `(σ v)_k = y^{k−1} = b y^k`. -/
theorem shift_eigen (F : Frame p κ g) {b : Shell p} (hb : b ≠ 0) :
    ∃ y : Shell p, b * y = 1 ∧ IsEigen (shift p) (p - 1) b (fun j => y ^ j) := by
  obtain ⟨y, hy⟩ := F.exists_inv hb
  have hy0 : y ≠ 0 := fun e => F.one_ne_zero (by rw [← hy, e, mul_zero])
  have hyn := unit_pow_n F hy0
  refine ⟨y, hy, ⟨0, F.n_pos, by show y ^ 0 ≠ 0; rw [pow_zero]; exact F.one_ne_zero⟩, fun k hk => ?_⟩
  rw [shift_act F _ hk]
  show y ^ ((k + (p - 1 - 1)) % (p - 1)) = b * y ^ k
  rw [← pow_mod_of_root F.n_pos hyn, pow_add, mul_comm]
  congr 1
  apply inv_unique (y := y)
  · rw [← pow_succ, FRC.Nat.sub_add_cancel F.n_pos, hyn]
  · exact hy

/-- Every nonzero `b` has the inverse `y` that `shift_eigen` names: the eigenvector is `(y^j)_j`. -/
theorem shift_eigen_exists (F : Frame p κ g) {b : Shell p} (hb : b ≠ 0) :
    ∃ v : Nat → Shell p, IsEigen (shift p) (p - 1) b v :=
  match shift_eigen F hb with
  | ⟨_, _, h⟩ => ⟨_, h⟩

/-! ## The family's spectrum (6:E9) -/

/-- The selection of the `m`-th term with `[m = ℓ]` factors, `m < 4`. -/
theorem four_select' (c : Nat → Shell p) (Q : Shell p) : ∀ {m : Nat}, m < 4 →
    c 0 * (if m = 0 then Q else 0) + c 1 * (if m = 1 then Q else 0) + c 2 * (if m = 2 then Q else 0) +
      c 3 * (if m = 3 then Q else 0) = c m * Q
  | 0, _ => by
    rw [ite_eq_left rfl, ite_eq_right (by decide), ite_eq_right (by decide), ite_eq_right (by decide), mul_zero, mul_zero,
      mul_zero, add_zero, add_zero, add_zero]
  | 1, _ => by
    rw [ite_eq_right (by decide), ite_eq_left rfl, ite_eq_right (by decide), ite_eq_right (by decide), mul_zero, mul_zero,
      mul_zero, zero_add, add_zero, add_zero]
  | 2, _ => by
    rw [ite_eq_right (by decide), ite_eq_right (by decide), ite_eq_left rfl, ite_eq_right (by decide), mul_zero, mul_zero,
      mul_zero, zero_add, zero_add, add_zero]
  | 3, _ => by
    rw [ite_eq_right (by decide), ite_eq_right (by decide), ite_eq_right (by decide), ite_eq_left rfl, mul_zero, mul_zero,
      mul_zero, zero_add, zero_add, zero_add]
  | n + 4, h => absurd (Nat.lt_of_lt_of_le h (Nat.le_add_left 4 n)) (Nat.lt_irrefl _)

theorem proj_frft_pt (z : Shell p) (s m k j l : Nat) :
    proj g κ m k l * frft g κ z s l j =
      (z ^ s) ^ 0 * (proj g κ m k l * proj g κ 0 l j) + (z ^ s) ^ 1 * (proj g κ m k l * proj g κ 1 l j) +
      (z ^ s) ^ 2 * (proj g κ m k l * proj g κ 2 l j) + (z ^ s) ^ 3 * (proj g κ m k l * proj g κ 3 l j) :=
  mul_lift_id _ _ _ _ _ _ _ _ _

/-- `Π_m F^{[s]} = (z^s)^m Π_m`, the projector on the left. -/
theorem proj_frft (F : Frame p κ g) (z : Shell p) (s : Nat) {m : Nat} (hm : m < 4) {k j : Nat} (hk : k < p - 1)
    (hj : j < p - 1) :
    sumRange (fun l => proj g κ m k l * frft g κ z s l j) (p - 1) = (z ^ s) ^ m * proj g κ m k j := by
  rw [sum_congr _ (fun l _ => proj_frft_pt z s m k j l), sum_add, sum_add, sum_add, sum_mul_left, sum_mul_left, sum_mul_left, sum_mul_left,
    proj_mul F hm (Nat.zero_lt_succ 3) hk hj, proj_mul F hm (by decide : (1 : Nat) < 4) hk hj,
    proj_mul F hm (by decide : (2 : Nat) < 4) hk hj, proj_mul F hm (by decide : (3 : Nat) < 4) hk hj]
  exact four_select' (fun ℓ => (z ^ s) ^ ℓ) (proj g κ m k j) hm

/-- `v = Π₀ v + Π₁ v + Π₂ v + Π₃ v` on the cycle. -/
theorem act_sum_proj (F : Frame p κ g) (v : Nat → Shell p) {k : Nat} (hk : k < p - 1) :
    act (proj g κ 0) v (p - 1) k + act (proj g κ 1) v (p - 1) k + act (proj g κ 2) v (p - 1) k +
      act (proj g κ 3) v (p - 1) k = v k := by
  show sumRange (fun l => proj g κ 0 k l * v l) (p - 1) + sumRange (fun l => proj g κ 1 k l * v l) (p - 1) +
    sumRange (fun l => proj g κ 2 k l * v l) (p - 1) + sumRange (fun l => proj g κ 3 k l * v l) (p - 1) = v k
  rw [← sum_add, ← sum_add, ← sum_add, ← act_idm v hk]
  exact sum_congr _ (fun l _ => by
    show proj g κ 0 k l * v l + proj g κ 1 k l * v l + proj g κ 2 k l * v l + proj g κ 3 k l * v l = idm k l * v l
    rw [← right_distrib, ← right_distrib, ← right_distrib, sum_proj F k l])

/-- A sum of four that is nonzero has a nonzero term. -/
theorem four_ne_zero {a : Nat → Shell p} (h : a 0 + a 1 + a 2 + a 3 ≠ 0) : ∃ m, m < 4 ∧ a m ≠ 0 :=
  match Decidable.em (a 0 = 0), Decidable.em (a 1 = 0), Decidable.em (a 2 = 0), Decidable.em (a 3 = 0) with
  | Or.inr h0, _, _, _ => ⟨0, by decide, h0⟩
  | _, Or.inr h1, _, _ => ⟨1, by decide, h1⟩
  | _, _, Or.inr h2, _ => ⟨2, by decide, h2⟩
  | _, _, _, Or.inr h3 => ⟨3, by decide, h3⟩
  | Or.inl h0, Or.inl h1, Or.inl h2, Or.inl h3 => absurd (by rw [h0, h1, h2, h3, add_zero, add_zero, add_zero]) h

/-- 6:E9, an eigenvalue of `F^{[s]}` is one of the four `(z^s)^ℓ`: on an eigenvector `v`, `Π_m F^{[s]} v` reads both
`lam Π_m v` and `(z^s)^m Π_m v`, and some `Π_m v` is nonzero since `v = Σ_m Π_m v`. -/
theorem frft_eigen (F : Frame p κ g) (z : Shell p) (s : Nat) {lam : Shell p} {v : Nat → Shell p}
    (h : IsEigen (frft g κ z s) (p - 1) lam v) : ∃ ℓ, ℓ < 4 ∧ lam = (z ^ s) ^ ℓ := by
  obtain ⟨⟨k, hk, hv⟩, hact⟩ := h
  have key : ∀ m, m < 4 → ∀ k, k < p - 1 → lam * act (proj g κ m) v (p - 1) k = (z ^ s) ^ m * act (proj g κ m) v (p - 1) k :=
    fun m hm k hk => by
      have e1 : act (proj g κ m) (act (frft g κ z s) v (p - 1)) (p - 1) k = lam * act (proj g κ m) v (p - 1) k := by
        rw [← act_smul]
        exact sum_congr _ (fun l hl => by rw [hact l hl])
      have e2 : act (proj g κ m) (act (frft g κ z s) v (p - 1)) (p - 1) k = (z ^ s) ^ m * act (proj g κ m) v (p - 1) k := by
        rw [← act_mmul]
        show sumRange (fun l => mmul (proj g κ m) (frft g κ z s) (p - 1) k l * v l) (p - 1) =
          (z ^ s) ^ m * sumRange (fun l => proj g κ m k l * v l) (p - 1)
        rw [← sum_mul_left]
        exact sum_congr _ (fun l hl => by
          show mmul (proj g κ m) (frft g κ z s) (p - 1) k l * v l = (z ^ s) ^ m * (proj g κ m k l * v l)
          rw [show mmul (proj g κ m) (frft g κ z s) (p - 1) k l = (z ^ s) ^ m * proj g κ m k l from
            proj_frft F z s hm hk hl, mul_assoc])
      rw [← e1, e2]
  have hsum : act (proj g κ 0) v (p - 1) k + act (proj g κ 1) v (p - 1) k + act (proj g κ 2) v (p - 1) k +
      act (proj g κ 3) v (p - 1) k ≠ 0 := by rw [act_sum_proj F v hk]; exact hv
  obtain ⟨m, hm, hne⟩ := four_ne_zero (a := fun m => act (proj g κ m) v (p - 1) k) hsum
  exact ⟨m, hm, F.mul_left_cancel hne (by rw [mul_comm, key m hm k hk, mul_comm])⟩

/-! ## The obstruction (6:E5) -/

/-- The least `ℓ < 4` with `P ℓ`, or `3`. -/
def find4 (P : Nat → Prop) [DecidablePred P] : Nat := if P 0 then 0 else if P 1 then 1 else if P 2 then 2 else 3

theorem find4_lt (P : Nat → Prop) [DecidablePred P] : find4 P < 4 := by
  unfold find4
  match Decidable.em (P 0), Decidable.em (P 1), Decidable.em (P 2) with
  | Or.inl h, _, _ => rw [ite_eq_left h]; decide
  | Or.inr h, Or.inl h1, _ => rw [ite_eq_right h, ite_eq_left h1]; decide
  | Or.inr h, Or.inr h1, Or.inl h2 => rw [ite_eq_right h, ite_eq_right h1, ite_eq_left h2]; decide
  | Or.inr h, Or.inr h1, Or.inr h2 => rw [ite_eq_right h, ite_eq_right h1, ite_eq_right h2]; decide

theorem find4_spec (P : Nat → Prop) [DecidablePred P] (h : ∃ ℓ, ℓ < 4 ∧ P ℓ) : P (find4 P) := by
  unfold find4
  match Decidable.em (P 0), Decidable.em (P 1), Decidable.em (P 2) with
  | Or.inl h0, _, _ => rw [ite_eq_left h0]; exact h0
  | Or.inr h0, Or.inl h1, _ => rw [ite_eq_right h0, ite_eq_left h1]; exact h1
  | Or.inr h0, Or.inr h1, Or.inl h2 => rw [ite_eq_right h0, ite_eq_right h1, ite_eq_left h2]; exact h2
  | Or.inr h0, Or.inr h1, Or.inr h2 =>
    rw [ite_eq_right h0, ite_eq_right h1, ite_eq_right h2]
    obtain ⟨ℓ, hℓ, hP⟩ := h
    match ℓ, hℓ, hP with
    | 0, _, hP => exact absurd hP h0
    | 1, _, hP => exact absurd hP h1
    | 2, _, hP => exact absurd hP h2
    | 3, _, hP => exact hP
    | n + 4, hℓ, _ => exact absurd (Nat.lt_of_lt_of_le hℓ (Nat.le_add_left 4 n)) (Nat.lt_irrefl _)

/-- 6:E5, the spectral obstruction: for `κ ≥ 2` no invertible `T` (with `T' T = I`) has `T σ T' = F^{[s]}`. Every
nonzero residue is an eigenvalue of `σ`, hence of `T σ T'` on `T v`, hence one of the four `(z^s)^ℓ`: an injection of
the `4κ` residues into four indices. -/
theorem spectral_obstruction (F : Frame p κ g) (hκ : 2 ≤ κ) (z : Shell p) (s : Nat)
    (T T' : Nat → Nat → Shell p) (hinv : ∀ k j, k < p - 1 → j < p - 1 → mmul T' T (p - 1) k j = idm k j)
    (hconj : ∀ k j, k < p - 1 → j < p - 1 → mmul (mmul T (shift p) (p - 1)) T' (p - 1) k j = frft g κ z s k j) :
    False := by
  have hn := F.n_pos
  -- every power g^m is an eigenvalue of F^[s]
  have heig : ∀ m, ∃ ℓ, ℓ < 4 ∧ g ^ m = (z ^ s) ^ ℓ := fun m => by
    obtain ⟨v, ⟨k0, hk0, hv0⟩, hσ⟩ := shift_eigen_exists F (F.pow_ne_zero m)
    -- w = T v is an eigenvector of F^[s] for g^m
    have hTv : ∀ k, k < p - 1 → act T' (act T v (p - 1)) (p - 1) k = v k := fun k hk => by
      rw [← act_mmul, ← act_idm v hk]
      exact sum_congr _ (fun l hl => by rw [hinv k l hk hl])
    have hw : ∃ k, k < p - 1 ∧ act T v (p - 1) k ≠ 0 :=
      match decExistsLT (fun k => act T v (p - 1) k ≠ 0) (p - 1) with
      | isTrue e => e
      | isFalse ne => absurd (by
          rw [← hTv k0 hk0]
          exact sum_zero _ (fun l hl => by
            have e : act T v (p - 1) l = 0 := match Decidable.em (act T v (p - 1) l = 0) with
              | Or.inl e => e
              | Or.inr e => absurd ⟨l, hl, e⟩ ne
            rw [e, mul_zero])) hv0
    have hact : ∀ k, k < p - 1 → act (frft g κ z s) (act T v (p - 1)) (p - 1) k = g ^ m * act T v (p - 1) k :=
      fun k hk => by
        rw [show act (frft g κ z s) (act T v (p - 1)) (p - 1) k =
            act (mmul (mmul T (shift p) (p - 1)) T' (p - 1)) (act T v (p - 1)) (p - 1) k from
          sum_congr _ (fun l hl => by rw [hconj k l hk hl])]
        rw [act_mmul, act_mmul, ← act_smul]
        exact sum_congr _ (fun l hl => by
          show T k l * act (shift p) (act T' (act T v (p - 1)) (p - 1)) (p - 1) l = T k l * (g ^ m * v l)
          rw [← hσ l hl]
          show T k l * act (shift p) (act T' (act T v (p - 1)) (p - 1)) (p - 1) l =
            T k l * act (shift p) v (p - 1) l
          rw [shift_act F _ hl, shift_act F _ hl, hTv _ (FRC.Nat.mod_lt' _ hn)])
    exact frft_eigen F z s ⟨hw, hact⟩
  -- the injection of [0, 4κ) into [0, 4)
  have h4 : 4 < p - 1 := four_lt_n F hκ
  exact FRC.Logic.no_mirror h4 (fun m => find4 (fun ℓ => (z ^ s) ^ ℓ = g ^ m)) (fun m _ => find4_lt _) (fun m m' hm hm' e =>
    F.pow_inj hm hm' (by
      have e1 := find4_spec (fun ℓ => (z ^ s) ^ ℓ = g ^ m) (match heig m with | ⟨ℓ, hℓ, e⟩ => ⟨ℓ, hℓ, e.symm⟩)
      have e2 := find4_spec (fun ℓ => (z ^ s) ^ ℓ = g ^ m') (match heig m' with | ⟨ℓ, hℓ, e⟩ => ⟨ℓ, hℓ, e.symm⟩)
      rw [← e1, ← e2, e]))

end Frame
end Shell
end FRC
