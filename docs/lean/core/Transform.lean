import FrcCore.Series
import FrcCore.Frame

/-!
# FrcCore.Transform — the shell Fourier transform on the cycle: `W`, the reversal `J`, `F = i W` (the frame theme)

The geometric sum gives the principal-root identity (2:F1, Prop. 6.1 of 2-geometry) and the entrywise inversion of the
shell Fourier matrix `W k j = g^{jk}`: `Σ_l W k l · (−g^{−lj}) = [k = j]` (2:F3, Prop. 6.3; 6:B5 in matrix form); the
reversal `rev`, `J`, and the quarter-turn transform `F = i W` with `W² = −J`, `F² = J`, `J² = I` and `W J = J W` (6:B5,
6:B7). Split from `Sum.lean` by the ledger migration (task LM25), every name unchanged, so that the fourier theme takes
the transform without the orbits (gate G10). No axioms.
-/

namespace FRC
namespace Shell

variable {p : Nat} [Pos p]

namespace Frame
variable {κ : Nat} {g : Shell p}

/-- `Σ_{l<n} x^l = 0` when `x^n = 1` and `x ≠ 1` (the field has no zero divisors). -/
theorem geom_sum_eq_zero (F : Frame p κ g) {x : Shell p} (n : Nat) (hn : x ^ n = 1) (hx : x ≠ 1) :
    sumRange (fun l => x ^ l) n = 0 := by
  have h := geom_sum_mul x n
  rw [hn, add_neg] at h
  match F.mul_eq_zero h with
  | .inl e => exact e
  | .inr e => exact absurd (by
      calc x = x + 0 := (add_zero x).symm
        _ = x + (-1 + 1) := by rw [neg_add]
        _ = (x + -1) + 1 := (add_assoc _ _ _).symm
        _ = 1 := by rw [e, zero_add]) hx

/-- 6:B6 — the normalization constant read in the field: `n = p − 1 ≡ −1`. -/
theorem ofNat_n (F : Frame p κ g) : (ofNat (p - 1) : Shell p) = -1 := by
  apply ext
  rw [val_ofNat, val_neg, val_one, FRC.Nat.mod_eq_of_lt F.one_lt_p,
    FRC.Nat.mod_eq_of_lt (Nat.sub_lt Pos.pos (Nat.zero_lt_succ 0))]

/-- 2:F1 (Prop. 6.1) — `g` is a principal root of unity: `g^n = 1`, `Σ_{j<n} (g^k)^j = 0` for
`0 < k < n`, and `n = p − 1` reads as `−1` in the shell. -/
theorem principal_root (F : Frame p κ g) (k : Nat) (hk0 : 0 < k) (hk : k < p - 1) :
    g ^ (p - 1) = 1 ∧ sumRange (fun j => (g ^ k) ^ j) (p - 1) = 0 ∧ (ofNat (p - 1) : Shell p) = -1 := by
  refine ⟨F.pow_n, ?_, F.ofNat_n⟩
  apply F.geom_sum_eq_zero
  · rw [pow_mul_comm, F.pow_n, one_pow]
  · exact F.prim.2 k hk hk0

/-- `g^{k + (n − j)} = 1` exactly when `k = j`, for `k, j < n`. -/
theorem pow_shift_eq_one_iff (F : Frame p κ g) {k j : Nat} (hk : k < p - 1) (hj : j < p - 1) :
    g ^ (k + (p - 1 - j)) = 1 ↔ k = j := by
  have hn := F.n_pos
  have hjn : p - 1 - j + j = p - 1 := FRC.Nat.sub_add_cancel (Nat.le_of_lt hj)
  constructor
  · intro h
    have hm := F.mod_eq_zero_of_pow_eq_one h
    match Nat.lt_or_ge k j with
    | .inl hlt =>
      have hlt' : k + (p - 1 - j) < p - 1 := by
        have := Nat.add_lt_add_right hlt (p - 1 - j)
        rw [Nat.add_comm j, hjn] at this
        exact this
      rw [FRC.Nat.mod_eq_of_lt hlt'] at hm
      have hpos : 0 < p - 1 - j := by
        refine Nat.lt_of_add_lt_add_right (n := j) ?_
        rw [Nat.zero_add, hjn]; exact hj
      exact absurd hm (Nat.ne_of_gt (Nat.lt_of_lt_of_le hpos (Nat.le_add_left _ _)))
    | .inr hge =>
      have e : k + (p - 1 - j) = (p - 1) * 1 + (k - j) := by
        rw [Nat.mul_one]
        calc k + (p - 1 - j) = (j + (k - j)) + (p - 1 - j) := by rw [FRC.Nat.add_sub_of_le hge]
          _ = (p - 1 - j + j) + (k - j) := by
              rw [Nat.add_comm j (k - j), Nat.add_assoc, Nat.add_comm (k - j), Nat.add_comm j (p - 1 - j)]
          _ = p - 1 + (k - j) := by rw [hjn]
      rw [e, FRC.Nat.add_mul_mod_self_left _ _ _ hn,
        FRC.Nat.mod_eq_of_lt (Nat.lt_of_le_of_lt (Nat.sub_le k j) hk)] at hm
      have := FRC.Nat.add_sub_of_le hge
      rw [hm, Nat.add_zero] at this
      exact this.symm
  · intro e
    rw [e, FRC.Nat.add_sub_of_le (Nat.le_of_lt hj), F.pow_n]

/-- 2:F3 (Prop. 6.3), 6:B5 — the inversion of the shell Fourier matrix, entrywise: with
`W k j = g^{jk}` and `W' l j = −g^{(n−j)l}` (`= −g^{−lj}`), `Σ_{l<n} W k l · W' l j = [k = j]`. -/
theorem dft_inverse (F : Frame p κ g) {k j : Nat} (hk : k < p - 1) (hj : j < p - 1) :
    sumRange (fun l => g ^ (l * k) * -(g ^ ((p - 1 - j) * l))) (p - 1) = if k = j then 1 else 0 := by
  have hsum : sumRange (fun l => g ^ (l * k) * -(g ^ ((p - 1 - j) * l))) (p - 1)
      = -(sumRange (fun l => (g ^ (k + (p - 1 - j))) ^ l) (p - 1)) := by
    rw [← sum_neg]
    apply sum_congr
    intro l _
    rw [← mul_neg, ← pow_add, ← pow_mul, Nat.mul_comm l k, ← FRC.Nat.add_mul]
  rw [hsum]
  exact match Nat.decEq k j with
    | .isTrue e => by
        rw [ite_eq_left e]
        have h1 : g ^ (k + (p - 1 - j)) = 1 := (F.pow_shift_eq_one_iff hk hj).2 e
        have : sumRange (fun l => (g ^ (k + (p - 1 - j))) ^ l) (p - 1) = ofNat (p - 1) * 1 := by
          rw [← sum_const]; apply sum_congr; intro l _; rw [h1, one_pow]
        rw [this, F.ofNat_n, mul_one, neg_neg]
    | .isFalse e => by
        rw [ite_eq_right e]
        have h1 : g ^ (k + (p - 1 - j)) ≠ 1 := fun h => e ((F.pow_shift_eq_one_iff hk hj).1 h)
        rw [F.geom_sum_eq_zero _ (by rw [pow_mul_comm, F.pow_n, one_pow]) h1, neg_zero]

/-- `g^{k + j} = 1` exactly when `(k + j) % n = 0`, i.e. `j` is the reversal `−k` of `k` (`k, j < n`). -/
theorem pow_add_eq_one_iff (F : Frame p κ g) (k j : Nat) : g ^ (k + j) = 1 ↔ (k + j) % (p - 1) = 0 :=
  ⟨F.mod_eq_zero_of_pow_eq_one, F.pow_eq_one_of_mod⟩

/-- 6:B5 (the shell Fourier matrix squares to the reversal, entrywise): with `W k j = g^{jk}` and
`J k j = [(k + j) % n = 0]`, `Σ_{l<n} W k l · W l j = −J k j` on every shell (`n = p − 1 ≡ −1`). -/
theorem W_sq (F : Frame p κ g) (k j : Nat) :
    sumRange (fun l => g ^ (l * k) * g ^ (j * l)) (p - 1)
      = -(if (k + j) % (p - 1) = 0 then 1 else 0) := by
  have hsum : sumRange (fun l => g ^ (l * k) * g ^ (j * l)) (p - 1)
      = sumRange (fun l => (g ^ (k + j)) ^ l) (p - 1) := by
    apply sum_congr; intro l _
    rw [← pow_add, ← pow_mul, Nat.mul_comm l k, ← FRC.Nat.add_mul]
  rw [hsum]
  exact match Nat.decEq ((k + j) % (p - 1)) 0 with
    | .isTrue e => by
        rw [ite_eq_left e]
        have h1 : g ^ (k + j) = 1 := F.pow_eq_one_of_mod e
        have : sumRange (fun l => (g ^ (k + j)) ^ l) (p - 1) = ofNat (p - 1) * 1 := by
          rw [← sum_const]; apply sum_congr; intro l _; rw [h1, one_pow]
        rw [this, F.ofNat_n, mul_one]
    | .isFalse e => by
        rw [ite_eq_right e, neg_zero]
        exact F.geom_sum_eq_zero _ (by rw [pow_mul_comm, F.pow_n, one_pow]) (fun h => e (F.mod_eq_zero_of_pow_eq_one h))

/-! ### The reversal, the Fourier matrix `W`, the quarter-turn transform `F = i·W` (6:B5, B7) -/

/-- The reversal `rev n k = (n − k) % n`: the index `l` with `(k + l) % n = 0`. -/
def rev (n k : Nat) : Nat := (n - k) % n

theorem rev_lt {n : Nat} (hn : 0 < n) (k : Nat) : rev n k < n := Nat.mod_lt _ hn

theorem rev_zero (n : Nat) (hn : 0 < n) : rev n 0 = 0 := by
  unfold rev; rw [Nat.sub_zero]; exact FRC.Nat.mod_self n hn

theorem rev_of_pos {n k : Nat} (hk : k < n) (hk0 : 0 < k) : rev n k = n - k := by
  unfold rev; exact FRC.Nat.mod_eq_of_lt (Nat.sub_lt (Nat.lt_of_lt_of_le hk0 (Nat.le_of_lt hk)) hk0)

theorem rev_add_mod {n k : Nat} (hk : k < n) : (rev n k + k) % n = 0 := by
  have hn : 0 < n := Nat.lt_of_le_of_lt (Nat.zero_le k) hk
  exact match Nat.decEq k 0 with
    | isTrue e => by rw [e, rev_zero n hn]; rfl
    | isFalse e => by
        rw [rev_of_pos hk (Nat.pos_of_ne_zero e), FRC.Nat.sub_add_cancel (Nat.le_of_lt hk)]
        exact FRC.Nat.mod_self n hn

theorem rev_rev {n k : Nat} (hk : k < n) : rev n (rev n k) = k := by
  have hn : 0 < n := Nat.lt_of_le_of_lt (Nat.zero_le k) hk
  exact match Nat.decEq k 0 with
    | isTrue e => by rw [e, rev_zero n hn, rev_zero n hn]
    | isFalse e => by
        have hk0 := Nat.pos_of_ne_zero e
        rw [rev_of_pos hk hk0]
        have hnk : n - k < n := Nat.sub_lt (Nat.lt_of_lt_of_le hk0 (Nat.le_of_lt hk)) hk0
        have hnk0 : 0 < n - k := by
          refine Nat.lt_of_add_lt_add_right (n := k) ?_
          rw [Nat.zero_add, FRC.Nat.sub_add_cancel (Nat.le_of_lt hk)]; exact hk
        rw [rev_of_pos hnk hnk0]
        calc n - (n - k) = (n - k + k) - (n - k) := by rw [FRC.Nat.sub_add_cancel (Nat.le_of_lt hk)]
          _ = k := FRC.Nat.add_sub_cancel_left _ _

/-- `(k + l) % n = 0` exactly when `l` is the reversal of `k` (`k, l < n`). -/
theorem add_mod_eq_zero_iff {n k l : Nat} (hk : k < n) (hl : l < n) : (k + l) % n = 0 ↔ l = rev n k := by
  have hn : 0 < n := Nat.lt_of_le_of_lt (Nat.zero_le k) hk
  constructor
  · intro h
    exact match Nat.decEq k 0 with
      | isTrue e => by
          rw [e, Nat.zero_add, FRC.Nat.mod_eq_of_lt hl] at h
          rw [e, rev_zero n hn, h]
      | isFalse e => by
          have hk0 := Nat.pos_of_ne_zero e
          rw [rev_of_pos hk hk0]
          exact match Nat.lt_or_ge l (n - k) with
            | Or.inl hlt => by
                have : k + l < n := by
                  have := Nat.add_lt_add_left hlt k
                  rw [FRC.Nat.add_sub_of_le (Nat.le_of_lt hk)] at this; exact this
                rw [FRC.Nat.mod_eq_of_lt this] at h
                exact absurd h (Nat.ne_of_gt (Nat.lt_of_lt_of_le hk0 (Nat.le_add_right k l)))
            | Or.inr hge => by
                have e1 : k + l = n * 1 + (l - (n - k)) := by
                  rw [Nat.mul_one]
                  calc k + l = k + ((n - k) + (l - (n - k))) := by rw [FRC.Nat.add_sub_of_le hge]
                    _ = (k + (n - k)) + (l - (n - k)) := (Nat.add_assoc _ _ _).symm
                    _ = n + (l - (n - k)) := by rw [FRC.Nat.add_sub_of_le (Nat.le_of_lt hk)]
                rw [e1, FRC.Nat.add_mul_mod_self_left _ _ _ hn,
                  FRC.Nat.mod_eq_of_lt (Nat.lt_of_le_of_lt (Nat.sub_le _ _) hl)] at h
                have := FRC.Nat.add_sub_of_le hge
                rw [h, Nat.add_zero] at this
                exact this.symm
  · intro e; rw [e, Nat.add_comm]; exact rev_add_mod hk

/-- The shell Fourier matrix, `W k j = g^{jk}` (6:B5's convention). -/
def W (g : Shell p) (k j : Nat) : Shell p := g ^ (j * k)

/-- The reversal matrix `J k j = [(k + j) % n = 0]`. -/
def J (n k j : Nat) : Shell p := if (k + j) % n = 0 then 1 else 0

/-- The quarter-turn transform `F = i·W`, `i = −g^κ`. -/
def Fmat (g : Shell p) (κ k j : Nat) : Shell p := quarterTurn g κ * W g k j

theorem J_eq {n k l : Nat} (hk : k < n) (hl : l < n) :
    (J n k l : Shell p) = (if l = rev n k then (1 : Shell p) else 0) := by
  unfold J
  exact match Nat.decEq l (rev n k) with
    | isTrue e => by rw [ite_eq_left e, ite_eq_left ((add_mod_eq_zero_iff hk hl).2 e)]
    | isFalse e => by rw [ite_eq_right e, ite_eq_right (fun h => e ((add_mod_eq_zero_iff hk hl).1 h))]

/-- 6:B5 (`W² = −J`, entrywise), in the matrix notation. -/
theorem W_sq' (F : Frame p κ g) (k j : Nat) :
    sumRange (fun l => W g k l * W g l j) (p - 1) = -(J (p - 1) k j) := F.W_sq k j

/-- 6:B5, 6:B7 (`J² = 1`, entrywise): the reversal is an involution, so `F⁴ = J² = 1`. -/
theorem J_sq (F : Frame p κ g) {k j : Nat} (hk : k < p - 1) (hj : j < p - 1) :
    sumRange (fun l => (J (p - 1) k l : Shell p) * J (p - 1) l j) (p - 1) = (if k = j then (1 : Shell p) else 0) := by
  have hn := F.n_pos
  have hr : rev (p - 1) k < p - 1 := rev_lt hn k
  rw [sum_eq_single hr (fun l hl hne => by rw [J_eq hk hl, ite_eq_right hne, zero_mul])]
  rw [J_eq hk hr, ite_eq_left rfl, one_mul, J_eq hr hj, rev_rev hk]
  exact match Nat.decEq k j with
    | isTrue e => by rw [ite_eq_left e, ite_eq_left e.symm]
    | isFalse e => by rw [ite_eq_right e, ite_eq_right (fun h => e h.symm)]

/-- 6:B5, 6:B7 (`F² = J`, entrywise): the quarter-turn transform squares to the reversal. -/
theorem F_sq (F : Frame p κ g) (k j : Nat) :
    sumRange (fun l => Fmat g κ k l * Fmat g κ l j) (p - 1) = J (p - 1) k j := by
  have e : ∀ l, Fmat g κ k l * Fmat g κ l j = (quarterTurn g κ * quarterTurn g κ) * (W g k l * W g l j) := by
    intro l; unfold Fmat
    rw [mul_assoc, mul_left_comm (W g k l), ← mul_assoc]
  rw [sum_congr _ (fun l _ => e l), sum_mul_left, F.W_sq' k j, F.quarter_turn_sq, ← neg_mul, one_mul, neg_neg]

/-- 6:B7 (`W J = J W`, entrywise). -/
theorem W_J_comm (F : Frame p κ g) {k j : Nat} (hk : k < p - 1) (hj : j < p - 1) :
    sumRange (fun l => W g k l * J (p - 1) l j) (p - 1) = sumRange (fun l => J (p - 1) k l * W g l j) (p - 1) := by
  have hn := F.n_pos
  have hrj : rev (p - 1) j < p - 1 := rev_lt hn j
  have hrk : rev (p - 1) k < p - 1 := rev_lt hn k
  rw [sum_eq_single hrj (fun l hl hne => by
        rw [J_eq hl hj, ite_eq_right (fun e => hne (by rw [e, rev_rev hl])), mul_zero])]
  rw [sum_eq_single hrk (fun l hl hne => by rw [J_eq hk hl, ite_eq_right hne, zero_mul])]
  rw [J_eq hrj hj, ite_eq_left (rev_rev hj).symm, mul_one, J_eq hk hrk, ite_eq_left rfl, one_mul]
  unfold W
  -- both are the inverse of g^{jk}
  apply inv_unique (y := g ^ (j * k))
  · rw [← pow_add, ← FRC.Nat.add_mul, F.pow_mod, ← FRC.Nat.mod_mul_mod _ _ _ hn, rev_add_mod hj, Nat.zero_mul,
      FRC.Nat.zero_mod, pow_zero]
  · rw [← pow_add, ← Nat.left_distrib, F.pow_mod, ← FRC.Nat.mul_mod_mod _ _ _ hn, rev_add_mod hk, Nat.mul_zero,
      FRC.Nat.zero_mod, pow_zero]

end Frame

end Shell
end FRC
