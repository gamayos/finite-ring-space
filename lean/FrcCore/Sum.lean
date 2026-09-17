import FrcCore.Frame
import FrcCore.Orbit

/-!
# FrcCore.Sum — finite sums on the shell, the geometric sum, the Fourier inversion

Sums over `l < n` are defined by structural recursion (`sumRange f (n+1) = sumRange f n + f n`): no
`Finset`, no quotient, no function extensionality — a congruence lemma (`sum_congr`) replaces `funext`.
The geometric sum gives the principal-root identity (2:F1, Prop. 6.1 of 2-geometry) and the entrywise
inversion of the shell Fourier matrix `W k j = g^{jk}`: `Σ_l W k l · (−g^{−lj}) = [k = j]` (2:F3,
Prop. 6.3; 6:B5 in matrix form). No axioms.
-/

namespace FRC
namespace Shell

variable {p : Nat} [Pos p]

/-- `sumRange f n = f 0 + f 1 + ⋯ + f (n−1)`. -/
def sumRange (f : Nat → Shell p) : Nat → Shell p
  | 0 => 0
  | n + 1 => sumRange f n + f n

theorem sumRange_zero (f : Nat → Shell p) : sumRange f 0 = 0 := rfl
theorem sumRange_succ (f : Nat → Shell p) (n : Nat) : sumRange f (n + 1) = sumRange f n + f n := rfl

theorem sum_congr {f h : Nat → Shell p} (n : Nat) (e : ∀ l, l < n → f l = h l) :
    sumRange f n = sumRange h n := by
  induction n with
  | zero => rfl
  | succ n ih =>
    rw [sumRange_succ, sumRange_succ, ih (fun l hl => e l (Nat.lt_succ_of_lt hl)),
      e n (Nat.lt_succ_self n)]

theorem sum_add (f h : Nat → Shell p) (n : Nat) :
    sumRange (fun l => f l + h l) n = sumRange f n + sumRange h n := by
  induction n with
  | zero => rw [sumRange_zero, sumRange_zero, sumRange_zero, add_zero]
  | succ n ih =>
    rw [sumRange_succ, sumRange_succ, sumRange_succ, ih, add_add_add_comm]

theorem sum_mul_right (f : Nat → Shell p) (c : Shell p) (n : Nat) :
    sumRange (fun l => f l * c) n = sumRange f n * c := by
  induction n with
  | zero => rw [sumRange_zero, sumRange_zero, zero_mul]
  | succ n ih => rw [sumRange_succ, sumRange_succ, ih, right_distrib]

theorem sum_mul_left (f : Nat → Shell p) (c : Shell p) (n : Nat) :
    sumRange (fun l => c * f l) n = c * sumRange f n := by
  induction n with
  | zero => rw [sumRange_zero, sumRange_zero, mul_zero]
  | succ n ih => rw [sumRange_succ, sumRange_succ, ih, left_distrib]

theorem sum_neg (f : Nat → Shell p) (n : Nat) : sumRange (fun l => -(f l)) n = -(sumRange f n) := by
  induction n with
  | zero => rw [sumRange_zero, sumRange_zero, neg_zero]
  | succ n ih => rw [sumRange_succ, sumRange_succ, ih, neg_add_rev]

theorem sum_const (c : Shell p) (n : Nat) : sumRange (fun _ => c) n = ofNat n * c := by
  induction n with
  | zero => rw [sumRange_zero]; exact (zero_mul c).symm
  | succ n ih =>
    rw [sumRange_succ, ih]
    have : (ofNat (n + 1) : Shell p) = ofNat n + 1 := ext (by
      rw [val_ofNat, val_add, val_ofNat, val_one, FRC.Nat.mod_add_mod _ _ _ hp, FRC.Nat.add_mod_mod _ _ _ hp])
    rw [this, right_distrib, one_mul]

theorem sum_zero {f : Nat → Shell p} (n : Nat) (h : ∀ l, l < n → f l = 0) : sumRange f n = 0 := by
  induction n with
  | zero => rfl
  | succ n ih => rw [sumRange_succ, ih (fun l hl => h l (Nat.lt_succ_of_lt hl)), h n (Nat.lt_succ_self n), add_zero]

/-- A sum with a single nonzero term. -/
theorem sum_eq_single {f : Nat → Shell p} {l₀ : Nat} : ∀ {n : Nat}, l₀ < n → (∀ l, l < n → l ≠ l₀ → f l = 0) →
    sumRange f n = f l₀
  | 0, h, _ => absurd h (Nat.not_lt_zero _)
  | n + 1, hl₀, h => by
    rw [sumRange_succ]
    exact match Nat.decEq l₀ n with
      | isTrue e => by
          rw [sum_zero n (fun l hl => h l (Nat.lt_succ_of_lt hl) (fun e' => absurd hl (by rw [e', e]; exact Nat.lt_irrefl n))),
            zero_add, e]
      | isFalse e => by
          rw [sum_eq_single (Nat.lt_of_le_of_ne (Nat.le_of_lt_succ hl₀) (fun e' => e e')) (fun l hl hne => h l (Nat.lt_succ_of_lt hl) hne),
            h n (Nat.lt_succ_self n) (fun e' => e e'.symm), add_zero]

/-- The telescoping geometric sum: `(Σ_{l<n} x^l)·(x − 1) = x^n − 1`. -/
theorem geom_sum_mul (x : Shell p) (n : Nat) :
    sumRange (fun l => x ^ l) n * (x + -1) = x ^ n + -1 := by
  induction n with
  | zero => rw [sumRange_zero, zero_mul, pow_zero, add_neg]
  | succ n ih =>
    rw [sumRange_succ, right_distrib, ih, left_distrib, ← mul_neg, mul_one, ← pow_succ]
    rw [add_add_add_comm, add_comm (x ^ n) (x ^ (n + 1)), add_comm (-1) (-(x ^ n)), add_assoc,
      ← add_assoc (x ^ n), add_neg, zero_add]

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
        rw [if_pos e]
        have h1 : g ^ (k + (p - 1 - j)) = 1 := (F.pow_shift_eq_one_iff hk hj).2 e
        have : sumRange (fun l => (g ^ (k + (p - 1 - j))) ^ l) (p - 1) = ofNat (p - 1) * 1 := by
          rw [← sum_const]; apply sum_congr; intro l _; rw [h1, one_pow]
        rw [this, F.ofNat_n, mul_one, neg_neg]
    | .isFalse e => by
        rw [if_neg e]
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
        rw [if_pos e]
        have h1 : g ^ (k + j) = 1 := F.pow_eq_one_of_mod e
        have : sumRange (fun l => (g ^ (k + j)) ^ l) (p - 1) = ofNat (p - 1) * 1 := by
          rw [← sum_const]; apply sum_congr; intro l _; rw [h1, one_pow]
        rw [this, F.ofNat_n, mul_one]
    | .isFalse e => by
        rw [if_neg e, neg_zero]
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
    | isTrue e => by rw [if_pos e, if_pos ((add_mod_eq_zero_iff hk hl).2 e)]
    | isFalse e => by rw [if_neg e, if_neg (fun h => e ((add_mod_eq_zero_iff hk hl).1 h))]

/-- 6:B5 (`W² = −J`, entrywise), in the matrix notation. -/
theorem W_sq' (F : Frame p κ g) (k j : Nat) :
    sumRange (fun l => W g k l * W g l j) (p - 1) = -(J (p - 1) k j) := F.W_sq k j

/-- 6:B5, 6:B7 (`J² = 1`, entrywise): the reversal is an involution, so `F⁴ = J² = 1`. -/
theorem J_sq (F : Frame p κ g) {k j : Nat} (hk : k < p - 1) (hj : j < p - 1) :
    sumRange (fun l => (J (p - 1) k l : Shell p) * J (p - 1) l j) (p - 1) = (if k = j then (1 : Shell p) else 0) := by
  have hn := F.n_pos
  have hr : rev (p - 1) k < p - 1 := rev_lt hn k
  rw [sum_eq_single hr (fun l hl hne => by rw [J_eq hk hl, if_neg hne, zero_mul])]
  rw [J_eq hk hr, if_pos rfl, one_mul, J_eq hr hj, rev_rev hk]
  exact match Nat.decEq k j with
    | isTrue e => by rw [if_pos e, if_pos e.symm]
    | isFalse e => by rw [if_neg e, if_neg (fun h => e h.symm)]

/-- 6:B5, 6:B7 (`F² = J`, entrywise): the quarter-turn transform squares to the reversal. -/
theorem F_sq (F : Frame p κ g) (k j : Nat) :
    sumRange (fun l => Fmat g κ k l * Fmat g κ l j) (p - 1) = J (p - 1) k j := by
  have e : ∀ l, Fmat g κ k l * Fmat g κ l j = (quarterTurn g κ * quarterTurn g κ) * (W g k l * W g l j) := by
    intro l; unfold Fmat
    rw [mul_assoc, mul_left_comm (W g k l), ← mul_assoc]
  rw [sum_congr _ (fun l _ => e l), sum_mul_left, F.W_sq' k j, F.quarter_turn_sq, ← neg_mul, one_mul, neg_neg]

theorem inv_unique {x x' y : Shell p} (h : x * y = 1) (h' : x' * y = 1) : x = x' := by
  calc x = x * (x' * y) := by rw [h', mul_one]
    _ = x' * (x * y) := mul_left_comm _ _ _
    _ = x' := by rw [h, mul_one]

/-- 6:B7 (`W J = J W`, entrywise). -/
theorem W_J_comm (F : Frame p κ g) {k j : Nat} (hk : k < p - 1) (hj : j < p - 1) :
    sumRange (fun l => W g k l * J (p - 1) l j) (p - 1) = sumRange (fun l => J (p - 1) k l * W g l j) (p - 1) := by
  have hn := F.n_pos
  have hrj : rev (p - 1) j < p - 1 := rev_lt hn j
  have hrk : rev (p - 1) k < p - 1 := rev_lt hn k
  rw [sum_eq_single hrj (fun l hl hne => by
        rw [J_eq hl hj, if_neg (fun e => hne (by rw [e, rev_rev hl])), mul_zero])]
  rw [sum_eq_single hrk (fun l hl hne => by rw [J_eq hk hl, if_neg hne, zero_mul])]
  rw [J_eq hrj hj, if_pos (rev_rev hj).symm, mul_one, J_eq hk hrk, if_pos rfl, one_mul]
  unfold W
  -- both are the inverse of g^{jk}
  apply inv_unique (y := g ^ (j * k))
  · rw [← pow_add, ← FRC.Nat.add_mul, F.pow_mod, ← FRC.Nat.mod_mul_mod _ _ _ hn, rev_add_mod hj, Nat.zero_mul,
      FRC.Nat.zero_mod, pow_zero]
  · rw [← pow_add, ← Nat.left_distrib, F.pow_mod, ← FRC.Nat.mul_mod_mod _ _ _ hn, rev_add_mod hk, Nat.mul_zero,
      FRC.Nat.zero_mod, pow_zero]

/-! ### Sums over lists, permutation invariance (the reindexing `j ↦ u·j` of 2:F5) -/

end Frame

/-- The sum of `F` over a list of indices. -/
def sumList (F : Nat → Shell p) : List Nat → Shell p
  | [] => 0
  | a :: l => F a + sumList F l

/-- `[n−1, …, 0]`. -/
def listRange : Nat → List Nat
  | 0 => []
  | n + 1 => n :: listRange n

/-- `[σ (n−1), …, σ 0]`. -/
def imageList (σ : Nat → Nat) : Nat → List Nat
  | 0 => []
  | n + 1 => σ n :: imageList σ n

theorem sumList_imageList (F : Nat → Shell p) (σ : Nat → Nat) (n : Nat) :
    sumList F (imageList σ n) = sumRange (fun j => F (σ j)) n := by
  induction n with
  | zero => rfl
  | succ n ih => show F (σ n) + sumList F (imageList σ n) = sumRange (fun j => F (σ j)) n + F (σ n); rw [ih, add_comm]

theorem sumList_erase (F : Nat → Shell p) {v : Nat} : ∀ {l : List Nat}, Pigeonhole.mem v l →
    sumList F l = F v + sumList F (Pigeonhole.erase v l)
  | [], h => absurd h id
  | a :: l, h => by
    exact match Nat.decEq a v with
      | isTrue e => by rw [show Pigeonhole.erase v (a :: l) = l from if_pos e, e]; rfl
      | isFalse e => by
          rw [show Pigeonhole.erase v (a :: l) = a :: Pigeonhole.erase v l from if_neg e]
          have hm : Pigeonhole.mem v l := match h with
            | Or.inl h' => absurd h'.symm e
            | Or.inr h' => h'
          show F a + sumList F l = F v + (F a + sumList F (Pigeonhole.erase v l))
          rw [sumList_erase F hm, add_left_comm]

theorem imageList_length (σ : Nat → Nat) (n : Nat) : (imageList σ n).length = n := by
  induction n with
  | zero => rfl
  | succ n ih => show (imageList σ n).length + 1 = n + 1; rw [ih]

theorem mem_imageList {σ : Nat → Nat} {v : Nat} : ∀ {n : Nat}, Pigeonhole.mem v (imageList σ n) → ∃ j, j < n ∧ σ j = v
  | 0, h => absurd h id
  | n + 1, h => match h with
    | Or.inl e => ⟨n, Nat.lt_succ_self n, e.symm⟩
    | Or.inr h' => match mem_imageList h' with
      | ⟨j, hj, e⟩ => ⟨j, Nat.lt_succ_of_lt hj, e⟩

theorem imageList_nodup {σ : Nat → Nat} {n : Nat} (hinj : ∀ i j, i < n → j < n → σ i = σ j → i = j) :
    ∀ {m : Nat}, m ≤ n → Pigeonhole.NoDup (imageList σ m)
  | 0, _ => trivial
  | m + 1, hm => ⟨fun h => match mem_imageList h with
      | ⟨j, hj, e⟩ => Nat.lt_irrefl j (hinj j m (Nat.lt_of_lt_of_le hj (Nat.le_of_lt hm)) hm e ▸ hj),
    imageList_nodup hinj (Nat.le_of_lt hm)⟩

/-- A sum over any list of `n` distinct indices below `n` is the sum over `0, …, n−1`. -/
theorem sumList_eq_sumRange (F : Nat → Shell p) : ∀ (n : Nat) (l : List Nat), Pigeonhole.NoDup l →
    (∀ e, Pigeonhole.mem e l → e < n) → l.length = n → sumList F l = sumRange F n
  | 0, [], _, _, _ => rfl
  | 0, a :: l, _, hb, _ => absurd (hb a (Or.inl rfl)) (Nat.not_lt_zero a)
  | n + 1, l, hnd, hb, hlen => by
    have hm : Pigeonhole.mem n l := Pigeonhole.mem_of_nodup_of_length_lt (n + 1) l hnd hb hlen n (Nat.lt_succ_self n)
    rw [sumList_erase F hm, sumRange_succ, add_comm]
    have hb' : ∀ e, Pigeonhole.mem e (Pigeonhole.erase n l) → e < n := fun e he =>
      match Nat.lt_or_ge e n with
      | Or.inl hlt => hlt
      | Or.inr hge =>
        have : e = n := Nat.le_antisymm (Nat.le_of_lt_succ (hb e (Pigeonhole.mem_of_mem_erase he))) hge
        absurd (this ▸ he) (Pigeonhole.not_mem_erase_self n hnd)
    have hlen' : (Pigeonhole.erase n l).length = n := by
      have := Pigeonhole.length_erase_of_mem hm; rw [hlen] at this; exact Nat.succ.inj this
    rw [sumList_eq_sumRange F n (Pigeonhole.erase n l) (Pigeonhole.nodup_erase n hnd) hb' hlen']

/-- Permutation invariance: for `σ` injective on `[0, n)` with values below `n`,
`Σ_{j<n} F (σ j) = Σ_{l<n} F l`. -/
theorem sum_perm (F : Nat → Shell p) (σ : Nat → Nat) (n : Nat) (hlt : ∀ j, j < n → σ j < n)
    (hinj : ∀ i j, i < n → j < n → σ i = σ j → i = j) :
    sumRange (fun j => F (σ j)) n = sumRange F n := by
  rw [← sumList_imageList]
  exact sumList_eq_sumRange F n (imageList σ n) (imageList_nodup hinj (Nat.le_refl n))
    (fun e he => match mem_imageList he with | ⟨j, hj, e'⟩ => e' ▸ hlt j hj) (imageList_length σ n)

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
    rw [if_pos hk]⟩
  intro k hk
  show (if rev (p - 1) k ≤ 2 * κ then c (rev (p - 1) k) else c (rev (p - 1) (rev (p - 1) k)))
      = (if k ≤ 2 * κ then c k else c (rev (p - 1) k))
  rw [rev_rev hk]
  exact match Nat.decLe k (2 * κ), Nat.decLe (rev (p - 1) k) (2 * κ) with
    | isTrue h1, isTrue h2 => by
        rw [if_pos h1, if_pos h2]
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
    | isTrue h1, isFalse h2 => by rw [if_pos h1, if_neg h2]
    | isFalse h1, isTrue h2 => by rw [if_neg h1, if_pos h2]
    | isFalse h1, isFalse h2 => by
        rw [if_neg h1, if_neg h2]
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
      rw [if_neg (Nat.ne_of_gt hk0), if_neg (Nat.ne_of_lt hk2), if_pos hk2]⟩
  intro k hk
  have hn := F.n_pos
  show (if rev (p - 1) k = 0 then 0 else if rev (p - 1) k = 2 * κ then 0 else if rev (p - 1) k < 2 * κ then c (rev (p - 1) k) else -(c (rev (p - 1) (rev (p - 1) k))))
      = -(if k = 0 then 0 else if k = 2 * κ then 0 else if k < 2 * κ then c k else -(c (rev (p - 1) k)))
  match Nat.decEq k 0 with
  | isTrue e => rw [e, rev_zero _ hn, if_pos rfl, if_pos rfl, neg_zero]
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
      rw [if_neg hr0, if_pos this, if_neg e0, if_pos e, neg_zero]
    | isFalse e2 =>
      have hr2 : rev (p - 1) k ≠ 2 * κ := fun h => e2 (by
        have := rev_rev hk
        rw [h] at this
        rw [← this, rev_eq_sub F.two_kappa_lt F.two_kappa_pos, ← F.four_kappa, FRC.Nat.add_sub_cancel])
      rw [if_neg hr0, if_neg hr2, if_neg e0, if_neg e2]
      match Nat.lt_or_ge k (2 * κ) with
      | Or.inl hlt =>
        have hge : ¬ rev (p - 1) k < 2 * κ := fun h => by
          rw [hrk] at h
          have := Nat.add_lt_add h hlt
          rw [FRC.Nat.sub_add_cancel (Nat.le_of_lt hk), F.four_kappa] at this
          exact Nat.lt_irrefl _ this
        rw [if_neg hge, if_pos hlt, rev_rev hk]
      | Or.inr hge =>
        have hlt' : ¬ k < 2 * κ := Nat.not_lt_of_le hge
        have hgt : 2 * κ < k := Nat.lt_of_le_of_ne hge (fun e => e2 e.symm)
        have hr : rev (p - 1) k < 2 * κ := by
          rw [hrk]
          refine Nat.lt_of_add_lt_add_right (n := k) ?_
          rw [FRC.Nat.sub_add_cancel (Nat.le_of_lt hk), ← F.four_kappa]
          exact Nat.add_lt_add_left hgt _
        rw [if_pos hr, if_neg hlt', neg_neg]

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
