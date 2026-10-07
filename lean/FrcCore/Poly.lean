import FrcCore.Series

/-!
# FrcCore.Poly — polynomials over the shell and the root criterion (1:E3)

A polynomial is its coefficient sequence `Nat → Shell p` with a degree bound (`Bound f n`: the coefficients
beyond `n` vanish); equality is coefficientwise, so no function extensionality is needed.  The Cauchy
product, evaluation as a finite sum, the evaluation homomorphism (`eval_mul`, by a triangular reindexing of
sums), synthetic division by `X − a` at a root (`quot_linear_spec`), and the root bound over any shell without
zero divisors (a polynomial of degree `n` vanishing at `n + 1` distinct points is zero, `root_bound_of`).  No
axioms.

Since task LM22 the module stands on `Series.lean` alone, without the frame: the frame's root bound
(`Frame.root_bound`) and 1:E3's criterion (`root_iff_common_factor`) are in the numbers theme's
`Theme/Numbers.lean`, under their names.
-/

namespace FRC
namespace Shell

variable {p : Nat} [Pos p]

theorem sum_split (f : Nat → Shell p) (n k : Nat) :
    sumRange f (n + k) = sumRange f n + sumRange (fun t => f (n + t)) k := by
  induction k with
  | zero => rw [Nat.add_zero, sumRange_zero, add_zero]
  | succ k ih =>
    show sumRange f (n + k + 1) = _
    rw [sumRange_succ, sumRange_succ, ih, add_assoc]

/-- The triangular reindexing `Σ_{l<N} Σ_{j≤l} F j (l − j) = Σ_{j<N} Σ_{k<N−j} F j k`. -/
theorem sum_triangle (F : Nat → Nat → Shell p) (N : Nat) :
    sumRange (fun l => sumRange (fun j => F j (l - j)) (l + 1)) N =
    sumRange (fun j => sumRange (fun k => F j k) (N - j)) N := by
  induction N with
  | zero => rfl
  | succ N ih =>
    rw [sumRange_succ, ih, sumRange_succ (fun j => sumRange (fun k => F j k) (N + 1 - j)) N]
    have h1 : sumRange (fun j => sumRange (fun k => F j k) (N + 1 - j)) N =
        sumRange (fun j => sumRange (fun k => F j k) (N - j) + F j (N - j)) N := by
      apply sum_congr
      intro j hj
      show sumRange (fun k => F j k) (N + 1 - j) = sumRange (fun k => F j k) (N - j) + F j (N - j)
      have e : N + 1 - j = (N - j) + 1 := by
        have := FRC.Nat.add_sub_of_le (Nat.le_of_lt hj)
        -- this : j + (N - j) = N
        calc N + 1 - j = j + (N - j) + 1 - j := by rw [this]
          _ = (N - j) + 1 + j - j := by rw [Nat.add_comm j (N - j), Nat.add_right_comm (N - j) j 1]
          _ = (N - j) + 1 := FRC.Nat.add_sub_cancel _ _
      rw [e, sumRange_succ]
    rw [h1, sum_add]
    have e2 : N + 1 - N = 1 := FRC.Nat.add_sub_cancel_left N 1
    rw [e2, sumRange_succ (fun k => F N k) 0, sumRange_zero, zero_add,
      sumRange_succ (fun j => F j (N - j)) N, Nat.sub_self, add_assoc]

/-- A polynomial as its coefficient sequence. -/
abbrev Poly (p : Nat) [Pos p] := Nat → Shell p

namespace Poly

/-- `f` has degree at most `n`: the coefficients beyond `n` vanish. -/
def Bound (f : Poly p) (n : Nat) : Prop := ∀ i, n < i → f i = 0

/-- The Cauchy product `(f·g) i = Σ_{j ≤ i} f j · g (i − j)`. -/
def mul (f g : Poly p) : Poly p := fun i => sumRange (fun j => f j * g (i - j)) (i + 1)

/-- `f(a)` summed to the bound `n`: `Σ_{i ≤ n} f i · a^i`. -/
def eval (f : Poly p) (n : Nat) (a : Shell p) : Shell p := sumRange (fun i => f i * a ^ i) (n + 1)

/-- `X − a`. -/
def linear (a : Shell p) : Poly p
  | 0 => -a
  | 1 => 1
  | _ + 2 => 0

/-- `X^p − X`. -/
def xpx : Poly p := fun i => if i = p then 1 else if i = 1 then -1 else 0

theorem eval_congr {f h : Poly p} (e : ∀ i, f i = h i) (n : Nat) (a : Shell p) : eval f n a = eval h n a :=
  sum_congr (n + 1) (fun i _ => by show f i * a ^ i = h i * a ^ i; rw [e i])

theorem eval_bound {f : Poly p} {n N : Nat} (hf : Bound f n) (hN : n ≤ N) (a : Shell p) :
    eval f N a = eval f n a := by
  unfold eval
  have e : N + 1 = (n + 1) + (N - n) := by
    rw [Nat.add_right_comm, FRC.Nat.add_sub_of_le hN]
  rw [e, sum_split, sum_zero (N - n) (fun t _ => by
    show f (n + 1 + t) * a ^ (n + 1 + t) = 0
    rw [hf _ (Nat.lt_of_lt_of_le (Nat.lt_succ_self n) (Nat.le_add_right (n + 1) t)), zero_mul]), add_zero]

theorem mul_bound {d q : Poly p} {m k : Nat} (hd : Bound d m) (hq : Bound q k) : Bound (mul d q) (m + k) := by
  intro i hi
  apply sum_zero
  intro j hj
  show d j * q (i - j) = 0
  match Nat.decLe j m with
  | .isTrue hjm =>
    have : k < i - j := by
      apply FRC.Nat.le_sub_of_add_le
      -- k + 1 + j ≤ i  from  m + k < i and j ≤ m
      show k + 1 + j ≤ i
      calc k + 1 + j ≤ k + 1 + m := Nat.add_le_add_left hjm _
        _ = m + k + 1 := by rw [Nat.add_comm (k + 1) m, Nat.add_assoc]
        _ ≤ i := hi
    rw [hq _ this, mul_zero]
  | .isFalse hjm => rw [hd j (Nat.lt_of_not_le hjm), zero_mul]

/-- The evaluation is multiplicative: `(f·g)(a) = f(a)·g(a)`, with the bounds added. -/
theorem eval_mul {f g : Poly p} {n m : Nat} (hf : Bound f n) (hg : Bound g m) (a : Shell p) :
    eval (mul f g) (n + m) a = eval f n a * eval g m a := by
  unfold eval mul
  have h1 : sumRange (fun l => sumRange (fun j => f j * g (l - j)) (l + 1) * a ^ l) (n + m + 1) =
      sumRange (fun l => sumRange (fun j => f j * a ^ j * (g (l - j) * a ^ (l - j))) (l + 1)) (n + m + 1) := by
    apply sum_congr
    intro l _
    show sumRange (fun j => f j * g (l - j)) (l + 1) * a ^ l =
      sumRange (fun j => f j * a ^ j * (g (l - j) * a ^ (l - j))) (l + 1)
    rw [← sum_mul_right]
    apply sum_congr
    intro j hj
    show f j * g (l - j) * a ^ l = f j * a ^ j * (g (l - j) * a ^ (l - j))
    have : a ^ l = a ^ j * a ^ (l - j) := by rw [← pow_add, FRC.Nat.add_sub_of_le (Nat.le_of_lt_succ hj)]
    rw [this, mul_assoc, mul_assoc, mul_left_comm (g (l - j))]
  rw [h1, sum_triangle (fun j k => f j * a ^ j * (g k * a ^ k)) (n + m + 1)]
  have h2 : sumRange (fun j => sumRange (fun k => f j * a ^ j * (g k * a ^ k)) (n + m + 1 - j)) (n + m + 1) =
      sumRange (fun j => f j * a ^ j * sumRange (fun i => g i * a ^ i) (m + 1)) (n + m + 1) := by
    apply sum_congr
    intro j hj
    show sumRange (fun k => f j * a ^ j * (g k * a ^ k)) (n + m + 1 - j) =
      f j * a ^ j * sumRange (fun i => g i * a ^ i) (m + 1)
    rw [sum_mul_left]
    match Nat.decLe j n with
    | .isTrue hjn =>
      have e : n + m + 1 - j = (n + m - j) + 1 := by
        have := FRC.Nat.add_sub_of_le (Nat.le_trans hjn (Nat.le_add_right n m))
        calc n + m + 1 - j = j + (n + m - j) + 1 - j := by rw [this]
          _ = (n + m - j) + 1 + j - j := by rw [Nat.add_comm j (n + m - j), Nat.add_right_comm (n + m - j) j 1]
          _ = (n + m - j) + 1 := FRC.Nat.add_sub_cancel _ _
      rw [e]
      have hm : m ≤ n + m - j := by
        apply FRC.Nat.le_sub_of_add_le
        rw [Nat.add_comm n m]; exact Nat.add_le_add_left hjn m
      exact congrArg (f j * a ^ j * ·) (eval_bound hg hm a)
    | .isFalse hjn =>
      rw [hf j (Nat.lt_of_not_le hjn), zero_mul, zero_mul, zero_mul]
  rw [h2, sum_mul_right]
  exact congrArg (· * sumRange (fun i => g i * a ^ i) (m + 1)) (eval_bound hf (Nat.le_add_right n m) a)

theorem linear_bound (a : Shell p) : Bound (linear a) 1 := by
  intro i hi
  match i, hi with
  | _ + 2, _ => rfl

theorem mul_linear_zero (a : Shell p) (q : Poly p) : mul (linear a) q 0 = -(a * q 0) := by
  show sumRange (fun j => linear a j * q (0 - j)) 1 = _
  rw [sumRange_succ, sumRange_zero, zero_add]
  show -a * q 0 = -(a * q 0)
  exact (neg_mul a (q 0)).symm

theorem mul_linear_succ (a : Shell p) (q : Poly p) (i : Nat) :
    mul (linear a) q (i + 1) = q i + -(a * q (i + 1)) := by
  show sumRange (fun j => linear a j * q (i + 1 - j)) (i + 1 + 1) = _
  have e : i + 1 + 1 = 2 + i := Nat.add_comm i 2
  rw [e, sum_split, sum_zero i (fun t _ => by
    show linear a (2 + t) * q (i + 1 - (2 + t)) = 0
    rw [Nat.add_comm 2 t]
    show (0 : Shell p) * _ = 0
    exact zero_mul _), add_zero, sumRange_succ, sumRange_succ, sumRange_zero, zero_add]
  show -a * q (i + 1) + 1 * q i = q i + -(a * q (i + 1))
  rw [← neg_mul, one_mul, add_comm]

/-- The quotient of `f` (bound `n`) by `X − a`: `q i = Σ_{t < n − i} f (i + 1 + t) · a^t`. -/
def quotLinear (f : Poly p) (n : Nat) (a : Shell p) : Poly p :=
  fun i => sumRange (fun t => f (i + 1 + t) * a ^ t) (n - i)

/-- Synthetic division: at a root `a` of `f`, `f = (X − a)·q` with `q` of degree one less. -/
theorem quot_linear_spec {f : Poly p} {n : Nat} (hf : Bound f n) {a : Shell p} (ha : eval f n a = 0) :
    Bound (quotLinear f n a) (n - 1) ∧ ∀ i, f i = mul (linear a) (quotLinear f n a) i := by
  constructor
  · intro i hi
    have hni : n ≤ i := by
      match n, hi with
      | 0, _ => exact Nat.zero_le i
      | n' + 1, hi => exact Nat.succ_le_of_lt hi
    show sumRange (fun t => f (i + 1 + t) * a ^ t) (n - i) = 0
    rw [FRC.Nat.sub_eq_zero_of_le hni]
    rfl
  · intro i
    match i with
    | 0 =>
      rw [mul_linear_zero]
      -- f 0 + a · q 0 = f(a) = 0
      have e1 : n + 1 = 1 + n := Nat.add_comm n 1
      unfold eval at ha
      rw [e1, sum_split, sumRange_succ, sumRange_zero, zero_add] at ha
      have ha' : f 0 * a ^ 0 + sumRange (fun t => f (1 + t) * a ^ (1 + t)) n = 0 := ha
      rw [pow_zero, mul_one] at ha'
      have h2 : sumRange (fun t => f (1 + t) * a ^ (1 + t)) n = a * quotLinear f n a 0 := by
        show _ = a * sumRange (fun t => f (0 + 1 + t) * a ^ t) (n - 0)
        rw [← sum_mul_left]
        apply sum_congr
        intro t _
        show f (1 + t) * a ^ (1 + t) = a * (f (0 + 1 + t) * a ^ t)
        rw [pow_add, pow_one, mul_left_comm]
      rw [h2] at ha'
      exact eq_neg_of_add_eq_zero ha'
    | i + 1 =>
      rw [mul_linear_succ]
      match Nat.decLt i n with
      | .isTrue hin =>
        -- n − i = (n − (i + 1)) + 1
        have hk := FRC.Nat.add_sub_of_le (Nat.succ_le_of_lt hin)
        -- hk : i + 1 + (n - (i + 1)) = n
        have e : n - i = (n - (i + 1)) + 1 := by
          calc n - i = i + 1 + (n - (i + 1)) - i := by rw [hk]
            _ = i + ((n - (i + 1)) + 1) - i := by rw [Nat.add_assoc, Nat.add_comm 1]
            _ = (n - (i + 1)) + 1 := FRC.Nat.add_sub_cancel_left _ _
        show f (i + 1) = sumRange (fun t => f (i + 1 + t) * a ^ t) (n - i) +
          -(a * sumRange (fun t => f (i + 1 + 1 + t) * a ^ t) (n - (i + 1)))
        rw [e, Nat.add_comm (n - (i + 1)) 1, sum_split, sumRange_succ, sumRange_zero, zero_add]
        show f (i + 1) = f (i + 1 + 0) * a ^ 0 + sumRange (fun t => f (i + 1 + (1 + t)) * a ^ (1 + t)) (n - (i + 1)) +
          -(a * sumRange (fun t => f (i + 1 + 1 + t) * a ^ t) (n - (i + 1)))
        have h3 : sumRange (fun t => f (i + 1 + (1 + t)) * a ^ (1 + t)) (n - (i + 1)) =
            a * sumRange (fun t => f (i + 1 + 1 + t) * a ^ t) (n - (i + 1)) := by
          rw [← sum_mul_left]
          apply sum_congr
          intro t _
          show f (i + 1 + (1 + t)) * a ^ (1 + t) = a * (f (i + 1 + 1 + t) * a ^ t)
          rw [← Nat.add_assoc, pow_add, pow_one, mul_left_comm]
        rw [h3, Nat.add_zero, pow_zero, mul_one, add_assoc, add_neg, add_zero]
      | .isFalse hin =>
        have hni : n ≤ i := Nat.le_of_not_lt hin
        have z1 : n - i = 0 := FRC.Nat.sub_eq_zero_of_le hni
        have z2 : n - (i + 1) = 0 := FRC.Nat.sub_eq_zero_of_le (Nat.le_succ_of_le hni)
        show f (i + 1) = sumRange (fun t => f (i + 1 + t) * a ^ t) (n - i) +
          -(a * sumRange (fun t => f (i + 1 + 1 + t) * a ^ t) (n - (i + 1)))
        rw [z1, z2, sumRange_zero, sumRange_zero, mul_zero, neg_zero, add_zero]
        exact hf _ (Nat.lt_succ_of_le hni)

theorem eval_linear (a b : Shell p) : eval (linear a) 1 b = b + -a := by
  show sumRange (fun i => linear a i * b ^ i) 2 = _
  rw [sumRange_succ, sumRange_succ, sumRange_zero, zero_add]
  show -a * b ^ 0 + 1 * b ^ 1 = b + -a
  rw [pow_zero, mul_one, pow_one, one_mul, add_comm]

theorem eval_mul_linear {q : Poly p} {n : Nat} (hq : Bound q n) (a b : Shell p) :
    eval (mul (linear a) q) (n + 1) b = (b + -a) * eval q n b := by
  rw [Nat.add_comm n 1, eval_mul (linear_bound a) hq, eval_linear]

/-- The root bound over any shell without zero divisors (task LM22): a polynomial of degree at most `n` that
vanishes at `n + 1` distinct points is zero. `Frame.root_bound` is its case of a frame; the prime shell's
(`Theme/Field`) needs no generator. -/
theorem root_bound_of (hzd : ∀ {a b : Shell p}, a * b = 0 → a = 0 ∨ b = 0) : ∀ (n : Nat) (f : Poly p), Bound f n →
    ∀ (r : Nat → Shell p), (∀ i j, i ≤ n → j ≤ n → r i = r j → i = j) → (∀ i, i ≤ n → eval f n (r i) = 0) →
    ∀ i, f i = 0 := by
  intro n
  induction n with
  | zero =>
    intro f hf r _ hroot i
    have h0 := hroot 0 (Nat.le_refl 0)
    unfold eval at h0
    rw [sumRange_succ, sumRange_zero, zero_add] at h0
    have h0' : f 0 * r 0 ^ 0 = 0 := h0
    rw [pow_zero, mul_one] at h0'
    match i with
    | 0 => exact h0'
    | i + 1 => exact hf _ (Nat.zero_lt_succ i)
  | succ n ih =>
    intro f hf r hinj hroot
    have ha := hroot 0 (Nat.zero_le _)
    have spec := quot_linear_spec hf ha
    have hq : Bound (quotLinear f (n + 1) (r 0)) n := spec.1
    have hf' : ∀ b, eval f (n + 1) b = (b + -(r 0)) * eval (quotLinear f (n + 1) (r 0)) n b := fun b => by
      rw [eval_congr spec.2, eval_mul_linear hq]
    have hz : ∀ i, quotLinear f (n + 1) (r 0) i = 0 := by
      apply ih _ hq (fun k => r (k + 1))
      · intro i j hi hj e
        exact Nat.succ.inj (hinj (i + 1) (j + 1) (Nat.succ_le_succ hi) (Nat.succ_le_succ hj) e)
      · intro k hk
        have h := hroot (k + 1) (Nat.succ_le_succ hk)
        rw [hf'] at h
        match hzd h with
        | .inl e =>
          have : r (k + 1) = r 0 := by
            calc r (k + 1) = r (k + 1) + 0 := (add_zero _).symm
              _ = r (k + 1) + (-(r 0) + r 0) := by rw [neg_add]
              _ = (r (k + 1) + -(r 0)) + r 0 := (add_assoc _ _ _).symm
              _ = r 0 := by rw [e, zero_add]
          exact absurd (hinj (k + 1) 0 (Nat.succ_le_succ hk) (Nat.zero_le _) this) (FRC.Nat.succ_ne_zero k)
        | .inr e => exact e
    intro i
    rw [spec.2 i]
    match i with
    | 0 => rw [mul_linear_zero, hz, mul_zero, neg_zero]
    | i + 1 => rw [mul_linear_succ, hz, hz, mul_zero, neg_zero, add_zero]

namespace Frame

theorem ofNat_inj_lt {i j : Nat} (hi : i < p) (hj : j < p) (h : (ofNat i : Shell p) = ofNat j) : i = j := by
  have := val_injective h
  rw [val_ofNat, val_ofNat, FRC.Nat.mod_eq_of_lt hi, FRC.Nat.mod_eq_of_lt hj] at this
  exact this

end Frame
end Poly
end Shell
end FRC
