import FrcCore.Series
import FrcCore.Poly

/-!
# FrcCore.Theme.Field — the prime shell is a field, without a generator (the foundation theme, tasks LM22 and LM24)

The shell `𝔽_p` of a prime `p` (`FRC.Nat.isPrime`, trial division), with no drive assumed, on `Series.lean` and
`Poly.lean` alone: Euclid's lemma; no zero divisors, cancellation and the square roots of one; Fermat's
little theorem by the permutation `x ↦ a x` of the nonzero residues (`prod_perm`); the roots of `x^m − 1`, bounded by
the degree, so some residue escapes `x^m = 1` for `m < p − 1`; hence a residue `a` with `a^{(p−1)/2} = −1`, and the
quarter-turn criterion: `x² = −1` is solvable iff `p ≡ 1 (mod 4)`, with `ħ = a^S` on `p = 4S + 1`; a shell without
zero divisors is prime; and the chart `p = 4S + 1`: the octant sector, the half-square and the parity flip. Task LM24
split this file from `Theme/Foundation.lean` under the size budget (G10), so that the programme themes take the field
without the foundation's rows; every name is unchanged. No axioms.
-/

namespace FRC

namespace Nat

theorem mod_eq_zero_of_add {a r p : Nat} (hp : 0 < p) (h : (a + r) % p = 0) (ha : a % p = 0) : r % p = 0 := by
  rw [FRC.Nat.add_mod _ _ _ hp, ha, Nat.zero_add, FRC.Nat.mod_mod _ _ hp] at h
  exact h

theorem mul_mod_eq_zero_left {a b p : Nat} (hp : 0 < p) (ha : a % p = 0) : (a * b) % p = 0 := by
  rw [FRC.Nat.mul_mod_left' _ _ _ hp, ha, Nat.zero_mul]; rfl

/-- Euclid's lemma, the step: for a prime `p` and `p ∤ b`, no `k` with `0 < k < p` has `p ∣ k b`. If `p ∣ k b` with
`2 ≤ k`, write `p = q k + r`: `p ∤ k` gives `0 < r < k`, and `r b = p b − q (k b)` is again divisible by `p`. -/
theorem prime_not_dvd_mul_aux {p b : Nat} (hp : isPrime p) (hb : b % p ≠ 0) :
    ∀ n k, k < n → 0 < k → k < p → (k * b) % p ≠ 0 := by
  have hp0 : 0 < p := Nat.lt_of_lt_of_le (Nat.zero_lt_succ 1) hp.1
  intro n
  induction n with
  | zero => intro k hk; exact absurd hk (Nat.not_lt_zero k)
  | succ n ih =>
    intro k hk hk0 hkp hkb
    match k, hk, hk0, hkp, hkb with
    | 0, _, hk0, _, _ => exact absurd hk0 (Nat.lt_irrefl 0)
    | 1, _, _, _, hkb => rw [Nat.one_mul] at hkb; exact hb hkb
    | k + 2, hk, _, hkp, hkb =>
      have hk2 : 0 < k + 2 := Nat.zero_lt_succ _
      have hpk : p % (k + 2) ≠ 0 := hp.2 (k + 2) hkp (Nat.le_add_left 2 k)
      obtain ⟨q, hq⟩ := FRC.Nat.mod_spec (k + 2) hk2 p
      have hr : p % (k + 2) < k + 2 := Nat.mod_lt _ hk2
      have e : p * b = (k + 2) * b * q + p % (k + 2) * b := by
        calc p * b = ((k + 2) * q + p % (k + 2)) * b := by rw [← hq]
          _ = (k + 2) * q * b + p % (k + 2) * b := FRC.Nat.add_mul _ _ _
          _ = (k + 2) * b * q + p % (k + 2) * b := by
              rw [FRC.Nat.mul_assoc, Nat.mul_comm q b, ← FRC.Nat.mul_assoc]
      have hpb : (p * b) % p = 0 := mul_mod_eq_zero_left hp0 (FRC.Nat.mod_self p hp0)
      have hA : ((k + 2) * b * q) % p = 0 := mul_mod_eq_zero_left hp0 hkb
      have hR : (p % (k + 2) * b) % p = 0 := mod_eq_zero_of_add hp0 (e ▸ hpb) hA
      exact ih (p % (k + 2)) (Nat.lt_of_lt_of_le hr (Nat.le_of_lt_succ hk)) (Nat.pos_of_ne_zero hpk)
        (Nat.lt_trans hr hkp) hR

/-- Euclid's lemma: a prime dividing a product divides a factor. -/
theorem prime_mul_mod {p a b : Nat} (hp : isPrime p) (h : (a * b) % p = 0) : a % p = 0 ∨ b % p = 0 := by
  have hp0 : 0 < p := Nat.lt_of_lt_of_le (Nat.zero_lt_succ 1) hp.1
  match Nat.decEq (b % p) 0 with
  | .isTrue hb => exact .inr hb
  | .isFalse hb =>
    match Nat.decEq (a % p) 0 with
    | .isTrue ha => exact .inl ha
    | .isFalse ha =>
      have h' : (a % p * b) % p = 0 := by rw [FRC.Nat.mod_mul_mod _ _ _ hp0]; exact h
      exact absurd h' (prime_not_dvd_mul_aux hp hb (a % p + 1) (a % p) (Nat.lt_succ_self _)
        (Nat.pos_of_ne_zero ha) (Nat.mod_lt _ hp0))

/-- `d ∣ n` iff `n % d = 0`. -/
theorem dvd_iff_mod {d n : Nat} (hd : 0 < d) : d ∣ n ↔ n % d = 0 :=
  ⟨fun ⟨c, hc⟩ => FRC.Nat.mod_unique hd (by rw [Nat.add_zero]; exact hc),
   fun h => match FRC.Nat.mod_spec d hd n with
     | ⟨q, hq⟩ => ⟨q, by rw [h, Nat.add_zero] at hq; exact hq⟩⟩

/-- Parity: `n % 2` is `0` or `1`. -/
theorem mod_two_cases (n : Nat) : n % 2 = 0 ∨ n % 2 = 1 := by
  have h := Nat.mod_lt n (Nat.zero_lt_succ 1)
  match n % 2, h with
  | 0, _ => exact .inl rfl
  | 1, _ => exact .inr rfl
  | k + 2, h => exact absurd h (Nat.not_lt_of_le (Nat.le_add_left 2 k))

theorem succ_lt_of_lt_pred {j n : Nat} (h : j < n - 1) : j + 1 < n := by
  match n, h with
  | 0, h => exact absurd h (Nat.not_lt_zero j)
  | n + 1, h => rw [FRC.Nat.add_sub_cancel] at h; exact Nat.succ_lt_succ h

theorem pred_lt_pred {v n : Nat} (hv : 0 < v) (h : v < n) : v - 1 < n - 1 := by
  match v, n, hv, h with
  | 0, _, hv, _ => exact absurd hv (Nat.lt_irrefl 0)
  | v + 1, 0, _, h => exact absurd h (Nat.not_lt_zero _)
  | v + 1, n + 1, _, h => rw [FRC.Nat.add_sub_cancel, FRC.Nat.add_sub_cancel]; exact Nat.lt_of_succ_lt_succ h

theorem eq_of_pred_eq {u v : Nat} (hu : 0 < u) (hv : 0 < v) (h : u - 1 = v - 1) : u = v := by
  rw [← FRC.Nat.sub_add_cancel hu, ← FRC.Nat.sub_add_cancel hv, h]

/-- An odd number is no sum of two numbers of equal parity. -/
theorem parity_split {a b n : Nat} (h : a + b = 2 * n + 1) : a % 2 = 0 ↔ ¬ b % 2 = 0 := by
  have h2 : (0 : Nat) < 2 := Nat.zero_lt_succ 1
  have hodd : (a + b) % 2 = 1 := by rw [h, FRC.Nat.add_mul_mod_self_left 1 n 2 h2]
  rw [FRC.Nat.add_mod _ _ _ h2] at hodd
  constructor
  · intro ha hb; rw [ha, hb] at hodd; exact absurd hodd (by decide)
  · intro hb
    match mod_two_cases a, mod_two_cases b with
    | .inl ha, _ => exact ha
    | .inr _, .inl hb' => exact absurd hb' hb
    | .inr ha, .inr hb' => rw [ha, hb'] at hodd; exact absurd hodd (by decide)

end Nat

namespace Shell

variable {p : Nat} [Pos p]

/-! ## The polynomial `X^n − 1` -/

namespace Poly

/-- `X^n − 1`, for `n ≥ 1`. -/
def xn1 (n : Nat) : Poly p := fun i => if i = n then 1 else if i = 0 then -1 else 0

theorem xn1_bound (n : Nat) : Bound (xn1 n : Poly p) n := fun i hi => by
  show (if i = n then 1 else if i = 0 then -1 else 0 : Shell p) = 0
  rw [ite_eq_right (Nat.ne_of_gt hi), ite_eq_right (Nat.ne_of_gt (Nat.lt_of_le_of_lt (Nat.zero_le n) hi))]

theorem xn1_top (n : Nat) : (xn1 n : Poly p) n = 1 := by
  show (if n = n then 1 else if n = 0 then -1 else 0 : Shell p) = 1
  rw [ite_eq_left rfl]

theorem eval_xn1 {n : Nat} (hn : 0 < n) (a : Shell p) : eval (xn1 n : Poly p) n a = a ^ n + -1 := by
  unfold eval
  rw [sumRange_succ, sum_eq_single hn (fun l hl hne => by
    show (if l = n then 1 else if l = 0 then -1 else 0 : Shell p) * a ^ l = 0
    rw [ite_eq_right (Nat.ne_of_lt hl), ite_eq_right hne, zero_mul])]
  show (if 0 = n then 1 else if 0 = 0 then -1 else 0 : Shell p) * a ^ 0 + xn1 n n * a ^ n = a ^ n + -1
  rw [ite_eq_right (Nat.ne_of_lt hn), ite_eq_left rfl, xn1_top, pow_zero, mul_one, one_mul, add_comm]

end Poly

namespace Prime

/-! ## The prime shell is a field: no zero divisors, cancellation, the square roots of one -/

omit [Pos p] in
theorem one_lt (hp : FRC.Nat.isPrime p) : 1 < p := hp.1

theorem one_ne_zero (hp : FRC.Nat.isPrime p) : (1 : Shell p) ≠ 0 := fun h => by
  have := val_injective h
  rw [val_one, val_zero, FRC.Nat.mod_eq_of_lt (one_lt hp)] at this
  exact Nat.noConfusion this

theorem eq_zero_of_val_mod {a : Shell p} (h : a.val % p = 0) : a = 0 :=
  ext (by rw [← FRC.Nat.mod_eq_of_lt a.lt]; exact h)

/-- No zero divisors on a prime shell (Euclid's lemma on the representatives). -/
theorem mul_eq_zero (hp : FRC.Nat.isPrime p) {a b : Shell p} (h : a * b = 0) : a = 0 ∨ b = 0 :=
  match FRC.Nat.prime_mul_mod hp (val_injective h) with
  | .inl ha => .inl (eq_zero_of_val_mod ha)
  | .inr hb => .inr (eq_zero_of_val_mod hb)

theorem mul_ne_zero (hp : FRC.Nat.isPrime p) {a b : Shell p} (ha : a ≠ 0) (hb : b ≠ 0) : a * b ≠ 0 :=
  fun h => match mul_eq_zero hp h with
    | .inl e => ha e
    | .inr e => hb e

theorem eq_of_sub_eq_zero {b c : Shell p} (e : b + -c = 0) : b = c :=
  calc b = b + 0 := (add_zero b).symm
    _ = b + (-c + c) := by rw [neg_add]
    _ = (b + -c) + c := (add_assoc _ _ _).symm
    _ = c := by rw [e, zero_add]

/-- Cancellation: `a b = a c` with `a ≠ 0` gives `b = c`. -/
theorem mul_left_cancel (hp : FRC.Nat.isPrime p) {a b c : Shell p} (ha : a ≠ 0) (h : a * b = a * c) : b = c := by
  have : a * (b + -c) = 0 := by rw [left_distrib, ← mul_neg, h, add_neg]
  match mul_eq_zero hp this with
  | .inl e => exact absurd e ha
  | .inr e => exact eq_of_sub_eq_zero e

/-- The square roots of a square are `±` its root: `x² = y²` gives `x = y` or `x = −y`. -/
theorem sq_eq_sq (hp : FRC.Nat.isPrime p) {x y : Shell p} (h : x * x = y * y) : x = y ∨ x = -y := by
  have e : (x + -y) * (x + y) = 0 := by
    rw [right_distrib, left_distrib, left_distrib, ← neg_mul, ← neg_mul, mul_comm y x, ← h,
      add_comm (-(x * y)) (-(x * x)), add_add_add_comm, add_neg, add_neg, add_zero]
  match mul_eq_zero hp e with
  | .inl e1 => exact .inl (eq_of_sub_eq_zero e1)
  | .inr e2 => exact .inr (eq_neg_of_add_eq_zero e2)

/-- The square roots of one are `±1`. -/
theorem sq_eq_one (hp : FRC.Nat.isPrime p) {x : Shell p} (h : x * x = 1) : x = 1 ∨ x = -1 :=
  sq_eq_sq hp (h.trans (mul_one 1).symm)

/-! ## Fermat's little theorem without a generator -/

theorem val_pos {a : Shell p} (h : a ≠ 0) : 0 < a.val := Nat.pos_of_ne_zero (fun e => h (ext e))

theorem ofNat_ne_zero {k : Nat} (hk0 : 0 < k) (hk : k < p) : (ofNat k : Shell p) ≠ 0 := fun h => by
  have := val_injective h
  rw [val_ofNat, val_zero, FRC.Nat.mod_eq_of_lt hk] at this
  exact Nat.ne_of_gt hk0 this

theorem prodRange_ne_zero (hp : FRC.Nat.isPrime p) {f : Nat → Shell p} :
    ∀ n, (∀ j, j < n → f j ≠ 0) → prodRange f n ≠ 0
  | 0, _ => one_ne_zero hp
  | n + 1, h => mul_ne_zero hp (prodRange_ne_zero hp n (fun j hj => h j (Nat.lt_succ_of_lt hj))) (h n (Nat.lt_succ_self n))

/-- The nonzero residues `1, …, p − 1`, indexed from `0`. -/
def nonzero (j : Nat) : Shell p := ofNat (j + 1)

/-- Where multiplication by `a` sends the `j`-th nonzero residue. -/
def nonzeroIndex (a : Shell p) (j : Nat) : Nat := (a * nonzero j).val - 1

theorem nonzero_ne_zero {j : Nat} (hj : j < p - 1) : (nonzero j : Shell p) ≠ 0 :=
  ofNat_ne_zero (Nat.zero_lt_succ j) (FRC.Nat.succ_lt_of_lt_pred hj)

/-- Fermat's little theorem, generator-free: `a^{p−1} = 1` for `a ≠ 0`. Multiplication by `a` permutes the nonzero
residues, so `a^{p−1} · Π u = Π u`, and the product, nonzero, cancels. -/
theorem fermat (hp : FRC.Nat.isPrime p) {a : Shell p} (ha : a ≠ 0) : a ^ (p - 1) = 1 := by
  have hv : ∀ j, j < p - 1 → 0 < (a * nonzero j).val := fun j hj =>
    val_pos (mul_ne_zero hp ha (nonzero_ne_zero hj))
  have hlt : ∀ j, j < p - 1 → nonzeroIndex a j < p - 1 := fun j hj =>
    FRC.Nat.pred_lt_pred (hv j hj) (a * nonzero j).lt
  have hinj : ∀ i j, i < p - 1 → j < p - 1 → nonzeroIndex a i = nonzeroIndex a j → i = j := fun i j hi hj e => by
    have e2 : (nonzero i : Shell p) = nonzero j :=
      mul_left_cancel hp ha (ext (FRC.Nat.eq_of_pred_eq (hv i hi) (hv j hj) e))
    exact Nat.succ.inj (Poly.Frame.ofNat_inj_lt (FRC.Nat.succ_lt_of_lt_pred hi) (FRC.Nat.succ_lt_of_lt_pred hj) e2)
  have hF : ∀ j, j < p - 1 → nonzero (nonzeroIndex a j) = a * nonzero j := fun j hj => by
    show ofNat ((a * nonzero j).val - 1 + 1) = a * nonzero j
    rw [FRC.Nat.sub_add_cancel (hv j hj), ofNat_val]
  have hperm := prod_perm (nonzero : Nat → Shell p) (nonzeroIndex a) (p - 1) hlt hinj
  rw [prodRange_congr (p - 1) hF, prodRange_mul_left] at hperm
  have hP := prodRange_ne_zero hp (f := (nonzero : Nat → Shell p)) (p - 1) (fun j hj => nonzero_ne_zero hj)
  exact mul_left_cancel hp hP (by rw [mul_comm, hperm, mul_one])

omit [Pos p] in
theorem two_le (hp : FRC.Nat.isPrime p) : 2 ≤ p := hp.1

/-- On a shell of more than two residues, `−1 ≠ 1`. -/
theorem neg_one_ne_one (h2 : 2 < p) : (-1 : Shell p) ≠ 1 := fun e => by
  have h : (1 : Shell p) + 1 = 0 :=
    calc (1 : Shell p) + 1 = -1 + 1 := by rw [e]
      _ = 0 := neg_add 1
  have v := val_injective h
  change (1 % p + 1 % p) % p = 0 at v
  rw [FRC.Nat.mod_eq_of_lt (Nat.lt_trans (Nat.lt_succ_self 1) h2)] at v
  change 2 % p = 0 at v
  rw [FRC.Nat.mod_eq_of_lt h2] at v
  exact absurd v (by decide)

theorem ne_zero_of_mul_self {h c : Shell p} (hc : c ≠ 0) (hh : h * h = c) : h ≠ 0 := fun e => by
  rw [e, zero_mul] at hh; exact hc hh.symm

theorem neg_one_ne_zero (hp : FRC.Nat.isPrime p) : (-1 : Shell p) ≠ 0 := fun e => by
  have : (1 : Shell p) = 0 := by rw [← neg_neg (1 : Shell p), e, neg_zero]
  exact one_ne_zero hp this

/-- The order divides the period: `z^d = 1` gives `z^{(p−1) mod d} = 1`. -/
theorem pow_mod_eq_one (hp : FRC.Nat.isPrime p) {z : Shell p} (hz : z ≠ 0) {d : Nat} (hd0 : 0 < d)
    (hd : z ^ d = 1) : z ^ ((p - 1) % d) = 1 := by
  obtain ⟨q, hq⟩ := FRC.Nat.mod_spec d hd0 (p - 1)
  have h := fermat hp hz
  rw [hq, pow_add, pow_mul, hd, one_pow, one_mul] at h
  exact h

/-! ## The roots of `X^m − 1`, and the residues they miss -/

/-- Some nonzero residue escapes `x^m = 1` when `0 < m < p − 1`: else `X^m − 1` had `m + 1` roots. -/
theorem exists_pow_ne_one (hp : FRC.Nat.isPrime p) {m : Nat} (hm : 0 < m) (hlt : m < p - 1) :
    ∃ a : Shell p, a ≠ 0 ∧ a ^ m ≠ 1 :=
  match decExistsLT (fun j => (nonzero j : Shell p) ^ m ≠ 1) (p - 1) with
  | .isTrue ⟨j, hj, h⟩ => ⟨nonzero j, nonzero_ne_zero hj, h⟩
  | .isFalse hno => by
    have hm1 : m + 1 < p := FRC.Nat.succ_lt_of_lt_pred hlt
    have hone : ∀ i, i ≤ m → (nonzero i : Shell p) ^ m = 1 := fun i hi =>
      match decEq ((nonzero i : Shell p) ^ m) 1 with
      | .isTrue e => e
      | .isFalse ne => absurd ⟨i, Nat.lt_of_le_of_lt hi hlt, ne⟩ hno
    have hz := Poly.root_bound_of (fun h => mul_eq_zero hp h) m (Poly.xn1 m) (Poly.xn1_bound m) (nonzero : Nat → Shell p)
      (fun i j hi hj e => Nat.succ.inj (Poly.Frame.ofNat_inj_lt (Nat.lt_of_le_of_lt (Nat.succ_le_succ hi) hm1)
        (Nat.lt_of_le_of_lt (Nat.succ_le_succ hj) hm1) e))
      (fun i hi => by rw [Poly.eval_xn1 hm, hone i hi, add_neg]) m
    rw [Poly.xn1_top] at hz
    exact absurd hz (one_ne_zero hp)

/-- On an odd prime `p = 2n + 1`, some residue has `aⁿ = −1`: a non-square, by Fermat and `x² = 1 ⇒ x = ±1`. -/
theorem exists_pow_half (hp : FRC.Nat.isPrime p) {n : Nat} (hn : p = 2 * n + 1) : ∃ a : Shell p, a ^ n = -1 := by
  have hn0 : 0 < n := by
    match n, hn with
    | 0, hn => have h := hp.1; rw [hn] at h; exact absurd h (by decide)
    | k + 1, _ => exact Nat.zero_lt_succ k
  have hp1 : p - 1 = n + n := by rw [hn, FRC.Nat.add_sub_cancel, Nat.two_mul]
  have hlt : n < p - 1 := by rw [hp1]; exact Nat.lt_add_of_pos_right hn0
  obtain ⟨a, ha, han⟩ := exists_pow_ne_one hp hn0 hlt
  have hsq : a ^ n * a ^ n = 1 := by rw [← pow_add, ← hp1, fermat hp ha]
  exact ⟨a, match sq_eq_one hp hsq with
    | .inl e => absurd e han
    | .inr e => e⟩

/-! ## The quarter-turn criterion: `−1` is a square iff `p ≡ 1 (mod 4)` -/

/-- The quarter-turn on the chart `p = 4S + 1`, generator-free: `ħ = a^S` with `a^{2S} = −1`. -/
theorem exists_quarter_turn (hp : FRC.Nat.isPrime p) {S : Nat} (hS : p = 4 * S + 1) :
    ∃ h : Shell p, h * h = -1 := by
  obtain ⟨a, ha⟩ := exists_pow_half hp (n := 2 * S) (by rw [hS, ← FRC.Nat.mul_assoc])
  exact ⟨a ^ S, by rw [← pow_add, ← Nat.two_mul, ha]⟩

/-- The quarter-turn criterion on a prime `p > 2`: `x² = −1` is solvable iff `p ≡ 1 (mod 4)`. Forward, `ħ⁴ = 1`
and `ħ^{(p−1) mod 4} = 1` leave only `(p − 1) mod 4 = 0`; backward, the chart. -/
theorem quarter_turn_iff (hp : FRC.Nat.isPrime p) (h2 : 2 < p) : (∃ h : Shell p, h * h = -1) ↔ p % 4 = 1 := by
  constructor
  · intro ⟨h, hh⟩
    have h0 : h ≠ 0 := ne_zero_of_mul_self (neg_one_ne_zero hp) hh
    have h4 : h ^ 4 = 1 := by
      rw [show (4 : Nat) = 2 + 2 from rfl, pow_add, pow_two, hh, neg_mul_neg, mul_one]
    have hcase : (p - 1) % 4 = 0 := by
      have hr := pow_mod_eq_one hp h0 (by decide : 0 < 4) h4
      have hlt := Nat.mod_lt (p - 1) (by decide : 0 < 4)
      generalize (p - 1) % 4 = r at hr hlt
      match r, hr, hlt with
      | 0, _, _ => rfl
      | 1, hr, _ => rw [pow_one] at hr; rw [hr, mul_one] at hh; exact absurd hh.symm (neg_one_ne_one h2)
      | 2, hr, _ => rw [pow_two, hh] at hr; exact absurd hr (neg_one_ne_one h2)
      | 3, hr, _ =>
        rw [show (4 : Nat) = 3 + 1 from rfl, pow_succ, hr, one_mul] at h4
        rw [h4, mul_one] at hh; exact absurd hh.symm (neg_one_ne_one h2)
      | k + 4, _, hlt => exact absurd hlt (Nat.not_lt_of_le (Nat.le_add_left 4 k))
    obtain ⟨q, hq⟩ := FRC.Nat.mod_spec 4 (by decide) (p - 1)
    rw [hcase, Nat.add_zero] at hq
    exact FRC.Nat.mod_unique (by decide)
      (by rw [← hq, FRC.Nat.sub_add_cancel (Nat.le_of_lt (Nat.lt_trans (Nat.lt_succ_self 1) h2))])
  · intro h4
    obtain ⟨S, hS⟩ := FRC.Nat.mod_spec 4 (by decide) p
    rw [h4] at hS
    exact exists_quarter_turn hp hS

/-! ## A shell without zero divisors is prime -/

theorem ofNat_mul (a b : Nat) : (ofNat a * ofNat b : Shell p) = ofNat (a * b) :=
  ext (by show (a % p * (b % p)) % p = (a * b) % p; rw [← FRC.Nat.mul_mod _ _ _ Pos.pos])

theorem ofNat_self : (ofNat p : Shell p) = 0 := ext (FRC.Nat.mod_self p Pos.pos)

/-- A shell of at least two residues without zero divisors is prime: a factorisation `p = d q` with `2 ≤ d < p`
makes `d · q = 0` with both factors nonzero. -/
theorem isPrime_of_no_zero_divisors (h2 : 2 ≤ p) (hz : ∀ {a b : Shell p}, a * b = 0 → a = 0 ∨ b = 0) :
    FRC.Nat.isPrime p := by
  refine ⟨h2, fun d hdp hd2 hmod => ?_⟩
  have hd0 : 0 < d := Nat.lt_of_lt_of_le (Nat.zero_lt_succ 1) hd2
  obtain ⟨q, hq⟩ := FRC.Nat.mod_spec d hd0 p
  rw [hmod, Nat.add_zero] at hq
  have hq0 : 0 < q := by
    match q, hq with
    | 0, hq => rw [Nat.mul_zero] at hq; rw [hq] at h2; exact absurd h2 (by decide)
    | k + 1, _ => exact Nat.zero_lt_succ k
  have hqp : q < p := by
    have h1 : 1 * q < d * q := FRC.Nat.mul_lt_mul_of_lt_of_pos (Nat.lt_of_lt_of_le (Nat.lt_succ_self 1) hd2) hq0
    rw [Nat.one_mul, ← hq] at h1; exact h1
  have e : (ofNat d * ofNat q : Shell p) = 0 := by rw [ofNat_mul, ← hq, ofNat_self]
  match hz e with
  | .inl e1 => exact ofNat_ne_zero hd0 hdp e1
  | .inr e2 => exact ofNat_ne_zero hq0 hqp e2

/-- Completeness is primality: for `p ≥ 2`, the shell has no zero divisors iff `p` is prime. -/
theorem isPrime_iff_no_zero_divisors (h2 : 2 ≤ p) :
    FRC.Nat.isPrime p ↔ ∀ a b : Shell p, a * b = 0 → a = 0 ∨ b = 0 :=
  ⟨fun hp _ _ h => mul_eq_zero hp h, fun hz => isPrime_of_no_zero_divisors h2 (fun h => hz _ _ h)⟩

/-! ## The chart `p = 4S + 1`: the octant sector, the half-square and the parity flip (moved from the Carrier's
theme by task LM24, so that every programme theme stands on them without the Carrier; `FRC.Carrier` keeps the old
names) -/

omit [Pos p] in
theorem chart_gt_two (hp : FRC.Nat.isPrime p) {S : Nat} (hS : p = 4 * S + 1) : 2 < p := by
  match S, hS with
  | 0, hS => have h := hp.1; rw [hS] at h; exact absurd h (by decide)
  | k + 1, hS =>
    rw [hS, Nat.left_distrib]
    exact Nat.lt_of_lt_of_le (by decide : 2 < 5) (Nat.le_add_left 5 (4 * k))

/-- `2 = 1 + 1` on every shell. -/
theorem two_eq : (2 : Shell p) = 1 + 1 :=
  ext (by show 2 % p = (1 % p + 1 % p) % p; rw [← FRC.Nat.add_mod _ _ _ Pos.pos])

/-- `a + 1 + (1 − a) = 1 + 1`. -/
theorem add_one_add_one_neg (a : Shell p) : a + 1 + (1 + -a) = 1 + 1 := by
  rw [add_assoc, ← add_assoc 1 1 (-a), add_comm (1 + 1) (-a), ← add_assoc a (-a) (1 + 1), add_neg, zero_add]

/-- The octant sector: on the chart `p = 4S + 1`, an element of order eight (`ζ⁸ = 1`,
`ζ⁴ ≠ 1`) exists iff `S` is even: `C₈ ⊂ C_{4S}` exactly when `8 ∣ 4S`. Forward, `ζ⁴ = −1` and Fermat give
`ζ^{4S} = 1`, which an odd `S = 2m + 1` turns into `ζ⁴ = 1`; backward, `ζ = a^{S/2}` with `a^{2S} = −1`. -/
theorem octant_sector (hp : FRC.Nat.isPrime p) {S : Nat} (hS : p = 4 * S + 1) :
    (∃ ζ : Shell p, ζ ^ 8 = 1 ∧ ζ ^ 4 ≠ 1) ↔ S % 2 = 0 := by
  have h2 := chart_gt_two hp hS
  constructor
  · intro ⟨ζ, h8, h4⟩
    have hz0 : ζ ≠ 0 := fun e => by
      rw [e, show (8 : Nat) = 7 + 1 from rfl, pow_succ, mul_zero] at h8; exact one_ne_zero hp h8.symm
    have h4' : ζ ^ 4 = -1 :=
      match sq_eq_one hp (by rw [← pow_add]; exact h8 : ζ ^ 4 * ζ ^ 4 = 1) with
      | .inl e => absurd e h4
      | .inr e => e
    match FRC.Nat.mod_two_cases S with
    | .inl e => exact e
    | .inr e =>
      obtain ⟨m, hm⟩ := FRC.Nat.mod_spec 2 (by decide) S
      rw [e] at hm
      have hf := fermat hp hz0
      have hp1 : p - 1 = 8 * m + 4 := by
        rw [hS, FRC.Nat.add_sub_cancel, hm, Nat.left_distrib, ← FRC.Nat.mul_assoc]
      rw [hp1, pow_add, pow_mul, h8, one_pow, one_mul, h4'] at hf
      exact absurd hf (neg_one_ne_one h2)
  · intro he
    obtain ⟨m, hm⟩ := FRC.Nat.mod_spec 2 (by decide) S
    rw [he, Nat.add_zero] at hm
    obtain ⟨a, ha⟩ := exists_pow_half hp (n := 2 * S) (by rw [hS, ← FRC.Nat.mul_assoc])
    have h4 : (a ^ m) ^ 4 = -1 := by
      rw [← pow_mul, show m * 4 = 2 * S by rw [hm, ← FRC.Nat.mul_assoc, Nat.mul_comm m 4]]; exact ha
    exact ⟨a ^ m, by rw [show (8 : Nat) = 4 * 2 from rfl, pow_mul, h4, pow_two, neg_mul_neg, mul_one],
      by rw [h4]; exact neg_one_ne_one h2⟩

/-- The Tsirelson square without a generator: `ζ⁴ = −1` gives `(ζ + ζ⁷)² = 2`. -/
theorem tsirelson {ζ : Shell p} (h4 : ζ ^ 4 = -1) : (ζ + ζ ^ 7) * (ζ + ζ ^ 7) = 2 := by
  have h8 : ζ ^ 8 = 1 := by rw [show (8 : Nat) = 4 + 4 from rfl, pow_add, h4, neg_mul_neg, mul_one]
  have hz : ζ * ζ ^ 7 = 1 := by rw [mul_comm, ← pow_succ]; exact h8
  have h14 : ζ ^ 7 * ζ ^ 7 = -(ζ * ζ) := by
    rw [← pow_add, show 7 + 7 = 8 + (4 + 2) from rfl, pow_add, pow_add, h8, h4, one_mul, neg_one_mul, pow_two]
  rw [left_distrib, right_distrib, right_distrib, hz, mul_comm (ζ ^ 7) ζ, hz, h14, two_eq]
  exact add_one_add_one_neg _

/-- `2S + 1` is `2⁻¹` on the chart `p = 4S + 1`. -/
theorem two_mul_chart_half {S : Nat} (hS : p = 4 * S + 1) : (2 : Shell p) * ofNat (2 * S + 1) = 1 := ext (by
  show (2 % p * ((2 * S + 1) % p)) % p = 1 % p
  rw [← FRC.Nat.mul_mod _ _ _ Pos.pos,
    show 2 * (2 * S + 1) = p * 1 + 1 by rw [hS, Nat.mul_one, Nat.left_distrib, ← FRC.Nat.mul_assoc],
    FRC.Nat.add_mul_mod_self_left 1 1 p Pos.pos])

/-- The half-square: on the chart `p = 4S + 1`, `2⁻¹ = 2S + 1` is a square iff `S` is even (Carrier B7, `c² = 2⁻¹`).
A root `c` of `c² = 2⁻¹` gives `ζ = c (1 + i)` with `ζ² = i`, an element of order eight; conversely the octant's `ζ`
gives `(ζ + ζ⁷)² = 2` and `c = (ζ + ζ⁷)/2`. -/
theorem half_square_iff (hp : FRC.Nat.isPrime p) {S : Nat} (hS : p = 4 * S + 1) :
    (∃ c : Shell p, c * c = ofNat (2 * S + 1)) ↔ S % 2 = 0 := by
  have h2 := chart_gt_two hp hS
  have hh := two_mul_chart_half hS
  constructor
  · intro ⟨c, hc⟩
    -- with `i² = −1`, `ζ = c (1 + i)` has `ζ² = c² · 2i = i`: an element of order eight
    obtain ⟨i, hi⟩ := exists_quarter_turn hp hS
    have hh' : (ofNat (2 * S + 1) : Shell p) * (1 + 1) = 1 := by rw [mul_comm, ← two_eq]; exact hh
    have e : (1 + i) * (1 + i) = (1 + 1) * i := by
      rw [left_distrib, right_distrib, right_distrib, one_mul, one_mul, mul_one, hi, right_distrib, one_mul,
        add_comm i (-1), add_add_add_comm, add_neg, zero_add]
    have hz : (c * (1 + i)) * (c * (1 + i)) = i := by
      rw [mul_mul_mul_comm, hc, e, ← mul_assoc, hh', one_mul]
    have hz4 : (c * (1 + i)) ^ 4 = -1 := by
      rw [show (4 : Nat) = 2 * 2 from rfl, pow_mul, pow_two (c * (1 + i)), hz, pow_two, hi]
    exact (octant_sector hp hS).1 ⟨c * (1 + i), by
      rw [show (8 : Nat) = 4 * 2 from rfl, pow_mul, hz4, pow_two, neg_mul_neg, mul_one],
      by rw [hz4]; exact neg_one_ne_one h2⟩
  · intro he
    obtain ⟨ζ, h8, h4⟩ := (octant_sector hp hS).2 he
    have h4' : ζ ^ 4 = -1 :=
      match sq_eq_one hp (by rw [← pow_add]; exact h8 : ζ ^ 4 * ζ ^ 4 = 1) with
      | .inl e => absurd e h4
      | .inr e => e
    refine ⟨(ζ + ζ ^ 7) * ofNat (2 * S + 1), ?_⟩
    rw [mul_mul_mul_comm, tsirelson h4', ← mul_assoc, hh, one_mul]

/-- Integer parity is frame data: on an odd shell the pair `x ↔ −x` flips the parity of the representative. -/
theorem parity_flips {S : Nat} (hS : p = 4 * S + 1) {x : Shell p} (hx : x ≠ 0) :
    x.val % 2 = 0 ↔ ¬ (-x).val % 2 = 0 := by
  have hneg : (-x).val = p - x.val := by
    show (p - x.val) % p = p - x.val
    exact FRC.Nat.mod_eq_of_lt (Nat.sub_lt Pos.pos (val_pos hx))
  rw [hneg]
  exact FRC.Nat.parity_split (n := 2 * S)
    (by rw [FRC.Nat.add_sub_of_le (Nat.le_of_lt x.lt), hS, ← FRC.Nat.mul_assoc])

end Prime
end Shell
end FRC
